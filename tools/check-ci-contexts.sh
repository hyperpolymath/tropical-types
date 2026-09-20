#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# check-ci-contexts.sh — prove that every status context this repository's
# branch rules require is a name its own workflows can actually publish.
#
# WHY THIS EXISTS
# ---------------
# A required status check is matched by *string equality* against the check-run
# name GitHub publishes. When the two never match, the required check is never
# satisfied: every pull request stays BLOCKED while the CI board shows green.
# That is this repository's issue #17, and the class is catalogued upstream in
# standards docs/audits/audit-hypatia-pin-orphan-2026-05-27.adoc.
#
# Two name shapes exist:
#   * a normal job publishes its `name:` (or its job id when it has no `name:`);
#   * a job that *calls a reusable workflow* publishes
#         <caller display name or id> / <inner job display name or id>
#     so a wrapper can never publish the reusable's bare inner name.
#
# WHAT IT CHECKS
#   1. CONTRACT — offline, always enforced: every [[wrapper]] block in
#      .machine_readable/CI-CONTEXTS.a2ml must still describe the workflow
#      as it is (caller job id present, declared contexts prefixed by it), so the
#      documented context string keeps being published. This is the half that
#      fails the build; it is deterministic and always satisfiable.
#   2. REQUIRED CONTEXTS — live, advisory by default: every context required by
#      this repository's branch rulesets (and legacy branch protection, when the
#      token can read it) is either producible by a workflow here, or attached to
#      a third-party app integration.
#
# USAGE
#   tools/check-ci-contexts.sh [REPO_ROOT] [--no-network]
#
# ENV
#   GITHUB_REPOSITORY         owner/repo; default: `gh repo view`, else live half skipped
#   GH_TOKEN / GITHUB_TOKEN   read-only token, used for the live half
#   CI_CONTEXTS_CONTRACT      override the contract path
#   REQUIRED_CONTEXTS_STRICT  1 = fail on a provably unproducible required context.
#                             Default 0 = warn only: a check that reds nobody yet
#                             is a warning, not a red.
#
# EXIT: 0 = contract intact and no hard finding; 1 = contract broken, or (strict)
#       an unproducible required context.
set -uo pipefail

ROOT="."
OFFLINE=0
for a in "$@"; do
  case "$a" in
    --no-network) OFFLINE=1 ;;
    --help|-h) sed -n '2,40p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    -*) printf 'unknown option: %s\n' "$a" >&2; exit 2 ;;
    *) ROOT="$a" ;;
  esac
done

WF_DIR="$ROOT/.github/workflows"
CONTRACT="${CI_CONTEXTS_CONTRACT:-$ROOT/.machine_readable/CI-CONTEXTS.a2ml}"
HAVE_GH=0; command -v gh >/dev/null 2>&1 && HAVE_GH=1
HAVE_JQ=0; command -v jq >/dev/null 2>&1 && HAVE_JQ=1
STRICT="${REQUIRED_CONTEXTS_STRICT:-0}"
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT

info() { printf '    %s\n' "$*"; }
note() { printf '::notice::%s\n' "$*"; }
warn() { printf '::warning::%s\n' "$*"; }
err()  { printf '::error::%s\n' "$*"; }

FAIL=0   # contract broken -> always fail
HARD=0   # unproducible required context -> fail only in strict mode

# ---------------------------------------------------------------- parsing ----

# Emit "jobId<TAB>nameOrDash<TAB>usesOrDash" for every job in one workflow file.
# Empty fields are written as "-" because `read` with IFS=tab collapses runs of
# IFS whitespace, which would silently shift every field after an empty one.
jobs_of() {
  awk '
    /^jobs:[[:space:]]*$/ { injobs=1; next }
    /^[^[:space:]#]/      { injobs=0 }
    injobs && /^  [A-Za-z0-9_.-]+:[[:space:]]*$/ {
      if (job != "") print job "\t" (name==""?"-":name) "\t" (uses==""?"-":uses)
      job=$1; sub(/:$/,"",job); name=""; uses=""; next
    }
    injobs && /^    name:[[:space:]]*/ {
      v=$0; sub(/^[[:space:]]*name:[[:space:]]*/,"",v); gsub(/^"|"[[:space:]]*$/,"",v); name=v
    }
    injobs && /^    uses:[[:space:]]*/ {
      v=$0; sub(/^[[:space:]]*uses:[[:space:]]*/,"",v); sub(/[[:space:]]*#.*$/,"",v); uses=v
    }
    END { if (job != "") print job "\t" (name==""?"-":name) "\t" (uses==""?"-":uses) }
  ' "$1"
}

# One line per [[wrapper]] block: "workflow<TAB>callerJobId<TAB>ctx,ctx"
contract_wrappers() {
  [ -f "$CONTRACT" ] || return 1
  awk '
    function flush() { if (wf != "") printf "%s\t%s\t%s\n", wf, cj, pc; wf=""; cj=""; pc="" }
    /^\[\[wrapper\]\]/ { flush(); inb=1; next }
    /^\[/             { flush(); inb=0; next }
    inb && /^[[:space:]]*workflow[[:space:]]*=/ {
      v=$0; sub(/^[^=]*=[[:space:]]*/,"",v); gsub(/^"|"[[:space:]]*$/,"",v); wf=v
    }
    inb && /^[[:space:]]*caller-job-id[[:space:]]*=/ {
      v=$0; sub(/^[^=]*=[[:space:]]*/,"",v); gsub(/^"|"[[:space:]]*$/,"",v); cj=v
    }
    inb && /^[[:space:]]*published-contexts[[:space:]]*=/ {
      v=$0; sub(/^[^=]*=[[:space:]]*/,"",v); gsub(/[][]|"/,"",v); gsub(/,[[:space:]]*/,",",v); pc=v
    }
    END { flush() }
  ' "$CONTRACT"
}

contract_value() { # section-key -> value
  [ -f "$CONTRACT" ] || return 1
  awk -v k="$1" '
    $0 ~ "^[[:space:]]*" k "[[:space:]]*=" {
      v=$0; sub(/^[^=]*=[[:space:]]*/,"",v); gsub(/^"|"[[:space:]]*$/,"",v); print v; exit
    }' "$CONTRACT"
}

# Inner jobs of a reusable, resolved from the pinned ref.
# Emits "jobId<TAB>displayNameOrDash".
reusable_jobs() {
  local spec="$1" path repo file ref url cache
  path="${spec%@*}"; ref="${spec##*@}"
  repo="${path%%/.github/workflows/*}"
  file=".github/workflows/${path##*/}"
  cache="$TMP/$(printf '%s' "$spec" | tr -c 'A-Za-z0-9.' '_')"
  if [ ! -f "$cache" ]; then
    [ "$OFFLINE" = 1 ] && return 1
    curl -fsSL "https://raw.githubusercontent.com/$repo/$ref/$file" -o "$cache" 2>/dev/null || return 1
  fi
  jobs_of "$cache"
}

# ------------------------------------------------------------------ step 1 ----
printf '\n== 1. CI context contract (%s)\n' "${CONTRACT#"$ROOT"/}"
if [ ! -f "$CONTRACT" ]; then
  err "contract file missing: $CONTRACT"
  err "the repository has no record of which context strings its workflows publish; add it (see docs/CI-CONTEXTS.adoc)"
  exit 1
fi

while IFS=$'\t' read -r wf cj pcs; do
  [ -n "$wf" ] || continue
  path="$ROOT/$wf"
  printf '  %s\n' "$wf"
  if [ ! -f "$path" ]; then
    err "$wf is named by the contract but does not exist"
    FAIL=1; continue
  fi
  jrow="$(jobs_of "$path" | awk -F'\t' -v id="$cj" '$1==id {print; exit}')"
  if [ -z "$jrow" ]; then
    err "$wf no longer defines caller job '$cj' — the published check name changes with it, so any required context naming the old string becomes unsatisfiable"
    FAIL=1
  else
    jname="$(printf '%s' "$jrow" | cut -f2)"
    [ "$jname" = "-" ] && jname=""
    info "caller job '$cj' present"
  fi
  oldifs="$IFS"; IFS=','
  for ctx in $pcs; do
    IFS="$oldifs"
    case "$ctx" in
      "$cj / "*) info "declared context: $ctx" ;;
      *) if [ -n "${jname:-}" ]; then
           case "$ctx" in "$jname / "*) info "declared context: $ctx (via caller display name)"; continue ;; esac
         fi
         if jobs_of "$path" | awk -F'\t' -v n="$ctx" '$2==n {f=1} END{exit(f?0:1)}'; then
           info "declared context: $ctx (a plain job display name in this workflow)"
         else
           err "$wf declares context '$ctx'; its caller job '$cj' can only publish '$cj / <inner job name>'"
           FAIL=1
         fi ;;
    esac
    IFS=','
  done
  IFS="$oldifs"
  rus="$(jobs_of "$path" | awk -F'\t' -v id="$cj" '$1==id {print $3; exit}')"
  [ "$rus" = "-" ] && rus=""
  case "$rus" in
    *".github/workflows/"*"@"*)
      if inner="$(reusable_jobs "$rus")" && [ -n "$inner" ]; then
        while IFS=$'\t' read -r iid iname _rest; do
          [ -n "$iid" ] || continue
          [ "$iname" = "-" ] && iname=""
          pub="$cj / ${iname:-$iid}"
          case ",$pcs," in
            *",$pub,"*) info "verified published name: $pub" ;;
            *) info "also published by $rus but not listed in the contract: $pub" ;;
          esac
        done <<<"$inner"
      else
        note "could not read $rus to confirm the inner job name — caller prefix checked only"
      fi ;;
    *) warn "$wf no longer calls a reusable workflow; its [[wrapper]] entry in the contract is stale" ;;
  esac
done < <(contract_wrappers)

# ------------------------------------------------------------ step 2 (live) ----
printf '\n== 2. branch rules vs publishable context names\n'
REPO="${GITHUB_REPOSITORY:-}"
if [ -z "$REPO" ] && [ "$HAVE_GH" = 1 ]; then
  REPO="$(gh repo view --json nameWithOwner -q .nameWithOwner 2>/dev/null || true)"
fi

live_ok=1
[ "$OFFLINE" = 1 ] && live_ok=0
[ "$HAVE_GH" = 0 ] && live_ok=0
[ "$HAVE_JQ" = 0 ] && live_ok=0
[ -z "$REPO" ] && live_ok=0
if [ "$live_ok" = 1 ] && ! gh api rate_limit >/dev/null 2>&1; then
  note "gh is not authenticated with a usable token — live half skipped"
  live_ok=0
fi

if [ "$live_ok" = 0 ]; then
  note "live half skipped (need gh + jq + GITHUB_REPOSITORY + a token; or --no-network was passed)"
  if [ "$FAIL" = 0 ]; then printf '\ncheck-ci-contexts: contract intact\n'; else printf '\ncheck-ci-contexts: CONTRACT BROKEN\n'; fi
  exit "$FAIL"
fi

# every name this repository can publish
publishable() {
  local f id name uses inner iid iname
  for f in "$WF_DIR"/*.yml "$WF_DIR"/*.yaml; do
    [ -f "$f" ] || continue
    while IFS=$'\t' read -r id name uses; do
      [ -n "$id" ] || continue
      [ "$name" = "-" ] && name=""
      [ "$uses" = "-" ] && uses=""
      if [ -n "$uses" ]; then
        case "$uses" in
          *".github/workflows/"*"@"*)
            if inner="$(reusable_jobs "$uses")" && [ -n "$inner" ]; then
              while IFS=$'\t' read -r iid iname _rest; do
                [ -n "$iid" ] || continue
                [ "$iname" = "-" ] && iname=""
                printf '%s / %s\n' "$id" "${iname:-$iid}"
                [ -n "$name" ] && printf '%s / %s\n' "$name" "${iname:-$iid}"
              done <<<"$inner"
            else
              printf '%s / *\n' "$id"
              [ -n "$name" ] && printf '%s / *\n' "$name"
            fi ;;
          *) : ;;
        esac
      else
        printf '%s\n' "${name:-$id}"
      fi
    done < <(jobs_of "$f")
  done
}
publishable | sort -u >"$TMP/publishable"
printf '  %s publishable name(s) from this repository:\n' "$(wc -l <"$TMP/publishable" | tr -d ' ')"
sed 's/^/    /' "$TMP/publishable"

BR="$(gh api "repos/$REPO" 2>/dev/null | jq -r '.default_branch // "main"' 2>/dev/null || echo main)"

# required contexts, from both places GitHub keeps them
: >"$TMP/required"
ruleset_ids="$(gh api "repos/$REPO/rulesets" 2>/dev/null \
  | jq -r '.[]? | select(.target=="branch") | .id' 2>/dev/null || true)"
for id in $ruleset_ids; do
  body="$(gh api "repos/$REPO/rulesets/$id" 2>/dev/null || true)"
  printf '%s' "$body" | jq -r '.rules[]? | select(.type=="required_status_checks")
      | .parameters.required_status_checks[]?
      | [(.context|tostring), ((.integration_id // 0)|tostring)] | @tsv' 2>/dev/null \
    | awk -F'\t' 'NF{print $0 "\truleset"}' >>"$TMP/required"
done

bp="$(gh api "repos/$REPO/branches/$BR/protection/required_status_checks" 2>/dev/null || true)"
if printf '%s' "$bp" | jq -e '.enforcement_level' >/dev/null 2>&1; then
  level="$(printf '%s' "$bp" | jq -r '.enforcement_level')"
  info "legacy branch protection on $BR: required status checks enforcement_level=$level"
  printf '%s' "$bp" | jq -r '.contexts[]? | [., "0"] | @tsv' 2>/dev/null \
    | awk -F'\t' 'NF{print $0 "\tbranch-protection"}' >>"$TMP/required"
  printf '%s' "$bp" | jq -r '.checks[]? | [(.context|tostring), ((.app_id // 0)|tostring)] | @tsv' 2>/dev/null \
    | awk -F'\t' 'NF{print $0 "\tbranch-protection"}' >>"$TMP/required"
else
  note "branch protection on $BR unreadable with this token (Administration: read is required) — rulesets only"
fi

sort -u "$TMP/required" -o "$TMP/required"
if [ ! -s "$TMP/required" ]; then
  info "no required status contexts found in this repository's branch rules"
  if [ "$FAIL" = 0 ]; then printf '\ncheck-ci-contexts: contract intact\n'; else printf '\ncheck-ci-contexts: CONTRACT BROKEN\n'; fi
  exit "$FAIL"
fi

CANON="$(contract_value canonical-hypatia)"
while IFS=$'\t' read -r ctx app src; do
  [ -n "$ctx" ] || continue
  if [ -n "$app" ] && [ "$app" != "0" ] && [ "$app" != "15368" ]; then
    info "required, third-party app $app ($src): $ctx"
    continue
  fi
  if awk -v req="$ctx" '$0==req{f=1} END{exit(f?0:1)}' "$TMP/publishable"; then
    info "required and producible ($src): $ctx"
    continue
  fi
  hit=0
  while IFS= read -r cand; do
    # shellcheck disable=SC2254  # unquoted RHS is a deliberate glob (matrix-suffixed names)
    case "$ctx" in $cand) hit=1; break ;; esac
  done <"$TMP/publishable"
  if [ "$hit" = 1 ]; then
    info "required and producible ($src): $ctx"
    continue
  fi
  bare="$(contract_value bare-hypatia)"
  if [ -n "$bare" ] && [ "$ctx" = "$bare" ]; then
    msg="required context '$ctx' is unsatisfiable by construction: it is the bare name of a reusable workflow's inner job, and a caller always publishes '<caller> / <inner job name>'. Require '$CANON' instead, or publish '$ctx' from a job implemented in this repository."
  else
    msg="required context '$ctx' ($src) is not producible by any workflow in this repository, and is not attached to a third-party app integration"
  fi
  HARD=1
  if [ "$STRICT" = 1 ]; then err "$msg"; else warn "$msg (advisory: set REQUIRED_CONTEXTS_STRICT=1 to fail)"; fi
done <"$TMP/required"

if [ "$FAIL" != 0 ]; then
  printf '\ncheck-ci-contexts: CONTRACT BROKEN\n'; exit 1
fi
if [ "$HARD" = 1 ] && [ "$STRICT" = 1 ]; then
  printf '\ncheck-ci-contexts: contract intact, but a required context is unproducible\n'; exit 1
fi
printf '\ncheck-ci-contexts: contract intact\n'
exit 0
