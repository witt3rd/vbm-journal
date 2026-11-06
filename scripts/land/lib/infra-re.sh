#!/usr/bin/env bash
# The ONE classifier of INFRASTRUCTURE failures of a CI run: the job never started (an account's payments or spending limit), a runner that was
# lost or shut down, a shallow fetch, the network, auth, a 5xx from a service, a tool the runner lacks. A run that matches says nothing about the
# commit, so it is not "main is red" and must not freeze landing. A code failure, an empty or unreadable log and an unreadable annotation are NOT
# infrastructure (fail closed). Sourced, never run. Gate-defining: weakening this list un-reds a red main.
#
#   infra_re            an ERE for `grep -E`, applied to the failed job's annotations and to the failed log
#   infra_failure RUN JOB   0 when the failed job (JOB, a check-run id, may be empty) or the run (RUN) failed for an infrastructure reason; needs $gh
infra_re='recent account payments have failed|spending limit|The job was not started|shallow update|Permission denied \(publickey\)|Internal Server Error|Bad Gateway|Service Unavailable|Gateway Time-?out|HTTP/[0-9.]+ 50[0-9]|error: 50[0-9]|status (code )?50[0-9]|RPC failed|early EOF|Could not resolve host|Temporary failure in name resolution|Connection (reset|timed out|refused)|TLS handshake timeout|No space left on device|runner has received a shutdown signal|lost communication with the server|E: (Unable to|Failed to fetch)|fatal: unable to access|fatal: could not read|Unable to (download|locate)|rate limit exceeded|is not installed'
infra_failure() {
  local ann log
  ann=$([ -z "${2:-}" ] || "${gh:-gh}" api "repos/{owner}/{repo}/check-runs/$2/annotations" --jq '.[].message' 2>/dev/null || true)
  if [ -n "$ann" ] && grep -qE -- "$infra_re" <<<"$ann"; then return 0; fi
  log=$("${gh:-gh}" run view "$1" --log-failed 2>/dev/null || true)
  if [ -n "$log" ] && grep -qE -- "$infra_re" <<<"$log"; then return 0; fi
  return 1
}
