# Repository settings checklist (do this before a repository goes public, and re-check after)

Replace `OWNER/REPO` and run with `gh` as a repository admin. Each item has a read-back command. A direct-landing repository needs the first item
(landing is plain fast-forward pushes by the owner; the ruleset has **no required pull request and no bypass list**, so landing still works and a force
push or a branch deletion cannot happen to the default branch).

1. **Protect the default branch from deletion and non-fast-forward updates.**
   `gh api repos/OWNER/REPO/rulesets --input templates/ruleset-protect-main.json`
   Read back: `gh api repos/OWNER/REPO/rules/branches/main --jq '.[].type'` prints `deletion` and `non_fast_forward` (`bin/land-audit` warns when it does not).
2. **Protect release tags from deletion and update** (a pin by tag must not be movable):
   `gh api repos/OWNER/REPO/rulesets --input templates/ruleset-protect-release-tags.json`
3. **Pull-request workflows from forks need approval for ALL outside contributors** (public repositories only; the API refuses it on a private one):
   `gh api -X PUT repos/OWNER/REPO/actions/permissions/fork-pr-contributor-approval -f approval_policy=all_external_contributors`
4. **The workflow token is read-only and cannot approve pull requests:**
   `gh api -X PUT repos/OWNER/REPO/actions/permissions/workflow -f default_workflow_permissions=read -F can_approve_pull_request_reviews=false`
   Read back: `gh api repos/OWNER/REPO/actions/permissions/workflow`
5. **Private vulnerability reporting on:** `gh api -X PUT repos/OWNER/REPO/private-vulnerability-reporting`
6. **Secret scanning and push protection on:**
   `gh api -X PATCH repos/OWNER/REPO -F 'security_and_analysis[secret_scanning][status]=enabled' -F 'security_and_analysis[secret_scanning_push_protection][status]=enabled'`
7. **Delete head branches after merge:** `gh api -X PATCH repos/OWNER/REPO -F delete_branch_on_merge=true`
8. **Workflows:** no `pull_request_target`; a `pull_request` trigger runs without secrets; `permissions:` is declared (read-only) in every workflow.
9. **A `SECURITY.md`** says how to report a vulnerability, and no secret is in the history (scan before flipping).
10. **Runners:** `runs-on` back to a hosted runner in every workflow (no `self-hosted`), the repository's self-hosted runner removed, and `.github/visibility` set to `public` (a repository's lint fails when a workflow names `self-hosted` and it is not `private`).
