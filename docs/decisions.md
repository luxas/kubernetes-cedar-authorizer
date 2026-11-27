# Decision log

Initial log, copied from PLAN.md section 8 at stage 0. Append new decisions below with the next free `D-n`.

## Resolved

- **D-1 Mirror.** Vendor/copy `kubernetes/lean` into `lean/mirror/` for now, to keep it distinct
  from the new layer; unify later. The Go source of truth is the review branch
  (`impl-conditional-authz-review`, `2ee49d340c9`).
- **D-2 Error semantics.** Start with Cedar's reference semantics (an erroring policy is not
  applicable). Strengthening (fail closed on a Deny-effect error) is a later option, recorded
  against KEP D-3; the `oracle` in C-3 is where it would change.
- **D-3 Condition encoding.** The Cedar residual itself, no CEL; domain `kubernetes.cedarpolicy.com/`
  for condition ids and type; Cedar JSON policy format now, Cedar text format as a follow-up.
- **D-4 No in-process CEL path** in this milestone.
- **D-5 No namespace object** (or other non-request entity) in conditions now; possible follow-up.
- **D-6 Workspace of three crates** (`core`, `schema`, `webhook`).
- **D-7 `main` history.** Tag `legacy-pre-1.38`, delete old files in the first stacked PR.
- **D-8 Lean version.** Always the one pinned by the cedar-spec commit we depend on.
- **D-9 Name on create / deletecollection.** Always unknown; no special case for a
  `metadata.name` field selector.

- **D-10 Residuals with an `error` node.** Current limitation of Cedar: fail closed for the
  request (counter, no `Allow`), documented; fix expected in a future Cedar (F-2). Residuals that
  are exactly `false` or `error` are dropped as they never apply.
- **D-11 Resource uid.** One fixed reserved synthetic uid per resource type, never usable by policies
  (lint); not random, because it would have to be carried in the condition (see 1.3).

Open, to decide at stage boundaries: Aeneas feasibility (5b); whether `Lawful` should also
cover reason/error text (currently only decision, with error-ness handled by A-7).
