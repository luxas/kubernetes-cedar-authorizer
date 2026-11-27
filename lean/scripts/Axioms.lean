import conditionsenforcer.conditionsenforcer_properties
import webhook.webhook_properties
import authorizer.evaluate_properties
import authorizer.conditions_properties
import Cedar.Thm.TPE

/-! Axiom audit, run by `scripts/check.sh` via `lake env lean scripts/Axioms.lean`.
Expected: only `propext`, `Classical.choice`, `Quot.sound` for Cedar; the mirror theorems
may additionally list the named axioms/opaques of the Go model (see mirror/STATUS.md). -/

#print axioms Cedar.Thm.reauthorize_is_sound
#print axioms conditionsenforcer.end_to_end_safety
#print axioms conditionsenforcer.served_safety_classified
#print axioms webhook.P_49_legacy_shape
#print axioms authorizer.P_27_counterexample
#print axioms webhook.P_49_legacy_conditional_not_allow
