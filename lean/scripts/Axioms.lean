import conditionsenforcer.conditionsenforcer_properties
import webhook.webhook_properties
import authorizer.evaluate_properties
import authorizer.conditions_properties
import Cedar.Thm.TPE
import K8sAuthz

/-! Axiom audit, run by `scripts/check.sh` via `lake env lean scripts/Axioms.lean`.
Expected: only `propext`, `Classical.choice`, `Quot.sound` for Cedar; the mirror theorems
may additionally list the named axioms/opaques of the Go model (see mirror/STATUS.md). -/

#print axioms Cedar.Thm.reauthorize_is_sound
#print axioms conditionsenforcer.end_to_end_safety
#print axioms conditionsenforcer.served_safety_classified
#print axioms webhook.P_49_legacy_shape
#print axioms authorizer.P_27_counterexample
#print axioms webhook.P_49_legacy_conditional_not_allow

/-! K8sAuthz headline theorems (stage 2): must not list `sorryAx`. -/
#print axioms K8sAuthz.refines_sem
#print axioms K8sAuthz.guard_guarded
#print axioms K8sAuthz.guard_inert
#print axioms K8sAuthz.guard_sound
#print axioms K8sAuthz.guard_lawful
#print axioms K8sAuthz.chain_sound
#print axioms K8sAuthz.chain_lawful
#print axioms K8sAuthz.chainN_lawful
#print axioms K8sAuthz.enforcement_forward
#print axioms K8sAuthz.enforcement_exact
#print axioms K8sAuthz.chain_enforcement_exact
#print axioms K8sAuthz.unaware_fail_closed
#print axioms K8sAuthz.chain_sound_of_deny_faithful
#print axioms K8sAuthz.fail_closed_to_noOp_is_fail_open
#print axioms K8sAuthz.plan_lawful_guarded_clash
#print axioms K8sAuthz.A0_not_both
#print axioms K8sAuthz.L4_literal_false
#print axioms K8sAuthz.G1_needs_good
#print axioms K8sAuthz.chain_needs_valid_names
#print axioms K8sAuthz.chain_needs_good_members
#print axioms K8sAuthz.union_eval_unconditional_is_FD
#print axioms K8sAuthz.A0_lawful
#print axioms K8sAuthz.A2_lawful
#print axioms K8sAuthz.A2_guarded
#print axioms K8sAuthz.W2_consistent_nontrivial
#print axioms K8sAuthz.chain_A2_lawful
#print axioms K8sAuthz.chain_A2_enforcement
#print axioms K8sAuthz.Bridge.pd_cua_toCAD
#print axioms K8sAuthz.Bridge.good_toCAD
#print axioms K8sAuthz.Bridge.sem_toCAD
#print axioms K8sAuthz.Bridge.pmap_refines
#print axioms K8sAuthz.Bridge.peval_is_refinement
