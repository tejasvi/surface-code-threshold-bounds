import QECML

/-!
# Axioms of the main theorems

Run from the project root after `lake build`: `lake env lean scripts/Axioms.lean`. Each theorem should depend on
`propext`, `Classical.choice` and `Quot.sound` at most.
-/

-- the bound on the optimal failure probability and the threshold
#print axioms QECML.theoremB_a12_main
#print axioms QECML.threshold_a12_main
#print axioms QECML.theoremB_a12_2Dproved
#print axioms QECML.threshold_a12_2Dproved
#print axioms QECML.pMLPlanar_mono_q
#print axioms QECML.pMLPlanar_mono_size

-- the confidence statement
#print axioms QECML.theoremB_certified
#print axioms QECML.theoremB_certified_familywise
#print axioms QECML.cert_confidence_A
#print axioms QECML.cp_accept_A
#print axioms QECML.cp_reject_A

-- the accepted counts and the quoted Clopper–Pearson upper bounds
#print axioms QECML.obs_accept
#print axioms QECML.obsK_le
#print axioms QECML.obs_cp
#print axioms QECML.cp_upper_k3
#print axioms QECML.cp_upper_k6
#print axioms QECML.cp_upper_k8
#print axioms QECML.cp_upper_k9
#print axioms QECML.cp_tight_k3
#print axioms QECML.cp_tight_k6
#print axioms QECML.cp_tight_k8
#print axioms QECML.cp_tight_k9

-- the counts of the certificate under measurement errors
#print axioms QECML.d1_accept
#print axioms QECML.d1_rule_tail
#print axioms QECML.d1_cp
#print axioms QECML.d1_cp_upper_k4
#print axioms QECML.d1_cp_tight_k4
