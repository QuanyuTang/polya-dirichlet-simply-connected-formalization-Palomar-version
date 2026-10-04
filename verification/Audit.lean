import RequestProject.Main

/-!
Checks the public statements and enforces the axiom dependencies of the final
theorems and the semantic bridge. Each guard asserts the entire axiom list;
an unexpected axiom or diagnostic makes this file fail to compile.
-/

#check main
#check main_counting
#check DirichletBridge.dirichletEigenvalue_eq_spectral
#check DirichletBridge.complexDirichletOperator_form_representation
#check DirichletBridge.spectralDirichletEigenvalue_multiplicity_complex

/-- info: 'main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms main

/-- info: 'main_counting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms main_counting

/-- info: 'DirichletBridge.dirichletEigenvalue_eq_spectral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DirichletBridge.dirichletEigenvalue_eq_spectral

/-- info: 'DirichletBridge.spectralDirichletEigenvalue_multiplicity_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DirichletBridge.spectralDirichletEigenvalue_multiplicity_complex

/-- info: 'DirichletBridge.complexDirichletOperator_form_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DirichletBridge.complexDirichletOperator_form_representation

/-- info: 'DirichletBridge.complexDirichletOperator_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DirichletBridge.complexDirichletOperator_selfAdjoint

/-- info: 'DirichletBridge.complex_Dirichlet_eigenvalue_iff_indexed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DirichletBridge.complex_Dirichlet_eigenvalue_iff_indexed

/-- info: 'DirichletBridge.complexEnergyForm_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DirichletBridge.complexEnergyForm_complete

/-- info: 'DirichletBridge.complexH01_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DirichletBridge.complexH01_norm_sq

/-- info: 'DirichletBridge.complexSmoothCoreJet_dense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DirichletBridge.complexSmoothCoreJet_dense

/-- info: 'DirichletBridge.complexDirichletOperator_eigenvalue_positive_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DirichletBridge.complexDirichletOperator_eigenvalue_positive_real

/-- info: 'DirichletBridge.complexEnergyForm_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DirichletBridge.complexEnergyForm_eq_integral

/-- info: 'DirichletBridge.complexSmoothCoreJet_gradient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DirichletBridge.complexSmoothCoreJet_gradient

/-- info: 'DirichletBridge.exists_complexCoreFunction_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DirichletBridge.exists_complexCoreFunction_eq

/-- info: 'DirichletBridge.spectralDirichletEigenvalue_tendsto_atTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DirichletBridge.spectralDirichletEigenvalue_tendsto_atTop

/-- info: 'DirichletBridge.spectralDirichletCountingSet_finite_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DirichletBridge.spectralDirichletCountingSet_finite_of_bounded
