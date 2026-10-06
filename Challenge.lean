module

public import Mathlib

@[expose] public section

noncomputable section

open MeasureTheory

/-- Smooth, compactly supported real functions whose closed support lies in Ω. -/
def testFunctions (Ω : Set ℂ) : Submodule ℝ (ℂ → ℝ) where
  carrier := {u | ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ tsupport u ⊆ Ω}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  add_mem' := by
    rintro u v ⟨hu, hu', hu''⟩ ⟨hv, hv', hv''⟩
    exact ⟨hu.add hv, hu'.add hv', (tsupport_add u v).trans (Set.union_subset hu'' hv'')⟩
  smul_mem' := by
    rintro c u ⟨hu, hu', hu''⟩
    refine ⟨hu.const_smul c, HasCompactSupport.smul_left (f := fun _ => c) hu', ?_⟩
    exact (tsupport_smul_subset_right (fun _ => c) u).trans hu''

def dirichletEnergy (u : ℂ → ℝ) : ENNReal :=
  ∫⁻ z, ‖fderiv ℝ u z‖ₑ ^ 2

def l2NormSq (u : ℂ → ℝ) : ENNReal :=
  ∫⁻ z, ‖u z‖ₑ ^ 2

def rayleigh (u : ℂ → ℝ) : ENNReal :=
  dirichletEnergy u / l2NormSq u

def dirichletEigenvalue (Ω : Set ℂ) (j : ℕ) : ENNReal :=
  ⨅ (V : Submodule ℝ (ℂ → ℝ)) (_ : V ≤ testFunctions Ω) (_ : Module.finrank ℝ V = j),
    ⨆ (u : ℂ → ℝ) (_ : u ∈ V) (_ : u ≠ 0), rayleigh u

namespace PalomarDirichlet

theorem main_result (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (hsc : SimplyConnectedSpace (↥Ω)) (j : ℕ) (hj : 1 ≤ j) :
    ENNReal.ofReal (4 * Real.pi * j) < MeasureTheory.volume Ω * dirichletEigenvalue Ω j := by
  sorry

end PalomarDirichlet

end
