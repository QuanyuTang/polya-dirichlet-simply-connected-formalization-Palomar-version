module

public import RequestProject.Main

@[expose] public section

namespace PalomarDirichlet

theorem main_result (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (hsc : SimplyConnectedSpace Ω) (j : ℕ) (hj : 1 ≤ j) :
    ENNReal.ofReal (4 * Real.pi * j) < MeasureTheory.volume Ω * dirichletEigenvalue Ω j := by
  exact strict_polya_variational Ω hopen hbdd hsc j hj

end PalomarDirichlet

end
