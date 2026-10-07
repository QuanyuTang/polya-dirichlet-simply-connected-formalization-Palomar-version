module

public import Mathlib

@[expose] public section


/-!
# The strict Dirichlet Pólya inequality on simply connected planar domains

`main` proves `4πj < |Ω| λ_j(Ω)` for every `j ≥ 1`, where the positive
Dirichlet eigenvalues are defined independently using orthonormal eigenvectors
of the compact inverse of the gradient-form Dirichlet operator.
`main_counting` proves the inclusive spectral counting inequality.

The original smooth-core variational proof is `strict_polya_variational`.
The bridge constructs the real and complex H₀¹ domains and their Dirichlet
operators, proves the min-max identification, and verifies multiplicities.
The variational development was produced with Aristotle; the spectral bridge
was developed with Codex. Toolchain: Palomar toolchain: Lean 4.35.0-rc2, mathlib v4.35.0-rc2.
-/

noncomputable section

section

/-! ## The unilateral shift on `ℓ²(ℕ₀)` -/

open scoped InnerProductSpace ENNReal

/-- The Hilbert space `ℓ²(ℕ₀)`. -/
abbrev L2N := lp (fun _ : ℕ => ℂ) 2

/-- Right shift of a sequence: `(x₀, x₁, …) ↦ (0, x₀, x₁, …)`. -/
def shiftFun (x : ℕ → ℂ) : ℕ → ℂ := fun n => Nat.casesOn n 0 x

/-- Left shift of a sequence: `(x₀, x₁, …) ↦ (x₁, x₂, …)`. -/
def shiftAdjFun (x : ℕ → ℂ) : ℕ → ℂ := fun n => x (n + 1)

lemma two_toReal : (2 : ℝ≥0∞).toReal = 2 := by norm_num

lemma memℓp_two_iff (f : ℕ → ℂ) : Memℓp f 2 ↔ Summable fun n => ‖f n‖ ^ (2 : ℝ) := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal), two_toReal]

lemma memℓp_shiftFun {x : ℕ → ℂ} (hx : Memℓp x 2) : Memℓp (shiftFun x) 2 := by
  rw [memℓp_two_iff] at hx ⊢
  rw [← summable_nat_add_iff 1]
  simpa [shiftFun] using hx

lemma memℓp_shiftAdjFun {x : ℕ → ℂ} (hx : Memℓp x 2) : Memℓp (shiftAdjFun x) 2 := by
  rw [memℓp_two_iff] at hx ⊢
  exact (summable_nat_add_iff 1).2 hx

lemma norm_sq_eq_tsum (x : L2N) : ‖x‖ ^ (2 : ℝ) = ∑' n, ‖x n‖ ^ (2 : ℝ) := by
  have := lp.norm_rpow_eq_tsum (p := 2) (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x
  simpa [two_toReal] using this

/-- The unilateral shift `S eₙ = eₙ₊₁` as a linear map. -/
def shiftLM : L2N →ₗ[ℂ] L2N where
  toFun x := ⟨shiftFun x, memℓp_shiftFun x.2⟩
  map_add' x y := by
    ext n
    change shiftFun (↑(x + y)) n = (shiftFun (↑x) + shiftFun (↑y)) n
    rw [lp.coeFn_add]
    cases n <;> simp [shiftFun]
  map_smul' c x := by
    ext n
    change shiftFun (↑(c • x)) n = (c • shiftFun (↑x)) n
    rw [lp.coeFn_smul]
    cases n <;> simp [shiftFun]

/-- The backward shift as a linear map. -/
def shiftAdjLM : L2N →ₗ[ℂ] L2N where
  toFun x := ⟨shiftAdjFun x, memℓp_shiftAdjFun x.2⟩
  map_add' x y := by
    ext n
    change shiftAdjFun (↑(x + y)) n = (shiftAdjFun (↑x) + shiftAdjFun (↑y)) n
    rw [lp.coeFn_add]
    simp [shiftAdjFun]
  map_smul' c x := by
    ext n
    change shiftAdjFun (↑(c • x)) n = (c • shiftAdjFun (↑x)) n
    rw [lp.coeFn_smul]
    simp [shiftAdjFun]

lemma norm_shiftLM (x : L2N) : ‖shiftLM x‖ = ‖x‖ := by
  have h1 := norm_sq_eq_tsum (shiftLM x)
  have hs : Summable fun n => ‖(shiftLM x) n‖ ^ (2 : ℝ) := (memℓp_two_iff _).1 (shiftLM x).2
  rw [hs.tsum_eq_zero_add] at h1
  simp only [show shiftLM x 0 = 0 from rfl,
    show ∀ n : ℕ, shiftLM x (n + 1) = x n from fun _ => rfl, norm_zero] at h1
  rw [Real.zero_rpow (by norm_num), zero_add, ← norm_sq_eq_tsum x] at h1
  have := (Real.rpow_left_injOn (by norm_num : (2 : ℝ) ≠ 0)) (norm_nonneg _) (norm_nonneg _) h1
  exact this

lemma norm_shiftAdjLM_le (x : L2N) : ‖shiftAdjLM x‖ ≤ ‖x‖ := by
  have h1 := norm_sq_eq_tsum (shiftAdjLM x)
  have h2 := norm_sq_eq_tsum x
  have hs : Summable fun n => ‖x n‖ ^ (2 : ℝ) := (memℓp_two_iff _).1 x.2
  rw [hs.tsum_eq_zero_add] at h2
  simp only [show ∀ n : ℕ, shiftAdjLM x n = x (n + 1) from fun _ => rfl] at h1
  have : ‖shiftAdjLM x‖ ^ (2 : ℝ) ≤ ‖x‖ ^ (2 : ℝ) := by
    rw [h1, h2]; linarith [Real.rpow_nonneg (norm_nonneg (x 0)) (2 : ℝ)]
  exact (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 this

/-- The unilateral shift `S` on `ℓ²(ℕ₀)`. -/
def shift : L2N →L[ℂ] L2N :=
  shiftLM.mkContinuous 1 fun x => by rw [one_mul, norm_shiftLM]

/-- The backward shift `S*` on `ℓ²(ℕ₀)`. -/
def shiftAdj : L2N →L[ℂ] L2N :=
  shiftAdjLM.mkContinuous 1 fun x => by rw [one_mul]; exact norm_shiftAdjLM_le x

@[simp] lemma shiftAdj_apply (x : L2N) (n : ℕ) : shiftAdj x n = x (n + 1) := rfl

/-- The adjoint of the shift is the backward shift. -/
theorem adjoint_shift : ContinuousLinearMap.adjoint shift = shiftAdj := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  have hsum : Summable (fun n : ℕ => ⟪x n, (shift y) n⟫_ℂ) :=
    lp.summable_inner x (shift y)
  rw [hsum.tsum_eq_zero_add]
  simp [show ∀ y : L2N, shift y 0 = 0 from fun _ => rfl,
    show ∀ (y : L2N) (n : ℕ), shift y (n + 1) = y n from fun _ _ => rfl]

/-- `star S = S*` (the star operation on bounded operators is the adjoint). -/
theorem star_shift : star shift = shiftAdj := adjoint_shift

/-- The vector `e₀`. -/
def e0 : L2N := lp.single 2 0 (1 : ℂ)

/-- The rank-one orthogonal projection `P₀ v = e₀ ⟪e₀, v⟫`. -/
def projE0 : L2N →L[ℂ] L2N := (innerSL ℂ e0).smulRight e0

lemma projE0_apply (v : L2N) (n : ℕ) : projE0 v n = if n = 0 then v 0 else 0 := by
  simp only [projE0, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, e0]
  rw [lp.inner_single_left]
  simp only [lp.coeFn_smul, Pi.smul_apply, lp.single_apply, smul_eq_mul]
  split_ifs with h
  · subst h; simp
  · simp [h]

/-- `[S*, S] = P₀`. -/
theorem commutator_shift : shiftAdj * shift - shift * shiftAdj = projE0 := by
  ext x n
  rw [projE0_apply]
  cases n with
  | zero =>
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, lp.coeFn_sub,
      Pi.sub_apply, shiftAdj_apply, show ∀ y : L2N, shift y 0 = 0 from fun _ => rfl]
    simp [show ∀ (y : L2N) (n : ℕ), shift y (n + 1) = y n from fun _ _ => rfl]
  | succ n => simp [show ∀ (y : L2N) (n : ℕ), shift y (n + 1) = y n from fun _ _ => rfl]

/-- `X = -(ik/2)(S + S*)`. -/
def opX (k : ℝ) : L2N →L[ℂ] L2N := (-(Complex.I * k / 2)) • (shift + shiftAdj)

/-- `Y = (k/2)(S* - S)`. -/
def opY (k : ℝ) : L2N →L[ℂ] L2N := ((k : ℂ) / 2) • (shiftAdj - shift)

lemma star_shiftAdj : star shiftAdj = shift := by rw [← star_shift, star_star]

/-- `X` is skew-adjoint. -/
theorem star_opX (k : ℝ) : star (opX k) = -opX k := by
  rw [opX, star_smul]
  have hsum : star (shift + shiftAdj) = shift + shiftAdj := by
    rw [ContinuousLinearMap.star_eq_adjoint, map_add,
      ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
      star_shift, star_shiftAdj]
    abel
  rw [hsum]
  rw [show -((-(Complex.I * k / 2)) • (shift + shiftAdj)) =
      (-(-(Complex.I * k / 2))) • (shift + shiftAdj) from (neg_smul _ _).symm]
  congr 1
  · simp [Complex.star_def, Complex.conj_ofReal]
    ring

/-- `Y` is skew-adjoint. -/
theorem star_opY (k : ℝ) : star (opY k) = -opY k := by
  rw [opY, star_smul]
  have hdiff : star (shiftAdj - shift) = -(shiftAdj - shift) := by
    rw [ContinuousLinearMap.star_eq_adjoint, map_sub,
      ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
      star_shiftAdj, star_shift]
    abel
  rw [hdiff]
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [smul_neg]
  have hscalar : (starRingEnd ℂ) ((k : ℂ) / 2) = (k : ℂ) / 2 := by
    rw [starRingEnd_apply, star_div₀, star_ofNat]
    simp [Complex.star_def, Complex.conj_ofReal]
  rw [hscalar]

/-- `[X, Y] = (i k² / 2) P₀`. -/
theorem commutator_opX_opY (k : ℝ) :
    opX k * opY k - opY k * opX k = (Complex.I * k ^ 2 / 2) • projE0 := by
  rw [← commutator_shift]
  simp only [opX, opY, smul_mul_smul]
  rw [mul_comm ((k : ℂ) / 2) (-(Complex.I * k / 2))]
  have hfactor :
      (-(Complex.I * k / 2) * ((k : ℂ) / 2)) •
          ((shift + shiftAdj) * (shiftAdj - shift)) -
        (-(Complex.I * k / 2) * ((k : ℂ) / 2)) •
          ((shiftAdj - shift) * (shift + shiftAdj)) =
      (-(Complex.I * k / 2) * ((k : ℂ) / 2)) •
        (((shift + shiftAdj) * (shiftAdj - shift)) -
          ((shiftAdj - shift) * (shift + shiftAdj))) := by
    exact (smul_sub _ _ _).symm
  rw [hfactor]
  have h : (shift + shiftAdj) * (shiftAdj - shift) - (shiftAdj - shift) * (shift + shiftAdj)
      = (2 : ℂ) • (shift * shiftAdj - shiftAdj * shift) := by
    rw [show (2 : ℂ) • (shift * shiftAdj - shiftAdj * shift) =
      (shift * shiftAdj - shiftAdj * shift) +
        (shift * shiftAdj - shiftAdj * shift) by
      exact two_smul ℂ (shift * shiftAdj - shiftAdj * shift)]
    simp only [add_mul, mul_sub, sub_mul, mul_add]
    abel
  rw [h, smul_smul]
  have h2 : shift * shiftAdj - shiftAdj * shift = -(shiftAdj * shift - shift * shiftAdj) := by
    abel
  rw [h2, smul_neg, ← neg_smul]
  congr 1
  ring

end

section

/-! ## Traces, Ky Fan partial traces and spectral tails -/

open scoped InnerProductSpace ComplexOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The diagonal sum `Σᵢ ⟪vᵢ, A vᵢ⟫` (real part, truncated at `0`). -/
def diagSum (A : E →L[ℂ] E) {n : ℕ} (v : Fin n → E) : ENNReal :=
  ∑ i, ENNReal.ofReal (RCLike.re ⟪v i, A (v i)⟫_ℂ)

/-- The trace of a positive operator, `tr A ∈ [0, ∞]`. -/
def posTrace (A : E →L[ℂ] E) : ENNReal :=
  ⨆ (n : ℕ) (v : Fin n → E) (_ : Orthonormal ℂ v), diagSum A v

/-- The Ky Fan partial trace `Φ_m(A)`: the sum of the `m` largest eigenvalues of a
positive trace-class operator, in its variational form. -/
def kyFan (m : ℕ) (A : E →L[ℂ] E) : ENNReal :=
  ⨆ (n : ℕ) (_ : n ≤ m) (v : Fin n → E) (_ : Orthonormal ℂ v), diagSum A v

/-- The spectral tail `τ_m(A) = tr A - Φ_m(A)`. -/
def spectralTail (m : ℕ) (A : E →L[ℂ] E) : ENNReal :=
  posTrace A - kyFan m A

/-- The trace norm `‖T‖_{𝒮₁}` (possibly `∞`). -/
def traceNorm (T : E →L[ℂ] E) : ENNReal :=
  ⨆ (n : ℕ) (u : Fin n → E) (v : Fin n → E) (_ : Orthonormal ℂ u) (_ : Orthonormal ℂ v),
    ∑ i, ‖⟪u i, T (v i)⟫_ℂ‖ₑ

/-- A positive trace-class operator. -/
def IsPosTraceClass (A : E →L[ℂ] E) : Prop :=
  A.IsPositive ∧ posTrace A < ⊤

/-- `Φ_m(A) ≤ tr A`. -/
theorem kyFan_le_posTrace (m : ℕ) (A : E →L[ℂ] E) : kyFan m A ≤ posTrace A :=
  iSup_le fun n => iSup_le fun _ => le_iSup (fun n => ⨆ (v : Fin n → E)
    (_ : Orthonormal ℂ v), diagSum A v) n

/-- `Φ_m` is monotone in `m`. -/
theorem kyFan_mono {m m' : ℕ} (h : m ≤ m') (A : E →L[ℂ] E) : kyFan m A ≤ kyFan m' A :=
  iSup_mono fun _ => iSup_mono' fun hn => ⟨hn.trans h, le_rfl⟩

lemma diagSum_smul (c : ℝ) (hc : 0 ≤ c) (A : E →L[ℂ] E) {n : ℕ} (v : Fin n → E) :
    diagSum ((c : ℂ) • A) v = ENNReal.ofReal c * diagSum A v := by
  unfold diagSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← ENNReal.ofReal_mul hc]
  congr 1
  simp

/-- Positive homogeneity `Φ_m(cA) = c Φ_m(A)`. -/
theorem kyFan_smul (m : ℕ) (c : ℝ) (hc : 0 ≤ c) (A : E →L[ℂ] E) :
    kyFan m ((c : ℂ) • A) = ENNReal.ofReal c * kyFan m A := by
  simp only [kyFan, diagSum_smul c hc, ENNReal.mul_iSup]

/-- Positive homogeneity of the trace. -/
theorem posTrace_smul (c : ℝ) (hc : 0 ≤ c) (A : E →L[ℂ] E) :
    posTrace ((c : ℂ) • A) = ENNReal.ofReal c * posTrace A := by
  simp only [posTrace, diagSum_smul c hc, ENNReal.mul_iSup]

/-- Positive homogeneity `τ_m(cA) = c τ_m(A)`. -/
theorem spectralTail_smul (m : ℕ) (c : ℝ) (hc : 0 ≤ c) (A : E →L[ℂ] E) :
    spectralTail m ((c : ℂ) • A) = ENNReal.ofReal c * spectralTail m A := by
  simp only [spectralTail, kyFan_smul m c hc, posTrace_smul c hc, ENNReal.mul_sub
    (fun _ _ => ENNReal.ofReal_ne_top)]

/-- `tr A = Φ_m(A) + τ_m(A)`. -/
theorem kyFan_add_spectralTail (m : ℕ) (A : E →L[ℂ] E) :
    kyFan m A + spectralTail m A = posTrace A :=
  add_tsub_cancel_of_le (kyFan_le_posTrace m A)

lemma diagSum_le_add (A B : E →L[ℂ] E) {n : ℕ} (v : Fin n → E) :
    diagSum A v ≤ diagSum B v + ∑ i, ‖⟪v i, (A - B) (v i)⟫_ℂ‖ₑ := by
  unfold diagSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : RCLike.re ⟪v i, A (v i)⟫_ℂ =
      RCLike.re ⟪v i, B (v i)⟫_ℂ + RCLike.re ⟪v i, (A - B) (v i)⟫_ℂ := by
    simp
  have h2 : RCLike.re ⟪v i, (A - B) (v i)⟫_ℂ ≤ ‖⟪v i, (A - B) (v i)⟫_ℂ‖ :=
    RCLike.re_le_norm _
  calc ENNReal.ofReal (RCLike.re ⟪v i, A (v i)⟫_ℂ)
      ≤ ENNReal.ofReal (RCLike.re ⟪v i, B (v i)⟫_ℂ + ‖⟪v i, (A - B) (v i)⟫_ℂ‖) := by
        apply ENNReal.ofReal_le_ofReal; linarith
    _ ≤ ENNReal.ofReal (RCLike.re ⟪v i, B (v i)⟫_ℂ) + ENNReal.ofReal ‖⟪v i, (A - B) (v i)⟫_ℂ‖ :=
        ENNReal.ofReal_add_le
    _ = _ := by rw [ofReal_norm_eq_enorm]

/-- The same Lipschitz bound for the trace. -/
theorem posTrace_le_add_traceNorm (A B : E →L[ℂ] E) :
    posTrace A ≤ posTrace B + traceNorm (A - B) := by
  refine iSup_le fun n => iSup_le fun v => iSup_le fun hv => ?_
  refine (diagSum_le_add A B v).trans (add_le_add ?_ ?_)
  · exact le_iSup_of_le n (le_iSup_of_le v (le_iSup_of_le hv le_rfl))
  · exact le_iSup_of_le n (le_iSup_of_le v (le_iSup_of_le v (le_iSup_of_le hv
      (le_iSup_of_le hv le_rfl))))

end

section

/-! ## Positive unitary paths and eigenphase counting -/

open scoped InnerProductSpace
open MeasureTheory Set Filter Topology Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The generator `L(t) = -i U(t)* U'(t)` of a path of operators on `[0, b]`. -/
def generator (U : ℝ → E →L[ℂ] E) (b t : ℝ) : E →L[ℂ] E :=
  (-Complex.I) • (star (U t) * derivWithin U (Icc 0 b) t)

/-- An admissible positive unitary path on `[0, b]`. -/
structure IsAdmissiblePath (b : ℝ) (U : ℝ → E →L[ℂ] E) : Prop where
  pos : 0 < b
  unitary : ∀ t ∈ Icc 0 b, U t ∈ unitary (E →L[ℂ] E)
  start : U 0 = 1
  contDiff : ContDiffOn ℝ 1 U (Icc 0 b)
  /-- the generator is positive and trace class -/
  posTraceClass : ∀ t ∈ Icc 0 b, IsPosTraceClass (generator U b t)
  /-- the generator is continuous in trace norm -/
  traceNorm_continuous : ∀ t ∈ Icc 0 b,
    Tendsto (fun s => traceNorm (generator U b s - generator U b t)) (𝓝[Icc 0 b] t) (𝓝 0)
  /-- strict positivity of the generator for positive times -/
  strictPos : ∀ t ∈ Ioc 0 b, ∀ v : E, v ≠ 0 → 0 < RCLike.re ⟪v, generator U b t v⟫_ℂ

/-- The multiplicity `dim ker (U(t) - e^{iα})` of `e^{iα}` as an eigenvalue of `U(t)`. -/
def crossingMult (U : ℝ → E →L[ℂ] E) (α t : ℝ) : ℕ∞ :=
  (Module.rank ℂ (LinearMap.ker
    ((U t - Complex.exp (α * Complex.I) • (1 : E →L[ℂ] E)) : E →ₗ[ℂ] E))).toENat

/-- The crossing count `c_α(I)`: the total multiplicity of crossings of the level `α`
at times in the set `I` (possibly `⊤`). -/
def crossingCount (U : ℝ → E →L[ℂ] E) (α : ℝ) (I : Set ℝ) : ℕ∞ :=
  ⨆ (s : Finset ℝ) (_ : ↑s ⊆ I), ∑ t ∈ s, crossingMult U α t

end

section

/-! ## Boundary transport and the area identity

For `F` holomorphic near the closed unit disk and `k > 0`: `γ_r(θ) = F(r e^{iθ})`;
`W_r` solves `∂_θ W_r = C_θ W_r`, `W_r(0) = I`, and `R_r` solves `∂_r R_r = B_r R_r`, `R_0 = I`;
`V_r = W_r(2π)`, `H_r = R_r^* V_r R_r`, `U_r = H_r^*`, and `L_{r,k}` is the generator of `r ↦ U_r`.
-/

open scoped InnerProductSpace
open MeasureTheory Set Real Metric Complex

open Classical in
/-- A solution of the linear operator equation `W' = C W`, `W(0) = I` on the set `T`
(chosen when one exists; `fun _ => I` otherwise). -/
def opODESol (C : ℝ → L2N →L[ℂ] L2N) (T : Set ℝ) : ℝ → L2N →L[ℂ] L2N :=
  if h : ∃ W : ℝ → L2N →L[ℂ] L2N, W 0 = 1 ∧ ∀ t ∈ T, HasDerivWithinAt W (C t * W t) T t
  then h.choose else fun _ => 1

variable (F : ℂ → ℂ) (k : ℝ)

/-- `∂_θ γ_r(θ) = i r e^{iθ} F'(r e^{iθ})`. -/
def dAng (r θ : ℝ) : ℂ := I * r * exp (θ * I) * deriv F (r * exp (θ * I))

/-- The Jacobian `J(r, θ) = r |F'(r e^{iθ})|²`. -/
def jac (r θ : ℝ) : ℝ := r * ‖deriv F (r * exp (θ * I))‖ ^ 2

/-- `C_θ = x_θ X + y_θ Y`. -/
def coefAng (r θ : ℝ) : L2N →L[ℂ] L2N :=
  ((dAng F r θ).re : ℂ) • opX k + ((dAng F r θ).im : ℂ) • opY k

/-- `B_r = x_r X + y_r Y` at `θ = 0`, where `∂_r γ_r(0) = F'(r)`. -/
def coefRad (r : ℝ) : L2N →L[ℂ] L2N :=
  ((deriv F r).re : ℂ) • opX k + ((deriv F r).im : ℂ) • opY k

/-- The angular transport `W_r(θ)`. -/
def holW (r : ℝ) : ℝ → L2N →L[ℂ] L2N := opODESol (coefAng F k r) (Icc 0 (2 * π))

/-- The radial transport `R_r` (on `0 ≤ r < 1`). -/
def holR : ℝ → L2N →L[ℂ] L2N := opODESol (coefRad F k) (Ico 0 1)

/-- The holonomy `V_r = W_r(2π)`. -/
def holV (r : ℝ) : L2N →L[ℂ] L2N := holW F k r (2 * π)

/-- The based holonomy `H_r = R_r^* V_r R_r`. -/
def holH (r : ℝ) : L2N →L[ℂ] L2N := star (holR F k r) * holV F k r * holR F k r

/-- The unitary path `U_r = H_r^*`. -/
def holU (r : ℝ) : L2N →L[ℂ] L2N := star (holH F k r)

/-- `Q_{r,k} = (k²/2) R_r^* (∫₀^{2π} J(r,θ) W_r(θ)^* P₀ W_r(θ) dθ) R_r`. -/
def holQ (r : ℝ) : L2N →L[ℂ] L2N :=
  ((k ^ 2 / 2 : ℝ) : ℂ) • (star (holR F k r) *
    (∫ θ in (0 : ℝ)..(2 * π), ((jac F r θ : ℝ) : ℂ) •
      (star (holW F k r θ) * projE0 * holW F k r θ)) * holR F k r)

/-- The generator `L_{r,k} = H_r Q_{r,k} H_r^*`. -/
def holL (r : ℝ) : L2N →L[ℂ] L2N := holH F k r * holQ F k r * star (holH F k r)

end

section

/-! ## Linear operator differential equations -/

open MeasureTheory Set Filter Topology intervalIntegral

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]

/-- The terms of the Picard series. -/
def picardTerm (C : ℝ → 𝔸) : ℕ → ℝ → 𝔸
  | 0 => fun _ => 1
  | n + 1 => fun t => ∫ s in (0 : ℝ)..t, C s * picardTerm C n s

lemma picardTerm_zero (C : ℝ → 𝔸) (t : ℝ) : picardTerm C 0 t = 1 := rfl

lemma picardTerm_succ (C : ℝ → 𝔸) (n : ℕ) (t : ℝ) :
    picardTerm C (n + 1) t = ∫ s in (0 : ℝ)..t, C s * picardTerm C n s := rfl

lemma continuous_picardTerm {C : ℝ → 𝔸} (hC : Continuous C) (n : ℕ) :
    Continuous (picardTerm C n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have : Continuous fun s => C s * picardTerm C n s := hC.mul ih
    exact intervalIntegral.continuous_primitive (fun a b => this.intervalIntegrable a b) 0

/-- `‖∫₀ᵗ f‖ ≤ K |t|ⁿ⁺¹ / (n+1)` when `‖f s‖ ≤ K |s|ⁿ`. -/
lemma norm_integral_le_pow {f : ℝ → 𝔸} {K : ℝ} {n : ℕ}
    (hb : ∀ s, ‖f s‖ ≤ K * |s| ^ n) (t : ℝ) :
    ‖∫ s in (0 : ℝ)..t, f s‖ ≤ K * |t| ^ (n + 1) / (n + 1) := by
  rcases le_total 0 t with ht | ht
  · have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (f := f)
      (g := fun s => K * s ^ n) ht
      (Eventually.of_forall fun s hs => by
        have := hb s
        rwa [abs_of_pos hs.1] at this)
      ((continuous_const.mul (continuous_pow n)).intervalIntegrable _ _)
    rw [intervalIntegral.integral_const_mul, integral_pow] at h
    rw [abs_of_nonneg ht]
    calc _ ≤ _ := h
      _ = K * t ^ (n + 1) / (n + 1) := by
        rw [zero_pow (Nat.succ_ne_zero n), sub_zero]; ring
  · rw [intervalIntegral.integral_symm, norm_neg]
    have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (f := f)
      (g := fun s => K * (-s) ^ n) ht
      (Eventually.of_forall fun s hs => by
        have := hb s
        rwa [abs_of_nonpos hs.2] at this)
      ((continuous_const.mul ((continuous_neg).pow n)).intervalIntegrable _ _)
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_neg (fun s => s ^ n), integral_pow] at h
    rw [abs_of_nonpos ht]
    calc _ ≤ _ := h
      _ = K * (-t) ^ (n + 1) / (n + 1) := by
        rw [neg_zero, zero_pow (Nat.succ_ne_zero n), sub_zero]; ring

lemma norm_picardTerm_le {C : ℝ → 𝔸} {M : ℝ} (hM : ∀ t, ‖C t‖ ≤ M)
    (n : ℕ) (t : ℝ) :
    ‖picardTerm C n t‖ ≤ ‖(1 : 𝔸)‖ * (M * |t|) ^ n / n.factorial := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  induction n generalizing t with
  | zero => simp [picardTerm_zero]
  | succ n ih =>
    rw [picardTerm_succ]
    have hb : ∀ s, ‖C s * picardTerm C n s‖ ≤
        (M * (‖(1 : 𝔸)‖ * M ^ n / n.factorial)) * |s| ^ n := by
      intro s
      calc ‖C s * picardTerm C n s‖ ≤ ‖C s‖ * ‖picardTerm C n s‖ := norm_mul_le _ _
        _ ≤ M * (‖(1 : 𝔸)‖ * (M * |s|) ^ n / n.factorial) :=
          mul_le_mul (hM s) (ih s) (norm_nonneg _) hM0
        _ = _ := by rw [mul_pow]; ring
    have := norm_integral_le_pow hb t
    calc _ ≤ _ := this
      _ = ‖(1 : 𝔸)‖ * (M * |t|) ^ (n + 1) / (n + 1).factorial := by
        rw [Nat.factorial_succ]
        push_cast
        have : (n.factorial : ℝ) ≠ 0 := by positivity
        field_simp
        ring

lemma norm_picardTerm_le_of_abs_le {C : ℝ → 𝔸} {M : ℝ}
    (hM : ∀ t, ‖C t‖ ≤ M) {T : ℝ} (n : ℕ) {t : ℝ} (ht : |t| ≤ T) :
    ‖picardTerm C n t‖ ≤ ‖(1 : 𝔸)‖ * ((M * T) ^ n / n.factorial) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  calc ‖picardTerm C n t‖ ≤ ‖(1 : 𝔸)‖ * (M * |t|) ^ n / n.factorial :=
        norm_picardTerm_le hM n t
    _ ≤ ‖(1 : 𝔸)‖ * (M * T) ^ n / n.factorial := by gcongr
    _ = _ := by ring

variable [CompleteSpace 𝔸]

/-- The solution `W(t) = Σₙ Pₙ(t)` of `W' = C W`, `W(0) = 1`. -/
def picardSol (C : ℝ → 𝔸) (t : ℝ) : 𝔸 := ∑' n, picardTerm C n t

lemma summable_picardTerm {C : ℝ → 𝔸} {M : ℝ} (hM : ∀ t, ‖C t‖ ≤ M)
    (t : ℝ) : Summable fun n => picardTerm C n t :=
  Summable.of_norm_bounded ((Real.summable_pow_div_factorial (M * |t|)).mul_left ‖(1 : 𝔸)‖)
    fun n => by
      have := norm_picardTerm_le hM n t
      rwa [mul_div_assoc] at this

lemma continuous_picardSol {C : ℝ → 𝔸} (hC : Continuous C) {M : ℝ} (hM : ∀ t, ‖C t‖ ≤ M) :
    Continuous (picardSol C) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hcont : ContinuousOn (picardSol C) (Icc (-(|t| + 1)) (|t| + 1)) := by
    apply continuousOn_tsum (fun n => (continuous_picardTerm hC n).continuousOn)
      ((Real.summable_pow_div_factorial (M * (|t| + 1))).mul_left ‖(1 : 𝔸)‖)
    intro n s hs
    exact norm_picardTerm_le_of_abs_le hM n (abs_le.2 hs)
  apply hcont.continuousAt
  apply Icc_mem_nhds
  · have := abs_nonneg t; have := neg_abs_le t; linarith
  · have := le_abs_self t; linarith

/-- The integral equation `W(t) = 1 + ∫₀ᵗ C W`. -/
lemma picardSol_eq {C : ℝ → 𝔸} (hC : Continuous C) {M : ℝ} (hM : ∀ t, ‖C t‖ ≤ M) (t : ℝ) :
    picardSol C t = 1 + ∫ s in (0 : ℝ)..t, C s * picardSol C s := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  unfold picardSol
  rw [(summable_picardTerm hM t).tsum_eq_zero_add, picardTerm_zero]
  congr 1
  simp only [picardTerm_succ]
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := 0) (b := t) (F := fun n s => C s * picardTerm C n s)
    (f := fun s => C s * ∑' n, picardTerm C n s)
    (fun n s => M * (‖(1 : 𝔸)‖ * ((M * |t|) ^ n / n.factorial)))
    (fun n => (hC.mul (continuous_picardTerm hC n)).aestronglyMeasurable)
    (fun n => Eventually.of_forall fun s hs => by
      have hst : |s| ≤ |t| := by
        rcases hs with ⟨h1, h2⟩
        rcases le_total 0 t with h | h
        · simp only [min_eq_left h, max_eq_right h] at h1 h2
          rw [abs_of_pos h1, abs_of_nonneg h]; exact h2
        · simp only [min_eq_right h, max_eq_left h] at h1 h2
          rw [abs_of_nonpos h2, abs_of_nonpos h]; linarith
      calc ‖C s * picardTerm C n s‖ ≤ ‖C s‖ * ‖picardTerm C n s‖ := norm_mul_le _ _
        _ ≤ _ := mul_le_mul (hM s) (norm_picardTerm_le_of_abs_le hM n hst)
            (norm_nonneg _) hM0)
    (Eventually.of_forall fun s _ =>
      ((Real.summable_pow_div_factorial (M * |t|)).mul_left _).mul_left _)
    _root_.intervalIntegrable_const
    (Eventually.of_forall fun s _ =>
      ((summable_picardTerm hM s).hasSum.mul_left (C s)))
  exact hsum.tsum_eq

/-- **Existence.** The Picard series solves `W' = C W`, `W(0) = 1`. -/
theorem hasDerivAt_picardSol {C : ℝ → 𝔸} (hC : Continuous C) {M : ℝ} (hM : ∀ t, ‖C t‖ ≤ M)
    (t : ℝ) : HasDerivAt (picardSol C) (C t * picardSol C t) t := by
  have hfun : picardSol C = fun t => 1 + ∫ s in (0 : ℝ)..t, C s * picardSol C s :=
    funext (picardSol_eq hC hM)
  rw [hfun]
  have hc : Continuous fun s => C s * picardSol C s := hC.mul (continuous_picardSol hC hM)
  have := (hc.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add 1
  convert this using 1
  rw [← hfun]

lemma picardSol_zero {C : ℝ → 𝔸} (hC : Continuous C) {M : ℝ} (hM : ∀ t, ‖C t‖ ≤ M) :
    picardSol C 0 = 1 := by
  rw [picardSol_eq hC hM]; simp

omit [CompleteSpace 𝔸] in
/-- Uniqueness for Lipschitz ODEs on `[0, b]`, with derivatives taken within `[0, b]`. -/
theorem eqOn_of_ode_Icc {v : ℝ → 𝔸 → 𝔸} {K : NNReal} {b : ℝ}
    (hv : ∀ t ∈ Icc 0 b, LipschitzWith K (v t)) {W V : ℝ → 𝔸}
    (hW : ∀ t ∈ Icc 0 b, HasDerivWithinAt W (v t (W t)) (Icc 0 b) t)
    (hV : ∀ t ∈ Icc 0 b, HasDerivWithinAt V (v t (V t)) (Icc 0 b) t) (h0 : W 0 = V 0) :
    EqOn W V (Icc 0 b) := by
  have hmem : ∀ t ∈ Ico 0 b, Icc 0 b ∈ 𝓝[Ici t] t := fun t ht =>
    mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)
  refine ODE_solution_unique_of_mem_Icc_right (s := fun _ => univ) (K := K)
    (fun t ht => (hv t (Ico_subset_Icc_self ht)).lipschitzOnWith)
    (fun t ht => (hW t ht).continuousWithinAt)
    (fun t ht => (hW t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (hmem t ht))
    (fun _ _ => mem_univ _)
    (fun t ht => (hV t ht).continuousWithinAt)
    (fun t ht => (hV t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (hmem t ht))
    (fun _ _ => mem_univ _) h0

omit [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] in
lemma lipschitzWith_mul_left {M : ℝ} {c : 𝔸} (hc : ‖c‖ ≤ M) :
    LipschitzWith M.toNNReal (fun x : 𝔸 => c * x) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, ← mul_sub, Real.coe_toNNReal']
  calc ‖c * (x - y)‖ ≤ ‖c‖ * ‖x - y‖ := norm_mul_le _ _
    _ ≤ max M 0 * ‖x - y‖ := by gcongr; exact hc.trans (le_max_left _ _)

omit [CompleteSpace 𝔸] in
/-- **Uniqueness.** Two solutions of `W' = C W` on `[0, b]` with the same
initial value agree. -/
theorem eqOn_of_linear_ode_Icc {C : ℝ → 𝔸} {b : ℝ} (hC : ContinuousOn C (Icc 0 b))
    {W V : ℝ → 𝔸}
    (hW : ∀ t ∈ Icc 0 b, HasDerivWithinAt W (C t * W t) (Icc 0 b) t)
    (hV : ∀ t ∈ Icc 0 b, HasDerivWithinAt V (C t * V t) (Icc 0 b) t) (h0 : W 0 = V 0) :
    EqOn W V (Icc 0 b) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := b)).exists_bound_of_continuousOn hC
  exact eqOn_of_ode_Icc (v := fun t x => C t * x) (fun t ht => lipschitzWith_mul_left (hM t ht))
    hW hV h0

/-- **Existence on `[0, b]`.** -/
theorem exists_linear_ode_Icc {C : ℝ → 𝔸} {b : ℝ} (hb : 0 ≤ b) (hC : ContinuousOn C (Icc 0 b)) :
    ∃ W : ℝ → 𝔸, W 0 = 1 ∧ ∀ t ∈ Icc 0 b, HasDerivAt W (C t * W t) t := by
  set p : ℝ → ℝ := fun t => max 0 (min b t) with hp
  have hpmem : ∀ t, p t ∈ Icc 0 b := fun t => ⟨le_max_left _ _, max_le hb (min_le_left _ _)⟩
  have hpid : ∀ t ∈ Icc 0 b, p t = t := fun t ht => by
    simp only [hp, min_eq_right ht.2, max_eq_right ht.1]
  set C' : ℝ → 𝔸 := fun t => C (p t) with hC'
  have hC'c : Continuous C' :=
    hC.comp_continuous (continuous_const.max (continuous_const.min continuous_id)) hpmem
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := b)).exists_bound_of_continuousOn hC
  have hM' : ∀ t, ‖C' t‖ ≤ M := fun t => hM _ (hpmem t)
  refine ⟨picardSol C', picardSol_zero hC'c hM', fun t ht => ?_⟩
  have := hasDerivAt_picardSol hC'c hM' t
  simpa [hC', hpid t ht] using this

/-- Existence on `[0, 1)` for a coefficient continuous on `[0, 1)` (possibly unbounded). -/
theorem exists_linear_ode_Ico {C : ℝ → 𝔸} (hC : ContinuousOn C (Ico 0 1)) :
    ∃ W : ℝ → 𝔸, W 0 = 1 ∧ ∀ t ∈ Ico 0 1, HasDerivWithinAt W (C t * W t) (Ico 0 1) t := by
  have hsol : ∀ b ∈ Ico (0 : ℝ) 1, ∃ S : ℝ → 𝔸, S 0 = 1 ∧
      ∀ t ∈ Icc 0 b, HasDerivAt S (C t * S t) t := fun b hb =>
    exists_linear_ode_Icc hb.1 (hC.mono (Icc_subset_Ico_right hb.2))
  choose! S hS0 hS using hsol
  have hagree : ∀ b₁ ∈ Ico (0 : ℝ) 1, ∀ b₂ ∈ Ico (0 : ℝ) 1, b₁ ≤ b₂ →
      ∀ t ∈ Icc 0 b₁, S b₁ t = S b₂ t := by
    intro b₁ hb₁ b₂ hb₂ h12 t ht
    exact eqOn_of_linear_ode_Icc (hC.mono (Icc_subset_Ico_right hb₁.2))
      (fun s hs => (hS b₁ hb₁ s hs).hasDerivWithinAt)
      (fun s hs => (hS b₂ hb₂ s ⟨hs.1, hs.2.trans h12⟩).hasDerivWithinAt)
      ((hS0 b₁ hb₁).trans (hS0 b₂ hb₂).symm) ht
  set β : ℝ → ℝ := fun t => (t + 1) / 2 with hβ
  have hβmem : ∀ t ∈ Ico (0 : ℝ) 1, β t ∈ Ico (0 : ℝ) 1 := fun t ht =>
    ⟨by simp only [hβ]; linarith [ht.1], by simp only [hβ]; linarith [ht.2]⟩
  have hβle : ∀ t ∈ Ico (0 : ℝ) 1, t ≤ β t := fun t ht => by simp only [hβ]; linarith [ht.2]
  refine ⟨fun t => S (β t) t, ?_, fun t ht => ?_⟩
  · exact hS0 _ (hβmem 0 ⟨le_rfl, one_pos⟩)
  · have hev : (fun s => S (β s) s) =ᶠ[𝓝[Ico 0 1] t] S (β t) := by
      have hlt : t < β t := by simp only [hβ]; linarith [ht.2]
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hlt)] with s hs hs'
      rcases le_total (β s) (β t) with h | h
      · exact hagree _ (hβmem s hs) _ (hβmem t ht) h s ⟨hs.1, hβle s hs⟩
      · exact (hagree _ (hβmem t ht) _ (hβmem s hs) h s ⟨hs.1, le_of_lt hs'⟩).symm
    have hd := (hS (β t) (hβmem t ht) t ⟨ht.1, hβle t ht⟩).hasDerivWithinAt (s := Ico 0 1)
    exact hd.congr_of_eventuallyEq hev rfl

section Unitary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

lemma lipschitzWith_commutator {M : ℝ} {c : E →L[ℂ] E} (hc : ‖c‖ ≤ M) :
    LipschitzWith (2 * M).toNNReal (fun x : E →L[ℂ] E => c * x - x * c) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal']
  have h : c * x - x * c - (c * y - y * c) = c * (x - y) - (x - y) * c := by
    simp only [mul_sub, sub_mul]; abel
  rw [h]
  calc ‖c * (x - y) - (x - y) * c‖ ≤ ‖c * (x - y)‖ + ‖(x - y) * c‖ := norm_sub_le _ _
    _ ≤ ‖c‖ * ‖x - y‖ + ‖x - y‖ * ‖c‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖c‖ * ‖x - y‖ := by ring
    _ ≤ max (2 * M) 0 * ‖x - y‖ := by
        gcongr; exact (by linarith : 2 * ‖c‖ ≤ 2 * M).trans (le_max_left _ _)

/-- **Unitarity.** If `C(t)` is skew-adjoint, the solution of `W' = C W`,
`W(0) = 1` on `[0, b]` is unitary. -/
theorem unitary_of_linear_ode_Icc {C : ℝ → E →L[ℂ] E} {b : ℝ} (hC : ContinuousOn C (Icc 0 b))
    (hskew : ∀ t ∈ Icc 0 b, star (C t) = -C t) {W : ℝ → E →L[ℂ] E} (hW0 : W 0 = 1)
    (hW : ∀ t ∈ Icc 0 b, HasDerivWithinAt W (C t * W t) (Icc 0 b) t) :
    ∀ t ∈ Icc 0 b, W t ∈ unitary (E →L[ℂ] E) := by
  have hmem : ∀ t ∈ Ico 0 b, Icc 0 b ∈ 𝓝[Ici t] t := fun t ht =>
    mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)
  have hWc : ContinuousOn W (Icc 0 b) := fun t ht => (hW t ht).continuousWithinAt
  -- `W* W = 1`
  have h1 : ∀ t ∈ Icc 0 b, star (W t) * W t = 1 := by
    have hcont : ContinuousOn (fun t => star (W t) * W t) (Icc 0 b) :=
      (continuous_star.comp_continuousOn hWc).mul hWc
    have hderiv : ∀ t ∈ Ico 0 b, HasDerivWithinAt (fun t => star (W t) * W t) 0 (Ici t) t := by
      intro t ht
      have ht' := Ico_subset_Icc_self ht
      have hd := ((hW t ht').star).mul (hW t ht')
      have h0 : star (C t * W t) * W t + star (W t) * (C t * W t) = 0 := by
        rw [star_mul, hskew t ht']
        simp only [mul_neg, neg_mul, mul_assoc]
        abel
      rw [h0] at hd
      exact hd.mono_of_mem_nhdsWithin (hmem t ht)
    intro t ht
    have := constant_of_has_deriv_right_zero hcont hderiv t ht
    rw [this, hW0, star_one, one_mul]
  -- `W W* = 1`
  have h2 : ∀ t ∈ Icc 0 b, W t * star (W t) = 1 := by
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := b)).exists_bound_of_continuousOn hC
    have hY : ∀ t ∈ Icc 0 b, HasDerivWithinAt (fun t => W t * star (W t))
        (C t * (W t * star (W t)) - (W t * star (W t)) * C t) (Icc 0 b) t := by
      intro t ht
      have hd := (hW t ht).mul ((hW t ht).star)
      convert hd using 1
      rw [star_mul, hskew t ht]
      simp only [mul_neg, mul_assoc]
      abel
    have hone : ∀ t ∈ Icc 0 b, HasDerivWithinAt (fun _ => (1 : E →L[ℂ] E))
        (C t * 1 - 1 * C t) (Icc 0 b) t := by
      intro t _
      rw [mul_one, one_mul, sub_self]
      exact hasDerivWithinAt_const _ _ _
    have := eqOn_of_ode_Icc (v := fun t Y => C t * Y - Y * C t)
      (fun t ht => lipschitzWith_commutator (hM t ht)) hY hone (by simp [hW0])
    exact fun t ht => this ht
  intro t ht
  exact Unitary.mem_iff.2 ⟨h1 t ht, h2 t ht⟩

end Unitary

end

section

/-! ## Unitarity of the boundary transport -/

open scoped InnerProductSpace
open MeasureTheory Set Real Metric Complex

/-- `opODESol` is a solution whenever a solution exists. -/
lemma opODESol_spec {C : ℝ → L2N →L[ℂ] L2N} {T : Set ℝ}
    (h : ∃ W : ℝ → L2N →L[ℂ] L2N, W 0 = 1 ∧ ∀ t ∈ T, HasDerivWithinAt W (C t * W t) T t) :
    opODESol C T 0 = 1 ∧
      ∀ t ∈ T, HasDerivWithinAt (opODESol C T) (C t * opODESol C T t) T t := by
  unfold opODESol
  rw [dif_pos h]
  exact h.choose_spec

lemma star_real_smul_opX_add (k a b : ℝ) :
    star ((a : ℂ) • opX k + (b : ℂ) • opY k) = -((a : ℂ) • opX k + (b : ℂ) • opY k) := by
  rw [ContinuousLinearMap.star_eq_adjoint, map_add,
    ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
    star_smul, star_smul, star_opX, star_opY]
  simp only [Complex.star_def, Complex.conj_ofReal, smul_neg, neg_add]

variable (F : ℂ → ℂ) (k : ℝ)

lemma star_coefAng (r θ : ℝ) : star (coefAng F k r θ) = -coefAng F k r θ :=
  star_real_smul_opX_add k _ _

lemma star_coefRad (r : ℝ) : star (coefRad F k r) = -coefRad F k r :=
  star_real_smul_opX_add k _ _

variable {F}

lemma continuous_coefAng {U : Set ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) {r : ℝ}
    (hr : ∀ θ : ℝ, (r : ℂ) * exp (θ * I) ∈ U) : Continuous (coefAng F k r) := by
  have hdF : ContinuousOn (deriv F) U := (hF.deriv hU).continuousOn
  have hγ : Continuous fun θ : ℝ => (r : ℂ) * exp (θ * I) := by fun_prop
  have hd : Continuous fun θ : ℝ => dAng F r θ := by
    unfold dAng
    exact (continuous_const.mul (by fun_prop)).mul (hdF.comp_continuous hγ hr)
  unfold coefAng
  have h1 : Continuous fun θ => ((dAng F r θ).re : ℂ) :=
    continuous_ofReal.comp (continuous_re.comp hd)
  have h2 : Continuous fun θ => ((dAng F r θ).im : ℂ) :=
    continuous_ofReal.comp (continuous_im.comp hd)
  exact (h1.smul continuous_const).add (h2.smul continuous_const)

lemma continuousOn_coefRad {U : Set ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    (hseg : ∀ r ∈ Ico (0 : ℝ) 1, (r : ℂ) ∈ U) : ContinuousOn (coefRad F k) (Ico 0 1) := by
  have hdF : ContinuousOn (deriv F) U := (hF.deriv hU).continuousOn
  have hd : ContinuousOn (fun r : ℝ => deriv F r) (Ico 0 1) :=
    hdF.comp continuous_ofReal.continuousOn hseg
  unfold coefRad
  have h1 : ContinuousOn (fun r : ℝ => ((deriv F r).re : ℂ)) (Ico 0 1) :=
    continuous_ofReal.comp_continuousOn (continuous_re.comp_continuousOn hd)
  have h2 : ContinuousOn (fun r : ℝ => ((deriv F r).im : ℂ)) (Ico 0 1) :=
    continuous_ofReal.comp_continuousOn (continuous_im.comp_continuousOn hd)
  exact (h1.smul continuousOn_const).add (h2.smul continuousOn_const)

/-- The angular transport `W_r` solves its equation on `[0, 2π]`. -/
lemma holW_spec {U : Set ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) {r : ℝ}
    (hr : ∀ θ : ℝ, (r : ℂ) * exp (θ * I) ∈ U) :
    holW F k r 0 = 1 ∧ ∀ θ ∈ Icc 0 (2 * π),
      HasDerivWithinAt (holW F k r) (coefAng F k r θ * holW F k r θ) (Icc 0 (2 * π)) θ := by
  obtain ⟨W, hW0, hW⟩ := exists_linear_ode_Icc (by positivity : (0 : ℝ) ≤ 2 * π)
    (continuous_coefAng k hU hF hr).continuousOn
  exact opODESol_spec ⟨W, hW0, fun t ht => (hW t ht).hasDerivWithinAt⟩

/-- The radial transport `R_r` solves its equation on `[0, 1)`. -/
lemma holR_spec {U : Set ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    (hseg : ∀ r ∈ Ico (0 : ℝ) 1, (r : ℂ) ∈ U) :
    holR F k 0 = 1 ∧ ∀ r ∈ Ico 0 1,
      HasDerivWithinAt (holR F k) (coefRad F k r * holR F k r) (Ico 0 1) r := by
  obtain ⟨W, hW0, hW⟩ := exists_linear_ode_Ico (continuousOn_coefRad k hU hF hseg)
  exact opODESol_spec ⟨W, hW0, hW⟩

/-- `W_r(θ)` is unitary for `θ ∈ [0, 2π]`. -/
theorem holW_mem_unitary {U : Set ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) {r : ℝ}
    (hr : ∀ θ : ℝ, (r : ℂ) * exp (θ * I) ∈ U) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    holW F k r θ ∈ unitary (L2N →L[ℂ] L2N) := by
  obtain ⟨h0, hd⟩ := holW_spec k hU hF hr
  exact unitary_of_linear_ode_Icc (continuous_coefAng k hU hF hr).continuousOn
    (fun t _ => star_coefAng F k r t) h0 hd θ hθ

/-- `R_r` is unitary for `r ∈ [0, 1)`. -/
theorem holR_mem_unitary {U : Set ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    (hseg : ∀ r ∈ Ico (0 : ℝ) 1, (r : ℂ) ∈ U) {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) :
    holR F k r ∈ unitary (L2N →L[ℂ] L2N) := by
  obtain ⟨h0, hd⟩ := holR_spec k hU hF hseg
  have hsub : Icc 0 r ⊆ Ico (0 : ℝ) 1 := Icc_subset_Ico_right hr.2
  exact unitary_of_linear_ode_Icc ((continuousOn_coefRad k hU hF hseg).mono hsub)
    (fun t _ => star_coefRad F k t) h0
    (fun t ht => (hd t (hsub ht)).mono hsub) r ⟨hr.1, le_rfl⟩

/-- `V_r`, `H_r` and `U_r` are unitary for `r ∈ [0, 1)`. -/
theorem holU_mem_unitary {U : Set ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    (hseg : ∀ r ∈ Ico (0 : ℝ) 1, (r : ℂ) ∈ U) {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1)
    (hcirc : ∀ θ : ℝ, (r : ℂ) * exp (θ * I) ∈ U) :
    holV F k r ∈ unitary (L2N →L[ℂ] L2N) ∧ holH F k r ∈ unitary (L2N →L[ℂ] L2N) ∧
      holU F k r ∈ unitary (L2N →L[ℂ] L2N) := by
  have hV : holV F k r ∈ unitary (L2N →L[ℂ] L2N) :=
    holW_mem_unitary k hU hF hcirc ⟨by positivity, le_rfl⟩
  have hR := holR_mem_unitary k hU hF hseg hr
  have hH : holH F k r ∈ unitary (L2N →L[ℂ] L2N) :=
    mul_mem (mul_mem (Unitary.star_mem hR) hV) hR
  exact ⟨hV, hH, Unitary.star_mem hH⟩

/-- `W_0(θ) = I` for `θ ∈ [0, 2π]`. -/
theorem holW_zero {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) : holW F k 0 θ = 1 := by
  have hC : coefAng F k 0 = fun _ => 0 := by
    funext θ
    unfold coefAng dAng
    norm_num
    change (0 : ℝ) • opX k + (0 : ℝ) • opY k = 0
    ext x n
    simp
  have hspec := opODESol_spec (C := coefAng F k 0) (T := Icc 0 (2 * π))
    ⟨fun _ => 1, rfl, fun t _ => by
      rw [hC]
      change HasDerivWithinAt (fun _ : ℝ => (1 : L2N →L[ℂ] L2N))
        (0 : L2N →L[ℂ] L2N) (Icc 0 (2 * π)) t
      exact hasDerivWithinAt_const _ _ _⟩
  have := eqOn_of_linear_ode_Icc (C := coefAng F k 0) (by rw [hC]; exact continuousOn_const)
    hspec.2 (V := fun _ => 1) (fun t _ => by
      rw [hC]
      change HasDerivWithinAt (fun _ : ℝ => (1 : L2N →L[ℂ] L2N))
        (0 : L2N →L[ℂ] L2N) (Icc 0 (2 * π)) t
      exact hasDerivWithinAt_const _ _ _)
    hspec.1 hθ
  exact this

/-- `V_0 = H_0 = U_0 = I`. -/
theorem holU_zero {U : Set ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    (hseg : ∀ r ∈ Ico (0 : ℝ) 1, (r : ℂ) ∈ U) :
    holV F k 0 = 1 ∧ holH F k 0 = 1 ∧ holU F k 0 = 1 := by
  have hV : holV F k 0 = 1 := holW_zero k ⟨by positivity, le_rfl⟩
  have hR : holR F k 0 = 1 := (holR_spec k hU hF hseg).1
  have hH : holH F k 0 = 1 := by simp [holH, hV, hR]
  exact ⟨hV, hH, by simp [holU, hH]⟩

end

section

/-! ## Unitary invariance of traces and a lower bound for spectral tails -/

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

lemma diagSum_conj (M A : E →L[ℂ] E) {n : ℕ} (v : Fin n → E) :
    diagSum (M * A * star M) v = diagSum A (fun i => star M (v i)) := by
  unfold diagSum
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.adjoint_inner_left]

lemma orthonormal_star_comp {M : E →L[ℂ] E} (hM : M ∈ unitary (E →L[ℂ] E)) {n : ℕ}
    {v : Fin n → E} (hv : Orthonormal ℂ v) : Orthonormal ℂ (fun i => star M (v i)) := by
  rw [orthonormal_iff_ite] at hv ⊢
  intro i j
  rw [← hv i j, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left,
    ← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.star_eq_adjoint,
    Unitary.mul_star_self_of_mem hM, ContinuousLinearMap.one_apply]

lemma posTrace_conj_le {M : E →L[ℂ] E} (hM : M ∈ unitary (E →L[ℂ] E)) (A : E →L[ℂ] E) :
    posTrace (M * A * star M) ≤ posTrace A := by
  refine iSup_le fun n => iSup_le fun v => iSup_le fun hv => ?_
  rw [diagSum_conj]
  exact le_iSup_of_le n (le_iSup_of_le _ (le_iSup_of_le (orthonormal_star_comp hM hv) le_rfl))

lemma kyFan_conj_le {M : E →L[ℂ] E} (hM : M ∈ unitary (E →L[ℂ] E)) (m : ℕ) (A : E →L[ℂ] E) :
    kyFan m (M * A * star M) ≤ kyFan m A := by
  refine iSup_le fun n => iSup_le fun hn => iSup_le fun v => iSup_le fun hv => ?_
  rw [diagSum_conj]
  exact le_iSup_of_le n (le_iSup_of_le hn (le_iSup_of_le _
    (le_iSup_of_le (orthonormal_star_comp hM hv) le_rfl)))

lemma conj_conj_star {M : E →L[ℂ] E} (hM : M ∈ unitary (E →L[ℂ] E)) (A : E →L[ℂ] E) :
    star M * (M * A * star M) * star (star M) = A := by
  rw [star_star]
  have h1 : star M * M = 1 := Unitary.star_mul_self_of_mem hM
  have h2 : M * star M = 1 := Unitary.mul_star_self_of_mem hM
  calc star M * (M * A * star M) * M = (star M * M) * A * (star M * M) := by
        simp only [mul_assoc]
    _ = A := by rw [h1, one_mul, mul_one]

/-- The trace is invariant under unitary conjugation. -/
theorem posTrace_conj {M : E →L[ℂ] E} (hM : M ∈ unitary (E →L[ℂ] E)) (A : E →L[ℂ] E) :
    posTrace (M * A * star M) = posTrace A := by
  refine le_antisymm (posTrace_conj_le hM A) ?_
  have := posTrace_conj_le (Unitary.star_mem hM) (M * A * star M)
  rwa [conj_conj_star hM] at this

/-- The Ky Fan partial traces are invariant under unitary conjugation. -/
theorem kyFan_conj {M : E →L[ℂ] E} (hM : M ∈ unitary (E →L[ℂ] E)) (m : ℕ) (A : E →L[ℂ] E) :
    kyFan m (M * A * star M) = kyFan m A := by
  refine le_antisymm (kyFan_conj_le hM m A) ?_
  have := kyFan_conj_le (Unitary.star_mem hM) m (M * A * star M)
  rwa [conj_conj_star hM] at this

/-- The spectral tails are invariant under unitary conjugation. -/
theorem spectralTail_conj {M : E →L[ℂ] E} (hM : M ∈ unitary (E →L[ℂ] E)) (m : ℕ)
    (A : E →L[ℂ] E) : spectralTail m (M * A * star M) = spectralTail m A := by
  simp only [spectralTail, posTrace_conj hM, kyFan_conj hM]

omit [CompleteSpace E] in
/-- `Φ_m(A) ≤ m ‖A‖ < ∞`. -/
lemma kyFan_le_mul_norm (m : ℕ) (A : E →L[ℂ] E) : kyFan m A ≤ ENNReal.ofReal (m * ‖A‖) := by
  refine iSup_le fun n => iSup_le fun hn => iSup_le fun v => iSup_le fun hv => ?_
  unfold diagSum
  calc ∑ i, ENNReal.ofReal (RCLike.re ⟪v i, A (v i)⟫_ℂ) ≤ ∑ _i : Fin n, ENNReal.ofReal ‖A‖ := by
        refine Finset.sum_le_sum fun i _ => ENNReal.ofReal_le_ofReal ?_
        calc RCLike.re ⟪v i, A (v i)⟫_ℂ ≤ ‖⟪v i, A (v i)⟫_ℂ‖ := RCLike.re_le_norm _
          _ ≤ ‖v i‖ * ‖A (v i)‖ := norm_inner_le_norm _ _
          _ ≤ ‖v i‖ * (‖A‖ * ‖v i‖) := by gcongr; exact A.le_opNorm _
          _ = ‖A‖ := by rw [hv.1 i]; ring
    _ = ENNReal.ofReal (n * ‖A‖) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (m * ‖A‖) := by
        apply ENNReal.ofReal_le_ofReal
        gcongr

omit [CompleteSpace E] in
/-- In a subspace of dimension `> n` there is a unit vector orthogonal to `n` given vectors. -/
lemma exists_unit_orthogonal {V : Submodule ℂ E} [FiniteDimensional ℂ V] {n : ℕ}
    (hV : n < Module.finrank ℂ V) (v : Fin n → E) :
    ∃ z ∈ V, ‖z‖ = 1 ∧ ∀ i, ⟪v i, z⟫_ℂ = 0 := by
  let φ : V →ₗ[ℂ] (Fin n → ℂ) :=
    LinearMap.pi fun i => (innerₛₗ ℂ (v i)).comp V.subtype
  have hker : LinearMap.ker φ ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hV)
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hw0' : (w : E) ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hnw : ‖(w : E)‖ ≠ 0 := norm_ne_zero_iff.2 hw0'
  refine ⟨((‖(w : E)‖⁻¹ : ℝ) : ℂ) • (w : E), V.smul_mem _ w.2, ?_, fun i => ?_⟩
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hnw]
  · have := congrFun (LinearMap.mem_ker.1 hw) i
    simp only [φ, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype, innerₛₗ_apply_apply, Pi.zero_apply] at this
    rw [inner_smul_right, this, mul_zero]

omit [CompleteSpace E] in
lemma orthonormal_cons {n : ℕ} {v : Fin n → E} (hv : Orthonormal ℂ v) {z : E} (hz : ‖z‖ = 1)
    (hzv : ∀ i, ⟪v i, z⟫_ℂ = 0) : Orthonormal ℂ (Fin.cons z v : Fin (n + 1) → E) := by
  rw [orthonormal_iff_ite] at hv ⊢
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simp [inner_self_eq_norm_sq_to_K, hz]
  · simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← inner_conj_symm, hzv j]; simp [(Fin.succ_ne_zero j).symm]
  · simp [hzv i, Fin.succ_ne_zero i]
  · simp [hv i j]

omit [CompleteSpace E] in
/-- **Lower bound for spectral tails.** If `re ⟪z, A z⟫ ≥ δ` for all unit vectors `z` of a
finite-dimensional subspace of dimension `> m`, then `τ_m(A) ≥ δ`. -/
theorem ofReal_le_spectralTail {m : ℕ} {A : E →L[ℂ] E} {V : Submodule ℂ E}
    [FiniteDimensional ℂ V] (hV : m < Module.finrank ℂ V) {δ : ℝ}
    (hδ : ∀ z ∈ V, ‖z‖ = 1 → δ ≤ RCLike.re ⟪z, A z⟫_ℂ) :
    ENNReal.ofReal δ ≤ spectralTail m A := by
  have key : ∀ (n : ℕ), n ≤ m → ∀ v : Fin n → E, Orthonormal ℂ v →
      diagSum A v + ENNReal.ofReal δ ≤ posTrace A := by
    intro n hn v hv
    obtain ⟨z, hzV, hz1, hzv⟩ := exists_unit_orthogonal (lt_of_le_of_lt hn hV) v
    have hon := orthonormal_cons hv hz1 hzv
    refine le_trans ?_ (le_iSup_of_le (n + 1) (le_iSup_of_le _ (le_iSup_of_le hon le_rfl)))
    unfold diagSum
    rw [Fin.sum_univ_succ, add_comm]
    simp only [Fin.cons_zero, Fin.cons_succ]
    gcongr
    exact hδ z hzV hz1
  have hfin : kyFan m A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (kyFan_le_mul_norm m A)
  have hδP : ENNReal.ofReal δ ≤ posTrace A := by
    have := key 0 (Nat.zero_le _) Fin.elim0 (by simp [Orthonormal])
    simpa [diagSum] using this
  have hle : kyFan m A ≤ posTrace A - ENNReal.ofReal δ := by
    refine iSup_le fun n => iSup_le fun hn => iSup_le fun v => iSup_le fun hv => ?_
    exact ENNReal.le_sub_of_add_le_right ENNReal.ofReal_ne_top (key n hn v hv)
  unfold spectralTail
  refine ENNReal.le_sub_of_add_le_left hfin ?_
  calc kyFan m A + ENNReal.ofReal δ ≤ (posTrace A - ENNReal.ofReal δ) + ENNReal.ofReal δ := by
        gcongr
    _ = posTrace A := tsub_add_cancel_of_le hδP

end

section

/-! ## Injective holomorphic maps have nonvanishing derivative -/

open Complex Metric Filter Topology Set

/-- **Injective holomorphic functions have nonzero derivative.** -/
theorem deriv_ne_zero_of_injOn {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) {a : ℂ} (ha : a ∈ U) :
    deriv f a ≠ 0 := by
  intro h0
  have hUa : U ∈ 𝓝 a := hU.mem_nhds ha
  have han : AnalyticAt ℂ f a := (hf.analyticOnNhd hU) a ha
  set g : ℂ → ℂ := fun z => f z - f a with hg
  have hgan : AnalyticAt ℂ g a := han.sub analyticAt_const
  -- `g` is not identically zero near `a`
  have hnz : ¬ ∀ᶠ z in 𝓝 a, g z = 0 := by
    intro hev
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.1 (inter_mem hev hUa)
    have hmem : a + (ε / 2 : ℝ) ∈ ball a ε := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith
    have h1 := hεsub hmem
    have h2 : f (a + (ε / 2 : ℝ)) = f a := sub_eq_zero.1 h1.1
    have := hinj h1.2 ha h2
    have : ((ε / 2 : ℝ) : ℂ) = 0 := by linear_combination this
    have : ε / 2 = 0 := by exact_mod_cast this
    linarith
  obtain ⟨n, h, hhan, hha, hgeq⟩ := hgan.exists_eventuallyEq_pow_smul_nonzero_iff.2 hnz
  simp only [smul_eq_mul] at hgeq
  -- `n ≥ 2`
  have hga : g a = 0 := by simp [hg]
  have hderg : deriv g a = 0 := by
    have : deriv g a = deriv f a := by
      rw [hg, deriv_sub_const]
    rw [this, h0]
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with hn | hn
    · exfalso
      interval_cases n
      · have := hgeq.self_of_nhds
        simp only [pow_zero, one_mul] at this
        exact hha (this ▸ hga)
      · have hd : HasDerivAt (fun z => (z - a) ^ 1 * h z)
            (1 * h a + (a - a) ^ 1 * deriv h a) a := by
          have h1 : HasDerivAt (fun z => (z - a) ^ 1) 1 a := by
            simpa using (hasDerivAt_id a).sub_const a
          exact h1.mul hhan.differentiableAt.hasDerivAt
        have := hd.deriv
        rw [← Filter.EventuallyEq.deriv_eq hgeq] at this
        rw [hderg] at this
        simp at this
        exact hha this.symm
    · exact hn
  have hn0 : n ≠ 0 := by omega
  -- an `n`-th root of `h` near `a`
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c ^ n = h a := IsAlgClosed.exists_pow_nat_eq _ (by omega)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hha (by rw [← hc, zero_pow hn0])
  set q : ℂ → ℂ := fun z => h z / h a with hq
  have hqa : q a = 1 := div_self hha
  have hqan : AnalyticAt ℂ q a := hhan.div analyticAt_const hha
  have hslit : q a ∈ slitPlane := by rw [hqa]; exact one_mem_slitPlane
  set ψ : ℂ → ℂ := fun z => c * exp (log (q z) / n) with hψ
  have hψan : AnalyticAt ℂ ψ a := by
    apply analyticAt_const.mul
    apply AnalyticAt.cexp
    exact (hqan.clog hslit).div analyticAt_const (by exact_mod_cast hn0)
  have hψpow : ∀ᶠ z in 𝓝 a, ψ z ^ n = h z := by
    have hev : ∀ᶠ z in 𝓝 a, q z ∈ slitPlane :=
      hqan.continuousAt.preimage_mem_nhds (isOpen_slitPlane.mem_nhds hslit)
    filter_upwards [hev] with z hz
    have hqz : q z ≠ 0 := slitPlane_ne_zero hz
    rw [hψ, mul_pow, hc, ← exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hn0),
      exp_log hqz, hq]
    field_simp
  set φ : ℂ → ℂ := fun z => (z - a) * ψ z with hφ
  have hφan : AnalyticAt ℂ φ a := (analyticAt_id.sub analyticAt_const).mul hψan
  have hφa : φ a = 0 := by simp [hφ]
  have hψa : ψ a = c := by simp [hψ, hqa]
  have hφd : HasDerivAt φ c a := by
    have := ((hasDerivAt_id a).sub_const a).mul hψan.differentiableAt.hasDerivAt
    convert this using 1
    · funext z
      rfl
    · simp [hψa]
  have hφnc : ¬ ∀ᶠ z in 𝓝 a, φ z = φ a := by
    intro hev
    have : deriv φ a = 0 := by
      have hev' : φ =ᶠ[𝓝 a] fun _ => φ a := hev
      rw [hev'.deriv_eq]
      simp
    rw [hφd.deriv] at this
    exact hc0 this
  have hopen : 𝓝 (φ a) ≤ map φ (𝓝 a) :=
    hφan.eventually_constant_or_nhds_le_map_nhds.resolve_left hφnc
  -- a neighbourhood of `a` where `g = φⁿ`
  have hVmem : {z | z ∈ U ∧ g z = φ z ^ n} ∈ 𝓝 a := by
    filter_upwards [hUa, hgeq, hψpow] with z hz h1 h2
    refine ⟨hz, ?_⟩
    rw [h1, hφ, mul_pow, h2]
  have himg : φ '' {z | z ∈ U ∧ g z = φ z ^ n} ∈ 𝓝 0 := by
    rw [← hφa]
    exact hopen (image_mem_map hVmem)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 himg
  set ε : ℂ := ((δ / 2 : ℝ) : ℂ) with hε
  set ζ : ℂ := exp (2 * Real.pi * I / n) with hζ
  have hζprim : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn0
  have hζ1 : ζ ≠ 1 := hζprim.ne_one (by omega)
  have hζn : ζ ^ n = 1 := hζprim.pow_eq_one
  have hζnorm : ‖ζ‖ = 1 := hζprim.norm'_eq_one hn0
  have hεnorm : ‖ε‖ = δ / 2 := by
    rw [hε, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hε0 : ε ≠ 0 := by
    intro h; rw [h, norm_zero] at hεnorm; linarith
  have hm1 : ε ∈ ball (0 : ℂ) δ := by
    rw [mem_ball_zero_iff, hεnorm]; linarith
  have hm2 : ε * ζ ∈ ball (0 : ℂ) δ := by
    rw [mem_ball_zero_iff, norm_mul, hεnorm, hζnorm]; linarith
  obtain ⟨z1, ⟨hz1U, hz1g⟩, hz1⟩ := hδsub hm1
  obtain ⟨z2, ⟨hz2U, hz2g⟩, hz2⟩ := hδsub hm2
  have hgz : g z1 = g z2 := by
    rw [hz1g, hz2g, hz1, hz2, mul_pow, hζn, mul_one]
  have hfz : f z1 = f z2 := by
    simpa [hg] using hgz
  have hz12 := hinj hz1U hz2U hfz
  rw [hz12, hz2] at hz1
  have : ε * (ζ - 1) = 0 := by linear_combination hz1
  rcases mul_eq_zero.1 this with h | h
  · exact hε0 h
  · exact hζ1 (sub_eq_zero.1 h)

end

section

/-! ## Positivity of the spectral tails of the generator -/

open scoped InnerProductSpace
open MeasureTheory Set Real Metric Complex Filter Topology

/-- The operator `A_r = ∫₀^{2π} J(r,θ) W_r(θ)^* P₀ W_r(θ) dθ`, so that
`Q_{r,k} = (k²/2) R_r^* A_r R_r`. -/
def holA (F : ℂ → ℂ) (k r : ℝ) : L2N →L[ℂ] L2N :=
  ∫ θ in (0 : ℝ)..(2 * π), ((jac F r θ : ℝ) : ℂ) •
    (star (holW F k r θ) * projE0 * holW F k r θ)

variable {G : ℂ → ℂ} (k : ℝ)

lemma circ_mem_ball {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) (θ : ℝ) :
    (r : ℂ) * exp (θ * I) ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr.1]
  exact hr.2

lemma seg_mem_ball : ∀ r ∈ Ico (0 : ℝ) 1, (r : ℂ) ∈ ball (0 : ℂ) 1 := fun r hr => by
  simpa using circ_mem_ball hr 0

/-- The coordinate functional `x ↦ xₙ` on `ℓ²(ℕ₀)`. -/
def coordCLM (n : ℕ) : L2N →L[ℂ] ℂ := innerSL ℂ (lp.single 2 n (1 : ℂ))

@[simp] lemma coordCLM_apply (n : ℕ) (x : L2N) : coordCLM n x = x n := by
  simp [coordCLM, lp.inner_single_left]

lemma continuousOn_holW (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1) : ContinuousOn (holW G k r) (Icc 0 (2 * π)) := fun θ hθ =>
  ((holW_spec k isOpen_ball hG (circ_mem_ball hr)).2 θ hθ).continuousWithinAt

lemma continuous_jac (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) :
    Continuous (jac G r) := by
  have hdF : ContinuousOn (deriv G) (ball 0 1) := (hG.deriv isOpen_ball).continuousOn
  have hγ : Continuous fun θ : ℝ => (r : ℂ) * exp (θ * I) := by fun_prop
  unfold jac
  exact continuous_const.mul ((hdF.comp_continuous hγ (circ_mem_ball hr)).norm.pow 2)

lemma jac_nonneg {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) : 0 ≤ jac G r θ := by
  unfold jac; positivity

lemma jac_pos (hG : DifferentiableOn ℂ G (ball 0 1)) (hinj : InjOn G (ball 0 1)) {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) (θ : ℝ) : 0 < jac G r θ := by
  have h := deriv_ne_zero_of_injOn isOpen_ball hG hinj
    (circ_mem_ball (Ioo_subset_Ico_self hr) θ)
  unfold jac
  have := norm_pos_iff.2 h
  have := hr.1
  positivity

lemma inner_e0 (x : L2N) : ⟪e0, x⟫_ℂ = x 0 := by
  simp [e0, lp.inner_single_left]

lemma re_inner_projE0 (x : L2N) : RCLike.re ⟪x, projE0 x⟫_ℂ = ‖x 0‖ ^ 2 := by
  simp only [projE0, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_right,
    inner_e0]
  rw [← inner_conj_symm, inner_e0, Complex.mul_conj']
  simp [← Complex.ofReal_pow]

lemma continuousOn_holA_integrand (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1) :
    ContinuousOn (fun θ => ((jac G r θ : ℝ) : ℂ) • (star (holW G k r θ) * projE0 * holW G k r θ))
      (Icc 0 (2 * π)) := by
  have hW := continuousOn_holW k hG hr
  have hstar : Continuous (fun T : L2N →L[ℂ] L2N => star T) := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using
      (LinearIsometryEquiv.continuous
        (ContinuousLinearMap.adjoint : (L2N →L[ℂ] L2N) ≃ₗᵢ⋆[ℂ] (L2N →L[ℂ] L2N)))
  refine (continuous_ofReal.comp (continuous_jac hG hr)).continuousOn.smul ?_
  exact ((hstar.comp_continuousOn hW).mul continuousOn_const).mul hW

/-- `L_{r,k} = (k²/2) M_r A_r M_r^*` with `M_r = H_r R_r^*`. -/
lemma holL_eq (F : ℂ → ℂ) (r : ℝ) :
    holL F k r = ((k ^ 2 / 2 : ℝ) : ℂ) •
      ((holH F k r * star (holR F k r)) * holA F k r * star (holH F k r * star (holR F k r))) := by
  simp only [holL, holQ, holA, star_mul, star_star, mul_smul_comm, smul_mul_assoc, mul_assoc]

lemma holM_mem_unitary (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) :
    holH G k r * star (holR G k r) ∈ unitary (L2N →L[ℂ] L2N) :=
  mul_mem (holU_mem_unitary k isOpen_ball hG seg_mem_ball hr (circ_mem_ball hr)).2.1
    (Unitary.star_mem (holR_mem_unitary k isOpen_ball hG seg_mem_ball hr))

/-- The quadratic form of `A_r`: `re ⟪z, A_r z⟫ = ∫₀^{2π} J(r,θ) |(W_r(θ) z)₀|² dθ`. -/
lemma re_inner_holA (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1)
    (z : L2N) :
    RCLike.re ⟪z, holA G k r z⟫_ℂ = ∫ θ in (0 : ℝ)..(2 * π), jac G r θ * ‖holW G k r θ z 0‖ ^ 2 := by
  let L : (L2N →L[ℂ] L2N) →L[ℝ] ℝ :=
    RCLike.reCLM.comp (((innerSL ℂ z).comp (ContinuousLinearMap.apply ℂ L2N z)).restrictScalars ℝ)
  have hL : ∀ T : L2N →L[ℂ] L2N, L T = RCLike.re ⟪z, T z⟫_ℂ := fun T => rfl
  have hint : IntervalIntegrable (fun θ => ((jac G r θ : ℝ) : ℂ) •
      (star (holW G k r θ) * projE0 * holW G k r θ)) volume 0 (2 * π) :=
    (continuousOn_holA_integrand k hG hr).intervalIntegrable_of_Icc (by positivity)
  rw [← hL, holA, ← L.intervalIntegral_comp_comm hint]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [hL, ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply, inner_smul_right,
    ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.adjoint_inner_right, RCLike.re_to_complex, Complex.re_ofReal_mul,
    ← RCLike.re_to_complex, re_inner_projE0]

lemma coefAng_apply_zero (F : ℂ → ℂ) (r θ : ℝ) (x : L2N) :
    coefAng F k r θ x 0 = -(I * k / 2) * dAng F r θ * x 1 := by
  simp only [coefAng, opX, opY, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, lp.coeFn_add, lp.coeFn_smul, lp.coeFn_sub, Pi.add_apply,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul, 
    show ∀ y : L2N, shift y 0 = 0 from fun _ => rfl, shiftAdj_apply]
  generalize dAng F r θ = d
  rw [← Complex.re_add_im d]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im]
  ring_nf; rw [I_sq]; ring

lemma coefAng_apply_succ (F : ℂ → ℂ) (r θ : ℝ) (x : L2N) (n : ℕ) :
    coefAng F k r θ x (n + 1) =
      -(I * k / 2) * (dAng F r θ * x (n + 2) + (starRingEnd ℂ) (dAng F r θ) * x n) := by
  simp only [coefAng, opX, opY, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, lp.coeFn_add, lp.coeFn_smul, lp.coeFn_sub, Pi.add_apply,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul, 
    show ∀ (y : L2N) (n : ℕ), shift y (n + 1) = y n from fun _ _ => rfl, shiftAdj_apply]
  generalize dAng F r θ = d
  rw [← Complex.re_add_im d]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]
  ring_nf; rw [I_sq]; ring

lemma dAng_ne_zero (hG : DifferentiableOn ℂ G (ball 0 1)) (hinj : InjOn G (ball 0 1)) {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) (θ : ℝ) : dAng G r θ ≠ 0 := by
  have h := deriv_ne_zero_of_injOn isOpen_ball hG hinj
    (circ_mem_ball (Ioo_subset_Ico_self hr) θ)
  unfold dAng
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.1.ne'
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero I_ne_zero hr0) (Complex.exp_ne_zero _)) h

/-- If the zeroth component of `W_r(θ) z`
vanishes for all `θ ∈ [0, 2π]`, then `z = 0`. -/
lemma eq_zero_of_holW_apply_zero (hG : DifferentiableOn ℂ G (ball 0 1))
    (hinj : InjOn G (ball 0 1)) (hk : k ≠ 0) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (z : L2N)
    (h0 : ∀ θ ∈ Icc 0 (2 * π), holW G k r θ z 0 = 0) : z = 0 := by
  have hr' := Ioo_subset_Ico_self hr
  obtain ⟨hW0, hW⟩ := holW_spec k isOpen_ball hG (circ_mem_ball hr')
  set f : ℝ → L2N := fun θ => holW G k r θ z with hf
  have hfd : ∀ θ ∈ Icc 0 (2 * π), ∀ n : ℕ, HasDerivWithinAt (fun t => f t n)
      (coefAng G k r θ (f θ) n) (Icc 0 (2 * π)) θ := by
    intro θ hθ n
    let L : (L2N →L[ℂ] L2N) →L[ℝ] ℂ :=
      ((coordCLM n).comp (ContinuousLinearMap.apply ℂ L2N z)).restrictScalars ℝ
    have h2 := L.hasFDerivAt.comp_hasDerivWithinAt θ (hW θ hθ)
    simpa [Function.comp_def, hf, L] using h2
  have huniq : ∀ θ ∈ Icc 0 (2 * π), ∀ n : ℕ, (∀ t ∈ Icc 0 (2 * π), f t n = 0) →
      coefAng G k r θ (f θ) n = 0 := by
    intro θ hθ n hzero
    have hc : HasDerivWithinAt (fun t => f t n) 0 (Icc 0 (2 * π)) θ :=
      (hasDerivWithinAt_const θ _ (0 : ℂ)).congr (fun t ht => hzero t ht) (hzero θ hθ)
    exact (uniqueDiffOn_Icc (by positivity) θ hθ).eq_deriv _ (hfd θ hθ n) hc
  have hfac : ∀ θ, -(I * k / 2) * dAng G r θ ≠ 0 := fun θ =>
    mul_ne_zero (neg_ne_zero.2 (div_ne_zero (mul_ne_zero I_ne_zero (ofReal_ne_zero.2 hk))
      two_ne_zero)) (dAng_ne_zero hG hinj hr θ)
  have key : ∀ n : ℕ, ∀ θ ∈ Icc 0 (2 * π), f θ n = 0 ∧ f θ (n + 1) = 0 := by
    intro n
    induction n with
    | zero =>
      intro θ hθ
      refine ⟨h0 θ hθ, ?_⟩
      have := huniq θ hθ 0 h0
      rw [coefAng_apply_zero] at this
      exact (mul_eq_zero.1 this).resolve_left (hfac θ)
    | succ n ih =>
      intro θ hθ
      refine ⟨(ih θ hθ).2, ?_⟩
      have := huniq θ hθ (n + 1) (fun t ht => (ih t ht).2)
      rw [coefAng_apply_succ, (ih θ hθ).1, mul_zero, add_zero, ← mul_assoc] at this
      exact (mul_eq_zero.1 this).resolve_left (hfac θ)
  have hz : f 0 = z := by simp [hf, hW0]
  ext n
  rw [← hz]
  exact (key n 0 ⟨le_rfl, by positivity⟩).1

/-- For `0 < r < 1` the quadratic form of `A_r` is strictly positive
on nonzero vectors. -/
theorem holA_pos (hG : DifferentiableOn ℂ G (ball 0 1)) (hinj : InjOn G (ball 0 1))
    (hk : k ≠ 0) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) {z : L2N} (hz : z ≠ 0) :
    0 < RCLike.re ⟪z, holA G k r z⟫_ℂ := by
  have hr' := Ioo_subset_Ico_self hr
  rw [re_inner_holA k hG hr' z]
  refine intervalIntegral.integral_pos (by positivity) ?_ ?_ ?_
  · refine (continuous_jac hG hr').continuousOn.mul ?_
    have h1 : ContinuousOn (fun θ => holW G k r θ z 0) (Icc 0 (2 * π)) := by
      have h0 : ContinuousOn (fun θ => holW G k r θ z) (Icc 0 (2 * π)) :=
        (continuousOn_holW k hG hr').clm_apply continuousOn_const
      have := (coordCLM 0).continuous.comp_continuousOn h0
      simpa [Function.comp_def] using this
    exact (h1.norm).pow 2
  · intro θ _
    exact mul_nonneg (jac_nonneg hr.1.le θ) (by positivity)
  · by_contra hcon
    push_neg at hcon
    apply hz
    refine eq_zero_of_holW_apply_zero k hG hinj hk hr z fun θ hθ => ?_
    have h1 := hcon θ hθ
    have h2 := jac_pos hG hinj hr θ
    have h3 : ‖holW G k r θ z 0‖ ^ 2 ≤ 0 := by
      by_contra h; push_neg at h; linarith [mul_pos h2 h]
    have : ‖holW G k r θ z 0‖ = 0 := by nlinarith [norm_nonneg (holW G k r θ z 0)]
    exact norm_eq_zero.1 this

/-- Comparison of angular transports with different coefficients. -/
lemma norm_holW_sub_le (hG : DifferentiableOn ℂ G (ball 0 1)) {k₁ k₂ r s : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1) (hs : s ∈ Ico (0 : ℝ) 1) {ε : ℝ}
    (hε : ∀ θ ∈ Icc 0 (2 * π), ‖coefAng G k₂ s θ - coefAng G k₁ r θ‖ ≤ ε)
    {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    ‖holW G k₂ s θ - holW G k₁ r θ‖ ≤ ε * θ := by
  letI : ContinuousSMul ℝ (L2N →L[ℂ] L2N) := ⟨by
    have hsmul : (fun p : ℝ × (L2N →L[ℂ] L2N) => p.1 • p.2) =
        fun p => ((p.1 : ℂ) • p.2) := by
      funext p
      exact RCLike.real_smul_eq_coe_smul (K := ℂ) p.1 p.2
    rw [hsmul]
    fun_prop⟩
  letI : StarModule ℝ (L2N →L[ℂ] L2N) :=
    ⟨fun a T => by
      change star ((a : ℂ) • T) = (a : ℂ) • star T
      rw [star_smul]
      simp⟩
  obtain ⟨hr0, hrd⟩ := holW_spec k₁ isOpen_ball hG (circ_mem_ball hr)
  obtain ⟨hs0, hsd⟩ := holW_spec k₂ isOpen_ball hG (circ_mem_ball hs)
  have hru : ∀ t ∈ Icc 0 (2 * π), holW G k₁ r t ∈ unitary (L2N →L[ℂ] L2N) := fun t ht =>
    holW_mem_unitary k₁ isOpen_ball hG (circ_mem_ball hr) ht
  have hsu : ∀ t ∈ Icc 0 (2 * π), holW G k₂ s t ∈ unitary (L2N →L[ℂ] L2N) := fun t ht =>
    holW_mem_unitary k₂ isOpen_ball hG (circ_mem_ball hs) ht
  set g : ℝ → L2N →L[ℂ] L2N := fun t => star (holW G k₁ r t) * holW G k₂ s t with hg
  have hgd : ∀ t ∈ Icc 0 (2 * π), HasDerivWithinAt g
      (star (holW G k₁ r t) * (coefAng G k₂ s t - coefAng G k₁ r t) * holW G k₂ s t)
      (Icc 0 (2 * π)) t := by
    intro t ht
    have hd := ((hrd t ht).star).mul (hsd t ht)
    convert hd using 1
    · apply Module.ext' _ _
      intro r x
      exact RCLike.real_smul_eq_coe_smul (K := ℂ) r x
    rw [star_mul, star_coefAng]
    simp only [mul_sub, sub_mul, mul_neg, neg_mul, mul_assoc, sub_eq_add_neg, add_comm]
    simp only [add_mul, mul_add, neg_mul, mul_assoc]
  have hbound : ∀ t ∈ Ico 0 (2 * π),
      ‖star (holW G k₁ r t) * (coefAng G k₂ s t - coefAng G k₁ r t) * holW G k₂ s t‖ ≤ ε := by
    intro t ht
    have ht' := Ico_subset_Icc_self ht
    rw [CStarRing.norm_mul_mem_unitary _ (hsu t ht'),
      CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem (hru t ht'))]
    exact hε t ht'
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hgd hbound θ hθ
  have hg0 : g 0 = 1 := by simp [hg, hr0, hs0]
  rw [hg0, sub_zero] at hmv
  have heq : holW G k₂ s θ - holW G k₁ r θ = holW G k₁ r θ * (g θ - 1) := by
    simp only [hg, mul_sub, mul_one, ← mul_assoc, Unitary.mul_star_self_of_mem (hru θ hθ),
      one_mul]
  rw [heq, CStarRing.norm_mem_unitary_mul _ (hru θ hθ)]
  exact hmv

lemma norm_projE0_le : ‖projE0‖ ≤ 1 := by
  have he : ‖e0‖ = 1 := by
    simp [e0, lp.norm_single]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  simp only [projE0, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, norm_smul, he,
    mul_one, one_mul]
  simpa [he] using norm_inner_le_norm (𝕜 := ℂ) e0 x

/-- Bounds for the rank-one operators `W^* P₀ W`. -/
lemma norm_conj_projE0_le {W V : L2N →L[ℂ] L2N} (hW : W ∈ unitary (L2N →L[ℂ] L2N))
    (hV : V ∈ unitary (L2N →L[ℂ] L2N)) :
    ‖star W * projE0 * W‖ ≤ 1 ∧
      ‖star W * projE0 * W - star V * projE0 * V‖ ≤ 2 * ‖W - V‖ := by
  constructor
  · rw [CStarRing.norm_mul_mem_unitary _ hW,
      CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem hW)]
    exact norm_projE0_le
  · have heq : star W * projE0 * W - star V * projE0 * V =
        star (W - V) * projE0 * W + star V * projE0 * (W - V) := by
      simp only [ContinuousLinearMap.star_eq_adjoint, map_sub, sub_mul, mul_sub]
      noncomm_ring
    rw [heq]
    calc ‖star (W - V) * projE0 * W + star V * projE0 * (W - V)‖
        ≤ ‖star (W - V) * projE0 * W‖ + ‖star V * projE0 * (W - V)‖ := norm_add_le _ _
      _ = ‖star (W - V) * projE0‖ + ‖projE0 * (W - V)‖ := by
          rw [CStarRing.norm_mul_mem_unitary _ hW, mul_assoc,
            CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem hV)]
      _ ≤ ‖W - V‖ * 1 + 1 * ‖W - V‖ := by
          refine add_le_add ((norm_mul_le _ _).trans ?_) ((norm_mul_le _ _).trans ?_)
          · rw [ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.norm_map]
            gcongr; exact norm_projE0_le
          · gcongr; exact norm_projE0_le
      _ = 2 * ‖W - V‖ := by ring

/-- Uniform continuity in the first variable, uniformly in the second, on a compact
rectangle. -/
lemma uniform_in_snd {E : Type*} [PseudoMetricSpace E] {f : ℝ → ℝ → E} {b T : ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 b ×ˢ Icc 0 T)) {r₀ : ℝ} (hr₀ : r₀ ∈ Icc 0 b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ s ∈ Icc 0 b, |s - r₀| < η → ∀ θ ∈ Icc 0 T, dist (f s θ) (f r₀ θ) < ε := by
  have hu := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hf
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨η, hη, h⟩ := hu ε hε
  refine ⟨η, hη, fun s hs hsη θ hθ => ?_⟩
  have := h (s, θ) ⟨hs, hθ⟩ (r₀, θ) ⟨hr₀, hθ⟩ (by simpa [Prod.dist_eq, Real.dist_eq] using hsη)
  simpa using this

lemma continuousOn_derivG_circ (hG : DifferentiableOn ℂ G (ball 0 1)) {b : ℝ} (hb : b < 1) :
    ContinuousOn (fun p : ℝ × ℝ => deriv G ((p.1 : ℂ) * exp (p.2 * I))) (Icc 0 b ×ˢ univ) := by
  have hdF : ContinuousOn (deriv G) (ball 0 1) := (hG.deriv isOpen_ball).continuousOn
  have hγ : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) * exp (p.2 * I) := by fun_prop
  refine hdF.comp hγ.continuousOn fun p hp => ?_
  exact circ_mem_ball ⟨hp.1.1, lt_of_le_of_lt hp.1.2 hb⟩ p.2

lemma continuousOn_dAng_uncurry (hG : DifferentiableOn ℂ G (ball 0 1)) {b : ℝ} (hb : b < 1) :
    ContinuousOn (fun p : ℝ × ℝ => dAng G p.1 p.2) (Icc 0 b ×ˢ univ) := by
  unfold dAng
  exact ContinuousOn.mul (Continuous.continuousOn (by fun_prop)) (continuousOn_derivG_circ hG hb)

lemma continuousOn_coefAng_uncurry (hG : DifferentiableOn ℂ G (ball 0 1)) {b : ℝ} (hb : b < 1) :
    ContinuousOn (Function.uncurry (coefAng G k)) (Icc 0 b ×ˢ univ) := by
  have hd := continuousOn_dAng_uncurry hG hb
  have h1 : ContinuousOn (fun p : ℝ × ℝ => ((dAng G p.1 p.2).re : ℂ)) (Icc 0 b ×ˢ univ) :=
    continuous_ofReal.comp_continuousOn (continuous_re.comp_continuousOn hd)
  have h2 : ContinuousOn (fun p : ℝ × ℝ => ((dAng G p.1 p.2).im : ℂ)) (Icc 0 b ×ˢ univ) :=
    continuous_ofReal.comp_continuousOn (continuous_im.comp_continuousOn hd)
  exact (h1.smul continuousOn_const).add (h2.smul continuousOn_const)

lemma continuousOn_jac_uncurry (hG : DifferentiableOn ℂ G (ball 0 1)) {b : ℝ} (hb : b < 1) :
    ContinuousOn (Function.uncurry (jac G)) (Icc 0 b ×ˢ univ) := by
  unfold jac
  exact continuous_fst.continuousOn.mul ((continuousOn_derivG_circ hG hb).norm.pow 2)

lemma norm_shift_le : ‖shift‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

lemma norm_shiftAdj_le : ‖shiftAdj‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

lemma norm_opX_le (k : ℝ) : ‖opX k‖ ≤ |k| := by
  unfold opX
  have h1 : ‖-(I * (k : ℂ) / 2)‖ = |k| / 2 := by
    simp [norm_neg, Complex.norm_I]
  rw [norm_smul, h1]
  calc |k| / 2 * ‖shift + shiftAdj‖ ≤ |k| / 2 * 2 := by
        gcongr
        exact (norm_add_le _ _).trans (by linarith [norm_shift_le, norm_shiftAdj_le])
    _ = |k| := by ring

lemma norm_opY_le (k : ℝ) : ‖opY k‖ ≤ |k| := by
  unfold opY
  have h1 : ‖(k : ℂ) / 2‖ = |k| / 2 := by
    simp
  rw [norm_smul, h1]
  calc |k| / 2 * ‖shiftAdj - shift‖ ≤ |k| / 2 * 2 := by
        gcongr
        exact (norm_sub_le _ _).trans (by linarith [norm_shift_le, norm_shiftAdj_le])
    _ = |k| := by ring

lemma coefAng_sub_coefAng (F : ℂ → ℂ) (k₁ k₂ r θ : ℝ) :
    coefAng F k₁ r θ - coefAng F k₂ r θ = coefAng F (k₁ - k₂) r θ := by
  simp only [coefAng, opX, opY, ofReal_sub, smul_smul]
  rw [show ∀ a b c d : ℂ, ∀ X Y : L2N →L[ℂ] L2N, (a • X + b • Y) - (c • X + d • Y) = (a - c) • X + (b - d) • Y from
    fun a b c d X Y => by module]
  congr 2 <;> ring

lemma norm_coefAng_le (F : ℂ → ℂ) (k r θ : ℝ) :
    ‖coefAng F k r θ‖ ≤ 2 * |k| * ‖dAng F r θ‖ := by
  unfold coefAng
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 := Complex.abs_re_le_norm (dAng F r θ)
  have h2 := Complex.abs_im_le_norm (dAng F r θ)
  have h3 := norm_opX_le k
  have h4 := norm_opY_le k
  calc |(dAng F r θ).re| * ‖opX k‖ + |(dAng F r θ).im| * ‖opY k‖
      ≤ ‖dAng F r θ‖ * |k| + ‖dAng F r θ‖ * |k| := by gcongr
    _ = 2 * |k| * ‖dAng F r θ‖ := by ring

/-- Continuity of `r ↦ A_r` in operator norm. -/
lemma norm_holA_sub_le (hG : DifferentiableOn ℂ G (ball 0 1)) {r₀ : ℝ}
    (hr₀ : r₀ ∈ Ico (0 : ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ s ∈ Ico (0 : ℝ) 1, |s - r₀| < η → ∀ k' : ℝ, |k' - k| < η →
      ‖holA G k' s - holA G k r₀‖ ≤ ε := by
  set b := (1 + r₀) / 2 with hbdef
  have hb : b < 1 := by rw [hbdef]; linarith [hr₀.2]
  have hr₀b : r₀ ∈ Icc 0 b := ⟨hr₀.1, by rw [hbdef]; linarith [hr₀.2]⟩
  obtain ⟨MJ, hMJ⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn
    (continuous_jac hG hr₀).continuousOn
  have hMJ0 : 0 ≤ |MJ| := abs_nonneg _
  have hpi := Real.pi_pos
  set ε₁ := ε / (16 * π ^ 2 * (|MJ| + 1)) with hε₁
  set ε₂ := ε / (4 * π) with hε₂
  have hε₁pos : 0 < ε₁ := by positivity
  have hε₂pos : 0 < ε₂ := by positivity
  obtain ⟨η₁, hη₁, h₁⟩ := uniform_in_snd ((continuousOn_coefAng_uncurry k hG hb).mono
    (prod_mono_right (subset_univ (Icc 0 (2 * π))))) hr₀b (half_pos hε₁pos)
  obtain ⟨Md, hMd⟩ := (isCompact_Icc.prod (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π))).exists_bound_of_continuousOn
    ((continuousOn_dAng_uncurry hG hb).mono (prod_mono_right (subset_univ _)))
  set η₃ := ε₁ / (4 * (|Md| + 1)) with hη₃
  have hη₃pos : 0 < η₃ := by positivity
  obtain ⟨η₂, hη₂, h₂⟩ := uniform_in_snd ((continuousOn_jac_uncurry hG hb).mono
    (prod_mono_right (subset_univ (Icc 0 (2 * π))))) hr₀b hε₂pos
  have hbr : 0 < b - r₀ := by rw [hbdef]; linarith [hr₀.2]
  refine ⟨min (min (min η₁ η₂) (b - r₀)) η₃, lt_min (lt_min (lt_min hη₁ hη₂) hbr) hη₃pos,
    fun s hs hsη' k' hk' => ?_⟩
  have hkη : |k' - k| < η₃ := lt_of_lt_of_le hk' (min_le_right _ _)
  have hsη : |s - r₀| < min (min η₁ η₂) (b - r₀) := lt_of_lt_of_le hsη' (min_le_left _ _)
  have hsη₁ : |s - r₀| < η₁ := lt_of_lt_of_le hsη ((min_le_left _ _).trans (min_le_left _ _))
  have hsη₂ : |s - r₀| < η₂ := lt_of_lt_of_le hsη ((min_le_left _ _).trans (min_le_right _ _))
  have hsb : s ∈ Icc 0 b := by
    have := lt_of_lt_of_le hsη (min_le_right _ _)
    rw [abs_lt] at this
    exact ⟨hs.1, by linarith [this.2]⟩
  have hC : ∀ θ ∈ Icc 0 (2 * π), ‖coefAng G k' s θ - coefAng G k r₀ θ‖ ≤ ε₁ := fun θ hθ => by
    have h1 := h₁ s hsb hsη₁ θ hθ
    rw [dist_eq_norm] at h1
    have h2 : ‖coefAng G k' s θ - coefAng G k s θ‖ ≤ ε₁ / 2 := by
      rw [coefAng_sub_coefAng]
      refine (norm_coefAng_le _ _ _ _).trans ?_
      have hd : ‖dAng G s θ‖ ≤ |Md| := (hMd (s, θ) ⟨hsb, hθ⟩).trans (le_abs_self _)
      calc 2 * |k' - k| * ‖dAng G s θ‖ ≤ 2 * η₃ * |Md| := by gcongr
        _ ≤ ε₁ / 2 := by
          rw [hη₃]
          have : 2 * (ε₁ / (4 * (|Md| + 1))) * |Md| = ε₁ / 2 * (|Md| / (|Md| + 1)) := by
            field_simp; ring
          rw [this]
          refine mul_le_of_le_one_right (by positivity) ?_
          rw [div_le_one (by positivity)]; linarith
    calc ‖coefAng G k' s θ - coefAng G k r₀ θ‖
        = ‖(coefAng G k' s θ - coefAng G k s θ) + (coefAng G k s θ - coefAng G k r₀ θ)‖ := by
          congr 1; abel
      _ ≤ ε₁ / 2 + ε₁ / 2 := (norm_add_le _ _).trans (add_le_add h2 h1.le)
      _ = ε₁ := by ring
  have hJ : ∀ θ ∈ Icc 0 (2 * π), |jac G s θ - jac G r₀ θ| ≤ ε₂ := fun θ hθ => by
    have := h₂ s hsb hsη₂ θ hθ
    rw [Real.dist_eq] at this
    exact this.le
  have hW : ∀ θ ∈ Icc 0 (2 * π), ‖holW G k' s θ - holW G k r₀ θ‖ ≤ ε₁ * (2 * π) := fun θ hθ =>
    (norm_holW_sub_le hG hr₀ hs hC hθ).trans (by gcongr; exact hθ.2)
  have hpt : ∀ θ ∈ Icc 0 (2 * π),
      ‖((jac G s θ : ℝ) : ℂ) • (star (holW G k' s θ) * projE0 * holW G k' s θ) -
        ((jac G r₀ θ : ℝ) : ℂ) • (star (holW G k r₀ θ) * projE0 * holW G k r₀ θ)‖ ≤
        ε₂ + |MJ| * (2 * (ε₁ * (2 * π))) := by
    intro θ hθ
    obtain ⟨h1, h2⟩ := norm_conj_projE0_le
      (holW_mem_unitary k' isOpen_ball hG (circ_mem_ball hs) hθ)
      (holW_mem_unitary k isOpen_ball hG (circ_mem_ball hr₀) hθ)
    set As := star (holW G k' s θ) * projE0 * holW G k' s θ
    set Ar := star (holW G k r₀ θ) * projE0 * holW G k r₀ θ
    have heq : ((jac G s θ : ℝ) : ℂ) • As - ((jac G r₀ θ : ℝ) : ℂ) • Ar =
        ((jac G s θ - jac G r₀ θ : ℝ) : ℂ) • As + ((jac G r₀ θ : ℝ) : ℂ) • (As - Ar) := by
      simp only [ofReal_sub, sub_smul, smul_sub]
      module
    rw [heq]
    calc ‖((jac G s θ - jac G r₀ θ : ℝ) : ℂ) • As + ((jac G r₀ θ : ℝ) : ℂ) • (As - Ar)‖
        ≤ ‖((jac G s θ - jac G r₀ θ : ℝ) : ℂ) • As‖ + ‖((jac G r₀ θ : ℝ) : ℂ) • (As - Ar)‖ :=
          norm_add_le _ _
      _ = |jac G s θ - jac G r₀ θ| * ‖As‖ + |jac G r₀ θ| * ‖As - Ar‖ := by
          rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs]
      _ ≤ ε₂ * 1 + |MJ| * (2 * (ε₁ * (2 * π))) := by
          have hJr : |jac G r₀ θ| ≤ |MJ| := by
            have := hMJ θ hθ
            rw [Real.norm_eq_abs] at this
            exact this.trans (le_abs_self _)
          have hAsAr : ‖As - Ar‖ ≤ 2 * (ε₁ * (2 * π)) :=
            h2.trans (mul_le_mul_of_nonneg_left (hW θ hθ) zero_le_two)
          exact add_le_add (mul_le_mul (hJ θ hθ) h1 (norm_nonneg _) hε₂pos.le)
            (mul_le_mul hJr hAsAr (norm_nonneg _) hMJ0)
      _ = ε₂ + |MJ| * (2 * (ε₁ * (2 * π))) := by ring
  have hint : ∀ k'' : ℝ, ∀ t ∈ Ico (0 : ℝ) 1, IntervalIntegrable (fun θ => ((jac G t θ : ℝ) : ℂ) •
      (star (holW G k'' t θ) * projE0 * holW G k'' t θ)) volume 0 (2 * π) := fun k'' t ht =>
    (continuousOn_holA_integrand k'' hG ht).intervalIntegrable_of_Icc (by positivity)
  rw [holA, holA, ← intervalIntegral.integral_sub (hint k' s hs) (hint k r₀ hr₀)]
  calc _ ≤ (ε₂ + |MJ| * (2 * (ε₁ * (2 * π)))) * |2 * π - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => hpt θ ?_
        rw [uIoc_of_le (by positivity)] at hθ
        exact Ioc_subset_Icc_self hθ
    _ = 2 * π * ε₂ + 8 * π ^ 2 * |MJ| * ε₁ := by
        rw [sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]; ring
    _ ≤ ε := by
        have e1 : 2 * π * ε₂ = ε / 2 := by rw [hε₂]; field_simp; ring
        have e2 : 8 * π ^ 2 * |MJ| * ε₁ ≤ ε / 2 := by
          have : 8 * π ^ 2 * |MJ| * ε₁ = ε / 2 * (|MJ| / (|MJ| + 1)) := by
            rw [hε₁]; field_simp; ring
          rw [this]
          refine mul_le_of_le_one_right (by positivity) ?_
          rw [div_le_one (by positivity)]; linarith
        linarith

set_option maxHeartbeats 1000000 in
/-- Uniform lower bound for the spectral tails near a positive radius. -/
lemma spectralTail_holL_ge (hG : DifferentiableOn ℂ G (ball 0 1)) (hinj : InjOn G (ball 0 1))
    (hk : 0 < k) (m : ℕ) {r₀ : ℝ} (hr₀ : r₀ ∈ Ioo (0 : ℝ) 1) :
    ∃ c > 0, ∃ η > 0, ∀ s ∈ Ico (0 : ℝ) 1, |s - r₀| < η → ∀ k' : ℝ, |k' - k| < η →
      ENNReal.ofReal c ≤ spectralTail m (holL G k' s) := by
  let b : HilbertBasis ℕ ℂ L2N := default
  let V : Submodule ℂ L2N := Submodule.span ℂ (Set.range (fun i : Fin (m + 1) => b i))
  haveI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hli : LinearIndependent ℂ (fun i : Fin (m + 1) => b i) :=
    b.orthonormal.linearIndependent.comp _ Fin.val_injective
  have hV : m < Module.finrank ℂ V := by
    rw [finrank_span_eq_card hli]; simp
  have hr₀' : r₀ ∈ Ico (0 : ℝ) 1 := Ioo_subset_Ico_self hr₀
  -- the minimum of the quadratic form of `A_{r₀}` on the unit sphere of `V`
  have hsph : IsCompact (sphere (0 : V) 1) := isCompact_sphere 0 1
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (lt_of_le_of_lt (Nat.zero_le m) hV)
  have hne : (sphere (0 : V) 1).Nonempty := NormedSpace.sphere_nonempty.2 zero_le_one
  have hcont : ContinuousOn (fun z : V => RCLike.re ⟪(z : L2N), holA G k r₀ z⟫_ℂ)
      (sphere (0 : V) 1) := by
    apply Continuous.continuousOn
    have : Continuous fun z : V => (z : L2N) := continuous_subtype_val
    exact RCLike.continuous_re.comp (this.inner ((holA G k r₀).continuous.comp this))
  obtain ⟨z₀, hz₀, hmin⟩ := hsph.exists_isMinOn hne hcont
  set μ := RCLike.re ⟪(z₀ : L2N), holA G k r₀ z₀⟫_ℂ with hμ
  have hz₀ne : (z₀ : L2N) ≠ 0 := by
    intro h
    have : ‖z₀‖ = 1 := by simpa using hz₀
    rw [Submodule.coe_norm, h, norm_zero] at this
    exact zero_ne_one this
  have hμpos : 0 < μ := holA_pos k hG hinj hk.ne' hr₀ hz₀ne
  obtain ⟨η, hη, hA⟩ := norm_holA_sub_le k hG hr₀' (half_pos hμpos)
  refine ⟨(k / 2) ^ 2 / 2 * (μ / 2), by positivity, min η (k / 2), lt_min hη (by positivity),
    fun s hs hsη k' hk' => ?_⟩
  have hsη₁ : |s - r₀| < η := lt_of_lt_of_le hsη (min_le_left _ _)
  have hkη : |k' - k| < η := lt_of_lt_of_le hk' (min_le_left _ _)
  have hk2 : k / 2 ≤ k' := by
    have := lt_of_lt_of_le hk' (min_le_right _ _)
    rw [abs_lt] at this; linarith [this.1]
  have hbound : ∀ z ∈ V, ‖z‖ = 1 → μ / 2 ≤ RCLike.re ⟪z, holA G k' s z⟫_ℂ := by
    intro z hzV hz1
    have h1 : μ ≤ RCLike.re ⟪z, holA G k r₀ z⟫_ℂ :=
      hmin (show (⟨z, hzV⟩ : V) ∈ sphere (0 : V) 1 by simpa using hz1)
    have h2 : |RCLike.re ⟪z, (holA G k' s - holA G k r₀) z⟫_ℂ| ≤ μ / 2 := by
      calc |RCLike.re ⟪z, (holA G k' s - holA G k r₀) z⟫_ℂ|
          ≤ ‖⟪z, (holA G k' s - holA G k r₀) z⟫_ℂ‖ := RCLike.abs_re_le_norm _
        _ ≤ ‖z‖ * ‖(holA G k' s - holA G k r₀) z‖ := norm_inner_le_norm _ _
        _ ≤ ‖z‖ * (‖holA G k' s - holA G k r₀‖ * ‖z‖) := by
            gcongr; exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ μ / 2 := by rw [hz1, one_mul, mul_one]; exact hA s hs hsη₁ k' hkη
    have h3 : RCLike.re ⟪z, holA G k' s z⟫_ℂ = RCLike.re ⟪z, holA G k r₀ z⟫_ℂ +
        RCLike.re ⟪z, (holA G k' s - holA G k r₀) z⟫_ℂ := by
      simp
    rw [h3]
    linarith [neg_abs_le (RCLike.re ⟪z, (holA G k' s - holA G k r₀) z⟫_ℂ)]
  have htail : ENNReal.ofReal (μ / 2) ≤ spectralTail m (holA G k' s) :=
    ofReal_le_spectralTail (A := holA G k' s) (δ := μ / 2) hV hbound
  have hc0 : (0 : ℝ) ≤ k' ^ 2 / 2 := by positivity
  have hc1 : (0 : ℝ) ≤ (k / 2) ^ 2 / 2 := by positivity
  rw [holL_eq, spectralTail_smul m (k' ^ 2 / 2) hc0, spectralTail_conj (holM_mem_unitary k' hG hs),
    ENNReal.ofReal_mul hc1]
  have hkk : (k / 2) ^ 2 / 2 ≤ k' ^ 2 / 2 := by
    have : 0 ≤ k / 2 := by positivity
    have : (k / 2) ^ 2 ≤ k' ^ 2 := pow_le_pow_left₀ this hk2 2
    linarith
  exact (mul_le_mul_left (ENNReal.ofReal_le_ofReal hkk) _).trans (mul_le_mul_right htail _)

/-- For `0 < r < 1` and every `m`, `τ_m(L_{r,k}) > 0`. -/
theorem spectralTail_holL_pos (hG : DifferentiableOn ℂ G (ball 0 1))
    (hinj : InjOn G (ball 0 1)) (hk : 0 < k) (m : ℕ) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    0 < spectralTail m (holL G k r) := by
  obtain ⟨c, hc, η, hη, h⟩ := spectralTail_holL_ge k hG hinj hk m hr
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 hc)
    (h r (Ioo_subset_Ico_self hr) (by simpa using hη) k (by simpa using hη))

/-- Positivity of the tail integral `∫₀¹ τ_m(L_{r,k}) dr`. -/
theorem tail_integral_pos_aux (hG : DifferentiableOn ℂ G (ball 0 1)) (hinj : InjOn G (ball 0 1))
    (hk : 0 < k) (m : ℕ) :
    0 < ∫⁻ r in Ico 0 1, spectralTail m (holL G k r) := by
  obtain ⟨c, hc, η, hη, h⟩ := spectralTail_holL_ge k hG hinj hk m
    (show (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 by norm_num)
  set η' := min η (1 / 2) with hη'
  have hη'pos : 0 < η' := lt_min hη (by norm_num)
  have hsub : Ioo (1 / 2 - η') (1 / 2 + η') ⊆ Ico (0 : ℝ) 1 := by
    intro s hs
    have h1 : η' ≤ 1 / 2 := min_le_right _ _
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hbd : ∀ s ∈ Ioo (1 / 2 - η') (1 / 2 + η'),
      ENNReal.ofReal c ≤ spectralTail m (holL G k s) := by
    intro s hs
    refine h s (hsub hs) ?_ k (by simpa using hη)
    have h1 : η' ≤ η := min_le_left _ _
    rw [abs_lt]; constructor <;> linarith [hs.1, hs.2]
  calc (0 : ENNReal) < ENNReal.ofReal c * volume (Ioo (1 / 2 - η') (1 / 2 + η')) := by
        rw [Real.volume_Ioo]
        exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 hc).ne'
          (ENNReal.ofReal_pos.2 (by linarith)).ne'
    _ = ∫⁻ _ in Ioo (1 / 2 - η') (1 / 2 + η'), ENNReal.ofReal c := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ r in Ioo (1 / 2 - η') (1 / 2 + η'), spectralTail m (holL G k r) :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall hbd))
    _ ≤ ∫⁻ r in Ico 0 1, spectralTail m (holL G k r) := lintegral_mono_set hsub

end

section

/-! ## Dirichlet eigenvalues via the min–max principle -/

open MeasureTheory

/-- Smooth, compactly supported real functions whose (closed) support lies in `Ω`. -/
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

/-- The Dirichlet energy `∫ |∇u|²` (as an extended nonnegative real). -/
def dirichletEnergy (u : ℂ → ℝ) : ENNReal :=
  ∫⁻ z, ‖fderiv ℝ u z‖ₑ ^ 2

/-- The squared `L²` norm `∫ |u|²`. -/
def l2NormSq (u : ℂ → ℝ) : ENNReal :=
  ∫⁻ z, ‖u z‖ₑ ^ 2

/-- The Rayleigh quotient `∫ |∇u|² / ∫ |u|²`. -/
def rayleigh (u : ℂ → ℝ) : ENNReal :=
  dirichletEnergy u / l2NormSq u

/-- The `j`-th Dirichlet eigenvalue `λ_j(Ω)` (counted with multiplicity, `j ≥ 1`),
defined by the min–max principle. -/
def dirichletEigenvalue (Ω : Set ℂ) (j : ℕ) : ENNReal :=
  ⨅ (V : Submodule ℝ (ℂ → ℝ)) (_ : V ≤ testFunctions Ω) (_ : Module.finrank ℝ V = j),
    ⨆ (u : ℂ → ℝ) (_ : u ∈ V) (_ : u ≠ 0), rayleigh u

end

section

/-! ## Elementary properties of the min–max Dirichlet eigenvalues -/

open MeasureTheory

lemma testFunctions_mono {Ω Ω' : Set ℂ} (h : Ω ⊆ Ω') : testFunctions Ω ≤ testFunctions Ω' :=
  fun _ ⟨hu, hu', hu''⟩ => ⟨hu, hu', hu''.trans h⟩

/-- Domain monotonicity: if `Ω ⊆ Ω'` then `λ_j(Ω') ≤ λ_j(Ω)`. -/
theorem dirichletEigenvalue_anti {Ω Ω' : Set ℂ} (h : Ω ⊆ Ω') (j : ℕ) :
    dirichletEigenvalue Ω' j ≤ dirichletEigenvalue Ω j := by
  unfold dirichletEigenvalue
  refine le_iInf fun V => le_iInf fun hV => le_iInf fun hj => ?_
  exact iInf_le_of_le V (iInf_le_of_le (hV.trans (testFunctions_mono h)) (iInf_le_of_le hj le_rfl))

/-- With the min–max convention, the "zeroth eigenvalue" is `0`. -/
@[simp] lemma dirichletEigenvalue_zero (Ω : Set ℂ) : dirichletEigenvalue Ω 0 = 0 := by
  refine le_antisymm ?_ bot_le
  unfold dirichletEigenvalue
  refine iInf_le_of_le ⊥ (iInf_le_of_le bot_le (iInf_le_of_le (finrank_bot ℝ _) ?_))
  refine iSup_le fun u => iSup_le fun hu => iSup_le fun hne => ?_
  exact absurd ((Submodule.mem_bot ℝ).1 hu) hne

/-- The eigenvalues are nondecreasing in the index: `λ_j(Ω) ≤ λ_{j+1}(Ω)`. -/
theorem dirichletEigenvalue_le_succ (Ω : Set ℂ) (j : ℕ) :
    dirichletEigenvalue Ω j ≤ dirichletEigenvalue Ω (j + 1) := by
  unfold dirichletEigenvalue
  refine le_iInf fun V => le_iInf fun hV => le_iInf fun hj => ?_
  have hfin : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hj
  let b := Module.finBasisOfFinrankEq ℝ V hj
  let f : Fin j → (ℂ → ℝ) := fun i => (b (Fin.castSucc i) : ℂ → ℝ)
  have hli : LinearIndependent ℝ f := by
    have h1 : LinearIndependent ℝ (fun i : Fin j => b (Fin.castSucc i)) :=
      b.linearIndependent.comp _ (Fin.castSucc_injective j)
    exact h1.map' V.subtype (Submodule.ker_subtype V)
  let W := Submodule.span ℝ (Set.range f)
  have hWV : W ≤ V := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (b (Fin.castSucc i)).2
  have hWdim : Module.finrank ℝ W = j := by
    simpa using finrank_span_eq_card hli
  refine iInf_le_of_le W (iInf_le_of_le (hWV.trans hV) (iInf_le_of_le hWdim ?_))
  exact iSup_mono fun u => iSup_mono' fun hu => ⟨hWV hu, le_rfl⟩

/-- The eigenvalues are monotone in the index. -/
theorem dirichletEigenvalue_mono (Ω : Set ℂ) : Monotone (dirichletEigenvalue Ω) :=
  monotone_nat_of_le_succ (dirichletEigenvalue_le_succ Ω)

/-- A finite-dimensional space of test functions on `Ω` is a space of test functions
on some member of any directed open cover of `Ω`. -/
lemma exists_testFunctions_of_directed {ι : Type*} [Nonempty ι] {Ω : Set ℂ}
    (Ωs : ι → Set ℂ) (hopen : ∀ i, IsOpen (Ωs i)) (hdir : Directed (· ⊆ ·) Ωs)
    (hunion : Ω ⊆ ⋃ i, Ωs i) (V : Submodule ℝ (ℂ → ℝ)) [FiniteDimensional ℝ V]
    (hV : V ≤ testFunctions Ω) : ∃ i, V ≤ testFunctions (Ωs i) := by
  let b := Module.finBasis ℝ V
  let K : Set ℂ := ⋃ k, tsupport (b k : ℂ → ℝ)
  have hK : IsCompact K := isCompact_iUnion fun k => (hV (b k).2).2.1
  have hKΩ : K ⊆ ⋃ i, Ωs i :=
    (Set.iUnion_subset fun k => (hV (b k).2).2.2).trans hunion
  obtain ⟨i, hi⟩ := hK.elim_directed_cover Ωs hopen hKΩ hdir
  refine ⟨i, ?_⟩
  have hspan : V = Submodule.span ℝ (Set.range fun k => (b k : ℂ → ℝ)) := by
    have := b.span_eq
    apply le_antisymm
    · intro u hu
      have hu' : (⟨u, hu⟩ : V) ∈ Submodule.span ℝ (Set.range b) := by rw [this]; trivial
      have := Submodule.apply_mem_span_image_of_mem_span V.subtype hu'
      rw [← Set.range_comp] at this
      simpa [Function.comp_def] using this
    · apply Submodule.span_le.2
      rintro _ ⟨k, rfl⟩
      exact (b k).2
  rw [hspan, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  have hk := hV (b k).2
  exact ⟨hk.1, hk.2.1, fun z hz => hi (Set.mem_iUnion.2 ⟨k, hz⟩)⟩

/-- Spectral convergence under exhaustion:
for a directed family of open sets `Ωs i` with union `Ω`,
`λ_j(Ω) = inf_i λ_j(Ωs i)`. -/
theorem dirichletEigenvalue_iUnion_directed {ι : Type*} [Nonempty ι]
    (Ωs : ι → Set ℂ) (hopen : ∀ i, IsOpen (Ωs i)) (hdir : Directed (· ⊆ ·) Ωs) (j : ℕ) :
    dirichletEigenvalue (⋃ i, Ωs i) j = ⨅ i, dirichletEigenvalue (Ωs i) j := by
  apply le_antisymm
  · exact le_iInf fun i => dirichletEigenvalue_anti (Set.subset_iUnion Ωs i) j
  · conv_rhs => unfold dirichletEigenvalue
    refine le_iInf fun V => le_iInf fun hV => le_iInf fun hj => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simp [dirichletEigenvalue_zero]
    · have : FiniteDimensional ℝ V := Module.finite_of_finrank_pos (hj ▸ hjpos)
      obtain ⟨i, hi⟩ := exists_testFunctions_of_directed Ωs hopen hdir le_rfl V hV
      refine iInf_le_of_le i ?_
      unfold dirichletEigenvalue
      exact iInf_le_of_le V (iInf_le_of_le hi (iInf_le_of_le hj le_rfl))

end

section

/-! ## The Poincaré inequality -/

open MeasureTheory Metric

lemma integral_sq_eq_neg_integral_re_mul (u : ℂ → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hc : HasCompactSupport u) :
    ∫ z, (u z) ^ 2 = - ∫ z, z.re * (2 * u z * fderiv ℝ u z 1) := by
  have hd : Differentiable ℝ u := hu.differentiable (by simp)
  have hfc : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by simp)
  have hcf : HasCompactSupport (fderiv ℝ u) := hc.fderiv (𝕜 := ℝ)
  have hcu : Continuous u := hu.continuous
  have hsq : HasCompactSupport (fun z => u z ^ 2) :=
    hc.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
  have hprod : HasCompactSupport fun z : ℂ => z.re * (2 * u z * fderiv ℝ u z 1) := by
    apply HasCompactSupport.mul_left
    apply HasCompactSupport.mul_right
    apply HasCompactSupport.mul_left
    exact hc
  have hcont1 : Continuous fun z => fderiv ℝ u z 1 := hfc.clm_apply continuous_const
  have h1 : ∀ z, fderiv ℝ (fun z : ℂ => z.re) z 1 = 1 := by
    intro z
    rw [show (fun z : ℂ => z.re) = Complex.reCLM from rfl, ContinuousLinearMap.fderiv]
    simp
  have h2 : ∀ z, fderiv ℝ (fun z => (u z) ^ 2) z 1 = 2 * u z * fderiv ℝ u z 1 := by
    intro z
    change (fderiv ℝ (u ^ 2) z) 1 = _
    rw [fderiv_pow 2 (hd z)]
    simp
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun z : ℂ => z.re) (g := fun z => (u z) ^ 2) (v := (1 : ℂ)) ?_ ?_ ?_
    (fun _ _ => Complex.reCLM.differentiableAt)
    (fun _ _ => (hd.pow 2).differentiableAt)
  · simp only [h1, h2, one_mul] at key
    rw [key, neg_neg]
  · simp only [h1, one_mul]
    exact (hu.continuous.pow 2).integrable_of_hasCompactSupport hsq
  · simp only [h2]
    exact Continuous.integrable_of_hasCompactSupport (by fun_prop) hprod
  · refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    exact hsq.mul_left

lemma integral_sq_eq_neg_integral_re_sub_mul (a : ℝ) (u : ℂ → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hc : HasCompactSupport u) :
    ∫ z, (u z) ^ 2 = - ∫ z, (z.re - a) * (2 * u z * fderiv ℝ u z 1) := by
  have hd : Differentiable ℝ u := hu.differentiable (by simp)
  have hfc : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by simp)
  have hcf : HasCompactSupport (fderiv ℝ u) := hc.fderiv (𝕜 := ℝ)
  have hcu : Continuous u := hu.continuous
  have hsq : HasCompactSupport (fun z => u z ^ 2) :=
    hc.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
  have hprod : HasCompactSupport fun z : ℂ => (z.re - a) * (2 * u z * fderiv ℝ u z 1) := by
    apply HasCompactSupport.mul_left
    apply HasCompactSupport.mul_right
    apply HasCompactSupport.mul_left
    exact hc
  have hcont1 : Continuous fun z => fderiv ℝ u z 1 := hfc.clm_apply continuous_const
  have hdre : Differentiable ℝ (fun z : ℂ => z.re - a) :=
    Complex.reCLM.differentiable.sub_const a
  have h1 : ∀ z, fderiv ℝ (fun z : ℂ => z.re - a) z 1 = 1 := by
    intro z
    rw [fderiv_sub_const]
    change (fderiv ℝ (Complex.reCLM : ℂ → ℝ) z) 1 = 1
    rw [ContinuousLinearMap.fderiv]
    simp
  have h2 : ∀ z, fderiv ℝ (fun z => (u z) ^ 2) z 1 = 2 * u z * fderiv ℝ u z 1 := by
    intro z
    change (fderiv ℝ (u ^ 2) z) 1 = _
    rw [fderiv_pow 2 (hd z)]
    simp
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun z : ℂ => z.re - a) (g := fun z => (u z) ^ 2) (v := (1 : ℂ)) ?_ ?_ ?_
    (fun _ _ => hdre.differentiableAt)
    (fun _ _ => (hd.pow 2).differentiableAt)
  · simp only [h1, h2, one_mul] at key
    rw [key, neg_neg]
  · simp only [h1, one_mul]
    exact (hu.continuous.pow 2).integrable_of_hasCompactSupport hsq
  · simp only [h2]
    exact Continuous.integrable_of_hasCompactSupport (by fun_prop) hprod
  · refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    exact hsq.mul_left

set_option maxHeartbeats 1000000 in
/-- **Poincaré inequality**: for a bounded set `Ω` there is `C > 0`
with `∫ |u|² ≤ C ∫ |∇u|²` for all smooth compactly supported `u` with support in `Ω`. -/
theorem poincare_inequality (Ω : Set ℂ) (hb : Bornology.IsBounded Ω) :
    ∃ C : NNReal, 0 < C ∧ ∀ u ∈ testFunctions Ω, l2NormSq u ≤ C * dirichletEnergy u := by
  obtain ⟨R₀, hR₀⟩ := hb.subset_closedBall 0
  set R : ℝ := max R₀ 1 with hR
  have hR1 : 1 ≤ R := le_max_right _ _
  have hΩR : Ω ⊆ closedBall 0 R := hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  refine ⟨(4 * R ^ 2).toNNReal, Real.toNNReal_pos.2 (by positivity), ?_⟩
  rintro u ⟨hu, hc, hsupp⟩
  have hd : Differentiable ℝ u := hu.differentiable (by simp)
  have hfc : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by simp)
  have hcf : HasCompactSupport (fderiv ℝ u) := hc.fderiv (𝕜 := ℝ)
  have hcu : Continuous u := hu.continuous
  have hsq : HasCompactSupport (fun z => u z ^ 2) :=
    hc.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
  have hprod : HasCompactSupport fun z : ℂ => -(z.re * (2 * u z * fderiv ℝ u z 1)) := by
    apply HasCompactSupport.neg
    apply HasCompactSupport.mul_left
    apply HasCompactSupport.mul_right
    apply HasCompactSupport.mul_left
    exact hc
  set A := ∫ z, (u z) ^ 2 with hA
  set D := ∫ z, ‖fderiv ℝ u z‖ ^ 2 with hD
  have hintA : Integrable (fun z => (u z) ^ 2) volume :=
    (hu.continuous.pow 2).integrable_of_hasCompactSupport hsq
  have hintD : Integrable (fun z => ‖fderiv ℝ u z‖ ^ 2) volume := by
    refine (hfc.norm.pow 2).integrable_of_hasCompactSupport ?_
    set_option maxHeartbeats 1000000 in
      exact hcf.norm.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
  -- pointwise AM-GM bound
  have hpt : ∀ z, -(z.re * (2 * u z * fderiv ℝ u z 1)) ≤
      (u z) ^ 2 / 2 + 2 * R ^ 2 * ‖fderiv ℝ u z‖ ^ 2 := by
    intro z
    by_cases huz : u z = 0
    · simp [huz]; positivity
    have hz : z ∈ closedBall (0 : ℂ) R :=
      hΩR (hsupp (subset_tsupport u huz))
    have hre : |z.re| ≤ R := by
      have := Complex.abs_re_le_norm z
      rw [mem_closedBall, dist_zero_right] at hz
      linarith
    have hder : |fderiv ℝ u z 1| ≤ ‖fderiv ℝ u z‖ := by
      have := (fderiv ℝ u z).le_opNorm 1
      rw [norm_one, mul_one, Real.norm_eq_abs] at this
      exact this
    set a := u z
    set d := fderiv ℝ u z 1
    set N := ‖fderiv ℝ u z‖
    have h1 : -(z.re * (2 * a * d)) ≤ 2 * R * |a| * |d| := by
      have : |z.re * (2 * a * d)| = 2 * |z.re| * |a| * |d| := by
        rw [abs_mul, abs_mul, abs_mul]; norm_num; ring
      have h3 : -(z.re * (2 * a * d)) ≤ |z.re * (2 * a * d)| := neg_le_abs _
      rw [this] at h3
      have : 2 * |z.re| * |a| * |d| ≤ 2 * R * |a| * |d| := by gcongr
      linarith
    have h2 : 2 * R * |a| * |d| ≤ a ^ 2 / 2 + 2 * R ^ 2 * d ^ 2 := by
      nlinarith [sq_nonneg (|a| - 2 * R * |d|), sq_abs a, sq_abs d]
    have h4 : d ^ 2 ≤ N ^ 2 := by
      rw [← sq_abs d]; exact pow_le_pow_left₀ (abs_nonneg _) hder 2
    nlinarith
  have hint_lhs : Integrable (fun z : ℂ => -(z.re * (2 * u z * fderiv ℝ u z 1))) volume := by
    exact Continuous.integrable_of_hasCompactSupport (by fun_prop) hprod
  have hAD : A ≤ A / 2 + 2 * R ^ 2 * D := by
    have := integral_mono (g := fun z => u z ^ 2 / 2 + 2 * R ^ 2 * ‖fderiv ℝ u z‖ ^ 2)
      hint_lhs ((hintA.div_const 2).add (hintD.const_mul _)) hpt
    rw [integral_neg, ← integral_sq_eq_neg_integral_re_mul u hu hc, integral_add
      (hintA.div_const 2) (hintD.const_mul _), integral_div, integral_const_mul] at this
    exact this
  have hAD' : A ≤ 4 * R ^ 2 * D := by linarith
  -- convert to lintegrals
  have hl2 : l2NormSq u = ENNReal.ofReal A := by
    rw [hA, ofReal_integral_eq_lintegral_ofReal hintA (Filter.Eventually.of_forall
      fun z => sq_nonneg _)]
    unfold l2NormSq
    congr 1; ext z
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
  have hen : dirichletEnergy u = ENNReal.ofReal D := by
    rw [hD, ofReal_integral_eq_lintegral_ofReal hintD (Filter.Eventually.of_forall
      fun z => sq_nonneg _)]
    unfold dirichletEnergy
    congr 1; ext z
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [hl2, hen]
  change ENNReal.ofReal A ≤ ENNReal.ofReal (4 * R ^ 2) * ENNReal.ofReal D
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hAD'

set_option maxHeartbeats 1000000 in
/-- Poincaré inequality with an explicit constant: if `Ω ⊆ closedBall c ρ`, then
`∫ |u|² ≤ 4ρ² ∫ |∇u|²` for all test functions `u` on `Ω`. -/
theorem poincare_inequality_closedBall (Ω : Set ℂ) (c : ℂ) {ρ : ℝ} (hΩ : Ω ⊆ closedBall c ρ) :
    ∀ u ∈ testFunctions Ω, l2NormSq u ≤ ENNReal.ofReal (4 * ρ ^ 2) * dirichletEnergy u := by
  rintro u ⟨hu, hc, hsupp⟩
  have hd : Differentiable ℝ u := hu.differentiable (by simp)
  have hfc : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by simp)
  have hcf : HasCompactSupport (fderiv ℝ u) := hc.fderiv (𝕜 := ℝ)
  have hcu : Continuous u := hu.continuous
  have hsq : HasCompactSupport (fun z => u z ^ 2) :=
    hc.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
  have hprod : HasCompactSupport fun z : ℂ => -((z.re - c.re) * (2 * u z * fderiv ℝ u z 1)) := by
    apply HasCompactSupport.neg
    apply HasCompactSupport.mul_left
    apply HasCompactSupport.mul_right
    apply HasCompactSupport.mul_left
    exact hc
  set A := ∫ z, (u z) ^ 2 with hA
  set D := ∫ z, ‖fderiv ℝ u z‖ ^ 2 with hD
  have hintA : Integrable (fun z => (u z) ^ 2) volume :=
    (hu.continuous.pow 2).integrable_of_hasCompactSupport hsq
  have hintD : Integrable (fun z => ‖fderiv ℝ u z‖ ^ 2) volume := by
    refine (hfc.norm.pow 2).integrable_of_hasCompactSupport ?_
    set_option maxHeartbeats 1000000 in
      exact hcf.norm.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
  have hpt : ∀ z, -((z.re - c.re) * (2 * u z * fderiv ℝ u z 1)) ≤
      (u z) ^ 2 / 2 + 2 * ρ ^ 2 * ‖fderiv ℝ u z‖ ^ 2 := by
    intro z
    by_cases huz : u z = 0
    · simp [huz]; positivity
    have hz : z ∈ closedBall c ρ := hΩ (hsupp (subset_tsupport u huz))
    have hre : |z.re - c.re| ≤ ρ := by
      have := Complex.abs_re_le_norm (z - c)
      rw [mem_closedBall, dist_eq_norm] at hz
      rw [Complex.sub_re] at this
      linarith
    have hder : |fderiv ℝ u z 1| ≤ ‖fderiv ℝ u z‖ := by
      have := (fderiv ℝ u z).le_opNorm 1
      rw [norm_one, mul_one, Real.norm_eq_abs] at this
      exact this
    set a := u z
    set d := fderiv ℝ u z 1
    set N := ‖fderiv ℝ u z‖
    set x := z.re - c.re
    have h1 : -(x * (2 * a * d)) ≤ 2 * ρ * |a| * |d| := by
      have : |x * (2 * a * d)| = 2 * |x| * |a| * |d| := by
        rw [abs_mul, abs_mul, abs_mul]; norm_num; ring
      have h3 : -(x * (2 * a * d)) ≤ |x * (2 * a * d)| := neg_le_abs _
      rw [this] at h3
      have : 2 * |x| * |a| * |d| ≤ 2 * ρ * |a| * |d| := by gcongr
      linarith
    have h2 : 2 * ρ * |a| * |d| ≤ a ^ 2 / 2 + 2 * ρ ^ 2 * d ^ 2 := by
      nlinarith [sq_nonneg (|a| - 2 * ρ * |d|), sq_abs a, sq_abs d]
    have h4 : d ^ 2 ≤ N ^ 2 := by
      rw [← sq_abs d]; exact pow_le_pow_left₀ (abs_nonneg _) hder 2
    nlinarith
  have hint_lhs : Integrable (fun z : ℂ => -((z.re - c.re) * (2 * u z * fderiv ℝ u z 1)))
      volume := by
    exact Continuous.integrable_of_hasCompactSupport (by fun_prop) hprod
  have hAD : A ≤ A / 2 + 2 * ρ ^ 2 * D := by
    have := integral_mono (g := fun z => u z ^ 2 / 2 + 2 * ρ ^ 2 * ‖fderiv ℝ u z‖ ^ 2)
      hint_lhs ((hintA.div_const 2).add (hintD.const_mul _)) hpt
    rw [integral_neg, ← integral_sq_eq_neg_integral_re_sub_mul c.re u hu hc, integral_add
      (hintA.div_const 2) (hintD.const_mul _), integral_div, integral_const_mul] at this
    exact this
  have hAD' : A ≤ 4 * ρ ^ 2 * D := by linarith
  have hl2 : l2NormSq u = ENNReal.ofReal A := by
    rw [hA, ofReal_integral_eq_lintegral_ofReal hintA (Filter.Eventually.of_forall
      fun z => sq_nonneg _)]
    unfold l2NormSq
    congr 1; ext z
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
  have hen : dirichletEnergy u = ENNReal.ofReal D := by
    rw [hD, ofReal_integral_eq_lintegral_ofReal hintD (Filter.Eventually.of_forall
      fun z => sq_nonneg _)]
    unfold dirichletEnergy
    congr 1; ext z
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [hl2, hen, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hAD'

/-- A nonzero continuous function has positive `L²` norm. -/
lemma l2NormSq_pos_of_ne_zero {u : ℂ → ℝ} (hu : Continuous u) (hne : u ≠ 0) :
    0 < l2NormSq u := by
  obtain ⟨z, hz⟩ : ∃ z, u z ≠ 0 := by
    by_contra h; push_neg at h; exact hne (funext h)
  unfold l2NormSq
  have hm : Measurable fun x => ‖u x‖ₑ ^ 2 := by fun_prop
  rw [lintegral_pos_iff_support hm]
  have : Function.support (fun x => ‖u x‖ₑ ^ 2) = {x | u x ≠ 0} := by
    ext x; simp
  rw [this]
  exact (isOpen_ne_fun hu continuous_const).measure_pos volume ⟨z, hz⟩

end

section

/-! ## Disk automorphisms `z ↦ (z - a) / (1 - ā z)` -/

open Complex Metric

/-- The disk automorphism `mob a z = (z - a) / (1 - ā z)`. -/
def mob (a z : ℂ) : ℂ := (z - a) / (1 - (starRingEnd ℂ) a * z)

lemma mob_denom_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    1 - (starRingEnd ℂ) a * z ≠ 0 := by
  intro h
  have h1 : (starRingEnd ℂ) a * z = 1 := by linear_combination -h
  have : ‖(starRingEnd ℂ) a * z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    calc ‖a‖ * ‖z‖ ≤ ‖a‖ * 1 := by gcongr
      _ < 1 := by linarith
  rw [h1] at this
  simp at this

/-- The key identity `|1 - ā z|² - |z - a|² = (1 - |a|²)(1 - |z|²)`. -/
lemma normSq_identity (a z : ℂ) :
    normSq (1 - (starRingEnd ℂ) a * z) - normSq (z - a) =
      (1 - normSq a) * (1 - normSq z) := by
  simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, conj_re, conj_im, one_re, one_im]
  ring

lemma norm_mob_lt_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : ‖mob a z‖ < 1 := by
  have hd := mob_denom_ne_zero ha hz
  unfold mob
  rw [norm_div, div_lt_one (norm_pos_iff.2 hd)]
  have hid := normSq_identity a z
  have ha2 : normSq a < 1 := by
    rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have hz2 : normSq z < 1 := by
    rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have : normSq (z - a) < normSq (1 - (starRingEnd ℂ) a * z) := by
    nlinarith [mul_pos (sub_pos.2 ha2) (sub_pos.2 hz2)]
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at this
  nlinarith [norm_nonneg (z - a), norm_nonneg (1 - (starRingEnd ℂ) a * z)]

lemma mob_mem_ball {a z : ℂ} (ha : a ∈ ball (0 : ℂ) 1) (hz : z ∈ ball (0 : ℂ) 1) :
    mob a z ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff] at *
  exact norm_mob_lt_one ha hz

@[simp] lemma mob_self (a : ℂ) : mob a a = 0 := by simp [mob]

@[simp] lemma mob_zero (a : ℂ) : mob a 0 = -a := by simp [mob]

lemma mob_neg_mob {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : mob (-a) (mob a z) = z := by
  have hd := mob_denom_ne_zero ha hz
  have hna : 1 - (starRingEnd ℂ) a * a ≠ 0 := mob_denom_ne_zero ha ha
  unfold mob
  rw [map_neg]
  have h2 : 1 - -(starRingEnd ℂ) a * ((z - a) / (1 - (starRingEnd ℂ) a * z)) =
      (1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z) := by
    field_simp; ring
  rw [h2, div_eq_iff (div_ne_zero hna hd)]
  generalize (starRingEnd ℂ) a = c at *
  rw [div_sub' hd, mul_div_assoc', div_left_inj' hd]
  ring

lemma mob_injOn {a : ℂ} (ha : ‖a‖ < 1) : Set.InjOn (mob a) (ball 0 1) := by
  intro z hz w hw h
  rw [mem_ball_zero_iff] at hz hw
  rw [← mob_neg_mob ha hz, ← mob_neg_mob ha hw, h]

lemma hasDerivAt_mob {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    HasDerivAt (mob a) ((1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z) ^ 2) z := by
  have hd := mob_denom_ne_zero ha hz
  have h1 : HasDerivAt (fun w => w - a) 1 z := (hasDerivAt_id z).sub_const a
  have h2 : HasDerivAt (fun w => 1 - (starRingEnd ℂ) a * w) (-(starRingEnd ℂ) a) z := by
    simpa using ((hasDerivAt_id z).const_mul ((starRingEnd ℂ) a)).const_sub 1
  have := h1.div h2 hd
  change HasDerivAt ((fun w => w - a) / fun w => 1 - (starRingEnd ℂ) a * w)
    ((1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z) ^ 2) z
  convert this using 1
  field_simp
  ring

lemma differentiableAt_mob {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (mob a) z := (hasDerivAt_mob ha hz).differentiableAt

lemma mob_eq_zero_iff {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : mob a z = 0 ↔ z = a := by
  constructor
  · intro h
    have hd := mob_denom_ne_zero ha hz
    unfold mob at h
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hd
  · rintro rfl; simp

end

section

/-! ## Holomorphic square roots on simply connected domains -/

open Complex Metric Filter Topology Set

/-- A continuous square root of a differentiable function is differentiable where it does
not vanish. -/
lemma hasDerivAt_of_sq_eq {g f : ℂ → ℂ} {z : ℂ} {U : Set ℂ} (hU : U ∈ 𝓝 z)
    (hg : ContinuousAt g z) (hsq : ∀ w ∈ U, g w ^ 2 = f w) (hf : DifferentiableAt ℂ f z)
    (hgz : g z ≠ 0) : HasDerivAt g (deriv f z / (2 * g z)) z := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hsum : Tendsto (fun w => g w + g z) (𝓝[≠] z) (𝓝 (2 * g z)) := by
    have : Tendsto (fun w => g w + g z) (𝓝 z) (𝓝 (g z + g z)) := hg.add tendsto_const_nhds
    rw [two_mul]
    exact this.mono_left nhdsWithin_le_nhds
  have h2 : (2 * g z) ≠ 0 := mul_ne_zero two_ne_zero hgz
  have hlim := hf.hasDerivAt.tendsto_slope.div hsum h2
  refine hlim.congr' ?_
  have hev1 : ∀ᶠ w in 𝓝[≠] z, g w + g z ≠ 0 := hsum.eventually_ne h2
  have hev2 : ∀ᶠ w in 𝓝[≠] z, w ∈ U := nhdsWithin_le_nhds hU
  filter_upwards [hev1, hev2, self_mem_nhdsWithin] with w hw1 hw2 hw3
  have hzU : z ∈ U := mem_of_mem_nhds hU
  rw [Pi.div_apply, slope_def_field, slope_def_field, ← hsq w hw2, ← hsq z hzU]
  have hwz : w - z ≠ 0 := sub_ne_zero.2 hw3
  field_simp
  ring

open Classical in
/-- **Holomorphic square roots.** A nonvanishing holomorphic function on a simply connected
open subset of `ℂ` has a holomorphic square root. -/
theorem exists_sqrt_of_simplyConnected {Ω : Set ℂ} (hΩ : IsOpen Ω) [SimplyConnectedSpace Ω]
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Ω) (hf0 : ∀ z ∈ Ω, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ Ω, g z ^ 2 = f z := by
  haveI := hΩ.locPathConnectedSpace
  obtain ⟨z0⟩ : Nonempty Ω := inferInstance
  have hp := isCoveringMap_npow (𝕜 := ℂ) 2 (by norm_num)
  let F : C(Ω, {x : ℂ // x ≠ 0}) :=
    ⟨fun z => ⟨f z, hf0 z z.2⟩, by
      refine Continuous.subtype_mk ?_ _
      exact hf.continuousOn.restrict⟩
  obtain ⟨e0, he0⟩ : ∃ e : ℂ, e ^ 2 = f z0 := IsAlgClosed.exists_pow_nat_eq _ two_pos
  have he0' : e0 ≠ 0 := by
    rintro rfl
    exact hf0 z0 z0.2 (by simpa using he0.symm)
  obtain ⟨G, ⟨-, hGp⟩, -⟩ :=
    hp.existsUnique_continuousMap_lifts F z0 ⟨e0, he0'⟩ (Subtype.ext he0)
  set g : ℂ → ℂ := fun z => if h : z ∈ Ω then ((G ⟨z, h⟩ : {x : ℂ // x ≠ 0}) : ℂ) else 0
    with hg_def
  have hsq : ∀ z ∈ Ω, g z ^ 2 = f z := by
    intro z hz
    have := congrArg Subtype.val (congrFun hGp ⟨z, hz⟩)
    simpa [hg_def, hz, F] using this
  have hne : ∀ z ∈ Ω, g z ≠ 0 := by
    intro z hz
    simp only [hg_def, hz, dite_true]
    exact (G ⟨z, hz⟩).2
  have hcont : ContinuousOn g Ω := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : Ω.domRestrict g = fun z : Ω => ((G z : {x : ℂ // x ≠ 0}) : ℂ) := by
      funext z
      simp [hg_def, z.2]
    rw [this]
    exact continuous_subtype_val.comp G.continuous
  refine ⟨g, ?_, hsq⟩
  intro z hz
  have hU : Ω ∈ 𝓝 z := hΩ.mem_nhds hz
  exact (hasDerivAt_of_sq_eq hU (hcont.continuousAt hU) hsq
    (hf.differentiableAt hU) (hne z hz)).differentiableAt.differentiableWithinAt

end

section

/-! ## Montel's theorem -/

open Complex Metric Filter Topology Set

/-- Cauchy estimate: a holomorphic family bounded by `1` on `U` is equicontinuous at every
point of `U`. -/
lemma equicontinuousAt_of_norm_le_one {ι : Type*} {F : ι → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hb : ∀ i, ∀ z ∈ U, ‖F i z‖ ≤ 1) {z : ℂ}
    (hz : z ∈ U) : EquicontinuousAt F z := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z hz
  set r := ε / 3 with hr
  have hr0 : 0 < r := by positivity
  have hsub : ∀ y ∈ ball z r, closedBall y r ⊆ U := by
    intro y hy w hw
    apply hεU
    rw [mem_ball] at hy ⊢
    rw [mem_closedBall] at hw
    calc dist w z ≤ dist w y + dist y z := dist_triangle _ _ _
      _ < r + r := by linarith
      _ < ε := by rw [hr]; linarith
  have hderiv : ∀ i, ∀ y ∈ ball z r, ‖deriv (F i) y‖ ≤ 1 / r := by
    intro i y hy
    apply norm_deriv_le_of_forall_mem_sphere_norm_le hr0
    · apply DifferentiableOn.diffContOnCl
      rw [closure_ball y hr0.ne']
      exact (hF i).mono (hsub y hy)
    · intro w hw
      exact hb i w (hsub y hy (sphere_subset_closedBall hw))
  have hdiff : ∀ i, ∀ y ∈ ball z r, DifferentiableAt ℂ (F i) y := by
    intro i y hy
    exact (hF i).differentiableAt (hU.mem_nhds (hsub y hy (mem_closedBall_self hr0.le)))
  have hlip : ∀ i, ∀ y ∈ ball z r, ‖F i y - F i z‖ ≤ 1 / r * ‖y - z‖ := fun i y hy =>
    (convex_ball z r).norm_image_sub_le_of_norm_deriv_le (hdiff i) (hderiv i)
      (mem_ball_self hr0) hy
  rw [Metric.equicontinuousAt_iff]
  intro e he
  refine ⟨min r (e * r / 2), by positivity, fun y hy i => ?_⟩
  have hy1 : y ∈ ball z r := mem_ball.2 (lt_of_lt_of_le hy (min_le_left _ _))
  have hy2 : dist y z < e * r / 2 := lt_of_lt_of_le hy (min_le_right _ _)
  rw [dist_comm, dist_eq_norm]
  calc ‖F i y - F i z‖ ≤ 1 / r * ‖y - z‖ := hlip i y hy1
    _ ≤ 1 / r * (e * r / 2) := by
        gcongr; rw [← dist_eq_norm]; exact hy2.le
    _ = e / 2 := by field_simp
    _ < e := by linarith

/-- **Montel's theorem.** A family of holomorphic functions on an open set `U`, bounded by `1`
on `U`, converges locally uniformly on `U` along any ultrafilter. -/
theorem montel {ι : Type*} (l : Ultrafilter ι) {F : ι → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hb : ∀ i, ∀ z ∈ U, ‖F i z‖ ≤ 1) :
    ∃ f : ℂ → ℂ, TendstoLocallyUniformlyOn F f (l : Filter ι) U := by
  have hpt : ∀ z, ∃ w, z ∈ U → Tendsto (fun i => F i z) (l : Filter ι) (𝓝 w) := by
    intro z
    by_cases hz : z ∈ U
    · obtain ⟨w, -, hw⟩ := (isCompact_closedBall (0 : ℂ) 1).ultrafilter_le_nhds
        (l.map (fun i => F i z)) (by
          rw [Ultrafilter.coe_map]
          refine tendsto_principal.2 (Eventually.of_forall fun i => ?_)
          rw [mem_closedBall_zero_iff]; exact hb i z hz)
      exact ⟨w, fun _ => by rwa [Ultrafilter.coe_map] at hw⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose f hf using hpt
  refine ⟨f, ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  have heq : ∀ K' ∈ ({K} : Set (Set ℂ)), EquicontinuousOn F K' := by
    rintro K' rfl x hx
    exact (equicontinuousAt_of_norm_le_one hU hF hb (hKU hx)).equicontinuousWithinAt _
  have key := (EquicontinuousOn.tendsto_uniformOnFun_iff_pi' (𝔖 := {K})
    (by simpa using hK) heq (l : Filter ι) f).2 (by
      rw [tendsto_pi_nhds]
      rintro ⟨x, hx⟩
      simp only [sUnion_singleton] at hx
      exact hf x (hKU hx))
  rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn] at key
  exact key K rfl

end

section

/-! ## Hurwitz's theorem -/

open Complex Metric Filter Topology Set

/-- Local Hurwitz theorem for nonvanishing functions. -/
theorem hurwitz_ne_zero {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → ℂ → ℂ} {g : ℂ → ℂ}
    {a : ℂ} {r : ℝ} (hr : 0 < r) (hF : ∀ i, DifferentiableOn ℂ (F i) (closedBall a r))
    (hF0 : ∀ i, ∀ z ∈ closedBall a r, F i z ≠ 0)
    (hconv : TendstoUniformlyOn F g l (closedBall a r))
    (hg : ContinuousOn g (sphere a r)) (hg0 : ∀ z ∈ sphere a r, g z ≠ 0) : g a ≠ 0 := by
  obtain ⟨z1, hz1, hmin⟩ := (isCompact_sphere a r).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 hr.le) hg.norm
  set m := ‖g z1‖ with hm
  have hm0 : 0 < m := norm_pos_iff.2 (hg0 z1 hz1)
  rw [Metric.tendstoUniformlyOn_iff] at hconv
  obtain ⟨i, hi⟩ := (hconv (m / 2) (by positivity)).exists
  have hbd : ∀ z ∈ sphere a r, ‖(F i z)⁻¹‖ ≤ 2 / m := by
    intro z hz
    have h1 : m ≤ ‖g z‖ := hmin hz
    have h2 : ‖g z - F i z‖ < m / 2 := by
      rw [← dist_eq_norm]; exact hi z (sphere_subset_closedBall hz)
    have h3 : m / 2 ≤ ‖F i z‖ := by
      have := norm_sub_norm_le (g z) (g z - F i z)
      simp only [sub_sub_cancel] at this
      linarith
    rw [norm_inv]
    calc ‖F i z‖⁻¹ ≤ (m / 2)⁻¹ := inv_anti₀ (by positivity) h3
      _ = 2 / m := by rw [inv_div]
  have hd : DiffContOnCl ℂ (fun z => (F i z)⁻¹) (ball a r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball a hr.ne']
    exact (hF i).inv (hF0 i)
  have hFa : ‖(F i a)⁻¹‖ ≤ 2 / m :=
    norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd
      (by rw [frontier_ball a hr.ne']; exact hbd) (subset_closure (mem_ball_self hr))
  have hFa' : m / 2 ≤ ‖F i a‖ := by
    have hne : F i a ≠ 0 := hF0 i a (mem_closedBall_self hr.le)
    rw [norm_inv] at hFa
    have hpos : 0 < ‖F i a‖ := norm_pos_iff.2 hne
    rw [inv_le_comm₀ hpos (by positivity), inv_div] at hFa
    exact hFa
  have hga : ‖g a - F i a‖ < m / 2 := by
    rw [← dist_eq_norm]; exact hi a (mem_closedBall_self hr.le)
  intro h0
  rw [h0, zero_sub, norm_neg] at hga
  linarith

/-- **Hurwitz's theorem.** A locally uniform limit of injective holomorphic functions on a
connected open set, whose derivative does not vanish at some point, is injective. -/
theorem hurwitz_injOn {ι : Type*} {l : Filter ι} [l.NeBot] {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hinj : ∀ i, InjOn (F i) U)
    (hconv : TendstoLocallyUniformlyOn F f l U) {z0 : ℂ} (hz0 : z0 ∈ U)
    (hd : deriv f z0 ≠ 0) : InjOn f U := by
  intro a ha b hb hab
  by_contra hne
  have hfd : DifferentiableOn ℂ f U :=
    hconv.differentiableOn (Eventually.of_forall hF) hU
  have han : AnalyticOnNhd ℂ f U := hfd.analyticOnNhd hU
  set g : ℂ → ℂ := fun z => f z - f b with hg
  have hgan : AnalyticOnNhd ℂ g U := fun z hz => (han z hz).sub analyticAt_const
  have hnz : ¬ ∀ᶠ z in 𝓝 a, g z = 0 := by
    intro hev
    have hEq : EqOn g 0 U := hgan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc ha hev
    have hloc : f =ᶠ[𝓝 z0] fun _ => f b := by
      filter_upwards [hU.mem_nhds hz0] with z hz
      have := hEq hz
      simp only [hg, Pi.zero_apply, sub_eq_zero] at this
      exact this
    apply hd
    rw [hloc.deriv_eq]
    simp
  have hev : ∀ᶠ z in 𝓝[≠] a, g z ≠ 0 :=
    ((hgan a ha).eventually_eq_zero_or_eventually_ne_zero).resolve_left hnz
  rw [eventually_nhdsWithin_iff] at hev
  have hbU : ({b}ᶜ : Set ℂ) ∈ 𝓝 a := isOpen_compl_singleton.mem_nhds hne
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.1
    (inter_mem (inter_mem hev (hU.mem_nhds ha)) hbU)
  set r := ε / 2 with hr
  have hr0 : 0 < r := by positivity
  have hcb : closedBall a r ⊆ ball a ε := closedBall_subset_ball (by rw [hr]; linarith)
  have hcbU : closedBall a r ⊆ U := fun z hz => (hεsub (hcb hz)).1.2
  have hcbb : ∀ z ∈ closedBall a r, z ≠ b := fun z hz => (hεsub (hcb hz)).2
  have hcbg : ∀ z ∈ closedBall a r, z ≠ a → g z ≠ 0 := fun z hz => (hεsub (hcb hz)).1.1
  have hunif : TendstoUniformlyOn F f l (closedBall a r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hconv _ hcbU (isCompact_closedBall a r)
  have hptb : Tendsto (fun i => F i b) l (𝓝 (f b)) := hconv.tendsto_at hb
  have hconv' : TendstoUniformlyOn (fun i z => F i z - F i b) g l (closedBall a r) :=
    hunif.sub (hptb.tendstoUniformlyOn_const _)
  have key := hurwitz_ne_zero hr0 (F := fun i z => F i z - F i b) (g := g)
    (fun i => ((hF i).mono hcbU).sub_const _)
    (fun i z hz h => hcbb z hz (hinj i (hcbU hz) hb (sub_eq_zero.1 h)))
    hconv' ((hfd.mono hcbU).continuousOn.sub continuousOn_const |>.mono
      sphere_subset_closedBall)
    (fun z hz => hcbg z (sphere_subset_closedBall hz) (by
      rintro rfl
      rw [mem_sphere, dist_self] at hz
      exact hr0.ne hz))
  exact key (by simp [hg, hab])

end

section

/-! ## The Riemann mapping theorem -/

open Complex Metric Filter Topology Set

/-- Open mapping theorem for injective holomorphic maps on a connected open set. -/
lemma isOpen_image_of_injOn {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) {s : Set ℂ} (hs : s ⊆ U)
    (hso : IsOpen s) : IsOpen (f '' s) := by
  rcases (hf.analyticOnNhd hU).is_constant_or_isOpen hUc with ⟨w, hw⟩ | h
  · rcases s.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
    · simp
    · exfalso
      obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z (hs hz)
      have hmem : z + (ε / 2 : ℝ) ∈ ball z ε := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
        linarith
      have := hinj (hεU hmem) (hs hz) ((hw _ (hεU hmem)).trans (hw z (hs hz)).symm)
      have : ((ε / 2 : ℝ) : ℂ) = 0 := by linear_combination this
      have : ε / 2 = 0 := by exact_mod_cast this
      linarith
  · exact h s hs hso

/-- The admissible family: injective holomorphic maps `Ω → 𝔻` sending `z₀` to `0`. -/
def Admissible (Ω : Set ℂ) (z₀ : ℂ) (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f Ω ∧ InjOn f Ω ∧ MapsTo f Ω (ball 0 1) ∧ f z₀ = 0

/-- The admissible family is nonempty (square-root trick). -/
lemma exists_admissible {Ω : Set ℂ} (hΩ : IsOpen Ω) [SimplyConnectedSpace Ω]
    (hne : Ω ≠ univ) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) : ∃ f, Admissible Ω z₀ f := by
  have hUc : IsPreconnected Ω := isPreconnected_iff_preconnectedSpace.2 inferInstance
  obtain ⟨a, ha⟩ : ∃ a, a ∉ Ω := by
    by_contra h; push_neg at h; exact hne (eq_univ_of_forall h)
  have hza : ∀ z ∈ Ω, z - a ≠ 0 := fun z hz h => ha (sub_eq_zero.1 h ▸ hz)
  obtain ⟨g, hgd, hgsq⟩ := exists_sqrt_of_simplyConnected hΩ
    (f := fun z => z - a) (differentiableOn_id.sub_const a) hza
  have hginj : InjOn g Ω := by
    intro z hz w hw h
    have := hgsq z hz
    rw [h, hgsq w hw] at this
    linear_combination -this
  have hgneg : ∀ z ∈ Ω, ∀ w ∈ Ω, g z ≠ -g w := by
    intro z hz w hw h
    have h1 := hgsq z hz
    rw [h, neg_sq, hgsq w hw] at h1
    have hzw : w = z := by linear_combination h1
    subst hzw
    have : g w = 0 := by linear_combination h / 2
    exact hza w hw (by rw [← hgsq w hw, this]; ring)
  have hopen : IsOpen (g '' Ω) := isOpen_image_of_injOn hΩ hUc hgd hginj subset_rfl hΩ
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 hopen (g z₀) ⟨z₀, hz₀, rfl⟩
  have hfar : ∀ z ∈ Ω, ρ ≤ ‖g z + g z₀‖ := by
    intro z hz
    by_contra hlt
    push_neg at hlt
    have : -g z ∈ ball (g z₀) ρ := by
      rw [mem_ball, dist_eq_norm, ← norm_neg]
      convert hlt using 2; ring
    obtain ⟨w, hw, hgw⟩ := hρsub this
    exact hgneg w hw z hz hgw
  have hne0 : ∀ z ∈ Ω, g z + g z₀ ≠ 0 := fun z hz h => by
    have := hfar z hz; rw [h, norm_zero] at this; linarith
  have hinvle : ∀ z ∈ Ω, ‖(g z + g z₀)⁻¹‖ ≤ 1 / ρ := by
    intro z hz
    rw [norm_inv, one_div]
    exact inv_anti₀ hρ (hfar z hz)
  refine ⟨fun z => ((ρ / 4 : ℝ) : ℂ) * ((g z + g z₀)⁻¹ - (g z₀ + g z₀)⁻¹), ?_, ?_, ?_, ?_⟩
  · intro z hz
    apply DifferentiableWithinAt.const_mul
    apply DifferentiableWithinAt.sub_const
    exact ((hgd z hz).add_const _).inv (hne0 z hz)
  · intro z hz w hw h
    simp only at h
    have hρ4 : ((ρ / 4 : ℝ) : ℂ) ≠ 0 := by
      have : ρ / 4 ≠ 0 := by positivity
      exact_mod_cast this
    have h1 := mul_left_cancel₀ hρ4 h
    have h2 : (g z + g z₀)⁻¹ = (g w + g z₀)⁻¹ := by linear_combination h1
    rw [inv_inj] at h2
    exact hginj hz hw (by linear_combination h2)
  · intro z hz
    rw [mem_ball_zero_iff, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc ρ / 4 * ‖(g z + g z₀)⁻¹ - (g z₀ + g z₀)⁻¹‖
        ≤ ρ / 4 * (‖(g z + g z₀)⁻¹‖ + ‖(g z₀ + g z₀)⁻¹‖) := by
          gcongr; exact norm_sub_le _ _
      _ ≤ ρ / 4 * (1 / ρ + 1 / ρ) := by
          gcongr
          · exact hinvle z hz
          · exact hinvle z₀ hz₀
      _ = 1 / 2 := by field_simp; ring
      _ < 1 := by norm_num
  · simp

/-- Cauchy estimate for admissible maps. -/
lemma norm_deriv_le_of_admissible {Ω : Set ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : closedBall z₀ r ⊆ Ω) {f : ℂ → ℂ} (hf : Admissible Ω z₀ f) :
    ‖deriv f z₀‖ ≤ 1 / r := by
  apply norm_deriv_le_of_forall_mem_sphere_norm_le hr
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball z₀ hr.ne']
    exact hf.1.mono hsub
  · intro w hw
    exact (mem_ball_zero_iff.1 (hf.2.2.1 (hsub (sphere_subset_closedBall hw)))).le

/-- Existence of an extremal admissible map (Montel + Hurwitz). -/
lemma exists_extremal {Ω : Set ℂ} (hΩ : IsOpen Ω) [SimplyConnectedSpace Ω]
    (hne : Ω ≠ univ) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ f, Admissible Ω z₀ f ∧ ∀ g, Admissible Ω z₀ g → ‖deriv g z₀‖ ≤ ‖deriv f z₀‖ := by
  have hUc : IsPreconnected Ω := isPreconnected_iff_preconnectedSpace.2 inferInstance
  obtain ⟨r, hr, hrsub⟩ : ∃ r > 0, closedBall z₀ r ⊆ Ω := by
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 hΩ z₀ hz₀
    exact ⟨ε / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hεsub⟩
  set S : Set ℝ := {t | ∃ g, Admissible Ω z₀ g ∧ ‖deriv g z₀‖ = t} with hS
  obtain ⟨f₁, hf₁⟩ := exists_admissible hΩ hne hz₀
  have hSne : S.Nonempty := ⟨_, f₁, hf₁, rfl⟩
  have hSbdd : BddAbove S := ⟨1 / r, by
    rintro t ⟨g, hg, rfl⟩
    exact norm_deriv_le_of_admissible hr hrsub hg⟩
  have hMpos : 0 < sSup S := by
    have h1 : ‖deriv f₁ z₀‖ ≤ sSup S := le_csSup hSbdd ⟨f₁, hf₁, rfl⟩
    have h2 : 0 < ‖deriv f₁ z₀‖ :=
      norm_pos_iff.2 (deriv_ne_zero_of_injOn hΩ hf₁.1 hf₁.2.1 hz₀)
    linarith
  obtain ⟨u, -, hu, huS⟩ := exists_seq_tendsto_sSup hSne hSbdd
  choose F hF hFu using huS
  set l : Ultrafilter ℕ := Ultrafilter.of atTop
  have hl : (l : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨f, hconv⟩ := montel l hΩ (fun n => (hF n).1)
    (fun n z hz => (mem_ball_zero_iff.1 ((hF n).2.2.1 hz)).le)
  have hfd : DifferentiableOn ℂ f Ω :=
    hconv.differentiableOn (Eventually.of_forall fun n => (hF n).1) hΩ
  have hderiv : Tendsto (fun n => deriv (F n) z₀) (l : Filter ℕ) (𝓝 (deriv f z₀)) :=
    (hconv.deriv (Eventually.of_forall fun n => (hF n).1) hΩ).tendsto_at hz₀
  have hnorm : ‖deriv f z₀‖ = sSup S := by
    have h1 : Tendsto (fun n => ‖deriv (F n) z₀‖) (l : Filter ℕ) (𝓝 ‖deriv f z₀‖) :=
      hderiv.norm
    have h2 : Tendsto (fun n => ‖deriv (F n) z₀‖) (l : Filter ℕ) (𝓝 (sSup S)) := by
      simp_rw [hFu]; exact hu.mono_left hl
    exact tendsto_nhds_unique h1 h2
  have hd0 : deriv f z₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hnorm; linarith
  have hfinj : InjOn f Ω :=
    hurwitz_injOn hΩ hUc (fun n => (hF n).1) (fun n => (hF n).2.1) hconv hz₀ hd0
  have hfz₀ : f z₀ = 0 := by
    have h1 : Tendsto (fun n => F n z₀) (l : Filter ℕ) (𝓝 (f z₀)) := hconv.tendsto_at hz₀
    have h2 : Tendsto (fun n => F n z₀) (l : Filter ℕ) (𝓝 0) := by
      simp_rw [(hF _).2.2.2]; exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  have hfle : ∀ z ∈ Ω, ‖f z‖ ≤ 1 := by
    intro z hz
    have h1 : Tendsto (fun n => ‖F n z‖) (l : Filter ℕ) (𝓝 ‖f z‖) :=
      (hconv.tendsto_at hz).norm
    exact le_of_tendsto' h1 fun n => (mem_ball_zero_iff.1 ((hF n).2.2.1 hz)).le
  have hmaps : MapsTo f Ω (ball 0 1) := by
    have hopen : IsOpen (f '' Ω) := isOpen_image_of_injOn hΩ hUc hfd hfinj subset_rfl hΩ
    have hsub : f '' Ω ⊆ closedBall 0 1 := by
      rintro _ ⟨z, hz, rfl⟩; exact mem_closedBall_zero_iff.2 (hfle z hz)
    have := hopen.subset_interior_iff.2 hsub
    rw [interior_closedBall (0 : ℂ) one_ne_zero] at this
    exact fun z hz => this ⟨z, hz, rfl⟩
  refine ⟨f, ⟨hfd, hfinj, hmaps, hfz₀⟩, fun g hg => ?_⟩
  rw [hnorm]
  exact le_csSup hSbdd ⟨g, hg, rfl⟩

/-- The derivative at `0` of `ζ ↦ mob (-w) ((mob (-c) ζ)²)` when `w = -c²`. -/
lemma hasDerivAt_psi {c : ℂ} (hc : ‖c‖ < 1) :
    HasDerivAt (fun ζ => mob (-(-c ^ 2)) (mob (-c) ζ ^ 2))
      (2 * c / (1 + (starRingEnd ℂ) c * c)) 0 := by
  have hc' : ‖-c‖ < 1 := by rwa [norm_neg]
  have hw : ‖-(-c ^ 2)‖ < 1 := by
    rw [neg_neg, norm_pow]; nlinarith [norm_nonneg c]
  have hc2 : ‖c ^ 2‖ < 1 := by rwa [neg_neg] at hw
  have h1 := hasDerivAt_mob hc' (z := 0) (by simp)
  have h2 : HasDerivAt (fun ζ => ζ ^ 2) (2 * mob (-c) 0) (mob (-c) 0) := by
    simpa using hasDerivAt_pow 2 (mob (-c) 0)
  have h3 := hasDerivAt_mob hw (z := mob (-c) 0 ^ 2) (by simpa using hc2)
  have := h3.comp (0 : ℂ) (h2.comp (0 : ℂ) h1)
  convert this using 1
  · funext ζ
    rfl
  simp only [mob_zero, neg_neg, map_neg, map_pow, mul_zero, sub_zero]
  have hden : 1 + (starRingEnd ℂ) c * c ≠ 0 := by
    rw [conj_mul']
    have : (0 : ℝ) ≤ ‖c‖ ^ 2 := by positivity
    intro h
    have h' : ((1 + ‖c‖ ^ 2 : ℝ) : ℂ) = 0 := by push_cast; exact h
    have : (1 + ‖c‖ ^ 2 : ℝ) = 0 := by exact_mod_cast h'
    linarith
  have hden2 : 1 - (starRingEnd ℂ) c * c ≠ 0 := by
    have := mob_denom_ne_zero hc hc
    exact this
  have hden3 : 1 - (starRingEnd ℂ) c ^ 2 * c ^ 2 ≠ 0 := by
    have : 1 - (starRingEnd ℂ) c ^ 2 * c ^ 2 =
        (1 - (starRingEnd ℂ) c * c) * (1 + (starRingEnd ℂ) c * c) := by ring
    rw [this]; exact mul_ne_zero hden2 hden
  have hden4 : 1 - -(starRingEnd ℂ) c ^ 2 * -c ^ 2 ≠ 0 := by
    have : 1 - -(starRingEnd ℂ) c ^ 2 * -c ^ 2 = 1 - (starRingEnd ℂ) c ^ 2 * c ^ 2 := by ring
    rw [this]; exact hden3
  generalize (starRingEnd ℂ) c = d at *
  have hden' : 1 + c * d ≠ 0 := by rwa [mul_comm]
  have hden3' : 1 - c ^ 2 * d ^ 2 ≠ 0 := by rwa [mul_comm]
  have hfac : 1 - c ^ 2 * d ^ 2 = (1 - d * c) * (1 + c * d) := by ring
  field_simp [hden, hden3]
  ring

/-- `|2c / (1 + |c|²)| < 1` for `|c| < 1`. -/
lemma norm_psi_deriv_lt_one {c : ℂ} (hc : ‖c‖ < 1) :
    ‖2 * c / (1 + (starRingEnd ℂ) c * c)‖ < 1 := by
  rw [conj_mul']
  have h1 : (1 + (‖c‖ : ℂ) ^ 2) = ((1 + ‖c‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h1, norm_div, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
    div_lt_one (by positivity)]
  simp only [norm_ofNat]
  nlinarith [sq_nonneg (1 - ‖c‖), norm_nonneg c]

/-- An extremal admissible map is onto the unit disk. -/
lemma surjOn_of_extremal {Ω : Set ℂ} (hΩ : IsOpen Ω) [SimplyConnectedSpace Ω] {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) {f : ℂ → ℂ} (hf : Admissible Ω z₀ f)
    (hmax : ∀ g, Admissible Ω z₀ g → ‖deriv g z₀‖ ≤ ‖deriv f z₀‖) :
    SurjOn f Ω (ball 0 1) := by
  intro w hw
  by_contra hnot
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
  obtain ⟨hfd, hfinj, hfmaps, hfz₀⟩ := hf
  have hfn : ∀ z ∈ Ω, ‖f z‖ < 1 := fun z hz => mem_ball_zero_iff.1 (hfmaps hz)
  -- `h = mob w ∘ f` does not vanish
  set h : ℂ → ℂ := fun z => mob w (f z) with hh
  have hhd : DifferentiableOn ℂ h Ω := fun z hz =>
    (differentiableAt_mob hw1 (hfn z hz)).comp_differentiableWithinAt z (hfd z hz)
  have hh0 : ∀ z ∈ Ω, h z ≠ 0 := by
    intro z hz h0
    rw [hh, mob_eq_zero_iff hw1 (hfn z hz)] at h0
    exact hnot ⟨z, hz, h0⟩
  obtain ⟨s, hsd, hssq⟩ := exists_sqrt_of_simplyConnected hΩ hhd hh0
  have hsn : ∀ z ∈ Ω, ‖s z‖ < 1 := by
    intro z hz
    have h1 : ‖s z‖ ^ 2 < 1 := by
      rw [← norm_pow, hssq z hz]; exact norm_mob_lt_one hw1 (hfn z hz)
    nlinarith [norm_nonneg (s z)]
  have hsinj : InjOn s Ω := by
    intro z hz z' hz' hzz
    have : h z = h z' := by rw [← hssq z hz, ← hssq z' hz', hzz]
    exact hfinj hz hz' (mob_injOn hw1 (mem_ball_zero_iff.2 (hfn z hz))
      (mem_ball_zero_iff.2 (hfn z' hz')) this)
  set c := s z₀ with hc
  have hcn : ‖c‖ < 1 := hsn z₀ hz₀
  have hc2 : c ^ 2 = -w := by
    rw [hc, hssq z₀ hz₀, hh]; simp [hfz₀]
  have hwc : w = -c ^ 2 := by rw [hc2, neg_neg]
  -- the competitor `F = mob c ∘ s`
  set F : ℂ → ℂ := fun z => mob c (s z) with hF
  have hFadm : Admissible Ω z₀ F := by
    refine ⟨fun z hz => (differentiableAt_mob hcn (hsn z hz)).comp_differentiableWithinAt z
      (hsd z hz), ?_, fun z hz => mob_mem_ball (mem_ball_zero_iff.2 hcn)
      (mem_ball_zero_iff.2 (hsn z hz)), by simp [hF, hc]⟩
    intro z hz z' hz' hzz
    exact hsinj hz hz' (mob_injOn hcn (mem_ball_zero_iff.2 (hsn z hz))
      (mem_ball_zero_iff.2 (hsn z' hz')) hzz)
  -- `f = Ψ ∘ F` on `Ω`
  set Ψ : ℂ → ℂ := fun ζ => mob (-(-c ^ 2)) (mob (-c) ζ ^ 2) with hΨ
  have hfΨ : ∀ z ∈ Ω, f z = Ψ (F z) := by
    intro z hz
    simp only [hΨ, hF]
    rw [mob_neg_mob hcn (hsn z hz), hssq z hz, hh, ← hwc, mob_neg_mob hw1 (hfn z hz)]
  have hFd : HasDerivAt F (deriv F z₀) z₀ :=
    (hFadm.1.differentiableAt (hΩ.mem_nhds hz₀)).hasDerivAt
  have hΨd := hasDerivAt_psi hcn
  have hFz₀ : F z₀ = 0 := hFadm.2.2.2
  rw [← hFz₀] at hΨd
  have hcomp : HasDerivAt (Ψ ∘ F) (2 * c / (1 + (starRingEnd ℂ) c * c) * deriv F z₀) z₀ :=
    hΨd.comp z₀ hFd
  have hfeq : f =ᶠ[𝓝 z₀] Ψ ∘ F := by
    filter_upwards [hΩ.mem_nhds hz₀] with z hz using hfΨ z hz
  have hdf : deriv f z₀ = 2 * c / (1 + (starRingEnd ℂ) c * c) * deriv F z₀ := by
    rw [hfeq.deriv_eq, hcomp.deriv]
  have hfd0 : deriv f z₀ ≠ 0 := deriv_ne_zero_of_injOn hΩ hfd hfinj hz₀
  have hFd0 : deriv F z₀ ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hdf; exact hfd0 hdf
  have hlt : ‖deriv f z₀‖ < ‖deriv F z₀‖ := by
    rw [hdf, norm_mul]
    have := norm_psi_deriv_lt_one hcn
    have hpos : 0 < ‖deriv F z₀‖ := norm_pos_iff.2 hFd0
    nlinarith
  have := hmax F hFadm
  linarith

/-- Inverse of a bijective holomorphic map onto the disk. -/
lemma exists_inverse {Ω : Set ℂ} (hΩ : IsOpen Ω) (hUc : IsPreconnected Ω) {f : ℂ → ℂ}
    (hfd : DifferentiableOn ℂ f Ω) (hfinj : InjOn f Ω) (hmaps : MapsTo f Ω (ball 0 1))
    (hsurj : SurjOn f Ω (ball 0 1)) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball 0 1) ∧ InjOn G (ball 0 1) ∧
      G '' ball 0 1 = Ω := by
  classical
  set G := Function.invFunOn f Ω with hG
  have hGmem : ∀ w ∈ ball (0 : ℂ) 1, G w ∈ Ω ∧ f (G w) = w := fun w hw =>
    Function.invFunOn_pos (hsurj hw)
  have hGf : ∀ z ∈ Ω, G (f z) = z := fun z hz =>
    hfinj (hGmem _ (hmaps hz)).1 hz (hGmem _ (hmaps hz)).2
  refine ⟨G, ?_, ?_, ?_⟩
  · intro w hw
    have hwn : ball (0 : ℂ) 1 ∈ 𝓝 w := isOpen_ball.mem_nhds hw
    obtain ⟨hGw, hfGw⟩ := hGmem w hw
    have hcont : ContinuousAt G w := by
      rw [ContinuousAt, (nhds_basis_opens (G w)).tendsto_right_iff]
      rintro V ⟨hV, hVo⟩
      have hopen : IsOpen (f '' (V ∩ Ω)) :=
        isOpen_image_of_injOn hΩ hUc hfd hfinj inter_subset_right (hVo.inter hΩ)
      have hmem : w ∈ f '' (V ∩ Ω) := ⟨G w, ⟨hV, hGw⟩, hfGw⟩
      filter_upwards [hopen.mem_nhds hmem] with y hy
      obtain ⟨z, ⟨hzV, hzΩ⟩, rfl⟩ := hy
      rw [hGf z hzΩ]; exact hzV
    have hfder : HasDerivAt f (deriv f (G w)) (G w) :=
      (hfd.differentiableAt (hΩ.mem_nhds hGw)).hasDerivAt
    have hne := deriv_ne_zero_of_injOn hΩ hfd hfinj hGw
    have hev : ∀ᶠ y in 𝓝 w, f (G y) = y := by
      filter_upwards [hwn] with y hy using (hGmem y hy).2
    exact (hfder.of_local_left_inverse hcont hne hev).differentiableAt.differentiableWithinAt
  · intro w hw w' hw' h
    rw [← (hGmem w hw).2, ← (hGmem w' hw').2, h]
  · ext z
    constructor
    · rintro ⟨w, hw, rfl⟩; exact (hGmem w hw).1
    · intro hz; exact ⟨f z, hmaps hz, hGf z hz⟩

/-- **Riemann mapping theorem.** Every simply connected open subset `Ω ≠ ℂ` of the plane is
the image of the open unit disk under an injective holomorphic map. (Simple connectivity
includes nonemptiness.) -/
theorem riemann_mapping_theorem (Ω : Set ℂ) (hopen : IsOpen Ω) [SimplyConnectedSpace Ω]
    (hne : Ω ≠ univ) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball 0 1) ∧ InjOn G (ball 0 1) ∧
      G '' ball 0 1 = Ω := by
  have hUc : IsPreconnected Ω := isPreconnected_iff_preconnectedSpace.2 inferInstance
  obtain ⟨⟨z₀, hz₀⟩⟩ : Nonempty Ω := inferInstance
  obtain ⟨f, hf, hmax⟩ := exists_extremal hopen hne hz₀
  exact exists_inverse hopen hUc hf.1 hf.2.1 hf.2.2.1 (surjOn_of_extremal hopen hz₀ hf hmax)

end

section

/-! ## Elementary bounds for the Ky Fan partial traces -/

open scoped InnerProductSpace NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma kyFan_le_add_norm (m : ℕ) (A B : E →L[ℂ] E) :
    kyFan m A ≤ kyFan m B + ENNReal.ofReal (m * ‖A - B‖) := by
  refine iSup_le fun n => iSup_le fun hn => iSup_le fun v => iSup_le fun hv => ?_
  refine (diagSum_le_add A B v).trans (add_le_add ?_ ?_)
  · exact le_iSup_of_le n (le_iSup_of_le hn (le_iSup_of_le v (le_iSup_of_le hv le_rfl)))
  · calc ∑ i, ‖⟪v i, (A - B) (v i)⟫_ℂ‖ₑ ≤ ∑ _i : Fin n, ENNReal.ofReal ‖A - B‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← ofReal_norm_eq_enorm]
          refine ENNReal.ofReal_le_ofReal ?_
          calc ‖⟪v i, (A - B) (v i)⟫_ℂ‖ ≤ ‖v i‖ * ‖(A - B) (v i)‖ := norm_inner_le_norm _ _
            _ ≤ ‖v i‖ * (‖A - B‖ * ‖v i‖) := by gcongr; exact (A - B).le_opNorm _
            _ = ‖A - B‖ := by rw [hv.1 i]; ring
      _ = ENNReal.ofReal (n * ‖A - B‖) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (m * ‖A - B‖) := ENNReal.ofReal_le_ofReal (by gcongr)

lemma kyFan_ne_top (m : ℕ) (A : E →L[ℂ] E) : kyFan m A ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (kyFan_le_mul_norm m A)

/-- `A ↦ Φ_m(A)` is `m`-Lipschitz in operator norm. -/
theorem lipschitzWith_kyFan_toReal (m : ℕ) :
    LipschitzWith (m : ℝ≥0) (fun A : E →L[ℂ] E => (kyFan m A).toReal) := by
  refine LipschitzWith.of_le_add_mul _ fun A B => ?_
  have h := kyFan_le_add_norm m A B
  rw [← ENNReal.ofReal_toReal (kyFan_ne_top m B), ← ENNReal.ofReal_add ENNReal.toReal_nonneg
    (by positivity)] at h
  have := ENNReal.toReal_le_of_le_ofReal (by positivity) h
  simpa [dist_eq_norm] using this

/-- For a positive operator, `Σ_{k ∈ J} ⟪u k, A u k⟫ ≤ Φ_{|J|}(A)` for an orthonormal family
`u`. -/
theorem sum_re_inner_le_kyFan {A : E →L[ℂ] E} (hA : ∀ x, 0 ≤ RCLike.re ⟪x, A x⟫_ℂ)
    {ι : Type*} {u : ι → E} (hu : Orthonormal ℂ u) (J : Finset ι) :
    ∑ k ∈ J, RCLike.re ⟪u k, A (u k)⟫_ℂ ≤ (kyFan J.card A).toReal := by
  classical
  set v : Fin J.card → E := fun i => u (J.equivFin.symm i)
  have hv : Orthonormal ℂ v := hu.comp _ (fun a b h =>
    J.equivFin.symm.injective (Subtype.ext h))
  have hsum : ∑ k ∈ J, RCLike.re ⟪u k, A (u k)⟫_ℂ = ∑ i, RCLike.re ⟪v i, A (v i)⟫_ℂ := by
    rw [← Finset.sum_coe_sort J]
    exact (Equiv.sum_comp J.equivFin.symm (fun k : J => RCLike.re ⟪u k, A (u k)⟫_ℂ)).symm
  have hdiag : diagSum A v = ENNReal.ofReal (∑ i, RCLike.re ⟪v i, A (v i)⟫_ℂ) := by
    unfold diagSum
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hA _)]
  have hle : diagSum A v ≤ kyFan J.card A :=
    le_iSup_of_le J.card (le_iSup_of_le le_rfl (le_iSup_of_le v (le_iSup_of_le hv le_rfl)))
  rw [hsum]
  rw [hdiag] at hle
  have := ENNReal.toReal_mono (kyFan_ne_top _ _) hle
  rwa [ENNReal.toReal_ofReal (Finset.sum_nonneg fun i _ => hA _)] at this

end

section

/-! ## Elementary operator bounds for positive trace-class operators -/

open scoped InnerProductSpace ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Cauchy–Schwarz inequality for a positive operator. -/
theorem norm_inner_sq_le_of_isPositive [CompleteSpace E] {A : E →L[ℂ] E} (hA : A.IsPositive) (x y : E) :
    ‖⟪x, A y⟫_ℂ‖ ^ 2 ≤ RCLike.re ⟪x, A x⟫_ℂ * RCLike.re ⟪y, A y⟫_ℂ := by
  set w := ⟪x, A y⟫_ℂ with hwdef
  set d := ⟪y, A y⟫_ℂ with hd
  have hsym : ⟪y, A x⟫_ℂ = conj w := by
    have := hA.isSelfAdjoint.isSymmetric y x
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [← this, hwdef, inner_conj_symm]
  have hN : w * conj w = (‖w‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hq : ∀ s : ℝ, 0 ≤ (‖w‖ ^ 2 * RCLike.re d) * (s * s) + (2 * ‖w‖ ^ 2) * s +
      RCLike.re ⟪x, A x⟫_ℂ := by
    intro s
    have h := hA.re_inner_nonneg_right (x + ((s : ℂ) * conj w) • y)
    simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, hsym] at h
    have hE : conj ((s : ℂ) * conj w) * conj w +
        (s : ℂ) * conj w * (w + conj ((s : ℂ) * conj w) * d)
        = ((2 * s * ‖w‖ ^ 2 : ℝ) : ℂ) + ((s ^ 2 * ‖w‖ ^ 2 : ℝ) : ℂ) * d := by
      simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
      push_cast
      linear_combination (2 * (s : ℂ) + (s : ℂ) ^ 2 * d) * hN
    have h2 : RCLike.re (conj ((s : ℂ) * conj w) * conj w) +
        RCLike.re ((s : ℂ) * conj w * (w + conj ((s : ℂ) * conj w) * d)) =
        2 * s * ‖w‖ ^ 2 + s ^ 2 * ‖w‖ ^ 2 * RCLike.re d := by
      rw [← map_add, hE]
      simp only [RCLike.re_to_complex, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
    have : 0 ≤ RCLike.re ⟪x, A x⟫_ℂ + (2 * s * ‖w‖ ^ 2 + s ^ 2 * ‖w‖ ^ 2 * RCLike.re d) := by
      rw [← h2, ← add_assoc]; exact h
    nlinarith
  have hdisc := discrim_le_zero hq
  unfold discrim at hdisc
  by_cases hw : w = 0
  · rw [hw, norm_zero]
    simpa using mul_nonneg (hA.re_inner_nonneg_right x) (hA.re_inner_nonneg_right y)
  have hwn : (0 : ℝ) < ‖w‖ ^ 2 := by positivity
  have : ‖w‖ ^ 2 * ‖w‖ ^ 2 ≤ ‖w‖ ^ 2 * (RCLike.re ⟪x, A x⟫_ℂ * RCLike.re d) := by nlinarith
  exact le_of_mul_le_mul_left this hwn

lemma orthonormal_single {w : E} (hw : ‖w‖ = 1) : Orthonormal ℂ (fun _ : Fin 1 => w) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp [Subsingleton.elim i j, inner_self_eq_norm_sq_to_K, hw]

lemma enorm_inner_le_traceNorm (T : E →L[ℂ] E) {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖⟪u, T v⟫_ℂ‖ₑ ≤ traceNorm T := by
  refine le_trans ?_ (le_iSup_of_le 1 (le_iSup_of_le (fun _ => u) (le_iSup_of_le (fun _ => v)
    (le_iSup_of_le (orthonormal_single hu) (le_iSup_of_le (orthonormal_single hv) le_rfl)))))
  simp

lemma norm_real_inv_norm_smul {x : E} (hx : x ≠ 0) : ‖((‖x‖⁻¹ : ℝ) : ℂ) • x‖ = 1 := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]

/-- The operator norm is bounded by the trace norm. -/
theorem ofReal_norm_le_traceNorm (T : E →L[ℂ] E) : ENNReal.ofReal ‖T‖ ≤ traceNorm T := by
  by_cases htop : traceNorm T = ⊤
  · simp [htop]
  rw [← ENNReal.ofReal_toReal htop]
  refine ENNReal.ofReal_le_ofReal (T.opNorm_le_bound ENNReal.toReal_nonneg fun v => ?_)
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  set v' := ((‖v‖⁻¹ : ℝ) : ℂ) • v with hv'def
  have hv' : ‖v'‖ = 1 := norm_real_inv_norm_smul hv
  have key : ‖T v'‖ ≤ (traceNorm T).toReal := by
    rcases eq_or_ne (T v') 0 with h | h
    · rw [h, norm_zero]; exact ENNReal.toReal_nonneg
    have hu := norm_real_inv_norm_smul h
    have h1 := enorm_inner_le_traceNorm T hu hv'
    have h2 : ‖⟪((‖T v'‖⁻¹ : ℝ) : ℂ) • T v', T v'⟫_ℂ‖ = ‖T v'‖ := by
      rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
      simp
      field_simp
    rw [← ofReal_norm_eq_enorm, h2] at h1
    exact (ENNReal.ofReal_le_iff_le_toReal htop).1 h1
  have hTv : T v = ((‖v‖ : ℝ) : ℂ) • T v' := by
    rw [hv'def, map_smul, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hv),
      Complex.ofReal_one, one_smul]
  rw [hTv, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_norm, mul_comm]
  exact mul_le_mul_of_nonneg_right key (norm_nonneg _)

/-- A positive trace-class operator has small quadratic form off a suitable finite orthonormal
family. -/
theorem exists_orthonormal_tail_le {A : E →L[ℂ] E} (hA : IsPosTraceClass A) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (N : ℕ) (v : Fin N → E), Orthonormal ℂ v ∧
      ∀ y, (∀ i, ⟪v i, y⟫_ℂ = 0) → RCLike.re ⟪y, A y⟫_ℂ ≤ ε * ‖y‖ ^ 2 := by
  have hfam : ∃ (N : ℕ) (v : Fin N → E), Orthonormal ℂ v ∧
      posTrace A < diagSum A v + ENNReal.ofReal ε := by
    by_cases h0 : posTrace A = 0
    · exact ⟨0, Fin.elim0, by simp [Orthonormal], by simp [h0, diagSum, hε]⟩
    have hlt : posTrace A - ENNReal.ofReal ε < posTrace A :=
      ENNReal.sub_lt_self hA.2.ne h0 (by simp [hε])
    obtain ⟨N, hN⟩ := lt_iSup_iff.1 hlt
    obtain ⟨v, hv⟩ := lt_iSup_iff.1 hN
    obtain ⟨hvo, hv'⟩ := lt_iSup_iff.1 hv
    refine ⟨N, v, hvo, ?_⟩
    have := ENNReal.lt_add_of_sub_lt_right (Or.inl hA.2.ne) hv'
    exact this
  obtain ⟨N, v, hvo, hv⟩ := hfam
  refine ⟨N, v, hvo, fun y hy => ?_⟩
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  set y' := ((‖y‖⁻¹ : ℝ) : ℂ) • y with hy'def
  have hy' : ‖y'‖ = 1 := norm_real_inv_norm_smul hy0
  have hy'v : ∀ i, ⟪v i, y'⟫_ℂ = 0 := fun i => by rw [hy'def, inner_smul_right, hy i, mul_zero]
  have hon := orthonormal_cons hvo hy' hy'v
  have hle : diagSum A v + ENNReal.ofReal (RCLike.re ⟪y', A y'⟫_ℂ) ≤ posTrace A := by
    refine le_trans ?_ (le_iSup_of_le (N + 1) (le_iSup_of_le _ (le_iSup_of_le hon le_rfl)))
    unfold diagSum
    rw [Fin.sum_univ_succ, add_comm]
    simp
  have hlt : ENNReal.ofReal (RCLike.re ⟪y', A y'⟫_ℂ) < ENNReal.ofReal ε := by
    have h1 := hle.trans_lt hv
    have hd : diagSum A v ≠ ⊤ := by
      unfold diagSum; exact ENNReal.sum_ne_top.2 fun i _ => ENNReal.ofReal_ne_top
    exact (ENNReal.add_lt_add_iff_left hd).1 h1
  have h2 : RCLike.re ⟪y', A y'⟫_ℂ < ε := by
    by_contra hc; push_neg at hc
    exact absurd hlt (not_lt.2 (ENNReal.ofReal_le_ofReal hc))
  have hscale : RCLike.re ⟪y, A y⟫_ℂ = ‖y‖ ^ 2 * RCLike.re ⟪y', A y'⟫_ℂ := by
    have hyy : y = ((‖y‖ : ℝ) : ℂ) • y' := by
      rw [hy'def, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hy0),
        Complex.ofReal_one, one_smul]
    conv_lhs => rw [hyy]
    rw [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc,
      ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.re_ofReal_mul, ← pow_two]
    rfl
  rw [hscale, mul_comm ε]
  exact mul_le_mul_of_nonneg_left h2.le (by positivity)

lemma le_sqrt_of_pow_four_le {a c : ℝ} (ha : 0 ≤ a) (h : a ^ 4 ≤ a ^ 2 * c) :
    a ≤ Real.sqrt c := by
  rcases ha.lt_or_eq with ha | rfl
  · have h2 : a ^ 2 ≤ c := by
      have : a ^ 2 * a ^ 2 ≤ a ^ 2 * c := by nlinarith
      exact le_of_mul_le_mul_left this (by positivity)
    calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha.le).symm
      _ ≤ Real.sqrt c := Real.sqrt_le_sqrt h2
  · exact Real.sqrt_nonneg _

lemma re_inner_le_norm_mul_sq (A : E →L[ℂ] E) (x : E) :
    RCLike.re ⟪x, A x⟫_ℂ ≤ ‖A‖ * ‖x‖ ^ 2 :=
  calc RCLike.re ⟪x, A x⟫_ℂ ≤ ‖⟪x, A x⟫_ℂ‖ := RCLike.re_le_norm _
    _ ≤ ‖x‖ * ‖A x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖A‖ * ‖x‖) := by gcongr; exact A.le_opNorm x
    _ = ‖A‖ * ‖x‖ ^ 2 := by ring

/-- **Compression estimate.** If `⟪y, A y⟫ ≤ ε ‖y‖²` on `K^⊥`, then
`‖A - P A P‖ ≤ 2 √(ε ‖A‖)` for the orthogonal projection `P` onto `K`. -/
theorem norm_sub_compress_le [CompleteSpace E] {A : E →L[ℂ] E} (hA : A.IsPositive)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] {ε : ℝ} (hε : 0 ≤ ε)
    (htail : ∀ y ∈ Kᗮ, RCLike.re ⟪y, A y⟫_ℂ ≤ ε * ‖y‖ ^ 2) :
    ‖A - K.starProjection * A * K.starProjection‖ ≤ 2 * Real.sqrt (ε * ‖A‖) := by
  set P := K.starProjection with hP
  set s := Real.sqrt (ε * ‖A‖) with hs
  have hsx : ∀ x : E, Real.sqrt (ε * ‖A‖ * ‖x‖ ^ 2) = s * ‖x‖ := fun x => by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  have hs1 : ∀ x, ‖A x - P (A x)‖ ≤ s * ‖x‖ := by
    intro x
    set w := A x - P (A x) with hw
    have hwK : w ∈ Kᗮ := K.sub_starProjection_mem_orthogonal _
    have hww : ⟪w, w⟫_ℂ = ⟪w, A x⟫_ℂ := by
      conv_lhs => rw [hw]
      rw [inner_sub_right, Submodule.inner_left_of_mem_orthogonal (K.starProjection_apply_mem _) hwK,
        sub_zero]
    have h1 := norm_inner_sq_le_of_isPositive hA w x
    rw [← hww, inner_self_eq_norm_sq_to_K] at h1
    replace h1 : ‖w‖ ^ 4 ≤ RCLike.re ⟪w, A w⟫_ℂ * RCLike.re ⟪x, A x⟫_ℂ := by
      convert h1 using 1; simp [norm_pow]; ring
    rw [← hsx]
    refine le_sqrt_of_pow_four_le (norm_nonneg _) (h1.trans ?_)
    calc RCLike.re ⟪w, A w⟫_ℂ * RCLike.re ⟪x, A x⟫_ℂ ≤ (ε * ‖w‖ ^ 2) * (‖A‖ * ‖x‖ ^ 2) :=
          mul_le_mul (htail w hwK) (re_inner_le_norm_mul_sq A x)
            (hA.re_inner_nonneg_right x) (by positivity)
      _ = ‖w‖ ^ 2 * (ε * ‖A‖ * ‖x‖ ^ 2) := by ring
  have hs2 : ∀ u ∈ Kᗮ, ‖A u‖ ≤ s * ‖u‖ := by
    intro u hu
    have h1 := norm_inner_sq_le_of_isPositive hA (A u) u
    rw [inner_self_eq_norm_sq_to_K] at h1
    replace h1 : ‖A u‖ ^ 4 ≤ RCLike.re ⟪A u, A (A u)⟫_ℂ * RCLike.re ⟪u, A u⟫_ℂ := by
      convert h1 using 1; simp [norm_pow]; ring
    rw [← hsx]
    refine le_sqrt_of_pow_four_le (norm_nonneg _) (h1.trans ?_)
    calc RCLike.re ⟪A u, A (A u)⟫_ℂ * RCLike.re ⟪u, A u⟫_ℂ ≤
          (‖A‖ * ‖A u‖ ^ 2) * (ε * ‖u‖ ^ 2) :=
          mul_le_mul (re_inner_le_norm_mul_sq A (A u)) (htail u hu)
            (hA.re_inner_nonneg_right u) (by positivity)
      _ = ‖A u‖ ^ 2 * (ε * ‖A‖ * ‖u‖ ^ 2) := by ring
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  have hdecomp : (A - P * A * P) x = (A x - P (A x)) + P (A (x - P x)) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, map_sub]
    abel
  rw [hdecomp]
  have hu : x - P x ∈ Kᗮ := K.sub_starProjection_mem_orthogonal _
  have hux : ‖x - P x‖ ≤ ‖x‖ := by
    have := K.starProjection_orthogonal ▸ Submodule.norm_starProjection_apply_le Kᗮ x
    simpa using this
  calc ‖(A x - P (A x)) + P (A (x - P x))‖ ≤ ‖A x - P (A x)‖ + ‖P (A (x - P x))‖ :=
        norm_add_le _ _
    _ ≤ s * ‖x‖ + ‖A (x - P x)‖ := add_le_add (hs1 x) (K.norm_starProjection_apply_le _)
    _ ≤ s * ‖x‖ + s * ‖x - P x‖ := by gcongr; exact hs2 _ hu
    _ ≤ s * ‖x‖ + s * ‖x‖ := by gcongr
    _ = 2 * s * ‖x‖ := by ring

end

section

/-! ## Uniform finite-dimensional compression of a continuous family of trace-class operators -/

open scoped InnerProductSpace
open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma exists_tail_subspace {A : E →L[ℂ] E} (hA : IsPosTraceClass A) {ε : ℝ} (hε : 0 < ε) :
    ∃ W : Submodule ℂ E, FiniteDimensional ℂ W ∧
      ∀ y ∈ Wᗮ, RCLike.re ⟪y, A y⟫_ℂ ≤ ε * ‖y‖ ^ 2 := by
  obtain ⟨N, v, -, hv⟩ := exists_orthonormal_tail_le hA hε
  refine ⟨Submodule.span ℂ (Set.range v), FiniteDimensional.span_of_finite ℂ (Set.finite_range v),
    fun y hy => hv y fun i => ?_⟩
  exact Submodule.inner_right_of_mem_orthogonal
    (Submodule.subset_span (Set.mem_range_self i)) hy

/-- **Uniform tail subspace.** -/
theorem exists_uniform_tail_subspace {L : ℝ → E →L[ℂ] E} {b : ℝ}
    (hLc : ContinuousOn L (Icc 0 b)) (hLp : ∀ t ∈ Icc 0 b, IsPosTraceClass (L t))
    (X₀ : Submodule ℂ E) [FiniteDimensional ℂ X₀] {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Submodule ℂ E, FiniteDimensional ℂ K ∧ X₀ ≤ K ∧
      ∀ t ∈ Icc 0 b, ∀ y ∈ Kᗮ, RCLike.re ⟪y, L t y⟫_ℂ ≤ ε * ‖y‖ ^ 2 := by
  classical
  obtain ⟨δ, hδ, hunif⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hLc) (ε / 2) (half_pos hε)
  obtain ⟨T, hTsub, hTfin, hcover⟩ := finite_cover_balls_of_compact (isCompact_Icc (a := 0) (b := b)) hδ
  have hW : ∀ τ, ∃ W : Submodule ℂ E, FiniteDimensional ℂ W ∧
      (τ ∈ Icc 0 b → ∀ y ∈ Wᗮ, RCLike.re ⟪y, L τ y⟫_ℂ ≤ ε / 2 * ‖y‖ ^ 2) := by
    intro τ
    by_cases hτ : τ ∈ Icc 0 b
    · obtain ⟨W, hW1, hW2⟩ := exists_tail_subspace (hLp τ hτ) (half_pos hε)
      exact ⟨W, hW1, fun _ => hW2⟩
    · exact ⟨⊥, inferInstance, fun h => absurd h hτ⟩
  choose W hWfin hWtail using hW
  set K : Submodule ℂ E := X₀ ⊔ hTfin.toFinset.sup W with hK
  haveI : ∀ τ, FiniteDimensional ℂ (W τ) := hWfin
  have hKfin : FiniteDimensional ℂ K := by
    rw [hK]; infer_instance
  refine ⟨K, hKfin, le_sup_left, fun t ht y hy => ?_⟩
  obtain ⟨τ, hτT, htτ⟩ := mem_iUnion₂.1 (hcover ht)
  have hτ : τ ∈ Icc 0 b := hTsub hτT
  have hWK : W τ ≤ K :=
    le_sup_of_le_right (Finset.le_sup (f := W) (hTfin.mem_toFinset.2 hτT))
  have hyW : y ∈ (W τ)ᗮ := Submodule.orthogonal_le hWK hy
  have h1 := hWtail τ hτ y hyW
  have h2 : ‖L t - L τ‖ < ε / 2 := by
    have := hunif t ht τ hτ (by rwa [mem_ball] at htτ)
    rwa [dist_eq_norm] at this
  have h3 : RCLike.re ⟪y, (L t - L τ) y⟫_ℂ ≤ ‖L t - L τ‖ * ‖y‖ ^ 2 :=
    re_inner_le_norm_mul_sq _ _
  have h4 : RCLike.re ⟪y, L t y⟫_ℂ = RCLike.re ⟪y, L τ y⟫_ℂ + RCLike.re ⟪y, (L t - L τ) y⟫_ℂ := by
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, map_sub]; ring
  rw [h4]
  have : ‖L t - L τ‖ * ‖y‖ ^ 2 ≤ ε / 2 * ‖y‖ ^ 2 := by gcongr
  linarith

end

section

/-! ## Finite-dimensional approximation of a positive unitary path -/

open scoped InnerProductSpace
open Set Metric Filter Topology Complex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Shortcut instance: real scalar multiplication on operators on a submodule is continuous
(instance search does not find it on its own, due to two `ℝ`-module structures on `K`). -/
instance continuousSMul_real_submodule_clm (K : Submodule ℂ E) :
    ContinuousSMul ℝ (K →L[ℂ] K) := ⟨by
  have : (fun p : ℝ × (K →L[ℂ] K) => p.1 • p.2) = fun p => ((p.1 : ℂ)) • p.2 := by
    ext p x; simp [Complex.coe_smul]
  rw [this]; fun_prop⟩

section Compress

variable (K : Submodule ℂ E) [FiniteDimensional ℂ K]

/-- The compression `π A ι` of an operator to a finite-dimensional subspace. -/
def compress (A : E →L[ℂ] E) : K →L[ℂ] K :=
  K.orthogonalProjection ∘L A ∘L K.subtypeL

lemma inner_compress (A : E →L[ℂ] E) (y z : K) :
    ⟪y, compress K A z⟫_ℂ = ⟪(y : E), A z⟫_ℂ := by
  simp only [compress, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  rw [← ContinuousLinearMap.adjoint_inner_left, Submodule.adjoint_orthogonalProjection,
    Submodule.subtypeL_apply]

lemma compress_isSelfAdjoint {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (compress K A) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hA ⊢
  intro y z
  simp only [ContinuousLinearMap.coe_coe]
  rw [← inner_conj_symm, inner_compress, inner_compress, ← inner_conj_symm (z : E)]
  have := hA (y : E) (z : E)
  simp only [ContinuousLinearMap.coe_coe] at this
  rw [← this]
  exact Complex.conj_conj _

omit [CompleteSpace E] in
lemma continuous_compress : Continuous (compress K) := by
  have : compress K = fun A => K.orthogonalProjection ∘L A ∘L K.subtypeL := rfl
  rw [this]
  fun_prop

end Compress

lemma norm_le_one_of_mem_unitary {W : E →L[ℂ] E} (hW : W ∈ unitary (E →L[ℂ] E)) : ‖W‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  have h : ‖W x‖ ^ 2 = ‖x‖ ^ 2 := by
    have h1 : ⟪W x, W x⟫_ℂ = ⟪x, x⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
        ← ContinuousLinearMap.mul_apply, Unitary.star_mul_self_of_mem hW,
        ContinuousLinearMap.one_apply]
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
    exact_mod_cast h1
  rw [one_mul]
  exact ((pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h).le

omit [CompleteSpace E] in
lemma norm_starProjection_le (K : Submodule ℂ E) [K.HasOrthogonalProjection] :
    ‖K.starProjection‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]; exact K.norm_starProjection_apply_le x

/-- The path `V' = i V A`, `V(0) = 1`, for a continuous self-adjoint family `A`. -/
theorem exists_unitary_path {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] {A : ℝ → F →L[ℂ] F} {b : ℝ} (hb : 0 ≤ b) (hAc : ContinuousOn A (Icc 0 b))
    (hAs : ∀ t ∈ Icc 0 b, IsSelfAdjoint (A t)) :
    ∃ V : ℝ → F →L[ℂ] F, V 0 = 1 ∧ (∀ t ∈ Icc 0 b, V t ∈ unitary (F →L[ℂ] F)) ∧
      ∀ t ∈ Icc 0 b, HasDerivWithinAt V (I • (V t * A t)) (Icc 0 b) t := by
  set C : ℝ → F →L[ℂ] F := fun t => (-I) • A t with hCdef
  have hCc : ContinuousOn C (Icc 0 b) := by
    rw [hCdef]
    convert (hAc.const_smul (Complex.I)).neg using 1
    funext t
    simp
  obtain ⟨W, hW0, hW⟩ := exists_linear_ode_Icc hb hCc
  have hWd : ∀ t ∈ Icc 0 b, HasDerivWithinAt W (C t * W t) (Icc 0 b) t :=
    fun t ht => (hW t ht).hasDerivWithinAt
  have hskew : ∀ t ∈ Icc 0 b, star (C t) = -C t := by
    intro t ht
    have := (hAs t ht).star_eq
    simp [C, this]
  have hWu := unitary_of_linear_ode_Icc hCc hskew hW0 hWd
  refine ⟨fun t => star (W t), by simp [hW0], fun t ht => Unitary.star_mem (hWu t ht),
    fun t ht => ?_⟩
  have := (hWd t ht).star
  convert this using 1
  rw [star_mul, hskew t ht]
  simp only [C, neg_smul, neg_neg, mul_smul_comm]

/-- Composition of a real derivative with a complex-linear map. -/
lemma HasDerivWithinAt.complexCLM_comp {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] {V : ℝ → F} {V' : F} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt V V' s t) (Φ : F →L[ℂ] G) :
    HasDerivWithinAt (fun x => Φ (V x)) (Φ V') s t :=
  (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t h

set_option maxHeartbeats 1000000 in
/-- **Finite-dimensional approximation.** -/
theorem exists_finite_approx_path {U L : ℝ → E →L[ℂ] E} {b : ℝ} (hb : 0 ≤ b) (hU0 : U 0 = 1)
    (hUu : ∀ t ∈ Icc 0 b, U t ∈ unitary (E →L[ℂ] E))
    (hUd : ∀ t ∈ Icc 0 b, HasDerivWithinAt U (I • (U t * L t)) (Icc 0 b) t)
    (hLc : ContinuousOn L (Icc 0 b)) (hLp : ∀ t ∈ Icc 0 b, IsPosTraceClass (L t))
    (X₀ : Submodule ℂ E) [FiniteDimensional ℂ X₀] {ε : ℝ} (hε : 0 < ε) :
    ∃ (K : Submodule ℂ E) (_ : FiniteDimensional ℂ K) (V : ℝ → K →L[ℂ] K), X₀ ≤ K ∧ V 0 = 1 ∧
      (∀ t ∈ Icc 0 b, V t ∈ unitary (K →L[ℂ] K)) ∧
      (∀ t ∈ Icc 0 b, HasDerivWithinAt V (I • (V t * compress K (L t))) (Icc 0 b) t) ∧
      ∀ t ∈ Icc 0 b,
        ‖K.subtypeL ∘L V t ∘L K.orthogonalProjection + (1 - K.starProjection) - U t‖ ≤ ε := by
  obtain ⟨Λ₀, hΛ₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hLc
  set Λ : ℝ := max Λ₀ 0 + 1 with hΛ
  have hΛpos : 0 < Λ := by positivity
  have hLΛ : ∀ t ∈ Icc 0 b, ‖L t‖ ≤ Λ := fun t ht =>
    (hΛ₀ t ht).trans (by linarith [le_max_left Λ₀ 0])
  set C₀ : ℝ := (Real.exp (Λ * b) - 1) / Λ with hC₀
  have hC₀nn : 0 ≤ C₀ := by
    refine div_nonneg ?_ hΛpos.le
    have := Real.add_one_le_exp (Λ * b)
    nlinarith [mul_nonneg hΛpos.le hb]
  set η : ℝ := ε / (C₀ + 1) with hη
  have hηpos : 0 < η := by positivity
  set ε' : ℝ := η ^ 2 / (4 * Λ) with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨K, hKfin, hXK, htail⟩ := exists_uniform_tail_subspace hLc hLp X₀ hε'pos
  haveI := hKfin
  obtain ⟨V, hV0, hVu, hVd⟩ := exists_unitary_path (A := fun t => compress K (L t)) hb
    ((continuous_compress K).comp_continuousOn hLc)
    (fun t ht => compress_isSelfAdjoint K (hLp t ht).1.isSelfAdjoint)
  refine ⟨K, hKfin, V, hXK, hV0, hVu, hVd, ?_⟩
  set P := K.starProjection with hP
  set M : ℝ → E →L[ℂ] E := fun t => P * L t * P with hM
  have hML : ∀ t ∈ Icc 0 b, ‖M t - L t‖ ≤ η := by
    intro t ht
    have h1 := norm_sub_compress_le (hLp t ht).1 K hε'pos.le (htail t ht)
    rw [norm_sub_rev]
    refine h1.trans ?_
    calc 2 * Real.sqrt (ε' * ‖L t‖) ≤ 2 * Real.sqrt (ε' * Λ) := by
          gcongr; exact hLΛ t ht
      _ = η := by
        rw [hε', show η ^ 2 / (4 * Λ) * Λ = (η / 2) ^ 2 by field_simp; ring,
          Real.sqrt_sq (by positivity)]
        ring
  have hMn : ∀ t ∈ Icc 0 b, ‖M t‖ ≤ Λ := by
    intro t ht
    calc ‖M t‖ ≤ ‖P‖ * ‖L t‖ * ‖P‖ :=
          (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
      _ ≤ 1 * Λ * 1 := by
          gcongr
          · exact norm_starProjection_le K
          · exact hLΛ t ht
          · exact norm_starProjection_le K
      _ = Λ := by ring
  set Φ : (K →L[ℂ] K) →L[ℂ] (E →L[ℂ] E) :=
    (ContinuousLinearMap.compL ℂ E K E K.subtypeL).comp
      ((ContinuousLinearMap.compL ℂ E K K).flip K.orthogonalProjection) with hΦ
  have hΦapp : ∀ X, Φ X = K.subtypeL ∘L X ∘L K.orthogonalProjection := fun X => rfl
  set Ũ : ℝ → E →L[ℂ] E :=
    fun t => K.subtypeL ∘L V t ∘L K.orthogonalProjection + (1 - P) with hŨ
  set h : ℝ → E →L[ℂ] E := fun t => Ũ t - U t with hh
  have hkey : ∀ t, Φ (V t * compress K (L t)) = Ũ t * M t := by
    intro t
    ext x
    simp only [hΦapp, Ũ, M, P, compress, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, Submodule.starProjection_apply,
      Submodule.orthogonalProjection_mem_subspace_eq_self, Submodule.subtypeL_apply, sub_self,
      add_zero]
  have hhd : ∀ t ∈ Icc 0 b,
      HasDerivWithinAt h (I • (h t * M t + U t * (M t - L t))) (Icc 0 b) t := by
    intro t ht
    have h1 : HasDerivWithinAt (fun s => Φ (V s)) (Φ (I • (V t * compress K (L t))))
        (Icc 0 b) t :=
      HasDerivWithinAt.complexCLM_comp (hVd t ht) Φ
    have h2 := (h1.add_const (1 - P)).sub (hUd t ht)
    change HasDerivWithinAt ((fun s => Φ (V s) + (1 - P)) - U) _ (Icc 0 b) t
    convert h2 using 1
    rw [map_smul, hkey, ← smul_sub]
    congr 1
    simp only [h]
    noncomm_ring
  have hcont : ContinuousOn h (Icc 0 b) := fun t ht => (hhd t ht).continuousWithinAt
  have hderiv : ∀ x ∈ Ico 0 b,
      HasDerivWithinAt h (I • (h x * M x + U x * (M x - L x))) (Ici x) x := fun x hx =>
    (hhd x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE hx.2) (Icc_subset_Icc_left hx.1))
  have h0 : ‖h 0‖ ≤ 0 := by
    have : h 0 = 0 := by
      simp only [h, Ũ, hV0, hU0]
      ext x
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply,
        Submodule.subtypeL_apply, ContinuousLinearMap.zero_apply, P]
      rw [Submodule.starProjection_apply]
      abel
    rw [this, norm_zero]
  have hbound : ∀ x ∈ Ico 0 b, ‖I • (h x * M x + U x * (M x - L x))‖ ≤ Λ * ‖h x‖ + η := by
    intro x hx
    have hx' := Ico_subset_Icc_self hx
    rw [norm_smul, Complex.norm_I, one_mul]
    calc ‖h x * M x + U x * (M x - L x)‖ ≤ ‖h x‖ * ‖M x‖ + ‖U x‖ * ‖M x - L x‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ ‖h x‖ * Λ + 1 * η := by
          gcongr
          · exact hMn x hx'
          · exact norm_le_one_of_mem_unitary (hUu x hx')
          · exact hML x hx'
      _ = Λ * ‖h x‖ + η := by ring
  intro t ht
  have := norm_le_gronwallBound_of_norm_deriv_right_le hcont hderiv h0 hbound t ht
  rw [gronwallBound_of_K_ne_0 hΛpos.ne', sub_zero] at this
  simp only [zero_mul, zero_add] at this
  show ‖h t‖ ≤ ε
  calc ‖h t‖ ≤ η / Λ * (Real.exp (Λ * t) - 1) := this
    _ ≤ η / Λ * (Real.exp (Λ * b) - 1) := by gcongr; exact ht.2
    _ = η * C₀ := by rw [hC₀]; ring
    _ ≤ ε := by
        rw [hη, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith

end

section

/-! ## Local spectral gaps near a crossing -/

open scoped InnerProductSpace ComplexConjugate
open Set Metric Filter Topology Complex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Pythagoras for an orthogonal pair `a ∈ K`, `b ∈ Kᗮ`. -/
lemma norm_add_sq_of_mem_orthogonal {K : Submodule ℂ E} {a b : E} (ha : a ∈ K)
    (hb : b ∈ Kᗮ) : ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have h : ⟪a, b⟫_ℂ = 0 := (Submodule.mem_orthogonal' K b).1 hb a ha |> fun h => by
    rw [← inner_conj_symm, h, map_zero]
  have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero a b h
  nlinarith [this]

/-- For a unitary `U` with `U k = e k`, `U* k = conj e • k`. -/
lemma star_apply_of_eigen {U : E →L[ℂ] E} (hU : U ∈ unitary (E →L[ℂ] E)) {e : ℂ}
    (he : ‖e‖ = 1) {k : E} (hk : U k = e • k) : star U k = conj e • k := by
  have h1 : star U (U k) = k := by
    rw [← ContinuousLinearMap.mul_apply, Unitary.star_mul_self_of_mem hU,
      ContinuousLinearMap.one_apply]
  rw [hk, map_smul] at h1
  have hce : conj e * e = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, he]; simp
  calc star U k = (conj e * e) • star U k := by rw [hce, one_smul]
    _ = conj e • k := by rw [mul_smul, h1]

/-- A unitary operator maps the orthogonal complement of an eigenspace into itself. -/
lemma mem_orthogonal_of_eigen {U : E →L[ℂ] E} (hU : U ∈ unitary (E →L[ℂ] E)) {e : ℂ}
    (he : ‖e‖ = 1) {K : Submodule ℂ E} (heig : ∀ k ∈ K, U k = e • k) {x : E} (hx : x ∈ Kᗮ) :
    U x ∈ Kᗮ := by
  rw [Submodule.mem_orthogonal]
  intro k hk
  rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
    star_apply_of_eigen hU he (heig k hk), inner_smul_left,
    (Submodule.mem_orthogonal K x).1 hx k hk, mul_zero]

/-- Zeroth-order decomposition: for `x₀ ∈ K`, `x₁ ∈ Kᗮ`,
`‖(U - z)(x₀ + x₁)‖² = ‖e - z‖² ‖x₀‖² + ‖(U - z) x₁‖²`. -/
lemma norm_sub_smul_apply_sq {U : E →L[ℂ] E} (hU : U ∈ unitary (E →L[ℂ] E)) {e : ℂ}
    (he : ‖e‖ = 1) {K : Submodule ℂ E} (heig : ∀ k ∈ K, U k = e • k) (z : ℂ) {x₀ x₁ : E}
    (h₀ : x₀ ∈ K) (h₁ : x₁ ∈ Kᗮ) :
    ‖(U - z • 1) (x₀ + x₁)‖ ^ 2 = ‖e - z‖ ^ 2 * ‖x₀‖ ^ 2 + ‖(U - z • 1) x₁‖ ^ 2 := by
  have hsplit : (U - z • 1) (x₀ + x₁) = (e - z) • x₀ + (U - z • 1) x₁ := by
    rw [map_add]
    congr 1
    simp [heig x₀ h₀, sub_smul]
  have ha : (e - z) • x₀ ∈ K := K.smul_mem _ h₀
  have hb : (U - z • 1) x₁ ∈ Kᗮ := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply]
    exact Kᗮ.sub_mem (mem_orthogonal_of_eigen hU he heig h₁) (Kᗮ.smul_mem _ h₁)
  rw [hsplit, norm_add_sq_of_mem_orthogonal ha hb, norm_smul, mul_pow]

/-- First-order estimate near a crossing. If `W = U₀ + σ h i U₀ L₀ + R` with `‖R‖ ≤ h ρ`,
`U₀ = e` on `K`, `L₀ ≥ λ` on `K`, and `z = e u` with `σ Im u ≤ 0`, then for `x₀ ∈ K`, `x₁ ∈ Kᗮ`,
`‖x₀‖ · h (λ ‖x₀‖ - Λ ‖x₁‖ - ρ ‖x₀ + x₁‖) ≤ ‖x₀‖ ‖(W - z)(x₀ + x₁)‖`. -/
lemma first_order_bound {W U₀ L₀ : E →L[ℂ] E} (hU : U₀ ∈ unitary (E →L[ℂ] E)) {e u z : ℂ}
    (he : ‖e‖ = 1) (hz : z = e * u) {K : Submodule ℂ E} (heig : ∀ k ∈ K, U₀ k = e • k)
    {σ h ρ lam Λ : ℝ} (hσ : σ ^ 2 = 1) (hu : σ * u.im ≤ 0)
    (hR : ‖W - U₀ - ((σ * h : ℝ) : ℂ) • (I • (U₀ * L₀))‖ ≤ h * ρ)
    (hpos : ∀ k ∈ K, lam * ‖k‖ ^ 2 ≤ RCLike.re ⟪k, L₀ k⟫_ℂ) (hΛ : ‖L₀‖ ≤ Λ) (hh : 0 ≤ h)
    {x₀ x₁ : E} (h₀ : x₀ ∈ K) (h₁ : x₁ ∈ Kᗮ) :
    ‖x₀‖ * (h * (lam * ‖x₀‖ - Λ * ‖x₁‖ - ρ * ‖x₀ + x₁‖)) ≤
      ‖x₀‖ * ‖(W - z • 1) (x₀ + x₁)‖ := by
  set x := x₀ + x₁ with hx
  set R := W - U₀ - ((σ * h : ℝ) : ℂ) • (I • (U₀ * L₀)) with hRdef
  set c : ℂ := -I * σ * conj e with hc
  have hce : conj e * e = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, he]; simp
  have hcn : ‖c‖ = 1 := by
    rw [hc, norm_mul, norm_mul, norm_neg, Complex.norm_I, Complex.norm_conj, he]
    have : ‖(σ : ℂ)‖ = 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have : |σ| ^ 2 = 1 := by rw [sq_abs, hσ]
      nlinarith [abs_nonneg σ]
    rw [this]; ring
  have hx0x1 : ⟪x₀, x₁⟫_ℂ = 0 := (Submodule.mem_orthogonal K x₁).1 h₁ x₀ h₀
  have hx0x : ⟪x₀, x⟫_ℂ = (‖x₀‖ ^ 2 : ℝ) := by
    rw [hx, inner_add_right, hx0x1, add_zero, inner_self_eq_norm_sq_to_K]; simp
  have hstar : ∀ y, ⟪x₀, U₀ y⟫_ℂ = e * ⟪x₀, y⟫_ℂ := by
    intro y
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
      star_apply_of_eigen hU he (heig x₀ h₀), inner_smul_left, Complex.conj_conj]
  have hWsplit : (W - z • 1) x = (U₀ x - z • x) + ((σ * h : ℝ) : ℂ) • (I • U₀ (L₀ x)) + R x := by
    simp only [hRdef, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.mul_apply]
    abel
  have hinner : ⟪x₀, (W - z • 1) x⟫_ℂ = (e - z) * (‖x₀‖ ^ 2 : ℝ) +
      ((σ * h : ℝ) : ℂ) * I * e * (⟪x₀, L₀ x₀⟫_ℂ + ⟪x₀, L₀ x₁⟫_ℂ) + ⟪x₀, R x⟫_ℂ := by
    rw [hWsplit, inner_add_right, inner_add_right, inner_sub_right, hstar, inner_smul_right,
      hx0x, inner_smul_right, inner_smul_right, hstar, hx, map_add, inner_add_right]
    ring
  -- the real part of `c ⟪x₀, (W - z) x⟫`
  have hre : RCLike.re (c * ⟪x₀, (W - z • 1) x⟫_ℂ) =
      -σ * u.im * ‖x₀‖ ^ 2 + h * RCLike.re ⟪x₀, L₀ x₀⟫_ℂ + h * RCLike.re ⟪x₀, L₀ x₁⟫_ℂ +
        RCLike.re (c * ⟪x₀, R x⟫_ℂ) := by
    rw [hinner, hz]
    have h1 : c * ((e - e * u) * (‖x₀‖ ^ 2 : ℝ)) = (-I * σ * (1 - u)) * (‖x₀‖ ^ 2 : ℝ) := by
      rw [hc]
      calc -I * σ * conj e * ((e - e * u) * (‖x₀‖ ^ 2 : ℝ))
          = -I * σ * (conj e * e) * (1 - u) * (‖x₀‖ ^ 2 : ℝ) := by ring
        _ = _ := by rw [hce]; ring
    have h2 : c * (((σ * h : ℝ) : ℂ) * I * e * (⟪x₀, L₀ x₀⟫_ℂ + ⟪x₀, L₀ x₁⟫_ℂ)) =
        (h : ℂ) * (⟪x₀, L₀ x₀⟫_ℂ + ⟪x₀, L₀ x₁⟫_ℂ) := by
      rw [hc]
      have hσc : (σ : ℂ) ^ 2 = 1 := by exact_mod_cast hσ
      calc -I * σ * conj e * (((σ * h : ℝ) : ℂ) * I * e * (⟪x₀, L₀ x₀⟫_ℂ + ⟪x₀, L₀ x₁⟫_ℂ))
          = -(I * I) * (σ : ℂ) ^ 2 * (conj e * e) * h *
              (⟪x₀, L₀ x₀⟫_ℂ + ⟪x₀, L₀ x₁⟫_ℂ) := by push_cast; ring
        _ = _ := by rw [hσc, hce, Complex.I_mul_I]; ring
    rw [mul_add, mul_add, h1, h2]
    simp only [RCLike.re_to_complex, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.neg_re,
      Complex.neg_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  -- lower bounds for the pieces
  have hb1 : 0 ≤ -σ * u.im * ‖x₀‖ ^ 2 := by
    have := sq_nonneg ‖x₀‖
    nlinarith
  have hb2 : h * (lam * ‖x₀‖ ^ 2) ≤ h * RCLike.re ⟪x₀, L₀ x₀⟫_ℂ :=
    mul_le_mul_of_nonneg_left (hpos x₀ h₀) hh
  have hb3 : -(h * (‖x₀‖ * (Λ * ‖x₁‖))) ≤ h * RCLike.re ⟪x₀, L₀ x₁⟫_ℂ := by
    have : |RCLike.re ⟪x₀, L₀ x₁⟫_ℂ| ≤ ‖x₀‖ * (Λ * ‖x₁‖) :=
      (RCLike.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left ((L₀.le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hΛ (norm_nonneg _))) (norm_nonneg _)))
    have := neg_abs_le (RCLike.re ⟪x₀, L₀ x₁⟫_ℂ)
    nlinarith
  have hb4 : -(‖x₀‖ * (h * ρ * ‖x‖)) ≤ RCLike.re (c * ⟪x₀, R x⟫_ℂ) := by
    have : |RCLike.re (c * ⟪x₀, R x⟫_ℂ)| ≤ ‖x₀‖ * (h * ρ * ‖x‖) := by
      refine (RCLike.abs_re_le_norm _).trans ?_
      rw [norm_mul, hcn, one_mul]
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
        ((R.le_opNorm _).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))) (norm_nonneg _))
    linarith [neg_abs_le (RCLike.re (c * ⟪x₀, R x⟫_ℂ))]
  have hup : RCLike.re (c * ⟪x₀, (W - z • 1) x⟫_ℂ) ≤ ‖x₀‖ * ‖(W - z • 1) x‖ := by
    refine (RCLike.re_le_norm _).trans ?_
    rw [norm_mul, hcn, one_mul]
    exact norm_inner_le_norm _ _
  have : ‖x₀‖ * (h * (lam * ‖x₀‖ - Λ * ‖x₁‖ - ρ * ‖x‖)) =
      h * (lam * ‖x₀‖ ^ 2) - h * (‖x₀‖ * (Λ * ‖x₁‖)) - ‖x₀‖ * (h * ρ * ‖x‖) := by ring
  rw [this]
  linarith

/-- Arithmetic combination of the zeroth- and first-order bounds. -/
lemma combine_gap_bounds {N a c₁ r g h lam Λ ρ : ℝ} (ha : 0 ≤ a) (hc₁ : 0 ≤ c₁)
    (hr : a ^ 2 + c₁ ^ 2 = r ^ 2) (hr0 : 0 ≤ r) (hg : 0 < g) (hh : 0 ≤ h) (hlam : 0 < lam)
    (hΛ : 0 ≤ Λ) (hρ : ρ ≤ lam / 4) (hhs : h * (lam + Λ) * (Λ + ρ) ≤ g * lam / 4)
    (h1 : g * c₁ - h * (Λ + ρ) * r ≤ N) (h2 : h * (lam * a - Λ * c₁ - ρ * r) ≤ N) :
    h * g * lam / (2 * (g + h * (lam + Λ))) * r ≤ N := by
  have hac : r ≤ a + c₁ := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_nonneg ha hc₁]
  have hpos : 0 < 2 * (g + h * (lam + Λ)) := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  -- `N ≥ h(λ - ρ) r - h(λ + Λ) c₁` and `g c₁ ≤ N + h(Λ+ρ) r`
  have h3 : h * (lam - ρ) * r - h * (lam + Λ) * c₁ ≤ N := by
    nlinarith [mul_nonneg (mul_nonneg hh hlam.le) (sub_nonneg.2 (by linarith : r - c₁ ≤ a))]
  have h4 : g * N ≥ g * (h * (lam - ρ) * r) - h * (lam + Λ) * (N + h * (Λ + ρ) * r) := by
    nlinarith [mul_nonneg hh (by positivity : (0 : ℝ) ≤ lam + Λ)]
  have h5 : h * (lam + Λ) * (h * (Λ + ρ) * r) ≤ h * (g * lam / 4) * r := by
    have := mul_le_mul_of_nonneg_left hhs (mul_nonneg hh hr0)
    nlinarith
  nlinarith [mul_nonneg (mul_nonneg hh hr0) hg.le]

end

section

/-! ## Eigenvalues of compact perturbations of the identity -/

open scoped InnerProductSpace ComplexConjugate
open Set Metric Filter Topology Complex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- An operator factoring through a finite-dimensional subspace is compact. -/
lemma isCompactOperator_subtypeL_comp (K : Submodule ℂ E) [FiniteDimensional ℂ K]
    [K.HasOrthogonalProjection] (X : K →L[ℂ] K) :
    IsCompactOperator (K.subtypeL ∘L X ∘L K.orthogonalProjection) := by
  have hX : IsCompactOperator (K.subtypeL ∘L X) := by
    refine ⟨(K.subtypeL ∘L X) '' closedBall 0 1, (isCompact_closedBall 0 1).image
      (K.subtypeL ∘L X).continuous, ?_⟩
    refine Filter.mem_of_superset (closedBall_mem_nhds 0 one_pos) fun x hx => ?_
    exact ⟨x, hx, rfl⟩
  exact hX.comp_clm K.orthogonalProjection

omit [CompleteSpace E] in
/-- For `U₀ - 1` compact and `w ≠ 1`, the eigenspace `ker (U₀ - w)` is finite-dimensional. -/
lemma finiteDimensional_ker_of_isCompactOperator {U₀ : E →L[ℂ] E}
    (hC : IsCompactOperator ((U₀ - 1 : E →L[ℂ] E) : E → E)) {w : ℂ} (hw : w ≠ 1) :
    FiniteDimensional ℂ (LinearMap.ker ((U₀ - w • 1 : E →L[ℂ] E) : E →ₗ[ℂ] E)) := by
  set K₀ := LinearMap.ker ((U₀ - w • 1 : E →L[ℂ] E) : E →ₗ[ℂ] E) with hK₀
  have hμ : w - 1 ≠ 0 := sub_ne_zero.2 hw
  obtain ⟨S, hS, hCS⟩ := IsCompactOperator.image_closedBall_subset_compact
    (f := ((U₀ - 1 : E →L[ℂ] E) : E →ₗ[ℂ] E)) hC 1
  have hclosed : IsClosed (K₀ : Set E) := ContinuousLinearMap.isClosed_ker _
  refine FiniteDimensional.of_isCompact_closedBall₀ ℂ one_pos ?_
  rw [Topology.IsInducing.subtypeVal.isCompact_iff]
  refine IsCompact.of_isClosed_subset (hS.smul (w - 1)⁻¹)
    (hclosed.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_closedBall) ?_
  rintro _ ⟨k, hk, rfl⟩
  have hk1 : U₀ k = w • (k : E) := by
    have h2 : (U₀ - w • 1) (k : E) = 0 := k.2
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, sub_eq_zero] at h2
    exact h2
  refine ⟨(U₀ - 1) k, hCS ⟨k, ?_, rfl⟩, ?_⟩
  · simpa using hk
  · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hk1]
    rw [show w • (k : E) - k = (w - 1) • (k : E) by rw [sub_smul, one_smul], smul_smul,
      inv_mul_cancel₀ hμ, one_smul]

omit [CompleteSpace E] in
/-- **Isolation of the eigenvalue.** For `U₀ - 1` compact and `e^{iα} ≠ 1`, `U₀ - e^{i(α+φ)}`
is uniformly bounded below on `ker (U₀ - e^{iα})ᗮ` for `|φ|` small. -/
lemma exists_gap_of_isCompactOperator {U₀ : E →L[ℂ] E}
    (hC : IsCompactOperator ((U₀ - 1 : E →L[ℂ] E) : E → E)) {α : ℝ}
    (hα : exp (α * I) ≠ 1) (K₀ : Submodule ℂ E)
    (hK₀ : ∀ v, (U₀ - exp (α * I) • 1) v = 0 → v ∈ K₀) :
    ∃ η > 0, ∃ g > 0, ∀ φ : ℝ, |φ| ≤ η → ∀ x ∈ K₀ᗮ,
        g * ‖x‖ ≤ ‖(U₀ - exp ((α + φ : ℝ) * I) • 1) x‖ := by
  by_contra H
  push_neg at H
  have H' : ∀ n : ℕ, ∃ φ : ℝ, |φ| ≤ 1 / (n + 1) ∧ ∃ x ∈ K₀ᗮ,
      ‖(U₀ - exp ((α + φ : ℝ) * I) • 1) x‖ < 1 / (n + 1) * ‖x‖ := fun n =>
    H _ (by positivity) _ (by positivity)
  choose φ hφ x hxK hx using H'
  have hx0 : ∀ n, x n ≠ 0 := by
    intro n h
    have := hx n
    rw [h, map_zero, norm_zero, mul_zero] at this
    exact lt_irrefl _ this
  let u : ℕ → E := fun n => ((‖x n‖⁻¹ : ℝ) : ℂ) • x n
  have hun : ∀ n, ‖u n‖ = 1 := fun n => by
    show ‖((‖x n‖⁻¹ : ℝ) : ℂ) • x n‖ = 1
    exact norm_real_inv_norm_smul (hx0 n)
  have huK : ∀ n, u n ∈ K₀ᗮ := fun n => by
    show ((‖x n‖⁻¹ : ℝ) : ℂ) • x n ∈ K₀ᗮ
    exact K₀ᗮ.smul_mem _ (hxK n)
  let z : ℕ → ℂ := fun n => exp ((α + φ n : ℝ) * I)
  have hu_small : ∀ n, ‖(U₀ - z n • 1) (u n)‖ ≤ 1 / (n + 1) := by
    intro n
    have hxn : 0 < ‖x n‖ := norm_pos_iff.2 (hx0 n)
    have h1 : ‖(U₀ - z n • 1) (u n)‖ = ‖x n‖⁻¹ * ‖(U₀ - z n • 1) (x n)‖ := by
      simp only [u, map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hxn)]
    rw [h1]
    calc ‖x n‖⁻¹ * ‖(U₀ - z n • 1) (x n)‖ ≤ ‖x n‖⁻¹ * (1 / (n + 1) * ‖x n‖) :=
          mul_le_mul_of_nonneg_left (hx n).le (inv_nonneg.2 hxn.le)
      _ = 1 / (n + 1) := by field_simp
  obtain ⟨S, hS, hCS⟩ := IsCompactOperator.image_closedBall_subset_compact
    (f := ((U₀ - 1 : E →L[ℂ] E) : E →ₗ[ℂ] E)) hC 1
  have hCu : ∀ n, (U₀ - 1) (u n) ∈ S := fun n =>
    hCS ⟨u n, by simp [hun n], rfl⟩
  obtain ⟨y, -, ψ, hψ, hy⟩ := hS.tendsto_subseq hCu
  have h1n : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hφ0 : Tendsto φ atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => (hφ n)) h1n
  have hzlim : Tendsto z atTop (𝓝 (exp (α * I))) := by
    have hc : Continuous fun s : ℝ => exp ((α + s : ℝ) * I) := by fun_prop
    have h := (hc.tendsto 0).comp hφ0
    simpa [z, Function.comp_def] using h
  have hsmall : Tendsto (fun n => (U₀ - z n • 1) (u n)) atTop (𝓝 0) :=
    squeeze_zero_norm hu_small h1n
  have hμ : exp (α * I) - 1 ≠ 0 := sub_ne_zero.2 hα
  have hψt : Tendsto ψ atTop atTop := hψ.tendsto_atTop
  -- `(z - 1) u = (U₀ - 1) u - (U₀ - z) u`
  have hid : ∀ n, (z n - 1) • u n = (U₀ - 1) (u n) - (U₀ - z n • 1) (u n) := by
    intro n
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, sub_smul, one_smul]
    abel
  have hlim1 : Tendsto (fun n => (z (ψ n) - 1) • u (ψ n)) atTop (𝓝 y) := by
    have := hy.sub (hsmall.comp hψt)
    rw [sub_zero] at this
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, hid]
  have hzψ : Tendsto (fun n => z (ψ n) - 1) atTop (𝓝 (exp (α * I) - 1)) :=
    (hzlim.comp hψt).sub_const 1
  have hlim2 : Tendsto (fun n => u (ψ n)) atTop (𝓝 ((exp (α * I) - 1)⁻¹ • y)) := by
    have h := (hzψ.inv₀ hμ).smul hlim1
    refine h.congr' ?_
    filter_upwards [hzψ.eventually_ne hμ] with n hn
    rw [smul_smul, inv_mul_cancel₀ hn, one_smul]
  set v := (exp (α * I) - 1)⁻¹ • y with hv
  have hvn : ‖v‖ = 1 := by
    have := (continuous_norm.tendsto v).comp hlim2
    simp only [Function.comp_def, hun] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have hvK : v ∈ K₀ᗮ :=
    (Submodule.isClosed_orthogonal K₀).mem_of_tendsto hlim2 (Eventually.of_forall fun n => huK _)
  have hvker : v ∈ K₀ := by
    have h1 : Tendsto (fun n => (U₀ - z (ψ n) • 1) (u (ψ n))) atTop
        (𝓝 ((U₀ - exp (α * I) • 1) v)) := by
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply]
      exact ((U₀.continuous.tendsto v).comp hlim2).sub ((hzlim.comp hψt).smul hlim2)
    exact hK₀ v (tendsto_nhds_unique h1 (hsmall.comp hψt))
  have : v ∈ K₀ ⊓ K₀ᗮ := ⟨hvker, hvK⟩
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at this
  rw [this, norm_zero] at hvn
  exact zero_ne_one hvn

omit [CompleteSpace E] in
/-- A strictly positive operator is coercive on a finite-dimensional subspace. -/
lemma exists_coercive_of_finiteDimensional (K₀ : Submodule ℂ E) [FiniteDimensional ℂ K₀]
    {L₀ : E →L[ℂ] E} (hL : ∀ v : E, v ≠ 0 → 0 < RCLike.re ⟪v, L₀ v⟫_ℂ) :
    ∃ lam > 0, ∀ k ∈ K₀, lam * ‖k‖ ^ 2 ≤ RCLike.re ⟪k, L₀ k⟫_ℂ := by
  have hscale : ∀ (c : ℝ) (k : E), RCLike.re ⟪(c : ℂ) • k, L₀ ((c : ℂ) • k)⟫_ℂ =
      c ^ 2 * RCLike.re ⟪k, L₀ k⟫_ℂ := by
    intro c k
    rw [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc,
      ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.re_ofReal_mul, RCLike.re_to_complex]
    ring
  by_cases hK : K₀ = ⊥
  · refine ⟨1, one_pos, fun k hk => ?_⟩
    rw [hK, Submodule.mem_bot] at hk
    simp [hk]
  haveI : Nontrivial K₀ := Submodule.nontrivial_iff_ne_bot.2 hK
  let f : K₀ → ℝ := fun k => RCLike.re ⟪(k : E), L₀ k⟫_ℂ
  have hf : Continuous f := by fun_prop
  obtain ⟨k₀, hk₀, hmin⟩ := (isCompact_sphere (0 : K₀) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 zero_le_one) hf.continuousOn
  have hk₀n : ‖(k₀ : E)‖ = 1 := by simpa using hk₀
  refine ⟨f k₀, hL _ (by intro h; rw [h, norm_zero] at hk₀n; exact zero_ne_one hk₀n), ?_⟩
  intro k hk
  by_cases hk0 : k = 0
  · simp [hk0]
  have hkn : 0 < ‖k‖ := norm_pos_iff.2 hk0
  set kk : K₀ := ⟨((‖k‖⁻¹ : ℝ) : ℂ) • k, K₀.smul_mem _ hk⟩
  have hkk : kk ∈ sphere (0 : K₀) 1 := by
    rw [mem_sphere_zero_iff_norm, Submodule.coe_norm]
    exact norm_real_inv_norm_smul hk0
  have h1 : f k₀ ≤ f kk := hmin hkk
  have h2 : f kk = (‖k‖⁻¹) ^ 2 * RCLike.re ⟪k, L₀ k⟫_ℂ := hscale _ k
  rw [h2, inv_pow, inv_mul_eq_div, le_div_iff₀ (by positivity)] at h1
  exact h1

end

section

/-! ## Courant–Fischer inequalities for self-adjoint operators in finite dimension -/

open scoped InnerProductSpace
open Module

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

omit [FiniteDimensional ℂ F] in
/-- The quadratic form in an orthonormal eigenbasis. -/
lemma re_inner_eq_sum_of_eigenbasis {T : F →ₗ[ℂ] F} (hT : T.IsSymmetric) {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι ℂ F) (ν : ι → ℝ)
    (hb : ∀ i, T (b i) = (ν i : ℂ) • b i) (x : F) :
    RCLike.re ⟪x, T x⟫_ℂ = ∑ i, ν i * ‖⟪b i, x⟫_ℂ‖ ^ 2 := by
  rw [← b.sum_inner_mul_inner x (T x), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ⟪b i, T x⟫_ℂ = (ν i : ℂ) * ⟪b i, x⟫_ℂ := by
    rw [← hT, hb, inner_smul_left]; simp
  rw [h1, ← inner_conj_symm x (b i)]
  have : (starRingEnd ℂ) ⟪b i, x⟫_ℂ * ((ν i : ℂ) * ⟪b i, x⟫_ℂ) =
      ((ν i * ‖⟪b i, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_left_comm, RCLike.conj_mul, Complex.ofReal_mul, Complex.ofReal_pow]; rfl
  rw [this]; exact Complex.ofReal_re _

variable {n : ℕ} {T : F →ₗ[ℂ] F}

/-- **Courant–Fischer, lower half.** If `re ⟪x, T x⟫ ≥ c ‖x‖²` on a subspace of dimension
`> k`, then `c ≤ ν_k`. -/
theorem le_eigenvalues_of_subspace (hT : T.IsSymmetric) (hn : finrank ℂ F = n) (k : Fin n)
    (S : Submodule ℂ F) (hS : k.1 < finrank ℂ S) (c : ℝ)
    (h : ∀ x ∈ S, c * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, T x⟫_ℂ) : c ≤ hT.eigenvalues hn k := by
  set b := hT.eigenvectorBasis hn
  set ν := hT.eigenvalues hn
  -- the map recording the first `k` coordinates
  let f : S →ₗ[ℂ] (Fin k.1 → ℂ) :=
    { toFun := fun x j => ⟪b ⟨j.1, j.2.trans k.2⟩, (x : F)⟫_ℂ
      map_add' := fun x y => by ext j; simp
      map_smul' := fun a x => by ext j; simp }
  have hker : LinearMap.ker f ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hS)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hcoord : ∀ j : Fin n, j < k → ⟪b j, (x : F)⟫_ℂ = 0 := by
    intro j hj
    have := congr_fun (LinearMap.mem_ker.mp hx) ⟨j.1, hj⟩
    simpa [f] using this
  have hxne : (x : F) ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hq := re_inner_eq_sum_of_eigenbasis hT b ν (fun i => by simp [b, ν]) (x : F)
  have hupper : RCLike.re ⟪(x : F), T x⟫_ℂ ≤ ν k * ‖(x : F)‖ ^ 2 := by
    rw [hq, ← b.sum_sq_norm_inner_right (x : F), Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rcases lt_or_ge j k with hj | hj
    · simp [hcoord j hj]
    · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hn hj) (by positivity)
  have hpos : 0 < ‖(x : F)‖ ^ 2 := by positivity
  have := (h x x.2).trans hupper
  exact le_of_mul_le_mul_right this hpos

/-- **Courant–Fischer, upper half.** If `re ⟪x, T x⟫ ≤ c ‖x‖²` on a subspace of dimension
`≥ n - k`, then `ν_k ≤ c`. -/
theorem eigenvalues_le_of_subspace (hT : T.IsSymmetric) (hn : finrank ℂ F = n) (k : Fin n)
    (S : Submodule ℂ F) (hS : n - k.1 ≤ finrank ℂ S) (c : ℝ)
    (h : ∀ x ∈ S, RCLike.re ⟪x, T x⟫_ℂ ≤ c * ‖x‖ ^ 2) : hT.eigenvalues hn k ≤ c := by
  set b := hT.eigenvectorBasis hn
  set ν := hT.eigenvalues hn
  let f : S →ₗ[ℂ] (Fin (n - k.1 - 1) → ℂ) :=
    { toFun := fun x j => ⟪b ⟨k.1 + 1 + j.1, by omega⟩, (x : F)⟫_ℂ
      map_add' := fun x y => by ext j; simp
      map_smul' := fun a x => by ext j; simp }
  have hker : LinearMap.ker f ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simp; omega)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hcoord : ∀ j : Fin n, k < j → ⟪b j, (x : F)⟫_ℂ = 0 := by
    intro j hj
    have := congr_fun (LinearMap.mem_ker.mp hx) ⟨j.1 - k.1 - 1, by omega⟩
    have e : (⟨k.1 + 1 + (j.1 - k.1 - 1), by omega⟩ : Fin n) = j := by
      ext; simp; omega
    simpa [f, e] using this
  have hxne : (x : F) ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hq := re_inner_eq_sum_of_eigenbasis hT b ν (fun i => by simp [b, ν]) (x : F)
  have hlower : ν k * ‖(x : F)‖ ^ 2 ≤ RCLike.re ⟪(x : F), T x⟫_ℂ := by
    rw [hq, ← b.sum_sq_norm_inner_right (x : F), Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rcases le_or_gt j k with hj | hj
    · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hn hj) (by positivity)
    · simp [hcoord j hj]
  have hpos : 0 < ‖(x : F)‖ ^ 2 := by positivity
  have := hlower.trans (h x x.2)
  exact le_of_mul_le_mul_right this hpos

/-- The span of the vectors of an orthonormal basis indexed by a finite set. -/
def obSpan {ι : Type*} [Fintype ι] (u : OrthonormalBasis ι ℂ F) (s : Finset ι) :
    Submodule ℂ F :=
  Submodule.span ℂ (u '' (s : Set ι))

omit [FiniteDimensional ℂ F] in
lemma finrank_obSpan {ι : Type*} [Fintype ι] (u : OrthonormalBasis ι ℂ F) (s : Finset ι) :
    finrank ℂ (obSpan u s) = s.card := by
  unfold obSpan
  rw [Set.image_eq_range, finrank_span_eq_card]
  · simp
  · exact (u.orthonormal.linearIndependent).comp _ Subtype.val_injective

omit [FiniteDimensional ℂ F] in
lemma inner_eq_zero_of_mem_obSpan {ι : Type*} [Fintype ι] (u : OrthonormalBasis ι ℂ F)
    (s : Finset ι) {x : F} (hx : x ∈ obSpan u s) {j : ι} (hj : j ∉ s) :
    ⟪u j, x⟫_ℂ = 0 := by
  unfold obSpan at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := hy
    have hne : j ≠ i := fun h => by subst h; exact hj hi
    simp [hne]
  | zero => simp
  | add y z _ _ hy hz => simp [hy, hz]
  | smul a y _ hy => simp [hy]

/-- On the span of the top `k + 1` eigenvectors the quadratic form is `≥ ν_k`. -/
lemma eigenvalues_mul_le_of_coord (hT : T.IsSymmetric) (hn : finrank ℂ F = n) (k : Fin n)
    (x : F) (hx : ∀ j : Fin n, k < j → ⟪hT.eigenvectorBasis hn j, x⟫_ℂ = 0) :
    hT.eigenvalues hn k * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, T x⟫_ℂ := by
  have hq := re_inner_eq_sum_of_eigenbasis hT (hT.eigenvectorBasis hn) (hT.eigenvalues hn)
    (fun i => by simp) x
  rw [hq, ← (hT.eigenvectorBasis hn).sum_sq_norm_inner_right x, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases le_or_gt j k with hj | hj
  · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hn hj) (by positivity)
  · simp [hx j hj]

/-- The span of the eigenvectors with index `≤ k`. -/
def topSpan (hT : T.IsSymmetric) (hn : finrank ℂ F = n) (k : Fin n) : Submodule ℂ F :=
  Submodule.span ℂ (Set.range fun j : {j : Fin n // j ≤ k} => hT.eigenvectorBasis hn j)

lemma finrank_topSpan (hT : T.IsSymmetric) (hn : finrank ℂ F = n) (k : Fin n) :
    finrank ℂ (topSpan hT hn k) = k.1 + 1 := by
  unfold topSpan
  rw [finrank_span_eq_card]
  · rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun j : Fin n => j ≤ k) = Finset.Iic k := by ext; simp
    rw [this, Fin.card_Iic]
  · exact ((hT.eigenvectorBasis hn).orthonormal.linearIndependent).comp _ Subtype.val_injective

lemma coord_eq_zero_of_mem_topSpan (hT : T.IsSymmetric) (hn : finrank ℂ F = n) (k : Fin n)
    {x : F} (hx : x ∈ topSpan hT hn k) (j : Fin n) (hj : k < j) :
    ⟪hT.eigenvectorBasis hn j, x⟫_ℂ = 0 := by
  unfold topSpan at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨i, hi⟩, rfl⟩ := hy
    have hne : j ≠ i := fun h => by subst h; exact absurd hi (not_le.mpr hj)
    simp [hne]
  | zero => simp
  | add y z _ _ hy hz => simp [hy, hz]
  | smul a y _ hy => simp [hy]

/-- **Weyl's inequality**: `ν_k(T) - ‖S - T‖ ≤ ν_k(S)`. -/
theorem eigenvalues_sub_norm_le {S T : F →L[ℂ] F} (hS : (S : F →ₗ[ℂ] F).IsSymmetric)
    (hT : (T : F →ₗ[ℂ] F).IsSymmetric) (hn : finrank ℂ F = n) (k : Fin n) :
    hT.eigenvalues hn k - ‖S - T‖ ≤ hS.eigenvalues hn k := by
  refine le_eigenvalues_of_subspace hS hn k (topSpan hT hn k)
    (by rw [finrank_topSpan]; omega) _ fun x hx => ?_
  have h1 := eigenvalues_mul_le_of_coord hT hn k x
    (fun j hj => coord_eq_zero_of_mem_topSpan hT hn k hx j hj)
  have h2 : |RCLike.re ⟪x, (S - T) x⟫_ℂ| ≤ ‖S - T‖ * ‖x‖ ^ 2 := by
    calc |RCLike.re ⟪x, (S - T) x⟫_ℂ| ≤ ‖⟪x, (S - T) x⟫_ℂ‖ := RCLike.abs_re_le_norm _
      _ ≤ ‖x‖ * ‖(S - T) x‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖S - T‖ * ‖x‖) := by gcongr; exact (S - T).le_opNorm x
      _ = ‖S - T‖ * ‖x‖ ^ 2 := by ring
  have h3 : RCLike.re ⟪x, S x⟫_ℂ = RCLike.re ⟪x, T x⟫_ℂ + RCLike.re ⟪x, (S - T) x⟫_ℂ := by
    simp
  change (hT.eigenvalues hn k - ‖S - T‖) * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, S x⟫_ℂ
  rw [h3]
  have := neg_abs_le (RCLike.re ⟪x, (S - T) x⟫_ℂ)
  have h1' : hT.eigenvalues hn k * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, T x⟫_ℂ := h1
  have e : (hT.eigenvalues hn k - ‖S - T‖) * ‖x‖ ^ 2 =
      hT.eigenvalues hn k * ‖x‖ ^ 2 - ‖S - T‖ * ‖x‖ ^ 2 := by ring
  linarith

/-- Weyl's inequality, two-sided form. -/
theorem abs_eigenvalues_sub_le {S T : F →L[ℂ] F} (hS : (S : F →ₗ[ℂ] F).IsSymmetric)
    (hT : (T : F →ₗ[ℂ] F).IsSymmetric) (hn : finrank ℂ F = n) (k : Fin n) :
    |hS.eigenvalues hn k - hT.eigenvalues hn k| ≤ ‖S - T‖ := by
  have h1 := eigenvalues_sub_norm_le hS hT hn k
  have h2 := eigenvalues_sub_norm_le hT hS hn k
  rw [norm_sub_rev] at h2
  rw [abs_le]; constructor <;> linarith

end

section

/-! ## First-order perturbation of sorted eigenvalues -/

open scoped InnerProductSpace
open Module Filter Topology Set

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- A finite family of reals has a positive gap between distinct values. -/
lemma exists_gap {ι : Type*} [Fintype ι] (ν : ι → ℝ) :
    ∃ g > 0, ∀ i j, ν i ≠ ν j → g ≤ |ν i - ν j| := by
  classical
  set S := ((Finset.univ ×ˢ Finset.univ).filter (fun p : ι × ι => ν p.1 ≠ ν p.2)).image
    (fun p => |ν p.1 - ν p.2|) with hSdef
  by_cases hS : S.Nonempty
  · refine ⟨S.min' hS, ?_, fun i j hij => S.min'_le _ ?_⟩
    · obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp (S.min'_mem hS)
      rw [← hpe]
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp
      exact abs_pos.mpr (sub_ne_zero.mpr hp)
    · exact Finset.mem_image.mpr ⟨(i, j), by simp [hij], rfl⟩
  · exact ⟨1, one_pos, fun i j hij =>
      absurd ⟨_, Finset.mem_image.mpr ⟨(i, j), by simp [hij], rfl⟩⟩ hS⟩

omit [FiniteDimensional ℂ F] in
lemma ob_ext {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ F)
    {x y : F} (h : ∀ j, ⟪b j, x⟫_ℂ = ⟪b j, y⟫_ℂ) : x = y :=
  b.repr.injective (by ext j; simp [b.repr_apply_apply, h])

section Adapted

variable {n : ℕ} {T₀ : F →ₗ[ℂ] F} (hT : T₀.IsSymmetric) (hn : finrank ℂ F = n)

/-- The orthogonal projection onto the eigenspace of `T₀` for the value `v`, written in the
eigenbasis. -/
def blockProj (v : ℝ) : F →ₗ[ℂ] F where
  toFun x := ∑ i ∈ Finset.univ.filter (fun i => hT.eigenvalues hn i = v),
    ⟪hT.eigenvectorBasis hn i, x⟫_ℂ • hT.eigenvectorBasis hn i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, smul_smul]

lemma inner_blockProj (v : ℝ) (j : Fin n) (x : F) :
    ⟪hT.eigenvectorBasis hn j, blockProj hT hn v x⟫_ℂ =
      if hT.eigenvalues hn j = v then ⟪hT.eigenvectorBasis hn j, x⟫_ℂ else 0 := by
  simp only [blockProj, LinearMap.coe_mk, AddHom.coe_mk, inner_sum, inner_smul_right,
    OrthonormalBasis.inner_eq_ite, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

lemma blockProj_blockProj (v w : ℝ) (x : F) :
    blockProj hT hn v (blockProj hT hn w x) = if v = w then blockProj hT hn v x else 0 := by
  refine ob_ext (hT.eigenvectorBasis hn) fun j => ?_
  rw [inner_blockProj, inner_blockProj]
  split_ifs with h1 h2 h3 h3 <;> simp_all [inner_blockProj]

lemma apply_blockProj (v : ℝ) (x : F) :
    T₀ (blockProj hT hn v x) = (v : ℂ) • blockProj hT hn v x := by
  refine ob_ext (hT.eigenvectorBasis hn) fun j => ?_
  rw [← hT, hT.apply_eigenvectorBasis, inner_smul_left, inner_smul_right, inner_blockProj]
  split_ifs with h <;> simp [h]

lemma blockProj_apply (v : ℝ) (x : F) :
    blockProj hT hn v (T₀ x) = (v : ℂ) • blockProj hT hn v x := by
  refine ob_ext (hT.eigenvectorBasis hn) fun j => ?_
  rw [inner_blockProj, inner_smul_right, inner_blockProj]
  split_ifs with h
  · rw [← hT, hT.apply_eigenvectorBasis, inner_smul_left, h]; simp
  · simp

lemma sum_blockProj (x : F) :
    ∑ v ∈ Finset.univ.image (hT.eigenvalues hn), blockProj hT hn v x = x := by
  refine ob_ext (hT.eigenvectorBasis hn) fun j => ?_
  rw [inner_sum]
  simp_rw [inner_blockProj]
  rw [Finset.sum_ite_eq]
  simp

lemma blockProj_isSymmetric (v : ℝ) : (blockProj hT hn v).IsSymmetric := by
  intro x y
  simp only [blockProj, LinearMap.coe_mk, AddHom.coe_mk, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_conj_symm, mul_comm]

/-- The pinching of `D`: its block-diagonal part with respect to the eigenspaces of `T₀`. -/
def pinch (D : F →ₗ[ℂ] F) : F →ₗ[ℂ] F :=
  ∑ v ∈ Finset.univ.image (hT.eigenvalues hn), blockProj hT hn v ∘ₗ D ∘ₗ blockProj hT hn v

lemma pinch_apply (D : F →ₗ[ℂ] F) (x : F) :
    pinch hT hn D x = ∑ v ∈ Finset.univ.image (hT.eigenvalues hn),
      blockProj hT hn v (D (blockProj hT hn v x)) := by
  simp [pinch, LinearMap.sum_apply]

lemma pinch_isSymmetric {D : F →ₗ[ℂ] F} (hD : D.IsSymmetric) : (pinch hT hn D).IsSymmetric := by
  intro x y
  simp only [pinch_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [blockProj_isSymmetric, hD, blockProj_isSymmetric]

lemma blockProj_pinch (D : F →ₗ[ℂ] F) {w : ℝ} (hw : w ∈ Finset.univ.image (hT.eigenvalues hn))
    (x : F) : blockProj hT hn w (pinch hT hn D x) =
      blockProj hT hn w (D (blockProj hT hn w x)) := by
  rw [pinch_apply, map_sum, Finset.sum_eq_single w]
  · rw [blockProj_blockProj, if_pos rfl]
  · intro v _ hv
    rw [blockProj_blockProj, if_neg (Ne.symm hv)]
  · intro h; exact absurd hw h

lemma pinch_blockProj (D : F →ₗ[ℂ] F) {w : ℝ} (hw : w ∈ Finset.univ.image (hT.eigenvalues hn))
    (x : F) : pinch hT hn D (blockProj hT hn w x) =
      blockProj hT hn w (D (blockProj hT hn w x)) := by
  rw [pinch_apply, Finset.sum_eq_single w]
  · rw [blockProj_blockProj, if_pos rfl]
  · intro v _ hv
    rw [blockProj_blockProj, if_neg hv, map_zero, map_zero]
  · intro h; exact absurd hw h

/-- **Adapted eigenbasis.** An orthonormal eigenbasis of `T₀`, sorted like its eigenvalues, which
diagonalizes the compression of `D` to every eigenspace, with decreasing diagonal entries. -/
theorem exists_adapted_eigenbasis {D : F →ₗ[ℂ] F} (hD : D.IsSymmetric) :
    ∃ u : OrthonormalBasis (Fin n) ℂ F,
      (∀ k, T₀ (u k) = (hT.eigenvalues hn k : ℂ) • u k) ∧
      (∀ j k, hT.eigenvalues hn j = hT.eigenvalues hn k → j ≠ k → ⟪u j, D (u k)⟫_ℂ = 0) ∧
      (∀ j k, hT.eigenvalues hn j = hT.eigenvalues hn k → j ≤ k →
        RCLike.re ⟪u k, D (u k)⟫_ℂ ≤ RCLike.re ⟪u j, D (u j)⟫_ℂ) := by
  classical
  set ν := hT.eigenvalues hn with hν
  set Vals := Finset.univ.image ν
  obtain ⟨g, hg, hgap⟩ := exists_gap ν
  set Pc := pinch hT hn D
  have hPc : Pc.IsSymmetric := pinch_isSymmetric hT hn hD
  set C := ‖LinearMap.toContinuousLinearMap Pc‖
  have hC : 0 ≤ C := norm_nonneg _
  have hbP : ∀ w ∈ Vals, ∀ x, blockProj hT hn w (Pc x) =
      blockProj hT hn w (D (blockProj hT hn w x)) := fun w hw x => blockProj_pinch hT hn D hw x
  have hPb : ∀ w ∈ Vals, ∀ x, Pc (blockProj hT hn w x) =
      blockProj hT hn w (D (blockProj hT hn w x)) := fun w hw x => pinch_blockProj hT hn D hw x
  have hPcb : ∀ x, ‖Pc x‖ ≤ C * ‖x‖ := fun x =>
    (LinearMap.toContinuousLinearMap Pc).le_opNorm x
  set ε : ℝ := g / (4 * (C + 1))
  have hε : 0 < ε := by positivity
  have hεC : 2 * (ε * C) < g := by
    have : ε * C ≤ g / 4 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  set M : F →ₗ[ℂ] F := T₀ + (ε : ℂ) • Pc
  have hM : M.IsSymmetric := by
    intro x y
    simp only [M, LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right]
    rw [hT x y, hPc x y]
    simp
  -- every eigenvector of `M` lies in a single eigenspace of `T₀`
  have key : ∀ (m : ℝ) (x : F), x ≠ 0 → M x = (m : ℂ) • x →
      ∃ w ∈ Vals, blockProj hT hn w x = x ∧ |m - w| ≤ ε * C ∧
        Pc x = (((m - w) / ε : ℝ) : ℂ) • x := by
    intro m x hx0 hMx
    have hblock : ∀ w ∈ Vals, (ε : ℂ) • Pc (blockProj hT hn w x) =
        ((m - w : ℝ) : ℂ) • blockProj hT hn w x := by
      intro w hw
      have h1 : blockProj hT hn w (M x) = (m : ℂ) • blockProj hT hn w x := by
        rw [hMx, map_smul]
      simp only [M, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
        blockProj_apply, hbP w hw] at h1
      rw [hPb w hw]
      rw [show ((m - w : ℝ) : ℂ) • blockProj hT hn w x =
        (m : ℂ) • blockProj hT hn w x - (w : ℂ) • blockProj hT hn w x by
          rw [← sub_smul]; push_cast; rfl]
      rw [← h1]; abel
    have hbound : ∀ w ∈ Vals, blockProj hT hn w x ≠ 0 → |m - w| ≤ ε * C := by
      intro w hw hne
      have h := congr_arg norm (hblock w hw)
      rw [norm_smul, norm_smul] at h
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε] at h
      have hpos : 0 < ‖blockProj hT hn w x‖ := norm_pos_iff.mpr hne
      have : |m - w| * ‖blockProj hT hn w x‖ ≤ ε * C * ‖blockProj hT hn w x‖ := by
        rw [← h, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hPcb _) hε.le
      exact le_of_mul_le_mul_right this hpos
    obtain ⟨w₀, hw₀, hne₀⟩ : ∃ w ∈ Vals, blockProj hT hn w x ≠ 0 := by
      by_contra h
      push_neg at h
      apply hx0
      rw [← sum_blockProj hT hn x]
      exact Finset.sum_eq_zero h
    have hzero : ∀ w ∈ Vals, w ≠ w₀ → blockProj hT hn w x = 0 := by
      intro w hw hww₀
      by_contra hne
      have h1 := hbound w hw hne
      have h2 := hbound w₀ hw₀ hne₀
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨i₀, -, rfl⟩ := Finset.mem_image.mp hw₀
      have h3 := hgap i i₀ hww₀
      have : |ν i - ν i₀| ≤ 2 * (ε * C) := by
        calc |ν i - ν i₀| = |(m - ν i₀) - (m - ν i)| := by ring_nf
          _ ≤ |m - ν i₀| + |m - ν i| := abs_sub _ _
          _ ≤ 2 * (ε * C) := by linarith
      linarith
    have hx : blockProj hT hn w₀ x = x := by
      conv_rhs => rw [← sum_blockProj hT hn x]
      rw [Finset.sum_eq_single w₀ (fun w hw hne => hzero w hw hne) (fun h => absurd hw₀ h)]
    refine ⟨w₀, hw₀, hx, hbound w₀ hw₀ hne₀, ?_⟩
    have h := hblock w₀ hw₀
    rw [hx] at h
    have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
    calc Pc x = (ε : ℂ)⁻¹ • ((ε : ℂ) • Pc x) := by rw [smul_smul, inv_mul_cancel₀ hε', one_smul]
      _ = _ := by rw [h, smul_smul]; congr 1; push_cast; field_simp
  -- the eigenbasis of `M`
  set u := hM.eigenvectorBasis hn
  set m := hM.eigenvalues hn
  have hu : ∀ k, M (u k) = (m k : ℂ) • u k := fun k => by simp [u, m]
  have hu0 : ∀ k, u k ≠ 0 := fun k => u.orthonormal.ne_zero k
  choose w hwV hwP hwb hwPc using fun k => key (m k) (u k) (hu0 k) (hu k)
  have hTu : ∀ k, T₀ (u k) = (w k : ℂ) • u k := fun k => by
    rw [← hwP k, apply_blockProj, hwP k]
  -- `w` is antitone
  have hwanti : ∀ j k, j ≤ k → w k ≤ w j := by
    intro j k hjk
    by_contra hlt
    push_neg at hlt
    have hm := hM.eigenvalues_antitone hn hjk
    have h1 := hwb j
    have h2 := hwb k
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (hwV j)
    obtain ⟨i', -, hi'⟩ := Finset.mem_image.mp (hwV k)
    have h3 := hgap i' i (by rw [hi, hi']; exact hlt.ne')
    rw [hi, hi', abs_of_pos (by linarith)] at h3
    rw [abs_le] at h1 h2
    have : m k ≤ m j := hm
    linarith
  -- `w = ν` by Courant–Fischer
  have hwν : ∀ k, w k = ν k := by
    intro k
    apply le_antisymm
    · refine le_eigenvalues_of_subspace hT hn k (obSpan u (Finset.Iic k))
        (by rw [finrank_obSpan, Fin.card_Iic]; omega) _ fun x hx => ?_
      rw [re_inner_eq_sum_of_eigenbasis hT u w hTu x, ← u.sum_sq_norm_inner_right x,
        Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      by_cases hj : j ∈ Finset.Iic k
      · exact mul_le_mul_of_nonneg_right (hwanti j k (Finset.mem_Iic.mp hj)) (by positivity)
      · simp [inner_eq_zero_of_mem_obSpan u _ hx hj]
    · refine eigenvalues_le_of_subspace hT hn k (obSpan u (Finset.Ici k))
        (by rw [finrank_obSpan, Fin.card_Ici]) _ fun x hx => ?_
      rw [re_inner_eq_sum_of_eigenbasis hT u w hTu x, ← u.sum_sq_norm_inner_right x,
        Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      by_cases hj : j ∈ Finset.Ici k
      · exact mul_le_mul_of_nonneg_right (hwanti k j (Finset.mem_Ici.mp hj)) (by positivity)
      · simp [inner_eq_zero_of_mem_obSpan u _ hx hj]
  -- inner products with `D` inside a block
  have hDblock : ∀ j k, w j = w k → ⟪u j, D (u k)⟫_ℂ =
      (((m k - w k) / ε : ℝ) : ℂ) * ⟪u j, u k⟫_ℂ := by
    intro j k hjk
    have e1 : ⟪u j, D (u k)⟫_ℂ = ⟪u j, Pc (u k)⟫_ℂ := by
      conv_lhs => rw [← hwP j, ← hwP k]
      rw [hjk, blockProj_isSymmetric, ← hPb _ (hwV k), hwP k]
    rw [e1, hwPc k, inner_smul_right]
  refine ⟨u, fun k => by rw [hTu, hwν], fun j k hjk hne => ?_, fun j k hjk hle => ?_⟩
  · rw [hDblock j k (by rw [hwν, hwν, hjk]), u.orthonormal.2 hne, mul_zero]
  · have hw : w j = w k := by rw [hwν, hwν, hjk]
    rw [hDblock k k rfl, hDblock j j rfl]
    have e : ∀ i, RCLike.re ((((m i - w i) / ε : ℝ) : ℂ) * ⟪u i, u i⟫_ℂ) = (m i - w i) / ε := by
      intro i; rw [inner_self_eq_norm_sq_to_K, u.orthonormal.1 i]; simp
    rw [e, e, hw]
    have hm := hM.eigenvalues_antitone hn hle
    exact div_le_div_of_nonneg_right (by linarith) hε.le

end Adapted

section Perturbation

variable {n : ℕ}

omit [FiniteDimensional ℂ F] in
/-- Coordinates of the block part of a vector. -/
lemma inner_blockSum {ι : Type*} [Fintype ι] [DecidableEq ι] (u : OrthonormalBasis ι ℂ F)
    (Z : Finset ι) (x : F) (j : ι) :
    ⟪u j, ∑ i ∈ Z, ⟪u i, x⟫_ℂ • u i⟫_ℂ = if j ∈ Z then ⟪u j, x⟫_ℂ else 0 := by
  simp only [inner_sum, inner_smul_right, OrthonormalBasis.inner_eq_ite, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq]

omit [FiniteDimensional ℂ F] in
/-- The quadratic form of `D` on a block on which `D` is diagonal. -/
lemma re_inner_blockSum {ι : Type*} [Fintype ι] [DecidableEq ι] (u : OrthonormalBasis ι ℂ F)
    (D : F →L[ℂ] F) (Z : Finset ι) (c : ι → ℂ)
    (hoff : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j → ⟪u i, D (u j)⟫_ℂ = 0) :
    RCLike.re ⟪∑ i ∈ Z, c i • u i, D (∑ i ∈ Z, c i • u i)⟫_ℂ =
      ∑ i ∈ Z, ‖c i‖ ^ 2 * RCLike.re ⟪u i, D (u i)⟫_ℂ := by
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j hj hji => by rw [hoff j hj i hi hji]; simp)
    (fun h => absurd hi h)]
  rw [← mul_assoc, mul_comm (c i), RCLike.conj_mul]
  simp [← Complex.ofReal_pow]

omit [FiniteDimensional ℂ F] in
lemma abs_re_inner_le (D : F →L[ℂ] F) (a b : F) :
    |RCLike.re ⟪a, D b⟫_ℂ| ≤ ‖D‖ * ‖a‖ * ‖b‖ := by
  calc |RCLike.re ⟪a, D b⟫_ℂ| ≤ ‖⟪a, D b⟫_ℂ‖ := RCLike.abs_re_le_norm _
    _ ≤ ‖a‖ * ‖D b‖ := norm_inner_le_norm _ _
    _ ≤ ‖a‖ * (‖D‖ * ‖b‖) := by gcongr; exact D.le_opNorm b
    _ = ‖D‖ * ‖a‖ * ‖b‖ := by ring

omit [FiniteDimensional ℂ F] in
/-- Splitting a vector into a block part and the rest. -/
lemma block_split {ι : Type*} [Fintype ι] [DecidableEq ι] (u : OrthonormalBasis ι ℂ F)
    (Z : Finset ι) (x : F) :
    let z := ∑ i ∈ Z, ⟪u i, x⟫_ℂ • u i
    (∀ j, ⟪u j, x - z⟫_ℂ = if j ∈ Z then 0 else ⟪u j, x⟫_ℂ) ∧
      ‖x‖ ^ 2 = ‖x - z‖ ^ 2 + ‖z‖ ^ 2 ∧ ‖z‖ ^ 2 = ∑ i ∈ Z, ‖⟪u i, x⟫_ℂ‖ ^ 2 := by
  intro z
  have hz : ∀ j, ⟪u j, z⟫_ℂ = if j ∈ Z then ⟪u j, x⟫_ℂ else 0 := inner_blockSum u Z x
  have hy : ∀ j, ⟪u j, x - z⟫_ℂ = if j ∈ Z then 0 else ⟪u j, x⟫_ℂ := by
    intro j; rw [inner_sub_right, hz]; split_ifs <;> simp
  refine ⟨hy, ?_, ?_⟩
  · have horth : ⟪x - z, z⟫_ℂ = 0 := by
      rw [← u.sum_inner_mul_inner]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [← inner_conj_symm, hy, hz]; split_ifs <;> simp
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x - z) z horth
    rw [sub_add_cancel] at this
    rw [sq, sq, sq]; exact this
  · rw [← u.sum_sq_norm_inner_right z]
    simp_rw [hz]
    rw [← Finset.sum_subset (Finset.subset_univ Z) (fun j _ hj => by simp [hj])]
    exact Finset.sum_congr rfl fun j hj => by simp [hj]

lemma amgm_aux {g h M X Y : ℝ} (hg : 0 < g) :
    -(h ^ 2 * M ^ 2 / (4 * g)) * X ^ 2 ≤ g * Y ^ 2 - h * M * Y * X := by
  have : g * Y ^ 2 - h * M * Y * X + h ^ 2 * M ^ 2 / (4 * g) * X ^ 2 =
      (2 * g * Y - h * M * X) ^ 2 / (4 * g) := by field_simp; ring
  have h2 : 0 ≤ (2 * g * Y - h * M * X) ^ 2 / (4 * g) := by positivity
  linarith

omit [FiniteDimensional ℂ F] in
/-- The lower quadratic estimate behind the first-order perturbation formula. -/
lemma quad_lower {T₀ D R : F →L[ℂ] F} (hT₀ : (T₀ : F →ₗ[ℂ] F).IsSymmetric)
    (u : OrthonormalBasis (Fin n) ℂ F) (ν : Fin n → ℝ) (hu1 : ∀ j, T₀ (u j) = (ν j : ℂ) • u j)
    (Z : Finset (Fin n)) {νk dk g h δ : ℝ} (hg : 0 < g) (hh : 0 ≤ h) (hR : ‖R‖ ≤ δ * h)
    (hZν : ∀ j ∈ Z, ν j = νk) (hZoff : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j → ⟪u i, D (u j)⟫_ℂ = 0)
    (hZd : ∀ j ∈ Z, dk ≤ RCLike.re ⟪u j, D (u j)⟫_ℂ) (x : F)
    (hx : ∀ j ∉ Z, ⟪u j, x⟫_ℂ ≠ 0 → νk + g ≤ ν j) :
    (νk + h * dk - δ * h - h ^ 2 * (|dk| + 3 * ‖D‖) ^ 2 / (4 * g)) * ‖x‖ ^ 2 ≤
      RCLike.re ⟪x, (T₀ + (h : ℂ) • D + R) x⟫_ℂ := by
  classical
  obtain ⟨hy, hnorm, hznorm⟩ := block_split u Z x
  set z := ∑ i ∈ Z, ⟪u i, x⟫_ℂ • u i
  set y := x - z
  have hxyz : x = y + z := by simp [y]
  have hT : νk * ‖x‖ ^ 2 + g * ‖y‖ ^ 2 ≤ RCLike.re ⟪x, T₀ x⟫_ℂ := by
    rw [show RCLike.re ⟪x, T₀ x⟫_ℂ = RCLike.re ⟪x, (T₀ : F →ₗ[ℂ] F) x⟫_ℂ from rfl,
      re_inner_eq_sum_of_eigenbasis hT₀ u ν hu1 x, ← u.sum_sq_norm_inner_right x,
      ← u.sum_sq_norm_inner_right y, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [hy j]
    by_cases hj : j ∈ Z
    · simp [hj, hZν j hj]
    · simp only [hj, if_false]
      by_cases hc : ⟪u j, x⟫_ℂ = 0
      · simp [hc]
      · have := hx j hj hc
        nlinarith [sq_nonneg ‖⟪u j, x⟫_ℂ‖]
  have hDz : dk * ‖z‖ ^ 2 ≤ RCLike.re ⟪z, D z⟫_ℂ := by
    rw [re_inner_blockSum u D Z _ hZoff, hznorm, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hZd j hj) (by positivity)
  have hy_le : ‖y‖ ≤ ‖x‖ := by
    have : ‖y‖ ^ 2 ≤ ‖x‖ ^ 2 := by rw [hnorm]; nlinarith [sq_nonneg ‖z‖]
    nlinarith [norm_nonneg y, norm_nonneg x]
  have hz_le : ‖z‖ ≤ ‖x‖ := by
    have : ‖z‖ ^ 2 ≤ ‖x‖ ^ 2 := by rw [hnorm]; nlinarith [sq_nonneg ‖y‖]
    nlinarith [norm_nonneg z, norm_nonneg x]
  have hD : RCLike.re ⟪z, D z⟫_ℂ - 3 * ‖D‖ * ‖y‖ * ‖x‖ ≤ RCLike.re ⟪x, D x⟫_ℂ := by
    have e : RCLike.re ⟪x, D x⟫_ℂ = RCLike.re ⟪z, D z⟫_ℂ + RCLike.re ⟪y, D y⟫_ℂ +
        RCLike.re ⟪y, D z⟫_ℂ + RCLike.re ⟪z, D y⟫_ℂ := by
      rw [hxyz]; simp only [map_add, inner_add_left, inner_add_right]; simp; ring
    have h1 := abs_re_inner_le D y y
    have h2 := abs_re_inner_le D y z
    have h3 := abs_re_inner_le D z y
    have hDn := norm_nonneg D
    have hyn := norm_nonneg y
    have b1 : ‖D‖ * ‖y‖ * ‖y‖ ≤ ‖D‖ * ‖y‖ * ‖x‖ :=
      mul_le_mul_of_nonneg_left hy_le (by positivity)
    have b2 : ‖D‖ * ‖y‖ * ‖z‖ ≤ ‖D‖ * ‖y‖ * ‖x‖ :=
      mul_le_mul_of_nonneg_left hz_le (by positivity)
    have b3 : ‖D‖ * ‖z‖ * ‖y‖ ≤ ‖D‖ * ‖y‖ * ‖x‖ := by nlinarith
    rw [e]
    linarith [neg_abs_le (RCLike.re ⟪y, D y⟫_ℂ), neg_abs_le (RCLike.re ⟪y, D z⟫_ℂ),
      neg_abs_le (RCLike.re ⟪z, D y⟫_ℂ)]
  have hRx : -(δ * h * ‖x‖ ^ 2) ≤ RCLike.re ⟪x, R x⟫_ℂ := by
    have := abs_re_inner_le R x x
    have : ‖R‖ * ‖x‖ * ‖x‖ ≤ δ * h * ‖x‖ ^ 2 := by
      rw [mul_assoc, ← sq]; exact mul_le_mul_of_nonneg_right hR (by positivity)
    linarith [neg_abs_le (RCLike.re ⟪x, R x⟫_ℂ)]
  have e : RCLike.re ⟪x, (T₀ + (h : ℂ) • D + R) x⟫_ℂ =
      RCLike.re ⟪x, T₀ x⟫_ℂ + h * RCLike.re ⟪x, D x⟫_ℂ + RCLike.re ⟪x, R x⟫_ℂ := by
    simp
  rw [e]
  have hz2 : ‖z‖ ^ 2 = ‖x‖ ^ 2 - ‖y‖ ^ 2 := by linarith
  have hdk : -(|dk| * ‖y‖ * ‖x‖) ≤ -(dk * ‖y‖ ^ 2) := by
    have : dk * ‖y‖ ^ 2 ≤ |dk| * ‖y‖ * ‖x‖ := by
      calc dk * ‖y‖ ^ 2 ≤ |dk| * ‖y‖ ^ 2 := by
            exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ = |dk| * ‖y‖ * ‖y‖ := by ring
        _ ≤ |dk| * ‖y‖ * ‖x‖ := mul_le_mul_of_nonneg_left hy_le (by positivity)
    linarith
  have ham := amgm_aux (h := h) (M := |dk| + 3 * ‖D‖) (X := ‖x‖) (Y := ‖y‖) hg
  have hhD := mul_le_mul_of_nonneg_left hD hh
  have hhDz := mul_le_mul_of_nonneg_left hDz hh
  rw [hz2] at hhDz
  have hhk := mul_le_mul_of_nonneg_left hdk hh
  nlinarith

omit [FiniteDimensional ℂ F] in
/-- The upper quadratic estimate, deduced from `quad_lower` by changing signs. -/
lemma quad_upper {T₀ D R : F →L[ℂ] F} (hT₀ : (T₀ : F →ₗ[ℂ] F).IsSymmetric)
    (u : OrthonormalBasis (Fin n) ℂ F) (ν : Fin n → ℝ) (hu1 : ∀ j, T₀ (u j) = (ν j : ℂ) • u j)
    (Z : Finset (Fin n)) {νk dk g h δ : ℝ} (hg : 0 < g) (hh : 0 ≤ h) (hR : ‖R‖ ≤ δ * h)
    (hZν : ∀ j ∈ Z, ν j = νk) (hZoff : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j → ⟪u i, D (u j)⟫_ℂ = 0)
    (hZd : ∀ j ∈ Z, RCLike.re ⟪u j, D (u j)⟫_ℂ ≤ dk) (x : F)
    (hx : ∀ j ∉ Z, ⟪u j, x⟫_ℂ ≠ 0 → ν j ≤ νk - g) :
    RCLike.re ⟪x, (T₀ + (h : ℂ) • D + R) x⟫_ℂ ≤
      (νk + h * dk + δ * h + h ^ 2 * (|dk| + 3 * ‖D‖) ^ 2 / (4 * g)) * ‖x‖ ^ 2 := by
  have hT' : ((-T₀ : F →L[ℂ] F) : F →ₗ[ℂ] F).IsSymmetric := by
    intro a b
    have := hT₀ a b
    simp only [ContinuousLinearMap.coe_coe] at this
    simp [inner_neg_left, inner_neg_right, this]
  have key := quad_lower (D := -D) (R := -R) hT' u (fun j => -ν j)
    (fun j => by simp [hu1 j, neg_smul]) Z (νk := -νk) (dk := -dk) (δ := δ) hg hh
    (by rwa [norm_neg]) (fun j hj => by simp [hZν j hj])
    (fun i hi j hj hij => by simp [hZoff i hi j hj hij])
    (fun j hj => by simp only [ContinuousLinearMap.neg_apply, inner_neg_right, map_neg]
                    linarith [hZd j hj]) x
    (fun j hj hc => by have := hx j hj hc; linarith)
  have e : (-T₀ + (h : ℂ) • -D + -R : F →L[ℂ] F) = -(T₀ + (h : ℂ) • D + R) := by
    rw [smul_neg]; abel
  rw [e, ContinuousLinearMap.neg_apply, inner_neg_right, map_neg, norm_neg, abs_neg] at key
  linarith

/-- **First-order perturbation of sorted eigenvalues.** If `T(t)` is a family of symmetric
operators with right derivative `D` at `t₀` and `u` is an eigenbasis of `T(t₀)` adapted to `D`
(as produced by `exists_adapted_eigenbasis`), then the `k`-th sorted eigenvalue of `T(t)` has
right derivative `re ⟪u k, D (u k)⟫` at `t₀`. -/
theorem hasDerivWithinAt_eigenvalues {T : ℝ → F →L[ℂ] F}
    (hT : ∀ t, (T t : F →ₗ[ℂ] F).IsSymmetric) {D : F →L[ℂ] F} {t₀ : ℝ}
    (hder : HasDerivWithinAt T D (Ici t₀) t₀) (hn : finrank ℂ F = n)
    (u : OrthonormalBasis (Fin n) ℂ F)
    (hu1 : ∀ k, T t₀ (u k) = ((hT t₀).eigenvalues hn k : ℂ) • u k)
    (hu2 : ∀ j k, (hT t₀).eigenvalues hn j = (hT t₀).eigenvalues hn k → j ≠ k →
      ⟪u j, D (u k)⟫_ℂ = 0)
    (hu3 : ∀ j k, (hT t₀).eigenvalues hn j = (hT t₀).eigenvalues hn k → j ≤ k →
      RCLike.re ⟪u k, D (u k)⟫_ℂ ≤ RCLike.re ⟪u j, D (u j)⟫_ℂ) (k : Fin n) :
    HasDerivWithinAt (fun t => (hT t).eigenvalues hn k) (RCLike.re ⟪u k, D (u k)⟫_ℂ)
      (Ici t₀) t₀ := by
  classical
  set ν := (hT t₀).eigenvalues hn with hν
  set dk := RCLike.re ⟪u k, D (u k)⟫_ℂ
  obtain ⟨g, hg, hgap⟩ := exists_gap ν
  set M := |dk| + 3 * ‖D‖
  rw [hasDerivWithinAt_iff_isLittleO]
  refine Asymptotics.IsLittleO.of_bound fun ε hε => ?_
  have hb := (hasDerivWithinAt_iff_isLittleO.mp hder).bound (half_pos hε)
  set η : ℝ := 2 * g * ε / (M ^ 2 + 1)
  have hη : 0 < η := by positivity
  have hnear : ∀ᶠ t in 𝓝[Ici t₀] t₀, t - t₀ < η := by
    have : ∀ᶠ t in 𝓝 t₀, t - t₀ < η := by
      have := (continuous_sub_right t₀).tendsto t₀
      simp only [sub_self] at this
      exact this (Iio_mem_nhds hη)
    exact nhdsWithin_le_nhds this
  filter_upwards [hb, hnear, self_mem_nhdsWithin] with t ht htη ht₀
  have hh : 0 ≤ t - t₀ := sub_nonneg.mpr ht₀
  set h := t - t₀
  set R := T t - T t₀ - h • D
  have hR : ‖R‖ ≤ ε / 2 * h := by
    have := ht; rw [Real.norm_eq_abs, abs_of_nonneg hh] at this; exact this
  have hTt : T t = T t₀ + (h : ℂ) • D + R := by
    simp only [R]; rw [← Complex.coe_smul]; abel
  have hquad : h ^ 2 * M ^ 2 / (4 * g) ≤ ε / 2 * h := by
    have h1 : h * M ^ 2 ≤ 2 * g * ε := by
      have : h * (M ^ 2 + 1) ≤ 2 * g * ε := by
        have := htη.le
        rwa [le_div_iff₀ (by positivity)] at this
      nlinarith [sq_nonneg M]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hsym := hT t₀
  -- lower bound
  have hlow : ν k + h * dk - ε / 2 * h - h ^ 2 * M ^ 2 / (4 * g) ≤
      (hT t).eigenvalues hn k := by
    refine le_eigenvalues_of_subspace (hT t) hn k (obSpan u (Finset.Iic k))
      (by rw [finrank_obSpan, Fin.card_Iic]; omega) _ fun x hx => ?_
    have := quad_lower hsym u ν hu1 ((Finset.Iic k).filter fun j => ν j = ν k)
      (dk := dk) hg hh hR (fun j hj => (Finset.mem_filter.mp hj).2)
      (fun i hi j hj hij => hu2 i j (by rw [(Finset.mem_filter.mp hi).2,
        (Finset.mem_filter.mp hj).2]) hij)
      (fun j hj => hu3 j k (Finset.mem_filter.mp hj).2
        (Finset.mem_Iic.mp (Finset.mem_filter.mp hj).1)) x
      (fun j hj hc => by
        have hjk : j ≤ k := by
          by_contra hjk
          exact hc (inner_eq_zero_of_mem_obSpan u _ hx (by simpa using hjk))
        have hne : ν j ≠ ν k := fun he => hj (by simp [hjk, he])
        have h1 := (hT t₀).eigenvalues_antitone hn hjk
        have h2 := hgap j k hne
        rw [abs_of_pos (lt_of_le_of_ne h1 (Ne.symm hne) |> sub_pos.mpr)] at h2
        linarith)
    rw [← hTt] at this
    exact this
  -- upper bound
  have hup : (hT t).eigenvalues hn k ≤
      ν k + h * dk + ε / 2 * h + h ^ 2 * M ^ 2 / (4 * g) := by
    refine eigenvalues_le_of_subspace (hT t) hn k (obSpan u (Finset.Ici k))
      (by rw [finrank_obSpan, Fin.card_Ici]) _ fun x hx => ?_
    have := quad_upper hsym u ν hu1 ((Finset.Ici k).filter fun j => ν j = ν k)
      (dk := dk) hg hh hR (fun j hj => (Finset.mem_filter.mp hj).2)
      (fun i hi j hj hij => hu2 i j (by rw [(Finset.mem_filter.mp hi).2,
        (Finset.mem_filter.mp hj).2]) hij)
      (fun j hj => hu3 k j (Finset.mem_filter.mp hj).2.symm
        (Finset.mem_Ici.mp (Finset.mem_filter.mp hj).1)) x
      (fun j hj hc => by
        have hjk : k ≤ j := by
          by_contra hjk
          exact hc (inner_eq_zero_of_mem_obSpan u _ hx (by simpa using hjk))
        have hne : ν j ≠ ν k := fun he => hj (by simp [hjk, he])
        have h1 := (hT t₀).eigenvalues_antitone hn hjk
        have h2 := hgap j k hne
        rw [abs_of_neg (lt_of_le_of_ne h1 hne |> sub_neg.mpr)] at h2
        linarith)
    rw [← hTt] at this
    exact this
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hh, smul_eq_mul, abs_le]
  constructor <;> nlinarith

end Perturbation

end

section

/-! ## The Cayley transform of a unitary operator -/

open scoped InnerProductSpace
open Complex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The Cayley transform `i (1 + W) (1 - W)⁻¹`. -/
def cayley (W : E →L[ℂ] E) : E →L[ℂ] E :=
  I • ((1 + W) * Ring.inverse (1 - W))

section

variable {W : E →L[ℂ] E}

omit [CompleteSpace E] in
lemma sub_mul_inverse (hW : IsUnit (1 - W)) : (1 - W) * Ring.inverse (1 - W) = 1 :=
  Ring.mul_inverse_cancel _ hW

omit [CompleteSpace E] in
lemma inverse_mul_sub (hW : IsUnit (1 - W)) : Ring.inverse (1 - W) * (1 - W) = 1 :=
  Ring.inverse_mul_cancel _ hW

lemma commute_of_inv {R : Type*} [Ring R] {W X : R} (h1 : (1 - W) * X = 1)
    (h2 : X * (1 - W) = 1) : W * X = X * W := by
  calc W * X = X * (1 - W) * (W * X) := by rw [h2, one_mul]
    _ = X * ((1 - W) * W) * X := by noncomm_ring
    _ = X * (W * (1 - W)) * X := by noncomm_ring
    _ = X * W * ((1 - W) * X) := by noncomm_ring
    _ = X * W := by rw [h1, mul_one]

omit [CompleteSpace E] in
lemma commute_inverse (hW : IsUnit (1 - W)) : W * Ring.inverse (1 - W) =
    Ring.inverse (1 - W) * W :=
  commute_of_inv (sub_mul_inverse hW) (inverse_mul_sub hW)

lemma star_of_inv {R : Type*} [Ring R] [StarRing R] {W X : R} (hWW : star W * W = 1)
    (h1 : (1 - W) * X = 1) (h2 : X * (1 - W) = 1) : star X = -(X * W) := by
  have hc := commute_of_inv h1 h2
  have hl : star X * (1 - star W) = 1 := by
    have := congrArg star h1
    rw [star_mul, star_sub, star_one] at this
    exact this
  have hr : (1 - star W) * -(X * W) = 1 := by
    calc (1 - star W) * -(X * W) = -(X * W) + star W * (W * X) := by rw [hc]; noncomm_ring
      _ = -(X * W) + X := by rw [← mul_assoc, hWW, one_mul]
      _ = X * (1 - W) := by noncomm_ring
      _ = 1 := h2
  calc star X = star X * ((1 - star W) * -(X * W)) := by rw [hr, mul_one]
    _ = (star X * (1 - star W)) * -(X * W) := by rw [mul_assoc]
    _ = -(X * W) := by rw [hl, one_mul]

lemma star_inverse (hWu : W ∈ unitary (E →L[ℂ] E)) (hW : IsUnit (1 - W)) :
    star (Ring.inverse (1 - W)) = -(Ring.inverse (1 - W) * W) :=
  star_of_inv (Unitary.star_mul_self_of_mem hWu) (sub_mul_inverse hW) (inverse_mul_sub hW)

/-- The Cayley transform of a unitary operator is self-adjoint. -/
theorem isSelfAdjoint_cayley (hWu : W ∈ unitary (E →L[ℂ] E)) (hW : IsUnit (1 - W)) :
    IsSelfAdjoint (cayley W) := by
  set X := Ring.inverse (1 - W)
  have hc := commute_inverse hW
  have hs := star_inverse hWu hW
  have hWW : W * star W = 1 := Unitary.mul_star_self_of_mem hWu
  unfold cayley
  show star (I • ((1 + W) * X)) = I • ((1 + W) * X)
  rw [star_smul, star_mul, hs, star_add, star_one]
  have : (starRingEnd ℂ) I = -I := Complex.conj_I
  simp only [RCLike.star_def, this]
  have e : -(X * W) * (1 + star W) = -(X * (W + W * star W)) := by noncomm_ring
  rw [e, hWW, neg_smul, smul_neg, neg_neg]
  congr 1
  calc X * (W + 1) = X * W + X := by noncomm_ring
    _ = W * X + X := by rw [hc]
    _ = (1 + W) * X := by noncomm_ring

omit [CompleteSpace E] in
lemma cayley_mul_sub (hW : IsUnit (1 - W)) : (1 - W) * cayley W = I • (1 + W) := by
  have hc := commute_inverse hW
  unfold cayley
  rw [mul_smul_comm]
  congr 1
  calc (1 - W) * ((1 + W) * Ring.inverse (1 - W)) =
      (1 + W) * ((1 - W) * Ring.inverse (1 - W)) := by
        have : (1 - W) * (1 + W) = (1 + W) * (1 - W) := by noncomm_ring
        rw [← mul_assoc, this, mul_assoc]
    _ = 1 + W := by rw [sub_mul_inverse hW, mul_one]

/-- The unit-circle point `exp(i (2 arctan ν - π)) = (ν - i)/(ν + i)`. -/
lemma add_I_mul_exp (ν : ℝ) :
    ((ν : ℂ) + I) * exp (((2 * Real.arctan ν - Real.pi : ℝ) : ℂ) * I) = (ν : ℂ) - I := by
  rw [exp_mul_I]
  have hc : Real.cos (2 * Real.arctan ν - Real.pi) = (ν ^ 2 - 1) / (1 + ν ^ 2) := by
    rw [Real.cos_sub_pi, Real.cos_two_mul, Real.cos_arctan]
    have h1 : 0 < 1 + ν ^ 2 := by positivity
    rw [div_pow, one_pow, Real.sq_sqrt h1.le]
    field_simp; ring
  have hs : Real.sin (2 * Real.arctan ν - Real.pi) = -(2 * ν) / (1 + ν ^ 2) := by
    rw [Real.sin_sub_pi, Real.sin_two_mul, Real.cos_arctan, Real.sin_arctan]
    have h1 : 0 < 1 + ν ^ 2 := by positivity
    have h2 := Real.sq_sqrt h1.le
    have h3 : Real.sqrt (1 + ν ^ 2) ≠ 0 := by positivity
    field_simp
    rw [h2]
  rw [← ofReal_cos, ← ofReal_sin, hc, hs]
  have h1 : (1 + (ν : ℂ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 1 + ν ^ 2 := by positivity
    exact_mod_cast this.ne'
  push_cast
  field_simp
  ring_nf
  rw [I_sq]
  ring

omit [CompleteSpace E] in
/-- Eigenvectors of the Cayley transform are eigenvectors of `W`. -/
theorem apply_eq_of_cayley_apply (hW : IsUnit (1 - W)) {x : E} {ν : ℝ}
    (hx : cayley W x = (ν : ℂ) • x) :
    W x = exp (((2 * Real.arctan ν - Real.pi : ℝ) : ℂ) * I) • x := by
  have h := congrArg (fun T : E →L[ℂ] E => T x) (cayley_mul_sub hW)
  simp only [ContinuousLinearMap.mul_apply, hx, map_smul, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply] at h
  -- `ν (x - W x) = i (x + W x)`, so `(ν + i) W x = (ν - i) x`
  have hνI : (ν : ℂ) + I ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
  have key : ((ν : ℂ) + I) • W x = ((ν : ℂ) - I) • x := by
    rw [smul_sub, smul_add] at h
    rw [add_smul, sub_smul]
    linear_combination (norm := module) -h
  have e := add_I_mul_exp ν
  set c := exp (((2 * Real.arctan ν - Real.pi : ℝ) : ℂ) * I)
  calc W x = ((ν : ℂ) + I)⁻¹ • (((ν : ℂ) + I) • W x) := by
        rw [smul_smul, inv_mul_cancel₀ hνI, one_smul]
    _ = ((ν : ℂ) + I)⁻¹ • (((ν : ℂ) + I) * c) • x := by rw [key, e]
    _ = c • x := by rw [smul_smul, ← mul_assoc, inv_mul_cancel₀ hνI, one_mul]

/-- Derivative of `t ↦ (1 - W t)⁻¹`. -/
lemma hasDerivWithinAt_inverse_one_sub {W : ℝ → E →L[ℂ] E} {W' : E →L[ℂ] E} {s : Set ℝ}
    {t : ℝ} (h : HasDerivWithinAt W W' s t) (hu : IsUnit (1 - W t)) :
    HasDerivWithinAt (fun τ => Ring.inverse (1 - W τ))
      (Ring.inverse (1 - W t) * W' * Ring.inverse (1 - W t)) s t := by
  obtain ⟨u, hu⟩ := hu
  have h1 : HasDerivWithinAt (fun τ => 1 - W τ) (-W') s t := by
    simpa using h.const_sub 1
  have h3 : HasFDerivAt Ring.inverse (-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℂ] E)
      (↑u⁻¹ : E →L[ℂ] E) ↑u⁻¹) (1 - W t) := hu ▸ hasFDerivAt_ringInverse (𝕜 := ℝ) u
  have h2 := h3.comp_hasDerivWithinAt t h1
  convert h2 using 1
  · funext τ
    rfl
  rw [← hu, Ring.inverse_unit]
  simp [ContinuousLinearMap.mulLeftRight_apply]

/-- Derivative of the Cayley transform along a positive path `W' = i W A`:
`C' = 2 X* A X` with `X = (1 - W)⁻¹`. -/
theorem hasDerivWithinAt_cayley {W A : ℝ → E →L[ℂ] E} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt W (I • (W t * A t)) s t) (hWu : W t ∈ unitary (E →L[ℂ] E))
    (hu : IsUnit (1 - W t)) :
    HasDerivWithinAt (fun τ => cayley (W τ))
      ((2 : ℂ) • (star (Ring.inverse (1 - W t)) * A t * Ring.inverse (1 - W t))) s t := by
  have hX := hasDerivWithinAt_inverse_one_sub h hu
  have h1 : HasDerivWithinAt (fun τ => 1 + W τ) (I • (W t * A t)) s t := by
    simpa using h.const_add 1
  have h2 := (h1.mul hX).const_smul I
  unfold cayley
  convert h2 using 1
  rw [star_inverse hWu hu]
  have hc := commute_inverse hu
  have h1' := sub_mul_inverse hu
  generalize Ring.inverse (1 - W t) = X at hc h1' ⊢
  generalize W t = w at hc h1' ⊢
  generalize A t = a
  have key : (w * a) * X + (1 + w) * (X * (w * a) * X) = (2 : ℂ) • (X * (w * a) * X) := by
    have e2' : (w * a) * X = (1 - w) * X * ((w * a) * X) := by rw [h1', one_mul]
    rw [two_smul]
    conv_lhs => rw [e2']
    noncomm_ring
  rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm, ← smul_add, key,
    smul_smul, smul_smul, I_mul_I]
  simp only [mul_assoc, neg_mul]
  module

/-- Along a positive path, the derivative of a Cayley eigenvalue `ν`, converted to the phase
variable `2 arctan ν`, is `⟪u, A u⟫`. -/
theorem re_inner_cayley_deriv (hW : IsUnit (1 - W))
    (A : E →L[ℂ] E) {u : E} {ν : ℝ} (hu : cayley W u = (ν : ℂ) • u) :
    2 / (1 + ν ^ 2) * RCLike.re ⟪u, ((2 : ℂ) • (star (Ring.inverse (1 - W)) * A *
      Ring.inverse (1 - W))) u⟫_ℂ = RCLike.re ⟪u, A u⟫_ℂ := by
  set X := Ring.inverse (1 - W)
  have hWx := apply_eq_of_cayley_apply hW hu
  set ω := exp (((2 * Real.arctan ν - Real.pi : ℝ) : ℂ) * I)
  have hω := add_I_mul_exp ν
  set c : ℂ := (1 - (ν : ℂ) * I) / 2
  have hc : c * (1 - ω) = 1 := by
    simp only [c]
    linear_combination (I / 2) * hω - ((1 + ω) / 2) * I_sq
  have hXu : X u = c • u := by
    have h1 : (1 - W) (c • u) = u := by
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, map_smul, hWx]
      rw [show c • (u - ω • u) = (c * (1 - ω)) • u by module, hc, one_smul]
    calc X u = X ((1 - W) (c • u)) := by rw [h1]
      _ = c • u := by
        rw [← ContinuousLinearMap.mul_apply, inverse_mul_sub hW, ContinuousLinearMap.one_apply]
  have hcn : (starRingEnd ℂ) c * c = (((1 + ν ^ 2) / 4 : ℝ) : ℂ) := by
    simp only [c, map_div₀, map_sub, map_one, map_mul, Complex.conj_ofReal, Complex.conj_I,
      map_ofNat]
    push_cast
    linear_combination (-(ν : ℂ) ^ 2 / 4) * I_sq
  have e : ⟪u, ((2 : ℂ) • (star X * A * X)) u⟫_ℂ = 2 * ((((1 + ν ^ 2) / 4 : ℝ) : ℂ) *
      ⟪u, A u⟫_ℂ) := by
    rw [ContinuousLinearMap.smul_apply, inner_smul_right, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, hXu, map_smul, inner_smul_left, inner_smul_right,
      ← hcn]
    ring
  rw [e]
  have h1 : (0 : ℝ) < 1 + ν ^ 2 := by positivity
  simp only [RCLike.re_to_complex]
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
  field_simp
  rw [Complex.re_ofReal_mul]
  ring

end

end

section

/-! ## Eigenphases of a positive unitary path on a window (finite dimensions) -/

open scoped InnerProductSpace
open Module Filter Topology Set Complex

section RealAnalysis

lemma sub_le_integral_of_rderiv {f f' g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (hg : ContinuousOn g (Icc a b)) (hle : ∀ x ∈ Ico a b, f' x ≤ g x) :
    f b - f a ≤ ∫ t in a..b, g t := by
  set G : ℝ → ℝ := fun t => g (projIcc a b hab t)
  have hGc : Continuous G := hg.comp_continuous (continuous_subtype_val.comp continuous_projIcc) (fun t => Subtype.mem _)
  have hGeq : ∀ t ∈ Icc a b, G t = g t := fun t ht => by simp [G, projIcc_of_mem hab ht]
  set B : ℝ → ℝ := fun t => f a + ∫ τ in a..t, G τ
  have hB : ∀ t, HasDerivAt B (G t) t := fun t =>
    (intervalIntegral.integral_hasDerivAt_right (hGc.intervalIntegrable _ _)
      (hGc.stronglyMeasurableAtFilter _ _) hGc.continuousAt).const_add _
  have key := image_le_of_deriv_right_le_deriv_boundary hf hf' (B := B) (B' := G)
    (by simp [B]) (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt)
    (fun t ht => by rw [hGeq t (Ico_subset_Icc_self ht)]; exact hle t ht)
    (right_mem_Icc.2 hab)
  have : ∫ τ in a..b, G τ = ∫ τ in a..b, g τ :=
    intervalIntegral.integral_congr fun t ht => hGeq t (by rwa [uIcc_of_le hab] at ht)
  simp only [B] at key
  linarith

lemma monotoneOn_of_rderiv_nonneg {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (hpos : ∀ x ∈ Ico a b, 0 ≤ f' x) : MonotoneOn f (Icc a b) := by
  intro x hx y hy hxy
  have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
  have := sub_le_integral_of_rderiv (f := fun t => -f t) (f' := fun t => -f' t) (g := fun _ => 0)
    hxy (hf.mono hsub).neg
    (fun t ht => (hf' t ⟨hx.1.trans ht.1, ht.2.trans_le hy.2⟩).neg) continuousOn_const
    (fun t ht => by simpa using hpos t ⟨hx.1.trans ht.1, ht.2.trans_le hy.2⟩)
  simp at this
  linarith

lemma strictMonoOn_of_rderiv_pos {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (hnn : ∀ x ∈ Ico a b, 0 ≤ f' x) (hpos : ∀ x ∈ Ioo a b, 0 < f' x) :
    StrictMonoOn f (Icc a b) := by
  have hmono := monotoneOn_of_rderiv_nonneg hf hf' hnn
  intro x hx y hy hxy
  refine lt_of_le_of_ne (hmono hx hy hxy.le) fun heq => ?_
  set z := (x + y) / 2
  have hz : z ∈ Ioo x y := ⟨by simp only [z]; linarith, by simp only [z]; linarith⟩
  have hzab : z ∈ Ioo a b := ⟨hx.1.trans_lt hz.1, hz.2.trans_le hy.2⟩
  have hconst : ∀ t ∈ Icc x y, f t = f x := fun t ht =>
    le_antisymm (heq ▸ hmono ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩ hy ht.2)
      (hmono hx ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩ ht.1)
  have h0 : HasDerivWithinAt f 0 (Ici z) z := by
    have hc : HasDerivWithinAt (fun _ => f x) 0 (Ici z) z := hasDerivWithinAt_const _ _ _
    refine hc.congr_of_eventuallyEq ?_ (hconst z (Ioo_subset_Icc_self hz))
    have : Icc z y ∈ 𝓝[Ici z] z := Icc_mem_nhdsGE hz.2
    filter_upwards [this] with t ht
    exact hconst t ⟨hz.1.le.trans ht.1, ht.2⟩
  have := (uniqueDiffWithinAt_Ici z).eq_deriv _ (hf' z (Ioo_subset_Ico_self hzab)) h0
  exact (hpos z hzab).ne' this

end RealAnalysis

section Window

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

lemma star_exp_neg_mul_I (β : ℝ) : star (exp (-(β * I))) * exp (-(β * I)) = 1 := by
  have : star (exp (-(β * I))) = exp (β * I) := by
    rw [Complex.star_def, ← Complex.exp_conj]; simp [Complex.conj_ofReal]
  rw [this, ← Complex.exp_add]; simp

lemma smul_mem_unitary {c : ℂ} (hc : star c * c = 1) {V : F →L[ℂ] F}
    (hV : V ∈ unitary (F →L[ℂ] F)) : c • V ∈ unitary (F →L[ℂ] F) := by
  have hc' : c * star c = 1 := by rw [mul_comm]; exact hc
  rw [Unitary.mem_iff] at hV ⊢
  refine ⟨?_, ?_⟩
  · rw [star_smul, smul_mul_smul_comm, hV.1, hc, one_smul]
  · rw [star_smul, smul_mul_smul_comm, hV.2, hc', one_smul]

lemma continuous_cayley_comp {W : ℝ → F →L[ℂ] F} (hW : Continuous W)
    (hu : ∀ t, IsUnit (1 - W t)) : Continuous fun t => cayley (W t) := by
  have hinv : Continuous fun t => Ring.inverse (1 - W t) := by
    refine continuous_iff_continuousAt.2 fun t => ?_
    obtain ⟨u, hu⟩ := hu t
    exact ContinuousAt.comp (f := fun t => 1 - W t)
      (show ContinuousAt Ring.inverse (1 - W t) from hu ▸ NormedRing.inverse_continuousAt u)
      (show ContinuousAt (fun t : ℝ => (1 : F →L[ℂ] F) - W t) t from
        (continuous_const.sub hW).continuousAt)
  unfold cayley
  exact Continuous.const_smul
    (((continuous_const : Continuous (fun _ : ℝ => (1 : F →L[ℂ] F))).add hW).mul hinv)
    (Complex.I : ℂ)

/-- **Eigenphases on a window.** Let `V` be a unitary path on `[s₁, s₂]` with right derivative
`V' = i V A`, `A(t)` self-adjoint, such that `e^{iβ}` is never an eigenvalue of `V(t)`. Then there
are continuous functions `φ_k` such that `e^{i φ_k(t)}` are the eigenvalues of `V(t)` (with an
orthonormal eigenbasis) and `φ_k` has right derivative `re ⟪u_k, A(t) u_k⟫` for some orthonormal
basis `u`. -/
theorem phase_window {n : ℕ} (hn : finrank ℂ F = n) {V A : ℝ → F →L[ℂ] F} {s₁ s₂ β : ℝ}
    (hs : s₁ ≤ s₂)
    (hVu : ∀ t ∈ Icc s₁ s₂, V t ∈ unitary (F →L[ℂ] F))
    (hVc : ContinuousOn V (Icc s₁ s₂))
    (hVd : ∀ t ∈ Ico s₁ s₂, HasDerivWithinAt V (I • (V t * A t)) (Ici t) t)
    (hAs : ∀ t ∈ Ico s₁ s₂, IsSelfAdjoint (A t))
    (hβ : ∀ t ∈ Icc s₁ s₂, IsUnit (1 - exp (-(β * I)) • V t)) :
    ∃ φ : Fin n → ℝ → ℝ,
      (∀ k, Continuous (φ k)) ∧
      (∀ t ∈ Icc s₁ s₂, ∃ e : OrthonormalBasis (Fin n) ℂ F,
        ∀ k, V t (e k) = exp (φ k t * I) • e k) ∧
      (∀ t ∈ Ico s₁ s₂, ∃ u : OrthonormalBasis (Fin n) ℂ F,
        ∀ k, HasDerivWithinAt (φ k) (RCLike.re ⟪u k, A t (u k)⟫_ℂ) (Ici t) t) ∧
      (∀ k t, φ k t ∈ Ioo (β - 2 * Real.pi) β) := by
  classical
  set p : ℝ → ℝ := fun t => projIcc s₁ s₂ hs t with hpdef
  have hp : ∀ t, p t ∈ Icc s₁ s₂ := fun t => Subtype.mem _
  have hpeq : ∀ t ∈ Icc s₁ s₂, p t = t := fun t ht => by simp [p, projIcc_of_mem hs ht]
  set c : ℂ := exp (-(β * I)) with hcdef
  have hc : star c * c = 1 := star_exp_neg_mul_I β
  set W : ℝ → F →L[ℂ] F := fun t => c • V (p t) with hWdef
  have hWu : ∀ t, W t ∈ unitary (F →L[ℂ] F) := fun t => smul_mem_unitary hc (hVu _ (hp t))
  have hWi : ∀ t, IsUnit (1 - W t) := fun t => hβ _ (hp t)
  have hWc : Continuous W :=
    (hVc.comp_continuous (continuous_subtype_val.comp continuous_projIcc) hp).const_smul c
  set T : ℝ → F →L[ℂ] F := fun t => cayley (W t) with hTdef
  have hT : ∀ t, (T t : F →ₗ[ℂ] F).IsSymmetric := fun t =>
    (isSelfAdjoint_cayley (hWu t) (hWi t)).isSymmetric
  have hTc : Continuous T := continuous_cayley_comp hWc hWi
  set ν : Fin n → ℝ → ℝ := fun k t => (hT t).eigenvalues hn k with hνdef
  have hνc : ∀ k, Continuous (ν k) := by
    intro k
    refine continuous_iff_continuousAt.2 fun t => ?_
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun s => ‖T s - T t‖) (𝓝 t) (𝓝 0) := by
      rw [← tendsto_iff_norm_sub_tendsto_zero]; exact hTc.continuousAt
    refine squeeze_zero (fun _ => norm_nonneg _) (fun s => ?_) h0
    rw [Real.norm_eq_abs]
    exact abs_eigenvalues_sub_le (hT s) (hT t) hn k
  refine ⟨fun k t => β - Real.pi + 2 * Real.arctan (ν k t), fun k => ?_, ?_, ?_, fun k t => ?_⟩
  rotate_left 3
  · have h1 := Real.neg_pi_div_two_lt_arctan (ν k t)
    have h2 := Real.arctan_lt_pi_div_two (ν k t)
    constructor <;> linarith
  · exact continuous_const.add (continuous_const.mul (Real.continuous_arctan.comp (hνc k)))
  · intro t ht
    refine ⟨(hT t).eigenvectorBasis hn, fun k => ?_⟩
    have h1 := (hT t).apply_eigenvectorBasis hn k
    have h2 := apply_eq_of_cayley_apply (hWi t) h1
    have hV : V t = exp (β * I) • W t := by
      simp only [W, hpeq t ht, smul_smul, c, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero,
        one_smul]
    simp only
    rw [hV, ContinuousLinearMap.smul_apply, h2, smul_smul, ← Complex.exp_add]
    congr 1
    rw [← add_mul, ← Complex.ofReal_add]
    congr 2
    simp only [Algebra.algebraMap_self, RingHom.id_apply, ν]
    ring_nf
  · intro t ht
    have htI : t ∈ Icc s₁ s₂ := Ico_subset_Icc_self ht
    have hVd' : HasDerivWithinAt (fun τ => V (p τ)) (I • (V t * A t)) (Ici t) t := by
      refine (hVd t ht).congr_of_eventuallyEq ?_ (by simp only [hpeq t htI])
      filter_upwards [Icc_mem_nhdsGE ht.2] with τ hτ
      rw [hpeq τ ⟨ht.1.trans hτ.1, hτ.2⟩]
    have hWd : HasDerivWithinAt W (I • (W t * A t)) (Ici t) t := by
      have := hVd'.const_smul c
      convert this using 1
      simp only [W, hpeq t htI, smul_mul_assoc, smul_comm c I]
    have hTd := hasDerivWithinAt_cayley hWd (hWu t) (hWi t)
    set X := Ring.inverse (1 - W t)
    set D : F →L[ℂ] F := (2 : ℂ) • (star X * A t * X) with hD
    have hDs : (D : F →ₗ[ℂ] F).IsSymmetric := by
      have h1 : IsSelfAdjoint (star X * A t * X) := (hAs t ht).conjugate' X
      have : IsSelfAdjoint D := by
        rw [hD, two_smul]; exact h1.add h1
      exact this.isSymmetric
    obtain ⟨u, hu1, hu2, hu3⟩ := exists_adapted_eigenbasis (hT t) hn hDs
    refine ⟨u, fun k => ?_⟩
    have hνd := hasDerivWithinAt_eigenvalues hT hTd hn u hu1 hu2 hu3 k
    have harc := (((Real.hasDerivAt_arctan (ν k t)).comp_hasDerivWithinAt t hνd).const_mul
      2).const_add (β - Real.pi)
    convert harc using 1
    · funext x
      rfl
    have := re_inner_cayley_deriv (hWi t) (A t) (hu1 k)
    rw [← this]
    simp only [ν]
    ring

end Window

end

section

/-! ## Global eigenphase lifts of a positive unitary path (finite dimensions) -/

open scoped InnerProductSpace
open Module Filter Topology Set Complex

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- Two eigenbases of the same operator have the same eigenvalues up to a permutation. -/
lemma exists_perm_of_eigenbases {M : Type*} [AddCommGroup M] [Module ℂ M] [Module.Finite ℂ M]
    {n : ℕ} {V : M →ₗ[ℂ] M} (e e' : Module.Basis (Fin n) ℂ M) (z w : Fin n → ℂ)
    (he : ∀ k, V (e k) = z k • e k) (he' : ∀ k, V (e' k) = w k • e' k) :
    ∃ σ : Fin n ≃ Fin n, ∀ k, w (σ k) = z k := by
  classical
  have hroots : ∀ (b : Module.Basis (Fin n) ℂ M) (z : Fin n → ℂ), (∀ k, V (b k) = z k • b k) →
      V.charpoly.roots = Multiset.map z Finset.univ.val := by
    intro b z hb
    have hM : LinearMap.toMatrix b b V = Matrix.diagonal z := by
      ext i j
      rw [LinearMap.toMatrix_apply, hb, map_smul, Module.Basis.repr_self, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    have hf : (fun i => Polynomial.X - Polynomial.C (z i)) =
        (fun a => Polynomial.X - Polynomial.C a) ∘ z := rfl
    rw [← LinearMap.charpoly_toMatrix V b, hM, Matrix.charpoly_diagonal,
      Finset.prod_eq_multiset_prod, hf, ← Multiset.map_map (fun a => Polynomial.X - Polynomial.C a) z,
      Polynomial.roots_multiset_prod_X_sub_C]
  have hm := (hroots e z he).symm.trans (hroots e' w he')
  have h1 : ∀ (c : ℂ) (f : Fin n → ℂ), Fintype.card {a // f a = c} =
      (Multiset.filter (fun a => c = f a) Finset.univ.val).card := fun c f => by
    rw [Fintype.card_subtype]; simp_rw [eq_comm (b := c)]; rfl
  have hcard : ∀ c, Fintype.card {a // z a = c} = Fintype.card {b // w b = c} := by
    intro c
    have := congrArg (Multiset.count c) hm
    rw [Multiset.count_map, Multiset.count_map] at this
    rw [h1, h1, this]
  exact ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hcard c)),
    fun k => Equiv.ofFiberEquiv_map _ k⟩

/-- Every operator on a finite-dimensional space misses some point `e^{iβ}` of the unit circle
in its spectrum. -/
lemma exists_level_unit (U : F →L[ℂ] F) : ∃ β : ℝ, IsUnit (1 - exp (-(β * I)) • U) := by
  have hfin := Module.End.finite_hasEigenvalue (U : F →ₗ[ℂ] F)
  have hinj : InjOn (fun β : ℝ => exp (β * I)) (Icc 0 1) := by
    intro a ha b hb hab
    obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 hab
    have him := congrArg Complex.im hm
    simp at him
    have hpi := Real.pi_gt_three
    rcases lt_trichotomy m 0 with h | h | h
    · have : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.mpr h
      nlinarith [ha.1, hb.2]
    · subst h; simpa using him
    · have : (1 : ℝ) ≤ m := by exact_mod_cast h
      nlinarith [ha.2, hb.1]
  have hinf := (Set.Icc_infinite (zero_lt_one' ℝ)).image hinj
  obtain ⟨μ, ⟨β, hβ, rfl⟩, hnot⟩ := (hinf.diff hfin).nonempty
  refine ⟨β, ContinuousLinearMap.isUnit_iff_bijective.2 ?_⟩
  have hi : Function.Injective ((1 - exp (-(β * I)) • U : F →L[ℂ] F) : F →ₗ[ℂ] F) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    apply hnot
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := x) ⟨?_, hx0⟩
    rw [Module.End.mem_eigenspace_iff]
    have : x = exp (-(β * I)) • U x := by
      have := hx; simp at this; exact sub_eq_zero.1 this
    simp only [ContinuousLinearMap.coe_coe]
    calc U x = (exp (β * I) * exp (-(β * I))) • U x := by rw [← Complex.exp_add]; simp
      _ = exp (β * I) • x := by rw [mul_smul, ← this]
  exact ⟨hi, LinearMap.injective_iff_surjective.1 hi⟩

variable {n : ℕ}

/-- Global eigenphase lifts of `V` on `[0, s]`. -/
def IsPhaseLift (V A : ℝ → F →L[ℂ] F) (s : ℝ) (lam : Fin n → ℝ → ℝ) : Prop :=
  (∀ k, lam k 0 = 0) ∧ (∀ k, ContinuousOn (lam k) (Icc 0 s)) ∧
  (∀ t ∈ Icc 0 s, ∃ e : OrthonormalBasis (Fin n) ℂ F,
    ∀ k, V t (e k) = exp (lam k t * I) • e k) ∧
  (∀ t ∈ Ico 0 s, ∃ u : OrthonormalBasis (Fin n) ℂ F,
    ∀ k, HasDerivWithinAt (lam k) (RCLike.re ⟪u k, A t (u k)⟫_ℂ) (Ici t) t)

/-- Extending global lifts by window lifts. -/
lemma IsPhaseLift.extend {V A : ℝ → F →L[ℂ] F} {s s₂ : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ s₂)
    {lam : Fin n → ℝ → ℝ} (hl : IsPhaseLift V A s lam)
    {φ : Fin n → ℝ → ℝ} (hφc : ∀ k, Continuous (φ k))
    (hφe : ∀ t ∈ Icc s s₂, ∃ e : OrthonormalBasis (Fin n) ℂ F,
      ∀ k, V t (e k) = exp (φ k t * I) • e k)
    (hφd : ∀ t ∈ Ico s s₂, ∃ u : OrthonormalBasis (Fin n) ℂ F,
      ∀ k, HasDerivWithinAt (φ k) (RCLike.re ⟪u k, A t (u k)⟫_ℂ) (Ici t) t) :
    ∃ lam' : Fin n → ℝ → ℝ, IsPhaseLift V A s₂ lam' := by
  classical
  obtain ⟨hl0, hlc, hle, hld⟩ := hl
  obtain ⟨e, he⟩ := hle s ⟨hs0, le_rfl⟩
  obtain ⟨e', he'⟩ := hφe s ⟨le_rfl, hs⟩
  obtain ⟨σ, hσ⟩ := exists_perm_of_eigenbases (V := (V s : F →ₗ[ℂ] F)) e.toBasis e'.toBasis
    (fun k => exp (lam k s * I)) (fun k => exp (φ k s * I))
    (fun k => by simpa using he k) (fun k => by simpa using he' k)
  set d : Fin n → ℝ := fun k => lam k s - φ (σ k) s with hd
  have hexpd : ∀ k, exp ((d k : ℝ) * I) = 1 := by
    intro k
    have h := hσ k
    have : ((d k : ℝ) : ℂ) * I = lam k s * I - φ (σ k) s * I := by
      simp only [d]; push_cast; ring
    rw [this, Complex.exp_sub, ← h, div_self (Complex.exp_ne_zero _)]
  set lam' : Fin n → ℝ → ℝ := fun k t => if t ≤ s then lam k t else φ (σ k) t + d k with hlam'
  have hlo : ∀ k t, t ≤ s → lam' k t = lam k t := fun k t ht => by simp [lam', ht]
  have hhi : ∀ k t, s ≤ t → lam' k t = φ (σ k) t + d k := by
    intro k t ht
    rcases ht.lt_or_eq with h | h
    · simp [lam', not_le.2 h]
    · subst h; simp [lam', d]
  refine ⟨lam', fun k => by rw [hlo k 0 hs0, hl0], fun k => ?_, ?_, ?_⟩
  · have h1 : ContinuousOn (lam' k) (Icc 0 s) :=
      (hlc k).congr fun t ht => hlo k t ht.2
    have h2 : ContinuousOn (lam' k) (Icc s s₂) :=
      ((hφc (σ k)).add continuous_const).continuousOn.congr fun t ht => hhi k t ht.1
    have := h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc
    rwa [Icc_union_Icc_eq_Icc hs0 hs] at this
  · intro t ht
    by_cases hts : t ≤ s
    · obtain ⟨e, he⟩ := hle t ⟨ht.1, hts⟩
      exact ⟨e, fun k => by rw [hlo k t hts]; exact he k⟩
    · obtain ⟨e, he⟩ := hφe t ⟨(not_le.1 hts).le, ht.2⟩
      refine ⟨e.reindex σ.symm, fun k => ?_⟩
      rw [OrthonormalBasis.reindex_apply, Equiv.symm_symm, he, hhi k t (not_le.1 hts).le]
      push_cast
      rw [add_mul, Complex.exp_add, hexpd, mul_one]
  · intro t ht
    by_cases hts : t < s
    · obtain ⟨u, hu⟩ := hld t ⟨ht.1, hts⟩
      refine ⟨u, fun k => (hu k).congr_of_eventuallyEq ?_ (hlo k t hts.le)⟩
      filter_upwards [Icc_mem_nhdsGE hts] with τ hτ
      exact hlo k τ hτ.2
    · obtain ⟨u, hu⟩ := hφd t ⟨not_lt.1 hts, ht.2⟩
      refine ⟨u.reindex σ.symm, fun k => ?_⟩
      rw [OrthonormalBasis.reindex_apply, Equiv.symm_symm]
      refine ((hu (σ k)).add_const (d k)).congr (fun τ hτ => ?_) ?_
      · exact hhi k τ ((not_lt.1 hts).trans hτ)
      · exact hhi k t (not_lt.1 hts)

/-- **Global eigenphase lifts.** A unitary path `V` on `[0, b]` (finite dimensions) with
`V(0) = 1` and right derivative `V' = i V A`, `A(t)` self-adjoint, has global continuous
eigenphase lifts starting at `0`, whose right derivatives are diagonal entries of `A(t)` in
orthonormal bases. -/
theorem exists_phaseLift (hn : finrank ℂ F = n) {V A : ℝ → F →L[ℂ] F} {b : ℝ} (hb : 0 ≤ b)
    (hVu : ∀ t ∈ Icc 0 b, V t ∈ unitary (F →L[ℂ] F)) (hV0 : V 0 = 1)
    (hVc : ContinuousOn V (Icc 0 b))
    (hVd : ∀ t ∈ Ico 0 b, HasDerivWithinAt V (I • (V t * A t)) (Ici t) t)
    (hAs : ∀ t ∈ Ico 0 b, IsSelfAdjoint (A t)) :
    ∃ lam : Fin n → ℝ → ℝ, IsPhaseLift V A b lam := by
  classical
  set p : ℝ → ℝ := fun t => projIcc 0 b hb t with hpdef
  have hp : ∀ t, p t ∈ Icc 0 b := fun t => Subtype.mem _
  have hpeq : ∀ t ∈ Icc 0 b, p t = t := fun t ht => by simp [p, projIcc_of_mem hb ht]
  have hVpc : Continuous fun t => V (p t) :=
    hVc.comp_continuous (continuous_subtype_val.comp continuous_projIcc) hp
  obtain ⟨δ, hδ, hcov⟩ := lebesgue_number_lemma_of_metric (isCompact_Icc (a := 0) (b := b))
    (c := fun β : ℝ => {t : ℝ | IsUnit (1 - exp (-(β * I)) • V (p t))})
     (fun β => Units.isOpen.preimage
       ((continuous_const : Continuous (fun _ : ℝ => (1 : F →L[ℂ] F))).sub
         (hVpc.const_smul (exp (-(β * I)) : ℂ))))
    (fun t ht => by
      obtain ⟨β, hβ⟩ := exists_level_unit (V t)
      exact mem_iUnion.2 ⟨β, by simp only [mem_setOf_eq, hpeq t ht]; exact hβ⟩)
  have key : ∀ N : ℕ, ∃ lam : Fin n → ℝ → ℝ, IsPhaseLift V A (min b (N * (δ / 2))) lam := by
    intro N
    induction N with
    | zero =>
      have h0 : min b ((0 : ℕ) * (δ / 2)) = 0 := by simp [hb]
      rw [h0]
      refine ⟨fun _ _ => 0, fun k => rfl, fun k => continuousOn_const, ?_, ?_⟩
      · intro t ht
        have ht0 : t = 0 := le_antisymm ht.2 ht.1
        refine ⟨(stdOrthonormalBasis ℂ F).reindex (finCongr hn), fun k => ?_⟩
        simp [ht0, hV0]
      · intro t ht
        exact absurd (ht.1.trans_lt ht.2) (lt_irrefl _)
    | succ N ih =>
      obtain ⟨lam, hl⟩ := ih
      set s := min b (N * (δ / 2)) with hsdef
      set s₂ := min b ((N + 1 : ℕ) * (δ / 2)) with hs₂def
      have hs0 : 0 ≤ s := le_min hb (by positivity)
      have hss : s ≤ s₂ := min_le_min le_rfl (by gcongr; linarith)
      have hsb : s₂ ≤ b := min_le_left _ _
      have hgap : s₂ ≤ s + δ / 2 := by
        calc s₂ ≤ min (b + δ / 2) (N * (δ / 2) + δ / 2) :=
              min_le_min (by linarith) (by push_cast; linarith)
          _ = s + δ / 2 := min_add_add_right _ _ _
      obtain ⟨β, hβ⟩ := hcov s ⟨hs0, hss.trans hsb⟩
      have hunit : ∀ t ∈ Icc s s₂, IsUnit (1 - exp (-(β * I)) • V t) := by
        intro t ht
        have htb : t ∈ Icc 0 b := ⟨hs0.trans ht.1, ht.2.trans hsb⟩
        have hball : t ∈ Metric.ball s δ := by
          rw [Metric.mem_ball, Real.dist_eq, abs_lt]
          constructor <;> linarith [ht.1, ht.2]
        have := hβ hball
        simpa [hpeq t htb] using this
      have hsub : Icc s s₂ ⊆ Icc 0 b := Icc_subset_Icc hs0 hsb
      have hsub' : Ico s s₂ ⊆ Ico 0 b := Ico_subset_Ico hs0 hsb
      obtain ⟨φ, hφc, hφe, hφd, -⟩ := phase_window hn hss (fun t ht => hVu t (hsub ht))
        (hVc.mono hsub) (fun t ht => hVd t (hsub' ht)) (fun t ht => hAs t (hsub' ht)) hunit
      exact hl.extend hs0 hss hφc hφe hφd
  obtain ⟨N, hN⟩ := exists_nat_ge (b / (δ / 2))
  obtain ⟨lam, hl⟩ := key N
  have : min b (N * (δ / 2)) = b :=
    min_eq_left (by rwa [div_le_iff₀ (by positivity)] at hN)
  rw [this] at hl
  exact ⟨lam, hl⟩

end

section

/-! ## The crossing-cost estimate in finite dimensions -/

open scoped InnerProductSpace
open Module Filter Topology Set Complex MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

omit [FiniteDimensional ℂ F] in
/-- The dimension of an eigenspace, computed in an orthonormal eigenbasis. -/
lemma finrank_ker_sub_eq_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℂ F) (T : F →L[ℂ] F) (z : ι → ℂ) (he : ∀ k, T (e k) = z k • e k)
    (c : ℂ) :
    finrank ℂ (LinearMap.ker ((T - c • 1 : F →L[ℂ] F) : F →ₗ[ℂ] F)) =
      (Finset.univ.filter (fun k => z k = c)).card := by
  set S := Finset.univ.filter (fun k => z k = c)
  have hS : LinearMap.ker ((T - c • 1 : F →L[ℂ] F) : F →ₗ[ℂ] F) =
      Submodule.span ℂ (e '' (S : Set ι)) := by
    apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker] at hx
      simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, sub_eq_zero] at hx
      have hTx : T x = ∑ k, (⟪e k, x⟫_ℂ * z k) • e k := by
        conv_lhs => rw [← e.sum_repr' x]
        simp [map_sum, map_smul, he, smul_smul]
      have hcoord : ∀ j, z j ≠ c → ⟪e j, x⟫_ℂ = 0 := by
        intro j hj
        have h1 : ⟪e j, T x⟫_ℂ = ⟪e j, x⟫_ℂ * z j := by
          rw [hTx]; exact e.orthonormal.inner_right_fintype _ j
        rw [hx, inner_smul_right] at h1
        have : (z j - c) * ⟪e j, x⟫_ℂ = 0 := by linear_combination -h1
        rcases mul_eq_zero.1 this with h | h
        · exact absurd (sub_eq_zero.1 h) hj
        · exact h
      have hx' : x = ∑ k ∈ S, ⟪e k, x⟫_ℂ • e k := by
        conv_lhs => rw [← e.sum_repr' x]
        rw [← Finset.sum_subset (Finset.subset_univ S)]
        intro j _ hj
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp [hcoord j hj]
      rw [hx']
      exact Submodule.sum_mem _ fun k hk =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨k, hk, rfl⟩
      simp only [S, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hk
      simp [he, hk]
  rw [hS, Set.image_eq_range, finrank_span_eq_card]
  · simp
  · exact (e.orthonormal.linearIndependent).comp _ Subtype.val_injective

/-- The crossing multiplicity computed from an eigenbasis. -/
lemma crossingMult_eq_card {n : ℕ} {V : ℝ → F →L[ℂ] F} {α t : ℝ}
    (e : OrthonormalBasis (Fin n) ℂ F) (lam : Fin n → ℝ)
    (he : ∀ k, V t (e k) = exp (lam k * I) • e k) :
    crossingMult V α t =
      ((Finset.univ.filter fun k => exp (lam k * I) = exp (α * I)).card : ℕ∞) := by
  classical
  have h := finrank_ker_sub_eq_card e (V t) _ he (exp (α * I))
  rw [ContinuousLinearMap.coe_sub, ContinuousLinearMap.coe_smul] at h
  unfold crossingMult
  rw [← Module.finrank_eq_rank, h]
  simp

/-- A strictly increasing branch starting at `0` which meets the level `α` (mod `2π`) at `N`
times in `(0, b)` reaches at least `α N` at time `b`. -/
lemma mul_card_le_of_strictMonoOn {f : ℝ → ℝ} {b α : ℝ} (hb : 0 ≤ b)
    (hf : StrictMonoOn f (Icc 0 b)) (hf0 : f 0 = 0) (hα0 : 0 < α) (hα : α < 2 * Real.pi)
    (s : Finset ℝ) (hs : ∀ t ∈ s, t ∈ Ioo 0 b ∧ exp (f t * I) = exp (α * I)) :
    α * s.card ≤ f b := by
  have hpi := Real.pi_pos
  have hb0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb⟩
  have hbb : b ∈ Icc 0 b := ⟨hb, le_rfl⟩
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty, Nat.cast_zero, mul_zero]
    rw [← hf0]; exact hf.monotoneOn hb0 hbb hb
  -- each crossing value is `α + 2π j` with `j ∈ ℕ`
  have hval : ∀ t ∈ s, ∃ j : ℕ, f t = α + 2 * Real.pi * j := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := hs t ht
    obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.1 ht2
    have him := congrArg Complex.im hj
    simp at him
    have hpos : 0 < f t := by
      rw [← hf0]; exact hf hb0 ⟨ht1.1.le, ht1.2.le⟩ ht1.1
    have hj0 : 0 ≤ j := by
      by_contra hneg
      have : (j : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.mpr (not_le.1 hneg)
      nlinarith
    refine ⟨j.toNat, ?_⟩
    rw [him]
    have : ((j.toNat : ℕ) : ℝ) = (j : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hj0
    rw [this]; ring
  have hle : ∀ t ∈ s, f t ≤ f b := fun t ht =>
    hf.monotoneOn ⟨(hs t ht).1.1.le, (hs t ht).1.2.le⟩ hbb (hs t ht).1.2.le
  obtain ⟨t₀, ht₀⟩ := hne
  obtain ⟨j₀, hj₀⟩ := hval t₀ ht₀
  have hαb : α ≤ f b := by
    have := hle t₀ ht₀; rw [hj₀] at this; nlinarith [(Nat.cast_nonneg j₀ : (0 : ℝ) ≤ j₀)]
  set J := ⌊(f b - α) / (2 * Real.pi)⌋₊ with hJ
  have hJle : (J : ℝ) ≤ (f b - α) / (2 * Real.pi) := Nat.floor_le (div_nonneg (by linarith) (by positivity))
  have hcard : s.card ≤ J + 1 := by
    have : s.card ≤ (Finset.range (J + 1)).card := by
      refine Finset.card_le_card_of_injOn (fun t => ⌊(f t - α) / (2 * Real.pi)⌋₊) ?_ ?_
      · intro t ht
        obtain ⟨j, hj⟩ := hval t ht
        simp only [Finset.coe_range, Set.mem_Iio]
        have h1 : (f t - α) / (2 * Real.pi) = j := by rw [hj]; field_simp; ring
        rw [h1, Nat.floor_natCast, Nat.lt_succ_iff]
        apply Nat.le_floor
        rw [← h1]
        gcongr
        exact hle t ht
      · intro t ht t' ht' htt
        obtain ⟨j, hj⟩ := hval t ht
        obtain ⟨j', hj'⟩ := hval t' ht'
        have h1 : (f t - α) / (2 * Real.pi) = j := by rw [hj]; field_simp; ring
        have h2 : (f t' - α) / (2 * Real.pi) = j' := by rw [hj']; field_simp; ring
        simp only [h1, h2, Nat.floor_natCast] at htt
        have : f t = f t' := by rw [hj, hj', htt]
        exact hf.injOn ⟨(hs t ht).1.1.le, (hs t ht).1.2.le⟩
          ⟨(hs t' ht').1.1.le, (hs t' ht').1.2.le⟩ this
    simpa using this
  have h2J : 2 * Real.pi * J ≤ f b - α := by
    rw [le_div_iff₀ (by positivity)] at hJle; linarith
  calc α * s.card ≤ α * (J + 1) := by gcongr; exact_mod_cast hcard
    _ = α * J + α := by ring
    _ ≤ 2 * Real.pi * J + α := by gcongr
    _ ≤ f b := by linarith

/-- Choosing at most `m` branches carrying at least `m` crossings. -/
lemma exists_finset_card_le_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ι → ℕ) {m : ℕ}
    (hm : m ≤ ∑ k, N k) : ∃ J : Finset ι, J.card ≤ m ∧ m ≤ ∑ k ∈ J, N k := by
  set P := Finset.univ.filter fun k => N k ≠ 0
  by_cases hP : m ≤ P.card
  · obtain ⟨J, hJP, hJ⟩ := Finset.exists_subset_card_eq hP
    refine ⟨J, hJ.le, ?_⟩
    calc m = ∑ _k ∈ J, 1 := by simp [hJ]
      _ ≤ ∑ k ∈ J, N k := Finset.sum_le_sum fun k hk => by
          have := (Finset.mem_filter.1 (hJP hk)).2; omega
  · refine ⟨P, (not_le.1 hP).le, ?_⟩
    rw [Finset.sum_filter_ne_zero]; exact hm

variable {n : ℕ}

lemma IsPhaseLift.strictMonoOn' (hn : finrank ℂ F = n) {V A : ℝ → F →L[ℂ] F} {b : ℝ}
    {lam : Fin n → ℝ → ℝ} (hl : IsPhaseLift V A b lam)
    (hApos : ∀ t ∈ Icc 0 b, ∀ x, 0 ≤ RCLike.re ⟪x, A t x⟫_ℂ)
    (hAsp : ∀ t ∈ Ioo 0 b, ∀ x, x ≠ 0 → 0 < RCLike.re ⟪x, A t x⟫_ℂ) (k : Fin n) :
    StrictMonoOn (lam k) (Icc 0 b) := by
  haveI : Nonempty (OrthonormalBasis (Fin n) ℂ F) :=
    ⟨(stdOrthonormalBasis ℂ F).reindex (finCongr hn)⟩
  choose! u hu using hl.2.2.2
  exact strictMonoOn_of_rderiv_pos (hl.2.1 k) (fun t ht => hu t ht k)
    (fun t ht => hApos t (Ico_subset_Icc_self ht) _)
    (fun t ht => hAsp t ht _ ((u t).orthonormal.ne_zero k))

lemma IsPhaseLift.sum_le_integral (hn : finrank ℂ F = n) {V A : ℝ → F →L[ℂ] F} {b : ℝ}
    (hb : 0 ≤ b) {lam : Fin n → ℝ → ℝ} (hl : IsPhaseLift V A b lam)
    (hApos : ∀ t ∈ Icc 0 b, ∀ x, 0 ≤ RCLike.re ⟪x, A t x⟫_ℂ)
    (hAc : ContinuousOn A (Icc 0 b)) (J : Finset (Fin n)) :
    ∑ k ∈ J, lam k b ≤ ∫ t in (0 : ℝ)..b, (kyFan J.card (A t)).toReal := by
  haveI : Nonempty (OrthonormalBasis (Fin n) ℂ F) :=
    ⟨(stdOrthonormalBasis ℂ F).reindex (finCongr hn)⟩
  choose! u hu using hl.2.2.2
  have := sub_le_integral_of_rderiv hb (f := fun t => ∑ k ∈ J, lam k t)
    (f' := fun t => ∑ k ∈ J, RCLike.re ⟪u t k, A t (u t k)⟫_ℂ)
    (continuousOn_finset_sum _ fun k _ => hl.2.1 k)
    (fun t ht => HasDerivWithinAt.fun_sum fun k _ => hu t ht k)
    ((lipschitzWith_kyFan_toReal _).continuous.comp_continuousOn hAc)
    (fun t ht => sum_re_inner_le_kyFan (hApos t (Ico_subset_Icc_self ht)) (u t).orthonormal J)
  simpa [hl.1] using this

/-- The crossing-cost estimate in finite dimensions. -/
theorem phase_cost_finiteDim {V A : ℝ → F →L[ℂ] F} {b : ℝ} (hb : 0 ≤ b)
    (hVu : ∀ t ∈ Icc 0 b, V t ∈ unitary (F →L[ℂ] F)) (hV0 : V 0 = 1)
    (hVc : ContinuousOn V (Icc 0 b))
    (hVd : ∀ t ∈ Ico 0 b, HasDerivWithinAt V (I • (V t * A t)) (Ici t) t)
    (hAs : ∀ t ∈ Ico 0 b, IsSelfAdjoint (A t)) (hAc : ContinuousOn A (Icc 0 b))
    (hApos : ∀ t ∈ Icc 0 b, ∀ x, 0 ≤ RCLike.re ⟪x, A t x⟫_ℂ)
    (hAsp : ∀ t ∈ Ioo 0 b, ∀ x, x ≠ 0 → 0 < RCLike.re ⟪x, A t x⟫_ℂ)
    {α : ℝ} (hα0 : 0 < α) (hα : α < 2 * Real.pi) :
    crossingCount V α (Ioo 0 b) < ⊤ ∧
      ∀ m : ℕ, (m : ℕ∞) ≤ crossingCount V α (Ioo 0 b) →
        ENNReal.ofReal (α * m) ≤ ∫⁻ t in Icc 0 b, kyFan m (A t) := by
  classical
  obtain ⟨lam, hl⟩ := exists_phaseLift (n := finrank ℂ F) rfl hb hVu hV0 hVc hVd hAs
  have hmono := fun k => hl.strictMonoOn' rfl hApos hAsp k
  set P : Fin (finrank ℂ F) → ℝ → Prop := fun k t => exp (lam k t * I) = exp (α * I)
  -- the crossing count of a finite set of times, branch by branch
  have hsum : ∀ s : Finset ℝ, ↑s ⊆ Ioo 0 b →
      ∑ t ∈ s, crossingMult V α t = ((∑ k, (s.filter (P k)).card : ℕ) : ℕ∞) := by
    intro s hs
    have h1 : ∀ t ∈ s, crossingMult V α t =
        ((Finset.univ.filter fun k => P k t).card : ℕ∞) := by
      intro t ht
      obtain ⟨e, he⟩ := hl.2.2.1 t (Ioo_subset_Icc_self (hs ht))
      exact crossingMult_eq_card e (fun k => lam k t) he
    rw [Finset.sum_congr rfl h1, ← Nat.cast_sum]
    congr 1
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hbranch : ∀ s : Finset ℝ, ↑s ⊆ Ioo 0 b → ∀ k,
      α * (s.filter (P k)).card ≤ lam k b := by
    intro s hs k
    refine mul_card_le_of_strictMonoOn hb (hmono k) (hl.1 k) hα0 hα _ fun t ht => ?_
    obtain ⟨ht1, ht2⟩ := Finset.mem_filter.1 ht
    exact ⟨hs ht1, ht2⟩
  set B : ℕ := ∑ k, ⌊lam k b / α⌋₊ with hB
  have hbound : ∀ s : Finset ℝ, ↑s ⊆ Ioo 0 b → ∑ k, (s.filter (P k)).card ≤ B := by
    intro s hs
    refine Finset.sum_le_sum fun k _ => Nat.le_floor ?_
    rw [le_div_iff₀ hα0, mul_comm]
    exact hbranch s hs k
  have hfin : crossingCount V α (Ioo 0 b) ≤ B := by
    refine iSup₂_le fun s hs => ?_
    rw [hsum s hs]
    exact_mod_cast hbound s hs
  refine ⟨hfin.trans_lt (ENat.coe_lt_top _), fun m hm => ?_⟩
  -- a finite set of times carrying at least `m` crossings
  obtain ⟨s, hs, hms⟩ : ∃ s : Finset ℝ, ↑s ⊆ Ioo 0 b ∧ m ≤ ∑ k, (s.filter (P k)).card := by
    by_contra hcon
    push_neg at hcon
    have hle : crossingCount V α (Ioo 0 b) ≤ ((m - 1 : ℕ) : ℕ∞) := by
      refine iSup₂_le fun s hs => ?_
      rw [hsum s hs]
      exact_mod_cast Nat.le_sub_one_of_lt (hcon s hs)
    have h1 : m ≤ m - 1 := by exact_mod_cast hm.trans hle
    have h0 : m = 0 := by omega
    have := hcon ∅ (by simp)
    simp [h0] at this
  obtain ⟨J, hJm, hJ⟩ := exists_finset_card_le_sum (fun k => (s.filter (P k)).card) hms
  have hcost : α * m ≤ ∫ t in (0 : ℝ)..b, (kyFan J.card (A t)).toReal := by
    calc α * m ≤ α * ((∑ k ∈ J, (s.filter (P k)).card : ℕ) : ℝ) := by
          gcongr
      _ = ∑ k ∈ J, α * (s.filter (P k)).card := by push_cast; rw [Finset.mul_sum]
      _ ≤ ∑ k ∈ J, lam k b := Finset.sum_le_sum fun k _ => hbranch s hs k
      _ ≤ _ := hl.sum_le_integral rfl hb hApos hAc J
  have hgc : ContinuousOn (fun t => (kyFan J.card (A t)).toReal) (Icc 0 b) :=
    (lipschitzWith_kyFan_toReal _).continuous.comp_continuousOn hAc
  have hint : ENNReal.ofReal (∫ t in (0 : ℝ)..b, (kyFan J.card (A t)).toReal) =
      ∫⁻ t in Icc 0 b, kyFan J.card (A t) := by
    rw [intervalIntegral.integral_of_le hb, ← integral_Icc_eq_integral_Ioc,
      ofReal_integral_eq_lintegral_ofReal hgc.integrableOn_Icc
        (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)]
    exact lintegral_congr fun t => ENNReal.ofReal_toReal (kyFan_ne_top _ _)
  calc ENNReal.ofReal (α * m) ≤ ENNReal.ofReal (∫ t in (0 : ℝ)..b,
        (kyFan J.card (A t)).toReal) := ENNReal.ofReal_le_ofReal hcost
    _ = ∫⁻ t in Icc 0 b, kyFan J.card (A t) := hint
    _ ≤ ∫⁻ t in Icc 0 b, kyFan m (A t) := lintegral_mono fun t => kyFan_mono hJm _

end

section

/-! ## Crossings inside a window (finite dimensions) -/

open scoped InnerProductSpace
open Module Filter Topology Set Complex

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- If `‖(W - c) y‖ ≤ ε ‖y‖` on a subspace `Y`, then `W` has at least `dim Y` eigenvalues within
`ε` of `c` (counted in an orthonormal eigenbasis). -/
lemma finrank_le_card_of_approx_eigen {n : ℕ} (hn : finrank ℂ F = n)
    (e : OrthonormalBasis (Fin n) ℂ F) (W : F →L[ℂ] F) (z : Fin n → ℂ)
    (he : ∀ k, W (e k) = z k • e k) (c : ℂ) {ε : ℝ} (Y : Submodule ℂ F)
    (hY : ∀ y ∈ Y, ‖(W - c • 1) y‖ ≤ ε * ‖y‖) :
    finrank ℂ Y ≤ (Finset.univ.filter fun k => ‖z k - c‖ ≤ ε).card := by
  classical
  by_contra hcon
  push_neg at hcon
  set B := Finset.univ.filter fun k => ε < ‖z k - c‖ with hB
  have hS : finrank ℂ (Submodule.span ℂ (e '' (B : Set (Fin n)))) = B.card := by
    rw [Set.image_eq_range, finrank_span_eq_card]
    · simp
    · exact (e.orthonormal.linearIndependent).comp _ Subtype.val_injective
  set S : Submodule ℂ F := Submodule.span ℂ (e '' (B : Set (Fin n))) with hSdef
  have hBc : B.card + (Finset.univ.filter fun k => ‖z k - c‖ ≤ ε).card = n := by
    rw [hB, ← Finset.card_union_of_disjoint]
    · convert Finset.card_fin n
      ext k; simp [lt_or_ge]
    · rw [Finset.disjoint_filter]; intro k _ h1 h2; linarith
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq Y S
  have hle := Submodule.finrank_le (Y ⊔ S)
  have hinf : Y ⊓ S ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hsup
    omega
  obtain ⟨y, hyYS, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  have hSorth : ∀ k, k ∉ B → ∀ x ∈ S, ⟪e k, x⟫_ℂ = 0 := by
    intro k hk x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      have hne : k ≠ i := fun h => by subst h; exact hk hi
      exact e.orthonormal.2 hne
    | zero => simp
    | add x w _ _ hx hw => simp [hx, hw]
    | smul a x _ hx => simp [hx]
  have hyS : ∀ k, k ∉ B → ⟪e k, y⟫_ℂ = 0 := fun k hk => hSorth k hk y hyYS.2
  have hcoord : ∀ k, ⟪e k, (W - c • 1) y⟫_ℂ = (z k - c) * ⟪e k, y⟫_ℂ := by
    intro k
    have : (W - c • 1) y = ∑ j, (⟪e j, y⟫_ℂ * (z j - c)) • e j := by
      conv_lhs => rw [← e.sum_repr' y]
      simp only [map_sum, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, he, mul_sub, sub_smul, smul_sub, smul_smul]
    rw [this, e.orthonormal.inner_right_fintype]; ring
  have h1 := hY y hyYS.1
  have hpos : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hε : 0 ≤ ε := by
    by_contra h
    push_neg at h
    have : ε * ‖y‖ < 0 := mul_neg_of_neg_of_pos h hpos
    linarith [norm_nonneg ((W - c • 1) y)]
  have key : ε ^ 2 * ‖y‖ ^ 2 < ‖(W - c • 1) y‖ ^ 2 := by
    rw [← e.sum_sq_norm_inner_right y, ← e.sum_sq_norm_inner_right, Finset.mul_sum]
    obtain ⟨k₀, hk₀⟩ : ∃ k, ⟪e k, y⟫_ℂ ≠ 0 := by
      by_contra h; push_neg at h
      exact hy0 (by rw [← e.sum_repr' y]; simp [h])
    apply Finset.sum_lt_sum
    · intro k _
      rw [hcoord, norm_mul, mul_pow]
      by_cases hk : k ∈ B
      · gcongr; exact (Finset.mem_filter.1 hk).2.le
      · simp [hyS k hk]
    · refine ⟨k₀, Finset.mem_univ _, ?_⟩
      have hk₀B : k₀ ∈ B := by by_contra h; exact hk₀ (hyS k₀ h)
      rw [hcoord, norm_mul, mul_pow]
      have := (Finset.mem_filter.1 hk₀B).2
      have h2 : 0 < ‖⟪e k₀, y⟫_ℂ‖ ^ 2 := by positivity
      gcongr
  have : ‖(W - c • 1) y‖ ^ 2 ≤ (ε * ‖y‖) ^ 2 := by gcongr
  nlinarith

lemma norm_exp_mul_I_sub_sq (a b : ℝ) :
    ‖exp (a * I) - exp (b * I)‖ ^ 2 = 2 - 2 * Real.cos (a - b) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  rw [Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b]

lemma cos_le_cos_of_mem_Icc {δ y : ℝ} (hδ0 : 0 ≤ δ) (h1 : δ ≤ y) (h2 : y ≤ 2 * Real.pi - δ) :
    Real.cos y ≤ Real.cos δ := by
  rcases le_total y Real.pi with h | h
  · exact Real.cos_le_cos_of_nonneg_of_le_pi hδ0 h h1
  · have : Real.cos y = Real.cos (2 * Real.pi - y) := by rw [Real.cos_two_pi_sub]
    rw [this]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hδ0 (by linarith) (by linarith)

lemma isUnit_one_sub_smul_of_injective (U : F →L[ℂ] F) (β : ℝ)
    (h : ∀ y, y ≠ 0 → (U - exp (β * I) • 1) y ≠ 0) : IsUnit (1 - exp (-(β * I)) • U) := by
  refine ContinuousLinearMap.isUnit_iff_bijective.2 ?_
  have hi : Function.Injective ((1 - exp (-(β * I)) • U : F →L[ℂ] F) : F →ₗ[ℂ] F) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    by_contra hy0
    apply h y hy0
    have hy' : y - exp (-(β * I)) • U y = 0 := by simpa using hy
    have : (U - exp (β * I) • 1) y = -exp (β * I) • (y - exp (-(β * I)) • U y) := by
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, smul_sub, smul_smul, neg_smul, neg_mul,
        ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]
      abel
    rw [this, hy', smul_zero]
  exact ⟨hi, LinearMap.injective_iff_surjective.1 hi⟩

/-- **Crossings inside a window.** -/
theorem crossings_in_window {n : ℕ} (hn : finrank ℂ F = n) {V A : ℝ → F →L[ℂ] F}
    {tl t₀ tr α δ ε : ℝ} (h₁ : tl ≤ t₀) (h₂ : t₀ ≤ tr)
    (hVu : ∀ t ∈ Icc tl tr, V t ∈ unitary (F →L[ℂ] F)) (hVc : ContinuousOn V (Icc tl tr))
    (hVd : ∀ t ∈ Ico tl tr, HasDerivWithinAt V (I • (V t * A t)) (Ici t) t)
    (hAs : ∀ t ∈ Ico tl tr, IsSelfAdjoint (A t))
    (hApos : ∀ t ∈ Ico tl tr, ∀ x, 0 ≤ RCLike.re ⟪x, A t x⟫_ℂ)
    (hδ0 : 0 < δ)
    (hgapA : ∀ t ∈ Icc tl tr, ∀ y, y ≠ 0 → (V t - exp ((α + δ : ℝ) * I) • 1) y ≠ 0)
    (hgapB : ∀ θ ∈ Icc α (α + δ), ∀ y, y ≠ 0 → (V tl - exp (θ * I) • 1) y ≠ 0)
    (hgapB' : ∀ θ ∈ Icc (α - δ) α, ∀ y, y ≠ 0 → (V tr - exp (θ * I) • 1) y ≠ 0)
    (hεδ : ε ^ 2 < 2 - 2 * Real.cos δ) (Y : Submodule ℂ F)
    (hY : ∀ y ∈ Y, ‖(V t₀ - exp (α * I) • 1) y‖ ≤ ε * ‖y‖) :
    ∃ s : Finset ℝ, ↑s ⊆ Ioo tl tr ∧ (finrank ℂ Y : ℕ∞) ≤ ∑ t ∈ s, crossingMult V α t := by
  classical
  set β : ℝ := α + δ with hβ
  have hle : tl ≤ tr := h₁.trans h₂
  obtain ⟨φ, hφc, hφe, hφd, hφr⟩ := phase_window hn (β := β) hle hVu hVc hVd hAs
    (fun t ht => isUnit_one_sub_smul_of_injective (V t) β (hgapA t ht))
  haveI : Nonempty (OrthonormalBasis (Fin n) ℂ F) :=
    ⟨(stdOrthonormalBasis ℂ F).reindex (finCongr hn)⟩
  choose! u hu using hφd
  have hmono : ∀ k, MonotoneOn (φ k) (Icc tl tr) := fun k =>
    monotoneOn_of_rderiv_nonneg (hφc k).continuousOn (fun t ht => hu t ht k)
      (fun t ht => hApos t ht _)
  have hexcl : ∀ t ∈ Icc tl tr, ∀ k, ∃ y : F, y ≠ 0 ∧ (V t - exp (φ k t * I) • 1) y = 0 := by
    intro t ht k
    obtain ⟨e, he⟩ := hφe t ht
    exact ⟨e k, e.orthonormal.ne_zero k, by simp [he]⟩
  have hlow : ∀ k, φ k tl < α := by
    intro k
    by_contra hcon; push_neg at hcon
    obtain ⟨y, hy0, hy⟩ := hexcl tl ⟨le_rfl, hle⟩ k
    exact hgapB _ ⟨hcon, (hφr k tl).2.le⟩ y hy0 hy
  have hhigh : ∀ k, φ k tr ∉ Icc (α - δ) α := by
    intro k hk
    obtain ⟨y, hy0, hy⟩ := hexcl tr ⟨hle, le_rfl⟩ k
    exact hgapB' _ hk y hy0 hy
  obtain ⟨e₀, he₀⟩ := hφe t₀ ⟨h₁, h₂⟩
  set K' := Finset.univ.filter fun k => ‖exp (φ k t₀ * I) - exp (α * I)‖ ≤ ε with hK'
  have hcard : finrank ℂ Y ≤ K'.card :=
    finrank_le_card_of_approx_eigen hn e₀ (V t₀) _ he₀ _ Y hY
  have hcross : ∀ k ∈ K', ∃ τ ∈ Ioo tl tr, φ k τ = α := by
    intro k hk
    have hk' := (Finset.mem_filter.1 hk).2
    have h0 : α - δ < φ k t₀ := by
      by_contra hcon; push_neg at hcon
      have hr := hφr k t₀
      have hcos : Real.cos (φ k t₀ - α) ≤ Real.cos δ := by
        rw [← Real.cos_neg, neg_sub]
        exact cos_le_cos_of_mem_Icc hδ0.le (by linarith) (by linarith [hr.1])
      have h1 := norm_exp_mul_I_sub_sq (φ k t₀) α
      have h2 : ‖exp (φ k t₀ * I) - exp (α * I)‖ ^ 2 ≤ ε ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hk' 2
      linarith
    have hup : α < φ k tr := by
      have hm := hmono k ⟨h₁, h₂⟩ ⟨hle, le_rfl⟩ h₂
      by_contra hcon; push_neg at hcon
      exact hhigh k ⟨by linarith, hcon⟩
    obtain ⟨τ, hτ, hτα⟩ := intermediate_value_Ioo hle (hφc k).continuousOn ⟨hlow k, hup⟩
    exact ⟨τ, hτ, hτα⟩
  choose! τ hτ hτα using hcross
  refine ⟨K'.image τ, ?_, ?_⟩
  · intro t ht
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ht)
    exact hτ k hk
  · have hmult : ∀ t ∈ K'.image τ,
        ((K'.filter fun k => τ k = t).card : ℕ∞) ≤ crossingMult V α t := by
      intro t ht
      obtain ⟨k, hk, hkt⟩ := Finset.mem_image.1 ht
      obtain ⟨e, he⟩ := hφe t (hkt ▸ Ioo_subset_Icc_self (hτ k hk))
      rw [crossingMult_eq_card e (fun j => φ j t) he]
      norm_cast
      apply Finset.card_le_card
      intro j hj
      obtain ⟨hjK, hjτ⟩ := Finset.mem_filter.1 hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hjτ, hτα j hjK]
    calc (finrank ℂ Y : ℕ∞) ≤ K'.card := by exact_mod_cast hcard
      _ = ∑ t ∈ K'.image τ, ((K'.filter fun k => τ k = t).card : ℕ∞) := by
          rw [Finset.card_eq_sum_card_image τ K']; push_cast; rfl
      _ ≤ _ := Finset.sum_le_sum hmult

end

section

/-! ## A spectral window around a crossing -/

open scoped InnerProductSpace ComplexConjugate
open Set Metric Filter Topology Complex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Orthogonal decomposition `x = x₀ + x₁`, `x₀ ∈ K`, `x₁ ∈ Kᗮ`. -/
lemma exists_orth_decomp (K : Submodule ℂ E) [K.HasOrthogonalProjection] (x : E) :
    ∃ x₀ ∈ K, ∃ x₁ ∈ Kᗮ, x = x₀ + x₁ :=
  ⟨K.starProjection x, K.starProjection_apply_mem x, x - K.starProjection x,
    K.sub_starProjection_mem_orthogonal x, by abel⟩

/-- Zeroth-order lower bound from a gap on `Kᗮ`. -/
lemma norm_ge_of_gap {U₀ : E →L[ℂ] E} (hU : U₀ ∈ unitary (E →L[ℂ] E)) {e : ℂ} (he : ‖e‖ = 1)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (heig : ∀ k ∈ K, U₀ k = e • k) {z : ℂ}
    {g : ℝ} (hg : 0 ≤ g) (hgap : ∀ x ∈ Kᗮ, g * ‖x‖ ≤ ‖(U₀ - z • 1) x‖) (x : E) :
    min ‖e - z‖ g * ‖x‖ ≤ ‖(U₀ - z • 1) x‖ := by
  obtain ⟨x₀, h₀, x₁, h₁, rfl⟩ := exists_orth_decomp K x
  have hsq := norm_sub_smul_apply_sq hU he heig z h₀ h₁
  have hx := norm_add_sq_of_mem_orthogonal h₀ h₁
  set m := min ‖e - z‖ g
  have hm0 : 0 ≤ m := le_min (norm_nonneg _) hg
  have hm1 : m ≤ ‖e - z‖ := min_le_left _ _
  have hm2 : m ≤ g := min_le_right _ _
  have hg1 := hgap x₁ h₁
  have : (m * ‖x₀ + x₁‖) ^ 2 ≤ ‖(U₀ - z • 1) (x₀ + x₁)‖ ^ 2 := by
    rw [mul_pow, hx, hsq]
    have a1 : m ^ 2 * ‖x₀‖ ^ 2 ≤ ‖e - z‖ ^ 2 * ‖x₀‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hm0 hm1 2) (sq_nonneg _)
    have a2 : m ^ 2 * ‖x₁‖ ^ 2 ≤ ‖(U₀ - z • 1) x₁‖ ^ 2 := by
      have : m * ‖x₁‖ ≤ ‖(U₀ - z • 1) x₁‖ :=
        (mul_le_mul_of_nonneg_right hm2 (norm_nonneg _)).trans hg1
      have := pow_le_pow_left₀ (by positivity) this 2
      rwa [mul_pow] at this
    nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 this

/-- First-order lower bound near a crossing (combining `first_order_bound` with the gap). -/
lemma norm_ge_of_first_order {W U₀ L₀ : E →L[ℂ] E} (hU : U₀ ∈ unitary (E →L[ℂ] E))
    {e u : ℂ} (he : ‖e‖ = 1) (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (heig : ∀ k ∈ K, U₀ k = e • k) {σ h ρ lam Λ g : ℝ} (hσ : σ ^ 2 = 1) (hu : σ * u.im ≤ 0)
    (hR : ‖W - U₀ - ((σ * h : ℝ) : ℂ) • (I • (U₀ * L₀))‖ ≤ h * ρ)
    (hpos : ∀ k ∈ K, lam * ‖k‖ ^ 2 ≤ RCLike.re ⟪k, L₀ k⟫_ℂ) (hΛ : ‖L₀‖ ≤ Λ) (hh : 0 ≤ h)
    (hg : 0 < g) (hlam : 0 < lam) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ lam / 4)
    (hhs : h * (lam + Λ) * (Λ + ρ) ≤ g * lam / 4)
    (hgap : ∀ x ∈ Kᗮ, g * ‖x‖ ≤ ‖(U₀ - (e * u) • 1) x‖) (x : E) :
    h * g * lam / (2 * (g + h * (lam + Λ))) * ‖x‖ ≤ ‖(W - (e * u) • 1) x‖ := by
  obtain ⟨x₀, h₀, x₁, h₁, rfl⟩ := exists_orth_decomp K x
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans hΛ
  have hU1 : ‖U₀‖ ≤ 1 := norm_le_one_of_mem_unitary hU
  set z := e * u
  set N := ‖(W - z • 1) (x₀ + x₁)‖
  -- `‖W - U₀‖ ≤ h (Λ + ρ)`
  have hWU : ‖W - U₀‖ ≤ h * (Λ + ρ) := by
    have h1 : W - U₀ = (W - U₀ - ((σ * h : ℝ) : ℂ) • (I • (U₀ * L₀))) +
        ((σ * h : ℝ) : ℂ) • (I • (U₀ * L₀)) := by abel
    have hσ1 : |σ| = 1 := by
      have : |σ| ^ 2 = 1 := by rw [sq_abs, hσ]
      nlinarith [abs_nonneg σ]
    have h2 : ‖((σ * h : ℝ) : ℂ) • (I • (U₀ * L₀))‖ ≤ h * Λ := by
      rw [norm_smul, norm_smul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_mul, hσ1, one_mul, abs_of_nonneg hh]
      exact mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans
        (by nlinarith [norm_nonneg U₀, norm_nonneg L₀])) hh
    rw [h1]
    refine (norm_add_le _ _).trans ?_
    linarith
  -- zeroth-order bound
  have hb1 : g * ‖x₁‖ - h * (Λ + ρ) * ‖x₀ + x₁‖ ≤ N := by
    have hsq := norm_sub_smul_apply_sq hU he heig z h₀ h₁
    have hge : ‖(U₀ - z • 1) x₁‖ ≤ ‖(U₀ - z • 1) (x₀ + x₁)‖ := by
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
      rw [hsq]; nlinarith [sq_nonneg (‖e - z‖ * ‖x₀‖)]
    have hsplit : (W - z • 1) (x₀ + x₁) = (U₀ - z • 1) (x₀ + x₁) + (W - U₀) (x₀ + x₁) := by
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply]
      abel
    have h3 : ‖(U₀ - z • 1) (x₀ + x₁)‖ - ‖(W - U₀) (x₀ + x₁)‖ ≤ N := by
      have := norm_sub_norm_le ((U₀ - z • 1) (x₀ + x₁)) (-(W - U₀) (x₀ + x₁))
      rw [norm_neg, sub_neg_eq_add, ← hsplit] at this
      exact this
    have h4 : ‖(W - U₀) (x₀ + x₁)‖ ≤ h * (Λ + ρ) * ‖x₀ + x₁‖ :=
      ((W - U₀).le_opNorm _).trans (mul_le_mul_of_nonneg_right hWU (norm_nonneg _))
    linarith [hgap x₁ h₁]
  -- first-order bound
  have hb2 : h * (lam * ‖x₀‖ - Λ * ‖x₁‖ - ρ * ‖x₀ + x₁‖) ≤ N := by
    have hfo := first_order_bound hU he rfl heig hσ hu hR hpos hΛ hh h₀ h₁
    rcases (norm_nonneg x₀).lt_or_eq with hpos0 | hzero
    · exact le_of_mul_le_mul_left hfo hpos0
    · rw [← hzero]
      have : 0 ≤ N := norm_nonneg _
      nlinarith [mul_nonneg hh (mul_nonneg hΛ0 (norm_nonneg x₁)),
        mul_nonneg hh (mul_nonneg hρ0 (norm_nonneg (x₀ + x₁)))]
  exact combine_gap_bounds (norm_nonneg _) (norm_nonneg _)
    (norm_add_sq_of_mem_orthogonal h₀ h₁).symm (norm_nonneg _) hg hh hlam hΛ0 hρ hhs hb1 hb2

/-- **Local spectral window at a crossing.** -/
theorem exists_local_window {U : ℝ → E →L[ℂ] E} {t₀ : ℝ} {L₀ : E →L[ℂ] E} {α : ℝ}
    (hd : HasDerivAt U (I • (U t₀ * L₀)) t₀) (hU₀ : U t₀ ∈ unitary (E →L[ℂ] E))
    (hC : IsCompactOperator ((U t₀ - 1 : E →L[ℂ] E) : E → E)) (hα : exp (α * I) ≠ 1)
    (hL : ∀ v : E, v ≠ 0 → 0 < RCLike.re ⟪v, L₀ v⟫_ℂ)
    (K₀ : Submodule ℂ E) [FiniteDimensional ℂ K₀]
    (hK₀ : ∀ v, v ∈ K₀ ↔ (U t₀ - exp (α * I) • 1) v = 0) {h₀ : ℝ} (hh₀ : 0 < h₀) :
    ∃ δ > 0, δ ≤ 1 ∧ ∃ h > 0, h ≤ h₀ ∧ ∃ c > 0,
      (∀ t ∈ Icc (t₀ - h) (t₀ + h), ∀ x, c * ‖x‖ ≤ ‖(U t - exp ((α + δ : ℝ) * I) • 1) x‖) ∧
      (∀ θ ∈ Icc α (α + δ), ∀ x, c * ‖x‖ ≤ ‖(U (t₀ - h) - exp ((θ : ℂ) * I) • 1) x‖) ∧
      (∀ θ ∈ Icc (α - δ) α, ∀ x, c * ‖x‖ ≤ ‖(U (t₀ + h) - exp ((θ : ℂ) * I) • 1) x‖) := by
  set e : ℂ := exp (α * I) with he_def
  have he : ‖e‖ = 1 := Complex.norm_exp_ofReal_mul_I α
  have heig : ∀ k ∈ K₀, U t₀ k = e • k := by
    intro k hk
    have := (hK₀ k).1 hk
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, sub_eq_zero] at this
    exact this
  obtain ⟨η, hη, g, hg, hgap⟩ :=
    exists_gap_of_isCompactOperator hC hα K₀ (fun v hv => (hK₀ v).2 hv)
  obtain ⟨lam, hlam, hpos⟩ := exists_coercive_of_finiteDimensional K₀ hL
  set Λ : ℝ := ‖L₀‖ with hΛ
  have hΛ0 : 0 ≤ Λ := norm_nonneg _
  set ρ : ℝ := lam / 4 with hρ
  have hρ0 : 0 < ρ := by positivity
  set δ : ℝ := min η 1 with hδ
  have hδ0 : 0 < δ := lt_min hη one_pos
  have hδη : δ ≤ η := min_le_left _ _
  have hδ1 : δ ≤ 1 := min_le_right _ _
  set w : ℂ := exp ((α + δ : ℝ) * I) with hw
  have hew : 0 < ‖e - w‖ := by
    have h1 := norm_exp_mul_I_sub_sq α (α + δ)
    have h2 : Real.cos (α - (α + δ)) < 1 := by
      rw [show α - (α + δ) = -δ by ring, Real.cos_neg, ← Real.cos_zero]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [Real.pi_gt_three]) hδ0
    have : 0 < ‖e - w‖ ^ 2 := by rw [he_def, hw, h1]; linarith
    nlinarith [norm_nonneg (e - w)]
  set m₀ : ℝ := min ‖e - w‖ g with hm₀
  have hm₀ : 0 < m₀ := lt_min hew hg
  have hzero : ∀ x, m₀ * ‖x‖ ≤ ‖(U t₀ - w • 1) x‖ := by
    have := hgap δ (by rw [abs_of_pos hδ0]; exact hδη)
    exact norm_ge_of_gap hU₀ he K₀ heig hg.le this
  -- continuity and first-order expansion at `t₀`
  obtain ⟨h₂, hh₂, hcont⟩ := Metric.continuousAt_iff.1 hd.continuousAt (m₀ / 2) (by positivity)
  obtain ⟨h₁, hh₁, hlo⟩ := Metric.eventually_nhds_iff.1
    ((hasDerivAt_iff_isLittleO.1 hd).def hρ0)
  set hs : ℝ := g * lam / (4 * (lam + Λ) * (Λ + ρ)) with hhs
  have hs0 : 0 < hs := by positivity
  set h : ℝ := min (min h₀ (h₁ / 2)) (min (h₂ / 2) hs) with hh
  have hh0 : 0 < h := lt_min (lt_min hh₀ (by positivity)) (lt_min (by positivity) hs0)
  have hhh₀ : h ≤ h₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hhh₁ : h < h₁ := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _))
    (by linarith)
  have hhh₂ : h < h₂ := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _))
    (by linarith)
  have hhhs : h ≤ hs := (min_le_right _ _).trans (min_le_right _ _)
  have hhs' : h * (lam + Λ) * (Λ + ρ) ≤ g * lam / 4 := by
    have hpos' : 0 < 4 * (lam + Λ) * (Λ + ρ) := by positivity
    have := mul_le_mul_of_nonneg_right hhhs hpos'.le
    rw [hhs, div_mul_cancel₀ _ hpos'.ne'] at this
    linear_combination (1 / 4 : ℝ) * this
  set cB : ℝ := h * g * lam / (2 * (g + h * (lam + Λ))) with hcB
  have hcB0 : 0 < cB := by positivity
  set c : ℝ := min (m₀ / 2) cB with hc
  have hc0 : 0 < c := lt_min (by positivity) hcB0
  -- the remainder estimate at `t₀ + σ h`
  have hrem : ∀ σ : ℝ, σ ^ 2 = 1 →
      ‖U (t₀ + σ * h) - U t₀ - ((σ * h : ℝ) : ℂ) • (I • (U t₀ * L₀))‖ ≤ h * ρ := by
    intro σ hσ
    have hσ1 : |σ| = 1 := by
      have : |σ| ^ 2 = 1 := by rw [sq_abs, hσ]
      nlinarith [abs_nonneg σ]
    have hdist : dist (t₀ + σ * h) t₀ < h₁ := by
      rw [Real.dist_eq, add_sub_cancel_left, abs_mul, hσ1, one_mul, abs_of_pos hh0]
      exact hhh₁
    have := hlo hdist
    rw [add_sub_cancel_left, RCLike.real_smul_eq_coe_smul (K := ℂ), Real.norm_eq_abs, abs_mul,
      hσ1, one_mul, abs_of_pos hh0] at this
    exact this.trans_eq (mul_comm _ _)
  -- the first-order bound for `θ = α + φ`
  have hfirst : ∀ σ : ℝ, σ ^ 2 = 1 → ∀ φ : ℝ, |φ| ≤ δ → σ * Real.sin φ ≤ 0 → ∀ x,
      cB * ‖x‖ ≤ ‖(U (t₀ + σ * h) - exp (((α + φ : ℝ) : ℂ) * I) • 1) x‖ := by
    intro σ hσ φ hφ hsin x
    have hsplit : exp (((α + φ : ℝ) : ℂ) * I) = e * exp ((φ : ℂ) * I) := by
      rw [he_def, ← Complex.exp_add]; push_cast; ring_nf
    have hgap' : ∀ x ∈ K₀ᗮ, g * ‖x‖ ≤ ‖(U t₀ - (e * exp ((φ : ℂ) * I)) • 1) x‖ := by
      rw [← hsplit]; exact hgap φ (hφ.trans hδη)
    rw [hsplit]
    exact norm_ge_of_first_order hU₀ he K₀ heig hσ
      (by rw [Complex.exp_ofReal_mul_I_im]; exact hsin) (hrem σ hσ) hpos le_rfl hh0.le hg hlam
      hρ0.le le_rfl hhs' hgap' x
  refine ⟨δ, hδ0, hδ1, h, hh0, hhh₀, c, hc0, ?_, ?_, ?_⟩
  · intro t ht x
    have hdist : dist t t₀ < h₂ := by
      rw [Real.dist_eq]
      exact lt_of_le_of_lt (abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩) hhh₂
    have hU : ‖U t - U t₀‖ ≤ m₀ / 2 := by
      have := hcont hdist
      rw [dist_eq_norm] at this
      exact this.le
    have hsplit : (U t - w • 1) x = (U t₀ - w • 1) x + (U t - U t₀) x := by
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply]
      abel
    have h3 : ‖(U t₀ - w • 1) x‖ - ‖(U t - U t₀) x‖ ≤ ‖(U t - w • 1) x‖ := by
      have := norm_sub_norm_le ((U t₀ - w • 1) x) (-(U t - U t₀) x)
      rwa [norm_neg, sub_neg_eq_add, ← hsplit] at this
    have h4 : ‖(U t - U t₀) x‖ ≤ m₀ / 2 * ‖x‖ :=
      ((U t - U t₀).le_opNorm _).trans (mul_le_mul_of_nonneg_right hU (norm_nonneg _))
    have h5 : c * ‖x‖ ≤ m₀ / 2 * ‖x‖ :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)
    linarith [hzero x]
  · intro θ hθ x
    have h1 := hfirst (-1) (by norm_num) (θ - α)
      (by rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2])
      (by
        have : 0 ≤ Real.sin (θ - α) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_gt_three])
        linarith) x
    rw [show t₀ + -1 * h = t₀ - h by ring, show α + (θ - α) = θ by ring] at h1
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)).trans h1
  · intro θ hθ x
    have h1 := hfirst 1 (by norm_num) (θ - α)
      (by rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2])
      (by
        have : 0 ≤ Real.sin (-(θ - α)) := Real.sin_nonneg_of_nonneg_of_le_pi
          (by linarith [hθ.2]) (by linarith [hθ.1, Real.pi_gt_three])
        rw [Real.sin_neg] at this
        linarith) x
    rw [show t₀ + 1 * h = t₀ + h by ring, show α + (θ - α) = θ by ring] at h1
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)).trans h1

end

section

/-! ## Basic facts about admissible positive unitary paths -/

open scoped InnerProductSpace
open MeasureTheory Set Metric Filter Topology Complex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma traceNorm_neg (T : E →L[ℂ] E) : traceNorm (-T) = traceNorm T := by
  simp only [traceNorm, ContinuousLinearMap.neg_apply, inner_neg_right, enorm_neg]

omit [CompleteSpace E] in
lemma traceNorm_sub_comm (A B : E →L[ℂ] E) : traceNorm (A - B) = traceNorm (B - A) := by
  rw [← neg_sub, traceNorm_neg]

namespace IsAdmissiblePath

variable {b : ℝ} {U : ℝ → E →L[ℂ] E}

/-- `U' = i U L` within `[0, b]`. -/
theorem hasDerivWithinAt (hU : IsAdmissiblePath b U) :
    ∀ t ∈ Icc 0 b, HasDerivWithinAt U (I • (U t * generator U b t)) (Icc 0 b) t := by
  intro t ht
  have hd : HasDerivWithinAt U (derivWithin U (Icc 0 b) t) (Icc 0 b) t :=
    ((hU.contDiff.differentiableOn one_ne_zero) t ht).hasDerivWithinAt
  convert hd using 1
  have hu := Unitary.mul_star_self_of_mem (hU.unitary t ht)
  simp only [generator]
  rw [mul_smul_comm, ← mul_assoc, hu, one_mul, smul_smul, show I * -I = 1 by
    rw [mul_neg, I_mul_I, neg_neg], one_smul]

/-- The generator is continuous in operator norm. -/
theorem continuousOn_generator (hU : IsAdmissiblePath b U) :
    ContinuousOn (generator U b) (Icc 0 b) := by
  intro t ht
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 := hU.traceNorm_continuous t ht
  have h2 : Tendsto (fun s => ENNReal.ofReal ‖generator U b s - generator U b t‖)
      (𝓝[Icc 0 b] t) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => bot_le)
      (fun s => ofReal_norm_le_traceNorm _)
  have h3 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h2
  simpa [Function.comp_def, ENNReal.toReal_ofReal (norm_nonneg _)] using h3

/-- `U(t) - 1` is a compact operator. -/
theorem isCompactOperator (hU : IsAdmissiblePath b U) {t : ℝ} (ht : t ∈ Icc 0 b) :
    IsCompactOperator ((U t - 1 : E →L[ℂ] E) : E → E) := by
  have hfin : ∀ n : ℕ, ∃ (K : Submodule ℂ E) (_ : FiniteDimensional ℂ K)
      (V : ℝ → K →L[ℂ] K), ‖K.subtypeL ∘L V t ∘L K.orthogonalProjection +
        (1 - K.starProjection) - U t‖ ≤ 1 / (n + 1) := by
    intro n
    obtain ⟨K, hK, V, -, -, -, -, hV⟩ := exists_finite_approx_path hU.pos.le hU.start
      hU.unitary hU.hasDerivWithinAt hU.continuousOn_generator hU.posTraceClass ⊥
      (by positivity : (0 : ℝ) < 1 / (n + 1))
    exact ⟨K, hK, V, hV t ht⟩
  choose K hK V hV using hfin
  set F : ℕ → E →L[ℂ] E := fun n => (K n).subtypeL ∘L V n t ∘L (K n).orthogonalProjection +
    (1 - (K n).starProjection) - 1 with hF
  have hFc : ∀ n, IsCompactOperator (F n) := by
    intro n
    haveI := hK n
    have h1 := isCompactOperator_subtypeL_comp (K n) (V n t)
    have h2 := isCompactOperator_subtypeL_comp (K n) 1
    have : F n = (K n).subtypeL ∘L V n t ∘L (K n).orthogonalProjection -
        (K n).subtypeL ∘L 1 ∘L (K n).orthogonalProjection := by
      ext x
      simp only [hF, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply,
        Submodule.subtypeL_apply]
      rw [Submodule.starProjection_apply]
      abel
    rw [this]
    exact h1.sub h2
  refine isCompactOperator_of_tendsto (l := atTop) (F := F) ?_ (Eventually.of_forall hFc)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  rw [hF]
  simp only [sub_sub_sub_cancel_right]
  exact hV n

/-- `∫₀ᵇ tr L(t) dt < ∞`. -/
theorem lintegral_posTrace_lt_top (hU : IsAdmissiblePath b U) :
    ∫⁻ t in Icc 0 b, posTrace (generator U b t) < ⊤ := by
  have hcont : ContinuousOn (fun t => posTrace (generator U b t)) (Icc 0 b) := by
    intro t ht
    have hfin := (hU.posTraceClass t ht).2
    have hτ := hU.traceNorm_continuous t ht
    have hτ' : Tendsto (fun s => traceNorm (generator U b t - generator U b s))
        (𝓝[Icc 0 b] t) (𝓝 0) := by
      simpa only [traceNorm_sub_comm (generator U b t)] using hτ
    have hup : Tendsto (fun s => posTrace (generator U b t) + traceNorm
        (generator U b s - generator U b t)) (𝓝[Icc 0 b] t)
        (𝓝 (posTrace (generator U b t))) := by
      simpa using tendsto_const_nhds.add hτ
    have hlow : Tendsto (fun s => posTrace (generator U b t) - traceNorm
        (generator U b t - generator U b s)) (𝓝[Icc 0 b] t)
        (𝓝 (posTrace (generator U b t))) := by
      have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := posTrace (generator U b t))) hτ'
        (Or.inl hfin.ne)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun s => ?_)
      (fun s => posTrace_le_add_traceNorm _ _)
    exact tsub_le_iff_right.2 (posTrace_le_add_traceNorm _ _)
  obtain ⟨t₁, ht₁, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hU.pos.le) hcont
  calc ∫⁻ t in Icc 0 b, posTrace (generator U b t)
      ≤ ∫⁻ _ in Icc 0 b, posTrace (generator U b t₁) :=
        setLIntegral_mono' measurableSet_Icc fun t ht => hmax ht
    _ = posTrace (generator U b t₁) * volume (Icc 0 b) := setLIntegral_const _ _
    _ < ⊤ := by
        rw [Real.volume_Icc]
        exact ENNReal.mul_lt_top (hU.posTraceClass t₁ ht₁).2 ENNReal.ofReal_lt_top

end IsAdmissiblePath

end

section

/-! ## Finite-dimensional approximation on an abstract finite-dimensional space -/

open scoped InnerProductSpace
open Set Metric Filter Topology Complex

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Finite-dimensional approximation**, on an abstract space. -/
theorem exists_finite_approx_path_gen {U L : ℝ → E →L[ℂ] E} {b : ℝ} (hb : 0 ≤ b)
    (hU0 : U 0 = 1) (hUu : ∀ t ∈ Icc 0 b, U t ∈ unitary (E →L[ℂ] E))
    (hUd : ∀ t ∈ Icc 0 b, HasDerivWithinAt U (I • (U t * L t)) (Icc 0 b) t)
    (hLc : ContinuousOn L (Icc 0 b)) (hLp : ∀ t ∈ Icc 0 b, IsPosTraceClass (L t))
    (X₀ : Submodule ℂ E) [FiniteDimensional ℂ X₀] {ε : ℝ} (hε : 0 < ε) :
    ∃ (F : Type u) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℂ F)
      (_ : FiniteDimensional ℂ F) (ι : F →L[ℂ] E) (π : E →L[ℂ] F) (V : ℝ → F →L[ℂ] F),
      (∀ x y, ⟪ι x, y⟫_ℂ = ⟪x, π y⟫_ℂ) ∧ (∀ x, π (ι x) = x) ∧ (∀ v ∈ X₀, ι (π v) = v) ∧
      V 0 = 1 ∧ (∀ t ∈ Icc 0 b, V t ∈ unitary (F →L[ℂ] F)) ∧
      (∀ t ∈ Icc 0 b, HasDerivWithinAt V (I • (V t * (π ∘L L t ∘L ι))) (Icc 0 b) t) ∧
      ∀ t ∈ Icc 0 b, ‖ι ∘L V t ∘L π + (1 - ι ∘L π) - U t‖ ≤ ε := by
  obtain ⟨K, hK, V, hX, hV0, hVu, hVd, hcl⟩ :=
    exists_finite_approx_path hb hU0 hUu hUd hLc hLp X₀ hε
  refine ⟨K, inferInstance, inferInstance, hK, K.subtypeL, K.orthogonalProjection, V,
    fun x y => ?_, fun x => ?_, fun v hv => ?_, hV0, hVu, hVd, hcl⟩
  · simp only [Submodule.subtypeL_apply]
    exact (Submodule.inner_orthogonalProjection_eq_of_mem_left x y).symm
  · simp
  · simpa using (Submodule.starProjection_eq_self_iff (K := K)).2 (hX hv)

end

section

/-! ## Transferring a spectral window to a finite-dimensional approximation -/

open scoped InnerProductSpace ComplexConjugate
open Module Set Metric Filter Topology Complex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

omit [CompleteSpace E] [FiniteDimensional ℂ F] in
/-- `ι` is an isometry when `π ι = 1` and `π` is the adjoint of `ι`. -/
lemma norm_isometry_apply {ι : F →L[ℂ] E} {π : E →L[ℂ] F}
    (hadj : ∀ x y, ⟪ι x, y⟫_ℂ = ⟪x, π y⟫_ℂ) (hπι : ∀ x, π (ι x) = x) (y : F) :
    ‖ι y‖ = ‖y‖ := by
  have h : ⟪ι y, ι y⟫_ℂ = ⟪y, y⟫_ℂ := by rw [hadj, hπι]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖ι y‖ ^ 2 = ‖y‖ ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h'

omit [CompleteSpace E] [FiniteDimensional ℂ F] in
lemma inner_compress_gen {ι : F →L[ℂ] E} {π : E →L[ℂ] F}
    (hadj : ∀ x y, ⟪ι x, y⟫_ℂ = ⟪x, π y⟫_ℂ) (A : E →L[ℂ] E) (x y : F) :
    ⟪x, (π ∘L A ∘L ι) y⟫_ℂ = ⟪ι x, A (ι y)⟫_ℂ := by
  rw [hadj]; rfl

lemma compress_gen_isSelfAdjoint {ι : F →L[ℂ] E} {π : E →L[ℂ] F}
    (hadj : ∀ x y, ⟪ι x, y⟫_ℂ = ⟪x, π y⟫_ℂ) {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (π ∘L A ∘L ι) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hA ⊢
  intro x y
  simp only [ContinuousLinearMap.coe_coe]
  rw [← inner_conj_symm, inner_compress_gen hadj, inner_compress_gen hadj, ← inner_conj_symm (ι x)]
  have := hA (ι y) (ι x)
  simp only [ContinuousLinearMap.coe_coe] at this
  rw [this]

omit [CompleteSpace E] [FiniteDimensional ℂ F] in
/-- Comparison of `V - z` on `F` with `U - z` on `E`, when `ι V π + (1 - ι π)` is
`ε`-close to `U`. -/
lemma norm_sub_smul_le_of_approx {ι : F →L[ℂ] E} {π : E →L[ℂ] F}
    (hadj : ∀ x y, ⟪ι x, y⟫_ℂ = ⟪x, π y⟫_ℂ) (hπι : ∀ x, π (ι x) = x)
    (V : F →L[ℂ] F) (U : E →L[ℂ] E) {ε : ℝ}
    (h : ‖ι ∘L V ∘L π + (1 - ι ∘L π) - U‖ ≤ ε) (z : ℂ) (y : F) :
    ‖(U - z • 1) (ι y)‖ ≤ ‖(V - z • 1) y‖ + ε * ‖y‖ ∧
      ‖(V - z • 1) y‖ ≤ ‖(U - z • 1) (ι y)‖ + ε * ‖y‖ := by
  set D := ι ∘L V ∘L π + (1 - ι ∘L π) - U with hD
  have hDy : ‖D (ι y)‖ ≤ ε * ‖y‖ := by
    rw [← norm_isometry_apply hadj hπι y]
    exact (D.le_opNorm _).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))
  have hkey : ι ((V - z • 1) y) = (U - z • 1) (ι y) + D (ι y) := by
    simp only [hD, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.smul_apply, hπι, map_sub, map_smul]
    abel
  have hn : ‖(V - z • 1) y‖ = ‖(U - z • 1) (ι y) + D (ι y)‖ := by
    rw [← hkey, norm_isometry_apply hadj hπι]
  rw [hn]
  constructor
  · have := norm_sub_norm_le ((U - z • 1) (ι y)) ((U - z • 1) (ι y) + D (ι y))
    rw [sub_add_cancel_left, norm_neg] at this
    linarith
  · exact (norm_add_le _ _).trans (by linarith)

omit [CompleteSpace E] [FiniteDimensional ℂ F] in
/-- A lower bound for `U - z` beyond the approximation error rules out the eigenvalue `z`
for `V`. -/
lemma apply_ne_zero_of_approx {ι : F →L[ℂ] E} {π : E →L[ℂ] F}
    (hadj : ∀ x y, ⟪ι x, y⟫_ℂ = ⟪x, π y⟫_ℂ) (hπι : ∀ x, π (ι x) = x)
    (V : F →L[ℂ] F) (U : E →L[ℂ] E) {ε c : ℝ}
    (h : ‖ι ∘L V ∘L π + (1 - ι ∘L π) - U‖ ≤ ε)
    (hεc : ε < c) {z : ℂ} (hU : ∀ x, c * ‖x‖ ≤ ‖(U - z • 1) x‖) (y : F) (hy : y ≠ 0) :
    (V - z • 1) y ≠ 0 := by
  intro h0
  have h1 := (norm_sub_smul_le_of_approx hadj hπι V U h z y).1
  rw [h0, norm_zero, zero_add] at h1
  have h2 := hU (ι y)
  rw [norm_isometry_apply hadj hπι] at h2
  have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
  nlinarith

/-- **Crossings near a crossing of `U`, for an approximating finite-dimensional path.** -/
theorem crossings_near_of_approx {ι : F →L[ℂ] E} {π : E →L[ℂ] F}
    (hadj : ∀ x y, ⟪ι x, y⟫_ℂ = ⟪x, π y⟫_ℂ) (hπι : ∀ x, π (ι x) = x)
    {V : ℝ → F →L[ℂ] F} {U L : ℝ → E →L[ℂ] E} {b ε δ h c α t₀ : ℝ}
    (hVu : ∀ t ∈ Icc 0 b, V t ∈ unitary (F →L[ℂ] F))
    (hVd : ∀ t ∈ Icc 0 b, HasDerivWithinAt V (I • (V t * (π ∘L L t ∘L ι))) (Icc 0 b) t)
    (hLp : ∀ t ∈ Icc 0 b, IsPosTraceClass (L t))
    (hclose : ∀ t ∈ Icc 0 b, ‖ι ∘L V t ∘L π + (1 - ι ∘L π) - U t‖ ≤ ε)
    (hwin : Icc (t₀ - h) (t₀ + h) ⊆ Icc 0 b) (hh : 0 < h) (hδ : 0 < δ) (hεc : ε < c)
    (hεδ : ε ^ 2 < 2 - 2 * Real.cos δ)
    (hA : ∀ t ∈ Icc (t₀ - h) (t₀ + h), ∀ x, c * ‖x‖ ≤ ‖(U t - exp ((α + δ : ℝ) * I) • 1) x‖)
    (hB : ∀ θ ∈ Icc α (α + δ), ∀ x, c * ‖x‖ ≤ ‖(U (t₀ - h) - exp ((θ : ℂ) * I) • 1) x‖)
    (hB' : ∀ θ ∈ Icc (α - δ) α, ∀ x, c * ‖x‖ ≤ ‖(U (t₀ + h) - exp ((θ : ℂ) * I) • 1) x‖)
    (K₀ : Submodule ℂ E) [FiniteDimensional ℂ K₀] (hK₀K : ∀ v ∈ K₀, ι (π v) = v)
    (hK₀ : ∀ v ∈ K₀, (U t₀ - exp (α * I) • 1) v = 0) :
    ∃ s : Finset ℝ, ↑s ⊆ Ioo (t₀ - h) (t₀ + h) ∧
      (finrank ℂ K₀ : ℕ∞) ≤ ∑ t ∈ s, crossingMult V α t := by
  have hl : t₀ - h ∈ Icc (t₀ - h) (t₀ + h) := ⟨le_rfl, by linarith⟩
  have hr : t₀ + h ∈ Icc (t₀ - h) (t₀ + h) := ⟨by linarith, le_rfl⟩
  have hb : t₀ + h ≤ b := (hwin hr).2
  have h0 : 0 ≤ t₀ - h := (hwin hl).1
  set Y : Submodule ℂ F := K₀.comap (ι : F →ₗ[ℂ] E) with hY
  have hYrank : finrank ℂ K₀ ≤ finrank ℂ Y := by
    let f : K₀ →ₗ[ℂ] Y :=
      { toFun := fun v => ⟨π v, by
          show ι (π v) ∈ K₀
          rw [hK₀K v v.2]; exact v.2⟩
        map_add' := fun v w => by ext; simp
        map_smul' := fun a v => by ext; simp }
    refine LinearMap.finrank_le_finrank_of_injective (f := f) fun v w hvw => ?_
    have h1 : π v = π w := congrArg Subtype.val hvw
    have h2 := congrArg ι h1
    rw [hK₀K v v.2, hK₀K w w.2] at h2
    exact Subtype.ext h2
  have hVc : ContinuousOn V (Icc (t₀ - h) (t₀ + h)) := fun t ht =>
    ((hVd t (hwin ht)).continuousWithinAt).mono hwin
  have hVd' : ∀ t ∈ Ico (t₀ - h) (t₀ + h),
      HasDerivWithinAt V (I • (V t * (π ∘L L t ∘L ι))) (Ici t) t := fun t ht =>
    (hVd t (hwin (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE (lt_of_lt_of_le ht.2 hb))
        (Icc_subset_Icc_left (h0.trans ht.1)))
  have hAs : ∀ t ∈ Ico (t₀ - h) (t₀ + h), IsSelfAdjoint (π ∘L L t ∘L ι) := fun t ht =>
    compress_gen_isSelfAdjoint hadj (hLp t (hwin (Ico_subset_Icc_self ht))).1.isSelfAdjoint
  have hApos : ∀ t ∈ Ico (t₀ - h) (t₀ + h), ∀ x : F,
      0 ≤ RCLike.re ⟪x, (π ∘L L t ∘L ι) x⟫_ℂ := fun t ht x => by
    rw [inner_compress_gen hadj]
    exact (hLp t (hwin (Ico_subset_Icc_self ht))).1.re_inner_nonneg_right _
  have hgA : ∀ t ∈ Icc (t₀ - h) (t₀ + h), ∀ y : F, y ≠ 0 →
      (V t - exp ((α + δ : ℝ) * I) • 1) y ≠ 0 := fun t ht y hy =>
    apply_ne_zero_of_approx hadj hπι (V t) (U t) (hclose t (hwin ht)) hεc (hA t ht) y hy
  have hgB : ∀ θ ∈ Icc α (α + δ), ∀ y : F, y ≠ 0 →
      (V (t₀ - h) - exp ((θ : ℂ) * I) • 1) y ≠ 0 := fun θ hθ y hy =>
    apply_ne_zero_of_approx hadj hπι (V (t₀ - h)) (U (t₀ - h)) (hclose _ (hwin hl)) hεc
      (hB θ hθ) y hy
  have hgB' : ∀ θ ∈ Icc (α - δ) α, ∀ y : F, y ≠ 0 →
      (V (t₀ + h) - exp ((θ : ℂ) * I) • 1) y ≠ 0 := fun θ hθ y hy =>
    apply_ne_zero_of_approx hadj hπι (V (t₀ + h)) (U (t₀ + h)) (hclose _ (hwin hr)) hεc
      (hB' θ hθ) y hy
  have hYa : ∀ y ∈ Y, ‖(V t₀ - exp (α * I) • 1) y‖ ≤ ε * ‖y‖ := fun y hy => by
    have h1 := (norm_sub_smul_le_of_approx hadj hπι (V t₀) (U t₀)
      (hclose t₀ (hwin ⟨by linarith, by linarith⟩)) (exp (α * I)) y).2
    rwa [hK₀ (ι y) hy, norm_zero, zero_add] at h1
  obtain ⟨s, hs, hcount⟩ := crossings_in_window (n := finrank ℂ F) rfl
    (by linarith : t₀ - h ≤ t₀) (by linarith : t₀ ≤ t₀ + h)
    (fun t ht => hVu t (hwin ht)) hVc hVd' hAs hApos hδ hgA hgB hgB' hεδ Y hYa
  exact ⟨s, hs, le_trans (by exact_mod_cast hYrank) hcount⟩

end

section

/-! ## The crossing-cost estimate -/

open scoped InnerProductSpace
open Module Set Metric Filter Topology Complex MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Ky Fan partial traces do not increase under compression by an isometry. -/
lemma kyFan_compress_gen_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {ι : F →L[ℂ] E} {π : E →L[ℂ] F}
    (hadj : ∀ x y, ⟪ι x, y⟫_ℂ = ⟪x, π y⟫_ℂ) (hπι : ∀ x, π (ι x) = x) (m : ℕ) (A : E →L[ℂ] E) :
    kyFan m (π ∘L A ∘L ι) ≤ kyFan m A := by
  refine iSup_le fun n => iSup_le fun hn => iSup_le fun v => iSup_le fun hv => ?_
  have hw : Orthonormal ℂ (fun i => ι (v i)) := by
    rw [orthonormal_iff_ite] at hv ⊢
    intro i j
    rw [hadj, hπι, hv i j]
  refine le_trans (le_of_eq ?_) (le_iSup_of_le n (le_iSup_of_le hn (le_iSup_of_le _
    (le_iSup_of_le hw le_rfl))))
  unfold diagSum
  simp only [inner_compress_gen hadj]

omit [CompleteSpace E] in
/-- The crossing multiplicity is the dimension of the (finite-dimensional) eigenspace. -/
lemma crossingMult_eq_finrank {U : ℝ → E →L[ℂ] E} {α t : ℝ}
    [FiniteDimensional ℂ (LinearMap.ker
      ((U t - exp (α * I) • (1 : E →L[ℂ] E) : E →L[ℂ] E) : E →ₗ[ℂ] E))] :
    crossingMult U α t = (finrank ℂ (LinearMap.ker
      ((U t - exp (α * I) • (1 : E →L[ℂ] E) : E →L[ℂ] E) : E →ₗ[ℂ] E)) : ℕ∞) := by
  unfold crossingMult
  rw [← Module.finrank_eq_rank]
  simp

omit [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] in
/-- Disjoint windows around finitely many interior points. -/
lemma exists_sep_radius {s : Finset ℝ} {b : ℝ} (hs : ↑s ⊆ Ioo 0 b) :
    ∃ h₀ > 0, (∀ t ∈ s, Icc (t - h₀) (t + h₀) ⊆ Icc 0 b) ∧
      ∀ t ∈ s, ∀ t' ∈ s, t ≠ t' → 2 * h₀ < |t - t'| := by
  have h1 : ∀ t ∈ s, ∀ᶠ h in 𝓝[>] (0 : ℝ), Icc (t - h) (t + h) ⊆ Icc 0 b := by
    intro t ht
    obtain ⟨h0, hb⟩ := hs ht
    have : ∀ᶠ h in 𝓝 (0 : ℝ), h < min t (b - t) :=
      eventually_lt_nhds (lt_min h0 (by linarith))
    filter_upwards [nhdsWithin_le_nhds this] with h hh
    intro x hx
    exact ⟨by linarith [hx.1, min_le_left t (b - t)], by linarith [hx.2, min_le_right t (b - t)]⟩
  have h2 : ∀ p ∈ s ×ˢ s, ∀ᶠ h in 𝓝[>] (0 : ℝ), p.1 ≠ p.2 → 2 * h < |p.1 - p.2| := by
    intro p _
    by_cases hne : p.1 = p.2
    · exact Eventually.of_forall fun _ h => absurd hne h
    · have hpos : 0 < |p.1 - p.2| := abs_pos.2 (sub_ne_zero.2 hne)
      have : ∀ᶠ h in 𝓝 (0 : ℝ), h < |p.1 - p.2| / 2 := eventually_lt_nhds (half_pos hpos)
      filter_upwards [nhdsWithin_le_nhds this] with h hh _
      linarith
  have h3 := (Filter.eventually_all_finset s).2 h1
  have h4 := (Filter.eventually_all_finset (s ×ˢ s)).2 h2
  obtain ⟨h, ⟨hA, hB⟩, hpos⟩ := ((h3.and h4).and eventually_mem_nhdsWithin).exists
  exact ⟨h, hpos, hA, fun t ht t' ht' hne => hB (t, t') (Finset.mem_product.2 ⟨ht, ht'⟩) hne⟩

omit [CompleteSpace E] in
lemma finiteDimensional_finset_sup_of {ι' : Type*} (s : Finset ι') (K : ι' → Submodule ℂ E)
    (hK : ∀ t ∈ s, FiniteDimensional ℂ (K t)) :
    FiniteDimensional ℂ ↥(s.sup K : Submodule ℂ E) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sup_empty]; infer_instance
  | insert a s ha ih =>
    rw [Finset.sup_insert]
    haveI := hK a (Finset.mem_insert_self a s)
    haveI := ih fun t ht => hK t (Finset.mem_insert_of_mem ht)
    infer_instance

/-- **Crossing cost.** For finitely many crossing times in `(0, b)` with total
multiplicity at least `m`, `α m ≤ ∫₀ᵇ Φ_m(L)`. -/
theorem phase_cost_finset {b : ℝ} {U : ℝ → E →L[ℂ] E} (hU : IsAdmissiblePath b U)
    {α : ℝ} (hα0 : 0 < α) (hα : α < 2 * Real.pi) (s : Finset ℝ) (hs : ↑s ⊆ Ioo 0 b)
    (m : ℕ) (hm : (m : ℕ∞) ≤ ∑ t ∈ s, crossingMult U α t) :
    ENNReal.ofReal (α * m) ≤ ∫⁻ t in Icc 0 b, kyFan m (generator U b t) := by
  classical
  set L := generator U b with hLdef
  have hb0 : 0 ≤ b := hU.pos.le
  have heα : exp (α * I) ≠ 1 := by
    intro h
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    have him := congrArg Complex.im hn
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, add_zero, mul_one, Complex.intCast_re,
      Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat] at him
    replace him : α = n * (2 * Real.pi) := by
      rw [him]; congr 1; simp
    have h1 : (0 : ℝ) < n := by
      by_contra hc; push_neg at hc; nlinarith [Real.pi_pos]
    have h2 : (n : ℝ) < 1 := by
      by_contra hc; push_neg at hc; nlinarith [Real.pi_pos]
    have h1' : (0 : ℤ) < n := by exact_mod_cast h1
    have h2' : n < (1 : ℤ) := by exact_mod_cast h2
    omega
  set K₀ : ℝ → Submodule ℂ E :=
    fun t => LinearMap.ker ((U t - exp (α * I) • (1 : E →L[ℂ] E) : E →L[ℂ] E) : E →ₗ[ℂ] E)
    with hK₀def
  have hK₀fin : ∀ t ∈ Icc 0 b, FiniteDimensional ℂ (K₀ t) := fun t ht =>
    finiteDimensional_ker_of_isCompactOperator (hU.isCompactOperator ht) heα
  have hmult : ∀ t ∈ Icc 0 b, crossingMult U α t = (finrank ℂ (K₀ t) : ℕ∞) := fun t ht => by
    haveI := hK₀fin t ht
    exact crossingMult_eq_finrank
  obtain ⟨h₀, hh₀, hwin₀, hsep⟩ := exists_sep_radius hs
  -- local windows around the crossing times
  have hloc : ∀ t ∈ s, ∃ δ > 0, δ ≤ 1 ∧ ∃ r > 0, r ≤ h₀ ∧ ∃ c > 0,
      (∀ u ∈ Icc (t - r) (t + r), ∀ x, c * ‖x‖ ≤ ‖(U u - exp ((α + δ : ℝ) * I) • 1) x‖) ∧
      (∀ θ ∈ Icc α (α + δ), ∀ x, c * ‖x‖ ≤ ‖(U (t - r) - exp ((θ : ℂ) * I) • 1) x‖) ∧
      (∀ θ ∈ Icc (α - δ) α, ∀ x, c * ‖x‖ ≤ ‖(U (t + r) - exp ((θ : ℂ) * I) • 1) x‖) := by
    intro t ht
    have htI : t ∈ Ioo 0 b := hs ht
    have htIcc := Ioo_subset_Icc_self htI
    haveI := hK₀fin t htIcc
    have hd : HasDerivAt U (I • (U t * L t)) t :=
      (hU.hasDerivWithinAt t htIcc).hasDerivAt (Icc_mem_nhds htI.1 htI.2)
    exact exists_local_window hd (hU.unitary t htIcc) (hU.isCompactOperator htIcc) heα
      (hU.strictPos t ⟨htI.1, htI.2.le⟩) (K₀ t) (fun v => by simp [K₀]) hh₀
  choose! δ hδ hδ1 r hr0 hrh₀ c hc hA hB hB' using hloc
  -- the approximation error
  have hε : ∀ t ∈ s, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < c t ∧ ε ^ 2 < 2 - 2 * Real.cos (δ t) := by
    intro t ht
    have hcos : 0 < 2 - 2 * Real.cos (δ t) := by
      have : Real.cos (δ t) < 1 := by
        rw [← Real.cos_zero]
        exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl
          (by linarith [hδ1 t ht, Real.pi_gt_three]) (hδ t ht)
      linarith
    have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), ε < c t := eventually_lt_nhds (hc t ht)
    have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), ε ^ 2 < 2 - 2 * Real.cos (δ t) := by
      have : Tendsto (fun ε : ℝ => ε ^ 2) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_pow 2).tendsto (0 : ℝ)
      exact this.eventually (eventually_lt_nhds hcos)
    exact nhdsWithin_le_nhds (h1.and h2)
  obtain ⟨ε, hεs, hεpos⟩ :=
    (((Filter.eventually_all_finset s).2 hε).and eventually_mem_nhdsWithin).exists
  -- the finite-dimensional approximation
  set X₀ : Submodule ℂ E := s.sup K₀ with hX₀
  haveI : FiniteDimensional ℂ X₀ := finiteDimensional_finset_sup_of s K₀
    (fun t ht => hK₀fin t (Ioo_subset_Icc_self (hs ht)))
  obtain ⟨F, _, _, _, ι, π, V, hadj, hπι, hX, hV0, hVu, hVd, hcl⟩ :=
    exists_finite_approx_path_gen hb0 hU.start hU.unitary hU.hasDerivWithinAt
      hU.continuousOn_generator hU.posTraceClass X₀ (show (0 : ℝ) < ε from hεpos)
  -- crossings of `V` near each crossing of `U`
  have hnear : ∀ t ∈ s, ∃ st : Finset ℝ, ↑st ⊆ Ioo (t - r t) (t + r t) ∧
      (finrank ℂ (K₀ t) : ℕ∞) ≤ ∑ u ∈ st, crossingMult V α u := by
    intro t ht
    haveI := hK₀fin t (Ioo_subset_Icc_self (hs ht))
    have hwin : Icc (t - r t) (t + r t) ⊆ Icc 0 b :=
      (Icc_subset_Icc (by linarith [hrh₀ t ht]) (by linarith [hrh₀ t ht])).trans (hwin₀ t ht)
    exact crossings_near_of_approx hadj hπι hVu hVd hU.posTraceClass hcl hwin (hr0 t ht)
      (hδ t ht) (hεs t ht).1 (hεs t ht).2 (hA t ht) (hB t ht) (hB' t ht) (K₀ t)
      (fun v hv => hX v (Finset.le_sup (f := K₀) ht hv))
      (fun v hv => by simpa [K₀] using hv)
  choose! st hst hstc using hnear
  have hdisj : (s : Set ℝ).PairwiseDisjoint st := by
    intro t ht t' ht' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro u hu hu'
    have h1 := hst t ht hu
    have h2 := hst t' ht' hu'
    have h3 := hsep t ht t' ht' hne
    have h4 := hrh₀ t ht
    have h5 := hrh₀ t' ht'
    have h6 : |t - u| < r t := abs_sub_lt_iff.2 ⟨by linarith [h1.1], by linarith [h1.2]⟩
    have h7 : |u - t'| < r t' := abs_sub_lt_iff.2 ⟨by linarith [h2.2], by linarith [h2.1]⟩
    have h8 := abs_sub_le t u t'
    linarith
  have hSsub : ↑(s.biUnion st) ⊆ Ioo 0 b := by
    intro u hu
    rw [Finset.coe_biUnion] at hu
    simp only [Set.mem_iUnion, Finset.mem_coe] at hu
    obtain ⟨t, ht, hut⟩ := hu
    have h1 := hst t ht hut
    have h2 := hwin₀ t ht ⟨le_rfl, by linarith [hh₀]⟩
    have h3 := hwin₀ t ht ⟨by linarith [hh₀], le_rfl⟩
    have h4 := hrh₀ t ht
    exact ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h3.2]⟩
  have hcount : (m : ℕ∞) ≤ crossingCount V α (Ioo 0 b) := by
    calc (m : ℕ∞) ≤ ∑ t ∈ s, crossingMult U α t := hm
      _ = ∑ t ∈ s, (finrank ℂ (K₀ t) : ℕ∞) :=
          Finset.sum_congr rfl fun t ht => hmult t (Ioo_subset_Icc_self (hs ht))
      _ ≤ ∑ t ∈ s, ∑ u ∈ st t, crossingMult V α u := Finset.sum_le_sum hstc
      _ = ∑ u ∈ s.biUnion st, crossingMult V α u := (Finset.sum_biUnion hdisj).symm
      _ ≤ crossingCount V α (Ioo 0 b) := le_iSup₂_of_le (s.biUnion st) hSsub le_rfl
  -- the finite-dimensional estimate
  have hVc : ContinuousOn V (Icc 0 b) := fun t ht => (hVd t ht).continuousWithinAt
  have hVd' : ∀ t ∈ Ico 0 b, HasDerivWithinAt V (I • (V t * (π ∘L L t ∘L ι))) (Ici t) t :=
    fun t ht => (hVd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1))
  have hAs : ∀ t ∈ Ico 0 b, IsSelfAdjoint (π ∘L L t ∘L ι) := fun t ht =>
    compress_gen_isSelfAdjoint hadj (hU.posTraceClass t (Ico_subset_Icc_self ht)).1.isSelfAdjoint
  have hΦ : Continuous fun A : E →L[ℂ] E => π ∘L A ∘L ι := by fun_prop
  have hAc : ContinuousOn (fun t => π ∘L L t ∘L ι) (Icc 0 b) :=
    hΦ.comp_continuousOn hU.continuousOn_generator
  have hApos : ∀ t ∈ Icc 0 b, ∀ x, 0 ≤ RCLike.re ⟪x, (π ∘L L t ∘L ι) x⟫_ℂ := fun t ht x => by
    rw [inner_compress_gen hadj]
    exact (hU.posTraceClass t ht).1.re_inner_nonneg_right _
  have hAsp : ∀ t ∈ Ioo 0 b, ∀ x, x ≠ 0 → 0 < RCLike.re ⟪x, (π ∘L L t ∘L ι) x⟫_ℂ :=
    fun t ht x hx => by
      rw [inner_compress_gen hadj]
      refine hU.strictPos t ⟨ht.1, ht.2.le⟩ (ι x) fun h => hx ?_
      have := norm_isometry_apply hadj hπι x
      rw [h, norm_zero] at this
      exact norm_eq_zero.1 this.symm
  have hfd := (phase_cost_finiteDim hb0 hVu hV0 hVc hVd' hAs hAc hApos hAsp hα0 hα).2 m hcount
  exact hfd.trans (lintegral_mono fun t => kyFan_compress_gen_le hadj hπι m _)

/-- For an admissible positive unitary path and `0 < α < 2π`, the
number of crossings `c_α` in `(0, b)` is finite, and for every `1 ≤ m ≤ c_α`,
`α m ≤ ∫₀ᵇ Φ_m(L(t)) dt`. -/
theorem phase_cost {b : ℝ} {U : ℝ → E →L[ℂ] E} (hU : IsAdmissiblePath b U)
    {α : ℝ} (hα0 : 0 < α) (hα : α < 2 * Real.pi) :
    crossingCount U α (Ioo 0 b) < ⊤ ∧
      ∀ m : ℕ, 1 ≤ m → (m : ℕ∞) ≤ crossingCount U α (Ioo 0 b) →
        ENNReal.ofReal (α * m) ≤ ∫⁻ t in Icc 0 b, kyFan m (generator U b t) := by
  have hclaim : ∀ m : ℕ, 1 ≤ m → (m : ℕ∞) ≤ crossingCount U α (Ioo 0 b) →
      ENNReal.ofReal (α * m) ≤ ∫⁻ t in Icc 0 b, kyFan m (generator U b t) := by
    intro m hm1 hm
    have hlt : ((m - 1 : ℕ) : ℕ∞) < crossingCount U α (Ioo 0 b) :=
      lt_of_lt_of_le (by exact_mod_cast Nat.sub_lt hm1 one_pos) hm
    unfold crossingCount at hlt
    obtain ⟨s, hs⟩ := lt_iSup_iff.1 hlt
    obtain ⟨hsI, hs'⟩ := lt_iSup_iff.1 hs
    refine phase_cost_finset hU hα0 hα s hsI m ?_
    have h1 := Order.add_one_le_of_lt hs'
    have e : ((m - 1 : ℕ) : ℕ∞) + 1 = m := by
      rw [← Nat.cast_one (R := ℕ∞), ← Nat.cast_add, Nat.sub_add_cancel hm1]
    rwa [e] at h1
  refine ⟨?_, hclaim⟩
  by_contra htop
  rw [not_lt, top_le_iff] at htop
  have hB := hU.lintegral_posTrace_lt_top
  obtain ⟨m, hm⟩ := exists_nat_gt ((∫⁻ t in Icc 0 b, posTrace (generator U b t)).toReal / α)
  have hm0 : (0 : ℝ) < m := lt_of_le_of_lt (div_nonneg ENNReal.toReal_nonneg hα0.le) hm
  have hm1 : 1 ≤ m := by
    have : 0 < m := by exact_mod_cast hm0
    omega
  have h1 := hclaim m hm1 (by rw [htop]; exact le_top)
  have h2 : ∫⁻ t in Icc 0 b, kyFan m (generator U b t) ≤
      ∫⁻ t in Icc 0 b, posTrace (generator U b t) :=
    lintegral_mono fun t => kyFan_le_posTrace m _
  have h3 : ∫⁻ t in Icc 0 b, posTrace (generator U b t) < ENNReal.ofReal (α * m) := by
    rw [← ENNReal.ofReal_toReal hB.ne]
    refine (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_
    rw [div_lt_iff₀ hα0] at hm
    linarith
  exact absurd (h1.trans h2) (not_le.2 h3)

end

section

/-! ## Eigenvalues in the lower semicircle -/

open scoped InnerProductSpace ComplexConjugate
open Module Set Metric Filter Topology Complex MeasureTheory

section FiniteDim

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

omit [FiniteDimensional ℂ F] in
/-- `Im ⟨y, W y⟩` in an eigenbasis of `W`. -/
lemma im_inner_apply_eq_sum {n : ℕ} (e : OrthonormalBasis (Fin n) ℂ F) (W : F →L[ℂ] F)
    (lam : Fin n → ℝ) (he : ∀ k, W (e k) = exp (lam k * I) • e k) (y : F) :
    (⟪y, W y⟫_ℂ).im = ∑ k, Real.sin (lam k) * ‖⟪e k, y⟫_ℂ‖ ^ 2 := by
  have h1 : ∀ k, ⟪e k, W y⟫_ℂ = exp (lam k * I) * ⟪e k, y⟫_ℂ := by
    intro k
    conv_lhs => rw [← e.sum_repr' y]
    simp only [map_sum, map_smul, he, smul_smul, inner_sum, inner_smul_right,
      OrthonormalBasis.inner_eq_ite, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    ring
  rw [← e.sum_inner_mul_inner y (W y), Complex.im_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h1]
  have hz : ⟪y, e k⟫_ℂ = (starRingEnd ℂ) ⟪e k, y⟫_ℂ := (inner_conj_symm _ _).symm
  rw [hz]
  have : (starRingEnd ℂ) ⟪e k, y⟫_ℂ * (exp (lam k * I) * ⟪e k, y⟫_ℂ) =
      exp (lam k * I) * ((‖⟪e k, y⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_left_comm, Complex.conj_mul']
    push_cast
    ring
  rw [this, Complex.im_mul_ofReal, exp_ofReal_mul_I_im]

/-- If `Im ⟨y, V(b) y⟩ < 0` on a
subspace `Y`, then for `p ≤ dim Y`, `π p ≤ ∫₀ᵇ Φ_p(A)`. -/
theorem lower_phases_finiteDim {V A : ℝ → F →L[ℂ] F} {b : ℝ} (hb : 0 ≤ b)
    (hVu : ∀ t ∈ Icc 0 b, V t ∈ unitary (F →L[ℂ] F)) (hV0 : V 0 = 1)
    (hVc : ContinuousOn V (Icc 0 b))
    (hVd : ∀ t ∈ Ico 0 b, HasDerivWithinAt V (I • (V t * A t)) (Ici t) t)
    (hAs : ∀ t ∈ Ico 0 b, IsSelfAdjoint (A t)) (hAc : ContinuousOn A (Icc 0 b))
    (hApos : ∀ t ∈ Icc 0 b, ∀ x, 0 ≤ RCLike.re ⟪x, A t x⟫_ℂ)
    (Y : Submodule ℂ F) (hY : ∀ y ∈ Y, y ≠ 0 → (⟪y, V b y⟫_ℂ).im < 0)
    {p : ℕ} (hp : p ≤ finrank ℂ Y) :
    ENNReal.ofReal (Real.pi * p) ≤ ∫⁻ t in Icc 0 b, kyFan p (A t) := by
  classical
  set n := finrank ℂ F with hn
  obtain ⟨lam, hl⟩ := exists_phaseLift (n := n) rfl hb hVu hV0 hVc hVd hAs
  haveI : Nonempty (OrthonormalBasis (Fin n) ℂ F) :=
    ⟨(stdOrthonormalBasis ℂ F).reindex (finCongr hn.symm)⟩
  have hmono : ∀ k, MonotoneOn (lam k) (Icc 0 b) := by
    choose! u hu using hl.2.2.2
    exact fun k => monotoneOn_of_rderiv_nonneg (hl.2.1 k) (fun t ht => hu t ht k)
      (fun t ht => hApos t (Ico_subset_Icc_self ht) _)
  have hnn : ∀ k, 0 ≤ lam k b := fun k => by
    have := hmono k ⟨le_rfl, hb⟩ ⟨hb, le_rfl⟩ hb
    rwa [hl.1 k] at this
  obtain ⟨e, he⟩ := hl.2.2.1 b ⟨hb, le_rfl⟩
  set J := Finset.univ.filter fun k => Real.sin (lam k b) < 0 with hJ
  -- at least `dim Y` branches end in the lower semicircle
  have hJcard : finrank ℂ Y ≤ J.card := by
    by_contra hcon
    push_neg at hcon
    set W := obSpan e Jᶜ with hW
    have hWr : finrank ℂ W = n - J.card := by
      rw [hW, finrank_obSpan, Finset.card_compl, Fintype.card_fin]
    have hJn : J.card ≤ n := by
      simpa using Finset.card_le_univ J
    have hnd : ¬ Disjoint Y W := by
      intro hd
      have := Submodule.finrank_add_finrank_le_of_disjoint hd
      omega
    rw [Submodule.disjoint_def] at hnd
    push_neg at hnd
    obtain ⟨y, hyY, hyW, hy0⟩ := hnd
    have h1 := hY y hyY hy0
    rw [im_inner_apply_eq_sum e (V b) (fun k => lam k b) he y] at h1
    have h2 : 0 ≤ ∑ k, Real.sin (lam k b) * ‖⟪e k, y⟫_ℂ‖ ^ 2 := by
      refine Finset.sum_nonneg fun k _ => ?_
      by_cases hk : k ∈ J
      · rw [inner_eq_zero_of_mem_obSpan e Jᶜ hyW (by simpa using hk)]
        simp
      · have : 0 ≤ Real.sin (lam k b) := by
          simpa [hJ] using hk
        positivity
    linarith
  obtain ⟨J', hJ'J, hJ'⟩ := Finset.exists_subset_card_eq (hp.trans hJcard)
  -- each such branch has travelled more than `π`
  have hpi : ∀ k ∈ J, Real.pi ≤ lam k b := by
    intro k hk
    by_contra hcon
    push_neg at hcon
    have := Real.sin_nonneg_of_nonneg_of_le_pi (hnn k) hcon.le
    have hk' := (Finset.mem_filter.1 hk).2
    linarith
  have hcost : Real.pi * p ≤ ∫ t in (0 : ℝ)..b, (kyFan J'.card (A t)).toReal := by
    calc Real.pi * p = ∑ _k ∈ J', Real.pi := by simp [hJ', mul_comm]
      _ ≤ ∑ k ∈ J', lam k b := Finset.sum_le_sum fun k hk => hpi k (hJ'J hk)
      _ ≤ _ := hl.sum_le_integral rfl hb hApos hAc J'
  have hgc : ContinuousOn (fun t => (kyFan J'.card (A t)).toReal) (Icc 0 b) :=
    (lipschitzWith_kyFan_toReal _).continuous.comp_continuousOn hAc
  have hint : ENNReal.ofReal (∫ t in (0 : ℝ)..b, (kyFan J'.card (A t)).toReal) =
      ∫⁻ t in Icc 0 b, kyFan J'.card (A t) := by
    rw [intervalIntegral.integral_of_le hb, ← integral_Icc_eq_integral_Ioc,
      ofReal_integral_eq_lintegral_ofReal hgc.integrableOn_Icc
        (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)]
    exact lintegral_congr fun t => ENNReal.ofReal_toReal (kyFan_ne_top _ _)
  rw [← hJ']
  calc ENNReal.ofReal (Real.pi * J'.card) ≤ ENNReal.ofReal (∫ t in (0 : ℝ)..b,
        (kyFan J'.card (A t)).toReal) := ENNReal.ofReal_le_ofReal (hJ' ▸ hcost)
    _ = ∫⁻ t in Icc 0 b, kyFan J'.card (A t) := hint

end FiniteDim

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- At each time `t ∈ [0, b]`, an admissible positive unitary path
has at most `B/π` eigenvalues, counted with multiplicity, in the open lower semicircle
`{e^{iθ} : π < θ < 2π}`, where `B = ∫₀ᵇ tr L(s) ds`: for any orthonormal family of `p`
eigenvectors of `U(t)` with eigenvalues `e^{iθ_j}`, `π < θ_j < 2π`, we have `π p ≤ B`. -/
theorem lower_eigenvalues_card_le {b : ℝ} {U : ℝ → E →L[ℂ] E} (hU : IsAdmissiblePath b U)
    {t : ℝ} (ht : t ∈ Icc 0 b) {p : ℕ} (u : Fin p → E) (hu : Orthonormal ℂ u)
    (θ : Fin p → ℝ) (hθ : ∀ j, θ j ∈ Ioo Real.pi (2 * Real.pi))
    (heig : ∀ j, U t (u j) = exp (θ j * I) • u j) :
    ENNReal.ofReal (Real.pi * p) ≤ ∫⁻ s in Icc 0 b, posTrace (generator U b s) := by
  classical
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · simp
  set L := generator U b with hLdef
  have hb0 : 0 ≤ b := hU.pos.le
  have hsin : ∀ j, Real.sin (θ j) < 0 := fun j => by
    have := Real.sin_pos_of_pos_of_lt_pi (x := θ j - Real.pi) (by linarith [(hθ j).1])
      (by linarith [(hθ j).2])
    rw [Real.sin_sub_pi] at this
    linarith
  have hne : (Finset.univ : Finset (Fin p)).Nonempty := ⟨⟨0, hp0⟩, Finset.mem_univ _⟩
  set κ := Finset.univ.inf' hne (fun j => -Real.sin (θ j)) with hκdef
  have hκ : 0 < κ := (Finset.lt_inf'_iff hne).2 fun j _ => by linarith [hsin j]
  have hκle : ∀ j, κ ≤ -Real.sin (θ j) := fun j => Finset.inf'_le _ (Finset.mem_univ j)
  set X₀ : Submodule ℂ E := Submodule.span ℂ (Set.range u) with hX₀
  haveI : FiniteDimensional ℂ X₀ := FiniteDimensional.span_of_finite ℂ (Set.finite_range u)
  obtain ⟨F, _, _, _, ι, π, V, hadj, hπι, hX, hV0, hVu, hVd, hcl⟩ :=
    exists_finite_approx_path_gen hb0 hU.start hU.unitary hU.hasDerivWithinAt
      hU.continuousOn_generator hU.posTraceClass X₀ (half_pos hκ)
  have hιu : ∀ j, ι (π (u j)) = u j := fun j => hX _ (Submodule.subset_span ⟨j, rfl⟩)
  have hinnι : ∀ x y : F, ⟪ι x, ι y⟫_ℂ = ⟪x, y⟫_ℂ := fun x y => by rw [hadj, hπι]
  have hon : Orthonormal ℂ (fun j => π (u j)) := by
    rw [orthonormal_iff_ite] at hu ⊢
    intro i j
    rw [← hinnι, hιu, hιu, hu i j]
  set Y : Submodule ℂ F := Submodule.span ℂ (Set.range fun j => π (u j)) with hY
  have hYrank : finrank ℂ Y = p := by
    rw [hY, finrank_span_eq_card hon.linearIndependent, Fintype.card_fin]
  -- the quadratic form `Im ⟨y, V(t) y⟩` is negative on `Y`
  have hYneg : ∀ y ∈ Y, y ≠ 0 → (⟪y, V t y⟫_ℂ).im < 0 := by
    intro y hy hy0
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hy
    set y := ∑ j, c j • π (u j) with hydef
    have hιy : ι y = ∑ j, c j • u j := by
      simp only [hydef, map_sum, map_smul, hιu]
    set Ũ := ι ∘L V t ∘L π + (1 - ι ∘L π) with hŨ
    have key1 : ⟪y, V t y⟫_ℂ = ⟪ι y, Ũ (ι y)⟫_ℂ := by
      simp only [hŨ, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hπι, sub_self, add_zero,
        hinnι]
    have key2 : (⟪ι y, Ũ (ι y)⟫_ℂ).im ≤ (⟪ι y, U t (ι y)⟫_ℂ).im + κ / 2 * ‖y‖ ^ 2 := by
      have h1 : ⟪ι y, Ũ (ι y)⟫_ℂ = ⟪ι y, U t (ι y)⟫_ℂ + ⟪ι y, (Ũ - U t) (ι y)⟫_ℂ := by
        rw [ContinuousLinearMap.sub_apply, inner_sub_right]; ring
      have h2 : (⟪ι y, (Ũ - U t) (ι y)⟫_ℂ).im ≤ κ / 2 * ‖y‖ ^ 2 := by
        have hny : ‖ι y‖ = ‖y‖ := norm_isometry_apply hadj hπι y
        calc (⟪ι y, (Ũ - U t) (ι y)⟫_ℂ).im ≤ ‖⟪ι y, (Ũ - U t) (ι y)⟫_ℂ‖ :=
              Complex.im_le_norm _
          _ ≤ ‖ι y‖ * ‖(Ũ - U t) (ι y)‖ := norm_inner_le_norm _ _
          _ ≤ ‖ι y‖ * (‖Ũ - U t‖ * ‖ι y‖) := by
              gcongr; exact (Ũ - U t).le_opNorm _
          _ ≤ ‖ι y‖ * (κ / 2 * ‖ι y‖) := by
              gcongr; exact hcl t ht
          _ = κ / 2 * ‖y‖ ^ 2 := by rw [hny]; ring
      rw [h1, Complex.add_im]
      linarith
    have key3 : (⟪ι y, U t (ι y)⟫_ℂ).im ≤ -κ * ‖y‖ ^ 2 := by
      have hUx : U t (ι y) = ∑ j, (c j * exp (θ j * I)) • u j := by
        rw [hιy, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, heig, smul_smul]
      have hny : ‖y‖ ^ 2 = ∑ j, ‖c j‖ ^ 2 := by
        rw [← norm_isometry_apply hadj hπι y, hιy, @norm_sq_eq_re_inner ℂ, hu.inner_sum, RCLike.re_to_complex,
          Complex.re_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Complex.conj_mul']
        norm_cast
      rw [hUx, hιy, hu.inner_sum, Complex.im_sum, hny, Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      have : (starRingEnd ℂ) (c j) * (c j * exp (θ j * I)) =
          exp (θ j * I) * ((‖c j‖ ^ 2 : ℝ) : ℂ) := by
        rw [← mul_assoc, Complex.conj_mul']
        push_cast
        ring
      rw [this, Complex.im_mul_ofReal, exp_ofReal_mul_I_im]
      have := hκle j
      nlinarith [sq_nonneg ‖c j‖]
    have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy0
    rw [key1]
    nlinarith [sq_pos_of_pos hy']
  -- the finite-dimensional estimate on `[0, t]`
  have hsub : Icc 0 t ⊆ Icc 0 b := Icc_subset_Icc_right ht.2
  have hVc : ContinuousOn V (Icc 0 t) := fun s hs => ((hVd s (hsub hs)).continuousWithinAt).mono hsub
  have hVd' : ∀ s ∈ Ico 0 t, HasDerivWithinAt V (I • (V s * (π ∘L L s ∘L ι))) (Ici s) s :=
    fun s hs => (hVd s (hsub (Ico_subset_Icc_self hs))).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE (lt_of_lt_of_le hs.2 ht.2)) (Icc_subset_Icc_left hs.1))
  have hAs : ∀ s ∈ Ico 0 t, IsSelfAdjoint (π ∘L L s ∘L ι) := fun s hs =>
    compress_gen_isSelfAdjoint hadj (hU.posTraceClass s (hsub (Ico_subset_Icc_self hs))).1.isSelfAdjoint
  have hΦ : Continuous fun A : E →L[ℂ] E => π ∘L A ∘L ι := by fun_prop
  have hAc : ContinuousOn (fun s => π ∘L L s ∘L ι) (Icc 0 t) :=
    hΦ.comp_continuousOn (hU.continuousOn_generator.mono hsub)
  have hApos : ∀ s ∈ Icc 0 t, ∀ x, 0 ≤ RCLike.re ⟪x, (π ∘L L s ∘L ι) x⟫_ℂ := fun s hs x => by
    rw [inner_compress_gen hadj]
    exact (hU.posTraceClass s (hsub hs)).1.re_inner_nonneg_right _
  have hfd := lower_phases_finiteDim ht.1 (fun s hs => hVu s (hsub hs)) hV0 hVc hVd' hAs hAc
    hApos Y hYneg hYrank.ge
  calc ENNReal.ofReal (Real.pi * p) ≤ ∫⁻ s in Icc 0 t, kyFan p (π ∘L L s ∘L ι) := hfd
    _ ≤ ∫⁻ s in Icc 0 t, posTrace (L s) := lintegral_mono fun s =>
        (kyFan_compress_gen_le hadj hπι p _).trans (kyFan_le_posTrace p _)
    _ ≤ ∫⁻ s in Icc 0 b, posTrace (L s) := lintegral_mono_set hsub

end

section

/-! ## Auxiliary results on crossings forced by an arc -/

open scoped InnerProductSpace ComplexConjugate
open Module Set Metric Filter Topology Complex MeasureTheory

section Chord

/-- `θ ↦ e^{iθ}` is injective on every half-open interval of length `2π`. -/
lemma exp_mul_I_injOn_Ico (c : ℝ) :
    InjOn (fun θ : ℝ => exp (θ * I)) (Ico c (c + 2 * Real.pi)) := by
  intro a ha b hb hab
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 hab
  have him := congrArg Complex.im hm
  simp at him
  have hpi := Real.pi_pos
  rcases lt_trichotomy m 0 with h | h | h
  · have : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.mpr h
    nlinarith [ha.1, hb.2]
  · subst h; simpa using him
  · have : (1 : ℝ) ≤ m := by exact_mod_cast h
    nlinarith [ha.2, hb.1]

/-- `‖e^{iδ} - 1‖ ≤ δ` for `δ ≥ 0`. -/
lemma norm_exp_mul_I_sub_one_le {δ : ℝ} (hδ : 0 ≤ δ) : ‖exp (δ * I) - 1‖ ≤ δ := by
  have h := norm_exp_mul_I_sub_sq δ 0
  rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero, sub_zero] at h
  have hc := Real.one_sub_sq_div_two_le_cos (x := δ)
  by_contra hcon
  push_neg at hcon
  nlinarith [norm_nonneg (exp (δ * I) - 1)]

/-- Chords of the unit circle increase with the arc length on `[0, π]`. -/
lemma norm_exp_mul_I_sub_le {a b δ : ℝ} (h : |a - b| ≤ δ) (hδ : δ ≤ Real.pi) :
    ‖exp (a * I) - exp (b * I)‖ ≤ ‖exp (δ * I) - 1‖ := by
  have hab := norm_exp_mul_I_sub_sq a b
  have hd := norm_exp_mul_I_sub_sq δ 0
  rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero, sub_zero] at hd
  have hcos : Real.cos δ ≤ Real.cos (a - b) := by
    rw [← Real.cos_abs (a - b)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hδ h
  by_contra hcon
  push_neg at hcon
  nlinarith [norm_nonneg (exp (δ * I) - 1), norm_nonneg (exp (a * I) - exp (b * I))]

/-- `‖e^{ia} - e^{ib}‖ = ‖e^{i(b - a)} - 1‖`. -/
lemma norm_exp_mul_I_sub_exp_mul_I (a b : ℝ) :
    ‖exp (a * I) - exp (b * I)‖ = ‖exp ((b - a : ℝ) * I) - 1‖ := by
  have h1 := norm_exp_mul_I_sub_sq a b
  have h2 := norm_exp_mul_I_sub_sq (b - a) 0
  rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero, sub_zero] at h2
  have h3 : Real.cos (b - a) = Real.cos (a - b) := by rw [← Real.cos_neg, neg_sub]
  rw [h3, ← h1] at h2
  exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2).symm

/-- `e^{iθ} ≠ 1` for `0 < θ < 2π`. -/
lemma exp_mul_I_ne_one {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 2 * Real.pi) : exp (θ * I) ≠ 1 := by
  intro h
  have := exp_mul_I_injOn_Ico 0 (show θ ∈ Ico 0 (0 + 2 * Real.pi) from ⟨h0.le, by linarith⟩)
    (show (0 : ℝ) ∈ Ico 0 (0 + 2 * Real.pi) from ⟨le_rfl, by linarith [Real.pi_pos]⟩)
    (by simpa using h)
  linarith

/-- Every nonempty open interval contains a point outside a given countable set. -/
lemma exists_mem_Ioo_not_mem_of_countable {S : Set ℝ} (hS : S.Countable) {x y : ℝ}
    (hxy : x < y) : ∃ t ∈ Ioo x y, t ∉ S := by
  obtain ⟨t, ht, htI⟩ := (hS.dense_compl ℝ).exists_mem_open isOpen_Ioo (nonempty_Ioo.2 hxy)
  exact ⟨t, htI, ht⟩

/-- Disjoint closed windows inside an open interval around finitely many points. -/
lemma exists_sep_radius_Ioo {s : Finset ℝ} {a b : ℝ} (hs : ↑s ⊆ Ioo a b) :
    ∃ h₀ > 0, (∀ t ∈ s, Icc (t - h₀) (t + h₀) ⊆ Ioo a b) ∧
      ∀ t ∈ s, ∀ t' ∈ s, t ≠ t' → 2 * h₀ < |t - t'| := by
  have h1 : ∀ t ∈ s, ∀ᶠ h in 𝓝[>] (0 : ℝ), Icc (t - h) (t + h) ⊆ Ioo a b := by
    intro t ht
    obtain ⟨h0, hb⟩ := hs ht
    have : ∀ᶠ h in 𝓝 (0 : ℝ), h < min (t - a) (b - t) :=
      eventually_lt_nhds (lt_min (by linarith) (by linarith))
    filter_upwards [nhdsWithin_le_nhds this] with h hh
    intro x hx
    exact ⟨by linarith [hx.1, min_le_left (t - a) (b - t)],
      by linarith [hx.2, min_le_right (t - a) (b - t)]⟩
  have h2 : ∀ p ∈ s ×ˢ s, ∀ᶠ h in 𝓝[>] (0 : ℝ), p.1 ≠ p.2 → 2 * h < |p.1 - p.2| := by
    intro p _
    by_cases hne : p.1 = p.2
    · exact Eventually.of_forall fun _ h => absurd hne h
    · have hpos : 0 < |p.1 - p.2| := abs_pos.2 (sub_ne_zero.2 hne)
      have : ∀ᶠ h in 𝓝 (0 : ℝ), h < |p.1 - p.2| / 2 := eventually_lt_nhds (half_pos hpos)
      filter_upwards [nhdsWithin_le_nhds this] with h hh _
      linarith
  have h3 := (Filter.eventually_all_finset s).2 h1
  have h4 := (Filter.eventually_all_finset (s ×ˢ s)).2 h2
  obtain ⟨h, ⟨hA, hB⟩, hpos⟩ := ((h3.and h4).and eventually_mem_nhdsWithin).exists
  exact ⟨h, hpos, hA, fun t ht t' ht' hne => hB (t, t') (Finset.mem_product.2 ⟨ht, ht'⟩) hne⟩

end Chord

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- If `e^{iα}` is not an eigenvalue at time `t`, there is no crossing at `t`. -/
lemma crossingMult_eq_zero_of_injective {U : ℝ → E →L[ℂ] E} {α t : ℝ}
    (h : ∀ y, y ≠ 0 → (U t - exp (α * I) • 1) y ≠ 0) : crossingMult U α t = 0 := by
  have hker : LinearMap.ker ((U t - exp (α * I) • (1 : E →L[ℂ] E) : E →L[ℂ] E) : E →ₗ[ℂ] E)
      = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro y hy
    by_contra hy0
    exact h y hy0 hy
  have e : crossingMult U α t = (Module.rank ℂ (LinearMap.ker
      ((U t - exp (α * I) • (1 : E →L[ℂ] E) : E →L[ℂ] E) : E →ₗ[ℂ] E))).toENat := rfl
  rw [e, hker, rank_bot, map_zero]

omit [CompleteSpace E] in
/-- Uniform lower bounds on compact parameter sets. -/
lemma exists_uniform_lower_bound {K : Set ℝ} (hK : IsCompact K) {T : ℝ → E →L[ℂ] E}
    (hT : ContinuousOn T K) (hloc : ∀ p ∈ K, ∃ g > 0, ∀ x, g * ‖x‖ ≤ ‖T p x‖) :
    ∃ c > 0, ∀ p ∈ K, ∀ x, c * ‖x‖ ≤ ‖T p x‖ := by
  by_contra H
  push_neg at H
  choose p hpK x hx using fun n : ℕ => H (1 / ((n : ℝ) + 1)) (by positivity)
  obtain ⟨p₀, hp₀K, φ, hφ, hlim⟩ := hK.tendsto_subseq hpK
  obtain ⟨g, hg, hgx⟩ := hloc p₀ hp₀K
  have hTlim : Tendsto (fun n => T (p (φ n))) atTop (𝓝 (T p₀)) :=
    (hT p₀ hp₀K).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => hpK _⟩)
  have h1 : ∀ᶠ n in atTop, ‖T (p (φ n)) - T p₀‖ < g / 2 :=
    (tendsto_iff_norm_sub_tendsto_zero.1 hTlim).eventually (gt_mem_nhds (half_pos hg))
  have h2 : ∀ᶠ n in atTop, 1 / ((φ n : ℝ) + 1) < g / 2 :=
    (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop).eventually
      (gt_mem_nhds (half_pos hg))
  obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
  have hy := hx (φ n)
  have hy0 : x (φ n) ≠ 0 := by
    intro h; rw [h] at hy; simp at hy
  have hny : 0 < ‖x (φ n)‖ := norm_pos_iff.2 hy0
  have h3 := hgx (x (φ n))
  have h4 : ‖T p₀ (x (φ n))‖ ≤ ‖T (p (φ n)) (x (φ n))‖ +
      ‖T (p (φ n)) - T p₀‖ * ‖x (φ n)‖ := by
    have e : T p₀ (x (φ n)) = T (p (φ n)) (x (φ n)) - (T (p (φ n)) - T p₀) (x (φ n)) := by
      simp
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add_right ((T (p (φ n)) - T p₀).le_opNorm _) _)
  have h5 : ‖T (p (φ n)) - T p₀‖ * ‖x (φ n)‖ ≤ g / 2 * ‖x (φ n)‖ :=
    mul_le_mul_of_nonneg_right hn1.le (norm_nonneg _)
  have h6 : 1 / ((φ n : ℝ) + 1) * ‖x (φ n)‖ ≤ g / 2 * ‖x (φ n)‖ :=
    mul_le_mul_of_nonneg_right hn2.le (norm_nonneg _)
  nlinarith

omit [CompleteSpace E] in
/-- If `U₀ - 1` is compact and `e^{iθ} ≠ 1` is not an eigenvalue of `U₀`, then `U₀ - e^{iθ}` is
bounded below. -/
lemma exists_lower_bound_of_injective {U₀ : E →L[ℂ] E}
    (hC : IsCompactOperator ((U₀ - 1 : E →L[ℂ] E) : E → E)) {θ : ℝ} (hθ : exp (θ * I) ≠ 1)
    (hinj : ∀ x, U₀ x = exp (θ * I) • x → x = 0) :
    ∃ g > 0, ∀ x, g * ‖x‖ ≤ ‖(U₀ - exp (θ * I) • 1) x‖ := by
  obtain ⟨η, hη, g, hg, hgap⟩ := exists_gap_of_isCompactOperator hC hθ ⊥
    (fun v hv => by
      rw [Submodule.mem_bot]
      refine hinj v ?_
      simpa [sub_eq_zero] using hv)
  refine ⟨g, hg, fun x => ?_⟩
  simpa using hgap 0 (by simpa using hη.le) x (by simp)

omit [CompleteSpace E] in
/-- A subspace on which `U₀ - w` is smaller than a gap on `K₀ᗮ` has dimension at most
`dim K₀`. -/
lemma finrank_le_of_gap {U₀ : E →L[ℂ] E} {w : ℂ} (K₀ : Submodule ℂ E) [FiniteDimensional ℂ K₀]
    {g : ℝ} (hgap : ∀ x ∈ K₀ᗮ, g * ‖x‖ ≤ ‖(U₀ - w • 1) x‖) (Z : Submodule ℂ E)
    [FiniteDimensional ℂ Z] (hZ : ∀ z ∈ Z, z ≠ 0 → ‖(U₀ - w • 1) z‖ < g * ‖z‖) :
    finrank ℂ Z ≤ finrank ℂ K₀ := by
  let f : Z →ₗ[ℂ] K₀ := (K₀.orthogonalProjection : E →ₗ[ℂ] K₀).comp Z.subtype
  refine LinearMap.finrank_le_finrank_of_injective (f := f) ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  have hzK : (z : E) ∈ K₀ᗮ := by
    rw [← Submodule.orthogonalProjection_eq_zero_iff]
    exact hz
  by_contra hz0
  have hz0' : (z : E) ≠ 0 := fun h => hz0 (Subtype.ext h)
  have h1 := hgap z hzK
  have h2 := hZ z z.2 hz0'
  linarith

omit [CompleteSpace E] in
/-- On the span of an orthonormal family of eigenvectors of `T` whose eigenvalues are within `M`
of `c`, `‖(T - c) y‖ ≤ M ‖y‖`. -/
lemma norm_sub_smul_le_of_mem_span_eigen {ι : Type*} [Fintype ι] {v : ι → E}
    (hv : Orthonormal ℂ v) (T : E →L[ℂ] E) (z : ι → ℂ) (hTv : ∀ i, T (v i) = z i • v i) (c : ℂ)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i, ‖z i - c‖ ≤ M) {y : E}
    (hy : y ∈ Submodule.span ℂ (Set.range v)) : ‖(T - c • 1) y‖ ≤ M * ‖y‖ := by
  classical
  have hnorm : ∀ l : ι → ℂ, ‖∑ i, l i • v i‖ ^ 2 = ∑ i, ‖l i‖ ^ 2 := by
    intro l
    have h := hv.inner_sum l l Finset.univ
    rw [@norm_sq_eq_re_inner ℂ, h, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.conj_mul]
    norm_cast
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hy
  have hT : (T - c • 1) (∑ i, a i • v i) = ∑ i, (a i * (z i - c)) • v i := by
    simp only [map_sum, map_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hTv, smul_smul, sub_smul, mul_sub, smul_sub]
  rw [hT]
  have h1 := hnorm (fun i => a i * (z i - c))
  have h2 := hnorm a
  have h3 : ∑ i, ‖a i * (z i - c)‖ ^ 2 ≤ M ^ 2 * ∑ i, ‖a i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hM i) 2) (by positivity)
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [h1, mul_pow, h2]
  exact h3

end General

section FiniteDim

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- **Crossings in a window, upper bound (finite dimensions).** If `V(t) - e^{i(α+δ)}` is
injective on `[tl, tr]` and the generator is positive definite, then the crossings of `α` in
`[tl, tr)` are bounded by the dimension of a subspace on which `V(tr)` is within
`‖e^{iδ} - 1‖` of `e^{iα}`. -/
theorem crossings_in_window_le {n : ℕ} (hn : finrank ℂ F = n) {V A : ℝ → F →L[ℂ] F}
    {tl tr α δ : ℝ} (hle : tl ≤ tr)
    (hVu : ∀ t ∈ Icc tl tr, V t ∈ unitary (F →L[ℂ] F)) (hVc : ContinuousOn V (Icc tl tr))
    (hVd : ∀ t ∈ Ico tl tr, HasDerivWithinAt V (I • (V t * A t)) (Ici t) t)
    (hAs : ∀ t ∈ Ico tl tr, IsSelfAdjoint (A t))
    (hAsp : ∀ t ∈ Ico tl tr, ∀ x, x ≠ 0 → 0 < RCLike.re ⟪x, A t x⟫_ℂ)
    (hδ0 : 0 < δ) (hδ : δ ≤ Real.pi)
    (hgapA : ∀ t ∈ Icc tl tr, ∀ y, y ≠ 0 → (V t - exp ((α + δ : ℝ) * I) • 1) y ≠ 0)
    (s : Finset ℝ) (hs : ↑s ⊆ Ico tl tr) :
    ∃ Y : Submodule ℂ F, (∑ t ∈ s, crossingMult V α t) ≤ (finrank ℂ Y : ℕ∞) ∧
      ∀ y ∈ Y, ‖(V tr - exp (α * I) • 1) y‖ ≤ ‖exp (δ * I) - 1‖ * ‖y‖ := by
  classical
  have hpi := Real.pi_pos
  set β : ℝ := α + δ with hβ
  obtain ⟨φ, hφc, hφe, hφd, hφr⟩ := phase_window hn (β := β) hle hVu hVc hVd hAs
    (fun t ht => isUnit_one_sub_smul_of_injective (V t) β (hgapA t ht))
  haveI : Nonempty (OrthonormalBasis (Fin n) ℂ F) :=
    ⟨(stdOrthonormalBasis ℂ F).reindex (finCongr hn)⟩
  choose! u hu using hφd
  have hsm : ∀ k, StrictMonoOn (φ k) (Icc tl tr) := fun k =>
    strictMonoOn_of_rderiv_pos (hφc k).continuousOn (fun t ht => hu t ht k)
      (fun t ht => (hAsp t ht _ ((u t).orthonormal.ne_zero k)).le)
      (fun t ht => hAsp t (Ioo_subset_Ico_self ht) _ ((u t).orthonormal.ne_zero k))
  have hmult : ∀ t ∈ Icc tl tr, crossingMult V α t =
      ((Finset.univ.filter fun k => φ k t = α).card : ℕ∞) := by
    intro t ht
    obtain ⟨e, he⟩ := hφe t ht
    rw [crossingMult_eq_card e (fun k => φ k t) he]
    congr 2
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact exp_mul_I_injOn_Ico (β - 2 * Real.pi)
        ⟨(hφr k t).1.le, by linarith [(hφr k t).2]⟩ ⟨by linarith, by linarith⟩ h
    · intro h; rw [h]
  have htr : tr ∈ Icc tl tr := ⟨hle, le_rfl⟩
  set K := Finset.univ.filter fun k => φ k tr ∈ Ioo α β with hK
  -- counting the crossings
  set P := (s ×ˢ (Finset.univ : Finset (Fin n))).filter fun p => φ p.2 p.1 = α with hP
  have hPcard : P.card = ∑ t ∈ s, (Finset.univ.filter fun k => φ k t = α).card := by
    rw [hP, Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.card_filter]
  have hPK : P.card ≤ K.card := by
    refine Finset.card_le_card_of_injOn (fun p => p.2) ?_ ?_
    · intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
      obtain ⟨hpt, -⟩ := Finset.mem_product.1 hp1
      have htI := hs hpt
      show p.2 ∈ K
      rw [hK, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, (hφr _ _).2⟩
      rw [← hp2]
      exact hsm p.2 (Ico_subset_Icc_self htI) htr htI.2
    · intro p hp p' hp' hpp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hp)
      obtain ⟨hp1', hp2'⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hp')
      have hk : p.2 = p'.2 := hpp
      have ht : p.1 = p'.1 := by
        refine (hsm p.2).injOn (Ico_subset_Icc_self (hs (Finset.mem_product.1 hp1).1))
          (Ico_subset_Icc_self (hs (Finset.mem_product.1 hp1').1)) ?_
        rw [hp2, hk, hp2']
      exact Prod.ext ht hk
  -- the subspace
  obtain ⟨e, he⟩ := hφe tr htr
  let v : {k // k ∈ K} → F := fun k => e k
  have hv : Orthonormal ℂ v := e.orthonormal.comp _ Subtype.val_injective
  refine ⟨Submodule.span ℂ (Set.range v), ?_, fun y hy => ?_⟩
  · rw [finrank_span_eq_card hv.linearIndependent, Fintype.card_coe]
    calc ∑ t ∈ s, crossingMult V α t
        = ∑ t ∈ s, ((Finset.univ.filter fun k => φ k t = α).card : ℕ∞) :=
          Finset.sum_congr rfl fun t ht => hmult t (Ico_subset_Icc_self (hs ht))
      _ = ((P.card : ℕ) : ℕ∞) := by rw [hPcard]; push_cast; rfl
      _ ≤ (K.card : ℕ∞) := by exact_mod_cast hPK
  · refine norm_sub_smul_le_of_mem_span_eigen hv (V tr) (fun k => exp (φ k tr * I))
      (fun k => he k) _ (norm_nonneg _) (fun k => ?_) hy
    have hk := (Finset.mem_filter.1 k.2).2
    exact norm_exp_mul_I_sub_le
      (by rw [abs_le]; constructor <;> linarith [hk.1, hk.2]) hδ

/-- Let `V` be a unitary path on `[0, b]` with
`V(0) = 1` and positive generator, `0 ≤ a < b₁ ≤ b`, and `α < γ - w`, `γ + w ≤ q`,
`0 ≤ w ≤ π`.
If `V(a)` has no eigenvalue `e^{iθ}` with `θ ∈ [α, q]` and `‖(V(b₁) - e^{iγ}) y‖ ≤ ρ ‖y‖` on a
subspace `Y`, where `ρ² < 2 - 2 cos w`, then `V` has at least `dim Y` crossings of `α` in
`(a, b₁)`. -/
theorem crossings_of_arc_finiteDim {n : ℕ} (hn : finrank ℂ F = n) {V A : ℝ → F →L[ℂ] F}
    {b a b₁ α q γ w ρ : ℝ} (hb : 0 ≤ b)
    (hVu : ∀ t ∈ Icc 0 b, V t ∈ unitary (F →L[ℂ] F)) (hV0 : V 0 = 1)
    (hVc : ContinuousOn V (Icc 0 b))
    (hVd : ∀ t ∈ Ico 0 b, HasDerivWithinAt V (I • (V t * A t)) (Ici t) t)
    (hAs : ∀ t ∈ Ico 0 b, IsSelfAdjoint (A t))
    (hApos : ∀ t ∈ Icc 0 b, ∀ x, 0 ≤ RCLike.re ⟪x, A t x⟫_ℂ)
    (ha : 0 ≤ a) (hab : a < b₁) (hb₁ : b₁ ≤ b)
    (hαγ : α < γ - w) (hγq : γ + w ≤ q) (hw0 : 0 ≤ w)
    (hgap : ∀ θ ∈ Icc α q, ∀ y, y ≠ 0 → (V a - exp (θ * I) • 1) y ≠ 0)
    (Y : Submodule ℂ F) (hY : ∀ y ∈ Y, ‖(V b₁ - exp (γ * I) • 1) y‖ ≤ ρ * ‖y‖)
    (hρ : ρ ^ 2 < 2 - 2 * Real.cos w) :
    ∃ S : Finset ℝ, ↑S ⊆ Ioo a b₁ ∧ (finrank ℂ Y : ℕ∞) ≤ ∑ t ∈ S, crossingMult V α t := by
  classical
  have hpi := Real.pi_pos
  obtain ⟨lam, hl⟩ := exists_phaseLift hn hb hVu hV0 hVc hVd hAs
  obtain ⟨-, hlc, hle, hld⟩ := hl
  haveI : Nonempty (OrthonormalBasis (Fin n) ℂ F) :=
    ⟨(stdOrthonormalBasis ℂ F).reindex (finCongr hn)⟩
  choose! u hu using hld
  have hmono : ∀ k, MonotoneOn (lam k) (Icc 0 b) := fun k =>
    monotoneOn_of_rderiv_nonneg (hlc k) (fun t ht => hu t ht k)
      (fun t ht => hApos t (Ico_subset_Icc_self ht) _)
  have hb₁I : b₁ ∈ Icc 0 b := ⟨ha.trans hab.le, hb₁⟩
  have haI : a ∈ Icc 0 b := ⟨ha, hab.le.trans hb₁⟩
  obtain ⟨e, he⟩ := hle b₁ hb₁I
  have hcard := finrank_le_card_of_approx_eigen hn e (V b₁) (fun k => exp (lam k b₁ * I)) he
    (exp (γ * I)) Y hY
  set K := Finset.univ.filter fun k => ‖exp (lam k b₁ * I) - exp (γ * I)‖ ≤ ρ with hK
  have hcross : ∀ k ∈ K, ∃ t ∈ Ioo a b₁, exp (lam k t * I) = exp (α * I) := by
    intro k hk
    have hk' := (Finset.mem_filter.1 hk).2
    set d := lam k b₁ - γ with hd
    set j : ℤ := ⌊(d + Real.pi) / (2 * Real.pi)⌋ with hj
    have hj1 : (j : ℝ) ≤ (d + Real.pi) / (2 * Real.pi) := Int.floor_le _
    have hj2 : (d + Real.pi) / (2 * Real.pi) < j + 1 := Int.lt_floor_add_one _
    rw [le_div_iff₀ (by positivity)] at hj1
    rw [div_lt_iff₀ (by positivity)] at hj2
    set d' := d - j * (2 * Real.pi) with hd'
    have hd'1 : -Real.pi ≤ d' := by rw [hd']; linarith
    have hd'2 : d' < Real.pi := by rw [hd']; linarith
    have hcosd : Real.cos d' = Real.cos d := Real.cos_sub_int_mul_two_pi d j
    have hsq := norm_exp_mul_I_sub_sq (lam k b₁) γ
    have hρ0 : ‖exp (lam k b₁ * I) - exp (γ * I)‖ ^ 2 ≤ ρ ^ 2 := by
      have h0 := norm_nonneg (exp (lam k b₁ * I) - exp (γ * I))
      nlinarith [sq_nonneg (ρ - ‖exp (lam k b₁ * I) - exp (γ * I)‖)]
    have hcos_gt : Real.cos w < Real.cos d' := by
      rw [hcosd, hd]; nlinarith
    have hd'w : |d'| < w := by
      by_contra hcon
      push_neg at hcon
      have := Real.cos_le_cos_of_nonneg_of_le_pi hw0 (abs_le.2 ⟨hd'1, hd'2.le⟩) hcon
      rw [Real.cos_abs] at this
      linarith
    have hlb : γ - w + j * (2 * Real.pi) < lam k b₁ := by
      have := (abs_lt.1 hd'w).1; rw [hd', hd] at this; linarith
    have hub : lam k b₁ < γ + w + j * (2 * Real.pi) := by
      have := (abs_lt.1 hd'w).2; rw [hd', hd] at this; linarith
    -- the phase at `a` lies below `α + 2πj`
    have hla : lam k a < α + j * (2 * Real.pi) := by
      by_contra hcon
      push_neg at hcon
      have hle' : lam k a ≤ lam k b₁ := hmono k haI hb₁I hab.le
      obtain ⟨ea, hea⟩ := hle a haI
      set θ' := lam k a - j * (2 * Real.pi) with hθ'
      have hθ'I : θ' ∈ Icc α q := ⟨by rw [hθ']; linarith, by rw [hθ']; linarith⟩
      have hexp : exp (lam k a * I) = exp (θ' * I) := by
        rw [show (lam k a : ℂ) * I = (θ' : ℂ) * I + (j : ℂ) * (2 * Real.pi * I) by
          rw [hθ']; push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      refine hgap θ' hθ'I (ea k) (ea.orthonormal.ne_zero k) ?_
      rw [ContinuousLinearMap.sub_apply, hea k, hexp]
      simp
    obtain ⟨t, ht, htv⟩ := intermediate_value_Ioo hab.le ((hlc k).mono (Icc_subset_Icc ha hb₁))
      ⟨hla, by linarith⟩
    refine ⟨t, ht, ?_⟩
    rw [htv, show ((α + j * (2 * Real.pi) : ℝ) : ℂ) * I = (α : ℂ) * I + (j : ℂ) * (2 * Real.pi * I)
      by push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  choose! tk htk htkv using hcross
  refine ⟨K.image tk, fun t ht => ?_, ?_⟩
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ht)
    exact htk k hk
  have hle2 : (K.card : ℕ∞) ≤ ∑ t ∈ K.image tk, crossingMult V α t := by
    rw [Finset.card_eq_sum_card_image tk K]
    push_cast
    refine Finset.sum_le_sum fun t ht => ?_
    obtain ⟨k₀, hk₀, rfl⟩ := Finset.mem_image.1 ht
    have htI : tk k₀ ∈ Icc 0 b := ⟨ha.trans (htk k₀ hk₀).1.le, (htk k₀ hk₀).2.le.trans hb₁⟩
    obtain ⟨et, het⟩ := hle (tk k₀) htI
    rw [crossingMult_eq_card et (fun k => lam k (tk k₀)) het]
    norm_cast
    refine Finset.card_le_card fun k hk => ?_
    obtain ⟨hkK, hkt⟩ := Finset.mem_filter.1 hk
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    have := htkv k hkK
    rw [hkt] at this
    exact this
  exact le_trans (by exact_mod_cast hcard) hle2

end FiniteDim

end

section

/-! ## Gaps below `2π` and crossings forced by an arc -/

open scoped InnerProductSpace ComplexConjugate
open Module Set Metric Filter Topology Complex MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Eigenvectors of a unitary operator for distinct eigenvalues of modulus one are
orthogonal. -/
lemma inner_eq_zero_of_eigen_unitary {U : E →L[ℂ] E} (hU : U ∈ unitary (E →L[ℂ] E))
    {a c : ℂ} (ha : ‖a‖ = 1) (hac : a ≠ c) {x y : E} (hx : U x = a • x) (hy : U y = c • y) :
    ⟪x, y⟫_ℂ = 0 := by
  have h1 : ⟪U x, U y⟫_ℂ = ⟪x, y⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.mul_apply,
      ← ContinuousLinearMap.star_eq_adjoint, Unitary.star_mul_self_of_mem hU,
      ContinuousLinearMap.one_apply]
  rw [hx, hy, inner_smul_left, inner_smul_right, ← mul_assoc] at h1
  have hca : (starRingEnd ℂ) a * a = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]; simp
  have h2 : ((starRingEnd ℂ) a * c - 1) * ⟪x, y⟫_ℂ = 0 := by
    rw [sub_mul, h1, one_mul, sub_self]
  rcases mul_eq_zero.1 h2 with h | h
  · exfalso
    apply hac
    have : (starRingEnd ℂ) a * c = (starRingEnd ℂ) a * a := by rw [hca]; exact sub_eq_zero.1 h
    have hne : (starRingEnd ℂ) a ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hca; exact zero_ne_one hca
    exact (mul_left_cancel₀ hne this).symm
  · exact h

/-- At every time `t`, an admissible positive unitary
path has no eigenvalue `e^{iθ}` with `θ ∈ (α₁, 2π)` for some `α₁ < 2π`. -/
theorem exists_eigen_gap_below_two_pi {b : ℝ} {U : ℝ → E →L[ℂ] E} (hU : IsAdmissiblePath b U)
    {t : ℝ} (ht : t ∈ Icc 0 b) :
    ∃ α₁ < 2 * Real.pi, ∀ θ ∈ Ioo α₁ (2 * Real.pi), ∀ x : E,
      U t x = exp (θ * I) • x → x = 0 := by
  classical
  by_contra H
  push_neg at H
  choose! g hg v hv hv0 using H
  -- a strictly increasing sequence of eigenphases in `(π, 2π)`
  set θs : ℕ → ℝ := fun n => Nat.rec (g Real.pi) (fun _ θ => g θ) n with hθs
  have hθs0 : θs 0 = g Real.pi := rfl
  have hθsS : ∀ n, θs (n + 1) = g (θs n) := fun n => rfl
  have hmem : ∀ n, θs n ∈ Ioo Real.pi (2 * Real.pi) ∧
      ∃ x : E, x ≠ 0 ∧ U t x = exp (θs n * I) • x := by
    intro n
    induction n with
    | zero =>
      have h := hg Real.pi (by linarith [Real.pi_pos])
      exact ⟨h, v Real.pi, hv0 _ (by linarith [Real.pi_pos]), hv _ (by linarith [Real.pi_pos])⟩
    | succ n ih =>
      rw [hθsS]
      have h := hg (θs n) ih.1.2
      exact ⟨⟨ih.1.1.trans h.1, h.2⟩, v (θs n), hv0 _ ih.1.2, hv _ ih.1.2⟩
  have hmono : StrictMono θs := strictMono_nat_of_lt_succ fun n => by
    rw [hθsS]; exact (hg (θs n) (hmem n).1.2).1
  choose w hw0 hw using fun n => (hmem n).2
  -- normalized eigenvectors are orthonormal
  set u : ℕ → E := fun n => ((‖w n‖ : ℂ)⁻¹) • w n with hu
  have hun : ∀ n, ‖u n‖ = 1 := fun n => by
    rw [hu, norm_smul, norm_inv, Complex.norm_real, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 (hw0 n))]
  have hueig : ∀ n, U t (u n) = exp (θs n * I) • u n := fun n => by
    rw [hu, map_smul, hw, smul_comm]
  have huo : Orthonormal ℂ u := by
    refine ⟨hun, fun i j hij => ?_⟩
    refine inner_eq_zero_of_eigen_unitary (hU.unitary t ht) (by
      rw [Complex.norm_exp_ofReal_mul_I]) ?_ (hueig i) (hueig j)
    intro hexp
    have hI : ∀ n, θs n ∈ Ico Real.pi (Real.pi + 2 * Real.pi) := fun n =>
      ⟨(hmem n).1.1.le, by linarith [(hmem n).1.2, Real.pi_pos]⟩
    exact hij (hmono.injective (exp_mul_I_injOn_Ico Real.pi (hI i) (hI j) hexp))
  -- contradiction with `lower_eigenvalues_card_le`
  have hB := hU.lintegral_posTrace_lt_top
  set B := ∫⁻ s in Icc 0 b, posTrace (generator U b s) with hBdef
  obtain ⟨p, hp⟩ := exists_nat_gt (B.toReal / Real.pi)
  have hle := lower_eigenvalues_card_le hU ht (fun j : Fin p => u j)
    (huo.comp _ (Fin.val_injective)) (fun j => θs j) (fun j => (hmem j).1) (fun j => hueig j)
  have := (ENNReal.ofReal_le_iff_le_toReal hB.ne).1 hle
  rw [div_lt_iff₀ Real.pi_pos] at hp
  linarith

omit [CompleteSpace E] in
/-- A time at which `e^{iα}` is an eigenvalue has crossing multiplicity at least one. -/
lemma one_le_crossingMult {U : ℝ → E →L[ℂ] E} {α t : ℝ} {x : E} (hx : x ≠ 0)
    (hUx : U t x = exp (α * I) • x) : 1 ≤ crossingMult U α t := by
  unfold crossingMult
  set K := LinearMap.ker ((U t - exp (α * I) • (1 : E →L[ℂ] E) : E →L[ℂ] E) : E →ₗ[ℂ] E)
  have hxK : x ∈ K := by
    simp [K, hUx]
  have h1 : (1 : Cardinal) ≤ Module.rank ℂ K := by
    have hKrank := Submodule.rank_mono (R := ℂ)
      ((Submodule.span_singleton_le_iff_mem x K).2 hxK)
    rw [← Module.finrank_eq_rank, finrank_span_singleton hx, Nat.cast_one] at hKrank
    simpa [K] using hKrank
  have := Cardinal.toENat.monotone' h1
  simpa [K] using this

/-- An admissible path has only finitely many crossing times of a level `0 < α < 2π`. -/
lemma finite_crossing_times {b : ℝ} {U : ℝ → E →L[ℂ] E} (hU : IsAdmissiblePath b U) {α : ℝ}
    (hα0 : 0 < α) (hα : α < 2 * Real.pi) :
    {t ∈ Ioo 0 b | ∃ x : E, x ≠ 0 ∧ U t x = exp (α * I) • x}.Finite := by
  by_contra hinf
  obtain ⟨hfin, -⟩ := phase_cost hU hα0 hα
  set c := crossingCount U α (Ioo 0 b) with hc
  lift c to ℕ using hfin.ne with N hN
  obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (N + 1)
  have hle : ((N + 1 : ℕ) : ℕ∞) ≤ ∑ t ∈ s, crossingMult U α t := by
    calc ((N + 1 : ℕ) : ℕ∞) = ∑ _t ∈ s, (1 : ℕ∞) := by simp [hcard]
      _ ≤ ∑ t ∈ s, crossingMult U α t := by
        refine Finset.sum_le_sum fun t ht => ?_
        obtain ⟨-, x, hx, hUx⟩ := hs ht
        exact one_le_crossingMult hx hUx
  have hle2 : ∑ t ∈ s, crossingMult U α t ≤ crossingCount U α (Ioo 0 b) :=
    le_iSup₂_of_le s (fun t ht => (hs ht).1) le_rfl
  have := hle.trans hle2
  rw [← hc] at this
  norm_cast at this
  omega

/-- Local data around a crossing time. -/
lemma exists_window_data {b : ℝ} {U : ℝ → E →L[ℂ] E} (hU : IsAdmissiblePath b U) {α : ℝ}
    (heα : exp (α * I) ≠ 1) {t h₀ : ℝ} (hh₀ : 0 < h₀) (hwin : Icc (t - h₀) (t + h₀) ⊆ Ioo 0 b)
    (hfin : {t ∈ Ioo 0 b | ∃ x : E, x ≠ 0 ∧ U t x = exp (α * I) • x}.Finite)
    [FiniteDimensional ℂ (LinearMap.ker
      ((U t - exp (α * I) • (1 : E →L[ℂ] E) : E →L[ℂ] E) : E →ₗ[ℂ] E))] :
    ∃ r > 0, r ≤ h₀ ∧ ∃ δ > 0, δ ≤ Real.pi ∧ ∃ c > 0, ∃ g > 0,
      (∀ u ∈ Icc (t - r) (t + r), ∀ x, c * ‖x‖ ≤ ‖(U u - exp ((α + δ : ℝ) * I) • 1) x‖) ∧
      (∀ x, U (t - r) x = exp (α * I) • x → x = 0) ∧
      (∀ x, U (t + r) x = exp (α * I) • x → x = 0) ∧
      (∀ x ∈ (LinearMap.ker
          ((U t - exp (α * I) • (1 : E →L[ℂ] E) : E →L[ℂ] E) : E →ₗ[ℂ] E))ᗮ,
        g * ‖x‖ ≤ ‖(U t - exp (α * I) • 1) x‖) ∧
      ‖exp (δ * I) - 1‖ ≤ g / 8 ∧ ‖U (t + r) - U t‖ ≤ g / 4 := by
  set K₀ := LinearMap.ker ((U t - exp (α * I) • (1 : E →L[ℂ] E) : E →L[ℂ] E) : E →ₗ[ℂ] E)
    with hK₀
  have htI : t ∈ Ioo 0 b := hwin ⟨by linarith, by linarith⟩
  have htIcc : t ∈ Icc 0 b := Ioo_subset_Icc_self htI
  obtain ⟨η, hη, g, hg, hgap⟩ := exists_gap_of_isCompactOperator (hU.isCompactOperator htIcc)
    heα K₀ (fun v hv => LinearMap.mem_ker.2 hv)
  have hgap0 : ∀ x ∈ K₀ᗮ, g * ‖x‖ ≤ ‖(U t - exp (α * I) • 1) x‖ := fun x hx => by
    simpa using hgap 0 (by simp [hη.le]) x hx
  set δ := min η (min (g / 8) 1) with hδdef
  have hδ0 : 0 < δ := lt_min hη (lt_min (by positivity) one_pos)
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hδπ : δ ≤ Real.pi := hδ1.trans (by linarith [Real.pi_gt_three])
  have hδg : ‖exp (δ * I) - 1‖ ≤ g / 8 :=
    (norm_exp_mul_I_sub_one_le hδ0.le).trans ((min_le_right _ _).trans (min_le_left _ _))
  have he1 : ‖exp (α * I)‖ = 1 := by rw [Complex.norm_exp_ofReal_mul_I]
  have heig : ∀ k ∈ K₀, U t k = exp (α * I) • k := fun k hk => by
    have := LinearMap.mem_ker.1 hk
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] at this
    exact sub_eq_zero.1 this
  have hlow : ∀ x, min ‖exp (α * I) - exp ((α + δ : ℝ) * I)‖ g * ‖x‖ ≤
      ‖(U t - exp ((α + δ : ℝ) * I) • 1) x‖ :=
    norm_ge_of_gap (hU.unitary t htIcc) he1 K₀ heig hg.le
      (fun x hx => hgap δ (by rw [abs_of_pos hδ0]; exact min_le_left _ _) x hx)
  set d := min ‖exp (α * I) - exp ((α + δ : ℝ) * I)‖ g with hd
  have hd0 : 0 < d := by
    refine lt_min ?_ hg
    rw [norm_exp_mul_I_sub_exp_mul_I, show α + δ - α = δ by ring]
    exact norm_pos_iff.2 (sub_ne_zero.2 (exp_mul_I_ne_one hδ0 (by linarith)))
  -- continuity of `U` at `t`
  have hUt : ContinuousAt U t :=
    hU.contDiff.continuousOn.continuousAt (Icc_mem_nhds htI.1 htI.2)
  obtain ⟨ρ, hρ, hρU⟩ := Metric.continuousAt_iff.1 hUt (min (d / 2) (g / 4))
    (lt_min (by positivity) (by positivity))
  set r' := min (ρ / 2) h₀ with hr'
  have hr'0 : 0 < r' := lt_min (by positivity) hh₀
  have hclose : ∀ u ∈ Icc (t - r') (t + r'), ‖U u - U t‖ < min (d / 2) (g / 4) := by
    intro u hu
    rw [← dist_eq_norm]
    refine hρU ?_
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hu.1, hu.2, min_le_left (ρ / 2) h₀]
  -- a radius avoiding the finitely many crossing times
  set C := {t ∈ Ioo 0 b | ∃ x : E, x ≠ 0 ∧ U t x = exp (α * I) • x} with hC
  have hS : ((fun x => x - t) '' C ∪ (fun x => t - x) '' C).Countable :=
    (hfin.image _).countable.union (hfin.image _).countable
  obtain ⟨r, hr, hrS⟩ := exists_mem_Ioo_not_mem_of_countable hS hr'0
  have hrh₀ : r ≤ h₀ := hr.2.le.trans (min_le_right _ _)
  have hsub : Icc (t - r) (t + r) ⊆ Icc (t - r') (t + r') :=
    Icc_subset_Icc (by linarith [hr.2]) (by linarith [hr.2])
  have hnc : ∀ u, u ∈ Ioo 0 b → u ∉ C → ∀ x, U u x = exp (α * I) • x → x = 0 := by
    intro u hu huC x hx
    by_contra hx0
    exact huC ⟨hu, x, hx0, hx⟩
  refine ⟨r, hr.1, hrh₀, δ, hδ0, hδπ, d / 2, by positivity, g, hg, ?_, ?_, ?_, hgap0, hδg, ?_⟩
  · intro u hu x
    have h1 := hlow x
    have h2 : ‖(U u - U t) x‖ ≤ d / 2 * ‖x‖ :=
      ((U u - U t).le_opNorm x).trans (mul_le_mul_of_nonneg_right
        ((hclose u (hsub hu)).le.trans (min_le_left _ _)) (norm_nonneg _))
    have h3 : (U u - exp ((α + δ : ℝ) * I) • 1) x =
        (U t - exp ((α + δ : ℝ) * I) • 1) x + (U u - U t) x := by
      simp only [ContinuousLinearMap.sub_apply]; abel
    have h4 := norm_sub_norm_le ((U t - exp ((α + δ : ℝ) * I) • 1) x)
      (-(U u - U t) x)
    rw [h3]
    rw [sub_neg_eq_add, norm_neg] at h4
    linarith
  · exact hnc (t - r) (hwin ⟨by linarith, by linarith [hr.1]⟩)
      (fun h => hrS (Or.inr ⟨t - r, h, by ring⟩))
  · exact hnc (t + r) (hwin ⟨by linarith [hr.1], by linarith⟩)
      (fun h => hrS (Or.inl ⟨t + r, h, by ring⟩))
  · exact (hclose (t + r) (hsub ⟨by linarith [hr.1], le_rfl⟩)).le.trans (min_le_right _ _)

set_option maxHeartbeats 1600000 in
/-- Let `0 < a < b₁ ≤ b` and `0 < α < 2π`. If `U(a)` has no eigenvalue with
argument in `[α, 2π)`, `e^{iα}` is not an eigenvalue of `U(b₁)`, and `U(b₁)` has `m` orthonormal
eigenvectors with arguments in `(α, 2π)`, then `U` has at least `m` crossings of `e^{iα}` in
`(a, b₁)`, counted with multiplicity. -/
theorem crossings_of_arc {b : ℝ} {U : ℝ → E →L[ℂ] E} (hU : IsAdmissiblePath b U)
    {a b₁ α : ℝ} (ha : 0 < a) (hab : a < b₁) (hb₁ : b₁ ≤ b) (hα0 : 0 < α)
    (hα : α < 2 * Real.pi)
    (hgap : ∀ θ ∈ Ico α (2 * Real.pi), ∀ x : E, U a x = exp (θ * I) • x → x = 0)
    (hend : ∀ x : E, U b₁ x = exp (α * I) • x → x = 0)
    {m : ℕ} (u : Fin m → E) (hu : Orthonormal ℂ u) (θ : Fin m → ℝ)
    (hθ : ∀ j, θ j ∈ Ioo α (2 * Real.pi)) (heig : ∀ j, U b₁ (u j) = exp (θ j * I) • u j) :
    (m : ℕ∞) ≤ crossingCount U α (Ioo a b₁) := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp
  have hpi := Real.pi_pos
  have hb0 : 0 ≤ b := hU.pos.le
  have hab' : Icc a b₁ ⊆ Icc 0 b := Icc_subset_Icc ha.le hb₁
  have hab'' : Ioo a b₁ ⊆ Ioo 0 b := Ioo_subset_Ioo ha.le hb₁
  set L := generator U b with hLdef
  have heα : exp (α * I) ≠ 1 := exp_mul_I_ne_one hα0 hα
  have hUc : ContinuousOn U (Icc 0 b) := hU.contDiff.continuousOn
  -- the crossing times of `U` in `(a, b₁)`
  set C := {t ∈ Ioo 0 b | ∃ x : E, x ≠ 0 ∧ U t x = exp (α * I) • x} with hC
  have hCfin : C.Finite := finite_crossing_times hU hα0 hα
  set s : Finset ℝ := hCfin.toFinset.filter (fun t => t ∈ Ioo a b₁) with hsdef
  have hs_sub : ↑s ⊆ Ioo a b₁ := fun t ht => (Finset.mem_filter.1 ht).2
  have hs_mem : ∀ t ∈ Ioo a b₁, (∃ x : E, x ≠ 0 ∧ U t x = exp (α * I) • x) → t ∈ s :=
    fun t ht hx => Finset.mem_filter.2 ⟨hCfin.mem_toFinset.2 ⟨hab'' ht, hx⟩, ht⟩
  set K₀ : ℝ → Submodule ℂ E :=
    fun t => LinearMap.ker ((U t - exp (α * I) • (1 : E →L[ℂ] E) : E →L[ℂ] E) : E →ₗ[ℂ] E)
    with hK₀def
  have hK₀fin : ∀ t ∈ Icc 0 b, FiniteDimensional ℂ (K₀ t) := fun t ht =>
    finiteDimensional_ker_of_isCompactOperator (hU.isCompactOperator ht) heα
  -- windows around the crossing times
  obtain ⟨h₀, hh₀, hwin₀, hsep⟩ := exists_sep_radius_Ioo hs_sub
  have hwin : ∀ t ∈ s, Icc (t - h₀) (t + h₀) ⊆ Ioo 0 b := fun t ht => (hwin₀ t ht).trans hab''
  have hdata : ∀ t ∈ s, ∃ r > 0, r ≤ h₀ ∧ ∃ δ > 0, δ ≤ Real.pi ∧ ∃ c > 0, ∃ g > 0,
      (∀ u ∈ Icc (t - r) (t + r), ∀ x, c * ‖x‖ ≤ ‖(U u - exp ((α + δ : ℝ) * I) • 1) x‖) ∧
      (∀ x, U (t - r) x = exp (α * I) • x → x = 0) ∧
      (∀ x, U (t + r) x = exp (α * I) • x → x = 0) ∧
      (∀ x ∈ (K₀ t)ᗮ, g * ‖x‖ ≤ ‖(U t - exp (α * I) • 1) x‖) ∧
      ‖exp (δ * I) - 1‖ ≤ g / 8 ∧ ‖U (t + r) - U t‖ ≤ g / 4 := by
    intro t ht
    haveI := hK₀fin t (Ioo_subset_Icc_self (hab'' (hs_sub ht)))
    exact exists_window_data hU heα hh₀ (hwin t ht) hCfin
  choose! r hr0 hrh₀ δ hδ0 hδπ c hc g hg hW2 hncl hncr hgapt hδg hUr using hdata
  -- outside the windows, `U - e^{iα}` is uniformly bounded below
  set Kout : Set ℝ := Icc a b₁ \ ⋃ t ∈ s, Ioo (t - r t) (t + r t) with hKout
  have hKout_cpt : IsCompact Kout :=
    isCompact_Icc.diff (isOpen_biUnion fun t _ => isOpen_Ioo)
  have hKout_sub : Kout ⊆ Icc 0 b := fun p hp => hab' hp.1
  have hKout_nc : ∀ p ∈ Kout, ∀ x, U p x = exp (α * I) • x → x = 0 := by
    intro p hp x hx
    obtain ⟨hpI, hpw⟩ := hp
    rcases eq_or_lt_of_le hpI.1 with hpa | hpa
    · subst hpa
      exact hgap α ⟨le_rfl, hα⟩ x hx
    rcases eq_or_lt_of_le hpI.2 with hpb | hpb
    · subst hpb
      exact hend x hx
    by_contra hx0
    have hps := hs_mem p ⟨hpa, hpb⟩ ⟨x, hx0, hx⟩
    exact hpw (mem_biUnion hps ⟨by linarith [hr0 p hps], by linarith [hr0 p hps]⟩)
  obtain ⟨c₃, hc₃, hbd₃⟩ := exists_uniform_lower_bound hKout_cpt
    (T := fun p => U p - exp (α * I) • 1)
    ((hUc.mono hKout_sub).sub continuousOn_const)
    (fun p hp => exists_lower_bound_of_injective
      (hU.isCompactOperator (hKout_sub hp)) heα (hKout_nc p hp))
  -- the arc at the final time `b₁`
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm0⟩, Finset.mem_univ _⟩
  set θmin := Finset.univ.inf' hne θ with hθmin
  set θmax := Finset.univ.sup' hne θ with hθmax
  have hθmin_le : ∀ j, θmin ≤ θ j := fun j => Finset.inf'_le _ (Finset.mem_univ j)
  have hθmax_ge : ∀ j, θ j ≤ θmax := fun j => Finset.le_sup' _ (Finset.mem_univ j)
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_eq_inf' hne θ
  obtain ⟨j₁, -, hj₁⟩ := Finset.exists_mem_eq_sup' hne θ
  have hθmin_gt : α < θmin := lt_of_lt_of_le (hθ j₀).1 (le_of_eq hj₀.symm)
  have hθmax_lt : θmax < 2 * Real.pi := lt_of_le_of_lt (le_of_eq hj₁) (hθ j₁).2
  have hθle : θmin ≤ θmax := (hθmin_le j₀).trans (hθmax_ge j₀)
  set μ := min (θmin - α) (2 * Real.pi - θmax) / 2 with hμ
  have hμ0 : 0 < μ := by
    have : 0 < min (θmin - α) (2 * Real.pi - θmax) := lt_min (by linarith) (by linarith)
    positivity
  have hμ1 : 2 * μ ≤ θmin - α := by
    have := min_le_left (θmin - α) (2 * Real.pi - θmax); linarith
  have hμ2 : 2 * μ ≤ 2 * Real.pi - θmax := by
    have := min_le_right (θmin - α) (2 * Real.pi - θmax); linarith
  set γ := (θmin + θmax) / 2 with hγ
  set w₀ := (θmax - θmin) / 2 with hw₀
  set w := w₀ + μ with hw
  set q := 2 * Real.pi - μ with hq
  have hw₀0 : 0 ≤ w₀ := by rw [hw₀]; linarith
  have hw₀π : w₀ ≤ Real.pi := by rw [hw₀]; linarith
  have hwπ : w ≤ Real.pi := by rw [hw, hw₀]; linarith
  have hαγ : α < γ - w := by rw [hγ, hw, hw₀]; linarith
  have hγq : γ + w ≤ q := by rw [hγ, hw, hw₀, hq]; linarith
  have hq2 : q < 2 * Real.pi := by rw [hq]; linarith
  set M := ‖exp (w₀ * I) - 1‖ with hM
  have hM0 : 0 ≤ M := norm_nonneg _
  have hMj : ∀ j, ‖exp (θ j * I) - exp (γ * I)‖ ≤ M := fun j =>
    norm_exp_mul_I_sub_le (by rw [abs_le]; constructor <;> linarith [hθmin_le j, hθmax_ge j])
      hw₀π
  have hUspan : ∀ y ∈ Submodule.span ℂ (Set.range u), ‖(U b₁ - exp (γ * I) • 1) y‖ ≤ M * ‖y‖ :=
    fun y hy => norm_sub_smul_le_of_mem_span_eigen hu (U b₁) _ heig _ hM0 hMj hy
  set ρ₀ := Real.sqrt (2 - 2 * Real.cos w) with hρ₀
  have hMρ : M < ρ₀ := by
    have hcos : Real.cos w < Real.cos w₀ :=
      Real.cos_lt_cos_of_nonneg_of_le_pi hw₀0 hwπ (by rw [hw]; linarith)
    have hM2 : M ^ 2 = 2 - 2 * Real.cos w₀ := by
      rw [hM, show (exp (w₀ * I) - 1) = exp (w₀ * I) - exp ((0 : ℝ) * I) by simp,
        norm_exp_mul_I_sub_sq, sub_zero]
    rw [hρ₀, ← Real.sqrt_sq hM0, hM2]
    exact Real.sqrt_lt_sqrt (by nlinarith [Real.cos_le_one w₀]) (by linarith)
  -- `U(a) - e^{iθ}` is uniformly bounded below for `θ ∈ [α, q]`
  obtain ⟨c₄, hc₄, hbd₄⟩ := exists_uniform_lower_bound (isCompact_Icc : IsCompact (Icc α q))
    (T := fun θ' : ℝ => U a - exp (θ' * I) • 1)
    (by fun_prop)
    (fun θ' hθ' => exists_lower_bound_of_injective
      (hU.isCompactOperator ⟨ha.le, hab.le.trans hb₁⟩)
      (exp_mul_I_ne_one (by linarith [hθ'.1]) (by linarith [hθ'.2]))
      (hgap θ' ⟨hθ'.1, by linarith [hθ'.2]⟩))
  -- the approximation error
  have hε : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < c₃ ∧ ε < c₄ ∧ ε < ρ₀ - M ∧
      ∀ t ∈ s, ε < c t ∧ ε < g t / 4 := by
    have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), ε < c₃ ∧ ε < c₄ ∧ ε < ρ₀ - M :=
      (eventually_lt_nhds hc₃).and ((eventually_lt_nhds hc₄).and
        (eventually_lt_nhds (by linarith)))
    have h2 : ∀ t ∈ s, ∀ᶠ ε in 𝓝 (0 : ℝ), ε < c t ∧ ε < g t / 4 := fun t ht =>
      (eventually_lt_nhds (hc t ht)).and (eventually_lt_nhds (by linarith [hg t ht]))
    filter_upwards [nhdsWithin_le_nhds (h1.and ((Filter.eventually_all_finset s).2 h2))]
      with ε hε
    exact ⟨hε.1.1, hε.1.2.1, hε.1.2.2, hε.2⟩
  obtain ⟨ε, ⟨hεc₃, hεc₄, hερ, hεs⟩, hεpos⟩ := (hε.and eventually_mem_nhdsWithin).exists
  -- the finite-dimensional approximation
  set X₀ : Submodule ℂ E := Submodule.span ℂ (Set.range u) with hX₀
  haveI : FiniteDimensional ℂ X₀ := FiniteDimensional.span_of_finite ℂ (Set.finite_range u)
  obtain ⟨F, _, _, _, ι, π, V, hadj, hπι, hX, hV0, hVu, hVd, hcl⟩ :=
    exists_finite_approx_path_gen hb0 hU.start hU.unitary hU.hasDerivWithinAt
      hU.continuousOn_generator hU.posTraceClass X₀ (show (0 : ℝ) < ε from hεpos)
  have hιinj : Function.Injective ι := fun x y hxy => by
    have := congrArg π hxy; rwa [hπι, hπι] at this
  have hVc : ContinuousOn V (Icc 0 b) := fun t ht => (hVd t ht).continuousWithinAt
  have hVd' : ∀ t ∈ Ico 0 b, HasDerivWithinAt V (I • (V t * (π ∘L L t ∘L ι))) (Ici t) t :=
    fun t ht => (hVd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1))
  have hAs : ∀ t ∈ Ico 0 b, IsSelfAdjoint (π ∘L L t ∘L ι) := fun t ht =>
    compress_gen_isSelfAdjoint hadj (hU.posTraceClass t (Ico_subset_Icc_self ht)).1.isSelfAdjoint
  have hApos : ∀ t ∈ Icc 0 b, ∀ x, 0 ≤ RCLike.re ⟪x, (π ∘L L t ∘L ι) x⟫_ℂ := fun t ht x => by
    rw [inner_compress_gen hadj]
    exact (hU.posTraceClass t ht).1.re_inner_nonneg_right _
  have hAsp : ∀ t ∈ Ioc 0 b, ∀ x, x ≠ 0 → 0 < RCLike.re ⟪x, (π ∘L L t ∘L ι) x⟫_ℂ :=
    fun t ht x hx => by
      rw [inner_compress_gen hadj]
      exact hU.strictPos t ht (ι x) fun h => hx (hιinj (h.trans (map_zero ι).symm))
  -- global count for `V`
  set YV : Submodule ℂ F := X₀.comap (ι : F →ₗ[ℂ] E) with hYV
  have hYVrank : finrank ℂ X₀ ≤ finrank ℂ YV := by
    let f : X₀ →ₗ[ℂ] YV :=
      { toFun := fun v => ⟨π v, by
          show ι (π v) ∈ X₀
          rw [hX v v.2]; exact v.2⟩
        map_add' := fun v w => by ext; simp
        map_smul' := fun a v => by ext; simp }
    refine LinearMap.finrank_le_finrank_of_injective (f := f) fun v w hvw => ?_
    have h1 : π v = π w := congrArg Subtype.val hvw
    have h2 := congrArg ι h1
    rw [hX v v.2, hX w w.2] at h2
    exact Subtype.ext h2
  have hX₀rank : finrank ℂ X₀ = m := by
    rw [hX₀, finrank_span_eq_card hu.linearIndependent, Fintype.card_fin]
  have hYVbd : ∀ y ∈ YV, ‖(V b₁ - exp (γ * I) • 1) y‖ ≤ (M + ε) * ‖y‖ := by
    intro y hy
    have h1 := (norm_sub_smul_le_of_approx hadj hπι (V b₁) (U b₁)
      (hcl b₁ ⟨hab.le.trans' ha.le, hb₁⟩) (exp (γ * I)) y).2
    have h2 := hUspan (ι y) hy
    rw [norm_isometry_apply hadj hπι] at h2
    calc ‖(V b₁ - exp (γ * I) • 1) y‖ ≤ ‖(U b₁ - exp (γ * I) • 1) (ι y)‖ + ε * ‖y‖ := h1
      _ ≤ M * ‖y‖ + ε * ‖y‖ := by gcongr
      _ = (M + ε) * ‖y‖ := by ring
  have hρ : (M + ε) ^ 2 < 2 - 2 * Real.cos w := by
    have h0 : 0 ≤ 2 - 2 * Real.cos w := by nlinarith [Real.cos_le_one w]
    have : M + ε < ρ₀ := by linarith
    calc (M + ε) ^ 2 < ρ₀ ^ 2 :=
          pow_lt_pow_left₀ this (add_nonneg hM0 (le_of_lt hεpos)) two_ne_zero
      _ = 2 - 2 * Real.cos w := Real.sq_sqrt h0
  have hgapV : ∀ θ' ∈ Icc α q, ∀ y, y ≠ 0 → (V a - exp (θ' * I) • 1) y ≠ 0 :=
    fun θ' hθ' y hy => apply_ne_zero_of_approx hadj hπι (V a) (U a)
      (hcl a ⟨ha.le, hab.le.trans hb₁⟩) hεc₄ (hbd₄ θ' hθ') y hy
  obtain ⟨S, hS, hScount⟩ := crossings_of_arc_finiteDim (n := finrank ℂ F) rfl hb0 hVu hV0 hVc
    hVd' hAs hApos ha.le hab hb₁ hαγ hγq (by positivity) hgapV YV hYVbd hρ
  -- every crossing of `V` lies in one of the windows
  set St : ℝ → Finset ℝ := fun t => S.filter (fun t' => t' ∈ Ioo (t - r t) (t + r t))
    with hSt
  have hSsub : ∀ t' ∈ S, crossingMult V α t' ≠ 0 → t' ∈ s.biUnion St := by
    intro t' ht' hne
    by_contra hnot
    apply hne
    refine crossingMult_eq_zero_of_injective fun y hy => ?_
    have hK : t' ∈ Kout := by
      refine ⟨Ioo_subset_Icc_self (hS ht'), fun hmem => hnot ?_⟩
      obtain ⟨t, ht, htt'⟩ := mem_iUnion₂.1 hmem
      exact Finset.mem_biUnion.2 ⟨t, ht, Finset.mem_filter.2 ⟨ht', htt'⟩⟩
    exact apply_ne_zero_of_approx hadj hπι (V t') (U t') (hcl t' (hKout_sub hK)) hεc₃
      (hbd₃ t' hK) y hy
  have hdisj : (s : Set ℝ).PairwiseDisjoint St := by
    intro t ht t' ht' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro u hu hu'
    have h1 := (Finset.mem_filter.1 hu).2
    have h2 := (Finset.mem_filter.1 hu').2
    have h3 := hsep t ht t' ht' hne
    have h4 := hrh₀ t ht
    have h5 := hrh₀ t' ht'
    have h6 : |t - u| < r t := abs_sub_lt_iff.2 ⟨by linarith [h1.1], by linarith [h1.2]⟩
    have h7 : |u - t'| < r t' := abs_sub_lt_iff.2 ⟨by linarith [h2.2], by linarith [h2.1]⟩
    have h8 := abs_sub_le t u t'
    linarith
  -- in each window, the crossings of `V` are bounded by the multiplicity of `U`
  have hwinbd : ∀ t ∈ s, ∑ t' ∈ St t, crossingMult V α t' ≤ crossingMult U α t := by
    intro t ht
    have htI : t ∈ Ioo 0 b := hab'' (hs_sub ht)
    have htIcc := Ioo_subset_Icc_self htI
    haveI := hK₀fin t htIcc
    have hw' : Icc (t - r t) (t + r t) ⊆ Icc 0 b :=
      (Icc_subset_Icc (by linarith [hrh₀ t ht]) (by linarith [hrh₀ t ht])).trans
        ((hwin t ht).trans Ioo_subset_Icc_self)
    have hw'' : Icc (t - r t) (t + r t) ⊆ Ioo 0 b :=
      (Icc_subset_Icc (by linarith [hrh₀ t ht]) (by linarith [hrh₀ t ht])).trans (hwin t ht)
    have hle : t - r t ≤ t + r t := by linarith [hr0 t ht]
    obtain ⟨Y, hYc, hYb⟩ := crossings_in_window_le (n := finrank ℂ F) rfl hle
      (fun u hu => hVu u (hw' hu)) (hVc.mono hw')
      (fun u hu => hVd' u ⟨(hw' (Ico_subset_Icc_self hu)).1,
        lt_of_lt_of_le hu.2 (hw' ⟨hle, le_rfl⟩).2⟩)
      (fun u hu => hAs u ⟨(hw' (Ico_subset_Icc_self hu)).1,
        lt_of_lt_of_le hu.2 (hw' ⟨hle, le_rfl⟩).2⟩)
      (fun u hu x hx => hAsp u ⟨(hw'' (Ico_subset_Icc_self hu)).1,
        (hw' (Ico_subset_Icc_self hu)).2⟩ x hx)
      (hδ0 t ht) (hδπ t ht)
      (fun u hu y hy => apply_ne_zero_of_approx hadj hπι (V u) (U u) (hcl u (hw' hu))
        (hεs t ht).1 (hW2 t ht u hu) y hy)
      (St t) (fun u hu => Ioo_subset_Ico_self (Finset.mem_filter.1 hu).2)
    -- transfer to `U`
    set Z : Submodule ℂ E := Y.map (ι : F →ₗ[ℂ] E) with hZ
    have hZrank : finrank ℂ Z = finrank ℂ Y :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hιinj Y)).symm
    have hZbd : ∀ z ∈ Z, z ≠ 0 → ‖(U t - exp (α * I) • 1) z‖ < g t * ‖z‖ := by
      rintro z ⟨y, hy, rfl⟩ hz
      have hy0 : y ≠ 0 := fun h => hz (by simp [h])
      have hny : 0 < ‖y‖ := norm_pos_iff.2 hy0
      have h1 := (norm_sub_smul_le_of_approx hadj hπι (V (t + r t)) (U (t + r t))
        (hcl _ (hw' ⟨hle, le_rfl⟩)) (exp (α * I)) y).1
      have h2 := hYb y hy
      have h3 : (U t - exp (α * I) • 1) (ι y) =
          (U (t + r t) - exp (α * I) • 1) (ι y) - (U (t + r t) - U t) (ι y) := by
        simp only [ContinuousLinearMap.sub_apply]; abel
      have h4 : ‖(U (t + r t) - U t) (ι y)‖ ≤ g t / 4 * ‖y‖ := by
        refine ((U (t + r t) - U t).le_opNorm _).trans ?_
        rw [norm_isometry_apply hadj hπι]
        exact mul_le_mul_of_nonneg_right (hUr t ht) (norm_nonneg _)
      have h5 := hδg t ht
      have h6 := (hεs t ht).2
      change ‖(U t - exp (α * I) • 1) (ι y)‖ < g t * ‖ι y‖
      rw [h3, norm_isometry_apply hadj hπι]
      calc ‖(U (t + r t) - exp (α * I) • 1) (ι y) - (U (t + r t) - U t) (ι y)‖
          ≤ ‖(U (t + r t) - exp (α * I) • 1) (ι y)‖ + ‖(U (t + r t) - U t) (ι y)‖ :=
            norm_sub_le _ _
        _ ≤ (‖exp (δ t * I) - 1‖ * ‖y‖ + ε * ‖y‖) + g t / 4 * ‖y‖ := by linarith
        _ < g t * ‖y‖ := by nlinarith [hg t ht]
    have hfr := finrank_le_of_gap (K₀ t) (hgapt t ht) Z hZbd
    calc ∑ t' ∈ St t, crossingMult V α t' ≤ (finrank ℂ Y : ℕ∞) := hYc
      _ = (finrank ℂ Z : ℕ∞) := by rw [hZrank]
      _ ≤ (finrank ℂ (K₀ t) : ℕ∞) := by exact_mod_cast hfr
      _ = crossingMult U α t := crossingMult_eq_finrank.symm
  calc (m : ℕ∞) = (finrank ℂ X₀ : ℕ∞) := by rw [hX₀rank]
    _ ≤ (finrank ℂ YV : ℕ∞) := by exact_mod_cast hYVrank
    _ ≤ ∑ t' ∈ S, crossingMult V α t' := hScount
    _ ≤ ∑ t' ∈ s.biUnion St, crossingMult V α t' := Finset.sum_le_sum_of_ne_zero hSsub
    _ = ∑ t ∈ s, ∑ t' ∈ St t, crossingMult V α t' := Finset.sum_biUnion hdisj
    _ ≤ ∑ t ∈ s, crossingMult U α t := Finset.sum_le_sum hwinbd
    _ ≤ crossingCount U α (Ioo a b₁) := le_iSup₂_of_le s hs_sub le_rfl

end

section

/-! ## Conformal comparison of Dirichlet eigenvalues -/

open MeasureTheory Set Metric Filter Topology Complex

/-- An injective holomorphic map on a connected open set has a holomorphic inverse on its
(open) image. -/
lemma exists_holomorphic_inverse {D : Set ℂ} (hD : IsOpen D) (hDc : IsPreconnected D)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f D) (hinj : InjOn f D) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (f '' D) ∧ MapsTo g (f '' D) D ∧
      (∀ z ∈ D, g (f z) = z) ∧ ∀ w ∈ f '' D, f (g w) = w := by
  classical
  set g := Function.invFunOn f D with hg
  have hgmem : ∀ w ∈ f '' D, g w ∈ D ∧ f (g w) = w := fun w hw => Function.invFunOn_pos hw
  have hgf : ∀ z ∈ D, g (f z) = z := fun z hz =>
    hinj (hgmem _ (mem_image_of_mem f hz)).1 hz (hgmem _ (mem_image_of_mem f hz)).2
  have hopen : IsOpen (f '' D) :=
    isOpen_image_of_injOn hD hDc hf hinj subset_rfl hD
  refine ⟨g, ?_, fun w hw => (hgmem w hw).1, hgf, fun w hw => (hgmem w hw).2⟩
  intro w hw
  have hwn : f '' D ∈ 𝓝 w := hopen.mem_nhds hw
  obtain ⟨hgw, hfgw⟩ := hgmem w hw
  have hcont : ContinuousAt g w := by
    rw [ContinuousAt, (nhds_basis_opens (g w)).tendsto_right_iff]
    rintro V ⟨hV, hVo⟩
    have hopen' : IsOpen (f '' (V ∩ D)) :=
      isOpen_image_of_injOn hD hDc hf hinj inter_subset_right (hVo.inter hD)
    have hmem : w ∈ f '' (V ∩ D) := ⟨g w, ⟨hV, hgw⟩, hfgw⟩
    filter_upwards [hopen'.mem_nhds hmem] with y hy
    obtain ⟨z, ⟨hzV, hzD⟩, rfl⟩ := hy
    rw [hgf z hzD]; exact hzV
  have hfder : HasDerivAt f (deriv f (g w)) (g w) :=
    (hf.differentiableAt (hD.mem_nhds hgw)).hasDerivAt
  have hne := deriv_ne_zero_of_injOn hD hf hinj hgw
  have hev : ∀ᶠ y in 𝓝 w, f (g y) = y := by
    filter_upwards [hwn] with y hy using (hgmem y hy).2
  exact (hfder.of_local_left_inverse hcont hne hev).differentiableAt.differentiableWithinAt

/-- Change of variables for an injective holomorphic map. -/
lemma lintegral_image_holomorphic {Ω : Set ℂ} (hΩ : IsOpen Ω) {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ Ω) (hinj : InjOn Φ Ω) (g : ℂ → ENNReal) :
    ∫⁻ w in Φ '' Ω, g w = ∫⁻ z in Ω, ENNReal.ofReal (‖deriv Φ z‖ ^ 2) * g (Φ z) := by
  have hf' : ∀ z ∈ Ω, HasFDerivWithinAt Φ
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv Φ z)).restrictScalars ℝ) Ω z :=
    fun z hz => ((hΦ.differentiableAt (hΩ.mem_nhds hz)).hasDerivAt.hasFDerivAt
      |>.restrictScalars ℝ).hasFDerivWithinAt
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hΩ.measurableSet hf' hinj g]
  refine setLIntegral_congr_fun hΩ.measurableSet fun z _ => ?_
  congr 2
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
    LinearMap.det_restrictScalars]
  simp [Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]

/-- Energy of a conformal pullback: `E(u ∘ Φ) ≤ E(u)`. -/
lemma dirichletEnergy_pullback_le {Ω : Set ℂ} (hΩ : IsOpen Ω) {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ Ω) (hinj : InjOn Φ Ω) {u : ℂ → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hv : ∀ z, z ∉ Ω → Ω.indicator (fun z => u (Φ z)) =ᶠ[𝓝 z] 0) :
    dirichletEnergy (Ω.indicator (fun z => u (Φ z))) ≤ dirichletEnergy u := by
  set v := Ω.indicator (fun z => u (Φ z)) with hvdef
  unfold dirichletEnergy
  have hsupp : Function.support (fun z => ‖fderiv ℝ v z‖ₑ ^ 2) ⊆ Ω := by
    intro z hz
    by_contra hzΩ
    apply hz
    show ‖fderiv ℝ v z‖ₑ ^ 2 = 0
    rw [(hv z hzΩ).fderiv_eq, show (0 : ℂ → ℝ) = fun _ => (0 : ℝ) from rfl, fderiv_const_apply,
      ← ofReal_norm_eq_enorm]
    simp
  rw [← setLIntegral_eq_of_support_subset hsupp]
  calc ∫⁻ z in Ω, ‖fderiv ℝ v z‖ₑ ^ 2
      ≤ ∫⁻ z in Ω, ENNReal.ofReal (‖deriv Φ z‖ ^ 2) * ‖fderiv ℝ u (Φ z)‖ₑ ^ 2 := by
        refine setLIntegral_mono' hΩ.measurableSet fun z hz => ?_
        have heq : v =ᶠ[𝓝 z] fun y => u (Φ y) := by
          filter_upwards [hΩ.mem_nhds hz] with y hy
          rw [hvdef, Set.indicator_of_mem hy]
        have hΦd : HasFDerivAt Φ
            ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv Φ z)).restrictScalars ℝ) z :=
          (hΦ.differentiableAt (hΩ.mem_nhds hz)).hasDerivAt.hasFDerivAt.restrictScalars ℝ
        have hud : HasFDerivAt u (fderiv ℝ u (Φ z)) (Φ z) :=
          ((hu.differentiable (by simp)) (Φ z)).hasFDerivAt
        rw [heq.fderiv_eq, show (fun y => u (Φ y)) = u ∘ Φ from rfl, (hud.comp z hΦd).fderiv]
        have hn : ‖(ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv Φ z)).restrictScalars ℝ‖
            = ‖deriv Φ z‖ := by
          rw [ContinuousLinearMap.norm_restrictScalars, ContinuousLinearMap.norm_smulRight_apply,
            norm_one, one_mul]
        have hle := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ u (Φ z))
          ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv Φ z)).restrictScalars ℝ)
        rw [hn] at hle
        rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
          ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h0 := norm_nonneg ((fderiv ℝ u (Φ z)).comp
          ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv Φ z)).restrictScalars ℝ))
        calc _ ≤ (‖fderiv ℝ u (Φ z)‖ * ‖deriv Φ z‖) ^ 2 := pow_le_pow_left₀ h0 hle 2
          _ = _ := by ring
    _ = ∫⁻ w in Φ '' Ω, ‖fderiv ℝ u w‖ₑ ^ 2 :=
        (lintegral_image_holomorphic hΩ hΦ hinj (fun w => ‖fderiv ℝ u w‖ₑ ^ 2)).symm
    _ ≤ ∫⁻ w, ‖fderiv ℝ u w‖ₑ ^ 2 := setLIntegral_le_lintegral _ _

/-- `L²` norm of a conformal pullback: `‖u‖² ≤ M ‖u ∘ Φ‖²` when `|Φ'|² ≤ M`. -/
lemma l2NormSq_le_pullback {Ω : Set ℂ} (hΩ : IsOpen Ω) {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ Ω) (hinj : InjOn Φ Ω) {M : ℝ}
    (hM : ∀ z ∈ Ω, ‖deriv Φ z‖ ^ 2 ≤ M) {u : ℂ → ℝ} (hu : tsupport u ⊆ Φ '' Ω) :
    l2NormSq u ≤ ENNReal.ofReal M * l2NormSq (Ω.indicator (fun z => u (Φ z))) := by
  unfold l2NormSq
  have hsupp : Function.support (fun w => ‖u w‖ₑ ^ 2) ⊆ Φ '' Ω := by
    intro w hw
    refine hu (subset_tsupport _ ?_)
    intro h; apply hw; simp [h]
  rw [← setLIntegral_eq_of_support_subset hsupp, lintegral_image_holomorphic hΩ hΦ hinj]
  calc ∫⁻ z in Ω, ENNReal.ofReal (‖deriv Φ z‖ ^ 2) * ‖u (Φ z)‖ₑ ^ 2
      ≤ ∫⁻ z in Ω, ENNReal.ofReal M * ‖Ω.indicator (fun z => u (Φ z)) z‖ₑ ^ 2 := by
        refine setLIntegral_mono' hΩ.measurableSet fun z hz => ?_
        rw [Set.indicator_of_mem hz]
        gcongr
        exact hM z hz
    _ = ENNReal.ofReal M * ∫⁻ z in Ω, ‖Ω.indicator (fun z => u (Φ z)) z‖ₑ ^ 2 :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by gcongr; exact Measure.restrict_le_self

/-- **Conformal comparison.** If `Φ` maps `Ω` biholomorphically onto `Ω'` (with continuous
inverse `Ψ`) and `|Φ'|² ≤ M` on `Ω`, then `λ_j(Ω) ≤ M λ_j(Ω')`. -/
theorem dirichletEigenvalue_le_of_biholomorphic {Ω Ω' : Set ℂ} (hΩ : IsOpen Ω)
    {Φ Ψ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ Ω) (hinj : InjOn Φ Ω) (hΦΩ : Φ '' Ω = Ω')
    (hΨ : ContinuousOn Ψ Ω') (hΨmaps : MapsTo Ψ Ω' Ω) (hΦΨ : ∀ w ∈ Ω', Φ (Ψ w) = w)
    {M : ℝ} (hM0 : 0 < M) (hM : ∀ z ∈ Ω, ‖deriv Φ z‖ ^ 2 ≤ M) (j : ℕ) :
    dirichletEigenvalue Ω j ≤ ENNReal.ofReal M * dirichletEigenvalue Ω' j := by
  classical
  -- the pullback map
  let T : (ℂ → ℝ) →ₗ[ℝ] (ℂ → ℝ) :=
    { toFun := fun u => Ω.indicator (fun z => u (Φ z))
      map_add' := fun u v => by
        simp only [Pi.add_apply]
        exact Set.indicator_add Ω _ _
      map_smul' := fun c u => by
        simp only [Pi.smul_apply, RingHom.id_apply]
        exact Set.indicator_const_smul Ω c _ }
  have hT : ∀ u z, T u z = Ω.indicator (fun z => u (Φ z)) z := fun _ _ => rfl
  have hΨΦ : ∀ z ∈ Ω, Ψ (Φ z) = z := fun z hz =>
    hinj (hΨmaps (hΦΩ ▸ mem_image_of_mem Φ hz)) hz (hΦΨ _ (hΦΩ ▸ mem_image_of_mem Φ hz))
  -- smoothness of `Φ`
  have hΦsmooth : ∀ z ∈ Ω, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ z := fun z hz =>
    ((hΦ.contDiffOn hΩ (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).contDiffAt (hΩ.mem_nhds hz)).restrict_scalars ℝ
  -- pullbacks of test functions are test functions
  have hTtest : ∀ u ∈ testFunctions Ω', T u ∈ testFunctions Ω ∧
      (∀ z, z ∉ Ψ '' tsupport u → T u =ᶠ[𝓝 z] 0) := by
    intro u ⟨hu, hus, husub⟩
    set K := tsupport u with hK
    have hKc : IsCompact K := hus
    have hK'c : IsCompact (Ψ '' K) := hKc.image_of_continuousOn (hΨ.mono husub)
    have hK'Ω : Ψ '' K ⊆ Ω := by rintro _ ⟨w, hw, rfl⟩; exact hΨmaps (husub hw)
    have hsupp : ∀ z, T u z ≠ 0 → z ∈ Ψ '' K := by
      intro z hz
      rw [hT] at hz
      by_cases hzΩ : z ∈ Ω
      · rw [Set.indicator_of_mem hzΩ] at hz
        exact ⟨Φ z, subset_tsupport _ hz, hΨΦ z hzΩ⟩
      · rw [Set.indicator_of_notMem hzΩ] at hz; exact absurd rfl hz
    have hzero : ∀ z, z ∉ Ψ '' K → T u =ᶠ[𝓝 z] 0 := by
      intro z hz
      filter_upwards [hK'c.isClosed.isOpen_compl.mem_nhds hz] with y hy
      by_contra h
      exact hy (hsupp y h)
    refine ⟨⟨?_, HasCompactSupport.intro hK'c fun z hz => by_contra fun h => hz (hsupp z h),
      (closure_minimal (fun z hz => hsupp z hz) hK'c.isClosed).trans hK'Ω⟩, hzero⟩
    refine contDiff_iff_contDiffAt.2 fun z => ?_
    by_cases hzΩ : z ∈ Ω
    · have heq : (fun y => u (Φ y)) =ᶠ[𝓝 z] T u := by
        filter_upwards [hΩ.mem_nhds hzΩ] with y hy
        rw [hT, Set.indicator_of_mem hy]
      exact ((hu.contDiffAt).comp z (hΦsmooth z hzΩ)).congr_of_eventuallyEq heq.symm
    · have hz' : z ∉ Ψ '' K := fun h => hzΩ (hK'Ω h)
      exact contDiffAt_const.congr_of_eventuallyEq (hzero z hz')
  -- `T` is injective on test functions
  have hTinj : ∀ u ∈ testFunctions Ω', T u = 0 → u = 0 := by
    intro u ⟨_, _, husub⟩ h0
    funext w
    by_cases hw : w ∈ Ω'
    · have := congrFun h0 (Ψ w)
      rw [hT, Set.indicator_of_mem (hΨmaps hw), hΦΨ w hw] at this
      exact this
    · exact image_eq_zero_of_notMem_tsupport (fun h => hw (husub h))
  have hM' : ENNReal.ofReal M ≠ 0 := by simpa using hM0
  -- Rayleigh quotient bound
  have hray : ∀ u ∈ testFunctions Ω', rayleigh (T u) ≤ ENNReal.ofReal M * rayleigh u := by
    intro u hu
    have hE : dirichletEnergy (T u) ≤ dirichletEnergy u :=
      dirichletEnergy_pullback_le hΩ hΦ hinj hu.1 fun z hz => (hTtest u hu).2 z
        (by rintro ⟨w, hw, rfl⟩; exact hz (hΨmaps (hu.2.2 hw)))
    have hL : l2NormSq u ≤ ENNReal.ofReal M * l2NormSq (T u) :=
      l2NormSq_le_pullback hΩ hΦ hinj hM (hΦΩ ▸ hu.2.2)
    unfold rayleigh
    calc dirichletEnergy (T u) / l2NormSq (T u) ≤ dirichletEnergy u / l2NormSq (T u) :=
          ENNReal.div_le_div_right hE _
      _ ≤ ENNReal.ofReal M * (dirichletEnergy u / l2NormSq u) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, mul_left_comm]
          gcongr
          calc (l2NormSq (T u))⁻¹
              = ENNReal.ofReal M * (ENNReal.ofReal M * l2NormSq (T u))⁻¹ := by
                rw [ENNReal.mul_inv (Or.inl hM') (Or.inl ENNReal.ofReal_ne_top), ← mul_assoc,
                  ENNReal.mul_inv_cancel hM' ENNReal.ofReal_ne_top, one_mul]
            _ ≤ ENNReal.ofReal M * (l2NormSq u)⁻¹ := by
                gcongr
  -- min–max comparison
  rw [mul_comm, ← ENNReal.div_le_iff_le_mul (Or.inl hM') (Or.inl ENNReal.ofReal_ne_top)]
  conv_rhs => unfold dirichletEigenvalue
  refine le_iInf fun V => le_iInf fun hV => le_iInf fun hj => ?_
  rw [ENNReal.div_le_iff_le_mul (Or.inl hM') (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  have hinjV : Function.Injective (T.domRestrict V) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact Subtype.ext (hTinj x (hV x.2) (by simpa using hx))
  set W := LinearMap.range (T.domRestrict V) with hW
  have hWdim : Module.finrank ℝ W = j := by
    rw [hW, LinearMap.finrank_range_of_inj hinjV, hj]
  have hWle : W ≤ testFunctions Ω := by
    rintro _ ⟨x, rfl⟩
    exact (hTtest x (hV x.2)).1
  calc dirichletEigenvalue Ω j ≤ ⨆ (v : ℂ → ℝ) (_ : v ∈ W) (_ : v ≠ 0), rayleigh v := by
        unfold dirichletEigenvalue
        exact iInf_le_of_le W (iInf_le_of_le hWle (iInf_le_of_le hWdim le_rfl))
    _ ≤ _ := by
        refine iSup_le fun v => iSup_le fun hv => iSup_le fun hv0 => ?_
        obtain ⟨x, rfl⟩ := hv
        have hx0 : (x : ℂ → ℝ) ≠ 0 := by
          rintro h
          apply hv0
          simp [h]
        calc rayleigh (T.domRestrict V x) ≤ ENNReal.ofReal M * rayleigh x := hray x (hV x.2)
          _ ≤ _ := by
            gcongr
            exact le_iSup_of_le (x : ℂ → ℝ) (le_iSup_of_le x.2 (le_iSup_of_le hx0 le_rfl))

end

section

/-! ## Continuity of `r ↦ λ_j(F(r𝔻))` -/

open MeasureTheory Set Metric Filter Topology Complex

/-- Comparison of `λ_j(F(r𝔻))` and `λ_j(F(s𝔻))` for `r ≤ s` through the radial dilation. -/
lemma dirichletEigenvalue_image_ball_le_of_dilation (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hDU : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) (hs : s ≤ 1) {M : ℝ} (hM0 : 0 < M)
    (hM : ∀ ζ ∈ ball (0 : ℂ) r,
      (s / r) ^ 2 * ‖deriv F (((s / r : ℝ) : ℂ) * ζ)‖ ^ 2 ≤ M * ‖deriv F ζ‖ ^ 2) (j : ℕ) :
    dirichletEigenvalue (F '' ball 0 r) j ≤
      ENNReal.ofReal M * dirichletEigenvalue (F '' ball 0 s) j := by
  have hball1 : ball (0 : ℂ) 1 ⊆ U := ball_subset_closedBall.trans hDU
  have hpc : IsPreconnected (ball (0 : ℂ) 1) := (convex_ball _ _).isPreconnected
  obtain ⟨H, hHd, -, hHF, -⟩ := exists_holomorphic_inverse isOpen_ball hpc
    (hF.mono hball1) (hinj.mono hball1)
  have hopen : ∀ ρ : ℝ, ρ ≤ 1 → IsOpen (F '' ball 0 ρ) := fun ρ hρ =>
    isOpen_image_of_injOn isOpen_ball hpc
      (hF.mono hball1) (hinj.mono hball1) (ball_subset_ball hρ) isOpen_ball
  have hr1 : ball (0 : ℂ) r ⊆ ball 0 1 := ball_subset_ball (hrs.trans hs)
  have hs1 : ball (0 : ℂ) s ⊆ ball 0 1 := ball_subset_ball hs
  set c : ℝ := s / r with hc
  have hc0 : 0 < c := div_pos (hr.trans_le hrs) hr
  have hcr : c * r = s := by rw [hc]; field_simp
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
  have hnorm : ∀ ζ : ℂ, ‖(c : ℂ) * ζ‖ = c * ‖ζ‖ := fun ζ => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0.le]
  have hnorm' : ∀ ζ : ℂ, ‖(c : ℂ)⁻¹ * ζ‖ = c⁻¹ * ‖ζ‖ := fun ζ => by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hc0.le]
  have hbc : ∀ ζ ∈ ball (0 : ℂ) r, (c : ℂ) * ζ ∈ ball (0 : ℂ) s := fun ζ hζ => by
    rw [mem_ball_zero_iff] at hζ ⊢
    rw [hnorm, ← hcr]; exact mul_lt_mul_of_pos_left hζ hc0
  have hbc' : ∀ ξ ∈ ball (0 : ℂ) s, (c : ℂ)⁻¹ * ξ ∈ ball (0 : ℂ) r := fun ξ hξ => by
    rw [mem_ball_zero_iff] at hξ ⊢
    rw [hnorm', inv_mul_lt_iff₀ hc0, hcr]; exact hξ
  set Φ : ℂ → ℂ := fun w => F ((c : ℂ) * H w) with hΦ
  set Ψ : ℂ → ℂ := fun w => F ((c : ℂ)⁻¹ * H w) with hΨ
  have hHFr : ∀ ζ ∈ ball (0 : ℂ) r, H (F ζ) = ζ := fun ζ hζ => hHF ζ (hr1 hζ)
  have hHFs : ∀ ξ ∈ ball (0 : ℂ) s, H (F ξ) = ξ := fun ξ hξ => hHF ξ (hs1 hξ)
  -- `H` is differentiable at points of `F(𝔻)`
  have hHat : ∀ ζ ∈ ball (0 : ℂ) 1, DifferentiableAt ℂ H (F ζ) := fun ζ hζ =>
    (hHd (F ζ) ⟨ζ, hζ, rfl⟩).differentiableAt ((hopen 1 le_rfl).mem_nhds ⟨ζ, hζ, rfl⟩)
  refine dirichletEigenvalue_le_of_biholomorphic (hopen r (hrs.trans hs)) (Φ := Φ) (Ψ := Ψ)
    ?_ ?_ ?_ ?_ ?_ ?_ hM0 ?_ j
  · rintro _ ⟨ζ, hζ, rfl⟩
    have hFd : DifferentiableAt ℂ F ((c : ℂ) * H (F ζ)) := by
      rw [hHFr ζ hζ]
      exact hF.differentiableAt (hU.mem_nhds (hball1 (hs1 (hbc ζ hζ))))
    exact (hFd.comp (F ζ) ((differentiableAt_const _).mul (hHat ζ (hr1 hζ)))).differentiableWithinAt
  · rintro _ ⟨ζ₁, h₁, rfl⟩ _ ⟨ζ₂, h₂, rfl⟩ h
    simp only [hΦ, hHFr ζ₁ h₁, hHFr ζ₂ h₂] at h
    have := hinj (hball1 (hs1 (hbc ζ₁ h₁))) (hball1 (hs1 (hbc ζ₂ h₂))) h
    rw [mul_left_cancel₀ hcC this]
  · ext w
    constructor
    · rintro ⟨_, ⟨ζ, hζ, rfl⟩, rfl⟩
      exact ⟨(c : ℂ) * ζ, hbc ζ hζ, by simp only [hΦ, hHFr ζ hζ]⟩
    · rintro ⟨ξ, hξ, rfl⟩
      refine ⟨F ((c : ℂ)⁻¹ * ξ), ⟨_, hbc' ξ hξ, rfl⟩, ?_⟩
      simp only [hΦ, hHFr _ (hbc' ξ hξ), mul_inv_cancel_left₀ hcC]
  · have hHc : ContinuousOn H (F '' ball 0 s) := hHd.continuousOn.mono (image_mono hs1)
    refine hF.continuousOn.comp (continuousOn_const.mul hHc) ?_
    rintro _ ⟨ξ, hξ, rfl⟩
    show (c : ℂ)⁻¹ * H (F ξ) ∈ U
    rw [hHFs ξ hξ]
    exact hball1 (hr1 (hbc' ξ hξ))
  · rintro _ ⟨ξ, hξ, rfl⟩
    exact ⟨(c : ℂ)⁻¹ * ξ, hbc' ξ hξ, by simp only [hΨ, hHFs ξ hξ]⟩
  · rintro _ ⟨ξ, hξ, rfl⟩
    simp only [hΦ, hΨ, hHFs ξ hξ, hHFr _ (hbc' ξ hξ), mul_inv_cancel_left₀ hcC]
  · rintro _ ⟨ζ, hζ, rfl⟩
    have hζ1 := hr1 hζ
    have hHw : HasDerivAt H (deriv H (F ζ)) (F ζ) := (hHat ζ hζ1).hasDerivAt
    have hFζ : HasDerivAt F (deriv F ζ) (H (F ζ)) := by
      rw [hHF ζ hζ1]
      exact (hF.differentiableAt (hU.mem_nhds (hball1 hζ1))).hasDerivAt
    have hid : (fun w => F (H w)) =ᶠ[𝓝 (F ζ)] id := by
      filter_upwards [(hopen 1 le_rfl).mem_nhds ⟨ζ, hζ1, rfl⟩]
      rintro _ ⟨ξ, hξ, rfl⟩
      simp [hHF ξ hξ]
    have hprod : deriv F ζ * deriv H (F ζ) = 1 :=
      (hFζ.comp (F ζ) hHw).unique ((hasDerivAt_id (F ζ)).congr_of_eventuallyEq hid)
    have hFc : HasDerivAt F (deriv F ((c : ℂ) * H (F ζ))) ((c : ℂ) * H (F ζ)) := by
      rw [hHF ζ hζ1]
      exact (hF.differentiableAt (hU.mem_nhds (hball1 (hs1 (hbc ζ hζ))))).hasDerivAt
    have hΦd := hFc.comp (F ζ) (hHw.const_mul (c : ℂ))
    rw [show Φ = F ∘ fun w => (c : ℂ) * H w from rfl, hΦd.deriv, hHF ζ hζ1]
    have hMζ := hM ζ hζ
    have hn : ‖deriv F ζ‖ * ‖deriv H (F ζ)‖ = 1 := by
      rw [← norm_mul, hprod, norm_one]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0.le]
    have hH0 : 0 ≤ ‖deriv H (F ζ)‖ ^ 2 := sq_nonneg _
    calc (‖deriv F ((c : ℂ) * ζ)‖ * (c * ‖deriv H (F ζ)‖)) ^ 2
        = c ^ 2 * ‖deriv F ((c : ℂ) * ζ)‖ ^ 2 * ‖deriv H (F ζ)‖ ^ 2 := by ring
      _ ≤ M * ‖deriv F ζ‖ ^ 2 * ‖deriv H (F ζ)‖ ^ 2 := by gcongr
      _ = M * (‖deriv F ζ‖ * ‖deriv H (F ζ)‖) ^ 2 := by ring
      _ = M := by rw [hn]; ring

/-- Uniform control of the dilation factor: for `t > 1` and `s > r` close to `r`,
`(s/r)² |F'((s/r)ζ)|² ≤ t |F'(ζ)|²` on `ball 0 r`. -/
lemma eventually_dilation_bound (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hDU : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : 1 < t) :
    ∃ δ > 0, ∀ s, r ≤ s → s < r + δ → s ≤ 1 → ∀ ζ ∈ ball (0 : ℂ) r,
      (s / r) ^ 2 * ‖deriv F (((s / r : ℝ) : ℂ) * ζ)‖ ^ 2 ≤ t * ‖deriv F ζ‖ ^ 2 := by
  have hcont : ContinuousOn (deriv F) (closedBall 0 1) :=
    (hF.deriv hU).continuousOn.mono hDU
  obtain ⟨ζ₀, hζ₀, hmin⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_isMinOn
    ⟨0, mem_closedBall_self zero_le_one⟩ hcont.norm
  set m := ‖deriv F ζ₀‖ with hm
  have hm0 : 0 < m := norm_pos_iff.2 (deriv_ne_zero_of_injOn hU hF hinj (hDU hζ₀))
  set ρ := Real.sqrt (Real.sqrt t) with hρ
  have ht0 : 0 ≤ t := by linarith
  have hsq1 : 1 < Real.sqrt t := by rw [Real.lt_sqrt zero_le_one]; simpa using ht
  have hρ1 : 1 < ρ := by rw [hρ, Real.lt_sqrt zero_le_one]; simpa using hsq1
  have hρ2 : ρ ^ 2 = Real.sqrt t := Real.sq_sqrt (Real.sqrt_nonneg _)
  have ht2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0
  obtain ⟨δ₁, hδ₁, hunif⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_closedBall (0 : ℂ) 1).uniformContinuousOn_of_continuous hcont) (m * (ρ - 1))
    (by nlinarith)
  refine ⟨min δ₁ (r * (ρ - 1)), lt_min hδ₁ (by nlinarith), ?_⟩
  intro s hrs hsδ hs1 ζ hζ
  have hsδ₁ : s < r + δ₁ := hsδ.trans_le (by linarith [min_le_left δ₁ (r * (ρ - 1))])
  have hsρ : s < r + r * (ρ - 1) := hsδ.trans_le (by linarith [min_le_right δ₁ (r * (ρ - 1))])
  set c := s / r with hc
  have hc1 : 1 ≤ c := by rw [hc, le_div_iff₀ hr]; linarith
  have hcρ : c ≤ ρ := by rw [hc, div_le_iff₀ hr]; nlinarith
  have hζn : ‖ζ‖ < r := by simpa using hζ
  have hcs : c * r = s := by rw [hc]; field_simp
  have hnorm : ‖((c : ℝ) : ℂ) * ζ‖ = c * ‖ζ‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hζ1 : ζ ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall_zero_iff]; linarith
  have hcζ1 : ((c : ℝ) : ℂ) * ζ ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall_zero_iff, hnorm]; nlinarith [norm_nonneg ζ]
  have hdist : dist (((c : ℝ) : ℂ) * ζ) ζ < δ₁ := by
    rw [dist_eq_norm, show ((c : ℝ) : ℂ) * ζ - ζ = ((c - 1 : ℝ) : ℂ) * ζ by push_cast; ring,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    nlinarith [norm_nonneg ζ]
  have h1 := hunif _ hcζ1 _ hζ1 hdist
  rw [dist_eq_norm] at h1
  have hmle : m ≤ ‖deriv F ζ‖ := hmin hζ1
  have h2 : ‖deriv F (((c : ℝ) : ℂ) * ζ)‖ ≤ ρ * ‖deriv F ζ‖ := by
    have := norm_le_norm_add_norm_sub' (deriv F (((c : ℝ) : ℂ) * ζ)) (deriv F ζ)
    have h3 : ‖deriv F (((c : ℝ) : ℂ) * ζ) - deriv F ζ‖ ≤ (ρ - 1) * ‖deriv F ζ‖ := by
      nlinarith
    linarith
  have h0 : 0 ≤ ‖deriv F (((c : ℝ) : ℂ) * ζ)‖ := norm_nonneg _
  have h4 : c ^ 2 * ‖deriv F (((c : ℝ) : ℂ) * ζ)‖ ^ 2 ≤ ρ ^ 2 * (ρ ^ 2 * ‖deriv F ζ‖ ^ 2) := by
    have := pow_le_pow_left₀ h0 h2 2
    have h5 : c ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (by linarith) hcρ 2
    calc c ^ 2 * ‖deriv F (((c : ℝ) : ℂ) * ζ)‖ ^ 2 ≤ ρ ^ 2 * (ρ * ‖deriv F ζ‖) ^ 2 := by
          gcongr
      _ = _ := by ring
  calc c ^ 2 * ‖deriv F (((c : ℝ) : ℂ) * ζ)‖ ^ 2 ≤ ρ ^ 2 * (ρ ^ 2 * ‖deriv F ζ‖ ^ 2) := h4
    _ = t * ‖deriv F ζ‖ ^ 2 := by rw [← mul_assoc, ← sq, hρ2, ht2]

/-- `r ↦ λ_j(F(r𝔻))` is continuous on `(0, 1]`. -/
theorem dirichletEigenvalue_image_ball_continuousOn (F : ℂ → ℂ) (U : Set ℂ)
    (hU : IsOpen U) (hDU : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U)
    (hinj : InjOn F U) (j : ℕ) :
    ContinuousOn (fun r : ℝ => dirichletEigenvalue (F '' ball 0 r) j) (Ioc 0 1) := by
  set f : ℝ → ENNReal := fun r => dirichletEigenvalue (F '' ball 0 r) j with hfdef
  have hanti : ∀ {a b : ℝ}, a ≤ b → f b ≤ f a := fun h =>
    dirichletEigenvalue_anti (image_mono (ball_subset_ball h)) j
  have hball1 : ball (0 : ℂ) 1 ⊆ U := ball_subset_closedBall.trans hDU
  have hopen : ∀ s : ℝ, s ≤ 1 → IsOpen (F '' ball 0 s) := fun s hs =>
    isOpen_image_of_injOn isOpen_ball (convex_ball _ _).isPreconnected
      (hF.mono hball1) (hinj.mono hball1) (ball_subset_ball hs) isOpen_ball
  intro r hr
  rw [ContinuousWithinAt, tendsto_order]
  constructor
  · intro a ha
    have hlim : Tendsto (fun t : ℝ => ENNReal.ofReal t * a) (𝓝[>] 1)
        (𝓝 (ENNReal.ofReal 1 * a)) :=
      (ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal tendsto_id) (Or.inl (by simp))).mono_left
        nhdsWithin_le_nhds
    rw [ENNReal.ofReal_one, one_mul] at hlim
    obtain ⟨t, hta, ht1⟩ := ((hlim.eventually (gt_mem_nhds ha)).and self_mem_nhdsWithin).exists
    obtain ⟨δ, hδ, hbd⟩ := eventually_dilation_bound F U hU hDU hF hinj hr.1 (t := t) ht1
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by linarith : r < r + δ))] with s hs hsδ
    rcases le_or_gt s r with hsr | hsr
    · exact ha.trans_le (hanti hsr)
    · by_contra hle
      push_neg at hle
      have hcmp := dirichletEigenvalue_image_ball_le_of_dilation F U hU hDU hF hinj hr.1
        hsr.le hs.2 (by linarith : (0 : ℝ) < t) (hbd s hsr.le hsδ hs.2) j
      have : f r ≤ ENNReal.ofReal t * a := hcmp.trans (by gcongr)
      exact absurd (this.trans_lt hta) (lt_irrefl _)
  · intro a ha
    have : Nonempty (Ioo 0 r) := ⟨⟨r / 2, by linarith [hr.1], by linarith [hr.1]⟩⟩
    have hU' : F '' ball 0 r = ⋃ s : Ioo 0 r, F '' ball 0 (s : ℝ) := by
      rw [← image_iUnion]
      congr 1
      ext z
      simp only [mem_ball_iff_norm, sub_zero, mem_iUnion]
      constructor
      · intro hz
        refine ⟨⟨(‖z‖ + r) / 2, by linarith [norm_nonneg z], by linarith⟩, ?_⟩
        show ‖z‖ < (‖z‖ + r) / 2
        linarith
      · rintro ⟨s, hs⟩; exact hs.trans s.2.2
    have hinf := dirichletEigenvalue_iUnion_directed (fun s : Ioo 0 r => F '' ball 0 (s : ℝ))
      (fun s => hopen s (s.2.2.le.trans hr.2))
      (fun s₁ s₂ => ⟨if (s₁ : ℝ) ≤ s₂ then s₂ else s₁, by
        split_ifs with h
        · exact ⟨image_mono (ball_subset_ball h), subset_rfl⟩
        · exact ⟨subset_rfl, image_mono (ball_subset_ball (by push_neg at h; exact h.le))⟩⟩) j
    rw [← hU'] at hinf
    have hlt : ⨅ s : Ioo 0 r, dirichletEigenvalue (F '' ball 0 (s : ℝ)) j < a := hinf ▸ ha
    obtain ⟨s₀, hs₀⟩ := iInf_lt_iff.1 hlt
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds s₀.2.2)] with s hs
    exact (hanti (le_of_lt hs)).trans_lt hs₀

end

section

/-! ## Finiteness, positivity and strict monotonicity of `r ↦ λ_j(F(r𝔻))` -/

open MeasureTheory Set Metric Filter Topology Complex

/-- The squared norm of a finite sum with at most one nonzero term. -/
lemma enorm_sum_sq_of_pairwise {ι E : Type*} [NormedAddCommGroup E] (s : Finset ι) (f : ι → E)
    (hf : ∀ i ∈ s, ∀ k ∈ s, f i ≠ 0 → f k ≠ 0 → i = k) :
    ‖∑ i ∈ s, f i‖ₑ ^ 2 = ∑ i ∈ s, ‖f i‖ₑ ^ 2 := by
  classical
  by_cases h : ∃ i ∈ s, f i ≠ 0
  · obtain ⟨i, hi, hfi⟩ := h
    have h1 : ∑ k ∈ s, f k = f i :=
      Finset.sum_eq_single_of_mem i hi fun k hk hki => by
        by_contra hne; exact hki (hf k hk i hi hne hfi)
    have h2 : ∑ k ∈ s, ‖f k‖ₑ ^ 2 = ‖f i‖ₑ ^ 2 :=
      Finset.sum_eq_single_of_mem i hi fun k hk hki => by
        by_contra hne
        have : f k ≠ 0 := by
          intro h0; apply hne; simp [h0]
        exact hki (hf k hk i hi this hfi)
    rw [h1, h2]
  · push_neg at h
    rw [Finset.sum_eq_zero h, Finset.sum_eq_zero fun i hi => by simp [h i hi]]
    simp

/-- **Finiteness of Dirichlet eigenvalues.** On a nonempty open set, `λ_j(Ω) < ∞`. -/
theorem dirichletEigenvalue_lt_top {Ω : Set ℂ} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (j : ℕ) :
    dirichletEigenvalue Ω j < ⊤ := by
  classical
  obtain ⟨z0, hz0⟩ := hne
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.1 hΩ z0 hz0
  set ρ : ℝ := R / (3 * j + 2) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρR : 3 * ρ * j + ρ < R := by
    have : ρ * (3 * j + 2) = R := by rw [hρ]; field_simp
    nlinarith
  let φ : ContDiffBump (0 : ℂ) := ⟨ρ / 2, ρ, by positivity, by linarith⟩
  set f : ℂ → ℝ := ⇑φ with hf
  have hfs : ContDiff ℝ (⊤ : ℕ∞) f := φ.contDiff
  have hfsupp : ∀ x, f x ≠ 0 → x ∈ ball (0 : ℂ) ρ := fun x hx => by
    have : x ∈ Function.support f := hx
    rwa [hf, φ.support_eq] at this
  have hftsupp : tsupport f = closedBall (0 : ℂ) ρ := φ.tsupport_eq
  have hf0 : f 0 = 1 := φ.one_of_mem_closedBall (by simp; positivity)
  have hfc : HasCompactSupport f := φ.hasCompactSupport
  set c : Fin j → ℂ := fun i => z0 + ((3 * ρ * (i : ℕ) : ℝ) : ℂ) with hc
  have hcdist : ∀ i k : Fin j, i ≠ k → 3 * ρ ≤ ‖c i - c k‖ := by
    intro i k hik
    have : c i - c k = (((3 * ρ * ((i : ℕ) - (k : ℕ) : ℝ)) : ℝ) : ℂ) := by
      simp only [hc]; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
    have hne' : ((i : ℕ) : ℝ) ≠ (k : ℕ) := by
      exact_mod_cast fun h => hik (Fin.ext h)
    have : (1 : ℝ) ≤ |((i : ℕ) : ℝ) - (k : ℕ)| := by
      rcases lt_or_gt_of_ne hne' with h | h
      · have : ((i : ℕ) : ℝ) + 1 ≤ (k : ℕ) := by exact_mod_cast (show (i : ℕ) + 1 ≤ k by exact_mod_cast h)
        rw [abs_of_neg (by linarith)]; linarith
      · have : ((k : ℕ) : ℝ) + 1 ≤ (i : ℕ) := by exact_mod_cast (show (k : ℕ) + 1 ≤ i by exact_mod_cast h)
        rw [abs_of_pos (by linarith)]; linarith
    nlinarith
  -- two closed balls of radius `ρ` around distinct centres are disjoint
  have hdisj : ∀ i k : Fin j, ∀ z : ℂ, ‖z - c i‖ ≤ ρ → ‖z - c k‖ ≤ ρ → i = k := by
    intro i k z hi hk
    by_contra hik
    have h1 := hcdist i k hik
    have : ‖c i - c k‖ ≤ ‖z - c k‖ + ‖z - c i‖ := by
      calc ‖c i - c k‖ = ‖(z - c k) - (z - c i)‖ := by congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    linarith
  have hcball : ∀ i : Fin j, closedBall (c i) ρ ⊆ Ω := by
    intro i z hz
    apply hball
    rw [mem_ball, dist_eq_norm]
    rw [mem_closedBall, dist_eq_norm] at hz
    have hci : ‖c i - z0‖ ≤ 3 * ρ * j := by
      simp only [hc, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      have : ((i : ℕ) : ℝ) ≤ j := by exact_mod_cast i.2.le
      nlinarith
    calc ‖z - z0‖ = ‖(z - c i) + (c i - z0)‖ := by congr 1; ring
      _ ≤ ‖z - c i‖ + ‖c i - z0‖ := norm_add_le _ _
      _ < R := by linarith
  -- the translated bumps and the linear map `a ↦ ∑ aᵢ uᵢ`
  set u : Fin j → ℂ → ℝ := fun i z => f (z - c i) with hu
  let T : (Fin j → ℝ) →ₗ[ℝ] (ℂ → ℝ) :=
    { toFun := fun a => ∑ i, a i • u i
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r a => by simp [Finset.smul_sum, smul_smul] }
  have hTapp : ∀ a z, T a z = ∑ i, a i * f (z - c i) := fun a z => by
    simp [T, hu, Finset.sum_apply]
  have hutest : ∀ i, u i ∈ testFunctions Ω := by
    intro i
    refine ⟨hfs.comp (contDiff_id.sub contDiff_const), ?_, ?_⟩
    · exact hfc.comp_homeomorph (Homeomorph.subRight (c i))
    · refine (closure_minimal ?_ isClosed_closedBall).trans (hcball i)
      intro z hz
      have := hfsupp _ hz
      rw [mem_ball_zero_iff] at this
      rw [mem_closedBall, dist_eq_norm]; exact this.le
  have hVle : LinearMap.range T ≤ testFunctions Ω := by
    rintro _ ⟨a, rfl⟩
    show ∑ i, a i • u i ∈ _
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hutest i)
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    funext k
    have := congrFun ha (c k)
    rw [hTapp, Finset.sum_eq_single k] at this
    · simpa [hf0] using this
    · intro i _ hik
      have : f (c k - c i) = 0 := by
        by_contra h
        have h1 := hfsupp _ h
        rw [mem_ball_zero_iff] at h1
        exact hik (hdisj i k (c k) h1.le (by simp; positivity))
      simp [this]
    · simp
  have hdim : Module.finrank ℝ (LinearMap.range T) = j := by
    rw [LinearMap.finrank_range_of_inj hTinj]; simp
  -- energy and mass of the bump
  set E := dirichletEnergy f with hE
  set N := l2NormSq f with hN
  have hfdc : Continuous (fderiv ℝ f) := hfs.continuous_fderiv (by simp)
  have hEfin : E ≠ ⊤ := by
    have h2 : MemLp (fderiv ℝ f) 2 volume :=
      hfdc.memLp_of_hasCompactSupport (HasCompactSupport.fderiv (𝕜 := ℝ) hfc)
    have := h2.eLpNorm_lt_top
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
      h2.aestronglyMeasurable] at this
    simpa [hE, dirichletEnergy] using this.ne
  have hN0 : N ≠ 0 := (l2NormSq_pos_of_ne_zero hfs.continuous (fun h => by
    have := congrFun h 0; rw [hf0] at this; simp at this)).ne'
  -- the Rayleigh quotient is constant on `range T \ {0}`
  have hray : ∀ a : Fin j → ℝ, T a ≠ 0 → rayleigh (T a) = E / N := by
    intro a ha
    set S : ENNReal := ∑ i, ‖a i‖ₑ ^ 2 with hS
    have hl2 : l2NormSq (T a) = S * N := by
      calc l2NormSq (T a) = ∫⁻ z, ∑ i, ‖a i‖ₑ ^ 2 * ‖f (z - c i)‖ₑ ^ 2 := by
            refine lintegral_congr fun z => ?_
            rw [hTapp, enorm_sum_sq_of_pairwise]
            · simp only [enorm_mul, mul_pow]
            · intro i _ k _ hi hk
              exact hdisj i k z (mem_ball_zero_iff.1 (hfsupp _ (right_ne_zero_of_mul hi))).le
                (mem_ball_zero_iff.1 (hfsupp _ (right_ne_zero_of_mul hk))).le
        _ = ∑ i, ‖a i‖ₑ ^ 2 * N := by
            rw [lintegral_finset_sum]
            · refine Finset.sum_congr rfl fun i _ => ?_
              rw [lintegral_const_mul, lintegral_sub_right_eq_self (fun z => ‖f z‖ₑ ^ 2) (c i)]
              · rfl
              · exact ((hfs.continuous.comp (continuous_sub_right (c i))).measurable.enorm.pow_const 2)
            · intro i _
              exact ((hfs.continuous.comp (continuous_sub_right (c i))).measurable.enorm.pow_const 2).const_mul _
        _ = S * N := by rw [hS, Finset.sum_mul]
    have hfd : ∀ z, fderiv ℝ (T a) z = ∑ i, a i • fderiv ℝ f (z - c i) := by
      intro z
      have hTfun : (T a : ℂ → ℝ) = fun z => ∑ i, a i * f (z - c i) := funext (hTapp a)
      rw [hTfun]
      refine HasFDerivAt.fderiv ?_
      refine HasFDerivAt.fun_sum fun i _ => ?_
      have h1 : HasFDerivAt (fun z => f (z - c i)) (fderiv ℝ f (z - c i)) z := by
        have := ((hfs.differentiable (by simp)) (z - c i)).hasFDerivAt.comp z
          ((hasFDerivAt_id z).sub_const (c i))
        convert this using 1
        · funext x
          rfl
        · simp
      exact h1.const_mul (a i)
    have hen : dirichletEnergy (T a) = S * E := by
      calc dirichletEnergy (T a) = ∫⁻ z, ∑ i, ‖a i‖ₑ ^ 2 * ‖fderiv ℝ f (z - c i)‖ₑ ^ 2 := by
            refine lintegral_congr fun z => ?_
            rw [hfd, enorm_sum_sq_of_pairwise]
            · simp only [enorm_smul, mul_pow]
            · intro i _ k _ hi hk
              have hi' := support_fderiv_subset ℝ (right_ne_zero_of_smul hi)
              have hk' := support_fderiv_subset ℝ (right_ne_zero_of_smul hk)
              rw [hftsupp, mem_closedBall, dist_zero_right] at hi' hk'
              exact hdisj i k z hi' hk'
        _ = ∑ i, ‖a i‖ₑ ^ 2 * E := by
            rw [lintegral_finset_sum]
            · refine Finset.sum_congr rfl fun i _ => ?_
              rw [lintegral_const_mul,
                lintegral_sub_right_eq_self (fun z => ‖fderiv ℝ f z‖ₑ ^ 2) (c i)]
              · rfl
              · exact ((hfdc.comp (continuous_sub_right (c i))).measurable.enorm.pow_const 2)
            · intro i _
              exact ((hfdc.comp (continuous_sub_right (c i))).measurable.enorm.pow_const 2).const_mul _
        _ = S * E := by rw [hS, Finset.sum_mul]
    have hS0 : S ≠ 0 := by
      intro h0
      apply ha
      have : ∀ i, a i = 0 := fun i => by
        have := (Finset.sum_eq_zero_iff.1 h0) i (Finset.mem_univ i)
        simpa using this
      funext z; rw [hTapp]; simp [this]
    have hStop : S ≠ ⊤ := by
      rw [hS]; exact ENNReal.sum_ne_top.2 fun i _ => by simp
    rw [rayleigh, hl2, hen, ENNReal.mul_div_mul_left _ _ hS0 hStop]
  calc dirichletEigenvalue Ω j
      ≤ ⨆ (v : ℂ → ℝ) (_ : v ∈ LinearMap.range T) (_ : v ≠ 0), rayleigh v :=
        iInf_le_of_le (LinearMap.range T) (iInf_le_of_le hVle (iInf_le _ hdim))
    _ ≤ E / N := by
        refine iSup_le fun v => iSup_le fun hv => iSup_le fun hv0 => ?_
        obtain ⟨a, rfl⟩ := hv
        exact (hray a hv0).le
    _ < ⊤ := ENNReal.div_lt_top hEfin hN0

/-- **Positivity of Dirichlet eigenvalues** on bounded sets:
`0 < λ_j(Ω)` for `j ≥ 1`. -/
theorem dirichletEigenvalue_pos (Ω : Set ℂ) (hb : Bornology.IsBounded Ω) {j : ℕ}
    (hj : 1 ≤ j) : 0 < dirichletEigenvalue Ω j := by
  refine lt_of_lt_of_le ?_ (dirichletEigenvalue_mono Ω hj)
  obtain ⟨C, hC, hP⟩ := poincare_inequality Ω hb
  have key : (C : ENNReal)⁻¹ ≤ dirichletEigenvalue Ω 1 := by
    unfold dirichletEigenvalue
    refine le_iInf fun V => le_iInf fun hV => le_iInf fun hdim => ?_
    obtain ⟨⟨u, huV⟩, hu0⟩ : ∃ x : V, x ≠ 0 := by
      have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hdim
      exact exists_ne 0
    have hu0' : u ≠ 0 := fun h => hu0 (Subtype.ext h)
    refine le_iSup_of_le u (le_iSup_of_le huV (le_iSup_of_le hu0' ?_))
    have htest := hV huV
    have hl2pos := l2NormSq_pos_of_ne_zero htest.1.continuous hu0'
    have hl2fin : l2NormSq u ≠ ⊤ := by
      unfold l2NormSq
      have h2 : MemLp u 2 volume := htest.1.continuous.memLp_of_hasCompactSupport htest.2.1
      have := h2.eLpNorm_lt_top
      rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
        h2.aestronglyMeasurable] at this
      simpa using this.ne
    unfold rayleigh
    rw [ENNReal.le_div_iff_mul_le (Or.inl hl2pos.ne') (Or.inl hl2fin)]
    calc (C : ENNReal)⁻¹ * l2NormSq u ≤ (C : ENNReal)⁻¹ * (C * dirichletEnergy u) := by
          gcongr; exact hP u htest
      _ = dirichletEnergy u := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hC.ne') ENNReal.coe_ne_top,
            one_mul]
  exact lt_of_lt_of_le (ENNReal.inv_pos.2 ENNReal.coe_ne_top) key

/-- Homothety comparison: `λ_j(Ω) ≤ c² λ_j(p + c(Ω - p))` for `c > 0`. -/
lemma dirichletEigenvalue_le_homothety {Ω : Set ℂ} (hΩ : IsOpen Ω) (p : ℂ) {c : ℝ}
    (hc : 0 < c) (j : ℕ) :
    dirichletEigenvalue Ω j ≤
      ENNReal.ofReal (c ^ 2) * dirichletEigenvalue ((fun w => p + (c : ℂ) * (w - p)) '' Ω) j := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hd : ∀ z, HasDerivAt (fun w => p + (c : ℂ) * (w - p)) (c : ℂ) z := fun z => by
    simpa using ((hasDerivAt_id z).sub_const p).const_mul (c : ℂ) |>.const_add p
  refine dirichletEigenvalue_le_of_biholomorphic hΩ (Ψ := fun w => p + (c : ℂ)⁻¹ * (w - p))
    (fun z _ => (hd z).differentiableAt.differentiableWithinAt) ?_ rfl (by fun_prop) ?_ ?_
    (by positivity) ?_ j
  · intro x _ y _ h
    simpa [hcC, sub_eq_iff_eq_add] using h
  · rintro _ ⟨z, hz, rfl⟩
    simpa [hcC] using hz
  · rintro _ ⟨z, hz, rfl⟩
    simp [hcC]
  · intro z _
    rw [(hd z).deriv, Complex.norm_real, Real.norm_of_nonneg hc.le]

/-- For each `j ≥ 1`, `r ↦ λ_j(F(r𝔻))` is
strictly decreasing on `(0, 1]`. -/
theorem dirichletEigenvalue_image_ball_strictAntiOn (F : ℂ → ℂ) (U : Set ℂ)
    (hDU : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    {j : ℕ} (hj : 1 ≤ j) :
    StrictAntiOn (fun r : ℝ => dirichletEigenvalue (F '' ball 0 r) j) (Ioc 0 1) := by
  intro a ha b hb hab
  simp only
  have hball1 : ball (0 : ℂ) 1 ⊆ U := ball_subset_closedBall.trans hDU
  have hpc : IsPreconnected (ball (0 : ℂ) 1) := (convex_ball _ _).isPreconnected
  have hopen : ∀ ρ : ℝ, ρ ≤ 1 → IsOpen (F '' ball 0 ρ) := fun ρ hρ =>
    isOpen_image_of_injOn isOpen_ball hpc
      (hF.mono hball1) (hinj.mono hball1) (ball_subset_ball hρ) isOpen_ball
  have haU : closedBall (0 : ℂ) a ⊆ U :=
    (closedBall_subset_ball (hab.trans_le hb.2)).trans hball1
  set K := F '' closedBall 0 a with hKdef
  have hKc : IsCompact K := (isCompact_closedBall 0 a).image_of_continuousOn
    (hF.continuousOn.mono haU)
  have hKb : K ⊆ F '' ball 0 b := image_mono (closedBall_subset_ball hab)
  obtain ⟨δ, hδ, hδK⟩ := hKc.exists_thickening_subset_open (hopen b hb.2) hKb
  set p := F 0
  obtain ⟨R, hR⟩ := hKc.isBounded.subset_closedBall p
  set D := |R| + 1 with hD
  have hD0 : 0 < D := by positivity
  have hKD : ∀ w ∈ K, ‖w - p‖ ≤ D := fun w hw => by
    have := hR hw; rw [mem_closedBall, dist_eq_norm] at this
    linarith [le_abs_self R]
  set c : ℝ := D / (D + δ / 2) with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c < 1 := by rw [hc, div_lt_one (by positivity)]; linarith
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
  have hsub : F '' ball 0 a ⊆ (fun w => p + (c : ℂ) * (w - p)) '' (F '' ball 0 b) := by
    intro w hw
    have hwK : w ∈ K := image_mono ball_subset_closedBall hw
    refine ⟨p + (c : ℂ)⁻¹ * (w - p), hδK ?_, by simp [hcC]⟩
    rw [mem_thickening_iff]
    refine ⟨w, hwK, ?_⟩
    have he : p + (c : ℂ)⁻¹ * (w - p) - w = ((c⁻¹ - 1 : ℝ) : ℂ) * (w - p) := by
      push_cast; ring
    have hci : c⁻¹ - 1 = δ / 2 / D := by
      rw [hc, inv_div]; field_simp; ring
    rw [dist_eq_norm, he, norm_mul, Complex.norm_real, hci,
      Real.norm_of_nonneg (by positivity)]
    calc δ / 2 / D * ‖w - p‖ ≤ δ / 2 / D * D := by gcongr; exact hKD w hwK
      _ = δ / 2 := by field_simp
      _ < δ := by linarith
  have hpos : 0 < dirichletEigenvalue (F '' ball 0 a) j :=
    dirichletEigenvalue_pos _ (hKc.isBounded.subset (image_mono ball_subset_closedBall)) hj
  have hfin : dirichletEigenvalue (F '' ball 0 a) j < ⊤ :=
    dirichletEigenvalue_lt_top (hopen a (hab.trans_le hb.2).le) ⟨F 0, 0, mem_ball_self ha.1, rfl⟩ j
  calc dirichletEigenvalue (F '' ball 0 b) j
      ≤ ENNReal.ofReal (c ^ 2) *
          dirichletEigenvalue ((fun w => p + (c : ℂ) * (w - p)) '' (F '' ball 0 b)) j :=
        dirichletEigenvalue_le_homothety (hopen b hb.2) p hc0 j
    _ ≤ ENNReal.ofReal (c ^ 2) * dirichletEigenvalue (F '' ball 0 a) j := by
        gcongr; exact dirichletEigenvalue_anti hsub j
    _ < dirichletEigenvalue (F '' ball 0 a) j := by
        have hc2 : ENNReal.ofReal (c ^ 2) < 1 := by
          rw [ENNReal.ofReal_lt_one]; nlinarith
        calc _ < 1 * dirichletEigenvalue (F '' ball 0 a) j := ENNReal.mul_lt_mul_left hpos.ne' hfin.ne hc2
            _ = _ := one_mul _

end

section

/-! ## Eigenvalues on an arc from a quadratic-form test -/

open scoped InnerProductSpace ComplexConjugate
open Set Metric Filter Topology Complex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Cauchy–Schwarz for a positive operator: `‖A x‖² ≤ ‖A‖ Re ⟪x, A x⟫`. -/
lemma norm_apply_sq_le_of_isPositive {A : E →L[ℂ] E} (hA : A.IsPositive) (x : E) :
    ‖A x‖ ^ 2 ≤ ‖A‖ * RCLike.re ⟪x, A x⟫_ℂ := by
  have h0 : 0 ≤ A := (ContinuousLinearMap.nonneg_iff_isPositive).2 hA
  set S := CFC.sqrt A
  have hS : S * S = A := CFC.sqrt_mul_sqrt_self A h0
  have hSsa : IsSelfAdjoint S := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hSS : ‖S‖ ^ 2 = ‖A‖ := by
    rw [← hS, sq]
    have := CStarRing.norm_star_mul_self (x := S)
    rw [hSsa.star_eq] at this
    rw [this]
  have h1 : ‖S x‖ ^ 2 = RCLike.re ⟪x, A x⟫_ℂ := by
    rw [← hS, ContinuousLinearMap.mul_apply]
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
      hSsa.star_eq]
    rw [@norm_sq_eq_re_inner ℂ]
  calc ‖A x‖ ^ 2 = ‖S (S x)‖ ^ 2 := by rw [← hS]; rfl
    _ ≤ (‖S‖ * ‖S x‖) ^ 2 := by gcongr; exact S.le_opNorm _
    _ = ‖A‖ * RCLike.re ⟪x, A x⟫_ℂ := by rw [mul_pow, hSS, h1]

/-- A compact self-adjoint operator whose quadratic form takes a positive value has an
eigenvector with a positive eigenvalue; if it commutes with `U`, the eigenvector can be chosen
to be an eigenvector of `U` as well. -/
lemma exists_joint_eigenvector {G U : E →L[ℂ] E} (hGc : IsCompactOperator (G : E → E))
    (hGs : IsSelfAdjoint G) (hcomm : U * G = G * U) {y₀ : E}
    (hy₀ : 0 < RCLike.re ⟪y₀, G y₀⟫_ℂ) :
    ∃ M : ℝ, 0 < M ∧ ∃ x : E, x ≠ 0 ∧ G x = (M : ℂ) • x ∧ ∃ μ : ℂ, U x = μ • x := by
  classical
  have hscale : ∀ (c : ℝ) (k : E), RCLike.re ⟪(c : ℂ) • k, G ((c : ℂ) • k)⟫_ℂ =
      c ^ 2 * RCLike.re ⟪k, G k⟫_ℂ := by
    intro c k
    rw [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc,
      ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.re_ofReal_mul, RCLike.re_to_complex]
    ring
  have hbd : ∀ y : E, RCLike.re ⟪y, G y⟫_ℂ ≤ ‖G‖ * ‖y‖ ^ 2 := fun y =>
    calc RCLike.re ⟪y, G y⟫_ℂ ≤ ‖⟪y, G y⟫_ℂ‖ := RCLike.re_le_norm _
      _ ≤ ‖y‖ * ‖G y‖ := norm_inner_le_norm _ _
      _ ≤ ‖y‖ * (‖G‖ * ‖y‖) := by gcongr; exact G.le_opNorm _
      _ = ‖G‖ * ‖y‖ ^ 2 := by ring
  set S := (fun y => RCLike.re ⟪y, G y⟫_ℂ) '' closedBall (0 : E) 1 with hSdef
  have hSne : S.Nonempty := ⟨_, 0, by simp, rfl⟩
  have hSbdd : BddAbove S := ⟨‖G‖, by
    rintro _ ⟨y, hy, rfl⟩
    have hy1 : ‖y‖ ≤ 1 := by simpa using hy
    calc RCLike.re ⟪y, G y⟫_ℂ ≤ ‖G‖ * ‖y‖ ^ 2 := hbd y
      _ ≤ ‖G‖ * 1 := by gcongr; nlinarith [norm_nonneg y]
      _ = ‖G‖ := mul_one _⟩
  set M := sSup S with hMdef
  have hle : ∀ z : E, RCLike.re ⟪z, G z⟫_ℂ ≤ M * ‖z‖ ^ 2 := by
    intro z
    by_cases hz : z = 0
    · simp [hz]
    have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hmem : RCLike.re ⟪((‖z‖⁻¹ : ℝ) : ℂ) • z, G (((‖z‖⁻¹ : ℝ) : ℂ) • z)⟫_ℂ ∈ S :=
      ⟨_, by rw [mem_closedBall_zero_iff, norm_real_inv_norm_smul hz], rfl⟩
    have h1 := le_csSup hSbdd hmem
    rw [hscale, inv_pow] at h1
    rw [← hMdef] at h1
    have := (inv_mul_le_iff₀ (by positivity : (0:ℝ) < ‖z‖ ^ 2)).1 h1
    linarith
  have hMpos : 0 < M := by
    have := hle y₀
    by_contra h
    push_neg at h
    nlinarith [sq_nonneg ‖y₀‖]
  -- a maximizing sequence
  have hseq : ∀ n : ℕ, ∃ y ∈ closedBall (0 : E) 1,
      M - 1 / (n + 1) < RCLike.re ⟪y, G y⟫_ℂ := by
    intro n
    obtain ⟨_, ⟨y, hy, rfl⟩, h⟩ := exists_lt_of_lt_csSup hSne
      (show M - 1 / ((n : ℝ) + 1) < M by linarith [show (0:ℝ) < 1 / ((n:ℝ)+1) by positivity])
    exact ⟨y, hy, h⟩
  choose y hy hyM using hseq
  set A : E →L[ℂ] E := (M : ℂ) • 1 - G with hA
  have hAre : ∀ x, RCLike.re ⟪x, A x⟫_ℂ = M * ‖x‖ ^ 2 - RCLike.re ⟪x, G x⟫_ℂ := by
    intro x
    have e1 : ⟪x, A x⟫_ℂ = (M:ℂ) * ⟪x, x⟫_ℂ - ⟪x, G x⟫_ℂ := by
      simp only [hA, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, inner_sub_right, inner_smul_right]
    rw [e1, map_sub, @norm_sq_eq_re_inner ℂ]
    congr 1
    simp
  have hApos : A.IsPositive := by
    refine ContinuousLinearMap.isPositive_def'.2 ⟨?_, fun x => ?_⟩
    · refine IsSelfAdjoint.sub ?_ hGs
      rw [IsSelfAdjoint, star_smul, star_one]
      simp [Complex.conj_ofReal]
    · rw [ContinuousLinearMap.reApplyInnerSelf]
      have h1 : RCLike.re ⟪A x, x⟫_ℂ = RCLike.re ⟪x, A x⟫_ℂ := by
        rw [← inner_conj_symm (A x) x, RCLike.conj_re]
      rw [h1, hAre]
      linarith [hle x]
  have hAy : ∀ n, ‖A (y n)‖ ^ 2 ≤ ‖A‖ * (1 / (n + 1)) := by
    intro n
    have hy1 : ‖y n‖ ≤ 1 := by simpa using hy n
    refine (norm_apply_sq_le_of_isPositive hApos _).trans ?_
    gcongr
    rw [hAre]
    have : M * ‖y n‖ ^ 2 ≤ M := by
      have : ‖y n‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (y n)]
      nlinarith
    linarith [hyM n]
  have h1n : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hAy0 : Tendsto (fun n => A (y n)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n : ℕ => Real.sqrt (‖A‖ * (1 / (n + 1)))) atTop (𝓝 0) := by
      have h3 : Tendsto (fun n : ℕ => ‖A‖ * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
        simpa using h1n.const_mul ‖A‖
      have := (Real.continuous_sqrt.tendsto 0).comp h3
      simpa [Function.comp_def] using this
    refine squeeze_zero_norm (fun n => ?_) h2
    exact Real.le_sqrt_of_sq_le (hAy n)
  obtain ⟨Sc, hSc, hCS⟩ := IsCompactOperator.image_closedBall_subset_compact
    (f := (G : E →ₗ[ℂ] E)) hGc 1
  have hGyS : ∀ n, G (y n) ∈ Sc := fun n => hCS ⟨y n, hy n, rfl⟩
  obtain ⟨z, -, ψ, hψ, hz⟩ := hSc.tendsto_subseq hGyS
  have hψt : Tendsto ψ atTop atTop := hψ.tendsto_atTop
  have hMne : (M : ℂ) ≠ 0 := by exact_mod_cast hMpos.ne'
  have hid : ∀ n, y n = (M : ℂ)⁻¹ • (A (y n) + G (y n)) := by
    intro n
    simp only [hA, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, sub_add_cancel, smul_smul, inv_mul_cancel₀ hMne, one_smul]
  set x := (M : ℂ)⁻¹ • z with hx
  have hyx : Tendsto (fun n => y (ψ n)) atTop (𝓝 x) := by
    have := ((hAy0.comp hψt).add hz).const_smul (M : ℂ)⁻¹
    rw [zero_add] at this
    refine this.congr fun n => ?_
    simp only [Function.comp_apply]
    exact (hid _).symm
  have hAx : A x = 0 :=
    tendsto_nhds_unique ((A.continuous.tendsto x).comp hyx) (hAy0.comp hψt)
  have hGx : G x = (M : ℂ) • x := by
    have := hAx
    simp only [hA, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, sub_eq_zero] at this
    exact this.symm
  have hxM : M ≤ RCLike.re ⟪x, G x⟫_ℂ := by
    have hc : Continuous fun w : E => RCLike.re ⟪w, G w⟫_ℂ := by fun_prop
    have hl : Tendsto (fun n => M - 1 / ((ψ n : ℝ) + 1)) atTop (𝓝 M) := by
      have := (tendsto_const_nhds (x := M)).sub (h1n.comp hψt)
      rw [sub_zero] at this
      exact this
    refine le_of_tendsto_of_tendsto' hl ((hc.tendsto x).comp hyx) (fun n => ?_)
    simp only [Function.comp_apply]
    exact (hyM (ψ n)).le
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0] at hxM
    simp at hxM
    linarith
  -- the eigenspace `ker (G - M)` is finite-dimensional and `U`-invariant
  set K := LinearMap.ker ((G - (M : ℂ) • 1 : E →L[ℂ] E) : E →ₗ[ℂ] E) with hK
  have hfd : FiniteDimensional ℂ K := by
    have hC : IsCompactOperator ((G + 1 - 1 : E →L[ℂ] E) : E → E) := by
      rw [add_sub_cancel_right]; exact hGc
    have h := finiteDimensional_ker_of_isCompactOperator hC (w := (M : ℂ) + 1)
      (by intro h; have : (M : ℂ) = 0 := by linear_combination h
          exact hMpos.ne' (by exact_mod_cast this))
    have he : (G + 1 - ((M : ℂ) + 1) • 1 : E →L[ℂ] E) = G - (M : ℂ) • 1 := by
      rw [add_smul, one_smul]; abel
    rw [he] at h
    exact h
  have hmem : ∀ w : E, w ∈ K ↔ G w = (M : ℂ) • w := by
    intro w
    simp [hK, sub_eq_zero]
  have hxK : x ∈ K := (hmem x).2 hGx
  have hmaps : ∀ w ∈ K, (U : E →ₗ[ℂ] E) w ∈ K := by
    intro w hw
    rw [hmem] at hw ⊢
    have : G (U w) = U (G w) := by
      rw [← ContinuousLinearMap.mul_apply, ← hcomm, ContinuousLinearMap.mul_apply]
    simp only [ContinuousLinearMap.coe_coe]
    rw [this, hw, map_smul]
  set f : Module.End ℂ K := (U : E →ₗ[ℂ] E).restrict hmaps
  haveI : Nontrivial K := ⟨⟨⟨x, hxK⟩, 0, by
    intro h; apply hx0; simpa using congrArg Subtype.val h⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  refine ⟨M, hMpos, v, ?_, (hmem v).1 v.2, c, ?_⟩
  · intro h; exact hv.2 (Subtype.ext h)
  · have := Module.End.mem_eigenspace_iff.1 hv.1
    have := congrArg Subtype.val this
    simpa [f] using this

/-- The self-adjoint operator `cot(α/2)(2 - U - U*) + i(U - U*)` whose quadratic form is
`cot(α/2) ‖y - U y‖² - 2 Im ⟪y, U y⟫`. -/
def arcForm (U : E →L[ℂ] E) (c : ℝ) : E →L[ℂ] E :=
  (c : ℂ) • ((2 : ℂ) • 1 - U - star U) + I • (U - star U)

lemma norm_apply_eq_of_mem_unitary {U : E →L[ℂ] E} (hU : U ∈ unitary (E →L[ℂ] E)) (y : E) :
    ‖U y‖ = ‖y‖ := by
  have h : ‖U y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, ← ContinuousLinearMap.adjoint_inner_right,
      ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.mul_apply,
      Unitary.star_mul_self_of_mem hU, ContinuousLinearMap.one_apply]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

lemma re_inner_arcForm {U : E →L[ℂ] E} (hU : U ∈ unitary (E →L[ℂ] E)) (c : ℝ) (y : E) :
    RCLike.re ⟪y, arcForm U c y⟫_ℂ = c * ‖y - U y‖ ^ 2 - 2 * (⟪y, U y⟫_ℂ).im := by
  have hs : ⟪y, star U y⟫_ℂ = conj ⟪y, U y⟫_ℂ := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
      inner_conj_symm]
  have hn : ‖y - U y‖ ^ 2 = 2 * ‖y‖ ^ 2 - 2 * (⟪y, U y⟫_ℂ).re := by
    rw [@norm_sub_sq ℂ, norm_apply_eq_of_mem_unitary hU]
    simp only [RCLike.re_to_complex]; ring
  have hyy : ⟪y, y⟫_ℂ = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  simp only [arcForm, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, inner_add_right,
    inner_smul_right, inner_sub_right, hs, hyy]
  rw [hn]
  simp only [RCLike.re_to_complex, Complex.add_re, Complex.mul_re, Complex.sub_re,
    Complex.sub_im, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
  norm_num
  ring

lemma isSelfAdjoint_arcForm (U : E →L[ℂ] E) (c : ℝ) : IsSelfAdjoint (arcForm U c) := by
  unfold arcForm
  rw [IsSelfAdjoint, star_add, star_smul, star_smul, star_sub, star_sub, star_sub, star_star,
    star_smul, star_one]
  simp only [Complex.star_def, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  rw [neg_smul, ← smul_neg, neg_sub, sub_right_comm]

lemma isCompactOperator_arcForm {U : E →L[ℂ] E} (hU : U ∈ unitary (E →L[ℂ] E))
    (hC : IsCompactOperator ((U - 1 : E →L[ℂ] E) : E → E)) (c : ℝ) :
    IsCompactOperator (arcForm U c : E → E) := by
  have hS : IsCompactOperator ((star U - 1 : E →L[ℂ] E) : E → E) := by
    have h : (star U - 1 : E →L[ℂ] E) = -(star U * (U - 1)) := by
      rw [mul_sub, Unitary.star_mul_self_of_mem hU, mul_one]; abel
    rw [h]
    simpa [ContinuousLinearMap.coe_comp] using (hC.clm_comp (star U)).neg
  have h1 : ((2 : ℂ) • 1 - U - star U : E →L[ℂ] E) = -(U - 1) - (star U - 1) := by
    rw [two_smul]; abel
  have h2 : (U - star U : E →L[ℂ] E) = (U - 1) - (star U - 1) := by abel
  unfold arcForm
  rw [h1, h2]
  simp only [ContinuousLinearMap.coe_add', ContinuousLinearMap.coe_smul',
    ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_neg']
  exact ((hC.neg.sub hS).smul _).add ((hC.sub hS).smul _)

lemma commute_arcForm {U : E →L[ℂ] E} (hU : U ∈ unitary (E →L[ℂ] E)) (c : ℝ) :
    U * arcForm U c = arcForm U c * U := by
  have h1 : U * star U = star U * U := by
    rw [Unitary.mul_star_self_of_mem hU, Unitary.star_mul_self_of_mem hU]
  unfold arcForm
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_one, one_mul,
    h1]

/-- The trigonometric sign condition: for `θ, α ∈ (0, 2π)`,
`cot(α/2)(2 - 2 cos θ) - 2 sin θ > 0` forces `α < θ`. -/
lemma lt_of_cot_form_pos {α θ : ℝ} (hα : α ∈ Ioo 0 (2 * Real.pi)) (hθ : θ ∈ Ioo 0 (2 * Real.pi))
    (h : 0 < Real.cot (α / 2) * (2 - 2 * Real.cos θ) - 2 * Real.sin θ) : α < θ := by
  have hsa : 0 < Real.sin (α / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hα.1]) (by linarith [hα.2])
  have hst : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hc : 2 - 2 * Real.cos θ = 4 * Real.sin (θ / 2) ^ 2 := by
    have h2 := Real.sin_sq_add_cos_sq (θ / 2)
    have h3 : Real.cos θ = Real.cos (2 * (θ / 2)) := by ring_nf
    rw [h3, Real.cos_two_mul]; nlinarith
  have hs : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  rw [hc, hs, Real.cot_eq_cos_div_sin] at h
  have hp : 0 < 4 * Real.sin (θ / 2) / Real.sin (α / 2) := by positivity
  have key : 0 < Real.sin (θ / 2 - α / 2) := by
    rw [Real.sin_sub]
    have e : Real.cos (α / 2) / Real.sin (α / 2) * (4 * Real.sin (θ / 2) ^ 2) -
        2 * (2 * Real.sin (θ / 2) * Real.cos (θ / 2)) = 4 * Real.sin (θ / 2) / Real.sin (α / 2) *
      (Real.sin (θ / 2) * Real.cos (α / 2) - Real.cos (θ / 2) * Real.sin (α / 2)) := by
      field_simp; ring
    rw [e] at h
    exact (mul_pos_iff_of_pos_left hp).1 h
  by_contra hle
  push_neg at hle
  have : Real.sin (θ / 2 - α / 2) ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith [hα.2, hθ.1])
  linarith

/-- **Eigenphases on an arc.** Let `U` be
unitary with `U - 1` compact and `0 < α < 2π`. If on every nonzero vector of an
`m`-dimensional subspace `Y`, `2 Im ⟪y, U y⟫ < cot(α/2) ‖y - U y‖²`, then `U` has `m`
orthonormal eigenvectors with eigenvalues `e^{iθ}`, `θ ∈ (α, 2π)`. -/
theorem exists_arc_eigenvectors {U : E →L[ℂ] E} (hU : U ∈ unitary (E →L[ℂ] E))
    (hC : IsCompactOperator ((U - 1 : E →L[ℂ] E) : E → E)) {α : ℝ}
    (hα : α ∈ Ioo 0 (2 * Real.pi)) {m : ℕ} (Y : Submodule ℂ E) [FiniteDimensional ℂ Y]
    (hYm : Module.finrank ℂ Y = m)
    (hq : ∀ y ∈ Y, y ≠ 0 → 2 * (⟪y, U y⟫_ℂ).im < Real.cot (α / 2) * ‖y - U y‖ ^ 2) :
    ∃ (u : Fin m → E) (θ : Fin m → ℝ), Orthonormal ℂ u ∧
      (∀ i, θ i ∈ Ioo α (2 * Real.pi)) ∧ ∀ i, U (u i) = exp (θ i * I) • u i := by
  classical
  set c := Real.cot (α / 2) with hc
  set G := arcForm U c with hG
  have hGc := isCompactOperator_arcForm hU hC c
  have hGs := isSelfAdjoint_arcForm U c
  have hcomm := commute_arcForm hU c
  have hGre := re_inner_arcForm hU c
  have heig_form : ∀ (x : E) (μ : ℂ), U x = μ • x →
      RCLike.re ⟪x, G x⟫_ℂ = (c * ‖1 - μ‖ ^ 2 - 2 * μ.im) * ‖x‖ ^ 2 := by
    intro x μ hx
    rw [hGre, hx]
    have h1 : x - μ • x = (1 - μ) • x := by rw [sub_smul, one_smul]
    have hyy : ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    rw [h1, norm_smul, inner_smul_right, hyy, Complex.im_mul_ofReal]
    ring
  suffices H : ∀ p ≤ m, ∃ (u : Fin p → E) (θ : Fin p → ℝ), Orthonormal ℂ u ∧
      (∀ i, θ i ∈ Ioo α (2 * Real.pi)) ∧ ∀ i, U (u i) = exp (θ i * I) • u i from H m le_rfl
  intro p
  induction p with
  | zero =>
    intro _
    refine ⟨Fin.elim0, Fin.elim0, ?_, fun i => i.elim0, fun i => i.elim0⟩
    rw [orthonormal_iff_ite]
    intro i; exact i.elim0
  | succ p ih =>
    intro hp
    obtain ⟨u, θ, hon, hθ, heig⟩ := ih (Nat.le_of_succ_le hp)
    set Q := Submodule.span ℂ (Set.range u) with hQ
    haveI : FiniteDimensional ℂ Q := FiniteDimensional.span_of_finite ℂ (Set.finite_range u)
    have hnorm1 : ∀ i, ‖exp (θ i * I)‖ = 1 := fun i => by
      rw [Complex.norm_exp_ofReal_mul_I]
    have hQU : ∀ q ∈ Q, U q ∈ Q := by
      intro q hq
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hq
      rw [map_sum]
      refine Q.sum_mem fun i _ => ?_
      rw [map_smul, heig, smul_smul]
      exact Q.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
    have hQS : ∀ q ∈ Q, star U q ∈ Q := by
      intro q hq
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hq
      rw [map_sum]
      refine Q.sum_mem fun i _ => ?_
      rw [map_smul, star_apply_of_eigen hU (hnorm1 i) (heig i), smul_smul]
      exact Q.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
    have hQoU : ∀ z ∈ Qᗮ, U z ∈ Qᗮ := by
      intro z hz
      rw [Submodule.mem_orthogonal] at hz ⊢
      intro q hq
      rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint]
      exact hz _ (hQS q hq)
    set P : E →L[ℂ] E := Qᗮ.starProjection with hP
    have hPval : ∀ z, P z = z - Q.starProjection z := fun z =>
      Submodule.starProjection_orthogonal_val z
    have hPmem : ∀ z, P z ∈ Qᗮ := fun z => by
      rw [hPval]; exact Submodule.sub_starProjection_mem_orthogonal z
    have hPfix : ∀ z ∈ Qᗮ, P z = z := fun z hz => Submodule.starProjection_eq_self_iff.2 hz
    have hPsa : IsSelfAdjoint P := isSelfAdjoint_starProjection _
    have hprojU : ∀ z, Q.starProjection (U z) = U (Q.starProjection z) := by
      intro z
      have hsplit : U z = U (Q.starProjection z) + U (z - Q.starProjection z) := by
        rw [← map_add, add_sub_cancel]
      rw [hsplit, map_add, Submodule.starProjection_eq_self_iff.2
        (hQU _ (Submodule.starProjection_apply_mem Q z)),
        (Submodule.starProjection_apply_eq_zero_iff Q).2
          (hQoU _ (Submodule.sub_starProjection_mem_orthogonal z)), add_zero]
    have hPU : U * P = P * U := by
      ext z
      simp only [ContinuousLinearMap.mul_apply, hPval, map_sub, hprojU]
    set G' := P * G * P with hG'
    have hG'c : IsCompactOperator (G' : E → E) := by
      rw [hG', hG]
      simpa [ContinuousLinearMap.coe_comp, Function.comp_def] using (hGc.comp_clm P).clm_comp P
    have hG's : IsSelfAdjoint G' := by
      rw [hG', IsSelfAdjoint, star_mul, star_mul, hPsa.star_eq, hGs.star_eq, mul_assoc]
    have hG'comm : U * G' = G' * U := by
      rw [hG', ← mul_assoc, ← mul_assoc, hPU, mul_assoc P U G, hcomm, ← mul_assoc,
        mul_assoc (P * G) U P, hPU, ← mul_assoc]
    have hG'inner : ∀ z ∈ Qᗮ, ⟪z, G' z⟫_ℂ = ⟪z, G z⟫_ℂ := by
      intro z hz
      rw [hG', ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hPfix z hz,
        ← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
        hPsa.star_eq, hPfix z hz]
    -- a nonzero vector of `Y ∩ Qᗮ`
    have hQrank : Module.finrank ℂ Q ≤ p := by
      rw [hQ]
      have hli := hon.linearIndependent
      simpa using (finrank_span_eq_card hli).le
    obtain ⟨y₀, hy₀Y, hy₀Q, hy₀0⟩ : ∃ y ∈ Y, y ∈ Qᗮ ∧ y ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      let T : Y →ₗ[ℂ] Q := (Q.orthogonalProjection : E →ₗ[ℂ] Q).comp Y.subtype
      have hT : Function.Injective T := by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro y hy
        have h1 : (y : E) ∈ Qᗮ := Submodule.orthogonalProjection_eq_zero_iff.1 hy
        exact Subtype.ext (hcon y y.2 h1)
      have := LinearMap.finrank_le_finrank_of_injective hT
      omega
    have hpos0 : 0 < RCLike.re ⟪y₀, G' y₀⟫_ℂ := by
      rw [hG'inner y₀ hy₀Q, hGre]
      linarith [hq y₀ hy₀Y hy₀0]
    obtain ⟨M, hM, x, hx0, hGx, μ, hUx⟩ := exists_joint_eigenvector hG'c hG's hG'comm hpos0
    have hxQ : x ∈ Qᗮ := by
      have : x = (M : ℂ)⁻¹ • G' x := by
        rw [hGx, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hM.ne'), one_smul]
      rw [this, hG', ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
      exact Submodule.smul_mem _ _ (hPmem (G (P x)))
    have hμ : ‖μ‖ = 1 := by
      have h1 := norm_apply_eq_of_mem_unitary hU x
      rw [hUx, norm_smul] at h1
      have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
      have h2 : (‖μ‖ - 1) * ‖x‖ = 0 := by linarith
      rcases mul_eq_zero.1 h2 with h | h
      · linarith
      · linarith
    have hform : 0 < c * ‖1 - μ‖ ^ 2 - 2 * μ.im := by
      have h1 : RCLike.re ⟪x, G x⟫_ℂ = M * ‖x‖ ^ 2 := by
        rw [← hG'inner x hxQ, hGx, inner_smul_right, @norm_sq_eq_re_inner ℂ]
        simp
      rw [heig_form x μ hUx] at h1
      have hxn : ‖x‖ ^ 2 ≠ 0 := by positivity
      have := mul_right_cancel₀ hxn h1
      rw [this]; exact hM
    -- the eigenphase
    set θ₀ := if Complex.arg μ ≤ 0 then Complex.arg μ + 2 * Real.pi else Complex.arg μ with hθ₀
    have hμexp : μ = exp (θ₀ * I) := by
      have h1 : μ = exp (Complex.arg μ * I) := by
        conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I μ, hμ]
        simp
      have h2 : exp (((Complex.arg μ + 2 * Real.pi : ℝ) : ℂ) * I) = exp (Complex.arg μ * I) := by
        push_cast
        rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
      rw [hθ₀]
      split_ifs
      · rw [h2]; exact h1
      · exact h1
    have hθ₀mem : θ₀ ∈ Ioc 0 (2 * Real.pi) := by
      have h1 := Complex.neg_pi_lt_arg μ
      have h2 := Complex.arg_le_pi μ
      rw [hθ₀]
      split_ifs with h
      · constructor <;> linarith
      · push_neg at h
        constructor <;> linarith [Real.pi_pos]
    have hθ₀ne : θ₀ ≠ 2 * Real.pi := by
      intro h
      rw [h] at hμexp
      have : μ = 1 := by rw [hμexp]; push_cast; exact Complex.exp_two_pi_mul_I
      rw [this] at hform
      simp at hform
    have hθ₀Ioo : θ₀ ∈ Ioo 0 (2 * Real.pi) := ⟨hθ₀mem.1, lt_of_le_of_ne hθ₀mem.2 hθ₀ne⟩
    have hαθ : α < θ₀ := by
      refine lt_of_cot_form_pos hα hθ₀Ioo ?_
      have h1 : ‖1 - μ‖ ^ 2 = 2 - 2 * Real.cos θ₀ := by
        rw [hμexp, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re, Complex.sub_im,
          Complex.one_im, Complex.exp_ofReal_mul_I_im]
        nlinarith [Real.sin_sq_add_cos_sq θ₀]
      have h2 : μ.im = Real.sin θ₀ := by rw [hμexp, Complex.exp_ofReal_mul_I_im]
      rw [← h1, ← h2]
      exact hform
    -- extend the family
    have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
    set x' : E := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hx'
    have hx'n : ‖x'‖ = 1 := norm_real_inv_norm_smul hx0
    have hx'Q : x' ∈ Qᗮ := Submodule.smul_mem _ _ hxQ
    have hUx' : U x' = exp (θ₀ * I) • x' := by
      rw [hx', map_smul, hUx, hμexp, smul_comm]
    have horth : ∀ i, ⟪u i, x'⟫_ℂ = 0 := fun i =>
      (Submodule.mem_orthogonal Q x').1 hx'Q (u i) (Submodule.subset_span ⟨i, rfl⟩)
    refine ⟨Fin.snoc u x', Fin.snoc θ θ₀, ?_, ?_, ?_⟩
    · rw [orthonormal_iff_ite] at hon ⊢
      intro i j
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => simp [Fin.snoc_last, inner_self_eq_norm_sq_to_K, hx'n]
        | cast j =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc]
          rw [← inner_conj_symm, horth j, map_zero]
          simp [(Fin.castSucc_lt_last j).ne']
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc, horth i]
          simp [(Fin.castSucc_lt_last i).ne]
        | cast j =>
          simp only [Fin.snoc_castSucc, hon i j, Fin.castSucc_inj]
    · intro i
      induction i using Fin.lastCases with
      | last => simpa [Fin.snoc_last] using ⟨hαθ, hθ₀Ioo.2⟩
      | cast i => simpa [Fin.snoc_castSucc] using hθ i
    · intro i
      induction i using Fin.lastCases with
      | last => simpa [Fin.snoc_last] using hUx'
      | cast i => simpa [Fin.snoc_castSucc] using heig i

end

section

/-! ## Herglotz wave functions -/

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory Set Real Complex

instance fact_two_pi_pos : Fact (0 < 2 * π) := ⟨by positivity⟩

/-- Continuous functions on the direction circle `ℝ / 2πℤ`. -/
abbrev CircFun := C(AddCircle (2 * π), ℂ)

/-- Evaluation of the `j`-th coordinate of `ℓ²(ℤ)`. -/
def lpEvalZ (j : ℤ) : lp (fun _ : ℤ => ℂ) 2 →L[ℂ] ℂ :=
    LinearMap.mkContinuous
    { toFun := fun x => x j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1
    (fun x => by
      change ‖x j‖ ≤ 1 * ‖x‖
      simpa using lp.norm_apply_le_norm (by norm_num) x j)

lemma memℓp_shiftZ (x : lp (fun _ : ℤ => ℂ) 2) :
    Memℓp (fun n : ℕ => x ((n : ℤ) + 1)) 2 := by
  have hx := lp.memℓp x
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)] at hx ⊢
  exact hx.comp_injective (fun a b h => by simpa using h)

/-- The map `ℓ²(ℤ) → ℓ²(ℕ₀)`, `x ↦ (x_{n+1})_{n ≥ 0}`. -/
def shiftZ : lp (fun _ : ℤ => ℂ) 2 →L[ℂ] L2N :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun n : ℕ => x ((n : ℤ) + 1), memℓp_shiftZ x⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1
    (fun x => by
      rw [one_mul]
      have h1 := norm_sq_eq_tsum (⟨fun n : ℕ => x ((n : ℤ) + 1), memℓp_shiftZ x⟩ : L2N)
      have h2 := lp.norm_rpow_eq_tsum (p := 2) (by norm_num : 0 < (2 : ENNReal).toReal) x
      have hs : Summable fun n : ℤ => ‖x n‖ ^ (2 : ℝ) := by
        have := (lp.memℓp x)
        rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)] at this
        simpa using this
      have hle : ‖(⟨fun n : ℕ => x ((n : ℤ) + 1), memℓp_shiftZ x⟩ : L2N)‖ ^ (2 : ℝ) ≤
          ‖x‖ ^ (2 : ℝ) := by
        rw [h1]
        simp only [ENNReal.toReal_ofNat] at h2
        rw [h2]
        exact (hs.comp_injective (fun a b h => by simpa using h)).tsum_le_tsum_of_inj _
          (fun a b h => by simpa using h) (fun _ _ => by positivity) (fun _ => le_rfl) hs
      exact (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 hle)

/-- The `j`-th Fourier coefficient on the direction circle, as a continuous linear functional. -/
def circCoeff (j : ℤ) : CircFun →L[ℂ] ℂ :=
  lpEvalZ j ∘L (fourierBasis (T := 2 * π)).repr.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    ContinuousMap.toLp (E := ℂ) 2 (@AddCircle.haarAddCircle (2 * π) _) ℂ

/-- The positive Fourier coefficients `g ↦ (ĝ(n+1))_{n ≥ 0}`. -/
def circPos : CircFun →L[ℂ] L2N :=
  shiftZ ∘L (fourierBasis (T := 2 * π)).repr.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    ContinuousMap.toLp (E := ℂ) 2 (@AddCircle.haarAddCircle (2 * π) _) ℂ

lemma circCoeff_apply (j : ℤ) (g : CircFun) : circCoeff j g = fourierCoeff g j := by
  simp only [circCoeff, ContinuousLinearMap.coe_comp', Function.comp_apply, lpEvalZ,
    LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  change (fourierBasis (T := 2 * π)).repr
      (ContinuousMap.toLp (E := ℂ) 2 (@AddCircle.haarAddCircle (2 * π) _) ℂ g) j = _
  rw [fourierBasis_repr, fourierCoeff_toLp]

lemma circPos_apply (g : CircFun) (n : ℕ) : circPos g n = circCoeff ((n : ℤ) + 1) g := by
  rw [circCoeff_apply]
  simp only [circPos, ContinuousLinearMap.coe_comp', Function.comp_apply, shiftZ,
    LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  change (fourierBasis (T := 2 * π)).repr
      (ContinuousMap.toLp (E := ℂ) 2 (@AddCircle.haarAddCircle (2 * π) _) ℂ g)
      ((n : ℤ) + 1) = _
  rw [fourierBasis_repr, fourierCoeff_toLp]

lemma circCoeff_mul_fourier (j m : ℤ) (g : CircFun) :
    circCoeff j (g * fourier m) = circCoeff (j - m) g := by
  rw [circCoeff_apply, circCoeff_apply, fourierCoeff, fourierCoeff]
  congr 1
  funext t
  simp only [ContinuousMap.mul_apply, smul_eq_mul]
  rw [show -(j - m) = -j + m by ring, fourier_add]
  ring

lemma circPos_mul_fourier_neg_one (g : CircFun) :
    circPos (g * fourier (-1)) = shiftAdj (circPos g) := by
  ext n
  rw [circPos_apply, shiftAdj_apply, circPos_apply, circCoeff_mul_fourier]
  congr 1

/-- The vector `e₀ = (1, 0, 0, …)` acts as the `0`-th coordinate. -/
lemma e0_apply (n : ℕ) : e0 n = if n = 0 then 1 else 0 := by
  simp only [e0, lp.single_apply, Pi.single_apply]

lemma circPos_mul_fourier_one (g : CircFun) :
    circPos (g * fourier 1) = shift (circPos g) + circCoeff 0 g • e0 := by
  ext n
  rw [circPos_apply, circCoeff_mul_fourier]
  cases n with
  | zero =>
      change circCoeff 0 g = 0 + circCoeff 0 g * 1
      simp
  | succ n =>
    simp only [lp.coeFn_add, Pi.add_apply, 
      show ∀ (y : L2N) (n : ℕ), shift y (n + 1) = y n from fun _ _ => rfl, lp.coeFn_smul, Pi.smul_apply,
      e0_apply, circPos_apply]
    simp

/-- The phase `Ψ z = -(ik/2)(z e^{-iφ} + z̄ e^{iφ}) = -ik Re(z e^{-iφ})`, real-linear in `z`. -/
def herglotzPhase (k : ℝ) : ℂ →L[ℝ] CircFun :=
  (-(I * k / 2)) • ((ContinuousLinearMap.id ℝ ℂ).smulRight (fourier (-1) : CircFun) +
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).smulRight (fourier 1 : CircFun))

lemma herglotzPhase_apply (k : ℝ) (w : ℂ) :
    herglotzPhase k w = (-(I * k / 2)) • (w • (fourier (-1) : CircFun) +
      conj w • (fourier 1 : CircFun)) := by
  simp [herglotzPhase]

/-- The direction-space function `g_z(φ) = a(φ) e^{-ik Re(z e^{-iφ})}`. -/
def herglotzDir (k : ℝ) (a : CircFun) (z : ℂ) : CircFun :=
  a * NormedSpace.exp (herglotzPhase k z)

/-- **Herglotz wave function** `u_a(z) = (1/2π) ∫₀^{2π} a(φ) e^{-ik Re(z e^{-iφ})} dφ`. -/
def herglotzWave (k : ℝ) (a : CircFun) (z : ℂ) : ℂ := circCoeff 0 (herglotzDir k a z)

/-- **Herglotz vector** `f(z) = (f_n(z))_{n ≥ 0} ∈ ℓ²(ℕ₀)`,
`f_n(z) = (1/2π) ∫₀^{2π} a(φ) e^{-ik Re(z e^{-iφ})} e^{-i(n+1)φ} dφ`. -/
def herglotzVec (k : ℝ) (a : CircFun) (z : ℂ) : L2N := circPos (herglotzDir k a z)

lemma hasFDerivAt_herglotzDir (k : ℝ) (a : CircFun) (z : ℂ) :
    HasFDerivAt (herglotzDir k a)
      ((ContinuousLinearMap.mul ℝ CircFun (herglotzDir k a z)) ∘L herglotzPhase k) z := by
  have h1 := hasFDerivAt_exp (𝕂 := ℝ) (𝔸 := CircFun) (x := herglotzPhase k z)
  have h2 := h1.comp z (herglotzPhase k).hasFDerivAt
  have h3 := (ContinuousLinearMap.mul ℝ CircFun a).hasFDerivAt.comp z h2
  convert h3 using 1 <;>
    first
    | (apply ContinuousLinearMap.ext; intro w; ext φ;
       simp [herglotzDir, mul_apply_eq_comp, smul_apply, smul_eq_mul, mul_assoc])
    | (funext w; ext φ;
       simp [herglotzDir, mul_apply_eq_comp, smul_apply, smul_eq_mul, mul_assoc])

lemma herglotzDir_mul_phase (k : ℝ) (a : CircFun) (z w : ℂ) :
    herglotzDir k a z * herglotzPhase k w = (-(I * k / 2)) •
      (w • (herglotzDir k a z * fourier (-1)) + conj w • (herglotzDir k a z * fourier 1)) := by
  rw [herglotzPhase_apply, mul_smul_comm, mul_add, mul_smul_comm, mul_smul_comm]

/-- Real derivative of the Herglotz wave function:
`D u_a(z) w = -(ik/2)(w f₀(z) + w̄ c₋₁(z))`. -/
lemma hasFDerivAt_herglotzWave (k : ℝ) (a : CircFun) (z : ℂ) :
    HasFDerivAt (herglotzWave k a)
      (((circCoeff 0).restrictScalars ℝ) ∘L
        (ContinuousLinearMap.mul ℝ CircFun (herglotzDir k a z)) ∘L herglotzPhase k) z :=
  ((circCoeff 0).restrictScalars ℝ).hasFDerivAt.comp z (hasFDerivAt_herglotzDir k a z)

lemma fderiv_herglotzWave_apply (k : ℝ) (a : CircFun) (z w : ℂ) :
    fderiv ℝ (herglotzWave k a) z w = (-(I * k / 2)) *
      (w * herglotzVec k a z 0 + conj w * circCoeff (-1) (herglotzDir k a z)) := by
  rw [(hasFDerivAt_herglotzWave k a z).fderiv]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.coe_restrictScalars']
  rw [herglotzDir_mul_phase, map_smul, map_add, map_smul, map_smul, circCoeff_mul_fourier,
    circCoeff_mul_fourier, herglotzVec, circPos_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  norm_num

/-- `i D u(z)(w) - D u(z)(-i w) = k w f₀(z)`: the combination of the tangential derivative and
the conormal derivative. -/
lemma herglotz_normal_identity (k : ℝ) (a : CircFun) (z w : ℂ) :
    I * fderiv ℝ (herglotzWave k a) z w - fderiv ℝ (herglotzWave k a) z (-I * w) =
      k * w * herglotzVec k a z 0 := by
  rw [fderiv_herglotzWave_apply, fderiv_herglotzWave_apply]
  simp only [map_mul, map_neg, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Derivative of the Herglotz vector along a curve:
`d/dθ f(γ θ) = -(ik/2)(γ' S* f + conj γ' (S f + u e₀))`. -/
lemma hasDerivAt_herglotzVec_comp (k : ℝ) (a : CircFun) {γ : ℝ → ℂ} {γ' : ℂ} {θ : ℝ}
    (hγ : HasDerivAt γ γ' θ) :
    HasDerivAt (fun t => herglotzVec k a (γ t))
      ((-(I * k / 2)) • (γ' • shiftAdj (herglotzVec k a (γ θ)) +
        conj γ' • (shift (herglotzVec k a (γ θ)) + herglotzWave k a (γ θ) • e0))) θ := by
  have h1 : HasFDerivAt (herglotzVec k a)
      ((circPos.restrictScalars ℝ) ∘L
        (ContinuousLinearMap.mul ℝ CircFun (herglotzDir k a (γ θ))) ∘L herglotzPhase k) (γ θ) :=
    (circPos.restrictScalars ℝ).hasFDerivAt.comp _ (hasFDerivAt_herglotzDir k a (γ θ))
  have h2 := h1.comp_hasDerivAt θ hγ
  convert h2 using 1
  · rfl
  · simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.mul_apply',
      ContinuousLinearMap.coe_restrictScalars']
    rw [herglotzDir_mul_phase, map_smul, map_add, map_smul, map_smul, circPos_mul_fourier_neg_one,
      circPos_mul_fourier_one]
    rfl

lemma herglotzVec_sum {m : ℕ} (k : ℝ) (a : Fin m → CircFun) (c : Fin m → ℂ) (z : ℂ) :
    herglotzVec k (∑ i, c i • a i) z = ∑ i, c i • herglotzVec k (a i) z := by
  simp only [herglotzVec, herglotzDir, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul]

end

section

/-! ## Herglotz traces and the boundary holonomy -/

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory Set Real Complex

/-- **Duhamel estimate.** For a `C¹` curve `G` in a Hilbert space on `[0, b]` with
`Λ = ∫₀ᵇ ‖G'‖`: `‖G b - G 0‖ ≤ Λ` and `|Im ⟪G 0, G b⟫ - Im ∫₀ᵇ ⟪G, G'⟫| ≤ Λ²`. -/
lemma duhamel_inner_estimate {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {G G' : ℝ → H} {b : ℝ} (hb : 0 ≤ b) (hG : ContinuousOn G (Icc 0 b))
    (hG' : ContinuousOn G' (Icc 0 b)) (hd : ∀ t ∈ Ioo 0 b, HasDerivAt G (G' t) t) :
    ‖G b - G 0‖ ≤ ∫ t in (0 : ℝ)..b, ‖G' t‖ ∧
      |(⟪G 0, G b⟫_ℂ).im - (∫ t in (0 : ℝ)..b, ⟪G t, G' t⟫_ℂ).im| ≤
        (∫ t in (0 : ℝ)..b, ‖G' t‖) ^ 2 := by
  have hint' : IntervalIntegrable G' volume 0 b := hG'.intervalIntegrable_of_Icc hb
  have hnint : IntervalIntegrable (fun t => ‖G' t‖) volume 0 b :=
    hG'.norm.intervalIntegrable_of_Icc hb
  set Λ := ∫ t in (0 : ℝ)..b, ‖G' t‖ with hΛ
  have hftc : ∀ s ∈ Icc 0 b, G s - G 0 = ∫ t in (0 : ℝ)..s, G' t := by
    intro s hs
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1
      (hG.mono (Icc_subset_Icc_right hs.2)) (fun t ht => hd t ⟨ht.1, ht.2.trans_le hs.2⟩)
      ((hG'.mono (Icc_subset_Icc_right hs.2)).intervalIntegrable_of_Icc hs.1)]
  have hbound : ∀ s ∈ Icc 0 b, ‖G s - G 0‖ ≤ Λ := by
    intro s hs
    rw [hftc s hs]
    calc ‖∫ t in (0 : ℝ)..s, G' t‖ ≤ ∫ t in (0 : ℝ)..s, ‖G' t‖ :=
          intervalIntegral.norm_integral_le_integral_norm hs.1
      _ ≤ Λ := intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2
          (Filter.Eventually.of_forall fun t => norm_nonneg _) hnint
  refine ⟨hbound b ⟨hb, le_rfl⟩, ?_⟩
  have hΛ0 : 0 ≤ Λ := intervalIntegral.integral_nonneg hb fun t _ => norm_nonneg _
  have h1 : ⟪G 0, G b⟫_ℂ = ⟪G 0, G 0⟫_ℂ + ∫ t in (0 : ℝ)..b, ⟪G 0, G' t⟫_ℂ := by
    have := (innerSL ℂ (G 0)).intervalIntegral_comp_comm hint'
    simp only [innerSL_apply_apply] at this
    rw [this, ← inner_add_right, ← hftc b ⟨hb, le_rfl⟩, add_sub_cancel]
  have h2 : (⟪G 0, G 0⟫_ℂ).im = 0 := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have hc1 : ContinuousOn (fun t => ⟪G t, G' t⟫_ℂ) (Icc 0 b) := hG.inner hG'
  have hc2 : ContinuousOn (fun t => ⟪G 0, G' t⟫_ℂ) (Icc 0 b) := continuousOn_const.inner hG'
  have h3 : (∫ t in (0 : ℝ)..b, ⟪G t, G' t⟫_ℂ) - ∫ t in (0 : ℝ)..b, ⟪G 0, G' t⟫_ℂ =
      ∫ t in (0 : ℝ)..b, ⟪G t - G 0, G' t⟫_ℂ := by
    rw [← intervalIntegral.integral_sub (hc1.intervalIntegrable_of_Icc hb)
      (hc2.intervalIntegrable_of_Icc hb)]
    congr 1
    funext t
    rw [inner_sub_left]
  have h4 : ‖∫ t in (0 : ℝ)..b, ⟪G t - G 0, G' t⟫_ℂ‖ ≤ Λ * Λ := by
    calc ‖∫ t in (0 : ℝ)..b, ⟪G t - G 0, G' t⟫_ℂ‖ ≤ ∫ t in (0 : ℝ)..b, Λ * ‖G' t‖ := by
          refine intervalIntegral.norm_integral_le_of_norm_le hb
            (Filter.Eventually.of_forall fun t ht => ?_) (hnint.const_mul Λ)
          calc ‖⟪G t - G 0, G' t⟫_ℂ‖ ≤ ‖G t - G 0‖ * ‖G' t‖ := norm_inner_le_norm _ _
            _ ≤ Λ * ‖G' t‖ := by
                gcongr
                exact hbound t ⟨ht.1.le, ht.2⟩
      _ = Λ * Λ := by rw [intervalIntegral.integral_const_mul]
  have h5 : (⟪G 0, G b⟫_ℂ).im - (∫ t in (0 : ℝ)..b, ⟪G t, G' t⟫_ℂ).im =
      -(∫ t in (0 : ℝ)..b, ⟪G t - G 0, G' t⟫_ℂ).im := by
    rw [h1, Complex.add_im, h2, ← h3, Complex.sub_im]
    ring
  rw [h5, abs_neg, sq]
  exact (Complex.abs_im_le_norm _).trans h4

variable (F : ℂ → ℂ) (k : ℝ)

/-- The derivative of the boundary curve `γ_r(θ) = F(r e^{iθ})`. -/
lemma hasDerivAt_circleCurve {U : Set ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) {r θ : ℝ}
    (hr : (r : ℂ) * exp (θ * I) ∈ U) :
    HasDerivAt (fun t : ℝ => F (r * exp (t * I))) (dAng F r θ) θ := by
  have h1 : HasDerivAt (fun t : ℝ => (r : ℂ) * exp (t * I)) (r * (exp (θ * I) * I)) θ := by
    have := ((hasDerivAt_id (θ : ℂ)).mul_const I).cexp.comp_ofReal (z := θ)
    simpa using this.const_mul (r : ℂ)
  have h2 := ((hF.differentiableAt (hU.mem_nhds hr)).hasDerivAt).comp θ h1
  convert h2 using 1
  · funext t
    simp only [Function.comp_apply]
  · unfold dAng
    ring

/-- `C_θ = -(ik/2)(γ' S* + conj γ' S)`. -/
lemma coefAng_eq_shift (r θ : ℝ) :
    coefAng F k r θ = (-(I * k / 2) * dAng F r θ) • shiftAdj +
      (-(I * k / 2) * conj (dAng F r θ)) • shift := by
  obtain ⟨p, q, hpq⟩ : ∃ p q : ℝ, dAng F r θ = p + q * I := ⟨_, _, (Complex.re_add_im _).symm⟩
  rw [coefAng, opX, opY, hpq]
  have h1 : ((p : ℂ) + q * I).re = p := by simp
  have h2 : ((p : ℂ) + q * I).im = q := by simp
  have h3 : conj ((p : ℂ) + q * I) = p - q * I := by
    apply Complex.ext <;> simp
  rw [h1, h2, h3]
  ext x n
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, lp.coeFn_add, lp.coeFn_smul, lp.coeFn_sub, Pi.add_apply,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Herglotz–holonomy estimate.** -/
theorem herglotz_holonomy_estimate {U : Set ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    {r : ℝ} (hr : ∀ θ : ℝ, (r : ℂ) * exp (θ * I) ∈ U) (a : CircFun) :
    let γ : ℝ → ℂ := fun θ => F (r * exp (θ * I))
    let v := herglotzVec k a (γ 0)
    let Λ := ∫ θ in (0 : ℝ)..(2 * π), |k| / 2 * ‖dAng F r θ‖ * ‖herglotzWave k a (γ θ)‖
    ‖v - holV F k r v‖ ≤ Λ ∧
      -(∫ θ in (0 : ℝ)..(2 * π), -(I * k / 2) * conj (dAng F r θ) *
          herglotzWave k a (γ θ) * conj (herglotzVec k a (γ θ) 0)).im - Λ ^ 2 ≤
        (⟪v, holV F k r v⟫_ℂ).im := by
  intro γ v Λ
  have hγd : ∀ θ, HasDerivAt γ (dAng F r θ) θ := fun θ => hasDerivAt_circleCurve F hU hF (hr θ)
  have hγc : Continuous γ := continuous_iff_continuousAt.2 fun θ => (hγd θ).continuousAt
  have hdc : Continuous (dAng F r) := by
    have hdF : ContinuousOn (deriv F) U := (hF.deriv hU).continuousOn
    have hc : Continuous fun θ : ℝ => (r : ℂ) * exp (θ * I) := by fun_prop
    unfold dAng
    exact (continuous_const.mul (by fun_prop)).mul (hdF.comp_continuous hc hr)
  set W := holW F k r with hWdef
  obtain ⟨hW0, hWd⟩ := holW_spec k hU hF hr
  have hWu : ∀ θ ∈ Icc 0 (2 * π), W θ ∈ unitary (L2N →L[ℂ] L2N) := fun θ hθ =>
    holW_mem_unitary k hU hF hr hθ
  have hWc : ContinuousOn W (Icc 0 (2 * π)) := fun θ hθ => (hWd θ hθ).continuousWithinAt
  set f : ℝ → L2N := fun θ => herglotzVec k a (γ θ) with hfdef
  set h : ℝ → ℂ := fun θ => herglotzWave k a (γ θ) with hhdef
  set frc : ℝ → L2N := fun θ => (-(I * k / 2) * conj (dAng F r θ) * h θ) • e0 with hfrc
  have hfd : ∀ θ, HasDerivAt f (coefAng F k r θ (f θ) + frc θ) θ := by
    intro θ
    have := hasDerivAt_herglotzVec_comp k a (hγd θ)
    convert this using 1
    rw [coefAng_eq_shift]
    simp only [hfrc, hhdef, hfdef, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_add, smul_smul, mul_assoc, add_assoc]
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun θ => (hfd θ).continuousAt
  have hhc : Continuous h :=
    continuous_iff_continuousAt.2 fun θ =>
      ((hasFDerivAt_herglotzWave k a (γ θ)).continuousAt).comp (hγc.continuousAt)
  have hfrcc : Continuous frc := by
    simp only [hfrc]
    exact (((continuous_const.mul (Complex.continuous_conj.comp hdc)).mul hhc).smul
      continuous_const)
  letI : StarModule ℝ (L2N →L[ℂ] L2N) :=
    ⟨fun a T => by
      change star ((a : ℂ) • T) = (a : ℂ) • star T
      rw [star_smul]
      simp⟩
  set G : ℝ → L2N := fun θ => star (W θ) (f θ) with hGdef
  set G' : ℝ → L2N := fun θ => star (W θ) (frc θ) with hG'def
  have hstarc : ContinuousOn (fun θ => star (W θ)) (Icc 0 (2 * π)) :=
    by
      simpa only [starL'_apply] using
        (starL' ℝ (A := L2N →L[ℂ] L2N)).continuous.comp_continuousOn' hWc
  have hGc : ContinuousOn G (Icc 0 (2 * π)) := hstarc.clm_apply hfc.continuousOn
  have hG'c : ContinuousOn G' (Icc 0 (2 * π)) := hstarc.clm_apply hfrcc.continuousOn
  have hGd : ∀ θ ∈ Ioo 0 (2 * π), HasDerivAt G (G' θ) θ := by
    intro θ hθ
    have hWθ : HasDerivAt W (coefAng F k r θ * W θ) θ :=
      (hWd θ (Ioo_subset_Icc_self hθ)).hasDerivAt (Icc_mem_nhds hθ.1 hθ.2)
    have hS : HasDerivAt (fun t => star (W t)) (star (coefAng F k r θ * W θ)) θ :=
      (starL' ℝ (A := L2N →L[ℂ] L2N)).hasFDerivAt.comp_hasDerivAt θ hWθ
    have hS' : HasDerivAt (fun t => (star (W t)).restrictScalars ℝ)
        ((star (coefAng F k r θ * W θ)).restrictScalars ℝ) θ :=
      (ContinuousLinearMap.restrictScalarsL ℂ L2N L2N ℝ ℝ).hasFDerivAt.comp_hasDerivAt θ hS
    have := hS'.clm_apply (hfd θ)
    convert this using 1
    · simpa only [hGdef, ContinuousLinearMap.coe_restrictScalars']
    · rw [hG'def]
      change star (W θ) (frc θ) = _
      simp only [ContinuousLinearMap.coe_restrictScalars', star_mul, star_coefAng,
        mul_apply_eq_comp, map_add, map_neg, neg_one_smul, neg_apply]
      abel
  obtain ⟨hA, hB⟩ := duhamel_inner_estimate (b := 2 * π) (by positivity) hGc hG'c hGd
  -- identifications
  have hV : holV F k r = W (2 * π) := rfl
  have hVu : holV F k r ∈ unitary (L2N →L[ℂ] L2N) := hWu _ ⟨by positivity, le_rfl⟩
  have hG0 : G 0 = v := by
    simp only [hGdef, hfdef]
    rw [hWdef, hW0, star_one]
    rfl
  have hf2π : f (2 * π) = v := by
    simp only [hfdef, v, γ]
    congr 3
    push_cast
    rw [Complex.exp_two_pi_mul_I, zero_mul, Complex.exp_zero]
  have hG2π : G (2 * π) = star (holV F k r) v := by
    simp only [hGdef, hV]; rw [hf2π]
  have hstar_norm : ∀ θ ∈ Icc 0 (2 * π), ∀ x : L2N, ‖star (W θ) x‖ = ‖x‖ := fun θ hθ x =>
    norm_apply_eq_of_mem_unitary (Unitary.star_mem (hWu θ hθ)) x
  have he0 : ‖e0‖ = 1 := by simp [e0]
  have hnormG' : ∀ θ ∈ Icc 0 (2 * π), ‖G' θ‖ = |k| / 2 * ‖dAng F r θ‖ * ‖h θ‖ := by
    intro θ hθ
    rw [hG'def]
    simp only
    rw [hstar_norm θ hθ, hfrc]
    simp only [norm_smul, he0, mul_one, norm_mul, norm_neg, Complex.norm_conj, norm_div,
      Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
  have hΛ : ∫ θ in (0 : ℝ)..(2 * π), ‖G' θ‖ = Λ := by
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [uIcc_of_le (by positivity)] at hθ
    exact hnormG' θ hθ
  have hinner : ∀ θ ∈ Icc 0 (2 * π), ⟪G θ, G' θ⟫_ℂ =
      -(I * k / 2) * conj (dAng F r θ) * h θ * conj (f θ 0) := by
    intro θ hθ
    rw [hGdef, hG'def]
    simp only
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint, star_star,
      ← ContinuousLinearMap.mul_apply, Unitary.mul_star_self_of_mem (hWu θ hθ),
      ContinuousLinearMap.one_apply, hfrc]
    simp only
    rw [inner_smul_right, e0, lp.inner_single_right]
    simp
  have hI : ∫ θ in (0 : ℝ)..(2 * π), ⟪G θ, G' θ⟫_ℂ = ∫ θ in (0 : ℝ)..(2 * π),
      -(I * k / 2) * conj (dAng F r θ) * h θ * conj (f θ 0) := by
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [uIcc_of_le (by positivity)] at hθ
    exact hinner θ hθ
  rw [hΛ, hG0, hG2π] at hA
  rw [hΛ, hG0, hG2π, hI] at hB
  constructor
  · have : v - holV F k r v = holV F k r (star (holV F k r) v - v) := by
      rw [map_sub, ← ContinuousLinearMap.mul_apply, Unitary.mul_star_self_of_mem hVu,
        ContinuousLinearMap.one_apply]
    rw [this, norm_apply_eq_of_mem_unitary hVu]
    exact hA
  · have h1 : (⟪v, holV F k r v⟫_ℂ).im = -(⟪v, star (holV F k r) v⟫_ℂ).im := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
        ← inner_conj_symm, Complex.conj_im]
    rw [h1]
    have := (abs_le.1 hB).2
    simp only [hfdef] at this ⊢
    linarith

lemma intervalIntegral_conj (f : ℝ → ℂ) (a b : ℝ) :
    ∫ x in a..b, conj (f x) = conj (∫ x in a..b, f x) := by
  simp only [intervalIntegral]
  rw [integral_conj, integral_conj, map_sub]

/-- **Herglotz–holonomy bound.** In the setting of `herglotz_holonomy_estimate`, with
`h = u_a ∘ γ`, the conormal derivative `N(θ) = |γ'| ∂_ν u_a(γ θ) = D u_a(γ θ)(-i γ'(θ))` and
`∂_θ h = D u_a(γ θ)(γ'(θ))`:
`2 Im ⟪v, V v⟫ ≥ -Re ∫₀^{2π} conj h (N - i ∂_θ h) - 2Λ²` and `‖v - V v‖ ≤ Λ`. -/
theorem herglotz_holonomy_bound {U : Set ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    {r : ℝ} (hr : ∀ θ : ℝ, (r : ℂ) * exp (θ * I) ∈ U) (a : CircFun) :
    let γ : ℝ → ℂ := fun θ => F (r * exp (θ * I))
    let u := herglotzWave k a
    let v := herglotzVec k a (γ 0)
    let Λ := ∫ θ in (0 : ℝ)..(2 * π), |k| / 2 * ‖dAng F r θ‖ * ‖u (γ θ)‖
    ‖v - holV F k r v‖ ≤ Λ ∧
      -(∫ θ in (0 : ℝ)..(2 * π), conj (u (γ θ)) *
          (fderiv ℝ u (γ θ) (-I * dAng F r θ) - I * fderiv ℝ u (γ θ) (dAng F r θ))).re -
        2 * Λ ^ 2 ≤ 2 * (⟪v, holV F k r v⟫_ℂ).im := by
  intro γ u v Λ
  obtain ⟨h1, h2⟩ := herglotz_holonomy_estimate F k hU hF hr a
  refine ⟨h1, ?_⟩
  set Y : ℝ → ℂ := fun θ => conj (u (γ θ)) *
    (fderiv ℝ u (γ θ) (-I * dAng F r θ) - I * fderiv ℝ u (γ θ) (dAng F r θ)) with hY
  have hX : ∀ θ, -(I * k / 2) * conj (dAng F r θ) * herglotzWave k a (γ θ) *
      conj (herglotzVec k a (γ θ) 0) = I / 2 * conj (Y θ) := by
    intro θ
    have hn := herglotz_normal_identity k a (γ θ) (dAng F r θ)
    have hN : fderiv ℝ u (γ θ) (-I * dAng F r θ) - I * fderiv ℝ u (γ θ) (dAng F r θ) =
        -(k * dAng F r θ * herglotzVec k a (γ θ) 0) := by
      rw [← hn]; ring
    simp only [hY, hN, map_mul, map_neg, Complex.conj_conj, Complex.conj_ofReal]
    ring
  have hint : (∫ θ in (0 : ℝ)..(2 * π), -(I * k / 2) * conj (dAng F r θ) *
      herglotzWave k a (γ θ) * conj (herglotzVec k a (γ θ) 0)) =
        I / 2 * conj (∫ θ in (0 : ℝ)..(2 * π), Y θ) := by
    simp_rw [hX]
    rw [intervalIntegral.integral_const_mul, intervalIntegral_conj]
  have him : (I / 2 * conj (∫ θ in (0 : ℝ)..(2 * π), Y θ)).im =
      (∫ θ in (0 : ℝ)..(2 * π), Y θ).re / 2 := by
    simp [Complex.mul_im]
    ring
  rw [hint, him] at h2
  simp only [hY] at h2 ⊢
  linarith

end


end

end


