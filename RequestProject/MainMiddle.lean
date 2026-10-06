module

public import RequestProject.MainBase

@[expose] public section

noncomputable section

section

/-! ## Trace of the generator and the area identity -/

open scoped InnerProductSpace
open MeasureTheory Set Real Metric Complex Filter Topology

variable {G : ℂ → ℂ} (k : ℝ)

/-- **Area formula**: `|G(b𝔻)| = ∫_{b𝔻} |G'|²`. -/
theorem volume_image_ball_eq (hG : DifferentiableOn ℂ G (ball 0 1)) (hinj : InjOn G (ball 0 1))
    {b : ℝ} (hb : b ≤ 1) :
    volume (G '' ball 0 b) = ∫⁻ z in ball 0 b, ENNReal.ofReal (‖deriv G z‖ ^ 2) := by
  have hsub : ball (0 : ℂ) b ⊆ ball 0 1 := ball_subset_ball hb
  have hf' : ∀ z ∈ ball (0 : ℂ) b, HasFDerivWithinAt G
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv G z)).restrictScalars ℝ)
      (ball 0 b) z := fun z hz =>
    ((hG.differentiableAt (isOpen_ball.mem_nhds (hsub hz))).hasDerivAt.hasFDerivAt
      |>.restrictScalars ℝ).hasFDerivWithinAt
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image volume measurableSet_ball hf' (hinj.mono hsub)]
  refine setLIntegral_congr_fun measurableSet_ball fun z _ => ?_
  congr 1
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
    LinearMap.det_restrictScalars]
  simp [Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]

/-- Integration over a disk in polar coordinates. -/
lemma lintegral_ball_polar {b : ℝ} (g : ℂ → ENNReal) (hg : Measurable g) :
    ∫⁻ z in ball 0 b, g z =
      ∫⁻ r in Ioo 0 b, ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal r * g (r * exp (θ * I)) := by
  have hsymm : ∀ p : ℝ × ℝ, Complex.polarCoord.symm p = p.1 * exp (p.2 * I) := fun p => by
    rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
  have hmeas : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal p.1 • (ball (0 : ℂ) b).indicator g (Complex.polarCoord.symm p) := by
    have hc : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) * exp (p.2 * I) := by fun_prop
    have h2 : Measurable fun p : ℝ × ℝ => (ball (0 : ℂ) b).indicator g (Complex.polarCoord.symm p) := by
      simp only [hsymm]
      exact (hg.indicator measurableSet_ball).comp hc.measurable
    exact (ENNReal.measurable_ofReal.comp measurable_fst).smul h2
  rw [← lintegral_indicator measurableSet_ball, ← Complex.lintegral_comp_polarCoord_symm,
    polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod _ hmeas.aemeasurable]
  rw [show Ioo (0 : ℝ) b = Iio b ∩ Ioi 0 from Iio_inter_Ioi.symm,
    ← setLIntegral_indicator measurableSet_Iio]
  refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  by_cases hrb : r < b
  · rw [indicator_of_mem (show r ∈ Iio b from hrb)]
    refine lintegral_congr fun θ => ?_
    have hmem : (r : ℂ) * exp (θ * I) ∈ ball (0 : ℂ) b := by
      rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (show 0 < r from hr)]
      exact hrb
    simp only [hsymm, smul_eq_mul, indicator_of_mem hmem]
  · rw [indicator_of_notMem (show r ∉ Iio b from hrb)]
    refine (lintegral_congr fun θ => ?_).trans lintegral_zero
    have hmem : (r : ℂ) * exp (θ * I) ∉ ball (0 : ℂ) b := by
      rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (show 0 < r from hr)]
      exact hrb
    simp only [hsymm, smul_eq_mul, indicator_of_notMem hmem, mul_zero]

/-- The angular integral of the Jacobian. -/
lemma lintegral_angle_jac (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1) :
    ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal r * ENNReal.ofReal (‖deriv G (r * exp (θ * I))‖ ^ 2) =
      ENNReal.ofReal (∫ θ in (0 : ℝ)..(2 * π), jac G r θ) := by
  have hc := continuous_jac hG hr
  have hper : Function.Periodic (jac G r) (2 * π) := by
    intro θ
    simp only [jac]
    congr 3
    push_cast
    rw [add_mul, Complex.exp_add, mul_assoc (2 : ℂ), ← mul_assoc (2 : ℂ),
      Complex.exp_two_pi_mul_I, mul_one]
  have h1 : ∀ θ : ℝ, ENNReal.ofReal r * ENNReal.ofReal (‖deriv G (r * exp (θ * I))‖ ^ 2) =
      ENNReal.ofReal (jac G r θ) := fun θ => by
    rw [← ENNReal.ofReal_mul hr.1]; rfl
  simp only [h1]
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((hc.integrableOn_Icc (a := -π) (b := π)).mono_set Ioo_subset_Icc_self)
    (Eventually.of_forall fun θ => jac_nonneg hr.1 θ)]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [pi_pos])]
  have := hper.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at this
  exact this

lemma apply_zero_eq_inner (W : L2N →L[ℂ] L2N) (x : L2N) : W x 0 = ⟪star W e0, x⟫_ℂ := by
  rw [← inner_e0, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

lemma continuousOn_quad (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1)
    (x : L2N) :
    ContinuousOn (fun θ => jac G r θ * ‖holW G k r θ x 0‖ ^ 2) (Icc 0 (2 * π)) := by
  refine (continuous_jac hG hr).continuousOn.mul ?_
  have h0 : ContinuousOn (fun θ => holW G k r θ x) (Icc 0 (2 * π)) :=
    (continuousOn_holW k hG hr).clm_apply continuousOn_const
  have := (coordCLM 0).continuous.comp_continuousOn h0
  simpa [Function.comp_def] using (this.norm).pow 2

/-- Bessel's inequality for the vectors `W_r(θ)^* e₀`. -/
lemma sum_norm_holW_apply_zero_le (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) {n : ℕ} {v : Fin n → L2N}
    (hv : Orthonormal ℂ v) : ∑ i, ‖holW G k r θ (v i) 0‖ ^ 2 ≤ 1 := by
  have hu := holW_mem_unitary k isOpen_ball hG (circ_mem_ball hr) hθ
  have he : ‖star (holW G k r θ) e0‖ = 1 := by
    rw [ContinuousLinearMap.norm_map_of_mem_unitary (Unitary.star_mem hu)]
    simp [e0, lp.norm_single]
  have := hv.sum_inner_products_le (star (holW G k r θ) e0) (s := Finset.univ)
  rw [he, one_pow] at this
  refine le_trans (le_of_eq ?_) this
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [apply_zero_eq_inner, norm_inner_symm]

/-- The diagonal sums of `A_r`. -/
lemma diagSum_holA (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1)
    {n : ℕ} (v : Fin n → L2N) :
    diagSum (holA G k r) v = ENNReal.ofReal
      (∫ θ in (0 : ℝ)..(2 * π), jac G r θ * ∑ i, ‖holW G k r θ (v i) 0‖ ^ 2) := by
  have hint : ∀ i, IntervalIntegrable (fun θ => jac G r θ * ‖holW G k r θ (v i) 0‖ ^ 2)
      volume 0 (2 * π) := fun i =>
    (continuousOn_quad k hG hr (v i)).intervalIntegrable_of_Icc (by positivity)
  have hnn : ∀ i, 0 ≤ ∫ θ in (0 : ℝ)..(2 * π), jac G r θ * ‖holW G k r θ (v i) 0‖ ^ 2 :=
    fun i => intervalIntegral.integral_nonneg (by positivity) fun θ _ =>
      mul_nonneg (jac_nonneg hr.1 θ) (by positivity)
  unfold diagSum
  simp only [re_inner_holA k hG hr]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hnn i,
    ← intervalIntegral.integral_finset_sum fun i _ => hint i]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [Finset.mul_sum]

/-- `tr A_r = ∫₀^{2π} J(r,θ) dθ`. -/
theorem posTrace_holA (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1) :
    posTrace (holA G k r) = ENNReal.ofReal (∫ θ in (0 : ℝ)..(2 * π), jac G r θ) := by
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have hJint : IntervalIntegrable (jac G r) volume 0 (2 * π) :=
    (continuous_jac hG hr).intervalIntegrable _ _
  apply le_antisymm
  · refine iSup_le fun n => iSup_le fun v => iSup_le fun hv => ?_
    rw [diagSum_holA k hG hr]
    refine ENNReal.ofReal_le_ofReal (intervalIntegral.integral_mono_on h2π ?_ hJint fun θ hθ => ?_)
    · exact ((continuous_jac hG hr).continuousOn.mul (continuousOn_finset_sum _
        fun i _ => by
          have h0 : ContinuousOn (fun θ => holW G k r θ (v i)) (Icc 0 (2 * π)) :=
            (continuousOn_holW k hG hr).clm_apply continuousOn_const
          have := (coordCLM 0).continuous.comp_continuousOn h0
          simpa [Function.comp_def] using (this.norm).pow 2)).intervalIntegrable_of_Icc h2π
    · calc jac G r θ * ∑ i, ‖holW G k r θ (v i) 0‖ ^ 2 ≤ jac G r θ * 1 :=
            mul_le_mul_of_nonneg_left (sum_norm_holW_apply_zero_le k hG hr hθ hv)
              (jac_nonneg hr.1 θ)
        _ = jac G r θ := mul_one _
  · -- the first `n` basis vectors
    let b : HilbertBasis ℕ ℂ L2N := default
    let u : (n : ℕ) → Fin n → L2N := fun n i => b i
    have hu : ∀ n, Orthonormal ℂ (u n) := fun n =>
      b.orthonormal.comp _ Fin.val_injective
    set F : ℕ → ℝ → ℝ := fun n θ => jac G r θ * ∑ i, ‖holW G k r θ (u n i) 0‖ ^ 2 with hF
    have hlim : Tendsto (fun n => ∫ θ in (0 : ℝ)..(2 * π), F n θ) atTop
        (𝓝 (∫ θ in (0 : ℝ)..(2 * π), jac G r θ)) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (jac G r) ?_ ?_
        hJint ?_
      · refine Eventually.of_forall fun n => ?_
        have hc : ContinuousOn (F n) (Icc 0 (2 * π)) :=
          (continuous_jac hG hr).continuousOn.mul (continuousOn_finset_sum _ fun i _ => by
            have h0 : ContinuousOn (fun θ => holW G k r θ (u n i)) (Icc 0 (2 * π)) :=
              (continuousOn_holW k hG hr).clm_apply continuousOn_const
            have := (coordCLM 0).continuous.comp_continuousOn h0
            simpa [Function.comp_def] using (this.norm).pow 2)
        rw [uIoc_of_le h2π]
        exact (hc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
      · refine Eventually.of_forall fun n => Eventually.of_forall fun θ hθ => ?_
        rw [uIoc_of_le h2π] at hθ
        have hθ' := Ioc_subset_Icc_self hθ
        have h1 := sum_norm_holW_apply_zero_le k hG hr hθ' (hu n)
        have h0 : 0 ≤ ∑ i, ‖holW G k r θ (u n i) 0‖ ^ 2 := by positivity
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (jac_nonneg hr.1 θ) h0)]
        calc jac G r θ * ∑ i, ‖holW G k r θ (u n i) 0‖ ^ 2 ≤ jac G r θ * 1 :=
              mul_le_mul_of_nonneg_left h1 (jac_nonneg hr.1 θ)
          _ = jac G r θ := mul_one _
      · refine Eventually.of_forall fun θ hθ => ?_
        rw [uIoc_of_le h2π] at hθ
        have hθ' := Ioc_subset_Icc_self hθ
        have hU := holW_mem_unitary k isOpen_ball hG (circ_mem_ball hr) hθ'
        set w := star (holW G k r θ) e0 with hw
        have hw1 : ‖w‖ = 1 := by
          rw [hw, ContinuousLinearMap.norm_map_of_mem_unitary (Unitary.star_mem hU)]
          simp [e0, lp.norm_single]
        have hsum : HasSum (fun i => ‖⟪b i, w⟫_ℂ‖ ^ 2) 1 := by
          have := lp.hasSum_norm (p := 2) (by norm_num) (b.repr w)
          simp only [HilbertBasis.repr_apply_apply, LinearIsometryEquiv.norm_map, hw1] at this
          norm_num at this
          exact this
        have hterm : ∀ n, ∑ i : Fin n, ‖holW G k r θ (u n i) 0‖ ^ 2 =
            ∑ i ∈ Finset.range n, ‖⟪b i, w⟫_ℂ‖ ^ 2 := by
          intro n
          rw [← Fin.sum_univ_eq_sum_range (fun i => ‖⟪b i, w⟫_ℂ‖ ^ 2) n]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [apply_zero_eq_inner, norm_inner_symm]
        have := (hsum.tendsto_sum_nat).const_mul (jac G r θ)
        rw [mul_one] at this
        simpa only [hF, hterm] using this
    refine le_of_tendsto' (ENNReal.tendsto_ofReal hlim) fun n => ?_
    rw [← diagSum_holA k hG hr (u n)]
    exact le_iSup_of_le n (le_iSup_of_le (u n) (le_iSup_of_le (hu n) le_rfl))

/-- `tr L_{r,k} = (k²/2) ∫₀^{2π} r |G'(r e^{iθ})|² dθ` for `0 ≤ r < 1`. -/
theorem posTrace_holL (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1) :
    posTrace (holL G k r) =
      ENNReal.ofReal (k ^ 2 / 2) * ENNReal.ofReal (∫ θ in (0 : ℝ)..(2 * π), jac G r θ) := by
  rw [holL_eq, posTrace_smul _ (by positivity), posTrace_conj (holM_mem_unitary k hG hr),
    posTrace_holA k hG hr]

/-- `∫₀ᵇ tr L_{r,k} dr = (k²/2) |G(b𝔻)|` for `0 < b < 1`. -/
theorem lintegral_posTrace_holL (hG : DifferentiableOn ℂ G (ball 0 1))
    (hinj : InjOn G (ball 0 1)) {b : ℝ} (hb1 : b < 1) :
    ∫⁻ r in Icc 0 b, posTrace (holL G k r) = ENNReal.ofReal (k ^ 2 / 2) * volume (G '' ball 0 b) := by
  have hsub : Icc 0 b ⊆ Ico (0 : ℝ) 1 := Icc_subset_Ico_right hb1
  rw [setLIntegral_congr_fun measurableSet_Icc (fun r hr => posTrace_holL k hG (hsub hr)),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, volume_image_ball_eq hG hinj hb1.le,
    lintegral_ball_polar _ (by fun_prop), setLIntegral_congr Ioo_ae_eq_Icc.symm]
  congr 1
  refine (setLIntegral_congr_fun measurableSet_Ioo fun r hr => ?_)
  exact (lintegral_angle_jac hG ⟨hr.1.le, hr.2.trans hb1⟩).symm

/-- For `0 < r < 1` and `v ≠ 0`,
`re ⟪v, L_{r,k} v⟫ > 0`. -/
theorem re_inner_holL_pos (hG : DifferentiableOn ℂ G (ball 0 1)) (hinj : InjOn G (ball 0 1))
    (hk : 0 < k) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) {v : L2N} (hv : v ≠ 0) :
    0 < RCLike.re ⟪v, holL G k r v⟫_ℂ := by
  have hr' := Ioo_subset_Ico_self hr
  set M := holH G k r * star (holR G k r) with hM
  have hMu : M ∈ unitary (L2N →L[ℂ] L2N) := holM_mem_unitary k hG hr'
  have hw : star M v ≠ 0 := by
    intro h
    apply hv
    have := congrArg M h
    rwa [← ContinuousLinearMap.mul_apply, Unitary.mul_star_self_of_mem hMu,
      ContinuousLinearMap.one_apply, map_zero] at this
  have hpos := holA_pos k hG hinj hk.ne' hr hw
  rw [holL_eq, ← hM]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply, inner_smul_right]
  rw [ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.adjoint_inner_left,
    ← ContinuousLinearMap.star_eq_adjoint, RCLike.re_to_complex, Complex.re_ofReal_mul,
    ← RCLike.re_to_complex]
  exact mul_pos (by positivity) hpos

end

section

/-! ## Polar boundary parametrization of a conformal map -/

open Complex

/-- Angular derivative: `∂_θ F(r e^{iθ}) = i r e^{iθ} F'(r e^{iθ})`. -/
theorem hasDerivAt_angular {F : ℂ → ℂ} {r θ : ℝ}
    (hF : DifferentiableAt ℂ F (r * exp (θ * I))) :
    HasDerivAt (fun t : ℝ => F (r * exp (t * I)))
      (I * r * exp (θ * I) * deriv F (r * exp (θ * I))) θ := by
  have h1 : HasDerivAt (fun t : ℝ => (r : ℂ) * exp (t * I)) (r * (exp (θ * I) * I)) θ := by
    have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I θ := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const I
    exact (h2.cexp).const_mul (r : ℂ)
  have := hF.hasDerivAt.comp θ h1
  convert this using 1
  ring

/-- The oriented real Jacobian of `(r, θ) ↦ F(r e^{iθ})` equals `r |F'(r e^{iθ})|²`:
with `∂_r γ = e^{iθ} F'` and `∂_θ γ = i r e^{iθ} F'`,
`Re(∂_r γ) Im(∂_θ γ) - Re(∂_θ γ) Im(∂_r γ) = r ‖F'‖²`. -/
theorem polar_jacobian (r θ : ℝ) (d : ℂ) :
    (exp (θ * I) * d).re * (I * r * exp (θ * I) * d).im
      - (I * r * exp (θ * I) * d).re * (exp (θ * I) * d).im = r * ‖d‖ ^ 2 := by
  set w := exp (θ * I) * d with hw
  have hnorm : ‖w‖ = ‖d‖ := by
    rw [hw, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have h1 : I * r * exp (θ * I) * d = I * r * w := by rw [hw]; ring
  rw [h1, ← hnorm, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im]
  ring

/-- The commutator identity, valid in any ring:
`[aX + bY, cX + dY] = (a d - b c) [X, Y]` for commuting real scalars. -/
theorem commutator_linear_combination {R : Type*} [Ring R] [Algebra ℝ R]
    (X Y : R) (a b c d : ℝ) :
    (a • X + b • Y) * (c • X + d • Y) - (c • X + d • Y) * (a • X + b • Y)
      = (a * d - b * c) • (X * Y - Y * X) := by
  simp only [add_mul, mul_add, smul_mul_smul, smul_sub, sub_smul, mul_comm d a, mul_comm c b]
  abel_nf
  simp only [mul_comm c a, mul_comm d b]
  abel

end

section

/-! ## Radial derivative of the holonomy -/

open scoped InnerProductSpace
open MeasureTheory Set Real Metric Complex Filter Topology Asymptotics

/-- The operator `Re(d) X + Im(d) Y` attached to a planar vector `d`. -/
def coefOf (k : ℝ) (d : ℂ) : L2N →L[ℂ] L2N :=
  (d.re : ℂ) • opX k + (d.im : ℂ) • opY k

variable {G : ℂ → ℂ} (k : ℝ)

/-- `∂_r γ_r(θ) = e^{iθ} G'(r e^{iθ})`. -/
def dRad (G : ℂ → ℂ) (r θ : ℝ) : ℂ := exp (θ * I) * deriv G (r * exp (θ * I))

/-- `∂_r ∂_θ γ_r(θ) = i e^{iθ} G'(r e^{iθ}) + i r e^{2iθ} G''(r e^{iθ})`. -/
def dMix (G : ℂ → ℂ) (r θ : ℝ) : ℂ :=
  I * exp (θ * I) * deriv G (r * exp (θ * I)) +
    I * r * exp (θ * I) * exp (θ * I) * deriv (deriv G) (r * exp (θ * I))

lemma coefAng_eq (G : ℂ → ℂ) (r θ : ℝ) : coefAng G k r θ = coefOf k (dAng G r θ) := rfl

lemma coefOf_sub (d e : ℂ) : coefOf k d - coefOf k e = coefOf k (d - e) := by
  simp only [coefOf, sub_re, sub_im, ofReal_sub, sub_smul]; abel

lemma coefOf_smul (a : ℝ) (d : ℂ) : coefOf k ((a : ℂ) * d) = (a : ℂ) • coefOf k d := by
  simp only [coefOf, re_ofReal_mul, im_ofReal_mul, ofReal_mul, smul_add, mul_smul]

lemma norm_coefOf_le (d : ℂ) : ‖coefOf k d‖ ≤ 2 * |k| * ‖d‖ := by
  unfold coefOf
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  have h1 := Complex.abs_re_le_norm d
  have h2 := Complex.abs_im_le_norm d
  have h3 := norm_opX_le k
  have h4 := norm_opY_le k
  calc |d.re| * ‖opX k‖ + |d.im| * ‖opY k‖
      ≤ ‖d‖ * |k| + ‖d‖ * |k| := by gcongr
    _ = 2 * |k| * ‖d‖ := by ring

/-- `r ↦ C_θ` has derivative `Re(∂_r∂_θγ) X + Im(∂_r∂_θγ) Y`. -/
lemma hasDerivAt_dAng (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1)
    (θ : ℝ) : HasDerivAt (fun s => dAng G s θ) (dMix G r θ) r := by
  have hmem := circ_mem_ball hr θ
  have hd : DifferentiableAt ℂ (deriv G) (r * exp (θ * I)) :=
    ((hG.deriv isOpen_ball) _ hmem).differentiableAt (isOpen_ball.mem_nhds hmem)
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * exp (θ * I)) (exp (θ * I)) r := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := r)).mul_const (exp (θ * I))
  have h2 := hd.hasDerivAt.comp r h1
  have h3 : HasDerivAt (fun s : ℝ => I * (s : ℂ) * exp (θ * I)) (I * exp (θ * I)) r := by
    simpa [mul_assoc] using h1.const_mul I
  have := h3.mul h2
  unfold dAng dMix
  convert this using 1
  simp only [Function.comp_apply]
  ring

lemma hasDerivAt_dRad (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1)
    (θ : ℝ) : HasDerivAt (fun t => dRad G r t) (dMix G r θ) θ := by
  have hmem := circ_mem_ball hr θ
  have hd : DifferentiableAt ℂ (deriv G) (r * exp (θ * I)) :=
    ((hG.deriv isOpen_ball) _ hmem).differentiableAt (isOpen_ball.mem_nhds hmem)
  have he : HasDerivAt (fun t : ℝ => exp (t * I)) (exp (θ * I) * I) θ := by
    have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I θ := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const I
    exact h2.cexp
  have h1 : HasDerivAt (fun t : ℝ => (r : ℂ) * exp (t * I)) (r * (exp (θ * I) * I)) θ :=
    he.const_mul _
  have h2 := hd.hasDerivAt.comp θ h1
  have := he.mul h2
  unfold dRad dMix
  convert this using 1
  simp only [Function.comp_apply]
  ring

lemma hasDerivAt_coefOf {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => coefOf k (f y)) (coefOf k f') x := by
  have hre : HasDerivAt (fun y => ((f y).re : ℂ)) (f'.re : ℂ) x := by
    have := (Complex.ofRealCLM.comp Complex.reCLM).hasFDerivAt.comp_hasDerivAt x hf
    simpa using this
  have him : HasDerivAt (fun y => ((f y).im : ℂ)) (f'.im : ℂ) x := by
    have := (Complex.ofRealCLM.comp Complex.imCLM).hasFDerivAt.comp_hasDerivAt x hf
    simpa using this
  exact (hre.smul_const (opX k)).add (him.smul_const (opY k))

lemma continuous_coefOf : Continuous (coefOf k) := by
  unfold coefOf
  fun_prop

lemma continuous_dMix (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) :
    Continuous (dMix G r) := by
  have h1 : ContinuousOn (deriv G) (ball 0 1) := (hG.deriv isOpen_ball).continuousOn
  have h2 : ContinuousOn (deriv (deriv G)) (ball 0 1) :=
    ((hG.deriv isOpen_ball).deriv isOpen_ball).continuousOn
  have hγ : Continuous fun θ : ℝ => (r : ℂ) * exp (θ * I) := by fun_prop
  unfold dMix
  have := h1.comp_continuous hγ (circ_mem_ball hr)
  have := h2.comp_continuous hγ (circ_mem_ball hr)
  fun_prop

/-- The commutator identity `[C_θ, C_rad] = -J (ik²/2) P₀`. -/
lemma commutator_coefAng_coefRad (G : ℂ → ℂ) (r θ : ℝ) :
    coefAng G k r θ * coefOf k (dRad G r θ) - coefOf k (dRad G r θ) * coefAng G k r θ =
      ((-jac G r θ : ℝ) : ℂ) • ((I * k ^ 2 / 2) • projE0) := by
  have h := commutator_linear_combination (opX k) (opY k) (dAng G r θ).re (dAng G r θ).im
    (dRad G r θ).re (dRad G r θ).im
  simp only [← Complex.coe_smul] at h
  have hs : (dAng G r θ).re * (dRad G r θ).im - (dAng G r θ).im * (dRad G r θ).re =
      -jac G r θ := by
    have hj := polar_jacobian r θ (deriv G (r * exp (θ * I)))
    simp only [dAng, dRad, jac]
    linarith
  rw [coefAng_eq, coefOf, coefOf, h, commutator_opX_opY, hs]

lemma continuousOn_dMix_uncurry (hG : DifferentiableOn ℂ G (ball 0 1)) {b : ℝ} (hb : b < 1) :
    ContinuousOn (Function.uncurry (dMix G)) (Icc 0 b ×ˢ univ) := by
  have h2 : ContinuousOn (deriv (deriv G)) (ball 0 1) :=
    ((hG.deriv isOpen_ball).deriv isOpen_ball).continuousOn
  have hγ : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) * exp (p.2 * I) := by fun_prop
  have hmem : ∀ p ∈ Icc 0 b ×ˢ (univ : Set ℝ), (p.1 : ℂ) * exp (p.2 * I) ∈ ball (0 : ℂ) 1 :=
    fun p hp => circ_mem_ball ⟨hp.1.1, lt_of_le_of_lt hp.1.2 hb⟩ p.2
  have hc2 := h2.comp hγ.continuousOn hmem
  have hc1 := continuousOn_derivG_circ hG hb
  have : Function.uncurry (dMix G) = fun p : ℝ × ℝ =>
      I * exp (p.2 * I) * deriv G (p.1 * exp (p.2 * I)) +
        I * p.1 * exp (p.2 * I) * exp (p.2 * I) * deriv (deriv G) (p.1 * exp (p.2 * I)) := by
    funext p; rfl
  rw [this]
  refine ContinuousOn.add ?_ ?_
  · exact (Continuous.continuousOn (by fun_prop)).mul hc1
  · exact (Continuous.continuousOn (by fun_prop)).mul hc2

/-- Uniform differentiability of `r ↦ ∂_θ γ_r(θ)` in `θ ∈ [0, 2π]`. -/
lemma dAng_unif_deriv (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s ∈ Ico (0 : ℝ) 1, |s - r| < δ → ∀ θ ∈ Icc 0 (2 * π),
      ‖dAng G s θ - dAng G r θ - (s - r) * dMix G r θ‖ ≤ ε * |s - r| := by
  set b := (1 + r) / 2 with hbdef
  have hb : b < 1 := by rw [hbdef]; linarith [hr.2]
  have hrb : r ∈ Icc 0 b := ⟨hr.1, by rw [hbdef]; linarith [hr.2]⟩
  obtain ⟨η, hη, h⟩ := uniform_in_snd ((continuousOn_dMix_uncurry hG hb).mono
    (prod_mono_right (subset_univ (Icc 0 (2 * π))))) hrb hε
  have hbr : 0 < b - r := by rw [hbdef]; linarith [hr.2]
  refine ⟨min η (b - r), lt_min hη hbr, fun s hs hsr θ hθ => ?_⟩
  have hsr1 := lt_of_lt_of_le hsr (min_le_left _ _)
  have hsr2 := lt_of_lt_of_le hsr (min_le_right _ _)
  set S := Icc 0 b ∩ Ioo (r - η) (r + η) with hS
  have hSc : Convex ℝ S := (convex_Icc _ _).inter (convex_Ioo _ _)
  have hrS : r ∈ S := ⟨hrb, by constructor <;> linarith⟩
  have hsS : s ∈ S := by
    rw [abs_lt] at hsr1 hsr2
    exact ⟨⟨hs.1, by linarith⟩, by constructor <;> linarith⟩
  have hderiv : ∀ u ∈ S, HasDerivWithinAt (fun u => dAng G u θ - u * dMix G r θ)
      (dMix G u θ - dMix G r θ) S u := by
    intro u hu
    have hu' : u ∈ Ico (0 : ℝ) 1 := ⟨hu.1.1, lt_of_le_of_lt hu.1.2 hb⟩
    have h1 := hasDerivAt_dAng hG hu' θ
    have h2 : HasDerivAt (fun u : ℝ => (u : ℂ) * dMix G r θ) (dMix G r θ) u := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).mul_const (dMix G r θ)
    exact (h1.sub h2).hasDerivWithinAt
  have hbound : ∀ u ∈ S, ‖dMix G u θ - dMix G r θ‖ ≤ ε := by
    intro u hu
    have := h u hu.1 (abs_lt.2 ⟨by linarith [hu.2.1], by linarith [hu.2.2]⟩) θ hθ
    rw [dist_eq_norm] at this
    exact this.le
  have := hSc.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hrS hsS
  rw [Real.norm_eq_abs] at this
  convert this using 2
  ring

/-- The Duhamel identity for the angular transport. -/
lemma holW_sub_holW (hG : DifferentiableOn ℂ G (ball 0 1)) {r s : ℝ} (hr : r ∈ Ico (0 : ℝ) 1)
    (hs : s ∈ Ico (0 : ℝ) 1) {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * π)) :
    holW G k s θ - holW G k r θ = holW G k r θ * ∫ t in (0 : ℝ)..θ,
      star (holW G k r t) * (coefAng G k s t - coefAng G k r t) * holW G k s t := by
  obtain ⟨hr0, hrd⟩ := holW_spec k isOpen_ball hG (circ_mem_ball hr)
  obtain ⟨hs0, hsd⟩ := holW_spec k isOpen_ball hG (circ_mem_ball hs)
  have hru : ∀ t ∈ Icc 0 (2 * π), holW G k r t ∈ unitary (L2N →L[ℂ] L2N) := fun t ht =>
    holW_mem_unitary k isOpen_ball hG (circ_mem_ball hr) ht
  set g : ℝ → L2N →L[ℂ] L2N := fun t => star (holW G k r t) * holW G k s t with hg
  set g' : ℝ → L2N →L[ℂ] L2N := fun t =>
    star (holW G k r t) * (coefAng G k s t - coefAng G k r t) * holW G k s t with hg'
  have hgd : ∀ t ∈ Icc 0 (2 * π), HasDerivWithinAt g (g' t) (Icc 0 (2 * π)) t := by
    intro t ht
    have hd := ((hrd t ht).star).mul (hsd t ht)
    convert hd using 1
    rw [star_mul, star_coefAng]
    simp only [hg', mul_sub, sub_mul, mul_neg, neg_mul, mul_assoc]
    abel
  have hsub : Icc 0 θ ⊆ Icc 0 (2 * π) := Icc_subset_Icc_right hθ.2
  have hg'c : ContinuousOn g' (Icc 0 (2 * π)) := by
    have hWr := continuousOn_holW k hG hr
    have hWs := continuousOn_holW k hG hs
    have hCs := (continuous_coefAng k isOpen_ball hG (circ_mem_ball hs)).continuousOn
      (s := Icc 0 (2 * π))
    have hCr := (continuous_coefAng k isOpen_ball hG (circ_mem_ball hr)).continuousOn
      (s := Icc 0 (2 * π))
    exact ((continuous_star.comp_continuousOn hWr).mul (hCs.sub hCr)).mul hWs
  have hint : ∫ t in (0 : ℝ)..θ, g' t = g θ - g 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hθ.1
      (fun t ht => (hgd t (hsub ht)).continuousWithinAt.mono hsub) (fun t ht => ?_)
      ((hg'c.mono hsub).intervalIntegrable_of_Icc hθ.1)
    have ht' : t ∈ Ioo 0 (2 * π) := ⟨ht.1, ht.2.trans_le hθ.2⟩
    exact ((hgd t (Ioo_subset_Icc_self ht')).hasDerivAt (Icc_mem_nhds ht'.1 ht'.2)).hasDerivWithinAt
  have hg0 : g 0 = 1 := by simp [hg, hr0, hs0]
  rw [hint, hg0]
  simp only [hg, mul_sub, mul_one, ← mul_assoc, Unitary.mul_star_self_of_mem (hru θ hθ), one_mul]

/-- Pointwise estimate for the Duhamel integrand. -/
lemma norm_duhamel_integrand_le (hG : DifferentiableOn ℂ G (ball 0 1)) {r s t : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1) (ht : t ∈ Icc 0 (2 * π)) :
    ‖star (holW G k r t) * (coefAng G k s t - coefAng G k r t) * holW G k s t -
        (s - r : ℂ) • (star (holW G k r t) * coefOf k (dMix G r t) * holW G k r t)‖ ≤
      2 * |k| * ‖dAng G s t - dAng G r t - (s - r) * dMix G r t‖ +
        2 * |k| * ‖dAng G s t - dAng G r t‖ * ‖holW G k s t - holW G k r t‖ := by
  have hru := holW_mem_unitary k isOpen_ball hG (circ_mem_ball hr) ht
  have heq : star (holW G k r t) * (coefAng G k s t - coefAng G k r t) * holW G k s t -
        (s - r : ℂ) • (star (holW G k r t) * coefOf k (dMix G r t) * holW G k r t) =
      star (holW G k r t) * coefOf k (dAng G s t - dAng G r t - (s - r) * dMix G r t) *
          holW G k r t +
        star (holW G k r t) * coefOf k (dAng G s t - dAng G r t) *
          (holW G k s t - holW G k r t) := by
    have : ((s : ℂ) - r) = ((s - r : ℝ) : ℂ) := by push_cast; ring
    rw [this, ← coefOf_sub, ← coefOf_sub, coefOf_smul, coefAng_eq, coefAng_eq]
    simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm]
    abel
  rw [heq]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [CStarRing.norm_mul_mem_unitary _ hru,
      CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem hru)]
    have : (dAng G s t - dAng G r t - (s - r) * dMix G r t) =
        (dAng G s t - dAng G r t - ((s - r : ℝ) : ℂ) * dMix G r t) := by push_cast; ring
    rw [this]
    exact norm_coefOf_le k _
  · rw [mul_assoc, CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem hru)]
    exact (norm_mul_le _ _).trans (by gcongr; exact norm_coefOf_le k _)

/-- The radial derivative of the holonomy: `∂_r V_r = V_r ∫₀^{2π} W_r^* (∂_r C_θ) W_r dθ`. -/
lemma hasDerivWithinAt_holV (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1) :
    HasDerivWithinAt (holV G k) (holV G k r * ∫ t in (0 : ℝ)..(2 * π),
      star (holW G k r t) * coefOf k (dMix G r t) * holW G k r t) (Ico 0 1) r := by
  rw [hasDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  have hpi := Real.pi_pos
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn
    (continuous_dMix hG hr).continuousOn
  set L := 2 * |k| * (1 + |M|) with hL
  have hL0 : 0 ≤ L := by positivity
  set ε₁ := min 1 (c / (8 * π * (|k| + 1))) with hε₁
  have hε₁pos : 0 < ε₁ := lt_min one_pos (by positivity)
  obtain ⟨δ, hδ, hδh⟩ := dAng_unif_deriv hG hr hε₁pos
  set δ₂ := c / (8 * π ^ 2 * (L ^ 2 + 1)) with hδ₂
  have hδ₂pos : 0 < δ₂ := by positivity
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds r (lt_min hδ hδ₂pos))]
    with s hs hsb
  rw [mem_ball, Real.dist_eq] at hsb
  have hsδ : |s - r| < δ := lt_of_lt_of_le hsb (min_le_left _ _)
  have hsδ₂ : |s - r| < δ₂ := lt_of_lt_of_le hsb (min_le_right _ _)
  have hVu := (holU_mem_unitary k isOpen_ball hG seg_mem_ball hr (circ_mem_ball hr)).1
  -- pointwise bounds
  have hdA : ∀ t ∈ Icc 0 (2 * π), ‖dAng G s t - dAng G r t - (s - r) * dMix G r t‖ ≤
      ε₁ * |s - r| := fun t ht => hδh s hs hsδ t ht
  have hdA' : ∀ t ∈ Icc 0 (2 * π), ‖dAng G s t - dAng G r t‖ ≤ (1 + |M|) * |s - r| := by
    intro t ht
    have h1 := hdA t ht
    have h2 : ‖((s : ℂ) - r) * dMix G r t‖ ≤ |s - r| * |M| := by
      rw [norm_mul, show ((s : ℂ) - r) = ((s - r : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs]
      gcongr
      exact (hM t ht).trans (le_abs_self _)
    have h3 := norm_add_le (dAng G s t - dAng G r t - (s - r) * dMix G r t) ((s - r) * dMix G r t)
    rw [sub_add_cancel] at h3
    have : ε₁ ≤ 1 := min_le_left _ _
    nlinarith [abs_nonneg (s - r)]
  have hW : ∀ t ∈ Icc 0 (2 * π), ‖holW G k s t - holW G k r t‖ ≤ L * |s - r| * (2 * π) := by
    intro t ht
    refine (norm_holW_sub_le hG hr hs (ε := L * |s - r|) (fun θ hθ => ?_) ht).trans ?_
    · rw [coefAng_eq, coefAng_eq, coefOf_sub]
      refine (norm_coefOf_le k _).trans ?_
      rw [hL, mul_assoc (2 * |k|)]
      gcongr
      exact hdA' θ hθ
    · gcongr; exact ht.2
  have hpt : ∀ t ∈ Icc 0 (2 * π),
      ‖star (holW G k r t) * (coefAng G k s t - coefAng G k r t) * holW G k s t -
        (s - r : ℂ) • (star (holW G k r t) * coefOf k (dMix G r t) * holW G k r t)‖ ≤
      (2 * |k| * ε₁ + L ^ 2 * (2 * π) * |s - r|) * |s - r| := by
    intro t ht
    refine (norm_duhamel_integrand_le k hG hr ht).trans ?_
    have e1 : 2 * |k| * ‖dAng G s t - dAng G r t - (s - r) * dMix G r t‖ ≤
        2 * |k| * (ε₁ * |s - r|) := by gcongr; exact hdA t ht
    have e2 : 2 * |k| * ‖dAng G s t - dAng G r t‖ * ‖holW G k s t - holW G k r t‖ ≤
        (L * |s - r|) * (L * |s - r| * (2 * π)) := by
      have a1 : 2 * |k| * ‖dAng G s t - dAng G r t‖ ≤ L * |s - r| := by
        rw [hL, mul_assoc (2 * |k|)]; gcongr; exact hdA' t ht
      exact mul_le_mul a1 (hW t ht) (norm_nonneg _) (by positivity)
    nlinarith [e1, e2]
  -- Duhamel at θ = 2π
  have hD := holW_sub_holW k hG hr hs ⟨two_pi_pos.le, le_rfl⟩
  have hint1 : IntervalIntegrable (fun t => star (holW G k r t) *
      (coefAng G k s t - coefAng G k r t) * holW G k s t) volume 0 (2 * π) := by
    have hWr := continuousOn_holW k hG hr
    have hWs := continuousOn_holW k hG hs
    have hCs := (continuous_coefAng k isOpen_ball hG (circ_mem_ball hs)).continuousOn
      (s := Icc 0 (2 * π))
    have hCr := (continuous_coefAng k isOpen_ball hG (circ_mem_ball hr)).continuousOn
      (s := Icc 0 (2 * π))
    exact (((continuous_star.comp_continuousOn hWr).mul (hCs.sub hCr)).mul hWs
      ).intervalIntegrable_of_Icc two_pi_pos.le
  have hc2 : ContinuousOn (fun t => star (holW G k r t) * coefOf k (dMix G r t) *
      holW G k r t) (Icc 0 (2 * π)) := by
    have hWr := continuousOn_holW k hG hr
    exact ((continuous_star.comp_continuousOn hWr).mul
      ((continuous_coefOf k).comp (continuous_dMix hG hr)).continuousOn).mul hWr
  have hexpr : holV G k s - holV G k r - (s - r) • (holV G k r * ∫ t in (0 : ℝ)..(2 * π),
      star (holW G k r t) * coefOf k (dMix G r t) * holW G k r t) =
      holV G k r * ∫ t in (0 : ℝ)..(2 * π),
        (star (holW G k r t) * (coefAng G k s t - coefAng G k r t) * holW G k s t -
        (s - r : ℂ) • (star (holW G k r t) * coefOf k (dMix G r t) * holW G k r t)) := by
    have hint3 : IntervalIntegrable (fun t => ((s : ℂ) - r) • (star (holW G k r t) *
        coefOf k (dMix G r t) * holW G k r t)) volume 0 (2 * π) :=
      (hc2.const_smul ((s : ℂ) - r)).intervalIntegrable_of_Icc two_pi_pos.le
    rw [intervalIntegral.integral_sub hint1 hint3, intervalIntegral.integral_smul,
      mul_sub, holV, holV, hD, mul_smul_comm, ← Complex.coe_smul]
    push_cast
    rfl
  rw [hexpr, CStarRing.norm_mem_unitary_mul _ hVu, Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C :=
    (2 * |k| * ε₁ + L ^ 2 * (2 * π) * |s - r|) * |s - r|) fun t ht => hpt t ?_).trans ?_
  · rw [uIoc_of_le two_pi_pos.le] at ht
    exact Ioc_subset_Icc_self ht
  rw [sub_zero, abs_of_pos two_pi_pos]
  clear_value L ε₁ δ₂
  have k1 : 2 * |k| * ε₁ * (2 * π) ≤ c / 2 := by
    have : ε₁ ≤ c / (8 * π * (|k| + 1)) := hε₁ ▸ min_le_right _ _
    calc 2 * |k| * ε₁ * (2 * π) ≤ 2 * |k| * (c / (8 * π * (|k| + 1))) * (2 * π) := by gcongr
      _ = c / 2 * (|k| / (|k| + 1)) := by field_simp; ring
      _ ≤ c / 2 := mul_le_of_le_one_right (by positivity)
          ((div_le_one (by positivity)).2 (by linarith))
  have k2 : L ^ 2 * (2 * π) * |s - r| * (2 * π) ≤ c / 2 := by
    calc L ^ 2 * (2 * π) * |s - r| * (2 * π) ≤ L ^ 2 * (2 * π) * δ₂ * (2 * π) := by
          gcongr
      _ = c / 2 * (L ^ 2 / (L ^ 2 + 1)) := by rw [hδ₂]; field_simp; ring
      _ ≤ c / 2 := mul_le_of_le_one_right (by positivity)
          ((div_le_one (by positivity)).2 (by linarith))
  calc (2 * |k| * ε₁ + L ^ 2 * (2 * π) * |s - r|) * |s - r| * (2 * π)
      = (2 * |k| * ε₁ * (2 * π) + L ^ 2 * (2 * π) * |s - r| * (2 * π)) * |s - r| := by ring
    _ ≤ (c / 2 + c / 2) * |s - r| :=
        mul_le_mul_of_nonneg_right (add_le_add k1 k2) (abs_nonneg _)
    _ = c * ‖s - r‖ := by rw [Real.norm_eq_abs]; ring

lemma hasDerivWithinAt_curv (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Icc 0 (2 * π)) :
    HasDerivWithinAt (fun t => star (holW G k r t) * coefOf k (dRad G r t) * holW G k r t)
      (star (holW G k r t) * coefOf k (dMix G r t) * holW G k r t +
        (I * k ^ 2 / 2) • (((jac G r t : ℝ) : ℂ) • (star (holW G k r t) * projE0 * holW G k r t)))
      (Icc 0 (2 * π)) t := by
  obtain ⟨-, hWd⟩ := holW_spec k isOpen_ball hG (circ_mem_ball hr)
  have hKd : HasDerivAt (fun t => coefOf k (dRad G r t)) (coefOf k (dMix G r t)) t :=
    hasDerivAt_coefOf k (hasDerivAt_dRad hG hr t)
  have hd := (((hWd t ht).star).mul hKd.hasDerivWithinAt).mul (hWd t ht)
  convert hd using 1
  have hcomm := commutator_coefAng_coefRad k G r t
  set W := holW G k r t
  set K := coefOf k (dRad G r t)
  set C := coefAng G k r t
  have hQ' : (I * k ^ 2 / 2) • (((jac G r t : ℝ) : ℂ) • (star W * projE0 * W)) =
      star W * (K * C - C * K) * W := by
    rw [show K * C - C * K = -(C * K - K * C) by abel, hcomm]
    simp only [ofReal_neg, neg_smul, neg_neg, mul_smul_comm, smul_mul_assoc, mul_assoc]
    rw [smul_comm]
  rw [hQ', star_mul, star_coefAng]
  simp only [Pi.mul_apply, mul_sub, sub_mul, mul_neg, neg_mul, mul_assoc, add_mul]
  abel

/-- `∫₀^{2π} W_r^* (∂_r C_θ) W_r dθ = V_r^* B_r V_r - B_r - (ik²/2) A_r`. -/
theorem integral_curvature (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..(2 * π), star (holW G k r t) * coefOf k (dMix G r t) * holW G k r t) =
      star (holV G k r) * coefRad G k r * holV G k r - coefRad G k r -
        (I * k ^ 2 / 2) • holA G k r := by
  have hW0 := (holW_spec k isOpen_ball hG (circ_mem_ball hr)).1
  have hWc := continuousOn_holW k hG hr
  have hPc : ContinuousOn (fun t => star (holW G k r t) * coefOf k (dMix G r t) * holW G k r t)
      (Icc 0 (2 * π)) :=
    ((continuous_star.comp_continuousOn hWc).mul
      ((continuous_coefOf k).comp (continuous_dMix hG hr)).continuousOn).mul hWc
  have hQc : ContinuousOn (fun t => (I * k ^ 2 / 2) •
      (((jac G r t : ℝ) : ℂ) • (star (holW G k r t) * projE0 * holW G k r t))) (Icc 0 (2 * π)) :=
    (continuousOn_holA_integrand k hG hr).const_smul _
  have hint := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le two_pi_pos.le
      (fun t ht => (hasDerivWithinAt_curv k hG hr ht).continuousWithinAt) (fun t ht =>
        ((hasDerivWithinAt_curv k hG hr (Ioo_subset_Icc_self ht)).hasDerivAt
          (Icc_mem_nhds ht.1 ht.2)).hasDerivWithinAt)
      ((hPc.add hQc).intervalIntegrable_of_Icc two_pi_pos.le)
  rw [intervalIntegral.integral_add (hPc.intervalIntegrable_of_Icc two_pi_pos.le)
    (hQc.intervalIntegrable_of_Icc two_pi_pos.le), intervalIntegral.integral_smul] at hint
  have he : exp (((2 * π : ℝ) : ℂ) * I) = 1 := by
    push_cast; exact Complex.exp_two_pi_mul_I
  simp only [dRad, ← show coefRad G k r = coefOf k (deriv G r) from rfl, he, one_mul, mul_one, ofReal_zero, zero_mul, Complex.exp_zero,
    hW0, star_one] at hint
  rw [← holA, ← holV] at hint
  rw [← hint]; abel

/-- `∂_r H_r = -(ik²/2) R_r^* V_r A_r R_r`. -/
theorem hasDerivWithinAt_holH (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1) :
    HasDerivWithinAt (holH G k)
      ((-(I * k ^ 2 / 2)) • (star (holR G k r) * holV G k r * holA G k r * holR G k r))
      (Ico 0 1) r := by
  have hR := (holR_spec k isOpen_ball hG seg_mem_ball).2 r hr
  have hV := hasDerivWithinAt_holV k hG hr
  rw [integral_curvature k hG hr] at hV
  have hVu := (holU_mem_unitary k isOpen_ball hG seg_mem_ball hr (circ_mem_ball hr)).1
  have hVV : ∀ X : L2N →L[ℂ] L2N, holV G k r * (star (holV G k r) * X) = X := fun X => by
    rw [← mul_assoc, Unitary.mul_star_self_of_mem hVu, one_mul]
  have hd := ((hR.star).mul hV).mul hR
  convert hd using 1
  rw [star_mul, star_coefRad]
  simp only [Pi.mul_apply, add_mul, sub_mul, mul_sub, mul_assoc, neg_mul, mul_neg, hVV, mul_smul_comm,
    smul_mul_assoc,
    neg_smul]
  abel

/-- `-i U_r^* ∂_r U_r = L_{r,k}` on `[0, b]`, for `0 < b < 1`. -/
theorem generator_holU (hG : DifferentiableOn ℂ G (ball 0 1)) {b : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1) {r : ℝ} (hr : r ∈ Icc 0 b) (hA : IsSelfAdjoint (holA G k r)) :
    generator (holU G k) b r = holL G k r := by
  have hsub : Icc 0 b ⊆ Ico (0 : ℝ) 1 := Icc_subset_Ico_right hb1
  have hr' := hsub hr
  have hH := (hasDerivWithinAt_holH k hG hr').mono hsub
  have hU : HasDerivWithinAt (holU G k) (star ((-(I * k ^ 2 / 2)) •
      (star (holR G k r) * holV G k r * holA G k r * holR G k r))) (Icc 0 b) r := hH.star
  have hRu := holR_mem_unitary k isOpen_ball hG seg_mem_ball hr'
  have hRR : ∀ X : L2N →L[ℂ] L2N, holR G k r * (star (holR G k r) * X) = X := fun X => by
    rw [← mul_assoc, Unitary.mul_star_self_of_mem hRu, one_mul]
  unfold generator
  rw [hU.derivWithin (uniqueDiffOn_Icc hb0 r hr), holL_eq, holU, star_star]
  simp only [holH, star_mul, star_star, star_smul, hA.star_eq, mul_smul_comm,
    smul_smul, mul_assoc, hRR]
  congr 1
  simp only [Complex.star_def, map_neg, map_div₀, map_mul, conj_I, map_pow, conj_ofReal,
    map_ofNat]
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- Continuity of `r ↦ A_r` in operator norm on `[0, 1)`. -/
lemma continuousOn_holA (hG : DifferentiableOn ℂ G (ball 0 1)) :
    ContinuousOn (holA G k) (Ico 0 1) := by
  intro r₀ hr₀
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨η, hη, h⟩ := norm_holA_sub_le k hG hr₀ (half_pos hε)
  refine ⟨η, hη, fun s hs hsη => ?_⟩
  rw [dist_eq_norm]
  rw [Real.dist_eq] at hsη
  exact lt_of_le_of_lt (h s hs hsη k (by simpa using hη)) (half_lt_self hε)

/-- The derivative of `r ↦ U_r`. -/
lemma hasDerivWithinAt_holU (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1) :
    HasDerivWithinAt (holU G k) (star ((-(I * k ^ 2 / 2)) •
      (star (holR G k r) * holV G k r * holA G k r * holR G k r))) (Ico 0 1) r :=
  (hasDerivWithinAt_holH k hG hr).star

/-- `r ↦ U_r` is continuously differentiable in operator
norm on `[0, b]` for `0 < b < 1`. -/
theorem contDiffOn_holU (hG : DifferentiableOn ℂ G (ball 0 1)) {b : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1) : ContDiffOn ℝ 1 (holU G k) (Icc 0 b) := by
  have hsub : Icc 0 b ⊆ Ico (0 : ℝ) 1 := Icc_subset_Ico_right hb1
  have hd : ∀ r ∈ Icc 0 b, HasDerivWithinAt (holU G k) (star ((-(I * k ^ 2 / 2)) •
      (star (holR G k r) * holV G k r * holA G k r * holR G k r))) (Icc 0 b) r :=
    fun r hr => (hasDerivWithinAt_holU k hG (hsub hr)).mono hsub
  have hRc : ContinuousOn (holR G k) (Ico 0 1) := fun r hr =>
    ((holR_spec k isOpen_ball hG seg_mem_ball).2 r hr).continuousWithinAt
  have hVc : ContinuousOn (holV G k) (Ico 0 1) := fun r hr =>
    (hasDerivWithinAt_holV k hG hr).continuousWithinAt
  have hAc := continuousOn_holA k hG
  have hcont : ContinuousOn (fun r => star ((-(I * k ^ 2 / 2)) •
      (star (holR G k r) * holV G k r * holA G k r * holR G k r))) (Icc 0 b) := by
    refine continuous_star.comp_continuousOn (ContinuousOn.const_smul ?_ _)
    exact ((((continuous_star.comp_continuousOn hRc).mul hVc).mul hAc).mul hRc).mono hsub
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl,
    contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hb0)]
  refine ⟨fun r hr => (hd r hr).differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  exact hcont.congr fun r hr => (hd r hr).derivWithin (uniqueDiffOn_Icc hb0 r hr)

end

section

/-! ## Trace-norm continuity of the generator -/

open scoped InnerProductSpace
open MeasureTheory Set Real Metric Complex Filter Topology

/-- The rank-one operator `a ⊗ a : x ↦ ⟪a, x⟫ a`. -/
def rankOne (a : L2N) : L2N →L[ℂ] L2N := (innerSL ℂ a).smulRight a

lemma rankOne_apply (a x : L2N) : rankOne a x = ⟪a, x⟫_ℂ • a := rfl

/-- Cauchy–Schwarz and Bessel: `|Σ ωᵢ ⟪uᵢ, p⟫ ⟪q, vᵢ⟫| ≤ ‖p‖ ‖q‖` for orthonormal families and
`|ωᵢ| ≤ 1`. -/
lemma norm_sum_inner_mul_inner_le {n : ℕ} {u v : Fin n → L2N} (hu : Orthonormal ℂ u)
    (hv : Orthonormal ℂ v) (ω : Fin n → ℂ) (hω : ∀ i, ‖ω i‖ ≤ 1) (p q : L2N) :
    ‖∑ i, ω i * (⟪u i, p⟫_ℂ * ⟪q, v i⟫_ℂ)‖ ≤ ‖p‖ * ‖q‖ := by
  have h1 : ‖∑ i, ω i * (⟪u i, p⟫_ℂ * ⟪q, v i⟫_ℂ)‖ ≤ ∑ i, ‖⟪u i, p⟫_ℂ‖ * ‖⟪v i, q⟫_ℂ‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, norm_mul, ← inner_conj_symm (v i), Complex.norm_conj]
    exact mul_le_of_le_one_left (by positivity) (hω i)
  have hp := hu.sum_inner_products_le (s := Finset.univ) p
  have hq := hv.sum_inner_products_le (s := Finset.univ) q
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖⟪u i, p⟫_ℂ‖)
    (fun i => ‖⟪v i, q⟫_ℂ‖)
  have h2 : ∑ i, ‖⟪u i, p⟫_ℂ‖ * ‖⟪v i, q⟫_ℂ‖ ≤ ‖p‖ * ‖q‖ := by
    have hnn : 0 ≤ ∑ i, ‖⟪u i, p⟫_ℂ‖ * ‖⟪v i, q⟫_ℂ‖ := by positivity
    have : (∑ i, ‖⟪u i, p⟫_ℂ‖ * ‖⟪v i, q⟫_ℂ‖) ^ 2 ≤ (‖p‖ * ‖q‖) ^ 2 := by
      rw [mul_pow]
      exact hcs.trans (mul_le_mul hp hq (by positivity) (by positivity))
    exact (pow_le_pow_iff_left₀ hnn (by positivity) two_ne_zero).1 this
  exact h1.trans h2

/-- Phases realizing `Σ ‖zᵢ‖` as a linear combination. -/
lemma exists_phase_sum {n : ℕ} (z : Fin n → ℂ) :
    ∃ ω : Fin n → ℂ, (∀ i, ‖ω i‖ ≤ 1) ∧ ∑ i, ω i * z i = ((∑ i, ‖z i‖ : ℝ) : ℂ) := by
  classical
  refine ⟨fun i => if z i = 0 then 0 else (starRingEnd ℂ (z i)) / (‖z i‖ : ℂ), fun i => ?_, ?_⟩
  · dsimp only
    split_ifs with h
    · simp
    · rw [norm_div, Complex.norm_conj, Complex.norm_real, norm_norm,
        div_self (norm_ne_zero_iff.2 h)]
  · push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · simp [h]
    · have hn : (‖z i‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h
      rw [div_mul_eq_mul_div, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      field_simp

variable {G : ℂ → ℂ} (k : ℝ)

lemma norm_unitary_apply {U : L2N →L[ℂ] L2N} (hU : U ∈ unitary (L2N →L[ℂ] L2N)) (x : L2N) :
    ‖U x‖ = ‖x‖ := by
  have h : ‖U x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ),
      ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.mul_apply,
      ← ContinuousLinearMap.star_eq_adjoint, Unitary.star_mul_self_of_mem hU,
      ContinuousLinearMap.one_apply]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

lemma norm_e0 : ‖e0‖ = 1 := by simp [e0, lp.norm_single]

/-- The unit vectors `a_r(θ) = M_r W_r(θ)^* e₀`. -/
def holVec (G : ℂ → ℂ) (k r θ : ℝ) : L2N :=
  (holH G k r * star (holR G k r)) (star (holW G k r θ) e0)

lemma norm_holVec (hG : DifferentiableOn ℂ G (ball 0 1)) {r θ : ℝ} (hr : r ∈ Ico (0 : ℝ) 1)
    (hθ : θ ∈ Icc 0 (2 * π)) : ‖holVec G k r θ‖ = 1 := by
  rw [holVec, norm_unitary_apply (holM_mem_unitary k hG hr),
    norm_unitary_apply (Unitary.star_mem
      (holW_mem_unitary k isOpen_ball hG (circ_mem_ball hr) hθ)), norm_e0]

lemma conj_projE0_eq_rankOne (M W : L2N →L[ℂ] L2N) :
    M * (star W * projE0 * W) * star M = rankOne (M (star W e0)) := by
  ext1 x
  simp only [ContinuousLinearMap.mul_apply, rankOne_apply, projE0,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, map_smul,
    ContinuousLinearMap.star_eq_adjoint]
  congr 1
  rw [← ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]

/-- `L_{r,k} = (k²/2) ∫₀^{2π} J(r,θ) a_r(θ) ⊗ a_r(θ) dθ`. -/
lemma holL_eq_integral (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1) :
    holL G k r = ((k ^ 2 / 2 : ℝ) : ℂ) •
      ∫ θ in (0 : ℝ)..(2 * π), ((jac G r θ : ℝ) : ℂ) • rankOne (holVec G k r θ) := by
  set M := holH G k r * star (holR G k r) with hM
  let Φ : (L2N →L[ℂ] L2N) →L[ℝ] (L2N →L[ℂ] L2N) :=
    ((ContinuousLinearMap.mul ℝ (L2N →L[ℂ] L2N)).flip (star M)).comp
      (ContinuousLinearMap.mul ℝ (L2N →L[ℂ] L2N) M)
  have hΦ : ∀ X, Φ X = M * X * star M := fun X => rfl
  have hint : IntervalIntegrable (fun θ => ((jac G r θ : ℝ) : ℂ) •
      (star (holW G k r θ) * projE0 * holW G k r θ)) volume 0 (2 * π) :=
    (continuousOn_holA_integrand k hG hr).intervalIntegrable_of_Icc two_pi_pos.le
  rw [holL_eq, ← hM, holA, ← hΦ, ← Φ.intervalIntegral_comp_comm hint]
  congr 2
  funext θ
  rw [hΦ, mul_smul_comm, smul_mul_assoc, conj_projE0_eq_rankOne]
  rfl

lemma continuousOn_holVec (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1) : ContinuousOn (holVec G k r) (Icc 0 (2 * π)) := by
  have hW := continuousOn_holW k hG hr
  have h1 : ContinuousOn (fun θ => star (holW G k r θ) e0) (Icc 0 (2 * π)) :=
    (continuous_star.comp_continuousOn hW).clm_apply continuousOn_const
  exact (holH G k r * star (holR G k r)).continuous.comp_continuousOn h1

/-- The functional `T ↦ Σ ωᵢ ⟪uᵢ, T vᵢ⟫`. -/
noncomputable def pairFun {n : ℕ} (u v : Fin n → L2N) (ω : Fin n → ℂ) : (L2N →L[ℂ] L2N) →L[ℂ] ℂ :=
  ∑ i, ω i • ((innerSL ℂ (u i)).comp (ContinuousLinearMap.apply ℂ L2N (v i)))

lemma pairFun_apply {n : ℕ} (u v : Fin n → L2N) (ω : Fin n → ℂ) (T : L2N →L[ℂ] L2N) :
    pairFun u v ω T = ∑ i, ω i * ⟪u i, T (v i)⟫_ℂ := by
  simp [pairFun, ContinuousLinearMap.sum_apply]

lemma pairFun_rankOne {n : ℕ} (u v : Fin n → L2N) (ω : Fin n → ℂ) (a : L2N) :
    pairFun u v ω (rankOne a) = ∑ i, ω i * (⟪u i, a⟫_ℂ * ⟪a, v i⟫_ℂ) := by
  rw [pairFun_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rankOne_apply, inner_smul_right, mul_comm ⟪a, v i⟫_ℂ]

lemma norm_pairFun_rankOne_sub_le {n : ℕ} {u v : Fin n → L2N} (hu : Orthonormal ℂ u)
    (hv : Orthonormal ℂ v) {ω : Fin n → ℂ} (hω : ∀ i, ‖ω i‖ ≤ 1) (a b : L2N) :
    ‖pairFun u v ω (rankOne a) - pairFun u v ω (rankOne b)‖ ≤ ‖a - b‖ * ‖a‖ + ‖b‖ * ‖a - b‖ := by
  have h : pairFun u v ω (rankOne a) - pairFun u v ω (rankOne b) =
      ∑ i, ω i * (⟪u i, a - b⟫_ℂ * ⟪a, v i⟫_ℂ) + ∑ i, ω i * (⟪u i, b⟫_ℂ * ⟪a - b, v i⟫_ℂ) := by
    rw [pairFun_rankOne, pairFun_rankOne, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [inner_sub_left, inner_sub_right]
    ring
  rw [h]
  exact (norm_add_le _ _).trans (add_le_add (norm_sum_inner_mul_inner_le hu hv ω hω _ _)
    (norm_sum_inner_mul_inner_le hu hv ω hω _ _))

lemma continuous_rankOne : Continuous rankOne := by
  unfold rankOne
  fun_prop

/-- Quantitative trace-norm estimate for `L_s - L_r`. -/
lemma traceNorm_holL_sub_le (hG : DifferentiableOn ℂ G (ball 0 1)) {r s : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1) (hs : s ∈ Ico (0 : ℝ) 1) {δ₁ δ₂ K : ℝ}
    (hJ : ∀ θ ∈ Icc 0 (2 * π), |jac G s θ - jac G r θ| ≤ δ₁)
    (ha : ∀ θ ∈ Icc 0 (2 * π), ‖holVec G k s θ - holVec G k r θ‖ ≤ δ₂)
    (hK : ∀ θ ∈ Icc 0 (2 * π), |jac G r θ| ≤ K) :
    traceNorm (holL G k s - holL G k r) ≤
      ENNReal.ofReal (k ^ 2 / 2 * (2 * π) * (δ₁ + 2 * K * δ₂)) := by
  unfold traceNorm
  refine iSup_le fun n => iSup_le fun u => iSup_le fun v => iSup_le fun hu => iSup_le fun hv => ?_
  simp_rw [← ofReal_norm_eq_enorm]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  obtain ⟨ω, hω, hsum⟩ := exists_phase_sum fun i => ⟪u i, (holL G k s - holL G k r) (v i)⟫_ℂ
  set Λ := pairFun u v ω with hΛ
  have hΛL : ∀ t ∈ Ico (0 : ℝ) 1, Λ (holL G k t) = ((k ^ 2 / 2 : ℝ) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * π), ((jac G t θ : ℝ) : ℂ) * Λ (rankOne (holVec G k t θ)) := by
    intro t ht
    have hint : IntervalIntegrable (fun θ => ((jac G t θ : ℝ) : ℂ) • rankOne (holVec G k t θ))
        volume 0 (2 * π) := by
      refine (ContinuousOn.smul (continuous_ofReal.comp (continuous_jac hG ht)).continuousOn
        ?_).intervalIntegrable_of_Icc two_pi_pos.le
      exact continuous_rankOne.comp_continuousOn (continuousOn_holVec k hG ht)
    rw [holL_eq_integral k hG ht, map_smul, smul_eq_mul]
    change _ * (Λ.restrictScalars ℝ) _ = _
    rw [← (Λ.restrictScalars ℝ).intervalIntegral_comp_comm hint]
    congr 1
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp
  have hcont : ∀ t ∈ Ico (0 : ℝ) 1, ContinuousOn (fun θ => ((jac G t θ : ℝ) : ℂ) *
      Λ (rankOne (holVec G k t θ))) (Icc 0 (2 * π)) := fun t ht =>
    (continuous_ofReal.comp (continuous_jac hG ht)).continuousOn.mul
      (Λ.continuous.comp_continuousOn (continuous_rankOne.comp_continuousOn
        (continuousOn_holVec k hG ht)))
  have hP1 : ∀ t ∈ Ico (0 : ℝ) 1, ∀ θ ∈ Icc 0 (2 * π), ‖Λ (rankOne (holVec G k t θ))‖ ≤ 1 := by
    intro t ht θ hθ
    rw [hΛ, pairFun_rankOne]
    refine (norm_sum_inner_mul_inner_le hu hv ω hω _ _).trans ?_
    rw [norm_holVec k hG ht hθ, mul_one]
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 ⟨le_rfl, two_pi_pos.le⟩)
  have hpt : ∀ θ ∈ Icc 0 (2 * π),
      ‖((jac G s θ : ℝ) : ℂ) * Λ (rankOne (holVec G k s θ)) -
        ((jac G r θ : ℝ) : ℂ) * Λ (rankOne (holVec G k r θ))‖ ≤ δ₁ + 2 * K * δ₂ := by
    intro θ hθ
    have heq : ((jac G s θ : ℝ) : ℂ) * Λ (rankOne (holVec G k s θ)) -
        ((jac G r θ : ℝ) : ℂ) * Λ (rankOne (holVec G k r θ)) =
        ((jac G s θ - jac G r θ : ℝ) : ℂ) * Λ (rankOne (holVec G k s θ)) +
        ((jac G r θ : ℝ) : ℂ) * (Λ (rankOne (holVec G k s θ)) - Λ (rankOne (holVec G k r θ))) := by
      push_cast; ring
    have hdiff : ‖Λ (rankOne (holVec G k s θ)) - Λ (rankOne (holVec G k r θ))‖ ≤ 2 * δ₂ := by
      rw [hΛ]
      refine (norm_pairFun_rankOne_sub_le hu hv hω _ _).trans ?_
      rw [norm_holVec k hG hs hθ, norm_holVec k hG hr hθ]
      linarith [ha θ hθ]
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    have e1 : |jac G s θ - jac G r θ| * ‖Λ (rankOne (holVec G k s θ))‖ ≤ δ₁ * 1 :=
      mul_le_mul (hJ θ hθ) (hP1 s hs θ hθ) (norm_nonneg _) ((abs_nonneg _).trans (hJ θ hθ))
    have e2 : |jac G r θ| * ‖Λ (rankOne (holVec G k s θ)) - Λ (rankOne (holVec G k r θ))‖ ≤
        K * (2 * δ₂) := mul_le_mul (hK θ hθ) hdiff (norm_nonneg _) hK0
    linarith
  have hnorm : ∑ i, ‖⟪u i, (holL G k s - holL G k r) (v i)⟫_ℂ‖ =
      ‖Λ (holL G k s - holL G k r)‖ := by
    rw [hΛ, pairFun_apply, hsum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)]
  rw [hnorm, map_sub, hΛL s hs, hΛL r hr, ← mul_sub,
    ← intervalIntegral.integral_sub ((hcont s hs).intervalIntegrable_of_Icc two_pi_pos.le)
      ((hcont r hr).intervalIntegrable_of_Icc two_pi_pos.le), norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => hpt θ ?_).trans ?_
  · rw [uIoc_of_le two_pi_pos.le] at hθ
    exact Ioc_subset_Icc_self hθ
  · rw [sub_zero, abs_of_pos two_pi_pos, mul_comm]

lemma continuousOn_holM (hG : DifferentiableOn ℂ G (ball 0 1)) :
    ContinuousOn (fun r => holH G k r * star (holR G k r)) (Ico 0 1) := by
  have hRc : ContinuousOn (holR G k) (Ico 0 1) := fun r hr =>
    ((holR_spec k isOpen_ball hG seg_mem_ball).2 r hr).continuousWithinAt
  have hHc : ContinuousOn (holH G k) (Ico 0 1) := fun r hr =>
    (hasDerivWithinAt_holH k hG hr).continuousWithinAt
  exact hHc.mul (continuous_star.comp_continuousOn hRc)

/-- Uniform convergence `a_s(θ) → a_r(θ)` as `s → r`. -/
lemma holVec_unif (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ s ∈ Ico (0 : ℝ) 1, |s - r| < η → ∀ θ ∈ Icc 0 (2 * π),
      ‖holVec G k s θ - holVec G k r θ‖ ≤ ε := by
  have hpi := Real.pi_pos
  -- continuity of `M`
  have hM := continuousOn_holM k hG r hr
  rw [Metric.continuousWithinAt_iff] at hM
  obtain ⟨η₁, hη₁, h₁⟩ := hM (ε / 2) (half_pos hε)
  -- uniform continuity of the angular coefficients
  set b := (1 + r) / 2 with hbdef
  have hb : b < 1 := by rw [hbdef]; linarith [hr.2]
  have hrb : r ∈ Icc 0 b := ⟨hr.1, by rw [hbdef]; linarith [hr.2]⟩
  have hbr : 0 < b - r := by rw [hbdef]; linarith [hr.2]
  obtain ⟨η₂, hη₂, h₂⟩ := uniform_in_snd ((continuousOn_coefAng_uncurry k hG hb).mono
    (prod_mono_right (subset_univ (Icc 0 (2 * π))))) hrb
    (by positivity : 0 < ε / (4 * π + 1))
  refine ⟨min (min η₁ η₂) (b - r), lt_min (lt_min hη₁ hη₂) hbr, fun s hs hsr θ hθ => ?_⟩
  have hs1 : |s - r| < η₁ := lt_of_lt_of_le hsr ((min_le_left _ _).trans (min_le_left _ _))
  have hs2 : |s - r| < η₂ := lt_of_lt_of_le hsr ((min_le_left _ _).trans (min_le_right _ _))
  have hs3 : |s - r| < b - r := lt_of_lt_of_le hsr (min_le_right _ _)
  have hsb : s ∈ Icc 0 b := ⟨hs.1, by rw [abs_lt] at hs3; linarith [hs3.2]⟩
  have hMs : ‖holH G k s * star (holR G k s) - holH G k r * star (holR G k r)‖ < ε / 2 := by
    have := h₁ hs (by rw [Real.dist_eq]; exact hs1)
    rwa [dist_eq_norm] at this
  have hW : ‖holW G k s θ - holW G k r θ‖ ≤ ε / 2 := by
    refine (norm_holW_sub_le hG hr hs (ε := ε / (4 * π + 1)) (fun t ht => ?_) hθ).trans ?_
    · have := h₂ s hsb hs2 t ht
      rw [dist_eq_norm] at this
      exact this.le
    · calc ε / (4 * π + 1) * θ ≤ ε / (4 * π + 1) * (2 * π) := by gcongr; exact hθ.2
        _ ≤ ε / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
          nlinarith
  have hWs := holW_mem_unitary k isOpen_ball hG (circ_mem_ball hs) hθ
  have hMr := holM_mem_unitary k hG hr
  have heq : holVec G k s θ - holVec G k r θ =
      (holH G k s * star (holR G k s) - holH G k r * star (holR G k r)) (star (holW G k s θ) e0) +
      (holH G k r * star (holR G k r)) ((star (holW G k s θ) - star (holW G k r θ)) e0) := by
    simp only [holVec, ContinuousLinearMap.sub_apply, map_sub]
    abel
  rw [heq]
  refine (norm_add_le _ _).trans ?_
  rw [norm_unitary_apply hMr]
  have e1 : ‖(holH G k s * star (holR G k s) - holH G k r * star (holR G k r))
      (star (holW G k s θ) e0)‖ ≤ ε / 2 := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [norm_unitary_apply (Unitary.star_mem hWs), norm_e0, mul_one]
    exact hMs.le
  have e2 : ‖(star (holW G k s θ) - star (holW G k r θ)) e0‖ ≤ ε / 2 := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [norm_e0, mul_one, ← star_sub, norm_star]
    exact hW
  linarith

/-- `r ↦ L_{r,k}` is continuous in trace norm on `[0, 1)`. -/
theorem tendsto_traceNorm_holL (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1) :
    Tendsto (fun s => traceNorm (holL G k s - holL G k r)) (𝓝[Ico 0 1] r) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεt
  · exact Eventually.of_forall fun _ => le_top
  have he : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
  set e := ε.toReal with hedef
  have hpi := Real.pi_pos
  obtain ⟨MJ, hMJ⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn
    (continuous_jac hG hr).continuousOn
  set K := |MJ| with hK
  have hK0 : 0 ≤ K := abs_nonneg _
  set C := k ^ 2 * π with hC
  have hC0 : 0 ≤ C := by positivity
  set δ₁ := e / (2 * (C + 1)) with hδ₁
  set δ₂ := e / (4 * (K + 1) * (C + 1)) with hδ₂
  have hδ₁pos : 0 < δ₁ := by positivity
  have hδ₂pos : 0 < δ₂ := by positivity
  set b := (1 + r) / 2 with hbdef
  have hb : b < 1 := by rw [hbdef]; linarith [hr.2]
  have hrb : r ∈ Icc 0 b := ⟨hr.1, by rw [hbdef]; linarith [hr.2]⟩
  have hbr : 0 < b - r := by rw [hbdef]; linarith [hr.2]
  obtain ⟨η₁, hη₁, h₁⟩ := uniform_in_snd ((continuousOn_jac_uncurry hG hb).mono
    (prod_mono_right (subset_univ (Icc 0 (2 * π))))) hrb hδ₁pos
  obtain ⟨η₂, hη₂, h₂⟩ := holVec_unif k hG hr hδ₂pos
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds
    (ball_mem_nhds r (lt_min (lt_min hη₁ hη₂) hbr))] with s hs hsb
  rw [mem_ball, Real.dist_eq] at hsb
  have hs1 : |s - r| < η₁ := lt_of_lt_of_le hsb ((min_le_left _ _).trans (min_le_left _ _))
  have hs2 : |s - r| < η₂ := lt_of_lt_of_le hsb ((min_le_left _ _).trans (min_le_right _ _))
  have hs3 : |s - r| < b - r := lt_of_lt_of_le hsb (min_le_right _ _)
  have hsb' : s ∈ Icc 0 b := ⟨hs.1, by rw [abs_lt] at hs3; linarith [hs3.2]⟩
  refine (traceNorm_holL_sub_le k hG hr hs (δ₁ := δ₁) (δ₂ := δ₂) (K := K)
    (fun θ hθ => ?_) (h₂ s hs hs2) (fun θ hθ => ?_)).trans ?_
  · have := h₁ s hsb' hs1 θ hθ
    rw [Real.dist_eq] at this
    exact this.le
  · have := hMJ θ hθ
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_abs_self _)
  · rw [← ENNReal.ofReal_toReal hεt]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← hedef]
    have e1 : 2 * K * δ₂ ≤ e / (2 * (C + 1)) := by
      rw [hδ₂, show 2 * K * (e / (4 * (K + 1) * (C + 1))) =
        e / (2 * (C + 1)) * (K / (K + 1)) by field_simp; ring]
      exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).2 (by linarith))
    calc k ^ 2 / 2 * (2 * π) * (δ₁ + 2 * K * δ₂) = C * (δ₁ + 2 * K * δ₂) := by rw [hC]; ring
      _ ≤ C * (e / (2 * (C + 1)) + e / (2 * (C + 1))) := by gcongr
      _ = e * (C / (C + 1)) := by field_simp; ring
      _ ≤ e := mul_le_of_le_one_right he.le ((div_le_one (by positivity)).2 (by linarith))

end

section

/-! ## The boundary transport is an admissible positive unitary path -/

open scoped InnerProductSpace
open MeasureTheory Set Real Metric Complex

variable (k : ℝ)

lemma inner_projE0_self (x : L2N) : ⟪x, projE0 x⟫_ℂ = ((‖x 0‖ ^ 2 : ℝ) : ℂ) := by
  simp only [projE0, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_right,
    inner_e0]
  rw [← inner_conj_symm, inner_e0, Complex.mul_conj']
  simp [← Complex.ofReal_pow]

/-- The quadratic form of `A_r` is real: `⟪z, A_r z⟫ = ∫₀^{2π} J(r,θ) |(W_r(θ) z)₀|² dθ`. -/
lemma inner_holA_self {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1) (z : L2N) :
    ⟪z, holA G k r z⟫_ℂ =
      ((∫ θ in (0 : ℝ)..(2 * π), jac G r θ * ‖holW G k r θ z 0‖ ^ 2 : ℝ) : ℂ) := by
  let L : (L2N →L[ℂ] L2N) →L[ℝ] ℂ :=
    ((innerSL ℂ z).comp (ContinuousLinearMap.apply ℂ L2N z)).restrictScalars ℝ
  have hL : ∀ T : L2N →L[ℂ] L2N, L T = ⟪z, T z⟫_ℂ := fun T => rfl
  have hint : IntervalIntegrable (fun θ => ((jac G r θ : ℝ) : ℂ) •
      (star (holW G k r θ) * projE0 * holW G k r θ)) volume 0 (2 * π) :=
    (continuousOn_holA_integrand k hG hr).intervalIntegrable_of_Icc (by positivity)
  rw [← hL, holA, ← L.intervalIntegral_comp_comm hint, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [hL, ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply, inner_smul_right,
    ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.adjoint_inner_right, inner_projE0_self]
  push_cast; ring

/-- `A_r` is a positive operator. -/
lemma holA_isPositive {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1) : (holA G k r).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  have h : ⟪holA G k r x, x⟫_ℂ =
      ((∫ θ in (0 : ℝ)..(2 * π), jac G r θ * ‖holW G k r θ x 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [← inner_conj_symm, inner_holA_self k hG hr, Complex.conj_ofReal]
  rw [h, RCLike.re_to_complex, Complex.ofReal_re]
  refine ⟨rfl, intervalIntegral.integral_nonneg (by positivity) fun θ _ => ?_⟩
  exact mul_nonneg (jac_nonneg hr.1 θ) (by positivity)

open scoped ComplexOrder in
/-- `L_{r,k}` is a positive operator. -/
lemma holL_isPositive {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1) : (holL G k r).IsPositive := by
  rw [holL_eq]
  refine ContinuousLinearMap.IsPositive.smul_of_nonneg ?_ (Complex.zero_le_real.2 (by positivity))
  have := (holA_isPositive k hG hr).conj_adjoint (holH G k r * star (holR G k r))
  simpa [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def] using this

/-- `L_{r,k}` is positive and trace class. -/
lemma holL_isPosTraceClass {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (ball 0 1)) {r : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1) : IsPosTraceClass (holL G k r) := by
  refine ⟨holL_isPositive k hG hr, ?_⟩
  rw [posTrace_holL k hG hr]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- For `F` holomorphic and injective on the unit disk, `k > 0` and
`0 < b < 1`: the path `r ↦ U_{r,k}` is an admissible positive unitary path on `[0, b]` with
generator `L_{r,k}`, its integrated trace is `∫₀ᵇ tr L_{r,k} dr = (k²/2) |F(b𝔻)|`, and all
spectral tails `τ_m(L_{r,k})`, `m ≥ 1`, `r > 0`, are positive. -/
theorem holonomy_path {F : ℂ → ℂ} (hG : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) (hk : 0 < k) {b : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1) :
    IsAdmissiblePath b (holU F k) ∧
      (∀ r ∈ Icc 0 b, generator (holU F k) b r = holL F k r) ∧
      (∫⁻ r in Icc 0 b, posTrace (holL F k r)) =
        ENNReal.ofReal (k ^ 2 / 2) * volume (F '' ball 0 b) ∧
      ∀ m : ℕ, 1 ≤ m → ∀ r ∈ Ioc 0 b, 0 < spectralTail m (holL F k r) := by
  have hsub : Icc 0 b ⊆ Ico (0 : ℝ) 1 := Icc_subset_Ico_right hb1
  have hgen : ∀ r ∈ Icc 0 b, generator (holU F k) b r = holL F k r := fun r hr =>
    generator_holU k hG hb0 hb1 hr (holA_isPositive k hG (hsub hr)).isSelfAdjoint
  refine ⟨⟨hb0, fun t ht => ?_, ?_, ?_, ?_, ?_, fun t ht v hv => ?_⟩, hgen,
    lintegral_posTrace_holL k hG hinj hb1, fun m _ r hr =>
    spectralTail_holL_pos k hG hinj hk m ⟨hr.1, hr.2.trans_lt hb1⟩⟩
  · exact (holU_mem_unitary k isOpen_ball hG seg_mem_ball (hsub ht)
      (circ_mem_ball (hsub ht))).2.2
  · exact (holU_zero k isOpen_ball hG seg_mem_ball).2.2
  · exact contDiffOn_holU k hG hb0 hb1
  · intro t ht
    rw [hgen t ht]
    exact holL_isPosTraceClass k hG (hsub ht)
  · intro t ht
    refine ((tendsto_traceNorm_holL k hG (hsub ht)).mono_left (nhdsWithin_mono _ hsub)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hgen s hs, hgen t ht]
  · rw [hgen t (Ioc_subset_Icc_self ht)]
    exact re_inner_holL_pos k hG hinj hk ⟨ht.1, ht.2.trans_lt hb1⟩ hv

end

section

/-! ## The Helmholtz equation -/

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory Set Real Metric Complex Filter Topology

/-- `φ` solves the Helmholtz equation `Δφ + k²φ = 0` (classically) on `Ω`. -/
def IsHelmholtzOn (k : ℝ) (φ : ℂ → ℂ) (Ω : Set ℂ) : Prop :=
  ContDiffOn ℝ 2 φ Ω ∧ ∀ z ∈ Ω, Laplacian.laplacian φ z + (k : ℂ) ^ 2 * φ z = 0

lemma IsHelmholtzOn.mono {k : ℝ} {φ : ℂ → ℂ} {Ω Ω' : Set ℂ} (h : IsHelmholtzOn k φ Ω)
    (hΩ : Ω' ⊆ Ω) : IsHelmholtzOn k φ Ω' :=
  ⟨h.1.mono hΩ, fun z hz => h.2 z (hΩ hz)⟩

lemma contDiff_herglotzWave (k : ℝ) (a : CircFun) : ContDiff ℝ 2 (herglotzWave k a) := by
  have hexp : ContDiff ℝ 2 (fun x : CircFun => NormedSpace.exp x) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  have hD : ContDiff ℝ 2 (herglotzDir k a) := by
    unfold herglotzDir
    exact contDiff_const.mul (hexp.comp (herglotzPhase k).contDiff)
  exact ((circCoeff 0).restrictScalars ℝ).contDiff.comp hD

lemma fderiv_herglotzWave_apply' (k : ℝ) (a : CircFun) (y w : ℂ) :
    fderiv ℝ (herglotzWave k a) y w = circCoeff 0 (herglotzDir k a y * herglotzPhase k w) := by
  rw [(hasFDerivAt_herglotzWave k a y).fderiv]
  rfl

lemma fderiv_fderiv_herglotzWave (k : ℝ) (a : CircFun) (z v w : ℂ) :
    fderiv ℝ (fderiv ℝ (herglotzWave k a)) z v w =
      circCoeff 0 (herglotzDir k a z * herglotzPhase k v * herglotzPhase k w) := by
  have hd : Differentiable ℝ (fderiv ℝ (herglotzWave k a)) :=
      ((contDiff_herglotzWave k a).fderiv_right (m := 1) (by norm_num)).differentiable
        (by norm_num)
  have h1 : fderiv ℝ (fun y => fderiv ℝ (herglotzWave k a) y w) z =
      (fderiv ℝ (fderiv ℝ (herglotzWave k a)) z).flip w := by
    rw [fderiv_clm_apply (hd z) (differentiableAt_const w)]
    simp
  have h2 : HasFDerivAt (fun y => fderiv ℝ (herglotzWave k a) y w)
      (((circCoeff 0).restrictScalars ℝ) ∘L
        ((ContinuousLinearMap.mul ℝ CircFun).flip (herglotzPhase k w)) ∘L
        ((ContinuousLinearMap.mul ℝ CircFun (herglotzDir k a z)) ∘L herglotzPhase k)) z := by
    simp_rw [fderiv_herglotzWave_apply']
    exact ((circCoeff 0).restrictScalars ℝ).hasFDerivAt.comp z
      (((ContinuousLinearMap.mul ℝ CircFun).flip (herglotzPhase k w)).hasFDerivAt.comp z
        (hasFDerivAt_herglotzDir k a z))
  have := congrArg (fun L => L v) (h1.symm.trans h2.fderiv)
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.mul_apply', ContinuousLinearMap.coe_restrictScalars'] at this
  exact this

lemma herglotzPhase_sq_add (k : ℝ) :
    herglotzPhase k 1 * herglotzPhase k 1 + herglotzPhase k I * herglotzPhase k I =
      ((-(k : ℂ) ^ 2) • (1 : CircFun)) := by
  have h : (fourier (-1) : CircFun) * fourier 1 = 1 := by
    ext x
    rw [ContinuousMap.mul_apply, ← fourier_add]
    simp
  simp only [herglotzPhase_apply, map_one, Complex.conj_I, one_smul, smul_mul_smul_comm]
  rw [← smul_add]
  have e : ((fourier (-1) : CircFun) + fourier 1) * (fourier (-1) + fourier 1) +
      (I • (fourier (-1) : CircFun) + -I • fourier 1) * (I • fourier (-1) + -I • fourier 1) =
      (4 : ℂ) • ((fourier (-1) : CircFun) * fourier 1) := by
    simp only [add_mul, mul_add, smul_mul_smul_comm]
    have hI : I * I = -1 := Complex.I_mul_I
    simp only [hI, neg_mul, mul_neg, neg_neg, neg_smul, one_smul]
    rw [mul_comm (fourier 1 : CircFun) (fourier (-1))]
    module
  rw [e, h, smul_smul]
  congr 1
  linear_combination (↑k ^ 2 : ℂ) * Complex.I_sq

/-- Herglotz wave functions solve the Helmholtz equation `Δu + k²u = 0` on the whole plane. -/
theorem isHelmholtzOn_herglotzWave (k : ℝ) (a : CircFun) (Ω : Set ℂ) :
    IsHelmholtzOn k (herglotzWave k a) Ω := by
  refine ⟨(contDiff_herglotzWave k a).contDiffOn, fun z _ => ?_⟩
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [fderiv_fderiv_herglotzWave, fderiv_fderiv_herglotzWave, ← map_add, mul_assoc, mul_assoc,
    ← mul_add, herglotzPhase_sq_add, mul_smul_comm, mul_one, map_smul, herglotzWave, smul_eq_mul]
  ring

end

section

/-! ## Uniqueness for Bessel's equation -/

open Set Filter Topology

/-- `(f, f')` solves Bessel's equation `f'' + f'/ρ + (k² - n²/ρ²) f = 0` on `(0, R)`. -/
def IsBesselSol (k : ℝ) (n : ℤ) (R : ℝ) (f f' : ℝ → ℂ) : Prop :=
  ∀ ρ ∈ Ioo 0 R, HasDerivAt f (f' ρ) ρ ∧
    HasDerivAt f' (-(f' ρ) / ρ - ((k : ℂ) ^ 2 - (n : ℂ) ^ 2 / (ρ : ℂ) ^ 2) * f ρ) ρ

lemma IsBesselSol.sub_smul {k : ℝ} {n : ℤ} {R : ℝ} {f f' g g' : ℝ → ℂ}
    (hf : IsBesselSol k n R f f') (hg : IsBesselSol k n R g g') (c : ℂ) :
    IsBesselSol k n R (fun ρ => f ρ - c * g ρ) (fun ρ => f' ρ - c * g' ρ) := by
  intro ρ hρ
  obtain ⟨h1, h2⟩ := hf ρ hρ
  obtain ⟨h3, h4⟩ := hg ρ hρ
  refine ⟨h1.sub (h3.const_mul c), ?_⟩
  convert h2.sub (h4.const_mul c) using 1
  ring

/-- The Wronskian of two solutions of Bessel's equation vanishes when both solutions stay bounded
with their derivatives near `0`. -/
lemma bessel_wronskian_eq_zero {k : ℝ} {n : ℤ} {R : ℝ} {f f' g g' : ℝ → ℂ}
    (hf : IsBesselSol k n R f f') (hg : IsBesselSol k n R g g') {M : ℝ}
    (hfM : ∀ ρ ∈ Ioo 0 R, ‖f ρ‖ ≤ M ∧ ‖f' ρ‖ ≤ M) (hgM : ∀ ρ ∈ Ioo 0 R, ‖g ρ‖ ≤ M ∧ ‖g' ρ‖ ≤ M) :
    ∀ ρ ∈ Ioo 0 R, f ρ * g' ρ - f' ρ * g ρ = 0 := by
  set W : ℝ → ℂ := fun ρ => (ρ : ℂ) * (f ρ * g' ρ - f' ρ * g ρ) with hW
  have hWd : ∀ ρ ∈ Ioo 0 R, HasDerivAt W 0 ρ := by
    intro ρ hρ
    obtain ⟨h1, h2⟩ := hf ρ hρ
    obtain ⟨h3, h4⟩ := hg ρ hρ
    have hρ0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.1.ne'
    have := ((hasDerivAt_id ρ).ofReal_comp).mul ((h1.mul h4).sub (h2.mul h3))
    refine this.congr_deriv ?_
    simp only [id, Complex.ofReal_one, Pi.sub_apply, Pi.mul_apply]
    field_simp
    ring
  have hconst : ∀ ρ ∈ Ioo 0 R, ∀ σ ∈ Ioo 0 R, W ρ = W σ := by
    intro ρ hρ σ hσ
    refine (convex_Ioo 0 R).is_const_of_fderivWithin_eq_zero (𝕜 := ℝ)
      (fun x hx => (hWd x hx).differentiableAt.differentiableWithinAt) (fun x hx => ?_) hρ hσ
    rw [fderivWithin_of_isOpen isOpen_Ioo hx, (hWd x hx).hasFDerivAt.fderiv]
    ext; simp
  intro ρ hρ
  have hρ0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.1.ne'
  suffices W ρ = 0 by simpa [hW, hρ0] using this
  have hbound : ∀ σ ∈ Ioo 0 R, ‖W σ‖ ≤ σ * (2 * M ^ 2) := by
    intro σ hσ
    obtain ⟨a1, a2⟩ := hfM σ hσ
    obtain ⟨b1, b2⟩ := hgM σ hσ
    have hM : 0 ≤ M := (norm_nonneg _).trans a1
    simp only [hW, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ.1]
    refine mul_le_mul_of_nonneg_left ?_ hσ.1.le
    calc ‖f σ * g' σ - f' σ * g σ‖ ≤ ‖f σ‖ * ‖g' σ‖ + ‖f' σ‖ * ‖g σ‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ M * M + M * M := by gcongr
      _ = 2 * M ^ 2 := by ring
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  set σ := min (R / 2) (ε / (2 * M ^ 2 + 1)) with hσdef
  have hR : 0 < R := hρ.1.trans hρ.2
  have hσ : σ ∈ Ioo 0 R := ⟨lt_min (by linarith) (by positivity),
    (min_le_left _ _).trans_lt (by linarith)⟩
  rw [hconst ρ hρ σ hσ, zero_add]
  refine (hbound σ hσ).trans ?_
  have h1 : σ ≤ ε / (2 * M ^ 2 + 1) := min_le_right _ _
  have h2 : σ * (2 * M ^ 2) ≤ σ * (2 * M ^ 2 + 1) := by nlinarith [hσ.1]
  calc σ * (2 * M ^ 2) ≤ σ * (2 * M ^ 2 + 1) := h2
    _ ≤ ε / (2 * M ^ 2 + 1) * (2 * M ^ 2 + 1) := by gcongr
    _ = ε := by field_simp

/-- A solution of Bessel's equation with vanishing Cauchy data at an interior point vanishes. -/
lemma bessel_eq_zero_of_cauchy {k : ℝ} {n : ℤ} {R : ℝ} {h h' : ℝ → ℂ}
    (hh : IsBesselSol k n R h h') {ρ₀ : ℝ} (hρ₀ : ρ₀ ∈ Ioo 0 R) (h0 : h ρ₀ = 0)
    (h0' : h' ρ₀ = 0) : ∀ ρ ∈ Ioo 0 R, h ρ = 0 := by
  intro ρ hρ
  set ε := min ρ ρ₀ / 2 with hε
  have hεpos : 0 < ε := by have := lt_min hρ.1 hρ₀.1; positivity
  have hερ : ε < ρ := by have := min_le_left ρ ρ₀; linarith [lt_min hρ.1 hρ₀.1]
  have hερ₀ : ε < ρ₀ := by have := min_le_right ρ ρ₀; linarith [lt_min hρ.1 hρ₀.1]
  set v : ℝ → ℂ × ℂ → ℂ × ℂ := fun t x =>
    (x.2, -x.2 / t - ((k : ℂ) ^ 2 - (n : ℂ) ^ 2 / (t : ℂ) ^ 2) * x.1) with hv
  set K : ℝ := 1 + 1 / ε + (k ^ 2 + (n : ℝ) ^ 2 / ε ^ 2) with hK
  have hK0 : 0 ≤ K := by positivity
  have hlip : ∀ t ∈ Ioo ε R, LipschitzOnWith (Real.toNNReal K) (v t) univ := by
    intro t ht
    have ht0 : 0 < t := hεpos.trans ht.1
    refine LipschitzWith.lipschitzOnWith (LipschitzWith.of_dist_le_mul fun x y => ?_)
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hK0]
    have hx1 : ‖x.1 - y.1‖ ≤ ‖x - y‖ := norm_fst_le (x - y)
    have hx2 : ‖x.2 - y.2‖ ≤ ‖x - y‖ := norm_snd_le (x - y)
    have hq : ‖(k : ℂ) ^ 2 - (n : ℂ) ^ 2 / (t : ℂ) ^ 2‖ ≤ k ^ 2 + (n : ℝ) ^ 2 / ε ^ 2 := by
      refine (norm_sub_le _ _).trans ?_
      have e1 : ‖(n : ℂ) ^ 2 / (t : ℂ) ^ 2‖ = (n : ℝ) ^ 2 / t ^ 2 := by
        rw [norm_div, norm_pow, norm_pow, Complex.norm_intCast, Complex.norm_real,
          Real.norm_eq_abs, sq_abs, sq_abs]
      have e2 : ‖(k : ℂ) ^ 2‖ = k ^ 2 := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [e1, e2]
      gcongr
      exact ht.1.le
    have hinv : 1 / t ≤ 1 / ε := by gcongr; exact ht.1.le
    have hd : v t x - v t y = (x.2 - y.2, -(x.2 - y.2) / t -
        ((k : ℂ) ^ 2 - (n : ℂ) ^ 2 / (t : ℂ) ^ 2) * (x.1 - y.1)) := by
      simp only [hv, Prod.mk_sub_mk]; ring_nf
    rw [hd, Prod.norm_def]
    refine max_le (hx2.trans (le_mul_of_one_le_left (norm_nonneg _) (by
      have : 0 ≤ 1 / ε := by positivity
      have : 0 ≤ k ^ 2 + (n : ℝ) ^ 2 / ε ^ 2 := by positivity
      linarith))) ?_
    calc ‖-(x.2 - y.2) / (t : ℂ) - ((k : ℂ) ^ 2 - (n : ℂ) ^ 2 / (t : ℂ) ^ 2) * (x.1 - y.1)‖
        ≤ ‖x.2 - y.2‖ * (1 / t) +
          ‖(k : ℂ) ^ 2 - (n : ℂ) ^ 2 / (t : ℂ) ^ 2‖ * ‖x.1 - y.1‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0,
            div_eq_mul_one_div]
      _ ≤ ‖x - y‖ * (1 / ε) + (k ^ 2 + (n : ℝ) ^ 2 / ε ^ 2) * ‖x - y‖ := by gcongr
      _ ≤ K * ‖x - y‖ := by rw [hK]; nlinarith [norm_nonneg (x - y)]
  have hsol : ∀ t ∈ Ioo ε R, HasDerivAt (fun t => (h t, h' t)) (v t (h t, h' t)) t ∧
      (h t, h' t) ∈ (univ : Set (ℂ × ℂ)) := by
    intro t ht
    obtain ⟨a, b⟩ := hh t ⟨hεpos.trans ht.1, ht.2⟩
    exact ⟨a.prodMk b, trivial⟩
  have hzero : ∀ t ∈ Ioo ε R, HasDerivAt (fun _ : ℝ => ((0 : ℂ), (0 : ℂ)))
      (v t ((fun _ : ℝ => ((0 : ℂ), (0 : ℂ))) t)) t ∧ ((0 : ℂ), (0 : ℂ)) ∈ (univ : Set (ℂ × ℂ)) := by
    intro t _
    refine ⟨?_, trivial⟩
    simpa [hv] using hasDerivAt_const t ((0 : ℂ), (0 : ℂ))
  have := ODE_solution_unique_of_mem_Ioo hlip ⟨hερ₀, hρ₀.2⟩ hsol hzero (by simp [h0, h0'])
    ⟨hερ, hρ.2⟩
  simpa using congrArg Prod.fst this

/-- **Uniqueness for Bessel's equation.** A solution `f` bounded together with its derivative near
`0` is the multiple `(f ρ₀ / g ρ₀) g` of any other such solution `g` with `g ρ₀ ≠ 0`. -/
theorem bessel_eq_smul {k : ℝ} {n : ℤ} {R : ℝ} {f f' g g' : ℝ → ℂ}
    (hf : IsBesselSol k n R f f') (hg : IsBesselSol k n R g g') {M : ℝ}
    (hfM : ∀ ρ ∈ Ioo 0 R, ‖f ρ‖ ≤ M ∧ ‖f' ρ‖ ≤ M) (hgM : ∀ ρ ∈ Ioo 0 R, ‖g ρ‖ ≤ M ∧ ‖g' ρ‖ ≤ M)
    {ρ₀ : ℝ} (hρ₀ : ρ₀ ∈ Ioo 0 R) (hg0 : g ρ₀ ≠ 0) :
    ∀ ρ ∈ Ioo 0 R, f ρ = f ρ₀ / g ρ₀ * g ρ := by
  set c := f ρ₀ / g ρ₀
  have hW := bessel_wronskian_eq_zero hf hg hfM hgM ρ₀ hρ₀
  have hh := hf.sub_smul hg c
  have h0 : f ρ₀ - c * g ρ₀ = 0 := by simp [c, hg0]
  have h0' : f' ρ₀ - c * g' ρ₀ = 0 := by
    have : (f' ρ₀ - c * g' ρ₀) * g ρ₀ = 0 := by
      simp only [c]; field_simp; linear_combination -hW
    simpa [hg0] using this
  intro ρ hρ
  have := bessel_eq_zero_of_cauchy hh hρ₀ h0 h0' ρ hρ
  linear_combination this

end

section

/-! ## Angular Fourier coefficients of solutions of the Helmholtz equation -/

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory Set Real Metric Complex Filter Topology

/-- Angular Fourier coefficient `a_n(ρ) = (2π)⁻¹ ∫₀^{2π} e^{-inθ} g(ρ e^{iθ}) dθ`. -/
def angCoeff (g : ℂ → ℂ) (n : ℤ) (ρ : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, cexp (-(n * θ * I)) * g (ρ * cexp (θ * I))

/-- The radial derivative of `angCoeff`: `(2π)⁻¹ ∫ e^{-inθ} Dg(ρe^{iθ}) e^{iθ} dθ`. -/
def angCoeffD (g : ℂ → ℂ) (n : ℤ) (ρ : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
    cexp (-(n * θ * I)) * fderiv ℝ g (ρ * cexp (θ * I)) (cexp (θ * I))

/-- The second radial derivative of `angCoeff`. -/
def angCoeffD2 (g : ℂ → ℂ) (n : ℤ) (ρ : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
    cexp (-(n * θ * I)) * fderiv ℝ (fderiv ℝ g) (ρ * cexp (θ * I)) (cexp (θ * I)) (cexp (θ * I))

lemma polar_mem_ball {R ρ : ℝ} (θ : ℝ) (hρ : |ρ| < R) : (ρ : ℂ) * cexp (θ * I) ∈ ball (0 : ℂ) R := by
  simpa [norm_mul, Complex.norm_exp_ofReal_mul_I] using hρ

lemma continuous_polar : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) * cexp (p.2 * I) := by
  fun_prop

/-- Differentiation under the integral sign in a parameter, for integrands with jointly continuous
derivative. -/
lemma hasDerivAt_intervalIntegral_param {G G' : ℝ → ℝ → ℂ} {ρ₀ δ : ℝ} (hδ : 0 < δ)
    (hG : ∀ ρ ∈ Ioo (ρ₀ - δ) (ρ₀ + δ), Continuous (G ρ))
    (hG' : ContinuousOn (fun p : ℝ × ℝ => G' p.1 p.2) (Icc (ρ₀ - δ) (ρ₀ + δ) ×ˢ Icc 0 (2 * π)))
    (hd : ∀ ρ ∈ Ioo (ρ₀ - δ) (ρ₀ + δ), ∀ θ, HasDerivAt (fun ρ => G ρ θ) (G' ρ θ) ρ) :
    HasDerivAt (fun ρ => ∫ θ in (0 : ℝ)..2 * π, G ρ θ) (∫ θ in (0 : ℝ)..2 * π, G' ρ₀ θ) ρ₀ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hG'
  have hρ₀ : ρ₀ ∈ Ioo (ρ₀ - δ) (ρ₀ + δ) := ⟨by linarith, by linarith⟩
  have hsub : uIoc (0 : ℝ) (2 * π) ⊆ Icc 0 (2 * π) := by
    rw [uIoc_of_le (by positivity)]; exact Ioc_subset_Icc_self
  have hcont0 : ContinuousOn (G' ρ₀) (Icc 0 (2 * π)) := by
    have : ContinuousOn (fun θ : ℝ => ((ρ₀, θ) : ℝ × ℝ)) (Icc 0 (2 * π)) := by fun_prop
    refine hG'.comp this fun θ hθ => ⟨⟨by linarith, by linarith⟩, hθ⟩
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ)
    (bound := fun _ => C) (Ioo_mem_nhds hρ₀.1 hρ₀.2) ?_ ((hG ρ₀ hρ₀).intervalIntegrable _ _)
    ((hcont0.mono hsub).aestronglyMeasurable measurableSet_uIoc) ?_ intervalIntegrable_const
    ?_).2
  · filter_upwards [Ioo_mem_nhds hρ₀.1 hρ₀.2] with ρ hρ
    exact (hG ρ hρ).aestronglyMeasurable
  · refine Eventually.of_forall fun θ hθ ρ hρ => hC (ρ, θ) ⟨Ioo_subset_Icc_self hρ, hsub hθ⟩
  · exact Eventually.of_forall fun θ _ ρ hρ => hd ρ hρ θ

/-- Integration by parts against `e^{-inθ}` for a `2π`-periodic function. -/
lemma integral_exp_mul_deriv_of_periodic {F F' : ℝ → ℂ} (hF : ∀ θ, HasDerivAt F (F' θ) θ)
    (hF' : Continuous F') (hper : F (2 * π) = F 0) (n : ℤ) :
    ∫ θ in (0 : ℝ)..2 * π, cexp (-(n * θ * I)) * F' θ =
      n * I * ∫ θ in (0 : ℝ)..2 * π, cexp (-(n * θ * I)) * F θ := by
  have hu : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => cexp (-(n * θ * I)))
      (cexp (-(n * θ * I)) * (-(n * I))) θ := by
    intro θ
    have := (((hasDerivAt_id θ).ofReal_comp).const_mul (n : ℂ)).mul_const I |>.neg |>.cexp
    convert this using 1
    simp
  have hcu : Continuous fun θ : ℝ => cexp (-(n * θ * I)) * (-(n * I)) := by fun_prop
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun θ _ => hu θ) (fun θ _ => hF θ)
    (hcu.intervalIntegrable _ _) (hF'.intervalIntegrable _ _)]
  have h2 : cexp (-(n * ((2 * π : ℝ) : ℂ) * I)) = 1 := by
    have := Complex.exp_int_mul_two_pi_mul_I (-n)
    rw [← this]; congr 1; push_cast; ring
  rw [h2, hper]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul, sub_self,
    zero_sub]
  rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_const_mul]
  congr 1; funext θ; ring

/-- Rotation invariance of the trace of a bilinear form on `ℂ = ℝ²`. -/
lemma bilin_rot_trace (B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ) (e : ℂ) (he : ‖e‖ = 1) :
    B e e + B (e * I) (e * I) = B 1 1 + B I I := by
  have key : ∀ a b : ℝ, B (a • (1 : ℂ) + b • I) (a • (1 : ℂ) + b • I) +
      B ((-b) • (1 : ℂ) + a • I) ((-b) • (1 : ℂ) + a • I) =
        ((a ^ 2 + b ^ 2 : ℝ) : ℂ) * (B 1 1 + B I I) := by
    intro a b
    simp only [map_add, ContinuousLinearMap.map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply]
    simp only [real_smul]
    push_cast; ring
  have h1 : e = e.re • (1 : ℂ) + e.im • I := by apply Complex.ext <;> simp
  have h2 : e * I = (-e.im) • (1 : ℂ) + e.re • I := by apply Complex.ext <;> simp
  have hn : e.re ^ 2 + e.im ^ 2 = 1 := by
    have := Complex.sq_norm e; rw [he, Complex.normSq_apply] at this; nlinarith
  have := key e.re e.im
  rw [← h1, ← h2, hn] at this
  simpa using this

section Helmholtz

variable {k R : ℝ} {ψ : ℂ → ℂ}

lemma IsHelmholtzOn.contDiffOn_fderiv (hψ : IsHelmholtzOn k ψ (ball 0 R)) :
    ContDiffOn ℝ 1 (fderiv ℝ ψ) (ball 0 R) :=
  hψ.1.fderiv_of_isOpen isOpen_ball (by norm_num)

lemma IsHelmholtzOn.hasFDerivAt (hψ : IsHelmholtzOn k ψ (ball 0 R)) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) : HasFDerivAt ψ (fderiv ℝ ψ z) z :=
  ((hψ.1.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds hz)).hasFDerivAt

lemma IsHelmholtzOn.hasFDerivAt_fderiv (hψ : IsHelmholtzOn k ψ (ball 0 R)) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) :
    HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) z) z :=
  ((hψ.contDiffOn_fderiv.differentiableOn (by norm_num)).differentiableAt
    (isOpen_ball.mem_nhds hz)).hasFDerivAt

lemma IsHelmholtzOn.continuousOn (hψ : IsHelmholtzOn k ψ (ball 0 R)) :
    ContinuousOn ψ (ball 0 R) := hψ.1.continuousOn

lemma IsHelmholtzOn.continuousOn_fderiv (hψ : IsHelmholtzOn k ψ (ball 0 R)) :
    ContinuousOn (fderiv ℝ ψ) (ball 0 R) := hψ.contDiffOn_fderiv.continuousOn

lemma IsHelmholtzOn.continuousOn_fderiv_fderiv (hψ : IsHelmholtzOn k ψ (ball 0 R)) :
    ContinuousOn (fderiv ℝ (fderiv ℝ ψ)) (ball 0 R) :=
  hψ.contDiffOn_fderiv.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl

lemma hasDerivAt_ofReal_mul (e : ℂ) (ρ : ℝ) :
    HasDerivAt (fun ρ : ℝ => (ρ : ℂ) * e) e ρ := by
  simpa using ((hasDerivAt_id ρ).ofReal_comp).mul_const e

lemma hasDerivAt_polar_angle (ρ θ : ℝ) :
    HasDerivAt (fun θ : ℝ => (ρ : ℂ) * cexp (θ * I)) ((ρ : ℂ) * cexp (θ * I) * I) θ := by
  have := ((((hasDerivAt_id θ).ofReal_comp).mul_const I).cexp).const_mul (ρ : ℂ)
  convert this using 1
  simp [mul_assoc]

/-- Pointwise polar form of the Helmholtz equation:
`ρ² ∂²_ρ g + ∂²_θ g + ρ ∂_ρ g + k² ρ² g = 0` at `z = ρ e^{iθ}`. -/
lemma helmholtz_polar (hψ : IsHelmholtzOn k ψ (ball 0 R)) {ρ : ℝ} (θ : ℝ) (hρ : |ρ| < R) :
    let z := (ρ : ℂ) * cexp (θ * I)
    let e := cexp (θ * I)
    (ρ : ℂ) ^ 2 * fderiv ℝ (fderiv ℝ ψ) z e e +
      (fderiv ℝ (fderiv ℝ ψ) z (z * I) (z * I) + fderiv ℝ ψ z (z * I * I)) +
      ρ * fderiv ℝ ψ z e + (k : ℂ) ^ 2 * (ρ : ℂ) ^ 2 * ψ z = 0 := by
  intro z e
  have hz : z ∈ ball (0 : ℂ) R := polar_mem_ball θ hρ
  have hH := hψ.2 z hz
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane] at hH
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hH
  have hrot := bilin_rot_trace (fderiv ℝ (fderiv ℝ ψ) z) e (Complex.norm_exp_ofReal_mul_I θ)
  set B := fderiv ℝ (fderiv ℝ ψ) z
  set L := fderiv ℝ ψ z
  have hzI : z * I = (ρ : ℝ) • (e * I) := by simp [z, e, real_smul, mul_assoc]
  have hzII : z * I * I = (-ρ : ℝ) • e := by
    simp only [z, e, real_smul, mul_assoc, Complex.I_mul_I]; push_cast; ring
  rw [hzII, hzI, ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.map_smul]
  simp only [real_smul]
  push_cast
  linear_combination (ρ : ℂ) ^ 2 * hH + (ρ : ℂ) ^ 2 * hrot

lemma polar_mapsTo {R ρ δ : ℝ} (h0 : 0 < ρ - δ) (h1 : ρ + δ < R) :
    MapsTo (fun p : ℝ × ℝ => (p.1 : ℂ) * cexp (p.2 * I)) (Icc (ρ - δ) (ρ + δ) ×ˢ Icc 0 (2 * π))
      (ball (0 : ℂ) R) := by
  intro p hp
  refine polar_mem_ball p.2 ?_
  rw [abs_of_pos (by linarith [hp.1.1])]
  linarith [hp.1.2]

lemma continuous_polar_comp (hψ : IsHelmholtzOn k ψ (ball 0 R)) {ρ : ℝ} (hρ : |ρ| < R) :
    Continuous fun θ : ℝ => ψ ((ρ : ℂ) * cexp (θ * I)) :=
  hψ.continuousOn.comp_continuous (by fun_prop) fun θ => polar_mem_ball θ hρ

lemma continuous_fderiv_polar_comp (hψ : IsHelmholtzOn k ψ (ball 0 R)) {ρ : ℝ} (hρ : |ρ| < R) :
    Continuous fun θ : ℝ => fderiv ℝ ψ ((ρ : ℂ) * cexp (θ * I)) :=
  hψ.continuousOn_fderiv.comp_continuous (by fun_prop) fun θ => polar_mem_ball θ hρ

lemma continuous_fderiv_fderiv_polar_comp (hψ : IsHelmholtzOn k ψ (ball 0 R)) {ρ : ℝ}
    (hρ : |ρ| < R) :
    Continuous fun θ : ℝ => fderiv ℝ (fderiv ℝ ψ) ((ρ : ℂ) * cexp (θ * I)) :=
  hψ.continuousOn_fderiv_fderiv.comp_continuous (by fun_prop) fun θ => polar_mem_ball θ hρ

lemma angCoeff_hasDerivAt (hψ : IsHelmholtzOn k ψ (ball 0 R)) (n : ℤ) {ρ : ℝ}
    (hρ : ρ ∈ Ioo 0 R) : HasDerivAt (angCoeff ψ n) (angCoeffD ψ n ρ) ρ := by
  set δ := min ρ (R - ρ) / 2 with hδ
  have hδ0 : 0 < δ := by have := lt_min hρ.1 (sub_pos.2 hρ.2); positivity
  have h0 : 0 < ρ - δ := by have := min_le_left ρ (R - ρ); linarith
  have h1 : ρ + δ < R := by have := min_le_right ρ (R - ρ); linarith
  have habs : ∀ ρ' ∈ Ioo (ρ - δ) (ρ + δ), |ρ'| < R := fun ρ' h' => by
    rw [abs_of_pos (by linarith [h'.1])]; linarith [h'.2]
  refine HasDerivAt.const_mul _ (hasDerivAt_intervalIntegral_param
    (G := fun ρ θ => cexp (-(n * θ * I)) * ψ (ρ * cexp (θ * I)))
    (G' := fun ρ θ => cexp (-(n * θ * I)) * fderiv ℝ ψ (ρ * cexp (θ * I)) (cexp (θ * I))) hδ0
    (fun ρ' h' => (by fun_prop : Continuous fun θ : ℝ => cexp (-(n * θ * I))).mul
      (continuous_polar_comp hψ (habs ρ' h'))) ?_ ?_)
  · refine ContinuousOn.mul (by fun_prop) ?_
    exact (hψ.continuousOn_fderiv.comp continuous_polar.continuousOn (polar_mapsTo h0 h1)).clm_apply
      (by fun_prop)
  · intro ρ' h' θ
    have hz := polar_mem_ball θ (habs ρ' h')
    exact ((hψ.hasFDerivAt hz).comp_hasDerivAt ρ' (hasDerivAt_ofReal_mul _ ρ')).const_mul _

lemma angCoeffD_hasDerivAt (hψ : IsHelmholtzOn k ψ (ball 0 R)) (n : ℤ) {ρ : ℝ}
    (hρ : ρ ∈ Ioo 0 R) : HasDerivAt (angCoeffD ψ n) (angCoeffD2 ψ n ρ) ρ := by
  set δ := min ρ (R - ρ) / 2 with hδ
  have hδ0 : 0 < δ := by have := lt_min hρ.1 (sub_pos.2 hρ.2); positivity
  have h0 : 0 < ρ - δ := by have := min_le_left ρ (R - ρ); linarith
  have h1 : ρ + δ < R := by have := min_le_right ρ (R - ρ); linarith
  have habs : ∀ ρ' ∈ Ioo (ρ - δ) (ρ + δ), |ρ'| < R := fun ρ' h' => by
    rw [abs_of_pos (by linarith [h'.1])]; linarith [h'.2]
  refine HasDerivAt.const_mul _ (hasDerivAt_intervalIntegral_param
    (G := fun ρ θ => cexp (-(n * θ * I)) * fderiv ℝ ψ (ρ * cexp (θ * I)) (cexp (θ * I)))
    (G' := fun ρ θ => cexp (-(n * θ * I)) *
      fderiv ℝ (fderiv ℝ ψ) (ρ * cexp (θ * I)) (cexp (θ * I)) (cexp (θ * I))) hδ0
    (fun ρ' h' => (by fun_prop : Continuous fun θ : ℝ => cexp (-(n * θ * I))).mul
      ((continuous_fderiv_polar_comp hψ (habs ρ' h')).clm_apply (by fun_prop))) ?_ ?_)
  · refine ContinuousOn.mul (by fun_prop) ?_
    exact ((hψ.continuousOn_fderiv_fderiv.comp continuous_polar.continuousOn
      (polar_mapsTo h0 h1)).clm_apply (by fun_prop)).clm_apply (by fun_prop)
  · intro ρ' h' θ
    have hz := polar_mem_ball θ (habs ρ' h')
    have h1 : HasDerivAt (fun ρ : ℝ => fderiv ℝ ψ (ρ * cexp (θ * I)))
        (fderiv ℝ (fderiv ℝ ψ) (ρ' * cexp (θ * I)) (cexp (θ * I))) ρ' :=
      (hψ.hasFDerivAt_fderiv hz).comp_hasDerivAt ρ' (hasDerivAt_ofReal_mul (cexp (θ * I)) ρ')
    have h2 := h1.clm_apply (hasDerivAt_const ρ' (cexp (θ * I)))
    rw [ContinuousLinearMap.map_zero, add_zero] at h2
    exact h2.const_mul _

lemma angCoeffD2_eq (hψ : IsHelmholtzOn k ψ (ball 0 R)) (n : ℤ) {ρ : ℝ} (hρ : ρ ∈ Ioo 0 R) :
    angCoeffD2 ψ n ρ = -(angCoeffD ψ n ρ) / ρ -
      ((k : ℂ) ^ 2 - (n : ℂ) ^ 2 / (ρ : ℂ) ^ 2) * angCoeff ψ n ρ := by
  have habs : |ρ| < R := by rw [abs_of_pos hρ.1]; exact hρ.2
  obtain ⟨z, hz⟩ : ∃ z : ℝ → ℂ, z = fun θ : ℝ => (ρ : ℂ) * cexp (θ * I) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℂ, F = fun θ => ψ (z θ) := ⟨_, rfl⟩
  obtain ⟨F1, hF1⟩ : ∃ F1 : ℝ → ℂ, F1 = fun θ => fderiv ℝ ψ (z θ) (z θ * I) := ⟨_, rfl⟩
  obtain ⟨F2, hF2⟩ : ∃ F2 : ℝ → ℂ, F2 = fun θ =>
    fderiv ℝ (fderiv ℝ ψ) (z θ) (z θ * I) (z θ * I) + fderiv ℝ ψ (z θ) (z θ * I * I) :=
    ⟨_, rfl⟩
  obtain ⟨G1, hG1⟩ : ∃ G1 : ℝ → ℂ, G1 = fun θ : ℝ => fderiv ℝ ψ (z θ) (cexp (θ * I)) :=
    ⟨_, rfl⟩
  obtain ⟨G2, hG2⟩ : ∃ G2 : ℝ → ℂ, G2 = fun θ : ℝ =>
    fderiv ℝ (fderiv ℝ ψ) (z θ) (cexp (θ * I)) (cexp (θ * I)) := ⟨_, rfl⟩
  have cL : Continuous fun θ => fderiv ℝ ψ (z θ) := by
    rw [hz]; exact continuous_fderiv_polar_comp hψ habs
  have cB : Continuous fun θ => fderiv ℝ (fderiv ℝ ψ) (z θ) := by
    rw [hz]; exact continuous_fderiv_fderiv_polar_comp hψ habs
  have hzc : Continuous z := by rw [hz]; fun_prop
  have ce : Continuous fun θ : ℝ => cexp (θ * I) := by fun_prop
  have cu : Continuous fun θ : ℝ => cexp (-(n * θ * I)) := by fun_prop
  have cF : Continuous F := by rw [hF, hz]; exact continuous_polar_comp hψ habs
  have cF1 : Continuous F1 := by rw [hF1]; exact cL.clm_apply (hzc.mul continuous_const)
  have cF2 : Continuous F2 := by
    rw [hF2]
    exact ((cB.clm_apply (hzc.mul continuous_const)).clm_apply (hzc.mul continuous_const)).add
      (cL.clm_apply ((hzc.mul continuous_const).mul continuous_const))
  have cG1 : Continuous G1 := by rw [hG1]; exact cL.clm_apply ce
  have cG2 : Continuous G2 := by rw [hG2]; exact (cB.clm_apply ce).clm_apply ce
  have hzm : ∀ θ, z θ ∈ ball (0 : ℂ) R := fun θ => by rw [hz]; exact polar_mem_ball θ habs
  have hzd : ∀ θ, HasDerivAt z (z θ * I) θ := fun θ => by
    rw [hz]; exact hasDerivAt_polar_angle ρ θ
  have dF : ∀ θ, HasDerivAt F (F1 θ) θ := fun θ => by
    rw [hF, hF1]; exact (hψ.hasFDerivAt (hzm θ)).comp_hasDerivAt θ (hzd θ)
  have dF1 : ∀ θ, HasDerivAt F1 (F2 θ) θ := fun θ => by
    rw [hF1, hF2]
    exact ((hψ.hasFDerivAt_fderiv (hzm θ)).comp_hasDerivAt θ (hzd θ)).clm_apply
      ((hzd θ).mul_const I)
  have hz2 : z (2 * π) = z 0 := by
    rw [hz]
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    rw [show ((2 * π : ℝ) : ℂ) * I = 2 * π * I by push_cast; ring, Complex.exp_two_pi_mul_I,
      mul_one]
  have pF : F (2 * π) = F 0 := by rw [hF]; simp only [hz2]
  have pF1 : F1 (2 * π) = F1 0 := by rw [hF1]; simp only [hz2]
  have i1 := integral_exp_mul_deriv_of_periodic dF cF1 pF n
  have i2 := integral_exp_mul_deriv_of_periodic dF1 cF2 pF1 n
  have hpt : ∀ θ : ℝ, (ρ : ℂ) ^ 2 * G2 θ + F2 θ + ρ * G1 θ + (k : ℂ) ^ 2 * (ρ : ℂ) ^ 2 * F θ
      = 0 := fun θ => by
    have := helmholtz_polar hψ θ habs
    rw [hG2, hF2, hG1, hF, hz]
    exact this
  have hsplit : ∀ θ : ℝ, cexp (-(n * θ * I)) * ((ρ : ℂ) ^ 2 * G2 θ + F2 θ + ρ * G1 θ +
      (k : ℂ) ^ 2 * (ρ : ℂ) ^ 2 * F θ) = (ρ : ℂ) ^ 2 * (cexp (-(n * θ * I)) * G2 θ) +
      cexp (-(n * θ * I)) * F2 θ + ρ * (cexp (-(n * θ * I)) * G1 θ) +
      (k : ℂ) ^ 2 * (ρ : ℂ) ^ 2 * (cexp (-(n * θ * I)) * F θ) := fun θ => by ring
  have hint : (ρ : ℂ) ^ 2 * (∫ θ in (0 : ℝ)..2 * π, cexp (-(n * θ * I)) * G2 θ) +
      (∫ θ in (0 : ℝ)..2 * π, cexp (-(n * θ * I)) * F2 θ) +
      ρ * (∫ θ in (0 : ℝ)..2 * π, cexp (-(n * θ * I)) * G1 θ) +
      (k : ℂ) ^ 2 * (ρ : ℂ) ^ 2 * (∫ θ in (0 : ℝ)..2 * π, cexp (-(n * θ * I)) * F θ) = 0 := by
    have h0 : ∫ θ in (0 : ℝ)..2 * π, cexp (-(n * θ * I)) * ((ρ : ℂ) ^ 2 * G2 θ + F2 θ +
        ρ * G1 θ + (k : ℂ) ^ 2 * (ρ : ℂ) ^ 2 * F θ) = 0 := by simp [hpt]
    rw [intervalIntegral.integral_congr (fun θ _ => hsplit θ)] at h0
    have c2 := continuous_const (y := (ρ : ℂ) ^ 2) |>.mul (cu.mul cG2)
    have c1 := continuous_const (y := (ρ : ℂ)) |>.mul (cu.mul cG1)
    have c0 := continuous_const (y := (k : ℂ) ^ 2 * (ρ : ℂ) ^ 2) |>.mul (cu.mul cF)
    rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h0
    · exact h0
    · exact c2.intervalIntegrable _ _
    · exact (cu.mul cF2).intervalIntegrable _ _
    · exact (c2.add (cu.mul cF2)).intervalIntegrable _ _
    · exact c1.intervalIntegrable _ _
    · exact ((c2.add (cu.mul cF2)).add c1).intervalIntegrable _ _
    · exact c0.intervalIntegrable _ _
  have hD2 : angCoeffD2 ψ n ρ = (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
      cexp (-(n * θ * I)) * G2 θ := by rw [hG2, hz]; rfl
  have hD1 : angCoeffD ψ n ρ = (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
      cexp (-(n * θ * I)) * G1 θ := by rw [hG1, hz]; rfl
  have hD0 : angCoeff ψ n ρ = (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
      cexp (-(n * θ * I)) * F θ := by rw [hF, hz]; rfl
  rw [hD2, hD1, hD0]
  rw [i2, i1] at hint
  have hρ0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.1.ne'
  generalize (∫ θ in (0 : ℝ)..2 * π, cexp (-(n * θ * I)) * G2 θ) = A2 at hint ⊢
  generalize (∫ θ in (0 : ℝ)..2 * π, cexp (-(n * θ * I)) * G1 θ) = A1 at hint ⊢
  generalize (∫ θ in (0 : ℝ)..2 * π, cexp (-(n * θ * I)) * F θ) = A0 at hint ⊢
  field_simp
  linear_combination hint - (n : ℂ) ^ 2 * A0 * I_sq

/-- **Separation of variables.** The angular Fourier coefficients of a solution of the Helmholtz
equation on `B(0, R)` solve Bessel's equation on `(0, R)`. -/
theorem angCoeff_isBesselSol (hψ : IsHelmholtzOn k ψ (ball 0 R)) (n : ℤ) :
    IsBesselSol k n R (angCoeff ψ n) (angCoeffD ψ n) := fun _ hρ =>
  ⟨angCoeff_hasDerivAt hψ n hρ, angCoeffD2_eq hψ n hρ ▸ angCoeffD_hasDerivAt hψ n hρ⟩

end Helmholtz

end

section

/-! ## Fourier–Bessel waves -/

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory Set Real Metric Complex Filter Topology

lemma fourier_coe_two_pi (n : ℤ) (x : ℝ) :
    fourier n (x : AddCircle (2 * π)) = cexp (n * x * I) := by
  rw [fourier_coe_apply]
  congr 1
  have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  push_cast
  ring

lemma fourier_add_pt {T : ℝ} (n : ℤ) (x y : AddCircle T) :
    fourier n (x + y) = fourier n x * fourier n y := by
  rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add,
    Circle.coe_mul]

lemma herglotzDir_apply (k : ℝ) (a : CircFun) (z : ℂ) (x : AddCircle (2 * π)) :
    herglotzDir k a z x = a x * cexp (herglotzPhase k z x) := by
  simp only [herglotzDir, ContinuousMap.mul_apply]
  congr 1
  have := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ x) (continuous_eval_const x)
    (herglotzPhase k z)
  simpa [Complex.exp_eq_exp_ℂ] using this

lemma herglotzWave_eq_integral (k : ℝ) (a : CircFun) (z : ℂ) :
    herglotzWave k a z = ∫ x, herglotzDir k a z x ∂AddCircle.haarAddCircle := by
  rw [herglotzWave, circCoeff_apply, fourierCoeff]
  simp

lemma herglotzPhase_rot (k : ℝ) (z : ℂ) (θ : ℝ) (x : AddCircle (2 * π)) :
    herglotzPhase k (cexp (θ * I) * z) x = herglotzPhase k z (x - θ) := by
  simp only [herglotzPhase_apply, ContinuousMap.smul_apply, ContinuousMap.add_apply, smul_eq_mul]
  rw [sub_eq_add_neg, fourier_add_pt, fourier_add_pt, ← AddCircle.coe_neg, fourier_coe_two_pi,
    fourier_coe_two_pi, map_mul, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring_nf

/-- The Fourier–Bessel wave `fbWave k n = u_{e^{inφ}}`, the Herglotz wave with density
`e^{inφ}`. -/
def fbWave (k : ℝ) (n : ℤ) : ℂ → ℂ := herglotzWave k (fourier n)

lemma fbWave_rot (k : ℝ) (n : ℤ) (z : ℂ) (θ : ℝ) :
    fbWave k n (cexp (θ * I) * z) = cexp (n * θ * I) * fbWave k n z := by
  simp only [fbWave, herglotzWave_eq_integral, herglotzDir_apply, herglotzPhase_rot]
  have h : ∀ x : AddCircle (2 * π), fourier n x * cexp (herglotzPhase k z (x - θ)) =
      cexp (n * θ * I) * (fourier n (x - (θ : AddCircle (2 * π))) *
        cexp (herglotzPhase k z (x - θ))) := by
    intro x
    have hx : fourier n x =
        fourier n ((x - (θ : AddCircle (2 * π))) + (θ : AddCircle (2 * π))) := by
      rw [sub_add_cancel]
    rw [hx, fourier_add_pt, fourier_coe_two_pi]
    ring
  simp_rw [h]
  rw [integral_const_mul]
  congr 1
  exact integral_sub_right_eq_self (fun x => fourier n x * cexp (herglotzPhase k z x)) _

lemma fbWave_polar (k : ℝ) (n : ℤ) (ρ θ : ℝ) :
    fbWave k n (ρ * cexp (θ * I)) = cexp (n * θ * I) * fbWave k n ρ := by
  rw [mul_comm, fbWave_rot]

lemma continuous_fbWave (k : ℝ) (n : ℤ) : Continuous (fbWave k n) :=
  (contDiff_herglotzWave k _).continuous

lemma integral_exp_int_mul (j : ℤ) :
    ∫ θ in (0 : ℝ)..2 * π, cexp (j * θ * I) = if j = 0 then 2 * π else 0 := by
  split_ifs with hj
  · subst hj; simp
  · have hc : (j : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hj) I_ne_zero
    have := integral_exp_mul_complex (a := 0) (b := 2 * π) hc
    simp_rw [show ∀ θ : ℝ, (j : ℂ) * θ * I = j * I * θ from fun θ => by ring]
    rw [this]
    have h2 : cexp (j * I * ((2 * π : ℝ) : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I j]; congr 1; push_cast; ring
    push_cast at h2
    simp [h2]

/-- The angular Fourier coefficients of `fbWave k n` on the circle of radius `ρ`. -/
lemma angCoeff_fbWave (k : ℝ) (n m : ℤ) (ρ : ℝ) :
    angCoeff (fbWave k n) m ρ = if m = n then fbWave k n ρ else 0 := by
  unfold angCoeff
  simp_rw [fbWave_polar]
  have h : ∀ θ : ℝ, cexp (-(m * θ * I)) * (cexp (n * θ * I) * fbWave k n ρ) =
      fbWave k n ρ * cexp (((n - m : ℤ) : ℂ) * θ * I) := by
    intro θ
    rw [mul_left_comm, ← mul_assoc, ← Complex.exp_add, mul_comm]
    congr 1
    push_cast
    ring_nf
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, integral_exp_int_mul]
  have hpi : (2 * π : ℂ) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  by_cases hmn : m = n
  · subst hmn; simp only [sub_self, if_true]; field_simp; push_cast; ring
  · have : n - m ≠ 0 := sub_ne_zero.2 (Ne.symm hmn)
    simp [hmn, this]

lemma circCoeff_herglotzDir_fourier (k : ℝ) (n j : ℤ) (z : ℂ) :
    circCoeff j (herglotzDir k (fourier n) z) = fbWave k (n - j) z := by
  have h : herglotzDir k (fourier n) z = herglotzDir k (fourier (n - j)) z * fourier j := by
    ext x
    simp only [herglotzDir, ContinuousMap.mul_apply]
    rw [show n = (n - j) + j by ring, fourier_add]
    simp only [sub_add_cancel]
    ring
  rw [h, circCoeff_mul_fourier, sub_self]
  rfl

/-- Derivative of a Fourier–Bessel wave:
`D fbWave_n(z) w = -(ik/2)(w fbWave_{n-1}(z) + w̄ fbWave_{n+1}(z))`. -/
lemma fderiv_fbWave (k : ℝ) (n : ℤ) (z w : ℂ) :
    fderiv ℝ (fbWave k n) z w =
      -(I * k / 2) * (w * fbWave k (n - 1) z + conj w * fbWave k (n + 1) z) := by
  rw [fbWave, fderiv_herglotzWave_apply, herglotzVec, circPos_apply,
    circCoeff_herglotzDir_fourier, circCoeff_herglotzDir_fourier]
  simp

lemma fbWave_zero_zero (k : ℝ) : fbWave k 0 0 = 1 := by
  simp [fbWave, herglotzWave_eq_integral, herglotzDir_apply]

/-- If `fbWave k m` vanishes on an open set, so do `fbWave k (m - 1)` and `fbWave k (m + 1)`. -/
lemma fbWave_eqOn_zero_step {k : ℝ} (hk : k ≠ 0) {V : Set ℂ} (hV : IsOpen V) {m : ℤ}
    (hm : ∀ z ∈ V, fbWave k m z = 0) :
    (∀ z ∈ V, fbWave k (m - 1) z = 0) ∧ (∀ z ∈ V, fbWave k (m + 1) z = 0) := by
  have hd : ∀ z ∈ V, ∀ w, fderiv ℝ (fbWave k m) z w = 0 := by
    intro z hz w
    have : fbWave k m =ᶠ[𝓝 z] fun _ => 0 :=
      Filter.eventually_of_mem (hV.mem_nhds hz) hm
    rw [this.fderiv_eq]; simp
  have hk' : -(I * k / 2) ≠ 0 := by
    have : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    simp [this, I_ne_zero]
  have key : ∀ z ∈ V, fbWave k (m - 1) z = 0 ∧ fbWave k (m + 1) z = 0 := by
    intro z hz
    have h1 := hd z hz 1
    have h2 := hd z hz I
    rw [fderiv_fbWave] at h1 h2
    have e1 : fbWave k (m - 1) z + fbWave k (m + 1) z = 0 := by
      have := (mul_eq_zero.1 h1).resolve_left hk'
      simpa using this
    have e2 : fbWave k (m - 1) z - fbWave k (m + 1) z = 0 := by
      have := (mul_eq_zero.1 h2).resolve_left hk'
      simp only [Complex.conj_I] at this
      have h3 : I * (fbWave k (m - 1) z - fbWave k (m + 1) z) = 0 := by
        linear_combination this
      simpa [I_ne_zero] using h3
    exact ⟨by linear_combination (e1 + e2) / 2, by linear_combination (e1 - e2) / 2⟩
  exact ⟨fun z hz => (key z hz).1, fun z hz => (key z hz).2⟩

lemma fbWave_zero_on_of_zero_on {k : ℝ} (hk : k ≠ 0) {V : Set ℂ} (hV : IsOpen V) :
    ∀ (N : ℕ) (m : ℤ), m.natAbs = N → (∀ z ∈ V, fbWave k m z = 0) →
      ∀ z ∈ V, fbWave k 0 z = 0 := by
  intro N
  induction N with
  | zero =>
    intro m hm h
    have : m = 0 := Int.natAbs_eq_zero.1 hm
    subst this; exact h
  | succ N ih =>
    intro m hm h
    obtain ⟨h1, h2⟩ := fbWave_eqOn_zero_step hk hV h
    rcases lt_or_gt_of_ne (show m ≠ 0 by omega) with hneg | hpos
    · exact ih (m + 1) (by omega) h2
    · exact ih (m - 1) (by omega) h1

/-- `ρ ↦ fbWave k n ρ` does not vanish identically on `(0, R)`. -/
lemma fbWave_exists_ne_zero {k : ℝ} (hk : k ≠ 0) (n : ℤ) {R : ℝ} (hR : 0 < R) :
    ∃ ρ ∈ Ioo 0 R, fbWave k n ρ ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hV : IsOpen (ball (0 : ℂ) R \ {0}) := isOpen_ball.sdiff isClosed_singleton
  have hzero : ∀ z ∈ ball (0 : ℂ) R \ {0}, fbWave k n z = 0 := by
    intro z hz
    have hz0 : z ≠ 0 := hz.2
    have hzR : ‖z‖ < R := by simpa using hz.1
    rw [← Complex.norm_mul_exp_arg_mul_I z, fbWave_polar,
      hcon ‖z‖ ⟨norm_pos_iff.2 hz0, hzR⟩, mul_zero]
  have h0 := fbWave_zero_on_of_zero_on hk hV _ n rfl hzero
  have hlim : Tendsto (fbWave k 0) (𝓝[≠] 0) (𝓝 (fbWave k 0 0)) :=
    (continuous_fbWave k 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hev : fbWave k 0 =ᶠ[𝓝[≠] 0] fun _ => 0 := by
    filter_upwards [inter_mem_nhdsWithin ({0}ᶜ : Set ℂ) (ball_mem_nhds (0 : ℂ) hR)] with z hz
    exact h0 z ⟨hz.2, hz.1⟩
  have : fbWave k 0 0 = 0 := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hev.symm)
  rw [fbWave_zero_zero] at this
  exact one_ne_zero this

end

section

/-! ## Angular Fourier coefficients of Helmholtz solutions are Fourier–Bessel multiples -/

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory Set Real Metric Complex Filter Topology

lemma IsBesselSol.mono {k : ℝ} {n : ℤ} {R R' : ℝ} {f f' : ℝ → ℂ} (h : IsBesselSol k n R f f')
    (hR : R' ≤ R) : IsBesselSol k n R' f f' := fun ρ hρ => h ρ ⟨hρ.1, hρ.2.trans_le hR⟩

lemma norm_exp_neg_int_mul_I (n : ℤ) (θ : ℝ) : ‖cexp (-(n * θ * I))‖ = 1 := by
  rw [show -((n : ℂ) * θ * I) = ((-(n * θ) : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma norm_inv_two_pi : ‖(2 * π : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
  rw [norm_inv]
  congr 1
  rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- `(2π)⁻¹ |∫₀^{2π} f| ≤ M` when `|f| ≤ M`. -/
lemma norm_inv_two_pi_mul_integral_le {f : ℝ → ℂ} {M : ℝ} (h : ∀ θ, ‖f θ‖ ≤ M) :
    ‖(2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, f θ‖ ≤ M := by
  rw [norm_mul, norm_inv_two_pi]
  have h1 : ‖∫ θ in (0 : ℝ)..2 * π, f θ‖ ≤ M * |2 * π - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => h θ
  rw [sub_zero, abs_of_pos (by positivity)] at h1
  calc (2 * π)⁻¹ * ‖∫ θ in (0 : ℝ)..2 * π, f θ‖ ≤ (2 * π)⁻¹ * (M * (2 * π)) := by gcongr
    _ = M := by field_simp

lemma norm_angCoeff_le {g : ℂ → ℂ} {R' M : ℝ} (h : ∀ z ∈ closedBall (0 : ℂ) R', ‖g z‖ ≤ M)
    (n : ℤ) {ρ : ℝ} (hρ : |ρ| ≤ R') : ‖angCoeff g n ρ‖ ≤ M := by
  refine norm_inv_two_pi_mul_integral_le fun θ => ?_
  rw [norm_mul, norm_exp_neg_int_mul_I, one_mul]
  exact h _ (by simpa [norm_mul, Complex.norm_exp_ofReal_mul_I] using hρ)

lemma norm_angCoeffD_le {g : ℂ → ℂ} {R' M : ℝ}
    (h : ∀ z ∈ closedBall (0 : ℂ) R', ‖fderiv ℝ g z‖ ≤ M) (n : ℤ) {ρ : ℝ} (hρ : |ρ| ≤ R') :
    ‖angCoeffD g n ρ‖ ≤ M := by
  refine norm_inv_two_pi_mul_integral_le fun θ => ?_
  rw [norm_mul, norm_exp_neg_int_mul_I, one_mul]
  refine ((fderiv ℝ g _).le_opNorm _).trans ?_
  rw [Complex.norm_exp_ofReal_mul_I, mul_one]
  exact h _ (by simpa [norm_mul, Complex.norm_exp_ofReal_mul_I] using hρ)

/-- **Fourier–Bessel structure of Helmholtz solutions.** For a solution of the Helmholtz equation
on `B(0, R)` and each `n`, the angular coefficient `angCoeff ψ n` is a constant multiple of
`ρ ↦ fbWave k n ρ` on `(0, R)`. -/
theorem angCoeff_eq_smul_fbWave {k R : ℝ} (hk : k ≠ 0) {ψ : ℂ → ℂ}
    (hψ : IsHelmholtzOn k ψ (ball 0 R)) (n : ℤ) (hR : 0 < R) :
    ∃ c : ℂ, ∀ ρ ∈ Ioo 0 R, angCoeff ψ n ρ = c * fbWave k n ρ := by
  obtain ⟨ρ₀, hρ₀, hne⟩ := fbWave_exists_ne_zero hk n hR
  refine ⟨angCoeff ψ n ρ₀ / fbWave k n ρ₀, fun ρ hρ => ?_⟩
  set R' := (max ρ ρ₀ + R) / 2 with hR'
  have hm1 := le_max_left ρ ρ₀
  have hm2 := le_max_right ρ ρ₀
  have hmR : max ρ ρ₀ < R := max_lt hρ.2 hρ₀.2
  have hR'R : R' < R := by rw [hR']; linarith
  have hρR' : ρ < R' := by rw [hR']; linarith
  have hρ₀R' : ρ₀ < R' := by rw [hR']; linarith
  have hsub : closedBall (0 : ℂ) R' ⊆ ball 0 R := closedBall_subset_ball hR'R
  have hfb : IsHelmholtzOn k (fbWave k n) (ball 0 R) := isHelmholtzOn_herglotzWave k _ _
  obtain ⟨M1, hM1⟩ := (isCompact_closedBall (0 : ℂ) R').exists_bound_of_continuousOn
    (hψ.continuousOn.mono hsub)
  obtain ⟨M2, hM2⟩ := (isCompact_closedBall (0 : ℂ) R').exists_bound_of_continuousOn
    (hψ.continuousOn_fderiv.mono hsub)
  obtain ⟨M3, hM3⟩ := (isCompact_closedBall (0 : ℂ) R').exists_bound_of_continuousOn
    (hfb.continuousOn.mono hsub)
  obtain ⟨M4, hM4⟩ := (isCompact_closedBall (0 : ℂ) R').exists_bound_of_continuousOn
    (hfb.continuousOn_fderiv.mono hsub)
  set M := max (max M1 M2) (max M3 M4)
  have habs : ∀ σ ∈ Ioo 0 R', |σ| ≤ R' := fun σ hσ => by rw [abs_of_pos hσ.1]; exact hσ.2.le
  have key := bessel_eq_smul ((angCoeff_isBesselSol hψ n).mono hR'R.le)
    ((angCoeff_isBesselSol hfb n).mono hR'R.le) (M := M)
    (fun σ hσ => ⟨norm_angCoeff_le (fun z hz => (hM1 z hz).trans (by simp [M])) n (habs σ hσ),
      norm_angCoeffD_le (fun z hz => (hM2 z hz).trans (by simp [M])) n (habs σ hσ)⟩)
    (fun σ hσ => ⟨norm_angCoeff_le (fun z hz => (hM3 z hz).trans (by simp [M])) n (habs σ hσ),
      norm_angCoeffD_le (fun z hz => (hM4 z hz).trans (by simp [M])) n (habs σ hσ)⟩)
    ⟨hρ₀.1, hρ₀R'⟩ (by rw [angCoeff_fbWave, if_pos rfl]; exact hne) ρ ⟨hρ.1, hρR'⟩
  simpa [angCoeff_fbWave] using key

end

section

/-! ## Fourier series on `[0, 2π]`: Parseval, pointwise convergence and tail bounds -/

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory Set Real Metric Complex Filter Topology

/-- The Fourier coefficient `cf f m = (2π)⁻¹ ∫₀^{2π} e^{-imθ} f(θ) dθ`. -/
def cf (f : ℝ → ℂ) (m : ℤ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, cexp (-(m * θ * I)) * f θ

lemma angCoeff_eq_cf (g : ℂ → ℂ) (n : ℤ) (ρ : ℝ) :
    angCoeff g n ρ = cf (fun θ => g (ρ * cexp (θ * I))) n := rfl

lemma fourierCoeffOn_eq_cf (f : ℝ → ℂ) (m : ℤ) :
    fourierCoeffOn Real.two_pi_pos f m = cf f m := by
  rw [fourierCoeffOn_eq_integral, cf, sub_zero, real_smul]
  congr 1
  · push_cast; ring
  · refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [smul_eq_mul]
    congr 1
    rw [fourier_coe_apply]
    congr 1
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp

lemma memLp_two_Ioc_of_continuous {f : ℝ → ℂ} (hf : Continuous f) (a b : ℝ) :
    MemLp f 2 (volume.restrict (Ioc a b)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hf.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  exact Filter.Eventually.of_forall fun x hx => hC x (Ioc_subset_Icc_self hx)

/-- **Parseval's identity** on `[0, 2π]`. -/
lemma hasSum_sq_cf {f : ℝ → ℂ} (hf : Continuous f) :
    HasSum (fun m => ‖cf f m‖ ^ 2) ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ‖f θ‖ ^ 2) := by
  have := hasSum_sq_fourierCoeffOn Real.two_pi_pos (memLp_two_Ioc_of_continuous hf 0 (2 * π))
  simpa only [fourierCoeffOn_eq_cf, sub_zero, smul_eq_mul] using this

lemma cf_deriv {f f' : ℝ → ℂ} (hf : ∀ θ, HasDerivAt f (f' θ) θ) (hf' : Continuous f')
    (hper : f (2 * π) = f 0) (m : ℤ) : cf f' m = m * I * cf f m := by
  unfold cf
  rw [integral_exp_mul_deriv_of_periodic hf hf' hper m]
  ring

lemma tsum_sq_cf_le {f : ℝ → ℂ} (hf : Continuous f) {B : ℝ} (hB : ∀ θ, ‖f θ‖ ≤ B) :
    ∑' m, ‖cf f m‖ ^ 2 ≤ B ^ 2 := by
  rw [(hasSum_sq_cf hf).tsum_eq]
  have h1 : ∫ θ in (0 : ℝ)..2 * π, ‖f θ‖ ^ 2 ≤ ∫ θ in (0 : ℝ)..2 * π, B ^ 2 :=
    intervalIntegral.integral_mono_on (by positivity)
      ((hf.norm.pow 2).intervalIntegrable _ _) intervalIntegrable_const
      (fun θ _ => pow_le_pow_left₀ (norm_nonneg _) (hB θ) 2)
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h1
  calc (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ‖f θ‖ ^ 2 ≤ (2 * π)⁻¹ * (2 * π * B ^ 2) := by
        gcongr
    _ = B ^ 2 := by field_simp

lemma summable_int_tail (N : ℕ) :
    Summable fun m : ℤ => if N < m.natAbs then 1 / (m : ℝ) ^ 2 else 0 := by
  refine (Real.summable_one_div_int_pow.2 one_lt_two).of_nonneg_of_le
    (fun m => by split_ifs <;> positivity) (fun m => ?_)
  split_ifs
  · exact le_rfl
  · positivity

/-- The tails `Σ_{|m| > N} m⁻²` tend to `0`. -/
lemma tendsto_int_tail :
    Tendsto (fun N : ℕ => ∑' m : ℤ, if N < m.natAbs then 1 / (m : ℝ) ^ 2 else 0) atTop (𝓝 0) := by
  have h := (tendsto_tsum_compl_atTop_zero (fun m : ℤ => 1 / (m : ℝ) ^ 2)).comp
    (Finset.tendsto_Icc_neg_atTop_atTop.comp tendsto_natCast_atTop_atTop)
  refine h.congr fun N => ?_
  simp only [Function.comp_apply]
  refine (tsum_subtype ({x | x ∉ Finset.Icc (-(N : ℤ)) N} : Set ℤ)
    (fun m : ℤ => 1 / (m : ℝ) ^ 2)).trans ?_
  congr 1
  funext m
  simp only [Set.indicator, Set.mem_setOf_eq, Finset.mem_Icc]
  congr 1
  apply propext
  omega

lemma am_gm_aux {x y t : ℝ} (ht : 0 < t) : x * y ≤ (t * x ^ 2 + y ^ 2 / t) / 2 := by
  have key : (t * x ^ 2 + y ^ 2 / t) / 2 - x * y = (t * x - y) ^ 2 / (2 * t) := by
    field_simp; ring
  have : 0 ≤ (t * x - y) ^ 2 / (2 * t) := by positivity
  linarith

/-- **Tail bound** for the Fourier coefficients of a periodic `C¹` function with `|f'| ≤ B`. -/
lemma cf_tail_le {f f' : ℝ → ℂ} (hf : ∀ θ, HasDerivAt f (f' θ) θ) (hf' : Continuous f')
    (hper : f (2 * π) = f 0) {B : ℝ} (hB : ∀ θ, ‖f' θ‖ ≤ B) (N : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (fun m : ℤ => if N < m.natAbs then ‖cf f m‖ else 0) ∧
      ∑' m : ℤ, (if N < m.natAbs then ‖cf f m‖ else 0) ≤
        t * B ^ 2 / 2 + (∑' m : ℤ, if N < m.natAbs then 1 / (m : ℝ) ^ 2 else 0) / (2 * t) := by
  have hsq : Summable fun m => ‖cf f' m‖ ^ 2 := (hasSum_sq_cf hf').summable
  set g : ℤ → ℝ := fun m => t / 2 * ‖cf f' m‖ ^ 2 +
    (if N < m.natAbs then 1 / (m : ℝ) ^ 2 else 0) / (2 * t) with hg
  have hgs : Summable g := (hsq.mul_left _).add ((summable_int_tail N).div_const _)
  have hle : ∀ m : ℤ, (if N < m.natAbs then ‖cf f m‖ else 0) ≤ g m := by
    intro m
    split_ifs with hm
    · have hm0 : m ≠ 0 := by omega
      have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
      have hcf : ‖cf f m‖ = ‖cf f' m‖ * (1 / |(m : ℝ)|) := by
        rw [cf_deriv hf hf' hper m, norm_mul, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_intCast]
        field_simp
      rw [hcf, hg]
      have := am_gm_aux (x := ‖cf f' m‖) (y := 1 / |(m : ℝ)|) ht
      have e : (1 / |(m : ℝ)|) ^ 2 = 1 / (m : ℝ) ^ 2 := by rw [div_pow, sq_abs, one_pow]
      rw [e] at this
      simp only [hm, if_true]
      calc ‖cf f' m‖ * (1 / |(m : ℝ)|) ≤ (t * ‖cf f' m‖ ^ 2 + 1 / (m : ℝ) ^ 2 / t) / 2 := this
        _ = t / 2 * ‖cf f' m‖ ^ 2 + 1 / (m : ℝ) ^ 2 / (2 * t) := by field_simp
    · rw [hg]; simp only [hm, if_false, zero_div, add_zero]; positivity
  have hnn : ∀ m : ℤ, 0 ≤ (if N < m.natAbs then ‖cf f m‖ else 0) := fun m => by
    split_ifs <;> positivity
  have hS : Summable (fun m : ℤ => if N < m.natAbs then ‖cf f m‖ else 0) :=
    hgs.of_nonneg_of_le hnn hle
  refine ⟨hS, (hS.tsum_le_tsum hle hgs).trans ?_⟩
  rw [hg, (hsq.mul_left _).tsum_add ((summable_int_tail N).div_const _), tsum_mul_left,
    tsum_div_const]
  have := tsum_sq_cf_le hf' hB
  have : t / 2 * ∑' m, ‖cf f' m‖ ^ 2 ≤ t / 2 * B ^ 2 := by gcongr
  linarith

lemma summable_norm_cf {f f' : ℝ → ℂ} (hf : ∀ θ, HasDerivAt f (f' θ) θ) (hf' : Continuous f')
    (hper : f (2 * π) = f 0) {B : ℝ} (hB : ∀ θ, ‖f' θ‖ ≤ B) :
    Summable fun m => ‖cf f m‖ := by
  have h1 := (cf_tail_le hf hf' hper hB 0 one_pos).1
  have h2 : Summable fun m : ℤ => if m = 0 then ‖cf f m‖ else 0 :=
    summable_of_ne_finset_zero (s := {0}) fun m hm => by simp_all
  refine (h1.add h2).of_nonneg_of_le (fun _ => norm_nonneg _) fun m => ?_
  by_cases hm : m = 0
  · subst hm; simp
  · have : 0 < m.natAbs := Int.natAbs_pos.2 hm
    simp [hm, this]

/-- **Pointwise convergence** of absolutely summable Fourier series of a continuous function on
the circle. -/
lemma hasSum_cf_circle {Φ : ℂ → ℂ} (hΦ : ContinuousOn Φ (sphere 0 1))
    (hs : Summable fun m => ‖cf (fun θ => Φ (cexp (θ * I))) m‖) (θ : ℝ) :
    HasSum (fun m : ℤ => cf (fun θ => Φ (cexp (θ * I))) m * cexp (m * θ * I))
      (Φ (cexp (θ * I))) := by
  let F : C(AddCircle (2 * π), ℂ) := ⟨fun x => Φ (AddCircle.toCircle x),
    hΦ.comp_continuous (continuous_subtype_val.comp AddCircle.continuous_toCircle)
      (fun x => by simp)⟩
  have hF : ∀ x : ℝ, F x = Φ (cexp (x * I)) := by
    intro x
    simp only [F, ContinuousMap.coe_mk, AddCircle.toCircle_apply_mk, Circle.coe_exp]
    congr 2
    have : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    push_cast
    field_simp
  have hcoef : ∀ m, fourierCoeff F m = cf (fun θ => Φ (cexp (θ * I))) m := by
    intro m
    rw [fourierCoeff_eq_intervalIntegral F m 0, zero_add, cf, real_smul]
    congr 1
    · push_cast; ring
    · refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [smul_eq_mul, hF, fourier_coe_two_pi]
      push_cast
      ring_nf
  have hsum : Summable (fourierCoeff F) := by
    have : fourierCoeff F = fun m => cf (fun θ => Φ (cexp (θ * I))) m := funext hcoef
    rw [this]; exact hs.of_norm
  have := has_pointwise_sum_fourier_series_of_summable hsum (θ : AddCircle (2 * π))
  simpa only [hcoef, smul_eq_mul, fourier_coe_two_pi, hF] using this

end

section

/-! ## Herglotz approximation of Helmholtz solutions on a disk -/

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory Set Real Metric Complex Filter Topology

lemma IsHelmholtzOn.sub {k : ℝ} {ψ φ : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hψ : IsHelmholtzOn k ψ Ω) (hφ : IsHelmholtzOn k φ Ω) :
    IsHelmholtzOn k (fun z => ψ z - φ z) Ω := by
  refine ⟨hψ.1.sub hφ.1, fun z hz => ?_⟩
  have h1 : ContDiffAt ℝ 2 ψ z := hψ.1.contDiffAt (hΩ.mem_nhds hz)
  have h2 : ContDiffAt ℝ 2 φ z := hφ.1.contDiffAt (hΩ.mem_nhds hz)
  have e : (fun z => ψ z - φ z) = ψ + (-1 : ℂ) • φ := by funext w; simp; ring
  have h3 : ContDiffAt ℝ 2 ((-1 : ℂ) • φ) z := h2.const_smul (-1 : ℂ)
  rw [e, h1.laplacian_add h3, InnerProductSpace.laplacian_smul _ h2]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination hψ.2 z hz - hφ.2 z hz

/-- `‖L‖ ≤ ‖L e‖ + ‖L (e i)‖` for a real-linear map `L : ℂ → ℂ` and `|e| = 1`. -/
lemma norm_clm_le_two (L : ℂ →L[ℝ] ℂ) {e : ℂ} (he : ‖e‖ = 1) : ‖L‖ ≤ ‖L e‖ + ‖L (e * I)‖ := by
  refine L.opNorm_le_bound (by positivity) fun w => ?_
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  set q := w / e
  have hw : w = q.re • e + q.im • (e * I) := by
    have : w = q * e := by simp [q, he0]
    rw [this]
    apply Complex.ext
    · simp; ring
    · simp
  have hq : ‖q‖ = ‖w‖ := by simp [q, he]
  calc ‖L w‖ = ‖q.re • L e + q.im • L (e * I)‖ := by
        conv_lhs => rw [hw]
        rw [map_add, map_smul, map_smul]
    _ ≤ |q.re| * ‖L e‖ + |q.im| * ‖L (e * I)‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_smul, norm_smul]; simp
    _ ≤ ‖q‖ * ‖L e‖ + ‖q‖ * ‖L (e * I)‖ := by
        gcongr
        · exact Complex.abs_re_le_norm q
        · exact Complex.abs_im_le_norm q
    _ = (‖L e‖ + ‖L (e * I)‖) * ‖w‖ := by rw [hq]; ring

lemma herglotzWave_finset_sum (k : ℝ) (s : Finset ℤ) (c : ℤ → ℂ) (a : ℤ → CircFun) (z : ℂ) :
    herglotzWave k (∑ n ∈ s, c n • a n) z = ∑ n ∈ s, c n * herglotzWave k (a n) z := by
  simp only [herglotzWave, herglotzDir, Finset.sum_mul, map_sum, smul_mul_assoc, map_smul,
    smul_eq_mul]

lemma angCoeff_finset_sum {R : ℝ} (s : Finset ℤ) (c : ℤ → ℂ) (f : ℤ → ℂ → ℂ)
    (hf : ∀ n ∈ s, ContinuousOn (f n) (ball 0 R)) (m : ℤ) {ρ : ℝ} (hρ : |ρ| < R) :
    angCoeff (fun z => ∑ n ∈ s, c n * f n z) m ρ = ∑ n ∈ s, c n * angCoeff (f n) m ρ := by
  unfold angCoeff
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finset_sum, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun n _ => ?_
    have : ∫ θ in (0 : ℝ)..2 * π, cexp (-(m * θ * I)) * (c n * f n (ρ * cexp (θ * I))) =
        c n * ∫ θ in (0 : ℝ)..2 * π, cexp (-(m * θ * I)) * f n (ρ * cexp (θ * I)) := by
      rw [← intervalIntegral.integral_const_mul]; congr 1; funext θ; ring
    rw [this]; ring
  · intro n hn
    refine Continuous.intervalIntegrable ?_ _ _
    exact (by fun_prop : Continuous fun θ : ℝ => cexp (-(m * θ * I))).mul
      (continuous_const.mul ((hf n hn).comp_continuous (by fun_prop) fun θ => polar_mem_ball θ hρ))

lemma angCoeff_sub {R : ℝ} {f g : ℂ → ℂ} (hf : ContinuousOn f (ball 0 R))
    (hg : ContinuousOn g (ball 0 R)) (m : ℤ) {ρ : ℝ} (hρ : |ρ| < R) :
    angCoeff (fun z => f z - g z) m ρ = angCoeff f m ρ - angCoeff g m ρ := by
  unfold angCoeff
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub, mul_sub]
  · exact ((by fun_prop : Continuous fun θ : ℝ => cexp (-(m * θ * I))).mul
      (hf.comp_continuous (by fun_prop) fun θ => polar_mem_ball θ hρ)).intervalIntegrable _ _
  · exact ((by fun_prop : Continuous fun θ : ℝ => cexp (-(m * θ * I))).mul
      (hg.comp_continuous (by fun_prop) fun θ => polar_mem_ball θ hρ)).intervalIntegrable _ _

lemma norm_exp_int_mul_I (m : ℤ) (θ : ℝ) : ‖cexp (m * θ * I)‖ = 1 := by
  rw [show (m : ℂ) * θ * I = ((m * θ : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma exp_two_pi_mul_I_eq : cexp (((2 * π : ℝ) : ℂ) * I) = cexp (((0 : ℝ) : ℂ) * I) := by
  rw [show ((2 * π : ℝ) : ℂ) * I = 2 * π * I by push_cast; ring, Complex.exp_two_pi_mul_I]
  simp

/-- The angular coefficient of the tangential derivative `Dg(ρe^{iθ})(ie^{iθ})`. -/
def angCoeffT (g : ℂ → ℂ) (n : ℤ) (ρ : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
    cexp (-(n * θ * I)) * fderiv ℝ g (ρ * cexp (θ * I)) (cexp (θ * I) * I)

section Helmholtz

variable {k R : ℝ} {g : ℂ → ℂ}

lemma angCoeffT_eq (hg : IsHelmholtzOn k g (ball 0 R)) {ρ : ℝ} (hρ : ρ ∈ Ioo 0 R) (m : ℤ) :
    angCoeffT g m ρ = m * I / ρ * angCoeff g m ρ := by
  have habs : |ρ| < R := by rw [abs_of_pos hρ.1]; exact hρ.2
  have dF : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => g (ρ * cexp (θ * I)))
      (fderiv ℝ g (ρ * cexp (θ * I)) (ρ * cexp (θ * I) * I)) θ := fun θ =>
    (hg.hasFDerivAt (polar_mem_ball θ habs)).comp_hasDerivAt θ (hasDerivAt_polar_angle ρ θ)
  have cF' : Continuous fun θ : ℝ => fderiv ℝ g (ρ * cexp (θ * I)) (ρ * cexp (θ * I) * I) :=
    (continuous_fderiv_polar_comp hg habs).clm_apply (by fun_prop)
  have hper : (fun θ : ℝ => g (ρ * cexp (θ * I))) (2 * π) =
      (fun θ : ℝ => g (ρ * cexp (θ * I))) 0 := by
    simp only; rw [exp_two_pi_mul_I_eq]
  have h := cf_deriv dF cF' hper m
  have h2 : cf (fun θ : ℝ => fderiv ℝ g (ρ * cexp (θ * I)) (ρ * cexp (θ * I) * I)) m =
      ρ * angCoeffT g m ρ := by
    unfold cf angCoeffT
    have e : ∀ θ : ℝ, cexp (-(m * θ * I)) * fderiv ℝ g (ρ * cexp (θ * I)) (ρ * cexp (θ * I) * I)
        = ρ * (cexp (-(m * θ * I)) * fderiv ℝ g (ρ * cexp (θ * I)) (cexp (θ * I) * I)) := by
      intro θ
      rw [show (ρ : ℂ) * cexp (θ * I) * I = (ρ : ℝ) • (cexp (θ * I) * I) by
        simp [real_smul, mul_assoc], ContinuousLinearMap.map_smul, real_smul]
      ring
    rw [intervalIntegral.integral_congr (fun θ _ => e θ), intervalIntegral.integral_const_mul]
    ring
  rw [h2, ← angCoeff_eq_cf] at h
  have hρ0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.1.ne'
  field_simp
  linear_combination h

lemma hasDerivAt_exp_mul_const (c : ℂ) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => cexp (θ * I) * c) (cexp (θ * I) * I * c) θ := by
  have := (((hasDerivAt_id θ).ofReal_comp).mul_const I).cexp.mul_const c
  simpa using this

lemma hasDerivAt_fderiv_polar (hg : IsHelmholtzOn k g (ball 0 R)) {ρ : ℝ} (habs : |ρ| < R)
    (c : ℂ) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => fderiv ℝ g (ρ * cexp (θ * I)) (cexp (θ * I) * c))
      (fderiv ℝ (fderiv ℝ g) (ρ * cexp (θ * I)) (ρ * cexp (θ * I) * I) (cexp (θ * I) * c) +
        fderiv ℝ g (ρ * cexp (θ * I)) (cexp (θ * I) * I * c)) θ := by
  have h1 : HasDerivAt (fun θ : ℝ => fderiv ℝ g (ρ * cexp (θ * I)))
      (fderiv ℝ (fderiv ℝ g) (ρ * cexp (θ * I)) (ρ * cexp (θ * I) * I)) θ :=
    (hg.hasFDerivAt_fderiv (polar_mem_ball θ habs)).comp_hasDerivAt θ
      (hasDerivAt_polar_angle ρ θ)
  exact h1.clm_apply (hasDerivAt_exp_mul_const c θ)

end Helmholtz

/-- Bound on a function on the circle by the tail of the coefficients it shares with `b`. -/
lemma norm_le_tsum_of_cf {Φ : ℂ → ℂ} (hΦ : ContinuousOn Φ (sphere 0 1)) {N : ℕ} {b : ℤ → ℂ}
    (hb : Summable fun m => ‖b m‖)
    (hcf : ∀ m, cf (fun θ => Φ (cexp (θ * I))) m = if N < m.natAbs then b m else 0) (θ : ℝ) :
    ‖Φ (cexp (θ * I))‖ ≤ ∑' m : ℤ, if N < m.natAbs then ‖b m‖ else 0 := by
  have hs : Summable fun m => ‖cf (fun θ => Φ (cexp (θ * I))) m‖ :=
    hb.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => by
      rw [hcf]; split_ifs <;> simp)
  have h := hasSum_cf_circle hΦ hs θ
  rw [← h.tsum_eq]
  have hn : ∀ m : ℤ, ‖cf (fun θ => Φ (cexp (θ * I))) m * cexp (m * θ * I)‖ =
      if N < m.natAbs then ‖b m‖ else 0 := fun m => by
    rw [norm_mul, norm_exp_int_mul_I, mul_one, hcf]; split_ifs <;> simp
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
  · simp_rw [hn]
    exact hb.of_nonneg_of_le (fun m => by split_ifs <;> simp) (fun m => by split_ifs <;> simp)
  · simp_rw [hn]

section Approx

variable {k R : ℝ} {ψ : ℂ → ℂ}

lemma polar_mem_closedBall {R2 ρ : ℝ} (hρ : ρ ∈ Ioc 0 R2) (θ : ℝ) :
    (ρ : ℂ) * cexp (θ * I) ∈ closedBall (0 : ℂ) R2 := by
  simpa [norm_mul, Complex.norm_exp_ofReal_mul_I, abs_of_pos hρ.1] using hρ.2

/-- Uniform Fourier tail bound for the values of `ψ` on circles. -/
lemma value_tail (hψ : IsHelmholtzOn k ψ (ball 0 R)) {R2 M : ℝ} (hR2 : R2 < R)
    (hM : ∀ z ∈ closedBall (0 : ℂ) R2, ‖fderiv ℝ ψ z‖ ≤ M) {ρ : ℝ} (hρ : ρ ∈ Ioc 0 R2)
    (N : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (fun m => ‖angCoeff ψ m ρ‖) ∧
      ∑' m : ℤ, (if N < m.natAbs then ‖angCoeff ψ m ρ‖ else 0) ≤
        t * (R2 * M) ^ 2 / 2 +
          (∑' m : ℤ, if N < m.natAbs then 1 / (m : ℝ) ^ 2 else 0) / (2 * t) := by
  have habs : |ρ| < R := by rw [abs_of_pos hρ.1]; linarith [hρ.2]
  have dF : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => ψ (ρ * cexp (θ * I)))
      (fderiv ℝ ψ (ρ * cexp (θ * I)) (ρ * cexp (θ * I) * I)) θ := fun θ =>
    (hψ.hasFDerivAt (polar_mem_ball θ habs)).comp_hasDerivAt θ (hasDerivAt_polar_angle ρ θ)
  have cF' : Continuous fun θ : ℝ => fderiv ℝ ψ (ρ * cexp (θ * I)) (ρ * cexp (θ * I) * I) :=
    (continuous_fderiv_polar_comp hψ habs).clm_apply (by fun_prop)
  have hper : (fun θ : ℝ => ψ (ρ * cexp (θ * I))) (2 * π) =
      (fun θ : ℝ => ψ (ρ * cexp (θ * I))) 0 := by
    simp only; rw [exp_two_pi_mul_I_eq]
  have hB : ∀ θ : ℝ, ‖fderiv ℝ ψ (ρ * cexp (θ * I)) (ρ * cexp (θ * I) * I)‖ ≤ R2 * M := by
    intro θ
    refine ((fderiv ℝ ψ _).le_opNorm _).trans ?_
    have hn : ‖(ρ : ℂ) * cexp (θ * I) * I‖ = ρ := by
      simp [Complex.norm_exp_ofReal_mul_I, abs_of_pos hρ.1]
    rw [hn]
    have h1 := hM _ (polar_mem_closedBall hρ θ)
    have h2 := norm_nonneg (fderiv ℝ ψ ((ρ : ℂ) * cexp (θ * I)))
    nlinarith [hρ.1, hρ.2]
  exact ⟨summable_norm_cf dF cF' hper hB, (cf_tail_le dF cF' hper hB N ht).2⟩

/-- Uniform Fourier tail bound for the derivative `Dψ(ρe^{iθ})(e^{iθ} c)`, `|c| = 1`. -/
lemma deriv_tail (hψ : IsHelmholtzOn k ψ (ball 0 R)) {R2 M : ℝ} (hR2 : R2 < R)
    (hM : ∀ z ∈ closedBall (0 : ℂ) R2, ‖fderiv ℝ ψ z‖ ≤ M ∧ ‖fderiv ℝ (fderiv ℝ ψ) z‖ ≤ M)
    {ρ : ℝ} (hρ : ρ ∈ Ioc 0 R2) (c : ℂ) (hc : ‖c‖ = 1) (N : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (fun m => ‖cf (fun θ : ℝ => fderiv ℝ ψ (ρ * cexp (θ * I)) (cexp (θ * I) * c)) m‖) ∧
      ∑' m : ℤ, (if N < m.natAbs then
          ‖cf (fun θ : ℝ => fderiv ℝ ψ (ρ * cexp (θ * I)) (cexp (θ * I) * c)) m‖ else 0) ≤
        t * ((R2 + 1) * M) ^ 2 / 2 +
          (∑' m : ℤ, if N < m.natAbs then 1 / (m : ℝ) ^ 2 else 0) / (2 * t) := by
  have habs : |ρ| < R := by rw [abs_of_pos hρ.1]; linarith [hρ.2]
  have dF := hasDerivAt_fderiv_polar hψ habs c
  have cL := continuous_fderiv_polar_comp hψ habs
  have cB := continuous_fderiv_fderiv_polar_comp hψ habs
  have cF' : Continuous fun θ : ℝ =>
      fderiv ℝ (fderiv ℝ ψ) (ρ * cexp (θ * I)) (ρ * cexp (θ * I) * I) (cexp (θ * I) * c) +
        fderiv ℝ ψ (ρ * cexp (θ * I)) (cexp (θ * I) * I * c) :=
    ((cB.clm_apply (by fun_prop)).clm_apply (by fun_prop)).add (cL.clm_apply (by fun_prop))
  have hper : (fun θ : ℝ => fderiv ℝ ψ (ρ * cexp (θ * I)) (cexp (θ * I) * c)) (2 * π) =
      (fun θ : ℝ => fderiv ℝ ψ (ρ * cexp (θ * I)) (cexp (θ * I) * c)) 0 := by
    simp only; rw [exp_two_pi_mul_I_eq]
  have hB : ∀ θ : ℝ, ‖fderiv ℝ (fderiv ℝ ψ) (ρ * cexp (θ * I)) (ρ * cexp (θ * I) * I)
      (cexp (θ * I) * c) + fderiv ℝ ψ (ρ * cexp (θ * I)) (cexp (θ * I) * I * c)‖ ≤
        (R2 + 1) * M := by
    intro θ
    obtain ⟨h1, h2⟩ := hM _ (polar_mem_closedBall hρ θ)
    have n1 : ‖(ρ : ℂ) * cexp (θ * I) * I‖ = ρ := by
      simp [Complex.norm_exp_ofReal_mul_I, abs_of_pos hρ.1]
    have n2 : ‖cexp (θ * I) * c‖ = 1 := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, hc, one_mul]
    have n3 : ‖cexp (θ * I) * I * c‖ = 1 := by
      rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, hc, Complex.norm_I]; norm_num
    have b1 : ‖fderiv ℝ (fderiv ℝ ψ) (ρ * cexp (θ * I)) (ρ * cexp (θ * I) * I)
        (cexp (θ * I) * c)‖ ≤ R2 * M := by
      refine ((fderiv ℝ (fderiv ℝ ψ) _).le_opNorm₂ _ _).trans ?_
      rw [n1, n2, mul_one]
      have := norm_nonneg (fderiv ℝ (fderiv ℝ ψ) ((ρ : ℂ) * cexp (θ * I)))
      nlinarith [hρ.1, hρ.2]
    have b2 : ‖fderiv ℝ ψ (ρ * cexp (θ * I)) (cexp (θ * I) * I * c)‖ ≤ M := by
      refine ((fderiv ℝ ψ _).le_opNorm _).trans ?_
      rw [n3, mul_one]; exact h1
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ R2 * M + M := add_le_add b1 b2
      _ = (R2 + 1) * M := by ring
  exact ⟨summable_norm_cf dF cF' hper hB, (cf_tail_le dF cF' hper hB N ht).2⟩

/-- **Herglotz approximation on a disk.** A solution of the Helmholtz equation `Δψ + k²ψ = 0`
(`k ≠ 0`) on the disk `B(0, R)` is approximated, together with its first derivatives, uniformly on
`B̄(0, R')` (`R' < R`) by Herglotz wave functions. -/
theorem herglotz_approx_ball (hk : k ≠ 0) (hψ : IsHelmholtzOn k ψ (ball 0 R)) {R' : ℝ}
    (hR' : R' < R) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : CircFun, ∀ z ∈ closedBall (0 : ℂ) R',
      ‖herglotzWave k a z - ψ z‖ < ε ∧ ‖fderiv ℝ (herglotzWave k a) z - fderiv ℝ ψ z‖ < ε := by
  rcases le_or_gt R 0 with hR | hR
  · refine ⟨0, fun z hz => absurd ((norm_nonneg z).trans (mem_closedBall_zero_iff.1 hz)) ?_⟩
    linarith
  set R2 := max R' (R / 2) with hR2def
  have hR2 : R2 < R := max_lt hR' (by linarith)
  have hR2pos : 0 < R2 := lt_max_of_lt_right (by linarith)
  have hsub : closedBall (0 : ℂ) R2 ⊆ ball 0 R := closedBall_subset_ball hR2
  obtain ⟨M1, hM1⟩ := (isCompact_closedBall (0 : ℂ) R2).exists_bound_of_continuousOn
    (hψ.continuousOn_fderiv.mono hsub)
  obtain ⟨M2, hM2⟩ := (isCompact_closedBall (0 : ℂ) R2).exists_bound_of_continuousOn
    (f := fderiv ℝ (fderiv ℝ ψ)) (hψ.continuousOn_fderiv_fderiv.mono hsub)
  set M := max M1 M2 with hMdef
  have hM : ∀ z ∈ closedBall (0 : ℂ) R2,
      ‖fderiv ℝ ψ z‖ ≤ M ∧ ‖fderiv ℝ (fderiv ℝ ψ) z‖ ≤ M := fun z hz =>
    ⟨(hM1 z hz).trans (le_max_left _ _), (hM2 z hz).trans (le_max_right _ _)⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp [hR2pos.le])).1
  set B := (R2 + 1) * M with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hRM : R2 * M ≤ B := by rw [hBdef]; nlinarith
  set t := ε / (8 * (B ^ 2 + 1)) with htdef
  have ht : 0 < t := by positivity
  have htB : t * B ^ 2 / 2 ≤ ε / 16 := by
    rw [htdef, div_mul_eq_mul_div, div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg B]
  have htRM : t * (R2 * M) ^ 2 / 2 ≤ ε / 16 := by
    refine le_trans ?_ htB
    have : (R2 * M) ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (by positivity) hRM 2
    have := mul_le_mul_of_nonneg_left this ht.le
    linarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ,
      (∑' m : ℤ, if N < m.natAbs then 1 / (m : ℝ) ^ 2 else 0) / (2 * t) < ε / 16 := by
    have hδ : 0 < ε / 16 * (2 * t) := by positivity
    obtain ⟨N, hN⟩ := ((tendsto_order.1 tendsto_int_tail).2 _ hδ).exists
    exact ⟨N, (div_lt_iff₀ (by positivity)).2 hN⟩
  choose c hc using fun n => angCoeff_eq_smul_fbWave hk hψ n hR
  set s := Finset.Icc (-(N : ℤ)) N with hs
  refine ⟨∑ n ∈ s, c n • fourier n, ?_⟩
  set S := herglotzWave k (∑ n ∈ s, c n • fourier n) with hSdef
  have hSfun : S = fun z => ∑ n ∈ s, c n * fbWave k n z :=
    funext fun z => herglotzWave_finset_sum k s c (fun n => fourier n) z
  have hSH : IsHelmholtzOn k S (ball 0 R) := isHelmholtzOn_herglotzWave _ _ _
  set g : ℂ → ℂ := fun z => ψ z - S z with hgdef
  have hg : IsHelmholtzOn k g (ball 0 R) := IsHelmholtzOn.sub isOpen_ball hψ hSH
  have hmem : ∀ m : ℤ, m ∈ s ↔ ¬ N < m.natAbs := by
    intro m; simp only [hs, Finset.mem_Icc]; omega
  -- the coefficients of `g = ψ - S` on circles
  have hcoef0 : ∀ ρ ∈ Ioo 0 R, ∀ m : ℤ,
      angCoeff g m ρ = if N < m.natAbs then angCoeff ψ m ρ else 0 := by
    intro ρ hρ m
    have habs : |ρ| < R := by rw [abs_of_pos hρ.1]; exact hρ.2
    rw [hgdef, angCoeff_sub hψ.continuousOn hSH.continuousOn m habs, hSfun,
      angCoeff_finset_sum s c (fun n => fbWave k n)
        (fun n _ => (continuous_fbWave k n).continuousOn) m habs]
    simp_rw [angCoeff_fbWave, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq]
    by_cases hm : N < m.natAbs
    · have : m ∉ s := fun h => (hmem m).1 h hm
      simp [hm, this]
    · have : m ∈ s := (hmem m).2 hm
      simp [hm, this, hc m ρ hρ]
  have hcoef1 : ∀ ρ ∈ Ioo 0 R, ∀ m : ℤ,
      angCoeffD g m ρ = if N < m.natAbs then angCoeffD ψ m ρ else 0 := by
    intro ρ hρ m
    have h1 := angCoeff_hasDerivAt hg m hρ
    have h2 : HasDerivAt (fun σ => if N < m.natAbs then angCoeff ψ m σ else 0)
        (if N < m.natAbs then angCoeffD ψ m ρ else 0) ρ := by
      split_ifs
      · exact angCoeff_hasDerivAt hψ m hρ
      · exact hasDerivAt_const _ _
    have hev : angCoeff g m =ᶠ[𝓝 ρ] fun σ => if N < m.natAbs then angCoeff ψ m σ else 0 :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hρ) fun σ hσ => hcoef0 σ hσ m
    exact h1.unique (h2.congr_of_eventuallyEq hev)
  have hcoefT : ∀ ρ ∈ Ioo 0 R, ∀ m : ℤ,
      angCoeffT g m ρ = if N < m.natAbs then angCoeffT ψ m ρ else 0 := by
    intro ρ hρ m
    rw [angCoeffT_eq hg hρ, angCoeffT_eq hψ hρ, hcoef0 ρ hρ m]
    split_ifs <;> simp
  -- pointwise bounds away from the origin
  have hbound : ∀ z ∈ closedBall (0 : ℂ) R2, z ≠ 0 →
      ‖g z‖ ≤ ε / 8 ∧ ‖fderiv ℝ g z‖ ≤ ε / 4 := by
    intro z hz hz0
    set ρ := ‖z‖ with hρdef
    set θ := arg z with hθdef
    have hρ : ρ ∈ Ioc 0 R2 := ⟨norm_pos_iff.2 hz0, mem_closedBall_zero_iff.1 hz⟩
    have hρR : ρ ∈ Ioo 0 R := ⟨hρ.1, hρ.2.trans_lt hR2⟩
    have habs : |ρ| < R := by rw [abs_of_pos hρ.1]; exact hρR.2
    have hzρ : z = ρ * cexp (θ * I) := (Complex.norm_mul_exp_arg_mul_I z).symm
    have hmapsto : ∀ e ∈ sphere (0 : ℂ) 1, (ρ : ℂ) * e ∈ ball (0 : ℂ) R := fun e he => by
      have : ‖e‖ = 1 := by simpa using he
      simpa [norm_mul, this, abs_of_pos hρ.1] using habs
    have hcm : ContinuousOn (fun e : ℂ => (ρ : ℂ) * e) (sphere 0 1) := by fun_prop
    -- value
    have hv := value_tail hψ hR2 (fun z hz => (hM z hz).1) hρ N ht
    have hval : ‖g z‖ ≤ ∑' m : ℤ, if N < m.natAbs then ‖angCoeff ψ m ρ‖ else 0 := by
      rw [hzρ]
      exact norm_le_tsum_of_cf (Φ := fun e => g (ρ * e)) (hg.continuousOn.comp hcm hmapsto)
        hv.1 (fun m => hcoef0 ρ hρR m) θ
    -- radial derivative
    have hr := deriv_tail hψ hR2 hM hρ 1 (by simp) N ht
    simp only [mul_one] at hr
    have hrad : ‖fderiv ℝ g z (cexp (θ * I))‖ ≤ ∑' m : ℤ, if N < m.natAbs then
        ‖cf (fun θ : ℝ => fderiv ℝ ψ (ρ * cexp (θ * I)) (cexp (θ * I))) m‖ else 0 := by
      rw [hzρ]
      exact norm_le_tsum_of_cf (Φ := fun e => fderiv ℝ g (ρ * e) e)
        ((hg.continuousOn_fderiv.comp hcm hmapsto).clm_apply continuousOn_id)
        hr.1 (fun m => hcoef1 ρ hρR m) θ
    -- tangential derivative
    have hT := deriv_tail hψ hR2 hM hρ I (by simp) N ht
    have htan : ‖fderiv ℝ g z (cexp (θ * I) * I)‖ ≤ ∑' m : ℤ, if N < m.natAbs then
        ‖cf (fun θ : ℝ => fderiv ℝ ψ (ρ * cexp (θ * I)) (cexp (θ * I) * I)) m‖ else 0 := by
      rw [hzρ]
      exact norm_le_tsum_of_cf (Φ := fun e => fderiv ℝ g (ρ * e) (e * I))
        ((hg.continuousOn_fderiv.comp hcm hmapsto).clm_apply (by fun_prop))
        hT.1 (fun m => hcoefT ρ hρR m) θ
    refine ⟨?_, ?_⟩
    · linarith [hv.2]
    · have hnorm := norm_clm_le_two (fderiv ℝ g z) (Complex.norm_exp_ofReal_mul_I θ)
      linarith [hr.2, hT.2]
  -- conclusion
  have hgS : ∀ z ∈ ball (0 : ℂ) R, ‖S z - ψ z‖ = ‖g z‖ ∧
      ‖fderiv ℝ S z - fderiv ℝ ψ z‖ = ‖fderiv ℝ g z‖ := by
    intro z hz
    refine ⟨norm_sub_rev _ _, ?_⟩
    have hd1 : DifferentiableAt ℝ ψ z := (hψ.hasFDerivAt hz).differentiableAt
    have hd2 : DifferentiableAt ℝ S z := (hSH.hasFDerivAt hz).differentiableAt
    rw [hgdef, fderiv_fun_sub hd1 hd2, norm_sub_rev]
  have hcont1 : ContinuousAt (fun z => ‖g z‖) 0 :=
    (hg.continuousOn.continuousAt (isOpen_ball.mem_nhds (by simpa using hR))).norm
  have hcont2 : ContinuousAt (fun z => ‖fderiv ℝ g z‖) 0 :=
    (hg.continuousOn_fderiv.continuousAt (isOpen_ball.mem_nhds (by simpa using hR))).norm
  have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ closedBall (0 : ℂ) R2 ∧ z ≠ 0 := by
    filter_upwards [inter_mem_nhdsWithin ({0}ᶜ : Set ℂ) (closedBall_mem_nhds (0 : ℂ) hR2pos)]
      with z hz
    exact ⟨hz.2, hz.1⟩
  have hbound' : ∀ z ∈ closedBall (0 : ℂ) R2, ‖g z‖ ≤ ε / 8 ∧ ‖fderiv ℝ g z‖ ≤ ε / 4 := by
    intro z hz
    by_cases hz0 : z = 0
    · subst hz0
      refine ⟨le_of_tendsto
          (hcont1.tendsto.mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))) ?_,
        le_of_tendsto
          (hcont2.tendsto.mono_left (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))) ?_⟩
      · filter_upwards [hev] with w hw using (hbound w hw.1 hw.2).1
      · filter_upwards [hev] with w hw using (hbound w hw.1 hw.2).2
    · exact hbound z hz hz0
  intro z hz
  have hz2 : z ∈ closedBall (0 : ℂ) R2 :=
    closedBall_subset_closedBall (le_max_left _ _) hz
  obtain ⟨e1, e2⟩ := hgS z (hsub hz2)
  obtain ⟨b1, b2⟩ := hbound' z hz2
  exact ⟨by rw [e1]; linarith, by rw [e2]; linarith⟩

end Approx

end

section

/-! ## Angular Fourier coefficients of Helmholtz solutions on annuli -/

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory Set Real Metric Complex Filter Topology

/-- The open annulus `a < |z| < b`. -/
def annulus (a b : ℝ) : Set ℂ := {z | a < ‖z‖ ∧ ‖z‖ < b}

lemma isOpen_annulus (a b : ℝ) : IsOpen (annulus a b) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

lemma polar_mem_annulus {a b ρ : ℝ} (θ : ℝ) (hρ : |ρ| ∈ Ioo a b) :
    (ρ : ℂ) * cexp (θ * I) ∈ annulus a b := by
  have : ‖(ρ : ℂ) * cexp (θ * I)‖ = |ρ| := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  simp only [annulus, mem_setOf_eq, this]
  exact hρ

section HelmholtzAnn

variable {k a b : ℝ} {ψ : ℂ → ℂ}

lemma ann_contDiffOn_fderiv (hψ : IsHelmholtzOn k ψ (annulus a b)) :
    ContDiffOn ℝ 1 (fderiv ℝ ψ) (annulus a b) :=
  hψ.1.fderiv_of_isOpen (isOpen_annulus a b) (by norm_num)

lemma ann_hasFDerivAt (hψ : IsHelmholtzOn k ψ (annulus a b)) {z : ℂ}
    (hz : z ∈ annulus a b) : HasFDerivAt ψ (fderiv ℝ ψ z) z :=
  ((hψ.1.differentiableOn (by norm_num)).differentiableAt ((isOpen_annulus a b).mem_nhds hz)).hasFDerivAt

lemma ann_hasFDerivAt_fderiv (hψ : IsHelmholtzOn k ψ (annulus a b)) {z : ℂ}
    (hz : z ∈ annulus a b) :
    HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) z) z :=
  (((ann_contDiffOn_fderiv hψ).differentiableOn (by norm_num)).differentiableAt
    ((isOpen_annulus a b).mem_nhds hz)).hasFDerivAt

lemma ann_continuousOn (hψ : IsHelmholtzOn k ψ (annulus a b)) :
    ContinuousOn ψ (annulus a b) := hψ.1.continuousOn

lemma ann_continuousOn_fderiv (hψ : IsHelmholtzOn k ψ (annulus a b)) :
    ContinuousOn (fderiv ℝ ψ) (annulus a b) := (ann_contDiffOn_fderiv hψ).continuousOn

lemma ann_continuousOn_fderiv_fderiv (hψ : IsHelmholtzOn k ψ (annulus a b)) :
    ContinuousOn (fderiv ℝ (fderiv ℝ ψ)) (annulus a b) :=
  (ann_contDiffOn_fderiv hψ).continuousOn_fderiv_of_isOpen (isOpen_annulus a b) le_rfl

/-- Pointwise polar form of the Helmholtz equation:
`ρ² ∂²_ρ g + ∂²_θ g + ρ ∂_ρ g + k² ρ² g = 0` at `z = ρ e^{iθ}`. -/
lemma helmholtz_polar_ann (hψ : IsHelmholtzOn k ψ (annulus a b)) {ρ : ℝ} (θ : ℝ) (hρ : |ρ| ∈ Ioo a b) :
    let z := (ρ : ℂ) * cexp (θ * I)
    let e := cexp (θ * I)
    (ρ : ℂ) ^ 2 * fderiv ℝ (fderiv ℝ ψ) z e e +
      (fderiv ℝ (fderiv ℝ ψ) z (z * I) (z * I) + fderiv ℝ ψ z (z * I * I)) +
      ρ * fderiv ℝ ψ z e + (k : ℂ) ^ 2 * (ρ : ℂ) ^ 2 * ψ z = 0 := by
  intro z e
  have hz : z ∈ annulus a b := polar_mem_annulus θ hρ
  have hH := hψ.2 z hz
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane] at hH
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hH
  have hrot := bilin_rot_trace (fderiv ℝ (fderiv ℝ ψ) z) e (Complex.norm_exp_ofReal_mul_I θ)
  set B := fderiv ℝ (fderiv ℝ ψ) z
  set L := fderiv ℝ ψ z
  have hzI : z * I = (ρ : ℝ) • (e * I) := by simp [z, e, real_smul, mul_assoc]
  have hzII : z * I * I = (-ρ : ℝ) • e := by
    simp only [z, e, real_smul, mul_assoc, Complex.I_mul_I]; push_cast; ring
  rw [hzII, hzI, ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.map_smul]
  simp only [real_smul]
  push_cast
  linear_combination (ρ : ℂ) ^ 2 * hH + (ρ : ℂ) ^ 2 * hrot

lemma polar_mapsTo_ann {ρ δ : ℝ} (ha : 0 ≤ a) (h0 : a < ρ - δ) (h1 : ρ + δ < b) :
    MapsTo (fun p : ℝ × ℝ => (p.1 : ℂ) * cexp (p.2 * I)) (Icc (ρ - δ) (ρ + δ) ×ˢ Icc 0 (2 * π))
      (annulus a b) := by
  intro p hp
  refine polar_mem_annulus p.2 ?_
  rw [abs_of_pos (by linarith [hp.1.1])]
  exact ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩

lemma continuous_polar_comp_ann (hψ : IsHelmholtzOn k ψ (annulus a b)) {ρ : ℝ} (hρ : |ρ| ∈ Ioo a b) :
    Continuous fun θ : ℝ => ψ ((ρ : ℂ) * cexp (θ * I)) :=
  (ann_continuousOn hψ).comp_continuous (by fun_prop) fun θ => polar_mem_annulus θ hρ

lemma continuous_fderiv_polar_comp_ann (hψ : IsHelmholtzOn k ψ (annulus a b)) {ρ : ℝ} (hρ : |ρ| ∈ Ioo a b) :
    Continuous fun θ : ℝ => fderiv ℝ ψ ((ρ : ℂ) * cexp (θ * I)) :=
  (ann_continuousOn_fderiv hψ).comp_continuous (by fun_prop) fun θ => polar_mem_annulus θ hρ

lemma continuous_fderiv_fderiv_polar_comp_ann (hψ : IsHelmholtzOn k ψ (annulus a b)) {ρ : ℝ}
    (hρ : |ρ| ∈ Ioo a b) :
    Continuous fun θ : ℝ => fderiv ℝ (fderiv ℝ ψ) ((ρ : ℂ) * cexp (θ * I)) :=
  (ann_continuousOn_fderiv_fderiv hψ).comp_continuous (by fun_prop) fun θ => polar_mem_annulus θ hρ

lemma angCoeff_hasDerivAt_ann (hψ : IsHelmholtzOn k ψ (annulus a b)) (n : ℤ) {ρ : ℝ}
    (ha : 0 ≤ a) (hρ : ρ ∈ Ioo a b) : HasDerivAt (angCoeff ψ n) (angCoeffD ψ n ρ) ρ := by
  set δ := min (ρ - a) (b - ρ) / 2 with hδ
  have hδ0 : 0 < δ := by have := lt_min (sub_pos.2 hρ.1) (sub_pos.2 hρ.2); positivity
  have h0 : a < ρ - δ := by have := min_le_left (ρ - a) (b - ρ); linarith
  have h1 : ρ + δ < b := by have := min_le_right (ρ - a) (b - ρ); linarith
  have habs : ∀ ρ' ∈ Ioo (ρ - δ) (ρ + δ), |ρ'| ∈ Ioo a b := fun ρ' h' => by
    rw [abs_of_pos (by linarith [h'.1])]; exact ⟨by linarith [h'.1], by linarith [h'.2]⟩
  refine HasDerivAt.const_mul _ (hasDerivAt_intervalIntegral_param
    (G := fun ρ θ => cexp (-(n * θ * I)) * ψ (ρ * cexp (θ * I)))
    (G' := fun ρ θ => cexp (-(n * θ * I)) * fderiv ℝ ψ (ρ * cexp (θ * I)) (cexp (θ * I))) hδ0
    (fun ρ' h' => (by fun_prop : Continuous fun θ : ℝ => cexp (-(n * θ * I))).mul
      (continuous_polar_comp_ann hψ (habs ρ' h'))) ?_ ?_)
  · refine ContinuousOn.mul (by fun_prop) ?_
    exact ((ann_continuousOn_fderiv hψ).comp continuous_polar.continuousOn (polar_mapsTo_ann ha h0 h1)).clm_apply
      (by fun_prop)
  · intro ρ' h' θ
    have hz := polar_mem_annulus θ (habs ρ' h')
    exact (((ann_hasFDerivAt hψ) hz).comp_hasDerivAt ρ' (hasDerivAt_ofReal_mul _ ρ')).const_mul _

lemma angCoeffD_hasDerivAt_ann (hψ : IsHelmholtzOn k ψ (annulus a b)) (n : ℤ) {ρ : ℝ}
    (ha : 0 ≤ a) (hρ : ρ ∈ Ioo a b) : HasDerivAt (angCoeffD ψ n) (angCoeffD2 ψ n ρ) ρ := by
  set δ := min (ρ - a) (b - ρ) / 2 with hδ
  have hδ0 : 0 < δ := by have := lt_min (sub_pos.2 hρ.1) (sub_pos.2 hρ.2); positivity
  have h0 : a < ρ - δ := by have := min_le_left (ρ - a) (b - ρ); linarith
  have h1 : ρ + δ < b := by have := min_le_right (ρ - a) (b - ρ); linarith
  have habs : ∀ ρ' ∈ Ioo (ρ - δ) (ρ + δ), |ρ'| ∈ Ioo a b := fun ρ' h' => by
    rw [abs_of_pos (by linarith [h'.1])]; exact ⟨by linarith [h'.1], by linarith [h'.2]⟩
  refine HasDerivAt.const_mul _ (hasDerivAt_intervalIntegral_param
    (G := fun ρ θ => cexp (-(n * θ * I)) * fderiv ℝ ψ (ρ * cexp (θ * I)) (cexp (θ * I)))
    (G' := fun ρ θ => cexp (-(n * θ * I)) *
      fderiv ℝ (fderiv ℝ ψ) (ρ * cexp (θ * I)) (cexp (θ * I)) (cexp (θ * I))) hδ0
    (fun ρ' h' => (by fun_prop : Continuous fun θ : ℝ => cexp (-(n * θ * I))).mul
      ((continuous_fderiv_polar_comp_ann hψ (habs ρ' h')).clm_apply (by fun_prop))) ?_ ?_)
  · refine ContinuousOn.mul (by fun_prop) ?_
    exact (((ann_continuousOn_fderiv_fderiv hψ).comp continuous_polar.continuousOn
      (polar_mapsTo_ann ha h0 h1)).clm_apply (by fun_prop)).clm_apply (by fun_prop)
  · intro ρ' h' θ
    have hz := polar_mem_annulus θ (habs ρ' h')
    have h1 : HasDerivAt (fun ρ : ℝ => fderiv ℝ ψ (ρ * cexp (θ * I)))
        (fderiv ℝ (fderiv ℝ ψ) (ρ' * cexp (θ * I)) (cexp (θ * I))) ρ' :=
      ((ann_hasFDerivAt_fderiv hψ) hz).comp_hasDerivAt ρ' (hasDerivAt_ofReal_mul (cexp (θ * I)) ρ')
    have h2 := h1.clm_apply (hasDerivAt_const ρ' (cexp (θ * I)))
    rw [ContinuousLinearMap.map_zero, add_zero] at h2
    exact h2.const_mul _

lemma angCoeffD2_eq_ann (hψ : IsHelmholtzOn k ψ (annulus a b)) (n : ℤ) {ρ : ℝ} (ha : 0 ≤ a)
    (hρ : ρ ∈ Ioo a b) :
    angCoeffD2 ψ n ρ = -(angCoeffD ψ n ρ) / ρ -
      ((k : ℂ) ^ 2 - (n : ℂ) ^ 2 / (ρ : ℂ) ^ 2) * angCoeff ψ n ρ := by
  have habs : |ρ| ∈ Ioo a b := by rw [abs_of_pos (ha.trans_lt hρ.1)]; exact hρ
  obtain ⟨z, hz⟩ : ∃ z : ℝ → ℂ, z = fun θ : ℝ => (ρ : ℂ) * cexp (θ * I) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℂ, F = fun θ => ψ (z θ) := ⟨_, rfl⟩
  obtain ⟨F1, hF1⟩ : ∃ F1 : ℝ → ℂ, F1 = fun θ => fderiv ℝ ψ (z θ) (z θ * I) := ⟨_, rfl⟩
  obtain ⟨F2, hF2⟩ : ∃ F2 : ℝ → ℂ, F2 = fun θ =>
    fderiv ℝ (fderiv ℝ ψ) (z θ) (z θ * I) (z θ * I) + fderiv ℝ ψ (z θ) (z θ * I * I) :=
    ⟨_, rfl⟩
  obtain ⟨G1, hG1⟩ : ∃ G1 : ℝ → ℂ, G1 = fun θ : ℝ => fderiv ℝ ψ (z θ) (cexp (θ * I)) :=
    ⟨_, rfl⟩
  obtain ⟨G2, hG2⟩ : ∃ G2 : ℝ → ℂ, G2 = fun θ : ℝ =>
    fderiv ℝ (fderiv ℝ ψ) (z θ) (cexp (θ * I)) (cexp (θ * I)) := ⟨_, rfl⟩
  have cL : Continuous fun θ => fderiv ℝ ψ (z θ) := by
    rw [hz]; exact continuous_fderiv_polar_comp_ann hψ habs
  have cB : Continuous fun θ => fderiv ℝ (fderiv ℝ ψ) (z θ) := by
    rw [hz]; exact continuous_fderiv_fderiv_polar_comp_ann hψ habs
  have hzc : Continuous z := by rw [hz]; fun_prop
  have ce : Continuous fun θ : ℝ => cexp (θ * I) := by fun_prop
  have cu : Continuous fun θ : ℝ => cexp (-(n * θ * I)) := by fun_prop
  have cF : Continuous F := by rw [hF, hz]; exact continuous_polar_comp_ann hψ habs
  have cF1 : Continuous F1 := by rw [hF1]; exact cL.clm_apply (hzc.mul continuous_const)
  have cF2 : Continuous F2 := by
    rw [hF2]
    exact ((cB.clm_apply (hzc.mul continuous_const)).clm_apply (hzc.mul continuous_const)).add
      (cL.clm_apply ((hzc.mul continuous_const).mul continuous_const))
  have cG1 : Continuous G1 := by rw [hG1]; exact cL.clm_apply ce
  have cG2 : Continuous G2 := by rw [hG2]; exact (cB.clm_apply ce).clm_apply ce
  have hzm : ∀ θ, z θ ∈ annulus a b := fun θ => by rw [hz]; exact polar_mem_annulus θ habs
  have hzd : ∀ θ, HasDerivAt z (z θ * I) θ := fun θ => by
    rw [hz]; exact hasDerivAt_polar_angle ρ θ
  have dF : ∀ θ, HasDerivAt F (F1 θ) θ := fun θ => by
    rw [hF, hF1]; exact ((ann_hasFDerivAt hψ) (hzm θ)).comp_hasDerivAt θ (hzd θ)
  have dF1 : ∀ θ, HasDerivAt F1 (F2 θ) θ := fun θ => by
    rw [hF1, hF2]
    exact (((ann_hasFDerivAt_fderiv hψ) (hzm θ)).comp_hasDerivAt θ (hzd θ)).clm_apply
      ((hzd θ).mul_const I)
  have hz2 : z (2 * π) = z 0 := by
    rw [hz]
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
    rw [show ((2 * π : ℝ) : ℂ) * I = 2 * π * I by push_cast; ring, Complex.exp_two_pi_mul_I,
      mul_one]
  have pF : F (2 * π) = F 0 := by rw [hF]; simp only [hz2]
  have pF1 : F1 (2 * π) = F1 0 := by rw [hF1]; simp only [hz2]
  have i1 := integral_exp_mul_deriv_of_periodic dF cF1 pF n
  have i2 := integral_exp_mul_deriv_of_periodic dF1 cF2 pF1 n
  have hpt : ∀ θ : ℝ, (ρ : ℂ) ^ 2 * G2 θ + F2 θ + ρ * G1 θ + (k : ℂ) ^ 2 * (ρ : ℂ) ^ 2 * F θ
      = 0 := fun θ => by
    have := helmholtz_polar_ann hψ θ habs
    rw [hG2, hF2, hG1, hF, hz]
    exact this
  have hsplit : ∀ θ : ℝ, cexp (-(n * θ * I)) * ((ρ : ℂ) ^ 2 * G2 θ + F2 θ + ρ * G1 θ +
      (k : ℂ) ^ 2 * (ρ : ℂ) ^ 2 * F θ) = (ρ : ℂ) ^ 2 * (cexp (-(n * θ * I)) * G2 θ) +
      cexp (-(n * θ * I)) * F2 θ + ρ * (cexp (-(n * θ * I)) * G1 θ) +
      (k : ℂ) ^ 2 * (ρ : ℂ) ^ 2 * (cexp (-(n * θ * I)) * F θ) := fun θ => by ring
  have hint : (ρ : ℂ) ^ 2 * (∫ θ in (0 : ℝ)..2 * π, cexp (-(n * θ * I)) * G2 θ) +
      (∫ θ in (0 : ℝ)..2 * π, cexp (-(n * θ * I)) * F2 θ) +
      ρ * (∫ θ in (0 : ℝ)..2 * π, cexp (-(n * θ * I)) * G1 θ) +
      (k : ℂ) ^ 2 * (ρ : ℂ) ^ 2 * (∫ θ in (0 : ℝ)..2 * π, cexp (-(n * θ * I)) * F θ) = 0 := by
    have h0 : ∫ θ in (0 : ℝ)..2 * π, cexp (-(n * θ * I)) * ((ρ : ℂ) ^ 2 * G2 θ + F2 θ +
        ρ * G1 θ + (k : ℂ) ^ 2 * (ρ : ℂ) ^ 2 * F θ) = 0 := by simp [hpt]
    rw [intervalIntegral.integral_congr (fun θ _ => hsplit θ)] at h0
    have c2 := continuous_const (y := (ρ : ℂ) ^ 2) |>.mul (cu.mul cG2)
    have c1 := continuous_const (y := (ρ : ℂ)) |>.mul (cu.mul cG1)
    have c0 := continuous_const (y := (k : ℂ) ^ 2 * (ρ : ℂ) ^ 2) |>.mul (cu.mul cF)
    rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h0
    · exact h0
    · exact c2.intervalIntegrable _ _
    · exact (cu.mul cF2).intervalIntegrable _ _
    · exact (c2.add (cu.mul cF2)).intervalIntegrable _ _
    · exact c1.intervalIntegrable _ _
    · exact ((c2.add (cu.mul cF2)).add c1).intervalIntegrable _ _
    · exact c0.intervalIntegrable _ _
  have hD2 : angCoeffD2 ψ n ρ = (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
      cexp (-(n * θ * I)) * G2 θ := by rw [hG2, hz]; rfl
  have hD1 : angCoeffD ψ n ρ = (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
      cexp (-(n * θ * I)) * G1 θ := by rw [hG1, hz]; rfl
  have hD0 : angCoeff ψ n ρ = (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
      cexp (-(n * θ * I)) * F θ := by rw [hF, hz]; rfl
  rw [hD2, hD1, hD0]
  rw [i2, i1] at hint
  have hρ0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast (ha.trans_lt hρ.1).ne'
  generalize (∫ θ in (0 : ℝ)..2 * π, cexp (-(n * θ * I)) * G2 θ) = A2 at hint ⊢
  generalize (∫ θ in (0 : ℝ)..2 * π, cexp (-(n * θ * I)) * G1 θ) = A1 at hint ⊢
  generalize (∫ θ in (0 : ℝ)..2 * π, cexp (-(n * θ * I)) * F θ) = A0 at hint ⊢
  field_simp
  linear_combination hint - (n : ℂ) ^ 2 * A0 * I_sq

/-- **Separation of variables on annuli.** -/
theorem angCoeff_bessel_ann (hψ : IsHelmholtzOn k ψ (annulus a b)) (n : ℤ) (ha : 0 ≤ a) {ρ : ℝ}
    (hρ : ρ ∈ Ioo a b) :
    HasDerivAt (angCoeff ψ n) (angCoeffD ψ n ρ) ρ ∧
      HasDerivAt (angCoeffD ψ n)
        (-(angCoeffD ψ n ρ) / ρ - ((k : ℂ) ^ 2 - (n : ℂ) ^ 2 / (ρ : ℂ) ^ 2) * angCoeff ψ n ρ) ρ :=
  ⟨angCoeff_hasDerivAt_ann hψ n ha hρ,
    angCoeffD2_eq_ann hψ n ha hρ ▸ angCoeffD_hasDerivAt_ann hψ n ha hρ⟩

end HelmholtzAnn

end

section

/-! ## Unique continuation for the Helmholtz equation -/

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory Set Real Metric Complex Filter Topology

/-- Translation invariance of the Helmholtz equation. -/
lemma IsHelmholtzOn.comp_add {k : ℝ} {u : ℂ → ℂ} {Ω : Set ℂ} (h : IsHelmholtzOn k u Ω) (c : ℂ) :
    IsHelmholtzOn k (fun z => u (c + z)) ((fun z => c + z) ⁻¹' Ω) := by
  refine ⟨h.1.comp (contDiff_const.add contDiff_id).contDiffOn fun z hz => hz, fun z hz => ?_⟩
  have e := h.2 (c + z) hz
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane] at e ⊢
  simp only [iteratedFDeriv_comp_add_left] at *
  exact e

lemma preimage_add_ball_self (c : ℂ) (δ : ℝ) : (fun z => c + z) ⁻¹' ball c δ = ball 0 δ := by
  ext z; simp [dist_eq_norm]

/-- A solution on `B(0, δ)` vanishing on `B(0, ε)` vanishes on `B(0, δ)`. -/
lemma helmholtz_ball_eq_zero {k : ℝ} (hk : k ≠ 0) {u : ℂ → ℂ} {δ ε : ℝ} (hε : 0 < ε)
    (hu : IsHelmholtzOn k u (ball 0 δ)) (hz : ∀ z ∈ ball (0 : ℂ) ε, u z = 0) :
    ∀ z ∈ ball (0 : ℂ) δ, u z = 0 := by
  intro z hzδ
  by_cases hzε : z ∈ ball (0 : ℂ) ε
  · exact hz z hzε
  have hδ : 0 < δ := (norm_nonneg z).trans_lt (by simpa using hzδ)
  set ε' := min ε δ with hε'
  have hε'0 : 0 < ε' := lt_min hε hδ
  -- all angular coefficients vanish on `(0, δ)`
  have hcoef : ∀ (n : ℤ), ∀ ρ ∈ Ioo 0 δ, angCoeff u n ρ = 0 := by
    intro n ρ hρ
    obtain ⟨c, hc⟩ := angCoeff_eq_smul_fbWave hk hu n hδ
    obtain ⟨ρ₀, hρ₀, hne⟩ := fbWave_exists_ne_zero hk n hε'0
    have h0 : angCoeff u n ρ₀ = 0 := by
      unfold angCoeff
      have : ∀ θ : ℝ, cexp (-(n * θ * I)) * u (ρ₀ * cexp (θ * I)) = 0 := fun θ => by
        rw [hz, mul_zero]
        simp [Complex.norm_exp_ofReal_mul_I, abs_of_pos hρ₀.1,
          hρ₀.2.trans_le (min_le_left _ _)]
      simp [this]
    have hc0 : c = 0 := by
      have := hc ρ₀ ⟨hρ₀.1, hρ₀.2.trans_le (min_le_right _ _)⟩
      rw [h0] at this
      exact (mul_eq_zero.1 this.symm).resolve_right hne
    rw [hc ρ hρ, hc0, zero_mul]
  -- hence `u` vanishes on the circle through `z`
  set ρ := ‖z‖ with hρdef
  have hρ : ρ ∈ Ioo 0 δ := by
    refine ⟨?_, by simpa using hzδ⟩
    rcases (norm_nonneg z).lt_or_eq with h | h
    · exact h
    · exact absurd (by simp [← h, hε] : z ∈ ball (0 : ℂ) ε) hzε
  set Φ : ℂ → ℂ := fun w => u (ρ * w)
  have hΦ : ContinuousOn Φ (sphere 0 1) := by
    refine hu.1.continuousOn.comp (continuousOn_const.mul continuousOn_id) fun w hw => ?_
    simp only [mem_sphere_iff_norm, sub_zero] at hw
    simp [hw, abs_of_pos hρ.1, hρ.2]
  have hcf : ∀ m : ℤ, cf (fun θ : ℝ => Φ (cexp (θ * I))) m =
      if 0 < m.natAbs then (0 : ℤ → ℂ) m else 0 := by
    intro m
    rw [← angCoeff_eq_cf, hcoef m ρ hρ]
    simp
  have hle := norm_le_tsum_of_cf hΦ (N := 0) (b := 0) (by simp) hcf (arg z)
  simp only [Pi.zero_apply, norm_zero, ite_self, tsum_zero, norm_le_zero_iff] at hle
  have : (ρ : ℂ) * cexp (arg z * I) = z := by
    rw [hρdef]; exact Complex.norm_mul_exp_arg_mul_I z
  simpa [Φ, this] using hle

/-- **Unique continuation for the Helmholtz equation.** -/
theorem helmholtz_eq_zero_of_isPreconnected {k : ℝ} (hk : k ≠ 0) {O V : Set ℂ} (hO : IsOpen O)
    (hOc : IsPreconnected O) {u : ℂ → ℂ} (hu : IsHelmholtzOn k u O) (hV : IsOpen V)
    (hVne : V.Nonempty) (hVO : V ⊆ O) (hzero : ∀ z ∈ V, u z = 0) : ∀ z ∈ O, u z = 0 := by
  set Z := {z : ℂ | ∀ᶠ w in 𝓝 z, u w = 0} with hZ
  have hZo : IsOpen Z := isOpen_iff_mem_nhds.2 fun z hz => hz.eventually_nhds
  obtain ⟨v, hv⟩ := hVne
  have hvZ : v ∈ Z := Filter.eventually_of_mem (hV.mem_nhds hv) hzero
  have hsub : O ⊆ Z := by
    refine hOc.subset_of_closure_inter_subset hZo ⟨v, hVO hv, hvZ⟩ ?_
    rintro p ⟨hpcl, hpO⟩
    obtain ⟨δ, hδ, hδO⟩ := Metric.isOpen_iff.1 hO p hpO
    obtain ⟨q, hqB, hqZ⟩ := mem_closure_iff.1 hpcl (ball p (δ / 2)) isOpen_ball
      (mem_ball_self (by linarith))
    obtain ⟨ε, hε, hεq⟩ := Metric.eventually_nhds_iff_ball.1 hqZ
    have hqδ : ball q (δ / 2) ⊆ O := by
      refine Subset.trans (fun w hw => ?_) hδO
      rw [mem_ball] at hw hqB ⊢
      calc dist w p ≤ dist w q + dist q p := dist_triangle _ _ _
        _ < δ / 2 + δ / 2 := add_lt_add hw hqB
        _ = δ := by ring
    have hv' : IsHelmholtzOn k (fun z => u (q + z)) (ball 0 (δ / 2)) := by
      rw [← preimage_add_ball_self q]
      exact (hu.mono hqδ).comp_add q
    have hzero' := helmholtz_ball_eq_zero hk hε hv' (fun z hz => hεq _ (by
      simpa [dist_eq_norm] using hz))
    have hpq : p ∈ ball q (δ / 2) := by rw [mem_ball, dist_comm]; exact hqB
    refine Filter.eventually_of_mem (isOpen_ball.mem_nhds hpq) fun w hw => ?_
    have := hzero' (w - q) (by simpa [dist_eq_norm] using hw)
    simpa using this
  exact fun z hz => (hsub hz).self_of_nhds

end

section

/-! ## Mean value property for the Helmholtz equation -/

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory Set Real Metric Complex Filter Topology

lemma continuous_polar_ball {v : ℂ → ℂ} {R ρ : ℝ} (hv : ContinuousOn v (ball 0 R))
    (hρ : |ρ| < R) : Continuous fun θ : ℝ => v (ρ * cexp (θ * I)) :=
  hv.comp_continuous (by fun_prop) fun θ => polar_mem_ball θ hρ

lemma two_pi_ne_zero_complex : (2 * π : ℂ) ≠ 0 := by
  have := Real.pi_pos; exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)

lemma tendsto_angCoeff_zero {v : ℂ → ℂ} {R : ℝ} (hR : 0 < R) (hv : ContinuousOn v (ball 0 R)) :
    Tendsto (angCoeff v 0) (𝓝[>] 0) (𝓝 (v 0)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hv0 : ContinuousAt v 0 := hv.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hR))
  obtain ⟨η, hη, hηv⟩ := Metric.continuousAt_iff.1 hv0 (ε / 2) (by linarith)
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ∈ Ioo 0 (min η R) := Ioo_mem_nhdsGT (lt_min hη hR)
  filter_upwards [hev] with ρ hρ
  have hρR : |ρ| < R := by rw [abs_of_pos hρ.1]; exact hρ.2.trans_le (min_le_right _ _)
  have hc := continuous_polar_ball hv hρR
  have e : angCoeff v 0 ρ - v 0 =
      (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, (v (ρ * cexp (θ * I)) - v 0) := by
    unfold angCoeff
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp only [Int.cast_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul, sub_zero,
      real_smul]
    rw [mul_sub]
    congr 1
    field_simp [two_pi_ne_zero_complex]
    push_cast; ring
  rw [dist_eq_norm, e]
  refine (norm_inv_two_pi_mul_integral_le fun θ => ?_).trans_lt (by linarith : ε / 2 < ε)
  refine (hηv ?_).le
  rw [dist_zero_right, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hρ.1]
  exact hρ.2.trans_le (min_le_left _ _)

/-- **Mean value property.** The mean of a Helmholtz solution on the circle of radius `ρ` about
the centre is `v(0) J(ρ)`. -/
lemma helmholtz_circle_mean {k : ℝ} (hk : k ≠ 0) {v : ℂ → ℂ} {R : ℝ}
    (hv : IsHelmholtzOn k v (ball 0 R)) {ρ : ℝ} (hρ : ρ ∈ Ioo 0 R) :
    angCoeff v 0 ρ = v 0 * fbWave k 0 ρ := by
  have hR : 0 < R := hρ.1.trans hρ.2
  obtain ⟨c, hc⟩ := angCoeff_eq_smul_fbWave hk hv 0 hR
  have h1 := tendsto_angCoeff_zero hR hv.1.continuousOn
  have h2 : Tendsto (fun ρ : ℝ => c * fbWave k 0 ρ) (𝓝[>] 0) (𝓝 c) := by
    have : Tendsto (fun ρ : ℝ => fbWave k 0 ρ) (𝓝[>] 0) (𝓝 1) := by
      have hc : Continuous fun ρ : ℝ => fbWave k 0 ρ :=
        (continuous_fbWave k 0).comp Complex.continuous_ofReal
      have := hc.tendsto 0
      simp only [Complex.ofReal_zero, fbWave_zero_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    simpa using this.const_mul c
  have hev : angCoeff v 0 =ᶠ[𝓝[>] 0] fun ρ => c * fbWave k 0 ρ := by
    filter_upwards [Ioo_mem_nhdsGT hR] with ρ hρ using hc ρ hρ
  have := tendsto_nhds_unique (h1.congr' hev) h2
  rw [hc ρ hρ, this]

lemma polarCoord_symm_eq (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = (p.1 : ℂ) * cexp (p.2 * I) := by
  rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]

/-- A radial weight integrates to zero against a function whose circle means vanish. -/
lemma integral_radial_eq_zero {χ0 : ℝ → ℝ} (hχ : Continuous χ0) {ρ1 R : ℝ} (hρR : ρ1 < R)
    (hχ0 : ∀ r, ρ1 ≤ r → χ0 r = 0) {g : ℂ → ℂ} (hg : ContinuousOn g (ball 0 R))
    (hmean : ∀ ρ ∈ Ioo 0 R, angCoeff g 0 ρ = 0) :
    ∫ y, (χ0 ‖y‖ : ℂ) * g y = 0 := by
  rw [← Complex.integral_comp_polarCoord_symm]
  set F : ℝ × ℝ → ℂ := fun p => ((p.1 * χ0 p.1 : ℝ) : ℂ) * g (p.1 * cexp (p.2 * I)) with hF
  have hcongr : ∀ p ∈ polarCoord.target,
      p.1 • ((χ0 ‖Complex.polarCoord.symm p‖ : ℂ) * g (Complex.polarCoord.symm p)) = F p := by
    rintro p hp
    rw [polarCoord_target] at hp
    have hp1 : 0 < p.1 := hp.1
    rw [polarCoord_symm_eq, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hp1, hF, real_smul]
    push_cast; ring
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet hcongr, polarCoord_target]
  have hFint : IntegrableOn F (Ioi 0 ×ˢ Ioo (-π) π) := by
    have hcont : ContinuousOn F (Icc 0 ρ1 ×ˢ Icc (-π) π) := by
      refine ContinuousOn.mul (by fun_prop) ?_
      refine hg.comp (by fun_prop) fun p hp => ?_
      have : |p.1| < R := by rw [abs_of_nonneg hp.1.1]; exact hp.1.2.trans_lt hρR
      exact polar_mem_ball p.2 this
    refine (hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).of_forall_diff_eq_zero
      (measurableSet_Ioi.prod measurableSet_Ioo) ?_
    rintro p ⟨⟨hp1, hp2⟩, hpn⟩
    have : ρ1 < p.1 := by
      by_contra h
      exact hpn ⟨⟨le_of_lt hp1, not_lt.1 h⟩, hp2.1.le, hp2.2.le⟩
    simp [hF, hχ0 p.1 this.le]
  have hprod := setIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) F
    (s := Ioi 0) (t := Ioo (-π) π) (by rw [← Measure.volume_eq_prod]; exact hFint)
  rw [← Measure.volume_eq_prod] at hprod
  rw [hprod]
  refine setIntegral_eq_zero_of_forall_eq_zero fun r hr => ?_
  simp only [hF]
  rw [integral_const_mul]
  by_cases hr1 : ρ1 ≤ r
  · simp [hχ0 r hr1]
  have hrR : r ∈ Ioo 0 R := ⟨hr, (not_le.1 hr1).trans hρR⟩
  have hper : Function.Periodic (fun θ : ℝ => g (r * cexp (θ * I))) (2 * π) := fun θ => by
    simp only
    congr 2
    rw [show ((θ + 2 * π : ℝ) : ℂ) * I = θ * I + 2 * π * I by push_cast; ring,
      Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hint : ∫ θ in Ioo (-π) π, g (r * cexp (θ * I)) = 0 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [pi_pos]),
      show ∫ θ in (-π)..π, g (r * cexp (θ * I)) = ∫ θ in (-π)..(-π + 2 * π), g (r * cexp (θ * I))
        by rw [show -π + 2 * π = π by ring], hper.intervalIntegral_add_eq (-π) 0, zero_add]
    have h := hmean r hrR
    unfold angCoeff at h
    simp only [Int.cast_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul] at h
    exact (mul_eq_zero.1 h).resolve_left (inv_ne_zero two_pi_ne_zero_complex)
  rw [hint, mul_zero]

lemma integrable_radial_mul {χ0 : ℝ → ℝ} (hχ : Continuous χ0) {ρ1 : ℝ}
    (hχ0 : ∀ r, ρ1 ≤ r → χ0 r = 0) {g : ℂ → ℂ} (hg : ContinuousOn g (closedBall 0 ρ1)) :
    Integrable fun y : ℂ => (χ0 ‖y‖ : ℂ) * g y := by
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := closedBall 0 ρ1) ?_ ?_
  · exact ContinuousOn.integrableOn_compact (isCompact_closedBall 0 ρ1)
      ((by fun_prop : Continuous fun y : ℂ => (χ0 ‖y‖ : ℂ)).continuousOn.mul hg)
  · intro y hy
    rw [mem_closedBall, dist_zero_right, not_le] at hy
    simp [hχ0 _ hy.le]

lemma angCoeff_sub_smul {f g : ℂ → ℂ} {ρ : ℝ} (hf : Continuous fun θ : ℝ => f (ρ * cexp (θ * I)))
    (hg : Continuous fun θ : ℝ => g (ρ * cexp (θ * I))) (c : ℂ) (n : ℤ) :
    angCoeff (fun z => f z - c * g z) n ρ = angCoeff f n ρ - c * angCoeff g n ρ := by
  unfold angCoeff
  have he : Continuous fun θ : ℝ => cexp (-(n * θ * I)) := by fun_prop
  have h1 : Continuous fun θ : ℝ => cexp (-(n * θ * I)) * f (ρ * cexp (θ * I)) := he.mul hf
  have h2 : Continuous fun θ : ℝ => cexp (-(n * θ * I)) * (c * g (ρ * cexp (θ * I))) :=
    he.mul (continuous_const.mul hg)
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub (h1.intervalIntegrable _ _)]
  · simp_rw [mul_left_comm (cexp _) c]
    rw [intervalIntegral.integral_const_mul]
    ring
  · exact h2.intervalIntegrable _ _

/-- **Mean value property against radial weights.** -/
theorem integral_radial_mul_helmholtz {k : ℝ} (hk : k ≠ 0) {u : ℂ → ℂ} {x : ℂ} {R : ℝ}
    (hu : IsHelmholtzOn k u (ball x R)) {χ0 : ℝ → ℝ} (hχ : Continuous χ0) {ρ1 : ℝ}
    (hρR : ρ1 < R) (hχ0 : ∀ r, ρ1 ≤ r → χ0 r = 0) :
    ∫ y, (χ0 ‖y‖ : ℂ) * u (x + y) = u x * ∫ y, (χ0 ‖y‖ : ℂ) * fbWave k 0 y := by
  have hv : IsHelmholtzOn k (fun y => u (x + y)) (ball 0 R) := by
    rw [← preimage_add_ball_self x]; exact hu.comp_add x
  have hvc : ContinuousOn (fun y => u (x + y)) (ball 0 R) := hv.1.continuousOn
  set g : ℂ → ℂ := fun y => u (x + y) - u x * fbWave k 0 y with hg
  have hgc : ContinuousOn g (ball 0 R) :=
    hvc.sub (continuousOn_const.mul (continuous_fbWave k 0).continuousOn)
  have hmean : ∀ ρ ∈ Ioo 0 R, angCoeff g 0 ρ = 0 := by
    intro ρ hρ
    have hρR' : |ρ| < R := by rw [abs_of_pos hρ.1]; exact hρ.2
    rw [hg, angCoeff_sub_smul (continuous_polar_ball hvc hρR')
      ((continuous_fbWave k 0).comp (by fun_prop)), helmholtz_circle_mean hk hv hρ,
      angCoeff_fbWave, if_pos rfl]
    simp
  have hzero := integral_radial_eq_zero hχ hρR hχ0 hgc hmean
  have hcl : closedBall (0 : ℂ) ρ1 ⊆ ball 0 R := closedBall_subset_ball hρR
  have i1 := integrable_radial_mul hχ hχ0 (hvc.mono hcl)
  have i2 := integrable_radial_mul hχ hχ0 (g := fun y => u x * fbWave k 0 y)
    (continuousOn_const.mul (continuous_fbWave k 0).continuousOn)
  simp only [hg, mul_sub] at hzero
  rw [integral_sub i1 i2, sub_eq_zero] at hzero
  rw [hzero, ← integral_const_mul]
  congr 1; funext y; ring

end

section

/-! ## A Rellich-type lemma for the Helmholtz equation -/

open scoped InnerProductSpace ComplexConjugate ENNReal
open MeasureTheory Set Real Metric Complex Filter Topology

/-! ### The energy argument for Bessel's equation -/

/-- Energy identity for Bessel's equation. -/
lemma bessel_energy_hasDerivAt {k : ℝ} {n : ℤ} {f f' : ℝ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : HasDerivAt f (f' ρ) ρ)
    (hf' : HasDerivAt f' (-(f' ρ) / ρ - ((k : ℂ) ^ 2 - (n : ℂ) ^ 2 / (ρ : ℂ) ^ 2) * f ρ) ρ) :
    HasDerivAt (fun r : ℝ => r * (‖f' r + f r / (2 * r)‖ ^ 2 + k ^ 2 * ‖f r‖ ^ 2))
      (((n : ℝ) ^ 2 - 1 / 4) / ρ *
        (star (f ρ) * (f' ρ + f ρ / (2 * ρ)) + star (f' ρ + f ρ / (2 * ρ)) * f ρ)).re ρ := by
  have hρ0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hr : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 ρ := hasDerivAt_id ρ |>.ofReal_comp
  have hg : HasDerivAt (fun r : ℝ => f' r + f r / (2 * r))
      ((-(f' ρ) / ρ - ((k : ℂ) ^ 2 - (n : ℂ) ^ 2 / (ρ : ℂ) ^ 2) * f ρ) +
        (f' ρ * (2 * ρ) - f ρ * (2 * 1)) / (2 * ρ) ^ 2) ρ :=
    hf'.add (hf.div (hr.const_mul 2) (by simpa using hρ0))
  have hP := hr.mul ((hg.star.mul hg).add ((hf.star.mul hf).const_mul ((k : ℂ) ^ 2)))
  have hE := (Complex.reCLM.hasFDerivAt (x := _)).comp_hasDerivAt ρ hP
  convert hE using 1
  · funext r
    simp only [Function.comp_apply, Pi.mul_apply, Pi.add_apply, Complex.reCLM_apply]
    rw [show star (f' r + f r / (2 * r)) = conj (f' r + f r / (2 * r)) from rfl,
      show star (f r) = conj (f r) from rfl, Complex.conj_mul', Complex.conj_mul']
    norm_cast
  · simp only [Complex.reCLM_apply, Pi.mul_apply, Pi.add_apply]
    congr 1
    simp only [star_add, star_div₀, star_mul', Complex.star_def, Complex.conj_ofReal, map_ofNat, star_neg, star_sub, map_pow, map_intCast, map_one]
    push_cast
    simp only [map_mul, Complex.conj_ofReal, map_ofNat]
    field_simp
    ring

/-- The energy derivative controls the energy. -/
lemma bessel_energy_deriv_ge {k r : ℝ} (hk : 0 < k) (hr : 0 < r) {n : ℤ} (F g : ℂ) :
    -(|(n : ℝ) ^ 2 - 1 / 4| / k / r ^ 2) * (r * (‖g‖ ^ 2 + k ^ 2 * ‖F‖ ^ 2)) ≤
      (((n : ℝ) ^ 2 - 1 / 4) / r * (star F * g + star g * F)).re := by
  set m : ℝ := (n : ℝ) ^ 2 - 1 / 4
  have hcoe : (((n : ℝ) ^ 2 - 1 / 4) / r * (star F * g + star g * F) : ℂ) =
      ((m / r : ℝ) : ℂ) * (star F * g + star g * F) := by simp [m]
  rw [hcoe]
  have hn : ‖((m / r : ℝ) : ℂ) * (star F * g + star g * F)‖ ≤ |m| / r * (2 * ‖F‖ * ‖g‖) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hr]
    gcongr
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    simp only [norm_mul, norm_star]; ring
  have hre := Complex.abs_re_le_norm (((m / r : ℝ) : ℂ) * (star F * g + star g * F))
  have hsq : 0 ≤ |m| / (k * r) * (‖g‖ - k * ‖F‖) ^ 2 := by positivity
  have e : |m| / (k * r) * (‖g‖ - k * ‖F‖) ^ 2 =
      |m| / k / r ^ 2 * (r * (‖g‖ ^ 2 + k ^ 2 * ‖F‖ ^ 2)) - |m| / r * (2 * ‖F‖ * ‖g‖) := by
    field_simp; ring
  linarith [neg_abs_le (((m / r : ℝ) : ℂ) * (star F * g + star g * F)).re]

/-- A solution of Bessel's equation on `(a, ∞)` with `∫ ρ (|f'|² + |f|²) dρ < ∞` vanishes. -/
lemma bessel_eq_zero_of_lintegral {k a : ℝ} (hk : 0 < k) (ha : 0 ≤ a) {n : ℤ} {f f' : ℝ → ℂ}
    (hf : ∀ ρ, a < ρ → HasDerivAt f (f' ρ) ρ)
    (hf' : ∀ ρ, a < ρ →
      HasDerivAt f' (-(f' ρ) / ρ - ((k : ℂ) ^ 2 - (n : ℂ) ^ 2 / (ρ : ℂ) ^ 2) * f ρ) ρ)
    (hfin : ∫⁻ ρ in Ioi a, ENNReal.ofReal (ρ * (‖f' ρ‖ ^ 2 + ‖f ρ‖ ^ 2)) ≠ ∞) :
    ∀ ρ, a < ρ → f ρ = 0 := by
  obtain ⟨E, hE⟩ : ∃ E : ℝ → ℝ,
      E = fun r => r * (‖f' r + f r / (2 * r)‖ ^ 2 + k ^ 2 * ‖f r‖ ^ 2) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ → ℝ, D = fun r => (((n : ℝ) ^ 2 - 1 / 4) / r *
      (star (f r) * (f' r + f r / (2 * r)) + star (f' r + f r / (2 * r)) * f r)).re := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = |(n : ℝ) ^ 2 - 1 / 4| / k := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hE0 : ∀ r, 0 < r → 0 ≤ E r := fun r hr => by rw [hE]; positivity
  have hdE : ∀ r, a < r → HasDerivAt E (D r) r := fun r hr => by
    rw [hE, hD]; exact bessel_energy_hasDerivAt (ha.trans_lt hr) (hf r hr) (hf' r hr)
  have hDge : ∀ r, a < r → -(c / r ^ 2) * E r ≤ D r := fun r hr => by
    rw [hE, hD, hc]; exact bessel_energy_deriv_ge hk (ha.trans_lt hr) _ _
  -- Grönwall
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ → ℝ, Q = fun r => E r * Real.exp (-c * r⁻¹) := ⟨_, rfl⟩
  have hdQ : ∀ r, a < r → HasDerivAt Q
      (D r * Real.exp (-c * r⁻¹) + E r * (Real.exp (-c * r⁻¹) * (-c * -(r ^ 2)⁻¹))) r := by
    intro r hr
    rw [hQ]
    exact (hdE r hr).mul (((hasDerivAt_inv (ha.trans_lt hr).ne').const_mul (-c)).exp)
  have hQmono : MonotoneOn Q (Ioi a) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi a) (f' := fun r =>
      D r * Real.exp (-c * r⁻¹) + E r * (Real.exp (-c * r⁻¹) * (-c * -(r ^ 2)⁻¹)))
      (fun r hr => (hdQ r hr).continuousAt.continuousWithinAt) (fun r hr => ?_) (fun r hr => ?_)
    · rw [interior_Ioi] at hr ⊢; exact (hdQ r hr).hasDerivWithinAt
    · rw [interior_Ioi] at hr
      have := hDge r hr
      have he := Real.exp_pos (-c * r⁻¹)
      have : 0 ≤ D r + E r * (c / r ^ 2) := by linarith
      calc (0 : ℝ) ≤ Real.exp (-c * r⁻¹) * (D r + E r * (c / r ^ 2)) := by positivity
        _ = _ := by field_simp
  -- contradiction
  intro ρ0 hρ0
  by_contra hne
  have hρ0p : 0 < ρ0 := ha.trans_lt hρ0
  have hEρ0 : 0 < E ρ0 := by
    rw [hE]
    have : 0 < ‖f ρ0‖ := norm_pos_iff.2 hne
    positivity
  set δ := Q ρ0 with hδ
  have hδ0 : 0 < δ := by rw [hδ, hQ]; positivity
  set C : ℝ := 2 + 1 / (2 * ρ0 ^ 2) + k ^ 2 with hC
  have hC0 : 0 < C := by positivity
  have hlow : ∀ r, ρ0 < r → δ / C ≤ r * (‖f' r‖ ^ 2 + ‖f r‖ ^ 2) := by
    intro r hr
    have hr0 : 0 < r := hρ0p.trans hr
    have h1 : δ ≤ Q r := hQmono hρ0 (hρ0.trans hr) hr.le
    have h2 : Q r ≤ E r := by
      rw [hQ]
      exact mul_le_of_le_one_right (hE0 r hr0)
        (Real.exp_le_one_iff.2 (by have := inv_pos.2 hr0; nlinarith))
    have h3 : E r ≤ C * (r * (‖f' r‖ ^ 2 + ‖f r‖ ^ 2)) := by
      rw [hE]
      have hn : ‖f' r + f r / (2 * r)‖ ≤ ‖f' r‖ + ‖f r‖ / (2 * r) := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
        norm_num
      have hsq : ‖f' r + f r / (2 * r)‖ ^ 2 ≤ 2 * ‖f' r‖ ^ 2 + ‖f r‖ ^ 2 / (2 * ρ0 ^ 2) := by
        have h4 : (‖f' r‖ + ‖f r‖ / (2 * r)) ^ 2 ≤ 2 * ‖f' r‖ ^ 2 + 2 * (‖f r‖ / (2 * r)) ^ 2 := by
          nlinarith [sq_nonneg (‖f' r‖ - ‖f r‖ / (2 * r))]
        have h5 : 2 * (‖f r‖ / (2 * r)) ^ 2 ≤ ‖f r‖ ^ 2 / (2 * ρ0 ^ 2) := by
          rw [div_pow, mul_pow]
          have : ρ0 ^ 2 ≤ r ^ 2 := by nlinarith
          calc 2 * (‖f r‖ ^ 2 / (2 ^ 2 * r ^ 2)) = ‖f r‖ ^ 2 / (2 * r ^ 2) := by ring
            _ ≤ ‖f r‖ ^ 2 / (2 * ρ0 ^ 2) := by gcongr
        nlinarith [pow_le_pow_left₀ (norm_nonneg _) hn 2]
      have : 0 ≤ ‖f' r‖ ^ 2 := by positivity
      have : 0 ≤ ‖f r‖ ^ 2 := by positivity
      have : 0 ≤ ‖f r‖ ^ 2 / (2 * ρ0 ^ 2) := by positivity
      calc r * (‖f' r + f r / (2 * r)‖ ^ 2 + k ^ 2 * ‖f r‖ ^ 2)
          ≤ r * (2 * ‖f' r‖ ^ 2 + ‖f r‖ ^ 2 / (2 * ρ0 ^ 2) + k ^ 2 * ‖f r‖ ^ 2) := by gcongr
        _ ≤ C * (r * (‖f' r‖ ^ 2 + ‖f r‖ ^ 2)) := by
          rw [hC]
          have : 0 ≤ 1 / (2 * ρ0 ^ 2) * ‖f' r‖ ^ 2 + k ^ 2 * ‖f' r‖ ^ 2 + 2 * ‖f r‖ ^ 2 := by
            positivity
          have e : ‖f r‖ ^ 2 / (2 * ρ0 ^ 2) = 1 / (2 * ρ0 ^ 2) * ‖f r‖ ^ 2 := by ring
          rw [e]; nlinarith
    rw [div_le_iff₀ hC0]; nlinarith
  apply hfin
  refine eq_top_iff.2 ?_
  calc (∞ : ℝ≥0∞) = ∫⁻ _ in Ioi ρ0, ENNReal.ofReal (δ / C) := by
        rw [setLIntegral_const, Real.volume_Ioi, ENNReal.mul_top]
        exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
    _ ≤ ∫⁻ r in Ioi ρ0, ENNReal.ofReal (r * (‖f' r‖ ^ 2 + ‖f r‖ ^ 2)) := by
        refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall
          fun r hr => ENNReal.ofReal_le_ofReal (hlow r hr)))
    _ ≤ _ := lintegral_mono_set (Ioi_subset_Ioi hρ0.le)

/-! ### Square-integrability of the angular coefficients -/

/-- A Fourier coefficient is bounded by the `L²` norm on a period. -/
lemma cf_sq_le_lintegral {h : ℝ → ℂ} (hc : Continuous h) (hp : Function.Periodic h (2 * π))
    (n : ℤ) :
    ENNReal.ofReal (‖cf h n‖ ^ 2) ≤
      ENNReal.ofReal (2 * π)⁻¹ * ∫⁻ θ in Ioo (-π) π, ‖h θ‖ₑ ^ 2 := by
  have h1 : ‖cf h n‖ ^ 2 ≤ (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ‖h θ‖ ^ 2 :=
    le_hasSum (hasSum_sq_cf hc) n (fun _ _ => sq_nonneg _)
  have hp2 : Function.Periodic (fun θ => ‖h θ‖ ^ 2) (2 * π) := fun θ => by simp only [hp θ]
  have h2 : ∫ θ in (0 : ℝ)..2 * π, ‖h θ‖ ^ 2 = ∫ θ in Ioo (-π) π, ‖h θ‖ ^ 2 := by
    have := hp2.intervalIntegral_add_eq 0 (-π)
    rw [zero_add, show -π + 2 * π = π by ring] at this
    rw [this, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      integral_Ioc_eq_integral_Ioo]
  have h3 : ENNReal.ofReal (∫ θ in Ioo (-π) π, ‖h θ‖ ^ 2) = ∫⁻ θ in Ioo (-π) π, ‖h θ‖ₑ ^ 2 := by
    rw [ofReal_integral_eq_lintegral_ofReal]
    · refine lintegral_congr fun θ => ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    · exact ((hc.norm.pow 2).integrableOn_Icc (a := -π) (b := π)).mono_set Ioo_subset_Icc_self
    · exact Filter.Eventually.of_forall fun θ => sq_nonneg _
  rw [← h3, ← ENNReal.ofReal_mul (by positivity), ← h2]
  exact ENNReal.ofReal_le_ofReal h1

/-- Polar coordinates for nonnegative measurable functions. -/
lemma lintegral_polar_eq {F : ℂ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ρ in Ioi 0, ENNReal.ofReal ρ * ∫⁻ θ in Ioo (-π) π, F (ρ * cexp (θ * I)) =
      ∫⁻ z, F z := by
  rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target, Measure.volume_eq_prod]
  simp_rw [polarCoord_symm_eq]
  rw [setLIntegral_prod]
  · refine lintegral_congr fun ρ => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rfl
  · exact (measurable_fst.ennreal_ofReal.smul (hF.comp (by fun_prop))).aemeasurable

/-! ### The Rellich lemma -/

lemma lintegral_enorm_sq_lt_top {E : Type*} [NormedAddCommGroup E] {f : ℂ → E}
    (hf : MemLp f 2) : ∫⁻ z, ‖f z‖ₑ ^ 2 < ∞ := by
  have := ((memLp_two_iff_integrable_sq_norm hf.1).1 hf).hasFiniteIntegral
  unfold HasFiniteIntegral at this
  convert this using 3 with z
  rw [enorm_pow, enorm_norm]

lemma cexp_periodic_real (θ : ℝ) : cexp (((θ + 2 * π : ℝ) : ℂ) * I) = cexp (θ * I) := by
  have := Complex.exp_mul_I_periodic (θ : ℂ)
  push_cast
  exact this

lemma periodic_polar_comp {E : Type*} (g : ℂ → E) (ρ : ℝ) :
    Function.Periodic (fun θ : ℝ => g (ρ * cexp (θ * I))) (2 * π) := fun θ => by
  simp only
  congr 2
  have := Complex.exp_mul_I_periodic (θ : ℂ)
  push_cast
  exact this

/-- Rellich-type lemma: an exterior Helmholtz solution with square-integrable value and gradient
vanishes. -/
theorem helmholtz_exterior_eq_zero {k : ℝ} (hk : 0 < k) {R0 : ℝ} {w : ℂ → ℂ}
    (hw : IsHelmholtzOn k w {z | R0 < ‖z‖}) (hw2 : MemLp w 2) (hdw2 : MemLp (fderiv ℝ w) 2) :
    ∀ z : ℂ, R0 < ‖z‖ → w z = 0 := by
  classical
  obtain ⟨a, ha_def⟩ : ∃ a, a = max R0 0 := ⟨_, rfl⟩
  have ha : 0 ≤ a := ha_def ▸ le_max_right _ _
  have hRa : R0 ≤ a := ha_def ▸ le_max_left _ _
  set U : Set ℂ := {z | a < ‖z‖} with hU_def
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hUsub : U ⊆ {z | R0 < ‖z‖} := fun z hz => hRa.trans_lt hz
  have hwU : IsHelmholtzOn k w U := hw.mono hUsub
  have hcw : ContinuousOn w U := hwU.1.continuousOn
  have hcdw : ContinuousOn (fderiv ℝ w) U := hwU.1.continuousOn_fderiv_of_isOpen hUo (by norm_num)
  have hann : ∀ ρ, a < ρ → IsHelmholtzOn k w (annulus a (ρ + 1)) := fun ρ _ =>
    hwU.mono fun z hz => hz.1
  have hpol : ∀ ρ θ : ℝ, a < ρ → (ρ : ℂ) * cexp (θ * I) ∈ U := fun ρ θ hρ => by
    show a < ‖(ρ : ℂ) * cexp (θ * I)‖
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (ha.trans_lt hρ)]
    exact hρ
  -- the majorant
  set G : ℂ → ℝ≥0∞ := fun z => ‖w z‖ₑ ^ 2 + ‖fderiv ℝ w z‖ₑ ^ 2 with hG
  set F : ℂ → ℝ≥0∞ := U.piecewise G 0 with hF
  have hFm : Measurable F :=
    ContinuousOn.measurable_piecewise
      (((ENNReal.continuous_pow 2).comp_continuousOn hcw.enorm).add
        ((ENNReal.continuous_pow 2).comp_continuousOn hcdw.enorm))
      continuousOn_const hUo.measurableSet
  have hFfin : ∫⁻ z, F z < ∞ := by
    have h1 : ∫⁻ z, F z ≤ ∫⁻ z, G z := lintegral_mono fun z => by
      by_cases hz : z ∈ U
      · simp [hF, hz]
      · simp [hF, hz]
    refine h1.trans_lt ?_
    rw [hG, lintegral_add_left' ((hw2.1.enorm.pow_const 2))]
    exact ENNReal.add_lt_top.2 ⟨lintegral_enorm_sq_lt_top hw2, lintegral_enorm_sq_lt_top hdw2⟩
  have hFU : ∀ ρ θ : ℝ, a < ρ → F ((ρ : ℂ) * cexp (θ * I)) = G ((ρ : ℂ) * cexp (θ * I)) :=
    fun ρ θ hρ => by simp [hF, hpol ρ θ hρ]
  -- all angular coefficients vanish
  have hcoef : ∀ (n : ℤ) ρ, a < ρ → angCoeff w n ρ = 0 := by
    intro n
    refine bessel_eq_zero_of_lintegral hk ha (f' := angCoeffD w n)
      (fun ρ hρ => (angCoeff_bessel_ann (hann ρ hρ) n ha ⟨hρ, by linarith⟩).1)
      (fun ρ hρ => (angCoeff_bessel_ann (hann ρ hρ) n ha ⟨hρ, by linarith⟩).2) ?_
    refine ne_top_of_le_ne_top (b := 2 * ENNReal.ofReal (2 * π)⁻¹ * ∫⁻ z, F z)
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) hFfin.ne) ?_
    rw [← lintegral_polar_eq hFm, ← lintegral_const_mul' _ _
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)]
    refine le_trans ?_ (lintegral_mono_set (Ioi_subset_Ioi ha))
    refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall fun ρ hρ => ?_))
    have hρ : a < ρ := hρ
    have habs : |ρ| ∈ Ioo a (ρ + 1) := by
      rw [abs_of_pos (ha.trans_lt hρ)]; exact ⟨hρ, by linarith⟩
    set X := ∫⁻ θ in Ioo (-π) π, F (ρ * cexp (θ * I))
    set C := ENNReal.ofReal (2 * π)⁻¹
    have hbw : ENNReal.ofReal (‖angCoeff w n ρ‖ ^ 2) ≤ C * X := by
      rw [angCoeff_eq_cf]
      refine (cf_sq_le_lintegral (continuous_polar_comp_ann (hann ρ hρ) habs)
        (periodic_polar_comp w ρ) n).trans ?_
      refine mul_le_mul_right (lintegral_mono fun θ => ?_) _
      rw [hFU ρ θ hρ, hG]
      exact le_self_add
    have hbd : ENNReal.ofReal (‖angCoeffD w n ρ‖ ^ 2) ≤ C * X := by
      have hper : Function.Periodic
          (fun θ : ℝ => fderiv ℝ w (ρ * cexp (θ * I)) (cexp (θ * I))) (2 * π) := fun θ => by
        simp only [cexp_periodic_real]
      refine (cf_sq_le_lintegral ((continuous_fderiv_polar_comp_ann (hann ρ hρ) habs).clm_apply
        (by fun_prop)) hper n).trans ?_
      refine mul_le_mul_right (lintegral_mono fun θ => ?_) _
      rw [hFU ρ θ hρ, hG]
      refine le_trans ?_ le_add_self
      gcongr
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
      refine ENNReal.ofReal_le_ofReal ?_
      have := (fderiv ℝ w (ρ * cexp (θ * I))).le_opNorm (cexp (θ * I))
      rwa [Complex.norm_exp_ofReal_mul_I, mul_one] at this
    rw [ENNReal.ofReal_mul (ha.trans_lt hρ).le, ENNReal.ofReal_add (by positivity) (by positivity)]
    calc ENNReal.ofReal ρ * (ENNReal.ofReal (‖angCoeffD w n ρ‖ ^ 2) +
          ENNReal.ofReal (‖angCoeff w n ρ‖ ^ 2))
        ≤ ENNReal.ofReal ρ * (C * X + C * X) := by gcongr
      _ = 2 * C * (ENNReal.ofReal ρ * X) := by ring
  -- conclusion
  have hmain : ∀ z : ℂ, a < ‖z‖ → w z = 0 := by
    intro z hz
    set ρ := ‖z‖ with hρdef
    set Φ : ℂ → ℂ := fun v => w (ρ * v)
    have hΦ : ContinuousOn Φ (sphere 0 1) := by
      refine hcw.comp (continuousOn_const.mul continuousOn_id) fun v hv => ?_
      simp only [mem_sphere_iff_norm, sub_zero] at hv
      show a < ‖(ρ : ℂ) * v‖
      rw [norm_mul, hv, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (ha.trans_lt hz)]
      exact hz
    have hcf : ∀ m : ℤ, cf (fun θ : ℝ => Φ (cexp (θ * I))) m =
        if 0 < m.natAbs then (0 : ℤ → ℂ) m else 0 := by
      intro m
      rw [← angCoeff_eq_cf, hcoef m ρ hz]
      simp
    have hle := norm_le_tsum_of_cf hΦ (N := 0) (b := 0) (by simp) hcf (arg z)
    simp only [Pi.zero_apply, norm_zero, ite_self, tsum_zero, norm_le_zero_iff] at hle
    have : (ρ : ℂ) * cexp (arg z * I) = z := by
      rw [hρdef]; exact Complex.norm_mul_exp_arg_mul_I z
    simpa [Φ, this] using hle
  intro z hz
  by_cases hza : a < ‖z‖
  · exact hmain z hza
  -- the only remaining case is `z = 0` with `R0 < 0`
  have hz0 : z = 0 := by
    have : ‖z‖ ≤ 0 := by
      rcases le_total R0 0 with h | h
      · rw [ha_def, max_eq_right h] at hza; linarith
      · rw [ha_def, max_eq_left h] at hza; linarith
    exact norm_le_zero_iff.1 this
  subst hz0
  have h0a : a = 0 := by
    rw [ha_def]; exact max_eq_right (by simpa using hz.le)
  have hcont : ContinuousAt w 0 :=
    hw.1.continuousOn.continuousAt ((isOpen_lt continuous_const continuous_norm).mem_nhds hz)
  by_contra hne
  have hev : ∀ᶠ x in 𝓝[≠] (0 : ℂ), w x ≠ 0 :=
    (hcont.eventually_ne hne).filter_mono nhdsWithin_le_nhds
  obtain ⟨x, hx1, hx2⟩ := (hev.and self_mem_nhdsWithin).exists
  exact hx1 (hmain x (by rw [h0a]; exact norm_pos_iff.2 hx2))

end

section

/-! ## Green's identity for compactly supported functions -/

open scoped InnerProductSpace ComplexConjugate Manifold ContDiff
open MeasureTheory Set Real Metric Complex Filter Topology

/-- The Laplacian on `ℂ` as a sum of second directional derivatives. -/
lemma laplacian_eq_fderiv_fderiv (f : ℂ → ℂ) (x : ℂ) :
    Laplacian.laplacian f x = fderiv ℝ (fderiv ℝ f) x 1 1 + fderiv ℝ (fderiv ℝ f) x I I := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

lemma fderiv_fderiv_apply_eq {f : ℂ → ℂ} (hf : ContDiff ℝ 2 f) (x v : ℂ) :
    fderiv ℝ (fderiv ℝ f) x v v = fderiv ℝ (fun y => fderiv ℝ f y v) x v := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  rw [fderiv_clm_apply (hd x) (differentiableAt_const v)]
  simp

lemma hasCompactSupport_clm_apply {L : ℂ → ℂ →L[ℝ] ℂ} (h : HasCompactSupport L) (v : ℂ) :
    HasCompactSupport fun x => L x v :=
  h.comp_left (g := fun T : ℂ →L[ℝ] ℂ => T v) (by simp)

lemma hasCompactSupport_clm_apply₂ {L : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℂ} (h : HasCompactSupport L)
    (v w : ℂ) : HasCompactSupport fun x => L x v w :=
  h.comp_left (g := fun T : ℂ →L[ℝ] ℂ →L[ℝ] ℂ => T v w) (by simp)

lemma continuous_fderiv_fderiv_of_contDiff {f : ℂ → ℂ} (hf : ContDiff ℝ 2 f) :
    Continuous (fderiv ℝ (fderiv ℝ f)) :=
  (hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)

/-- Integration by parts twice in the direction `v`. -/
lemma integral_fderiv_fderiv_mul {w ψ : ℂ → ℂ} (hw : ContDiff ℝ 2 w) (hψ : ContDiff ℝ 2 ψ)
    (hwc : HasCompactSupport w) (v : ℂ) :
    ∫ x, fderiv ℝ (fderiv ℝ w) x v v * ψ x = ∫ x, w x * fderiv ℝ (fderiv ℝ ψ) x v v := by
  set g : ℂ → ℂ := fun y => fderiv ℝ w y v
  set h : ℂ → ℂ := fun y => fderiv ℝ ψ y v
  have hw1 : ContDiff ℝ 1 (fderiv ℝ w) := hw.fderiv_right (m := 1) (by norm_num)
  have hψ1 : ContDiff ℝ 1 (fderiv ℝ ψ) := hψ.fderiv_right (m := 1) (by norm_num)
  have hg : ContDiff ℝ 1 g := hw1.clm_apply contDiff_const
  have hh : ContDiff ℝ 1 h := hψ1.clm_apply contDiff_const
  have hgc : HasCompactSupport g := hasCompactSupport_clm_apply (hwc.fderiv (𝕜 := ℝ)) v
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hhd : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hwd : Differentiable ℝ w := hw.differentiable (by norm_num)
  have hdg : Continuous fun x => fderiv ℝ g x v :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdh : Continuous fun x => fderiv ℝ h x v :=
    (hh.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hgcont : Continuous g := hg.continuous
  have hhcont : Continuous h := hh.continuous
  have hdgc : HasCompactSupport fun x => fderiv ℝ g x v :=
    hasCompactSupport_clm_apply (hgc.fderiv (𝕜 := ℝ)) v
  -- first integration by parts: `∫ ψ ∂g = -∫ ∂ψ g`
  have e1 : ∫ x, ψ x * fderiv ℝ g x v = -∫ x, fderiv ℝ ψ x v * g x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      ((hhcont.mul hgcont).integrable_of_hasCompactSupport hgc.mul_left)
      ((hψ.continuous.mul hdg).integrable_of_hasCompactSupport hdgc.mul_left)
      ((hψ.continuous.mul hgcont).integrable_of_hasCompactSupport hgc.mul_left) hψd hgd
  -- second integration by parts: `∫ w ∂h = -∫ ∂w h`
  have e2 : ∫ x, w x * fderiv ℝ h x v = -∫ x, fderiv ℝ w x v * h x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      ((hgcont.mul hhcont).integrable_of_hasCompactSupport hgc.mul_right)
      ((hw.continuous.mul hdh).integrable_of_hasCompactSupport hwc.mul_right)
      ((hw.continuous.mul hhcont).integrable_of_hasCompactSupport hwc.mul_right) hwd hhd
  have l1 : ∀ x, fderiv ℝ (fderiv ℝ w) x v v * ψ x = ψ x * fderiv ℝ g x v := fun x => by
    rw [fderiv_fderiv_apply_eq hw, mul_comm]
  have l2 : ∀ x, w x * fderiv ℝ (fderiv ℝ ψ) x v v = w x * fderiv ℝ h x v := fun x => by
    rw [fderiv_fderiv_apply_eq hψ]
  simp_rw [l1, l2, e1, e2]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [g, h]; ring

/-- `∫ Δw ψ = ∫ w Δψ` for `C²` functions, `w` compactly supported. -/
lemma integral_laplacian_mul {w ψ : ℂ → ℂ} (hw : ContDiff ℝ 2 w) (hψ : ContDiff ℝ 2 ψ)
    (hwc : HasCompactSupport w) :
    ∫ x, Laplacian.laplacian w x * ψ x = ∫ x, w x * Laplacian.laplacian ψ x := by
  have hc2 : ∀ {f : ℂ → ℂ}, ContDiff ℝ 2 f → ∀ v : ℂ,
      Continuous fun x => fderiv ℝ (fderiv ℝ f) x v v := fun hf v =>
    ((continuous_fderiv_fderiv_of_contDiff hf).clm_apply continuous_const).clm_apply
      continuous_const
  have hcs : ∀ v : ℂ, HasCompactSupport fun x => fderiv ℝ (fderiv ℝ w) x v v := fun v =>
    hasCompactSupport_clm_apply₂ ((hwc.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)) v v
  simp_rw [laplacian_eq_fderiv_fderiv, add_mul, mul_add]
  rw [integral_add, integral_add, integral_fderiv_fderiv_mul hw hψ hwc 1,
    integral_fderiv_fderiv_mul hw hψ hwc I]
  · exact (hw.continuous.mul (hc2 hψ 1)).integrable_of_hasCompactSupport hwc.mul_right
  · exact (hw.continuous.mul (hc2 hψ I)).integrable_of_hasCompactSupport hwc.mul_right
  · exact ((hc2 hw 1).mul hψ.continuous).integrable_of_hasCompactSupport (hcs 1).mul_right
  · exact ((hc2 hw I).mul hψ.continuous).integrable_of_hasCompactSupport (hcs I).mul_right

/-- **Green's identity against a compactly supported function.** -/
theorem integral_helmholtz_green {k : ℝ} {Ω A : Set ℂ} (hΩ : IsOpen Ω) (hA : IsCompact A)
    (hAΩ : A ⊆ Ω) {w : ℂ → ℂ} (hw : ContDiff ℝ 2 w) (hwA : ∀ z ∉ A, w z = 0) {φ : ℂ → ℂ}
    (hφ : IsHelmholtzOn k φ Ω) :
    ∫ z, (Laplacian.laplacian w z + (k : ℂ) ^ 2 * w z) * φ z = 0 := by
  -- a cutoff equal to `1` near `A`, supported in `Ω`
  obtain ⟨δ, hδ, hδΩ⟩ := hA.exists_cthickening_subset_open hΩ hAΩ
  have hAint : A ⊆ interior (cthickening δ A) :=
    (self_subset_thickening hδ A).trans
      (interior_maximal (thickening_subset_cthickening δ A) isOpen_thickening)
  obtain ⟨f, hf1, hf0, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, ℂ)
    (n := 2) hA.isClosed hAint
  have hfc : ContDiff ℝ 2 (f : ℂ → ℝ) := f.contMDiff.contDiff
  set ψ : ℂ → ℂ := fun x => (f x : ℂ) * φ x with hψdef
  have hcl : IsClosed (cthickening δ A) := isClosed_cthickening
  have hψ : ContDiff ℝ 2 ψ := by
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x ∈ Ω
    · exact (ofRealCLM.contDiff.comp hfc).contDiffAt.mul
        (hφ.1.contDiffAt (hΩ.mem_nhds hx))
    · have hxA : x ∉ cthickening δ A := fun h => hx (hδΩ h)
      refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [hcl.isOpen_compl.mem_nhds hxA] with y hy
      simp [ψ, hf0 y hy]
  have hψA : ∀ x ∈ A, ψ =ᶠ[𝓝 x] φ := fun x hx => by
    filter_upwards [hf1.filter_mono (nhds_le_nhdsSet hx)] with y hy
    simp [ψ, hy]
  have hwc : HasCompactSupport w := HasCompactSupport.intro hA hwA
  have hwz : ∀ x ∉ A, Laplacian.laplacian w x = 0 := fun x hx => by
    have : w =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      filter_upwards [hA.isClosed.isOpen_compl.mem_nhds hx] with y hy using hwA y hy
    rw [(InnerProductSpace.laplacian_congr_nhds this).eq_of_nhds]
    simp [laplacian_eq_fderiv_fderiv]
  -- replace `φ` by `ψ`
  have step1 : ∫ z, (Laplacian.laplacian w z + (k : ℂ) ^ 2 * w z) * φ z =
      ∫ z, (Laplacian.laplacian w z + (k : ℂ) ^ 2 * w z) * ψ z := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ A
    · simp only [(hψA x hx).eq_of_nhds]
    · simp [hwz x hx, hwA x hx]
  have hΔw : Continuous (Laplacian.laplacian w) := by
    have : Laplacian.laplacian w = fun x =>
        fderiv ℝ (fderiv ℝ w) x 1 1 + fderiv ℝ (fderiv ℝ w) x I I := by
      funext x; exact laplacian_eq_fderiv_fderiv w x
    rw [this]
    have hc := continuous_fderiv_fderiv_of_contDiff hw
    exact ((hc.clm_apply continuous_const).clm_apply continuous_const).add
      ((hc.clm_apply continuous_const).clm_apply continuous_const)
  have hΔwc : HasCompactSupport (Laplacian.laplacian w) :=
    HasCompactSupport.intro hA hwz
  have step2 : ∫ z, (Laplacian.laplacian w z + (k : ℂ) ^ 2 * w z) * ψ z =
      ∫ z, w z * (Laplacian.laplacian ψ z + (k : ℂ) ^ 2 * ψ z) := by
    simp_rw [add_mul, mul_add]
    rw [integral_add, integral_add, integral_laplacian_mul hw hψ hwc]
    · congr 1
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      ring
    · have hΔψ : Continuous (Laplacian.laplacian ψ) := by
        have : Laplacian.laplacian ψ = fun x =>
            fderiv ℝ (fderiv ℝ ψ) x 1 1 + fderiv ℝ (fderiv ℝ ψ) x I I := by
          funext x; exact laplacian_eq_fderiv_fderiv ψ x
        rw [this]
        have hc := continuous_fderiv_fderiv_of_contDiff hψ
        exact ((hc.clm_apply continuous_const).clm_apply continuous_const).add
          ((hc.clm_apply continuous_const).clm_apply continuous_const)
      exact (hw.continuous.mul hΔψ).integrable_of_hasCompactSupport hwc.mul_right
    · exact (hw.continuous.mul (continuous_const.mul hψ.continuous)).integrable_of_hasCompactSupport
        hwc.mul_right
    · exact (hΔw.mul hψ.continuous).integrable_of_hasCompactSupport hΔwc.mul_right
    · exact ((continuous_const.mul hw.continuous).mul hψ.continuous).integrable_of_hasCompactSupport
        (hwc.mul_left.mul_right)
  rw [step1, step2]
  have : ∀ z, w z * (Laplacian.laplacian ψ z + (k : ℂ) ^ 2 * ψ z) = 0 := fun z => by
    by_cases hz : z ∈ A
    · rw [(InnerProductSpace.laplacian_congr_nhds (hψA z hz)).eq_of_nhds, (hψA z hz).eq_of_nhds, hφ.2 z (hAΩ hz),
        mul_zero]
    · rw [hwA z hz, zero_mul]
  simp [this]

end

section

/-! ## Fourier construction of a potential -/

open scoped InnerProductSpace ComplexConjugate FourierTransform ContDiff ENNReal SchwartzMap
open MeasureTheory Set Real Metric Complex Filter Topology

/-! ### Auxiliary facts -/

lemma fourier_lincomb {f g : ℂ → ℂ} (hf : Integrable f) (hg : Integrable g) (a b z : ℂ) :
    𝓕 (fun ξ => a * f ξ + b * g ξ) z = a * 𝓕 f z + b * 𝓕 g z := by
  have h1 := (Real.fourierIntegral_convergent_iff (μ := volume) z).2 (hf.const_mul a)
  have h2 := (Real.fourierIntegral_convergent_iff (μ := volume) z).2 (hg.const_mul b)
  rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq, ← integral_const_mul,
    ← integral_const_mul, ← integral_add]
  · congr 1; funext v; simp only [Circle.smul_def, smul_eq_mul]; ring
  · refine h1.congr (Eventually.of_forall fun v => ?_)
    simp only [Circle.smul_def, smul_eq_mul]; ring
  · refine h2.congr (Eventually.of_forall fun v => ?_)
    simp only [Circle.smul_def, smul_eq_mul]; ring

lemma norm_clm_le_one_I (T : ℂ →L[ℝ] ℂ) : ‖T‖ ≤ ‖T 1‖ + ‖T I‖ := by
  refine T.opNorm_le_bound (by positivity) fun v => ?_
  have hv : v = v.re • (1 : ℂ) + v.im • I := by
    simp
  rw [hv, map_add, map_smul, map_smul]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 := Complex.abs_re_le_norm v
  have h2 := Complex.abs_im_le_norm v
  have : ‖v.re • (1 : ℂ) + v.im • I‖ = ‖v‖ := by rw [← hv]
  rw [this]
  nlinarith [norm_nonneg (T 1), norm_nonneg (T I)]

/-- Functions dominated by `(1 + |ξ|)⁻³` are integrable and square integrable. -/
lemma integrable_memLp_of_le {f : ℂ → ℂ} (hf : AEStronglyMeasurable f) {D : ℝ}
    (hD : ∀ ξ, ‖f ξ‖ ≤ D * (1 + ‖ξ‖) ^ (-3 : ℝ)) : Integrable f ∧ MemLp f 2 := by
  have hint : Integrable (fun ξ : ℂ => (1 + ‖ξ‖) ^ (-3 : ℝ)) :=
    integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
  have hint6 : Integrable (fun ξ : ℂ => (1 + ‖ξ‖) ^ (-6 : ℝ)) :=
    integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
  refine ⟨Integrable.mono' (hint.const_mul D) hf (Eventually.of_forall hD), ?_⟩
  have hm : MemLp (fun ξ : ℂ => D * (1 + ‖ξ‖) ^ (-3 : ℝ)) 2 := by
    refine (memLp_two_iff_integrable_sq_norm (hint.const_mul D).aestronglyMeasurable).2 ?_
    refine (hint6.const_mul (D ^ 2)).congr (Eventually.of_forall fun ξ => ?_)
    have h0 : 0 < 1 + ‖ξ‖ := by positivity
    have e : ((1 + ‖ξ‖) ^ (-3 : ℝ)) ^ (2 : ℕ) = (1 + ‖ξ‖) ^ (-6 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le]; norm_num
    simp only [Real.norm_eq_abs, sq_abs, mul_pow, e]
  refine hm.of_le hf (Eventually.of_forall fun ξ => (hD ξ).trans (le_abs_self _))

/-! ### Plancherel for `L¹ ∩ L²` -/

lemma integral_fourier_mul_schwartz {K : ℂ → ℂ} (hK : Integrable K) (ψ : 𝓢(ℂ, ℂ)) :
    ∫ ξ, 𝓕 K ξ * ψ ξ = ∫ x, K x * 𝓕 (ψ : ℂ → ℂ) x := by
  simpa using VectorFourier.integral_bilin_fourierIntegral_eq_flip (ContinuousLinearMap.mul ℂ ℂ)
    (L := innerₗ ℂ) Real.continuous_fourierChar continuous_inner hK ψ.integrable

/-- For real-valued `ψ`, conjugating the inverse Fourier transform gives the Fourier transform. -/
lemma inner_fourier_aux (f g : Lp ℂ 2 (volume : Measure ℂ)) : ⟪f, 𝓕 g⟫_ℂ = ⟪𝓕⁻ f, g⟫_ℂ := by
  have := Lp.inner_fourier_eq (𝓕⁻ f) g
  rwa [FourierInvPair.fourier_fourierInv_eq] at this

lemma conj_fourierInv_of_real (ψ : ℂ → ℂ) (hψ : ∀ x, conj (ψ x) = ψ x) (x : ℂ) :
    conj (𝓕⁻ ψ x) = 𝓕 ψ x := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_eq, Real.fourier_eq, ← integral_conj]
  congr 1; funext v
  simp only [Circle.smul_def, smul_eq_mul, map_mul, hψ, inner_neg_right, neg_neg]
  congr 1
  rw [Real.fourierChar_apply, Real.fourierChar_apply, ← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal, map_ofNat]
  ring

/-- The Fourier transform of an integrable square-integrable function is square integrable. -/
theorem memLp_two_fourier {K : ℂ → ℂ} (hK : Integrable K) (hK2 : MemLp K 2) :
    MemLp (𝓕 K) 2 := by
  obtain ⟨u, hu⟩ : ∃ u : Lp ℂ 2 (volume : Measure ℂ), u = 𝓕 (hK2.toLp K) := ⟨_, rfl⟩
  have hcont : Continuous (𝓕 K) :=
    VectorFourier.fourierIntegral_continuous (L := innerₗ ℂ) Real.continuous_fourierChar
      continuous_inner hK
  have hae : 𝓕 K =ᵐ[volume] (u : ℂ → ℂ) := by
    refine ae_eq_of_integral_contDiff_smul_eq hcont.locallyIntegrable
      ((Lp.memLp u).locallyIntegrable (by norm_num)) fun g hg hgc => ?_
    have hgc' : HasCompactSupport (fun x => (g x : ℂ)) := hgc.comp_left Complex.ofReal_zero
    have hg' : ContDiff ℝ ∞ (fun x => (g x : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
    obtain ⟨ψ, hψdef⟩ : ∃ ψ : 𝓢(ℂ, ℂ), ψ = hgc'.toSchwartzMap hg' := ⟨_, rfl⟩
    have hψ : ∀ x, ψ x = (g x : ℂ) := fun x => by rw [hψdef]; rfl
    have hψc : ∀ x, conj (ψ x) = ψ x := fun x => by rw [hψ]; exact Complex.conj_ofReal _
    have hL : ∫ x, g x • 𝓕 K x = ∫ x, K x * 𝓕 (ψ : ℂ → ℂ) x := by
      rw [← integral_fourier_mul_schwartz hK ψ]
      congr 1; funext x; rw [hψ, Complex.real_smul, mul_comm]
    have h1 : ∫ x, g x • (u : ℂ → ℂ) x = ⟪ψ.toLp 2, u⟫_ℂ := by
      rw [L2.inner_def]; refine integral_congr_ae ?_
      filter_upwards [ψ.coeFn_toLp 2 volume] with x hx
      rw [hx, hψ, Complex.real_smul]
      simp only [RCLike.inner_apply, Complex.conj_ofReal]
      ring
    have h2 : ⟪ψ.toLp 2, u⟫_ℂ = ⟪(𝓕⁻ ψ).toLp 2, hK2.toLp K⟫_ℂ := by
      rw [hu, inner_fourier_aux, SchwartzMap.toLp_fourierInv_eq]
    have h3 : ⟪(𝓕⁻ ψ).toLp 2, hK2.toLp K⟫_ℂ = ∫ x, conj (𝓕⁻ (ψ : ℂ → ℂ) x) * K x := by
      rw [L2.inner_def]; refine integral_congr_ae ?_
      filter_upwards [(𝓕⁻ ψ).coeFn_toLp 2 volume, hK2.coeFn_toLp] with x hx hx'
      rw [hx, hx', SchwartzMap.fourierInv_coe]
      simp only [RCLike.inner_apply]
      ring
    rw [hL, h1, h2, h3]
    congr 1; funext x
    rw [conj_fourierInv_of_real _ hψc, mul_comm]
  exact (Lp.memLp u).ae_eq hae.symm

/-! ### Derivatives of Fourier transforms -/

lemma fderiv_fourier_apply {H : ℂ → ℂ} (hH : Integrable H)
    (hH1 : Integrable fun ξ => ‖ξ‖ * ‖H ξ‖) (z v : ℂ) :
    fderiv ℝ (𝓕 H) z v = 𝓕 (fun ξ => (-(2 * π * I) * (⟪ξ, v⟫_ℝ : ℂ)) * H ξ) z := by
  rw [Real.fderiv_fourier hH hH1, Real.fourier_continuousLinearMap_apply]
  · refine congrArg (fun f : ℂ → ℂ => 𝓕 f z) (funext fun ξ => ?_)
    simp only [VectorFourier.fourierSMulRight_apply, smul_eq_mul, Complex.real_smul]
    rw [show ((innerSL ℝ) ξ) v = ⟪ξ, v⟫_ℝ from rfl]
    ring
  · refine (hH1.const_mul (2 * π * ‖innerSL ℝ (E := ℂ)‖)).mono'
      (hH.1.fourierSMulRight (L := innerSL ℝ)) (Eventually.of_forall fun ξ => ?_)
    exact (VectorFourier.norm_fourierSMulRight_le _ _ _).trans (le_of_eq (by ring))

lemma laplacian_fourier {H : ℂ → ℂ} (hHm : AEStronglyMeasurable H)
    (hint : ∀ n : ℕ, n ≤ 2 → Integrable fun ξ => ‖ξ‖ ^ n * ‖H ξ‖) (z : ℂ) :
    Laplacian.laplacian (𝓕 H : ℂ → ℂ) z = 𝓕 (fun ξ => ((-(4 * π ^ 2 * ‖ξ‖ ^ 2) : ℝ) : ℂ) * H ξ) z := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only
  rw [Real.iteratedFDeriv_fourier (N := 2) (fun n hn => hint n (by exact_mod_cast hn)) hHm
    (n := 2) (by norm_num)]
  have hI := VectorFourier.integrable_fourierPowSMulRight (innerSL ℝ) (hint 2 le_rfl) hHm
  rw [Real.fourier_continuousMultilinearMap_apply hI, Real.fourier_continuousMultilinearMap_apply hI]
  have e : ∀ m : ℂ, (fun x => VectorFourier.fourierPowSMulRight (innerSL ℝ) H x 2 ![m, m]) =
      fun ξ => ((-(2 * π * I)) ^ 2 * ((⟪ξ, m⟫_ℝ : ℝ) : ℂ) ^ 2) * H ξ := by
    intro m; funext ξ
    rw [VectorFourier.fourierPowSMulRight_apply]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul,
      Complex.real_smul]
    rw [show ((innerSL ℝ) ξ) m = ⟪ξ, m⟫_ℝ from rfl]
    push_cast; ring
  have hm : ∀ m : ℂ, ‖m‖ = 1 →
      Integrable fun ξ => ((-(2 * π * I)) ^ 2 * ((⟪ξ, m⟫_ℝ : ℝ) : ℂ) ^ 2) * H ξ := by
    intro m hm1
    refine ((hint 2 le_rfl).const_mul (4 * π ^ 2)).mono' (by fun_prop)
      (Eventually.of_forall fun ξ => ?_)
    have h2 : |⟪ξ, m⟫_ℝ| ≤ ‖ξ‖ := by
      have := abs_real_inner_le_norm ξ m; rwa [hm1, mul_one] at this
    simp only [norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      mul_one, Complex.norm_ofNat, abs_of_pos Real.pi_pos, sq_abs]
    have : ⟪ξ, m⟫_ℝ ^ 2 ≤ ‖ξ‖ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    calc (2 * π) ^ 2 * ⟪ξ, m⟫_ℝ ^ 2 * ‖H ξ‖ ≤ (2 * π) ^ 2 * ‖ξ‖ ^ 2 * ‖H ξ‖ := by gcongr
      _ = 4 * π ^ 2 * (‖ξ‖ ^ 2 * ‖H ξ‖) := by ring
  rw [e, e]
  have := fourier_lincomb (hm 1 (by simp)) (hm I (by simp)) 1 1 z
  rw [one_mul, one_mul] at this
  rw [← this]
  refine congrArg (fun f : ℂ → ℂ => 𝓕 f z) (funext fun ξ => ?_)
  have h1 : ⟪ξ, (1 : ℂ)⟫_ℝ = ξ.re := by simp [Complex.inner]
  have h2 : ⟪ξ, I⟫_ℝ = ξ.im := by simp [Complex.inner]
  have h3 : ‖ξ‖ ^ 2 = ξ.re ^ 2 + ξ.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  rw [h1, h2, h3]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ### Division by the Helmholtz symbol -/

/-- The Helmholtz symbol `4π²|ξ|² - k²`. -/
def helmSymb (k : ℝ) (ξ : ℂ) : ℝ := 4 * π ^ 2 * ‖ξ‖ ^ 2 - k ^ 2

/-- Division by the Helmholtz symbol (with the convention `x / 0 = 0`). -/
def helmDiv (k : ℝ) (F : ℂ → ℂ) (ξ : ℂ) : ℂ := F ξ / (helmSymb k ξ : ℂ)

lemma helmSymb_mul_helmDiv {k : ℝ} (hk : 0 < k) {F : ℂ → ℂ}
    (hvan : ∀ ξ : ℂ, ‖ξ‖ = k / (2 * π) → F ξ = 0) (ξ : ℂ) :
    (helmSymb k ξ : ℂ) * helmDiv k F ξ = F ξ := by
  unfold helmDiv
  by_cases h : helmSymb k ξ = 0
  · have hξ : ‖ξ‖ = k / (2 * π) := by
      unfold helmSymb at h
      have hp := Real.pi_pos
      have h2 : (2 * π * ‖ξ‖ - k) * (2 * π * ‖ξ‖ + k) = 0 := by linear_combination h
      rcases mul_eq_zero.1 h2 with h3 | h3
      · field_simp; linarith
      · nlinarith [norm_nonneg ξ]
    rw [hvan ξ hξ]; simp
  · rw [mul_div_cancel₀]; exact_mod_cast h

lemma schwartz_lipschitz (F : 𝓢(ℂ, ℂ)) : ∃ L, 0 ≤ L ∧ ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖ := by
  obtain ⟨C, hC0, hC⟩ := F.decay 0 1
  refine ⟨C, hC0.le, fun x y => ?_⟩
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := univ) (f := F)
    (fun z _ => F.differentiableAt) (fun z _ => by
      have := hC z; rwa [pow_zero, one_mul, norm_iteratedFDeriv_one] at this)
    convex_univ (mem_univ y) (mem_univ x)
  exact this

lemma one_add_pow_five_le (t : ℝ) (ht : 0 ≤ t) : (1 + t) ^ 5 ≤ 32 * (1 + t ^ 5) := by
  rcases le_total t 1 with h | h
  · have : (1 + t) ^ 5 ≤ 2 ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
    nlinarith [pow_nonneg ht 5]
  · have : (1 + t) ^ 5 ≤ (2 * t) ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
    nlinarith [pow_nonneg ht 5]

lemma schwartz_decay5 (F : 𝓢(ℂ, ℂ)) : ∃ D, ∀ ξ, ‖F ξ‖ ≤ D * (1 + ‖ξ‖) ^ (-5 : ℝ) := by
  obtain ⟨C0, hC00, hC0⟩ := F.decay 0 0
  obtain ⟨C5, hC50, hC5⟩ := F.decay 5 0
  refine ⟨32 * (C0 + C5), fun ξ => ?_⟩
  have h0 := hC0 ξ
  have h5 := hC5 ξ
  rw [norm_iteratedFDeriv_zero] at h0 h5
  rw [pow_zero, one_mul] at h0
  have hp : 0 < 1 + ‖ξ‖ := by positivity
  have e : (1 + ‖ξ‖) ^ (-5 : ℝ) = ((1 + ‖ξ‖) ^ 5)⁻¹ := by
    rw [Real.rpow_neg hp.le]; norm_cast
  rw [e, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have := one_add_pow_five_le ‖ξ‖ (norm_nonneg _)
  calc ‖F ξ‖ * (1 + ‖ξ‖) ^ 5 ≤ ‖F ξ‖ * (32 * (1 + ‖ξ‖ ^ 5)) := by gcongr
    _ = 32 * (‖F ξ‖ + ‖ξ‖ ^ 5 * ‖F ξ‖) := by ring
    _ ≤ 32 * (C0 + C5) := by gcongr

lemma norm_le_dist_circle {F : ℂ → ℂ} {L r0 : ℝ} (hr0 : 0 < r0)
    (hL : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (hvan : ∀ ξ : ℂ, ‖ξ‖ = r0 → F ξ = 0) (ξ : ℂ) :
    ‖F ξ‖ ≤ L * |‖ξ‖ - r0| := by
  by_cases hξ : ξ = 0
  · subst hξ
    have := hL 0 (r0 : ℂ)
    rw [hvan (r0 : ℂ) (by simp [abs_of_pos hr0]), sub_zero, zero_sub, norm_neg] at this
    simpa [abs_of_pos hr0] using this
  · have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    set η : ℂ := ((r0 / ‖ξ‖ : ℝ) : ℂ) * ξ
    have hη : ‖η‖ = r0 := by
      simp only [η, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hr0,
        abs_norm]
      field_simp
    have := hL ξ η
    rw [hvan η hη, sub_zero] at this
    refine this.trans (le_of_eq ?_)
    congr 1
    have : ξ - η = ((1 - r0 / ‖ξ‖ : ℝ) : ℂ) * ξ := by simp only [η]; push_cast; ring
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, ← abs_norm ξ, ← abs_mul, abs_norm]
    congr 1; field_simp

lemma abs_helmSymb_ge {k : ℝ} (hk : 0 < k) (ξ : ℂ) :
    2 * π * k * |‖ξ‖ - k / (2 * π)| ≤ |helmSymb k ξ| := by
  have hp := Real.pi_pos
  have e : helmSymb k ξ = (2 * π * (‖ξ‖ - k / (2 * π))) * (2 * π * ‖ξ‖ + k) := by
    unfold helmSymb; field_simp; ring
  rw [e, abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π),
    abs_of_pos (by positivity : 0 < 2 * π * ‖ξ‖ + k)]
  have : k ≤ 2 * π * ‖ξ‖ + k := by have := norm_nonneg ξ; nlinarith
  have h0 := abs_nonneg (‖ξ‖ - k / (2 * π))
  have := mul_le_mul_of_nonneg_left this (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * π) h0)
  linarith

lemma helmSymb_ge_far {k : ℝ} (hk : 0 < k) {ξ : ℂ} (h : k / π ≤ ‖ξ‖) :
    3 * π ^ 2 * ‖ξ‖ ^ 2 ≤ helmSymb k ξ := by
  have hp := Real.pi_pos
  have : k ≤ π * ‖ξ‖ := by rwa [div_le_iff₀ hp, mul_comm] at h
  unfold helmSymb
  nlinarith

lemma norm_helmDiv_le {k : ℝ} (hk : 0 < k) (F : 𝓢(ℂ, ℂ))
    (hvan : ∀ ξ : ℂ, ‖ξ‖ = k / (2 * π) → F ξ = 0) :
    ∃ C, ∀ ξ, ‖helmDiv k F ξ‖ ≤ C * (1 + ‖ξ‖) ^ (-5 : ℝ) := by
  obtain ⟨L, hL0, hL⟩ := schwartz_lipschitz F
  obtain ⟨D, hD⟩ := schwartz_decay5 F
  have hp := Real.pi_pos
  have hr0 : 0 < k / (2 * π) := by positivity
  obtain ⟨R, hR⟩ : ∃ R, R = max (k / π) 1 := ⟨_, rfl⟩
  have hR1 : 1 ≤ R := hR ▸ le_max_right _ _
  refine ⟨L / (2 * π * k) * (1 + R) ^ 5 + |D|, fun ξ => ?_⟩
  have hq : 0 < 1 + ‖ξ‖ := by positivity
  have hw : 0 < (1 + ‖ξ‖) ^ (-5 : ℝ) := Real.rpow_pos_of_pos hq _
  have e : (1 + ‖ξ‖) ^ (-5 : ℝ) = ((1 + ‖ξ‖) ^ 5)⁻¹ := by
    rw [Real.rpow_neg hq.le]; norm_cast
  unfold helmDiv
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
  by_cases hP : helmSymb k ξ = 0
  · rw [hP, abs_zero, div_zero]; positivity
  have hPpos : 0 < |helmSymb k ξ| := abs_pos.2 hP
  rcases le_total R ‖ξ‖ with hfar | hnear
  · have h1 : k / π ≤ ‖ξ‖ := (hR ▸ le_max_left _ _ : k / π ≤ R).trans hfar
    have h2 : 1 ≤ ‖ξ‖ := hR1.trans hfar
    have h3 := helmSymb_ge_far hk h1
    have h4 : 1 ≤ |helmSymb k ξ| := by
      have h5 : 1 ≤ ‖ξ‖ ^ 2 := one_le_pow₀ h2
      have h6 : 9 ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
      have : 1 ≤ 3 * π ^ 2 * ‖ξ‖ ^ 2 := by nlinarith
      rw [abs_of_pos (by linarith)]; linarith
    calc ‖F ξ‖ / |helmSymb k ξ| ≤ ‖F ξ‖ := div_le_self (norm_nonneg _) h4
      _ ≤ D * (1 + ‖ξ‖) ^ (-5 : ℝ) := hD ξ
      _ ≤ |D| * (1 + ‖ξ‖) ^ (-5 : ℝ) := by gcongr; exact le_abs_self D
      _ ≤ _ := by gcongr; exact le_add_of_nonneg_left (by positivity)
  · have hd : 0 < |‖ξ‖ - k / (2 * π)| := by
      refine abs_pos.2 fun hc => hP ?_
      have : ‖ξ‖ = k / (2 * π) := by linarith
      unfold helmSymb; rw [this]; field_simp; ring
    have h1 : ‖F ξ‖ / |helmSymb k ξ| ≤ L / (2 * π * k) := by
      rw [div_le_div_iff₀ hPpos (by positivity)]
      have h5 := norm_le_dist_circle hr0 hL hvan ξ
      have h6 := abs_helmSymb_ge hk ξ
      calc ‖F ξ‖ * (2 * π * k) ≤ L * |‖ξ‖ - k / (2 * π)| * (2 * π * k) := by gcongr
        _ = L * (2 * π * k * |‖ξ‖ - k / (2 * π)|) := by ring
        _ ≤ L * |helmSymb k ξ| := by gcongr
    have h2 : 1 ≤ (1 + R) ^ 5 * (1 + ‖ξ‖) ^ (-5 : ℝ) := by
      rw [e, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_left₀ hq.le (by linarith) 5
    calc ‖F ξ‖ / |helmSymb k ξ| ≤ L / (2 * π * k) := h1
      _ ≤ L / (2 * π * k) * ((1 + R) ^ 5 * (1 + ‖ξ‖) ^ (-5 : ℝ)) :=
          le_mul_of_one_le_right (by positivity) h2
      _ = L / (2 * π * k) * (1 + R) ^ 5 * (1 + ‖ξ‖) ^ (-5 : ℝ) := by ring
      _ ≤ _ := by gcongr; exact le_add_of_nonneg_right (abs_nonneg _)

lemma measurable_helmDiv {k : ℝ} {F : ℂ → ℂ} (hF : Continuous F) :
    Measurable (helmDiv k F) := by
  unfold helmDiv helmSymb
  fun_prop

/-! ### The potential -/

/-- Fourier construction of a potential. -/
theorem exists_helmholtz_potential {k : ℝ} (hk : 0 < k) {G : ℂ → ℂ} (hG : ContDiff ℝ ∞ G)
    (hGc : HasCompactSupport G) (hvan : ∀ ξ : ℂ, ‖ξ‖ = k / (2 * π) → 𝓕 G ξ = 0) :
    ∃ w : ℂ → ℂ, ContDiff ℝ 2 w ∧
      (∀ z, Laplacian.laplacian w z + (k : ℂ) ^ 2 * w z = -G z) ∧
      MemLp w 2 ∧ MemLp (fderiv ℝ w) 2 := by
  obtain ⟨Gs, hGs⟩ : ∃ Gs : 𝓢(ℂ, ℂ), Gs = hGc.toSchwartzMap hG := ⟨_, rfl⟩
  have hGs_apply : ∀ x, Gs x = G x := fun x => by rw [hGs]; rfl
  obtain ⟨Fs, hFs⟩ : ∃ Fs : 𝓢(ℂ, ℂ), Fs = 𝓕⁻ Gs := ⟨_, rfl⟩
  have hFcoe : ∀ ξ, Fs ξ = 𝓕 G (-ξ) := fun ξ => by
    have : (Gs : ℂ → ℂ) = G := funext hGs_apply
    rw [hFs, SchwartzMap.fourierInv_coe, this, Real.fourierInv_eq_fourier_neg]
  have hFvan : ∀ ξ : ℂ, ‖ξ‖ = k / (2 * π) → Fs ξ = 0 := fun ξ h => by
    rw [hFcoe]; exact hvan _ (by rwa [norm_neg])
  have hFG : ∀ z, 𝓕 (Fs : ℂ → ℂ) z = G z := fun z => by
    rw [← SchwartzMap.fourier_coe, hFs, FourierInvPair.fourier_fourierInv_eq, hGs_apply]
  obtain ⟨H, hH⟩ : ∃ H : ℂ → ℂ, H = helmDiv k Fs := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ := norm_helmDiv_le hk Fs hFvan
  rw [← hH] at hC
  have hHm : Measurable H := hH ▸ measurable_helmDiv Fs.continuous
  have hpow : ∀ n : ℕ, n ≤ 2 → ∀ ξ : ℂ, ‖ξ‖ ^ n * ‖H ξ‖ ≤ C * (1 + ‖ξ‖) ^ (-3 : ℝ) := by
    intro n hn ξ
    have h0 : 0 < 1 + ‖ξ‖ := by positivity
    have h1 : ‖ξ‖ ^ n ≤ (1 + ‖ξ‖) ^ (2 : ℝ) := by
      rw [Real.rpow_two]
      calc ‖ξ‖ ^ n ≤ (1 + ‖ξ‖) ^ n := pow_le_pow_left₀ (norm_nonneg _) (by linarith) n
        _ ≤ (1 + ‖ξ‖) ^ 2 := pow_le_pow_right₀ (by linarith [norm_nonneg ξ]) hn
    have hC0 : 0 ≤ C := le_trans (by positivity) ((hC 0).trans (le_of_eq (by simp)))
    calc ‖ξ‖ ^ n * ‖H ξ‖ ≤ (1 + ‖ξ‖) ^ (2 : ℝ) * (C * (1 + ‖ξ‖) ^ (-5 : ℝ)) := by
          gcongr; exact hC ξ
      _ = C * (1 + ‖ξ‖) ^ (-3 : ℝ) := by
          rw [mul_left_comm, ← Real.rpow_add h0]; norm_num
  have hint3 : Integrable (fun ξ : ℂ => (1 + ‖ξ‖) ^ (-3 : ℝ)) :=
    integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
  have hint : ∀ n : ℕ, n ≤ 2 → Integrable fun ξ : ℂ => ‖ξ‖ ^ n * ‖H ξ‖ := fun n hn =>
    Integrable.mono' (hint3.const_mul C) (by fun_prop) (Eventually.of_forall fun ξ => by
      rw [Real.norm_of_nonneg (by positivity)]; exact hpow n hn ξ)
  have hH0 := integrable_memLp_of_le hHm.aestronglyMeasurable (D := C)
    (fun ξ => by simpa using hpow 0 (by norm_num) ξ)
  obtain ⟨K, hKdef⟩ : ∃ K : ℂ → ℂ → ℂ,
      K = fun v ξ => (-(2 * π * I) * (⟪ξ, v⟫_ℝ : ℂ)) * H ξ := ⟨_, rfl⟩
  have hK : ∀ v : ℂ, ‖v‖ = 1 → Integrable (K v) ∧ MemLp (K v) 2 := by
    intro v hv
    refine integrable_memLp_of_le (by rw [hKdef]; fun_prop) (D := 2 * π * C) fun ξ => ?_
    have h1 := hpow 1 (by norm_num) ξ
    rw [pow_one] at h1
    have h2 : |⟪ξ, v⟫_ℝ| ≤ ‖ξ‖ := by
      have := abs_real_inner_le_norm ξ v; rwa [hv, mul_one] at this
    rw [hKdef]
    simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
      Complex.norm_ofNat, abs_of_pos Real.pi_pos]
    calc 2 * π * |⟪ξ, v⟫_ℝ| * ‖H ξ‖ ≤ 2 * π * (‖ξ‖ * ‖H ξ‖) := by
          rw [mul_assoc]; gcongr
      _ ≤ 2 * π * C * (1 + ‖ξ‖) ^ (-3 : ℝ) := by rw [mul_assoc (2 * π)]; gcongr
  have hcd : ContDiff ℝ 2 (𝓕 H) := Real.contDiff_fourier (N := 2) (fun n hn => hint n (by exact_mod_cast hn))
  refine ⟨𝓕 H, hcd, fun z => ?_, memLp_two_fourier hH0.1 hH0.2, ?_⟩
  · rw [laplacian_fourier hHm.aestronglyMeasurable hint z]
    have hcH : Integrable fun ξ : ℂ => ((-(4 * π ^ 2 * ‖ξ‖ ^ 2) : ℝ) : ℂ) * H ξ :=
      Integrable.mono' ((hint 2 le_rfl).const_mul (4 * π ^ 2)) (by fun_prop)
        (Eventually.of_forall fun ξ => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
            abs_of_nonneg (by positivity), mul_assoc])
    have e1 := fourier_lincomb hcH hH0.1 1 ((k : ℂ) ^ 2) z
    have e2 := fourier_lincomb (Fs.integrable (μ := volume)) (Fs.integrable (μ := volume)) (-1) 0 z
    have hfun : (fun ξ => 1 * (((-(4 * π ^ 2 * ‖ξ‖ ^ 2) : ℝ) : ℂ) * H ξ) + (k : ℂ) ^ 2 * H ξ) =
        fun ξ => -1 * Fs ξ + 0 * Fs ξ := by
      funext ξ
      have := helmSymb_mul_helmDiv hk hFvan ξ
      rw [← hH, helmSymb] at this
      rw [← this]; push_cast; ring
    rw [hfun, e2, hFG] at e1
    linear_combination -e1
  · have h1 := hK 1 (by simp)
    have hI := hK I (by simp)
    have hm1 := memLp_two_fourier h1.1 h1.2
    have hmI := memLp_two_fourier hI.1 hI.2
    have hH1 : Integrable fun ξ : ℂ => ‖ξ‖ * ‖H ξ‖ := by simpa using hint 1 (by norm_num)
    refine MemLp.of_le (hm1.norm.add hmI.norm)
      ((hcd.continuous_fderiv (by norm_num)).aestronglyMeasurable)
      (Eventually.of_forall fun z => ?_)
    refine (norm_clm_le_one_I _).trans ?_
    rw [fderiv_fourier_apply hH0.1 hH1 z 1, fderiv_fourier_apply hH0.1 hH1 z I, hKdef]
    simp only [Pi.add_apply, Real.norm_eq_abs]
    exact le_abs_self _

end

section

/-! ## The duality step of the Runge approximation theorem -/

open scoped InnerProductSpace ComplexConjugate FourierTransform ContDiff
open MeasureTheory Set Real Metric Complex Filter Topology

/-- The core duality statement. -/
theorem runge_core {k : ℝ} (hk : 0 < k) {Ω A : Set ℂ} (hΩ : IsOpen Ω) (hA : IsCompact A)
    (hAΩ : A ⊆ Ω) (hAc : IsPreconnected Aᶜ) {G : ℂ → ℂ} (hG : ContDiff ℝ ∞ G)
    (hGA : ∀ z ∉ A, G z = 0) (hvan : ∀ ξ : ℂ, ‖ξ‖ = k / (2 * π) → 𝓕 G ξ = 0) {φ : ℂ → ℂ}
    (hφ : IsHelmholtzOn k φ Ω) : ∫ z, G z * φ z = 0 := by
  have hGc : HasCompactSupport G :=
    HasCompactSupport.intro hA fun z hz => hGA z hz
  obtain ⟨w, hw, hwe, hw2, hdw2⟩ := exists_helmholtz_potential hk hG hGc hvan
  obtain ⟨R0, hR0⟩ := hA.isBounded.subset_closedBall 0
  have hAo : IsOpen Aᶜ := hA.isClosed.isOpen_compl
  have hwH : IsHelmholtzOn k w Aᶜ := by
    refine ⟨hw.contDiffOn, fun z hz => ?_⟩
    rw [hwe z, hGA z hz, neg_zero]
  have hext : {z : ℂ | R0 < ‖z‖} ⊆ Aᶜ := fun z hz hzA => by
    have := hR0 hzA
    simp only [mem_closedBall, dist_zero_right] at this
    exact absurd hz (not_lt.2 this)
  have hwext := helmholtz_exterior_eq_zero hk (hwH.mono hext) hw2 hdw2
  have hwA : ∀ z ∉ A, w z = 0 :=
    helmholtz_eq_zero_of_isPreconnected hk.ne' hAo hAc hwH
      (isOpen_lt continuous_const continuous_norm)
      ⟨((|R0| + 1 : ℝ) : ℂ), by
        simp only [mem_setOf_eq, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_pos (by positivity)]; linarith [le_abs_self R0]⟩
      hext (fun z hz => hwext z hz)
  have hgr := integral_helmholtz_green hΩ hA hAΩ hw hwA hφ
  simp only [hwe, neg_mul, integral_neg, neg_eq_zero] at hgr
  exact hgr

end

section

/-! ## Interior estimates for the Helmholtz equation -/

open scoped InnerProductSpace ComplexConjugate Convolution ContDiff
open MeasureTheory Set Real Metric Complex Filter Topology

/-- Radial profile of the bump: `smoothTransition(1 - r²/ρ₁²)`. -/
def rungeBump0 (ρ1 r : ℝ) : ℝ := Real.smoothTransition (1 - r ^ 2 / ρ1 ^ 2)

/-- The smooth radial bump `y ↦ smoothTransition(1 - |y|²/ρ₁²)`, supported in `B̄(0, ρ₁)`. -/
def rungeBump (ρ1 : ℝ) (y : ℂ) : ℝ := rungeBump0 ρ1 ‖y‖

lemma continuous_rungeBump0 (ρ1 : ℝ) : Continuous (rungeBump0 ρ1) :=
  Real.smoothTransition.continuous.comp (by fun_prop)

lemma rungeBump0_eq_zero {ρ1 : ℝ} (hρ1 : 0 < ρ1) {r : ℝ} (hr : ρ1 ≤ r) : rungeBump0 ρ1 r = 0 := by
  unfold rungeBump0
  apply Real.smoothTransition.zero_of_nonpos
  have h1 : ρ1 ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hρ1.le hr 2
  have h2 : 1 ≤ r ^ 2 / ρ1 ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
  linarith

lemma contDiff_rungeBump (ρ1 : ℝ) {n : ℕ∞} : ContDiff ℝ n (rungeBump ρ1) := by
  have : rungeBump ρ1 = fun y : ℂ => Real.smoothTransition (1 - ‖y‖ ^ 2 / ρ1 ^ 2) := rfl
  rw [this]
  exact Real.smoothTransition.contDiff.comp (contDiff_const.sub ((contDiff_norm_sq ℝ).div_const _))

lemma contDiff_rungeBumpC (ρ1 : ℝ) {n : ℕ∞} : ContDiff ℝ n fun y => (rungeBump ρ1 y : ℂ) :=
  ofRealCLM.contDiff.comp (contDiff_rungeBump ρ1)

lemma rungeBump_nonneg (ρ1 : ℝ) (y : ℂ) : 0 ≤ rungeBump ρ1 y := Real.smoothTransition.nonneg _

lemma rungeBump_zero (ρ1 : ℝ) : rungeBump ρ1 0 = 1 := by
  simp [rungeBump, rungeBump0, Real.smoothTransition.one_of_one_le]

lemma rungeBump_eq_zero {ρ1 : ℝ} (hρ1 : 0 < ρ1) {y : ℂ} (hy : ρ1 ≤ ‖y‖) : rungeBump ρ1 y = 0 :=
  rungeBump0_eq_zero hρ1 hy

lemma hasCompactSupport_rungeBump {ρ1 : ℝ} (hρ1 : 0 < ρ1) : HasCompactSupport (rungeBump ρ1) :=
  HasCompactSupport.intro (isCompact_closedBall 0 ρ1) fun y hy => rungeBump_eq_zero hρ1 (by
    rw [mem_closedBall, dist_zero_right, not_le] at hy; exact hy.le)

lemma hasCompactSupport_rungeBumpC {ρ1 : ℝ} (hρ1 : 0 < ρ1) :
    HasCompactSupport fun y => (rungeBump ρ1 y : ℂ) :=
  (hasCompactSupport_rungeBump hρ1).comp_left (g := ((↑) : ℝ → ℂ)) (by simp)

lemma rungeBump_neg (ρ1 : ℝ) (y : ℂ) : rungeBump ρ1 (-y) = rungeBump ρ1 y := by
  simp [rungeBump]

/-- For small radii, the mean value constant `∫ χ J` is nonzero. -/
lemma exists_rungeBump_ne_zero (k : ℝ) :
    ∃ ρk > 0, ∀ ρ1 ∈ Ioc 0 ρk, ∫ y, (rungeBump ρ1 y : ℂ) * fbWave k 0 y ≠ 0 := by
  have hc : ContinuousAt (fbWave k 0) 0 := (continuous_fbWave k 0).continuousAt
  obtain ⟨ρk, hρk, hball⟩ := Metric.continuousAt_iff.1 hc (1 / 2) (by norm_num)
  refine ⟨ρk, hρk, fun ρ1 hρ1 hzero => ?_⟩
  have hρ0 := hρ1.1
  set χ : ℂ → ℝ := rungeBump ρ1
  have hχc : Continuous χ := (contDiff_rungeBump ρ1 (n := 0)).continuous
  have hχs : HasCompactSupport χ := hasCompactSupport_rungeBump hρ0
  have hIpos : 0 < ∫ y, χ y :=
    hχc.integral_pos_of_hasCompactSupport_nonneg_nonzero hχs (rungeBump_nonneg ρ1)
      (x := 0) (by simp [χ, rungeBump_zero])
  have hJ1 : Continuous fun y => fbWave k 0 y - 1 := (continuous_fbWave k 0).sub continuous_const
  have i1 : Integrable fun y => (χ y : ℂ) * (fbWave k 0 y - 1) :=
    ((continuous_ofReal.comp hχc).mul hJ1).integrable_of_hasCompactSupport
      (hasCompactSupport_rungeBumpC hρ0).mul_right
  have i2 : Integrable fun y => (χ y : ℂ) :=
    (continuous_ofReal.comp hχc).integrable_of_hasCompactSupport (hasCompactSupport_rungeBumpC hρ0)
  have e : ∫ y, (χ y : ℂ) * fbWave k 0 y =
      ((∫ y, χ y : ℝ) : ℂ) + ∫ y, (χ y : ℂ) * (fbWave k 0 y - 1) := by
    rw [← integral_complex_ofReal, ← integral_add i2 i1]
    congr 1; funext y; ring
  have hbound : ‖∫ y, (χ y : ℂ) * (fbWave k 0 y - 1)‖ ≤ (1 / 2) * ∫ y, χ y := by
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le ((hχc.integrable_of_hasCompactSupport hχs).const_mul (1 / 2))
      (Eventually.of_forall fun y => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (rungeBump_nonneg ρ1 y)]
    by_cases hy : ‖y‖ < ρ1
    · have : ‖fbWave k 0 y - 1‖ ≤ 1 / 2 := by
        have := hball (x := y) (by rw [dist_zero_right]; exact hy.trans_le hρ1.2)
        rw [dist_eq_norm, fbWave_zero_zero] at this
        exact this.le
      nlinarith [rungeBump_nonneg ρ1 y]
    · simp [χ, rungeBump_eq_zero hρ0 (not_lt.1 hy)]
  rw [hzero] at e
  have : ‖((∫ y, χ y : ℝ) : ℂ)‖ ≤ (1 / 2) * ∫ y, χ y := by
    rw [show ((∫ y, χ y : ℝ) : ℂ) = -∫ y, (χ y : ℂ) * (fbWave k 0 y - 1) by
      linear_combination -e, norm_neg]
    exact hbound
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hIpos] at this
  linarith

/-- Cauchy–Schwarz inequality for integrals of norms. -/
lemma integral_norm_mul_norm_le {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {f : ℂ → E} {g : ℂ → F} (hf : MemLp f 2) (hg : MemLp g 2) :
    ∫ t, ‖f t‖ * ‖g t‖ ≤ Real.sqrt (∫ t, ‖f t‖ ^ 2) * Real.sqrt (∫ t, ‖g t‖ ^ 2) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) Real.HolderConjugate.two_two
    (f := fun t => ‖f t‖) (g := fun t => ‖g t‖)
    (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall fun _ => norm_nonneg _)
    (by rw [show ENNReal.ofReal 2 = 2 by norm_num]; exact hf.norm)
    (by rw [show ENNReal.ofReal 2 = 2 by norm_num]; exact hg.norm)
  simp only [Real.rpow_two] at h
  rwa [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

lemma memLp_two_of_continuous_hasCompactSupport {E : Type*} [NormedAddCommGroup E]
    {g : ℂ → E} (hg : Continuous g) (hgc : HasCompactSupport g) : MemLp g 2 :=
  hg.memLp_of_hasCompactSupport hgc

/-- Truncation of `u` to the closed disk `B̄(x, r)`. -/
def truncDisk (u : ℂ → ℂ) (x : ℂ) (r : ℝ) : ℂ → ℂ := (closedBall x r).indicator u

lemma memLp_truncDisk {u : ℂ → ℂ} {x : ℂ} {r : ℝ} (hu : ContinuousOn u (closedBall x r)) :
    MemLp (truncDisk u x r) 2 := by
  unfold truncDisk
  rw [memLp_indicator_iff_restrict measurableSet_closedBall]
  rw [memLp_two_iff_integrable_sq_norm (hu.aestronglyMeasurable measurableSet_closedBall)]
  exact ContinuousOn.integrableOn_compact (isCompact_closedBall x r) ((hu.norm).pow 2)

lemma integrable_truncDisk {u : ℂ → ℂ} {x : ℂ} {r : ℝ} (hu : ContinuousOn u (closedBall x r)) :
    Integrable (truncDisk u x r) := by
  unfold truncDisk
  rw [integrable_indicator_iff measurableSet_closedBall]
  exact ContinuousOn.integrableOn_compact (isCompact_closedBall x r) hu

lemma integral_norm_truncDisk_sq (u : ℂ → ℂ) (x : ℂ) (r : ℝ) :
    ∫ t, ‖truncDisk u x r t‖ ^ 2 = ∫ t in closedBall x r, ‖u t‖ ^ 2 := by
  rw [← integral_indicator measurableSet_closedBall]
  congr 1; funext t
  by_cases ht : t ∈ closedBall x r <;> simp [truncDisk, ht]

/-- Convolution representation: near `x`, `c u = ũ ⋆ χ`. -/
lemma helmholtz_eq_convolution {k : ℝ} (hk : k ≠ 0) {u : ℂ → ℂ} {x : ℂ} {δ ρ1 : ℝ}
    (hu : IsHelmholtzOn k u (ball x δ)) (hρ1 : 0 < ρ1) (hρ1δ : ρ1 ≤ δ / 4) {y : ℂ}
    (hy : y ∈ ball x (δ / 4)) :
    (truncDisk u x (δ / 2) ⋆[ContinuousLinearMap.mul ℝ ℂ] fun t => (rungeBump ρ1 t : ℂ)) y =
      (∫ t, (rungeBump ρ1 t : ℂ) * fbWave k 0 t) * u y := by
  rw [convolution_def]
  simp only [ContinuousLinearMap.mul_apply']
  rw [← integral_add_left_eq_self (fun t => truncDisk u x (δ / 2) t * (rungeBump ρ1 (y - t) : ℂ)) y]
  have hpt : ∀ s : ℂ, truncDisk u x (δ / 2) (y + s) * (rungeBump ρ1 (y - (y + s)) : ℂ) =
      (rungeBump0 ρ1 ‖s‖ : ℂ) * u (y + s) := by
    intro s
    rw [show y - (y + s) = -s by ring, rungeBump_neg, mul_comm]
    by_cases hs : ‖s‖ < ρ1
    · have hmem : y + s ∈ closedBall x (δ / 2) := by
        rw [mem_closedBall, dist_eq_norm]
        rw [mem_ball, dist_eq_norm] at hy
        calc ‖y + s - x‖ = ‖(y - x) + s‖ := by ring_nf
          _ ≤ ‖y - x‖ + ‖s‖ := norm_add_le _ _
          _ ≤ δ / 2 := by linarith
      simp [truncDisk, hmem, rungeBump]
    · simp [rungeBump, rungeBump0_eq_zero hρ1 (not_lt.1 hs)]
  simp_rw [hpt]
  have hball : ball y (3 * δ / 4) ⊆ ball x δ := by
    intro z hz
    rw [mem_ball] at hz hy ⊢
    calc dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
      _ < 3 * δ / 4 + δ / 4 := add_lt_add hz hy
      _ = δ := by ring
  have hδ : 0 < δ := by linarith
  rw [integral_radial_mul_helmholtz hk (hu.mono hball) (continuous_rungeBump0 ρ1)
    (by linarith) (fun r hr => rungeBump0_eq_zero hρ1 hr), mul_comm]
  rfl

/-- **Interior estimate**: values and first derivatives of a Helmholtz solution are controlled by
its `L²` norm on a neighbouring disk. -/
theorem helmholtz_C1_le_L2 {k : ℝ} (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ (u : ℂ → ℂ) (x : ℂ), IsHelmholtzOn k u (ball x δ) →
      ‖u x‖ ≤ C * Real.sqrt (∫ z in closedBall x (δ / 2), ‖u z‖ ^ 2) ∧
      ‖fderiv ℝ u x‖ ≤ C * Real.sqrt (∫ z in closedBall x (δ / 2), ‖u z‖ ^ 2) := by
  obtain ⟨ρk, hρk, hne⟩ := exists_rungeBump_ne_zero k
  set ρ1 := min (δ / 4) ρk with hρ1def
  have hρ1 : 0 < ρ1 := lt_min (by linarith) hρk
  have hρ1δ : ρ1 ≤ δ / 4 := min_le_left _ _
  set c := ∫ t, (rungeBump ρ1 t : ℂ) * fbWave k 0 t with hcdef
  have hc : c ≠ 0 := hne ρ1 ⟨hρ1, min_le_right _ _⟩
  set χ : ℂ → ℂ := fun t => (rungeBump ρ1 t : ℂ) with hχdef
  have hχs : HasCompactSupport χ := hasCompactSupport_rungeBumpC hρ1
  have hχc : ContDiff ℝ 1 χ := contDiff_rungeBumpC ρ1
  have hDχc : Continuous (fderiv ℝ χ) := hχc.continuous_fderiv (by norm_num)
  have hDχs : HasCompactSupport (fderiv ℝ χ) := hχs.fderiv ℝ
  set A0 := Real.sqrt (∫ t, ‖χ t‖ ^ 2)
  set A1 := Real.sqrt (∫ t, ‖fderiv ℝ χ t‖ ^ 2)
  refine ⟨(A0 + A1) / ‖c‖, fun u x hu => ?_⟩
  have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc
  set ũ := truncDisk u x (δ / 2)
  have hcl : closedBall x (δ / 2) ⊆ ball x δ := closedBall_subset_ball (by linarith)
  have hucont : ContinuousOn u (closedBall x (δ / 2)) := hu.1.continuousOn.mono hcl
  have hũ : MemLp ũ 2 := memLp_truncDisk hucont
  have hũi : Integrable ũ := integrable_truncDisk hucont
  set S := ∫ z in closedBall x (δ / 2), ‖u z‖ ^ 2
  have hS : ∫ t, ‖ũ t‖ ^ 2 = S := integral_norm_truncDisk_sq u x (δ / 2)
  have hA0 : 0 ≤ A0 := Real.sqrt_nonneg _
  have hA1 : 0 ≤ A1 := Real.sqrt_nonneg _
  have hsS : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
  -- translates of `χ` and `Dχ`
  have htrχ : MemLp (fun t => χ (x - t)) 2 :=
    memLp_two_of_continuous_hasCompactSupport (hχc.continuous.comp (by fun_prop))
      (hχs.comp_homeomorph (Homeomorph.subLeft x))
  have htrD : MemLp (fun t => fderiv ℝ χ (x - t)) 2 :=
    memLp_two_of_continuous_hasCompactSupport (hDχc.comp (by fun_prop))
      (hDχs.comp_homeomorph (Homeomorph.subLeft x))
  have hint0 : ∫ t, ‖χ (x - t)‖ ^ 2 = ∫ t, ‖χ t‖ ^ 2 :=
    integral_sub_left_eq_self (fun t => ‖χ t‖ ^ 2) volume x
  have hint1 : ∫ t, ‖fderiv ℝ χ (x - t)‖ ^ 2 = ∫ t, ‖fderiv ℝ χ t‖ ^ 2 :=
    integral_sub_left_eq_self (fun t => ‖fderiv ℝ χ t‖ ^ 2) volume x
  have hx : x ∈ ball x (δ / 4) := mem_ball_self (by linarith)
  constructor
  · -- value
    have hrep := helmholtz_eq_convolution hk.ne' hu hρ1 hρ1δ hx
    rw [convolution_def] at hrep
    simp only [ContinuousLinearMap.mul_apply'] at hrep
    have hle : ‖c * u x‖ ≤ A0 * Real.sqrt S := by
      rw [← hrep]
      refine (norm_integral_le_integral_norm _).trans ?_
      simp only [norm_mul]
      refine (integral_norm_mul_norm_le hũ htrχ).trans (le_of_eq ?_)
      rw [hS, hint0]; ring
    rw [norm_mul] at hle
    rw [div_mul_eq_mul_div, le_div_iff₀ hcpos]
    nlinarith
  · -- derivative
    have hev : (fun y => c • u y) =ᶠ[𝓝 x]
        (ũ ⋆[ContinuousLinearMap.mul ℝ ℂ] χ) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      rw [helmholtz_eq_convolution hk.ne' hu hρ1 hρ1δ hy, smul_eq_mul]
    have hconv := hχs.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
      hũi.locallyIntegrable hχc x
    have hdu : DifferentiableAt ℝ u x :=
      (hu.1.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hδ))
    have hfd : c • fderiv ℝ u x =
        (ũ ⋆[(ContinuousLinearMap.mul ℝ ℂ).precompR ℂ] fderiv ℝ χ) x := by
      rw [← fderiv_const_smul hdu c, ← hconv.fderiv]
      exact hev.fderiv_eq
    have hle : ‖c • fderiv ℝ u x‖ ≤ A1 * Real.sqrt S := by
      rw [hfd, convolution_def]
      refine (norm_integral_le_integral_norm _).trans ?_
      have hpt : ∀ t, ‖((ContinuousLinearMap.mul ℝ ℂ).precompR ℂ) (ũ t) (fderiv ℝ χ (x - t))‖ ≤
          ‖ũ t‖ * ‖fderiv ℝ χ (x - t)‖ := fun t => by
        refine (ContinuousLinearMap.le_opNorm₂ _ _ _).trans ?_
        have h1 : ‖(ContinuousLinearMap.mul ℝ ℂ).precompR ℂ‖ ≤ 1 :=
          (ContinuousLinearMap.norm_precompR_le _ _).trans (ContinuousLinearMap.opNorm_mul_le ℝ ℂ)
        have h2 : 0 ≤ ‖ũ t‖ * ‖fderiv ℝ χ (x - t)‖ := by positivity
        nlinarith [norm_nonneg ((ContinuousLinearMap.mul ℝ ℂ).precompR ℂ), norm_nonneg (ũ t),
          norm_nonneg (fderiv ℝ χ (x - t))]
      have hint : Integrable fun t => ‖ũ t‖ * ‖fderiv ℝ χ (x - t)‖ := by
        have := (hũ.norm).integrable_mul (htrD.norm) (p := 2) (q := 2)
        exact this
      refine (integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _) hint
        (Eventually.of_forall hpt)).trans ?_
      refine (integral_norm_mul_norm_le hũ htrD).trans (le_of_eq ?_)
      rw [hS, hint1]; ring
    rw [norm_smul] at hle
    rw [div_mul_eq_mul_div, le_div_iff₀ hcpos]
    nlinarith [norm_nonneg (fderiv ℝ u x)]

end

section

/-! ## `L²` approximation by entire solutions of the Helmholtz equation -/

open scoped InnerProductSpace ComplexConjugate FourierTransform Convolution ContDiff
open MeasureTheory Set Real Metric Complex Filter Topology

/-- The real-linear phase of a plane wave. -/
def pwL (ξ : ℂ) : ℂ →L[ℝ] ℂ := ((-(2 * π) : ℂ) * I) • (ofRealCLM.comp (innerSL ℝ ξ))

/-- The plane wave `z ↦ e^{-2πi ⟪z, ξ⟫}`. -/
def planeWave (ξ : ℂ) (z : ℂ) : ℂ := cexp (pwL ξ z)

lemma pwL_apply (ξ z : ℂ) : pwL ξ z = (-(2 * π) : ℂ) * I * (⟪ξ, z⟫_ℝ : ℂ) := by
  simp [pwL]

lemma fourierChar_eq_planeWave (ξ z : ℂ) : ((𝐞 (-⟪z, ξ⟫_ℝ) : Circle) : ℂ) = planeWave ξ z := by
  rw [Real.fourierChar_apply, planeWave, pwL_apply, real_inner_comm]
  congr 1; push_cast; ring

lemma fourier_eq_integral_planeWave (G : ℂ → ℂ) (ξ : ℂ) :
    𝓕 G ξ = ∫ z, G z * planeWave ξ z := by
  rw [Real.fourier_eq]
  congr 1; funext z
  rw [Circle.smul_def, smul_eq_mul, fourierChar_eq_planeWave, mul_comm]

lemma hasFDerivAt_planeWave (ξ z : ℂ) :
    HasFDerivAt (planeWave ξ) (planeWave ξ z • pwL ξ) z :=
  (pwL ξ).hasFDerivAt.cexp

lemma fderiv_fderiv_planeWave (ξ z v w : ℂ) :
    fderiv ℝ (fderiv ℝ (planeWave ξ)) z v w = planeWave ξ z * pwL ξ v * pwL ξ w := by
  have h1 : fderiv ℝ (planeWave ξ) = fun y => planeWave ξ y • pwL ξ := by
    funext y; exact (hasFDerivAt_planeWave ξ y).fderiv
  rw [h1, ((hasFDerivAt_planeWave ξ z).smul_const (pwL ξ)).fderiv]
  simp [smul_eq_mul, mul_assoc]

lemma contDiff_planeWave (ξ : ℂ) : ContDiff ℝ 2 (planeWave ξ) :=
  (pwL ξ).contDiff.cexp

/-- Plane waves with `|ξ| = k/2π` solve the Helmholtz equation. -/
lemma isHelmholtzOn_planeWave {k : ℝ} {ξ : ℂ} (hξ : ‖ξ‖ = k / (2 * π)) (Ω : Set ℂ) :
    IsHelmholtzOn k (planeWave ξ) Ω := by
  refine ⟨(contDiff_planeWave ξ).contDiffOn, fun z _ => ?_⟩
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [fderiv_fderiv_planeWave, fderiv_fderiv_planeWave, pwL_apply, pwL_apply]
  have h1 : ⟪ξ, (1 : ℂ)⟫_ℝ = ξ.re := by simp [Complex.inner]
  have h2 : ⟪ξ, I⟫_ℝ = ξ.im := by simp [Complex.inner]
  rw [h1, h2]
  have hk : (k : ℂ) = 2 * π * ‖ξ‖ := by
    rw [hξ]; push_cast; field_simp
  have hn : (‖ξ‖ : ℂ) ^ 2 = (ξ.re : ℂ) ^ 2 + (ξ.im : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.normSq_apply]; push_cast; ring
  rw [hk]
  linear_combination (4 * (π : ℂ) ^ 2 * planeWave ξ z) * hn +
    (4 * (π : ℂ) ^ 2 * planeWave ξ z * ((ξ.re : ℂ) ^ 2 + (ξ.im : ℂ) ^ 2)) * Complex.I_sq

lemma isCompact_cthickening_of_isBounded {B : Set ℂ} (hBb : Bornology.IsBounded B) (δ : ℝ) :
    IsCompact (cthickening δ B) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_cthickening hBb.cthickening

/-- The smoothed density vanishes outside `cthickening δ B`. -/
lemma convolution_rungeBump_eq_zero {B : Set ℂ} {δ ρ1 : ℝ} (hρ1 : 0 < ρ1) (hρδ : ρ1 ≤ δ)
    {F : ℂ → ℂ} (hFB : ∀ t ∉ B, F t = 0) {z : ℂ} (hz : z ∉ cthickening δ B) :
    (F ⋆[ContinuousLinearMap.mul ℝ ℂ] fun t => (rungeBump ρ1 t : ℂ)) z = 0 := by
  rw [convolution_def]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.mul_apply', Pi.zero_apply]
  by_cases ht : t ∈ B
  · have hd : δ < dist z t := by
      by_contra h
      exact hz (mem_cthickening_of_dist_le z t δ B ht (not_lt.1 h))
    rw [rungeBump_eq_zero hρ1 (by rw [← dist_eq_norm]; linarith)]
    simp
  · rw [hFB t ht, zero_mul]

/-- **Smoothing identity.** Pairing the smoothed density `F ⋆ χ` with a Helmholtz solution
multiplies the pairing of `F` by the mean value constant `∫ χ J`. -/
lemma integral_convolution_mul_helmholtz {k : ℝ} (hk : k ≠ 0) {Ω B : Set ℂ} {δ ρ1 : ℝ}
    (hρ1 : 0 < ρ1) (hρδ : ρ1 < δ) (hBb : Bornology.IsBounded B)
    (hBΩ : cthickening δ B ⊆ Ω) {F : ℂ → ℂ} (hF : Integrable F) (hFB : ∀ t ∉ B, F t = 0)
    {u : ℂ → ℂ} (hu : IsHelmholtzOn k u Ω) :
    ∫ z, (F ⋆[ContinuousLinearMap.mul ℝ ℂ] fun t => (rungeBump ρ1 t : ℂ)) z * u z =
      (∫ t, (rungeBump ρ1 t : ℂ) * fbWave k 0 t) * ∫ t, F t * u t := by
  set χ : ℂ → ℂ := fun t => (rungeBump ρ1 t : ℂ) with hχdef
  set K := cthickening δ B with hKdef
  have hK : IsCompact K := isCompact_cthickening_of_isBounded hBb δ
  have hKm : MeasurableSet K := isClosed_cthickening.measurableSet
  have hucK : ContinuousOn u K := hu.1.continuousOn.mono hBΩ
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hucK
  set ū := K.indicator u with hūdef
  have hūM : ∀ z, ‖ū z‖ ≤ max M 0 := fun z => by
    by_cases hz : z ∈ K
    · simp only [hūdef, indicator_of_mem hz]; exact (hM z hz).trans (le_max_left _ _)
    · simp [hūdef, indicator_of_notMem hz]
  have hūm : AEStronglyMeasurable ū volume :=
    (aestronglyMeasurable_indicator_iff hKm).2 (hucK.aestronglyMeasurable hKm)
  have hχint : Integrable χ :=
    (contDiff_rungeBumpC ρ1 (n := 0)).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_rungeBumpC hρ1)
  -- step a: replace `u` by its truncation
  have stepa : ∫ z, (F ⋆[ContinuousLinearMap.mul ℝ ℂ] χ) z * u z =
      ∫ z, (F ⋆[ContinuousLinearMap.mul ℝ ℂ] χ) z * ū z := by
    congr 1; funext z
    by_cases hz : z ∈ K
    · simp [hūdef, indicator_of_mem hz]
    · rw [convolution_rungeBump_eq_zero hρ1 hρδ.le hFB hz]; simp
  -- step b, c: Fubini
  have hint : Integrable (Function.uncurry fun z t => F t * χ (z - t) * ū z)
      (volume.prod volume) := by
    have h1 := hF.convolution_integrand (ContinuousLinearMap.mul ℝ ℂ) hχint
      (μ := volume) (ν := volume)
    have h2 := h1.bdd_mul (f := fun p : ℂ × ℂ => ū p.1) (c := max M 0)
      hūm.comp_fst (Eventually.of_forall fun p => hūM p.1)
    refine h2.congr (Eventually.of_forall fun p => ?_)
    simp only [ContinuousLinearMap.mul_apply', Function.uncurry]
    ring
  have stepb : ∫ z, (F ⋆[ContinuousLinearMap.mul ℝ ℂ] χ) z * ū z =
      ∫ z, ∫ t, F t * χ (z - t) * ū z := by
    congr 1; funext z
    rw [convolution_def, ← integral_mul_const]
    rfl
  rw [stepa, stepb, integral_integral_swap hint, ← integral_const_mul]
  congr 1; funext t
  by_cases ht : t ∈ B
  · have hball : ball t δ ⊆ K := fun y hy =>
      mem_cthickening_of_dist_le y t δ B ht (mem_ball.1 hy).le
    have e1 : ∫ z, F t * χ (z - t) * ū z = F t * ∫ z, χ (z - t) * ū z := by
      rw [← integral_const_mul]; congr 1; funext z; ring
    have e2 : ∫ z, χ (z - t) * ū z = ∫ s, (rungeBump0 ρ1 ‖s‖ : ℂ) * u (t + s) := by
      rw [← integral_add_left_eq_self (fun z => χ (z - t) * ū z) t]
      congr 1; funext s
      simp only [add_sub_cancel_left, hχdef]
      by_cases hs : ‖s‖ < ρ1
      · have hmem : t + s ∈ K := hball (by
          rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; linarith)
        simp [hūdef, indicator_of_mem hmem, rungeBump]
      · simp [rungeBump, rungeBump0_eq_zero hρ1 (not_lt.1 hs)]
    rw [e1, e2, integral_radial_mul_helmholtz hk (hu.mono (hball.trans hBΩ))
      (continuous_rungeBump0 ρ1) hρδ (fun r hr => rungeBump0_eq_zero hρ1 hr)]
    simp only [rungeBump]
    ring
  · simp [hFB t ht]

lemma isHelmholtzOn_zero (k : ℝ) (Ω : Set ℂ) : IsHelmholtzOn k (0 : ℂ → ℂ) Ω := by
  refine ⟨contDiff_const.contDiffOn, fun z _ => ?_⟩
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  have : (0 : ℂ → ℂ) = fun _ => (0 : ℂ) := rfl
  rw [this, iteratedFDeriv_zero_fun]
  simp

lemma IsHelmholtzOn.add {k : ℝ} {ψ φ : ℂ → ℂ} (hψ : IsHelmholtzOn k ψ univ)
    (hφ : IsHelmholtzOn k φ univ) : IsHelmholtzOn k (ψ + φ) univ := by
  refine ⟨hψ.1.add hφ.1, fun z hz => ?_⟩
  have h1 : ContDiffAt ℝ 2 ψ z := hψ.1.contDiffAt (isOpen_univ.mem_nhds hz)
  have h2 : ContDiffAt ℝ 2 φ z := hφ.1.contDiffAt (isOpen_univ.mem_nhds hz)
  rw [h1.laplacian_add h2]
  simp only [Pi.add_apply]
  linear_combination hψ.2 z hz + hφ.2 z hz

lemma IsHelmholtzOn.const_smul {k : ℝ} {ψ : ℂ → ℂ} (hψ : IsHelmholtzOn k ψ univ) (c : ℂ) :
    IsHelmholtzOn k (c • ψ) univ := by
  refine ⟨hψ.1.const_smul c, fun z hz => ?_⟩
  have h1 : ContDiffAt ℝ 2 ψ z := hψ.1.contDiffAt (isOpen_univ.mem_nhds hz)
  rw [InnerProductSpace.laplacian_smul _ h1]
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination c * hψ.2 z hz

lemma L2_norm_sq_toLp {μ : Measure ℂ} {f : ℂ → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def]
  have h : ∀ a, ⟪(hf.toLp f : ℂ → ℂ) a, (hf.toLp f : ℂ → ℂ) a⟫_ℂ =
      ((‖(hf.toLp f : ℂ → ℂ) a‖ ^ 2 : ℝ) : ℂ) := fun a => by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  simp_rw [h]
  rw [integral_complex_ofReal, RCLike.re_to_complex, Complex.ofReal_re]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

lemma L2_inner_toLp {μ : Measure ℂ} (g : Lp ℂ 2 μ) {f : ℂ → ℂ} (hf : MemLp f 2 μ) :
    ⟪g, hf.toLp f⟫_ℂ = ∫ x, conj (g x) * f x ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, RCLike.inner_apply, mul_comm]

/-- **`L²` approximation by entire solutions.** -/
theorem helmholtz_L2_approx {k : ℝ} (hk : 0 < k) {Ω A B : Set ℂ} (hΩ : IsOpen Ω)
    (hA : IsCompact A) (hAΩ : A ⊆ Ω) (hAc : IsPreconnected Aᶜ) (hB : MeasurableSet B)
    (hBb : Bornology.IsBounded B) {δ : ℝ} (hδ : 0 < δ) (hBA : cthickening δ B ⊆ A)
    {φ : ℂ → ℂ} (hφ : IsHelmholtzOn k φ Ω) {η : ℝ} (hη : 0 < η) :
    ∃ ψ : ℂ → ℂ, IsHelmholtzOn k ψ univ ∧ ∫ z in B, ‖ψ z - φ z‖ ^ 2 < η := by
  set μ := volume.restrict B with hμdef
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 hBb.measure_lt_top.ne
  set K := cthickening δ B with hKdef
  have hK : IsCompact K := isCompact_cthickening_of_isBounded hBb δ
  have hKm : MeasurableSet K := isClosed_cthickening.measurableSet
  have hBK : B ⊆ K := self_subset_cthickening B
  have hKΩ : K ⊆ Ω := hBA.trans hAΩ
  have hmem : ∀ f : ℂ → ℂ, ContinuousOn f K → MemLp f 2 μ := fun f hf => by
    have : MemLp f 2 (volume.restrict K) :=
      (memLp_two_iff_integrable_sq_norm (hf.aestronglyMeasurable hKm)).2
        (ContinuousOn.integrableOn_compact hK (hf.norm.pow 2))
    exact this.mono_measure (Measure.restrict_mono hBK le_rfl)
  have hφK : ContinuousOn φ K := hφ.1.continuousOn.mono hKΩ
  set φL := (hmem φ hφK).toLp φ with hφLdef
  set S : Set (Lp ℂ 2 μ) :=
    {f | ∃ ψ : ℂ → ℂ, IsHelmholtzOn k ψ univ ∧ ∃ h : MemLp ψ 2 μ, f = h.toLp ψ} with hSdef
  set M := Submodule.span ℂ S with hMdef
  have hMS : ∀ m ∈ M, m ∈ S := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, isHelmholtzOn_zero k univ, MemLp.zero, (MemLp.toLp_zero _).symm⟩
    | add x y _ _ hx hy =>
      obtain ⟨ψ1, h1, m1, rfl⟩ := hx
      obtain ⟨ψ2, h2, m2, rfl⟩ := hy
      exact ⟨ψ1 + ψ2, h1.add h2, m1.add m2, (MemLp.toLp_add m1 m2).symm⟩
    | smul c x _ hx =>
      obtain ⟨ψ1, h1, m1, rfl⟩ := hx
      exact ⟨c • ψ1, h1.const_smul c, m1.const_smul c, (MemLp.toLp_const_smul c m1).symm⟩
  -- the mean value constant
  obtain ⟨ρk, hρk, hne⟩ := exists_rungeBump_ne_zero k
  set ρ1 := min (δ / 2) ρk with hρ1def
  have hρ1 : 0 < ρ1 := lt_min (by linarith) hρk
  have hρδ : ρ1 < δ := (min_le_left _ _).trans_lt (by linarith)
  set c := ∫ t, (rungeBump ρ1 t : ℂ) * fbWave k 0 t with hcdef
  have hc : c ≠ 0 := hne ρ1 ⟨hρ1, min_le_right _ _⟩
  -- `φL` lies in the closure of `M`
  have hφcl : φL ∈ M.topologicalClosure := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal']
    intro g hg
    rw [Submodule.mem_orthogonal'] at hg
    set Fd : ℂ → ℂ := B.indicator fun x => conj (g x) with hFddef
    have hFdB : ∀ t ∉ B, Fd t = 0 := fun t ht => indicator_of_notMem ht _
    have hFdint : Integrable Fd := by
      rw [integrable_indicator_iff hB]
      exact (Complex.conjCLE.toContinuousLinearMap).integrable_comp
        ((Lp.memLp g).integrable one_le_two)
    have hpair : ∀ (f : ℂ → ℂ) (hf : MemLp f 2 μ), ⟪g, hf.toLp f⟫_ℂ = ∫ x, Fd x * f x := by
      intro f hf
      rw [L2_inner_toLp, ← integral_indicator hB]
      congr 1; funext x
      by_cases hx : x ∈ B <;> simp [hFddef, hx]
    have hzero : ∀ ψ : ℂ → ℂ, IsHelmholtzOn k ψ univ → ∀ h : MemLp ψ 2 μ,
        ∫ x, Fd x * ψ x = 0 := fun ψ hψ h => by
      rw [← hpair ψ h]
      exact hg _ (Submodule.subset_span ⟨ψ, hψ, h, rfl⟩)
    set G := Fd ⋆[ContinuousLinearMap.mul ℝ ℂ] fun t => (rungeBump ρ1 t : ℂ) with hGdef
    have hGs : ContDiff ℝ ∞ G :=
      (hasCompactSupport_rungeBumpC hρ1).contDiff_convolution_right
        (ContinuousLinearMap.mul ℝ ℂ) hFdint.locallyIntegrable (contDiff_rungeBumpC ρ1)
    have hGA : ∀ z ∉ A, G z = 0 := fun z hz =>
      convolution_rungeBump_eq_zero hρ1 hρδ.le hFdB (fun h => hz (hBA h))
    have hvan : ∀ ξ : ℂ, ‖ξ‖ = k / (2 * π) → 𝓕 G ξ = 0 := by
      intro ξ hξ
      rw [fourier_eq_integral_planeWave, integral_convolution_mul_helmholtz (Ω := univ) hk.ne'
        hρ1 hρδ hBb (subset_univ _) hFdint hFdB (isHelmholtzOn_planeWave hξ univ)]
      rw [hzero _ (isHelmholtzOn_planeWave hξ univ)
        (hmem _ (contDiff_planeWave ξ).continuous.continuousOn), mul_zero]
    have hcore := runge_core hk hΩ hA hAΩ hAc hGs hGA hvan hφ
    rw [integral_convolution_mul_helmholtz hk.ne' hρ1 hρδ hBb hKΩ hFdint hFdB hφ] at hcore
    rw [inner_eq_zero_symm, hpair]
    exact (mul_eq_zero.1 hcore).resolve_left hc
  have hφcl' : φL ∈ closure (M : Set (Lp ℂ 2 μ)) := by
    rw [← Submodule.topologicalClosure_coe]; exact hφcl
  obtain ⟨m, hm, hdist⟩ := Metric.mem_closure_iff.1 hφcl' (Real.sqrt η) (Real.sqrt_pos.2 hη)
  obtain ⟨ψ, hψ, hψm, rfl⟩ := hMS m hm
  refine ⟨ψ, hψ, ?_⟩
  have hsub := (hmem φ hφK).sub hψm
  have e1 : ∫ z in B, ‖ψ z - φ z‖ ^ 2 = ‖hsub.toLp (φ - ψ)‖ ^ 2 := by
    rw [L2_norm_sq_toLp]
    congr 1; funext z
    rw [Pi.sub_apply, norm_sub_rev]
  rw [e1, MemLp.toLp_sub (hmem φ hφK) hψm, ← dist_eq_norm]
  have h0 : 0 ≤ dist φL (hψm.toLp ψ) := dist_nonneg
  calc dist φL (hψm.toLp ψ) ^ 2 < Real.sqrt η ^ 2 := by gcongr
    _ = η := Real.sq_sqrt hη.le

end

section

/-! ## The complement of `F(r 𝔻̄)` is connected -/

open Set Metric Complex Filter Topology

theorem isPreconnected_compl_image_closedBall (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hDU : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) : IsPreconnected (F '' closedBall 0 r)ᶜ := by
  have hball1 : ball (0 : ℂ) 1 ⊆ U := ball_subset_closedBall.trans hDU
  have hrU : closedBall (0 : ℂ) r ⊆ U := (closedBall_subset_closedBall hr.2.le).trans hDU
  have hO : IsOpen (F '' ball 0 1) :=
    isOpen_image_of_injOn isOpen_ball (convex_ball _ _).isPreconnected
      (hF.mono hball1) (hinj.mono hball1) subset_rfl isOpen_ball
  have hAc : IsCompact (F '' closedBall 0 r) :=
    (isCompact_closedBall 0 r).image_of_continuousOn (hF.continuousOn.mono hrU)
  have hAo : IsOpen (F '' closedBall 0 r)ᶜ := hAc.isClosed.isOpen_compl
  have hAO : F '' closedBall 0 r ⊆ F '' ball 0 1 := image_mono (closedBall_subset_ball hr.2)
  -- the connected set `W = F(r < |z| < 1)`
  set W := (fun p : ℝ × ℝ => F (p.1 * exp (p.2 * I))) '' (Ioo r 1 ×ˢ univ) with hWdef
  have hpolar : ∀ p ∈ Ioo r 1 ×ˢ (univ : Set ℝ), (p.1 : ℂ) * exp (p.2 * I) ∈ ball (0 : ℂ) 1 ∧
      (p.1 : ℂ) * exp (p.2 * I) ∉ closedBall (0 : ℂ) r := by
    rintro ⟨ρ, θ⟩ ⟨hρ, -⟩
    have hn : ‖(ρ : ℂ) * exp (θ * I)‖ = ρ := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hr.1.trans hρ.1)]
    simp only [mem_ball, dist_zero_right, mem_closedBall, not_le]
    rw [hn]; exact ⟨hρ.2, hρ.1⟩
  have hWc : IsPreconnected W := by
    refine (isPreconnected_Ioo.prod isPreconnected_univ).image _ ?_
    intro p hp
    have h1 := (hpolar p hp).1
    have hc : ContinuousAt (fun p : ℝ × ℝ => (p.1 : ℂ) * exp (p.2 * I)) p := by fun_prop
    have hFc : ContinuousAt F ((p.1 : ℂ) * exp (p.2 * I)) :=
      (hF.differentiableAt (hU.mem_nhds (hball1 h1))).continuousAt
    exact (ContinuousAt.comp (f := fun p : ℝ × ℝ => (p.1 : ℂ) * exp (p.2 * I)) hFc
      hc).continuousWithinAt
  have hWA : W ⊆ (F '' closedBall 0 r)ᶜ := by
    rintro _ ⟨p, hp, rfl⟩ ⟨z', hz', hFz⟩
    have := hinj (hrU hz') (hball1 (hpolar p hp).1) hFz
    exact (hpolar p hp).2 (this ▸ hz')
  have hW0 : F (((r + 1) / 2 : ℝ) * exp ((0 : ℝ) * I)) ∈ W :=
    ⟨((r + 1) / 2, 0), ⟨⟨by linarith [hr.2], by linarith [hr.2]⟩, mem_univ _⟩, rfl⟩
  -- points of `F(𝔻) \ A` lie in `W`
  have hOW : ∀ y ∈ F '' ball 0 1, y ∉ F '' closedBall 0 r → y ∈ W := by
    rintro _ ⟨z, hz, rfl⟩ hzA
    have hzr : r < ‖z‖ := by
      by_contra h
      exact hzA ⟨z, by simpa using not_lt.1 h, rfl⟩
    refine ⟨(‖z‖, arg z), ⟨⟨hzr, by simpa using hz⟩, mem_univ _⟩, ?_⟩
    simp only
    rw [Complex.norm_mul_exp_arg_mul_I]
  set w0 := F (((r + 1) / 2 : ℝ) * exp ((0 : ℝ) * I))
  have key : (F '' closedBall 0 r)ᶜ ⊆ connectedComponentIn (F '' closedBall 0 r)ᶜ w0 := by
    intro x hx
    set C := connectedComponentIn (F '' closedBall 0 r)ᶜ x with hC
    have hCo : IsOpen C := hAo.connectedComponentIn
    have hxC : x ∈ C := mem_connectedComponentIn hx
    have hCA : C ⊆ (F '' closedBall 0 r)ᶜ := connectedComponentIn_subset _ _
    -- `C` is not closed
    have hnc : ¬ IsClosed C := by
      intro hcl
      rcases isClopen_iff.1 ⟨hcl, hCo⟩ with h | h
      · rw [h] at hxC; exact hxC
      · have h0 : F 0 ∈ F '' closedBall 0 r := ⟨0, by simp [hr.1.le], rfl⟩
        exact hCA (h ▸ mem_univ (F 0)) h0
    obtain ⟨p, hpcl, hpC⟩ : ∃ p ∈ closure C, p ∉ C := by
      by_contra h
      push_neg at h
      exact hnc (closure_subset_iff_isClosed.1 h)
    -- the boundary point `p` lies in `A`
    have hpA : p ∈ F '' closedBall 0 r := by
      by_contra hpA
      obtain ⟨ε, hε, hεA⟩ := Metric.isOpen_iff.1 hAo p hpA
      obtain ⟨q, hqB, hqC⟩ := mem_closure_iff.1 hpcl (ball p ε) isOpen_ball (mem_ball_self hε)
      have hsub : ball p ε ⊆ connectedComponentIn (F '' closedBall 0 r)ᶜ q :=
        (convex_ball p ε).isPreconnected.subset_connectedComponentIn hqB hεA
      rw [← connectedComponentIn_eq hqC] at hsub
      exact hpC (hsub (mem_ball_self hε))
    obtain ⟨y, hyO, hyC⟩ := mem_closure_iff.1 hpcl _ hO (hAO hpA)
    have hyW : y ∈ W := hOW y hyO (hCA hyC)
    have hWC : W ⊆ C := by
      have := hWc.subset_connectedComponentIn hyW hWA
      rwa [← connectedComponentIn_eq hyC] at this
    have := connectedComponentIn_eq (hWC hW0)
    rw [← this]
    exact hxC
  have heq : connectedComponentIn (F '' closedBall 0 r)ᶜ w0 = (F '' closedBall 0 r)ᶜ :=
    Subset.antisymm (connectedComponentIn_subset _ _) key
  rw [← heq]
  exact isPreconnected_connectedComponentIn

end

section

/-! ## Runge approximation for the Helmholtz equation -/

open scoped InnerProductSpace ComplexConjugate FourierTransform
open MeasureTheory Set Real Metric Complex Filter Topology

/-- **Runge approximation for the Helmholtz equation** on `F(r_* 𝔻)`. -/
theorem helmholtz_runge_entire_proof (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hDU : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    {k : ℝ} (hk : 0 < k) {rs : ℝ} (hrs : rs ∈ Ioc (0 : ℝ) 1) {φ : ℂ → ℂ}
    (hφ : IsHelmholtzOn k φ (F '' ball 0 rs)) {r : ℝ} (hr : r ∈ Ioo 0 rs) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ ψ : ℂ → ℂ, IsHelmholtzOn k ψ univ ∧ ∀ z ∈ F '' closedBall 0 r,
      ‖ψ z - φ z‖ < ε ∧ ‖fderiv ℝ ψ z - fderiv ℝ φ z‖ < ε := by
  obtain ⟨r1, r2, hrr1, hr12, hr2s⟩ : ∃ r1 r2 : ℝ, r < r1 ∧ r1 < r2 ∧ r2 < rs :=
    ⟨r + (rs - r) / 3, r + 2 * (rs - r) / 3, by linarith [hr.2], by linarith [hr.2],
      by linarith [hr.2]⟩
  have hball1 : ball (0 : ℂ) 1 ⊆ U := ball_subset_closedBall.trans hDU
  have hcl1 : closedBall (0 : ℂ) 1 ⊆ U := hDU
  have hFc : ContinuousOn F U := hF.continuousOn
  have hopen : ∀ s : ℝ, s ≤ 1 → IsOpen (F '' ball 0 s) := fun s hs =>
    isOpen_image_of_injOn isOpen_ball (convex_ball _ _).isPreconnected
      (hF.mono hball1) (hinj.mono hball1) (ball_subset_ball hs) isOpen_ball
  have hcpt : ∀ s : ℝ, s ≤ 1 → IsCompact (F '' closedBall 0 s) := fun s hs =>
    (isCompact_closedBall 0 s).image_of_continuousOn
      (hFc.mono ((closedBall_subset_closedBall hs).trans hDU))
  have hcb : ∀ s t : ℝ, s < t → F '' closedBall 0 s ⊆ F '' ball 0 t := fun s t hst =>
    image_mono (closedBall_subset_ball hst)
  have hrs1 := hrs.2
  obtain ⟨D, hD⟩ : ∃ D, D = F '' ball 0 rs := ⟨_, rfl⟩
  rw [← hD] at hφ
  have hDo : IsOpen D := hD ▸ hopen rs hrs1
  obtain ⟨K, hKd⟩ : ∃ K, K = F '' closedBall 0 r := ⟨_, rfl⟩
  rw [← hKd]
  obtain ⟨Ω1, hΩ1d⟩ : ∃ Ω1, Ω1 = F '' ball 0 r1 := ⟨_, rfl⟩
  have hK : IsCompact K := hKd ▸ hcpt r (by linarith [hr.2])
  have hΩ1 : IsOpen Ω1 := hΩ1d ▸ hopen r1 (by linarith)
  obtain ⟨δ0, hδ0, hδ0K⟩ := hK.exists_cthickening_subset_open hΩ1
    (hKd ▸ hΩ1d ▸ hcb r r1 hrr1)
  obtain ⟨C, hC⟩ := helmholtz_C1_le_L2 hk hδ0
  have hA : IsCompact (F '' closedBall 0 r2) := hcpt r2 (by linarith)
  have hAD : F '' closedBall 0 r2 ⊆ D := hD ▸ hcb r2 rs hr2s
  have hAc : IsPreconnected (F '' closedBall 0 r2)ᶜ :=
    isPreconnected_compl_image_closedBall F U hU hDU hF hinj
      ⟨by linarith [hr.1], by linarith⟩
  have hK1 : IsCompact (F '' closedBall 0 r1) := hcpt r1 (by linarith)
  obtain ⟨δ1, hδ1, hδ1K⟩ := hK1.exists_cthickening_subset_open (hopen r2 (by linarith))
    (hcb r1 r2 hr12)
  have hΩ1sub : Ω1 ⊆ F '' closedBall 0 r1 := hΩ1d ▸ image_mono ball_subset_closedBall
  have hBA : cthickening δ1 Ω1 ⊆ F '' closedBall 0 r2 :=
by
    refine (cthickening_subset_of_subset δ1 hΩ1sub).trans (hδ1K.trans ?_)
    exact image_mono ball_subset_closedBall
  obtain ⟨η, hη⟩ : ∃ η, η = (ε / (|C| + 1)) ^ 2 := ⟨_, rfl⟩
  have hηpos : 0 < η := by rw [hη]; positivity
  obtain ⟨ψ, hψ, hψη⟩ := helmholtz_L2_approx hk hDo hA hAD hAc hΩ1.measurableSet
    (hK1.isBounded.subset hΩ1sub) hδ1 hBA hφ hηpos
  refine ⟨ψ, hψ, fun z hz => ?_⟩
  -- local estimate
  have hΩ1D : Ω1 ⊆ D := hD ▸ (hΩ1sub.trans (hcb r1 rs (by linarith)))
  have hballz : ball z δ0 ⊆ Ω1 :=
    ball_subset_closedBall.trans ((closedBall_subset_cthickening hz δ0).trans hδ0K)
  have hu : IsHelmholtzOn k (fun w => ψ w - φ w) (ball z δ0) :=
    ((hψ.mono (subset_univ D)).sub hDo hφ).mono (hballz.trans hΩ1D)
  obtain ⟨h1, h2⟩ := hC _ z hu
  -- the L² norm over the small disk is at most the L² norm over `Ω1`
  have hcl : closure Ω1 ⊆ D :=
    (closure_minimal hΩ1sub hK1.isClosed).trans (hD ▸ hcb r1 rs (by linarith))
  have hcontD : ContinuousOn (fun w => ψ w - φ w) D :=
    (hψ.1.continuousOn.mono (subset_univ D)).sub hφ.1.continuousOn
  have hint : IntegrableOn (fun w => ‖ψ w - φ w‖ ^ 2) Ω1 := by
    have hcc : IsCompact (closure Ω1) := hK1.closure_of_subset hΩ1sub
    refine (ContinuousOn.integrableOn_compact hcc ?_).mono_set subset_closure
    exact ((hcontD.mono hcl).norm).pow 2
  have hsmall : closedBall z (δ0 / 2) ⊆ Ω1 :=
    (closedBall_subset_ball (by linarith)).trans hballz
  have hI : ∫ w in closedBall z (δ0 / 2), ‖ψ w - φ w‖ ^ 2 ≤ η := by
    refine (setIntegral_mono_set hint (Eventually.of_forall fun _ => by positivity)
      (Eventually.of_forall hsmall)).trans hψη.le
  have hsq : Real.sqrt (∫ w in closedBall z (δ0 / 2), ‖ψ w - φ w‖ ^ 2) ≤ ε / (|C| + 1) := by
    rw [show ε / (|C| + 1) = Real.sqrt η by
      rw [hη, Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt hI
  have hCε : |C| * (ε / (|C| + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [abs_nonneg C]
  have hfin : C * Real.sqrt (∫ w in closedBall z (δ0 / 2), ‖ψ w - φ w‖ ^ 2) < ε :=
    calc C * _ ≤ |C| * Real.sqrt (∫ w in closedBall z (δ0 / 2), ‖ψ w - φ w‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)
      _ ≤ |C| * (ε / (|C| + 1)) := mul_le_mul_of_nonneg_left hsq (abs_nonneg C)
      _ < ε := hCε
  have hzD : z ∈ D := hΩ1D (hδ0K (self_subset_cthickening _ hz))
  have hdψ : DifferentiableAt ℝ ψ z :=
    (hψ.1.differentiableOn (by norm_num)).differentiableAt (isOpen_univ.mem_nhds (mem_univ z))
  have hdφ : DifferentiableAt ℝ φ z :=
    (hφ.1.differentiableOn (by norm_num)).differentiableAt (hDo.mem_nhds hzD)
  have hfd : fderiv ℝ (fun w => ψ w - φ w) z = fderiv ℝ ψ z - fderiv ℝ φ z :=
    fderiv_sub hdψ hdφ
  exact ⟨h1.trans_lt hfin, hfd ▸ h2.trans_lt hfin⟩

end

section

/-! ## Integrability of radial singularities in the plane -/

open MeasureTheory Set Real Metric Filter Topology

/-- A radial function `g(‖y‖)` with `|t g(t)|` bounded on `(0, R)` is integrable on `B(0, R)`. -/
lemma integrableOn_ball_radial {g : ℝ → ℝ} (hg : Measurable g) {R C : ℝ}
    (hC : ∀ t ∈ Ioo 0 R, |t * g t| ≤ C) :
    IntegrableOn (fun y : ℂ => g ‖y‖) (ball 0 R) := by
  rw [← integrable_indicator_iff measurableSet_ball]
  have heq : (ball (0 : ℂ) R).indicator (fun y : ℂ => g ‖y‖) =
      fun y : ℂ => (Iio R).indicator g ‖y‖ := by
    funext y
    by_cases hy : ‖y‖ < R
    · simp [indicator_of_mem, hy, mem_ball_zero_iff.2 hy]
    · rw [indicator_of_notMem (by simpa using hy), indicator_of_notMem (by simpa using hy)]
  rw [heq, integrable_fun_norm_addHaar (volume : Measure ℂ)]
  simp only [Complex.finrank_real_complex, Nat.add_one_sub_one, pow_one, smul_eq_mul]
  have hR : IntegrableOn (fun _ : ℝ => |C|) (Ioc 0 R) := by
    by_cases h : 0 ≤ R
    · exact integrableOn_const (by simp [Real.volume_Ioc]) |>.mono_set subset_rfl
    · rw [Ioc_eq_empty (by linarith)]; exact integrableOn_empty
  have hsplit : Ioi (0 : ℝ) = Ioc 0 R ∪ Ioi (max 0 R) := by
    ext t; simp only [mem_Ioi, mem_union, mem_Ioc, max_lt_iff]
    constructor
    · intro ht; by_cases h : t ≤ R
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr ⟨ht, by linarith⟩
    · rintro (h | h) <;> linarith [h.1]
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · refine Integrable.mono' hR ?_ ?_
    · exact (measurable_id.mul (hg.indicator measurableSet_Iio)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
      by_cases htR : t < R
      · rw [indicator_of_mem (by simpa using htR), Real.norm_eq_abs]
        exact (hC t ⟨ht.1, htR⟩).trans (le_abs_self C)
      · rw [indicator_of_notMem (by simpa using htR)]
        simp
  · refine integrableOn_zero.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have : ¬ t < R := by simp only [mem_Ioi, max_lt_iff] at ht; linarith [ht.2]
    simp [indicator_of_notMem (show t ∉ Iio R by simpa using this)]

lemma integrableOn_ball_inv_norm (R : ℝ) :
    IntegrableOn (fun y : ℂ => ‖y‖⁻¹) (ball 0 R) :=
  integrableOn_ball_radial (g := fun t => t⁻¹) measurable_inv (C := 1) fun t ht => by
    rw [mul_inv_cancel₀ ht.1.ne']; simp

lemma t_mul_log_le {t R : ℝ} (ht : t ∈ Ioo 0 R) : |t * Real.log t| ≤ 1 + R * R := by
  rcases le_or_gt t 1 with h1 | h1
  · have := Real.abs_log_mul_self_lt t ht.1 h1
    rw [mul_comm]; nlinarith [mul_self_nonneg R]
  · have hl : 0 ≤ Real.log t := Real.log_nonneg h1.le
    have hl' : Real.log t ≤ t := (Real.log_le_sub_one_of_pos ht.1).trans (by linarith)
    rw [abs_of_nonneg (by positivity)]
    nlinarith [ht.2, mul_le_mul_of_nonneg_left hl' ht.1.le]

lemma integrableOn_ball_log_norm (R : ℝ) :
    IntegrableOn (fun y : ℂ => Real.log ‖y‖) (ball 0 R) :=
  integrableOn_ball_radial Real.measurable_log fun _ ht => t_mul_log_le ht

lemma t_mul_log_sq_le {t R : ℝ} (ht : t ∈ Ioo 0 R) : |t * Real.log t ^ 2| ≤ 4 + R ^ 3 := by
  rw [abs_of_nonneg (by have := ht.1; positivity)]
  rcases le_or_gt t 1 with h1 | h1
  · have h := Real.abs_log_mul_self_rpow_lt t (1 / 2) ht.1 h1 (by norm_num)
    have hs : (t ^ (1 / 2 : ℝ)) ^ 2 = t := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.1.le]; norm_num
    have h' : (Real.log t * t ^ (1 / 2 : ℝ)) ^ 2 < 4 := by
      have := abs_lt.1 h; nlinarith
    have hR : 0 ≤ R ^ 3 := pow_nonneg (by linarith [ht.1, ht.2]) 3
    calc t * Real.log t ^ 2 = (Real.log t * t ^ (1 / 2 : ℝ)) ^ 2 := by rw [mul_pow, hs]; ring
      _ ≤ 4 + R ^ 3 := by linarith
  · have hl : 0 ≤ Real.log t := Real.log_nonneg h1.le
    have hl' : Real.log t ≤ t := (Real.log_le_sub_one_of_pos ht.1).trans (by linarith)
    have h2 : Real.log t ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hl hl' 2
    have h3 : t ^ 3 ≤ R ^ 3 := pow_le_pow_left₀ ht.1.le ht.2.le 3
    nlinarith [mul_le_mul_of_nonneg_left h2 ht.1.le]

lemma integrableOn_ball_log_norm_sq (R : ℝ) :
    IntegrableOn (fun y : ℂ => Real.log ‖y‖ ^ 2) (ball 0 R) :=
  integrableOn_ball_radial (g := fun t => Real.log t ^ 2) (Real.measurable_log.pow_const 2)
    fun _ ht => t_mul_log_sq_le ht

/-- Translating a radial integrability statement. -/
lemma integrableOn_ball_sub {g : ℂ → ℝ} {R : ℝ} (hg : IntegrableOn g (ball 0 R)) (w : ℂ) :
    IntegrableOn (fun η => g (w - η)) (ball w R) := by
  have hmp := Measure.measurePreserving_sub_left (volume : Measure ℂ) w
  have h := (hmp.integrableOn_comp_preimage (Homeomorph.subLeft w).measurableEmbedding).2 hg
  have hpre : (fun η => w - η) ⁻¹' ball 0 R = ball w R := by
    ext η; simp [dist_eq_norm, norm_sub_rev]
  rw [hpre] at h
  exact h

end

section

/-! ## The logarithmic potential of a bounded density -/

open MeasureTheory Set Real Metric Filter Topology
open scoped InnerProductSpace

/-- Bounded measurable functions vanishing outside `closedBall 0 ρ`. -/
structure BddSupp (f : ℂ → ℝ) (M ρ : ℝ) : Prop where
  meas : AEStronglyMeasurable f
  bdd : ∀ x, |f x| ≤ M
  supp : ∀ x, ρ < ‖x‖ → f x = 0

namespace BddSupp

variable {f : ℂ → ℝ} {M ρ : ℝ}

lemma eq_indicator (hf : BddSupp f M ρ) {s : Set ℂ} (hs : closedBall 0 ρ ⊆ s) (g : ℂ → ℝ) :
    (fun η => g η * f η) = fun η => s.indicator g η * f η := by
  funext η
  by_cases h : η ∈ s
  · simp [indicator_of_mem h]
  · have : ρ < ‖η‖ := by
      by_contra hc; exact h (hs (mem_closedBall_zero_iff.2 (not_lt.1 hc)))
    simp [hf.supp η this]

lemma integrable (hf : BddSupp f M ρ) : Integrable f := by
  have h : IntegrableOn (fun _ : ℂ => (1 : ℝ)) (closedBall 0 ρ) :=
    integrableOn_const (measure_closedBall_lt_top.ne)
  have h2 := (h.integrable_indicator measurableSet_closedBall).mul_bdd hf.meas
    (c := M) (Eventually.of_forall fun x => by simpa using hf.bdd x)
  convert h2 using 1
  have := hf.eq_indicator (s := closedBall 0 ρ) subset_rfl (fun _ => 1)
  simp only [one_mul] at this
  funext η; rw [← congrFun this η]

lemma integrable_mul (hf : BddSupp f M ρ) {g : ℂ → ℝ} {s : Set ℂ} (hsm : MeasurableSet s)
    (hgi : IntegrableOn g s) (hs : closedBall 0 ρ ⊆ s) :
    Integrable (fun η => g η * f η) := by
  rw [hf.eq_indicator hs g]
  exact (hgi.integrable_indicator hsm).mul_bdd hf.meas
    (c := M) (Eventually.of_forall fun x => by simpa using hf.bdd x)

lemma integrable_smul (hf : BddSupp f M ρ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℂ → E} {s : Set ℂ} (hsm : MeasurableSet s) (hgi : IntegrableOn g s)
    (hs : closedBall 0 ρ ⊆ s) : Integrable (fun η => f η • g η) := by
  have heq : (fun η => f η • g η) = fun η => f η • s.indicator g η := by
    funext η
    by_cases h : η ∈ s
    · simp [indicator_of_mem h]
    · have : ρ < ‖η‖ := by
        by_contra hc; exact h (hs (mem_closedBall_zero_iff.2 (not_lt.1 hc)))
      simp [hf.supp η this]
  rw [heq]
  exact (hgi.integrable_indicator hsm).bdd_smul M hf.meas
    (Eventually.of_forall fun x => by simpa using hf.bdd x)

lemma nonneg_M (hf : BddSupp f M ρ) : 0 ≤ M := (abs_nonneg _).trans (hf.bdd 0)

end BddSupp

/-! ### Kernels -/

/-- The logarithmic potential `∫ log ‖w - η‖ f(η) dη`. -/
def logPot (f : ℂ → ℝ) (w : ℂ) : ℝ := ∫ η, Real.log ‖w - η‖ * f η

/-- The gradient of `log ‖y‖`, i.e. `v ↦ ⟪y, v⟫ / ‖y‖²`. -/
def gradKer (y : ℂ) : ℂ →L[ℝ] ℝ := (‖y‖ ^ 2)⁻¹ • innerSL ℝ y

/-- The candidate derivative `∫ f(η) ∇ log ‖w - η‖ dη` of the logarithmic potential. -/
def gradPot (f : ℂ → ℝ) (w : ℂ) : ℂ →L[ℝ] ℝ := ∫ η, f η • gradKer (w - η)

/-- Regularized kernel `½ log (‖y‖² + ε²)`. -/
def logReg (ε : ℝ) (y : ℂ) : ℝ := Real.log (‖y‖ ^ 2 + ε ^ 2) / 2

/-- Gradient of the regularized kernel. -/
def gradReg (ε : ℝ) (y : ℂ) : ℂ →L[ℝ] ℝ := (‖y‖ ^ 2 + ε ^ 2)⁻¹ • innerSL ℝ y

lemma continuous_gradReg {ε : ℝ} (hε : ε ≠ 0) : Continuous (gradReg ε) := by
  unfold gradReg
  refine Continuous.smul ?_ (innerSL ℝ (E := ℂ)).continuous
  refine Continuous.inv₀ (by fun_prop) fun y => ?_
  positivity

lemma measurable_gradKer : Measurable gradKer := by
  unfold gradKer
  exact ((continuous_norm.pow 2).measurable.inv).smul (innerSL ℝ (E := ℂ)).continuous.measurable

lemma hasFDerivAt_logReg {ε : ℝ} (hε : ε ≠ 0) (y : ℂ) :
    HasFDerivAt (logReg ε) (gradReg ε y) y := by
  have hpos : 0 < ‖y‖ ^ 2 + ε ^ 2 := by positivity
  have h1 : HasFDerivAt (fun y : ℂ => ‖y‖ ^ 2 + ε ^ 2) (2 • innerSL ℝ y) y :=
    (hasStrictFDerivAt_norm_sq y).hasFDerivAt.add_const _
  have h2 := (Real.hasDerivAt_log hpos.ne').comp_hasFDerivAt y h1
  have h3 := h2.mul_const (1 / 2 : ℝ)
  have e : logReg ε = fun y => (Real.log ∘ fun y : ℂ => ‖y‖ ^ 2 + ε ^ 2) y * (1 / 2) := by
    funext y; simp only [logReg, Function.comp]; ring
  rw [e]
  convert h3 using 1
  ext v
  simp only [gradReg, ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  ring

lemma norm_gradReg_le {ε : ℝ} (hε : 0 < ε) (y : ℂ) : ‖gradReg ε y‖ ≤ 1 / ε := by
  unfold gradReg
  rw [norm_smul, innerSL_apply_norm, norm_inv, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < ‖y‖ ^ 2 + ε ^ 2)]
  rw [inv_mul_le_iff₀ (by positivity), mul_one_div, le_div_iff₀ hε]
  nlinarith [sq_nonneg (‖y‖ - ε), norm_nonneg y]

lemma norm_gradKer (y : ℂ) : ‖gradKer y‖ = ‖y‖⁻¹ := by
  unfold gradKer
  rw [norm_smul, innerSL_apply_norm, norm_inv, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  by_cases h : y = 0
  · simp [h]
  · field_simp

lemma norm_gradReg_sub_gradKer_le {ε : ℝ} (y : ℂ) : ‖gradReg ε y - gradKer y‖ ≤ ‖y‖⁻¹ := by
  by_cases h : y = 0
  · simp [h, gradReg, gradKer]
  have hy : 0 < ‖y‖ := norm_pos_iff.2 h
  unfold gradReg gradKer
  rw [← sub_smul, norm_smul, innerSL_apply_norm, Real.norm_eq_abs]
  have h1 : 0 < (‖y‖ ^ 2)⁻¹ - (‖y‖ ^ 2 + ε ^ 2)⁻¹ + (‖y‖ ^ 2 + ε ^ 2)⁻¹ := by
    simp; positivity
  have h2 : (‖y‖ ^ 2 + ε ^ 2)⁻¹ ≤ (‖y‖ ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (by nlinarith [sq_nonneg ε])
  rw [abs_of_nonpos (by linarith), neg_sub]
  calc ((‖y‖ ^ 2)⁻¹ - (‖y‖ ^ 2 + ε ^ 2)⁻¹) * ‖y‖ ≤ (‖y‖ ^ 2)⁻¹ * ‖y‖ := by
        have : 0 ≤ (‖y‖ ^ 2 + ε ^ 2)⁻¹ := by positivity
        nlinarith
    _ = ‖y‖⁻¹ := by field_simp

lemma tendsto_gradReg (y : ℂ) :
    Tendsto (fun n : ℕ => gradReg (1 / (n + 1 : ℝ)) y) atTop (𝓝 (gradKer y)) := by
  by_cases h : y = 0
  · simp [h, gradReg, gradKer]
  unfold gradReg gradKer
  refine Tendsto.smul_const ?_ _
  refine Tendsto.inv₀ ?_ (by positivity)
  have : Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ))) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have := (this.pow 2).const_add (‖y‖ ^ 2)
  simpa using this

lemma abs_logReg_sub_log_le {ε : ℝ} (hε : 0 < ε) {y : ℂ} (hy : y ≠ 0) :
    |logReg ε y - Real.log ‖y‖| ≤ ε / ‖y‖ := by
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  unfold logReg
  have hlog : Real.log ‖y‖ = Real.log (‖y‖ ^ 2) / 2 := by
    rw [Real.log_pow]; push_cast; ring
  rw [hlog, ← sub_div, ← Real.log_div (by positivity) (by positivity)]
  have hq : (‖y‖ ^ 2 + ε ^ 2) / ‖y‖ ^ 2 = 1 + (ε / ‖y‖) ^ 2 := by field_simp
  rw [hq, abs_of_nonneg (by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + (ε / ‖y‖) ^ 2 by nlinarith [sq_nonneg (ε/‖y‖)])
    positivity)]
  have ht : 0 ≤ ε / ‖y‖ := by positivity
  have key : Real.log (1 + (ε / ‖y‖) ^ 2) ≤ 2 * (ε / ‖y‖) := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + (ε / ‖y‖) ^ 2 by positivity)
    have h2 : (ε / ‖y‖) ^ 2 ≤ 2 * (ε / ‖y‖) ∨ 2 * (ε / ‖y‖) < (ε / ‖y‖) ^ 2 := le_or_gt _ _
    rcases h2 with h2 | h2
    · linarith
    · -- for large `t`, use `log (1 + t²) ≤ 2 log (1 + t) ≤ 2 t`
      have h3 : 1 + (ε / ‖y‖) ^ 2 ≤ (1 + ε / ‖y‖) ^ 2 := by nlinarith
      have h4 := Real.log_le_log (by positivity) h3
      rw [Real.log_pow] at h4
      have h5 := Real.log_le_sub_one_of_pos (show 0 < 1 + ε / ‖y‖ by positivity)
      push_cast at h4
      linarith
  linarith

/-! ### Convergence of the regularized potentials -/

/-- Regularized potential. -/
def logPotReg (ε : ℝ) (f : ℂ → ℝ) (w : ℂ) : ℝ := ∫ η, logReg ε (w - η) * f η

/-- Derivative of the regularized potential. -/
def gradPotReg (ε : ℝ) (f : ℂ → ℝ) (w : ℂ) : ℂ →L[ℝ] ℝ := ∫ η, f η • gradReg ε (w - η)

lemma continuous_logReg {ε : ℝ} (hε : ε ≠ 0) : Continuous (logReg ε) :=
  continuous_iff_continuousAt.2 fun y => (hasFDerivAt_logReg hε y).continuousAt

lemma ae_ne_point (w : ℂ) : ∀ᵐ η ∂(volume : Measure ℂ), η ≠ w := by
  have := (measure_eq_zero_iff_ae_notMem (μ := (volume : Measure ℂ)) (s := {w})).1
    (measure_singleton w)
  simpa using this

lemma closedBall_subset_ball_sub {ρ R : ℝ} {w : ℂ} (hw : ‖w‖ ≤ R) :
    closedBall (0 : ℂ) ρ ⊆ ball w (R + ρ + 1) := by
  intro η hη
  rw [mem_closedBall_zero_iff] at hη
  rw [mem_ball, dist_eq_norm]
  calc ‖η - w‖ ≤ ‖η‖ + ‖w‖ := norm_sub_le _ _
    _ < R + ρ + 1 := by linarith

namespace BddSupp

variable {f : ℂ → ℝ} {M ρ : ℝ}

lemma abs (hf : BddSupp f M ρ) : BddSupp (fun x => |f x|) M ρ :=
  ⟨hf.meas.norm, fun x => by simpa using hf.bdd x, fun x hx => by simp [hf.supp x hx]⟩

lemma hasFDerivAt_logPotReg (hf : BddSupp f M ρ) {ε : ℝ} (hε : 0 < ε) (w : ℂ) :
    HasFDerivAt (logPotReg ε f) (gradPotReg ε f w) w := by
  have hc := continuous_logReg hε.ne'
  have hcg := continuous_gradReg hε.ne'
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun η => |f η| * (1 / ε))
    (F := fun x η => logReg ε (x - η) * f η) (F' := fun x η => f η • gradReg ε (x - η))
    (s := univ) univ_mem ?_ ?_ ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun x =>
      (hc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul hf.meas
  · exact hf.integrable_mul measurableSet_closedBall
      ((hc.comp (continuous_const.sub continuous_id)).continuousOn.integrableOn_compact
        (isCompact_closedBall 0 ρ)) subset_rfl
  · exact hf.meas.smul (hcg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine Eventually.of_forall fun η x _ => ?_
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_gradReg_le hε _) (abs_nonneg _)
  · exact hf.integrable.abs.mul_const _
  · refine Eventually.of_forall fun η x _ => ?_
    have h := ((hasFDerivAt_logReg hε.ne' (x - η)).comp x
      ((hasFDerivAt_id x).sub_const η)).mul_const (f η)
    convert h using 1

lemma tendsto_logPotReg (hf : BddSupp f M ρ) (w : ℂ) :
    Tendsto (fun n : ℕ => logPotReg (1 / (n + 1 : ℝ)) f w) atTop (𝓝 (logPot f w)) := by
  set R := ‖w‖ + ρ + 1
  have hsub : closedBall (0 : ℂ) ρ ⊆ ball w R := closedBall_subset_ball_sub le_rfl
  have hg : IntegrableOn (fun η => |Real.log ‖w - η‖| + ‖w - η‖⁻¹) (ball w R) :=
    (integrableOn_ball_sub (integrableOn_ball_log_norm R).abs w).add
      (integrableOn_ball_sub (integrableOn_ball_inv_norm R) w)
  refine tendsto_integral_of_dominated_convergence
    (fun η => (|Real.log ‖w - η‖| + ‖w - η‖⁻¹) * |f η|) (fun n => ?_)
    (hf.abs.integrable_mul measurableSet_ball hg hsub) (fun n => ?_) ?_
  · exact ((continuous_logReg (by positivity)).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable.mul hf.meas
  · filter_upwards [ae_ne_point w] with η hη
    have hy : w - η ≠ 0 := sub_ne_zero.2 hη.symm
    have hε : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    have hε1 : 1 / (n + 1 : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    have h1 := abs_logReg_sub_log_le hε hy
    have hn : 0 < ‖w - η‖ := norm_pos_iff.2 hy
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    have h2 : 1 / (n + 1 : ℝ) / ‖w - η‖ ≤ ‖w - η‖⁻¹ := by
      rw [div_eq_mul_inv]; exact mul_le_of_le_one_left (by positivity) hε1
    calc |logReg (1 / (n + 1 : ℝ)) (w - η)|
        ≤ |Real.log ‖w - η‖| + |logReg (1 / (n + 1 : ℝ)) (w - η) - Real.log ‖w - η‖| := by
          have := abs_add_le (Real.log ‖w - η‖) (logReg (1 / (n + 1 : ℝ)) (w - η) -
            Real.log ‖w - η‖)
          simpa using this
      _ ≤ _ := by linarith
  · filter_upwards [ae_ne_point w] with η hη
    have hy : w - η ≠ 0 := sub_ne_zero.2 hη.symm
    refine Tendsto.mul_const _ ?_
    have hpos : 0 < ‖w - η‖ ^ 2 := by positivity
    have h0 : Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ))) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : Tendsto (fun n : ℕ => ‖w - η‖ ^ 2 + (1 / (n + 1 : ℝ)) ^ 2) atTop
        (𝓝 (‖w - η‖ ^ 2)) := by simpa using (h0.pow 2).const_add (‖w - η‖ ^ 2)
    have h2 := ((Real.continuousAt_log hpos.ne').tendsto.comp h1).div_const 2
    have hlog : Real.log ‖w - η‖ = Real.log (‖w - η‖ ^ 2) / 2 := by
      rw [Real.log_pow]; push_cast; ring
    rw [hlog]
    exact h2

lemma integrable_gradKer (hf : BddSupp f M ρ) (w : ℂ) :
    Integrable (fun η => f η • gradKer (w - η)) := by
  set R := ‖w‖ + ρ + 1
  have hsub : closedBall (0 : ℂ) ρ ⊆ ball w R := closedBall_subset_ball_sub le_rfl
  refine hf.integrable_smul measurableSet_ball ?_ hsub
  refine Integrable.mono' (integrableOn_ball_sub (integrableOn_ball_inv_norm R) w) ?_ ?_
  · exact (measurable_gradKer.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  · exact Eventually.of_forall fun η => (norm_gradKer _).le

lemma integrable_gradReg (hf : BddSupp f M ρ) {ε : ℝ} (hε : 0 < ε) (w : ℂ) :
    Integrable (fun η => f η • gradReg ε (w - η)) := by
  refine Integrable.mono' (hf.integrable.abs.mul_const (1 / ε)) ?_ ?_
  · exact hf.meas.smul ((continuous_gradReg hε.ne').comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine Eventually.of_forall fun η => ?_
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_gradReg_le hε _) (abs_nonneg _)

lemma norm_gradPotReg_sub_le (hf : BddSupp f M ρ) {ε : ℝ} (hε : 0 < ε) {R : ℝ} {w : ℂ}
    (hw : ‖w‖ ≤ R) :
    ‖gradPotReg ε f w - gradPot f w‖ ≤
      M * ∫ y in ball (0 : ℂ) (R + ρ + 1), ‖gradReg ε y - gradKer y‖ := by
  set R' := R + ρ + 1
  set D : ℂ → ℝ := fun y => ‖gradReg ε y - gradKer y‖
  have hDi : IntegrableOn D (ball 0 R') := by
    refine Integrable.mono' (integrableOn_ball_inv_norm R') ?_ ?_
    · exact (((continuous_gradReg hε.ne').measurable.sub measurable_gradKer).norm).aestronglyMeasurable
    · exact Eventually.of_forall fun y => by
        simpa [D] using norm_gradReg_sub_gradKer_le (ε := ε) y
  unfold gradPotReg gradPot
  rw [← integral_sub (hf.integrable_gradReg hε w) (hf.integrable_gradKer w)]
  have hgi : Integrable (fun η => M * (ball 0 R').indicator D (w - η)) := by
    refine Integrable.const_mul ?_ M
    have := (hDi.integrable_indicator measurableSet_ball).comp_sub_left w
    exact this
  calc ‖∫ η, (f η • gradReg ε (w - η) - f η • gradKer (w - η))‖
      ≤ ∫ η, M * (ball 0 R').indicator D (w - η) := by
        refine norm_integral_le_of_norm_le hgi (Eventually.of_forall fun η => ?_)
        rw [← smul_sub, norm_smul, Real.norm_eq_abs]
        by_cases hη : ρ < ‖η‖
        · simp only [hf.supp η hη, abs_zero, zero_mul]
          exact mul_nonneg hf.nonneg_M (indicator_nonneg (fun _ _ => norm_nonneg _) _)
        · have hmem : w - η ∈ ball (0 : ℂ) R' := by
            rw [mem_ball_zero_iff]
            calc ‖w - η‖ ≤ ‖w‖ + ‖η‖ := norm_sub_le _ _
              _ < R' := by simp only [R']; linarith [not_lt.1 hη]
          rw [indicator_of_mem hmem]
          exact mul_le_mul_of_nonneg_right (hf.bdd η) (norm_nonneg _)
    _ = M * ∫ y in ball (0 : ℂ) R', D y := by
        rw [integral_const_mul, integral_sub_left_eq_self (fun y => (ball 0 R').indicator D y),
          integral_indicator measurableSet_ball]

lemma tendstoLocallyUniformly_gradPotReg (hf : BddSupp f M ρ) :
    TendstoLocallyUniformly (fun n : ℕ => gradPotReg (1 / (n + 1 : ℝ)) f) (gradPot f) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  set R' := R + ρ + 1
  -- the integrals of the kernel differences tend to zero
  have hI : Tendsto (fun n : ℕ => ∫ y in ball (0 : ℂ) R',
      ‖gradReg (1 / (n + 1 : ℝ)) y - gradKer y‖) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := volume.restrict (ball (0 : ℂ) R'))
      (F := fun (n : ℕ) y => ‖gradReg (1 / (n + 1 : ℝ)) y - gradKer y‖) (f := fun _ => (0 : ℝ))
      (fun y => ‖y‖⁻¹) (fun n => ?_) (integrableOn_ball_inv_norm R') (fun n => ?_) ?_
    · simpa using this
    · exact (((continuous_gradReg (by positivity)).measurable.sub
        measurable_gradKer).norm).aestronglyMeasurable
    · exact Eventually.of_forall fun y => by
        simpa using norm_gradReg_sub_gradKer_le (ε := 1 / (n + 1 : ℝ)) y
    · refine Eventually.of_forall fun y => ?_
      have := (tendsto_gradReg y).sub_const (gradKer y)
      simpa using this.norm
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  have hM := hf.nonneg_M
  have hev : ∀ᶠ n : ℕ in atTop, M * ∫ y in ball (0 : ℂ) R',
      ‖gradReg (1 / (n + 1 : ℝ)) y - gradKer y‖ < δ := by
    have := (hI.const_mul M)
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds hδ)
  filter_upwards [hev] with n hn w hw
  rw [dist_eq_norm, norm_sub_rev]
  have hwR : ‖w‖ ≤ R := mem_closedBall_zero_iff.1 (hR hw)
  exact (hf.norm_gradPotReg_sub_le (by positivity) hwR).trans_lt hn

lemma continuous_gradPotReg (hf : BddSupp f M ρ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (gradPotReg ε f) := by
  have hcg := continuous_gradReg hε.ne'
  refine continuous_of_dominated (bound := fun η => |f η| * (1 / ε)) (fun x => ?_) (fun x => ?_)
    (hf.integrable.abs.mul_const _) ?_
  · exact hf.meas.smul (hcg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine Eventually.of_forall fun η => ?_
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_gradReg_le hε _) (abs_nonneg _)
  · exact Eventually.of_forall fun η =>
      continuous_const.smul (hcg.comp (continuous_id.sub continuous_const))

/-- **Derivative of the logarithmic potential.** -/
theorem hasFDerivAt_logPot (hf : BddSupp f M ρ) (w : ℂ) :
    HasFDerivAt (logPot f) (gradPot f w) w :=
  hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ
    (hf.tendstoLocallyUniformly_gradPotReg.tendstoLocallyUniformlyOn)
    (fun n x _ => hf.hasFDerivAt_logPotReg (by positivity) x)
    (fun x _ => hf.tendsto_logPotReg x) (mem_univ w)

theorem continuous_gradPot (hf : BddSupp f M ρ) : Continuous (gradPot f) :=
  hf.tendstoLocallyUniformly_gradPotReg.continuous
    (Eventually.of_forall fun (n : ℕ) =>
      hf.continuous_gradPotReg (ε := 1 / (n + 1 : ℝ)) (by positivity)).frequently

theorem fderiv_logPot (hf : BddSupp f M ρ) : fderiv ℝ (logPot f) = gradPot f :=
  funext fun w => (hf.hasFDerivAt_logPot w).fderiv

/-- **The logarithmic potential of a bounded density is `C¹`.** -/
theorem contDiff_logPot (hf : BddSupp f M ρ) : ContDiff ℝ 1 (logPot f) := by
  rw [contDiff_one_iff_fderiv]
  exact ⟨fun w => (hf.hasFDerivAt_logPot w).differentiableAt,
    by rw [hf.fderiv_logPot]; exact hf.continuous_gradPot⟩

end BddSupp

end

section

/-! ## A polar-coordinates identity -/

open MeasureTheory Set Real Metric Filter Topology

lemma exists_radius_fderiv_eq_zero {h : ℂ → ℝ} (hc : HasCompactSupport h) (w : ℂ) :
    ∃ R > 0, ∀ y : ℂ, R < ‖y‖ → fderiv ℝ h (w - y) = 0 ∧ h (w - y) = 0 := by
  obtain ⟨R₀, hR₀⟩ := hc.isCompact.isBounded.subset_closedBall 0
  refine ⟨‖w‖ + |R₀| + 1, by positivity, fun y hy => ?_⟩
  have hnot : w - y ∉ tsupport h := by
    intro hm
    have := mem_closedBall_zero_iff.1 (hR₀ hm)
    have h2 : ‖y‖ ≤ ‖w‖ + ‖w - y‖ := by
      calc ‖y‖ = ‖w - (w - y)‖ := by simp
        _ ≤ ‖w‖ + ‖w - y‖ := norm_sub_le _ _
    linarith [le_abs_self R₀]
  exact ⟨image_eq_zero_of_notMem_tsupport (fun hm => hnot (tsupport_fderiv_subset ℝ hm)),
    image_eq_zero_of_notMem_tsupport hnot⟩

/-- The radial integral `∫₀^∞ Dh(w - r e)(e) dr = h(w)`. -/
lemma integral_Ioi_fderiv_radial {h : ℂ → ℝ} (hh : ContDiff ℝ 1 h) (hc : HasCompactSupport h)
    (w e : ℂ) (he : ‖e‖ = 1) :
    ∫ r in Ioi (0 : ℝ), fderiv ℝ h (w - r * e) e = h w := by
  obtain ⟨R, hR, hRz⟩ := exists_radius_fderiv_eq_zero hc w
  have hd : Differentiable ℝ h := hh.differentiable one_ne_zero
  have hcd : Continuous (fderiv ℝ h) := hh.continuous_fderiv one_ne_zero
  set g : ℝ → ℝ := fun r => -h (w - r * e)
  have hg' : ∀ r : ℝ, HasDerivAt g (fderiv ℝ h (w - r * e) e) r := by
    intro r
    have h1 : HasDerivAt (fun r : ℝ => w - (r : ℂ) * e) (-e) r := by
      have := ((Complex.ofRealCLM.hasDerivAt (x := r)).mul_const e).const_sub w
      simpa using this
    have h2 := (hd (w - r * e)).hasFDerivAt.comp_hasDerivAt r h1
    have h3 := h2.neg
    simpa [g] using h3
  have hcont : Continuous fun r : ℝ => fderiv ℝ h (w - r * e) e :=
    (hcd.comp (continuous_const.sub (Complex.continuous_ofReal.mul continuous_const))).clm_apply
      continuous_const
  have hzero : ∀ r : ℝ, R < r → fderiv ℝ h (w - r * e) e = 0 ∧ g r = 0 := by
    intro r hr
    have hn : R < ‖(r : ℂ) * e‖ := by
      rw [norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact hr.trans_le (le_abs_self r)
    obtain ⟨h1, h2⟩ := hRz _ hn
    exact ⟨by rw [h1]; simp, by simp [g, h2]⟩
  have hint : IntegrableOn (fun r : ℝ => fderiv ℝ h (w - r * e) e) (Ioi 0) := by
    refine IntegrableOn.of_forall_diff_eq_zero
      (hcont.continuousOn.integrableOn_compact (isCompact_Icc (a := 0) (b := R)))
      measurableSet_Ioi fun r hr => ?_
    have : R < r := by
      simp only [mem_diff, mem_Ioi, mem_Icc, not_and, not_le] at hr
      exact hr.2 hr.1.le
    exact (hzero r this).1
  have hlim : Tendsto g atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop R] with r hr
    exact (hzero r hr).2.symm
  have := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0) (f := g)
    (f' := fun r => fderiv ℝ h (w - r * e) e)
    (by
      have : Continuous g := by
        exact (hd.continuous.comp (continuous_const.sub
          (Complex.continuous_ofReal.mul continuous_const))).neg
      exact this.continuousWithinAt)
    (fun r _ => hg' r) hint hlim
  rw [this]
  simp [g]

/-- **Polar identity.** -/
theorem integral_fderiv_div_norm_sq {h : ℂ → ℝ} (hh : ContDiff ℝ 1 h) (hc : HasCompactSupport h)
    (w : ℂ) :
    ∫ η, fderiv ℝ h η (w - η) * (‖w - η‖ ^ 2)⁻¹ = 2 * π * h w := by
  set φ : ℂ → ℝ := fun y => fderiv ℝ h (w - y) y * (‖y‖ ^ 2)⁻¹
  have h1 : (∫ η, fderiv ℝ h η (w - η) * (‖w - η‖ ^ 2)⁻¹) = ∫ y, φ y := by
    have := integral_sub_left_eq_self φ (μ := (volume : Measure ℂ)) w
    rw [← this]
    simp [φ]
  rw [h1, ← Complex.integral_comp_polarCoord_symm φ]
  set e : ℝ → ℂ := fun θ => Real.cos θ + Real.sin θ * Complex.I
  have he : ∀ θ, ‖e θ‖ = 1 := fun θ => by
    have : e θ = Complex.exp (θ * Complex.I) := by
      rw [Complex.exp_mul_I]; simp [e, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [this, Complex.norm_exp_ofReal_mul_I]
  set ψ : ℝ × ℝ → ℝ := fun p => fderiv ℝ h (w - p.1 * e p.2) (e p.2)
  have h2 : (∫ p in polarCoord.target, p.1 • φ (Complex.polarCoord.symm p)) =
      ∫ p in polarCoord.target, ψ p := by
    refine setIntegral_congr_fun (polarCoord.open_target.measurableSet) fun p hp => ?_
    have hr : 0 < p.1 := hp.1
    simp only [Complex.polarCoord_symm_apply, φ, ψ, smul_eq_mul]
    have hn : ‖(p.1 : ℂ) * e p.2‖ = p.1 := by
      rw [norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    change p.1 * (fderiv ℝ h (w - p.1 * e p.2) (p.1 * e p.2) * (‖(p.1 : ℂ) * e p.2‖ ^ 2)⁻¹) = _
    rw [hn]
    have : (p.1 : ℂ) * e p.2 = p.1 • e p.2 := by simp
    rw [this, map_smul, smul_eq_mul]
    field_simp
  rw [h2]
  -- Fubini
  obtain ⟨R, hR, hRz⟩ := exists_radius_fderiv_eq_zero hc w
  have hcd : Continuous (fderiv ℝ h) := hh.continuous_fderiv one_ne_zero
  have hecont : Continuous e := by fun_prop
  have hψc : Continuous ψ :=
    (hcd.comp (continuous_const.sub ((Complex.continuous_ofReal.comp continuous_fst).mul
      (hecont.comp continuous_snd)))).clm_apply (hecont.comp continuous_snd)
  have hψint : IntegrableOn ψ (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) := by
    refine IntegrableOn.of_forall_diff_eq_zero
      (hψc.continuousOn.integrableOn_compact ((isCompact_Icc (a := (0 : ℝ)) (b := R)).prod
        (isCompact_Icc (a := -π) (b := π))))
      (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    have hRp : R < p.1 := by
      by_contra hc'
      exact h3 ⟨⟨(mem_Ioi.1 h1).le, not_lt.1 hc'⟩, (mem_Ioo.1 h2).1.le, (mem_Ioo.1 h2).2.le⟩
    have hn : R < ‖(p.1 : ℂ) * e p.2‖ := by
      rw [norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact hRp.trans_le (le_abs_self _)
    simp only [ψ, (hRz _ hn).1, ContinuousLinearMap.zero_apply]
  rw [polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict] at *
  rw [IntegrableOn, ← Measure.prod_restrict] at hψint
  rw [integral_prod_symm ψ hψint]
  have h3 : ∀ θ, (∫ r in Ioi (0 : ℝ), ψ (r, θ)) = h w := fun θ =>
    integral_Ioi_fderiv_radial hh hc w (e θ) (he θ)
  simp_rw [h3]
  rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos]), smul_eq_mul]
  ring

end

section

/-! ## Harmonic functions defined by logarithmic integrals -/

open MeasureTheory Set Real Metric Filter Topology

/-- `∫ G(η) log ‖1 + (w - c) a(η)‖ dη`. -/
def logHolo (G : ℂ → ℝ) (a : ℂ → ℂ) (c w : ℂ) : ℝ :=
  ∫ η, G η * Real.log ‖1 + (w - c) * a η‖

/-- The holomorphic function whose real part is `logHolo`. -/
def logHoloC (G : ℂ → ℝ) (a : ℂ → ℂ) (c w : ℂ) : ℂ :=
  ∫ η, (G η : ℂ) * Complex.log (1 + (w - c) * a η)

section

variable {G : ℂ → ℝ} {a : ℂ → ℂ} {A r : ℝ} {c : ℂ}

lemma norm_mul_le_of_mem_ball (hA : ∀ η, ‖a η‖ ≤ A) {x : ℂ} (hx : x ∈ ball c r)
    (η : ℂ) : ‖(x - c) * a η‖ ≤ r * A := by
  rw [norm_mul]
  have : ‖x - c‖ ≤ r := (mem_ball_iff_norm.1 hx).le
  exact mul_le_mul this (hA η) (norm_nonneg _) ((norm_nonneg _).trans this)

lemma one_add_mem_slitPlane {z : ℂ} (hz : ‖z‖ < 1) : 1 + z ∈ Complex.slitPlane := by
  left
  have := Complex.abs_re_le_norm z
  simp only [Complex.add_re, Complex.one_re]
  linarith [abs_le.1 this]

lemma one_sub_le_norm_one_add {z : ℂ} : 1 - ‖z‖ ≤ ‖1 + z‖ := by
  have := norm_sub_norm_le (1 : ℂ) (-z)
  simpa [sub_neg_eq_add] using this

lemma norm_log_le {z : ℂ} {m : ℝ} (hm : 0 < m) (hz1 : m ≤ ‖z‖) (hz2 : ‖z‖ ≤ 2) :
    ‖Complex.log z‖ ≤ |Real.log m| + 1 + π := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz1; linarith
  calc ‖Complex.log z‖ ≤ |(Complex.log z).re| + |(Complex.log z).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ (|Real.log m| + 1) + π := by
        refine add_le_add ?_ ?_
        · rw [Complex.log_re]
          rcases le_or_gt 1 ‖z‖ with h | h
          · rw [abs_of_nonneg (Real.log_nonneg h)]
            have := Real.log_le_sub_one_of_pos (show 0 < ‖z‖ by positivity)
            linarith [abs_nonneg (Real.log m)]
          · rw [abs_of_neg (Real.log_neg (by positivity) h)]
            have := Real.log_le_log hm hz1
            have : -Real.log m ≤ |Real.log m| := neg_le_abs _
            linarith
        · rw [Complex.log_im]; exact Complex.abs_arg_le_pi z
    _ = _ := by ring

lemma hasDerivAt_logHoloC (hG : Integrable G) (ha : Measurable a) (hA : ∀ η, ‖a η‖ ≤ A)
    (hrA : r * A < 1) {w₀ : ℂ} (hw₀ : w₀ ∈ ball c r) :
    HasDerivAt (logHoloC G a c)
      (∫ η, (G η : ℂ) * ((1 + (w₀ - c) * a η)⁻¹ * a η)) w₀ := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  set m := 1 - r * A with hm
  have hmpos : 0 < m := by linarith
  have hz : ∀ x ∈ ball c r, ∀ η, m ≤ ‖1 + (x - c) * a η‖ ∧ ‖1 + (x - c) * a η‖ ≤ 2 ∧
      1 + (x - c) * a η ∈ Complex.slitPlane := by
    intro x hx η
    have h1 := norm_mul_le_of_mem_ball hA hx η
    have h2 : r * A ≤ 1 := hrA.le
    refine ⟨?_, ?_, one_add_mem_slitPlane (by linarith)⟩
    · exact le_trans (by linarith) one_sub_le_norm_one_add
    · calc ‖1 + (x - c) * a η‖ ≤ ‖(1 : ℂ)‖ + ‖(x - c) * a η‖ := norm_add_le _ _
        _ ≤ 2 := by rw [norm_one]; linarith
  have hmeas : ∀ x : ℂ, AEStronglyMeasurable (fun η => (G η : ℂ) *
      Complex.log (1 + (x - c) * a η)) := fun x =>
    (Complex.measurable_ofReal.comp_aemeasurable hG.aemeasurable).aestronglyMeasurable.mul
      ((Complex.measurable_log.comp (measurable_const.add
        (measurable_const.mul ha))).aestronglyMeasurable)
  have hint : Integrable (fun η => (G η : ℂ) * Complex.log (1 + (w₀ - c) * a η)) := by
    refine Integrable.mono' (hG.norm.mul_const (|Real.log m| + 1 + π)) (hmeas w₀)
      (Eventually.of_forall fun η => ?_)
    obtain ⟨h1, h2, _⟩ := hz w₀ hw₀ η
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (norm_log_le hmpos h1 h2) (norm_nonneg _)
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun x η => (G η : ℂ) * Complex.log (1 + (x - c) * a η))
    (F' := fun x η => (G η : ℂ) * ((1 + (x - c) * a η)⁻¹ * a η))
    (bound := fun η => ‖G η‖ * (A / m)) (isOpen_ball.mem_nhds hw₀)
    (Eventually.of_forall hmeas) hint ?_ ?_ (hG.norm.mul_const _) ?_
  · exact this.2
  · exact (Complex.measurable_ofReal.comp_aemeasurable hG.aemeasurable).aestronglyMeasurable.mul
      (((measurable_const.add (measurable_const.mul ha)).inv.mul ha).aestronglyMeasurable)
  · refine Eventually.of_forall fun η x hx => ?_
    obtain ⟨h1, _, _⟩ := hz x hx η
    rw [norm_mul, Complex.norm_real, norm_mul, norm_inv]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [inv_mul_eq_div]
    exact div_le_div₀ hA0 (hA η) hmpos h1
  · refine Eventually.of_forall fun η x hx => ?_
    obtain ⟨_, _, h3⟩ := hz x hx η
    have hlin : HasDerivAt (fun x : ℂ => 1 + (x - c) * a η) (a η) x := by
      simpa using ((hasDerivAt_id x).sub_const c).mul_const (a η) |>.const_add 1
    exact ((Complex.hasDerivAt_log h3).comp x hlin).const_mul (G η : ℂ)

lemma logHolo_eq_re (hG : Integrable G) (ha : Measurable a) (hA : ∀ η, ‖a η‖ ≤ A)
    (hrA : r * A < 1) {w : ℂ} (hw : w ∈ ball c r) :
    logHolo G a c w = (logHoloC G a c w).re := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hm : 0 < 1 - r * A := by linarith
  have hint : Integrable (fun η => (G η : ℂ) * Complex.log (1 + (w - c) * a η)) := by
    refine Integrable.mono' (hG.norm.mul_const (|Real.log (1 - r * A)| + 1 + π)) ?_
      (Eventually.of_forall fun η => ?_)
    · exact (Complex.measurable_ofReal.comp_aemeasurable hG.aemeasurable).aestronglyMeasurable.mul
        ((Complex.measurable_log.comp (measurable_const.add
          (measurable_const.mul ha))).aestronglyMeasurable)
    · have h1 := norm_mul_le_of_mem_ball hA hw η
      rw [norm_mul, Complex.norm_real]
      refine mul_le_mul_of_nonneg_left (norm_log_le hm ?_ ?_) (norm_nonneg _)
      · exact le_trans (by linarith) one_sub_le_norm_one_add
      · calc ‖1 + (w - c) * a η‖ ≤ ‖(1 : ℂ)‖ + ‖(w - c) * a η‖ := norm_add_le _ _
          _ ≤ 2 := by rw [norm_one]; linarith
  unfold logHolo logHoloC
  have h := integral_re hint
  simp only [RCLike.re_to_complex] at h
  rw [← h]
  congr 1
  funext η
  simp [Complex.log_re]

theorem logHolo_analytic (hG : Integrable G) (ha : Measurable a) (hA : ∀ η, ‖a η‖ ≤ A)
    (hrA : r * A < 1) {w : ℂ} (hw : w ∈ ball c r) : AnalyticAt ℂ (logHoloC G a c) w := by
  have hd : DifferentiableOn ℂ (logHoloC G a c) (ball c r) := fun x hx =>
    (hasDerivAt_logHoloC hG ha hA hrA hx).differentiableAt.differentiableWithinAt
  exact hd.analyticAt (isOpen_ball.mem_nhds hw)

theorem logHolo_eventuallyEq (hG : Integrable G) (ha : Measurable a) (hA : ∀ η, ‖a η‖ ≤ A)
    (hrA : r * A < 1) {w : ℂ} (hw : w ∈ ball c r) :
    logHolo G a c =ᶠ[𝓝 w] fun x => (logHoloC G a c x).re :=
  Filter.eventually_of_mem (isOpen_ball.mem_nhds hw) fun _ hx => logHolo_eq_re hG ha hA hrA hx

/-- `logHolo` is smooth on `B(c, r)`. -/
theorem logHolo_contDiffAt (hG : Integrable G) (ha : Measurable a) (hA : ∀ η, ‖a η‖ ≤ A)
    (hrA : r * A < 1) {w : ℂ} (hw : w ∈ ball c r) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (logHolo G a c) w := by
  have h1 : ContDiffAt ℂ n (logHoloC G a c) w := (logHolo_analytic hG ha hA hrA hw).contDiffAt
  have h2 : ContDiffAt ℝ n (fun x => (logHoloC G a c x).re) w :=
    Complex.reCLM.contDiff.contDiffAt.comp w (h1.restrict_scalars ℝ)
  exact h2.congr_of_eventuallyEq (logHolo_eventuallyEq hG ha hA hrA hw)

/-- `logHolo` is harmonic on `B(c, r)`. -/
theorem logHolo_laplacian (hG : Integrable G) (ha : Measurable a) (hA : ∀ η, ‖a η‖ ≤ A)
    (hrA : r * A < 1) {w : ℂ} (hw : w ∈ ball c r) :
    Laplacian.laplacian (logHolo G a c) w = 0 := by
  have h := (logHolo_analytic hG ha hA hrA hw).harmonicAt_re
  rw [(InnerProductSpace.laplacian_congr_nhds (logHolo_eventuallyEq hG ha hA hrA hw)).self_of_nhds]
  exact h.2.self_of_nhds

end

end

section

/-! ## Second derivatives of the logarithmic potential -/

open MeasureTheory Set Real Metric Filter Topology
open scoped InnerProductSpace

lemma logPot_eq_conv (f : ℂ → ℝ) (w : ℂ) :
    logPot f w = ∫ y, Real.log ‖y‖ * f (w - y) := by
  unfold logPot
  have := integral_sub_left_eq_self (fun η => Real.log ‖w - η‖ * f η)
    (μ := (volume : Measure ℂ)) w
  rw [← this]
  simp

lemma clm_apply_eq_re_im (T : ℂ →L[ℝ] ℝ) (v : ℂ) : T v = v.re * T 1 + v.im * T Complex.I := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by simp
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

lemma clm_eq_re_im (T : ℂ →L[ℝ] ℝ) : T = T 1 • Complex.reCLM + T Complex.I • Complex.imCLM := by
  ext v
  simp [clm_apply_eq_re_im T v, mul_comm]

/-- Continuous compactly supported functions are bounded with bounded support. -/
lemma bddSupp_of_continuous {g : ℂ → ℝ} (hg : Continuous g) (hc : HasCompactSupport g) :
    ∃ M ρ, BddSupp g M ρ := by
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hc
  obtain ⟨ρ, hρ⟩ := hc.isCompact.isBounded.subset_closedBall 0
  refine ⟨M, ρ, hg.aestronglyMeasurable, fun x => by simpa using hM x, fun x hx => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun hm => ?_
  have := mem_closedBall_zero_iff.1 (hρ hm)
  linarith

/-- The directional derivative `η ↦ Dh(η) v`. -/
def dirDeriv (h : ℂ → ℝ) (v : ℂ) : ℂ → ℝ := fun η => fderiv ℝ h η v

section C1

variable {h : ℂ → ℝ}

lemma continuous_dirDeriv (hh : ContDiff ℝ 1 h) (v : ℂ) : Continuous (dirDeriv h v) :=
  (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const

lemma hasCompactSupport_dirDeriv (hc : HasCompactSupport h) (v : ℂ) :
    HasCompactSupport (dirDeriv h v) := hc.fderiv_apply (𝕜 := ℝ) v

/-- **Derivative of the logarithmic potential of a `C¹_c` function.** -/
theorem hasFDerivAt_logPot_of_C1 (hh : ContDiff ℝ 1 h) (hc : HasCompactSupport h) (w₀ : ℂ) :
    HasFDerivAt (logPot h) (logPot (dirDeriv h 1) w₀ • Complex.reCLM +
      logPot (dirDeriv h Complex.I) w₀ • Complex.imCLM) w₀ := by
  have hd : Differentiable ℝ h := hh.differentiable one_ne_zero
  have hcd : Continuous (fderiv ℝ h) := hh.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := hcd.bounded_above_of_compact_support (hc.fderiv (𝕜 := ℝ))
  obtain ⟨ρ, hρ⟩ := hc.isCompact.isBounded.subset_closedBall 0
  set R := ‖w₀‖ + 1 + |ρ| + 1
  have hzero : ∀ w ∈ ball w₀ 1, ∀ y : ℂ, R ≤ ‖y‖ → fderiv ℝ h (w - y) = 0 := by
    intro w hw y hy
    refine image_eq_zero_of_notMem_tsupport fun hm => ?_
    have h1 := mem_closedBall_zero_iff.1 (hρ (tsupport_fderiv_subset ℝ hm))
    have h2 : ‖w‖ < ‖w₀‖ + 1 := by
      have := mem_ball_iff_norm.1 hw
      calc ‖w‖ ≤ ‖w₀‖ + ‖w - w₀‖ := by
            calc ‖w‖ = ‖w₀ + (w - w₀)‖ := by ring_nf
              _ ≤ _ := norm_add_le _ _
        _ < _ := by linarith
    have h3 : ‖y‖ ≤ ‖w‖ + ‖w - y‖ := by
      calc ‖y‖ = ‖w - (w - y)‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    linarith [le_abs_self ρ]
  have hlogint : IntegrableOn (fun y : ℂ => Real.log ‖y‖) (ball 0 R) := integrableOn_ball_log_norm R
  have hbound_int : Integrable (fun y : ℂ => (ball 0 R).indicator (fun y => |Real.log ‖y‖| * C) y) :=
    (integrable_indicator_iff measurableSet_ball).2 (hlogint.abs.mul_const C)
  have hcont : ∀ w : ℂ, Continuous fun y : ℂ => h (w - y) := fun w =>
    hd.continuous.comp (continuous_const.sub continuous_id)
  have hmeas : ∀ w : ℂ, AEStronglyMeasurable (fun y : ℂ => Real.log ‖y‖ * h (w - y)) := fun w =>
    (Real.measurable_log.comp measurable_norm).aestronglyMeasurable.mul
      (hcont w).aestronglyMeasurable
  obtain ⟨Ch, hCh⟩ := hd.continuous.bounded_above_of_compact_support hc
  have hzero' : ∀ y : ℂ, R ≤ ‖y‖ → h (w₀ - y) = 0 := by
    intro y hy
    refine image_eq_zero_of_notMem_tsupport fun hm => ?_
    have h1 := mem_closedBall_zero_iff.1 (hρ hm)
    have h3 : ‖y‖ ≤ ‖w₀‖ + ‖w₀ - y‖ := by
      calc ‖y‖ = ‖w₀ - (w₀ - y)‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    linarith [le_abs_self ρ]
  have hint : Integrable (fun y : ℂ => Real.log ‖y‖ * h (w₀ - y)) := by
    refine Integrable.mono' ((integrable_indicator_iff measurableSet_ball).2
      (hlogint.abs.mul_const Ch))
      (hmeas w₀) (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ ball (0 : ℂ) R
    · rw [indicator_of_mem hy, norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hCh _) (abs_nonneg _)
    · rw [indicator_of_notMem hy, hzero' y (by simpa using hy)]
      simp
  have hderiv := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (F := fun w y => Real.log ‖y‖ * h (w - y))
    (F' := fun w y => Real.log ‖y‖ • fderiv ℝ h (w - y))
    (bound := fun y => (ball 0 R).indicator (fun y => |Real.log ‖y‖| * C) y)
    (ball_mem_nhds w₀ one_pos) (Eventually.of_forall hmeas) hint ?_ ?_ hbound_int ?_
  · have hL : (∫ y, Real.log ‖y‖ • fderiv ℝ h (w₀ - y)) =
        logPot (dirDeriv h 1) w₀ • Complex.reCLM +
          logPot (dirDeriv h Complex.I) w₀ • Complex.imCLM := by
      have hI : Integrable (fun y : ℂ => Real.log ‖y‖ • fderiv ℝ h (w₀ - y)) := by
        refine Integrable.mono' hbound_int ?_ (Eventually.of_forall fun y => ?_)
        · exact (Real.measurable_log.comp measurable_norm).aestronglyMeasurable.smul
            (hcd.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
        · by_cases hy : y ∈ ball (0 : ℂ) R
          · rw [indicator_of_mem hy, norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)
          · rw [indicator_of_notMem hy, hzero w₀ (mem_ball_self one_pos) y (by simpa using hy)]
            simp
      rw [clm_eq_re_im (∫ y, Real.log ‖y‖ • fderiv ℝ h (w₀ - y)),
        ContinuousLinearMap.integral_apply hI, ContinuousLinearMap.integral_apply hI,
        logPot_eq_conv, logPot_eq_conv]
      rfl
    rw [← hL]
    have e : logPot h = fun x => ∫ y, Real.log ‖y‖ * h (x - y) := funext (logPot_eq_conv h)
    rw [e]
    exact hderiv
  · exact (Real.measurable_log.comp measurable_norm).aestronglyMeasurable.smul
      (hcd.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine Eventually.of_forall fun y w hw => ?_
    beta_reduce
    by_cases hy : y ∈ ball (0 : ℂ) R
    · rw [indicator_of_mem hy, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)
    · rw [indicator_of_notMem hy, hzero w hw y (by simpa using hy)]
      simp
  · refine Eventually.of_forall fun y w _ => ?_
    have := ((hd (w - y)).hasFDerivAt.comp w ((hasFDerivAt_id w).sub_const y)).const_mul
      (Real.log ‖y‖)
    simpa using this

/-- The logarithmic potential of a smooth compactly supported function is smooth. -/
theorem contDiff_logPot_of_smooth (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hc : HasCompactSupport h) :
    ContDiff ℝ (⊤ : ℕ∞) (logPot h) := by
  have key : ∀ n : ℕ, ∀ g : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      ContDiff ℝ n (logPot g) := by
    intro n
    induction n with
    | zero =>
      intro g hg hgc
      obtain ⟨M, ρ, hb⟩ := bddSupp_of_continuous hg.continuous hgc
      exact contDiff_zero.2 hb.contDiff_logPot.continuous
    | succ n ih =>
      intro g hg hgc
      have hg1 : ContDiff ℝ 1 g := hg.of_le (by exact_mod_cast le_top)
      rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl,
        contDiff_succ_iff_hasFDerivAt]
      refine ⟨fun w => logPot (dirDeriv g 1) w • Complex.reCLM +
        logPot (dirDeriv g Complex.I) w • Complex.imCLM, ?_, fun w =>
        hasFDerivAt_logPot_of_C1 hg1 hgc w⟩
      have hdg : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (dirDeriv g v) := fun v =>
        (hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
      refine ContDiff.add ?_ ?_
      · exact (ih _ (hdg 1) (hasCompactSupport_dirDeriv hgc 1)).smul contDiff_const
      · exact (ih _ (hdg Complex.I) (hasCompactSupport_dirDeriv hgc Complex.I)).smul
          contDiff_const
  exact contDiff_infty.2 fun n => key n h hh hc

lemma laplacian_eq_fderiv_fderiv_real (g : ℂ → ℝ) (w : ℂ) :
    Laplacian.laplacian g w = fderiv ℝ (fderiv ℝ g) w 1 1 +
      fderiv ℝ (fderiv ℝ g) w Complex.I Complex.I := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

lemma gradKer_apply (y u : ℂ) : gradKer y u = (‖y‖ ^ 2)⁻¹ * (y.re * u.re + y.im * u.im) := by
  simp [gradKer, Complex.inner, mul_comm]

lemma BddSupp.gradPot_apply {f : ℂ → ℝ} {M ρ : ℝ} (hf : BddSupp f M ρ) (w u : ℂ) :
    gradPot f w u = ∫ η, f η * gradKer (w - η) u := by
  unfold gradPot
  rw [ContinuousLinearMap.integral_apply (hf.integrable_gradKer w)]
  rfl

/-- **Laplacian of the logarithmic potential of a `C¹_c` function.** -/
theorem laplacian_logPot_of_C1 (hh : ContDiff ℝ 1 h) (hc : HasCompactSupport h) :
    ContDiff ℝ 2 (logPot h) ∧ ∀ w, Laplacian.laplacian (logPot h) w = 2 * π * h w := by
  obtain ⟨M1, ρ1, hb1⟩ := bddSupp_of_continuous (continuous_dirDeriv hh 1)
    (hasCompactSupport_dirDeriv hc 1)
  obtain ⟨M2, ρ2, hb2⟩ := bddSupp_of_continuous (continuous_dirDeriv hh Complex.I)
    (hasCompactSupport_dirDeriv hc Complex.I)
  set a := logPot (dirDeriv h 1)
  set b := logPot (dirDeriv h Complex.I)
  set L : ℂ → ℂ →L[ℝ] ℝ := fun w => a w • Complex.reCLM + b w • Complex.imCLM
  have hL : ∀ w, HasFDerivAt (logPot h) (L w) w := hasFDerivAt_logPot_of_C1 hh hc
  have hfd : fderiv ℝ (logPot h) = L := funext fun w => (hL w).fderiv
  have hLd : ∀ w, HasFDerivAt L ((gradPot (dirDeriv h 1) w).smulRight Complex.reCLM +
      (gradPot (dirDeriv h Complex.I) w).smulRight Complex.imCLM) w := fun w =>
    ((hb1.hasFDerivAt_logPot w).smul_const Complex.reCLM).add
      ((hb2.hasFDerivAt_logPot w).smul_const Complex.imCLM)
  refine ⟨?_, fun w => ?_⟩
  · rw [show (2 : WithTop ℕ∞) = ((1 : ℕ) : WithTop ℕ∞) + 1 by norm_num,
      contDiff_succ_iff_hasFDerivAt]
    exact ⟨L, (hb1.contDiff_logPot.smul contDiff_const).add
      (hb2.contDiff_logPot.smul contDiff_const), hL⟩
  · rw [laplacian_eq_fderiv_fderiv_real, hfd, (hLd w).fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.smul_apply,
      Complex.reCLM_apply, Complex.imCLM_apply, Complex.one_re, Complex.one_im, Complex.I_re,
      Complex.I_im, smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
    rw [hb1.gradPot_apply, hb2.gradPot_apply, ← integral_add]
    · rw [← integral_fderiv_div_norm_sq hh hc w]
      congr 1
      funext η
      rw [gradKer_apply, gradKer_apply, clm_apply_eq_re_im (fderiv ℝ h η) (w - η)]
      simp only [dirDeriv, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
      ring
    · have := (hb1.integrable_gradKer w).apply_continuousLinearMap 1
      simpa using this
    · have := (hb2.integrable_gradKer w).apply_continuousLinearMap Complex.I
      simpa using this

end C1

lemma abs_log_le_log_two {x : ℝ} (h1 : 1 / 2 ≤ x) (h2 : x ≤ 2) : |Real.log x| ≤ Real.log 2 := by
  rcases le_or_gt 1 x with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    exact Real.log_le_log (by linarith) h2
  · rw [abs_of_neg (Real.log_neg (by linarith) h)]
    have := Real.log_le_log (by norm_num) h1
    rw [one_div, Real.log_inv] at this
    linarith

lemma laplacian_const_add {g : ℂ → ℝ} {w : ℂ} (c : ℝ) (hg : ContDiffAt ℝ 2 g w) :
    Laplacian.laplacian (fun x => c + g x) w = Laplacian.laplacian g w := by
  have h := (contDiffAt_const (c := c)).laplacian_add hg
  have e : (fun x => c + g x) = (fun _ => c) + g := rfl
  rw [e, h]
  simp [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    iteratedFDeriv_const_of_ne (show (2 : ℕ) ≠ 0 by norm_num)]

/-- **Local `C²` regularity and Poisson equation for the logarithmic potential.** -/
theorem BddSupp.logPot_laplacian {f : ℂ → ℝ} {M ρ : ℝ} (hf : BddSupp f M ρ) {W : Set ℂ}
    (hW : IsOpen W) (hfW : ContDiffOn ℝ 1 f W) {w₀ : ℂ} (hw₀ : w₀ ∈ W) :
    ContDiffAt ℝ 2 (logPot f) w₀ ∧ Laplacian.laplacian (logPot f) w₀ = 2 * π * f w₀ := by
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hW w₀ hw₀
  set δ := ε / 3 with hδdef
  have hδ : 0 < δ := by positivity
  let χ : ContDiffBump w₀ := ⟨δ, 2 * δ, hδ, by linarith⟩
  have hχW : tsupport χ ⊆ W := by
    rw [χ.tsupport_eq]
    exact (closedBall_subset_ball (by simp [χ]; linarith)).trans hεW
  set f₁ : ℂ → ℝ := fun x => χ x * f x
  set f₂ : ℂ → ℝ := fun x => (1 - χ x) * f x
  have hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1 := fun x => ⟨χ.nonneg, χ.le_one⟩
  -- `f₁` is `C¹` with compact support
  have hf₁ : ContDiff ℝ 1 f₁ := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ W
    · exact (χ.contDiff.contDiffAt).mul (hfW.contDiffAt (hW.mem_nhds hx))
    · have hx' : x ∉ tsupport χ := fun h => hx (hχW h)
      have hev : f₁ =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
        simp [f₁, hy]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hf₁c : HasCompactSupport f₁ := χ.hasCompactSupport.mul_right
  have hb₁ : BddSupp f₁ M ρ := ⟨(χ.continuous.aestronglyMeasurable).mul hf.meas, fun x => by
      simp only [f₁, abs_mul]
      have := hf.bdd x
      have h0 := hχ01 x
      rw [abs_of_nonneg h0.1]
      nlinarith [abs_nonneg (f x)], fun x hx => by simp [f₁, hf.supp x hx]⟩
  have hb₂ : BddSupp f₂ M ρ := ⟨(continuous_const.sub χ.continuous).aestronglyMeasurable.mul
      hf.meas, fun x => by
      simp only [f₂, abs_mul]
      have := hf.bdd x
      have h0 := hχ01 x
      rw [abs_of_nonneg (by linarith)]
      nlinarith [abs_nonneg (f x)], fun x hx => by simp [f₂, hf.supp x hx]⟩
  -- splitting the potential
  have hlogi : ∀ (w : ℂ) {g : ℂ → ℝ} {M' ρ' : ℝ}, BddSupp g M' ρ' →
      Integrable (fun η => Real.log ‖w - η‖ * g η) := by
    intro w g M' ρ' hg
    exact hg.integrable_mul measurableSet_ball
      (integrableOn_ball_sub (integrableOn_ball_log_norm _) w) (closedBall_subset_ball_sub le_rfl)
  have hsplit : logPot f = logPot f₁ + logPot f₂ := by
    funext w
    simp only [Pi.add_apply, logPot]
    rw [← integral_add (hlogi w hb₁) (hlogi w hb₂)]
    congr 1; funext η; simp only [f₁, f₂]; ring
  -- the potential of `f₁`
  obtain ⟨h1C, h1L⟩ := laplacian_logPot_of_C1 hf₁ hf₁c
  -- the potential of `f₂` is harmonic near `w₀`
  set a : ℂ → ℂ := fun η => if ‖η - w₀‖ < δ then 0 else (w₀ - η)⁻¹
  have ha : Measurable a :=
    Measurable.ite (measurableSet_lt (measurable_norm.comp (measurable_id.sub_const w₀))
      measurable_const) measurable_const (measurable_const.sub measurable_id).inv
  have hA : ∀ η, ‖a η‖ ≤ 1 / δ := by
    intro η
    simp only [a]
    split_ifs with h
    · simp; positivity
    · rw [norm_inv, one_div]
      refine inv_anti₀ hδ ?_
      rw [norm_sub_rev]; exact not_lt.1 h
  have hrA : δ / 2 * (1 / δ) < 1 := by field_simp; norm_num
  set c₀ := ∫ η, f₂ η * Real.log ‖w₀ - η‖
  have hf₂zero : ∀ η, ‖η - w₀‖ ≤ δ → f₂ η = 0 := by
    intro η hη
    have : χ η = 1 := χ.one_of_mem_closedBall (by rw [mem_closedBall, dist_eq_norm]; exact hη)
    simp [f₂, this]
  have hloc : ∀ w ∈ ball w₀ (δ / 2), logPot f₂ w = c₀ + logHolo f₂ a w₀ w := by
    intro w hw
    have hww : ‖w - w₀‖ < δ / 2 := mem_ball_iff_norm.1 hw
    have hpt : ∀ η, Real.log ‖w - η‖ * f₂ η =
        f₂ η * Real.log ‖w₀ - η‖ + f₂ η * Real.log ‖1 + (w - w₀) * a η‖ := by
      intro η
      by_cases hη : ‖η - w₀‖ ≤ δ
      · simp [hf₂zero η hη]
      · have hη' : δ < ‖η - w₀‖ := not_le.1 hη
        have haη : a η = (w₀ - η)⁻¹ := by simp [a, not_lt.2 hη'.le]
        have hne : w₀ - η ≠ 0 := by
          intro h; rw [norm_sub_rev, h, norm_zero] at hη'; linarith
        have hne' : w - η ≠ 0 := by
          intro h
          have : ‖η - w₀‖ = ‖w - w₀‖ := by
            calc ‖η - w₀‖ = ‖(w - w₀) - (w - η)‖ := by congr 1; ring
              _ = ‖w - w₀‖ := by rw [h, sub_zero]
          linarith
        have hq : 1 + (w - w₀) * a η = (w - η) / (w₀ - η) := by
          rw [haη]; field_simp; ring
        rw [hq, norm_div, Real.log_div (norm_ne_zero_iff.2 hne') (norm_ne_zero_iff.2 hne)]
        ring
    unfold logPot logHolo
    simp_rw [hpt]
    rw [integral_add]
    · have := hb₂.integrable_mul measurableSet_ball
        (integrableOn_ball_sub (integrableOn_ball_log_norm _) w₀)
        (closedBall_subset_ball_sub le_rfl)
      simpa [mul_comm] using this
    · refine Integrable.mono' (hb₂.integrable.abs.mul_const (Real.log 2)) ?_
        (Eventually.of_forall fun η => ?_)
      · exact hb₂.meas.mul ((Real.measurable_log.comp (measurable_norm.comp
          (measurable_const.add (measurable_const.mul ha)))).aestronglyMeasurable)
      · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have hz : ‖(w - w₀) * a η‖ ≤ 1 / 2 := by
          rw [norm_mul]
          calc ‖w - w₀‖ * ‖a η‖ ≤ (δ / 2) * (1 / δ) :=
                mul_le_mul hww.le (hA η) (norm_nonneg _) (by positivity)
            _ = 1 / 2 := by field_simp
        refine abs_log_le_log_two ?_ ?_
        · have := one_sub_le_norm_one_add (z := (w - w₀) * a η); linarith
        · calc ‖1 + (w - w₀) * a η‖ ≤ ‖(1 : ℂ)‖ + ‖(w - w₀) * a η‖ := norm_add_le _ _
            _ ≤ 2 := by rw [norm_one]; linarith
  have hw₀b : w₀ ∈ ball w₀ (δ / 2) := mem_ball_self (by positivity)
  have hev2 : logPot f₂ =ᶠ[𝓝 w₀] fun w => c₀ + logHolo f₂ a w₀ w :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hw₀b) hloc
  have h2C : ContDiffAt ℝ 2 (logPot f₂) w₀ :=
    (contDiffAt_const.add (logHolo_contDiffAt hb₂.integrable ha hA hrA hw₀b)).congr_of_eventuallyEq
      hev2
  have h2L : Laplacian.laplacian (logPot f₂) w₀ = 0 := by
    rw [(InnerProductSpace.laplacian_congr_nhds hev2).self_of_nhds,
      laplacian_const_add c₀ (logHolo_contDiffAt hb₂.integrable ha hA hrA hw₀b)]
    exact logHolo_laplacian hb₂.integrable ha hA hrA hw₀b
  -- combine
  refine ⟨hsplit ▸ (h1C.contDiffAt.add h2C), ?_⟩
  rw [hsplit, h1C.contDiffAt.laplacian_add h2C, h1L, h2L]
  have : χ w₀ = 1 := χ.one_of_mem_closedBall (mem_closedBall_self hδ.le)
  simp [f₁, this]

end

section

/-! ## The Green potential of the unit disk -/

open MeasureTheory Set Real Metric Filter Topology
open scoped ComplexConjugate

/-- `∫ log ‖1 - η̄ w‖ F(η) dη`. -/
def reflPot (F : ℂ → ℝ) (w : ℂ) : ℝ := ∫ η, Real.log ‖1 - conj η * w‖ * F η

/-- The Green potential of the unit disk. -/
def greenPot (F : ℂ → ℝ) (w : ℂ) : ℝ := (reflPot F w - logPot F w) / (2 * π)

/-- The Green function of the unit disk. -/
def diskGreen (w η : ℂ) : ℝ := (Real.log ‖1 - conj η * w‖ - Real.log ‖w - η‖) / (2 * π)

/-- Auxiliary coefficient: `-η̄` on `closedBall 0 ρ`, `0` outside. -/
def reflA (ρ : ℝ) (η : ℂ) : ℂ := if ‖η‖ ≤ ρ then -conj η else 0

lemma measurable_reflA (ρ : ℝ) : Measurable (reflA ρ) :=
  Measurable.ite (measurableSet_le measurable_norm measurable_const)
    (Complex.continuous_conj.measurable.neg) measurable_const

lemma norm_reflA_le {ρ : ℝ} (hρ : 0 ≤ ρ) (η : ℂ) : ‖reflA ρ η‖ ≤ ρ := by
  unfold reflA
  split_ifs with h
  · simpa using h
  · simpa using hρ

variable {F : ℂ → ℝ} {M ρ : ℝ}

lemma reflPot_eq_logHolo (hf : BddSupp F M ρ) : reflPot F = logHolo F (reflA ρ) 0 := by
  funext w
  unfold reflPot logHolo
  congr 1; funext η
  by_cases h : ‖η‖ ≤ ρ
  · simp only [reflA, h, if_true, sub_zero]
    rw [mul_comm]; congr 3; ring
  · simp [hf.supp η (not_le.1 h)]

lemma reflPot_smooth (hf : BddSupp F M ρ) (hρ0 : 0 ≤ ρ) {w : ℂ} (hw : ρ * ‖w‖ < 1)
    {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (reflPot F) w ∧ Laplacian.laplacian (reflPot F) w = 0 := by
  set r := ‖w‖ + (1 - ρ * ‖w‖) / (2 * (ρ + 1))
  have hwr : w ∈ ball (0 : ℂ) r := by
    rw [mem_ball_zero_iff]
    have : 0 < (1 - ρ * ‖w‖) / (2 * (ρ + 1)) := by
      apply div_pos <;> linarith
    linarith
  have hrA : r * ρ < 1 := by
    have h1 : (1 - ρ * ‖w‖) / (2 * (ρ + 1)) * ρ < 1 - ρ * ‖w‖ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    calc r * ρ = ρ * ‖w‖ + (1 - ρ * ‖w‖) / (2 * (ρ + 1)) * ρ := by ring
      _ < 1 := by linarith
  rw [reflPot_eq_logHolo hf]
  exact ⟨logHolo_contDiffAt hf.integrable (measurable_reflA ρ) (norm_reflA_le hρ0) hrA hwr,
    logHolo_laplacian hf.integrable (measurable_reflA ρ) (norm_reflA_le hρ0) hrA hwr⟩

lemma norm_one_sub_conj_mul {w : ℂ} (hw : w ≠ 0) (η : ℂ) :
    ‖1 - conj η * w‖ = ‖w‖ * ‖(conj w)⁻¹ - η‖ := by
  have hc : conj w ≠ 0 := by simpa using hw
  calc ‖1 - conj η * w‖ = ‖conj (1 - conj η * w)‖ := (Complex.norm_conj _).symm
    _ = ‖conj w * ((conj w)⁻¹ - η)‖ := by
        congr 1; simp only [map_sub, map_one, map_mul, Complex.conj_conj]
        field_simp
    _ = ‖w‖ * ‖(conj w)⁻¹ - η‖ := by rw [norm_mul, Complex.norm_conj]

lemma integrable_log_mul (hf : BddSupp F M ρ) (z : ℂ) :
    Integrable (fun η => Real.log ‖z - η‖ * F η) :=
  hf.integrable_mul measurableSet_ball (integrableOn_ball_sub (integrableOn_ball_log_norm _) z)
    (closedBall_subset_ball_sub le_rfl)

lemma reflPot_integrand_ae_eq {w : ℂ} (hw : w ≠ 0) :
    (fun η => Real.log ‖1 - conj η * w‖ * F η) =ᵐ[volume]
      fun η => Real.log ‖w‖ * F η + Real.log ‖(conj w)⁻¹ - η‖ * F η := by
  filter_upwards [ae_ne_point ((conj w)⁻¹)] with η hη
  rw [norm_one_sub_conj_mul hw, Real.log_mul (norm_ne_zero_iff.2 hw)
    (norm_ne_zero_iff.2 (sub_ne_zero.2 hη.symm))]
  ring

lemma integrable_reflPot_integrand (hf : BddSupp F M ρ) (w : ℂ) :
    Integrable (fun η => Real.log ‖1 - conj η * w‖ * F η) := by
  by_cases hw : w = 0
  · simp [hw]
  · exact Integrable.congr ((hf.integrable.const_mul _).add (integrable_log_mul hf _))
      (reflPot_integrand_ae_eq hw).symm

lemma reflPot_eq_of_ne (hf : BddSupp F M ρ) {w : ℂ} (hw : w ≠ 0) :
    reflPot F w = Real.log ‖w‖ * (∫ η, F η) + logPot F ((conj w)⁻¹) := by
  unfold reflPot logPot
  rw [integral_congr_ae (reflPot_integrand_ae_eq hw),
    integral_add (hf.integrable.const_mul _) (integrable_log_mul hf _), integral_const_mul]

lemma conj_inv_eq_self {w : ℂ} (hw : ‖w‖ = 1) : (conj w)⁻¹ = w := by
  have h : conj w * w = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]; simp
  have hc : conj w ≠ 0 := by intro h0; rw [h0, zero_mul] at h; exact zero_ne_one h
  field_simp
  rw [mul_comm]; exact h.symm ▸ (by ring)

/-- **The Green potential vanishes on the unit circle.** -/
theorem greenPot_eq_zero_of_norm_eq_one (hf : BddSupp F M ρ) {w : ℂ} (hw : ‖w‖ = 1) :
    greenPot F w = 0 := by
  have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hw; exact zero_ne_one hw
  unfold greenPot
  rw [reflPot_eq_of_ne hf hw0, conj_inv_eq_self hw, hw]
  simp

lemma contDiffAt_reflPot_of_ne (hf : BddSupp F M ρ) {w : ℂ} (hw : w ≠ 0) :
    ContDiffAt ℝ 1 (reflPot F) w := by
  have hev : reflPot F =ᶠ[𝓝 w] fun x => Real.log ‖x‖ * (∫ η, F η) + logPot F ((conj x)⁻¹) := by
    filter_upwards [isOpen_ne.mem_nhds hw] with x hx
    exact reflPot_eq_of_ne hf hx
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  refine ContDiffAt.add ?_ ?_
  · exact ((Real.contDiffAt_log.2 (norm_ne_zero_iff.2 hw)).comp w (contDiffAt_norm ℝ hw)).mul
      contDiffAt_const
  · have hc : conj w ≠ 0 := by simpa using hw
    have h1 : ContDiffAt ℝ 1 (fun x : ℂ => (conj x)⁻¹) w :=
      (contDiffAt_inv ℝ hc).comp w Complex.conjCLE.contDiff.contDiffAt
    exact hf.contDiff_logPot.contDiffAt.comp w h1

/-- **The Green potential is `C¹`.** -/
theorem greenPot_contDiff (hf : BddSupp F M ρ) (hρ0 : 0 ≤ ρ) :
    ContDiff ℝ 1 (greenPot F) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  have hr : ContDiffAt ℝ 1 (reflPot F) w := by
    by_cases hw : w = 0
    · exact (reflPot_smooth hf hρ0 (by simp [hw])).1
    · exact contDiffAt_reflPot_of_ne hf hw
  exact (hr.sub hf.contDiff_logPot.contDiffAt).div_const _

lemma laplacian_lincomb {f g : ℂ → ℝ} {w : ℂ} (a b : ℝ) (hf : ContDiffAt ℝ 2 f w)
    (hg : ContDiffAt ℝ 2 g w) :
    Laplacian.laplacian (fun x => a * f x + b * g x) w =
      a * Laplacian.laplacian f w + b * Laplacian.laplacian g w := by
  have e : (fun x => a * f x + b * g x) = a • f + b • g := by funext x; simp
  have h := (hf.const_smul a).laplacian_add (hg.const_smul b)
  rw [e]
  change Laplacian.laplacian ((fun y => a • f y) + fun y => b • g y) w = _
  rw [h]
  change Laplacian.laplacian (a • f) w + Laplacian.laplacian (b • g) w = _
  rw [InnerProductSpace.laplacian_smul _ hf, InnerProductSpace.laplacian_smul _ hg]
  simp

/-- **Poisson equation for the Green potential.** -/
theorem greenPot_laplacian (hf : BddSupp F M ρ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {W : Set ℂ}
    (hW : IsOpen W) (hWsub : W ⊆ ball 0 1) (hFW : ContDiffOn ℝ 1 F W) {w : ℂ} (hw : w ∈ W) :
    ContDiffAt ℝ 2 (greenPot F) w ∧ Laplacian.laplacian (greenPot F) w = -F w := by
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 (hWsub hw)
  have hρw : ρ * ‖w‖ < 1 := by nlinarith [norm_nonneg w]
  obtain ⟨hrC, hrL⟩ := reflPot_smooth hf hρ0 hρw (n := 2)
  obtain ⟨hlC, hlL⟩ := hf.logPot_laplacian hW hFW hw
  have e : greenPot F = fun x => (1 / (2 * π)) * reflPot F x + (-(1 / (2 * π))) * logPot F x := by
    funext x; simp only [greenPot]; ring
  refine ⟨?_, ?_⟩
  · rw [e]; exact (contDiffAt_const.mul hrC).add (contDiffAt_const.mul hlC)
  · rw [e, laplacian_lincomb _ _ hrC hlC, hrL, hlL]
    field_simp
    ring

/-- **Smoothness of the Green potential of a smooth density.** -/
theorem greenPot_smooth_of_smooth {X : ℂ → ℝ} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hXc : HasCompactSupport X) {ρ₀ : ℝ} (hρ₀ : 0 ≤ ρ₀) (hρ₀1 : ρ₀ < 1)
    (hsupp : ∀ x, ρ₀ < ‖x‖ → X x = 0) :
    ∃ R > 1, ContDiffOn ℝ (⊤ : ℕ∞) (greenPot X) (ball 0 R) := by
  obtain ⟨M, hM⟩ := hX.continuous.bounded_above_of_compact_support hXc
  have hb : BddSupp X M ρ₀ := ⟨hX.continuous.aestronglyMeasurable,
    fun x => by simpa using hM x, hsupp⟩
  refine ⟨2 / (1 + ρ₀), by rw [gt_iff_lt, lt_div_iff₀ (by linarith)]; linarith, fun w hw => ?_⟩
  have hw' : ‖w‖ < 2 / (1 + ρ₀) := mem_ball_zero_iff.1 hw
  have hρw : ρ₀ * ‖w‖ < 1 := by
    calc ρ₀ * ‖w‖ ≤ ρ₀ * (2 / (1 + ρ₀)) := mul_le_mul_of_nonneg_left hw'.le hρ₀
      _ < 1 := by rw [mul_div_assoc', div_lt_one (by linarith)]; linarith
  have h1 := (reflPot_smooth hb hρ₀ hρw (n := (⊤ : ℕ∞))).1
  have h2 := (contDiff_logPot_of_smooth hX hXc).contDiffAt (x := w)
  exact ((h1.sub h2).div_const _).contDiffWithinAt

/-- The Green potential as an integral against the Green function. -/
lemma greenPot_eq_integral (hf : BddSupp F M ρ) (w : ℂ) :
    greenPot F w = ∫ η, diskGreen w η * F η := by
  unfold greenPot reflPot logPot diskGreen
  rw [← integral_sub (integrable_reflPot_integrand hf w) (integrable_log_mul hf w),
    ← integral_div]
  congr 1; funext η; ring

lemma diskGreen_symm (w η : ℂ) : diskGreen w η = diskGreen η w := by
  unfold diskGreen
  have h1 : ‖1 - conj η * w‖ = ‖1 - conj w * η‖ := by
    rw [← Complex.norm_conj]; congr 1; simp [mul_comm]
  rw [h1, norm_sub_rev w η]

lemma norm_sub_le_norm_one_sub_conj_mul {w η : ℂ} (hw : ‖w‖ ≤ 1) (hη : ‖η‖ ≤ 1) :
    ‖w - η‖ ≤ ‖1 - conj η * w‖ := by
  have key : ‖1 - conj η * w‖ ^ 2 - ‖w - η‖ ^ 2 = (1 - ‖w‖ ^ 2) * (1 - ‖η‖ ^ 2) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re,
      Complex.one_im]
    ring
  have h1 : 0 ≤ (1 - ‖w‖ ^ 2) * (1 - ‖η‖ ^ 2) := by
    apply mul_nonneg <;> nlinarith [norm_nonneg w, norm_nonneg η]
  have : ‖w - η‖ ^ 2 ≤ ‖1 - conj η * w‖ ^ 2 := by linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

lemma diskGreen_bounds {w η : ℂ} (hw : ‖w‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hne : w ≠ η) :
    0 ≤ diskGreen w η ∧ diskGreen w η ≤ (Real.log 2 - Real.log ‖w - η‖) / (2 * π) := by
  have hpos : 0 < ‖w - η‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have h1 := norm_sub_le_norm_one_sub_conj_mul hw hη
  have h2 : ‖1 - conj η * w‖ ≤ 2 := by
    calc ‖1 - conj η * w‖ ≤ ‖(1 : ℂ)‖ + ‖conj η * w‖ := norm_sub_le _ _
      _ ≤ 2 := by
        rw [norm_one, norm_mul, Complex.norm_conj]
        nlinarith [norm_nonneg w, norm_nonneg η]
  unfold diskGreen
  constructor
  · apply div_nonneg _ (by positivity)
    linarith [Real.log_le_log hpos h1]
  · apply div_le_div_of_nonneg_right _ (by positivity)
    linarith [Real.log_le_log (hpos.trans_le h1) h2]

lemma measurable_diskGreen : Measurable (Function.uncurry diskGreen) := by
  unfold diskGreen Function.uncurry
  fun_prop

end

section

/-! ## Regularity of weak Dirichlet solutions on the unit disk -/

open MeasureTheory Set Real Metric Filter Topology
open scoped ComplexConjugate

instance isFiniteMeasure_restrict_ball (c : ℂ) (r : ℝ) :
    IsFiniteMeasure (volume.restrict (ball c r)) :=
  isFiniteMeasure_restrict.2 measure_ball_lt_top.ne

/-- Cauchy–Schwarz for real integrals. -/
lemma abs_integral_mul_le_sqrt {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤ √(∫ x, f x ^ 2 ∂μ) * √(∫ x, g x ^ 2 ∂μ) := by
  have h2 : ENNReal.ofReal 2 = 2 := by norm_num
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (f := fun x => |f x|) (g := fun x => |g x|) (μ := μ)
    (Eventually.of_forall fun x => abs_nonneg _) (Eventually.of_forall fun x => abs_nonneg _)
    (by rw [h2]; exact hf.abs) (by rw [h2]; exact hg.abs)
  have e1 : ∀ φ : α → ℝ, (∫ a, |φ a| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = √(∫ a, φ a ^ 2 ∂μ) := by
    intro φ
    rw [Real.sqrt_eq_rpow]
    congr 1
    congr 1; funext a
    rw [Real.rpow_two, sq_abs]
  rw [e1, e1] at h
  calc |∫ x, f x * g x ∂μ| ≤ ∫ x, |f x * g x| ∂μ := abs_integral_le_integral_abs
    _ = ∫ x, |f x| * |g x| ∂μ := by simp_rw [abs_mul]
    _ ≤ _ := h

/-- Translation of an integral over a ball. -/
lemma setIntegral_ball_sub (g : ℂ → ℝ) (w : ℂ) (R : ℝ) :
    ∫ η in ball w R, g (w - η) = ∫ y in ball (0 : ℂ) R, g y := by
  rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball]
  have : (ball w R).indicator (fun η => g (w - η)) = fun η => (ball 0 R).indicator g (w - η) := by
    funext η
    by_cases h : η ∈ ball w R
    · have h' : w - η ∈ ball (0 : ℂ) R := by
        rw [mem_ball_zero_iff, norm_sub_rev]; exact mem_ball_iff_norm.1 h
      simp [indicator_of_mem h, indicator_of_mem h']
    · have h' : w - η ∉ ball (0 : ℂ) R := by
        rw [mem_ball_zero_iff, norm_sub_rev]; exact fun h2 => h (mem_ball_iff_norm.2 h2)
      simp [indicator_of_notMem h, indicator_of_notMem h']
  rw [this, integral_sub_left_eq_self (fun y => (ball (0 : ℂ) R).indicator g y)]

/-- Majorant of the squared Green function. -/
def gBound (y : ℂ) : ℝ := (2 * Real.log 2 ^ 2 + 2 * Real.log ‖y‖ ^ 2) / (4 * π ^ 2)

lemma diskGreen_sq_le {w η : ℂ} (hw : ‖w‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hne : w ≠ η) :
    diskGreen w η ^ 2 ≤ gBound (w - η) := by
  obtain ⟨h0, h1⟩ := diskGreen_bounds hw hη hne
  have h2 : diskGreen w η ^ 2 ≤ ((Real.log 2 - Real.log ‖w - η‖) / (2 * π)) ^ 2 :=
    pow_le_pow_left₀ h0 h1 2
  refine h2.trans ?_
  unfold gBound
  rw [div_pow, mul_pow, show (2 : ℝ) ^ 2 * π ^ 2 = 4 * π ^ 2 by ring]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [sq_nonneg (Real.log 2 + Real.log ‖w - η‖)]

lemma integrableOn_gBound (R : ℝ) : IntegrableOn gBound (ball 0 R) := by
  unfold gBound
  refine Integrable.div_const ?_ _
  exact (integrableOn_const (measure_ball_lt_top.ne)).add
    ((integrableOn_ball_log_norm_sq R).const_mul 2)

/-- The constant bounding `∫_𝔻 G(w, ·)²`. -/
def greenL2Const : ℝ := ∫ y in ball (0 : ℂ) 2, gBound y

lemma measurable_diskGreen_left (w : ℂ) : Measurable (diskGreen w) := by
  unfold diskGreen
  fun_prop

lemma diskGreen_sq_integrable {w : ℂ} (hw : ‖w‖ ≤ 1) :
    IntegrableOn (fun η => diskGreen w η ^ 2) (ball 0 1) ∧
      ∫ η in ball (0 : ℂ) 1, diskGreen w η ^ 2 ≤ greenL2Const := by
  have hsub : ball (0 : ℂ) 1 ⊆ ball w 2 := by
    intro η hη
    rw [mem_ball_zero_iff] at hη
    rw [mem_ball, dist_eq_norm]
    calc ‖η - w‖ ≤ ‖η‖ + ‖w‖ := norm_sub_le _ _
      _ < 2 := by linarith
  have hgi : IntegrableOn (fun η => gBound (w - η)) (ball w 2) :=
    integrableOn_ball_sub (integrableOn_gBound 2) w
  have hgnn : ∀ y, 0 ≤ gBound y := fun y => by unfold gBound; positivity
  have hae : ∀ᵐ η ∂(volume.restrict (ball (0 : ℂ) 1)), ‖diskGreen w η ^ 2‖ ≤ gBound (w - η) := by
    have h1 := ae_restrict_of_ae (μ := volume) (s := ball (0 : ℂ) 1) (ae_ne_point w)
    filter_upwards [h1, ae_restrict_mem measurableSet_ball] with η hη hηD
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact diskGreen_sq_le hw (mem_ball_zero_iff.1 hηD).le (Ne.symm hη)
  have hint : IntegrableOn (fun η => diskGreen w η ^ 2) (ball 0 1) :=
    Integrable.mono' (hgi.mono_set hsub) ((measurable_diskGreen_left w).pow_const 2).aestronglyMeasurable hae
  refine ⟨hint, ?_⟩
  calc ∫ η in ball (0 : ℂ) 1, diskGreen w η ^ 2 ≤ ∫ η in ball (0 : ℂ) 1, gBound (w - η) :=
        setIntegral_mono_ae_restrict hint (hgi.mono_set hsub)
          (by filter_upwards [hae] with η hη; exact (le_abs_self _).trans (by simpa using hη))
    _ ≤ ∫ η in ball w 2, gBound (w - η) :=
        setIntegral_mono_set hgi (Eventually.of_forall fun η => hgnn _)
          (Eventually.of_forall hsub)
    _ = greenL2Const := setIntegral_ball_sub gBound w 2

lemma memLp_diskGreen {w : ℂ} (hw : ‖w‖ ≤ 1) :
    MemLp (diskGreen w) 2 (volume.restrict (ball 0 1)) :=
  (memLp_two_iff_integrable_sq (measurable_diskGreen_left w).aestronglyMeasurable).2
    (diskGreen_sq_integrable hw).1

/-- The Green potential of an `L²(𝔻)` density, restricted to `𝔻`. -/
def greenPotD (f : ℂ → ℝ) (w : ℂ) : ℝ := ∫ η in ball (0 : ℂ) 1, diskGreen w η * f η

lemma abs_greenPotD_le {f : ℂ → ℝ} (hf : MemLp f 2 (volume.restrict (ball 0 1))) {w : ℂ}
    (hw : ‖w‖ ≤ 1) :
    |greenPotD f w| ≤ √greenL2Const * √(∫ η in ball (0 : ℂ) 1, f η ^ 2) := by
  refine (abs_integral_mul_le_sqrt (memLp_diskGreen hw) hf).trans ?_
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (diskGreen_sq_integrable hw).2)
    (Real.sqrt_nonneg _)

lemma stronglyMeasurable_greenPotD {f : ℂ → ℝ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (greenPotD f) := by
  have h : StronglyMeasurable (fun p : ℂ × ℂ => diskGreen p.1 p.2 * f p.2) :=
    (measurable_diskGreen.stronglyMeasurable).mul (hf.comp_measurable measurable_snd)
  exact h.integral_prod_right' (ν := volume.restrict (ball (0 : ℂ) 1))

lemma integral_abs_diskGreen_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ∫ η in ball (0 : ℂ) 1, |diskGreen w η| ≤
      √(volume.real (ball (0 : ℂ) 1)) * √greenL2Const := by
  have h1 : MemLp (fun _ : ℂ => (1 : ℝ)) 2 (volume.restrict (ball (0 : ℂ) 1)) := memLp_const 1
  have h := abs_integral_mul_le_sqrt h1 (memLp_diskGreen hw).abs
  simp only [one_mul, one_pow, integral_const, smul_eq_mul, mul_one, Pi.abs_apply, sq_abs] at h
  rw [measureReal_restrict_apply_univ] at h
  refine (le_abs_self _).trans (h.trans ?_)
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (diskGreen_sq_integrable hw).2)
    (Real.sqrt_nonneg _)

/-- **Duality** `∫_𝔻 f · G χ = ∫_𝔻 χ · G f`. -/
lemma green_duality {f χ : ℂ → ℝ} (hf : MemLp f 2 (volume.restrict (ball 0 1)))
    (hfm : StronglyMeasurable f) (hχ : Continuous χ) (hχs : ∀ x ∉ ball (0 : ℂ) 1, χ x = 0)
    {Mχ : ℝ} (hχb : ∀ x, |χ x| ≤ Mχ) :
    ∫ η in ball (0 : ℂ) 1, f η * (∫ ζ, diskGreen η ζ * χ ζ) =
      ∫ ζ in ball (0 : ℂ) 1, χ ζ * greenPotD f ζ := by
  set D := ball (0 : ℂ) 1
  set μD := volume.restrict D
  have hinner : ∀ η, (∫ ζ, diskGreen η ζ * χ ζ) = ∫ ζ in D, diskGreen η ζ * χ ζ := by
    intro η
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro ζ hζ; simp [hχs ζ hζ]
  simp_rw [hinner]
  set F : ℂ × ℂ → ℝ := fun p => f p.1 * (diskGreen p.1 p.2 * χ p.2)
  have hFm : StronglyMeasurable F :=
    (hfm.comp_measurable measurable_fst).mul ((measurable_diskGreen.stronglyMeasurable).mul
      (hχ.stronglyMeasurable.comp_measurable measurable_snd))
  have hK := fun η (hη : η ∈ D) => integral_abs_diskGreen_le (mem_ball_zero_iff.1 hη).le
  set K := √(volume.real D) * √greenL2Const
  have hMχ : 0 ≤ Mχ := (abs_nonneg _).trans (hχb 0)
  have hfint : Integrable f μD := hf.integrable (by norm_num)
  have hGint : ∀ η ∈ D, Integrable (fun ζ => diskGreen η ζ) μD := fun η hη =>
    (memLp_diskGreen (mem_ball_zero_iff.1 hη).le).integrable (by norm_num)
  have hFint : Integrable F (μD.prod μD) := by
    rw [integrable_prod_iff hFm.aestronglyMeasurable]
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_ball] with η hη
      refine ((hGint η hη).mul_bdd hχ.aestronglyMeasurable (c := Mχ)
        (Eventually.of_forall fun ζ => by simpa using hχb ζ)).const_mul (f η)
    · refine Integrable.mono' (hfint.norm.mul_const (Mχ * K)) ?_ ?_
      · exact (hFm.norm.integral_prod_right' (ν := μD)).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_ball] with η hη
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        calc ∫ ζ, ‖F (η, ζ)‖ ∂μD ≤ ∫ ζ, ‖f η‖ * (Mχ * |diskGreen η ζ|) ∂μD := by
              refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
                (((hGint η hη).abs.const_mul Mχ).const_mul _) (Eventually.of_forall fun ζ => ?_)
              simp only [F, norm_mul, Real.norm_eq_abs]
              rw [mul_comm (|diskGreen η ζ|) (|χ ζ|)]
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right (hχb ζ) (abs_nonneg _)) (abs_nonneg _)
          _ = ‖f η‖ * (Mχ * ∫ ζ in D, |diskGreen η ζ|) := by
              rw [integral_const_mul, integral_const_mul]
          _ ≤ ‖f η‖ * (Mχ * K) := by
              gcongr
              exact hK η hη
  have hswap := integral_integral_swap (μ := μD) (ν := μD) (f := fun η ζ => F (η, ζ)) hFint
  simp only [F] at hswap
  calc ∫ η in D, f η * ∫ ζ in D, diskGreen η ζ * χ ζ
      = ∫ η in D, ∫ ζ in D, f η * (diskGreen η ζ * χ ζ) := by
        congr 1; funext η; rw [integral_const_mul]
    _ = ∫ ζ in D, ∫ η in D, f η * (diskGreen η ζ * χ ζ) := hswap
    _ = ∫ ζ in D, χ ζ * greenPotD f ζ := by
        congr 1; funext ζ
        unfold greenPotD
        rw [← integral_const_mul]
        congr 1; funext η
        rw [diskGreen_symm η ζ]; ring

/-- The weak Dirichlet problem `Δv + k²ρv = 0` on the unit disk. -/
def DiskWeak (ρw : ℂ → ℝ) (k : ℝ) (v : ℂ → ℝ) : Prop :=
  ∀ (W : Set ℂ) (w : ℂ → ℝ), IsOpen W → closedBall 0 1 ⊆ W → ContDiffOn ℝ (⊤ : ℕ∞) w W →
    (∀ z ∈ sphere (0 : ℂ) 1, w z = 0) →
    ∫ z in ball (0 : ℂ) 1, v z * (Laplacian.laplacian w z + k ^ 2 * ρw z * w z) = 0

lemma exists_bound_ball_of_continuous {g : ℂ → ℝ} (hg : Continuous g) :
    ∃ C, ∀ z ∈ ball (0 : ℂ) 1, |g z| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hg.continuousOn
  exact ⟨C, fun z hz => by simpa using hC z (ball_subset_closedBall hz)⟩

/-- Testing the weak equation against Green potentials. -/
lemma disk_weak_test {ρw : ℂ → ℝ} {k : ℝ} {v f : ℂ → ℝ}
    (hv : MemLp v 2 (volume.restrict (ball 0 1))) (hw : DiskWeak ρw k v)
    (hf : MemLp f 2 (volume.restrict (ball 0 1))) (hfm : StronglyMeasurable f)
    (hfe : f =ᵐ[volume.restrict (ball 0 1)] fun z => k ^ 2 * ρw z * v z)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ ball 0 1) :
    ∫ z in ball (0 : ℂ) 1, v z * χ z = ∫ z in ball (0 : ℂ) 1, χ z * greenPotD f z := by
  set D := ball (0 : ℂ) 1
  set μD := volume.restrict D
  obtain ⟨ρ₀, hρ₀1, hρ₀s⟩ := exists_lt_subset_ball (isClosed_tsupport χ) hχs
  set ρ₁ := max ρ₀ 0
  have hρ₁0 : 0 ≤ ρ₁ := le_max_right _ _
  have hρ₁1 : ρ₁ < 1 := max_lt hρ₀1 one_pos
  have hsupp : ∀ x, ρ₁ < ‖x‖ → χ x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxs
    have := mem_ball_zero_iff.1 (hρ₀s hxs)
    linarith [le_max_left ρ₀ 0]
  obtain ⟨Mχ, hMχ⟩ := hχ.continuous.bounded_above_of_compact_support hχc
  have hb : BddSupp χ Mχ ρ₁ :=
    ⟨hχ.continuous.aestronglyMeasurable, fun x => by simpa using hMχ x, hsupp⟩
  obtain ⟨R, hR1, hRs⟩ := greenPot_smooth_of_smooth hχ hχc hρ₁0 hρ₁1 hsupp
  have hcl : closedBall (0 : ℂ) 1 ⊆ ball 0 R := closedBall_subset_ball hR1
  have hweq := hw (ball 0 R) (greenPot χ) isOpen_ball hcl hRs
    (fun z hz => greenPot_eq_zero_of_norm_eq_one hb (by simpa using hz))
  have hlap : ∀ z ∈ D, Laplacian.laplacian (greenPot χ) z = -χ z := fun z hz =>
    (greenPot_laplacian hb hρ₁0 hρ₁1.le isOpen_ball subset_rfl
      (hχ.of_le (by norm_cast)).contDiffOn hz).2
  have hWc : Continuous (greenPot χ) := (greenPot_contDiff hb hρ₁0).continuous
  obtain ⟨MW, hMW⟩ := exists_bound_ball_of_continuous hWc
  have hvi : Integrable v μD := hv.integrable (by norm_num)
  have hfi : Integrable f μD := hf.integrable (by norm_num)
  have hvχ : Integrable (fun z => v z * χ z) μD :=
    hvi.mul_bdd hχ.continuous.aestronglyMeasurable
      (Eventually.of_forall fun z => by simpa using hMχ z)
  have hfW : Integrable (fun z => f z * greenPot χ z) μD :=
    hfi.mul_bdd hWc.aestronglyMeasurable
      (by filter_upwards [ae_restrict_mem measurableSet_ball] with z hz; simpa using hMW z hz)
  have h1 : ∫ z in D, v z * (Laplacian.laplacian (greenPot χ) z + k ^ 2 * ρw z * greenPot χ z) =
      ∫ z in D, (-(v z * χ z) + f z * greenPot χ z) := by
    refine integral_congr_ae ?_
    filter_upwards [hfe, ae_restrict_mem measurableSet_ball] with z hz hzD
    rw [hlap z hzD, hz]; ring
  rw [h1, integral_add (f := fun z => -(v z * χ z)) hvχ.neg hfW, integral_neg] at hweq
  have h2 : ∫ z in D, f z * greenPot χ z = ∫ z in D, χ z * greenPotD f z := by
    rw [← green_duality hf hfm hχ.continuous (fun x hx => image_eq_zero_of_notMem_tsupport
      (fun h => hx (hχs h))) (fun x => by simpa using hMχ x)]
    congr 1; funext z; rw [greenPot_eq_integral hb]
  linarith

/-- **Regularity of weak Dirichlet solutions on the disk.** -/
theorem disk_weak_regularity {ρw : ℂ → ℝ} (hρ : ContDiffOn ℝ 1 ρw (ball 0 1)) {Mρ : ℝ}
    (hρb : ∀ z ∈ ball (0 : ℂ) 1, |ρw z| ≤ Mρ) {k : ℝ} {v : ℂ → ℝ}
    (hv : MemLp v 2 (volume.restrict (ball 0 1))) (hw : DiskWeak ρw k v) :
    ∃ Φ : ℂ → ℝ, ContDiff ℝ 1 Φ ∧
      (∀ z ∈ ball (0 : ℂ) 1,
        ContDiffAt ℝ 2 Φ z ∧ Laplacian.laplacian Φ z + k ^ 2 * ρw z * Φ z = 0) ∧
      (∀ z ∈ sphere (0 : ℂ) 1, Φ z = 0) ∧ v =ᵐ[volume.restrict (ball 0 1)] Φ := by
  set D := ball (0 : ℂ) 1
  set μD := volume.restrict D
  have hρm : AEStronglyMeasurable ρw μD := hρ.continuousOn.aestronglyMeasurable measurableSet_ball
  have hg : MemLp (fun z => k ^ 2 * ρw z * v z) 2 μD := by
    refine MemLp.of_le (hv.const_mul (k ^ 2 * |Mρ|))
      ((aestronglyMeasurable_const.mul hρm).mul hv.1) ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_abs, sq_abs]
    have h1 := (hρb z hz).trans (le_abs_self Mρ)
    have h3 := mul_le_mul_of_nonneg_left h1 (sq_nonneg k)
    exact mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
  set f := D.indicator (hg.1.mk _)
  have hfm : StronglyMeasurable f := hg.1.stronglyMeasurable_mk.indicator measurableSet_ball
  have hfe : f =ᵐ[μD] fun z => k ^ 2 * ρw z * v z := by
    filter_upwards [hg.1.ae_eq_mk, ae_restrict_mem measurableSet_ball] with z hz hzD
    simp only [f, indicator_of_mem hzD]; exact hz.symm
  have hf : MemLp f 2 μD := hg.ae_eq hfe.symm
  set Φ₀ := greenPotD f
  set C := √greenL2Const * √(∫ η in D, f η ^ 2)
  have hC0 : 0 ≤ C := by positivity
  have hΦ₀b : ∀ z ∈ D, |Φ₀ z| ≤ C := fun z hz =>
    abs_greenPotD_le hf (mem_ball_zero_iff.1 hz).le
  have hΦ₀m : StronglyMeasurable Φ₀ := stronglyMeasurable_greenPotD hfm
  have hvi : Integrable v μD := hv.integrable (by norm_num)
  have hΦ₀i : Integrable Φ₀ μD := Integrable.of_bound hΦ₀m.aestronglyMeasurable C
    (by filter_upwards [ae_restrict_mem measurableSet_ball] with z hz; simpa using hΦ₀b z hz)
  have hae := isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := volume) (f := fun z => v z - Φ₀ z) (IntegrableOn.locallyIntegrableOn (s := D) (hvi.sub hΦ₀i))
    (fun g hgs hgc hgt => by
      obtain ⟨Mg, hMg⟩ := hgs.continuous.bounded_above_of_compact_support hgc
      have hgm := hgs.continuous.aestronglyMeasurable (μ := μD)
      have hb1 : Integrable (fun z => v z * g z) μD :=
        hvi.mul_bdd hgm (Eventually.of_forall fun z => hMg z)
      have hb2 : Integrable (fun z => g z * Φ₀ z) μD :=
        hΦ₀i.bdd_mul hgm (Eventually.of_forall fun z => hMg z)
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := D)
        (fun z hz => by simp [image_eq_zero_of_notMem_tsupport (fun h => hz (hgt h))])]
      have e : ∀ z, g z • (v z - Φ₀ z) = v z * g z - g z * Φ₀ z := fun z => by
        simp only [smul_eq_mul]; ring
      simp_rw [e]
      rw [integral_sub hb1 hb2, disk_weak_test hv hw hf hfm hfe hgs hgc hgt, sub_self])
  have hve : v =ᵐ[μD] Φ₀ := by
    filter_upwards [(ae_restrict_iff' measurableSet_ball).2 hae] with z hz
    exact sub_eq_zero.1 hz
  set F₁ := D.indicator (fun z => k ^ 2 * ρw z * Φ₀ z)
  have hF₁e : F₁ =ᵐ[volume] f := by
    filter_upwards [(ae_restrict_iff' measurableSet_ball).1 hve,
      (ae_restrict_iff' measurableSet_ball).1 hfe] with z h1 h2
    by_cases hz : z ∈ D
    · have h2' := h2 hz
      simp only [F₁, f, indicator_of_mem hz] at h2' ⊢
      rw [h2', h1 hz]
    · simp [F₁, f, indicator_of_notMem hz]
  have hb : BddSupp F₁ (k ^ 2 * |Mρ| * C) 1 := by
    refine ⟨hfm.aestronglyMeasurable.congr hF₁e.symm, fun x => ?_, fun x hx => ?_⟩
    · by_cases hx : x ∈ D
      · simp only [F₁, indicator_of_mem hx, abs_mul, abs_pow, sq_abs]
        have h1 := (hρb x hx).trans (le_abs_self Mρ)
        have h3 := mul_le_mul_of_nonneg_left h1 (sq_nonneg k)
        exact mul_le_mul h3 (hΦ₀b x hx) (abs_nonneg _) (by positivity)
      · simp only [F₁, indicator_of_notMem hx, abs_zero]; positivity
    · have : x ∉ D := fun h => by have := mem_ball_zero_iff.1 h; linarith
      simp [F₁, indicator_of_notMem this]
  have hΦeq : ∀ w, greenPot F₁ w = Φ₀ w := by
    intro w
    rw [greenPot_eq_integral hb]
    calc ∫ η, diskGreen w η * F₁ η = ∫ η, diskGreen w η * f η :=
          integral_congr_ae (by filter_upwards [hF₁e] with η hη; rw [hη])
      _ = Φ₀ w := by
          unfold Φ₀ greenPotD
          rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
          intro η hη
          have : f η = 0 := indicator_of_notMem hη _
          rw [this, mul_zero]
  have hΦc : ContDiff ℝ 1 (greenPot F₁) := greenPot_contDiff hb zero_le_one
  have hF₁c : ContDiffOn ℝ 1 F₁ D := by
    refine (((contDiffOn_const (c := k ^ 2)).mul hρ).mul hΦc.contDiffOn).congr fun z hz => ?_
    simp only [F₁, indicator_of_mem hz, hΦeq]
  refine ⟨greenPot F₁, hΦc, fun z hz => ?_, fun z hz => greenPot_eq_zero_of_norm_eq_one hb
    (by simpa using hz), ?_⟩
  · obtain ⟨h1, h2⟩ := greenPot_laplacian hb zero_le_one le_rfl isOpen_ball subset_rfl hF₁c hz
    refine ⟨h1, ?_⟩
    rw [h2]; simp only [F₁, indicator_of_mem hz, hΦeq]; ring
  · filter_upwards [hve] with z hz; rw [hz, hΦeq]

end

section

/-! ## The weighted Green operator on `L²(𝔻)` -/

open MeasureTheory Set Real Metric Filter Topology
open scoped ComplexConjugate InnerProductSpace

lemma inner_Lp_eq (f g : Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1))) : ⟪f, g⟫_ℝ = ∫ x, f x * g x ∂(volume.restrict (ball (0 : ℂ) 1)) := by
  rw [L2.inner_def]; simp [mul_comm]

lemma norm_Lp_sq_eq (f : Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1))) : ‖f‖ ^ 2 = ∫ x, f x ^ 2 ∂(volume.restrict (ball (0 : ℂ) 1)) := by
  rw [← real_inner_self_eq_norm_sq, inner_Lp_eq]; simp [sq]

lemma integral_sq_toLp {f : ℂ → ℝ} (hf : MemLp f 2 (volume.restrict (ball (0 : ℂ) 1))) :
    ∫ x, (hf.toLp f) x ^ 2 ∂(volume.restrict (ball (0 : ℂ) 1)) = ∫ x, f x ^ 2 ∂(volume.restrict (ball (0 : ℂ) 1)) :=
  integral_congr_ae (by filter_upwards [hf.coeFn_toLp] with x hx; rw [hx])

lemma norm_toLp_sq {f : ℂ → ℝ} (hf : MemLp f 2 (volume.restrict (ball (0 : ℂ) 1))) : ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂(volume.restrict (ball (0 : ℂ) 1)) := by
  rw [norm_Lp_sq_eq, integral_sq_toLp]

/-- Multiplication by a bounded measurable weight preserves `L²(𝔻)`. -/
lemma memLp_mul_weight {a f : ℂ → ℝ} (ha : Measurable a) {A : ℝ}
    (hA : ∀ η ∈ ball (0 : ℂ) 1, |a η| ≤ A) (hf : MemLp f 2 (volume.restrict (ball (0 : ℂ) 1))) :
    MemLp (fun η => a η * f η) 2 (volume.restrict (ball (0 : ℂ) 1)) := by
  refine MemLp.of_le (hf.const_mul A) (ha.aestronglyMeasurable.mul hf.1) ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with η hη
  simp only [Real.norm_eq_abs, abs_mul]
  have hA0 : |a η| ≤ |A| := (hA η hη).trans (le_abs_self A)
  exact mul_le_mul_of_nonneg_right hA0 (abs_nonneg _)

lemma integral_sq_mul_weight_le {a f : ℂ → ℝ} {A : ℝ}
    (hA : ∀ η ∈ ball (0 : ℂ) 1, |a η| ≤ A) (hf : MemLp f 2 (volume.restrict (ball (0 : ℂ) 1))) :
    ∫ η, (a η * f η) ^ 2 ∂(volume.restrict (ball (0 : ℂ) 1)) ≤ A ^ 2 * ∫ η, f η ^ 2 ∂(volume.restrict (ball (0 : ℂ) 1)) := by
  rw [← integral_const_mul]
  have hf2 : Integrable (fun η => f η ^ 2) (volume.restrict (ball (0 : ℂ) 1)) := (memLp_two_iff_integrable_sq hf.1).1 hf
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
    (hf2.const_mul _) ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with η hη
  rw [mul_pow]
  have : a η ^ 2 ≤ A ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hA η hη) 2
  exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

/-! ### Linearity of the Green potential -/

lemma integrable_diskGreen_mul {f : ℂ → ℝ} (hf : MemLp f 2 (volume.restrict (ball (0 : ℂ) 1))) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    Integrable (fun η => diskGreen w η * f η) (volume.restrict (ball (0 : ℂ) 1)) :=
  (memLp_diskGreen hw).integrable_mul hf

lemma greenPotD_congr_ae {f g : ℂ → ℝ} (h : f =ᵐ[(volume.restrict (ball (0 : ℂ) 1))] g) : greenPotD f = greenPotD g := by
  funext w
  unfold greenPotD
  refine integral_congr_ae ?_
  filter_upwards [h] with η hη; rw [hη]

lemma greenPotD_add {f g : ℂ → ℝ} (hf : MemLp f 2 (volume.restrict (ball (0 : ℂ) 1))) (hg : MemLp g 2 (volume.restrict (ball (0 : ℂ) 1))) {w : ℂ}
    (hw : ‖w‖ ≤ 1) : greenPotD (fun η => f η + g η) w = greenPotD f w + greenPotD g w := by
  unfold greenPotD
  rw [← integral_add (integrable_diskGreen_mul hf hw) (integrable_diskGreen_mul hg hw)]
  congr 1; funext η; ring

lemma greenPotD_smul (c : ℝ) (f : ℂ → ℝ) (w : ℂ) :
    greenPotD (fun η => c * f η) w = c * greenPotD f w := by
  unfold greenPotD
  rw [← integral_const_mul]
  congr 1; funext η; ring

/-- Duality for two `L²` densities: `∫_𝔻 χ · G f = ∫_𝔻 f · G χ`. -/
lemma green_duality_L2 {f χ : ℂ → ℝ} (hf : MemLp f 2 (volume.restrict (ball (0 : ℂ) 1))) (hfm : StronglyMeasurable f)
    (hχ : MemLp χ 2 (volume.restrict (ball (0 : ℂ) 1))) (hχm : StronglyMeasurable χ) :
    ∫ w, χ w * greenPotD f w ∂(volume.restrict (ball (0 : ℂ) 1)) = ∫ η, f η * greenPotD χ η ∂(volume.restrict (ball (0 : ℂ) 1)) := by
  set F : ℂ × ℂ → ℝ := fun p => χ p.1 * (diskGreen p.1 p.2 * f p.2)
  have hFm : StronglyMeasurable F :=
    (hχm.comp_measurable measurable_fst).mul ((measurable_diskGreen.stronglyMeasurable).mul
      (hfm.comp_measurable measurable_snd))
  set C := √greenL2Const * √(∫ η, f η ^ 2 ∂(volume.restrict (ball (0 : ℂ) 1)))
  have hχi : Integrable χ (volume.restrict (ball (0 : ℂ) 1)) := hχ.integrable (by norm_num)
  have hFint : Integrable F ((volume.restrict (ball (0 : ℂ) 1)).prod (volume.restrict (ball (0 : ℂ) 1))) := by
    rw [integrable_prod_iff hFm.aestronglyMeasurable]
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
      exact (integrable_diskGreen_mul hf (mem_ball_zero_iff.1 hw).le).const_mul (χ w)
    · refine Integrable.mono' (hχi.norm.mul_const C) ?_ ?_
      · exact (hFm.norm.integral_prod_right' (ν := (volume.restrict (ball (0 : ℂ) 1)))).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
        have hw1 : ‖w‖ ≤ 1 := (mem_ball_zero_iff.1 hw).le
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        have e : ∫ η, ‖F (w, η)‖ ∂(volume.restrict (ball (0 : ℂ) 1)) = ‖χ w‖ * ∫ η, |diskGreen w η| * |f η| ∂(volume.restrict (ball (0 : ℂ) 1)) := by
          rw [← integral_const_mul]; congr 1; funext η
          simp only [F, norm_mul, Real.norm_eq_abs]
        rw [e]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have h := abs_integral_mul_le_sqrt (memLp_diskGreen hw1).abs hf.abs
        simp only [Pi.abs_apply, sq_abs] at h
        refine (le_abs_self _).trans (h.trans ?_)
        exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (diskGreen_sq_integrable hw1).2)
          (Real.sqrt_nonneg _)
  have hswap := integral_integral_swap (μ := (volume.restrict (ball (0 : ℂ) 1))) (ν := (volume.restrict (ball (0 : ℂ) 1))) (f := fun w η => F (w, η)) hFint
  simp only [F] at hswap
  calc ∫ w, χ w * greenPotD f w ∂(volume.restrict (ball (0 : ℂ) 1))
      = ∫ w, ∫ η, χ w * (diskGreen w η * f η) ∂(volume.restrict (ball (0 : ℂ) 1)) ∂(volume.restrict (ball (0 : ℂ) 1)) := by
        congr 1; funext w; unfold greenPotD; rw [integral_const_mul]
    _ = ∫ η, ∫ w, χ w * (diskGreen w η * f η) ∂(volume.restrict (ball (0 : ℂ) 1)) ∂(volume.restrict (ball (0 : ℂ) 1)) := hswap
    _ = ∫ η, f η * greenPotD χ η ∂(volume.restrict (ball (0 : ℂ) 1)) := by
        congr 1; funext η
        unfold greenPotD
        rw [← integral_const_mul]
        congr 1; funext w
        rw [diskGreen_symm w η]; ring

/-! ### The operator -/

variable {a : ℂ → ℝ} {A : ℝ}

/-- The function `a · G(a f)`. -/
def greenOpFun (a f : ℂ → ℝ) (w : ℂ) : ℝ := a w * greenPotD (fun η => a η * f η) w

lemma abs_greenOpFun_le (hA : ∀ η ∈ ball (0 : ℂ) 1, |a η| ≤ A) {f : ℂ → ℝ}
    (hf : MemLp f 2 (volume.restrict (ball (0 : ℂ) 1))) {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) (ha : Measurable a) :
    |greenOpFun a f w| ≤ A * (√greenL2Const * (A * √(∫ η, f η ^ 2 ∂(volume.restrict (ball (0 : ℂ) 1))))) := by
  unfold greenOpFun
  rw [abs_mul]
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA w hw)
  refine mul_le_mul (hA w hw) ?_ (abs_nonneg _) hA0
  refine (abs_greenPotD_le (memLp_mul_weight ha hA hf) (mem_ball_zero_iff.1 hw).le).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  rw [← Real.sqrt_sq hA0, ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt (integral_sq_mul_weight_le hA hf)

lemma memLp_greenOpFun (ha : Measurable a) (hA : ∀ η ∈ ball (0 : ℂ) 1, |a η| ≤ A)
    {f : ℂ → ℝ} (hf : MemLp f 2 (volume.restrict (ball (0 : ℂ) 1))) (hfm : StronglyMeasurable f) :
    MemLp (greenOpFun a f) 2 (volume.restrict (ball (0 : ℂ) 1)) := by
  refine MemLp.of_bound ?_ (A * (√greenL2Const * (A * √(∫ η, f η ^ 2 ∂(volume.restrict (ball (0 : ℂ) 1)))))) ?_
  · exact (ha.stronglyMeasurable.mul (stronglyMeasurable_greenPotD
      (ha.stronglyMeasurable.mul hfm))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    rw [Real.norm_eq_abs]; exact abs_greenOpFun_le hA hf hw ha

lemma greenOpFun_congr_ae {f g : ℂ → ℝ} (h : f =ᵐ[(volume.restrict (ball (0 : ℂ) 1))] g) : greenOpFun a f = greenOpFun a g := by
  unfold greenOpFun
  rw [greenPotD_congr_ae (f := fun η => a η * f η) (g := fun η => a η * g η)
    (by filter_upwards [h] with η hη; rw [hη])]

/-- The weighted Green operator as a linear map on `L²(𝔻)`. -/
def greenOpLin (ha : Measurable a) (hA : ∀ η ∈ ball (0 : ℂ) 1, |a η| ≤ A) :
    Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1)) →ₗ[ℝ] Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1)) where
  toFun f := (memLp_greenOpFun ha hA (Lp.memLp f) (Lp.stronglyMeasurable f)).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
    filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    have hw1 : ‖w‖ ≤ 1 := (mem_ball_zero_iff.1 hw).le
    simp only [Pi.add_apply]
    rw [greenOpFun_congr_ae (Lp.coeFn_add f g)]
    unfold greenOpFun
    simp only [Pi.add_apply, mul_add]
    rw [greenPotD_add (memLp_mul_weight ha hA (Lp.memLp f)) (memLp_mul_weight ha hA (Lp.memLp g))
      hw1, mul_add]
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
    refine Eventually.of_forall fun w => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [greenOpFun_congr_ae (Lp.coeFn_smul c f)]
    unfold greenOpFun
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (fun η => a η * (c * f η)) = fun η => c * (a η * f η) by funext η; ring,
      greenPotD_smul]
    ring

lemma greenOpLin_apply (ha : Measurable a) (hA : ∀ η ∈ ball (0 : ℂ) 1, |a η| ≤ A)
    (f : Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1))) : greenOpLin ha hA f =ᵐ[(volume.restrict (ball (0 : ℂ) 1))] greenOpFun a f :=
  MemLp.coeFn_toLp (memLp_greenOpFun ha hA (Lp.memLp f) (Lp.stronglyMeasurable f))

/-- The operator norm bound. -/
def greenOpBound (A : ℝ) : ℝ := √(volume.real (ball (0 : ℂ) 1)) * (A * (√greenL2Const * A))

lemma norm_greenOpLin_le (ha : Measurable a) (hA : ∀ η ∈ ball (0 : ℂ) 1, |a η| ≤ A)
    (f : Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1))) : ‖greenOpLin ha hA f‖ ≤ greenOpBound A * ‖f‖ := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 (mem_ball_self one_pos))
  have h := Lp.norm_le_of_ae_bound (f := greenOpLin ha hA f)
    (C := A * (√greenL2Const * (A * √(∫ η, f η ^ 2 ∂(volume.restrict (ball (0 : ℂ) 1)))))) (by positivity) (by
      filter_upwards [greenOpLin_apply ha hA f, ae_restrict_mem measurableSet_ball] with w hw hwD
      rw [hw, Real.norm_eq_abs]; exact abs_greenOpFun_le hA (Lp.memLp f) hwD ha)
  have e1 : (↑(measureUnivNNReal (volume.restrict (ball (0 : ℂ) 1))) : ℝ) ^ (ENNReal.toReal 2)⁻¹ =
      √(volume.real (ball (0 : ℂ) 1)) := by
    rw [Real.sqrt_eq_rpow]
    congr 1
    · simp [measureUnivNNReal, Measure.real]
    · norm_num
  have e2 : √(∫ η, f η ^ 2 ∂(volume.restrict (ball (0 : ℂ) 1))) = ‖f‖ := by
    rw [← norm_Lp_sq_eq, Real.sqrt_sq (norm_nonneg _)]
  rw [e1, e2] at h
  refine h.trans (le_of_eq ?_)
  unfold greenOpBound; ring

/-- The weighted Green operator `f ↦ a · G(a f)` on `L²(𝔻)`. -/
def greenOp (ha : Measurable a) (hA : ∀ η ∈ ball (0 : ℂ) 1, |a η| ≤ A) :
    Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1)) →L[ℝ] Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1)) :=
  (greenOpLin ha hA).mkContinuous (greenOpBound A) (norm_greenOpLin_le ha hA)

lemma greenOp_apply (ha : Measurable a) (hA : ∀ η ∈ ball (0 : ℂ) 1, |a η| ≤ A)
    (f : Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1))) : greenOp ha hA f =ᵐ[(volume.restrict (ball (0 : ℂ) 1))] greenOpFun a f :=
  greenOpLin_apply ha hA f

lemma inner_greenOp (ha : Measurable a) (hA : ∀ η ∈ ball (0 : ℂ) 1, |a η| ≤ A)
    (f g : Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1))) :
    ⟪greenOp ha hA f, g⟫_ℝ = ∫ w, (a w * g w) * greenPotD (fun η => a η * f η) w ∂(volume.restrict (ball (0 : ℂ) 1)) := by
  rw [inner_Lp_eq]
  refine integral_congr_ae ?_
  filter_upwards [greenOp_apply ha hA f] with w hw
  rw [hw, greenOpFun]; ring

/-- Symmetry of the weighted Green operator. -/
lemma greenOp_symm (ha : Measurable a) (hA : ∀ η ∈ ball (0 : ℂ) 1, |a η| ≤ A)
    (f g : Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1))) : ⟪greenOp ha hA f, g⟫_ℝ = ⟪f, greenOp ha hA g⟫_ℝ := by
  rw [inner_greenOp, real_inner_comm, inner_greenOp]
  have := green_duality_L2 (memLp_mul_weight ha hA (Lp.memLp f))
    (ha.stronglyMeasurable.mul (Lp.stronglyMeasurable f))
    (memLp_mul_weight ha hA (Lp.memLp g)) (ha.stronglyMeasurable.mul (Lp.stronglyMeasurable g))
  exact this

end

section

/-! ## Compactness of the weighted Green operator -/

open MeasureTheory Set Real Metric Filter Topology
open scoped ComplexConjugate InnerProductSpace

/-- The logarithm truncated at height `log t`. -/
def logTr (t x : ℝ) : ℝ := Real.log (max x t)

/-- The truncated Green kernel. -/
def diskGreenTr (t : ℝ) (w η : ℂ) : ℝ :=
  (logTr t ‖1 - conj η * w‖ - logTr t ‖w - η‖) / (2 * π)

lemma continuous_logTr {t : ℝ} (ht : 0 < t) : Continuous (logTr t) := by
  unfold logTr
  exact (continuous_id.max continuous_const).log fun x => (ht.trans_le (le_max_right x t)).ne'

lemma continuous_diskGreenTr {t : ℝ} (ht : 0 < t) :
    Continuous (Function.uncurry (diskGreenTr t)) := by
  unfold diskGreenTr Function.uncurry
  have h := continuous_logTr ht
  fun_prop

lemma abs_log_sub_logTr_le {t x : ℝ} (hx : 0 < x) (ht1 : t ≤ 1) :
    |Real.log x - logTr t x| ≤ if x < t then |Real.log x| else 0 := by
  unfold logTr
  split_ifs with h
  · rw [max_eq_right h.le]
    have h1 : Real.log x ≤ Real.log t := Real.log_le_log hx h.le
    have h2 : Real.log t ≤ 0 := Real.log_nonpos (hx.trans h).le ht1
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · rw [max_eq_left (not_lt.1 h)]; simp

lemma abs_diskGreen_sub_tr_le {t : ℝ} (ht1 : t ≤ 1) {w η : ℂ} (hw : ‖w‖ ≤ 1) (hη : ‖η‖ ≤ 1)
    (hne : w ≠ η) :
    |diskGreen w η - diskGreenTr t w η| ≤ (ball w t).indicator (fun η => |Real.log ‖w - η‖| / π) η := by
  have hx : 0 < ‖w - η‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have hxy := norm_sub_le_norm_one_sub_conj_mul hw hη
  have hy : 0 < ‖1 - conj η * w‖ := hx.trans_le hxy
  have e : diskGreen w η - diskGreenTr t w η =
      ((Real.log ‖1 - conj η * w‖ - logTr t ‖1 - conj η * w‖) -
        (Real.log ‖w - η‖ - logTr t ‖w - η‖)) / (2 * π) := by
    unfold diskGreen diskGreenTr; ring
  rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  have h1 := abs_log_sub_logTr_le hy ht1
  have h2 := abs_log_sub_logTr_le hx ht1
  by_cases hxt : ‖w - η‖ < t
  · have hmem : η ∈ ball w t := by rw [mem_ball, dist_comm, dist_eq_norm]; exact hxt
    rw [indicator_of_mem hmem, if_pos hxt] at *
    have h3 : |Real.log ‖1 - conj η * w‖ - logTr t ‖1 - conj η * w‖| ≤ |Real.log ‖w - η‖| := by
      refine h1.trans ?_
      split_ifs with hyt
      · have hy1 : ‖1 - conj η * w‖ < 1 := hyt.trans_le ht1
        rw [abs_of_nonpos (Real.log_nonpos hy.le hy1.le),
          abs_of_nonpos (Real.log_nonpos hx.le (hxy.trans hy1.le))]
        linarith [Real.log_le_log hx hxy]
      · exact abs_nonneg _
    rw [div_le_div_iff₀ (by positivity) pi_pos]
    have := abs_sub (Real.log ‖1 - conj η * w‖ - logTr t ‖1 - conj η * w‖)
      (Real.log ‖w - η‖ - logTr t ‖w - η‖)
    nlinarith [pi_pos, abs_nonneg (Real.log ‖w - η‖)]
  · have hmem : η ∉ ball w t := by rw [mem_ball, dist_comm, dist_eq_norm]; exact hxt
    rw [indicator_of_notMem hmem, if_neg hxt] at *
    have hyt : ¬ ‖1 - conj η * w‖ < t := fun h => hxt (hxy.trans_lt h)
    rw [if_neg hyt] at h1
    have a1 := abs_nonpos_iff.1 h1
    have a2 := abs_nonpos_iff.1 h2
    rw [a1, a2]; simp

lemma integral_ball_log_sq_small {ε : ℝ} (hε : 0 < ε) :
    ∃ t > 0, t ≤ 1 ∧ ∫ y in ball (0 : ℂ) t, Real.log ‖y‖ ^ 2 ≤ ε := by
  have hi : Integrable ((ball (0 : ℂ) 1).indicator fun y : ℂ => Real.log ‖y‖ ^ 2) :=
    (integrable_indicator_iff measurableSet_ball).2 (integrableOn_ball_log_norm_sq 1)
  have hs : Tendsto (fun t : ℝ => volume (ball (0 : ℂ) t)) (𝓝[>] 0) (𝓝 0) := by
    simp only [Complex.volume_ball]
    have : Tendsto (fun t : ℝ => ENNReal.ofReal t ^ 2 * (NNReal.pi : ENNReal)) (𝓝 0)
        (𝓝 (ENNReal.ofReal 0 ^ 2 * NNReal.pi)) := by
      refine ENNReal.Tendsto.mul_const
        (((ENNReal.continuous_pow 2).tendsto _).comp (ENNReal.continuous_ofReal.tendsto 0)) ?_
      right; exact ENNReal.coe_ne_top
    simp only [ENNReal.ofReal_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h := hi.tendsto_setIntegral_nhds_zero hs
  have hev := (h.eventually (Iio_mem_nhds hε)).and (Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨t, ht, ht0, ht1⟩ := hev.exists
  refine ⟨t, ht0, ht1, ?_⟩
  have e : ∫ y in ball (0 : ℂ) t, (ball (0 : ℂ) 1).indicator (fun y : ℂ => Real.log ‖y‖ ^ 2) y =
      ∫ y in ball (0 : ℂ) t, Real.log ‖y‖ ^ 2 :=
    setIntegral_congr_fun measurableSet_ball fun y hy =>
      indicator_of_mem (ball_subset_ball ht1 hy) _
  rw [← e]; exact ht.le

lemma integral_sq_diskGreen_sub_tr_le {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    IntegrableOn (fun η => (diskGreen w η - diskGreenTr t w η) ^ 2) (ball 0 1) ∧
    ∫ η in ball (0 : ℂ) 1, (diskGreen w η - diskGreenTr t w η) ^ 2 ≤
      (∫ y in ball (0 : ℂ) t, Real.log ‖y‖ ^ 2) / π ^ 2 := by
  set h : ℂ → ℝ := (ball w t).indicator (fun η => Real.log ‖w - η‖ ^ 2 / π ^ 2)
  have hhi : Integrable h := by
    refine (integrable_indicator_iff measurableSet_ball).2 ?_
    exact (integrableOn_ball_sub (integrableOn_ball_log_norm_sq t) w).div_const _
  have hm : AEStronglyMeasurable (fun η => (diskGreen w η - diskGreenTr t w η) ^ 2) (volume.restrict (ball (0 : ℂ) 1)) := by
    refine Measurable.aestronglyMeasurable ?_
    have h1 := measurable_diskGreen_left w
    have h2 : Measurable (diskGreenTr t w) :=
      (continuous_diskGreenTr ht0).comp (Continuous.prodMk_right w) |>.measurable
    exact (h1.sub h2).pow_const 2
  have hae : ∀ᵐ η ∂(volume.restrict (ball (0 : ℂ) 1)), ‖(diskGreen w η - diskGreenTr t w η) ^ 2‖ ≤ h η := by
    have h1 := ae_restrict_of_ae (μ := volume) (s := ball (0 : ℂ) 1) (ae_ne_point w)
    filter_upwards [h1, ae_restrict_mem measurableSet_ball] with η hη hηD
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    have hb := abs_diskGreen_sub_tr_le ht1 hw (mem_ball_zero_iff.1 hηD).le (Ne.symm hη)
    by_cases hm : η ∈ ball w t
    · rw [indicator_of_mem hm] at hb
      simp only [h, indicator_of_mem hm]
      calc |diskGreen w η - diskGreenTr t w η| ^ 2 ≤ (|Real.log ‖w - η‖| / π) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hb 2
        _ = _ := by rw [div_pow, sq_abs]
    · rw [indicator_of_notMem hm] at hb
      simp only [h, indicator_of_notMem hm]
      have := abs_nonpos_iff.1 hb
      rw [this]; simp
  have hint : IntegrableOn (fun η => (diskGreen w η - diskGreenTr t w η) ^ 2) (ball 0 1) :=
    Integrable.mono' hhi.integrableOn hm hae
  refine ⟨hint, ?_⟩
  calc ∫ η in ball (0 : ℂ) 1, (diskGreen w η - diskGreenTr t w η) ^ 2 ≤ ∫ η in ball (0 : ℂ) 1, h η :=
        setIntegral_mono_ae_restrict hint hhi.integrableOn
          (by filter_upwards [hae] with η hη; exact (le_abs_self _).trans (by simpa using hη))
    _ ≤ ∫ η, h η := by
        refine setIntegral_le_integral hhi (Eventually.of_forall fun η => ?_)
        simp only [h]; exact indicator_nonneg (fun _ _ => by positivity) _
    _ = ∫ η in ball w t, Real.log ‖w - η‖ ^ 2 / π ^ 2 := integral_indicator measurableSet_ball
    _ = (∫ y in ball (0 : ℂ) t, Real.log ‖y‖ ^ 2) / π ^ 2 := by
        rw [integral_div, setIntegral_ball_sub (fun y => Real.log ‖y‖ ^ 2) w t]

/-- **`L²` continuity of the Green function.** -/
theorem diskGreen_L2_continuous {w₀ : ℂ} (hw₀ : ‖w₀‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ w : ℂ, ‖w‖ ≤ 1 → ‖w - w₀‖ < δ →
      ∫ η in ball (0 : ℂ) 1, (diskGreen w η - diskGreen w₀ η) ^ 2 ≤ ε := by
  obtain ⟨t, ht0, ht1, htε⟩ := integral_ball_log_sq_small
    (show 0 < ε * π ^ 2 / 12 by positivity)
  set V := volume.real (ball (0 : ℂ) 1)
  have hV : 0 < V := by
    simp only [V, Measure.real, Complex.volume_ball]; simp [pi_pos]
  set s := √(ε / (6 * V))
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have huc := (isCompact_closedBall (0 : ℂ) 1 |>.prod (isCompact_closedBall (0 : ℂ) 1))
    |>.uniformContinuousOn_of_continuous (continuous_diskGreenTr ht0).continuousOn
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1 huc s hs
  refine ⟨δ, hδ, fun w hw hww => ?_⟩
  obtain ⟨i1, b1⟩ := integral_sq_diskGreen_sub_tr_le ht0 ht1 hw
  obtain ⟨i2, b2⟩ := integral_sq_diskGreen_sub_tr_le ht0 ht1 hw₀
  have hunif : ∀ η ∈ closedBall (0 : ℂ) 1, |diskGreenTr t w η - diskGreenTr t w₀ η| ≤ s := by
    intro η hη
    have := hδu (w, η) ⟨mem_closedBall_zero_iff.2 hw, hη⟩ (w₀, η)
      ⟨mem_closedBall_zero_iff.2 hw₀, hη⟩ (by
        rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, dist_eq_norm]; exact hww)
    exact (Real.dist_eq _ _ ▸ this).le
  have hmid : IntegrableOn (fun η => (diskGreenTr t w η - diskGreenTr t w₀ η) ^ 2) (ball 0 1) := by
    refine Integrable.of_bound ?_ (s ^ 2) ?_
    · exact (((continuous_diskGreenTr ht0).comp (Continuous.prodMk_right w)).sub
        ((continuous_diskGreenTr ht0).comp (Continuous.prodMk_right w₀))).pow 2
        |>.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_ball] with η hη
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hunif η (ball_subset_closedBall hη)) 2
  have hpt : ∀ η, (diskGreen w η - diskGreen w₀ η) ^ 2 ≤
      3 * (diskGreen w η - diskGreenTr t w η) ^ 2 +
      3 * (diskGreenTr t w η - diskGreenTr t w₀ η) ^ 2 +
      3 * (diskGreen w₀ η - diskGreenTr t w₀ η) ^ 2 := by
    intro η
    nlinarith [sq_nonneg (diskGreen w η - diskGreenTr t w η - (diskGreenTr t w η - diskGreenTr t w₀ η)),
      sq_nonneg (diskGreen w η - diskGreenTr t w η + (diskGreen w₀ η - diskGreenTr t w₀ η)),
      sq_nonneg (diskGreenTr t w η - diskGreenTr t w₀ η + (diskGreen w₀ η - diskGreenTr t w₀ η))]
  have hsum : IntegrableOn (fun η => 3 * (diskGreen w η - diskGreenTr t w η) ^ 2 +
      3 * (diskGreenTr t w η - diskGreenTr t w₀ η) ^ 2 +
      3 * (diskGreen w₀ η - diskGreenTr t w₀ η) ^ 2) (ball 0 1) :=
    ((i1.const_mul 3).add (hmid.const_mul 3)).add (i2.const_mul 3)
  have hlhs : IntegrableOn (fun η => (diskGreen w η - diskGreen w₀ η) ^ 2) (ball 0 1) := by
    refine Integrable.mono' hsum ?_ (Eventually.of_forall fun η => ?_)
    · exact ((measurable_diskGreen_left w).sub (measurable_diskGreen_left w₀)).pow_const 2
        |>.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt η
  have hmidb : ∫ η in ball (0 : ℂ) 1, (diskGreenTr t w η - diskGreenTr t w₀ η) ^ 2 ≤ s ^ 2 * V := by
    have := setIntegral_mono_on hmid (integrableOn_const (measure_ball_lt_top.ne) (C := s ^ 2))
      measurableSet_ball fun η hη => by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hunif η (ball_subset_closedBall hη)) 2
    simpa [V, mul_comm] using this
  have hsV : s ^ 2 * V = ε / 6 := by
    rw [Real.sq_sqrt (by positivity)]; field_simp
  calc ∫ η in ball (0 : ℂ) 1, (diskGreen w η - diskGreen w₀ η) ^ 2
      ≤ ∫ η in ball (0 : ℂ) 1, (3 * (diskGreen w η - diskGreenTr t w η) ^ 2 +
          3 * (diskGreenTr t w η - diskGreenTr t w₀ η) ^ 2 +
          3 * (diskGreen w₀ η - diskGreenTr t w₀ η) ^ 2) :=
        setIntegral_mono_on hlhs hsum measurableSet_ball fun η _ => hpt η
    _ = 3 * (∫ η in ball (0 : ℂ) 1, (diskGreen w η - diskGreenTr t w η) ^ 2) +
          3 * (∫ η in ball (0 : ℂ) 1, (diskGreenTr t w η - diskGreenTr t w₀ η) ^ 2) +
          3 * (∫ η in ball (0 : ℂ) 1, (diskGreen w₀ η - diskGreenTr t w₀ η) ^ 2) := by
        rw [integral_add (f := fun η => 3 * (diskGreen w η - diskGreenTr t w η) ^ 2 +
          3 * (diskGreenTr t w η - diskGreenTr t w₀ η) ^ 2)
          ((i1.const_mul 3).add (hmid.const_mul 3)) (i2.const_mul 3),
          integral_add (f := fun η => 3 * (diskGreen w η - diskGreenTr t w η) ^ 2)
          (i1.const_mul 3) (hmid.const_mul 3), integral_const_mul,
          integral_const_mul, integral_const_mul]
    _ ≤ 3 * ((ε * π ^ 2 / 12) / π ^ 2) + 3 * (ε / 6) + 3 * ((ε * π ^ 2 / 12) / π ^ 2) := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · exact mul_le_mul_of_nonneg_left
            (b1.trans (div_le_div_of_nonneg_right htε (by positivity))) (by norm_num)
        · rw [← hsV]; exact mul_le_mul_of_nonneg_left hmidb (by norm_num)
        · exact mul_le_mul_of_nonneg_left
            (b2.trans (div_le_div_of_nonneg_right htε (by positivity))) (by norm_num)
    _ = ε := by field_simp; ring

end

section

/-! ## Conformal invariance of the Laplacian -/

open MeasureTheory Set Real Metric Filter Topology

/-- The real derivative of a holomorphic map. -/
lemma hasFDerivAt_holo {G : ℂ → ℂ} {c y : ℂ} (h : HasDerivAt G c y) :
    HasFDerivAt G ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ) y :=
  h.hasFDerivAt.restrictScalars ℝ

lemma bilin_conformal (Q : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (hQ : Q 1 Complex.I = Q Complex.I 1) (a : ℂ) :
    Q a a + Q (Complex.I * a) (Complex.I * a) = ‖a‖ ^ 2 * (Q 1 1 + Q Complex.I Complex.I) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  set x := a.re
  set y := a.im
  have ha : a = x • (1 : ℂ) + y • Complex.I := by simp [x, y]
  have hIa : Complex.I * a = (-y) • (1 : ℂ) + x • Complex.I := by
    apply Complex.ext <;> simp [x, y]
  rw [hIa, ha]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, hQ]
  ring

/-- **Conformal invariance of the Laplacian.** -/
theorem laplacian_comp_holomorphic {f : ℂ → ℝ} {G : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S) {z : ℂ}
    (hz : z ∈ S) (hG : DifferentiableOn ℂ G S) (hf : ContDiffAt ℝ 2 f (G z)) :
    Laplacian.laplacian (f ∘ G) z = ‖deriv G z‖ ^ 2 * Laplacian.laplacian f (G z) := by
  have hGd : ∀ y ∈ S, HasDerivAt G (deriv G y) y := fun y hy =>
    (hG.differentiableAt (hS.mem_nhds hy)).hasDerivAt
  have hG2 : HasDerivAt (deriv G) (deriv (deriv G) z) z :=
    ((hG.deriv hS).differentiableAt (hS.mem_nhds hz)).hasDerivAt
  have hfev : ∀ᶠ y in 𝓝 (G z), ContDiffAt ℝ 2 f y := hf.eventually (by simp)
  have hev : ∀ᶠ y in 𝓝 z, y ∈ S ∧ ContDiffAt ℝ 2 f (G y) :=
    Filter.Eventually.and (hS.mem_nhds hz) ((hGd z hz).continuousAt.tendsto.eventually hfev)
  -- first derivative near `z`
  have hfd1 : ∀ w : ℂ, (fun y => fderiv ℝ (f ∘ G) y w) =ᶠ[𝓝 z]
      fun y => fderiv ℝ f (G y) (w * deriv G y) := by
    intro w
    filter_upwards [hev] with y ⟨hyS, hyf⟩
    have h := (hyf.differentiableAt (by norm_num)).hasFDerivAt.comp y (hasFDerivAt_holo (hGd y hyS))
    rw [h.fderiv]
    simp
  -- the second derivative
  have hf1 : ContDiffAt ℝ 1 (fderiv ℝ f) (G z) := hf.fderiv_right (by norm_num)
  have hA : HasFDerivAt (fun y => fderiv ℝ f (G y))
      ((fderiv ℝ (fderiv ℝ f) (G z)).comp
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv G z)).restrictScalars ℝ)) z :=
    (hf1.differentiableAt (by norm_num)).hasFDerivAt.comp z (hasFDerivAt_holo (hGd z hz))
  have hC2 : ContDiffAt ℝ 2 (f ∘ G) z := by
    have hGc : ContDiffAt ℝ 2 G z :=
      ((hG.contDiffOn hS (n := 2)).contDiffAt (hS.mem_nhds hz)).restrict_scalars ℝ
    exact hf.comp z hGc
  have hfd2 : ∀ v w : ℂ, fderiv ℝ (fderiv ℝ (f ∘ G)) z v w =
      fderiv ℝ (fderiv ℝ f) (G z) (v * deriv G z) (w * deriv G z) +
        fderiv ℝ f (G z) (w * (v * deriv (deriv G) z)) := by
    intro v w
    have hdiff : DifferentiableAt ℝ (fderiv ℝ (f ∘ G)) z :=
      (hC2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have e1 : fderiv ℝ (fderiv ℝ (f ∘ G)) z v w = fderiv ℝ (fun y => fderiv ℝ (f ∘ G) y w) z v := by
      rw [fderiv_clm_apply hdiff (differentiableAt_const w)]
      simp
    have hu : HasFDerivAt (fun y => w * deriv G y)
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (w * deriv (deriv G) z)).restrictScalars ℝ)
        z := hasFDerivAt_holo (hG2.const_mul w)
    have h := hA.clm_apply hu
    rw [e1, (hfd1 w).fderiv_eq, h.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, smul_eq_mul]
    rw [add_comm]
    congr 2; ring
  rw [laplacian_eq_fderiv_fderiv_real, laplacian_eq_fderiv_fderiv_real, hfd2, hfd2]
  have hsym := hf.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  have hb := bilin_conformal (fderiv ℝ (fderiv ℝ f) (G z)) (hsym 1 Complex.I) (deriv G z)
  have e2 : Complex.I * (Complex.I * deriv (deriv G) z) = -(1 * (1 * deriv (deriv G) z)) := by
    ring_nf; rw [Complex.I_sq]; ring
  rw [e2, map_neg, one_mul, ← hb]
  ring_nf

end

section

/-! ## Regularity of weak Dirichlet eigenfunctions on conformal disks -/

open MeasureTheory Set Real Metric Filter Topology

/-- `u` is a weak solution of `Δu + k²u = 0` in `Ω_r = F(r𝔻)` with Dirichlet boundary values:
`∫_{Ω_r} u (Δw + k² w) = 0` for every `w` smooth on a neighbourhood of `F(r𝔻̄)` and vanishing on
`F(r𝕋)`. -/
def WeakDirichletHelmholtz (F : ℂ → ℂ) (r k : ℝ) (u : ℂ → ℝ) : Prop :=
  ∀ (W : Set ℂ) (w : ℂ → ℝ), IsOpen W → F '' closedBall 0 r ⊆ W →
    ContDiffOn ℝ (⊤ : ℕ∞) w W → (∀ z ∈ F '' sphere 0 r, w z = 0) →
    ∫ z in F '' ball 0 r, u z * (Laplacian.laplacian w z + k ^ 2 * w z) = 0

/-- Change of variables for an injective holomorphic map (Bochner integral). -/
lemma integral_image_holomorphic {s : Set ℂ} (hs : IsOpen s) {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G s) (hinj : InjOn G s) (h : ℂ → ℝ) :
    ∫ z in G '' s, h z = ∫ η in s, ‖deriv G η‖ ^ 2 * h (G η) := by
  have hf' : ∀ z ∈ s, HasFDerivWithinAt G
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv G z)).restrictScalars ℝ) s z :=
    fun z hz => ((hG.differentiableAt (hs.mem_nhds hz)).hasDerivAt.hasFDerivAt
      |>.restrictScalars ℝ).hasFDerivWithinAt
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs.measurableSet hf' hinj h]
  refine setIntegral_congr_fun hs.measurableSet fun z _ => ?_
  simp only [smul_eq_mul]
  congr 1
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
    LinearMap.det_restrictScalars]
  simp [Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]

/-- Null sets are preserved: an a.e. identity on `s` transfers to `G(s)`. -/
lemma ae_image_holomorphic {s : Set ℂ} {G g : ℂ → ℂ} (hs : MeasurableSet s)
    (hGs : MeasurableSet (G '' s)) (hG : DifferentiableOn ℝ G s) (hgG : ∀ η ∈ s, g (G η) = η) {p q : ℂ → ℝ}
    (h : ∀ᵐ η ∂(volume.restrict s), p (G η) = q η) :
    p =ᵐ[volume.restrict (G '' s)] fun z => q (g z) := by
  have h1 := (ae_restrict_iff' hs).1 h
  rw [ae_iff] at h1
  set N := {η | ¬(η ∈ s → p (G η) = q η)}
  have hNs : N ⊆ s := fun η hη => by
    by_contra hc; exact hη fun h => absurd h hc
  have hGN : volume (G '' N) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume (hG.mono hNs) h1
  refine (ae_restrict_iff' hGs).2 ?_
  rw [ae_iff]
  refine measure_mono_null ?_ hGN
  intro z hz
  simp only [mem_setOf_eq, Classical.not_imp] at hz
  obtain ⟨⟨η, hη, rfl⟩, hne⟩ := hz
  refine ⟨η, fun h' => hne ?_, rfl⟩
  rw [hgG η hη]; exact h' hη

/-- Pullback of `L²` functions by a holomorphic map with derivative bounded below. -/
lemma memLp_comp_holomorphic {s : Set ℂ} (hs : IsOpen s) {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G s) (hinj : InjOn G s) {c : ℝ} (hc : 0 < c)
    (hcG : ∀ η ∈ s, c ≤ ‖deriv G η‖) {u : ℂ → ℝ} (hum : StronglyMeasurable u)
    (hu : MemLp u 2 (volume.restrict (G '' s))) :
    MemLp (u ∘ G) 2 (volume.restrict s) := by
  have hGm : AEMeasurable G (volume.restrict s) :=
    hG.continuousOn.aemeasurable hs.measurableSet
  have hm : AEStronglyMeasurable (u ∘ G) (volume.restrict s) := hum.aestronglyMeasurable.comp_aemeasurable hGm
  refine (memLp_two_iff_integrable_sq hm).2 ⟨hm.pow 2, ?_⟩
  have hu2 := ((memLp_two_iff_integrable_sq hu.1).1 hu).2
  unfold HasFiniteIntegral at hu2 ⊢
  have key := lintegral_image_holomorphic hs hG hinj (fun z => ‖u z ^ 2‖ₑ)
  set a := ENNReal.ofReal (c ^ 2)
  have ha0 : a ≠ 0 := by simp [a]; positivity
  have hle : ∫⁻ η in s, ‖(u ∘ G) η ^ 2‖ₑ ≤
      ∫⁻ η in s, a⁻¹ * (ENNReal.ofReal (‖deriv G η‖ ^ 2) * ‖u (G η) ^ 2‖ₑ) := by
    refine setLIntegral_mono' hs.measurableSet fun η hη => ?_
    have hab : a ≤ ENNReal.ofReal (‖deriv G η‖ ^ 2) :=
      ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hc.le (hcG η hη) 2)
    calc ‖(u ∘ G) η ^ 2‖ₑ = a⁻¹ * (a * ‖u (G η) ^ 2‖ₑ) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 ENNReal.ofReal_ne_top, one_mul]; rfl
      _ ≤ _ := by gcongr
  refine hle.trans_lt ?_
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 ha0), ← key]
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 ha0)) hu2

/-- **Regularity of weak solutions on a conformal image of the disk.** -/
theorem conformal_weak_regularity {R0 : ℝ} (hR0 : 1 < R0) {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G (ball 0 R0)) (hinj : InjOn G (ball 0 R0)) {k : ℝ} {u : ℂ → ℝ}
    (hum : StronglyMeasurable u) (hu : MemLp u 2 (volume.restrict (G '' ball 0 1)))
    (hw : WeakDirichletHelmholtz G 1 k u) :
    ∃ (V : Set ℂ) (φ : ℂ → ℝ), IsOpen V ∧ G '' closedBall 0 1 ⊆ V ∧ ContDiffOn ℝ 1 φ V ∧
      ContDiffOn ℝ 2 φ (G '' ball 0 1) ∧
      (∀ z ∈ G '' ball 0 1, Laplacian.laplacian φ z + k ^ 2 * φ z = 0) ∧
      (∀ z ∈ G '' sphere 0 1, φ z = 0) ∧ u =ᵐ[volume.restrict (G '' ball 0 1)] φ := by
  set B := ball (0 : ℂ) R0
  have hBo : IsOpen B := isOpen_ball
  have hBc : IsPreconnected B := (convex_ball _ _).isPreconnected
  have hD1 : ball (0 : ℂ) 1 ⊆ B := ball_subset_ball hR0.le
  have hcl1 : closedBall (0 : ℂ) 1 ⊆ B := closedBall_subset_ball hR0
  obtain ⟨g, hgd, -, hgG, -⟩ := exists_holomorphic_inverse hBo hBc hG hinj
  have hΩ1 : IsOpen (G '' B) :=
    isOpen_image_of_injOn hBo hBc hG hinj subset_rfl hBo
  have hΩ : IsOpen (G '' ball 0 1) :=
    isOpen_image_of_injOn hBo hBc hG hinj hD1 isOpen_ball
  have hgs : ContDiffOn ℝ (⊤ : ℕ∞) g (G '' B) := (hgd.contDiffOn hΩ1).restrict_scalars ℝ
  have hG'd : DifferentiableOn ℂ (deriv G) B := hG.deriv hBo
  have hne : ∀ η ∈ B, deriv G η ≠ 0 := fun η hη =>
    deriv_ne_zero_of_injOn hBo hG hinj hη
  set ρw : ℂ → ℝ := fun η => ‖deriv G η‖ ^ 2
  have hρ : ContDiffOn ℝ 1 ρw (ball 0 1) :=
    ((contDiff_norm_sq ℝ).comp_contDiffOn
      ((hG'd.contDiffOn hBo (n := 1)).restrict_scalars ℝ)).mono hD1
  have hG'c : ContinuousOn (deriv G) (closedBall 0 1) := hG'd.continuousOn.mono hcl1
  obtain ⟨M0, hM0⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hG'c
  have hρb : ∀ z ∈ ball (0 : ℂ) 1, |ρw z| ≤ M0 ^ 2 := fun z hz => by
    simp only [ρw, abs_pow, abs_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hM0 z (ball_subset_closedBall hz)) 2
  obtain ⟨η0, hη0, hmin⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_isMinOn
    (nonempty_closedBall.2 zero_le_one) (continuous_norm.comp_continuousOn hG'c)
  have hc : 0 < ‖deriv G η0‖ := norm_pos_iff.2 (hne η0 (hcl1 hη0))
  have hcG : ∀ η ∈ ball (0 : ℂ) 1, ‖deriv G η0‖ ≤ ‖deriv G η‖ := fun η hη =>
    hmin (ball_subset_closedBall hη)
  have hv : MemLp (u ∘ G) 2 (volume.restrict (ball 0 1)) :=
    memLp_comp_holomorphic isOpen_ball (hG.mono hD1) (hinj.mono hD1) hc hcG hum hu
  have hdw : DiskWeak ρw k (u ∘ G) := by
    intro W' Wt hW'o hW'sub hWt hWt0
    set V0 := G '' (B ∩ W')
    have hV0o : IsOpen V0 := isOpen_image_of_injOn hBo hBc hG hinj
      inter_subset_left (hBo.inter hW'o)
    have hV0sub : G '' closedBall 0 1 ⊆ V0 := image_mono (subset_inter hcl1 hW'sub)
    have hV0B : V0 ⊆ G '' B := image_mono inter_subset_left
    have hmaps : MapsTo g V0 W' := by
      rintro _ ⟨η, hη, rfl⟩; rw [hgG η hη.1]; exact hη.2
    have hws : ContDiffOn ℝ (⊤ : ℕ∞) (Wt ∘ g) V0 := hWt.comp (hgs.mono hV0B) hmaps
    have h0 := hw V0 (Wt ∘ g) hV0o hV0sub hws (by
      rintro _ ⟨η, hη, rfl⟩
      simp only [Function.comp_apply, hgG η (hcl1 (sphere_subset_closedBall hη))]
      exact hWt0 η hη)
    rw [integral_image_holomorphic isOpen_ball (hG.mono hD1) (hinj.mono hD1)] at h0
    refine Eq.trans ?_ h0
    refine setIntegral_congr_fun measurableSet_ball fun η hη => ?_
    have hηB := hD1 hη
    have hηW : η ∈ W' := hW'sub (ball_subset_closedBall hη)
    have hev : Wt =ᶠ[𝓝 η] (Wt ∘ g) ∘ G := by
      filter_upwards [(hBo.inter hW'o).mem_nhds ⟨hηB, hηW⟩] with y hy
      simp [Function.comp, hgG y hy.1]
    have hGη : G η ∈ V0 := ⟨η, ⟨hηB, hηW⟩, rfl⟩
    have hC2 : ContDiffAt ℝ 2 (Wt ∘ g) (G η) :=
      (hws.contDiffAt (hV0o.mem_nhds hGη)).of_le (by norm_cast)
    have hL := (InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds
    rw [laplacian_comp_holomorphic hBo hηB hG hC2] at hL
    simp only [Function.comp_apply, hgG η hηB] at hL ⊢
    rw [hL]
    ring
  obtain ⟨Φ, hΦ1, hΦint, hΦ0, hΦae⟩ := disk_weak_regularity hρ hρb hv hdw
  have hgC : ∀ z ∈ G '' B, ContDiffAt ℝ 2 g z := fun z hz =>
    (hgs.contDiffAt (hΩ1.mem_nhds hz)).of_le (by norm_cast)
  refine ⟨G '' B, Φ ∘ g, hΩ1, image_mono hcl1,
    hΦ1.comp_contDiffOn (hgs.of_le (by norm_cast)), ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨η, hη, rfl⟩
    have hΦη : ContDiffAt ℝ 2 Φ (g (G η)) := by rw [hgG η (hD1 hη)]; exact (hΦint η hη).1
    exact (hΦη.comp (G η) (hgC _ ⟨η, hD1 hη, rfl⟩)).contDiffWithinAt
  · rintro _ ⟨η, hη, rfl⟩
    have hηB := hD1 hη
    have hΦη : ContDiffAt ℝ 2 Φ (g (G η)) := by rw [hgG η hηB]; exact (hΦint η hη).1
    rw [laplacian_comp_holomorphic hΩ1 ⟨η, hηB, rfl⟩ hgd hΦη]
    simp only [Function.comp_apply, hgG η hηB]
    have hGd : HasDerivAt G (deriv G η) η := (hG.differentiableAt (hBo.mem_nhds hηB)).hasDerivAt
    have hgdd : HasDerivAt g (deriv g (G η)) (G η) :=
      (hgd.differentiableAt (hΩ1.mem_nhds ⟨η, hηB, rfl⟩)).hasDerivAt
    have hcomp := hgdd.comp η hGd
    have hid : HasDerivAt (g ∘ G) 1 η := by
      refine (hasDerivAt_id η).congr_of_eventuallyEq ?_
      filter_upwards [hBo.mem_nhds hηB] with y hy
      simp [hgG y hy]
    have h1 : deriv g (G η) * deriv G η = 1 := hcomp.unique hid
    have h2 : ‖deriv g (G η)‖ ^ 2 * ‖deriv G η‖ ^ 2 = 1 := by
      rw [← mul_pow, ← norm_mul, h1, norm_one, one_pow]
    have h3 := (hΦint η hη).2
    simp only [ρw] at h3
    linear_combination ‖deriv g (G η)‖ ^ 2 * h3 - k ^ 2 * Φ η * h2
  · rintro _ ⟨η, hη, rfl⟩
    simp only [Function.comp_apply, hgG η (hcl1 (sphere_subset_closedBall hη))]
    exact hΦ0 η hη
  · exact ae_image_holomorphic measurableSet_ball hΩ.measurableSet
      ((hG.mono hD1).restrictScalars ℝ) (fun η hη => hgG η (hD1 hη)) hΦae

lemma image_mul_ofReal_setOf {r : ℝ} (hr : 0 < r) (P : ℝ → Prop) :
    (fun η : ℂ => (r : ℂ) * η) '' {η | P ‖η‖} = {z | P (‖z‖ / r)} := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  ext z
  simp only [mem_image, mem_setOf_eq]
  constructor
  · rintro ⟨η, hη, rfl⟩
    rwa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      mul_div_cancel_left₀ _ hr.ne']
  · intro hz
    refine ⟨z / r, ?_, by field_simp⟩
    rwa [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

lemma image_mul_ofReal_ball {r : ℝ} (hr : 0 < r) :
    (fun η : ℂ => (r : ℂ) * η) '' ball 0 1 = ball 0 r := by
  have h := image_mul_ofReal_setOf hr (fun t => t < 1)
  have e1 : ball (0 : ℂ) 1 = {η | ‖η‖ < 1} := by ext; simp
  have e2 : ball (0 : ℂ) r = {z | ‖z‖ / r < 1} := by ext; simp [div_lt_one hr]
  rw [e1, e2, h]

lemma image_mul_ofReal_closedBall {r : ℝ} (hr : 0 < r) :
    (fun η : ℂ => (r : ℂ) * η) '' closedBall 0 1 = closedBall 0 r := by
  have h := image_mul_ofReal_setOf hr (fun t => t ≤ 1)
  have e1 : closedBall (0 : ℂ) 1 = {η | ‖η‖ ≤ 1} := by ext; simp
  have e2 : closedBall (0 : ℂ) r = {z | ‖z‖ / r ≤ 1} := by ext; simp [div_le_one hr]
  rw [e1, e2, h]

lemma image_mul_ofReal_sphere {r : ℝ} (hr : 0 < r) :
    (fun η : ℂ => (r : ℂ) * η) '' sphere 0 1 = sphere 0 r := by
  have h := image_mul_ofReal_setOf hr (fun t => t = 1)
  have e1 : sphere (0 : ℂ) 1 = {η | ‖η‖ = 1} := by ext; simp
  have e2 : sphere (0 : ℂ) r = {z | ‖z‖ / r = 1} := by ext; simp [div_eq_one_iff_eq hr.ne']
  rw [e1, e2, h]

lemma exists_scaled_ball_subset {U : Set ℂ} (hU : IsOpen U) {r : ℝ} (hr : 0 < r)
    (hDU : closedBall (0 : ℂ) r ⊆ U) : ∃ R0 > 1, ball (0 : ℂ) (r * R0) ⊆ U := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall (0 : ℂ) r).exists_thickening_subset_open hU hDU
  refine ⟨(r + δ) / r, by rw [gt_iff_lt, one_lt_div hr]; linarith, ?_⟩
  rw [mul_div_cancel₀ _ hr.ne', add_comm, ← thickening_closedBall hδ hr.le]
  exact hsub

/-- **Regularity of weak Dirichlet solutions** (proof of `weak_dirichlet_regularity`). -/
theorem weak_dirichlet_regularity_proof (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) {r : ℝ}
    (hr : 0 < r) (hDU : closedBall (0 : ℂ) r ⊆ U) (hF : DifferentiableOn ℂ F U)
    (hinj : InjOn F U) {k : ℝ} (u : ℂ → ℝ) (hu : MemLp u 2 (volume.restrict (F '' ball 0 r)))
    (hw : WeakDirichletHelmholtz F r k u) :
    ∃ (V : Set ℂ) (φ : ℂ → ℝ), IsOpen V ∧ F '' closedBall 0 r ⊆ V ∧ ContDiffOn ℝ 1 φ V ∧
      ContDiffOn ℝ 2 φ (F '' ball 0 r) ∧
      (∀ z ∈ F '' ball 0 r, Laplacian.laplacian φ z + k ^ 2 * φ z = 0) ∧
      (∀ z ∈ F '' sphere 0 r, φ z = 0) ∧ u =ᵐ[volume.restrict (F '' ball 0 r)] φ := by
  obtain ⟨R0, hR0, hsub⟩ := exists_scaled_ball_subset hU hr hDU
  set G : ℂ → ℂ := fun η => F (r * η)
  have himg : ∀ A : Set ℂ, G '' A = F '' ((fun η : ℂ => (r : ℂ) * η) '' A) := fun A =>
    (image_image F _ A).symm
  have hball : G '' ball 0 1 = F '' ball 0 r := by rw [himg, image_mul_ofReal_ball hr]
  have hcl : G '' closedBall 0 1 = F '' closedBall 0 r := by
    rw [himg, image_mul_ofReal_closedBall hr]
  have hsph : G '' sphere 0 1 = F '' sphere 0 r := by rw [himg, image_mul_ofReal_sphere hr]
  have hmaps : MapsTo (fun η : ℂ => (r : ℂ) * η) (ball 0 R0) U := by
    intro η hη
    apply hsub
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_lt_mul_of_pos_left (mem_ball_zero_iff.1 hη) hr
  have hG : DifferentiableOn ℂ G (ball 0 R0) :=
    hF.comp ((differentiable_id.const_mul (r : ℂ)).differentiableOn) hmaps
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hGinj : InjOn G (ball 0 R0) := fun a ha b hb hab =>
    mul_left_cancel₀ hr0 (hinj (hmaps ha) (hmaps hb) hab)
  -- a strongly measurable representative
  set ũ := hu.1.mk u
  have hue : u =ᵐ[volume.restrict (F '' ball 0 r)] ũ := hu.1.ae_eq_mk
  have hũ : MemLp ũ 2 (volume.restrict (G '' ball 0 1)) := by
    rw [hball]; exact hu.ae_eq hue
  have hwG : WeakDirichletHelmholtz G 1 k ũ := by
    intro W w hWo hWsub hws hw0
    rw [hcl] at hWsub
    rw [hsph] at hw0
    rw [hball, ← hw W w hWo hWsub hws hw0]
    refine integral_congr_ae ?_
    filter_upwards [hue] with z hz
    rw [hz]
  obtain ⟨V, φ, hVo, hVsub, h1, h2, h3, h4, h5⟩ :=
    conformal_weak_regularity hR0 hG hGinj hu.1.stronglyMeasurable_mk hũ hwG
  rw [hball] at h2 h3 h5
  rw [hcl] at hVsub
  rw [hsph] at h4
  exact ⟨V, φ, hVo, hVsub, h1, h2, h3, h4, hue.trans h5⟩

end

section

/-! ## Green's identity on the unit disk for functions with vanishing Cauchy data -/

open MeasureTheory Set Real Metric Filter Topology

/-- Radial cutoff, `0` for `1 - |z|² ≤ t`, `1` for `1 - |z|² ≥ 2t`. -/
def cutB (t : ℝ) (z : ℂ) : ℝ := Real.smoothTransition ((1 - ‖z‖ ^ 2) / t - 1)

/-- The boundary layer. -/
def annLayer (t : ℝ) : Set ℂ := {z | 1 - 2 * t ≤ ‖z‖ ^ 2 ∧ ‖z‖ ^ 2 ≤ 1}

lemma contDiff_cutB (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (cutB t) :=
  Real.smoothTransition.contDiff.comp
    (((contDiff_const.sub (contDiff_norm_sq ℝ)).div_const t).sub contDiff_const)

lemma cutB_eq_zero {t : ℝ} (ht : 0 < t) {z : ℂ} (h : 1 - ‖z‖ ^ 2 ≤ t) : cutB t z = 0 :=
  Real.smoothTransition.zero_of_nonpos (by rw [sub_nonpos, div_le_one ht]; exact h)

lemma cutB_eq_one {t : ℝ} (ht : 0 < t) {z : ℂ} (h : 2 * t ≤ 1 - ‖z‖ ^ 2) : cutB t z = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_sub_iff_add_le, le_div_iff₀ ht]; linarith)

lemma cutB_nonneg (t : ℝ) (z : ℂ) : 0 ≤ cutB t z := Real.smoothTransition.nonneg _

lemma cutB_le_one (t : ℝ) (z : ℂ) : cutB t z ≤ 1 := Real.smoothTransition.le_one _

lemma fderiv_cutB_eq_zero {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : z ∉ annLayer t) :
    fderiv ℝ (cutB t) z = 0 := by
  have hc : Continuous fun y : ℂ => 1 - ‖y‖ ^ 2 := continuous_const.sub (continuous_norm.pow 2)
  simp only [annLayer, mem_setOf_eq, not_and_or, not_le] at hz
  rcases hz with h | h
  · have hev : cutB t =ᶠ[𝓝 z] fun _ => 1 := by
      filter_upwards [(isOpen_lt continuous_const hc).mem_nhds
        (show 2 * t < 1 - ‖z‖ ^ 2 by linarith)] with y hy
      exact cutB_eq_one ht (le_of_lt hy)
    rw [hev.fderiv_eq]; simp
  · have hev : cutB t =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [(isOpen_lt hc continuous_const).mem_nhds
        (show 1 - ‖z‖ ^ 2 < t by linarith)] with y hy
      exact cutB_eq_zero ht (le_of_lt hy)
    rw [hev.fderiv_eq]; simp

/-- A bound for the derivative of the smooth transition function. -/
lemma exists_bound_deriv_smoothTransition :
    ∃ C, 0 ≤ C ∧ ∀ x, |deriv Real.smoothTransition x| ≤ C := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  have hs : HasCompactSupport (deriv Real.smoothTransition) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun x hx => ?_
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with h | h
    · have hev : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds h] with y hy
        exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
      rw [hev.deriv_eq, deriv_const]
    · have hev : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 1 := by
        filter_upwards [Ioi_mem_nhds h] with y hy
        exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
      rw [hev.deriv_eq, deriv_const]
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨C, (norm_nonneg _).trans (hC 0), fun x => by simpa using hC x⟩

lemma norm_fderiv_cutB_le {t : ℝ} (ht : 0 < t) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, |deriv Real.smoothTransition x| ≤ C) (z : ℂ) :
    ‖fderiv ℝ (cutB t) z‖ ≤ C * (2 * ‖z‖ / t) := by
  set q : ℂ → ℝ := fun y => (1 - ‖id y‖ ^ 2) * (1 / t) - 1
  have hq : HasFDerivAt q _ z :=
    ((((hasFDerivAt_id z).norm_sq).const_sub 1).mul_const (1 / t)).sub_const 1
  have hθ : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (q z)) (q z) :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) |>.differentiableAt
      |>.hasDerivAt
  have h := hθ.comp_hasFDerivAt z hq
  have e : cutB t = Real.smoothTransition ∘ q := by
    funext y; simp only [cutB, q, id, Function.comp_apply]; rw [← div_eq_mul_one_div]
  rw [e, h.fderiv, norm_smul, Real.norm_eq_abs]
  refine mul_le_mul (hC _) ?_ (norm_nonneg _) hC0
  rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h1 : ‖((innerSL ℝ) (id z)).comp (ContinuousLinearMap.id ℝ ℂ)‖ ≤ ‖z‖ := by
    refine ((innerSL ℝ (id z)).opNorm_comp_le _).trans ?_
    rw [innerSL_apply_norm]
    exact mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le
  have h2 : ‖(2 : ℕ) • ((innerSL ℝ) (id z)).comp (ContinuousLinearMap.id ℝ ℂ)‖ ≤ 2 * ‖z‖ := by
    rw [two_nsmul]
    refine (norm_add_le _ _).trans ?_
    linarith
  calc 1 / t * ‖(2 : ℕ) • ((innerSL ℝ) (id z)).comp (ContinuousLinearMap.id ℝ ℂ)‖
      ≤ 1 / t * (2 * ‖z‖) := by gcongr
    _ = 2 * ‖z‖ / t := by ring

lemma measurableSet_annLayer (t : ℝ) : MeasurableSet (annLayer t) :=
  (measurableSet_le measurable_const (measurable_norm.pow_const 2)).inter
    (measurableSet_le (measurable_norm.pow_const 2) measurable_const)

lemma volume_real_closedBall_zero {s : ℝ} (hs : 0 ≤ s) :
    volume.real (closedBall (0 : ℂ) s) = π * s ^ 2 := by
  simp [Measure.real, Complex.volume_closedBall, ENNReal.toReal_ofReal hs, mul_comm]

lemma volume_real_ball_zero {s : ℝ} (hs : 0 ≤ s) :
    volume.real (ball (0 : ℂ) s) = π * s ^ 2 := by
  simp [Measure.real, Complex.volume_ball, ENNReal.toReal_ofReal hs, mul_comm]

lemma volume_real_annLayer_le {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2) :
    volume.real (annLayer t) ≤ 2 * π * t := by
  set s := √(1 - 2 * t)
  have hsub : annLayer t ⊆ closedBall 0 1 \ ball 0 s := by
    rintro z ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall_zero_iff]
      nlinarith [norm_nonneg z]
    · rw [mem_ball_zero_iff, not_lt]
      calc s ≤ √(‖z‖ ^ 2) := Real.sqrt_le_sqrt h1
        _ = ‖z‖ := Real.sqrt_sq (norm_nonneg _)
  have hs1 : ball (0 : ℂ) s ⊆ closedBall 0 1 := by
    refine ball_subset_closedBall.trans (closedBall_subset_closedBall ?_)
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  calc volume.real (annLayer t) ≤ volume.real (closedBall (0 : ℂ) 1 \ ball 0 s) :=
        measureReal_mono hsub (measure_ne_top_of_subset diff_subset measure_closedBall_lt_top.ne)
    _ = volume.real (closedBall (0 : ℂ) 1) - volume.real (ball (0 : ℂ) s) :=
        measureReal_diff hs1 measurableSet_ball measure_closedBall_lt_top.ne
    _ = 2 * π * t := by
        rw [volume_real_closedBall_zero zero_le_one, volume_real_ball_zero (Real.sqrt_nonneg _),
          Real.sq_sqrt (by linarith)]
        ring

lemma abs_setIntegral_le_layer {g : ℂ → ℝ} {K t : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2)
    (hK : 0 ≤ K) (hgi : IntegrableOn g (ball 0 1)) (hg : ∀ z ∈ ball (0 : ℂ) 1, |g z| ≤ K)
    (hg0 : ∀ z ∈ ball (0 : ℂ) 1, z ∉ annLayer t → g z = 0) :
    |∫ z in ball (0 : ℂ) 1, g z| ≤ K * (2 * π * t) := by
  have hind : IntegrableOn ((annLayer t).indicator fun _ => K) (ball (0 : ℂ) 1) :=
    (integrableOn_const measure_ball_lt_top.ne).indicator (measurableSet_annLayer t)
  calc |∫ z in ball (0 : ℂ) 1, g z| ≤ ∫ z in ball (0 : ℂ) 1, |g z| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ z in ball (0 : ℂ) 1, (annLayer t).indicator (fun _ => K) z := by
        refine setIntegral_mono_on hgi.abs hind measurableSet_ball fun z hz => ?_
        by_cases hzA : z ∈ annLayer t
        · rw [indicator_of_mem hzA]; exact hg z hz
        · rw [indicator_of_notMem hzA, hg0 z hz hzA, abs_zero]
    _ = K * volume.real (annLayer t ∩ ball 0 1) := by
        rw [integral_indicator_const _ (measurableSet_annLayer t), smul_eq_mul, mul_comm,
          measureReal_restrict_apply (measurableSet_annLayer t)]
    _ ≤ K * (2 * π * t) := by
        gcongr
        have hfin : volume (annLayer t) ≠ ⊤ := by
          have hsub : annLayer t ⊆ closedBall (0 : ℂ) 1 := fun z hz => by
            rw [mem_closedBall_zero_iff]; nlinarith [norm_nonneg z, hz.2]
          exact ne_top_of_le_ne_top
            (measure_closedBall_lt_top (μ := volume) (x := (0 : ℂ)) (r := 1)).ne
            (measure_mono hsub)
        exact (measureReal_mono inter_subset_left hfin).trans (volume_real_annLayer_le ht ht2)

/-- The integral of a directional derivative of a compactly supported `C¹` function vanishes. -/
lemma integral_fderiv_apply_eq_zero {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (v : ℂ) : ∫ x, fderiv ℝ g x v = 0 := by
  have hd : Continuous fun x => fderiv ℝ g x v :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdc : HasCompactSupport fun x => fderiv ℝ g x v :=
    (hgc.fderiv (𝕜 := ℝ)).comp_left (g := fun T : ℂ →L[ℝ] ℝ => T v) (by simp)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : ℂ => (1 : ℝ)) (g := g) (v := v) (by simp)
    (by simpa using hd.integrable_of_hasCompactSupport hdc)
    (by simpa using hg.continuous.integrable_of_hasCompactSupport hgc)
    (differentiable_const _) (hg.differentiable (by norm_num))
  simpa using h

/-- The Green current `Ψ ∂_v W - W ∂_v Ψ`. -/
def greenJ (Ψ W : ℂ → ℝ) (v z : ℂ) : ℝ := Ψ z * fderiv ℝ W z v - W z * fderiv ℝ Ψ z v

lemma hasFDerivAt_fderiv_apply {f : ℂ → ℝ} {z : ℂ} (hf : ContDiffAt ℝ 2 f z) (v : ℂ) :
    HasFDerivAt (fun y => fderiv ℝ f y v) ((fderiv ℝ (fderiv ℝ f) z).flip v) z := by
  have h := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have := h.clm_apply (hasFDerivAt_const v z)
  simpa using this

lemma greenJ_contDiffAt {Ψ W : ℂ → ℝ} {z : ℂ} (hΨ : ContDiffAt ℝ 2 Ψ z)
    (hW : ContDiffAt ℝ 2 W z) (v : ℂ) : ContDiffAt ℝ 1 (greenJ Ψ W v) z := by
  have hΨ1 : ContDiffAt ℝ 1 (fun y => fderiv ℝ Ψ y v) z :=
    (hΨ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have hW1 : ContDiffAt ℝ 1 (fun y => fderiv ℝ W y v) z :=
    (hW.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  exact ((hΨ.of_le (by norm_num)).mul hW1).sub ((hW.of_le (by norm_num)).mul hΨ1)

lemma fderiv_greenJ_apply {Ψ W : ℂ → ℝ} {z : ℂ} (hΨ : ContDiffAt ℝ 2 Ψ z)
    (hW : ContDiffAt ℝ 2 W z) (v : ℂ) :
    fderiv ℝ (greenJ Ψ W v) z v =
      Ψ z * fderiv ℝ (fderiv ℝ W) z v v - W z * fderiv ℝ (fderiv ℝ Ψ) z v v := by
  have hΨd := (hΨ.differentiableAt (by norm_num)).hasFDerivAt
  have hWd := (hW.differentiableAt (by norm_num)).hasFDerivAt
  have h := (hΨd.mul (hasFDerivAt_fderiv_apply hW v)).sub
    (hWd.mul (hasFDerivAt_fderiv_apply hΨ v))
  have e : greenJ Ψ W v = (Ψ * fun y => fderiv ℝ W y v) - W * fun y => fderiv ℝ Ψ y v := rfl
  rw [e, h.fderiv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
  ring

lemma cutB_eventually_zero {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : 1 ≤ ‖z‖) :
    cutB t =ᶠ[𝓝 z] fun _ => 0 := by
  have hc : Continuous fun y : ℂ => 1 - ‖y‖ ^ 2 := continuous_const.sub (continuous_norm.pow 2)
  filter_upwards [(isOpen_lt hc continuous_const).mem_nhds
    (show 1 - ‖z‖ ^ 2 < t by nlinarith)] with y hy
  exact cutB_eq_zero ht (le_of_lt hy)

/-- **Divergence identity** for a cut-off vector field `(P 1, P I)`. -/
lemma integral_div_cutB {t : ℝ} (ht : 0 < t) {P : ℂ → ℂ → ℝ}
    (hP : ∀ v, ∀ z ∈ ball (0 : ℂ) 1, ContDiffAt ℝ 1 (P v) z) :
    ∫ z in ball (0 : ℂ) 1, (fderiv ℝ (cutB t) z 1 * P 1 z +
      fderiv ℝ (cutB t) z Complex.I * P Complex.I z +
      cutB t z * (fderiv ℝ (P 1) z 1 + fderiv ℝ (P Complex.I) z Complex.I)) = 0 := by
  set Fv : ℂ → ℂ → ℝ := fun v z => cutB t z * P v z
  have hzero : ∀ v z, 1 ≤ ‖z‖ → Fv v =ᶠ[𝓝 z] fun _ => 0 := fun v z hz => by
    filter_upwards [cutB_eventually_zero ht hz] with y hy
    simp [Fv, hy]
  have hC1 : ∀ v, ContDiff ℝ 1 (Fv v) := fun v => by
    refine contDiff_iff_contDiffAt.2 fun z => ?_
    by_cases hz : z ∈ ball (0 : ℂ) 1
    · exact ((contDiff_cutB t).contDiffAt.of_le (by norm_cast)).mul (hP v z hz)
    · exact contDiffAt_const.congr_of_eventuallyEq
        (hzero v z (by simpa [mem_ball_zero_iff] using hz))
  have hcs : ∀ v, HasCompactSupport (Fv v) := fun v =>
    HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) 1) fun z hz =>
      (hzero v z (by rw [mem_closedBall_zero_iff, not_le] at hz; exact hz.le)).self_of_nhds
  have hint : ∀ v w, Integrable fun x => fderiv ℝ (Fv v) x w := fun v w =>
    ((hC1 v).continuous_fderiv (by norm_num) |>.clm_apply continuous_const).integrable_of_hasCompactSupport
      ((hcs v).fderiv (𝕜 := ℝ) |>.comp_left (g := fun T : ℂ →L[ℝ] ℝ => T w) (by simp))
  have hsum : ∫ z, (fderiv ℝ (Fv 1) z 1 + fderiv ℝ (Fv Complex.I) z Complex.I) = 0 := by
    rw [integral_add (hint 1 1) (hint _ _), integral_fderiv_apply_eq_zero (hC1 1) (hcs 1),
      integral_fderiv_apply_eq_zero (hC1 _) (hcs _), add_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ball (0 : ℂ) 1)] at hsum
  · rw [← hsum]
    refine setIntegral_congr_fun measurableSet_ball fun z hz => ?_
    have hβ := ((contDiff_cutB t).differentiable (by norm_cast)).differentiableAt
      (x := z) |>.hasFDerivAt
    have hd : ∀ v, fderiv ℝ (Fv v) z v =
        fderiv ℝ (cutB t) z v * P v z + cutB t z * fderiv ℝ (P v) z v := by
      intro v
      have hJ := ((hP v z hz).differentiableAt (by norm_num)).hasFDerivAt
      have e2 : Fv v = cutB t * P v := rfl
      rw [e2, (hβ.mul hJ).fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    simp only [hd]
    ring
  · intro z hz
    have hz1 : 1 ≤ ‖z‖ := by simpa [mem_ball_zero_iff] using hz
    rw [(hzero 1 z hz1).fderiv_eq, (hzero Complex.I z hz1).fderiv_eq]
    simp

lemma continuousOn_greenJ {O : Set ℂ} (hO : IsOpen O) {Ψ W : ℂ → ℝ} (hΨ1 : ContDiffOn ℝ 1 Ψ O)
    (hW1 : ContDiffOn ℝ 1 W O) (v : ℂ) : ContinuousOn (greenJ Ψ W v) O := by
  have h1 : ContinuousOn (fun y => fderiv ℝ W y v) O :=
    (hW1.continuousOn_fderiv_of_isOpen hO le_rfl).clm_apply continuousOn_const
  have h2 : ContinuousOn (fun y => fderiv ℝ Ψ y v) O :=
    (hΨ1.continuousOn_fderiv_of_isOpen hO le_rfl).clm_apply continuousOn_const
  exact (hΨ1.continuousOn.mul h1).sub (hW1.continuousOn.mul h2)

/-- A function continuous on `𝔻̄` and vanishing on `𝕋` is small near `𝕋`. -/
lemma small_near_sphere {f : ℂ → ℝ} (hc : ContinuousOn f (closedBall 0 1))
    (h0 : ∀ z ∈ sphere (0 : ℂ) 1, f z = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z : ℂ, ‖z‖ ≤ 1 → 1 - δ < ‖z‖ → |f z| ≤ ε := by
  have huc := (isCompact_closedBall (0 : ℂ) 1).uniformContinuousOn_of_continuous hc
  obtain ⟨δ, hδ, hδc⟩ := Metric.uniformContinuousOn_iff.1 huc ε hε
  refine ⟨min δ (1 / 2), lt_min hδ (by norm_num), fun z hz1 hz2 => ?_⟩
  have hzpos : 0 < ‖z‖ := by linarith [min_le_right δ (1 / 2)]
  set w := z / (‖z‖ : ℂ)
  have hnorm : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hzpos.ne'
  have hw : ‖w‖ = 1 := by
    simp only [w, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    exact div_self hzpos.ne'
  have hJw : f w = 0 := h0 w (by simpa using hw)
  have hdist : dist z w < δ := by
    rw [dist_eq_norm]
    have : z - w = z * (1 - 1 / (‖z‖ : ℂ)) := by simp only [w]; field_simp
    rw [this, norm_mul]
    have e : (1 : ℂ) - 1 / (‖z‖ : ℂ) = ((1 - 1 / ‖z‖ : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos]
    · have : ‖z‖ * -(1 - 1 / ‖z‖) = 1 - ‖z‖ := by field_simp; ring
      rw [this]; linarith [min_le_left δ (1 / 2)]
    · rw [sub_nonpos, le_div_iff₀ hzpos]; linarith
  have h := hδc z (by simpa using hz1) w (by simp [hw]) hdist
  rw [hJw, Real.dist_eq, sub_zero] at h
  exact h.le

lemma exists_bound_closedBall {f : ℂ → ℝ} (hf : ContinuousOn f (closedBall 0 1)) :
    ∃ A, 0 ≤ A ∧ ∀ z ∈ closedBall (0 : ℂ) 1, |f z| ≤ A := by
  obtain ⟨A, hA⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hf
  exact ⟨A, (norm_nonneg _).trans (hA 0 (mem_closedBall_self zero_le_one)),
    fun z hz => by simpa using hA z hz⟩

lemma continuousOn_laplacian_of_contDiffOn {f : ℂ → ℝ} {O : Set ℂ} (hO : IsOpen O)
    (hf : ContDiffOn ℝ 2 f O) : ContinuousOn (Laplacian.laplacian f) O := by
  have h2 : ContinuousOn (fderiv ℝ (fderiv ℝ f)) O :=
    (hf.fderiv_of_isOpen hO (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hO le_rfl
  have e : Laplacian.laplacian f = fun z => fderiv ℝ (fderiv ℝ f) z 1 1 +
      fderiv ℝ (fderiv ℝ f) z Complex.I Complex.I := by
    funext z; exact laplacian_eq_fderiv_fderiv_real f z
  rw [e]
  exact ((h2.clm_apply continuousOn_const).clm_apply continuousOn_const).add
    ((h2.clm_apply continuousOn_const).clm_apply continuousOn_const)

lemma eq_zero_of_abs_le_mul_all {x c : ℝ} (hc : 0 ≤ c) (h : ∀ ε > 0, |x| ≤ c * ε) : x = 0 := by
  by_contra hx
  have hxp : 0 < |x| := abs_pos.2 hx
  have := h (|x| / (c + 1)) (by positivity)
  rw [mul_div_assoc', le_div_iff₀ (by positivity)] at this
  nlinarith

/-- **Divergence theorem on the disk** for a field vanishing on the boundary: if `P 1, P I` are
`C¹` in `𝔻`, continuous on `𝔻̄`, vanish on `𝕋`, and have bounded divergence, then the integral
of the divergence over `𝔻` vanishes. -/
theorem integral_div_disk_zero {P : ℂ → ℂ → ℝ}
    (hP1 : ∀ v, ∀ z ∈ ball (0 : ℂ) 1, ContDiffAt ℝ 1 (P v) z)
    (hPc : ∀ v, ContinuousOn (P v) (closedBall 0 1))
    (hP0 : ∀ v, ∀ z ∈ sphere (0 : ℂ) 1, P v z = 0) {K : ℝ}
    (hD : ∀ z ∈ ball (0 : ℂ) 1,
      |fderiv ℝ (P 1) z 1 + fderiv ℝ (P Complex.I) z Complex.I| ≤ K) :
    ∫ z in ball (0 : ℂ) 1, (fderiv ℝ (P 1) z 1 + fderiv ℝ (P Complex.I) z Complex.I) = 0 := by
  set D := ball (0 : ℂ) 1
  set E : ℂ → ℝ := fun z => fderiv ℝ (P 1) z 1 + fderiv ℝ (P Complex.I) z Complex.I
  have hDcl : D ⊆ closedBall 0 1 := ball_subset_closedBall
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hD 0 (mem_ball_self one_pos))
  have hdc : ∀ v w, ContinuousOn (fun z => fderiv ℝ (P v) z w) D := fun v w z hz =>
    (((hP1 v z hz).continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const).continuousWithinAt
  have hEc : ContinuousOn E D := (hdc 1 1).add (hdc _ _)
  have hbdd : ∀ {g : ℂ → ℝ} {K' : ℝ}, ContinuousOn g D → (∀ z ∈ D, |g z| ≤ K') →
      IntegrableOn g D := fun hg hgb =>
    Integrable.of_bound (hg.aestronglyMeasurable measurableSet_ball) _
      (by filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
          simpa using hgb z hz)
  have hEi : IntegrableOn E D := hbdd hEc hD
  obtain ⟨C, hC0, hC⟩ := exists_bound_deriv_smoothTransition
  have hβc : ∀ t, Continuous (cutB t) := fun t => (contDiff_cutB t).continuous
  have hdβc : ∀ t v, Continuous fun z => fderiv ℝ (cutB t) z v := fun t v =>
    ((contDiff_cutB t).continuous_fderiv (by norm_cast)).clm_apply continuous_const
  refine eq_zero_of_abs_le_mul_all (c := K * 2 * π + 8 * π * C) (by positivity) fun ε hε => ?_
  obtain ⟨δ1, hδ1, h1⟩ := small_near_sphere (hPc 1) (hP0 1) hε
  obtain ⟨δ2, hδ2, h2⟩ := small_near_sphere (hPc Complex.I) (hP0 Complex.I) hε
  set t := min (min (1 / 4) (min δ1 δ2 / 4)) ε
  have ht : 0 < t := lt_min (lt_min (by norm_num) (by positivity)) hε
  have ht2 : t ≤ 1 / 2 := (min_le_left _ _).trans ((min_le_left _ _).trans (by norm_num))
  have htε : t ≤ ε := min_le_right _ _
  have htδ : t ≤ min δ1 δ2 / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hdiv := integral_div_cutB ht hP1
  set B1 : ℂ → ℝ := fun z => fderiv ℝ (cutB t) z 1 * P 1 z +
    fderiv ℝ (cutB t) z Complex.I * P Complex.I z
  have hB1c : ContinuousOn B1 D :=
    (((hdβc t 1).continuousOn).mul ((hPc 1).mono hDcl)).add
      (((hdβc t _).continuousOn).mul ((hPc _).mono hDcl))
  have hdβ : ∀ z ∈ D, ∀ v : ℂ, ‖v‖ = 1 → |fderiv ℝ (cutB t) z v| ≤ 2 * C / t := by
    intro z hz v hv
    have h := norm_fderiv_cutB_le ht hC0 hC z
    calc |fderiv ℝ (cutB t) z v| ≤ ‖fderiv ℝ (cutB t) z‖ * ‖v‖ := by
          rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * (2 * ‖z‖ / t) * 1 := by rw [hv]; gcongr
      _ ≤ 2 * C / t := by
          have : ‖z‖ ≤ 1 := (mem_ball_zero_iff.1 hz).le
          rw [mul_one, mul_div_assoc', div_le_div_iff_of_pos_right ht]
          nlinarith
  have hJsmall : ∀ z ∈ D, z ∈ annLayer t → |P 1 z| ≤ ε ∧ |P Complex.I z| ≤ ε := by
    intro z hz hzA
    have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.1 hz).le
    have hlay : 1 - ‖z‖ ≤ 2 * t := by nlinarith [hzA.1, norm_nonneg z]
    have hδ : 2 * t < min δ1 δ2 := by linarith [lt_min hδ1 hδ2]
    exact ⟨h1 z hz1 (by linarith [min_le_left δ1 δ2]),
      h2 z hz1 (by linarith [min_le_right δ1 δ2])⟩
  have hB1b : ∀ z ∈ D, |B1 z| ≤ 2 * (2 * C / t * ε) := by
    intro z hz
    by_cases hzA : z ∈ annLayer t
    · obtain ⟨hj1, hj2⟩ := hJsmall z hz hzA
      simp only [B1]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, two_mul]
      exact add_le_add (mul_le_mul (hdβ z hz 1 (by simp)) hj1 (abs_nonneg _) (by positivity))
        (mul_le_mul (hdβ z hz _ (by simp)) hj2 (abs_nonneg _) (by positivity))
    · simp [B1, fderiv_cutB_eq_zero ht hzA]; positivity
  have hB1i : IntegrableOn B1 D := hbdd hB1c hB1b
  have hβEi : IntegrableOn (fun z => cutB t z * E z) D :=
    hbdd ((hβc t).continuousOn.mul hEc) (K' := K) fun z hz => by
      rw [abs_mul, abs_of_nonneg (cutB_nonneg t z)]
      exact (mul_le_of_le_one_left (abs_nonneg _) (cutB_le_one t z)).trans (hD z hz)
  have hsplit : ∫ z in D, E z = (∫ z in D, (1 - cutB t z) * E z) - ∫ z in D, B1 z := by
    have e1 : ∫ z in D, (B1 z + cutB t z * E z) = 0 := hdiv
    rw [integral_add hB1i hβEi] at e1
    have e2 : ∫ z in D, (1 - cutB t z) * E z = ∫ z in D, (E z - cutB t z * E z) := by
      congr 1; funext z; ring
    rw [integral_sub hEi hβEi] at e2
    rw [e2]
    linear_combination e1
  have hI1 : |∫ z in D, (1 - cutB t z) * E z| ≤ K * (2 * π * t) := by
    refine abs_setIntegral_le_layer ht ht2 hK0 (hEi.sub hβEi |>.congr ?_) ?_ ?_
    · filter_upwards with z; simp only [Pi.sub_apply]; ring
    · intro z hz
      rw [abs_mul, abs_of_nonneg (by linarith [cutB_le_one t z])]
      exact (mul_le_of_le_one_left (abs_nonneg _) (by linarith [cutB_nonneg t z])).trans
        (hD z hz)
    · intro z hz hzA
      have hz1 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [(mem_ball_zero_iff.1 hz).le, norm_nonneg z]
      simp only [annLayer, mem_setOf_eq, not_and_or, not_le] at hzA
      rcases hzA with h | h
      · rw [cutB_eq_one ht (by linarith), sub_self, zero_mul]
      · linarith
  have hI2 : |∫ z in D, B1 z| ≤ 2 * (2 * C / t * ε) * (2 * π * t) :=
    abs_setIntegral_le_layer ht ht2 (by positivity) hB1i hB1b
      (fun z _ hzA => by simp [B1, fderiv_cutB_eq_zero ht hzA])
  rw [hsplit]
  have hab := abs_sub (∫ z in D, (1 - cutB t z) * E z) (∫ z in D, B1 z)
  have e3 : 2 * (2 * C / t * ε) * (2 * π * t) = 8 * π * C * ε := by field_simp; ring
  rw [e3] at hI2
  have : K * (2 * π * t) ≤ K * 2 * π * ε := by
    have := mul_le_mul_of_nonneg_left htε (show 0 ≤ K * 2 * π by positivity)
    linarith
  nlinarith

/-- **Green's second identity on the disk** when the Green current vanishes on `𝕋`. -/
theorem integral_green_disk_zero' {O : Set ℂ} (hO : IsOpen O) (hDO : closedBall (0 : ℂ) 1 ⊆ O)
    {Ψ W : ℂ → ℝ} (hΨ1 : ContDiffOn ℝ 1 Ψ O) (hΨ2 : ContDiffOn ℝ 2 Ψ (ball 0 1))
    (hW : ContDiffOn ℝ 2 W O) {M : ℝ}
    (hΔΨ : ∀ z ∈ ball (0 : ℂ) 1, |Laplacian.laplacian Ψ z| ≤ M)
    (hJ0 : ∀ v, ∀ z ∈ sphere (0 : ℂ) 1, greenJ Ψ W v z = 0) :
    ∫ z in ball (0 : ℂ) 1, (Ψ z * Laplacian.laplacian W z - W z * Laplacian.laplacian Ψ z) =
      0 := by
  have hDcl : ball (0 : ℂ) 1 ⊆ closedBall 0 1 := ball_subset_closedBall
  have hΨD : ∀ z ∈ ball (0 : ℂ) 1, ContDiffAt ℝ 2 Ψ z := fun z hz =>
    hΨ2.contDiffAt (isOpen_ball.mem_nhds hz)
  have hWD : ∀ z ∈ ball (0 : ℂ) 1, ContDiffAt ℝ 2 W z := fun z hz =>
    hW.contDiffAt (hO.mem_nhds (hDO (hDcl hz)))
  have hW1 : ContDiffOn ℝ 1 W O := hW.of_le (by norm_num)
  have hdiv : ∀ z ∈ ball (0 : ℂ) 1, fderiv ℝ (greenJ Ψ W 1) z 1 +
      fderiv ℝ (greenJ Ψ W Complex.I) z Complex.I =
      Ψ z * Laplacian.laplacian W z - W z * Laplacian.laplacian Ψ z := by
    intro z hz
    rw [fderiv_greenJ_apply (hΨD z hz) (hWD z hz), fderiv_greenJ_apply (hΨD z hz) (hWD z hz),
      laplacian_eq_fderiv_fderiv_real W, laplacian_eq_fderiv_fderiv_real Ψ]
    ring
  obtain ⟨AΨ, hAΨ0, hAΨ⟩ := exists_bound_closedBall (hΨ1.continuousOn.mono hDO)
  obtain ⟨AW, hAW0, hAW⟩ := exists_bound_closedBall (hW1.continuousOn.mono hDO)
  obtain ⟨AL, hAL0, hAL⟩ :=
    exists_bound_closedBall ((continuousOn_laplacian_of_contDiffOn hO hW).mono hDO)
  rw [← setIntegral_congr_fun measurableSet_ball hdiv]
  refine integral_div_disk_zero (fun v z hz => greenJ_contDiffAt (hΨD z hz) (hWD z hz) v)
    (fun v => (continuousOn_greenJ hO hΨ1 hW1 v).mono hDO) hJ0 (K := AΨ * AL + AW * M)
    fun z hz => ?_
  rw [hdiv z hz]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul]
  exact add_le_add (mul_le_mul (hAΨ z (hDcl hz)) (hAL z (hDcl hz)) (abs_nonneg _) hAΨ0)
    (mul_le_mul (hAW z (hDcl hz)) (hΔΨ z hz) (abs_nonneg _) hAW0)

/-- **Green's identity on the disk for vanishing Cauchy data.** -/
theorem integral_green_disk_zero {O : Set ℂ} (hO : IsOpen O) (hDO : closedBall (0 : ℂ) 1 ⊆ O)
    {Ψ W : ℂ → ℝ} (hΨ1 : ContDiffOn ℝ 1 Ψ O) (hΨ2 : ContDiffOn ℝ 2 Ψ (ball 0 1))
    (hW : ContDiffOn ℝ 2 W O) {M : ℝ}
    (hΔΨ : ∀ z ∈ ball (0 : ℂ) 1, |Laplacian.laplacian Ψ z| ≤ M)
    (h0 : ∀ z ∈ sphere (0 : ℂ) 1, Ψ z = 0 ∧ fderiv ℝ Ψ z = 0) :
    ∫ z in ball (0 : ℂ) 1, (Ψ z * Laplacian.laplacian W z - W z * Laplacian.laplacian Ψ z) =
      0 :=
  integral_green_disk_zero' hO hDO hΨ1 hΨ2 hW hΔΨ fun v z hz => by
    obtain ⟨a, b⟩ := h0 z hz
    simp [greenJ, a, b]

/-- **Green's second identity on the disk** for two functions vanishing on `𝕋`. -/
theorem integral_green_disk_dirichlet {O : Set ℂ} (hO : IsOpen O)
    (hDO : closedBall (0 : ℂ) 1 ⊆ O) {Ψ W : ℂ → ℝ} (hΨ1 : ContDiffOn ℝ 1 Ψ O)
    (hΨ2 : ContDiffOn ℝ 2 Ψ (ball 0 1)) (hW : ContDiffOn ℝ 2 W O) {M : ℝ}
    (hΔΨ : ∀ z ∈ ball (0 : ℂ) 1, |Laplacian.laplacian Ψ z| ≤ M)
    (hΨ0 : ∀ z ∈ sphere (0 : ℂ) 1, Ψ z = 0) (hW0 : ∀ z ∈ sphere (0 : ℂ) 1, W z = 0) :
    ∫ z in ball (0 : ℂ) 1, (Ψ z * Laplacian.laplacian W z - W z * Laplacian.laplacian Ψ z) =
      0 :=
  integral_green_disk_zero' hO hDO hΨ1 hΨ2 hW hΔΨ fun v z hz => by
    simp [greenJ, hΨ0 z hz, hW0 z hz]

/-- The squared norm of a real functional on `ℂ`. -/
lemma norm_clm_sq (L : ℂ →L[ℝ] ℝ) : ‖L‖ ^ 2 = L 1 ^ 2 + L Complex.I ^ 2 := by
  set r := √(L 1 ^ 2 + L Complex.I ^ 2)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hle : ‖L‖ ≤ r := by
    refine L.opNorm_le_bound hr0 fun v => ?_
    rw [clm_apply_eq_re_im L v, Real.norm_eq_abs]
    have h1 : |v.re * L 1 + v.im * L Complex.I| ≤ √(v.re ^ 2 + v.im ^ 2) * r := by
      rw [← Real.sqrt_mul (by positivity)]
      apply Real.abs_le_sqrt
      nlinarith [sq_nonneg (v.re * L Complex.I - v.im * L 1)]
    have h2 : √(v.re ^ 2 + v.im ^ 2) = ‖v‖ := by
      rw [Complex.norm_eq_sqrt_sq_add_sq]
    rw [h2] at h1; rwa [mul_comm r]
  have hge : r ≤ ‖L‖ := by
    by_cases hr : r = 0
    · rw [hr]; exact norm_nonneg _
    have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    set v : ℂ := ⟨L 1 / r, L Complex.I / r⟩
    have hv : ‖v‖ = 1 := by
      rw [Complex.norm_eq_sqrt_sq_add_sq]
      simp only [v, div_pow]
      rw [← add_div, ← Real.sq_sqrt (show 0 ≤ L 1 ^ 2 + L Complex.I ^ 2 by positivity)]
      rw [div_self (by positivity), Real.sqrt_one]
    have h := L.le_opNorm v
    rw [hv, mul_one, clm_apply_eq_re_im L v, Real.norm_eq_abs] at h
    simp only [v] at h
    have : L 1 / r * L 1 + L Complex.I / r * L Complex.I = r := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, ← sq, ← sq,
        ← Real.sq_sqrt (show 0 ≤ L 1 ^ 2 + L Complex.I ^ 2 by positivity)]
      field_simp
      rfl
    rw [this, abs_of_pos hrpos] at h
    exact h
  rw [le_antisymm hle hge, Real.sq_sqrt (by positivity)]

/-- **Green's first identity on the disk** for a function vanishing on `𝕋`. -/
theorem integral_first_green_disk {O : Set ℂ} (hO : IsOpen O) (hDO : closedBall (0 : ℂ) 1 ⊆ O)
    {W : ℂ → ℝ} (hW : ContDiffOn ℝ 2 W O) (hW0 : ∀ z ∈ sphere (0 : ℂ) 1, W z = 0) :
    ∫ z in ball (0 : ℂ) 1, ‖fderiv ℝ W z‖ ^ 2 = -∫ z in ball (0 : ℂ) 1, W z * Laplacian.laplacian W z := by
  have hDcl : ball (0 : ℂ) 1 ⊆ closedBall 0 1 := ball_subset_closedBall
  have hWD : ∀ z ∈ ball (0 : ℂ) 1, ContDiffAt ℝ 2 W z := fun z hz =>
    hW.contDiffAt (hO.mem_nhds (hDO (hDcl hz)))
  have hW1 : ContDiffOn ℝ 1 W O := hW.of_le (by norm_num)
  set P : ℂ → ℂ → ℝ := fun v z => W z * fderiv ℝ W z v
  have hP1 : ∀ v, ∀ z ∈ ball (0 : ℂ) 1, ContDiffAt ℝ 1 (P v) z := fun v z hz =>
    ((hWD z hz).of_le (by norm_num)).mul
      (((hWD z hz).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const)
  have hfd : ∀ v, ∀ z ∈ ball (0 : ℂ) 1, fderiv ℝ (P v) z v =
      fderiv ℝ W z v * fderiv ℝ W z v + W z * fderiv ℝ (fderiv ℝ W) z v v := by
    intro v z hz
    have hWd := ((hWD z hz).differentiableAt (by norm_num)).hasFDerivAt
    have h := hWd.mul (hasFDerivAt_fderiv_apply (hWD z hz) v)
    have e : P v = W * fun y => fderiv ℝ W y v := rfl
    rw [e, h.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul]
    ring
  have hdiv : ∀ z ∈ ball (0 : ℂ) 1, fderiv ℝ (P 1) z 1 + fderiv ℝ (P Complex.I) z Complex.I =
      ‖fderiv ℝ W z‖ ^ 2 + W z * Laplacian.laplacian W z := by
    intro z hz
    rw [hfd 1 z hz, hfd _ z hz, norm_clm_sq, laplacian_eq_fderiv_fderiv_real W]
    ring
  have hPc : ∀ v, ContinuousOn (P v) (closedBall 0 1) := fun v =>
    (hW1.continuousOn.mul ((hW1.continuousOn_fderiv_of_isOpen hO le_rfl).clm_apply
      continuousOn_const)).mono hDO
  obtain ⟨AW, hAW0, hAW⟩ := exists_bound_closedBall (hW1.continuousOn.mono hDO)
  obtain ⟨AL, hAL0, hAL⟩ :=
    exists_bound_closedBall ((continuousOn_laplacian_of_contDiffOn hO hW).mono hDO)
  have hGc : ContinuousOn (fun z => ‖fderiv ℝ W z‖) (closedBall 0 1) :=
    ((hW1.continuousOn_fderiv_of_isOpen hO le_rfl).norm).mono hDO
  obtain ⟨AG, hAG0, hAG⟩ := exists_bound_closedBall hGc
  have h0 := integral_div_disk_zero hP1 hPc (fun v z hz => by simp [P, hW0 z hz])
    (K := AG ^ 2 + AW * AL) fun z hz => by
      rw [hdiv z hz]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hAG z (hDcl hz)) 2
      · rw [abs_mul]
        exact mul_le_mul (hAW z (hDcl hz)) (hAL z (hDcl hz)) (abs_nonneg _) hAW0
  rw [setIntegral_congr_fun measurableSet_ball hdiv] at h0
  have hi1 : IntegrableOn (fun z => ‖fderiv ℝ W z‖ ^ 2) (ball (0 : ℂ) 1) :=
    Integrable.of_bound ((hGc.mono hDcl).pow 2 |>.aestronglyMeasurable measurableSet_ball)
      (AG ^ 2) (by
        filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hAG z (hDcl hz)) 2)
  have hi2 : IntegrableOn (fun z => W z * Laplacian.laplacian W z) (ball (0 : ℂ) 1) :=
    Integrable.of_bound (((hW1.continuousOn.mono (hDcl.trans hDO)).mul
      ((continuousOn_laplacian_of_contDiffOn hO hW).mono (hDcl.trans hDO))).aestronglyMeasurable
        measurableSet_ball) (AW * AL) (by
        filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hAW z (hDcl hz)) (hAL z (hDcl hz)) (abs_nonneg _) hAW0)
  rw [integral_add hi1 hi2] at h0
  linarith

end

section

/-! ## The Green form on the unit disk -/

open MeasureTheory Set Real Metric Filter Topology
open scoped ComplexConjugate InnerProductSpace

/-- Functions which are `C²` on a neighbourhood of `𝔻̄` and vanish on `𝕋`. -/
def DiskNice (w : ℂ → ℝ) : Prop :=
  ∃ O : Set ℂ, IsOpen O ∧ closedBall (0 : ℂ) 1 ⊆ O ∧ ContDiffOn ℝ 2 w O ∧
    ∀ z ∈ sphere (0 : ℂ) 1, w z = 0

/-- The pointwise inner product of two gradients. -/
def gradInner (L M : ℂ →L[ℝ] ℝ) : ℝ := L 1 * M 1 + L Complex.I * M Complex.I

lemma gradInner_self (L : ℂ →L[ℝ] ℝ) : gradInner L L = ‖L‖ ^ 2 := by
  rw [norm_clm_sq]; unfold gradInner; ring

lemma abs_gradInner_le (L M : ℂ →L[ℝ] ℝ) : |gradInner L M| ≤ 2 * (‖L‖ * ‖M‖) := by
  unfold gradInner
  have h1 : |L 1| ≤ ‖L‖ := by simpa using L.le_opNorm 1
  have h2 : |M 1| ≤ ‖M‖ := by simpa using M.le_opNorm 1
  have h3 : |L Complex.I| ≤ ‖L‖ := by simpa using L.le_opNorm Complex.I
  have h4 : |M Complex.I| ≤ ‖M‖ := by simpa using M.le_opNorm Complex.I
  calc |L 1 * M 1 + L Complex.I * M Complex.I| ≤ |L 1| * |M 1| + |L Complex.I| * |M Complex.I| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ ‖L‖ * ‖M‖ + ‖L‖ * ‖M‖ := add_le_add (mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _))
        (mul_le_mul h3 h4 (abs_nonneg _) (norm_nonneg _))
    _ = _ := by ring

namespace DiskNice

variable {w v : ℂ → ℝ}

lemma common (hw : DiskNice w) (hv : DiskNice v) :
    ∃ O : Set ℂ, IsOpen O ∧ closedBall (0 : ℂ) 1 ⊆ O ∧ ContDiffOn ℝ 2 w O ∧ ContDiffOn ℝ 2 v O := by
  obtain ⟨O, hO, hDO, hwO, -⟩ := hw
  obtain ⟨O', hO', hDO', hvO, -⟩ := hv
  exact ⟨O ∩ O', hO.inter hO', subset_inter hDO hDO', hwO.mono inter_subset_left,
    hvO.mono inter_subset_right⟩

lemma add (hw : DiskNice w) (hv : DiskNice v) : DiskNice (fun z => w z + v z) := by
  obtain ⟨O, hO, hDO, hwO, hvO⟩ := hw.common hv
  exact ⟨O, hO, hDO, hwO.add hvO, fun z hz => by simp [hw.choose_spec.2.2.2 z hz,
    hv.choose_spec.2.2.2 z hz]⟩

lemma smul (c : ℝ) (hw : DiskNice w) : DiskNice (fun z => c * w z) := by
  obtain ⟨O, hO, hDO, hwO, h0⟩ := hw
  exact ⟨O, hO, hDO, contDiffOn_const.mul hwO, fun z hz => by simp [h0 z hz]⟩

lemma continuousOn (hw : DiskNice w) : ContinuousOn w (closedBall 0 1) := by
  obtain ⟨O, hO, hDO, hwO, -⟩ := hw
  exact hwO.continuousOn.mono hDO

lemma laplacian_continuousOn (hw : DiskNice w) :
    ContinuousOn (Laplacian.laplacian w) (closedBall 0 1) := by
  obtain ⟨O, hO, hDO, hwO, -⟩ := hw
  exact (continuousOn_laplacian_of_contDiffOn hO hwO).mono hDO

lemma fderiv_continuousOn (hw : DiskNice w) :
    ContinuousOn (fderiv ℝ w) (closedBall 0 1) := by
  obtain ⟨O, hO, hDO, hwO, -⟩ := hw
  exact (hwO.continuousOn_fderiv_of_isOpen hO (by norm_num)).mono hDO

lemma contDiffAt (hw : DiskNice w) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    ContDiffAt ℝ 2 w z := by
  obtain ⟨O, hO, hDO, hwO, -⟩ := hw
  exact hwO.contDiffAt (hO.mem_nhds (hDO hz))

/-- **Green's second identity.** -/
theorem green_second (hw : DiskNice w) (hv : DiskNice v) :
    ∫ z in ball (0 : ℂ) 1, w z * Laplacian.laplacian v z =
      ∫ z in ball (0 : ℂ) 1, v z * Laplacian.laplacian w z := by
  obtain ⟨O, hO, hDO, hwO, hvO⟩ := hw.common hv
  obtain ⟨M, -, hM⟩ := exists_bound_closedBall hw.laplacian_continuousOn
  have h := integral_green_disk_dirichlet hO hDO (hwO.of_le (by norm_num))
    (hwO.mono (ball_subset_closedBall.trans hDO)) hvO (M := M)
    (fun z hz => hM z (ball_subset_closedBall hz)) hw.choose_spec.2.2.2 hv.choose_spec.2.2.2
  have i1 : IntegrableOn (fun z => w z * Laplacian.laplacian v z) (ball (0 : ℂ) 1) :=
    ((hw.continuousOn.mul hv.laplacian_continuousOn).integrableOn_compact
      (isCompact_closedBall 0 1)).mono_set ball_subset_closedBall
  have i2 : IntegrableOn (fun z => v z * Laplacian.laplacian w z) (ball (0 : ℂ) 1) :=
    ((hv.continuousOn.mul hw.laplacian_continuousOn).integrableOn_compact
      (isCompact_closedBall 0 1)).mono_set ball_subset_closedBall
  rw [integral_sub i1 i2] at h
  linarith

lemma integrableOn_ball_of_continuousOn {f : ℂ → ℝ} (hf : ContinuousOn f (closedBall 0 1)) :
    IntegrableOn f (ball (0 : ℂ) 1) :=
  (hf.integrableOn_compact (isCompact_closedBall 0 1)).mono_set ball_subset_closedBall

lemma setIntegral_lin3 {f g h : ℂ → ℝ} {s : Set ℂ} (hf : IntegrableOn f s)
    (hg : IntegrableOn g s) (hh : IntegrableOn h s) (a b : ℝ) :
    ∫ z in s, (f z + a * g z + b * h z) = (∫ z in s, f z) + a * (∫ z in s, g z) +
      b * ∫ z in s, h z := by
  have h1 : IntegrableOn (fun z => f z + a * g z) s := hf.add (hg.const_mul a)
  rw [integral_add h1 (hh.const_mul b), integral_add hf (hg.const_mul a), integral_const_mul,
    integral_const_mul]

lemma fderiv_add_of_mem (hw : DiskNice w) (hv : DiskNice v) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) 1) (c : ℝ) :
    fderiv ℝ (fun y => w y + c * v y) z = fderiv ℝ w z + c • fderiv ℝ v z := by
  have h1 := ((hw.contDiffAt hz).differentiableAt (by norm_num)).hasFDerivAt
  have h2 := ((hv.contDiffAt hz).differentiableAt (by norm_num)).hasFDerivAt
  exact (h1.add (h2.const_mul c)).fderiv

/-- **Green's first identity**, polarized. -/
theorem green_first (hw : DiskNice w) (hv : DiskNice v) :
    ∫ z in ball (0 : ℂ) 1, gradInner (fderiv ℝ w z) (fderiv ℝ v z) =
      -∫ z in ball (0 : ℂ) 1, w z * Laplacian.laplacian v z := by
  have hp := hw.add (hv.smul 1)
  have hm := hw.add (hv.smul (-1))
  have e1 : ∀ c : ℝ, ∫ z in ball (0 : ℂ) 1, ‖fderiv ℝ (fun y => w y + c * v y) z‖ ^ 2 =
      -∫ z in ball (0 : ℂ) 1, (w z + c * v z) *
        Laplacian.laplacian (fun y => w y + c * v y) z := by
    intro c
    obtain ⟨O, hO, hDO, hO2, h0⟩ := hw.add (hv.smul c)
    exact integral_first_green_disk hO hDO hO2 h0
  have hL : ∀ c : ℝ, ∀ z ∈ ball (0 : ℂ) 1, Laplacian.laplacian (fun y => w y + c * v y) z =
      Laplacian.laplacian w z + c * Laplacian.laplacian v z := by
    intro c z hz
    have := laplacian_lincomb 1 c (hw.contDiffAt (ball_subset_closedBall hz))
      (hv.contDiffAt (ball_subset_closedBall hz))
    simpa using this
  have hD : ∀ c : ℝ, ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ (fun y => w y + c * v y) z‖ ^ 2 =
      ‖fderiv ℝ w z‖ ^ 2 + 2 * c * gradInner (fderiv ℝ w z) (fderiv ℝ v z) +
        c ^ 2 * ‖fderiv ℝ v z‖ ^ 2 := by
    intro c z hz
    rw [fderiv_add_of_mem hw hv (ball_subset_closedBall hz), ← gradInner_self, ← gradInner_self,
      ← gradInner_self]
    simp only [gradInner, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    ring
  have e2 : ∀ c : ℝ, ∫ z in ball (0 : ℂ) 1, ‖fderiv ℝ (fun y => w y + c * v y) z‖ ^ 2 =
      (∫ z in ball (0 : ℂ) 1, ‖fderiv ℝ w z‖ ^ 2) +
        2 * c * (∫ z in ball (0 : ℂ) 1, gradInner (fderiv ℝ w z) (fderiv ℝ v z)) +
        c ^ 2 * ∫ z in ball (0 : ℂ) 1, ‖fderiv ℝ v z‖ ^ 2 := by
    intro c
    have iw := integrableOn_ball_of_continuousOn (hw.fderiv_continuousOn.norm.pow 2)
    have iv := integrableOn_ball_of_continuousOn (hv.fderiv_continuousOn.norm.pow 2)
    have ig : IntegrableOn (fun z => gradInner (fderiv ℝ w z) (fderiv ℝ v z)) (ball (0 : ℂ) 1) :=
      integrableOn_ball_of_continuousOn (by
        unfold gradInner
        exact ((hw.fderiv_continuousOn.clm_apply continuousOn_const).mul
          (hv.fderiv_continuousOn.clm_apply continuousOn_const)).add
          ((hw.fderiv_continuousOn.clm_apply continuousOn_const).mul
          (hv.fderiv_continuousOn.clm_apply continuousOn_const)))
    rw [setIntegral_congr_fun measurableSet_ball (hD c), setIntegral_lin3 iw ig iv]
  have e3 : ∀ c : ℝ, ∫ z in ball (0 : ℂ) 1, (w z + c * v z) *
        Laplacian.laplacian (fun y => w y + c * v y) z =
      (∫ z in ball (0 : ℂ) 1, w z * Laplacian.laplacian w z) +
        c * ((∫ z in ball (0 : ℂ) 1, w z * Laplacian.laplacian v z) +
          ∫ z in ball (0 : ℂ) 1, v z * Laplacian.laplacian w z) +
        c ^ 2 * ∫ z in ball (0 : ℂ) 1, v z * Laplacian.laplacian v z := by
    intro c
    have i1 := integrableOn_ball_of_continuousOn (hw.continuousOn.mul hw.laplacian_continuousOn)
    have i2 := integrableOn_ball_of_continuousOn (hw.continuousOn.mul hv.laplacian_continuousOn)
    have i3 := integrableOn_ball_of_continuousOn (hv.continuousOn.mul hw.laplacian_continuousOn)
    have i4 := integrableOn_ball_of_continuousOn (hv.continuousOn.mul hv.laplacian_continuousOn)
    have hpt : ∀ z ∈ ball (0 : ℂ) 1, (w z + c * v z) *
        Laplacian.laplacian (fun y => w y + c * v y) z =
        w z * Laplacian.laplacian w z + c * (w z * Laplacian.laplacian v z +
          v z * Laplacian.laplacian w z) + c ^ 2 * (v z * Laplacian.laplacian v z) := by
      intro z hz; rw [hL c z hz]; ring
    rw [setIntegral_congr_fun measurableSet_ball hpt,
      setIntegral_lin3 (f := fun z => w z * Laplacian.laplacian w z)
        (g := fun z => w z * Laplacian.laplacian v z + v z * Laplacian.laplacian w z)
        (h := fun z => v z * Laplacian.laplacian v z) i1 (i2.add i3) i4,
      integral_add (f := fun z => w z * Laplacian.laplacian v z)
        (g := fun z => v z * Laplacian.laplacian w z) i2 i3]
  have hs := hw.green_second hv
  have k1 := e1 1
  have k2 := e1 (-1)
  rw [e2, e3] at k1 k2
  linarith

end DiskNice

/-! ### Test functions on the disk -/

section Tests

variable {q : ℂ → ℝ}

lemma test_supp (hq : q ∈ testFunctions (ball (0 : ℂ) 1)) :
    ∃ ρ₀ : ℝ, 0 ≤ ρ₀ ∧ ρ₀ < 1 ∧ ∀ x, ρ₀ < ‖x‖ → q x = 0 := by
  obtain ⟨-, hc, hsub⟩ := hq
  obtain ⟨r, hr, hsr⟩ := exists_lt_subset_ball (isClosed_tsupport q) hsub
  refine ⟨max r 0, le_max_right _ _, max_lt hr one_pos, fun x hx => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun hm => ?_
  have := mem_ball_zero_iff.1 (hsr hm)
  linarith [le_max_left r 0]

lemma test_bddSupp (hq : q ∈ testFunctions (ball (0 : ℂ) 1)) :
    ∃ M ρ₀, 0 ≤ ρ₀ ∧ ρ₀ < 1 ∧ BddSupp q M ρ₀ := by
  obtain ⟨ρ₀, h0, h1, hs⟩ := test_supp hq
  obtain ⟨M, hM⟩ := hq.1.continuous.bounded_above_of_compact_support hq.2.1
  exact ⟨M, ρ₀, h0, h1, hq.1.continuous.aestronglyMeasurable, fun x => by simpa using hM x, hs⟩

lemma test_eq_zero_of_not_mem (hq : q ∈ testFunctions (ball (0 : ℂ) 1)) {x : ℂ}
    (hx : x ∉ ball (0 : ℂ) 1) : q x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hx (hq.2.2 h)

lemma DiskNice.of_test (hq : q ∈ testFunctions (ball (0 : ℂ) 1)) : DiskNice q :=
  ⟨univ, isOpen_univ, subset_univ _, (hq.1.of_le (by norm_cast)).contDiffOn,
    fun z hz => test_eq_zero_of_not_mem hq (by simp [mem_sphere_zero_iff_norm.1 hz])⟩

lemma test_memLp (hq : q ∈ testFunctions (ball (0 : ℂ) 1)) : MemLp q 2 (volume.restrict (ball (0 : ℂ) 1)) :=
  (hq.1.continuous.memLp_of_hasCompactSupport hq.2.1).restrict _

/-- Green potentials of test functions. -/
theorem greenPot_test (hq : q ∈ testFunctions (ball (0 : ℂ) 1)) :
    DiskNice (greenPot q) ∧
      (∀ z ∈ ball (0 : ℂ) 1, Laplacian.laplacian (greenPot q) z = -q z) ∧
      ∀ w, greenPotD q w = greenPot q w := by
  obtain ⟨M, ρ₀, h0, h1, hb⟩ := test_bddSupp hq
  obtain ⟨R, hR, hs⟩ := greenPot_smooth_of_smooth hq.1 hq.2.1 h0 h1 hb.supp
  refine ⟨⟨ball 0 R, isOpen_ball, closedBall_subset_ball hR,
    hs.of_le (by norm_cast), fun z hz =>
      greenPot_eq_zero_of_norm_eq_one hb (mem_sphere_zero_iff_norm.1 hz)⟩,
    fun z hz => (greenPot_laplacian hb h0 h1.le isOpen_ball subset_rfl
      ((hq.1.of_le (by norm_cast)).contDiffOn) hz).2, fun w => ?_⟩
  rw [greenPot_eq_integral hb, greenPotD]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun η hη => ?_
  rw [test_eq_zero_of_not_mem hq hη, mul_zero]

end Tests

/-! ### The Green form -/

/-- The Green form `B(p, q) = ∫_𝔻 p · G q`. -/
def formB (p q : ℂ → ℝ) : ℝ := ∫ x in ball (0 : ℂ) 1, p x * greenPotD q x

lemma formB_symm {p q : ℂ → ℝ} (hp : MemLp p 2 (volume.restrict (ball (0 : ℂ) 1))) (hpm : StronglyMeasurable p)
    (hq : MemLp q 2 (volume.restrict (ball (0 : ℂ) 1))) (hqm : StronglyMeasurable q) : formB p q = formB q p :=
  green_duality_L2 hq hqm hp hpm

lemma formB_test_symm {p q : ℂ → ℝ} (hp : p ∈ testFunctions (ball (0 : ℂ) 1))
    (hq : q ∈ testFunctions (ball (0 : ℂ) 1)) : formB p q = formB q p :=
  formB_symm (test_memLp hp) hp.1.continuous.stronglyMeasurable (test_memLp hq)
    hq.1.continuous.stronglyMeasurable

/-- `B(p, q) = -∫ p Δ(Gq)` written through the Green potential. -/
lemma formB_test_eq {p q : ℂ → ℝ} (hq : q ∈ testFunctions (ball (0 : ℂ) 1)) :
    formB p q = ∫ x in ball (0 : ℂ) 1, p x * greenPot q x := by
  unfold formB
  simp_rw [(greenPot_test hq).2.2]

lemma formB_self_nonneg {q : ℂ → ℝ} (hq : q ∈ testFunctions (ball (0 : ℂ) 1)) :
    0 ≤ formB q q := by
  obtain ⟨hn, hL, -⟩ := greenPot_test hq
  rw [formB_test_eq hq]
  have h1 : ∫ x in ball (0 : ℂ) 1, q x * greenPot q x =
      -∫ x in ball (0 : ℂ) 1, greenPot q x * Laplacian.laplacian (greenPot q) x := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_ball fun x hx => ?_
    rw [hL x hx]; ring
  rw [h1, ← hn.green_first hn]
  exact setIntegral_nonneg measurableSet_ball fun x _ => by
    rw [gradInner_self]; positivity

lemma formB_add_left {p r q : ℂ → ℝ} (hp : p ∈ testFunctions (ball (0 : ℂ) 1))
    (hr : r ∈ testFunctions (ball (0 : ℂ) 1)) (hq : q ∈ testFunctions (ball (0 : ℂ) 1)) (s : ℝ) :
    formB (fun x => p x + s * r x) q = formB p q + s * formB r q := by
  rw [formB_test_eq hq, formB_test_eq hq, formB_test_eq hq]
  have hc := (greenPot_test hq).1.continuousOn
  have i1 : IntegrableOn (fun x => p x * greenPot q x) (ball (0 : ℂ) 1) :=
    DiskNice.integrableOn_ball_of_continuousOn (hp.1.continuous.continuousOn.mul hc)
  have i2 : IntegrableOn (fun x => r x * greenPot q x) (ball (0 : ℂ) 1) :=
    DiskNice.integrableOn_ball_of_continuousOn (hr.1.continuous.continuousOn.mul hc)
  rw [← integral_const_mul, ← integral_add i1 (i2.const_mul s)]
  congr 1; funext x; ring

lemma test_add {p r : ℂ → ℝ} (hp : p ∈ testFunctions (ball (0 : ℂ) 1))
    (hr : r ∈ testFunctions (ball (0 : ℂ) 1)) (s : ℝ) :
    (fun x => p x + s * r x) ∈ testFunctions (ball (0 : ℂ) 1) :=
  (testFunctions _).add_mem hp ((testFunctions _).smul_mem s hr)

lemma sq_le_of_quadratic_nonneg {a b c : ℝ} (hc : 0 ≤ c) (h : ∀ s : ℝ, 0 ≤ a + 2 * b * s + c * s ^ 2) :
    b ^ 2 ≤ a * c := by
  rcases hc.lt_or_eq with hc | hc
  · have := h (-b / c)
    have e : a + 2 * b * (-b / c) + c * (-b / c) ^ 2 = a - b ^ 2 / c := by field_simp; ring
    rw [e, sub_nonneg, div_le_iff₀ hc] at this
    linarith
  · subst hc
    by_contra hb
    have hb0 : b ≠ 0 := by rintro rfl; simp at hb
    have := h (-(a + 1) / (2 * b))
    have e : a + 2 * b * (-(a + 1) / (2 * b)) + 0 * (-(a + 1) / (2 * b)) ^ 2 = -1 := by
      field_simp; ring
    rw [e] at this; linarith

/-- **Cauchy–Schwarz** for the Green form on test functions. -/
theorem formB_sq_le {p q : ℂ → ℝ} (hp : p ∈ testFunctions (ball (0 : ℂ) 1))
    (hq : q ∈ testFunctions (ball (0 : ℂ) 1)) : formB p q ^ 2 ≤ formB p p * formB q q := by
  refine sq_le_of_quadratic_nonneg (formB_self_nonneg hq) fun s => ?_
  have h := formB_self_nonneg (test_add hp hq s)
  rw [formB_add_left hp hq (test_add hp hq s), formB_test_symm hp (test_add hp hq s),
    formB_test_symm hq (test_add hp hq s), formB_add_left hp hq hp, formB_add_left hp hq hq,
    formB_test_symm hq hp] at h
  nlinarith [h]

/-- Hypotheses on the weight `a = |G'|` used in the spectral comparison. -/
structure WeightOK (a : ℂ → ℝ) (A : ℝ) : Prop where
  meas : Measurable a
  bound : ∀ η ∈ ball (0 : ℂ) 1, |a η| ≤ A
  pos : ∀ η ∈ ball (0 : ℂ) 1, 0 < a η
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun η => a η ^ 2) (ball 0 1)

section TestOps

variable {ψ : ℂ → ℝ}

lemma laplacian_eq_zero_of_not_mem_tsupport {z : ℂ} (hz : z ∉ tsupport ψ) :
    Laplacian.laplacian ψ z = 0 := by
  have h : ψ =ᶠ[𝓝 z] fun _ => (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.1 hz
  rw [(InnerProductSpace.laplacian_congr_nhds h).eq_of_nhds, laplacian_eq_fderiv_fderiv_real]
  simp

/-- The Laplacian of a test function is a test function. -/
lemma test_laplacian (hψ : ψ ∈ testFunctions (ball (0 : ℂ) 1)) :
    Laplacian.laplacian ψ ∈ testFunctions (ball (0 : ℂ) 1) := by
  have hsupp : Function.support (Laplacian.laplacian ψ) ⊆ tsupport ψ := fun z hz => by
    by_contra h; exact hz (laplacian_eq_zero_of_not_mem_tsupport h)
  refine ⟨?_, hψ.2.1.mono' hsupp,
    (closure_minimal hsupp (isClosed_tsupport ψ)).trans hψ.2.2⟩
  have e : Laplacian.laplacian ψ = fun z => fderiv ℝ (fderiv ℝ ψ) z 1 1 +
      fderiv ℝ (fderiv ℝ ψ) z Complex.I Complex.I := by
    funext z; exact laplacian_eq_fderiv_fderiv_real ψ z
  rw [e]
  have h1 := hψ.1.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have h2 := h1.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  exact ((h2.clm_apply contDiff_const).clm_apply contDiff_const).add
    ((h2.clm_apply contDiff_const).clm_apply contDiff_const)

/-- A test function times a function smooth on the disk is a test function. -/
lemma test_mul_smooth (hψ : ψ ∈ testFunctions (ball (0 : ℂ) 1)) {ρ : ℂ → ℝ}
    (hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ (ball 0 1)) :
    (fun x => ρ x * ψ x) ∈ testFunctions (ball (0 : ℂ) 1) := by
  have hsupp : Function.support (fun x => ρ x * ψ x) ⊆ tsupport ψ := fun z hz =>
    subset_tsupport _ (right_ne_zero_of_mul hz)
  refine ⟨?_, hψ.2.1.mono' hsupp,
    (closure_minimal hsupp (isClosed_tsupport ψ)).trans hψ.2.2⟩
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  by_cases hz : z ∈ ball (0 : ℂ) 1
  · exact (hρ.contDiffAt (isOpen_ball.mem_nhds hz)).mul hψ.1.contDiffAt
  · have h : ψ =ᶠ[𝓝 z] fun _ => (0 : ℝ) :=
      notMem_tsupport_iff_eventuallyEq.1 fun h => hz (hψ.2.2 h)
    refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [h] with y hy
    simp [hy]

end TestOps

end

section

/-! ## Min–max values and conformal transport -/

open MeasureTheory Set Real Metric Filter Topology

/-- Min–max values of a Rayleigh quotient over a space of functions. -/
def minmax (S : Submodule ℝ (ℂ → ℝ)) (R : (ℂ → ℝ) → ENNReal) (j : ℕ) : ENNReal :=
  ⨅ (V : Submodule ℝ (ℂ → ℝ)) (_ : V ≤ S) (_ : Module.finrank ℝ V = j),
    ⨆ (u : ℂ → ℝ) (_ : u ∈ V) (_ : u ≠ 0), R u

lemma dirichletEigenvalue_eq_minmax (Ω : Set ℂ) (j : ℕ) :
    dirichletEigenvalue Ω j = minmax (testFunctions Ω) rayleigh j := rfl

/-- The weighted mass `∫ ρ |u|²`. -/
def massW (ρ : ℂ → ℝ) (u : ℂ → ℝ) : ENNReal := ∫⁻ z, ENNReal.ofReal (ρ z) * ‖u z‖ₑ ^ 2

/-- The weighted Rayleigh quotient `∫ |∇u|² / ∫ ρ |u|²`. -/
def wRayleigh (ρ : ℂ → ℝ) (u : ℂ → ℝ) : ENNReal := dirichletEnergy u / massW ρ u

/-- **Comparison of min–max values** along an injective linear map. -/
theorem minmax_le_of_map {S1 S2 : Submodule ℝ (ℂ → ℝ)} {R1 R2 : (ℂ → ℝ) → ENNReal}
    (P : (ℂ → ℝ) →ₗ[ℝ] (ℂ → ℝ)) (hPS : ∀ u ∈ S1, P u ∈ S2)
    (hinj : ∀ u ∈ S1, P u = 0 → u = 0) (hR : ∀ u ∈ S1, u ≠ 0 → R2 (P u) ≤ R1 u) (j : ℕ) :
    minmax S2 R2 j ≤ minmax S1 R1 j := by
  classical
  conv_rhs => unfold minmax
  refine le_iInf fun V => le_iInf fun hV => le_iInf fun hj => ?_
  have hinjV : Function.Injective (P.domRestrict V) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact Subtype.ext (hinj x (hV x.2) (by simpa using hx))
  set W := LinearMap.range (P.domRestrict V) with hW
  have hWdim : Module.finrank ℝ W = j := by
    rw [hW, LinearMap.finrank_range_of_inj hinjV, hj]
  have hWle : W ≤ S2 := by
    rintro _ ⟨x, rfl⟩
    exact hPS x (hV x.2)
  calc minmax S2 R2 j ≤ ⨆ (v : ℂ → ℝ) (_ : v ∈ W) (_ : v ≠ 0), R2 v := by
        unfold minmax
        exact iInf_le_of_le W (iInf_le_of_le hWle (iInf_le_of_le hWdim le_rfl))
    _ ≤ _ := by
        refine iSup_le fun v => iSup_le fun hv => iSup_le fun hv0 => ?_
        obtain ⟨x, rfl⟩ := hv
        have hx0 : (x : ℂ → ℝ) ≠ 0 := by
          rintro h
          apply hv0
          simp [h]
        calc R2 (P.domRestrict V x) ≤ R1 x := hR x (hV x.2) hx0
          _ ≤ _ := le_iSup_of_le (x : ℂ → ℝ) (le_iSup_of_le x.2
            (le_iSup (fun _ : (x : ℂ → ℝ) ≠ 0 => R1 x) hx0))

/-- The pullback `Ω.indicator (u ∘ Φ)` as a linear map. -/
def pullbackLin (Ω : Set ℂ) (Φ : ℂ → ℂ) : (ℂ → ℝ) →ₗ[ℝ] (ℂ → ℝ) where
  toFun u := Ω.indicator (fun z => u (Φ z))
  map_add' u v := by
    simp only [Pi.add_apply]
    exact Set.indicator_add Ω _ _
  map_smul' c u := by
    simp only [Pi.smul_apply, RingHom.id_apply]
    exact Set.indicator_const_smul Ω c _

lemma pullbackLin_apply (Ω : Set ℂ) (Φ : ℂ → ℂ) (u : ℂ → ℝ) :
    pullbackLin Ω Φ u = Ω.indicator (fun z => u (Φ z)) := rfl

section Pullback

variable {Ω Ω' : Set ℂ} {Φ Ψ : ℂ → ℂ}

/-- Pullbacks of test functions by biholomorphisms are test functions. -/
lemma pullback_test (hΩ : IsOpen Ω) (hΦ : DifferentiableOn ℂ Φ Ω) (hΨ : ContinuousOn Ψ Ω')
    (hΨmaps : MapsTo Ψ Ω' Ω) (hΨΦ : ∀ z ∈ Ω, Φ z ∈ Ω' ∧ Ψ (Φ z) = z) {u : ℂ → ℝ}
    (hu : u ∈ testFunctions Ω') :
    pullbackLin Ω Φ u ∈ testFunctions Ω ∧
      ∀ z, z ∉ Ω → Ω.indicator (fun z => u (Φ z)) =ᶠ[𝓝 z] 0 := by
  obtain ⟨hu, hus, husub⟩ := hu
  set K := tsupport u with hK
  have hKc : IsCompact K := hus
  have hK'c : IsCompact (Ψ '' K) := hKc.image_of_continuousOn (hΨ.mono husub)
  have hK'Ω : Ψ '' K ⊆ Ω := by rintro _ ⟨w, hw, rfl⟩; exact hΨmaps (husub hw)
  have hΦsmooth : ∀ z ∈ Ω, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ z := fun z hz =>
    ((hΦ.contDiffOn hΩ (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).contDiffAt (hΩ.mem_nhds hz)).restrict_scalars ℝ
  have hsupp : ∀ z, pullbackLin Ω Φ u z ≠ 0 → z ∈ Ψ '' K := by
    intro z hz
    rw [pullbackLin_apply] at hz
    by_cases hzΩ : z ∈ Ω
    · rw [Set.indicator_of_mem hzΩ] at hz
      exact ⟨Φ z, subset_tsupport _ hz, (hΨΦ z hzΩ).2⟩
    · rw [Set.indicator_of_notMem hzΩ] at hz; exact absurd rfl hz
  have hzero : ∀ z, z ∉ Ψ '' K → pullbackLin Ω Φ u =ᶠ[𝓝 z] 0 := by
    intro z hz
    filter_upwards [hK'c.isClosed.isOpen_compl.mem_nhds hz] with y hy
    by_contra h
    exact hy (hsupp y h)
  refine ⟨⟨?_, HasCompactSupport.intro hK'c fun z hz => by_contra fun h => hz (hsupp z h),
    (closure_minimal (fun z hz => hsupp z hz) hK'c.isClosed).trans hK'Ω⟩,
    fun z hz => hzero z fun h => hz (hK'Ω h)⟩
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  by_cases hzΩ : z ∈ Ω
  · have heq : (fun y => u (Φ y)) =ᶠ[𝓝 z] pullbackLin Ω Φ u := by
      filter_upwards [hΩ.mem_nhds hzΩ] with y hy
      rw [pullbackLin_apply, Set.indicator_of_mem hy]
    exact ((hu.contDiffAt).comp z (hΦsmooth z hzΩ)).congr_of_eventuallyEq heq.symm
  · have hz' : z ∉ Ψ '' K := fun h => hzΩ (hK'Ω h)
    exact contDiffAt_const.congr_of_eventuallyEq (hzero z hz')

lemma pullback_inj (hΨmaps : MapsTo Ψ Ω' Ω) (hΦΨ : ∀ w ∈ Ω', Φ (Ψ w) = w) {u : ℂ → ℝ}
    (hu : u ∈ testFunctions Ω') (h0 : pullbackLin Ω Φ u = 0) : u = 0 := by
  funext w
  by_cases hw : w ∈ Ω'
  · have := congrFun h0 (Ψ w)
    rw [pullbackLin_apply, Set.indicator_of_mem (hΨmaps hw), hΦΨ w hw] at this
    exact this
  · exact image_eq_zero_of_notMem_tsupport (fun h => hw (hu.2.2 h))

end Pullback

/-! ### Conformal transport of eigenvalues -/

section Transport

variable {R0 : ℝ} {G : ℂ → ℂ}

/-- The conformal weight `|G'|²`. -/
def confWeight (G : ℂ → ℂ) (η : ℂ) : ℝ := ‖deriv G η‖ ^ 2

/-- The common setup: a holomorphic inverse of `G`. -/
lemma conf_setup (hR0 : 1 < R0) (hG : DifferentiableOn ℂ G (ball 0 R0))
    (hinj : InjOn G (ball 0 R0)) :
    ∃ g : ℂ → ℂ, IsOpen (G '' ball 0 1) ∧ DifferentiableOn ℂ g (G '' ball 0 1) ∧
      MapsTo g (G '' ball 0 1) (ball 0 1) ∧ (∀ z ∈ ball (0 : ℂ) R0, g (G z) = z) ∧
      (∀ w ∈ G '' ball 0 1, G (g w) = w) := by
  have hBo : IsOpen (ball (0 : ℂ) R0) := isOpen_ball
  have hBc : IsPreconnected (ball (0 : ℂ) R0) := (convex_ball _ _).isPreconnected
  have hD1 : ball (0 : ℂ) 1 ⊆ ball 0 R0 := ball_subset_ball hR0.le
  obtain ⟨g, hgd, -, hgG, hGg⟩ := exists_holomorphic_inverse hBo hBc hG hinj
  refine ⟨g, isOpen_image_of_injOn hBo hBc hG hinj hD1 isOpen_ball,
    hgd.mono (image_mono hD1), ?_, hgG, fun w hw => hGg w (image_mono hD1 hw)⟩
  rintro _ ⟨η, hη, rfl⟩
  rw [hgG η (hD1 hη)]; exact hη

lemma div_le_div_of_le_of_eq {a b c d : ENNReal} (h1 : a ≤ b) (h2 : c = d) : a / c ≤ b / d := by
  rw [h2]; exact ENNReal.div_le_div_right h1 _

/-- Lower comparison: weighted min–max values on the disk are at most the Dirichlet
eigenvalues of `G(𝔻)`. -/
theorem minmax_weighted_le (hR0 : 1 < R0) (hG : DifferentiableOn ℂ G (ball 0 R0))
    (hinj : InjOn G (ball 0 R0)) (j : ℕ) :
    minmax (testFunctions (ball 0 1)) (wRayleigh (confWeight G)) j ≤
      dirichletEigenvalue (G '' ball 0 1) j := by
  obtain ⟨g, hΩ, hgd, hgmaps, hgG, hGg⟩ := conf_setup hR0 hG hinj
  have hD1 : ball (0 : ℂ) 1 ⊆ ball 0 R0 := ball_subset_ball hR0.le
  have hG1 := hG.mono hD1
  have hΨΦ : ∀ z ∈ ball (0 : ℂ) 1, G z ∈ G '' ball 0 1 ∧ g (G z) = z := fun z hz =>
    ⟨mem_image_of_mem G hz, hgG z (hD1 hz)⟩
  have htest := fun {u : ℂ → ℝ} (hu : u ∈ testFunctions (G '' ball 0 1)) =>
    pullback_test isOpen_ball hG1 hgd.continuousOn hgmaps hΨΦ hu
  rw [dirichletEigenvalue_eq_minmax]
  refine minmax_le_of_map (R1 := rayleigh) (R2 := wRayleigh (confWeight G))
    (pullbackLin (ball 0 1) G) (fun u hu => (htest hu).1)
    (fun u hu h0 => pullback_inj hgmaps hGg hu h0) (fun u hu _ => ?_) j
  refine div_le_div_of_le_of_eq
    (dirichletEnergy_pullback_le isOpen_ball hG1 (hinj.mono hD1) hu.1 (htest hu).2) ?_
  unfold massW l2NormSq
  have hsupp : Function.support (fun w => ‖u w‖ₑ ^ 2) ⊆ G '' ball 0 1 := by
    intro w hw
    refine hu.2.2 (subset_tsupport _ ?_)
    intro h; apply hw; simp [h]
  rw [← setLIntegral_eq_of_support_subset hsupp, lintegral_image_holomorphic isOpen_ball hG1
    (hinj.mono hD1)]
  have e : (fun z => ENNReal.ofReal (confWeight G z) * ‖pullbackLin (ball 0 1) G u z‖ₑ ^ 2) =
      (ball (0 : ℂ) 1).indicator fun z => ENNReal.ofReal (‖deriv G z‖ ^ 2) * ‖u (G z)‖ₑ ^ 2 := by
    funext z
    by_cases hz : z ∈ ball (0 : ℂ) 1
    · simp [pullbackLin_apply, indicator_of_mem hz, confWeight]
    · simp [pullbackLin_apply, indicator_of_notMem hz]
  rw [e, lintegral_indicator measurableSet_ball]

/-- Upper comparison: the Dirichlet eigenvalues of `G(𝔻)` are at most the weighted min–max
values on the disk. -/
theorem dirichletEigenvalue_le_weighted (hR0 : 1 < R0) (hG : DifferentiableOn ℂ G (ball 0 R0))
    (hinj : InjOn G (ball 0 R0)) (j : ℕ) :
    dirichletEigenvalue (G '' ball 0 1) j ≤
      minmax (testFunctions (ball 0 1)) (wRayleigh (confWeight G)) j := by
  obtain ⟨g, hΩ, hgd, hgmaps, hgG, hGg⟩ := conf_setup hR0 hG hinj
  have hD1 : ball (0 : ℂ) 1 ⊆ ball 0 R0 := ball_subset_ball hR0.le
  have hG1 := hG.mono hD1
  have hGmaps : MapsTo G (ball 0 1) (G '' ball 0 1) := fun z hz => mem_image_of_mem G hz
  have hΨΦ : ∀ z ∈ G '' ball 0 1, g z ∈ ball (0 : ℂ) 1 ∧ G (g z) = z := fun z hz =>
    ⟨hgmaps hz, hGg z hz⟩
  have hginj : InjOn g (G '' ball 0 1) := fun a ha b hb hab => by
    rw [← hGg a ha, ← hGg b hb, hab]
  have htest := fun {u : ℂ → ℝ} (hu : u ∈ testFunctions (ball (0 : ℂ) 1)) =>
    pullback_test hΩ hgd hG1.continuousOn hGmaps hΨΦ hu
  rw [dirichletEigenvalue_eq_minmax]
  refine minmax_le_of_map (R1 := wRayleigh (confWeight G)) (R2 := rayleigh)
    (pullbackLin (G '' ball 0 1) g) (fun u hu => (htest hu).1)
    (fun u hu h0 => pullback_inj hGmaps (fun w hw => hgG w (hD1 hw)) hu h0) (fun u hu _ => ?_) j
  refine div_le_div_of_le_of_eq
    (dirichletEnergy_pullback_le hΩ hgd hginj hu.1 (htest hu).2) ?_
  unfold massW l2NormSq
  have hsupp : Function.support (fun w => ENNReal.ofReal (confWeight G w) * ‖u w‖ₑ ^ 2) ⊆
      ball 0 1 := by
    intro w hw
    refine hu.2.2 (subset_tsupport _ ?_)
    intro h; apply hw; simp [h]
  rw [← setLIntegral_eq_of_support_subset hsupp]
  have e : (fun z => ‖pullbackLin (G '' ball 0 1) g u z‖ₑ ^ 2) =
      (G '' ball 0 1).indicator fun z => ‖u (g z)‖ₑ ^ 2 := by
    funext z
    by_cases hz : z ∈ G '' ball 0 1
    · simp [pullbackLin_apply, indicator_of_mem hz]
    · simp [pullbackLin_apply, indicator_of_notMem hz]
  rw [e, lintegral_indicator hΩ.measurableSet, lintegral_image_holomorphic isOpen_ball hG1
    (hinj.mono hD1)]
  refine setLIntegral_congr_fun measurableSet_ball fun z hz => ?_
  simp [confWeight, hgG z (hD1 hz)]

end Transport

end

section

/-! ## Eigenvectors of compact positive symmetric operators on real Hilbert spaces -/

open scoped InnerProductSpace
open Set Metric Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Cauchy–Schwarz for a positive semidefinite symmetric operator. -/
lemma inner_apply_sq_le_of_psd {T : H →L[ℝ] H} (hs : ∀ x y, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ)
    (hp : ∀ x, 0 ≤ ⟪T x, x⟫_ℝ) (x y : H) :
    ⟪T x, y⟫_ℝ ^ 2 ≤ ⟪T x, x⟫_ℝ * ⟪T y, y⟫_ℝ := by
  have h : ∀ s : ℝ, 0 ≤ ⟪T y, y⟫_ℝ * (s * s) + 2 * ⟪T x, y⟫_ℝ * s + ⟪T x, x⟫_ℝ := by
    intro s
    have := hp (x + s • y)
    simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, RCLike.conj_to_real] at this
    have e : ⟪T y, x⟫_ℝ = ⟪T x, y⟫_ℝ := by rw [hs, real_inner_comm]
    rw [e] at this
    nlinarith
  have := discrim_le_zero h
  unfold discrim at this
  nlinarith

omit [CompleteSpace H] in
/-- `‖T x‖² ≤ ‖T‖ ⟪T x, x⟫` for a positive semidefinite symmetric operator. -/
lemma norm_apply_sq_le_of_psd {T : H →L[ℝ] H} (hs : ∀ x y, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ)
    (hp : ∀ x, 0 ≤ ⟪T x, x⟫_ℝ) (x : H) : ‖T x‖ ^ 2 ≤ ‖T‖ * ⟪T x, x⟫_ℝ := by
  have h1 := inner_apply_sq_le_of_psd hs hp x (T x)
  rw [real_inner_self_eq_norm_sq] at h1
  have h2 : ⟪T (T x), T x⟫_ℝ ≤ ‖T‖ * ‖T x‖ ^ 2 := by
    calc ⟪T (T x), T x⟫_ℝ ≤ ‖T (T x)‖ * ‖T x‖ := real_inner_le_norm _ _
      _ ≤ ‖T‖ * ‖T x‖ * ‖T x‖ := by gcongr; exact T.le_opNorm _
      _ = ‖T‖ * ‖T x‖ ^ 2 := by ring
  have h0 := hp x
  by_cases hz : ‖T x‖ = 0
  · rw [hz, sq, zero_mul]; exact mul_nonneg (norm_nonneg _) h0
  have hpos : 0 < ‖T x‖ ^ 2 := by positivity
  have : (‖T x‖ ^ 2) ^ 2 ≤ ⟪T x, x⟫_ℝ * (‖T‖ * ‖T x‖ ^ 2) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 h0)
  nlinarith

omit [CompleteSpace H] in
/-- **Top eigenvector** of a compact symmetric operator whose quadratic form takes a positive
value. -/
lemma exists_top_eigenvector {T : H →L[ℝ] H} (hc : IsCompactOperator T)
    (hs : ∀ x y, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ) {y₀ : H}
    (hy₀ : 0 < ⟪T y₀, y₀⟫_ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∃ x : H, ‖x‖ = 1 ∧ T x = M • x ∧ ∀ y, ⟪T y, y⟫_ℝ ≤ M * ‖y‖ ^ 2 := by
  have hscale : ∀ (c : ℝ) (k : H), ⟪T (c • k), c • k⟫_ℝ = c ^ 2 * ⟪T k, k⟫_ℝ := by
    intro c k
    rw [map_smul, inner_smul_left, inner_smul_right, RCLike.conj_to_real]; ring
  have hbd : ∀ y : H, ⟪T y, y⟫_ℝ ≤ ‖T‖ * ‖y‖ ^ 2 := fun y =>
    calc ⟪T y, y⟫_ℝ ≤ ‖T y‖ * ‖y‖ := real_inner_le_norm _ _
      _ ≤ ‖T‖ * ‖y‖ * ‖y‖ := by gcongr; exact T.le_opNorm _
      _ = ‖T‖ * ‖y‖ ^ 2 := by ring
  set S := (fun y => ⟪T y, y⟫_ℝ) '' closedBall (0 : H) 1 with hSdef
  have hSne : S.Nonempty := ⟨_, 0, by simp, rfl⟩
  have hSbdd : BddAbove S := ⟨‖T‖, by
    rintro _ ⟨y, hy, rfl⟩
    have hy1 : ‖y‖ ≤ 1 := by simpa using hy
    calc ⟪T y, y⟫_ℝ ≤ ‖T‖ * ‖y‖ ^ 2 := hbd y
      _ ≤ ‖T‖ * 1 := by gcongr; nlinarith [norm_nonneg y]
      _ = ‖T‖ := mul_one _⟩
  set M := sSup S with hMdef
  have hle : ∀ z : H, ⟪T z, z⟫_ℝ ≤ M * ‖z‖ ^ 2 := by
    intro z
    by_cases hz : z = 0
    · simp [hz]
    have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hmem : ⟪T (‖z‖⁻¹ • z), ‖z‖⁻¹ • z⟫_ℝ ∈ S :=
      ⟨_, by rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
        inv_mul_cancel₀ hzn.ne'], rfl⟩
    have h1 := le_csSup hSbdd hmem
    rw [hscale, inv_pow, ← hMdef] at h1
    have := (inv_mul_le_iff₀ (by positivity : (0:ℝ) < ‖z‖ ^ 2)).1 h1
    linarith
  have hMpos : 0 < M := by
    have := hle y₀
    by_contra h
    push_neg at h
    nlinarith [sq_nonneg ‖y₀‖]
  have hseq : ∀ n : ℕ, ∃ y ∈ closedBall (0 : H) 1, M - 1 / (n + 1) < ⟪T y, y⟫_ℝ := by
    intro n
    obtain ⟨_, ⟨y, hy, rfl⟩, h⟩ := exists_lt_of_lt_csSup hSne
      (show M - 1 / ((n : ℝ) + 1) < M by linarith [show (0:ℝ) < 1 / ((n:ℝ)+1) by positivity])
    exact ⟨y, hy, h⟩
  choose y hy hyM using hseq
  set A : H →L[ℝ] H := M • 1 - T with hA
  have hAapp : ∀ x, A x = M • x - T x := fun x => rfl
  have hAre : ∀ x, ⟪A x, x⟫_ℝ = M * ‖x‖ ^ 2 - ⟪T x, x⟫_ℝ := by
    intro x
    rw [hAapp, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, RCLike.conj_to_real]
  have hAs : ∀ x z, ⟪A x, z⟫_ℝ = ⟪x, A z⟫_ℝ := by
    intro x z
    rw [hAapp, hAapp, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hs,
      RCLike.conj_to_real]
  have hAp : ∀ x, 0 ≤ ⟪A x, x⟫_ℝ := fun x => by rw [hAre]; linarith [hle x]
  have hAy : ∀ n, ‖A (y n)‖ ^ 2 ≤ ‖A‖ * (1 / (n + 1)) := by
    intro n
    have hy1 : ‖y n‖ ≤ 1 := by simpa using hy n
    refine (norm_apply_sq_le_of_psd hAs hAp _).trans ?_
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
    (f := (T : H →ₗ[ℝ] H)) hc 1
  have hGyS : ∀ n, T (y n) ∈ Sc := fun n => hCS ⟨y n, hy n, rfl⟩
  obtain ⟨z, -, ψ, hψ, hz⟩ := hSc.tendsto_subseq hGyS
  have hψt : Tendsto ψ atTop atTop := hψ.tendsto_atTop
  have hid : ∀ n, y n = M⁻¹ • (A (y n) + T (y n)) := by
    intro n
    rw [hAapp, sub_add_cancel, smul_smul, inv_mul_cancel₀ hMpos.ne', one_smul]
  set x := M⁻¹ • z with hx
  have hyx : Tendsto (fun n => y (ψ n)) atTop (𝓝 x) := by
    have := ((hAy0.comp hψt).add hz).const_smul M⁻¹
    rw [zero_add] at this
    refine this.congr fun n => ?_
    simp only [Function.comp_apply]
    exact (hid _).symm
  have hAx : A x = 0 :=
    tendsto_nhds_unique ((A.continuous.tendsto x).comp hyx) (hAy0.comp hψt)
  have hTx : T x = M • x := by
    rw [hAapp, sub_eq_zero] at hAx; exact hAx.symm
  have hxM : M ≤ ⟪T x, x⟫_ℝ := by
    have hcont : Continuous fun w : H => ⟪T w, w⟫_ℝ := by fun_prop
    have hl : Tendsto (fun n => M - 1 / ((ψ n : ℝ) + 1)) atTop (𝓝 M) := by
      have := (tendsto_const_nhds (x := M)).sub (h1n.comp hψt)
      rw [sub_zero] at this
      exact this
    refine le_of_tendsto_of_tendsto' hl ((hcont.tendsto x).comp hyx) (fun n => ?_)
    simp only [Function.comp_apply]
    exact (hyM (ψ n)).le
  have hx1 : ‖x‖ ≤ 1 := by
    have : x ∈ closedBall (0 : H) 1 :=
      isClosed_closedBall.mem_of_tendsto hyx (Eventually.of_forall fun n => hy (ψ n))
    simpa using this
  have hx1' : 1 ≤ ‖x‖ := by
    have := hxM.trans (hle x)
    have : 1 ≤ ‖x‖ ^ 2 := by
      by_contra h; push_neg at h; nlinarith
    nlinarith [norm_nonneg x]
  exact ⟨M, hMpos, x, le_antisymm hx1 hx1', hTx, hle⟩

omit [CompleteSpace H] in
/-- **Successive maximizers of the Rayleigh quotient** of a compact symmetric operator. Either
`n` eigenpairs with positive eigenvalues are produced, or the construction stops at some `m < n` because the quadratic form
is nonpositive on the orthogonal complement of the first `m` eigenvectors. -/
theorem exists_eigen_family {T : H →L[ℝ] H} (hc : IsCompactOperator T)
    (hs : ∀ x y, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ) (n : ℕ) :
    ∃ (m : ℕ) (e : ℕ → H) (μ : ℕ → ℝ), m ≤ n ∧
      (∀ i < m, ∀ l < m, ⟪e i, e l⟫_ℝ = if i = l then 1 else 0) ∧
      (∀ i < m, T (e i) = μ i • e i ∧ 0 < μ i) ∧
      (∀ i < m, ∀ x, (∀ l < i, ⟪e l, x⟫_ℝ = 0) → ⟪T x, x⟫_ℝ ≤ μ i * ‖x‖ ^ 2) ∧
      (m < n → ∀ x, (∀ l < m, ⟪e l, x⟫_ℝ = 0) → ⟪T x, x⟫_ℝ ≤ 0) := by
  induction n with
  | zero => exact ⟨0, fun _ => 0, fun _ => 0, le_rfl, by simp, by simp, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨m, e, μ, hmn, horth, heig, hmax, hstop⟩ := ih
    rcases lt_or_eq_of_le hmn with hlt | rfl
    · exact ⟨m, e, μ, hmn.trans (Nat.le_succ n), horth, heig, hmax,
        fun _ => hstop hlt⟩
    -- the compression to the orthogonal complement of `e₀, …, e_{m-1}`
    set Q : H →L[ℝ] H := 1 - ∑ l ∈ Finset.range m, (innerSL ℝ (e l)).smulRight (e l) with hQ
    have hQapp : ∀ x, Q x = x - ∑ l ∈ Finset.range m, ⟪e l, x⟫_ℝ • e l := by
      intro x
      simp [hQ]
    have hQorth : ∀ x, ∀ k < m, ⟪e k, Q x⟫_ℝ = 0 := by
      intro x k hk
      rw [hQapp, inner_sub_right, inner_sum]
      simp_rw [inner_smul_right]
      rw [Finset.sum_eq_single k]
      · rw [horth k hk k hk]; simp [real_inner_comm]
      · intro l hl hlk
        rw [horth k hk l (Finset.mem_range.1 hl), if_neg (Ne.symm hlk), mul_zero]
      · intro h; exact absurd (Finset.mem_range.2 hk) h
    have hQfix : ∀ x, (∀ l < m, ⟪e l, x⟫_ℝ = 0) → Q x = x := by
      intro x hx
      rw [hQapp, Finset.sum_eq_zero fun l hl => by rw [hx l (Finset.mem_range.1 hl), zero_smul],
        sub_zero]
    have hTe : ∀ x, ∀ k < m, ⟪e k, T (Q x)⟫_ℝ = 0 := by
      intro x k hk
      rw [real_inner_comm, hs, (heig k hk).1, inner_smul_right, real_inner_comm, hQorth x k hk,
        mul_zero]
    set T' := T.comp Q
    have hsub : ∀ x, x - Q x = ∑ l ∈ Finset.range m, ⟪e l, x⟫_ℝ • e l := by
      intro x; rw [hQapp]; abel
    have hperp : ∀ x y, ⟪T (Q x), y - Q y⟫_ℝ = 0 := by
      intro x y
      rw [hsub, inner_sum]
      refine Finset.sum_eq_zero fun l hl => ?_
      rw [inner_smul_right, ← real_inner_comm (T (Q x)) (e l), hTe x l (Finset.mem_range.1 hl),
        mul_zero]
    have hT'q : ∀ x y, ⟪T' x, y⟫_ℝ = ⟪T (Q x), Q y⟫_ℝ := by
      intro x y
      have : y = Q y + (y - Q y) := by abel
      simp only [T', ContinuousLinearMap.comp_apply]
      conv_lhs => rw [this]
      rw [inner_add_right, hperp, add_zero]
    have hs' : ∀ x y, ⟪T' x, y⟫_ℝ = ⟪x, T' y⟫_ℝ := by
      intro x y
      rw [hT'q, real_inner_comm (T' y) x, hT'q, hs, real_inner_comm]
    have hc' : IsCompactOperator T' := hc.comp_clm Q
    by_cases hpos : ∃ y, 0 < ⟪T' y, y⟫_ℝ
    · obtain ⟨y₀, hy₀⟩ := hpos
      obtain ⟨M, hM, x, hx1, hTx, hle⟩ := exists_top_eigenvector hc' hs' hy₀
      have hxperp : ∀ k < m, ⟪e k, x⟫_ℝ = 0 := by
        intro k hk
        have hx : x = M⁻¹ • T' x := by
          rw [hTx, smul_smul, inv_mul_cancel₀ hM.ne', one_smul]
        rw [hx, inner_smul_right]
        simp only [T', ContinuousLinearMap.comp_apply]
        rw [hTe x k hk, mul_zero]
      have hQx : Q x = x := hQfix x hxperp
      refine ⟨m + 1, Function.update e m x, Function.update μ m M, le_rfl, ?_, ?_, ?_, by simp⟩
      · intro i hi l hl
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | rfl <;>
          rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl' | rfl
        · rw [Function.update_of_ne hi'.ne, Function.update_of_ne hl'.ne]; exact horth i hi' l hl'
        · rw [Function.update_of_ne hi'.ne, Function.update_self, hxperp i hi', if_neg hi'.ne]
        · rw [Function.update_self, Function.update_of_ne hl'.ne, real_inner_comm,
            hxperp l hl', if_neg hl'.ne']
        · rw [Function.update_self, real_inner_self_eq_norm_sq, hx1]; simp
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | rfl
        · rw [Function.update_of_ne hi'.ne, Function.update_of_ne hi'.ne]; exact heig i hi'
        · rw [Function.update_self, Function.update_self]
          refine ⟨?_, hM⟩
          rw [← hTx]; simp only [T', ContinuousLinearMap.comp_apply, hQx]
      · intro i hi z hz
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | rfl
        · rw [Function.update_of_ne hi'.ne]
          exact hmax i hi' z fun l hl => by
            have := hz l hl; rwa [Function.update_of_ne (hl.trans hi').ne] at this
        · rw [Function.update_self]
          have hz' : ∀ l < i, ⟪e l, z⟫_ℝ = 0 := fun l hl => by
            have := hz l hl; rwa [Function.update_of_ne hl.ne] at this
          have := hle z
          simp only [T', ContinuousLinearMap.comp_apply, hQfix z hz'] at this
          exact this
    · push_neg at hpos
      refine ⟨m, e, μ, Nat.le_succ m, horth, heig, hmax, fun _ z hz => ?_⟩
      have := hpos z
      simp only [T', ContinuousLinearMap.comp_apply, hQfix z hz] at this
      exact this

end

section

/-! ## Lower bound for the weighted min–max values -/

open MeasureTheory Set Real Metric Filter Topology
open scoped ComplexConjugate InnerProductSpace

variable {a : ℂ → ℝ} {A : ℝ}

lemma memLp_weight_test (hw : WeightOK a A) {ψ : ℂ → ℝ}
    (hψ : ψ ∈ testFunctions (ball (0 : ℂ) 1)) : MemLp (fun η => a η * ψ η) 2 (volume.restrict (ball (0 : ℂ) 1)) :=
  memLp_mul_weight hw.meas hw.bound (test_memLp hψ)

/-- The `L²` element `a ψ`. -/
def weightLp (hw : WeightOK a A) {ψ : ℂ → ℝ} (hψ : ψ ∈ testFunctions (ball (0 : ℂ) 1)) :
    Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1)) :=
  (memLp_weight_test hw hψ).toLp _

lemma inner_weightLp (hw : WeightOK a A) {ψ : ℂ → ℝ} (hψ : ψ ∈ testFunctions (ball (0 : ℂ) 1))
    (e : Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1))) : ⟪e, weightLp hw hψ⟫_ℝ = ∫ x in ball (0 : ℂ) 1, e x * (a x * ψ x) := by
  rw [inner_Lp_eq]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_weight_test hw hψ).coeFn_toLp] with x hx
  rw [weightLp, hx]

lemma lintegral_ofReal_ball {F : ℂ → ℝ} (hF : ∀ z, 0 ≤ F z) (hFi : IntegrableOn F (ball 0 1))
    (hF0 : ∀ z ∉ ball (0 : ℂ) 1, F z = 0) :
    ∫⁻ z, ENNReal.ofReal (F z) = ENNReal.ofReal (∫ z in ball (0 : ℂ) 1, F z) := by
  rw [ofReal_integral_eq_lintegral_ofReal hFi (Eventually.of_forall hF)]
  refine (setLIntegral_eq_of_support_subset fun z hz => ?_).symm
  by_contra h
  exact hz (by simp [hF0 z h])

lemma enorm_sq_eq_ofReal (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]

lemma enorm_sq_eq_ofReal' {E : Type*} [NormedAddCommGroup E] (x : E) :
    ‖x‖ₑ ^ 2 = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]

lemma norm_weightLp_sq (hw : WeightOK a A) {ψ : ℂ → ℝ}
    (hψ : ψ ∈ testFunctions (ball (0 : ℂ) 1)) :
    ‖weightLp hw hψ‖ ^ 2 = ∫ x in ball (0 : ℂ) 1, (a x ^ 2 * ψ x) * ψ x := by
  rw [weightLp, norm_toLp_sq]
  congr 1; funext x; ring

lemma massW_weight (hw : WeightOK a A) {ψ : ℂ → ℝ} (hψ : ψ ∈ testFunctions (ball (0 : ℂ) 1)) :
    massW (fun η => a η ^ 2) ψ = ENNReal.ofReal (‖weightLp hw hψ‖ ^ 2) := by
  rw [weightLp, norm_toLp_sq]
  unfold massW
  have e : (fun z => ENNReal.ofReal (a z ^ 2) * ‖ψ z‖ₑ ^ 2) =
      fun z => ENNReal.ofReal ((a z * ψ z) ^ 2) := by
    funext z
    rw [enorm_sq_eq_ofReal, ← ENNReal.ofReal_mul (sq_nonneg _), mul_pow]
  rw [e]
  exact lintegral_ofReal_ball (fun z => sq_nonneg _) (memLp_weight_test hw hψ).integrable_sq
    fun z hz => by simp [test_eq_zero_of_not_mem hψ hz]

lemma dirichletEnergy_test {ψ : ℂ → ℝ} (hψ : ψ ∈ testFunctions (ball (0 : ℂ) 1)) :
    dirichletEnergy ψ = ENNReal.ofReal (∫ x in ball (0 : ℂ) 1, ‖fderiv ℝ ψ x‖ ^ 2) := by
  unfold dirichletEnergy
  simp_rw [enorm_sq_eq_ofReal']
  have hc : Continuous (fun x => ‖fderiv ℝ ψ x‖ ^ 2) :=
    ((hψ.1.continuous_fderiv (by simp)).norm).pow 2
  refine lintegral_ofReal_ball (fun z => sq_nonneg _)
    (DiskNice.integrableOn_ball_of_continuousOn hc.continuousOn) fun z hz => ?_
  have : fderiv ℝ ψ z = 0 := by
    by_contra h
    exact hz (hψ.2.2 (support_fderiv_subset ℝ h))
  simp [this]

lemma inner_greenOp_weightLp (hw : WeightOK a A) {ψ : ℂ → ℝ}
    (hψ : ψ ∈ testFunctions (ball (0 : ℂ) 1)) :
    ⟪greenOp hw.meas hw.bound (weightLp hw hψ), weightLp hw hψ⟫_ℝ =
      formB (fun x => a x ^ 2 * ψ x) (fun x => a x ^ 2 * ψ x) := by
  have hae := (memLp_weight_test hw hψ).coeFn_toLp
  rw [inner_greenOp, formB]
  have hg : greenPotD (fun η => a η * (weightLp hw hψ) η) = greenPotD (fun x => a x ^ 2 * ψ x) :=
    greenPotD_congr_ae (by filter_upwards [hae] with x hx; rw [weightLp, hx]; ring)
  rw [hg]
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [weightLp, hx]; ring

/-- **Key inequality** for the lower bound. -/
theorem key_lower (hw : WeightOK a A) {ψ : ℂ → ℝ} (hψ : ψ ∈ testFunctions (ball (0 : ℂ) 1)) :
    massW (fun η => a η ^ 2) ψ = ENNReal.ofReal (‖weightLp hw hψ‖ ^ 2) ∧
    dirichletEnergy ψ = ENNReal.ofReal (∫ x in ball (0 : ℂ) 1, ‖fderiv ℝ ψ x‖ ^ 2) ∧
    ‖weightLp hw hψ‖ ^ 4 ≤ ⟪greenOp hw.meas hw.bound (weightLp hw hψ), weightLp hw hψ⟫_ℝ *
      ∫ x in ball (0 : ℂ) 1, ‖fderiv ℝ ψ x‖ ^ 2 ∧
    (ψ ≠ 0 → 0 < ‖weightLp hw hψ‖) := by
  refine ⟨massW_weight hw hψ, dirichletEnergy_test hψ, ?_, ?_⟩
  · set h := fun x => a x ^ 2 * ψ x
    have hh : h ∈ testFunctions (ball (0 : ℂ) 1) := test_mul_smooth hψ hw.smooth
    have hg := test_laplacian hψ
    have hψn := DiskNice.of_test hψ
    obtain ⟨hWh, hLh, -⟩ := greenPot_test hh
    obtain ⟨hWg, hLg, -⟩ := greenPot_test hg
    -- `‖f‖² = -B(Δψ, h)`
    have h1 : ‖weightLp hw hψ‖ ^ 2 = -formB (Laplacian.laplacian ψ) h := by
      rw [norm_weightLp_sq, formB_test_eq hh]
      have := hψn.green_second hWh
      have e1 : ∫ x in ball (0 : ℂ) 1, ψ x * Laplacian.laplacian (greenPot h) x =
          -∫ x in ball (0 : ℂ) 1, h x * ψ x := by
        rw [← integral_neg]
        refine setIntegral_congr_fun measurableSet_ball fun x hx => ?_
        rw [hLh x hx]; ring
      have e2 : ∫ x in ball (0 : ℂ) 1, Laplacian.laplacian ψ x * greenPot h x =
          ∫ x in ball (0 : ℂ) 1, greenPot h x * Laplacian.laplacian ψ x := by
        congr 1; funext x; ring
      rw [e2]; linarith
    -- `∫ |∇ψ|² = B(Δψ, Δψ)`
    have h2 : ∫ x in ball (0 : ℂ) 1, ‖fderiv ℝ ψ x‖ ^ 2 =
        formB (Laplacian.laplacian ψ) (Laplacian.laplacian ψ) := by
      have e0 : ∫ x in ball (0 : ℂ) 1, ‖fderiv ℝ ψ x‖ ^ 2 =
          ∫ x in ball (0 : ℂ) 1, gradInner (fderiv ℝ ψ x) (fderiv ℝ ψ x) := by
        congr 1; funext x; rw [gradInner_self]
      rw [e0, hψn.green_first hψn, formB_test_eq hg]
      have := hψn.green_second hWg
      have e1 : ∫ x in ball (0 : ℂ) 1, ψ x * Laplacian.laplacian (greenPot
          (Laplacian.laplacian ψ)) x = -∫ x in ball (0 : ℂ) 1, ψ x * Laplacian.laplacian ψ x := by
        rw [← integral_neg]
        refine setIntegral_congr_fun measurableSet_ball fun x hx => ?_
        rw [hLg x hx]; ring
      have e2 : ∫ x in ball (0 : ℂ) 1, Laplacian.laplacian ψ x *
          greenPot (Laplacian.laplacian ψ) x = ∫ x in ball (0 : ℂ) 1,
            greenPot (Laplacian.laplacian ψ) x * Laplacian.laplacian ψ x := by
        congr 1; funext x; ring
      rw [e2]; linarith
    have hcs := formB_sq_le hg hh
    rw [inner_greenOp_weightLp, h2]
    have : ‖weightLp hw hψ‖ ^ 4 = (formB (Laplacian.laplacian ψ) h) ^ 2 := by
      rw [show ‖weightLp hw hψ‖ ^ 4 = (‖weightLp hw hψ‖ ^ 2) ^ 2 by ring, h1]; ring
    rw [this]; linarith
  · intro hψ0
    obtain ⟨z0, hz0⟩ : ∃ z0, ψ z0 ≠ 0 := by
      by_contra h; push_neg at h; exact hψ0 (funext h)
    have hz0b : z0 ∈ ball (0 : ℂ) 1 := by
      by_contra h; exact hz0 (test_eq_zero_of_not_mem hψ h)
    have hh : (fun x => a x ^ 2 * ψ x) ∈ testFunctions (ball (0 : ℂ) 1) :=
      test_mul_smooth hψ hw.smooth
    have hpos : 0 < ∫ x, (a x ^ 2 * ψ x) * ψ x :=
      Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := z0)
        (hh.1.continuous.mul hψ.1.continuous) (hψ.2.1.mul_left)
        (fun x => by
          show 0 ≤ a x ^ 2 * ψ x * ψ x
          nlinarith [sq_nonneg (a x * ψ x)])
        (by
          have := hw.pos z0 hz0b
          positivity)
    have e : ∫ x in ball (0 : ℂ) 1, (a x ^ 2 * ψ x) * ψ x = ∫ x, (a x ^ 2 * ψ x) * ψ x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        simp [test_eq_zero_of_not_mem hψ hx]
    have h2 : 0 < ‖weightLp hw hψ‖ ^ 2 := by rw [norm_weightLp_sq, e]; exact hpos
    by_contra hle
    push_neg at hle
    have h0 : ‖weightLp hw hψ‖ = 0 := le_antisymm hle (norm_nonneg _)
    rw [h0] at h2; simp at h2

/-- A nonzero element of a `j`-dimensional space of test functions with `a ψ ⊥ e₀, …, e_{c-1}`
for `c < j`. -/
theorem exists_orth_test (hw : WeightOK a A) {V : Submodule ℝ (ℂ → ℝ)}
    (hV : V ≤ testFunctions (ball 0 1)) {j c : ℕ} (hVj : Module.finrank ℝ V = j) (hc : c < j)
    (e : ℕ → Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1))) :
    ∃ (ψ : ℂ → ℝ) (hψV : ψ ∈ V), ψ ≠ 0 ∧ ∀ l < c, ⟪e l, weightLp hw (hV hψV)⟫_ℝ = 0 := by
  have hfd : FiniteDimensional ℝ V := Module.finite_of_finrank_pos (by omega)
  have hint : ∀ (l : ℕ) (ψ : V),
      Integrable (fun x => e l x * (a x * (ψ : ℂ → ℝ) x)) (volume.restrict (ball (0 : ℂ) 1)) := fun l ψ =>
    (Lp.memLp (e l)).integrable_mul (memLp_weight_test hw (hV ψ.2))
  let L : V →ₗ[ℝ] (Fin c → ℝ) :=
    { toFun := fun ψ l => ∫ x in ball (0 : ℂ) 1, e l x * (a x * (ψ : ℂ → ℝ) x)
      map_add' := fun ψ φ => by
        funext l
        simp only [Submodule.coe_add, Pi.add_apply]
        rw [← integral_add (hint l ψ) (hint l φ)]
        congr 1; funext x; ring
      map_smul' := fun r ψ => by
        funext l
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1; funext x; ring }
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := L) (by simp [hVj]; omega)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨x.1, x.2, fun h => hx0 (Subtype.ext h), fun l hl => ?_⟩
  rw [inner_weightLp]
  exact congrFun (LinearMap.mem_ker.1 hx) ⟨l, hl⟩

/-- **Lower bound** for the weighted min–max values. -/
theorem minmax_lower (hw : WeightOK a A) {n m : ℕ} {e : ℕ → Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1))} {μ : ℕ → ℝ}
    (hpos : ∀ i < m, 0 < μ i)
    (hmax : ∀ i < m, ∀ x, (∀ l < i, ⟪e l, x⟫_ℝ = 0) →
      ⟪greenOp hw.meas hw.bound x, x⟫_ℝ ≤ μ i * ‖x‖ ^ 2)
    (hstop : m < n → ∀ x, (∀ l < m, ⟪e l, x⟫_ℝ = 0) → ⟪greenOp hw.meas hw.bound x, x⟫_ℝ ≤ 0)
    {j : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ n)
    (hfin : minmax (testFunctions (ball 0 1)) (wRayleigh (fun η => a η ^ 2)) j < ⊤) :
    j ≤ m ∧ ENNReal.ofReal (1 / μ (j - 1)) ≤
      minmax (testFunctions (ball 0 1)) (wRayleigh (fun η => a η ^ 2)) j := by
  -- if `m < j`, no `j`-dimensional space of test functions exists
  have hjm : j ≤ m := by
    by_contra hlt
    push_neg at hlt
    apply (lt_top_iff_ne_top.1 hfin)
    unfold minmax
    refine iInf_eq_top.2 fun V => iInf_eq_top.2 fun hV => iInf_eq_top.2 fun hVj => ?_
    exfalso
    obtain ⟨ψ, hψV, hψ0, horth⟩ := exists_orth_test hw hV hVj hlt e
    obtain ⟨-, -, hkey, hpos'⟩ := key_lower hw (hV hψV)
    have h0 := hstop (lt_of_lt_of_le hlt hjn) _ horth
    have hE : 0 ≤ ∫ x in ball (0 : ℂ) 1, ‖fderiv ℝ ψ x‖ ^ 2 :=
      setIntegral_nonneg measurableSet_ball fun _ _ => by positivity
    have := hpos' hψ0
    nlinarith [mul_nonpos_of_nonpos_of_nonneg h0 hE, pow_pos this 4]
  refine ⟨hjm, ?_⟩
  have hμ := hpos (j - 1) (by omega)
  unfold minmax
  refine le_iInf fun V => le_iInf fun hV => le_iInf fun hVj => ?_
  obtain ⟨ψ, hψV, hψ0, horth⟩ := exists_orth_test hw hV hVj (show j - 1 < j by omega) e
  obtain ⟨hM, hE, hkey, hpos'⟩ := key_lower hw (hV hψV)
  refine le_trans ?_ (le_iSup_of_le ψ (le_iSup_of_le hψV
    (le_iSup (fun _ : ψ ≠ 0 => wRayleigh (fun η => a η ^ 2) ψ) hψ0)))
  have hT := hmax (j - 1) (by omega) _ horth
  set N := ‖weightLp hw (hV hψV)‖
  set E := ∫ x in ball (0 : ℂ) 1, ‖fderiv ℝ ψ x‖ ^ 2
  have hN := hpos' hψ0
  have hE0 : 0 ≤ E := setIntegral_nonneg measurableSet_ball fun _ _ => by positivity
  have hNE : N ^ 2 ≤ μ (j - 1) * E := by
    have h1 : N ^ 4 ≤ μ (j - 1) * N ^ 2 * E :=
      hkey.trans (mul_le_mul_of_nonneg_right hT hE0)
    have h2 : 0 < N ^ 2 := by positivity
    nlinarith
  unfold wRayleigh
  rw [hM, hE, ← ENNReal.ofReal_div_of_pos (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_div_iff₀ hμ (by positivity)]
  linarith

end


end

end



