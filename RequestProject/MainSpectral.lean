module

public import RequestProject.MainMiddle

@[expose] public section

noncomputable section

section

/-! ## Density of test functions and the weak Green representation -/

open MeasureTheory Set Real Metric Filter Topology
open scoped ComplexConjugate InnerProductSpace

lemma integral_sq_le_of_eLpNorm_le {h : ℂ → ℝ} (hh : MemLp h 2 (volume.restrict (ball (0 : ℂ) 1))) {ε : ℝ} (hε : 0 ≤ ε)
    (H : eLpNorm h 2 (volume.restrict (ball (0 : ℂ) 1)) ≤ ENNReal.ofReal ε) : ∫ x in ball (0 : ℂ) 1, h x ^ 2 ≤ ε ^ 2 := by
  rw [hh.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.ofReal_le_ofReal_iff hε] at H
  have e : (fun x => ‖h x‖ ^ (2 : ENNReal).toReal) = fun x => h x ^ 2 := by
    funext x; simp [Real.norm_eq_abs, sq_abs]
  rw [e] at H
  have hI : 0 ≤ ∫ x in ball (0 : ℂ) 1, h x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have h2 : ((2 : ENNReal).toReal)⁻¹ = (1 / 2 : ℝ) := by norm_num
  rw [h2, ← Real.sqrt_eq_rpow] at H
  calc ∫ x in ball (0 : ℂ) 1, h x ^ 2 = (√(∫ x in ball (0 : ℂ) 1, h x ^ 2)) ^ 2 :=
        (Real.sq_sqrt hI).symm
    _ ≤ ε ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) H 2

lemma cutB_mul_test {g : ℂ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    {t : ℝ} (ht : 0 < t) : (fun x => cutB t x * g x) ∈ testFunctions (ball (0 : ℂ) 1) := by
  have hsupp : Function.support (fun x => cutB t x * g x) ⊆ {z : ℂ | ‖z‖ ^ 2 ≤ 1 - t} := by
    intro z hz
    by_contra h
    simp only [mem_setOf_eq, not_le] at h
    exact hz (by simp [cutB_eq_zero ht (by linarith)])
  have hcl : IsClosed {z : ℂ | ‖z‖ ^ 2 ≤ 1 - t} :=
    isClosed_le (continuous_norm.pow 2) continuous_const
  refine ⟨(contDiff_cutB t).mul hg, hgc.mul_left, (closure_minimal hsupp hcl).trans ?_⟩
  intro z hz
  simp only [mem_setOf_eq] at hz
  rw [mem_ball_zero_iff]
  nlinarith [norm_nonneg z]

/-- **Density of test functions** in `L²(𝔻)`. -/
theorem exists_test_approx {f : ℂ → ℝ} (hf : MemLp f 2 (volume.restrict (ball (0 : ℂ) 1))) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q ∈ testFunctions (ball (0 : ℂ) 1), ∫ x in ball (0 : ℂ) 1, (f x - q x) ^ 2 ≤ δ := by
  haveI : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) 1)) := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  obtain ⟨g, hgc, hg, hfg⟩ := hf.exist_eLpNorm_sub_le (by norm_num) (by norm_num)
    (show 0 < √(δ / 4) by positivity)
  have hgL : MemLp g 2 (volume.restrict (ball (0 : ℂ) 1)) := (hg.continuous.memLp_of_hasCompactSupport hgc).restrict _
  have h1 : ∫ x in ball (0 : ℂ) 1, (f x - g x) ^ 2 ≤ δ / 4 := by
    have := integral_sq_le_of_eLpNorm_le (hf.sub hgL) (Real.sqrt_nonneg _) hfg
    rwa [Real.sq_sqrt (by positivity)] at this
  obtain ⟨M, hM⟩ := hg.continuous.bounded_above_of_compact_support hgc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set t := min (1 / 2) (δ / (4 * (2 * π) * (M ^ 2 + 1)))
  have ht : 0 < t := lt_min (by norm_num) (by positivity)
  have ht2 : t ≤ 1 / 2 := min_le_left _ _
  refine ⟨_, cutB_mul_test hg hgc ht, ?_⟩
  have hq := cutB_mul_test hg hgc ht
  have hqL : MemLp (fun x => cutB t x * g x) 2 (volume.restrict (ball (0 : ℂ) 1)) := test_memLp hq
  -- the cutoff error
  have h2 : ∫ x in ball (0 : ℂ) 1, (g x - cutB t x * g x) ^ 2 ≤ δ / 4 := by
    have hint : IntegrableOn (fun x => (g x - cutB t x * g x) ^ 2) (ball (0 : ℂ) 1) :=
      (hgL.sub hqL).integrable_sq
    have hb := abs_setIntegral_le_layer ht ht2 (K := M ^ 2) (sq_nonneg _) hint
      (fun z _ => by
        rw [abs_of_nonneg (sq_nonneg _)]
        have h0 := cutB_nonneg t z
        have h1 := cutB_le_one t z
        have hgz : |g z| ≤ M := by simpa using hM z
        have : |g z - cutB t z * g z| ≤ M := by
          rw [show g z - cutB t z * g z = (1 - cutB t z) * g z by ring, abs_mul,
            abs_of_nonneg (by linarith)]
          nlinarith [abs_nonneg (g z)]
        calc (g z - cutB t z * g z) ^ 2 = |g z - cutB t z * g z| ^ 2 := (sq_abs _).symm
          _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2)
      (fun z hz hzA => by
        have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
        simp only [annLayer, mem_setOf_eq, not_and_or, not_le] at hzA
        rcases hzA with h | h
        · rw [cutB_eq_one ht (by linarith)]; ring
        · nlinarith [norm_nonneg z])
    have hle : M ^ 2 * (2 * π * t) ≤ δ / 4 := by
      have htle : t ≤ δ / (4 * (2 * π) * (M ^ 2 + 1)) := min_le_right _ _
      calc M ^ 2 * (2 * π * t) ≤ (M ^ 2 + 1) * (2 * π) * t := by nlinarith [pi_pos]
        _ ≤ (M ^ 2 + 1) * (2 * π) * (δ / (4 * (2 * π) * (M ^ 2 + 1))) := by
          gcongr
        _ = δ / 4 := by field_simp
    exact (le_abs_self _).trans (hb.trans hle)
  have hint1 : IntegrableOn (fun x => (f x - g x) ^ 2) (ball (0 : ℂ) 1) :=
    (hf.sub hgL).integrable_sq
  have hint2 : IntegrableOn (fun x => (g x - cutB t x * g x) ^ 2) (ball (0 : ℂ) 1) :=
    (hgL.sub hqL).integrable_sq
  calc ∫ x in ball (0 : ℂ) 1, (f x - cutB t x * g x) ^ 2
      ≤ ∫ x in ball (0 : ℂ) 1, (2 * (f x - g x) ^ 2 + 2 * (g x - cutB t x * g x) ^ 2) := by
        refine setIntegral_mono_on (hf.sub hqL).integrable_sq
          ((hint1.const_mul 2).add (hint2.const_mul 2)) measurableSet_ball fun x _ => ?_
        nlinarith [sq_nonneg (f x - 2 * g x + cutB t x * g x)]
    _ = 2 * (∫ x in ball (0 : ℂ) 1, (f x - g x) ^ 2) +
          2 * ∫ x in ball (0 : ℂ) 1, (g x - cutB t x * g x) ^ 2 := by
        rw [integral_add (hint1.const_mul 2) (hint2.const_mul 2), integral_const_mul,
          integral_const_mul]
    _ ≤ δ := by linarith

lemma memLp_greenPotD {f : ℂ → ℝ} (hf : MemLp f 2 (volume.restrict (ball (0 : ℂ) 1))) (hfm : StronglyMeasurable f) :
    MemLp (greenPotD f) 2 (volume.restrict (ball (0 : ℂ) 1)) :=
  MemLp.of_bound (stronglyMeasurable_greenPotD hfm).aestronglyMeasurable _ (by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    rw [Real.norm_eq_abs]
    exact abs_greenPotD_le hf (mem_ball_zero_iff.1 hz).le)

lemma memLp_of_continuousOn_closedBall {φ : ℂ → ℝ} (hφ : ContinuousOn φ (closedBall 0 1)) :
    MemLp φ 2 (volume.restrict (ball (0 : ℂ) 1)) := by
  obtain ⟨C, -, hC⟩ := exists_bound_closedBall hφ
  refine MemLp.of_bound ((hφ.mono ball_subset_closedBall).aestronglyMeasurable
    measurableSet_ball) C ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  rw [Real.norm_eq_abs]; exact hC z (ball_subset_closedBall hz)

lemma greenPotD_sub {f g : ℂ → ℝ} (hf : MemLp f 2 (volume.restrict (ball (0 : ℂ) 1))) (hg : MemLp g 2 (volume.restrict (ball (0 : ℂ) 1))) {w : ℂ}
    (hw : ‖w‖ ≤ 1) : greenPotD (fun η => f η - g η) w = greenPotD f w - greenPotD g w := by
  unfold greenPotD
  rw [← integral_sub (integrable_diskGreen_mul hf hw) (integrable_diskGreen_mul hg hw)]
  congr 1; funext η; ring

/-- **Weak Green representation.** -/
theorem integral_greenPotD_laplacian {f w : ℂ → ℝ} (hf : MemLp f 2 (volume.restrict (ball (0 : ℂ) 1)))
    (hfm : StronglyMeasurable f) (hw : DiskNice w) :
    ∫ x in ball (0 : ℂ) 1, greenPotD f x * Laplacian.laplacian w x =
      -∫ x in ball (0 : ℂ) 1, f x * w x := by
  have hL2 := memLp_of_continuousOn_closedBall hw.laplacian_continuousOn
  have hw2 := memLp_of_continuousOn_closedBall hw.continuousOn
  set K1 := √greenL2Const * ∫ x in ball (0 : ℂ) 1, |Laplacian.laplacian w x|
  set K2 := √(∫ x in ball (0 : ℂ) 1, w x ^ 2)
  have hK1 : 0 ≤ K1 := mul_nonneg (Real.sqrt_nonneg _)
    (integral_nonneg fun _ => abs_nonneg _)
  have hK2 : 0 ≤ K2 := Real.sqrt_nonneg _
  rw [← sub_eq_zero, sub_neg_eq_add]
  refine eq_zero_of_abs_le_mul_all (c := K1 + K2) (add_nonneg hK1 hK2) fun ε hε => ?_
  obtain ⟨q, hq, hfq⟩ := exists_test_approx hf (show 0 < ε ^ 2 by positivity)
  have hqL := test_memLp hq
  have hqm : StronglyMeasurable q := hq.1.continuous.stronglyMeasurable
  set I := ∫ x in ball (0 : ℂ) 1, (f x - q x) ^ 2
  have hI : √I ≤ ε := by
    rw [show ε = √(ε ^ 2) by rw [Real.sqrt_sq hε.le]]; exact Real.sqrt_le_sqrt hfq
  -- the identity for test functions
  obtain ⟨hWn, hWL, hWeq⟩ := greenPot_test hq
  have hq_id : ∫ x in ball (0 : ℂ) 1, greenPotD q x * Laplacian.laplacian w x =
      -∫ x in ball (0 : ℂ) 1, q x * w x := by
    simp_rw [hWeq]
    rw [hWn.green_second hw, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_ball fun x hx => ?_
    rw [hWL x hx]; ring
  -- error terms
  have hfqL : MemLp (fun x => f x - q x) 2 (volume.restrict (ball (0 : ℂ) 1)) := hf.sub hqL
  have hfqm : StronglyMeasurable (fun x => f x - q x) := hfm.sub hqm
  have hu := memLp_greenPotD hfqL hfqm
  have e1 : (∫ x in ball (0 : ℂ) 1, greenPotD f x * Laplacian.laplacian w x) -
      ∫ x in ball (0 : ℂ) 1, greenPotD q x * Laplacian.laplacian w x =
      ∫ x in ball (0 : ℂ) 1, greenPotD (fun η => f η - q η) x * Laplacian.laplacian w x := by
    rw [← integral_sub (f := fun x => greenPotD f x * Laplacian.laplacian w x)
      (g := fun x => greenPotD q x * Laplacian.laplacian w x)
      ((memLp_greenPotD hf hfm).integrable_mul hL2)
      ((memLp_greenPotD hqL hqm).integrable_mul hL2)]
    refine setIntegral_congr_fun measurableSet_ball fun x hx => ?_
    rw [greenPotD_sub hf hqL (mem_ball_zero_iff.1 hx).le]; ring
  have b1 : |∫ x in ball (0 : ℂ) 1, greenPotD (fun η => f η - q η) x *
      Laplacian.laplacian w x| ≤ K1 * √I := by
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ x in ball (0 : ℂ) 1, |greenPotD (fun η => f η - q η) x * Laplacian.laplacian w x|
        ≤ ∫ x in ball (0 : ℂ) 1, (√greenL2Const * √I) * |Laplacian.laplacian w x| := by
          refine setIntegral_mono_on (hu.integrable_mul hL2).abs
            (((hL2.integrable (by norm_num)).abs).const_mul (√greenL2Const * √I))
            measurableSet_ball fun x hx => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right
            (abs_greenPotD_le hfqL (mem_ball_zero_iff.1 hx).le) (abs_nonneg _)
      _ = K1 * √I := by rw [integral_const_mul]; ring
  have b2 : |(∫ x in ball (0 : ℂ) 1, f x * w x) - ∫ x in ball (0 : ℂ) 1, q x * w x| ≤
      √I * K2 := by
    rw [← integral_sub (f := fun x => f x * w x) (g := fun x => q x * w x)
      (hf.integrable_mul hw2) (hqL.integrable_mul hw2)]
    have := abs_integral_mul_le_sqrt hfqL hw2
    simpa [sub_mul] using this
  have key : (∫ x in ball (0 : ℂ) 1, greenPotD f x * Laplacian.laplacian w x) +
      ∫ x in ball (0 : ℂ) 1, f x * w x =
      (∫ x in ball (0 : ℂ) 1, greenPotD (fun η => f η - q η) x * Laplacian.laplacian w x) +
      ((∫ x in ball (0 : ℂ) 1, f x * w x) - ∫ x in ball (0 : ℂ) 1, q x * w x) := by
    rw [← e1, hq_id]; ring
  rw [key]
  refine (abs_add_le _ _).trans ?_
  calc _ ≤ K1 * √I + √I * K2 := add_le_add b1 b2
    _ = (K1 + K2) * √I := by ring
    _ ≤ (K1 + K2) * ε := mul_le_mul_of_nonneg_left hI (add_nonneg hK1 hK2)

end

section

/-! ## Cutting off functions vanishing on the unit circle -/

open MeasureTheory Set Real Metric Filter Topology
open scoped ComplexConjugate InnerProductSpace

/-- Green potentials of test functions are smooth on a neighbourhood of `𝔻̄`. -/
lemma greenPot_test_smooth {q : ℂ → ℝ} (hq : q ∈ testFunctions (ball (0 : ℂ) 1)) :
    ∃ R > 1, ContDiffOn ℝ (⊤ : ℕ∞) (greenPot q) (ball 0 R) := by
  obtain ⟨M, ρ₀, h0, h1, hb⟩ := test_bddSupp hq
  exact greenPot_smooth_of_smooth hq.1 hq.2.1 h0 h1 hb.supp

/-- Cut-offs of functions smooth near `𝔻̄` are test functions. -/
lemma cutB_mul_smooth_test {w : ℂ → ℝ} {R : ℝ} (hR : 1 < R)
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w (ball 0 R)) {t : ℝ} (ht : 0 < t) :
    (fun x => cutB t x * w x) ∈ testFunctions (ball (0 : ℂ) 1) := by
  have hsupp : Function.support (fun x => cutB t x * w x) ⊆ {z : ℂ | ‖z‖ ^ 2 ≤ 1 - t} := by
    intro z hz
    by_contra h
    simp only [mem_setOf_eq, not_le] at h
    exact hz (by simp [cutB_eq_zero ht (by linarith)])
  have hcl : IsClosed {z : ℂ | ‖z‖ ^ 2 ≤ 1 - t} :=
    isClosed_le (continuous_norm.pow 2) continuous_const
  have hsub : {z : ℂ | ‖z‖ ^ 2 ≤ 1 - t} ⊆ ball 0 1 := by
    intro z hz
    simp only [mem_setOf_eq] at hz
    rw [mem_ball_zero_iff]
    nlinarith [norm_nonneg z]
  have hts : tsupport (fun x => cutB t x * w x) ⊆ {z : ℂ | ‖z‖ ^ 2 ≤ 1 - t} :=
    closure_minimal hsupp hcl
  refine ⟨?_, HasCompactSupport.intro ((isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset hcl
    (hsub.trans ball_subset_closedBall)) fun z hz => by
      by_contra h; exact hz (hsupp h), hts.trans hsub⟩
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  by_cases hz : z ∈ ball (0 : ℂ) R
  · exact (contDiff_cutB t).contDiffAt.mul (hw.contDiffAt (isOpen_ball.mem_nhds hz))
  · have hz1 : z ∉ closedBall (0 : ℂ) 1 := fun h =>
      hz (closedBall_subset_ball hR h)
    have hev : (fun x => cutB t x * w x) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hz1] with y hy
      have : y ∉ {z : ℂ | ‖z‖ ^ 2 ≤ 1 - t} := fun h =>
        hy (ball_subset_closedBall (hsub h))
      by_contra h; exact this (hsupp h)
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- Functions vanishing on `𝕋` are `O(1 - |z|)`. -/
lemma abs_le_boundary_dist {w : ℂ → ℝ} (hw : DiskNice w) :
    ∃ L, 0 ≤ L ∧ (∀ z ∈ closedBall (0 : ℂ) 1, ‖fderiv ℝ w z‖ ≤ L) ∧
      ∀ z ∈ closedBall (0 : ℂ) 1, |w z| ≤ L * (1 - ‖z‖) := by
  obtain ⟨L0, hL0⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hw.fderiv_continuousOn
  set L := max L0 0
  have hL : ∀ z ∈ closedBall (0 : ℂ) 1, ‖fderiv ℝ w z‖ ≤ L := fun z hz =>
    (by simpa using hL0 z hz : ‖fderiv ℝ w z‖ ≤ L0).trans (le_max_left _ _)
  refine ⟨L, le_max_right _ _, hL, fun z hz => ?_⟩
  have hz1 : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.1 hz
  obtain ⟨p, hp1, hzp⟩ : ∃ p : ℂ, ‖p‖ = 1 ∧ ‖z - p‖ = 1 - ‖z‖ := by
    by_cases h0 : z = 0
    · exact ⟨1, by simp, by simp [h0]⟩
    · have hn : (0 : ℝ) < ‖z‖ := norm_pos_iff.2 h0
      refine ⟨z / (‖z‖ : ℂ), by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn, div_self hn.ne'], ?_⟩
      have e : z - z / (‖z‖ : ℂ) = ((‖z‖ - 1) / ‖z‖ : ℝ) • z := by
        have hc : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
        rw [Complex.real_smul]; push_cast; field_simp
      rw [e, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hn, abs_of_nonpos (by linarith)]
      field_simp
      ring
  have hpD : p ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.2 hp1.le
  have h := (convex_closedBall (0 : ℂ) 1).norm_image_sub_le_of_norm_fderiv_le
    (fun x hx => (hw.contDiffAt hx).differentiableAt (by norm_num)) hL hpD hz
  obtain ⟨-, -, -, -, h0⟩ := hw
  rw [h0 p (mem_sphere_zero_iff_norm.2 hp1), sub_zero, Real.norm_eq_abs, hzp] at h
  exact h

lemma fderiv_cutB_mul {w : ℂ → ℝ} (hw : DiskNice w) {t : ℝ} {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) 1) :
    fderiv ℝ (fun x => cutB t x * w x) z = cutB t z • fderiv ℝ w z + w z • fderiv ℝ (cutB t) z := by
  have h1 := ((contDiff_cutB t).differentiable (by simp) z).hasFDerivAt
  have h2 := ((hw.contDiffAt hz).differentiableAt (by norm_num)).hasFDerivAt
  exact (h1.mul h2).fderiv

/-- Uniform gradient bound for the cut-offs and agreement away from the boundary layer. -/
lemma cut_props {w : ℂ → ℝ} (hw : DiskNice w) :
    ∃ K, 0 ≤ K ∧ ∀ t, 0 < t → t ≤ 1 / 2 →
      (∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ (fun x => cutB t x * w x) z‖ ≤ K) ∧
      (∀ z ∈ ball (0 : ℂ) 1, z ∉ annLayer t →
        fderiv ℝ (fun x => cutB t x * w x) z = fderiv ℝ w z ∧ cutB t z = 1) := by
  obtain ⟨L, hL0, hLd, hLw⟩ := abs_le_boundary_dist hw
  obtain ⟨C, hC0, hC⟩ := exists_bound_deriv_smoothTransition
  refine ⟨L + 4 * L * C, by positivity, fun t ht ht2 => ⟨fun z hz => ?_, fun z hz hzA => ?_⟩⟩
  · have hzc := ball_subset_closedBall hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
    rw [fderiv_cutB_mul hw hzc]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (cutB_nonneg t z)]
    have e1 : cutB t z * ‖fderiv ℝ w z‖ ≤ L :=
      (mul_le_of_le_one_left (norm_nonneg _) (cutB_le_one t z)).trans (hLd z hzc)
    have e2 : |w z| * ‖fderiv ℝ (cutB t) z‖ ≤ 4 * L * C := by
      by_cases hA : z ∈ annLayer t
      · have hd : ‖fderiv ℝ (cutB t) z‖ ≤ C * (2 * ‖z‖ / t) := norm_fderiv_cutB_le ht hC0 hC z
        have hd' : ‖fderiv ℝ (cutB t) z‖ ≤ 2 * C / t := by
          refine hd.trans ?_
          rw [mul_div_assoc', div_le_div_iff_of_pos_right ht]
          nlinarith [norm_nonneg z]
        have hw' : |w z| ≤ L * (2 * t) := by
          refine (hLw z hzc).trans (mul_le_mul_of_nonneg_left ?_ hL0)
          have := hA.1
          nlinarith [norm_nonneg z]
        calc |w z| * ‖fderiv ℝ (cutB t) z‖ ≤ L * (2 * t) * (2 * C / t) :=
              mul_le_mul hw' hd' (norm_nonneg _) (by positivity)
          _ = 4 * L * C := by field_simp; ring
      · rw [fderiv_cutB_eq_zero ht hA, norm_zero, mul_zero]; positivity
    linarith
  · have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
    have hlt : ‖z‖ ^ 2 < 1 - 2 * t := by
      simp only [annLayer, mem_setOf_eq, not_and_or, not_le] at hzA
      rcases hzA with h | h
      · exact h
      · nlinarith [norm_nonneg z]
    have hc : Continuous fun y : ℂ => 1 - ‖y‖ ^ 2 := continuous_const.sub (continuous_norm.pow 2)
    have hev : (fun x => cutB t x * w x) =ᶠ[𝓝 z] w := by
      filter_upwards [(isOpen_lt continuous_const hc).mem_nhds
        (show 2 * t < 1 - ‖z‖ ^ 2 by linarith)] with y hy
      rw [cutB_eq_one ht hy.le, one_mul]
    exact ⟨hev.fderiv_eq, cutB_eq_one ht (by linarith)⟩

/-- **Gram entries of cut-offs** differ from those of the original functions by `O(t)`. -/
theorem cut_gram_close {w v : ℂ → ℝ} (hw : DiskNice w) (hv : DiskNice v) {ρ : ℂ → ℝ}
    (hρ : ContinuousOn ρ (ball 0 1)) {B : ℝ} (hB : ∀ z ∈ ball (0 : ℂ) 1, |ρ z| ≤ B) :
    ∃ K, 0 ≤ K ∧ ∀ t, 0 < t → t ≤ 1 / 2 →
      |(∫ z in ball (0 : ℂ) 1, gradInner (fderiv ℝ (fun x => cutB t x * w x) z)
          (fderiv ℝ (fun x => cutB t x * v x) z)) -
        ∫ z in ball (0 : ℂ) 1, gradInner (fderiv ℝ w z) (fderiv ℝ v z)| ≤ K * t ∧
      |(∫ z in ball (0 : ℂ) 1, ρ z * (cutB t z * w z) * (cutB t z * v z)) -
        ∫ z in ball (0 : ℂ) 1, ρ z * w z * v z| ≤ K * t := by
  haveI : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) 1)) := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  obtain ⟨Kw, hKw0, hKw⟩ := cut_props hw
  obtain ⟨Kv, hKv0, hKv⟩ := cut_props hv
  obtain ⟨Lw, hLw0, hLw, -⟩ := abs_le_boundary_dist hw
  obtain ⟨Lv, hLv0, hLv, -⟩ := abs_le_boundary_dist hv
  obtain ⟨Bw, hBw0, hBw⟩ := exists_bound_closedBall hw.continuousOn
  obtain ⟨Bv, hBv0, hBv⟩ := exists_bound_closedBall hv.continuousOn
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 (mem_ball_self one_pos))
  set K1 := 2 * (Kw * Kv) + 2 * (Lw * Lv)
  set K2 := 2 * (B * (Bw * Bv))
  have hK1n : 0 ≤ K1 := by positivity
  have hK2n : 0 ≤ K2 := mul_nonneg (by norm_num) (mul_nonneg hB0 (mul_nonneg hBw0 hBv0))
  refine ⟨(K1 + K2) * (2 * π), by positivity, fun t ht ht2 => ⟨?_, ?_⟩⟩
  · -- energy
    obtain ⟨hK1, hK2⟩ := hKw t ht ht2
    obtain ⟨hK3, hK4⟩ := hKv t ht ht2
    have hcw : ContDiffOn ℝ 2 (fun x => cutB t x * w x) (hw.choose) :=
      ((contDiff_cutB t).of_le (by norm_cast)).contDiffOn.mul hw.choose_spec.2.2.1
    have hcv : ContDiffOn ℝ 2 (fun x => cutB t x * v x) (hv.choose) :=
      ((contDiff_cutB t).of_le (by norm_cast)).contDiffOn.mul hv.choose_spec.2.2.1
    have hdw : ContinuousOn (fderiv ℝ (fun x => cutB t x * w x)) (closedBall 0 1) :=
      (hcw.continuousOn_fderiv_of_isOpen hw.choose_spec.1 (by norm_num)).mono
        hw.choose_spec.2.1
    have hdv : ContinuousOn (fderiv ℝ (fun x => cutB t x * v x)) (closedBall 0 1) :=
      (hcv.continuousOn_fderiv_of_isOpen hv.choose_spec.1 (by norm_num)).mono
        hv.choose_spec.2.1
    have gc : ∀ {P Q : ℂ → ℂ →L[ℝ] ℝ}, ContinuousOn P (closedBall 0 1) →
        ContinuousOn Q (closedBall 0 1) →
        IntegrableOn (fun z => gradInner (P z) (Q z)) (ball (0 : ℂ) 1) := fun hP hQ =>
      DiskNice.integrableOn_ball_of_continuousOn (by
        unfold gradInner
        exact ((hP.clm_apply continuousOn_const).mul (hQ.clm_apply continuousOn_const)).add
          ((hP.clm_apply continuousOn_const).mul (hQ.clm_apply continuousOn_const)))
    have i1 := gc hdw hdv
    have i2 := gc hw.fderiv_continuousOn hv.fderiv_continuousOn
    rw [← integral_sub i1 i2]
    have h := abs_setIntegral_le_layer ht ht2 (K := K1) (by positivity) (i1.sub i2)
      (fun z hz => by
        have hzc := ball_subset_closedBall hz
        rw [Pi.sub_apply]
        refine (abs_sub _ _).trans (add_le_add ?_ ?_)
        · refine (abs_gradInner_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_left (mul_le_mul (hK1 z hz) (hK3 z hz) (norm_nonneg _)
            hKw0) (by norm_num)
        · refine (abs_gradInner_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_left (mul_le_mul (hLw z hzc) (hLv z hzc) (norm_nonneg _)
            hLw0) (by norm_num))
      (fun z hz hzA => by
        simp only [Pi.sub_apply, (hK2 z hz hzA).1, (hK4 z hz hzA).1, sub_self])
    calc _ ≤ K1 * (2 * π * t) := h
      _ ≤ (K1 + K2) * (2 * π) * t := by
        have := mul_nonneg hK2n (show 0 ≤ 2 * π * t by positivity)
        linarith
  · -- mass
    have hρm : AEStronglyMeasurable ρ (volume.restrict (ball (0 : ℂ) 1)) := hρ.aestronglyMeasurable measurableSet_ball
    have i1 : IntegrableOn (fun z => ρ z * (cutB t z * w z) * (cutB t z * v z)) (ball 0 1) := by
      refine Integrable.of_bound ((hρm.mul ((((contDiff_cutB t).continuous.continuousOn.mul
        hw.continuousOn).mono ball_subset_closedBall).aestronglyMeasurable
        measurableSet_ball)).mul ((((contDiff_cutB t).continuous.continuousOn.mul
        hv.continuousOn).mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball))
        (B * (Bw * Bv)) ?_
      filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      have hzc := ball_subset_closedBall hz
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (cutB_nonneg t z), mul_assoc]
      refine mul_le_mul (hB z hz) ?_ (mul_nonneg (mul_nonneg (cutB_nonneg t z) (abs_nonneg _))
        (mul_nonneg (cutB_nonneg t z) (abs_nonneg _))) hB0
      exact mul_le_mul ((mul_le_of_le_one_left (abs_nonneg _) (cutB_le_one t z)).trans
        (hBw z hzc)) ((mul_le_of_le_one_left (abs_nonneg _) (cutB_le_one t z)).trans
        (hBv z hzc)) (mul_nonneg (cutB_nonneg t z) (abs_nonneg _)) hBw0
    have i2 : IntegrableOn (fun z => ρ z * w z * v z) (ball 0 1) := by
      refine Integrable.of_bound ((hρm.mul ((hw.continuousOn.mono
        ball_subset_closedBall).aestronglyMeasurable measurableSet_ball)).mul
        ((hv.continuousOn.mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball))
        (B * (Bw * Bv)) ?_
      filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      have hzc := ball_subset_closedBall hz
      rw [Real.norm_eq_abs, abs_mul, abs_mul, mul_assoc]
      exact mul_le_mul (hB z hz) (mul_le_mul (hBw z hzc) (hBv z hzc) (abs_nonneg _) hBw0)
        (by positivity) hB0
    rw [← integral_sub i1 i2]
    have h := abs_setIntegral_le_layer ht ht2 (K := K2) (by positivity) (i1.sub i2)
      (fun z hz => by
        have hzc := ball_subset_closedBall hz
        have e : ρ z * (cutB t z * w z) * (cutB t z * v z) - ρ z * w z * v z =
            ρ z * w z * v z * (cutB t z ^ 2 - 1) := by ring
        simp only [Pi.sub_apply]
        rw [e, abs_mul, abs_mul, abs_mul]
        have hb : |cutB t z ^ 2 - 1| ≤ 2 := by
          have := cutB_nonneg t z; have := cutB_le_one t z
          rw [abs_le]; constructor <;> nlinarith
        calc |ρ z| * |w z| * |v z| * |cutB t z ^ 2 - 1| ≤ B * Bw * Bv * 2 := by
              gcongr
              · exact hB z hz
              · exact hBw z hzc
              · exact hBv z hzc
          _ = K2 := by ring)
      (fun z hz hzA => by
        simp only [Pi.sub_apply, (hKw t ht ht2).2 z hz hzA |>.2]
        ring)
    calc _ ≤ K2 * (2 * π * t) := h
      _ ≤ (K1 + K2) * (2 * π) * t := by
        have := mul_nonneg hK1n (show 0 ≤ 2 * π * t by positivity)
        linarith

end

section

/-! ## Upper bound for the weighted min–max values -/

open MeasureTheory Set Real Metric Filter Topology
open scoped ComplexConjugate InnerProductSpace

variable {a : ℂ → ℝ} {A : ℝ}

/-! ### Gram matrices -/

/-- The energy Gram matrix `∫_𝔻 ∇ψᵢ · ∇ψₗ`. -/
def gramE {j : ℕ} (ψ : Fin j → ℂ → ℝ) (i l : Fin j) : ℝ :=
  ∫ x in ball (0 : ℂ) 1, gradInner (fderiv ℝ (ψ i) x) (fderiv ℝ (ψ l) x)

/-- The weighted mass Gram matrix `∫_𝔻 a² ψᵢ ψₗ`. -/
def gramM (a : ℂ → ℝ) {j : ℕ} (ψ : Fin j → ℂ → ℝ) (i l : Fin j) : ℝ :=
  ∫ x in ball (0 : ℂ) 1, a x ^ 2 * ψ i x * ψ l x

lemma test_fderiv_continuous {ψ : ℂ → ℝ} (hψ : ψ ∈ testFunctions (ball (0 : ℂ) 1)) :
    Continuous (fderiv ℝ ψ) :=
  hψ.1.continuous_fderiv (by simp)

lemma energy_sum {j : ℕ} {ψ : Fin j → ℂ → ℝ} (hψ : ∀ i, ψ i ∈ testFunctions (ball (0 : ℂ) 1))
    (c : Fin j → ℝ) :
    ∫ x in ball (0 : ℂ) 1, ‖fderiv ℝ (fun y => ∑ i, c i * ψ i y) x‖ ^ 2 =
      ∑ i, ∑ l, c i * c l * gramE ψ i l := by
  have hD : ∀ x, fderiv ℝ (fun y => ∑ i, c i * ψ i y) x = ∑ i, c i • fderiv ℝ (ψ i) x := by
    intro x
    exact (HasFDerivAt.fun_sum (u := Finset.univ) (A := fun i y => c i * ψ i y)
      (A' := fun i => c i • fderiv ℝ (ψ i) x) fun i _ =>
        (((hψ i).1.differentiable (by simp) x).hasFDerivAt.const_mul (c i))).fderiv
  have hpt : ∀ x, ‖fderiv ℝ (fun y => ∑ i, c i * ψ i y) x‖ ^ 2 =
      ∑ i, ∑ l, c i * c l * gradInner (fderiv ℝ (ψ i) x) (fderiv ℝ (ψ l) x) := by
    intro x
    rw [hD, ← gradInner_self]
    simp only [gradInner, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  have hint : ∀ i l, IntegrableOn (fun x => gradInner (fderiv ℝ (ψ i) x) (fderiv ℝ (ψ l) x))
      (ball (0 : ℂ) 1) := fun i l =>
    DiskNice.integrableOn_ball_of_continuousOn (by
      unfold gradInner
      have h1 := test_fderiv_continuous (hψ i)
      have h2 := test_fderiv_continuous (hψ l)
      exact (((h1.clm_apply continuous_const).mul (h2.clm_apply continuous_const)).add
        ((h1.clm_apply continuous_const).mul (h2.clm_apply continuous_const))).continuousOn)
  simp_rw [hpt]
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun l _ => (hint i l).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ fun l _ => (hint i l).const_mul _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul]; rfl

lemma mass_sum (hw : WeightOK a A) {j : ℕ} {ψ : Fin j → ℂ → ℝ}
    (hψ : ∀ i, ψ i ∈ testFunctions (ball (0 : ℂ) 1)) (c : Fin j → ℝ) :
    ∫ x in ball (0 : ℂ) 1, (a x ^ 2 * (∑ i, c i * ψ i x)) * (∑ i, c i * ψ i x) =
      ∑ i, ∑ l, c i * c l * gramM a ψ i l := by
  have hpt : ∀ x, (a x ^ 2 * (∑ i, c i * ψ i x)) * (∑ i, c i * ψ i x) =
      ∑ i, ∑ l, c i * c l * (a x ^ 2 * ψ i x * ψ l x) := by
    intro x
    rw [show ∀ S : ℝ, (a x ^ 2 * S) * S = a x ^ 2 * (S * S) from fun S => by ring,
      Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hint : ∀ i l, IntegrableOn (fun x => a x ^ 2 * ψ i x * ψ l x) (ball (0 : ℂ) 1) :=
    fun i l => DiskNice.integrableOn_ball_of_continuousOn
      ((test_mul_smooth (hψ i) hw.smooth).1.continuous.mul (hψ l).1.continuous).continuousOn
  simp_rw [hpt]
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun l _ => (hint i l).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ fun l _ => (hint i l).const_mul _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul]; rfl

lemma massW_test (hw : WeightOK a A) {ψ : ℂ → ℝ} (hψ : ψ ∈ testFunctions (ball (0 : ℂ) 1)) :
    massW (fun η => a η ^ 2) ψ = ENNReal.ofReal (∫ x in ball (0 : ℂ) 1, (a x ^ 2 * ψ x) * ψ x) := by
  rw [massW_weight hw hψ, norm_weightLp_sq]

/-- The quadratic-form estimate behind the upper bound. -/
lemma quad_bound {j : ℕ} (μ' : Fin j → ℝ) {ν η : ℝ} (hν : 0 < ν) (hμν : ∀ i, ν ≤ μ' i) (hη : 0 ≤ η)
    (E M : Fin j → Fin j → ℝ)
    (hE : ∀ i l, |E i l - if i = l then μ' i else 0| ≤ η)
    (hM : ∀ i l, |M i l - if i = l then μ' i ^ 2 else 0| ≤ η) (c : Fin j → ℝ) :
    ∑ i, ∑ l, c i * c l * E i l ≤ (∑ i, c i ^ 2 * μ' i ^ 2) / ν + η * j * ∑ i, c i ^ 2 ∧
    (∑ i, c i ^ 2 * μ' i ^ 2) - η * j * ∑ i, c i ^ 2 ≤ ∑ i, ∑ l, c i * c l * M i l ∧
    ν ^ 2 * ∑ i, c i ^ 2 ≤ ∑ i, c i ^ 2 * μ' i ^ 2 := by
  classical
  have hcs : (∑ i, |c i|) ^ 2 ≤ j * ∑ i, c i ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin j))) (f := fun i => |c i|)
    simpa [sq_abs] using this
  have herr : ∀ (X : Fin j → Fin j → ℝ) (d : Fin j → ℝ),
      (∀ i l, |X i l - if i = l then d i else 0| ≤ η) →
      |∑ i, ∑ l, c i * c l * X i l - ∑ i, c i ^ 2 * d i| ≤ η * j * ∑ i, c i ^ 2 := by
    intro X d hX
    have e : ∑ i, ∑ l, c i * c l * X i l - ∑ i, c i ^ 2 * d i =
        ∑ i, ∑ l, c i * c l * (X i l - if i = l then d i else 0) := by
      have : ∀ i, c i ^ 2 * d i = ∑ l, c i * c l * (if i = l then d i else 0) := fun i => by
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]; ring
      simp_rw [this, ← Finset.sum_sub_distrib, mul_sub]
    rw [e]
    calc |∑ i, ∑ l, c i * c l * (X i l - if i = l then d i else 0)|
        ≤ ∑ i, ∑ l, |c i| * |c l| * η := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left (hX i l) (by positivity)
      _ = η * (∑ i, |c i|) ^ 2 := by
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring
      _ ≤ η * (j * ∑ i, c i ^ 2) := mul_le_mul_of_nonneg_left hcs hη
      _ = η * j * ∑ i, c i ^ 2 := by ring
  have hE' := herr E μ' hE
  have hM' := herr M (fun i => μ' i ^ 2) hM
  have h1 : ∑ i, c i ^ 2 * μ' i ≤ (∑ i, c i ^ 2 * μ' i ^ 2) / ν := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [le_div_iff₀ hν]
    have := hμν i
    have h0 : 0 ≤ c i ^ 2 * μ' i := mul_nonneg (sq_nonneg _) (hν.le.trans this)
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · linarith [le_abs_self (∑ i, ∑ l, c i * c l * E i l - ∑ i, c i ^ 2 * μ' i)]
  · linarith [neg_abs_le (∑ i, ∑ l, c i * c l * M i l - ∑ i, c i ^ 2 * μ' i ^ 2)]
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have := hμν i
    have : ν ^ 2 ≤ μ' i ^ 2 := pow_le_pow_left₀ hν.le this 2
    nlinarith [sq_nonneg (c i)]

/-! ### Perturbation estimates -/

lemma cs_bound {X Y : ℂ → ℝ} (hX : MemLp X 2 (volume.restrict (ball (0 : ℂ) 1))) (hY : MemLp Y 2 (volume.restrict (ball (0 : ℂ) 1))) {bx bY : ℝ}
    (hbx0 : 0 ≤ bx) (hbY0 : 0 ≤ bY)
    (hbx : ∫ x in ball (0 : ℂ) 1, X x ^ 2 ≤ bx ^ 2) (hbY : ∫ x in ball (0 : ℂ) 1, Y x ^ 2 ≤ bY ^ 2) :
    |∫ x in ball (0 : ℂ) 1, X x * Y x| ≤ bx * bY := by
  refine (abs_integral_mul_le_sqrt hX hY).trans (mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) hbx0)
  · rw [show bx = √(bx ^ 2) by rw [Real.sqrt_sq hbx0]]; exact Real.sqrt_le_sqrt hbx
  · rw [show bY = √(bY ^ 2) by rw [Real.sqrt_sq hbY0]]; exact Real.sqrt_le_sqrt hbY

/-- `L²` bound for weighted Green potentials. -/
lemma integral_sq_weight_greenPotD_le {b : ℂ → ℝ} {B : ℝ} (hb : Measurable b)
    (hB : ∀ η ∈ ball (0 : ℂ) 1, |b η| ≤ B) {r : ℂ → ℝ} (hr : MemLp r 2 (volume.restrict (ball (0 : ℂ) 1)))
    (hrm : StronglyMeasurable r) :
    MemLp (fun x => b x * greenPotD r x) 2 (volume.restrict (ball (0 : ℂ) 1)) ∧
    ∫ x in ball (0 : ℂ) 1, (b x * greenPotD r x) ^ 2 ≤
      (B * √(volume.real (ball (0 : ℂ) 1)) * √greenL2Const) ^ 2 *
        ∫ x in ball (0 : ℂ) 1, r x ^ 2 := by
  have hm := memLp_mul_weight hb hB (memLp_greenPotD hr hrm)
  refine ⟨hm, ?_⟩
  have hI : 0 ≤ ∫ x in ball (0 : ℂ) 1, r x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 (mem_ball_self one_pos))
  have hpt : ∀ x ∈ ball (0 : ℂ) 1, (b x * greenPotD r x) ^ 2 ≤
      B ^ 2 * (greenL2Const * ∫ x in ball (0 : ℂ) 1, r x ^ 2) := by
    intro x hx
    have h1 := abs_greenPotD_le hr (mem_ball_zero_iff.1 hx).le
    have hc0 : 0 ≤ greenL2Const := by
      unfold greenL2Const; exact setIntegral_nonneg measurableSet_ball fun y _ => by
        unfold gBound; positivity
    have h2 : (b x * greenPotD r x) ^ 2 = |b x| ^ 2 * |greenPotD r x| ^ 2 := by
      rw [mul_pow, sq_abs, sq_abs]
    rw [h2]
    refine mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hB x hx) 2) ?_ (by positivity)
      (by positivity)
    calc |greenPotD r x| ^ 2 ≤ (√greenL2Const * √(∫ x in ball (0 : ℂ) 1, r x ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = _ := by rw [mul_pow, Real.sq_sqrt hc0, Real.sq_sqrt hI]
  have hc0 : 0 ≤ greenL2Const := by
    unfold greenL2Const; exact setIntegral_nonneg measurableSet_ball fun y _ => by
      unfold gBound; positivity
  calc ∫ x in ball (0 : ℂ) 1, (b x * greenPotD r x) ^ 2
      ≤ ∫ x in ball (0 : ℂ) 1, B ^ 2 * (greenL2Const * ∫ x in ball (0 : ℂ) 1, r x ^ 2) :=
        setIntegral_mono_on hm.integrable_sq (integrableOn_const measure_ball_lt_top.ne)
          measurableSet_ball hpt
    _ = _ := by
        rw [setIntegral_const, smul_eq_mul, mul_pow, mul_pow, Real.sq_sqrt (by positivity),
          Real.sq_sqrt hc0]
        ring

lemma measurable_one_fun : Measurable (fun _ : ℂ => (1 : ℝ)) := measurable_const

/-- Perturbation of the Green form. -/
lemma formB_close {F F' q q' : ℂ → ℝ} (hF : MemLp F 2 (volume.restrict (ball (0 : ℂ) 1))) (hF' : MemLp F' 2 (volume.restrict (ball (0 : ℂ) 1)))
    (hq : MemLp q 2 (volume.restrict (ball (0 : ℂ) 1))) (hq' : MemLp q' 2 (volume.restrict (ball (0 : ℂ) 1))) (hFm : StronglyMeasurable F)
    (hqm : StronglyMeasurable q) {A0 Bq δ : ℝ} (hA0 : 0 ≤ A0) (hBq : 0 ≤ Bq) (hδ : 0 ≤ δ)
    (hFb : ∫ x in ball (0 : ℂ) 1, F' x ^ 2 ≤ A0 ^ 2) (hqb : ∫ x in ball (0 : ℂ) 1, q x ^ 2 ≤ Bq ^ 2)
    (hd : ∫ x in ball (0 : ℂ) 1, (q x - F x) ^ 2 ≤ δ ^ 2)
    (hd' : ∫ x in ball (0 : ℂ) 1, (q' x - F' x) ^ 2 ≤ δ ^ 2) :
    |formB q' q - formB F' F| ≤
      √(volume.real (ball (0 : ℂ) 1)) * √greenL2Const * (Bq + A0) * δ := by
  set κ := √(volume.real (ball (0 : ℂ) 1)) * √greenL2Const
  have hκ : 0 ≤ κ := by positivity
  have hone : ∀ η ∈ ball (0 : ℂ) 1, |(fun _ : ℂ => (1 : ℝ)) η| ≤ 1 := fun _ _ => by simp
  obtain ⟨hGq, hGqb⟩ := integral_sq_weight_greenPotD_le measurable_one_fun hone hq hqm
  obtain ⟨hGd, hGdb⟩ := integral_sq_weight_greenPotD_le (r := fun y => q y - F y)
    measurable_one_fun hone (hq.sub hF)
    (hqm.sub hFm)
  have hGq' : MemLp (greenPotD q) 2 (volume.restrict (ball (0 : ℂ) 1)) := memLp_greenPotD hq hqm
  have hGd' : MemLp (greenPotD (fun y => q y - F y)) 2 (volume.restrict (ball (0 : ℂ) 1)) := memLp_greenPotD (hq.sub hF) (hqm.sub hFm)
  have hGqb' : ∫ x in ball (0 : ℂ) 1, greenPotD q x ^ 2 ≤ κ ^ 2 * ∫ x in ball (0 : ℂ) 1, q x ^ 2 :=
    (Eq.le (by simp)).trans (hGqb.trans_eq (by simp only [κ]; ring))
  have hGdb' : ∫ x in ball (0 : ℂ) 1, greenPotD (fun y => q y - F y) x ^ 2 ≤
      κ ^ 2 * ∫ x in ball (0 : ℂ) 1, (q x - F x) ^ 2 :=
    (Eq.le (by simp)).trans (hGdb.trans_eq (by simp only [κ]; ring))
  have e : formB q' q - formB F' F =
      (∫ x in ball (0 : ℂ) 1, (q' x - F' x) * greenPotD q x) +
        ∫ x in ball (0 : ℂ) 1, F' x * greenPotD (fun y => q y - F y) x := by
    unfold formB
    rw [← integral_add (f := fun x => (q' x - F' x) * greenPotD q x)
        (g := fun x => F' x * greenPotD (fun y => q y - F y) x)
        ((hq'.sub hF').integrable_mul hGq') (hF'.integrable_mul hGd'),
      ← integral_sub (f := fun x => q' x * greenPotD q x) (g := fun x => F' x * greenPotD F x)
        (hq'.integrable_mul hGq') (hF'.integrable_mul (memLp_greenPotD hF hFm))]
    refine setIntegral_congr_fun measurableSet_ball fun x hx => ?_
    rw [greenPotD_sub hq hF (mem_ball_zero_iff.1 hx).le]; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have b1 := cs_bound (hq'.sub hF') hGq' hδ (mul_nonneg hκ hBq) hd' (by
    refine hGqb'.trans ?_
    rw [mul_pow κ]
    exact mul_le_mul_of_nonneg_left hqb (sq_nonneg _))
  have b2 := cs_bound hF' hGd' hA0 (mul_nonneg hκ hδ) hFb (by
    refine hGdb'.trans ?_
    rw [mul_pow κ]
    exact mul_le_mul_of_nonneg_left hd (sq_nonneg _))
  calc _ ≤ δ * (κ * Bq) + A0 * (κ * δ) := add_le_add b1 b2
    _ = κ * (Bq + A0) * δ := by ring

/-- Perturbation of the weighted mass of Green potentials. -/
lemma mass_close {b : ℂ → ℝ} {B : ℝ} (hb : Measurable b) (hB : ∀ η ∈ ball (0 : ℂ) 1, |b η| ≤ B)
    {F F' q q' : ℂ → ℝ} (hF : MemLp F 2 (volume.restrict (ball (0 : ℂ) 1))) (hF' : MemLp F' 2 (volume.restrict (ball (0 : ℂ) 1)))
    (hq : MemLp q 2 (volume.restrict (ball (0 : ℂ) 1))) (hq' : MemLp q' 2 (volume.restrict (ball (0 : ℂ) 1))) (hFm : StronglyMeasurable F)
    (hF'm : StronglyMeasurable F') (hqm : StronglyMeasurable q) (hq'm : StronglyMeasurable q')
    {A0 Bq δ : ℝ} (hA0 : 0 ≤ A0) (hBq : 0 ≤ Bq) (hδ : 0 ≤ δ)
    (hFb : ∫ x in ball (0 : ℂ) 1, F x ^ 2 ≤ A0 ^ 2) (hqb : ∫ x in ball (0 : ℂ) 1, q' x ^ 2 ≤ Bq ^ 2)
    (hd : ∫ x in ball (0 : ℂ) 1, (q x - F x) ^ 2 ≤ δ ^ 2)
    (hd' : ∫ x in ball (0 : ℂ) 1, (q' x - F' x) ^ 2 ≤ δ ^ 2) :
    |(∫ x in ball (0 : ℂ) 1, (b x * greenPotD q x) * (b x * greenPotD q' x)) -
      ∫ x in ball (0 : ℂ) 1, (b x * greenPotD F x) * (b x * greenPotD F' x)| ≤
      (B * √(volume.real (ball (0 : ℂ) 1)) * √greenL2Const) ^ 2 * (Bq + A0) * δ := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 (mem_ball_self one_pos))
  set κ := B * √(volume.real (ball (0 : ℂ) 1)) * √greenL2Const
  have hκ : 0 ≤ κ := by positivity
  obtain ⟨h1, h1b⟩ := integral_sq_weight_greenPotD_le (r := fun y => q y - F y) hb hB (hq.sub hF) (hqm.sub hFm)
  obtain ⟨h2, h2b⟩ := integral_sq_weight_greenPotD_le hb hB hq' hq'm
  obtain ⟨h3, h3b⟩ := integral_sq_weight_greenPotD_le hb hB hF hFm
  obtain ⟨h4, h4b⟩ := integral_sq_weight_greenPotD_le (r := fun y => q' y - F' y) hb hB (hq'.sub hF') (hq'm.sub hF'm)
  obtain ⟨h5, -⟩ := integral_sq_weight_greenPotD_le hb hB hq hqm
  obtain ⟨h6, -⟩ := integral_sq_weight_greenPotD_le hb hB hF' hF'm
  have e : (∫ x in ball (0 : ℂ) 1, (b x * greenPotD q x) * (b x * greenPotD q' x)) -
      ∫ x in ball (0 : ℂ) 1, (b x * greenPotD F x) * (b x * greenPotD F' x) =
      (∫ x in ball (0 : ℂ) 1, (b x * greenPotD (fun y => q y - F y) x) *
        (b x * greenPotD q' x)) +
      ∫ x in ball (0 : ℂ) 1, (b x * greenPotD F x) * (b x * greenPotD (fun y => q' y - F' y) x) := by
    rw [← integral_add (f := fun x => (b x * greenPotD (fun y => q y - F y) x) *
          (b x * greenPotD q' x))
        (g := fun x => (b x * greenPotD F x) * (b x * greenPotD (fun y => q' y - F' y) x))
        (h1.integrable_mul h2) (h3.integrable_mul h4),
      ← integral_sub (f := fun x => (b x * greenPotD q x) * (b x * greenPotD q' x))
        (g := fun x => (b x * greenPotD F x) * (b x * greenPotD F' x))
        (h5.integrable_mul h2) (h3.integrable_mul h6)]
    refine setIntegral_congr_fun measurableSet_ball fun x hx => ?_
    rw [greenPotD_sub hq hF (mem_ball_zero_iff.1 hx).le,
      greenPotD_sub hq' hF' (mem_ball_zero_iff.1 hx).le]; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have b1 := cs_bound h1 h2 (mul_nonneg hκ hδ) (mul_nonneg hκ hBq)
    (by rw [mul_pow]; exact h1b.trans (mul_le_mul_of_nonneg_left hd (sq_nonneg _)))
    (by rw [mul_pow]; exact h2b.trans (mul_le_mul_of_nonneg_left hqb (sq_nonneg _)))
  have b2 := cs_bound h3 h4 (mul_nonneg hκ hA0) (mul_nonneg hκ hδ)
    (by rw [mul_pow]; exact h3b.trans (mul_le_mul_of_nonneg_left hFb (sq_nonneg _)))
    (by rw [mul_pow]; exact h4b.trans (mul_le_mul_of_nonneg_left hd' (sq_nonneg _)))
  calc _ ≤ κ * δ * (κ * Bq) + κ * A0 * (κ * δ) := add_le_add b1 b2
    _ = κ ^ 2 * (Bq + A0) * δ := by ring

/-- `L²` bound for an approximant. -/
lemma integral_sq_le_of_close {q F : ℂ → ℝ} (hq : MemLp q 2 (volume.restrict (ball (0 : ℂ) 1))) (hF : MemLp F 2 (volume.restrict (ball (0 : ℂ) 1))) {A0 δ : ℝ}
    (hFb : ∫ x in ball (0 : ℂ) 1, F x ^ 2 ≤ A0 ^ 2) (hδ1 : δ ≤ 1) (hδ0 : 0 ≤ δ)
    (hd : ∫ x in ball (0 : ℂ) 1, (q x - F x) ^ 2 ≤ δ ^ 2) :
    ∫ x in ball (0 : ℂ) 1, q x ^ 2 ≤ √(2 * A0 ^ 2 + 2) ^ 2 := by
  rw [Real.sq_sqrt (by positivity)]
  have hδ2 : δ ^ 2 ≤ 1 := by nlinarith
  have i1 := hF.integrable_sq
  have i2 := (hq.sub hF).integrable_sq
  calc ∫ x in ball (0 : ℂ) 1, q x ^ 2
      ≤ ∫ x in ball (0 : ℂ) 1, (2 * F x ^ 2 + 2 * (q x - F x) ^ 2) := by
        refine integral_mono hq.integrable_sq ((i1.const_mul 2).add (i2.const_mul 2)) fun x => ?_
        nlinarith [sq_nonneg (q x - 2 * F x)]
    _ = 2 * (∫ x in ball (0 : ℂ) 1, F x ^ 2) + 2 * ∫ x in ball (0 : ℂ) 1, (q x - F x) ^ 2 := by
        rw [integral_add (f := fun x => 2 * F x ^ 2) (g := fun x => 2 * (q x - F x) ^ 2)
          (i1.const_mul 2) (i2.const_mul 2), integral_const_mul, integral_const_mul]
    _ ≤ 2 * A0 ^ 2 + 2 := by linarith

/-- The constant in the Gram estimates for Green potentials of approximants. -/
def gramConst (A : ℝ) : ℝ :=
  √(volume.real (ball (0 : ℂ) 1)) * √greenL2Const * (√(2 * A ^ 2 + 2) + A) +
    (A * √(volume.real (ball (0 : ℂ) 1)) * √greenL2Const) ^ 2 * (√(2 * A ^ 2 + 2) + A)

lemma eigen_formB (hw : WeightOK a A) {m : ℕ} {e : ℕ → Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1))} {μ : ℕ → ℝ}
    (horth : ∀ i < m, ∀ l < m, ⟪e i, e l⟫_ℝ = if i = l then 1 else 0)
    (heig : ∀ i < m, greenOp hw.meas hw.bound (e i) = μ i • e i ∧ 0 < μ i)
    {i l : ℕ} (hi : i < m) (hl : l < m) :
    formB (fun x => a x * e l x) (fun x => a x * e i x) = (if i = l then μ i else 0) ∧
    ∫ x in ball (0 : ℂ) 1, (a x * greenPotD (fun y => a y * e i y) x) *
      (a x * greenPotD (fun y => a y * e l y) x) = if i = l then μ i ^ 2 else 0 := by
  constructor
  · have h := inner_greenOp hw.meas hw.bound (e i) (e l)
    rw [(heig i hi).1, real_inner_smul_left, horth i hi l hl] at h
    rw [formB, ← h]
    split_ifs <;> simp
  · have h := inner_Lp_eq (greenOp hw.meas hw.bound (e i)) (greenOp hw.meas hw.bound (e l))
    have h2 : ∫ x, (greenOp hw.meas hw.bound (e i)) x * (greenOp hw.meas hw.bound (e l)) x ∂(volume.restrict (ball (0 : ℂ) 1)) =
        ∫ x in ball (0 : ℂ) 1, (a x * greenPotD (fun y => a y * e i y) x) *
          (a x * greenPotD (fun y => a y * e l y) x) := by
      refine integral_congr_ae ?_
      filter_upwards [greenOp_apply hw.meas hw.bound (e i), greenOp_apply hw.meas hw.bound (e l)]
        with x h1 h2
      rw [h1, h2]; rfl
    rw [← h2, ← h, (heig i hi).1, (heig l hl).1, real_inner_smul_left, real_inner_smul_right,
      horth i hi l hl]
    split_ifs with h
    · subst h; ring
    · simp

lemma integral_sq_eig_le (hw : WeightOK a A) {e : Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1))} (he : ⟪e, e⟫_ℝ = 1) :
    ∫ x in ball (0 : ℂ) 1, (a x * e x) ^ 2 ≤ A ^ 2 := by
  have h := integral_sq_mul_weight_le hw.bound (Lp.memLp e)
  rw [← norm_Lp_sq_eq, ← real_inner_self_eq_norm_sq, he, mul_one] at h
  exact h

/-- Gram estimates for the Green potentials of approximants of `a eᵢ`. -/
lemma w_gram_close (hw : WeightOK a A) {m : ℕ} {e : ℕ → Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1))} {μ : ℕ → ℝ}
    (horth : ∀ i < m, ∀ l < m, ⟪e i, e l⟫_ℝ = if i = l then 1 else 0)
    (heig : ∀ i < m, greenOp hw.meas hw.bound (e i) = μ i • e i ∧ 0 < μ i)
    {i l : ℕ} (hi : i < m) (hl : l < m) {qi ql : ℂ → ℝ}
    (hqi : qi ∈ testFunctions (ball (0 : ℂ) 1)) (hql : ql ∈ testFunctions (ball (0 : ℂ) 1))
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hdi : ∫ x in ball (0 : ℂ) 1, (qi x - a x * e i x) ^ 2 ≤ δ ^ 2)
    (hdl : ∫ x in ball (0 : ℂ) 1, (ql x - a x * e l x) ^ 2 ≤ δ ^ 2) :
    |(∫ x in ball (0 : ℂ) 1, gradInner (fderiv ℝ (greenPot qi) x) (fderiv ℝ (greenPot ql) x)) -
        if i = l then μ i else 0| ≤ gramConst A * δ ∧
    |(∫ x in ball (0 : ℂ) 1, a x ^ 2 * greenPot qi x * greenPot ql x) -
        if i = l then μ i ^ 2 else 0| ≤ gramConst A * δ := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hw.bound 0 (mem_ball_self one_pos))
  obtain ⟨T1, T2⟩ := eigen_formB hw horth heig hi hl
  have hFi : MemLp (fun x => a x * e i x) 2 (volume.restrict (ball (0 : ℂ) 1)) := memLp_mul_weight hw.meas hw.bound (Lp.memLp _)
  have hFl : MemLp (fun x => a x * e l x) 2 (volume.restrict (ball (0 : ℂ) 1)) := memLp_mul_weight hw.meas hw.bound (Lp.memLp _)
  have hFim : StronglyMeasurable (fun x => a x * e i x) :=
    hw.meas.stronglyMeasurable.mul (Lp.stronglyMeasurable _)
  have hFlm : StronglyMeasurable (fun x => a x * e l x) :=
    hw.meas.stronglyMeasurable.mul (Lp.stronglyMeasurable _)
  have hFib := integral_sq_eig_le hw (e := e i) (by rw [horth i hi i hi, if_pos rfl])
  have hFlb := integral_sq_eig_le hw (e := e l) (by rw [horth l hl l hl, if_pos rfl])
  have hqiL := test_memLp hqi
  have hqlL := test_memLp hql
  have hqib := integral_sq_le_of_close hqiL hFi hFib hδ1 hδ0 hdi
  have hqlb := integral_sq_le_of_close hqlL hFl hFlb hδ1 hδ0 hdl
  have hB := formB_close hFi hFl hqiL hqlL hFim hqi.1.continuous.stronglyMeasurable hA0
    (Real.sqrt_nonneg _) hδ0 hFlb hqib hdi hdl
  have hM := mass_close hw.meas hw.bound hFi hFl hqiL hqlL hFim hFlm
    hqi.1.continuous.stronglyMeasurable hql.1.continuous.stronglyMeasurable hA0
    (Real.sqrt_nonneg _) hδ0 hFib hqlb hdi hdl
  obtain ⟨hni, -, hgi⟩ := greenPot_test hqi
  obtain ⟨hnl, hLl, hgl⟩ := greenPot_test hql
  have E1 : ∫ x in ball (0 : ℂ) 1, gradInner (fderiv ℝ (greenPot qi) x)
      (fderiv ℝ (greenPot ql) x) = formB ql qi := by
    rw [hni.green_first hnl, formB, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_ball fun x hx => ?_
    rw [hLl x hx, hgi]; ring
  have M1 : ∫ x in ball (0 : ℂ) 1, a x ^ 2 * greenPot qi x * greenPot ql x =
      ∫ x in ball (0 : ℂ) 1, (a x * greenPotD qi x) * (a x * greenPotD ql x) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hgi, hgl]; ring
  have hκ : 0 ≤ √(volume.real (ball (0 : ℂ) 1)) * √greenL2Const * (√(2 * A ^ 2 + 2) + A) :=
    by positivity
  have hκ' : 0 ≤ (A * √(volume.real (ball (0 : ℂ) 1)) * √greenL2Const) ^ 2 *
      (√(2 * A ^ 2 + 2) + A) := by positivity
  constructor
  · rw [E1, ← T1]
    refine hB.trans ?_
    unfold gramConst
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hκ') hδ0
  · rw [M1, ← T2]
    refine hM.trans ?_
    unfold gramConst
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hκ) hδ0

/-- **Approximation step**: test functions whose Gram matrices are close to `diag(μᵢ)` and
`diag(μᵢ²)`. -/
theorem exists_test_gram (hw : WeightOK a A) {m : ℕ} {e : ℕ → Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1))} {μ : ℕ → ℝ}
    (horth : ∀ i < m, ∀ l < m, ⟪e i, e l⟫_ℝ = if i = l then 1 else 0)
    (heig : ∀ i < m, greenOp hw.meas hw.bound (e i) = μ i • e i ∧ 0 < μ i)
    {j : ℕ} (hjm : j ≤ m) {η : ℝ} (hη : 0 < η) :
    ∃ ψ : Fin j → ℂ → ℝ, (∀ i, ψ i ∈ testFunctions (ball (0 : ℂ) 1)) ∧
      (∀ i l, |gramE ψ i l - if i = l then μ i else 0| ≤ η) ∧
      (∀ i l, |gramM a ψ i l - if i = l then μ i ^ 2 else 0| ≤ η) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hw.bound 0 (mem_ball_self one_pos))
  have hC0 : 0 ≤ gramConst A := by unfold gramConst; positivity
  set δ := min 1 (η / (2 * (gramConst A + 1))) with hδdef
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hCδ : gramConst A * δ ≤ η / 2 := by
    have h1 : δ ≤ η / (2 * (gramConst A + 1)) := min_le_right _ _
    calc gramConst A * δ ≤ gramConst A * (η / (2 * (gramConst A + 1))) :=
          mul_le_mul_of_nonneg_left h1 hC0
      _ ≤ η / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have happrox : ∀ i : Fin j, ∃ q ∈ testFunctions (ball (0 : ℂ) 1),
      ∫ x in ball (0 : ℂ) 1, (q x - a x * e i x) ^ 2 ≤ δ ^ 2 := by
    intro i
    obtain ⟨q, hq, hqd⟩ := exists_test_approx
      (memLp_mul_weight hw.meas hw.bound (Lp.memLp (e i))) (pow_pos hδ0 2)
    refine ⟨q, hq, le_of_eq_of_le ?_ hqd⟩
    congr 1; funext x; ring
  choose q hq hqd using happrox
  choose R hR1 hRs using fun i => greenPot_test_smooth (hq i)
  have hrho : ∀ z ∈ ball (0 : ℂ) 1, |(fun η => a η ^ 2) z| ≤ A ^ 2 := fun z hz => by
    simp only [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hw.bound z hz) 2
  choose K hK0 hK using fun i l => cut_gram_close (greenPot_test (hq i)).1
    (greenPot_test (hq l)).1 hw.smooth.continuousOn hrho
  set Kt := ∑ i, ∑ l, K i l with hKt
  have hKle : ∀ i l, K i l ≤ Kt := fun i l =>
    (Finset.single_le_sum (fun l _ => hK0 i l) (Finset.mem_univ l)).trans
      (Finset.single_le_sum (f := fun i => ∑ l, K i l)
        (fun i _ => Finset.sum_nonneg fun l _ => hK0 i l) (Finset.mem_univ i))
  have hKt0 : 0 ≤ Kt := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun l _ => hK0 i l
  set t := min (1 / 2) (η / (2 * (Kt + 1))) with htdef
  have ht0 : 0 < t := lt_min (by norm_num) (by positivity)
  have ht2 : t ≤ 1 / 2 := min_le_left _ _
  have hKtη : ∀ i l, K i l * t ≤ η / 2 := by
    intro i l
    have h1 : t ≤ η / (2 * (Kt + 1)) := min_le_right _ _
    calc K i l * t ≤ Kt * (η / (2 * (Kt + 1))) :=
          mul_le_mul (hKle i l) h1 ht0.le hKt0
      _ ≤ η / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have hif : ∀ i l : Fin j, ∀ x y : ℝ,
      (if (i : ℕ) = l then x else y) = if i = l then x else y := by
    intro i l x y; simp only [Fin.val_inj]
  refine ⟨fun i x => cutB t x * greenPot (q i) x,
    fun i => cutB_mul_smooth_test (hR1 i) (hRs i) ht0, ?_, ?_⟩
  · intro i l
    obtain ⟨h1, -⟩ := hK i l t ht0 ht2
    obtain ⟨h2, -⟩ := w_gram_close hw horth heig (i.2.trans_le hjm) (l.2.trans_le hjm)
      (hq i) (hq l) hδ0.le hδ1 (hqd i) (hqd l)
    rw [hif] at h2
    unfold gramE
    calc _ ≤ _ := abs_sub_le _ _ _
      _ ≤ η / 2 + η / 2 := add_le_add (h1.trans (hKtη i l)) (h2.trans hCδ)
      _ = η := by ring
  · intro i l
    obtain ⟨-, h1⟩ := hK i l t ht0 ht2
    obtain ⟨-, h2⟩ := w_gram_close hw horth heig (i.2.trans_le hjm) (l.2.trans_le hjm)
      (hq i) (hq l) hδ0.le hδ1 (hqd i) (hqd l)
    rw [hif] at h2
    unfold gramM
    calc _ ≤ _ := abs_sub_le _ _ _
      _ ≤ η / 2 + η / 2 := add_le_add (h1.trans (hKtη i l)) (h2.trans hCδ)
      _ = η := by ring

/-- **Upper bound** for the weighted min–max values. -/
theorem minmax_upper (hw : WeightOK a A) {m : ℕ} {e : ℕ → Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1))} {μ : ℕ → ℝ}
    (horth : ∀ i < m, ∀ l < m, ⟪e i, e l⟫_ℝ = if i = l then 1 else 0)
    (heig : ∀ i < m, greenOp hw.meas hw.bound (e i) = μ i • e i ∧ 0 < μ i)
    (hmax : ∀ i < m, ∀ x, (∀ l < i, ⟪e l, x⟫_ℝ = 0) →
      ⟪greenOp hw.meas hw.bound x, x⟫_ℝ ≤ μ i * ‖x‖ ^ 2)
    {j : ℕ} (hj1 : 1 ≤ j) (hjm : j ≤ m) :
    minmax (testFunctions (ball 0 1)) (wRayleigh (fun η => a η ^ 2)) j ≤
      ENNReal.ofReal (1 / μ (j - 1)) := by
  classical
  set ν := μ (j - 1)
  have hν : 0 < ν := (heig (j - 1) (by omega)).2
  -- the eigenvalues are decreasing
  have hμν : ∀ i : Fin j, ν ≤ μ i := by
    intro i
    have hi : (i : ℕ) < m := by omega
    have h := hmax i hi (e (j - 1)) fun l hl => by
      rw [horth l (by omega) (j - 1) (by omega)]
      simp only [ite_eq_right_iff, one_ne_zero, imp_false]
      omega
    rw [(heig (j - 1) (by omega)).1, real_inner_smul_left, real_inner_self_eq_norm_sq] at h
    have hn : ‖e (j - 1)‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, horth _ (by omega) _ (by omega)]; simp
    rw [hn] at h; simpa using h
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ) < ε := hε
  set η := min (ν ^ 2 / (2 * (j + 1))) (ε * ν ^ 2 / ((j + 1) * (1 + 1 / ν + ε)))
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hη1 : η * j ≤ ν ^ 2 / 2 := by
    have : η ≤ ν ^ 2 / (2 * (j + 1)) := min_le_left _ _
    calc η * j ≤ ν ^ 2 / (2 * (j + 1)) * j := by gcongr
      _ ≤ ν ^ 2 / 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg ν]
  have hη2 : η * j * (1 + 1 / ν + ε) ≤ ε * ν ^ 2 := by
    have : η ≤ ε * ν ^ 2 / ((j + 1) * (1 + 1 / ν + ε)) := min_le_right _ _
    have hpos : 0 < (1 + 1 / ν + (ε : ℝ)) := by positivity
    calc η * j * (1 + 1 / ν + ε) ≤ ε * ν ^ 2 / ((j + 1) * (1 + 1 / ν + ε)) * j *
          (1 + 1 / ν + ε) := by gcongr
      _ = ε * ν ^ 2 * (j / (j + 1)) := by field_simp
      _ ≤ ε * ν ^ 2 := by
        refine mul_le_of_le_one_right (by positivity) ?_
        rw [div_le_one (by positivity)]; linarith
  obtain ⟨ψ, hψ, hE, hM⟩ := exists_test_gram hw horth heig hjm hη
  have hquad := fun c => quad_bound (fun i : Fin j => μ i) hν hμν hη.le (gramE ψ) (gramM a ψ)
    hE hM c
  -- the span of the `ψᵢ`
  set V := Submodule.span ℝ (Set.range ψ)
  have hfun : ∀ c : Fin j → ℝ, (∑ i, c i • ψ i) = fun y => ∑ i, c i * ψ i y := by
    intro c; funext y; simp [Finset.sum_apply]
  have hsumtest : ∀ c : Fin j → ℝ, (fun y => ∑ i, c i * ψ i y) ∈ testFunctions (ball (0 : ℂ) 1) :=
    fun c => by
      rw [← hfun]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hψ i)
  have hmass_pos : ∀ c : Fin j → ℝ, c ≠ 0 →
      0 < ∫ x in ball (0 : ℂ) 1, (a x ^ 2 * (∑ i, c i * ψ i x)) * (∑ i, c i * ψ i x) := by
    intro c hc
    obtain ⟨-, h2, h3⟩ := hquad c
    rw [mass_sum hw hψ]
    have hS : 0 < ∑ i, c i ^ 2 := by
      obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
        by_contra h; push_neg at h; exact hc (funext h)
      exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun i => c i ^ 2)
        (fun i _ => sq_nonneg (c i)) (Finset.mem_univ i))
    have := mul_le_mul_of_nonneg_right hη1 hS.le
    have hν2 : 0 < ν ^ 2 * ∑ i, c i ^ 2 := by positivity
    nlinarith
  have hli : LinearIndependent ℝ ψ := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra h
    push_neg at h
    obtain ⟨i, hi⟩ := h
    have hc0 : c ≠ 0 := fun h0 => hi (by rw [h0]; rfl)
    have := hmass_pos c hc0
    rw [hfun] at hc
    have hz : ∀ x, ∑ i, c i * ψ i x = 0 := fun x => congrFun hc x
    simp [hz] at this
  have hVle : V ≤ testFunctions (ball 0 1) := by
    rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hψ i
  have hVdim : Module.finrank ℝ V = j := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  calc minmax (testFunctions (ball 0 1)) (wRayleigh (fun η => a η ^ 2)) j
      ≤ ⨆ (u : ℂ → ℝ) (_ : u ∈ V) (_ : u ≠ 0), wRayleigh (fun η => a η ^ 2) u := by
        unfold minmax
        exact iInf_le_of_le V (iInf_le_of_le hVle (iInf_le_of_le hVdim le_rfl))
    _ ≤ ENNReal.ofReal (1 / ν) + ε := by
        refine iSup_le fun u => iSup_le fun hu => iSup_le fun hu0 => ?_
        obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hu
        have hc0 : c ≠ 0 := by rintro rfl; apply hu0; simp
        rw [hfun] at hu0 ⊢
        obtain ⟨h1, h2, h3⟩ := hquad c
        have hMpos := hmass_pos c hc0
        unfold wRayleigh
        rw [dirichletEnergy_test (hsumtest c), massW_test hw (hsumtest c),
          ← ENNReal.ofReal_div_of_pos hMpos, energy_sum hψ, ← ENNReal.ofReal_coe_nnreal,
          ← ENNReal.ofReal_add (by positivity) hε'.le]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ hMpos, mass_sum hw hψ]
        rw [mass_sum hw hψ] at hMpos
        set X := ∑ i, c i ^ 2 * μ i ^ 2
        set S := ∑ i, c i ^ 2
        set QE := ∑ i, ∑ l, c i * c l * gramE ψ i l
        set QM := ∑ i, ∑ l, c i * c l * gramM a ψ i l
        have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
        -- `QE ≤ X/ν + ηjS ≤ (1/ν + ε)(X - ηjS) ≤ (1/ν + ε) QM`
        have k1 : η * j * S * (1 + 1 / ν + ε) ≤ ε * X := by
          calc η * j * S * (1 + 1 / ν + ε) = (η * j * (1 + 1 / ν + ε)) * S := by ring
            _ ≤ ε * ν ^ 2 * S := mul_le_mul_of_nonneg_right hη2 hS0
            _ ≤ ε * X := by
                rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h3 hε'.le
        have k2 : X / ν + η * j * S ≤ (1 / ν + ε) * (X - η * j * S) := by
          have : X / ν = 1 / ν * X := by ring
          nlinarith
        have k3 : (1 / ν + ε) * (X - η * j * S) ≤ (1 / ν + ε) * QM :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        linarith

end

section

/-! ## Compactness of the weighted Green operator -/

open MeasureTheory Set Real Metric Filter Topology
open scoped ComplexConjugate InnerProductSpace

variable {a : ℂ → ℝ} {A : ℝ}

lemma greenPotD_diff_le {h : ℂ → ℝ} (hh : MemLp h 2 (volume.restrict (ball (0 : ℂ) 1))) {w w₀ : ℂ} (hw : ‖w‖ ≤ 1)
    (hw₀ : ‖w₀‖ ≤ 1) :
    |greenPotD h w - greenPotD h w₀| ≤
      √(∫ η in ball (0 : ℂ) 1, (diskGreen w η - diskGreen w₀ η) ^ 2) *
        √(∫ η in ball (0 : ℂ) 1, h η ^ 2) := by
  have e : greenPotD h w - greenPotD h w₀ =
      ∫ η in ball (0 : ℂ) 1, (diskGreen w η - diskGreen w₀ η) * h η := by
    unfold greenPotD
    rw [← integral_sub (integrable_diskGreen_mul hh hw) (integrable_diskGreen_mul hh hw₀)]
    congr 1; funext η; ring
  rw [e]
  exact abs_integral_mul_le_sqrt ((memLp_diskGreen hw).sub (memLp_diskGreen hw₀)) hh

/-- Uniform equicontinuity of Green potentials of bounded subsets of `L²(𝔻)`. -/
lemma greenPotD_equicont {w₀ : ℂ} (hw₀ : ‖w₀‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) {B : ℝ} (hB : 0 ≤ B) :
    ∃ δ > 0, ∀ w : ℂ, ‖w‖ ≤ 1 → ‖w - w₀‖ < δ → ∀ h : ℂ → ℝ, MemLp h 2 (volume.restrict (ball (0 : ℂ) 1)) →
      ∫ η in ball (0 : ℂ) 1, h η ^ 2 ≤ B ^ 2 → |greenPotD h w - greenPotD h w₀| < ε := by
  set ε' := (ε / (B + 1)) ^ 2
  obtain ⟨δ, hδ, hδε⟩ := diskGreen_L2_continuous hw₀ (show 0 < ε' by positivity)
  refine ⟨δ, hδ, fun w hw hww₀ h hh hhB => ?_⟩
  refine (greenPotD_diff_le hh hw hw₀).trans_lt ?_
  have h1 : √(∫ η in ball (0 : ℂ) 1, (diskGreen w η - diskGreen w₀ η) ^ 2) ≤ ε / (B + 1) := by
    rw [show ε / (B + 1) = √ε' by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (hδε w hw hww₀)
  have h2 : √(∫ η in ball (0 : ℂ) 1, h η ^ 2) ≤ B := by
    rw [show B = √(B ^ 2) by rw [Real.sqrt_sq hB]]; exact Real.sqrt_le_sqrt hhB
  calc _ ≤ ε / (B + 1) * B := mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith

open Classical in
/-- Extension by zero of a function on the closed disk. -/
def extDisk (φ : closedBall (0 : ℂ) 1 → ℝ) (z : ℂ) : ℝ :=
  if hz : z ∈ closedBall (0 : ℂ) 1 then φ ⟨z, hz⟩ else 0

lemma extDisk_continuousOn (φ : BoundedContinuousFunction (closedBall (0 : ℂ) 1) ℝ) :
    ContinuousOn (extDisk φ) (closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : (closedBall (0 : ℂ) 1).domRestrict (extDisk φ) = φ := by
    funext x
    change extDisk φ x = φ x
    simp [extDisk, x.2]
  rw [this]; exact φ.continuous

lemma abs_extDisk_le (φ : BoundedContinuousFunction (closedBall (0 : ℂ) 1) ℝ) (z : ℂ) :
    |extDisk φ z| ≤ ‖φ‖ := by
  unfold extDisk
  split_ifs with hz
  · simpa using φ.norm_coe_le_norm ⟨z, hz⟩
  · simp

lemma memLp_weight_extDisk (ha : Measurable a) (hA : ∀ η ∈ ball (0 : ℂ) 1, |a η| ≤ A)
    (φ : BoundedContinuousFunction (closedBall (0 : ℂ) 1) ℝ) :
    MemLp (fun z => a z * extDisk φ z) 2 (volume.restrict (ball (0 : ℂ) 1)) := by
  haveI : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) 1)) := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  refine MemLp.of_bound (ha.aestronglyMeasurable.mul (((extDisk_continuousOn φ).mono
    ball_subset_closedBall).aestronglyMeasurable measurableSet_ball)) (A * ‖φ‖) ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hA z hz) (abs_extDisk_le φ z) (abs_nonneg _)
    ((abs_nonneg _).trans (hA z hz))

/-- The multiplication map `φ ↦ a · φ` from `C(𝔻̄)` to `L²(𝔻)`. -/
def weightMapLin (ha : Measurable a) (hA : ∀ η ∈ ball (0 : ℂ) 1, |a η| ≤ A) :
    BoundedContinuousFunction (closedBall (0 : ℂ) 1) ℝ →ₗ[ℝ] Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1)) where
  toFun φ := (memLp_weight_extDisk ha hA φ).toLp _
  map_add' φ ψ := by
    rw [← MemLp.toLp_add]
    congr 1; funext z; simp only [Pi.add_apply, extDisk]; split_ifs <;> simp [mul_add]
  map_smul' c φ := by
    rw [← MemLp.toLp_const_smul]
    congr 1; funext z; simp only [Pi.smul_apply, extDisk, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp; ring

lemma weightMapLin_bound (ha : Measurable a) (hA : ∀ η ∈ ball (0 : ℂ) 1, |a η| ≤ A)
    (φ : BoundedContinuousFunction (closedBall (0 : ℂ) 1) ℝ) :
    ‖weightMapLin ha hA φ‖ ≤ ((measureUnivNNReal (volume.restrict (ball (0 : ℂ) 1)) : ℝ) ^ (2 : ENNReal).toReal⁻¹ * A) * ‖φ‖ := by
  haveI : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) 1)) := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 (mem_ball_self one_pos))
  rw [mul_assoc]
  refine Lp.norm_le_of_ae_bound (by positivity) ?_
  filter_upwards [(memLp_weight_extDisk ha hA φ).coeFn_toLp,
    ae_restrict_mem measurableSet_ball] with z hz hzb
  change ‖((memLp_weight_extDisk ha hA φ).toLp _ : ℂ → ℝ) z‖ ≤ _
  rw [hz, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hA z hzb) (abs_extDisk_le φ z) (abs_nonneg _) hA0

/-- **Compactness of the weighted Green operator.** -/
theorem greenOp_isCompactOperator (ha : Measurable a) (hA : ∀ η ∈ ball (0 : ℂ) 1, |a η| ≤ A) :
    IsCompactOperator (greenOp ha hA) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 (mem_ball_self one_pos))
  set h : Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1)) → ℂ → ℝ := fun f η => a η * f η
  have hh : ∀ f : Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1)), MemLp (h f) 2 (volume.restrict (ball (0 : ℂ) 1)) := fun f => memLp_mul_weight ha hA (Lp.memLp f)
  have hhB : ∀ f : Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1)), ‖f‖ ≤ 1 → ∫ η in ball (0 : ℂ) 1, h f η ^ 2 ≤ A ^ 2 := by
    intro f hf
    refine (integral_sq_mul_weight_le hA (Lp.memLp f)).trans ?_
    rw [← norm_Lp_sq_eq]
    have : ‖f‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg f]
    nlinarith [sq_nonneg A]
  -- the Green potentials as continuous functions on the closed disk
  have hcont : ∀ f : Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1)),
      Continuous fun x : closedBall (0 : ℂ) 1 => greenPotD (h f) x := by
    intro f
    rw [Metric.continuous_iff]
    intro x₀ ε hε
    obtain ⟨δ, hδ, H⟩ := greenPotD_equicont (mem_closedBall_zero_iff.1 x₀.2) hε
      (Real.sqrt_nonneg (∫ η in ball (0 : ℂ) 1, h f η ^ 2))
    refine ⟨δ, hδ, fun x hx => ?_⟩
    rw [Real.dist_eq]
    have hx' : ‖(x : ℂ) - (x₀ : ℂ)‖ < δ := by
      simpa only [Subtype.dist_eq, dist_eq_norm] using hx
    exact H x (mem_closedBall_zero_iff.1 x.2) hx' (h f) (hh f)
      (Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)).ge
  set P : Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1)) → BoundedContinuousFunction (closedBall (0 : ℂ) 1) ℝ := fun f =>
    BoundedContinuousFunction.mkOfCompact ⟨_, hcont f⟩
  have hP : ∀ f x, P f x = greenPotD (h f) x := fun _ _ => rfl
  set S := P '' closedBall (0 : Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1))) 1
  have hS : IsCompact (closure S) := by
    refine BoundedContinuousFunction.arzela_ascoli (closedBall 0 (√greenL2Const * A))
      (isCompact_closedBall _ _) S ?_ ?_
    · rintro _ x ⟨f, hf, rfl⟩
      rw [mem_closedBall_zero_iff, hP, Real.norm_eq_abs]
      refine (abs_greenPotD_le (hh f) (mem_closedBall_zero_iff.1 x.2)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      rw [show A = √(A ^ 2) by rw [Real.sqrt_sq hA0]]
      exact Real.sqrt_le_sqrt (hhB f (mem_closedBall_zero_iff.1 hf))
    · intro x₀
      rw [Metric.equicontinuousAt_iff]
      intro ε hε
      obtain ⟨δ, hδ, H⟩ := greenPotD_equicont (mem_closedBall_zero_iff.1 x₀.2) hε hA0
      refine ⟨δ, hδ, fun x hx i => ?_⟩
      obtain ⟨_, ⟨f, hf, rfl⟩⟩ := i
      rw [Real.dist_eq, abs_sub_comm]
      have hx' : ‖(x : ℂ) - (x₀ : ℂ)‖ < δ := by
        simpa only [Subtype.dist_eq, dist_eq_norm] using hx
      exact H x (mem_closedBall_zero_iff.1 x.2) hx' (h f) (hh f)
        (hhB f (mem_closedBall_zero_iff.1 hf))
  set Q := weightMapLin ha hA
  have hQc : Continuous Q := by
    dsimp [Q]
    refine Continuous.congr
      ((weightMapLin ha hA).mkContinuous _ (weightMapLin_bound ha hA)).continuous ?_
    intro x
    rfl
  have hTQP : ∀ f, greenOp ha hA f = Q (P f) := by
    intro f
    refine Lp.ext ?_
    filter_upwards [greenOp_apply ha hA f, (memLp_weight_extDisk ha hA (P f)).coeFn_toLp,
      ae_restrict_mem measurableSet_ball] with z h1 h2 h3
    change _ = ((memLp_weight_extDisk ha hA (P f)).toLp _ : ℂ → ℝ) z
    rw [h1, h2]
    simp [greenOpFun, extDisk, ball_subset_closedBall h3, hP, h]
  rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
  refine ⟨closedBall 0 1, closedBall_mem_nhds 0 one_pos, Q '' closure S, hS.image hQc, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  exact ⟨P f, subset_closure ⟨f, hf, rfl⟩, (hTQP f).symm⟩

end

section

/-! ## Weak Dirichlet eigenfunctions on conformal disks -/

open MeasureTheory Set Real Metric Filter Topology
open scoped ComplexConjugate InnerProductSpace

variable {a : ℂ → ℝ} {A : ℝ}

/-- Green potentials of eigenvectors are weak solutions on the disk. -/
theorem eigvec_diskWeak (hw : WeightOK a A) {f : Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1))} {μ k : ℝ}
    (hT : greenOp hw.meas hw.bound f = μ • f) (hμk : μ * k ^ 2 = 1) :
    DiskWeak (fun η => a η ^ 2) k (greenPotD (fun η => a η * f η)) := by
  intro W w hWo hWsub hws hw0
  have hn : DiskNice w := ⟨W, hWo, hWsub, hws.of_le (by norm_cast), hw0⟩
  set af := fun η => a η * f η
  have haf : MemLp af 2 (volume.restrict (ball (0 : ℂ) 1)) := memLp_mul_weight hw.meas hw.bound (Lp.memLp f)
  have hafm : StronglyMeasurable af := hw.meas.stronglyMeasurable.mul (Lp.stronglyMeasurable f)
  have hu := memLp_greenPotD haf hafm
  have hL2 := memLp_of_continuousOn_closedBall hn.laplacian_continuousOn
  have hw2 := memLp_of_continuousOn_closedBall hn.continuousOn
  have i1 : Integrable (fun z => greenPotD af z * Laplacian.laplacian w z) (volume.restrict (ball (0 : ℂ) 1)) :=
    hu.integrable_mul hL2
  -- `a · G(a f) = T f = μ f` a.e.
  have hTf : ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)), a z * greenPotD af z = μ * f z := by
    filter_upwards [greenOp_apply hw.meas hw.bound f, Lp.coeFn_smul μ f] with z h1 h2
    rw [← hT] at h2
    have : greenOpFun a f z = (μ • ⇑f) z := h1.symm.trans h2
    simpa [greenOpFun] using this
  have i2 : Integrable (fun z => af z * w z) (volume.restrict (ball (0 : ℂ) 1)) := haf.integrable_mul hw2
  have e2 : ∫ z in ball (0 : ℂ) 1, greenPotD af z * (k ^ 2 * a z ^ 2 * w z) =
      ∫ z in ball (0 : ℂ) 1, af z * w z := by
    refine integral_congr_ae ?_
    filter_upwards [hTf] with z hz
    have : greenPotD af z * (k ^ 2 * a z ^ 2 * w z) = k ^ 2 * (a z * greenPotD af z) * a z * w z :=
      by ring
    rw [this, hz]
    simp only [af]
    linear_combination (a z * f z * w z) * hμk
  have i3 : Integrable (fun z => greenPotD af z * (k ^ 2 * a z ^ 2 * w z)) (volume.restrict (ball (0 : ℂ) 1)) :=
    i2.congr (by
      filter_upwards [hTf] with z hz
      have : greenPotD af z * (k ^ 2 * a z ^ 2 * w z) =
          k ^ 2 * (a z * greenPotD af z) * a z * w z := by ring
      rw [this, hz]
      simp only [af]
      linear_combination -(a z * f z * w z) * hμk)
  have e : (fun z => greenPotD af z * (Laplacian.laplacian w z + k ^ 2 * a z ^ 2 * w z)) =
      fun z => greenPotD af z * Laplacian.laplacian w z +
        greenPotD af z * (k ^ 2 * a z ^ 2 * w z) := by
    funext z; ring
  show ∫ z in ball (0 : ℂ) 1, greenPotD af z * (Laplacian.laplacian w z + k ^ 2 * a z ^ 2 * w z)
    = 0
  rw [e, integral_add i1 i3, e2, integral_greenPotD_laplacian haf hafm hn]
  ring

variable {R0 : ℝ} {G : ℂ → ℂ}

/-- Transport of weak solutions from the disk to `G(𝔻)`. -/
theorem diskWeak_to_weak (hR0 : 1 < R0) (hG : DifferentiableOn ℂ G (ball 0 R0))
    (hinj : InjOn G (ball 0 R0)) {k : ℝ} {v : ℂ → ℝ} (hv : DiskWeak (confWeight G) k v)
    {g : ℂ → ℂ} (hgG : ∀ z ∈ ball (0 : ℂ) R0, g (G z) = z) :
    WeakDirichletHelmholtz G 1 k (fun z => v (g z)) := by
  intro W' w hW'o hW'sub hws hw0
  have hD1 : ball (0 : ℂ) 1 ⊆ ball 0 R0 := ball_subset_ball hR0.le
  have hcl1 : closedBall (0 : ℂ) 1 ⊆ ball 0 R0 := closedBall_subset_ball hR0
  rw [integral_image_holomorphic isOpen_ball (hG.mono hD1) (hinj.mono hD1)]
  set O := ball (0 : ℂ) R0 ∩ G ⁻¹' W'
  have hOo : IsOpen O := hG.continuousOn.isOpen_inter_preimage isOpen_ball hW'o
  have hDO : closedBall (0 : ℂ) 1 ⊆ O := fun η hη =>
    ⟨hcl1 hη, hW'sub (mem_image_of_mem G hη)⟩
  have hGs : ContDiffOn ℝ (⊤ : ℕ∞) G (ball 0 R0) :=
    (hG.contDiffOn isOpen_ball).restrict_scalars ℝ
  have hwG : ContDiffOn ℝ (⊤ : ℕ∞) (w ∘ G) O :=
    hws.comp (hGs.mono inter_subset_left) fun η hη => hη.2
  have h := hv O (w ∘ G) hOo hDO hwG fun η hη => hw0 (G η)
    (mem_image_of_mem G hη)
  rw [← h]
  refine setIntegral_congr_fun measurableSet_ball fun η hη => ?_
  have hηO : η ∈ O := hDO (ball_subset_closedBall hη)
  have hC2 : ContDiffAt ℝ 2 w (G η) :=
    (hws.contDiffAt (hW'o.mem_nhds hηO.2)).of_le (by norm_cast)
  rw [laplacian_comp_holomorphic isOpen_ball (hD1 hη) hG hC2]
  simp only [Function.comp_apply, hgG η (hD1 hη), confWeight]
  ring

lemma greenOp_eig_ae (hw : WeightOK a A) {f : Lp ℝ 2 (volume.restrict (ball (0 : ℂ) 1))} {μ : ℝ}
    (hT : greenOp hw.meas hw.bound f = μ • f) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)), a z * greenPotD (fun η => a η * f η) z = μ * f z := by
  filter_upwards [greenOp_apply hw.meas hw.bound f, Lp.coeFn_smul μ f] with z h1 h2
  rw [← hT] at h2
  have : greenOpFun a f z = (μ • ⇑f) z := h1.symm.trans h2
  simpa [greenOpFun] using this

/-- Null sets of `G(𝔻)` pull back to null sets of `𝔻`. -/
lemma ae_pullback {g : ℂ → ℂ} (hΩ : IsOpen (G '' ball 0 1))
    (hgd : DifferentiableOn ℂ g (G '' ball 0 1)) (hgG : ∀ z ∈ ball (0 : ℂ) 1, g (G z) = z)
    {F : ℂ → ℝ} (hF : F =ᵐ[volume.restrict (G '' ball 0 1)] 0) :
    ∀ᵐ η ∂(volume.restrict (ball (0 : ℂ) 1)), F (G η) = 0 := by
  have h1 := (ae_restrict_iff' hΩ.measurableSet).1 hF
  rw [ae_iff] at h1
  set N := {z | ¬(z ∈ G '' ball 0 1 → F z = (0 : ℂ → ℝ) z)}
  have hNs : N ⊆ G '' ball 0 1 := fun z hz => by
    by_contra hc; exact hz fun h => absurd h hc
  have hgN : volume (g '' N) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      ((hgd.mono hNs).restrictScalars ℝ) h1
  refine (ae_restrict_iff' measurableSet_ball).2 ?_
  rw [ae_iff]
  refine measure_mono_null ?_ hgN
  intro η hη
  simp only [mem_setOf_eq, Classical.not_imp] at hη
  obtain ⟨hηb, hne⟩ := hη
  refine ⟨G η, ?_, hgG η hηb⟩
  simp only [N, mem_setOf_eq, Classical.not_imp, Pi.zero_apply]
  exact ⟨mem_image_of_mem G hηb, hne⟩

/-- **Weak Dirichlet eigenfunctions on conformal disks.** -/
theorem conformal_weak_eigenfunctions (hR0 : 1 < R0) (hG : DifferentiableOn ℂ G (ball 0 R0))
    (hinj : InjOn G (ball 0 R0)) {k : ℝ} (hk : 0 < k) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, 1 ≤ j ∧ dirichletEigenvalue (G '' ball 0 1) j = ENNReal.ofReal (k ^ 2)) :
    ∃ u : Fin J.card → ℂ → ℝ, (∀ i, MemLp (u i) 2 (volume.restrict (G '' ball 0 1))) ∧
      (∀ i, WeakDirichletHelmholtz G 1 k (u i)) ∧
      ∀ c : Fin J.card → ℝ,
        (fun z => ∑ i, c i * u i z) =ᵐ[volume.restrict (G '' ball 0 1)] 0 → c = 0 := by
  classical
  have hD1 : ball (0 : ℂ) 1 ⊆ ball 0 R0 := ball_subset_ball hR0.le
  have hcl1 : closedBall (0 : ℂ) 1 ⊆ ball 0 R0 := closedBall_subset_ball hR0
  set a : ℂ → ℝ := fun η => ‖deriv G η‖ with ha
  have hne : ∀ η ∈ ball (0 : ℂ) R0, deriv G η ≠ 0 := fun η hη =>
    deriv_ne_zero_of_injOn isOpen_ball hG hinj hη
  have hG'd : DifferentiableOn ℂ (deriv G) (ball 0 R0) := hG.deriv isOpen_ball
  obtain ⟨A, hA⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (hG'd.continuousOn.mono hcl1)
  have hw : WeightOK a A :=
    ⟨(measurable_deriv G).norm, fun η hη => by simpa [a] using hA η (ball_subset_closedBall hη),
      fun η hη => norm_pos_iff.2 (hne η (hD1 hη)),
      ((contDiff_norm_sq ℝ).comp_contDiffOn
        ((hG'd.contDiffOn isOpen_ball (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).restrict_scalars ℝ)).mono
        hD1⟩
  obtain ⟨m, e, μ, -, horth, heig, hmax, hstop⟩ :=
    exists_eigen_family (greenOp_isCompactOperator hw.meas hw.bound)
      (greenOp_symm hw.meas hw.bound) (J.sup id)
  -- the eigenvalues
  have key : ∀ j ∈ J, j ≤ m ∧ μ (j - 1) * k ^ 2 = 1 := by
    intro j hj
    obtain ⟨hj1, hlam⟩ := hJ j hj
    have hjn : j ≤ J.sup id := Finset.le_sup (f := id) hj
    have hle1 := minmax_weighted_le hR0 hG hinj j
    have hle2 := dirichletEigenvalue_le_weighted hR0 hG hinj j
    rw [hlam] at hle1 hle2
    have hfin : minmax (testFunctions (ball 0 1)) (wRayleigh (fun η => a η ^ 2)) j < ⊤ :=
      lt_of_le_of_lt hle1 ENNReal.ofReal_lt_top
    obtain ⟨hjm, hlow⟩ := minmax_lower hw (fun i hi => (heig i hi).2) hmax hstop hj1 hjn hfin
    have hup := minmax_upper hw horth heig hmax hj1 hjm
    have hμ := (heig (j - 1) (by omega)).2
    have h1 : ENNReal.ofReal (1 / μ (j - 1)) = ENNReal.ofReal (k ^ 2) :=
      le_antisymm (hlow.trans hle1) (hle2.trans hup)
    rw [ENNReal.ofReal_eq_ofReal_iff (by positivity) (sq_nonneg k)] at h1
    refine ⟨hjm, ?_⟩
    rw [← h1]; field_simp
  -- indices
  set φ := J.orderEmbOfFin rfl
  set idx : Fin J.card → ℕ := fun i => φ i - 1
  have hφJ : ∀ i, φ i ∈ J := fun i => Finset.orderEmbOfFin_mem J rfl i
  have hidx : ∀ i, idx i < m ∧ μ (idx i) * k ^ 2 = 1 := fun i => by
    have h := key (φ i) (hφJ i)
    have h1 := (hJ (φ i) (hφJ i)).1
    exact ⟨by simp only [idx]; omega, h.2⟩
  have hidx_inj : ∀ i i', idx i = idx i' → i = i' := fun i i' h => by
    have h1 := (hJ (φ i) (hφJ i)).1
    have h2 := (hJ (φ i') (hφJ i')).1
    simp only [idx] at h
    exact φ.injective (by omega)
  obtain ⟨g, hΩ, hgd, hgmaps, hgG, hGg⟩ := conf_setup hR0 hG hinj
  set ũ : ℕ → ℂ → ℝ := fun l => greenPotD (fun η => a η * e l η)
  have hafm : ∀ l, StronglyMeasurable (fun η => a η * e l η) := fun l =>
    hw.meas.stronglyMeasurable.mul (Lp.stronglyMeasurable (e l))
  have haf : ∀ l, MemLp (fun η => a η * e l η) 2 (volume.restrict (ball (0 : ℂ) 1)) := fun l =>
    memLp_mul_weight hw.meas hw.bound (Lp.memLp (e l))
  refine ⟨fun i z => ũ (idx i) (g z), fun i => ?_, fun i => ?_, fun c hc => ?_⟩
  · -- square integrability
    have hfin : IsFiniteMeasure (volume.restrict (G '' ball 0 1)) := by
      refine isFiniteMeasure_restrict.2 (ne_top_of_le_ne_top ?_ (measure_mono (image_mono
        (ball_subset_closedBall (x := (0 : ℂ)) (ε := 1)))))
      exact ((isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn
        (hG.continuousOn.mono hcl1)).measure_lt_top.ne
    refine MemLp.of_bound ((stronglyMeasurable_greenPotD (hafm (idx i))).aestronglyMeasurable
      |>.comp_aemeasurable (hgd.continuousOn.aemeasurable hΩ.measurableSet))
      (√greenL2Const * √(∫ η in ball (0 : ℂ) 1, (a η * e (idx i) η) ^ 2)) ?_
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with z hz
    rw [Real.norm_eq_abs]
    exact abs_greenPotD_le (haf (idx i)) (mem_ball_zero_iff.1 (hgmaps hz)).le
  · -- weak equation
    exact diskWeak_to_weak hR0 hG hinj
      (eigvec_diskWeak hw (heig (idx i) (hidx i).1).1 (hidx i).2) hgG
  · -- linear independence
    have h1 := ae_pullback hΩ hgd (fun z hz => hgG z (hD1 hz)) hc
    have hsum0 : ∀ᵐ η ∂(volume.restrict (ball (0 : ℂ) 1)), ∑ i, c i * e (idx i) η = 0 := by
      have hall : ∀ᵐ η ∂(volume.restrict (ball (0 : ℂ) 1)), ∀ i, a η * ũ (idx i) η = μ (idx i) * e (idx i) η :=
        ae_all_iff.2 fun i => greenOp_eig_ae hw (heig (idx i) (hidx i).1).1
      filter_upwards [h1, hall, ae_restrict_mem measurableSet_ball] with η hη hall hηb
      simp only [hgG η (hD1 hηb)] at hη
      have e1 : a η * ∑ i, c i * ũ (idx i) η = 0 := by rw [hη, mul_zero]
      rw [Finset.mul_sum] at e1
      have e2 : ∑ i, a η * (c i * ũ (idx i) η) = ∑ i, c i * e (idx i) η * (1 / k ^ 2) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have h := hall i
        have hμi : μ (idx i) = 1 / k ^ 2 := by
          field_simp; linarith [(hidx i).2]
        rw [mul_left_comm, h, hμi]; ring
      rw [e2, ← Finset.sum_mul] at e1
      have hk2 : (1 / k ^ 2 : ℝ) ≠ 0 := by positivity
      exact (mul_eq_zero.1 e1).resolve_right hk2
    funext i'
    have hint : ∀ i ∈ (Finset.univ : Finset (Fin J.card)),
        Integrable (fun x => e (idx i') x * (c i * e (idx i) x)) (volume.restrict (ball (0 : ℂ) 1)) := fun i _ =>
      (Lp.memLp (e (idx i'))).integrable_mul ((Lp.memLp (e (idx i))).const_mul (c i))
    have hcalc : c i' = ∑ i, c i * ⟪e (idx i'), e (idx i)⟫_ℝ := by
      have : ∀ i, c i * ⟪e (idx i'), e (idx i)⟫_ℝ = if i' = i then c i else 0 := fun i => by
        rw [horth _ (hidx i').1 _ (hidx i).1]
        by_cases h : i' = i
        · simp [h]
        · have : idx i' ≠ idx i := fun h' => h (hidx_inj _ _ h')
          simp [h, this]
      simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [hcalc]
    simp_rw [inner_Lp_eq]
    simp only [Pi.zero_apply]
    have e3 : ∑ i, c i * ∫ x, e (idx i') x * e (idx i) x ∂(volume.restrict (ball (0 : ℂ) 1)) =
        ∫ x, e (idx i') x * ∑ i, c i * e (idx i) x ∂(volume.restrict (ball (0 : ℂ) 1)) := by
      simp_rw [Finset.mul_sum]
      rw [integral_finset_sum _ hint]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_const_mul]; congr 1; funext x; ring
    rw [e3]
    have : (fun x => e (idx i') x * ∑ i, c i * e (idx i) x) =ᵐ[(volume.restrict (ball (0 : ℂ) 1))] 0 := by
      filter_upwards [hsum0] with x hx; simp [hx]
    rw [integral_congr_ae this]; simp

end

section

/-! ## Solutions with vanishing Cauchy data -/

open MeasureTheory Set Real Metric Filter Topology

lemma laplacian_ofReal_comp {φ : ℂ → ℝ} {z : ℂ} (h : ContDiffAt ℝ 2 φ z) :
    Laplacian.laplacian (fun x => (φ x : ℂ)) z = (Laplacian.laplacian φ z : ℂ) := by
  have := h.laplacian_CLM_comp_left (l := Complex.ofRealCLM)
  simpa [Function.comp_def] using this

/-- The rescaled map `η ↦ F(rη)` on a disk slightly larger than `𝔻`. -/
lemma exists_scaled_map {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) {r : ℝ} (hr : 0 < r)
    (hDU : closedBall (0 : ℂ) r ⊆ U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U) :
    ∃ R0 > 1, ball (0 : ℂ) (r * R0) ⊆ U ∧
      DifferentiableOn ℂ (fun η => F (r * η)) (ball 0 R0) ∧
      InjOn (fun η => F (r * η)) (ball 0 R0) ∧
      (fun η => F (r * η)) '' ball 0 1 = F '' ball 0 r ∧
      (fun η => F (r * η)) '' closedBall 0 1 = F '' closedBall 0 r ∧
      (fun η => F (r * η)) '' sphere 0 1 = F '' sphere 0 r := by
  obtain ⟨R0, hR0, hsub⟩ := exists_scaled_ball_subset hU hr hDU
  have himg : ∀ A : Set ℂ, (fun η => F (r * η)) '' A =
      F '' ((fun η : ℂ => (r : ℂ) * η) '' A) := fun A => (image_image F _ A).symm
  have hmaps : MapsTo (fun η : ℂ => (r : ℂ) * η) (ball 0 R0) U := by
    intro η hη
    apply hsub
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_lt_mul_of_pos_left (mem_ball_zero_iff.1 hη) hr
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  refine ⟨R0, hR0, hsub, hF.comp ((differentiable_id.const_mul (r : ℂ)).differentiableOn) hmaps,
    fun a ha b hb hab => mul_left_cancel₀ hr0 (hinj (hmaps ha) (hmaps hb) hab), ?_, ?_, ?_⟩
  · rw [himg, image_mul_ofReal_ball hr]
  · rw [himg, image_mul_ofReal_closedBall hr]
  · rw [himg, image_mul_ofReal_sphere hr]

/-- **Green's identity for vanishing Cauchy data** on `Ω = F(r𝔻)`. -/
theorem integral_helmholtz_zero_cauchy (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) {rs : ℝ}
    (hrs : 0 < rs) (hDU : closedBall (0 : ℂ) rs ⊆ U) (hF : DifferentiableOn ℂ F U)
    (hinj : InjOn F U) {k : ℝ} {V : Set ℂ} {ψ : ℂ → ℝ} (hV : IsOpen V)
    (hVsub : F '' closedBall 0 rs ⊆ V) (hψ1 : ContDiffOn ℝ 1 ψ V)
    (hψ2 : ContDiffOn ℝ 2 ψ (F '' ball 0 rs))
    (hψH : ∀ z ∈ F '' ball 0 rs, Laplacian.laplacian ψ z + k ^ 2 * ψ z = 0)
    (hd : ∀ z ∈ F '' sphere 0 rs, ψ z = 0 ∧ fderiv ℝ ψ z = 0)
    {W' : Set ℂ} {w : ℂ → ℝ} (hW'o : IsOpen W') (hW'sub : F '' closedBall 0 rs ⊆ W')
    (hw : ContDiffOn ℝ 2 w W') :
    ∫ z in F '' ball 0 rs, ψ z * (Laplacian.laplacian w z + k ^ 2 * w z) = 0 := by
  obtain ⟨R0, hR0, -, hG, hGinj, hball, hcl, hsph⟩ := exists_scaled_map hU hrs hDU hF hinj
  set G : ℂ → ℂ := fun η => F (rs * η)
  set B := ball (0 : ℂ) R0
  have hBo : IsOpen B := isOpen_ball
  have hBc : IsPreconnected B := (convex_ball _ _).isPreconnected
  have hD1 : ball (0 : ℂ) 1 ⊆ B := ball_subset_ball hR0.le
  have hcl1 : closedBall (0 : ℂ) 1 ⊆ B := closedBall_subset_ball hR0
  have hGs : ContDiffOn ℝ 2 G B := (hG.contDiffOn hBo).restrict_scalars ℝ
  have hΩ : IsOpen (F '' ball 0 rs) := by
    rw [← hball]; exact isOpen_image_of_injOn hBo hBc hG hGinj hD1 isOpen_ball
  set O := B ∩ G ⁻¹' (V ∩ W')
  have hOo : IsOpen O := hG.continuousOn.isOpen_inter_preimage hBo (hV.inter hW'o)
  have hGcl : ∀ η ∈ closedBall (0 : ℂ) 1, G η ∈ F '' closedBall 0 rs := fun η hη => by
    rw [← hcl]; exact ⟨η, hη, rfl⟩
  have hDO : closedBall (0 : ℂ) 1 ⊆ O := fun η hη =>
    ⟨hcl1 hη, hVsub (hGcl η hη), hW'sub (hGcl η hη)⟩
  have hGball : ∀ η ∈ ball (0 : ℂ) 1, G η ∈ F '' ball 0 rs := fun η hη => by
    rw [← hball]; exact ⟨η, hη, rfl⟩
  have hΨ1 : ContDiffOn ℝ 1 (ψ ∘ G) O :=
    hψ1.comp ((hGs.of_le (by norm_num)).mono inter_subset_left) fun η hη => hη.2.1
  have hΨ2 : ContDiffOn ℝ 2 (ψ ∘ G) (ball 0 1) := hψ2.comp (hGs.mono hD1) hGball
  have hWd : ContDiffOn ℝ 2 (w ∘ G) O := hw.comp (hGs.mono inter_subset_left) fun η hη => hη.2.2
  have hlapΨ : ∀ η ∈ ball (0 : ℂ) 1, Laplacian.laplacian (ψ ∘ G) η =
      -(k ^ 2 * ‖deriv G η‖ ^ 2 * ψ (G η)) := by
    intro η hη
    rw [laplacian_comp_holomorphic hBo (hD1 hη) hG
      (hψ2.contDiffAt (hΩ.mem_nhds (hGball η hη)))]
    have := hψH _ (hGball η hη)
    linear_combination ‖deriv G η‖ ^ 2 * this
  obtain ⟨AΨ, hAΨ0, hAΨ⟩ := exists_bound_closedBall (hΨ1.continuousOn.mono hDO)
  have hG'c : ContinuousOn (deriv G) (closedBall 0 1) :=
    (hG.deriv hBo).continuousOn.mono hcl1
  obtain ⟨M0, hM0⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hG'c
  have hΔb : ∀ η ∈ ball (0 : ℂ) 1, |Laplacian.laplacian (ψ ∘ G) η| ≤ k ^ 2 * M0 ^ 2 * AΨ := by
    intro η hη
    rw [hlapΨ η hη, abs_neg, abs_mul, abs_mul, abs_pow, abs_pow, abs_norm]
    have h1 : ‖deriv G η‖ ^ 2 ≤ M0 ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hM0 η (ball_subset_closedBall hη)) 2
    have h2 : |ψ (G η)| ≤ AΨ := hAΨ η (ball_subset_closedBall hη)
    rw [sq_abs]
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (sq_nonneg _)) h2 (abs_nonneg _)
      (by positivity)
  have h0 : ∀ η ∈ sphere (0 : ℂ) 1, (ψ ∘ G) η = 0 ∧ fderiv ℝ (ψ ∘ G) η = 0 := by
    intro η hη
    have hGs' : G η ∈ F '' sphere 0 rs := by rw [← hsph]; exact ⟨η, hη, rfl⟩
    obtain ⟨a, b⟩ := hd _ hGs'
    refine ⟨a, ?_⟩
    have hηB := hcl1 (sphere_subset_closedBall hη)
    have hψd : DifferentiableAt ℝ ψ (G η) :=
      (hψ1.contDiffAt (hV.mem_nhds (hDO (sphere_subset_closedBall hη)).2.1)).differentiableAt
        (by norm_num)
    have hGd : DifferentiableAt ℝ G η :=
      ((hG.differentiableAt (hBo.mem_nhds hηB)).restrictScalars ℝ)
    rw [fderiv_comp η hψd hGd, b, ContinuousLinearMap.zero_comp]
  have hgreen := integral_green_disk_zero hOo hDO hΨ1 hΨ2 hWd hΔb h0
  rw [← hball, integral_image_holomorphic isOpen_ball (hG.mono hD1) (hGinj.mono hD1), ← hgreen]
  refine setIntegral_congr_fun measurableSet_ball fun η hη => ?_
  have hGW : G η ∈ W' := (hDO (ball_subset_closedBall hη)).2.2
  rw [laplacian_comp_holomorphic hBo (hD1 hη) hG (hw.contDiffAt (hW'o.mem_nhds hGW)),
    hlapΨ η hη]
  simp only [Function.comp_apply]
  ring

/-- **Vanishing Cauchy data** (proof of `eq_zero_of_zero_cauchy_data`). -/
theorem eq_zero_of_zero_cauchy_data_proof (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hDU : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    {k : ℝ} (hk : 0 < k) {rs : ℝ} (hrs : rs ∈ Ioc (0 : ℝ) 1) {V : Set ℂ} (ψ : ℂ → ℝ)
    (hV : IsOpen V) (hVsub : F '' closedBall 0 rs ⊆ V) (hψ1 : ContDiffOn ℝ 1 ψ V)
    (hψ2 : ContDiffOn ℝ 2 ψ (F '' ball 0 rs))
    (hψH : ∀ z ∈ F '' ball 0 rs, Laplacian.laplacian ψ z + k ^ 2 * ψ z = 0)
    (hd : ∀ z ∈ F '' sphere 0 rs, ψ z = 0 ∧ fderiv ℝ ψ z = 0) :
    ∀ z ∈ F '' ball 0 rs, ψ z = 0 := by
  have hrs0 := hrs.1
  have hDU' : closedBall (0 : ℂ) rs ⊆ U := (closedBall_subset_closedBall hrs.2).trans hDU
  obtain ⟨R0, hR0, hsubU⟩ := exists_scaled_ball_subset hU hrs0 hDU'
  set r' := rs * (1 + R0) / 2
  have hr'1 : rs < r' := by simp only [r']; nlinarith
  have hr'2 : r' < rs * R0 := by simp only [r']; nlinarith
  have hr'0 : 0 < r' := hrs0.trans hr'1
  set Bb := ball (0 : ℂ) (rs * R0)
  have hBbo : IsOpen Bb := isOpen_ball
  have hBbc : IsPreconnected Bb := (convex_ball _ _).isPreconnected
  have hFB : DifferentiableOn ℂ F Bb := hF.mono hsubU
  have hinjB : InjOn F Bb := hinj.mono hsubU
  have hDU'' : closedBall (0 : ℂ) r' ⊆ U := (closedBall_subset_ball hr'2).trans hsubU
  set Ω := F '' ball 0 rs
  set Ω' := F '' ball 0 r'
  have hbB : ∀ {s : ℝ}, s ≤ rs * R0 → ball (0 : ℂ) s ⊆ Bb := fun h => ball_subset_ball h
  have hΩo : IsOpen Ω := isOpen_image_of_injOn hBbo hBbc hFB hinjB
    (hbB (by nlinarith)) isOpen_ball
  have hΩ'o : IsOpen Ω' := isOpen_image_of_injOn hBbo hBbc hFB hinjB
    (hbB hr'2.le) isOpen_ball
  have hΩΩ' : Ω ⊆ Ω' := image_mono (ball_subset_ball hr'1.le)
  -- the zero extension
  set ψt := Ω.indicator ψ
  have hKc : IsCompact (F '' closedBall 0 rs) :=
    (isCompact_closedBall _ _).image_of_continuousOn (hF.continuousOn.mono hDU')
  obtain ⟨A, hA⟩ := hKc.exists_bound_of_continuousOn (hψ1.continuousOn.mono hVsub)
  have hΩK : Ω ⊆ F '' closedBall 0 rs := image_mono ball_subset_closedBall
  have hψtm : AEStronglyMeasurable ψt volume :=
    (aestronglyMeasurable_indicator_iff hΩo.measurableSet).2
      ((hψ1.continuousOn.mono (hΩK.trans hVsub)).aestronglyMeasurable hΩo.measurableSet)
  have hK'c : IsCompact (F '' closedBall 0 r') :=
    (isCompact_closedBall _ _).image_of_continuousOn (hF.continuousOn.mono hDU'')
  haveI : IsFiniteMeasure (volume.restrict Ω') :=
    isFiniteMeasure_restrict.2 (ne_top_of_le_ne_top hK'c.measure_lt_top.ne
      (measure_mono (image_mono ball_subset_closedBall)))
  have hψtL : MemLp ψt 2 (volume.restrict Ω') := by
    refine MemLp.of_bound hψtm.restrict A (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ Ω
    · simp only [ψt, indicator_of_mem hz]; exact hA z (hΩK hz)
    · simp only [ψt, indicator_of_notMem hz, norm_zero]
      exact (norm_nonneg _).trans (hA _ (hΩK ⟨0, mem_ball_self hrs0, rfl⟩))
  have hweak : WeakDirichletHelmholtz F r' k ψt := by
    intro W w hWo hWsub hws hw0
    have e : ∫ z in Ω', ψt z * (Laplacian.laplacian w z + k ^ 2 * w z) =
        ∫ z in Ω, ψ z * (Laplacian.laplacian w z + k ^ 2 * w z) := by
      have : (fun z => ψt z * (Laplacian.laplacian w z + k ^ 2 * w z)) =
          Ω.indicator (fun z => ψ z * (Laplacian.laplacian w z + k ^ 2 * w z)) := by
        funext z
        by_cases hz : z ∈ Ω
        · simp [ψt, indicator_of_mem hz]
        · simp [ψt, indicator_of_notMem hz]
      rw [this, integral_indicator hΩo.measurableSet, Measure.restrict_restrict hΩo.measurableSet,
        inter_eq_left.2 hΩΩ']
    rw [e]
    exact integral_helmholtz_zero_cauchy F U hU hrs0 hDU' hF hinj hV hVsub hψ1 hψ2 hψH hd hWo
      ((image_mono (closedBall_subset_closedBall hr'1.le)).trans hWsub)
      (hws.of_le (by norm_cast))
  obtain ⟨V2, φ, -, -, -, hφ2, hφH, -, hφae⟩ :=
    weak_dirichlet_regularity_proof F U hU hr'0 hDU'' hF hinj ψt hψtL hweak
  -- the annulus
  set An := F '' (ball 0 r' \ closedBall 0 rs)
  have hAno : IsOpen An := isOpen_image_of_injOn hBbo hBbc hFB hinjB
    (diff_subset.trans (hbB hr'2.le)) (isOpen_ball.sdiff isClosed_closedBall)
  have hAnne : An.Nonempty := by
    refine ⟨F (((rs + r') / 2 : ℝ) : ℂ), _, ⟨?_, ?_⟩, rfl⟩
    · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith), not_le]
      linarith
  have hAnΩ' : An ⊆ Ω' := image_mono diff_subset
  have hAnΩ : ∀ z ∈ An, z ∉ Ω := by
    rintro _ ⟨a, ⟨ha1, ha2⟩, rfl⟩ ⟨b, hb, hab⟩
    have hbU : b ∈ U := hsubU (hbB (by nlinarith) hb)
    have haU : a ∈ U := hsubU (hbB hr'2.le ha1)
    rw [hinj hbU haU hab] at hb
    exact ha2 (ball_subset_closedBall hb)
  have hφc : ContinuousOn φ Ω' := hφ2.continuousOn
  have hφAn : ∀ z ∈ An, φ z = 0 := by
    have h1 : φ =ᵐ[volume.restrict An] fun _ => (0 : ℝ) := by
      have h2 := ae_restrict_of_ae_restrict_of_subset hAnΩ' hφae
      filter_upwards [h2, ae_restrict_mem hAno.measurableSet] with z hz hzA
      rw [← hz]; simp [ψt, indicator_of_notMem (hAnΩ z hzA)]
    exact fun z hz => Measure.eqOn_open_of_ae_eq h1 hAno (hφc.mono hAnΩ') continuousOn_const hz
  -- unique continuation
  have hHelm : IsHelmholtzOn k (fun z => (φ z : ℂ)) Ω' := by
    refine ⟨Complex.ofRealCLM.contDiff.comp_contDiffOn hφ2, fun z hz => ?_⟩
    rw [laplacian_ofReal_comp (hφ2.contDiffAt (hΩ'o.mem_nhds hz))]
    have h' : ((Laplacian.laplacian φ z + k ^ 2 * φ z : ℝ) : ℂ) = 0 := by
      rw [hφH z hz]; simp
    push_cast at h'
    exact h'
  have hΩ'c : IsPreconnected Ω' :=
    (convex_ball _ _).isPreconnected.image F (hF.continuousOn.mono
      (ball_subset_closedBall.trans hDU''))
  have hφ0 := helmholtz_eq_zero_of_isPreconnected hk.ne' hΩ'o hΩ'c hHelm hAno hAnne hAnΩ'
    (fun z hz => by simp [hφAn z hz])
  -- conclusion
  have hψae : ψ =ᵐ[volume.restrict Ω] fun _ => (0 : ℝ) := by
    have h2 := ae_restrict_of_ae_restrict_of_subset hΩΩ' hφae
    filter_upwards [h2, ae_restrict_mem hΩo.measurableSet] with z hz hzΩ
    have := hφ0 z (hΩΩ' hzΩ)
    simp only [Complex.ofReal_eq_zero] at this
    simp only [ψt, indicator_of_mem hzΩ] at hz
    rw [hz, this]
  exact fun z hz => Measure.eqOn_open_of_ae_eq hψae hΩo
    (hψ1.continuousOn.mono (hΩK.trans hVsub)) continuousOn_const hz

end

section

/-! ## Regular Dirichlet eigenfunctions (assembly) -/

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory Set Real Metric Complex Filter Topology

/-- **Weak eigenfunctions.** -/
theorem exists_weak_dirichlet_eigenfunctions (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hDU : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    {k : ℝ} (hk : 0 < k) {rs : ℝ} (hrs : rs ∈ Ioc (0 : ℝ) 1) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, 1 ≤ j ∧ dirichletEigenvalue (F '' ball 0 rs) j = ENNReal.ofReal (k ^ 2)) :
    ∃ u : Fin J.card → ℂ → ℝ, (∀ i, MemLp (u i) 2 (volume.restrict (F '' ball 0 rs))) ∧
      (∀ i, WeakDirichletHelmholtz F rs k (u i)) ∧
      ∀ c : Fin J.card → ℝ,
        (fun z => ∑ i, c i * u i z) =ᵐ[volume.restrict (F '' ball 0 rs)] 0 → c = 0 := by
  obtain ⟨R0, hR0, hsub⟩ := exists_scaled_ball_subset hU hrs.1
    ((closedBall_subset_closedBall hrs.2).trans hDU)
  set G : ℂ → ℂ := fun η => F (rs * η)
  have himg : ∀ A : Set ℂ, G '' A = F '' ((fun η : ℂ => (rs : ℂ) * η) '' A) := fun A =>
    (image_image F _ A).symm
  have hball : G '' ball 0 1 = F '' ball 0 rs := by rw [himg, image_mul_ofReal_ball hrs.1]
  have hcl : G '' closedBall 0 1 = F '' closedBall 0 rs := by
    rw [himg, image_mul_ofReal_closedBall hrs.1]
  have hsph : G '' sphere 0 1 = F '' sphere 0 rs := by
    rw [himg, image_mul_ofReal_sphere hrs.1]
  have hmaps : MapsTo (fun η : ℂ => (rs : ℂ) * η) (ball 0 R0) U := by
    intro η hη
    apply hsub
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrs.1]
    exact mul_lt_mul_of_pos_left (mem_ball_zero_iff.1 hη) hrs.1
  have hG : DifferentiableOn ℂ G (ball 0 R0) :=
    hF.comp ((differentiable_id.const_mul (rs : ℂ)).differentiableOn) hmaps
  have hr0 : (rs : ℂ) ≠ 0 := by exact_mod_cast hrs.1.ne'
  have hGinj : InjOn G (ball 0 R0) := fun a ha b hb hab =>
    mul_left_cancel₀ hr0 (hinj (hmaps ha) (hmaps hb) hab)
  obtain ⟨u, h1, h2, h3⟩ := conformal_weak_eigenfunctions hR0 hG hGinj hk J (by
    rw [hball]; exact hJ)
  refine ⟨u, fun i => by rw [← hball]; exact h1 i, fun i => ?_, fun c hc => h3 c (by
    rw [hball]; exact hc)⟩
  intro W w hWo hWsub hws hw0
  have := h2 i W w hWo (by rw [hcl]; exact hWsub) hws (by rw [hsph]; exact hw0)
  rwa [hball] at this

/-- **Regularity of weak Dirichlet solutions.** -/
theorem weak_dirichlet_regularity (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) {r : ℝ} (hr : 0 < r)
    (hDU : closedBall (0 : ℂ) r ⊆ U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    {k : ℝ} (u : ℂ → ℝ) (hu : MemLp u 2 (volume.restrict (F '' ball 0 r)))
    (hw : WeakDirichletHelmholtz F r k u) :
    ∃ (V : Set ℂ) (φ : ℂ → ℝ), IsOpen V ∧ F '' closedBall 0 r ⊆ V ∧ ContDiffOn ℝ 1 φ V ∧
      ContDiffOn ℝ 2 φ (F '' ball 0 r) ∧
      (∀ z ∈ F '' ball 0 r, Laplacian.laplacian φ z + k ^ 2 * φ z = 0) ∧
      (∀ z ∈ F '' sphere 0 r, φ z = 0) ∧ u =ᵐ[volume.restrict (F '' ball 0 r)] φ :=
  weak_dirichlet_regularity_proof F U hU hr hDU hF hinj u hu hw

/-- **Vanishing Cauchy data.** -/
theorem eq_zero_of_zero_cauchy_data (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hDU : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    {k : ℝ} (hk : 0 < k) {rs : ℝ} (hrs : rs ∈ Ioc (0 : ℝ) 1) {V : Set ℂ} (ψ : ℂ → ℝ)
    (hV : IsOpen V) (hVsub : F '' closedBall 0 rs ⊆ V) (hψ1 : ContDiffOn ℝ 1 ψ V)
    (hψ2 : ContDiffOn ℝ 2 ψ (F '' ball 0 rs))
    (hψH : ∀ z ∈ F '' ball 0 rs, Laplacian.laplacian ψ z + k ^ 2 * ψ z = 0)
    (hd : ∀ z ∈ F '' sphere 0 rs, ψ z = 0 ∧ fderiv ℝ ψ z = 0) :
    ∀ z ∈ F '' ball 0 rs, ψ z = 0 :=
  eq_zero_of_zero_cauchy_data_proof F U hU hDU hF hinj hk hrs ψ hV hVsub hψ1 hψ2 hψH hd

/-! ### Assembly -/

lemma laplacian_sum_mul {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → ℂ → ℝ) {z : ℂ}
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) z) :
    Laplacian.laplacian (fun x => ∑ i ∈ s, c i * f i x) z =
      ∑ i ∈ s, c i * Laplacian.laplacian (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  | insert a s ha ih =>
    have hfa : ContDiffAt ℝ 2 (f a) z := hf a (Finset.mem_insert_self a s)
    have hs : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) z := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have h1 : ContDiffAt ℝ 2 (fun x => c a * f a x) z := contDiffAt_const.mul hfa
    have h2 : ContDiffAt ℝ 2 (fun x => ∑ i ∈ s, c i * f i x) z :=
      ContDiffAt.sum fun i hi => contDiffAt_const.mul (hs i hi)
    have hsplit : (fun x => ∑ i ∈ insert a s, c i * f i x) =
        (fun x => c a * f a x) + (fun x => ∑ i ∈ s, c i * f i x) := by
      funext x; simp [Finset.sum_insert ha]
    rw [hsplit, h1.laplacian_add h2, Finset.sum_insert ha, ih hs]
    have : (fun x => c a * f a x) = c a • f a := by funext x; simp
    rw [this, InnerProductSpace.laplacian_smul _ hfa]
    simp

lemma exists_angle_of_mem_sphere {rs : ℝ} {w : ℂ} (hw : w ∈ sphere (0 : ℂ) rs) :
    ∃ θ ∈ Icc (0 : ℝ) (2 * π), w = rs * exp (θ * I) := by
  have hnorm : ‖w‖ = rs := by simpa using hw
  have hpolar : (rs : ℂ) * exp (arg w * I) = w := by
    rw [← hnorm]; exact Complex.norm_mul_exp_arg_mul_I w
  rcases le_or_gt 0 (arg w) with h | h
  · exact ⟨arg w, ⟨h, by linarith [Complex.arg_le_pi w, Real.pi_pos]⟩, hpolar.symm⟩
  · refine ⟨arg w + 2 * π, ⟨by linarith [Complex.neg_pi_lt_arg w], by linarith⟩, ?_⟩
    have : cexp (2 * ↑π * I) = 1 := Complex.exp_two_pi_mul_I
    calc w = (rs : ℂ) * exp (arg w * I) := hpolar.symm
      _ = _ := by push_cast; rw [add_mul, Complex.exp_add, this, mul_one]

lemma clm_eq_zero_of_apply_eq_zero {L : ℂ →L[ℝ] ℝ} {d : ℂ} (hd : d ≠ 0) (h1 : L d = 0)
    (h2 : L (-I * d) = 0) : L = 0 := by
  ext v
  set q := v / d
  have hv : v = q.re • d - q.im • (-I * d) := by
    have : v = q * d := by simp [q, div_mul_cancel₀ v hd]
    conv_lhs => rw [this, ← Complex.re_add_im q]
    simp only [Complex.real_smul]
    ring_nf
  rw [hv, map_sub, map_smul, map_smul, h1, h2]
  simp

/-- The tangential derivative of a function vanishing on `F(r𝕋)` vanishes. -/
lemma fderiv_dAng_eq_zero (F : ℂ → ℂ) {r θ : ℝ} {ψ : ℂ → ℝ}
    (hF : DifferentiableAt ℂ F (r * exp (θ * I)))
    (hψ : DifferentiableAt ℝ ψ (F (r * exp (θ * I))))
    (hzero : ∀ t : ℝ, ψ (F (r * exp (t * I))) = 0) :
    fderiv ℝ ψ (F (r * exp (θ * I))) (dAng F r θ) = 0 := by
  have hγ := hasDerivAt_angular (r := r) (θ := θ) hF
  have h := hψ.hasFDerivAt.comp_hasDerivAt θ hγ
  have h0 : HasDerivAt (fun t : ℝ => ψ (F (r * exp (t * I)))) 0 θ := by
    have : (fun t : ℝ => ψ (F (r * exp (t * I)))) = fun _ => 0 := funext hzero
    rw [this]; exact hasDerivAt_const θ 0
  have := h.unique h0
  simpa [dAng] using this

/-- **Regular Dirichlet eigenfunctions** (proof of `dirichlet_eigenfunctions_boundary`). -/
theorem dirichlet_eigenfunctions_boundary_proof (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hDU : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    {k : ℝ} (hk : 0 < k) {rs : ℝ} (hrs : rs ∈ Ioc (0 : ℝ) 1) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, 1 ≤ j ∧ dirichletEigenvalue (F '' ball 0 rs) j = ENNReal.ofReal (k ^ 2)) :
    ∃ (V : Set ℂ) (φ : Fin J.card → ℂ → ℂ), IsOpen V ∧ F '' sphere 0 rs ⊆ V ∧
      (∀ i, ContDiffOn ℝ 1 (φ i) V) ∧
      (∀ i, IsHelmholtzOn k (φ i) (F '' ball 0 rs)) ∧
      (∀ i, ∀ z ∈ F '' sphere 0 rs, φ i z = 0) ∧
      ∀ c : Fin J.card → ℂ, c ≠ 0 → ∃ θ ∈ Icc (0 : ℝ) (2 * π),
        fderiv ℝ (fun z => ∑ i, c i * φ i z) (F (rs * exp (θ * I))) (-I * dAng F rs θ) ≠ 0 := by
  obtain ⟨u, huL, huW, huind⟩ :=
    exists_weak_dirichlet_eigenfunctions F U hU hDU hF hinj hk hrs J hJ
  have hDU' : closedBall (0 : ℂ) rs ⊆ U := (closedBall_subset_closedBall hrs.2).trans hDU
  choose V φ hVo hVsub hφ1 hφ2 hφH hφ0 hφae using fun i =>
    weak_dirichlet_regularity F U hU hrs.1 hDU' hF hinj (u i) (huL i) (huW i)
  have hball1 : ball (0 : ℂ) 1 ⊆ U := ball_subset_closedBall.trans hDU
  have hΩ : IsOpen (F '' ball 0 rs) :=
    isOpen_image_of_injOn isOpen_ball (convex_ball _ _).isPreconnected
      (hF.mono hball1) (hinj.mono hball1) (ball_subset_ball hrs.2) isOpen_ball
  set V' := ⋂ i, V i with hV'
  have hV'o : IsOpen V' := isOpen_iInter_of_finite hVo
  have hV'sub : F '' closedBall 0 rs ⊆ V' := subset_iInter hVsub
  have hsph : F '' sphere 0 rs ⊆ F '' closedBall 0 rs := image_mono sphere_subset_closedBall
  have hφ1' : ∀ i, ContDiffOn ℝ 1 (φ i) V' := fun i => (hφ1 i).mono (iInter_subset _ i)
  refine ⟨V', fun i z => (φ i z : ℂ), hV'o, hsph.trans hV'sub,
    fun i => Complex.ofRealCLM.contDiff.comp_contDiffOn (hφ1' i), fun i => ?_,
    fun i z hz => by simp [hφ0 i z hz], ?_⟩
  · refine ⟨Complex.ofRealCLM.contDiff.comp_contDiffOn (hφ2 i), fun z hz => ?_⟩
    have hca : ContDiffAt ℝ 2 (φ i) z := (hφ2 i).contDiffAt (hΩ.mem_nhds hz)
    rw [laplacian_ofReal_comp hca]
    have h' : ((Laplacian.laplacian (φ i) z + k ^ 2 * φ i z : ℝ) : ℂ) = 0 := by
      rw [hφH i z hz]; simp
    push_cast at h'
    simpa using h'
  · intro c hc
    by_contra hall
    push_neg at hall
    -- real and imaginary parts
    set ψa : ℂ → ℝ := fun z => ∑ i, (c i).re * φ i z with hψa
    set ψb : ℂ → ℝ := fun z => ∑ i, (c i).im * φ i z with hψb
    have hsplit : (fun z => ∑ i, c i * (φ i z : ℂ)) =
        fun z => (ψa z : ℂ) + (ψb z : ℂ) * I := by
      funext z
      simp only [hψa, hψb]
      push_cast
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      conv_lhs => rw [← Complex.re_add_im (c i)]
      ring
    have hψa1 : ContDiffOn ℝ 1 ψa V' :=
      ContDiffOn.sum fun i _ => contDiffOn_const.mul (hφ1' i)
    have hψb1 : ContDiffOn ℝ 1 ψb V' :=
      ContDiffOn.sum fun i _ => contDiffOn_const.mul (hφ1' i)
    have hdiff : ∀ {ψ : ℂ → ℝ}, ContDiffOn ℝ 1 ψ V' → ∀ z ∈ V', DifferentiableAt ℝ ψ z :=
      fun h z hz => (h.contDiffAt (hV'o.mem_nhds hz)).differentiableAt one_ne_zero
    -- the derivative of the complex combination
    have hfd : ∀ z ∈ V', ∀ v : ℂ,
        fderiv ℝ (fun z => ∑ i, c i * (φ i z : ℂ)) z v =
          (fderiv ℝ ψa z v : ℂ) + (fderiv ℝ ψb z v : ℂ) * I := by
      intro z hz v
      rw [hsplit]
      have ha := (hdiff hψa1 z hz).hasFDerivAt
      have hb := (hdiff hψb1 z hz).hasFDerivAt
      have h := ((Complex.ofRealCLM.hasFDerivAt.comp z ha).add
        ((Complex.ofRealCLM.hasFDerivAt.comp z hb).mul_const I))
      have e : (fun z => (ψa z : ℂ) + (ψb z : ℂ) * I) =
          (⇑Complex.ofRealCLM ∘ ψa + fun y => (⇑Complex.ofRealCLM ∘ ψb) y * I) := rfl
      rw [e, h.fderiv]
      simp [mul_comm]
    -- vanishing of all derivatives on the boundary
    have hbd : ∀ {ψ : ℂ → ℝ}, ContDiffOn ℝ 1 ψ V' → (∀ z ∈ F '' sphere 0 rs, ψ z = 0) →
        (∀ θ ∈ Icc (0 : ℝ) (2 * π), fderiv ℝ ψ (F (rs * exp (θ * I))) (-I * dAng F rs θ) = 0) →
        ∀ z ∈ F '' sphere 0 rs, ψ z = 0 ∧ fderiv ℝ ψ z = 0 := by
      intro ψ hψ1 hψ0 hn z hz
      refine ⟨hψ0 z hz, ?_⟩
      obtain ⟨w, hw, rfl⟩ := hz
      obtain ⟨θ, hθ, rfl⟩ := exists_angle_of_mem_sphere hw
      have hmem : ∀ t : ℝ, (rs : ℂ) * exp (t * I) ∈ sphere (0 : ℂ) rs := fun t => by
        simp [Complex.norm_exp_ofReal_mul_I, abs_of_pos hrs.1]
      have hFd : DifferentiableAt ℂ F (rs * exp (θ * I)) :=
        hF.differentiableAt (hU.mem_nhds (hDU' (sphere_subset_closedBall (hmem θ))))
      have hψd := hdiff hψ1 _ (hV'sub ⟨_, sphere_subset_closedBall (hmem θ), rfl⟩)
      have htan := fderiv_dAng_eq_zero F hFd hψd fun t => hψ0 _ ⟨_, hmem t, rfl⟩
      have hd0 : dAng F rs θ ≠ 0 := by
        have hne := deriv_ne_zero_of_injOn hU hF hinj
          (hDU' (sphere_subset_closedBall (hmem θ)))
        simp only [dAng]
        have : (rs : ℂ) ≠ 0 := by exact_mod_cast hrs.1.ne'
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero I_ne_zero this) (Complex.exp_ne_zero _)) hne
      exact clm_eq_zero_of_apply_eq_zero hd0 htan (hn θ hθ)
    have hnorm : ∀ θ ∈ Icc (0 : ℝ) (2 * π),
        fderiv ℝ ψa (F (rs * exp (θ * I))) (-I * dAng F rs θ) = 0 ∧
        fderiv ℝ ψb (F (rs * exp (θ * I))) (-I * dAng F rs θ) = 0 := by
      intro θ hθ
      have hmem : (rs : ℂ) * exp (θ * I) ∈ closedBall (0 : ℂ) rs := by
        simp [Complex.norm_exp_ofReal_mul_I, abs_of_pos hrs.1]
      have h := hall θ hθ
      rw [hfd _ (hV'sub ⟨_, hmem, rfl⟩)] at h
      have h1 := congrArg Complex.re h
      have h2 := congrArg Complex.im h
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.zero_re,
        Complex.zero_im] at h1 h2
      constructor
      · simpa using h1
      · simpa using h2
    have hzero : ∀ (a : Fin J.card → ℝ), (∀ θ ∈ Icc (0 : ℝ) (2 * π),
        fderiv ℝ (fun z => ∑ i, a i * φ i z) (F (rs * exp (θ * I))) (-I * dAng F rs θ) = 0) →
        a = 0 := by
      intro a ha
      have h1 : ContDiffOn ℝ 1 (fun z => ∑ i, a i * φ i z) V' :=
        ContDiffOn.sum fun i _ => contDiffOn_const.mul (hφ1' i)
      have h0 : ∀ z ∈ F '' sphere 0 rs, (∑ i, a i * φ i z) = 0 := fun z hz => by
        simp [hφ0 _ z hz]
      have hcd := hbd h1 h0 ha
      have hEq := eq_zero_of_zero_cauchy_data F U hU hDU hF hinj hk hrs
        (fun z => ∑ i, a i * φ i z) hV'o hV'sub h1
        (ContDiffOn.sum fun i _ => contDiffOn_const.mul (hφ2 i))
        (fun z hz => by
          rw [laplacian_sum_mul Finset.univ a φ
            (fun i _ => (hφ2 i).contDiffAt (hΩ.mem_nhds hz)), Finset.mul_sum,
            ← Finset.sum_add_distrib]
          refine Finset.sum_eq_zero fun i _ => ?_
          have := hφH i z hz
          linear_combination a i * this) hcd
      apply huind a
      have hall' : ∀ᵐ z ∂(volume.restrict (F '' ball 0 rs)), ∀ i, u i z = φ i z :=
        ae_all_iff.2 hφae
      filter_upwards [hall', ae_restrict_mem (hΩ.measurableSet)] with z hz hzΩ
      simp only [Pi.zero_apply, hz]
      exact hEq z hzΩ
    have ha := hzero (fun i => (c i).re) fun θ hθ => (hnorm θ hθ).1
    have hb := hzero (fun i => (c i).im) fun θ hθ => (hnorm θ hθ).2
    apply hc
    funext i
    have h1 := congrFun ha i
    have h2 := congrFun hb i
    simp only [Pi.zero_apply] at h1 h2
    exact Complex.ext h1 h2

end

section

/-! ## Herglotz approximation of a Dirichlet pole -/

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory Set Real Metric Complex Filter Topology

/-- **Regular Dirichlet eigenfunctions.** If `k² = λ_j(F(r_*𝔻))` for every
`j` in a finite set `J` of indices `≥ 1`, there are `#J` eigenfunctions `φ_i` which solve the
Helmholtz equation in `Ω_{r_*} = F(r_*𝔻)`, vanish on `∂Ω_{r_*} = F(r_* 𝕋)`, are `C¹` on a
neighbourhood of `∂Ω_{r_*}` (after odd reflection across the analytic boundary curve), and whose
normal derivatives on `∂Ω_{r_*}` are linearly independent. -/
theorem dirichlet_eigenfunctions_boundary (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hDU : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    {k : ℝ} (hk : 0 < k) {rs : ℝ} (hrs : rs ∈ Ioc (0 : ℝ) 1) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, 1 ≤ j ∧ dirichletEigenvalue (F '' ball 0 rs) j = ENNReal.ofReal (k ^ 2)) :
    ∃ (V : Set ℂ) (φ : Fin J.card → ℂ → ℂ), IsOpen V ∧ F '' sphere 0 rs ⊆ V ∧
      (∀ i, ContDiffOn ℝ 1 (φ i) V) ∧
      (∀ i, IsHelmholtzOn k (φ i) (F '' ball 0 rs)) ∧
      (∀ i, ∀ z ∈ F '' sphere 0 rs, φ i z = 0) ∧
      ∀ c : Fin J.card → ℂ, c ≠ 0 → ∃ θ ∈ Icc (0 : ℝ) (2 * π),
        fderiv ℝ (fun z => ∑ i, c i * φ i z) (F (rs * exp (θ * I))) (-I * dAng F rs θ) ≠ 0 :=
  dirichlet_eigenfunctions_boundary_proof F U hU hDU hF hinj hk hrs J hJ

/-- **Runge approximation for the Helmholtz equation.** A solution of `Δφ + k²φ = 0` on
`Ω_{r_*} = F(r_*𝔻)` is approximated, with its first derivatives, uniformly on `F(r𝔻̄)`
(`r < r_*`) by solutions of the Helmholtz equation on the whole plane. -/
theorem helmholtz_runge_entire (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hDU : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    {k : ℝ} (hk : 0 < k) {rs : ℝ} (hrs : rs ∈ Ioc (0 : ℝ) 1) {φ : ℂ → ℂ}
    (hφ : IsHelmholtzOn k φ (F '' ball 0 rs)) {r : ℝ} (hr : r ∈ Ioo 0 rs) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ ψ : ℂ → ℂ, IsHelmholtzOn k ψ univ ∧ ∀ z ∈ F '' closedBall 0 r,
      ‖ψ z - φ z‖ < ε ∧ ‖fderiv ℝ ψ z - fderiv ℝ φ z‖ < ε :=
  helmholtz_runge_entire_proof F U hU hDU hF hinj hk hrs hφ hr hε

/-- **Density of Herglotz wave functions.** A solution of
`Δφ + k²φ = 0` on `Ω_{r_*} = F(r_*𝔻)` is approximated, with its first derivatives, uniformly on
`F(r𝔻̄)` (`r < r_*`) by Herglotz wave functions. -/
theorem herglotz_runge (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hDU : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    {k : ℝ} (hk : 0 < k) {rs : ℝ} (hrs : rs ∈ Ioc (0 : ℝ) 1) {φ : ℂ → ℂ}
    (hφ : IsHelmholtzOn k φ (F '' ball 0 rs)) {r : ℝ} (hr : r ∈ Ioo 0 rs) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ a : CircFun, ∀ z ∈ F '' closedBall 0 r,
      ‖herglotzWave k a z - φ z‖ < ε ∧ ‖fderiv ℝ (herglotzWave k a) z - fderiv ℝ φ z‖ < ε := by
  obtain ⟨ψ, hψ, happrox⟩ :=
    helmholtz_runge_entire F U hU hDU hF hinj hk hrs hφ hr (half_pos hε)
  have hsubU : closedBall (0 : ℂ) r ⊆ U :=
    (closedBall_subset_closedBall (hr.2.le.trans hrs.2)).trans hDU
  obtain ⟨R', hR'⟩ := ((isCompact_closedBall (0 : ℂ) r).image_of_continuousOn
    (hF.continuousOn.mono hsubU)).isBounded.subset_closedBall 0
  obtain ⟨a, ha⟩ := herglotz_approx_ball hk.ne'
    (hψ.mono (subset_univ (ball (0 : ℂ) (R' + 1)))) (lt_add_one R') (half_pos hε)
  refine ⟨a, fun z hz => ?_⟩
  obtain ⟨h1, h2⟩ := ha z (hR' hz)
  obtain ⟨h3, h4⟩ := happrox z hz
  constructor
  · calc ‖herglotzWave k a z - φ z‖ ≤ ‖herglotzWave k a z - ψ z‖ + ‖ψ z - φ z‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add h1 h3
      _ = ε := add_halves ε
  · calc ‖fderiv ℝ (herglotzWave k a) z - fderiv ℝ φ z‖ ≤
          ‖fderiv ℝ (herglotzWave k a) z - fderiv ℝ ψ z‖ + ‖fderiv ℝ ψ z - fderiv ℝ φ z‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add h2 h4
      _ = ε := add_halves ε

/-! ### Quadratic forms on `ℂ^m` -/

/-- The sesquilinear form `Re Σ_{i,j} c̄_i A_{ij} c_j`. -/
def qform {m : ℕ} (A : Fin m → Fin m → ℂ) (c : Fin m → ℂ) : ℝ :=
  (∑ i, ∑ j, conj (c i) * A i j * c j).re

lemma qform_smul {m : ℕ} (A : Fin m → Fin m → ℂ) (c : Fin m → ℂ) (t : ℝ) :
    qform A ((t : ℂ) • c) = t ^ 2 * qform A c := by
  unfold qform
  have : ∑ i, ∑ j, conj (((t : ℂ) • c) i) * A i j * ((t : ℂ) • c) j =
      ((t ^ 2 : ℝ) : ℂ) * ∑ i, ∑ j, conj (c i) * A i j * c j := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
    push_cast; ring
  rw [this, Complex.re_ofReal_mul]

lemma qform_sub_le {m : ℕ} (A B : Fin m → Fin m → ℂ) (c : Fin m → ℂ) (hc : ‖c‖ ≤ 1) {η : ℝ}
    (hη : ∀ i j, ‖B i j - A i j‖ ≤ η) : |qform B c - qform A c| ≤ m ^ 2 * η := by
  unfold qform
  rw [← Complex.sub_re, ← Finset.sum_sub_distrib]
  refine (Complex.abs_re_le_norm _).trans ?_
  refine (norm_sum_le _ _).trans ?_
  have hci : ∀ i, ‖c i‖ ≤ 1 := fun i => (norm_le_pi_norm c i).trans hc
  calc ∑ i, ‖∑ j, conj (c i) * B i j * c j - ∑ j, conj (c i) * A i j * c j‖
      ≤ ∑ i : Fin m, ∑ j : Fin m, η := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        have : conj (c i) * B i j * c j - conj (c i) * A i j * c j =
            conj (c i) * (B i j - A i j) * c j := by ring
        rw [this, norm_mul, norm_mul, Complex.norm_conj]
        have hη0 : 0 ≤ η := (norm_nonneg _).trans (hη i j)
        calc ‖c i‖ * ‖B i j - A i j‖ * ‖c j‖ ≤ 1 * η * 1 := by
              gcongr
              · exact hci i
              · exact hη i j
              · exact hci j
          _ = η := by ring
    _ = m ^ 2 * η := by simp; ring

/-- Positive definiteness of `qform A` is an open condition on `A`. -/
lemma posDef_open {m : ℕ} (A : Fin m → Fin m → ℂ) (hA : ∀ c : Fin m → ℂ, c ≠ 0 → 0 < qform A c) :
    ∃ η > 0, ∀ B : Fin m → Fin m → ℂ, (∀ i j, ‖B i j - A i j‖ < η) →
      ∀ c : Fin m → ℂ, c ≠ 0 → 0 < qform B c := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨1, one_pos, fun B _ c hc => absurd (Subsingleton.elim c 0) hc⟩
  have hcont : Continuous (qform A) := by
    unfold qform; fun_prop
  have hne : (sphere (0 : Fin m → ℂ) 1).Nonempty := by
    haveI : Nontrivial (Fin m → ℂ) := by
      haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
      infer_instance
    exact NormedSpace.sphere_nonempty.2 zero_le_one
  obtain ⟨c0, hc0, hmin⟩ := (isCompact_sphere (0 : Fin m → ℂ) 1).exists_isMinOn hne
    hcont.continuousOn
  have hc0ne : c0 ≠ 0 := by
    rintro rfl; simp at hc0
  set δ := qform A c0
  have hδ : 0 < δ := hA c0 hc0ne
  refine ⟨δ / (m ^ 2 + 1), by positivity, fun B hB c hc => ?_⟩
  have hcn : 0 < ‖c‖ := norm_pos_iff.2 hc
  set c' : Fin m → ℂ := ((‖c‖⁻¹ : ℝ) : ℂ) • c
  have hc'1 : ‖c'‖ = 1 := by
    simp only [c', norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    field_simp
  have hcc : c = ((‖c‖ : ℝ) : ℂ) • c' := by
    simp only [c', smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hcn.ne', Complex.ofReal_one,
      one_smul]
  have hAc' : δ ≤ qform A c' := hmin (by simpa using hc'1)
  have hle := qform_sub_le A B c' hc'1.le (η := δ / (m ^ 2 + 1)) fun i j => (hB i j).le
  have hB' : 0 < qform B c' := by
    have h1 : (m : ℝ) ^ 2 * (δ / (m ^ 2 + 1)) < δ := by
      rw [mul_div_assoc']; rw [div_lt_iff₀ (by positivity)]; nlinarith
    have := (abs_le.1 hle).1
    linarith
  rw [hcc, qform_smul]
  positivity

/-! ### Boundary data on the curves `γ_r` -/

/-- The boundary matrix `A_{ij} = ∫₀^{2π} (-h̄_i d_j - C h̄_i h_j) dθ`. -/
def bdMat {m : ℕ} (h d : Fin m → ℝ → ℂ) (C : ℝ) : Fin m → Fin m → ℂ := fun i j =>
  ∫ θ in (0 : ℝ)..(2 * π), (-(conj (h i θ) * d j θ) - C * (conj (h i θ) * h j θ))

/-- The trace `θ ↦ g(γ_r(θ))`. -/
def trc (F g : ℂ → ℂ) (r θ : ℝ) : ℂ := g (F (r * exp (θ * I)))

/-- The boundary derivative combination `D g(γ_r)(-i γ_r') - i D g(γ_r)(γ_r')`. -/
def bdDer (F g : ℂ → ℂ) (r θ : ℝ) : ℂ :=
  fderiv ℝ g (F (r * exp (θ * I))) (-I * dAng F r θ) -
    I * fderiv ℝ g (F (r * exp (θ * I))) (dAng F r θ)

/-- Expansion of the boundary form of a combination. -/
lemma qform_bdMat {m : ℕ} (h d : Fin m → ℝ → ℂ) (hh : ∀ i, Continuous (h i))
    (hd : ∀ i, Continuous (d i)) (C : ℝ) (c : Fin m → ℂ) :
    qform (bdMat h d C) c =
      -(∫ θ in (0 : ℝ)..(2 * π), conj (∑ i, c i * h i θ) * ∑ j, c j * d j θ).re -
        C * ∫ θ in (0 : ℝ)..(2 * π), ‖∑ i, c i * h i θ‖ ^ 2 := by
  have hcont : ∀ i j, Continuous fun θ => conj (c i) *
      (-(conj (h i θ) * d j θ) - C * (conj (h i θ) * h j θ)) * c j := by
    intro i j
    have := (hh i).star
    fun_prop
  have h1 : ∑ i, ∑ j, conj (c i) * bdMat h d C i j * c j =
      ∫ θ in (0 : ℝ)..(2 * π), ∑ i, ∑ j, conj (c i) *
        (-(conj (h i θ) * d j θ) - C * (conj (h i θ) * h j θ)) * c j := by
    rw [intervalIntegral.integral_finset_sum fun i _ =>
      (continuous_finset_sum _ fun j _ => hcont i j).intervalIntegrable _ _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finset_sum fun j _ => (hcont i j).intervalIntegrable _ _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [bdMat, intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
  have h2 : ∀ θ, ∑ i, ∑ j, conj (c i) *
        (-(conj (h i θ) * d j θ) - C * (conj (h i θ) * h j θ)) * c j =
      -(conj (∑ i, c i * h i θ) * ∑ j, c j * d j θ) -
        (C : ℂ) * ((‖∑ i, c i * h i θ‖ ^ 2 : ℝ) : ℂ) := by
    intro θ
    rw [Complex.ofReal_pow, ← Complex.conj_mul', map_sum, Finset.sum_mul, Finset.sum_mul,
      Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_mul]; ring
  have hs : Continuous fun θ => ∑ i, c i * h i θ := continuous_finset_sum _ fun i _ => by
      have := hh i; fun_prop
  have hc1 : Continuous fun θ => conj (∑ i, c i * h i θ) * ∑ j, c j * d j θ := by
    have h' : Continuous fun θ => ∑ j, c j * d j θ := continuous_finset_sum _ fun i _ => by
      have := hd i; fun_prop
    exact hs.star.mul h'
  have hc2 : Continuous fun θ => ‖∑ i, c i * h i θ‖ ^ 2 := by fun_prop
  have i1 : IntervalIntegrable (fun θ => -(conj (∑ i, c i * h i θ) * ∑ j, c j * d j θ))
      MeasureTheory.volume 0 (2 * π) := hc1.neg.intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun θ => (C : ℂ) * ((‖∑ i, c i * h i θ‖ ^ 2 : ℝ) : ℂ))
      MeasureTheory.volume 0 (2 * π) :=
    (continuous_const.mul (Complex.continuous_ofReal.comp hc2)).intervalIntegrable _ _
  unfold qform
  rw [h1, funext h2, intervalIntegral.integral_sub i1 i2,
    intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal]
  simp

lemma herglotzDir_sum {m : ℕ} (k : ℝ) (a : Fin m → CircFun) (c : Fin m → ℂ) (z : ℂ) :
    herglotzDir k (∑ i, c i • a i) z = ∑ i, c i • herglotzDir k (a i) z := by
  simp only [herglotzDir, Finset.sum_mul, smul_mul_assoc]

lemma herglotzWave_sum {m : ℕ} (k : ℝ) (a : Fin m → CircFun) (c : Fin m → ℂ) (z : ℂ) :
    herglotzWave k (∑ i, c i • a i) z = ∑ i, c i * herglotzWave k (a i) z := by
  simp only [herglotzWave, herglotzDir_sum, map_sum, map_smul, smul_eq_mul]

lemma fderiv_herglotzWave_sum {m : ℕ} (k : ℝ) (a : Fin m → CircFun) (c : Fin m → ℂ) (z w : ℂ) :
    fderiv ℝ (herglotzWave k (∑ i, c i • a i)) z w =
      ∑ i, c i * fderiv ℝ (herglotzWave k (a i)) z w := by
  simp only [fderiv_herglotzWave_apply, herglotzVec_sum, herglotzDir_sum, map_sum, map_smul,
    smul_eq_mul]
  rw [lp.coeFn_sum]
  simp only [lp.coeFn_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma continuous_herglotzWave (k : ℝ) (a : CircFun) : Continuous (herglotzWave k a) :=
  continuous_iff_continuousAt.2 fun z => (hasFDerivAt_herglotzWave k a z).continuousAt

lemma continuous_fderiv_herglotzWave (k : ℝ) (a : CircFun) :
    Continuous (fun p : ℂ × ℂ => fderiv ℝ (herglotzWave k a) p.1 p.2) := by
  have hD : Continuous (herglotzDir k a) :=
    continuous_iff_continuousAt.2 fun z => (hasFDerivAt_herglotzDir k a z).continuousAt
  simp only [fderiv_herglotzWave_apply, herglotzVec, circPos_apply]
  have h1 : Continuous fun z => circCoeff ((0 : ℕ) + 1 : ℤ) (herglotzDir k a z) :=
    (circCoeff _).continuous.comp hD
  have h2 : Continuous fun z => circCoeff (-1) (herglotzDir k a z) :=
    (circCoeff _).continuous.comp hD
  fun_prop

lemma continuous_circleCurve (F : ℂ → ℂ) {U : Set ℂ} (hDU : closedBall (0 : ℂ) 1 ⊆ U)
    (hF : DifferentiableOn ℂ F U) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    Continuous fun θ : ℝ => F (r * exp (θ * I)) :=
  hF.continuousOn.comp_continuous (by fun_prop) fun θ => hDU (by
    simp [Complex.norm_exp_ofReal_mul_I, abs_of_nonneg hr.1, hr.2])

lemma continuous_dAng (F : ℂ → ℂ) {U : Set ℂ} (hU : IsOpen U) (hDU : closedBall (0 : ℂ) 1 ⊆ U)
    (hF : DifferentiableOn ℂ F U) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) : Continuous (dAng F r) := by
  have hdF : ContinuousOn (deriv F) U := (hF.deriv hU).continuousOn
  have hc' : Continuous fun θ : ℝ => (r : ℂ) * exp (θ * I) := by fun_prop
  unfold dAng
  exact (continuous_const.mul (by fun_prop)).mul (hdF.comp_continuous hc' fun θ => hDU (by
    simp [Complex.norm_exp_ofReal_mul_I, abs_of_nonneg hr.1, hr.2]))

/-- A closed annulus `a ≤ |z| ≤ r_*` is mapped by `F` into an open set `V ⊇ F(r_* 𝕋)`. -/
lemma exists_annulus_subset (F : ℂ → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hDU : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U) {rs : ℝ}
    (hrs : rs ∈ Ioc (0 : ℝ) 1) {V : Set ℂ} (hV : IsOpen V) (hsub : F '' sphere 0 rs ⊆ V) :
    ∃ a ∈ Ioo 0 rs, ∀ ρ ∈ Icc a rs, ∀ θ : ℝ, F (ρ * exp (θ * I)) ∈ V := by
  have hW : IsOpen (U ∩ F ⁻¹' V) := hF.continuousOn.isOpen_inter_preimage hU hV
  have hK : sphere (0 : ℂ) rs ⊆ U ∩ F ⁻¹' V := fun z hz =>
    ⟨hDU ((sphere_subset_closedBall.trans (closedBall_subset_closedBall hrs.2)) hz),
      hsub ⟨z, hz, rfl⟩⟩
  obtain ⟨δ, hδ, hδsub⟩ := (isCompact_sphere (0 : ℂ) rs).exists_thickening_subset_open hW hK
  refine ⟨max (rs / 2) (rs - δ / 2), ⟨lt_max_of_lt_left (by linarith [hrs.1]),
    max_lt (by linarith [hrs.1]) (by linarith)⟩, fun ρ hρ θ => ?_⟩
  have hmem : (ρ : ℂ) * exp (θ * I) ∈ thickening δ (sphere (0 : ℂ) rs) := by
    rw [mem_thickening_iff]
    refine ⟨rs * exp (θ * I), by simp [Complex.norm_exp_ofReal_mul_I, abs_of_pos hrs.1], ?_⟩
    rw [dist_eq_norm, ← sub_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [hρ.1, hρ.2, le_max_right (rs / 2) (rs - δ / 2)]
  exact (hδsub hmem).2

/-- Radial derivative of `s ↦ F(s e^{iθ})`. -/
lemma hasDerivAt_radialCurve (F : ℂ → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {s θ : ℝ} (hs : (s : ℂ) * exp (θ * I) ∈ U) :
    HasDerivAt (fun t : ℝ => F (t * exp (θ * I))) (exp (θ * I) * deriv F (s * exp (θ * I))) s := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * exp (θ * I)) (1 * exp (θ * I)) s :=
    (hasDerivAt_id s).ofReal_comp.mul_const _
  have h2 := ((hF.differentiableAt (hU.mem_nhds hs)).hasDerivAt).comp s h1
  convert h2 using 1 <;> simp [Function.comp_def, mul_comm, mul_left_comm, mul_assoc]

/-- **Pole asymptotics.** Functions `φ_i` that are `C¹` near `∂Ω_{r_*}`, vanish on it and have
linearly independent normal derivatives have positive definite boundary matrix at every radius
`r < r_*` close enough to `r_*`. -/
lemma boundary_pole_asymptotic (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hDU : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U)
    {rs : ℝ} (hrs : rs ∈ Ioc (0 : ℝ) 1) {m : ℕ} (V : Set ℂ) (φ : Fin m → ℂ → ℂ)
    (hV : IsOpen V) (hsub : F '' sphere 0 rs ⊆ V) (hφ : ∀ i, ContDiffOn ℝ 1 (φ i) V)
    (hzero : ∀ i, ∀ z ∈ F '' sphere 0 rs, φ i z = 0)
    (hind : ∀ c : Fin m → ℂ, c ≠ 0 → ∃ θ ∈ Icc (0 : ℝ) (2 * π),
        fderiv ℝ (fun z => ∑ i, c i * φ i z) (F (rs * exp (θ * I))) (-I * dAng F rs θ) ≠ 0)
    (C : ℝ) :
    ∀ᶠ r in 𝓝[<] rs, ∀ c : Fin m → ℂ, c ≠ 0 →
      0 < qform (bdMat (fun i => trc F (φ i) r) (fun i => bdDer F (φ i) r) C) c := by
  obtain ⟨a, ha, haV⟩ := exists_annulus_subset F hU hDU hF hrs hV hsub
  have hfd : ∀ i, ContinuousOn (fderiv ℝ (φ i)) V := fun i =>
    (hφ i).continuousOn_fderiv_of_isOpen hV le_rfl
  have hφd : ∀ i, ∀ z ∈ V, HasFDerivAt (φ i) (fderiv ℝ (φ i) z) z := fun i z hz =>
    (((hφ i).differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hz)).hasFDerivAt
  set p : ℝ → ℝ := fun ρ => max a (min ρ rs) with hpdef
  have hp : Continuous p := by fun_prop
  have hpI : ∀ ρ, p ρ ∈ Icc a rs := fun ρ =>
    ⟨le_max_left _ _, max_le ha.2.le (min_le_right _ _)⟩
  have hpid : ∀ ρ ∈ Icc a rs, p ρ = ρ := fun ρ hρ => by
    simp only [hpdef, min_eq_left hρ.2, max_eq_right hρ.1]
  have hU' : ∀ ρ ∈ Icc a rs, ∀ θ : ℝ, (ρ : ℂ) * exp (θ * I) ∈ U := fun ρ hρ θ => hDU (by
    simp [Complex.norm_exp_ofReal_mul_I, abs_of_pos (ha.1.trans_le hρ.1), hρ.2.trans hrs.2])
  set Rf : Fin m → ℝ → ℝ → ℂ := fun i ρ θ =>
    fderiv ℝ (φ i) (F (p ρ * exp (θ * I))) (exp (θ * I) * deriv F (p ρ * exp (θ * I)))
    with hRf
  set Tf : Fin m → ℝ → ℝ → ℂ := fun i ρ θ =>
    fderiv ℝ (φ i) (F (p ρ * exp (θ * I))) (dAng F (p ρ) θ) with hTf
  -- continuity
  have hz : Continuous fun x : ℝ × ℝ => (p x.1 : ℂ) * exp (x.2 * I) := by fun_prop
  have hzU : ∀ x : ℝ × ℝ, (p x.1 : ℂ) * exp (x.2 * I) ∈ U := fun x => hU' _ (hpI _) _
  have hγc : Continuous fun x : ℝ × ℝ => F (p x.1 * exp (x.2 * I)) :=
    hF.continuousOn.comp_continuous hz hzU
  have hγV : ∀ x : ℝ × ℝ, F (p x.1 * exp (x.2 * I)) ∈ V := fun x => haV _ (hpI _) _
  have hdF : Continuous fun x : ℝ × ℝ => deriv F (p x.1 * exp (x.2 * I)) :=
    (hF.deriv hU).continuousOn.comp_continuous hz hzU
  have hRc : ∀ i, Continuous fun x : ℝ × ℝ => Rf i x.1 x.2 := fun i =>
    ((hfd i).comp_continuous hγc hγV).clm_apply ((by fun_prop : Continuous fun x : ℝ × ℝ =>
      exp ((x.2 : ℂ) * I)).mul hdF)
  have hTc : ∀ i, Continuous fun x : ℝ × ℝ => Tf i x.1 x.2 := fun i => by
    refine ((hfd i).comp_continuous hγc hγV).clm_apply ?_
    simp only [dAng]
    exact (by fun_prop : Continuous fun x : ℝ × ℝ => I * (p x.1 : ℂ) * exp ((x.2 : ℂ) * I)).mul hdF
  set H : Fin m → ℝ → ℝ → ℂ := fun i ρ θ => -∫ t in (0 : ℝ)..1, Rf i (ρ + t * (rs - ρ)) θ
    with hHdef
  have hHc : ∀ i, Continuous fun x : ℝ × ℝ => H i x.1 x.2 := fun i => by
    have : Continuous fun q : (ℝ × ℝ) × ℝ => Rf i (q.1.1 + q.2 * (rs - q.1.1)) q.1.2 :=
      (hRc i).comp (f := fun q : (ℝ × ℝ) × ℝ => (q.1.1 + q.2 * (rs - q.1.1), q.1.2))
        (by fun_prop)
    exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' this 0 1).neg
  -- the boundary data in terms of `H`, `Rf`, `Tf`
  have hN : ∀ i, ∀ ρ ∈ Icc a rs, ∀ θ : ℝ,
      fderiv ℝ (φ i) (F (ρ * exp (θ * I))) (-I * dAng F ρ θ) = ρ * Rf i ρ θ := by
    intro i ρ hρ θ
    simp only [hRf, hpid ρ hρ]
    have : -I * dAng F ρ θ = (ρ : ℝ) • (exp (θ * I) * deriv F (ρ * exp (θ * I))) := by
      rw [Complex.real_smul]; unfold dAng; ring_nf; rw [Complex.I_sq]; ring
    rw [this, map_smul, Complex.real_smul]
  have hbd : ∀ i, ∀ ρ ∈ Icc a rs, ∀ θ : ℝ,
      bdDer F (φ i) ρ θ = ρ * Rf i ρ θ - I * Tf i ρ θ := by
    intro i ρ hρ θ
    simp only [bdDer, hN i ρ hρ θ, hTf, hpid ρ hρ]
  have htrc : ∀ i, ∀ ρ ∈ Icc a rs, ∀ θ : ℝ,
      trc F (φ i) ρ θ = ((rs - ρ : ℝ) : ℂ) * H i ρ θ := by
    intro i ρ hρ θ
    set g : ℝ → ℂ := fun t => φ i (F (((ρ + t * (rs - ρ) : ℝ) : ℂ) * exp (θ * I))) with hg
    set g' : ℝ → ℂ := fun t => ((rs - ρ : ℝ) : ℂ) * Rf i (ρ + t * (rs - ρ)) θ with hg'
    have hsI : ∀ t ∈ uIcc (0 : ℝ) 1, ρ + t * (rs - ρ) ∈ Icc a rs := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      constructor <;> nlinarith [hρ.1, hρ.2, ht.1, ht.2]
    have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt g (g' t) t := by
      intro t ht
      have hs := hsI t ht
      have h1 : HasDerivAt (fun t : ℝ => ρ + t * (rs - ρ)) (rs - ρ) t := by
        simpa using ((hasDerivAt_id t).mul_const (rs - ρ)).const_add ρ
      have h2 := hasDerivAt_radialCurve F hU hF (hU' _ hs θ)
      have h3 := (hφd i _ (haV _ hs θ)).comp_hasDerivAt _ h2
      have h4 := h3.scomp t h1
      convert h4 using 1
      · rw [hg]
        funext x
        simp [Function.comp_def]
      · rw [hg']
        simp [hRf, hpid _ hs, Complex.real_smul]
    have hint : IntervalIntegrable g' MeasureTheory.volume 0 1 :=
      (continuous_const.mul ((hRc i).comp (f := fun t : ℝ => (ρ + t * (rs - ρ), θ))
        (by fun_prop))).intervalIntegrable _ _
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have hg1 : g 1 = 0 := by
      simp only [hg, one_mul, add_sub_cancel]
      exact hzero i _ ⟨_, by simp [Complex.norm_exp_ofReal_mul_I, abs_of_pos hrs.1], rfl⟩
    have hg0 : g 0 = trc F (φ i) ρ θ := by simp [hg, trc]
    rw [hg1, hg0, hg', intervalIntegral.integral_const_mul] at hFTC
    simp only [hHdef]
    linear_combination hFTC
  have hT0 : ∀ i, ∀ θ : ℝ, Tf i rs θ = 0 := by
    intro i θ
    have hrsI : rs ∈ Icc a rs := ⟨ha.2.le, le_rfl⟩
    simp only [hTf, hpid rs hrsI]
    have h1 := (hφd i _ (haV _ hrsI θ)).comp_hasDerivAt θ
      (hasDerivAt_circleCurve F hU hF (hU' _ hrsI θ))
    have h0 : (φ i ∘ fun t : ℝ => F (rs * exp (t * I))) = fun _ => 0 := by
      funext t
      exact hzero i _ ⟨_, by simp [Complex.norm_exp_ofReal_mul_I, abs_of_pos hrs.1], rfl⟩
    rw [h0] at h1
    exact h1.unique (hasDerivAt_const θ 0)
  have hH0 : ∀ i, ∀ θ : ℝ, H i rs θ = -Rf i rs θ := by
    intro i θ
    simp [hHdef]
  -- the rescaled matrix
  set Bm : ℝ → Fin m → Fin m → ℂ := fun ρ => bdMat (fun i θ => H i ρ θ)
    (fun j θ => ρ * Rf j ρ θ - I * Tf j ρ θ) (C * (rs - ρ)) with hBm
  have hBc : ∀ i j, Continuous fun ρ => Bm ρ i j := by
    intro i j
    simp only [hBm, bdMat]
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ 0 (2 * π)
    have hc1 : Continuous fun x : ℝ × ℝ => conj (H i x.1 x.2) :=
      Complex.continuous_conj.comp (hHc i)
    have := hHc j
    have := hRc j
    have := hTc j
    have : Continuous fun x : ℝ × ℝ => -(conj (H i x.1 x.2) *
        ((x.1 : ℂ) * Rf j x.1 x.2 - I * Tf j x.1 x.2)) -
        ((C * (rs - x.1) : ℝ) : ℂ) * (conj (H i x.1 x.2) * H j x.1 x.2) := by fun_prop
    exact this
  -- factorization `A(ρ) = (r_* - ρ) B(ρ)`
  have hfac : ∀ ρ ∈ Icc a rs, bdMat (fun i => trc F (φ i) ρ) (fun i => bdDer F (φ i) ρ) C =
      fun i j => ((rs - ρ : ℝ) : ℂ) * Bm ρ i j := by
    intro ρ hρ
    funext i j
    simp only [bdMat, hBm, htrc _ ρ hρ, hbd _ ρ hρ]
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [map_mul, Complex.conj_ofReal]
    push_cast; ring
  have hqs : ∀ (t : ℝ) (A : Fin m → Fin m → ℂ) (c : Fin m → ℂ),
      qform (fun i j => (t : ℂ) * A i j) c = t * qform A c := by
    intro t A c
    unfold qform
    have : ∑ i, ∑ j, conj (c i) * ((t : ℂ) * A i j) * c j =
        (t : ℂ) * ∑ i, ∑ j, conj (c i) * A i j * c j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this, Complex.re_ofReal_mul]
  -- positive definiteness at `r_*`
  have hrsI : rs ∈ Icc a rs := ⟨ha.2.le, le_rfl⟩
  have hpos0 : ∀ c : Fin m → ℂ, c ≠ 0 → 0 < qform (Bm rs) c := by
    intro c hc
    obtain ⟨θ0, hθ0, hne⟩ := hind c hc
    set S : ℝ → ℂ := fun θ => ∑ i, c i * Rf i rs θ with hS
    have hSc : Continuous S := continuous_finset_sum _ fun i _ =>
      continuous_const.mul ((hRc i).comp (f := fun θ : ℝ => (rs, θ)) (by fun_prop))
    have hcH : ∀ i, Continuous fun θ => H i rs θ := fun i =>
      (hHc i).comp (f := fun θ : ℝ => (rs, θ)) (by fun_prop)
    have hcD : ∀ j, Continuous fun θ => (rs : ℂ) * Rf j rs θ - I * Tf j rs θ := fun j =>
      (continuous_const.mul ((hRc j).comp (f := fun θ : ℝ => (rs, θ)) (by fun_prop))).sub
        (continuous_const.mul ((hTc j).comp (f := fun θ : ℝ => (rs, θ)) (by fun_prop)))
    simp only [hBm]
    rw [qform_bdMat _ _ hcH hcD]
    have hpt : ∀ θ, conj (∑ i, c i * H i rs θ) *
        ∑ j, c j * ((rs : ℂ) * Rf j rs θ - I * Tf j rs θ) =
        -(rs : ℂ) * ((‖S θ‖ ^ 2 : ℝ) : ℂ) := by
      intro θ
      simp only [hH0, hT0, mul_zero, sub_zero]
      rw [show ∑ i, c i * -Rf i rs θ = -S θ by simp [hS, Finset.sum_neg_distrib],
        show ∑ j, c j * ((rs : ℂ) * Rf j rs θ) = (rs : ℂ) * S θ by
          simp only [hS, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring]
      rw [Complex.ofReal_pow, ← Complex.conj_mul', map_neg]; ring
    have hint : ∫ θ in (0 : ℝ)..(2 * π), conj (∑ i, c i * H i rs θ) *
        ∑ j, c j * ((rs : ℂ) * Rf j rs θ - I * Tf j rs θ) =
        -(rs : ℂ) * ((∫ θ in (0 : ℝ)..(2 * π), ‖S θ‖ ^ 2 : ℝ) : ℂ) := by
      simp_rw [hpt]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
    rw [hint]
    have hSne : S θ0 ≠ 0 := by
      intro h0
      apply hne
      have hγV0 : F (rs * exp (θ0 * I)) ∈ V := haV _ hrsI θ0
      have hsum : HasFDerivAt (fun z => ∑ i, c i * φ i z)
          (∑ i, c i • fderiv ℝ (φ i) (F (rs * exp (θ0 * I)))) (F (rs * exp (θ0 * I))) :=
        HasFDerivAt.fun_sum fun i _ => (hφd i _ hγV0).const_mul (c i)
      rw [hsum.fderiv]
      simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
        Pi.smul_apply, smul_eq_mul]
      simp_rw [hN _ rs hrsI θ0]
      have : ∑ i, c i * ((rs : ℂ) * Rf i rs θ0) = (rs : ℂ) * S θ0 := by
        simp only [hS, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [this, h0, mul_zero]
    have hSpos : 0 < ∫ θ in (0 : ℝ)..(2 * π), ‖S θ‖ ^ 2 := by
      refine intervalIntegral.integral_pos (by positivity) (hSc.norm.pow 2).continuousOn
        (fun _ _ => by positivity) ⟨θ0, hθ0, ?_⟩
      have := norm_pos_iff.2 hSne
      positivity
    rw [show -(rs : ℂ) * ((∫ θ in (0 : ℝ)..(2 * π), ‖S θ‖ ^ 2 : ℝ) : ℂ) =
        ((-(rs * ∫ θ in (0 : ℝ)..(2 * π), ‖S θ‖ ^ 2) : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re, sub_self, mul_zero, zero_mul, sub_zero, neg_neg]
    exact mul_pos hrs.1 hSpos
  obtain ⟨η, hη, hB⟩ := posDef_open _ hpos0
  have hev : ∀ᶠ ρ in 𝓝[<] rs, ∀ i j, ‖Bm ρ i j - Bm rs i j‖ < η := by
    simp only [Filter.eventually_all]
    intro i j
    have h1 := ((hBc i j).tendsto rs).mono_left (nhdsWithin_le_nhds (s := Iio rs))
    have h2 := (Metric.tendsto_nhds.1 h1) η hη
    simpa [dist_eq_norm] using h2
  filter_upwards [hev, Ioo_mem_nhdsLT ha.2] with ρ hρ hρI c hc
  rw [hfac ρ ⟨hρI.1.le, hρI.2.le⟩, hqs]
  exact mul_pos (by linarith [hρI.2]) (hB _ hρ c hc)

lemma continuous_trc_herglotz (F : ℂ → ℂ) {U : Set ℂ} (hDU : closedBall (0 : ℂ) 1 ⊆ U)
    (hF : DifferentiableOn ℂ F U) (k : ℝ) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (a : CircFun) :
    Continuous (trc F (herglotzWave k a) r) :=
  (continuous_herglotzWave k a).comp (continuous_circleCurve F hDU hF hr)

lemma continuous_bdDer_herglotz (F : ℂ → ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hDU : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U) (k : ℝ) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) (a : CircFun) : Continuous (bdDer F (herglotzWave k a) r) := by
  have hγ := continuous_circleCurve F hDU hF hr
  have hdA := continuous_dAng F hU hDU hF hr
  have h0 := continuous_fderiv_herglotzWave k a
  have h1 : Continuous fun θ : ℝ => fderiv ℝ (herglotzWave k a) (F (r * exp (θ * I)))
      (-I * dAng F r θ) := h0.comp (hγ.prodMk (continuous_const.mul hdA))
  have h2 : Continuous fun θ : ℝ => fderiv ℝ (herglotzWave k a) (F (r * exp (θ * I)))
      (dAng F r θ) := h0.comp (hγ.prodMk hdA)
  exact h1.sub (continuous_const.mul h2)

lemma conj_mul_close {x x' y y' : ℂ} {B ε : ℝ} (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B)
    (hx' : ‖x' - x‖ ≤ ε) (hy' : ‖y' - y‖ ≤ ε) (hε1 : ε ≤ 1) :
    ‖conj x' * y' - conj x * y‖ ≤ (2 * B + 1) * ε := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hx'
  have hy'B : ‖y'‖ ≤ B + 1 := by
    calc ‖y'‖ = ‖(y' - y) + y‖ := by ring_nf
      _ ≤ ‖y' - y‖ + ‖y‖ := norm_add_le _ _
      _ ≤ B + 1 := by linarith
  have : conj x' * y' - conj x * y = conj (x' - x) * y' + conj x * (y' - y) := by
    simp only [map_sub]; ring
  rw [this]
  calc ‖conj (x' - x) * y' + conj x * (y' - y)‖
      ≤ ‖x' - x‖ * ‖y'‖ + ‖x‖ * ‖y' - y‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
    _ ≤ ε * (B + 1) + B * ε := by
        gcongr
        exact (norm_nonneg _).trans hx
    _ = (2 * B + 1) * ε := by ring

/-- Entrywise stability of `bdMat` under uniform perturbation of the boundary data. -/
lemma bdMat_close {m : ℕ} (h d h' d' : Fin m → ℝ → ℂ) (hh : ∀ i, Continuous (h i))
    (hd : ∀ i, Continuous (d i)) (hh' : ∀ i, Continuous (h' i)) (hd' : ∀ i, Continuous (d' i))
    (C : ℝ) {B ε : ℝ} (hB : ∀ i, ∀ θ ∈ Icc (0 : ℝ) (2 * π), ‖h i θ‖ ≤ B ∧ ‖d i θ‖ ≤ B)
    (hε : ∀ i, ∀ θ ∈ Icc (0 : ℝ) (2 * π), ‖h' i θ - h i θ‖ ≤ ε ∧ ‖d' i θ - d i θ‖ ≤ ε)
    (hε1 : ε ≤ 1) (i j : Fin m) :
    ‖bdMat h' d' C i j - bdMat h d C i j‖ ≤ (1 + |C|) * ((2 * B + 1) * ε) * (2 * π) := by
  have hcont : ∀ (h d : Fin m → ℝ → ℂ), (∀ i, Continuous (h i)) → (∀ i, Continuous (d i)) →
      Continuous fun θ => -(conj (h i θ) * d j θ) - C * (conj (h i θ) * h j θ) := by
    intro h d hh hd
    have := (hh i).star
    have := hd j
    have := hh j
    fun_prop
  unfold bdMat
  rw [← intervalIntegral.integral_sub ((hcont h' d' hh' hd').intervalIntegrable _ _)
    ((hcont h d hh hd).intervalIntegrable _ _)]
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  refine (intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ => ?_).trans_eq
    (by rw [sub_zero, abs_of_nonneg h2π])
  rw [uIoc_of_le h2π] at hθ
  have hθ' : θ ∈ Icc (0 : ℝ) (2 * π) := ⟨hθ.1.le, hθ.2⟩
  have e1 := conj_mul_close (hB i θ hθ').1 (hB j θ hθ').2 (hε i θ hθ').1 (hε j θ hθ').2 hε1
  have e2 := conj_mul_close (hB i θ hθ').1 (hB j θ hθ').1 (hε i θ hθ').1 (hε j θ hθ').1 hε1
  have : -(conj (h' i θ) * d' j θ) - C * (conj (h' i θ) * h' j θ) -
      (-(conj (h i θ) * d j θ) - C * (conj (h i θ) * h j θ)) =
      -(conj (h' i θ) * d' j θ - conj (h i θ) * d j θ) -
        C * (conj (h' i θ) * h' j θ - conj (h i θ) * h j θ) := by ring
  rw [this]
  have hK : 0 ≤ (2 * B + 1) * ε := (norm_nonneg _).trans e1
  calc _ ≤ ‖conj (h' i θ) * d' j θ - conj (h i θ) * d j θ‖ +
        |C| * ‖conj (h' i θ) * h' j θ - conj (h i θ) * h j θ‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (2 * B + 1) * ε + |C| * ((2 * B + 1) * ε) := by gcongr
    _ = (1 + |C|) * ((2 * B + 1) * ε) := by ring

/-- **Herglotz approximation at a fixed radius.** If the boundary matrix of `φ_1, …, φ_m` at
radius `r < r_*` is positive definite and each `φ_i` solves the Helmholtz equation in `Ω_{r_*}`,
then Herglotz waves `u_{a_i}` have positive definite boundary matrix too. -/
lemma herglotz_posDef (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hDU : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    {k : ℝ} (hk : 0 < k) {rs : ℝ} (hrs : rs ∈ Ioc (0 : ℝ) 1) {m : ℕ} (φ : Fin m → ℂ → ℂ)
    (hφ : ∀ i, IsHelmholtzOn k (φ i) (F '' ball 0 rs)) {r : ℝ} (hr : r ∈ Ioo 0 rs) (C : ℝ)
    (hpos : ∀ c : Fin m → ℂ, c ≠ 0 →
      0 < qform (bdMat (fun i => trc F (φ i) r) (fun i => bdDer F (φ i) r) C) c) :
    ∃ a : Fin m → CircFun, ∀ c : Fin m → ℂ, c ≠ 0 →
      0 < qform (bdMat (fun i => trc F (herglotzWave k (a i)) r)
        (fun i => bdDer F (herglotzWave k (a i)) r) C) c := by
  obtain ⟨η, hη, hB⟩ := posDef_open _ hpos
  have hr1 : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1.le, hr.2.le.trans hrs.2⟩
  have hball1 : ball (0 : ℂ) 1 ⊆ U := ball_subset_closedBall.trans hDU
  have hΩ : IsOpen (F '' ball 0 rs) :=
    isOpen_image_of_injOn isOpen_ball (convex_ball _ _).isPreconnected
      (hF.mono hball1) (hinj.mono hball1) (ball_subset_ball hrs.2) isOpen_ball
  have hγ := continuous_circleCurve F hDU hF hr1
  have hdA := continuous_dAng F hU hDU hF hr1
  have hγΩ : ∀ θ : ℝ, F (r * exp (θ * I)) ∈ F '' ball 0 rs := fun θ =>
    ⟨_, by simp [Complex.norm_exp_ofReal_mul_I, abs_of_pos hr.1, hr.2], rfl⟩
  have hγK : ∀ θ : ℝ, F (r * exp (θ * I)) ∈ F '' closedBall 0 r := fun θ =>
    ⟨_, by simp [Complex.norm_exp_ofReal_mul_I, abs_of_pos hr.1], rfl⟩
  -- continuity of the data of `φ_i`
  have hφc : ∀ i, Continuous (trc F (φ i) r) := fun i =>
    (hφ i).1.continuousOn.comp_continuous hγ hγΩ
  have hφd : ∀ i, ContinuousOn (fderiv ℝ (φ i)) (F '' ball 0 rs) := fun i =>
    (hφ i).1.continuousOn_fderiv_of_isOpen hΩ (by norm_num)
  have hφdc : ∀ i, Continuous fun θ : ℝ => fderiv ℝ (φ i) (F (r * exp (θ * I))) :=
    fun i => (hφd i).comp_continuous hγ hγΩ
  have hφD : ∀ i, Continuous (bdDer F (φ i) r) := fun i =>
    ((hφdc i).clm_apply (continuous_const.mul hdA)).sub
      (continuous_const.mul ((hφdc i).clm_apply hdA))
  -- bounds
  obtain ⟨B, hBd⟩ : ∃ B, ∀ θ ∈ Icc (0 : ℝ) (2 * π),
      ‖∑ i, (‖trc F (φ i) r θ‖ + ‖bdDer F (φ i) r θ‖)‖ ≤ B :=
    isCompact_Icc.exists_bound_of_continuousOn (Continuous.continuousOn (by
      refine continuous_finset_sum _ fun i _ => ?_
      exact (hφc i).norm.add (hφD i).norm))
  have hBi : ∀ i, ∀ θ ∈ Icc (0 : ℝ) (2 * π), ‖trc F (φ i) r θ‖ ≤ B ∧ ‖bdDer F (φ i) r θ‖ ≤ B := by
    intro i θ hθ
    have h1 := hBd θ hθ
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity)] at h1
    have h2 := Finset.single_le_sum (f := fun i => ‖trc F (φ i) r θ‖ + ‖bdDer F (φ i) r θ‖)
      (fun _ _ => by positivity) (Finset.mem_univ i)
    constructor <;> linarith [norm_nonneg (trc F (φ i) r θ), norm_nonneg (bdDer F (φ i) r θ)]
  obtain ⟨M, hM⟩ : ∃ M, ∀ θ ∈ Icc (0 : ℝ) (2 * π), ‖dAng F r θ‖ ≤ M :=
    isCompact_Icc.exists_bound_of_continuousOn hdA.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, by positivity⟩)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hBd 0 ⟨le_rfl, by positivity⟩)
  set K := (1 + |C|) * (2 * B + 1) * (2 * π) with hK
  have hK0 : 0 < K := by positivity
  set ε := min 1 (η / (2 * K)) with hεdef
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεK : K * ε < η := by
    calc K * ε ≤ K * (η / (2 * K)) := by gcongr; exact min_le_right _ _
      _ = η / 2 := by field_simp
      _ < η := by linarith
  set ε0 := ε / (1 + 2 * M) with hε0def
  have hε00 : 0 < ε0 := by positivity
  have hrun := fun i => herglotz_runge F U hU hDU hF hinj hk hrs (hφ i) hr hε00
  choose a ha using hrun
  refine ⟨a, hB _ fun i j => ?_⟩
  have hcl := bdMat_close (fun i => trc F (φ i) r) (fun i => bdDer F (φ i) r)
    (fun i => trc F (herglotzWave k (a i)) r) (fun i => bdDer F (herglotzWave k (a i)) r)
    hφc hφD (fun i => (continuous_trc_herglotz F hDU hF k hr1 (a i)))
    (fun i => continuous_bdDer_herglotz F hU hDU hF k hr1 (a i)) C hBi (ε := ε) ?_ hε1 i j
  · calc _ ≤ (1 + |C|) * ((2 * B + 1) * ε) * (2 * π) := hcl
      _ = K * ε := by rw [hK]; ring
      _ < η := hεK
  · intro i θ hθ
    obtain ⟨h1, h2⟩ := ha i _ (hγK θ)
    have hε0ε : ε0 ≤ ε := by
      rw [hε0def]; exact div_le_self hε0.le (by linarith)
    refine ⟨(h1.le.trans hε0ε), ?_⟩
    simp only [bdDer]
    set L := fderiv ℝ (herglotzWave k (a i)) (F (r * exp (θ * I))) -
      fderiv ℝ (φ i) (F (r * exp (θ * I)))
    have : fderiv ℝ (herglotzWave k (a i)) (F (r * exp (θ * I))) (-I * dAng F r θ) -
        I * fderiv ℝ (herglotzWave k (a i)) (F (r * exp (θ * I))) (dAng F r θ) -
        (fderiv ℝ (φ i) (F (r * exp (θ * I))) (-I * dAng F r θ) -
        I * fderiv ℝ (φ i) (F (r * exp (θ * I))) (dAng F r θ)) =
        L (-I * dAng F r θ) - I * L (dAng F r θ) := by
      simp only [L, ContinuousLinearMap.sub_apply]; ring
    rw [this]
    have hdM := hM θ hθ
    calc ‖L (-I * dAng F r θ) - I * L (dAng F r θ)‖
        ≤ ‖L‖ * ‖-I * dAng F r θ‖ + ‖L‖ * ‖dAng F r θ‖ := by
          refine (norm_sub_le _ _).trans (add_le_add (L.le_opNorm _) ?_)
          rw [norm_mul, Complex.norm_I, one_mul]; exact L.le_opNorm _
      _ ≤ ε0 * M + ε0 * M := by
          rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
          gcongr
      _ ≤ ε := by
          rw [hε0def, ← add_mul, ← two_mul]
          rw [show 2 * (ε / (1 + 2 * M)) * M = ε * (2 * M / (1 + 2 * M)) by ring]
          exact mul_le_of_le_one_right hε0.le
            ((div_le_one (by positivity)).2 (by linarith))

/-- Conversion of the positive definite boundary matrix of Herglotz waves into the boundary
inequality for the Herglotz wave of the combined density. -/
lemma herglotz_qform_eq (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hDU : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U) (k : ℝ) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) (C : ℝ) {m : ℕ} (a : Fin m → CircFun) (c : Fin m → ℂ) :
    qform (bdMat (fun i => trc F (herglotzWave k (a i)) r)
        (fun i => bdDer F (herglotzWave k (a i)) r) C) c =
      -(∫ θ in (0 : ℝ)..(2 * π),
            conj (herglotzWave k (∑ i, c i • a i) (F (r * exp (θ * I)))) *
              (fderiv ℝ (herglotzWave k (∑ i, c i • a i)) (F (r * exp (θ * I)))
                  (-I * dAng F r θ) -
                I * fderiv ℝ (herglotzWave k (∑ i, c i • a i)) (F (r * exp (θ * I)))
                  (dAng F r θ))).re -
        C * ∫ θ in (0 : ℝ)..(2 * π),
            ‖herglotzWave k (∑ i, c i • a i) (F (r * exp (θ * I)))‖ ^ 2 := by
  have hγ := continuous_circleCurve F hDU hF hr
  have hdA := continuous_dAng F hU hDU hF hr
  have hh : ∀ i, Continuous (trc F (herglotzWave k (a i)) r) := fun i =>
    (continuous_herglotzWave k (a i)).comp hγ
  have hd : ∀ i, Continuous (bdDer F (herglotzWave k (a i)) r) := fun i => by
    have h0 := continuous_fderiv_herglotzWave k (a i)
    have h1 : Continuous fun θ : ℝ => fderiv ℝ (herglotzWave k (a i)) (F (r * exp (θ * I)))
        (-I * dAng F r θ) := h0.comp (hγ.prodMk (continuous_const.mul hdA))
    have h2 : Continuous fun θ : ℝ => fderiv ℝ (herglotzWave k (a i)) (F (r * exp (θ * I)))
        (dAng F r θ) := h0.comp (hγ.prodMk hdA)
    exact h1.sub (continuous_const.mul h2)
  rw [qform_bdMat _ _ hh hd]
  simp only [trc, bdDer, herglotzWave_sum, fderiv_herglotzWave_sum]
  congr 3
  refine intervalIntegral.integral_congr fun θ _ => ?_
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Herglotz approximation of a Dirichlet pole.**
Suppose `k² = λ_j(F(r_*𝔻))` for every index `j` in a finite set `J` of indices `≥ 1`. For every
constant `C` and every nonresonant radius `r < r_*` sufficiently close to `r_*` there are
Herglotz densities `a_1, …, a_{#J}` such that every nonzero combination `u = u_{Σ c_i a_i}` has
boundary trace `h = u ∘ γ_r` (`γ_r(θ) = F(r e^{iθ})`) with
`⟪h, Λ_r h⟫ - ⟪h, i ∂_θ h⟫ < -C ‖h‖²_{L²}`,
where `Λ_r h = |γ_r'| ∂_ν u ∘ γ_r = D u(γ_r)(-i γ_r')` is the conormal derivative of `u` and
`∂_θ h = D u(γ_r)(γ_r')`. -/
theorem herglotz_dirichlet_pole (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hDU : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    {k : ℝ} (hk : 0 < k) {rs : ℝ} (hrs : rs ∈ Ioc (0 : ℝ) 1) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, 1 ≤ j ∧ dirichletEigenvalue (F '' ball 0 rs) j = ENNReal.ofReal (k ^ 2))
    (C : ℝ) :
    ∀ᶠ r in 𝓝[<] rs,
      (∀ j : ℕ, 1 ≤ j → dirichletEigenvalue (F '' ball 0 r) j ≠ ENNReal.ofReal (k ^ 2)) →
      ∃ a : Fin J.card → CircFun, ∀ c : Fin J.card → ℂ, c ≠ 0 →
        C * ∫ θ in (0 : ℝ)..(2 * π),
            ‖herglotzWave k (∑ i, c i • a i) (F (r * exp (θ * I)))‖ ^ 2 <
          -(∫ θ in (0 : ℝ)..(2 * π),
            conj (herglotzWave k (∑ i, c i • a i) (F (r * exp (θ * I)))) *
              (fderiv ℝ (herglotzWave k (∑ i, c i • a i)) (F (r * exp (θ * I)))
                  (-I * dAng F r θ) -
                I * fderiv ℝ (herglotzWave k (∑ i, c i • a i)) (F (r * exp (θ * I)))
                  (dAng F r θ))).re := by
  obtain ⟨V, φ, hV, hsub, hφ1, hφH, hzero, hind⟩ :=
    dirichlet_eigenfunctions_boundary F U hU hDU hF hinj hk hrs J hJ
  have hev := boundary_pole_asymptotic F U hU hDU hF hrs V φ hV hsub hφ1 hzero hind C
  have hnear : ∀ᶠ r in 𝓝[<] rs, r ∈ Ioo 0 rs := Ioo_mem_nhdsLT hrs.1
  filter_upwards [hev, hnear] with r hr hrI _
  obtain ⟨a, ha⟩ := herglotz_posDef F U hU hDU hF hinj hk hrs φ hφH hrI C hr
  refine ⟨a, fun c hc => ?_⟩
  have h1 := ha c hc
  rw [herglotz_qform_eq F U hU hDU hF k ⟨hrI.1.le, hrI.2.le.trans hrs.2⟩ C a c] at h1
  linarith

end

section

/-! ## Dirichlet poles and eigenphases -/

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory Set Real Metric Complex Filter Topology

/-- Cauchy–Schwarz on an interval: `(∫₀ᵇ g)² ≤ b ∫₀ᵇ g²` for continuous `g`. -/
lemma sq_intervalIntegral_le {g : ℝ → ℝ} {b : ℝ} (hb : 0 < b) (hg : Continuous g) :
    (∫ t in (0 : ℝ)..b, g t) ^ 2 ≤ b * ∫ t in (0 : ℝ)..b, g t ^ 2 := by
  set A := ∫ t in (0 : ℝ)..b, g t
  set B := ∫ t in (0 : ℝ)..b, g t ^ 2
  have hnn : 0 ≤ ∫ t in (0 : ℝ)..b, (g t - A / b) ^ 2 :=
    intervalIntegral.integral_nonneg hb.le (fun _ _ => sq_nonneg _)
  have hfun : (fun t => (g t - A / b) ^ 2) =
      fun t => (g t ^ 2 - (2 * (A / b)) * g t) + (A / b) ^ 2 := by
    funext t; ring
  have hi1 : IntervalIntegrable (fun t => g t ^ 2) volume 0 b :=
    (hg.pow 2).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun t => (2 * (A / b)) * g t) volume 0 b :=
    (continuous_const.mul hg).intervalIntegrable _ _
  have hexp : ∫ t in (0 : ℝ)..b, (g t - A / b) ^ 2 = B - 2 * (A / b) * A + (A / b) ^ 2 * b := by
    rw [hfun, intervalIntegral.integral_add (hi1.sub hi2) intervalIntegrable_const,
      intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  rw [hexp] at hnn
  have h2 : B - 2 * (A / b) * A + (A / b) ^ 2 * b = B - A ^ 2 / b := by
    field_simp; ring
  rw [h2, sub_nonneg, div_le_iff₀ hb] at hnn
  linarith

/-- If a Herglotz wave `u = u_a` satisfies the
pole inequality with constant `(D + 2) K`, `K = k²/4 · M² · 2π` (`M` a bound for `|γ_r'|`), then
its value `v` at `γ_r(0)` satisfies `D ‖v - V v‖² < 2 Im ⟪v, V v⟫` for the holonomy
`V = V_{r,k}`. -/
lemma herglotz_key_ineq (F : ℂ → ℂ) {U : Set ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    {k r M D : ℝ} (hcirc : ∀ θ : ℝ, (r : ℂ) * exp (θ * I) ∈ U)
    (hdAng : ∀ θ : ℝ, ‖dAng F r θ‖ ≤ M) (hD : 0 < D) (A : CircFun)
    (hpole : (D + 2) * (k ^ 2 / 4 * M ^ 2 * (2 * π)) * ∫ θ in (0 : ℝ)..(2 * π),
            ‖herglotzWave k A (F (r * exp (θ * I)))‖ ^ 2 <
          -(∫ θ in (0 : ℝ)..(2 * π),
            conj (herglotzWave k A (F (r * exp (θ * I)))) *
              (fderiv ℝ (herglotzWave k A) (F (r * exp (θ * I))) (-I * dAng F r θ) -
                I * fderiv ℝ (herglotzWave k A) (F (r * exp (θ * I))) (dAng F r θ))).re) :
    D * ‖herglotzVec k A (F (r * exp ((0 : ℝ) * I))) -
        holV F k r (herglotzVec k A (F (r * exp ((0 : ℝ) * I))))‖ ^ 2 <
      2 * (⟪herglotzVec k A (F (r * exp ((0 : ℝ) * I))),
        holV F k r (herglotzVec k A (F (r * exp ((0 : ℝ) * I))))⟫_ℂ).im := by
  obtain ⟨hb1, hb2⟩ := herglotz_holonomy_bound F k hU hF hcirc A
  set P := -(∫ θ in (0 : ℝ)..(2 * π),
            conj (herglotzWave k A (F (r * exp (θ * I)))) *
              (fderiv ℝ (herglotzWave k A) (F (r * exp (θ * I))) (-I * dAng F r θ) -
                I * fderiv ℝ (herglotzWave k A) (F (r * exp (θ * I))) (dAng F r θ))).re with hP
  set v := herglotzVec k A (F (r * exp ((0 : ℝ) * I))) with hv
  set Λ := ∫ θ in (0 : ℝ)..(2 * π), |k| / 2 * ‖dAng F r θ‖ *
      ‖herglotzWave k A (F (r * exp (θ * I)))‖ with hΛdef
  set I2 := ∫ θ in (0 : ℝ)..(2 * π), ‖herglotzWave k A (F (r * exp (θ * I)))‖ ^ 2 with hI2
  set K := k ^ 2 / 4 * M ^ 2 * (2 * π) with hK
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hdAng 0)
  have hhc : Continuous fun θ : ℝ => herglotzWave k A (F (r * exp (θ * I))) := by
    have hγc : Continuous fun θ : ℝ => F (r * exp (θ * I)) :=
      continuous_iff_continuousAt.2 fun θ =>
        (hasDerivAt_circleCurve F hU hF (hcirc θ)).continuousAt
    exact continuous_iff_continuousAt.2 fun θ =>
      ((hasFDerivAt_herglotzWave k A _).continuousAt).comp hγc.continuousAt
  have hdc : Continuous (dAng F r) := by
    have hdF : ContinuousOn (deriv F) U := (hF.deriv hU).continuousOn
    have hc' : Continuous fun θ : ℝ => (r : ℂ) * exp (θ * I) := by fun_prop
    unfold dAng
    exact (continuous_const.mul (by fun_prop)).mul (hdF.comp_continuous hc' hcirc)
  have hΛ0 : 0 ≤ Λ := intervalIntegral.integral_nonneg (by positivity) fun θ _ => by positivity
  have hΛle : Λ ≤ |k| / 2 * M *
      ∫ θ in (0 : ℝ)..(2 * π), ‖herglotzWave k A (F (r * exp (θ * I)))‖ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by positivity)
      ((((continuous_const.mul hdc.norm)).mul hhc.norm).intervalIntegrable _ _)
      ((continuous_const.mul hhc.norm).intervalIntegrable _ _) fun θ _ => ?_
    have := hdAng θ
    gcongr
  have hCS := sq_intervalIntegral_le (by positivity : (0 : ℝ) < 2 * π) hhc.norm
  have hΛsq : Λ ^ 2 ≤ K * I2 := by
    have h1 : Λ ^ 2 ≤ (|k| / 2 * M) ^ 2 *
        (∫ θ in (0 : ℝ)..(2 * π), ‖herglotzWave k A (F (r * exp (θ * I)))‖) ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hΛ0 hΛle 2
    have h2 : (|k| / 2 * M) ^ 2 = k ^ 2 / 4 * M ^ 2 := by
      rw [mul_pow, div_pow, sq_abs]; ring
    rw [h2] at h1
    calc Λ ^ 2 ≤ k ^ 2 / 4 * M ^ 2 *
          (∫ θ in (0 : ℝ)..(2 * π), ‖herglotzWave k A (F (r * exp (θ * I)))‖) ^ 2 := h1
      _ ≤ k ^ 2 / 4 * M ^ 2 * (2 * π * I2) := by gcongr
      _ = K * I2 := by rw [hK]; ring
  have hnv : ‖v - holV F k r v‖ ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb1 2
  have e1 : (D + 2) * Λ ^ 2 ≤ (D + 2) * (K * I2) :=
    mul_le_mul_of_nonneg_left hΛsq (by linarith)
  have e2 : D * ‖v - holV F k r v‖ ^ 2 ≤ D * Λ ^ 2 := mul_le_mul_of_nonneg_left hnv hD.le
  have e3 : (D + 2) * K * I2 = (D + 2) * (K * I2) := by ring
  linarith

/-- If `U = R* V* R` with `R`, `V` unitary and `U - 1`
compact, and vectors `w_1, …, w_m` satisfy `-cot(α/2) ‖z - V z‖² < 2 Im ⟪z, V z⟫` for every
nonzero combination `z`, then `U` has `m` orthonormal eigenvectors with phases in `(α, 2π)`. -/
lemma arc_eigen_of_conj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {R V : E →L[ℂ] E} (hR : R ∈ unitary (E →L[ℂ] E))
    (hV : V ∈ unitary (E →L[ℂ] E))
    (hC : IsCompactOperator ((star R * star V * R - 1 : E →L[ℂ] E) : E → E)) {α : ℝ}
    (hα : α ∈ Ioo 0 (2 * π)) {m : ℕ} (w : Fin m → E)
    (hkey : ∀ cc : Fin m → ℂ, cc ≠ 0 →
      -Real.cot (α / 2) * ‖(∑ i, cc i • w i) - V (∑ i, cc i • w i)‖ ^ 2 <
        2 * (⟪∑ i, cc i • w i, V (∑ i, cc i • w i)⟫_ℂ).im) :
    ∃ (u : Fin m → E) (θ : Fin m → ℝ), Orthonormal ℂ u ∧
      (∀ i, θ i ∈ Ioo α (2 * π)) ∧ ∀ i, (star R * star V * R) (u i) = exp (θ i * I) • u i := by
  classical
  have hUu : star R * star V * R ∈ unitary (E →L[ℂ] E) :=
    Submonoid.mul_mem _ (Submonoid.mul_mem _ (Unitary.star_mem hR) (Unitary.star_mem hV)) hR
  have hRR : ∀ x, R (star R x) = x := fun x => by
    rw [← ContinuousLinearMap.mul_apply, Unitary.mul_star_self_of_mem hR,
      ContinuousLinearMap.one_apply]
  let y : Fin m → E := fun i => star R (w i)
  have hysum : ∀ cc : Fin m → ℂ, ∑ i, cc i • y i = star R (∑ i, cc i • w i) := fun cc => by
    simp only [y, map_sum, map_smul]
  have hli : LinearIndependent ℂ y := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    by_contra hne
    push_neg at hne
    have hg0 : g ≠ 0 := fun h => by
      obtain ⟨i, hi⟩ := hne
      exact hi (by rw [h]; rfl)
    have h0 : ∑ i, g i • w i = 0 := by
      rw [← hRR (∑ i, g i • w i), ← hysum, hg, map_zero]
    have := hkey g hg0
    rw [h0] at this
    simp at this
  let Y := Submodule.span ℂ (Set.range y)
  haveI : FiniteDimensional ℂ Y := FiniteDimensional.span_of_finite ℂ (Set.finite_range y)
  have hYm : Module.finrank ℂ Y = m := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  refine exists_arc_eigenvectors hUu hC hα Y hYm ?_
  intro x hx hx0
  obtain ⟨cc, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hx
  have hcc : cc ≠ 0 := fun h => hx0 (by simp [h])
  have hk' := hkey cc hcc
  rw [hysum]
  generalize ∑ i, cc i • w i = z at hk' ⊢
  simp only [ContinuousLinearMap.mul_apply, hRR]
  have h1 : ⟪star R z, star R (star V z)⟫_ℂ = conj ⟪z, V z⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      star_star, hRR, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]
  have h2 : ‖star R z - star R (star V z)‖ = ‖z - V z‖ := by
    rw [← map_sub, norm_apply_eq_of_mem_unitary (Unitary.star_mem hR),
      ← norm_apply_eq_of_mem_unitary hV, map_sub, ← ContinuousLinearMap.mul_apply,
      Unitary.mul_star_self_of_mem hV, ContinuousLinearMap.one_apply, norm_sub_rev]
  rw [h1, h2, Complex.conj_im]
  linarith

/-- Suppose `k² = λ_j(F(r_*𝔻))` for every index `j` in a finite set
`J` of indices `≥ 1` (so `#J` is at most the multiplicity of `k²`). For every `π < α < 2π`
and every nonresonant radius `r < r_*` sufficiently close to `r_*`, the unitary `U_{r,k}` has
`#J` orthonormal eigenvectors with eigenvalues `e^{iθ}`, `θ ∈ (α, 2π)`. -/
theorem eigenphases_near_resonance (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hDU : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    {k : ℝ} (hk : 0 < k) {rs : ℝ} (hrs : rs ∈ Ioc (0 : ℝ) 1) (J : Finset ℕ)
    (hJ : ∀ j ∈ J, 1 ≤ j ∧ dirichletEigenvalue (F '' ball 0 rs) j = ENNReal.ofReal (k ^ 2))
    {α : ℝ} (hα : α ∈ Ioo π (2 * π)) :
    ∀ᶠ r in 𝓝[<] rs,
      (∀ j : ℕ, 1 ≤ j → dirichletEigenvalue (F '' ball 0 r) j ≠ ENNReal.ofReal (k ^ 2)) →
      ∃ (u : Fin J.card → L2N) (θ : Fin J.card → ℝ), Orthonormal ℂ u ∧
        (∀ i, θ i ∈ Ioo α (2 * π)) ∧ ∀ i, holU F k r (u i) = exp (θ i * I) • u i := by
  classical
  -- a uniform bound for `|γ_r'|`
  obtain ⟨M, hM⟩ : ∃ M, ∀ z ∈ closedBall (0 : ℂ) 1, ‖deriv F z‖ ≤ M :=
    (isCompact_closedBall 0 1).exists_bound_of_continuousOn
      ((hF.deriv hU).continuousOn.mono hDU)
  have hdAng : ∀ r ∈ Icc (0 : ℝ) 1, ∀ θ : ℝ, ‖dAng F r θ‖ ≤ max M 0 := by
    intro r hr θ
    have hz : (r : ℂ) * exp (θ * I) ∈ closedBall (0 : ℂ) 1 := by
      simp [Complex.norm_exp_ofReal_mul_I, abs_of_nonneg hr.1, hr.2]
    simp only [dAng, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp_ofReal_mul_I, one_mul, mul_one, abs_of_nonneg hr.1]
    calc r * ‖deriv F (r * exp (θ * I))‖ ≤ 1 * max M 0 :=
          mul_le_mul hr.2 ((hM _ hz).trans (le_max_left _ _)) (norm_nonneg _) zero_le_one
      _ = max M 0 := one_mul _
  -- the constants
  have hα2 : α / 2 ∈ Ioo (π / 2) π :=
    ⟨by linarith [hα.1, hα.2, pi_pos], by linarith [hα.1, hα.2, pi_pos]⟩
  have hc : Real.cot (α / 2) < 0 := by
    rw [Real.cot_eq_cos_div_sin]
    exact div_neg_of_neg_of_pos (Real.cos_neg_of_pi_div_two_lt_of_lt hα2.1 (by linarith [hα2.2, pi_pos]))
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hα2.1, pi_pos]) hα2.2)
  have hD0 : 0 < -Real.cot (α / 2) := by linarith
  have hcore := herglotz_dirichlet_pole F U hU hDU hF hinj hk hrs J hJ
    ((-Real.cot (α / 2) + 2) * (k ^ 2 / 4 * (max M 0) ^ 2 * (2 * π)))
  have hnear : ∀ᶠ r in 𝓝[<] rs, r ∈ Ioo (rs / 2) rs := Ioo_mem_nhdsLT (by linarith [hrs.1])
  filter_upwards [hcore, hnear] with r hr hrI hnonres
  obtain ⟨a, ha⟩ := hr hnonres
  have hr0 : 0 < r := by linarith [hrI.1, hrs.1]
  have hr1 : r < 1 := lt_of_lt_of_le hrI.2 hrs.2
  have hcirc : ∀ θ : ℝ, (r : ℂ) * exp (θ * I) ∈ U := fun θ => hDU (by
    simp [Complex.norm_exp_ofReal_mul_I, abs_of_pos hr0, hr1.le])
  have hseg : ∀ s ∈ Ico (0 : ℝ) 1, (s : ℂ) ∈ U := fun s hs => hDU (by
    simp [abs_of_nonneg hs.1, hs.2.le])
  obtain ⟨hVu, -, -⟩ := holU_mem_unitary k hU hF hseg ⟨hr0.le, hr1⟩ hcirc
  have hRu := holR_mem_unitary k hU hF hseg ⟨hr0.le, hr1⟩
  have hUeq : holU F k r = star (holR F k r) * star (holV F k r) * holR F k r := by
    rw [holU, holH, star_mul, star_mul, star_star, mul_assoc]
  have hG : DifferentiableOn ℂ F (ball 0 1) := hF.mono (ball_subset_closedBall.trans hDU)
  have hinj' : InjOn F (ball 0 1) := hinj.mono (ball_subset_closedBall.trans hDU)
  have hC := (holonomy_path k hG hinj' hk hr0 hr1).1.isCompactOperator ⟨hr0.le, le_rfl⟩
  rw [hUeq] at hC ⊢
  refine arc_eigen_of_conj hRu hVu hC ⟨by linarith [hα.1, pi_pos], hα.2⟩
    (fun i => herglotzVec k (a i) (F (r * exp ((0 : ℝ) * I)))) ?_
  intro cc hcc
  rw [← herglotzVec_sum k a cc]
  exact herglotz_key_ineq F hU hF hcirc (hdAng r ⟨hr0.le, hr1.le⟩) hD0 _ (ha cc hcc)

end

section

/-! ## Divergence of Dirichlet eigenvalues at radius zero -/

open MeasureTheory Set Metric Filter Topology

/-- `λ_j(Ω) ≥ 1/(4ρ²)` for `Ω ⊆ closedBall c ρ` and `j ≥ 1`. -/
theorem dirichletEigenvalue_ge_of_subset_closedBall (Ω : Set ℂ) (c : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) (hΩ : Ω ⊆ closedBall c ρ) {j : ℕ} (hj : 1 ≤ j) :
    ENNReal.ofReal (1 / (4 * ρ ^ 2)) ≤ dirichletEigenvalue Ω j := by
  refine le_trans ?_ (dirichletEigenvalue_mono Ω hj)
  have hP := poincare_inequality_closedBall Ω c hΩ
  set C : ENNReal := ENNReal.ofReal (4 * ρ ^ 2) with hC
  have hC0 : C ≠ 0 := by
    rw [hC]; exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hCt : C ≠ ⊤ := ENNReal.ofReal_ne_top
  have hCinv : ENNReal.ofReal (1 / (4 * ρ ^ 2)) = C⁻¹ := by
    rw [hC, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one, one_div]
  rw [hCinv]
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
  calc C⁻¹ * l2NormSq u ≤ C⁻¹ * (C * dirichletEnergy u) := by
        gcongr; exact hP u htest
    _ = dirichletEnergy u := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hC0 hCt, one_mul]

/-- If `F` is complex differentiable at `0`, then
`λ_j(F(r𝔻)) → ∞` as `r ↓ 0`, for every `j ≥ 1`. -/
theorem tendsto_dirichletEigenvalue_image_ball {F : ℂ → ℂ} (hF : DifferentiableAt ℂ F 0)
    {j : ℕ} (hj : 1 ≤ j) :
    Tendsto (fun r : ℝ => dirichletEigenvalue (F '' ball 0 r) j) (𝓝[>] 0) (𝓝 ⊤) := by
  obtain ⟨C₀, hC₀⟩ := (hF.isBigO_sub).bound
  set C : ℝ := max C₀ 1 with hCdef
  have hC : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hC₀
  -- `F(r𝔻) ⊆ closedBall (F 0) (C r)` for `0 < r < δ`
  have hsub : ∀ r, 0 < r → r < δ → F '' ball 0 r ⊆ closedBall (F 0) (C * r) := by
    rintro r hr hrδ _ ⟨z, hz, rfl⟩
    have hz' : dist z 0 < δ := lt_of_lt_of_le hz hrδ.le
    have h1 := hball hz'
    rw [sub_zero] at h1
    rw [mem_closedBall, dist_eq_norm]
    rw [mem_ball, dist_zero_right] at hz
    calc ‖F z - F 0‖ ≤ C₀ * ‖z‖ := h1
      _ ≤ C * ‖z‖ := by gcongr; exact le_max_left _ _
      _ ≤ C * r := by gcongr
  rw [ENNReal.tendsto_nhds_top_iff_nat]
  intro n
  have hε : (0 : ℝ) < 1 / (4 * C ^ 2 * (n + 1)) := by positivity
  have h1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < δ :=
    nhdsWithin_le_nhds (eventually_lt_nhds hδ)
  have h2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ^ 2 < 1 / (4 * C ^ 2 * (n + 1)) := by
    have : Tendsto (fun r : ℝ => r ^ 2) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_pow 2).tendsto (0 : ℝ)
    exact nhdsWithin_le_nhds (this.eventually (eventually_lt_nhds hε))
  filter_upwards [h1, h2, self_mem_nhdsWithin] with r hrδ hr2 hr0
  have hr0' : (0 : ℝ) < r := hr0
  have hlow := dirichletEigenvalue_ge_of_subset_closedBall (F '' ball 0 r) (F 0)
    (mul_pos hC hr0') (hsub r hr0' hrδ) hj
  refine lt_of_lt_of_le ?_ hlow
  have hn : ((n : ℕ) : ENNReal) = ENNReal.ofReal n := by simp
  rw [hn, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  have hpos : 0 < 4 * (C * r) ^ 2 := by positivity
  rw [lt_div_iff₀ hpos]
  have : 4 * C ^ 2 * (n + 1) * r ^ 2 < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hr2
    linarith
  nlinarith [sq_nonneg (C * r)]

end

section

/-! ## From resonances to crossings -/

open scoped InnerProductSpace
open MeasureTheory Set Real Metric Complex Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A lower bound on a crossing count is realized by a finite set of crossing times. -/
lemma exists_finset_of_le_crossingCount {U : ℝ → E →L[ℂ] E} {α : ℝ} {I : Set ℝ} {n : ℕ}
    (h : (n : ℕ∞) ≤ crossingCount U α I) :
    ∃ s : Finset ℝ, ↑s ⊆ I ∧ (n : ℕ∞) ≤ ∑ t ∈ s, crossingMult U α t := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨∅, by simp, by simp⟩
  have hlt : ((n - 1 : ℕ) : ℕ∞) < crossingCount U α I :=
    lt_of_lt_of_le (by exact_mod_cast Nat.sub_lt hn one_pos) h
  unfold crossingCount at hlt
  obtain ⟨s, hs⟩ := lt_iSup_iff.1 hlt
  obtain ⟨hsI, hs'⟩ := lt_iSup_iff.1 hs
  refine ⟨s, hsI, ?_⟩
  have h1 := Order.add_one_le_of_lt hs'
  have e : ((n - 1 : ℕ) : ℕ∞) + 1 = n := by
    rw [← Nat.cast_one (R := ℕ∞), ← Nat.cast_add, Nat.sub_add_cancel hn]
  rwa [e] at h1

/-- The crossing times of the holonomy path in `(0, 1)` form a countable set. -/
lemma countable_crossing_times_holU {F : ℂ → ℂ} (hG : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) {k : ℝ} (hk : 0 < k) {α : ℝ} (hα0 : 0 < α)
    (hα : α < 2 * Real.pi) :
    {t ∈ Ioo 0 1 | ∃ x : L2N, x ≠ 0 ∧ holU F k t x = exp (α * I) • x}.Countable := by
  have hsub : {t ∈ Ioo 0 1 | ∃ x : L2N, x ≠ 0 ∧ holU F k t x = exp (α * I) • x} ⊆
      ⋃ n : ℕ, {t ∈ Ioo 0 (1 - 1 / ((n : ℝ) + 2)) |
        ∃ x : L2N, x ≠ 0 ∧ holU F k t x = exp (α * I) • x} := by
    rintro t ⟨⟨h0, h1⟩, hx⟩
    have hr : 0 < 1 - t := by linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (1 - t))
    refine mem_iUnion.2 ⟨n, ⟨h0, ?_⟩, hx⟩
    have : 1 / ((n : ℝ) + 2) < 1 - t := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hr] at hn
      nlinarith
    linarith
  refine Set.Countable.mono hsub (Set.countable_iUnion fun n => ?_)
  have hb0 : (0 : ℝ) < 1 - 1 / ((n : ℝ) + 2) := by
    have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := by
      gcongr; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    linarith
  have hb1 : 1 - 1 / ((n : ℝ) + 2) < 1 := by
    have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    linarith
  exact (finite_crossing_times (holonomy_path k hG hinj hk hb0 hb1).1 hα0 hα).countable

/-- If `λ_j(F(𝔻)) ≤ k²`, then
`λ_j(F(r𝔻)) = k²` for some `r ∈ (0, 1]`. -/
lemma exists_resonance_radius (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hDU : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    {k : ℝ} {j : ℕ} (hj : 1 ≤ j)
    (hlam : dirichletEigenvalue (F '' ball 0 1) j ≤ ENNReal.ofReal (k ^ 2)) :
    ∃ r ∈ Ioc (0 : ℝ) 1, dirichletEigenvalue (F '' ball 0 r) j = ENNReal.ofReal (k ^ 2) := by
  have h0U : (0 : ℂ) ∈ U := hDU (mem_closedBall_self zero_le_one)
  have hF0 : DifferentiableAt ℂ F 0 := hF.differentiableAt (hU.mem_nhds h0U)
  have ht := tendsto_dirichletEigenvalue_image_ball hF0 hj
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (k ^ 2) < dirichletEigenvalue (F '' ball 0 r) j ∧ r < 1 :=
    (ht.eventually (lt_mem_nhds ENNReal.ofReal_lt_top)).and
      (nhdsWithin_le_nhds (eventually_lt_nhds one_pos))
  obtain ⟨r₀, ⟨hr₀v, hr₀1⟩, hr₀0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hcont : ContinuousOn (fun r : ℝ => dirichletEigenvalue (F '' ball 0 r) j) (Icc r₀ 1) :=
    (dirichletEigenvalue_image_ball_continuousOn F U hU hDU hF hinj j).mono
      (Icc_subset_Ioc_iff hr₀1.le |>.2 ⟨hr₀0, le_rfl⟩)
  obtain ⟨r, hr, hrv⟩ := intermediate_value_Icc' hr₀1.le hcont ⟨hlam, hr₀v.le⟩
  exact ⟨r, ⟨lt_of_lt_of_le (show (0 : ℝ) < r₀ from hr₀0) hr.1, hr.2⟩, hrv⟩

/-- The resonant radii form a countable set. -/
lemma countable_resonant_radii (F : ℂ → ℂ) (U : Set ℂ)
    (hDU : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    (k : ℝ) :
    {r ∈ Ioc (0 : ℝ) 1 | ∃ j : ℕ, 1 ≤ j ∧
      dirichletEigenvalue (F '' ball 0 r) j = ENNReal.ofReal (k ^ 2)}.Countable := by
  have hsub : {r ∈ Ioc (0 : ℝ) 1 | ∃ j : ℕ, 1 ≤ j ∧
      dirichletEigenvalue (F '' ball 0 r) j = ENNReal.ofReal (k ^ 2)} ⊆
      ⋃ j : ℕ, {r ∈ Ioc (0 : ℝ) 1 | 1 ≤ j ∧
        dirichletEigenvalue (F '' ball 0 r) j = ENNReal.ofReal (k ^ 2)} := by
    rintro r ⟨hr, j, hj, hv⟩
    exact mem_iUnion.2 ⟨j, hr, hj, hv⟩
  refine Set.Countable.mono hsub (Set.countable_iUnion fun j => ?_)
  refine Set.Subsingleton.countable ?_
  rintro r ⟨hr, hj, hv⟩ r' ⟨hr', -, hv'⟩
  exact (dirichletEigenvalue_image_ball_strictAntiOn F U hDU hF hinj hj).injOn hr hr'
    (hv.trans hv'.symm)

/-- **From resonances to crossings.** Let `F` be holomorphic and
injective on a neighbourhood of the closed unit disk, `k > 0` and `m` with
`λ_m(F(𝔻)) ≤ k²`. Then there is `α₀ < 2π` such that for every
`α ∈ (α₀, 2π)` the path `r ↦ U_{r,k}` has at least `m` crossings of `e^{iα}` in `(0, 1)`,
counted with multiplicity. -/
theorem crossings_of_resonances (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hDU : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    {k : ℝ} (hk : 0 < k) {m : ℕ}
    (hlam : dirichletEigenvalue (F '' ball 0 1) m ≤ ENNReal.ofReal (k ^ 2)) :
    ∃ α₀ < 2 * π, ∀ α ∈ Ioo α₀ (2 * π),
      (m : ℕ∞) ≤ crossingCount (holU F k) α (Ioo 0 1) := by
  classical
  have hball : ball (0 : ℂ) 1 ⊆ U := ball_subset_closedBall.trans hDU
  have hG := hF.mono hball
  have hinj' := hinj.mono hball
  set c := ENNReal.ofReal (k ^ 2) with hcdef
  -- the resonance radii of the first `m` eigenvalues
  have hρ : ∀ j ∈ Finset.Icc 1 m, ∃ r ∈ Ioc (0 : ℝ) 1,
      dirichletEigenvalue (F '' ball 0 r) j = c := by
    intro j hj
    obtain ⟨hj1, hjm⟩ := Finset.mem_Icc.1 hj
    exact exists_resonance_radius F U hU hDU hF hinj hj1
      ((dirichletEigenvalue_mono _ hjm).trans hlam)
  choose! ρ hρmem hρv using hρ
  set R := (Finset.Icc 1 m).image ρ with hR
  set J : ℝ → Finset ℕ := fun r => (Finset.Icc 1 m).filter (fun j => ρ j = r) with hJ
  have hsum : m = ∑ r ∈ R, (J r).card := by
    have := Finset.card_eq_sum_card_image ρ (Finset.Icc 1 m)
    simpa using this
  have hRmem : ∀ r ∈ R, r ∈ Ioc (0 : ℝ) 1 := by
    intro r hr
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hr
    exact hρmem j hj
  -- the previous resonant radius
  set p : ℝ → ℝ := fun r =>
    (insert 0 (R.filter (· < r))).max' (Finset.insert_nonempty _ _) with hp
  have hp_lt : ∀ r ∈ R, p r < r := by
    intro r hr
    rw [hp, Finset.max'_lt_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact (hRmem r hr).1
    · exact (Finset.mem_filter.1 hy).2
  have hp_ge : ∀ r ∈ R, ∀ r' ∈ R, r < r' → r ≤ p r' := by
    intro r hr r' hr' hlt
    exact Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hr, hlt⟩))
  have hp_nonneg : ∀ r, 0 ≤ p r := fun r => Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  -- resonant radii
  set Sres := {r ∈ Ioc (0 : ℝ) 1 | ∃ j : ℕ, 1 ≤ j ∧
    dirichletEigenvalue (F '' ball 0 r) j = c} with hSresdef
  have hSres : Sres.Countable := countable_resonant_radii F U hDU hF hinj k
  -- nonresonant radii `a_r` between consecutive resonant radii
  have ha : ∀ r ∈ R, ∃ a ∈ Ioo (p r) r, a ∉ Sres := fun r hr =>
    exists_mem_Ioo_not_mem_of_countable hSres (hp_lt r hr)
  choose! a ha_mem ha_res using ha
  have ha0 : ∀ r ∈ R, 0 < a r := fun r hr => lt_of_le_of_lt (hp_nonneg r) (ha_mem r hr).1
  -- gaps below `2π` at the radii `a_r`
  have hgap : ∀ r ∈ R, ∃ α₁ < 2 * π, ∀ θ ∈ Ioo α₁ (2 * π), ∀ x : L2N,
      holU F k (a r) x = exp (θ * I) • x → x = 0 := by
    intro r hr
    have ha1 : a r < 1 := lt_of_lt_of_le (ha_mem r hr).2 (hRmem r hr).2
    exact exists_eigen_gap_below_two_pi (holonomy_path k hG hinj' hk (ha0 r hr) ha1).1
      ⟨(ha0 r hr).le, le_rfl⟩
  choose! α₁ hα₁ hα₁gap using hgap
  refine ⟨(insert π (R.image α₁)).max' (Finset.insert_nonempty _ _), ?_, ?_⟩
  · rw [Finset.max'_lt_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · linarith [pi_pos]
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hy
      exact hα₁ r hr
  intro α hα
  have hπα : π < α := lt_of_le_of_lt (Finset.le_max' _ _ (Finset.mem_insert_self _ _)) hα.1
  have hα₁α : ∀ r ∈ R, α₁ r < α := fun r hr =>
    lt_of_le_of_lt (Finset.le_max' _ _
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hr))) hα.1
  have hα0 : 0 < α := by linarith [pi_pos]
  set Scr := {t ∈ Ioo 0 1 | ∃ x : L2N, x ≠ 0 ∧ holU F k t x = exp (α * I) • x} with hScrdef
  have hScr : Scr.Countable := countable_crossing_times_holU hG hinj' hk hα0 hα.2
  -- crossings in `(a_r, r)` for each resonant radius `r`
  have hloc : ∀ r ∈ R, ∃ s : Finset ℝ, ↑s ⊆ Ioo (a r) r ∧
      ((J r).card : ℕ∞) ≤ ∑ t ∈ s, crossingMult (holU F k) α t := by
    intro r hr
    have hJr : ∀ j ∈ J r, 1 ≤ j ∧ dirichletEigenvalue (F '' ball 0 r) j = c := by
      intro j hj
      obtain ⟨hjI, hjr⟩ := Finset.mem_filter.1 hj
      exact ⟨(Finset.mem_Icc.1 hjI).1, hjr ▸ hρv j hjI⟩
    have hnear := eigenphases_near_resonance F U hU hDU hF hinj hk (hRmem r hr) (J r) hJr
      ⟨hπα, hα.2⟩
    obtain ⟨l, hl, hlsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hnear
    obtain ⟨b₁, hb₁, hb₁S⟩ := exists_mem_Ioo_not_mem_of_countable (hSres.union hScr)
      (max_lt (ha_mem r hr).2 hl : max (a r) l < r)
    have hb₁a : a r < b₁ := lt_of_le_of_lt (le_max_left _ _) hb₁.1
    have hb₁l : l < b₁ := lt_of_le_of_lt (le_max_right _ _) hb₁.1
    have hb₁1 : b₁ < 1 := lt_of_lt_of_le hb₁.2 (hRmem r hr).2
    have hnonres : ∀ j : ℕ, 1 ≤ j → dirichletEigenvalue (F '' ball 0 b₁) j ≠ c := by
      intro j hj hjv
      exact hb₁S (Or.inl ⟨⟨(ha0 r hr).trans hb₁a, hb₁1.le⟩, j, hj, hjv⟩)
    obtain ⟨u, θ, hu, hθ, heig⟩ := hlsub ⟨hb₁l, hb₁.2⟩ hnonres
    have hpath := (holonomy_path k hG hinj' hk ((ha0 r hr).trans hb₁a) hb₁1).1
    have hcr := crossings_of_arc hpath (ha0 r hr) hb₁a le_rfl hα0 hα.2
      (fun θ' hθ' x hx => hα₁gap r hr θ' ⟨lt_of_lt_of_le (hα₁α r hr) hθ'.1, hθ'.2⟩ x hx)
      (fun x hx => by
        by_contra hx0
        exact hb₁S (Or.inr ⟨⟨(ha0 r hr).trans hb₁a, hb₁1⟩, x, hx0, hx⟩))
      u hu θ hθ heig
    obtain ⟨s, hs, hsc⟩ := exists_finset_of_le_crossingCount hcr
    exact ⟨s, hs.trans (Ioo_subset_Ioo_right hb₁.2.le), hsc⟩
  choose! s hs hsc using hloc
  have hdisj : (R : Set ℝ).PairwiseDisjoint s := by
    intro r hr r' hr' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro t ht ht'
    have h1 := hs r hr ht
    have h2 := hs r' hr' ht'
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hp_ge r hr r' hr' hlt
      have := (ha_mem r' hr').1
      linarith [h1.2, h2.1]
    · have := hp_ge r' hr' r hr hlt
      have := (ha_mem r hr).1
      linarith [h1.1, h2.2]
  have hsub : ↑(R.biUnion s) ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    rw [Finset.coe_biUnion] at ht
    simp only [Set.mem_iUnion, Finset.mem_coe] at ht
    obtain ⟨r, hr, htr⟩ := ht
    have h1 := hs r hr htr
    exact ⟨(ha0 r hr).trans h1.1, lt_of_lt_of_le h1.2 (hRmem r hr).2⟩
  calc (m : ℕ∞) = ∑ r ∈ R, ((J r).card : ℕ∞) := by
        conv_lhs => rw [hsum]
        push_cast; rfl
    _ ≤ ∑ r ∈ R, ∑ t ∈ s r, crossingMult (holU F k) α t := Finset.sum_le_sum hsc
    _ = ∑ t ∈ R.biUnion s, crossingMult (holU F k) α t := (Finset.sum_biUnion hdisj).symm
    _ ≤ crossingCount (holU F k) α (Ioo 0 1) := le_iSup₂_of_le (R.biUnion s) hsub le_rfl

end

section

/-! ## The partial-trace counting estimate -/

open MeasureTheory Set Real Metric

/-- **Partial-trace counting estimate.** If `λ_m(F(𝔻)) ≤ k²`, then
`2πm ≤ ∫₀¹ Φ_m(L_{r,k}) dr`. -/
theorem partial_trace_counting (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hDU : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    {k : ℝ} (hk : 0 < k) {m : ℕ} (hm : 1 ≤ m)
    (hlam : dirichletEigenvalue (F '' ball 0 1) m ≤ ENNReal.ofReal (k ^ 2)) :
    ENNReal.ofReal (2 * π * m) ≤ ∫⁻ r in Ico 0 1, kyFan m (holL F k r) := by
  obtain ⟨α₀, hα₀, hcross⟩ := crossings_of_resonances F U hU hDU hF hinj hk hlam
  have hball : ball (0 : ℂ) 1 ⊆ U := ball_subset_closedBall.trans hDU
  have hG := hF.mono hball
  have hinj' := hinj.mono hball
  have key : ∀ α ∈ Ioo (max α₀ 0) (2 * π),
      ENNReal.ofReal (α * m) ≤ ∫⁻ r in Ico 0 1, kyFan m (holL F k r) := by
    intro α hα
    have hc := hcross α ⟨(le_max_left _ _).trans_lt hα.1, hα.2⟩
    have hlt : ((m - 1 : ℕ) : ℕ∞) < crossingCount (holU F k) α (Ioo 0 1) :=
      lt_of_lt_of_le (by exact_mod_cast Nat.sub_lt hm one_pos) hc
    unfold crossingCount at hlt
    obtain ⟨s, hs⟩ := lt_iSup_iff.1 hlt
    obtain ⟨hsI, hs'⟩ := lt_iSup_iff.1 hs
    have hms : (m : ℕ∞) ≤ ∑ t ∈ s, crossingMult (holU F k) α t := by
      have h1 := Order.add_one_le_of_lt hs'
      have e : ((m - 1 : ℕ) : ℕ∞) + 1 = m := by
        rw [← Nat.cast_one (R := ℕ∞), ← Nat.cast_add, Nat.sub_add_cancel hm]
      rwa [e] at h1
    obtain ⟨b, hb0, hb1, hsb⟩ : ∃ b : ℝ, 0 < b ∧ b < 1 ∧ ↑s ⊆ Ioo 0 b := by
      by_cases hsne : s.Nonempty
      · have hM : s.max' hsne ∈ Ioo (0 : ℝ) 1 := hsI (s.max'_mem hsne)
        refine ⟨(s.max' hsne + 1) / 2, by linarith [hM.1], by linarith [hM.2],
          fun t ht => ⟨(hsI ht).1, ?_⟩⟩
        have := s.le_max' t ht
        linarith [hM.2]
      · rw [Finset.not_nonempty_iff_eq_empty] at hsne
        subst hsne
        exact ⟨1 / 2, by norm_num, by norm_num, by simp⟩
    obtain ⟨hpath, hgen, -, -⟩ := holonomy_path k hG hinj' hk hb0 hb1
    have hα0 : 0 < α := (le_max_right _ _).trans_lt hα.1
    have hcb : (m : ℕ∞) ≤ crossingCount (holU F k) α (Ioo 0 b) :=
      hms.trans (le_iSup₂_of_le s hsb le_rfl)
    calc ENNReal.ofReal (α * m)
        ≤ ∫⁻ t in Icc 0 b, kyFan m (generator (holU F k) b t) :=
          (phase_cost hpath hα0 hα.2).2 m hm hcb
      _ = ∫⁻ t in Icc 0 b, kyFan m (holL F k t) :=
          setLIntegral_congr_fun measurableSet_Icc fun t ht => by rw [hgen t ht]
      _ ≤ ∫⁻ t in Ico 0 1, kyFan m (holL F k t) :=
          lintegral_mono_set (Icc_subset_Ico_right hb1)
  by_contra hcon
  push_neg at hcon
  set X := ∫⁻ r in Ico 0 1, kyFan m (holL F k r) with hXdef
  have hX : X ≠ ⊤ := ne_top_of_lt hcon
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hy : X.toReal / m < 2 * π := by
    rw [div_lt_iff₀ hm0]
    have := (ENNReal.toReal_lt_toReal hX ENNReal.ofReal_ne_top).2 hcon
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  set a := max (max α₀ 0) (X.toReal / m) with ha_def
  have ha : a < 2 * π := max_lt (max_lt hα₀ (by positivity)) hy
  have h1 := key ((a + 2 * π) / 2)
    ⟨by linarith [le_max_left (max α₀ 0) (X.toReal / m)], by linarith⟩
  have h2 : X < ENNReal.ofReal ((a + 2 * π) / 2 * m) := by
    rw [← ENNReal.ofReal_toReal hX]
    refine (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_
    have : X.toReal / m < (a + 2 * π) / 2 := by
      linarith [le_max_right (max α₀ 0) (X.toReal / m)]
    rwa [div_lt_iff₀ hm0] at this
  exact absurd h1 (not_le.2 h2)

/-- `∫₀¹ tr L_{r,k} dr ≤ (k²/2) |G(𝔻)|`. -/
theorem lintegral_Ico_posTrace_holL_le {G : ℂ → ℂ} (k : ℝ)
    (hG : DifferentiableOn ℂ G (ball 0 1)) (hinj : InjOn G (ball 0 1)) :
    ∫⁻ r in Ico 0 1, posTrace (holL G k r) ≤
      ENNReal.ofReal (k ^ 2 / 2) * volume (G '' ball 0 1) := by
  have hU' : Ico (0 : ℝ) 1 = ⋃ n : ℕ, Icc 0 (1 - 1 / ((n : ℝ) + 2)) := by
    ext r
    simp only [mem_Ico, mem_iUnion, mem_Icc]
    constructor
    · rintro ⟨h0, h1⟩
      have hr : 0 < 1 - r := by linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / (1 - r))
      refine ⟨n, h0, ?_⟩
      have : 1 / ((n : ℝ) + 2) < 1 - r := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hr] at hn
        nlinarith
      linarith
    · rintro ⟨n, h0, h1⟩
      exact ⟨h0, by have : 0 < 1 / ((n : ℝ) + 2) := by positivity
                    linarith⟩
  rw [hU', setLIntegral_iUnion_of_directed]
  · refine iSup_le fun n => ?_
    have hb1 : 1 - 1 / ((n : ℝ) + 2) < 1 := by
      have : 0 < 1 / ((n : ℝ) + 2) := by positivity
      linarith
    rw [lintegral_posTrace_holL k hG hinj hb1]
    gcongr
  · refine Monotone.directed_le fun i j hij => Icc_subset_Icc_right ?_
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    gcongr

end

section

/-! ## Quantitative Pólya inequalities -/

open MeasureTheory Set Real Metric

/-- **Riemann mapping theorem.** Every nonempty simply connected proper open subset of `ℂ` is
the image of the unit disk under an injective holomorphic map. -/
theorem riemann_mapping (Ω : Set ℂ) (hopen : IsOpen Ω) (hsc : SimplyConnectedSpace Ω)
    (hne : Ω ≠ Set.univ) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball 0 1) ∧ Set.InjOn G (ball 0 1) ∧
      G '' ball 0 1 = Ω :=
  riemann_mapping_theorem Ω hopen hne

/-- Open mapping for an injective holomorphic map on the unit disk. -/
lemma isOpen_image_of_injOn_ball {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (ball 0 1))
    (hinj : Set.InjOn G (ball 0 1)) {s : Set ℂ} (hs : s ⊆ ball 0 1) (hso : IsOpen s) :
    IsOpen (G '' s) := by
  have han : AnalyticOnNhd ℂ G (ball 0 1) := hG.analyticOnNhd isOpen_ball
  rcases han.is_constant_or_isOpen (convex_ball (0 : ℂ) 1).isPreconnected with ⟨w, hw⟩ | h
  · exfalso
    have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
    have h1 : (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball, dist_zero_right]; norm_num
    have := hinj h0 h1 ((hw 0 h0).trans (hw _ h1).symm)
    norm_num at this
  · exact h s hs hso

/-- Let `F` be holomorphic and injective on a neighbourhood
of the closed unit disk, `Ω₁ = F(𝔻)`, `k > 0` and `m ≥ 1` with `λ_m(Ω₁) ≤ k²`
(equivalently `m ≤ N_{Ω₁}(k²)`). Then
`k² |Ω₁| ≥ 4πm + 2 ∫₀¹ τ_m(L_{r,k}) dr` and the tail integral is positive. -/
theorem quantitative_analytic (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hDU : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    {k : ℝ} (hk : 0 < k) {m : ℕ} (hm : 1 ≤ m)
    (hlam : dirichletEigenvalue (F '' ball 0 1) m ≤ ENNReal.ofReal (k ^ 2)) :
    ENNReal.ofReal (4 * π * m) + 2 * ∫⁻ r in Ico 0 1, spectralTail m (holL F k r) ≤
        ENNReal.ofReal (k ^ 2) * volume (F '' ball 0 1) ∧
      0 < ∫⁻ r in Ico 0 1, spectralTail m (holL F k r) := by
  have hballU : ball (0 : ℂ) 1 ⊆ U := ball_subset_closedBall.trans hDU
  refine ⟨?_, tail_integral_pos_aux k (hF.mono hballU) (hinj.mono hballU) hk m⟩
  have hfan := partial_trace_counting F U hU hDU hF hinj hk hm hlam
  have htr := lintegral_Ico_posTrace_holL_le k (hF.mono hballU) (hinj.mono hballU)
  have h4 : ENNReal.ofReal (4 * π * m) = 2 * ENNReal.ofReal (2 * π * m) := by
    rw [show 4 * π * m = 2 * (2 * π * m) by ring, ENNReal.ofReal_mul (by norm_num)]
    simp
  have hk2 : 2 * ENNReal.ofReal (k ^ 2 / 2) = ENNReal.ofReal (k ^ 2) := by
    rw [show k ^ 2 = 2 * (k ^ 2 / 2) by ring, ENNReal.ofReal_mul (by norm_num)]
    simp
  calc ENNReal.ofReal (4 * π * m) + 2 * ∫⁻ r in Ico 0 1, spectralTail m (holL F k r)
      = 2 * (ENNReal.ofReal (2 * π * m) + ∫⁻ r in Ico 0 1, spectralTail m (holL F k r)) := by
        rw [h4, mul_add]
    _ ≤ 2 * ((∫⁻ r in Ico 0 1, kyFan m (holL F k r)) +
          ∫⁻ r in Ico 0 1, spectralTail m (holL F k r)) := by gcongr
    _ ≤ 2 * ∫⁻ r in Ico 0 1, (kyFan m (holL F k r) + spectralTail m (holL F k r)) := by
        gcongr; exact le_lintegral_add _ _
    _ = 2 * ∫⁻ r in Ico 0 1, posTrace (holL F k r) := by
        simp_rw [kyFan_add_spectralTail]
    _ ≤ 2 * (ENNReal.ofReal (k ^ 2 / 2) * volume (F '' ball 0 1)) := by gcongr
    _ = ENNReal.ofReal (k ^ 2) * volume (F '' ball 0 1) := by rw [← mul_assoc, hk2]

end

section

/-! ## Conformal exhaustion: reduction to analytic boundaries -/

open MeasureTheory Real Metric

/-- The rescaled disks `s • 𝔻`, `0 < s < 1`. -/
lemma image_mul_ball_subset {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    (fun z : ℂ => (s : ℂ) * z) '' ball 0 1 ⊆ ball 0 1 := by
  rintro _ ⟨w, hw, rfl⟩
  rw [mem_ball, dist_zero_right] at hw ⊢
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
  nlinarith [norm_nonneg w]

lemma image_mul_ball_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (fun z : ℂ => (a : ℂ) * z) '' ball 0 1 ⊆ (fun z : ℂ => (b : ℂ) * z) '' ball 0 1 := by
  rintro _ ⟨w, hw, rfl⟩
  have hb : 0 < b := ha.trans_le hab
  refine ⟨((a / b : ℝ) : ℂ) * w, ?_, ?_⟩
  · rw [mem_ball, dist_zero_right] at hw ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos ha hb)]
    calc a / b * ‖w‖ ≤ 1 * ‖w‖ := by gcongr; exact div_le_one_of_le₀ hab hb.le
      _ < 1 := by linarith
  · have : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    simp only
    push_cast
    field_simp

/-- The rescaled maps `G_s(z) = G(s z)`, `0 < s < 1`, are holomorphic and injective on a
neighbourhood `ball 0 (1/s)` of the closed unit disk. -/
lemma scale_hyps {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (ball 0 1)) (hinj : Set.InjOn G (ball 0 1))
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    closedBall (0 : ℂ) 1 ⊆ ball 0 (1 / s) ∧
      DifferentiableOn ℂ (fun z => G ((s : ℂ) * z)) (ball 0 (1 / s)) ∧
      Set.InjOn (fun z => G ((s : ℂ) * z)) (ball 0 (1 / s)) := by
  have hmem : ∀ x ∈ ball (0 : ℂ) (1 / s), (s : ℂ) * x ∈ ball (0 : ℂ) 1 := by
    intro x hx
    rw [mem_ball, dist_zero_right] at hx ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    calc s * ‖x‖ < s * (1 / s) := by gcongr
      _ = 1 := by field_simp
  refine ⟨closedBall_subset_ball (by rw [lt_div_iff₀ hs0]; linarith), ?_, ?_⟩
  · intro z hz
    exact (hG.differentiableAt (isOpen_ball.mem_nhds (hmem z hz))).comp z
      ((differentiableAt_id.const_mul _)) |>.differentiableWithinAt
  · intro z hz w hw hzw
    have := hinj (hmem z hz) (hmem w hw) hzw
    exact mul_left_cancel₀ (by exact_mod_cast hs0.ne') this

lemma scale_image_eq (G : ℂ → ℂ) (s : ℝ) :
    (fun z => G ((s : ℂ) * z)) '' ball 0 1 = G '' ((fun z : ℂ => (s : ℂ) * z) '' ball 0 1) := by
  rw [Set.image_image]

lemma scale_image_mono (G : ℂ → ℂ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (fun z => G ((a : ℂ) * z)) '' ball 0 1 ⊆ (fun z => G ((b : ℂ) * z)) '' ball 0 1 := by
  rw [scale_image_eq, scale_image_eq]
  exact Set.image_mono (image_mul_ball_mono ha hab)

lemma scale_image_subset (G : ℂ → ℂ) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    (fun z => G ((s : ℂ) * z)) '' ball 0 1 ⊆ G '' ball 0 1 := by
  rw [scale_image_eq]
  exact Set.image_mono (image_mul_ball_subset hs0 hs1)

/-- **Conformal exhaustion**: `λ_j(G(𝔻)) = inf_{0<s<1} λ_j(G(s𝔻))`. -/
theorem dirichletEigenvalue_eq_iInf_scale {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (ball 0 1))
    (hinj : Set.InjOn G (ball 0 1)) (j : ℕ) :
    dirichletEigenvalue (G '' ball 0 1) j =
      ⨅ s : Set.Ioo (0 : ℝ) 1, dirichletEigenvalue ((fun z => G (((s : ℝ) : ℂ) * z)) '' ball 0 1) j := by
  let ι := Set.Ioo (0 : ℝ) 1
  have : Nonempty ι := ⟨⟨1 / 2, by norm_num, by norm_num⟩⟩
  let Ωs : ι → Set ℂ := fun s => (fun z => G (((s : ℝ) : ℂ) * z)) '' ball 0 1
  have hopen_s : ∀ s : ι, IsOpen (Ωs s) := by
    intro s
    simp only [Ωs]
    rw [scale_image_eq]
    refine isOpen_image_of_injOn_ball hG hinj (image_mul_ball_subset s.2.1 s.2.2) ?_
    exact (Homeomorph.mulLeft₀ ((s : ℝ) : ℂ) (by exact_mod_cast s.2.1.ne')).isOpenMap _
      isOpen_ball
  have hdir : Directed (· ⊆ ·) Ωs := by
    intro s t
    exact ⟨max s t, scale_image_mono G s.2.1 (le_max_left s t : s ≤ max s t),
      scale_image_mono G t.2.1 (le_max_right s t : t ≤ max s t)⟩
  have hunion : (⋃ s, Ωs s) = G '' ball 0 1 := by
    apply le_antisymm
    · exact Set.iUnion_subset fun s => scale_image_subset G s.2.1 s.2.2
    · rintro _ ⟨z, hz, rfl⟩
      rw [mem_ball, dist_zero_right] at hz
      set s : ℝ := (‖z‖ + 1) / 2 with hsdef
      have hs0 : 0 < s := by positivity
      have hs1 : s < 1 := by rw [hsdef]; linarith
      refine Set.mem_iUnion.2 ⟨⟨s, hs0, hs1⟩, ?_⟩
      refine ⟨(1 / (s : ℂ)) * z, ?_, ?_⟩
      · rw [mem_ball, dist_zero_right, norm_mul, norm_div, norm_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hs0, div_mul_eq_mul_div, one_mul, div_lt_one hs0, hsdef]
        linarith
      · simp only
        congr 1
        have : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
        field_simp
  have hlim := dirichletEigenvalue_iUnion_directed Ωs hopen_s hdir j
  rw [hunion] at hlim
  exact hlim

end

section

/-! ## Rescaling of the boundary transport -/

open scoped InnerProductSpace
open MeasureTheory Set Real Metric Complex

variable {G : ℂ → ℂ} (k : ℝ)

lemma deriv_scale (s : ℝ) (w : ℂ) :
    deriv (fun z => G ((s : ℂ) * z)) w = (s : ℂ) * deriv G ((s : ℂ) * w) := by
  have := deriv_comp_mul_left (f := G) (c := (s : ℂ)) (x := w)
  simpa [smul_eq_mul] using this

lemma dAng_scale (s r θ : ℝ) : dAng (fun z => G ((s : ℂ) * z)) r θ = dAng G (s * r) θ := by
  simp only [dAng, deriv_scale]
  push_cast
  ring_nf

lemma coefAng_scale (s r : ℝ) :
    coefAng (fun z => G ((s : ℂ) * z)) k r = coefAng G k (s * r) := by
  funext θ
  simp only [coefAng, dAng_scale]

lemma holW_scale (s r : ℝ) : holW (fun z => G ((s : ℂ) * z)) k r = holW G k (s * r) := by
  simp only [holW, coefAng_scale]

lemma jac_scale {s : ℝ} (hs : 0 ≤ s) (r θ : ℝ) :
    jac (fun z => G ((s : ℂ) * z)) r θ = s * jac G (s * r) θ := by
  simp only [jac, deriv_scale, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
  push_cast
  ring_nf

lemma coefRad_scale (s r : ℝ) :
    coefRad (fun z => G ((s : ℂ) * z)) k r = (s : ℂ) • coefRad G k (s * r) := by
  simp only [coefRad, deriv_scale, smul_add, smul_smul, Complex.re_ofReal_mul,
    Complex.im_ofReal_mul, ofReal_mul]

lemma differentiableOn_scale (hG : DifferentiableOn ℂ G (ball 0 1)) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : DifferentiableOn ℂ (fun z => G ((s : ℂ) * z)) (ball 0 1) := by
  refine hG.comp (differentiableOn_id.const_mul _) fun z hz => ?_
  rw [mem_ball, dist_zero_right] at hz ⊢
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
  calc s * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
    _ < 1 := by rw [one_mul]; exact hz

lemma holR_scale (hG : DifferentiableOn ℂ G (ball 0 1)) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) :
    holR (fun z => G ((s : ℂ) * z)) k r = holR G k (s * r) := by
  have hGs := differentiableOn_scale hG hs0 hs1
  obtain ⟨h0s, hds⟩ := holR_spec k isOpen_ball hGs seg_mem_ball
  obtain ⟨h0, hd⟩ := holR_spec k isOpen_ball hG seg_mem_ball
  have hmaps : MapsTo (fun t : ℝ => s * t) (Ico (0 : ℝ) 1) (Ico (0 : ℝ) 1) := fun t ht =>
    ⟨mul_nonneg hs0 ht.1, lt_of_le_of_lt (mul_le_of_le_one_left ht.1 hs1) ht.2⟩
  have hV : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt (fun t => holR G k (s * t))
      (coefRad (fun z => G ((s : ℂ) * z)) k t * holR G k (s * t)) (Ico 0 1) t := by
    intro t ht
    have h1 := (hd (s * t) (hmaps ht)).scomp t
      ((hasDerivWithinAt_id t (Ico 0 1)).const_mul s) hmaps
    convert h1 using 1
    · simp [Function.comp_def]
    · rw [coefRad_scale]
      apply ContinuousLinearMap.ext
      intro x
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, mul_one]
      exact (RCLike.real_smul_eq_coe_smul (K := ℂ) (E := L2N) s _).symm
  have hsub : Icc 0 r ⊆ Ico (0 : ℝ) 1 := Icc_subset_Ico_right hr.2
  have heq := eqOn_of_linear_ode_Icc
    ((continuousOn_coefRad k isOpen_ball hGs seg_mem_ball).mono hsub)
    (fun t ht => (hds t (hsub ht)).mono hsub) (fun t ht => (hV t (hsub ht)).mono hsub)
    (by simp [h0s, h0]) (⟨hr.1, le_rfl⟩ : r ∈ Icc 0 r)
  exact heq

/-- **Rescaling.** `L^{G_s}_{r,k} = s L^{G}_{sr,k}` for `0 ≤ s ≤ 1`, `0 ≤ r < 1`. -/
theorem holL_scale (hG : DifferentiableOn ℂ G (ball 0 1)) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) :
    holL (fun z => G ((s : ℂ) * z)) k r = (s : ℂ) • holL G k (s * r) := by
  have hint : (∫ θ in (0 : ℝ)..(2 * π), ((jac (fun z => G ((s : ℂ) * z)) r θ : ℝ) : ℂ) •
      (star (holW G k (s * r) θ) * projE0 * holW G k (s * r) θ)) =
      (s : ℂ) • ∫ θ in (0 : ℝ)..(2 * π), ((jac G (s * r) θ : ℝ) : ℂ) •
      (star (holW G k (s * r) θ) * projE0 * holW G k (s * r) θ) := by
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [jac_scale hs0, ofReal_mul, smul_smul]
  simp only [holL, holH, holV, holQ, holW_scale, holR_scale k hG hs0 hs1 hr, hint,
    smul_mul_assoc, mul_smul_comm, smul_comm ((s : ℂ)) ((((k ^ 2 / 2 : ℝ)) : ℂ))]

/-- Uniform positivity of the tail integrals of the rescaled maps `G_s`, `3/4 ≤ s ≤ 1`, for
wave numbers `k'` near `k`. -/
theorem tail_integral_scale_ge (hG : DifferentiableOn ℂ G (ball 0 1))
    (hinj : InjOn G (ball 0 1)) (hk : 0 < k) (m : ℕ) :
    ∃ c > 0, ∃ η > 0, ∀ s : ℝ, 3 / 4 ≤ s → s ≤ 1 → ∀ k' : ℝ, |k' - k| < η →
      ENNReal.ofReal c ≤ ∫⁻ r in Ico 0 1, spectralTail m (holL (fun z => G ((s : ℂ) * z)) k' r) := by
  obtain ⟨c, hc, η, hη, h⟩ := spectralTail_holL_ge k hG hinj hk m
    (show (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 by norm_num)
  set η' := min η (1 / 8) with hη'
  have hη'pos : 0 < η' := lt_min hη (by norm_num)
  have hη'η : η' ≤ η := min_le_left _ _
  have hη'8 : η' ≤ 1 / 8 := min_le_right _ _
  refine ⟨3 / 4 * c * (2 * η'), by positivity, η, hη, fun s hs34 hs1 k' hk' => ?_⟩
  have hs0 : 0 < s := by linarith
  set J := Ioo ((1 / 2 - η') / s) ((1 / 2 + η') / s) with hJ
  have hJsub : J ⊆ Ico (0 : ℝ) 1 := by
    intro r hr
    have h1 : 0 < (1 / 2 - η') / s := div_pos (by linarith) hs0
    have h2 : (1 / 2 + η') / s < 1 := by rw [div_lt_one hs0]; linarith
    exact ⟨(h1.trans hr.1).le, hr.2.trans h2⟩
  have hbd : ∀ r ∈ J, ENNReal.ofReal (3 / 4 * c) ≤
      spectralTail m (holL (fun z => G ((s : ℂ) * z)) k' r) := by
    intro r hr
    have hr' := hJsub hr
    have h1 : 1 / 2 - η' < s * r := by
      have := hr.1; rwa [div_lt_iff₀ hs0, mul_comm] at this
    have h2 : s * r < 1 / 2 + η' := by
      have := hr.2; rwa [lt_div_iff₀ hs0, mul_comm] at this
    have hsr : s * r ∈ Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hsr' : |s * r - 1 / 2| < η := by rw [abs_lt]; constructor <;> linarith
    rw [holL_scale k' hG hs0.le hs1 hr', spectralTail_smul m s hs0.le,
      ENNReal.ofReal_mul (by norm_num)]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hs34) (h (s * r) hsr hsr' k' hk')
  have hvol : ENNReal.ofReal (2 * η') ≤ volume J := by
    rw [hJ, Real.volume_Ioo]
    apply ENNReal.ofReal_le_ofReal
    rw [← sub_div, div_eq_mul_inv]
    have : 1 ≤ s⁻¹ := one_le_inv₀ hs0 |>.2 hs1
    nlinarith
  calc ENNReal.ofReal (3 / 4 * c * (2 * η'))
      = ENNReal.ofReal (3 / 4 * c) * ENNReal.ofReal (2 * η') :=
        ENNReal.ofReal_mul (by positivity)
    _ ≤ ENNReal.ofReal (3 / 4 * c) * volume J := mul_le_mul_right hvol _
    _ = ∫⁻ _ in J, ENNReal.ofReal (3 / 4 * c) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ r in J, spectralTail m (holL (fun z => G ((s : ℂ) * z)) k' r) :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall hbd))
    _ ≤ _ := lintegral_mono_set hJsub

end

section

/-! ## The strict inequality by conformal exhaustion -/

open MeasureTheory Set Real Metric

/-- **Strict Pólya inequality for conformal images of the disk.** If `G` is holomorphic and
injective on the unit disk
and `Ω = G(𝔻)` is bounded, then `4πj < |Ω| λ_j(Ω)` for every `j ≥ 1`. -/
theorem strict_polya_conformal (G : ℂ → ℂ) (hG : DifferentiableOn ℂ G (ball 0 1))
    (hinj : InjOn G (ball 0 1)) (hbdd : Bornology.IsBounded (G '' ball 0 1)) (j : ℕ)
    (hj : 1 ≤ j) :
    ENNReal.ofReal (4 * π * j) < volume (G '' ball 0 1) * dirichletEigenvalue (G '' ball 0 1) j := by
  have hopen : IsOpen (G '' ball 0 1) := isOpen_image_of_injOn_ball hG hinj subset_rfl isOpen_ball
  have hvol : 0 < volume (G '' ball 0 1) :=
    hopen.measure_pos volume ⟨G 0, 0, mem_ball_self one_pos, rfl⟩
  have hvolfin : volume (G '' ball 0 1) ≠ ⊤ := hbdd.measure_lt_top.ne
  set lam := dirichletEigenvalue (G '' ball 0 1) j with hlam
  by_cases htop : lam = ⊤
  · rw [htop, ENNReal.mul_top hvol.ne']
    exact ENNReal.ofReal_lt_top
  have hpos : 0 < lam := dirichletEigenvalue_pos _ hbdd hj
  have hlr : 0 < lam.toReal := ENNReal.toReal_pos hpos.ne' htop
  set k := Real.sqrt lam.toReal with hkdef
  have hk0 : 0 < k := Real.sqrt_pos.2 hlr
  have hk2 : ENNReal.ofReal (k ^ 2) = lam := by
    rw [hkdef, Real.sq_sqrt hlr.le, ENNReal.ofReal_toReal htop]
  obtain ⟨c, hc, η, hη, htail⟩ := tail_integral_scale_ge k hG hinj hk0 j
  -- the eigenvalues of the rescaled domains
  set lamS : ℝ → ENNReal := fun s => dirichletEigenvalue ((fun z => G ((s : ℂ) * z)) '' ball 0 1) j
    with hlamS
  have hinf : lam = ⨅ s : Ioo (0 : ℝ) 1, lamS s := dirichletEigenvalue_eq_iInf_scale hG hinj j
  have hanti : ∀ a b : ℝ, 0 < a → a ≤ b → lamS b ≤ lamS a := fun a b ha hab =>
    dirichletEigenvalue_anti (scale_image_mono G ha hab) j
  have hge : ∀ s : ℝ, 0 < s → s < 1 → lam ≤ lamS s := fun s hs0 hs1 =>
    dirichletEigenvalue_anti (scale_image_subset G hs0 hs1) j
  -- choose `s₁` with `λ_j(G(s₁𝔻)) < (k + η/2)²`
  have hlt : lam < ENNReal.ofReal ((k + η / 2) ^ 2) := by
    rw [← hk2]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by nlinarith)
  rw [hinf] at hlt
  obtain ⟨s₁, hs₁⟩ := iInf_lt_iff.1 hlt
  set s₂ : ℝ := max (s₁ : ℝ) (3 / 4) with hs₂
  have hs₂0 : 0 < s₂ := lt_max_of_lt_right (by norm_num)
  have hs₂1 : s₂ < 1 := max_lt s₁.2.2 (by norm_num)
  -- the uniform bound for `s ∈ [s₂, 1)`
  have key : ∀ s : ℝ, s₂ ≤ s → s < 1 →
      ENNReal.ofReal (4 * π * j) + 2 * ENNReal.ofReal c ≤ volume (G '' ball 0 1) * lamS s := by
    intro s hs hs1
    have hs34 : 3 / 4 ≤ s := (le_max_right _ _).trans hs
    have hs0 : 0 < s := by linarith
    have hss₁ : (s₁ : ℝ) ≤ s := (le_max_left _ _).trans hs
    have hlamS_lt : lamS s < ENNReal.ofReal ((k + η / 2) ^ 2) :=
      lt_of_le_of_lt (hanti _ _ s₁.2.1 hss₁) hs₁
    have hlamS_top : lamS s ≠ ⊤ := ne_top_of_lt hlamS_lt
    have hlamS_pos : lam ≤ lamS s := hge s hs0 hs1
    set ks := Real.sqrt (lamS s).toReal with hksdef
    have hks2 : ENNReal.ofReal (ks ^ 2) = lamS s := by
      rw [hksdef, Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hlamS_top]
    have hks_ge : k ≤ ks := by
      rw [hkdef, hksdef]
      exact Real.sqrt_le_sqrt (ENNReal.toReal_mono hlamS_top hlamS_pos)
    have hks_lt : ks < k + η / 2 := by
      have h1 : ks ^ 2 < (k + η / 2) ^ 2 := by
        rw [← hks2] at hlamS_lt
        exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hlamS_lt
      nlinarith [Real.sqrt_nonneg (lamS s).toReal]
    have hks0 : 0 < ks := lt_of_lt_of_le hk0 hks_ge
    have hksη : |ks - k| < η := by
      rw [abs_lt]; constructor <;> linarith
    obtain ⟨hD, hd, hi⟩ := scale_hyps hG hinj hs0 hs1
    obtain ⟨hq, -⟩ := quantitative_analytic (fun z => G ((s : ℂ) * z)) (ball 0 (1 / s))
      isOpen_ball hD hd hi hks0 hj (by rw [hks2])
    have hT := htail s hs34 hs1.le ks hksη
    calc ENNReal.ofReal (4 * π * j) + 2 * ENNReal.ofReal c
        ≤ ENNReal.ofReal (4 * π * j) + 2 * ∫⁻ r in Ico 0 1,
            spectralTail j (holL (fun z => G ((s : ℂ) * z)) ks r) := by gcongr
      _ ≤ ENNReal.ofReal (ks ^ 2) * volume ((fun z => G ((s : ℂ) * z)) '' ball 0 1) := hq
      _ ≤ ENNReal.ofReal (ks ^ 2) * volume (G '' ball 0 1) := by
          gcongr; exact scale_image_subset G hs0 hs1
      _ = volume (G '' ball 0 1) * lamS s := by rw [hks2, mul_comm]
  -- pass to the limit
  have hbound : ENNReal.ofReal (4 * π * j) + 2 * ENNReal.ofReal c ≤ volume (G '' ball 0 1) * lam := by
    rw [hinf, ENNReal.mul_iInf_of_ne hvol.ne' hvolfin]
    refine le_iInf fun s => ?_
    have hm1 : max (s : ℝ) s₂ < 1 := max_lt s.2.2 hs₂1
    refine (key (max (s : ℝ) s₂) (le_max_right _ _) hm1).trans ?_
    gcongr
    exact hanti _ _ s.2.1 (le_max_left _ _)
  refine lt_of_lt_of_le ?_ hbound
  exact ENNReal.lt_add_right ENNReal.ofReal_ne_top
    (mul_ne_zero two_ne_zero (ENNReal.ofReal_pos.2 hc).ne')

end

section

/-! ## The strict Dirichlet Pólya inequality on simply connected planar domains -/

open MeasureTheory Real

/-- **Strict Dirichlet Pólya inequality, eigenvalue form.**
For a bounded, simply connected open set `Ω ⊆ ℂ` (simple connectivity includes
nonemptiness and connectedness), `4πj < |Ω| λ_j(Ω)` for every `j ≥ 1`. -/
theorem strict_polya_variational (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (hsc : SimplyConnectedSpace Ω) (j : ℕ) (hj : 1 ≤ j) :
    ENNReal.ofReal (4 * π * j) < volume Ω * dirichletEigenvalue Ω j := by
  have hne_univ : Ω ≠ Set.univ := by
    rintro rfl
    exact (NormedSpace.unbounded_univ ℝ ℂ) hbdd
  obtain ⟨G, hG, hinj, himg⟩ := riemann_mapping Ω hopen hsc hne_univ
  subst himg
  exact strict_polya_conformal G hG hinj hbdd j hj

end

end

/-! Index counting for a monotone sequence, including multiplicities and the
inclusive endpoint. The specialization below counts the existing variational
values; identification with the operator spectrum is a separate theorem. -/

noncomputable section

namespace DirichletBridge

open MeasureTheory Set Real

def countingSet (eig : ℕ → ℝ) (E : ℝ) : Set ℕ := {j | 1 ≤ j ∧ eig j ≤ E}

def count (eig : ℕ → ℝ) (E : ℝ) : ℕ := (countingSet eig E).ncard

theorem countingSet_finite_of_growth (eig : ℕ → ℝ) {a c : ℝ}
    (ha : 0 < a) (hc : 0 < c)
    (hbound : ∀ j, 1 ≤ j → c * j < a * eig j) (E : ℝ) :
    (countingSet eig E).Finite := by
  obtain ⟨N, hN⟩ := exists_nat_gt (a * E / c)
  apply (Set.finite_Iio N).subset
  intro j hj
  have hj' := hbound j hj.1
  have hE := mul_le_mul_of_nonneg_left hj.2 ha.le
  have hreal : (j : ℝ) < a * E / c := by
    apply (lt_div_iff₀ hc).2
    nlinarith
  exact_mod_cast hreal.trans hN

theorem count_strict_of_growth (eig : ℕ → ℝ) (hmono : Monotone eig)
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hbound : ∀ j, 1 ≤ j → c * j < a * eig j) {E : ℝ} (hE : 0 < E) :
    c * count eig E < a * E := by
  classical
  have hfin := countingSet_finite_of_growth eig ha hc hbound E
  by_cases hne : (countingSet eig E).Nonempty
  · let s := hfin.toFinset
    have hs : s.Nonempty := by simpa [s] using hne
    let m := s.max' hs
    have hm : m ∈ countingSet eig E := by
      exact hfin.mem_toFinset.mp (Finset.max'_mem s hs)
    have hset : countingSet eig E = Set.Icc 1 m := by
      ext j
      constructor
      · intro hj
        exact ⟨hj.1, Finset.le_max' s j (hfin.mem_toFinset.mpr hj)⟩
      · intro hj
        exact ⟨hj.1, (hmono hj.2).trans hm.2⟩
    have hcount : count eig E = m := by
      simp [count, hset]
    rw [hcount]
    exact (hbound m hm.1).trans_le (mul_le_mul_of_nonneg_left hm.2 ha.le)
  · have hzero : count eig E = 0 := by
      simp [count, Set.not_nonempty_iff_eq_empty.mp hne]
    rw [hzero, Nat.cast_zero, mul_zero]
    exact mul_pos ha hE

theorem growth_of_count_strict (eig : ℕ → ℝ) (hmono : Monotone eig)
    (hpos : ∀ j, 1 ≤ j → 0 < eig j)
    (hfin : ∀ E, (countingSet eig E).Finite)
    {a c : ℝ} (hc : 0 < c)
    (hcount : ∀ E, 0 < E → c * count eig E < a * E) :
    ∀ j, 1 ≤ j → c * j < a * eig j := by
  intro j hj
  have hsubset : Set.Icc 1 j ⊆ countingSet eig (eig j) := by
    intro i hi
    exact ⟨hi.1, hmono hi.2⟩
  have hjcount : j ≤ count eig (eig j) := by
    simpa [count] using Set.ncard_le_ncard hsubset (hfin (eig j))
  have hreal : (j : ℝ) ≤ count eig (eig j) := by exact_mod_cast hjcount
  exact (mul_le_mul_of_nonneg_left hreal hc.le).trans_lt (hcount (eig j) (hpos j hj))

theorem growth_iff_count_strict (eig : ℕ → ℝ) (hmono : Monotone eig)
    (hpos : ∀ j, 1 ≤ j → 0 < eig j)
    (hfin : ∀ E, (countingSet eig E).Finite)
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    (∀ j, 1 ≤ j → c * j < a * eig j) ↔
      (∀ E, 0 < E → c * count eig E < a * E) := by
  constructor
  · intro hbound E hE
    exact count_strict_of_growth eig hmono ha hc hbound hE
  · exact growth_of_count_strict eig hmono hpos hfin hc

def variationalEigenvalue (Ω : Set ℂ) (j : ℕ) : ℝ :=
  (dirichletEigenvalue Ω j).toReal

def variationalCountingFunction (Ω : Set ℂ) (E : ℝ) : ℕ :=
  count (variationalEigenvalue Ω) E

theorem variationalEigenvalue_mono {Ω : Set ℂ} (hopen : IsOpen Ω)
    (hne : Ω.Nonempty) : Monotone (variationalEigenvalue Ω) := by
  intro i j hij
  exact ENNReal.toReal_mono (dirichletEigenvalue_lt_top hopen hne j).ne
    (dirichletEigenvalue_mono Ω hij)

theorem variationalEigenvalue_pos {Ω : Set ℂ} (hopen : IsOpen Ω)
    (hne : Ω.Nonempty) (hbdd : Bornology.IsBounded Ω) {j : ℕ} (hj : 1 ≤ j) :
    0 < variationalEigenvalue Ω j :=
  ENNReal.toReal_pos_iff.mpr
    ⟨dirichletEigenvalue_pos Ω hbdd hj, dirichletEigenvalue_lt_top hopen hne j⟩

theorem strict_polya_real (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hne : Ω.Nonempty) (hbdd : Bornology.IsBounded Ω)
    (hsc : SimplyConnectedSpace Ω) (j : ℕ) (hj : 1 ≤ j) :
    4 * π * j < (volume Ω).toReal * variationalEigenvalue Ω j := by
  have hv := hbdd.measure_lt_top (μ := volume)
  have heig := dirichletEigenvalue_lt_top hopen hne j
  have h := strict_polya_variational Ω hopen hbdd hsc j hj
  rw [← ENNReal.ofReal_toReal hv.ne, ← ENNReal.ofReal_toReal heig.ne,
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg] at h
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp h

theorem polya_extended_iff_real (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hne : Ω.Nonempty) (hbdd : Bornology.IsBounded Ω) (j : ℕ) :
    (ENNReal.ofReal (4 * π * j) < volume Ω * dirichletEigenvalue Ω j) ↔
      (4 * π * j < (volume Ω).toReal * variationalEigenvalue Ω j) := by
  have hv := hbdd.measure_lt_top (μ := volume)
  have heig := dirichletEigenvalue_lt_top hopen hne j
  have heq : volume Ω * dirichletEigenvalue Ω j =
      ENNReal.ofReal ((volume Ω).toReal * variationalEigenvalue Ω j) := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hv.ne, variationalEigenvalue, ENNReal.ofReal_toReal heig.ne]
  rw [heq]
  exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)

theorem variationalCountingFunction_finite (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hne : Ω.Nonempty) (hbdd : Bornology.IsBounded Ω)
    (hsc : SimplyConnectedSpace Ω) (E : ℝ) :
    (countingSet (variationalEigenvalue Ω) E).Finite := by
  have ha : 0 < (volume Ω).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨hopen.measure_pos volume hne, hbdd.measure_lt_top⟩
  exact countingSet_finite_of_growth _ ha (by positivity)
    (strict_polya_real Ω hopen hne hbdd hsc) E

theorem strict_polya_variational_count (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hne : Ω.Nonempty) (hbdd : Bornology.IsBounded Ω)
    (hsc : SimplyConnectedSpace Ω) (E : ℝ) (hE : 0 < E) :
    (variationalCountingFunction Ω E : ℝ) < (volume Ω).toReal * E / (4 * π) := by
  have ha : 0 < (volume Ω).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨hopen.measure_pos volume hne, hbdd.measure_lt_top⟩
  apply (lt_div_iff₀ (by positivity : 0 < 4 * π)).2
  have h := count_strict_of_growth (variationalEigenvalue Ω)
    (variationalEigenvalue_mono hopen hne) ha (by positivity)
    (strict_polya_real Ω hopen hne hbdd hsc) hE
  simpa [variationalCountingFunction, mul_comm] using h

/-- The counting conclusion with exactly the domain hypotheses of the original
`main`; no separate nonemptiness assumption is required. -/
theorem strict_polya_counting (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (hsc : SimplyConnectedSpace Ω)
    (E : ℝ) (hE : 0 < E) :
    (variationalCountingFunction Ω E : ℝ) < (volume Ω).toReal * E / (4 * π) := by
  letI : SimplyConnectedSpace Ω := hsc
  have hne : Ω.Nonempty := Set.nonempty_coe_sort.mp (inferInstance : Nonempty Ω)
  exact strict_polya_variational_count Ω hopen hne hbdd hsc E hE



end DirichletBridge

/-!
The zero-boundary Sobolev space as the Hilbert graph closure of smooth compactly
supported functions. The three coordinates are the value and the two real
directional derivatives. All coordinates use full-plane Lebesgue measure.
-/

noncomputable section

namespace DirichletBridge

open MeasureTheory Set Topology
open scoped InnerProductSpace

abbrev RealL2 := Lp ℝ 2 (volume : Measure ℂ)
abbrev JetL2 := PiLp 2 (fun _ : Fin 3 => RealL2)
abbrev SmoothCore (Ω : Set ℂ) := testFunctions Ω

lemma core_memLp (Ω : Set ℂ) (u : SmoothCore Ω) :
    MemLp (u : ℂ → ℝ) 2 volume :=
  u.property.1.continuous.memLp_of_hasCompactSupport u.property.2.1

lemma core_deriv_continuous (Ω : Set ℂ) (u : SmoothCore Ω) (v : ℂ) :
    Continuous (fun z => fderiv ℝ (u : ℂ → ℝ) z v) :=
  (u.property.1.continuous_fderiv (by simp)).clm_apply continuous_const

lemma core_deriv_hasCompactSupport (Ω : Set ℂ) (u : SmoothCore Ω) (v : ℂ) :
    HasCompactSupport (fun z => fderiv ℝ (u : ℂ → ℝ) z v) :=
  (u.property.2.1.fderiv (𝕜 := ℝ)).comp_left
    (g := fun T : ℂ →L[ℝ] ℝ => T v) (by simp)

lemma core_deriv_memLp (Ω : Set ℂ) (u : SmoothCore Ω) (v : ℂ) :
    MemLp (fun z => fderiv ℝ (u : ℂ → ℝ) z v) 2 volume :=
  (core_deriv_continuous Ω u v).memLp_of_hasCompactSupport
    (core_deriv_hasCompactSupport Ω u v)

def coreValue (Ω : Set ℂ) : SmoothCore Ω →ₗ[ℝ] RealL2 where
  toFun u := (core_memLp Ω u).toLp (u : ℂ → ℝ)
  map_add' u w := by
    exact MemLp.toLp_add (core_memLp Ω u) (core_memLp Ω w)
  map_smul' c u := by
    exact MemLp.toLp_const_smul c (core_memLp Ω u)

def coreDeriv (Ω : Set ℂ) (v : ℂ) : SmoothCore Ω →ₗ[ℝ] RealL2 where
  toFun u := (core_deriv_memLp Ω u v).toLp _
  map_add' u w := by
    apply Lp.ext
    filter_upwards [(core_deriv_memLp Ω (u + w) v).coeFn_toLp,
      Lp.coeFn_add ((core_deriv_memLp Ω u v).toLp _)
        ((core_deriv_memLp Ω w v).toLp _),
      (core_deriv_memLp Ω u v).coeFn_toLp,
      (core_deriv_memLp Ω w v).coeFn_toLp] with z huw hadd hu hw
    rw [huw, hadd]
    simp only [Pi.add_apply]
    rw [hu, hw]
    change fderiv ℝ ((u : ℂ → ℝ) + (w : ℂ → ℝ)) z v = _
    rw [fderiv_add (u.property.1.differentiable (by simp) z)
      (w.property.1.differentiable (by simp) z)]
    rfl
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [(core_deriv_memLp Ω (c • u) v).coeFn_toLp,
      Lp.coeFn_smul c ((core_deriv_memLp Ω u v).toLp _),
      (core_deriv_memLp Ω u v).coeFn_toLp] with z hcu hsmul hu
    simp only [RingHom.id_apply]
    rw [hcu, hsmul]
    simp only [Pi.smul_apply]
    rw [hu]
    change fderiv ℝ (c • (u : ℂ → ℝ)) z v = _
    rw [fderiv_const_smul (u.property.1.differentiable (by simp) z) c]
    rfl

def coreJet (Ω : Set ℂ) : SmoothCore Ω →ₗ[ℝ] JetL2 where
  toFun u := WithLp.toLp 2 ![coreValue Ω u, coreDeriv Ω 1 u, coreDeriv Ω Complex.I u]
  map_add' u w := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [map_add]
  map_smul' c u := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [map_smul]

def H01Subspace (Ω : Set ℂ) : Submodule ℝ JetL2 :=
  (coreJet Ω).range.topologicalClosure

abbrev H01 (Ω : Set ℂ) := H01Subspace Ω

instance (Ω : Set ℂ) : CompleteSpace (H01 Ω) :=
  inferInstanceAs (CompleteSpace (coreJet Ω).range.topologicalClosure)

def coreToH01 (Ω : Set ℂ) : SmoothCore Ω →ₗ[ℝ] H01 Ω :=
  (coreJet Ω).codRestrict (H01Subspace Ω)
    (fun u => (coreJet Ω).range.le_topologicalClosure ⟨u, rfl⟩)

lemma coreToH01_dense (Ω : Set ℂ) : DenseRange (coreToH01 Ω) := by
  intro u
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hu : (u : JetL2) ∈ closure ((coreJet Ω).range : Set JetL2) := u.property
  obtain ⟨x, hx, hdist⟩ := Metric.mem_closure_iff.1 hu ε hε
  obtain ⟨w, rfl⟩ := hx
  exact ⟨coreToH01 Ω w, ⟨w, rfl⟩, hdist⟩

def value (Ω : Set ℂ) : H01 Ω →L[ℝ] RealL2 :=
  (PiLp.proj 2 (fun _ : Fin 3 => RealL2) 0).comp (H01Subspace Ω).subtypeL

def direction (i : Fin 2) : ℂ := ![1, Complex.I] i

def gradient (Ω : Set ℂ) (i : Fin 2) : H01 Ω →L[ℝ] RealL2 :=
  (PiLp.proj 2 (fun _ : Fin 3 => RealL2) i.succ).comp (H01Subspace Ω).subtypeL

@[simp] lemma value_coreToH01 (Ω : Set ℂ) (u : SmoothCore Ω) :
    value Ω (coreToH01 Ω u) = coreValue Ω u := rfl

@[simp] lemma gradient_coreToH01 (Ω : Set ℂ) (i : Fin 2) (u : SmoothCore Ω) :
    gradient Ω i (coreToH01 Ω u) = coreDeriv Ω (direction i) u := by
  fin_cases i <;> rfl

lemma inner_realL2 (f g : RealL2) :
    ⟪f, g⟫_ℝ = ∫ z, f z * g z := by
  rw [L2.inner_def]
  simp [mul_comm]

lemma inner_coreValue_coreDeriv (Ω Δ : Set ℂ) (u : SmoothCore Ω)
    (w : SmoothCore Δ) (v : ℂ) :
    ⟪coreValue Ω u, coreDeriv Δ v w⟫_ℝ =
      ∫ z, (u : ℂ → ℝ) z * fderiv ℝ (w : ℂ → ℝ) z v := by
  rw [inner_realL2]
  apply integral_congr_ae
  filter_upwards [(core_memLp Ω u).coeFn_toLp,
    (core_deriv_memLp Δ w v).coeFn_toLp] with z hu hw
  change (core_memLp Ω u).toLp _ z * (core_deriv_memLp Δ w v).toLp _ z = _
  rw [hu, hw]

def weakTestFunctional (i : Fin 2) (φ : SmoothCore Set.univ) : JetL2 →L[ℝ] ℝ :=
  (innerSL ℝ (coreValue Set.univ φ)).comp
      (PiLp.proj 2 (fun _ : Fin 3 => RealL2) i.succ) +
    (innerSL ℝ (coreDeriv Set.univ (direction i) φ)).comp
      (PiLp.proj 2 (fun _ : Fin 3 => RealL2) 0)

lemma weakTestFunctional_coreJet (Ω : Set ℂ) (i : Fin 2)
    (φ : SmoothCore Set.univ) (u : SmoothCore Ω) :
    weakTestFunctional i φ (coreJet Ω u) = 0 := by
  have hgrad : (coreJet Ω u) i.succ = coreDeriv Ω (direction i) u := by
    fin_cases i <;> rfl
  change ⟪coreValue Set.univ φ, (coreJet Ω u) i.succ⟫_ℝ +
    ⟪coreDeriv Set.univ (direction i) φ, (coreJet Ω u) 0⟫_ℝ = 0
  rw [hgrad, show (coreJet Ω u) 0 = coreValue Ω u from rfl,
    real_inner_comm (coreValue Ω u) (coreDeriv Set.univ (direction i) φ),
    inner_coreValue_coreDeriv, inner_coreValue_coreDeriv]
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := (φ : ℂ → ℝ)) (g := (u : ℂ → ℝ)) (v := direction i)
    (((core_deriv_continuous Set.univ φ (direction i)).mul u.property.1.continuous).integrable_of_hasCompactSupport
      u.property.2.1.mul_left)
    ((φ.property.1.continuous.mul (core_deriv_continuous Ω u (direction i))).integrable_of_hasCompactSupport
      φ.property.2.1.mul_right)
    ((φ.property.1.continuous.mul u.property.1.continuous).integrable_of_hasCompactSupport
      φ.property.2.1.mul_right)
    (fun x _ => (φ.property.1.differentiable (by simp)).differentiableAt)
    (fun x _ => (u.property.1.differentiable (by simp)).differentiableAt)
  rw [hibp]
  have hcomm : (∫ z, (u : ℂ → ℝ) z * fderiv ℝ (φ : ℂ → ℝ) z (direction i)) =
      ∫ z, fderiv ℝ (φ : ℂ → ℝ) z (direction i) * (u : ℂ → ℝ) z := by
    congr 1
    funext z
    exact mul_comm _ _
  rw [hcomm]
  exact neg_add_cancel _

lemma weakTestFunctional_H01 (Ω : Set ℂ) (i : Fin 2)
    (φ : SmoothCore Set.univ) (u : H01 Ω) :
    weakTestFunctional i φ (u : JetL2) = 0 := by
  have hcore : (coreJet Ω).range ≤ (weakTestFunctional i φ).ker := by
    rintro x ⟨w, rfl⟩
    exact weakTestFunctional_coreJet Ω i φ w
  exact (coreJet Ω).range.topologicalClosure_minimal hcore
    (weakTestFunctional i φ).isClosed_ker u.property

lemma weak_derivative_identity (Ω : Set ℂ) (i : Fin 2)
    (φ : SmoothCore Set.univ) (u : H01 Ω) :
    ⟪coreValue Set.univ φ, gradient Ω i u⟫_ℝ +
      ⟪coreDeriv Set.univ (direction i) φ, value Ω u⟫_ℝ = 0 :=
  weakTestFunctional_H01 Ω i φ u

lemma value_eq_zero_imp (Ω : Set ℂ) (u : H01 Ω) (hu : value Ω u = 0) : u = 0 := by
  have hgrad : ∀ i : Fin 2, gradient Ω i u = 0 := by
    intro i
    apply (Lp.eq_zero_iff_ae_eq_zero).2
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((Lp.memLp (gradient Ω i u)).locallyIntegrable (by norm_num))
    intro g hg hgc
    let φ : SmoothCore Set.univ := ⟨g, hg, hgc, subset_univ _⟩
    have hw := weak_derivative_identity Ω i φ u
    rw [hu, inner_zero_right, add_zero, inner_realL2] at hw
    change (∫ z, g z * gradient Ω i u z) = 0
    rw [← hw]
    apply integral_congr_ae
    filter_upwards [(core_memLp Set.univ φ).coeFn_toLp] with z hz
    change g z * gradient Ω i u z = (core_memLp Set.univ φ).toLp _ z * _
    rw [hz]
  apply Subtype.ext
  apply PiLp.ext
  intro k
  fin_cases k
  · exact hu
  · exact hgrad 0
  · exact hgrad 1

lemma value_injective (Ω : Set ℂ) : Function.Injective (value Ω) := by
  intro u w huw
  apply sub_eq_zero.mp
  apply value_eq_zero_imp Ω (u - w)
  rw [map_sub, huw, sub_self]

abbrev DomainL2 (Ω : Set ℂ) := Lp ℝ 2 (volume.restrict Ω)

def restrictL2Linear (Ω : Set ℂ) : RealL2 →ₗ[ℝ] DomainL2 Ω where
  toFun f := ((Lp.memLp f).restrict Ω).toLp (f : ℂ → ℝ)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [((Lp.memLp (f + g)).restrict Ω).coeFn_toLp,
      Lp.coeFn_add (((Lp.memLp f).restrict Ω).toLp _)
        (((Lp.memLp g).restrict Ω).toLp _),
      ((Lp.memLp f).restrict Ω).coeFn_toLp,
      ((Lp.memLp g).restrict Ω).coeFn_toLp,
      ae_restrict_of_ae (Lp.coeFn_add f g)] with z hfg hadd hf hg hsum
    rw [hfg, hadd, hsum]
    simp only [Pi.add_apply, hf, hg]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [((Lp.memLp (c • f)).restrict Ω).coeFn_toLp,
      Lp.coeFn_smul c (((Lp.memLp f).restrict Ω).toLp _),
      ((Lp.memLp f).restrict Ω).coeFn_toLp,
      ae_restrict_of_ae (Lp.coeFn_smul c f)] with z hcf hsmul hf hscalar
    simp only [RingHom.id_apply]
    rw [hcf, hsmul, hscalar]
    simp only [Pi.smul_apply, hf]

lemma restrictL2Linear_norm_le (Ω : Set ℂ) (f : RealL2) :
    ‖restrictL2Linear Ω f‖ ≤ ‖f‖ := by
  change ‖((Lp.memLp f).restrict Ω).toLp (f : ℂ → ℝ)‖ ≤ ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_mono_measure (f : ℂ → ℝ) Measure.restrict_le_self)

def restrictL2 (Ω : Set ℂ) : RealL2 →L[ℝ] DomainL2 Ω :=
  (restrictL2Linear Ω).mkContinuous 1 (by
    intro f
    simpa using restrictL2Linear_norm_le Ω f)

lemma restrictL2_coeFn (Ω : Set ℂ) (f : RealL2) :
    (restrictL2 Ω f : ℂ → ℝ) =ᵐ[volume.restrict Ω] f :=
  ((Lp.memLp f).restrict Ω).coeFn_toLp

lemma core_zero_outside (Ω : Set ℂ) (u : SmoothCore Ω) {z : ℂ} (hz : z ∉ Ω) :
    (u : ℂ → ℝ) z = 0 := by
  by_contra h
  exact hz (u.property.2.2 (subset_closure h))

lemma restrictL2_compl_coreValue_zero (Ω : Set ℂ) (hΩ : MeasurableSet Ω)
    (u : SmoothCore Ω) : restrictL2 Ωᶜ (coreValue Ω u) = 0 := by
  apply (Lp.eq_zero_iff_ae_eq_zero).2
  filter_upwards [restrictL2_coeFn Ωᶜ (coreValue Ω u),
    ae_restrict_of_ae (core_memLp Ω u).coeFn_toLp,
    ae_restrict_mem hΩ.compl] with z hrestrict hcore hz
  rw [hrestrict]
  change (core_memLp Ω u).toLp _ z = 0
  rw [hcore]
  exact core_zero_outside Ω u hz

lemma restrictL2_compl_value_zero (Ω : Set ℂ) (hΩ : MeasurableSet Ω)
    (u : H01 Ω) : restrictL2 Ωᶜ (value Ω u) = 0 := by
  let F : JetL2 →L[ℝ] DomainL2 Ωᶜ :=
    (restrictL2 Ωᶜ).comp (PiLp.proj 2 (fun _ : Fin 3 => RealL2) 0)
  have hcore : (coreJet Ω).range ≤ F.ker := by
    rintro x ⟨w, rfl⟩
    exact restrictL2_compl_coreValue_zero Ω hΩ w
  exact (coreJet Ω).range.topologicalClosure_minimal hcore F.isClosed_ker u.property

def inclusion (Ω : Set ℂ) : H01 Ω →L[ℝ] DomainL2 Ω :=
  (restrictL2 Ω).comp (value Ω)

lemma inclusion_coeFn (Ω : Set ℂ) (u : H01 Ω) :
    (inclusion Ω u : ℂ → ℝ) =ᵐ[volume.restrict Ω] value Ω u :=
  restrictL2_coeFn Ω (value Ω u)

lemma inclusion_eq_zero_imp (Ω : Set ℂ) (hΩ : MeasurableSet Ω)
    (u : H01 Ω) (hu : inclusion Ω u = 0) : u = 0 := by
  apply value_eq_zero_imp Ω u
  apply (Lp.eq_zero_iff_ae_eq_zero).2
  apply ae_of_ae_restrict_of_ae_restrict_compl Ω
  · have hzero : (inclusion Ω u : ℂ → ℝ) =ᵐ[volume.restrict Ω] 0 :=
      (Lp.eq_zero_iff_ae_eq_zero).1 hu
    exact (inclusion_coeFn Ω u).symm.trans hzero
  · have hzero : (restrictL2 Ωᶜ (value Ω u) : ℂ → ℝ) =ᵐ[volume.restrict Ωᶜ] 0 :=
      (Lp.eq_zero_iff_ae_eq_zero).1 (restrictL2_compl_value_zero Ω hΩ u)
    exact (restrictL2_coeFn Ωᶜ (value Ω u)).symm.trans hzero

lemma inclusion_injective (Ω : Set ℂ) (hΩ : MeasurableSet Ω) :
    Function.Injective (inclusion Ω) := by
  intro u w huw
  apply sub_eq_zero.mp
  apply inclusion_eq_zero_imp Ω hΩ (u - w)
  rw [map_sub, huw, sub_self]

lemma inner_domainL2 (Ω : Set ℂ) (f g : DomainL2 Ω) :
    ⟪f, g⟫_ℝ = ∫ z, f z * g z ∂(volume.restrict Ω) := by
  rw [L2.inner_def]
  simp [mul_comm]

lemma inclusion_coreToH01_coeFn (Ω : Set ℂ) (u : SmoothCore Ω) :
    (inclusion Ω (coreToH01 Ω u) : ℂ → ℝ) =ᵐ[volume.restrict Ω] (u : ℂ → ℝ) := by
  apply (inclusion_coeFn Ω (coreToH01 Ω u)).trans
  change ((core_memLp Ω u).toLp (u : ℂ → ℝ) : ℂ → ℝ) =ᵐ[volume.restrict Ω] _
  exact ae_restrict_of_ae (core_memLp Ω u).coeFn_toLp

lemma inclusion_dense (Ω : Set ℂ) (hΩ : IsOpen Ω) : DenseRange (inclusion Ω) := by
  have hperp : (inclusion Ω).rangeᗮ = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro f hf
    apply (Lp.eq_zero_iff_ae_eq_zero).2
    let F : ℂ → ℝ := Ω.indicator (f : ℂ → ℝ)
    have hF : MemLp F 2 volume :=
      (memLp_indicator_iff_restrict hΩ.measurableSet).2 (Lp.memLp f)
    have htest : ∀ (g : ℂ → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
        tsupport g ⊆ Ω → ∫ z, g z • F z = 0 := by
      intro g hg hgc hgs
      let φ : SmoothCore Ω := ⟨g, hg, hgc, hgs⟩
      have horth : ⟪inclusion Ω (coreToH01 Ω φ), f⟫_ℝ = 0 :=
        ((inclusion Ω).range.mem_orthogonal f).1 hf
          (inclusion Ω (coreToH01 Ω φ)) ⟨coreToH01 Ω φ, rfl⟩
      rw [inner_domainL2] at horth
      have hind : (fun z => g z • F z) = Ω.indicator (fun z => g z * f z) := by
        funext z
        by_cases hz : z ∈ Ω <;> simp [F, hz, smul_eq_mul]
      rw [hind, integral_indicator hΩ.measurableSet]
      calc (∫ z, g z * f z ∂(volume.restrict Ω)) =
          ∫ z, inclusion Ω (coreToH01 Ω φ) z * f z ∂(volume.restrict Ω) := by
            apply integral_congr_ae
            filter_upwards [inclusion_coreToH01_coeFn Ω φ] with z hz
            rw [hz]
        _ = 0 := horth
    have hae : ∀ᵐ z ∂volume, z ∈ Ω → F z = 0 :=
      hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        ((hF.locallyIntegrable (by norm_num)).locallyIntegrableOn Ω) htest
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hΩ.measurableSet] with z hz hmem
    simpa [F, hmem] using hz hmem
  change Dense ((inclusion Ω).range : Set (DomainL2 Ω))
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    ← Submodule.orthogonal_orthogonal_eq_closure, hperp, Submodule.bot_orthogonal_eq_top]

lemma norm_coreValue_sq (Ω : Set ℂ) (u : SmoothCore Ω) :
    ‖coreValue Ω u‖ ^ 2 = ∫ z, (u : ℂ → ℝ) z ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_realL2]
  apply integral_congr_ae
  filter_upwards [(core_memLp Ω u).coeFn_toLp] with z hz
  change (core_memLp Ω u).toLp _ z * (core_memLp Ω u).toLp _ z = (u : ℂ → ℝ) z ^ 2
  rw [hz, pow_two]

lemma norm_coreDeriv_sq (Ω : Set ℂ) (v : ℂ) (u : SmoothCore Ω) :
    ‖coreDeriv Ω v u‖ ^ 2 = ∫ z, (fderiv ℝ (u : ℂ → ℝ) z v) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_realL2]
  apply integral_congr_ae
  filter_upwards [(core_deriv_memLp Ω u v).coeFn_toLp] with z hz
  change (core_deriv_memLp Ω u v).toLp _ z *
    (core_deriv_memLp Ω u v).toLp _ z = (fderiv ℝ (u : ℂ → ℝ) z v) ^ 2
  rw [hz, pow_two]

lemma l2NormSq_core (Ω : Set ℂ) (u : SmoothCore Ω) :
    l2NormSq (u : ℂ → ℝ) = ENNReal.ofReal (‖coreValue Ω u‖ ^ 2) := by
  unfold l2NormSq
  simp_rw [enorm_sq_eq_ofReal]
  rw [← ofReal_integral_eq_lintegral_ofReal (core_memLp Ω u).integrable_sq
    (Filter.Eventually.of_forall fun z => sq_nonneg ((u : ℂ → ℝ) z)), norm_coreValue_sq]

lemma dirichletEnergy_core (Ω : Set ℂ) (u : SmoothCore Ω) :
    dirichletEnergy (u : ℂ → ℝ) =
      ENNReal.ofReal (‖coreDeriv Ω 1 u‖ ^ 2 + ‖coreDeriv Ω Complex.I u‖ ^ 2) := by
  unfold dirichletEnergy
  simp_rw [enorm_sq_eq_ofReal', norm_clm_sq]
  have h1 := (core_deriv_memLp Ω u 1).integrable_sq
  have hI := (core_deriv_memLp Ω u Complex.I).integrable_sq
  have hi : Integrable (fun z => fderiv ℝ (u : ℂ → ℝ) z 1 ^ 2 +
      fderiv ℝ (u : ℂ → ℝ) z Complex.I ^ 2) volume := h1.add hI
  have hsplit : (∫ z, fderiv ℝ (u : ℂ → ℝ) z 1 ^ 2 +
      fderiv ℝ (u : ℂ → ℝ) z Complex.I ^ 2) =
      (∫ z, fderiv ℝ (u : ℂ → ℝ) z 1 ^ 2) +
      ∫ z, fderiv ℝ (u : ℂ → ℝ) z Complex.I ^ 2 := integral_add h1 hI
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun z => add_nonneg (sq_nonneg _) (sq_nonneg _)),
    hsplit, norm_coreDeriv_sq, norm_coreDeriv_sq]

lemma poincare_core (Ω : Set ℂ) (hΩ : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : SmoothCore Ω,
      ‖coreValue Ω u‖ ^ 2 ≤ C *
        (‖coreDeriv Ω 1 u‖ ^ 2 + ‖coreDeriv Ω Complex.I u‖ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := poincare_inequality Ω hΩ
  refine ⟨C, hC, fun u => ?_⟩
  have h := hbound (u : ℂ → ℝ) u.property
  rw [l2NormSq_core Ω u, dirichletEnergy_core Ω u] at h
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h

def energy (Ω : Set ℂ) (u : H01 Ω) : ℝ :=
  ‖gradient Ω 0 u‖ ^ 2 + ‖gradient Ω 1 u‖ ^ 2

lemma norm_H01_sq (Ω : Set ℂ) (u : H01 Ω) :
    ‖u‖ ^ 2 = ‖value Ω u‖ ^ 2 + energy Ω u := by
  change ‖(u : JetL2)‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  simp [Fin.sum_univ_succ, value, gradient, energy]

lemma poincare_H01 (Ω : Set ℂ) (hΩ : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : H01 Ω, ‖value Ω u‖ ^ 2 ≤ C * energy Ω u := by
  obtain ⟨C, hC, hbound⟩ := poincare_core Ω hΩ
  refine ⟨C, hC, fun u => ?_⟩
  let S : Set JetL2 := {x | ‖x 0‖ ^ 2 ≤ C * (‖x 1‖ ^ 2 + ‖x 2‖ ^ 2)}
  have h0 : Continuous (fun x : JetL2 => ‖x 0‖ ^ 2) :=
    ((PiLp.proj 2 (fun _ : Fin 3 => RealL2) 0 : JetL2 →L[ℝ] RealL2).continuous.norm).pow 2
  have h1 : Continuous (fun x : JetL2 => ‖x 1‖ ^ 2) :=
    ((PiLp.proj 2 (fun _ : Fin 3 => RealL2) 1 : JetL2 →L[ℝ] RealL2).continuous.norm).pow 2
  have h2 : Continuous (fun x : JetL2 => ‖x 2‖ ^ 2) :=
    ((PiLp.proj 2 (fun _ : Fin 3 => RealL2) 2 : JetL2 →L[ℝ] RealL2).continuous.norm).pow 2
  have hS : IsClosed S := isClosed_le h0 (continuous_const.mul (h1.add h2))
  have hcore : ((coreJet Ω).range : Set JetL2) ⊆ S := by
    rintro x ⟨w, rfl⟩
    exact hbound w
  exact closure_minimal hcore hS u.property

lemma energy_controls_H01_norm (Ω : Set ℂ) (hΩ : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : H01 Ω, ‖u‖ ^ 2 ≤ C * energy Ω u := by
  obtain ⟨C, hC, hbound⟩ := poincare_H01 Ω hΩ
  refine ⟨C + 1, by linarith, fun u => ?_⟩
  rw [norm_H01_sq]
  calc ‖value Ω u‖ ^ 2 + energy Ω u ≤ C * energy Ω u + energy Ω u :=
      add_le_add (hbound u) le_rfl
    _ = (C + 1) * energy Ω u := by ring

/-- The Dirichlet form contains only gradient coordinates; the inherited Hilbert
inner product on `H01` also contains the value coordinate. -/
def energyForm (Ω : Set ℂ) : H01 Ω →L[ℝ] H01 Ω →L[ℝ] ℝ :=
  (innerSL ℝ (E := RealL2)).bilinearComp (gradient Ω 0) (gradient Ω 0) +
    (innerSL ℝ (E := RealL2)).bilinearComp (gradient Ω 1) (gradient Ω 1)

@[simp] lemma energyForm_apply (Ω : Set ℂ) (u v : H01 Ω) :
    energyForm Ω u v = ⟪gradient Ω 0 u, gradient Ω 0 v⟫_ℝ +
      ⟪gradient Ω 1 u, gradient Ω 1 v⟫_ℝ := rfl

@[simp] lemma energyForm_self (Ω : Set ℂ) (u : H01 Ω) :
    energyForm Ω u u = energy Ω u := by
  simp [energy]

lemma energyForm_symmetric (Ω : Set ℂ) (u v : H01 Ω) :
    energyForm Ω u v = energyForm Ω v u := by
  simp only [energyForm_apply, real_inner_comm]

lemma energyForm_coercive (Ω : Set ℂ) (hΩ : Bornology.IsBounded Ω) :
    IsCoercive (energyForm Ω) := by
  obtain ⟨C, hC, hbound⟩ := energy_controls_H01_norm Ω hΩ
  refine ⟨C⁻¹, inv_pos.mpr hC, fun u => ?_⟩
  rw [energyForm_self]
  have h := mul_le_mul_of_nonneg_left (hbound u) (inv_nonneg.mpr hC.le)
  calc C⁻¹ * ‖u‖ * ‖u‖ = C⁻¹ * ‖u‖ ^ 2 := by ring
    _ ≤ C⁻¹ * (C * energy Ω u) := h
    _ = energy Ω u := by rw [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]

lemma norm_restrictL2_eq_of_compl_zero (Ω : Set ℂ) (hΩ : MeasurableSet Ω)
    (f : RealL2) (hf : restrictL2 Ωᶜ f = 0) : ‖restrictL2 Ω f‖ = ‖f‖ := by
  have hzero : (f : ℂ → ℝ) =ᵐ[volume.restrict Ωᶜ] 0 :=
    (restrictL2_coeFn Ωᶜ f).symm.trans ((Lp.eq_zero_iff_ae_eq_zero).1 hf)
  have hind : Ω.indicator (f : ℂ → ℝ) =ᵐ[volume] f :=
    indicator_ae_eq_of_restrict_compl_ae_eq_zero hΩ hzero
  change ‖((Lp.memLp f).restrict Ω).toLp (f : ℂ → ℝ)‖ = ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def]
  have he : eLpNorm (f : ℂ → ℝ) 2 (volume.restrict Ω) =
      eLpNorm (f : ℂ → ℝ) 2 volume := by
    calc eLpNorm (f : ℂ → ℝ) 2 (volume.restrict Ω) =
        eLpNorm (Ω.indicator (f : ℂ → ℝ)) 2 volume :=
          (eLpNorm_indicator_eq_eLpNorm_restrict hΩ).symm
      _ = eLpNorm (f : ℂ → ℝ) 2 volume := eLpNorm_congr_ae hind
  rw [he]

lemma norm_inclusion_eq_value (Ω : Set ℂ) (hΩ : MeasurableSet Ω) (u : H01 Ω) :
    ‖inclusion Ω u‖ = ‖value Ω u‖ :=
  norm_restrictL2_eq_of_compl_zero Ω hΩ (value Ω u) (restrictL2_compl_value_zero Ω hΩ u)

lemma core_fderiv_zero_outside (Ω : Set ℂ) (u : SmoothCore Ω) {z : ℂ}
    (hz : z ∉ Ω) : fderiv ℝ (u : ℂ → ℝ) z = 0 := by
  by_contra h
  exact hz (u.property.2.2 (support_fderiv_subset ℝ h))

lemma restrictL2_compl_coreDeriv_zero (Ω : Set ℂ) (hΩ : MeasurableSet Ω)
    (v : ℂ) (u : SmoothCore Ω) : restrictL2 Ωᶜ (coreDeriv Ω v u) = 0 := by
  apply (Lp.eq_zero_iff_ae_eq_zero).2
  filter_upwards [restrictL2_coeFn Ωᶜ (coreDeriv Ω v u),
    ae_restrict_of_ae (core_deriv_memLp Ω u v).coeFn_toLp,
    ae_restrict_mem hΩ.compl] with z hrestrict hcore hz
  rw [hrestrict]
  change (core_deriv_memLp Ω u v).toLp _ z = 0
  rw [hcore, core_fderiv_zero_outside Ω u hz]
  simp

lemma restrictL2_compl_gradient_zero (Ω : Set ℂ) (hΩ : MeasurableSet Ω)
    (i : Fin 2) (u : H01 Ω) : restrictL2 Ωᶜ (gradient Ω i u) = 0 := by
  let F : JetL2 →L[ℝ] DomainL2 Ωᶜ :=
    (restrictL2 Ωᶜ).comp (PiLp.proj 2 (fun _ : Fin 3 => RealL2) i.succ)
  have hcore : (coreJet Ω).range ≤ F.ker := by
    rintro x ⟨w, rfl⟩
    change restrictL2 Ωᶜ (gradient Ω i (coreToH01 Ω w)) = 0
    rw [gradient_coreToH01]
    exact restrictL2_compl_coreDeriv_zero Ω hΩ (direction i) w
  exact (coreJet Ω).range.topologicalClosure_minimal hcore F.isClosed_ker u.property

def domainGradient (Ω : Set ℂ) (i : Fin 2) : H01 Ω →L[ℝ] DomainL2 Ω :=
  (restrictL2 Ω).comp (gradient Ω i)

lemma norm_domainGradient_eq_gradient (Ω : Set ℂ) (hΩ : MeasurableSet Ω)
    (i : Fin 2) (u : H01 Ω) : ‖domainGradient Ω i u‖ = ‖gradient Ω i u‖ :=
  norm_restrictL2_eq_of_compl_zero Ω hΩ (gradient Ω i u)
    (restrictL2_compl_gradient_zero Ω hΩ i u)

lemma inner_restrictL2_eq_of_compl_zero (Ω : Set ℂ) (hΩ : MeasurableSet Ω)
    (f g : RealL2) (hf : restrictL2 Ωᶜ f = 0) (hg : restrictL2 Ωᶜ g = 0) :
    ⟪restrictL2 Ω f, restrictL2 Ω g⟫_ℝ = ⟪f, g⟫_ℝ := by
  have hfg : restrictL2 Ωᶜ (f - g) = 0 := by rw [map_sub, hf, hg, sub_self]
  have h := norm_sub_sq_real f g
  have h' := norm_sub_sq_real (restrictL2 Ω f) (restrictL2 Ω g)
  rw [← map_sub, norm_restrictL2_eq_of_compl_zero Ω hΩ (f - g) hfg,
    norm_restrictL2_eq_of_compl_zero Ω hΩ f hf,
    norm_restrictL2_eq_of_compl_zero Ω hΩ g hg] at h'
  linarith

lemma energyForm_eq_domainGradient (Ω : Set ℂ) (hΩ : MeasurableSet Ω)
    (u v : H01 Ω) :
    energyForm Ω u v = ⟪domainGradient Ω 0 u, domainGradient Ω 0 v⟫_ℝ +
      ⟪domainGradient Ω 1 u, domainGradient Ω 1 v⟫_ℝ := by
  unfold domainGradient
  simp only [ContinuousLinearMap.comp_apply]
  rw [inner_restrictL2_eq_of_compl_zero Ω hΩ (gradient Ω 0 u) (gradient Ω 0 v)
      (restrictL2_compl_gradient_zero Ω hΩ 0 u) (restrictL2_compl_gradient_zero Ω hΩ 0 v),
    inner_restrictL2_eq_of_compl_zero Ω hΩ (gradient Ω 1 u) (gradient Ω 1 v)
      (restrictL2_compl_gradient_zero Ω hΩ 1 u) (restrictL2_compl_gradient_zero Ω hΩ 1 v)]
  rfl

lemma energyForm_eq_integral_domain (Ω : Set ℂ) (hΩ : MeasurableSet Ω)
    (u v : H01 Ω) : energyForm Ω u v =
    ∫ z in Ω, gradient Ω 0 u z * gradient Ω 0 v z +
      gradient Ω 1 u z * gradient Ω 1 v z := by
  rw [energyForm_eq_domainGradient Ω hΩ, inner_domainL2, inner_domainL2]
  have h0 : Integrable (fun z => domainGradient Ω 0 u z * domainGradient Ω 0 v z)
      (volume.restrict Ω) := by
    simpa [mul_comm] using L2.integrable_inner (𝕜 := ℝ) (domainGradient Ω 0 u) (domainGradient Ω 0 v)
  have h1 : Integrable (fun z => domainGradient Ω 1 u z * domainGradient Ω 1 v z)
      (volume.restrict Ω) := by
    simpa [mul_comm] using L2.integrable_inner (𝕜 := ℝ) (domainGradient Ω 1 u) (domainGradient Ω 1 v)
  have hsplit : (∫ z, domainGradient Ω 0 u z * domainGradient Ω 0 v z +
      domainGradient Ω 1 u z * domainGradient Ω 1 v z ∂(volume.restrict Ω)) =
      (∫ z, domainGradient Ω 0 u z * domainGradient Ω 0 v z ∂(volume.restrict Ω)) +
      ∫ z, domainGradient Ω 1 u z * domainGradient Ω 1 v z ∂(volume.restrict Ω) :=
    integral_add h0 h1
  rw [← hsplit]
  apply integral_congr_ae
  filter_upwards [restrictL2_coeFn Ω (gradient Ω 0 u), restrictL2_coeFn Ω (gradient Ω 0 v),
    restrictL2_coeFn Ω (gradient Ω 1 u), restrictL2_coeFn Ω (gradient Ω 1 v)] with z h0u h0v h1u h1v
  change (restrictL2 Ω (gradient Ω 0 u)) z * (restrictL2 Ω (gradient Ω 0 v)) z +
    (restrictL2 Ω (gradient Ω 1 u)) z * (restrictL2 Ω (gradient Ω 1 v)) z = _
  rw [h0u, h0v, h1u, h1v]

end DirichletBridge

namespace PolyaBridge.CompactSpectral

open Set
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- An infinite-dimensional inner-product space has a nonzero vector orthogonal to
any prescribed finite family. -/
theorem exists_nonzero_orthogonal (hInfinite : ¬ Module.Finite ℝ H)
    (e : ℕ → H) (n : ℕ) :
    ∃ x : H, x ≠ 0 ∧ ∀ i < n, ⟪e i, x⟫_ℝ = 0 := by
  classical
  let coordinates : H →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun x i => ⟪e i, x⟫_ℝ
      map_add' := by
        intro x y
        ext i
        simp [inner_add_right]
      map_smul' := by
        intro c x
        ext i
        simp [inner_smul_right] }
  have hker : LinearMap.ker coordinates ≠ ⊥ := by
    intro hker
    exact hInfinite
      (FiniteDimensional.of_injective coordinates (LinearMap.ker_eq_bot.mp hker))
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨x, hx0, ?_⟩
  intro i hi
  have hzero := congrFun (LinearMap.mem_ker.mp hx) (⟨i, hi⟩ : Fin n)
  simpa [coordinates] using hzero

/-- Finite successive maximizers of the quadratic form of an operator. The entries
outside `i < n` are unused. -/
structure PositiveEigenFamily (T : H →L[ℝ] H) (n : ℕ) where
  vectors : ℕ → H
  values : ℕ → ℝ
  orthogonal : ∀ i < n, ∀ l < n,
    ⟪vectors i, vectors l⟫_ℝ = if i = l then 1 else 0
  eigenvector : ∀ i < n, T (vectors i) = values i • vectors i
  positive : ∀ i < n, 0 < values i
  maximal : ∀ i < n, ∀ x,
    (∀ l < i, ⟪vectors l, x⟫_ℝ = 0) →
      ⟪T x, x⟫_ℝ ≤ values i * ‖x‖ ^ 2

namespace PositiveEigenFamily

variable {T : H →L[ℝ] H} {n : ℕ}

theorem norm_sq_eq_one (f : PositiveEigenFamily T n) {i : ℕ} (hi : i < n) :
    ‖f.vectors i‖ ^ 2 = 1 := by
  rw [← real_inner_self_eq_norm_sq, f.orthogonal i hi i hi, if_pos rfl]

theorem orthonormal (f : PositiveEigenFamily T n) :
    Orthonormal ℝ (fun i : Fin n => f.vectors i) := by
  classical
  rw [orthonormal_iff_ite]
  intro i l
  simpa only [Fin.ext_iff] using f.orthogonal i i.isLt l l.isLt

theorem value_le (f : PositiveEigenFamily T n) {i j : ℕ}
    (hi : i < n) (hj : j < n) (hij : i ≤ j) : f.values j ≤ f.values i := by
  have h := f.maximal i hi (f.vectors j) (by
    intro l hl
    have hlj : l ≠ j := (lt_of_lt_of_le hl hij).ne
    rw [f.orthogonal l (hl.trans hi) j hj, if_neg hlj])
  rw [f.eigenvector j hj, real_inner_smul_left,
    real_inner_self_eq_norm_sq, f.norm_sq_eq_one hj, mul_one, mul_one] at h
  exact h

theorem antitoneOn_values (f : PositiveEigenFamily T n) :
    AntitoneOn f.values (Iio n) := by
  intro i hi j hj hij
  exact f.value_le hi hj hij

end PositiveEigenFamily

/-- Strict positivity and infinite dimension rule out the stopping alternative in
`exists_eigen_family`. Consequently every finite truncation exists. -/
theorem exists_positive_eigenfamily {T : H →L[ℝ] H}
    (hCompact : IsCompactOperator T)
    (hSymmetric : ∀ x y, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ)
    (hPositive : ∀ x : H, x ≠ 0 → 0 < ⟪T x, x⟫_ℝ)
    (hInfinite : ¬ Module.Finite ℝ H) (n : ℕ) :
    Nonempty (PositiveEigenFamily T n) := by
  obtain ⟨m, e, μ, hmn, horth, heig, hmax, hstop⟩ :=
    _root_.exists_eigen_family hCompact hSymmetric n
  have hnm : n ≤ m := by
    by_contra hnm
    have hmn' : m < n := Nat.lt_of_not_ge hnm
    obtain ⟨x, hx0, hxorth⟩ := exists_nonzero_orthogonal hInfinite e m
    exact (not_lt_of_ge (hstop hmn' x hxorth)) (hPositive x hx0)
  have hmn_eq : m = n := le_antisymm hmn hnm
  subst m
  exact ⟨
    { vectors := e
      values := μ
      orthogonal := horth
      eigenvector := fun i hi => (heig i hi).1
      positive := fun i hi => (heig i hi).2
      maximal := hmax }⟩

/-- The truncation has genuinely orthonormal eigenvectors and decreasing positive
eigenvalues. This theorem does not assert compatibility between different truncations. -/
theorem exists_orthonormal_positive_eigenfamily {T : H →L[ℝ] H}
    (hCompact : IsCompactOperator T)
    (hSymmetric : ∀ x y, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ)
    (hPositive : ∀ x : H, x ≠ 0 → 0 < ⟪T x, x⟫_ℝ)
    (hInfinite : ¬ Module.Finite ℝ H) (n : ℕ) :
    ∃ f : PositiveEigenFamily T n,
      Orthonormal ℝ (fun i : Fin n => f.vectors i) ∧ AntitoneOn f.values (Iio n) := by
  obtain ⟨f⟩ := exists_positive_eigenfamily hCompact hSymmetric hPositive hInfinite n
  exact ⟨f, f.orthonormal, f.antitoneOn_values⟩

/-- Positive spectral thresholds supported by `j` orthonormal eigenvectors.
This definition uses genuine eigenvector equations, independently of any min-max quantity. -/
def SpectralThreshold (T : H →L[ℝ] H) (j : ℕ) : Set ℝ :=
  {s | 0 < s ∧ ∃ e : Fin j → H, Orthonormal ℝ e ∧
    ∃ ν : Fin j → ℝ, ∀ i, T (e i) = ν i • e i ∧ s ≤ ν i}

/-- The `j`-th decreasing positive eigenvalue, when the positive spectral
threshold set has a maximum. The theorems below establish this for `j > 0`. -/
noncomputable def spectralEigenvalue (T : H →L[ℝ] H) (j : ℕ) : ℝ :=
  sSup (SpectralThreshold T j)

/-- A spectral reciprocal; identification with a Dirichlet min-max is a separate theorem. -/
noncomputable def inverseSpectralEigenvalue (T : H →L[ℝ] H) (j : ℕ) : ENNReal :=
  ENNReal.ofReal (1 / spectralEigenvalue T j)

/-- The norm of a linear combination of orthonormal real vectors. -/
theorem norm_sq_sum_orthonormal {n : ℕ} {g : Fin n → H} (hg : Orthonormal ℝ g)
    (c : Fin n → ℝ) : ‖∑ i, c i • g i‖ ^ 2 = ∑ i, c i ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp_rw [real_inner_smul_left, hg.inner_right_fintype c]
  simp only [pow_two]

theorem quadratic_sum_eigenvectors {T : H →L[ℝ] H} {n : ℕ}
    {g : Fin n → H} (hg : Orthonormal ℝ g) (ν : Fin n → ℝ)
    (hEigen : ∀ i, T (g i) = ν i • g i) (c : Fin n → ℝ) :
    ⟪T (∑ i, c i • g i), ∑ i, c i • g i⟫_ℝ = ∑ i, ν i * c i ^ 2 := by
  classical
  rw [map_sum, sum_inner]
  simp_rw [map_smul, hEigen, smul_smul, real_inner_smul_left,
    hg.inner_right_fintype c]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- On the span of orthonormal eigenvectors with eigenvalues at least `s`, the
quadratic form is at least `s` times the norm squared. -/
theorem quadratic_lower_on_eigenspan {T : H →L[ℝ] H} {n : ℕ}
    {g : Fin n → H} (hg : Orthonormal ℝ g) (ν : Fin n → ℝ)
    (hEigen : ∀ i, T (g i) = ν i • g i) {s : ℝ} (hs : ∀ i, s ≤ ν i)
    {x : H} (hx : x ∈ Submodule.span ℝ (Set.range g)) :
    s * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
  rw [← hc, norm_sq_sum_orthonormal hg c,
    quadratic_sum_eigenvectors hg ν hEigen c, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hs i) (sq_nonneg _)

namespace PositiveEigenFamily

variable {T : H →L[ℝ] H} {j : ℕ}

/-- The last successive maximizer bounds every `j`-vector spectral threshold. -/
theorem threshold_le_last (f : PositiveEigenFamily T j) (hj : 0 < j)
    {s : ℝ} (hs : s ∈ SpectralThreshold T j) : s ≤ f.values (j - 1) := by
  classical
  obtain ⟨_, g, hg, ν, hν⟩ := hs
  let W : Submodule ℝ H := Submodule.span ℝ (Set.range g)
  have hWdim : Module.finrank ℝ W = j := by
    dsimp [W]
    rw [finrank_span_eq_card hg.linearIndependent, Fintype.card_fin]
  letI : Module.Finite ℝ W := Module.finite_of_finrank_pos (by
    rw [hWdim]
    exact hj)
  let coordinates : W →ₗ[ℝ] (Fin (j - 1) → ℝ) :=
    { toFun := fun x i => ⟪f.vectors i, (x : H)⟫_ℝ
      map_add' := by
        intro x y
        ext i
        simp [inner_add_right]
      map_smul' := by
        intro c x
        ext i
        simp [inner_smul_right] }
  have hker : LinearMap.ker coordinates ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simp [hWdim]; omega)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hx0' : (x : H) ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hxOrth : ∀ l < j - 1, ⟪f.vectors l, (x : H)⟫_ℝ = 0 := by
    intro l hl
    have hzero := congrFun (LinearMap.mem_ker.mp hx) (⟨l, hl⟩ : Fin (j - 1))
    simpa [coordinates] using hzero
  have hLower : s * ‖(x : H)‖ ^ 2 ≤ ⟪T (x : H), (x : H)⟫_ℝ :=
    quadratic_lower_on_eigenspan hg ν (fun i => (hν i).1) (fun i => (hν i).2) x.property
  have hUpper := f.maximal (j - 1) (by omega) (x : H) hxOrth
  have hNormPos : 0 < ‖(x : H)‖ ^ 2 := by positivity
  exact le_of_mul_le_mul_right (hLower.trans hUpper) hNormPos

theorem last_mem_threshold (f : PositiveEigenFamily T j) (hj : 0 < j) :
    f.values (j - 1) ∈ SpectralThreshold T j := by
  refine ⟨f.positive (j - 1) (by omega),
    (fun i : Fin j => f.vectors i), f.orthonormal,
    (fun i : Fin j => f.values i), ?_⟩
  intro i
  exact ⟨f.eigenvector i i.isLt, f.value_le i.isLt (by omega) (by omega)⟩

theorem last_isGreatest (f : PositiveEigenFamily T j) (hj : 0 < j) :
    IsGreatest (SpectralThreshold T j) (f.values (j - 1)) :=
  ⟨f.last_mem_threshold hj, fun _ hs => f.threshold_le_last hj hs⟩

theorem spectralEigenvalue_eq_last (f : PositiveEigenFamily T j) (hj : 0 < j) :
    spectralEigenvalue T j = f.values (j - 1) :=
  (f.last_isGreatest hj).csSup_eq

/-- Ordered values agree across different choices of a truncation of equal size. -/
theorem last_unique (f g : PositiveEigenFamily T j) (hj : 0 < j) :
    f.values (j - 1) = g.values (j - 1) := by
  rw [← f.spectralEigenvalue_eq_last hj, ← g.spectralEigenvalue_eq_last hj]

theorem spectralEigenvalue_pos (f : PositiveEigenFamily T j) (hj : 0 < j) :
    0 < spectralEigenvalue T j := by
  rw [f.spectralEigenvalue_eq_last hj]
  exact f.positive (j - 1) (by omega)

theorem mem_threshold_iff (f : PositiveEigenFamily T j) (hj : 0 < j) {s : ℝ} :
    s ∈ SpectralThreshold T j ↔ 0 < s ∧ s ≤ spectralEigenvalue T j := by
  rw [f.spectralEigenvalue_eq_last hj]
  constructor
  · intro hs
    exact ⟨hs.1, f.threshold_le_last hj hs⟩
  · rintro ⟨hs0, hsLast⟩
    refine ⟨hs0, (fun i : Fin j => f.vectors i), f.orthonormal,
      (fun i : Fin j => f.values i), ?_⟩
    intro i
    exact ⟨f.eigenvector i i.isLt,
      hsLast.trans (f.value_le i.isLt (by omega) (by omega))⟩

end PositiveEigenFamily

theorem spectralThreshold_antitone {T : H →L[ℝ] H} {j k : ℕ} (hjk : j ≤ k) :
    SpectralThreshold T k ⊆ SpectralThreshold T j := by
  intro s hs
  obtain ⟨hs0, e, he, ν, hν⟩ := hs
  have hInjective : Function.Injective (Fin.castLE hjk) := by
    intro i l h
    exact Fin.ext (congrArg (fun x : Fin k => x.val) h)
  refine ⟨hs0, (fun i : Fin j => e (Fin.castLE hjk i)),
    he.comp (Fin.castLE hjk) hInjective,
    (fun i : Fin j => ν (Fin.castLE hjk i)), ?_⟩
  intro i
  exact hν (Fin.castLE hjk i)

theorem spectralEigenvalue_pos {T : H →L[ℝ] H}
    (hCompact : IsCompactOperator T)
    (hSymmetric : ∀ x y, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ)
    (hPositive : ∀ x : H, x ≠ 0 → 0 < ⟪T x, x⟫_ℝ)
    (hInfinite : ¬ Module.Finite ℝ H) {j : ℕ} (hj : 0 < j) :
    0 < spectralEigenvalue T j := by
  obtain ⟨f⟩ := exists_positive_eigenfamily hCompact hSymmetric hPositive hInfinite j
  exact f.spectralEigenvalue_pos hj

theorem spectralEigenvalue_le_of_index_le {T : H →L[ℝ] H}
    (hCompact : IsCompactOperator T)
    (hSymmetric : ∀ x y, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ)
    (hPositive : ∀ x : H, x ≠ 0 → 0 < ⟪T x, x⟫_ℝ)
    (hInfinite : ¬ Module.Finite ℝ H) {j k : ℕ} (hj : 0 < j) (hjk : j ≤ k) :
    spectralEigenvalue T k ≤ spectralEigenvalue T j := by
  obtain ⟨f⟩ := exists_positive_eigenfamily hCompact hSymmetric hPositive hInfinite j
  obtain ⟨g⟩ := exists_positive_eigenfamily hCompact hSymmetric hPositive hInfinite k
  have hk : 0 < k := hj.trans_le hjk
  have hJBounded : BddAbove (SpectralThreshold T j) :=
    (f.last_isGreatest hj).isLUB.bddAbove
  exact csSup_le_csSup hJBounded (g.last_isGreatest hk).nonempty
    (spectralThreshold_antitone hjk)

theorem exists_eigenvector_at_spectralEigenvalue {T : H →L[ℝ] H}
    (hCompact : IsCompactOperator T)
    (hSymmetric : ∀ x y, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ)
    (hPositive : ∀ x : H, x ≠ 0 → 0 < ⟪T x, x⟫_ℝ)
    (hInfinite : ¬ Module.Finite ℝ H) {j : ℕ} (hj : 0 < j) :
    ∃ x : H, ‖x‖ = 1 ∧ T x = spectralEigenvalue T j • x := by
  obtain ⟨f⟩ := exists_positive_eigenfamily hCompact hSymmetric hPositive hInfinite j
  refine ⟨f.vectors (j - 1), ?_, ?_⟩
  · exact f.orthonormal.norm_eq_one ⟨j - 1, by omega⟩
  · rw [f.spectralEigenvalue_eq_last hj]
    exact f.eigenvector (j - 1) (by omega)

theorem inverseSpectralEigenvalue_pos {T : H →L[ℝ] H}
    (hCompact : IsCompactOperator T)
    (hSymmetric : ∀ x y, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ)
    (hPositive : ∀ x : H, x ≠ 0 → 0 < ⟪T x, x⟫_ℝ)
    (hInfinite : ¬ Module.Finite ℝ H) {j : ℕ} (hj : 0 < j) :
    0 < inverseSpectralEigenvalue T j :=
  ENNReal.ofReal_pos.mpr
    (one_div_pos.mpr (spectralEigenvalue_pos hCompact hSymmetric hPositive hInfinite hj))

theorem inverseSpectralEigenvalue_lt_top (T : H →L[ℝ] H) (j : ℕ) :
    inverseSpectralEigenvalue T j < ⊤ := ENNReal.ofReal_lt_top

theorem inverseSpectralEigenvalue_le_of_index_le {T : H →L[ℝ] H}
    (hCompact : IsCompactOperator T)
    (hSymmetric : ∀ x y, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ)
    (hPositive : ∀ x : H, x ≠ 0 → 0 < ⟪T x, x⟫_ℝ)
    (hInfinite : ¬ Module.Finite ℝ H) {j k : ℕ} (hj : 0 < j) (hjk : j ≤ k) :
    inverseSpectralEigenvalue T j ≤ inverseSpectralEigenvalue T k := by
  apply ENNReal.ofReal_le_ofReal
  exact one_div_le_one_div_of_le
    (spectralEigenvalue_pos hCompact hSymmetric hPositive hInfinite (hj.trans_le hjk))
    (spectralEigenvalue_le_of_index_le hCompact hSymmetric hPositive hInfinite hj hjk)

end PolyaBridge.CompactSpectral

/-!
Association of a coercive energy form with a densely defined operator.
The construction is subsequently applied to the actual Dirichlet gradient form.
-/

noncomputable section

open scoped Topology

namespace PolyaBridge.AbstractForm

open scoped InnerProductSpace

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem adjoint_eq_zero_iff (J : V →L[ℝ] H) (hJdense : DenseRange J) (f : H) :
    ContinuousLinearMap.adjoint J f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    have hd : Dense (J.range : Set H) := hJdense
    apply hd.eq_zero_of_inner_left (𝕜 := ℝ)
    intro y hy
    obtain ⟨v, rfl⟩ := hy
    change ⟪f, J v⟫_ℝ = 0
    rw [← ContinuousLinearMap.adjoint_inner_left J v f, hf, inner_zero_left]
  · rintro rfl
    exact map_zero _

end PolyaBridge.AbstractForm

namespace PolyaBridge.InverseOperator

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- The partial inverse of an everywhere-defined bounded operator. -/
def operator (K : H →L[ℝ] H) : H →ₗ.[ℝ] H :=
  (K.toLinearMap.toPMap ⊤).inverse

omit [CompleteSpace H] in
theorem domain (K : H →L[ℝ] H) : (operator K).domain = K.range := by
  rw [operator, LinearPMap.inverse_domain]
  ext f
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨(v : H), hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨⟨v, Submodule.mem_top⟩, hv⟩

def domainVector (K : H →L[ℝ] H) (f : H) : (operator K).domain :=
  ⟨K f, by rw [domain]; exact ⟨f, rfl⟩⟩

omit [CompleteSpace H] in
@[simp] theorem domainVector_coe (K : H →L[ℝ] H) (f : H) :
    (domainVector K f : H) = K f := rfl

omit [CompleteSpace H] in
theorem partial_ker_eq_bot (K : H →L[ℝ] H) (hKinj : Function.Injective K) :
    (K.toLinearMap.toPMap ⊤).ker = ⊥ := by
  rw [LinearPMap.ker_eq_bot']
  intro f hf
  apply Subtype.ext
  apply hKinj
  change K (f : H) = 0 at hf
  simpa using hf

omit [CompleteSpace H] in
@[simp] theorem apply_vector (K : H →L[ℝ] H) (hKinj : Function.Injective K)
    (f : H) : operator K (domainVector K f) = f := by
  change (K.toLinearMap.toPMap ⊤).inverse ⟨K f, _⟩ = (f : H)
  simpa using (LinearPMap.inverse_apply_eq (f := K.toLinearMap.toPMap ⊤)
    (partial_ker_eq_bot K hKinj) (x := ⟨f, Submodule.mem_top⟩) rfl)

omit [CompleteSpace H] in
theorem inverse_apply (K : H →L[ℝ] H) (hKinj : Function.Injective K)
    (u : (operator K).domain) : K (operator K u) = (u : H) := by
  obtain ⟨f, hf⟩ : ∃ f, K f = (u : H) := by
    have hu := u.property
    simp only [domain] at hu
    exact hu
  have hu : u = domainVector K f := Subtype.ext hf.symm
  rw [hu, apply_vector K hKinj]
  rfl

omit [CompleteSpace H] in
theorem dense_domain (K : H →L[ℝ] H) (hKdense : DenseRange K) :
    Dense ((operator K).domain : Set H) := by
  rw [domain]
  exact hKdense

theorem denseRange_of_symmetric_injective (K : H →L[ℝ] H)
    (hKsym : K.IsSymmetric) (hKinj : Function.Injective K) : DenseRange K := by
  change Dense (K.range : Set H)
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, ContinuousLinearMap.orthogonal_range,
    hKsym.clm_adjoint_eq, LinearMap.ker_eq_bot]
  exact hKinj

omit [CompleteSpace H] in
theorem formalAdjoint (K : H →L[ℝ] H) (hKinj : Function.Injective K)
    (hKsym : K.IsSymmetric) : (operator K).IsFormalAdjoint (operator K) := by
  intro u v
  calc
    ⟪operator K u, (v : H)⟫_ℝ = ⟪operator K u, K (operator K v)⟫_ℝ := by
      rw [inverse_apply K hKinj]
    _ = ⟪K (operator K u), operator K v⟫_ℝ := (hKsym _ _).symm
    _ = ⟪(u : H), operator K v⟫_ℝ := by rw [inverse_apply K hKinj]

theorem inverse_adjoint_apply (K : H →L[ℝ] H) (hKinj : Function.Injective K)
    (hKsym : K.IsSymmetric) (hKdense : DenseRange K)
    (u : (operator K).adjoint.domain) : K ((operator K).adjoint u) = (u : H) := by
  apply ext_inner_right ℝ
  intro f
  calc
    ⟪K ((operator K).adjoint u), f⟫_ℝ = ⟪(operator K).adjoint u, K f⟫_ℝ := hKsym _ _
    _ = ⟪(u : H), f⟫_ℝ := by
      have h := LinearPMap.adjoint_isFormalAdjoint
        (hT := dense_domain K hKdense) u (domainVector K f)
      change ⟪(operator K).adjoint u, K f⟫_ℝ =
        ⟪(u : H), operator K (domainVector K f)⟫_ℝ at h
      rwa [apply_vector K hKinj] at h

theorem selfAdjoint (K : H →L[ℝ] H) (hKinj : Function.Injective K)
    (hKsym : K.IsSymmetric) (hKdense : DenseRange K) : IsSelfAdjoint (operator K) := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · refine ⟨?_, ?_⟩
    · intro f hf
      rw [domain]
      exact ⟨(operator K).adjoint ⟨f, hf⟩,
        inverse_adjoint_apply K hKinj hKsym hKdense ⟨f, hf⟩⟩
    · intro u v huv
      apply hKinj
      calc
        K ((operator K).adjoint u) = (u : H) :=
          inverse_adjoint_apply K hKinj hKsym hKdense u
        _ = (v : H) := huv
        _ = K (operator K v) := (inverse_apply K hKinj v).symm
  · exact LinearPMap.IsFormalAdjoint.le_adjoint (hT := dense_domain K hKdense)
      (formalAdjoint K hKinj hKsym)

theorem closed (K : H →L[ℝ] H) (hKinj : Function.Injective K)
    (hKsym : K.IsSymmetric) (hKdense : DenseRange K) : (operator K).IsClosed :=
  (selfAdjoint K hKinj hKsym hKdense).isClosed

omit [CompleteSpace H] in
theorem nonneg (K : H →L[ℝ] H) (hKinj : Function.Injective K)
    (hKpositive : K.IsPositive) (u : (operator K).domain) :
    0 ≤ ⟪operator K u, (u : H)⟫_ℝ := by
  rw [← inverse_apply K hKinj u]
  exact hKpositive.inner_nonneg_right _

omit [CompleteSpace H] in
theorem eigenvector_mem_domain (K : H →L[ℝ] H) (μ : ℝ) (hμ : μ ≠ 0)
    (f : H) (hf : K f = μ • f) : f ∈ (operator K).domain := by
  rw [domain]
  refine ⟨μ⁻¹ • f, ?_⟩
  change K (μ⁻¹ • f) = f
  rw [map_smul]
  change μ⁻¹ • K f = f
  rw [hf, smul_smul, inv_mul_cancel₀ hμ, one_smul]

omit [CompleteSpace H] in
/-- A nonzero inverse eigenvalue gives an eigenvalue of the actual partial
operator on its genuine domain. -/
theorem eigenvector_apply (K : H →L[ℝ] H) (hKinj : Function.Injective K)
    (μ : ℝ) (hμ : μ ≠ 0) (f : H) (hf : K f = μ • f) :
    operator K ⟨f, eigenvector_mem_domain K μ hμ f hf⟩ = μ⁻¹ • f := by
  have hv : (⟨f, eigenvector_mem_domain K μ hμ f hf⟩ : (operator K).domain) =
      domainVector K (μ⁻¹ • f) := by
    apply Subtype.ext
    change f = K (μ⁻¹ • f)
    rw [map_smul]
    change f = μ⁻¹ • K f
    rw [hf, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  rw [hv]
  exact apply_vector K hKinj _

omit [CompleteSpace H] in
/-- Conversely every nonzero eigenvalue of the partial operator gives its
reciprocal as an eigenvalue of the bounded inverse. -/
theorem inverse_eigen_of_operator_eigen (K : H →L[ℝ] H)
    (hKinj : Function.Injective K) (lam : ℝ) (hlam : lam ≠ 0)
    (u : (operator K).domain) (hu : operator K u = lam • (u : H)) :
    K (u : H) = lam⁻¹ • (u : H) := by
  have h := inverse_apply K hKinj u
  rw [hu, map_smul] at h
  have h' := congrArg (fun x : H => lam⁻¹ • x) h
  simpa only [smul_smul, inv_mul_cancel₀ hlam, one_smul] using h'

end PolyaBridge.InverseOperator

namespace PolyaBridge.CoerciveForm

open scoped InnerProductSpace

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Lax–Milgram solution for a bounded coercive form on the form domain `V`.
The Hilbert inner product of `V` need not equal the form `B`. -/
def solution (J : V →L[ℝ] H) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) : H →L[ℝ] V :=
  hB.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.adjoint J)

theorem riesz_solution (J : V →L[ℝ] H) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (f : H) :
    hB.continuousLinearEquivOfBilin (solution J B hB f) =
      ContinuousLinearMap.adjoint J f := by
  exact hB.continuousLinearEquivOfBilin.apply_symm_apply _

theorem solution_form (J : V →L[ℝ] H) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (f : H) (v : V) :
    B (solution J B hB f) v = ⟪f, J v⟫_ℝ := by
  rw [← hB.continuousLinearEquivOfBilin_apply, riesz_solution]
  exact ContinuousLinearMap.adjoint_inner_left J v f

theorem form_equation_iff (J : V →L[ℝ] H) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (u : V) (f : H) :
    (∀ v : V, B u v = ⟪f, J v⟫_ℝ) ↔ u = solution J B hB f := by
  constructor
  · intro hu
    apply hB.continuousLinearEquivOfBilin.injective
    apply ext_inner_right ℝ
    intro v
    rw [hB.continuousLinearEquivOfBilin_apply,
      hB.continuousLinearEquivOfBilin_apply]
    exact (hu v).trans (solution_form J B hB f v).symm
  · rintro rfl
    exact solution_form J B hB f

/-- The bounded inverse obtained from the actual form, rather than the ambient
Hilbert inner product of the form domain. -/
def formInverse (J : V →L[ℝ] H) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) : H →L[ℝ] H :=
  J.comp (solution J B hB)

@[simp] theorem formInverse_apply (J : V →L[ℝ] H) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (f : H) :
    formInverse J B hB f = J (solution J B hB f) := rfl

theorem formInverse_inner (J : V →L[ℝ] H) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (f g : H) :
    ⟪formInverse J B hB f, g⟫_ℝ = B (solution J B hB g) (solution J B hB f) := by
  rw [solution_form, formInverse_apply, real_inner_comm]

theorem formInverse_symmetric (J : V →L[ℝ] H) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (hBsym : ∀ u v, B u v = B v u) :
    (formInverse J B hB).IsSymmetric := by
  intro f g
  calc
    ⟪formInverse J B hB f, g⟫_ℝ =
        B (solution J B hB g) (solution J B hB f) := formInverse_inner J B hB f g
    _ = B (solution J B hB f) (solution J B hB g) := hBsym _ _
    _ = ⟪f, formInverse J B hB g⟫_ℝ := solution_form J B hB f _

omit [CompleteSpace V] in
theorem form_self_nonneg (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (u : V) : 0 ≤ B u u := by
  obtain ⟨c, hc, hbound⟩ := hB
  exact le_trans (by positivity : 0 ≤ c * ‖u‖ * ‖u‖) (hbound u)

omit [CompleteSpace V] in
theorem form_self_pos (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (u : V) (hu : u ≠ 0) : 0 < B u u := by
  obtain ⟨c, hc, hbound⟩ := hB
  exact lt_of_lt_of_le (by positivity : 0 < c * ‖u‖ * ‖u‖) (hbound u)

omit [CompleteSpace V] in
/-- Coercivity makes a form-Cauchy sequence Cauchy in the given Hilbert topology. -/
theorem cauchySeq_of_formCauchy (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (u : ℕ → V)
    (hu : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      B (u m - u n) (u m - u n) < ε) : CauchySeq u := by
  obtain ⟨c, hc, hbound⟩ := hB
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := hu (c * ε ^ 2) (mul_pos hc (sq_pos_of_pos hε))
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [dist_eq_norm]
  have hlt : c * ‖u m - u n‖ ^ 2 < c * ε ^ 2 := by
    calc
      c * ‖u m - u n‖ ^ 2 = c * ‖u m - u n‖ * ‖u m - u n‖ := by ring
      _ ≤ B (u m - u n) (u m - u n) := hbound _
      _ < c * ε ^ 2 := hN m hm n hn
  have hs := (mul_lt_mul_iff_right₀ hc).mp hlt
  nlinarith [norm_nonneg (u m - u n)]

omit [CompleteSpace H] in
/-- The sequential closed-form criterion: an L² limit of a form-Cauchy sequence
belongs to the form domain, and convergence also holds in form energy. -/
theorem form_complete (J : V →L[ℝ] H) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (u : ℕ → V) (f : H)
    (huf : Filter.Tendsto (fun n => J (u n)) Filter.atTop (𝓝 f))
    (hu : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      B (u m - u n) (u m - u n) < ε) :
    ∃ v : V, J v = f ∧
      Filter.Tendsto (fun n => B (u n - v) (u n - v)) Filter.atTop (𝓝 0) := by
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_formCauchy B hB u hu)
  refine ⟨v, ?_, ?_⟩
  · exact tendsto_nhds_unique (J.continuous.continuousAt.tendsto.comp hv) huf
  · have hd : Filter.Tendsto (fun n => u n - v) Filter.atTop (𝓝 (0 : V)) := by
      simpa using hv.sub
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => v) Filter.atTop (𝓝 v))
    have hq := B.continuous₂.continuousAt.tendsto.comp (hd.prodMk_nhds hd)
    change Filter.Tendsto (fun n => B (u n - v) (u n - v)) Filter.atTop
      (𝓝 (B (0 : V) 0)) at hq
    simpa only [map_zero, ContinuousLinearMap.zero_apply] using hq

theorem formInverse_positive (J : V →L[ℝ] H) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (hBsym : ∀ u v, B u v = B v u) :
    (formInverse J B hB).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff]
  refine ⟨formInverse_symmetric J B hB hBsym, ?_⟩
  intro f
  rw [formInverse_inner]
  exact form_self_nonneg B hB _

theorem solution_eq_zero_iff (J : V →L[ℝ] H) (hJdense : DenseRange J)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (f : H) :
    solution J B hB f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    apply (AbstractForm.adjoint_eq_zero_iff J hJdense f).mp
    rw [← riesz_solution J B hB f, hf, map_zero]
  · rintro rfl
    exact map_zero _

theorem formInverse_strictPositive (J : V →L[ℝ] H) (hJdense : DenseRange J)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (f : H) (hf : f ≠ 0) : 0 < ⟪formInverse J B hB f, f⟫_ℝ := by
  rw [formInverse_inner]
  apply form_self_pos B hB
  intro h
  exact hf ((solution_eq_zero_iff J hJdense B hB f).mp h)

theorem formInverse_injective (J : V →L[ℝ] H) (hJdense : DenseRange J)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) :
    Function.Injective (formInverse J B hB) := by
  change Function.Injective (formInverse J B hB).toLinearMap
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  change formInverse J B hB f = 0 at hf
  by_contra h
  have hp := formInverse_strictPositive J hJdense B hB f h
  rw [hf, inner_zero_left] at hp
  exact (lt_irrefl 0) hp

theorem formInverse_denseRange (J : V →L[ℝ] H) (hJdense : DenseRange J)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (hBsym : ∀ u v, B u v = B v u) : DenseRange (formInverse J B hB) :=
  InverseOperator.denseRange_of_symmetric_injective _
    (formInverse_symmetric J B hB hBsym) (formInverse_injective J hJdense B hB)

theorem formInverse_compact (J : V →L[ℝ] H) (hJcompact : IsCompactOperator J)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) :
    IsCompactOperator (formInverse J B hB) :=
  hJcompact.comp_clm (solution J B hB)

/-- The operator associated with a bounded coercive form on `V`. Its inverse
is the Lax–Milgram solution transported to `H` by the embedding `J`. -/
def associatedOperator (J : V →L[ℝ] H) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) : H →ₗ.[ℝ] H :=
  InverseOperator.operator (formInverse J B hB)

theorem form_representation (J : V →L[ℝ] H) (hJdense : DenseRange J)
    (hJinj : Function.Injective J) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (u : V) (f : H) :
    (∃ hu : J u ∈ (associatedOperator J B hB).domain,
      associatedOperator J B hB ⟨J u, hu⟩ = f) ↔
      ∀ v : V, B u v = ⟪f, J v⟫_ℝ := by
  rw [form_equation_iff]
  constructor
  · rintro ⟨hu, huf⟩
    have hJu := InverseOperator.inverse_apply (formInverse J B hB)
      (formInverse_injective J hJdense B hB) ⟨J u, hu⟩
    change formInverse J B hB (associatedOperator J B hB ⟨J u, hu⟩) = J u at hJu
    rw [huf] at hJu
    exact hJinj hJu.symm
  · intro hu
    have hJu : J u = formInverse J B hB f := by rw [hu]; rfl
    have hm : J u ∈ (associatedOperator J B hB).domain := by
      rw [associatedOperator, InverseOperator.domain]
      exact ⟨f, hJu.symm⟩
    refine ⟨hm, ?_⟩
    have hv : (⟨J u, hm⟩ : (associatedOperator J B hB).domain) =
        InverseOperator.domainVector (formInverse J B hB) f := Subtype.ext hJu
    rw [hv]
    exact InverseOperator.apply_vector (formInverse J B hB)
      (formInverse_injective J hJdense B hB) f

theorem associatedOperator_nonneg (J : V →L[ℝ] H) (hJdense : DenseRange J)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (hBsym : ∀ u v, B u v = B v u) (u : (associatedOperator J B hB).domain) :
    0 ≤ ⟪associatedOperator J B hB u, (u : H)⟫_ℝ :=
  InverseOperator.nonneg (formInverse J B hB) (formInverse_injective J hJdense B hB)
    (formInverse_positive J B hB hBsym) u

theorem associatedOperator_selfAdjoint (J : V →L[ℝ] H) (hJdense : DenseRange J)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (hBsym : ∀ u v, B u v = B v u) : IsSelfAdjoint (associatedOperator J B hB) :=
  InverseOperator.selfAdjoint _ (formInverse_injective J hJdense B hB)
    (formInverse_symmetric J B hB hBsym) (formInverse_denseRange J hJdense B hB hBsym)

theorem associatedOperator_closed (J : V →L[ℝ] H) (hJdense : DenseRange J)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (hBsym : ∀ u v, B u v = B v u) : (associatedOperator J B hB).IsClosed :=
  (associatedOperator_selfAdjoint J hJdense B hB hBsym).isClosed

/-- Operator eigenvectors are precisely solutions of the weak eigen-equation.
This statement uses the actual form `B`, including when `V` has the H¹ norm. -/
theorem eigenvector_iff_weak_equation (J : V →L[ℝ] H) (hJdense : DenseRange J)
    (hJinj : Function.Injective J) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (u : V) (lam : ℝ) :
    (∃ hu : J u ∈ (associatedOperator J B hB).domain,
      associatedOperator J B hB ⟨J u, hu⟩ = lam • J u) ↔
      ∀ v : V, B u v = lam * ⟪J u, J v⟫_ℝ := by
  rw [form_representation J hJdense hJinj B hB u (lam • J u)]
  simp only [real_inner_smul_left]

end PolyaBridge.CoerciveForm

namespace PolyaBridge.CoreMinmax

open Set Filter Topology
open scoped InnerProductSpace

variable {V H : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Density holds simultaneously for every entry of a finite family. -/
theorem dense_core_families (S : Submodule ℝ V) (hS : Dense (S : Set V)) (n : ℕ) :
    Dense (Set.pi (Set.univ : Set (Fin n)) (fun _ => (S : Set V))) :=
  dense_pi Set.univ (fun _ _ => hS)

/-- Linear synthesis from finite coefficient vectors. -/
def synthesis {n : ℕ} (u : Fin n → V) : (Fin n → ℝ) →ₗ[ℝ] V :=
  Fintype.linearCombination ℝ u

@[simp] theorem synthesis_apply {n : ℕ} (u : Fin n → V) (c : Fin n → ℝ) :
    synthesis u c = ∑ i, c i • u i :=
  rfl

theorem synthesis_injective {n : ℕ} {u : Fin n → V} (hu : LinearIndependent ℝ u) :
    Function.Injective (synthesis u) :=
  hu.fintypeLinearCombination_injective

/-! The following interface keeps the energy form separate from the ambient
Hilbert norm. In particular, the `H¹` norm is not substituted for Dirichlet energy. -/

def formRayleigh (B : V →L[ℝ] V →L[ℝ] ℝ) (J : V →L[ℝ] H) (v : V) : ENNReal :=
  ENNReal.ofReal (B v v) / ENNReal.ofReal (‖J v‖ ^ 2)

def formMinmaxOn (B : V →L[ℝ] V →L[ℝ] ℝ) (J : V →L[ℝ] H)
    (S : Submodule ℝ V) (j : ℕ) : ENNReal :=
  ⨅ (W : Submodule ℝ V) (_ : W ≤ S) (_ : Module.finrank ℝ W = j),
    ⨆ (v : V) (_ : v ∈ W) (_ : v ≠ 0), formRayleigh B J v

theorem form_diagonal_smul (B : V →L[ℝ] V →L[ℝ] ℝ) (r : ℝ) (v : V) :
    B (r • v) (r • v) = r ^ 2 * B v v := by
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Gram approximation for the actual energy form, independently of the norm on `V`. -/
theorem exists_core_form_gram_approx (B : V →L[ℝ] V →L[ℝ] ℝ)
    (J : V →L[ℝ] H) (S : Submodule ℝ V) (hS : Dense (S : Set V))
    {n : ℕ} (u : Fin n → V) (hu : LinearIndependent ℝ u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : Fin n → V, (∀ i, v i ∈ S) ∧ LinearIndependent ℝ v ∧
      (∀ i l, |B (v i) (v l) - B (u i) (u l)| < ε) ∧
      (∀ i l, |⟪J (v i), J (v l)⟫_ℝ - ⟪J (u i), J (u l)⟫_ℝ| < ε) := by
  classical
  have hEnergy : ∀ᶠ v : Fin n → V in 𝓝 u,
      ∀ i l, |B (v i) (v l) - B (u i) (u l)| < ε := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro l
    have hc : Continuous (fun v : Fin n → V =>
        |B (v i) (v l) - B (u i) (u l)|) := by fun_prop
    exact hc.continuousAt.eventually (gt_mem_nhds (by simpa using hε))
  have hMass : ∀ᶠ v : Fin n → V in 𝓝 u,
      ∀ i l, |⟪J (v i), J (v l)⟫_ℝ - ⟪J (u i), J (u l)⟫_ℝ| < ε := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro l
    have hc : Continuous (fun v : Fin n → V =>
        |⟪J (v i), J (v l)⟫_ℝ - ⟪J (u i), J (u l)⟫_ℝ|) := by fun_prop
    exact hc.continuousAt.eventually (gt_mem_nhds (by simpa using hε))
  obtain ⟨v, hvS, hv⟩ := (dense_core_families S hS n).inter_nhds_nonempty
    (hu.eventually.and (hEnergy.and hMass))
  exact ⟨v, (fun i => hvS i (Set.mem_univ i)), hv.1, hv.2.1, hv.2.2⟩

theorem eventually_trial_form_bound (B : V →L[ℝ] V →L[ℝ] ℝ)
    (J : V →L[ℝ] H) (hJ : Function.Injective J) {n : ℕ}
    (u : Fin n → V) (hu : LinearIndependent ℝ u) {A C : ℝ} (hAC : A < C)
    (hA : ∀ c : Fin n → ℝ,
      B (synthesis u c) (synthesis u c) ≤ A * ‖J (synthesis u c)‖ ^ 2) :
    ∀ᶠ v : Fin n → V in 𝓝 u, ∀ c : Fin n → ℝ,
      B (synthesis v c) (synthesis v c) ≤ C * ‖J (synthesis v c)‖ ^ 2 := by
  classical
  have hSphere : ∀ᶠ v : Fin n → V in 𝓝 u,
      ∀ c ∈ Metric.sphere (0 : Fin n → ℝ) 1,
        B (synthesis v c) (synthesis v c) < C * ‖J (synthesis v c)‖ ^ 2 := by
    apply (isCompact_sphere (0 : Fin n → ℝ) 1).eventually_forall_of_forall_eventually
    intro c hc
    have hcNorm : ‖c‖ = 1 := by simpa using hc
    have hc0 : c ≠ 0 := by
      intro hc0
      simp [hc0] at hcNorm
    have huc0 : synthesis u c ≠ 0 := by
      intro hz
      exact hc0 ((synthesis_injective hu) (by simpa using hz))
    have hJuc0 : J (synthesis u c) ≠ 0 := by
      intro hz
      exact huc0 (hJ (by simpa using hz))
    have hMassPos : 0 < ‖J (synthesis u c)‖ ^ 2 := by positivity
    have hStrict : B (synthesis u c) (synthesis u c) <
        C * ‖J (synthesis u c)‖ ^ 2 :=
      (hA c).trans_lt (mul_lt_mul_of_pos_right hAC hMassPos)
    have hEnergyCont : Continuous (fun p : (Fin n → V) × (Fin n → ℝ) =>
        B (synthesis p.1 p.2) (synthesis p.1 p.2)) := by
      simp only [synthesis_apply]
      fun_prop
    have hMassCont : Continuous (fun p : (Fin n → V) × (Fin n → ℝ) =>
        C * ‖J (synthesis p.1 p.2)‖ ^ 2) := by
      simp only [synthesis_apply]
      fun_prop
    exact (isOpen_lt hEnergyCont hMassCont).mem_nhds hStrict
  filter_upwards [hSphere] with v hv c
  by_cases hc0 : c = 0
  · simp [hc0]
  have hcPos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  let d : Fin n → ℝ := ‖c‖⁻¹ • c
  have hdSphere : d ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
    rw [Metric.mem_sphere, dist_zero_right]
    simp only [d, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ hcPos.ne']
  have hd := hv d hdSphere
  have hSynth : synthesis v d = ‖c‖⁻¹ • synthesis v c := by
    exact (synthesis v).map_smul ‖c‖⁻¹ c
  rw [hSynth, form_diagonal_smul, J.map_smul] at hd
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, mul_pow] at hd
  have hd' : (‖c‖⁻¹) ^ 2 * B (synthesis v c) (synthesis v c) <
      (‖c‖⁻¹) ^ 2 * (C * ‖J (synthesis v c)‖ ^ 2) := by
    simpa only [mul_assoc, mul_left_comm] using hd
  exact ((mul_lt_mul_iff_right₀ (by positivity : 0 < (‖c‖⁻¹) ^ 2)).mp hd').le

theorem formRayleigh_le_of_energy_bound (B : V →L[ℝ] V →L[ℝ] ℝ)
    (J : V →L[ℝ] H) {v : V} {C : ℝ} (hC : 0 ≤ C)
    (hBound : B v v ≤ C * ‖J v‖ ^ 2) :
    formRayleigh B J v ≤ ENNReal.ofReal C := by
  apply ENNReal.div_le_of_le_mul
  rw [← ENNReal.ofReal_mul hC]
  exact ENNReal.ofReal_le_ofReal hBound

theorem exists_core_trial_form_rayleigh_bound (B : V →L[ℝ] V →L[ℝ] ℝ)
    (J : V →L[ℝ] H) (hJ : Function.Injective J)
    (S : Submodule ℝ V) (hS : Dense (S : Set V))
    {n : ℕ} (u : Fin n → V) (hu : LinearIndependent ℝ u)
    {A C : ℝ} (hAC : A < C) (hC : 0 ≤ C)
    (hA : ∀ c : Fin n → ℝ,
      B (synthesis u c) (synthesis u c) ≤ A * ‖J (synthesis u c)‖ ^ 2) :
    ∃ W : Submodule ℝ V, W ≤ S ∧ Module.finrank ℝ W = n ∧
      ∀ x ∈ W, formRayleigh B J x ≤ ENNReal.ofReal C := by
  have hBound := eventually_trial_form_bound B J hJ u hu hAC hA
  obtain ⟨v, hvS, hv⟩ := (dense_core_families S hS n).inter_nhds_nonempty
    (hu.eventually.and hBound)
  refine ⟨Submodule.span ℝ (Set.range v), ?_, ?_, ?_⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hvS i (Set.mem_univ i)
  · rw [finrank_span_eq_card hv.1, Fintype.card_fin]
  · intro x hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
    apply formRayleigh_le_of_energy_bound B J hC
    have hxc : synthesis v c = x := by simpa only [synthesis_apply] using hc
    simpa only [hxc] using hv.2 c

theorem core_formMinmax_le_of_trial_energy_bound (B : V →L[ℝ] V →L[ℝ] ℝ)
    (J : V →L[ℝ] H) (hJ : Function.Injective J)
    (S : Submodule ℝ V) (hS : Dense (S : Set V))
    {n : ℕ} (u : Fin n → V) (hu : LinearIndependent ℝ u)
    {A C : ℝ} (hAC : A < C) (hC : 0 ≤ C)
    (hA : ∀ c : Fin n → ℝ,
      B (synthesis u c) (synthesis u c) ≤ A * ‖J (synthesis u c)‖ ^ 2) :
    formMinmaxOn B J S n ≤ ENNReal.ofReal C := by
  obtain ⟨W, hWS, hWdim, hWBound⟩ :=
    exists_core_trial_form_rayleigh_bound B J hJ S hS u hu hAC hC hA
  calc
    formMinmaxOn B J S n ≤
        ⨆ (x : V) (_ : x ∈ W) (_ : x ≠ 0), formRayleigh B J x :=
      iInf_le_of_le W (iInf_le_of_le hWS (iInf_le_of_le hWdim le_rfl))
    _ ≤ ENNReal.ofReal C :=
      iSup_le fun x => iSup_le fun hx => iSup_le fun _ => hWBound x hx

/-- Supremum of the Rayleigh quotient on a fixed trial space. -/
def formTrialSup (B : V →L[ℝ] V →L[ℝ] ℝ) (J : V →L[ℝ] H)
    (W : Submodule ℝ V) : ENNReal :=
  ⨆ (v : V) (_ : v ∈ W) (_ : v ≠ 0), formRayleigh B J v

theorem form_energy_bound_of_rayleigh_le (B : V →L[ℝ] V →L[ℝ] ℝ)
    (J : V →L[ℝ] H) (hJ : Function.Injective J) {v : V} {A : ℝ}
    (hA : 0 ≤ A) (hRayleigh : formRayleigh B J v ≤ ENNReal.ofReal A) :
    B v v ≤ A * ‖J v‖ ^ 2 := by
  by_cases hv0 : v = 0
  · simp [hv0]
  have hJv0 : J v ≠ 0 := by
    intro hz
    exact hv0 (hJ (by simpa using hz))
  have hMassPos : 0 < ‖J v‖ ^ 2 := by positivity
  have hMass0 : ENNReal.ofReal (‖J v‖ ^ 2) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hMassPos)
  have hMassTop : ENNReal.ofReal (‖J v‖ ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hEnergy : ENNReal.ofReal (B v v) ≤
      ENNReal.ofReal A * ENNReal.ofReal (‖J v‖ ^ 2) :=
    (ENNReal.div_le_iff hMass0 hMassTop).mp hRayleigh
  rw [← ENNReal.ofReal_mul hA] at hEnergy
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA (sq_nonneg _))).mp hEnergy

/-- The core min-max is bounded by the Rayleigh supremum of any finite-dimensional
trial space. The finite bound case is obtained by approximation and order density;
an infinite trial supremum needs no approximation. -/
theorem core_formMinmax_le_trialSup (B : V →L[ℝ] V →L[ℝ] ℝ)
    (J : V →L[ℝ] H) (hJ : Function.Injective J)
    (S : Submodule ℝ V) (hS : Dense (S : Set V))
    {j : ℕ} (hj : 0 < j) (W : Submodule ℝ V) (hWdim : Module.finrank ℝ W = j) :
    formMinmaxOn B J S j ≤ formTrialSup B J W := by
  classical
  by_cases hTop : formTrialSup B J W = ⊤
  · rw [hTop]
    exact le_top
  letI : Module.Finite ℝ W := Module.finite_of_finrank_pos (by
    rw [hWdim]
    exact hj)
  let b := Module.finBasisOfFinrankEq ℝ W hWdim
  let u : Fin j → V := fun i => (b i : V)
  have hu : LinearIndependent ℝ u := by
    exact b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hMem : ∀ c : Fin j → ℝ, synthesis u c ∈ W := by
    intro c
    rw [synthesis_apply]
    exact W.sum_mem fun i _ => W.smul_mem (c i) (b i).property
  have hRayleigh : ∀ c : Fin j → ℝ,
      formRayleigh B J (synthesis u c) ≤ formTrialSup B J W := by
    intro c
    by_cases hc0 : synthesis u c = 0
    · simp [hc0, formRayleigh]
    · exact le_iSup_of_le (synthesis u c)
        (le_iSup_of_le (hMem c) (le_iSup_of_le hc0 le_rfl))
  have hA : ∀ c : Fin j → ℝ,
      B (synthesis u c) (synthesis u c) ≤
        (formTrialSup B J W).toReal * ‖J (synthesis u c)‖ ^ 2 := by
    intro c
    apply form_energy_bound_of_rayleigh_le B J hJ ENNReal.toReal_nonneg
    simpa only [ENNReal.ofReal_toReal hTop] using hRayleigh c
  apply le_of_forall_gt_imp_ge_of_dense
  intro C hC
  by_cases hCTop : C = ⊤
  · rw [hCTop]
    exact le_top
  have hAC : (formTrialSup B J W).toReal < C.toReal :=
    (ENNReal.toReal_lt_toReal hTop hCTop).mpr hC
  have hBound := core_formMinmax_le_of_trial_energy_bound B J hJ S hS u hu
    hAC ENNReal.toReal_nonneg hA
  simpa only [ENNReal.ofReal_toReal hCTop] using hBound

/-- A dense form core has exactly the same positive-index min-max values as the
whole form domain. The energy remains the supplied continuous bilinear form. -/
theorem formMinmaxOn_eq_top_of_dense (B : V →L[ℝ] V →L[ℝ] ℝ)
    (J : V →L[ℝ] H) (hJ : Function.Injective J)
    (S : Submodule ℝ V) (hS : Dense (S : Set V)) {j : ℕ} (hj : 0 < j) :
    formMinmaxOn B J S j = formMinmaxOn B J ⊤ j := by
  apply le_antisymm
  · unfold formMinmaxOn
    refine le_iInf fun W => le_iInf fun _ => le_iInf fun hWdim => ?_
    exact core_formMinmax_le_trialSup B J hJ S hS hj W hWdim
  · unfold formMinmaxOn
    refine le_iInf fun W => le_iInf fun _ => le_iInf fun hWdim => ?_
    exact iInf_le_of_le W
      (iInf_le_of_le (le_top : W ≤ ⊤) (iInf_le_of_le hWdim le_rfl))

end PolyaBridge.CoreMinmax

/-! Transport of the original smooth-core min-max to the actual Sobolev graph
closure. -/

noncomputable section

namespace DirichletBridge.MinmaxTransport

variable {U W : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup W] [Module ℝ W]

def minmax (S : Submodule ℝ U) (R : U → ENNReal) (j : ℕ) : ENNReal :=
  ⨅ (V : Submodule ℝ U) (_ : V ≤ S) (_ : Module.finrank ℝ V = j),
    ⨆ (u : U) (_ : u ∈ V) (_ : u ≠ 0), R u

theorem le_of_map {S : Submodule ℝ U} {T : Submodule ℝ W}
    {R : U → ENNReal} {Q : W → ENNReal} (P : U →ₗ[ℝ] W)
    (hPT : ∀ u ∈ S, P u ∈ T)
    (hinj : ∀ u ∈ S, P u = 0 → u = 0)
    (hR : ∀ u ∈ S, u ≠ 0 → Q (P u) ≤ R u) (j : ℕ) :
    minmax T Q j ≤ minmax S R j := by
  classical
  unfold minmax
  refine le_iInf fun V => le_iInf fun hV => le_iInf fun hj => ?_
  have hinjV : Function.Injective (P.domRestrict V) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact Subtype.ext (hinj x (hV x.property) (by simpa using hx))
  let Z := LinearMap.range (P.domRestrict V)
  have hZdim : Module.finrank ℝ Z = j := by
    rw [LinearMap.finrank_range_of_inj hinjV, hj]
  have hZT : Z ≤ T := by
    rintro _ ⟨x, rfl⟩
    exact hPT x (hV x.property)
  apply (iInf_le_of_le Z (iInf_le_of_le hZT (iInf_le_of_le hZdim le_rfl))).trans
  refine iSup_le fun v => iSup_le fun hv => iSup_le fun hv0 => ?_
  obtain ⟨x, rfl⟩ := hv
  have hx0 : (x : U) ≠ 0 := by
    rintro h
    apply hv0
    simp [h]
  exact (hR x (hV x.property) hx0).trans
    (le_iSup_of_le (x : U) (le_iSup_of_le x.property (le_iSup_of_le hx0 le_rfl)))

theorem eq_range_of_injective (P : U →ₗ[ℝ] W) (hP : Function.Injective P)
    (R : U → ENNReal) (Q : W → ENNReal) (hR : ∀ u, Q (P u) = R u) (j : ℕ) :
    minmax P.range Q j = minmax ⊤ R j := by
  obtain ⟨L, hL⟩ := P.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hP)
  have hLP : ∀ u, L (P u) = u := by
    intro u
    exact congrArg (fun f : U →ₗ[ℝ] U => f u) hL
  apply le_antisymm
  · exact le_of_map (S := ⊤) (T := P.range) P (fun u _ => ⟨u, rfl⟩)
      (fun u _ hu => hP (by simpa using hu)) (fun u _ _ => (hR u).le) j
  · apply le_of_map (S := P.range) (T := ⊤) L (fun _ _ => Submodule.mem_top)
    · rintro v ⟨u, rfl⟩ hu
      rw [hLP] at hu
      rw [hu, map_zero]
    · rintro v ⟨u, rfl⟩ _
      rw [hLP, hR]

end DirichletBridge.MinmaxTransport

namespace DirichletBridge

open MeasureTheory Set
open scoped InnerProductSpace

lemma coreValue_eq_zero_imp (Ω : Set ℂ) (u : SmoothCore Ω)
    (hu : coreValue Ω u = 0) : (u : ℂ → ℝ) = 0 := by
  by_contra h
  have hpos := l2NormSq_pos_of_ne_zero u.property.1.continuous h
  rw [l2NormSq_core, hu, norm_zero, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero] at hpos
  exact lt_irrefl 0 hpos

lemma coreToH01_injective (Ω : Set ℂ) : Function.Injective (coreToH01 Ω) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  apply Subtype.ext
  apply coreValue_eq_zero_imp Ω u
  have h := congrArg (value Ω) hu
  simpa using h

def sobolevEigenvalue (Ω : Set ℂ) (j : ℕ) : ENNReal :=
  PolyaBridge.CoreMinmax.formMinmaxOn (energyForm Ω) (value Ω) ⊤ j

/-- On the smooth core the actual gradient form has exactly the original
Rayleigh quotient, with no added L² term and no change of normalization. -/
lemma formRayleigh_coreToH01 (Ω : Set ℂ) (u : SmoothCore Ω) :
    PolyaBridge.CoreMinmax.formRayleigh (energyForm Ω) (value Ω) (coreToH01 Ω u) =
      rayleigh (u : ℂ → ℝ) := by
  rw [PolyaBridge.CoreMinmax.formRayleigh, energyForm_self, energy,
    gradient_coreToH01, gradient_coreToH01, value_coreToH01, rayleigh,
    l2NormSq_core, dirichletEnergy_core]
  rfl

/-- The smooth compact-support min-max is the min-max of the genuine H₀¹ form
domain. This equality by itself does not yet identify the form values with the
operator's ordered spectral eigenvalues. -/
theorem dirichletEigenvalue_eq_sobolevEigenvalue (Ω : Set ℂ) {j : ℕ} (hj : 1 ≤ j) :
    dirichletEigenvalue Ω j = sobolevEigenvalue Ω j := by
  have hSubtype := MinmaxTransport.eq_range_of_injective (testFunctions Ω).subtype
    Subtype.val_injective (fun u : SmoothCore Ω => rayleigh (u : ℂ → ℝ))
    rayleigh (fun _ => rfl) j
  have hCore := MinmaxTransport.eq_range_of_injective (coreToH01 Ω)
    (coreToH01_injective Ω) (fun u : SmoothCore Ω => rayleigh (u : ℂ → ℝ))
    (PolyaBridge.CoreMinmax.formRayleigh (energyForm Ω) (value Ω))
    (formRayleigh_coreToH01 Ω) j
  have hRange : ((coreToH01 Ω).range : Set (H01 Ω)) = Set.range (coreToH01 Ω) := rfl
  have hDense : Dense ((coreToH01 Ω).range : Set (H01 Ω)) := by
    rw [hRange]
    exact coreToH01_dense Ω
  have hDenseEq := PolyaBridge.CoreMinmax.formMinmaxOn_eq_top_of_dense
    (energyForm Ω) (value Ω) (value_injective Ω) (coreToH01 Ω).range hDense
    (Nat.lt_of_lt_of_le Nat.zero_lt_one hj)
  have hSource : MinmaxTransport.minmax (testFunctions Ω).subtype.range rayleigh j =
      dirichletEigenvalue Ω j := by
    rw [Submodule.range_subtype]
    rfl
  rw [hSource] at hSubtype
  change dirichletEigenvalue Ω j =
    MinmaxTransport.minmax ⊤
      (PolyaBridge.CoreMinmax.formRayleigh (energyForm Ω) (value Ω)) j
  rw [hSubtype, ← hCore]
  exact hDenseEq

end DirichletBridge

/-! The real Dirichlet operator constructed from the genuine H₀¹ gradient form.
-/

noncomputable section

namespace DirichletBridge

open scoped InnerProductSpace

def dirichletResolventZero (Ω : Set ℂ) (hbdd : Bornology.IsBounded Ω) :
    DomainL2 Ω →L[ℝ] DomainL2 Ω :=
  PolyaBridge.CoerciveForm.formInverse (inclusion Ω) (energyForm Ω)
    (energyForm_coercive Ω hbdd)

def dirichletOperator (Ω : Set ℂ) (hbdd : Bornology.IsBounded Ω) :
    DomainL2 Ω →ₗ.[ℝ] DomainL2 Ω :=
  PolyaBridge.CoerciveForm.associatedOperator (inclusion Ω) (energyForm Ω)
    (energyForm_coercive Ω hbdd)

/-- The actual defining weak equation of the Dirichlet operator, on its genuine
domain. No spectral or min-max equality is an assumption of this result. -/
theorem dirichletOperator_form_representation (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (u : H01 Ω) (f : DomainL2 Ω) :
    (∃ hu : inclusion Ω u ∈ (dirichletOperator Ω hbdd).domain,
      dirichletOperator Ω hbdd ⟨inclusion Ω u, hu⟩ = f) ↔
      ∀ v : H01 Ω, energyForm Ω u v = ⟪f, inclusion Ω v⟫_ℝ :=
  PolyaBridge.CoerciveForm.form_representation (inclusion Ω) (inclusion_dense Ω hopen)
    (inclusion_injective Ω hopen.measurableSet) (energyForm Ω) (energyForm_coercive Ω hbdd)
    u f

theorem dirichletResolventZero_strictPositive (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (f : DomainL2 Ω) (hf : f ≠ 0) :
    0 < ⟪dirichletResolventZero Ω hbdd f, f⟫_ℝ :=
  PolyaBridge.CoerciveForm.formInverse_strictPositive (inclusion Ω) (inclusion_dense Ω hopen)
    (energyForm Ω) (energyForm_coercive Ω hbdd) f hf

theorem dirichletResolventZero_injective (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) : Function.Injective (dirichletResolventZero Ω hbdd) :=
  PolyaBridge.CoerciveForm.formInverse_injective (inclusion Ω) (inclusion_dense Ω hopen)
    (energyForm Ω) (energyForm_coercive Ω hbdd)

theorem dirichletResolventZero_symmetric (Ω : Set ℂ) (hbdd : Bornology.IsBounded Ω) :
    (dirichletResolventZero Ω hbdd).IsSymmetric :=
  PolyaBridge.CoerciveForm.formInverse_symmetric (inclusion Ω) (energyForm Ω)
    (energyForm_coercive Ω hbdd) (energyForm_symmetric Ω)

theorem dirichletOperator_selfAdjoint (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) : IsSelfAdjoint (dirichletOperator Ω hbdd) :=
  PolyaBridge.CoerciveForm.associatedOperator_selfAdjoint (inclusion Ω)
    (inclusion_dense Ω hopen) (energyForm Ω) (energyForm_coercive Ω hbdd)
    (energyForm_symmetric Ω)

theorem dirichletOperator_closed (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) : (dirichletOperator Ω hbdd).IsClosed :=
  PolyaBridge.CoerciveForm.associatedOperator_closed (inclusion Ω)
    (inclusion_dense Ω hopen) (energyForm Ω) (energyForm_coercive Ω hbdd)
    (energyForm_symmetric Ω)

theorem dirichletOperator_nonneg (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (u : (dirichletOperator Ω hbdd).domain) :
    0 ≤ ⟪dirichletOperator Ω hbdd u, (u : DomainL2 Ω)⟫_ℝ :=
  PolyaBridge.CoerciveForm.associatedOperator_nonneg (inclusion Ω)
    (inclusion_dense Ω hopen) (energyForm Ω) (energyForm_coercive Ω hbdd)
    (energyForm_symmetric Ω) u

theorem dirichletOperator_eigenvector_iff_weak (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (u : H01 Ω) (lam : ℝ) :
    (∃ hu : inclusion Ω u ∈ (dirichletOperator Ω hbdd).domain,
      dirichletOperator Ω hbdd ⟨inclusion Ω u, hu⟩ = lam • inclusion Ω u) ↔
      ∀ v : H01 Ω, energyForm Ω u v = lam * ⟪inclusion Ω u, inclusion Ω v⟫_ℝ :=
  PolyaBridge.CoerciveForm.eigenvector_iff_weak_equation (inclusion Ω)
    (inclusion_dense Ω hopen) (inclusion_injective Ω hopen.measurableSet)
    (energyForm Ω) (energyForm_coercive Ω hbdd) u lam

theorem sobolevEigenvalue_eq_domainFormMinmax (Ω : Set ℂ) (hΩ : MeasurableSet Ω)
    (j : ℕ) : sobolevEigenvalue Ω j =
      PolyaBridge.CoreMinmax.formMinmaxOn (energyForm Ω) (inclusion Ω) ⊤ j := by
  simp only [sobolevEigenvalue, PolyaBridge.CoreMinmax.formMinmaxOn,
    PolyaBridge.CoreMinmax.formRayleigh, norm_inclusion_eq_value Ω hΩ]

lemma exists_smooth_trial_space (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hne : Ω.Nonempty) (j : ℕ) :
    ∃ W : Submodule ℝ (ℂ → ℝ), W ≤ testFunctions Ω ∧ Module.finrank ℝ W = j := by
  by_contra h
  have htop : dirichletEigenvalue Ω j = ⊤ := by
    apply top_unique
    unfold dirichletEigenvalue
    refine le_iInf fun W => le_iInf fun hW => le_iInf fun hdim => ?_
    exact False.elim (h ⟨W, hW, hdim⟩)
  exact (dirichletEigenvalue_lt_top hopen hne j).ne htop

theorem domainL2_infinite (Ω : Set ℂ) (hopen : IsOpen Ω) (hne : Ω.Nonempty) :
    ¬ Module.Finite ℝ (DomainL2 Ω) := by
  intro hfinite
  letI : Module.Finite ℝ (DomainL2 Ω) := hfinite
  let P : SmoothCore Ω →ₗ[ℝ] DomainL2 Ω := (inclusion Ω).toLinearMap.comp (coreToH01 Ω)
  have hP : Function.Injective P :=
    (inclusion_injective Ω hopen.measurableSet).comp (coreToH01_injective Ω)
  letI : Module.Finite ℝ (SmoothCore Ω) := FiniteDimensional.of_injective P hP
  obtain ⟨W, hW, hdim⟩ := exists_smooth_trial_space Ω hopen hne
    (Module.finrank ℝ (SmoothCore Ω) + 1)
  have hle : Module.finrank ℝ W ≤ Module.finrank ℝ (SmoothCore Ω) :=
    LinearMap.finrank_le_finrank_of_injective (Submodule.inclusion_injective hW)
  rw [hdim] at hle
  exact Nat.not_succ_le_self _ hle

theorem strict_polya_sobolev (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (hsc : SimplyConnectedSpace Ω)
    (j : ℕ) (hj : 1 ≤ j) :
    ENNReal.ofReal (4 * Real.pi * j) < MeasureTheory.volume Ω * sobolevEigenvalue Ω j := by
  rw [← dirichletEigenvalue_eq_sobolevEigenvalue Ω hj]
  exact strict_polya_variational Ω hopen hbdd hsc j hj


end DirichletBridge

noncomputable section

namespace DirichletBridge

open MeasureTheory Set Metric Topology
open scoped InnerProductSpace

section CompactTransfer

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

omit [CompleteSpace W] in
lemma compact_transfer_quartic_bound (J : V →L[ℝ] W) (T : W →L[ℝ] W)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ v, ‖J v‖ ^ 4 ≤ C * (‖T (J v)‖ * ‖J v‖) * ‖v‖ ^ 2)
    (v : V) (hv : ‖v‖ ≤ 2) :
    ‖J v‖ ^ 4 ≤ (8 * (C + 1) * (‖J‖ + 1)) * ‖T (J v)‖ := by
  have hv2 : ‖v‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg v]
  have hJv : ‖J v‖ ≤ 2 * (‖J‖ + 1) := by
    calc ‖J v‖ ≤ ‖J‖ * ‖v‖ := J.le_opNorm v
      _ ≤ ‖J‖ * 2 := mul_le_mul_of_nonneg_left hv (norm_nonneg J)
      _ ≤ 2 * (‖J‖ + 1) := by linarith
  calc ‖J v‖ ^ 4 ≤ C * (‖T (J v)‖ * ‖J v‖) * ‖v‖ ^ 2 := hbound v
    _ ≤ C * (‖T (J v)‖ * (2 * (‖J‖ + 1))) * 4 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hJv (norm_nonneg _)) hC)
        hv2 (sq_nonneg _) (by positivity)
    _ = (8 * C * (‖J‖ + 1)) * ‖T (J v)‖ := by ring
    _ ≤ (8 * (C + 1) * (‖J‖ + 1)) * ‖T (J v)‖ := by
      gcongr
      linarith

/-- A quartic bound controlled by a compact operator gives a compact embedding.
This proves the required finite-net statement rather than assuming Rellich. -/
theorem isCompactOperator_of_quartic_bound (J : V →L[ℝ] W) (T : W →L[ℝ] W)
    (hT : IsCompactOperator T) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ v, ‖J v‖ ^ 4 ≤ C * (‖T (J v)‖ * ‖J v‖) * ‖v‖ ^ 2) :
    IsCompactOperator J := by
  classical
  let S : Set W := J '' closedBall (0 : V) 1
  have hTJ : IsCompactOperator (T.comp J) := hT.comp_clm J
  have hTS : TotallyBounded ((T.comp J) '' closedBall (0 : V) 1) :=
    (hTJ.isCompact_closure_image_closedBall 1).totallyBounded.subset subset_closure
  have hS : TotallyBounded S := by
    apply totallyBounded_of_finite_discretization
    intro ε hε
    let R : ℝ := 8 * (C + 1) * (‖J‖ + 1)
    have hR : 0 < R := by dsimp [R]; positivity
    let δ : ℝ := (ε ^ 4 / R) / 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.1 hTS δ hδ
    letI : Fintype t := ht.fintype
    have hcenters : ∀ x : S, ∃ y : t, dist (T x.val) y.val < δ := by
      intro x
      have hxT : T x.val ∈ (T.comp J) '' closedBall (0 : V) 1 := by
        obtain ⟨v, hv, heq⟩ := x.property
        exact ⟨v, hv, congrArg T heq⟩
      have hx := hcover hxT
      simp only [mem_iUnion, mem_ball] at hx
      obtain ⟨y, hyt, hxy⟩ := hx
      exact ⟨⟨y, hyt⟩, hxy⟩
    choose F hF using hcenters
    refine ⟨t, inferInstance, F, fun x y hxy => ?_⟩
    obtain ⟨vx, hvx, hex⟩ := x.property
    obtain ⟨vy, hvy, hey⟩ := y.property
    have hvx1 : ‖vx‖ ≤ 1 := mem_closedBall_zero_iff.1 hvx
    have hvy1 : ‖vy‖ ≤ 1 := mem_closedBall_zero_iff.1 hvy
    have hv : ‖vx - vy‖ ≤ 2 :=
      (norm_sub_le vx vy).trans (by linarith)
    have hnear : ‖T (J (vx - vy))‖ < ε ^ 4 / R := by
      rw [map_sub, map_sub, hex, hey, ← dist_eq_norm]
      calc dist (T x.val) (T y.val) ≤
          dist (T x.val) (F x).val + dist (F x).val (T y.val) := dist_triangle _ _ _
        _ < δ + δ := add_lt_add (hF x) (by
          rw [hxy, dist_comm]
          exact hF y)
        _ = ε ^ 4 / R := by dsimp [δ]; ring
    have hquartic : ‖J (vx - vy)‖ ^ 4 < ε ^ 4 := by
      calc ‖J (vx - vy)‖ ^ 4 ≤ R * ‖T (J (vx - vy))‖ :=
          compact_transfer_quartic_bound J T C hC hbound _ hv
        _ < R * (ε ^ 4 / R) := mul_lt_mul_of_pos_left hnear hR
        _ = ε ^ 4 := by field_simp [hR.ne']
    have hnorm : ‖J (vx - vy)‖ < ε :=
      lt_of_pow_lt_pow_left₀ 4 hε.le hquartic
    rw [map_sub, hex, hey, ← dist_eq_norm] at hnorm
    exact hnorm
  change IsCompactOperator J.toLinearMap
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall J.toLinearMap one_pos).2
  exact isCompact_iff_totallyBounded_isComplete.2
    ⟨hS.closure, isClosed_closure.isComplete⟩

end CompactTransfer

section NormControlTransfer

variable {V W₁ W₂ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W₁] [NormedSpace ℝ W₁] [CompleteSpace W₁]
  [NormedAddCommGroup W₂] [NormedSpace ℝ W₂]

/-- Compactness passes through an actual uniform norm comparison. -/
theorem isCompactOperator_of_norm_control (J₁ : V →L[ℝ] W₁)
    (J₂ : V →L[ℝ] W₂) (hJ₂ : IsCompactOperator J₂)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ v, ‖J₁ v‖ ≤ C * ‖J₂ v‖) :
    IsCompactOperator J₁ := by
  classical
  let S : Set W₁ := J₁ '' closedBall (0 : V) 1
  have hTS : TotallyBounded (J₂ '' closedBall (0 : V) 1) :=
    (hJ₂.isCompact_closure_image_closedBall 1).totallyBounded.subset subset_closure
  have hS : TotallyBounded S := by
    apply totallyBounded_of_finite_discretization
    intro ε hε
    let δ : ℝ := ε / (2 * (C + 1))
    have hden : 0 < 2 * (C + 1) := by positivity
    have hδ : 0 < δ := div_pos hε hden
    obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.1 hTS δ hδ
    letI : Fintype t := ht.fintype
    have hcenters : ∀ x : S, ∃ y : t, ∃ v : V,
        J₁ v = x.val ∧ dist (J₂ v) y.val < δ := by
      intro x
      obtain ⟨v, hv, heq⟩ := x.property
      have hx := hcover (show J₂ v ∈ J₂ '' closedBall (0 : V) 1 from ⟨v, hv, rfl⟩)
      simp only [mem_iUnion, mem_ball] at hx
      obtain ⟨y, hyt, hxy⟩ := hx
      exact ⟨⟨y, hyt⟩, v, heq, hxy⟩
    choose F source hvalue hF using hcenters
    refine ⟨ULift (Fin (Fintype.card t)), inferInstance,
      fun x => ⟨(Fintype.equivFin t) (F x)⟩, fun x y hxy => ?_⟩
    have hxy' : F x = F y :=
      (Fintype.equivFin t).injective (congrArg ULift.down hxy)
    have hnear : ‖J₂ (source x - source y)‖ < 2 * δ := by
      rw [map_sub, ← dist_eq_norm]
      calc dist (J₂ (source x)) (J₂ (source y)) ≤
          dist (J₂ (source x)) (F x).val +
            dist (F x).val (J₂ (source y)) := dist_triangle _ _ _
        _ < δ + δ := add_lt_add (hF x) (by
          rw [hxy', dist_comm]
          exact hF y)
        _ = 2 * δ := by ring
    have hnorm : ‖J₁ (source x - source y)‖ < ε := by
      calc ‖J₁ (source x - source y)‖ ≤ C * ‖J₂ (source x - source y)‖ :=
          hbound _
        _ ≤ (C + 1) * ‖J₂ (source x - source y)‖ := by
          exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
        _ < (C + 1) * (2 * δ) := mul_lt_mul_of_pos_left hnear (by linarith)
        _ = ε := by dsimp [δ]; field_simp [hden.ne']
    rw [map_sub, hvalue x, hvalue y, ← dist_eq_norm] at hnorm
    exact hnorm
  change IsCompactOperator J₁.toLinearMap
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall J₁.toLinearMap one_pos).2
  exact isCompact_iff_totallyBounded_isComplete.2
    ⟨hS.closure, isClosed_closure.isComplete⟩

end NormControlTransfer

abbrev unitDisk : Set ℂ := ball 0 1

def unitDiskWeight : WeightOK (fun _ : ℂ => (1 : ℝ)) 1 where
  meas := measurable_const
  bound := by simp
  pos := by simp
  smooth := contDiff_const.contDiffOn

def diskGreen : DomainL2 unitDisk →L[ℝ] DomainL2 unitDisk :=
  greenOp unitDiskWeight.meas unitDiskWeight.bound

lemma inclusion_core_disk_eq_weightLp (u : SmoothCore unitDisk) :
    inclusion unitDisk (coreToH01 unitDisk u) = weightLp unitDiskWeight u.property := by
  apply Lp.ext
  filter_upwards [inclusion_coreToH01_coeFn unitDisk u,
    (memLp_weight_test unitDiskWeight u.property).coeFn_toLp] with z hinc hweight
  rw [hinc]
  change (u : ℂ → ℝ) z = (memLp_weight_test unitDiskWeight u.property).toLp _ z
  rw [hweight]
  simp

lemma energy_core_disk (u : SmoothCore unitDisk) :
    energy unitDisk (coreToH01 unitDisk u) =
      ∫ z in unitDisk, ‖fderiv ℝ (u : ℂ → ℝ) z‖ ^ 2 := by
  change ‖coreDeriv unitDisk 1 u‖ ^ 2 + ‖coreDeriv unitDisk Complex.I u‖ ^ 2 = _
  have h := congrArg ENNReal.toReal
    ((dirichletEnergy_core unitDisk u).symm.trans (dirichletEnergy_test u.property))
  rw [ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (integral_nonneg fun z => sq_nonneg _)] at h
  exact h

lemma disk_quartic_bound_core (u : SmoothCore unitDisk) :
    ‖inclusion unitDisk (coreToH01 unitDisk u)‖ ^ 4 ≤
      (‖diskGreen (inclusion unitDisk (coreToH01 unitDisk u))‖ *
        ‖inclusion unitDisk (coreToH01 unitDisk u)‖) *
      energy unitDisk (coreToH01 unitDisk u) := by
  have h := (key_lower unitDiskWeight u.property).2.2.1
  simp only [← inclusion_core_disk_eq_weightLp, ← energy_core_disk] at h
  exact h.trans (mul_le_mul_of_nonneg_right (real_inner_le_norm _ _) (by
    unfold energy
    positivity))

lemma disk_quartic_bound_H01 (u : H01 unitDisk) :
    ‖inclusion unitDisk u‖ ^ 4 ≤
      (‖diskGreen (inclusion unitDisk u)‖ * ‖inclusion unitDisk u‖) * energy unitDisk u := by
  let S : Set (H01 unitDisk) := {v | ‖inclusion unitDisk v‖ ^ 4 ≤
    (‖diskGreen (inclusion unitDisk v)‖ * ‖inclusion unitDisk v‖) * energy unitDisk v}
  have hE : Continuous (energy unitDisk) :=
    ((gradient unitDisk 0).continuous.norm.pow 2).add
      ((gradient unitDisk 1).continuous.norm.pow 2)
  have hS : IsClosed S := isClosed_le ((inclusion unitDisk).continuous.norm.pow 4)
    (((diskGreen.continuous.comp (inclusion unitDisk).continuous).norm.mul
      (inclusion unitDisk).continuous.norm).mul hE)
  have hcore : Set.range (coreToH01 unitDisk) ⊆ S := by
    rintro v ⟨w, rfl⟩
    exact disk_quartic_bound_core w
  exact closure_minimal hcore hS (coreToH01_dense unitDisk u)

theorem inclusion_unitDisk_compact : IsCompactOperator (inclusion unitDisk) := by
  have hG : IsCompactOperator diskGreen :=
    greenOp_isCompactOperator unitDiskWeight.meas unitDiskWeight.bound
  apply isCompactOperator_of_quartic_bound (inclusion unitDisk) diskGreen hG 1 zero_le_one
  intro u
  simp only [one_mul]
  have hE : energy unitDisk u ≤ ‖u‖ ^ 2 := by
    rw [norm_H01_sq]
    exact le_add_of_nonneg_left (sq_nonneg _)
  exact (disk_quartic_bound_H01 u).trans
    (mul_le_mul_of_nonneg_left hE (mul_nonneg (norm_nonneg _) (norm_nonneg _)))

end DirichletBridge

namespace PolyaBridge.SpectralMinmax

open Set
open scoped InnerProductSpace

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem form_cauchy_schwarz (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (hSym : ∀ u v, B u v = B v u) (u v : V) :
    (B u v) ^ 2 ≤ B u u * B v v := by
  let T : V →L[ℝ] V := InnerProductSpace.continuousLinearMapOfBilin B
  have hRep : ∀ x y : V, ⟪T x, y⟫_ℝ = B x y :=
    InnerProductSpace.continuousLinearMapOfBilin_apply B
  have hTsym : ∀ x y : V, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ := by
    intro x y
    calc
      ⟪T x, y⟫_ℝ = B x y := hRep x y
      _ = B y x := hSym x y
      _ = ⟪T y, x⟫_ℝ := (hRep y x).symm
      _ = ⟪x, T y⟫_ℝ := real_inner_comm x (T y)
  have hTpos : ∀ x : V, 0 ≤ ⟪T x, x⟫_ℝ := by
    intro x
    rw [hRep]
    exact CoerciveForm.form_self_nonneg B hB x
  simpa only [hRep] using _root_.inner_apply_sq_le_of_psd hTsym hTpos u v

omit [CompleteSpace V] [CompleteSpace H] in
theorem exists_trial_vector_orthogonal (J : V →L[ℝ] H)
    {j : ℕ} (hj : 0 < j) (W : Submodule ℝ V)
    (hWdim : Module.finrank ℝ W = j) (e : ℕ → H) :
    ∃ u : V, u ∈ W ∧ u ≠ 0 ∧ ∀ l < j - 1, ⟪e l, J u⟫_ℝ = 0 := by
  classical
  letI : Module.Finite ℝ W := Module.finite_of_finrank_pos (by
    rw [hWdim]
    exact hj)
  let coordinates : W →ₗ[ℝ] (Fin (j - 1) → ℝ) :=
    { toFun := fun u i => ⟪e i, J (u : V)⟫_ℝ
      map_add' := by
        intro u v
        ext i
        simp [inner_add_right]
      map_smul' := by
        intro c u
        ext i
        simp [inner_smul_right] }
  have hker : LinearMap.ker coordinates ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simp [hWdim]; omega)
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨u, u.property, (fun h => hu0 (Subtype.ext h)), ?_⟩
  intro l hl
  have hzero := congrFun (LinearMap.mem_ker.mp hu) (⟨l, hl⟩ : Fin (j - 1))
  simpa [coordinates] using hzero

theorem lower_rayleigh_of_orthogonality (J : V →L[ℝ] H)
    (hJ : Function.Injective J) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (hSym : ∀ u v, B u v = B v u)
    {j : ℕ} (hj : 0 < j)
    (f : CompactSpectral.PositiveEigenFamily (CoerciveForm.formInverse J B hB) j)
    {u : V} (hu : u ≠ 0)
    (hOrth : ∀ l < j - 1, ⟪f.vectors l, J u⟫_ℝ = 0) :
    ENNReal.ofReal (1 / f.values (j - 1)) ≤ CoreMinmax.formRayleigh B J u := by
  have hJu : J u ≠ 0 := by
    intro h
    exact hu (hJ (by simpa using h))
  have hMassPos : 0 < ‖J u‖ ^ 2 := by positivity
  have hMuPos : 0 < f.values (j - 1) := f.positive (j - 1) (by omega)
  let v : V := CoerciveForm.solution J B hB (J u)
  have hvu : B v u = ‖J u‖ ^ 2 := by
    rw [CoerciveForm.solution_form, real_inner_self_eq_norm_sq]
  have hvv : B v v = ⟪CoerciveForm.formInverse J B hB (J u), J u⟫_ℝ :=
    (CoerciveForm.formInverse_inner J B hB (J u) (J u)).symm
  have hCS := form_cauchy_schwarz B hB hSym v u
  rw [hvu, hvv] at hCS
  have hUpper := f.maximal (j - 1) (by omega) (J u) hOrth
  have hEnergyNonneg : 0 ≤ B u u := CoerciveForm.form_self_nonneg B hB u
  have hScaled := hCS.trans (mul_le_mul_of_nonneg_right hUpper hEnergyNonneg)
  have hScaled' : ‖J u‖ ^ 2 * ‖J u‖ ^ 2 ≤
      ‖J u‖ ^ 2 * (f.values (j - 1) * B u u) := by
    simpa only [pow_two, mul_assoc, mul_left_comm] using hScaled
  have hMassBound : ‖J u‖ ^ 2 ≤ f.values (j - 1) * B u u :=
    (mul_le_mul_iff_right₀ hMassPos).mp hScaled'
  have hEnergyBound : (1 / f.values (j - 1)) * ‖J u‖ ^ 2 ≤ B u u := by
    rw [one_div]
    exact (inv_mul_le_iff₀ hMuPos).mpr hMassBound
  have hMass0 : ENNReal.ofReal (‖J u‖ ^ 2) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hMassPos)
  unfold CoreMinmax.formRayleigh
  apply (ENNReal.le_div_iff_mul_le (Or.inl hMass0) (Or.inl ENNReal.ofReal_ne_top)).mpr
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / f.values (j - 1))]
  exact ENNReal.ofReal_le_ofReal hEnergyBound

theorem minmax_lower_of_eigenfamily (J : V →L[ℝ] H)
    (hJ : Function.Injective J) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (hSym : ∀ u v, B u v = B v u)
    {j : ℕ} (hj : 0 < j)
    (f : CompactSpectral.PositiveEigenFamily (CoerciveForm.formInverse J B hB) j) :
    ENNReal.ofReal (1 / f.values (j - 1)) ≤ CoreMinmax.formMinmaxOn B J ⊤ j := by
  unfold CoreMinmax.formMinmaxOn
  refine le_iInf fun W => le_iInf fun _ => le_iInf fun hWdim => ?_
  obtain ⟨u, huW, hu0, huOrth⟩ := exists_trial_vector_orthogonal J hj W hWdim f.vectors
  exact le_iSup_of_le u (le_iSup_of_le huW (le_iSup_of_le hu0
    (lower_rayleigh_of_orthogonality J hJ B hB hSym hj f hu0 huOrth)))

theorem minmax_upper_of_eigenfamily (J : V →L[ℝ] H)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    {j : ℕ} (hj : 0 < j)
    (f : CompactSpectral.PositiveEigenFamily (CoerciveForm.formInverse J B hB) j) :
    CoreMinmax.formMinmaxOn B J ⊤ j ≤ ENNReal.ofReal (1 / f.values (j - 1)) := by
  classical
  have hMuPos : 0 < f.values (j - 1) := f.positive (j - 1) (by omega)
  let u : Fin j → V := fun i => (1 / f.values i) • CoerciveForm.solution J B hB (f.vectors i)
  have hJu : ∀ i : Fin j, J (u i) = f.vectors i := by
    intro i
    change J ((1 / f.values i) • CoerciveForm.solution J B hB (f.vectors i)) = f.vectors i
    rw [map_smul]
    change (1 / f.values i) • CoerciveForm.formInverse J B hB (f.vectors i) = f.vectors i
    rw [f.eigenvector i i.isLt, smul_smul, one_div,
      inv_mul_cancel₀ (f.positive i i.isLt).ne', one_smul]
  have hForm : ∀ (i : Fin j) (v : V),
      B (u i) v = (1 / f.values i) * ⟪f.vectors i, J v⟫_ℝ := by
    intro i v
    simp only [u, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
      CoerciveForm.solution_form]
  have huLI : LinearIndependent ℝ u := by
    apply LinearIndependent.of_comp J.toLinearMap
    change LinearIndependent ℝ (fun i : Fin j => J (u i))
    simp_rw [hJu]
    exact f.orthonormal.linearIndependent
  have hJuSum : ∀ c : Fin j → ℝ,
      J (CoreMinmax.synthesis u c) = ∑ i, c i • f.vectors i := by
    intro c
    simp only [CoreMinmax.synthesis_apply, map_sum, map_smul, hJu]
  have hNormSum : ∀ c : Fin j → ℝ,
      ‖J (CoreMinmax.synthesis u c)‖ ^ 2 = ∑ i, c i ^ 2 := by
    intro c
    rw [hJuSum]
    exact CompactSpectral.norm_sq_sum_orthonormal f.orthonormal c
  have hFormSum : ∀ c : Fin j → ℝ,
      B (CoreMinmax.synthesis u c) (CoreMinmax.synthesis u c) =
        ∑ i : Fin j, (1 / f.values i) * c i ^ 2 := by
    intro c
    change B (∑ i : Fin j, c i • u i) (CoreMinmax.synthesis u c) = _
    rw [map_sum, ContinuousLinearMap.sum_apply]
    simp_rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
      hForm, hJuSum, f.orthonormal.inner_right_fintype c]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hInvLe : ∀ i : Fin j, 1 / f.values i ≤ 1 / f.values (j - 1) := by
    intro i
    exact one_div_le_one_div_of_le (f.positive (j - 1) (by omega))
      (f.value_le i.isLt (by omega) (by omega))
  have hEnergy : ∀ c : Fin j → ℝ,
      B (CoreMinmax.synthesis u c) (CoreMinmax.synthesis u c) ≤
        (1 / f.values (j - 1)) * ‖J (CoreMinmax.synthesis u c)‖ ^ 2 := by
    intro c
    rw [hFormSum, hNormSum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hInvLe i) (sq_nonneg _)
  let W : Submodule ℝ V := Submodule.span ℝ (Set.range u)
  have hWdim : Module.finrank ℝ W = j := by
    dsimp [W]
    rw [finrank_span_eq_card huLI, Fintype.card_fin]
  have hRayleigh : ∀ x ∈ W,
      CoreMinmax.formRayleigh B J x ≤ ENNReal.ofReal (1 / f.values (j - 1)) := by
    intro x hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
    apply CoreMinmax.formRayleigh_le_of_energy_bound B J
      (by positivity : 0 ≤ 1 / f.values (j - 1))
    have hcx : CoreMinmax.synthesis u c = x := by
      simpa only [CoreMinmax.synthesis_apply] using hc
    simpa only [hcx] using hEnergy c
  calc
    CoreMinmax.formMinmaxOn B J ⊤ j ≤
        ⨆ (x : V) (_ : x ∈ W) (_ : x ≠ 0), CoreMinmax.formRayleigh B J x :=
      iInf_le_of_le W (iInf_le_of_le (le_top : W ≤ ⊤) (iInf_le_of_le hWdim le_rfl))
    _ ≤ ENNReal.ofReal (1 / f.values (j - 1)) :=
      iSup_le fun x => iSup_le fun hx => iSup_le fun _ => hRayleigh x hx

theorem minmax_eq_reciprocal_of_eigenfamily (J : V →L[ℝ] H)
    (hJ : Function.Injective J) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (hSym : ∀ u v, B u v = B v u)
    {j : ℕ} (hj : 0 < j)
    (f : CompactSpectral.PositiveEigenFamily (CoerciveForm.formInverse J B hB) j) :
    CoreMinmax.formMinmaxOn B J ⊤ j = ENNReal.ofReal (1 / f.values (j - 1)) :=
  le_antisymm (minmax_upper_of_eigenfamily J B hB hj f)
    (minmax_lower_of_eigenfamily J hJ B hB hSym hj f)

/-- The independently defined, ordered eigenvalues of the genuine form inverse
are the reciprocals of the form-domain min-max values. -/
theorem form_minmax_eq_inverse_spectral (J : V →L[ℝ] H)
    (hJ : Function.Injective J) (hJdense : DenseRange J) (hJcompact : IsCompactOperator J)
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (hSym : ∀ u v, B u v = B v u) (hInfinite : ¬ Module.Finite ℝ H)
    {j : ℕ} (hj : 0 < j) :
    CoreMinmax.formMinmaxOn B J ⊤ j =
      ENNReal.ofReal ((CompactSpectral.spectralEigenvalue (CoerciveForm.formInverse J B hB) j)⁻¹) := by
  have hCompact := CoerciveForm.formInverse_compact J hJcompact B hB
  have hSymmetric : ∀ x y : H,
      ⟪CoerciveForm.formInverse J B hB x, y⟫_ℝ =
        ⟪x, CoerciveForm.formInverse J B hB y⟫_ℝ :=
    CoerciveForm.formInverse_symmetric J B hB hSym
  have hPositive : ∀ x : H, x ≠ 0 → 0 < ⟪CoerciveForm.formInverse J B hB x, x⟫_ℝ :=
    CoerciveForm.formInverse_strictPositive J hJdense B hB
  obtain ⟨f⟩ := CompactSpectral.exists_positive_eigenfamily
    hCompact hSymmetric hPositive hInfinite j
  calc
    CoreMinmax.formMinmaxOn B J ⊤ j = ENNReal.ofReal (1 / f.values (j - 1)) :=
      minmax_eq_reciprocal_of_eigenfamily J hJ B hB hSym hj f
    _ = ENNReal.ofReal ((CompactSpectral.spectralEigenvalue (CoerciveForm.formInverse J B hB) j)⁻¹) := by
      rw [f.spectralEigenvalue_eq_last hj, one_div]

end PolyaBridge.SpectralMinmax

/-! Dilation from any bounded planar zero-boundary form domain to the unit disk.
The extension is made from the smooth core with an actual H¹ norm estimate. -/

noncomputable section

namespace DirichletBridge

open MeasureTheory Set Metric Topology
open scoped InnerProductSpace

def dilate (R : ℝ) (z : ℂ) : ℂ := (R : ℂ) * z

lemma norm_dilate (R : ℝ) (hR : 0 < R) (z : ℂ) :
    ‖dilate R z‖ = R * ‖z‖ := by
  rw [dilate, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]

lemma dilate_hasDerivAt (R : ℝ) (z : ℂ) : HasDerivAt (dilate R) (R : ℂ) z := by
  change HasDerivAt (fun y : ℂ => (R : ℂ) * y) (R : ℂ) z
  simpa using (hasDerivAt_const_mul (R : ℂ) (x := z))

lemma dilate_injective (R : ℝ) (hR : 0 < R) : Function.Injective (dilate R) := by
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  intro z w h
  exact mul_left_cancel₀ hRC h

lemma dilate_image_univ (R : ℝ) (hR : 0 < R) : dilate R '' univ = univ := by
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  ext w
  constructor
  · intro _
    exact mem_univ _
  · intro _
    exact ⟨(R : ℂ)⁻¹ * w, mem_univ _, by simp [dilate, hRC]⟩

lemma dilate_inv_dilate (R : ℝ) (hR : 0 < R) (z : ℂ) :
    dilate R⁻¹ (dilate R z) = z := by
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  simp [dilate, Complex.ofReal_inv, hRC]

lemma dilate_dilate_inv (R : ℝ) (hR : 0 < R) (z : ℂ) :
    dilate R (dilate R⁻¹ z) = z := by
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  simp [dilate, Complex.ofReal_inv, hRC]

def dilateFunction (R : ℝ) : (ℂ → ℝ) →ₗ[ℝ] (ℂ → ℝ) where
  toFun u := fun z => u (dilate R z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma dilate_test_ball (R : ℝ) (hR : 0 < R) {u : ℂ → ℝ}
    (hu : u ∈ testFunctions (ball (0 : ℂ) R)) :
    dilateFunction R u ∈ testFunctions unitDisk := by
  have hPhi : DifferentiableOn ℂ (dilate R) unitDisk :=
    fun z _ => (dilate_hasDerivAt R z).differentiableAt.differentiableWithinAt
  have hPsi : ContinuousOn (dilate R⁻¹) (ball (0 : ℂ) R) := by
    unfold dilate
    fun_prop
  have hPsiMaps : MapsTo (dilate R⁻¹) (ball (0 : ℂ) R) unitDisk := by
    intro w hw
    rw [mem_ball, dist_zero_right] at hw ⊢
    rw [norm_dilate R⁻¹ (inv_pos.mpr hR)]
    calc R⁻¹ * ‖w‖ < R⁻¹ * R := mul_lt_mul_of_pos_left hw (inv_pos.mpr hR)
      _ = 1 := inv_mul_cancel₀ hR.ne'
  have hPsiPhi : ∀ z ∈ unitDisk,
      dilate R z ∈ ball (0 : ℂ) R ∧ dilate R⁻¹ (dilate R z) = z := by
    intro z hz
    refine ⟨?_, dilate_inv_dilate R hR z⟩
    rw [mem_ball, dist_zero_right] at hz ⊢
    rw [norm_dilate R hR]
    simpa only [mul_one] using mul_lt_mul_of_pos_left hz hR
  have htest := (pullback_test (Ω := unitDisk) (Ω' := ball (0 : ℂ) R)
    isOpen_ball hPhi hPsi hPsiMaps hPsiPhi hu).1
  have heq : pullbackLin unitDisk (dilate R) u = dilateFunction R u := by
    funext z
    rw [pullbackLin_apply]
    by_cases hz : z ∈ unitDisk
    · rw [indicator_of_mem hz]
      rfl
    · have hzero : u (dilate R z) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hsupport
        have hnorm := hu.2.2 hsupport
        rw [mem_ball, dist_zero_right, norm_dilate R hR] at hnorm
        have hzNorm : 1 ≤ ‖z‖ := by
          apply le_of_not_gt
          intro h
          exact hz (by simpa only [unitDisk, mem_ball, dist_zero_right] using h)
        nlinarith
      rw [indicator_of_notMem hz]
      exact hzero.symm
  rwa [heq] at htest

def dilateCore (Ω : Set ℂ) (R : ℝ) (hR : 0 < R)
    (hΩ : Ω ⊆ ball (0 : ℂ) R) : SmoothCore Ω →ₗ[ℝ] SmoothCore unitDisk :=
  ((dilateFunction R).domRestrict (testFunctions Ω)).codRestrict (testFunctions unitDisk)
    (fun u => dilate_test_ball R hR
      ⟨u.property.1, u.property.2.1, u.property.2.2.trans hΩ⟩)

@[simp] lemma dilateCore_apply (Ω : Set ℂ) (R : ℝ) (hR : 0 < R)
    (hΩ : Ω ⊆ ball (0 : ℂ) R) (u : SmoothCore Ω) (z : ℂ) :
    (dilateCore Ω R hR hΩ u : ℂ → ℝ) z = (u : ℂ → ℝ) (dilate R z) := rfl

/-- The exact two-dimensional mass scaling, proved by the holomorphic Jacobian. -/
lemma l2NormSq_dilate (R : ℝ) (hR : 0 < R) (u : ℂ → ℝ) :
    l2NormSq u = ENNReal.ofReal (R ^ 2) * l2NormSq (dilateFunction R u) := by
  have hPhi : DifferentiableOn ℂ (dilate R) univ :=
    fun z _ => (dilate_hasDerivAt R z).differentiableAt.differentiableWithinAt
  have h := lintegral_image_holomorphic isOpen_univ hPhi
    (dilate_injective R hR).injOn (fun z => ‖u z‖ₑ ^ 2)
  simp only [dilate_image_univ R hR, Measure.restrict_univ] at h
  have hJac : ∀ z, ENNReal.ofReal (‖deriv (dilate R) z‖ ^ 2) =
      ENNReal.ofReal (R ^ 2) := by
    intro z
    rw [(dilate_hasDerivAt R z).deriv, Complex.norm_real,
      Real.norm_of_nonneg hR.le]
  simp_rw [hJac] at h
  change l2NormSq u = ∫⁻ z, ENNReal.ofReal (R ^ 2) *
    ‖(dilateFunction R u) z‖ₑ ^ 2 at h
  exact h.trans (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)

lemma dirichletEnergy_dilate_le (R : ℝ) (hR : 0 < R) {u : ℂ → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    dirichletEnergy (dilateFunction R u) ≤ dirichletEnergy u := by
  have hPhi : DifferentiableOn ℂ (dilate R) univ :=
    fun z _ => (dilate_hasDerivAt R z).differentiableAt.differentiableWithinAt
  have h := dirichletEnergy_pullback_le isOpen_univ hPhi
    (dilate_injective R hR).injOn hu
    (fun z hz => (hz (mem_univ z)).elim)
  have hdilate : (dilateFunction R u : ℂ → ℝ) = (fun z => u (dilate R z)) := rfl
  rw [hdilate]
  simpa only [Set.indicator_univ] using h

/-- Dirichlet energy is invariant under a two-dimensional dilation. Both
inequalities follow from conformal pullback, using the true inverse dilation. -/
lemma dirichletEnergy_dilate (R : ℝ) (hR : 0 < R) {u : ℂ → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    dirichletEnergy (dilateFunction R u) = dirichletEnergy u := by
  apply le_antisymm (dirichletEnergy_dilate_le R hR hu)
  have hv : ContDiff ℝ (⊤ : ℕ∞) (dilateFunction R u) :=
    hu.comp (contDiff_const.mul contDiff_id)
  have h := dirichletEnergy_dilate_le R⁻¹ (inv_pos.mpr hR) hv
  have heq : dilateFunction R⁻¹ (dilateFunction R u) = u := by
    funext z
    exact congrArg u (dilate_dilate_inv R hR z)
  rwa [heq] at h

def coreDilationH01 (Ω : Set ℂ) (R : ℝ) (hR : 0 < R)
    (hΩ : Ω ⊆ ball (0 : ℂ) R) : SmoothCore Ω →ₗ[ℝ] H01 unitDisk :=
  (coreToH01 unitDisk).comp (dilateCore Ω R hR hΩ)

lemma coreDilation_mass (Ω : Set ℂ) (R : ℝ) (hR : 0 < R)
    (hΩ : Ω ⊆ ball (0 : ℂ) R) (u : SmoothCore Ω) :
    ‖coreValue Ω u‖ ^ 2 = R ^ 2 *
      ‖value unitDisk (coreDilationH01 Ω R hR hΩ u)‖ ^ 2 := by
  have h := l2NormSq_dilate R hR (u : ℂ → ℝ)
  change l2NormSq (u : ℂ → ℝ) = ENNReal.ofReal (R ^ 2) *
    l2NormSq (dilateCore Ω R hR hΩ u : ℂ → ℝ) at h
  rw [l2NormSq_core Ω u, l2NormSq_core unitDisk] at h
  have ht := congrArg ENNReal.toReal h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)] at ht
  exact ht

lemma coreDilation_energy (Ω : Set ℂ) (R : ℝ) (hR : 0 < R)
    (hΩ : Ω ⊆ ball (0 : ℂ) R) (u : SmoothCore Ω) :
    energy unitDisk (coreDilationH01 Ω R hR hΩ u) = energy Ω (coreToH01 Ω u) := by
  have h := dirichletEnergy_dilate R hR u.property.1
  change dirichletEnergy (dilateCore Ω R hR hΩ u : ℂ → ℝ) =
    dirichletEnergy (u : ℂ → ℝ) at h
  rw [dirichletEnergy_core unitDisk, dirichletEnergy_core Ω u] at h
  have ht := congrArg ENNReal.toReal h
  simp only [ENNReal.toReal_ofReal (add_nonneg (sq_nonneg _) (sq_nonneg _))] at ht
  simpa only [energy, coreDilationH01, LinearMap.comp_apply,
    gradient_coreToH01, direction, Matrix.cons_val_zero, Matrix.cons_val_one] using ht

lemma coreDilation_bound (Ω : Set ℂ) (R : ℝ) (hR : 0 < R)
    (hΩ : Ω ⊆ ball (0 : ℂ) R) (u : SmoothCore Ω) :
    ‖coreDilationH01 Ω R hR hΩ u‖ ≤ (R⁻¹ + 1) * ‖coreToH01 Ω u‖ := by
  have hMass := coreDilation_mass Ω R hR hΩ u
  have hMassInv : ‖value unitDisk (coreDilationH01 Ω R hR hΩ u)‖ ^ 2 =
      R⁻¹ ^ 2 * ‖coreValue Ω u‖ ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hR.ne')
    calc
      R ^ 2 * ‖value unitDisk (coreDilationH01 Ω R hR hΩ u)‖ ^ 2 =
          ‖coreValue Ω u‖ ^ 2 := hMass.symm
      _ = R ^ 2 * (R⁻¹ ^ 2 * ‖coreValue Ω u‖ ^ 2) := by
        rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hR.ne']
        simp
  have hEpos : 0 ≤ energy Ω (coreToH01 Ω u) := by unfold energy; positivity
  have hMbound : ‖coreValue Ω u‖ ^ 2 ≤ ‖coreToH01 Ω u‖ ^ 2 := by
    rw [norm_H01_sq, value_coreToH01]
    exact le_add_of_nonneg_right hEpos
  have hEbound : energy Ω (coreToH01 Ω u) ≤ ‖coreToH01 Ω u‖ ^ 2 := by
    rw [norm_H01_sq]
    exact le_add_of_nonneg_left (sq_nonneg _)
  have hC : 0 ≤ R⁻¹ + 1 := by positivity
  have hCsq : R⁻¹ ^ 2 + 1 ≤ (R⁻¹ + 1) ^ 2 := by
    nlinarith [inv_nonneg.mpr hR.le]
  have hsq : ‖coreDilationH01 Ω R hR hΩ u‖ ^ 2 ≤
      ((R⁻¹ + 1) * ‖coreToH01 Ω u‖) ^ 2 := by
    rw [norm_H01_sq, hMassInv, coreDilation_energy]
    calc
      R⁻¹ ^ 2 * ‖coreValue Ω u‖ ^ 2 + energy Ω (coreToH01 Ω u) ≤
          (R⁻¹ ^ 2 + 1) * ‖coreToH01 Ω u‖ ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hMbound (sq_nonneg R⁻¹)]
      _ ≤ (R⁻¹ + 1) ^ 2 * ‖coreToH01 Ω u‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hCsq (sq_nonneg _)
      _ = ((R⁻¹ + 1) * ‖coreToH01 Ω u‖) ^ 2 := (mul_pow _ _ _).symm
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp hsq

def dilationH01 (Ω : Set ℂ) (R : ℝ) (hR : 0 < R)
    (hΩ : Ω ⊆ ball (0 : ℂ) R) : H01 Ω →L[ℝ] H01 unitDisk :=
  (coreDilationH01 Ω R hR hΩ).extendOfNorm (coreToH01 Ω)

@[simp] lemma dilationH01_core (Ω : Set ℂ) (R : ℝ) (hR : 0 < R)
    (hΩ : Ω ⊆ ball (0 : ℂ) R) (u : SmoothCore Ω) :
    dilationH01 Ω R hR hΩ (coreToH01 Ω u) = coreDilationH01 Ω R hR hΩ u := by
  exact LinearMap.extendOfNorm_eq (coreToH01_dense Ω)
    ⟨R⁻¹ + 1, coreDilation_bound Ω R hR hΩ⟩ u

lemma norm_value_dilationH01 (Ω : Set ℂ) (R : ℝ) (hR : 0 < R)
    (hΩ : Ω ⊆ ball (0 : ℂ) R) (u : H01 Ω) :
    ‖value Ω u‖ = R * ‖value unitDisk (dilationH01 Ω R hR hΩ u)‖ := by
  let S : Set (H01 Ω) := {v | ‖value Ω v‖ =
    R * ‖value unitDisk (dilationH01 Ω R hR hΩ v)‖}
  have hS : IsClosed S := isClosed_eq (value Ω).continuous.norm
    (continuous_const.mul ((value unitDisk).continuous.comp
      (dilationH01 Ω R hR hΩ).continuous).norm)
  have hcore : Set.range (coreToH01 Ω) ⊆ S := by
    rintro v ⟨w, rfl⟩
    change ‖value Ω (coreToH01 Ω w)‖ =
      R * ‖value unitDisk (dilationH01 Ω R hR hΩ (coreToH01 Ω w))‖
    rw [dilationH01_core, value_coreToH01]
    apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hR.le (norm_nonneg _))).mp
    simpa only [mul_pow] using coreDilation_mass Ω R hR hΩ w
  exact closure_minimal hcore hS (coreToH01_dense Ω u)

lemma norm_inclusion_dilationH01 (Ω : Set ℂ) (hOpen : IsOpen Ω)
    (R : ℝ) (hR : 0 < R) (hΩ : Ω ⊆ ball (0 : ℂ) R) (u : H01 Ω) :
    ‖inclusion Ω u‖ = R * ‖inclusion unitDisk (dilationH01 Ω R hR hΩ u)‖ := by
  rw [norm_inclusion_eq_value Ω hOpen.measurableSet,
    norm_inclusion_eq_value unitDisk measurableSet_ball]
  exact norm_value_dilationH01 Ω R hR hΩ u

theorem inclusion_compact_of_subset_ball (Ω : Set ℂ) (hOpen : IsOpen Ω)
    (R : ℝ) (hR : 0 < R) (hΩ : Ω ⊆ ball (0 : ℂ) R) :
    IsCompactOperator (inclusion Ω) := by
  let T := dilationH01 Ω R hR hΩ
  let J₂ := (inclusion unitDisk).comp T
  have hJ₂ : IsCompactOperator J₂ := inclusion_unitDisk_compact.comp_clm T
  apply isCompactOperator_of_norm_control (inclusion Ω) J₂ hJ₂ R hR.le
  intro u
  exact (norm_inclusion_dilationH01 Ω hOpen R hR hΩ u).le

/-- Rellich compactness for every bounded open planar domain, obtained from
the disk by an explicit dilation. No boundary regularity is required. -/
theorem inclusion_compact_of_bounded (Ω : Set ℂ) (hOpen : IsOpen Ω)
    (hBound : Bornology.IsBounded Ω) : IsCompactOperator (inclusion Ω) := by
  obtain ⟨R, hR, hΩ⟩ := hBound.subset_ball_lt 0 (0 : ℂ)
  exact inclusion_compact_of_subset_ball Ω hOpen R hR hΩ

end DirichletBridge

/-! The Dirichlet eigenvalues are defined independently from the eigenvectors
of the actual inverse of the gradient-form operator. The equality below is
proved, rather than used as a definition or an extra hypothesis. -/

noncomputable section

namespace DirichletBridge

open MeasureTheory Set Real
open scoped InnerProductSpace

theorem dirichletResolventZero_compact (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) :
    IsCompactOperator (dirichletResolventZero Ω hbdd) :=
  PolyaBridge.CoerciveForm.formInverse_compact (inclusion Ω)
    (inclusion_compact_of_bounded Ω hopen hbdd) (energyForm Ω)
    (energyForm_coercive Ω hbdd)

/-- The positive Dirichlet eigenvalues, in increasing order with multiplicity.
The unused zeroth index is set to zero. The spectral threshold defining the
inverse values uses orthonormal eigenvectors, independently of min-max. -/
def spectralDirichletEigenvalue (Ω : Set ℂ) (hbdd : Bornology.IsBounded Ω)
    (j : ℕ) : ℝ :=
  if j = 0 then 0 else
    (PolyaBridge.CompactSpectral.spectralEigenvalue (dirichletResolventZero Ω hbdd) j)⁻¹

lemma spectralDirichletEigenvalue_eq_inverse (Ω : Set ℂ)
    (hbdd : Bornology.IsBounded Ω) {j : ℕ} (hj : 1 ≤ j) :
    spectralDirichletEigenvalue Ω hbdd j =
      (PolyaBridge.CompactSpectral.spectralEigenvalue (dirichletResolventZero Ω hbdd) j)⁻¹ := by
  simp only [spectralDirichletEigenvalue, if_neg (by omega : j ≠ 0)]

theorem spectralDirichletEigenvalue_pos (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hne : Ω.Nonempty) (hbdd : Bornology.IsBounded Ω) {j : ℕ} (hj : 1 ≤ j) :
    0 < spectralDirichletEigenvalue Ω hbdd j := by
  rw [spectralDirichletEigenvalue_eq_inverse Ω hbdd hj]
  exact inv_pos.mpr (PolyaBridge.CompactSpectral.spectralEigenvalue_pos
    (dirichletResolventZero_compact Ω hopen hbdd)
    (dirichletResolventZero_symmetric Ω hbdd)
    (dirichletResolventZero_strictPositive Ω hopen hbdd)
    (domainL2_infinite Ω hopen hne) (by omega))

/-- The missing identification between the original smooth-core min-max
and the ordered spectrum of the genuine Dirichlet operator. -/
theorem dirichletEigenvalue_eq_spectral (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hne : Ω.Nonempty) (hbdd : Bornology.IsBounded Ω) {j : ℕ} (hj : 1 ≤ j) :
    dirichletEigenvalue Ω j = ENNReal.ofReal (spectralDirichletEigenvalue Ω hbdd j) := by
  rw [dirichletEigenvalue_eq_sobolevEigenvalue Ω hj,
    sobolevEigenvalue_eq_domainFormMinmax Ω hopen.measurableSet,
    spectralDirichletEigenvalue_eq_inverse Ω hbdd hj]
  exact PolyaBridge.SpectralMinmax.form_minmax_eq_inverse_spectral
    (inclusion Ω) (inclusion_injective Ω hopen.measurableSet) (inclusion_dense Ω hopen)
    (inclusion_compact_of_bounded Ω hopen hbdd) (energyForm Ω)
    (energyForm_coercive Ω hbdd) (energyForm_symmetric Ω)
    (domainL2_infinite Ω hopen hne) (by omega)

theorem variationalEigenvalue_eq_spectral (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hne : Ω.Nonempty) (hbdd : Bornology.IsBounded Ω) (j : ℕ) :
    variationalEigenvalue Ω j = spectralDirichletEigenvalue Ω hbdd j := by
  by_cases hj : j = 0
  · subst j
    simp [variationalEigenvalue, dirichletEigenvalue_zero, spectralDirichletEigenvalue]
  · rw [variationalEigenvalue, dirichletEigenvalue_eq_spectral Ω hopen hne hbdd (by omega),
      ENNReal.toReal_ofReal (spectralDirichletEigenvalue_pos Ω hopen hne hbdd (by omega)).le]

theorem spectralDirichletEigenvalue_mono (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hne : Ω.Nonempty) (hbdd : Bornology.IsBounded Ω) :
    Monotone (spectralDirichletEigenvalue Ω hbdd) := by
  have heq := funext (variationalEigenvalue_eq_spectral Ω hopen hne hbdd)
  rw [← heq]
  exact variationalEigenvalue_mono hopen hne

/-- Each numbered value has a normalized eigenvector in the actual operator
domain, with the eigen-equation for the partial Dirichlet operator itself. -/
theorem spectralDirichletEigenvalue_has_eigenvector (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hne : Ω.Nonempty) (hbdd : Bornology.IsBounded Ω) {j : ℕ} (hj : 1 ≤ j) :
    ∃ u : (dirichletOperator Ω hbdd).domain,
      ‖(u : DomainL2 Ω)‖ = 1 ∧
      dirichletOperator Ω hbdd u = spectralDirichletEigenvalue Ω hbdd j • (u : DomainL2 Ω) := by
  let K := dirichletResolventZero Ω hbdd
  let μ := PolyaBridge.CompactSpectral.spectralEigenvalue K j
  have hμ : 0 < μ := PolyaBridge.CompactSpectral.spectralEigenvalue_pos
    (dirichletResolventZero_compact Ω hopen hbdd)
    (dirichletResolventZero_symmetric Ω hbdd)
    (dirichletResolventZero_strictPositive Ω hopen hbdd)
    (domainL2_infinite Ω hopen hne) (by omega)
  obtain ⟨x, hxnorm, hx⟩ := PolyaBridge.CompactSpectral.exists_eigenvector_at_spectralEigenvalue
    (dirichletResolventZero_compact Ω hopen hbdd)
    (dirichletResolventZero_symmetric Ω hbdd)
    (dirichletResolventZero_strictPositive Ω hopen hbdd)
    (domainL2_infinite Ω hopen hne) (by omega : 0 < j)
  have hdom : x ∈ (dirichletOperator Ω hbdd).domain :=
    PolyaBridge.InverseOperator.eigenvector_mem_domain K μ hμ.ne' x hx
  refine ⟨⟨x, hdom⟩, hxnorm, ?_⟩
  rw [spectralDirichletEigenvalue_eq_inverse Ω hbdd hj]
  exact PolyaBridge.InverseOperator.eigenvector_apply K
    (dirichletResolventZero_injective Ω hopen hbdd) μ hμ.ne' x hx

def spectralDirichletCountingFunction (Ω : Set ℂ) (hbdd : Bornology.IsBounded Ω)
    (E : ℝ) : ℕ := count (spectralDirichletEigenvalue Ω hbdd) E

theorem spectralCounting_eq_variationalCounting (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hne : Ω.Nonempty) (hbdd : Bornology.IsBounded Ω) (E : ℝ) :
    spectralDirichletCountingFunction Ω hbdd E = variationalCountingFunction Ω E := by
  rw [spectralDirichletCountingFunction, variationalCountingFunction,
    funext (variationalEigenvalue_eq_spectral Ω hopen hne hbdd)]

/-- Strict Pólya for the independently defined spectrum of the Dirichlet
gradient-form operator, under precisely the original domain hypotheses. -/
theorem strict_polya_spectral (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (hsc : SimplyConnectedSpace Ω)
    (j : ℕ) (hj : 1 ≤ j) :
    4 * π * j < (volume Ω).toReal * spectralDirichletEigenvalue Ω hbdd j := by
  letI : SimplyConnectedSpace Ω := hsc
  have hne : Ω.Nonempty := Set.nonempty_coe_sort.mp (inferInstance : Nonempty Ω)
  rw [← variationalEigenvalue_eq_spectral Ω hopen hne hbdd j]
  exact strict_polya_real Ω hopen hne hbdd hsc j hj

theorem spectralDirichletCountingSet_finite (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (hsc : SimplyConnectedSpace Ω) (E : ℝ) :
    (countingSet (spectralDirichletEigenvalue Ω hbdd) E).Finite := by
  letI : SimplyConnectedSpace Ω := hsc
  have hne : Ω.Nonempty := Set.nonempty_coe_sort.mp (inferInstance : Nonempty Ω)
  rw [← funext (variationalEigenvalue_eq_spectral Ω hopen hne hbdd)]
  exact variationalCountingFunction_finite Ω hopen hne hbdd hsc E

theorem strict_polya_spectral_counting (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (hsc : SimplyConnectedSpace Ω)
    (E : ℝ) (hE : 0 < E) :
    (spectralDirichletCountingFunction Ω hbdd E : ℝ) < (volume Ω).toReal * E / (4 * π) := by
  letI : SimplyConnectedSpace Ω := hsc
  have hne : Ω.Nonempty := Set.nonempty_coe_sort.mp (inferInstance : Nonempty Ω)
  rw [spectralCounting_eq_variationalCounting Ω hopen hne hbdd E]
  exact strict_polya_counting Ω hopen hbdd hsc E hE

theorem strict_polya_spectral_iff_counting (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (hsc : SimplyConnectedSpace Ω) :
    (∀ j, 1 ≤ j → 4 * π * j < (volume Ω).toReal * spectralDirichletEigenvalue Ω hbdd j) ↔
    (∀ E, 0 < E →
      (spectralDirichletCountingFunction Ω hbdd E : ℝ) < (volume Ω).toReal * E / (4 * π)) := by
  letI : SimplyConnectedSpace Ω := hsc
  have hne : Ω.Nonempty := Set.nonempty_coe_sort.mp (inferInstance : Nonempty Ω)
  have ha : 0 < (volume Ω).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨hopen.measure_pos volume hne, hbdd.measure_lt_top⟩
  have h := growth_iff_count_strict (spectralDirichletEigenvalue Ω hbdd)
    (spectralDirichletEigenvalue_mono Ω hopen hne hbdd)
    (fun j hj => spectralDirichletEigenvalue_pos Ω hopen hne hbdd hj)
    (spectralDirichletCountingSet_finite Ω hopen hbdd hsc) ha (by positivity : 0 < 4 * π)
  convert h using 1
  simp only [spectralDirichletCountingFunction, lt_div_iff₀ (by positivity : 0 < 4 * π),
    mul_comm (4 * π)]


end DirichletBridge

namespace PolyaBridge.SpectralDiscrete

open Set Filter
open scoped InnerProductSpace Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- An orthonormal family contained in a fixed compact set has uniformly bounded size. -/
theorem orthonormal_card_bound_of_compact {K : Set H} (hK : IsCompact K) :
    ∃ N : ℕ, ∀ {j : ℕ} {e : Fin j → H}, Orthonormal ℝ e →
      (∀ i, e i ∈ K) → j ≤ N := by
  classical
  obtain ⟨t, _, ht, hcover⟩ := hK.finite_cover_balls (by norm_num : (0 : ℝ) < 1 / 2)
  letI : Fintype t := ht.fintype
  refine ⟨Fintype.card t, ?_⟩
  intro j e he heK
  have hcenter : ∀ i : Fin j, ∃ y : t, dist (e i) (y : H) < 1 / 2 := by
    intro i
    obtain ⟨y, hy, hball⟩ := Set.mem_iUnion₂.mp (hcover (heK i))
    exact ⟨⟨y, hy⟩, Metric.mem_ball.mp hball⟩
  choose g hg using hcenter
  have hgInjective : Function.Injective g := by
    intro i l hil
    by_contra hne
    have hleft : dist (e i) (g i : H) < 1 / 2 := hg i
    have hright : dist (g i : H) (e l) < 1 / 2 := by
      rw [hil, dist_comm]
      exact hg l
    have hdist : dist (e i) (e l) < 1 := by
      have htriangle := dist_triangle (e i) (g i : H) (e l)
      linarith
    have hsquared : dist (e i) (e l) ^ 2 = 2 := by
      rw [dist_eq_norm, norm_sub_sq_real, he.norm_eq_one i,
        he.norm_eq_one l, he.inner_eq_zero hne]
      norm_num
    have hnonneg : 0 ≤ dist (e i) (e l) := dist_nonneg
    nlinarith
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective g hgInjective

/-- Compactness bounds the number of orthonormal eigenvectors above any positive threshold. -/
theorem spectralThreshold_card_bound {T : H →L[ℝ] H}
    (hCompact : IsCompactOperator T) {s : ℝ} (hs : 0 < s) :
    ∃ N : ℕ, ∀ j : ℕ, s ∈ CompactSpectral.SpectralThreshold T j → j ≤ N := by
  classical
  obtain ⟨K, hK, hTK⟩ := IsCompactOperator.image_closedBall_subset_compact
    (f := T.toLinearMap) hCompact (1 / s)
  obtain ⟨N, hN⟩ := orthonormal_card_bound_of_compact hK
  refine ⟨N, ?_⟩
  intro j hj
  obtain ⟨_, e, he, ν, hν⟩ := hj
  apply hN he
  intro i
  have hνPos : 0 < ν i := hs.trans_le (hν i).2
  apply hTK
  refine ⟨(1 / ν i) • e i, ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr hνPos), he.norm_eq_one i, mul_one]
    exact one_div_le_one_div_of_le hs (hν i).2
  · rw [map_smul]
    change (1 / ν i) • T (e i) = e i
    rw [(hν i).1, smul_smul, one_div,
      inv_mul_cancel₀ hνPos.ne', one_smul]

theorem finite_spectralThreshold_indices {T : H →L[ℝ] H}
    (hCompact : IsCompactOperator T) {s : ℝ} (hs : 0 < s) :
    Set.Finite {j : ℕ | s ∈ CompactSpectral.SpectralThreshold T j} := by
  obtain ⟨N, hN⟩ := spectralThreshold_card_bound hCompact hs
  exact (Set.finite_le_nat N).subset fun j hj => hN j hj

/-- Every value in a finite successive-maximizer family agrees with the
independent threshold definition at its own index. -/
theorem eigenfamily_value_eq_spectralEigenvalue {T : H →L[ℝ] H} {n : ℕ}
    (f : CompactSpectral.PositiveEigenFamily T n) {i : ℕ} (hi : i < n) :
    CompactSpectral.spectralEigenvalue T (i + 1) = f.values i := by
  let g : CompactSpectral.PositiveEigenFamily T (i + 1) :=
    { vectors := f.vectors
      values := f.values
      orthogonal := fun k hk l hl => f.orthogonal k (by omega) l (by omega)
      eigenvector := fun k hk => f.eigenvector k (by omega)
      positive := fun k hk => f.positive k (by omega)
      maximal := fun k hk x hx => f.maximal k (by omega) x hx }
  simpa only [Nat.add_sub_cancel, g] using
    g.spectralEigenvalue_eq_last (by omega : 0 < i + 1)

variable {T : H →L[ℝ] H}
  (hCompact : IsCompactOperator T)
  (hSymmetric : ∀ x y, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ)
  (hPositive : ∀ x : H, x ≠ 0 → 0 < ⟪T x, x⟫_ℝ)
  (hInfinite : ¬ Module.Finite ℝ H)

include hCompact hSymmetric hPositive hInfinite

/-- Every fixed positive spectral threshold is eventually larger than the ordered eigenvalues. -/
theorem eventually_spectralEigenvalue_lt {s : ℝ} (hs : 0 < s) :
    ∀ᶠ j : ℕ in atTop, CompactSpectral.spectralEigenvalue T j < s := by
  obtain ⟨N, hN⟩ := spectralThreshold_card_bound hCompact hs
  refine eventually_atTop.2 ⟨N + 1, ?_⟩
  intro j hj
  have hjPos : 0 < j := by omega
  obtain ⟨f⟩ := CompactSpectral.exists_positive_eigenfamily
    hCompact hSymmetric hPositive hInfinite j
  by_contra hlt
  have hmem : s ∈ CompactSpectral.SpectralThreshold T j :=
    (f.mem_threshold_iff hjPos).mpr ⟨hs, le_of_not_gt hlt⟩
  have hbound := hN j hmem
  omega

/-- The independently defined positive eigenvalues of a compact, strictly positive
operator on an infinite-dimensional real inner-product space tend to zero. -/
theorem spectralEigenvalue_tendsto_zero :
    Tendsto (CompactSpectral.spectralEigenvalue T) atTop (𝓝 (0 : ℝ)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with j hj
    exact ha.trans (CompactSpectral.spectralEigenvalue_pos
      hCompact hSymmetric hPositive hInfinite (by omega : 0 < j))
  · intro b hb
    exact eventually_spectralEigenvalue_lt hCompact hSymmetric hPositive hInfinite hb

theorem spectralEigenvalue_tendsto_zero_from_above :
    Tendsto (CompactSpectral.spectralEigenvalue T) atTop (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨spectralEigenvalue_tendsto_zero hCompact hSymmetric hPositive hInfinite, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with j hj
  exact CompactSpectral.spectralEigenvalue_pos
    hCompact hSymmetric hPositive hInfinite (by omega : 0 < j)

theorem reciprocal_spectralEigenvalue_tendsto_atTop :
    Tendsto (fun j => (CompactSpectral.spectralEigenvalue T j)⁻¹) atTop atTop :=
  (spectralEigenvalue_tendsto_zero_from_above
    hCompact hSymmetric hPositive hInfinite).inv_tendsto_nhdsGT_zero

/-- The spectral reciprocals diverge to infinity, in the extended nonnegative reals. -/
theorem inverseSpectralEigenvalue_tendsto_top :
    Tendsto (CompactSpectral.inverseSpectralEigenvalue T) atTop (𝓝 (⊤ : ENNReal)) := by
  change Tendsto (fun j => ENNReal.ofReal (1 / CompactSpectral.spectralEigenvalue T j))
    atTop (𝓝 (⊤ : ENNReal))
  simp_rw [one_div]
  exact ENNReal.tendsto_ofReal_nhds_top.mpr
    (reciprocal_spectralEigenvalue_tendsto_atTop hCompact hSymmetric hPositive hInfinite)

/-- Every positive eigenvalue occurs in the threshold-indexed sequence.
No compatibility between choices of finite eigenfamilies is assumed. -/
theorem every_positive_eigenvalue_is_indexed {μ : ℝ} (hμ : 0 < μ)
    {x : H} (hx : x ≠ 0) (hTx : T x = μ • x) :
    ∃ j : ℕ, 0 < j ∧ CompactSpectral.spectralEigenvalue T j = μ := by
  by_contra hNo
  have hNoValue : ∀ j : ℕ, 0 < j → CompactSpectral.spectralEigenvalue T j ≠ μ := by
    intro j hj hEq
    exact hNo ⟨j, hj, hEq⟩
  obtain ⟨n, hnLt, hnPos⟩ :=
    ((eventually_spectralEigenvalue_lt hCompact hSymmetric hPositive hInfinite hμ).and
      (eventually_ge_atTop (1 : ℕ))).exists
  obtain ⟨f⟩ := CompactSpectral.exists_positive_eigenfamily
    hCompact hSymmetric hPositive hInfinite n
  have hValuesNe : ∀ i < n, f.values i ≠ μ := by
    intro i hi
    rw [← eigenfamily_value_eq_spectralEigenvalue f hi]
    exact hNoValue (i + 1) (by omega)
  have hOrth : ∀ i < n - 1, ⟪f.vectors i, x⟫_ℝ = 0 := by
    intro i hi
    have hiN : i < n := by omega
    have hSym := hSymmetric (f.vectors i) x
    rw [f.eigenvector i hiN, hTx, real_inner_smul_left, real_inner_smul_right] at hSym
    have hProduct : f.values i * ⟪f.vectors i, x⟫_ℝ =
        μ * ⟪f.vectors i, x⟫_ℝ := by
      simpa only [mul_comm] using hSym
    exact (mul_eq_mul_right_iff.mp hProduct).resolve_left (hValuesNe i hiN)
  have hUpper := f.maximal (n - 1) (by omega) x hOrth
  rw [hTx, real_inner_smul_left, real_inner_self_eq_norm_sq] at hUpper
  have hNormPos : 0 < ‖x‖ ^ 2 := by positivity
  have hμLe : μ ≤ f.values (n - 1) := le_of_mul_le_mul_right hUpper hNormPos
  rw [← f.spectralEigenvalue_eq_last (by omega : 0 < n)] at hμLe
  exact (not_le_of_gt hnLt) hμLe

theorem eigenvalue_iff_indexed {μ : ℝ} (hμ : 0 < μ) :
    (∃ x : H, x ≠ 0 ∧ T x = μ • x) ↔
      ∃ j : ℕ, 0 < j ∧ CompactSpectral.spectralEigenvalue T j = μ := by
  constructor
  · rintro ⟨x, hx, hTx⟩
    exact every_positive_eigenvalue_is_indexed
      hCompact hSymmetric hPositive hInfinite hμ hx hTx
  · rintro ⟨j, hj, hEq⟩
    obtain ⟨x, hxNorm, hTx⟩ := CompactSpectral.exists_eigenvector_at_spectralEigenvalue
      hCompact hSymmetric hPositive hInfinite hj
    refine ⟨x, ?_, ?_⟩
    · intro hx
      rw [hx, norm_zero] at hxNorm
      norm_num at hxNorm
    · simpa only [hEq] using hTx

end PolyaBridge.SpectralDiscrete

noncomputable section

namespace DirichletBridge

open MeasureTheory Set Filter
open scoped Topology

theorem spectralDirichletEigenvalue_tendsto_atTop (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hne : Ω.Nonempty) (hbdd : Bornology.IsBounded Ω) :
    Tendsto (spectralDirichletEigenvalue Ω hbdd) atTop atTop := by
  have h := PolyaBridge.SpectralDiscrete.reciprocal_spectralEigenvalue_tendsto_atTop
    (dirichletResolventZero_compact Ω hopen hbdd)
    (dirichletResolventZero_symmetric Ω hbdd)
    (dirichletResolventZero_strictPositive Ω hopen hbdd)
    (domainL2_infinite Ω hopen hne)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with j hj
  exact (spectralDirichletEigenvalue_eq_inverse Ω hbdd hj).symm

/-- Spectral counting is finite on every bounded nonempty open domain,
independently of the Pólya inequality or simple connectivity. -/
theorem spectralDirichletCountingSet_finite_of_bounded (Ω : Set ℂ)
    (hopen : IsOpen Ω) (hne : Ω.Nonempty) (hbdd : Bornology.IsBounded Ω) (E : ℝ) :
    (countingSet (spectralDirichletEigenvalue Ω hbdd) E).Finite := by
  have hev := (spectralDirichletEigenvalue_tendsto_atTop Ω hopen hne hbdd).eventually
    (eventually_gt_atTop E)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  apply (Set.finite_Iio N).subset
  intro j hj
  by_contra hjN
  exact (not_lt_of_ge hj.2) (hN j (Nat.le_of_not_gt hjN))

theorem spectralDirichletCountingFunction_eq_zero (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hne : Ω.Nonempty) (hbdd : Bornology.IsBounded Ω) {E : ℝ} (hE : E ≤ 0) :
    spectralDirichletCountingFunction Ω hbdd E = 0 := by
  have hset : countingSet (spectralDirichletEigenvalue Ω hbdd) E = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro j hj
    exact (not_lt_of_ge (hj.2.trans hE))
      (spectralDirichletEigenvalue_pos Ω hopen hne hbdd hj.1)
  simp only [spectralDirichletCountingFunction, count, hset, Set.ncard_empty]

end DirichletBridge

/-! Complexification of the actual real L² resolvent. Real and imaginary parts
identify each complex eigenspace with two copies of its real eigenspace as a real
vector space; the complex multiplicity itself equals the real multiplicity. -/

noncomputable section

namespace DirichletBridge

open MeasureTheory Set Metric Topology
open scoped InnerProductSpace

abbrev ComplexDomainL2 (Ω : Set ℂ) := Lp ℂ 2 (volume.restrict Ω)

def reL2 (Ω : Set ℂ) : ComplexDomainL2 Ω →L[ℝ] DomainL2 Ω :=
  Complex.reCLM.compLpL 2 (volume.restrict Ω)

def imL2 (Ω : Set ℂ) : ComplexDomainL2 Ω →L[ℝ] DomainL2 Ω :=
  Complex.imCLM.compLpL 2 (volume.restrict Ω)

def ofRealL2 (Ω : Set ℂ) : DomainL2 Ω →L[ℝ] ComplexDomainL2 Ω :=
  Complex.ofRealCLM.compLpL 2 (volume.restrict Ω)

lemma reL2_coeFn (Ω : Set ℂ) (f : ComplexDomainL2 Ω) :
    reL2 Ω f =ᵐ[volume.restrict Ω] fun z => (f z).re :=
  Complex.reCLM.coeFn_compLpL f

lemma imL2_coeFn (Ω : Set ℂ) (f : ComplexDomainL2 Ω) :
    imL2 Ω f =ᵐ[volume.restrict Ω] fun z => (f z).im :=
  Complex.imCLM.coeFn_compLpL f

lemma ofRealL2_coeFn (Ω : Set ℂ) (f : DomainL2 Ω) :
    ofRealL2 Ω f =ᵐ[volume.restrict Ω] fun z => (f z : ℂ) :=
  Complex.ofRealCLM.coeFn_compLpL f

@[simp] lemma reL2_ofRealL2 (Ω : Set ℂ) (f : DomainL2 Ω) :
    reL2 Ω (ofRealL2 Ω f) = f := by
  apply Lp.ext
  filter_upwards [reL2_coeFn Ω (ofRealL2 Ω f), ofRealL2_coeFn Ω f] with z hre hof
  rw [hre, hof]
  simp

@[simp] lemma imL2_ofRealL2 (Ω : Set ℂ) (f : DomainL2 Ω) :
    imL2 Ω (ofRealL2 Ω f) = 0 := by
  apply Lp.ext
  filter_upwards [imL2_coeFn Ω (ofRealL2 Ω f), ofRealL2_coeFn Ω f,
    Lp.coeFn_zero (E := ℝ) (p := 2) (μ := volume.restrict Ω)] with z him hof hzero
  rw [him, hof, hzero]
  simp

lemma reL2_smul_complex (Ω : Set ℂ) (c : ℂ) (f : ComplexDomainL2 Ω) :
    reL2 Ω (c • f) = c.re • reL2 Ω f - c.im • imL2 Ω f := by
  apply Lp.ext
  filter_upwards [reL2_coeFn Ω (c • f), reL2_coeFn Ω f, imL2_coeFn Ω f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c.re (reL2 Ω f),
    Lp.coeFn_smul c.im (imL2 Ω f),
    Lp.coeFn_sub (c.re • reL2 Ω f) (c.im • imL2 Ω f)] with z hleft hre him hcf hr hi hsub
  rw [hleft, hcf, hsub]
  simp only [Pi.sub_apply, Pi.smul_apply]
  rw [hr, hi]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_re]
  rw [hre, him]

lemma imL2_smul_complex (Ω : Set ℂ) (c : ℂ) (f : ComplexDomainL2 Ω) :
    imL2 Ω (c • f) = c.re • imL2 Ω f + c.im • reL2 Ω f := by
  apply Lp.ext
  filter_upwards [imL2_coeFn Ω (c • f), reL2_coeFn Ω f, imL2_coeFn Ω f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c.re (imL2 Ω f),
    Lp.coeFn_smul c.im (reL2 Ω f),
    Lp.coeFn_add (c.re • imL2 Ω f) (c.im • reL2 Ω f)] with z hleft hre him hcf hr hi hadd
  rw [hleft, hcf, hadd]
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [hr, hi]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_im]
  rw [hre, him]

@[simp] lemma reL2_I_smul (Ω : Set ℂ) (f : ComplexDomainL2 Ω) :
    reL2 Ω (Complex.I • f) = -imL2 Ω f := by
  simp [reL2_smul_complex]

@[simp] lemma imL2_I_smul (Ω : Set ℂ) (f : ComplexDomainL2 Ω) :
    imL2 Ω (Complex.I • f) = reL2 Ω f := by
  simp [imL2_smul_complex]

lemma ofReal_reL2_add_I_imL2 (Ω : Set ℂ) (f : ComplexDomainL2 Ω) :
    ofRealL2 Ω (reL2 Ω f) + Complex.I • ofRealL2 Ω (imL2 Ω f) = f := by
  apply Lp.ext
  filter_upwards [ofRealL2_coeFn Ω (reL2 Ω f), ofRealL2_coeFn Ω (imL2 Ω f),
    reL2_coeFn Ω f, imL2_coeFn Ω f,
    Lp.coeFn_smul Complex.I (ofRealL2 Ω (imL2 Ω f)),
    Lp.coeFn_add (ofRealL2 Ω (reL2 Ω f)) (Complex.I • ofRealL2 Ω (imL2 Ω f))]
      with z hor hoi hre him hsmul hadd
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hor, hoi, hre, him]
  simpa only [mul_comm] using Complex.re_add_im (f z)

lemma reL2_imL2_ext (Ω : Set ℂ) {f g : ComplexDomainL2 Ω}
    (hre : reL2 Ω f = reL2 Ω g) (him : imL2 Ω f = imL2 Ω g) : f = g := by
  rw [← ofReal_reL2_add_I_imL2 Ω f, ← ofReal_reL2_add_I_imL2 Ω g, hre, him]

lemma ofRealL2_inner (Ω : Set ℂ) (f g : DomainL2 Ω) :
    ⟪ofRealL2 Ω f, ofRealL2 Ω g⟫_ℂ = (⟪f, g⟫_ℝ : ℂ) := by
  rw [L2.inner_def, inner_domainL2]
  calc
    (∫ z, ⟪ofRealL2 Ω f z, ofRealL2 Ω g z⟫_ℂ ∂(volume.restrict Ω)) =
        ∫ z, ((f z * g z : ℝ) : ℂ) ∂(volume.restrict Ω) := by
      apply integral_congr_ae
      filter_upwards [ofRealL2_coeFn Ω f, ofRealL2_coeFn Ω g] with z hf hg
      rw [hf, hg]
      simp [RCLike.inner_apply, mul_comm]
    _ = (∫ z, f z * g z ∂(volume.restrict Ω) : ℝ) := integral_complex_ofReal

lemma complexDomainL2_inner_re_im (Ω : Set ℂ) (f g : ComplexDomainL2 Ω) :
    ⟪f, g⟫_ℂ =
      (⟪reL2 Ω f, reL2 Ω g⟫_ℝ + ⟪imL2 Ω f, imL2 Ω g⟫_ℝ : ℝ) +
        Complex.I * (⟪reL2 Ω f, imL2 Ω g⟫_ℝ - ⟪imL2 Ω f, reL2 Ω g⟫_ℝ : ℝ) := by
  calc
    ⟪f, g⟫_ℂ = ⟪ofRealL2 Ω (reL2 Ω f) + Complex.I • ofRealL2 Ω (imL2 Ω f),
        ofRealL2 Ω (reL2 Ω g) + Complex.I • ofRealL2 Ω (imL2 Ω g)⟫_ℂ := by
      rw [ofReal_reL2_add_I_imL2, ofReal_reL2_add_I_imL2]
    _ = _ := by
      simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
        ofRealL2_inner]
      apply Complex.ext <;> simp
      ring

def complexifyReal (Ω : Set ℂ) (T : DomainL2 Ω →L[ℝ] DomainL2 Ω) :
    ComplexDomainL2 Ω →L[ℝ] ComplexDomainL2 Ω :=
  ((ofRealL2 Ω).comp (T.comp (reL2 Ω))) +
    Complex.I • ((ofRealL2 Ω).comp (T.comp (imL2 Ω)))

@[simp] lemma reL2_complexifyReal (Ω : Set ℂ) (T : DomainL2 Ω →L[ℝ] DomainL2 Ω)
    (f : ComplexDomainL2 Ω) : reL2 Ω (complexifyReal Ω T f) = T (reL2 Ω f) := by
  simp [complexifyReal]

@[simp] lemma imL2_complexifyReal (Ω : Set ℂ) (T : DomainL2 Ω →L[ℝ] DomainL2 Ω)
    (f : ComplexDomainL2 Ω) : imL2 Ω (complexifyReal Ω T f) = T (imL2 Ω f) := by
  simp [complexifyReal]

def complexify (Ω : Set ℂ) (T : DomainL2 Ω →L[ℝ] DomainL2 Ω) :
    ComplexDomainL2 Ω →L[ℂ] ComplexDomainL2 Ω where
  toFun := complexifyReal Ω T
  map_add' := (complexifyReal Ω T).map_add
  map_smul' c f := by
    apply reL2_imL2_ext Ω
    · simp [reL2_smul_complex, map_sub, map_smul]
    · simp [imL2_smul_complex, map_add, map_smul]
  cont := (complexifyReal Ω T).continuous

@[simp] lemma reL2_complexify (Ω : Set ℂ) (T : DomainL2 Ω →L[ℝ] DomainL2 Ω)
    (f : ComplexDomainL2 Ω) : reL2 Ω (complexify Ω T f) = T (reL2 Ω f) :=
  reL2_complexifyReal Ω T f

@[simp] lemma imL2_complexify (Ω : Set ℂ) (T : DomainL2 Ω →L[ℝ] DomainL2 Ω)
    (f : ComplexDomainL2 Ω) : imL2 Ω (complexify Ω T f) = T (imL2 Ω f) :=
  imL2_complexifyReal Ω T f

theorem complexify_compact (Ω : Set ℂ) (T : DomainL2 Ω →L[ℝ] DomainL2 Ω)
    (hT : IsCompactOperator T) : IsCompactOperator (complexify Ω T) := by
  have hr : IsCompactOperator ((ofRealL2 Ω).comp (T.comp (reL2 Ω))) :=
    (hT.comp_clm (reL2 Ω)).clm_comp (ofRealL2 Ω)
  have hi : IsCompactOperator ((ofRealL2 Ω).comp (T.comp (imL2 Ω))) :=
    (hT.comp_clm (imL2 Ω)).clm_comp (ofRealL2 Ω)
  change IsCompactOperator (complexifyReal Ω T)
  exact hr.add (hi.smul Complex.I)

theorem complexify_injective (Ω : Set ℂ) (T : DomainL2 Ω →L[ℝ] DomainL2 Ω)
    (hT : Function.Injective T) : Function.Injective (complexify Ω T) := by
  intro f g hfg
  apply reL2_imL2_ext Ω
  · apply hT
    simpa using congrArg (reL2 Ω) hfg
  · apply hT
    simpa using congrArg (imL2 Ω) hfg

theorem complexify_symmetric (Ω : Set ℂ) (T : DomainL2 Ω →L[ℝ] DomainL2 Ω)
    (hT : T.IsSymmetric) : (complexify Ω T).IsSymmetric := by
  intro f g
  change ⟪complexify Ω T f, g⟫_ℂ = ⟪f, complexify Ω T g⟫_ℂ
  have hT' : ∀ x y : DomainL2 Ω, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ := hT
  simp only [complexDomainL2_inner_re_im, reL2_complexify, imL2_complexify]
  rw [hT' (reL2 Ω f) (reL2 Ω g), hT' (imL2 Ω f) (imL2 Ω g),
    hT' (reL2 Ω f) (imL2 Ω g), hT' (imL2 Ω f) (reL2 Ω g)]

theorem complexify_strictPositive (Ω : Set ℂ) (T : DomainL2 Ω →L[ℝ] DomainL2 Ω)
    (hT : ∀ f : DomainL2 Ω, f ≠ 0 → 0 < ⟪T f, f⟫_ℝ)
    (f : ComplexDomainL2 Ω) (hf : f ≠ 0) :
    0 < (⟪complexify Ω T f, f⟫_ℂ).re := by
  have hr : 0 ≤ ⟪T (reL2 Ω f), reL2 Ω f⟫_ℝ := by
    by_cases hzero : reL2 Ω f = 0
    · simp [hzero]
    · exact (hT _ hzero).le
  have hi : 0 ≤ ⟪T (imL2 Ω f), imL2 Ω f⟫_ℝ := by
    by_cases hzero : imL2 Ω f = 0
    · simp [hzero]
    · exact (hT _ hzero).le
  have hne : reL2 Ω f ≠ 0 ∨ imL2 Ω f ≠ 0 := by
    by_cases hre : reL2 Ω f = 0
    · right
      intro him
      apply hf
      apply reL2_imL2_ext Ω
      · simpa using hre
      · simpa using him
    · exact Or.inl hre
  simp only [complexDomainL2_inner_re_im, reL2_complexify, imL2_complexify,
    Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  rcases hne with hre | him
  · exact add_pos_of_pos_of_nonneg (hT _ hre) hi
  · exact add_pos_of_nonneg_of_pos hr (hT _ him)

theorem mem_complexified_eigenspace_iff (Ω : Set ℂ)
    (T : DomainL2 Ω →L[ℝ] DomainL2 Ω) (μ : ℝ) (f : ComplexDomainL2 Ω) :
    f ∈ Module.End.eigenspace (complexify Ω T).toLinearMap (μ : ℂ) ↔
      reL2 Ω f ∈ Module.End.eigenspace T.toLinearMap μ ∧
      imL2 Ω f ∈ Module.End.eigenspace T.toLinearMap μ := by
  simp only [Module.End.mem_eigenspace_iff]
  constructor
  · intro h
    constructor
    · have hr := congrArg (reL2 Ω) h
      change reL2 Ω ((complexify Ω T) f) = reL2 Ω ((μ : ℂ) • f) at hr
      rw [reL2_complexify, reL2_smul_complex] at hr
      simpa using hr
    · have hi := congrArg (imL2 Ω) h
      change imL2 Ω ((complexify Ω T) f) = imL2 Ω ((μ : ℂ) • f) at hi
      rw [imL2_complexify, imL2_smul_complex] at hi
      simpa using hi
  · rintro ⟨hr, hi⟩
    apply reL2_imL2_ext Ω
    · change reL2 Ω ((complexify Ω T) f) = reL2 Ω ((μ : ℂ) • f)
      rw [reL2_complexify, reL2_smul_complex]
      simpa using hr
    · change imL2 Ω ((complexify Ω T) f) = imL2 Ω ((μ : ℂ) • f)
      rw [imL2_complexify, imL2_smul_complex]
      simpa using hi

theorem complexify_hasEigenvalue_iff (Ω : Set ℂ)
    (T : DomainL2 Ω →L[ℝ] DomainL2 Ω) (μ : ℝ) :
    Module.End.HasEigenvalue (complexify Ω T).toLinearMap (μ : ℂ) ↔
      Module.End.HasEigenvalue T.toLinearMap μ := by
  constructor
  · intro hμ
    obtain ⟨f, hf⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hμ
    obtain ⟨hfe, hfne⟩ := Module.End.hasEigenvector_iff.mp hf
    have hRI := (mem_complexified_eigenspace_iff Ω T μ f).mp hfe
    by_cases hre : reL2 Ω f = 0
    · have him : imL2 Ω f ≠ 0 := by
        intro him
        apply hfne
        apply reL2_imL2_ext Ω
        · simpa using hre
        · simpa using him
      exact Module.End.hasEigenvalue_of_hasEigenvector ⟨hRI.2, him⟩
    · exact Module.End.hasEigenvalue_of_hasEigenvector ⟨hRI.1, hre⟩
  · intro hμ
    obtain ⟨f, hf⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hμ
    obtain ⟨hfe, hfne⟩ := Module.End.hasEigenvector_iff.mp hf
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨?_, ?_⟩
    · apply (mem_complexified_eigenspace_iff Ω T μ (ofRealL2 Ω f)).mpr
      constructor
      · simpa using hfe
      · simp
    · intro hzero
      exact hfne (by simpa using congrArg (reL2 Ω) hzero)

theorem complexify_hasEigenvalue_real (Ω : Set ℂ)
    (T : DomainL2 Ω →L[ℝ] DomainL2 Ω) (hT : T.IsSymmetric)
    (μ : ℂ) (hμ : Module.End.HasEigenvalue (complexify Ω T).toLinearMap μ) :
    (μ.re : ℂ) = μ := by
  exact Complex.conj_eq_iff_re.mp
    ((complexify_symmetric Ω T hT).conj_eigenvalue_eq_self hμ)

def eigenspaceReImEquiv (Ω : Set ℂ) (T : DomainL2 Ω →L[ℝ] DomainL2 Ω) (μ : ℝ) :
    Module.End.eigenspace (complexify Ω T).toLinearMap (μ : ℂ) ≃ₗ[ℝ]
      (Module.End.eigenspace T.toLinearMap μ × Module.End.eigenspace T.toLinearMap μ) where
  toFun f :=
    (⟨reL2 Ω f, ((mem_complexified_eigenspace_iff Ω T μ f).mp f.property).1⟩,
     ⟨imL2 Ω f, ((mem_complexified_eigenspace_iff Ω T μ f).mp f.property).2⟩)
  invFun p := ⟨ofRealL2 Ω p.1 + Complex.I • ofRealL2 Ω p.2, by
    apply (mem_complexified_eigenspace_iff Ω T μ _).mpr
    simp [p.1.property, p.2.property]⟩
  left_inv f := by
    apply Subtype.ext
    exact ofReal_reL2_add_I_imL2 Ω f
  right_inv p := by
    apply Prod.ext <;> apply Subtype.ext <;> simp
  map_add' f g := by
    apply Prod.ext <;> apply Subtype.ext <;> simp
  map_smul' c f := by
    apply Prod.ext <;> apply Subtype.ext <;> simp

/-- This is complex multiplicity, not the twice-as-large underlying real dimension. -/
theorem finrank_complexified_eigenspace (Ω : Set ℂ)
    (T : DomainL2 Ω →L[ℝ] DomainL2 Ω) (μ : ℝ)
    [Module.Finite ℝ (Module.End.eigenspace T.toLinearMap μ)] :
    Module.finrank ℂ (Module.End.eigenspace (complexify Ω T).toLinearMap (μ : ℂ)) =
      Module.finrank ℝ (Module.End.eigenspace T.toLinearMap μ) := by
  let e := eigenspaceReImEquiv Ω T μ
  letI : Module.Finite ℝ (Module.End.eigenspace (complexify Ω T).toLinearMap (μ : ℂ)) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  letI : Module.Finite ℂ (Module.End.eigenspace (complexify Ω T).toLinearMap (μ : ℂ)) :=
    Module.Finite.of_restrictScalars_finite ℝ ℂ _
  have hdim := e.finrank_eq
  have hreal :
      Module.finrank ℝ (Module.End.eigenspace (complexify Ω T).toLinearMap (μ : ℂ)) =
        2 * Module.finrank ℂ (Module.End.eigenspace (complexify Ω T).toLinearMap (μ : ℂ)) :=
    finrank_real_of_complex _
  simp only [Module.finrank_prod] at hdim
  omega

/-- A nonzero eigenspace of an actual compact operator is finite dimensional. -/
theorem compact_eigenspace_finite {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (T : H →L[ℝ] H) (hT : IsCompactOperator T)
    (μ : ℝ) (hμ : μ ≠ 0) : Module.Finite ℝ (Module.End.eigenspace T.toLinearMap μ) := by
  let E := Module.End.eigenspace T.toLinearMap μ
  have hclosed : IsClosed (E : Set H) := by
    have hE : (E : Set H) = {x : H | T x = μ • x} := by
      ext x
      exact Module.End.mem_eigenspace_iff
    rw [hE]
    exact isClosed_eq T.continuous (continuous_const.smul continuous_id)
  have hInvariant : ∀ x ∈ E, T.toLinearMap x ∈ E := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [hx, map_smul, hx]
  have hR : IsCompactOperator (T.toLinearMap.restrict hInvariant) :=
    hT.restrict hInvariant hclosed
  have hid : IsCompactOperator (LinearMap.id : E →ₗ[ℝ] E) := by
    have h := hR.smul μ⁻¹
    convert h using 1
    funext x
    apply Subtype.ext
    change (x : H) = μ⁻¹ • T (x : H)
    have hx : T (x : H) = μ • (x : H) := Module.End.mem_eigenspace_iff.mp x.property
    rw [hx, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  have hball := hid.isCompact_closure_image_closedBall 1
  simp only [LinearMap.id_coe, image_id, isClosed_closedBall.closure_eq] at hball
  exact FiniteDimensional.of_isCompact_closedBall ℝ zero_lt_one hball

theorem finrank_complexified_compact_eigenspace (Ω : Set ℂ)
    (T : DomainL2 Ω →L[ℝ] DomainL2 Ω) (hT : IsCompactOperator T)
    (μ : ℝ) (hμ : μ ≠ 0) :
    Module.finrank ℂ (Module.End.eigenspace (complexify Ω T).toLinearMap (μ : ℂ)) =
      Module.finrank ℝ (Module.End.eigenspace T.toLinearMap μ) := by
  letI := compact_eigenspace_finite T hT μ hμ
  exact finrank_complexified_eigenspace Ω T μ

def complexDirichletResolventZero (Ω : Set ℂ) (hbdd : Bornology.IsBounded Ω) :
    ComplexDomainL2 Ω →L[ℂ] ComplexDomainL2 Ω :=
  complexify Ω (dirichletResolventZero Ω hbdd)

theorem complexDirichletResolventZero_eigenspace_iff (Ω : Set ℂ)
    (hbdd : Bornology.IsBounded Ω) (μ : ℝ) (f : ComplexDomainL2 Ω) :
    f ∈ Module.End.eigenspace (complexDirichletResolventZero Ω hbdd).toLinearMap (μ : ℂ) ↔
      reL2 Ω f ∈ Module.End.eigenspace (dirichletResolventZero Ω hbdd).toLinearMap μ ∧
      imL2 Ω f ∈ Module.End.eigenspace (dirichletResolventZero Ω hbdd).toLinearMap μ :=
  mem_complexified_eigenspace_iff Ω (dirichletResolventZero Ω hbdd) μ f

theorem complexDirichletResolventZero_compact (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) :
    IsCompactOperator (complexDirichletResolventZero Ω hbdd) :=
  complexify_compact Ω (dirichletResolventZero Ω hbdd)
    (dirichletResolventZero_compact Ω hopen hbdd)

theorem complexDirichletResolventZero_injective (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) :
    Function.Injective (complexDirichletResolventZero Ω hbdd) :=
  complexify_injective Ω (dirichletResolventZero Ω hbdd)
    (dirichletResolventZero_injective Ω hopen hbdd)

theorem complexDirichletResolventZero_symmetric (Ω : Set ℂ)
    (hbdd : Bornology.IsBounded Ω) : (complexDirichletResolventZero Ω hbdd).IsSymmetric :=
  complexify_symmetric Ω (dirichletResolventZero Ω hbdd)
    (dirichletResolventZero_symmetric Ω hbdd)

theorem complexDirichletResolventZero_strictPositive (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (f : ComplexDomainL2 Ω) (hf : f ≠ 0) :
    0 < (⟪complexDirichletResolventZero Ω hbdd f, f⟫_ℂ).re :=
  complexify_strictPositive Ω (dirichletResolventZero Ω hbdd)
    (dirichletResolventZero_strictPositive Ω hopen hbdd) f hf

theorem complexDirichletResolventZero_multiplicity (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (μ : ℝ) (hμ : μ ≠ 0) :
    Module.finrank ℂ
        (Module.End.eigenspace (complexDirichletResolventZero Ω hbdd).toLinearMap (μ : ℂ)) =
      Module.finrank ℝ (Module.End.eigenspace (dirichletResolventZero Ω hbdd).toLinearMap μ) :=
  finrank_complexified_compact_eigenspace Ω (dirichletResolventZero Ω hbdd)
    (dirichletResolventZero_compact Ω hopen hbdd) μ hμ

theorem complexDirichletResolventZero_hasEigenvalue_iff (Ω : Set ℂ)
    (hbdd : Bornology.IsBounded Ω) (μ : ℝ) :
    Module.End.HasEigenvalue (complexDirichletResolventZero Ω hbdd).toLinearMap (μ : ℂ) ↔
      Module.End.HasEigenvalue (dirichletResolventZero Ω hbdd).toLinearMap μ :=
  complexify_hasEigenvalue_iff Ω (dirichletResolventZero Ω hbdd) μ

theorem complexDirichletResolventZero_hasEigenvalue_real (Ω : Set ℂ)
    (hbdd : Bornology.IsBounded Ω) (μ : ℂ)
    (hμ : Module.End.HasEigenvalue (complexDirichletResolventZero Ω hbdd).toLinearMap μ) :
    (μ.re : ℂ) = μ :=
  complexify_hasEigenvalue_real Ω (dirichletResolventZero Ω hbdd)
    (dirichletResolventZero_symmetric Ω hbdd) μ hμ

end DirichletBridge

/-! The complex zero-boundary form domain is represented by its value and two
weak derivatives. Its real and imaginary jets lie in the actual real H₀¹ graph.
Thus this is the complexification of that graph, with the native complex Hilbert
norm inherited from three copies of L²(Ω;ℂ). -/

noncomputable section

set_option synthInstance.maxHeartbeats 200000

namespace DirichletBridge

open MeasureTheory Set Metric Topology
open scoped InnerProductSpace

abbrev RealDomainJet (Ω : Set ℂ) := PiLp 2 (fun _ : Fin 3 => DomainL2 Ω)
abbrev ComplexDomainJet (Ω : Set ℂ) := PiLp 2 (fun _ : Fin 3 => ComplexDomainL2 Ω)

def realDomainJet (Ω : Set ℂ) : H01 Ω →L[ℝ] RealDomainJet Ω :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => DomainL2 Ω)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![inclusion Ω, domainGradient Ω 0, domainGradient Ω 1])

@[simp] lemma realDomainJet_apply (Ω : Set ℂ) (u : H01 Ω) :
    realDomainJet Ω u = WithLp.toLp 2
      ![inclusion Ω u, domainGradient Ω 0 u, domainGradient Ω 1 u] := by
  apply PiLp.ext
  intro i
  fin_cases i <;> rfl

lemma norm_realDomainJet (Ω : Set ℂ) (hΩ : MeasurableSet Ω) (u : H01 Ω) :
    ‖realDomainJet Ω u‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, norm_H01_sq]
  simp only [realDomainJet_apply, Fin.sum_univ_succ, Fin.sum_univ_zero,
    add_zero, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_succ,
    norm_inclusion_eq_value Ω hΩ, norm_domainGradient_eq_gradient Ω hΩ, energy]

def realDomainJetIsometry (Ω : Set ℂ) (hΩ : MeasurableSet Ω) :
    H01 Ω →ₗᵢ[ℝ] RealDomainJet Ω where
  toLinearMap := (realDomainJet Ω).toLinearMap
  norm_map' := norm_realDomainJet Ω hΩ

def realJetPart (Ω : Set ℂ) : ComplexDomainJet Ω →L[ℝ] RealDomainJet Ω :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => DomainL2 Ω)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i =>
      (reL2 Ω).comp (PiLp.proj 2 (fun _ : Fin 3 => ComplexDomainL2 Ω) i :
        ComplexDomainJet Ω →L[ℝ] ComplexDomainL2 Ω)))

def imagJetPart (Ω : Set ℂ) : ComplexDomainJet Ω →L[ℝ] RealDomainJet Ω :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => DomainL2 Ω)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i =>
      (imL2 Ω).comp (PiLp.proj 2 (fun _ : Fin 3 => ComplexDomainL2 Ω) i :
        ComplexDomainJet Ω →L[ℝ] ComplexDomainL2 Ω)))

def ofRealJet (Ω : Set ℂ) : RealDomainJet Ω →L[ℝ] ComplexDomainJet Ω :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ComplexDomainL2 Ω)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i =>
      (ofRealL2 Ω).comp (PiLp.proj 2 (fun _ : Fin 3 => DomainL2 Ω) i)))

@[simp] lemma realJetPart_apply (Ω : Set ℂ) (x : ComplexDomainJet Ω) (i : Fin 3) :
    realJetPart Ω x i = reL2 Ω (x i) := rfl

@[simp] lemma imagJetPart_apply (Ω : Set ℂ) (x : ComplexDomainJet Ω) (i : Fin 3) :
    imagJetPart Ω x i = imL2 Ω (x i) := rfl

@[simp] lemma ofRealJet_apply (Ω : Set ℂ) (x : RealDomainJet Ω) (i : Fin 3) :
    ofRealJet Ω x i = ofRealL2 Ω (x i) := rfl

@[simp] lemma realJetPart_ofRealJet (Ω : Set ℂ) (x : RealDomainJet Ω) :
    realJetPart Ω (ofRealJet Ω x) = x := by
  apply PiLp.ext
  intro i
  simp

@[simp] lemma imagJetPart_ofRealJet (Ω : Set ℂ) (x : RealDomainJet Ω) :
    imagJetPart Ω (ofRealJet Ω x) = 0 := by
  apply PiLp.ext
  intro i
  simp

lemma realJetPart_smul_complex (Ω : Set ℂ) (c : ℂ) (x : ComplexDomainJet Ω) :
    realJetPart Ω (c • x) = c.re • realJetPart Ω x - c.im • imagJetPart Ω x := by
  apply PiLp.ext
  intro i
  change reL2 Ω (c • x i) = c.re • reL2 Ω (x i) - c.im • imL2 Ω (x i)
  exact reL2_smul_complex Ω c (x i)

lemma imagJetPart_smul_complex (Ω : Set ℂ) (c : ℂ) (x : ComplexDomainJet Ω) :
    imagJetPart Ω (c • x) = c.re • imagJetPart Ω x + c.im • realJetPart Ω x := by
  apply PiLp.ext
  intro i
  change imL2 Ω (c • x i) = c.re • imL2 Ω (x i) + c.im • reL2 Ω (x i)
  exact imL2_smul_complex Ω c (x i)

@[simp] lemma realJetPart_I_smul (Ω : Set ℂ) (x : ComplexDomainJet Ω) :
    realJetPart Ω (Complex.I • x) = -imagJetPart Ω x := by
  simp only [realJetPart_smul_complex, Complex.I_re, Complex.I_im,
    zero_smul, one_smul, zero_sub]

@[simp] lemma imagJetPart_I_smul (Ω : Set ℂ) (x : ComplexDomainJet Ω) :
    imagJetPart Ω (Complex.I • x) = realJetPart Ω x := by
  simp only [imagJetPart_smul_complex, Complex.I_re, Complex.I_im,
    zero_smul, one_smul, zero_add]

lemma complexDomainJet_ext (Ω : Set ℂ) {x y : ComplexDomainJet Ω}
    (hr : realJetPart Ω x = realJetPart Ω y)
    (hi : imagJetPart Ω x = imagJetPart Ω y) : x = y := by
  apply PiLp.ext
  intro i
  apply reL2_imL2_ext Ω
  · simpa only [realJetPart_apply] using congrArg (fun w : RealDomainJet Ω => w i) hr
  · simpa only [imagJetPart_apply] using congrArg (fun w : RealDomainJet Ω => w i) hi

/-- Native complex H₀¹ jets, equivalent to two copies of the real H₀¹ graph. -/
def ComplexH01Subspace (Ω : Set ℂ) : Submodule ℂ (ComplexDomainJet Ω) where
  carrier := {x | realJetPart Ω x ∈ (realDomainJet Ω).range ∧
    imagJetPart Ω x ∈ (realDomainJet Ω).range}
  zero_mem' := by
    change realJetPart Ω 0 ∈ (realDomainJet Ω).range ∧
      imagJetPart Ω 0 ∈ (realDomainJet Ω).range
    simp only [map_zero]
    exact ⟨⟨0, map_zero _⟩, ⟨0, map_zero _⟩⟩
  add_mem' hx hy := by
    change realJetPart Ω (_ + _) ∈ (realDomainJet Ω).range ∧
      imagJetPart Ω (_ + _) ∈ (realDomainJet Ω).range
    simpa only [map_add] using And.intro
      ((realDomainJet Ω).range.add_mem hx.1 hy.1)
      ((realDomainJet Ω).range.add_mem hx.2 hy.2)
  smul_mem' c x hx := by
    constructor
    · rw [realJetPart_smul_complex]
      exact (realDomainJet Ω).range.sub_mem
        ((realDomainJet Ω).range.smul_mem c.re hx.1)
        ((realDomainJet Ω).range.smul_mem c.im hx.2)
    · rw [imagJetPart_smul_complex]
      exact (realDomainJet Ω).range.add_mem
        ((realDomainJet Ω).range.smul_mem c.re hx.2)
        ((realDomainJet Ω).range.smul_mem c.im hx.1)

abbrev ComplexH01 (Ω : Set ℂ) := ComplexH01Subspace Ω

lemma complexH01_isClosed (Ω : Set ℂ) (hΩ : MeasurableSet Ω) :
    IsClosed (ComplexH01Subspace Ω : Set (ComplexDomainJet Ω)) := by
  have hZ : IsClosed ((realDomainJet Ω).range : Set (RealDomainJet Ω)) :=
    (realDomainJetIsometry Ω hΩ).isometry.isClosedEmbedding.isClosed_range
  exact (hZ.preimage (realJetPart Ω).continuous).inter
    (hZ.preimage (imagJetPart Ω).continuous)

def complexH01Complete (Ω : Set ℂ) (hΩ : MeasurableSet Ω) : CompleteSpace (ComplexH01 Ω) :=
  (complexH01_isClosed Ω hΩ).completeSpace_coe

def realH01Part (Ω : Set ℂ) (hΩ : MeasurableSet Ω) : ComplexH01 Ω →L[ℝ] H01 Ω :=
  (realDomainJetIsometry Ω hΩ).equivRange.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((realJetPart Ω).comp ((ComplexH01Subspace Ω).subtypeL.restrictScalars ℝ)).codRestrict
      (realDomainJet Ω).range (fun x => x.property.1))

def imagH01Part (Ω : Set ℂ) (hΩ : MeasurableSet Ω) : ComplexH01 Ω →L[ℝ] H01 Ω :=
  (realDomainJetIsometry Ω hΩ).equivRange.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((imagJetPart Ω).comp ((ComplexH01Subspace Ω).subtypeL.restrictScalars ℝ)).codRestrict
      (realDomainJet Ω).range (fun x => x.property.2))

@[simp] lemma realDomainJet_realH01Part (Ω : Set ℂ) (hΩ : MeasurableSet Ω)
    (x : ComplexH01 Ω) :
    realDomainJet Ω (realH01Part Ω hΩ x) = realJetPart Ω (x : ComplexDomainJet Ω) := by
  exact congrArg Subtype.val
    ((realDomainJetIsometry Ω hΩ).equivRange.apply_symm_apply
      ⟨realJetPart Ω (x : ComplexDomainJet Ω), x.property.1⟩)

@[simp] lemma realDomainJet_imagH01Part (Ω : Set ℂ) (hΩ : MeasurableSet Ω)
    (x : ComplexH01 Ω) :
    realDomainJet Ω (imagH01Part Ω hΩ x) = imagJetPart Ω (x : ComplexDomainJet Ω) := by
  exact congrArg Subtype.val
    ((realDomainJetIsometry Ω hΩ).equivRange.apply_symm_apply
      ⟨imagJetPart Ω (x : ComplexDomainJet Ω), x.property.2⟩)

def assembleComplexH01 (Ω : Set ℂ) (u v : H01 Ω) : ComplexH01 Ω :=
  ⟨ofRealJet Ω (realDomainJet Ω u) + Complex.I • ofRealJet Ω (realDomainJet Ω v), by
    constructor
    · simp only [map_add, realJetPart_ofRealJet, realJetPart_I_smul,
        imagJetPart_ofRealJet, neg_zero, add_zero]
      exact ⟨u, rfl⟩
    · simp only [map_add, imagJetPart_ofRealJet, imagJetPart_I_smul,
        realJetPart_ofRealJet, zero_add]
      exact ⟨v, rfl⟩⟩

@[simp] lemma realH01Part_assemble (Ω : Set ℂ) (hΩ : MeasurableSet Ω) (u v : H01 Ω) :
    realH01Part Ω hΩ (assembleComplexH01 Ω u v) = u := by
  apply (realDomainJetIsometry Ω hΩ).injective
  change realDomainJet Ω (realH01Part Ω hΩ (assembleComplexH01 Ω u v)) = realDomainJet Ω u
  rw [realDomainJet_realH01Part]
  simp only [assembleComplexH01, map_add, realJetPart_ofRealJet,
    realJetPart_I_smul, imagJetPart_ofRealJet, neg_zero, add_zero]

@[simp] lemma imagH01Part_assemble (Ω : Set ℂ) (hΩ : MeasurableSet Ω) (u v : H01 Ω) :
    imagH01Part Ω hΩ (assembleComplexH01 Ω u v) = v := by
  apply (realDomainJetIsometry Ω hΩ).injective
  change realDomainJet Ω (imagH01Part Ω hΩ (assembleComplexH01 Ω u v)) = realDomainJet Ω v
  rw [realDomainJet_imagH01Part]
  simp only [assembleComplexH01, map_add, imagJetPart_ofRealJet,
    imagJetPart_I_smul, realJetPart_ofRealJet, zero_add]

lemma assembleComplexH01_parts (Ω : Set ℂ) (hΩ : MeasurableSet Ω) (x : ComplexH01 Ω) :
    assembleComplexH01 Ω (realH01Part Ω hΩ x) (imagH01Part Ω hΩ x) = x := by
  apply Subtype.ext
  apply complexDomainJet_ext Ω
  · simp only [assembleComplexH01, map_add, realJetPart_ofRealJet,
      realJetPart_I_smul, imagJetPart_ofRealJet, neg_zero, add_zero,
      realDomainJet_realH01Part]
  · simp only [assembleComplexH01, map_add, imagJetPart_ofRealJet,
      imagJetPart_I_smul, realJetPart_ofRealJet, zero_add,
      realDomainJet_imagH01Part]

def complexInclusion (Ω : Set ℂ) : ComplexH01 Ω →L[ℂ] ComplexDomainL2 Ω :=
  (PiLp.proj 2 (fun _ : Fin 3 => ComplexDomainL2 Ω) 0).comp (ComplexH01Subspace Ω).subtypeL

def complexGradient (Ω : Set ℂ) (i : Fin 2) : ComplexH01 Ω →L[ℂ] ComplexDomainL2 Ω :=
  (PiLp.proj 2 (fun _ : Fin 3 => ComplexDomainL2 Ω) i.succ).comp (ComplexH01Subspace Ω).subtypeL

@[simp] lemma complexInclusion_assemble (Ω : Set ℂ) (u v : H01 Ω) :
    complexInclusion Ω (assembleComplexH01 Ω u v) =
      ofRealL2 Ω (inclusion Ω u) + Complex.I • ofRealL2 Ω (inclusion Ω v) := rfl

@[simp] lemma complexGradient_assemble (Ω : Set ℂ) (i : Fin 2) (u v : H01 Ω) :
    complexGradient Ω i (assembleComplexH01 Ω u v) =
      ofRealL2 Ω (domainGradient Ω i u) + Complex.I • ofRealL2 Ω (domainGradient Ω i v) := by
  fin_cases i <;> rfl

lemma complexInclusion_injective (Ω : Set ℂ) (hΩ : MeasurableSet Ω) :
    Function.Injective (complexInclusion Ω) := by
  intro x y h
  rw [← assembleComplexH01_parts Ω hΩ x, ← assembleComplexH01_parts Ω hΩ y]
  congr 1
  · apply inclusion_injective Ω hΩ
    have hr := congrArg (reL2 Ω) h
    rw [← assembleComplexH01_parts Ω hΩ x, ← assembleComplexH01_parts Ω hΩ y] at hr
    simpa only [complexInclusion_assemble, map_add, reL2_ofRealL2,
      reL2_I_smul, imL2_ofRealL2, neg_zero, add_zero] using hr
  · apply inclusion_injective Ω hΩ
    have hi := congrArg (imL2 Ω) h
    rw [← assembleComplexH01_parts Ω hΩ x, ← assembleComplexH01_parts Ω hΩ y] at hi
    simpa only [complexInclusion_assemble, map_add, imL2_ofRealL2,
      imL2_I_smul, reL2_ofRealL2, zero_add] using hi

def complexEnergyForm (Ω : Set ℂ) : ComplexH01 Ω →L⋆[ℂ] ComplexH01 Ω →L[ℂ] ℂ :=
  let B0 : ComplexH01 Ω →L⋆[ℂ] ComplexH01 Ω →L[ℂ] ℂ :=
    (innerSL ℂ (E := ComplexDomainL2 Ω)).bilinearComp (complexGradient Ω 0) (complexGradient Ω 0)
  let B1 : ComplexH01 Ω →L⋆[ℂ] ComplexH01 Ω →L[ℂ] ℂ :=
    (innerSL ℂ (E := ComplexDomainL2 Ω)).bilinearComp (complexGradient Ω 1) (complexGradient Ω 1)
  B0 + B1

@[simp] lemma complexEnergyForm_apply (Ω : Set ℂ) (u v : ComplexH01 Ω) :
    complexEnergyForm Ω u v = ⟪complexGradient Ω 0 u, complexGradient Ω 0 v⟫_ℂ +
      ⟪complexGradient Ω 1 u, complexGradient Ω 1 v⟫_ℂ := rfl

@[simp] lemma reL2_complexInclusion (Ω : Set ℂ) (hΩ : MeasurableSet Ω)
    (u : ComplexH01 Ω) :
    reL2 Ω (complexInclusion Ω u) = inclusion Ω (realH01Part Ω hΩ u) := by
  change reL2 Ω ((u : ComplexDomainJet Ω) 0) = _
  have h := congrArg (fun x : RealDomainJet Ω => x 0)
    (realDomainJet_realH01Part Ω hΩ u)
  simpa only [realDomainJet_apply, PiLp.toLp_apply, Matrix.cons_val_zero,
    realJetPart_apply] using h.symm

@[simp] lemma imL2_complexInclusion (Ω : Set ℂ) (hΩ : MeasurableSet Ω)
    (u : ComplexH01 Ω) :
    imL2 Ω (complexInclusion Ω u) = inclusion Ω (imagH01Part Ω hΩ u) := by
  change imL2 Ω ((u : ComplexDomainJet Ω) 0) = _
  have h := congrArg (fun x : RealDomainJet Ω => x 0)
    (realDomainJet_imagH01Part Ω hΩ u)
  simpa only [realDomainJet_apply, PiLp.toLp_apply, Matrix.cons_val_zero,
    imagJetPart_apply] using h.symm

@[simp] lemma reL2_complexGradient (Ω : Set ℂ) (hΩ : MeasurableSet Ω)
    (i : Fin 2) (u : ComplexH01 Ω) :
    reL2 Ω (complexGradient Ω i u) = domainGradient Ω i (realH01Part Ω hΩ u) := by
  change reL2 Ω ((u : ComplexDomainJet Ω) i.succ) = _
  have h := congrArg (fun x : RealDomainJet Ω => x i.succ)
    (realDomainJet_realH01Part Ω hΩ u)
  fin_cases i <;>
    simpa [realDomainJet_apply, PiLp.toLp_apply, Matrix.cons_val_succ,
      Matrix.cons_val_zero, realJetPart_apply, domainGradient] using h.symm

@[simp] lemma imL2_complexGradient (Ω : Set ℂ) (hΩ : MeasurableSet Ω)
    (i : Fin 2) (u : ComplexH01 Ω) :
    imL2 Ω (complexGradient Ω i u) = domainGradient Ω i (imagH01Part Ω hΩ u) := by
  change imL2 Ω ((u : ComplexDomainJet Ω) i.succ) = _
  have h := congrArg (fun x : RealDomainJet Ω => x i.succ)
    (realDomainJet_imagH01Part Ω hΩ u)
  fin_cases i <;>
    simpa [realDomainJet_apply, PiLp.toLp_apply, Matrix.cons_val_succ,
      Matrix.cons_val_zero, imagJetPart_apply, domainGradient] using h.symm

set_option maxHeartbeats 800000 in
lemma complexEnergyForm_parts (Ω : Set ℂ) (hΩ : MeasurableSet Ω)
    (u v : ComplexH01 Ω) :
    complexEnergyForm Ω u v =
      ((energyForm Ω (realH01Part Ω hΩ u) (realH01Part Ω hΩ v) +
        energyForm Ω (imagH01Part Ω hΩ u) (imagH01Part Ω hΩ v) : ℝ) : ℂ) +
      Complex.I * ((energyForm Ω (realH01Part Ω hΩ u) (imagH01Part Ω hΩ v) -
        energyForm Ω (imagH01Part Ω hΩ u) (realH01Part Ω hΩ v) : ℝ) : ℂ) := by
  rw [complexEnergyForm_apply, complexDomainL2_inner_re_im,
    complexDomainL2_inner_re_im]
  simp only [reL2_complexGradient Ω hΩ, imL2_complexGradient Ω hΩ]
  rw [energyForm_eq_domainGradient Ω hΩ, energyForm_eq_domainGradient Ω hΩ,
    energyForm_eq_domainGradient Ω hΩ, energyForm_eq_domainGradient Ω hΩ]
  push_cast
  ring

/-- The native complex weak equation is exactly its two real component
equations, with the usual sum of the two coordinate derivative energies. -/
lemma complex_form_equation_iff_real (Ω : Set ℂ) (hΩ : MeasurableSet Ω)
    (u : ComplexH01 Ω) (f : ComplexDomainL2 Ω) :
    (∀ v : ComplexH01 Ω, complexEnergyForm Ω u v = ⟪f, complexInclusion Ω v⟫_ℂ) ↔
      (∀ v : H01 Ω, energyForm Ω (realH01Part Ω hΩ u) v =
        ⟪reL2 Ω f, inclusion Ω v⟫_ℝ) ∧
      (∀ v : H01 Ω, energyForm Ω (imagH01Part Ω hΩ u) v =
        ⟪imL2 Ω f, inclusion Ω v⟫_ℝ) := by
  constructor
  · intro hu
    constructor
    · intro v
      have h := congrArg Complex.re (hu (assembleComplexH01 Ω v 0))
      simpa [complexEnergyForm_parts Ω hΩ, complexDomainL2_inner_re_im] using h
    · intro v
      have h := congrArg Complex.im (hu (assembleComplexH01 Ω v 0))
      have hv : -energyForm Ω (imagH01Part Ω hΩ u) v =
          -⟪imL2 Ω f, inclusion Ω v⟫_ℝ := by
        simpa [complexEnergyForm_parts Ω hΩ, complexDomainL2_inner_re_im] using h
      exact neg_injective hv
  · rintro ⟨hr, hi⟩ v
    rw [complexEnergyForm_parts Ω hΩ, complexDomainL2_inner_re_im]
    simp only [reL2_complexInclusion Ω hΩ, imL2_complexInclusion Ω hΩ,
      hr, hi]

def complexFormSolution (Ω : Set ℂ) (hbdd : Bornology.IsBounded Ω)
    (f : ComplexDomainL2 Ω) : ComplexH01 Ω :=
  assembleComplexH01 Ω
    (PolyaBridge.CoerciveForm.solution (inclusion Ω) (energyForm Ω)
      (energyForm_coercive Ω hbdd) (reL2 Ω f))
    (PolyaBridge.CoerciveForm.solution (inclusion Ω) (energyForm Ω)
      (energyForm_coercive Ω hbdd) (imL2 Ω f))

lemma complexFormSolution_equation (Ω : Set ℂ) (hΩ : MeasurableSet Ω)
    (hbdd : Bornology.IsBounded Ω) (f : ComplexDomainL2 Ω) (v : ComplexH01 Ω) :
    complexEnergyForm Ω (complexFormSolution Ω hbdd f) v =
      ⟪f, complexInclusion Ω v⟫_ℂ := by
  have hs : ∀ w : ComplexH01 Ω,
      complexEnergyForm Ω (complexFormSolution Ω hbdd f) w =
        ⟪f, complexInclusion Ω w⟫_ℂ :=
    (complex_form_equation_iff_real Ω hΩ _ f).mpr (by
      constructor
      · intro w
        simp only [complexFormSolution, realH01Part_assemble]
        exact PolyaBridge.CoerciveForm.solution_form _ _ _ _ _
      · intro w
        simp only [complexFormSolution, imagH01Part_assemble]
        exact PolyaBridge.CoerciveForm.solution_form _ _ _ _ _)
  exact hs v

lemma complex_form_equation_iff_solution (Ω : Set ℂ) (hΩ : MeasurableSet Ω)
    (hbdd : Bornology.IsBounded Ω) (u : ComplexH01 Ω) (f : ComplexDomainL2 Ω) :
    (∀ v : ComplexH01 Ω, complexEnergyForm Ω u v = ⟪f, complexInclusion Ω v⟫_ℂ) ↔
      u = complexFormSolution Ω hbdd f := by
  rw [complex_form_equation_iff_real Ω hΩ]
  constructor
  · rintro ⟨hr, hi⟩
    have hur := (PolyaBridge.CoerciveForm.form_equation_iff (inclusion Ω)
      (energyForm Ω) (energyForm_coercive Ω hbdd) _ _).mp hr
    have hui := (PolyaBridge.CoerciveForm.form_equation_iff (inclusion Ω)
      (energyForm Ω) (energyForm_coercive Ω hbdd) _ _).mp hi
    rw [← assembleComplexH01_parts Ω hΩ u, hur, hui]
    rfl
  · rintro rfl
    exact (complex_form_equation_iff_real Ω hΩ _ f).mp
      (complexFormSolution_equation Ω hΩ hbdd f)

lemma complexInclusion_solution (Ω : Set ℂ) (hbdd : Bornology.IsBounded Ω)
    (f : ComplexDomainL2 Ω) :
    complexInclusion Ω (complexFormSolution Ω hbdd f) =
      complexDirichletResolventZero Ω hbdd f := by
  apply reL2_imL2_ext Ω
  · simp [complexFormSolution, complexDirichletResolventZero,
      dirichletResolventZero, PolyaBridge.CoerciveForm.formInverse]
  · simp [complexFormSolution, complexDirichletResolventZero,
      dirichletResolventZero, PolyaBridge.CoerciveForm.formInverse]

lemma complexEnergyForm_self_re (Ω : Set ℂ) (hΩ : MeasurableSet Ω)
    (u : ComplexH01 Ω) :
    (complexEnergyForm Ω u u).re =
      energyForm Ω (realH01Part Ω hΩ u) (realH01Part Ω hΩ u) +
      energyForm Ω (imagH01Part Ω hΩ u) (imagH01Part Ω hΩ u) := by
  rw [complexEnergyForm_parts Ω hΩ]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul,
    sub_zero, add_zero]

lemma complexEnergyForm_self_eq_gradient_norm (Ω : Set ℂ) (u : ComplexH01 Ω) :
    (complexEnergyForm Ω u u).re =
      ‖complexGradient Ω 0 u‖ ^ 2 + ‖complexGradient Ω 1 u‖ ^ 2 := by
  rw [complexEnergyForm_apply, Complex.add_re]
  change RCLike.re ⟪complexGradient Ω 0 u, complexGradient Ω 0 u⟫_ℂ +
    RCLike.re ⟪complexGradient Ω 1 u, complexGradient Ω 1 u⟫_ℂ = _
  rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq]

/-- The inherited jet norm is exactly the usual H¹ form norm. -/
lemma complexH01_norm_sq (Ω : Set ℂ) (u : ComplexH01 Ω) :
    ‖u‖ ^ 2 = ‖complexInclusion Ω u‖ ^ 2 + (complexEnergyForm Ω u u).re := by
  rw [complexEnergyForm_self_eq_gradient_norm]
  change ‖(u : ComplexDomainJet Ω)‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

/-- The usual complex Dirichlet integral, with the sum of the squared
coordinate derivatives rather than the operator norm of a real derivative. -/
lemma complexEnergyForm_eq_integral (Ω : Set ℂ) (u v : ComplexH01 Ω) :
    complexEnergyForm Ω u v = ∫ z in Ω,
      star (complexGradient Ω 0 u z) * complexGradient Ω 0 v z +
      star (complexGradient Ω 1 u z) * complexGradient Ω 1 v z := by
  have h0 := L2.integrable_inner (𝕜 := ℂ) (complexGradient Ω 0 u) (complexGradient Ω 0 v)
  have h1 := L2.integrable_inner (𝕜 := ℂ) (complexGradient Ω 1 u) (complexGradient Ω 1 v)
  rw [complexEnergyForm_apply, L2.inner_def, L2.inner_def, ← integral_add h0 h1]
  congr 1
  funext z
  simp only [RCLike.inner_apply, starRingEnd_apply, mul_comm]

lemma complexEnergyForm_nonneg (Ω : Set ℂ) (hΩ : MeasurableSet Ω)
    (hbdd : Bornology.IsBounded Ω) (u : ComplexH01 Ω) :
    0 ≤ (complexEnergyForm Ω u u).re := by
  rw [complexEnergyForm_self_re Ω hΩ]
  exact add_nonneg
    (PolyaBridge.CoerciveForm.form_self_nonneg _ (energyForm_coercive Ω hbdd) _)
    (PolyaBridge.CoerciveForm.form_self_nonneg _ (energyForm_coercive Ω hbdd) _)

set_option maxHeartbeats 800000 in
/-- The usual closed-form criterion on complex L². An L² limit of a
form-Cauchy sequence lies in the genuine complex H₀¹ graph, with convergence
in the two-coordinate Dirichlet energy. -/
lemma complexEnergyForm_complete (Ω : Set ℂ) (hΩ : MeasurableSet Ω)
    (hbdd : Bornology.IsBounded Ω) (u : ℕ → ComplexH01 Ω) (f : ComplexDomainL2 Ω)
    (huf : Filter.Tendsto (fun n => complexInclusion Ω (u n)) Filter.atTop (𝓝 f))
    (hu : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      (complexEnergyForm Ω (u m - u n) (u m - u n)).re < ε) :
    ∃ v : ComplexH01 Ω, complexInclusion Ω v = f ∧
      Filter.Tendsto (fun n => (complexEnergyForm Ω (u n - v) (u n - v)).re)
        Filter.atTop (𝓝 0) := by
  have hreal : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      energyForm Ω (realH01Part Ω hΩ (u m) - realH01Part Ω hΩ (u n))
        (realH01Part Ω hΩ (u m) - realH01Part Ω hΩ (u n)) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have hsum := hN m hm n hn
    rw [complexEnergyForm_self_re Ω hΩ] at hsum
    simp only [map_sub (realH01Part Ω hΩ), map_sub (imagH01Part Ω hΩ)] at hsum
    have hnon := PolyaBridge.CoerciveForm.form_self_nonneg (energyForm Ω)
      (energyForm_coercive Ω hbdd) (imagH01Part Ω hΩ (u m) - imagH01Part Ω hΩ (u n))
    linarith
  have himag : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      energyForm Ω (imagH01Part Ω hΩ (u m) - imagH01Part Ω hΩ (u n))
        (imagH01Part Ω hΩ (u m) - imagH01Part Ω hΩ (u n)) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have hsum := hN m hm n hn
    rw [complexEnergyForm_self_re Ω hΩ] at hsum
    simp only [map_sub (realH01Part Ω hΩ), map_sub (imagH01Part Ω hΩ)] at hsum
    have hnon := PolyaBridge.CoerciveForm.form_self_nonneg (energyForm Ω)
      (energyForm_coercive Ω hbdd) (realH01Part Ω hΩ (u m) - realH01Part Ω hΩ (u n))
    linarith
  have hreal_lim : Filter.Tendsto (fun n => inclusion Ω (realH01Part Ω hΩ (u n)))
      Filter.atTop (𝓝 (reL2 Ω f)) := by
    have h := (reL2 Ω).continuous.continuousAt.tendsto.comp huf
    change Filter.Tendsto (fun n => reL2 Ω (complexInclusion Ω (u n)))
      Filter.atTop (𝓝 (reL2 Ω f)) at h
    simp only [reL2_complexInclusion Ω hΩ] at h
    exact h
  have himag_lim : Filter.Tendsto (fun n => inclusion Ω (imagH01Part Ω hΩ (u n)))
      Filter.atTop (𝓝 (imL2 Ω f)) := by
    have h := (imL2 Ω).continuous.continuousAt.tendsto.comp huf
    change Filter.Tendsto (fun n => imL2 Ω (complexInclusion Ω (u n)))
      Filter.atTop (𝓝 (imL2 Ω f)) at h
    simp only [imL2_complexInclusion Ω hΩ] at h
    exact h
  obtain ⟨vr, hvr, hqr⟩ := PolyaBridge.CoerciveForm.form_complete (inclusion Ω)
    (energyForm Ω) (energyForm_coercive Ω hbdd) (fun n => realH01Part Ω hΩ (u n))
    (reL2 Ω f) hreal_lim hreal
  obtain ⟨vi, hvi, hqi⟩ := PolyaBridge.CoerciveForm.form_complete (inclusion Ω)
    (energyForm Ω) (energyForm_coercive Ω hbdd) (fun n => imagH01Part Ω hΩ (u n))
    (imL2 Ω f) himag_lim himag
  refine ⟨assembleComplexH01 Ω vr vi, ?_, ?_⟩
  · apply reL2_imL2_ext Ω
    · simpa only [reL2_complexInclusion Ω hΩ, realH01Part_assemble] using hvr
    · simpa only [imL2_complexInclusion Ω hΩ, imagH01Part_assemble] using hvi
  · have hq := hqr.add hqi
    simpa only [complexEnergyForm_self_re Ω hΩ,
      map_sub (realH01Part Ω hΩ), map_sub (imagH01Part Ω hΩ),
      realH01Part_assemble, imagH01Part_assemble, add_zero] using hq

end DirichletBridge

/-! A genuine complex smooth compactly supported core for the native complex
zero-boundary graph. Its value and both directional derivatives are identified,
and its jets have dense range in the complex form domain. -/

noncomputable section

namespace DirichletBridge

open MeasureTheory Set Topology
open scoped InnerProductSpace

abbrev ComplexSmoothCorePair (Ω : Set ℂ) := SmoothCore Ω × SmoothCore Ω

def complexCoreFunction (Ω : Set ℂ) (p : ComplexSmoothCorePair Ω) (z : ℂ) : ℂ :=
  ((p.1 : ℂ → ℝ) z : ℂ) + Complex.I * ((p.2 : ℂ → ℝ) z : ℂ)

lemma complexCoreFunction_contDiff (Ω : Set ℂ) (p : ComplexSmoothCorePair Ω) :
    ContDiff ℝ (⊤ : ℕ∞) (complexCoreFunction Ω p) := by
  have hu : ContDiff ℝ (⊤ : ℕ∞) (fun z => ((p.1 : ℂ → ℝ) z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp p.1.property.1
  have hv : ContDiff ℝ (⊤ : ℕ∞) (fun z => ((p.2 : ℂ → ℝ) z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp p.2.property.1
  exact hu.add (contDiff_const.mul hv)

lemma complexCoreFunction_hasCompactSupport (Ω : Set ℂ) (p : ComplexSmoothCorePair Ω) :
    HasCompactSupport (complexCoreFunction Ω p) := by
  have hu : HasCompactSupport (fun z => ((p.1 : ℂ → ℝ) z : ℂ)) :=
    p.1.property.2.1.comp_left Complex.ofReal_zero
  have hv : HasCompactSupport (fun z => Complex.I * ((p.2 : ℂ → ℝ) z : ℂ)) :=
    p.2.property.2.1.comp_left (g := fun x : ℝ => Complex.I * (x : ℂ)) (by simp)
  exact hu.add hv

lemma complexCoreFunction_tsupport (Ω : Set ℂ) (p : ComplexSmoothCorePair Ω) :
    tsupport (complexCoreFunction Ω p) ⊆ Ω := by
  have hu : tsupport (fun z => ((p.1 : ℂ → ℝ) z : ℂ)) ⊆ tsupport (p.1 : ℂ → ℝ) :=
    tsupport_comp_subset Complex.ofReal_zero (p.1 : ℂ → ℝ)
  have hv : tsupport (fun z => Complex.I * ((p.2 : ℂ → ℝ) z : ℂ)) ⊆
      tsupport (p.2 : ℂ → ℝ) :=
    tsupport_comp_subset (g := fun x : ℝ => Complex.I * (x : ℂ)) (by simp) (p.2 : ℂ → ℝ)
  exact (tsupport_add _ _).trans
    (union_subset (hu.trans p.1.property.2.2) (hv.trans p.2.property.2.2))

/-- The paired real core represents every complex smooth compactly supported
function in the domain, not just a chosen family of examples. -/
theorem exists_complexCoreFunction_eq (Ω : Set ℂ) {f : ℂ → ℂ}
    (hSmooth : ContDiff ℝ (⊤ : ℕ∞) f) (hCompact : HasCompactSupport f)
    (hSupport : tsupport f ⊆ Ω) :
    ∃ p : ComplexSmoothCorePair Ω, complexCoreFunction Ω p = f := by
  have hu : (fun z => (f z).re) ∈ testFunctions Ω := by
    refine ⟨Complex.reCLM.contDiff.comp hSmooth,
      hCompact.comp_left (g := Complex.re) (by simp), ?_⟩
    exact (tsupport_comp_subset (g := Complex.re) (by simp) f).trans hSupport
  have hv : (fun z => (f z).im) ∈ testFunctions Ω := by
    refine ⟨Complex.imCLM.contDiff.comp hSmooth,
      hCompact.comp_left (g := Complex.im) (by simp), ?_⟩
    exact (tsupport_comp_subset (g := Complex.im) (by simp) f).trans hSupport
  refine ⟨(⟨_, hu⟩, ⟨_, hv⟩), ?_⟩
  funext z
  simpa only [complexCoreFunction, mul_comm] using Complex.re_add_im (f z)

lemma complexCoreFunction_fderiv (Ω : Set ℂ) (p : ComplexSmoothCorePair Ω) (z d : ℂ) :
    fderiv ℝ (complexCoreFunction Ω p) z d =
      (fderiv ℝ (p.1 : ℂ → ℝ) z d : ℂ) +
        Complex.I * (fderiv ℝ (p.2 : ℂ → ℝ) z d : ℂ) := by
  have hu := Complex.ofRealCLM.hasFDerivAt.comp z
    ((p.1.property.1.differentiable (by simp) z).hasFDerivAt)
  have hv := Complex.ofRealCLM.hasFDerivAt.comp z
    ((p.2.property.1.differentiable (by simp) z).hasFDerivAt)
  have h := (hu.add (hv.const_mul Complex.I)).fderiv
  have hd := congrArg (fun L : ℂ →L[ℝ] ℂ => L d) h
  unfold complexCoreFunction
  have hfun :
      (fun y : ℂ => ((p.1 : ℂ → ℝ) y : ℂ) + Complex.I * ((p.2 : ℂ → ℝ) y : ℂ)) =
        (⇑Complex.ofRealCLM ∘ (p.1 : ℂ → ℝ) +
          fun y => Complex.I * (⇑Complex.ofRealCLM ∘ (p.2 : ℂ → ℝ)) y) := by
    funext y
    rfl
  rw [hfun]
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul] using hd

def complexSmoothCoreJet (Ω : Set ℂ) (p : ComplexSmoothCorePair Ω) : ComplexH01 Ω :=
  assembleComplexH01 Ω (coreToH01 Ω p.1) (coreToH01 Ω p.2)

lemma continuous_assembleComplexH01 (Ω : Set ℂ) :
    Continuous (fun p : H01 Ω × H01 Ω => assembleComplexH01 Ω p.1 p.2) := by
  apply Continuous.subtype_mk
  have hc : Continuous (fun _ : H01 Ω × H01 Ω => (Complex.I : ℂ)) := continuous_const
  convert (((ofRealJet Ω).continuous.comp
      ((realDomainJet Ω).continuous.comp continuous_fst)).add
    (hc.smul ((ofRealJet Ω).continuous.comp
      ((realDomainJet Ω).continuous.comp continuous_snd)))) using 1 <;>
    funext x <;> rfl

set_option maxHeartbeats 800000 in
theorem complexSmoothCoreJet_dense (Ω : Set ℂ) (hΩ : MeasurableSet Ω) :
    DenseRange (complexSmoothCoreJet Ω) := by
  intro x
  rw [Metric.mem_closure_iff]
  intro ε hε
  let u : H01 Ω := realH01Part Ω hΩ x
  let v : H01 Ω := imagH01Part Ω hΩ x
  let A : H01 Ω × H01 Ω → ComplexH01 Ω :=
    fun p => assembleComplexH01 Ω p.1 p.2
  have hcont : ContinuousAt A (u, v) :=
    (continuous_assembleComplexH01 Ω).continuousAt
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hcont ε hε
  obtain ⟨ur, hur, hdu⟩ := Metric.mem_closure_iff.mp (coreToH01_dense Ω u) δ hδ
  obtain ⟨vi, hvi, hdv⟩ := Metric.mem_closure_iff.mp (coreToH01_dense Ω v) δ hδ
  obtain ⟨p, rfl⟩ := hur
  obtain ⟨q, rfl⟩ := hvi
  rw [dist_comm] at hdu hdv
  have hpq : dist (coreToH01 Ω p, coreToH01 Ω q) (u, v) < δ := by
    rw [Prod.dist_eq]
    exact max_lt_iff.mpr ⟨hdu, hdv⟩
  have hnear := hclose hpq
  have hA : A (u, v) = x := assembleComplexH01_parts Ω hΩ x
  have hApq : A (coreToH01 Ω p, coreToH01 Ω q) = complexSmoothCoreJet Ω (p, q) := rfl
  rw [hA, hApq] at hnear
  refine ⟨complexSmoothCoreJet Ω (p, q), ⟨(p, q), rfl⟩, ?_⟩
  simpa only [dist_comm] using hnear

lemma domainGradient_coreToH01_coeFn (Ω : Set ℂ) (i : Fin 2) (u : SmoothCore Ω) :
    domainGradient Ω i (coreToH01 Ω u) =ᵐ[volume.restrict Ω]
      fun z => fderiv ℝ (u : ℂ → ℝ) z (direction i) := by
  simp only [domainGradient, ContinuousLinearMap.comp_apply, gradient_coreToH01]
  exact (restrictL2_coeFn Ω (coreDeriv Ω (direction i) u)).trans
    (ae_restrict_of_ae (core_deriv_memLp Ω u (direction i)).coeFn_toLp)

theorem complexSmoothCoreJet_value (Ω : Set ℂ) (p : ComplexSmoothCorePair Ω) :
    complexInclusion Ω (complexSmoothCoreJet Ω p) =ᵐ[volume.restrict Ω]
      complexCoreFunction Ω p := by
  rw [complexSmoothCoreJet, complexInclusion_assemble]
  filter_upwards [
    Lp.coeFn_add (ofRealL2 Ω (inclusion Ω (coreToH01 Ω p.1)))
      (Complex.I • ofRealL2 Ω (inclusion Ω (coreToH01 Ω p.2))),
    Lp.coeFn_smul Complex.I (ofRealL2 Ω (inclusion Ω (coreToH01 Ω p.2))),
    ofRealL2_coeFn Ω (inclusion Ω (coreToH01 Ω p.1)),
    ofRealL2_coeFn Ω (inclusion Ω (coreToH01 Ω p.2)),
    inclusion_coreToH01_coeFn Ω p.1, inclusion_coreToH01_coeFn Ω p.2]
      with z hadd hsmul hor hoi hu hv
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hor, hoi, hu, hv]
  rfl

theorem complexSmoothCoreJet_gradient (Ω : Set ℂ) (p : ComplexSmoothCorePair Ω)
    (i : Fin 2) :
    complexGradient Ω i (complexSmoothCoreJet Ω p) =ᵐ[volume.restrict Ω]
      fun z => fderiv ℝ (complexCoreFunction Ω p) z (direction i) := by
  rw [complexSmoothCoreJet, complexGradient_assemble]
  filter_upwards [
    Lp.coeFn_add (ofRealL2 Ω (domainGradient Ω i (coreToH01 Ω p.1)))
      (Complex.I • ofRealL2 Ω (domainGradient Ω i (coreToH01 Ω p.2))),
    Lp.coeFn_smul Complex.I (ofRealL2 Ω (domainGradient Ω i (coreToH01 Ω p.2))),
    ofRealL2_coeFn Ω (domainGradient Ω i (coreToH01 Ω p.1)),
    ofRealL2_coeFn Ω (domainGradient Ω i (coreToH01 Ω p.2)),
    domainGradient_coreToH01_coeFn Ω i p.1, domainGradient_coreToH01_coeFn Ω i p.2]
      with z hadd hsmul hor hoi hu hv
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hor, hoi, hu, hv]
  exact (complexCoreFunction_fderiv Ω p z (direction i)).symm

end DirichletBridge

namespace PolyaBridge.SpectralMultiplicity

open Set Filter
open scoped InnerProductSpace Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem inner_eq_zero_of_distinct_eigenvalues {T : H →L[ℝ] H}
    (hSymmetric : ∀ x y, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ)
    {μ ν : ℝ} {x y : H} (hTx : T x = μ • x) (hTy : T y = ν • y)
    (hne : μ ≠ ν) : ⟪x, y⟫_ℝ = 0 := by
  have hSym := hSymmetric x y
  rw [hTx, hTy, real_inner_smul_left, real_inner_smul_right] at hSym
  have hProduct : μ * ⟪x, y⟫_ℝ = ν * ⟪x, y⟫_ℝ := by
    simpa only [mul_comm] using hSym
  exact (mul_eq_mul_right_iff.mp hProduct).resolve_left hne

/-- Once a finite truncation reaches below `μ`, its vectors with eigenvalue `μ`
span the entire `μ`-eigenspace. -/
theorem eigenspace_eq_span_of_truncation {T : H →L[ℝ] H}
    (hSymmetric : ∀ x y, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ)
    {n : ℕ} (hn : 0 < n) (f : CompactSpectral.PositiveEigenFamily T n)
    {μ : ℝ} (hBelow : f.values (n - 1) < μ) :
    Module.End.eigenspace T.toLinearMap μ = Submodule.span ℝ
      (Set.range (fun i : {i : Fin n // f.values i = μ} => f.vectors i.val)) := by
  classical
  let W : Submodule ℝ H := Submodule.span ℝ
    (Set.range (fun i : {i : Fin n // f.values i = μ} => f.vectors i.val))
  have hW : W ≤ Module.End.eigenspace T.toLinearMap μ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    change T (f.vectors i.val) = μ • f.vectors i.val
    rw [f.eigenvector i.val i.val.isLt, i.property]
  refine le_antisymm ?_ hW
  intro x hx
  have hxT : T x = μ • x := Module.End.mem_eigenspace_iff.mp hx
  let c : Fin n → ℝ := fun i => ⟪f.vectors i, x⟫_ℝ
  let y : H := ∑ i : Fin n, c i • f.vectors i
  have hcoeff0 : ∀ i : Fin n, f.values i ≠ μ → c i = 0 := by
    intro i hi
    exact inner_eq_zero_of_distinct_eigenvalues hSymmetric
      (f.eigenvector i i.isLt) hxT hi
  have hyW : y ∈ W := by
    apply W.sum_mem
    intro i _
    by_cases hi : f.values i = μ
    · apply W.smul_mem
      exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    · rw [hcoeff0 i hi, zero_smul]
      exact W.zero_mem
  have hyT : T y = μ • y := Module.End.mem_eigenspace_iff.mp (hW hyW)
  let r : H := x - y
  have hrT : T r = μ • r := by
    change T (x - y) = μ • (x - y)
    rw [map_sub, hxT, hyT, smul_sub]
  have hrOrth : ∀ i < n - 1, ⟪f.vectors i, r⟫_ℝ = 0 := by
    intro i hi
    let k : Fin n := ⟨i, by omega⟩
    change ⟪f.vectors k, x - ∑ l : Fin n, c l • f.vectors l⟫_ℝ = 0
    rw [inner_sub_right, f.orthonormal.inner_right_fintype c k]
    exact sub_self _
  have hr0 : r = 0 := by
    by_contra hne
    have hNormPos : 0 < ‖r‖ ^ 2 := by positivity
    have hUpper := f.maximal (n - 1) (by omega) r hrOrth
    rw [hrT, real_inner_smul_left, real_inner_self_eq_norm_sq] at hUpper
    exact (not_le_of_gt hBelow) (le_of_mul_le_mul_right hUpper hNormPos)
  have hxy : x = y := sub_eq_zero.mp hr0
  simpa only [hxy] using hyW

theorem eigenspace_finrank_eq_truncation_multiplicity {T : H →L[ℝ] H}
    (hSymmetric : ∀ x y, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ)
    {n : ℕ} (hn : 0 < n) (f : CompactSpectral.PositiveEigenFamily T n)
    {μ : ℝ} (hBelow : f.values (n - 1) < μ) :
    Module.finrank ℝ (Module.End.eigenspace T.toLinearMap μ) =
      Nat.card {i : Fin n // f.values i = μ} := by
  classical
  rw [eigenspace_eq_span_of_truncation hSymmetric hn f hBelow, Nat.card_eq_fintype_card]
  apply finrank_span_eq_card
  exact f.orthonormal.linearIndependent.comp
    (fun i : {i : Fin n // f.values i = μ} => i.val) Subtype.val_injective

variable {T : H →L[ℝ] H}
  (hCompact : IsCompactOperator T)
  (hSymmetric : ∀ x y, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ)
  (hPositive : ∀ x : H, x ≠ 0 → 0 < ⟪T x, x⟫_ℝ)
  (hInfinite : ¬ Module.Finite ℝ H)

include hCompact hSymmetric hPositive hInfinite

theorem finite_spectralEigenvalue_occurrences {μ : ℝ} (hμ : 0 < μ) :
    Set.Finite {j : ℕ | 0 < j ∧ CompactSpectral.spectralEigenvalue T j = μ} := by
  apply (SpectralDiscrete.finite_spectralThreshold_indices hCompact hμ).subset
  intro j hj
  obtain ⟨f⟩ := CompactSpectral.exists_positive_eigenfamily
    hCompact hSymmetric hPositive hInfinite j
  apply (f.mem_threshold_iff hj.1).mpr
  exact ⟨hμ, hj.2.ge⟩

/-- Spectral numbering counts each positive eigenvalue exactly as many times as
the real dimension of its eigenspace. -/
theorem spectralEigenvalue_multiplicity_eq_finrank {μ : ℝ} (hμ : 0 < μ) :
    Set.ncard {j : ℕ | 0 < j ∧ CompactSpectral.spectralEigenvalue T j = μ} =
      Module.finrank ℝ (Module.End.eigenspace T.toLinearMap μ) := by
  classical
  obtain ⟨n, hnBelow, hnPos⟩ :=
    ((SpectralDiscrete.eventually_spectralEigenvalue_lt
      hCompact hSymmetric hPositive hInfinite hμ).and
        (eventually_ge_atTop (1 : ℕ))).exists
  have hn : 0 < n := by omega
  obtain ⟨f⟩ := CompactSpectral.exists_positive_eigenfamily
    hCompact hSymmetric hPositive hInfinite n
  have hfBelow : f.values (n - 1) < μ := by
    rwa [f.spectralEigenvalue_eq_last hn] at hnBelow
  let I := {i : Fin n // f.values i = μ}
  let O := {j : ℕ // 0 < j ∧ CompactSpectral.spectralEigenvalue T j = μ}
  let a : I → O := fun i =>
    ⟨i.val.val + 1, by omega, by
      rw [SpectralDiscrete.eigenfamily_value_eq_spectralEigenvalue f i.val.isLt]
      exact i.property⟩
  have haInjective : Function.Injective a := by
    intro i l h
    apply Subtype.ext
    apply Fin.ext
    have hv := congrArg (fun j : O => j.val) h
    change i.val.val + 1 = l.val.val + 1 at hv
    omega
  have haSurjective : Function.Surjective a := by
    intro j
    have hjn : j.val < n := by
      by_contra hnot
      have hnJ : n ≤ j.val := Nat.le_of_not_gt hnot
      have hle := CompactSpectral.spectralEigenvalue_le_of_index_le
        hCompact hSymmetric hPositive hInfinite hn hnJ
      rw [j.property.2] at hle
      exact (not_le_of_gt hnBelow) hle
    have hi : j.val - 1 < n := by omega
    have hIndex : j.val - 1 + 1 = j.val := by have := j.property.1; omega
    have hValue : f.values (j.val - 1) = μ := by
      rw [← SpectralDiscrete.eigenfamily_value_eq_spectralEigenvalue f hi, hIndex]
      exact j.property.2
    refine ⟨⟨⟨j.val - 1, hi⟩, hValue⟩, ?_⟩
    apply Subtype.ext
    exact hIndex
  have hCard : Nat.card O = Fintype.card I := by
    rw [← Nat.card_eq_fintype_card]
    exact (Nat.card_congr (Equiv.ofBijective a ⟨haInjective, haSurjective⟩)).symm
  calc
    Set.ncard {j : ℕ | 0 < j ∧ CompactSpectral.spectralEigenvalue T j = μ} =
        Fintype.card I := hCard
    _ = Module.finrank ℝ (Module.End.eigenspace T.toLinearMap μ) := by
      simpa only [I, Nat.card_eq_fintype_card] using
        (eigenspace_finrank_eq_truncation_multiplicity hSymmetric hn f hfBelow).symm

end PolyaBridge.SpectralMultiplicity

noncomputable section

namespace PolyaBridge.ComplexInverseOperator

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The partial inverse of an everywhere-defined bounded operator. -/
def operator (K : H →L[ℂ] H) : H →ₗ.[ℂ] H :=
  (K.toLinearMap.toPMap ⊤).inverse

omit [CompleteSpace H] in
theorem domain (K : H →L[ℂ] H) : (operator K).domain = K.range := by
  rw [operator, LinearPMap.inverse_domain]
  ext f
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨(v : H), hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨⟨v, Submodule.mem_top⟩, hv⟩

def domainVector (K : H →L[ℂ] H) (f : H) : (operator K).domain :=
  ⟨K f, by rw [domain]; exact ⟨f, rfl⟩⟩

omit [CompleteSpace H] in
@[simp] theorem domainVector_coe (K : H →L[ℂ] H) (f : H) :
    (domainVector K f : H) = K f := rfl

omit [CompleteSpace H] in
theorem partial_ker_eq_bot (K : H →L[ℂ] H) (hKinj : Function.Injective K) :
    (K.toLinearMap.toPMap ⊤).ker = ⊥ := by
  rw [LinearPMap.ker_eq_bot']
  intro f hf
  apply Subtype.ext
  apply hKinj
  change K (f : H) = 0 at hf
  simpa using hf

omit [CompleteSpace H] in
@[simp] theorem apply_vector (K : H →L[ℂ] H) (hKinj : Function.Injective K)
    (f : H) : operator K (domainVector K f) = f := by
  change (K.toLinearMap.toPMap ⊤).inverse ⟨K f, _⟩ = (f : H)
  simpa using (LinearPMap.inverse_apply_eq (f := K.toLinearMap.toPMap ⊤)
    (partial_ker_eq_bot K hKinj) (x := ⟨f, Submodule.mem_top⟩) rfl)

omit [CompleteSpace H] in
theorem inverse_apply (K : H →L[ℂ] H) (hKinj : Function.Injective K)
    (u : (operator K).domain) : K (operator K u) = (u : H) := by
  obtain ⟨f, hf⟩ : ∃ f, K f = (u : H) := by
    have hu := u.property
    simp only [domain] at hu
    exact hu
  have hu : u = domainVector K f := Subtype.ext hf.symm
  rw [hu, apply_vector K hKinj]
  rfl

omit [CompleteSpace H] in
theorem dense_domain (K : H →L[ℂ] H) (hKdense : DenseRange K) :
    Dense ((operator K).domain : Set H) := by
  rw [domain]
  exact hKdense

theorem denseRange_of_symmetric_injective (K : H →L[ℂ] H)
    (hKsym : K.IsSymmetric) (hKinj : Function.Injective K) : DenseRange K := by
  change Dense (K.range : Set H)
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, ContinuousLinearMap.orthogonal_range,
    hKsym.clm_adjoint_eq, LinearMap.ker_eq_bot]
  exact hKinj

omit [CompleteSpace H] in
theorem formalAdjoint (K : H →L[ℂ] H) (hKinj : Function.Injective K)
    (hKsym : K.IsSymmetric) : (operator K).IsFormalAdjoint (operator K) := by
  intro u v
  calc
    ⟪operator K u, (v : H)⟫_ℂ = ⟪operator K u, K (operator K v)⟫_ℂ := by
      rw [inverse_apply K hKinj]
    _ = ⟪K (operator K u), operator K v⟫_ℂ := (hKsym _ _).symm
    _ = ⟪(u : H), operator K v⟫_ℂ := by rw [inverse_apply K hKinj]

theorem inverse_adjoint_apply (K : H →L[ℂ] H) (hKinj : Function.Injective K)
    (hKsym : K.IsSymmetric) (hKdense : DenseRange K)
    (u : (operator K).adjoint.domain) : K ((operator K).adjoint u) = (u : H) := by
  apply ext_inner_right ℂ
  intro f
  calc
    ⟪K ((operator K).adjoint u), f⟫_ℂ = ⟪(operator K).adjoint u, K f⟫_ℂ := hKsym _ _
    _ = ⟪(u : H), f⟫_ℂ := by
      have h := LinearPMap.adjoint_isFormalAdjoint
        (hT := dense_domain K hKdense) u (domainVector K f)
      change ⟪(operator K).adjoint u, K f⟫_ℂ =
        ⟪(u : H), operator K (domainVector K f)⟫_ℂ at h
      rwa [apply_vector K hKinj] at h

theorem selfAdjoint (K : H →L[ℂ] H) (hKinj : Function.Injective K)
    (hKsym : K.IsSymmetric) (hKdense : DenseRange K) : IsSelfAdjoint (operator K) := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · refine ⟨?_, ?_⟩
    · intro f hf
      rw [domain]
      exact ⟨(operator K).adjoint ⟨f, hf⟩,
        inverse_adjoint_apply K hKinj hKsym hKdense ⟨f, hf⟩⟩
    · intro u v huv
      apply hKinj
      calc
        K ((operator K).adjoint u) = (u : H) :=
          inverse_adjoint_apply K hKinj hKsym hKdense u
        _ = (v : H) := huv
        _ = K (operator K v) := (inverse_apply K hKinj v).symm
  · exact LinearPMap.IsFormalAdjoint.le_adjoint (hT := dense_domain K hKdense)
      (formalAdjoint K hKinj hKsym)

theorem closed (K : H →L[ℂ] H) (hKinj : Function.Injective K)
    (hKsym : K.IsSymmetric) (hKdense : DenseRange K) : (operator K).IsClosed :=
  (selfAdjoint K hKinj hKsym hKdense).isClosed

omit [CompleteSpace H] in
theorem nonneg (K : H →L[ℂ] H) (hKinj : Function.Injective K)
    (hKpositive : K.IsPositive) (u : (operator K).domain) :
    0 ≤ (⟪operator K u, (u : H)⟫_ℂ).re := by
  rw [← inverse_apply K hKinj u]
  exact hKpositive.re_inner_nonneg_right _

omit [CompleteSpace H] in
theorem eigenvector_mem_domain (K : H →L[ℂ] H) (μ : ℂ) (hμ : μ ≠ 0)
    (f : H) (hf : K f = μ • f) : f ∈ (operator K).domain := by
  rw [domain]
  refine ⟨μ⁻¹ • f, ?_⟩
  change K (μ⁻¹ • f) = f
  rw [map_smul]
  change μ⁻¹ • K f = f
  rw [hf, smul_smul, inv_mul_cancel₀ hμ, one_smul]

omit [CompleteSpace H] in
/-- A nonzero inverse eigenvalue gives an eigenvalue of the actual partial
operator on its genuine domain. -/
theorem eigenvector_apply (K : H →L[ℂ] H) (hKinj : Function.Injective K)
    (μ : ℂ) (hμ : μ ≠ 0) (f : H) (hf : K f = μ • f) :
    operator K ⟨f, eigenvector_mem_domain K μ hμ f hf⟩ = μ⁻¹ • f := by
  have hv : (⟨f, eigenvector_mem_domain K μ hμ f hf⟩ : (operator K).domain) =
      domainVector K (μ⁻¹ • f) := by
    apply Subtype.ext
    change f = K (μ⁻¹ • f)
    rw [map_smul]
    change f = μ⁻¹ • K f
    rw [hf, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  rw [hv]
  exact apply_vector K hKinj _

omit [CompleteSpace H] in
/-- Conversely every nonzero eigenvalue of the partial operator gives its
reciprocal as an eigenvalue of the bounded inverse. -/
theorem inverse_eigen_of_operator_eigen (K : H →L[ℂ] H)
    (hKinj : Function.Injective K) (lam : ℂ) (hlam : lam ≠ 0)
    (u : (operator K).domain) (hu : operator K u = lam • (u : H)) :
    K (u : H) = lam⁻¹ • (u : H) := by
  have h := inverse_apply K hKinj u
  rw [hu, map_smul] at h
  have h' := congrArg (fun x : H => lam⁻¹ • x) h
  simpa only [smul_smul, inv_mul_cancel₀ hlam, one_smul] using h'

end PolyaBridge.ComplexInverseOperator

namespace DirichletBridge

open scoped InnerProductSpace

/-- The genuine complex Dirichlet operator: the partial inverse of the
zero-resolvent obtained from the gradient form. -/
def complexDirichletOperator (Ω : Set ℂ) (hbdd : Bornology.IsBounded Ω) :
    ComplexDomainL2 Ω →ₗ.[ℂ] ComplexDomainL2 Ω :=
  PolyaBridge.ComplexInverseOperator.operator (complexDirichletResolventZero Ω hbdd)

lemma complexDirichletOperator_domain (Ω : Set ℂ) (hbdd : Bornology.IsBounded Ω) :
    (complexDirichletOperator Ω hbdd).domain = (complexDirichletResolventZero Ω hbdd).range :=
  PolyaBridge.ComplexInverseOperator.domain _

lemma complexDirichletResolventZero_dense (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) : DenseRange (complexDirichletResolventZero Ω hbdd) :=
  PolyaBridge.ComplexInverseOperator.denseRange_of_symmetric_injective _
    (complexDirichletResolventZero_symmetric Ω hbdd)
    (complexDirichletResolventZero_injective Ω hopen hbdd)

lemma complexDirichletOperator_selfAdjoint (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) : IsSelfAdjoint (complexDirichletOperator Ω hbdd) :=
  PolyaBridge.ComplexInverseOperator.selfAdjoint _
    (complexDirichletResolventZero_injective Ω hopen hbdd)
    (complexDirichletResolventZero_symmetric Ω hbdd)
    (complexDirichletResolventZero_dense Ω hopen hbdd)

lemma complexDirichletOperator_closed (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) : (complexDirichletOperator Ω hbdd).IsClosed :=
  (complexDirichletOperator_selfAdjoint Ω hopen hbdd).isClosed

lemma complexDirichletOperator_inverse_apply (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (u : (complexDirichletOperator Ω hbdd).domain) :
    complexDirichletResolventZero Ω hbdd (complexDirichletOperator Ω hbdd u) =
      (u : ComplexDomainL2 Ω) :=
  PolyaBridge.ComplexInverseOperator.inverse_apply _
    (complexDirichletResolventZero_injective Ω hopen hbdd) u

lemma complexDirichletOperator_form_representation (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (u : ComplexH01 Ω) (f : ComplexDomainL2 Ω) :
    (∃ hu : complexInclusion Ω u ∈ (complexDirichletOperator Ω hbdd).domain,
      complexDirichletOperator Ω hbdd ⟨complexInclusion Ω u, hu⟩ = f) ↔
      ∀ v : ComplexH01 Ω, complexEnergyForm Ω u v = ⟪f, complexInclusion Ω v⟫_ℂ := by
  rw [complex_form_equation_iff_solution Ω hopen.measurableSet hbdd]
  constructor
  · rintro ⟨hu, huf⟩
    have hJu := complexDirichletOperator_inverse_apply Ω hopen hbdd
      ⟨complexInclusion Ω u, hu⟩
    rw [huf] at hJu
    apply complexInclusion_injective Ω hopen.measurableSet
    exact hJu.symm.trans (complexInclusion_solution Ω hbdd f).symm
  · intro hu
    have hJu : complexInclusion Ω u = complexDirichletResolventZero Ω hbdd f := by
      rw [hu]
      exact complexInclusion_solution Ω hbdd f
    have hm : complexInclusion Ω u ∈ (complexDirichletOperator Ω hbdd).domain := by
      rw [complexDirichletOperator_domain]
      exact ⟨f, hJu.symm⟩
    refine ⟨hm, ?_⟩
    have hv : (⟨complexInclusion Ω u, hm⟩ : (complexDirichletOperator Ω hbdd).domain) =
        PolyaBridge.ComplexInverseOperator.domainVector (complexDirichletResolventZero Ω hbdd) f :=
      Subtype.ext hJu
    rw [hv]
    exact PolyaBridge.ComplexInverseOperator.apply_vector _
      (complexDirichletResolventZero_injective Ω hopen hbdd) f

/-- The operator domain consists precisely of H₀¹ functions whose weak
Dirichlet Laplacian is represented by an L² function. -/
lemma complexDirichletOperator_domain_iff (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (f : ComplexDomainL2 Ω) :
    f ∈ (complexDirichletOperator Ω hbdd).domain ↔
      ∃ u : ComplexH01 Ω, complexInclusion Ω u = f ∧
        ∃ g : ComplexDomainL2 Ω, ∀ v : ComplexH01 Ω,
          complexEnergyForm Ω u v = ⟪g, complexInclusion Ω v⟫_ℂ := by
  constructor
  · intro hf
    let g := complexDirichletOperator Ω hbdd ⟨f, hf⟩
    refine ⟨complexFormSolution Ω hbdd g, ?_, g, ?_⟩
    · exact (complexInclusion_solution Ω hbdd g).trans
        (complexDirichletOperator_inverse_apply Ω hopen hbdd ⟨f, hf⟩)
    · exact complexFormSolution_equation Ω hopen.measurableSet hbdd g
  · rintro ⟨u, hu, g, hg⟩
    obtain ⟨hm, _⟩ := (complexDirichletOperator_form_representation Ω hopen hbdd u g).mpr hg
    exact hu ▸ hm

lemma complexDirichletOperator_nonneg (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (u : (complexDirichletOperator Ω hbdd).domain) :
    0 ≤ (⟪complexDirichletOperator Ω hbdd u, (u : ComplexDomainL2 Ω)⟫_ℂ).re := by
  rw [← complexDirichletOperator_inverse_apply Ω hopen hbdd u]
  by_cases hu : complexDirichletOperator Ω hbdd u = 0
  · simp [hu]
  · change 0 ≤ RCLike.re (⟪complexDirichletOperator Ω hbdd u,
      complexDirichletResolventZero Ω hbdd (complexDirichletOperator Ω hbdd u)⟫_ℂ)
    rw [inner_re_symm]
    exact (complexDirichletResolventZero_strictPositive Ω hopen hbdd _ hu).le

lemma complexDirichletOperator_eigenvector_iff_weak (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (u : ComplexH01 Ω) (lam : ℂ) :
    (∃ hu : complexInclusion Ω u ∈ (complexDirichletOperator Ω hbdd).domain,
      complexDirichletOperator Ω hbdd ⟨complexInclusion Ω u, hu⟩ =
        lam • complexInclusion Ω u) ↔
      ∀ v : ComplexH01 Ω, complexEnergyForm Ω u v =
        star lam * ⟪complexInclusion Ω u, complexInclusion Ω v⟫_ℂ := by
  rw [complexDirichletOperator_form_representation Ω hopen hbdd]
  simp only [inner_smul_left, starRingEnd_apply]

/-- Every eigenvalue of the actual complex partial operator is real and
strictly positive, including eigenvalues initially given as arbitrary complex
numbers. Thus no zero, negative or nonreal eigenvalues are omitted by the
positive-real spectral indexing. -/
lemma complexDirichletOperator_eigenvalue_positive_real (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (lam : ℂ)
    (u : (complexDirichletOperator Ω hbdd).domain)
    (hu0 : (u : ComplexDomainL2 Ω) ≠ 0)
    (hu : complexDirichletOperator Ω hbdd u = lam • (u : ComplexDomainL2 Ω)) :
    (lam.re : ℂ) = lam ∧ 0 < lam.re := by
  have hlam : lam ≠ 0 := by
    intro hzero
    have hAu : complexDirichletOperator Ω hbdd u = 0 := by simpa [hzero] using hu
    apply hu0
    rw [← complexDirichletOperator_inverse_apply Ω hopen hbdd u, hAu, map_zero]
  have hKu : complexDirichletResolventZero Ω hbdd (u : ComplexDomainL2 Ω) =
      lam⁻¹ • (u : ComplexDomainL2 Ω) :=
    PolyaBridge.ComplexInverseOperator.inverse_eigen_of_operator_eigen _
      (complexDirichletResolventZero_injective Ω hopen hbdd) lam hlam u hu
  have hKeigen : Module.End.HasEigenvalue
      (complexDirichletResolventZero Ω hbdd).toLinearMap lam⁻¹ := by
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨?_, hu0⟩
    exact Module.End.mem_eigenspace_iff.mpr hKu
  have hInvReal := complexDirichletResolventZero_hasEigenvalue_real Ω hbdd lam⁻¹ hKeigen
  have hReal : (lam.re : ℂ) = lam := by
    apply Complex.conj_eq_iff_re.mp
    have h := congrArg (fun z : ℂ => z⁻¹) (Complex.conj_eq_iff_re.mpr hInvReal)
    simpa only [map_inv₀, inv_inv] using h
  have hPos := complexDirichletResolventZero_strictPositive Ω hopen hbdd
    (u : ComplexDomainL2 Ω) hu0
  rw [hKu, ← hInvReal] at hPos
  simp only [inner_smul_left, inner_self_eq_norm_sq_to_K] at hPos
  rw [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal] at hPos
  change 0 < (((lam⁻¹).re : ℂ) * (‖(u : ComplexDomainL2 Ω)‖ : ℂ) ^ 2).re at hPos
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re] at hPos
  have hInvPos : 0 < (lam⁻¹).re :=
    (mul_pos_iff_of_pos_right (sq_pos_of_pos (norm_pos_iff.mpr hu0))).mp hPos
  have hInvRe : (lam⁻¹).re = lam.re⁻¹ := by
    calc
      (lam⁻¹).re = ((lam.re : ℂ)⁻¹).re :=
        congrArg (fun z : ℂ => (z⁻¹).re) hReal.symm
      _ = lam.re⁻¹ := by simp only [← Complex.ofReal_inv, Complex.ofReal_re]
  rw [hInvRe] at hInvPos
  exact ⟨hReal, inv_pos.mp hInvPos⟩

end DirichletBridge

noncomputable section

namespace PolyaBridge

variable {𝕜 H : Type*} [Field 𝕜] [AddCommGroup H] [Module 𝕜 H]

/-- Eigenvectors of a partially defined operator, viewed in the ambient space.
The definition requires actual domain membership and the operator equation. -/
def partialEigenspace (A : H →ₗ.[𝕜] H) (lam : 𝕜) : Submodule 𝕜 H :=
  (A.toFun - lam • A.domain.subtype).ker.map A.domain.subtype

theorem mem_partialEigenspace_iff (A : H →ₗ.[𝕜] H) (lam : 𝕜) (x : H) :
    x ∈ partialEigenspace A lam ↔
      ∃ hx : x ∈ A.domain, A ⟨x, hx⟩ = lam • x := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u.property, ?_⟩
    have h := LinearMap.mem_ker.mp hu
    change A u - lam • (u : H) = 0 at h
    exact sub_eq_zero.mp h
  · rintro ⟨hx, hAx⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    apply LinearMap.mem_ker.mpr
    change A ⟨x, hx⟩ - lam • x = 0
    exact sub_eq_zero.mpr hAx

end PolyaBridge

namespace DirichletBridge

open MeasureTheory Set
open scoped InnerProductSpace

theorem real_operator_eigenspace_eq_inverse (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (lam : ℝ) (hlam : lam ≠ 0) :
    PolyaBridge.partialEigenspace (dirichletOperator Ω hbdd) lam =
      Module.End.eigenspace (dirichletResolventZero Ω hbdd).toLinearMap lam⁻¹ := by
  ext x
  rw [PolyaBridge.mem_partialEigenspace_iff, Module.End.mem_eigenspace_iff]
  change (∃ hx : x ∈ (dirichletOperator Ω hbdd).domain,
    dirichletOperator Ω hbdd ⟨x, hx⟩ = lam • x) ↔
    dirichletResolventZero Ω hbdd x = lam⁻¹ • x
  constructor
  · rintro ⟨hx, hAx⟩
    simpa only [dirichletOperator, PolyaBridge.CoerciveForm.associatedOperator] using
      PolyaBridge.InverseOperator.inverse_eigen_of_operator_eigen
      (dirichletResolventZero Ω hbdd) (dirichletResolventZero_injective Ω hopen hbdd)
      lam hlam ⟨x, hx⟩ hAx
  · intro hKx
    have hdom := PolyaBridge.InverseOperator.eigenvector_mem_domain
      (dirichletResolventZero Ω hbdd) lam⁻¹ (inv_ne_zero hlam) x hKx
    refine ⟨hdom, ?_⟩
    simpa only [inv_inv, dirichletOperator, dirichletResolventZero, PolyaBridge.CoerciveForm.associatedOperator] using PolyaBridge.InverseOperator.eigenvector_apply
      (dirichletResolventZero Ω hbdd) (dirichletResolventZero_injective Ω hopen hbdd)
      lam⁻¹ (inv_ne_zero hlam) x hKx

theorem complex_operator_eigenspace_eq_inverse (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (lam : ℂ) (hlam : lam ≠ 0) :
    PolyaBridge.partialEigenspace (complexDirichletOperator Ω hbdd) lam =
      Module.End.eigenspace (complexDirichletResolventZero Ω hbdd).toLinearMap lam⁻¹ := by
  ext x
  rw [PolyaBridge.mem_partialEigenspace_iff, Module.End.mem_eigenspace_iff]
  change (∃ hx : x ∈ (complexDirichletOperator Ω hbdd).domain,
    complexDirichletOperator Ω hbdd ⟨x, hx⟩ = lam • x) ↔
    complexDirichletResolventZero Ω hbdd x = lam⁻¹ • x
  constructor
  · rintro ⟨hx, hAx⟩
    exact PolyaBridge.ComplexInverseOperator.inverse_eigen_of_operator_eigen
      (complexDirichletResolventZero Ω hbdd)
      (complexDirichletResolventZero_injective Ω hopen hbdd) lam hlam ⟨x, hx⟩ hAx
  · intro hKx
    have hdom := PolyaBridge.ComplexInverseOperator.eigenvector_mem_domain
      (complexDirichletResolventZero Ω hbdd) lam⁻¹ (inv_ne_zero hlam) x hKx
    refine ⟨hdom, ?_⟩
    simpa only [inv_inv, complexDirichletOperator,
      PolyaBridge.CoerciveForm.associatedOperator] using PolyaBridge.ComplexInverseOperator.eigenvector_apply
      (complexDirichletResolventZero Ω hbdd)
      (complexDirichletResolventZero_injective Ω hopen hbdd) lam⁻¹ (inv_ne_zero hlam) x hKx

theorem real_Dirichlet_eigenvalue_iff_indexed (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hne : Ω.Nonempty) (hbdd : Bornology.IsBounded Ω) (lam : ℝ) (hlam : 0 < lam) :
    (∃ x : DomainL2 Ω, x ≠ 0 ∧
      x ∈ PolyaBridge.partialEigenspace (dirichletOperator Ω hbdd) lam) ↔
      ∃ j : ℕ, 1 ≤ j ∧ spectralDirichletEigenvalue Ω hbdd j = lam := by
  rw [real_operator_eigenspace_eq_inverse Ω hopen hbdd lam hlam.ne']
  have h := PolyaBridge.SpectralDiscrete.eigenvalue_iff_indexed
    (dirichletResolventZero_compact Ω hopen hbdd)
    (dirichletResolventZero_symmetric Ω hbdd)
    (dirichletResolventZero_strictPositive Ω hopen hbdd)
    (domainL2_infinite Ω hopen hne) (inv_pos.mpr hlam)
  constructor
  · rintro ⟨x, hx, hKx⟩
    obtain ⟨j, hj, hμ⟩ := h.mp ⟨x, hx, Module.End.mem_eigenspace_iff.mp hKx⟩
    refine ⟨j, by omega, ?_⟩
    rw [spectralDirichletEigenvalue_eq_inverse Ω hbdd (by omega), hμ, inv_inv]
  · rintro ⟨j, hj, hEig⟩
    have hμ := congrArg (fun x : ℝ => x⁻¹) hEig
    rw [spectralDirichletEigenvalue_eq_inverse Ω hbdd hj] at hμ
    change (PolyaBridge.CompactSpectral.spectralEigenvalue
      (dirichletResolventZero Ω hbdd) j)⁻¹⁻¹ = lam⁻¹ at hμ
    rw [inv_inv] at hμ
    obtain ⟨x, hx, hKx⟩ := h.mpr ⟨j, by omega, hμ⟩
    exact ⟨x, hx, Module.End.mem_eigenspace_iff.mpr hKx⟩

theorem complex_real_Dirichlet_eigenvalue_iff (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (lam : ℝ) (hlam : lam ≠ 0) :
    (∃ x : ComplexDomainL2 Ω, x ≠ 0 ∧
      x ∈ PolyaBridge.partialEigenspace (complexDirichletOperator Ω hbdd) (lam : ℂ)) ↔
    (∃ x : DomainL2 Ω, x ≠ 0 ∧
      x ∈ PolyaBridge.partialEigenspace (dirichletOperator Ω hbdd) lam) := by
  rw [real_operator_eigenspace_eq_inverse Ω hopen hbdd lam hlam,
    complex_operator_eigenspace_eq_inverse Ω hopen hbdd (lam : ℂ)
      (Complex.ofReal_ne_zero.mpr hlam), ← Complex.ofReal_inv]
  constructor
  · rintro ⟨x, hx, hKx⟩
    obtain ⟨hr, hi⟩ :=
      (complexDirichletResolventZero_eigenspace_iff Ω hbdd lam⁻¹ x).mp hKx
    by_cases hre : reL2 Ω x = 0
    · have him : imL2 Ω x ≠ 0 := by
        intro him
        apply hx
        apply reL2_imL2_ext Ω
        · simpa only [map_zero] using hre
        · simpa only [map_zero] using him
      exact ⟨imL2 Ω x, him, hi⟩
    · exact ⟨reL2 Ω x, hre, hr⟩
  · rintro ⟨x, hx, hKx⟩
    refine ⟨ofRealL2 Ω x, ?_, ?_⟩
    · intro hzero
      apply hx
      have hr := congrArg (reL2 Ω) hzero
      simpa only [reL2_ofRealL2, map_zero] using hr
    · apply (complexDirichletResolventZero_eigenspace_iff Ω hbdd lam⁻¹ _).mpr
      simp only [reL2_ofRealL2, imL2_ofRealL2]
      exact ⟨hKx, by simp⟩

/-- The list exhausts the positive complex Dirichlet eigenvalues, and every
listed value is an eigenvalue of the actual complex partial operator. -/
theorem complex_Dirichlet_eigenvalue_iff_indexed (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hne : Ω.Nonempty) (hbdd : Bornology.IsBounded Ω) (lam : ℝ) (hlam : 0 < lam) :
    (∃ x : ComplexDomainL2 Ω, x ≠ 0 ∧
      x ∈ PolyaBridge.partialEigenspace (complexDirichletOperator Ω hbdd) (lam : ℂ)) ↔
      ∃ j : ℕ, 1 ≤ j ∧ spectralDirichletEigenvalue Ω hbdd j = lam :=
  (complex_real_Dirichlet_eigenvalue_iff Ω hopen hbdd lam hlam.ne').trans
    (real_Dirichlet_eigenvalue_iff_indexed Ω hopen hne hbdd lam hlam)

/-- The numbered spectral values repeat exactly as often as the dimension of the
actual real Dirichlet eigenspace. -/
theorem spectralDirichletEigenvalue_multiplicity_real (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hne : Ω.Nonempty) (hbdd : Bornology.IsBounded Ω) (lam : ℝ) (hlam : 0 < lam) :
    Set.ncard {j : ℕ | 0 < j ∧ spectralDirichletEigenvalue Ω hbdd j = lam} =
      Module.finrank ℝ (PolyaBridge.partialEigenspace (dirichletOperator Ω hbdd) lam) := by
  rw [real_operator_eigenspace_eq_inverse Ω hopen hbdd lam hlam.ne']
  have hset : {j : ℕ | 0 < j ∧ spectralDirichletEigenvalue Ω hbdd j = lam} =
      {j : ℕ | 0 < j ∧
        PolyaBridge.CompactSpectral.spectralEigenvalue (dirichletResolventZero Ω hbdd) j = lam⁻¹} := by
    ext j
    constructor
    · rintro ⟨hj, heq⟩
      refine ⟨hj, ?_⟩
      rw [spectralDirichletEigenvalue_eq_inverse Ω hbdd (by omega)] at heq
      simpa only [inv_inv] using (congrArg (fun x : ℝ => x⁻¹) heq)
    · rintro ⟨hj, heq⟩
      exact ⟨hj, by rw [spectralDirichletEigenvalue_eq_inverse Ω hbdd (by omega), heq, inv_inv]⟩
  rw [hset]
  exact PolyaBridge.SpectralMultiplicity.spectralEigenvalue_multiplicity_eq_finrank
    (dirichletResolventZero_compact Ω hopen hbdd)
    (dirichletResolventZero_symmetric Ω hbdd)
    (dirichletResolventZero_strictPositive Ω hopen hbdd)
    (domainL2_infinite Ω hopen hne) (inv_pos.mpr hlam)

/-- Complex multiplicity equals the number of occurrences in the very same
ordered list. No doubling of multiplicities occurs. -/
theorem spectralDirichletEigenvalue_multiplicity_complex (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hne : Ω.Nonempty) (hbdd : Bornology.IsBounded Ω) (lam : ℝ) (hlam : 0 < lam) :
    Set.ncard {j : ℕ | 0 < j ∧ spectralDirichletEigenvalue Ω hbdd j = lam} =
      Module.finrank ℂ
        (PolyaBridge.partialEigenspace (complexDirichletOperator Ω hbdd) (lam : ℂ)) := by
  rw [spectralDirichletEigenvalue_multiplicity_real Ω hopen hne hbdd lam hlam,
    real_operator_eigenspace_eq_inverse Ω hopen hbdd lam hlam.ne',
    complex_operator_eigenspace_eq_inverse Ω hopen hbdd (lam : ℂ)
      (Complex.ofReal_ne_zero.mpr hlam.ne'), ← Complex.ofReal_inv]
  exact (complexDirichletResolventZero_multiplicity Ω hopen hbdd lam⁻¹
    (inv_ne_zero hlam.ne')).symm

end DirichletBridge

noncomputable section

/-- Strict Dirichlet Pólya for the ordered eigenvalues of the actual gradient-form
Dirichlet operator. The spectral definition is independent of the original min-max. -/
theorem main (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (hsc : SimplyConnectedSpace Ω) (j : ℕ) (hj : 1 ≤ j) :
    4 * Real.pi * j < (MeasureTheory.volume Ω).toReal *
      DirichletBridge.spectralDirichletEigenvalue Ω hbdd j :=
  DirichletBridge.strict_polya_spectral Ω hopen hbdd hsc j hj

/-- Inclusive spectral counting, with multiplicity, for the same Dirichlet operator. -/
theorem main_counting (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (hsc : SimplyConnectedSpace Ω) (E : ℝ) (hE : 0 < E) :
    (DirichletBridge.spectralDirichletCountingFunction Ω hbdd E : ℝ) <
      (MeasureTheory.volume Ω).toReal * E / (4 * Real.pi) :=
  DirichletBridge.strict_polya_spectral_counting Ω hopen hbdd hsc E hE

#print axioms DirichletBridge.dirichletEigenvalue_eq_spectral
#print axioms DirichletBridge.spectralDirichletEigenvalue_multiplicity_complex
#print axioms DirichletBridge.complexDirichletOperator_form_representation
#print axioms DirichletBridge.complexDirichletOperator_selfAdjoint
#print axioms DirichletBridge.complex_Dirichlet_eigenvalue_iff_indexed
#print axioms DirichletBridge.complexDirichletOperator_eigenvalue_positive_real
#print axioms DirichletBridge.complexEnergyForm_complete
#print axioms DirichletBridge.complexH01_norm_sq
#print axioms DirichletBridge.complexSmoothCoreJet_dense
#print axioms main_counting
#print axioms main

end

end


