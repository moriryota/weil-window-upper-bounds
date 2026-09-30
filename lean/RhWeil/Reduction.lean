import RhWeil.Construction
import RhWeil.RHatBound
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Reduction of `TheoremA.Inputs` to two quantitative estimates

With `η(y) = smoothTransition((y + a)/τ)`, `k = η e`, `r = (1 - η) e`, all qualitative clauses of
`TheoremA.Inputs` hold for every even real `φ ∈ C³_c` with `φ(0) = ∫φ = 0` and support in `[-λ, λ]`.
What remains is: `‖k‖² ≥ c₀` and `(wL1 r + wL1 r')² ≤ C₁ λ^p e^{-2πλ²}`.
-/

noncomputable section

namespace RhWeil
namespace Construction

open Complex MeasureTheory Set Filter Topology Real Zeta23
open scoped FourierTransform

/-- The cut-off `η(y) = smoothTransition((y + a)/τ)`. -/
def eta (a τ : ℝ) (y : ℝ) : ℂ := (Real.smoothTransition ((y + a) / τ) : ℂ)

def kF (φ : ℝ → ℂ) (a τ : ℝ) (y : ℝ) : ℂ := eta a τ y * eF φ y
def rF (φ : ℝ → ℂ) (a τ : ℝ) (y : ℝ) : ℂ := (1 - eta a τ y) * eF φ y

theorem contDiff_eta (a τ : ℝ) {m : ℕ∞} : ContDiff ℝ m (eta a τ) :=
  Complex.ofRealCLM.contDiff.comp
    (Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const τ))

theorem eta_eq_zero {a τ y : ℝ} (hτ : 0 < τ) (hy : y ≤ -a) : eta a τ y = 0 := by
  simp [eta, Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith : y + a ≤ 0) hτ.le)]

theorem eta_eq_one {a τ y : ℝ} (hτ : 0 < τ) (hy : -a + τ ≤ y) : eta a τ y = 1 := by
  simp [eta, Real.smoothTransition.one_of_one_le ((le_div_iff₀ hτ).2 (by linarith : 1 * τ ≤ y + a))]

theorem norm_one_sub_eta_le (a τ y : ℝ) : ‖1 - eta a τ y‖ ≤ 1 := by
  have h0 := Real.smoothTransition.nonneg ((y + a) / τ)
  have h1 := Real.smoothTransition.le_one ((y + a) / τ)
  rw [eta, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith)]
  linarith

theorem eF_eq_zero_of_ge {φ : ℝ → ℂ} {L : ℝ} (hsupp : ∀ v, L ≤ |v| → φ v = 0) {y : ℝ}
    (hy : L ≤ Real.exp y) : eF φ y = 0 := by
  have : ∀ n : ℕ, φ (((n : ℝ) + 1) * Real.exp y) = 0 := by
    intro n; apply hsupp
    rw [abs_of_nonneg (by positivity)]
    exact hy.trans (le_mul_of_one_le_left (Real.exp_pos y).le (by linarith [n.cast_nonneg (α := ℝ)]))
  simp [eF, this]

theorem exists_bound_deriv_smoothTransition : ∃ D, ∀ x, ‖deriv Real.smoothTransition x‖ ≤ D := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max M 0, fun x => ?_⟩
  by_cases hx : x ∈ Icc (0:ℝ) 1
  · exact (hM x hx).trans (le_max_left _ _)
  · simp only [mem_Icc, not_and_or, not_le] at hx
    have : deriv Real.smoothTransition x = 0 := by
      rcases hx with hx | hx
      · have e : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 0 := by
          filter_upwards [Iio_mem_nhds hx] with w hw using Real.smoothTransition.zero_of_nonpos hw.le
        simp [e.deriv_eq]
      · have e : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 1 := by
          filter_upwards [Ioi_mem_nhds hx] with w hw using Real.smoothTransition.one_of_one_le hw.le
        simp [e.deriv_eq]
    rw [this, norm_zero]; exact le_max_right _ _

/-! ### Properties of `k` and `r` -/

section Props

variable {φ : ℝ → ℂ} {L a τ : ℝ}

theorem contDiff_kF (hφ : ContDiff ℝ 2 φ) (hL : 0 ≤ L) (hsupp : ∀ v, L ≤ |v| → φ v = 0) :
    ContDiff ℝ 2 (kF φ a τ) :=
  (contDiff_eta a τ).mul (contDiff_eF hφ hL hsupp)

theorem contDiff_rF (hφ : ContDiff ℝ 2 φ) (hL : 0 ≤ L) (hsupp : ∀ v, L ≤ |v| → φ v = 0) :
    ContDiff ℝ 2 (rF φ a τ) :=
  (contDiff_const.sub (contDiff_eta a τ)).mul (contDiff_eF hφ hL hsupp)

theorem kF_eq_zero_of_le (hτ : 0 < τ) {y : ℝ} (hy : y ≤ -a) : kF φ a τ y = 0 := by
  simp [kF, eta_eq_zero hτ hy]

theorem rF_eq_zero_of_ge (hτ : 0 < τ) {y : ℝ} (hy : -a + τ ≤ y) : rF φ a τ y = 0 := by
  simp [rF, eta_eq_one hτ hy]

theorem tsupport_kF (hτ : 0 < τ) (hL0 : 0 < L) (hsupp : ∀ v, L ≤ |v| → φ v = 0) :
    tsupport (kF φ a τ) ⊆ Icc (-a) (Real.log L) := by
  refine closure_minimal (fun y hy => ?_) isClosed_Icc
  simp only [Function.mem_support] at hy
  constructor
  · by_contra h; push_neg at h; exact hy (kF_eq_zero_of_le hτ h.le)
  · by_contra h; push_neg at h
    apply hy
    simp only [kF]
    rw [eF_eq_zero_of_ge hsupp (by rw [← Real.exp_log hL0]; exact Real.exp_le_exp.2 h.le), mul_zero]

theorem kF_real (hreal : ∀ v, (starRingEnd ℂ) (φ v) = φ v) (y : ℝ) :
    (starRingEnd ℂ) (kF φ a τ y) = kF φ a τ y := by
  simp only [kF, eF, eta, map_mul, Complex.conj_ofReal, Complex.conj_tsum, hreal]

theorem norm_eta_le (y : ℝ) : ‖eta a τ y‖ ≤ 1 := by
  rw [eta, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

theorem hasDerivAt_eta (hτ : 0 < τ) (y : ℝ) :
    HasDerivAt (eta a τ) ((deriv Real.smoothTransition ((y + a) / τ) / τ : ℝ)) y := by
  have h1 : HasDerivAt (fun y : ℝ => (y + a) / τ) (1 / τ) y :=
    ((hasDerivAt_id y).add_const a).div_const τ
  have h2 := ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
    ((y + a) / τ)).hasDerivAt.comp y h1
  have h3 := h2.ofReal_comp
  refine h3.congr_deriv ?_
  simp only [div_eq_mul_inv, one_mul]

end Props

/-! ### Decay bounds, integrability, radical property, and the reduction -/

section Main

variable {φ : ℝ → ℂ} {L a τ : ℝ}

theorem hasDerivAt_rF (hφ : ContDiff ℝ 1 φ) (hL : 0 ≤ L) (hsupp : ∀ v, L ≤ |v| → φ v = 0)
    (hτ : 0 < τ) (y : ℝ) :
    HasDerivAt (rF φ a τ)
      (-(((deriv Real.smoothTransition ((y + a) / τ) / τ : ℝ)) : ℂ) * eF φ y +
        (1 - eta a τ y) * deriv (eF φ) y) y := by
  have he := hasDerivAt_eF hφ hL hsupp y
  have := ((hasDerivAt_const y (1 : ℂ)).sub (hasDerivAt_eta (a := a) hτ y)).mul
    (he.deriv ▸ he : HasDerivAt (eF φ) (deriv (eF φ) y) y)
  have e : ((fun _ => (1:ℂ)) - eta a τ) * eF φ = rF φ a τ := by funext y; simp [rF]
  rw [e] at this
  simpa [zero_sub, neg_mul] using this

theorem exists_bounds (hφ : ContDiff ℝ 3 φ) (hL : 0 ≤ L) (hsupp : ∀ v, L ≤ |v| → φ v = 0)
    (heven : ∀ v, φ (-v) = φ v) (h00 : φ 0 = 0) (hint : 𝓕 φ 0 = 0) (hτ : 0 < τ) :
    ∃ K, ∀ y, ‖kF φ a τ y‖ ≤ K * Real.exp (3 / 2 * y) ∧ ‖rF φ a τ y‖ ≤ K * Real.exp (3 / 2 * y) ∧
      ‖deriv (rF φ a τ) y‖ ≤ K * Real.exp (3 / 2 * y) := by
  obtain ⟨K0, b0⟩ : ∃ K0, ∀ y, ‖eF φ y‖ ≤ K0 * Real.exp (3 / 2 * y) :=
    ⟨_, norm_eF_le (hφ.of_le (by norm_num)) hsupp heven h00 hint⟩
  obtain ⟨K1, b1⟩ := norm_deriv_eF_le hφ hL hsupp heven h00 hint
  obtain ⟨D, hD⟩ := exists_bound_deriv_smoothTransition
  have hK0 : 0 ≤ K0 := by have := (norm_nonneg _).trans (b0 0); simpa using this
  have hK1 : 0 ≤ K1 := by have := (norm_nonneg _).trans (b1 0); simpa using this
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  refine ⟨K0 + D / τ * K0 + K1, fun y => ⟨?_, ?_, ?_⟩⟩
  · calc ‖kF φ a τ y‖ = ‖eta a τ y‖ * ‖eF φ y‖ := norm_mul _ _
      _ ≤ 1 * (K0 * Real.exp (3 / 2 * y)) := by
          gcongr; exact norm_eta_le y; exact b0 y
      _ ≤ _ := by nlinarith [Real.exp_pos (3 / 2 * y), div_nonneg hD0 hτ.le, mul_nonneg (div_nonneg hD0 hτ.le) hK0]
  · calc ‖rF φ a τ y‖ = ‖1 - eta a τ y‖ * ‖eF φ y‖ := norm_mul _ _
      _ ≤ 1 * (K0 * Real.exp (3 / 2 * y)) := by
          gcongr; exact norm_one_sub_eta_le a τ y; exact b0 y
      _ ≤ _ := by nlinarith [Real.exp_pos (3 / 2 * y), div_nonneg hD0 hτ.le, mul_nonneg (div_nonneg hD0 hτ.le) hK0]
  · rw [(hasDerivAt_rF (hφ.of_le (by norm_num)) hL hsupp hτ y).deriv]
    have e1 : ‖(((deriv Real.smoothTransition ((y + a) / τ) / τ : ℝ)) : ℂ)‖ ≤ D / τ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hτ]
      gcongr; simpa using hD ((y + a) / τ)
    calc ‖-(((deriv Real.smoothTransition ((y + a) / τ) / τ : ℝ)) : ℂ) * eF φ y +
          (1 - eta a τ y) * deriv (eF φ) y‖
        ≤ D / τ * (K0 * Real.exp (3 / 2 * y)) + 1 * (K1 * Real.exp (3 / 2 * y)) := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_mul, norm_neg]; exact mul_le_mul e1 (b0 y) (norm_nonneg _) (by positivity)
          · rw [norm_mul]; exact mul_le_mul (norm_one_sub_eta_le a τ y) (b1 y) (norm_nonneg _) zero_le_one
      _ ≤ _ := by nlinarith [Real.exp_pos (3 / 2 * y), mul_nonneg hK0 (Real.exp_pos (3 / 2 * y)).le]

end Main

/-! ### The reduction theorem -/

section Reduction

variable {φ : ℝ → ℂ} {L a τ : ℝ}

theorem paperFT_eF_eq_add (hφ : ContDiff ℝ 3 φ) (hL : 0 ≤ L) (hsupp : ∀ v, L ≤ |v| → φ v = 0)
    (heven : ∀ v, φ (-v) = φ v) (h00 : φ 0 = 0) (hint : 𝓕 φ 0 = 0) (hτ : 0 < τ) (ha : 0 ≤ a)
    (hLa : L ≤ Real.exp a) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    paperFT (eF φ) z = paperFT (kF φ a τ) z + paperFT (rF φ a τ) z := by
  obtain ⟨K, hK⟩ := exists_bounds (a := a) hφ hL hsupp heven h00 hint hτ
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  have ck : Continuous (kF φ a τ) := (contDiff_kF hφ2 hL hsupp).continuous
  have cr : Continuous (rF φ a τ) := (contDiff_rF hφ2 hL hsupp).continuous
  have ik := integrable_weighted_of_bound ck (T := max 0 a) (le_max_left _ _) (fun y => (hK y).1)
    (fun y hy => by
      simp only [kF]
      rw [eF_eq_zero_of_ge hsupp (hLa.trans (Real.exp_le_exp.2 ((le_max_right _ _).trans hy))),
        mul_zero])
  have ir := integrable_weighted_of_bound cr (T := max 0 (-a + τ)) (le_max_left _ _)
    (fun y => (hK y).2.1) (fun y hy => rF_eq_zero_of_ge hτ ((le_max_right _ _).trans hy))
  unfold paperFT
  rw [← integral_add (integrable_mul_cexp ck ik hz) (integrable_mul_cexp cr ir hz)]
  congr 1; ext y
  simp only [kF, rF]; ring

/-- **Reduction.** `TheoremA.Inputs` follows from the two quantitative estimates for the
explicit `k = η e`, `r = (1 - η) e`. -/
theorem inputs_of_quantitative
    (h : ∃ c₀ C₁ p lam₀ : ℝ, 0 < c₀ ∧ 0 ≤ C₁ ∧ 1 ≤ lam₀ ∧ ∀ lam ≥ lam₀, ∃ (φ : ℝ → ℂ) (L τ : ℝ),
      ContDiff ℝ 3 φ ∧ (∀ v, (starRingEnd ℂ) (φ v) = φ v) ∧ (∀ v, φ (-v) = φ v) ∧ φ 0 = 0 ∧
      𝓕 φ 0 = 0 ∧ 0 < L ∧ L ≤ lam ∧ (∀ v, L ≤ |v| → φ v = 0) ∧ 0 < τ ∧
      c₀ ≤ TheoremA.l2sq (kF φ (Real.log lam) τ) ∧
      (TheoremA.wL1 (rF φ (Real.log lam) τ) + TheoremA.wL1 (deriv (rF φ (Real.log lam) τ))) ^ 2
        ≤ C₁ * lam ^ p * Real.exp (-2 * Real.pi * lam ^ 2)) :
    TheoremA.Inputs := by
  obtain ⟨c₀, C₁, p, lam₀, hc₀, hC₁, hlam₀, hq⟩ := h
  refine ⟨⟨c₀, C₁, p, lam₀, hc₀, hC₁, fun lam hlam => ?_⟩⟩
  obtain ⟨φ, L, τ, hφ, hreal, heven, h00, hint, hL0, hLlam, hsupp, hτ, hnorm, hq'⟩ := hq lam hlam
  have hlam1 : 1 ≤ lam := hlam₀.trans hlam
  have hlampos : 0 < lam := lt_of_lt_of_le one_pos hlam1
  set a := Real.log lam
  have ha : 0 ≤ a := Real.log_nonneg hlam1
  have hLa : L ≤ Real.exp a := by rw [Real.exp_log hlampos]; exact hLlam
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  obtain ⟨K, hK⟩ := exists_bounds (a := a) hφ hL0.le hsupp heven h00 hint hτ
  have crF := contDiff_rF (a := a) (τ := τ) hφ2 hL0.le hsupp
  refine ⟨kF φ a τ, rF φ a τ, deriv (rF φ a τ), ⟨contDiff_kF hφ2 hL0.le hsupp, ?_⟩,
    kF_real hreal, hnorm, ?_, fun y => (crF.differentiable (by norm_num) y).hasDerivAt,
    crF.continuous_deriv (by norm_num), ?_, ?_, hq'⟩
  · refine (tsupport_kF hτ hL0 hsupp).trans (Icc_subset_Icc le_rfl ?_)
    exact Real.log_le_log hL0 hLlam
  · intro ρ hρ
    have hρ' : Zeta23.IsNontrivialZero ρ := hρ
    have hz := Radical.paperFT_Esum_zero_C2 hφ2 hsupp heven h00 hint hρ'
    have heq : (fun y => Radical.Esum φ (Real.exp y)) = eF φ := funext fun y => (eF_eq_Esum φ y).symm
    rw [heq] at hz
    have s1 := TheoremA.abs_im_gammaOf_le hρ
    have s2 : |(-gammaOf ρ).im| ≤ 1 / 2 := by simpa [abs_neg] using s1
    rw [paperFT_eF_eq_add hφ hL0.le hsupp heven h00 hint hτ ha hLa s1] at hz
    rw [paperFT_eF_eq_add hφ hL0.le hsupp heven h00 hint hτ ha hLa s2] at hz
    exact ⟨eq_neg_of_add_eq_zero_left hz.1, eq_neg_of_add_eq_zero_left hz.2⟩
  · exact integrable_weighted_of_bound crF.continuous (T := max 0 (-a + τ)) (le_max_left _ _)
      (fun y => (hK y).2.1) (fun y hy => rF_eq_zero_of_ge hτ ((le_max_right _ _).trans hy))
  · refine integrable_weighted_of_bound (crF.continuous_deriv (by norm_num))
      (T := max 0 (-a + τ) + 1) (by positivity) (fun y => (hK y).2.2) (fun y hy => ?_)
    have hy' : -a + τ < y := by linarith [le_max_right 0 (-a + τ)]
    have e : rF φ a τ =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds hy'] with w hw using rF_eq_zero_of_ge hτ hw.le
    simp [e.deriv_eq]

end Reduction

end Construction
end RhWeil
