import RhWeil.Reduction

/-!
# Quantitative estimates from tail bounds of `𝓕φ` (sup form of Lemma F5)

If `|𝓕φ(ξ)| ≤ M/ξ²` only for `|ξ| ≥ Ξ`, then for `0 < u ≤ 1/Ξ`, `|Σ_{n≥1} φ(n u)| ≤ M ζ(2) u`.
This gives `wL1 r` and `wL1 r'` in terms of the tail constants of `φ` and `ψ₁ = x φ'`.
-/

noncomputable section

namespace RhWeil
namespace Radical

open Complex MeasureTheory Set Filter Asymptotics Topology Real
open scoped FourierTransform

variable {φ : ℝ → ℂ} {L : ℝ}

theorem norm_fourier_scaled_tail {M Ξ : ℝ} (h0 : 𝓕 φ 0 = 0)
    (hFt : ∀ ξ, Ξ ≤ |ξ| → ‖𝓕 φ ξ‖ ≤ M / ξ ^ 2) {u : ℝ} (hu : 0 < u) (huΞ : u * Ξ ≤ 1)
    (m : ℤ) : ‖𝓕 (fun t => φ (u * t)) m‖ ≤ M * u * (1 / (m : ℝ) ^ 2) := by
  rw [fourier_comp_mul φ hu, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hu)]
  rcases eq_or_ne m 0 with rfl | hm
  · simp [h0]
  have hm' : (1:ℝ) ≤ |(m : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hm
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hξ : Ξ ≤ |(m : ℝ) / u| := by
    rw [abs_div, abs_of_pos hu, le_div_iff₀ hu]
    nlinarith
  calc u⁻¹ * ‖𝓕 φ ((m : ℝ) / u)‖ ≤ u⁻¹ * (M / ((m : ℝ) / u) ^ 2) := by
        gcongr; exact hFt _ hξ
    _ = M * u * (1 / (m : ℝ) ^ 2) := by field_simp

/-- **Tail form of the Poisson bound.** -/
theorem bound_Fsum_tail (hφc : Continuous φ) (hsupp : ∀ v, L ≤ |v| → φ v = 0)
    (heven : ∀ v, φ (-v) = φ v) (h00 : φ 0 = 0) {C : ℝ} (hF : ∀ ξ, ‖𝓕 φ ξ‖ ≤ C / ξ ^ 2)
    {M Ξ : ℝ} (hFt : ∀ ξ, Ξ ≤ |ξ| → ‖𝓕 φ ξ‖ ≤ M / ξ ^ 2) {u : ℝ} (hu : 0 < u)
    (huΞ : u * Ξ ≤ 1) :
    ‖Fsum φ u‖ ≤ M * (∑' m : ℤ, 1 / (m : ℝ) ^ 2) / 2 * u := by
  have h0 : 𝓕 φ 0 = 0 := by
    have := hF 0; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero] at this
    exact norm_le_zero_iff.1 this
  set f : ℝ → ℂ := fun t => φ (u * t) with hf_def
  have hfc : Continuous f := hφc.comp (continuous_const.mul continuous_id)
  have hsuppf : ∀ t, L / u < |t| → f t = 0 := by
    intro t ht
    apply hsupp
    rw [abs_mul, abs_of_pos hu]
    have := (div_lt_iff₀' hu).1 ht; linarith
  have hfO := isBigO_cocompact_of_supp hsuppf 2
  have hFf := norm_fourier_scaled_le hF hu
  have hC : 0 ≤ C := by
    have h1 := (norm_nonneg _).trans (hF 1); simpa using h1
  have hFfO : (𝓕 f) =O[cocompact ℝ] (|·| ^ (-(2:ℝ))) := by
    refine IsBigO.of_bound (C * u) (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_neg (abs_nonneg _),
      Real.rpow_two, sq_abs, ← div_eq_mul_inv]
    exact hFf ξ
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay hfc (by norm_num : (1:ℝ) < 2) hfO hFfO 0
  simp only [zero_add, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] at hP
  have hle := norm_fourier_scaled_tail h0 hFt hu huΞ
  have hM : 0 ≤ M * u := by
    have := (norm_nonneg _).trans (hle 1); simpa using this
  have hsum1 : Summable fun m : ℤ => M * u * (1 / (m : ℝ) ^ 2) :=
    (summable_one_div_int_pow.2 (by norm_num : 1 < 2)).mul_left (M * u)
  have hsumF : Summable fun m : ℤ => ‖𝓕 f m‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsum1
  have hZ := tsum_int_eq_two_Fsum heven h00 (summable_int_of_supp hsuppf)
  have key : ‖2 * Fsum φ u‖ ≤ M * u * ∑' m : ℤ, 1 / (m : ℝ) ^ 2 := by
    rw [← hZ]
    change ‖∑' n : ℤ, f n‖ ≤ _
    rw [hP, ← tsum_mul_left]
    exact (norm_tsum_le_tsum_norm hsumF).trans (hsumF.tsum_le_tsum hle hsum1)
  rw [norm_mul, Complex.norm_two] at key
  calc ‖Fsum φ u‖ = (2 * ‖Fsum φ u‖) / 2 := by ring
    _ ≤ (M * u * ∑' m : ℤ, 1 / (m : ℝ) ^ 2) / 2 := by gcongr
    _ = M * (∑' m : ℤ, 1 / (m : ℝ) ^ 2) / 2 * u := by ring

end Radical

namespace Construction

open Radical Complex MeasureTheory Set Filter Asymptotics Topology Real
open scoped FourierTransform

variable {φ : ℝ → ℂ} {L a τ : ℝ}

/-- `‖e(y)‖ e^{|y|/2} ≤ K e^y` for `y ≤ y₁ ≤ 0`, from a tail bound valid on `|ξ| ≥ Ξ`, `e^{y₁} Ξ ≤ 1`. -/
theorem norm_eF_weight_le (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ v, L ≤ |v| → φ v = 0)
    (heven : ∀ v, φ (-v) = φ v) (h00 : φ 0 = 0) (hint : 𝓕 φ 0 = 0) {M Ξ : ℝ} (hΞ : 0 ≤ Ξ)
    (hFt : ∀ ξ, Ξ ≤ |ξ| → ‖𝓕 φ ξ‖ ≤ M / ξ ^ 2) {y₁ : ℝ} (hy₁ : y₁ ≤ 0)
    (hΞy : Real.exp y₁ * Ξ ≤ 1) {y : ℝ} (hy : y ≤ y₁) :
    ‖eF φ y‖ * Real.exp (|y| / 2) ≤ M * (∑' m : ℤ, 1 / (m : ℝ) ^ 2) / 2 * Real.exp y := by
  have hs : HasCompactSupport φ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0:ℝ) L) fun v hv => hsupp v ?_
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hv
    exact hv.le
  have huΞ : Real.exp y * Ξ ≤ 1 :=
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hy) hΞ).trans hΞy
  have hb := bound_Fsum_tail hφ.continuous hsupp heven h00
    (norm_fourier_le_of_contDiff_two hφ hs hint) hFt (Real.exp_pos y) huΞ
  rw [eF_eq_mul_Fsum, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), abs_of_nonpos (hy.trans hy₁)]
  calc Real.exp (y / 2) * ‖Fsum φ (Real.exp y)‖ * Real.exp (-y / 2)
      = ‖Fsum φ (Real.exp y)‖ * (Real.exp (y / 2) * Real.exp (-y / 2)) := by ring
    _ = ‖Fsum φ (Real.exp y)‖ := by
        rw [← Real.exp_add, show y / 2 + -y / 2 = 0 by ring, Real.exp_zero, mul_one]
    _ ≤ _ := hb

theorem deriv_smoothTransition_of_neg {x : ℝ} (hx : x < 0) : deriv Real.smoothTransition x = 0 := by
  have e : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds hx] with w hw using Real.smoothTransition.zero_of_nonpos hw.le
  simp [e.deriv_eq]

/-- `wL1 r ≤ K e^{y₁}` with `y₁ = -a + τ`. -/
theorem wL1_rF_le (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ v, L ≤ |v| → φ v = 0)
    (heven : ∀ v, φ (-v) = φ v) (h00 : φ 0 = 0) (hint : 𝓕 φ 0 = 0) {M Ξ : ℝ} (hΞ : 0 ≤ Ξ)
    (hFt : ∀ ξ, Ξ ≤ |ξ| → ‖𝓕 φ ξ‖ ≤ M / ξ ^ 2) (hτ : 0 < τ) (hy₁ : -a + τ ≤ 0)
    (hΞy : Real.exp (-a + τ) * Ξ ≤ 1) :
    TheoremA.wL1 (rF φ a τ) ≤ M * (∑' m : ℤ, 1 / (m : ℝ) ^ 2) / 2 * Real.exp (-a + τ) := by
  set K := M * (∑' m : ℤ, 1 / (m : ℝ) ^ 2) / 2
  have hbound : ∀ y, ‖rF φ a τ y‖ * Real.exp (|y| / 2) ≤
      Set.indicator (Iic (-a + τ)) (fun y => K * Real.exp y) y := by
    intro y
    by_cases hy : y ≤ -a + τ
    · rw [Set.indicator_of_mem (show y ∈ Iic (-a + τ) from hy)]
      calc ‖rF φ a τ y‖ * Real.exp (|y| / 2) ≤ ‖eF φ y‖ * Real.exp (|y| / 2) := by
            gcongr
            rw [rF, norm_mul]
            exact mul_le_of_le_one_left (norm_nonneg _) (norm_one_sub_eta_le a τ y)
        _ ≤ _ := norm_eF_weight_le hφ hsupp heven h00 hint hΞ hFt hy₁ hΞy hy
    · push_neg at hy
      rw [rF_eq_zero_of_ge hτ hy.le, norm_zero, zero_mul,
        Set.indicator_of_notMem (show y ∉ Iic (-a + τ) from not_le.2 hy)]
  have hint2 : Integrable (Set.indicator (Iic (-a + τ)) fun y => K * Real.exp y) :=
    (integrable_indicator_iff measurableSet_Iic).2 ((integrableOn_exp_Iic _).const_mul _)
  unfold TheoremA.wL1
  calc ∫ y, ‖rF φ a τ y‖ * Real.exp (|y| / 2)
      ≤ ∫ y, Set.indicator (Iic (-a + τ)) (fun y => K * Real.exp y) y :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => by positivity) hint2
          (Filter.Eventually.of_forall hbound)
    _ = K * Real.exp (-a + τ) := by
        rw [integral_indicator measurableSet_Iic, integral_const_mul, integral_exp_Iic]

/-- `wL1 r' ≤ (D K + K/2 + K₁) e^{y₁}`, `K = M ζ₂/2`, `K₁ = M₁ ζ₂/2` (`ζ₂ = Σ_{m∈ℤ} m⁻²`). -/
theorem wL1_deriv_rF_le (hφ : ContDiff ℝ 3 φ) (hL : 0 ≤ L) (hsupp : ∀ v, L ≤ |v| → φ v = 0)
    (heven : ∀ v, φ (-v) = φ v) (h00 : φ 0 = 0) (hint : 𝓕 φ 0 = 0) {M M₁ Ξ : ℝ} (hΞ : 0 ≤ Ξ)
    (hFt : ∀ ξ, Ξ ≤ |ξ| → ‖𝓕 φ ξ‖ ≤ M / ξ ^ 2)
    (hFt1 : ∀ ξ, Ξ ≤ |ξ| → ‖𝓕 (psi1 φ) ξ‖ ≤ M₁ / ξ ^ 2) (hτ : 0 < τ) (hy₁ : -a + τ ≤ 0)
    (hΞy : Real.exp (-a + τ) * Ξ ≤ 1) {D : ℝ} (hD : ∀ x, ‖deriv Real.smoothTransition x‖ ≤ D) :
    TheoremA.wL1 (deriv (rF φ a τ)) ≤
      (D * (M * (∑' m : ℤ, 1 / (m : ℝ) ^ 2) / 2) + (M * (∑' m : ℤ, 1 / (m : ℝ) ^ 2) / 2) / 2 +
        M₁ * (∑' m : ℤ, 1 / (m : ℝ) ^ 2) / 2) * Real.exp (-a + τ) := by
  set Z := ∑' m : ℤ, 1 / (m : ℝ) ^ 2
  set K := M * Z / 2
  set K₁ := M₁ * Z / 2
  set y₁ := -a + τ
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hd : Differentiable ℝ φ := hφ1.differentiable one_ne_zero
  have hs : HasCompactSupport φ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0:ℝ) L) fun v hv => hsupp v ?_
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hv
    exact hv.le
  have bφ := fun {y : ℝ} (hy : y ≤ y₁) =>
    norm_eF_weight_le hφ2 hsupp heven h00 hint hΞ hFt hy₁ hΞy hy
  have bψ := fun {y : ℝ} (hy : y ≤ y₁) =>
    norm_eF_weight_le (contDiff_psi1 hφ) (psi1_supp hsupp) (psi1_even hd heven) (by simp [psi1])
      (fourier_psi1_zero hφ1 hs hint) hΞ hFt1 hy₁ hΞy hy
  have hK : 0 ≤ K := by
    have := (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le).trans (bφ (le_refl y₁))
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  set c := D / τ * K * Real.exp y₁
  have hbound : ∀ y, ‖deriv (rF φ a τ) y‖ * Real.exp (|y| / 2) ≤
      Set.indicator (Icc (-a) y₁) (fun _ => c) y +
        Set.indicator (Iic y₁) (fun y => (K / 2 + K₁) * Real.exp y) y := by
    intro y
    by_cases hy : y ≤ y₁
    · rw [Set.indicator_of_mem (show y ∈ Iic y₁ from hy),
        (hasDerivAt_rF hφ1 hL hsupp hτ y).deriv, (hasDerivAt_eF hφ1 hL hsupp y).deriv]
      have w := Real.exp_pos (|y| / 2)
      have t1 : ‖-(((deriv Real.smoothTransition ((y + a) / τ) / τ : ℝ)) : ℂ) * eF φ y‖ *
          Real.exp (|y| / 2) ≤ Set.indicator (Icc (-a) y₁) (fun _ => c) y := by
        by_cases ha : -a ≤ y
        · rw [Set.indicator_of_mem (show y ∈ Icc (-a) y₁ from ⟨ha, hy⟩), norm_mul, norm_neg,
            Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hτ]
          have h1 : |deriv Real.smoothTransition ((y + a) / τ)| ≤ D := by
            simpa using hD ((y + a) / τ)
          calc |deriv Real.smoothTransition ((y + a) / τ)| / τ * ‖eF φ y‖ * Real.exp (|y| / 2)
              = |deriv Real.smoothTransition ((y + a) / τ)| / τ * (‖eF φ y‖ * Real.exp (|y| / 2)) := by ring
            _ ≤ D / τ * (K * Real.exp y) :=
                mul_le_mul (div_le_div_of_nonneg_right h1 hτ.le) (bφ hy) (by positivity) (by positivity)
            _ ≤ c := by
                simp only [c]; rw [mul_assoc]; gcongr
        · push_neg at ha
          rw [Set.indicator_of_notMem (show y ∉ Icc (-a) y₁ from fun h => not_le.2 ha h.1),
            deriv_smoothTransition_of_neg ((div_neg_iff).2 (Or.inr ⟨by linarith, hτ⟩))]
          simp
      have t2 : ‖(1 - eta a τ y) * ((1 / 2 : ℂ) * eF φ y + eF (psi1 φ) y)‖ * Real.exp (|y| / 2) ≤
          (K / 2 + K₁) * Real.exp y := by
        rw [norm_mul]
        calc ‖1 - eta a τ y‖ * ‖(1 / 2 : ℂ) * eF φ y + eF (psi1 φ) y‖ * Real.exp (|y| / 2)
            ≤ 1 * ((1 / 2) * ‖eF φ y‖ + ‖eF (psi1 φ) y‖) * Real.exp (|y| / 2) := by
              gcongr
              · exact norm_one_sub_eta_le a τ y
              · refine (norm_add_le _ _).trans ?_
                rw [norm_mul]; norm_num
          _ = (1 / 2) * (‖eF φ y‖ * Real.exp (|y| / 2)) + ‖eF (psi1 φ) y‖ * Real.exp (|y| / 2) := by ring
          _ ≤ (1 / 2) * (K * Real.exp y) + K₁ * Real.exp y :=
              add_le_add (mul_le_mul_of_nonneg_left (bφ hy) (by norm_num)) (bψ hy)
          _ = (K / 2 + K₁) * Real.exp y := by ring
      calc _ ≤ (‖-(((deriv Real.smoothTransition ((y + a) / τ) / τ : ℝ)) : ℂ) * eF φ y‖ +
            ‖(1 - eta a τ y) * ((1 / 2 : ℂ) * eF φ y + eF (psi1 φ) y)‖) * Real.exp (|y| / 2) := by
            gcongr; exact norm_add_le _ _
        _ = _ := by ring
        _ ≤ _ := add_le_add t1 t2
    · push_neg at hy
      have e : rF φ a τ =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [Ioi_mem_nhds hy] with w hw using rF_eq_zero_of_ge hτ hw.le
      rw [e.deriv_eq,
        Set.indicator_of_notMem (show y ∉ Icc (-a) y₁ from fun h => not_le.2 hy h.2),
        Set.indicator_of_notMem (show y ∉ Iic y₁ from not_le.2 hy)]
      simp
  have i1 : Integrable (Set.indicator (Icc (-a) y₁) fun _ => c) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  have i2 : Integrable (Set.indicator (Iic y₁) fun y => (K / 2 + K₁) * Real.exp y) :=
    (integrable_indicator_iff measurableSet_Iic).2 ((integrableOn_exp_Iic _).const_mul _)
  unfold TheoremA.wL1
  calc ∫ y, ‖deriv (rF φ a τ) y‖ * Real.exp (|y| / 2)
      ≤ ∫ y, (Set.indicator (Icc (-a) y₁) (fun _ => c) y +
          Set.indicator (Iic y₁) (fun y => (K / 2 + K₁) * Real.exp y) y) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => by positivity) (i1.add i2)
          (Filter.Eventually.of_forall hbound)
    _ = c * τ + (K / 2 + K₁) * Real.exp y₁ := by
        rw [integral_add i1 i2, integral_indicator_const _ measurableSet_Icc,
          integral_indicator measurableSet_Iic, integral_const_mul, integral_exp_Iic]
        simp only [measureReal_def, Real.volume_Icc, smul_eq_mul]
        rw [ENNReal.toReal_ofReal (by simp [y₁]; linarith)]
        simp only [y₁]; ring
    _ = _ := by simp only [c]; field_simp; ring

theorem wL1_nonneg (f : ℝ → ℂ) : 0 ≤ TheoremA.wL1 f :=
  integral_nonneg fun _ => by positivity

/-- **Reduction to tail bounds.** `TheoremA.Inputs` follows from: for each large `λ`, an even real
`φ ∈ C³_c` (support in `[-λ, λ]`, `φ(0) = ∫φ = 0`) whose Fourier transform and that of `x φ'` satisfy
`|·(ξ)| ≤ M/ξ²` on `|ξ| ≥ Ξ` with `M ≤ C λ^q e^{-πλ²}`, and `‖k‖² ≥ c₀`. -/
theorem inputs_of_tails
    (h : ∃ c₀ Cm q lam₀ : ℝ, 0 < c₀ ∧ 0 ≤ Cm ∧ 1 ≤ lam₀ ∧ ∀ lam ≥ lam₀,
      ∃ (φ : ℝ → ℂ) (L τ M M₁ Ξ : ℝ),
      ContDiff ℝ 3 φ ∧ (∀ v, (starRingEnd ℂ) (φ v) = φ v) ∧ (∀ v, φ (-v) = φ v) ∧ φ 0 = 0 ∧
      𝓕 φ 0 = 0 ∧ 0 < L ∧ L ≤ lam ∧ (∀ v, L ≤ |v| → φ v = 0) ∧ 0 < τ ∧ τ ≤ 1 ∧
      -Real.log lam + τ ≤ 0 ∧ 0 ≤ Ξ ∧ Real.exp (-Real.log lam + τ) * Ξ ≤ 1 ∧
      (∀ ξ, Ξ ≤ |ξ| → ‖𝓕 φ ξ‖ ≤ M / ξ ^ 2) ∧ (∀ ξ, Ξ ≤ |ξ| → ‖𝓕 (psi1 φ) ξ‖ ≤ M₁ / ξ ^ 2) ∧
      M ≤ Cm * lam ^ q * Real.exp (-Real.pi * lam ^ 2) ∧
      M₁ ≤ Cm * lam ^ q * Real.exp (-Real.pi * lam ^ 2) ∧
      c₀ ≤ TheoremA.l2sq (kF φ (Real.log lam) τ)) :
    TheoremA.Inputs := by
  obtain ⟨c₀, Cm, q, lam₀, hc₀, hCm, hlam₀, hq⟩ := h
  obtain ⟨D, hD⟩ := exists_bound_deriv_smoothTransition
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  set Z := ∑' m : ℤ, 1 / (m : ℝ) ^ 2
  have hZ : 0 ≤ Z := tsum_nonneg fun _ => by positivity
  set A := Z / 2 * (D + 5 / 2) * Cm * Real.exp 1
  have hA : 0 ≤ A := by positivity
  refine inputs_of_quantitative ⟨c₀, A ^ 2, 2 * q, lam₀, hc₀, by positivity, hlam₀, fun lam hlam => ?_⟩
  obtain ⟨φ, L, τ, M, M₁, Ξ, hφ, hreal, heven, h00, hint, hL0, hLlam, hsupp, hτ, hτ1, hy₁, hΞ,
    hΞy, hFt, hFt1, hM, hM₁, hnorm⟩ := hq lam hlam
  refine ⟨φ, L, τ, hφ, hreal, heven, h00, hint, hL0, hLlam, hsupp, hτ, hnorm, ?_⟩
  have hlam1 : 1 ≤ lam := hlam₀.trans hlam
  have hlampos : 0 < lam := lt_of_lt_of_le one_pos hlam1
  set a := Real.log lam
  have b1 := wL1_rF_le (a := a) (hφ.of_le (by norm_num)) hsupp heven h00 hint hΞ hFt hτ hy₁ hΞy
  have b2 := wL1_deriv_rF_le (a := a) hφ hL0.le hsupp heven h00 hint hΞ hFt hFt1 hτ hy₁ hΞy hD
  set G := Cm * lam ^ q * Real.exp (-Real.pi * lam ^ 2)
  have hG : 0 ≤ G := by positivity
  have hy : Real.exp (-a + τ) ≤ Real.exp 1 := Real.exp_le_exp.2 (by
    have : 0 ≤ a := Real.log_nonneg hlam1
    linarith)
  have hey : 0 < Real.exp (-a + τ) := Real.exp_pos _
  have hsum : TheoremA.wL1 (rF φ a τ) + TheoremA.wL1 (deriv (rF φ a τ)) ≤ A * (lam ^ q * Real.exp (-Real.pi * lam ^ 2)) := by
    have e1 : M * Z / 2 * Real.exp (-a + τ) ≤ Z / 2 * G * Real.exp (-a + τ) := by
      have : M * Z / 2 = Z / 2 * M := by ring
      rw [this]; gcongr
    have e2 : (D * (M * Z / 2) + M * Z / 2 / 2 + M₁ * Z / 2) * Real.exp (-a + τ) ≤
        (D * (Z / 2 * G) + Z / 2 * G / 2 + Z / 2 * G) * Real.exp (-a + τ) := by
      gcongr
      · have : M * Z / 2 = Z / 2 * M := by ring
        rw [this]; gcongr
      · have : M * Z / 2 = Z / 2 * M := by ring
        rw [this]; gcongr
      · have : M₁ * Z / 2 = Z / 2 * M₁ := by ring
        rw [this]; gcongr
    calc TheoremA.wL1 (rF φ a τ) + TheoremA.wL1 (deriv (rF φ a τ))
        ≤ Z / 2 * G * Real.exp (-a + τ) +
          (D * (Z / 2 * G) + Z / 2 * G / 2 + Z / 2 * G) * Real.exp (-a + τ) :=
          add_le_add (b1.trans e1) (b2.trans e2)
      _ = Z / 2 * (D + 5 / 2) * G * Real.exp (-a + τ) := by ring
      _ ≤ Z / 2 * (D + 5 / 2) * G * Real.exp 1 := by gcongr
      _ = A * (lam ^ q * Real.exp (-Real.pi * lam ^ 2)) := by simp only [A, G]; ring
  have h0 : 0 ≤ TheoremA.wL1 (rF φ a τ) + TheoremA.wL1 (deriv (rF φ a τ)) :=
    add_nonneg (wL1_nonneg _) (wL1_nonneg _)
  calc (TheoremA.wL1 (rF φ a τ) + TheoremA.wL1 (deriv (rF φ a τ))) ^ 2
      ≤ (A * (lam ^ q * Real.exp (-Real.pi * lam ^ 2))) ^ 2 := pow_le_pow_left₀ h0 hsum 2
    _ = A ^ 2 * lam ^ (2 * q) * Real.exp (-2 * Real.pi * lam ^ 2) := by
        have e1 : (lam ^ q) ^ 2 = lam ^ (2 * q) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hlampos.le]; ring_nf
        have e2 : (Real.exp (-Real.pi * lam ^ 2)) ^ 2 = Real.exp (-2 * Real.pi * lam ^ 2) := by
          rw [← Real.exp_nat_mul]; ring_nf
        simp only [mul_pow]; rw [e1, e2]; ring

end Construction
end RhWeil
