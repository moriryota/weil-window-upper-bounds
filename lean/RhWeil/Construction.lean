import RhWeil.RadicalC2
import RhWeil.TheoremA

/-!
# The functions `e = ℰφ ∘ exp`, `k = e η`, `r = e (1 - η)` (paper draft §2, Lean version)

Part 1: `e` is a locally finite sum, hence `C^n` when `φ` is.
-/

noncomputable section

namespace RhWeil
namespace Construction

open Complex MeasureTheory Set Filter Topology Real

variable {φ : ℝ → ℂ} {L : ℝ}

/-- `e(y) = e^{y/2} Σ_{n≥1} φ(n e^y)`. -/
def eF (φ : ℝ → ℂ) (y : ℝ) : ℂ := (Real.exp (y / 2) : ℂ) * ∑' n : ℕ, φ (((n : ℝ) + 1) * Real.exp y)

theorem eF_eq_Esum (φ : ℝ → ℂ) (y : ℝ) : eF φ y = Radical.Esum φ (Real.exp y) := by
  unfold eF Radical.Esum
  rw [Radical.ofReal_exp_cpow, Complex.ofReal_exp]
  congr 2; push_cast; ring

/-- Near any `y₀`, only the terms `n < N` of `e` are non-zero, for every `N ≥ ⌈L e^{1-y₀}⌉`. -/
theorem eF_eventuallyEq_finite (hL : 0 ≤ L) (hsupp : ∀ v, L ≤ |v| → φ v = 0) (y₀ : ℝ) {N : ℕ}
    (hNge : Nat.ceil (L * Real.exp (1 - y₀)) ≤ N) :
    ∀ᶠ y in 𝓝 y₀, eF φ y =
      (Real.exp (y / 2) : ℂ) * ∑ n ∈ Finset.range N, φ (((n : ℝ) + 1) * Real.exp y) := by
  filter_upwards [Ioi_mem_nhds (show y₀ - 1 < y₀ by linarith)] with y hy
  unfold eF
  congr 1
  refine tsum_eq_sum fun n hn => hsupp _ ?_
  simp only [Finset.mem_range, not_lt] at hn
  have hN : L * Real.exp (1 - y₀) ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast hNge.trans hn)
  have hy' : (y₀ - 1 : ℝ) < y := hy
  have h1 : Real.exp (1 - y₀) * Real.exp y ≥ 1 := by
    rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
  rw [abs_of_nonneg (by positivity)]
  calc L ≤ L * (Real.exp (1 - y₀) * Real.exp y) := le_mul_of_one_le_right hL h1
    _ = (L * Real.exp (1 - y₀)) * Real.exp y := by ring
    _ ≤ n * Real.exp y := by gcongr
    _ ≤ ((n : ℝ) + 1) * Real.exp y := by gcongr; linarith

theorem contDiff_eF {m : ℕ∞} (hφ : ContDiff ℝ m φ) (hL : 0 ≤ L) (hsupp : ∀ v, L ≤ |v| → φ v = 0) :
    ContDiff ℝ m (eF φ) := by
  refine contDiff_iff_contDiffAt.2 fun y₀ => ?_
  have hN := eF_eventuallyEq_finite hL hsupp y₀ le_rfl
  refine (ContDiffAt.congr_of_eventuallyEq ?_ hN)
  refine ContDiff.contDiffAt ?_
  refine (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_id.div_const 2))).mul ?_
  refine ContDiff.sum fun n _ => hφ.comp ?_
  exact contDiff_const.mul Real.contDiff_exp

/-! ### Part 2: decay of `e` and the derivative formula -/

open scoped FourierTransform

theorem eF_eq_mul_Fsum (φ : ℝ → ℂ) (y : ℝ) :
    eF φ y = (Real.exp (y / 2) : ℂ) * Radical.Fsum φ (Real.exp y) := rfl

/-- `‖e(y)‖ ≤ K e^{3y/2}` for all `y`, with `K = ‖φ''‖₁/(4π²) · Σ_{m∈ℤ} m⁻² / 2`. -/
theorem norm_eF_le {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ v, L ≤ |v| → φ v = 0)
    (heven : ∀ v, φ (-v) = φ v) (h00 : φ 0 = 0) (hint : 𝓕 φ 0 = 0) (y : ℝ) :
    ‖eF φ y‖ ≤ ((∫ x, ‖iteratedDeriv 2 φ x‖) / (4 * π ^ 2) * (∑' m : ℤ, 1 / (m : ℝ) ^ 2) / 2)
      * Real.exp (3 / 2 * y) := by
  have hs : HasCompactSupport φ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0:ℝ) L) fun v hv => hsupp v ?_
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hv
    exact hv.le
  have hb := Radical.bound_Fsum hφ.continuous hsupp heven h00
    (norm_fourier_le_of_contDiff_two hφ hs hint) (Real.exp_pos y)
  rw [eF_eq_mul_Fsum, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc Real.exp (y / 2) * ‖Radical.Fsum φ (Real.exp y)‖
      ≤ Real.exp (y / 2) * (_ * Real.exp y) := by gcongr
    _ = _ := by
        rw [mul_comm (Real.exp (y / 2)), mul_assoc, ← Real.exp_add]; congr 2; ring

/-- `ψ₁(x) = x φ'(x)`. -/
def psi1 (φ : ℝ → ℂ) (x : ℝ) : ℂ := (x : ℂ) * deriv φ x

theorem psi1_supp {φ : ℝ → ℂ} (hsupp : ∀ v, L ≤ |v| → φ v = 0) :
    ∀ v, L + 1 ≤ |v| → psi1 φ v = 0 := by
  intro v hv
  have : φ =ᶠ[𝓝 v] fun _ => 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds
      (show L < |v| by linarith)] with w hw using hsupp w hw.le
  simp [psi1, this.deriv_eq]

theorem hasDerivAt_eF {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) (hL : 0 ≤ L)
    (hsupp : ∀ v, L ≤ |v| → φ v = 0) (y₀ : ℝ) :
    HasDerivAt (eF φ) ((1 / 2 : ℂ) * eF φ y₀ + eF (psi1 φ) y₀) y₀ := by
  have hL1 : 0 ≤ L + 1 := by linarith
  have hsupp' : ∀ v, L + 1 ≤ |v| → φ v = 0 := fun v hv => hsupp v (by linarith)
  set N := Nat.ceil ((L + 1) * Real.exp (1 - y₀))
  have hN := eF_eventuallyEq_finite hL1 hsupp' y₀ le_rfl
  have hN' := eF_eventuallyEq_finite hL1 (psi1_supp hsupp) y₀ le_rfl
  set F : ℝ → ℂ := fun y =>
    (Real.exp (y / 2) : ℂ) * ∑ n ∈ Finset.range N, φ (((n : ℝ) + 1) * Real.exp y)
  have hd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hexp : HasDerivAt (fun y : ℝ => (Real.exp (y / 2) : ℂ)) ((Real.exp (y₀ / 2) : ℂ) * (1 / 2)) y₀ := by
    have := ((Real.hasDerivAt_exp (y₀ / 2)).comp y₀ ((hasDerivAt_id y₀).div_const 2)).ofReal_comp
    simpa using this
  have hterm : ∀ n : ℕ, HasDerivAt (fun y : ℝ => φ (((n : ℝ) + 1) * Real.exp y))
      (psi1 φ (((n : ℝ) + 1) * Real.exp y₀)) y₀ := by
    intro n
    have hg : HasDerivAt (fun y : ℝ => ((n : ℝ) + 1) * Real.exp y) (((n : ℝ) + 1) * Real.exp y₀) y₀ :=
      (Real.hasDerivAt_exp y₀).const_mul _
    have := (hd _).hasDerivAt.scomp y₀ hg
    simpa [psi1, Function.comp_def, smul_eq_mul, mul_comm] using this
  have hF : HasDerivAt F ((Real.exp (y₀ / 2) : ℂ) * (1 / 2) *
      ∑ n ∈ Finset.range N, φ (((n : ℝ) + 1) * Real.exp y₀) +
      (Real.exp (y₀ / 2) : ℂ) * ∑ n ∈ Finset.range N, psi1 φ (((n : ℝ) + 1) * Real.exp y₀)) y₀ :=
    hexp.mul (HasDerivAt.fun_sum fun n _ => hterm n)
  refine (hF.congr_of_eventuallyEq hN).congr_deriv ?_
  rw [hN.self_of_nhds, hN'.self_of_nhds]; ring

/-! ### Part 3: `ψ₁ = x φ'` inherits the hypotheses (for `φ ∈ C³`), hence `e'` decays -/

theorem fourier_zero_eq_integral (f : ℝ → ℂ) : 𝓕 f 0 = ∫ x, f x := by
  rw [Real.fourier_real_eq]; simp

theorem contDiff_psi1 {φ : ℝ → ℂ} (hφ : ContDiff ℝ 3 φ) : ContDiff ℝ 2 (psi1 φ) := by
  have h : ContDiff ℝ 2 (deriv φ) := by simpa using hφ.iterate_deriv' 2 1
  exact (Complex.ofRealCLM.contDiff.comp contDiff_id).mul h

theorem deriv_odd {φ : ℝ → ℂ} (hd : Differentiable ℝ φ) (heven : ∀ v, φ (-v) = φ v) (v : ℝ) :
    deriv φ (-v) = -deriv φ v := by
  have h1 : deriv (fun w => φ (-w)) v = -deriv φ (-v) := by
    simpa using deriv_comp_neg (f := φ) (x := v)
  have h2 : deriv (fun w => φ (-w)) v = deriv φ v := by
    rw [show (fun w => φ (-w)) = φ from funext heven]
  have h3 := h2.symm.trans h1
  linear_combination h3

theorem psi1_even {φ : ℝ → ℂ} (hd : Differentiable ℝ φ) (heven : ∀ v, φ (-v) = φ v) (v : ℝ) :
    psi1 φ (-v) = psi1 φ v := by
  simp only [psi1, deriv_odd hd heven v]; push_cast; ring

theorem fourier_psi1_zero {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ)
    (hint : 𝓕 φ 0 = 0) : 𝓕 (psi1 φ) 0 = 0 := by
  rw [fourier_zero_eq_integral] at hint ⊢
  have hd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hcd : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hsd : HasCompactSupport (deriv φ) := hs.deriv
  have i1 : Integrable ((fun x : ℝ => (x : ℂ)) * deriv φ) :=
    ((continuous_ofReal.mul hcd)).integrable_of_hasCompactSupport (μ := volume) (hsd.mul_left)
  have i2 : Integrable ((fun _ : ℝ => (1 : ℂ)) * φ) := by
    have h := hφ.continuous.integrable_of_hasCompactSupport (μ := volume) hs
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp
  have i3 : Integrable ((fun x : ℝ => (x : ℂ)) * φ) :=
    ((continuous_ofReal.mul hφ.continuous)).integrable_of_hasCompactSupport (μ := volume) (hs.mul_left)
  have := integral_mul_deriv_eq_deriv_mul_of_integrable (u := fun x : ℝ => (x : ℂ)) (v := φ)
    (u' := fun _ => 1) (v' := deriv φ)
    (fun x _ => by simpa using (hasDerivAt_id x).ofReal_comp) (fun x _ => (hd x).hasDerivAt) i1 i2 i3
  simp only [one_mul] at this
  unfold psi1
  rw [this, hint, neg_zero]

/-- `‖e'(y)‖ ≤ K' e^{3y/2}` for all `y`, for `φ ∈ C³` even, compactly supported, `φ(0) = ∫φ = 0`. -/
theorem norm_deriv_eF_le {φ : ℝ → ℂ} (hφ : ContDiff ℝ 3 φ) (hL : 0 ≤ L)
    (hsupp : ∀ v, L ≤ |v| → φ v = 0) (heven : ∀ v, φ (-v) = φ v) (h00 : φ 0 = 0)
    (hint : 𝓕 φ 0 = 0) :
    ∃ K, ∀ y, ‖deriv (eF φ) y‖ ≤ K * Real.exp (3 / 2 * y) := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_num)
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hd : Differentiable ℝ φ := hφ1.differentiable one_ne_zero
  have hs : HasCompactSupport φ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0:ℝ) L) fun v hv => hsupp v ?_
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hv
    exact hv.le
  obtain ⟨K0, b0⟩ : ∃ K0, ∀ y, ‖eF φ y‖ ≤ K0 * Real.exp (3 / 2 * y) :=
    ⟨_, norm_eF_le hφ2 hsupp heven h00 hint⟩
  obtain ⟨K1, b1⟩ : ∃ K1, ∀ y, ‖eF (psi1 φ) y‖ ≤ K1 * Real.exp (3 / 2 * y) :=
    ⟨_, norm_eF_le (contDiff_psi1 hφ) (psi1_supp hsupp) (psi1_even hd heven) (by simp [psi1])
      (fourier_psi1_zero hφ1 hs hint)⟩
  refine ⟨1 / 2 * K0 + K1, fun y => ?_⟩
  rw [(hasDerivAt_eF hφ1 hL hsupp y).deriv]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have e1 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [e1]
  have := add_le_add (mul_le_mul_of_nonneg_left (b0 y) (by norm_num : (0:ℝ) ≤ 1 / 2)) (b1 y)
  refine this.trans (le_of_eq ?_)
  ring

/-! ### Part 4: weighted integrability from exponential decay -/

theorem integrable_weighted_of_bound {g : ℝ → ℂ} (hg : Continuous g) {K T : ℝ} (hT : 0 ≤ T)
    (hb : ∀ y, ‖g y‖ ≤ K * Real.exp (3 / 2 * y)) (hz : ∀ y, T ≤ y → g y = 0) :
    Integrable (fun y => ‖g y‖ * Real.exp (|y| / 2)) := by
  have hK : 0 ≤ K := by
    have := (norm_nonneg _).trans (hb 0); simpa using this
  have hint : Integrable (Set.indicator (Iic T) fun y => K * Real.exp T * Real.exp y) :=
    (integrable_indicator_iff measurableSet_Iic).2 ((integrableOn_exp_Iic T).const_mul _)
  refine hint.mono' ((hg.norm.mul (Real.continuous_exp.comp
    (continuous_abs.div_const 2))).aestronglyMeasurable) (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  by_cases hy : y ≤ T
  · rw [Set.indicator_of_mem (show y ∈ Iic T from hy)]
    calc ‖g y‖ * Real.exp (|y| / 2) ≤ K * Real.exp (3 / 2 * y) * Real.exp (|y| / 2) := by
          gcongr; exact hb y
      _ = K * Real.exp (3 / 2 * y + |y| / 2) := by rw [mul_assoc, ← Real.exp_add]
      _ ≤ K * Real.exp (T + y) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK
          rcases le_total y 0 with h | h
          · rw [abs_of_nonpos h]; linarith
          · rw [abs_of_nonneg h]; linarith
      _ = K * Real.exp T * Real.exp y := by rw [Real.exp_add]; ring
  · push_neg at hy
    rw [hz y hy.le, norm_zero, zero_mul, Set.indicator_of_notMem (show y ∉ Iic T from not_le.2 hy)]

end Construction
end RhWeil
