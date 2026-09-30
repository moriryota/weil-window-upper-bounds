import Zeta23.Defs
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Bound for `r̂` on the critical strip (Proposition 3.1 of the paper draft, analytic part)

For a `C¹` function `r` with `∫ ‖r‖ e^{|y|/2} ≤ A₀` and `∫ ‖r'‖ e^{|y|/2} ≤ A₁`,
`‖r̂ z‖² ≤ 2 (A₀ + A₁)² / (1 + |z|²)` for `|Im z| ≤ 1/2`.
-/

noncomputable section

namespace RhWeil

open Complex MeasureTheory Zeta23

theorem norm_cexp_I_mul_le {z : ℂ} (hz : |z.im| ≤ 1 / 2) (y : ℝ) :
    ‖Complex.exp (I * z * (y : ℂ))‖ ≤ Real.exp (|y| / 2) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  have : (I * z * (y : ℂ)).re = -(z.im * y) := by simp [Complex.mul_re]
  rw [this]
  calc -(z.im * y) ≤ |z.im * y| := neg_le_abs _
    _ = |z.im| * |y| := abs_mul _ _
    _ ≤ 1 / 2 * |y| := by gcongr
    _ = |y| / 2 := by ring

theorem integrable_mul_cexp {r : ℝ → ℂ} (hr : Continuous r)
    (hint : Integrable (fun y => ‖r y‖ * Real.exp (|y| / 2))) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    Integrable (fun y : ℝ => r y * Complex.exp (I * z * (y : ℂ))) := by
  refine hint.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact (hr.mul (by fun_prop)).aestronglyMeasurable
  · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_cexp_I_mul_le hz y) (norm_nonneg _)

/-- `‖r̂ z‖ ≤ ∫ ‖r‖ e^{|y|/2}` on the strip. -/
theorem norm_paperFT_le {r : ℝ → ℂ} (hr : Continuous r)
    (hint : Integrable (fun y => ‖r y‖ * Real.exp (|y| / 2))) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT r z‖ ≤ ∫ y, ‖r y‖ * Real.exp (|y| / 2) := by
  unfold paperFT
  refine (norm_integral_le_integral_norm _).trans ?_
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hint
    (Filter.Eventually.of_forall fun y => ?_)
  simp only [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_cexp_I_mul_le hz y) (norm_nonneg _)

/-- Integration by parts: `z · r̂(z) = I · (r')^(z)` on the strip. -/
theorem mul_paperFT_eq {r r' : ℝ → ℂ} (hd : ∀ y, HasDerivAt r (r' y) y) (hr' : Continuous r')
    (hint : Integrable (fun y => ‖r y‖ * Real.exp (|y| / 2)))
    (hint' : Integrable (fun y => ‖r' y‖ * Real.exp (|y| / 2))) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    z * paperFT r z = I * paperFT r' z := by
  have hr : Continuous r := continuous_iff_continuousAt.2 fun y => (hd y).continuousAt
  set v : ℝ → ℂ := fun y => Complex.exp (I * z * (y : ℂ))
  have hv : ∀ y : ℝ, HasDerivAt v (I * z * v y) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => I * z * (y : ℂ)) (I * z) y := by
      simpa using ((hasDerivAt_id (y : ℝ)).ofReal_comp).const_mul (I * z)
    simpa [v, mul_comm] using h1.cexp
  have i1 := integrable_mul_cexp hr hint hz
  have i2 := integrable_mul_cexp hr' hint' hz
  have i3 : Integrable (r * fun y => I * z * v y) := by
    have := i1.const_mul (I * z)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp [v]; ring
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := r) (v := v) (u' := r')
    (v' := fun y => I * z * v y) (fun y _ => hd y) (fun y _ => hv y) i3 i2 i1
  have e1 : ∫ y, r y * (I * z * v y) = I * z * paperFT r z := by
    unfold paperFT; rw [← integral_const_mul]; congr 1; ext y; simp [v]; ring
  have e2 : ∫ y, r' y * v y = paperFT r' z := rfl
  rw [e1, e2] at key
  have hI : I * I = -1 := I_mul_I
  calc z * paperFT r z = -I * (I * z * paperFT r z) := by ring_nf; rw [I_sq]; ring
    _ = -I * -paperFT r' z := by rw [key]
    _ = I * paperFT r' z := by ring

theorem sq_le_of_min {x A₀ A₁ u : ℝ} (hx : 0 ≤ x) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hu : 0 ≤ u)
    (h0 : x ≤ A₀) (h1 : u * x ≤ A₁) : x ^ 2 ≤ 2 * (A₀ + A₁) ^ 2 / (1 + u ^ 2) := by
  have hpos : 0 < 1 + u ^ 2 := by positivity
  rw [le_div_iff₀ hpos]
  rcases le_total u 1 with hu1 | hu1
  · have : x ^ 2 ≤ (A₀ + A₁) ^ 2 := pow_le_pow_left₀ hx (by linarith) 2
    nlinarith [sq_nonneg u, mul_le_mul_of_nonneg_left hu1 hu]
  · have hux : (u * x) ^ 2 ≤ (A₀ + A₁) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) (sub_nonneg.2 hu1)]

/-- **Bound for `r̂`** (hypothesis `hr` of `ZeroSumBound.norm_zeroSide_le`). -/
theorem norm_paperFT_sq_le {r r' : ℝ → ℂ} (hd : ∀ y, HasDerivAt r (r' y) y) (hr' : Continuous r')
    (hint : Integrable (fun y => ‖r y‖ * Real.exp (|y| / 2)))
    (hint' : Integrable (fun y => ‖r' y‖ * Real.exp (|y| / 2))) {A₀ A₁ : ℝ}
    (hA₀ : ∫ y, ‖r y‖ * Real.exp (|y| / 2) ≤ A₀) (hA₁ : ∫ y, ‖r' y‖ * Real.exp (|y| / 2) ≤ A₁)
    {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT r z‖ ^ 2 ≤ 2 * (A₀ + A₁) ^ 2 / (1 + normSq z) := by
  have hr : Continuous r := continuous_iff_continuousAt.2 fun y => (hd y).continuousAt
  have b0 := (norm_paperFT_le hr hint hz).trans hA₀
  have b1 : ‖z‖ * ‖paperFT r z‖ ≤ A₁ := by
    rw [← norm_mul, mul_paperFT_eq hd hr' hint hint' hz, norm_mul, norm_I, one_mul]
    exact (norm_paperFT_le hr' hint' hz).trans hA₁
  have hA₀' : 0 ≤ A₀ := (norm_nonneg _).trans b0
  have hA₁' : 0 ≤ A₁ := (integral_nonneg fun _ => by positivity).trans hA₁
  have := sq_le_of_min (norm_nonneg _) hA₀' hA₁' (norm_nonneg z) b0 b1
  rw [Complex.normSq_eq_norm_sq]; exact this

end RhWeil
