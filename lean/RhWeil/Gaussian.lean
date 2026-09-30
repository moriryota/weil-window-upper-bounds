import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Fourier transforms of `xⁿ e^{-πx²}`

`G(x) = e^{-πx²}` is its own Fourier transform. Its derivatives are `Pₙ(x) G(x)` with
`P₀ = 1`, `Pₙ₊₁ = Pₙ' - 2π X Pₙ`, and `𝓕(xⁿ G) = (-2πi)⁻ⁿ Pₙ G`, so
`|𝓕(xⁿ G)(ξ)| ≤ (2π)⁻ⁿ Sₙ (1+|ξ|)^{deg Pₙ} e^{-πξ²}`.
-/

noncomputable section

namespace RhWeil
namespace Gaussian

open Complex MeasureTheory Real Polynomial
open scoped FourierTransform

/-- The Gaussian `e^{-πx²}` (complex-valued). -/
def G (x : ℝ) : ℂ := (Real.exp (-π * x ^ 2) : ℂ)

theorem G_eq : G = fun x : ℝ => cexp (-π * (1 : ℂ) * (x : ℂ) ^ 2) := by
  funext x; simp [G, Complex.ofReal_exp]

theorem fourier_G : 𝓕 G = G := by
  rw [G_eq, fourier_gaussian_pi (by simp : (0:ℝ) < (1:ℂ).re)]
  funext t; simp

/-- `P₀ = 1`, `Pₙ₊₁ = Pₙ' - 2π X Pₙ`. -/
def P : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => derivative (P n) - C (2 * π) * X * P n

/-- `Qₙ(x) = Pₙ(x) e^{-πx²}`. -/
def Q (n : ℕ) (x : ℝ) : ℝ := (P n).eval x * Real.exp (-π * x ^ 2)

theorem hasDerivAt_Q (n : ℕ) (x : ℝ) : HasDerivAt (Q n) (Q (n + 1) x) x := by
  have h1 : HasDerivAt (fun x => Real.exp (-π * x ^ 2)) (Real.exp (-π * x ^ 2) * (-π * (2 * x))) x := by
    have := ((hasDerivAt_pow 2 x).const_mul (-π)).exp
    simpa [mul_comm] using this
  have h2 := (Polynomial.hasDerivAt (P n) x).mul h1
  have e : Q (n + 1) x = eval x (derivative (P n)) * Real.exp (-π * x ^ 2) +
      eval x (P n) * (Real.exp (-π * x ^ 2) * (-π * (2 * x))) := by
    show eval x (derivative (P n) - C (2 * π) * X * P n) * _ = _
    rw [eval_sub, eval_mul, eval_mul, eval_C, eval_X]; ring
  rw [e]; exact h2

theorem iteratedDeriv_G (n : ℕ) : iteratedDeriv n G = fun x => (Q n x : ℂ) := by
  induction n with
  | zero => funext x; simp [G, Q, P]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact ((hasDerivAt_Q n x).ofReal_comp).deriv

theorem integrable_pow_mul_G (n : ℕ) : Integrable (fun x : ℝ => (x : ℂ) ^ n * G x) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := π) pi_pos (s := (n : ℝ)) (by linarith [n.cast_nonneg (α := ℝ)])
  have h' : Integrable (fun x : ℝ => ((x ^ n * Real.exp (-π * x ^ 2) : ℝ) : ℂ)) := by
    refine h.ofReal.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [Real.rpow_natCast]
  refine h'.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [G]

/-- `𝓕(xⁿ G) = (-2πi)⁻ⁿ Qₙ`. -/
theorem fourier_pow_mul_G (n : ℕ) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (x : ℂ) ^ n * G x) ξ = (-2 * π * I) ^ (-(n : ℤ)) * (Q n ξ : ℂ) := by
  have hint : ∀ m : ℕ, (m : ℕ∞) ≤ (n : ℕ∞) → Integrable (fun x : ℝ => x ^ m • G x) := by
    intro m _
    refine (integrable_pow_mul_G m).congr (Filter.Eventually.of_forall fun x => ?_)
    simp [Complex.real_smul]
  have key := congrFun (iteratedDeriv_fourier (N := (n : ℕ∞)) (n := n) hint le_rfl) ξ
  rw [fourier_G, iteratedDeriv_G] at key
  have hne : (-2 * π * I : ℂ) ≠ 0 := by
    simp [pi_ne_zero, I_ne_zero]
  have e : (fun x : ℝ => (-2 * π * I * x) ^ n • G x) = fun x : ℝ => (-2 * π * I) ^ n * ((x : ℂ) ^ n * G x) := by
    funext x; rw [smul_eq_mul, mul_pow]; ring
  rw [e] at key
  have lin : 𝓕 (fun x : ℝ => (-2 * π * I) ^ n * ((x : ℂ) ^ n * G x)) ξ =
      (-2 * π * I) ^ n * 𝓕 (fun x : ℝ => (x : ℂ) ^ n * G x) ξ := by
    rw [Real.fourier_real_eq, Real.fourier_real_eq, ← integral_const_mul]
    congr 1; ext v; rw [Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul]; ring
  rw [lin] at key
  simp only at key
  rw [zpow_neg, zpow_natCast, key]
  field_simp

/-- Polynomial bound `|p(x)| ≤ S(p) (1+|x|)^{deg p}`. -/
def coeffSum (p : ℝ[X]) : ℝ := ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|

theorem abs_eval_le (p : ℝ[X]) (x : ℝ) : |p.eval x| ≤ coeffSum p * (1 + |x|) ^ p.natDegree := by
  rw [eval_eq_sum_range, coeffSum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [abs_mul, abs_pow]
  gcongr
  calc |x| ^ i ≤ (1 + |x|) ^ i := by gcongr; linarith [abs_nonneg x]
    _ ≤ (1 + |x|) ^ p.natDegree := by
        apply pow_le_pow_right₀ (by linarith [abs_nonneg x])
        simpa [Nat.lt_succ_iff] using Finset.mem_range.1 hi

/-- **Bound:** `|𝓕(xⁿ G)(ξ)| ≤ (2π)⁻ⁿ Sₙ (1+|ξ|)^{dₙ} e^{-πξ²}`. -/
theorem norm_fourier_pow_mul_G_le (n : ℕ) (ξ : ℝ) :
    ‖𝓕 (fun x : ℝ => (x : ℂ) ^ n * G x) ξ‖ ≤
      (2 * π)⁻¹ ^ n * coeffSum (P n) * (1 + |ξ|) ^ (P n).natDegree * Real.exp (-π * ξ ^ 2) := by
  rw [fourier_pow_mul_G, norm_mul, norm_zpow, Complex.norm_real, Real.norm_eq_abs, Q, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  have hn : ‖(-2 * π * I : ℂ)‖ = 2 * π := by
    simp [abs_of_pos pi_pos]
  rw [hn, zpow_neg, zpow_natCast, ← inv_pow]
  have := abs_eval_le (P n) ξ
  have h0 : 0 ≤ (2 * π)⁻¹ ^ n := by positivity
  calc (2 * π)⁻¹ ^ n * (|(P n).eval ξ| * Real.exp (-π * ξ ^ 2))
      ≤ (2 * π)⁻¹ ^ n * (coeffSum (P n) * (1 + |ξ|) ^ (P n).natDegree * Real.exp (-π * ξ ^ 2)) := by
        gcongr
    _ = _ := by ring

end Gaussian
end RhWeil
