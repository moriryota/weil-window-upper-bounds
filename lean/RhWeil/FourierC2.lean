import RhWeil.FourierDecay
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Fourier decay without compact support; `iteratedDeriv` of real functions viewed in `ℂ`
-/

noncomputable section

namespace RhWeil

open Complex MeasureTheory Real
open scoped FourierTransform

/-- `|𝓕f(ξ)| ≤ ‖f''‖₁ / (4π² ξ²)` for `ξ ≠ 0`, `f ∈ C²` with `f, f', f''` integrable. -/
theorem norm_fourier_le_of_integrable {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hi : ∀ n : ℕ, (n : ℕ∞) ≤ (2 : ℕ∞) → Integrable (iteratedDeriv n f)) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖𝓕 f ξ‖ ≤ (∫ x, ‖iteratedDeriv 2 f x‖) / (4 * π ^ 2) / ξ ^ 2 := by
  have key := congrFun (fourier_iteratedDeriv (N := (2 : ℕ∞)) (n := 2) (by exact_mod_cast hf) hi le_rfl) ξ
  have hnorm : ‖((2 * π * I * ξ) ^ 2 : ℂ)‖ = 4 * π ^ 2 * ξ ^ 2 := by
    rw [norm_pow, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, norm_I, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos pi_pos]
    ring_nf; rw [sq_abs]
  have h1 : 4 * π ^ 2 * ξ ^ 2 * ‖𝓕 f ξ‖ ≤ ∫ x, ‖iteratedDeriv 2 f x‖ := by
    rw [← hnorm, ← norm_mul, ← smul_eq_mul, ← key]
    exact norm_fourier_le_integral _ ξ
  rw [div_div, le_div_iff₀ (by positivity)]
  linarith

/-- `iteratedDeriv` commutes with `ℝ → ℂ`. -/
theorem iteratedDeriv_ofReal {f : ℝ → ℝ} (hf : ∀ n : ℕ, ContDiff ℝ n f) (n : ℕ) :
    iteratedDeriv n (fun x => (f x : ℂ)) = fun x => ((iteratedDeriv n f x : ℝ) : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have hd : Differentiable ℝ (iteratedDeriv n f) := (hf (n + 1)).differentiable_iteratedDeriv' n
    rw [((hd x).hasDerivAt.ofReal_comp).deriv, iteratedDeriv_succ]

end RhWeil
