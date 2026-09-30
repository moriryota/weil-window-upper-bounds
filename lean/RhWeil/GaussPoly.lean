import RhWeil.Gaussian
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Polynomial × Gaussian: derivatives, pointwise and tail bounds

`F_R(x) = R(x) e^{-πx²}`. Then `F_R' = F_{D R}` with `D R = R' - 2π X R`, and
`|F_R(x)| ≤ S(R) (1+|x|)^{deg R} e^{-πx²}`. Tail lemma: for `1 ≤ b ≤ x`,
`(1+x)^d e^{-πx²} ≤ d! e (1+b)^d e^{-πb²} e^{-(x-b)}`.
-/

noncomputable section

namespace RhWeil
namespace GaussPoly

open Real Polynomial MeasureTheory Set
open Gaussian (coeffSum abs_eval_le)

/-- `D R = R' - 2π X R`. -/
def D (R : ℝ[X]) : ℝ[X] := derivative R - C (2 * π) * X * R

/-- `F_R(x) = R(x) e^{-πx²}`. -/
def F (R : ℝ[X]) (x : ℝ) : ℝ := R.eval x * Real.exp (-π * x ^ 2)

theorem hasDerivAt_F (R : ℝ[X]) (x : ℝ) : HasDerivAt (F R) (F (D R) x) x := by
  have h1 : HasDerivAt (fun x => Real.exp (-π * x ^ 2)) (Real.exp (-π * x ^ 2) * (-π * (2 * x))) x := by
    have := ((hasDerivAt_pow 2 x).const_mul (-π)).exp
    simpa [mul_comm] using this
  have h2 := (Polynomial.hasDerivAt R x).mul h1
  have e : F (D R) x = eval x (derivative R) * Real.exp (-π * x ^ 2) +
      eval x R * (Real.exp (-π * x ^ 2) * (-π * (2 * x))) := by
    show eval x (derivative R - C (2 * π) * X * R) * _ = _
    rw [eval_sub, eval_mul, eval_mul, eval_C, eval_X]; ring
  rw [e]; exact h2

theorem deriv_F (R : ℝ[X]) : deriv (F R) = F (D R) := funext fun x => (hasDerivAt_F R x).deriv

theorem iteratedDeriv_F (R : ℝ[X]) (n : ℕ) : iteratedDeriv n (F R) = F (D^[n] R) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, deriv_F, Function.iterate_succ_apply']

theorem contDiff_eval (R : ℝ[X]) {m : ℕ∞} : ContDiff ℝ m (fun x : ℝ => R.eval x) := by
  simpa using Polynomial.contDiff_aeval (𝕜 := ℝ) R m

theorem contDiff_F (R : ℝ[X]) {m : ℕ∞} : ContDiff ℝ m (F R) :=
  (contDiff_eval R).mul (Real.contDiff_exp.comp (contDiff_const.mul (contDiff_id.pow 2)))

theorem abs_F_le (R : ℝ[X]) (x : ℝ) :
    |F R x| ≤ coeffSum R * (1 + |x|) ^ R.natDegree * Real.exp (-π * x ^ 2) := by
  rw [F, abs_mul, abs_of_pos (Real.exp_pos _)]
  gcongr
  exact abs_eval_le R x

/-- **Tail lemma.** For `1 ≤ b ≤ x`: `(1+x)^d e^{-πx²} ≤ d! e (1+b)^d e^{-πb²} e^{-(x-b)}`. -/
theorem tail_pointwise (d : ℕ) {b x : ℝ} (hb : 1 ≤ b) (hx : b ≤ x) :
    (1 + x) ^ d * Real.exp (-π * x ^ 2) ≤
      d.factorial * Real.exp 1 * (1 + b) ^ d * Real.exp (-π * b ^ 2) * Real.exp (-(x - b)) := by
  set t := x - b with ht
  have ht0 : 0 ≤ t := by linarith
  have h1 : (1 + x) ^ d ≤ (1 + b) ^ d * (1 + t) ^ d := by
    rw [← mul_pow]
    have e : (1 + b) * (1 + t) = 1 + x + b * t := by rw [ht]; ring
    gcongr
    · linarith
    · rw [e]; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ b) ht0]
  have h2 : (1 + t) ^ d ≤ d.factorial * Real.exp (1 + t) := by
    have := Real.pow_div_factorial_le_exp (1 + t) (by linarith) d
    rw [div_le_iff₀ (by positivity)] at this; linarith
  have h3 : Real.exp (-π * x ^ 2) ≤ Real.exp (-π * b ^ 2) * Real.exp (-2 * π * t) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2
    have : x ^ 2 - b ^ 2 ≥ 2 * t := by nlinarith
    nlinarith [pi_pos]
  have h4 : Real.exp (1 + t) * Real.exp (-2 * π * t) ≤ Real.exp 1 * Real.exp (-t) := by
    rw [← Real.exp_add, ← Real.exp_add]; apply Real.exp_le_exp.2
    nlinarith [Real.pi_gt_three]
  calc (1 + x) ^ d * Real.exp (-π * x ^ 2)
      ≤ ((1 + b) ^ d * (d.factorial * Real.exp (1 + t))) * (Real.exp (-π * b ^ 2) * Real.exp (-2 * π * t)) := by
        gcongr; exact h1.trans (by gcongr)
    _ = d.factorial * (1 + b) ^ d * Real.exp (-π * b ^ 2) * (Real.exp (1 + t) * Real.exp (-2 * π * t)) := by ring
    _ ≤ d.factorial * (1 + b) ^ d * Real.exp (-π * b ^ 2) * (Real.exp 1 * Real.exp (-t)) := by gcongr
    _ = _ := by ring

/-- Sup form: for `|ξ| ≥ Ξ ≥ 1`, `(1+|ξ|)^d e^{-πξ²} ≤ d! e (1+Ξ)^d e^{-πΞ²}`. -/
theorem sup_tail (d : ℕ) {Ξ ξ : ℝ} (hΞ : 1 ≤ Ξ) (hξ : Ξ ≤ |ξ|) :
    (1 + |ξ|) ^ d * Real.exp (-π * ξ ^ 2) ≤ d.factorial * Real.exp 1 * (1 + Ξ) ^ d * Real.exp (-π * Ξ ^ 2) := by
  have := tail_pointwise d hΞ hξ
  rw [sq_abs] at this
  refine this.trans ?_
  have : Real.exp (-(|ξ| - Ξ)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  calc _ ≤ (d.factorial : ℝ) * Real.exp 1 * (1 + Ξ) ^ d * Real.exp (-π * Ξ ^ 2) * 1 := by gcongr
    _ = _ := by ring

open Complex in
open scoped FourierTransform in
/-- `𝓕(R(x) e^{-πx²})` has Gaussian decay: `‖𝓕 F_R (ξ)‖ ≤ K (1+|ξ|)^d e^{-πξ²}`. -/
theorem fourier_F_bound (R : ℝ[X]) : ∃ K : ℝ, ∃ d : ℕ, 0 ≤ K ∧ ∀ ξ : ℝ,
    ‖𝓕 (fun x : ℝ => ((F R x : ℝ) : ℂ)) ξ‖ ≤ K * (1 + |ξ|) ^ d * Real.exp (-π * ξ ^ 2) := by
  set N := R.natDegree
  set T : ℕ → ℝ → ℂ := fun k x => (R.coeff k : ℂ) * ((x : ℂ) ^ k * Gaussian.G x)
  have hsum : (fun x : ℝ => ((F R x : ℝ) : ℂ)) = fun x => ∑ k ∈ Finset.range (N + 1), T k x := by
    funext x
    simp only [F, T, Gaussian.G, eval_eq_sum_range, Complex.ofReal_mul, Complex.ofReal_sum,
      Complex.ofReal_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => by ring
  refine ⟨∑ k ∈ Finset.range (N + 1), |R.coeff k| * ((2 * π)⁻¹ ^ k * Gaussian.coeffSum (Gaussian.P k)),
    ∑ k ∈ Finset.range (N + 1), (Gaussian.P k).natDegree, ?_, fun ξ => ?_⟩
  · refine Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (mul_nonneg (by positivity) ?_)
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hTi : ∀ k, Integrable (fun v : ℝ => 𝐞 (-(v * ξ)) • T k v) := by
    intro k
    refine ((Gaussian.integrable_pow_mul_G k).const_mul (R.coeff k : ℂ)).norm.mono'
      ?_ (Filter.Eventually.of_forall fun v => ?_)
    · exact (Continuous.smul (by fun_prop) (by
        simp only [T, Gaussian.G]; fun_prop)).aestronglyMeasurable
    · rw [Circle.norm_smul]
  have hlin : 𝓕 (fun x : ℝ => ((F R x : ℝ) : ℂ)) ξ = ∑ k ∈ Finset.range (N + 1), 𝓕 (T k) ξ := by
    rw [hsum, Real.fourier_real_eq]
    simp_rw [Finset.smul_sum]
    rw [integral_finsetSum _ fun k _ => hTi k]
    refine Finset.sum_congr rfl fun k _ => by rw [Real.fourier_real_eq]
  have hTk : ∀ k, 𝓕 (T k) ξ = (R.coeff k : ℂ) * 𝓕 (fun x : ℝ => (x : ℂ) ^ k * Gaussian.G x) ξ := by
    intro k
    rw [Real.fourier_real_eq, Real.fourier_real_eq, ← integral_const_mul]
    congr 1; ext v; simp only [T, Circle.smul_def, smul_eq_mul]; ring
  rw [hlin]
  have hx1 : (1:ℝ) ≤ 1 + |ξ| := by linarith [abs_nonneg ξ]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [hTk, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have b := Gaussian.norm_fourier_pow_mul_G_le k ξ
  calc |R.coeff k| * ‖𝓕 (fun x : ℝ => (x : ℂ) ^ k * Gaussian.G x) ξ‖
      ≤ |R.coeff k| * ((2 * π)⁻¹ ^ k * Gaussian.coeffSum (Gaussian.P k) *
          (1 + |ξ|) ^ (Gaussian.P k).natDegree * Real.exp (-π * ξ ^ 2)) := by gcongr
    _ ≤ |R.coeff k| * ((2 * π)⁻¹ ^ k * Gaussian.coeffSum (Gaussian.P k)) *
          (1 + |ξ|) ^ (∑ k ∈ Finset.range (N + 1), (Gaussian.P k).natDegree) * Real.exp (-π * ξ ^ 2) := by
        have hcs : 0 ≤ Gaussian.coeffSum (Gaussian.P k) := Finset.sum_nonneg fun _ _ => abs_nonneg _
        rw [show |R.coeff k| * ((2 * π)⁻¹ ^ k * Gaussian.coeffSum (Gaussian.P k) *
          (1 + |ξ|) ^ (Gaussian.P k).natDegree * Real.exp (-π * ξ ^ 2)) =
          |R.coeff k| * ((2 * π)⁻¹ ^ k * Gaussian.coeffSum (Gaussian.P k)) *
          (1 + |ξ|) ^ (Gaussian.P k).natDegree * Real.exp (-π * ξ ^ 2) by ring]
        gcongr
        exact Finset.single_le_sum (f := fun k => (Gaussian.P k).natDegree)
          (fun _ _ => Nat.zero_le _) hk

end GaussPoly
end RhWeil
