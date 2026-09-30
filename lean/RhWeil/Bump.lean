import RhWeil.FourierC2
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# A fixed bump `ψ`: smooth, even, `ψ(0) = 0`, `∫ψ = 1`, `supp ψ ⊆ [-1, 1]`

`ψ₀(x) = x² st(1 - x²)`, `ψ = ψ₀ / ∫ψ₀`. Its Fourier transform, and that of `x ψ'`, are `O(ξ⁻²)`.
-/

noncomputable section

namespace RhWeil
namespace Bump

open Real MeasureTheory Set
open scoped FourierTransform

local notation "st" => Real.smoothTransition

def psi0 (x : ℝ) : ℝ := x ^ 2 * st (1 - x ^ 2)

theorem contDiff_psi0 {n : ℕ∞} : ContDiff ℝ n psi0 :=
  (contDiff_id.pow 2).mul (Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2)))

theorem psi0_nonneg (x : ℝ) : 0 ≤ psi0 x := mul_nonneg (sq_nonneg x) (Real.smoothTransition.nonneg _)

theorem psi0_eq_zero {x : ℝ} (hx : 1 ≤ |x|) : psi0 x = 0 := by
  have : 1 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  simp [psi0, Real.smoothTransition.zero_of_nonpos (by linarith : 1 - x ^ 2 ≤ 0)]

theorem hasCompactSupport_psi0 : HasCompactSupport psi0 := by
  refine HasCompactSupport.intro (isCompact_closedBall (0:ℝ) 1) fun x hx => psi0_eq_zero ?_
  simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hx
  exact hx.le

def I0 : ℝ := ∫ x, psi0 x

theorem I0_pos : 0 < I0 := by
  refine (contDiff_psi0 (n := 0)).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := 1 / 2) hasCompactSupport_psi0 psi0_nonneg ?_
  have : 0 < st (1 - (1 / 2 : ℝ) ^ 2) := Real.smoothTransition.pos_of_pos (by norm_num)
  simp only [psi0]; positivity

/-- The bump. -/
def psi (x : ℝ) : ℝ := psi0 x / I0

theorem contDiff_psi {n : ℕ∞} : ContDiff ℝ n psi := contDiff_psi0.div_const _

theorem psi_even (x : ℝ) : psi (-x) = psi x := by simp [psi, psi0]

theorem psi_zero : psi 0 = 0 := by simp [psi, psi0]

theorem psi_eq_zero {x : ℝ} (hx : 1 ≤ |x|) : psi x = 0 := by simp [psi, psi0_eq_zero hx]

theorem hasCompactSupport_psi : HasCompactSupport psi := by
  refine HasCompactSupport.intro (isCompact_closedBall (0:ℝ) 1) fun x hx => psi_eq_zero ?_
  simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hx
  exact hx.le

theorem integral_psi : ∫ x, psi x = 1 := by
  simp only [psi]; rw [integral_div]; exact div_self I0_pos.ne'

/-- Fourier decay of a smooth compactly supported real function viewed in `ℂ`. -/
theorem exists_fourier_bound {f : ℝ → ℝ} (hf : ∀ n : ℕ, ContDiff ℝ n f) (hs : HasCompactSupport f) :
    ∃ C, ∀ ξ : ℝ, ξ ≠ 0 → ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ≤ C / ξ ^ 2 := by
  have hc : ∀ n : ℕ, ContDiff ℝ n (fun x => (f x : ℂ)) := fun n =>
    Complex.ofRealCLM.contDiff.comp (hf n)
  have hsd : ∀ n : ℕ, HasCompactSupport (iteratedDeriv n (fun x => (f x : ℂ))) := by
    intro n
    rw [iteratedDeriv_eq_iterate]
    induction n with
    | zero => exact hs.comp_left (g := fun y : ℝ => (y : ℂ)) (by simp)
    | succ n ih => rw [Function.iterate_succ_apply']; exact ih.deriv
  refine ⟨(∫ x, ‖iteratedDeriv 2 (fun x => (f x : ℂ)) x‖) / (4 * π ^ 2), fun ξ hξ => ?_⟩
  exact norm_fourier_le_of_integrable (hc 2) (fun n hn =>
    ((hc n).continuous_iteratedDeriv' n).integrable_of_hasCompactSupport (hsd n)) hξ

end Bump
end RhWeil
