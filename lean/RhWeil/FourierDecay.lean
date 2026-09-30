import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Distribution.SchwartzSpace

/-!
# Fourier decay `|𝓕φ(ξ)| ≤ ‖φ''‖₁ / (4π² ξ²)` for `φ ∈ C²_c` with `∫ φ = 0`

This supplies the hypothesis `hF` of `Radical.Esum_isBigO` / `paperFT_Esum_zero'`.
-/

noncomputable section

namespace RhWeil

open Complex MeasureTheory Real
open scoped FourierTransform

theorem norm_fourier_le_integral (f : ℝ → ℂ) (ξ : ℝ) : ‖𝓕 f ξ‖ ≤ ∫ x, ‖f x‖ := by
  rw [Real.fourier_real_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; ext x
  rw [Circle.norm_smul]

theorem norm_fourier_le_of_contDiff_two {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ)
    (h0 : 𝓕 φ 0 = 0) (ξ : ℝ) :
    ‖𝓕 φ ξ‖ ≤ (∫ x, ‖iteratedDeriv 2 φ x‖) / (4 * π ^ 2) / ξ ^ 2 := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [h0]
  have hsd : ∀ n : ℕ, HasCompactSupport (iteratedDeriv n φ) := by
    intro n
    rw [iteratedDeriv_eq_iterate]
    induction n with
    | zero => simpa using hs
    | succ n ih => rw [Function.iterate_succ_apply']; exact ih.deriv
  have hint : ∀ n : ℕ, (n : ℕ∞) ≤ (2 : ℕ∞) → Integrable (iteratedDeriv n φ) := by
    intro n hn
    exact (hφ.continuous_iteratedDeriv n (by exact_mod_cast hn)).integrable_of_hasCompactSupport
      (hsd n)
  have key := congrFun (fourier_iteratedDeriv (N := (2 : ℕ∞)) (n := 2) (by exact_mod_cast hφ) hint le_rfl) ξ
  have hpos : 0 < 4 * π ^ 2 * ξ ^ 2 := by positivity
  have hnorm : ‖((2 * π * I * ξ) ^ 2 : ℂ)‖ = 4 * π ^ 2 * ξ ^ 2 := by
    rw [norm_pow, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, norm_I, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos pi_pos]
    ring_nf; rw [sq_abs]
  have h1 : 4 * π ^ 2 * ξ ^ 2 * ‖𝓕 φ ξ‖ ≤ ∫ x, ‖iteratedDeriv 2 φ x‖ := by
    rw [← hnorm, ← norm_mul, ← smul_eq_mul, ← key]
    exact norm_fourier_le_integral _ ξ
  rw [div_div, le_div_iff₀ (by positivity)]
  linarith

end RhWeil

namespace RhWeil

open Complex MeasureTheory Real Filter Asymptotics Topology Set

/-- An even `C²` function with `φ(0) = 0` is `O(v²)` at `0⁺`. -/
theorem isBigO_sq_of_even {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ) (heven : ∀ v, φ (-v) = φ v)
    (h00 : φ 0 = 0) : φ =O[𝓝[>] 0] (fun v : ℝ => v ^ (2 : ℝ)) := by
  have hd1 : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hc2 : ContDiff ℝ 1 (deriv φ) := hφ.iterate_deriv' 1 1
  have hd2 : Differentiable ℝ (deriv φ) := hc2.differentiable one_ne_zero
  have hcont2 : Continuous (deriv (deriv φ)) := (hφ.iterate_deriv' 0 2).continuous
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont2.continuousOn
  -- `φ'(0) = 0` by evenness
  have hder0 : deriv φ 0 = 0 := by
    have h1 : deriv (fun v => φ (-v)) 0 = -deriv φ 0 := by
      simpa using deriv_comp_neg (f := φ) (x := 0)
    have h2 : deriv (fun v => φ (-v)) 0 = deriv φ 0 := by
      rw [show (fun v => φ (-v)) = φ from funext heven]
    have : deriv φ 0 = -deriv φ 0 := h2.symm.trans h1
    linear_combination this / 2
  refine IsBigO.of_bound M ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with v hv
  obtain ⟨hv0, hv1⟩ := hv
  -- `|φ'(t)| ≤ M t` on `[0, v]`
  have hφ' : ∀ t ∈ Icc (0:ℝ) v, ‖deriv φ t‖ ≤ M * v := by
    intro t ht
    have := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (fun x _ => hd2 x) (fun x hx => hM x hx) (left_mem_Icc.2 zero_le_one)
      ⟨ht.1, ht.2.trans hv1.le⟩
    rw [hder0, sub_zero, sub_zero, Real.norm_eq_abs, abs_of_nonneg ht.1] at this
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (left_mem_Icc.2 zero_le_one))
    exact this.trans (mul_le_mul_of_nonneg_left ht.2 hM0)
  have := (convex_Icc (0:ℝ) v).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => hd1 x) hφ' (left_mem_Icc.2 hv0.le) (right_mem_Icc.2 hv0.le)
  rw [h00, sub_zero, sub_zero, Real.norm_eq_abs, abs_of_pos hv0] at this
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hv0 _), Real.rpow_two]
  nlinarith

end RhWeil
