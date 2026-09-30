import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The cut-off `χ(x) = st((b+δ-x)/δ) st((b+δ+x)/δ)`

`χ` is smooth and even, `0 ≤ χ ≤ 1`, `χ = 1` on `|x| ≤ b`, `χ = 0` on `|x| ≥ b + δ`, and
`|χ^{(j)}(x)| ≤ E_j δ^{-j}`, with `E_j` independent of `b, δ`.
-/

noncomputable section

namespace RhWeil
namespace Cutoff

open Real Set Filter Topology

local notation "st" => Real.smoothTransition

/-- Iterated derivative of `f (A x + B)`. -/
theorem iteratedDeriv_comp_affine {f : ℝ → ℝ} (hf : ∀ n : ℕ, ContDiff ℝ n f) (A B : ℝ) (j : ℕ) :
    iteratedDeriv j (fun x => f (A * x + B)) = fun x => A ^ j * iteratedDeriv j f (A * x + B) := by
  induction j with
  | zero => funext x; simp
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have hd : Differentiable ℝ (iteratedDeriv j f) := (hf (j + 1)).differentiable_iteratedDeriv' j
    have h1 : HasDerivAt (fun x => A * x + B) A x := by
      simpa using ((hasDerivAt_id x).const_mul A).add_const B
    have h2 := ((hd (A * x + B)).hasDerivAt.comp x h1).const_mul (A ^ j)
    have e : (fun y => A ^ j * (iteratedDeriv j f ∘ fun x => A * x + B) y) =
        fun x => A ^ j * iteratedDeriv j f (A * x + B) := rfl
    rw [e] at h2
    rw [h2.deriv, iteratedDeriv_succ]
    ring

theorem st_contDiff (n : ℕ) : ContDiff ℝ n st := Real.smoothTransition.contDiff

theorem continuous_iteratedDeriv_st (j : ℕ) : Continuous (iteratedDeriv j st) :=
  (st_contDiff j).continuous_iteratedDeriv' j

theorem iteratedDeriv_st_eq_zero {j : ℕ} (hj : 1 ≤ j) {x : ℝ} (hx : x < 0 ∨ 1 < x) :
    iteratedDeriv j st x = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rcases hx with hx | hx
  · have e : st =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hx] with w hw using Real.smoothTransition.zero_of_nonpos hw.le
    rw [e.iteratedDeriv_eq]; simp [iteratedDeriv_succ']
  · have e : st =ᶠ[𝓝 x] fun _ => 1 := by
      filter_upwards [Ioi_mem_nhds hx] with w hw using Real.smoothTransition.one_of_one_le hw.le
    rw [e.iteratedDeriv_eq]; simp [iteratedDeriv_succ']

/-- `S_j = sup |st^{(j)}|` exists. -/
theorem exists_bound_iteratedDeriv_st (j : ℕ) : ∃ S, 0 ≤ S ∧ ∀ x, |iteratedDeriv j st x| ≤ S := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · refine ⟨1, zero_le_one, fun x => ?_⟩
    simp only [iteratedDeriv_zero]
    rw [abs_of_nonneg (Real.smoothTransition.nonneg x)]; exact Real.smoothTransition.le_one x
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_iteratedDeriv_st j).continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Icc (0:ℝ) 1
  · exact (by simpa using hM x hx : |iteratedDeriv j st x| ≤ M).trans (le_max_left _ _)
  · simp only [mem_Icc, not_and_or, not_le] at hx
    rw [iteratedDeriv_st_eq_zero hj hx, abs_zero]; exact le_max_right _ _

/-- The cut-off. -/
def chi (b δ : ℝ) (x : ℝ) : ℝ := st ((b + δ - x) / δ) * st ((b + δ + x) / δ)

variable {b δ : ℝ}

theorem contDiff_chi (b δ : ℝ) {n : ℕ∞} : ContDiff ℝ n (chi b δ) := by
  unfold chi
  exact (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const δ)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.add contDiff_id).div_const δ))

theorem chi_even (x : ℝ) : chi b δ (-x) = chi b δ x := by
  simp only [chi, sub_neg_eq_add]; ring_nf

theorem chi_nonneg (x : ℝ) : 0 ≤ chi b δ x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem chi_le_one (x : ℝ) : chi b δ x ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem chi_eq_one (hδ : 0 < δ) {x : ℝ} (hx : |x| ≤ b) : chi b δ x = 1 := by
  have h1 := (abs_le.1 hx)
  simp only [chi]
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ hδ).2 (by linarith)),
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ hδ).2 (by linarith)), mul_one]

theorem chi_eq_zero (hδ : 0 < δ) {x : ℝ} (hx : b + δ ≤ |x|) : chi b δ x = 0 := by
  simp only [chi]
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h] at hx
    rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le),
      zero_mul]
  · rw [abs_of_nonpos h] at hx
    rw [Real.smoothTransition.zero_of_nonpos (x := (b + δ + x) / δ)
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le), mul_zero]

/-- Near `x > -b`, `χ` equals the right transition only. -/
theorem chi_eventuallyEq_right (hδ : 0 < δ) {x : ℝ} (hx : -b < x) :
    chi b δ =ᶠ[𝓝 x] fun y => st ((-1 / δ) * y + (b + δ) / δ) := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  simp only [chi]
  rw [Real.smoothTransition.one_of_one_le (x := (b + δ + y) / δ) ((le_div_iff₀ hδ).2 (by
    have : -b < y := hy; linarith)), mul_one]
  congr 1; field_simp; ring

theorem chi_eventuallyEq_left (hδ : 0 < δ) {x : ℝ} (hx : x < b) :
    chi b δ =ᶠ[𝓝 x] fun y => st ((1 / δ) * y + (b + δ) / δ) := by
  filter_upwards [Iio_mem_nhds hx] with y hy
  simp only [chi]
  rw [Real.smoothTransition.one_of_one_le (x := (b + δ - y) / δ) ((le_div_iff₀ hδ).2 (by
    have : y < b := hy; linarith)), one_mul]
  congr 1; field_simp; ring

/-- **Derivative bounds** `|χ^{(j)}(x)| ≤ S_j δ^{-j}`, and `χ^{(j)} = 0` on `|x| < b` for `j ≥ 1`. -/
theorem abs_iteratedDeriv_chi_le (hδ : 0 < δ) (hb : 0 < b) (j : ℕ) {S : ℝ}
    (hS : ∀ x, |iteratedDeriv j st x| ≤ S) (x : ℝ) :
    |iteratedDeriv j (chi b δ) x| ≤ S / δ ^ j := by
  rcases lt_or_ge (-b) x with hx | hx
  · rw [(chi_eventuallyEq_right hδ hx).iteratedDeriv_eq,
      iteratedDeriv_comp_affine st_contDiff, abs_mul, abs_pow,
      abs_div, abs_neg, abs_one, abs_of_pos hδ, div_pow, one_pow, one_div, ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right (hS _) (by positivity)
  · rw [(chi_eventuallyEq_left hδ (by linarith : x < b)).iteratedDeriv_eq,
      iteratedDeriv_comp_affine st_contDiff, abs_mul, abs_pow,
      abs_div, abs_one, abs_of_pos hδ, div_pow, one_pow, one_div, ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right (hS _) (by positivity)

theorem iteratedDeriv_chi_eq_zero (hδ : 0 < δ) {j : ℕ} (hj : 1 ≤ j) {x : ℝ} (hx : |x| < b) :
    iteratedDeriv j (chi b δ) x = 0 := by
  have e : chi b δ =ᶠ[𝓝 x] fun _ => 1 := by
    filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hx] with y hy
    exact chi_eq_one hδ hy.le
  rw [e.iteratedDeriv_eq]
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simp [iteratedDeriv_const]

end Cutoff
end RhWeil
