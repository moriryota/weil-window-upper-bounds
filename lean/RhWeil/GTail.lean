import RhWeil.GaussPoly
import RhWeil.Cutoff
import RhWeil.FourierC2

/-!
# Bounds for `g = h (1 - χ)` (Theorem A, §4)

`h = F_R` with `R = X⁴ - (3/2π) X²`, and `χ = chi b δ`. For `n ≤ 3` and `0 < δ ≤ 1`:
`|g^{(n)}(x)| ≤ 2ⁿ K B δ⁻ⁿ (1+|x|)^d e^{-πx²}`, `g^{(n)} = 0` on `|x| < b`, hence
`∫ (1+|x|)^e |g^{(n)}| ≤ 2ⁿ K B δ⁻ⁿ · 2 (d+e)! e (1+b)^{d+e} e^{-πb²}` for `b ≥ 1`.
-/

noncomputable section

namespace RhWeil
namespace Concrete

open Real Polynomial MeasureTheory Set Filter Topology
open GaussPoly Cutoff
open Gaussian (coeffSum)

/-- `R = X⁴ - (3/2π) X²`. -/
def R : ℝ[X] := X ^ 4 - C (3 / (2 * π)) * X ^ 2

/-- `h(x) = (x⁴ - (3/2π) x²) e^{-πx²}` (Riemann's function divided by `π²`). -/
def h : ℝ → ℝ := F R

theorem contDiff_h {m : ℕ∞} : ContDiff ℝ m h := contDiff_F R

/-- Uniform bound on `h, h', h'', h'''`. -/
theorem exists_bound_h : ∃ K d, 0 ≤ K ∧ ∀ i ≤ 3, ∀ x,
    |iteratedDeriv i h x| ≤ K * (1 + |x|) ^ d * Real.exp (-π * x ^ 2) := by
  refine ⟨∑ i ∈ Finset.range 4, coeffSum (D^[i] R), ∑ i ∈ Finset.range 4, (D^[i] R).natDegree,
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _, fun i hi x => ?_⟩
  have hi' : i ∈ Finset.range 4 := Finset.mem_range.2 (by omega)
  rw [h, iteratedDeriv_F]
  refine (abs_F_le _ x).trans ?_
  have hx : (1:ℝ) ≤ 1 + |x| := by linarith [abs_nonneg x]
  gcongr
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  · exact Finset.single_le_sum (f := fun i => coeffSum (D^[i] R))
      (fun j _ => Finset.sum_nonneg fun k _ => abs_nonneg _) hi'
  · exact Finset.single_le_sum (f := fun i => (D^[i] R).natDegree) (fun j _ => Nat.zero_le _) hi'

/-- `g = h (1 - χ)`. -/
def g (b δ : ℝ) (x : ℝ) : ℝ := h x * (1 - chi b δ x)

theorem contDiff_g (b δ : ℝ) {m : ℕ∞} : ContDiff ℝ m (g b δ) :=
  contDiff_h.mul (contDiff_const.sub (contDiff_chi b δ))

theorem g_eventually_zero {b δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : |x| < b) :
    g b δ =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hx] with y hy
  simp [g, chi_eq_one hδ hy.le]

/-- A single constant `B ≥ 1` with `|(1-χ)^{(k)}| ≤ B δ^{-k}` for `k ≤ 3`. -/
theorem exists_bound_one_sub_chi : ∃ B, 1 ≤ B ∧ ∀ {b δ : ℝ}, 0 < δ → 0 < b → ∀ k ≤ 3, ∀ x,
    |iteratedDeriv k (fun x => 1 - chi b δ x) x| ≤ B / δ ^ k := by
  choose S hS0 hS using exists_bound_iteratedDeriv_st
  refine ⟨1 + ∑ k ∈ Finset.range 4, S k, by
    linarith [Finset.sum_nonneg fun k (_ : k ∈ Finset.range 4) => hS0 k], ?_⟩
  intro b δ hδ hb k hk x
  have hSk : S k ≤ 1 + ∑ k ∈ Finset.range 4, S k := by
    have := Finset.single_le_sum (f := S) (fun j _ => hS0 j) (Finset.mem_range.2 (by omega : k < 4))
    linarith
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp only [iteratedDeriv_zero, pow_zero, div_one]
    have h0 := chi_nonneg (b := b) (δ := δ) x
    have h1 := chi_le_one (b := b) (δ := δ) x
    rw [abs_of_nonneg (by linarith)]
    linarith [Finset.sum_nonneg fun k (_ : k ∈ Finset.range 4) => hS0 k]
  · rw [iteratedDeriv_const_sub hk0, iteratedDeriv_neg, abs_neg]
    exact (abs_iteratedDeriv_chi_le hδ hb k (hS k) x).trans
      (div_le_div_of_nonneg_right hSk (by positivity))

theorem iteratedDeriv_g_eq_zero {b δ : ℝ} (hδ : 0 < δ) (n : ℕ) {x : ℝ} (hx : |x| < b) :
    iteratedDeriv n (g b δ) x = 0 := by
  rw [(g_eventually_zero hδ hx).iteratedDeriv_eq, iteratedDeriv_const]; simp

theorem abs_iteratedDeriv_g_le {K : ℝ} {d : ℕ} (hK : 0 ≤ K)
    (hh : ∀ i ≤ 3, ∀ x, |iteratedDeriv i h x| ≤ K * (1 + |x|) ^ d * Real.exp (-π * x ^ 2))
    {B : ℝ} (hB1 : 1 ≤ B)
    (hB : ∀ {b δ : ℝ}, 0 < δ → 0 < b → ∀ k ≤ 3, ∀ x,
      |iteratedDeriv k (fun x => 1 - chi b δ x) x| ≤ B / δ ^ k)
    {b δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb : 0 < b) {n : ℕ} (hn : n ≤ 3) (x : ℝ) :
    |iteratedDeriv n (g b δ) x| ≤
      2 ^ n * K * B / δ ^ n * ((1 + |x|) ^ d * Real.exp (-π * x ^ 2)) := by
  have e : g b δ = h * fun x => 1 - chi b δ x := rfl
  rw [e, iteratedDeriv_mul contDiff_h.contDiffAt
    ((contDiff_const.sub (contDiff_chi b δ)).contDiffAt)]
  set G := (1 + |x|) ^ d * Real.exp (-π * x ^ 2)
  have hG : 0 ≤ G := by positivity
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i ∈ Finset.range (n + 1),
      |(n.choose i : ℝ) * iteratedDeriv i h x * iteratedDeriv (n - i) (fun x => 1 - chi b δ x) x|
        ≤ (n.choose i : ℝ) * (K * B / δ ^ n * G) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [abs_mul, abs_mul, Nat.abs_cast]
    have h1 := hh i (hi'.trans hn) x
    have h2 := hB hδ hb (n - i) (by omega) x
    have h3 : B / δ ^ (n - i) ≤ B / δ ^ n := by
      apply div_le_div_of_nonneg_left (by linarith) (by positivity)
      exact pow_le_pow_of_le_one hδ.le hδ1 (by omega)
    calc (n.choose i : ℝ) * |iteratedDeriv i h x| * |iteratedDeriv (n - i) (fun x => 1 - chi b δ x) x|
        ≤ (n.choose i : ℝ) * (K * G) * (B / δ ^ n) := by
          gcongr
          · simpa [G, mul_assoc] using h1
          · exact h2.trans h3
      _ = (n.choose i : ℝ) * (K * B / δ ^ n * G) := by ring
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← Finset.sum_mul]
  have : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  rw [this]; ring

/-- **Integral bound.** If `|f| ≤ A (1+|x|)^d e^{-πx²}` and `f = 0` on `|x| < b`, `b ≥ 1`, then
`f` is integrable and `∫|f| ≤ 2 A d! e (1+b)^d e^{-πb²}`. -/
theorem integral_abs_le_of_tail {f : ℝ → ℝ} (hf : Continuous f) {A b : ℝ} {d : ℕ} (hA : 0 ≤ A)
    (hb : 1 ≤ b) (hbound : ∀ x, |f x| ≤ A * ((1 + |x|) ^ d * Real.exp (-π * x ^ 2)))
    (hzero : ∀ x, |x| < b → f x = 0) :
    Integrable f ∧ ∫ x, |f x| ≤
      2 * (A * d.factorial * Real.exp 1 * (1 + b) ^ d * Real.exp (-π * b ^ 2)) := by
  set c := A * d.factorial * Real.exp 1 * (1 + b) ^ d * Real.exp (-π * b ^ 2)
  have hc : 0 ≤ c := by positivity
  set m : ℝ → ℝ := fun x => c * (Set.indicator (Ici b) (fun x => Real.exp (-(x - b))) x +
    Set.indicator (Iic (-b)) (fun x => Real.exp (x + b)) x)
  have i1 : Integrable (Set.indicator (Ici b) fun x => Real.exp (-(x - b))) := by
    refine (integrable_indicator_iff measurableSet_Ici).2 ?_
    have : IntegrableOn (fun x => Real.exp b * Real.exp (-x)) (Ici b) :=
      ((integrableOn_Ici_iff_integrableOn_Ioi).2 (integrableOn_exp_neg_Ioi b)).const_mul _
    refine this.congr_fun (fun x _ => ?_) measurableSet_Ici
    show Real.exp b * Real.exp (-x) = _
    rw [← Real.exp_add]; ring_nf
  have i2 : Integrable (Set.indicator (Iic (-b)) fun x => Real.exp (x + b)) := by
    refine (integrable_indicator_iff measurableSet_Iic).2 ?_
    have : IntegrableOn (fun x => Real.exp b * Real.exp x) (Iic (-b)) :=
      (integrableOn_exp_Iic (-b)).const_mul _
    refine this.congr_fun (fun x _ => ?_) measurableSet_Iic
    show Real.exp b * Real.exp x = _
    rw [← Real.exp_add]; ring_nf
  have im : Integrable m := (i1.add i2).const_mul c
  have hle : ∀ x, |f x| ≤ m x := by
    intro x
    by_cases hx : |x| < b
    · rw [hzero x hx, abs_zero]
      exact mul_nonneg hc (add_nonneg (Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _)
        (Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _))
    · push_neg at hx
      rcases le_total 0 x with h0 | h0
      · rw [abs_of_nonneg h0] at hx
        have ht := tail_pointwise d hb hx
        have hn : x ∉ Iic (-b) := by simp; linarith
        simp only [m, Set.indicator_of_mem (show x ∈ Ici b from hx), Set.indicator_of_notMem hn, add_zero]
        refine (hbound x).trans ?_
        rw [abs_of_nonneg h0]
        calc A * ((1 + x) ^ d * Real.exp (-π * x ^ 2))
            ≤ A * (d.factorial * Real.exp 1 * (1 + b) ^ d * Real.exp (-π * b ^ 2) * Real.exp (-(x - b))) := by
              gcongr
          _ = c * Real.exp (-(x - b)) := by simp only [c]; ring
      · rw [abs_of_nonpos h0] at hx
        have ht := tail_pointwise d hb hx
        have hn : x ∉ Ici b := by simp; linarith
        simp only [m, Set.indicator_of_mem (show x ∈ Iic (-b) by simp; linarith), Set.indicator_of_notMem hn, zero_add]
        refine (hbound x).trans ?_
        rw [abs_of_nonpos h0]
        have e2 : (-x) ^ 2 = x ^ 2 := by ring
        rw [e2] at ht
        calc A * ((1 + -x) ^ d * Real.exp (-π * x ^ 2))
            ≤ A * (d.factorial * Real.exp 1 * (1 + b) ^ d * Real.exp (-π * b ^ 2) * Real.exp (-(-x - b))) := by
              gcongr
          _ = c * Real.exp (x + b) := by simp only [c]; ring_nf
  have hfi : Integrable f :=
    im.mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hle x)
  refine ⟨hfi, ?_⟩
  calc ∫ x, |f x| ≤ ∫ x, m x :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _) im
          (Filter.Eventually.of_forall hle)
    _ = c * (1 + 1) := by
        simp only [m]
        rw [integral_const_mul, integral_add i1 i2, integral_indicator measurableSet_Ici,
          integral_indicator measurableSet_Iic]
        congr 2
        · rw [integral_Ici_eq_integral_Ioi]
          have : ∫ x in Ioi b, Real.exp (-(x - b)) = ∫ x in Ioi b, Real.exp b * Real.exp (-x) := by
            refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
            rw [← Real.exp_add]; ring_nf
          rw [this, integral_const_mul, integral_exp_neg_Ioi, ← Real.exp_add]; simp
        · have : ∫ x in Iic (-b), Real.exp (x + b) = ∫ x in Iic (-b), Real.exp b * Real.exp x := by
            refine setIntegral_congr_fun measurableSet_Iic fun x _ => ?_
            rw [← Real.exp_add]; ring_nf
          rw [this, integral_const_mul, integral_exp_Iic, ← Real.exp_add]; simp
    _ = _ := by ring

/-! ### Basic properties of `h` -/

open Complex in
theorem h_ofReal (x : ℝ) : ((h x : ℝ) : ℂ) =
    (x : ℂ) ^ 4 * Gaussian.G x - ((3 / (2 * π) : ℝ) : ℂ) * ((x : ℂ) ^ 2 * Gaussian.G x) := by
  simp only [h, F, R, Gaussian.G, eval_sub, eval_pow, eval_X, eval_mul, eval_C]
  push_cast; ring

theorem h_even (x : ℝ) : h (-x) = h x := by
  simp only [h, F, R, eval_sub, eval_pow, eval_X, eval_mul, eval_C]; ring_nf

theorem h_zero : h 0 = 0 := by simp [h, F, R]

open Complex in
theorem integrable_h_ofReal : Integrable (fun x : ℝ => ((h x : ℝ) : ℂ)) := by
  simp_rw [h_ofReal]
  exact (Gaussian.integrable_pow_mul_G 4).sub ((Gaussian.integrable_pow_mul_G 2).const_mul _)

theorem integrable_h : Integrable h := by
  have := integrable_h_ofReal.re
  simpa using this

open Complex in
open scoped FourierTransform in
theorem integral_pow_mul_G (n : ℕ) :
    ∫ x : ℝ, (x : ℂ) ^ n * Gaussian.G x = (-2 * π * I) ^ (-(n : ℤ)) * (((Gaussian.P n).eval (0:ℝ) : ℝ) : ℂ) := by
  have := Gaussian.fourier_pow_mul_G n 0
  rw [Real.fourier_real_eq] at this
  simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul] at this
  rw [this]; simp [Gaussian.Q]

theorem integral_h : ∫ x, h x = 0 := by
  have hc : ∫ x : ℝ, ((h x : ℝ) : ℂ) = 0 := by
    simp_rw [h_ofReal]
    rw [integral_sub (Gaussian.integrable_pow_mul_G 4) ((Gaussian.integrable_pow_mul_G 2).const_mul _),
      integral_const_mul, integral_pow_mul_G, integral_pow_mul_G]
    have e2 : (Gaussian.P 2).eval 0 = -2 * π := by simp [Gaussian.P]
    have e4 : (Gaussian.P 4).eval 0 = 12 * π ^ 2 := by simp [Gaussian.P]; ring
    rw [e2, e4]
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
    simp only [zpow_neg, zpow_natCast]
    field_simp
    push_cast
    ring_nf
    simp [Complex.I_sq]
    field_simp
    ring
  rw [integral_complex_ofReal] at hc
  exact_mod_cast hc

end Concrete
end RhWeil
