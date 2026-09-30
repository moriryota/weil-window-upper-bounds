import RhWeil.TailPhi

/-!
# Tail bound for `𝓕(x φ_λ')` on `|ξ| ≥ Ξ`

`x φ' = x h' - x g' + ε x ψ'`; `x h' = F_{X·DR}` has Gaussian Fourier decay, `u = x g'` is handled by
`‖u''‖₁`, and `x ψ'` is a fixed compactly supported smooth function.
-/

noncomputable section

namespace RhWeil
namespace Concrete

open Real MeasureTheory Set Filter Topology Cutoff Complex Polynomial
open scoped FourierTransform

theorem abs_iteratedDeriv_id_le (i : ℕ) (x : ℝ) : |iteratedDeriv i (fun a : ℝ => a) x| ≤ 1 + |x| := by
  rw [iteratedDeriv_fun_id]
  split_ifs <;> simp <;> linarith [abs_nonneg x]

/-- `u = x g'`. -/
def u (b δ : ℝ) (x : ℝ) : ℝ := x * deriv (g b δ) x

theorem contDiff_deriv_g (b δ : ℝ) (n : ℕ) : ContDiff ℝ n (deriv (g b δ)) := by
  have := (contDiff_g b δ (m := ((n + 1 : ℕ) : ℕ∞))).iterate_deriv' n 1
  simpa using this

theorem contDiff_u (b δ : ℝ) (n : ℕ) : ContDiff ℝ n (u b δ) :=
  contDiff_id.mul (contDiff_deriv_g b δ n)

theorem u_eventually_zero {b δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : |x| < b) :
    u b δ =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hx] with y hy
  simp [u, (g_eventually_zero hδ hy).deriv_eq]

theorem iteratedDeriv_u_eq_zero {b δ : ℝ} (hδ : 0 < δ) (n : ℕ) {x : ℝ} (hx : |x| < b) :
    iteratedDeriv n (u b δ) x = 0 := by
  rw [(u_eventually_zero hδ hx).iteratedDeriv_eq, iteratedDeriv_const]; simp

theorem abs_iteratedDeriv_u_le {K : ℝ} {d : ℕ} (hK : 0 ≤ K)
    (hh : ∀ i ≤ 3, ∀ x, |iteratedDeriv i h x| ≤ K * (1 + |x|) ^ d * Real.exp (-π * x ^ 2))
    {B : ℝ} (hB1 : 1 ≤ B)
    (hB : ∀ {b δ : ℝ}, 0 < δ → 0 < b → ∀ k ≤ 3, ∀ x,
      |iteratedDeriv k (fun x => 1 - chi b δ x) x| ≤ B / δ ^ k)
    {b δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb : 0 < b) {n : ℕ} (hn : n ≤ 2) (x : ℝ) :
    |iteratedDeriv n (u b δ) x| ≤
      2 ^ n * (8 * K * B / δ ^ 3) * ((1 + |x|) ^ (d + 1) * Real.exp (-π * x ^ 2)) := by
  have e : u b δ = (fun a : ℝ => a) * deriv (g b δ) := rfl
  rw [e, iteratedDeriv_mul (f := fun a : ℝ => a) (g := deriv (g b δ)) (x := x)
    (contDiff_id.contDiffAt) ((contDiff_deriv_g b δ n).contDiffAt)]
  set G := (1 + |x|) ^ d * Real.exp (-π * x ^ 2)
  have hG : 0 ≤ G := by positivity
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i ∈ Finset.range (n + 1),
      |(n.choose i : ℝ) * iteratedDeriv i (fun a : ℝ => a) x * iteratedDeriv (n - i) (deriv (g b δ)) x|
        ≤ (n.choose i : ℝ) * ((8 * K * B / δ ^ 3) * ((1 + |x|) * G)) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [abs_mul, abs_mul, Nat.abs_cast, ← iteratedDeriv_succ']
    have h1 := abs_iteratedDeriv_id_le i x
    have h2 := abs_iteratedDeriv_g_le hK hh hB1 hB hδ hδ1 hb (n := n - i + 1) (by omega) x
    have h3 : 2 ^ (n - i + 1) * K * B / δ ^ (n - i + 1) ≤ 8 * K * B / δ ^ 3 := by
      have p1 : (2:ℝ) ^ (n - i + 1) ≤ 8 := by
        calc (2:ℝ) ^ (n - i + 1) ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) (by omega)
          _ = 8 := by norm_num
      have p2 : δ ^ 3 ≤ δ ^ (n - i + 1) := pow_le_pow_of_le_one hδ.le hδ1 (by omega)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hKB : 0 ≤ K * B := mul_nonneg hK (by linarith)
      calc 2 ^ (n - i + 1) * K * B * δ ^ 3 = 2 ^ (n - i + 1) * (K * B) * δ ^ 3 := by ring
        _ ≤ 8 * (K * B) * δ ^ (n - i + 1) := by gcongr
        _ = 8 * K * B * δ ^ (n - i + 1) := by ring
    calc (n.choose i : ℝ) * |iteratedDeriv i (fun a : ℝ => a) x| * |iteratedDeriv (n - i + 1) (g b δ) x|
        ≤ (n.choose i : ℝ) * (1 + |x|) * (2 ^ (n - i + 1) * K * B / δ ^ (n - i + 1) * G) := by
          gcongr
      _ ≤ (n.choose i : ℝ) * (1 + |x|) * ((8 * K * B / δ ^ 3) * G) := by gcongr
      _ = (n.choose i : ℝ) * ((8 * K * B / δ ^ 3) * ((1 + |x|) * G)) := by ring
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← Finset.sum_mul]
  have : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  rw [this]; simp only [G]; ring

open GaussPoly in
theorem integrable_F_ofReal (R : ℝ[X]) : Integrable (fun x : ℝ => ((F R x : ℝ) : ℂ)) := by
  have hsum : (fun x : ℝ => ((F R x : ℝ) : ℂ)) = fun x : ℝ =>
      ∑ k ∈ Finset.range (R.natDegree + 1), (R.coeff k : ℂ) * ((x : ℂ) ^ k * Gaussian.G x) := by
    funext x
    simp only [F, Gaussian.G, eval_eq_sum_range, Complex.ofReal_mul, Complex.ofReal_sum,
      Complex.ofReal_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [hsum]
  exact integrable_finset_sum _ fun k _ => (Gaussian.integrable_pow_mul_G k).const_mul _

theorem deriv_φR (lam : ℝ) : deriv (φR lam) =
    fun x => deriv h x - deriv (g (bb lam) (δ lam)) x + eps lam * deriv Bump.psi x := by
  have e : φR lam = fun x => h x - g (bb lam) (δ lam) x + eps lam * Bump.psi x := by
    funext x; simp only [φR, g]; ring
  rw [e]; funext x
  have h1 := (contDiff_h (m := 1).differentiable one_ne_zero x).hasDerivAt
  have h2 := ((contDiff_g (bb lam) (δ lam) (m := 1)).differentiable one_ne_zero x).hasDerivAt
  have h3 := ((Bump.contDiff_psi (n := 1)).differentiable one_ne_zero x).hasDerivAt
  exact ((h1.sub h2).add (h3.const_mul (eps lam))).deriv

open GaussPoly in
theorem psi1_φ_eq (lam : ℝ) : Construction.psi1 (φ lam) = fun x =>
    ((F (X * D R) x : ℝ) : ℂ) - ((u (bb lam) (δ lam) x : ℝ) : ℂ) +
      ((eps lam : ℝ) : ℂ) * ((x * deriv Bump.psi x : ℝ) : ℂ) := by
  funext x
  have hd : deriv (φ lam) x = ((deriv (φR lam) x : ℝ) : ℂ) :=
    (((contDiff_φR lam (n := 1)).differentiable one_ne_zero x).hasDerivAt.ofReal_comp).deriv
  simp only [Construction.psi1, hd, deriv_φR, u]
  have e1 : F (X * D R) x = x * deriv h x := by
    rw [h, deriv_F]; simp only [F, eval_mul, eval_X]; ring
  rw [e1]; push_cast; ring

/-- **Tail bound for `𝓕(x φ_λ')`.** -/
theorem tail_psi1 : ∃ C : ℝ, ∃ q : ℕ, 0 ≤ C ∧ ∀ lam : ℝ, 3 ≤ lam → ∀ ξ : ℝ, Ξ lam ≤ |ξ| →
    ‖𝓕 (Construction.psi1 (φ lam)) ξ‖ ≤ C * lam ^ q * Real.exp (-π * lam ^ 2) / ξ ^ 2 := by
  obtain ⟨KF, dF, hKF, hF⟩ := GaussPoly.fourier_F_bound (X * GaussPoly.D R)
  obtain ⟨A, d, hA, hg⟩ := g_bounds_unif
  obtain ⟨K, d', hK, hh⟩ := exists_bound_h
  obtain ⟨B, hB1, hB⟩ := exists_bound_one_sub_chi
  have wsm : ∀ n : ℕ, ContDiff ℝ n (fun x => x * deriv Bump.psi x) := fun n => by
    have := (Bump.contDiff_psi (n := ((n + 1 : ℕ) : ℕ∞))).iterate_deriv' n 1
    exact contDiff_id.mul (by simpa using this)
  have wcs : HasCompactSupport (fun x => x * deriv Bump.psi x) :=
    Bump.hasCompactSupport_psi.deriv.mul_left
  obtain ⟨Cw, hw⟩ := Bump.exists_fourier_bound wsm wcs
  set Cw' := max Cw 0
  set C1 := KF * ((dF + 2).factorial * Real.exp 1 * 2 ^ (dF + 2) * Real.exp (2 * π))
  set C2 := 2 * (4 * (8 * K * B) * (d' + 1).factorial * Real.exp 1 * 2 ^ (d' + 1) * Real.exp (4 * π)) / (4 * π ^ 2)
  set C3 := 2 * (A * d.factorial * Real.exp 1 * 2 ^ d * Real.exp (4 * π)) * Cw'
  have hKB : 0 ≤ K * B := mul_nonneg hK (by linarith)
  refine ⟨C1 + C2 + C3, dF + d + d' + 9, by positivity, fun lam hl ξ hξ => ?_⟩
  have hl1 : 1 ≤ lam := by linarith
  have hΞ1 := Ξ_ge_one hl
  have hξ0 : ξ ≠ 0 := by intro h; rw [h, abs_zero] at hξ; linarith
  have hξ2 : 0 < ξ ^ 2 := by positivity
  have hδ := δ_pos hl
  have hδ1 : δ lam ≤ 1 := (δ_le hl).trans (by norm_num)
  have hb := bb_ge hl
  set E := Real.exp (-π * lam ^ 2)
  have hE : 0 < E := Real.exp_pos _
  obtain ⟨ig0, bg0⟩ := hg lam hl 0 (by norm_num)
  simp only [iteratedDeriv_zero] at ig0 bg0
  -- bounds for `u`
  have hub : ∀ n ≤ 2, Integrable (iteratedDeriv n (u (bb lam) (δ lam))) ∧
      ∫ x, |iteratedDeriv n (u (bb lam) (δ lam)) x| ≤
        2 * (2 ^ n * (8 * K * B / δ lam ^ 3) * (d' + 1).factorial * Real.exp 1 * (1 + bb lam) ^ (d' + 1) *
          Real.exp (-π * bb lam ^ 2)) := by
    intro n hn
    have hcont : Continuous (iteratedDeriv n (u (bb lam) (δ lam))) :=
      (contDiff_u (bb lam) (δ lam) n).continuous_iteratedDeriv' n
    exact integral_abs_le_of_tail hcont (by positivity) hb
      (fun x => abs_iteratedDeriv_u_le hK hh hB1 hB hδ hδ1 (by linarith) hn x)
      (fun x hx => iteratedDeriv_u_eq_zero hδ n hx)
  obtain ⟨iu0, _⟩ := hub 0 (by norm_num)
  simp only [iteratedDeriv_zero] at iu0
  have iw : Integrable (fun x => ((x * deriv Bump.psi x : ℝ) : ℂ)) :=
    ((wsm 0).continuous.integrable_of_hasCompactSupport wcs).ofReal
  rw [psi1_φ_eq, fourier_lin3 (f₁ := fun x => ((GaussPoly.F (X * GaussPoly.D R) x : ℝ) : ℂ))
    (f₂ := fun x => ((u (bb lam) (δ lam) x : ℝ) : ℂ)) (f₃ := fun x => ((x * deriv Bump.psi x : ℝ) : ℂ))
    (integrable_F_ofReal _) iu0.ofReal iw]
  have t1 : ‖𝓕 (fun x => ((GaussPoly.F (X * GaussPoly.D R) x : ℝ) : ℂ)) ξ‖ ≤
      C1 * lam ^ (dF + d + d' + 9) * E / ξ ^ 2 := by
    have b1 := hF ξ
    have b2 := GaussPoly.sup_tail (dF + 2) hΞ1 hξ
    have b3 : (1 + Ξ lam) ^ (dF + 2) ≤ (2 * lam) ^ (dF + 2) := by
      gcongr; linarith [Ξ_le hl]
    have b4 := exp_Ξ_le hl
    rw [le_div_iff₀ hξ2]
    calc ‖𝓕 (fun x => ((GaussPoly.F (X * GaussPoly.D R) x : ℝ) : ℂ)) ξ‖ * ξ ^ 2
        ≤ KF * (1 + |ξ|) ^ dF * Real.exp (-π * ξ ^ 2) * (1 + |ξ|) ^ 2 := by
          have hsq : ξ ^ 2 ≤ (1 + |ξ|) ^ 2 := by nlinarith [abs_nonneg ξ, sq_abs ξ]
          exact mul_le_mul b1 hsq (by positivity) (by positivity)
      _ = KF * ((1 + |ξ|) ^ (dF + 2) * Real.exp (-π * ξ ^ 2)) := by ring
      _ ≤ KF * ((dF + 2).factorial * Real.exp 1 * (1 + Ξ lam) ^ (dF + 2) * Real.exp (-π * Ξ lam ^ 2)) := by
          gcongr
      _ ≤ KF * ((dF + 2).factorial * Real.exp 1 * (2 * lam) ^ (dF + 2) * (Real.exp (2 * π) * E)) := by
          gcongr
      _ = C1 * lam ^ (dF + 2) * E := by simp only [C1]; ring
      _ ≤ C1 * lam ^ (dF + d + d' + 9) * E := by gcongr <;> omega
  have t2 : ‖𝓕 (fun x => ((u (bb lam) (δ lam) x : ℝ) : ℂ)) ξ‖ ≤
      C2 * lam ^ (dF + d + d' + 9) * E / ξ ^ 2 := by
    have hsm : ∀ n : ℕ, ContDiff ℝ n (u (bb lam) (δ lam)) := fun n => contDiff_u _ _ n
    have hdc : ContDiff ℝ 2 (fun x => ((u (bb lam) (δ lam) x : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (hsm 2)
    have hint : ∀ n : ℕ, (n : ℕ∞) ≤ (2 : ℕ∞) →
        Integrable (iteratedDeriv n (fun x => ((u (bb lam) (δ lam) x : ℝ) : ℂ))) := by
      intro n hn
      rw [iteratedDeriv_ofReal hsm]
      have hn2 : n ≤ 2 := by exact_mod_cast hn
      exact (hub n hn2).1.ofReal
    have key := norm_fourier_le_of_integrable hdc hint hξ0
    rw [iteratedDeriv_ofReal hsm] at key
    simp only [Complex.norm_real, Real.norm_eq_abs] at key
    refine key.trans ?_
    rw [div_le_div_iff_of_pos_right hξ2]
    have hδ3 : 1 / δ lam ^ 3 = lam ^ 6 := by
      rw [one_div, ← inv_pow, ← one_div, inv_δ hl]; ring
    calc (∫ x, |iteratedDeriv 2 (u (bb lam) (δ lam)) x|) / (4 * π ^ 2)
        ≤ 2 * (2 ^ 2 * (8 * K * B / δ lam ^ 3) * (d' + 1).factorial * Real.exp 1 * (1 + bb lam) ^ (d' + 1) *
            Real.exp (-π * bb lam ^ 2)) / (4 * π ^ 2) := by gcongr; exact (hub 2 le_rfl).2
      _ ≤ 2 * (2 ^ 2 * (8 * K * B * lam ^ 6) * (d' + 1).factorial * Real.exp 1 * (2 * lam) ^ (d' + 1) *
            (Real.exp (4 * π) * E)) / (4 * π ^ 2) := by
          rw [div_eq_mul_one_div (8 * K * B) (δ lam ^ 3), hδ3]
          have p1 : (1 + bb lam) ^ (d' + 1) ≤ (2 * lam) ^ (d' + 1) :=
            pow_le_pow_left₀ (by linarith [bb_ge hl]) (one_add_bb_le hl) _
          have p2 := exp_bb_le hl
          gcongr
      _ = C2 * lam ^ (d' + 7) * E := by simp only [C2]; ring
      _ ≤ C2 * lam ^ (dF + d + d' + 9) * E := by gcongr <;> omega
  have t3 : ‖((eps lam : ℝ) : ℂ) * 𝓕 (fun x => ((x * deriv Bump.psi x : ℝ) : ℂ)) ξ‖ ≤
      C3 * lam ^ (dF + d + d' + 9) * E / ξ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have he : |eps lam| ≤ 2 * (A * d.factorial * Real.exp 1 * (2 * lam) ^ d * (Real.exp (4 * π) * E)) := by
      refine (abs_integral_le_integral_abs).trans (bg0.trans ?_)
      simp only [pow_zero, div_one, one_mul]
      have p1 : (1 + bb lam) ^ d ≤ (2 * lam) ^ d :=
        pow_le_pow_left₀ (by linarith [bb_ge hl]) (one_add_bb_le hl) d
      have p2 := exp_bb_le hl
      gcongr
    have hp : ‖𝓕 (fun x => ((x * deriv Bump.psi x : ℝ) : ℂ)) ξ‖ ≤ Cw' / ξ ^ 2 :=
      (hw ξ hξ0).trans (by gcongr; exact le_max_left _ _)
    calc |eps lam| * ‖𝓕 (fun x => ((x * deriv Bump.psi x : ℝ) : ℂ)) ξ‖
        ≤ 2 * (A * d.factorial * Real.exp 1 * (2 * lam) ^ d * (Real.exp (4 * π) * E)) * (Cw' / ξ ^ 2) := by
          gcongr
      _ = C3 * lam ^ d * E / ξ ^ 2 := by simp only [C3]; ring
      _ ≤ C3 * lam ^ (dF + d + d' + 9) * E / ξ ^ 2 := by gcongr <;> omega
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add_left (norm_sub_le _ _) _).trans ?_
  refine (add_le_add (add_le_add t1 t2) t3).trans (le_of_eq ?_)
  ring

end Concrete
end RhWeil
