import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Analytic.Uniqueness
import Zeta23.Statement
import Zeta23.ZetaReflect

/-!
# The radical lemma (Lemma 2.2 of the paper draft), Mellin form

For `φ` continuous on `ℝ`, vanishing on `[L, ∞)`, put `ℰφ(u) = u^{1/2} Σ_{n≥1} φ(n u)`.
Step 1 (this file, first part): for `Re s > 1/2`,
`mellin (ℰφ) s = ζ(s + 1/2) · mellin φ (s + 1/2)`.
-/

noncomputable section

namespace RhWeil
namespace Radical

open Complex MeasureTheory Set Filter Asymptotics Topology

variable {φ : ℝ → ℂ} {L : ℝ}

/-- `ℰφ(u) = u^{1/2} Σ_{n≥1} φ(n u)`. -/
def Esum (φ : ℝ → ℂ) (u : ℝ) : ℂ := (u : ℂ) ^ (1 / 2 : ℂ) * ∑' n : ℕ, φ (((n : ℝ) + 1) * u)

/-- The sum part `Σ_{n≥1} φ(n u)`. -/
def Fsum (φ : ℝ → ℂ) (u : ℝ) : ℂ := ∑' n : ℕ, φ (((n : ℝ) + 1) * u)

theorem mellinConvergent_of_support (hφc : Continuous φ) (hsupp : ∀ v, L ≤ v → φ v = 0)
    {w : ℂ} (hw : 0 < w.re) : MellinConvergent φ w := by
  refine mellinConvergent_of_isBigO_rpow (a := w.re + 1) (b := 0)
    (hφc.locallyIntegrable.locallyIntegrableOn _) ?_ (by linarith) ?_ (by simpa using hw)
  · refine (EventuallyEq.isBigO ?_).trans (isBigO_zero _ _)
    filter_upwards [eventually_ge_atTop L] with v hv using hsupp v hv
  · have : Tendsto φ (𝓝[>] 0) (𝓝 (φ 0)) := (hφc.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using this.isBigO_one ℝ

/-- `∫_{(0,∞)} ‖t^{w-1} φ(a t)‖ = a^{-Re w} ∫_{(0,∞)} ‖t^{w-1} φ(t)‖`. -/
theorem integral_norm_comp_mul_left (φ : ℝ → ℂ) (w : ℂ) {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0:ℝ), ‖(t : ℂ) ^ (w - 1) • φ (a * t)‖
      = a ^ (-w.re) * ∫ t in Ioi (0:ℝ), ‖(t : ℂ) ^ (w - 1) • φ t‖ := by
  set g : ℝ → ℝ := fun t => t ^ (w.re - 1) * ‖φ t‖
  have e1 : ∀ t ∈ Ioi (0:ℝ), ‖(t : ℂ) ^ (w - 1) • φ t‖ = g t := by
    intro t ht
    simp only [g, norm_smul, norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re]
  have e2 : ∀ t ∈ Ioi (0:ℝ), ‖(t : ℂ) ^ (w - 1) • φ (a * t)‖ = a ^ (1 - w.re) * g (a * t) := by
    intro t ht
    have ht' : (0:ℝ) < t := ht
    simp only [g, norm_smul, norm_cpow_eq_rpow_re_of_pos ht', sub_re, one_re]
    rw [Real.mul_rpow ha.le ht'.le, ← mul_assoc, ← mul_assoc, ← Real.rpow_add ha]
    ring_nf; simp
  rw [setIntegral_congr_fun measurableSet_Ioi e2, setIntegral_congr_fun measurableSet_Ioi e1,
    integral_const_mul, integral_comp_mul_left_Ioi g 0 ha, mul_zero, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [← Real.rpow_neg_one, ← Real.rpow_add ha]; ring_nf

/-- **Dirichlet region.** For `Re w > 1`, `mellin (Σ φ(n·)) w = ζ(w) · mellin φ w`. -/
theorem mellin_Fsum (hφc : Continuous φ) (hsupp : ∀ v, L ≤ v → φ v = 0) {w : ℂ} (hw : 1 < w.re) :
    mellin (Fsum φ) w = riemannZeta w * mellin φ w := by
  have hw0 : 0 < w.re := by linarith
  have hconv := mellinConvergent_of_support hφc hsupp hw0
  set F : ℕ → ℝ → ℂ := fun n t => (t : ℂ) ^ (w - 1) • φ (((n : ℝ) + 1) * t)
  have hpos : ∀ n : ℕ, (0:ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi 0)) := fun n =>
    (MellinConvergent.comp_mul_left (f := φ) (s := w) (hpos n)).2 hconv
  have hnorm : ∀ n, ∫ t in Ioi (0:ℝ), ‖F n t‖
      = ((n : ℝ) + 1) ^ (-w.re) * ∫ t in Ioi (0:ℝ), ‖(t : ℂ) ^ (w - 1) • φ t‖ :=
    fun n => integral_norm_comp_mul_left φ w (hpos n)
  have hsum : Summable fun n => ∫ t in Ioi (0:ℝ), ‖F n t‖ := by
    simp_rw [hnorm]
    refine Summable.mul_right _ ?_
    have := (Real.summable_nat_rpow_inv.2 hw)
    refine ((summable_nat_add_iff 1).2 this).congr fun n => ?_
    push_cast
    rw [Real.rpow_neg (by positivity)]
  have hHS := hasSum_integral_of_summable_integral_norm hint hsum
  have lhs : mellin (Fsum φ) w = ∫ t in Ioi (0:ℝ), ∑' n, F n t := by
    unfold mellin Fsum
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [F, smul_eq_mul]; rw [tsum_mul_left]
  have each : ∀ n : ℕ, ∫ t in Ioi (0:ℝ), F n t = 1 / ((n : ℂ) + 1) ^ w * mellin φ w := by
    intro n
    have := mellin_comp_mul_left φ w (hpos n)
    simp only [mellin] at this
    simp only [F]
    rw [this, smul_eq_mul, cpow_neg, one_div]
    push_cast; rfl
  rw [lhs, ← hHS.tsum_eq]
  simp_rw [each]
  rw [tsum_mul_right, zeta_eq_tsum_one_div_nat_add_one_cpow hw]

/-- **Step 1.** For `Re s > 1/2`, `mellin (ℰφ) s = ζ(s + 1/2) · mellin φ (s + 1/2)`. -/
theorem mellin_Esum (hφc : Continuous φ) (hsupp : ∀ v, L ≤ v → φ v = 0) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    mellin (Esum φ) s = riemannZeta (s + 1 / 2) * mellin φ (s + 1 / 2) := by
  have : Esum φ = fun t : ℝ => (t : ℂ) ^ (1 / 2 : ℂ) • Fsum φ t := by
    funext t; simp [Esum, Fsum, smul_eq_mul]
  rw [this, mellin_cpow_smul]
  exact mellin_Fsum hφc hsupp (by simp; linarith)

/-! ### Step 2: holomorphy of both sides -/

theorem exists_bound_nonneg (hφc : Continuous φ) (hsupp : ∀ v, L ≤ v → φ v = 0) :
    ∃ M, ∀ v, 0 ≤ v → ‖φ v‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := max L 0)).exists_bound_of_continuousOn
    hφc.continuousOn
  refine ⟨max M 0, fun v hv => ?_⟩
  by_cases h : v ≤ max L 0
  · exact (hM v ⟨hv, h⟩).trans (le_max_left _ _)
  · rw [hsupp v (by push_neg at h; exact (le_max_left _ _).trans h.le), norm_zero]
    exact le_max_right _ _

theorem continuousOn_Fsum (hφc : Continuous φ) (hsupp : ∀ v, L ≤ v → φ v = 0) :
    ContinuousOn (Fsum φ) (Ioi 0) := by
  obtain ⟨M, hM⟩ := exists_bound_nonneg hφc hsupp
  intro u₀ hu₀
  have hu₀' : (0:ℝ) < u₀ := hu₀
  set ε := u₀ / 2
  have hε : 0 < ε := by positivity
  -- on `Ioi ε` only the terms with `(n+1) ε < L` can be non-zero
  have hcont : ContinuousOn (Fsum φ) (Ioi ε) := by
    refine continuousOn_tsum (u := fun n : ℕ => if ((n : ℝ) + 1) * ε < L then M else 0)
      (fun n => (hφc.comp (continuous_const.mul continuous_id)).continuousOn) ?_ ?_
    · refine summable_of_ne_finset_zero (s := Finset.range (Nat.ceil (L / ε) + 1)) fun n hn => ?_
      simp only [Finset.mem_range, not_lt] at hn
      rw [if_neg]; push_neg
      have h1 : L / ε ≤ n := by
        have := Nat.le_ceil (L / ε); have h2 : (Nat.ceil (L / ε) : ℝ) ≤ n := by exact_mod_cast (by omega : Nat.ceil (L / ε) ≤ n)
        linarith
      have := (div_le_iff₀ hε).1 h1
      nlinarith
    · intro n u hu
      have hu' : ε < u := hu
      split_ifs with h
      · exact hM _ (mul_pos (by positivity) (hε.trans hu')).le
      · push_neg at h
        rw [hsupp _ (h.trans (mul_le_mul_of_nonneg_left hu'.le (by positivity))), norm_zero]
  exact (hcont.continuousAt (Ioi_mem_nhds (half_lt_self hu₀'))).continuousWithinAt

theorem continuousOn_Esum (hφc : Continuous φ) (hsupp : ∀ v, L ≤ v → φ v = 0) :
    ContinuousOn (Esum φ) (Ioi 0) := by
  have h1 : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (1 / 2 : ℂ)) (Ioi 0) := fun u hu =>
    (continuousAt_ofReal_cpow_const u (1 / 2) (Or.inr (ne_of_gt hu))).continuousWithinAt
  exact h1.mul (continuousOn_Fsum hφc hsupp)

theorem Esum_eq_zero_of_ge (hsupp : ∀ v, L ≤ v → φ v = 0) {u : ℝ} (hu : L ≤ u) (hu0 : 0 ≤ u) :
    Esum φ u = 0 := by
  have : ∀ n : ℕ, φ (((n : ℝ) + 1) * u) = 0 := fun n =>
    hsupp _ (hu.trans (le_mul_of_one_le_left hu0 (by linarith [n.cast_nonneg (α := ℝ)])))
  simp [Esum, this]

theorem differentiableAt_mellin_Esum (hφc : Continuous φ) (hsupp : ∀ v, L ≤ v → φ v = 0)
    (hdecay : Esum φ =O[𝓝[>] 0] (fun u : ℝ => u ^ (3 / 2 : ℝ))) {s : ℂ} (hs : -(3 / 2) < s.re) :
    DifferentiableAt ℂ (mellin (Esum φ)) s := by
  refine mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := -(3 / 2))
    ((continuousOn_Esum hφc hsupp).locallyIntegrableOn measurableSet_Ioi) ?_ (by linarith)
    (by simpa using hdecay) hs
  refine (EventuallyEq.isBigO ?_).trans (isBigO_zero _ _)
  filter_upwards [eventually_ge_atTop (max L 0)] with u hu
  exact Esum_eq_zero_of_ge hsupp ((le_max_left _ _).trans hu) ((le_max_right _ _).trans hu)

theorem differentiableAt_mellin_phi (hφc : Continuous φ) (hsupp : ∀ v, L ≤ v → φ v = 0)
    (hφ0 : φ =O[𝓝[>] 0] (fun v : ℝ => v ^ (2 : ℝ))) {w : ℂ} (hw : -2 < w.re) :
    DifferentiableAt ℂ (mellin φ) w := by
  refine mellin_differentiableAt_of_isBigO_rpow (a := w.re + 1) (b := -2)
    ((hφc.locallyIntegrable.locallyIntegrableOn _)) ?_ (by linarith) (by simpa using hφ0) hw
  refine (EventuallyEq.isBigO ?_).trans (isBigO_zero _ _)
  filter_upwards [eventually_ge_atTop L] with v hv using hsupp v hv

/-! ### Step 3: the domain `{Re s > -3/2} \ {1/2}` is preconnected -/

def Udom : Set ℂ := {s | -(3 / 2) < s.re} \ {1 / 2}

theorem isOpen_Udom : IsOpen Udom :=
  (isOpen_lt continuous_const continuous_re).sdiff isClosed_singleton

theorem isPreconnected_Udom : IsPreconnected Udom := by
  set H : Set ℂ := {s | -(3 / 2) < s.re}
  have cH : Convex ℝ H := convex_halfSpace_re_gt _
  set A := H ∩ {s : ℂ | 0 < s.im}
  set B : Set ℂ := {s | 1 / 2 < s.re}
  set C := H ∩ {s : ℂ | s.im < 0}
  set D := H ∩ {s : ℂ | s.re < 1 / 2}
  have pA : IsPreconnected A := (cH.inter (convex_halfSpace_im_gt _)).isPreconnected
  have pB : IsPreconnected B := (convex_halfSpace_re_gt _).isPreconnected
  have pC : IsPreconnected C := (cH.inter (convex_halfSpace_im_lt _)).isPreconnected
  have pD : IsPreconnected D := (cH.inter (convex_halfSpace_re_lt _)).isPreconnected
  have pAB : IsPreconnected (A ∪ B) :=
    pA.union (1 + I) ⟨by simp [H]; norm_num, by simp⟩ (by simp [B]; norm_num) pB
  have pABC : IsPreconnected (A ∪ B ∪ C) :=
    pAB.union (1 - I) (Or.inr (by simp [B]; norm_num)) ⟨by simp [H]; norm_num, by simp⟩ pC
  have pABCD : IsPreconnected (A ∪ B ∪ C ∪ D) :=
    pABC.union (-I) (Or.inr ⟨by simp [H], by simp⟩) ⟨by simp [H], by norm_num⟩ pD
  convert pABCD using 1
  ext s
  simp only [Udom, H, A, B, C, D, mem_diff, mem_setOf_eq, mem_singleton_iff, mem_union, mem_inter_iff]
  constructor
  · rintro ⟨h1, h2⟩
    rcases lt_trichotomy s.im 0 with h | h | h
    · exact Or.inl (Or.inr ⟨h1, h⟩)
    · rcases lt_or_gt_of_ne (show s.re ≠ 1 / 2 from fun hr => h2 (Complex.ext (by simpa using hr) (by simpa using h))) with hr | hr
      · exact Or.inr ⟨h1, hr⟩
      · exact Or.inl (Or.inl (Or.inr hr))
    · exact Or.inl (Or.inl (Or.inl ⟨h1, h⟩))
  · rintro (((⟨h1, h⟩ | h) | ⟨h1, h⟩) | ⟨h1, h⟩)
    · exact ⟨h1, fun e => by rw [e] at h; simp at h⟩
    · exact ⟨by linarith, fun e => by rw [e] at h; simp at h⟩
    · exact ⟨h1, fun e => by rw [e] at h; simp at h⟩
    · exact ⟨h1, fun e => by rw [e] at h; norm_num at h⟩

/-! ### Step 4: identity on `Udom` and vanishing at the zeros -/

theorem mellin_Esum_eqOn (hφc : Continuous φ) (hsupp : ∀ v, L ≤ v → φ v = 0)
    (hφ0 : φ =O[𝓝[>] 0] (fun v : ℝ => v ^ (2 : ℝ)))
    (hdecay : Esum φ =O[𝓝[>] 0] (fun u : ℝ => u ^ (3 / 2 : ℝ))) :
    EqOn (mellin (Esum φ)) (fun s => riemannZeta (s + 1 / 2) * mellin φ (s + 1 / 2)) Udom := by
  have hf : AnalyticOnNhd ℂ (mellin (Esum φ)) Udom :=
    DifferentiableOn.analyticOnNhd (fun s hs =>
      (differentiableAt_mellin_Esum hφc hsupp hdecay hs.1).differentiableWithinAt) isOpen_Udom
  have hg : AnalyticOnNhd ℂ (fun s => riemannZeta (s + 1 / 2) * mellin φ (s + 1 / 2)) Udom := by
    refine (DifferentiableOn.analyticOnNhd (fun s hs => ?_) isOpen_Udom)
    have hs1 : s + 1 / 2 ≠ 1 := fun e => hs.2 (by
      simp only [mem_singleton_iff]; linear_combination e)
    have hre : -2 < (s + 1 / 2).re := by
      have := hs.1; simp at this ⊢; linarith
    exact (((differentiableAt_riemannZeta hs1).comp s (differentiableAt_id.add_const _)).mul
      ((differentiableAt_mellin_phi hφc hsupp hφ0 hre).comp s
        (differentiableAt_id.add_const _))).differentiableWithinAt
  have h2 : (2 : ℂ) ∈ Udom := ⟨by simp; norm_num, by simp; norm_num⟩
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_Udom h2 ?_
  have : {s : ℂ | 1 / 2 < s.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by simp; norm_num)
  filter_upwards [this] with s hs using mellin_Esum hφc hsupp hs

/-- **Radical lemma (Mellin form).** If `ζ(ρ) = 0` with `0 < Re ρ < 1`, then
`mellin (ℰφ) (ρ - 1/2) = 0`. -/
theorem mellin_Esum_zero (hφc : Continuous φ) (hsupp : ∀ v, L ≤ v → φ v = 0)
    (hφ0 : φ =O[𝓝[>] 0] (fun v : ℝ => v ^ (2 : ℝ)))
    (hdecay : Esum φ =O[𝓝[>] 0] (fun u : ℝ => u ^ (3 / 2 : ℝ)))
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (hζ : riemannZeta ρ = 0) :
    mellin (Esum φ) (ρ - 1 / 2) = 0 := by
  have hU : ρ - 1 / 2 ∈ Udom := by
    refine ⟨by simp; linarith, fun e => ?_⟩
    have := congrArg Complex.re e; simp at this; linarith
  rw [mellin_Esum_eqOn hφc hsupp hφ0 hdecay hU]
  simp [hζ]

/-! ### Step 5: from Mellin to `paperFT` (`u = e^y`), and the zeros `±γ_ρ` -/

theorem ofReal_exp_cpow (y : ℝ) (w : ℂ) : ((Real.exp y : ℝ) : ℂ) ^ w = Complex.exp (y * w) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos y).ne'),
    ← Complex.ofReal_log (Real.exp_pos y).le, Real.log_exp]

theorem integral_Ioi_eq_integral_exp (g : ℝ → ℂ) :
    ∫ t in Ioi (0:ℝ), g t = ∫ y : ℝ, Real.exp y • g (Real.exp y) := by
  rw [← Real.range_exp, ← image_univ, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn, setIntegral_univ]
  simp [abs_of_pos (Real.exp_pos _)]

/-- `ê(z) = mellin (ℰφ) (i z)` with `e = ℰφ ∘ exp`. -/
theorem paperFT_Esum_exp (φ : ℝ → ℂ) (z : ℂ) :
    Zeta23.paperFT (fun y => Esum φ (Real.exp y)) z = mellin (Esum φ) (I * z) := by
  unfold mellin Zeta23.paperFT
  rw [integral_Ioi_eq_integral_exp]
  congr 1; ext y
  rw [ofReal_exp_cpow, real_smul, smul_eq_mul, ← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
  rw [mul_comm (Esum φ _)]
  congr 2; ring

/-- **Radical lemma.** For every non-trivial zero `ρ`, `ê(γ_ρ) = ê(-γ_ρ) = 0`. -/
theorem paperFT_Esum_zero (hφc : Continuous φ) (hsupp : ∀ v, L ≤ v → φ v = 0)
    (hφ0 : φ =O[𝓝[>] 0] (fun v : ℝ => v ^ (2 : ℝ)))
    (hdecay : Esum φ =O[𝓝[>] 0] (fun u : ℝ => u ^ (3 / 2 : ℝ)))
    {ρ : ℂ} (hρ : Zeta23.IsNontrivialZero ρ) :
    Zeta23.paperFT (fun y => Esum φ (Real.exp y)) (Zeta23.gammaOf ρ) = 0 ∧
    Zeta23.paperFT (fun y => Esum φ (Real.exp y)) (-Zeta23.gammaOf ρ) = 0 := by
  obtain ⟨hζ, h0, h1⟩ := hρ
  -- `1 - ρ` is a zero as well: conjugate, then reflect.
  have hρ1 : ρ ≠ 1 := fun e => by rw [e] at h1; simp at h1
  have hconj : Zeta23.IsNontrivialZero ((starRingEnd ℂ) ρ) :=
    ⟨by rw [Zeta23.riemannZeta_conj hρ1, hζ, map_zero], by simpa using h0, by simpa using h1⟩
  obtain ⟨hζ', h0', h1'⟩ := Zeta23.zeta_reflect_zero _ hconj
  have hr : Zeta23.reflect ((starRingEnd ℂ) ρ) = 1 - ρ := by simp [Zeta23.reflect]
  rw [hr] at hζ' h0' h1'
  have g1 : I * Zeta23.gammaOf ρ = ρ - 1 / 2 := by
    simp only [Zeta23.gammaOf]; field_simp
  have g2 : I * -Zeta23.gammaOf ρ = (1 - ρ) - 1 / 2 := by
    rw [mul_neg, g1]; ring
  refine ⟨?_, ?_⟩
  · rw [paperFT_Esum_exp, g1]; exact mellin_Esum_zero hφc hsupp hφ0 hdecay h0 h1 hζ
  · rw [paperFT_Esum_exp, g2]; exact mellin_Esum_zero hφc hsupp hφ0 hdecay h0' h1' hζ'

end Radical
end RhWeil
