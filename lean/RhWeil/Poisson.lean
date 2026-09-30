import RhWeil.Radical
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.PSeries

/-!
# Poisson summation: `ℰφ(u) = O(u^{3/2})` as `u → 0⁺` (Lemma 2.1 of the paper draft)

For `φ` continuous, even, compactly supported, with `|𝓕φ(ξ)| ≤ C/ξ²` (which forces `𝓕φ(0) = ∫φ = 0`),
Poisson summation gives `Σ_{n∈ℤ} φ(u n) = u⁻¹ Σ_{m∈ℤ} 𝓕φ(m/u)`, hence `|Σ_{n≥1} φ(n u)| ≤ C ζ(2) u`
and `ℰφ(u) = O(u^{3/2})`. This discharges the hypothesis `hdecay` of `Radical.paperFT_Esum_zero`.
-/

noncomputable section

namespace RhWeil
namespace Radical

open Complex MeasureTheory Set Filter Asymptotics Topology Real
open scoped FourierTransform

variable {φ : ℝ → ℂ} {L : ℝ}

/-- Scaling: `𝓕(φ(u ·))(ξ) = u⁻¹ 𝓕φ(ξ/u)`. -/
theorem fourier_comp_mul (φ : ℝ → ℂ) {u : ℝ} (hu : 0 < u) (ξ : ℝ) :
    𝓕 (fun t => φ (u * t)) ξ = (u⁻¹ : ℝ) • 𝓕 φ (ξ / u) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  set g : ℝ → ℂ := fun y => 𝐞 (-(y * (ξ / u))) • φ y
  have : (fun v : ℝ => 𝐞 (-(v * ξ)) • φ (u * v)) = fun v => g (u * v) := by
    funext v; simp only [g]; congr 3; field_simp
  rw [this, Measure.integral_comp_mul_left g u, abs_of_pos (inv_pos.2 hu)]

theorem isBigO_cocompact_of_supp {f : ℝ → ℂ} {R : ℝ} (hf : ∀ t, R < |t| → f t = 0) (b : ℝ) :
    f =O[cocompact ℝ] (|·| ^ (-b)) := by
  refine (EventuallyEq.isBigO ?_).trans (isBigO_zero _ _)
  rw [EventuallyEq, Filter.eventually_iff_exists_mem]
  refine ⟨(Metric.closedBall 0 R)ᶜ, (isCompact_closedBall 0 _).compl_mem_cocompact, fun t ht => ?_⟩
  simp only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at ht
  simpa using hf t ht

theorem norm_fourier_scaled_le {C : ℝ} (hF : ∀ ξ, ‖𝓕 φ ξ‖ ≤ C / ξ ^ 2) {u : ℝ} (hu : 0 < u)
    (ξ : ℝ) : ‖𝓕 (fun t => φ (u * t)) ξ‖ ≤ C * u / ξ ^ 2 := by
  rw [fourier_comp_mul φ hu, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hu)]
  rcases eq_or_ne ξ 0 with rfl | hξ
  · have h := hF 0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero] at h
    have : ‖𝓕 φ (0 / u)‖ = 0 := by rw [zero_div]; exact le_antisymm h (norm_nonneg _)
    rw [this]; simp
  calc u⁻¹ * ‖𝓕 φ (ξ / u)‖ ≤ u⁻¹ * (C / (ξ / u) ^ 2) := by gcongr; exact hF _
    _ = C * u / ξ ^ 2 := by field_simp

theorem summable_int_of_supp {f : ℝ → ℂ} {R : ℝ} (hf : ∀ t, R < |t| → f t = 0) :
    Summable fun n : ℤ => f n := by
  refine summable_of_ne_finset_zero (s := Finset.Icc (-(Nat.ceil R : ℤ)) (Nat.ceil R))
    fun n hn => hf n ?_
  have hc := Nat.le_ceil R
  simp only [Finset.mem_Icc, not_and_or, not_le] at hn
  rcases hn with h | h
  · have : (n : ℝ) < -(Nat.ceil R : ℝ) := by exact_mod_cast h
    have h0 : (0:ℝ) ≤ Nat.ceil R := Nat.cast_nonneg _
    rw [abs_of_neg (by linarith)]; linarith
  · have : (Nat.ceil R : ℝ) < n := by exact_mod_cast h
    have h0 : (0:ℝ) ≤ Nat.ceil R := Nat.cast_nonneg _
    rw [abs_of_pos (by linarith)]; linarith

theorem tsum_int_eq_two_Fsum (heven : ∀ v, φ (-v) = φ v) (h00 : φ 0 = 0) {u : ℝ}
    (hsum : Summable fun n : ℤ => φ (u * n)) :
    ∑' n : ℤ, φ (u * n) = 2 * Fsum φ u := by
  have hinj : Function.Injective (fun n : ℕ => -((n : ℤ) + 1)) := by
    intro a b h
    simp only [neg_inj, add_left_inj, Nat.cast_inj] at h
    exact h
  have hnat : Summable fun n : ℕ => φ (u * ((n : ℤ) : ℝ)) :=
    hsum.comp_injective Nat.cast_injective
  have hneg : Summable fun n : ℕ => φ (u * ((-((n : ℤ) + 1) : ℤ) : ℝ)) :=
    hsum.comp_injective hinj
  rw [tsum_of_nat_of_neg_add_one (f := fun n : ℤ => φ (u * n)) hnat hneg, hnat.tsum_eq_zero_add]
  have e0 : φ (u * (((0 : ℕ) : ℤ) : ℝ)) = 0 := by
    rw [Nat.cast_zero, Int.cast_zero, mul_zero, h00]
  have e1 : ∀ n : ℕ, φ (u * (((n + 1 : ℕ) : ℤ) : ℝ)) = φ (((n : ℝ) + 1) * u) := by
    intro n; congr 1; push_cast; ring
  have e2 : ∀ n : ℕ, φ (u * ((-((n : ℤ) + 1) : ℤ) : ℝ)) = φ (((n : ℝ) + 1) * u) := by
    intro n
    rw [← heven]; congr 1; push_cast; ring
  rw [e0, zero_add, tsum_congr e1, tsum_congr e2, Fsum]
  ring

theorem bound_Fsum (hφc : Continuous φ) (hsupp : ∀ v, L ≤ |v| → φ v = 0)
    (heven : ∀ v, φ (-v) = φ v) (h00 : φ 0 = 0) {C : ℝ} (hF : ∀ ξ, ‖𝓕 φ ξ‖ ≤ C / ξ ^ 2)
    {u : ℝ} (hu : 0 < u) :
    ‖Fsum φ u‖ ≤ C * (∑' m : ℤ, 1 / (m : ℝ) ^ 2) / 2 * u := by
  set f : ℝ → ℂ := fun t => φ (u * t) with hf_def
  have hfc : Continuous f := hφc.comp (continuous_const.mul continuous_id)
  have hsuppf : ∀ t, L / u < |t| → f t = 0 := by
    intro t ht
    apply hsupp
    rw [abs_mul, abs_of_pos hu]
    have := (div_lt_iff₀' hu).1 ht; linarith
  have hfO := isBigO_cocompact_of_supp hsuppf 2
  have hFf := norm_fourier_scaled_le hF hu
  have hC : 0 ≤ C := by
    have h1 := (norm_nonneg _).trans (hF 1); simpa using h1
  have hFfO : (𝓕 f) =O[cocompact ℝ] (|·| ^ (-(2:ℝ))) := by
    refine IsBigO.of_bound (C * u) (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_neg (abs_nonneg _),
      Real.rpow_two, sq_abs, ← div_eq_mul_inv]
    exact hFf ξ
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay hfc (by norm_num : (1:ℝ) < 2) hfO hFfO 0
  simp only [zero_add, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] at hP
  have hsum1 : Summable fun m : ℤ => C * u * (1 / (m : ℝ) ^ 2) :=
    (summable_one_div_int_pow.2 (by norm_num : 1 < 2)).mul_left (C * u)
  have hle : ∀ m : ℤ, ‖𝓕 f m‖ ≤ C * u * (1 / (m : ℝ) ^ 2) := fun m => by
    have h1 := hFf m; rwa [div_eq_mul_one_div] at h1
  have hsumF : Summable fun m : ℤ => ‖𝓕 f m‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsum1
  have hZ := tsum_int_eq_two_Fsum heven h00 (summable_int_of_supp hsuppf)
  have key : ‖2 * Fsum φ u‖ ≤ C * u * ∑' m : ℤ, 1 / (m : ℝ) ^ 2 := by
    rw [← hZ]
    change ‖∑' n : ℤ, f n‖ ≤ _
    rw [hP, ← tsum_mul_left]
    exact (norm_tsum_le_tsum_norm hsumF).trans (hsumF.tsum_le_tsum hle hsum1)
  rw [norm_mul, Complex.norm_two] at key
  calc ‖Fsum φ u‖ = (2 * ‖Fsum φ u‖) / 2 := by ring
    _ ≤ (C * u * ∑' m : ℤ, 1 / (m : ℝ) ^ 2) / 2 := by gcongr
    _ = C * (∑' m : ℤ, 1 / (m : ℝ) ^ 2) / 2 * u := by ring

/-- **`hdecay`**: `ℰφ(u) = O(u^{3/2})` as `u → 0⁺`. -/
theorem Esum_isBigO (hφc : Continuous φ) (hsupp : ∀ v, L ≤ |v| → φ v = 0)
    (heven : ∀ v, φ (-v) = φ v) (h00 : φ 0 = 0) {C : ℝ} (hF : ∀ ξ, ‖𝓕 φ ξ‖ ≤ C / ξ ^ 2) :
    Esum φ =O[𝓝[>] 0] (fun u : ℝ => u ^ (3 / 2 : ℝ)) := by
  set K := C * (∑' m : ℤ, 1 / (m : ℝ) ^ 2) / 2
  refine IsBigO.of_bound K ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu' : (0:ℝ) < u := hu
  have hb := bound_Fsum hφc hsupp heven h00 hF hu'
  rw [Esum, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hu' _)]
  have hn : ‖(u : ℂ) ^ (1 / 2 : ℂ)‖ = u ^ (1 / 2 : ℝ) := by
    have h2 : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
    rw [norm_cpow_eq_rpow_re_of_pos hu', h2]
  rw [hn]
  have : u ^ (3 / 2 : ℝ) = u ^ (1 / 2 : ℝ) * u := by
    rw [← Real.rpow_add_one hu'.ne']; norm_num
  rw [this]
  calc u ^ (1 / 2 : ℝ) * ‖Fsum φ u‖ ≤ u ^ (1 / 2 : ℝ) * (K * u) := by gcongr
    _ = K * (u ^ (1 / 2 : ℝ) * u) := by ring

/-- **Radical lemma, hypotheses on `φ` only.** Let `φ` be continuous, even, supported in `[-L, L]`,
with `φ(0) = 0`, `φ(v) = O(v²)` at `0⁺`, and `|𝓕φ(ξ)| ≤ C/ξ²`. Then `e = ℰφ ∘ exp` satisfies
`ê(±γ_ρ) = 0` for every non-trivial zero `ρ` of `ζ`. -/
theorem paperFT_Esum_zero' (hφc : Continuous φ) (hsupp : ∀ v, L ≤ |v| → φ v = 0)
    (heven : ∀ v, φ (-v) = φ v) (h00 : φ 0 = 0) {C : ℝ} (hF : ∀ ξ, ‖𝓕 φ ξ‖ ≤ C / ξ ^ 2)
    (hφ0 : φ =O[𝓝[>] 0] (fun v : ℝ => v ^ (2 : ℝ)))
    {ρ : ℂ} (hρ : Zeta23.IsNontrivialZero ρ) :
    Zeta23.paperFT (fun y => Esum φ (Real.exp y)) (Zeta23.gammaOf ρ) = 0 ∧
    Zeta23.paperFT (fun y => Esum φ (Real.exp y)) (-Zeta23.gammaOf ρ) = 0 :=
  paperFT_Esum_zero hφc (fun v hv => hsupp v (hv.trans (le_abs_self v))) hφ0
    (Esum_isBigO hφc hsupp heven h00 hF) hρ

end Radical
end RhWeil
