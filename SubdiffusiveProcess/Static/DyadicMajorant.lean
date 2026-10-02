import SubdiffusiveProcess.Probability.CountableEnvelope
import SubdiffusiveProcess.Static.CutoffMassMomentBound
import Mathlib.Analysis.SpecificLimits.Normed

/-! # One measurable constant for a finite family of dyadic cube sequences

There are at most `p * (2^n+1)` estimates at level `n`. Discounting their
absolute sum by `4^(-n)` is summable in every prescribed finite `Lᵖ` space.
The resulting simultaneous factor grows by `2^(2n)`, below the fixed exponent
five used for the static estimates.
-/

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section
namespace SubdiffusiveProcess.Static

private theorem dyadic_discount_card (n : ℕ) :
    (1 / 4 : ℝ) ^ n * ((2 : ℝ) ^ n + 1) =
      (1 / 2 : ℝ) ^ n + (1 / 4 : ℝ) ^ n := by
  rw [mul_add, ← mul_pow, mul_one]
  norm_num

private theorem eLpNorm_finite_sum_le_uniform {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] (μ : Measure Ω) {q : ℝ≥0∞} (hq : 1 ≤ q) {B : ℝ} (hB : 0 ≤ B)
    (Z : ι → Ω → ℝ) (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hnorm : ∀ i, eLpNorm (Z i) q μ ≤ ENNReal.ofReal B) :
    eLpNorm (fun ω => ∑ i, Z i ω) q μ ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * B) := by
  classical
  have htriangle : eLpNorm (∑ i : ι, Z i) q μ ≤ ∑ i : ι, eLpNorm (Z i) q μ :=
    eLpNorm_sum_le (f := Z) (s := Finset.univ) (μ := μ) (p := q) (fun i _ => hZ i) hq
  have heq : (fun ω => ∑ i : ι, Z i ω) = ∑ i : ι, Z i := by
    funext ω
    rw [Finset.sum_apply]
  rw [heq]
  refine htriangle.trans ?_
  calc
    ∑ i, eLpNorm (Z i) q μ ≤ ∑ _i : ι, ENNReal.ofReal B :=
      Finset.sum_le_sum fun i _ => hnorm i
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

private theorem dyadic_weighted_bank_norm_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p n : ℕ) {q : ℝ≥0∞} (hq : 1 ≤ q) {B : ℝ} (hB : 0 ≤ B)
    (Z : Fin p → Fin (2 ^ n + 1) → Ω → ℝ)
    (hZ : ∀ i k, AEStronglyMeasurable (Z i k) μ)
    (hnorm : ∀ i k, eLpNorm (Z i k) q μ ≤ ENNReal.ofReal B) :
    eLpNorm (fun ω => (1 / 4 : ℝ) ^ n * ∑ i, ∑ k, |Z i k ω|) q μ ≤
      ENNReal.ofReal ((p : ℝ) * B * ((1 / 2 : ℝ) ^ n + (1 / 4 : ℝ) ^ n)) := by
  have hinner : ∀ i : Fin p, eLpNorm (fun ω => ∑ k : Fin (2 ^ n + 1), |Z i k ω|) q μ ≤
      ENNReal.ofReal (((2 ^ n + 1 : ℕ) : ℝ) * B) := by
    intro i
    have hnormabs : ∀ k, eLpNorm (fun ω => |Z i k ω|) q μ ≤ ENNReal.ofReal B :=
      fun k => (show eLpNorm (fun ω => |Z i k ω|) q μ = eLpNorm (Z i k) q μ from
        eLpNorm_norm (Z i k)).trans_le (hnorm i k)
    simpa only [Fintype.card_fin] using eLpNorm_finite_sum_le_uniform μ hq hB
      (fun k ω => |Z i k ω|) (fun k => (hZ i k).norm) hnormabs
  have houter := eLpNorm_finite_sum_le_uniform μ hq
    (by positivity : 0 ≤ (((2 ^ n + 1 : ℕ) : ℝ) * B))
    (fun i ω => ∑ k : Fin (2 ^ n + 1), |Z i k ω|)
    (fun i => Finset.aestronglyMeasurable_fun_sum Finset.univ fun k _ => (hZ i k).norm)
    hinner
  change eLpNorm (((1 / 4 : ℝ) ^ n) • (fun ω => ∑ i, ∑ k, |Z i k ω|)) q μ ≤ _
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity : 0 ≤ (1 / 4 : ℝ) ^ n)]
  refine (mul_le_mul_right houter _).trans_eq ?_
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (1 / 4 : ℝ) ^ n)]
  congr 1
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  calc
    (1 / 4 : ℝ) ^ n * ((p : ℝ) * (((2 : ℝ) ^ n + 1) * B)) =
        ((p : ℝ) * B) * ((1 / 4 : ℝ) ^ n * ((2 : ℝ) ^ n + 1)) := by ring
    _ = _ := by rw [dyadic_discount_card]

/-- Uniform moments of individual dyadic estimates yield one everywhere
measurable constant at least one. Its moment bound and dyadic exponent are
independent of the field or any cutoff index. -/
theorem exists_dyadic_majorant {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ℕ) {q B : ℝ}
    (hq : 1 ≤ q) (hB : 0 ≤ B)
    (Z : ∀ n : ℕ, Fin p → Fin (2 ^ n + 1) → Ω → ℝ)
    (hZ : ∀ n i k, AEStronglyMeasurable (Z n i k) μ)
    (hnorm : ∀ n i k, eLpNorm (Z n i k) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B) :
    ∃ K : Ω → ℝ, Measurable K ∧ (∀ ω, 1 ≤ K ω) ∧
      (∫⁻ ω, ENNReal.ofReal (K ω ^ q) ∂μ) ≤
        ENNReal.ofReal ((1 + 4 * (p : ℝ) * B) ^ q) ∧
      ∀ᵐ ω ∂μ, ∀ n : ℕ, ∀ i : Fin p, ∀ k : Fin (2 ^ n + 1),
        |Z n i k ω| ≤ K ω * (2 : ℝ) ^ (2 * n) := by
  classical
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.mpr hq
  let F : ℕ → Ω → ℝ := fun n ω =>
    (1 / 4 : ℝ) ^ n * ∑ i : Fin p, ∑ k : Fin (2 ^ n + 1), |Z n i k ω|
  let a : ℕ → ℝ := fun n => (p : ℝ) * B * ((1 / 2 : ℝ) ^ n + (1 / 4 : ℝ) ^ n)
  have ha0 : ∀ n, 0 ≤ a n := fun n => by dsimp only [a]; positivity
  have hameas : ∀ n, AEStronglyMeasurable (F n) μ := fun n =>
    (Finset.aestronglyMeasurable_fun_sum Finset.univ fun i _ =>
      Finset.aestronglyMeasurable_fun_sum Finset.univ fun k _ =>
        (hZ n i k).norm).const_mul _
  have hFnorm : ∀ n, eLpNorm (F n) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (a n) :=
    fun n => dyadic_weighted_bank_norm_le μ p n hp hB (Z n) (hZ n) (hnorm n)
  have hFmem : ∀ n, MemLp (F n) (ENNReal.ofReal q) μ := fun n =>
    ⟨hameas n, (hFnorm n).trans_lt ENNReal.ofReal_lt_top⟩
  have hhalf : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  have hquarter : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  have hasum : Summable a := (hhalf.add hquarter).mul_left ((p : ℝ) * B)
  have hsum_norm : Summable (fun n => (eLpNorm (F n) (ENNReal.ofReal q) μ).toReal) := by
    apply Summable.of_nonneg_of_le (fun n => ENNReal.toReal_nonneg) _ hasum
    intro n
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hFnorm n)).trans_eq
      (ENNReal.toReal_ofReal (ha0 n))
  have hsum_bound : (∑' n, a n) ≤ 4 * (p : ℝ) * B := by
    change (∑' n : ℕ, (p : ℝ) * B * ((1 / 2 : ℝ) ^ n + (1 / 4 : ℝ) ^ n)) ≤ _
    rw [tsum_mul_left, hhalf.tsum_add hquarter,
      tsum_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1),
      tsum_geometric_of_abs_lt_one (by norm_num : |(1 / 4 : ℝ)| < 1)]
    norm_num
    nlinarith
  obtain ⟨W, hWmem, hWdom, hWnorm⟩ :=
    SubdiffusiveProcess.exists_memLp_dominating_of_summable_eLpNorm
      μ hp ENNReal.ofReal_ne_top F hFmem hsum_norm
  have hWbound : eLpNorm W (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (4 * (p : ℝ) * B) := by
    refine hWnorm.trans ((ENNReal.tsum_le_tsum hFnorm).trans ?_)
    rw [← ENNReal.ofReal_tsum_of_nonneg ha0 hasum]
    exact ENNReal.ofReal_le_ofReal hsum_bound
  let K : Ω → ℝ := fun ω => 1 + |hWmem.1.mk W ω|
  have hKmeas : Measurable K := measurable_const.add
    (hWmem.1.stronglyMeasurable_mk.measurable.norm)
  have hKone : ∀ ω, 1 ≤ K ω := fun ω => le_add_of_nonneg_right (abs_nonneg _)
  have hKbound : eLpNorm K (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (1 + 4 * (p : ℝ) * B) := by
    have hmk : (fun ω => |hWmem.1.mk W ω|) =ᵐ[μ] fun ω => |W ω| :=
      hWmem.1.ae_eq_mk.symm.fun_comp abs
    refine (eLpNorm_add_le aestronglyMeasurable_const
      (hWmem.1.stronglyMeasurable_mk.aestronglyMeasurable.norm) hp).trans ?_
    have hconst : eLpNorm (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal q) μ = 1 := by
      rw [eLpNorm_const _ (ENNReal.ofReal_pos.mpr hq0).ne' (NeZero.ne μ)]
      simp only [measure_univ, ENNReal.one_rpow, mul_one, enorm_one]
    rw [hconst]
    change 1 + eLpNorm (fun ω => |hWmem.1.mk W ω|) (ENNReal.ofReal q) μ ≤ _
    rw [eLpNorm_congr_ae hmk]
    simp only [← Real.norm_eq_abs, eLpNorm_norm]
    refine (add_le_add le_rfl hWbound).trans_eq ?_
    rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_one]
  have hmoment : (∫⁻ ω, ENNReal.ofReal (K ω ^ q) ∂μ) ≤
      ENNReal.ofReal ((1 + 4 * (p : ℝ) * B) ^ q) := by
    rw [SubdiffusiveProcess.Static.lintegral_rpow_eq_eLpNorm_rpow μ K
      (fun ω => zero_le_one.trans (hKone ω)) hq0]
    exact (ENNReal.rpow_le_rpow hKbound hq0.le).trans_eq
      (ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le)
  refine ⟨K, hKmeas, hKone, hmoment, ?_⟩
  filter_upwards [hWdom, hWmem.1.ae_eq_mk] with ω hω hmk
  intro n i k
  have hterm : |Z n i k ω| ≤ ∑ j : Fin p, ∑ l : Fin (2 ^ n + 1), |Z n j l ω| := by
    have hkbound : |Z n i k ω| ≤ ∑ l : Fin (2 ^ n + 1), |Z n i l ω| :=
      Finset.single_le_sum (f := fun l : Fin (2 ^ n + 1) => |Z n i l ω|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    have hibound : (∑ l : Fin (2 ^ n + 1), |Z n i l ω|) ≤
        ∑ j : Fin p, ∑ l : Fin (2 ^ n + 1), |Z n j l ω| :=
      Finset.single_le_sum (f := fun j : Fin p => ∑ l : Fin (2 ^ n + 1), |Z n j l ω|)
        (fun j _ => Finset.sum_nonneg fun l _ => abs_nonneg _) (Finset.mem_univ i)
    exact hkbound.trans hibound
  have hw : (1 / 4 : ℝ) ^ n * |Z n i k ω| ≤ K ω := by
    refine (mul_le_mul_of_nonneg_left hterm (by positivity)).trans ?_
    change F n ω ≤ K ω
    refine ((le_abs_self _).trans (hω.2 n)).trans ?_
    dsimp only [K]
    rw [← hmk]
    exact (le_abs_self _).trans (le_add_of_nonneg_left zero_le_one)
  have hcancel : (1 / 4 : ℝ) ^ n * (2 : ℝ) ^ (2 * n) = 1 := by
    rw [pow_mul, ← mul_pow]
    norm_num
  apply (mul_le_mul_iff_of_pos_left (by positivity : 0 < (1 / 4 : ℝ) ^ n)).mp
  have hscaled : (1 / 4 : ℝ) ^ n * (K ω * (2 : ℝ) ^ (2 * n)) = K ω := by
    calc
      _ = K ω * ((1 / 4 : ℝ) ^ n * (2 : ℝ) ^ (2 * n)) := by ring
      _ = _ := by rw [hcancel, mul_one]
  rw [hscaled]
  exact hw

end SubdiffusiveProcess.Static
