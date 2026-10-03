module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Probability.GrowingMeshEnvelope
public import SubdiffusiveProcess.Paper.lane4_cell_maximum_moment
public import SubdiffusiveProcess.Paper.lane4_weighted_cell_summation
public import SubdiffusiveProcess.Paper.lane4_weighted_minkowski
public import SubdiffusiveProcess.Paper.lem_extension_cell_moment
public import SubdiffusiveProcess.Paper.lem_extension_grid_cardinality

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open Filter
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem lem_extension_grid_assembly :
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d J : ℕ) (eta p q : ℝ), 0 < eta → 1 ≤ p → p ≤ q →
      q * eta > (d : ℝ) →
    ∀ (admissible : ℕ → Fin J → (Fin d → ℤ) → Prop)
      (F : ℕ → ℕ → Fin J → (Fin d → ℤ) → Ω → ℝ)
      (Cgrid : ℕ) (Ccell growth : ℝ),
      0 ≤ Ccell → 0 ≤ growth →
      growth < (eta - (d : ℝ) / q) * Real.log 3 →
      (∀ (k : ℕ) (index : Fin J),
        ∃ S : Finset (Fin d → ℤ),
          (∀ nidx, nidx ∈ S ↔ admissible k index nidx) ∧
          S.card ≤ Cgrid * 3 ^ (d * k)) →
      (∀ (N k : ℕ) (index : Fin J) (nidx : Fin d → ℤ), k ≤ N →
        admissible k index nidx →
        AEStronglyMeasurable (F N k index nidx) μ) →
      (∀ (N k : ℕ) (index : Fin J) (nidx : Fin d → ℤ), k ≤ N →
        admissible k index nidx →
        eLpNorm (F N k index nidx) (ENNReal.ofReal q) μ ≤
          ENNReal.ofReal (Ccell * Real.exp (growth * (k : ℝ)))) →
    ∃ (K : ℕ → Ω → ℝ) (Cbound : ℝ),
      (∀ N, MemLp (K N) (ENNReal.ofReal p) μ) ∧
      (∀ N, eLpNorm (K N) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal Cbound) ∧
      ∀ᵐ om ∂μ,
        ∀ (N k : ℕ) (index : Fin J) (nidx : Fin d → ℤ), k ≤ N →
          admissible k index nidx →
          F N k index nidx om ≤
            K N om * ((3 : ℝ) ^ (-(k : ℤ))) ^ (-eta) := by
  classical
  intro Ω mΩ μ hμ d J eta p q heta hp hpq hqeta admissible F Cgrid Ccell growth
    hCcell hgrowth hmargin hcard hmeas hmoment
  have hqpos : 0 < q := by
    nlinarith [hqeta]
  have hq1 : 1 ≤ q := le_trans hp hpq
  have hlog : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hqeta' : (d : ℝ) < q * (eta - growth / Real.log 3) := by
    have htmp : growth / Real.log 3 < eta - (d : ℝ) / q :=
      (div_lt_iff₀ hlog).2 hmargin
    have htmp' : (d : ℝ) / q < eta - growth / Real.log 3 := by
      linarith
    have htmp'' := (div_lt_iff₀ hqpos).mp htmp'
    simpa [mul_comm] using htmp''
  have hgap_grow :
      (d : ℝ) * Real.log 3 + (ENNReal.ofReal q).toReal * growth <
        (ENNReal.ofReal q).toReal * eta * Real.log 3 := by
    rw [ENNReal.toReal_ofReal hqpos.le]
    calc
      (d : ℝ) * Real.log 3 + q * growth <
          (d : ℝ) * Real.log 3 + q * ((eta - (d : ℝ) / q) * Real.log 3) := by
            simpa [add_comm] using
              (add_lt_add_right (mul_lt_mul_of_pos_left hmargin hqpos)
                ((d : ℝ) * Real.log 3))
      _ = q * eta * Real.log 3 := by
        field_simp [ne_of_gt hqpos]
        ring
  choose S hS_spec using hcard
  let m : ℕ → ℕ := fun k => Cgrid * 3 ^ (d * k)
  have hmcard : ∀ n : ℕ, (m n : ℝ) ≤
      (Cgrid : ℝ) * ((n : ℝ) + 1) ^ (0 : ℕ) *
        (3 : ℝ) ^ ((d : ℝ) * (n : ℝ)) := by
    intro n
    dsimp [m]
    rw [Nat.cast_mul, Nat.cast_pow]
    rw [show (d : ℝ) * (n : ℝ) = ((d * n : ℕ) : ℝ) by norm_num]
    rw [Real.rpow_natCast]
    norm_num
  let Kq : ℝ≥0∞ := ENNReal.ofReal Ccell
  let H : ℝ≥0∞ := ∑' n : ℕ,
      ENNReal.ofReal (Real.exp (growth * (n : ℝ)) *
        (3 : ℝ) ^ (-eta * (n : ℝ))) *
        (m n : ℝ≥0∞) ^ (1 / (ENNReal.ofReal q).toReal)
  let htermReal : ℕ → ℝ := fun n =>
      Real.exp (growth * (n : ℝ)) * (3 : ℝ) ^ (-eta * (n : ℝ)) *
        (m n : ℝ) ^ (1 / q)
  have hseries : Summable htermReal := by
    have hs := SubdiffusiveProcess.summable_triadic_mesh_cardinality
      m d 0 Cgrid q (eta - growth / Real.log 3) (by positivity) hq1 hqeta' hmcard
    apply hs.congr
    intro n
    dsimp [htermReal]
    have heq : Real.exp (growth * (n : ℝ)) *
        (3 : ℝ) ^ (-eta * (n : ℝ)) =
          (3 : ℝ) ^ (-(eta - growth / Real.log 3) * (n : ℝ)) := by
      rw [Real.rpow_def_of_pos (by norm_num),
        Real.rpow_def_of_pos (by norm_num), ← Real.exp_add]
      congr 1
      field_simp [ne_of_gt hlog]
      ring
    rw [heq]
  have hterm_nonneg : ∀ n, 0 ≤ htermReal n := by
    intro n
    dsimp [htermReal]
    positivity
  have hterm_enn : ∀ (n : ℕ), ENNReal.ofReal (Real.exp (growth * (n : ℝ)) *
        (3 : ℝ) ^ (-eta * (n : ℝ))) *
        (m n : ℝ≥0∞) ^ (1 / (ENNReal.ofReal q).toReal) =
      ENNReal.ofReal (htermReal n) := by
    intro n
    have hqto : (ENNReal.ofReal q).toReal = q :=
      ENNReal.toReal_ofReal hqpos.le
    have hmto : (m n : ℝ≥0∞) = ENNReal.ofReal (m n : ℝ) := by
      norm_num
    rw [hqto, hmto, ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _) (by positivity)]
    rw [← ENNReal.ofReal_mul (by positivity)]
  have hH : H = ENNReal.ofReal (∑' n, htermReal n) := by
    dsimp [H]
    calc
      (∑' n : ℕ,
          ENNReal.ofReal (Real.exp (growth * (n : ℝ)) *
            (3 : ℝ) ^ (-eta * (n : ℝ))) *
            (m n : ℝ≥0∞) ^ (1 / (ENNReal.ofReal q).toReal)) =
          ∑' n : ℕ, ENNReal.ofReal (htermReal n) :=
            tsum_congr hterm_enn
      _ = ENNReal.ofReal (∑' n, htermReal n) :=
        (ENNReal.ofReal_tsum_of_nonneg hterm_nonneg hseries).symm
  have hHtop : H ≠ ⊤ := by
    rw [hH]
    exact ENNReal.ofReal_ne_top
  have htotal : H * Kq ≠ ⊤ := by
    exact ENNReal.mul_ne_top hHtop (by simp [Kq])
  let Z : ℕ → Fin J → (n : ℕ) → Fin (m n) → Ω → ℝ := fun N index n i om =>
    if hn : n ≤ N then
      if hi : i.val < (S n index).card then
        F N n index ((S n index).equivFin.symm ⟨i.val, hi⟩) om
      else 0
    else 0
  have hZ : ∀ (N : ℕ) (index : Fin J) (n : ℕ) (i : Fin (m n)),
      AEStronglyMeasurable (Z N index n i) μ := by
    intro N index n i
    by_cases hn : n ≤ N
    · by_cases hi : i.val < (S n index).card
      · simp only [Z, dif_pos hn, dif_pos hi]
        apply hmeas N n index _ hn
        exact ((hS_spec n index).1 _).mp
          ((S n index).equivFin.symm ⟨i.val, hi⟩).property
      · simpa [Z, hn, hi] using
          (stronglyMeasurable_const.aestronglyMeasurable :
            AEStronglyMeasurable (fun _ : Ω => (0 : ℝ)) μ)
    · simpa [Z, hn] using
        (stronglyMeasurable_const.aestronglyMeasurable :
          AEStronglyMeasurable (fun _ : Ω => (0 : ℝ)) μ)
  have hK : ∀ (N : ℕ) (index : Fin J) (n : ℕ) (i : Fin (m n)),
      eLpNorm (Z N index n i) (ENNReal.ofReal q) μ ≤
        Kq * ENNReal.ofReal (Real.exp (growth * (n : ℝ))) := by
    intro N index n i
    by_cases hn : n ≤ N
    · by_cases hi : i.val < (S n index).card
      · have hadm : admissible n index
            ((S n index).equivFin.symm ⟨i.val, hi⟩) :=
          ((hS_spec n index).1 _).mp
            ((S n index).equivFin.symm ⟨i.val, hi⟩).property
        have hFbound := hmoment N n index
          ((S n index).equivFin.symm ⟨i.val, hi⟩) hn hadm
        calc
          eLpNorm (Z N index n i) (ENNReal.ofReal q) μ =
              eLpNorm (F N n index
                ((S n index).equivFin.symm ⟨i.val, hi⟩))
                (ENNReal.ofReal q) μ := by simp [Z, hn, hi]
          _ ≤ ENNReal.ofReal (Ccell * Real.exp (growth * (n : ℝ))) := hFbound
          _ = Kq * ENNReal.ofReal (Real.exp (growth * (n : ℝ))) := by
            rw [ENNReal.ofReal_mul hCcell]
      · simp [Z, hn, hi, Kq]
    · simp [Z, hn, Kq]
  have henv : ∀ (N : ℕ) (index : Fin J), ∃ W : Ω → ℝ,
      MemLp W (ENNReal.ofReal p) μ ∧
        (∀ᵐ om ∂μ, 0 ≤ W om ∧ ∀ (n : ℕ) (i : Fin (m n)),
          |Z N index n i om| ≤ W om * (3 : ℝ) ^ (eta * (n : ℝ))) ∧
        eLpNorm W (ENNReal.ofReal p) μ ≤ H * Kq := by
    intro N index
    obtain ⟨W, hW, hWae, hWnorm⟩ :=
      SubdiffusiveProcess.exists_triadic_mesh_envelope_of_exponential_growth
        μ m d 0 (Cgrid : ℝ) eta growth (by positivity) hgrowth
        (by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal hp)
        (ENNReal.ofReal_le_ofReal hpq) (by simp) hgap_grow hmcard
        (Z N index) (hZ N index) Kq (by simp [Kq]) (hK N index)
    refine ⟨W, hW, hWae, ?_⟩
    simpa [H, Kq] using hWnorm
  choose W hW using henv
  let K : ℕ → Ω → ℝ := fun N om => ∑ i : Fin J, W N i om
  have hK_eq : ∀ N, K N = ∑ i : Fin J, W N i := by
    intro N
    funext om
    simp [K]
  have hKmem : ∀ N, MemLp (K N) (ENNReal.ofReal p) μ := by
    intro N
    rw [hK_eq N]
    exact memLp_finset_sum' (p := ENNReal.ofReal p) (μ := μ)
      (Finset.univ : Finset (Fin J)) (fun i hi => (hW N i).1)
  have hKnorm : ∀ N, eLpNorm (K N) (ENNReal.ofReal p) μ ≤
      (J : ℝ≥0∞) * (H * Kq) := by
    intro N
    rw [hK_eq N]
    calc
      eLpNorm (∑ i : Fin J, W N i) (ENNReal.ofReal p) μ ≤
          ∑ i : Fin J, eLpNorm (W N i) (ENNReal.ofReal p) μ := by
            apply eLpNorm_sum_le
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal hp
      _ ≤ ∑ _i : Fin J, H * Kq := by
        gcongr
        exact (hW N _).2.2
      _ = (J : ℝ≥0∞) * (H * Kq) := by simp
  let Cbound : ℝ := ((J : ℝ≥0∞) * (H * Kq)).toReal
  have hCbound : ENNReal.ofReal Cbound = (J : ℝ≥0∞) * (H * Kq) := by
    dsimp [Cbound]
    exact ENNReal.ofReal_toReal (by
      exact ENNReal.mul_ne_top (by simp) htotal)
  have hdom : ∀ᵐ om ∂μ, ∀ (N : ℕ) (index : Fin J),
      0 ≤ W N index om ∧ ∀ (n : ℕ) (i : Fin (m n)),
        |Z N index n i om| ≤ W N index om * (3 : ℝ) ^ (eta * (n : ℝ)) := by
    apply ae_all_iff.2
    intro N
    apply ae_all_iff.2
    intro index
    exact (hW N index).2.1
  refine ⟨K, Cbound, hKmem, ?_, ?_⟩
  · intro N
    exact (hKnorm N).trans_eq hCbound.symm
  · filter_upwards [hdom] with om hω
    intro N k index nidx hk hadm
    have hnmem : nidx ∈ S k index := ((hS_spec k index).1 nidx).mpr hadm
    let i0 : Fin (S k index).card := (S k index).equivFin ⟨nidx, hnmem⟩
    have hi0 : i0.val < (m k) := by
      exact lt_of_lt_of_le i0.isLt ((hS_spec k index).2.trans_eq (by rfl))
    let i : Fin (m k) := ⟨i0.val, hi0⟩
    have hsub : (⟨i.val, (show i.val < (S k index).card by simpa [i, i0])⟩ :
        Fin (S k index).card) = i0 := by
      apply Fin.ext
      rfl
    have hget : ((S k index).equivFin.symm
        ⟨i.val, (show i.val < (S k index).card by simpa [i, i0])⟩).val = nidx := by
      rw [hsub]
      exact congrArg Subtype.val
        ((S k index).equivFin.symm_apply_apply ⟨nidx, hnmem⟩)
    have hFi : |F N k index nidx om| ≤
        W N index om * (3 : ℝ) ^ (eta * (k : ℝ)) := by
      simpa [Z, hk, i, i0, hget] using (hω N index).2 k i
    have hWle : W N index om ≤ K N om := by
      dsimp [K]
      exact Finset.single_le_sum
        (fun j _ => (hω N j).1) (Finset.mem_univ index)
    have hpow : 0 ≤ (3 : ℝ) ^ (eta * (k : ℝ)) := by positivity
    have hsum : W N index om * (3 : ℝ) ^ (eta * (k : ℝ)) ≤
        K N om * (3 : ℝ) ^ (eta * (k : ℝ)) :=
      mul_le_mul_of_nonneg_right hWle hpow
    have hfactor : ((3 : ℝ) ^ (-(k : ℤ))) ^ (-eta) =
        (3 : ℝ) ^ (eta * (k : ℝ)) := by
      rw [zpow_neg, zpow_natCast]
      rw [Real.rpow_def_of_pos (by positivity)]
      rw [Real.log_inv, Real.log_pow]
      rw [Real.rpow_def_of_pos (by norm_num)]
      congr 1
      ring
    calc
      F N k index nidx om ≤ |F N k index nidx om| := le_abs_self _
      _ ≤ W N index om * (3 : ℝ) ^ (eta * (k : ℝ)) := hFi
      _ ≤ K N om * (3 : ℝ) ^ (eta * (k : ℝ)) := hsum
      _ = K N om * ((3 : ℝ) ^ (-(k : ℤ))) ^ (-eta) := by rw [hfactor]

end Paper
