import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.ChaosSampleLaw
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section
namespace Paper

theorem aux_lem_finite_stopping_moments_markov
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p B t : ℝ) (hp : 1 ≤ p) (ht : 0 < t)
    (f : α → ℝ) (hf : MemLp f (ENNReal.ofReal p) μ)
    (hbound : eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal B)
    (hB : 0 ≤ B) :
    ∃ Bad : Set α, MeasurableSet Bad ∧
      {x | t ≤ |f x|} ⊆ Bad ∧
        μ Bad ≤ ENNReal.ofReal (B ^ p * t ^ (-p)) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq0 : ENNReal.ofReal p ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hp0).ne'
  have hqt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hqreal : (ENNReal.ofReal p).toReal = p :=
    ENNReal.toReal_ofReal hp0.le
  have ht0 : 0 ≤ t := ht.le
  have hmark :
      μ {x | ENNReal.ofReal t ≤ ‖f x‖ₑ} ≤
        (ENNReal.ofReal t)⁻¹ ^ (ENNReal.ofReal p).toReal *
          eLpNorm f (ENNReal.ofReal p) μ ^ (ENNReal.ofReal p).toReal :=
    MeasureTheory.meas_ge_le_mul_pow_eLpNorm_enorm μ hq0 hqt
      hf.aestronglyMeasurable (by
        exact (ENNReal.ofReal_pos.mpr ht).ne') (by simp)
  have hpow :
      eLpNorm f (ENNReal.ofReal p) μ ^ (ENNReal.ofReal p).toReal ≤
        ENNReal.ofReal (B ^ p) := by
    calc
      eLpNorm f (ENNReal.ofReal p) μ ^ (ENNReal.ofReal p).toReal ≤
          ENNReal.ofReal B ^ (ENNReal.ofReal p).toReal := by
            exact ENNReal.rpow_le_rpow hbound ENNReal.toReal_nonneg
      _ = ENNReal.ofReal (B ^ p) := by
        rw [hqreal, ENNReal.ofReal_rpow_of_nonneg hB hp0.le]
  have hthreshold :
      (ENNReal.ofReal t)⁻¹ ^ (ENNReal.ofReal p).toReal =
        ENNReal.ofReal (t ^ (-p)) := by
    rw [hqreal, ← ENNReal.ofReal_inv_of_pos ht,
      ENNReal.ofReal_rpow_of_pos (inv_pos.mpr ht),
      ← Real.rpow_neg_eq_inv_rpow]
  have hbound' :
      (ENNReal.ofReal t)⁻¹ ^ (ENNReal.ofReal p).toReal *
          eLpNorm f (ENNReal.ofReal p) μ ^ (ENNReal.ofReal p).toReal ≤
        ENNReal.ofReal (B ^ p * t ^ (-p)) := by
    calc
      (ENNReal.ofReal t)⁻¹ ^ (ENNReal.ofReal p).toReal *
            eLpNorm f (ENNReal.ofReal p) μ ^ (ENNReal.ofReal p).toReal =
          ENNReal.ofReal (t ^ (-p)) *
            eLpNorm f (ENNReal.ofReal p) μ ^ (ENNReal.ofReal p).toReal := by
              rw [hthreshold]
      _ ≤ ENNReal.ofReal (t ^ (-p)) * ENNReal.ofReal (B ^ p) := by
            gcongr
      _ = ENNReal.ofReal (B ^ p * t ^ (-p)) := by
            rw [mul_comm, ← ENNReal.ofReal_mul (Real.rpow_nonneg hB _)]
  let E : Set α := {x | t ≤ |f x|}
  have hE : E = {x | ENNReal.ofReal t ≤ ‖f x‖ₑ} := by
    ext x
    change t ≤ |f x| ↔ ENNReal.ofReal t ≤ ‖f x‖ₑ
    rw [ENNReal.ofReal_eq_coe_nnreal ht0, enorm_eq_nnnorm, ENNReal.coe_le_coe]
    change t ≤ ‖f x‖₊.val ↔ t ≤ |f x|
    simp [Real.norm_eq_abs]
  have hmeasureE : μ E ≤ ENNReal.ofReal (B ^ p * t ^ (-p)) := by
    rw [hE]
    exact hmark.trans hbound'
  refine ⟨toMeasurable μ E, measurableSet_toMeasurable _ _,
    subset_toMeasurable _ _, ?_⟩
  rw [measure_toMeasurable]
  exact hmeasureE

theorem aux_lem_finite_stopping_moments_sum
    (m : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (∑ _i : Fin m, (ENNReal.ofReal r + ENNReal.ofReal r)) =
      ENNReal.ofReal ((2 : ℝ) * (m : ℝ) * r) := by
  calc
    (∑ i : Fin m, (ENNReal.ofReal r + ENNReal.ofReal r)) =
        ∑ _i : Fin m, ENNReal.ofReal (r + r) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [ENNReal.ofReal_add hr hr]
    _ = (m : ℝ≥0∞) * ENNReal.ofReal (r + r) := by
          simp [nsmul_eq_mul]
    _ = ENNReal.ofReal ((2 : ℝ) * (m : ℝ) * r) := by
          rw [← ENNReal.ofReal_natCast m,
            ← ENNReal.ofReal_mul (show 0 ≤ (m : ℝ) from by positivity)]
          congr 1
          ring



theorem lem_finite_stopping_moments
    (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (m : ℕ) (p Cbank : ℝ) (hp : 1 ≤ p)
    (K : Fin m → ℕ → BilateralField d → ℝ)
    (hmoment : ∀ i J, MemLp (K i J) (ENNReal.ofReal p)
      (chaosSampleLaw model).toMeasure)
    (hbound : ∀ i J, eLpNorm (K i J) (ENNReal.ofReal p)
      (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal Cbank) :
    ∃ Ctail : ℝ, 0 < Ctail ∧
      ∀ epsilon : ℝ, 0 < epsilon → ∀ N M : ℕ,
      ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
        (chaosSampleLaw model).toMeasure Bad ≤
          ENNReal.ofReal (Ctail * (3 : ℝ) ^ (-p * epsilon * (N : ℝ))) ∧
        ∀ omega ∉ Bad, ∀ i : Fin m,
          |K i N omega| ≤ (3 : ℝ) ^ (epsilon * (N : ℝ)) ∧
          |K i M omega| ≤ (3 : ℝ) ^ (epsilon * (N : ℝ)) := by
  classical
  let B : ℝ := max Cbank 0 + 1
  have hBpos : 0 < B := by
    dsimp [B]
    linarith [le_max_right Cbank 0]
  have hBnonneg : 0 ≤ B := hBpos.le
  have hCB : Cbank ≤ B := by
    dsimp [B]
    linarith [le_max_left Cbank 0]
  let Ctail : ℝ := ((2 : ℝ) * (m : ℝ) + 1) * B ^ p
  have hCtail : 0 < Ctail := by
    dsimp [Ctail]
    exact mul_pos (by positivity) (Real.rpow_pos_of_pos hBpos p)
  refine ⟨Ctail, hCtail, ?_⟩
  intro epsilon hepsilon N M
  let t : ℝ := (3 : ℝ) ^ (epsilon * (N : ℝ))
  have ht : 0 < t := by
    dsimp [t]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hnorm : ∀ i : Fin m, ∀ J : ℕ,
      eLpNorm (K i J) (ENNReal.ofReal p) (chaosSampleLaw model).toMeasure ≤
        ENNReal.ofReal B := by
    intro i J
    exact (hbound i J).trans (ENNReal.ofReal_le_ofReal hCB)
  have hN : ∀ i : Fin m, ∃ Bad : Set (BilateralField d),
      MeasurableSet Bad ∧ {x : BilateralField d | t ≤ abs (K i N x)} ⊆ Bad ∧
        (chaosSampleLaw model).toMeasure Bad ≤
          ENNReal.ofReal (B ^ p * t ^ (-p)) := by
    intro i
    exact aux_lem_finite_stopping_moments_markov
      (chaosSampleLaw model).toMeasure p B t hp ht (K i N) (hmoment i N)
      (hnorm i N) hBnonneg
  have hM : ∀ i : Fin m, ∃ Bad : Set (BilateralField d),
      MeasurableSet Bad ∧ {x : BilateralField d | t ≤ abs (K i M x)} ⊆ Bad ∧
        (chaosSampleLaw model).toMeasure Bad ≤
          ENNReal.ofReal (B ^ p * t ^ (-p)) := by
    intro i
    exact aux_lem_finite_stopping_moments_markov
      (chaosSampleLaw model).toMeasure p B t hp ht (K i M) (hmoment i M)
      (hnorm i M) hBnonneg
  choose BadN hBadN hsubN hmeasureN using hN
  choose BadM hBadM hsubM hmeasureM using hM
  let Bad : Set (BilateralField d) := ⋃ i : Fin m, BadN i ∪ BadM i
  have hBadmeas : MeasurableSet Bad := by
    dsimp [Bad]
    exact MeasurableSet.iUnion fun i => (hBadN i).union (hBadM i)
  have hsum :
      (∑ i : Fin m,
        (ENNReal.ofReal (B ^ p * t ^ (-p)) +
          ENNReal.ofReal (B ^ p * t ^ (-p)))) =
        ENNReal.ofReal ((2 : ℝ) * (m : ℝ) * (B ^ p * t ^ (-p))) := by
    apply aux_lem_finite_stopping_moments_sum
    exact mul_nonneg (Real.rpow_nonneg hBnonneg _) (Real.rpow_nonneg ht.le _)
  have htneg : t ^ (-p) = (3 : ℝ) ^ (-p * epsilon * (N : ℝ)) := by
    dsimp [t]
    calc
      ((3 : ℝ) ^ (epsilon * (N : ℝ))) ^ (-p) =
          (3 : ℝ) ^ ((epsilon * (N : ℝ)) * (-p)) := by
            rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      _ = (3 : ℝ) ^ (-p * epsilon * (N : ℝ)) := by
            congr 1
            ring
  have hRnonneg : 0 ≤ (3 : ℝ) ^ (-p * epsilon * (N : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hmeasure :
      (chaosSampleLaw model).toMeasure Bad ≤
        ENNReal.ofReal (Ctail * (3 : ℝ) ^ (-p * epsilon * (N : ℝ))) := by
    calc
      (chaosSampleLaw model).toMeasure Bad ≤
          ∑ i : Fin m,
            (chaosSampleLaw model).toMeasure (BadN i ∪ BadM i) :=
        MeasureTheory.measure_iUnion_fintype_le _ _
      _ ≤ ∑ i : Fin m,
          (ENNReal.ofReal (B ^ p * t ^ (-p)) +
            ENNReal.ofReal (B ^ p * t ^ (-p))) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (measure_union_le _ _).trans
          (add_le_add (hmeasureN i) (hmeasureM i))
      _ = ENNReal.ofReal ((2 : ℝ) * (m : ℝ) *
            (B ^ p * t ^ (-p))) := hsum
      _ ≤ ENNReal.ofReal (Ctail * (3 : ℝ) ^ (-p * epsilon * (N : ℝ))) := by
        apply ENNReal.ofReal_le_ofReal
        rw [htneg]
        dsimp [Ctail]
        calc
          (2 : ℝ) * (m : ℝ) *
              (B ^ p * (3 : ℝ) ^ (-p * epsilon * (N : ℝ))) ≤
              ((2 : ℝ) * (m : ℝ) + 1) *
                (B ^ p * (3 : ℝ) ^ (-p * epsilon * (N : ℝ))) := by
            gcongr
            linarith
          _ = ((2 : ℝ) * (m : ℝ) + 1) * B ^ p *
                (3 : ℝ) ^ (-p * epsilon * (N : ℝ)) := by ring
  refine ⟨Bad, hBadmeas, hmeasure, ?_⟩
  intro omega hnot i
  constructor
  · have hgood : |K i N omega| ≤ t := by
      by_contra hbad
      have hbad' : omega ∈ BadN i := hsubN i (le_of_not_ge hbad)
      exact hnot (show omega ∈ Bad from
        Set.mem_iUnion.2 ⟨i, Set.mem_union_left _ hbad'⟩)
    simpa [t] using hgood
  · have hgood : |K i M omega| ≤ t := by
      by_contra hbad
      have hbad' : omega ∈ BadM i := hsubM i (le_of_not_ge hbad)
      exact hnot (show omega ∈ Bad from
        Set.mem_iUnion.2 ⟨i, Set.mem_union_right _ hbad'⟩)
    simpa [t] using hgood

end Paper
