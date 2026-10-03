module

public import SubdiffusiveProcess.Paper.lem_weighted_cluster
public import SubdiffusiveProcess.Paper.prop_killed_consistency
public import SubdiffusiveProcess.Paper.lem_sincos
public import SubdiffusiveProcess.Paper.prop_regularity
public import SubdiffusiveProcess.Paper.conv_represented_sequence
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Lane4.Carriers
public import Mathlib.Topology.PartitionOfUnity

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

lemma aux_prop_21_catalog_global_weighted_energy_fine_cube
    (Q : Opens (SpatialCoordinates d)) (rho : SpatialCoordinates d → ℝ)
    (hQopen : IsOpen (Q : Set (SpatialCoordinates d)))
    (hrhocont : ContinuousOn rho (closure (Q : Set (SpatialCoordinates d))))
    (K : Set (SpatialCoordinates d)) (hKQ : K ⊆ (Q : Set (SpatialCoordinates d)))
    (ε : ℝ) (hε : 0 < ε) (x : SpatialCoordinates d) (hx : x ∈ K) :
    ∃ (zq : SpatialCoordinates d) (rq : ℝ) (hrq : 0 < rq),
      (∀ i : Fin d, ∃ s : ℚ, zq i = (s : ℝ)) ∧
      (∃ k : ℤ, rq = (3 : ℝ) ^ k) ∧
      x ∈ (centeredCube zq rq hrq : Set (SpatialCoordinates d)) ∧
      (centeredCube zq rq hrq : Set (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d)) ∧
      ∀ y ∈ (centeredCube zq rq hrq : Set (SpatialCoordinates d)),
        |rho y - rho x| < ε := by
  have hxQ : x ∈ (Q : Set (SpatialCoordinates d)) := hKQ hx
  have hxcl : x ∈ closure (Q : Set (SpatialCoordinates d)) := subset_closure hxQ
  obtain ⟨δQ, hδQ, hballQ⟩ := Metric.isOpen_iff.mp hQopen x hxQ
  obtain ⟨δρ, hδρ, hρ⟩ :=
    (Metric.continuousWithinAt_iff.mp (hrhocont.continuousWithinAt hxcl)) ε hε
  let δ : ℝ := min δQ δρ
  have hδ : 0 < δ := lt_min hδQ hδρ
  obtain ⟨k, hk⟩ := exists_mem_Ioc_zpow (x := δ / 2) (y := (3 : ℝ))
    (div_pos hδ (by norm_num)) (by norm_num)
  let rq : ℝ := (3 : ℝ) ^ k
  have hrq : 0 < rq := by
    dsimp [rq]
    exact zpow_pos (by norm_num) k
  have hrqδ : rq < δ / 2 := hk.1
  let Rq : Set (SpatialCoordinates d) :=
    Set.pi Set.univ (fun _ : Fin d => Set.range (fun s : ℚ => (s : ℝ)))
  have hRq : Dense Rq := by
    apply dense_pi Set.univ
    intro i hi
    exact (Rat.denseRange_cast (𝕜 := ℝ))
  have hopen : IsOpen (Metric.ball x (rq / 4)) := Metric.isOpen_ball
  have hne : (Metric.ball x (rq / 4)).Nonempty :=
    Metric.nonempty_ball.mpr (div_pos hrq (by norm_num))
  obtain ⟨zq, hzqR, hzqx⟩ := hRq.exists_mem_open hopen hne
  have hzqx' : dist zq x < rq / 4 := Metric.mem_ball.mp hzqx
  have hzqrat : ∀ i : Fin d, ∃ s : ℚ, zq i = (s : ℝ) := by
    intro i
    have hi := (Set.mem_pi.mp hzqR) i (Set.mem_univ i)
    rcases Set.mem_range.mp hi with ⟨s, hs⟩
    exact ⟨s, hs.symm⟩
  have hxC : x ∈ (centeredCube zq rq hrq : Set (SpatialCoordinates d)) := by
    change dist x zq < rq / 2
    rw [dist_comm]
    exact lt_of_lt_of_le hzqx' (by linarith)
  have hCQ : (centeredCube zq rq hrq : Set (SpatialCoordinates d)) ⊆
      (Q : Set (SpatialCoordinates d)) := by
    intro y hy
    have hyC : dist y zq < rq / 2 := hy
    apply hballQ
    have hxy : dist y x ≤ dist y zq + dist zq x := dist_triangle y zq x
    have hxy' : dist y x < δQ := by
      have hδle : δ ≤ δQ := min_le_left _ _
      have : dist y zq + dist zq x < rq / 2 + rq / 4 := by
        exact add_lt_add hyC hzqx'
      linarith [hrqδ, hδle]
    exact hxy'
  have hCρ : ∀ y ∈ (centeredCube zq rq hrq : Set (SpatialCoordinates d)),
      |rho y - rho x| < ε := by
    intro y hy
    have hyQ : y ∈ (Q : Set (SpatialCoordinates d)) := hCQ hy
    have hycl : y ∈ closure (Q : Set (SpatialCoordinates d)) := subset_closure hyQ
    have hxy : dist y x ≤ dist y zq + dist zq x := dist_triangle y zq x
    have hxy' : dist y x < δρ := by
      have hδle : δ ≤ δρ := min_le_right _ _
      have : dist y zq + dist zq x < rq / 2 + rq / 4 := by
        exact add_lt_add (show dist y zq < rq / 2 from hy) hzqx'
      linarith [hrqδ, hδle]
    have hval := hρ hycl hxy'
    simpa [Real.dist_eq] using hval
  exact ⟨zq, rq, hrq, hzqrat, ⟨k, rfl⟩, hxC, hCQ, hCρ⟩

lemma aux_prop_21_catalog_global_weighted_energy_local_upper
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    (ν μ : Measure X) [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    (C : Set X) (hC : MeasurableSet C) (c : ℝ) (hc : 0 ≤ c)
    (hdom : ∀ B : Set X, MeasurableSet B → B ⊆ C →
      (ν B).toReal ≤ c * (μ B).toReal)
    (φ : X → ℝ) (hφc : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hφb : ∀ x, |φ x| ≤ 1) (hφsupp : tsupport φ ⊆ C) :
    (∫ x, φ x ∂ν) ≤ c * ∫ x, φ x ∂μ := by
  have hrest : ν.restrict C ≤ (ENNReal.ofReal c) • μ.restrict C := by
    refine Measure.le_iff.mpr (fun B hB => ?_)
    rw [Measure.restrict_apply hB, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply hB]
    have hreal := hdom (B ∩ C) (hB.inter hC) inter_subset_right
    apply (ENNReal.toReal_le_toReal (measure_ne_top ν _) ?_).mp
    · simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] using hreal
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _)
  have hφμ : Integrable φ μ :=
    DirichletForm.integrable_of_continuous_of_bound hφc hφb
  have hφscale : Integrable φ ((ENNReal.ofReal c) • μ.restrict C) := by
    apply (hφμ.mono_measure Measure.restrict_le_self).smul_measure
    exact ENNReal.ofReal_ne_top
  have hmono := integral_mono_measure hrest (Filter.Eventually.of_forall hφ0) hφscale
  have hνrestrict : (∫ x, φ x ∂ν) = ∫ x, φ x ∂(ν.restrict C) := by
    rw [← integral_indicator hC]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      by_cases hx : x ∈ C
      · simp [Set.indicator_of_mem hx]
      · have hzero : φ x = 0 := by
          by_contra hne
          exact hx (hφsupp (subset_closure (show x ∈ Function.support φ from hne)))
        simp [Set.indicator_of_notMem hx, hzero])
  have hscale :
      (∫ x, φ x ∂((ENNReal.ofReal c) • μ.restrict C)) =
        c * ∫ x, φ x ∂μ := by
    rw [integral_smul_measure, ENNReal.toReal_ofReal hc]
    have hμrestrict : (∫ x, φ x ∂(μ.restrict C)) = ∫ x, φ x ∂μ := by
      rw [← integral_indicator hC]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        by_cases hx : x ∈ C
        · simp [Set.indicator_of_mem hx]
        · have hzero : φ x = 0 := by
            by_contra hne
            exact hx (hφsupp (subset_closure (show x ∈ Function.support φ from hne)))
          simp [Set.indicator_of_notMem hx, hzero])
    rw [hμrestrict, smul_eq_mul]
  rw [← hνrestrict, hscale] at hmono
  exact hmono

lemma aux_prop_21_catalog_global_weighted_energy_local_lower
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    (ν μ : Measure X) [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    (C : Set X) (hC : MeasurableSet C) (c : ℝ) (hc : 0 ≤ c)
    (hdom : ∀ B : Set X, MeasurableSet B → B ⊆ C →
      c * (μ B).toReal ≤ (ν B).toReal)
    (φ : X → ℝ) (hφc : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hφb : ∀ x, |φ x| ≤ 1) (hφsupp : tsupport φ ⊆ C) :
    c * ∫ x, φ x ∂μ ≤ (∫ x, φ x ∂ν) := by
  have hrest : (ENNReal.ofReal c) • μ.restrict C ≤ ν.restrict C := by
    refine Measure.le_iff.mpr (fun B hB => ?_)
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hB,
      Measure.restrict_apply hB]
    have hreal := hdom (B ∩ C) (hB.inter hC) inter_subset_right
    exact (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _))
      (measure_ne_top ν _)).mp (by
        simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] using hreal)
  have hφμ : Integrable φ μ :=
    DirichletForm.integrable_of_continuous_of_bound hφc hφb
  have hφν : Integrable φ ν :=
    DirichletForm.integrable_of_continuous_of_bound hφc hφb
  have hscale : Integrable φ ((ENNReal.ofReal c) • μ.restrict C) := by
    apply (hφμ.mono_measure Measure.restrict_le_self).smul_measure
    exact ENNReal.ofReal_ne_top
  have hφνrestrict : Integrable φ (ν.restrict C) :=
    hφν.mono_measure Measure.restrict_le_self
  have hmono := integral_mono_measure hrest (Filter.Eventually.of_forall hφ0) hφνrestrict
  have hμrestrict : (∫ x, φ x ∂(μ.restrict C)) = ∫ x, φ x ∂μ := by
    rw [← integral_indicator hC]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      by_cases hx : x ∈ C
      · simp [Set.indicator_of_mem hx]
      · have hzero : φ x = 0 := by
          by_contra hne
          exact hx (hφsupp (subset_closure (show x ∈ Function.support φ from hne)))
        simp [Set.indicator_of_notMem hx, hzero])
  have hscale' :
      (∫ x, φ x ∂((ENNReal.ofReal c) • μ.restrict C)) =
        c * ∫ x, φ x ∂μ := by
    rw [integral_smul_measure, ENNReal.toReal_ofReal hc, hμrestrict, smul_eq_mul]
  have hνrestrict : (∫ x, φ x ∂(ν.restrict C)) = ∫ x, φ x ∂ν := by
    rw [← integral_indicator hC]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      by_cases hx : x ∈ C
      · simp [Set.indicator_of_mem hx]
      · have hzero : φ x = 0 := by
          by_contra hne
          exact hx (hφsupp (subset_closure (show x ∈ Function.support φ from hne)))
        simp [Set.indicator_of_notMem hx, hzero])
  rw [hscale', hνrestrict] at hmono
  exact hmono

lemma aux_prop_21_catalog_global_weighted_energy_partition_upper
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (ν μ : Measure X) [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    {n : ℕ} (K : Set X) (φ : Fin n → X → ℝ) (rho : X → ℝ) (ε : ℝ)
    (hνK : ν Kᶜ = 0) (hμK : μ Kᶜ = 0)
    (hφ0 : ∀ i x, 0 ≤ φ i x) (hφc : ∀ i, Continuous (φ i))
    (hsum : ∀ x ∈ K, ∑ i, φ i x = 1)
    (hνint : ∀ i, Integrable (φ i) ν)
    (hμint : ∀ i, Integrable (fun x => (rho x + ε) * φ i x) μ)
    (hρint : Integrable rho μ) (hε : 0 ≤ ε)
    (hpiece : ∀ i, (∫ x, φ i x ∂ν) ≤ ∫ x, (rho x + ε) * φ i x ∂μ) :
    (ν Set.univ).toReal ≤ (∫ x, rho x ∂μ) + ε * (μ Set.univ).toReal := by
  have hνae : ∀ᵐ x ∂ν, x ∈ K := by
    rw [ae_iff]
    exact hνK
  have hμae : ∀ᵐ x ∂μ, x ∈ K := by
    rw [ae_iff]
    exact hμK
  have hone : (∫ _x, (1 : ℝ) ∂ν) = (ν Set.univ).toReal := by
    rw [integral_const, measureReal_def, smul_eq_mul, mul_one]
  have hsumν : (ν Set.univ).toReal = ∑ i, ∫ x, φ i x ∂ν := by
    rw [← hone, ← integral_finset_sum Finset.univ (fun i _ => hνint i)]
    exact integral_congr_ae (hνae.mono fun x hx => by simp [hsum x hx])
  have hsumμ : (∫ x, (rho x + ε) ∂μ) =
      ∑ i, ∫ x, (rho x + ε) * φ i x ∂μ := by
    rw [← integral_finset_sum Finset.univ (fun i _ => hμint i)]
    exact integral_congr_ae (hμae.mono fun x hx => by
      change rho x + ε = ∑ i, (rho x + ε) * φ i x
      rw [← Finset.mul_sum, hsum x hx, mul_one])
  have hsplit : (∫ x, (rho x + ε) ∂μ) =
      (∫ x, rho x ∂μ) + ε * (μ Set.univ).toReal := by
    rw [integral_add hρint (integrable_const ε), integral_const, measureReal_def,
      smul_eq_mul, mul_comm]
  calc
    (ν Set.univ).toReal = ∑ i, ∫ x, φ i x ∂ν := hsumν
    _ ≤ ∑ i, ∫ x, (rho x + ε) * φ i x ∂μ :=
      Finset.sum_le_sum (fun i hi => hpiece i)
    _ = ∫ x, (rho x + ε) ∂μ := hsumμ.symm
    _ = (∫ x, rho x ∂μ) + ε * (μ Set.univ).toReal := hsplit

lemma aux_prop_21_catalog_global_weighted_energy_partition_lower
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (ν μ : Measure X) [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    {n : ℕ} (K : Set X) (φ : Fin n → X → ℝ) (rho : X → ℝ) (ε : ℝ)
    (hνK : ν Kᶜ = 0) (hμK : μ Kᶜ = 0)
    (hφ0 : ∀ i x, 0 ≤ φ i x) (hφc : ∀ i, Continuous (φ i))
    (hsum : ∀ x ∈ K, ∑ i, φ i x = 1)
    (hνint : ∀ i, Integrable (φ i) ν)
    (hμint : ∀ i, Integrable (fun x => (rho x - ε) * φ i x) μ)
    (hρint : Integrable rho μ) (hε : 0 ≤ ε)
    (hpiece : ∀ i, (∫ x, (rho x - ε) * φ i x ∂μ) ≤ ∫ x, φ i x ∂ν) :
    (∫ x, rho x ∂μ) ≤ (ν Set.univ).toReal + ε * (μ Set.univ).toReal := by
  have hνae : ∀ᵐ x ∂ν, x ∈ K := by
    rw [ae_iff]
    exact hνK
  have hμae : ∀ᵐ x ∂μ, x ∈ K := by
    rw [ae_iff]
    exact hμK
  have hone : (∫ _x, (1 : ℝ) ∂ν) = (ν Set.univ).toReal := by
    rw [integral_const, measureReal_def, smul_eq_mul, mul_one]
  have hsumν : (ν Set.univ).toReal = ∑ i, ∫ x, φ i x ∂ν := by
    rw [← hone, ← integral_finset_sum Finset.univ (fun i _ => hνint i)]
    exact integral_congr_ae (hνae.mono fun x hx => by simp [hsum x hx])
  have hsumμ : (∫ x, (rho x - ε) ∂μ) =
      ∑ i, ∫ x, (rho x - ε) * φ i x ∂μ := by
    rw [← integral_finset_sum Finset.univ (fun i _ => hμint i)]
    exact integral_congr_ae (hμae.mono fun x hx => by
      change rho x - ε = ∑ i, (rho x - ε) * φ i x
      rw [← Finset.mul_sum, hsum x hx, mul_one])
  have hsplit : (∫ x, rho x ∂μ) =
      (∫ x, (rho x - ε) ∂μ) + ε * (μ Set.univ).toReal := by
    rw [integral_sub hρint (integrable_const ε), integral_const, measureReal_def,
      smul_eq_mul, mul_comm]
    ring
  calc
    (∫ x, rho x ∂μ) = (∫ x, (rho x - ε) ∂μ) + ε * (μ Set.univ).toReal := hsplit
    _ = (∑ i, ∫ x, (rho x - ε) * φ i x ∂μ) + ε * (μ Set.univ).toReal :=
      congrArg (fun t => t + ε * (μ Set.univ).toReal) hsumμ
    _ ≤ (∑ i, ∫ x, φ i x ∂ν) + ε * (μ Set.univ).toReal := by
      have hs : (∑ i, ∫ x, (rho x - ε) * φ i x ∂μ) ≤
          ∑ i, ∫ x, φ i x ∂ν := by
        simpa using (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpiece i))
      simpa [add_comm] using add_le_add_right hs (ε * (μ Set.univ).toReal)
    _ = (ν Set.univ).toReal + ε * (μ Set.univ).toReal := by rw [← hsumν]

lemma aux_prop_21_catalog_global_weighted_energy_core_mass
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    {Q : Opens (SpatialCoordinates d)}
    (hQcube : Q = centeredCube z0 R hR)
    (E F : DirichletForm.ClosedForm
      (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GE GF : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hEform : ∀ w : DomainL2 Q, E.energy w = limitFormEnergy GE w)
    (hFform : ∀ w : DomainL2 Q, F.energy w = limitFormEnergy GF w)
    (GammaE : DirichletForm.EnergyMeasure E)
    (GammaF : DirichletForm.EnergyMeasure F)
    (rho : SpatialCoordinates d → ℝ)
    (hrhocont : ContinuousOn rho (closure (Q : Set (SpatialCoordinates d))))
    (hrhopos : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), 0 < rho x)
    (w : DomainL2 Q)
    (hcore : MemFormCore GE w)
    (hwE : w ∈ E.domain) (hwF : w ∈ F.domain)
    (K : Set (SpatialCoordinates d)) (hK : IsCompact K)
    (hKQ : K ⊆ (Q : Set (SpatialCoordinates d)))
    (hμK : GammaE.measure w Kᶜ = 0) (hνK : GammaF.measure w Kᶜ = 0)
    (hmeasure : ∀ (zq : SpatialCoordinates d) (rq : ℝ) (hrq : 0 < rq),
      (∀ i : Fin d, ∃ s : ℚ, zq i = (s : ℝ)) →
      (∃ k : ℤ, rq = (3 : ℝ) ^ k) →
      (centeredCube zq rq hrq : Set (SpatialCoordinates d)) ⊆
        (Q : Set (SpatialCoordinates d)) →
      ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
        B ⊆ (centeredCube zq rq hrq : Set (SpatialCoordinates d)) →
        sInf (rho '' (centeredCube zq rq hrq : Set (SpatialCoordinates d))) *
            (GammaE.measure w B).toReal ≤
            (GammaF.measure w B).toReal ∧
          (GammaF.measure w B).toReal ≤
            sSup (rho '' (centeredCube zq rq hrq : Set (SpatialCoordinates d))) *
              (GammaE.measure w B).toReal) :
    (GammaF.measure w Set.univ).toReal =
      ∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure w) := by
  let μ : Measure (SpatialCoordinates d) := GammaE.measure w
  let ν : Measure (SpatialCoordinates d) := GammaF.measure w
  let S : Set (SpatialCoordinates d) := closure (Q : Set (SpatialCoordinates d))
  have hQcompact : IsCompact S := by
    dsimp [S]
    rw [hQcube, centeredCube]
    change IsCompact (closure (Metric.ball z0 (R / 2)))
    rw [closure_ball _ (by positivity)]
    exact ProperSpace.isCompact_closedBall z0 (R / 2)
  have hμfin : IsFiniteMeasure μ := ⟨by simpa [μ] using GammaE.measure_univ_lt_top w hwE⟩
  have hνfin : IsFiniteMeasure ν := ⟨by simpa [ν] using GammaF.measure_univ_lt_top w hwF⟩
  letI : IsFiniteMeasure μ := hμfin
  letI : IsFiniteMeasure ν := hνfin
  letI : IsFiniteMeasureOnCompacts μ :=
    ⟨fun {C} hC => lt_of_le_of_lt (measure_mono (Set.subset_univ C))
      (measure_lt_top μ Set.univ)⟩
  letI : IsFiniteMeasureOnCompacts ν :=
    ⟨fun {C} hC => lt_of_le_of_lt (measure_mono (Set.subset_univ C))
      (measure_lt_top ν Set.univ)⟩
  have hμQ : μ (Q : Set (SpatialCoordinates d))ᶜ = 0 := by
    apply measure_mono_null
      (show (Q : Set (SpatialCoordinates d))ᶜ ⊆ Kᶜ by
        intro x hx hxK
        exact hx (hKQ hxK))
    simpa [μ] using hμK
  have hνQ : ν (Q : Set (SpatialCoordinates d))ᶜ = 0 := by
    apply measure_mono_null
      (show (Q : Set (SpatialCoordinates d))ᶜ ⊆ Kᶜ by
        intro x hx hxK
        exact hx (hKQ hxK))
    simpa [ν] using hνK
  have hμS : μ Sᶜ = 0 := by
    apply measure_mono_null (show Sᶜ ⊆ (Q : Set (SpatialCoordinates d))ᶜ by
      intro x hx hxQ
      exact hx (subset_closure hxQ))
    exact hμQ
  have hνS : ν Sᶜ = 0 := by
    apply measure_mono_null (show Sᶜ ⊆ (Q : Set (SpatialCoordinates d))ᶜ by
      intro x hx hxQ
      exact hx (subset_closure hxQ))
    exact hνQ
  have hSmeas : MeasurableSet S := isClosed_closure.measurableSet
  have hIntOnμ : ∀ (g : SpatialCoordinates d → ℝ), ContinuousOn g S → Integrable g μ := by
    intro g hg
    have hi : IntegrableOn g S μ := hg.integrableOn_compact hQcompact
    have hi' : Integrable (S.indicator g) μ := hi.integrable_indicator hSmeas
    have ha : ∀ᵐ x ∂μ, x ∈ S := by
      rw [ae_iff]
      exact hμS
    exact hi'.congr (ha.mono fun x hx => by simp [Set.indicator_of_mem hx])
  have hIntOnν : ∀ (g : SpatialCoordinates d → ℝ), ContinuousOn g S → Integrable g ν := by
    intro g hg
    have hi : IntegrableOn g S ν := hg.integrableOn_compact hQcompact
    have hi' : Integrable (S.indicator g) ν := hi.integrable_indicator hSmeas
    have ha : ∀ᵐ x ∂ν, x ∈ S := by
      rw [ae_iff]
      exact hνS
    exact hi'.congr (ha.mono fun x hx => by simp [Set.indicator_of_mem hx])
  have hρint : Integrable rho μ := hIntOnμ rho hrhocont
  have hμmass : 0 ≤ (μ Set.univ).toReal := ENNReal.toReal_nonneg
  have hfine : ∀ (ε : ℝ), 0 < ε →
      (ν Set.univ).toReal ≤ (∫ x, rho x ∂μ) + ε * (μ Set.univ).toReal ∧
      (∫ x, rho x ∂μ) ≤ (ν Set.univ).toReal + ε * (μ Set.univ).toReal := by
    intro ε hε
    have hcover : ∀ x : K, ∃ (zq : SpatialCoordinates d) (rq : ℝ) (hrq : 0 < rq),
        (∀ i : Fin d, ∃ s : ℚ, zq i = (s : ℝ)) ∧
        (∃ k : ℤ, rq = (3 : ℝ) ^ k) ∧
        (x : SpatialCoordinates d) ∈ (centeredCube zq rq hrq : Set (SpatialCoordinates d)) ∧
        (centeredCube zq rq hrq : Set (SpatialCoordinates d)) ⊆
          (Q : Set (SpatialCoordinates d)) ∧
        ∀ y ∈ (centeredCube zq rq hrq : Set (SpatialCoordinates d)),
          |rho y - rho (x : SpatialCoordinates d)| < ε / 2 := by
      intro x
      simpa using aux_prop_21_catalog_global_weighted_energy_fine_cube Q rho Q.isOpen
        hrhocont K hKQ (ε / 2) (by linarith) x x.property
    choose zq rq hrq hzrat hpow hxC hCQ hosc using hcover
    let U : K → Set (SpatialCoordinates d) := fun x =>
      (centeredCube (zq x) (rq x) (hrq x) : Set (SpatialCoordinates d))
    have hUopen : ∀ x : K, IsOpen (U x) := by
      intro x
      change IsOpen (Metric.ball (zq x) (rq x / 2))
      exact Metric.isOpen_ball
    have hUcover : K ⊆ ⋃ x : K, U x := by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxC ⟨x, hx⟩⟩
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hUopen hUcover
    let e : (t : Set K) ≃ Fin t.card := Finset.equivFin t
    let V : Fin t.card → Set (SpatialCoordinates d) := fun i => U (e.symm i)
    have hVopen : ∀ i, IsOpen (V i) := by
      intro i
      exact hUopen (e.symm i)
    have hVcover : K ⊆ ⋃ i, V i := by
      intro x hx
      rcases mem_iUnion.mp (ht hx) with ⟨y, hy⟩
      rcases mem_iUnion.mp hy with ⟨hyt, hxy⟩
      let i : Fin t.card := e ⟨y, hyt⟩
      refine mem_iUnion.mpr ⟨i, ?_⟩
      simpa [V, i, e] using hxy
    obtain ⟨f, hfsupp, hfsum, hfIcc, hfcompact⟩ :=
      exists_continuous_sum_one_of_isOpen_isCompact hVopen hK hVcover
    let φ : Fin t.card → SpatialCoordinates d → ℝ := fun i x => f i x
    have hsum : ∀ x ∈ K, ∑ i, φ i x = 1 := by
      intro x hx
      simpa [φ] using hfsum hx
    have hφ0 : ∀ i x, 0 ≤ φ i x := by
      intro i x
      exact (hfIcc i x).1
    have hφc : ∀ i, Continuous (φ i) := by
      intro i
      exact (f i).continuous
    have hφsupp : ∀ i, tsupport (φ i) ⊆ V i := by
      intro i
      simpa [φ] using hfsupp i
    have hφcompact : ∀ i, HasCompactSupport (φ i) := by
      intro i
      simpa [φ] using hfcompact i
    have hφb : ∀ i x, |φ i x| ≤ 1 := by
      intro i x
      rw [abs_of_nonneg (hφ0 i x)]
      exact (hfIcc i x).2
    have hpiece_upper : ∀ i, (∫ x, φ i x ∂ν) ≤
        ∫ x, (rho x + ε) * φ i x ∂μ := by
      intro i
      let C : Set (SpatialCoordinates d) := V i
      have hCopen : IsOpen C := hVopen i
      have hCmeas : MeasurableSet C := hCopen.measurableSet
      have hCQ' : C ⊆ (Q : Set (SpatialCoordinates d)) := by
        intro x hx
        exact hCQ (e.symm i) hx
      let c : ℝ := sSup (rho '' C)
      have hBdd : BddAbove (rho '' C) := by
        apply (hQcompact.bddAbove_image hrhocont).mono
        exact image_mono (fun x hx => subset_closure (hCQ' hx))
      have hbase : ((e.symm i : K) : SpatialCoordinates d) ∈ C := by
        exact hxC (e.symm i)
      have hbaseQ : ((e.symm i : K) : SpatialCoordinates d) ∈
          (Q : Set (SpatialCoordinates d)) := hCQ' hbase
      have hbasepos : 0 < rho ((e.symm i : K) : SpatialCoordinates d) :=
        hrhopos _ (subset_closure hbaseQ)
      have hc : 0 ≤ c := by
        dsimp [c]
        have hbasele : rho ((e.symm i : K) : SpatialCoordinates d) ≤
            sSup (rho '' C) := le_csSup hBdd ⟨_, hbase, rfl⟩
        exact le_trans (le_of_lt hbasepos) hbasele
      have hcsup : c ≤ rho ((e.symm i : K) : SpatialCoordinates d) + ε / 2 := by
        dsimp [c]
        have hnonempty : (rho '' C).Nonempty :=
          ⟨rho ((e.symm i : K) : SpatialCoordinates d),
            ⟨((e.symm i : K) : SpatialCoordinates d), hbase, rfl⟩⟩
        apply csSup_le hnonempty
        rintro _ ⟨y, hy, rfl⟩
        have ho := hosc (e.symm i) y hy
        exact le_of_lt (by
          simpa [add_comm] using (sub_lt_iff_lt_add.mp (abs_lt.mp ho).2))
      have hdom : ∀ B : Set (SpatialCoordinates d), MeasurableSet B → B ⊆ C →
          (ν B).toReal ≤ c * (μ B).toReal := by
        intro B hB hBC
        have hh := hmeasure (zq (e.symm i)) (rq (e.symm i)) (hrq (e.symm i))
          (hzrat (e.symm i)) (hpow (e.symm i)) (hCQ (e.symm i)) B hB hBC
        exact hh.2
      have hlocal := aux_prop_21_catalog_global_weighted_energy_local_upper ν μ C
        hCmeas c hc hdom (φ i) (hφc i) (hφ0 i) (hφb i) (hφsupp i)
      have hprod : ContinuousOn (fun x => (rho x + ε) * φ i x) S := by
        exact (hrhocont.add continuousOn_const).mul (hφc i).continuousOn
      have hprodint : Integrable (fun x => (rho x + ε) * φ i x) μ :=
        hIntOnμ _ hprod
      have hφint : Integrable (φ i) μ := hIntOnμ _ (hφc i).continuousOn
      have hpoint : ∀ x, c * φ i x ≤ (rho x + ε) * φ i x := by
        intro x
        by_cases hx : x ∈ C
        · have ho := hosc (e.symm i) x hx
          have hcx : c ≤ rho x + ε := by
            linarith [hcsup, (abs_lt.mp ho).1]
          exact mul_le_mul_of_nonneg_right hcx (hφ0 i x)
        · have hz : φ i x = 0 := by
            by_contra hn
            exact hx (hφsupp i (subset_closure (show x ∈ Function.support (φ i) from hn)))
          simp [hz]
      have hint := integral_mono (hφint.const_mul c) hprodint hpoint
      calc
        (∫ x, φ i x ∂ν) ≤ c * ∫ x, φ i x ∂μ := by
          simpa using hlocal
        _ = ∫ x, c * φ i x ∂μ := (integral_const_mul c (φ i)).symm
        _ ≤ ∫ x, (rho x + ε) * φ i x ∂μ := hint
    have hpiece_lower : ∀ i, (∫ x, (rho x - ε) * φ i x ∂μ) ≤
        ∫ x, φ i x ∂ν := by
      intro i
      let C : Set (SpatialCoordinates d) := V i
      have hCopen : IsOpen C := hVopen i
      have hCmeas : MeasurableSet C := hCopen.measurableSet
      have hCQ' : C ⊆ (Q : Set (SpatialCoordinates d)) := by
        intro x hx
        exact hCQ (e.symm i) hx
      let c : ℝ := sInf (rho '' C)
      have hBdd : BddBelow (rho '' C) := by
        apply (hQcompact.bddBelow_image hrhocont).mono
        exact image_mono (fun x hx => subset_closure (hCQ' hx))
      have hbase : ((e.symm i : K) : SpatialCoordinates d) ∈ C := hxC (e.symm i)
      have hbaseQ : ((e.symm i : K) : SpatialCoordinates d) ∈
          (Q : Set (SpatialCoordinates d)) := hCQ' hbase
      have hbasepos : 0 < rho ((e.symm i : K) : SpatialCoordinates d) :=
        hrhopos _ (subset_closure hbaseQ)
      have hc : 0 ≤ c := by
        dsimp [c]
        have hnonempty : (rho '' C).Nonempty :=
          ⟨rho ((e.symm i : K) : SpatialCoordinates d),
            ⟨((e.symm i : K) : SpatialCoordinates d), hbase, rfl⟩⟩
        apply le_csInf hnonempty
        intro b hb
        rcases hb with ⟨y, hy, rfl⟩
        exact le_of_lt (hrhopos _ (subset_closure (hCQ' hy)))
      have hcinf : rho ((e.symm i : K) : SpatialCoordinates d) - ε / 2 ≤ c := by
        dsimp [c]
        have hnonempty : (rho '' C).Nonempty :=
          ⟨rho ((e.symm i : K) : SpatialCoordinates d),
            ⟨((e.symm i : K) : SpatialCoordinates d), hbase, rfl⟩⟩
        apply le_csInf hnonempty
        rintro _ ⟨y, hy, rfl⟩
        have ho := hosc (e.symm i) y hy
        exact le_of_lt (by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            (lt_sub_iff_add_lt.mp (abs_lt.mp ho).1))
      have hdom : ∀ B : Set (SpatialCoordinates d), MeasurableSet B → B ⊆ C →
          c * (μ B).toReal ≤ (ν B).toReal := by
        intro B hB hBC
        have hh := hmeasure (zq (e.symm i)) (rq (e.symm i)) (hrq (e.symm i))
          (hzrat (e.symm i)) (hpow (e.symm i)) (hCQ (e.symm i)) B hB hBC
        exact hh.1
      have hlocal := aux_prop_21_catalog_global_weighted_energy_local_lower ν μ C
        hCmeas c hc hdom (φ i) (hφc i) (hφ0 i) (hφb i) (hφsupp i)
      have hprod : ContinuousOn (fun x => (rho x - ε) * φ i x) S := by
        exact (hrhocont.sub continuousOn_const).mul (hφc i).continuousOn
      have hprodint : Integrable (fun x => (rho x - ε) * φ i x) μ :=
        hIntOnμ _ hprod
      have hφint : Integrable (φ i) μ := hIntOnμ _ (hφc i).continuousOn
      have hpoint : ∀ x, (rho x - ε) * φ i x ≤ c * φ i x := by
        intro x
        by_cases hx : x ∈ C
        · have ho := hosc (e.symm i) x hx
          have hxc : rho x - ε ≤ c := by
            linarith [hcinf, (abs_lt.mp ho).2]
          exact mul_le_mul_of_nonneg_right hxc (hφ0 i x)
        · have hz : φ i x = 0 := by
            by_contra hn
            exact hx (hφsupp i (subset_closure (show x ∈ Function.support (φ i) from hn)))
          simp [hz]
      have hint := integral_mono hprodint (hφint.const_mul c) hpoint
      calc
        (∫ x, (rho x - ε) * φ i x ∂μ) ≤ ∫ x, c * φ i x ∂μ := hint
        _ = c * ∫ x, φ i x ∂μ := integral_const_mul c (φ i)
        _ ≤ ∫ x, φ i x ∂ν := by simpa using hlocal
    have hνint : ∀ i, Integrable (φ i) ν := by
      intro i
      exact hIntOnν _ (hφc i).continuousOn
    have hμplus : ∀ i, Integrable (fun x => (rho x + ε) * φ i x) μ := by
      intro i
      exact hIntOnμ _ ((hrhocont.add continuousOn_const).mul (hφc i).continuousOn)
    have hμminus : ∀ i, Integrable (fun x => (rho x - ε) * φ i x) μ := by
      intro i
      exact hIntOnμ _ ((hrhocont.sub continuousOn_const).mul (hφc i).continuousOn)
    constructor
    · exact aux_prop_21_catalog_global_weighted_energy_partition_upper ν μ K φ rho ε
        hνK hμK hφ0 hφc hsum hνint hμplus hρint (le_of_lt hε) hpiece_upper
    · exact aux_prop_21_catalog_global_weighted_energy_partition_lower ν μ K φ rho ε
        hνK hμK hφ0 hφc hsum hνint hμminus hρint (le_of_lt hε) hpiece_lower
  have hνle : (ν Set.univ).toReal ≤ ∫ x, rho x ∂μ := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    have hden : 0 < (μ Set.univ).toReal + 1 := by linarith
    have hh := (hfine (δ / ((μ Set.univ).toReal + 1)) (div_pos hδ hden)).1
    have hratio : (μ Set.univ).toReal / ((μ Set.univ).toReal + 1) ≤ 1 := by
      apply (div_le_iff₀ hden).2
      linarith
    have hmul : δ / ((μ Set.univ).toReal + 1) * (μ Set.univ).toReal ≤ δ := by
      calc
        δ / ((μ Set.univ).toReal + 1) * (μ Set.univ).toReal =
            δ * ((μ Set.univ).toReal / ((μ Set.univ).toReal + 1)) := by ring
        _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hratio (le_of_lt hδ)
        _ = δ := by ring
    linarith
  have hIle : (∫ x, rho x ∂μ) ≤ (ν Set.univ).toReal := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    have hden : 0 < (μ Set.univ).toReal + 1 := by linarith
    have hh := (hfine (δ / ((μ Set.univ).toReal + 1)) (div_pos hδ hden)).2
    have hratio : (μ Set.univ).toReal / ((μ Set.univ).toReal + 1) ≤ 1 := by
      apply (div_le_iff₀ hden).2
      linarith
    have hmul : δ / ((μ Set.univ).toReal + 1) * (μ Set.univ).toReal ≤ δ := by
      calc
        δ / ((μ Set.univ).toReal + 1) * (μ Set.univ).toReal =
            δ * ((μ Set.univ).toReal / ((μ Set.univ).toReal + 1)) := by ring
        _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hratio (le_of_lt hδ)
        _ = δ := by ring
    linarith
  have hmass : (ν Set.univ).toReal = ∫ x, rho x ∂μ := le_antisymm hνle hIle
  have hQint : (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂μ) =
      ∫ x, rho x ∂μ := by
    rw [← integral_indicator (Q.isOpen.measurableSet)]
    apply integral_congr_ae
    have ha : ∀ᵐ x ∂μ, x ∈ (Q : Set (SpatialCoordinates d)) := by
      rw [ae_iff]
      exact hμQ
    filter_upwards [ha] with x hx
    simp [Set.indicator_of_mem hx]
  simpa [μ, ν] using hmass.trans hQint.symm

lemma aux_prop_21_catalog_global_weighted_energy_core_sub
    {Q : Opens (SpatialCoordinates d)}
    (E : DirichletForm.ClosedForm
      (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GE : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hEform : ∀ w : DomainL2 Q, E.energy w = limitFormEnergy GE w)
    (a b : DomainL2 Q) (ha : MemFormCore GE a) (hb : MemFormCore GE b) :
    MemFormCore GE (a - b) := by
  rcases ha with ⟨ha_lim, fa, hfa_cont, hfa_comp, hfa_Q, hfa_rep⟩
  rcases hb with ⟨hb_lim, fb, hfb_cont, hfb_comp, hfb_Q, hfb_rep⟩
  have haE : a ∈ E.domain := by
    apply E.mem_domain_of_energy_lt_top
    rw [hEform]
    exact ha_lim
  have hbE : b ∈ E.domain := by
    apply E.mem_domain_of_energy_lt_top
    rw [hEform]
    exact hb_lim
  have habE : a - b ∈ E.domain := E.domain.sub_mem haE hbE
  refine ⟨?_, fa - fb, hfa_cont.sub hfb_cont, hfa_comp.sub hfb_comp,
    ?_, ?_⟩
  · change limitFormEnergy GE (a - b) < (⊤ : EReal)
    rw [← hEform, E.energy_of_mem habE]
    exact EReal.coe_lt_top _
  · exact (tsupport_sub fa fb).trans (union_subset hfa_Q hfb_Q)
  · filter_upwards [hfa_rep, hfb_rep, Lp.coeFn_sub a b] with x hax hbx hab
    rw [hab]
    simpa using congrArg₂ (fun x y : ℝ => x - y) hax hbx

lemma aux_prop_21_catalog_global_weighted_energy_energy_measure_add_le
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} {E : DirichletForm.ClosedForm m}
    (Gamma : DirichletForm.EnergyMeasure E)
    {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    {t : ℝ} (ht : 0 < t) :
    Gamma.measure (u + v) ≤
      (ENNReal.ofReal (1 + t)) • Gamma.measure u +
        (ENNReal.ofReal (1 + t⁻¹)) • Gamma.measure v := by
  refine Measure.le_iff.mpr (fun B hB => ?_)
  have huv : u + v ∈ E.domain := E.domain.add_mem hu hv
  have hcross := Gamma.cross_add_self_apply hu hv B
  rw [Gamma.cross_self (u + v) huv B hB, Gamma.cross_self u hu B hB,
    Gamma.cross_self v hv B hB] at hcross
  have hcs := Gamma.abs_cross_le u hu v hv B hB
  have hnonneg_u : 0 ≤ (Gamma.measure u B).toReal := ENNReal.toReal_nonneg
  have hnonneg_v : 0 ≤ (Gamma.measure v B).toReal := ENNReal.toReal_nonneg
  have hyoung : 2 * |Gamma.cross u v B| ≤
      t * (Gamma.measure u B).toReal + t⁻¹ * (Gamma.measure v B).toReal := by
    have hsq : 0 ≤ (t * Real.sqrt ((Gamma.measure u B).toReal) -
        Real.sqrt ((Gamma.measure v B).toReal)) ^ 2 := sq_nonneg _
    have htu : 0 ≤ t * Real.sqrt ((Gamma.measure u B).toReal) ^ 2 := by positivity
    have hsqu : Real.sqrt ((Gamma.measure u B).toReal) ^ 2 =
        (Gamma.measure u B).toReal := Real.sq_sqrt hnonneg_u
    have hsqv : Real.sqrt ((Gamma.measure v B).toReal) ^ 2 =
        (Gamma.measure v B).toReal := Real.sq_sqrt hnonneg_v
    have hbase : 2 * t * (Real.sqrt ((Gamma.measure u B).toReal) *
        Real.sqrt ((Gamma.measure v B).toReal)) ≤
        t ^ 2 * (Gamma.measure u B).toReal + (Gamma.measure v B).toReal := by
      nlinarith [hsq]
    have ht0 : t ≠ 0 := ne_of_gt ht
    have := mul_le_mul_of_nonneg_left hbase (le_of_lt (inv_pos.mpr ht))
    rw [mul_add] at this
    have hrewrite : (t⁻¹) * (t ^ 2 * (Gamma.measure u B).toReal) =
        t * (Gamma.measure u B).toReal := by field_simp
    have hscaled : 2 * (Real.sqrt ((Gamma.measure u B).toReal) *
        Real.sqrt ((Gamma.measure v B).toReal)) ≤
        t * (Gamma.measure u B).toReal + t⁻¹ * (Gamma.measure v B).toReal := by
      calc
        2 * (Real.sqrt ((Gamma.measure u B).toReal) *
            Real.sqrt ((Gamma.measure v B).toReal)) =
            t⁻¹ * (2 * t * (Real.sqrt ((Gamma.measure u B).toReal) *
              Real.sqrt ((Gamma.measure v B).toReal))) := by field_simp
        _ ≤ t⁻¹ * (t ^ 2 * (Gamma.measure u B).toReal) +
            t⁻¹ * (Gamma.measure v B).toReal := this
        _ = t * (Gamma.measure u B).toReal +
            t⁻¹ * (Gamma.measure v B).toReal := by rw [hrewrite]
    exact (mul_le_mul_of_nonneg_left hcs (by norm_num)).trans hscaled
  have hleft : Gamma.measure (u + v) B ≠ ⊤ := Gamma.measure_ne_top huv B
  have hu_top : Gamma.measure u B ≠ ⊤ := Gamma.measure_ne_top hu B
  have hv_top : Gamma.measure v B ≠ ⊤ := Gamma.measure_ne_top hv B
  have hprod_u : ENNReal.ofReal (1 + t) * Gamma.measure u B ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hu_top
  have hprod_v : ENNReal.ofReal (1 + t⁻¹) * Gamma.measure v B ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hv_top
  have hright :
      ((ENNReal.ofReal (1 + t)) • Gamma.measure u +
        (ENNReal.ofReal (1 + t⁻¹)) • Gamma.measure v) B ≠ ⊤ := by
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    change ENNReal.ofReal (1 + t) * Gamma.measure u B +
      ENNReal.ofReal (1 + t⁻¹) * Gamma.measure v B ≠ ⊤
    exact ENNReal.add_ne_top.mpr ⟨hprod_u, hprod_v⟩
  apply (ENNReal.toReal_le_toReal hleft hright).mp
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [smul_eq_mul]
  rw [
    ENNReal.toReal_add hprod_u hprod_v, ENNReal.toReal_mul,
    ENNReal.toReal_mul,
    ENNReal.toReal_ofReal, ENNReal.toReal_ofReal]
  · rw [hcross]
    calc
      (Gamma.measure u B).toReal + 2 * Gamma.cross u v B +
          (Gamma.measure v B).toReal ≤
          (Gamma.measure u B).toReal +
            (t * (Gamma.measure u B).toReal + t⁻¹ *
              (Gamma.measure v B).toReal) +
            (Gamma.measure v B).toReal := by
        have hcrossle : Gamma.cross u v B ≤ |Gamma.cross u v B| := le_abs_self _
        linarith [hyoung, hcrossle]
      _ = (1 + t) * (Gamma.measure u B).toReal +
            (1 + t⁻¹) * (Gamma.measure v B).toReal := by ring
  · positivity
  · positivity

lemma aux_prop_21_catalog_global_weighted_energy_core_measure_eq
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    {Q : Opens (SpatialCoordinates d)}
    (hQcube : Q = centeredCube z0 R hR)
    (E F : DirichletForm.ClosedForm
      (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GE GF : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hEform : ∀ w : DomainL2 Q, E.energy w = limitFormEnergy GE w)
    (hFform : ∀ w : DomainL2 Q, F.energy w = limitFormEnergy GF w)
    (GammaE : DirichletForm.EnergyMeasure E)
    (GammaF : DirichletForm.EnergyMeasure F)
    (rho : SpatialCoordinates d → ℝ)
    (hrhocont : ContinuousOn rho (closure (Q : Set (SpatialCoordinates d))))
    (hrhopos : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), 0 < rho x)
    (hFdomain : ∀ w : DomainL2 Q, MemFormCore GE w → w ∈ F.domain)
    (hmeasure : ∀ (zq : SpatialCoordinates d) (rq : ℝ) (hrq : 0 < rq),
      (∀ i : Fin d, ∃ s : ℚ, zq i = (s : ℝ)) →
      (∃ k : ℤ, rq = (3 : ℝ) ^ k) →
      (centeredCube zq rq hrq : Set (SpatialCoordinates d)) ⊆
        (Q : Set (SpatialCoordinates d)) →
      ∀ w : DomainL2 Q, MemFormCore GE w →
      ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
        B ⊆ (centeredCube zq rq hrq : Set (SpatialCoordinates d)) →
        sInf (rho '' (centeredCube zq rq hrq : Set (SpatialCoordinates d))) *
            (GammaE.measure w B).toReal ≤
            (GammaF.measure w B).toReal ∧
          (GammaF.measure w B).toReal ≤
            sSup (rho '' (centeredCube zq rq hrq : Set (SpatialCoordinates d))) *
              (GammaE.measure w B).toReal)
    (w : DomainL2 Q) (hw : MemFormCore GE w) :
    F.form w w = ∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure w) := by
  have hwE : w ∈ E.domain := by
    apply E.mem_domain_of_energy_lt_top
    rw [hEform]
    exact hw.1
  have hwF : w ∈ F.domain := hFdomain w hw
  rcases hw with ⟨hwlim, f, hfc, hfs, hfQ, hwrep⟩
  have hμK : GammaE.measure w (tsupport f)ᶜ = 0 :=
    GammaE.measure_compl_tsupport w hwE f hfc hwrep
  have hνK : GammaF.measure w (tsupport f)ᶜ = 0 :=
    GammaF.measure_compl_tsupport w hwF f hfc hwrep
  have hmass := aux_prop_21_catalog_global_weighted_energy_core_mass z0 R hR hQcube E F GE GF
    hEform hFform GammaE GammaF rho hrhocont hrhopos w
    ⟨hwlim, f, hfc, hfs, hfQ, hwrep⟩ hwE hwF
    (tsupport f) hfs hfQ hμK hνK (fun zq rq hrq hzq hk hq B hB hBcube =>
      hmeasure zq rq hrq hzq hk hq w
        ⟨hwlim, f, hfc, hfs, hfQ, hwrep⟩ B hB hBcube)
  calc
    F.form w w = (GammaF.measure w Set.univ).toReal :=
      (GammaF.measure_univ w hwF).symm
    _ = ∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure w) := hmass

lemma aux_prop_21_catalog_global_weighted_energy_weighted_measure_add_le
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} {E : DirichletForm.ClosedForm m}
    (Gamma : DirichletForm.EnergyMeasure E) (Q : Set X) (rho : X → ℝ)
    (hQ : MeasurableSet Q)
    (hInt : ∀ u : Lp ℝ 2 m, u ∈ E.domain →
      Integrable rho ((Gamma.measure u).restrict Q))
    (hρ : ∀ x ∈ Q, 0 ≤ rho x)
    {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    {t : ℝ} (ht : 0 < t) :
    (∫ x in Q, rho x ∂(Gamma.measure (u + v))) ≤
      (1 + t) * (∫ x in Q, rho x ∂(Gamma.measure u)) +
        (1 + t⁻¹) * (∫ x in Q, rho x ∂(Gamma.measure v)) := by
  let a : ℝ≥0∞ := ENNReal.ofReal (1 + t)
  let b : ℝ≥0∞ := ENNReal.ofReal (1 + t⁻¹)
  have huv : u + v ∈ E.domain := E.domain.add_mem hu hv
  have hmeas := aux_prop_21_catalog_global_weighted_energy_energy_measure_add_le Gamma hu hv ht
  have hrest : (Gamma.measure (u + v)).restrict Q ≤
      (a • Gamma.measure u + b • Gamma.measure v).restrict Q :=
    Measure.restrict_mono (subset_rfl) hmeas
  have hia : Integrable rho (a • (Gamma.measure u).restrict Q) := by
    exact (hInt u hu).smul_measure (by simp [a])
  have hib : Integrable rho (b • (Gamma.measure v).restrict Q) := by
    exact (hInt v hv).smul_measure (by simp [b])
  have hir : Integrable rho ((a • Gamma.measure u + b • Gamma.measure v).restrict Q) := by
    rw [Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul]
    exact hia.add_measure hib
  have hnonneg : ∀ᵐ x ∂((a • Gamma.measure u + b • Gamma.measure v).restrict Q),
      0 ≤ rho x := by
    filter_upwards [ae_restrict_mem hQ] with x hx
    exact hρ x hx
  have hmono := integral_mono_measure hrest hnonneg hir
  rw [Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul,
    integral_add_measure hia hib, integral_smul_measure, integral_smul_measure] at hmono
  have ha0 : 0 ≤ 1 + t := by linarith
  have hb0 : 0 ≤ 1 + t⁻¹ := by positivity
  simpa [a, b, ENNReal.toReal_ofReal ha0, ENNReal.toReal_ofReal hb0] using hmono

lemma aux_prop_21_catalog_global_weighted_energy_form_sub_sqrt_bound
    {X : Type*} [MeasurableSpace X] {m : Measure X}
    (E : DirichletForm.ClosedForm m) {a b c : Lp ℝ 2 m}
    (ha : a ∈ E.domain) (hb : b ∈ E.domain) (hc : c ∈ E.domain) :
    E.form (a - b) (a - b) ≤
      (Real.sqrt (E.form (a - c) (a - c)) +
        Real.sqrt (E.form (b - c) (b - c))) ^ 2 := by
  let x : Lp ℝ 2 m := a - c
  let y : Lp ℝ 2 m := b - c
  have hx : x ∈ E.domain := by
    dsimp [x]
    exact E.domain.sub_mem ha hc
  have hy : y ∈ E.domain := by
    dsimp [y]
    exact E.domain.sub_mem hb hc
  have hab : a - b = x - y := by
    dsimp [x, y]
    abel
  have hxy := E.form_add_smul_self (-1) hx hy
  have hcross := E.abs_form_le hx hy
  have hxn : 0 ≤ E.form x x := E.form_nonneg x hx
  have hyn : 0 ≤ E.form y y := E.form_nonneg y hy
  have hsx : Real.sqrt (E.form x x) ^ 2 = E.form x x := Real.sq_sqrt hxn
  have hsy : Real.sqrt (E.form y y) ^ 2 = E.form y y := Real.sq_sqrt hyn
  calc
    E.form (a - b) (a - b) = E.form (x - y) (x - y) := by rw [hab]
    _ = E.form (x + (-1 : ℝ) • y) (x + (-1 : ℝ) • y) := by
      rw [neg_one_smul, sub_eq_add_neg]
    _ = E.form x x + 2 * (-1 : ℝ) * E.form x y + (-1 : ℝ) ^ 2 * E.form y y := hxy
    _ = E.form x x - 2 * E.form x y + E.form y y := by ring
    _ ≤ E.form x x + 2 * (Real.sqrt (E.form x x) * Real.sqrt (E.form y y)) +
      E.form y y := by
        have hformle : E.form x y ≤ |E.form x y| := le_abs_self _
        have hneg : -E.form x y ≤ |E.form x y| := neg_le_abs _
        linarith [hcross, hformle, hneg]
    _ = (Real.sqrt (E.form x x) + Real.sqrt (E.form y y)) ^ 2 := by
      calc
        E.form x x + 2 * (Real.sqrt (E.form x x) * Real.sqrt (E.form y y)) +
              E.form y y =
            (Real.sqrt (E.form x x)) ^ 2 +
              2 * (Real.sqrt (E.form x x) * Real.sqrt (E.form y y)) +
              (Real.sqrt (E.form y y)) ^ 2 := by rw [hsx, hsy]
        _ = (Real.sqrt (E.form x x) + Real.sqrt (E.form y y)) ^ 2 := by ring

lemma aux_prop_21_catalog_global_weighted_energy_form_cauchy
    {X : Type*} [MeasurableSpace X] {m : Measure X}
    (F : DirichletForm.ClosedForm m) (M : ℝ) (s : ℕ → ℝ)
    (p : ℕ → Lp ℝ 2 m) (hMnonneg : 0 ≤ M)
    (hspos : ∀ n, 0 < s n) (hs_tendsto : Tendsto s atTop (𝓝 0))
    (hFformdiff : ∀ n m,
      F.form (p n - p m) (p n - p m) ≤
        M * (Real.sqrt ((s n) ^ 4) + Real.sqrt ((s m) ^ 4)) ^ 2) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      F.form (p n - p m) (p n - p m) < ε := by
  intro ε hε
  let η : ℝ := min 1 (ε / (16 * (M + 1)))
  have hη0 : 0 ≤ η := le_min (by norm_num) (by positivity)
  have hηpos : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : 16 * (M + 1) * η ≤ ε := by
    have htmp := min_le_right (1 : ℝ) (ε / (16 * (M + 1)))
    have htmp' := (le_div_iff₀ (by positivity : 0 < 16 * (M + 1))).mp htmp
    simpa [η, mul_comm, mul_left_comm, mul_assoc] using htmp'
  have hev : ∀ᶠ n in atTop, s n < η :=
    hs_tendsto.eventually (eventually_lt_nhds hηpos)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, ?_⟩
  intro n hnN m hmN
  have hn' := hN n hnN
  have hm' := hN m hmN
  have hsn0 : 0 ≤ s n := (hspos n).le
  have hsm0 : 0 ≤ s m := (hspos m).le
  have hn2a : (s n) ^ 2 ≤ s n * η := by
    simpa [pow_two] using mul_le_mul_of_nonneg_left (le_of_lt hn') hsn0
  have hn2b : s n * η ≤ η * η := by
    exact mul_le_mul_of_nonneg_right (le_of_lt hn') hη0
  have hηsqMul : η * η ≤ η := by
    have h := mul_le_mul_of_nonneg_left hη1 hη0
    simpa using h
  have hηsq : η ^ 2 ≤ η := by simpa [pow_two] using hηsqMul
  have hn2 : (s n) ^ 2 ≤ η := by
    calc
      (s n) ^ 2 ≤ s n * η := hn2a
      _ ≤ η * η := hn2b
      _ ≤ η := hηsqMul
  have hm2a : (s m) ^ 2 ≤ s m * η := by
    simpa [pow_two] using mul_le_mul_of_nonneg_left (le_of_lt hm') hsm0
  have hm2b : s m * η ≤ η * η := by
    exact mul_le_mul_of_nonneg_right (le_of_lt hm') hη0
  have hm2 : (s m) ^ 2 ≤ η := by
    calc
      (s m) ^ 2 ≤ s m * η := hm2a
      _ ≤ η * η := hm2b
      _ ≤ η := hηsqMul
  have hsqn : Real.sqrt ((s n) ^ 4) = (s n) ^ 2 := by
    rw [show (s n) ^ 4 = ((s n) ^ 2) ^ 2 by ring,
      Real.sqrt_sq (sq_nonneg _)]
  have hsqm : Real.sqrt ((s m) ^ 4) = (s m) ^ 2 := by
    rw [show (s m) ^ 4 = ((s m) ^ 2) ^ 2 by ring,
      Real.sqrt_sq (sq_nonneg _)]
  have hfd := hFformdiff n m
  rw [hsqn, hsqm] at hfd
  have hsum : (s n) ^ 2 + (s m) ^ 2 ≤ 2 * η := by linarith
  have hsum0 : 0 ≤ (s n) ^ 2 + (s m) ^ 2 := by positivity
  have htwo0 : 0 ≤ 2 * η := by positivity
  have hsum_sq : ((s n) ^ 2 + (s m) ^ 2) ^ 2 ≤ (2 * η) ^ 2 :=
    (sq_le_sq₀ hsum0 htwo0).2 hsum
  have hprod4 : 4 * M * η ≤ ε / 4 := by
    have hcoef : 4 * M ≤ 4 * (M + 1) := by linarith
    have hfirst : 4 * M * η ≤ 4 * (M + 1) * η :=
      mul_le_mul_of_nonneg_right hcoef hη0
    have hsecond : 4 * (M + 1) * η ≤ ε / 4 := by
      nlinarith [hηε]
    exact hfirst.trans hsecond
  have hprod : 4 * M * η < ε := hprod4.trans_lt (by linarith)
  have hbound : M * ((s n) ^ 2 + (s m) ^ 2) ^ 2 < ε := by
    calc
      M * ((s n) ^ 2 + (s m) ^ 2) ^ 2 ≤ M * (2 * η) ^ 2 :=
        mul_le_mul_of_nonneg_left hsum_sq hMnonneg
      _ = 4 * M * η ^ 2 := by ring
      _ ≤ 4 * M * η := by
        have h4M : 0 ≤ 4 * M := by positivity
        have hmul := mul_le_mul_of_nonneg_left hηsq h4M
        change (4 * M) * η ^ 2 ≤ (4 * M) * η
        exact hmul
      _ < ε := hprod
  exact hfd.trans_lt hbound



theorem prop_21_catalog_global_weighted_energy
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    {Q : Opens (SpatialCoordinates d)}
    (hQcube : Q = centeredCube z0 R hR)
    (E F : DirichletForm.ClosedForm
      (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GE GF : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hEform : ∀ w : DomainL2 Q, E.energy w = limitFormEnergy GE w)
    (hFform : ∀ w : DomainL2 Q, F.energy w = limitFormEnergy GF w)
    (GammaE : DirichletForm.EnergyMeasure E)
    (GammaF : DirichletForm.EnergyMeasure F)
    (rho : SpatialCoordinates d → ℝ)
    (hrhocont : ContinuousOn rho (closure (Q : Set (SpatialCoordinates d))))
    (hrhopos : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), 0 < rho x)
    (hFdomainEq : limitFormDomain GF = limitFormDomain GE)
    (hFdomain : ∀ w : DomainL2 Q, MemFormCore GE w → w ∈ F.domain)
    (hmeasure : ∀ (zq : SpatialCoordinates d) (rq : ℝ) (hrq : 0 < rq),
      (∀ i : Fin d, ∃ s : ℚ, zq i = (s : ℝ)) →
      (∃ k : ℤ, rq = (3 : ℝ) ^ k) →
      (centeredCube zq rq hrq : Set (SpatialCoordinates d)) ⊆
        (Q : Set (SpatialCoordinates d)) →
      ∀ w : DomainL2 Q, MemFormCore GE w →
      ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
        B ⊆ (centeredCube zq rq hrq : Set (SpatialCoordinates d)) →
        sInf (rho '' (centeredCube zq rq hrq : Set (SpatialCoordinates d))) *
            (GammaE.measure w B).toReal ≤
            (GammaF.measure w B).toReal ∧
          (GammaF.measure w B).toReal ≤
            sSup (rho '' (centeredCube zq rq hrq : Set (SpatialCoordinates d))) *
              (GammaE.measure w B).toReal)
    (hdense : ∀ w ∈ limitFormDomain GE, ∀ ε : ℝ, 0 < ε →
      ∃ p : DomainL2 Q, MemFormCore GE p ∧ ‖p - w‖ ≤ ε ∧
        limitFormEnergy GE (p - w) ≤ ((ε : ℝ) : EReal)) :
    ∀ u ∈ limitFormDomain GE,
      limitFormEnergy GF u =
        (((∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure u)) : ℝ)
          : EReal) := by
  intro u hu
  have huE : u ∈ E.domain := by
    apply E.mem_domain_of_energy_lt_top
    rw [hEform]
    exact hu
  have huGF : u ∈ limitFormDomain GF := hFdomainEq.symm ▸ hu
  have huF : u ∈ F.domain := by
    apply F.mem_domain_of_energy_lt_top
    rw [hFform]
    exact huGF
  have hQcompact : IsCompact (closure (Q : Set (SpatialCoordinates d))) := by
    rw [hQcube, centeredCube]
    change IsCompact (closure (Metric.ball z0 (R / 2)))
    rw [closure_ball _ (by positivity)]
    exact ProperSpace.isCompact_closedBall z0 (R / 2)
  have hQmeas : MeasurableSet (Q : Set (SpatialCoordinates d)) := Q.isOpen.measurableSet
  have hGammaEint : ∀ v : DomainL2 Q, v ∈ E.domain →
      Integrable rho ((GammaE.measure v).restrict (Q : Set (SpatialCoordinates d))) := by
    intro v hv
    let μ : Measure (SpatialCoordinates d) := GammaE.measure v
    letI : IsFiniteMeasure μ := ⟨by simpa [μ] using GammaE.measure_univ_lt_top v hv⟩
    letI : IsFiniteMeasureOnCompacts μ :=
      ⟨fun {C} hC => lt_of_le_of_lt (measure_mono (Set.subset_univ C))
        (measure_lt_top μ Set.univ)⟩
    have hS : IntegrableOn rho (closure (Q : Set (SpatialCoordinates d))) μ :=
      hrhocont.integrableOn_compact hQcompact
    change Integrable rho (μ.restrict (closure (Q : Set (SpatialCoordinates d)))) at hS
    have hrest : μ.restrict (Q : Set (SpatialCoordinates d)) ≤
        μ.restrict (closure (Q : Set (SpatialCoordinates d))) :=
      Measure.restrict_mono subset_closure le_rfl
    simpa [μ] using hS.mono_measure hrest
  have hρnonneg : ∀ x ∈ (Q : Set (SpatialCoordinates d)), 0 ≤ rho x := by
    intro x hx
    exact (hrhopos x (subset_closure hx)).le
  have hBdd : BddAbove (rho '' closure (Q : Set (SpatialCoordinates d))) :=
    hQcompact.bddAbove_image hrhocont
  have hQnonempty : (Q : Set (SpatialCoordinates d)).Nonempty := by
    rw [hQcube, centeredCube]
    exact Metric.nonempty_ball.mpr (by positivity)
  let M : ℝ := sSup (rho '' closure (Q : Set (SpatialCoordinates d)))
  have hM : ∀ x ∈ (Q : Set (SpatialCoordinates d)), rho x ≤ M := by
    intro x hx
    exact le_csSup hBdd ⟨x, subset_closure hx, rfl⟩
  have hMnonneg : 0 ≤ M := by
    obtain ⟨x, hx⟩ := hQnonempty
    exact le_trans (hρnonneg x hx) (hM x hx)
  have hI_bounds : ∀ v : DomainL2 Q, v ∈ E.domain →
      0 ≤ (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure v)) ∧
      (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure v)) ≤
        M * E.form v v := by
    intro v hv
    letI : IsFiniteMeasure (GammaE.measure v) :=
      ⟨GammaE.measure_univ_lt_top v hv⟩
    letI : IsFiniteMeasure ((GammaE.measure v).restrict (Q : Set (SpatialCoordinates d))) := inferInstance
    have hi := hGammaEint v hv
    have hnonneg : ∀ᵐ x ∂(GammaE.measure v).restrict (Q : Set (SpatialCoordinates d)),
        0 ≤ rho x := by
      filter_upwards [ae_restrict_mem hQmeas] with x hx
      exact hρnonneg x hx
    have hupper : ∀ᵐ x ∂(GammaE.measure v).restrict (Q : Set (SpatialCoordinates d)),
        rho x ≤ M := by
      filter_upwards [ae_restrict_mem hQmeas] with x hx
      exact hM x hx
    have h0 : 0 ≤ (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure v)) := by
      have h0' := integral_mono_ae (μ := (GammaE.measure v).restrict (Q : Set (SpatialCoordinates d)))
        (integrable_const 0) hi hnonneg
      simpa using h0'
    have h1 := integral_mono_ae hi (integrable_const M) hupper
    rw [integral_const, measureReal_def, smul_eq_mul] at h1
    have hmassQ : ((GammaE.measure v).restrict (Q : Set (SpatialCoordinates d)) Set.univ).toReal ≤
        (GammaE.measure v Set.univ).toReal := by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp only [Set.univ_inter]
      exact GammaE.toReal_measure_mono hv (Set.subset_univ _)
    have h1' : (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure v)) ≤
        M * E.form v v := by
      calc
        _ ≤ M * ((GammaE.measure v).restrict (Q : Set (SpatialCoordinates d)) Set.univ).toReal := by
          simpa [mul_comm] using h1
        _ ≤ M * (GammaE.measure v Set.univ).toReal :=
          mul_le_mul_of_nonneg_left hmassQ hMnonneg
        _ = M * E.form v v := by
          simpa only [GammaE.measure_univ v hv]
    exact ⟨h0, h1'⟩

  let s : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hspos : ∀ n, 0 < s n := by
    intro n
    dsimp [s]
    positivity
  have hepspos : ∀ n, 0 < (s n) ^ 4 := fun n => pow_pos (hspos n) _
  choose p hp hpnorm hpenergy using fun n => hdense u hu (s n ^ 4) (hepspos n)
  have hpE : ∀ n, p n ∈ E.domain := by
    intro n
    apply E.mem_domain_of_energy_lt_top
    rw [hEform]
    exact hp n |>.1
  have hpF : ∀ n, p n ∈ F.domain := fun n => hFdomain (p n) (hp n)
  have hdiffE : ∀ n, p n - u ∈ E.domain := fun n => E.domain.sub_mem (hpE n) huE
  have hresform : ∀ n, E.form (p n - u) (p n - u) ≤ (s n) ^ 4 := by
    intro n
    have hcoe : (E.form (p n - u) (p n - u) : EReal) ≤ ((s n) ^ 4 : ℝ) := by
      calc
        (E.form (p n - u) (p n - u) : EReal) = E.energy (p n - u) :=
          (E.energy_of_mem (hdiffE n)).symm
        _ = limitFormEnergy GE (p n - u) := hEform _
        _ ≤ ((s n) ^ 4 : ℝ) := hpenergy n
    exact_mod_cast hcoe
  have hcoreeq : ∀ n, F.form (p n) (p n) =
      ∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure (p n)) := by
    intro n
    exact aux_prop_21_catalog_global_weighted_energy_core_measure_eq z0 R hR hQcube E F GE GF hEform hFform GammaE GammaF
      rho hrhocont hrhopos hFdomain hmeasure (p n) (hp n)
  have hIres : ∀ n, (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure (p n - u))) ≤
      M * (s n) ^ 4 := by
    intro n
    exact (hI_bounds (p n - u) (hdiffE n)).2.trans (mul_le_mul_of_nonneg_left
      (hresform n) hMnonneg)
  have hdiffE' : ∀ n, u - p n ∈ E.domain := fun n => E.domain.sub_mem huE (hpE n)
  have hresform' : ∀ n, E.form (u - p n) (u - p n) ≤ (s n) ^ 4 := by
    intro n
    have hsame : E.form (u - p n) (u - p n) = E.form (p n - u) (p n - u) := by
      rw [show u - p n = -(p n - u) by rw [neg_sub]]
      rw [E.form_neg_left (hdiffE n) (E.domain.neg_mem (hdiffE n)),
        E.form_neg_right (hdiffE n) (hdiffE n)]
      ring
    rw [hsame]
    exact hresform n
  have hIres' : ∀ n, (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure (u - p n))) ≤
      M * (s n) ^ 4 := by
    intro n
    exact (hI_bounds (u - p n) (hdiffE' n)).2.trans (mul_le_mul_of_nonneg_left
      (hresform' n) hMnonneg)
  have hs_tendsto : Tendsto s atTop (𝓝 0) := by
    simpa [s] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let A : ℕ → ℝ := fun n => M * ((s n) ^ 4 + (s n) ^ 3)
  have hA_tendsto : Tendsto A atTop (𝓝 0) := by
    have h34 : Tendsto (fun n => (s n) ^ 4 + (s n) ^ 3) atTop (𝓝 0) := by
      simpa using (hs_tendsto.pow 4).add (hs_tendsto.pow 3)
    simpa [A] using h34.const_mul M
  have hI_tendsto : Tendsto
      (fun n => ∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure (p n)))
      atTop (𝓝 (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure u)) ) := by
    let Iu : ℝ := ∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure u)
    have hupper : ∀ n,
        (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure (p n))) ≤
          (1 + s n) * Iu + A n := by
      intro n
      have hh := aux_prop_21_catalog_global_weighted_energy_weighted_measure_add_le GammaE (Q : Set (SpatialCoordinates d))
        rho hQmeas hGammaEint hρnonneg huE (hdiffE n) (hspos n)
      have hmul : (1 + (s n)⁻¹) * (M * (s n) ^ 4) = A n := by
        dsimp [A]
        field_simp [ne_of_gt (hspos n)]
      have hh' : (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure (u + (p n - u)))) ≤
          (1 + s n) * Iu + (1 + (s n)⁻¹) *
            (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure (p n - u))) := by
        simpa [Iu] using hh
      have hcoef : 0 ≤ 1 + (s n)⁻¹ := by positivity
      have := add_le_add_left (mul_le_mul_of_nonneg_left (hIres n) hcoef) ((1 + s n) * Iu)
      rw [hmul] at this
      have heq : u + (p n - u) = p n := by abel
      rw [heq] at hh'
      linarith
    have hlower : ∀ n,
        (Iu - A n) / (1 + s n) ≤
          (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure (p n))) := by
      intro n
      have hh := aux_prop_21_catalog_global_weighted_energy_weighted_measure_add_le GammaE (Q : Set (SpatialCoordinates d))
        rho hQmeas hGammaEint hρnonneg (hpE n) (hdiffE' n) (hspos n)
      have hmul : (1 + (s n)⁻¹) * (M * (s n) ^ 4) = A n := by
        dsimp [A]
        field_simp [ne_of_gt (hspos n)]
      have hh' : Iu ≤ (1 + s n) *
          (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure (p n))) +
          (1 + (s n)⁻¹) *
            (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure (u - p n))) := by
        have heq : p n + (u - p n) = u := by abel
        simpa [Iu, heq] using hh
      have hcoef : 0 ≤ 1 + (s n)⁻¹ := by positivity
      have hA := add_le_add_left (mul_le_mul_of_nonneg_left (hIres' n) hcoef)
        ((1 + s n) * (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure (p n))))
      rw [hmul] at hA
      apply (div_le_iff₀ (by positivity : 0 < 1 + s n)).2
      linarith [hh', hA]
    have hden : Tendsto (fun n => 1 + s n) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.add hs_tendsto)
    have hupper' : Tendsto (fun n => (1 + s n) * Iu + A n) atTop (𝓝 Iu) := by
      simpa using (hden.mul_const Iu).add hA_tendsto
    have hlower' : Tendsto (fun n => (Iu - A n) / (1 + s n)) atTop (𝓝 Iu) := by
      simpa using! (tendsto_const_nhds.sub hA_tendsto).div hden (by norm_num)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower' hupper'
    · exact hlower
    · exact hupper
  have hpL2 : Tendsto p atTop (𝓝 u) := by
    have hn : Tendsto (fun n => ‖p n - u‖) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => norm_nonneg _) hpnorm ?_
      simpa using hs_tendsto.pow 4
    rw [tendsto_iff_dist_tendsto_zero]
    simpa [dist_eq_norm] using hn
  have hFformdiff : ∀ n m,
      F.form (p n - p m) (p n - p m) ≤
        M * (Real.sqrt ((s n) ^ 4) + Real.sqrt ((s m) ^ 4)) ^ 2 := by
    intro n m
    have hcore : MemFormCore GE (p n - p m) :=
      aux_prop_21_catalog_global_weighted_energy_core_sub E GE hEform (p n) (p m)
        (hp n) (hp m)
    have hsubE : p n - p m ∈ E.domain := E.domain.sub_mem (hpE n) (hpE m)
    have hfm := aux_prop_21_catalog_global_weighted_energy_core_measure_eq z0 R hR hQcube E F GE GF hEform hFform GammaE
      GammaF rho hrhocont hrhopos hFdomain hmeasure (p n - p m) hcore
    have hI := (hI_bounds (p n - p m) hsubE).2
    have hform := aux_prop_21_catalog_global_weighted_energy_form_sub_sqrt_bound E (a := p n) (b := p m) (c := u)
      (hpE n) (hpE m) huE
    calc
      F.form (p n - p m) (p n - p m) =
          ∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure (p n - p m)) := hfm
      _ ≤ M * E.form (p n - p m) (p n - p m) := hI
      _ ≤ M * (Real.sqrt (E.form (p n - u) (p n - u)) +
          Real.sqrt (E.form (p m - u) (p m - u))) ^ 2 :=
        mul_le_mul_of_nonneg_left hform hMnonneg
      _ ≤ M * (Real.sqrt ((s n) ^ 4) + Real.sqrt ((s m) ^ 4)) ^ 2 := by
        have hn := Real.sqrt_le_sqrt (hresform n)
        have hm := Real.sqrt_le_sqrt (hresform m)
        have hsum := add_le_add hn hm
        have hsum0 : 0 ≤ Real.sqrt (E.form (p n - u) (p n - u)) +
            Real.sqrt (E.form (p m - u) (p m - u)) := by positivity
        have hsum'0 : 0 ≤ Real.sqrt ((s n) ^ 4) + Real.sqrt ((s m) ^ 4) := by
          positivity
        have hsq := (sq_le_sq₀ hsum0 hsum'0).2 hsum
        exact mul_le_mul_of_nonneg_left hsq hMnonneg
  have hFcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      F.form (p n - p m) (p n - p m) < ε :=
    aux_prop_21_catalog_global_weighted_energy_form_cauchy F M s p hMnonneg hspos
      hs_tendsto hFformdiff
  have hFclosed := F.mem_domain_of_tendsto_of_formCauchy p hpF u hpL2 hFcauchy
  have hFenergyconv := hFclosed.2
  have hFself := F.tendsto_form_self_of_tendsto_energyNormSq hpF huF hFenergyconv
  have hFweighted : Tendsto
      (fun n => ∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure (p n))) atTop
      (𝓝 (F.form u u)) := by
    exact hFself.congr hcoreeq
  have hweighted_eq : F.form u u =
      ∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure u) :=
    tendsto_nhds_unique hFweighted hI_tendsto
  calc
    limitFormEnergy GF u = F.energy u := (hFform u).symm
    _ = (F.form u u : EReal) := F.energy_of_mem huF
    _ = (((∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(GammaE.measure u)) : ℝ) : EReal) :=
      congrArg (fun x : ℝ => (x : EReal)) hweighted_eq

end Paper
