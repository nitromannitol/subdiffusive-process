module

public import SubdiffusiveProcess.GoodCube.RobustAssembly
public import SubdiffusiveProcess.Section9.WeightedMultiscalePercolation
public import SubdiffusiveProcess.Section9.WeightedGoodCubeEvents
public import SubdiffusiveProcess.Section9.WeightedLocalTorsion
public import SubdiffusiveProcess.Section9.WeightedPathDiscretization
public import SubdiffusiveProcess.Section9.WeightedChronologicalSelection
public import SubdiffusiveProcess.Section8.LocalTorsionSurvival
public import SubdiffusiveProcess.Section8.CommonSemigroupCrossing
public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.Main.CutoffSpeedMeasure
public import SubdiffusiveProcess.Main.CutoffSpeedDensity
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.WeightedChaosCutoff
public import SubdiffusiveProcess.Main.ChaosCutoff
public import SubdiffusiveProcess.Main.ConditionalFineFiltration
public import SubdiffusiveProcess.Main.MeasuresConvergeLocally
public import SubdiffusiveProcess.Main.SemigroupSymmetric
public import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
public import SubdiffusiveProcess.Main.HasStrongMarkovRestart
public import SubdiffusiveProcess.Main.HasFiniteMeanExits
public import SubdiffusiveProcess.Main.PathLevyProkhorovDist
public import SubdiffusiveProcess.Main.PhysicalRescaledPath
public import SubdiffusiveProcess.Main.PhysicalTimeFactor
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.DiffusionPath
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.Sobolev.ResponseSpace
public import SubdiffusiveProcess.ResponseMoments.DirichletForm
public import SubdiffusiveProcess.VariationalResponses.KilledInverse
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Probability.CubeMassMartingale
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Inputs.MarkovProcesses
public import MarkovProcess.Trajectory.StoppingLtTop
public import MarkovProcess.Path.ExitTime
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import SubdiffusiveProcess.Vocab.Ahom
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.in_timescale
public import SubdiffusiveProcess.Paper.physical_rescaling
public import SubdiffusiveProcess.Paper.physical_generator_reindexing
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import MarkovProcess.Lifetime.Law
public import SubdiffusiveProcess.Paper.finiteDimensional_cutoff
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedChronologicalSelectionRun
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeTranslation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
public import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedProviders
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellSummable
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GoodSetMeasurable

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped Pointwise

namespace SubdiffusiveProcess.Paper

/-- The sup-distance path event `∃ s ≤ u, R ≤ dist (path s) x` is closed, hence
measurable, in the compact-open topology of continuous paths. -/
theorem aux_lem_crossing_isClosed_exitEvent {d : ℕ} (u R : ℝ) (hu : 0 ≤ u)
    (x : SpatialCoordinates d) :
    IsClosed {path : DiffusionPath d | ∃ s : ℝ≥0, (s : ℝ) ≤ u ∧ R ≤ dist (path s) x} := by
  let K : Set ℝ≥0 := Set.Icc 0 (Real.toNNReal u)
  have : CompactSpace K := isCompact_iff_compactSpace.mp isCompact_Icc
  let F : DiffusionPath d × K → ℝ := fun p => dist (p.1 (p.2 : ℝ≥0)) x
  have hF : Continuous F := by
    have h1 : Continuous (fun p : DiffusionPath d × K => p.1 (p.2 : ℝ≥0)) :=
      continuous_eval.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    exact h1.dist continuous_const
  have hclosed : IsClosed {p : DiffusionPath d × K | R ≤ F p} :=
    isClosed_le continuous_const hF
  have himage := isClosedMap_fst_of_compactSpace _ hclosed
  convert himage using 1
  ext path
  simp only [Set.mem_ofPred_eq, Set.mem_image, Prod.exists, F, K]
  constructor
  · rintro ⟨s, hs, hR⟩
    refine ⟨path, ⟨s, ?_⟩, hR, rfl⟩
    refine ⟨zero_le, ?_⟩
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu]
    exact hs
  · rintro ⟨p, ⟨s, hsK⟩, hR, rfl⟩
    refine ⟨s, ?_, hR⟩
    have := hsK.2
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu] at this
    exact this

theorem aux_lem_crossing_measurableSet_exitEvent {d : ℕ} (u R : ℝ) (hu : 0 ≤ u)
    (x : SpatialCoordinates d) :
    MeasurableSet {path : DiffusionPath d | ∃ s : ℝ≥0, (s : ℝ) ≤ u ∧ R ≤ dist (path s) x} :=
  (aux_lem_crossing_isClosed_exitEvent u R hu x).measurableSet


/-- The physical (cutoff-zero) conjunct of `lem_crossing`, verbatim, at fixed
constants. -/
def aux_lem_crossing_physical {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (c C q : ℝ) (Tscale : ℝ → ℝ) : Prop :=
  ∀ (Region : Set (SpatialCoordinates d)), Bornology.IsBounded Region →
    ∀ (r R : ℝ), 1 ≤ r → C * r ≤ R →
      ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
        (chaosSampleLaw M).toMeasure Bad ≤
          ENNReal.ofReal (C * (1 + Metric.diam Region / r) ^ d *
            Real.exp (-(c * q * R / r))) ∧
        ∀ omega, omega ∉ Bad → ∀ x ∈ Region, ∀ u : ℝ, 0 < u →
          (KN 0 (omega, x))
              {path : DiffusionPath d |
                ∃ s : ℝ≥0, (s : ℝ) ≤ SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 * u ∧
                  R ≤ dist (path s) x} ≤
            ENNReal.ofReal (C * Real.exp (C * u / Tscale r - c * R / r))

/-- The transported (cutoff-`N`) conjunct of `lem_crossing`, verbatim, at fixed
constants. -/
def aux_lem_crossing_transported {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (c C q : ℝ) (Tscale : ℝ → ℝ) : Prop :=
  ∀ (N : ℕ) (Region : Set (SpatialCoordinates d)), Bornology.IsBounded Region →
    ∀ (r R : ℝ), (3 : ℝ) ^ (-(N : ℝ)) ≤ r → C * r ≤ R →
      ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
        (chaosSampleLaw M).toMeasure Bad ≤
          ENNReal.ofReal (C * (1 + Metric.diam Region / r) ^ d *
            Real.exp (-(c * q * R / r))) ∧
        ∀ omega, omega ∉ Bad → ∀ x ∈ Region, ∀ u : ℝ, 0 < u →
          (KN N (omega, x))
              {path : DiffusionPath d |
                ∃ s : ℝ≥0, (s : ℝ) ≤ u ∧ R ≤ dist (path s) x} ≤
            ENNReal.ofReal (C * Real.exp (C * u * Tscale ((3 : ℝ) ^ N) /
              Tscale ((3 : ℝ) ^ N * r) - c * R / r))

/-- The reindexing of the physical layers used by `physical_rescaling`. -/
def aux_lem_crossing_sigma {d : ℕ} (N : ℕ) (omega : BilateralField d) : BilateralField d :=
  fun j => SubdiffusiveProcess.layerScaling d (-(N : ℤ)) (omega (j + (N : ℤ)))

/-- Its inverse. -/
def aux_lem_crossing_sigmaInv {d : ℕ} (N : ℕ) (omega : BilateralField d) : BilateralField d :=
  fun j => SubdiffusiveProcess.layerScaling d (N : ℤ) (omega (j - (N : ℤ)))

theorem aux_lem_crossing_sigma_apply {d : ℕ} (N : ℕ) (omega : BilateralField d) (j : ℤ)
    (x : SpatialCoordinates d) :
    aux_lem_crossing_sigma N omega j x = omega (j + (N : ℤ)) (((3 : ℝ) ^ N) • x) := by
  simp only [aux_lem_crossing_sigma, SubdiffusiveProcess.layerScaling,
    ContinuousMap.compRightContinuousMap_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk]
  congr 2
  rw [neg_neg, zpow_natCast]

theorem aux_lem_crossing_sigma_sigmaInv {d : ℕ} (N : ℕ) (omega : BilateralField d) :
    aux_lem_crossing_sigma N (aux_lem_crossing_sigmaInv N omega) = omega := by
  funext j
  apply ContinuousMap.ext
  intro x
  rw [aux_lem_crossing_sigma_apply]
  simp only [aux_lem_crossing_sigmaInv, SubdiffusiveProcess.layerScaling,
    ContinuousMap.compRightContinuousMap_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, add_sub_cancel_right, smul_smul]
  have h3 : (3 : ℝ) ^ (-(N : ℤ)) * (3 : ℝ) ^ N = 1 := by
    rw [zpow_neg, zpow_natCast]
    exact inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))
  rw [h3, one_smul]

theorem aux_lem_crossing_sigmaInv_sigma {d : ℕ} (N : ℕ) (omega : BilateralField d) :
    aux_lem_crossing_sigmaInv N (aux_lem_crossing_sigma N omega) = omega := by
  funext j
  apply ContinuousMap.ext
  intro x
  simp only [aux_lem_crossing_sigmaInv, SubdiffusiveProcess.layerScaling,
    ContinuousMap.compRightContinuousMap_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk]
  rw [aux_lem_crossing_sigma_apply, sub_add_cancel, smul_smul]
  have h3 : (3 : ℝ) ^ N * (3 : ℝ) ^ (-(N : ℤ)) = 1 := by
    rw [zpow_neg, zpow_natCast]
    exact mul_inv_cancel₀ (pow_ne_zero _ (by norm_num))
  rw [h3, one_smul]

theorem aux_lem_crossing_measurable_sigmaInv {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (N : ℕ) : Measurable (aux_lem_crossing_sigmaInv (d := d) N) := by
  refine measurable_pi_iff.mpr (fun j => ?_)
  exact (SubdiffusiveProcess.layerScaling d (N : ℤ)).continuous.measurable.comp
    (measurable_pi_apply (j - (N : ℤ)))

theorem aux_lem_crossing_measurable_sigma {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (N : ℕ) : Measurable (aux_lem_crossing_sigma (d := d) N) := by
  refine measurable_pi_iff.mpr (fun j => ?_)
  exact (SubdiffusiveProcess.layerScaling d (-(N : ℤ))).continuous.measurable.comp
    (measurable_pi_apply (j + (N : ℤ)))

/-- **Transport.**  The physical conjunct implies the transported conjunct, by
`physical_rescaling` (measure preservation of the reindexing and the a.e. path
law identity), with the exceptional set pulled back along the inverse
reindexing and enlarged only by a measurable null set. -/
theorem aux_lem_crossing_transport
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (c C q : ℝ) (Tscale : ℝ → ℝ)
    (hT : ∀ m : ℕ, Tscale ((3 : ℝ) ^ m) =
      ((3 : ℝ) ^ (2 * m) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M m))
    (hphys : aux_lem_crossing_physical M KN c C q Tscale) :
    aux_lem_crossing_transported M KN c C q Tscale := by
  obtain ⟨hmp, hlaw, -⟩ := _root_.SubdiffusiveProcess.Paper.physical_rescaling hd M H hH PN KN hKN hin
    (fun N => aux_lem_crossing_sigma N) (fun N omega j x => aux_lem_crossing_sigma_apply N omega j x)
  intro N Region hRegion r R hr hRr
  set μ := (chaosSampleLaw M).toMeasure with hμ
  set S : ℝ := (3 : ℝ) ^ N with hS
  have hSpos : 0 < S := pow_pos (by norm_num) N
  have hSr : 1 ≤ S * r := by
    have h1 : S * (3 : ℝ) ^ (-(N : ℝ)) = 1 := by
      rw [hS, Real.rpow_neg (by norm_num), Real.rpow_natCast]
      exact mul_inv_cancel₀ (pow_ne_zero _ (by norm_num))
    calc (1 : ℝ) = S * (3 : ℝ) ^ (-(N : ℝ)) := h1.symm
      _ ≤ S * r := mul_le_mul_of_nonneg_left hr hSpos.le
  have hrpos : 0 < r := by
    have : 0 < (3 : ℝ) ^ (-(N : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    linarith
  have hSR : C * (S * r) ≤ S * R := by nlinarith
  obtain ⟨Bad0, hBad0m, hBad0μ, hBad0⟩ :=
    hphys (S • Region) (hRegion.smul₀ S) (S * r) (S * R) hSr hSR
  -- the full-measure set on which the path-law transport holds
  set G : Set (BilateralField d) := {omega | ∀ x : SpatialCoordinates d,
      Measure.map (physicalRescaledPath M N) (KN 0 (omega, (3 : ℝ) ^ N • x)) =
        KN N (aux_lem_crossing_sigma N omega, x)} with hG
  have hGc : μ Gᶜ = 0 := by
    have := hlaw N
    rw [ae_iff] at this
    convert this using 2 ; rfl
  set Null := toMeasurable μ Gᶜ with hNull
  have hNullm : MeasurableSet Null := measurableSet_toMeasurable μ Gᶜ
  have hNullμ : μ Null = 0 := by rw [hNull, measure_toMeasurable]; exact hGc
  refine ⟨aux_lem_crossing_sigmaInv N ⁻¹' (Bad0 ∪ Null),
    (aux_lem_crossing_measurable_sigmaInv N) (hBad0m.union hNullm), ?_, ?_⟩
  · -- measure bound: the inverse reindexing is measure preserving
    have hmpInv : MeasurePreserving (aux_lem_crossing_sigmaInv (d := d) N) μ μ := by
      refine ⟨aux_lem_crossing_measurable_sigmaInv N, ?_⟩
      have h := (hmp N).map_eq
      calc Measure.map (aux_lem_crossing_sigmaInv N) μ
          = Measure.map (aux_lem_crossing_sigmaInv N)
              (Measure.map (aux_lem_crossing_sigma N) μ) := by rw [h]
        _ = Measure.map (aux_lem_crossing_sigmaInv N ∘ aux_lem_crossing_sigma N) μ := by
              rw [Measure.map_map (aux_lem_crossing_measurable_sigmaInv N)
                (aux_lem_crossing_measurable_sigma N)]
        _ = μ := by
              have : (aux_lem_crossing_sigmaInv (d := d) N ∘ aux_lem_crossing_sigma N) = id := by
                funext omega; exact aux_lem_crossing_sigmaInv_sigma N omega
              rw [this, Measure.map_id]
    rw [hmpInv.measure_preimage (hBad0m.union hNullm).nullMeasurableSet]
    calc μ (Bad0 ∪ Null) ≤ μ Bad0 + μ Null := measure_union_le _ _
      _ = μ Bad0 := by rw [hNullμ, add_zero]
      _ ≤ _ := by
        refine hBad0μ.trans (le_of_eq ?_)
        congr 1
        have hdiam : Metric.diam (S • Region) = S * Metric.diam Region := by
          rw [diam_smul₀, Real.norm_eq_abs, abs_of_pos hSpos]
        rw [hdiam]
        have h1 : S * Metric.diam Region / (S * r) = Metric.diam Region / r := by
          field_simp
        have h2 : c * q * (S * R) / (S * r) = c * q * R / r := by
          field_simp
        rw [h1, h2]
  · intro omega homega x hx u hu
    set omega0 := aux_lem_crossing_sigmaInv N omega with homega0
    have h0 : omega0 ∉ Bad0 ∪ Null := homega
    have h0Bad : omega0 ∉ Bad0 := fun h => h0 (Or.inl h)
    have h0G : omega0 ∈ G := by
      by_contra hcon
      exact h0 (Or.inr (subset_toMeasurable μ Gᶜ hcon))
    have hlawx := h0G x
    rw [aux_lem_crossing_sigma_sigmaInv] at hlawx
    rw [← hlawx]
    have hTS : Tscale S = S ^ 2 / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N := by
      rw [hS, hT N, pow_mul, pow_right_comm]
    have hahomN := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
    have hahom0 := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M 0
    have hTSpos : 0 < Tscale S := by rw [hTS]; positivity
    set u' := Tscale S * u with hu'
    have hu'pos : 0 < u' := mul_pos hTSpos hu
    have hxS : S • x ∈ S • Region := Set.smul_mem_smul_set hx
    have hbound := hBad0 omega0 h0Bad (S • x) hxS u' hu'pos
    have hcontP : Continuous (physicalRescaledPath M N) := by
      unfold physicalRescaledPath
      exact (continuous_const_smul _).comp
        (ContinuousMap.continuous_precomp
          (⟨fun t : ℝ≥0 => physicalTimeFactor M N * t,
            continuous_const.mul continuous_id⟩ : C(ℝ≥0, ℝ≥0)))
    rw [Measure.map_apply hcontP.measurable (aux_lem_crossing_measurableSet_exitEvent u R hu.le x)]
    refine le_trans (measure_mono ?_) (hbound.trans (le_of_eq ?_))
    · intro path hpath
      obtain ⟨s, hs, hRs⟩ := hpath
      refine ⟨physicalTimeFactor M N * s, ?_, ?_⟩
      · have hlam : ((physicalTimeFactor M N : ℝ≥0) : ℝ) =
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 * (3 : ℝ) ^ (2 * N) /
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M N := rfl
        rw [NNReal.coe_mul, hlam, hu', hTS]
        have hs0 : (0 : ℝ) ≤ s := s.2
        calc SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 * (3 : ℝ) ^ (2 * N) /
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M N * (s : ℝ)
            ≤ SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 * (3 : ℝ) ^ (2 * N) /
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M N * u := by
              apply mul_le_mul_of_nonneg_left hs; positivity
          _ = SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 * (S ^ 2 / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N * u) := by
              rw [hS, ← pow_mul, mul_comm N 2]; ring
      · simp only [physicalRescaledPath, ContinuousMap.smul_apply, ContinuousMap.comp_apply,
          ContinuousMap.coe_mk] at hRs
        have hx' : x = ((3 : ℝ)⁻¹ ^ N) • (S • x) := by
          rw [smul_smul, hS, ← mul_pow, inv_mul_cancel₀ (by norm_num : (3 : ℝ) ≠ 0), one_pow,
            one_smul]
        rw [hx', dist_smul₀] at hRs
        have hnorm : ‖(3 : ℝ)⁻¹ ^ N‖ = S⁻¹ := by
          rw [norm_pow, norm_inv, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3), hS,
            inv_pow]
        rw [hnorm] at hRs
        have := mul_le_mul_of_nonneg_left hRs hSpos.le
        rw [← mul_assoc, mul_inv_cancel₀ hSpos.ne', one_mul] at this
        exact this
    · congr 1
      have h1 : C * u' / Tscale (S * r) = C * u * Tscale S / Tscale (S * r) := by
        rw [hu']; ring
      have h2 : c * (S * R) / (S * r) = c * R / r := by field_simp
      rw [h1, h2]


/-- The physical conjunct is monotone in `C`. -/
theorem aux_lem_crossing_physical_mono {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    {c C C' q : ℝ} {Tscale : ℝ → ℝ} (hC : 0 ≤ C) (hCC' : C ≤ C')
    (hTpos : ∀ r : ℝ, 1 ≤ r → 0 < Tscale r)
    (h : aux_lem_crossing_physical M KN c C q Tscale) :
    aux_lem_crossing_physical M KN c C' q Tscale := by
  intro Region hRegion r R hr hR
  have hrpos : 0 < r := lt_of_lt_of_le one_pos hr
  obtain ⟨Bad, hBadm, hBadμ, hBad⟩ :=
    h Region hRegion r R hr (le_trans (mul_le_mul_of_nonneg_right hCC' hrpos.le) hR)
  refine ⟨Bad, hBadm, hBadμ.trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
  · have h1 : 0 ≤ (1 + Metric.diam Region / r) ^ d :=
      pow_nonneg (by have := Metric.diam_nonneg (s := Region); positivity) _
    have h2 := Real.exp_pos (-(c * q * R / r))
    have h3 : 0 ≤ (1 + Metric.diam Region / r) ^ d * Real.exp (-(c * q * R / r)) :=
      mul_nonneg h1 h2.le
    calc C * (1 + Metric.diam Region / r) ^ d * Real.exp (-(c * q * R / r))
        = C * ((1 + Metric.diam Region / r) ^ d * Real.exp (-(c * q * R / r))) := by ring
      _ ≤ C' * ((1 + Metric.diam Region / r) ^ d * Real.exp (-(c * q * R / r))) :=
          mul_le_mul_of_nonneg_right hCC' h3
      _ = C' * (1 + Metric.diam Region / r) ^ d * Real.exp (-(c * q * R / r)) := by ring
  · intro omega homega x hx u hu
    refine (hBad omega homega x hx u hu).trans (ENNReal.ofReal_le_ofReal ?_)
    have hT := hTpos r hr
    have h1 : C * u / Tscale r ≤ C' * u / Tscale r :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCC' hu.le) hT.le
    have h2 : Real.exp (C * u / Tscale r - c * R / r) ≤
        Real.exp (C' * u / Tscale r - c * R / r) :=
      Real.exp_le_exp.mpr (by linarith)
    exact mul_le_mul hCC' h2 (Real.exp_pos _).le (hC.trans hCC')

/-- **The exact typed residual**: the physical (cutoff-zero) half of
`lem_crossing`, with the same quantifier order (`cgood, delta0` before the model;
`c, C` after the model and the clock, before everything else). -/
def aux_lem_crossing_physicalResidual (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] : Prop :=
  ∃ (cgood delta0 : ℝ), 0 < cgood ∧ 0 < delta0 ∧ delta0 ≤ cgood ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
      ∀ (Tscale : ℝ → ℝ),
        (∀ m : ℕ, Tscale ((3 : ℝ) ^ m) =
          ((3 : ℝ) ^ (2 * m) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M m)) →
        (∀ (m : ℕ) (t : ℝ), 0 ≤ t → t ≤ 1 →
          Tscale ((3 : ℝ) ^ ((m : ℝ) + t))
            = ((3 : ℝ) ^ (2 * m) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M m) ^ (1 - t)
              * ((3 : ℝ) ^ (2 * (m + 1)) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M (m + 1)) ^ t) →
        ∃ (c C : ℝ), 0 < c ∧ 0 < C ∧
          ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
            (_hH : InfraredCharacterization M H)
            (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
            (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
            (_hKN : ∀ N, IsMarkovKernel (KN N))
            (_hin : in_crossing M H PN KN)
            (L : ℕ → BilateralField d →
              Kernel (SpatialCoordinates d)
                (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
            (_hL : ∀ (N : ℕ) (omega : BilateralField d) (x : SpatialCoordinates d),
              Measure.map MarkovProcess.LifetimePath.ofContinuousPath (KN N (omega, x)) =
                L N omega x)
            (_hLlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              ∀ (N : ℕ),
                SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusionData
                  (cutoffCoefficient M H omega N)
                  (cutoffSpeedDensity M H omega N)
                  (L N omega))
            (_hLstrong : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              ∀ (N : ℕ),
                SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.StrongMarkov
                  (L N omega)),
            aux_lem_crossing_physical M KN c C
              (cgood / (M.delta ^ 2 * |Real.log M.delta| ^ 2)) Tscale

/-- **Assembly.**  The exact statement of `lem_crossing` follows from the
typed physical residual, `in_timescale`, and the transport
`aux_lem_crossing_transport`. -/
theorem aux_lem_crossing_of_physicalResidual
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (hres : aux_lem_crossing_physicalResidual d) :
    ∃ (cgood delta0 : ℝ), 0 < cgood ∧ 0 < delta0 ∧ delta0 ≤ cgood ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
        ∃ (c C beta : ℝ) (Tscale : ℝ → ℝ),
          0 < c ∧ 0 < C ∧ 0 < beta ∧
          (∀ m : ℕ, Tscale ((3 : ℝ) ^ m) =
            ((3 : ℝ) ^ (2 * m) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M m)) ∧
          (∀ (m : ℕ) (t : ℝ), 0 ≤ t → t ≤ 1 →
            Tscale ((3 : ℝ) ^ ((m : ℝ) + t))
              = ((3 : ℝ) ^ (2 * m) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M m) ^ (1 - t)
                * ((3 : ℝ) ^ (2 * (m + 1)) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M (m + 1)) ^ t) ∧
          (∀ r : ℝ, 1 ≤ r → 0 < Tscale r) ∧
          (beta ≤ 2 + 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P / Real.log 3) ∧
          (∀ r S : ℝ, 1 ≤ r → r ≤ S → Tscale S ≤ C * (S / r) ^ beta * Tscale r) ∧
          (let q : ℝ := cgood / (M.delta ^ 2 * |Real.log M.delta| ^ 2)
           0 < q ∧
             ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
               (_hH : InfraredCharacterization M H)
               (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
               (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
               (_hKN : ∀ N, IsMarkovKernel (KN N))
               (_hin : in_crossing M H PN KN)
               (L : ℕ → BilateralField d →
                 Kernel (SpatialCoordinates d)
                   (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
               (_hL : ∀ (N : ℕ) (omega : BilateralField d) (x : SpatialCoordinates d),
                 Measure.map MarkovProcess.LifetimePath.ofContinuousPath (KN N (omega, x)) =
                   L N omega x)
               (_hLlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                 ∀ (N : ℕ),
                   SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusionData
                     (cutoffCoefficient M H omega N)
                     (cutoffSpeedDensity M H omega N)
                     (L N omega))
               (_hLstrong : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                 ∀ (N : ℕ),
                   SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.StrongMarkov
                     (L N omega)),
               (∀ (Region : Set (SpatialCoordinates d)), Bornology.IsBounded Region →
                 ∀ (r R : ℝ), 1 ≤ r → C * r ≤ R →
                   ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
                     (chaosSampleLaw M).toMeasure Bad ≤
                       ENNReal.ofReal (C * (1 + Metric.diam Region / r) ^ d *
                         Real.exp (-(c * q * R / r))) ∧
                     ∀ omega, omega ∉ Bad → ∀ x ∈ Region, ∀ u : ℝ, 0 < u →
                       (KN 0 (omega, x))
                           {path : DiffusionPath d |
                             ∃ s : ℝ≥0, (s : ℝ) ≤ SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 * u ∧
                               R ≤ dist (path s) x} ≤
                         ENNReal.ofReal (C * Real.exp (C * u / Tscale r - c * R / r))) ∧
               (∀ (N : ℕ) (Region : Set (SpatialCoordinates d)), Bornology.IsBounded Region →
                 ∀ (r R : ℝ), (3 : ℝ) ^ (-(N : ℝ)) ≤ r → C * r ≤ R →
                   ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
                     (chaosSampleLaw M).toMeasure Bad ≤
                       ENNReal.ofReal (C * (1 + Metric.diam Region / r) ^ d *
                         Real.exp (-(c * q * R / r))) ∧
                     ∀ omega, omega ∉ Bad → ∀ x ∈ Region, ∀ u : ℝ, 0 < u →
                       (KN N (omega, x))
                           {path : DiffusionPath d |
                             ∃ s : ℝ≥0, (s : ℝ) ≤ u ∧ R ≤ dist (path s) x} ≤
                         ENNReal.ofReal (C * Real.exp (C * u * Tscale ((3 : ℝ) ^ N) /
                           Tscale ((3 : ℝ) ^ N * r) - c * R / r)))) := by
  obtain ⟨cgood, delta0, hcg, hd0, hd0le, hM⟩ := hres
  refine ⟨cgood, delta0, hcg, hd0, hd0le, ?_⟩
  intro M hMdelta
  obtain ⟨Tscale, CT, beta, hCT, hbeta, hT3, hTint, hTpos, hbetale, hTscal⟩ :=
    _root_.SubdiffusiveProcess.Paper.in_timescale hd M
  obtain ⟨c, CP, hc, hCP, hphys⟩ := hM M hMdelta Tscale hT3 hTint
  refine ⟨c, max CT CP, beta, Tscale, hc, lt_max_of_lt_left hCT, hbeta, hT3, hTint, hTpos,
    hbetale, ?_, ?_⟩
  · intro r S hr hrS
    refine (hTscal r S hr hrS).trans ?_
    have hrpos : 0 < r := lt_of_lt_of_le one_pos hr
    have h1 : 0 ≤ (S / r) ^ beta := Real.rpow_nonneg (div_nonneg (hrpos.le.trans hrS) hrpos.le) _
    have h2 := (hTpos r hr).le
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg h1 h2)
  · have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
    have hδhalf : M.delta ≤ 1 / 2 := M.shellPrefix.delta_le_half
    have hlog : Real.log M.delta < 0 := Real.log_neg hδpos (by linarith)
    refine ⟨?_, ?_⟩
    · have : 0 < |Real.log M.delta| := abs_pos.mpr hlog.ne
      positivity
    · intro H hH PN KN hKN hin L hL hLlocal hLstrong
      have hphysM := hphys H hH PN KN hKN hin L hL hLlocal hLstrong
      have hphysC := aux_lem_crossing_physical_mono M KN hCP.le (le_max_right CT CP) hTpos hphysM
      exact ⟨hphysC, aux_lem_crossing_transport hd M H hH PN KN hKN hin c (max CT CP) _ Tscale
        hT3 hphysC⟩

end SubdiffusiveProcess.Paper

namespace SubdiffusiveProcess.Paper

/-- **Clock normalization.**  Any clock with the triadic values and log-affine
interpolation of `in_timescale` is GMC's intrinsic clock
`Section7Process.timeScale (ahom M)` on `[1, ∞)`. -/
theorem aux_lem_crossing_Tscale_eq_timeScale {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Tscale : ℝ → ℝ)
    (hT3 : ∀ m : ℕ, Tscale ((3 : ℝ) ^ m) =
      ((3 : ℝ) ^ (2 * m) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M m))
    (hTint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → t ≤ 1 →
      Tscale ((3 : ℝ) ^ ((m : ℝ) + t))
        = ((3 : ℝ) ^ (2 * m) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M m) ^ (1 - t)
          * ((3 : ℝ) ^ (2 * (m + 1)) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M (m + 1)) ^ t)
    {r : ℝ} (hr : 1 ≤ r) :
    Tscale r = SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M) r := by
  open SubdiffusiveProcess.CoarseGrainingVocab.Section7Process in
  rcases eq_or_lt_of_le hr with h1 | h1
  · subst h1
    have := hT3 0
    simp only [pow_zero, mul_zero] at this
    rw [this, timeScale_one]
  · set n := triadicIndex r with hn
    have hrpos : 0 < r := lt_trans one_pos h1
    have hlog : 0 ≤ Real.logb 3 r := Real.logb_nonneg (by norm_num) hr
    set t := Real.logb 3 r - n with ht
    have hfloor_le : (n : ℝ) ≤ Real.logb 3 r := Nat.floor_le hlog
    have hlt_floor : Real.logb 3 r < n + 1 := Nat.lt_floor_add_one _
    have ht0 : 0 ≤ t := by rw [ht]; linarith
    have ht1 : t ≤ 1 := by rw [ht]; linarith
    have hr_eq : r = (3 : ℝ) ^ ((n : ℝ) + t) := by
      rw [ht, add_sub_cancel, Real.rpow_logb (by norm_num) (by norm_num) hrpos]
    have hA : 0 < (3 : ℝ) ^ (2 * n) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M n :=
      div_pos (by positivity) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M n)
    have hB : 0 < (3 : ℝ) ^ (2 * (n + 1)) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M (n + 1) :=
      div_pos (by positivity) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (n + 1))
    rw [timeScale, ite_eq_right (not_le.mpr h1), ← hn]
    conv_lhs => rw [hr_eq]
    rw [hTint n t ht0 ht1]
    have hratio : r / (3 : ℝ) ^ n = (3 : ℝ) ^ t := by
      rw [hr_eq, Real.rpow_add (by norm_num), Real.rpow_natCast]
      field_simp
    rw [hratio]
    simp only [timeScaleTriadic, timeScaleExponent]
    rw [← Real.rpow_mul (by norm_num), mul_comm t, Real.rpow_mul (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) (div_pos hB hA)]
    rw [Real.div_rpow hB.le hA.le, Real.rpow_sub hA, Real.rpow_one]
    field_simp

/-- The time change `rawPath` of `physical_generator_reindexing` (speed-up of
the normalized cutoff-zero path by `ahom M 0`). -/
def aux_lem_crossing_rawPath {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (path : DiffusionPath d) : DiffusionPath d :=
  path.comp
    ⟨fun t ↦ Real.toNNReal (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0) * t,
      continuous_const.mul continuous_id⟩

/-- **Clock normalization at `N = 0`.**  The physical event of `lem_crossing`,
at normalized time `ahom M 0 * u`, is the raw-clock event at time `u` of the
speed-up path. -/
theorem aux_lem_crossing_rawPath_event {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (u R : ℝ) (x : SpatialCoordinates d) :
    {path : DiffusionPath d |
        ∃ s : ℝ≥0, (s : ℝ) ≤ SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 * u ∧ R ≤ dist (path s) x} =
      aux_lem_crossing_rawPath M ⁻¹'
        {path : DiffusionPath d | ∃ s : ℝ≥0, (s : ℝ) ≤ u ∧ R ≤ dist (path s) x} := by
  have ha := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M 0
  set a := SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 with ha_def
  ext path
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, aux_lem_crossing_rawPath,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  constructor
  · rintro ⟨s, hs, hR⟩
    refine ⟨Real.toNNReal ((s : ℝ) / a), ?_, ?_⟩
    · rw [Real.coe_toNNReal _ (div_nonneg (NNReal.coe_nonneg s) ha.le)]
      rw [div_le_iff₀ ha]; linarith
    · have : Real.toNNReal a * Real.toNNReal ((s : ℝ) / a) = s := by
        apply NNReal.eq
        rw [NNReal.coe_mul, Real.coe_toNNReal _ ha.le,
          Real.coe_toNNReal _ (div_nonneg (NNReal.coe_nonneg s) ha.le)]
        field_simp
      rw [this]; exact hR
  · rintro ⟨s, hs, hR⟩
    refine ⟨Real.toNNReal a * s, ?_, hR⟩
    rw [NNReal.coe_mul, Real.coe_toNNReal _ ha.le]
    exact mul_le_mul_of_nonneg_left hs ha.le

end SubdiffusiveProcess.Paper

namespace SubdiffusiveProcess.Paper

section StoppingTransfer

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]

/-- Galmarino's test, set form: events observable by time `t` on continuous-path
space cannot distinguish two paths agreeing on `[0, t]`. -/
theorem aux_lem_crossing_saturated {t : ℝ≥0} {A : Set (ContinuousPath α)}
    (hA : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := α) t] A)
    {p p' : ContinuousPath α} (hpp' : ∀ s ≤ t, p s = p' s) : p ∈ A ↔ p' ∈ A := by
  let m : MeasurableSpace (ContinuousPath α) :=
    { MeasurableSet' := fun A => ∀ p p' : ContinuousPath α, (∀ s ≤ t, p s = p' s) →
        (p ∈ A ↔ p' ∈ A)
      measurableSet_empty := by intros; simp
      measurableSet_compl := by
        intro A hA p p' h
        simp only [Set.mem_compl_iff, hA p p' h]
      measurableSet_iUnion := by
        intro f hf p p' h
        simp only [Set.mem_iUnion]
        exact exists_congr (fun i => hf i p p' h) }
  have hle : ContinuousPath.canonicalFiltration (alpha := α) t ≤ m := by
    change (⨆ s : Set.Iic t, MeasurableSpace.comap
      (ContinuousPath.coordinateProcess (alpha := α) s) ‹MeasurableSpace α›) ≤ m
    refine iSup_le fun s => ?_
    intro A hA
    obtain ⟨B, _, rfl⟩ := hA
    intro p p' h
    simp only [Set.mem_preimage, ContinuousPath.coordinateProcess_apply]
    rw [h s s.2]
  exact hle A hA p p' hpp'

/-- Galmarino's test for stopping times. -/
theorem aux_lem_crossing_galmarino {τ : ContinuousPath α → ℝ≥0∞}
    (hτ : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := α)) τ)
    {t : ℝ≥0} {p p' : ContinuousPath α} (hpp' : ∀ s ≤ t, p s = p' s) (hτp : τ p ≤ t) :
    τ p' = τ p := by
  have key : ∀ u : ℝ≥0, u ≤ t → (τ p ≤ u ↔ τ p' ≤ u) := fun u hu =>
    aux_lem_crossing_saturated (hτ u) (fun s hs => hpp' s (hs.trans hu))
  have hfin : τ p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hτp
  have hv : τ p = ((τ p).toNNReal : ℝ≥0∞) := (ENNReal.coe_toNNReal hfin).symm
  have hvt : (τ p).toNNReal ≤ t := by
    have := hτp; rw [hv] at this; exact_mod_cast this
  apply le_antisymm
  · have := (key _ hvt).1 (le_of_eq hv)
    rw [hv]; exact this
  · by_contra hlt
    push Not at hlt
    have hfin' : τ p' ≠ ⊤ := ne_top_of_lt hlt
    have hu : τ p' = ((τ p').toNNReal : ℝ≥0∞) := (ENNReal.coe_toNNReal hfin').symm
    have hut : (τ p').toNNReal ≤ t := by
      have h1 : τ p' ≤ t := hlt.le.trans hτp
      rw [hu] at h1; exact_mod_cast h1
    have := (key _ hut).2 (le_of_eq hu)
    rw [← hu] at this
    exact absurd hlt (not_lt.mpr this)

variable [Nonempty α]

/-- The live path through a deterministic horizon `u` strictly before death, held
constant after `u`; a fixed constant path otherwise.  It is adapted: its
coordinates up to `u` are measurable with respect to the lifetime-path filtration
at `u`. -/
def aux_lem_crossing_preDeath (u : ℝ≥0) (w : LifetimePath α) : ContinuousPath α :=
  if h : (u : ℝ≥0∞) < w.lifetime then
    ⟨fun s => w.livePath ⟨min s u,
        (ENNReal.coe_le_coe.mpr (min_le_right s u)).trans_lt h⟩,
      w.continuous_livePath.comp ((continuous_id.min continuous_const).subtype_mk _)⟩
  else ContinuousMap.const _ (Classical.arbitrary α)

omit [MeasurableSpace α] [BorelSpace α] in
theorem aux_lem_crossing_preDeath_apply {α : Type*} [TopologicalSpace α] [_ms : MeasurableSpace α]
    [_borel : BorelSpace α] [Nonempty α]
    {u : ℝ≥0} {w : LifetimePath α}
    (h : (u : ℝ≥0∞) < w.lifetime) {s : ℝ≥0} (hs : s ≤ u) :
    aux_lem_crossing_preDeath u w s =
      w.livePath ⟨s, (ENNReal.coe_le_coe.mpr hs).trans_lt h⟩ := by
  simp only [aux_lem_crossing_preDeath, dite_eq_left h, ContinuousMap.coe_mk]
  congr 2
  exact min_eq_left hs

theorem aux_lem_crossing_preDeath_agree {u u' : ℝ≥0} {w : LifetimePath α}
    (huu' : u ≤ u') (h' : (u' : ℝ≥0∞) < w.lifetime) :
    ∀ s ≤ u, aux_lem_crossing_preDeath u w s = aux_lem_crossing_preDeath u' w s := by
  intro s hs
  have h : (u : ℝ≥0∞) < w.lifetime := (ENNReal.coe_le_coe.mpr huu').trans_lt h'
  rw [aux_lem_crossing_preDeath_apply h hs, aux_lem_crossing_preDeath_apply h' (hs.trans huu')]

theorem aux_lem_crossing_preDeath_agree_top {u : ℝ≥0} {w : LifetimePath α}
    (hw : w.lifetime = ⊤) :
    ∀ s ≤ u, aux_lem_crossing_preDeath u w s = LifetimePath.toContinuousPath w hw s := by
  intro s hs
  have h : (u : ℝ≥0∞) < w.lifetime := by rw [hw]; exact ENNReal.coe_lt_top
  rw [aux_lem_crossing_preDeath_apply h hs]
  rfl

/-- The pre-death representative is adapted. -/
theorem aux_lem_crossing_measurable_preDeath (u : ℝ≥0) :
    Measurable[LifetimePath.canonicalFiltration (alpha := α) u,
      ContinuousPath.canonicalFiltration (alpha := α) u]
      (aux_lem_crossing_preDeath (α := α) u) := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap (aux_lem_crossing_preDeath (α := α) u)
    (⨆ s : Set.Iic u, MeasurableSpace.comap
      (ContinuousPath.coordinateProcess (alpha := α) s) ‹MeasurableSpace α›) ≤ _
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun s => ?_
  rw [MeasurableSpace.comap_comp]
  apply Measurable.comap_le
  have hlive : MeasurableSet[LifetimePath.canonicalFiltration (alpha := α) u]
      {w : LifetimePath α | (u : ℝ≥0∞) < w.lifetime} := by
    have := (LifetimePath.isStoppingTime_lifetime (alpha := α)) u
    have heq : {w : LifetimePath α | (u : ℝ≥0∞) < w.lifetime} =
        {w : LifetimePath α | w.lifetime ≤ (u : ℝ≥0∞)}ᶜ := by
      ext w; simp
    rw [heq]; exact this.compl
  have hcoord : Measurable[LifetimePath.canonicalFiltration (alpha := α) u]
      (fun w : LifetimePath α =>
        (LifetimePath.coordinate (s : ℝ≥0) w).elim id (fun _ => Classical.arbitrary α)) := by
    have h1 := LifetimePath.measurable_coordinate_canonicalFiltration (alpha := α) (s : ℝ≥0)
    have h2 : Measurable[LifetimePath.canonicalFiltration (alpha := α) u]
        (LifetimePath.coordinate (α := α) (s : ℝ≥0)) :=
      h1.mono ((LifetimePath.canonicalFiltration (alpha := α)).mono s.2) le_rfl
    exact (measurable_id.sumElim measurable_const).comp h2
  have heq : (ContinuousPath.coordinateProcess (alpha := α) s ∘
      aux_lem_crossing_preDeath (α := α) u) =
      Set.piecewise {w : LifetimePath α | (u : ℝ≥0∞) < w.lifetime}
        (fun w => (LifetimePath.coordinate (s : ℝ≥0) w).elim id
          (fun _ => Classical.arbitrary α))
        (fun _ => Classical.arbitrary α) := by
    funext w
    simp only [Function.comp_apply, ContinuousPath.coordinateProcess_apply, Set.piecewise]
    split_ifs with h
    · rw [aux_lem_crossing_preDeath_apply h s.2,
        LifetimePath.coordinate_of_lt w s ((ENNReal.coe_le_coe.mpr s.2).trans_lt h)]
      rfl
    · have h' : ¬ (u : ℝ≥0∞) < w.lifetime := h
      rw [aux_lem_crossing_preDeath, dite_eq_right h']
      rfl
  rw [heq]
  exact Measurable.piecewise hlive hcoord measurable_const

/-- **Lifting a continuous-path stopping time to lifetime paths.** -/
def aux_lem_crossing_liftStop (τ : ContinuousPath α → ℝ≥0∞) (w : LifetimePath α) : ℝ≥0∞ :=
  sInf {s : ℝ≥0∞ | ∃ u : ℝ≥0, s = u ∧ (u : ℝ≥0∞) < w.lifetime ∧
    τ (aux_lem_crossing_preDeath u w) ≤ u}

section Lift

variable {τ : ContinuousPath α → ℝ≥0∞}
  (hτ : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := α)) τ)
include hτ

theorem aux_lem_crossing_liftStop_mono {w : LifetimePath α} {u u' : ℝ≥0}
    (hu : τ (aux_lem_crossing_preDeath u w) ≤ u) (huu' : u ≤ u')
    (h' : (u' : ℝ≥0∞) < w.lifetime) :
    τ (aux_lem_crossing_preDeath u' w) = τ (aux_lem_crossing_preDeath u w) :=
  aux_lem_crossing_galmarino hτ (aux_lem_crossing_preDeath_agree huu' h') hu

theorem aux_lem_crossing_liftStop_eq {w : LifetimePath α} {u : ℝ≥0}
    (hlt : (u : ℝ≥0∞) < w.lifetime) (hu : τ (aux_lem_crossing_preDeath u w) ≤ u) :
    aux_lem_crossing_liftStop τ w = τ (aux_lem_crossing_preDeath u w) := by
  set v := τ (aux_lem_crossing_preDeath u w) with hv_def
  have hfin : v ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hu
  have hv : v = (v.toNNReal : ℝ≥0∞) := (ENNReal.coe_toNNReal hfin).symm
  have hvu : v.toNNReal ≤ u := by
    have := hu; rw [hv] at this; exact_mod_cast this
  have hvlt : (v.toNNReal : ℝ≥0∞) < w.lifetime :=
    (ENNReal.coe_le_coe.mpr hvu).trans_lt hlt
  apply le_antisymm
  · -- `v.toNNReal` belongs to the defining set
    apply sInf_le
    refine ⟨v.toNNReal, hv, hvlt, ?_⟩
    have h := aux_lem_crossing_galmarino hτ
      (fun s hs => (aux_lem_crossing_preDeath_agree hvu hlt s hs).symm)
      (t := v.toNNReal) (p := aux_lem_crossing_preDeath u w)
      (p' := aux_lem_crossing_preDeath v.toNNReal w) (le_of_eq hv)
    rw [h]; exact le_of_eq hv
  · apply le_sInf
    rintro s ⟨u'', rfl, hlt'', hu''⟩
    rcases le_total u'' u with h | h
    · have := aux_lem_crossing_liftStop_mono hτ hu'' h hlt
      rw [hv_def, this]; exact hu''
    · exact hu.trans (ENNReal.coe_le_coe.mpr h)

theorem aux_lem_crossing_liftStop_le_iff_of_lt {w : LifetimePath α} {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < w.lifetime) :
    aux_lem_crossing_liftStop τ w ≤ t ↔ τ (aux_lem_crossing_preDeath t w) ≤ t := by
  constructor
  · intro hle
    have hne : {s : ℝ≥0∞ | ∃ u : ℝ≥0, s = u ∧ (u : ℝ≥0∞) < w.lifetime ∧
        τ (aux_lem_crossing_preDeath u w) ≤ u}.Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      have : aux_lem_crossing_liftStop τ w = ⊤ := by
        rw [aux_lem_crossing_liftStop, hempty, sInf_empty]
      rw [this] at hle
      exact ENNReal.coe_ne_top (top_le_iff.mp hle)
    obtain ⟨_, u, rfl, hlt, hu⟩ := hne
    rw [aux_lem_crossing_liftStop_eq hτ hlt hu] at hle
    rcases le_total u t with h | h
    · rw [aux_lem_crossing_liftStop_mono hτ hu h ht]; exact hu.trans (ENNReal.coe_le_coe.mpr h)
    · have := aux_lem_crossing_galmarino hτ (p := aux_lem_crossing_preDeath u w)
        (p' := aux_lem_crossing_preDeath t w)
        (fun s hs => (aux_lem_crossing_preDeath_agree h hlt s hs).symm) hle
      rw [this]; exact hle
  · intro h
    exact sInf_le ⟨t, rfl, ht, h⟩

theorem aux_lem_crossing_liftStop_le_iff_of_le {w : LifetimePath α} {t : ℝ≥0}
    (ht : w.lifetime ≤ (t : ℝ≥0∞)) :
    aux_lem_crossing_liftStop τ w ≤ t ↔
      ∃ q : ℚ, (Real.toNNReal q : ℝ≥0∞) < w.lifetime ∧
        τ (aux_lem_crossing_preDeath (Real.toNNReal q) w) ≤ Real.toNNReal q := by
  constructor
  · intro hle
    have hne : {s : ℝ≥0∞ | ∃ u : ℝ≥0, s = u ∧ (u : ℝ≥0∞) < w.lifetime ∧
        τ (aux_lem_crossing_preDeath u w) ≤ u}.Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      have : aux_lem_crossing_liftStop τ w = ⊤ := by
        rw [aux_lem_crossing_liftStop, hempty, sInf_empty]
      rw [this] at hle
      exact ENNReal.coe_ne_top (top_le_iff.mp hle)
    obtain ⟨_, u, rfl, hlt, hu⟩ := hne
    have hζfin : w.lifetime ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top ht
    have hlt' : (u : ℝ) < (w.lifetime.toNNReal : ℝ) := by
      have : (u : ℝ≥0∞) < (w.lifetime.toNNReal : ℝ≥0∞) := by
        rw [ENNReal.coe_toNNReal hζfin]; exact hlt
      exact_mod_cast this
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt'
    have hq0 : (0 : ℝ) ≤ q := (NNReal.coe_nonneg u).trans hq1.le
    have huq : u ≤ Real.toNNReal q := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]; exact hq1.le
    have hqlt : (Real.toNNReal q : ℝ≥0∞) < w.lifetime := by
      rw [← ENNReal.coe_toNNReal hζfin, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe,
        Real.coe_toNNReal _ hq0]
      exact hq2
    refine ⟨q, hqlt, ?_⟩
    rw [aux_lem_crossing_liftStop_mono hτ hu huq hqlt]
    exact hu.trans (ENNReal.coe_le_coe.mpr huq)
  · rintro ⟨q, hqlt, hq⟩
    have hmem : ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) ∈ {s : ℝ≥0∞ | ∃ u : ℝ≥0, s = u ∧
        (u : ℝ≥0∞) < w.lifetime ∧ τ (aux_lem_crossing_preDeath u w) ≤ u} :=
      ⟨Real.toNNReal q, rfl, hqlt, hq⟩
    exact (sInf_le hmem).trans (hqlt.le.trans ht)

/-- **The lifted time is a lifetime-path stopping time.** -/
theorem aux_lem_crossing_isStoppingTime_liftStop :
    IsStoppingTime (LifetimePath.canonicalFiltration (alpha := α))
      (aux_lem_crossing_liftStop τ) := by
  intro t
  have hpre : ∀ u : ℝ≥0, MeasurableSet[LifetimePath.canonicalFiltration (alpha := α) u]
      {w : LifetimePath α | (u : ℝ≥0∞) < w.lifetime ∧
        τ (aux_lem_crossing_preDeath u w) ≤ u} := by
    intro u
    have hlive : MeasurableSet[LifetimePath.canonicalFiltration (alpha := α) u]
        {w : LifetimePath α | (u : ℝ≥0∞) < w.lifetime} := by
      have := (LifetimePath.isStoppingTime_lifetime (alpha := α)) u
      have heq : {w : LifetimePath α | (u : ℝ≥0∞) < w.lifetime} =
          {w : LifetimePath α | w.lifetime ≤ (u : ℝ≥0∞)}ᶜ := by
        ext w; simp
      rw [heq]; exact this.compl
    exact hlive.inter ((aux_lem_crossing_measurable_preDeath u) (hτ u))
  have hdeath : MeasurableSet[LifetimePath.canonicalFiltration (alpha := α) t]
      {w : LifetimePath α | w.lifetime ≤ (t : ℝ≥0∞)} :=
    (LifetimePath.isStoppingTime_lifetime (alpha := α)) t
  have hevent : {w : LifetimePath α | aux_lem_crossing_liftStop τ w ≤ (t : ℝ≥0∞)} =
      {w : LifetimePath α | (t : ℝ≥0∞) < w.lifetime ∧
          τ (aux_lem_crossing_preDeath t w) ≤ t} ∪
        ({w : LifetimePath α | w.lifetime ≤ (t : ℝ≥0∞)} ∩
          ⋃ q : {q : ℚ // Real.toNNReal q ≤ t},
            {w : LifetimePath α | (Real.toNNReal q.1 : ℝ≥0∞) < w.lifetime ∧
              τ (aux_lem_crossing_preDeath (Real.toNNReal q.1) w) ≤ Real.toNNReal q.1}) := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_iUnion]
    by_cases ht : (t : ℝ≥0∞) < w.lifetime
    · rw [aux_lem_crossing_liftStop_le_iff_of_lt hτ ht]
      simp only [ht, true_and, not_le.mpr ht, false_and, or_false]
    · have ht' : w.lifetime ≤ (t : ℝ≥0∞) := not_lt.mp ht
      rw [aux_lem_crossing_liftStop_le_iff_of_le hτ ht']
      simp only [ht, false_and, false_or, ht', true_and]
      constructor
      · rintro ⟨q, hqlt, hq⟩
        refine ⟨⟨q, ?_⟩, hqlt, hq⟩
        exact_mod_cast (hqlt.le.trans ht')
      · rintro ⟨⟨q, _⟩, hqlt, hq⟩
        exact ⟨q, hqlt, hq⟩
  change MeasurableSet[LifetimePath.canonicalFiltration (alpha := α) t]
    {w : LifetimePath α | aux_lem_crossing_liftStop τ w ≤ (t : ℝ≥0∞)}
  rw [hevent]
  refine (hpre t).union (hdeath.inter (MeasurableSet.iUnion fun q => ?_))
  exact (LifetimePath.canonicalFiltration (alpha := α)).mono q.2 _ (hpre _)

/-- **On nonexplosive paths the lifted time is the original stopping time.** -/
theorem aux_lem_crossing_liftStop_of_lifetime_top {w : LifetimePath α}
    (hw : w.lifetime = ⊤) :
    aux_lem_crossing_liftStop τ w = τ (LifetimePath.toContinuousPath w hw) := by
  by_cases hfin : τ (LifetimePath.toContinuousPath w hw) = ⊤
  · rw [hfin]
    apply le_antisymm le_top
    apply le_sInf
    rintro s ⟨u, rfl, hlt, hu⟩
    exfalso
    have := aux_lem_crossing_galmarino hτ
      (fun s hs => aux_lem_crossing_preDeath_agree_top hw s hs) hu
    rw [← this, hfin] at hu
    exact ENNReal.coe_ne_top (top_le_iff.mp hu)
  · set u := (τ (LifetimePath.toContinuousPath w hw)).toNNReal
    have hu : τ (LifetimePath.toContinuousPath w hw) = (u : ℝ≥0∞) :=
      (ENNReal.coe_toNNReal hfin).symm
    have hlt : (u : ℝ≥0∞) < w.lifetime := by rw [hw]; exact ENNReal.coe_lt_top
    have hpre := aux_lem_crossing_galmarino hτ
      (fun s hs => (aux_lem_crossing_preDeath_agree_top hw s hs).symm) (le_of_eq hu)
    have hule : τ (aux_lem_crossing_preDeath u w) ≤ u := by rw [hpre, hu]
    rw [aux_lem_crossing_liftStop_eq hτ hlt hule, hpre]

theorem aux_lem_crossing_liftStop_ofContinuousPath (p : ContinuousPath α) :
    aux_lem_crossing_liftStop τ (LifetimePath.ofContinuousPath p) = τ p := by
  rw [aux_lem_crossing_liftStop_of_lifetime_top hτ (LifetimePath.lifetime_ofContinuousPath p),
    LifetimePath.toContinuousPath_ofContinuousPath]

end Lift

end StoppingTransfer

end SubdiffusiveProcess.Paper

namespace SubdiffusiveProcess.Paper

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9PathGeometry
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation (Lattice IsJStepPath)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.ChronologicalSelection

section QGeom

variable {d : ℕ}

/-- Centres of the fine lattice of the path discretization at `r = ℓ / 2`. -/
def aux_lem_crossing_ctr (ℓ : ℝ) (k : Lattice d) : Homogenization.Vec d :=
  (gridCube d (ℓ / 2) k).1

/-- Selection cube (side `3ℓ/4`). -/
def aux_lem_crossing_W (ℓ : ℝ) (k : Lattice d) : Cube d := (aux_lem_crossing_ctr ℓ k, 3 * ℓ / 4)

/-- Good (torsion) cube (side `ℓ`), concentric with the selection cube. -/
def aux_lem_crossing_G (ℓ : ℝ) (k : Lattice d) : Cube d := (aux_lem_crossing_ctr ℓ k, ℓ)

theorem aux_lem_crossing_ctr_apply (ℓ : ℝ) (k : Lattice d) (i : Fin d) :
    aux_lem_crossing_ctr ℓ k i = ℓ / 16 * (k i : ℝ) := by
  simp only [aux_lem_crossing_ctr, gridCube]; ring

theorem aux_lem_crossing_mem_centeredAxisCube_iff (c y : Homogenization.Vec d) (L : ℝ) :
    y ∈ SubdiffusiveProcess.Section9.centeredAxisCube c L ↔ ∀ i, |y i - c i| < L / 2 := by
  simp only [SubdiffusiveProcess.Section9.centeredAxisCube, Homogenization.axisCube, Set.mem_pi, Set.mem_univ,
    Set.mem_Ioo, forall_const, abs_lt]
  refine forall_congr' fun i => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem aux_lem_crossing_closedQuarter_iff (U : Cube d) (hU : 0 < U.2) (y : Homogenization.Vec d) :
    y ∈ closedQuarter U ↔ ∀ i, |y i - U.1 i| ≤ U.2 / 8 := by
  have hcl : closure (middleQuarter U)
      = Set.univ.pi fun j : Fin d =>
        Set.Icc (U.1 j - U.2 / 4 / 2) (U.1 j - U.2 / 4 / 2 + U.2 / 4) := by
    show closure (Set.univ.pi fun j : Fin d =>
        Set.Ioo (U.1 j - U.2 / 4 / 2) (U.1 j - U.2 / 4 / 2 + U.2 / 4)) = _
    rw [closure_pi_set]
    exact congrArg _ (funext fun j => closure_Ioo (by intro hEq; linarith))
  rw [closedQuarter, hcl]
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const, abs_le]
  refine forall_congr' fun i => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem aux_lem_crossing_closedQuarter_W_subset {ℓ : ℝ} (hℓ : 0 < ℓ) (k : Lattice d) :
    closedQuarter (aux_lem_crossing_W ℓ k) ⊆ middleQuarter (aux_lem_crossing_G ℓ k) := by
  intro y hy
  rw [aux_lem_crossing_closedQuarter_iff _ (by simp [aux_lem_crossing_W]; positivity)] at hy
  show y ∈ SubdiffusiveProcess.Section9.centeredAxisCube (aux_lem_crossing_G ℓ k).1 ((aux_lem_crossing_G ℓ k).2 / 4)
  rw [aux_lem_crossing_mem_centeredAxisCube_iff]
  intro i
  have := hy i
  simp only [aux_lem_crossing_W, aux_lem_crossing_G] at this ⊢
  linarith

/-- The good cube attached to a point of two closed quarters lies in the `2`-dilate of the
other selection cube. -/
theorem aux_lem_crossing_G_subset_dilate {ℓ : ℝ} (hℓ : 0 < ℓ) {j m : Lattice d}
    {y : Homogenization.Vec d} (hyj : y ∈ closedQuarter (aux_lem_crossing_W ℓ j))
    (hym : y ∈ closedQuarter (aux_lem_crossing_W ℓ m)) :
    cubeSet (aux_lem_crossing_G ℓ m) ⊆
      SubdiffusiveProcess.Section9.centeredAxisCube (aux_lem_crossing_W ℓ j).1
        (2 * (aux_lem_crossing_W ℓ j).2) := by
  have hW : 0 < (aux_lem_crossing_W (d := d) ℓ j).2 := by simp [aux_lem_crossing_W]; positivity
  have hW' : 0 < (aux_lem_crossing_W (d := d) ℓ m).2 := by simp [aux_lem_crossing_W]; positivity
  rw [aux_lem_crossing_closedQuarter_iff _ hW] at hyj
  rw [aux_lem_crossing_closedQuarter_iff _ hW'] at hym
  intro z hz
  rw [cubeSet, aux_lem_crossing_mem_centeredAxisCube_iff] at hz
  rw [aux_lem_crossing_mem_centeredAxisCube_iff]
  intro i
  have h1 := hz i
  have h2 := hyj i
  have h3 := hym i
  simp only [aux_lem_crossing_W, aux_lem_crossing_G] at h1 h2 h3 ⊢
  have htri : |z i - aux_lem_crossing_ctr ℓ j i| ≤
      |z i - aux_lem_crossing_ctr ℓ m i| + |y i - aux_lem_crossing_ctr ℓ m i| +
        |y i - aux_lem_crossing_ctr ℓ j i| := by
    calc |z i - aux_lem_crossing_ctr ℓ j i|
        = |(z i - aux_lem_crossing_ctr ℓ m i) - (y i - aux_lem_crossing_ctr ℓ m i) +
            (y i - aux_lem_crossing_ctr ℓ j i)| := by ring_nf
      _ ≤ |(z i - aux_lem_crossing_ctr ℓ m i) - (y i - aux_lem_crossing_ctr ℓ m i)| +
            |y i - aux_lem_crossing_ctr ℓ j i| := abs_add_le _ _
      _ ≤ _ := by gcongr; exact abs_sub _ _
  linarith

/-- A lattice box is finite. -/
theorem aux_lem_crossing_finite_lattice_box (ℓ : ℝ) (hℓ : 0 < ℓ) (y : Homogenization.Vec d)
    (ρ : ℝ) :
    {k : Lattice d | ∀ i, |aux_lem_crossing_ctr ℓ k i - y i| < ρ}.Finite := by
  classical
  refine (Set.finite_Icc (fun i : Fin d => ⌊16 * (y i - ρ) / ℓ⌋)
    (fun i : Fin d => ⌈16 * (y i + ρ) / ℓ⌉)).subset ?_
  intro k hk
  simp only [Set.mem_ofPred_eq] at hk
  constructor
  · intro i
    have h := hk i
    rw [aux_lem_crossing_ctr_apply, abs_lt] at h
    have : 16 * (y i - ρ) / ℓ ≤ (k i : ℝ) := by
      rw [div_le_iff₀ hℓ]; linarith
    exact Int.floor_le_iff.mpr (by exact_mod_cast (lt_of_le_of_lt this (lt_add_one _)))
  · intro i
    have h := hk i
    rw [aux_lem_crossing_ctr_apply, abs_lt] at h
    have : (k i : ℝ) ≤ 16 * (y i + ρ) / ℓ := by
      rw [le_div_iff₀ hℓ]; linarith
    exact Int.le_ceil_iff.mpr (by linarith)

/-- The selection cubes (indexed through an enumeration) form a locally finite family. -/
theorem aux_lem_crossing_locallyFinite_W {ℓ : ℝ} (hℓ : 0 < ℓ) (e : ℕ ≃ Lattice d)
    (F : Set ℕ) :
    LocallyFinite (fun i : F => cubeSet (aux_lem_crossing_W ℓ (e i))) := by
  intro y
  refine ⟨Metric.ball y ℓ, Metric.ball_mem_nhds y hℓ, ?_⟩
  have hbox := aux_lem_crossing_finite_lattice_box ℓ hℓ y (3 * ℓ / 8 + ℓ)
  have hsub : {i : F | (cubeSet (aux_lem_crossing_W ℓ (e i)) ∩ Metric.ball y ℓ).Nonempty} ⊆
      (fun i : F => e i) ⁻¹' {k : Lattice d | ∀ i, |aux_lem_crossing_ctr ℓ k i - y i| <
        3 * ℓ / 8 + ℓ} := by
    rintro i ⟨z, hz, hzb⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    intro j
    rw [cubeSet, aux_lem_crossing_mem_centeredAxisCube_iff] at hz
    have h1 := hz j
    simp only [aux_lem_crossing_W] at h1
    have h2 : |z j - y j| < ℓ := by
      have := (dist_le_pi_dist z y j).trans_lt (Metric.mem_ball.mp hzb)
      rwa [Real.dist_eq] at this
    calc |aux_lem_crossing_ctr ℓ (e i) j - y j|
        = |(z j - y j) - (z j - aux_lem_crossing_ctr ℓ (e i) j)| := by ring_nf
      _ ≤ |z j - y j| + |z j - aux_lem_crossing_ctr ℓ (e i) j| := abs_sub _ _
      _ < ℓ + 3 * ℓ / 4 / 2 := add_lt_add h2 h1
      _ = 3 * ℓ / 8 + ℓ := by ring
  refine Set.Finite.subset ?_ hsub
  exact Set.Finite.preimage (fun a _ b _ hab => Subtype.ext (e.injective hab)) hbox

/-- Supremum distance is at most Euclidean distance. -/
theorem aux_lem_crossing_dist_le_euclid (y x : Homogenization.Vec d) :
    dist y x ≤ Homogenization.euclideanNorm (y - x) := by
  rw [dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (Homogenization.euclideanNorm_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  have hsq : (y - x) i ^ 2 ≤ Homogenization.vecNormSq (y - x) := by
    unfold Homogenization.vecNormSq Homogenization.vecDot
    have := Finset.single_le_sum (f := fun j => (y - x) j * (y - x) j)
      (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
    simpa [sq] using this
  rw [Homogenization.euclideanNorm]
  exact Real.abs_le_sqrt hsq

end QGeom


section QSurv

variable {d : ℕ}

/-- The selection family, indexed through an enumeration of the fine lattice. -/
def aux_lem_crossing_U (ℓ : ℝ) (e : ℕ ≃ Lattice d) : ℕ → Cube d :=
  fun i => aux_lem_crossing_W ℓ (e i)

/-- The survival event: started at `v 0`, the path stays at least time `h` in the good cube of
the source-order least selection cube whose closed quarter contains `v 0`. -/
def aux_lem_crossing_surv (ℓ h : ℝ) (e : ℕ ≃ Lattice d) (Fs : Set ℕ) : Set (Path d) :=
  {v | ∀ m : ℕ, selIndexAt (inferInstance : LinearOrder ℕ) (aux_lem_crossing_U ℓ e) Fs
      (position 0 v) = (m : WithTop ℕ) →
    ENNReal.ofReal h ≤ LifetimePath.exitTime (cubeSet (aux_lem_crossing_G ℓ (e m))) v}

theorem aux_lem_crossing_measurable_position (t : ℝ≥0) :
    Measurable (position (d := d) t) :=
  (measurable_id.sumElim measurable_const).comp (LifetimePath.measurable_coordinate t)

theorem aux_lem_crossing_measurableSet_surv (ℓ h : ℝ) (e : ℕ ≃ Lattice d) (Fs : Set ℕ) :
    MeasurableSet (aux_lem_crossing_surv ℓ h e Fs) := by
  have heq : aux_lem_crossing_surv ℓ h e Fs = ⋂ m : ℕ,
      ((position 0 ⁻¹' {y | selIndexAt (inferInstance : LinearOrder ℕ)
          (aux_lem_crossing_U ℓ e) Fs y = (m : WithTop ℕ)})ᶜ ∪
        {v | ENNReal.ofReal h ≤ LifetimePath.exitTime
          (cubeSet (aux_lem_crossing_G ℓ (e m))) v}) := by
    ext v
    simp only [aux_lem_crossing_surv, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union,
      Set.mem_compl_iff, Set.mem_preimage]
    refine forall_congr' fun m => ?_
    tauto
  rw [heq]
  refine MeasurableSet.iInter fun m => ?_
  refine MeasurableSet.union ?_ ?_
  · exact ((aux_lem_crossing_measurable_position 0)
      (measurableSet_selIndexAt_eq_coe _ _ _ m)).compl
  · have hm : Measurable (LifetimePath.exitTime (cubeSet (aux_lem_crossing_G ℓ (e m)))) := by
      simpa using! (LifetimePath.isStoppingTime_exitTime _ (isOpen_cubeSet _)).measurable'
    exact measurableSet_le measurable_const hm

theorem aux_lem_crossing_isBounded_cubeSet (Q : Cube d) : Bornology.IsBounded (cubeSet Q) := by
  rw [Metric.isBounded_iff_subset_closedBall Q.1]
  refine ⟨|Q.2|, fun y hy => ?_⟩
  rw [cubeSet, aux_lem_crossing_mem_centeredAxisCube_iff] at hy
  rw [Metric.mem_closedBall, dist_pi_le_iff (abs_nonneg _)]
  intro i
  rw [Real.dist_eq]
  have := hy i
  have h2 : Q.2 / 2 ≤ |Q.2| := by
    have := le_abs_self Q.2
    have h0 : 0 ≤ |Q.2| := abs_nonneg _
    linarith
  linarith

/-- The position selector at a point of `V` returns a candidate. -/
theorem aux_lem_crossing_selIndexAt_exists {ℓ : ℝ} (hℓ : 0 < ℓ) (e : ℕ ≃ Lattice d)
    (Fs : Set ℕ) {y : Homogenization.Vec d}
    (hy : ∃ m ∈ Fs, y ∈ closedQuarter (aux_lem_crossing_U ℓ e m)) :
    ∃ m₀ : ℕ, m₀ ∈ Fs ∧ y ∈ closedQuarter (aux_lem_crossing_U ℓ e m₀) ∧
      selIndexAt (inferInstance : LinearOrder ℕ) (aux_lem_crossing_U ℓ e) Fs y =
        (m₀ : WithTop ℕ) := by
  have hside : ∀ i ∈ Fs, 0 < (aux_lem_crossing_U ℓ e i).2 := fun i _ => by
    simp [aux_lem_crossing_U, aux_lem_crossing_W]; positivity
  have hfin := finite_mem_closedQuarter (aux_lem_crossing_U ℓ e) Fs hside
    (aux_lem_crossing_locallyFinite_W hℓ e Fs) y
  obtain ⟨m, hmF, hmy⟩ := hy
  obtain ⟨i₀, ⟨hi₀F, hi₀y⟩, hmin⟩ :=
    exists_order_min (inferInstance : LinearOrder ℕ) hfin ⟨m, hmF, hmy⟩
  exact ⟨i₀, hi₀F, hi₀y, selIndexAt_of_min _ _ _ _ i₀ hi₀F hi₀y
    (fun k hk hky => hmin k ⟨hk, hky⟩)⟩

/-- **Survival bound on `V`.** -/
theorem aux_lem_crossing_surv_bound {κ Aκ c0 : ℝ} (hsurv : ∀ d : ℕ, ∀ _hd : 2 ≤ d,
      ∀ law : Kernel (Homogenization.Vec d) (Path d),
      StrongMarkov law → ∀ U V : Set (Homogenization.Vec d), IsOpen U → Bornology.IsBounded U →
      V ⊆ U → ∀ F : ℝ, 0 < F →
      (∀ x ∈ V, ENNReal.ofReal (κ * F) ≤ meanExit law U x) →
      (∀ x ∈ U, meanExit law U x ≤ ENNReal.ofReal (Aκ * F)) →
        ∀ x ∈ V,
          ENNReal.ofReal c0 ≤
            law x {w | ENNReal.ofReal (κ * F / 2) ≤ LifetimePath.exitTime U w} ∧
          (∫⁻ w, (if LifetimePath.exitTime U w = ∞ then 0 else
            ENNReal.ofReal (Real.exp (-(LifetimePath.exitTime U w).toReal / F))) ∂law x) ≤
              ENNReal.ofReal (1 - c0))
    (hd : 2 ≤ d) (law : Kernel (Homogenization.Vec d) (Path d)) (hSM : StrongMarkov law)
    {ℓ F : ℝ} (hℓ : 0 < ℓ) (hF : 0 < F) (e : ℕ ≃ Lattice d) (Good : Set (Lattice d))
    (htors : ∀ k ∈ Good,
      (∀ y ∈ middleQuarter (aux_lem_crossing_G ℓ k),
        ENNReal.ofReal (κ * F) ≤ meanExit law (cubeSet (aux_lem_crossing_G ℓ k)) y) ∧
      (∀ y ∈ cubeSet (aux_lem_crossing_G ℓ k),
        meanExit law (cubeSet (aux_lem_crossing_G ℓ k)) y ≤ ENNReal.ofReal (Aκ * F)))
    {y : Homogenization.Vec d}
    (hy : ∃ m ∈ {m : ℕ | e m ∈ Good}, y ∈ closedQuarter (aux_lem_crossing_U ℓ e m)) :
    ENNReal.ofReal c0 ≤
      law y (aux_lem_crossing_surv ℓ (κ * F / 2) e {m : ℕ | e m ∈ Good}) := by
  obtain ⟨m₀, hm₀F, hm₀y, hsel⟩ := aux_lem_crossing_selIndexAt_exists hℓ e _ hy
  have hGpos : 0 < (aux_lem_crossing_G (d := d) ℓ (e m₀)).2 := by
    simp [aux_lem_crossing_G]; exact hℓ
  have hyV : y ∈ middleQuarter (aux_lem_crossing_G ℓ (e m₀)) :=
    aux_lem_crossing_closedQuarter_W_subset hℓ (e m₀) hm₀y
  have hs := (hsurv d hd law hSM (cubeSet (aux_lem_crossing_G ℓ (e m₀)))
    (middleQuarter (aux_lem_crossing_G ℓ (e m₀))) (isOpen_cubeSet _)
    (aux_lem_crossing_isBounded_cubeSet _) (middleQuarter_subset_cubeSet _ hGpos) F hF
    (htors _ hm₀F).1 (htors _ hm₀F).2 y hyV).1
  refine hs.trans (measure_mono_ae ?_)
  filter_upwards [hSM.2.1 y] with w hw0 hw
  intro m hm
  have hpos : position 0 w = y := by
    simp only [position, hw0]; rfl
  rw [hpos, hsel] at hm
  have hmm : m = m₀ := by exact_mod_cast hm.symm
  subst hmm
  exact hw

end QSurv


section QSelect

variable {d : ℕ}

/-- The good index set. -/
def aux_lem_crossing_Fs (e : ℕ ≃ Lattice d) (Good : Set (Lattice d)) : Set ℕ := {m | e m ∈ Good}

/-- The `i`-th greedy entrance time (from time `0`) for the selection family. -/
def aux_lem_crossing_ent (ℓ : ℝ) (e : ℕ ≃ Lattice d) (Good : Set (Lattice d)) (i : ℕ)
    (p : ContinuousPath (Homogenization.Vec d)) : ℝ≥0∞ :=
  entrance (inferInstance : LinearOrder ℕ) (aux_lem_crossing_U ℓ e) ((2 : ℕ) : ℝ)
    (aux_lem_crossing_Fs e Good) ((0 : ℝ≥0) : ℝ≥0∞) i p

/-- The degree bound of the selection family, from the path-discretization lemma. -/
theorem aux_lem_crossing_W_degree (hd : 2 ≤ d) {ℓ : ℝ} (hℓ : 0 < ℓ) (k : Lattice d) :
    {j : Lattice d | ¬ Disjoint
      (SubdiffusiveProcess.Section9.centeredAxisCube (aux_lem_crossing_W ℓ k).1
        (((2 : ℕ) : ℝ) * (aux_lem_crossing_W ℓ k).2))
      (SubdiffusiveProcess.Section9.centeredAxisCube (aux_lem_crossing_W ℓ j).1
        (((2 : ℕ) : ℝ) * (aux_lem_crossing_W ℓ j).2))}.encard ≤ ((48 * 2 + 1) ^ d : ℕ) := by
  obtain ⟨_, hpd⟩ := _root_.SubdiffusiveProcess.Section9.weighted_path_discretization d hd
  obtain ⟨c, _, hc⟩ := hpd 2 (by norm_num)
  have h := (hc (ℓ / 2) (by positivity)).2.2 (aux_lem_crossing_W ℓ) (fun k => rfl)
    (fun k => by simp only [aux_lem_crossing_W]; constructor <;> linarith)
  exact h.1 k

theorem aux_lem_crossing_U_degree (hd : 2 ≤ d) {ℓ : ℝ} (hℓ : 0 < ℓ) (e : ℕ ≃ Lattice d)
    (Fs : Set ℕ) (i : ℕ) :
    {j : ℕ | j ∈ Fs ∧ ¬ Disjoint
      (SubdiffusiveProcess.Section9.centeredAxisCube (aux_lem_crossing_U ℓ e i).1
        (((2 : ℕ) : ℝ) * (aux_lem_crossing_U ℓ e i).2))
      (SubdiffusiveProcess.Section9.centeredAxisCube (aux_lem_crossing_U ℓ e j).1
        (((2 : ℕ) : ℝ) * (aux_lem_crossing_U ℓ e j).2))}.encard ≤ ((48 * 2 + 1) ^ d : ℕ) := by
  set S := {j : Lattice d | ¬ Disjoint
      (SubdiffusiveProcess.Section9.centeredAxisCube (aux_lem_crossing_W ℓ (e i)).1
        (((2 : ℕ) : ℝ) * (aux_lem_crossing_W ℓ (e i)).2))
      (SubdiffusiveProcess.Section9.centeredAxisCube (aux_lem_crossing_W ℓ j).1
        (((2 : ℕ) : ℝ) * (aux_lem_crossing_W ℓ j).2))} with hS
  have hsub : {j : ℕ | j ∈ Fs ∧ ¬ Disjoint
      (SubdiffusiveProcess.Section9.centeredAxisCube (aux_lem_crossing_U ℓ e i).1
        (((2 : ℕ) : ℝ) * (aux_lem_crossing_U ℓ e i).2))
      (SubdiffusiveProcess.Section9.centeredAxisCube (aux_lem_crossing_U ℓ e j).1
        (((2 : ℕ) : ℝ) * (aux_lem_crossing_U ℓ e j).2))} ⊆ e ⁻¹' S := fun j hj => hj.2
  refine (Set.encard_le_encard hsub).trans ?_
  have himg : (e '' (e ⁻¹' S)).encard = (e ⁻¹' S).encard := e.injective.encard_image _
  rw [← himg]
  exact (Set.encard_le_encard (Set.image_preimage_subset e S)).trans
    (aux_lem_crossing_W_degree hd hℓ (e i))

/-- The chronological selection instantiated on the selection family. -/
theorem aux_lem_crossing_selection (hd : 2 ≤ d) {ℓ : ℝ} (hℓ : 0 < ℓ) (e : ℕ ≃ Lattice d)
    (Good : Set (Lattice d)) :
    let order : LinearOrder ℕ := inferInstance
    let U := aux_lem_crossing_U ℓ e
    let F := aux_lem_crossing_Fs e Good
    let A : ℝ := ((2 : ℕ) : ℝ)
    let theta0 : ContinuousPath (Homogenization.Vec d) → ℝ≥0∞ := fun _ => ((0 : ℝ≥0) : ℝ≥0∞)
    (∀ i : ℕ,
      IsStoppingTime ContinuousPath.canonicalFiltration
        (fun p => entrance order U A F (theta0 p) i p) ∧
      IsStoppingTime ContinuousPath.canonicalFiltration
        (fun p => departure order U A F (theta0 p) i p)) ∧
    (∀ (i : ℕ) (p : ContinuousPath (Homogenization.Vec d)),
      entrance order U A F (theta0 p) i p ≤ departure order U A F (theta0 p) i p ∧
      departure order U A F (theta0 p) i p ≤ entrance order U A F (theta0 p) (i + 1) p) ∧
    (∀ (p : ContinuousPath (Homogenization.Vec d)) (i : ℕ), 1 ≤ i →
      entrance order U A F (theta0 p) i p < ⊤ →
      ∃ j ∈ F, (greedyRun order U A F (theta0 p) p i).2.2.2 = (j : WithTop ℕ) ∧
        p (entrance order U A F (theta0 p) i p).toNNReal ∈ closedQuarter (U j) ∧
        entrance order U A F (theta0 p) i p < departure order U A F (theta0 p) i p) ∧
    (∀ (p : ContinuousPath (Homogenization.Vec d)) (theta : ℝ≥0∞), theta0 p ≤ theta →
      ∀ S : Finset ℕ, (∀ i ∈ S, i ∈ F) →
        Set.Pairwise (S : Set ℕ) (fun i j => Disjoint
          (SubdiffusiveProcess.Section9.centeredAxisCube (U i).1 (A * (U i).2))
          (SubdiffusiveProcess.Section9.centeredAxisCube (U j).1 (A * (U j).2))) →
        (∀ i ∈ S, ∃ t : ℝ≥0, theta0 p ≤ (t : ℝ≥0∞) ∧
          (t : ℝ≥0∞) ≤ theta ∧ p t ∈ middleQuarter (U i)) →
        ∀ k : ℕ, 1 ≤ k → k * ((48 * 2 + 1) ^ d : ℕ) ≤ S.card →
          entrance order U A F (theta0 p) k p ≤ theta) := by
  intro order U F A theta0
  have hside : ∀ i ∈ F, 0 < (U i).2 := fun i _ => by
    simp [U, aux_lem_crossing_U, aux_lem_crossing_W]; positivity
  have hsel := _root_.SubdiffusiveProcess.Section9.weighted_chronological_selection d hd order U F A
    (by norm_num [A]) hside (aux_lem_crossing_locallyFinite_W hℓ e F) ((48 * 2 + 1) ^ d)
    (Nat.one_le_pow _ _ (by norm_num))
    (fun i _ => aux_lem_crossing_U_degree hd hℓ e F i) theta0
    (isStoppingTime_const _ (0 : ℝ≥0))
  exact ⟨hsel.1, hsel.2.1, hsel.2.2.1, hsel.2.2.2.1⟩

end QSelect


section QStep

variable {d : ℕ}

/-- **One greedy step.**  A finite entrance lands in the closed quarter of a good selection
cube; the next finite entrance lies outside the good cube attached (by the position
selector) to the previous entrance point. -/
theorem aux_lem_crossing_path_step (hd : 2 ≤ d) {ℓ : ℝ} (hℓ : 0 < ℓ) (e : ℕ ≃ Lattice d)
    (Good : Set (Lattice d)) (p : ContinuousPath (Homogenization.Vec d)) (i : ℕ)
    (hi : aux_lem_crossing_ent ℓ e Good (i + 1) p < ⊤) :
    (∃ m ∈ aux_lem_crossing_Fs e Good,
        p (aux_lem_crossing_ent ℓ e Good (i + 1) p).toNNReal ∈
          closedQuarter (aux_lem_crossing_U ℓ e m)) ∧
      (aux_lem_crossing_ent ℓ e Good (i + 1 + 1) p < ⊤ → ∀ m₀ : ℕ,
        selIndexAt (inferInstance : LinearOrder ℕ) (aux_lem_crossing_U ℓ e)
          (aux_lem_crossing_Fs e Good)
          (p (aux_lem_crossing_ent ℓ e Good (i + 1) p).toNNReal) = (m₀ : WithTop ℕ) →
        p (aux_lem_crossing_ent ℓ e Good (i + 1 + 1) p).toNNReal ∉
          cubeSet (aux_lem_crossing_G ℓ (e m₀))) := by
  have hsel := aux_lem_crossing_selection hd hℓ e Good
  dsimp only at hsel
  unfold aux_lem_crossing_ent at hi ⊢
  obtain ⟨-, -, h3, -⟩ := hsel
  obtain ⟨j, hjF, hselj, hjq, -⟩ := h3 p (i + 1) (by omega) hi
  refine ⟨⟨j, hjF, hjq⟩, ?_⟩
  intro hi2 m₀ hm₀
  obtain ⟨j', _, hselj', hj'q, -⟩ := h3 p (i + 1 + 1) (by omega) hi2
  have hact : j' ∈ (greedyRun (inferInstance : LinearOrder ℕ) (aux_lem_crossing_U ℓ e)
      ((2 : ℕ) : ℝ) (aux_lem_crossing_Fs e Good) ((0 : ℝ≥0) : ℝ≥0∞) p (i + 1)).1 := by
    have h1 := sel_succ (inferInstance : LinearOrder ℕ) (aux_lem_crossing_U ℓ e)
      ((2 : ℕ) : ℝ) (aux_lem_crossing_Fs e Good) ((0 : ℝ≥0) : ℝ≥0∞) p (i + 1)
    rw [selectedIndex_eq_selIndexAt _ _ _ _ hi2 p, hselj'] at h1
    exact ((selIndexAt_eq_coe_iff _ _ _ _ _).mp h1.symm).1
  rw [greedyRun_succ_fst] at hact
  have hdisj := hact.2 j hselj
  have hm0 := (selIndexAt_eq_coe_iff _ _ _ _ _).mp hm₀
  have hGsub := aux_lem_crossing_G_subset_dilate hℓ hjq hm0.2.1
  have hpos : 0 < (aux_lem_crossing_U ℓ e j').2 := by
    simp [aux_lem_crossing_U, aux_lem_crossing_W]; positivity
  intro hz
  have hz' := cubeSet_subset_dilate (aux_lem_crossing_U ℓ e j') hpos ((2 : ℕ) : ℝ)
    (by norm_num) (closedQuarter_subset_cubeSet _ hpos hj'q)
  apply Set.disjoint_left.mp hdisj hz'
  have := hGsub hz
  simp only [aux_lem_crossing_U] at this ⊢
  convert this using 2

/-- On a nonexplosive path the GMC position is the continuous path. -/
theorem aux_lem_crossing_position_of_top {w : Path d} (hw : w.lifetime = ⊤) (s : ℝ≥0) :
    position s w = LifetimePath.toContinuousPath w hw s := by
  have hs : (s : ℝ≥0∞) < w.lifetime := by rw [hw]; exact ENNReal.coe_lt_top
  simp only [position, LifetimePath.coordinate_of_lt w s hs]
  rfl

theorem aux_lem_crossing_position_shift_of_top {w : Path d} (hw : w.lifetime = ⊤) (t : ℝ≥0) :
    position 0 (LifetimePath.shift t w) = LifetimePath.toContinuousPath w hw t := by
  simp only [position, LifetimePath.coordinate_shift, add_zero]
  exact aux_lem_crossing_position_of_top hw t

/-- A later exit point bounds the exit time of the shifted path. -/
theorem aux_lem_crossing_exitTime_shift_le {w : Path d} (hw : w.lifetime = ⊤)
    {U : Set (Homogenization.Vec d)} {t t' : ℝ≥0} (htt' : t ≤ t')
    (hout : LifetimePath.toContinuousPath w hw t' ∉ U) :
    LifetimePath.exitTime U (LifetimePath.shift t w) ≤ ((t' - t : ℝ≥0) : ℝ≥0∞) := by
  apply LifetimePath.exitTime_le_of_coordinate_notMem
  rw [LifetimePath.coordinate_shift, add_tsub_cancel_of_le htt']
  have hs : (t' : ℝ≥0∞) < w.lifetime := by rw [hw]; exact ENNReal.coe_lt_top
  rw [LifetimePath.coordinate_of_lt w t' hs]
  rintro ⟨y, hy, hyeq⟩
  have : y = LifetimePath.toContinuousPath w hw t' := Sum.inl.inj hyeq
  exact hout (this ▸ hy)

end QStep

section QTimes

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [Nonempty α]

/-- Running maximum of a sequence of times. -/
def aux_lem_crossing_runMax {Ω : Type*} (L : ℕ → Ω → ℝ≥0∞) : ℕ → Ω → ℝ≥0∞
  | 0 => L 0
  | i + 1 => fun w => max (aux_lem_crossing_runMax L i w) (L (i + 1) w)

/-- **Lifted, monotone stopping times** agreeing with a monotone family of continuous-path
stopping times on every nonexplosive path. -/
theorem aux_lem_crossing_liftFamily (τ : ℕ → ContinuousPath α → ℝ≥0∞)
    (hτ : ∀ i, IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := α)) (τ i))
    (hmono : ∀ i p, τ i p ≤ τ (i + 1) p) :
    let T := aux_lem_crossing_runMax (fun i => aux_lem_crossing_liftStop (τ i))
    (∀ i, IsStoppingTime (LifetimePath.canonicalFiltration (alpha := α)) (T i)) ∧
    (∀ i w, T i w ≤ T (i + 1) w) ∧
    (∀ i (w : LifetimePath α) (hw : w.lifetime = ⊤), T i w = τ i (LifetimePath.toContinuousPath w hw)) := by
  intro T
  refine ⟨fun i => ?_, fun i w => le_max_left _ _, fun i w hw => ?_⟩
  · induction i with
    | zero => exact aux_lem_crossing_isStoppingTime_liftStop (hτ 0)
    | succ i ih => exact ih.max (aux_lem_crossing_isStoppingTime_liftStop (hτ (i + 1)))
  · induction i with
    | zero => exact aux_lem_crossing_liftStop_of_lifetime_top (hτ 0) hw
    | succ i ih =>
      show max (T i w) (aux_lem_crossing_liftStop (τ (i + 1)) w) = _
      rw [ih, aux_lem_crossing_liftStop_of_lifetime_top (hτ (i + 1)) hw]
      exact max_eq_right (hmono i _)

end QTimes


section QCount

attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- **Counting.**  If every fine lattice path from `x` of reach `R` meets at least `c₁ R / ℓ`
good sites, then a continuous path from `x` reaching distance `R` by time `s` has made its
`k`-th greedy entrance by time `s`, for every `k` with `k D ≤ c_pd c₁ R / ℓ`. -/
theorem aux_lem_crossing_count (hd : 2 ≤ d) :
    ∃ cpd : ℝ, 0 < cpd ∧ ∀ {ℓ : ℝ} (_hℓ : 0 < ℓ) (e : ℕ ≃ Lattice d) (Good : Set (Lattice d))
      (c₁ : ℝ) (x : Homogenization.Vec d) (R : ℝ) (_hR : ℓ ≤ R)
      (_hgood : ∀ (N : ℕ) (q : ℕ → Lattice d), IsJStepPath 1 q N →
        Set.InjOn q (Set.Icc 0 N) → x ∈ cubeSet (aux_lem_crossing_W ℓ (q 0)) →
        (∃ y ∈ cubeSet (aux_lem_crossing_W ℓ (q N)), R ≤ dist y x) →
        c₁ * R / ℓ ≤ (((Finset.range (N + 1)).filter (fun i => q i ∈ Good)).card : ℝ))
      (p : ContinuousPath (Homogenization.Vec d)) (_hp0 : p 0 = x) (s : ℝ≥0)
      (_hs : R ≤ dist (p s) x) (k : ℕ) (_hk : 1 ≤ k)
      (_hkD : ((k * (48 * 2 + 1) ^ d : ℕ) : ℝ) ≤ cpd * (c₁ * R / ℓ)),
      aux_lem_crossing_ent ℓ e Good k p ≤ (s : ℝ≥0∞) := by
  obtain ⟨_, hpd⟩ := _root_.SubdiffusiveProcess.Section9.weighted_path_discretization d hd
  obtain ⟨cpd, hcpd, hc⟩ := hpd 2 (by norm_num)
  refine ⟨cpd, hcpd, ?_⟩
  intro ℓ hℓ e Good c₁ x R hR hgood p hp0 s hs k hk hkD
  have hQ := (hc (ℓ / 2) (by positivity)).2.2 (aux_lem_crossing_W ℓ) (fun k => rfl)
    (fun k => by simp only [aux_lem_crossing_W]; constructor <;> linarith)
  have hAr : ((2 : ℕ) : ℝ) * (ℓ / 2) ≤ R := by norm_num; linarith
  have heu0 : Homogenization.euclideanNorm (p 0 - x) ≤ 0 := by
    rw [hp0, sub_self, Homogenization.euclideanNorm_zero]
  have heus : 0 + R ≤ Homogenization.euclideanNorm (p s - x) := by
    rw [zero_add]; exact hs.trans (aux_lem_crossing_dist_le_euclid _ _)
  obtain ⟨N, q, t, hJ, hinj, htmono, hta, htb, hpa, hpb, hmid, -, hsel⟩ :=
    hQ.2 x 0 R le_rfl hAr p 0 s (zero_le) heu0 heus
  obtain ⟨selected, hselS, hpair, hcard⟩ := hsel Good
  have hcount := hgood N q hJ hinj (by rw [← hp0]; exact hpa) ⟨p s, hpb, hs⟩
  set S : Finset ℕ := selected.image (fun i => e.symm (q i)) with hSdef
  have hinjS : Set.InjOn (fun i => e.symm (q i)) (selected : Set ℕ) := by
    intro i hi j hj hij
    exact hinj ⟨Nat.zero_le _, (hselS i hi).1⟩ ⟨Nat.zero_le _, (hselS j hj).1⟩
      (e.symm.injective hij)
  have hScard : S.card = selected.card := Finset.card_image_of_injOn hinjS
  have hsel := aux_lem_crossing_selection hd hℓ e Good
  dsimp only at hsel
  obtain ⟨-, -, -, h4⟩ := hsel
  refine h4 p (s : ℝ≥0∞) (by simp) S ?_ ?_ ?_ k hk ?_
  · intro m hm
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
    show e (e.symm (q i)) ∈ Good
    rw [Equiv.apply_symm_apply]; exact (hselS i hi).2
  · intro m₁ hm₁ m₂ hm₂ hne
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm₁
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm₂
    have hij : i ≠ j := fun h => hne (by rw [h])
    have := hpair hi hj hij
    simp only [aux_lem_crossing_U, Equiv.apply_symm_apply]
    exact this
  · intro m hm
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
    have hiN : i ≤ N := (hselS i hi).1
    refine ⟨t i, by simp, ?_, ?_⟩
    · have h1 : t i ≤ t N := htmono ⟨Nat.zero_le _, hiN⟩ ⟨Nat.zero_le _, le_rfl⟩ hiN
      exact ENNReal.coe_le_coe.mpr (h1.trans htb)
    · simp only [aux_lem_crossing_U, Equiv.apply_symm_apply]
      exact hmid i hiN
  · rw [hScard]
    have h1 : ((k * (48 * 2 + 1) ^ d : ℕ) : ℝ) ≤ (selected.card : ℝ) :=
      hkD.trans ((mul_le_mul_of_nonneg_left hcount hcpd.le).trans hcard)
    exact_mod_cast h1

end QCount


/-- The lifetime-path form of the physical exit event: some live time `s ≤ T`
at which the live position is at distance at least `R` from `x`. -/
def aux_lem_crossing_lifeEvent {d : ℕ} (T R : ℝ) (x : SpatialCoordinates d) :
    Set (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d) :=
  {w | ∃ s : ℝ≥0, (s : ℝ) ≤ T ∧ ∃ y : SpatialCoordinates d,
    LifetimePath.coordinate s w = Cemetery.alive y ∧ R ≤ dist y x}





/-- **Crossing from survival.**  Iterating the strong Markov property: if at every
selected time `T i` (finite, before death) the process sits in a region `V` from which
the survival event `Surv` has probability at least `c0`, and the shifted path in `Surv`
forces a residence `T (i+1) - T i ≥ c0 F0`, then the `Crossing` predicate of
the common-semigroup crossing lemma holds for `S i := T (i+1)` and the event
`{T n ≤ t}`. -/
theorem aux_lem_crossing_crossing_of_survival {d : ℕ}
    (law : Kernel (Homogenization.Vec d) (Path d)) (hSM : StrongMarkov law) (x : Homogenization.Vec d)
    (hnonexp : ∀ᵐ w ∂law x, w.lifetime = ⊤)
    (c0 F0 t : ℝ) (n : ℕ)
    (T : ℕ → Path d → ℝ≥0∞)
    (hT : ∀ i, IsStoppingTime LifetimePath.canonicalFiltration (T i))
    (hmono : ∀ i w, T i w ≤ T (i + 1) w)
    (V : Set (Homogenization.Vec d)) (Surv : Set (Path d)) (hSurv : MeasurableSet Surv)
    (hV : ∀ y ∈ V, ENNReal.ofReal c0 ≤ law y Surv)
    (hpath : ∀ i < n, ∀ w : Path d, w.lifetime = ⊤ → T i w < ⊤ →
      position (T i w).toNNReal w ∈ V ∧
        (LifetimePath.shift (T i w).toNNReal w ∈ Surv →
          ENNReal.ofReal (c0 * F0) ≤ T (i + 1) w - T i w)) :
    Crossing (law x) c0 F0 t n {w | T n w ≤ ENNReal.ofReal t} := by
  refine ⟨T, fun i => T (i + 1), fun i _ => ⟨hT i, hT (i + 1)⟩, fun i _ w => hmono i w,
    fun i _ w => le_rfl, ?_, ?_⟩
  · intro w hw
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact Or.inl hn
    · right
      simp only [Set.mem_ofPred_eq] at hw ⊢
      rw [Nat.sub_add_cancel hn]
      exact hw
  · intro i hi hTi B hB hBfin
    set μ := law x with hμ
    have hTmeas : Measurable (T i) := hTi.measurable'
    have hlive : MeasurableSet {w : Path d | T i w < w.lifetime} :=
      measurableSet_lt hTmeas LifetimePath.measurable_lifetime
    have hBm : MeasurableSet B := hTi.measurableSpace_le _ hB
    set A := B ∩ {w : Path d | T i w < w.lifetime} with hA
    have hAm : MeasurableSet A := hBm.inter hlive
    -- B and A agree almost surely
    have hBA : μ B = μ A := by
      apply le_antisymm _ (measure_mono Set.inter_subset_left)
      apply measure_mono_ae
      filter_upwards [hnonexp] with w hw hwB
      refine ⟨hwB, ?_⟩
      show T i w < w.lifetime
      rw [hw]; exact hBfin hwB
    set E := {w : Path d | ENNReal.ofReal (c0 * F0) ≤ T (i + 1) w - T i w} with hE
    set g : Path d → ℝ≥0∞ := Surv.indicator 1 with hg
    have hgm : Measurable g := measurable_one.indicator hSurv
    have hSMi := hSM.2.2 x (T i) hTi B hB g hgm
    have hinner : ∀ y, (∫⁻ v, g v ∂law y) = law y Surv := fun y =>
      lintegral_indicator_one hSurv
    calc ENNReal.ofReal c0 * μ B = ENNReal.ofReal c0 * μ A := by rw [hBA]
      _ = ∫⁻ w in A, ENNReal.ofReal c0 ∂μ := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ w in A, (∫⁻ v, g v ∂law (position (T i w).toNNReal w)) ∂μ := by
          apply lintegral_mono_ae
          rw [ae_restrict_iff' hAm]
          filter_upwards [hnonexp] with w hw hwA
          rw [hinner]
          have hTfin : T i w < ⊤ := by
            have h2 : T i w < w.lifetime := hwA.2
            rw [hw] at h2; exact h2
          exact hV _ (hpath i hi w hw hTfin).1
      _ = ∫⁻ w in A, g (LifetimePath.shift (T i w).toNNReal w) ∂μ := hSMi.symm
      _ ≤ ∫⁻ w in A, E.indicator 1 w ∂μ := by
          apply lintegral_mono_ae
          rw [ae_restrict_iff' hAm]
          filter_upwards [hnonexp] with w hw hwA
          have hTfin : T i w < ⊤ := by
            have h2 : T i w < w.lifetime := hwA.2
            rw [hw] at h2; exact h2
          by_cases hs : LifetimePath.shift (T i w).toNNReal w ∈ Surv
          · have := (hpath i hi w hw hTfin).2 hs
            simp [hg, hs, Set.indicator_of_mem (show w ∈ E from this)]
          · simp [hg, hs]
      _ ≤ μ (E ∩ A) := by
          rw [← Measure.restrict_apply' hAm]
          exact lintegral_indicator_one_le E
      _ ≤ μ (B ∩ E) := measure_mono (fun w hw => ⟨hw.2.1, hw.1⟩)

/-- **The iterated strong-Markov bound** (the common-semigroup crossing lemma, clause 1) applied to the crossing built from survival. -/
theorem aux_lem_crossing_bound_of_survival (c0 : ℝ) (hc0 : 0 < c0) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {d : ℕ} (_hd : 2 ≤ d) (law : Kernel (Homogenization.Vec d) (Path d))
        (_hSM : StrongMarkov law) (x : Homogenization.Vec d)
        (_hnonexp : ∀ᵐ w ∂law x, w.lifetime = ⊤)
        (F0 t : ℝ) (_ht : 0 < t) (_hF0 : 0 < F0) (n : ℕ)
        (T : ℕ → Path d → ℝ≥0∞)
        (_hT : ∀ i, IsStoppingTime LifetimePath.canonicalFiltration (T i))
        (_hmono : ∀ i w, T i w ≤ T (i + 1) w)
        (V : Set (Homogenization.Vec d)) (Surv : Set (Path d)) (_hSurv : MeasurableSet Surv)
        (_hV : ∀ y ∈ V, ENNReal.ofReal c0 ≤ law y Surv)
        (_hpath : ∀ i < n, ∀ w : Path d, w.lifetime = ⊤ → T i w < ⊤ →
          position (T i w).toNNReal w ∈ V ∧
            (LifetimePath.shift (T i w).toNNReal w ∈ Surv →
              ENNReal.ofReal (c0 * F0) ≤ T (i + 1) w - T i w)),
        law x {w | T n w ≤ ENNReal.ofReal t} ≤
          ENNReal.ofReal (Real.exp (C * t / F0 - c * n)) := by
  obtain ⟨c, C, hc, hC, h1, -, -⟩ := _root_.SubdiffusiveProcess.Section8.common_semigroup_crossing c0 hc0
  refine ⟨c, C, hc, hC, ?_⟩
  intro d hd law hSM x hnonexp F0 t ht hF0 n T hT hmono V Surv hSurv hV hpath
  have : IsProbabilityMeasure (law x) := ⟨hSM.1 x⟩
  exact h1 d hd (law x) inferInstance t F0 ht hF0 n _ ((hT n) (Real.toNNReal t))
    (aux_lem_crossing_crossing_of_survival law hSM x hnonexp c0 F0 t n T hT hmono V Surv hSurv
      hV hpath)


section QCoreMain

attribute [local instance] Classical.propDecidable

variable {d : ℕ}

theorem aux_lem_crossing_core_numeric {cs Cs c0 κ C u F X : ℝ} {n₀ : ℕ}
    (hcs : 0 < cs) (hc0 : 0 < c0) (hκ : 0 < κ) (hu : 0 < u) (hF : 0 < F)
    (hCexp : Real.exp (2 * cs) ≤ C) (hCs : 2 * c0 * Cs / κ ≤ C)
    (hn₀ : 1 ≤ n₀) (hX : X < n₀ + 1) :
    Real.exp (Cs * u / (κ * F / (2 * c0)) - cs * ((n₀ - 1 : ℕ) : ℝ)) ≤
      C * Real.exp (C * u / F - cs * X) := by
  have hn : (((n₀ - 1 : ℕ) : ℝ)) = (n₀ : ℝ) - 1 := by
    rw [Nat.cast_sub hn₀, Nat.cast_one]
  have h1 : Cs * u / (κ * F / (2 * c0)) = (2 * c0 * Cs / κ) * (u / F) := by
    field_simp
  have h2 : (2 * c0 * Cs / κ) * (u / F) ≤ C * (u / F) :=
    mul_le_mul_of_nonneg_right hCs (div_nonneg hu.le hF.le)
  have h3 : C * (u / F) = C * u / F := by ring
  calc Real.exp (Cs * u / (κ * F / (2 * c0)) - cs * ((n₀ - 1 : ℕ) : ℝ))
      ≤ Real.exp (2 * cs + (C * u / F - cs * X)) := by
        apply Real.exp_le_exp.mpr
        rw [h1, hn]
        nlinarith
    _ = Real.exp (2 * cs) * Real.exp (C * u / F - cs * X) := Real.exp_add _ _
    _ ≤ C * Real.exp (C * u / F - cs * X) :=
        mul_le_mul_of_nonneg_right hCexp (Real.exp_pos _).le

/-- **Quenched crossing core** (fixed environment).  Built from the path-discretization lemma, the
chronological-selection lemma, the local torsion survival estimate and the common-semigroup crossing
lemma: a strong-Markov nonexplosive law whose good cubes carry the two-sided mean-exit bounds (the
output of the local torsion lemma), and whose good sites are dense along every fine lattice path
of reach `R` from `x` (the output of the percolation lemmas), satisfies the crossing
estimate at `x`. -/
theorem aux_lem_crossing_quenched_core (hd : 2 ≤ d) (κ Aκ c₁ : ℝ) (hκ : 0 < κ)
    (hκA : κ ≤ Aκ) (hc₁ : 0 < c₁) :
    ∃ c C : ℝ, 0 < c ∧ 1 ≤ C ∧
      ∀ (law : Kernel (Homogenization.Vec d) (Path d)) (_hSM : StrongMarkov law)
        (ℓ F : ℝ) (_hℓ : 0 < ℓ) (_hF : 0 < F) (_e : ℕ ≃ Lattice d) (Good : Set (Lattice d))
        (_htors : ∀ k ∈ Good,
          (∀ y ∈ middleQuarter (aux_lem_crossing_G ℓ k),
            ENNReal.ofReal (κ * F) ≤ meanExit law (cubeSet (aux_lem_crossing_G ℓ k)) y) ∧
          (∀ y ∈ cubeSet (aux_lem_crossing_G ℓ k),
            meanExit law (cubeSet (aux_lem_crossing_G ℓ k)) y ≤ ENNReal.ofReal (Aκ * F)))
        (x : Homogenization.Vec d) (_hnonexp : ∀ᵐ w ∂law x, w.lifetime = ⊤)
        (R : ℝ) (_hR : C * ℓ ≤ R)
        (_hgood : ∀ (N : ℕ) (q : ℕ → Lattice d), IsJStepPath 1 q N →
          Set.InjOn q (Set.Icc 0 N) → x ∈ cubeSet (aux_lem_crossing_W ℓ (q 0)) →
          (∃ y ∈ cubeSet (aux_lem_crossing_W ℓ (q N)), R ≤ dist y x) →
          c₁ * R / ℓ ≤ (((Finset.range (N + 1)).filter (fun i => q i ∈ Good)).card : ℝ))
        (u : ℝ) (_hu : 0 < u),
        law x (aux_lem_crossing_lifeEvent u R x) ≤
          ENNReal.ofReal (C * Real.exp (C * u / F - c * R / ℓ)) := by
  obtain ⟨c0, hc0, hsurv⟩ := _root_.SubdiffusiveProcess.Section8.local_torsion_survival κ Aκ hκ hκA
  obtain ⟨cs, Cs, hcs, hCs, hbound⟩ := aux_lem_crossing_bound_of_survival c0 hc0
  obtain ⟨cpd, hcpd, hcount⟩ := aux_lem_crossing_count (d := d) hd
  have hDpos : (0 : ℝ) < ((48 * 2 + 1) ^ d : ℕ) := by positivity
  set D : ℝ := (((48 * 2 + 1) ^ d : ℕ) : ℝ) with hD
  set C : ℝ := max (max 1 (2 * c0 * Cs / κ)) (Real.exp (2 * cs)) with hCdef
  have hC1 : 1 ≤ C := le_max_of_le_left (le_max_left _ _)
  have hCs' : 2 * c0 * Cs / κ ≤ C := le_max_of_le_left (le_max_right _ _)
  have hCexp : Real.exp (2 * cs) ≤ C := le_max_right _ _
  refine ⟨cs * cpd * c₁ / D, C, by positivity, hC1, ?_⟩
  intro law hSM ℓ F hℓ hF e Good htors x hnonexp R hR hgood u hu
  have hℓR : ℓ ≤ R := le_trans (le_mul_of_one_le_left hℓ.le hC1) hR
  set X : ℝ := cpd * (c₁ * R / ℓ) / D with hXdef
  have hX : 0 ≤ X := by
    have : 0 ≤ R := hℓ.le.trans hℓR
    positivity
  have hcX : cs * cpd * c₁ / D * R / ℓ = cs * X := by
    rw [hXdef]; field_simp
  have : IsProbabilityMeasure (law x) := ⟨hSM.1 x⟩
  rw [hcX]
  by_cases hn₀ : ⌊X⌋₊ = 0
  · -- the bound is at least one
    have hXlt : X < 1 := Nat.floor_eq_zero.mp hn₀
    refine prob_le_one.trans ?_
    rw [ENNReal.one_le_ofReal]
    have h1 : Real.exp (-cs) ≤ Real.exp (C * u / F - cs * X) := by
      apply Real.exp_le_exp.mpr
      have : 0 ≤ C * u / F := by positivity
      nlinarith
    calc (1 : ℝ) = Real.exp (2 * cs) * Real.exp (-cs) * Real.exp (-cs) := by
          rw [← Real.exp_add, ← Real.exp_add, show 2 * cs + -cs + -cs = 0 by ring, Real.exp_zero]
      _ ≤ C * Real.exp (C * u / F - cs * X) * 1 := by
          apply mul_le_mul _ (Real.exp_le_one_iff.mpr (by linarith)) (Real.exp_pos _).le
            (by positivity)
          exact mul_le_mul hCexp h1 (Real.exp_pos _).le (by linarith)
      _ = C * Real.exp (C * u / F - cs * X) := mul_one _
  · set n₀ := ⌊X⌋₊ with hn₀def
    have hn₀pos : 1 ≤ n₀ := Nat.one_le_iff_ne_zero.mpr hn₀
    set n := n₀ - 1 with hndef
    have hsel := aux_lem_crossing_selection hd hℓ e Good
    dsimp only at hsel
    obtain ⟨h1, h2, -, -⟩ := hsel
    set τ : ℕ → ContinuousPath (Homogenization.Vec d) → ℝ≥0∞ :=
      fun i p => aux_lem_crossing_ent ℓ e Good (i + 1) p with hτdef
    have hτ : ∀ i, IsStoppingTime ContinuousPath.canonicalFiltration (τ i) :=
      fun i => (h1 (i + 1)).1
    have hτmono : ∀ i p, τ i p ≤ τ (i + 1) p := fun i p =>
      (h2 (i + 1) p).1.trans (h2 (i + 1) p).2
    obtain ⟨hT, hTmono, hTeq⟩ := aux_lem_crossing_liftFamily τ hτ hτmono
    set T := aux_lem_crossing_runMax (fun i => aux_lem_crossing_liftStop (τ i)) with hTdef
    set Fs := aux_lem_crossing_Fs e Good with hFs
    set V : Set (Homogenization.Vec d) :=
      {y | ∃ m ∈ Fs, y ∈ closedQuarter (aux_lem_crossing_U ℓ e m)} with hVdef
    set Surv := aux_lem_crossing_surv ℓ (κ * F / 2) e Fs with hSurvdef
    set F0 : ℝ := κ * F / (2 * c0) with hF0def
    have hF0 : 0 < F0 := by positivity
    have hc0F0 : c0 * F0 = κ * F / 2 := by rw [hF0def]; field_simp
    have hV : ∀ y ∈ V, ENNReal.ofReal c0 ≤ law y Surv := fun y hy =>
      aux_lem_crossing_surv_bound hsurv hd law hSM hℓ hF e Good htors hy
    have hpath : ∀ i < n, ∀ w : Path d, w.lifetime = ⊤ → T i w < ⊤ →
        position (T i w).toNNReal w ∈ V ∧
          (LifetimePath.shift (T i w).toNNReal w ∈ Surv →
            ENNReal.ofReal (c0 * F0) ≤ T (i + 1) w - T i w) := by
      intro i _ w hw hTi
      set p := LifetimePath.toContinuousPath w hw with hpdef
      have hTi' : T i w = aux_lem_crossing_ent ℓ e Good (i + 1) p := hTeq i w hw
      have hTi1 : T (i + 1) w = aux_lem_crossing_ent ℓ e Good (i + 1 + 1) p := hTeq (i + 1) w hw
      have hent : aux_lem_crossing_ent ℓ e Good (i + 1) p < ⊤ := hTi' ▸ hTi
      obtain ⟨hstepV, hstepOut⟩ := aux_lem_crossing_path_step hd hℓ e Good p i hent
      have hpos : position (T i w).toNNReal w =
          p (aux_lem_crossing_ent ℓ e Good (i + 1) p).toNNReal := by
        rw [aux_lem_crossing_position_of_top hw, hTi']
      refine ⟨hpos ▸ hstepV, ?_⟩
      intro hshift
      rw [hc0F0]
      obtain ⟨m₀, _, _, hselm₀⟩ := aux_lem_crossing_selIndexAt_exists hℓ e Fs hstepV
      have hsurvw := hshift m₀ (by
        rw [aux_lem_crossing_position_shift_of_top hw, hTi']; exact hselm₀)
      rw [hTi'] at hsurvw
      by_cases hinf : aux_lem_crossing_ent ℓ e Good (i + 1 + 1) p = ⊤
      · rw [hTi1, hinf, hTi', ENNReal.top_sub hent.ne]
        exact le_top
      · have hlt : aux_lem_crossing_ent ℓ e Good (i + 1 + 1) p < ⊤ := lt_top_iff_ne_top.mpr hinf
        have hout := hstepOut hlt m₀ hselm₀
        have htt' : (aux_lem_crossing_ent ℓ e Good (i + 1) p).toNNReal ≤
            (aux_lem_crossing_ent ℓ e Good (i + 1 + 1) p).toNNReal :=
          ENNReal.toNNReal_mono hinf (hτmono i p)
        have hex := aux_lem_crossing_exitTime_shift_le hw htt' hout
        calc ENNReal.ofReal (κ * F / 2)
            ≤ LifetimePath.exitTime (cubeSet (aux_lem_crossing_G ℓ (e m₀)))
                (LifetimePath.shift (aux_lem_crossing_ent ℓ e Good (i + 1) p).toNNReal w) :=
              hsurvw
          _ ≤ _ := hex
          _ = T (i + 1) w - T i w := by
              rw [hTi1, hTi', ENNReal.coe_sub, ENNReal.coe_toNNReal hinf,
                ENNReal.coe_toNNReal hent.ne]
    have hB := hbound hd law hSM x hnonexp F0 u hu hF0 n T hT hTmono V Surv
      (aux_lem_crossing_measurableSet_surv _ _ _ _) hV hpath
    have hkD : ((n₀ * (48 * 2 + 1) ^ d : ℕ) : ℝ) ≤ cpd * (c₁ * R / ℓ) := by
      have h := Nat.floor_le hX
      rw [← hn₀def] at h
      have : (n₀ : ℝ) * D ≤ cpd * (c₁ * R / ℓ) := by
        rw [hXdef, le_div_iff₀ hDpos] at h; exact h
      push_cast
      simpa [hD] using this
    have hsub : law x (aux_lem_crossing_lifeEvent u R x) ≤
        law x {w | T n w ≤ ENNReal.ofReal u} := by
      apply measure_mono_ae
      filter_upwards [hnonexp, hSM.2.1 x] with w hw hw0 hwE
      obtain ⟨s, hsu, y, hy, hRy⟩ := hwE
      set p := LifetimePath.toContinuousPath w hw with hpdef
      have hp0 : p 0 = x := by
        have := aux_lem_crossing_position_of_top hw 0
        rw [← this]; simp only [position, hw0]; rfl
      have hps : p s = y := by
        have := aux_lem_crossing_position_of_top hw s
        rw [← this]; simp only [position, hy]; rfl
      have hk := hcount hℓ e Good c₁ x R hℓR hgood p hp0 s (hps ▸ hRy) n₀ hn₀pos hkD
      show T n w ≤ ENNReal.ofReal u
      rw [hTeq n w hw]
      show aux_lem_crossing_ent ℓ e Good (n + 1) p ≤ ENNReal.ofReal u
      rw [hndef, Nat.sub_add_cancel hn₀pos]
      refine hk.trans ?_
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal hsu
    refine hsub.trans (hB.trans (ENNReal.ofReal_le_ofReal ?_))
    exact aux_lem_crossing_core_numeric hcs hc0 hκ hu hF hCexp hCs' hn₀pos
      (by have := Nat.lt_floor_add_one X; rw [← hn₀def] at this; exact_mod_cast this)

end QCoreMain

end SubdiffusiveProcess.Paper

namespace SubdiffusiveProcess.Paper

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput (Path position)

/-- Pulled back along `ofContinuousPath`, the lifetime event is exactly the
continuous-path event of `lem_crossing`. -/
theorem aux_lem_crossing_preimage_lifeEvent {d : ℕ} (T R : ℝ) (x : SpatialCoordinates d) :
    LifetimePath.ofContinuousPath ⁻¹' aux_lem_crossing_lifeEvent (d := d) T R x =
      {path : DiffusionPath d | ∃ s : ℝ≥0, (s : ℝ) ≤ T ∧ R ≤ dist (path s) x} := by
  ext path
  simp only [aux_lem_crossing_lifeEvent, Set.mem_preimage, Set.mem_ofPred_eq,
    LifetimePath.coordinate_ofContinuousPath]
  constructor
  · rintro ⟨s, hs, y, hy, hR⟩
    have : path s = y := Sum.inl.inj hy
    exact ⟨s, hs, this ▸ hR⟩
  · rintro ⟨s, hs, hR⟩
    exact ⟨s, hs, path s, rfl, hR⟩

/-- On the lifetime event the GMC `position` is the live coordinate. -/
theorem aux_lem_crossing_lifeEvent_position {d : ℕ} (T R : ℝ) (x : SpatialCoordinates d)
    (w : SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d) :
    w ∈ aux_lem_crossing_lifeEvent T R x ↔
      ∃ s : ℝ≥0, (s : ℝ) ≤ T ∧ (s : ℝ≥0∞) < w.lifetime ∧ R ≤ dist (position s w) x := by
  constructor
  · rintro ⟨s, hs, y, hy, hR⟩
    refine ⟨s, hs, ?_, ?_⟩
    · have hne : LifetimePath.coordinate s w ≠ Cemetery.delta := by
        rw [hy]; exact Sum.inl_ne_inr
      exact (LifetimePath.coordinate_ne_delta_iff w s).mp hne
    · simp only [position, hy]
      exact hR
  · rintro ⟨s, hs, hlt, hR⟩
    refine ⟨s, hs, w.livePath ⟨s, hlt⟩, LifetimePath.coordinate_of_lt w s hlt, ?_⟩
    simpa [position, LifetimePath.coordinate_of_lt w s hlt] using hR

/-- **Event comparison (lifetime ← continuous).**  For every set of lifetime
paths, the carried law `L` dominates the `KN` law of the preimage; no
measurability is needed. -/
theorem aux_lem_crossing_KN_le_L {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (L : ℕ → BilateralField d →
      Kernel (SpatialCoordinates d) (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
    (hL : ∀ (N : ℕ) (omega : BilateralField d) (x : SpatialCoordinates d),
      Measure.map MarkovProcess.LifetimePath.ofContinuousPath (KN N (omega, x)) = L N omega x)
    (N : ℕ) (omega : BilateralField d) (x : SpatialCoordinates d)
    (E : Set (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d)) :
    KN N (omega, x) (LifetimePath.ofContinuousPath ⁻¹' E) ≤ L N omega x E := by
  rw [← hL N omega x]
  exact Measure.le_map_apply
    (LifetimePath.measurable_ofContinuousPath).aemeasurable E

/-- **The physical exit event, lifetime form.**  The `KN` probability of the
continuous-path event of `lem_crossing` is at most the `L` probability of the
lifetime event. -/
theorem aux_lem_crossing_exit_KN_le_L {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (L : ℕ → BilateralField d →
      Kernel (SpatialCoordinates d) (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
    (hL : ∀ (N : ℕ) (omega : BilateralField d) (x : SpatialCoordinates d),
      Measure.map MarkovProcess.LifetimePath.ofContinuousPath (KN N (omega, x)) = L N omega x)
    (N : ℕ) (omega : BilateralField d) (x : SpatialCoordinates d) (T R : ℝ) :
    KN N (omega, x) {path : DiffusionPath d | ∃ s : ℝ≥0, (s : ℝ) ≤ T ∧ R ≤ dist (path s) x} ≤
      L N omega x (aux_lem_crossing_lifeEvent T R x) := by
  rw [← aux_lem_crossing_preimage_lifeEvent]
  exact aux_lem_crossing_KN_le_L KN L hL N omega x _

/-- The carried law `L N omega x` is concentrated on nonexplosive paths. -/
theorem aux_lem_crossing_L_lifetime_top {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (L : ℕ → BilateralField d →
      Kernel (SpatialCoordinates d) (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
    (hL : ∀ (N : ℕ) (omega : BilateralField d) (x : SpatialCoordinates d),
      Measure.map MarkovProcess.LifetimePath.ofContinuousPath (KN N (omega, x)) = L N omega x)
    (N : ℕ) (omega : BilateralField d) (x : SpatialCoordinates d) :
    ∀ᵐ w ∂(L N omega x), w.lifetime = ∞ := by
  rw [← hL N omega x]
  rw [ae_map_iff LifetimePath.measurable_ofContinuousPath.aemeasurable]
  · exact Filter.Eventually.of_forall (fun path => LifetimePath.lifetime_ofContinuousPath path)
  · exact (LifetimePath.measurable_lifetime (α := SpatialCoordinates d))
      (measurableSet_singleton ∞)

end SubdiffusiveProcess.Paper

namespace SubdiffusiveProcess.Paper

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9PathGeometry
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation (Lattice IsJStepPath)

section EnvAssembly

attribute [local instance] Classical.propDecidable

/-- **The environment residual.**  For the actual cutoff-zero data of `lem_crossing`, at each
triadic scale `3^n` and reach `R ≥ CB 3^n`, outside an exceptional environment event of the
displayed probability there are: a strong-Markov lifetime law `law` (the cutoff-zero law on
the raw clock), a set `Good` of fine lattice sites whose good cubes carry the two-sided
mean-exit bounds at clock `F = T(3^n)`, the percolation density of `Good` along lattice paths
of reach `R` from every starting point of the region, and the comparison of the physical event
with the lifetime event. -/
def aux_lem_crossing_envResidual (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] : Prop :=
  ∃ (cgood delta0 : ℝ), 0 < cgood ∧ 0 < delta0 ∧ delta0 ≤ cgood ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
      ∃ (κ Aκ c₁ cB CB : ℝ), 0 < κ ∧ κ ≤ Aκ ∧ 0 < c₁ ∧ 0 < cB ∧ 0 < CB ∧
        ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
          (_hH : InfraredCharacterization M H)
          (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
          (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
          (_hKN : ∀ N, IsMarkovKernel (KN N))
          (_hin : in_crossing M H PN KN)
          (L : ℕ → BilateralField d →
            Kernel (SpatialCoordinates d)
              (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
          (_hL : ∀ (N : ℕ) (omega : BilateralField d) (x : SpatialCoordinates d),
            Measure.map MarkovProcess.LifetimePath.ofContinuousPath (KN N (omega, x)) =
              L N omega x)
          (_hLlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            ∀ (N : ℕ),
              SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusionData
                (cutoffCoefficient M H omega N)
                (cutoffSpeedDensity M H omega N)
                (L N omega))
          (_hLstrong : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            ∀ (N : ℕ),
              SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.StrongMarkov (L N omega))
          (Region : Set (SpatialCoordinates d)), Bornology.IsBounded Region →
          ∀ (n : ℕ) (R : ℝ), CB * (3 : ℝ) ^ n ≤ R →
            ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
              (chaosSampleLaw M).toMeasure Bad ≤
                ENNReal.ofReal (CB * (1 + Metric.diam Region / (3 : ℝ) ^ n) ^ d *
                  Real.exp (-(cB * (cgood / (M.delta ^ 2 * |Real.log M.delta| ^ 2)) *
                    R / (3 : ℝ) ^ n))) ∧
              ∀ omega, omega ∉ Bad →
                ∃ (law : Kernel (Homogenization.Vec d) (Path d)) (_e : ℕ ≃ Lattice d)
                  (Good : Set (Lattice d)),
                  StrongMarkov law ∧
                  (∀ k ∈ Good,
                    (∀ y ∈ middleQuarter (aux_lem_crossing_G ((3 : ℝ) ^ n) k),
                      ENNReal.ofReal (κ * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
                          (SubdiffusiveProcess.CoarseGrainingVocab.ahom M) ((3 : ℝ) ^ n)) ≤
                        meanExit law (cubeSet (aux_lem_crossing_G ((3 : ℝ) ^ n) k)) y) ∧
                    (∀ y ∈ cubeSet (aux_lem_crossing_G ((3 : ℝ) ^ n) k),
                      meanExit law (cubeSet (aux_lem_crossing_G ((3 : ℝ) ^ n) k)) y ≤
                        ENNReal.ofReal (Aκ * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
                          (SubdiffusiveProcess.CoarseGrainingVocab.ahom M) ((3 : ℝ) ^ n)))) ∧
                  ∀ x ∈ Region,
                    (∀ᵐ w ∂law x, w.lifetime = ⊤) ∧
                    (∀ (N : ℕ) (q : ℕ → Lattice d), IsJStepPath 1 q N →
                      Set.InjOn q (Set.Icc 0 N) →
                      x ∈ cubeSet (aux_lem_crossing_W ((3 : ℝ) ^ n) (q 0)) →
                      (∃ y ∈ cubeSet (aux_lem_crossing_W ((3 : ℝ) ^ n) (q N)), R ≤ dist y x) →
                      c₁ * R / (3 : ℝ) ^ n ≤
                        (((Finset.range (N + 1)).filter (fun i => q i ∈ Good)).card : ℝ)) ∧
                    ∀ u : ℝ, 0 < u →
                      (KN 0 (omega, x))
                          {path : DiffusionPath d |
                            ∃ s : ℝ≥0, (s : ℝ) ≤ SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 * u ∧
                              R ≤ dist (path s) x} ≤
                        law x (aux_lem_crossing_lifeEvent u R x)

/-- Triadic block of a radius `r ≥ 1`. -/
theorem aux_lem_crossing_triadic_block {r : ℝ} (hr : 1 ≤ r) :
    ∃ n : ℕ, (3 : ℝ) ^ n ≤ r ∧ r < 3 * (3 : ℝ) ^ n := by
  refine ⟨⌊Real.logb 3 r⌋₊, ?_, ?_⟩
  · have hlog : 0 ≤ Real.logb 3 r := Real.logb_nonneg (by norm_num) hr
    have h := Nat.floor_le hlog
    calc (3 : ℝ) ^ ⌊Real.logb 3 r⌋₊ = (3 : ℝ) ^ ((⌊Real.logb 3 r⌋₊ : ℕ) : ℝ) :=
          (Real.rpow_natCast 3 _).symm
      _ ≤ (3 : ℝ) ^ (Real.logb 3 r) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h
      _ = r := Real.rpow_logb (by norm_num) (by norm_num) (lt_of_lt_of_le one_pos hr)
  · have h := Nat.lt_floor_add_one (Real.logb 3 r)
    calc r = (3 : ℝ) ^ (Real.logb 3 r) :=
          (Real.rpow_logb (by norm_num) (by norm_num) (lt_of_lt_of_le one_pos hr)).symm
      _ < (3 : ℝ) ^ ((⌊Real.logb 3 r⌋₊ : ℝ) + 1) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h
      _ = 3 * (3 : ℝ) ^ ⌊Real.logb 3 r⌋₊ := by
          rw [Real.rpow_add (by norm_num), Real.rpow_one, Real.rpow_natCast]; ring

/-- **The physical residual from the environment residual** (with the quenched core and the
clock normalization). -/
theorem aux_lem_crossing_physicalResidual_of_env {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (henv : aux_lem_crossing_envResidual d) :
    aux_lem_crossing_physicalResidual d := by
  obtain ⟨cgood, delta0, hcg, hd0, hd0le, hM⟩ := henv
  refine ⟨cgood, delta0, hcg, hd0, hd0le, ?_⟩
  intro M hMdelta Tscale hT3 hTint
  obtain ⟨κ, Aκ, c₁, cB, CB, hκ, hκA, hc₁, hcB, hCB, hdata⟩ := hM M hMdelta
  obtain ⟨cq, Cq, hcq, hCq, hcore⟩ := aux_lem_crossing_quenched_core hd κ Aκ c₁ hκ hκA hc₁
  obtain ⟨TT, CT, beta, hCT, hbeta, hTT3, hTTint, hTTpos, -, hTTscal⟩ := _root_.SubdiffusiveProcess.Paper.in_timescale hd M
  have hTeq : ∀ r : ℝ, 1 ≤ r → Tscale r = TT r := fun r hr => by
    rw [aux_lem_crossing_Tscale_eq_timeScale M Tscale hT3 hTint hr,
      aux_lem_crossing_Tscale_eq_timeScale M TT hTT3 hTTint hr]
  set K : ℝ := CT * (3 : ℝ) ^ beta with hK
  have hKpos : 0 < K := by positivity
  set C : ℝ := max (max (Cq * K) Cq) (max (CB * 3 ^ d) CB) with hCdef
  set c : ℝ := min cq cB with hcdef
  have hc : 0 < c := lt_min hcq hcB
  have hC1 : Cq ≤ C := le_max_of_le_left (le_max_right _ _)
  have hC2 : Cq * K ≤ C := le_max_of_le_left (le_max_left _ _)
  have hC3 : CB * 3 ^ d ≤ C := le_max_of_le_right (le_max_left _ _)
  have hC4 : CB ≤ C := le_max_of_le_right (le_max_right _ _)
  have hCpos : 0 < C := lt_of_lt_of_le (by linarith) hC1
  refine ⟨c, C, hc, hCpos, ?_⟩
  intro H hH PN KN hKN hin L hL hLlocal hLstrong Region hRegion r R hr hR
  obtain ⟨n, hnr, hrn⟩ := aux_lem_crossing_triadic_block hr
  have h3n : 0 < (3 : ℝ) ^ n := by positivity
  have hrpos : 0 < r := lt_of_lt_of_le one_pos hr
  have hRn : CB * (3 : ℝ) ^ n ≤ R :=
    (mul_le_mul hC4 hnr h3n.le hCpos.le).trans hR
  set q : ℝ := cgood / (M.delta ^ 2 * |Real.log M.delta| ^ 2) with hq
  have hqpos : 0 < q := by
    have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
    have hlog : Real.log M.delta < 0 :=
      Real.log_neg hδpos (by linarith [M.shellPrefix.delta_le_half])
    have : 0 < |Real.log M.delta| := abs_pos.mpr hlog.ne
    positivity
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hR
  obtain ⟨Bad, hBadm, hBadμ, hBad⟩ :=
    hdata H hH PN KN hKN hin L hL hLlocal hLstrong Region hRegion n R hRn
  refine ⟨Bad, hBadm, hBadμ.trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
  · -- probability bound comparison
    have hdiam := Metric.diam_nonneg (s := Region)
    have h1 : 1 + Metric.diam Region / (3 : ℝ) ^ n ≤ 3 * (1 + Metric.diam Region / r) := by
      have : Metric.diam Region / (3 : ℝ) ^ n ≤ 3 * (Metric.diam Region / r) := by
        rw [div_le_iff₀ h3n]
        calc Metric.diam Region = Metric.diam Region / r * r := by field_simp
          _ ≤ Metric.diam Region / r * (3 * (3 : ℝ) ^ n) :=
              mul_le_mul_of_nonneg_left hrn.le (by positivity)
          _ = 3 * (Metric.diam Region / r) * (3 : ℝ) ^ n := by ring
      linarith
    have h2 : (1 + Metric.diam Region / (3 : ℝ) ^ n) ^ d ≤
        3 ^ d * (1 + Metric.diam Region / r) ^ d := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h1 d
    have h3 : Real.exp (-(cB * q * R / (3 : ℝ) ^ n)) ≤ Real.exp (-(c * q * R / r)) := by
      apply Real.exp_le_exp.mpr
      have ha : c * q * R / r ≤ cB * q * R / r := by
        apply div_le_div_of_nonneg_right _ hrpos.le
        have := min_le_right cq cB
        have : 0 ≤ q * R := by positivity
        nlinarith
      have hb : cB * q * R / r ≤ cB * q * R / (3 : ℝ) ^ n :=
        div_le_div_of_nonneg_left (by positivity) h3n hnr
      linarith
    calc CB * (1 + Metric.diam Region / (3 : ℝ) ^ n) ^ d *
          Real.exp (-(cB * q * R / (3 : ℝ) ^ n))
        ≤ CB * (3 ^ d * (1 + Metric.diam Region / r) ^ d) * Real.exp (-(c * q * R / r)) := by
          gcongr
      _ = CB * 3 ^ d * (1 + Metric.diam Region / r) ^ d * Real.exp (-(c * q * R / r)) := by
          ring
      _ ≤ C * (1 + Metric.diam Region / r) ^ d * Real.exp (-(c * q * R / r)) := by
          gcongr
  · intro omega homega x hx u hu
    obtain ⟨law, e, Good, hSM, htors, hx'⟩ := hBad omega homega
    obtain ⟨hnonexp, hgood, hcomp⟩ := hx' x hx
    have hF : 0 < SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom M) ((3 : ℝ) ^ n) :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale_pos
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M) h3n
    have hRq : Cq * (3 : ℝ) ^ n ≤ R := (mul_le_mul hC1 hnr h3n.le hCpos.le).trans hR
    have hcoreb := hcore law hSM ((3 : ℝ) ^ n) _ h3n hF e Good htors x hnonexp R hRq hgood u hu
    refine (hcomp u hu).trans (hcoreb.trans (ENNReal.ofReal_le_ofReal ?_))
    -- numeric comparison
    set F := SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom M) ((3 : ℝ) ^ n) with hFdef
    have h1n : (1 : ℝ) ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hFT : F = Tscale ((3 : ℝ) ^ n) :=
      (aux_lem_crossing_Tscale_eq_timeScale M Tscale hT3 hTint h1n).symm
    have hTr : Tscale r ≤ K * F := by
      rw [hTeq r hr, hFT, hTeq _ h1n]
      have := hTTscal ((3 : ℝ) ^ n) r h1n hnr
      refine this.trans ?_
      have hratio : (r / (3 : ℝ) ^ n) ^ beta ≤ (3 : ℝ) ^ beta := by
        apply Real.rpow_le_rpow (by positivity) _ hbeta.le
        rw [div_le_iff₀ h3n]; linarith
      have hT0 := (hTTpos _ h1n).le
      rw [hK]
      calc CT * (r / (3 : ℝ) ^ n) ^ beta * TT ((3 : ℝ) ^ n)
          ≤ CT * (3 : ℝ) ^ beta * TT ((3 : ℝ) ^ n) := by gcongr
        _ = _ := by ring
    have hTrpos : 0 < Tscale r := by rw [hTeq r hr]; exact hTTpos r hr
    have hu1 : Cq * u / F ≤ C * u / Tscale r := by
      rw [div_le_div_iff₀ hF hTrpos]
      calc Cq * u * Tscale r ≤ Cq * u * (K * F) := by gcongr
        _ = (Cq * K) * u * F := by ring
        _ ≤ C * u * F := by gcongr
    have hu2 : c * R / r ≤ cq * R / (3 : ℝ) ^ n := by
      have ha : c * R / r ≤ cq * R / r := by
        apply div_le_div_of_nonneg_right _ hrpos.le
        exact mul_le_mul_of_nonneg_right (min_le_left _ _) hRpos.le
      have hb : cq * R / r ≤ cq * R / (3 : ℝ) ^ n :=
        div_le_div_of_nonneg_left (by positivity) h3n hnr
      linarith
    have hexp : Real.exp (Cq * u / F - cq * R / (3 : ℝ) ^ n) ≤
        Real.exp (C * u / Tscale r - c * R / r) := Real.exp_le_exp.mpr (by linarith)
    exact mul_le_mul hC1 hexp (Real.exp_pos _).le hCpos.le

end EnvAssembly

end SubdiffusiveProcess.Paper
namespace SubdiffusiveProcess.Paper



theorem aux_lem_crossing_of_envResidual
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) (henv : aux_lem_crossing_envResidual d) :
    ∃ (cgood delta0 : ℝ), 0 < cgood ∧ 0 < delta0 ∧ delta0 ≤ cgood ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
        ∃ (c C beta : ℝ) (Tscale : ℝ → ℝ),
          0 < c ∧ 0 < C ∧ 0 < beta ∧
          (∀ m : ℕ, Tscale ((3 : ℝ) ^ m) =
            ((3 : ℝ) ^ (2 * m) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M m)) ∧
          (∀ (m : ℕ) (t : ℝ), 0 ≤ t → t ≤ 1 →
            Tscale ((3 : ℝ) ^ ((m : ℝ) + t))
              = ((3 : ℝ) ^ (2 * m) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M m) ^ (1 - t)
                * ((3 : ℝ) ^ (2 * (m + 1)) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M (m + 1)) ^ t) ∧
          (∀ r : ℝ, 1 ≤ r → 0 < Tscale r) ∧
          (beta ≤ 2 + 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P / Real.log 3) ∧
          (∀ r S : ℝ, 1 ≤ r → r ≤ S → Tscale S ≤ C * (S / r) ^ beta * Tscale r) ∧
          (let q : ℝ := cgood / (M.delta ^ 2 * |Real.log M.delta| ^ 2)
           0 < q ∧
             ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
               (_hH : InfraredCharacterization M H)
               (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
               (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
               (_hKN : ∀ N, IsMarkovKernel (KN N))
               (_hin : in_crossing M H PN KN)
               (L : ℕ → BilateralField d →
                 Kernel (SpatialCoordinates d)
                   (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
               (_hL : ∀ (N : ℕ) (omega : BilateralField d) (x : SpatialCoordinates d),
                 Measure.map MarkovProcess.LifetimePath.ofContinuousPath (KN N (omega, x)) =
                   L N omega x)
               (_hLlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                 ∀ (N : ℕ),
                   SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusionData
                     (cutoffCoefficient M H omega N)
                     (cutoffSpeedDensity M H omega N)
                     (L N omega))
               (_hLstrong : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                 ∀ (N : ℕ),
                   SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.StrongMarkov
                     (L N omega)),
               (∀ (Region : Set (SpatialCoordinates d)), Bornology.IsBounded Region →
                 ∀ (r R : ℝ), 1 ≤ r → C * r ≤ R →
                   ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
                     (chaosSampleLaw M).toMeasure Bad ≤
                       ENNReal.ofReal (C * (1 + Metric.diam Region / r) ^ d *
                         Real.exp (-(c * q * R / r))) ∧
                     ∀ omega, omega ∉ Bad → ∀ x ∈ Region, ∀ u : ℝ, 0 < u →
                       (KN 0 (omega, x))
                           {path : DiffusionPath d |
                             ∃ s : ℝ≥0, (s : ℝ) ≤ SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 * u ∧
                               R ≤ dist (path s) x} ≤
                         ENNReal.ofReal (C * Real.exp (C * u / Tscale r - c * R / r))) ∧
               (∀ (N : ℕ) (Region : Set (SpatialCoordinates d)), Bornology.IsBounded Region →
                 ∀ (r R : ℝ), (3 : ℝ) ^ (-(N : ℝ)) ≤ r → C * r ≤ R →
                   ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
                     (chaosSampleLaw M).toMeasure Bad ≤
                       ENNReal.ofReal (C * (1 + Metric.diam Region / r) ^ d *
                         Real.exp (-(c * q * R / r))) ∧
                     ∀ omega, omega ∉ Bad → ∀ x ∈ Region, ∀ u : ℝ, 0 < u →
                       (KN N (omega, x))
                           {path : DiffusionPath d |
                             ∃ s : ℝ≥0, (s : ℝ) ≤ u ∧ R ≤ dist (path s) x} ≤
                         ENNReal.ofReal (C * Real.exp (C * u * Tscale ((3 : ℝ) ^ N) /
                           Tscale ((3 : ℝ) ^ N * r) - c * R / r)))) :=
  aux_lem_crossing_of_physicalResidual hd (aux_lem_crossing_physicalResidual_of_env hd henv)

end SubdiffusiveProcess.Paper
namespace SubdiffusiveProcess.Paper

section TimeChange

variable {α : Type*} [TopologicalSpace α]

theorem aux_lem_crossing_tc_lt {a : ℝ≥0} {ζ : ℝ≥0∞} {t : ℝ≥0} (h : (t : ℝ≥0∞) < ζ / a) :
    ((a * t : ℝ≥0) : ℝ≥0∞) < ζ := by
  have := ENNReal.mul_lt_of_lt_div h
  rw [mul_comm] at this
  exact_mod_cast this

/-- Time change of a lifetime path: `(tc a w) t = w (a t)`, lifetime `ζ / a`. -/
def aux_lem_crossing_tc (a : ℝ≥0) (w : LifetimePath α) : LifetimePath α where
  lifetime := w.lifetime / a
  livePath := fun t => w.livePath ⟨a * t, aux_lem_crossing_tc_lt t.2⟩
  continuous_livePath :=
    w.continuous_livePath.comp ((continuous_const.mul continuous_subtype_val).subtype_mk _)

theorem aux_lem_crossing_tc_lifetime (a : ℝ≥0) (w : LifetimePath α) :
    (aux_lem_crossing_tc a w).lifetime = w.lifetime / a := rfl

theorem aux_lem_crossing_coordinate_tc {a : ℝ≥0} (ha : 0 < a) (t : ℝ≥0) (w : LifetimePath α) :
    LifetimePath.coordinate t (aux_lem_crossing_tc a w) = LifetimePath.coordinate (a * t) w := by
  by_cases h : (t : ℝ≥0∞) < w.lifetime / a
  · rw [LifetimePath.coordinate_of_lt _ _ h,
      LifetimePath.coordinate_of_lt _ _ (aux_lem_crossing_tc_lt h)]
    rfl
  · have h' : w.lifetime ≤ ((a * t : ℝ≥0) : ℝ≥0∞) := by
      rw [not_lt, ENNReal.div_le_iff_le_mul (Or.inl (by exact_mod_cast ha.ne'))
        (Or.inl ENNReal.coe_ne_top)] at h
      rw [ENNReal.coe_mul, mul_comm]; exact h
    rw [LifetimePath.coordinate_of_le _ _ (not_lt.mp h), LifetimePath.coordinate_of_le _ _ h']

theorem aux_lem_crossing_tc_inv {a : ℝ≥0} (ha : 0 < a) (w : LifetimePath α) :
    aux_lem_crossing_tc a⁻¹ (aux_lem_crossing_tc a w) = w := by
  apply LifetimePath.ext_coordinate
  · simp only [aux_lem_crossing_tc_lifetime]
    rw [ENNReal.coe_inv ha.ne', div_eq_mul_inv, div_eq_mul_inv, inv_inv, mul_assoc,
      ENNReal.inv_mul_cancel (by exact_mod_cast ha.ne') ENNReal.coe_ne_top, mul_one]
  · intro t
    rw [aux_lem_crossing_coordinate_tc (inv_pos.mpr ha), aux_lem_crossing_coordinate_tc ha,
      ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]

theorem aux_lem_crossing_tc_inv' {a : ℝ≥0} (ha : 0 < a) (w : LifetimePath α) :
    aux_lem_crossing_tc a (aux_lem_crossing_tc a⁻¹ w) = w := by
  have := aux_lem_crossing_tc_inv (inv_pos.mpr ha) w
  rwa [inv_inv] at this

variable [MeasurableSpace α]

theorem aux_lem_crossing_measurable_tc_filtration {a : ℝ≥0} (ha : 0 < a) (t : ℝ≥0) :
    Measurable[LifetimePath.canonicalFiltration (alpha := α) (a * t),
      LifetimePath.canonicalFiltration (alpha := α) t] (aux_lem_crossing_tc (α := α) a) := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap (aux_lem_crossing_tc (α := α) a)
    (⨆ s : Set.Iic t, MeasurableSpace.comap
      (LifetimePath.coordinate (α := α) (s : ℝ≥0)) inferInstance) ≤ _
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun s => ?_
  rw [MeasurableSpace.comap_comp]
  have hfun : LifetimePath.coordinate (α := α) (s : ℝ≥0) ∘ aux_lem_crossing_tc a =
      LifetimePath.coordinate (a * s) := by
    funext w; exact aux_lem_crossing_coordinate_tc ha s w
  rw [hfun]
  have hle : a * (s : ℝ≥0) ≤ a * t := mul_le_mul_of_nonneg_left s.2 (zero_le)
  exact (LifetimePath.measurable_coordinate_canonicalFiltration (alpha := α) (a * s)).comap_le.trans
    ((LifetimePath.canonicalFiltration (alpha := α)).mono hle)

theorem aux_lem_crossing_measurable_tc {a : ℝ≥0} (ha : 0 < a) :
    Measurable (aux_lem_crossing_tc (α := α) a) := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap (aux_lem_crossing_tc (α := α) a)
    (MeasurableSpace.comap LifetimePath.lifetime inferInstance ⊔
      ⨆ t : ℝ≥0, MeasurableSpace.comap (LifetimePath.coordinate (α := α) t) inferInstance) ≤ _
  rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup]
  refine sup_le ?_ (iSup_le fun t => ?_)
  · rw [MeasurableSpace.comap_comp]
    exact (LifetimePath.measurable_lifetime.div_const _).comap_le
  · rw [MeasurableSpace.comap_comp]
    have hfun : LifetimePath.coordinate (α := α) t ∘ aux_lem_crossing_tc a =
        LifetimePath.coordinate (a * t) := by
      funext w; exact aux_lem_crossing_coordinate_tc ha t w
    rw [hfun]
    exact (LifetimePath.measurable_coordinate (a * t)).comap_le

/-- The time change as a measurable equivalence. -/
def aux_lem_crossing_tcEquiv {a : ℝ≥0} (ha : 0 < a) : LifetimePath α ≃ᵐ LifetimePath α where
  toFun := aux_lem_crossing_tc a
  invFun := aux_lem_crossing_tc a⁻¹
  left_inv := aux_lem_crossing_tc_inv ha
  right_inv := aux_lem_crossing_tc_inv' ha
  measurable_toFun := aux_lem_crossing_measurable_tc ha
  measurable_invFun := aux_lem_crossing_measurable_tc (inv_pos.mpr ha)

omit [MeasurableSpace α] in
theorem aux_lem_crossing_shift_tc {α : Type*} [TopologicalSpace α] [_ms : MeasurableSpace α]
    {a : ℝ≥0} (ha : 0 < a) (S : ℝ≥0) (w : LifetimePath α) :
    LifetimePath.shift S (aux_lem_crossing_tc a w) =
      aux_lem_crossing_tc a (LifetimePath.shift (a * S) w) := by
  apply LifetimePath.ext_coordinate
  · simp only [LifetimePath.lifetime_shift, aux_lem_crossing_tc_lifetime]
    have ha0 : (a : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha.ne'
    rw [ENNReal.sub_div (fun _ _ => ha0), ENNReal.coe_mul, mul_comm (a : ℝ≥0∞),
      ENNReal.mul_div_cancel_right ha0 ENNReal.coe_ne_top]
  · intro t
    rw [LifetimePath.coordinate_shift, aux_lem_crossing_coordinate_tc ha,
      aux_lem_crossing_coordinate_tc ha, LifetimePath.coordinate_shift, mul_add]

end TimeChange

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

section TimeChangeMarkov

variable {d : ℕ}

theorem aux_lem_crossing_position_tc {a : ℝ≥0} (ha : 0 < a) (t : ℝ≥0) (w : Path d) :
    position t (aux_lem_crossing_tc a w) = position (a * t) w := by
  simp only [position, aux_lem_crossing_coordinate_tc ha]

/-- Stopping times transfer through the time change. -/
theorem aux_lem_crossing_isStoppingTime_tc {a : ℝ≥0} (ha : 0 < a) {T' : Path d → ℝ≥0∞}
    (hT' : IsStoppingTime LifetimePath.canonicalFiltration T') :
    IsStoppingTime LifetimePath.canonicalFiltration
      (fun v : Path d => (a : ℝ≥0∞) * T' (aux_lem_crossing_tc a v)) := by
  intro t
  have hset : {v : Path d | (a : ℝ≥0∞) * T' (aux_lem_crossing_tc a v) ≤ (t : ℝ≥0∞)} =
      aux_lem_crossing_tc a ⁻¹' {w | T' w ≤ ((t / a : ℝ≥0) : ℝ≥0∞)} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [ENNReal.coe_div ha.ne', ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast ha.ne'))
      (Or.inl ENNReal.coe_ne_top), mul_comm]
  change MeasurableSet[LifetimePath.canonicalFiltration t]
    {v : Path d | (a : ℝ≥0∞) * T' (aux_lem_crossing_tc a v) ≤ (t : ℝ≥0∞)}
  rw [hset]
  have hm := aux_lem_crossing_measurable_tc_filtration (α := Homogenization.Vec d) ha (t / a)
  rw [mul_div_cancel₀ t ha.ne'] at hm
  exact hm (hT' (t / a))

/-- **Strong Markov property is preserved by the time change.** -/
theorem aux_lem_crossing_strongMarkov_tc (law : Kernel (Homogenization.Vec d) (Path d))
    (hSM : StrongMarkov law) {a : ℝ≥0} (ha : 0 < a) :
    StrongMarkov (law.map (aux_lem_crossing_tc a)) := by
  set E := aux_lem_crossing_tcEquiv (α := Homogenization.Vec d) ha with hEdef
  have hmeas := aux_lem_crossing_measurable_tc (α := Homogenization.Vec d) ha
  have hmap : ∀ y, (law.map (aux_lem_crossing_tc a)) y = (law y).map E := fun y =>
    Kernel.map_apply law hmeas y
  have hE : ∀ v, E v = aux_lem_crossing_tc a v := fun v => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro y
    rw [hmap, E.map_apply, Set.preimage_univ]
    exact hSM.1 y
  · intro y
    rw [hmap, E.measurableEmbedding.ae_map_iff]
    filter_upwards [hSM.2.1 y] with v hv
    rw [hE, aux_lem_crossing_coordinate_tc ha, mul_zero]
    exact hv
  · intro x T' hT' B hB g hg
    set T : Path d → ℝ≥0∞ := fun v => (a : ℝ≥0∞) * T' (aux_lem_crossing_tc a v) with hTdef
    have hT : IsStoppingTime LifetimePath.canonicalFiltration T :=
      aux_lem_crossing_isStoppingTime_tc ha hT'
    have hBambient : MeasurableSet B := hT'.measurableSpace_le B hB
    have hTm : Measurable T := by simpa using! hT.measurable'
    have hEterminal : Measurable[⨆ t, LifetimePath.canonicalFiltration t,
        ⨆ t, LifetimePath.canonicalFiltration t] E := by
      apply Measurable.of_comap_le
      rw [MeasurableSpace.comap_iSup]
      refine iSup_le fun t => ?_
      exact (aux_lem_crossing_measurable_tc_filtration (α := Homogenization.Vec d) ha t).comap_le.trans (le_iSup _ _)
    have hB' : MeasurableSet[hT.measurableSpace] (E ⁻¹' B) := by
      refine ⟨hEterminal hB.1, fun t => ?_⟩
      have hset : E ⁻¹' B ∩ {v | T v ≤ (t : ℝ≥0∞)} =
          aux_lem_crossing_tc a ⁻¹' (B ∩ {w | T' w ≤ ((t / a : ℝ≥0) : ℝ≥0∞)}) := by
        ext v
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, hE, hTdef]
        rw [ENNReal.coe_div ha.ne', ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast ha.ne'))
          (Or.inl ENNReal.coe_ne_top), mul_comm]
      change MeasurableSet[LifetimePath.canonicalFiltration t]
        (E ⁻¹' B ∩ {v | T v ≤ (t : ℝ≥0∞)})
      rw [hset]
      have hm := aux_lem_crossing_measurable_tc_filtration (α := Homogenization.Vec d) ha (t / a)
      rw [mul_div_cancel₀ t ha.ne'] at hm
      exact hm (hB.2 (t / a))
    have hset : E ⁻¹' (B ∩ {w | T' w < w.lifetime}) = E ⁻¹' B ∩ {v | T v < v.lifetime} := by
      ext v
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, hE, hTdef,
        aux_lem_crossing_tc_lifetime]
      rw [ENNReal.lt_div_iff_mul_lt (Or.inl (by exact_mod_cast ha.ne'))
        (Or.inl ENNReal.coe_ne_top), mul_comm]
    have hsetm : MeasurableSet (E ⁻¹' B ∩ {v : Path d | T v < v.lifetime}) :=
      (E.measurable hBambient).inter (measurableSet_lt hTm LifetimePath.measurable_lifetime)
    -- pointwise identities on the set
    have hpt : ∀ v ∈ E ⁻¹' B ∩ {v : Path d | T v < v.lifetime},
        (T' (E v)).toNNReal * a = (T v).toNNReal ∧
        LifetimePath.shift (T' (E v)).toNNReal (E v) =
          E (LifetimePath.shift (T v).toNNReal v) := by
      intro v hv
      have h1 : (T v).toNNReal = a * (T' (E v)).toNNReal := by
        simp only [hTdef, hE, ENNReal.toNNReal_mul, ENNReal.toNNReal_coe]
      refine ⟨by rw [h1, mul_comm], ?_⟩
      rw [hE, hE, aux_lem_crossing_shift_tc ha, h1]
      rfl
    rw [hmap x, E.restrict_map, lintegral_map_equiv _ E, lintegral_map_equiv _ E, hset]
    calc ∫⁻ v in E ⁻¹' B ∩ {v | T v < v.lifetime},
          g (LifetimePath.shift (T' (E v)).toNNReal (E v)) ∂law x
        = ∫⁻ v in E ⁻¹' B ∩ {v | T v < v.lifetime},
            (g ∘ E) (LifetimePath.shift (T v).toNNReal v) ∂law x := by
          refine setLIntegral_congr_fun hsetm (fun v hv => ?_)
          rw [(hpt v hv).2]; rfl
      _ = ∫⁻ v in E ⁻¹' B ∩ {v | T v < v.lifetime},
            (∫⁻ u, (g ∘ E) u ∂law (position (T v).toNNReal v)) ∂law x :=
          hSM.2.2 x T hT (E ⁻¹' B) hB' (g ∘ E) (hg.comp E.measurable)
      _ = ∫⁻ v in E ⁻¹' B ∩ {v | T v < v.lifetime},
            (∫⁻ u, g u ∂(law.map (aux_lem_crossing_tc a))
              (position (T' (E v)).toNNReal (E v))) ∂law x := by
          refine setLIntegral_congr_fun hsetm (fun v hv => ?_)
          have h1 : (T' (aux_lem_crossing_tc a v)).toNNReal * a = (T v).toNNReal := (hpt v hv).1
          rw [hmap, lintegral_map_equiv _ E, hE, aux_lem_crossing_position_tc ha, mul_comm, h1]
          rfl

end TimeChangeMarkov

end SubdiffusiveProcess.Paper

namespace SubdiffusiveProcess.Paper

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9PathGeometry
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation (Lattice IsJStepPath)

section RawLaw

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The raw-clock cutoff-zero lifetime law: the carried law `L 0 omega` sped up by `ahom M 0`
(`X_t = Z_0(ahom M 0 · t)`). -/
def aux_lem_crossing_rawLaw (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (L : ℕ → BilateralField d →
      Kernel (SpatialCoordinates d) (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
    (omega : BilateralField d) : Kernel (Homogenization.Vec d) (Path d) :=
  (L 0 omega).map (aux_lem_crossing_tc (Real.toNNReal (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)))

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lem_crossing_rawLaw_strongMarkov {d : ℕ} [_ms : MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [_borel : BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (L : ℕ → BilateralField d →
      Kernel (SpatialCoordinates d) (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
    (omega : BilateralField d) (h : StrongMarkov (L 0 omega)) :
    StrongMarkov (aux_lem_crossing_rawLaw M L omega) :=
  aux_lem_crossing_strongMarkov_tc (L 0 omega) h
    (Real.toNNReal_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M 0))

theorem aux_lem_crossing_rawLaw_lifetime_top (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (L : ℕ → BilateralField d →
      Kernel (SpatialCoordinates d) (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
    (hL : ∀ (N : ℕ) (omega : BilateralField d) (x : SpatialCoordinates d),
      Measure.map MarkovProcess.LifetimePath.ofContinuousPath (KN N (omega, x)) = L N omega x)
    (omega : BilateralField d) (x : Homogenization.Vec d) :
    ∀ᵐ w ∂(aux_lem_crossing_rawLaw M L omega x), w.lifetime = ⊤ := by
  have ha : 0 < Real.toNNReal (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0) :=
    Real.toNNReal_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M 0)
  rw [aux_lem_crossing_rawLaw, Kernel.map_apply _ (aux_lem_crossing_measurable_tc ha),
    show (aux_lem_crossing_tc (Real.toNNReal (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)) :
      Path d → Path d) = aux_lem_crossing_tcEquiv ha from rfl,
    (aux_lem_crossing_tcEquiv ha).measurableEmbedding.ae_map_iff]
  filter_upwards [aux_lem_crossing_L_lifetime_top KN L hL 0 omega x] with w hw
  change w.lifetime / _ = ⊤
  rw [hw, ENNReal.top_div_of_ne_top ENNReal.coe_ne_top]

/-- **Event comparison with the raw-clock law.** -/
theorem aux_lem_crossing_rawLaw_event (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (L : ℕ → BilateralField d →
      Kernel (SpatialCoordinates d) (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
    (hL : ∀ (N : ℕ) (omega : BilateralField d) (x : SpatialCoordinates d),
      Measure.map MarkovProcess.LifetimePath.ofContinuousPath (KN N (omega, x)) = L N omega x)
    (omega : BilateralField d) (x : SpatialCoordinates d) (u R : ℝ) (_hu : 0 ≤ u) :
    (KN 0 (omega, x))
        {path : DiffusionPath d |
          ∃ s : ℝ≥0, (s : ℝ) ≤ SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 * u ∧ R ≤ dist (path s) x} ≤
      aux_lem_crossing_rawLaw M L omega x (aux_lem_crossing_lifeEvent u R x) := by
  set a := Real.toNNReal (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0) with hadef
  have ha : 0 < a := Real.toNNReal_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M 0)
  have haR : (a : ℝ) = SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 :=
    Real.coe_toNNReal _ (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M 0).le
  refine (aux_lem_crossing_exit_KN_le_L KN L hL 0 omega x _ R).trans (le_of_eq ?_)
  rw [aux_lem_crossing_rawLaw, Kernel.map_apply _ (aux_lem_crossing_measurable_tc ha),
    show (aux_lem_crossing_tc a : Path d → Path d) = aux_lem_crossing_tcEquiv ha from rfl,
    (aux_lem_crossing_tcEquiv ha).map_apply]
  congr 1
  ext w
  simp only [aux_lem_crossing_lifeEvent, Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · rintro ⟨s, hs, y, hy, hRy⟩
    refine ⟨s / a, ?_, y, ?_, hRy⟩
    · rw [NNReal.coe_div, div_le_iff₀ (by exact_mod_cast ha), mul_comm, haR]; exact hs
    · show LifetimePath.coordinate (s / a) (aux_lem_crossing_tc a w) = _
      rw [aux_lem_crossing_coordinate_tc ha, mul_div_cancel₀ s ha.ne']; exact hy
  · rintro ⟨s, hs, y, hy, hRy⟩
    refine ⟨a * s, ?_, y, ?_, hRy⟩
    · rw [NNReal.coe_mul, haR]
      exact mul_le_mul_of_nonneg_left hs (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M 0).le
    · have : LifetimePath.coordinate s (aux_lem_crossing_tc a w) = _ := hy
      rw [aux_lem_crossing_coordinate_tc ha] at this; exact this

end RawLaw

end SubdiffusiveProcess.Paper
namespace SubdiffusiveProcess.Paper

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9PathGeometry
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation (Lattice IsJStepPath)

section EnvResidual2

attribute [local instance] Classical.propDecidable

/-- **The refined environment residual**: the law is fixed to the raw-clock cutoff-zero law
`aux_lem_crossing_rawLaw M L omega`; what remains is the environment content — the good
fine-lattice sites with their two-sided mean-exit bounds and their percolation density, off an
exceptional event of the displayed probability. -/
def aux_lem_crossing_envResidual2 (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] : Prop :=
  ∃ (cgood delta0 : ℝ), 0 < cgood ∧ 0 < delta0 ∧ delta0 ≤ cgood ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
      ∃ (κ Aκ c₁ cB CB : ℝ), 0 < κ ∧ κ ≤ Aκ ∧ 0 < c₁ ∧ 0 < cB ∧ 0 < CB ∧
        ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
          (_hH : InfraredCharacterization M H)
          (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
          (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
          (_hKN : ∀ N, IsMarkovKernel (KN N))
          (_hin : in_crossing M H PN KN)
          (L : ℕ → BilateralField d →
            Kernel (SpatialCoordinates d)
              (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
          (_hL : ∀ (N : ℕ) (omega : BilateralField d) (x : SpatialCoordinates d),
            Measure.map MarkovProcess.LifetimePath.ofContinuousPath (KN N (omega, x)) =
              L N omega x)
          (_hLlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            ∀ (N : ℕ),
              SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusionData
                (cutoffCoefficient M H omega N)
                (cutoffSpeedDensity M H omega N)
                (L N omega))
          (_hLstrong : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            ∀ (N : ℕ),
              SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.StrongMarkov (L N omega))
          (Region : Set (SpatialCoordinates d)), Bornology.IsBounded Region →
          ∀ (n : ℕ) (R : ℝ), CB * (3 : ℝ) ^ n ≤ R →
            ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
              (chaosSampleLaw M).toMeasure Bad ≤
                ENNReal.ofReal (CB * (1 + Metric.diam Region / (3 : ℝ) ^ n) ^ d *
                  Real.exp (-(cB * (cgood / (M.delta ^ 2 * |Real.log M.delta| ^ 2)) *
                    R / (3 : ℝ) ^ n))) ∧
              ∀ omega, omega ∉ Bad →
                ∃ (_e : ℕ ≃ Lattice d) (Good : Set (Lattice d)),
                  (∀ k ∈ Good,
                    (∀ y ∈ middleQuarter (aux_lem_crossing_G ((3 : ℝ) ^ n) k),
                      ENNReal.ofReal (κ * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
                          (SubdiffusiveProcess.CoarseGrainingVocab.ahom M) ((3 : ℝ) ^ n)) ≤
                        meanExit (aux_lem_crossing_rawLaw M L omega)
                          (cubeSet (aux_lem_crossing_G ((3 : ℝ) ^ n) k)) y) ∧
                    (∀ y ∈ cubeSet (aux_lem_crossing_G ((3 : ℝ) ^ n) k),
                      meanExit (aux_lem_crossing_rawLaw M L omega)
                          (cubeSet (aux_lem_crossing_G ((3 : ℝ) ^ n) k)) y ≤
                        ENNReal.ofReal (Aκ * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
                          (SubdiffusiveProcess.CoarseGrainingVocab.ahom M) ((3 : ℝ) ^ n)))) ∧
                  ∀ x ∈ Region,
                    ∀ (N : ℕ) (q : ℕ → Lattice d), IsJStepPath 1 q N →
                      Set.InjOn q (Set.Icc 0 N) →
                      x ∈ cubeSet (aux_lem_crossing_W ((3 : ℝ) ^ n) (q 0)) →
                      (∃ y ∈ cubeSet (aux_lem_crossing_W ((3 : ℝ) ^ n) (q N)), R ≤ dist y x) →
                      c₁ * R / (3 : ℝ) ^ n ≤
                        (((Finset.range (N + 1)).filter (fun i => q i ∈ Good)).card : ℝ)

theorem aux_lem_crossing_envResidual_of_envResidual2 {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (h2 : aux_lem_crossing_envResidual2 d) : aux_lem_crossing_envResidual d := by
  obtain ⟨cgood, delta0, hcg, hd0, hd0le, hM⟩ := h2
  refine ⟨cgood, delta0, hcg, hd0, hd0le, ?_⟩
  intro M hMdelta
  obtain ⟨κ, Aκ, c₁, cB, CB, hκ, hκA, hc₁, hcB, hCB, hdata⟩ := hM M hMdelta
  refine ⟨κ, Aκ, c₁, cB, CB, hκ, hκA, hc₁, hcB, hCB, ?_⟩
  intro H hH PN KN hKN hin L hL hLlocal hLstrong Region hRegion n R hR
  obtain ⟨Bad, hBadm, hBadμ, hBad⟩ :=
    hdata H hH PN KN hKN hin L hL hLlocal hLstrong Region hRegion n R hR
  set μ := (chaosSampleLaw M).toMeasure with hμ
  set G : Set (BilateralField d) := {omega | ∀ N, StrongMarkov (L N omega)} with hG
  have hGc : μ Gᶜ = 0 := by
    have := hLstrong
    rw [ae_iff] at this
    convert this using 2 ; rfl
  set Null := toMeasurable μ Gᶜ with hNull
  have hNullm : MeasurableSet Null := measurableSet_toMeasurable μ Gᶜ
  have hNullμ : μ Null = 0 := by rw [hNull, measure_toMeasurable]; exact hGc
  refine ⟨Bad ∪ Null, hBadm.union hNullm, ?_, ?_⟩
  · calc μ (Bad ∪ Null) ≤ μ Bad + μ Null := measure_union_le _ _
      _ = μ Bad := by rw [hNullμ, add_zero]
      _ ≤ _ := hBadμ
  · intro omega homega
    have h1 : omega ∉ Bad := fun h => homega (Or.inl h)
    have h2 : omega ∈ G := by
      by_contra hcon
      exact homega (Or.inr (subset_toMeasurable μ Gᶜ hcon))
    obtain ⟨e, Good, htors, hgood⟩ := hBad omega h1
    refine ⟨aux_lem_crossing_rawLaw M L omega, e, Good,
      aux_lem_crossing_rawLaw_strongMarkov M L omega (h2 0), htors, ?_⟩
    intro x hx
    refine ⟨aux_lem_crossing_rawLaw_lifetime_top M KN L hL omega x, hgood x hx, ?_⟩
    intro u hu
    exact aux_lem_crossing_rawLaw_event M KN L hL omega x u R hu.le

end EnvResidual2

end SubdiffusiveProcess.Paper

namespace SubdiffusiveProcess.Paper

section LDDTimeChange

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

variable {d : ℕ}

theorem aux_lem_crossing_exitTime_tc {a : ℝ≥0} (ha : 0 < a) (U : Set (Homogenization.Vec d))
    (w : Path d) :
    LifetimePath.exitTime U (aux_lem_crossing_tc a w) = LifetimePath.exitTime U w / a := by
  have ha0 : (a : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha.ne'
  have hat : (a : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  apply le_antisymm
  · -- exitTime (tc w) * a ≤ exitTime w
    rw [ENNReal.le_div_iff_mul_le (Or.inl ha0) (Or.inl hat)]
    apply le_sInf
    rintro s ⟨t, rfl, ht⟩
    have hmem : LifetimePath.coordinate (t / a) (aux_lem_crossing_tc a w) ∉
        Cemetery.alive '' U := by
      rw [aux_lem_crossing_coordinate_tc ha, mul_div_cancel₀ t ha.ne']; exact ht
    have := LifetimePath.exitTime_le_of_coordinate_notMem U _ (t / a) hmem
    calc LifetimePath.exitTime U (aux_lem_crossing_tc a w) * a ≤ ((t / a : ℝ≥0) : ℝ≥0∞) * a :=
          mul_le_mul_of_nonneg_right this zero_le
      _ = t := by
          rw [← ENNReal.coe_mul, div_mul_cancel₀ t ha.ne']
  · apply le_sInf
    rintro s ⟨t, rfl, ht⟩
    rw [ENNReal.div_le_iff_le_mul (Or.inl ha0) (Or.inl hat)]
    have hmem : LifetimePath.coordinate (a * t) w ∉ Cemetery.alive '' U := by
      rw [← aux_lem_crossing_coordinate_tc ha]; exact ht
    have := LifetimePath.exitTime_le_of_coordinate_notMem U w (a * t) hmem
    rw [ENNReal.coe_mul, mul_comm] at this
    exact this

/-- **The killed resolvent under the time change.** -/
theorem aux_lem_crossing_killedResolvent_tc (law : Kernel (Homogenization.Vec d) (Path d))
    {a : ℝ≥0} (ha : 0 < a) (U : Set (Homogenization.Vec d)) (s : ℝ) (hs : 0 < s)
    (f : Homogenization.Vec d → ℝ) (x : Homogenization.Vec d) :
    killedResolvent (law.map (aux_lem_crossing_tc a)) U s f x =
      killedResolvent law U ((a : ℝ) * s) f x := by
  set E := aux_lem_crossing_tcEquiv (α := Homogenization.Vec d) ha with hEdef
  have hmeas := aux_lem_crossing_measurable_tc (α := Homogenization.Vec d) ha
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha
  set inner : ℝ → ℝ := fun t => ∫ w in {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime U w},
    f (position (Real.toNNReal t) w) ∂law x with hinner
  have hinner' : ∀ t : ℝ, 0 < t →
      (∫ w in {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime U w},
        f (position (Real.toNNReal t) w) ∂(law.map (aux_lem_crossing_tc a)) x) =
        inner ((a : ℝ) * t) := by
    intro t ht
    rw [Kernel.map_apply _ hmeas,
      show (aux_lem_crossing_tc a : Path d → Path d) = E from rfl, E.restrict_map,
      integral_map_equiv]
    have hset : E ⁻¹' {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime U w} =
        {w : Path d | ENNReal.ofReal ((a : ℝ) * t) < LifetimePath.exitTime U w} := by
      ext v
      simp only [Set.mem_preimage, Set.mem_ofPred_eq]
      change ENNReal.ofReal t < LifetimePath.exitTime U (aux_lem_crossing_tc a v) ↔ _
      rw [aux_lem_crossing_exitTime_tc ha, ENNReal.lt_div_iff_mul_lt
        (Or.inl (by exact_mod_cast ha.ne')) (Or.inl ENNReal.coe_ne_top),
        ENNReal.ofReal_mul (NNReal.coe_nonneg a), ENNReal.ofReal_coe_nnreal, mul_comm]
    rw [hset]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    change f (position (Real.toNNReal t) (aux_lem_crossing_tc a v)) =
      f (position (Real.toNNReal ((a : ℝ) * t)) v)
    rw [aux_lem_crossing_position_tc ha]
    congr 2
    apply NNReal.eq
    rw [NNReal.coe_mul, Real.coe_toNNReal _ ht.le, Real.coe_toNNReal _ (by positivity)]
  unfold killedResolvent
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => by
    rw [hinner' t ht])]
  have hchg := integral_comp_mul_left_Ioi
    (fun t' : ℝ => Real.exp (-t' / ((a : ℝ) * s)) * inner t') 0 hapos
  have hfun : (fun t : ℝ => Real.exp (-t / s) * inner ((a : ℝ) * t)) =
      (fun t : ℝ => (fun t' : ℝ => Real.exp (-t' / ((a : ℝ) * s)) * inner t') ((a : ℝ) * t)) := by
    funext t
    simp only
    congr 2
    field_simp
  rw [hfun, hchg, mul_zero, smul_eq_mul, ← mul_assoc, mul_inv]
  ring

end LDDTimeChange


section LDDTransfer

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open Homogenization

variable {d : ℕ}

theorem aux_lem_crossing_withDensity_smul {ρ : Vec d → ℝ} {β : ℝ} (hβ : 0 < β) :
    (volume.withDensity fun x => ENNReal.ofReal (β * ρ x)) =
      ENNReal.ofReal β • volume.withDensity fun x => ENNReal.ofReal (ρ x) := by
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  exact ENNReal.ofReal_mul hβ.le

theorem aux_lem_crossing_weightedMeasure_smul {ρ : Vec d → ℝ} {β : ℝ} (hβ : 0 < β) :
    weightedMeasure (fun x => β * ρ x) = ENNReal.ofReal β • weightedMeasure ρ :=
  aux_lem_crossing_withDensity_smul hβ

theorem aux_lem_crossing_coefficientOn_smul {K : Set (Vec d)} {c : Vec d → ℝ}
    (h : CoefficientOn K c) {k : ℝ} (hk : 0 < k) : CoefficientOn K (fun x => k * c x) := by
  obtain ⟨hmeas, lo, hi, hlo, hae⟩ := h
  refine ⟨hmeas.const_mul k, k * lo, k * hi, mul_pos hk hlo, ?_⟩
  filter_upwards [hae] with x hx
  exact ⟨mul_le_mul_of_nonneg_left hx.1 hk.le, mul_le_mul_of_nonneg_left hx.2 hk.le⟩

theorem aux_lem_crossing_vecDot_smul_left (r : ℝ) (v w : Vec d) :
    vecDot (r • v) w = r * vecDot v w := by
  unfold vecDot
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The massive weak form under the time change and a constant multiple of both
coefficients. -/
theorem aux_lem_crossing_weak_scale {c ρ : Vec d → ℝ} {W : Set (Vec d)} {u : H1Function W}
    {f : Vec d → ℝ} {a s β : ℝ} (ha : 0 < a) (hs : 0 < s) (hβ : 0 < β)
    (h : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsMassiveWeakSolutionOn c ρ (a * s)⁻¹ W u
      (fun x => (a * s)⁻¹ * f x)) :
    SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsMassiveWeakSolutionOn
      (fun x => a * β * c x) (fun x => β * ρ x) s⁻¹ W u (fun x => s⁻¹ * f x) := by
  intro φ
  have hφ := h φ
  have e1 : (∫ x in W, β * ρ x * u.toFun x * φ.toH1Function.toFun x) =
      β * ∫ x in W, ρ x * u.toFun x * φ.toH1Function.toFun x := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  have e2 : (∫ x in W, vecDot ((a * β * c x) • u.grad x) (φ.toH1Function.grad x)) =
      (a * β) * ∫ x in W, vecDot (c x • u.grad x) (φ.toH1Function.grad x) := by
    rw [← integral_const_mul]; congr 1; funext x
    rw [show (a * β * c x) • u.grad x = (a * β) • (c x • u.grad x) by rw [smul_smul],
      aux_lem_crossing_vecDot_smul_left]
  have e3 : (∫ x in W, β * ρ x * (s⁻¹ * f x) * φ.toH1Function.toFun x) =
      (β * s⁻¹) * ∫ x in W, ρ x * f x * φ.toH1Function.toFun x := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  have e4 : (∫ x in W, ρ x * ((a * s)⁻¹ * f x) * φ.toH1Function.toFun x) =
      (a * s)⁻¹ * ∫ x in W, ρ x * f x * φ.toH1Function.toFun x := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  rw [e1, e2, e3]
  rw [e4] at hφ
  set I1 := ∫ x in W, ρ x * u.toFun x * φ.toH1Function.toFun x
  set I2 := ∫ x in W, vecDot (c x • u.grad x) (φ.toH1Function.grad x)
  set I3 := ∫ x in W, ρ x * f x * φ.toH1Function.toFun x
  have hI2 : I2 = (a * s)⁻¹ * I3 - (a * s)⁻¹ * I1 := by linarith
  rw [hI2]
  field_simp
  ring

/-- **`LocalDiffusionData` under the time change `tc a` and a constant multiple `β`**:
`(c, ρ, law) ↦ (a β c, β ρ, law ∘ tc a)`. -/
theorem aux_lem_crossing_localDiffusionData_tc (law : Kernel (Vec d) (Path d)) {c ρ : Vec d → ℝ}
    (h : LocalDiffusionData c ρ law) {a : ℝ≥0} (ha : 0 < a) {β : ℝ} (hβ : 0 < β) :
    LocalDiffusionData (fun x => (a : ℝ) * β * c x) (fun x => β * ρ x)
      (law.map (aux_lem_crossing_tc a)) := by
  obtain ⟨⟨hSM, hcoef, hres⟩, hkill⟩ := h
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha
  set E := aux_lem_crossing_tcEquiv (α := Vec d) ha with hEdef
  have hmeas := aux_lem_crossing_measurable_tc (α := Vec d) ha
  have hβ0 : ENNReal.ofReal β ≠ 0 := (ENNReal.ofReal_pos.mpr hβ).ne'
  refine ⟨⟨aux_lem_crossing_strongMarkov_tc law hSM ha, ?_, ?_⟩, ?_⟩
  · intro K hK
    obtain ⟨h1, h2⟩ := hcoef K hK
    exact ⟨aux_lem_crossing_coefficientOn_smul h1 (mul_pos hapos hβ),
      aux_lem_crossing_coefficientOn_smul h2 hβ⟩
  · intro U hU hUb s hs f hf
    rw [aux_lem_crossing_weightedMeasure_smul hβ, Measure.restrict_smul] at hf
    have hf' : MemLp f 2 ((weightedMeasure ρ).restrict U) := by
      have := hf.smul_measure (c := (ENNReal.ofReal β)⁻¹)
        (ENNReal.inv_ne_top.mpr hβ0)
      rwa [smul_smul, ENNReal.inv_mul_cancel hβ0 ENNReal.ofReal_ne_top, one_smul] at this
    obtain ⟨u, hu_ae, hu_weak⟩ := hres U hU hUb ((a : ℝ) * s) (by positivity) f hf'
    refine ⟨u, ?_, aux_lem_crossing_weak_scale hapos hs hβ hu_weak⟩
    rw [aux_lem_crossing_weightedMeasure_smul hβ, Measure.restrict_smul,
      Measure.ae_ennreal_smul_measure_eq hβ0]
    filter_upwards [hu_ae] with x hx
    rw [hx, aux_lem_crossing_killedResolvent_tc law ha U s hs f x]
  · intro U hU hUb
    obtain ⟨p, ⟨hp1, hp2, hp3⟩, hpc⟩ := hkill U hU hUb
    refine ⟨fun t x y => β⁻¹ * p ((a : ℝ) * t) x y, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro t ht
      exact (hp1 ((a : ℝ) * t) (by positivity)).const_mul _
    · intro t ht x hx y hy
      exact mul_nonneg (inv_nonneg.mpr hβ.le) (hp2 _ (by positivity) x hx y hy)
    · intro t ht x hx B hB
      have hat : 0 < (a : ℝ) * t := by positivity
      rw [Kernel.map_apply _ hmeas,
        show (aux_lem_crossing_tc a : Path d → Path d) = E from rfl, E.map_apply]
      have hset : E ⁻¹' {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime U w ∧
            LifetimePath.coordinate (Real.toNNReal t) w ∈ Cemetery.alive '' B} =
          {w : Path d | ENNReal.ofReal ((a : ℝ) * t) < LifetimePath.exitTime U w ∧
            LifetimePath.coordinate (Real.toNNReal ((a : ℝ) * t)) w ∈ Cemetery.alive '' B} := by
        ext v
        simp only [Set.mem_preimage, Set.mem_ofPred_eq]
        change ENNReal.ofReal t < LifetimePath.exitTime U (aux_lem_crossing_tc a v) ∧
            LifetimePath.coordinate (Real.toNNReal t) (aux_lem_crossing_tc a v) ∈ _ ↔ _
        rw [aux_lem_crossing_exitTime_tc ha, ENNReal.lt_div_iff_mul_lt
          (Or.inl (by exact_mod_cast ha.ne')) (Or.inl ENNReal.coe_ne_top),
          ENNReal.ofReal_mul (NNReal.coe_nonneg a), ENNReal.ofReal_coe_nnreal, mul_comm,
          aux_lem_crossing_coordinate_tc ha]
        have : a * Real.toNNReal t = Real.toNNReal ((a : ℝ) * t) := by
          apply NNReal.eq
          rw [NNReal.coe_mul, Real.coe_toNNReal _ ht.le, Real.coe_toNNReal _ hat.le]
        rw [this]
      rw [hset, hp3 ((a : ℝ) * t) hat x hx B hB, aux_lem_crossing_withDensity_smul hβ,
        Measure.restrict_smul, lintegral_smul_measure]
      have hpt : ∀ y, ENNReal.ofReal (β⁻¹ * p ((a : ℝ) * t) x y) =
          ENNReal.ofReal β⁻¹ * ENNReal.ofReal (p ((a : ℝ) * t) x y) := fun y =>
        ENNReal.ofReal_mul (inv_nonneg.mpr hβ.le)
      simp_rw [hpt]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, smul_eq_mul, ← mul_assoc,
        ← ENNReal.ofReal_mul hβ.le, mul_inv_cancel₀ hβ.ne', ENNReal.ofReal_one, one_mul]
    · have hmaps : Set.MapsTo (fun z : ℝ × Vec d × Vec d => ((a : ℝ) * z.1, z.2.1, z.2.2))
          (Set.Ioi 0 ×ˢ U ×ˢ U) (Set.Ioi 0 ×ˢ U ×ˢ U) := by
        rintro ⟨t, x, y⟩ ⟨ht, hx, hy⟩
        exact ⟨mul_pos hapos ht, hx, hy⟩
      have hcont := hpc.comp (Continuous.continuousOn (by fun_prop)) hmaps
      exact continuousOn_const.mul hcont

end LDDTransfer


section SpaceShift

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open Homogenization

variable {d : ℕ}

/-- Spatial translation of a lifetime path by `v`. -/
def aux_lem_crossing_sp (v : Vec d) (w : Path d) : Path d where
  lifetime := w.lifetime
  livePath := fun t => w.livePath t + v
  continuous_livePath := w.continuous_livePath.add continuous_const

theorem aux_lem_crossing_coordinate_sp (v : Vec d) (t : ℝ≥0) (w : Path d) :
    LifetimePath.coordinate t (aux_lem_crossing_sp v w) =
      Sum.map (fun y => y + v) id (LifetimePath.coordinate t w) := by
  by_cases h : (t : ℝ≥0∞) < w.lifetime
  · rw [LifetimePath.coordinate_of_lt (aux_lem_crossing_sp v w) t h,
      LifetimePath.coordinate_of_lt w t h]; rfl
  · rw [LifetimePath.coordinate_of_le (aux_lem_crossing_sp v w) t (not_lt.mp h),
      LifetimePath.coordinate_of_le w t (not_lt.mp h)]; rfl

theorem aux_lem_crossing_sp_neg (v : Vec d) (w : Path d) :
    aux_lem_crossing_sp (-v) (aux_lem_crossing_sp v w) = w := by
  apply LifetimePath.ext_coordinate
  · rfl
  intro t
  rw [aux_lem_crossing_coordinate_sp, aux_lem_crossing_coordinate_sp]
  rcases LifetimePath.coordinate t w with y | u
  · simp
  · rfl

theorem aux_lem_crossing_measurable_sp_filtration (v : Vec d) (t : ℝ≥0) :
    Measurable[LifetimePath.canonicalFiltration (alpha := Vec d) t,
      LifetimePath.canonicalFiltration (alpha := Vec d) t] (aux_lem_crossing_sp (d := d) v) := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap (aux_lem_crossing_sp (d := d) v)
    (⨆ s : Set.Iic t, MeasurableSpace.comap
      (LifetimePath.coordinate (α := Vec d) (s : ℝ≥0)) inferInstance) ≤ _
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun s => ?_
  rw [MeasurableSpace.comap_comp]
  have hfun : LifetimePath.coordinate (α := Vec d) (s : ℝ≥0) ∘ aux_lem_crossing_sp v =
      Sum.map (fun y => y + v) id ∘ LifetimePath.coordinate (s : ℝ≥0) := by
    funext w; exact aux_lem_crossing_coordinate_sp v s w
  rw [hfun]
  have hm : Measurable[LifetimePath.canonicalFiltration (alpha := Vec d) t]
      (Sum.map (fun y : Vec d => y + v) id ∘ LifetimePath.coordinate (α := Vec d) (s : ℝ≥0)) :=
    ((measurable_add_const v).sumMap measurable_id).comp
      ((LifetimePath.measurable_coordinate_canonicalFiltration (alpha := Vec d) (s : ℝ≥0)).mono
        ((LifetimePath.canonicalFiltration (alpha := Vec d)).mono s.2) le_rfl)
  exact hm.comap_le

theorem aux_lem_crossing_measurable_sp (v : Vec d) : Measurable (aux_lem_crossing_sp (d := d) v) := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap (aux_lem_crossing_sp (d := d) v)
    (MeasurableSpace.comap LifetimePath.lifetime inferInstance ⊔
      ⨆ t : ℝ≥0, MeasurableSpace.comap (LifetimePath.coordinate (α := Vec d) t) inferInstance) ≤ _
  rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup]
  refine sup_le ?_ (iSup_le fun t => ?_)
  · rw [MeasurableSpace.comap_comp]
    exact LifetimePath.measurable_lifetime.comap_le
  · rw [MeasurableSpace.comap_comp]
    have hfun : LifetimePath.coordinate (α := Vec d) t ∘ aux_lem_crossing_sp v =
        Sum.map (fun y => y + v) id ∘ LifetimePath.coordinate t := by
      funext w; exact aux_lem_crossing_coordinate_sp v t w
    rw [hfun]
    exact (((measurable_add_const v).sumMap measurable_id).comp
      (LifetimePath.measurable_coordinate t)).comap_le

/-- Spatial translation as a measurable equivalence. -/
def aux_lem_crossing_spEquiv (v : Vec d) : Path d ≃ᵐ Path d where
  toFun := aux_lem_crossing_sp v
  invFun := aux_lem_crossing_sp (-v)
  left_inv := aux_lem_crossing_sp_neg v
  right_inv := fun w => by
    have := aux_lem_crossing_sp_neg (-v) w
    rwa [neg_neg] at this
  measurable_toFun := aux_lem_crossing_measurable_sp v
  measurable_invFun := aux_lem_crossing_measurable_sp (-v)

theorem aux_lem_crossing_shift_sp (v : Vec d) (S : ℝ≥0) (w : Path d) :
    LifetimePath.shift S (aux_lem_crossing_sp v w) =
      aux_lem_crossing_sp v (LifetimePath.shift S w) := by
  apply LifetimePath.ext_coordinate
  · rfl
  intro t
  simp only [LifetimePath.coordinate_shift, aux_lem_crossing_coordinate_sp]

theorem aux_lem_crossing_position_sp_of_lt (v : Vec d) {t : ℝ≥0} {w : Path d}
    (h : (t : ℝ≥0∞) < w.lifetime) :
    position t (aux_lem_crossing_sp v w) = position t w + v := by
  simp only [position, aux_lem_crossing_coordinate_sp, LifetimePath.coordinate_of_lt _ _ h]
  rfl

/-- The translated law: `y ↦ (law (y + v)).map (sp (-v))`. -/
def aux_lem_crossing_trLaw (law : Kernel (Vec d) (Path d)) (v : Vec d) :
    Kernel (Vec d) (Path d) :=
  (law.comap (fun y => y + v) (measurable_add_const v)).map (aux_lem_crossing_sp (-v))

theorem aux_lem_crossing_trLaw_apply (law : Kernel (Vec d) (Path d)) (v y : Vec d) :
    aux_lem_crossing_trLaw law v y = (law (y + v)).map (aux_lem_crossing_spEquiv (-v)) := by
  rw [aux_lem_crossing_trLaw, Kernel.map_apply _ (aux_lem_crossing_measurable_sp (-v)),
    Kernel.comap_apply]
  rfl

/-- **Strong Markov is preserved by spatial translation.** -/
theorem aux_lem_crossing_strongMarkov_trLaw (law : Kernel (Vec d) (Path d))
    (hSM : StrongMarkov law) (v : Vec d) : StrongMarkov (aux_lem_crossing_trLaw law v) := by
  set E := aux_lem_crossing_spEquiv (d := d) (-v) with hEdef
  have hE : ∀ w, E w = aux_lem_crossing_sp (-v) w := fun w => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro y
    rw [aux_lem_crossing_trLaw_apply, E.map_apply, Set.preimage_univ]
    exact hSM.1 (y + v)
  · intro y
    rw [aux_lem_crossing_trLaw_apply, ← hEdef, E.measurableEmbedding.ae_map_iff]
    filter_upwards [hSM.2.1 (y + v)] with w hw
    rw [hE, aux_lem_crossing_coordinate_sp, hw]
    simp
  · intro x T' hT' B hB g hg
    set T : Path d → ℝ≥0∞ := fun u => T' (E u) with hTdef
    have hT : IsStoppingTime LifetimePath.canonicalFiltration T := by
      intro t
      exact (aux_lem_crossing_measurable_sp_filtration (-v) t) (hT' t)
    have hBambient : MeasurableSet B := hT'.measurableSpace_le B hB
    have hTm : Measurable T := by simpa using! hT.measurable'
    have hEterminal : Measurable[⨆ t, LifetimePath.canonicalFiltration t,
        ⨆ t, LifetimePath.canonicalFiltration t] E := by
      apply Measurable.of_comap_le
      rw [MeasurableSpace.comap_iSup]
      refine iSup_le fun t => ?_
      exact (aux_lem_crossing_measurable_sp_filtration (-v) t).comap_le.trans (le_iSup _ _)
    have hB' : MeasurableSet[hT.measurableSpace] (E ⁻¹' B) := by
      refine ⟨hEterminal hB.1, fun t => ?_⟩
      exact (aux_lem_crossing_measurable_sp_filtration (-v) t) (hB.2 t)
    have hset : E ⁻¹' (B ∩ {w | T' w < w.lifetime}) = E ⁻¹' B ∩ {u | T u < u.lifetime} := by
      ext u; rfl
    have hsetm : MeasurableSet (E ⁻¹' B ∩ {u : Path d | T u < u.lifetime}) :=
      (E.measurable hBambient).inter (measurableSet_lt hTm LifetimePath.measurable_lifetime)
    rw [aux_lem_crossing_trLaw_apply, ← hEdef, E.restrict_map, lintegral_map_equiv _ E,
      lintegral_map_equiv _ E, hset]
    calc ∫⁻ u in E ⁻¹' B ∩ {u | T u < u.lifetime},
          g (LifetimePath.shift (T' (E u)).toNNReal (E u)) ∂law (x + v)
        = ∫⁻ u in E ⁻¹' B ∩ {u | T u < u.lifetime},
            (g ∘ E) (LifetimePath.shift (T u).toNNReal u) ∂law (x + v) := by
          refine setLIntegral_congr_fun hsetm (fun u _ => ?_)
          simp only [Function.comp_apply, hE, hTdef, aux_lem_crossing_shift_sp]
      _ = ∫⁻ u in E ⁻¹' B ∩ {u | T u < u.lifetime},
            (∫⁻ w, (g ∘ E) w ∂law (position (T u).toNNReal u)) ∂law (x + v) :=
          hSM.2.2 (x + v) T hT (E ⁻¹' B) hB' (g ∘ E) (hg.comp E.measurable)
      _ = ∫⁻ u in E ⁻¹' B ∩ {u | T u < u.lifetime},
            (∫⁻ w, g w ∂aux_lem_crossing_trLaw law v
              (position (T' (E u)).toNNReal (E u))) ∂law (x + v) := by
          refine setLIntegral_congr_fun hsetm (fun u hu => ?_)
          have hlt : ((T u).toNNReal : ℝ≥0∞) < u.lifetime := by
            have h1 : T u < u.lifetime := hu.2
            have hfin : T u ≠ ⊤ := ne_top_of_lt h1
            rw [ENNReal.coe_toNNReal hfin]; exact h1
          have key : position (T' (aux_lem_crossing_sp (-v) u)).toNNReal
              (aux_lem_crossing_sp (-v) u) + v = position (T u).toNNReal u := by
            have h2 := aux_lem_crossing_position_sp_of_lt (-v) hlt
            simp only [hTdef, hE] at h2 ⊢
            rw [h2, neg_add_cancel_right]
          rw [aux_lem_crossing_trLaw_apply, ← hEdef, lintegral_map_equiv _ E, hE, key]
          rfl

end SpaceShift


section LDDTranslate

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open Homogenization

variable {d : ℕ}

/-- Translation carries the weighted measure of `ρ (· + v)` to that of `ρ`. -/
theorem aux_lem_crossing_mp_weighted_add {ρ : Vec d → ℝ} (hρ : Measurable ρ) (v : Vec d) :
    MeasurePreserving (fun x : Vec d => x + v) (weightedMeasure (fun x => ρ (x + v)))
      (weightedMeasure ρ) := by
  refine ⟨measurable_add_const v, ?_⟩
  ext S hS
  rw [Measure.map_apply (measurable_add_const v) hS]
  unfold weightedMeasure
  rw [withDensity_apply _ ((measurable_add_const v) hS), withDensity_apply _ hS]
  have hmp : MeasurePreserving (fun x : Vec d => x + v) volume volume :=
    measurePreserving_add_right volume v
  have := hmp.setLIntegral_comp_preimage hS
    (ENNReal.measurable_ofReal.comp hρ)
  simpa using this

theorem aux_lem_crossing_isOpen_translateSet {U : Set (Vec d)} (hU : IsOpen U) (v : Vec d) :
    IsOpen (translateSet v U) := by
  rw [← image_addRight_eq_translateSet]
  exact (Homeomorph.addRight v).isOpenMap U hU

theorem aux_lem_crossing_isBounded_translateSet {U : Set (Vec d)} (hU : Bornology.IsBounded U)
    (v : Vec d) : Bornology.IsBounded (translateSet v U) := by
  rw [← image_addRight_eq_translateSet]
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff).mp hU
  refine (Metric.isBounded_iff).mpr ⟨C, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [dist_add_right]; exact hC hx hy

theorem aux_lem_crossing_coordinate_sp_mem (v : Vec d) (t : ℝ≥0) (w : Path d) (U : Set (Vec d)) :
    LifetimePath.coordinate t (aux_lem_crossing_sp (-v) w) ∈ Cemetery.alive '' U ↔
      LifetimePath.coordinate t w ∈ Cemetery.alive '' translateSet v U := by
  rw [aux_lem_crossing_coordinate_sp]
  rcases LifetimePath.coordinate t w with y | u
  · constructor
    · rintro ⟨z, hz, hzeq⟩
      have : z = y + -v := Sum.inl.inj hzeq
      refine ⟨y, ?_, rfl⟩
      rw [mem_translateSet_iff_sub_mem, sub_eq_add_neg, ← this]; exact hz
    · rintro ⟨z, hz, hzeq⟩
      have : z = y := Sum.inl.inj hzeq
      refine ⟨y + -v, ?_, rfl⟩
      rw [← this, ← sub_eq_add_neg, ← mem_translateSet_iff_sub_mem]; exact hz
  · constructor
    · rintro ⟨z, _, hzeq⟩; exact absurd hzeq Sum.inl_ne_inr
    · rintro ⟨z, _, hzeq⟩; exact absurd hzeq Sum.inl_ne_inr

theorem aux_lem_crossing_exitTime_sp_neg (v : Vec d) (U : Set (Vec d)) (w : Path d) :
    LifetimePath.exitTime U (aux_lem_crossing_sp (-v) w) =
      LifetimePath.exitTime (translateSet v U) w := by
  unfold LifetimePath.exitTime
  congr 1
  ext s
  simp only [Set.mem_ofPred_eq, aux_lem_crossing_coordinate_sp_mem]

theorem aux_lem_crossing_killedResolvent_trLaw (law : Kernel (Vec d) (Path d)) (v : Vec d)
    (U : Set (Vec d)) (hU : IsOpen U) (s : ℝ) (f : Vec d → ℝ) (x : Vec d) :
    killedResolvent (aux_lem_crossing_trLaw law v) U s f x =
      killedResolvent law (translateSet v U) s (fun y => f (y - v)) (x + v) := by
  set E := aux_lem_crossing_spEquiv (d := d) (-v) with hEdef
  unfold killedResolvent
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  congr 1
  rw [aux_lem_crossing_trLaw_apply, ← hEdef, E.restrict_map, integral_map_equiv]
  have hset : E ⁻¹' {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime U w} =
      {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime (translateSet v U) w} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    change ENNReal.ofReal t < LifetimePath.exitTime U (aux_lem_crossing_sp (-v) w) ↔ _
    rw [aux_lem_crossing_exitTime_sp_neg]
  rw [hset]
  have hmexit : Measurable (LifetimePath.exitTime (translateSet v U)) := by
    simpa using! (LifetimePath.isStoppingTime_exitTime _ (aux_lem_crossing_isOpen_translateSet hU v)).measurable'
  have hmeas : MeasurableSet {w : Path d |
      ENNReal.ofReal t < LifetimePath.exitTime (translateSet v U) w} :=
    measurableSet_lt measurable_const hmexit
  refine setIntegral_congr_fun hmeas (fun w hw => ?_)
  have hlt : ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞) < w.lifetime := by
    have h1 : ENNReal.ofReal t < LifetimePath.exitTime (translateSet v U) w := hw
    exact lt_of_lt_of_le h1 (LifetimePath.exitTime_le_lifetime _ w)
  show f (position (Real.toNNReal t) (aux_lem_crossing_sp (-v) w)) = f (position _ w - v)
  rw [aux_lem_crossing_position_sp_of_lt _ hlt, sub_eq_add_neg]

/-- **`LocalDiffusionData` under spatial translation.** -/
theorem aux_lem_crossing_localDiffusionData_trLaw (law : Kernel (Vec d) (Path d))
    {c ρ : Vec d → ℝ} (h : LocalDiffusionData c ρ law) (hρ : Measurable ρ) (v : Vec d) :
    LocalDiffusionData (fun x => c (x + v)) (fun x => ρ (x + v))
      (aux_lem_crossing_trLaw law v) := by
  obtain ⟨⟨hSM, hcoef, hres⟩, hkill⟩ := h
  have hmpw := aux_lem_crossing_mp_weighted_add hρ v
  refine ⟨⟨aux_lem_crossing_strongMarkov_trLaw law hSM v, ?_, ?_⟩, ?_⟩
  · intro K hK
    have hK' : IsCompact (translateSet v K) := by
      rw [← image_addRight_eq_translateSet]; exact hK.image (continuous_id.add continuous_const)
    obtain ⟨h1, h2⟩ := hcoef _ hK'
    have hmpK := measurePreserving_addRight_restrict_translateSet v K
    have htr : ∀ {a : Vec d → ℝ}, CoefficientOn (translateSet v K) a →
        CoefficientOn K (fun x => a (x + v)) := by
      intro a ha
      obtain ⟨hmeas, lo, hi, hlo, hae⟩ := ha
      exact ⟨hmeas.comp_measurePreserving hmpK, lo, hi, hlo,
        hmpK.quasiMeasurePreserving.ae hae⟩
    exact ⟨htr h1, htr h2⟩
  · intro U hU hUb s hs f hf
    set U' := translateSet v U with hU'
    have hU'o := aux_lem_crossing_isOpen_translateSet hU v
    have hU'b := aux_lem_crossing_isBounded_translateSet hUb v
    have hpre : (fun x : Vec d => x + v) ⁻¹' U' = U := preimage_addRight_translateSet_eq v U
    have hmpU : MeasurePreserving (fun x : Vec d => x + v)
        ((weightedMeasure (fun x => ρ (x + v))).restrict U) ((weightedMeasure ρ).restrict U') := by
      have := hmpw.restrict_preimage (hU'o.measurableSet)
      rwa [hpre] at this
    have hmpU' : MeasurePreserving (fun y : Vec d => y - v)
        ((weightedMeasure ρ).restrict U') ((weightedMeasure (fun x => ρ (x + v))).restrict U) := by
      have hinv := hmpU.symm (Homeomorph.addRight v).toMeasurableEquiv
      convert hinv using 1
      funext y
      simp [Homeomorph.addRight, sub_eq_add_neg]
    have hf' : MemLp (fun y => f (y - v)) 2 ((weightedMeasure ρ).restrict U') :=
      hf.comp_measurePreserving hmpU'
    obtain ⟨u', hu'ae, hu'weak⟩ := hres U' hU'o hU'b s hs _ hf'
    refine ⟨H10Function.untranslate v u', ?_, ?_⟩
    · have := hmpU.quasiMeasurePreserving.ae hu'ae
      filter_upwards [this] with x hx
      rw [aux_lem_crossing_killedResolvent_trLaw law v U hU s f x]
      exact hx
    · intro φ
      have hφ := hu'weak (φ.translate v)
      have hmpV := measurePreserving_addRight_restrict_translateSet v U
      have hemb : MeasurableEmbedding (fun x : Vec d => x + v) :=
        (Homeomorph.addRight v).toMeasurableEquiv.measurableEmbedding
      rw [← hmpV.integral_comp hemb, ← hmpV.integral_comp hemb,
        ← hmpV.integral_comp hemb] at hφ
      convert hφ using 3 <;> simp [H10Function.untranslate_toH1Function,
        H10Function.translate_toH1Function, H1Function.untranslate]
  · intro U hU hUb
    set U' := translateSet v U with hU'
    have hU'o := aux_lem_crossing_isOpen_translateSet hU v
    have hU'b := aux_lem_crossing_isBounded_translateSet hUb v
    obtain ⟨p, ⟨hp1, hp2, hp3⟩, hpc⟩ := hkill U' hU'o hU'b
    refine ⟨fun t x y => p t (x + v) (y + v), ⟨?_, ?_, ?_⟩, ?_⟩
    · intro t ht
      exact (hp1 t ht).comp ((measurable_fst.add_const v).prodMk (measurable_snd.add_const v))
    · intro t ht x hx y hy
      exact hp2 t ht _ (by rw [hU', mem_translateSet_iff_sub_mem]; simpa using hx) _
        (by rw [hU', mem_translateSet_iff_sub_mem]; simpa using hy)
    · intro t ht x hx B hB
      set E := aux_lem_crossing_spEquiv (d := d) (-v) with hEdef
      have hxv : x + v ∈ U' := by rw [hU', mem_translateSet_iff_sub_mem]; simpa using hx
      rw [aux_lem_crossing_trLaw_apply, ← hEdef, E.map_apply]
      have hset : E ⁻¹' {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime U w ∧
            LifetimePath.coordinate (Real.toNNReal t) w ∈ Cemetery.alive '' B} =
          {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime U' w ∧
            LifetimePath.coordinate (Real.toNNReal t) w ∈ Cemetery.alive '' translateSet v B} := by
        ext w
        simp only [Set.mem_preimage, Set.mem_ofPred_eq]
        change ENNReal.ofReal t < LifetimePath.exitTime U (aux_lem_crossing_sp (-v) w) ∧
          LifetimePath.coordinate _ (aux_lem_crossing_sp (-v) w) ∈ _ ↔ _
        rw [aux_lem_crossing_exitTime_sp_neg, aux_lem_crossing_coordinate_sp_mem]
      have hBv : MeasurableSet (translateSet v B) := by
        rw [← preimage_subRight_eq_translateSet]; exact (measurable_sub_const v) hB
      rw [hset, hp3 t ht (x + v) hxv (translateSet v B) hBv]
      have hBU : translateSet v B ∩ U' = (fun y : Vec d => y + v) '' (B ∩ U) := by
        rw [hU', ← translateSet_inter, image_addRight_eq_translateSet]
      rw [hBU]
      have := hmpw.setLIntegral_comp_emb
        (Homeomorph.addRight v).toMeasurableEquiv.measurableEmbedding
        (fun y => ENNReal.ofReal (p t (x + v) y)) (B ∩ U)
      exact this.symm
    · have hmaps : Set.MapsTo (fun z : ℝ × Vec d × Vec d => (z.1, z.2.1 + v, z.2.2 + v))
          (Set.Ioi 0 ×ˢ U ×ˢ U) (Set.Ioi 0 ×ˢ U' ×ˢ U') := by
        rintro ⟨t, x, y⟩ ⟨ht, hx, hy⟩
        refine ⟨ht, ?_, ?_⟩
        · rw [hU', mem_translateSet_iff_sub_mem]; simpa using hx
        · rw [hU', mem_translateSet_iff_sub_mem]; simpa using hy
      exact hpc.comp (Continuous.continuousOn (by fun_prop)) hmaps

end LDDTranslate

end SubdiffusiveProcess.Paper

namespace SubdiffusiveProcess.Paper

open _root_.SubdiffusiveProcess.Model

section Lift

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The underlying continuous function of a potential field. -/
def aux_lem_crossing_forget (g : PotentialField d) : C(SpatialCoordinates d, ℝ) := g.1.1

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lem_crossing_continuous_forget {d : ℕ} [_ms : MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [_borel : BorelSpace C(SpatialCoordinates d, ℝ)]
    : Continuous (aux_lem_crossing_forget (d := d)) :=
  continuous_fst.comp continuous_subtype_val

theorem aux_lem_crossing_measurable_forget : Measurable (aux_lem_crossing_forget (d := d)) :=
  aux_lem_crossing_continuous_forget.measurable

/-- The zero potential field. -/
def aux_lem_crossing_zeroField : PotentialField d := by
  refine ⟨(0, 0), ?_, ?_⟩
  · intro x
    simpa using! (hasFDerivAt_const (x := x) (c := (0 : ℝ)))
  · intro K _hK
    exact ⟨0, by simp [LipschitzOnWith]⟩

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lem_crossing_forget_injective {d : ℕ} [_ms : MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [_borel : BorelSpace C(SpatialCoordinates d, ℝ)]
    :
    Function.Injective (aux_lem_crossing_forget (d := d)) := by
  intro g h hgh
  apply Subtype.ext
  apply Prod.ext hgh
  apply ContinuousMap.ext
  intro x
  have h1 := (g.2.1 x).fderiv
  have h2 := (h.2.1 x).fderiv
  have hfun : (g.1.1 : SpatialCoordinates d → ℝ) = h.1.1 := congrArg DFunLike.coe hgh
  rw [← h1, ← h2, hfun]

theorem aux_lem_crossing_measurableEmbedding_forget :
    MeasurableEmbedding (aux_lem_crossing_forget (d := d)) :=
  aux_lem_crossing_measurable_forget.measurableEmbedding aux_lem_crossing_forget_injective

theorem aux_lem_crossing_exists_unforget :
    ∃ g' : C(SpatialCoordinates d, ℝ) → PotentialField d, Measurable g' ∧
      g' ∘ aux_lem_crossing_forget = id :=
  aux_lem_crossing_measurableEmbedding_forget.exists_measurable_extend measurable_id
    (fun _ => ⟨aux_lem_crossing_zeroField⟩)

/-- A measurable left inverse of `forget`. -/
def aux_lem_crossing_unforget : C(SpatialCoordinates d, ℝ) → PotentialField d :=
  Classical.choose (aux_lem_crossing_exists_unforget (d := d))

theorem aux_lem_crossing_measurable_unforget : Measurable (aux_lem_crossing_unforget (d := d)) :=
  (Classical.choose_spec (aux_lem_crossing_exists_unforget (d := d))).1

theorem aux_lem_crossing_unforget_forget (g : PotentialField d) :
    aux_lem_crossing_unforget (aux_lem_crossing_forget g) = g :=
  congrFun (Classical.choose_spec (aux_lem_crossing_exists_unforget (d := d))).2 g

/-- **The lift** of a bilateral field to a GMC potential sample (layers `k ≥ 0`). -/
def aux_lem_crossing_lift (omega : BilateralField d) : PotentialSample d :=
  fun k => aux_lem_crossing_unforget (omega (k : ℤ))

theorem aux_lem_crossing_measurable_lift : Measurable (aux_lem_crossing_lift (d := d)) :=
  measurable_pi_iff.mpr fun k =>
    aux_lem_crossing_measurable_unforget.comp (measurable_pi_apply (k : ℤ))

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lem_crossing_layerScaling_forget {d : ℕ} [_ms : MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [_borel : BorelSpace C(SpatialCoordinates d, ℝ)]
    (k : ℕ) (g : PotentialField d) :
    SubdiffusiveProcess.layerScaling d (k : ℤ) (aux_lem_crossing_forget g) =
      aux_lem_crossing_forget (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k g) := by
  apply ContinuousMap.ext
  intro x
  simp only [SubdiffusiveProcess.layerScaling, ContinuousMap.compRightContinuousMap_apply,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, aux_lem_crossing_forget]
  change g.1.1 _ = (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k g) x
  rw [_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale_apply, zpow_neg, zpow_natCast]

/-- **The lift is measure preserving** from the chaos sample law to the GMC sample law. -/
theorem aux_lem_crossing_measurePreserving_lift (M : GMCModel d) :
    MeasurePreserving (aux_lem_crossing_lift (d := d)) (SubdiffusiveProcess.chaosSampleLaw M).toMeasure
      M.P.toMeasure := by
  refine ⟨aux_lem_crossing_measurable_lift, ?_⟩
  set ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ) := SubdiffusiveProcess.chaosRootFieldLaw M
  have hlaw : (SubdiffusiveProcess.chaosSampleLaw M).toMeasure =
      Measure.infinitePi (fun j : ℤ =>
        (SubdiffusiveProcess.scaledLayerLaw d ν j : Measure C(SpatialCoordinates d, ℝ))) := rfl
  -- independence of the lifted layers
  have hind0 := iIndepFun_infinitePi
    (P := fun j : ℤ => (SubdiffusiveProcess.scaledLayerLaw d ν j : Measure C(SpatialCoordinates d, ℝ)))
    (X := fun _ : ℤ => aux_lem_crossing_unforget (d := d))
    (fun _ => aux_lem_crossing_measurable_unforget)
  have hind : ProbabilityTheory.iIndepFun
      (fun (k : ℕ) (omega : SubdiffusiveProcess.BilateralField d) =>
        aux_lem_crossing_unforget (omega (k : ℤ))) (SubdiffusiveProcess.chaosSampleLaw M).toMeasure := by
    rw [hlaw]
    exact hind0.precomp (g := fun k : ℕ => (k : ℤ)) (fun a b h => Int.ofNat.inj h)
  -- the marginals
  have hmarg : ∀ k : ℕ, Measure.map (fun omega : SubdiffusiveProcess.BilateralField d =>
      aux_lem_crossing_unforget (omega (k : ℤ))) (SubdiffusiveProcess.chaosSampleLaw M).toMeasure =
      (potentialMarginalLaw M.P k : Measure (PotentialField d)) := by
    intro k
    have h1 : (fun omega : SubdiffusiveProcess.BilateralField d =>
        aux_lem_crossing_unforget (omega (k : ℤ))) =
        aux_lem_crossing_unforget ∘ (fun omega : SubdiffusiveProcess.BilateralField d => omega (k : ℤ)) :=
      rfl
    rw [h1, ← Measure.map_map aux_lem_crossing_measurable_unforget
      (measurable_pi_apply (X := fun _ : ℤ => C(SpatialCoordinates d, ℝ)) (k : ℤ)), hlaw,
      Measure.infinitePi_map_eval]
    rw [M.shellPrefix.marginal_scaling k]
    change Measure.map aux_lem_crossing_unforget
      (Measure.map (SubdiffusiveProcess.layerScaling d (k : ℤ))
        (Measure.map aux_lem_crossing_forget (zeroPotentialLaw M.P).toMeasure)) =
      Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k) (zeroPotentialLaw M.P).toMeasure
    rw [Measure.map_map (SubdiffusiveProcess.layerScaling d (k : ℤ)).continuous.measurable
        aux_lem_crossing_measurable_forget,
      Measure.map_map aux_lem_crossing_measurable_unforget
        ((SubdiffusiveProcess.layerScaling d (k : ℤ)).continuous.measurable.comp
          aux_lem_crossing_measurable_forget)]
    congr 1
    funext g
    simp only [Function.comp_apply, aux_lem_crossing_layerScaling_forget,
      aux_lem_crossing_unforget_forget]
  have : IsProbabilityMeasure M.P.toMeasure := inferInstance
  have hP := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun k : ℕ => measurable_potentialCoordinate k)).mp M.shellPrefix.independent
  have hlift := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun k : ℕ => aux_lem_crossing_measurable_unforget.comp (measurable_pi_apply (k : ℤ)))).mp hind
  change Measure.map (fun (omega : SubdiffusiveProcess.BilateralField d) (k : ℕ) =>
      aux_lem_crossing_unforget (omega (k : ℤ)))
    (SubdiffusiveProcess.chaosSampleLaw M).toMeasure = M.P.toMeasure
  have hlift' : Measure.map (fun (omega : SubdiffusiveProcess.BilateralField d) (k : ℕ) =>
      aux_lem_crossing_unforget (omega (k : ℤ))) (SubdiffusiveProcess.chaosSampleLaw M).toMeasure =
      Measure.infinitePi fun (k : ℕ) => Measure.map (fun omega : SubdiffusiveProcess.BilateralField d =>
        aux_lem_crossing_unforget (omega (k : ℤ))) (SubdiffusiveProcess.chaosSampleLaw M).toMeasure :=
    hlift
  rw [hlift']
  conv_rhs => rw [show M.P.toMeasure =
    Measure.map (fun (omega : PotentialSample d) (k : ℕ) => omega k) M.P.toMeasure by
    rw [Measure.map_id']]
  rw [hP]
  congr 1
  funext k
  rw [hmarg k]
  rfl

/-- Almost surely every lifted layer recovers the bilateral layer. -/
theorem aux_lem_crossing_forget_lift_ae (M : GMCModel d) :
    ∀ᵐ omega ∂(SubdiffusiveProcess.chaosSampleLaw M).toMeasure, ∀ k : ℕ,
      aux_lem_crossing_forget (aux_lem_crossing_lift omega k) = omega (k : ℤ) := by
  rw [ae_all_iff]
  intro k
  set ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ) := SubdiffusiveProcess.chaosRootFieldLaw M
  have hrange : MeasurableSet (Set.range (aux_lem_crossing_forget (d := d))) :=
    aux_lem_crossing_measurableEmbedding_forget.measurableSet_range
  have hfull : ∀ᵐ omega ∂(SubdiffusiveProcess.chaosSampleLaw M).toMeasure,
      omega (k : ℤ) ∈ Set.range (aux_lem_crossing_forget (d := d)) := by
    have hmeas : MeasurableSet {omega : SubdiffusiveProcess.BilateralField d |
        omega (k : ℤ) ∈ Set.range (aux_lem_crossing_forget (d := d))} :=
      (measurable_pi_apply (k : ℤ)) hrange
    rw [ae_iff, ← Set.compl_ofPred]
    rw [prob_compl_eq_zero_iff hmeas]
    change (Measure.infinitePi (fun j : ℤ =>
        (SubdiffusiveProcess.scaledLayerLaw d ν j : Measure C(SpatialCoordinates d, ℝ))))
      ((fun omega : SubdiffusiveProcess.BilateralField d => omega (k : ℤ)) ⁻¹'
        Set.range aux_lem_crossing_forget) = 1
    rw [← Measure.map_apply (measurable_pi_apply (k : ℤ)) hrange, Measure.infinitePi_map_eval]
    change (Measure.map (SubdiffusiveProcess.layerScaling d (k : ℤ))
        (Measure.map aux_lem_crossing_forget (zeroPotentialLaw M.P).toMeasure)) _ = 1
    rw [Measure.map_map (SubdiffusiveProcess.layerScaling d (k : ℤ)).continuous.measurable
        aux_lem_crossing_measurable_forget,
      Measure.map_apply ((SubdiffusiveProcess.layerScaling d (k : ℤ)).continuous.measurable.comp
        aux_lem_crossing_measurable_forget) hrange]
    have : (SubdiffusiveProcess.layerScaling d (k : ℤ) ∘ aux_lem_crossing_forget) ⁻¹'
        Set.range aux_lem_crossing_forget = Set.univ := by
      ext g
      simp only [Set.mem_preimage, Function.comp_apply, Set.mem_range, Set.mem_univ, iff_true]
      exact ⟨_, (aux_lem_crossing_layerScaling_forget k g).symm⟩
    rw [this, measure_univ]
  filter_upwards [hfull] with omega homega
  obtain ⟨g, hg⟩ := homega
  simp only [aux_lem_crossing_lift, ← hg, aux_lem_crossing_unforget_forget]

end Lift


section AnchoredId

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem aux_lem_crossing_anchoredPartialSum_lift {omega : SubdiffusiveProcess.BilateralField d}
    (hrec : ∀ k : ℕ, aux_lem_crossing_forget (aux_lem_crossing_lift omega k) = omega (k : ℤ))
    (L : ℕ) (x : SpatialCoordinates d) :
    anchoredPartialSum (aux_lem_crossing_lift omega) L x =
      (omega 0 x - omega 0 0) + SubdiffusiveProcess.infraredPartialSum omega L x := by
  have hval : ∀ k : ℕ, ∀ y, (aux_lem_crossing_lift omega k) y = omega (k : ℤ) y := by
    intro k y
    change aux_lem_crossing_forget (aux_lem_crossing_lift omega k) y = _
    rw [hrec k]
  unfold anchoredPartialSum SubdiffusiveProcess.infraredPartialSum
  rw [Finset.sum_range_succ', ContinuousMap.coe_sum, Finset.sum_apply]
  simp only [hval, ContinuousMap.sub_apply, ContinuousMap.const_apply, Int.ofNat_eq_natCast,
    CharP.cast_eq_zero]
  ring

/-- **Anchored identification.**  On the lifted good sample, the anchored log-coefficient is
`ω 0 − ω 0 0 + H ω`. -/
theorem aux_lem_crossing_anchoredLog_lift {omega : SubdiffusiveProcess.BilateralField d}
    {H : SubdiffusiveProcess.BilateralField d → C(SpatialCoordinates d, ℝ)}
    (hrec : ∀ k : ℕ, aux_lem_crossing_forget (aux_lem_crossing_lift omega k) = omega (k : ℤ))
    (hH : Tendsto (SubdiffusiveProcess.infraredPartialSum omega) atTop (𝓝 (H omega)))
    (hgood : aux_lem_crossing_lift omega ∈ anchoredC11GoodSet d) (x : SpatialCoordinates d) :
    anchoredLog (⟨aux_lem_crossing_lift omega, hgood⟩ : AnchoredC11Sample d) x =
      omega 0 x - omega 0 0 + H omega x := by
  have hspec : IsAnchoredC11Limit (aux_lem_crossing_lift omega)
      (anchoredLog (⟨aux_lem_crossing_lift omega, hgood⟩ : AnchoredC11Sample d)) :=
    (Classical.choose_spec hgood.exists)
  have h1 : Tendsto (fun L => anchoredPartialSum (aux_lem_crossing_lift omega) L x) atTop
      (𝓝 (anchoredLog (⟨aux_lem_crossing_lift omega, hgood⟩ : AnchoredC11Sample d) x)) :=
    (hspec.value_tendsto {x} isCompact_singleton).tendsto_at (Set.mem_singleton x)
  have h2 : Tendsto (fun L => anchoredPartialSum (aux_lem_crossing_lift omega) L x) atTop
      (𝓝 (omega 0 x - omega 0 0 + H omega x)) := by
    simp_rw [aux_lem_crossing_anchoredPartialSum_lift hrec]
    exact tendsto_const_nhds.add ((continuous_eval_const x).tendsto _ |>.comp hH)
  exact tendsto_nhds_unique h1 h2

/-- **The cutoff-zero speed density is a constant multiple of the anchored coefficient.** -/
theorem aux_lem_crossing_cutoffSpeedDensity_zero (M : GMCModel d)
    {omega : SubdiffusiveProcess.BilateralField d}
    {H : SubdiffusiveProcess.BilateralField d → C(SpatialCoordinates d, ℝ)}
    (hrec : ∀ k : ℕ, aux_lem_crossing_forget (aux_lem_crossing_lift omega k) = omega (k : ℤ))
    (hH : Tendsto (SubdiffusiveProcess.infraredPartialSum omega) atTop (𝓝 (H omega)))
    (hgood : aux_lem_crossing_lift omega ∈ anchoredC11GoodSet d) (x : SpatialCoordinates d) :
    SubdiffusiveProcess.cutoffSpeedDensity M H omega 0 x =
      Real.exp (omega 0 0 - tauSq M.P) *
        aAnchored M (⟨aux_lem_crossing_lift omega, hgood⟩ : AnchoredC11Sample d) x := by
  rw [aAnchored, aux_lem_crossing_anchoredLog_lift hrec hH hgood, ← Real.exp_add]
  unfold SubdiffusiveProcess.cutoffSpeedDensity SubdiffusiveProcess.cutoffPotential
  congr 1
  simp only [zero_add, Finset.range_one, Finset.sum_singleton, Int.ofNat_eq_natCast, Nat.cast_zero,
    neg_zero, one_mul]
  ring

theorem aux_lem_crossing_lift_good_ae (M : GMCModel d) :
    ∀ᵐ omega ∂(SubdiffusiveProcess.chaosSampleLaw M).toMeasure,
      aux_lem_crossing_lift omega ∈ anchoredC11GoodSet d := by
  have hmp := aux_lem_crossing_measurePreserving_lift M
  have hfull : ∀ᵐ ω' ∂M.P.toMeasure, ω' ∈ anchoredC11GoodSet d :=
    (mem_ae_iff_prob_eq_one
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measurableSet_anchoredC11GoodSet d)).mpr
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measure_anchoredC11GoodSet_eq_one M)
  exact hmp.quasiMeasurePreserving.ae hfull

end AnchoredId

end SubdiffusiveProcess.Paper

namespace SubdiffusiveProcess.Paper

open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open Homogenization

section EnvTorsion

variable {d : ℕ}

theorem aux_lem_crossing_tc_one (w : Path d) : aux_lem_crossing_tc 1 w = w := by
  apply LifetimePath.ext_coordinate
  · simp [aux_lem_crossing_tc_lifetime]
  · intro t
    rw [aux_lem_crossing_coordinate_tc one_pos, one_mul]

theorem aux_lem_crossing_map_tc_one (law : Kernel (Vec d) (Path d)) :
    law.map (aux_lem_crossing_tc 1) = law := by
  ext y S hS
  rw [Kernel.map_apply _ (aux_lem_crossing_measurable_tc one_pos),
    Measure.map_apply (aux_lem_crossing_measurable_tc one_pos) hS]
  congr 1
  ext w
  simp [aux_lem_crossing_tc_one]

theorem aux_lem_crossing_meanExit_trLaw (law : Kernel (Vec d) (Path d)) (v : Vec d)
    (U : Set (Vec d)) (y : Vec d) :
    meanExit (aux_lem_crossing_trLaw law v) U y = meanExit law (translateSet v U) (y + v) := by
  unfold meanExit
  rw [aux_lem_crossing_trLaw_apply, lintegral_map_equiv]
  congr 1
  funext w
  exact aux_lem_crossing_exitTime_sp_neg v U w

theorem aux_lem_crossing_translateSet_centeredAxisCube (v : Vec d) (L : ℝ) :
    translateSet v (SubdiffusiveProcess.Section9.centeredAxisCube (0 : Vec d) L) =
      SubdiffusiveProcess.Section9.centeredAxisCube v L := by
  ext y
  rw [mem_translateSet_iff_sub_mem, aux_lem_crossing_mem_centeredAxisCube_iff,
    aux_lem_crossing_mem_centeredAxisCube_iff]
  simp

/-- Translating a good sample: the anchored log-coefficient is translated and re-anchored. -/
theorem aux_lem_crossing_anchoredLog_translate {ω' : PotentialSample d} (v : Vec d)
    (hg : ω' ∈ anchoredC11GoodSet d)
    (hgv : SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSequence v ω' ∈ anchoredC11GoodSet d)
    (x : Vec d) :
    anchoredLog (⟨_, hgv⟩ : AnchoredC11Sample d) x =
      anchoredLog (⟨ω', hg⟩ : AnchoredC11Sample d) (x + v) -
        anchoredLog (⟨ω', hg⟩ : AnchoredC11Sample d) v := by
  have hspec : IsAnchoredC11Limit ω' (anchoredLog (⟨ω', hg⟩ : AnchoredC11Sample d)) :=
    Classical.choose_spec hg.exists
  have hspecv : IsAnchoredC11Limit _ (anchoredLog (⟨_, hgv⟩ : AnchoredC11Sample d)) :=
    Classical.choose_spec hgv.exists
  have hpt : ∀ y, Tendsto (fun L => anchoredPartialSum ω' L y) atTop
      (𝓝 (anchoredLog (⟨ω', hg⟩ : AnchoredC11Sample d) y)) := fun y =>
    (hspec.value_tendsto {y} isCompact_singleton).tendsto_at (Set.mem_singleton y)
  have h1 := (hspecv.value_tendsto {x} isCompact_singleton).tendsto_at (Set.mem_singleton x)
  have hsum : ∀ L, anchoredPartialSum (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSequence v ω') L x =
      anchoredPartialSum ω' L (x + v) - anchoredPartialSum ω' L v := by
    intro L
    unfold anchoredPartialSum SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSequence
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [_root_.SubdiffusiveProcess.Model.PotentialField.translate_apply, zero_add]
    ring
  have h2 : Tendsto (fun L => anchoredPartialSum
      (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSequence v ω') L x) atTop
      (𝓝 (anchoredLog (⟨ω', hg⟩ : AnchoredC11Sample d) (x + v) -
        anchoredLog (⟨ω', hg⟩ : AnchoredC11Sample d) v)) := by
    simp_rw [hsum]; exact (hpt _).sub (hpt _)
  exact tendsto_nhds_unique h1 h2

end EnvTorsion

end SubdiffusiveProcess.Paper
namespace SubdiffusiveProcess.Paper

open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open Homogenization

section EnvTorsion2

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lem_crossing_continuous_anchoredLog {d : ℕ} [_ms : MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [_borel : BorelSpace C(SpatialCoordinates d, ℝ)]
    (s : AnchoredC11Sample d) :
    Continuous (fun x => anchoredLog s x) :=
  (_root_.SubdiffusiveProcess.Model.PotentialField.contDiff_one (anchoredLog s)).continuous

/-- **Torsion on a translated good cube.**  The GMC local torsion package for the translated
anchored sample, applied to the translated and time-changed carried law, gives the two
mean-exit bounds for the raw-clock cutoff-zero law on the translated cube. -/
theorem aux_lem_crossing_torsion_of_good (M : GMCModel d)
    (H : SubdiffusiveProcess.BilateralField d → C(SpatialCoordinates d, ℝ))
    (L : ℕ → SubdiffusiveProcess.BilateralField d →
      Kernel (SpatialCoordinates d) (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
    (omega : SubdiffusiveProcess.BilateralField d) (n : ℕ) (v : Vec d)
    (hrec : ∀ k : ℕ, aux_lem_crossing_forget (aux_lem_crossing_lift omega k) = omega (k : ℤ))
    (hHω : Tendsto (SubdiffusiveProcess.infraredPartialSum omega) atTop (𝓝 (H omega)))
    (hgood : aux_lem_crossing_lift omega ∈ anchoredC11GoodSet d)
    (hgoodv : SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSequence v (aux_lem_crossing_lift omega) ∈
      anchoredC11GoodSet d)
    (hLloc : LocalDiffusionData (SubdiffusiveProcess.cutoffCoefficient M H omega 0)
      (SubdiffusiveProcess.cutoffSpeedDensity M H omega 0) (L 0 omega))
    (p0 cc CC : ℝ) (Qfam Afam : Set (Cube d))
    (hGMC : ∀ law : Kernel (Vec d) (Path d),
      LocalDiffusionData (aAnchored M ⟨_, hgoodv⟩) (aAnchored M ⟨_, hgoodv⟩) law →
      LocalTorsionEstimates (aAnchored M ⟨_, hgoodv⟩) law
        (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale (SubdiffusiveProcess.CoarseGrainingVocab.ahom M))
        p0 cc CC ((0 : Vec d), (3 : ℝ) ^ n) Qfam Afam) :
    (∀ y ∈ middleQuarter ((v, (3 : ℝ) ^ n) : Cube d),
      ENNReal.ofReal (cc * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom M) ((3 : ℝ) ^ n)) ≤
        meanExit (aux_lem_crossing_rawLaw M L omega) (cubeSet ((v, (3 : ℝ) ^ n) : Cube d)) y) ∧
    (∀ y ∈ cubeSet ((v, (3 : ℝ) ^ n) : Cube d),
      meanExit (aux_lem_crossing_rawLaw M L omega) (cubeSet ((v, (3 : ℝ) ^ n) : Cube d)) y ≤
        ENNReal.ofReal (CC * SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom M) ((3 : ℝ) ^ n))) := by
  set a : Vec d → ℝ := aAnchored M ⟨aux_lem_crossing_lift omega, hgood⟩ with hadef
  set K : ℝ := Real.exp (omega 0 0 - tauSq M.P) with hKdef
  have hK : 0 < K := Real.exp_pos _
  have ha0 := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M 0
  set lam : ℝ≥0 := Real.toNNReal (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0) with hlam
  have hlam0 : 0 < lam := Real.toNNReal_pos.mpr ha0
  have hlamR : (lam : ℝ) = SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 := Real.coe_toNNReal _ ha0.le
  -- time change and normalization: `LocalDiffusionData a a rawLaw`
  have h1 := aux_lem_crossing_localDiffusionData_tc (L 0 omega) hLloc hlam0 (inv_pos.mpr hK)
  have hcfun : (fun x => (lam : ℝ) * K⁻¹ * SubdiffusiveProcess.cutoffCoefficient M H omega 0 x) = a := by
    funext x
    have hρx := aux_lem_crossing_cutoffSpeedDensity_zero M hrec hHω hgood x
    have hcx : SubdiffusiveProcess.cutoffCoefficient M H omega 0 x =
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)⁻¹ * SubdiffusiveProcess.cutoffSpeedDensity M H omega 0 x :=
      rfl
    rw [hcx, hρx, hlamR]
    field_simp
    rfl
  have hρfun : (fun x => K⁻¹ * SubdiffusiveProcess.cutoffSpeedDensity M H omega 0 x) = a := by
    funext x
    rw [aux_lem_crossing_cutoffSpeedDensity_zero M hrec hHω hgood x]
    field_simp
    rfl
  rw [hcfun, hρfun] at h1
  -- `h1 : LocalDiffusionData a a rawLaw`
  have ha_meas : Measurable a :=
    (Real.continuous_exp.comp (aux_lem_crossing_continuous_anchoredLog _)).measurable
  have h2 := aux_lem_crossing_localDiffusionData_trLaw _ h1 ha_meas v
  set g : Vec d → ℝ := fun x =>
    anchoredLog (⟨aux_lem_crossing_lift omega, hgood⟩ : AnchoredC11Sample d) x with hgdef
  have hβ : 0 < Real.exp (-g v) := Real.exp_pos _
  have h3 := aux_lem_crossing_localDiffusionData_tc _ h2 one_pos hβ
  rw [aux_lem_crossing_map_tc_one] at h3
  have hafun : (fun x => ((1 : ℝ≥0) : ℝ) * Real.exp (-g v) * a (x + v)) =
      aAnchored M ⟨_, hgoodv⟩ := by
    funext x
    rw [aAnchored, aux_lem_crossing_anchoredLog_translate v hgood hgoodv x, hadef, aAnchored,
      NNReal.coe_one, one_mul, ← Real.exp_add]
    congr 1; ring
  have hafun' : (fun x => Real.exp (-g v) * a (x + v)) = aAnchored M ⟨_, hgoodv⟩ := by
    rw [← hafun]; funext x; simp
  rw [hafun, hafun'] at h3
  have hT := hGMC _ h3
  have htrC : translateSet v (cubeSet (((0 : Vec d), (3 : ℝ) ^ n) : Cube d)) =
      cubeSet ((v, (3 : ℝ) ^ n) : Cube d) :=
    aux_lem_crossing_translateSet_centeredAxisCube v _
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · have hy' : y - v ∈ middleQuarter (((0 : Vec d), (3 : ℝ) ^ n) : Cube d) := by
      have : y ∈ translateSet v (middleQuarter (((0 : Vec d), (3 : ℝ) ^ n) : Cube d)) := by
        rw [middleQuarter, aux_lem_crossing_translateSet_centeredAxisCube]; exact hy
      rwa [mem_translateSet_iff_sub_mem] at this
    have := hT.exit_lower (y - v) hy'
    rw [aux_lem_crossing_meanExit_trLaw, htrC, sub_add_cancel] at this
    exact this
  · have hy' : y - v ∈ cubeSet (((0 : Vec d), (3 : ℝ) ^ n) : Cube d) := by
      have : y ∈ translateSet v (cubeSet (((0 : Vec d), (3 : ℝ) ^ n) : Cube d)) := by
        rw [htrC]; exact hy
      rwa [mem_translateSet_iff_sub_mem] at this
    have := hT.exit_upper (y - v) hy'
    rw [aux_lem_crossing_meanExit_trLaw, htrC, sub_add_cancel] at this
    exact this

end EnvTorsion2

end SubdiffusiveProcess.Paper
namespace SubdiffusiveProcess.Paper

open _root_.SubdiffusiveProcess.Model
open Homogenization

section LocalSigmaTranslate

variable {d : ℕ}

theorem aux_lem_crossing_entryTestR_translate (i j : Fin d) (φ : Vec d → ℝ) (v : Vec d)
    (g : PotentialField d) :
    entryTestR i j φ (_root_.SubdiffusiveProcess.Model.PotentialField.forgetPotential (_root_.SubdiffusiveProcess.Model.PotentialField.translate v g)) =
      entryTestR i j (fun y => φ (y - v)) (_root_.SubdiffusiveProcess.Model.PotentialField.forgetPotential g) := by
  unfold entryTestR
  have h := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure (Vec d)))
    (fun y => (_root_.SubdiffusiveProcess.Model.PotentialField.forgetPotential g) y i j * φ (y - v)) v
  simp only [add_sub_cancel_right] at h
  rw [← h]
  rfl

/-- **Translation moves the probe σ-algebra.** -/
theorem aux_lem_crossing_measurable_translate_localSigma (v : Vec d) (U : Set (Vec d)) :
    Measurable[_root_.SubdiffusiveProcess.Model.PotentialField.localSigma (translateSet v U), _root_.SubdiffusiveProcess.Model.PotentialField.localSigma U]
      (_root_.SubdiffusiveProcess.Model.PotentialField.translate (d := d) v) := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap (_root_.SubdiffusiveProcess.Model.PotentialField.translate (d := d) v)
    (MeasurableSpace.comap _root_.SubdiffusiveProcess.Model.PotentialField.forgetPotential (LocalSigmaR U)) ≤ _
  rw [MeasurableSpace.comap_comp]
  unfold _root_.SubdiffusiveProcess.Model.PotentialField.localSigma
  intro A hA
  obtain ⟨B, hB, rfl⟩ := hA
  -- `B` is `LocalSigmaR U`-measurable: show the preimage under the composite is measurable
  have hmeas : Measurable[MeasurableSpace.comap _root_.SubdiffusiveProcess.Model.PotentialField.forgetPotential
      (LocalSigmaR (translateSet v U)), LocalSigmaR U]
      (_root_.SubdiffusiveProcess.Model.PotentialField.forgetPotential ∘ _root_.SubdiffusiveProcess.Model.PotentialField.translate (d := d) v) := by
    refine Measurable.of_comap_le ?_
    change MeasurableSpace.comap _ (MeasurableSpace.generateFrom _) ≤ _
    rw [MeasurableSpace.comap_generateFrom]
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨s, ⟨i, j, φ, hφ, hsupp, t, ht, rfl⟩, rfl⟩
    have hφ' : IsProbeR (fun y => φ (y - v)) := by
      refine ⟨hφ.measurable.comp (measurable_sub_const v), ?_, ?_⟩
      · obtain ⟨C, hC⟩ := hφ.bounded; exact ⟨C, fun x => hC _⟩
      · exact hφ.hasCompactSupport.comp_homeomorph (Homeomorph.subRight v)
    have hsupp' : Function.support (fun y => φ (y - v)) ⊆ translateSet v U := by
      intro y hy
      rw [mem_translateSet_iff_sub_mem]
      exact hsupp hy
    refine ⟨entryTestR i j (fun y => φ (y - v)) ⁻¹' t, ?_, ?_⟩
    · exact MeasurableSpace.measurableSet_generateFrom ⟨i, j, _, hφ', hsupp', t, ht, rfl⟩
    · ext g
      simp only [Set.mem_preimage, Function.comp_apply]
      rw [aux_lem_crossing_entryTestR_translate]
  exact hmeas hB

end LocalSigmaTranslate

end SubdiffusiveProcess.Paper
namespace SubdiffusiveProcess.Paper

open _root_.SubdiffusiveProcess.Model
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab (translatePotentialSequence)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

section FineEvents

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem aux_lem_crossing_translate_translate (a b : Vec d) (g : PotentialField d) :
    _root_.SubdiffusiveProcess.Model.PotentialField.translate a (_root_.SubdiffusiveProcess.Model.PotentialField.translate b g) =
      _root_.SubdiffusiveProcess.Model.PotentialField.translate (a + b) g := by
  apply aux_lem_crossing_forget_injective
  apply ContinuousMap.ext
  intro x
  change (_root_.SubdiffusiveProcess.Model.PotentialField.translate a (_root_.SubdiffusiveProcess.Model.PotentialField.translate b g)) x =
    (_root_.SubdiffusiveProcess.Model.PotentialField.translate (a + b) g) x
  simp only [_root_.SubdiffusiveProcess.Model.PotentialField.translate_apply, add_assoc]

theorem aux_lem_crossing_T_comp (a b : Vec d) (ω : PotentialSample d) :
    translatePotentialSequence a (translatePotentialSequence b ω) =
      translatePotentialSequence (a + b) ω :=
  funext fun k => aux_lem_crossing_translate_translate a b (ω k)

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lem_crossing_ctr_add {d : ℕ} [_ms : MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [_borel : BorelSpace C(SpatialCoordinates d, ℝ)]
    (ℓ : ℝ) (k m : Lattice d) :
    aux_lem_crossing_ctr ℓ (k + m) = aux_lem_crossing_ctr ℓ k + aux_lem_crossing_ctr ℓ m := by
  funext i
  simp only [aux_lem_crossing_ctr_apply, Pi.add_apply, Int.cast_add]
  ring

/-- The fine-lattice event field: the GMC events at the origin, read in the environment
translated to the fine site. -/
def aux_lem_crossing_Efine (ℓ : ℝ) (E : ℕ → Lattice d → Set (PotentialSample d)) :
    ℕ → Lattice d → Set (PotentialSample d) :=
  fun j k => translatePotentialSequence (aux_lem_crossing_ctr ℓ k) ⁻¹' (E j 0)

theorem aux_lem_crossing_Efine_cov (ℓ : ℝ) (E : ℕ → Lattice d → Set (PotentialSample d))
    (j : ℕ) (k m : Lattice d) :
    aux_lem_crossing_Efine ℓ E j (k + m) =
      translatePotentialSequence (aux_lem_crossing_ctr ℓ m) ⁻¹' aux_lem_crossing_Efine ℓ E j k := by
  ext ω
  simp only [aux_lem_crossing_Efine, Set.mem_preimage, aux_lem_crossing_T_comp,
    aux_lem_crossing_ctr_add]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lem_crossing_T_shellLocalSigma {d : ℕ} [_ms : MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [_borel : BorelSpace C(SpatialCoordinates d, ℝ)]
    (v : Vec d) (k : ℕ) (B : Set (Vec d))
    {A : Set (PotentialSample d)} (hA : MeasurableSet[shellLocalSigma k B] A) :
    MeasurableSet[shellLocalSigma k (translateSet v B)] (translatePotentialSequence v ⁻¹' A) := by
  obtain ⟨A', hA', rfl⟩ := hA
  refine ⟨_root_.SubdiffusiveProcess.Model.PotentialField.translate v ⁻¹' A',
    aux_lem_crossing_measurable_translate_localSigma v B hA', ?_⟩
  ext ω
  rfl

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lem_crossing_T_aCutoffLocal {d : ℕ} [_ms : MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [_borel : BorelSpace C(SpatialCoordinates d, ℝ)]
    (v : Vec d) (L : ℕ) (B : Set (Vec d))
    {A : Set (PotentialSample d)}
    (hA : MeasurableSet[SubdiffusiveProcess.CoarseGrainingVocab.aCutoffPotentialLocalSigma L B] A) :
    MeasurableSet[SubdiffusiveProcess.CoarseGrainingVocab.aCutoffPotentialLocalSigma L (translateSet v B)]
      (translatePotentialSequence v ⁻¹' A) := by
  have hm : Measurable[SubdiffusiveProcess.CoarseGrainingVocab.aCutoffPotentialLocalSigma L (translateSet v B),
      SubdiffusiveProcess.CoarseGrainingVocab.aCutoffPotentialLocalSigma L B]
      (translatePotentialSequence (d := d) v) := by
    apply Measurable.of_comap_le
    unfold SubdiffusiveProcess.CoarseGrainingVocab.aCutoffPotentialLocalSigma
    rw [MeasurableSpace.comap_iSup]
    refine iSup_le fun q => ?_
    rw [MeasurableSpace.comap_comp]
    have hfun : (fun omega : PotentialSample d => omega q) ∘ translatePotentialSequence v =
        _root_.SubdiffusiveProcess.Model.PotentialField.translate v ∘ (fun omega : PotentialSample d => omega q) := rfl
    rw [hfun, ← MeasurableSpace.comap_comp]
    refine le_trans (MeasurableSpace.comap_mono
      (aux_lem_crossing_measurable_translate_localSigma v B).comap_le) ?_
    exact le_iSup (fun q : Fin (L + 1) =>
      (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma (translateSet v B)).comap
        (fun omega : PotentialSample d => omega q)) q
  exact hm hA

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lem_crossing_T_comap_block {d : ℕ} [_ms : MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [_borel : BorelSpace C(SpatialCoordinates d, ℝ)]
    (v : Vec d) (S : Set ℕ) {A : Set (PotentialSample d)}
    (hA : MeasurableSet[⨆ k ∈ S, MeasurableSpace.comap
      (fun omega : PotentialSample d => omega k) inferInstance] A) :
    MeasurableSet[⨆ k ∈ S, MeasurableSpace.comap
      (fun omega : PotentialSample d => omega k) inferInstance]
      (translatePotentialSequence v ⁻¹' A) := by
  have hm : Measurable[⨆ k ∈ S, MeasurableSpace.comap
      (fun omega : PotentialSample d => omega k) inferInstance,
      ⨆ k ∈ S, MeasurableSpace.comap
      (fun omega : PotentialSample d => omega k) inferInstance]
      (translatePotentialSequence (d := d) v) := by
    apply Measurable.of_comap_le
    rw [MeasurableSpace.comap_iSup]
    refine iSup_le fun k => ?_
    rw [MeasurableSpace.comap_iSup]
    refine iSup_le fun hk => ?_
    rw [MeasurableSpace.comap_comp]
    have hfun : (fun omega : PotentialSample d => omega k) ∘ translatePotentialSequence v =
        _root_.SubdiffusiveProcess.Model.PotentialField.translate v ∘ (fun omega : PotentialSample d => omega k) := rfl
    rw [hfun, ← MeasurableSpace.comap_comp]
    refine le_trans (MeasurableSpace.comap_mono
      (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate v).comap_le) ?_
    exact le_iSup₂ (f := fun k (_ : k ∈ S) => MeasurableSpace.comap
      (fun omega : PotentialSample d => omega k) inferInstance) k hk
  exact hm hA

end FineEvents

end SubdiffusiveProcess.Paper
namespace SubdiffusiveProcess.Paper

open _root_.SubdiffusiveProcess.Model
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab (translatePotentialSequence)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

section FineHyps

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lem_crossing_goodCubeCentre_zero {d : ℕ} [_ms : MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [_borel : BorelSpace C(SpatialCoordinates d, ℝ)]
    (n : ℕ) : goodCubeCentre (d := d) n 0 = 0 := by
  funext i; simp [goodCubeCentre]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- Separation of translated boxes on the fine lattice. -/
theorem aux_lem_crossing_box_separation {d : ℕ} [_ms : MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [_borel : BorelSpace C(SpatialCoordinates d, ℝ)]
    {n j : ℕ} {C : ℝ} {Cdep : ℕ}
    (hCdep : 16 * (C + Real.sqrt (d : ℝ)) ≤ (Cdep : ℝ)) {k k' : Lattice d}
    (hkk : Cdep * 3 ^ j < latticeDist k k') {x y : Vec d}
    (hx : x ∈ SubdiffusiveProcess.Section9.centeredAxisCube (aux_lem_crossing_ctr ((3 : ℝ) ^ n) k)
      (C * (3 : ℝ) ^ (n + j)))
    (hy : y ∈ SubdiffusiveProcess.Section9.centeredAxisCube (aux_lem_crossing_ctr ((3 : ℝ) ^ n) k')
      (C * (3 : ℝ) ^ (n + j))) :
    Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n + j) ≤ Homogenization.euclideanNorm (x - y) := by
  unfold latticeDist at hkk
  obtain ⟨i, -, hi⟩ := Finset.lt_sup_iff.mp hkk
  rw [aux_lem_crossing_mem_centeredAxisCube_iff] at hx hy
  have hxi := hx i
  have hyi := hy i
  rw [aux_lem_crossing_ctr_apply] at hxi hyi
  have h3n : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have h3j : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have hdiff : (Cdep : ℝ) * 3 ^ j ≤ |(k i : ℝ) - (k' i : ℝ)| := by
    have h1 : ((Cdep * 3 ^ j : ℕ) : ℝ) < ((k i - k' i).natAbs : ℝ) := by exact_mod_cast hi
    have h2 : ((k i - k' i).natAbs : ℝ) = |(k i : ℝ) - (k' i : ℝ)| := by
      rw [Nat.cast_natAbs]; push_cast; rfl
    push_cast at h1
    linarith
  have hctr : (3 : ℝ) ^ n / 16 * ((Cdep : ℝ) * 3 ^ j) ≤
      |(3 : ℝ) ^ n / 16 * (k i : ℝ) - (3 : ℝ) ^ n / 16 * (k' i : ℝ)| := by
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left hdiff (by positivity)
  have htri : |(3 : ℝ) ^ n / 16 * (k i : ℝ) - (3 : ℝ) ^ n / 16 * (k' i : ℝ)| ≤
      |x i - y i| + |x i - (3 : ℝ) ^ n / 16 * (k i : ℝ)| +
        |y i - (3 : ℝ) ^ n / 16 * (k' i : ℝ)| := by
    calc _ = |(x i - y i) - (x i - (3 : ℝ) ^ n / 16 * (k i : ℝ)) +
          (y i - (3 : ℝ) ^ n / 16 * (k' i : ℝ))| := by ring_nf
      _ ≤ |(x i - y i) - (x i - (3 : ℝ) ^ n / 16 * (k i : ℝ))| +
          |y i - (3 : ℝ) ^ n / 16 * (k' i : ℝ)| := abs_add_le _ _
      _ ≤ _ := by gcongr; exact abs_sub _ _
  have hpow : (3 : ℝ) ^ (n + j) = (3 : ℝ) ^ n * (3 : ℝ) ^ j := pow_add _ _ _
  have hsqrt : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hkey : Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n + j) ≤ |x i - y i| := by
    rw [hpow] at hxi hyi ⊢
    have : (3 : ℝ) ^ n / 16 * ((Cdep : ℝ) * 3 ^ j) ≥
        (C + Real.sqrt (d : ℝ)) * ((3 : ℝ) ^ n * (3 : ℝ) ^ j) := by
      have := mul_le_mul_of_nonneg_right hCdep (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ n / 16 * 3 ^ j)
      nlinarith
    nlinarith
  refine hkey.trans ?_
  have h1 : |x i - y i| ≤ dist x y := by
    rw [← Real.dist_eq]; exact dist_le_pi_dist x y i
  exact h1.trans (aux_lem_crossing_dist_le_euclid x y)

/-- **The percolation hypotheses for the fine-lattice event field.** -/
theorem aux_lem_crossing_Efine_hyps [NeZero d] (M : GMCModel d) (n : ℕ) {C : ℝ} (_hC : 0 ≤ C)
    {Cdep : ℕ} (hCdep : 16 * (C + Real.sqrt (d : ℝ)) ≤ (Cdep : ℝ))
    (E : ℕ → Lattice d → Set (PotentialSample d))
    (hE0 : MeasurableSet[SubdiffusiveProcess.CoarseGrainingVocab.restrictedCoefficientSigma
      (fun omega : PotentialSample d => aCutoff M n omega)
      (SubdiffusiveProcess.Section9.centeredAxisCube (goodCubeCentre n 0) (C * (3 : ℝ) ^ n))] (E 0 0))
    (hEj : ∀ j : ℕ, 1 ≤ j → MeasurableSet[shellLocalSigma (n + j)
      (SubdiffusiveProcess.Section9.centeredAxisCube (goodCubeCentre n 0) (C * (3 : ℝ) ^ (n + j)))] (E j 0)) :
    let F := aux_lem_crossing_Efine ((3 : ℝ) ^ n) E
    (∀ j k, M.P.toMeasure (F j k) = M.P.toMeasure (E j 0)) ∧
    IndependentEventScales M.P.toMeasure F ∧
    MultiscaleFiniteRangeIndependentEvents M.P.toMeasure (fun j => Cdep * 3 ^ j) F ∧
    TranslationInvariantEventLaw M.P.toMeasure F := by
  intro F
  rw [aux_lem_crossing_goodCubeCentre_zero] at hE0 hEj
  have hT : ∀ v : Vec d, MeasurePreserving (translatePotentialSequence (d := d) v)
      M.P.toMeasure M.P.toMeasure := fun v =>
    ⟨SubdiffusiveProcess.CoarseGrainingVocab.measurable_translatePotentialSequence v,
      SubdiffusiveProcess.CoarseGrainingVocab.potentialSequenceLaw_stationary M v⟩
  -- ambient measurability of the origin events
  have hE0amb : MeasurableSet (E 0 0) := by
    have h := restrictedCoefficientSigma_aCutoff_le_prefix M n _ _ hE0
    refine (iSup₂_le fun k _ => ?_ : (⨆ k ∈ Set.Iic n, MeasurableSpace.comap
      (fun omega : PotentialSample d => omega k) inferInstance) ≤ _) _ h
    exact (measurable_potentialCoordinate k).comap_le
  have hEamb : ∀ j, MeasurableSet (E j 0) := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact hE0amb
    · exact measurableSet_of_shellLocalSigma (hEj j hj)
  have hFmeas : ∀ j k, MeasurableSet (F j k) := fun j k =>
    SubdiffusiveProcess.CoarseGrainingVocab.measurable_translatePotentialSequence _ (hEamb j)
  refine ⟨fun j k => (hT _).measure_preimage (hEamb j).nullMeasurableSet, ?_, ?_, ?_⟩
  · -- scale independence
    refine independentEventScales_of_blocks M.shellPrefix.independent
      (goodCubeBlock n) (pairwise_disjoint_goodCubeBlock n) ?_
    intro j
    refine MeasurableSpace.generateFrom_le ?_
    rintro A ⟨k, -, rfl⟩
    apply aux_lem_crossing_T_comap_block
    match j with
    | 0 =>
        exact restrictedCoefficientSigma_aCutoff_le_prefix M n _ _ hE0
    | (i + 1) =>
        have hle : shellLocalSigma (n + (i + 1))
            (SubdiffusiveProcess.Section9.centeredAxisCube 0 (C * (3 : ℝ) ^ (n + (i + 1)))) ≤
            ⨆ k ∈ goodCubeBlock n (i + 1), MeasurableSpace.comap
              (fun omega : PotentialSample d => omega k) inferInstance := by
          refine le_trans (MeasurableSpace.comap_mono
            (SubdiffusiveProcess.CoarseGrainingVocab.potentialFieldLocalSigma_le_borel _)) ?_
          exact le_iSup₂ (f := fun k (_ : k ∈ goodCubeBlock n (i + 1)) =>
            MeasurableSpace.comap (fun omega : PotentialSample d => omega k) inferInstance)
            (n + (i + 1)) rfl
        exact hle _ (hEj (i + 1) (Nat.le_add_left 1 i))
  · -- finite-range independence
    intro j S T hsep
    set L : ℝ := C * (3 : ℝ) ^ (n + j) with hL
    set US := ⋃ k ∈ S, SubdiffusiveProcess.Section9.centeredAxisCube (aux_lem_crossing_ctr ((3 : ℝ) ^ n) k) L
    set UT := ⋃ k ∈ T, SubdiffusiveProcess.Section9.centeredAxisCube (aux_lem_crossing_ctr ((3 : ℝ) ^ n) k) L
    have hUS : MeasurableSet US := MeasurableSet.biUnion S.to_countable fun k _ =>
      (isOpen_centeredAxisCube _ _).measurableSet
    have hUT : MeasurableSet UT := MeasurableSet.biUnion T.to_countable fun k _ =>
      (isOpen_centeredAxisCube _ _).measurableSet
    have hsepUT : ∀ ⦃x y : Vec d⦄, x ∈ US → y ∈ UT →
        Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n + j) ≤ Homogenization.euclideanNorm (x - y) := by
      intro x y hx hy
      obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨k', hk', hyk⟩ := Set.mem_iUnion₂.mp hy
      exact aux_lem_crossing_box_separation hCdep (hsep k hk k' hk') hxk hyk
    have hbox : ∀ k, translateSet (aux_lem_crossing_ctr ((3 : ℝ) ^ n) k)
        (SubdiffusiveProcess.Section9.centeredAxisCube (0 : Vec d) L) =
        SubdiffusiveProcess.Section9.centeredAxisCube (aux_lem_crossing_ctr ((3 : ℝ) ^ n) k) L := fun k =>
      aux_lem_crossing_translateSet_centeredAxisCube _ _
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · -- scale zero: the cutoff source σ-fields
      have hE0loc : MeasurableSet[SubdiffusiveProcess.CoarseGrainingVocab.aCutoffPotentialLocalSigma n
          (SubdiffusiveProcess.Section9.centeredAxisCube (0 : Vec d) (C * (3 : ℝ) ^ n))] (E 0 0) :=
        restrictedCoefficientSigma_aCutoff_le_localSource M n (isOpen_centeredAxisCube _ _) _ hE0
      have hdom : ∀ R' : Set (Lattice d), eventFieldSigma (F 0) R' ≤
          SubdiffusiveProcess.CoarseGrainingVocab.aCutoffPotentialLocalSigma n
            (⋃ k ∈ R', SubdiffusiveProcess.Section9.centeredAxisCube (aux_lem_crossing_ctr ((3 : ℝ) ^ n) k)
              (C * (3 : ℝ) ^ (n + 0))) := by
        intro R'
        refine MeasurableSpace.generateFrom_le ?_
        rintro A ⟨k, hk, rfl⟩
        have h1 := aux_lem_crossing_T_aCutoffLocal (aux_lem_crossing_ctr ((3 : ℝ) ^ n) k) n _ hE0loc
        rw [aux_lem_crossing_translateSet_centeredAxisCube] at h1
        have hmono : SubdiffusiveProcess.CoarseGrainingVocab.aCutoffPotentialLocalSigma n
            (SubdiffusiveProcess.Section9.centeredAxisCube (aux_lem_crossing_ctr ((3 : ℝ) ^ n) k) (C * (3 : ℝ) ^ n)) ≤
            SubdiffusiveProcess.CoarseGrainingVocab.aCutoffPotentialLocalSigma n
              (⋃ k ∈ R', SubdiffusiveProcess.Section9.centeredAxisCube (aux_lem_crossing_ctr ((3 : ℝ) ^ n) k)
                (C * (3 : ℝ) ^ (n + 0))) := by
          unfold SubdiffusiveProcess.CoarseGrainingVocab.aCutoffPotentialLocalSigma
          refine iSup_mono fun q => MeasurableSpace.comap_mono ?_
          apply potentialLocalSigma_mono
          intro x hx
          exact Set.mem_iUnion₂.mpr ⟨k, hk, by simpa using hx⟩
        exact hmono _ h1
      have hsep0 : ∀ ⦃x y : Vec d⦄, x ∈ US → y ∈ UT →
          Real.sqrt (d : ℝ) * (3 : ℝ) ^ n ≤ Homogenization.Book.Ch02.vecNorm (x - y) := by
        intro x y hx hy
        rw [← euclideanNorm_eq_vecNorm]
        simpa using hsepUT hx hy
      have hindep := SubdiffusiveProcess.CoarseGrainingVocab.indep_aCutoffPotentialLocalSigma_of_separation
        M n US UT hUS hUT hsep0
      exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hindep (hdom S)) (hdom T)
    · have hdom : ∀ R' : Set (Lattice d), eventFieldSigma (F j) R' ≤
          shellLocalSigma (n + j)
            (⋃ k ∈ R', SubdiffusiveProcess.Section9.centeredAxisCube (aux_lem_crossing_ctr ((3 : ℝ) ^ n) k) L) := by
        intro R'
        refine MeasurableSpace.generateFrom_le ?_
        rintro A ⟨k, hk, rfl⟩
        have h1 := aux_lem_crossing_T_shellLocalSigma (aux_lem_crossing_ctr ((3 : ℝ) ^ n) k)
          (n + j) _ (hEj j hj)
        rw [hbox k] at h1
        exact shellLocalSigma_mono (n + j) (Set.subset_biUnion_of_mem hk) _ h1
      have hindep := indep_shellLocalSigma_of_separation M (n + j) US UT hUS hUT hsepUT
      exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hindep (hdom S)) (hdom T)
  · -- translation invariance
    exact translationInvariantEventLaw_of_covariant hFmeas
      (fun m => translatePotentialSequence (aux_lem_crossing_ctr ((3 : ℝ) ^ n) m))
      (fun m => SubdiffusiveProcess.CoarseGrainingVocab.measurable_translatePotentialSequence _)
      (fun m => SubdiffusiveProcess.CoarseGrainingVocab.potentialSequenceLaw_stationary M _)
      (fun j k m => aux_lem_crossing_Efine_cov _ E j k m)

end FineHyps

end SubdiffusiveProcess.Paper
namespace SubdiffusiveProcess.Paper

open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube

section PercTail

/-- **Tail of an `O_Γ(1)`-bounded variable.** -/
theorem aux_lem_crossing_OGamma_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {A : ℝ} (hA : 0 < A) {X : Ω → ℝ} (h : SubdiffusiveProcess.OGammaLE μ 1 A X)
    {s : ℝ} (_hs : 0 ≤ s) :
    μ {ω | s < X ω} ≤ ENNReal.ofReal (2 * Real.exp (-(s / A))) := by
  obtain ⟨hint, hle⟩ := h
  set f : Ω → ℝ := fun ω => Real.exp ((A⁻¹ * max (X ω) 0) ^ (1 : ℝ)) with hf
  have hnn : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le
  have hM := mul_meas_ge_le_integral_of_nonneg hnn hint (Real.exp (s / A))
  have hsub : {ω | s < X ω} ⊆ {ω | Real.exp (s / A) ≤ f ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, hf, Real.rpow_one]
    apply Real.exp_le_exp.mpr
    rw [inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (le_trans hω.le (le_max_left _ _)) hA.le
  have hreal : μ.real {ω | Real.exp (s / A) ≤ f ω} ≤ 2 * Real.exp (-(s / A)) := by
    have hpos := Real.exp_pos (s / A)
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hpos]
    linarith [hM.trans hle]
  calc μ {ω | s < X ω} ≤ μ {ω | Real.exp (s / A) ≤ f ω} := measure_mono hsub
    _ = ENNReal.ofReal (μ.real {ω | Real.exp (s / A) ≤ f ω}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

end PercTail

section Density

attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- The fine lattice site nearest to `x`. -/
def aux_lem_crossing_near (ℓ : ℝ) (x : Homogenization.Vec d) : Lattice d :=
  fun i => round (16 * x i / ℓ)

theorem aux_lem_crossing_near_close {ℓ : ℝ} (hℓ : 0 < ℓ) (x : Homogenization.Vec d) (i : Fin d) :
    |aux_lem_crossing_ctr ℓ (aux_lem_crossing_near ℓ x) i - x i| ≤ ℓ / 32 := by
  rw [aux_lem_crossing_ctr_apply]
  have h := abs_sub_round (16 * x i / ℓ)
  have heq : ℓ / 16 * ((aux_lem_crossing_near ℓ x i : ℤ) : ℝ) - x i =
      ℓ / 16 * ((round (16 * x i / ℓ) : ℝ) - 16 * x i / ℓ) := by
    simp only [aux_lem_crossing_near]; field_simp
  rw [heq, abs_mul, abs_of_pos (by positivity), abs_sub_comm]
  calc ℓ / 16 * |16 * x i / ℓ - (round (16 * x i / ℓ) : ℝ)| ≤ ℓ / 16 * (1 / 2) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = ℓ / 32 := by ring

theorem aux_lem_crossing_list_count {Good : Set (Lattice d)} (q : ℕ → Lattice d) (N : ℕ)
    {chosen : List (Lattice d)} (hsub : chosen.Sublist ((List.range (N + 1)).map q))
    (hgood : ∀ v ∈ chosen, v ∈ Good) :
    (chosen.length : ℝ) ≤ (((Finset.range (N + 1)).filter (fun i => q i ∈ Good)).card : ℝ) := by
  have h1 : chosen.filter (fun v => decide (v ∈ Good)) = chosen :=
    List.filter_eq_self.mpr fun v hv => by simpa using hgood v hv
  have h2 := hsub.filter (fun v => decide (v ∈ Good))
  rw [h1, List.filter_map] at h2
  have h3 := h2.length_le
  rw [List.length_map] at h3
  have h4 : ((Finset.range (N + 1)).filter (fun i => q i ∈ Good)).card =
      ((List.range (N + 1)).filter ((fun v => decide (v ∈ Good)) ∘ q)).length := by
    rw [Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range,
      Multiset.filter_coe, Multiset.coe_card]
    congr 1
  rw [h4]
  exact_mod_cast h3

theorem aux_lem_crossing_getElem!_map_range (q : ℕ → Lattice d) (N k : ℕ) (hk : k < N + 1) :
    ((List.range (N + 1)).map q)[k]! = q k := by
  rw [getElem!_pos ((List.range (N + 1)).map q) k (by simpa using hk)]
  simp

/-- **Good-site density along fine lattice paths** from percolation clause 1. -/
theorem aux_lem_crossing_density {Ω : Type*} {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ}
    {c Cp qp : ℝ} {crossing component : Lattice d → Ω → ℕ} {ω : Ω}
    (hgeo : FiniteRangePercolationGeometryAt E Cbox
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps d) c Cp qp
      crossing component ω)
    (hc : 0 < c) {ℓ : ℝ} (hℓ : 0 < ℓ) (x : Homogenization.Vec d) {R : ℝ} (hR : 32 * ℓ ≤ R)
    (hcross : crossing (aux_lem_crossing_near ℓ x) ω ≤ ⌊16 * R / ℓ⌋₊ - 7) :
    ∀ (N : ℕ) (q : ℕ → Lattice d), IsJStepPath 1 q N →
      Set.InjOn q (Set.Icc 0 N) → x ∈ cubeSet (aux_lem_crossing_W ℓ (q 0)) →
      (∃ y ∈ cubeSet (aux_lem_crossing_W ℓ (q N)), R ≤ dist y x) →
      8 * c * R / ℓ ≤ (((Finset.range (N + 1)).filter
        (fun i => q i ∈ {k | IsPercolationGoodSite E Cbox ω k})).card : ℝ) := by
  intro N q hJ _ hq0 hqN
  set z := aux_lem_crossing_near ℓ x with hz
  set l : ℕ := ⌊16 * R / ℓ⌋₊ - 7 with hl
  set X : ℝ := 16 * R / ℓ with hX
  have hbig : 512 ≤ X := by rw [hX, le_div_iff₀ hℓ]; linarith
  have hX8 : 16 * R / ℓ = 2 * (8 * R / ℓ) := by ring
  have hfl : X - 1 < (⌊X⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one X; linarith
  have hfl' : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le (by linarith)
  have hge7 : 7 ≤ ⌊X⌋₊ := by
    have : (7 : ℝ) ≤ ⌊X⌋₊ := by linarith
    exact_mod_cast this
  have hlR : (l : ℝ) = (⌊X⌋₊ : ℝ) - 7 := by
    rw [hl, Nat.cast_sub hge7]; norm_num
  have hXℓ : X * (ℓ / 16) = R := by rw [hX]; field_simp
  -- the list path
  set path := (List.range (N + 1)).map q with hpath
  have hlen : path.length = N + 1 := by simp [hpath]
  have hJlist : IsJStepListPath (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps d)
      path := by
    intro k hk
    rw [hlen] at hk
    rw [aux_lem_crossing_getElem!_map_range q N k (by omega),
      aux_lem_crossing_getElem!_map_range q N (k + 1) hk]
    exact hJ k (by omega)
  have hℓ16 : (0 : ℝ) < ℓ / 16 := by positivity
  -- the start is near `z`
  have hstart : ∃ v ∈ path, InLatticeBallReal z v (l / 3 : ℝ) := by
    refine ⟨q 0, List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩, fun i => ?_⟩
    rw [cubeSet, aux_lem_crossing_mem_centeredAxisCube_iff] at hq0
    have h1 := hq0 i
    have h2 := aux_lem_crossing_near_close hℓ x i
    simp only [aux_lem_crossing_W] at h1
    rw [aux_lem_crossing_ctr_apply] at h1 h2
    have hdiff' : |ℓ / 16 * ((q 0 i : ℝ) - (z i : ℝ))| < 13 * ℓ / 32 := by
      calc |ℓ / 16 * ((q 0 i : ℝ) - (z i : ℝ))|
          = |(x i - ℓ / 16 * (z i : ℝ)) - (x i - ℓ / 16 * (q 0 i : ℝ))| := by ring_nf
        _ ≤ |x i - ℓ / 16 * (z i : ℝ)| + |x i - ℓ / 16 * (q 0 i : ℝ)| := abs_sub _ _
        _ < ℓ / 32 + 3 * ℓ / 4 / 2 := by
            rw [abs_sub_comm (x i) (ℓ / 16 * (z i : ℝ))]
            exact add_lt_add_of_le_of_lt h2 h1
        _ = 13 * ℓ / 32 := by ring
    have hdiff : ℓ / 16 * |(q 0 i : ℝ) - (z i : ℝ)| < 13 * ℓ / 32 := by
      rwa [abs_mul, abs_of_pos hℓ16] at hdiff'
    have h3 : |(q 0 i : ℝ) - (z i : ℝ)| < 13 / 2 := by
      by_contra hc
      push Not at hc
      have := mul_le_mul_of_nonneg_left hc hℓ16.le
      linarith
    have hint : |(q 0 i - z i : ℤ)| ≤ 6 := by
      have h7 : |(q 0 i - z i : ℤ)| < 7 := by
        by_contra hc; push Not at hc
        have : (7 : ℝ) ≤ ((|(q 0 i - z i : ℤ)| : ℤ) : ℝ) := by exact_mod_cast hc
        rw [Int.cast_abs] at this
        push_cast at this
        linarith
      omega
    have h4 : (6 : ℝ) ≤ (l : ℝ) / 3 := by rw [hlR]; linarith
    have h5 : ((|(q 0 i - z i : ℤ)| : ℤ) : ℝ) ≤ 6 := by exact_mod_cast hint
    exact h5.trans h4
  -- the end is far from `z`
  have hend : ∃ v ∈ path, ¬ InLatticeBallReal z v (2 * l / 3 : ℝ) := by
    refine ⟨q N, List.mem_map.mpr ⟨N, List.mem_range.mpr (by omega), rfl⟩, ?_⟩
    obtain ⟨y, hy, hRy⟩ := hqN
    intro hball
    rw [cubeSet, aux_lem_crossing_mem_centeredAxisCube_iff] at hy
    have hsup : ∀ i, |y i - x i| < 2 * l / 3 * (ℓ / 16) + 13 * ℓ / 32 := by
      intro i
      have h1 := hy i
      have h2 := aux_lem_crossing_near_close hℓ x i
      have h3 := hball i
      simp only [aux_lem_crossing_W] at h1
      rw [aux_lem_crossing_ctr_apply] at h1 h2
      have h3' : |(q N i : ℝ) - (z i : ℝ)| ≤ 2 * l / 3 := by
        have : ((|(q N i - z i : ℤ)| : ℤ) : ℝ) ≤ 2 * l / 3 := h3
        rw [Int.cast_abs] at this
        push_cast at this; exact this
      calc |y i - x i| = |(y i - ℓ / 16 * (q N i : ℝ)) + ℓ / 16 * ((q N i : ℝ) - (z i : ℝ)) +
            (ℓ / 16 * (z i : ℝ) - x i)| := by ring_nf
        _ ≤ |y i - ℓ / 16 * (q N i : ℝ)| + |ℓ / 16 * ((q N i : ℝ) - (z i : ℝ))| +
            |ℓ / 16 * (z i : ℝ) - x i| := abs_add_three _ _ _
        _ < 3 * ℓ / 4 / 2 + ℓ / 16 * (2 * l / 3) + ℓ / 32 := by
            rw [abs_mul, abs_of_pos hℓ16]
            have := mul_le_mul_of_nonneg_left h3' hℓ16.le
            linarith
        _ = 2 * l / 3 * (ℓ / 16) + 13 * ℓ / 32 := by ring
    have hbound : 2 * (l : ℝ) / 3 * (ℓ / 16) + 13 * ℓ / 32 ≤ R := by
      rw [hlR]
      have h1 : ((⌊X⌋₊ : ℝ) - 7) * (ℓ / 16) ≤ X * (ℓ / 16) :=
        mul_le_mul_of_nonneg_right (by linarith) hℓ16.le
      rw [hXℓ] at h1
      nlinarith
    have hlt : dist y x < R := by
      rcases Nat.eq_zero_or_pos d with hd0 | hdpos
      · subst hd0
        have : dist y x = 0 := by
          rw [dist_eq_norm, Subsingleton.elim (y - x) 0, norm_zero]
        linarith
      · have : Nonempty (Fin d) := ⟨⟨0, hdpos⟩⟩
        rw [dist_pi_lt_iff (by linarith)]
        intro i
        rw [Real.dist_eq]
        linarith [hsup i]
    linarith
  obtain ⟨chosen, hsub, hcl, hgoodc, -⟩ := (hgeo z).1 l hcross path hJlist hstart hend
  have hcount := aux_lem_crossing_list_count (Good := {k | IsPercolationGoodSite E Cbox ω k}) q N
    hsub (fun v hv => (hgoodc v hv).1)
  refine le_trans ?_ (hcl.trans hcount)
  rw [hlR]
  have h8 : 8 * R / ℓ ≤ (⌊X⌋₊ : ℝ) - 7 := by
    have : 8 ≤ 8 * R / ℓ := by rw [le_div_iff₀ hℓ]; linarith
    have hXeq : X = 2 * (8 * R / ℓ) := by rw [hX]; ring
    linarith
  calc 8 * c * R / ℓ = c * (8 * R / ℓ) := by ring
    _ ≤ c * ((⌊X⌋₊ : ℝ) - 7) := mul_le_mul_of_nonneg_left h8 hc.le

end Density

end SubdiffusiveProcess.Paper
namespace SubdiffusiveProcess.Paper

open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab (translatePotentialSequence)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

section FinalHelpers

/-- For small disorder the percolation parameter is large. -/
theorem aux_lem_crossing_delta_small {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₁ → δ ^ 2 * Real.log δ ^ 2 ≤ ε := by
  have hc := Real.continuous_mul_log.continuousAt (x := (0 : ℝ))
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ₁, hδ₁, h⟩ := hc (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
  refine ⟨δ₁, hδ₁, fun δ hδ hδ1 => ?_⟩
  have h1 := h (x := δ) (by rw [Real.dist_eq, sub_zero, abs_of_pos hδ]; exact hδ1)
  simp only [zero_mul, Real.dist_eq, sub_zero] at h1
  have h2 : (δ * Real.log δ) ^ 2 < ε := by
    have := sq_lt_sq' (by linarith [abs_nonneg (δ * Real.log δ), neg_abs_le (δ * Real.log δ)])
      (lt_of_le_of_lt (le_abs_self _) h1)
    rwa [Real.sq_sqrt hε.le] at this
  nlinarith [h2]

variable {d : ℕ}

/-- Finitely many starting sites cover a bounded region. -/
theorem aux_lem_crossing_card_near {Region : Set (Homogenization.Vec d)}
    (hRegion : Bornology.IsBounded Region) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ Z : Finset (Lattice d), (∀ x ∈ Region, aux_lem_crossing_near ℓ x ∈ Z) ∧
      (Z.card : ℝ) ≤ 32 ^ d * (1 + Metric.diam Region / ℓ) ^ d := by
  classical
  rcases Region.eq_empty_or_nonempty with hE | ⟨x0, hx0⟩
  · refine ⟨∅, by simp [hE], ?_⟩
    simp only [Finset.card_empty, Nat.cast_zero]
    have := Metric.diam_nonneg (s := Region)
    positivity
  set D := Metric.diam Region with hD
  have hD0 : 0 ≤ D := Metric.diam_nonneg
  set m : ℤ := ⌈16 * D / ℓ⌉ + 1 with hm
  set lo : Lattice d := fun i => aux_lem_crossing_near ℓ x0 i - m
  set hi : Lattice d := fun i => aux_lem_crossing_near ℓ x0 i + m
  refine ⟨Fintype.piFinset fun i => Finset.Icc (lo i) (hi i), ?_, ?_⟩
  · intro x hx
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have hdist : |x i - x0 i| ≤ D := by
      have h1 : dist x x0 ≤ D := Metric.dist_le_diam_of_mem hRegion hx hx0
      exact (by rw [← Real.dist_eq]; exact dist_le_pi_dist x x0 i : |x i - x0 i| ≤ dist x x0).trans h1
    have hr1 := abs_sub_round (16 * x i / ℓ)
    have hr0 := abs_sub_round (16 * x0 i / ℓ)
    have hsc : |16 * x i / ℓ - 16 * x0 i / ℓ| ≤ 16 * D / ℓ := by
      rw [← sub_div, ← mul_sub, abs_div, abs_mul, abs_of_pos hℓ]
      norm_num
      exact div_le_div_of_nonneg_right (by linarith [hdist]) hℓ.le
    have hceil := Int.le_ceil (16 * D / ℓ)
    have hdiff : |((aux_lem_crossing_near ℓ x i - aux_lem_crossing_near ℓ x0 i : ℤ) : ℝ)| ≤
        16 * D / ℓ + 1 := by
      simp only [aux_lem_crossing_near]
      push_cast
      calc |(round (16 * x i / ℓ) : ℝ) - (round (16 * x0 i / ℓ) : ℝ)|
          = |((round (16 * x i / ℓ) : ℝ) - 16 * x i / ℓ) + (16 * x i / ℓ - 16 * x0 i / ℓ) +
              (16 * x0 i / ℓ - (round (16 * x0 i / ℓ) : ℝ))| := by ring_nf
        _ ≤ |(round (16 * x i / ℓ) : ℝ) - 16 * x i / ℓ| + |16 * x i / ℓ - 16 * x0 i / ℓ| +
              |16 * x0 i / ℓ - (round (16 * x0 i / ℓ) : ℝ)| := abs_add_three _ _ _
        _ ≤ 1 / 2 + 16 * D / ℓ + 1 / 2 := by
            rw [abs_sub_comm ((round (16 * x i / ℓ) : ℝ))]
            linarith
        _ = 16 * D / ℓ + 1 := by ring
    have hmR : 16 * D / ℓ + 1 ≤ (m : ℝ) := by rw [hm]; push_cast; linarith
    have habs : |(aux_lem_crossing_near ℓ x i - aux_lem_crossing_near ℓ x0 i : ℤ)| ≤ m := by
      have : ((|(aux_lem_crossing_near ℓ x i - aux_lem_crossing_near ℓ x0 i : ℤ)| : ℤ) : ℝ) ≤ m := by
        rw [Int.cast_abs]; linarith
      exact_mod_cast this
    rw [abs_le] at habs
    simp only [lo, hi]
    constructor <;> linarith [habs.1, habs.2]
  · rw [Fintype.card_piFinset]
    have hcard : ∀ i, ((Finset.Icc (lo i) (hi i)).card : ℝ) ≤ 32 * (1 + D / ℓ) := by
      intro i
      rw [Int.card_Icc]
      have hle : hi i + 1 - lo i = 2 * m + 1 := by simp only [lo, hi]; ring
      rw [hle]
      have hm0 : 0 ≤ 2 * m + 1 := by
        have : (0 : ℤ) ≤ ⌈16 * D / ℓ⌉ := Int.ceil_nonneg (by positivity)
        omega
      rw [show ((2 * m + 1).toNat : ℝ) = ((2 * m + 1 : ℤ) : ℝ) by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hm0]]
      push_cast
      have hceil : (⌈16 * D / ℓ⌉ : ℝ) < 16 * D / ℓ + 1 := Int.ceil_lt_add_one _
      rw [hm]; push_cast
      have : 16 * D / ℓ = 16 * (D / ℓ) := by ring
      nlinarith [div_nonneg hD0 hℓ.le]
    calc ((∏ i, (Finset.Icc (lo i) (hi i)).card : ℕ) : ℝ)
        = ∏ i, ((Finset.Icc (lo i) (hi i)).card : ℝ) := by push_cast; rfl
      _ ≤ ∏ _i : Fin d, (32 * (1 + D / ℓ)) :=
          Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => hcard i)
      _ = 32 ^ d * (1 + D / ℓ) ^ d := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]

variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- Almost surely every fine translate of the lifted sample is anchored-good. -/
theorem aux_lem_crossing_translated_good_ae (M : GMCModel d) (ℓ : ℝ) :
    ∀ᵐ omega ∂(SubdiffusiveProcess.chaosSampleLaw M).toMeasure, ∀ k : Lattice d,
      translatePotentialSequence (aux_lem_crossing_ctr ℓ k) (aux_lem_crossing_lift omega) ∈
        anchoredC11GoodSet d := by
  rw [ae_all_iff]
  intro k
  have hmp := aux_lem_crossing_measurePreserving_lift M
  have hgoodm := SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measurableSet_anchoredC11GoodSet d
  have hT : MeasurePreserving (translatePotentialSequence (d := d) (aux_lem_crossing_ctr ℓ k))
      M.P.toMeasure M.P.toMeasure :=
    ⟨SubdiffusiveProcess.CoarseGrainingVocab.measurable_translatePotentialSequence _,
      SubdiffusiveProcess.CoarseGrainingVocab.potentialSequenceLaw_stationary M _⟩
  have hfull : ∀ᵐ ω' ∂M.P.toMeasure,
      translatePotentialSequence (aux_lem_crossing_ctr ℓ k) ω' ∈ anchoredC11GoodSet d := by
    have h1 : ∀ᵐ ω' ∂M.P.toMeasure, ω' ∈ anchoredC11GoodSet d :=
      (mem_ae_iff_prob_eq_one hgoodm).mpr
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measure_anchoredC11GoodSet_eq_one M)
    exact hT.quasiMeasurePreserving.ae h1
  exact hmp.quasiMeasurePreserving.ae hfull

end FinalHelpers

end SubdiffusiveProcess.Paper
namespace SubdiffusiveProcess.Paper

open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab (translatePotentialSequence)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

section EnvProof

attribute [local instance] Classical.propDecidable

/-- **The refined environment residual is proved** (from the seven exports; the anchored clause
of `weighted_good_cube_events` is used). -/
theorem aux_lem_crossing_envResidual2_proof {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) : aux_lem_crossing_envResidual2 d := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨cg, Cg, eps0, p0, Cdepg, j1, j2, hcg, hCg, -, -, -, -, grid0, Pfam0, Qfam0, Afam0,
    -, hGCE⟩ := _root_.SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.RobustGoodCube.weighted_good_cube_events_v5_robust
      d hd (1 / 2) (by norm_num) (by norm_num)
  set Cdep' : ℕ := ⌈16 * (Cg + Real.sqrt (d : ℝ))⌉₊ with hCdep'def
  have hCdep' : 16 * (Cg + Real.sqrt (d : ℝ)) ≤ (Cdep' : ℝ) := Nat.le_ceil _
  obtain ⟨q0, L0, Cbox, cp, Cp, hcp, hCp, -, hperc⟩ :=
    _root_.SubdiffusiveProcess.Section9.weighted_multiscale_percolation d Cdep' Cg cg hCg hcg hd
  obtain ⟨δ₁, hδ₁, hsmall⟩ := aux_lem_crossing_delta_small
    (ε := cg / ((q0 : ℝ) + 1)) (div_pos hcg (by positivity))
  refine ⟨cg, min cg (δ₁ / 2), hcg, lt_min hcg (half_pos hδ₁), min_le_left _ _, ?_⟩
  intro M hMδ
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hδhalf : M.delta ≤ 1 / 2 := M.shellPrefix.delta_le_half
  have hδcg : M.delta ≤ cg := hMδ.trans (min_le_left _ _)
  have hδδ₁ : M.delta < δ₁ := lt_of_le_of_lt (hMδ.trans (min_le_right _ _)) (half_lt_self hδ₁)
  have hlog : Real.log M.delta < 0 := Real.log_neg hδpos (by linarith)
  have hden : 0 < M.delta ^ 2 * Real.log M.delta ^ 2 :=
    mul_pos (pow_pos hδpos 2) (pow_pos (neg_pos.mpr hlog) 2 |>.trans_eq (by ring))
  set qg : ℝ := cg / (M.delta ^ 2 * Real.log M.delta ^ 2) with hqg
  have hqgpos : 0 < qg := div_pos hcg hden
  have hq0 : (q0 : ℝ) ≤ qg := by
    have h1 := hsmall M.delta hδpos hδδ₁
    rw [hqg, le_div_iff₀ hden]
    have h2 : (q0 : ℝ) * (M.delta ^ 2 * Real.log M.delta ^ 2) ≤ (q0 + 1) * (cg / ((q0 : ℝ) + 1)) :=
      mul_le_mul (by linarith) h1 hden.le (by positivity)
    rwa [mul_div_cancel₀ _ (by positivity)] at h2
  have hqabs : cg / (M.delta ^ 2 * |Real.log M.delta| ^ 2) = qg := by rw [sq_abs]
  set CB : ℝ := 2 * 32 ^ d + 32 + L0 with hCBdef
  have hCB : 0 < CB := by positivity
  refine ⟨min cg Cg, max cg Cg, 8 * cp, 4 / Cp, CB, lt_min hcg hCg,
    (min_le_left _ _).trans (le_max_left _ _), by positivity, by positivity, hCB, ?_⟩
  intro H hH PN KN hKN hin L hL hLlocal hLstrong Region hRegion n R hR
  set ℓ : ℝ := (3 : ℝ) ^ n with hℓdef
  have hℓ : 0 < ℓ := by positivity
  have hRℓ : CB ≤ R / ℓ := by rw [le_div_iff₀ hℓ]; exact hR
  have hR32 : 32 * ℓ ≤ R := by
    have : (32 : ℝ) ≤ CB := by rw [hCBdef]; have := pow_pos (by norm_num : (0:ℝ) < 32) d; have : (0:ℝ) ≤ L0 := Nat.cast_nonneg _; linarith
    rw [le_div_iff₀ hℓ] at hRℓ
    nlinarith
  obtain ⟨E, hE0, hEj, hEprob, -, -, -, -, hEanch⟩ := hGCE M hδcg n
  set F := aux_lem_crossing_Efine ℓ E with hFdef
  obtain ⟨hFprob, hFind, hFfin, hFtrans⟩ :=
    aux_lem_crossing_Efine_hyps M n hCg.le hCdep' E (hE0 0) (fun j hj => hEj j hj 0)
  have hprob : ∀ j z, M.P.toMeasure (F j z) ≤
      ENNReal.ofReal (Cg * Real.exp (-cg * qg * 3 ^ ((3 : ℝ) * j / 2))) := by
    intro j z
    rw [hFprob j z]
    refine (hEprob j 0).trans (le_of_eq ?_)
    congr 2
    rw [hqg]; ring_nf
  obtain ⟨crossing, component, -, -, hcrossTail, -, hgeoAE⟩ :=
    hperc M.P.toMeasure F qg hq0 hprob hFind hFfin hFtrans
  obtain ⟨Z, hZ, hZcard⟩ := aux_lem_crossing_card_near hRegion hℓ
  set l : ℕ := ⌊16 * R / ℓ⌋₊ - 7 with hldef
  set μ := (SubdiffusiveProcess.chaosSampleLaw M).toMeasure with hμ
  have hmp := aux_lem_crossing_measurePreserving_lift M
  -- the good environment set
  set G : Set (SubdiffusiveProcess.BilateralField d) := {omega |
    (∀ k : ℕ, aux_lem_crossing_forget (aux_lem_crossing_lift omega k) = omega (k : ℤ)) ∧
    Tendsto (SubdiffusiveProcess.infraredPartialSum omega) atTop (𝓝 (H omega)) ∧
    aux_lem_crossing_lift omega ∈ anchoredC11GoodSet d ∧
    (∀ k : Lattice d, translatePotentialSequence (aux_lem_crossing_ctr ℓ k)
      (aux_lem_crossing_lift omega) ∈ anchoredC11GoodSet d) ∧
    LocalDiffusionData (SubdiffusiveProcess.cutoffCoefficient M H omega 0)
      (SubdiffusiveProcess.cutoffSpeedDensity M H omega 0) (L 0 omega) ∧
    FiniteRangePercolationGeometryAt F Cbox (section9CrossingSteps d) cp Cp qg crossing component
      (aux_lem_crossing_lift omega)} with hGdef
  have hGae : ∀ᵐ omega ∂μ, omega ∈ G := by
    filter_upwards [aux_lem_crossing_forget_lift_ae M, hH.2, aux_lem_crossing_lift_good_ae M,
      aux_lem_crossing_translated_good_ae M ℓ, hLlocal,
      hmp.quasiMeasurePreserving.ae hgeoAE.2] with omega h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5 0, h6⟩
  have hGc : μ Gᶜ = 0 := by rw [ae_iff] at hGae; convert hGae using 2
  set Null := toMeasurable μ Gᶜ with hNull
  set BadP : Set (PotentialSample d) :=
    ⋃ z ∈ Z, toMeasurable M.P.toMeasure {ω' | l < crossing z ω'} with hBadP
  have hBadPm : MeasurableSet BadP :=
    Finset.measurableSet_biUnion Z fun z _ => measurableSet_toMeasurable _ _
  refine ⟨aux_lem_crossing_lift ⁻¹' BadP ∪ Null,
    (aux_lem_crossing_measurable_lift hBadPm).union (measurableSet_toMeasurable _ _), ?_, ?_⟩
  · -- the probability bound
    have hL0le : (L0 : ℝ) ≤ l := by
      have hfl : 16 * R / ℓ - 1 < (⌊16 * R / ℓ⌋₊ : ℝ) := by
        have := Nat.lt_floor_add_one (16 * R / ℓ); linarith
      have hge7 : 7 ≤ ⌊16 * R / ℓ⌋₊ := by
        have : (7 : ℝ) ≤ ⌊16 * R / ℓ⌋₊ := by
          have : (512 : ℝ) ≤ 16 * R / ℓ := by rw [le_div_iff₀ hℓ]; linarith
          linarith
        exact_mod_cast this
      rw [hldef, Nat.cast_sub hge7]
      have : (L0 : ℝ) + 8 ≤ 16 * R / ℓ := by
        have h1 : (L0 : ℝ) ≤ CB := by rw [hCBdef]; have := pow_pos (by norm_num : (0:ℝ) < 32) d; linarith
        have h2 : 16 * CB ≤ 16 * R / ℓ := by
          have := mul_le_mul_of_nonneg_left hRℓ (by norm_num : (0:ℝ) ≤ 16)
          rwa [show 16 * (R / ℓ) = 16 * R / ℓ by ring] at this
        have h3 : 8 ≤ 15 * CB := by
          have : (32 : ℝ) ≤ CB := by rw [hCBdef]; have := pow_pos (by norm_num : (0:ℝ) < 32) d; have : (0:ℝ) ≤ L0 := Nat.cast_nonneg _; linarith
          linarith
        linarith
      push_cast; linarith
    have hs : 4 * R / ℓ ≤ (l : ℝ) - L0 := by
      have hfl : 16 * R / ℓ - 1 < (⌊16 * R / ℓ⌋₊ : ℝ) := by
        have := Nat.lt_floor_add_one (16 * R / ℓ); linarith
      have hge7 : 7 ≤ ⌊16 * R / ℓ⌋₊ := by
        have : (7 : ℝ) ≤ ⌊16 * R / ℓ⌋₊ := by
          have : (512 : ℝ) ≤ 16 * R / ℓ := by rw [le_div_iff₀ hℓ]; linarith
          linarith
        exact_mod_cast this
      rw [hldef, Nat.cast_sub hge7]
      have h1 : (L0 : ℝ) ≤ CB := by rw [hCBdef]; have := pow_pos (by norm_num : (0:ℝ) < 32) d; linarith
      have h2 : CB ≤ R / ℓ := hRℓ
      have h32 : (32 : ℝ) ≤ CB := by rw [hCBdef]; have := pow_pos (by norm_num : (0:ℝ) < 32) d; have : (0:ℝ) ≤ L0 := Nat.cast_nonneg _; linarith
      have e1 : 16 * R / ℓ = 16 * (R / ℓ) := by ring
      have e2 : 4 * R / ℓ = 4 * (R / ℓ) := by ring
      push_cast; linarith
    have htail : ∀ z, M.P.toMeasure {ω' | l < crossing z ω'} ≤
        ENNReal.ofReal (2 * Real.exp (-(4 / Cp * qg * R / ℓ))) := by
      intro z
      have hsub : {ω' | l < crossing z ω'} ⊆
          {ω' | (l : ℝ) - L0 < (crossing z ω' : ℝ) - L0} := by
        intro ω' hω'
        simp only [Set.mem_ofPred_eq] at hω' ⊢
        have : (l : ℝ) < crossing z ω' := by exact_mod_cast hω'
        linarith
      refine (measure_mono hsub).trans ?_
      refine (aux_lem_crossing_OGamma_tail M.P.toMeasure (div_pos hCp hqgpos) (hcrossTail z)
        (by linarith)).trans (ENNReal.ofReal_le_ofReal ?_)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      rw [div_div_eq_mul_div]
      have : 4 / Cp * qg * R / ℓ = (4 * R / ℓ) * qg / Cp := by field_simp
      rw [this]
      apply neg_le_neg
      apply div_le_div_of_nonneg_right _ hCp.le
      exact mul_le_mul_of_nonneg_right hs hqgpos.le |>.trans_eq' (by ring) |>.trans (le_of_eq (by ring))
    calc μ (aux_lem_crossing_lift ⁻¹' BadP ∪ Null)
        ≤ μ (aux_lem_crossing_lift ⁻¹' BadP) + μ Null := measure_union_le _ _
      _ = M.P.toMeasure BadP := by
          rw [hmp.measure_preimage hBadPm.nullMeasurableSet, hNull, measure_toMeasurable, hGc,
            add_zero]
      _ ≤ ∑ z ∈ Z, M.P.toMeasure (toMeasurable M.P.toMeasure {ω' | l < crossing z ω'}) :=
          measure_biUnion_finset_le Z _
      _ = ∑ z ∈ Z, M.P.toMeasure {ω' | l < crossing z ω'} := by
          simp_rw [measure_toMeasurable]
      _ ≤ ∑ _z ∈ Z, ENNReal.ofReal (2 * Real.exp (-(4 / Cp * qg * R / ℓ))) :=
          Finset.sum_le_sum fun z _ => htail z
      _ = ENNReal.ofReal (Z.card * (2 * Real.exp (-(4 / Cp * qg * R / ℓ)))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          rw [hqabs]
          have hE := Real.exp_pos (-(4 / Cp * qg * R / ℓ))
          have hdiam := Metric.diam_nonneg (s := Region)
          have h1 : (Z.card : ℝ) * (2 * Real.exp (-(4 / Cp * qg * R / ℓ))) ≤
              (32 ^ d * (1 + Metric.diam Region / ℓ) ^ d) * (2 * Real.exp (-(4 / Cp * qg * R / ℓ))) :=
            mul_le_mul_of_nonneg_right hZcard (by positivity)
          refine h1.trans ?_
          have h2 : 2 * 32 ^ d ≤ CB := by
            rw [hCBdef]; have : (0:ℝ) ≤ L0 := Nat.cast_nonneg _; linarith
          have h3 : 0 ≤ (1 + Metric.diam Region / ℓ) ^ d * Real.exp (-(4 / Cp * qg * R / ℓ)) := by
            positivity
          calc 32 ^ d * (1 + Metric.diam Region / ℓ) ^ d * (2 * Real.exp (-(4 / Cp * qg * R / ℓ)))
              = 2 * 32 ^ d * ((1 + Metric.diam Region / ℓ) ^ d *
                  Real.exp (-(4 / Cp * qg * R / ℓ))) := by ring
            _ ≤ CB * ((1 + Metric.diam Region / ℓ) ^ d * Real.exp (-(4 / Cp * qg * R / ℓ))) :=
                mul_le_mul_of_nonneg_right h2 h3
            _ = CB * (1 + Metric.diam Region / ℓ) ^ d * Real.exp (-(4 / Cp * qg * R / ℓ)) := by ring
  · intro omega homega
    have hωG : omega ∈ G := by
      by_contra hcon
      exact homega (Or.inr (subset_toMeasurable μ Gᶜ hcon))
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hωG
    have hcross : ∀ z ∈ Z, crossing z (aux_lem_crossing_lift omega) ≤ l := by
      intro z hz
      by_contra hcon
      push Not at hcon
      apply homega
      left
      simp only [Set.mem_preimage, hBadP, Set.mem_iUnion]
      exact ⟨z, hz, subset_toMeasurable _ _ hcon⟩
    have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    let : Denumerable (Lattice d) := Denumerable.ofEncodableOfInfinite (Lattice d)
    refine ⟨(Denumerable.eqv (Lattice d)).symm,
      {k | IsPercolationGoodSite F Cbox (aux_lem_crossing_lift omega) k}, ?_, ?_⟩
    · intro k hk
      have hgoodEv : translatePotentialSequence (aux_lem_crossing_ctr ℓ k)
          (aux_lem_crossing_lift omega) ∈ goodCubeEvent E 0 := by
        simp only [goodCubeEvent, Set.mem_iInter, Set.mem_compl_iff]
        intro j hj
        apply hk j k (by simp [InInfluenceBox, latticeDist])
        exact hj
      have hGMC := fun law hlaw =>
        (hEanch 0 ⟨_, h4 k⟩ hgoodEv law hlaw).1
      rw [aux_lem_crossing_goodCubeCentre_zero] at hGMC
      obtain ⟨hlow, hup⟩ := aux_lem_crossing_torsion_of_good M H L omega n
        (aux_lem_crossing_ctr ℓ k) h1 h2 h3 (h4 k) h5 p0 cg Cg _ _ hGMC
      have hFpos : 0 < SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom M) ℓ :=
        SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale_pos
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M) hℓ
      refine ⟨fun y hy => ((ENNReal.ofReal_le_ofReal ?_)).trans (hlow y hy),
        fun y hy => (hup y hy).trans (ENNReal.ofReal_le_ofReal ?_)⟩
      · exact mul_le_mul_of_nonneg_right (min_le_left _ _) hFpos.le
      · exact mul_le_mul_of_nonneg_right (le_max_right _ _) hFpos.le
    · intro x hx N q hJ hinj hq0 hqN
      exact aux_lem_crossing_density h6 hcp hℓ x hR32 (hcross _ (hZ x hx)) N q hJ hinj hq0 hqN

end EnvProof

end SubdiffusiveProcess.Paper
namespace SubdiffusiveProcess.Paper

/-- Lemma `lem_crossing`, "Crossing estimate at a fixed
pair of radii", repaired so that BOTH the physical assertion and the
transported cutoff assertion are conclusions.

Tick list:
- in_crossing actual attachment only, not the seven analytic results.  The paper's missing crossing
inputs are the percolation export, the good-cube package, local torsion, path discretization,
chronological selection, survival, and the iterated strong-Markov estimate.
- The carried lifetime-path law `L` is the finite-cutoff diffusion law supplied
  by `finiteDimensional_cutoff` 
  transported from `KN` by
  `LifetimePath.ofContinuousPath`.  Its `LocalDiffusionData` and `StrongMarkov`
  fields are supplied almost everywhere in the environment by that same
  diffusion construction, and their two full-measure events are intersected
  before the crossing estimate is applied.  The resulting common null set is
  absorbed into `Bad`; these interfaces are not conclusions of `in_crossing`.
- Their q=cgood/(delta² log²delta) and small-disorder threshold have constants
  before M, as native weighted_good_cube_events does.
- in_timescale supplies exact clock and ratio; physical_generator_reindexing and
  physical_rescaling supply the concrete cutoff transport, with relative-vs-raw
  clocks explained.
- BOTH physical and transported assertions are now conclusions.
- the seven published inputs are imported as GMC
  theorem exports; their applicability and transport remain proof obligations.
  hcross is the desired conclusion, never a premise.

The physical assertion is expressed using the cutoff-zero law `KN 0`, whose generator is
`ahom M 0⁻¹` times the raw physical generator, so that `X_t = Z_0(ahom M 0 · t)`;
its event is the exact path event `sup_{s ≤ ahom M 0 · u} |path s - x| ≥ R`.  The
transported assertion is the previous cutoff-`N` conclusion, verbatim, with
rescaled radius `r ≥ 3^{-N}` and time factor `u · Tscale(3^N) / Tscale(3^N r)`.
`cgood` and `delta0` are fixed before `M`, and `c, C, beta, Tscale` depend only
on the model and the dimension, not on the realization, `H`, `PN`, `KN`, `N`,
the region or the radii. -/
theorem lem_crossing
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    ∃ (cgood delta0 : ℝ), 0 < cgood ∧ 0 < delta0 ∧ delta0 ≤ cgood ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
        ∃ (c C beta : ℝ) (Tscale : ℝ → ℝ),
          0 < c ∧ 0 < C ∧ 0 < beta ∧
          (∀ m : ℕ, Tscale ((3 : ℝ) ^ m) =
            ((3 : ℝ) ^ (2 * m) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M m)) ∧
          (∀ (m : ℕ) (t : ℝ), 0 ≤ t → t ≤ 1 →
            Tscale ((3 : ℝ) ^ ((m : ℝ) + t))
              = ((3 : ℝ) ^ (2 * m) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M m) ^ (1 - t)
                * ((3 : ℝ) ^ (2 * (m + 1)) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M (m + 1)) ^ t) ∧
          (∀ r : ℝ, 1 ≤ r → 0 < Tscale r) ∧
          (beta ≤ 2 + 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P / Real.log 3) ∧
          (∀ r S : ℝ, 1 ≤ r → r ≤ S → Tscale S ≤ C * (S / r) ^ beta * Tscale r) ∧
          (let q : ℝ := cgood / (M.delta ^ 2 * |Real.log M.delta| ^ 2)
           0 < q ∧
             ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
               (_hH : InfraredCharacterization M H)
               (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
               (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
               (_hKN : ∀ N, IsMarkovKernel (KN N))
               (_hin : in_crossing M H PN KN)
               (L : ℕ → BilateralField d →
                 Kernel (SpatialCoordinates d)
                   (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
               (_hL : ∀ (N : ℕ) (omega : BilateralField d) (x : SpatialCoordinates d),
                 Measure.map MarkovProcess.LifetimePath.ofContinuousPath (KN N (omega, x)) =
                   L N omega x)
               (_hLlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                 ∀ (N : ℕ),
                   SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusionData
                     (cutoffCoefficient M H omega N)
                     (cutoffSpeedDensity M H omega N)
                     (L N omega))
               (_hLstrong : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                 ∀ (N : ℕ),
                   SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.StrongMarkov
                     (L N omega)),
               (∀ (Region : Set (SpatialCoordinates d)), Bornology.IsBounded Region →
                 ∀ (r R : ℝ), 1 ≤ r → C * r ≤ R →
                   ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
                     (chaosSampleLaw M).toMeasure Bad ≤
                       ENNReal.ofReal (C * (1 + Metric.diam Region / r) ^ d *
                         Real.exp (-(c * q * R / r))) ∧
                     ∀ omega, omega ∉ Bad → ∀ x ∈ Region, ∀ u : ℝ, 0 < u →
                       (KN 0 (omega, x))
                           {path : DiffusionPath d |
                             ∃ s : ℝ≥0, (s : ℝ) ≤ SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 * u ∧
                               R ≤ dist (path s) x} ≤
                         ENNReal.ofReal (C * Real.exp (C * u / Tscale r - c * R / r))) ∧
               (∀ (N : ℕ) (Region : Set (SpatialCoordinates d)), Bornology.IsBounded Region →
                 ∀ (r R : ℝ), (3 : ℝ) ^ (-(N : ℝ)) ≤ r → C * r ≤ R →
                   ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
                     (chaosSampleLaw M).toMeasure Bad ≤
                       ENNReal.ofReal (C * (1 + Metric.diam Region / r) ^ d *
                         Real.exp (-(c * q * R / r))) ∧
                     ∀ omega, omega ∉ Bad → ∀ x ∈ Region, ∀ u : ℝ, 0 < u →
                       (KN N (omega, x))
                           {path : DiffusionPath d |
                             ∃ s : ℝ≥0, (s : ℝ) ≤ u ∧ R ≤ dist (path s) x} ≤
                         ENNReal.ofReal (C * Real.exp (C * u * Tscale ((3 : ℝ) ^ N) /
                           Tscale ((3 : ℝ) ^ N * r) - c * R / r)))) := by
  exact aux_lem_crossing_of_envResidual hd
    (aux_lem_crossing_envResidual_of_envResidual2 (aux_lem_crossing_envResidual2_proof hd))

end SubdiffusiveProcess.Paper
