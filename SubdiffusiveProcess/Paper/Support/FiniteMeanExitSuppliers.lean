module

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
public import SubdiffusiveProcess.Lane3.DirichletForm
public import SubdiffusiveProcess.Lane2.KilledInverse
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Probability.CubeMassMartingale
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Inputs.MarkovProcesses
public import MarkovProcess.Trajectory.StoppingLtTop
public import MarkovProcess.Path.ExitTime
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import SubdiffusiveProcess.Frozen.Vocab.Ahom
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import SubdiffusiveProcess.Lane1.ExitMoment
public import SubdiffusiveProcess.Lane1.ChaosBasic
public import SubdiffusiveProcess.Paper.lem_killing

@[expose] public section





open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Internal finite-mean-exit passage. Its torsion and discounted-resolvent
premises are discharged in `mfd_convergence` by the proved torsion/growth and
killed-resolvent suppliers. This is not a paper-map principal. -/
theorem aux_cor_finite_exit_of_suppliers
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K)
    (hin : in_crossing M H PN KN)
    (Qc : ℕ → SpatialCoordinates d) (Qr : ℕ → ℝ) (hQr : ∀ n, 0 < Qr n)
    (htorsion : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ n : ℕ, ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ N : ℕ,
        ∀ x ∈ (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)),
          ∫⁻ path, ContinuousPath.exitTime (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)) path
            ∂(KN N (omega, x)) ≤ ENNReal.ofReal Cw)
    (hres : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (n : ℕ) (lam : ℝ), 0 < lam →
        ∀ x ∈ (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)),
          Tendsto (fun N ↦ ∫ path, (∫ t in Set.Ioi (0 : ℝ),
                Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                  ((centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))) path}
                  (fun s => Real.exp (-lam * s) * (1 : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (path (Real.toNNReal s))) t)
              ∂(KN N (omega, x)))
            atTop
            (nhds (∫ path, (∫ t in Set.Ioi (0 : ℝ),
                  Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                    ((centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))) path}
                    (fun s => Real.exp (-lam * s) * (1 : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (path (Real.toNNReal s))) t)
                ∂(K (omega, x))))) 
    (hQ : ∀ U : Set (SpatialCoordinates d), Bornology.IsBounded U →
      ∃ n : ℕ, U ⊆ (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d))) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, HasFiniteMeanExits K omega := by
  classical
  filter_upwards [htorsion, hres] with omega htor hr
  intro U hUopen hUbdd
  obtain ⟨n, hUn⟩ := hQ U hUbdd
  obtain ⟨Cw, hCw0, hCwb⟩ := htor n
  refine ⟨ENNReal.ofReal Cw, ENNReal.ofReal_lt_top, fun x hxU => ?_⟩
  set Qn : Set (SpatialCoordinates d) :=
    (centeredCube (Qc n) (Qr n) (hQr n) : Set (SpatialCoordinates d)) with hQn
  have hxQ : x ∈ Qn := hUn hxU
  have hQopen : IsOpen Qn := by
    rw [hQn, centeredCube_coe_eq_ball]
    exact Metric.isOpen_ball
  have hmeasexit : Measurable
      (ContinuousPath.exitTime Qn : DiffusionPath d → ℝ≥0∞) :=
    ContinuousPath.measurable_exitTime Qn hQopen
  -- the killed discounted source is the discounted survival integral
  have hinner : ∀ (lam : ℝ) (path : DiffusionPath d),
      (∫ t in Set.Ioi (0 : ℝ),
        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Qn path}
          (fun s => Real.exp (-lam * s) *
            (1 : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
              (path (Real.toNNReal s))) t)
        = survivalIntegral lam (ContinuousPath.exitTime Qn path) := by
    intro lam path
    simp [survivalIntegral]
  -- measurability and integrability of the survival integral along a path
  have hgmeas : ∀ lam : ℝ, 0 < lam → Measurable
      (fun path : DiffusionPath d =>
        survivalIntegral lam (ContinuousPath.exitTime Qn path)) :=
    fun lam hlam => (measurable_survivalIntegral hlam).comp hmeasexit
  have hgint : ∀ (lam : ℝ), 0 < lam →
      ∀ nu : Measure (DiffusionPath d), IsProbabilityMeasure nu →
      Integrable (fun path : DiffusionPath d =>
        survivalIntegral lam (ContinuousPath.exitTime Qn path)) nu := by
    intro lam hlam nu hnu
    refine Integrable.mono' (integrable_const lam⁻¹)
      (hgmeas lam hlam).aestronglyMeasurable ?_
    filter_upwards with path
    rw [Real.norm_eq_abs, abs_of_nonneg (survivalIntegral_nonneg _ _)]
    exact survivalIntegral_le_inv hlam _
  -- at every discount the limiting resolvent is bounded by the torsion constant
  have hlimbd : ∀ k : ℕ,
      ∫ path, survivalIntegral (discountSeq k) (ContinuousPath.exitTime Qn path)
          ∂(K (omega, x)) ≤ Cw := by
    intro k
    have hlam := discountSeq_pos k
    have hN : ∀ N : ℕ,
        ∫ path, survivalIntegral (discountSeq k) (ContinuousPath.exitTime Qn path)
            ∂(KN N (omega, x)) ≤ Cw := by
      intro N
      haveI := hKN N
      have hint := hgint (discountSeq k) hlam (KN N (omega, x)) inferInstance
      have hofReal : ENNReal.ofReal
          (∫ path, survivalIntegral (discountSeq k)
            (ContinuousPath.exitTime Qn path) ∂(KN N (omega, x)))
          = ∫⁻ path, ENNReal.ofReal (survivalIntegral (discountSeq k)
              (ContinuousPath.exitTime Qn path)) ∂(KN N (omega, x)) := by
        refine ofReal_integral_eq_lintegral_ofReal hint ?_
        filter_upwards with path
        exact survivalIntegral_nonneg _ _
      have hle : ∫⁻ path, ENNReal.ofReal (survivalIntegral (discountSeq k)
            (ContinuousPath.exitTime Qn path)) ∂(KN N (omega, x))
          ≤ ENNReal.ofReal Cw := by
        refine le_trans (lintegral_mono fun path => ?_) (hCwb N x hxQ)
        exact ofReal_survivalIntegral_le hlam.le _
      have hbd : ENNReal.ofReal
          (∫ path, survivalIntegral (discountSeq k)
            (ContinuousPath.exitTime Qn path) ∂(KN N (omega, x)))
          ≤ ENNReal.ofReal Cw := by
        rw [hofReal]
        exact hle
      exact (ENNReal.ofReal_le_ofReal_iff hCw0).mp hbd
    have hconv := hr n (discountSeq k) hlam x hxQ
    rw [← hQn] at hconv
    simp only [hinner] at hconv
    exact le_of_tendsto hconv (Filter.Eventually.of_forall hN)
  -- the exit time is the supremum of the discounted survival integrals
  have hkey : ∫⁻ path, ContinuousPath.exitTime Qn path ∂(K (omega, x))
      ≤ ENNReal.ofReal Cw := by
    have hpt : (fun path : DiffusionPath d => ContinuousPath.exitTime Qn path)
        = fun path => ⨆ k : ℕ, ENNReal.ofReal
          (survivalIntegral (discountSeq k) (ContinuousPath.exitTime Qn path)) := by
      funext path
      exact (iSup_ofReal_survivalIntegral _).symm
    rw [hpt, lintegral_iSup
      (fun k => ((hgmeas (discountSeq k) (discountSeq_pos k)).ennreal_ofReal))
      (fun k l hkl path => ENNReal.ofReal_le_ofReal
        (monotone_survivalIntegral _ hkl))]
    refine iSup_le fun k => ?_
    have hlam := discountSeq_pos k
    haveI : IsProbabilityMeasure (K (omega, x)) := hK.isProbabilityMeasure _
    have hint := hgint (discountSeq k) hlam (K (omega, x)) inferInstance
    have hofReal : ENNReal.ofReal
        (∫ path, survivalIntegral (discountSeq k)
          (ContinuousPath.exitTime Qn path) ∂(K (omega, x)))
        = ∫⁻ path, ENNReal.ofReal (survivalIntegral (discountSeq k)
            (ContinuousPath.exitTime Qn path)) ∂(K (omega, x)) := by
      refine ofReal_integral_eq_lintegral_ofReal hint ?_
      filter_upwards with path
      exact survivalIntegral_nonneg _ _
    rw [← hofReal]
    exact ENNReal.ofReal_le_ofReal (hlimbd k)
  exact le_trans (lintegral_mono fun path => exitTime_mono hUn path) hkey


end Paper
