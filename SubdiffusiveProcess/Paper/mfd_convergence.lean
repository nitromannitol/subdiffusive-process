module

public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.Main.InfraredPartialSum
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.CutoffSpeedDensity
public import SubdiffusiveProcess.Main.CutoffSpeedMeasure
public import SubdiffusiveProcess.Main.MeasuresConvergeLocally
public import SubdiffusiveProcess.Main.SemigroupSymmetric
public import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
public import SubdiffusiveProcess.Main.HasStrongMarkovRestart
public import SubdiffusiveProcess.Main.HasFiniteMeanExits
public import SubdiffusiveProcess.Main.PathLevyProkhorovDist
public import SubdiffusiveProcess.Main.PhysicalRescaledPath
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Main.DiffusionPath
public import SubdiffusiveProcess.Inputs.MarkovProcesses
public import MarkovProcess.Trajectory.StoppingLtTop
public import MarkovProcess.Path.ExitTime
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import SubdiffusiveProcess.Vocab.Ahom
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.Metrizable.ContinuousMap
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import SubdiffusiveProcess.Paper.annealed_kernel_convergence
public import SubdiffusiveProcess.Paper.Support.FiniteMeanExitSuppliers
public import SubdiffusiveProcess.Paper.cube_exhaustion
public import SubdiffusiveProcess.Paper.finiteDimensional_cutoff
public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.in_cutoff_start_continuity
public import SubdiffusiveProcess.Paper.in_prescribed_moments
public import SubdiffusiveProcess.Paper.in_timescale
public import SubdiffusiveProcess.Paper.lem_infrared
public import SubdiffusiveProcess.Paper.lem_killing
public import SubdiffusiveProcess.Paper.limit_kernel
public import SubdiffusiveProcess.Paper.physical_rescaling
public import SubdiffusiveProcess.Paper.prop_as_quenched
public import SubdiffusiveProcess.Paper.prop_chaos_growth
public import SubdiffusiveProcess.Paper.Support.LimitPropertiesSuppliers
public import SubdiffusiveProcess.Paper.prop_quenched_convergence
public import SubdiffusiveProcess.Paper.torsion_bound
public import SubdiffusiveProcess.Paper.cor_as_resolvent
public import SubdiffusiveProcess.Paper.in_stopped_passage
public import SubdiffusiveProcess.Paper.determining_functional_convergence
public import SubdiffusiveProcess.Paper.tight_whole_space_resolvent_limit
public import SubdiffusiveProcess.Paper.limiting_local_energy
public import SubdiffusiveProcess.Paper.sum_errors_baseline_input
public import SubdiffusiveProcess.Paper.speed_trace_completion
public import SubdiffusiveProcess.Paper.tight_prop
public import SubdiffusiveProcess.Paper.tight_fixed_cutoff
public import SubdiffusiveProcess.Paper.cutoff_lifetime_package
public import SubdiffusiveProcess.MultiplicativeChaos.SpeedBasic
public import SubdiffusiveProcess.MultiplicativeChaos.TimeMarginal
public import SubdiffusiveProcess.Probability.InfraredCharacterizationExistence
public import SubdiffusiveProcess.Geometry.UpstreamCube

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The reindexing of the physical layers used by `physical_rescaling` (copied from the
`lem_crossing` file so that the main theorem no longer imports the crossing estimate). -/
def aux_mfd_convergence_sigma {d : ℕ} (N : ℕ) (omega : BilateralField d) : BilateralField d :=
  fun j => SubdiffusiveProcess.layerScaling d (-(N : ℤ)) (omega (j + (N : ℤ)))

theorem aux_mfd_convergence_sigma_apply {d : ℕ} (N : ℕ) (omega : BilateralField d) (j : ℤ)
    (x : SpatialCoordinates d) :
    aux_mfd_convergence_sigma N omega j x = omega (j + (N : ℤ)) (((3 : ℝ) ^ N) • x) := by
  simp only [aux_mfd_convergence_sigma, SubdiffusiveProcess.layerScaling,
    ContinuousMap.compRightContinuousMap_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk]
  congr 2
  rw [neg_neg, zpow_natCast]


-- ===== from MfdBase.lean =====


-- ===== from T1.lean =====
def aux_mfd_convergence_eps (d : ℕ) : ℝ := 1 / (16 * ((d : ℝ) + 2))

def aux_mfd_convergence_p (d : ℕ) : ℕ := 16 * (d + 2) * d + 1

theorem aux_mfd_convergence_eps_torsion (d : ℕ) :
    aux_mfd_convergence_eps d ∈ Set.Ioo (0 : ℝ) (1 / (8 * ((d : ℝ) + 2))) := by
  unfold aux_mfd_convergence_eps
  have hd : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  constructor
  · positivity
  · apply one_div_lt_one_div_of_lt (by positivity)
    linarith

theorem aux_mfd_convergence_eps_unit (d : ℕ) :
    aux_mfd_convergence_eps d ∈ Set.Ioo (0 : ℝ) 1 := by
  unfold aux_mfd_convergence_eps
  have hd : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  constructor
  · positivity
  · rw [div_lt_one (by positivity)]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith

theorem aux_mfd_convergence_p_spec (d : ℕ) :
    (d : ℝ) < (aux_mfd_convergence_p d : ℕ) * aux_mfd_convergence_eps d := by
  unfold aux_mfd_convergence_p aux_mfd_convergence_eps
  have hd : (0 : ℝ) < 16 * ((d : ℝ) + 2) := by positivity
  push_cast
  rw [mul_one_div, lt_div_iff₀ hd]
  nlinarith

def aux_mfd_convergence_Qtri (d : ℕ) (n : ℕ) : Homogenization.TriadicCube d := ⟨(n : ℤ), 0⟩

theorem aux_mfd_convergence_hr (d : ℕ) (n : ℕ) :
    0 < Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n) := by
  unfold Homogenization.cubeScaleFactor
  positivity

theorem aux_mfd_convergence_triadic (d : ℕ) (n : ℕ) :
    ∃ k : ℤ, Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n) = (3 : ℝ) ^ k :=
  ⟨(n : ℤ), rfl⟩

theorem aux_mfd_convergence_center (d : ℕ) (n : ℕ) :
    Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n) = 0 := by
  funext i
  simp [Homogenization.cubeCenter, aux_mfd_convergence_Qtri]

theorem aux_mfd_convergence_exhaust (d : ℕ) (U : Set (SpatialCoordinates d))
    (hU : Bornology.IsBounded U) :
    ∃ n : ℕ, U ⊆ (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
      (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
      (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)) := by
  obtain ⟨R, hR⟩ := hU.subset_ball (0 : SpatialCoordinates d)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * R) (by norm_num : (1 : ℝ) < 3)
  refine ⟨n, fun x hx => ?_⟩
  change x ∈ Metric.ball _ _
  rw [aux_mfd_convergence_center]
  have hx' := hR hx
  rw [Metric.mem_ball] at hx' ⊢
  have hsc : Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n) = (3 : ℝ) ^ n := by
    simp [Homogenization.cubeScaleFactor, aux_mfd_convergence_Qtri]
  rw [hsc]
  linarith

-- ===== from T2.lean =====
/-- Borel–Cantelli along a fast subsequence: locally uniform convergence in (outer)
probability gives a subsequence converging almost surely, locally uniformly. -/
theorem aux_mfd_convergence_ae_subseq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {d : ℕ}
    (D : ℕ → Ω → SpatialCoordinates d → ℝ)
    (hconv : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
        ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → μ {omega | ∃ x ∈ B, eps ≤ D N omega x} ≤
          ENNReal.ofReal rho) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∀ᵐ omega ∂μ, ∀ B : Set (SpatialCoordinates d), IsCompact B →
        ∀ eps : ℝ, 0 < eps → ∃ J0 : ℕ, ∀ j : ℕ, J0 ≤ j → ∀ x ∈ B,
          D (phi j) omega x < eps := by
  have hchoose : ∀ j : ℕ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      μ {omega | ∃ x ∈ Metric.closedBall (0 : SpatialCoordinates d) j,
        1 / ((j : ℝ) + 1) ≤ D N omega x} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ j) :=
    fun j => hconv _ (isCompact_closedBall _ _) _ (by positivity) _ (by positivity)
  choose N0 hN0 using hchoose
  let phi : ℕ → ℕ := fun j => j + ∑ i ∈ Finset.range (j + 1), N0 i
  have hphi : StrictMono phi := by
    refine strictMono_nat_of_lt_succ fun j => ?_
    simp only [phi, Finset.sum_range_succ _ (j + 1)]
    omega
  have hphiN : ∀ j, N0 j ≤ phi j := by
    intro j
    have : N0 j ≤ ∑ i ∈ Finset.range (j + 1), N0 i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (N0 i)) (Finset.self_mem_range_succ j)
    simp only [phi]
    omega
  refine ⟨phi, hphi, ?_⟩
  let s : ℕ → Set Ω := fun j => {omega | ∃ x ∈ Metric.closedBall (0 : SpatialCoordinates d) j,
    1 / ((j : ℝ) + 1) ≤ D (phi j) omega x}
  have hs : ∀ j, μ (s j) ≤ (2⁻¹ : ℝ≥0∞) ^ j := by
    intro j
    refine (hN0 j (phi j) (hphiN j)).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num),
      ENNReal.ofReal_ofNat]
  have hsum : (∑' j, μ (s j)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hs)
    rw [ENNReal.tsum_geometric, Ne, ENNReal.inv_eq_top]
    exact (tsub_pos_iff_lt.2 (ENNReal.inv_lt_one.2 (by norm_num))).ne'
  filter_upwards [ae_eventually_notMem hsum] with omega hom
  intro B hB eps heps
  obtain ⟨R, hR⟩ := hB.isBounded.subset_closedBall (0 : SpatialCoordinates d)
  obtain ⟨J1, hJ1⟩ := exists_nat_one_div_lt heps
  obtain ⟨J2, hJ2⟩ := exists_nat_ge R
  rw [eventually_atTop] at hom
  obtain ⟨J3, hJ3⟩ := hom
  refine ⟨max (max J1 J2) J3, fun j hj x hx => ?_⟩
  have hj1 : J1 ≤ j := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hj
  have hj2 : J2 ≤ j := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hj
  have hj3 : J3 ≤ j := le_trans (le_max_right _ _) hj
  have hnot := hJ3 j hj3
  by_contra hcon
  push Not at hcon
  apply hnot
  refine ⟨x, ?_, ?_⟩
  · have hxR := hR hx
    rw [Metric.mem_closedBall] at hxR ⊢
    have hJ2j : (J2 : ℝ) ≤ j := by exact_mod_cast hj2
    linarith
  · have hle : 1 / ((j : ℝ) + 1) ≤ 1 / ((J1 : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (J1 : ℝ) ≤ j := by exact_mod_cast hj1
      linarith
    linarith

/-- Almost sure uniform convergence of jointly measurable functions gives uniform
convergence in (outer) probability: the exceptional events are analytic. -/
theorem aux_mfd_convergence_prob_of_ae {Ω X : Type*}
    [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : ℕ → Ω × X → ℝ) (hF : ∀ N, Measurable (F N))
    (S : Set X) (hS : MeasurableSet S)
    (hae : ∀ᵐ omega ∂μ, ∀ eps : ℝ, 0 < eps → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
      ∀ x ∈ S, |F N (omega, x)| < eps) :
    ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
      μ {omega | ∃ x ∈ S, eps ≤ |F N (omega, x)|} ≤ ENNReal.ofReal rho := by
  intro eps heps rho hrho
  let E : ℕ → Set Ω := fun N => {omega | ∃ x ∈ S, eps ≤ |F N (omega, x)|}
  have hE : ∀ N, AnalyticSet (E N) := by
    intro N
    have hm : MeasurableSet {p : Ω × X | p.2 ∈ S ∧ eps ≤ |F N p|} :=
      (measurable_snd hS).inter
        (measurableSet_le measurable_const (continuous_abs.measurable.comp (hF N)))
    have heq : E N = Prod.fst '' {p : Ω × X | p.2 ∈ S ∧ eps ≤ |F N p|} := by
      ext omega
      constructor
      · rintro ⟨x, hx, hc⟩
        exact ⟨(omega, x), ⟨hx, hc⟩, rfl⟩
      · rintro ⟨⟨omega', x⟩, ⟨hx, hc⟩, rfl⟩
        exact ⟨x, hx, hc⟩
    rw [heq]
    exact hm.analyticSet.image_of_continuous continuous_fst
  let A : ℕ → Set Ω := fun n => ⋃ k : ℕ, E (n + k)
  have hA : ∀ n, NullMeasurableSet (A n) μ := fun n =>
    aux_determining_functional_convergence_analytic_nullMeasurable μ
      (AnalyticSet.iUnion fun k => hE (n + k))
  have hanti : Antitone A := by
    intro n m hnm omega homega
    simp only [A, Set.mem_iUnion] at homega ⊢
    obtain ⟨k, hmem⟩ := homega
    exact ⟨m - n + k, by rwa [show n + (m - n + k) = m + k by omega]⟩
  have hnull : μ (⋂ n, A n) = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 hae)
    intro omega homega
    simp only [Set.mem_ofPred_eq]
    intro hgood
    obtain ⟨N0, hN0⟩ := hgood eps heps
    have hmem := Set.mem_iInter.1 homega N0
    simp only [A, Set.mem_iUnion] at hmem
    obtain ⟨k, x, hx, hc⟩ := hmem
    exact absurd (hN0 (N0 + k) (Nat.le_add_right _ _) x hx) (not_lt.2 hc)
  have htend := tendsto_measure_iInter_atTop hA hanti ⟨0, measure_ne_top μ _⟩
  rw [hnull] at htend
  have hev := htend.eventually (eventually_lt_nhds (ENNReal.ofReal_pos.2 hrho))
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 hev
  refine ⟨n0, fun N hN => ?_⟩
  have hsub : E N ⊆ A n0 := by
    intro omega homega
    simp only [A, Set.mem_iUnion]
    exact ⟨N - n0, by rwa [show n0 + (N - n0) = N by omega]⟩
  exact (measure_mono hsub).trans (hn0 n0 le_rfl).le

/-- The finite-dimensional identification at one environment and one start gives
`path 0 = x` almost surely. -/
theorem aux_mfd_convergence_start
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (omega : BilateralField d) (x : SpatialCoordinates d)
    (h : ∀ I, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
      SubMarkovKernelSemigroup.finiteSetKernel P I x) :
    ∀ᵐ path ∂(K (omega, x)), path 0 = x := by
  have heval : ∀ I : Finset ℝ≥0,
      Measurable (ContinuousPath.finsetEvaluation (alpha := SpatialCoordinates d) I) := by
    intro I
    rw [measurable_pi_iff]
    intro s
    exact ContinuousPath.measurable_coordinateProcess (alpha := SpatialCoordinates d)
      (s : NNReal)
  have hmap : ∀ I : Finset ℝ≥0, (K (omega, x)).map (ContinuousPath.finsetEvaluation I) =
      SubMarkovKernelSemigroup.finiteSetKernel P I x := by
    intro I
    rw [← Kernel.map_apply _ (heval I)]
    exact h I
  have h0 := aux_determining_functional_convergence_marginal P x (K (omega, x)) hmap 0
  rw [P.kernel_zero, Kernel.id_apply] at h0
  have hmeas : Measurable (fun path : DiffusionPath d => path 0) :=
    ContinuousPath.measurable_coordinateProcess (alpha := SpatialCoordinates d) 0
  rw [ae_iff]
  have hset : {path : DiffusionPath d | ¬ path 0 = x} =
      (fun path : DiffusionPath d => path 0) ⁻¹' {x}ᶜ := rfl
  rw [hset, ← Measure.map_apply hmeas (measurableSet_singleton x).compl, h0]
  simp

/-- The killed occupation integral vanishes from a start outside the domain. -/
theorem aux_mfd_convergence_occ_zero {d : ℕ} (κ : Measure (DiffusionPath d))
    (U : Set (SpatialCoordinates d)) (x : SpatialCoordinates d) (hx : x ∉ U)
    (hstart : ∀ᵐ path ∂κ, path 0 = x) (lam : ℝ)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    ∫ path, (∫ t in Set.Ioi (0 : ℝ),
      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
        (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t) ∂κ = 0 := by
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hstart] with path hpath
  have hexit : ContinuousPath.exitTime U path = 0 := by
    have hle := ContinuousPath.exitTime_le_of_notMem U path 0 (by rw [hpath]; exact hx)
    simpa using hle
  have hset : {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path} = ∅ := by
    ext s
    simp [hexit]
  simp only [Pi.zero_apply]
  rw [hset, Set.indicator_empty]
  simp

-- ===== from T3.lean =====
/-- The finite-cutoff killed occupation resolvent on the `n`-th triadic cube. -/
def aux_mfd_convergence_RN {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (n N : ℕ) (omega : BilateralField d) (lam : ℝ)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d) : ℝ :=
  ∫ path, (∫ t in Set.Ioi (0 : ℝ),
    Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
      ((centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
        (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
        (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))) path}
      (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t) ∂(KN N (omega, x))

theorem aux_mfd_convergence_abs_sub_congr {a b c eps : ℝ} (e : c = b) (h : |a - c| < eps) :
    |a - b| < eps := by
  rw [← e]; exact h

theorem aux_mfd_convergence_abs_zero_lt {a b eps : ℝ} (ha : a = 0) (hb : b = 0) (h : 0 < eps) :
    |a - b| < eps := by
  rw [ha, hb, sub_zero, abs_zero]; exact h

theorem aux_mfd_convergence_killed
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (_hP : ∀ omega, (P omega).IsConservative)
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K)
    (hcontK : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        Continuous (fun x : SpatialCoordinates d =>
          jointPathProbabilityMeasure K hK omega x))
    (hlim : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
          SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x)
    (hconvP : ∀ B : Set (SpatialCoordinates d), IsCompact B →
        ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
          ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
            (chaosSampleLaw M).toMeasure
                {omega : BilateralField d | ∃ x ∈ B, eps ≤
                  pathLevyProkhorovDist
                    (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                    (jointPathProbabilityMeasure K hK omega x)} ≤
              ENNReal.ofReal rho)
    (Rlim : ℕ → BilateralField d → ℝ →
          BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          (∀ (n : ℕ) (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
              ContinuousOn (Rlim n omega lam f)
                (closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                  (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                  (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))) ∧
              ∀ x ∈ frontier (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                  (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                  (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)),
                Rlim n omega lam f x = 0) ∧
          (∀ (n : ℕ) (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
              ∀ delta : ℝ, 0 < delta → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
                ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                  (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                  (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)),
                  |(∫ path, (∫ t in Set.Ioi (0 : ℝ),
                      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                        ((centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                          (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                          (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))) path}
                        (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
                      ∂(KN N (omega, x))) - Rlim n omega lam f x| < delta) ∧
          (∀ (n : ℕ) (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ, ∀ N : ℕ,
              ContinuousOn (fun x => ∫ path, (∫ t in Set.Ioi (0 : ℝ),
                      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                        ((centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                          (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                          (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))) path}
                        (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
                      ∂(KN N (omega, x)))
                (closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                  (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                  (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))))) :
    (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (n : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∀ eps : ℝ, 0 < eps →
            ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
              ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                  (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                  (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)),
                |(∫ path, (∫ t in Set.Ioi (0 : ℝ),
                      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                        ((centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                          (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                          (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))) path}
                        (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
                    ∂(KN N (omega, x)))
                 - (∫ path, (∫ t in Set.Ioi (0 : ℝ),
                        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                          ((centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                            (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                            (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))) path}
                          (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
                      ∂(K (omega, x)))| < eps) ∧
    (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (n : ℕ) (lam : ℝ), 0 < lam →
        ∀ x ∈ (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                  (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                  (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)),
          Tendsto (fun N ↦ ∫ path, (∫ t in Set.Ioi (0 : ℝ),
                Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                  ((centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                    (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                    (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))) path}
                  (fun s => Real.exp (-lam * s) * (1 : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (path (Real.toNNReal s))) t)
              ∂(KN N (omega, x)))
            atTop
            (nhds (∫ path, (∫ t in Set.Ioi (0 : ℝ),
                  Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                    ((centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                      (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                      (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))) path}
                    (fun s => Real.exp (-lam * s) * (1 : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (path (Real.toNNReal s))) t)
                ∂(K (omega, x))))) := by
  have hsub := aux_mfd_convergence_ae_subseq (chaosSampleLaw M).toMeasure
    (fun N omega x => pathLevyProkhorovDist
      (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
      (jointPathProbabilityMeasure K hK omega x)) hconvP
  rcases hsub with ⟨phi, hphi, hphiae⟩
  have hin' := hin
  unfold in_crossing at hin'
  have hfront : ∀ n : ℕ, ∀ x ∈ frontier (centeredCube
      (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
      (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
      (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)),
      x ∉ (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
        (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
        (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)) := by
    intro n x hx
    rw [(centeredCube _ _ _).isOpen.frontier_eq] at hx
    exact hx.2
  have hRN0 : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ (n N : ℕ) (lam : ℝ)
      (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ),
      ∀ x ∈ frontier (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
        (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
        (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)),
      aux_mfd_convergence_RN KN n N omega lam f x = 0 := by
    filter_upwards [hin'.2.2] with omega hI
    intro n N lam f x hx
    exact aux_mfd_convergence_occ_zero _ _ x (hfront n x hx)
      (aux_mfd_convergence_start (KN N) (PN N omega) omega x (fun I => hI N I x)) lam f
  have hK0 : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ (n : ℕ) (lam : ℝ)
      (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ),
      ∀ x ∈ frontier (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
        (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
        (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)),
      aux_mfd_convergence_RN (fun _ => K) n 0 omega lam f x = 0 := by
    filter_upwards [hlim] with omega hI
    intro n lam f x hx
    exact aux_mfd_convergence_occ_zero _ _ x (hfront n x hx)
      (aux_mfd_convergence_start K (P omega) omega x (fun I => hI I x)) lam f
  have hbound : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (n : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ContinuousOn (Rlim n omega lam f)
            (closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
              (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
              (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))) ∧
          (∀ x ∈ frontier (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
              (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
              (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)),
            Rlim n omega lam f x = 0) ∧
          ∀ N : ℕ, ContinuousOn (aux_mfd_convergence_RN KN n N omega lam f)
            (closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
              (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
              (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))) ∧
            (∀ x ∈ frontier (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
              (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
              (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)),
              aux_mfd_convergence_RN KN n N omega lam f x = 0) := by
    filter_upwards [hRae, hRN0] with omega h1 h2
    intro n lam hlam f
    exact ⟨(h1.1 n lam hlam f).1, (h1.1 n lam hlam f).2,
      fun N => ⟨h1.2.2 n lam hlam f N, fun x hx => h2 n N lam f x hx⟩⟩
  have hpass := in_stopped_passage hd M H hH PN KN hKN K hK hin phi hphi hphiae hcontK
    (fun n => Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
    (fun n => Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
    (aux_mfd_convergence_hr d) (aux_mfd_convergence_RN KN) Rlim
    (fun _ _ _ _ _ _ => rfl) (hRae.mono fun omega h => h.2.1) hbound
  have hrespt : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (n : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ x ∈ (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
            (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
            (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)),
          Tendsto (fun N => aux_mfd_convergence_RN KN n N omega lam f x) atTop
            (nhds (Rlim n omega lam f x)) := by
    filter_upwards [hRae] with omega h
    intro n lam hlam f x hx
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N0, hN0⟩ := h.2.1 n lam hlam f ε hε
    exact ⟨N0, fun N hN => by rw [Real.dist_eq]; exact hN0 N hN x (subset_closure hx)⟩
  have hkill := lem_killing hd M H hH PN KN hKN K hK hin
    (fun n => Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
    (fun n => Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
    (aux_mfd_convergence_hr d) (aux_mfd_convergence_RN KN) Rlim
    (fun _ _ _ _ _ _ => rfl) hrespt hpass
  refine ⟨?_, ?_⟩
  · filter_upwards [hRae, hkill, hRN0, hK0] with omega h1 h2 h3 h4
    intro n lam hlam f eps heps
    obtain ⟨N0, hN0⟩ := h1.2.1 n lam hlam f eps heps
    refine ⟨N0, fun N hN x hx => ?_⟩
    by_cases hxQ : x ∈ (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
        (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
        (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))
    · have e := h2 n lam hlam f x hxQ
      have h5 := hN0 N hN x hx
      exact aux_mfd_convergence_abs_sub_congr e h5
    · have hxF : x ∈ frontier (centeredCube (Homogenization.cubeCenter
          (aux_mfd_convergence_Qtri d n))
          (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
          (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)) := by
        rw [(centeredCube _ _ _).isOpen.frontier_eq]
        exact ⟨hx, hxQ⟩
      have e3 := h3 n N lam f x hxF
      have e4 := h4 n lam f x hxF
      exact aux_mfd_convergence_abs_zero_lt e3 e4 heps
  · filter_upwards [hpass] with omega h
    intro n lam hlam x hx
    exact h n lam hlam 1 x hx

-- ===== from T4a.lean =====
/-- The discounted path functional `path ↦ ∫_0^∞ e^{-λ t} f(path t) dt`. -/
def aux_mfd_convergence_Phi {d : ℕ} (lam : ℝ)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (path : DiffusionPath d) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-lam * t) * f (path (Real.toNNReal t))

theorem aux_mfd_convergence_Phi_integrand_le {d : ℕ} (lam : ℝ)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (path : DiffusionPath d) (t : ℝ) :
    ‖Real.exp (-lam * t) * f (path (Real.toNNReal t))‖ ≤ ‖f‖ * Real.exp (-lam * t) := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
  exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm _) (Real.exp_pos _).le

theorem aux_mfd_convergence_Phi_abs_le {d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (path : DiffusionPath d) :
    |aux_mfd_convergence_Phi lam f path| ≤ ‖f‖ / lam := by
  have h := norm_integral_le_of_norm_le ((exp_neg_integrableOn_Ioi 0 hlam).const_mul ‖f‖)
    (Eventually.of_forall (aux_mfd_convergence_Phi_integrand_le lam f path))
  rw [integral_const_mul, aux_in_stopped_passage_exp_Ioi hlam, mul_zero, Real.exp_zero,
    ← div_eq_mul_one_div] at h
  exact h

theorem aux_mfd_convergence_Phi_continuous {d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    Continuous (aux_mfd_convergence_Phi (d := d) lam f) := by
  unfold aux_mfd_convergence_Phi
  refine continuous_of_dominated (bound := fun t => ‖f‖ * Real.exp (-lam * t)) ?_ ?_ ?_ ?_
  · intro path
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (f.continuous.comp (path.continuous.comp continuous_real_toNNReal))).aestronglyMeasurable
  · intro path
    exact Eventually.of_forall (aux_mfd_convergence_Phi_integrand_le lam f path)
  · exact (exp_neg_integrableOn_Ioi 0 hlam).const_mul ‖f‖
  · refine Eventually.of_forall fun t => ?_
    exact continuous_const.mul (f.continuous.comp (continuous_eval_const _))

/-- The discounted path functional as a bounded continuous function. -/
def aux_mfd_convergence_PhiB {d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    BoundedContinuousFunction (DiffusionPath d) ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨aux_mfd_convergence_Phi lam f,
      aux_mfd_convergence_Phi_continuous hlam f⟩ (2 * (‖f‖ / lam)) (by
    intro p q
    rw [Real.dist_eq]
    have h1 := aux_mfd_convergence_Phi_abs_le hlam f p
    have h2 := aux_mfd_convergence_Phi_abs_le hlam f q
    calc |aux_mfd_convergence_Phi lam f p - aux_mfd_convergence_Phi lam f q|
        ≤ |aux_mfd_convergence_Phi lam f p| + |aux_mfd_convergence_Phi lam f q| :=
          abs_sub _ _
      _ ≤ 2 * (‖f‖ / lam) := by linarith)

theorem aux_mfd_convergence_PhiB_apply {d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (path : DiffusionPath d) :
    aux_mfd_convergence_PhiB hlam f path = aux_mfd_convergence_Phi lam f path := rfl

/-- Continuity in the start of the discounted path integral, from continuity of the laws. -/
theorem aux_mfd_convergence_RW_continuous
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K) (omega : BilateralField d)
    (hc : Continuous (fun x : SpatialCoordinates d => jointPathProbabilityMeasure K hK omega x))
    {lam : ℝ} (hlam : 0 < lam) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    Continuous (fun x => ∫ path, (∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-lam * t) * f (path (Real.toNNReal t))) ∂(K (omega, x))) := by
  have h := ProbabilityMeasure.continuous_iff_forall_continuous_integral.1 hc
    (aux_mfd_convergence_PhiB hlam f)
  exact h

/-- The semigroup resolvent equals the discounted path integral, given the one-time
marginals. -/
theorem aux_mfd_convergence_resolvent_path {d : ℕ}
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (x : SpatialCoordinates d)
    (κ : Measure (DiffusionPath d)) [IsProbabilityMeasure κ]
    (hmarg : ∀ t : ℝ≥0, κ.map (fun path : DiffusionPath d => path t) = P t x)
    {lam : ℝ} (hlam : 0 < lam) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    P.kernelResolventReal lam f x =
      ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-lam * t) * f (path (Real.toNNReal t))) ∂κ := by
  have hev : ∀ t : ℝ≥0, Measurable (fun path : DiffusionPath d => path t) := fun t =>
    ContinuousPath.measurable_coordinateProcess (alpha := SpatialCoordinates d) t
  have hki : ∀ t : ℝ, kernelIntegral (P (Real.toNNReal t)) f x =
      ∫ path, f (path (Real.toNNReal t)) ∂κ := by
    intro t
    unfold kernelIntegral
    rw [← hmarg, integral_map (hev _).aemeasurable f.continuous.aestronglyMeasurable]
  unfold SubMarkovKernelSemigroup.kernelResolventReal
  simp_rw [hki, ← integral_const_mul]
  have hcont : Continuous (fun p : ℝ × DiffusionPath d =>
      Real.exp (-lam * p.1) * f (p.2 (Real.toNNReal p.1))) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_fst)).mul
      (f.continuous.comp (continuous_eval.comp
        (continuous_snd.prodMk (continuous_real_toNNReal.comp continuous_fst))))
  have hint : Integrable (Function.uncurry fun (t : ℝ) (path : DiffusionPath d) =>
      Real.exp (-lam * t) * f (path (Real.toNNReal t)))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod κ) := by
    have h1 : Integrable (fun t : ℝ => ‖f‖ * Real.exp (-lam * t))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (exp_neg_integrableOn_Ioi 0 hlam).const_mul ‖f‖
    refine Integrable.mono' (Integrable.comp_fst h1 κ) hcont.aestronglyMeasurable ?_
    refine Eventually.of_forall fun p => ?_
    exact aux_mfd_convergence_Phi_integrand_le lam f p.2 p.1
  exact integral_integral_swap hint

-- ===== from T4b.lean =====
/-- One-time marginals of a path kernel from its finite-dimensional identification. -/
theorem aux_mfd_convergence_marg
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (omega : BilateralField d) (x : SpatialCoordinates d)
    (h : ∀ I, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
      SubMarkovKernelSemigroup.finiteSetKernel P I x) (t : ℝ≥0) :
    (K (omega, x)).map (fun path : DiffusionPath d => path t) = P t x := by
  have heval : ∀ I : Finset ℝ≥0,
      Measurable (ContinuousPath.finsetEvaluation (alpha := SpatialCoordinates d) I) := by
    intro I
    rw [measurable_pi_iff]
    intro s
    exact ContinuousPath.measurable_coordinateProcess (alpha := SpatialCoordinates d)
      (s : NNReal)
  have hmap : ∀ I : Finset ℝ≥0, (K (omega, x)).map (ContinuousPath.finsetEvaluation I) =
      SubMarkovKernelSemigroup.finiteSetKernel P I x := by
    intro I
    rw [← Kernel.map_apply _ (heval I)]
    exact h I
  exact aux_determining_functional_convergence_marginal P x (K (omega, x)) hmap t

/-- Measurability of the killed occupation resolvent in `(omega, x)`. -/
theorem aux_mfd_convergence_RN_measurable
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (m N : ℕ) (lam : ℝ) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    Measurable (fun p : BilateralField d × SpatialCoordinates d =>
      aux_mfd_convergence_RN KN m N p.1 lam f p.2) := by
  have := hKN N
  have hocc := aux_in_stopped_passage_occ_measurable
    (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d m))
      (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d m))
      (aux_mfd_convergence_hr d m) : Set (SpatialCoordinates d))
    (centeredCube _ _ _).isOpen lam f
  exact ((hocc.comp measurable_snd).stronglyMeasurable.integral_kernel_prod_right'
    (κ := KN N)).measurable

/-- Compact containment of the exit from a large cube, from expectation tightness. -/
theorem aux_mfd_convergence_contain
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (μ : Measure (BilateralField d)) [IsProbabilityMeasure μ]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (htight : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ Kset : Set (DiffusionPath d), IsCompact Kset ∧
          ∀ N : ℕ, (∫⁻ omega, ⨆ x ∈ B, (KN N (omega, x)) Ksetᶜ ∂μ) ≤
            ENNReal.ofReal epsilon) :
    ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ T : ℝ, 0 ≤ T → ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
        ∃ m : ℕ, B ⊆ (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d m))
            (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d m))
            (aux_mfd_convergence_hr d m) : Set (SpatialCoordinates d)) ∧
          ∀ N : ℕ, μ {omega | ∃ x ∈ B, eps ≤
            ((KN N (omega, x)) {path | ContinuousPath.exitTime
              (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d m))
                (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d m))
                (aux_mfd_convergence_hr d m) : Set (SpatialCoordinates d)) path ≤
                  ENNReal.ofReal T}).toReal} ≤ ENNReal.ofReal rho := by
  intro B hB T hT eps heps rho hrho
  obtain ⟨Kset, hKc, hKint⟩ := htight B hB (rho * (eps / 2)) (by positivity)
  let Kpos : Set (SpatialCoordinates d) :=
    (fun p : DiffusionPath d × ℝ≥0 => p.1 p.2) '' (Kset ×ˢ Set.Icc 0 (Real.toNNReal T))
  have hKpos : IsCompact Kpos := (hKc.prod isCompact_Icc).image continuous_eval
  obtain ⟨m, hm⟩ := aux_mfd_convergence_exhaust d (B ∪ Kpos)
    (hB.isBounded.union hKpos.isBounded)
  refine ⟨m, fun x hx => hm (Or.inl hx), fun N => ?_⟩
  have hsub : ∀ path ∈ Kset, ¬ (ContinuousPath.exitTime
      (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d m))
        (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d m))
        (aux_mfd_convergence_hr d m) : Set (SpatialCoordinates d)) path ≤
          ENNReal.ofReal T) := by
    intro path hpath hle
    have hle' : ContinuousPath.exitTime
        (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d m))
          (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d m))
          (aux_mfd_convergence_hr d m) : Set (SpatialCoordinates d)) path ≤
        ((Real.toNNReal T : ℝ≥0) : ℝ≥0∞) := hle
    obtain ⟨s, hs⟩ := (ContinuousPath.exitTime_le_iff_mem_hitsSetBy _
      (centeredCube _ _ _).isOpen _ path).1 hle'
    apply hs
    exact hm (Or.inr ⟨(path, (s : ℝ≥0)), ⟨hpath, ⟨zero_le, s.property⟩⟩, rfl⟩)
  have hset : {omega | ∃ x ∈ B, eps ≤
      ((KN N (omega, x)) {path | ContinuousPath.exitTime
        (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d m))
          (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d m))
          (aux_mfd_convergence_hr d m) : Set (SpatialCoordinates d)) path ≤
            ENNReal.ofReal T}).toReal} ⊆
      {omega | ∃ x ∈ B, ENNReal.ofReal (eps / 2) < (KN N (omega, x)) Ksetᶜ} := by
    rintro omega ⟨x, hx, hle⟩
    refine ⟨x, hx, ?_⟩
    have := (hKN N).isProbabilityMeasure (omega, x)
    have hmono : (KN N (omega, x)) {path | ContinuousPath.exitTime
        (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d m))
          (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d m))
          (aux_mfd_convergence_hr d m) : Set (SpatialCoordinates d)) path ≤
            ENNReal.ofReal T} ≤ (KN N (omega, x)) Ksetᶜ :=
      measure_mono fun path hp hK' => hsub path hK' hp
    have h1 : ENNReal.ofReal eps ≤ (KN N (omega, x)) {path | ContinuousPath.exitTime
        (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d m))
          (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d m))
          (aux_mfd_convergence_hr d m) : Set (SpatialCoordinates d)) path ≤
            ENNReal.ofReal T} :=
      (ENNReal.ofReal_le_ofReal hle).trans (ENNReal.ofReal_toReal (measure_ne_top _ _)).le
    calc ENNReal.ofReal (eps / 2) < ENNReal.ofReal eps :=
          (ENNReal.ofReal_lt_ofReal_iff heps).2 (by linarith)
      _ ≤ _ := h1.trans hmono
  exact (measure_mono hset).trans (aux_determining_functional_convergence_tight_event μ (KN N)
    B hB Kset hKc (by positivity) (hKint N))

/-- The determining functional in the form of `determining_functional_convergence`
equals the one in `prop_quenched_convergence`. -/
theorem aux_mfd_convergence_psi_eq {d k : ℕ}
    (f : Fin k → BoundedContinuousFunction (SpatialCoordinates d) ℝ) (n : Fin k → ℕ) :
    (fun path : DiffusionPath d => ∫ s in {s : Fin k → ℝ | ∀ i, 0 < s i},
      Real.exp (-(∑ i : Fin k, (n i + 1 : ℝ) * s i)) *
        ∏ i : Fin k, f i (path (Real.toNNReal (∑ j ∈ Finset.Iic i, s j)))) =
    (fun path : DiffusionPath d =>
      ∫ s in Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)),
        Real.exp (-(∑ i : Fin k, ((n i + 1 : ℕ) : ℝ) * s i)) *
          ∏ i : Fin k, f i (path (Real.toNNReal
            (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j)))) := by
  funext path
  have hset : Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)) =
      {s : Fin k → ℝ | ∀ i, 0 < s i} := by
    ext s
    simp
  have hfil : ∀ i : Fin k, Finset.univ.filter (fun j : Fin k => j ≤ i) = Finset.Iic i := by
    intro i
    ext j
    simp
  rw [hset]
  simp only [hfil]
  push_cast
  rfl

-- ===== from T4c.lean =====
/-- The deterministic finite-cutoff resolvent Cauchy estimate `hdet` of
`determining_functional_convergence`, from the whole-space convergence in probability. -/
theorem aux_mfd_convergence_det_cauchy
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hfdd : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ N I x, (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
        SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x)
    (R : ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
        BilateralField d → C(SpatialCoordinates d, ℝ))
    (hR : ∀ lam : ℝ, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ B : Set (SpatialCoordinates d), IsCompact B →
          ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
            ∃ N0 : Nat, ∀ N, N0 ≤ N →
              (chaosSampleLaw M).toMeasure
                {omega | ∃ x ∈ B, eps ≤ |(∫ path, (∫ t in Set.Ioi (0 : ℝ),
                    Real.exp (-lam * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x))) -
                  R lam f omega x|} ≤ ENNReal.ofReal rho) :
    ∀ n : Nat, 0 < n →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
      ∃ N0 : Nat, ∀ N N' : Nat, N0 ≤ N → N0 ≤ N' →
        (chaosSampleLaw M).toMeasure
          {omega | ∃ x ∈ B, eps ≤ |(PN N omega).kernelResolventReal (n : ℝ) f x -
            (PN N' omega).kernelResolventReal (n : ℝ) f x|} ≤
            ENNReal.ofReal rho := by
  intro n hn f B hB eps heps rho hrho
  have hlam : (0 : ℝ) < n := Nat.cast_pos.2 hn
  obtain ⟨N0, hN0⟩ := hR n hlam f B hB (eps / 2) (by positivity) (rho / 2) (by positivity)
  refine ⟨N0, fun N N' hN hN' => ?_⟩
  set μ := (chaosSampleLaw M).toMeasure with hμ
  let Z : Set (BilateralField d) := {omega | ¬ ∀ N I x,
    (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
      SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x}
  have hZ : μ Z = 0 := ae_iff.1 hfdd
  let A : ℕ → Set (BilateralField d) := fun N => {omega | ∃ x ∈ B, eps / 2 ≤
    |(∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-(n : ℝ) * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x))) -
      R n f omega x|}
  have hsub : {omega | ∃ x ∈ B, eps ≤ |(PN N omega).kernelResolventReal (n : ℝ) f x -
      (PN N' omega).kernelResolventReal (n : ℝ) f x|} ⊆ (A N ∪ A N') ∪ Z := by
    rintro omega ⟨x, hx, hc⟩
    by_cases hω : omega ∈ Z
    · exact Or.inr hω
    · left
      have hI : ∀ N I x, (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
          SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x := not_not.1 hω
      have e : ∀ N, (PN N omega).kernelResolventReal (n : ℝ) f x =
          ∫ path, (∫ t in Set.Ioi (0 : ℝ),
            Real.exp (-(n : ℝ) * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x)) := by
        intro N
        have := (hKN N).isProbabilityMeasure (omega, x)
        exact aux_mfd_convergence_resolvent_path (PN N omega) x (KN N (omega, x))
          (aux_mfd_convergence_marg (KN N) (PN N omega) omega x (fun I => hI N I x)) hlam f
      rw [e N, e N'] at hc
      by_contra hcon
      simp only [Set.mem_union, A, Set.mem_ofPred_eq, not_or, not_exists, not_and,
        not_le] at hcon
      have h1 := hcon.1 x hx
      have h2 := hcon.2 x hx
      have h3 := abs_sub_le
        (∫ path, (∫ t in Set.Ioi (0 : ℝ),
            Real.exp (-(n : ℝ) * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x)))
        (R n f omega x)
        (∫ path, (∫ t in Set.Ioi (0 : ℝ),
            Real.exp (-(n : ℝ) * t) * f (path (Real.toNNReal t))) ∂(KN N' (omega, x)))
      rw [abs_sub_comm (R n f omega x)] at h3
      linarith
  calc μ {omega | ∃ x ∈ B, eps ≤ |(PN N omega).kernelResolventReal (n : ℝ) f x -
        (PN N' omega).kernelResolventReal (n : ℝ) f x|}
      ≤ μ ((A N ∪ A N') ∪ Z) := measure_mono hsub
    _ ≤ μ (A N) + μ (A N') + μ Z :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (rho / 2) + ENNReal.ofReal (rho / 2) + 0 := by
        rw [hZ]
        exact add_le_add (add_le_add (hN0 N hN) (hN0 N' hN')) le_rfl
    _ = ENNReal.ofReal rho := by
        rw [add_zero, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

/-- The Cauchy property of the integrated determining functionals, in the form of
`prop_quenched_convergence`, from their convergence in probability. -/
theorem aux_mfd_convergence_fun_cauchy
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (Psi : DiffusionPath d → ℝ) (U : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hU : ∀ B : Set (SpatialCoordinates d), IsCompact B →
        ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
        ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N →
          (chaosSampleLaw M).toMeasure
            {omega | ∃ x ∈ B,
              eps ≤ |(∫ path, Psi path ∂(KN N (omega, x))) - U omega x|} ≤
                ENNReal.ofReal rho) :
    ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N N', N0 ≤ N → N0 ≤ N' →
        (chaosSampleLaw M).toMeasure
            {omega : BilateralField d | ∃ x ∈ B, eps ≤
              |(∫ path, Psi path ∂(KN N (omega, x))) -
                (∫ path, Psi path ∂(KN N' (omega, x)))|} ≤ ENNReal.ofReal rho := by
  intro B hB eps heps rho hrho
  obtain ⟨N0, hN0⟩ := hU B hB (eps / 2) (by positivity) (rho / 2) (by positivity)
  refine ⟨N0, fun N N' hN hN' => ?_⟩
  let A : ℕ → Set (BilateralField d) := fun N => {omega | ∃ x ∈ B,
    eps / 2 ≤ |(∫ path, Psi path ∂(KN N (omega, x))) - U omega x|}
  have hsub : {omega : BilateralField d | ∃ x ∈ B, eps ≤
      |(∫ path, Psi path ∂(KN N (omega, x))) -
        (∫ path, Psi path ∂(KN N' (omega, x)))|} ⊆ A N ∪ A N' := by
    rintro omega ⟨x, hx, hc⟩
    by_contra hcon
    simp only [Set.mem_union, A, Set.mem_ofPred_eq, not_or, not_exists, not_and,
      not_le] at hcon
    have h1 := hcon.1 x hx
    have h2 := hcon.2 x hx
    have h3 := abs_sub_le (∫ path, Psi path ∂(KN N (omega, x))) (U omega x)
      (∫ path, Psi path ∂(KN N' (omega, x)))
    rw [abs_sub_comm (U omega x)] at h3
    linarith
  calc (chaosSampleLaw M).toMeasure {omega : BilateralField d | ∃ x ∈ B, eps ≤
        |(∫ path, Psi path ∂(KN N (omega, x))) -
          (∫ path, Psi path ∂(KN N' (omega, x)))|}
      ≤ (chaosSampleLaw M).toMeasure (A N ∪ A N') := measure_mono hsub
    _ ≤ (chaosSampleLaw M).toMeasure (A N) + (chaosSampleLaw M).toMeasure (A N') :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (rho / 2) + ENNReal.ofReal (rho / 2) :=
        add_le_add (hN0 N hN) (hN0 N' hN')
    _ = ENNReal.ofReal rho := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

theorem aux_mfd_convergence_path_cauchy
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (_hinput : aux_cutoff_lifetime_package_LocalInput M H KN)
    (hstart : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      Continuous (fun x : SpatialCoordinates d =>
        jointPathProbabilityMeasure (KN N) (hKN N) omega x))
    (htight : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ Kset : Set (DiffusionPath d), IsCompact Kset ∧
          ∀ N : ℕ,
            (∫⁻ omega, ⨆ x ∈ B, (KN N (omega, x)) Ksetᶜ
              ∂(chaosSampleLaw M).toMeasure) ≤ ENNReal.ofReal epsilon)
    (Rlim : ℕ → BilateralField d → ℝ →
          BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRmeas : ∀ (n : ℕ) (lam : ℝ), 0 < lam →
          ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
            Measurable (fun p : BilateralField d × SpatialCoordinates d =>
              Rlim n p.1 lam f p.2))
    (hRconv : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          (∀ (n : ℕ) (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
              ∀ delta : ℝ, 0 < delta → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
                ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                  (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                  (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)),
                  |(∫ path, (∫ t in Set.Ioi (0 : ℝ),
                      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                        ((centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                          (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                          (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))) path}
                        (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
                      ∂(KN N (omega, x))) - Rlim n omega lam f x| < delta)) :
    ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
        ∃ N0 : ℕ, ∀ N N' : ℕ, N0 ≤ N → N0 ≤ N' →
          (chaosSampleLaw M).toMeasure
              {omega : BilateralField d | ∃ x ∈ B, eps ≤
                pathLevyProkhorovDist
                  (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                  (jointPathProbabilityMeasure (KN N') (hKN N') omega x)} ≤
            ENNReal.ofReal rho := by
  classical
  have : PolishSpace (BilateralField d) := {}
  have hin' := hin
  unfold in_crossing at hin'
  have hcontWS : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          Continuous (fun x => ∫ path, (∫ t in Set.Ioi (0 : ℝ),
            Real.exp (-lam * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x))) := by
    filter_upwards [hstart] with omega h
    intro N lam hlam f
    exact aux_mfd_convergence_RW_continuous (KN N) (hKN N) omega (h N) hlam f
  have hkilledP : ∀ (m : ℕ) (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
        (chaosSampleLaw M).toMeasure
          {omega | ∃ x ∈ closure (centeredCube
              (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d m))
              (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d m))
              (aux_mfd_convergence_hr d m) : Set (SpatialCoordinates d)),
            eps ≤ |aux_mfd_convergence_RN KN m N omega lam f x - Rlim m omega lam f x|} ≤
          ENNReal.ofReal rho := by
    intro m lam hlam f
    refine aux_mfd_convergence_prob_of_ae (chaosSampleLaw M).toMeasure
      (fun N p => aux_mfd_convergence_RN KN m N p.1 lam f p.2 - Rlim m p.1 lam f p.2)
      (fun N => (aux_mfd_convergence_RN_measurable KN hKN m N lam f).sub
        (hRmeas m lam hlam f)) _ isClosed_closure.measurableSet ?_
    filter_upwards [hRconv] with omega h
    intro eps heps
    exact h m lam hlam f eps heps
  have hWS := _root_.SubdiffusiveProcess.Paper.tight_whole_space_resolvent_limit hd M H hH
    PN KN hKN hin
    (fun n => Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
    (fun n => Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
    (aux_mfd_convergence_hr d)
    (fun N omega lam f x => ∫ path, (∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-lam * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x)))
    (aux_mfd_convergence_RN KN) Rlim
    (fun m N omega x T => ((KN N (omega, x)) {path | ContinuousPath.exitTime
      (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d m))
        (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d m))
        (aux_mfd_convergence_hr d m) : Set (SpatialCoordinates d)) path ≤
          ENNReal.ofReal T}).toReal)
    (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    hcontWS hkilledP
    (aux_mfd_convergence_contain (chaosSampleLaw M).toMeasure KN hKN htight)
  rcases hWS with ⟨R, hR⟩
  have hdetD := aux_mfd_convergence_det_cauchy M PN KN hKN hin'.2.2 R
    (fun lam hlam f => (hR lam hlam f).2.2.1)
  have hcontD : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N n : ℕ), 0 < n → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        Continuous ((PN N omega).kernelResolventReal (n : ℝ) f) := by
    filter_upwards [hin'.2.2, hcontWS] with omega hI hc
    intro N n hn f
    have hlam : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have e : (PN N omega).kernelResolventReal (n : ℝ) f = fun x => ∫ path,
        (∫ t in Set.Ioi (0 : ℝ),
          Real.exp (-(n : ℝ) * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x)) := by
      funext x
      have := (hKN N).isProbabilityMeasure (omega, x)
      exact aux_mfd_convergence_resolvent_path (PN N omega) x (KN N (omega, x))
        (aux_mfd_convergence_marg (KN N) (PN N omega) omega x (fun I => hI N I x)) hlam f
    rw [e]
    exact hc N n hlam f
  have htightD : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∃ A : Set (DiffusionPath d), IsCompact A ∧
        ∀ N : Nat,
          (∫⁻ omega, ⨆ x : B, KN N (omega, x.val) Aᶜ ∂(chaosSampleLaw M).toMeasure) ≤
            ENNReal.ofReal eps := by
    intro B hB eps heps
    obtain ⟨A, hA, hAi⟩ := htight B hB eps heps
    refine ⟨A, hA, fun N => le_of_eq_of_le ?_ (hAi N)⟩
    congr 1
    funext omega
    rw [iSup_subtype']
  have hcauchyQ : ∀ (k : ℕ) (f : Fin k → BoundedContinuousFunction (SpatialCoordinates d) ℝ)
        (n : Fin k → ℕ) (B : Set (SpatialCoordinates d)), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N N', N0 ≤ N → N0 ≤ N' →
        (chaosSampleLaw M).toMeasure
            {omega : BilateralField d | ∃ x ∈ B, eps ≤
              |(∫ path, (∫ s in {s : Fin k → ℝ | ∀ i, 0 < s i},
                  Real.exp (-(∑ i : Fin k, (n i + 1 : ℝ) * s i)) *
                    ∏ i : Fin k, f i (path (Real.toNNReal (∑ j ∈ Finset.Iic i, s j))))
                  ∂(KN N (omega, x))) -
                (∫ path, (∫ s in {s : Fin k → ℝ | ∀ i, 0 < s i},
                  Real.exp (-(∑ i : Fin k, (n i + 1 : ℝ) * s i)) *
                    ∏ i : Fin k, f i (path (Real.toNNReal (∑ j ∈ Finset.Iic i, s j))))
                  ∂(KN N' (omega, x)))|} ≤ ENNReal.ofReal rho := by
    intro k f n B hB eps heps rho hrho
    rw [aux_mfd_convergence_psi_eq f n]
    have hDF := determining_functional_convergence M H PN KN hKN hin
      (fun N omega n f x => (PN N omega).kernelResolventReal (n : ℝ) f x)
      (fun _ _ _ _ _ => rfl) hcontD hdetD htightD k f (fun i => n i + 1)
      (fun i => Nat.succ_pos _)
      (fun path : DiffusionPath d =>
        ∫ s in Set.pi Set.univ (fun _ : Fin k => Set.Ioi (0 : ℝ)),
          Real.exp (-(∑ i : Fin k, ((n i + 1 : ℕ) : ℝ) * s i)) *
            ∏ i : Fin k, f i (path (Real.toNNReal
              (∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≤ i), s j))))
      (fun _ => rfl)
    rcases hDF with ⟨U, -, hU⟩
    exact aux_mfd_convergence_fun_cauchy M KN _ U hU B hB eps heps rho hrho
  exact prop_quenched_convergence hd M H hH PN KN hKN hin hcauchyQ htight

-- ===== from T5.lean =====
/-- The ordinary killed Poincaré inequality on a centred cube. -/
theorem aux_mfd_convergence_cube_poincare {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube z r hr),
      ‖(v : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) v‖ := by
  have : NeZero d := ⟨by omega⟩
  have : IsFiniteMeasure (volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    isFiniteMeasure_restrict.2 (measure_ball_lt_top (x := z) (r := r / 2)).ne
  have hgeom : Homogenization.IsOpenBoundedConvexDomain
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    refine ⟨(centeredCube z r hr).isOpen, ⟨dist z 0 + r + 1, by positivity, ?_⟩, ?_⟩
    · intro x hx i
      have hx' : dist x z < r / 2 := hx
      have hi : |x i| ≤ dist x 0 := by
        have := dist_le_pi_dist x 0 i
        simpa [Real.dist_eq] using this
      have htri := dist_triangle x z 0
      linarith
    · exact convex_ball z (r / 2)
  exact (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
    (centeredCube z r hr) hgeom).1

/-- Two continuous functions that agree a.e. on an open set `W` (w.r.t. the *restricted*
measure `volume.restrict W`) agree everywhere on `closure W`. -/
theorem aux_mfd_convergence_hcamp_glue {d : ℕ} {W : Set (SpatialCoordinates d)}
    (hW : IsOpen W) {f g : SpatialCoordinates d → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : f =ᵐ[volume.restrict W] g) : Set.EqOn f g (closure W) := by
  have hWmeas : MeasurableSet W := hW.measurableSet
  have hWeq : Set.EqOn f g W := by
    intro x hx
    by_contra hne
    set c : ℝ := |f x - g x| / 2 with hcdef
    have hcpos : 0 < |f x - g x| := abs_pos.mpr (sub_ne_zero.mpr hne)
    have hc : 0 < c := by rw [hcdef]; linarith
    have hcontabs : Continuous (fun w => |f w - g w|) := (hf.sub hg).abs
    have hWx : IsOpen (W ∩ (fun w => |f w - g w|) ⁻¹' (Set.Ioi c)) :=
      hW.inter (hcontabs.isOpen_preimage _ isOpen_Ioi)
    have hxW : x ∈ W ∩ (fun w => |f w - g w|) ⁻¹' (Set.Ioi c) := by
      refine ⟨hx, ?_⟩
      simp only [Set.mem_preimage, Set.mem_Ioi, hcdef]
      linarith
    have hWpos : 0 < volume (W ∩ (fun w => |f w - g w|) ⁻¹' (Set.Ioi c)) :=
      hWx.measure_pos volume ⟨x, hxW⟩
    have hbad : volume (W ∩ {w | f w ≠ g w}) = 0 := by
      have h1 : volume.restrict W {w | f w ≠ g w} = 0 := ae_iff.mp hfg
      rwa [Measure.restrict_apply' hWmeas, Set.inter_comm] at h1
    have hsub : W ∩ (fun w => |f w - g w|) ⁻¹' (Set.Ioi c) ⊆ W ∩ {w | f w ≠ g w} := by
      rintro w ⟨hw1, hw2⟩
      refine ⟨hw1, ?_⟩
      simp only [Set.mem_preimage, Set.mem_Ioi] at hw2
      intro heq
      rw [heq] at hw2
      simp at hw2
      linarith
    have : volume (W ∩ (fun w => |f w - g w|) ⁻¹' (Set.Ioi c)) ≤
        volume (W ∩ {w | f w ≠ g w}) := measure_mono hsub
    rw [hbad] at this
    exact absurd (le_antisymm this (zero_le)) (ne_of_gt hWpos)
  exact hWeq.closure hf hg

/-- The Euclidean coordinate distance is controlled by `Real.sqrt d` times the ambient
(sup-norm) `dist`. -/
theorem aux_mfd_convergence_hcamp_euclid_le {d : ℕ} (x y : SpatialCoordinates d) :
    Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt d * dist x y := by
  have hcoord : ∀ j : Fin d, (x j - y j) ^ 2 ≤ (dist x y) ^ 2 := by
    intro j
    have hj : dist (x j) (y j) ≤ dist x y := dist_le_pi_dist x y j
    rw [Real.dist_eq] at hj
    have h0 : 0 ≤ |x j - y j| := abs_nonneg _
    calc (x j - y j) ^ 2 = |x j - y j| ^ 2 := (sq_abs _).symm
      _ ≤ (dist x y) ^ 2 := pow_le_pow_left₀ h0 hj 2
  have hsum : (∑ j : Fin d, (x j - y j) ^ 2) ≤ (d : ℝ) * (dist x y) ^ 2 := by
    calc (∑ j : Fin d, (x j - y j) ^ 2) ≤ ∑ _j : Fin d, (dist x y) ^ 2 :=
          Finset.sum_le_sum fun j _ => hcoord j
      _ = (d : ℝ) * (dist x y) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt ((d : ℝ) * (dist x y) ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d * dist x y := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq dist_nonneg]

/-- Pointwise Hölder increment on a closed cube of side `r ≤ 1`, in terms of the ambient
`dist` (sup-norm) rather than the Euclidean coordinate distance baked into
`holderSeminorm`. -/
theorem aux_mfd_convergence_hcamp_holder_pt {d : ℕ} (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) {alpha : ℝ} (ha0 : 0 < alpha)
    {U : SpatialCoordinates d → ℝ}
    (hH : IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U)
    {K : ℝ} (hKle : holderSeminorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤ K)
    (hK0 : 0 ≤ K)
    {x y : SpatialCoordinates d}
    (hx : x ∈ (closedCube z r hr : Set (SpatialCoordinates d)))
    (hy : y ∈ (closedCube z r hr : Set (SpatialCoordinates d))) :
    |U x - U y| ≤ K * (Real.sqrt d) ^ alpha * dist x y ^ alpha := by
  by_cases hxy : x = y
  · subst hxy
    simp only [sub_self, abs_zero]
    positivity
  · set e := Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) with hedef
    have he0 : 0 < e := by
      rw [hedef, Real.sqrt_pos]
      obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
        by_contra h
        push Not at h
        exact hxy (funext h)
      have hjpos : 0 < (x j - y j) ^ 2 := by
        have hne : x j - y j ≠ 0 := sub_ne_zero.mpr hj
        positivity
      exact lt_of_lt_of_le hjpos
        (Finset.single_le_sum (f := fun j => (x j - y j) ^ 2) (fun j _ => sq_nonneg _)
          (Finset.mem_univ j))
    have hea : 0 < e ^ alpha := Real.rpow_pos_of_pos he0 _
    have hratio : |U x - U y| / e ^ alpha ≤
        holderSeminorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U :=
      le_csSup hH ⟨x, hx, y, hy, hxy, rfl⟩
    have h1 : |U x - U y| ≤
        holderSeminorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U * e ^ alpha :=
      (div_le_iff₀ hea).mp hratio
    have h2 : holderSeminorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U * e ^ alpha
        ≤ K * e ^ alpha := mul_le_mul_of_nonneg_right hKle hea.le
    have hele := aux_mfd_convergence_hcamp_euclid_le x y
    have he3 : e ^ alpha ≤ (Real.sqrt d * dist x y) ^ alpha :=
      Real.rpow_le_rpow he0.le hele ha0.le
    have he4 : (Real.sqrt d * dist x y) ^ alpha =
        (Real.sqrt d) ^ alpha * (dist x y) ^ alpha :=
      Real.mul_rpow (Real.sqrt_nonneg _) dist_nonneg
    calc |U x - U y| ≤
          holderSeminorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U * e ^ alpha :=
          h1
      _ ≤ K * e ^ alpha := h2
      _ ≤ K * (Real.sqrt d * dist x y) ^ alpha := mul_le_mul_of_nonneg_left he3 hK0
      _ = K * ((Real.sqrt d) ^ alpha * (dist x y) ^ alpha) := by rw [he4]
      _ = K * (Real.sqrt d) ^ alpha * dist x y ^ alpha := by ring


/-- Elementary 1-D interval overlap: a ball of radius `rad ≤ r` centred anywhere in the
open interval of half-width `r/2` around `c` meets that interval in a set of length at
least `rad`. -/
theorem aux_mfd_convergence_hcamp_overlap1d {c t r rad : ℝ}
    (hrad : 0 < rad) (hle : rad ≤ r) (ht0 : c - r / 2 < t) (ht1 : t < c + r / 2) :
    rad ≤ min (t + rad) (c + r / 2) - max (t - rad) (c - r / 2) := by
  rcases le_total (t + rad) (c + r / 2) with h1 | h1 <;>
    rcases le_total (t - rad) (c - r / 2) with h2 | h2 <;>
    simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h1, h2] <;>
    linarith

/-- `d`-dimensional density: the (sup-norm) ball of radius `rad ≤ 1` around an interior
point `x'` of the unit-side cube centred at `c` meets that cube in a set whose volume is
at least `2⁻ᵈ` times the volume of the whole ball. -/
theorem aux_mfd_convergence_hcamp_density {d : ℕ} (c x' : SpatialCoordinates d) {rad : ℝ}
    (hrad : 0 < rad) (hrad1 : rad ≤ 1)
    (hx' : x' ∈ (centeredCube c 1 one_pos : Set (SpatialCoordinates d))) :
    volume.real (Metric.ball x' rad) ≤
      (2 : ℝ) ^ d * volume.real (Metric.ball x' rad ∩
        (centeredCube c 1 one_pos : Set (SpatialCoordinates d))) := by
  have hballpi : Metric.ball x' rad = Set.pi Set.univ (fun i => Set.Ioo (x' i - rad) (x' i + rad)) := by
    rw [ball_pi x' hrad]
    congr 1
    funext i
    rw [Real.ball_eq_Ioo]
  have hcubepi : (centeredCube c 1 one_pos : Set (SpatialCoordinates d)) =
      Set.pi Set.univ (fun i => Set.Ioo (c i - 1 / 2) (c i + 1 / 2)) := by
    rw [centeredCube_eq_pi]
  have hinterpi : Metric.ball x' rad ∩ (centeredCube c 1 one_pos : Set (SpatialCoordinates d)) =
      Set.pi Set.univ (fun i => Set.Ioo (x' i - rad) (x' i + rad) ∩
        Set.Ioo (c i - 1 / 2) (c i + 1 / 2)) := by
    rw [hballpi, hcubepi]
    ext p
    simp only [Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, true_implies, forall_and]
  have hx'i : ∀ i, c i - 1 / 2 < x' i ∧ x' i < c i + 1 / 2 := by
    intro i
    have h := hx'
    rw [hcubepi] at h
    exact Set.mem_univ_pi.mp h i
  have hover : ∀ i, rad ≤ volume.real (Set.Ioo (x' i - rad) (x' i + rad) ∩
      Set.Ioo (c i - 1 / 2) (c i + 1 / 2)) := by
    intro i
    rw [Set.Ioo_inter_Ioo, Measure.real, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by
        have := aux_mfd_convergence_hcamp_overlap1d (c := c i) (t := x' i) (r := 1) (rad := rad)
          hrad hrad1 (hx'i i).1 (hx'i i).2
        linarith)]
    exact aux_mfd_convergence_hcamp_overlap1d (c := c i) (t := x' i) (r := 1) (rad := rad)
      hrad hrad1 (hx'i i).1 (hx'i i).2
  have hballvol : volume.real (Metric.ball x' rad) = (2 * rad) ^ d := by
    rw [Measure.real, hballpi, volume_pi_pi]
    have : ∀ i : Fin d, volume (Set.Ioo (x' i - rad) (x' i + rad)) =
        ENNReal.ofReal (2 * rad) := by
      intro i; rw [Real.volume_Ioo]; ring_nf
    rw [Finset.prod_congr rfl (fun i _ => this i)]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow (by linarith)]
    exact ENNReal.toReal_ofReal (by positivity)
  have hinterval : volume.real (Metric.ball x' rad ∩
      (centeredCube c 1 one_pos : Set (SpatialCoordinates d))) =
      ∏ i : Fin d, volume.real (Set.Ioo (x' i - rad) (x' i + rad) ∩
        Set.Ioo (c i - 1 / 2) (c i + 1 / 2)) := by
    rw [Measure.real, hinterpi, volume_pi_pi, ENNReal.toReal_prod]
    rfl
  have hprodle : (rad : ℝ) ^ d ≤ ∏ i : Fin d, volume.real (Set.Ioo (x' i - rad) (x' i + rad) ∩
      Set.Ioo (c i - 1 / 2) (c i + 1 / 2)) := by
    calc (rad : ℝ) ^ d = ∏ _i : Fin d, rad := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := Finset.prod_le_prod₀ (fun i _ => hrad.le) (fun i _ => hover i)
  rw [hballvol, hinterval]
  calc (2 * rad) ^ d = (2:ℝ) ^ d * rad ^ d := by ring
    _ ≤ (2:ℝ) ^ d * ∏ i : Fin d, volume.real (Set.Ioo (x' i - rad) (x' i + rad) ∩
        Set.Ioo (c i - 1 / 2) (c i + 1 / 2)) :=
      mul_le_mul_of_nonneg_left hprodle (by positivity)


/-- The mean minimizes the `L²` oscillation: for any competitor constant `c`, the
`L²(S)` distance to the mean of `u` over `S` is at most the `L²(S)` distance to `c`. -/
theorem aux_mfd_convergence_hcamp_variance {d : ℕ} {S : Set (SpatialCoordinates d)}
    (hSfin : volume S ≠ ⊤)
    {u : SpatialCoordinates d → ℝ} (hu : IntegrableOn u S volume)
    (hu2 : IntegrableOn (fun x => u x ^ 2) S volume) (c : ℝ) :
    (∫ y in S, (u y - (volume.real S)⁻¹ * ∫ w in S, u w) ^ 2) ≤ ∫ y in S, (u y - c) ^ 2 := by
  set m : ℝ := (volume.real S)⁻¹ * ∫ w in S, u w with hmdef
  by_cases hS0 : volume.real S = 0
  · have hSz : volume S = 0 := by
      rwa [Measure.real, ENNReal.toReal_eq_zero_iff, or_iff_left hSfin] at hS0
    have hRz : volume.restrict S = 0 := Measure.restrict_eq_zero.mpr hSz
    simp [hRz]
  · have hconstInt : ∀ k : ℝ, IntegrableOn (fun _ : SpatialCoordinates d => k) S volume :=
      fun k => integrableOn_const hSfin
    have hmuInt : IntegrableOn (fun y => m * u y) S volume := hu.const_mul m
    have hu_m_sq : IntegrableOn (fun y => (u y - m) ^ 2) S volume := by
      have hEq : (fun y => (u y - m) ^ 2) =
          (fun y => u y ^ 2 - 2 * m * u y + m ^ 2) := funext fun y => by ring
      rw [hEq]
      exact ((hu2.sub ((hu.const_mul (2 * m)))).add (hconstInt (m ^ 2)))
    have hu_c_sq : IntegrableOn (fun y => (u y - c) ^ 2) S volume := by
      have hEq : (fun y => (u y - c) ^ 2) =
          (fun y => u y ^ 2 - 2 * c * u y + c ^ 2) := funext fun y => by ring
      rw [hEq]
      exact ((hu2.sub ((hu.const_mul (2 * c)))).add (hconstInt (c ^ 2)))
    have hInt2u : IntegrableOn (fun y => 2 * u y - (c + m)) S volume :=
      (hu.const_mul 2).sub (hconstInt (c + m))
    have hdiffPt : ∀ y, (u y - c) ^ 2 - (u y - m) ^ 2 = (m - c) * (2 * u y - (c + m)) := by
      intro y; ring
    have hSumEq : (fun y => (u y - c) ^ 2) =
        (fun y => (u y - m) ^ 2 + (m - c) * (2 * u y - (c + m))) := by
      funext y; have := hdiffPt y; linarith
    have hInt3 : IntegrableOn (fun y => (m - c) * (2 * u y - (c + m))) S volume :=
      hInt2u.const_mul (m - c)
    have hsplit : (∫ y in S, (u y - c) ^ 2) =
        (∫ y in S, (u y - m) ^ 2) + ∫ y in S, (m - c) * (2 * u y - (c + m)) := by
      rw [hSumEq]
      exact integral_add hu_m_sq hInt3
    have hcrossVal : (∫ y in S, (m - c) * (2 * u y - (c + m))) = (m - c) ^ 2 * volume.real S := by
      rw [integral_const_mul]
      have hInt2uEq : (∫ y in S, (2 * u y - (c + m))) =
          2 * (∫ y in S, u y) - (c + m) * volume.real S := by
        rw [integral_sub (hu.const_mul 2) (hconstInt (c + m)), integral_const_mul,
          MeasureTheory.setIntegral_const]
        simp [Measure.real, smul_eq_mul, mul_comm]
      rw [hInt2uEq]
      have hmuEq : (∫ y in S, u y) = m * volume.real S := by
        rw [hmdef]; field_simp
      rw [hmuEq]; ring
    rw [hsplit, hcrossVal]
    have hnn : 0 ≤ (m - c) ^ 2 * volume.real S := by positivity
    linarith


/-- A locally integrable function with locally integrable square is `MemLp 2` on any
cube. -/
theorem aux_mfd_convergence_hcamp_memLp {d : ℕ} {u : SpatialCoordinates d → ℝ}
    (hLIu : LocallyIntegrable u volume) (hLIu2 : LocallyIntegrable (fun x => u x ^ 2) volume)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    MemLp u 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  have hIntClosed : IntegrableOn u (closedCube z r hr : Set (SpatialCoordinates d)) volume :=
    hLIu.integrableOn_isCompact (closedCube z r hr).isCompact
  have hInt2Closed : IntegrableOn (fun x => u x ^ 2) (closedCube z r hr : Set (SpatialCoordinates d))
      volume := hLIu2.integrableOn_isCompact (closedCube z r hr).isCompact
  have hsub : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (closedCube z r hr : Set (SpatialCoordinates d)) := centeredCube_subset_closedCube z hr
  have hInt2 : IntegrableOn (fun x => u x ^ 2) (centeredCube z r hr : Set (SpatialCoordinates d))
      volume := hInt2Closed.mono_set hsub
  have hMeas : AEStronglyMeasurable u (volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    (hIntClosed.mono_set hsub).aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq hMeas).mpr hInt2


/-- Transfer the whole-space (unintersected-ball) `L²` oscillation hypothesis to the
Campanato hypothesis on a side-`1` cube, at a centre `x'` inside the cube and any radius
`rad ≤ 1`: the mean-minimizing property (`variance`) plus the `2^d` density bound. -/
theorem aux_mfd_convergence_hcamp_osc1 {d : ℕ} {u : SpatialCoordinates d → ℝ} {A alpha : ℝ}
    (hLIu : LocallyIntegrable u volume) (hLIu2 : LocallyIntegrable (fun x => u x ^ 2) volume)
    (hosc : ∀ (x : SpatialCoordinates d) (rad : ℝ), 0 < rad → rad ≤ 1 →
      (∫ y in Metric.ball x rad, (u y - (volume.real (Metric.ball x rad))⁻¹ *
        ∫ w in Metric.ball x rad, u w) ^ 2) ≤
        A ^ 2 * volume.real (Metric.ball x rad) * rad ^ (2 * alpha))
    (c : SpatialCoordinates d) (x' : SpatialCoordinates d)
    (hx' : x' ∈ (centeredCube c 1 one_pos : Set (SpatialCoordinates d)))
    (rad : ℝ) (hrad : 0 < rad) (hrad1 : rad ≤ 1) :
    (∫ y in Metric.ball x' rad ∩ (centeredCube c 1 one_pos : Set (SpatialCoordinates d)),
        (u y - (volume.real (Metric.ball x' rad ∩
              (centeredCube c 1 one_pos : Set (SpatialCoordinates d))))⁻¹ *
            ∫ w in Metric.ball x' rad ∩ (centeredCube c 1 one_pos : Set (SpatialCoordinates d)),
              u w) ^ 2) ≤
      (A * (2 : ℝ) ^ ((d : ℝ) / 2)) ^ 2 * rad ^ (2 * alpha) *
        volume.real (Metric.ball x' rad ∩
          (centeredCube c 1 one_pos : Set (SpatialCoordinates d))) := by
  set B : Set (SpatialCoordinates d) := Metric.ball x' rad with hBdef
  set S : Set (SpatialCoordinates d) := B ∩ (centeredCube c 1 one_pos : Set (SpatialCoordinates d))
    with hSdef
  set mB : ℝ := (volume.real B)⁻¹ * ∫ w in B, u w with hmBdef
  have hBfin : volume B ≠ ⊤ := (measure_ball_lt_top).ne
  have hSfin : volume S ≠ ⊤ :=
    ne_top_of_le_ne_top hBfin (measure_mono (hSdef ▸ Set.inter_subset_left))
  have hIntBClosed : IntegrableOn u (Metric.closedBall x' rad) volume :=
    hLIu.integrableOn_isCompact (isCompact_closedBall x' rad)
  have hInt2BClosed : IntegrableOn (fun x => u x ^ 2) (Metric.closedBall x' rad) volume :=
    hLIu2.integrableOn_isCompact (isCompact_closedBall x' rad)
  have hBsub : B ⊆ Metric.closedBall x' rad := Metric.ball_subset_closedBall
  have hIntB : IntegrableOn u B volume := hIntBClosed.mono_set hBsub
  have hInt2B : IntegrableOn (fun x => u x ^ 2) B volume := hInt2BClosed.mono_set hBsub
  have hSsub : S ⊆ B := hSdef ▸ Set.inter_subset_left
  have hIntS : IntegrableOn u S volume := hIntB.mono_set hSsub
  have hInt2S : IntegrableOn (fun x => u x ^ 2) S volume := hInt2B.mono_set hSsub
  have hconstIntB : IntegrableOn (fun _ : SpatialCoordinates d => mB) B volume :=
    integrableOn_const hBfin
  have hsqIntB : IntegrableOn (fun y => (u y - mB) ^ 2) B volume := by
    have hEq : (fun y => (u y - mB) ^ 2) = (fun y => u y ^ 2 - 2 * mB * u y + mB ^ 2) :=
      funext fun y => by ring
    rw [hEq]
    exact ((hInt2B.sub (hIntB.const_mul (2 * mB))).add (integrableOn_const hBfin))
  -- Step 1: the mean over `S` minimizes the `L²(S)` distance among all constants,
  -- in particular the competitor `mB`.
  have hstep1 := aux_mfd_convergence_hcamp_variance (S := S) hSfin hIntS hInt2S mB
  -- Step 2: extending the domain of integration from `S` to `B ⊇ S` only adds a
  -- nonnegative amount (the integrand is a square).
  have hstep2 : (∫ y in S, (u y - mB) ^ 2) ≤ ∫ y in B, (u y - mB) ^ 2 :=
    setIntegral_mono_set hsqIntB
      (Filter.Eventually.of_forall fun y => sq_nonneg _) hSsub.eventuallyLE
  -- Step 3: the global hypothesis at the centre `x'`, radius `rad`.
  have hstep3 : (∫ y in B, (u y - mB) ^ 2) ≤ A ^ 2 * volume.real B * rad ^ (2 * alpha) :=
    hosc x' rad hrad hrad1
  -- Step 4: `2^d`-density of `S` inside `B`.
  have hstep4 : volume.real B ≤ (2 : ℝ) ^ d * volume.real S :=
    aux_mfd_convergence_hcamp_density c x' hrad hrad1 hx'
  have hA2nn : (0:ℝ) ≤ A ^ 2 := sq_nonneg _
  have hradnn : (0:ℝ) ≤ rad ^ (2 * alpha) := by positivity
  have hchain : (∫ y in S, (u y - (volume.real S)⁻¹ * ∫ w in S, u w) ^ 2) ≤
      A ^ 2 * ((2 : ℝ) ^ d * volume.real S) * rad ^ (2 * alpha) := by
    calc (∫ y in S, (u y - (volume.real S)⁻¹ * ∫ w in S, u w) ^ 2)
        ≤ ∫ y in S, (u y - mB) ^ 2 := hstep1
      _ ≤ ∫ y in B, (u y - mB) ^ 2 := hstep2
      _ ≤ A ^ 2 * volume.real B * rad ^ (2 * alpha) := hstep3
      _ ≤ A ^ 2 * ((2:ℝ) ^ d * volume.real S) * rad ^ (2 * alpha) := by
          have := mul_le_mul_of_nonneg_left hstep4 hA2nn
          exact mul_le_mul_of_nonneg_right this hradnn
  have hfinal : A ^ 2 * ((2:ℝ) ^ d * volume.real S) * rad ^ (2 * alpha) =
      (A * (2:ℝ) ^ ((d:ℝ)/2)) ^ 2 * rad ^ (2 * alpha) * volume.real S := by
    have h2d : ((2:ℝ) ^ ((d:ℝ)/2)) ^ 2 = (2:ℝ) ^ d := by
      rw [← Real.rpow_natCast (2:ℝ) d, ← Real.rpow_two, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rw [mul_pow]
    rw [h2d]
    ring
  rw [hfinal] at hchain
  exact hchain


/-- The Campanato representative on a single side-`1` cube centred at `c`, built from
`Cp` and the whole-space oscillation hypothesis, with the `2^{d/2}`-inflated seminorm
bound. -/
theorem aux_mfd_convergence_hcamp_cell {d : ℕ} (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    {alpha : ℝ} (ha0 : 0 < alpha) (ha1 : alpha < 1)
    {u : SpatialCoordinates d → ℝ} {A : ℝ} (hA0 : 0 ≤ A)
    (hLIu : LocallyIntegrable u volume) (hLIu2 : LocallyIntegrable (fun x => u x ^ 2) volume)
    (hosc : ∀ (x : SpatialCoordinates d) (rad : ℝ), 0 < rad → rad ≤ 1 →
      (∫ y in Metric.ball x rad, (u y - (volume.real (Metric.ball x rad))⁻¹ *
        ∫ w in Metric.ball x rad, u w) ^ 2) ≤
        A ^ 2 * volume.real (Metric.ball x rad) * rad ^ (2 * alpha))
    (c : SpatialCoordinates d) :
    ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
      U =ᵐ[volume.restrict (centeredCube c 1 one_pos : Set (SpatialCoordinates d))] u ∧
      IsHolderOn alpha (closedCube c 1 one_pos : Set (SpatialCoordinates d)) U ∧
      holderSeminorm alpha (closedCube c 1 one_pos : Set (SpatialCoordinates d)) U ≤
        Cp.C alpha * (A * (2 : ℝ) ^ ((d : ℝ) / 2)) := by
  have hMemLp := aux_mfd_convergence_hcamp_memLp hLIu hLIu2 c 1 one_pos
  set uk : DomainL2 (centeredCube c 1 one_pos) := hMemLp.toLp u with hukdef
  have hukAE : (uk : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube c 1 one_pos : Set (SpatialCoordinates d))] u := by
    rw [hukdef]; exact MemLp.coeFn_toLp hMemLp
  have hAK0 : (0:ℝ) ≤ A * (2:ℝ) ^ ((d:ℝ)/2) := by positivity
  have hoscHyp : ∀ x ∈ (centeredCube c 1 one_pos : Set (SpatialCoordinates d)),
      ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
      (∫ y in Metric.ball x rad ∩ (centeredCube c 1 one_pos : Set (SpatialCoordinates d)),
          (uk y - setAverage (Metric.ball x rad ∩
              (centeredCube c 1 one_pos : Set (SpatialCoordinates d))) uk) ^ 2
          ∂volume.restrict (centeredCube c 1 one_pos : Set (SpatialCoordinates d))) ≤
        (A * (2:ℝ) ^ ((d:ℝ)/2)) ^ 2 * rad ^ (2 * alpha) *
          volume.real (Metric.ball x rad ∩
            (centeredCube c 1 one_pos : Set (SpatialCoordinates d))) := by
    intro x hx rad hrad hrad1
    set S : Set (SpatialCoordinates d) :=
      Metric.ball x rad ∩ (centeredCube c 1 one_pos : Set (SpatialCoordinates d)) with hSdef
    have hSsub : S ⊆ (centeredCube c 1 one_pos : Set (SpatialCoordinates d)) :=
      hSdef ▸ Set.inter_subset_right
    have hukAES : (uk : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict S] u :=
      ae_restrict_of_ae_restrict_of_subset hSsub hukAE
    have hRestr : (volume.restrict (centeredCube c 1 one_pos : Set (SpatialCoordinates d))).restrict
        S = volume.restrict S := Measure.restrict_restrict_of_subset hSsub
    have hAvgEq : setAverage S uk = (volume.real S)⁻¹ * ∫ w in S, u w := by
      unfold setAverage
      rw [hRestr, integral_congr_ae hukAES]
    have hintEq : (∫ y in S, (uk y - setAverage S uk) ^ 2
        ∂volume.restrict (centeredCube c 1 one_pos : Set (SpatialCoordinates d))) =
        ∫ y in S, (u y - (volume.real S)⁻¹ * ∫ w in S, u w) ^ 2 := by
      rw [hRestr, hAvgEq]
      exact integral_congr_ae (hukAES.mono fun y hy => by simp only [hy])
    rw [hintEq]
    exact aux_mfd_convergence_hcamp_osc1 hLIu hLIu2 hosc c x hx rad hrad hrad1
  obtain ⟨U, hUcont, hUae, hUholder, hUsemi⟩ := Cp.holder_of_campanato alpha ha0 ha1 c 1 one_pos
    le_rfl uk (A * (2:ℝ) ^ ((d:ℝ)/2)) hAK0 hoscHyp
  exact ⟨U, hUcont, hUae.symm.trans hukAE, hUholder, hUsemi⟩


/-- If `x` lies in an open set `A` and in the closure of `B`, it lies in the closure of
`A ∩ B`. (No delicate boundary/tangency argument needed: `IsOpen.closure_inter` does the
work.) -/
theorem aux_mfd_convergence_hcamp_mem_closure_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} {x : X} (hA : IsOpen A) (hxA : x ∈ A) (hxB : x ∈ closure B) :
    x ∈ closure (A ∩ B) := by
  have hmem : x ∈ closure (B ∩ A) := (hA.closure_inter (s := B)) ⟨hxB, hxA⟩
  rwa [Set.inter_comm] at hmem


/-- Two Campanato representatives on side-`1` cells that both approximate the same `u`
agree pointwise at any point `x` that lies in the (open) first cell and in the closure
of the second. -/
theorem aux_mfd_convergence_hcamp_bridge {d : ℕ} {u : SpatialCoordinates d → ℝ}
    {k1 k2 : SpatialCoordinates d} {U1 U2 : SpatialCoordinates d → ℝ}
    (hU1cont : Continuous U1) (hU2cont : Continuous U2)
    (hU1ae : U1 =ᵐ[volume.restrict (centeredCube k1 1 one_pos : Set (SpatialCoordinates d))] u)
    (hU2ae : U2 =ᵐ[volume.restrict (centeredCube k2 1 one_pos : Set (SpatialCoordinates d))] u)
    {x : SpatialCoordinates d} (hx1 : x ∈ (centeredCube k1 1 one_pos : Set (SpatialCoordinates d)))
    (hx2 : x ∈ closure (centeredCube k2 1 one_pos : Set (SpatialCoordinates d))) :
    U1 x = U2 x := by
  have hW : IsOpen ((centeredCube k1 1 one_pos : Set (SpatialCoordinates d)) ∩
      (centeredCube k2 1 one_pos : Set (SpatialCoordinates d))) :=
    (centeredCube k1 1 one_pos).isOpen.inter (centeredCube k2 1 one_pos).isOpen
  have hxW : x ∈ closure ((centeredCube k1 1 one_pos : Set (SpatialCoordinates d)) ∩
      (centeredCube k2 1 one_pos : Set (SpatialCoordinates d))) :=
    aux_mfd_convergence_hcamp_mem_closure_inter (centeredCube k1 1 one_pos).isOpen hx1 hx2
  have h1 : U1 =ᵐ[volume.restrict ((centeredCube k1 1 one_pos : Set (SpatialCoordinates d)) ∩
      (centeredCube k2 1 one_pos : Set (SpatialCoordinates d)))] u :=
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left hU1ae
  have h2 : U2 =ᵐ[volume.restrict ((centeredCube k1 1 one_pos : Set (SpatialCoordinates d)) ∩
      (centeredCube k2 1 one_pos : Set (SpatialCoordinates d)))] u :=
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right hU2ae
  exact aux_mfd_convergence_hcamp_glue hW hU1cont hU2cont (h1.trans h2.symm) hxW


/-- Two points at sup-norm distance `≤ 1` both lie in the closure of the side-`1` cube
centred at their coordinatewise midpoint. -/
theorem aux_mfd_convergence_hcamp_midpoint_mem {d : ℕ} (x y : SpatialCoordinates d)
    (hxy : dist x y ≤ 1) :
    x ∈ closure (centeredCube (fun i => (x i + y i) / 2) 1 one_pos :
        Set (SpatialCoordinates d)) ∧
    y ∈ closure (centeredCube (fun i => (x i + y i) / 2) 1 one_pos :
        Set (SpatialCoordinates d)) := by
  set m : SpatialCoordinates d := fun i => (x i + y i) / 2 with hmdef
  have hclos : closure (centeredCube m 1 one_pos : Set (SpatialCoordinates d)) =
      (closedCube m 1 one_pos : Set (SpatialCoordinates d)) := by
    show closure (Metric.ball m (1 / 2)) = Metric.closedBall m (1 / 2)
    exact closure_ball m (by norm_num)
  have hxyi : ∀ i, |x i - y i| ≤ dist x y := by
    intro i
    have h := dist_le_pi_dist x y i
    rwa [Real.dist_eq] at h
  have hdxm : dist x m ≤ 1 / 2 := by
    rw [dist_pi_le_iff (by norm_num : (0:ℝ) ≤ 1/2)]
    intro i
    rw [Real.dist_eq]
    have hxi : x i - m i = (x i - y i) / 2 := by rw [hmdef]; ring
    rw [hxi, abs_div]
    have h2 : |(2:ℝ)| = 2 := by norm_num
    rw [h2]
    linarith [hxyi i]
  have hdym : dist y m ≤ 1 / 2 := by
    rw [dist_pi_le_iff (by norm_num : (0:ℝ) ≤ 1/2)]
    intro i
    rw [Real.dist_eq]
    have hyi : y i - m i = -(x i - y i) / 2 := by rw [hmdef]; ring
    rw [hyi, abs_div, abs_neg]
    have h2 : |(2:ℝ)| = 2 := by norm_num
    rw [h2]
    linarith [hxyi i]
  refine ⟨hclos ▸ ?_, hclos ▸ ?_⟩
  · exact Metric.mem_closedBall.mpr hdxm
  · exact Metric.mem_closedBall.mpr hdym


/-- The lattice index of `x` on the spacing-`1/3` grid (`Fin d → ℤ` is countable — this
is what keeps the assembled `v` a.e. equal to `u`: a countable union of null sets is
null, but a per-point-own-cell construction would not have this property since its
index set (all of `SpatialCoordinates d`) is uncountable). -/
def aux_mfd_convergence_hcamp_idx {d : ℕ} (x : SpatialCoordinates d) : Fin d → ℤ :=
  fun i => round (3 * x i)

/-- The real centre of lattice cell `k`. -/
def aux_mfd_convergence_hcamp_center {d : ℕ} (k : Fin d → ℤ) : SpatialCoordinates d :=
  fun i => ((k i : ℤ) : ℝ) / 3

/-- The "home" cell centre of `x`: rounding each coordinate of `3x` to the nearest
integer and dividing by `3` lands strictly inside the open side-`1` cell centred there
(margin `1/2 - 1/6 = 1/3 > 0`, so no boundary/tie case is an issue, unlike a
spacing-`1/2` grid). -/
def aux_mfd_convergence_hcamp_home {d : ℕ} (x : SpatialCoordinates d) : SpatialCoordinates d :=
  aux_mfd_convergence_hcamp_center (aux_mfd_convergence_hcamp_idx x)

theorem aux_mfd_convergence_hcamp_home_mem {d : ℕ} (x : SpatialCoordinates d) :
    x ∈ (centeredCube (aux_mfd_convergence_hcamp_home x) 1 one_pos :
        Set (SpatialCoordinates d)) := by
  show x ∈ Metric.ball (aux_mfd_convergence_hcamp_home x) (1 / 2)
  rw [Metric.mem_ball, dist_pi_lt_iff (by norm_num : (0:ℝ) < 1 / 2)]
  intro i
  rw [Real.dist_eq]
  have hr := abs_sub_round (3 * x i)
  have heq : x i - aux_mfd_convergence_hcamp_home x i =
      (3 * x i - ((round (3 * x i) : ℤ) : ℝ)) / 3 := by
    unfold aux_mfd_convergence_hcamp_home aux_mfd_convergence_hcamp_center
      aux_mfd_convergence_hcamp_idx
    ring
  rw [heq, abs_div]
  have h3 : |(3:ℝ)| = 3 := by norm_num
  rw [h3]
  linarith


/-- Assembling cellwise-a.e.-equal representatives along `aux_mfd_convergence_hcamp_idx`
gives a globally a.e.-equal function, because the index set `Fin d → ℤ` is countable. -/
theorem aux_mfd_convergence_hcamp_ae_of_cellwise {d : ℕ} {u : SpatialCoordinates d → ℝ}
    {Uf : (Fin d → ℤ) → SpatialCoordinates d → ℝ}
    (hUfae : ∀ k : Fin d → ℤ, Uf k =ᵐ[volume.restrict
        (centeredCube (aux_mfd_convergence_hcamp_center k) 1 one_pos :
          Set (SpatialCoordinates d))] u) :
    (fun x => Uf (aux_mfd_convergence_hcamp_idx x) x) =ᵐ[volume] u := by
  apply ae_iff.mpr
  have hsub : {x | ¬ Uf (aux_mfd_convergence_hcamp_idx x) x = u x} ⊆
      ⋃ k : Fin d → ℤ, {x | aux_mfd_convergence_hcamp_idx x = k} ∩
        {x | ¬ Uf k x = u x} := by
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨aux_mfd_convergence_hcamp_idx x, rfl, hx⟩
  have hnull : ∀ k : Fin d → ℤ, volume ({x | aux_mfd_convergence_hcamp_idx x = k} ∩
      {x | ¬ Uf k x = u x}) = 0 := by
    intro k
    have hsub2 : {x | aux_mfd_convergence_hcamp_idx x = k} ∩ {x | ¬ Uf k x = u x} ⊆
        (centeredCube (aux_mfd_convergence_hcamp_center k) 1 one_pos :
          Set (SpatialCoordinates d)) ∩ {x | ¬ Uf k x = u x} := by
      rintro x ⟨hx1, hx2⟩
      refine ⟨?_, hx2⟩
      have hhome := aux_mfd_convergence_hcamp_home_mem x
      unfold aux_mfd_convergence_hcamp_home at hhome
      rwa [hx1] at hhome
    have hnull2 : volume ((centeredCube (aux_mfd_convergence_hcamp_center k) 1 one_pos :
        Set (SpatialCoordinates d)) ∩ {x | ¬ Uf k x = u x}) = 0 := by
      have h := ae_iff.mp (hUfae k)
      rwa [Measure.restrict_apply' (centeredCube (aux_mfd_convergence_hcamp_center k) 1
        one_pos).isOpen.measurableSet, Set.inter_comm] at h
    exact measure_mono_null hsub2 hnull2
  exact measure_mono_null hsub (measure_iUnion_null hnull)


/-- Final assembly: Campanato's criterion in the whole-space, plain-function form
consumed by `torsion_bound` (the `aux_mfd_convergence_hcamp` estimate). -/
theorem aux_mfd_convergence_hcamp_final {d : ℕ} (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d) :
    ∀ alpha : ℝ, alpha ∈ Set.Ioo (0 : ℝ) 1 →
          ∃ C : ℝ, 0 < C ∧
            ∀ (z : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
              (u : SpatialCoordinates d → ℝ) (A : ℝ), 0 ≤ A →
              LocallyIntegrable u volume → LocallyIntegrable (fun x => (u x) ^ 2) volume →
              (∀ x ∉ (centeredCube z rQ hrQ : Set (SpatialCoordinates d)), u x = 0) →
              (∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
                (∫ y in Metric.ball x r,
                    (u y - (volume.real (Metric.ball x r))⁻¹ *
                      ∫ w in Metric.ball x r, u w) ^ 2) ≤
                  A ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * alpha)) →
              ∃ v : SpatialCoordinates d → ℝ,
                v =ᵐ[volume] u ∧
                (∀ x y : SpatialCoordinates d, dist x y ≤ 1 →
                  |v x - v y| ≤ C * A * dist x y ^ alpha) ∧
                ∀ x ∉ (centeredCube z rQ hrQ : Set (SpatialCoordinates d)), v x = 0 := by
  intro alpha halpha
  obtain ⟨ha0, ha1⟩ := halpha
  refine ⟨Cp.C alpha * (2 : ℝ) ^ ((d : ℝ) / 2) * (Real.sqrt d + 1) ^ alpha, ?_, ?_⟩
  · have hCpos := Cp.C_pos alpha ha0 ha1
    have hsd1 : (0:ℝ) < Real.sqrt d + 1 := by positivity
    have hrp : (0:ℝ) < (Real.sqrt d + 1) ^ alpha := Real.rpow_pos_of_pos hsd1 alpha
    positivity
  intro z rQ hrQ u A hA0 hLIu hLIu2 hvanish hosc
  have hcell : ∀ k : SpatialCoordinates d, ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
      U =ᵐ[volume.restrict (centeredCube k 1 one_pos : Set (SpatialCoordinates d))] u ∧
      IsHolderOn alpha (closedCube k 1 one_pos : Set (SpatialCoordinates d)) U ∧
      holderSeminorm alpha (closedCube k 1 one_pos : Set (SpatialCoordinates d)) U ≤
        Cp.C alpha * (A * (2 : ℝ) ^ ((d : ℝ) / 2)) :=
    fun k => aux_mfd_convergence_hcamp_cell Cp ha0 ha1 hA0 hLIu hLIu2 hosc k
  choose Uf hUfcont hUfae hUfholder hUfsemi using hcell
  set v : SpatialCoordinates d → ℝ :=
    fun x => Uf (aux_mfd_convergence_hcamp_center (aux_mfd_convergence_hcamp_idx x)) x with hvdef
  have hAK0 : (0:ℝ) ≤ A * (2:ℝ) ^ ((d:ℝ)/2) := by positivity
  refine ⟨v, ?_, ?_, ?_⟩
  · exact aux_mfd_convergence_hcamp_ae_of_cellwise
      (u := u) (Uf := fun k => Uf (aux_mfd_convergence_hcamp_center k))
      (fun k => hUfae (aux_mfd_convergence_hcamp_center k))
  · intro x y hxy
    obtain ⟨hxm, hym⟩ := aux_mfd_convergence_hcamp_midpoint_mem x y hxy
    set m : SpatialCoordinates d := fun i => (x i + y i) / 2 with hmdef
    have hvx : v x = Uf m x :=
      aux_mfd_convergence_hcamp_bridge (hUfcont _) (hUfcont m) (hUfae _) (hUfae m)
        (aux_mfd_convergence_hcamp_home_mem x) hxm
    have hvy : v y = Uf m y :=
      aux_mfd_convergence_hcamp_bridge (hUfcont _) (hUfcont m) (hUfae _) (hUfae m)
        (aux_mfd_convergence_hcamp_home_mem y) hym
    have hclos : closure (centeredCube m 1 one_pos : Set (SpatialCoordinates d)) =
        (closedCube m 1 one_pos : Set (SpatialCoordinates d)) := by
      show closure (Metric.ball m (1 / 2)) = Metric.closedBall m (1 / 2)
      exact closure_ball m (by norm_num)
    have hxclosed : x ∈ (closedCube m 1 one_pos : Set (SpatialCoordinates d)) := hclos ▸ hxm
    have hyclosed : y ∈ (closedCube m 1 one_pos : Set (SpatialCoordinates d)) := hclos ▸ hym
    have hCK0 : (0:ℝ) ≤ Cp.C alpha * (A * (2:ℝ) ^ ((d:ℝ)/2)) := by
      have := Cp.C_pos alpha ha0 ha1
      positivity
    have hpt := aux_mfd_convergence_hcamp_holder_pt m one_pos ha0
      (hUfholder m) (hUfsemi m) hCK0 hxclosed hyclosed
    rw [hvx, hvy]
    have hmono : (Real.sqrt d) ^ alpha ≤ (Real.sqrt d + 1) ^ alpha :=
      Real.rpow_le_rpow (Real.sqrt_nonneg _) (by linarith) ha0.le
    have hdxynn : (0:ℝ) ≤ dist x y ^ alpha := by positivity
    calc |Uf m x - Uf m y|
        ≤ Cp.C alpha * (A * (2:ℝ) ^ ((d:ℝ)/2)) * (Real.sqrt d) ^ alpha * dist x y ^ alpha := hpt
      _ ≤ Cp.C alpha * (A * (2:ℝ) ^ ((d:ℝ)/2)) * (Real.sqrt d + 1) ^ alpha * dist x y ^ alpha := by
          gcongr
      _ = Cp.C alpha * (2:ℝ) ^ ((d:ℝ)/2) * (Real.sqrt d + 1) ^ alpha * A * dist x y ^ alpha := by
          ring
  · intro x hx
    have hhome := aux_mfd_convergence_hcamp_home_mem x
    set k : SpatialCoordinates d := aux_mfd_convergence_hcamp_home x with hkdef
    -- `x ≠ z`, since `x` is outside the open cube but `z` is its centre.
    have hxz : x ≠ z := by
      rintro rfl
      exact hx (Metric.mem_ball_self (by positivity))
    have : Nontrivial (SpatialCoordinates d) := ⟨x, z, hxz⟩
    -- the interior of the closed support cube is exactly the open support cube.
    have hint : interior (closedCube z rQ hrQ : Set (SpatialCoordinates d)) =
        (centeredCube z rQ hrQ : Set (SpatialCoordinates d)) :=
      interior_closedBall' z (rQ / 2)
    have hxclB : x ∈ closure ((closedCube z rQ hrQ : Set (SpatialCoordinates d))ᶜ) := by
      rw [closure_compl, hint]
      exact hx
    set W : Set (SpatialCoordinates d) :=
      (centeredCube k 1 one_pos : Set (SpatialCoordinates d)) ∩
        (closedCube z rQ hrQ : Set (SpatialCoordinates d))ᶜ with hWdef
    have hWopen : IsOpen W :=
      (centeredCube k 1 one_pos).isOpen.inter (closedCube z rQ hrQ).isCompact.isClosed.isOpen_compl
    have hxW : x ∈ closure W :=
      aux_mfd_convergence_hcamp_mem_closure_inter (centeredCube k 1 one_pos).isOpen hhome hxclB
    have hsub : (closedCube z rQ hrQ : Set (SpatialCoordinates d))ᶜ ⊆
        (centeredCube z rQ hrQ : Set (SpatialCoordinates d))ᶜ :=
      Set.compl_subset_compl.mpr (centeredCube_subset_closedCube z hrQ)
    have huW : ∀ y ∈ W, u y = 0 := fun y hy => hvanish y (hsub hy.2)
    have hUf0 : Uf k =ᵐ[volume.restrict W] (fun _ : SpatialCoordinates d => (0:ℝ)) := by
      have h1 : Uf k =ᵐ[volume.restrict W] u :=
        ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left (hUfae k)
      refine h1.trans ?_
      apply ae_iff.mpr
      have hz0 : W ∩ {y | ¬ u y = (0:ℝ)} = ∅ := by
        ext y
        simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, Set.mem_ofPred_eq]
        rintro ⟨hyW, hyne⟩
        exact hyne (huW y hyW)
      rw [Measure.restrict_apply' hWopen.measurableSet, Set.inter_comm, hz0]
      exact measure_empty
    have hUfzero : Set.EqOn (Uf k) (fun _ => (0:ℝ)) (closure W) :=
      aux_mfd_convergence_hcamp_glue hWopen (hUfcont k) continuous_const hUf0
    exact hUfzero hxW


theorem aux_mfd_convergence_hcamp {d : ℕ} (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d) :
    ∀ alpha : ℝ, alpha ∈ Set.Ioo (0 : ℝ) 1 →
          ∃ C : ℝ, 0 < C ∧
            ∀ (z : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
              (u : SpatialCoordinates d → ℝ) (A : ℝ), 0 ≤ A →
              LocallyIntegrable u volume → LocallyIntegrable (fun x => (u x) ^ 2) volume →
              (∀ x ∉ (centeredCube z rQ hrQ : Set (SpatialCoordinates d)), u x = 0) →
              (∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
                (∫ y in Metric.ball x r,
                    (u y - (volume.real (Metric.ball x r))⁻¹ *
                      ∫ w in Metric.ball x r, u w) ^ 2) ≤
                  A ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * alpha)) →
              ∃ v : SpatialCoordinates d → ℝ,
                v =ᵐ[volume] u ∧
                (∀ x y : SpatialCoordinates d, dist x y ≤ 1 →
                  |v x - v y| ≤ C * A * dist x y ^ alpha) ∧
                ∀ x ∉ (centeredCube z rQ hrQ : Set (SpatialCoordinates d)), v x = 0 := by
  intro alpha halpha
  obtain ⟨ha0, ha1⟩ := halpha
  refine ⟨Cp.C alpha * (2 : ℝ) ^ ((d : ℝ) / 2) * (Real.sqrt d + 1) ^ alpha, ?_, ?_⟩
  · have hCpos := Cp.C_pos alpha ha0 ha1
    have hsd1 : (0:ℝ) < Real.sqrt d + 1 := by positivity
    have hrp : (0:ℝ) < (Real.sqrt d + 1) ^ alpha := Real.rpow_pos_of_pos hsd1 alpha
    positivity
  intro z rQ hrQ u A hA0 hLIu hLIu2 hvanish hosc
  have hcell : ∀ k : SpatialCoordinates d, ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
      U =ᵐ[volume.restrict (centeredCube k 1 one_pos : Set (SpatialCoordinates d))] u ∧
      IsHolderOn alpha (closedCube k 1 one_pos : Set (SpatialCoordinates d)) U ∧
      holderSeminorm alpha (closedCube k 1 one_pos : Set (SpatialCoordinates d)) U ≤
        Cp.C alpha * (A * (2 : ℝ) ^ ((d : ℝ) / 2)) :=
    fun k => aux_mfd_convergence_hcamp_cell Cp ha0 ha1 hA0 hLIu hLIu2 hosc k
  choose Uf hUfcont hUfae hUfholder hUfsemi using hcell
  set v : SpatialCoordinates d → ℝ :=
    fun x => Uf (aux_mfd_convergence_hcamp_center (aux_mfd_convergence_hcamp_idx x)) x with hvdef
  have hAK0 : (0:ℝ) ≤ A * (2:ℝ) ^ ((d:ℝ)/2) := by positivity
  refine ⟨v, ?_, ?_, ?_⟩
  · exact aux_mfd_convergence_hcamp_ae_of_cellwise
      (u := u) (Uf := fun k => Uf (aux_mfd_convergence_hcamp_center k))
      (fun k => hUfae (aux_mfd_convergence_hcamp_center k))
  · intro x y hxy
    obtain ⟨hxm, hym⟩ := aux_mfd_convergence_hcamp_midpoint_mem x y hxy
    set m : SpatialCoordinates d := fun i => (x i + y i) / 2 with hmdef
    have hvx : v x = Uf m x :=
      aux_mfd_convergence_hcamp_bridge (hUfcont _) (hUfcont m) (hUfae _) (hUfae m)
        (aux_mfd_convergence_hcamp_home_mem x) hxm
    have hvy : v y = Uf m y :=
      aux_mfd_convergence_hcamp_bridge (hUfcont _) (hUfcont m) (hUfae _) (hUfae m)
        (aux_mfd_convergence_hcamp_home_mem y) hym
    have hclos : closure (centeredCube m 1 one_pos : Set (SpatialCoordinates d)) =
        (closedCube m 1 one_pos : Set (SpatialCoordinates d)) := by
      show closure (Metric.ball m (1 / 2)) = Metric.closedBall m (1 / 2)
      exact closure_ball m (by norm_num)
    have hxclosed : x ∈ (closedCube m 1 one_pos : Set (SpatialCoordinates d)) := hclos ▸ hxm
    have hyclosed : y ∈ (closedCube m 1 one_pos : Set (SpatialCoordinates d)) := hclos ▸ hym
    have hCK0 : (0:ℝ) ≤ Cp.C alpha * (A * (2:ℝ) ^ ((d:ℝ)/2)) := by
      have := Cp.C_pos alpha ha0 ha1
      positivity
    have hpt := aux_mfd_convergence_hcamp_holder_pt m one_pos ha0
      (hUfholder m) (hUfsemi m) hCK0 hxclosed hyclosed
    rw [hvx, hvy]
    have hmono : (Real.sqrt d) ^ alpha ≤ (Real.sqrt d + 1) ^ alpha :=
      Real.rpow_le_rpow (Real.sqrt_nonneg _) (by linarith) ha0.le
    have hdxynn : (0:ℝ) ≤ dist x y ^ alpha := by positivity
    calc |Uf m x - Uf m y|
        ≤ Cp.C alpha * (A * (2:ℝ) ^ ((d:ℝ)/2)) * (Real.sqrt d) ^ alpha * dist x y ^ alpha := hpt
      _ ≤ Cp.C alpha * (A * (2:ℝ) ^ ((d:ℝ)/2)) * (Real.sqrt d + 1) ^ alpha * dist x y ^ alpha := by
          gcongr
      _ = Cp.C alpha * (2:ℝ) ^ ((d:ℝ)/2) * (Real.sqrt d + 1) ^ alpha * A * dist x y ^ alpha := by
          ring
  · intro x hx
    have hhome := aux_mfd_convergence_hcamp_home_mem x
    set k : SpatialCoordinates d := aux_mfd_convergence_hcamp_home x with hkdef
    -- `x ≠ z`, since `x` is outside the open cube but `z` is its centre.
    have hxz : x ≠ z := by
      rintro rfl
      exact hx (Metric.mem_ball_self (by positivity))
    have : Nontrivial (SpatialCoordinates d) := ⟨x, z, hxz⟩
    -- the interior of the closed support cube is exactly the open support cube.
    have hint : interior (closedCube z rQ hrQ : Set (SpatialCoordinates d)) =
        (centeredCube z rQ hrQ : Set (SpatialCoordinates d)) :=
      interior_closedBall' z (rQ / 2)
    have hxclB : x ∈ closure ((closedCube z rQ hrQ : Set (SpatialCoordinates d))ᶜ) := by
      rw [closure_compl, hint]
      exact hx
    set W : Set (SpatialCoordinates d) :=
      (centeredCube k 1 one_pos : Set (SpatialCoordinates d)) ∩
        (closedCube z rQ hrQ : Set (SpatialCoordinates d))ᶜ with hWdef
    have hWopen : IsOpen W :=
      (centeredCube k 1 one_pos).isOpen.inter (closedCube z rQ hrQ).isCompact.isClosed.isOpen_compl
    have hxW : x ∈ closure W :=
      aux_mfd_convergence_hcamp_mem_closure_inter (centeredCube k 1 one_pos).isOpen hhome hxclB
    have hsub : (closedCube z rQ hrQ : Set (SpatialCoordinates d))ᶜ ⊆
        (centeredCube z rQ hrQ : Set (SpatialCoordinates d))ᶜ :=
      Set.compl_subset_compl.mpr (centeredCube_subset_closedCube z hrQ)
    have huW : ∀ y ∈ W, u y = 0 := fun y hy => hvanish y (hsub hy.2)
    have hUf0 : Uf k =ᵐ[volume.restrict W] (fun _ : SpatialCoordinates d => (0:ℝ)) := by
      have h1 : Uf k =ᵐ[volume.restrict W] u :=
        ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left (hUfae k)
      refine h1.trans ?_
      apply ae_iff.mpr
      have hz0 : W ∩ {y | ¬ u y = (0:ℝ)} = ∅ := by
        ext y
        simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, Set.mem_ofPred_eq]
        rintro ⟨hyW, hyne⟩
        exact hyne (huW y hyW)
      rw [Measure.restrict_apply' hWopen.measurableSet, Set.inter_comm, hz0]
      exact measure_empty
    have hUfzero : Set.EqOn (Uf k) (fun _ => (0:ℝ)) (closure W) :=
      aux_mfd_convergence_hcamp_glue hWopen (hUfcont k) continuous_const hUf0
    exact hUfzero hxW


theorem aux_mfd_convergence_torsion
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (_Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (_S : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg), M.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
      ∀ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)),
        (∀ N, IsMarkovKernel (KN N)) → in_crossing M H PN KN →
        aux_cutoff_lifetime_package_LocalInput M H KN →
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ n : ℕ, ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ N : ℕ,
            ∀ x ∈ (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                  (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                  (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)),
              ∫⁻ path, ContinuousPath.exitTime
                (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                  (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                  (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)) path
                ∂(KN N (omega, x)) ≤ ENNReal.ofReal Cw := by
  have hTB := torsion_bound hd E _P _X _W _Cp D _S hES Step Dbase Interp (aux_mfd_convergence_eps d)
    (aux_mfd_convergence_eps_torsion d)
  rcases hTB with ⟨δ1, hδ1, hTB⟩
  have hCG := prop_chaos_growth (d := d) hd (aux_mfd_convergence_eps d)
    (aux_mfd_convergence_eps_unit d) (aux_mfd_convergence_p d) (aux_mfd_convergence_p_spec d)
  rcases hCG with ⟨δ2, hδ2, hCG⟩
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, ?_⟩
  intro M Rm Sreg It hle H hH PN KN hKN hin hinput
  have hLP := aux_cutoff_lifetime_package_local M H KN hinput
  rcases hLP with ⟨L, hL, hLlocal, hLstrong⟩
  have hcg := hCG M H hH (hle.trans (min_le_right _ _))
  rcases hcg with ⟨mu, -, -, hgr⟩
  have hgrowth : ∀ (R : Set (SpatialCoordinates d)), Bornology.IsBounded R →
      ∃ Kmu : BilateralField d → ℝ,
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, 0 ≤ Kmu omega ∧
          ∀ N x, x ∈ R → ∀ r : ℝ, 0 < r → r ≤ 1 →
            weightedChaosCutoff M H N omega (Metric.ball x r) ≤
              ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - aux_mfd_convergence_eps d)) := by
    intro R hR
    have h := hgr R hR
    rcases h with ⟨Kmu, -, hK⟩
    exact ⟨Kmu, hK.mono fun omega h => ⟨h.1, h.2.1⟩⟩
  exact hTB M Rm Sreg It (hle.trans (min_le_left _ _)) H hH PN KN hKN hin L hL hLlocal hLstrong
    (fun n => Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
    (fun n => Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
    (aux_mfd_convergence_hr d) (aux_mfd_convergence_exhaust d) (aux_mfd_convergence_triadic d)
    hgrowth (aux_mfd_convergence_hcamp _Cp)

-- ===== from T6a.lean =====
/-- Pointwise comparison of the fractional kernels of orders `a ≤ b` on a set of
diameter at most `Dm`. -/
theorem aux_mfd_convergence_frac_pt {A ρ Dm a b : ℝ} (hρ0 : 0 ≤ ρ) (hρD : ρ ≤ Dm)
    (hab : a ≤ b) (hA : ρ = 0 → A = 0) :
    ENNReal.ofReal A / ENNReal.ofReal ρ ^ a ≤
      ENNReal.ofReal Dm ^ (b - a) * (ENNReal.ofReal A / ENNReal.ofReal ρ ^ b) := by
  by_cases hρ : ρ = 0
  · rw [hA hρ, ENNReal.ofReal_zero, ENNReal.zero_div]
    exact zero_le
  · have hpos : 0 < ρ := lt_of_le_of_ne hρ0 (Ne.symm hρ)
    have hR0 : ENNReal.ofReal ρ ≠ 0 := (ENNReal.ofReal_pos.2 hpos).ne'
    have hRt : ENNReal.ofReal ρ ≠ ⊤ := ENNReal.ofReal_ne_top
    have hQ0 : ENNReal.ofReal ρ ^ (b - a) ≠ 0 := (ENNReal.rpow_pos
      (ENNReal.ofReal_pos.2 hpos) hRt).ne'
    have hQt : ENNReal.ofReal ρ ^ (b - a) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.2 hab) hRt
    have hsplit : ENNReal.ofReal ρ ^ b = ENNReal.ofReal ρ ^ a * ENNReal.ofReal ρ ^ (b - a) := by
      rw [← ENNReal.rpow_add _ _ hR0 hRt]
      congr 1
      ring
    calc ENNReal.ofReal A / ENNReal.ofReal ρ ^ a
        = ENNReal.ofReal A * ENNReal.ofReal ρ ^ (b - a) /
            (ENNReal.ofReal ρ ^ a * ENNReal.ofReal ρ ^ (b - a)) :=
          (ENNReal.mul_div_mul_right _ _ hQ0 hQt).symm
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal Dm ^ (b - a) /
            (ENNReal.ofReal ρ ^ a * ENNReal.ofReal ρ ^ (b - a)) :=
          ENNReal.div_le_div_right (mul_le_mul_right (ENNReal.rpow_le_rpow
            (ENNReal.ofReal_le_ofReal hρD) (sub_nonneg.2 hab)) _) _
      _ = ENNReal.ofReal Dm ^ (b - a) * (ENNReal.ofReal A / ENNReal.ofReal ρ ^ b) := by
          rw [← hsplit, mul_comm, mul_div_assoc]

/-- On a cube, a finite fractional seminorm of order `t` gives a finite seminorm of
every smaller order `s`. -/
theorem aux_mfd_convergence_seminorm_mono {d k : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s t : Set.Ioo (0 : ℝ) 1)
    (hst : (s : ℝ) ≤ t) (f : Fin k → DomainL2 (centeredCube z r hr))
    (h : cubeFractionalL2Seminorm hd z r hr t f < ⊤) :
    cubeFractionalL2Seminorm hd z r hr s f < ⊤ := by
  unfold cubeFractionalL2Seminorm at h ⊢
  set Q : Set (SpatialCoordinates d) := (centeredCube z r hr : Set (SpatialCoordinates d))
    with hQ
  have hQm : MeasurableSet Q := (centeredCube z r hr).isOpen.measurableSet
  have hvol0 : volume Q ≠ 0 := (Metric.measure_ball_pos volume z (half_pos hr)).ne'
  have hvolt : volume Q ≠ ⊤ := (measure_ball_lt_top (x := z) (r := r / 2)).ne
  set Dm : ℝ := Real.sqrt ((d : ℝ) * r ^ 2) with hDm
  set c : ℝ≥0∞ := ENNReal.ofReal Dm ^ (2 * (t : ℝ) - 2 * (s : ℝ)) with hc
  have hct : c ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top
  have hpt : ∀ x ∈ Q, ∀ y ∈ Q,
      ENNReal.ofReal (∑ i : Fin k, (f i x - f i y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (s : ℝ)) ≤
        c * (ENNReal.ofReal (∑ i : Fin k, (f i x - f i y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (t : ℝ))) := by
    intro x hx y hy
    have hxy : dist x y < r := by
      have h1 : dist x z < r / 2 := hx
      have h2 : dist y z < r / 2 := hy
      have := dist_triangle_right x y z
      linarith
    have hcoord : ∀ j : Fin d, (x j - y j) ^ 2 ≤ r ^ 2 := by
      intro j
      have hj : |x j - y j| ≤ dist x y := by
        have := dist_le_pi_dist x y j
        rwa [Real.dist_eq] at this
      have h0 : 0 ≤ |x j - y j| := abs_nonneg _
      calc (x j - y j) ^ 2 = |x j - y j| ^ 2 := (sq_abs _).symm
        _ ≤ r ^ 2 := pow_le_pow_left₀ h0 (hj.trans hxy.le) 2
    have hsum : ∑ j : Fin d, (x j - y j) ^ 2 ≤ (d : ℝ) * r ^ 2 := by
      calc ∑ j : Fin d, (x j - y j) ^ 2 ≤ ∑ _j : Fin d, r ^ 2 :=
            Finset.sum_le_sum fun j _ => hcoord j
        _ = (d : ℝ) * r ^ 2 := by simp
    have hexp : (d : ℝ) + 2 * (t : ℝ) - ((d : ℝ) + 2 * (s : ℝ)) =
        2 * (t : ℝ) - 2 * (s : ℝ) := by ring
    have := aux_mfd_convergence_frac_pt (A := ∑ i : Fin k, (f i x - f i y) ^ 2)
      (ρ := Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) (Dm := Dm)
      (a := (d : ℝ) + 2 * (s : ℝ)) (b := (d : ℝ) + 2 * (t : ℝ))
      (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hsum) (by linarith) (by
        intro h0
        rw [Real.sqrt_eq_zero (Finset.sum_nonneg fun j _ => sq_nonneg _)] at h0
        have hall : ∀ j ∈ Finset.univ, (x j - y j) ^ 2 = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).1 h0
        have hxy' : x = y := by
          funext j
          have := hall j (Finset.mem_univ j)
          have : x j - y j = 0 := by simpa using this
          linarith
        subst hxy'
        simp)
    rwa [hexp] at this
  have hinner : ∀ x ∈ Q,
      ∫⁻ y in Q, ENNReal.ofReal (∑ i : Fin k, (f i x - f i y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (s : ℝ)) ≤
        c * ∫⁻ y in Q, ENNReal.ofReal (∑ i : Fin k, (f i x - f i y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (t : ℝ)) := by
    intro x hx
    rw [← lintegral_const_mul' c _ hct]
    exact setLIntegral_mono' hQm fun y hy => hpt x hx y hy
  have hI : (∫⁻ x in Q, ∫⁻ y in Q, ENNReal.ofReal (∑ i : Fin k, (f i x - f i y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (s : ℝ))) ≤
        c * ∫⁻ x in Q, ∫⁻ y in Q, ENNReal.ofReal (∑ i : Fin k, (f i x - f i y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (t : ℝ)) := by
    rw [← lintegral_const_mul' c _ hct]
    exact setLIntegral_mono' hQm hinner
  have ht0 : ENNReal.ofReal (t : ℝ) / volume Q ≠ 0 :=
    ENNReal.div_ne_zero.2 ⟨(ENNReal.ofReal_pos.2 t.2.1).ne', hvolt⟩
  have hIt : (∫⁻ x in Q, ∫⁻ y in Q, ENNReal.ofReal (∑ i : Fin k, (f i x - f i y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (t : ℝ))) < ⊤ := by
    have h2 := (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).1 h
    rcases ENNReal.mul_lt_top_iff.1 h2 with h3 | h3 | h3
    · exact h3.2
    · exact absurd h3 ht0
    · rw [h3]; exact ENNReal.zero_lt_top
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  refine ENNReal.mul_ne_top (ENNReal.div_lt_top ENNReal.ofReal_ne_top hvol0).ne ?_
  exact (lt_of_le_of_lt hI (ENNReal.mul_lt_top hct.lt_top hIt)).ne

/-- A function with a Hölder modulus on a set is continuous on it. -/
theorem aux_mfd_convergence_holder_continuousOn {X : Type*} [PseudoMetricSpace X]
    (g : X → ℝ) (S : Set X) (K a : ℝ) (ha : 0 < a)
    (h : ∀ x ∈ S, ∀ y ∈ S, |g x - g y| ≤ K * dist x y ^ a) : ContinuousOn g S := by
  intro x hx
  have h1 : Tendsto (fun y => K * dist y x ^ a) (𝓝[S] x) (𝓝 (K * dist x x ^ a)) := by
    apply Tendsto.const_mul
    apply ((Real.continuousAt_rpow_const _ a (Or.inr ha.le)).tendsto).comp
    exact tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id.dist tendsto_const_nhds)
  rw [dist_self, Real.zero_rpow ha.ne', mul_zero] at h1
  rw [ContinuousWithinAt, ← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ h1
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [Real.norm_eq_abs]
  exact h y hy x hx

-- ===== from T6b.lean =====
/-- The limiting killed inverses on the triadic cube family (`limiting_local_energy`),
with their `H^{3/4}` domain clause. -/
theorem aux_mfd_convergence_G
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (hP : ∀ n : ℕ, ∃ K : ℝ≥0,
          ∀ v : killedSobolevGraph (centeredCube
              (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
              (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
              (aux_mfd_convergence_hr d n)),
            ‖(v : SobolevData (centeredCube
              (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
              (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
              (aux_mfd_convergence_hr d n))).1‖ ≤
              K * ‖subspaceGradient (killedSobolevGraph (centeredCube
                (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                (aux_mfd_convergence_hr d n))) v‖),
      ∃ G : (n : ℕ) → BilateralField d →
          (DomainL2 (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
              (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
              (aux_mfd_convergence_hr d n)) →L[ℝ]
            DomainL2 (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
              (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
              (aux_mfd_convergence_hr d n))),
        (∀ n : ℕ, Measurable (G n)) ∧
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ n : ℕ,
          (∀ f : DomainL2 (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
              (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
              (aux_mfd_convergence_hr d n)),
            Tendsto
              (fun N : ℕ =>
                (responseSolution (killedResponseSpace (Ω := centeredCube
                    (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                    (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                    (aux_mfd_convergence_hr d n)) (hP n))
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                      (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                      (aux_mfd_convergence_hr d n))
                    ((sobolevVolumeLoad f).comp
                      (killedResponseSpace (Ω := centeredCube
                        (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                        (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                        (aux_mfd_convergence_hr d n)) (hP n)).space.subtypeL)).val.1)
              atTop (𝓝 (G n omega f))) ∧
          (∀ u : DomainL2 (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
              (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
              (aux_mfd_convergence_hr d n)),
            limitFormEnergy (G n omega) u ≠ ⊤ →
            ∃ v : CubeFractionalL2 (k := 1) hd
                (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                (aux_mfd_convergence_hr d n) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
              v.val 0 = u) := by
  -- `HCUT`/`HUNIF` are RESULTS of this paper,
  -- not standing inputs of `mfd_convergence`: obtained here from `cor_as_resolvent`'s two supplier
  -- helpers, combined by `min` into this helper’s own `∃ delta0`,
  -- exactly at the one term-level call site (`hL`, below) that needs them.
  have hcutSup := aux_cor_as_resolvent_hcut_supply hd Jc Pc Xc W Cp D Sf Step Dbase Interp
  obtain ⟨delta0_hcut, hpos_hcut, hHcut_all⟩ := hcutSup
  have hunifSup := aux_cor_as_resolvent_hunif_supply hd Jc Pc Xc W Cp D Sf Step Dbase Interp
  obtain ⟨delta0_hunif, hpos_hunif, hHunif_all⟩ := hunifSup
  have hL := limiting_local_energy d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp BD BDQ hcontract
  rcases hL with ⟨δ, hδ, hL⟩
  refine ⟨min 1 (min δ (min delta0_hcut delta0_hunif)),
    lt_min one_pos (lt_min hδ (lt_min hpos_hcut hpos_hunif)), ?_⟩
  intro M Rm Sreg It H hH hle hP
  have hle1 : M.delta ≤ 1 := hle.trans (min_le_left _ _)
  have hle2 : M.delta ≤ δ := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hle3 : M.delta ≤ delta0_hcut :=
    hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hle4 : M.delta ≤ delta0_hunif :=
    hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hle_δ : M.delta ≤ min 1 δ := le_min hle1 hle2
  have hcutInst := hHcut_all M Rm Sreg It H hH hle3
  have hunifInst := hHunif_all M Rm Sreg It H hH hle4
  have hn : ∀ n : ℕ, ∃ G : BilateralField d →
      (DomainL2 (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
          (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
          (aux_mfd_convergence_hr d n)) →L[ℝ]
        DomainL2 (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
          (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
          (aux_mfd_convergence_hr d n))),
      Measurable G ∧ ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        (∀ f : DomainL2 (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
            (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
            (aux_mfd_convergence_hr d n)),
          Tendsto
            (fun N : ℕ =>
              (responseSolution (killedResponseSpace (Ω := centeredCube
                  (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                  (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                  (aux_mfd_convergence_hr d n)) (hP n))
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                    (aux_mfd_convergence_hr d n))
                  ((sobolevVolumeLoad f).comp
                    (killedResponseSpace (Ω := centeredCube
                      (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                      (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                      (aux_mfd_convergence_hr d n)) (hP n)).space.subtypeL)).val.1)
            atTop (𝓝 (G omega f))) ∧
        (∀ u : DomainL2 (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
            (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
            (aux_mfd_convergence_hr d n)),
          limitFormEnergy (G omega) u ≠ ⊤ →
          ∃ v : CubeFractionalL2 (k := 1) hd
              (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
              (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
              (aux_mfd_convergence_hr d n) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
            v.val 0 = u) := by
    intro n
    have h := hL M Rm Sreg It H hH hle_δ hcutInst hunifInst
      (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
      (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
      (aux_mfd_convergence_hr d n) ⟨(n : ℤ), rfl⟩ (hP n)
    rcases h with ⟨G, hGm, hGae, -⟩
    refine ⟨G, hGm, ?_⟩
    filter_upwards [hGae] with omega hω
    refine ⟨hω.1, fun u hu => ?_⟩
    rcases hω.2.2.2.1 with ⟨Ccoer, -, -, hco⟩
    rcases hco u hu with ⟨v, hv, -⟩
    exact ⟨v, hv⟩
  choose G hGm hGae using hn
  exact ⟨G, hGm, ae_all_iff.2 hGae⟩

/-- The zero datum has a finite fractional seminorm. -/
theorem aux_mfd_convergence_seminorm_zero {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1) :
    cubeFractionalL2Seminorm hd z r hr s
      (fun _ : Fin 1 => (0 : DomainL2 (centeredCube z r hr))) < ⊤ := by
  unfold cubeFractionalL2Seminorm
  have h0 : (⇑(0 : DomainL2 (centeredCube z r hr))) =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))] 0 := Lp.coeFn_zero _ _ _
  have hI : (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal (∑ i : Fin 1, ((fun _ : Fin 1 => (0 : DomainL2 (centeredCube z r hr))) i x -
          (fun _ : Fin 1 => (0 : DomainL2 (centeredCube z r hr))) i y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (s : ℝ))) = 0 := by
    rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
    filter_upwards [h0] with x hx
    rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
    filter_upwards [h0] with y hy
    have hx' : ((0 : DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ) x = 0 := hx
    have hy' : ((0 : DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ) y = 0 := hy
    simp only [hx', hy', sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero, ENNReal.ofReal_zero, ENNReal.zero_div]
  rw [hI, mul_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
  exact ENNReal.zero_lt_top

/-- The half-order embedding of the finite-energy domain. -/
theorem aux_mfd_convergence_i
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (G : (n : ℕ) → BilateralField d →
          (DomainL2 (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
              (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
              (aux_mfd_convergence_hr d n)) →L[ℝ]
            DomainL2 (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
              (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
              (aux_mfd_convergence_hr d n))))
    (hco : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ n : ℕ,
          (∀ u : DomainL2 (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
              (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
              (aux_mfd_convergence_hr d n)),
            limitFormEnergy (G n omega) u ≠ ⊤ →
            ∃ v : CubeFractionalL2 (k := 1) hd
                (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                (aux_mfd_convergence_hr d n) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
              v.val 0 = u)) :
    ∃ i : (n : ℕ) → (omega : BilateralField d) →
        (u : DomainL2 (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
              (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
              (aux_mfd_convergence_hr d n))) →
          (limitFormEnergy (G n omega) u).toENNReal ≠ ⊤ →
          CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
            (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
            (aux_mfd_convergence_hr d n) halfFractionalOrder,
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ (n : ℕ) (u : DomainL2 (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
              (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
              (aux_mfd_convergence_hr d n)))
          (hu : (limitFormEnergy (G n omega) u).toENNReal ≠ ⊤),
          (i n omega u hu).val 0 = u := by
  classical
  refine ⟨fun n omega u _ =>
    if h : cubeFractionalL2Seminorm hd (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
        (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
        (aux_mfd_convergence_hr d n) halfFractionalOrder (fun _ : Fin 1 => u) < ⊤
    then ⟨fun _ => u, h⟩
    else ⟨fun _ => 0, aux_mfd_convergence_seminorm_zero hd _ _ _ halfFractionalOrder⟩, ?_⟩
  filter_upwards [hco] with omega h
  intro n u hu
  have hne : limitFormEnergy (G n omega) u ≠ ⊤ := by
    intro htop
    apply hu
    rw [htop]
    rfl
  obtain ⟨v, hv⟩ := h n u hne
  have hv' : v.val = fun _ : Fin 1 => u := by
    funext j
    rw [Fin.fin_one_eq_zero j]
    exact hv
  have h34 : cubeFractionalL2Seminorm hd (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
      (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
      (aux_mfd_convergence_hr d n) _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder (fun _ : Fin 1 => u) < ⊤ := by
    rw [← hv']
    exact v.property
  have h12 := aux_mfd_convergence_seminorm_mono hd _ _ _ halfFractionalOrder
    _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder (by
      simp only [halfFractionalOrder, _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder]
      norm_num) _ h34
  dsimp only [CubeFractionalL2]
  simp only [dite_eq_left h12]

-- ===== from T6c.lean =====
/-- The completed speed traces on the triadic cube family (`speed_trace_completion`). -/
theorem aux_mfd_convergence_trace
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (mu : BilateralField d → Measure (SpatialCoordinates d))
    (hgr : ∀ (R : Set (SpatialCoordinates d)), Bornology.IsBounded R →
      ∃ Kmu : BilateralField d → ℝ, ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        0 ≤ Kmu omega ∧
        (∀ N x, x ∈ R → ∀ r : ℝ, 0 < r → r ≤ 1 →
          cutoffSpeedMeasure M H omega N (Metric.ball x r) ≤
            ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - aux_mfd_convergence_eps d))) ∧
        (∀ x, x ∈ R → ∀ r : ℝ, 0 < r → r ≤ 1 →
          mu omega (Metric.ball x r) ≤
            ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - aux_mfd_convergence_eps d))))
    (hmu : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) (mu omega) ∧
        ∀ n : ℕ, mu omega (closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n)) (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n)) (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))) < ⊤) :
    ∃ (T : (n : ℕ) → (omega : BilateralField d) → CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n)) (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n)) (aux_mfd_convergence_hr d n) halfFractionalOrder →
          Lp ℝ 2 ((mu omega).restrict (closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n)) (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n)) (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)))))
      (Ktrace Ctrace : ℕ → BilateralField d → ℝ),
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ n : ℕ,
        0 ≤ Ktrace n omega ∧ 0 ≤ Ctrace n omega ∧
        MeasureTraceCharacterization hd (aux_mfd_convergence_Qtri d n) (aux_mfd_convergence_hr d n)
          ((mu omega).restrict (closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n)) (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n)) (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)))) (Ktrace n omega) (Ctrace n omega) (T n omega) := by
  classical
  have hε := aux_mfd_convergence_eps_unit d
  have hSTC := fun n : ℕ => speed_trace_completion hd (aux_mfd_convergence_Qtri d n)
    (aux_mfd_convergence_hr d n) _ hε.1 hε.2
  choose Cn hCn0 hCn using hSTC
  have hK := fun n : ℕ => hgr (closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n)) (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n)) (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)))
    (Metric.isBounded_ball (x := Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
      (r := Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n) / 2)).closure
  choose Kmu hKmu using hK
  have hset : ∀ n : ℕ, closure (Homogenization.openCubeSet (aux_mfd_convergence_Qtri d n)) =
      closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n)) (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n)) (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)) := by
    intro n
    rw [centeredCube_eq_openCubeSet]
  have hTex : ∀ (n : ℕ) (omega : BilateralField d), ∃ T : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n)) (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n)) (aux_mfd_convergence_hr d n) halfFractionalOrder →
      Lp ℝ 2 ((mu omega).restrict (closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n)) (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n)) (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)))),
      (0 ≤ Kmu n omega ∧ mu omega (closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n)) (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n)) (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))) < ⊤ ∧
          MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) (mu omega) ∧
          (∀ x ∈ closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n)) (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n)) (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)), ∀ r : ℝ, 0 < r → r ≤ 1 →
            mu omega (Metric.ball x r) ≤ ENNReal.ofReal (Kmu n omega * r ^ ((d : ℝ) - aux_mfd_convergence_eps d)) ∧
            ∀ N, cutoffSpeedMeasure M H omega N (Metric.ball x r) ≤
              ENNReal.ofReal (Kmu n omega * r ^ ((d : ℝ) - aux_mfd_convergence_eps d)))) →
        MeasureTraceCharacterization hd (aux_mfd_convergence_Qtri d n)
          (aux_mfd_convergence_hr d n) ((mu omega).restrict (closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n)) (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n)) (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))))
          (Kmu n omega) (Cn n) T := by
    intro n omega
    by_cases hc : (0 ≤ Kmu n omega ∧ mu omega (closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n)) (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n)) (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))) < ⊤ ∧
          MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) (mu omega) ∧
          (∀ x ∈ closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n)) (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n)) (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)), ∀ r : ℝ, 0 < r → r ≤ 1 →
            mu omega (Metric.ball x r) ≤ ENNReal.ofReal (Kmu n omega * r ^ ((d : ℝ) - aux_mfd_convergence_eps d)) ∧
            ∀ N, cutoffSpeedMeasure M H omega N (Metric.ball x r) ≤
              ENNReal.ofReal (Kmu n omega * r ^ ((d : ℝ) - aux_mfd_convergence_eps d))))
    · have h := hCn n M H omega (mu omega) (Kmu n omega) hc.1 (by rw [hset n]; exact hc.2.1)
        hc.2.2.1 (by rw [hset n]; exact hc.2.2.2)
        ((mu omega).restrict (closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n)) (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n)) (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)))) (Or.inl (by rw [hset n]))
      obtain ⟨T, hT, -⟩ := h
      exact ⟨T, fun _ => hT⟩
    · exact ⟨fun _ => 0, fun h => absurd h hc⟩
  choose T hT using hTex
  refine ⟨T, Kmu, fun n _ => Cn n, ?_⟩
  have hae : ∀ n : ℕ, ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, (0 ≤ Kmu n omega ∧ mu omega (closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n)) (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n)) (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))) < ⊤ ∧
          MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) (mu omega) ∧
          (∀ x ∈ closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n)) (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n)) (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)), ∀ r : ℝ, 0 < r → r ≤ 1 →
            mu omega (Metric.ball x r) ≤ ENNReal.ofReal (Kmu n omega * r ^ ((d : ℝ) - aux_mfd_convergence_eps d)) ∧
            ∀ N, cutoffSpeedMeasure M H omega N (Metric.ball x r) ≤
              ENNReal.ofReal (Kmu n omega * r ^ ((d : ℝ) - aux_mfd_convergence_eps d)))) := by
    intro n
    filter_upwards [hKmu n, hmu] with omega hk hm
    exact ⟨hk.1, hm.2 n, hm.1, fun x hx r hr0 hr1 =>
      ⟨hk.2.2 x hx r hr0 hr1, fun N => hk.2.1 N x hx r hr0 hr1⟩⟩
  filter_upwards [ae_all_iff.2 hae] with omega h n
  exact ⟨(h n).1, hCn0 n, hT n omega (h n)⟩

/-- Linearity of the killed occupation resolvent in the datum (scalar multiples). -/
theorem aux_mfd_convergence_RN_smul {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (n N : ℕ) (omega : BilateralField d) {lam : ℝ} (hlam : 0 < lam) (c : ℝ)
    (g : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d) :
    aux_mfd_convergence_RN KN n N omega lam (c • g) x =
      c * aux_mfd_convergence_RN KN n N omega lam g x := by
  have hlin : ∀ path : DiffusionPath d,
      aux_in_stopped_passage_occ (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n)) (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n)) (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)) lam (c • g) path =
        c * aux_in_stopped_passage_occ (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n)) (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n)) (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)) lam g path := by
    intro path
    have h := aux_in_stopped_passage_occ_lin (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n)) (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n)) (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)) hlam (c • g) g g c 0
      (fun y => by simp) path
    rw [h, zero_mul, add_zero]
  change ∫ path, aux_in_stopped_passage_occ (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n)) (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n)) (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)) lam (c • g) path ∂(KN N (omega, x)) =
    c * ∫ path, aux_in_stopped_passage_occ (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n)) (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n)) (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)) lam g path ∂(KN N (omega, x))
  simp_rw [hlin]
  exact integral_const_mul c _

theorem aux_mfd_convergence_resolvent
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg),
        M.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
      ∀ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)),
        (∀ N, IsMarkovKernel (KN N)) → in_crossing M H PN KN →
        aux_cutoff_lifetime_package_LocalInput M H KN →
      ∃ Rlim : ℕ → BilateralField d → ℝ →
          BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ,
        (∀ (n : ℕ) (lam : ℝ), 0 < lam →
          ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
            Measurable (fun p : BilateralField d × SpatialCoordinates d =>
              Rlim n p.1 lam f p.2)) ∧
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          (∀ (n : ℕ) (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
              ContinuousOn (Rlim n omega lam f)
                (closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                  (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                  (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))) ∧
              ∀ x ∈ frontier (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                  (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                  (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)),
                Rlim n omega lam f x = 0) ∧
          (∀ (n : ℕ) (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
              ∀ delta : ℝ, 0 < delta → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
                ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                  (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                  (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)),
                  |(∫ path, (∫ t in Set.Ioi (0 : ℝ),
                      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                        ((centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                          (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                          (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))) path}
                        (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
                      ∂(KN N (omega, x))) - Rlim n omega lam f x| < delta) ∧
          (∀ (n : ℕ) (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ, ∀ N : ℕ,
              ContinuousOn (fun x => ∫ path, (∫ t in Set.Ioi (0 : ℝ),
                      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                        ((centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                          (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                          (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))) path}
                        (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
                      ∂(KN N (omega, x)))
                (closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                  (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                  (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))))) := by
  have hCAR := cor_as_resolvent hd Jc Pc Xc Sf W Cp Interp BD BDQ D Step Dbase hcontract
  rcases hCAR with ⟨δ1, hδ1, hCAR⟩
  have hGG := aux_mfd_convergence_G hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp BD BDQ hcontract
  rcases hGG with ⟨δ2, hδ2, hGG⟩
  have hCG := prop_chaos_growth (d := d) hd (aux_mfd_convergence_eps d)
    (aux_mfd_convergence_eps_unit d) (aux_mfd_convergence_p d) (aux_mfd_convergence_p_spec d)
  rcases hCG with ⟨δ3, hδ3, hCG⟩
  refine ⟨min δ1 (min δ2 δ3), lt_min hδ1 (lt_min hδ2 hδ3), ?_⟩
  intro M Rm Sreg It hle H hH PN KN hKN hin hinput
  have hle1 : M.delta ≤ δ1 := hle.trans (min_le_left _ _)
  have hle2 : M.delta ≤ δ2 := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hle3 : M.delta ≤ δ3 := hle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hP := fun n : ℕ => aux_mfd_convergence_cube_poincare hd
    (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
    (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n)) (aux_mfd_convergence_hr d n)
  have hG := hGG M Rm Sreg It H hH hle2 hP
  rcases hG with ⟨G, hGm, hGae⟩
  have hcg := hCG M H hH hle3
  rcases hcg with ⟨mu, -, hmuae, hgr⟩
  have hmuF : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) (mu omega) ∧
        (∀ n : ℕ, mu omega (frontier (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n)) (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n)) (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))) = 0) ∧ (∀ n : ℕ, mu omega (closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n)) (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n)) (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))) < ⊤) := by
    filter_upwards [hmuae] with omega h
    have heq : (fun N => cutoffSpeedMeasure M H omega N) =
        fun N => weightedChaosCutoff M H N omega :=
      funext fun N => cutoffSpeedMeasure_eq_weightedChaosCutoff M H omega N
    have := h.2.1
    refine ⟨by rw [heq]; exact h.1, fun n => h.2.2.2.2 _ _ _, fun n => ?_⟩
    exact (Metric.isBounded_ball.isCompact_closure).measure_lt_top
  have hgr' : ∀ (R : Set (SpatialCoordinates d)), Bornology.IsBounded R →
      ∃ Kmu : BilateralField d → ℝ, ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        0 ≤ Kmu omega ∧
        (∀ N x, x ∈ R → ∀ r : ℝ, 0 < r → r ≤ 1 →
          cutoffSpeedMeasure M H omega N (Metric.ball x r) ≤
            ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - aux_mfd_convergence_eps d))) ∧
        (∀ x, x ∈ R → ∀ r : ℝ, 0 < r → r ≤ 1 →
          mu omega (Metric.ball x r) ≤
            ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - aux_mfd_convergence_eps d))) := by
    intro R hR
    have h := hgr R hR
    rcases h with ⟨Kmu, -, hK⟩
    refine ⟨Kmu, hK.mono fun omega h => ⟨h.1, fun N x hx r h0 h1 => ?_, h.2.2⟩⟩
    rw [cutoffSpeedMeasure_eq_weightedChaosCutoff]
    exact h.2.1 N x hx r h0 h1
  have hTr := aux_mfd_convergence_trace hd M H mu hgr'
    (hmuF.mono fun omega h => ⟨h.1, h.2.2⟩)
  rcases hTr with ⟨T, Ktrace, Ctrace, hTae⟩
  have hI := aux_mfd_convergence_i hd M G (hGae.mono fun omega h n => (h n).2)
  rcases hI with ⟨i, hiae⟩
  classical
  let J : (n : ℕ) → BilateralField d →
      DomainL2 (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
        (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
        (aux_mfd_convergence_hr d n)) → SpatialCoordinates d → ℝ :=
    fun n omega u => if hu : (limitFormEnergy (G n omega) u).toENNReal ≠ ⊤ then
      (T n omega (i n omega u hu) : SpatialCoordinates d → ℝ) else 0
  have hJ : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (n : ℕ) (u : DomainL2 (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
        (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
        (aux_mfd_convergence_hr d n)))
        (hu : (limitFormEnergy (G n omega) u).toENNReal ≠ ⊤),
        (J n omega u) =ᵐ[(mu omega).restrict (closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n)) (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n)) (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)))]
          (T n omega (i n omega u hu) : SpatialCoordinates d → ℝ) := by
    refine Eventually.of_forall fun omega n u hu => ?_
    simp only [J, dite_eq_left hu]
    rfl
  have hR := hCAR M Rm Sreg It hle1 H hH PN KN hKN hin hinput (aux_mfd_convergence_Qtri d)
    (aux_mfd_convergence_hr d) hP G hGm (hGae.mono fun omega h n f => (h n).1 f) mu hmuF
    T Ktrace Ctrace hTae i hiae J hJ (aux_mfd_convergence_RN KN) (fun _ _ _ _ _ _ => rfl)
  rcases hR with ⟨Rlim, hRm, hRae⟩
  refine ⟨Rlim, hRm, ?_⟩
  filter_upwards [hRae] with omega h
  refine ⟨h.1, h.2.1, ?_⟩
  intro n lam hlam f N
  show ContinuousOn (fun x => aux_mfd_convergence_RN KN n N omega lam f x) (closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n)) (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n)) (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)))
  have hc : 0 < ‖f‖ + 1 := by positivity
  have hg : ‖(‖f‖ + 1)⁻¹ • f‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc, inv_mul_le_iff₀ hc]
    linarith
  obtain ⟨Kom, -, hKom⟩ := h.2.2.1 n lam lam hlam le_rfl
  have hhol := (hKom N lam le_rfl le_rfl ((‖f‖ + 1)⁻¹ • f) hg).2
  have hcont := aux_mfd_convergence_holder_continuousOn
    (fun x => aux_mfd_convergence_RN KN n N omega lam ((‖f‖ + 1)⁻¹ • f) x) (closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n)) (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n)) (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))) Kom
    (1 / 4) (by norm_num) hhol
  have heq : (fun x => aux_mfd_convergence_RN KN n N omega lam f x) =
      fun x => (‖f‖ + 1) * aux_mfd_convergence_RN KN n N omega lam ((‖f‖ + 1)⁻¹ • f) x := by
    funext x
    rw [← aux_mfd_convergence_RN_smul KN n N omega hlam, smul_smul, mul_inv_cancel₀ hc.ne',
      one_smul]
  rw [heq]
  exact continuousOn_const.mul hcont

-- ===== from MfdMain.lean =====
/-- Convergence in probability, in the `∃ N0` form, gives convergence of the
measures to zero. -/
theorem aux_mfd_convergence_tendsto_of_prob {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (S : ℕ → Set α)
    (h : ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N, N0 ≤ N → μ (S N) ≤ ENNReal.ofReal rho) :
    Tendsto (fun N => μ (S N)) atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases htop : ε = ⊤
  · exact Eventually.of_forall fun N => htop ▸ le_top
  · have hpos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
    obtain ⟨N0, hN0⟩ := h ε.toReal hpos
    refine eventually_atTop.2 ⟨N0, fun N hN => (hN0 N hN).trans ?_⟩
    rw [ENNReal.ofReal_toReal htop]

/-! ## Assembly on the common event -/

theorem aux_mfd_convergence_final
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (hinput : aux_cutoff_lifetime_package_LocalInput M H KN)
    (hstart : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      Continuous (fun x : SpatialCoordinates d =>
        jointPathProbabilityMeasure (KN N) (hKN N) omega x))
    (P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hP : ∀ omega, (P omega).IsConservative)
    (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hK : IsMarkovKernel K)
    (hcontK : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        Continuous (fun x : SpatialCoordinates d =>
          jointPathProbabilityMeasure K hK omega x))
    (hlim : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
          SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x)
    (hconvP : ∀ B : Set (SpatialCoordinates d), IsCompact B →
        ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
          ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
            (chaosSampleLaw M).toMeasure
                {omega : BilateralField d | ∃ x ∈ B, eps ≤
                  pathLevyProkhorovDist
                    (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                    (jointPathProbabilityMeasure K hK omega x)} ≤
              ENNReal.ofReal rho)
    (Rlim : ℕ → BilateralField d → ℝ →
          BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          (∀ (n : ℕ) (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
              ContinuousOn (Rlim n omega lam f)
                (closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                  (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                  (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))) ∧
              ∀ x ∈ frontier (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                  (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                  (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)),
                Rlim n omega lam f x = 0) ∧
          (∀ (n : ℕ) (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
              ∀ delta : ℝ, 0 < delta → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
                ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                  (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                  (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)),
                  |(∫ path, (∫ t in Set.Ioi (0 : ℝ),
                      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                        ((centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                          (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                          (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))) path}
                        (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
                      ∂(KN N (omega, x))) - Rlim n omega lam f x| < delta) ∧
          (∀ (n : ℕ) (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ, ∀ N : ℕ,
              ContinuousOn (fun x => ∫ path, (∫ t in Set.Ioi (0 : ℝ),
                      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                        ((centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                          (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                          (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d))) path}
                        (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
                      ∂(KN N (omega, x)))
                (closure (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                  (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                  (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)))))
    (htors : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ n : ℕ, ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ N : ℕ,
            ∀ x ∈ (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                  (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                  (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)),
              ∫⁻ path, ContinuousPath.exitTime
                (centeredCube (Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
                  (Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
                  (aux_mfd_convergence_hr d n) : Set (SpatialCoordinates d)) path
                ∂(KN N (omega, x)) ≤ ENNReal.ofReal Cw)
    (mu : BilateralField d → Measure (SpatialCoordinates d))
    (hmuae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          MeasuresConvergeLocally
            (fun N ↦ weightedChaosCutoff M H N omega) (mu omega) ∧
          IsLocallyFiniteMeasure (mu omega) ∧
          (mu omega).IsOpenPosMeasure ∧ NullSingletonClass (mu omega) ∧
          (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
            mu omega (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) = 0)) :
    (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            Tendsto (infraredPartialSum omega) atTop (nhds (H omega)) ∧
            (∀ N, ∃ D :
                SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum
                  (SpatialCoordinates d),
              (∀ mu, DenseRange (D.operator mu)) ∧
              SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
                (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) D ∧
              ∀ (mu : Semigroup.PositiveShift)
                (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ)
                (x : SpatialCoordinates d),
                D.solution mu f x =
                  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
                    kernelIntegral (PN N omega (Real.toNNReal t)) f x) ∧
            (∀ N I x,
              (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
                SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x) ∧
            (∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
              SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x) ∧
            Continuous (fun x ↦ jointPathProbabilityMeasure K hK omega x) ∧
            (∀ B : Set (SpatialCoordinates d), IsCompact B →
              ∀ epsilon : ℝ, 0 < epsilon → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
                ∀ x ∈ B,
                  pathLevyProkhorovDist
                    (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                    (jointPathProbabilityMeasure K hK omega x) < epsilon) ∧
            (∀ (t : ℝ≥0) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ),
              Continuous (kernelIntegral (P omega t) f)) ∧
            (∃ mu : Measure (SpatialCoordinates d),
              MeasuresConvergeLocally (fun N ↦ cutoffSpeedMeasure M H omega N) mu ∧
              IsLocallyFiniteMeasure mu ∧ NullSingletonClass mu ∧ mu.IsOpenPosMeasure ∧
              SemigroupSymmetric (P omega) mu) ∧
            HasStrongMarkovRestart K omega ∧ HasFiniteMeanExits K omega) ∧
          ∀ (x : SpatialCoordinates d) (F : BoundedContinuousFunction (DiffusionPath d) ℝ),
            Tendsto
              (fun N ↦ ∫ omega,
                (∫ path, F (physicalRescaledPath M N path)
                  ∂(KN 0 (omega, (3 : ℝ) ^ N • x))) ∂(chaosSampleLaw M).toMeasure)
              atTop
              (nhds (∫ omega, (∫ path, F path ∂(K (omega, x))) ∂(chaosSampleLaw M).toMeasure)) := by
  have hmuC : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N ↦ cutoffSpeedMeasure M H omega N) (mu omega) ∧
        IsLocallyFiniteMeasure (mu omega) := by
    filter_upwards [hmuae] with omega h
    have heq : (fun N ↦ cutoffSpeedMeasure M H omega N) =
        fun N ↦ weightedChaosCutoff M H N omega :=
      funext fun N => cutoffSpeedMeasure_eq_weightedChaosCutoff M H omega N
    rw [heq]
    exact ⟨h.1, h.2.1⟩
  have hconvT : ∀ B : Set (SpatialCoordinates d), IsCompact B → ∀ eps : ℝ, 0 < eps →
      Tendsto (fun N ↦ (chaosSampleLaw M).toMeasure
          {omega : BilateralField d | ∃ x ∈ B, eps ≤
            pathLevyProkhorovDist
              (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
              (jointPathProbabilityMeasure K hK omega x)}) atTop (nhds 0) :=
    fun B hB eps heps => aux_mfd_convergence_tendsto_of_prob _ _ (hconvP B hB eps heps)
  have hPL := aux_prop_limit_properties_of_suppliers hd M H hH PN P hP KN hKN K hK hin hinput hlim hconvT
    (hmuC.mono fun omega h => ⟨mu omega, h⟩)
  have hkill := aux_mfd_convergence_killed hd M H hH PN KN hKN hin P hP K hK hcontK hlim
    hconvP Rlim hRae
  rcases hkill with ⟨hkilled, hres1⟩
  have hAS := prop_as_quenched hd M H hH PN KN hKN K hK hin hinput
    (fun n => Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
    (fun n => Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
    (aux_mfd_convergence_hr d) (aux_mfd_convergence_exhaust d) P hP hkilled
    (hPL.mono fun omega h => ⟨h.1, h.2.2.1⟩) hlim hstart
  have hFE := aux_cor_finite_exit_of_suppliers hd M H hH PN KN hKN K hK hin
    (fun n => Homogenization.cubeCenter (aux_mfd_convergence_Qtri d n))
    (fun n => Homogenization.cubeScaleFactor (aux_mfd_convergence_Qtri d n))
    (aux_mfd_convergence_hr d) htors hres1 (aux_mfd_convergence_exhaust d)
  have hPR := physical_rescaling hd M H hH PN KN hKN hin (fun N => aux_mfd_convergence_sigma N)
    (fun N omega j x => aux_mfd_convergence_sigma_apply N omega j x)
  have hAK := annealed_kernel_convergence M KN hKN K hK hAS
  refine ⟨?_, ?_⟩
  · filter_upwards [hH.2, hin.1, hin.2.2, hlim, hPL, hAS, hmuC, hmuae, hFE] with
      omega h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact ⟨h1, h2, h3, h4, h5.1, h6, h5.2.1,
      ⟨mu omega, h7.1, h7.2, h8.2.2.2.1, h8.2.2.1, h5.2.2.2 (mu omega) h7.1 h7.2⟩,
      h5.2.2.1, h9⟩
  · intro x F
    exact (hAK x F).congr (fun N => (hPR.2.2 N x F).symm)

-- ===== from MfdTop.lean =====
/-- The common threshold: the minimum of the thresholds of the cited inputs. -/
def aux_mfd_convergence_delta0
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u) : ℝ :=
  min (min (Classical.choose (finiteDimensional_cutoff (d := d) hd))
      (Classical.choose (tight_prop (d := d) hd Jc Pc Xc Sf W Cp)))
    (min (min (1 : ℝ)
        (Classical.choose (prop_chaos_growth (d := d) hd (aux_mfd_convergence_eps d)
          (aux_mfd_convergence_eps_unit d) (aux_mfd_convergence_p d)
          (aux_mfd_convergence_p_spec d))))
      (min (Classical.choose (aux_mfd_convergence_torsion hd Jc Pc Xc W Cp D Sf hES Step Dbase Interp))
        (Classical.choose (aux_mfd_convergence_resolvent hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp BD BDQ
          hcontract))))

theorem aux_mfd_convergence_delta0_pos
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u) :
    0 < aux_mfd_convergence_delta0 hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp BD BDQ hcontract := by
  unfold aux_mfd_convergence_delta0
  have h1 := (Classical.choose_spec (finiteDimensional_cutoff (d := d) hd)).1
  have h2 := (Classical.choose_spec (tight_prop (d := d) hd Jc Pc Xc Sf W Cp)).1
  have h3 : (0 : ℝ) < 1 := one_pos
  have h4 := (Classical.choose_spec (prop_chaos_growth (d := d) hd (aux_mfd_convergence_eps d)
    (aux_mfd_convergence_eps_unit d) (aux_mfd_convergence_p d)
    (aux_mfd_convergence_p_spec d))).1
  have h5 := (Classical.choose_spec (aux_mfd_convergence_torsion hd Jc Pc Xc W Cp D Sf hES Step Dbase Interp)).1
  have h6 := (Classical.choose_spec (aux_mfd_convergence_resolvent hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp BD BDQ
    hcontract)).1
  exact lt_min (lt_min h1 h2) (lt_min (lt_min h3 h4) (lt_min h5 h6))

/-- One model: every cited input applied at the fixed thresholds. -/
theorem aux_mfd_convergence_core
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
    (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
    (_hMpos : 0 < M.delta)
    (hMle : M.delta ≤ aux_mfd_convergence_delta0 hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp BD BDQ hcontract)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (hinput : aux_cutoff_lifetime_package_LocalInput M H KN) :
    ∃ (P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
      (_hP : ∀ omega, (P omega).IsConservative)
      (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
      (hK : IsMarkovKernel K),
    (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            Tendsto (infraredPartialSum omega) atTop (nhds (H omega)) ∧
            (∀ N, ∃ D :
                SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum
                  (SpatialCoordinates d),
              (∀ mu, DenseRange (D.operator mu)) ∧
              SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
                (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) D ∧
              ∀ (mu : Semigroup.PositiveShift)
                (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ)
                (x : SpatialCoordinates d),
                D.solution mu f x =
                  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
                    kernelIntegral (PN N omega (Real.toNNReal t)) f x) ∧
            (∀ N I x,
              (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
                SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x) ∧
            (∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
              SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x) ∧
            Continuous (fun x ↦ jointPathProbabilityMeasure K hK omega x) ∧
            (∀ B : Set (SpatialCoordinates d), IsCompact B →
              ∀ epsilon : ℝ, 0 < epsilon → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
                ∀ x ∈ B,
                  pathLevyProkhorovDist
                    (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                    (jointPathProbabilityMeasure K hK omega x) < epsilon) ∧
            (∀ (t : ℝ≥0) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ),
              Continuous (kernelIntegral (P omega t) f)) ∧
            (∃ mu : Measure (SpatialCoordinates d),
              MeasuresConvergeLocally (fun N ↦ cutoffSpeedMeasure M H omega N) mu ∧
              IsLocallyFiniteMeasure mu ∧ NullSingletonClass mu ∧ mu.IsOpenPosMeasure ∧
              SemigroupSymmetric (P omega) mu) ∧
            HasStrongMarkovRestart K omega ∧ HasFiniteMeanExits K omega) ∧
          ∀ (x : SpatialCoordinates d) (F : BoundedContinuousFunction (DiffusionPath d) ℝ),
            Tendsto
              (fun N ↦ ∫ omega,
                (∫ path, F (physicalRescaledPath M N path)
                  ∂(KN 0 (omega, (3 : ℝ) ^ N • x))) ∂(chaosSampleLaw M).toMeasure)
              atTop
              (nhds (∫ omega, (∫ path, F path ∂(K (omega, x))) ∂(chaosSampleLaw M).toMeasure)) := by
  unfold aux_mfd_convergence_delta0 at hMle
  have hle2 : M.delta ≤ Classical.choose (tight_prop (d := d) hd Jc Pc Xc Sf W Cp) :=
    hMle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hle4 : M.delta ≤ Classical.choose (prop_chaos_growth (d := d) hd
      (aux_mfd_convergence_eps d) (aux_mfd_convergence_eps_unit d) (aux_mfd_convergence_p d)
      (aux_mfd_convergence_p_spec d)) :=
    hMle.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hle5 : M.delta ≤ Classical.choose (aux_mfd_convergence_torsion hd Jc Pc Xc W Cp D Sf hES Step Dbase Interp) :=
    hMle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hle6 : M.delta ≤ Classical.choose (aux_mfd_convergence_resolvent hd Jc Pc Xc Sf W Cp D hES Step Dbase
      Interp BD BDQ hcontract) :=
    hMle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  -- tightness, lifetime package, start continuity
  have hLP := aux_cutoff_lifetime_package_local M H KN hinput
  rcases hLP with ⟨L, hL, hLlocal, hLstrong⟩
  have hLloc := hLlocal
  have htightNew := (Classical.choose_spec
    (tight_prop (d := d) hd Jc Pc Xc Sf W Cp)).2 M Rm Sreg It hle2
      H hH PN KN hKN hin L hL hLloc
  have htight : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ Kset : Set (DiffusionPath d), IsCompact Kset ∧
          ∀ N : ℕ, (∫⁻ omega, ⨆ x ∈ B, (KN N (omega, x)) Ksetᶜ
            ∂(chaosSampleLaw M).toMeasure) ≤ ENNReal.ofReal epsilon := by
    intro B hB epsilon hepsilon
    obtain ⟨Kset, hKset, hmajorant, _⟩ := htightNew B hB epsilon hepsilon
    refine ⟨Kset, hKset, ?_⟩
    intro N
    obtain ⟨G, _, hG, hGint⟩ := hmajorant N
    exact (lintegral_mono fun omega => iSup_le fun x => iSup_le fun hx =>
      hG omega x hx).trans hGint
  have hbounds := tight_fixed_cutoff hd M H hH PN KN hKN hin L hL
    (hLlocal)
  have hstart := in_cutoff_start_continuity hd M H hH PN KN hKN hin hbounds
  -- pathwise killed resolvents
  have hRES := (Classical.choose_spec (aux_mfd_convergence_resolvent hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
    BD BDQ hcontract)).2 M Rm Sreg It hle6 H hH PN KN hKN hin hinput
  rcases hRES with ⟨Rlim, hRmeas, hRae⟩
  -- Cauchy property and the limit
  have hcauchy := aux_mfd_convergence_path_cauchy hd M H hH PN KN hKN hin hinput hstart htight
    Rlim hRmeas (hRae.mono fun omega h => h.2.1)
  have hLK := limit_kernel hd M H hH PN KN hKN hin hcauchy hstart hin.2.2
  rcases hLK with ⟨P, hP, K, hK, hcontK, hlim, hconvP⟩
  -- torsion and speed measure
  have htors := (Classical.choose_spec (aux_mfd_convergence_torsion hd Jc Pc Xc W Cp D Sf hES Step Dbase Interp)).2 M Rm
    Sreg It hle5 H hH PN KN hKN hin hinput
  have hCG := (Classical.choose_spec (prop_chaos_growth (d := d) hd
      (aux_mfd_convergence_eps d) (aux_mfd_convergence_eps_unit d) (aux_mfd_convergence_p d)
      (aux_mfd_convergence_p_spec d))).2 M H hH hle4
  rcases hCG with ⟨mu, -, hmuae, -⟩
  exact ⟨P, hP, K, hK, aux_mfd_convergence_final hd M H hH PN KN hKN hin hinput hstart P hP K hK
    hcontK hlim hconvP Rlim hRae htors mu hmuae⟩

/-- Process convergence, `thm:mfd-convergence`. -/
theorem mfd_convergence
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)
    (hlife : ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
        (∃ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
          (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)),
          (∀ N, IsMarkovKernel (KN N)) ∧ in_crossing M H PN KN) →
        ∃ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
          (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)),
          (∀ N, IsMarkovKernel (KN N)) ∧ in_crossing M H PN KN ∧
            aux_cutoff_lifetime_package_LocalInput M H KN) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg),
        0 < M.delta → M.delta ≤ delta0 →
        let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d,
            C(SpatialCoordinates d, ℝ)) :=
          ⟨fun g ↦ g.1.1, continuous_subtype_val.fst⟩
        let nu := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).map
          forget
        let law := (commonScaleLaw d nu).toMeasure
        ∃ H : BilateralField d → C(SpatialCoordinates d, ℝ), Measurable H ∧
        ∃ PN : ℕ → BilateralField d →
            SubMarkovKernelSemigroup (SpatialCoordinates d),
        ∃ _hPN : ∀ N omega, (PN N omega).IsConservative,
        ∃ P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d),
        ∃ _hP : ∀ omega, (P omega).IsConservative,
        ∃ KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d),
        ∃ hKN : ∀ N, IsMarkovKernel (KN N),
        ∃ K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d),
        ∃ hK : IsMarkovKernel K,
          (∀ᵐ omega ∂law,
            Tendsto (infraredPartialSum omega) atTop (nhds (H omega)) ∧
            (∀ N, ∃ D :
                SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum
                  (SpatialCoordinates d),
              (∀ mu, DenseRange (D.operator mu)) ∧
              SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
                (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) D ∧
              ∀ (mu : Semigroup.PositiveShift)
                (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ)
                (x : SpatialCoordinates d),
                D.solution mu f x =
                  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
                    kernelIntegral (PN N omega (Real.toNNReal t)) f x) ∧
            (∀ N I x,
              (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
                SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x) ∧
            (∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
              SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x) ∧
            Continuous (fun x ↦ jointPathProbabilityMeasure K hK omega x) ∧
            (∀ B : Set (SpatialCoordinates d), IsCompact B →
              ∀ epsilon : ℝ, 0 < epsilon → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
                ∀ x ∈ B,
                  pathLevyProkhorovDist
                    (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                    (jointPathProbabilityMeasure K hK omega x) < epsilon) ∧
            (∀ (t : ℝ≥0) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ),
              Continuous (kernelIntegral (P omega t) f)) ∧
            (∃ mu : Measure (SpatialCoordinates d),
              MeasuresConvergeLocally (fun N ↦ cutoffSpeedMeasure M H omega N) mu ∧
              IsLocallyFiniteMeasure mu ∧ NullSingletonClass mu ∧ mu.IsOpenPosMeasure ∧
              SemigroupSymmetric (P omega) mu) ∧
            HasStrongMarkovRestart K omega ∧ HasFiniteMeanExits K omega) ∧
          ∀ (x : SpatialCoordinates d) (F : BoundedContinuousFunction (DiffusionPath d) ℝ),
            Tendsto
              (fun N ↦ ∫ omega,
                (∫ path, F (physicalRescaledPath M N path)
                  ∂(KN 0 (omega, (3 : ℝ) ^ N • x))) ∂law)
              atTop
              (nhds (∫ omega, (∫ path, F path ∂(K (omega, x))) ∂law)) := by
  refine ⟨aux_mfd_convergence_delta0 hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp BD BDQ hcontract,
    aux_mfd_convergence_delta0_pos hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp BD BDQ hcontract, ?_⟩
  intro M Rm Sreg It hMpos hMle forget nu law
  have hle1 : M.delta ≤ Classical.choose (finiteDimensional_cutoff (d := d) hd) := by
    unfold aux_mfd_convergence_delta0 at hMle
    exact hMle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hHex := exists_infraredCharacterization hd M
  rcases hHex with ⟨H, hH⟩
  have hFD := (Classical.choose_spec (finiteDimensional_cutoff (d := d) hd)).2 M H hH hle1
  have hsel := hlife M H hH hFD
  rcases hsel with ⟨PN, KN, hKN, hin, hinput⟩
  have hcore := aux_mfd_convergence_core hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp BD BDQ hcontract M Rm Sreg It
    hMpos hMle H hH PN KN hKN hin hinput
  rcases hcore with ⟨P, hP, K, hK, hae, hann⟩
  exact ⟨H, hH.1, PN, hin.2.1, P, hP, KN, hKN, K, hK, hae, hann⟩

end SubdiffusiveProcess.Paper
