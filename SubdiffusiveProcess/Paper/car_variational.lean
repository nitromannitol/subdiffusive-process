module

public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_J
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
public import SubdiffusiveProcess.Main.MeasureTraceCharacterization
public import SubdiffusiveProcess.Main.CubeFractionalL2Norm
public import SubdiffusiveProcess.Main.HalfFractionalOrder
public import SubdiffusiveProcess.Sobolev.ResponseSpace
public import SubdiffusiveProcess.ResponseMoments.DirichletForm
public import SubdiffusiveProcess.VariationalResponses.KilledInverse
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Probability.CubeMassMartingale
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Inputs.MarkovProcesses
public import MarkovProcess.Trajectory.StoppingLtTop
public import MarkovProcess.Path.ExitTime
public import MarkovProcess.Killed.Nested
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.Packet455DirichletForm
public import SubdiffusiveProcess.Vocab.Ahom
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.prop_as_forms
public import SubdiffusiveProcess.Paper.lem_as_coarse
public import SubdiffusiveProcess.Paper.lem_as_regularity
public import SubdiffusiveProcess.Paper.prop_chaos_growth
public import SubdiffusiveProcess.Paper.prop_uniform_resolvent
public import SubdiffusiveProcess.Paper.prop_uniform_resolvent_subsequence_bridge
public import SubdiffusiveProcess.Paper.inputs_classical_mosco_liminf
public import SubdiffusiveProcess.Paper.prop_speed_resolvent
public import SubdiffusiveProcess.Paper.in_normalization
public import SubdiffusiveProcess.Paper.limiting_local_energy
public import SubdiffusiveProcess.Paper.speed_trace_completion
public import SubdiffusiveProcess.Paper.lem_19
public import SubdiffusiveProcess.Paper.in_killed_inverse
public import SubdiffusiveProcess.Paper.cutoff_campanato_bound
public import SubdiffusiveProcess.Paper.cutoff_lifetime_package
public import SubdiffusiveProcess.Paper.car_resolvent_abs_cont
public import SubdiffusiveProcess.Paper.car_rn_continuous_version
public import SubdiffusiveProcess.Paper.lem_band
public import SubdiffusiveProcess.Paper.catalog_cutoff_existence
public import SubdiffusiveProcess.ResponseMoments.LocalEnergyAux
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import SubdiffusiveProcess.Paper.lem_cutoffs
public import SubdiffusiveProcess.VariationalResponses.CellAssembly
public import SubdiffusiveProcess.Sobolev.GradientEnergyMeasure
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import SubdiffusiveProcess.Paper.conv_represented_sequence
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Analysis.Convex.Measure
public import SubdiffusiveProcess.MultiplicativeChaos.SpeedBasic
public import SubdiffusiveProcess.Paper.torsion_bound
public import SubdiffusiveProcess.Section10.TransitionPositiveTests
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationKernel

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory ProbabilityTheory Topology Set TopologicalSpace
open MarkovProcess
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped CompactlySupported ENNReal NNReal LevyProkhorov BigOperators

noncomputable section
namespace SubdiffusiveProcess.Paper

section CutSupply
open Metric
open scoped ContDiff Manifold

/-- A native harmonic function with the given zero trace difference satisfies
the project's Dirichlet equation with zero source, with unchanged value and gradient. -/
theorem aux_car_variational_cut_harmonic_dirichlet_bridge
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (A : PositiveCoefficient Q) (a : SpatialCoordinates d → ℝ)
    (hA : (fun x => A.val x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] a)
    (u b : Homogenization.H1Function (Q : Set (SpatialCoordinates d)))
    (hu : SubdiffusiveProcess.CoarseGrainingVocab.IsWeaklyHarmonicOn a
      (Q : Set (SpatialCoordinates d)) u)
    (hb : SubdiffusiveProcess.CoarseGrainingVocab.HasZeroTraceDifferenceOn
      (Q : Set (SpatialCoordinates d)) u b) :
    SolvesDirichlet A (fun _ => 0)
      ⟨sobolevDataOfH1 b, sobolevDataOfH1_mem_weak b⟩
      ⟨sobolevDataOfH1 u, sobolevDataOfH1_mem_weak u⟩ := by
  obtain ⟨v, hv, hv1, hv2⟩ := killed_of_zeroTraceDifference hb
  have heq : sobolevDataOfH1 u - sobolevDataOfH1 b = v := by
    refine Prod.ext ?_ ?_
    · apply Lp.ext
      exact ((Lp.coeFn_sub _ _).trans
        ((sobolevDataOfH1_fst_coeFn u).sub (sobolevDataOfH1_fst_coeFn b))).trans hv1.symm
    · funext i
      apply Lp.ext
      exact ((Lp.coeFn_sub _ _).trans
        ((sobolevDataOfH1_snd_coeFn u i).sub
          (sobolevDataOfH1_snd_coeFn b i))).trans (hv2 i).symm
  refine ⟨heq ▸ hv, ?_⟩
  intro w
  obtain ⟨wH, _, hwgrad⟩ := exists_nativeH10Function_of_killedSobolevGraph w
  rw [sobolevCoefficientForm_eq_upstream_integral A a hA]
  simp only [zero_mul, integral_zero]
  rw [← hu wH]
  apply integral_congr_ae
  have hgu := ae_all_iff.2 (fun i => sobolevDataOfH1_snd_coeFn u i)
  filter_upwards [hgu] with x hx
  rw [hwgrad]
  rw [vecDot_matVecMul_scalarCoeffField]
  simp only [Homogenization.vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hx i]; ring

/-- The native harmonic energy is the graph energy of the same Sobolev datum. -/
theorem aux_car_variational_cut_harmonic_energy
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (A : PositiveCoefficient Q) (a : SpatialCoordinates d → ℝ)
    (hA : (fun x => A.val x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] a)
    (u : Homogenization.H1Function (Q : Set (SpatialCoordinates d))) :
    sobolevCoefficientForm A (sobolevDataOfH1 u) (sobolevDataOfH1 u) =
      SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.energy a (Q : Set (SpatialCoordinates d)) u := by
  rw [sobolevCoefficientForm_eq_upstream_integral A a hA]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.2 (fun i => sobolevDataOfH1_snd_coeFn u i)] with x hx
  rw [vecDot_matVecMul_scalarCoeffField]
  simp only [Homogenization.vecDot]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [hx i]

/-- Smooth plateau data for the harmonic mesh construction, without a catalogue choice. -/
theorem aux_car_variational_cut_smooth_plateau {d : ℕ}
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (K O : Set (SpatialCoordinates d)) (hK : IsCompact K) (hO : IsOpen O)
    (hKO : K ⊆ O) (hOQ : closure O ⊆ (centeredCube z R hR : Set (SpatialCoordinates d))) :
    ∃ θ : SpatialCoordinates d → ℝ, ∃ W : Set (SpatialCoordinates d),
      ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧ tsupport θ ⊆ O ∧
      IsOpen W ∧ K ⊆ W ∧ W ⊆ O ∧
      (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) ∧ ∀ x ∈ W, θ x = 1 := by
  obtain ⟨U, hU, hKU, hUO⟩ := normal_exists_closure_subset hK.isClosed hO hKO
  obtain ⟨f, hf1, hf0, hfr⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ, SpatialCoordinates d)) hK.isClosed
    (show K ⊆ interior U by simpa only [hU.interior_eq] using hKU)
  obtain ⟨V, hV, hKV, hVf⟩ := mem_nhdsSet_iff_exists.1 hf1
  have hs : Function.support (fun x => f x) ⊆ U := by
    intro x hx
    by_contra h
    exact hx (hf0 x h)
  have hts : tsupport (fun x => f x) ⊆ O := (closure_mono hs).trans hUO
  have hcomp : HasCompactSupport (fun x => f x) :=
    IsCompact.of_isClosed_subset (isCompact_closure_centeredCube z hR)
      (isClosed_tsupport _) ((hts.trans (subset_closure.trans hOQ)).trans subset_closure)
  refine ⟨(fun x => f x), V ∩ U, ?_, hcomp, hts, hV.inter hU,
    fun x hx => ⟨hKV hx, hKU hx⟩, fun x hx => hUO (subset_closure hx.2),
    hfr, fun x hx => hVf hx.1⟩
  exact contMDiff_iff_contDiff.1 f.contMDiff

/-- Extend an interior ball-growth estimate to boundary centers, using the total
mass for radii above one half. -/
theorem aux_car_variational_cut_growth_on_closure
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (ν : Measure X) (Q : Set X) (E t : ℝ) (hE : 0 ≤ E) (ht : 0 ≤ t)
    (htotal : ν Set.univ ≤ ENNReal.ofReal E)
    (hinside : ∀ x ∈ Q, ∀ r : ℝ, 0 < r → r ≤ 1 →
      ν (Metric.ball x r) ≤ ENNReal.ofReal (E * r ^ t)) :
    ∀ x ∈ closure Q, ∀ r : ℝ, 0 < r → r ≤ 1 →
      ν (Metric.ball x r) ≤ ENNReal.ofReal ((2 : ℝ) ^ t * (E + E) * r ^ t) := by
  intro x hx r hr _
  have heq : (E + E) * (2 * r) ^ t = (2 : ℝ) ^ t * (E + E) * r ^ t := by
    rw [Real.mul_rpow (by norm_num) hr.le]
    ring
  by_cases hsmall : r ≤ 1 / 2
  · obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx r hr
    have hsub : Metric.ball x r ⊆ Metric.ball y (2 * r) := by
      intro a ha
      apply lt_of_le_of_lt (dist_triangle a x y)
      have har : dist a x < r := ha
      linarith
    refine ((measure_mono hsub).trans (hinside y hy (2 * r) (by positivity)
      (by linarith))).trans ?_
    apply ENNReal.ofReal_le_ofReal
    rw [← heq]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hE)
      (Real.rpow_nonneg (by positivity) _)
  · refine ((measure_mono (Set.subset_univ _)).trans htotal).trans ?_
    apply ENNReal.ofReal_le_ofReal
    rw [← heq]
    have hp : 1 ≤ (2 * r) ^ t := Real.one_le_rpow (by linarith) ht
    exact (le_add_of_nonneg_right hE).trans
      (le_mul_of_one_le_right (add_nonneg hE hE) hp)

/-- The energy measure in HCUT is exactly the existing local gradient energy. -/
theorem aux_car_variational_cut_energy_measure
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (A : PositiveCoefficient Q) (u : SobolevData Q)
    (S : Set (SpatialCoordinates d)) (hS : MeasurableSet S) :
    ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
      (fun x => ENNReal.ofReal (A.val x * ∑ i : Fin d, (u.2 i x) ^ 2))) S =
      ENNReal.ofReal (localGradientEnergy A hS (sobolevGradient u)) := by
  let ν := (volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
    (fun x => ENNReal.ofReal (∑ i : Fin d, A.val x * (u.2 i x) ^ 2))
  have hν := gradientEnergy_withDensity_finite_and_real A (sobolevGradient u)
  have : IsFiniteMeasure ν := hν.1
  calc
    _ = ν S := by simp only [ν, Finset.mul_sum]
    _ = ENNReal.ofReal (ν.real S) := (ENNReal.ofReal_toReal (measure_ne_top ν S)).symm
    _ = _ := congrArg ENNReal.ofReal (hν.2 S hS)

theorem aux_car_variational_cut_local_energy_inter_domain
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (A : PositiveCoefficient Q) (g : HilbertGradient Q)
    (S : Set (SpatialCoordinates d)) (hS : MeasurableSet S) :
    localGradientEnergy A hS g =
      localGradientEnergy A (hS.inter Q.isOpen.measurableSet) g := by
  simp only [localGradientEnergy_eq_integral, Measure.restrict_restrict hS,
    Measure.restrict_restrict (hS.inter Q.isOpen.measurableSet),
    Set.inter_assoc, Set.inter_self]

/-- Uniform zero-source Dirichlet estimates, with the exponents needed for cutoffs. -/
def aux_car_variational_cut_ZeroDirProp {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (A : PositiveCoefficient (centeredCube z r hr)) (K : ℝ) : Prop :=
  ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ), ContDiff ℝ 2 phi →
    c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
    ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
      ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
      SolvesDirichlet A (fun _ => 0) b u →
      (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) →
        0 < rad → rad ≤ 1 →
        localGradientEnergy A
          (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
            K * Cphi ^ 2 * rad ^ ((d : ℝ) - 1 / 2)) ∧
      ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
        ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
        IsHolderOn (1 / 2) (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
        cAlphaNorm (1 / 2) (closedCube z r hr : Set (SpatialCoordinates d)) U ≤ K * Cphi

/-- The original-field regularity event, projected before constructing any plateau. -/
theorem aux_car_variational_cut_zero_dir_event {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Jc : in_J d) (Pc : in_poincare d hd Jc)
    (Xc : in_extension d hd Jc) (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ δ →
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
          ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 < K ∧
            ∀ N, aux_car_variational_cut_ZeroDirProp z r hr
              (cutoffPositiveCoefficient M H omega N z hr) K := by
  obtain ⟨δ, hδ, hregular⟩ := lem_as_regularity d hd Jc Pc Xc W D Cp Sf Step Dbase Interp
    (1 / 2) (3 / 4) ((d : ℝ) - 1 / 2) ((d : ℝ) - 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith)
  refine ⟨min 1 δ, lt_min one_pos hδ, ?_⟩
  intro M Rm Sreg It H HI hM z r hr
  filter_upwards [hregular M Rm Sreg It H HI hM z r hr] with omega homega
  obtain ⟨K, hK, hreg⟩ := homega
  refine ⟨K, hK, ?_⟩
  intro N phi Cphi hphi hC b u hb hu
  simpa only [zero_add] using! (hreg N).1 (fun _ => 0) 0 le_rfl aemeasurable_const
    (by simp) phi Cphi hphi hC b u hb hu

/-- The countable mesh-regularity event on one parent cube. -/
def aux_car_variational_cut_MeshRegProp {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) : Prop :=
  ∀ J : ℕ, ∀ k : OddGridIndex d (triadicHalf J), ∃ K : ℝ, 0 < K ∧
      ∀ N, aux_car_variational_cut_ZeroDirProp
        (oddGridCenter z R (triadicHalf J) k) (R / (2 * (triadicHalf J : ℝ) + 1))
        (div_pos hR (by positivity))
        (cutoffPositiveCoefficient (r := R / (2 * (triadicHalf J : ℝ) + 1))
          M H omega N (oddGridCenter z R (triadicHalf J) k)
          (div_pos hR (by positivity))) K

/-- A smooth compact plateau admits a fine mesh whose transition cells stay in the prescribed annulus. -/
theorem aux_car_variational_cut_plateau_mesh {d : ℕ} [NeZero d]
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (K O : Set (SpatialCoordinates d)) (hK : IsCompact K) (hO : IsOpen O)
    (hKO : K ⊆ O) (hOQ : closure O ⊆ (centeredCube z R hR : Set (SpatialCoordinates d))) :
    ∃ (θ : SpatialCoordinates d → ℝ) (V₀ : Set (SpatialCoordinates d)) (J : ℕ),
      ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧ tsupport θ ⊆ O ∧
      IsOpen V₀ ∧ K ⊆ V₀ ∧ V₀ ⊆ O ∧
      (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) ∧ (∀ x ∈ V₀, θ x = 1) ∧
      R / (2 * (triadicHalf J : ℝ) + 1) ≤ 1 ∧
      ∀ k : OddGridIndex d (triadicHalf J),
        (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ∩
          {x | 0 < θ x ∧ θ x < 1}).Nonempty →
        closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ⊆ O \ K := by
  obtain ⟨θ, V₀, hθ, hθcomp, hθsupp, hV₀, hKV₀, hV₀O, hθ01, hθ1⟩ :=
    aux_car_variational_cut_smooth_plateau z R hR K O hK hO hKO hOQ
  obtain ⟨δO, hδO, hthO⟩ := hθcomp.exists_thickening_subset_open hO hθsupp
  obtain ⟨δV, hδV, hthV⟩ := hK.exists_thickening_subset_open hV₀ hKV₀
  obtain ⟨J, hJ⟩ := aux_catalog_cutoff_existence_mesh_scale (R := R) (δ := min (min δO δV) 1) hR
    (lt_min (lt_min hδO hδV) (one_pos : (0 : ℝ) < 1))
  have hmesh : R / (3 : ℝ) ^ J < min δO δV := hJ.trans_le (min_le_left _ _)
  have hside : R / (2 * (triadicHalf J : ℝ) + 1) ≤ 1 := by
    rw [triadic_denominator]
    exact (hJ.trans_le (min_le_right _ _)).le
  have htrans := aux_catalog_cutoff_existence_transition_cells_apply z R hR θ K V₀ O
    hθ1 δO δV hthO hthV J hmesh
  exact ⟨θ, V₀, J, hθ, hθcomp, hθsupp, hV₀, hKV₀, hV₀O, hθ01, hθ1, hside, htrans⟩

/-- Native cell energy, ball growth, and Holder bounds for one coefficient. -/
def aux_car_variational_cut_HarmonicBound {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (a : SpatialCoordinates d → ℝ) (bH : Homogenization.H1Function (Q : Set (SpatialCoordinates d)))
    (E Gr Ho : ℝ) : Prop :=
  ∀ w : Homogenization.H1Function (Q : Set (SpatialCoordinates d)),
    SubdiffusiveProcess.CoarseGrainingVocab.IsWeaklyHarmonicOn a (Q : Set (SpatialCoordinates d)) w →
    SubdiffusiveProcess.CoarseGrainingVocab.HasZeroTraceDifferenceOn (Q : Set (SpatialCoordinates d)) w bH →
    ContinuousOn w.toFun (closure (Q : Set (SpatialCoordinates d))) →
    SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.energy a (Q : Set (SpatialCoordinates d)) w ≤ E ∧
    (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ r : ℝ, 0 < r → r ≤ 1 →
      ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal (a y * ∑ i : Fin d, (w.grad y i) ^ 2))) (Metric.ball x r) ≤
          ENNReal.ofReal (Gr * r ^ ((d : ℝ) - 1 / 2))) ∧
    (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ y ∈ closure (Q : Set (SpatialCoordinates d)),
      |w.toFun x - w.toFun y| ≤ Ho * (Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)) ^ (1 / 2 : ℝ))

/-- Original-field zero-source regularity bounds all native cell solutions with a fixed datum. -/
theorem aux_car_variational_cut_zero_cell_bounds {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (c : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hside : r ≤ 1)
    (θ : SpatialCoordinates d → ℝ) (hθ : ContDiff ℝ 2 θ)
    (bH : Homogenization.H1Function (centeredCube c r hr : Set (SpatialCoordinates d)))
    (hbH : bH.toFun = θ) (Kc : ℝ) (hKc : 0 < Kc)
    (hreg : ∀ N, aux_car_variational_cut_ZeroDirProp c r hr
      (cutoffPositiveCoefficient M H omega N c hr) Kc) :
    ∃ E Gr Ho : ℝ, 0 ≤ E ∧ 0 ≤ Gr ∧ 0 ≤ Ho ∧
      ∀ N, aux_car_variational_cut_HarmonicBound (centeredCube c r hr)
        (cutoffCoefficient M H omega N) bH E Gr Ho := by
  let Q := centeredCube c r hr
  let t : ℝ := (d : ℝ) - 1 / 2
  have ht : 0 ≤ t := by
    dsimp [t]
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  let Cθ := max 1 (c2Norm (closedCube c r hr : Set (SpatialCoordinates d)) θ)
  have hCθ : 0 ≤ Cθ := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  let E := Kc * Cθ ^ 2
  have hE : 0 ≤ E := mul_nonneg hKc.le (sq_nonneg _)
  refine ⟨E, (2 : ℝ) ^ t * (E + E), Kc * Cθ, hE, by positivity, by positivity, ?_⟩
  intro N w hwh hwt hwc
  let A := cutoffPositiveCoefficient M H omega N c hr
  let wS : weakSobolevGraph Q := ⟨sobolevDataOfH1 w, sobolevDataOfH1_mem_weak w⟩
  let bS : weakSobolevGraph Q := ⟨sobolevDataOfH1 bH, sobolevDataOfH1_mem_weak bH⟩
  have hA := aux_lem_cutoffs_positiveCoefficient_ae M H omega N c hr
  have hsolve : SolvesDirichlet A (fun _ => 0) bS wS :=
    aux_car_variational_cut_harmonic_dirichlet_bridge A _ hA w bH hwh hwt
  have hbval : ((bS : SobolevData Q).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] θ :=
    (sobolevDataOfH1_fst_coeFn bH).trans (Filter.Eventually.of_forall (fun x => congrFun hbH x))
  obtain ⟨hg, U, hUc, hwU, hUh, hUn⟩ := (hreg N) θ Cθ hθ (le_max_right _ _)
    bS wS hbval hsolve
  have hcenter : c ∈ (Q : Set (SpatialCoordinates d)) := Metric.mem_ball_self (half_pos hr)
  have hsub : (Q : Set (SpatialCoordinates d)) ⊆ Metric.ball c 1 :=
    Metric.ball_subset_ball (by linarith [hside])
  have hballQ : Metric.ball c 1 ∩ (centeredCube c r hr : Set (SpatialCoordinates d)) =
      (centeredCube c r hr : Set (SpatialCoordinates d)) :=
    Set.inter_eq_right.2 hsub
  have hgraph : sobolevCoefficientForm A (wS : SobolevData Q) (wS : SobolevData Q) ≤ E := by
    have hb := hg c 1 hcenter one_pos le_rfl
    rw [← localGradientEnergy_domain_eq_sobolevCoefficientForm A (wS : SobolevData Q)]
    simpa only [localGradientEnergy_eq_integral, hballQ, Real.one_rpow, mul_one] using hb
  let ν := (volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
    (fun x => ENNReal.ofReal (A.val x * ∑ i : Fin d, ((wS : SobolevData Q).2 i x) ^ 2))
  have htotal : ν Set.univ ≤ ENNReal.ofReal E := by
    rw [aux_car_variational_cut_energy_measure A (wS : SobolevData Q) Set.univ MeasurableSet.univ,
      _root_.SubdiffusiveProcess.ResponseMoments.localGradientEnergy_univ]
    exact ENNReal.ofReal_le_ofReal hgraph
  have hinside : ∀ x ∈ (Q : Set (SpatialCoordinates d)), ∀ s : ℝ, 0 < s → s ≤ 1 →
      ν (Metric.ball x s) ≤ ENNReal.ofReal (E * s ^ t) := by
    intro x hx s hs hs1
    rw [aux_car_variational_cut_energy_measure A (wS : SobolevData Q) _ isOpen_ball.measurableSet,
      aux_car_variational_cut_local_energy_inter_domain]
    apply ENNReal.ofReal_le_ofReal
    simpa only [zero_add] using hg x s hx hs hs1
  have hbound := aux_car_variational_cut_growth_on_closure ν (Q : Set (SpatialCoordinates d))
    E t hE ht htotal hinside
  have hden : (fun x => ENNReal.ofReal (A.val x * ∑ i : Fin d,
      ((wS : SobolevData Q).2 i x) ^ 2)) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      (fun x => ENNReal.ofReal (cutoffCoefficient M H omega N x * ∑ i : Fin d, (w.grad x i) ^ 2)) :=
    aux_lem_cutoffs_cc_density_congr _ _ _ _ hA (fun i => sobolevDataOfH1_snd_coeFn w i)
  have hEq := withDensity_congr_ae hden
  have hcl : closure (Q : Set (SpatialCoordinates d)) =
      (closedCube c r hr : Set (SpatialCoordinates d)) :=
    aux_lem_cutoffs_geom_closure_eq c r hr
  have hwUpoint := aux_lem_cutoffs_eqOn_closure (Q : Set (SpatialCoordinates d)) Q.isOpen
    w.toFun U hwc hUc.continuousOn ((sobolevDataOfH1_fst_coeFn w).symm.trans hwU)
  have hUbound := aux_lem_cutoffs_pair_bound_of_holder (by norm_num : (0 : ℝ) < 1 / 2)
    hUh (by simpa only [zero_add] using hUn)
  refine ⟨?_, ?_, ?_⟩
  · rw [← aux_car_variational_cut_harmonic_energy A _ hA w]
    exact hgraph
  · intro x hx s hs hs1
    rw [← hEq]
    exact hbound x hx s hs hs1
  · intro x hx y hy
    rw [hwUpoint x hx, hwUpoint y hy]
    exact hUbound x (hcl ▸ hx) y (hcl ▸ hy)

/-- Uniform energy and Holder bounds for the actual cutoff sequence. -/
def aux_car_variational_cut_CutoffFamily {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z R hR),
      ‖(u : SobolevData (centeredCube z R hR)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z R hR)) u‖)
    (K O : Set (SpatialCoordinates d)) : Prop :=
  ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → (killedResponseSpace hP).space)
      (chic : ℕ → SpatialCoordinates d → ℝ) (B C : ℝ),
    IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ 0 ≤ C ∧ ∀ n : ℕ,
      ContinuousOn (chic n) (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
      ((chi n).val.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] chic n ∧
      (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
        0 ≤ chic n x ∧ chic n x ≤ 1) ∧
      (∀ x ∈ V, chic n x = 1) ∧
      (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
      responseForm (killedResponseSpace hP)
        (cutoffPositiveCoefficient M H omega n z hR) (chi n) (chi n) ≤ B ∧
      (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)), ∀ rr : ℝ,
        0 < rr → rr ≤ 1 →
        ((volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal ((cutoffPositiveCoefficient M H omega n z hR).val y *
            ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
          (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ ((d : ℝ) - 1 / 2))) ∧
      (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
        ∀ y ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
        |chic n x - chic n y| ≤ C * (Real.sqrt (∑ i : Fin d, (x i - y i)^2)) ^ (1 / 2 : ℝ))

/-- Finite-cell Dirichlet regularity constructs the cutoff family on a fixed cube. -/
theorem aux_car_variational_cut_strong_cutoffs {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z R hR),
      ‖(u : SobolevData (centeredCube z R hR)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z R hR)) u‖)
    (omega : BilateralField d)
    (homega : aux_car_variational_cut_MeshRegProp M H omega z R hR) :
    ∀ (K O : Set (SpatialCoordinates d)), IsCompact K → IsOpen O → K ⊆ O →
      closure O ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) →
      aux_car_variational_cut_CutoffFamily M H omega z R hR hP K O := by
  classical
  have : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩
  intro K O hK hO hKO hOQ
  obtain ⟨θ, V₀, J, hθ, hθcomp, hθsupp, hV₀, hKV₀, hV₀O, hθ01, hθ1, hside, htrans⟩ :=
    aux_car_variational_cut_plateau_mesh z R hR K O hK hO hKO hOQ
  let θH := Homogenization.H1Function.ofContDiff (centeredCube z R hR).isOpen
    (hθ.of_le (by simp)) hθcomp
  let t : ℝ := (d : ℝ) - 1 / 2
  have ht : 0 ≤ t := by
    dsimp [t]
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hcell : ∀ k : OddGridIndex d (triadicHalf J), ∃ E Gr Ho : ℝ,
      0 ≤ E ∧ 0 ≤ Gr ∧ 0 ≤ Ho ∧ ∀ N, aux_car_variational_cut_HarmonicBound
        (oddGridCell z R hR (triadicHalf J) k) (cutoffCoefficient M H omega N)
        (θH.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
          (oddGridCell_subset z hR (triadicHalf J) k)) E Gr Ho := by
    intro k
    obtain ⟨Kc, hKc, hreg⟩ := homega J k
    exact aux_car_variational_cut_zero_cell_bounds hd M H omega
      (oddGridCenter z R (triadicHalf J) k) (R / (2 * (triadicHalf J : ℝ) + 1))
      (div_pos hR (by positivity)) hside θ (hθ.of_le (by decide))
      (θH.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
        (oddGridCell_subset z hR (triadicHalf J) k)) rfl Kc hKc hreg
  obtain ⟨chiH, chiS, chic, V, BE, BG, BH, hV, hKV, hVO, hBE, hBG, hBH, hchi, _⟩ :=
    aux_lem_cutoffs_plateau_generic hd z R hR (killedResponseSpace hP) rfl
      (fun N => cutoffCoefficient M H omega N)
      (fun N => cutoffCoefficient_continuous M H omega N)
      (fun N => cutoffCoefficient_pos M H omega N)
      (fun N => cutoffPositiveCoefficient M H omega N z hR)
      (fun N => aux_lem_cutoffs_positiveCoefficient_ae M H omega N z hR)
      t (1 / 2) ht (by norm_num) θ θH rfl hθ K O V₀ J hO hOQ hKV₀ hV₀O
      hθ01 hθ1 hθsupp htrans hcell
  refine ⟨V, chiS, chic, max BE BG, BH, hV, hKV, hVO,
    hBE.trans (le_max_left _ _), hBH, ?_⟩
  intro N
  obtain ⟨_, hcc, hcae, hcrange, hc1, hc0, _, _, hce, hcg, hhol, hnorm⟩ := hchi N
  refine ⟨hcc, hcae, hcrange, hc1, hc0, hce.trans (le_max_left _ _), ?_, ?_⟩
  · intro x hx r hr hr1
    refine (hcg x hx r hr hr1).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hr.le _)
  · exact aux_lem_cutoffs_pair_bound_of_holder (by norm_num) hhol hnorm

/-- A compactly supported representative may be restricted to a smaller killed
Sobolev graph. Both its value and weak gradient are preserved on the smaller domain. -/
theorem aux_car_variational_cut_restrict_compact_datum
    {d : ℕ} {Q P : Opens (SpatialCoordinates d)}
    (hQ : Homogenization.IsOpenBoundedConvexDomain (Q : Set (SpatialCoordinates d)))
    (hQP : (Q : Set (SpatialCoordinates d)) ⊆ P)
    (u : killedSobolevGraph P) (f : SpatialCoordinates d → ℝ)
    (hae : (u.val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] f)
    (K : Set (SpatialCoordinates d)) (hK : IsCompact K) (hKQ : K ⊆ Q)
    (hf : ∀ x ∉ K, f x = 0) :
    ∃ v : killedSobolevGraph Q,
      (v.val.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] f ∧
      ∀ i : Fin d, (v.val.2 i : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] (u.val.2 i : SpatialCoordinates d → ℝ) := by
  obtain ⟨w, hw, hwgrad⟩ := exists_nativeH10Function_of_killedSobolevGraph u
  let b := H1ofAEEq (w.toH1Function.restrict Q.isOpen hQP) f
    (by simpa only [Homogenization.H1Function.restrict, hw] using hae.symm)
  obtain ⟨v, hv⟩ := Homogenization.memH10_of_compactSupport hQ b hK hKQ hf
  have hval : (sobolevDataOfH1 v.toH1Function).1 = (sobolevDataOfH1 b).1 := by
    apply Lp.ext
    exact (sobolevDataOfH1_fst_coeFn v.toH1Function).trans
      (Filter.EventuallyEq.trans (Filter.Eventually.of_forall (fun x => congrFun hv x))
        (sobolevDataOfH1_fst_coeFn b).symm)
  have hgrad : (sobolevDataOfH1 v.toH1Function).2 = (sobolevDataOfH1 b).2 := by
    apply weakSobolevGraph_gradient_unique (sobolevDataOfH1_mem_weak v.toH1Function)
    change ((sobolevDataOfH1 v.toH1Function).1, (sobolevDataOfH1 b).2) ∈ weakSobolevGraph Q
    rw [hval]
    exact sobolevDataOfH1_mem_weak b
  refine ⟨⟨sobolevDataOfH1 v.toH1Function, sobolevDataOfH1_mem_killed v⟩, ?_, ?_⟩
  · exact (sobolevDataOfH1_fst_coeFn v.toH1Function).trans
      (Filter.Eventually.of_forall (fun x => congrFun hv x))
  · intro i
    change (fun x => (sobolevDataOfH1 v.toH1Function).2 i x) =ᵐ[_] _
    rw [hgrad]
    have hb := sobolevDataOfH1_snd_coeFn b i
    change (fun x => (sobolevDataOfH1 b).2 i x) =ᵐ[_] fun x => w.toH1Function.grad x i at hb
    simpa only [hwgrad] using hb

/-- Local energy measures agree with restriction when coefficients and weak gradients agree. -/
theorem aux_car_variational_cut_restrict_energy_measure
    {d : ℕ} {Q P : Opens (SpatialCoordinates d)}
    (hQP : (Q : Set (SpatialCoordinates d)) ⊆ P)
    (A : PositiveCoefficient Q) (B : PositiveCoefficient P)
    (u : SobolevData Q) (v : SobolevData P)
    (hA : (fun x => A.val x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] fun x => B.val x)
    (hg : ∀ i : Fin d, (u.2 i : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] (v.2 i : SpatialCoordinates d → ℝ)) :
    (volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
        (fun x => ENNReal.ofReal (A.val x * ∑ i : Fin d, (u.2 i x)^2)) =
      ((volume.restrict (P : Set (SpatialCoordinates d))).withDensity
        (fun x => ENNReal.ofReal (B.val x * ∑ i : Fin d, (v.2 i x)^2))).restrict Q := by
  rw [restrict_withDensity Q.isOpen.measurableSet,
    Measure.restrict_restrict Q.isOpen.measurableSet, Set.inter_eq_left.2 hQP]
  exact withDensity_congr_ae (aux_lem_cutoffs_cc_density_congr _ _ _ _ hA hg)

/-- Restrict compactly supported cutoff data with its energy bound preserved. -/
theorem aux_car_variational_cut_restrict_cutoff_sequence {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z R hR),
      ‖(u : SobolevData (centeredCube z R hR)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z R hR)) u‖)
    (z' : SpatialCoordinates d) (R' : ℝ) (hR' : 0 < R')
    (hP' : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z' R' hR'),
      ‖(u : SobolevData (centeredCube z' R' hR')).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z' R' hR')) u‖)
    (hQP : (centeredCube z R hR : Set (SpatialCoordinates d)) ⊆ centeredCube z' R' hR')
    (O : Set (SpatialCoordinates d))
    (hOQ : closure O ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)))
    (chi : ℕ → (killedResponseSpace hP').space) (chic : ℕ → SpatialCoordinates d → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hae : ∀ n, ((chi n).val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z' R' hR' : Set (SpatialCoordinates d))] chic n)
    (hz : ∀ n, ∀ x ∈ (centeredCube z' R' hR' : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0)
    (he : ∀ n, responseForm (killedResponseSpace hP')
      (cutoffPositiveCoefficient M H omega n z' hR') (chi n) (chi n) ≤ B) :
    ∃ chiQ : ℕ → (killedResponseSpace hP).space, ∀ n,
      ((chiQ n).val.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] chic n ∧
      responseForm (killedResponseSpace hP)
        (cutoffPositiveCoefficient M H omega n z hR) (chiQ n) (chiQ n) ≤ B := by
  classical
  let Q := centeredCube z R hR
  let P := centeredCube z' R' hR'
  have hsub : (Q : Set (SpatialCoordinates d)) ⊆ P := hQP
  have hOcompact : IsCompact (closure O) :=
    (isCompact_closure_centeredCube z hR).of_isClosed_subset isClosed_closure
      (hOQ.trans subset_closure)
  let f := fun n => (P : Set (SpatialCoordinates d)).indicator (chic n)
  have hprops : ∀ n, ∃ v : killedSobolevGraph Q,
      (v.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] f n ∧
      ∀ i : Fin d, (v.val.2 i : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] ((chi n).val.2 i : SpatialCoordinates d → ℝ) := by
    intro n
    apply aux_car_variational_cut_restrict_compact_datum
      (isOpenBoundedConvexDomain_centeredCube z hR) hsub (chi n) (f n) ?_
      (closure O) hOcompact hOQ ?_
    · filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (hae n),
        ae_restrict_mem Q.isOpen.measurableSet] with x hx hxQ
      simpa only [f, Set.indicator_of_mem (hsub hxQ)] using hx
    · intro x hx
      by_cases hxP : x ∈ (P : Set (SpatialCoordinates d))
      · rw [show f n x = chic n x from Set.indicator_of_mem hxP _]
        exact hz n x hxP (fun hxO => hx (subset_closure hxO))
      · exact Set.indicator_of_notMem hxP _
  choose chiQ hchiQ hgrad using hprops
  refine ⟨chiQ, ?_⟩
  intro n
  have hden := aux_car_variational_cut_restrict_energy_measure hsub
    (cutoffPositiveCoefficient M H omega n z hR)
    (cutoffPositiveCoefficient M H omega n z' hR') (chiQ n).val (chi n).val
    ((aux_lem_cutoffs_positiveCoefficient_ae M H omega n z hR).trans
      (Filter.EventuallyEq.symm (ae_restrict_of_ae_restrict_of_subset hsub
        (aux_lem_cutoffs_positiveCoefficient_ae M H omega n z' hR')))) (hgrad n)
  have hmono := le_of_eq_of_le hden Measure.restrict_le_self
  constructor
  · filter_upwards [hchiQ n, ae_restrict_mem Q.isOpen.measurableSet] with x hx hxQ
    simpa only [f, Set.indicator_of_mem (hsub hxQ)] using hx
  · apply (ENNReal.ofReal_le_ofReal_iff hB).1
    have hm := hmono Set.univ
    rw [aux_car_variational_cut_energy_measure _ _ Set.univ MeasurableSet.univ,
      aux_car_variational_cut_energy_measure _ _ Set.univ MeasurableSet.univ,
      _root_.SubdiffusiveProcess.ResponseMoments.localGradientEnergy_univ, _root_.SubdiffusiveProcess.ResponseMoments.localGradientEnergy_univ] at hm
    exact hm.trans (ENNReal.ofReal_le_ofReal (he n))

/-- Uniform convergence of representatives on the cube implies convergence in its L2 space. -/
theorem aux_car_variational_cut_lp_of_uniform {d : ℕ}
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (uN : ℕ → DomainL2 (centeredCube z R hR)) (u : DomainL2 (centeredCube z R hR))
    (fN : ℕ → SpatialCoordinates d → ℝ) (f : SpatialCoordinates d → ℝ)
    (hN : ∀ n, (uN n : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] fN n)
    (hu : (u : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] f)
    (hconv : TendstoUniformlyOn fN f atTop (centeredCube z R hR : Set (SpatialCoordinates d))) :
    Tendsto uN atTop (𝓝 u) := by
  let Q : Set (SpatialCoordinates d) := centeredCube z R hR
  have hQmeas : MeasurableSet Q := (centeredCube z R hR).isOpen.measurableSet
  have hQfin : (volume.restrict Q) Q ≠ ⊤ := measure_ne_top _ _
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let L : ℝ := Real.sqrt ((volume.restrict Q) Q).toReal
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  let δ : ℝ := ε / (L + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hbound : δ * L < ε := by
    have heq : δ * (L + 1) = ε := div_mul_cancel₀ ε (by linarith)
    nlinarith
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv δ hδ] with n hn
  have hae : ∀ᵐ x ∂volume.restrict Q,
      ‖(uN n - u) x‖ ≤ Q.indicator (fun _ => δ) x := by
    filter_upwards [Lp.coeFn_sub (uN n) u, hN n, hu, ae_restrict_mem hQmeas]
      with x hx hxN hxu hxQ
    rw [hx, Pi.sub_apply, hxN, hxu, Real.norm_eq_abs, Set.indicator_of_mem hxQ]
    have hh := hn x hxQ
    simpa only [Real.dist_eq, abs_sub_comm] using hh.le
  rw [dist_eq_norm]
  exact (_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.norm_le_of_ae_indicator_bound hQmeas hQfin hδ.le hae).trans_lt hbound

/-- A uniformly bounded-energy, equicontinuous plateau has a plateau in the limit form domain. -/
theorem aux_car_variational_cut_limit_plateau {d : ℕ}
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (a : ℕ → PositiveCoefficient (centeredCube z R hR))
    (G : DomainL2 (centeredCube z R hR) →L[ℝ] DomainL2 (centeredCube z R hR))
    (F : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))))
    (hF : ∀ u, F.toClosedForm.energy u = limitFormEnergy G u)
    (hresponse : ∀ f : DomainL2 (centeredCube z R hR),
      Tendsto (fun n => inverseResponse S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop (𝓝 (inner ℝ f (G f))))
    (K O : Set (SpatialCoordinates d)) (hKO : K ⊆ O)
    (hOQ : closure O ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)))
    (chi : ℕ → S.space) (chic : ℕ → SpatialCoordinates d → ℝ) (B C : ℝ) (hC : 0 ≤ C)
    (hchi : ∀ n,
      ContinuousOn (chic n) (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
      ((chi n).val.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] chic n ∧
      (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
        0 ≤ chic n x ∧ chic n x ≤ 1) ∧
      (∀ x ∈ K, chic n x = 1) ∧
      (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
      responseForm S (a n) (chi n) (chi n) ≤ B ∧
      (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
        ∀ y ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
        |chic n x - chic n y| ≤ C * (Real.sqrt (∑ i : Fin d, (x i - y i)^2)) ^ (1 / 2 : ℝ))) :
    ∃ w ∈ F.toClosedForm.domain, ∃ g : SpatialCoordinates d → ℝ,
      Continuous g ∧ HasCompactSupport g ∧
      tsupport g ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
      (w : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] g ∧
      (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧ (∀ x ∈ K, g x = 1) ∧ ∀ x ∉ O, g x = 0 := by
  classical
  let Q : Set (SpatialCoordinates d) := centeredCube z R hR
  have hQopen : IsOpen Q := (centeredCube z R hR).isOpen
  have hQcomp : IsCompact (closure Q) := isCompact_closure_centeredCube z hR
  obtain ⟨σ, hσ, f, hfc, hconv⟩ := aux_lem_cutoffs_subseq_uniform (closure Q) hQcomp chic
    (fun n => (hchi n).1) (by norm_num : (0 : ℝ) < 1 / 2) hC
    (B := 1) (fun n x hx => by
      rw [abs_of_nonneg ((hchi n).2.2.1 x hx).1]
      exact ((hchi n).2.2.1 x hx).2)
    (fun n => (hchi n).2.2.2.2.2.2)
  have hf0 : ∀ x ∈ closure Q, x ∉ O → f x = 0 := by
    intro x hx hxo
    have hz : Tendsto (fun n => chic (σ n) x) atTop (𝓝 0) := by
      simpa only [(hchi _).2.2.2.2.1 x hx hxo] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    exact tendsto_nhds_unique (hconv.tendsto_at hx) hz
  have hf1 : ∀ x ∈ K, f x = 1 := by
    intro x hx
    have hxQ : x ∈ closure Q := subset_closure (hOQ (subset_closure (hKO hx)))
    have hz : Tendsto (fun n => chic (σ n) x) atTop (𝓝 1) := by
      simpa only [(hchi _).2.2.2.1 x hx] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    exact tendsto_nhds_unique (hconv.tendsto_at hxQ) hz
  have hfr : ∀ x ∈ closure Q, 0 ≤ f x ∧ f x ≤ 1 := by
    intro x hx
    exact ⟨ge_of_tendsto (hconv.tendsto_at hx)
      (Eventually.of_forall fun n => ((hchi (σ n)).2.2.1 x hx).1),
      le_of_tendsto (hconv.tendsto_at hx)
        (Eventually.of_forall fun n => ((hchi (σ n)).2.2.1 x hx).2)⟩
  let g : SpatialCoordinates d → ℝ := (closure Q).piecewise f 0
  have hgf : ∀ x ∈ closure Q, g x = f x := fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  have hgc : Continuous g := by
    apply continuous_piecewise _ _ continuousOn_const
    · intro x hx
      rw [isClosed_closure.frontier_eq] at hx
      apply hf0 x hx.1
      intro hxo
      have hxQ := hOQ (subset_closure hxo)
      exact hx.2 (interior_maximal subset_closure hQopen hxQ)
    · simpa only [closure_closure] using hfc
  have hgzero : ∀ x ∉ O, g x = 0 := by
    intro x hxo
    by_cases hxQ : x ∈ closure Q
    · rw [hgf x hxQ]; exact hf0 x hxQ hxo
    · exact Set.piecewise_eq_of_notMem _ _ _ hxQ
  have hgs : tsupport g ⊆ closure O := by
    apply closure_mono
    intro x hx
    by_contra hxo
    exact hx (hgzero x hxo)
  have hgcs : HasCompactSupport g :=
    hQcomp.of_isClosed_subset (isClosed_tsupport g) (hgs.trans (hOQ.trans subset_closure))
  have hgLp : MemLp g 2 (volume.restrict Q) := hgc.memLp_of_hasCompactSupport hgcs
  let w : DomainL2 (centeredCube z R hR) := hgLp.toLp g
  have hw : (w : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict Q] g := hgLp.coeFn_toLp
  have hconvg : TendstoUniformlyOn (fun n => chic (σ n)) g atTop Q := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv ε hε] with n hn x hx
    rw [hgf x (subset_closure hx)]
    exact hn x (subset_closure hx)
  have hlp := aux_car_variational_cut_lp_of_uniform z R hR
    (fun n => (chi (σ n)).val.1) w (fun n => chic (σ n)) g
    (fun n => (hchi (σ n)).2.1) hw hconvg
  have hlow := quadraticDual_le_liminf_responseForm S (fun n => a (σ n)) G
    (fun n => chi (σ n)) w (fun f => tendsto_const_nhds.inner hlp)
    (fun f => (hresponse f).comp hσ.tendsto_atTop)
  have hlim : liminf (fun n => ((responseForm S (a (σ n)) (chi (σ n)) (chi (σ n)) : ℝ) : EReal))
      atTop ≤ (B : EReal) := by
    apply liminf_le_of_frequently_le
    · exact (Eventually.of_forall fun n => EReal.coe_le_coe_iff.mpr
        (hchi (σ n)).2.2.2.2.2.1).frequently
    · exact isBoundedUnder_of_eventually_ge (a := (0 : EReal))
        (Eventually.of_forall fun n => EReal.coe_nonneg.mpr (responseForm_nonneg S _ _))
  have hwdom : w ∈ F.toClosedForm.domain := by
    apply F.toClosedForm.mem_domain_of_energy_lt_top
    rw [hF]
    exact hlow.trans_lt (hlim.trans_lt (EReal.coe_lt_top B))
  refine ⟨w, hwdom, g, hgc, hgcs, hgs.trans hOQ, hw, ?_, ?_, hgzero⟩
  · intro x
    by_cases hxQ : x ∈ closure Q
    · rw [hgf x hxQ]; exact hfr x hxQ
    · rw [show g x = 0 from Set.piecewise_eq_of_notMem _ _ _ hxQ]
      exact ⟨le_rfl, zero_le_one⟩
  · intro x hx
    rw [hgf x (subset_closure (hOQ (subset_closure (hKO hx))))]
    exact hf1 x hx

/-- Sums of level cutoffs approximate a nonnegative number to one mesh unit. -/
lemma aux_car_variational_cut_level_sum (δ : ℝ) (hδ : 0 < δ) (N : ℕ)
    (q : ℝ) (hq : 0 ≤ q) (hqN : q ≤ N * δ) (c : ℕ → ℝ)
    (hc : ∀ i < N, 0 ≤ c i ∧ c i ≤ 1)
    (hc1 : ∀ i < N, (i + 1 : ℕ) * δ ≤ q → c i = 1)
    (hc0 : ∀ i < N, q ≤ i * δ → c i = 0) :
    |δ * (∑ i ∈ Finset.range N, c i) - q| ≤ δ := by
  induction N with
  | zero =>
    have hq0 : q = 0 := by
      simp only [Nat.cast_zero, zero_mul] at hqN
      exact le_antisymm hqN hq
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero, hq0, sub_self, abs_zero]
    exact hδ.le
  | succ N ih =>
    by_cases hq' : q ≤ N * δ
    · rw [Finset.sum_range_succ, hc0 N (Nat.lt_succ_self N) hq', add_zero]
      exact ih hq' (fun i hi => hc i (Nat.lt_succ_of_lt hi))
        (fun i hi => hc1 i (Nat.lt_succ_of_lt hi))
        (fun i hi => hc0 i (Nat.lt_succ_of_lt hi))
    · have hsum : (∑ i ∈ Finset.range N, c i) = N := by
        calc
          _ = ∑ i ∈ Finset.range N, (1 : ℝ) := Finset.sum_congr rfl fun i hi =>
            hc1 i (Nat.lt_succ_of_lt (Finset.mem_range.mp hi))
              ((mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.mem_range.mp hi :
                  ((i + 1 : ℕ) : ℝ) ≤ N) hδ.le).trans (le_of_not_ge hq'))
          _ = N := by simp
      rw [Finset.sum_range_succ, hsum]
      have hcn := hc N (Nat.lt_succ_self N)
      rw [Nat.cast_add, Nat.cast_one] at hqN
      apply abs_le.mpr
      constructor <;> nlinarith

/-- A real vector space containing continuous plateau cutoffs uniformly
approximates every compactly supported continuous function. -/
theorem aux_car_variational_cut_positive_density_of_plateaus
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (A : Submodule ℝ (X → ℝ)) (Q : Set X)
    (hcut : ∀ (K O : Set X), IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ Q →
      ∃ g ∈ A, (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧
        (∀ x ∈ K, g x = 1) ∧ ∀ x ∉ O, g x = 0)
    (f : X → ℝ) (hf : Continuous f) (hfcs : HasCompactSupport f)
    (hfs : tsupport f ⊆ Q) (hf0 : ∀ x, 0 ≤ f x) (δ : ℝ) (hδ : 0 < δ) :
    ∃ g ∈ A, ∀ x, |g x - f x| ≤ δ := by
  classical
  obtain ⟨B, hB⟩ := hfcs.exists_bound_of_continuous hf
  obtain ⟨N, hN⟩ := exists_nat_gt (B / δ)
  have hBN : B ≤ N * δ := ((div_lt_iff₀ hδ).mp hN).le
  let K : ℕ → Set X := fun i => {x | ((i + 1 : ℕ) : ℝ) * δ ≤ f x}
  let O : ℕ → Set X := fun i => {x | (i : ℝ) * δ < f x}
  have hKsupport : ∀ i, K i ⊆ tsupport f := by
    intro i x hx
    apply subset_tsupport f
    have hipos : 0 < ((i + 1 : ℕ) : ℝ) * δ := mul_pos (by positivity) hδ
    exact ne_of_gt (hipos.trans_le hx)
  have hOcl : ∀ i, closure (O i) ⊆ tsupport f := by
    intro i
    apply closure_minimal _ (isClosed_tsupport f)
    intro x hx
    apply subset_tsupport f
    exact ne_of_gt ((mul_nonneg (Nat.cast_nonneg i) hδ.le).trans_lt hx)
  have hg : ∀ i : ℕ, ∃ g ∈ A, (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧
      (∀ x ∈ K i, g x = 1) ∧ ∀ x ∉ O i, g x = 0 := by
    intro i
    apply hcut (K i) (O i)
    · exact hfcs.of_isClosed_subset (isClosed_le continuous_const hf) (hKsupport i)
    · exact isOpen_lt continuous_const hf
    · intro x hx
      have hi : (i : ℝ) * δ < ((i + 1 : ℕ) : ℝ) * δ := by
        push_cast
        nlinarith
      exact hi.trans_le hx
    · exact (hOcl i).trans hfs
  choose g hgA hgr hg1 hg0 using hg
  refine ⟨δ • ∑ i ∈ Finset.range N, g i,
    A.smul_mem δ (A.sum_mem fun i hi => hgA i), ?_⟩
  intro x
  have hfx : f x ≤ N * δ := (le_abs_self _).trans ((hB x).trans hBN)
  have hx := aux_car_variational_cut_level_sum δ hδ N (f x) (hf0 x) hfx
    (fun i => g i x) (fun i _ => hgr i x)
    (fun i _ hi => hg1 i x hi) (fun i _ hi => hg0 i x (not_lt.mpr hi))
  simpa only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] using hx

/-- A real vector space containing continuous plateau cutoffs uniformly
approximates every compactly supported continuous function. -/
theorem aux_car_variational_cut_uniform_density_of_plateaus
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (A : Submodule ℝ (X → ℝ)) (Q : Set X)
    (hcut : ∀ (K O : Set X), IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ Q →
      ∃ g ∈ A, (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧
        (∀ x ∈ K, g x = 1) ∧ ∀ x ∉ O, g x = 0)
    (f : X → ℝ) (hf : Continuous f) (hfcs : HasCompactSupport f)
    (hfs : tsupport f ⊆ Q) (ε : ℝ) (hε : 0 < ε) :
    ∃ g ∈ A, ∀ x, |g x - f x| < ε := by
  classical
  let fp : X → ℝ := fun x => max (f x) 0
  let fm : X → ℝ := fun x => max (-f x) 0
  have hfp : Continuous fp := hf.max continuous_const
  have hfm : Continuous fm := hf.neg.max continuous_const
  have hfps : tsupport fp ⊆ tsupport f := tsupport_comp_subset (g := fun t : ℝ => max t 0) (by simp) f
  have hfms : tsupport fm ⊆ tsupport f := tsupport_comp_subset (g := fun t : ℝ => max (-t) 0) (by simp) f
  have hfpc : HasCompactSupport fp := hfcs.comp_left (g := fun t : ℝ => max t 0) (by simp)
  have hfmc : HasCompactSupport fm := hfcs.comp_left (g := fun t : ℝ => max (-t) 0) (by simp)
  obtain ⟨gp, hgp, hp⟩ := aux_car_variational_cut_positive_density_of_plateaus A Q hcut fp hfp hfpc (hfps.trans hfs)
    (fun x => le_max_right _ _) (ε / 3) (by positivity)
  obtain ⟨gm, hgm, hm⟩ := aux_car_variational_cut_positive_density_of_plateaus A Q hcut fm hfm hfmc (hfms.trans hfs)
    (fun x => le_max_right _ _) (ε / 3) (by positivity)
  refine ⟨gp - gm, A.sub_mem hgp hgm, ?_⟩
  intro x
  have hdecomp : f x = fp x - fm x := by
    dsimp [fp, fm]
    rcases le_total (f x) 0 with h | h
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
  have heq : (gp - gm) x - f x = (gp x - fp x) - (gm x - fm x) := by
    rw [hdecomp]
    simp only [Pi.sub_apply]
    ring
  rw [heq]
  exact (abs_sub (gp x - fp x) (gm x - fm x)).trans_lt
    ((add_le_add (hp x) (hm x)).trans_lt (by linarith))

/-- The vector space of continuous compactly supported representatives in a form domain. -/
def aux_car_variational_cut_continuous_core {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (F : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d)))) :
    Submodule ℝ (SpatialCoordinates d → ℝ) where
  carrier := {g | Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ (Q : Set (SpatialCoordinates d)) ∧
    ∃ w ∈ F.toClosedForm.domain, (w : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] g}
  zero_mem' := by
    refine ⟨continuous_const, ?_, ?_, 0, F.toClosedForm.domain.zero_mem, Lp.coeFn_zero ℝ 2 _⟩ <;>
      simp only [HasCompactSupport, tsupport_zero, isCompact_empty, empty_subset]
  add_mem' := by
    rintro f g ⟨hfc, hfcs, hfs, u, hu, hue⟩ ⟨hgc, hgcs, hgs, v, hv, hve⟩
    refine ⟨hfc.add hgc, hfcs.add hgcs, ?_, u + v, F.toClosedForm.domain.add_mem hu hv,
      (Lp.coeFn_add u v).trans (hue.add hve)⟩
    exact ((closure_mono (Function.support_add f g)).trans closure_union.le).trans
      (union_subset hfs hgs)
  smul_mem' := by
    rintro c f ⟨hfc, hfcs, hfs, u, hu, hue⟩
    exact ⟨hfc.const_smul c, hfcs.smul_left,
      (tsupport_smul_subset_right (fun _ => c) f).trans hfs,
      c • u, F.toClosedForm.domain.smul_mem c hu, (Lp.coeFn_smul c u).trans (hue.const_smul c)⟩

/-- On every cube inside a parent regularity event, every convergent inverse
subsequence has a uniformly dense continuous compact core. -/
theorem aux_car_variational_cut_hunif_fixed {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H)
    (omega : BilateralField d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z R hR),
      ‖(u : SobolevData (centeredCube z R hR)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z R hR)) u‖)
    (z' : SpatialCoordinates d) (R' : ℝ) (hR' : 0 < R')
    (hP' : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z' R' hR'),
      ‖(u : SobolevData (centeredCube z' R' hR')).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z' R' hR')) u‖)
    (hQP : closure (centeredCube z R hR : Set (SpatialCoordinates d)) ⊆ centeredCube z' R' hR')
    (hreg : aux_car_variational_cut_MeshRegProp M H omega z' R' hR')
    (s : ℕ → ℕ)
    (GNi : ℕ → DomainL2 (centeredCube z R hR) →L[ℝ] DomainL2 (centeredCube z R hR))
    (G : DomainL2 (centeredCube z R hR) →L[ℝ] DomainL2 (centeredCube z R hR))
    (hGNi : ∀ n f, GNi n f =
      (in_killed_inverse M H HI omega (s n) z hR hP f : SobolevData (centeredCube z R hR)).1)
    (hconv : Tendsto GNi atTop (𝓝 G))
    (F : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))))
    (hF : ∀ u, F.toClosedForm.energy u = limitFormEnergy G u) :
    ∀ f0 : SpatialCoordinates d → ℝ, Continuous f0 → HasCompactSupport f0 →
      tsupport f0 ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) →
      ∀ ε : ℝ, 0 < ε → ∃ w ∈ F.toClosedForm.domain, ∃ g : SpatialCoordinates d → ℝ,
        Continuous g ∧ HasCompactSupport g ∧
        tsupport g ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
        (w : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] g ∧
        ∀ x, |g x - f0 x| < ε := by
  let Q := centeredCube z R hR
  let P := centeredCube z' R' hR'
  let A := aux_car_variational_cut_continuous_core Q F
  have hsub : (Q : Set (SpatialCoordinates d)) ⊆ P := subset_closure.trans hQP
  have hresponse : ∀ f : DomainL2 Q,
      Tendsto (fun n => inverseResponse (killedResponseSpace hP)
        (cutoffPositiveCoefficient M H omega (s n) z hR)
        ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)) atTop
        (𝓝 (inner ℝ f (G f))) := by
    intro f
    have hev : Tendsto (fun n => GNi n f) atTop (𝓝 (G f)) :=
      ((continuous_id.clm_apply continuous_const).tendsto G).comp hconv
    have hh : Tendsto (fun n => inner ℝ f (GNi n f)) atTop (𝓝 (inner ℝ f (G f))) :=
      tendsto_const_nhds.inner hev
    simpa only [hGNi, in_killed_inverse, inverseResponse_eq_load] using! hh
  have hcut : ∀ (K O : Set (SpatialCoordinates d)), IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ Q →
      ∃ g ∈ A, (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧ (∀ x ∈ K, g x = 1) ∧ ∀ x ∉ O, g x = 0 := by
    intro K O hK hO hKO hOQ
    obtain ⟨V, chi, chic, B, C, hV, hKV, hVO, hB, hC, hc⟩ :=
      aux_car_variational_cut_strong_cutoffs hd M H z' R' hR' hP' omega hreg K O hK hO hKO
        (hOQ.trans hsub)
    obtain ⟨chiQ, hchiQ⟩ := aux_car_variational_cut_restrict_cutoff_sequence M H omega
      z R hR hP z' R' hR' hP' hsub O hOQ chi chic B hB
      (fun n => (hc n).2.1) (fun n => (hc n).2.2.2.2.1) (fun n => (hc n).2.2.2.2.2.1)
    have hdata : ∀ n,
        ContinuousOn (chic (s n)) (closure (Q : Set (SpatialCoordinates d))) ∧
        ((chiQ (s n)).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] chic (s n) ∧
        (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), 0 ≤ chic (s n) x ∧ chic (s n) x ≤ 1) ∧
        (∀ x ∈ K, chic (s n) x = 1) ∧
        (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), x ∉ O → chic (s n) x = 0) ∧
        responseForm (killedResponseSpace hP) (cutoffPositiveCoefficient M H omega (s n) z hR)
          (chiQ (s n)) (chiQ (s n)) ≤ B ∧
        (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ y ∈ closure (Q : Set (SpatialCoordinates d)),
          |chic (s n) x - chic (s n) y| ≤ C * (Real.sqrt (∑ i : Fin d, (x i - y i)^2)) ^ (1 / 2 : ℝ)) := by
      intro n
      obtain ⟨hcc, hae, hcr, hc1, hc0, he, hg, hhol⟩ := hc (s n)
      exact ⟨hcc.mono (hQP.trans subset_closure), (hchiQ (s n)).1,
        fun x hx => hcr x (subset_closure (hQP hx)), fun x hx => hc1 x (hKV hx),
        fun x hx hxo => hc0 x (hQP hx) hxo, (hchiQ (s n)).2,
        fun x hx y hy => hhol x (subset_closure (hQP hx)) y (subset_closure (hQP hy))⟩
    obtain ⟨w, hw, g, hgc, hgcs, hgs, hwg, hgr, hg1, hg0⟩ :=
      aux_car_variational_cut_limit_plateau z R hR (killedResponseSpace hP)
        (fun n => cutoffPositiveCoefficient M H omega (s n) z hR) G F hF hresponse K O hKO hOQ
        (fun n => chiQ (s n)) (fun n => chic (s n)) B C hC hdata
    exact ⟨g, ⟨hgc, hgcs, hgs, w, hw, hwg⟩, hgr, hg1, hg0⟩
  intro f0 hf0 hfcs hfs ε hε
  obtain ⟨g, hg, hgf⟩ := aux_car_variational_cut_uniform_density_of_plateaus A Q hcut f0 hf0 hfcs hfs ε hε
  obtain ⟨hgc, hgcs, hgs, w, hw, hwg⟩ := hg
  exact ⟨w, hw, g, hgc, hgcs, hgs, hwg, hgf⟩

/-- A cutoff supported inside a smaller cube retains its energy bounds there. -/
theorem aux_car_variational_cut_hcut_restrict {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z R hR),
      ‖(u : SobolevData (centeredCube z R hR)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z R hR)) u‖)
    (z' : SpatialCoordinates d) (R' : ℝ) (hR' : 0 < R')
    (hP' : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z' R' hR'),
      ‖(u : SobolevData (centeredCube z' R' hR')).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z' R' hR')) u‖)
    (hQP : closure (centeredCube z R hR : Set (SpatialCoordinates d)) ⊆ centeredCube z' R' hR')
    (hcut : aux_limiting_local_energy_HCUTProp M H z' R' hR' hP' id omega) :
    aux_limiting_local_energy_HCUTProp M H z R hR hP id omega := by
  classical
  let Q := centeredCube z R hR
  let P := centeredCube z' R' hR'
  have hsub : (Q : Set (SpatialCoordinates d)) ⊆ P := subset_closure.trans hQP
  intro K O hK hO hKO hOQ
  obtain ⟨V, chi, chic, B, hV, hKV, hVO, hB, hchi⟩ :=
    hcut K O hK hO hKO (hOQ.trans hsub)
  have hOcompact : IsCompact (closure O) :=
    (isCompact_closure_centeredCube z hR).of_isClosed_subset isClosed_closure
      (hOQ.trans subset_closure)
  let f := fun n => (P : Set (SpatialCoordinates d)).indicator (chic n)
  have hprops : ∀ n, ∃ v : killedSobolevGraph Q,
      (v.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] f n ∧
      ∀ i : Fin d, (v.val.2 i : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] ((chi n).val.2 i : SpatialCoordinates d → ℝ) := by
    intro n
    apply aux_car_variational_cut_restrict_compact_datum
      (isOpenBoundedConvexDomain_centeredCube z hR) hsub (chi n) (f n) ?_
      (closure O) hOcompact hOQ ?_
    · filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (hchi n).2.1,
        ae_restrict_mem Q.isOpen.measurableSet] with x hx hxQ
      simpa only [f, Set.indicator_of_mem (hsub hxQ)] using hx
    · intro x hx
      by_cases hxP : x ∈ (P : Set (SpatialCoordinates d))
      · rw [show f n x = chic n x from Set.indicator_of_mem hxP _]
        exact (hchi n).2.2.2.2.1 x hxP (fun hxO => hx (subset_closure hxO))
      · exact Set.indicator_of_notMem hxP _
  choose chiQ hchiQ hgrad using hprops
  refine ⟨V, chiQ, chic, B, hV, hKV, hVO, hB, ?_⟩
  intro n
  have hden := aux_car_variational_cut_restrict_energy_measure hsub
    (cutoffPositiveCoefficient M H omega n z hR)
    (cutoffPositiveCoefficient M H omega n z' hR') (chiQ n).val (chi n).val
    ((aux_lem_cutoffs_positiveCoefficient_ae M H omega n z hR).trans
      (Filter.EventuallyEq.symm (ae_restrict_of_ae_restrict_of_subset hsub
        (aux_lem_cutoffs_positiveCoefficient_ae M H omega n z' hR')))) (hgrad n)
  have hmono := le_of_eq_of_le hden Measure.restrict_le_self
  refine ⟨(hchi n).1.mono (hQP.trans subset_closure), ?_,
    fun x hx => (hchi n).2.2.1 x (hsub hx), (hchi n).2.2.2.1,
    fun x hx hxo => (hchi n).2.2.2.2.1 x (hsub hx) hxo, ?_, ?_⟩
  · filter_upwards [hchiQ n, ae_restrict_mem Q.isOpen.measurableSet] with x hx hxQ
    simpa only [f, Set.indicator_of_mem (hsub hxQ)] using hx
  · apply (ENNReal.ofReal_le_ofReal_iff hB).1
    have hm := hmono Set.univ
    rw [aux_car_variational_cut_energy_measure _ _ Set.univ MeasurableSet.univ,
      aux_car_variational_cut_energy_measure _ _ Set.univ MeasurableSet.univ,
      _root_.SubdiffusiveProcess.ResponseMoments.localGradientEnergy_univ, _root_.SubdiffusiveProcess.ResponseMoments.localGradientEnergy_univ] at hm
    exact hm.trans (ENNReal.ofReal_le_ofReal (hchi n).2.2.2.2.2.1)
  · intro x hx r hr hr1
    exact (hmono (Metric.ball x r)).trans ((hchi n).2.2.2.2.2.2 x (subset_closure (hQP hx)) r hr hr1)

/-- Finite-cell Dirichlet regularity constructs the cutoff family on a fixed cube. -/
theorem aux_car_variational_cut_hcut_of_mesh_regularity {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z R hR),
      ‖(u : SobolevData (centeredCube z R hR)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z R hR)) u‖)
    (omega : BilateralField d)
    (homega : aux_car_variational_cut_MeshRegProp M H omega z R hR) :
    aux_limiting_local_energy_HCUTProp M H z R hR hP id omega := by
  intro K O hK hO hKO hOQ
  obtain ⟨V, chi, chic, B, C, hV, hKV, hVO, hB, hC, hc⟩ :=
    aux_car_variational_cut_strong_cutoffs hd M H z R hR hP omega homega K O hK hO hKO hOQ
  refine ⟨V, chi, chic, B, hV, hKV, hVO, hB, ?_⟩
  intro n
  obtain ⟨hcc, hae, hcr, hc1, hc0, he, hg, _⟩ := hc n
  exact ⟨hcc, hae, fun x hx => hcr x (subset_closure hx), hc1, hc0, he, hg⟩

/-- Original-space HCUT on a fixed cube. The event contains every finite mesh
before the compact set, open set, and smooth plateau are chosen. -/
theorem aux_car_variational_cut_hcut_cube_event {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Jc : in_J d) (Pc : in_poincare d hd Jc)
    (Xc : in_extension d hd Jc) (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ δ →
        ∀ (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
          (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z R hR),
            ‖(u : SobolevData (centeredCube z R hR)).1‖ ≤
              K * ‖subspaceGradient (killedSobolevGraph (centeredCube z R hR)) u‖),
          ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            aux_limiting_local_energy_HCUTProp M H z R hR hP id omega := by
  obtain ⟨δ, hδ, hregular⟩ := aux_car_variational_cut_zero_dir_event hd Jc Pc Xc W Cp D Sf Step Dbase Interp
  refine ⟨δ, hδ, ?_⟩
  intro M Rm Sreg It H HI hM z R hR hP
  have hevents := ae_all_iff.2 fun J : ℕ => ae_all_iff.2 fun k : OddGridIndex d (triadicHalf J) =>
    hregular M Rm Sreg It H HI hM (oddGridCenter z R (triadicHalf J) k)
      (R / (2 * (triadicHalf J : ℝ) + 1)) (div_pos hR (by positivity))
  filter_upwards [hevents] with omega homega
  exact aux_car_variational_cut_hcut_of_mesh_regularity hd M H z R hR hP omega homega

/-- Original-space HCUT on a fixed cube. The event contains every finite mesh
before the compact set, open set, and smooth plateau are chosen. -/
theorem aux_car_variational_cut_mesh_cube_event {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Jc : in_J d) (Pc : in_poincare d hd Jc)
    (Xc : in_extension d hd Jc) (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ δ →
        ∀ (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
          ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            aux_car_variational_cut_MeshRegProp M H omega z R hR := by
  obtain ⟨δ, hδ, hregular⟩ := aux_car_variational_cut_zero_dir_event hd Jc Pc Xc W Cp D Sf Step Dbase Interp
  refine ⟨δ, hδ, ?_⟩
  intro M Rm Sreg It H HI hM z R hR
  have hevents := ae_all_iff.2 fun J : ℕ => ae_all_iff.2 fun k : OddGridIndex d (triadicHalf J) =>
    hregular M Rm Sreg It H HI hM (oddGridCenter z R (triadicHalf J) k)
      (R / (2 * (triadicHalf J : ℝ) + 1)) (div_pos hR (by positivity))
  filter_upwards [hevents] with omega homega
  exact homega

/-- A countable exhaustion and compact-support restriction yield the common HCUT event. -/
theorem aux_car_variational_cut_hcut_supply {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc) (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D0 : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_HI : InfraredCharacterization M H),
        M.delta ≤ delta0 →
        _root_.SubdiffusiveProcess.Paper.aux_limiting_local_energy_HCUT_prop M H := by
  have : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩
  obtain ⟨δ, hδ, hfixed⟩ := aux_car_variational_cut_hcut_cube_event hd Jc Pc Xc W Cp D0 Sf Step Dbase Interp
  refine ⟨δ, hδ, ?_⟩
  intro M Rm Sreg It H HI hM s hs
  refine ⟨id, strictMono_id, ?_⟩
  let radius : ℕ → ℝ := fun n => 2 * ((n : ℝ) + 1)
  have hrad : ∀ n, 0 < radius n := fun n => by dsimp [radius]; positivity
  have hp : ∀ n, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) (radius n) (hrad n)),
      ‖(u : SobolevData (centeredCube (0 : SpatialCoordinates d) (radius n) (hrad n))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) (radius n) (hrad n))) u‖ := by
    intro n
    exact (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
      (centeredCube (0 : SpatialCoordinates d) (radius n) (hrad n))
      (isOpenBoundedConvexDomain_centeredCube (0 : SpatialCoordinates d) (hrad n))).1
  have hevents := ae_all_iff.2 fun n : ℕ => hfixed M Rm Sreg It H HI hM
    0 (radius n) (hrad n) (hp n)
  filter_upwards [hevents] with omega homega
  intro z R hR _ hP
  obtain ⟨n, hn⟩ := exists_nat_gt (R / 2 + dist z 0)
  have hQP : closure (centeredCube z R hR : Set (SpatialCoordinates d)) ⊆
      centeredCube (0 : SpatialCoordinates d) (radius n) (hrad n) := by
    intro x hx
    rw [aux_lem_cutoffs_geom_closure_eq] at hx
    have hx' : dist x z ≤ R / 2 := hx
    change dist x 0 < radius n / 2
    have ht := dist_triangle x z 0
    dsimp [radius]
    linarith
  have hcut := aux_car_variational_cut_hcut_restrict M H omega z R hR hP
    0 (radius n) (hrad n) (hp n) hQP (homega n)
  intro K O hK hO hKO hOQ
  obtain ⟨V, chi, chic, B, hV, hKV, hVO, hB, hchi⟩ := hcut K O hK hO hKO hOQ
  exact ⟨V, chi ∘ s, chic ∘ s, B, hV, hKV, hVO, hB, fun n => hchi (s n)⟩

/-- A countable exhaustion and compact-support restriction yield the common HUNIF event. -/
theorem aux_car_variational_cut_hunif_supply {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc) (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D0 : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H),
        M.delta ≤ delta0 →
        _root_.SubdiffusiveProcess.Paper.aux_limiting_local_energy_HUNIF_prop M H HI := by
  have : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩
  obtain ⟨δ, hδ, hfixed⟩ := aux_car_variational_cut_mesh_cube_event hd Jc Pc Xc W Cp D0 Sf Step Dbase Interp
  refine ⟨δ, hδ, ?_⟩
  intro M Rm Sreg It H HI hM s hs
  refine ⟨id, strictMono_id, ?_⟩
  let radius : ℕ → ℝ := fun n => 2 * ((n : ℝ) + 1)
  have hrad : ∀ n, 0 < radius n := fun n => by dsimp [radius]; positivity
  have hp : ∀ n, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) (radius n) (hrad n)),
      ‖(u : SobolevData (centeredCube (0 : SpatialCoordinates d) (radius n) (hrad n))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) (radius n) (hrad n))) u‖ := by
    intro n
    exact (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
      (centeredCube (0 : SpatialCoordinates d) (radius n) (hrad n))
      (isOpenBoundedConvexDomain_centeredCube (0 : SpatialCoordinates d) (hrad n))).1
  have hevents := ae_all_iff.2 fun n : ℕ => hfixed M Rm Sreg It H HI hM
    0 (radius n) (hrad n)
  filter_upwards [hevents] with omega homega
  intro z R hR _ hP
  obtain ⟨n, hn⟩ := exists_nat_gt (R / 2 + dist z 0)
  have hQP : closure (centeredCube z R hR : Set (SpatialCoordinates d)) ⊆
      centeredCube (0 : SpatialCoordinates d) (radius n) (hrad n) := by
    intro x hx
    rw [aux_lem_cutoffs_geom_closure_eq] at hx
    have hx' : dist x z ≤ R / 2 := hx
    change dist x 0 < radius n / 2
    have ht := dist_triangle x z 0
    dsimp [radius]
    linarith
  exact aux_car_variational_cut_hunif_fixed hd M H HI omega z R hR hP
    0 (radius n) (hrad n) (hp n) hQP (homega n) (s ∘ id)



end CutSupply

section HolderPackage
open Metric
open scoped ContDiff Manifold

/-! Copied verbatim (renamed aux_cor_as_resolvent_ -> aux_car_variational_hol_) from
`cor_as_resolvent`'s PROVED `cube_cutoff_holder` cone: uniform-in-`N` sup and 1/4-Hoelder
bounds for the killed resolvents `RN n0 N omega lam f` on the closed cube (equicontinuity). -/

/--
The Laplace-type normalizing integral for the killed resolvent's time kernel:
`∫_{(0,∞)} exp(-λ t) dt = 1/λ` for `λ > 0`. This is the elementary fact behind the
operator bound `‖R^Q_{N,λ}‖_{∞→∞} ≤ λ^{-1}` cited in the proof  ( "the bounds... and the resolvent
identity extend the assertion to all f, λ"). -/
theorem aux_car_variational_hol_integral_exp_Ioi (lam : ℝ) (hlam : 0 < lam) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-lam * t) = 1 / lam := by
  calc
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-lam * t)
        = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(lam * t)) := by
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro t ht
      simp [neg_mul]
    _ = lam⁻¹ • ∫ t in Set.Ioi (lam * (0 : ℝ)), Real.exp (-t) := by
      rw [integral_comp_mul_left_Ioi (fun x => Real.exp (-x)) 0 hlam]
    _ = lam⁻¹ • ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) := by simp
    _ = lam⁻¹ • (1 : ℝ) := by rw [integral_exp_neg_Ioi_zero]
    _ = lam⁻¹ := by simp
    _ = 1 / lam := by rw [one_div]

/--
Abstract pointwise bound on the inner (time) integral shape used to define the cutoff
resolvent kernel `RN`: for any set `S` and any function `g0` bounded in absolute value
by `C ≥ 0`, the `t`-integral of `indicator S (fun s => exp(-λ s) * g0 s)` over `(0,∞)`
is bounded by `C / λ`. Builds on the normalizing integral. -/
theorem aux_car_variational_hol_indicator_exp_bound
    (lam C : ℝ) (hlam : 0 < lam) (hC : 0 ≤ C)
    (S : Set ℝ) (g0 : ℝ → ℝ) (hg0 : ∀ s, |g0 s| ≤ C) :
    |∫ t in Set.Ioi (0 : ℝ), Set.indicator S (fun s => Real.exp (-lam * s) * g0 s) t|
      ≤ C / lam := by
  have h_pointwise : ∀ t, |Set.indicator S (fun s => Real.exp (-lam * s) * g0 s) t| ≤ C * Real.exp (-lam * t) := by
    intro t
    calc
      |Set.indicator S (fun s => Real.exp (-lam * s) * g0 s) t|
          ≤ ‖Set.indicator S (fun s => Real.exp (-lam * s) * g0 s) t‖ := by
        simp [Real.norm_eq_abs]
      _ ≤ ‖(fun s => Real.exp (-lam * s) * g0 s) t‖ := norm_indicator_le_norm_self _ _
      _ = |Real.exp (-lam * t) * g0 t| := by simp [Real.norm_eq_abs]
      _ = |Real.exp (-lam * t)| * |g0 t| := by rw [abs_mul]
      _ = Real.exp (-lam * t) * |g0 t| := by rw [Real.abs_exp (-lam * t)]
      _ ≤ Real.exp (-lam * t) * C := by
        nlinarith [hg0 t, Real.exp_pos (-lam * t)]
      _ = C * Real.exp (-lam * t) := by ring
  have h_int_g : IntegrableOn (fun t => C * Real.exp (-lam * t)) (Set.Ioi (0 : ℝ)) :=
    (exp_neg_integrableOn_Ioi (0 : ℝ) hlam).const_mul C
  have h_int_abs : |∫ t in Set.Ioi (0 : ℝ), Set.indicator S (fun s => Real.exp (-lam * s) * g0 s) t|
      ≤ ∫ t in Set.Ioi (0 : ℝ), |Set.indicator S (fun s => Real.exp (-lam * s) * g0 s) t| :=
    abs_integral_le_integral_abs (μ := Measure.restrict volume (Set.Ioi (0 : ℝ)))
      (f := Set.indicator S (fun s => Real.exp (-lam * s) * g0 s))
  have h_int_bound : ∫ t in Set.Ioi (0 : ℝ), |Set.indicator S (fun s => Real.exp (-lam * s) * g0 s) t|
      ≤ ∫ t in Set.Ioi (0 : ℝ), C * Real.exp (-lam * t) := by
    by_cases h_int_f : IntegrableOn (fun t => |Set.indicator S (fun s => Real.exp (-lam * s) * g0 s) t|)
      (Set.Ioi (0 : ℝ))
    · refine integral_mono (μ := Measure.restrict volume (Set.Ioi (0 : ℝ))) h_int_f h_int_g ?_
      intro t
      simpa [Real.norm_eq_abs] using h_pointwise t
    · rw [integral_undef h_int_f]
      exact setIntegral_nonneg measurableSet_Ioi (fun t ht => by positivity)
  have h_int_Cexp : ∫ t in Set.Ioi (0 : ℝ), C * Real.exp (-lam * t) = C / lam := by
    calc
      ∫ t in Set.Ioi (0 : ℝ), C * Real.exp (-lam * t) = C * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-lam * t) := by
        rw [integral_const_mul]
      _ = C * (1 / lam) := by rw [aux_car_variational_hol_integral_exp_Ioi lam hlam]
      _ = C / lam := by ring
  linarith



theorem aux_car_variational_hol_RN_inner_bound
    {d : ℕ} (Q : Set (SpatialCoordinates d)) (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (path : DiffusionPath d) :
    |∫ t in Set.Ioi (0 : ℝ),
        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q path}
          (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t|
      ≤ ‖f‖ / lam := by
  set S := {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q path}
  set g0 := fun s : ℝ => f (path (Real.toNNReal s))
  have hg0 : ∀ s, |g0 s| ≤ ‖f‖ := by
    intro s
    simpa [Real.norm_eq_abs] using f.norm_coe_le_norm (path (Real.toNNReal s))
  exact aux_car_variational_hol_indicator_exp_bound lam ‖f‖ hlam (norm_nonneg f) S g0 hg0

/--
Integrating the pathwise bound of the pathwise bound over any probability kernel gives the
uniform-in-`N` resolvent bound `|RN n N ω λ f x| ≤ ‖f‖ / λ`. This is exactly the
operator-norm estimate `‖R^Q_{N,λ}‖_{∞→∞} ≤ λ^{-1}` (for `‖f‖ ≤ 1`) that 
cites, together with the resolvent identity, to extend the a.s. convergence from a
countable dense family of `f, λ` to all `f ∈ C(closure Q), λ > 0` on the same event;
it also literally proves the fifth conjunct of `cor_as_resolvent`'s conclusion,
`|Rlim n ω λ f x| ≤ ‖f‖ / λ`, once combined (elsewhere) with the limit `RN → Rlim`. -/
theorem aux_car_variational_hol_RN_bound
    {d : ℕ} (Q : Set (SpatialCoordinates d)) (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (kappa : Measure (DiffusionPath d)) [IsProbabilityMeasure kappa] :
    |∫ path : DiffusionPath d, (∫ t in Set.Ioi (0 : ℝ),
        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q path}
          (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
      ∂kappa|
      ≤ ‖f‖ / lam := by
  have h_ae_bound : ∀ᵐ path ∂kappa, ‖(∫ t in Set.Ioi (0 : ℝ),
      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q path}
        (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)‖ ≤ ‖f‖ / lam := by
    refine Eventually.of_forall fun path => ?_
    simpa [Real.norm_eq_abs] using aux_car_variational_hol_RN_inner_bound Q lam hlam f path
  have h_norm_int : ‖∫ path : DiffusionPath d, (∫ t in Set.Ioi (0 : ℝ),
      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q path}
        (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t) ∂kappa‖
      ≤ (‖f‖ / lam) * kappa.real univ :=
    norm_integral_le_of_norm_le_const h_ae_bound
  simpa [Real.norm_eq_abs, MeasureTheory.probReal_univ, mul_one] using h_norm_int

/-- The unnormalized occupation resolvent on a bounded open set. -/
def aux_car_variational_hol_occupation {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (Q : Set (SpatialCoordinates d)) (lam : ℝ)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d) : ℝ :=
  ∫ p, (∫ t in Set.Ioi (0 : ℝ),
    Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q p}
      (fun s => Real.exp (-lam * s) * f (p (Real.toNNReal s))) t) ∂K x

/-- Fubini for the actual bounded-datum occupation integral. -/
theorem aux_car_variational_hol_occupation_swap {d : ℕ}
    (ν : Measure (DiffusionPath d)) [IsProbabilityMeasure ν]
    (Q : Set (SpatialCoordinates d)) (hQ : IsOpen Q) (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    (∫ p, (∫ t in Set.Ioi (0 : ℝ),
      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q p}
        (fun s => Real.exp (-lam * s) * f (p (Real.toNNReal s))) t) ∂ν) =
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-lam * t) *
      ∫ p in {p : DiffusionPath d | ENNReal.ofReal t < ContinuousPath.exitTime Q p},
        f (p (Real.toNNReal t)) ∂ν := by
  let F : DiffusionPath d × ℝ → ℝ := fun q =>
    Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q q.1}
      (fun s => Real.exp (-lam * s) * f (q.1 (Real.toNNReal s))) q.2
  have heval : Measurable (fun q : DiffusionPath d × ℝ => q.1 (Real.toNNReal q.2)) :=
    ContinuousEval.continuous_eval.measurable.comp
      (measurable_fst.prodMk (measurable_real_toNNReal.comp measurable_snd))
  have hF : Measurable F := by
    change Measurable
      ({q : DiffusionPath d × ℝ | ENNReal.ofReal q.2 < ContinuousPath.exitTime Q q.1}.indicator
        (fun q => Real.exp (-lam * q.2) * f (q.1 (Real.toNNReal q.2))))
    exact ((Real.measurable_exp.comp (measurable_const.mul measurable_snd)).mul
      (f.continuous.measurable.comp heval)).indicator
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd)
        ((ContinuousPath.measurable_exitTime Q hQ).comp measurable_fst))
  have hint : Integrable F (ν.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    have hdom : Integrable (fun q : DiffusionPath d × ℝ =>
        ‖f‖ * Real.exp (-lam * q.2)) (ν.prod (volume.restrict (Set.Ioi (0 : ℝ)))) :=
      Integrable.mul_prod (integrable_const ‖f‖) (exp_neg_integrableOn_Ioi 0 hlam)
    refine hdom.mono' hF.aestronglyMeasurable (Eventually.of_forall fun q => ?_)
    calc ‖F q‖ ≤ ‖Real.exp (-lam * q.2) * f (q.1 (Real.toNNReal q.2))‖ :=
        norm_indicator_le_norm_self _ _
      _ = Real.exp (-lam * q.2) * ‖f (q.1 (Real.toNNReal q.2))‖ := by
        rw [norm_mul, Real.norm_eq_abs, Real.abs_exp]
      _ ≤ Real.exp (-lam * q.2) * ‖f‖ :=
        mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (Real.exp_pos _).le
      _ = ‖f‖ * Real.exp (-lam * q.2) := mul_comm _ _
  have hswap := integral_integral_swap (f := fun p t => F (p, t)) hint
  change (∫ p, ∫ t, F (p,t) ∂(volume.restrict (Set.Ioi (0 : ℝ))) ∂ν) = _
  rw [hswap]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  have hset : MeasurableSet {p : DiffusionPath d |
      ENNReal.ofReal t < ContinuousPath.exitTime Q p} :=
    measurableSet_lt measurable_const (ContinuousPath.measurable_exitTime Q hQ)
  have heq : (fun p => F (p,t)) =
      {p : DiffusionPath d | ENNReal.ofReal t < ContinuousPath.exitTime Q p}.indicator
        (fun p => Real.exp (-lam * t) * f (p (Real.toNNReal t))) := by
    funext p
    rfl
  dsimp only
  rw [heq, integral_indicator hset, integral_const_mul]

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput in
/-- Correct normalization of the Section 9 resolvent for a general bounded datum. -/
theorem aux_car_variational_hol_killed_normalization {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (law : Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ x, Measure.map LifetimePath.ofContinuousPath (K x) = law x)
    (Q : Set (SpatialCoordinates d)) (hQ : IsOpen Q) (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d) :
    killedResolvent law Q lam⁻¹ f x =
      lam * aux_car_variational_hol_occupation K Q lam f x := by
  have : BorelSpace (MarkovProcess.Cemetery (SpatialCoordinates d)) :=
    SubdiffusiveProcess.Model.LifetimeProcess.borelSpace_sum
  have hmass (t : ℝ) : (∫ w in {w : Path d |
      ENNReal.ofReal t < LifetimePath.exitTime Q w}, f (position (Real.toNNReal t) w) ∂law x) =
      ∫ p in {p : DiffusionPath d | ENNReal.ofReal t < ContinuousPath.exitTime Q p},
        f (p (Real.toNNReal t)) ∂K x := by
    have hS : MeasurableSet {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime Q w} :=
      measurableSet_lt measurable_const (LifetimePath.measurable_exitTime Q hQ)
    rw [← hL x, ← integral_indicator hS]
    rw [integral_map LifetimePath.measurable_ofContinuousPath.aemeasurable]
    · rw [← integral_indicator (measurableSet_lt measurable_const
        (ContinuousPath.measurable_exitTime Q hQ))]
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        simp only [Set.indicator, mem_ofPred_eq, LifetimePath.exitTime_ofContinuousPath,
          SubdiffusiveProcess.Model.LifetimeProcess.position_ofContinuousPath]
    · exact ((f.continuous.measurable.comp
        (SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration.position_fixed_measurable (Real.toNNReal t))).indicator hS).aestronglyMeasurable
  unfold aux_car_variational_hol_occupation
  rw [aux_car_variational_hol_occupation_swap (K x) Q hQ lam hlam f]
  unfold killedResolvent
  rw [inv_inv]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only
  rw [hmass t]
  congr 2
  field_simp

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput in
theorem aux_car_variational_hol_weak_ident {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (K : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d))) [IsMarkovKernel K]
    (law : Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ x, Measure.map LifetimePath.ofContinuousPath (K x) = law x)
    (hLD : LocalDiffusion (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) law)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    ∃ u : killedSobolevGraph (centeredCube z r hr),
      ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
          (fun x => aux_car_variational_hol_occupation K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x) ∧
      ∀ w : killedSobolevGraph (centeredCube z r hr),
        sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr) u.val w.val =
          ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            (f x - lam * aux_car_variational_hol_occupation K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x) *
              (w : SobolevData (centeredCube z r hr)).1 x ∂(cutoffSpeedMeasure M H omega N) := by
  obtain ⟨Q, hQdef⟩ : ∃ Q : Set (SpatialCoordinates d),
      Q = (centeredCube z r hr : Set (SpatialCoordinates d)) := ⟨_, rfl⟩
  have hQo : IsOpen Q := hQdef ▸ (centeredCube z r hr).isOpen
  have hQm : MeasurableSet Q := hQo.measurableSet
  have hQb : Bornology.IsBounded Q := hQdef ▸ centeredCube_isBounded z hr
  obtain ⟨S, hSdef⟩ : ∃ S : SpatialCoordinates d → ℝ,
      S = fun x => aux_car_variational_hol_occupation K Q lam f x := ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : SpatialCoordinates d → ℝ, ρ = cutoffSpeedDensity M H omega N :=
    ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : SpatialCoordinates d → ℝ, c = cutoffCoefficient M H omega N :=
    ⟨_, rfl⟩
  have hρc : Continuous ρ := hρdef ▸ aux_torsion_bound_density_continuous M H omega N
  have hρpos : ∀ x, 0 < ρ x := fun x => hρdef ▸ aux_torsion_bound_density_pos M H omega N x
  have hcc : Continuous c := hcdef ▸ _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous M H omega N
  obtain ⟨Cρ, hCρ0, hCρ⟩ := aux_torsion_bound_cube_bound ρ hρc z hr
  obtain ⟨Cc, hCc0, hCc⟩ := aux_torsion_bound_cube_bound c hcc z hr
  rw [← hQdef] at hCρ hCc
  have hρb : ∀ᵐ x ∂volume.restrict Q, |ρ x| ≤ Cρ := by
    filter_upwards [ae_restrict_mem hQm] with x hx using hCρ x hx
  have hcb : ∀ᵐ x ∂volume.restrict Q, |c x| ≤ Cc := by
    filter_upwards [ae_restrict_mem hQm] with x hx using hCc x hx
  -- the weighted measure on the cube is finite and equivalent to Lebesgue
  have hfinW : IsFiniteMeasure ((weightedMeasure ρ).restrict Q) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, weightedMeasure, withDensity_apply _ hQm]
    calc (∫⁻ x in Q, ENNReal.ofReal (ρ x)) ≤ ∫⁻ _x in Q, ENNReal.ofReal Cρ := by
          refine setLIntegral_mono' hQm (fun x hx => ENNReal.ofReal_le_ofReal ?_)
          exact (le_abs_self _).trans (hCρ x hx)
      _ = ENNReal.ofReal Cρ * volume Q := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hQb.measure_lt_top
  have hac : volume.restrict Q ≪ (weightedMeasure ρ).restrict Q := by
    rw [weightedMeasure, restrict_withDensity hQm]
    exact withDensity_absolutelyContinuous'
      (ENNReal.measurable_ofReal.comp hρc.measurable).aemeasurable
      (ae_of_all _ (fun x => by
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hρpos x))
  have hmem1 : MemLp f 2
      ((weightedMeasure ρ).restrict Q) :=
    MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖ (Eventually.of_forall f.norm_coe_le_norm)
  have hsol := hLD.2.2 Q hQo hQb lam⁻¹ (inv_pos.2 hlam) f
    (by rw [← hρdef]; exact hmem1)
  obtain ⟨u0, hu0a, hu0w⟩ := hsol
  rw [← hρdef] at hu0a
  rw [← hρdef, ← hcdef, inv_inv] at hu0w
  -- `u0 = λ S` Lebesgue-a.e. on the cube
  have hu0S : ∀ᵐ x ∂volume.restrict Q, u0.toH1Function.toFun x = lam * S x := by
    filter_upwards [hac.ae_le hu0a] with x hx
    rw [hx, aux_car_variational_hol_killed_normalization K law hL Q hQo lam hlam f x, hSdef]
  -- the killed carrier of `u0`
  subst hQdef
  have hK := _root_.SubdiffusiveProcess.EllipticRegularity.exists_killedSobolevGraph_of_nativeH10 (Ω := centeredCube z r hr) u0
  obtain ⟨U, hUv, hUg⟩ := hK
  refine ⟨lam⁻¹ • U, ?_, ?_⟩
  · have hsm := Lp.coeFn_smul lam⁻¹ (U : SobolevData (centeredCube z r hr)).1
    have hc1 : ((lam⁻¹ • U : killedSobolevGraph (centeredCube z r hr)) :
        SobolevData (centeredCube z r hr)).1 = lam⁻¹ • (U : SobolevData (centeredCube z r hr)).1 :=
      rfl
    rw [hc1]
    filter_upwards [hsm, hUv, hu0S] with x h1 h2 h3
    rw [h1, Pi.smul_apply, smul_eq_mul, h2, h3, hSdef, ← mul_assoc, inv_mul_cancel₀ hlam.ne',
      one_mul]
  · intro w
    have hφ := exists_nativeH10Function_of_killedSobolevGraph w
    obtain ⟨φ, hφv, hφg⟩ := hφ
    have heq := hu0w φ
    -- left side: the coefficient form
    have hL1 : sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
        (lam⁻¹ • U : killedSobolevGraph (centeredCube z r hr)).val w.val =
        lam⁻¹ * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
          U.val w.val := by
      rw [Submodule.coe_smul, map_smul, smul_apply, smul_eq_mul]
    have hgradU : ∀ i : Fin d, MemLp (fun x => u0.toH1Function.grad x i) 2
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      fun i => u0.toH1Function.gradMemL2 i
    have hgradφ : ∀ i : Fin d, MemLp (fun x => φ.toH1Function.grad x i) 2
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      fun i => φ.toH1Function.gradMemL2 i
    have hcm : AEStronglyMeasurable c
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      hcc.aestronglyMeasurable
    have hL2 : sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
        U.val w.val =
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          Homogenization.vecDot (c x • u0.toH1Function.grad x) (φ.toH1Function.grad x) := by
      rw [_root_.SubdiffusiveProcess.EllipticRegularity.sobolevCoefficientForm_eq_sum_integral]
      have hsum : (fun x => Homogenization.vecDot (c x • u0.toH1Function.grad x) (φ.toH1Function.grad x)) =
          fun x => ∑ i : Fin d, c x * (u0.toH1Function.grad x i * φ.toH1Function.grad x i) := by
        funext x
        simp only [Homogenization.vecDot, Pi.smul_apply, smul_eq_mul]
        refine Finset.sum_congr rfl (fun i _ => by ring)
      rw [hsum, integral_finsetSum _ (fun i _ =>
        aux_torsion_bound_int_w_mul _ c _ _ Cc hcm hcb (hgradU i) (hgradφ i))]
      refine Finset.sum_congr rfl (fun i _ => integral_congr_ae ?_)
      filter_upwards [aux_torsion_bound_coef_ae M H omega N z hr, hUg i] with x hx1 hx2
      rw [hx1, hx2, ← hcdef]
      have hw : (w : SobolevData (centeredCube z r hr)).2 i x = φ.toH1Function.grad x i := by
        rw [hφg]
      rw [hw]
    -- right side: the speed-measure pairing
    have hR1 : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        (f x - lam * aux_car_variational_hol_occupation K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x) *
          (w : SobolevData (centeredCube z r hr)).1 x ∂(cutoffSpeedMeasure M H omega N)) =
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          (ρ x * (f x * φ.toH1Function.toFun x) - ρ x * u0.toH1Function.toFun x * φ.toH1Function.toFun x) := by
      rw [aux_torsion_bound_speed_integral M H omega N _ hQm, ← hρdef]
      refine integral_congr_ae ?_
      filter_upwards [hu0S] with x hx
      have hw : (w : SobolevData (centeredCube z r hr)).1 x = φ.toH1Function.toFun x := by
        have := congrFun hφv x
        exact this.symm
      have hS' : (aux_car_variational_hol_occupation K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x) = S x := by rw [hSdef]
      rw [hw, hS', ← hx]
      ring
    have hφL2 : MemLp φ.toH1Function.toFun 2
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      φ.toH1Function.memL2
    have hu0L2 : MemLp u0.toH1Function.toFun 2
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      u0.toH1Function.memL2
    have hρm : AEStronglyMeasurable ρ
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      hρc.aestronglyMeasurable
    have hi1 : Integrable (fun x => ρ x * (f x * φ.toH1Function.toFun x))
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      aux_torsion_bound_int_w_mul _ ρ f _ Cρ hρm hρb
        (MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖
          (Eventually.of_forall f.norm_coe_le_norm)) hφL2
    have hi2 : Integrable (fun x => ρ x * (u0.toH1Function.toFun x * φ.toH1Function.toFun x))
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      aux_torsion_bound_int_w_mul _ ρ _ _ Cρ hρm hρb hu0L2 hφL2
    have hi2' : Integrable (fun x => ρ x * u0.toH1Function.toFun x * φ.toH1Function.toFun x)
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      hi2.congr (ae_of_all _ (fun x => by ring))
    have hRHS := hR1.trans (integral_sub hi1 hi2')
    have hsrc : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ρ x * (lam * f x) * φ.toH1Function.toFun x) =
        lam * ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ρ x * (f x * φ.toH1Function.toFun x) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ (fun x => by ring))
    rw [hsrc] at heq
    have hv : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        Homogenization.vecDot (c x • u0.toH1Function.grad x) (φ.toH1Function.grad x)) =
        lam * ((∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ρ x * (f x * φ.toH1Function.toFun x)) -
          ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ρ x * u0.toH1Function.toFun x * φ.toH1Function.toFun x) := by
      linarith
    exact hL1.trans ((congrArg (fun y => lam⁻¹ * y) (hL2.trans hv)).trans
      ((inv_mul_cancel_left₀ hlam.ne' _).trans hRHS.symm))

theorem aux_car_variational_hol_hcamp_glue {d : ℕ} {W : Set (SpatialCoordinates d)}
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
    exact absurd (le_antisymm this (bot_le)) (ne_of_gt hWpos)
  exact hWeq.closure hf hg

/-- The Euclidean coordinate distance is controlled by `Real.sqrt d` times the ambient
(sup-norm) `dist`. -/
theorem aux_car_variational_hol_hcamp_euclid_le {d : ℕ} (x y : SpatialCoordinates d) :
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
theorem aux_car_variational_hol_hcamp_holder_pt {d : ℕ} (z : SpatialCoordinates d)
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
    have hele := aux_car_variational_hol_hcamp_euclid_le x y
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
theorem aux_car_variational_hol_hcamp_overlap1d {c t r rad : ℝ}
    (hrad : 0 < rad) (hle : rad ≤ r) (ht0 : c - r / 2 < t) (ht1 : t < c + r / 2) :
    rad ≤ min (t + rad) (c + r / 2) - max (t - rad) (c - r / 2) := by
  rcases le_total (t + rad) (c + r / 2) with h1 | h1 <;>
    rcases le_total (t - rad) (c - r / 2) with h2 | h2 <;>
    simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h1, h2] <;>
    linarith

/-- `d`-dimensional density: the (sup-norm) ball of radius `rad ≤ 1` around an interior
point `x'` of the unit-side cube centred at `c` meets that cube in a set whose volume is
at least `2⁻ᵈ` times the volume of the whole ball. -/
theorem aux_car_variational_hol_hcamp_density {d : ℕ} (c x' : SpatialCoordinates d) {rad : ℝ}
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
        have := aux_car_variational_hol_hcamp_overlap1d (c := c i) (t := x' i) (r := 1) (rad := rad)
          hrad hrad1 (hx'i i).1 (hx'i i).2
        linarith)]
    exact aux_car_variational_hol_hcamp_overlap1d (c := c i) (t := x' i) (r := 1) (rad := rad)
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
theorem aux_car_variational_hol_hcamp_variance {d : ℕ} {S : Set (SpatialCoordinates d)}
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
theorem aux_car_variational_hol_hcamp_memLp {d : ℕ} {u : SpatialCoordinates d → ℝ}
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
theorem aux_car_variational_hol_hcamp_osc1 {d : ℕ} {u : SpatialCoordinates d → ℝ} {A alpha : ℝ}
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
  have hstep1 := aux_car_variational_hol_hcamp_variance (S := S) hSfin hIntS hInt2S mB
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
    aux_car_variational_hol_hcamp_density c x' hrad hrad1 hx'
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
theorem aux_car_variational_hol_hcamp_cell {d : ℕ} (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
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
  have hMemLp := aux_car_variational_hol_hcamp_memLp hLIu hLIu2 c 1 one_pos
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
    exact aux_car_variational_hol_hcamp_osc1 hLIu hLIu2 hosc c x hx rad hrad hrad1
  obtain ⟨U, hUcont, hUae, hUholder, hUsemi⟩ := Cp.holder_of_campanato alpha ha0 ha1 c 1 one_pos
    le_rfl uk (A * (2:ℝ) ^ ((d:ℝ)/2)) hAK0 hoscHyp
  exact ⟨U, hUcont, hUae.symm.trans hukAE, hUholder, hUsemi⟩

/-- If `x` lies in an open set `A` and in the closure of `B`, it lies in the closure of
`A ∩ B`. (No delicate boundary/tangency argument needed: `IsOpen.closure_inter` does the
work.) -/
theorem aux_car_variational_hol_hcamp_mem_closure_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} {x : X} (hA : IsOpen A) (hxA : x ∈ A) (hxB : x ∈ closure B) :
    x ∈ closure (A ∩ B) := by
  have hmem : x ∈ closure (B ∩ A) := (hA.closure_inter (s := B)) ⟨hxB, hxA⟩
  rwa [Set.inter_comm] at hmem

/-- Two Campanato representatives on side-`1` cells that both approximate the same `u`
agree pointwise at any point `x` that lies in the (open) first cell and in the closure
of the second. -/
theorem aux_car_variational_hol_hcamp_bridge {d : ℕ} {u : SpatialCoordinates d → ℝ}
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
    aux_car_variational_hol_hcamp_mem_closure_inter (centeredCube k1 1 one_pos).isOpen hx1 hx2
  have h1 : U1 =ᵐ[volume.restrict ((centeredCube k1 1 one_pos : Set (SpatialCoordinates d)) ∩
      (centeredCube k2 1 one_pos : Set (SpatialCoordinates d)))] u :=
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left hU1ae
  have h2 : U2 =ᵐ[volume.restrict ((centeredCube k1 1 one_pos : Set (SpatialCoordinates d)) ∩
      (centeredCube k2 1 one_pos : Set (SpatialCoordinates d)))] u :=
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right hU2ae
  exact aux_car_variational_hol_hcamp_glue hW hU1cont hU2cont (h1.trans h2.symm) hxW

/-- Two points at sup-norm distance `≤ 1` both lie in the closure of the side-`1` cube
centred at their coordinatewise midpoint. -/
theorem aux_car_variational_hol_hcamp_midpoint_mem {d : ℕ} (x y : SpatialCoordinates d)
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
def aux_car_variational_hol_hcamp_idx {d : ℕ} (x : SpatialCoordinates d) : Fin d → ℤ :=
  fun i => round (3 * x i)

/-- The real centre of lattice cell `k`. -/
def aux_car_variational_hol_hcamp_center {d : ℕ} (k : Fin d → ℤ) : SpatialCoordinates d :=
  fun i => ((k i : ℤ) : ℝ) / 3

/-- The "home" cell centre of `x`: rounding each coordinate of `3x` to the nearest
integer and dividing by `3` lands strictly inside the open side-`1` cell centred there
(margin `1/2 - 1/6 = 1/3 > 0`, so no boundary/tie case is an issue, unlike a
spacing-`1/2` grid). -/
def aux_car_variational_hol_hcamp_home {d : ℕ} (x : SpatialCoordinates d) : SpatialCoordinates d :=
  aux_car_variational_hol_hcamp_center (aux_car_variational_hol_hcamp_idx x)

theorem aux_car_variational_hol_hcamp_home_mem {d : ℕ} (x : SpatialCoordinates d) :
    x ∈ (centeredCube (aux_car_variational_hol_hcamp_home x) 1 one_pos :
        Set (SpatialCoordinates d)) := by
  show x ∈ Metric.ball (aux_car_variational_hol_hcamp_home x) (1 / 2)
  rw [Metric.mem_ball, dist_pi_lt_iff (by norm_num : (0:ℝ) < 1 / 2)]
  intro i
  rw [Real.dist_eq]
  have hr := abs_sub_round (3 * x i)
  have heq : x i - aux_car_variational_hol_hcamp_home x i =
      (3 * x i - ((round (3 * x i) : ℤ) : ℝ)) / 3 := by
    unfold aux_car_variational_hol_hcamp_home aux_car_variational_hol_hcamp_center
      aux_car_variational_hol_hcamp_idx
    ring
  rw [heq, abs_div]
  have h3 : |(3:ℝ)| = 3 := by norm_num
  rw [h3]
  linarith

/-- Assembling cellwise-a.e.-equal representatives along `aux_car_variational_hol_hcamp_idx`
gives a globally a.e.-equal function, because the index set `Fin d → ℤ` is countable. -/
theorem aux_car_variational_hol_hcamp_ae_of_cellwise {d : ℕ} {u : SpatialCoordinates d → ℝ}
    {Uf : (Fin d → ℤ) → SpatialCoordinates d → ℝ}
    (hUfae : ∀ k : Fin d → ℤ, Uf k =ᵐ[volume.restrict
        (centeredCube (aux_car_variational_hol_hcamp_center k) 1 one_pos :
          Set (SpatialCoordinates d))] u) :
    (fun x => Uf (aux_car_variational_hol_hcamp_idx x) x) =ᵐ[volume] u := by
  apply ae_iff.mpr
  have hsub : {x | ¬ Uf (aux_car_variational_hol_hcamp_idx x) x = u x} ⊆
      ⋃ k : Fin d → ℤ, {x | aux_car_variational_hol_hcamp_idx x = k} ∩
        {x | ¬ Uf k x = u x} := by
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_inter_iff, mem_ofPred_eq]
    exact ⟨aux_car_variational_hol_hcamp_idx x, rfl, hx⟩
  have hnull : ∀ k : Fin d → ℤ, volume ({x | aux_car_variational_hol_hcamp_idx x = k} ∩
      {x | ¬ Uf k x = u x}) = 0 := by
    intro k
    have hsub2 : {x | aux_car_variational_hol_hcamp_idx x = k} ∩ {x | ¬ Uf k x = u x} ⊆
        (centeredCube (aux_car_variational_hol_hcamp_center k) 1 one_pos :
          Set (SpatialCoordinates d)) ∩ {x | ¬ Uf k x = u x} := by
      rintro x ⟨hx1, hx2⟩
      refine ⟨?_, hx2⟩
      have hhome := aux_car_variational_hol_hcamp_home_mem x
      unfold aux_car_variational_hol_hcamp_home at hhome
      rwa [hx1] at hhome
    have hnull2 : volume ((centeredCube (aux_car_variational_hol_hcamp_center k) 1 one_pos :
        Set (SpatialCoordinates d)) ∩ {x | ¬ Uf k x = u x}) = 0 := by
      have h := ae_iff.mp (hUfae k)
      rwa [Measure.restrict_apply' (centeredCube (aux_car_variational_hol_hcamp_center k) 1
        one_pos).isOpen.measurableSet, Set.inter_comm] at h
    exact measure_mono_null hsub2 hnull2
  exact measure_mono_null hsub (measure_iUnion_null hnull)

/-- Final assembly: Campanato's criterion in the whole-space, plain-function form
consumed by `torsion_bound` (the `aux_car_variational_hol_hcamp` estimate). -/
theorem aux_car_variational_hol_hcamp_final {d : ℕ} (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d) :
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
    fun k => aux_car_variational_hol_hcamp_cell Cp ha0 ha1 hA0 hLIu hLIu2 hosc k
  choose Uf hUfcont hUfae hUfholder hUfsemi using hcell
  set v : SpatialCoordinates d → ℝ :=
    fun x => Uf (aux_car_variational_hol_hcamp_center (aux_car_variational_hol_hcamp_idx x)) x with hvdef
  have hAK0 : (0:ℝ) ≤ A * (2:ℝ) ^ ((d:ℝ)/2) := by positivity
  refine ⟨v, ?_, ?_, ?_⟩
  · exact aux_car_variational_hol_hcamp_ae_of_cellwise
      (u := u) (Uf := fun k => Uf (aux_car_variational_hol_hcamp_center k))
      (fun k => hUfae (aux_car_variational_hol_hcamp_center k))
  · intro x y hxy
    obtain ⟨hxm, hym⟩ := aux_car_variational_hol_hcamp_midpoint_mem x y hxy
    set m : SpatialCoordinates d := fun i => (x i + y i) / 2 with hmdef
    have hvx : v x = Uf m x :=
      aux_car_variational_hol_hcamp_bridge (hUfcont _) (hUfcont m) (hUfae _) (hUfae m)
        (aux_car_variational_hol_hcamp_home_mem x) hxm
    have hvy : v y = Uf m y :=
      aux_car_variational_hol_hcamp_bridge (hUfcont _) (hUfcont m) (hUfae _) (hUfae m)
        (aux_car_variational_hol_hcamp_home_mem y) hym
    have hclos : closure (centeredCube m 1 one_pos : Set (SpatialCoordinates d)) =
        (closedCube m 1 one_pos : Set (SpatialCoordinates d)) := by
      show closure (Metric.ball m (1 / 2)) = Metric.closedBall m (1 / 2)
      exact closure_ball m (by norm_num)
    have hxclosed : x ∈ (closedCube m 1 one_pos : Set (SpatialCoordinates d)) := hclos ▸ hxm
    have hyclosed : y ∈ (closedCube m 1 one_pos : Set (SpatialCoordinates d)) := hclos ▸ hym
    have hCK0 : (0:ℝ) ≤ Cp.C alpha * (A * (2:ℝ) ^ ((d:ℝ)/2)) := by
      have := Cp.C_pos alpha ha0 ha1
      positivity
    have hpt := aux_car_variational_hol_hcamp_holder_pt m one_pos ha0
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
    have hhome := aux_car_variational_hol_hcamp_home_mem x
    set k : SpatialCoordinates d := aux_car_variational_hol_hcamp_home x with hkdef
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
      aux_car_variational_hol_hcamp_mem_closure_inter (centeredCube k 1 one_pos).isOpen hhome hxclB
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
        simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, mem_ofPred_eq]
        rintro ⟨hyW, hyne⟩
        exact hyne (huW y hyW)
      rw [Measure.restrict_apply' hWopen.measurableSet, Set.inter_comm, hz0]
      exact measure_empty
    have hUfzero : Set.EqOn (Uf k) (fun _ => (0:ℝ)) (closure W) :=
      aux_car_variational_hol_hcamp_glue hWopen (hUfcont k) continuous_const hUf0
    exact hUfzero hxW

theorem aux_car_variational_hol_occupation_measurable {d : ℕ}
    (KN : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel KN]
    (Q : Set (SpatialCoordinates d)) (hQ : IsOpen Q) (lam : ℝ)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    Measurable (aux_car_variational_hol_occupation KN Q lam f) := by
  unfold aux_car_variational_hol_occupation

  have hExit : Measurable (ContinuousPath.exitTime Q : DiffusionPath d → ℝ≥0∞) :=
    ContinuousPath.measurable_exitTime Q hQ
  set Sset : Set (DiffusionPath d × ℝ) :=
    {q : DiffusionPath d × ℝ | ENNReal.ofReal q.2 < ContinuousPath.exitTime Q q.1} with hSdef
  set B : DiffusionPath d × ℝ → ℝ :=
    fun q => Real.exp (-lam * q.2) * f (q.1 (Real.toNNReal q.2)) with hBdef
  have hSmeas : MeasurableSet Sset :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd) (hExit.comp measurable_fst)
  have heval : Measurable (fun q : DiffusionPath d × ℝ => q.1 (Real.toNNReal q.2)) :=
    ContinuousEval.continuous_eval.measurable.comp
      (measurable_fst.prodMk (measurable_real_toNNReal.comp measurable_snd))
  have hfeval : Measurable (fun q : DiffusionPath d × ℝ => f (q.1 (Real.toNNReal q.2))) :=
    f.continuous.measurable.comp heval
  have hexp : Measurable (fun q : DiffusionPath d × ℝ => Real.exp (-lam * q.2)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
      measurable_snd
  have hBmeas : Measurable B := hexp.mul hfeval
  have hFmeas : StronglyMeasurable (Sset.indicator B) :=
    hBmeas.stronglyMeasurable.indicator hSmeas
  have hgFmeas : StronglyMeasurable
      (fun path : DiffusionPath d => ∫ t, Sset.indicator B (path, t)
        ∂(volume.restrict (Set.Ioi (0 : ℝ)))) :=
    hFmeas.integral_prod_right'
  have hgeq : (fun path : DiffusionPath d =>
      ∫ t in Set.Ioi (0 : ℝ),
        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q path}
          (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t) =
      (fun path : DiffusionPath d => ∫ t, Sset.indicator B (path, t)
        ∂(volume.restrict (Set.Ioi (0 : ℝ)))) := by
    funext path
    congr 1
  rw [hgeq]
  exact (hgFmeas.integral_kernel (κ := KN)).measurable

theorem aux_car_variational_hol_occupation_bound {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (Q : Set (SpatialCoordinates d)) (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d) :
    |aux_car_variational_hol_occupation K Q lam f x| ≤ ‖f‖ / lam :=
  aux_car_variational_hol_RN_bound Q lam hlam f (K x)

theorem aux_car_variational_hol_occupation_source {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (Q : Set (SpatialCoordinates d)) (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d) :
    |f x - lam * aux_car_variational_hol_occupation K Q lam f x| ≤ 2 * ‖f‖ := by
  have hR := aux_car_variational_hol_occupation_bound K Q lam hlam f x
  have hmul : lam * |aux_car_variational_hol_occupation K Q lam f x| ≤ ‖f‖ := by
    calc lam * |aux_car_variational_hol_occupation K Q lam f x| ≤ lam * (‖f‖ / lam) :=
        mul_le_mul_of_nonneg_left hR hlam.le
      _ = ‖f‖ := mul_div_cancel₀ _ hlam.ne'
  calc |f x - lam * aux_car_variational_hol_occupation K Q lam f x|
      ≤ |f x| + |lam * aux_car_variational_hol_occupation K Q lam f x| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (f x) (0 : ℝ) (lam * aux_car_variational_hol_occupation K Q lam f x)
    _ ≤ ‖f‖ + ‖f‖ := add_le_add (by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x)
      (by simpa only [abs_mul, abs_of_pos hlam] using hmul)
    _ = 2 * ‖f‖ := (two_mul _).symm

theorem aux_car_variational_hol_occupation_zero {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (hstart : ∀ x, ∀ᵐ p ∂K x, p 0 = x)
    (Q : Set (SpatialCoordinates d)) (lam : ℝ)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (x : SpatialCoordinates d) (hx : x ∉ Q) :
    aux_car_variational_hol_occupation K Q lam f x = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [hstart x] with p hp
  have he : ContinuousPath.exitTime Q p = 0 := by
    apply le_antisymm _ (bot_le)
    simpa only [ENNReal.coe_zero] using!
      ContinuousPath.exitTime_le_of_notMem Q p 0 (by rw [hp]; exact hx)
  have hs : {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q p} = ∅ := by
    simp only [he, not_lt_zero, ofPred_false]
  simp only [hs, Set.indicator_empty, integral_zero, Pi.zero_apply]

/-- At one environment, the coercivity, bounded-source regularity, and speed-growth
estimates give a common local Hölder bound for all finite-cutoff occupation resolvents. -/
theorem aux_car_variational_hol_fixed_representatives
    {d : ℕ} (hd : 2 ≤ d) (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (Qtri : Homogenization.TriadicCube d) (hr : 0 < Homogenization.cubeScaleFactor Qtri)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (K : ℕ → Kernel (SpatialCoordinates d) (DiffusionPath d))
    (hK : ∀ N, IsMarkovKernel (K N))
    (law : ℕ → Kernel (SpatialCoordinates d) (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
    (hL : ∀ N x, Measure.map LifetimePath.ofContinuousPath (K N x) = law N x)
    (hLD : ∀ N, SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusion
      (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (law N))
    (Kmu : ℝ) (Region : Set (SpatialCoordinates d))
    (hNeighborhood : ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)),
      Metric.ball x 1 ⊆ Region)
    (hgrowth : ∀ x ∈ Region, ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ N,
      cutoffSpeedMeasure M H omega N (Metric.ball x r) ≤
        ENNReal.ofReal (Kmu * r ^ ((d : ℝ) - epsilon)))
    (K1 Cext K2 : ℝ) (hK1 : 0 ≤ K1) (hCext : 0 ≤ Cext)
    (hcf : ∀ N (v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr)),
      cubeFractionalSqNorm hd (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri)
        hr threeQuarterOrder v.val.1 ≤
        K1 * sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N
          (Homogenization.cubeCenter Qtri) hr) v.val v.val)
    (hext : ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr),
      globalFractionalSqNorm (3 / 4)
        (Set.indicator (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))
          (fun x => v.val.1 x)) ≤
        ENNReal.ofReal (Cext * cubeFractionalSqNorm hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr threeQuarterOrder v.val.1))
    (hDir : ∀ N, aux_limiting_local_energy_DirProp (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr
      (cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr) K2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∃ v : SpatialCoordinates d → ℝ, Continuous v ∧
        aux_car_variational_hol_occupation (K N)
          (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)
          lam f =ᵐ[volume.restrict (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))] v ∧
        (∀ x y, dist x y ≤ 1 → |v x - v y| ≤ C * ‖f‖ * dist x y ^ (1 / 4 : ℝ)) ∧
        ∀ x ∉ (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)), v x = 0 := by
  classical
  let Q := centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr
  let aN := fun N => cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr
  let muN := fun N => cutoffSpeedMeasure M H omega N
  let RN := fun N lam f => aux_car_variational_hol_occupation (K N) Q lam f
  let E := fun N (v w : killedSobolevGraph Q) => sobolevCoefficientForm (aN N) v.val w.val
  have hex : ∀ (N : ℕ) (lam : ℝ) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ),
      ∃ u : killedSobolevGraph Q, 0 < lam →
        ((u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
          RN N lam f) ∧
        ∀ w : killedSobolevGraph Q, E N u w =
          ∫ x in (Q : Set (SpatialCoordinates d)), (f x - lam * RN N lam f x) * w.val.1 x ∂muN N := by
    intro N lam f
    by_cases h : 0 < lam
    · have := hK N
      obtain ⟨u, hu, hw⟩ := aux_car_variational_hol_weak_ident M H omega N (K N)
        (law N) (hL N) (hLD N) (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr lam h f
      exact ⟨u, fun _ => ⟨hu, hw⟩⟩
    · exact ⟨0, fun hp => (h hp).elim⟩
  choose uN huN using hex
  let uN0 := fun N lam f => (Q : Set (SpatialCoordinates d)).indicator (fun x => (uN N lam f).val.1 x)
  have hmeas : ∀ N lam, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      AEMeasurable (RN N lam f) ((muN N).restrict (Q : Set (SpatialCoordinates d))) := by
    intro N lam _ f
    have := hK N
    exact (aux_car_variational_hol_occupation_measurable (K N) Q Q.isOpen lam f).aemeasurable
  have hsource : ∀ N lam, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ᵐ x ∂((muN N).restrict (Q : Set (SpatialCoordinates d))), |f x - lam * RN N lam f x| ≤ 2 * ‖f‖ := by
    intro N lam hlam f
    have := hK N
    exact Eventually.of_forall (aux_car_variational_hol_occupation_source (K N) Q lam hlam f)
  have hcoer := fun N => aux_torsion_bound_hcoer hd (Homogenization.cubeCenter Qtri)
    (Homogenization.cubeScaleFactor Qtri) hr (aN N) K1 Cext hK1 hCext hext (hcf N)
  have hhol := fun N => aux_torsion_bound_hHol (Homogenization.cubeCenter Qtri)
    (Homogenization.cubeScaleFactor Qtri) hr (aN N) K2 (hDir N)
  have hac : ∀ N, (muN N).restrict (Q : Set (SpatialCoordinates d)) ≪ volume := by
    intro N
    exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans
      (withDensity_absolutelyContinuous _ _)
  obtain ⟨A, hA, hosc⟩ := aux_prop_uniform_resolvent_cutoff_oscillation_omega hd epsilon
    hepsilon hepsilon' Qtri hr muN E RN uN uN0 aN (fun _ _ _ => rfl)
    hmeas hsource Kmu (fun _ => K1 * ((Homogenization.cubeScaleFactor Qtri) ^ d + Cext))
    (fun _ => K2 * Real.sqrt (d : ℝ) ^ (1 / 2 : ℝ))
    (by constructor <;> exact ⟨_, by rintro _ ⟨_, rfl⟩; exact le_rfl⟩) Region hNeighborhood
    (fun N lam hlam f => (huN N lam f hlam).2) (fun _ _ _ _ => rfl) hgrowth hcoer hhol hac
  obtain ⟨Cc, hCc, hcamp⟩ := aux_car_variational_hol_hcamp_final Cp (1 / 4) ⟨by norm_num, by norm_num⟩
  refine ⟨Cc * A, mul_nonneg hCc.le hA, ?_⟩
  intro N lam hlam f
  have hbeta : (1 / 4 : ℝ) ≤ 1 / 2 - ((d : ℝ) + 2) * epsilon :=
    (aux_prop_uniform_resolvent_cutoff_oscillation_exponent hd epsilon hepsilon hepsilon').le
  obtain ⟨v, hvc, hvae, hvhol, hv0⟩ := aux_prop_uniform_resolvent_camp_holder
    (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr Cc hcamp
    (1 / 2 - ((d : ℝ) + 2) * epsilon) hbeta (A * ‖f‖)
    (mul_nonneg hA (norm_nonneg f)) (uN N lam f).val.1 (hosc N lam hlam f)
  refine ⟨v, hvc, ?_, ?_, hv0⟩
  · have hrep : (uN N lam f).val.1 =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] v := by
      filter_upwards [ae_restrict_of_ae hvae, ae_restrict_mem Q.isOpen.measurableSet] with x hx hxQ
      change v x = (Q : Set (SpatialCoordinates d)).indicator (fun y => (uN N lam f).val.1 y) x at hx
      rw [Set.indicator_of_mem hxQ] at hx
      exact hx.symm
    exact (huN N lam f hlam).1.symm.trans hrep
  · intro x y hxy
    simpa only [mul_assoc] using hvhol x y hxy

/-- Time-zero attachment from the finite-dimensional distributions. -/
theorem aux_car_variational_hol_start {d : ℕ}
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (ν : Measure (DiffusionPath d)) (x : SpatialCoordinates d)
    (hfdd : ν.map (ContinuousPath.finsetEvaluation (alpha := SpatialCoordinates d)
      ({0} : Finset ℝ≥0)) = P.finiteSetKernel ({0} : Finset ℝ≥0) x) :
    ∀ᵐ p ∂ν, p 0 = x := by
  have heval := map_eval_eq_of_finsetEvaluation P ν x 0 hfdd
  have hev0 : Measurable (fun p : DiffusionPath d => p 0) :=
    (ContinuousPath.continuous_eval (alpha := SpatialCoordinates d) 0).measurable
  rw [ae_iff]
  change ν ((fun p : DiffusionPath d => p 0) ⁻¹' ({x}ᶜ)) = 0
  rw [← Measure.map_apply hev0 (measurableSet_singleton x).compl, heval,
    P.kernel_zero, Kernel.id_apply]
  simp

/-- A local Hölder bound together with the resolvent contraction gives a global bound,
uniform on each positive compact range of the discount parameter. -/
theorem aux_car_variational_hol_compact_range
    {d : ℕ} (Q : Set (SpatialCoordinates d)) (lam0 C : ℝ)
    (hlam0 : 0 < lam0) (hC : 0 ≤ C)
    (R : ℕ → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (habs : ∀ N lam, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ x, |R N lam f x| ≤ ‖f‖ / lam)
    (hlocal : ∀ N lam, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ x ∈ closure Q, ∀ y ∈ closure Q, dist x y ≤ 1 →
        |R N lam f x - R N lam f y| ≤ C * ‖f‖ * dist x y ^ (1 / 4 : ℝ)) :
    ∃ Kom : ℝ, 0 < Kom ∧ ∀ (N : ℕ) (lam : ℝ), lam0 ≤ lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ, ‖f‖ ≤ 1 →
        (∀ x ∈ closure Q, |R N lam f x| ≤ Kom) ∧
        ∀ x ∈ closure Q, ∀ y ∈ closure Q,
          |R N lam f x - R N lam f y| ≤ Kom * dist x y ^ (1 / 4 : ℝ) := by
  let Kom := 1 + C + 2 / lam0
  have hKom : 0 < Kom := by dsimp [Kom]; positivity
  have hCK : C ≤ Kom := by
    have hdiv : 0 ≤ 2 / lam0 := by positivity
    dsimp [Kom]; linarith
  have h2K : 2 / lam0 ≤ Kom := by dsimp [Kom]; linarith
  refine ⟨Kom, hKom, ?_⟩
  intro N lam hlam f hf
  have hlampos := hlam0.trans_le hlam
  have hb : ∀ x, |R N lam f x| ≤ 1 / lam0 := by
    intro x
    exact ((habs N lam hlampos f x).trans
      (div_le_div_of_nonneg_right hf hlampos.le)).trans (one_div_le_one_div_of_le hlam0 hlam)
  refine ⟨fun x _ => (hb x).trans ?_, ?_⟩
  · exact (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) hlam0.le).trans h2K
  · intro x hx y hy
    by_cases hxy : dist x y ≤ 1
    · refine (hlocal N lam hlampos f x hx y hy hxy).trans ?_
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg dist_nonneg _)
      exact (mul_le_of_le_one_right hC hf).trans hCK
    · have hpow : 1 ≤ dist x y ^ (1 / 4 : ℝ) :=
        Real.one_le_rpow (le_of_lt (lt_of_not_ge hxy)) (by norm_num)
      calc
        |R N lam f x - R N lam f y| ≤ |R N lam f x| + |R N lam f y| := by
          simpa only [sub_zero, zero_sub, abs_neg] using
            abs_sub_le (R N lam f x) (0 : ℝ) (R N lam f y)
        _ ≤ 1 / lam0 + 1 / lam0 := add_le_add (hb x) (hb y)
        _ = 2 / lam0 := by ring
        _ ≤ Kom := h2K
        _ ≤ Kom * dist x y ^ (1 / 4 : ℝ) := le_mul_of_one_le_right hKom.le hpow

lemma aux_car_variational_hol_cube_cutoff_holder_p_choice
    {d : ℕ} (hd : 2 ≤ d) :
    (d : ℝ) < ((16 * d * (d + 2) + 1 : ℕ) : ℝ) * (1 / (16 * ((d : ℝ) + 2))) := by
  have hpos : (0 : ℝ) < 16 * ((d : ℝ) + 2) := by positivity
  push_cast
  rw [mul_one_div, lt_div_iff₀ hpos]
  nlinarith

lemma aux_car_variational_hol_cube_cutoff_holder_eps_choice {d : ℕ} (hd : 2 ≤ d) :
    0 < 1 / (16 * ((d : ℝ) + 2)) ∧ 1 / (16 * ((d : ℝ) + 2)) < 1 / (8 * ((d : ℝ) + 2)) := by
  have hd2 : (0 : ℝ) < (d : ℝ) + 2 := by
    have h : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  constructor
  · positivity
  · exact one_div_lt_one_div_of_lt (by positivity) (by nlinarith)

lemma aux_car_variational_hol_cube_cutoff_holder_w_hregion {d : ℕ}
    (Qtri : Homogenization.TriadicCube d) (hr : 0 < Homogenization.cubeScaleFactor Qtri) :
    Bornology.IsBounded (Metric.ball (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri / 2 + 1)) ∧
      (∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))),
        Metric.ball x 1 ⊆ Metric.ball (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri / 2 + 1)) := by
  refine ⟨Metric.isBounded_ball, ?_⟩
  intro x hx y hy
  rw [Metric.mem_ball] at hy ⊢
  have hcube : (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) = Metric.ball (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri / 2) :=
    centeredCube_coe_eq_ball _ _ hr
  rw [hcube] at hx
  have hxc : x ∈ Metric.closedBall (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri / 2) :=
    Metric.closure_ball_subset_closedBall hx
  rw [Metric.mem_closedBall] at hxc
  calc dist y (Homogenization.cubeCenter Qtri) ≤ dist y x + dist x (Homogenization.cubeCenter Qtri) := dist_triangle _ _ _
    _ < 1 + Homogenization.cubeScaleFactor Qtri / 2 := by linarith
    _ = Homogenization.cubeScaleFactor Qtri / 2 + 1 := by ring

/-- Uniform cutoff resolvent bounds on a fixed cube. Coercivity and Dirichlet regularity
come from the original-field suppliers; the weak equation, Campanato estimate, and
continuous-version identification preserve the given occupation resolvent pointwise. -/
theorem aux_car_variational_hol_cube_cutoff_holder
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d) (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Interp : CubeFractionalInterpolationInput d hd)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M) (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M)
        (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg), M.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
      ∀ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)),
        (∀ N, IsMarkovKernel (KN N)) → in_crossing M H PN KN →
        aux_cutoff_lifetime_package_LocalInput M H KN →
      ∀ (Qtri : ℕ → Homogenization.TriadicCube d)
        (hr : ∀ n : ℕ, 0 < Homogenization.cubeScaleFactor (Qtri n))
        (RN : ℕ → ℕ → BilateralField d → ℝ →
            BoundedContinuousFunction (SpatialCoordinates d) ℝ →
            SpatialCoordinates d → ℝ)
        (_hRN_formula : ∀ (n N : ℕ) (omega : BilateralField d) (lam : ℝ)
            (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
            (x : SpatialCoordinates d),
          RN n N omega lam f x =
            ∫ path, (∫ t in Set.Ioi (0 : ℝ),
              Set.indicator
                {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                  (centeredCube (Homogenization.cubeCenter (Qtri n))
                    (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d)) path}
                (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
              ∂(KN N (omega, x)))
        (n0 : ℕ),
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        -- Piggy-backs the `lem_as_coarse` fractional coercivity constant already computed
        -- internally below (`K1`/`hcf`), so `car_variational` gets it for free from this
        -- already-paid-for call instead of re-invoking `lem_as_coarse` at car_variational's
        -- own top level (which is expensive enough there to breach the 200000-heartbeat
        -- ceiling on the whole `car_variational` declaration; see NOTES.md).
        (∃ K1 : ℝ, 0 < K1 ∧ ∀ (N : ℕ) (v : killedSobolevGraph (centeredCube
              (Homogenization.cubeCenter (Qtri n0)) (Homogenization.cubeScaleFactor (Qtri n0))
              (hr n0))),
          cubeFractionalSqNorm hd (Homogenization.cubeCenter (Qtri n0))
              (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0) threeQuarterOrder
              (v : SobolevData (centeredCube (Homogenization.cubeCenter (Qtri n0))
                (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0))).1 ≤
            K1 * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (Homogenization.cubeCenter (Qtri n0)) (hr n0))
              (v : SobolevData (centeredCube (Homogenization.cubeCenter (Qtri n0))
                (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0)))
              (v : SobolevData (centeredCube (Homogenization.cubeCenter (Qtri n0))
                (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0)))) ∧
        ∀ (lam0 lam1 : ℝ), 0 < lam0 → lam0 ≤ lam1 →
          ∃ Kom : ℝ, 0 < Kom ∧ ∀ (N : ℕ) (lam : ℝ), lam0 ≤ lam → lam ≤ lam1 →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ, ‖f‖ ≤ 1 →
              (∀ x ∈ closure (centeredCube (Homogenization.cubeCenter (Qtri n0))
                  (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0) : Set (SpatialCoordinates d)),
                |RN n0 N omega lam f x| ≤ Kom) ∧
              ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter (Qtri n0))
                  (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0) : Set (SpatialCoordinates d)),
              ∀ y ∈ closure (centeredCube (Homogenization.cubeCenter (Qtri n0))
                  (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0) : Set (SpatialCoordinates d)),
                |RN n0 N omega lam f x - RN n0 N omega lam f y| ≤
                  Kom * dist x y ^ (1 / 4 : ℝ)  := by


  classical
  let epsilon : ℝ := 1 / (16 * ((d : ℝ) + 2))
  have heps := aux_car_variational_hol_cube_cutoff_holder_eps_choice hd
  have heps1 : epsilon < 1 := by
    dsimp only [epsilon]
    apply (div_lt_one (by positivity)).2
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨δg, hδg, hgrowth⟩ := prop_chaos_growth hd epsilon ⟨heps.1, heps1⟩
    (16 * d * (d + 2) + 1) (aux_car_variational_hol_cube_cutoff_holder_p_choice hd)
  obtain ⟨δc, hδc, hcoarse⟩ := lem_as_coarse d hd Jc Pc Xc Sf W Cp D aux_lem_band_rcJ_hES Step Dbase Interp 1 (3 / 4)
    ⟨one_pos, le_rfl⟩ ⟨by norm_num, by norm_num⟩
  obtain ⟨δr, hδr, hregular⟩ := lem_as_regularity d hd Jc Pc Xc W D Cp Sf Step Dbase Interp
    (1 / 2) (3 / 4) ((d : ℝ) - 3 / 4) ((d : ℝ) - 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith)
  refine ⟨min δg (min 1 (min δc δr)), lt_min hδg (lt_min one_pos (lt_min hδc hδr)), ?_⟩
  intro M Rm Sreg It hδ H HI PN KN hKN hin hinput Qtri hr RN hRN n0
  have hδg' : M.delta ≤ δg := hδ.trans (min_le_left _ _)
  have hδ1 : M.delta ≤ 1 := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδc' : M.delta ≤ δc := hδ.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδr' : M.delta ≤ δr := hδ.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let Q := centeredCube (Homogenization.cubeCenter (Qtri n0))
    (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0)
  let Region := Metric.ball (Homogenization.cubeCenter (Qtri n0))
    (Homogenization.cubeScaleFactor (Qtri n0) / 2 + 1)
  have hRegion := aux_car_variational_hol_cube_cutoff_holder_w_hregion (Qtri n0) (hr n0)
  obtain ⟨mu, _, _, hg⟩ := hgrowth M H HI hδg'
  obtain ⟨Kmu, _, hKmu⟩ := hg Region hRegion.1
  have eC := hcoarse M Rm Sreg It H HI (le_min hδ1 hδc')
    (Homogenization.cubeCenter (Qtri n0)) (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0)
    ⟨(Qtri n0).scale, rfl⟩
  have eR := hregular M Rm Sreg It H HI (le_min hδ1 hδr')
    (Homogenization.cubeCenter (Qtri n0)) (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0)
  obtain ⟨Cext, hCext, hext, _⟩ := killed_zero_extension_bound hd Sf
    (Homogenization.cubeCenter (Qtri n0)) (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0)
  have hac := car_resolvent_abs_cont hd M H HI PN KN hKN hin hinput
  have hpoint := car_rn_continuous_version hd M H HI PN KN hKN hin hinput hac Qtri hr RN hRN
  filter_upwards [eC, eR, hKmu, hinput.localDiffusion, hpoint, hin.2.2] with omega hC hR hgω hLD hpointω hfdd
  obtain ⟨K1, hK1, hcf⟩ := hC
  obtain ⟨K2, hK2, hDir⟩ := hR
  let K := fun N => (KN N).comap (fun x : SpatialCoordinates d => (omega,x))
    (measurable_const.prodMk measurable_id)
  have hK : ∀ N, IsMarkovKernel (K N) := by
    intro N
    have := hKN N
    dsimp only [K]
    infer_instance
  have hL : ∀ N x, Measure.map LifetimePath.ofContinuousPath (K N x) =
      aux_cutoff_lifetime_package_kernel KN N omega x :=
    fun N x => aux_cutoff_lifetime_package_spec KN N omega x
  have hgr : ∀ x ∈ Region, ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ N,
      cutoffSpeedMeasure M H omega N (Metric.ball x r) ≤
        ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - epsilon)) := by
    intro x hx r hr0 hr1 N
    rw [cutoffSpeedMeasure_eq_weightedChaosCutoff]
    exact hgω.2.1 N x hx r hr0 hr1
  have hD : ∀ N, aux_limiting_local_energy_DirProp (Homogenization.cubeCenter (Qtri n0))
      (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0)
      (cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter (Qtri n0)) (hr n0)) K2 := by
    intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol
    exact ((hDir N).1 F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol).2
  obtain ⟨C, hC0, hrep⟩ := aux_car_variational_hol_fixed_representatives hd Cp epsilon heps.1 heps.2
    (Qtri n0) (hr n0) M H omega K hK (fun N => aux_cutoff_lifetime_package_kernel KN N omega)
    hL hLD (Kmu omega) Region hRegion.2 hgr K1 Cext K2 hK1.le hCext.le
    (fun N v => (hcf true).2.1 N v) hext hD
  have hRN' : ∀ N lam f, RN n0 N omega lam f = aux_car_variational_hol_occupation (K N) Q lam f := by
    intro N lam f
    funext x
    exact hRN n0 N omega lam f x
  have hstart : ∀ N x, ∀ᵐ p ∂K N x, p 0 = x := by
    intro N x
    apply aux_car_variational_hol_start (PN N omega) (K N x) x
    change (KN N (omega,x)).map _ = _
    rw [← Kernel.map_apply (KN N) (ContinuousPath.measurable_finsetEvaluation
      (alpha := SpatialCoordinates d) ({0} : Finset ℝ≥0)) (omega,x)]
    exact hfdd N ({0} : Finset ℝ≥0) x
  have habs : ∀ N lam, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ x, |RN n0 N omega lam f x| ≤ ‖f‖ / lam := by
    intro N lam hlam f x
    have := hK N
    rw [hRN']
    exact aux_car_variational_hol_occupation_bound (K N) Q lam hlam f x
  have hlocal : ∀ N lam, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ y ∈ closure (Q : Set (SpatialCoordinates d)),
        dist x y ≤ 1 → |RN n0 N omega lam f x - RN n0 N omega lam f y| ≤
          C * ‖f‖ * dist x y ^ (1 / 4 : ℝ) := by
    intro N lam hlam f
    obtain ⟨v, hvc, hvae, hvhol, hv0⟩ := hrep N lam hlam f
    have hRv : RN n0 N omega lam f = v := by
      funext x
      by_cases hx : x ∈ (Q : Set (SpatialCoordinates d))
      · apply hpointω n0 N lam hlam f v hvc.continuousOn
        · rw [hRN']; exact hvae
        · exact hx
      · rw [hRN', aux_car_variational_hol_occupation_zero (K N) (hstart N) Q lam f x hx, hv0 x hx]
    intro x _ y _ hxy
    rw [hRv]
    exact hvhol x y hxy
  refine ⟨⟨K1, hK1, fun N v => (hcf true).2.1 N v⟩, ?_⟩
  intro lam0 lam1 hlam0 _
  obtain ⟨Kom, hKom, hKomall⟩ := aux_car_variational_hol_compact_range (Q : Set (SpatialCoordinates d))
    lam0 C hlam0 hC0 (fun N lam f => RN n0 N omega lam f) habs hlocal
  exact ⟨Kom, hKom, fun N lam hlow _ f hf => hKomall N lam hlow f hf⟩



end HolderPackage



theorem aux_car_variational_mosco
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube z r hr),
      ‖(v : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) v‖)
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hG : ∀ f : DomainL2 (centeredCube z r hr),
      Tendsto
        (fun N : ℕ =>
          (responseSolution (killedResponseSpace (Ω := centeredCube z r hr) hP)
              (a N) ((sobolevVolumeLoad f).comp
                (killedResponseSpace (Ω := centeredCube z r hr) hP).space.subtypeL)).val.1)
        atTop (𝓝 (G f))) :
    (∀ x y : DomainL2 (centeredCube z r hr), inner ℝ (G x) y = inner ℝ x (G y)) ∧
      (∀ x : DomainL2 (centeredCube z r hr), 0 ≤ inner ℝ x (G x)) ∧
      (∀ (uN : ℕ → (killedResponseSpace (Ω := centeredCube z r hr) hP).space)
          (u : DomainL2 (centeredCube z r hr)),
        (∀ f : DomainL2 (centeredCube z r hr),
          Tendsto (fun n => inner ℝ f (uN n).val.1) atTop
            (𝓝 (inner ℝ f u))) →
        limitFormEnergy G u ≤
          liminf (fun n =>
            ((responseForm (killedResponseSpace (Ω := centeredCube z r hr) hP)
              (a n) (uN n) (uN n) : ℝ) : EReal)) atTop) ∧
      (∀ u : DomainL2 (centeredCube z r hr),
        u ∈ limitFormDomain G →
        ∃ w : ℕ → (killedResponseSpace (Ω := centeredCube z r hr) hP).space,
          Tendsto (fun n => ((w n).val.1,
            ((responseForm (killedResponseSpace (Ω := centeredCube z r hr) hP)
              (a n) (w n) (w n) : ℝ) : EReal))) atTop
            (𝓝 (u, limitFormEnergy G u))) := by
  let S : ResponseSpace (centeredCube z r hr) := killedResponseSpace hP
  have hstrong : ∀ f : DomainL2 (centeredCube z r hr),
      Tendsto (fun n => (responseSolution S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1) atTop (𝓝 (G f)) := by
    intro f
    exact hG f
  have hsym : ∀ x y : DomainL2 (centeredCube z r hr),
      inner ℝ (G x) y = inner ℝ x (G y) := by
    intro x y
    have hxy : Tendsto
        (fun n => inner ℝ
          (responseSolution S (a n)
            ((sobolevVolumeLoad x).comp S.space.subtypeL)).val.1 y)
        atTop (𝓝 (inner ℝ (G x) y)) :=
      (hstrong x).inner tendsto_const_nhds
    have hyx : Tendsto
        (fun n => inner ℝ x
          (responseSolution S (a n)
            ((sobolevVolumeLoad y).comp S.space.subtypeL)).val.1)
        atTop (𝓝 (inner ℝ x (G y))) :=
      tendsto_const_nhds.inner (hstrong y)
    apply tendsto_nhds_unique (hxy.congr' (Filter.Eventually.of_forall fun n => by
      rw [real_inner_comm]
      exact volumeResponse_pairing_symm S (a n) y x)) hyx
  have hpos : ∀ x : DomainL2 (centeredCube z r hr),
      0 ≤ inner ℝ x (G x) := by
    intro x
    have hx : Tendsto
        (fun n => inner ℝ x
          (responseSolution S (a n)
            ((sobolevVolumeLoad x).comp S.space.subtypeL)).val.1)
        atTop (𝓝 (inner ℝ x (G x))) :=
      tendsto_const_nhds.inner (hstrong x)
    exact ge_of_tendsto hx (Filter.Eventually.of_forall fun n =>
      volumeResponse_pairing_nonneg S (a n) x)
  have hweakresponse : ∀ f : DomainL2 (centeredCube z r hr),
      Tendsto (fun n => inverseResponse S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop
        (𝓝 (inner ℝ f (G f))) := by
    intro f
    refine (tendsto_const_nhds.inner (hstrong f)).congr' ?_
    filter_upwards [] with n
    rw [inverseResponse_eq_load]
    rfl
  obtain ⟨hlow, hrec⟩ := killedInverse_mosco S a G hsym hpos hstrong hweakresponse
  exact ⟨hsym, hpos, hlow, hrec⟩

theorem aux_car_variational_limit_coercive
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (_HI : InfraredCharacterization M H)
    (omega : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube z r hr),
      ‖(v : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) v‖)
    (K : ℝ) (hK : 0 < K)
    (hc : ∀ (N : ℕ) (v : killedSobolevGraph (centeredCube z r hr)),
      cubeFractionalSqNorm hd z r hr threeQuarterOrder
          (v : SobolevData (centeredCube z r hr)).1 ≤
        K * sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
          (v : SobolevData (centeredCube z r hr))
          (v : SobolevData (centeredCube z r hr)))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (ha : ∀ N, a N = _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
    (hsym : ∀ x y : DomainL2 (centeredCube z r hr),
      inner ℝ (G x) y = inner ℝ x (G y))
    (hpos : ∀ x : DomainL2 (centeredCube z r hr), 0 ≤ inner ℝ x (G x))
    (hstrong : ∀ f : DomainL2 (centeredCube z r hr),
      Tendsto
        (fun N : ℕ =>
          (responseSolution (killedResponseSpace (Ω := centeredCube z r hr) hP)
            (a N) ((sobolevVolumeLoad f).comp
              (killedResponseSpace (Ω := centeredCube z r hr) hP).space.subtypeL)).val.1)
        atTop (𝓝 (G f))) :
    ∃ Ccoer : ℝ, 0 < Ccoer ∧
      ∀ u : DomainL2 (centeredCube z r hr),
        (limitFormEnergy G u).toENNReal ≠ ⊤ →
        ENNReal.ofReal (‖u‖ ^ 2) ≤ ENNReal.ofReal Ccoer *
          (limitFormEnergy G u).toENNReal := by
  obtain ⟨Cbase, hKC, hlimC⟩ := aux_limiting_local_energy_coercive_limit hd z r hr K hK
    (limitFormEnergy G) (limitFormEnergy_nonneg G)
    (fun u hu' => by
      obtain ⟨wseq, hwseq⟩ := exists_responseForm_recoverySequence
        (killedResponseSpace (Ω := centeredCube z r hr) hP) a G hsym hpos hstrong u hu'
      refine ⟨fun n => (wseq n).val.1,
        fun n => responseForm (killedResponseSpace (Ω := centeredCube z r hr) hP)
          (a n) (wseq n) (wseq n), hwseq.fst_nhds, hwseq.snd_nhds, ?_, ?_⟩
      · intro n
        exact Sf.h1_fractional_finite z r hr
          ⟨(wseq n).val, killedSobolevGraph_le_weakSobolevGraph (wseq n).property⟩
      · intro n
        simpa [ha n, responseForm_apply, sobolevCoefficientForm_apply] using
          hc n ⟨(wseq n).val, (wseq n).property⟩)
    (fun w v hw => aux_limiting_local_energy_seminorm_le_liminf hd z r hr
      threeQuarterOrder w v hw)
  have hvol : 0 < volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    SubdiffusiveProcess.centeredCube_volume_pos z hr
  have hcoefpos : 0 < r ^ (-(threeQuarterOrder : ℝ)) /
        Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    exact div_pos (Real.rpow_pos_of_pos hr _) (Real.sqrt_pos.mpr hvol)
  have hinvpos : 0 < (r ^ (-(threeQuarterOrder : ℝ)) /
        Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))⁻¹ ^ 2 := by
    positivity
  refine ⟨(r ^ (-(threeQuarterOrder : ℝ)) /
      Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))⁻¹ ^ 2 * Cbase, ?_, ?_⟩
  · exact mul_pos hinvpos (lt_of_lt_of_le hK hKC)
  · intro u hu
    have hfinite : limitFormEnergy G u < (⊤ : EReal) :=
      lt_top_iff_ne_top.mpr (EReal.toENNReal_ne_top_iff.mp hu)
    obtain ⟨v, hv, hvb⟩ := hlimC u hfinite.ne
    have hnorm : ‖u‖ ≤
        cubeFractionalL2Norm hd z r hr threeQuarterOrder v /
          (r ^ (-(threeQuarterOrder : ℝ)) /
            Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) := by
      have hnon : 0 ≤ (cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
          v.val).toReal := ENNReal.toReal_nonneg
      have hterm : r ^ (-(threeQuarterOrder : ℝ)) *
          (‖u‖ / Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) ≤
        cubeFractionalL2Norm hd z r hr threeQuarterOrder v := by
        unfold cubeFractionalL2Norm
        rw [Fin.sum_univ_one, hv, Real.sqrt_sq (norm_nonneg u)]
        exact le_add_of_nonneg_left hnon
      have hrpow : 0 < r ^ (-(threeQuarterOrder : ℝ)) := Real.rpow_pos_of_pos hr _
      have hsqrt : 0 < Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) :=
        Real.sqrt_pos.mpr hvol
      have hcoef : 0 < r ^ (-(threeQuarterOrder : ℝ)) /
          Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) :=
        div_pos hrpow hsqrt
      have hterm' : (r ^ (-(threeQuarterOrder : ℝ)) /
          Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) * ‖u‖ ≤
          cubeFractionalL2Norm hd z r hr threeQuarterOrder v := by
        simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hterm
      apply (le_div_iff₀ hcoef).2
      change ‖u‖ * (r ^ (-(threeQuarterOrder : ℝ)) /
        Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) ≤ _
      simpa [mul_comm] using hterm'
    have hnormsq : ‖u‖ ^ 2 ≤
        (r ^ (-(threeQuarterOrder : ℝ)) /
          Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))⁻¹ ^ 2 *
          (cubeFractionalL2Norm hd z r hr threeQuarterOrder v) ^ 2 := by
      have hnormv : 0 ≤ cubeFractionalL2Norm hd z r hr threeQuarterOrder v := by
        unfold cubeFractionalL2Norm
        positivity
      have hB : 0 ≤ (r ^ (-(threeQuarterOrder : ℝ)) /
          Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))⁻¹ *
          cubeFractionalL2Norm hd z r hr threeQuarterOrder v := by positivity
      have hsqB : ((r ^ (-(threeQuarterOrder : ℝ)) /
          Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))⁻¹ *
          cubeFractionalL2Norm hd z r hr threeQuarterOrder v) ^ 2 =
          (r ^ (-(threeQuarterOrder : ℝ)) /
          Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))⁻¹ ^ 2 *
          (cubeFractionalL2Norm hd z r hr threeQuarterOrder v) ^ 2 := by ring
      have hnorm' : ‖u‖ ≤
          (r ^ (-(threeQuarterOrder : ℝ)) /
            Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))⁻¹ *
            cubeFractionalL2Norm hd z r hr threeQuarterOrder v := by
        simpa [div_eq_mul_inv, mul_comm] using hnorm
      simpa [mul_pow] using (sq_le_sq₀ (norm_nonneg u) hB).2 hnorm'
    have hreal : 0 ≤ (limitFormEnergy G u).toReal :=
        EReal.toReal_nonneg (limitFormEnergy_nonneg G u)
    have hvb' :
        (r ^ (-(threeQuarterOrder : ℝ)) /
          Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))⁻¹ ^ 2 *
            cubeFractionalL2Norm hd z r hr threeQuarterOrder v ^ 2 ≤
          (r ^ (-(threeQuarterOrder : ℝ)) /
            Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))⁻¹ ^ 2 *
            (Cbase * (limitFormEnergy G u).toReal) :=
      mul_le_mul_of_nonneg_left hvb (sq_nonneg _)
    have hsq : ‖u‖ ^ 2 ≤
        ((r ^ (-(threeQuarterOrder : ℝ)) /
          Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))⁻¹ ^ 2 * Cbase) *
          (limitFormEnergy G u).toReal :=
      hnormsq.trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using hvb')
    have hconst : 0 ≤ (r ^ (-(threeQuarterOrder : ℝ)) /
        Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))))⁻¹ ^ 2 * Cbase :=
      mul_nonneg (sq_nonneg _) (le_of_lt (lt_of_lt_of_le hK hKC))
    rw [EReal.toENNReal_of_ne_top hfinite.ne]
    rw [← ENNReal.ofReal_mul hconst]
    exact ENNReal.ofReal_le_ofReal hsq

/-- Same hypotheses as `aux_car_variational_limit_coercive`; exposes the intermediate
three-quarter-order fractional representative and its norm bound directly (needed to build the
half-order trace bound `Ktr`, since `interpolation_half` compares a half-order representative to a
three-quarter-order one with the same restriction). -/
theorem aux_car_variational_frac_bound
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube z r hr),
      ‖(v : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) v‖)
    (K : ℝ) (hK : 0 < K)
    (hc : ∀ (N : ℕ) (v : killedSobolevGraph (centeredCube z r hr)),
      cubeFractionalSqNorm hd z r hr threeQuarterOrder
          (v : SobolevData (centeredCube z r hr)).1 ≤
        K * sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
          (v : SobolevData (centeredCube z r hr))
          (v : SobolevData (centeredCube z r hr)))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (ha : ∀ N, a N = _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
    (hsym : ∀ x y : DomainL2 (centeredCube z r hr),
      inner ℝ (G x) y = inner ℝ x (G y))
    (hpos : ∀ x : DomainL2 (centeredCube z r hr), 0 ≤ inner ℝ x (G x))
    (hstrong : ∀ f : DomainL2 (centeredCube z r hr),
      Tendsto
        (fun N : ℕ =>
          (responseSolution (killedResponseSpace (Ω := centeredCube z r hr) hP)
            (a N) ((sobolevVolumeLoad f).comp
              (killedResponseSpace (Ω := centeredCube z r hr) hP).space.subtypeL)).val.1)
        atTop (𝓝 (G f))) :
    ∃ Cbase : ℝ, 0 < Cbase ∧
      ∀ u : DomainL2 (centeredCube z r hr),
        (limitFormEnergy G u).toENNReal ≠ ⊤ →
        ∃ v : CubeFractionalL2 (k := 1) hd z r hr threeQuarterOrder,
          v.val 0 = u ∧
          (cubeFractionalL2Norm hd z r hr threeQuarterOrder v) ^ 2 ≤
            Cbase * (limitFormEnergy G u).toReal := by
  obtain ⟨Cbase, hKC, hlimC⟩ := aux_limiting_local_energy_coercive_limit hd z r hr K hK
    (limitFormEnergy G) (limitFormEnergy_nonneg G)
    (fun u hu' => by
      obtain ⟨wseq, hwseq⟩ := exists_responseForm_recoverySequence
        (killedResponseSpace (Ω := centeredCube z r hr) hP) a G hsym hpos hstrong u hu'
      refine ⟨fun n => (wseq n).val.1,
        fun n => responseForm (killedResponseSpace (Ω := centeredCube z r hr) hP)
          (a n) (wseq n) (wseq n), hwseq.fst_nhds, hwseq.snd_nhds, ?_, ?_⟩
      · intro n
        exact Sf.h1_fractional_finite z r hr
          ⟨(wseq n).val, killedSobolevGraph_le_weakSobolevGraph (wseq n).property⟩
      · intro n
        simpa [ha n, responseForm_apply, sobolevCoefficientForm_apply] using
          hc n ⟨(wseq n).val, (wseq n).property⟩)
    (fun w v hw => aux_limiting_local_energy_seminorm_le_liminf hd z r hr
      threeQuarterOrder w v hw)
  refine ⟨Cbase, lt_of_lt_of_le hK hKC, ?_⟩
  intro u hu
  have hfinite : limitFormEnergy G u < (⊤ : EReal) :=
    lt_top_iff_ne_top.mpr (EReal.toENNReal_ne_top_iff.mp hu)
  exact hlimC u hfinite.ne

theorem aux_car_variational_energy_algebra
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (G : DomainL2 (centeredCube z r hr) →L[ℝ]
      DomainL2 (centeredCube z r hr))
    (_hsym : ∀ x y, inner ℝ (G x) y = inner ℝ x (G y))
    (hpos : ∀ x, 0 ≤ inner ℝ x (G x)) :
    (limitFormEnergy G 0).toENNReal = 0 ∧
    (∀ c u, (limitFormEnergy G u).toENNReal ≠ ⊤ →
      (limitFormEnergy G (c • u)).toENNReal = ENNReal.ofReal (c ^ 2) *
        (limitFormEnergy G u).toENNReal) := by
  constructor
  · have hzero : limitFormEnergy G 0 = 0 := by
      unfold limitFormEnergy
      apply le_antisymm
      · refine iSup_le fun f => ?_
        rw [← EReal.coe_zero, EReal.coe_le_coe_iff]
        simp only [inner_zero_right]
        linarith [hpos f]
      · exact le_iSup_of_le (0 : DomainL2 (centeredCube z r hr)) (by simp)
    rw [hzero]
    exact EReal.toENNReal_zero
  · intro c u hu
    have hq := quadraticDual_smul G hpos c u
    unfold limitFormEnergy at hq ⊢
    rw [hq, EReal.toENNReal_mul (by positivity)]
    rfl

theorem aux_car_variational_energy_properties
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (G : DomainL2 (centeredCube z r hr) →L[ℝ]
      DomainL2 (centeredCube z r hr))
    (hsym : ∀ x y, inner ℝ (G x) y = inner ℝ x (G y))
    (hpos : ∀ x, 0 ≤ inner ℝ x (G x)) :
    (∀ (c : ℝ) (w1 w2 : DomainL2 (centeredCube z r hr)),
      (limitFormEnergy G w1).toENNReal ≠ ⊤ →
      (limitFormEnergy G w2).toENNReal ≠ ⊤ →
      (limitFormEnergy G (c • w1 + w2)).toENNReal ≠ ⊤) ∧
    (∀ w1 w2 : DomainL2 (centeredCube z r hr),
      (limitFormEnergy G w1).toENNReal ≠ ⊤ →
      (limitFormEnergy G w2).toENNReal ≠ ⊤ →
      (limitFormEnergy G (w1 + w2)).toReal +
          (limitFormEnergy G (w1 - w2)).toReal =
        2 * (limitFormEnergy G w1).toReal +
          2 * (limitFormEnergy G w2).toReal) ∧
    (∀ (c : ℝ) (u : DomainL2 (centeredCube z r hr)),
      (limitFormEnergy G u).toENNReal ≠ ⊤ →
      (limitFormEnergy G (c • u)).toENNReal =
        ENNReal.ofReal (c ^ 2) * (limitFormEnergy G u).toENNReal) := by
  obtain ⟨hE0, hscale⟩ := aux_car_variational_energy_algebra z r hr G hsym hpos
  have htop : ∀ u : DomainL2 (centeredCube z r hr),
      (limitFormEnergy G u).toENNReal ≠ ⊤ → limitFormEnergy G u ≠ (⊤ : EReal) := by
    intro u hu
    exact EReal.toENNReal_ne_top_iff.mp hu
  have hbot : ∀ u : DomainL2 (centeredCube z r hr),
      limitFormEnergy G u ≠ (⊥ : EReal) := by
    intro u hu
    have hnon := limitFormEnergy_nonneg G u
    rw [hu] at hnon
    simp at hnon
  have hscaleE : ∀ (c : ℝ) (u : DomainL2 (centeredCube z r hr)),
      (limitFormEnergy G u).toENNReal ≠ ⊤ →
      limitFormEnergy G (c • u) ≠ (⊤ : EReal) := by
    intro c u hu
    have h := hscale c u hu
    have h' : (limitFormEnergy G (c • u)).toENNReal ≠ ⊤ := by
      rw [h]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hu
    exact htop _ h'
  have hclosed : ∀ (c : ℝ) (w1 w2 : DomainL2 (centeredCube z r hr)),
      (limitFormEnergy G w1).toENNReal ≠ ⊤ →
      (limitFormEnergy G w2).toENNReal ≠ ⊤ →
      (limitFormEnergy G (c • w1 + w2)).toENNReal ≠ ⊤ := by
    intro c w1 w2 hw1 hw2
    have hp := aux_prop_locality_energy_parallelogram d (centeredCube z r hr) G
      (c • w1) w2 hsym hpos
    have hcw1 := hscaleE c w1 hw1
    have hsum : limitFormEnergy G (c • w1) + limitFormEnergy G w2 ≠ (⊤ : EReal) :=
      aux_prop_locality_add_ne_top hcw1 (htop _ hw2)
    have hright : (limitFormEnergy G (c • w1) + limitFormEnergy G w2) +
        (limitFormEnergy G (c • w1) + limitFormEnergy G w2) ≠ (⊤ : EReal) :=
      aux_prop_locality_add_ne_top hsum hsum
    have hresult : limitFormEnergy G (c • w1 + w2) ≠ (⊤ : EReal) := by
      intro hbad
      apply hright
      rw [← hp, hbad]
      exact EReal.top_add_of_ne_bot (hbot (c • w1 - w2))
    exact EReal.toENNReal_ne_top_iff.mpr hresult
  have hpara : ∀ (w1 w2 : DomainL2 (centeredCube z r hr)),
      (limitFormEnergy G w1).toENNReal ≠ ⊤ →
      (limitFormEnergy G w2).toENNReal ≠ ⊤ →
      (limitFormEnergy G (w1 + w2)).toReal +
          (limitFormEnergy G (w1 - w2)).toReal =
        2 * (limitFormEnergy G w1).toReal +
          2 * (limitFormEnergy G w2).toReal := by
    intro w1 w2 hw1 hw2
    have hp := aux_prop_locality_energy_parallelogram d (centeredCube z r hr) G
      w1 w2 hsym hpos
    have hplus : (limitFormEnergy G (w1 + w2)).toENNReal ≠ ⊤ := by
      simpa using hclosed 1 w1 w2 hw1 hw2
    have hminus : (limitFormEnergy G (w1 - w2)).toENNReal ≠ ⊤ := by
      simpa [neg_one_smul, neg_add_eq_sub] using hclosed (-1) w2 w1 hw2 hw1
    have hplus' := htop _ hplus
    have hminus' := htop _ hminus
    have hw1' := htop _ hw1
    have hw2' := htop _ hw2
    have hbplus := hbot (w1 + w2)
    have hbminus := hbot (w1 - w2)
    have hb1 := hbot w1
    have hb2 := hbot w2
    rw [← EReal.coe_toReal hplus' hbplus,
      ← EReal.coe_toReal hminus' hbminus,
      ← EReal.coe_toReal hw1' hb1,
      ← EReal.coe_toReal hw2' hb2] at hp
    calc
      _ = (limitFormEnergy G w1).toReal + (limitFormEnergy G w2).toReal +
          ((limitFormEnergy G w1).toReal + (limitFormEnergy G w2).toReal) := by
        exact_mod_cast hp
      _ = _ := by ring
  exact ⟨hclosed, hpara, hscale⟩

theorem aux_car_variational_occupation_measurable
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (N : ℕ) (hKN : IsMarkovKernel (KN N)) (Q : Opens (SpatialCoordinates d))
    (lam : ℝ) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    Measurable (fun p : BilateralField d × SpatialCoordinates d =>
      ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Set.indicator
          {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
            (Q : Set (SpatialCoordinates d)) path}
          (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
        ∂(KN N p)) := by
  let g : DiffusionPath d → ℝ := fun path =>
        ∫ t in Set.Ioi (0 : ℝ),
          Set.indicator
            {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
              (Q : Set (SpatialCoordinates d)) path}
            (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t
  have hG : Measurable g := by
    dsimp [g]
    exact aux_prop_uniform_resolvent_point_G_measurable
      (Q : Set (SpatialCoordinates d)) Q.isOpen lam (fun x => f x)
      f.continuous.measurable
  let : IsMarkovKernel (KN N) := hKN
  change Measurable (fun p : BilateralField d × SpatialCoordinates d =>
      ∫ path, g path ∂(KN N p))
  exact (StronglyMeasurable.integral_kernel_prod_right' (κ := KN N)
    (f := fun z : (BilateralField d × SpatialCoordinates d) × DiffusionPath d => g z.2)
    (hG.comp measurable_snd).stronglyMeasurable).measurable

theorem aux_car_variational_path_start
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hcross : in_crossing M H PN KN) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ, ∀ x : SpatialCoordinates d,
      ∀ᵐ path ∂(KN N (omega, x)), path (0 : ℝ≥0) = x := by
  filter_upwards [hcross.2.2] with omega hfd
  intro N x
  have hfdd0 : (KN N (omega, x)).map
        (ContinuousPath.finsetEvaluation (alpha := SpatialCoordinates d) ({0} : Finset ℝ≥0)) =
      SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) ({0} : Finset ℝ≥0) x := by
    rw [← Kernel.map_apply (KN N)
      (ContinuousPath.measurable_finsetEvaluation (alpha := SpatialCoordinates d)
        ({0} : Finset ℝ≥0)) (omega, x)]
    exact hfd N ({0} : Finset ℝ≥0) x
  have heval := map_eval_eq_of_finsetEvaluation (PN N omega) (KN N (omega, x)) x 0 hfdd0
  have hev0 : Measurable (fun path : DiffusionPath d => path 0) :=
    (ContinuousPath.continuous_eval (alpha := SpatialCoordinates d) 0).measurable
  rw [ae_iff]
  have hset : {z : DiffusionPath d | ¬ z 0 = x} =
      (fun path : DiffusionPath d => path 0) ⁻¹' ({x}ᶜ) := rfl
  rw [hset, ← Measure.map_apply hev0 (measurableSet_singleton x).compl, heval,
    (PN N omega).kernel_zero, Kernel.id_apply]
  simp

theorem aux_car_variational_RN_zero_outside
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Qtri : ℕ → Homogenization.TriadicCube d)
    (hr : ∀ n : ℕ, 0 < Homogenization.cubeScaleFactor (Qtri n))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hstart : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ, ∀ x : SpatialCoordinates d,
      ∀ᵐ path ∂(KN N (omega, x)), path (0 : ℝ≥0) = x)
    (RN : ℕ → ℕ → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRN : ∀ (n N : ℕ) (omega : BilateralField d) (lam : ℝ)
        (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
        (x : SpatialCoordinates d),
      RN n N omega lam f x =
        ∫ path, (∫ t in Set.Ioi (0 : ℝ),
          Set.indicator
            {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
              (centeredCube (Homogenization.cubeCenter (Qtri n))
                (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d)) path}
            (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
          ∂(KN N (omega, x))) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (n N : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∀ x ∉ (centeredCube (Homogenization.cubeCenter (Qtri n))
              (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d)),
            RN n N omega lam f x = 0 := by
  filter_upwards [hstart] with omega hω
  intro n N lam hlam f x hx
  rw [hRN n N omega lam f x]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hω N x] with path hpath
  have hExit : ContinuousPath.exitTime
      (centeredCube (Homogenization.cubeCenter (Qtri n))
        (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d)) path = 0 := by
    apply le_antisymm _ (bot_le)
    have hle := ContinuousPath.exitTime_le_of_notMem
      (centeredCube (Homogenization.cubeCenter (Qtri n))
        (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d))
      path 0 (by rw [hpath]; exact hx)
    simpa using hle
  have hempty : {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
      (centeredCube (Homogenization.cubeCenter (Qtri n))
        (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d)) path} = ∅ := by
    ext s
    simp [hExit]
  simp [hempty]

theorem aux_car_variational_RN_bound
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (_M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Qtri : ℕ → Homogenization.TriadicCube d)
    (hr : ∀ n : ℕ, 0 < Homogenization.cubeScaleFactor (Qtri n))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (RN : ℕ → ℕ → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRN : ∀ (n N : ℕ) (omega : BilateralField d) (lam : ℝ)
        (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
        (x : SpatialCoordinates d),
      RN n N omega lam f x =
        ∫ path, (∫ t in Set.Ioi (0 : ℝ),
          Set.indicator
            {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
              (centeredCube (Homogenization.cubeCenter (Qtri n))
                (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d)) path}
            (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
          ∂(KN N (omega, x))) :
    ∀ (n N : ℕ) (omega : BilateralField d) (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ x ∈ (centeredCube (Homogenization.cubeCenter (Qtri n))
            (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d)),
          |RN n N omega lam f x| ≤ ‖f‖ / lam := by
  intro n N omega lam hlam f x hx
  rw [hRN n N omega lam f x]
  let : IsMarkovKernel (KN N) := hKN N
  let : IsProbabilityMeasure (KN N (omega, x)) :=
    IsMarkovKernel.isProbabilityMeasure (omega, x)
  have hpath : ∀ path : DiffusionPath d,
      |∫ t in Set.Ioi (0 : ℝ),
        Set.indicator
          {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
            (centeredCube (Homogenization.cubeCenter (Qtri n))
              (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d)) path}
          (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t| ≤ ‖f‖ / lam := by
    intro path
    simpa [Real.norm_eq_abs, aux_prop_uniform_resolvent_point_G,
      aux_prop_uniform_resolvent_point_F] using
      (aux_prop_uniform_resolvent_point_G_abs_le
        (centeredCube (Homogenization.cubeCenter (Qtri n))
          (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d))
        lam hlam (fun y => f y) ‖f‖
        (fun y => by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm y) path)
  have h_ae_bound : ∀ᵐ path ∂(KN N (omega, x)),
      ‖(∫ t in Set.Ioi (0 : ℝ),
        Set.indicator
          {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
            (centeredCube (Homogenization.cubeCenter (Qtri n))
              (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d)) path}
          (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)‖ ≤ ‖f‖ / lam := by
    filter_upwards [] with path
    simpa [Real.norm_eq_abs] using hpath path
  have hnorm := norm_integral_le_of_norm_le_const h_ae_bound
  simpa [Real.norm_eq_abs, MeasureTheory.probReal_univ, mul_one] using hnorm

theorem aux_car_variational_RN_smul
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Qtri : ℕ → Homogenization.TriadicCube d)
    (hr : ∀ n : ℕ, 0 < Homogenization.cubeScaleFactor (Qtri n))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (RN : ℕ → ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRN_formula : ∀ (n N : ℕ) (omega : BilateralField d) (lam : ℝ)
        (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d),
      RN n N omega lam f x =
        ∫ path, (∫ t in Set.Ioi (0 : ℝ),
          Set.indicator
            {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
              (centeredCube (Homogenization.cubeCenter (Qtri n))
                (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d)) path}
            (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
          ∂(KN N (omega, x))) :
    ∀ (n N : ℕ) (omega : BilateralField d) (c lam : ℝ)
      (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d),
      RN n N omega lam (c • f) x = c * RN n N omega lam f x := by
  intro n N omega c lam f x
  rw [hRN_formula, hRN_formula]
  set μ : Measure (DiffusionPath d) := KN N (omega, x)
  have hinner : ∀ path : DiffusionPath d,
      (∫ t in Set.Ioi (0 : ℝ), Set.indicator
          {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
            (centeredCube (Homogenization.cubeCenter (Qtri n))
              (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d)) path}
          (fun s : ℝ => Real.exp (-lam * s) * (c • f) (path (Real.toNNReal s))) t)
        = c * (∫ t in Set.Ioi (0 : ℝ), Set.indicator
          {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
            (centeredCube (Homogenization.cubeCenter (Qtri n))
              (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d)) path}
          (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t) := by
    intro path
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    by_cases ht : t ∈ {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
        (centeredCube (Homogenization.cubeCenter (Qtri n))
          (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d)) path}
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht,
        BoundedContinuousFunction.smul_apply, smul_eq_mul]
      ring
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
      ring
  calc
    ∫ path, (∫ t in Set.Ioi (0 : ℝ), Set.indicator
        {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
          (centeredCube (Homogenization.cubeCenter (Qtri n))
            (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d)) path}
        (fun s : ℝ => Real.exp (-lam * s) * (c • f) (path (Real.toNNReal s))) t) ∂μ
        = ∫ path, c * (∫ t in Set.Ioi (0 : ℝ), Set.indicator
            {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
              (centeredCube (Homogenization.cubeCenter (Qtri n))
                (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d)) path}
            (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t) ∂μ := by
      apply integral_congr_ae
      filter_upwards with path
      exact hinner path
    _ = c * ∫ path, (∫ t in Set.Ioi (0 : ℝ), Set.indicator
            {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
              (centeredCube (Homogenization.cubeCenter (Qtri n))
                (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d)) path}
            (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t) ∂μ := by
      rw [integral_const_mul]

theorem aux_car_variational_cutoff_elliptic
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ lamC LamC : ℝ, 0 < lamC ∧
      Homogenization.IsEllipticFieldOn lamC LamC
        (centeredCube z r hr : Set (SpatialCoordinates d))
        (SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField
          (cutoffCoefficient M H omega N)) := by
  let c : SpatialCoordinates d → ℝ := cutoffCoefficient M H omega N
  have hc : Continuous c := cutoffCoefficient_continuous M H omega N
  have hcp : ∀ x, 0 < c x := cutoffCoefficient_pos M H omega N
  have hK : IsCompact (closure (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    (centeredCube_isBounded z hr).isCompact_closure
  have hKn : (closure (centeredCube z r hr : Set (SpatialCoordinates d))).Nonempty :=
    ⟨z, subset_closure (by exact Metric.mem_ball_self (half_pos hr))⟩
  obtain ⟨xmin, hxmin, hmin⟩ := hK.exists_isMinOn hKn hc.continuousOn
  obtain ⟨xmax, hxmax, hmax⟩ := hK.exists_isMaxOn hKn hc.continuousOn
  refine ⟨c xmin, c xmax, hcp xmin, ?_⟩
  refine SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.isEllipticFieldOn_scalarCoeffField_of_continuousOn
    (centeredCube z r hr).isOpen.measurableSet (hc.continuousOn.mono subset_closure)
    (hcp xmin) ?_
  intro x hx
  exact ⟨by simpa [c] using hmin (subset_closure hx),
    by simpa [c] using hmax (subset_closure hx)⟩

theorem aux_car_variational_local_form
    {d : ℕ} {U : Opens (SpatialCoordinates d)}
    {c rho : SpatialCoordinates d → ℝ}
    {law : Kernel (SpatialCoordinates d)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d)}
    (hD : SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusion c rho law)
    (hUb : Bornology.IsBounded (U : Set (SpatialCoordinates d)))
    {lamC LamC : ℝ}
    (hEll : Homogenization.IsEllipticFieldOn lamC LamC (U : Set (SpatialCoordinates d))
      (SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField c))
    {lam : ℝ} (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (hf : MemLp (fun x : SpatialCoordinates d => f x) 2
      ((SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.weightedMeasure rho).restrict U)) :
    ∃ u : Homogenization.H10Function (U : Set (SpatialCoordinates d)),
      (∀ᵐ x ∂(SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.weightedMeasure rho).restrict U,
        u.toH1Function.toFun x =
          SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.killedResolvent law
            (U : Set (SpatialCoordinates d)) lam⁻¹ (fun y => f y) x) ∧
      ∀ v : Homogenization.H10Function (U : Set (SpatialCoordinates d)),
      (∫ x in (U : Set (SpatialCoordinates d)),
          rho x * u.toH1Function.toFun x * v.toFun x) +
            lam⁻¹ *
              (SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.Packet455.dirichletBilin hEll
                u.toH1Function v.toH1Function) =
          ∫ x in (U : Set (SpatialCoordinates d)),
            rho x * f x * v.toFun x := by
  simpa only [inv_inv] using
      (SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.Packet455.exists_killedResolvent_form_identity
        hD U.isOpen hUb hEll (s := lam⁻¹) (by positivity) (fun y => f y) hf)

theorem aux_car_variational_operator_eq
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q)
    (G₁ G₂ : DomainL2 Q →L[ℝ] DomainL2 Q)
    (h₁ : ∀ f : DomainL2 Q,
      Tendsto
        (fun N : ℕ =>
          (responseSolution S (a N)
            ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
        atTop (𝓝 (G₁ f)))
    (h₂ : ∀ f : DomainL2 Q,
      Tendsto
        (fun N : ℕ =>
          (responseSolution S (a N)
            ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
        atTop (𝓝 (G₂ f))) :
    G₁ = G₂ := by
  apply ContinuousLinearMap.ext
  intro f
  exact tendsto_nhds_unique (h₁ f) (h₂ f)



/-- The unnormalized occupation resolvent on a bounded open set. -/
def aux_car_variational_occupation {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (Q : Set (SpatialCoordinates d)) (lam : ℝ)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d) : ℝ :=
  ∫ p, (∫ t in Set.Ioi (0 : ℝ),
    Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q p}
      (fun s => Real.exp (-lam * s) * f (p (Real.toNNReal s))) t) ∂K x

/-- Fubini for the actual bounded-datum occupation integral. -/
theorem aux_car_variational_occupation_swap {d : ℕ}
    (ν : Measure (DiffusionPath d)) [IsProbabilityMeasure ν]
    (Q : Set (SpatialCoordinates d)) (hQ : IsOpen Q) (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    (∫ p, (∫ t in Set.Ioi (0 : ℝ),
      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q p}
        (fun s => Real.exp (-lam * s) * f (p (Real.toNNReal s))) t) ∂ν) =
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-lam * t) *
      ∫ p in {p : DiffusionPath d | ENNReal.ofReal t < ContinuousPath.exitTime Q p},
        f (p (Real.toNNReal t)) ∂ν := by
  let F : DiffusionPath d × ℝ → ℝ := fun q =>
    Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime Q q.1}
      (fun s => Real.exp (-lam * s) * f (q.1 (Real.toNNReal s))) q.2
  have heval : Measurable (fun q : DiffusionPath d × ℝ => q.1 (Real.toNNReal q.2)) :=
    ContinuousEval.continuous_eval.measurable.comp
      (measurable_fst.prodMk (measurable_real_toNNReal.comp measurable_snd))
  have hF : Measurable F := by
    change Measurable
      ({q : DiffusionPath d × ℝ | ENNReal.ofReal q.2 < ContinuousPath.exitTime Q q.1}.indicator
        (fun q => Real.exp (-lam * q.2) * f (q.1 (Real.toNNReal q.2))))
    exact ((Real.measurable_exp.comp (measurable_const.mul measurable_snd)).mul
      (f.continuous.measurable.comp heval)).indicator
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd)
        ((ContinuousPath.measurable_exitTime Q hQ).comp measurable_fst))
  have hint : Integrable F (ν.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    have hdom : Integrable (fun q : DiffusionPath d × ℝ =>
        ‖f‖ * Real.exp (-lam * q.2)) (ν.prod (volume.restrict (Set.Ioi (0 : ℝ)))) :=
      Integrable.mul_prod (integrable_const ‖f‖) (exp_neg_integrableOn_Ioi 0 hlam)
    refine hdom.mono' hF.aestronglyMeasurable (Eventually.of_forall fun q => ?_)
    calc ‖F q‖ ≤ ‖Real.exp (-lam * q.2) * f (q.1 (Real.toNNReal q.2))‖ :=
        norm_indicator_le_norm_self _ _
      _ = Real.exp (-lam * q.2) * ‖f (q.1 (Real.toNNReal q.2))‖ := by
        rw [norm_mul, Real.norm_eq_abs, Real.abs_exp]
      _ ≤ Real.exp (-lam * q.2) * ‖f‖ :=
        mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (Real.exp_pos _).le
      _ = ‖f‖ * Real.exp (-lam * q.2) := mul_comm _ _
  have hswap := integral_integral_swap (f := fun p t => F (p, t)) hint
  change (∫ p, ∫ t, F (p,t) ∂(volume.restrict (Set.Ioi (0 : ℝ))) ∂ν) = _
  rw [hswap]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  have hset : MeasurableSet {p : DiffusionPath d |
      ENNReal.ofReal t < ContinuousPath.exitTime Q p} :=
    measurableSet_lt measurable_const (ContinuousPath.measurable_exitTime Q hQ)
  have heq : (fun p => F (p,t)) =
      {p : DiffusionPath d | ENNReal.ofReal t < ContinuousPath.exitTime Q p}.indicator
        (fun p => Real.exp (-lam * t) * f (p (Real.toNNReal t))) := by
    funext p
    rfl
  dsimp only
  rw [heq, integral_indicator hset, integral_const_mul]

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput in
/-- Correct normalization of the Section 9 resolvent for a general bounded datum. -/
theorem aux_car_variational_killed_normalization {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (law : Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ x, Measure.map LifetimePath.ofContinuousPath (K x) = law x)
    (Q : Set (SpatialCoordinates d)) (hQ : IsOpen Q) (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d) :
    killedResolvent law Q lam⁻¹ f x =
      lam * aux_car_variational_occupation K Q lam f x := by
  have : BorelSpace (MarkovProcess.Cemetery (SpatialCoordinates d)) :=
    SubdiffusiveProcess.Model.LifetimeProcess.borelSpace_sum
  have hmass (t : ℝ) : (∫ w in {w : Path d |
      ENNReal.ofReal t < LifetimePath.exitTime Q w}, f (position (Real.toNNReal t) w) ∂law x) =
      ∫ p in {p : DiffusionPath d | ENNReal.ofReal t < ContinuousPath.exitTime Q p},
        f (p (Real.toNNReal t)) ∂K x := by
    have hS : MeasurableSet {w : Path d | ENNReal.ofReal t < LifetimePath.exitTime Q w} :=
      measurableSet_lt measurable_const (LifetimePath.measurable_exitTime Q hQ)
    rw [← hL x, ← integral_indicator hS]
    rw [integral_map LifetimePath.measurable_ofContinuousPath.aemeasurable]
    · rw [← integral_indicator (measurableSet_lt measurable_const
        (ContinuousPath.measurable_exitTime Q hQ))]
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        simp only [Set.indicator, mem_ofPred_eq, LifetimePath.exitTime_ofContinuousPath,
          SubdiffusiveProcess.Model.LifetimeProcess.position_ofContinuousPath]
    · exact ((f.continuous.measurable.comp
        (SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration.position_fixed_measurable (Real.toNNReal t))).indicator hS).aestronglyMeasurable
  unfold aux_car_variational_occupation
  rw [aux_car_variational_occupation_swap (K x) Q hQ lam hlam f]
  unfold killedResolvent
  rw [inv_inv]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only
  rw [hmass t]
  congr 2
  field_simp


open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput in
theorem aux_car_variational_weak_ident {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (K : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d))) [IsMarkovKernel K]
    (law : Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ x, Measure.map LifetimePath.ofContinuousPath (K x) = law x)
    (hLD : LocalDiffusion (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) law)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    ∃ u : killedSobolevGraph (centeredCube z r hr),
      ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
          (fun x => aux_car_variational_occupation K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x) ∧
      ∀ w : killedSobolevGraph (centeredCube z r hr),
        sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr) u.val w.val =
          ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            (f x - lam * aux_car_variational_occupation K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x) *
              (w : SobolevData (centeredCube z r hr)).1 x ∂(cutoffSpeedMeasure M H omega N) := by
  obtain ⟨Q, hQdef⟩ : ∃ Q : Set (SpatialCoordinates d),
      Q = (centeredCube z r hr : Set (SpatialCoordinates d)) := ⟨_, rfl⟩
  have hQo : IsOpen Q := hQdef ▸ (centeredCube z r hr).isOpen
  have hQm : MeasurableSet Q := hQo.measurableSet
  have hQb : Bornology.IsBounded Q := hQdef ▸ centeredCube_isBounded z hr
  obtain ⟨S, hSdef⟩ : ∃ S : SpatialCoordinates d → ℝ,
      S = fun x => aux_car_variational_occupation K Q lam f x := ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : SpatialCoordinates d → ℝ, ρ = cutoffSpeedDensity M H omega N :=
    ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : SpatialCoordinates d → ℝ, c = cutoffCoefficient M H omega N :=
    ⟨_, rfl⟩
  have hρc : Continuous ρ := hρdef ▸ aux_torsion_bound_density_continuous M H omega N
  have hρpos : ∀ x, 0 < ρ x := fun x => hρdef ▸ aux_torsion_bound_density_pos M H omega N x
  have hcc : Continuous c := hcdef ▸ _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous M H omega N
  obtain ⟨Cρ, hCρ0, hCρ⟩ := aux_torsion_bound_cube_bound ρ hρc z hr
  obtain ⟨Cc, hCc0, hCc⟩ := aux_torsion_bound_cube_bound c hcc z hr
  rw [← hQdef] at hCρ hCc
  have hρb : ∀ᵐ x ∂volume.restrict Q, |ρ x| ≤ Cρ := by
    filter_upwards [ae_restrict_mem hQm] with x hx using hCρ x hx
  have hcb : ∀ᵐ x ∂volume.restrict Q, |c x| ≤ Cc := by
    filter_upwards [ae_restrict_mem hQm] with x hx using hCc x hx
  -- the weighted measure on the cube is finite and equivalent to Lebesgue
  have hfinW : IsFiniteMeasure ((weightedMeasure ρ).restrict Q) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, weightedMeasure, withDensity_apply _ hQm]
    calc (∫⁻ x in Q, ENNReal.ofReal (ρ x)) ≤ ∫⁻ _x in Q, ENNReal.ofReal Cρ := by
          refine setLIntegral_mono' hQm (fun x hx => ENNReal.ofReal_le_ofReal ?_)
          exact (le_abs_self _).trans (hCρ x hx)
      _ = ENNReal.ofReal Cρ * volume Q := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hQb.measure_lt_top
  have hac : volume.restrict Q ≪ (weightedMeasure ρ).restrict Q := by
    rw [weightedMeasure, restrict_withDensity hQm]
    exact withDensity_absolutelyContinuous'
      (ENNReal.measurable_ofReal.comp hρc.measurable).aemeasurable
      (ae_of_all _ (fun x => by
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hρpos x))
  have hmem1 : MemLp f 2
      ((weightedMeasure ρ).restrict Q) :=
    MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖ (Eventually.of_forall f.norm_coe_le_norm)
  have hsol := hLD.2.2 Q hQo hQb lam⁻¹ (inv_pos.2 hlam) f
    (by rw [← hρdef]; exact hmem1)
  obtain ⟨u0, hu0a, hu0w⟩ := hsol
  rw [← hρdef] at hu0a
  rw [← hρdef, ← hcdef, inv_inv] at hu0w
  -- `u0 = λ S` Lebesgue-a.e. on the cube
  have hu0S : ∀ᵐ x ∂volume.restrict Q, u0.toH1Function.toFun x = lam * S x := by
    filter_upwards [hac.ae_le hu0a] with x hx
    rw [hx, aux_car_variational_killed_normalization K law hL Q hQo lam hlam f x, hSdef]
  -- the killed carrier of `u0`
  subst hQdef
  have hK := _root_.SubdiffusiveProcess.EllipticRegularity.exists_killedSobolevGraph_of_nativeH10 (Ω := centeredCube z r hr) u0
  obtain ⟨U, hUv, hUg⟩ := hK
  refine ⟨lam⁻¹ • U, ?_, ?_⟩
  · have hsm := Lp.coeFn_smul lam⁻¹ (U : SobolevData (centeredCube z r hr)).1
    have hc1 : ((lam⁻¹ • U : killedSobolevGraph (centeredCube z r hr)) :
        SobolevData (centeredCube z r hr)).1 = lam⁻¹ • (U : SobolevData (centeredCube z r hr)).1 :=
      rfl
    rw [hc1]
    filter_upwards [hsm, hUv, hu0S] with x h1 h2 h3
    rw [h1, Pi.smul_apply, smul_eq_mul, h2, h3, hSdef, ← mul_assoc, inv_mul_cancel₀ hlam.ne',
      one_mul]
  · intro w
    have hφ := exists_nativeH10Function_of_killedSobolevGraph w
    obtain ⟨φ, hφv, hφg⟩ := hφ
    have heq := hu0w φ
    -- left side: the coefficient form
    have hL1 : sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
        (lam⁻¹ • U : killedSobolevGraph (centeredCube z r hr)).val w.val =
        lam⁻¹ * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
          U.val w.val := by
      rw [Submodule.coe_smul, map_smul, smul_apply, smul_eq_mul]
    have hgradU : ∀ i : Fin d, MemLp (fun x => u0.toH1Function.grad x i) 2
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      fun i => u0.toH1Function.gradMemL2 i
    have hgradφ : ∀ i : Fin d, MemLp (fun x => φ.toH1Function.grad x i) 2
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      fun i => φ.toH1Function.gradMemL2 i
    have hcm : AEStronglyMeasurable c
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      hcc.aestronglyMeasurable
    have hL2 : sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
        U.val w.val =
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          Homogenization.vecDot (c x • u0.toH1Function.grad x) (φ.toH1Function.grad x) := by
      rw [_root_.SubdiffusiveProcess.EllipticRegularity.sobolevCoefficientForm_eq_sum_integral]
      have hsum : (fun x => Homogenization.vecDot (c x • u0.toH1Function.grad x) (φ.toH1Function.grad x)) =
          fun x => ∑ i : Fin d, c x * (u0.toH1Function.grad x i * φ.toH1Function.grad x i) := by
        funext x
        simp only [Homogenization.vecDot, Pi.smul_apply, smul_eq_mul]
        refine Finset.sum_congr rfl (fun i _ => by ring)
      rw [hsum, integral_finsetSum _ (fun i _ =>
        aux_torsion_bound_int_w_mul _ c _ _ Cc hcm hcb (hgradU i) (hgradφ i))]
      refine Finset.sum_congr rfl (fun i _ => integral_congr_ae ?_)
      filter_upwards [aux_torsion_bound_coef_ae M H omega N z hr, hUg i] with x hx1 hx2
      rw [hx1, hx2, ← hcdef]
      have hw : (w : SobolevData (centeredCube z r hr)).2 i x = φ.toH1Function.grad x i := by
        rw [hφg]
      rw [hw]
    -- right side: the speed-measure pairing
    have hR1 : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        (f x - lam * aux_car_variational_occupation K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x) *
          (w : SobolevData (centeredCube z r hr)).1 x ∂(cutoffSpeedMeasure M H omega N)) =
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          (ρ x * (f x * φ.toH1Function.toFun x) - ρ x * u0.toH1Function.toFun x * φ.toH1Function.toFun x) := by
      rw [aux_torsion_bound_speed_integral M H omega N _ hQm, ← hρdef]
      refine integral_congr_ae ?_
      filter_upwards [hu0S] with x hx
      have hw : (w : SobolevData (centeredCube z r hr)).1 x = φ.toH1Function.toFun x := by
        have := congrFun hφv x
        exact this.symm
      have hS' : (aux_car_variational_occupation K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x) = S x := by rw [hSdef]
      rw [hw, hS', ← hx]
      ring
    have hφL2 : MemLp φ.toH1Function.toFun 2
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      φ.toH1Function.memL2
    have hu0L2 : MemLp u0.toH1Function.toFun 2
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      u0.toH1Function.memL2
    have hρm : AEStronglyMeasurable ρ
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      hρc.aestronglyMeasurable
    have hi1 : Integrable (fun x => ρ x * (f x * φ.toH1Function.toFun x))
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      aux_torsion_bound_int_w_mul _ ρ f _ Cρ hρm hρb
        (MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖
          (Eventually.of_forall f.norm_coe_le_norm)) hφL2
    have hi2 : Integrable (fun x => ρ x * (u0.toH1Function.toFun x * φ.toH1Function.toFun x))
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      aux_torsion_bound_int_w_mul _ ρ _ _ Cρ hρm hρb hu0L2 hφL2
    have hi2' : Integrable (fun x => ρ x * u0.toH1Function.toFun x * φ.toH1Function.toFun x)
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      hi2.congr (ae_of_all _ (fun x => by ring))
    have hRHS := hR1.trans (integral_sub hi1 hi2')
    have hsrc : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ρ x * (lam * f x) * φ.toH1Function.toFun x) =
        lam * ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ρ x * (f x * φ.toH1Function.toFun x) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ (fun x => by ring))
    rw [hsrc] at heq
    have hv : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        Homogenization.vecDot (c x • u0.toH1Function.grad x) (φ.toH1Function.grad x)) =
        lam * ((∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ρ x * (f x * φ.toH1Function.toFun x)) -
          ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ρ x * u0.toH1Function.toFun x * φ.toH1Function.toFun x) := by
      linarith
    exact hL1.trans ((congrArg (fun y => lam⁻¹ * y) (hL2.trans hv)).trans
      ((inv_mul_cancel_left₀ hlam.ne' _).trans hRHS.symm))



theorem aux_car_variational_muFull_compact_bound
    {d : ℕ} (cutoffSeq : ℕ → Measure (SpatialCoordinates d))
    (mu muFull : Measure (SpatialCoordinates d))
    [IsLocallyFiniteMeasure mu] [mu.IsOpenPosMeasure]
    (hmuconv : MeasuresConvergeLocally cutoffSeq mu)
    (hmuFullconv : MeasuresConvergeLocally cutoffSeq muFull)
    (x : SpatialCoordinates d) (r : ℝ) (K : Set (SpatialCoordinates d))
    (hK : IsCompact K) (hKint : (interior K).Nonempty) (hKr : K ⊆ Metric.ball x r)
    (B : ℝ≥0∞) (hBfin : B ≠ ⊤) (hB : mu (Metric.ball x r) ≤ B) :
    muFull K ≤ B := by
  obtain ⟨f, hf0, hfsupp, hflow, hfup⟩ :=
    _root_.SubdiffusiveProcess.Paper.aux_lim_transition_domination_bump_sandwich K (Metric.ball x r) hK
      Metric.isOpen_ball hKr
  have hVmeas : MeasurableSet (Metric.ball x r : Set (SpatialCoordinates d)) :=
    Metric.isOpen_ball.measurableSet
  have hKmeas : MeasurableSet K := hK.measurableSet
  -- `mu`'s side: the lintegral of the bump against `mu` is finite and positive.
  have hmuUpper : (∫⁻ y, ENNReal.ofReal (f y) ∂mu) ≤ mu (Metric.ball x r) :=
    (lintegral_mono hfup).trans_eq (lintegral_indicator_one hVmeas)
  have hmuLower : mu K ≤ ∫⁻ y, ENNReal.ofReal (f y) ∂mu :=
    (lintegral_indicator_one hKmeas).symm.trans_le (lintegral_mono hflow)
  have hmuFinite : (∫⁻ y, ENNReal.ofReal (f y) ∂mu) < ⊤ :=
    lt_of_le_of_lt (hmuUpper.trans hB) (lt_top_iff_ne_top.mpr hBfin)
  have hmuPos : 0 < ∫⁻ y, ENNReal.ofReal (f y) ∂mu :=
    lt_of_lt_of_le (Measure.measure_pos_of_nonempty_interior mu hKint) hmuLower
  -- Bochner values against `mu` and `muFull` agree (same limit of the same sequence).
  have hBochnerEq : (∫ y, f y ∂mu) = ∫ y, f y ∂muFull :=
    tendsto_nhds_unique (hmuconv f) (hmuFullconv f)
  have hfnonneg : 0 ≤ᵐ[mu] (f : SpatialCoordinates d → ℝ) := Eventually.of_forall hf0
  have hfnonneg' : 0 ≤ᵐ[muFull] (f : SpatialCoordinates d → ℝ) := Eventually.of_forall hf0
  have hmuBochner : (∫ y, f y ∂mu) = (∫⁻ y, ENNReal.ofReal (f y) ∂mu).toReal :=
    integral_eq_lintegral_of_nonneg_ae hfnonneg f.continuous.aestronglyMeasurable
  have hmuFullBochner : (∫ y, f y ∂muFull) =
      (∫⁻ y, ENNReal.ofReal (f y) ∂muFull).toReal :=
    integral_eq_lintegral_of_nonneg_ae hfnonneg' f.continuous.aestronglyMeasurable
  have hLpos : 0 < (∫⁻ y, ENNReal.ofReal (f y) ∂mu).toReal :=
    ENNReal.toReal_pos hmuPos.ne' hmuFinite.ne
  have htoRealEq : (∫⁻ y, ENNReal.ofReal (f y) ∂muFull).toReal =
      (∫⁻ y, ENNReal.ofReal (f y) ∂mu).toReal := by
    rw [← hmuFullBochner, ← hBochnerEq, hmuBochner]
  have hmuFullNeTop : (∫⁻ y, ENNReal.ofReal (f y) ∂muFull) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at htoRealEq
    exact hLpos.ne' htoRealEq.symm
  have hmuFullEq : (∫⁻ y, ENNReal.ofReal (f y) ∂muFull) =
      (∫⁻ y, ENNReal.ofReal (f y) ∂mu) := by
    have hround := ENNReal.ofReal_toReal hmuFullNeTop
    rw [htoRealEq, ENNReal.ofReal_toReal hmuFinite.ne] at hround
    exact hround.symm
  have hmuFullLower : muFull K ≤ ∫⁻ y, ENNReal.ofReal (f y) ∂muFull :=
    (lintegral_indicator_one hKmeas).symm.trans_le (lintegral_mono hflow)
  exact hmuFullLower.trans (hmuFullEq.trans_le (hmuUpper.trans hB))

/-- Exhausting the open ball `Metric.ball x r` by an increasing sequence of closed balls, so that
`aux_car_variational_muFull_compact_bound` (proved for compact `K ⊆ Metric.ball x r`, not for the
whole open ball, since the compact-bump-sandwich lemma needs `K` compact) upgrades to the whole
ball via continuity from below. -/
theorem aux_car_variational_muFull_growth
    {d : ℕ} (cutoffSeq : ℕ → Measure (SpatialCoordinates d))
    (mu muFull : Measure (SpatialCoordinates d))
    [IsLocallyFiniteMeasure mu] [mu.IsOpenPosMeasure]
    (hmuconv : MeasuresConvergeLocally cutoffSeq mu)
    (hmuFullconv : MeasuresConvergeLocally cutoffSeq muFull)
    (x : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (B : ℝ≥0∞) (hBfin : B ≠ ⊤) (hB : mu (Metric.ball x r) ≤ B) :
    muFull (Metric.ball x r) ≤ B := by
  set s : ℕ → Set (SpatialCoordinates d) :=
    fun n => Metric.closedBall x (r - r / (n + 2)) with hsdef
  have hrn0 : ∀ n : ℕ, 0 < r - r / (n + 2) := by
    intro n
    have : r / ((n : ℝ) + 2) < r := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have hrnr : ∀ n : ℕ, r - r / (n + 2) < r := by
    intro n
    have : 0 < r / ((n : ℝ) + 2) := by positivity
    linarith
  have hmono : Monotone s := by
    intro m n hmn
    apply Metric.closedBall_subset_closedBall
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have h2 : 0 < (m : ℝ) + 2 := by positivity
    have h2' : 0 < (n : ℝ) + 2 := by positivity
    have hle : r / ((n : ℝ) + 2) ≤ r / ((m : ℝ) + 2) :=
      div_le_div_of_nonneg_left hr.le h2 (by linarith)
    linarith
  have hunion : (⋃ n, s n) = Metric.ball x r := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset (fun n => (Metric.closedBall_subset_ball (hrnr n)))
    · intro y hy
      rw [Metric.mem_ball] at hy
      have hδ : 0 < r - dist y x := by linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (r / (r - dist y x))
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      show dist y x ≤ r - r / (n + 2)
      have h2 : 0 < (n : ℝ) + 2 := by positivity
      have hn' : r / ((n : ℝ) + 2) < r - dist y x := by
        rw [div_lt_iff₀ h2]
        have : r < (r - dist y x) * n := by
          rw [div_lt_iff₀ hδ] at hn
          linarith
        nlinarith
      linarith
  have hcompact : ∀ n, IsCompact (s n) := fun n => isCompact_closedBall x _
  have hint : ∀ n, (interior (s n)).Nonempty := fun n =>
    ⟨x, interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball
      (Metric.mem_ball_self (hrn0 n))⟩
  have hsub : ∀ n, s n ⊆ Metric.ball x r := fun n => Metric.closedBall_subset_ball (hrnr n)
  have hbound : ∀ n, muFull (s n) ≤ B := fun n =>
    aux_car_variational_muFull_compact_bound cutoffSeq mu muFull hmuconv hmuFullconv
      x r (s n) (hcompact n) (hint n) (hsub n) B hBfin hB
  calc muFull (Metric.ball x r) = muFull (⋃ n, s n) := by rw [hunion]
    _ = ⨆ n, muFull (s n) := hmono.measure_iUnion
    _ ≤ B := iSup_le hbound

/-- Scaling the unit-norm holder package to arbitrary bounded data. -/
theorem aux_car_variational_holder_all
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Qtri : ℕ → Homogenization.TriadicCube d)
    (hr : ∀ n : ℕ, 0 < Homogenization.cubeScaleFactor (Qtri n))
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (RN : ℕ → ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRN_formula : ∀ (n N : ℕ) (omega : BilateralField d) (lam : ℝ)
        (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d),
      RN n N omega lam f x =
        ∫ path, (∫ t in Set.Ioi (0 : ℝ),
          Set.indicator
            {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
              (centeredCube (Homogenization.cubeCenter (Qtri n))
                (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d)) path}
            (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
          ∂(KN N (omega, x)))
    (n0 : ℕ)
    (hHolder : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (lam0 lam1 : ℝ), 0 < lam0 → lam0 ≤ lam1 →
        ∃ Kom : ℝ, 0 < Kom ∧ ∀ (N : ℕ) (lam : ℝ), lam0 ≤ lam → lam ≤ lam1 →
          ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ, ‖f‖ ≤ 1 →
            (∀ x ∈ closure (centeredCube (Homogenization.cubeCenter (Qtri n0))
                (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0) : Set (SpatialCoordinates d)),
              |RN n0 N omega lam f x| ≤ Kom) ∧
            ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter (Qtri n0))
                (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0) : Set (SpatialCoordinates d)),
            ∀ y ∈ closure (centeredCube (Homogenization.cubeCenter (Qtri n0))
                (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0) : Set (SpatialCoordinates d)),
              |RN n0 N omega lam f x - RN n0 N omega lam f y| ≤
                Kom * dist x y ^ (1 / 4 : ℝ)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ),
            ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter (Qtri n0))
                (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0) : Set (SpatialCoordinates d)),
            ∀ y ∈ closure (centeredCube (Homogenization.cubeCenter (Qtri n0))
                (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0) : Set (SpatialCoordinates d)),
              |RN n0 N omega lam f x - RN n0 N omega lam f y| ≤
                C * dist x y ^ (1 / 4 : ℝ) := by
  filter_upwards [hHolder] with omega hω
  intro lam hlam f
  let c : ℝ := max ‖f‖ 1
  have hc : 0 < c := lt_of_lt_of_le one_pos (le_max_right _ _)
  let f0 : BoundedContinuousFunction (SpatialCoordinates d) ℝ := c⁻¹ • f
  have hf0 : ‖f0‖ ≤ 1 := by
    dsimp [f0]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc]
    calc
      c⁻¹ * ‖f‖ = ‖f‖ / c := by rw [div_eq_mul_inv, mul_comm]
      _ ≤ 1 := by
        apply (div_le_iff₀ hc).2
        calc
          ‖f‖ ≤ max ‖f‖ 1 := le_max_left _ _
          _ = 1 * c := by simp [c]
  have hf_eq : c • f0 = f := by
    ext x
    dsimp [f0]
    rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  obtain ⟨C, hC, hCbound⟩ := hω lam lam hlam le_rfl
  refine ⟨c * C, mul_pos hc hC, ?_⟩
  intro N x hx y hy
  obtain ⟨_, hosc⟩ := hCbound N lam le_rfl le_rfl f0 hf0
  have h := hosc x hx y hy
  have hscale_x := aux_car_variational_RN_smul Qtri hr KN RN hRN_formula
    n0 N omega c lam f0 x
  have hscale_y := aux_car_variational_RN_smul Qtri hr KN RN hRN_formula
    n0 N omega c lam f0 y
  have hx_eq : RN n0 N omega lam f x = c * RN n0 N omega lam f0 x := by
    calc
      RN n0 N omega lam f x = RN n0 N omega lam (c • f0) x := by rw [hf_eq]
      _ = c * RN n0 N omega lam f0 x := hscale_x
  have hy_eq : RN n0 N omega lam f y = c * RN n0 N omega lam f0 y := by
    calc
      RN n0 N omega lam f y = RN n0 N omega lam (c • f0) y := by rw [hf_eq]
      _ = c * RN n0 N omega lam f0 y := hscale_y
  rw [hx_eq, hy_eq, ← mul_sub, abs_mul, abs_of_pos hc]
  exact (mul_le_mul_of_nonneg_left h hc.le).trans_eq (by ring)

theorem aux_car_variational_RN_continuous
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Qtri : ℕ → Homogenization.TriadicCube d)
    (hr : ∀ n : ℕ, 0 < Homogenization.cubeScaleFactor (Qtri n))
    {M : _root_.SubdiffusiveProcess.Model.GMCModel d}
    (RN : ℕ → ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (n0 : ℕ)
    (hHolderAll : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ),
            ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter (Qtri n0))
                (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0) : Set (SpatialCoordinates d)),
            ∀ y ∈ closure (centeredCube (Homogenization.cubeCenter (Qtri n0))
                (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0) : Set (SpatialCoordinates d)),
              |RN n0 N omega lam f x - RN n0 N omega lam f y| ≤
                C * dist x y ^ (1 / 4 : ℝ)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∀ N : ℕ, ContinuousOn (fun x => RN n0 N omega lam f x)
            (closure (centeredCube (Homogenization.cubeCenter (Qtri n0))
              (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0) : Set (SpatialCoordinates d))) := by
  filter_upwards [hHolderAll] with omega hω
  intro lam hlam f N
  obtain ⟨C, hC, hbound⟩ := hω lam hlam f
  rw [Metric.continuousOn_iff]
  intro b hb eps heps
  refine ⟨(eps / C) ^ 4, by positivity, ?_⟩
  intro a ha hdist
  have hab := hbound N a ha b hb
  rw [Real.dist_eq]
  rcases eq_or_lt_of_le (dist_nonneg : (0 : ℝ) ≤ dist a b) with hzero | hpos
  · rw [← hzero, Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0), mul_zero] at hab
    linarith
  · have hlt : dist a b ^ (1 / 4 : ℝ) < eps / C := by
      have hpow : ((eps / C) ^ 4 : ℝ) ^ (1 / 4 : ℝ) = eps / C := by
        have h4 : ((eps / C) ^ 4 : ℝ) = (eps / C) ^ (4 : ℝ) := by
          norm_num [Real.rpow_natCast]
        rw [h4, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ eps / C)
          (4 : ℝ) (1 / 4), show (4 : ℝ) * (1 / 4) = 1 by norm_num,
          Real.rpow_one]
      exact (Real.rpow_lt_rpow hpos.le hdist (by norm_num)).trans_eq hpow
    have hstrict : C * dist a b ^ (1 / 4 : ℝ) < eps := by
      simpa [mul_comm] using (lt_div_iff₀ hC).mp hlt
    linarith

theorem aux_car_variational_occupation_smul {d : ℕ}
    (nu : Measure (DiffusionPath d)) (U : Set (SpatialCoordinates d))
    (lam c : ℝ) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
          (fun s : ℝ => Real.exp (-lam * s) * (c • f) (path (Real.toNNReal s))) t) ∂nu =
      c * ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
          (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t) ∂nu := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with path
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
    simp only [BoundedContinuousFunction.coe_smul, smul_eq_mul]
    ring
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
    ring

theorem aux_car_variational_uniform_to_L2 {d : ℕ}
    (Q : Opens (SpatialCoordinates d))
    (hQ : volume (Q : Set (SpatialCoordinates d)) ≠ ⊤)
    (u : ℕ → DomainL2 Q) (v : DomainL2 Q)
    (U : ℕ → SpatialCoordinates d → ℝ) (V : SpatialCoordinates d → ℝ)
    (hU : ∀ n, (u n : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U n)
    (hV : (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V)
    (hunif : ∀ eps : ℝ, 0 < eps → ∃ n0 : ℕ, ∀ n, n0 ≤ n →
      ∀ x ∈ (Q : Set (SpatialCoordinates d)), |U n x - V x| < eps) :
    Tendsto u atTop (𝓝 v) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm' u v, ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with hεtop | hεtop
  · rw [hεtop]
    filter_upwards with n
    exact le_top
  · have hμtop : (volume.restrict (Q : Set (SpatialCoordinates d))) univ ≠ ⊤ := by
      rw [Measure.restrict_apply_univ]
      exact hQ
    have hεt : 0 < ε.toReal := ENNReal.toReal_pos (ne_of_gt hε) hεtop
    let M : ℝ := ((volume.restrict (Q : Set (SpatialCoordinates d))) univ).toReal
    have hM : 0 ≤ M := ENNReal.toReal_nonneg
    have hMpow : 0 ≤ M ^ (2:ℝ≥0∞).toReal⁻¹ := Real.rpow_nonneg hM _
    let r : ℝ := ε.toReal / (M ^ (2:ℝ≥0∞).toReal⁻¹ + 1)
    have hrpos : 0 < r := by
      have h : 0 < M ^ (2:ℝ≥0∞).toReal⁻¹ + 1 := by linarith
      exact div_pos hεt h
    obtain ⟨n0, hn0⟩ := hunif r hrpos
    refine Filter.eventually_atTop.mpr ⟨n0, fun n hn => ?_⟩
    have hbound : ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
        ‖((u n).val.cast - v.val.cast) x‖ ≤ r := by
      filter_upwards [hU n, hV, ae_restrict_mem Q.isOpen.measurableSet] with x hxU hxV hxQ
      change ‖(u n).val.cast x - v.val.cast x‖ ≤ r
      rw [hxU, hxV, Real.norm_eq_abs]
      exact le_of_lt (hn0 n hn x hxQ)
    calc eLpNorm ((u n).val.cast - v.val.cast) (2:ℝ≥0∞)
            (volume.restrict (Q : Set (SpatialCoordinates d)))
        ≤ ((volume.restrict (Q : Set (SpatialCoordinates d))) univ) ^ (2:ℝ≥0∞).toReal⁻¹
            * ENNReal.ofReal r :=
          eLpNorm_le_of_ae_bound ((u n).val.aestronglyMeasurable.sub v.val.aestronglyMeasurable) hbound
      _ = ENNReal.ofReal (M ^ (2:ℝ≥0∞).toReal⁻¹) * ENNReal.ofReal r := by
          rw [← ENNReal.ofReal_toReal hμtop,
            ENNReal.ofReal_rpow_of_nonneg hM (inv_nonneg.mpr ENNReal.toReal_nonneg)]
      _ = ENNReal.ofReal (M ^ (2:ℝ≥0∞).toReal⁻¹ * r) := by
          rw [← ENNReal.ofReal_mul hMpow]
      _ ≤ ENNReal.ofReal (ε.toReal) := ENNReal.ofReal_le_ofReal (by
          dsimp [r]
          have hM1 : 0 < M ^ (2:ℝ≥0∞).toReal⁻¹ + 1 := by linarith
          have hdiv : M ^ (2:ℝ≥0∞).toReal⁻¹ /
              (M ^ (2:ℝ≥0∞).toReal⁻¹ + 1) ≤ 1 := by
            rw [div_le_one hM1]
            linarith
          calc M ^ (2:ℝ≥0∞).toReal⁻¹ *
                (ε.toReal / (M ^ (2:ℝ≥0∞).toReal⁻¹ + 1))
              = ε.toReal * (M ^ (2:ℝ≥0∞).toReal⁻¹ /
                  (M ^ (2:ℝ≥0∞).toReal⁻¹ + 1)) := by ring
            _ ≤ ε.toReal * 1 := mul_le_mul_of_nonneg_left hdiv (le_of_lt hεt)
            _ = ε.toReal := mul_one _)
      _ = ε := ENNReal.ofReal_toReal hεtop

theorem aux_car_variational_weak_minimizer {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsym : ∀ u v, B u v = B v u) (hpos : ∀ v, 0 ≤ B v v)
    (L : V →ₗ[ℝ] ℝ) (u : V) (hu : ∀ v, B u v = L v) :
    ∀ v, B u u - 2 * L u ≤ B v v - 2 * L v := by
  intro v
  have hL : ∀ w, L w = B u w := fun w => (hu w).symm
  have hb : B (v - u) (v - u) = B v v - 2 * B u v + B u u := by
    rw [LinearMap.map_sub B v u, LinearMap.sub_apply,
      LinearMap.map_sub (B v) v u, LinearMap.map_sub (B u) v u, hsym v u]
    ring
  have hmain : (0:ℝ) ≤ B v v - 2 * L v - (B u u - 2 * L u) := by
    have hpu := hpos (v - u)
    rw [hb] at hpu
    rw [hL v, hL u]
    linarith
  linarith

theorem aux_car_variational_speed_restrict_finite {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ((cutoffSpeedMeasure M H omega N).restrict
      (closure (centeredCube z r hr : Set (SpatialCoordinates d)))) Set.univ < ⊤ := by
  rw [Measure.restrict_apply_univ]
  unfold cutoffSpeedMeasure
  rw [withDensity_apply _ isClosed_closure.measurableSet]
  have hK : IsCompact (closure (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    (centeredCube_isBounded z hr).isCompact_closure
  have hden : Continuous (cutoffSpeedDensity M H omega N) := by
    unfold cutoffSpeedDensity cutoffPotential
    exact Real.continuous_exp.comp (Continuous.sub
      ((H omega).continuous.add
        (continuous_finsetSum _ fun j _ => (omega (-(Int.ofNat j))).continuous))
      continuous_const)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hden.continuousOn
  have hbound : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
      (ENNReal.ofReal ∘ cutoffSpeedDensity M H omega N) x ≤ ENNReal.ofReal C := by
    intro x hx
    simp only [Function.comp_apply]
    have h1 : ‖cutoffSpeedDensity M H omega N x‖ ≤ C := hC x hx
    rw [Real.norm_eq_abs] at h1
    exact ENNReal.ofReal_le_ofReal (le_trans (le_abs_self _) h1)
  calc ∫⁻ a in closure (centeredCube z r hr : Set (SpatialCoordinates d)),
        (ENNReal.ofReal ∘ cutoffSpeedDensity M H omega N) a
      ≤ ∫⁻ _a in closure (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal C := setLIntegral_mono measurable_const hbound
    _ = ENNReal.ofReal C * volume (closure (centeredCube z r hr : Set (SpatialCoordinates d))) :=
        setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

theorem aux_car_variational_frontier_closure_cube {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    frontier (closure (centeredCube z r hr : Set (SpatialCoordinates d))) =
      frontier (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  have hgeom := isOpenBoundedConvexDomain_centeredCube z hr
  have hconv : Convex ℝ (centeredCube z r hr : Set (SpatialCoordinates d)) := hgeom.2.2
  have hopen : IsOpen (centeredCube z r hr : Set (SpatialCoordinates d)) := hgeom.1
  have hz : z ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    change z ∈ Metric.ball z (r / 2)
    exact Metric.mem_ball_self (half_pos hr)
  have hne : (interior (centeredCube z r hr : Set (SpatialCoordinates d))).Nonempty := by
    rw [hopen.interior_eq]
    exact ⟨z, hz⟩
  rw [← closure_sdiff_interior (closure (centeredCube z r hr : Set (SpatialCoordinates d))),
      ← closure_sdiff_interior (centeredCube z r hr : Set (SpatialCoordinates d)),
      closure_closure]
  have hinter : interior (closure (centeredCube z r hr : Set (SpatialCoordinates d))) =
      interior (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    Convex.interior_closure_eq_interior_of_nonempty_interior hconv hne
  rw [hinter]

theorem aux_car_variational_cc_tendsto {d : ℕ}
    (μN : ℕ → Measure (SpatialCoordinates d)) (μ : Measure (SpatialCoordinates d))
    (hconv : MeasuresConvergeLocally μN μ)
    {S : Set (SpatialCoordinates d)} (hS : IsCompact S)
    (hN : ∀ N, μN N Sᶜ = 0) (h : μ Sᶜ = 0)
    (g : SpatialCoordinates d → ℝ) (hg : Continuous g) :
    Tendsto (fun N => ∫ x, g x ∂μN N) atTop (𝓝 (∫ x, g x ∂μ)) := by
  obtain ⟨χ, hχ1, -, hχc, -⟩ :=
    exists_continuous_one_zero_of_isCompact hS isClosed_empty (Set.disjoint_empty S)
  let G : C_c(SpatialCoordinates d, ℝ) :=
    ⟨⟨fun x => χ x * g x, χ.continuous.mul hg⟩, hχc.mul_right⟩
  have key : ∀ ν : Measure (SpatialCoordinates d), ν Sᶜ = 0 →
      ∫ x, G x ∂ν = ∫ x, g x ∂ν := by
    intro ν hν
    apply integral_congr_ae
    have hae : ∀ᵐ x ∂ν, x ∈ S := mem_ae_iff.2 hν
    filter_upwards [hae] with x hx
    simp [G, hχ1 hx]
  have hG := hconv G
  rw [key μ h] at hG
  simpa only [key _ (hN _)] using hG

theorem aux_car_variational_energy_upper {d : ℕ} {U : Opens (SpatialCoordinates d)}
    {a : PositiveCoefficient U} {ν : Measure (SpatialCoordinates d)}
    (hνfin : ν Set.univ < ⊤) (D : ℝ)
    (hν : ν ≤ ENNReal.ofReal D • volume.restrict (U : Set (SpatialCoordinates d)))
    (F : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (hF : MemLp (F : SpatialCoordinates d → ℝ) 2 ν)
    (lam : ℝ) (hlam : 0 < lam) (R : SpatialCoordinates d → ℝ)
    (u : killedSobolevGraph U)
    (hRu : R =ᵐ[volume.restrict (U : Set (SpatialCoordinates d))]
      ((u : SobolevData U).1 : SpatialCoordinates d → ℝ))
    (hweak : ∀ w : killedSobolevGraph U,
      sobolevCoefficientForm a (u : SobolevData U) (w : SobolevData U) =
        ∫ x, (F x - lam * R x) * (w : SobolevData U).1 x ∂ν) :
    sobolevCoefficientForm a (u : SobolevData U) (u : SobolevData U) ≤
      ‖F‖ ^ 2 * (ν Set.univ).toReal / lam := by
  let : IsFiniteMeasure ν := ⟨hνfin⟩
  have hmem : MemLp ((u : SobolevData U).1 : SpatialCoordinates d → ℝ) 2 ν :=
    (Lp.memLp _).of_measure_le_smul ENNReal.ofReal_ne_top hν
  have hmin := aux_prop_uniform_resolvent_ident_finite_min U a ν D hν F hF lam hlam.le R u hRu hweak
    (0 : killedSobolevGraph U)
  have hprod : Integrable (fun x => F x * (u : SobolevData U).1 x) ν :=
    aux_prop_uniform_resolvent_ident_integrable_mul hF hmem
  have hpoint : ∀ x, 2 * F x * (u : SobolevData U).1 x ≤
      lam * ((u : SobolevData U).1 x) ^ 2 + (F x) ^ 2 / lam := by
    intro x
    have hsquare : 0 ≤ (lam * (u : SobolevData U).1 x - F x) ^ 2 := sq_nonneg _
    have hmul : 2 * lam * (F x * (u : SobolevData U).1 x) ≤
        lam ^ 2 * ((u : SobolevData U).1 x) ^ 2 + (F x) ^ 2 := by
      nlinarith
    calc
      2 * F x * (u : SobolevData U).1 x =
          (2 * lam * (F x * (u : SobolevData U).1 x)) / lam := by field_simp
      _ ≤ (lam ^ 2 * ((u : SobolevData U).1 x) ^ 2 + (F x) ^ 2) / lam :=
        div_le_div_of_nonneg_right hmul hlam.le
      _ = lam * ((u : SobolevData U).1 x) ^ 2 + (F x) ^ 2 / lam := by
        field_simp
  have hYoung : 2 * ∫ x, F x * (u : SobolevData U).1 x ∂ν ≤
      lam * ∫ x, ((u : SobolevData U).1 x) ^ 2 ∂ν +
        (1 / lam) * ∫ x, (F x) ^ 2 ∂ν := by
    calc
      _ = ∫ x, (2 * (F x * (u : SobolevData U).1 x)) ∂ν := by
        rw [integral_const_mul]
      _ ≤ ∫ x, (lam * ((u : SobolevData U).1 x) ^ 2 + (F x) ^ 2 / lam) ∂ν := by
        apply integral_mono_ae (hprod.const_mul 2)
          ((hmem.integrable_sq.const_mul lam).add (hF.integrable_sq.div_const lam))
        exact Eventually.of_forall (fun x => by
          simpa [mul_assoc, mul_comm, mul_left_comm] using hpoint x)
      _ = _ := by
        rw [integral_add (hmem.integrable_sq.const_mul lam)
          (hF.integrable_sq.div_const lam), integral_const_mul, integral_div]
        ring
  have hF2 : ∫ x, (F x) ^ 2 ∂ν ≤ ‖F‖ ^ 2 * (ν Set.univ).toReal := by
    calc
      _ ≤ ∫ _x, ‖F‖ ^ 2 ∂ν := by
        apply integral_mono_ae hF.integrable_sq (integrable_const _)
        filter_upwards [] with x
        have hs := (sq_le_sq₀ (abs_nonneg (F x)) (norm_nonneg F)).2
          (by simpa [Real.norm_eq_abs] using F.norm_coe_le_norm x)
        simpa [sq_abs] using hs
      _ = ‖F‖ ^ 2 * (ν Set.univ).toReal := by
        rw [integral_const]
        rw [measureReal_def]
        simp only [smul_eq_mul]
        ring
  have hzero_data : ((0 : killedSobolevGraph U) : SobolevData U) = 0 := rfl
  rw [hzero_data] at hmin
  have hformzero : sobolevCoefficientForm a (0 : SobolevData U) (0 : SobolevData U) = 0 := by
    simp only [map_zero]
  have hzero_fun : ((0 : SobolevData U).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (U : Set (SpatialCoordinates d))] 0 :=
    Lp.coeFn_zero ℝ 2 _
  have hzero_fun_nu : ((0 : SobolevData U).1 : SpatialCoordinates d → ℝ) =ᵐ[ν] 0 :=
    (Measure.absolutelyContinuous_of_le_smul hν).ae_eq hzero_fun
  have hzsq : ∫ x, ((0 : SobolevData U).1 x) ^ 2 ∂ν = 0 := by
    calc
      _ = ∫ _x, (0 : ℝ) ∂ν := by
        apply integral_congr_ae
        filter_upwards [hzero_fun_nu] with x hx
        have hx' : (0 : SobolevData U).1 x = 0 := by
          convert hx using 1
        change ((0 : SobolevData U).1 x) ^ 2 = (0 : ℝ)
        rw [hx']
        norm_num
      _ = 0 := by simp
  have hzlin : ∫ x, F x * (0 : SobolevData U).1 x ∂ν = 0 := by
    calc
      _ = ∫ _x, (0 : ℝ) ∂ν := by
        apply integral_congr_ae
        filter_upwards [hzero_fun_nu] with x hx
        have hx' : (0 : SobolevData U).1 x = 0 := by
          convert hx using 1
        change F x * (0 : SobolevData U).1 x = (0 : ℝ)
        rw [hx']
        ring
      _ = 0 := by simp
  rw [hformzero, hzsq, hzlin] at hmin
  have hmin' : sobolevCoefficientForm a (u : SobolevData U) (u : SobolevData U) +
      lam * ∫ x, ((u : SobolevData U).1 x) ^ 2 ∂ν -
        2 * ∫ x, F x * (u : SobolevData U).1 x ∂ν ≤ 0 := by
    simpa only [Submodule.coe_zero, Prod.fst_zero, map_zero, Pi.zero_apply, zero_mul,
      mul_zero, integral_zero, sub_zero, add_zero] using hmin
  have hYoung' := mul_le_mul_of_nonneg_left hYoung hlam.le
  have hYoung'' : lam * (2 * ∫ x, F x * (u : SobolevData U).1 x ∂ν) ≤
      lam ^ 2 * ∫ x, ((u : SobolevData U).1 x) ^ 2 ∂ν +
        ∫ x, (F x) ^ 2 ∂ν := by
    convert hYoung' using 1 ; field_simp
  apply (le_div_iff₀ hlam).2
  have hmin'' := mul_le_mul_of_nonneg_left hmin' hlam.le
  ring_nf at hmin'' hYoung''
  have hA : lam * sobolevCoefficientForm a (u : SobolevData U) (u : SobolevData U) ≤
      ∫ x, (F x) ^ 2 ∂ν := by
    linarith
  calc
    sobolevCoefficientForm a (u : SobolevData U) (u : SobolevData U) * lam =
        lam * sobolevCoefficientForm a (u : SobolevData U) (u : SobolevData U) := by ring
    _ ≤ ∫ x, (F x) ^ 2 ∂ν := hA
    _ ≤ ‖F‖ ^ 2 * (ν Set.univ).toReal := hF2

theorem aux_car_variational_finite_cutoff_data
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ)
    (Qtri : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Qtri)
    (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : IsMarkovKernel (KN N))
    (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
    (hL : ∀ x, Measure.map MarkovProcess.LifetimePath.ofContinuousPath
      ((KN N).comap (fun y : SpatialCoordinates d => (omega, y))
        (measurable_const.prodMk measurable_id) x) = L N omega x)
    (hLD : SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusion
      (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (L N omega))
    (rN : SpatialCoordinates d → ℝ)
    (hrN : ∀ x, rN x = aux_car_variational_hol_occupation
      ((KN N).comap (fun y : SpatialCoordinates d => (omega, y))
        (measurable_const.prodMk measurable_id))
      (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) (hr)) lam f x) :
    ∃ u : killedSobolevGraph
        (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) (hr)),
      rN =ᵐ[volume.restrict
        (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) (hr) : Set (SpatialCoordinates d))]
        ((u : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) (hr))).1 : SpatialCoordinates d → ℝ) ∧
      (∀ w : killedSobolevGraph
          (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) (hr)),
        sobolevCoefficientForm
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
              (Homogenization.cubeCenter Qtri) (hr))
            (u : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) (hr))) (w : SobolevData _ ) =
          ∫ x, (f x - lam * rN x) *
            (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) (hr))).1 x ∂
              ((cutoffSpeedMeasure M H omega N).restrict
                (closure (centeredCube (Homogenization.cubeCenter Qtri)
                  (Homogenization.cubeScaleFactor Qtri) (hr) : Set (SpatialCoordinates d))))) ∧
      sobolevCoefficientForm
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
              (Homogenization.cubeCenter Qtri) (hr))
            (u : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) (hr)))
            (u : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) (hr))) ≤
        ‖f‖ ^ 2 *
          (((cutoffSpeedMeasure M H omega N).restrict
            (closure (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) (hr) : Set (SpatialCoordinates d))))
            (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) (hr) : Set (SpatialCoordinates d))).toReal / lam := by
  let Q0 := centeredCube (Homogenization.cubeCenter Qtri)
    (Homogenization.cubeScaleFactor Qtri) (hr)
  let K : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d)) :=
    (KN N).comap (fun x : SpatialCoordinates d => (omega, x))
      (measurable_const.prodMk measurable_id)
  let : IsMarkovKernel K := by
    dsimp [K]
    infer_instance
  have hLK : ∀ x, Measure.map LifetimePath.ofContinuousPath (K x) = L N omega x := by
    intro x
    simpa [K] using hL x
  obtain ⟨u, hu, hw⟩ := aux_car_variational_hol_weak_ident M H omega N K
    (L N omega) hLK hLD (Homogenization.cubeCenter Qtri)
    (Homogenization.cubeScaleFactor Qtri) (hr) lam hlam f
  have hocc : ∀ x, rN x =
      aux_car_variational_hol_occupation K (Q0 : Set (SpatialCoordinates d)) lam f x := by
    intro x
    simpa [K, Q0] using hrN x
  have hrestrict :
      (cutoffSpeedMeasure M H omega N).restrict (closure (Q0 : Set (SpatialCoordinates d))) =
        (cutoffSpeedMeasure M H omega N).restrict (Q0 : Set (SpatialCoordinates d)) := by
    unfold cutoffSpeedMeasure
    rw [restrict_withDensity isClosed_closure.measurableSet,
      restrict_withDensity Q0.isOpen.measurableSet,
      aux_prop_uniform_resolvent_ident_cube_restrict_closure
        (Homogenization.cubeCenter Qtri) (hr)]
  have hweak : ∀ w : killedSobolevGraph Q0,
      sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
            (Homogenization.cubeCenter Qtri) (hr))
          (u : SobolevData Q0) (w : SobolevData Q0) =
        ∫ x, (f x - lam * rN x) * (w : SobolevData Q0).1 x ∂
          ((cutoffSpeedMeasure M H omega N).restrict (closure (Q0 : Set (SpatialCoordinates d)))) := by
    intro w
    rw [hrestrict]
    simpa [hocc] using hw w
  let ν : Measure (SpatialCoordinates d) :=
    (cutoffSpeedMeasure M H omega N).restrict (closure (Q0 : Set (SpatialCoordinates d)))
  have hνfin : ν Set.univ < ⊤ := by
    dsimp [ν]
    exact aux_car_variational_speed_restrict_finite M H omega N
      (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) (hr)
  obtain ⟨D, hD0, hD⟩ := aux_prop_uniform_resolvent_ident_density_le M H omega N
    (Homogenization.cubeCenter Qtri) (hr)
  let : IsFiniteMeasure ν := ⟨hνfin⟩
  have hF : MemLp (f : SpatialCoordinates d → ℝ) 2 ν :=
    MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖
      (Eventually.of_forall fun x => f.norm_coe_le_norm x)
  have henergyν := aux_car_variational_energy_upper hνfin D hD f hF lam hlam
    rN u
    (by
      filter_upwards [Filter.Eventually.of_forall hocc, hu] with x hx hxu
      exact hx.trans hxu.symm)
    (by simpa [ν] using hweak)
  have hνQ : ν (Q0 : Set (SpatialCoordinates d)) = ν Set.univ := by
    dsimp [ν]
    rw [hrestrict, Measure.restrict_apply Q0.isOpen.measurableSet,
      Measure.restrict_apply_univ]
    simp
  refine ⟨u, ?_, hweak, ?_⟩
  · filter_upwards [Filter.Eventually.of_forall hocc, hu] with x hx hxu
    exact hx.trans hxu.symm
  · change sobolevCoefficientForm _ (u : SobolevData Q0) (u : SobolevData Q0) ≤
      ‖f‖ ^ 2 * (ν (Q0 : Set (SpatialCoordinates d))).toReal / lam
    simpa [hνQ] using henergyν

theorem aux_car_variational_finite_cutoff_event
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (_PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hinput : aux_cutoff_lifetime_package_LocalInput M H KN)
    (Qtri : ℕ → Homogenization.TriadicCube d)
    (hr : ∀ n, 0 < Homogenization.cubeScaleFactor (Qtri n))
    (RN : ℕ → ℕ → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRN : ∀ (n N : ℕ) (omega : BilateralField d) (lam : ℝ)
        (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d),
      RN n N omega lam f x =
        ∫ path, (∫ t in Set.Ioi (0 : ℝ),
          Set.indicator
            {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
              (centeredCube (Homogenization.cubeCenter (Qtri n))
                (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d)) path}
            (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
          ∂(KN N (omega, x)))
    (n0 : ℕ) (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
    (_hL : ∀ N omega x,
      Measure.map MarkovProcess.LifetimePath.ofContinuousPath (KN N (omega, x)) = L N omega x)
    (_hLlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusion
        (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (L N omega)) :
    let Q0 : Opens (SpatialCoordinates d) :=
      centeredCube (Homogenization.cubeCenter (Qtri n0))
        (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0)
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∃ u : killedSobolevGraph Q0,
            (RN n0 N omega lam f) =ᵐ[volume.restrict (Q0 : Set (SpatialCoordinates d))]
              ((u : SobolevData Q0).1 : SpatialCoordinates d → ℝ) ∧
            (∀ w : killedSobolevGraph Q0,
              sobolevCoefficientForm
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (Homogenization.cubeCenter (Qtri n0)) (hr n0))
                  (u : SobolevData Q0) (w : SobolevData Q0) =
                ∫ x, (f x - lam * RN n0 N omega lam f x) *
                  (w : SobolevData Q0).1 x ∂
                    ((cutoffSpeedMeasure M H omega N).restrict
                      (closure (Q0 : Set (SpatialCoordinates d))))) ∧
            sobolevCoefficientForm
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (Homogenization.cubeCenter (Qtri n0)) (hr n0))
                  (u : SobolevData Q0) (u : SobolevData Q0) ≤
              ‖f‖ ^ 2 *
                (((cutoffSpeedMeasure M H omega N).restrict
                  (closure (Q0 : Set (SpatialCoordinates d))))
                  (Q0 : Set (SpatialCoordinates d))).toReal / lam := by
  obtain ⟨L', hL', hLlocal', _⟩ := aux_cutoff_lifetime_package_local M H KN hinput
  dsimp
  filter_upwards [hLlocal'] with omega hLD
  intro N lam hlam f
  apply aux_car_variational_finite_cutoff_data M H omega N
    (Qtri n0) (hr n0) lam hlam f KN (hKN N) L' (by
      intro x
      simpa using hL' N omega x) (hLD N) (fun x => RN n0 N omega lam f x) (by
      intro x
      simpa [aux_car_variational_hol_occupation] using hRN n0 N omega lam f x)

/-- At most one killed-Sobolev-graph element projects to a given `DomainL2` value: weak
derivatives are a.e. unique (`weakSobolevGraph_gradient_unique`), and `killedSobolevGraph Ω` is a
submodule of `weakSobolevGraph Ω`. -/
theorem aux_car_variational_killed_fst_unique {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    {v1 v2 : killedSobolevGraph Ω}
    (h : (v1 : SobolevData Ω).1 = (v2 : SobolevData Ω).1) : v1 = v2 := by
  apply Subtype.ext
  apply Prod.ext h
  have h1 : ((v1 : SobolevData Ω).1, (v1 : SobolevData Ω).2) ∈ weakSobolevGraph Ω := by
    have := killedSobolevGraph_le_weakSobolevGraph v1.2
    simpa using this
  have h2 : ((v1 : SobolevData Ω).1, (v2 : SobolevData Ω).2) ∈ weakSobolevGraph Ω := by
    have hv2 := killedSobolevGraph_le_weakSobolevGraph v2.2
    rw [show (v2 : SobolevData Ω) = ((v2 : SobolevData Ω).1, (v2 : SobolevData Ω).2) from rfl,
      ← h] at hv2
    exact hv2
  exact weakSobolevGraph_gradient_unique h1 h2

/-- Bridges `car_variational`'s per-cube data (strong resolvent convergence `hG`, the
`lem_as_coarse` fractional coercivity constant `K1`/`hc1`, the half-order trace
characterization `hT`) into `aux_prop_speed_resolvent_parts_AB`'s abstract minimization
conclusion (existence, minimality, uniqueness of the killed-resolvent variational limit).
Isolated as its own declaration (house elaboration-budget rule): assembling this inline
inside `car_variational`'s own proof pushed the whole declaration past the 200000-heartbeat
ceiling. Does NOT establish the identification `Rn =ᵃᵉ ustar` with the actual occupation-time
resolvents; that is a separate step. -/
theorem aux_car_variational_variational_step
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHI : InfraredCharacterization M H)
    (omega : BilateralField d)
    (Qtri : Homogenization.TriadicCube d) (hr : 0 < Homogenization.cubeScaleFactor Qtri)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr),
      ‖(v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube
          (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) v‖)
    (G : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) →L[ℝ]
      DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr))
    (hG : ∀ f : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr),
      Tendsto (fun N : ℕ =>
        (responseSolution (killedResponseSpace (Ω := centeredCube
              (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) hP)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
            ((sobolevVolumeLoad f).comp
              (killedResponseSpace (Ω := centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr) hP).space.subtypeL)).val.1)
        atTop (𝓝 (G f)))
    (K1 : ℝ) (hK1 : 0 < K1)
    (hc1 : ∀ (N : ℕ) (v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr)),
      cubeFractionalSqNorm hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr threeQuarterOrder
          (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr)).1 ≤
        K1 * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
            (Homogenization.cubeCenter Qtri) hr)
          (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr))
          (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr)))
    (mu muFull : Measure (SpatialCoordinates d))
    (hmu : mu = muFull.restrict
      (closure (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))
    (hmufin : mu Set.univ < ⊤) (K C : ℝ)
    (T : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder → Lp ℝ 2 mu)
    (hT : MeasureTraceCharacterization hd Qtri hr mu K C T)
    (i : (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)) →
      (limitFormEnergy G u).toENNReal ≠ ⊤ →
      CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder)
    (hi : ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr))
      (hu : (limitFormEnergy G u).toENNReal ≠ ⊤), (i u hu).val 0 = u)
    (J : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) → SpatialCoordinates d → ℝ)
    (hJ : ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr))
      (hu : (limitFormEnergy G u).toENNReal ≠ ⊤),
      (J u) =ᵐ[mu] (T (i u hu) : SpatialCoordinates d → ℝ))
    (Ktr : ℝ) (hKtr : 0 ≤ Ktr)
    (hJtr : ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr))
      (_hu : (limitFormEnergy G u).toENNReal ≠ ⊤),
      (∫⁻ x, ENNReal.ofReal (J u x ^ 2) ∂mu) ≤
        ENNReal.ofReal Ktr * (limitFormEnergy G u).toENNReal)
    (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    ∃ ustar : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr),
      (limitFormEnergy G ustar).toENNReal ≠ ⊤ ∧
      (∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr),
        (limitFormEnergy G w).toENNReal ≠ ⊤ →
        (limitFormEnergy G ustar).toENNReal.toReal + lam * (∫ x, J ustar x ^ 2 ∂mu) -
            2 * ∫ x, f x * J ustar x ∂mu ≤
          (limitFormEnergy G w).toENNReal.toReal + lam * (∫ x, J w x ^ 2 ∂mu) -
            2 * ∫ x, f x * J w x ∂mu) ∧
      (∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr),
        (limitFormEnergy G w).toENNReal ≠ ⊤ →
        (∀ v : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr),
          (limitFormEnergy G v).toENNReal ≠ ⊤ →
          (limitFormEnergy G w).toENNReal.toReal + lam * (∫ x, J w x ^ 2 ∂mu) -
              2 * ∫ x, f x * J w x ∂mu ≤
            (limitFormEnergy G v).toENNReal.toReal + lam * (∫ x, J v x ^ 2 ∂mu) -
              2 * ∫ x, f x * J v x ∂mu) →
        w = ustar) := by
  obtain ⟨hsym, hpos, _, _⟩ := aux_car_variational_mosco (Homogenization.cubeCenter Qtri)
    (Homogenization.cubeScaleFactor Qtri) hr hP
    (fun N => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
    G hG
  obtain ⟨hE0, _⟩ := aux_car_variational_energy_algebra (Homogenization.cubeCenter Qtri)
    (Homogenization.cubeScaleFactor Qtri) hr G hsym hpos
  obtain ⟨hclosed, hpara, hscale⟩ := aux_car_variational_energy_properties
    (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr G hsym hpos
  obtain ⟨Ccoer, hCcoer, hcoer_cond⟩ := aux_car_variational_limit_coercive hd Sf M H hHI omega
    (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr hP K1 hK1 hc1 G
    (fun N => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
    (fun _ => rfl) hsym hpos hG
  have hcoer : ∃ Ccoer : ℝ, 0 < Ccoer ∧
      ∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr),
        ENNReal.ofReal (‖w‖ ^ 2) ≤ ENNReal.ofReal Ccoer * (limitFormEnergy G w).toENNReal := by
    refine ⟨Ccoer, hCcoer, fun w => ?_⟩
    by_cases hw : (limitFormEnergy G w).toENNReal = ⊤
    · rw [hw, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hCcoer).ne']
      exact le_top
    · exact hcoer_cond w hw
  have hpara' : ∀ (w1 w2 : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr)),
      (limitFormEnergy G w1).toENNReal ≠ ⊤ → (limitFormEnergy G w2).toENNReal ≠ ⊤ →
      (limitFormEnergy G (w1 + w2)).toENNReal.toReal +
          (limitFormEnergy G (w1 - w2)).toENNReal.toReal =
        2 * (limitFormEnergy G w1).toENNReal.toReal +
          2 * (limitFormEnergy G w2).toENNReal.toReal := by
    intro w1 w2 hw1 hw2
    rw [EReal.toReal_toENNReal (limitFormEnergy_nonneg G (w1 + w2)),
      EReal.toReal_toENNReal (limitFormEnergy_nonneg G (w1 - w2)),
      EReal.toReal_toENNReal (limitFormEnergy_nonneg G w1),
      EReal.toReal_toENNReal (limitFormEnergy_nonneg G w2)]
    exact hpara w1 w2 hw1 hw2
  exact aux_prop_speed_resolvent_parts_AB hd Qtri hr G (fun u => (limitFormEnergy G u).toENNReal)
    (fun _ => rfl) mu muFull hmu hmufin K C T hT i hi J hJ hcoer
    hE0 hclosed hpara' hscale Ktr hKtr hJtr lam hlam f

/-- `∫⁻ x, ofReal((g x)²) ∂μ = ofReal(‖g‖²)` for any `g : Lp ℝ 2 μ` (any measure `μ`) — the same
identity as `lintegral_coordinate_sq_eq_sum_norm_sq` specialized to a single (`k = 1`) coordinate,
generalized off `DomainL2 Ω = Lp ℝ 2 (volume.restrict Ω)` to an arbitrary measure. -/
theorem aux_car_variational_Ktr_lintegral_sq_eq_norm_sq
    {d : ℕ} {mu : Measure (SpatialCoordinates d)} (g : Lp ℝ 2 mu) :
    (∫⁻ x, ENNReal.ofReal ((g x) ^ 2) ∂mu) = ENNReal.ofReal (‖g‖ ^ 2) := by
  have hi : Integrable (fun x => (g x) ^ 2) mu := (Lp.memLp g).integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all mu fun x => sq_nonneg (g x))]
  congr 1
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact ae_of_all mu fun x => by simp [pow_two]

/-- `(A ^ r) ^ (2:ℕ) = A ^ (r * 2)` for `A ≥ 0` — converts a squared `rpow` term back to a single
`rpow`, the one fiddly step in combining the two coercivity bounds' fractional exponents. -/
theorem aux_car_variational_Ktr_rpow_sq {A r : ℝ} (hA : 0 ≤ A) :
    (A ^ r) ^ (2 : ℕ) = A ^ (r * 2) := by
  rw [← Real.rpow_natCast (A ^ r) 2, ← Real.rpow_mul hA]
  norm_num

/-- `(A ^ (2:ℕ)) ^ s = A ^ (2 * s)` for `A ≥ 0` — the reverse composition, `rpow` on the outside
of a square, used to convert a squared-coercivity bound into the matching fractional power. -/
theorem aux_car_variational_Ktr_sq_rpow {A s : ℝ} (hA : 0 ≤ A) :
    (A ^ (2 : ℕ)) ^ s = A ^ (2 * s) := by
  rw [← Real.rpow_natCast A 2, ← Real.rpow_mul hA]
  norm_num

/-- `E ^ (1/3) * E ^ (2/3) = E` for `E ≥ 0` — the exponent-additivity step (`1/3 + 2/3 = 1`)
combining the two coercivity bounds' contributions into a single power of the energy. -/
theorem aux_car_variational_Ktr_rpow_split {E : ℝ} (hE : 0 ≤ E) :
    E ^ (1 / 3 : ℝ) * E ^ (2 / 3 : ℝ) = E := by
  rcases eq_or_lt_of_le hE with h | h
  · have h : E = 0 := h.symm
    rw [h, Real.zero_rpow (show (1 / 3 : ℝ) ≠ 0 by norm_num),
      Real.zero_rpow (show (2 / 3 : ℝ) ≠ 0 by norm_num), mul_zero]
  · rw [← Real.rpow_add h]
    norm_num

/-- Pure real-number combination step for `Ktr` (house rule: keep the fractional-exponent algebra
in its own small, type-simple declaration, separate from the heavy dependent types of `CubeFractionalL2`/`DomainL2`
that make `aux_car_variational_Ktr_bound` itself expensive to elaborate). Given the two `1/2`-order
coercivity bounds on `A := ‖u‖/√vol` and `B :=` the three-quarter-order norm, and the interpolation
bound on `Nh :=` the half-order norm, concludes the single degree-1 bound on `Nh²`. -/
theorem aux_car_variational_Ktr_real_combine {A B Cint Ccoer Cbase vol E Nh : ℝ}
    (hvol : 0 < vol) (hCcoer : 0 ≤ Ccoer) (hCbase : 0 < Cbase)
    (hE : 0 ≤ E) (hA : 0 ≤ A) (hB : 0 ≤ B) (hNh : 0 ≤ Nh)
    (hA2 : A ^ 2 ≤ Ccoer / vol * E) (hB2 : B ^ 2 ≤ Cbase * E)
    (hcombine : Nh ≤ Cint * A ^ (1 / 3 : ℝ) * B ^ (2 / 3 : ℝ)) :
    Nh ^ 2 ≤ Cint ^ 2 * (Ccoer / vol) ^ (1 / 3 : ℝ) * Cbase ^ (2 / 3 : ℝ) * E := by
  have hA23 : A ^ (2 / 3 : ℝ) ≤ (Ccoer / vol * E) ^ (1 / 3 : ℝ) := by
    have h := Real.rpow_le_rpow (sq_nonneg A) hA2 (by norm_num : (0:ℝ) ≤ 1 / 3)
    rw [aux_car_variational_Ktr_sq_rpow hA, show (2:ℝ) * (1/3) = 2/3 by norm_num] at h
    exact h
  have hB43 : B ^ (4 / 3 : ℝ) ≤ (Cbase * E) ^ (2 / 3 : ℝ) := by
    have h := Real.rpow_le_rpow (sq_nonneg B) hB2 (by norm_num : (0:ℝ) ≤ 2 / 3)
    rw [aux_car_variational_Ktr_sq_rpow hB, show (2:ℝ) * (2/3) = 4/3 by norm_num] at h
    exact h
  have hsq : Nh ^ 2 ≤ Cint ^ 2 * (A ^ (2 / 3 : ℝ) * B ^ (4 / 3 : ℝ)) := by
    calc Nh ^ 2 ≤ (Cint * A ^ (1 / 3 : ℝ) * B ^ (2 / 3 : ℝ)) ^ 2 :=
          pow_le_pow_left₀ hNh hcombine 2
      _ = Cint ^ 2 * (A ^ (2 / 3 : ℝ) * B ^ (4 / 3 : ℝ)) := by
          rw [mul_pow, mul_pow, aux_car_variational_Ktr_rpow_sq hA,
            aux_car_variational_Ktr_rpow_sq hB]
          ring
  have hEsplit : (Ccoer / vol * E) ^ (1 / 3 : ℝ) * (Cbase * E) ^ (2 / 3 : ℝ) =
      (Ccoer / vol) ^ (1 / 3 : ℝ) * Cbase ^ (2 / 3 : ℝ) * E := by
    rw [Real.mul_rpow (by positivity) hE, Real.mul_rpow hCbase.le hE]
    calc (Ccoer / vol) ^ (1/3:ℝ) * E ^ (1/3:ℝ) * (Cbase ^ (2/3:ℝ) * E ^ (2/3:ℝ))
        = (Ccoer / vol) ^ (1/3:ℝ) * Cbase ^ (2/3:ℝ) * (E ^ (1/3:ℝ) * E ^ (2/3:ℝ)) := by ring
      _ = (Ccoer / vol) ^ (1/3:ℝ) * Cbase ^ (2/3:ℝ) * E := by
          rw [aux_car_variational_Ktr_rpow_split hE]
  calc Nh ^ 2 ≤ Cint ^ 2 * (A ^ (2 / 3 : ℝ) * B ^ (4 / 3 : ℝ)) := hsq
    _ ≤ Cint ^ 2 * ((Ccoer / vol * E) ^ (1 / 3 : ℝ) * (Cbase * E) ^ (2 / 3 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left (mul_le_mul hA23 hB43 (by positivity) (by positivity))
          (by positivity)
    _ = Cint ^ 2 * (Ccoer / vol) ^ (1 / 3 : ℝ) * Cbase ^ (2 / 3 : ℝ) * E := by
        rw [hEsplit]; ring

/-- Given ANY witness `w0`, `T (w0 - w0) = 0` for ANY `MeasureTraceCharacterization` — generic
and omega-independent, extracted into its own declaration (house elaboration-budget rule) since
`aux_car_variational_Ktr_bound`'s body was still too large even after moving the fractional-
exponent algebra out. `CubeFractionalL2` has no `Zero` instance (it is a plain finite-seminorm
subtype, not a submodule), so the "zero" here is built as `w0 - w0` (coordinatewise, on the
underlying `Fin 1 → DomainL2` family), finite via the already-proven `cubeFractionalL2Seminorm_
sub_lt_top` applied to `w0` with itself — avoiding re-deriving finiteness of the seminorm at the
zero function directly. -/
theorem aux_car_variational_Ktr_T_zero {d : ℕ} (hd : 2 ≤ d)
    {Qtri : Homogenization.TriadicCube d} {hr : 0 < Homogenization.cubeScaleFactor Qtri}
    {mu : Measure (SpatialCoordinates d)} {K C : ℝ}
    {T : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder → Lp ℝ 2 mu}
    (hT : MeasureTraceCharacterization hd Qtri hr mu K C T)
    (w0 : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder) :
    ∃ z0 : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder,
      z0.val 0 = w0.val 0 - w0.val 0 ∧ T z0 = 0 := by
  refine ⟨⟨fun i => w0.val i - w0.val i,
    cubeFractionalL2Seminorm_sub_lt_top hd (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder w0.val w0.val
      w0.property w0.property⟩, rfl, ?_⟩
  have hae0 : ((⟨fun i => w0.val i - w0.val i,
      cubeFractionalL2Seminorm_sub_lt_top hd (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder w0.val w0.val
        w0.property w0.property⟩ : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder).val 0 :
      SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube
        (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr :
        Set (SpatialCoordinates d))] (fun _ => (0 : ℝ)) := by
    show ((w0.val 0 - w0.val 0 : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr)) : SpatialCoordinates d → ℝ) =ᵐ[_]
        (fun _ => (0 : ℝ))
    rw [sub_self]
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict (centeredCube
      (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr :
      Set (SpatialCoordinates d)))] with x hx
    simpa using hx
  have hmemlp0 : MemLp (fun _ : SpatialCoordinates d => (0 : ℝ)) 2 mu := MemLp.zero'
  rw [hT.2.2 (fun _ => (0 : ℝ)) contDiff_const _ hae0 hmemlp0]
  exact hmemlp0.toLp_zero

/-- Bundles the three per-omega coercivity/interpolation constants (`Ccoer` from `aux_car_
variational_limit_coercive`, `Cbase` from `aux_car_variational_frac_bound`, `Cint` from `Interp.
interpolation_half`) into ONE call, so `aux_car_variational_Ktr_bound`'s own body only needs one
`obtain` instead of four separate large-signature calls (house elaboration-budget rule: this
alone was still enough for `aux_car_variational_Ktr_bound` to breach the 200000-heartbeat ceiling
even after the fractional-exponent algebra and `T 0 = 0` derivation were already extracted). -/
theorem aux_car_variational_Ktr_constants
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (Interp : CubeFractionalInterpolationInput d hd)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHI : InfraredCharacterization M H)
    (Qtri : Homogenization.TriadicCube d) (hr : 0 < Homogenization.cubeScaleFactor Qtri)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr),
      ‖(v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube
          (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) v‖)
    (omega : BilateralField d)
    (G : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) →L[ℝ]
      DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr))
    (hG : ∀ f : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr),
      Tendsto (fun N : ℕ =>
        (responseSolution (killedResponseSpace (Ω := centeredCube
              (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) hP)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
            ((sobolevVolumeLoad f).comp
              (killedResponseSpace (Ω := centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr) hP).space.subtypeL)).val.1)
        atTop (𝓝 (G f)))
    (K1 : ℝ) (hK1 : 0 < K1)
    (hc1 : ∀ (N : ℕ) (v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr)),
      cubeFractionalSqNorm hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr threeQuarterOrder
          (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr)).1 ≤
        K1 * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
            (Homogenization.cubeCenter Qtri) hr)
          (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr))
          (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr))) :
    ∃ Ccoer Cbase Cint : ℝ, 0 < Ccoer ∧ 0 < Cbase ∧ 0 < Cint ∧
      (∀ u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr),
        (limitFormEnergy G u).toENNReal ≠ ⊤ →
        ENNReal.ofReal (‖u‖ ^ 2) ≤ ENNReal.ofReal Ccoer * (limitFormEnergy G u).toENNReal) ∧
      (∀ u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr),
        (limitFormEnergy G u).toENNReal ≠ ⊤ →
        ∃ v3 : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr threeQuarterOrder,
          v3.val 0 = u ∧
          (cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr threeQuarterOrder v3) ^ 2 ≤
            Cbase * (limitFormEnergy G u).toReal) ∧
      (∀ (wHalf : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder)
          (wThree : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr threeQuarterOrder),
        wThree.val 0 = wHalf.val 0 →
        cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder wHalf ≤
          Cint * (‖wHalf.val 0‖ / Real.sqrt (volume.real (centeredCube
              (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr :
              Set (SpatialCoordinates d)))) ^ (1 / 3 : ℝ) *
            cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr threeQuarterOrder wThree ^ (2 / 3 : ℝ)) := by
  obtain ⟨hsym, hpos, _, _⟩ := aux_car_variational_mosco (Homogenization.cubeCenter Qtri)
    (Homogenization.cubeScaleFactor Qtri) hr hP
    (fun N => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
    G hG
  obtain ⟨Ccoer, hCcoer, hcoer⟩ := aux_car_variational_limit_coercive hd Sf M H hHI omega
    (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr hP K1 hK1 hc1 G
    (fun N => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
    (fun _ => rfl) hsym hpos hG
  obtain ⟨Cbase, hCbase, hfrac⟩ := aux_car_variational_frac_bound hd Sf M H omega
    (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr hP K1 hK1 hc1 G
    (fun N => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
    (fun _ => rfl) hsym hpos hG
  obtain ⟨Cint, hCint, hinterp⟩ := Interp.interpolation_half (Homogenization.cubeCenter Qtri)
    (Homogenization.cubeScaleFactor Qtri) hr ⟨3 / 4, by norm_num, by norm_num⟩ rfl
  exact ⟨Ccoer, Cbase, Cint, hCcoer, hCbase, hCint, hcoer, hfrac, hinterp⟩

/-- The "per `(omega, u)`" finish of `Ktr`: given the three bundled constants and the
already-specialized per-`u` facts (`hcoer`, `hfrac`, the generic `hinterp`, `hi`, `hJ`), assembles
the final trace-of-limit-coercivity bound. Extracted into its own declaration (house
elaboration-budget rule): `aux_car_variational_Ktr_bound`'s body was still too large even after
factoring out the fractional-exponent algebra, `T 0 = 0`, and the four-lemma constant bundle. -/
theorem aux_car_variational_Ktr_per_u
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Qtri : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Qtri)
    (G : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) →L[ℝ]
      DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr))
    (Ccoer Cbase Cint : ℝ) (hCcoer : 0 < Ccoer) (hCbase : 0 < Cbase) (hCint : 0 < Cint)
    (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr))
    (hu : (limitFormEnergy G u).toENNReal ≠ ⊤)
    (hcoer : ENNReal.ofReal (‖u‖ ^ 2) ≤ ENNReal.ofReal Ccoer * (limitFormEnergy G u).toENNReal)
    (hfrac : ∃ v3 : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr threeQuarterOrder,
      v3.val 0 = u ∧ (cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr threeQuarterOrder v3) ^ 2 ≤
          Cbase * (limitFormEnergy G u).toReal)
    (hinterp : ∀ (wHalf : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder)
        (wThree : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr threeQuarterOrder),
      wThree.val 0 = wHalf.val 0 →
        cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder wHalf ≤
          Cint * (‖wHalf.val 0‖ / Real.sqrt (volume.real (centeredCube
              (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr :
              Set (SpatialCoordinates d)))) ^ (1 / 3 : ℝ) *
            cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr threeQuarterOrder wThree ^ (2 / 3 : ℝ))
    (i : (u' : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)) →
        (limitFormEnergy G u').toENNReal ≠ ⊤ →
        CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder)
    (hi : (i u hu).val 0 = u)
    (mu : Measure (SpatialCoordinates d)) (K C : ℝ)
    (T : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder → Lp ℝ 2 mu)
    (hT : MeasureTraceCharacterization hd Qtri hr mu K C T) (hKnn : 0 ≤ K) (hCnn : 0 ≤ C)
    (J : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) → SpatialCoordinates d → ℝ)
    (hJ : (J u) =ᵐ[mu] (T (i u hu) : SpatialCoordinates d → ℝ)) :
    (∫⁻ x, ENNReal.ofReal (J u x ^ 2) ∂mu) ≤
      ENNReal.ofReal (C * (K + (mu (closure (Homogenization.openCubeSet Qtri))).toReal) *
        (Cint ^ 2 * (Ccoer / volume.real (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) ^ (1/3:ℝ) *
          Cbase ^ (2/3:ℝ))) * (limitFormEnergy G u).toENNReal := by
  have hvol : 0 < volume.real (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) :=
    SubdiffusiveProcess.centeredCube_volume_pos (Homogenization.cubeCenter Qtri) hr
  obtain ⟨v3, hv3_eq, hv3_bound⟩ := hfrac
  set E := (limitFormEnergy G u).toReal with hEdef
  have hEnn : 0 ≤ E := EReal.toReal_nonneg (limitFormEnergy_nonneg G u)
  have hunorm : ‖u‖ ^ 2 ≤ Ccoer * E := by
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hu) hcoer
    rwa [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hCcoer.le, EReal.toReal_toENNReal (limitFormEnergy_nonneg G u)] at h2
  have hv3norm : (cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr threeQuarterOrder v3) ^ 2 ≤ Cbase * E := hv3_bound
  have hcombine := hinterp (i u hu) v3 (hv3_eq.trans hi.symm)
  rw [hi] at hcombine
  set A := ‖u‖ / Real.sqrt (volume.real (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) with hAdef
  set B := cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
    (Homogenization.cubeScaleFactor Qtri) hr threeQuarterOrder v3 with hBdef
  have hAnn : 0 ≤ A := by rw [hAdef]; positivity
  have hBnn : 0 ≤ B := by rw [hBdef]; unfold cubeFractionalL2Norm; positivity
  have hA2 : A ^ 2 ≤ (Ccoer / volume.real (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) * E := by
    rw [hAdef, div_pow, Real.sq_sqrt hvol.le, div_le_iff₀ hvol, mul_right_comm,
      div_mul_cancel₀ Ccoer hvol.ne']
    exact hunorm
  have hB2 : B ^ 2 ≤ Cbase * E := hv3norm
  have hhalf_nonneg : (0:ℝ) ≤ cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder (i u hu) :=
    by unfold cubeFractionalL2Norm; positivity
  have hsq' : (cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder (i u hu)) ^ 2 ≤
      Cint ^ 2 * (Ccoer / volume.real (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) ^ (1/3:ℝ) *
        Cbase ^ (2/3:ℝ) * E :=
    aux_car_variational_Ktr_real_combine hvol hCcoer.le hCbase hEnn hAnn hBnn hhalf_nonneg hA2 hB2
      hcombine
  obtain ⟨z0, hz0val, hz0T⟩ := aux_car_variational_Ktr_T_zero hd hT (i u hu)
  have hTlip := hT.2.1 (i u hu) z0 (i u hu) (by rw [hz0val]; abel)
  rw [hz0T, sub_zero] at hTlip
  have hnormsq : ‖T (i u hu)‖ ^ 2 ≤
      C * (K + (mu (closure (Homogenization.openCubeSet Qtri))).toReal) *
        (Cint ^ 2 * (Ccoer / volume.real (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) ^ (1/3:ℝ) *
          Cbase ^ (2/3:ℝ) * E) := by
    refine hTlip.trans ?_
    apply mul_le_mul_of_nonneg_left hsq'
    have hKterm : 0 ≤ K + (mu (closure (Homogenization.openCubeSet Qtri))).toReal :=
      add_nonneg hKnn ENNReal.toReal_nonneg
    positivity
  have hlintJ : (∫⁻ x, ENNReal.ofReal (J u x ^ 2) ∂mu) =
      ∫⁻ x, ENNReal.ofReal ((T (i u hu) x) ^ 2) ∂mu := by
    apply lintegral_congr_ae
    filter_upwards [hJ] with x hx
    rw [hx]
  rw [hlintJ, aux_car_variational_Ktr_lintegral_sq_eq_norm_sq]
  have hEeq : (limitFormEnergy G u).toENNReal = ENNReal.ofReal E := by
    rw [hEdef, ← EReal.toReal_toENNReal (limitFormEnergy_nonneg G u), ENNReal.ofReal_toReal hu]
  rw [hEeq, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [hnormsq])

theorem aux_car_variational_Ktr_bound
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (Interp : CubeFractionalInterpolationInput d hd)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHI : InfraredCharacterization M H)
    (Qtri : Homogenization.TriadicCube d) (hr : 0 < Homogenization.cubeScaleFactor Qtri)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr),
      ‖(v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube
          (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) v‖)
    (G : BilateralField d → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) →L[ℝ]
      DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr))
    (hG_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ f : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr),
        Tendsto (fun N : ℕ =>
          (responseSolution (killedResponseSpace (Ω := centeredCube
                (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) hP)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
              ((sobolevVolumeLoad f).comp
                (killedResponseSpace (Ω := centeredCube (Homogenization.cubeCenter Qtri)
                  (Homogenization.cubeScaleFactor Qtri) hr) hP).space.subtypeL)).val.1)
          atTop (𝓝 (G omega f)))
    (hK1_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K1 : ℝ, 0 < K1 ∧
      ∀ (N : ℕ) (v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)),
        cubeFractionalSqNorm hd (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr threeQuarterOrder
            (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr)).1 ≤
          K1 * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
              (Homogenization.cubeCenter Qtri) hr)
            (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr))
            (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr)))
    (muFull : BilateralField d → Measure (SpatialCoordinates d))
    (K C : BilateralField d → ℝ)
    (T : (omega : BilateralField d) → CubeFractionalL2 (k := 1) hd
        (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr
        halfFractionalOrder →
      Lp ℝ 2 ((muFull omega).restrict (closure (centeredCube
        (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr :
        Set (SpatialCoordinates d)))))
    (hKC_nonneg_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, 0 ≤ K omega ∧ 0 ≤ C omega)
    (hT_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasureTraceCharacterization hd Qtri hr
        ((muFull omega).restrict (closure (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))
        (K omega) (C omega) (T omega))
    (i : (omega : BilateralField d) →
        (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr)) →
          (limitFormEnergy (G omega) u).toENNReal ≠ ⊤ →
          CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder)
    (hi_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr))
        (hu : (limitFormEnergy (G omega) u).toENNReal ≠ ⊤), (i omega u hu).val 0 = u)
    (J : (omega : BilateralField d) → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) → SpatialCoordinates d → ℝ)
    (hJ_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr))
        (hu : (limitFormEnergy (G omega) u).toENNReal ≠ ⊤),
        (J omega u) =ᵐ[(muFull omega).restrict (closure (centeredCube
            (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr :
            Set (SpatialCoordinates d)))] (T omega (i omega u hu) : SpatialCoordinates d → ℝ)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ Ktr : ℝ, 0 ≤ Ktr ∧
      ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr))
        (_hu : (limitFormEnergy (G omega) u).toENNReal ≠ ⊤),
        (∫⁻ x, ENNReal.ofReal (J omega u x ^ 2)
            ∂((muFull omega).restrict (closure (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))) ≤
          ENNReal.ofReal Ktr * (limitFormEnergy (G omega) u).toENNReal := by
  filter_upwards [hG_ae, hK1_ae, hKC_nonneg_ae, hT_ae, hi_ae, hJ_ae]
    with omega hG hK1all hKCnn hT hi hJ
  obtain ⟨K1, hK1, hc1⟩ := hK1all
  obtain ⟨hKnn, hCnn⟩ := hKCnn
  obtain ⟨Ccoer, Cbase, Cint, hCcoer, hCbase, hCint, hcoer, hfrac, hinterp⟩ :=
    aux_car_variational_Ktr_constants hd Sf Interp M H hHI Qtri hr hP omega (G omega) hG K1 hK1
      hc1
  refine ⟨C omega * (K omega + ((muFull omega).restrict (closure (centeredCube
      (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr :
      Set (SpatialCoordinates d))) (closure (Homogenization.openCubeSet Qtri))).toReal) *
      (Cint ^ 2 * (Ccoer / volume.real (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) ^ (1/3:ℝ) *
        Cbase ^ (2/3:ℝ)), by positivity, fun u hu => ?_⟩
  exact aux_car_variational_Ktr_per_u hd Qtri hr (G omega) Ccoer Cbase Cint hCcoer hCbase hCint u
    hu (hcoer u hu) (hfrac u hu) hinterp (i omega) (hi u hu)
    ((muFull omega).restrict (closure (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))
    (K omega) (C omega) (T omega) hT hKnn hCnn (J omega) (hJ u hu)
theorem aux_car_variational_hVariational_full
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHI : InfraredCharacterization M H)
    (Qtri : Homogenization.TriadicCube d) (hr : 0 < Homogenization.cubeScaleFactor Qtri)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr),
      ‖(v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube
          (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) v‖)
    (G : BilateralField d → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) →L[ℝ]
      DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr))
    (hG_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ f : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr),
        Tendsto (fun N : ℕ =>
          (responseSolution (killedResponseSpace (Ω := centeredCube
                (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) hP)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
              ((sobolevVolumeLoad f).comp
                (killedResponseSpace (Ω := centeredCube (Homogenization.cubeCenter Qtri)
                  (Homogenization.cubeScaleFactor Qtri) hr) hP).space.subtypeL)).val.1)
          atTop (𝓝 (G omega f)))
    (hK1_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K1 : ℝ, 0 < K1 ∧
      ∀ (N : ℕ) (v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)),
        cubeFractionalSqNorm hd (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr threeQuarterOrder
            (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr)).1 ≤
          K1 * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
              (Homogenization.cubeCenter Qtri) hr)
            (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr))
            (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr)))
    (muFull : BilateralField d → Measure (SpatialCoordinates d))
    (hmufin_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      muFull omega (closure (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) < ⊤)
    (K C : BilateralField d → ℝ)
    (T : (omega : BilateralField d) → CubeFractionalL2 (k := 1) hd
        (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr
        halfFractionalOrder →
      Lp ℝ 2 ((muFull omega).restrict (closure (centeredCube
        (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr :
        Set (SpatialCoordinates d)))))
    (hT_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasureTraceCharacterization hd Qtri hr
        ((muFull omega).restrict (closure (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))
        (K omega) (C omega) (T omega))
    (i : (omega : BilateralField d) →
        (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr)) →
          (limitFormEnergy (G omega) u).toENNReal ≠ ⊤ →
          CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder)
    (hi_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr))
        (hu : (limitFormEnergy (G omega) u).toENNReal ≠ ⊤), (i omega u hu).val 0 = u)
    (J : (omega : BilateralField d) → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) → SpatialCoordinates d → ℝ)
    (hJ_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr))
        (hu : (limitFormEnergy (G omega) u).toENNReal ≠ ⊤),
        (J omega u) =ᵐ[(muFull omega).restrict (closure (centeredCube
            (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr :
            Set (SpatialCoordinates d)))] (T omega (i omega u hu) : SpatialCoordinates d → ℝ))
    (hKtr_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ Ktr : ℝ, 0 ≤ Ktr ∧
      ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr))
        (_hu : (limitFormEnergy (G omega) u).toENNReal ≠ ⊤),
        (∫⁻ x, ENNReal.ofReal (J omega u x ^ 2)
            ∂((muFull omega).restrict (closure (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))) ≤
          ENNReal.ofReal Ktr * (limitFormEnergy (G omega) u).toENNReal) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∃ ustar : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr),
            (limitFormEnergy (G omega) ustar).toENNReal ≠ ⊤ ∧
            (∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr),
              (limitFormEnergy (G omega) w).toENNReal ≠ ⊤ →
              (limitFormEnergy (G omega) ustar).toENNReal.toReal +
                  lam * (∫ x, J omega ustar x ^ 2 ∂((muFull omega).restrict (closure
                    (centeredCube (Homogenization.cubeCenter Qtri)
                      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))) -
                2 * ∫ x, f x * J omega ustar x ∂((muFull omega).restrict (closure
                    (centeredCube (Homogenization.cubeCenter Qtri)
                      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))) ≤
              (limitFormEnergy (G omega) w).toENNReal.toReal +
                  lam * (∫ x, J omega w x ^ 2 ∂((muFull omega).restrict (closure
                    (centeredCube (Homogenization.cubeCenter Qtri)
                      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))) -
                2 * ∫ x, f x * J omega w x ∂((muFull omega).restrict (closure
                    (centeredCube (Homogenization.cubeCenter Qtri)
                      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))) ∧
            (∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr),
              (limitFormEnergy (G omega) w).toENNReal ≠ ⊤ →
              (∀ v : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
                  (Homogenization.cubeScaleFactor Qtri) hr),
                (limitFormEnergy (G omega) v).toENNReal ≠ ⊤ →
                (limitFormEnergy (G omega) w).toENNReal.toReal +
                    lam * (∫ x, J omega w x ^ 2 ∂((muFull omega).restrict (closure
                      (centeredCube (Homogenization.cubeCenter Qtri)
                        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))) -
                  2 * ∫ x, f x * J omega w x ∂((muFull omega).restrict (closure
                      (centeredCube (Homogenization.cubeCenter Qtri)
                        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))) ≤
                (limitFormEnergy (G omega) v).toENNReal.toReal +
                    lam * (∫ x, J omega v x ^ 2 ∂((muFull omega).restrict (closure
                      (centeredCube (Homogenization.cubeCenter Qtri)
                        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))) -
                  2 * ∫ x, f x * J omega v x ∂((muFull omega).restrict (closure
                      (centeredCube (Homogenization.cubeCenter Qtri)
                        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))) →
              w = ustar) := by
  filter_upwards [hG_ae, hK1_ae, hmufin_ae, hT_ae, hi_ae, hJ_ae, hKtr_ae]
    with omega hG hK1all hmufin hT hi hJ hKtrall
  intro lam hlam f
  obtain ⟨K1, hK1, hc1⟩ := hK1all
  obtain ⟨Ktr, hKtr, hJtr⟩ := hKtrall
  have hmufin' : ((muFull omega).restrict (closure (centeredCube
      (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr :
      Set (SpatialCoordinates d)))) Set.univ < ⊤ := by
    rw [Measure.restrict_apply_univ]; exact hmufin
  exact aux_car_variational_variational_step hd Sf M H hHI omega Qtri hr hP (G omega) hG K1 hK1
    hc1 ((muFull omega).restrict (closure (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))
    (muFull omega) rfl hmufin' (K omega) (C omega) (T omega) hT (i omega) hi (J omega) hJ
    Ktr hKtr hJtr lam hlam f

/-- Pointwise: `(f - λR)R ≤ f²/(4λ)` for `λ > 0` (completing the square, no bound on `R` needed). -/
theorem aux_car_variational_weak_ident_energy_pointwise (lam : ℝ) (hlam : 0 < lam) (fx Rx : ℝ) :
    (fx - lam * Rx) * Rx ≤ fx ^ 2 / (4 * lam) := by
  rw [le_div_iff₀ (by positivity : (0:ℝ) < 4 * lam)]
  nlinarith [sq_nonneg (fx - 2 * lam * Rx)]

/-- Bounds `coeffform(u,u) ≤ ‖f‖²·mass/λ` from the weak equation `coeffform(u,w)=∫(f-λR)w`,
`u.val0=ᵃᵉR`, and boundedness of `R`. Pure completing-the-square + a Cauchy-Schwarz-free
integral bound; kept measure-generic so it applies verbatim to either `cutoffSpeedMeasure`
or its closure-restriction. -/
theorem aux_car_variational_weak_ident_energy_bound {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (muN : Measure (SpatialCoordinates d))
    (a : PositiveCoefficient (centeredCube z r hr))
    (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (R : SpatialCoordinates d → ℝ)
    (u : killedSobolevGraph (centeredCube z r hr))
    (hmass : muN (centeredCube z r hr : Set (SpatialCoordinates d)) < ⊤)
    (hRmeas : AEStronglyMeasurable R
      (muN.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hRbound : ∀ᵐ x ∂(muN.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
      |R x| ≤ ‖f‖ / lam)
    (hueq : (u : SobolevData (centeredCube z r hr)).1
        =ᵐ[muN.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] R)
    (hw : sobolevCoefficientForm a (u : SobolevData (centeredCube z r hr))
        (u : SobolevData (centeredCube z r hr)) =
      ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        (f x - lam * R x) * (u : SobolevData (centeredCube z r hr)).1 x ∂muN) :
    sobolevCoefficientForm a (u : SobolevData (centeredCube z r hr))
        (u : SobolevData (centeredCube z r hr)) ≤
      ‖f‖ ^ 2 * (muN (centeredCube z r hr : Set (SpatialCoordinates d))).toReal / lam := by
  have hfin : IsFiniteMeasure
      (muN.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    ⟨by rwa [Measure.restrict_apply_univ]⟩
  set Q : Set (SpatialCoordinates d) := (centeredCube z r hr : Set (SpatialCoordinates d)) with hQdef
  have hstep1 : sobolevCoefficientForm a (u : SobolevData (centeredCube z r hr))
      (u : SobolevData (centeredCube z r hr)) =
      ∫ x in Q, (f x - lam * R x) * R x ∂muN := by
    rw [hw]
    exact integral_congr_ae (Filter.EventuallyEq.rfl.mul hueq)
  have hRintegrable : Integrable R (muN.restrict Q) :=
    (MemLp.of_bound (p := 1) hRmeas (‖f‖ / lam) hRbound).integrable le_rfl
  have hfmeas : AEStronglyMeasurable f (muN.restrict Q) :=
    f.continuous.aestronglyMeasurable.mono_ac (Measure.absolutelyContinuous_of_le
      Measure.restrict_le_self) |>.mono_measure le_rfl
  have hLHSmeas : AEStronglyMeasurable (fun x => (f x - lam * R x) * R x) (muN.restrict Q) :=
    ((hfmeas.sub (hRmeas.const_mul lam)).mul hRmeas)
  have hfx0 : ∀ x, |f x| ≤ ‖f‖ := fun x => by
    have := f.norm_coe_le_norm x; rwa [Real.norm_eq_abs] at this
  have hfsq : ∀ x, (f x) ^ 2 ≤ ‖f‖ ^ 2 := fun x => by
    rw [← sq_abs (f x)]; exact pow_le_pow_left₀ (abs_nonneg _) (hfx0 x) 2
  have hLHSbound : ∀ᵐ x ∂(muN.restrict Q), ‖(f x - lam * R x) * R x‖ ≤ 2 * ‖f‖ ^ 2 / lam := by
    filter_upwards [hRbound] with x hx
    have hfx : |f x| ≤ ‖f‖ := hfx0 x
    have hxle := abs_le.mp hx
    have hfxle := abs_le.mp hfx
    have hcancel1 : lam * (‖f‖ / lam) = ‖f‖ := by field_simp
    have hcancel2 : lam * (-(‖f‖ / lam)) = -‖f‖ := by rw [mul_neg, hcancel1]
    have h1 : |f x - lam * R x| ≤ 2 * ‖f‖ := by
      rw [abs_le]
      constructor
      · nlinarith [hfxle.1, mul_le_mul_of_nonneg_left hxle.2 hlam.le, hcancel1]
      · nlinarith [hfxle.2, mul_le_mul_of_nonneg_left hxle.1 hlam.le, hcancel2]
    calc ‖(f x - lam * R x) * R x‖ = |f x - lam * R x| * |R x| := by
          rw [Real.norm_eq_abs, abs_mul]
      _ ≤ (2 * ‖f‖) * (‖f‖ / lam) := mul_le_mul h1 hx (abs_nonneg _) (by positivity)
      _ = 2 * ‖f‖ ^ 2 / lam := by ring
  have hLHSintegrable : Integrable (fun x => (f x - lam * R x) * R x) (muN.restrict Q) :=
    (MemLp.of_bound (p := 1) hLHSmeas (2 * ‖f‖ ^ 2 / lam) hLHSbound).integrable le_rfl
  have hRHSintegrable : Integrable (fun x => (f x) ^ 2 / (4 * lam)) (muN.restrict Q) := by
    have hmeas2 : AEStronglyMeasurable (fun x => (f x) ^ 2 / (4 * lam)) (muN.restrict Q) := by
      have h1 : AEStronglyMeasurable (fun x => f x * f x) (muN.restrict Q) := hfmeas.mul hfmeas
      have h2 := h1.mul (aestronglyMeasurable_const :
        AEStronglyMeasurable (fun _ : SpatialCoordinates d => (4 * lam)⁻¹) (muN.restrict Q))
      simpa [sq, div_eq_mul_inv, Pi.mul_apply] using! h2
    have hbound2 : ∀ᵐ x ∂(muN.restrict Q), ‖(f x) ^ 2 / (4 * lam)‖ ≤ ‖f‖ ^ 2 / (4 * lam) := by
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0:ℝ) < 4 * lam),
        abs_of_nonneg (sq_nonneg (f x))]
      exact div_le_div_of_nonneg_right (hfsq x) (by positivity)
    exact (MemLp.of_bound (p := 1) hmeas2 (‖f‖ ^ 2 / (4 * lam)) hbound2).integrable le_rfl
  have hstep2 : (∫ x in Q, (f x - lam * R x) * R x ∂muN) ≤
      ∫ x in Q, (f x) ^ 2 / (4 * lam) ∂muN :=
    integral_mono hLHSintegrable hRHSintegrable
      (fun x => aux_car_variational_weak_ident_energy_pointwise lam hlam (f x) (R x))
  have hstep3 : (∫ x in Q, (f x) ^ 2 / (4 * lam) ∂muN) ≤ ‖f‖ ^ 2 * (muN Q).toReal / (4 * lam) := by
    have hbound3 : (fun x : SpatialCoordinates d => (f x) ^ 2 / (4 * lam)) ≤ᵐ[muN.restrict Q]
        (fun _ => ‖f‖ ^ 2 / (4 * lam)) := by
      filter_upwards with x
      exact div_le_div_of_nonneg_right (hfsq x) (by positivity)
    calc (∫ x in Q, (f x) ^ 2 / (4 * lam) ∂muN) ≤ ∫ _x in Q, ‖f‖ ^ 2 / (4 * lam) ∂muN :=
          integral_mono_ae hRHSintegrable (integrable_const _) hbound3
      _ = ‖f‖ ^ 2 / (4 * lam) * (muN.restrict Q Set.univ).toReal := by
          rw [integral_const, Measure.real_def, smul_eq_mul, mul_comm]
      _ = ‖f‖ ^ 2 * (muN Q).toReal / (4 * lam) := by
          rw [Measure.restrict_apply_univ]; ring
  calc sobolevCoefficientForm a (u : SobolevData (centeredCube z r hr))
        (u : SobolevData (centeredCube z r hr))
      = ∫ x in Q, (f x - lam * R x) * R x ∂muN := hstep1
    _ ≤ ∫ x in Q, (f x) ^ 2 / (4 * lam) ∂muN := hstep2
    _ ≤ ‖f‖ ^ 2 * (muN Q).toReal / (4 * lam) := hstep3
    _ ≤ ‖f‖ ^ 2 * (muN Q).toReal / lam := by
        apply div_le_div_of_nonneg_left (by positivity) hlam (by linarith)

/-- A finite-cutoff speed measure gives zero mass to any cube's frontier: `cutoffSpeedMeasure` is
`volume.withDensity(...)`, and a cube (a metric ball, hence convex) has Lebesgue-null frontier
(`Convex.addHaar_frontier`) — integrating any density over a null set gives `0`. Unconditional,
no growth-bound machinery needed (unlike the analogous fact for the *limit* measure `muFull`,
which is not automatically absolutely continuous w.r.t. Lebesgue). -/
theorem aux_car_variational_cutoffSpeedMeasure_frontier_null {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    cutoffSpeedMeasure M H omega N
      (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) = 0 := by
  have hball : (centeredCube z r hr : Set (SpatialCoordinates d)) = Metric.ball z (r / 2) := rfl
  have hconv : Convex ℝ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    rw [hball]; exact convex_ball z (r / 2)
  have hvol : volume (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) = 0 :=
    Convex.addHaar_frontier volume hconv
  have hrestrict0 : volume.restrict
      (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) = 0 :=
    Measure.restrict_eq_zero.mpr hvol
  show volume.withDensity (ENNReal.ofReal ∘ cutoffSpeedDensity M H omega N)
    (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) = 0
  rw [withDensity_apply _ isClosed_frontier.measurableSet]
  simp only [Function.comp_apply]
  rw [hrestrict0, lintegral_zero_measure]

/-- Given the RAW `aux_car_variational_weak_ident` output (`u`, `hu1 : u.val0 =ᵃᵉ[volume.restrict
Q] R`, `hu2` : the weak equation w.r.t. raw `cutoffSpeedMeasure`) and the sup bound `hsup` (from
`aux_car_variational_RN_bound`), reshapes onto `(cutoffSpeedMeasure).restrict (closure Q)` (the
measure convention `aux_prop_uniform_resolvent_ident_sample`'s `hfinite` uses) and supplies the
energy bound, matching `hfinite`'s full 4-conjunct shape exactly. -/
theorem aux_car_variational_hfinite_of_weak_ident
    {d : ℕ} (_hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (R : SpatialCoordinates d → ℝ)
    (u : killedSobolevGraph (centeredCube z r hr))
    (hu1 : ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] R)
    (hu2 : ∀ w : killedSobolevGraph (centeredCube z r hr),
      sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
        (u : SobolevData (centeredCube z r hr)) (w : SobolevData (centeredCube z r hr)) =
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), (f x - lam * R x) *
          (w : SobolevData (centeredCube z r hr)).1 x ∂(cutoffSpeedMeasure M H omega N))
    (hsup : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), |R x| ≤ ‖f‖ / lam) :
    R =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) ∧
    (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), |R x| ≤ ‖f‖ / lam) ∧
    (∀ w : killedSobolevGraph (centeredCube z r hr),
      sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
        (u : SobolevData (centeredCube z r hr)) (w : SobolevData (centeredCube z r hr)) =
        ∫ x, (f x - lam * R x) * (w : SobolevData (centeredCube z r hr)).1 x
          ∂((cutoffSpeedMeasure M H omega N).restrict
            (closure (centeredCube z r hr : Set (SpatialCoordinates d))))) ∧
    sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
      (u : SobolevData (centeredCube z r hr)) (u : SobolevData (centeredCube z r hr)) ≤
      ‖f‖ ^ 2 * (((cutoffSpeedMeasure M H omega N).restrict
        (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal / lam := by
  set Q : Set (SpatialCoordinates d) := (centeredCube z r hr : Set (SpatialCoordinates d))
    with hQdef
  have hQopen : IsOpen Q := (centeredCube z r hr).isOpen
  have hfrontier : cutoffSpeedMeasure M H omega N (frontier Q) = 0 :=
    aux_car_variational_cutoffSpeedMeasure_frontier_null M H omega N z r hr
  have hQeq : Q =ᵐ[cutoffSpeedMeasure M H omega N] (closure Q) := by
    rw [ae_eq_set]
    refine ⟨?_, ?_⟩
    · rw [Set.sdiff_eq_empty.mpr subset_closure]; exact measure_empty
    · rw [← hQopen.frontier_eq]; exact hfrontier
  have hrestricteq : (cutoffSpeedMeasure M H omega N).restrict Q =
      (cutoffSpeedMeasure M H omega N).restrict (closure Q) :=
    Measure.restrict_congr_set hQeq
  have hu2' : ∀ w : killedSobolevGraph (centeredCube z r hr),
      sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
        (u : SobolevData (centeredCube z r hr)) (w : SobolevData (centeredCube z r hr)) =
        ∫ x, (f x - lam * R x) * (w : SobolevData (centeredCube z r hr)).1 x
          ∂((cutoffSpeedMeasure M H omega N).restrict (closure Q)) := by
    intro w
    rw [hu2 w, ← hrestricteq]
  refine ⟨hu1.symm, hsup, hu2', ?_⟩
  set muN : Measure (SpatialCoordinates d) :=
    (cutoffSpeedMeasure M H omega N).restrict (closure Q) with hmuNdef
  have hρc := aux_torsion_bound_density_continuous M H omega N
  obtain ⟨Cρ, hCρ0, hCρ⟩ := aux_torsion_bound_cube_bound (cutoffSpeedDensity M H omega N) hρc z hr
  have hmassQ : cutoffSpeedMeasure M H omega N Q < ⊤ := by
    rw [show cutoffSpeedMeasure M H omega N =
      volume.withDensity (ENNReal.ofReal ∘ cutoffSpeedDensity M H omega N) from rfl,
      withDensity_apply _ hQopen.measurableSet]
    calc (∫⁻ x in Q, ENNReal.ofReal (cutoffSpeedDensity M H omega N x)) ≤
        ∫⁻ _x in Q, ENNReal.ofReal Cρ :=
          setLIntegral_mono' hQopen.measurableSet
            (fun x hx => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hCρ x hx)))
      _ = ENNReal.ofReal Cρ * volume Q := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (centeredCube_isBounded z hr).measure_lt_top
  have hmuNQ2 : muN.restrict Q = muN :=
    (Measure.restrict_restrict_of_subset subset_closure).trans hrestricteq
  have hmassQ' : muN Q < ⊤ := by
    rw [hmuNdef, Measure.restrict_apply hQopen.measurableSet,
      Set.inter_eq_self_of_subset_left subset_closure]
    exact hmassQ
  have hac : (cutoffSpeedMeasure M H omega N).restrict Q ≪ volume.restrict Q :=
    (withDensity_absolutelyContinuous volume _).restrict Q
  have hmuNac : muN ≪ volume.restrict Q := hrestricteq ▸ hac
  have hu0meas : AEStronglyMeasurable
      ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      (volume.restrict Q) :=
    Lp.aestronglyMeasurable (u : SobolevData (centeredCube z r hr)).1
  have hRmeas : AEStronglyMeasurable R (muN.restrict Q) := by
    rw [hmuNQ2]
    exact (hu0meas.mono_ac hmuNac).congr (hmuNac.ae_eq hu1)
  have hRbound' : ∀ᵐ x ∂(muN.restrict Q), |R x| ≤ ‖f‖ / lam := by
    rw [hmuNQ2]
    exact hmuNac.ae_le (ae_restrict_of_forall_mem hQopen.measurableSet hsup)
  have hueq' : ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[muN.restrict Q] R := by
    rw [hmuNQ2]; exact hmuNac.ae_eq hu1
  have hw' : sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
      (u : SobolevData (centeredCube z r hr)) (u : SobolevData (centeredCube z r hr)) =
      ∫ x in Q, (f x - lam * R x) *
        (u : SobolevData (centeredCube z r hr)).1 x ∂muN := by
    show sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
      (u : SobolevData (centeredCube z r hr)) (u : SobolevData (centeredCube z r hr)) =
      ∫ x, (f x - lam * R x) *
        (u : SobolevData (centeredCube z r hr)).1 x ∂(muN.restrict Q)
    rw [hmuNQ2]
    exact hu2' u
  exact aux_car_variational_weak_ident_energy_bound z r hr muN
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr) lam hlam f R u
    hmassQ' hRmeas hRbound' hueq' hw'

/-- The `hidentify` criterion (car_variational's `hUniform`/final identification, at one fixed
`omega, lam, f`): any continuous uniform-on-`closure Q`-limit `g` of a subsequence of the actual
finite-cutoff resolvents `RN` equals `ustar`'s class a.e. on `Q`. Pure assembly of `aux_prop_
uniform_resolvent_ident_sample` (already proved) — `u`/`hfinite` (the per-`N` weak-solution
package, `aux_car_variational_hfinite_of_weak_ident` above) and `hmosco` (the frozen classical
`inputs_classical_mosco_liminf`) are taken as GIVEN inputs, not derived here, to keep this
declaration's own elaboration small (house rule). `Kc` is the CONSTANT `K1` (car_variational's
own fractional coercivity bound is already uniform in `N`), so `hbd` is trivial. -/
theorem aux_car_variational_hidentify_at_omega
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (epsilon : ℝ) (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (Qtri : Homogenization.TriadicCube d)
    (hr : 0 < Homogenization.cubeScaleFactor Qtri)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (Region : Set (SpatialCoordinates d))
    (hNeighborhood : ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
      Metric.ball x 1 ⊆ Region)
    (muFull : Measure (SpatialCoordinates d))
    (hmu : MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) muFull ∧
      muFull (frontier ((centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) = 0 ∧
      muFull (closure ((centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))) < ∞)
    (Kmu : ℝ) (hKmu : 0 ≤ Kmu)
    (hgrowth : ∀ x ∈ Region, ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
      muFull (Metric.ball x rr) ≤ ENNReal.ofReal (Kmu * rr ^ ((d : ℝ) - epsilon)) ∧
        ∀ N, cutoffSpeedMeasure M H omega N (Metric.ball x rr) ≤
          ENNReal.ofReal (Kmu * rr ^ ((d : ℝ) - epsilon)))
    (Elim : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) → ℝ≥0∞)
    (hmosco : _root_.SubdiffusiveProcess.ResponseMoments.MoscoLiminf (fun N u => ⨅ v : {v : killedSobolevGraph (centeredCube
          (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) //
        (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)).1 = u},
        ENNReal.ofReal (sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
          (v.val : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr))
          (v.val : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr)))) Elim ∧
      _root_.SubdiffusiveProcess.ResponseMoments.MoscoRecovery (fun N u => ⨅ v : {v : killedSobolevGraph (centeredCube
          (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) //
        (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)).1 = u},
        ENNReal.ofReal (sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
          (v.val : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr))
          (v.val : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr)))) Elim)
    (T : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder →
      Lp ℝ 2 (muFull.restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))))
    (Ktrace Ctrace : ℝ)
    (hT : 0 ≤ Ktrace ∧ 0 ≤ Ctrace ∧
      MeasureTraceCharacterization hd Qtri hr (muFull.restrict (closure
        ((centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))) Ktrace Ctrace T)
    (i : (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)) → Elim u ≠ ∞ →
      CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder)
    (hival : ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)) (hu : Elim u ≠ ∞), (i u hu).val 0 = u)
    (J : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) → SpatialCoordinates d → ℝ)
    (hJ : ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)) (hu : Elim u ≠ ∞),
      (J u) =ᵐ[muFull.restrict (closure ((centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))]
        (T (i u hu) : SpatialCoordinates d → ℝ))
    (lam : ℝ) (hlam : 0 < lam) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (ustar : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr))
    (hmin : Elim ustar ≠ ∞ ∧
      (∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr), Elim w ≠ ∞ →
        (Elim ustar).toReal + lam * (∫ x, (J ustar x) ^ 2 ∂(muFull.restrict (closure
            ((centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))))) -
          2 * (∫ x, f x * J ustar x ∂(muFull.restrict (closure
            ((centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))))) ≤
        (Elim w).toReal + lam * (∫ x, (J w x) ^ 2 ∂(muFull.restrict (closure
            ((centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))))) -
          2 * (∫ x, f x * J w x ∂(muFull.restrict (closure
            ((centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))))) ∧
      (∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr), Elim w ≠ ∞ →
        (∀ v : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr), Elim v ≠ ∞ →
          (Elim w).toReal + lam * (∫ x, (J w x) ^ 2 ∂(muFull.restrict (closure
              ((centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))))) -
            2 * (∫ x, f x * J w x ∂(muFull.restrict (closure
              ((centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))))) ≤
            (Elim v).toReal + lam * (∫ x, (J v x) ^ 2 ∂(muFull.restrict (closure
              ((centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))))) -
              2 * (∫ x, f x * J v x ∂(muFull.restrict (closure
              ((centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))))) →
        w = ustar))
    (u : ℕ → killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr))
    (R : ℕ → SpatialCoordinates d → ℝ)
    (hfinite : ∀ N : ℕ,
      (R N =ᵐ[volume.restrict ((centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))]
        ((u N : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)).1 : SpatialCoordinates d → ℝ)) ∧
      (∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr),
        sobolevCoefficientForm
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
            (u N : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr))
            (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr)) =
          ∫ x, (f x - lam * R N x) * (w : SobolevData (centeredCube
              (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)).1 x
            ∂((cutoffSpeedMeasure M H omega N).restrict (closure
              ((centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))))) ∧
      sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
          (u N : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr))
          (u N : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr)) ≤
        ‖f‖ ^ 2 * ((cutoffSpeedMeasure M H omega N).restrict (closure
            ((centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))
          ((centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))).toReal / lam)
    (K1 : ℝ) (_hK1 : 0 < K1)
    (hc1 : ∀ N (v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr)),
      ∃ v3 : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
        v3.val 0 = (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)).1 ∧
        (cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3) ^ 2 ≤
          K1 * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
              (Homogenization.cubeCenter Qtri) hr)
            (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr))
            (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr)))
    (SInterp : CubeFractionalInterpolationInput d hd)
    (g : C(SpatialCoordinates d, ℝ)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (hunif : ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
      ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
        |R (σ k) x - g x| < eps) :
    (g : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict ((centeredCube
      (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) :
      Set (SpatialCoordinates d))] (ustar : SpatialCoordinates d → ℝ) :=
  aux_prop_uniform_resolvent_ident_sample hd epsilon hepsilon' Qtri hr M H omega Region
    hNeighborhood muFull hmu Kmu hKmu hgrowth Elim hmosco T Ktrace Ctrace hT i hival J hJ
    lam hlam f ustar hmin u R hfinite (fun _ => K1) hc1 SInterp g K1 σ hσ (fun _ => le_refl K1)
    hunif

/-- The final assembly: given the Hölder-equicontinuous/bounded/zero-on-frontier package for
`R` (from `aux_car_variational_holder_all`/`aux_car_variational_RN_bound`/`aux_car_variational_
RN_zero_outside`, already built in the `car_variational` WIP) and an ABSTRACT `hidentify`-shaped
criterion (kept abstract here — at the real integration site it is `aux_car_variational_
hidentify_at_omega`, partially applied; kept a black-box hypothesis in this test so the giant
binder telescope above is not duplicated a second time), produces the full uniform-convergence +
identification conclusion used for both `hUniform` and the limiting identification. -/
theorem aux_car_variational_full_convergence_of_hidentify {d : ℕ}
    (Q : Set (SpatialCoordinates d)) (hQopen : IsOpen Q) (hQne : Q.Nonempty)
    (hQbdd : Bornology.IsBounded Q)
    (R : ℕ → SpatialCoordinates d → ℝ) (ustar : SpatialCoordinates d → ℝ)
    (hcont : ∀ N, ContinuousOn (R N) (closure Q))
    (hzero : ∀ N, ∀ x ∈ frontier (closure Q), R N x = 0)
    (Kom : ℝ) (hKom : 0 ≤ Kom)
    (hbound : ∀ N, ∀ x ∈ closure Q, |R N x| ≤ Kom)
    (hHolderR : ∀ N, ∀ x ∈ closure Q, ∀ y ∈ closure Q,
      |R N x - R N y| ≤ Kom * dist x y ^ (1 / 4 : ℝ))
    (hidentify : ∀ g : C(SpatialCoordinates d, ℝ),
      (∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
          ∀ x ∈ closure Q, |R (σ k) x - g x| < eps) →
      (g : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict Q] ustar) :
    ∃ g : SpatialCoordinates d → ℝ, ContinuousOn g (closure Q) ∧
      (∀ x ∈ frontier (closure Q), g x = 0) ∧
      (∀ x ∈ closure Q, Filter.limsup (fun N => R N x) atTop = g x) ∧
      (∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k → ∀ x ∈ closure Q, |R k x - g x| < eps) ∧
      (∀ x ∈ closure Q, ∀ y ∈ closure Q, |g x - g y| ≤ Kom * dist x y ^ (1 / 4 : ℝ)) ∧
      g =ᵐ[volume.restrict Q] ustar := by
  have hKc : IsCompact (closure Q) := hQbdd.isCompact_closure
  classical
  refine aux_prop_uniform_resolvent_subsequence_bridge_full_limit_identification
    (closure Q) Q hKc hQopen hQne rfl R ustar hcont hzero ⟨Kom, hbound⟩ Kom hKom hHolderR ?_
  intro g0 hg0cont hex
  obtain ⟨σ, hσ, hunif⟩ := hex
  have hg0zero : ∀ x ∈ frontier (closure Q), g0 x = 0 := by
    intro x hx
    have hxK : x ∈ closure Q := by
      have := frontier_subset_closure hx; rwa [closure_closure] at this
    have htendsto : Filter.Tendsto (fun k => R (σ k) x) Filter.atTop (nhds (g0 x)) := by
      rw [Metric.tendsto_atTop]
      intro eps heps
      obtain ⟨k0, hk0⟩ := hunif eps heps
      exact ⟨k0, fun k hk => by rw [Real.dist_eq]; exact hk0 k hk x hxK⟩
    have hzeroSeq : (fun k => R (σ k) x) = fun _ => (0 : ℝ) := by
      funext k
      exact hzero (σ k) x hx
    rw [hzeroSeq] at htendsto
    exact tendsto_nhds_unique htendsto tendsto_const_nhds
  have hg0cont' : Continuous (fun x => if x ∈ closure Q then g0 x else 0) :=
    aux_prop_uniform_resolvent_subsequence_bridge_zero_extend_continuous (closure Q) g0
      isClosed_closure hg0cont hg0zero
  set g0b : C(SpatialCoordinates d, ℝ) := ⟨_, hg0cont'⟩ with hg0bdef
  have hg0beq : ∀ x ∈ closure Q, g0b x = g0 x := fun x hx => by
    change (if x ∈ closure Q then g0 x else 0) = g0 x
    rw [ite_eq_left hx]
  have hunif' : ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
      ∀ x ∈ closure Q, |R (σ k) x - g0b x| < eps := by
    intro eps heps
    obtain ⟨k0, hk0⟩ := hunif eps heps
    exact ⟨k0, fun k hk x hx => by rw [hg0beq x hx]; exact hk0 k hk x hx⟩
  have hfin := hidentify g0b ⟨σ, hσ, hunif'⟩
  have hQmem : ∀ᵐ x ∂(volume.restrict Q), x ∈ Q := ae_restrict_mem hQopen.measurableSet
  filter_upwards [hfin, hQmem] with x hx hxQ
  rw [← hg0beq x (subset_closure hxQ)]
  exact hx

-- Combines `aux_car_variational_variational_step` (existence/minimality/uniqueness of the
-- abstract minimizer `ustar`) with the Arzelà–Ascoli/`aux_prop_uniform_resolvent_ident_sample`
-- identification chain (`aux_car_variational_hidentify_at_omega` +
-- `aux_car_variational_full_convergence_of_hidentify`), at one fixed `omega` (a.e.). This is the
-- One application supplies uniform convergence and identification in
-- own `hFixedCube` (house elaboration-budget rule: kept as its own top-level declaration with a
-- small per-omega proof, matching `aux_car_variational_hVariational_full`'s own precedent).
theorem aux_car_variational_hcoer3_of_hc1 {d : ℕ} (hd : 2 ≤ d)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr)) (K1 : ℝ) (_hK1 : 0 ≤ K1)
    (v : killedSobolevGraph (centeredCube z r hr))
    (hc1v : cubeFractionalSqNorm hd z r hr threeQuarterOrder
        (v : SobolevData (centeredCube z r hr)).1 ≤
      K1 * sobolevCoefficientForm a (v : SobolevData (centeredCube z r hr))
        (v : SobolevData (centeredCube z r hr))) :
    ∃ v3 : CubeFractionalL2 (k := 1) hd z r hr threeQuarterOrder,
      v3.val 0 = (v : SobolevData (centeredCube z r hr)).1 ∧
      (cubeFractionalL2Norm hd z r hr threeQuarterOrder v3) ^ 2 ≤
        (1 + r ^ (-(3 / 2 : ℝ))) *
          (K1 * sobolevCoefficientForm a (v : SobolevData (centeredCube z r hr))
            (v : SobolevData (centeredCube z r hr))) := by
  have hfin : cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
      (fun _ : Fin 1 => (v : SobolevData (centeredCube z r hr)).1) < ⊤ :=
    Sf.h1_fractional_finite z r hr ⟨v.val, killedSobolevGraph_le_weakSobolevGraph v.property⟩
  refine ⟨⟨fun _ => (v : SobolevData (centeredCube z r hr)).1, hfin⟩, rfl, ?_⟩
  set A : ℝ := (cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
    (fun _ : Fin 1 => (v : SobolevData (centeredCube z r hr)).1)).toReal with hAdef
  set B : ℝ := ‖(v : SobolevData (centeredCube z r hr)).1‖ /
    Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) with hBdef
  have hAnn : 0 ≤ A := ENNReal.toReal_nonneg
  have hBnn : 0 ≤ B := div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hthreeq : (threeQuarterOrder : ℝ) = 3 / 4 := rfl
  have hL2eq : cubeFractionalL2Norm hd z r hr threeQuarterOrder
      ⟨fun _ => (v : SobolevData (centeredCube z r hr)).1, hfin⟩ = A + r ^ (-(3 / 4 : ℝ)) * B := by
    show (cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
        (fun _ : Fin 1 => (v : SobolevData (centeredCube z r hr)).1)).toReal +
      r ^ (-(threeQuarterOrder : ℝ)) *
        (Real.sqrt (∑ _i : Fin 1, ‖(v : SobolevData (centeredCube z r hr)).1‖ ^ 2) /
          Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) = _
    rw [hthreeq, hAdef, hBdef]
    congr 2
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul,
      Real.sqrt_sq (norm_nonneg _)]
  have hSqNormEq : cubeFractionalSqNorm hd z r hr threeQuarterOrder
      (v : SobolevData (centeredCube z r hr)).1 = A ^ 2 + B ^ 2 := by
    show (cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
        (fun _ : Fin 1 => (v : SobolevData (centeredCube z r hr)).1)).toReal ^ 2 +
      (∑ _i : Fin 1, ‖(v : SobolevData (centeredCube z r hr)).1‖ ^ 2) /
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) = _
    rw [hAdef, hBdef, Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul, div_pow,
      Real.sq_sqrt (by positivity : (0:ℝ) ≤ volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))]
  have hsq : (r ^ (-(3 / 4 : ℝ))) ^ 2 = r ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast (r ^ (-(3 / 4 : ℝ))) 2, ← Real.rpow_mul hr.le]
    norm_num
  have hcauchy : (A + r ^ (-(3 / 4 : ℝ)) * B) ^ 2 ≤
      (1 + (r ^ (-(3 / 4 : ℝ))) ^ 2) * (A ^ 2 + B ^ 2) := by
    nlinarith [sq_nonneg (r ^ (-(3 / 4 : ℝ)) * A - B), sq_nonneg (r ^ (-(3 / 4 : ℝ)))]
  rw [hL2eq]
  calc (A + r ^ (-(3 / 4 : ℝ)) * B) ^ 2
      ≤ (1 + (r ^ (-(3 / 4 : ℝ))) ^ 2) * (A ^ 2 + B ^ 2) := hcauchy
    _ = (1 + r ^ (-(3 / 2 : ℝ))) * cubeFractionalSqNorm hd z r hr threeQuarterOrder
          (v : SobolevData (centeredCube z r hr)).1 := by rw [hsq, hSqNormEq]
    _ ≤ (1 + r ^ (-(3 / 2 : ℝ))) *
          (K1 * sobolevCoefficientForm a (v : SobolevData (centeredCube z r hr))
            (v : SobolevData (centeredCube z r hr))) :=
        mul_le_mul_of_nonneg_left hc1v (by positivity)

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput in
theorem aux_car_variational_hpack_at_N
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    [IsMarkovKernel (KN N)]
    (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ omega x, Measure.map LifetimePath.ofContinuousPath (KN N (omega, x)) = L N omega x)
    (hLlocal : LocalDiffusion (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N)
      (L N omega))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (RN : ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRN_formula : ∀ (N : ℕ) (omega : BilateralField d) (lam : ℝ)
        (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d),
      RN N omega lam f x =
        ∫ path, (∫ t in Set.Ioi (0 : ℝ),
          Set.indicator
            {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
              (centeredCube z r hr : Set (SpatialCoordinates d)) path}
            (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
          ∂(KN N (omega, x)))
    (hRNbound : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
      |RN N omega lam f x| ≤ ‖f‖ / lam) :
    ∃ u0 : killedSobolevGraph (centeredCube z r hr),
      (RN N omega lam f =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        ((u0 : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)) ∧
      (∀ w : killedSobolevGraph (centeredCube z r hr),
        sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
          (u0 : SobolevData (centeredCube z r hr)) (w : SobolevData (centeredCube z r hr)) =
          ∫ x, (f x - lam * RN N omega lam f x) *
            (w : SobolevData (centeredCube z r hr)).1 x
            ∂((cutoffSpeedMeasure M H omega N).restrict
              (closure (centeredCube z r hr : Set (SpatialCoordinates d))))) ∧
      sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
        (u0 : SobolevData (centeredCube z r hr)) (u0 : SobolevData (centeredCube z r hr)) ≤
        ‖f‖ ^ 2 * (((cutoffSpeedMeasure M H omega N).restrict
          (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal / lam := by
  let K0 : Kernel (SpatialCoordinates d) (ContinuousPath (SpatialCoordinates d)) :=
    (KN N).comap (Prod.mk omega) measurable_prodMk_left
  have hK0z : ∀ x, K0 x = KN N (omega, x) := fun x => Kernel.comap_apply _ _ _
  obtain ⟨u0, hu01, hu02⟩ := aux_car_variational_weak_ident M H omega N K0 (L N omega)
    (fun x => by rw [hK0z]; exact hL omega x) hLlocal z r hr lam hlam f
  have hoccRN : ∀ x, aux_car_variational_occupation K0
      (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x = RN N omega lam f x := by
    intro x
    show (∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
          (centeredCube z r hr : Set (SpatialCoordinates d)) path}
          (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t) ∂(K0 x)) = _
    rw [hK0z]
    exact (hRN_formula N omega lam f x).symm
  have hu01' : ((u0 : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      RN N omega lam f := by
    filter_upwards [hu01] with x hx
    rw [hx, hoccRN]
  have hu02' : ∀ w : killedSobolevGraph (centeredCube z r hr),
      sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N z hr)
        (u0 : SobolevData (centeredCube z r hr)) (w : SobolevData (centeredCube z r hr)) =
      ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        (f x - lam * RN N omega lam f x) * (w : SobolevData (centeredCube z r hr)).1 x
          ∂(cutoffSpeedMeasure M H omega N) := by
    intro w
    rw [hu02 w]
    simp only [hoccRN]
  obtain ⟨hfin1, _hfin2, hfin3, hfin4⟩ := aux_car_variational_hfinite_of_weak_ident hd M H omega N
    z r hr lam hlam f (RN N omega lam f) u0 hu01' hu02' hRNbound
  exact ⟨u0, hfin1, hfin3, hfin4⟩

theorem aux_car_variational_hidentify_and_converge
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Qtri : Homogenization.TriadicCube d) (hr : 0 < Homogenization.cubeScaleFactor Qtri)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr),
      ‖(v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube
          (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) v‖)
    (omega : BilateralField d)
    (G : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) →L[ℝ]
      DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr))
    (hG : ∀ f : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr),
      Tendsto (fun N : ℕ =>
        (responseSolution (killedResponseSpace (Ω := centeredCube
              (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) hP)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
            ((sobolevVolumeLoad f).comp
              (killedResponseSpace (Ω := centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr) hP).space.subtypeL)).val.1)
        atTop (𝓝 (G f)))
    (K1 : ℝ) (hK1 : 0 < K1)
    (hc1 : ∀ (N : ℕ) (v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr)),
      cubeFractionalSqNorm hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr threeQuarterOrder
          (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr)).1 ≤
        K1 * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
            (Homogenization.cubeCenter Qtri) hr)
          (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr))
          (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr)))
    (muFull : Measure (SpatialCoordinates d))
    (hmuFull1 : MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) muFull ∧
      muFull (frontier (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) = 0 ∧
      muFull (closure (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) < ⊤)
    (K C : ℝ)
    (T : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder →
      Lp ℝ 2 (muFull.restrict (closure (centeredCube
        (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr :
        Set (SpatialCoordinates d)))))
    (hT : MeasureTraceCharacterization hd Qtri hr
        (muFull.restrict (closure (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))
        K C T)
    (hKCnn : 0 ≤ K ∧ 0 ≤ C)
    (i : (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)) →
      (limitFormEnergy G u).toENNReal ≠ ⊤ →
      CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder)
    (hi : ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr))
      (hu : (limitFormEnergy G u).toENNReal ≠ ⊤), (i u hu).val 0 = u)
    (J : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) → SpatialCoordinates d → ℝ)
    (hJ : ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr))
      (hu : (limitFormEnergy G u).toENNReal ≠ ⊤),
      (J u) =ᵐ[muFull.restrict (closure (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))]
        (T (i u hu) : SpatialCoordinates d → ℝ))
    (lam : ℝ) (hlam : 0 < lam) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (ustar : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr))
    (hustar_ne : (limitFormEnergy G ustar).toENNReal ≠ ⊤)
    (hmin : ∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr),
      (limitFormEnergy G w).toENNReal ≠ ⊤ →
      (limitFormEnergy G ustar).toENNReal.toReal + lam * (∫ x, J ustar x ^ 2 ∂muFull.restrict
          (closure (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))) -
        2 * ∫ x, f x * J ustar x ∂muFull.restrict (closure
          (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) ≤
      (limitFormEnergy G w).toENNReal.toReal + lam * (∫ x, J w x ^ 2 ∂muFull.restrict
          (closure (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))) -
        2 * ∫ x, f x * J w x ∂muFull.restrict (closure
          (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))
    (huniq : ∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr),
      (limitFormEnergy G w).toENNReal ≠ ⊤ →
      (∀ v : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr),
        (limitFormEnergy G v).toENNReal ≠ ⊤ →
        (limitFormEnergy G w).toENNReal.toReal + lam * (∫ x, J w x ^ 2 ∂muFull.restrict
            (closure (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))) -
          2 * ∫ x, f x * J w x ∂muFull.restrict (closure
            (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) ≤
        (limitFormEnergy G v).toENNReal.toReal + lam * (∫ x, J v x ^ 2 ∂muFull.restrict
            (closure (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))) -
          2 * ∫ x, f x * J v x ∂muFull.restrict (closure
            (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))) →
      w = ustar)
    (RN : ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRNbound : ∀ (N : ℕ), ∀ x ∈ (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)),
      |RN N omega lam f x| ≤ ‖f‖ / lam)
    (hRNzero : ∀ (N : ℕ), ∀ x ∈ frontier (closure (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))),
      RN N omega lam f x = 0)
    (CHol : ℝ) (hCHol0 : 0 < CHol)
    (hHolderR : ∀ N, ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)),
      ∀ y ∈ closure (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)),
      |RN N omega lam f x - RN N omega lam f y| ≤ CHol * dist x y ^ (1 / 4 : ℝ))
    (Region : Set (SpatialCoordinates d))
    (hNeighborhood : ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
      Metric.ball x 1 ⊆ Region)
    (Kmu : ℝ) (hKmu0 : 0 ≤ Kmu) (epsilon : ℝ) (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (hgrowthBound : ∀ x ∈ Region, ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        muFull (Metric.ball x rr) ≤ ENNReal.ofReal (Kmu * rr ^ ((d : ℝ) - epsilon)) ∧
          ∀ N, cutoffSpeedMeasure M H omega N (Metric.ball x rr) ≤
            ENNReal.ofReal (Kmu * rr ^ ((d : ℝ) - epsilon)))
    (SInterp : CubeFractionalInterpolationInput d hd)
    (u : ℕ → killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr))
    (hfinite : ∀ N : ℕ,
      (RN N omega lam f =ᵐ[volume.restrict (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))]
        ((u N : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)).1 : SpatialCoordinates d → ℝ)) ∧
      (∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr),
        sobolevCoefficientForm
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
            (u N : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr))
            (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr)) =
          ∫ x, (f x - lam * RN N omega lam f x) * (w : SobolevData
              (centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr)).1 x
            ∂((cutoffSpeedMeasure M H omega N).restrict (closure
              ((centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))))) ∧
      sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
          (u N : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr))
          (u N : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr)) ≤
        ‖f‖ ^ 2 * ((cutoffSpeedMeasure M H omega N).restrict (closure
            ((centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))
          ((centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))).toReal
          / lam) :
    ∃ g : SpatialCoordinates d → ℝ,
      ContinuousOn g (closure (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) ∧
      (∀ x ∈ frontier (closure (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))), g x = 0) ∧
      (∀ x ∈ closure (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)),
        Filter.limsup (fun N => RN N omega lam f x) atTop = g x) ∧
      (∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
        ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)),
          |RN k omega lam f x - g x| < eps) ∧
      g =ᵐ[volume.restrict (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))]
        (ustar : SpatialCoordinates d → ℝ) := by
  set Kom : ℝ := max CHol (‖f‖ / lam) with hKomdef
  have hKom0 : 0 ≤ Kom := le_trans hCHol0.le (le_max_left _ _)
  have hbound : ∀ N, ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)),
      |RN N omega lam f x| ≤ Kom := by
    intro N x hx
    have hmapsto : Set.MapsTo (RN N omega lam f)
        (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr :
          Set (SpatialCoordinates d))
        (Set.Icc (-(‖f‖ / lam)) (‖f‖ / lam)) :=
      fun y hy => abs_le.mp (hRNbound N y hy)
    have hcontN : ContinuousOn (RN N omega lam f)
        (closure (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) :=
      aux_prop_uniform_resolvent_subsequence_bridge_holder_continuousOn
        (RN N omega lam f) (closure (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) CHol hCHol0.le
        (hHolderR N)
    have hmapsto' := (hmapsto.closure_of_continuousOn hcontN) hx
    rw [(isClosed_Icc).closure_eq] at hmapsto'
    exact (abs_le.mpr hmapsto').trans (le_max_right _ _)
  have hcont : ∀ N, ContinuousOn (RN N omega lam f)
      (closure (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) := by
    intro N
    exact aux_prop_uniform_resolvent_subsequence_bridge_holder_continuousOn
      (RN N omega lam f) (closure (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) CHol hCHol0.le
      (hHolderR N)
  have hzero : ∀ N, ∀ x ∈ frontier (closure (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))),
      RN N omega lam f x = 0 :=
    fun N => hRNzero N
  have hHolderR' : ∀ N, ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)),
      ∀ y ∈ closure (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)),
      |RN N omega lam f x - RN N omega lam f y| ≤ Kom * dist x y ^ (1 / 4 : ℝ) := by
    intro N x hx y hy
    exact (hHolderR N x hx y hy).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hQbdd : Bornology.IsBounded (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) :=
    centeredCube_isBounded (Homogenization.cubeCenter Qtri) hr
  have hQopen : IsOpen (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) :=
    (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr).isOpen
  have hQne : (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)).Nonempty :=
    aux_prop_speed_resolvent_cube_nonempty (Homogenization.cubeCenter Qtri) hr
  set K1' : ℝ := (1 + (Homogenization.cubeScaleFactor Qtri) ^ (-(3 / 2 : ℝ))) * K1 with hK1'def
  have hK1'0 : 0 < K1' := by
    rw [hK1'def]; positivity
  have hc1' : ∀ N (v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr)),
      ∃ v3 : CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
        v3.val 0 = (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)).1 ∧
        (cubeFractionalL2Norm hd (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3) ^ 2 ≤
          K1' * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
              (Homogenization.cubeCenter Qtri) hr)
            (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr))
            (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr)) := by
    intro N v
    obtain ⟨v3, hv30, hv3b⟩ := aux_car_variational_hcoer3_of_hc1 hd Sf
      (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
      K1 hK1.le v (hc1 N v)
    exact ⟨v3, hv30, by rw [hK1'def, mul_assoc]; exact hv3b⟩
  have hidentify : ∀ g : C(SpatialCoordinates d, ℝ),
      (∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
          ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)),
            |RN (σ k) omega lam f x - g x| < eps) →
      (g : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri)
            hr : Set (SpatialCoordinates d))]
        (ustar : SpatialCoordinates d → ℝ) := by
    intro g ⟨σ, hσ, hunif⟩
    have hmosco := inputs_classical_mosco_liminf hP
      (fun N => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
      G hG
    exact aux_car_variational_hidentify_at_omega hd epsilon hepsilon' Qtri hr M H omega Region
      hNeighborhood muFull hmuFull1 Kmu hKmu0 hgrowthBound
      (fun u => (limitFormEnergy G u).toENNReal) hmosco
      T K C ⟨hKCnn.1, hKCnn.2, hT⟩ i hi J hJ lam hlam f
      ustar ⟨hustar_ne, hmin, huniq⟩ u (fun N => RN N omega lam f) hfinite K1' hK1'0 hc1' SInterp
      g σ hσ hunif
  obtain ⟨g, hgcont, hgzero, hglimsup, hgunif, _hgHolder, hgustar⟩ :=
    aux_car_variational_full_convergence_of_hidentify
      (centeredCube (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr :
        Set (SpatialCoordinates d)) hQopen hQne hQbdd (fun N => RN N omega lam f) ustar hcont hzero
      Kom hKom0 hbound hHolderR' hidentify
  exact ⟨g, hgcont, hgzero, hglimsup, hgunif, hgustar⟩

theorem aux_car_variational_growth_muFull_bridge
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (epsilon : ℝ)
    (Region : Set (SpatialCoordinates d))
    (muFull muChaos : Measure (SpatialCoordinates d))
    (hmuFullconv : MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) muFull)
    [IsLocallyFiniteMeasure muChaos] [muChaos.IsOpenPosMeasure]
    (hmuChaosconv : MeasuresConvergeLocally (fun N => weightedChaosCutoff M H N omega) muChaos)
    (Kmu : ℝ) (_hKmu0 : 0 ≤ Kmu)
    (hKmuBound : (∀ N x, x ∈ Region → ∀ r, 0 < r → r ≤ 1 →
        weightedChaosCutoff M H N omega (Metric.ball x r) ≤
          ENNReal.ofReal (Kmu * r ^ ((d : ℝ) - epsilon))) ∧
      (∀ x, x ∈ Region → ∀ r, 0 < r → r ≤ 1 →
        muChaos (Metric.ball x r) ≤ ENNReal.ofReal (Kmu * r ^ ((d : ℝ) - epsilon)))) :
    ∀ x ∈ Region, ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
      muFull (Metric.ball x rr) ≤ ENNReal.ofReal (Kmu * rr ^ ((d : ℝ) - epsilon)) ∧
        ∀ N, cutoffSpeedMeasure M H omega N (Metric.ball x rr) ≤
          ENNReal.ofReal (Kmu * rr ^ ((d : ℝ) - epsilon)) := by
  have hconvEq : (fun N => weightedChaosCutoff M H N omega) =
      (fun N => cutoffSpeedMeasure M H omega N) :=
    funext (fun N => (cutoffSpeedMeasure_eq_weightedChaosCutoff M H omega N).symm)
  refine fun x hx rr hrr0 hrr1 => ⟨?_, fun N => ?_⟩
  · exact aux_car_variational_muFull_growth (fun N => cutoffSpeedMeasure M H omega N)
      muChaos muFull (hconvEq ▸ hmuChaosconv) hmuFullconv x rr hrr0
      (ENNReal.ofReal (Kmu * rr ^ ((d : ℝ) - epsilon))) ENNReal.ofReal_ne_top
      (hKmuBound.2 x hx rr hrr0 hrr1)
  · rw [cutoffSpeedMeasure_eq_weightedChaosCutoff]
    exact hKmuBound.1 N x hx rr hrr0 hrr1

theorem aux_car_variational_hRemaining_final
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q0 : Opens (SpatialCoordinates d))
    (Elim0 : BilateralField d → DomainL2 Q0 → ℝ≥0∞)
    (Func0 : BilateralField d → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      DomainL2 Q0 → ℝ)
    (RN : ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (Rn : BilateralField d → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
        SpatialCoordinates d → ℝ)
    (hRndef : ∀ omega lam f x, Rn omega lam f x = Filter.limsup (fun N => RN N omega lam f x) atTop)
    (hzeroOutside : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ (N : ℕ) (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ x ∉ (Q0 : Set (SpatialCoordinates d)),
          RN N omega lam f x = 0)
    (hcontAE : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (lam : ℝ), 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ N : ℕ, ContinuousOn (RN N omega lam f)
          (closure (Q0 : Set (SpatialCoordinates d))))
    (hUniform : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (lam : ℝ), 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ delta : ℝ, 0 < delta → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
          ∀ x ∈ closure (Q0 : Set (SpatialCoordinates d)),
            |RN N omega lam f x - Rn omega lam f x| < delta)
    (hVariational : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (lam : ℝ), 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∃ ustar : DomainL2 Q0,
          Elim0 omega ustar ≠ ⊤ ∧
          (Rn omega lam f) =ᵐ[volume.restrict (Q0 : Set (SpatialCoordinates d))]
            (ustar : SpatialCoordinates d → ℝ) ∧
          (∀ v : DomainL2 Q0, Elim0 omega v ≠ ⊤ →
            Func0 omega lam f ustar ≤ Func0 omega lam f v) ∧
          (∀ v : DomainL2 Q0, Elim0 omega v ≠ ⊤ →
            (∀ w : DomainL2 Q0, Elim0 omega w ≠ ⊤ →
              Func0 omega lam f v ≤ Func0 omega lam f w) →
            v = ustar)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      (∀ (lam : ℝ), 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ContinuousOn (Rn omega lam f) (closure (Q0 : Set (SpatialCoordinates d))) ∧
        ∀ x ∈ frontier (Q0 : Set (SpatialCoordinates d)),
          Rn omega lam f x = 0) ∧
      (∀ (lam : ℝ), 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ delta : ℝ, 0 < delta → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
          ∀ x ∈ closure (Q0 : Set (SpatialCoordinates d)),
            |RN N omega lam f x - Rn omega lam f x| < delta) ∧
      (∀ (lam : ℝ), 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∃ ustar : DomainL2 Q0,
          Elim0 omega ustar ≠ ⊤ ∧
          (Rn omega lam f) =ᵐ[volume.restrict (Q0 : Set (SpatialCoordinates d))]
            (ustar : SpatialCoordinates d → ℝ) ∧
          (∀ v : DomainL2 Q0, Elim0 omega v ≠ ⊤ →
            Func0 omega lam f ustar ≤ Func0 omega lam f v) ∧
          (∀ v : DomainL2 Q0, Elim0 omega v ≠ ⊤ →
            (∀ w : DomainL2 Q0, Elim0 omega w ≠ ⊤ →
              Func0 omega lam f v ≤ Func0 omega lam f w) →
            v = ustar)) := by
  have hContinuous : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (lam : ℝ), 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ContinuousOn (Rn omega lam f) (closure (Q0 : Set (SpatialCoordinates d))) := by
    filter_upwards [hUniform, hcontAE] with omega hunif hcont
    intro lam hlam f
    have htu : TendstoUniformlyOn (fun N : ℕ => RN N omega lam f)
        (Rn omega lam f) atTop (closure (Q0 : Set (SpatialCoordinates d))) := by
      apply Metric.tendstoUniformlyOn_iff.mpr
      intro eps heps
      obtain ⟨N0, hN0⟩ := hunif lam hlam f eps heps
      filter_upwards [eventually_ge_atTop N0] with N hN x hx
      rw [Real.dist_eq]
      simpa only [abs_sub_comm] using hN0 N hN x hx
    exact htu.continuousOn
      (Eventually.of_forall (fun N => hcont lam hlam f N)).frequently
  have hRnzero : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (lam : ℝ), 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ x ∈ frontier (Q0 : Set (SpatialCoordinates d)),
          Rn omega lam f x = 0 := by
    filter_upwards [hzeroOutside] with omega hω
    intro lam hlam f x hx
    rw [hRndef]
    have hseq : (fun N : ℕ => RN N omega lam f x) = fun _ => 0 := by
      funext N
      exact hω N lam hlam f x (fun hxQ =>
        (disjoint_left.1 (disjoint_frontier_iff_isOpen.mpr Q0.isOpen) hx) hxQ)
    rw [hseq]
    simp
  filter_upwards [hContinuous, hRnzero, hUniform, hVariational]
    with omega hcont hzero hunif hvar
  exact ⟨(fun lam hlam f => ⟨hcont lam hlam f, hzero lam hlam f⟩), hunif, hvar⟩

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput in
theorem aux_car_variational_hFullConv
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHI : InfraredCharacterization M H)
    (Qtri : Homogenization.TriadicCube d) (hr : 0 < Homogenization.cubeScaleFactor Qtri)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr),
      ‖(v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube
          (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) v‖)
    (G : BilateralField d → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) →L[ℝ]
      DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr))
    (hG_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ f : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr),
        Tendsto (fun N : ℕ =>
          (responseSolution (killedResponseSpace (Ω := centeredCube
                (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) hP)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
              ((sobolevVolumeLoad f).comp
                (killedResponseSpace (Ω := centeredCube (Homogenization.cubeCenter Qtri)
                  (Homogenization.cubeScaleFactor Qtri) hr) hP).space.subtypeL)).val.1)
          atTop (𝓝 (G omega f)))
    (hK1_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K1 : ℝ, 0 < K1 ∧
      ∀ (N : ℕ) (v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)),
        cubeFractionalSqNorm hd (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr threeQuarterOrder
            (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr)).1 ≤
          K1 * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
              (Homogenization.cubeCenter Qtri) hr)
            (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr))
            (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr)))
    (muFull : BilateralField d → Measure (SpatialCoordinates d))
    (hmuFull_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) (muFull omega) ∧
      muFull omega (frontier (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) = 0 ∧
      muFull omega (closure (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) < ⊤)
    (K C : BilateralField d → ℝ)
    (T : (omega : BilateralField d) → CubeFractionalL2 (k := 1) hd
        (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr
        halfFractionalOrder →
      Lp ℝ 2 ((muFull omega).restrict (closure (centeredCube
        (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr :
        Set (SpatialCoordinates d)))))
    (hT_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasureTraceCharacterization hd Qtri hr
        ((muFull omega).restrict (closure (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))
        (K omega) (C omega) (T omega))
    (hKCnn_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, 0 ≤ K omega ∧ 0 ≤ C omega)
    (i : (omega : BilateralField d) →
        (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr)) →
          (limitFormEnergy (G omega) u).toENNReal ≠ ⊤ →
          CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder)
    (hi_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr))
        (hu : (limitFormEnergy (G omega) u).toENNReal ≠ ⊤), (i omega u hu).val 0 = u)
    (J : (omega : BilateralField d) → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) → SpatialCoordinates d → ℝ)
    (hJ_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr))
        (hu : (limitFormEnergy (G omega) u).toENNReal ≠ ⊤),
        (J omega u) =ᵐ[(muFull omega).restrict (closure (centeredCube
            (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr :
            Set (SpatialCoordinates d)))] (T omega (i omega u hu) : SpatialCoordinates d → ℝ))
    (hKtr_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ Ktr : ℝ, 0 ≤ Ktr ∧
      ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr))
        (_hu : (limitFormEnergy (G omega) u).toENNReal ≠ ⊤),
        (∫⁻ x, ENNReal.ofReal (J omega u x ^ 2)
            ∂((muFull omega).restrict (closure (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))) ≤
          ENNReal.ofReal Ktr * (limitFormEnergy (G omega) u).toENNReal)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ N omega x, Measure.map LifetimePath.ofContinuousPath (KN N (omega, x)) = L N omega x)
    (hLlocal_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      LocalDiffusion (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (L N omega))
    (RN : ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRN_formula : ∀ (N : ℕ) (omega : BilateralField d) (lam : ℝ)
        (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d),
      RN N omega lam f x =
        ∫ path, (∫ t in Set.Ioi (0 : ℝ),
          Set.indicator
            {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
              (centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) path}
            (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
          ∂(KN N (omega, x)))
    (hRNbound : ∀ (N : ℕ) (omega : BilateralField d) (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ x ∈ (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)),
          |RN N omega lam f x| ≤ ‖f‖ / lam)
    (hRNzero_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∀ x ∈ frontier (closure (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))),
            RN N omega lam f x = 0)
    (epsilon : ℝ) (_hepsilon : epsilon ∈ Set.Ioo (0 : ℝ) 1)
    (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (Region : Set (SpatialCoordinates d))
    (hNeighborhood : ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
      Metric.ball x 1 ⊆ Region)
    (hGrowth_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ Kmu : ℝ, 0 ≤ Kmu ∧
      ∀ x ∈ Region, ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        muFull omega (Metric.ball x rr) ≤ ENNReal.ofReal (Kmu * rr ^ ((d : ℝ) - epsilon)) ∧
          ∀ N, cutoffSpeedMeasure M H omega N (Metric.ball x rr) ≤
            ENNReal.ofReal (Kmu * rr ^ ((d : ℝ) - epsilon)))
    (hHolderAll_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ),
            ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
            ∀ y ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              |RN N omega lam f x - RN N omega lam f y| ≤ C * dist x y ^ (1 / 4 : ℝ))
    (SInterp : CubeFractionalInterpolationInput d hd) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∃ ustar : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr),
            ((limitFormEnergy (G omega) ustar).toENNReal ≠ ⊤ ∧
            (∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr),
              (limitFormEnergy (G omega) w).toENNReal ≠ ⊤ →
              (limitFormEnergy (G omega) ustar).toENNReal.toReal +
                  lam * (∫ x, J omega ustar x ^ 2 ∂((muFull omega).restrict (closure
                    (centeredCube (Homogenization.cubeCenter Qtri)
                      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))) -
                2 * ∫ x, f x * J omega ustar x ∂((muFull omega).restrict (closure
                    (centeredCube (Homogenization.cubeCenter Qtri)
                      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))) ≤
              (limitFormEnergy (G omega) w).toENNReal.toReal +
                  lam * (∫ x, J omega w x ^ 2 ∂((muFull omega).restrict (closure
                    (centeredCube (Homogenization.cubeCenter Qtri)
                      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))) -
                2 * ∫ x, f x * J omega w x ∂((muFull omega).restrict (closure
                    (centeredCube (Homogenization.cubeCenter Qtri)
                      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))) ∧
            (∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr),
              (limitFormEnergy (G omega) w).toENNReal ≠ ⊤ →
              (∀ v : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
                  (Homogenization.cubeScaleFactor Qtri) hr),
                (limitFormEnergy (G omega) v).toENNReal ≠ ⊤ →
                (limitFormEnergy (G omega) w).toENNReal.toReal +
                    lam * (∫ x, J omega w x ^ 2 ∂((muFull omega).restrict (closure
                      (centeredCube (Homogenization.cubeCenter Qtri)
                        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))) -
                  2 * ∫ x, f x * J omega w x ∂((muFull omega).restrict (closure
                      (centeredCube (Homogenization.cubeCenter Qtri)
                        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))) ≤
                (limitFormEnergy (G omega) v).toENNReal.toReal +
                    lam * (∫ x, J omega v x ^ 2 ∂((muFull omega).restrict (closure
                      (centeredCube (Homogenization.cubeCenter Qtri)
                        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))) -
                  2 * ∫ x, f x * J omega v x ∂((muFull omega).restrict (closure
                      (centeredCube (Homogenization.cubeCenter Qtri)
                        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))) →
              w = ustar)) ∧
            ∃ g : SpatialCoordinates d → ℝ,
              ContinuousOn g (closure (centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) ∧
              (∀ x ∈ frontier (closure (centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))),
                g x = 0) ∧
              (∀ x ∈ closure (centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)),
                Filter.limsup (fun N => RN N omega lam f x) atTop = g x) ∧
              (∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
                ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter Qtri)
                  (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)),
                  |RN k omega lam f x - g x| < eps) ∧
              g =ᵐ[volume.restrict (centeredCube (Homogenization.cubeCenter Qtri)
                  (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))]
                (ustar : SpatialCoordinates d → ℝ) := by
  filter_upwards [hG_ae, hK1_ae, hmuFull_ae, hT_ae, hKCnn_ae, hi_ae, hJ_ae, hKtr_ae, hLlocal_ae,
    hRNzero_ae, hGrowth_ae, hHolderAll_ae]
    with omega hG hK1all hmuFull1 hT hKCnn hi hJ hKtrall hLlocal hRNzero hGrowth1 hHolderAll1
  intro lam hlam f
  obtain ⟨K1, hK1, hc1⟩ := hK1all
  obtain ⟨Ktr, hKtr, hJtr⟩ := hKtrall
  have hmufin' : ((muFull omega).restrict (closure (centeredCube
      (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr :
      Set (SpatialCoordinates d)))) Set.univ < ⊤ := by
    rw [Measure.restrict_apply_univ]; exact hmuFull1.2.2
  obtain ⟨ustar, hustar_ne, hmin, huniq⟩ :=
    aux_car_variational_variational_step hd Sf M H hHI omega Qtri hr hP (G omega) hG K1 hK1
      hc1 ((muFull omega).restrict (closure (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))
      (muFull omega) rfl hmufin' (K omega) (C omega) (T omega) hT (i omega) hi (J omega) hJ
      Ktr hKtr hJtr lam hlam f
  refine ⟨ustar, ⟨hustar_ne, hmin, huniq⟩, ?_⟩
  have hpack : ∀ N : ℕ, ∃ u0 : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
      (Homogenization.cubeScaleFactor Qtri) hr),
      (RN N omega lam f =ᵐ[volume.restrict (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))]
        ((u0 : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)).1 : SpatialCoordinates d → ℝ)) ∧
      (∀ w : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr),
        sobolevCoefficientForm
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
            (u0 : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr))
            (w : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr)) =
          ∫ x, (f x - lam * RN N omega lam f x) * (w : SobolevData
              (centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr)).1 x
            ∂((cutoffSpeedMeasure M H omega N).restrict (closure
              ((centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))))) ∧
      sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
          (u0 : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr))
          (u0 : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr)) ≤
        ‖f‖ ^ 2 * ((cutoffSpeedMeasure M H omega N).restrict (closure
            ((centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)))
          ((centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d))).toReal
          / lam := fun N => by
    have := hKN N
    exact aux_car_variational_hpack_at_N hd M H omega N KN L (hL N) (hLlocal N)
      (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr lam hlam f
      RN hRN_formula (hRNbound N omega lam hlam f)
  choose u hfinite using hpack
  obtain ⟨CHol, hCHol0, hHolderR⟩ := hHolderAll1 lam hlam f
  obtain ⟨Kmu, hKmu0, hgrowthBound⟩ := hGrowth1
  exact aux_car_variational_hidentify_and_converge hd Sf M H Qtri hr hP omega (G omega) hG K1 hK1
    hc1 (muFull omega) hmuFull1 (K omega) (C omega) (T omega) hT hKCnn (i omega) hi (J omega) hJ
    lam hlam f ustar hustar_ne hmin huniq RN (fun N => hRNbound N omega lam hlam f)
    (fun N => hRNzero N lam hlam f) CHol hCHol0 hHolderR Region hNeighborhood Kmu hKmu0 epsilon
    hepsilon' hgrowthBound SInterp u hfinite

open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput in
theorem aux_car_variational_hUniform_hVariational
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHI : InfraredCharacterization M H)
    (Qtri : Homogenization.TriadicCube d) (hr : 0 < Homogenization.cubeScaleFactor Qtri)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr),
      ‖(v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube
          (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr)) v‖)
    (G : BilateralField d → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) →L[ℝ]
      DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr))
    (hG_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ f : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr),
        Tendsto (fun N : ℕ =>
          (responseSolution (killedResponseSpace (Ω := centeredCube
                (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr) hP)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N (Homogenization.cubeCenter Qtri) hr)
              ((sobolevVolumeLoad f).comp
                (killedResponseSpace (Ω := centeredCube (Homogenization.cubeCenter Qtri)
                  (Homogenization.cubeScaleFactor Qtri) hr) hP).space.subtypeL)).val.1)
          atTop (𝓝 (G omega f)))
    (hK1_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K1 : ℝ, 0 < K1 ∧
      ∀ (N : ℕ) (v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr)),
        cubeFractionalSqNorm hd (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr threeQuarterOrder
            (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr)).1 ≤
          K1 * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
              (Homogenization.cubeCenter Qtri) hr)
            (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr))
            (v : SobolevData (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr)))
    (muFull : BilateralField d → Measure (SpatialCoordinates d))
    (hmuFull_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) (muFull omega) ∧
      muFull omega (frontier (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) = 0 ∧
      muFull omega (closure (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) < ⊤)
    (K C : BilateralField d → ℝ)
    (T : (omega : BilateralField d) → CubeFractionalL2 (k := 1) hd
        (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr
        halfFractionalOrder →
      Lp ℝ 2 ((muFull omega).restrict (closure (centeredCube
        (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr :
        Set (SpatialCoordinates d)))))
    (hT_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasureTraceCharacterization hd Qtri hr
        ((muFull omega).restrict (closure (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))
        (K omega) (C omega) (T omega))
    (hKCnn_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, 0 ≤ K omega ∧ 0 ≤ C omega)
    (i : (omega : BilateralField d) →
        (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr)) →
          (limitFormEnergy (G omega) u).toENNReal ≠ ⊤ →
          CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr halfFractionalOrder)
    (hi_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr))
        (hu : (limitFormEnergy (G omega) u).toENNReal ≠ ⊤), (i omega u hu).val 0 = u)
    (J : (omega : BilateralField d) → DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) → SpatialCoordinates d → ℝ)
    (hJ_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr))
        (hu : (limitFormEnergy (G omega) u).toENNReal ≠ ⊤),
        (J omega u) =ᵐ[(muFull omega).restrict (closure (centeredCube
            (Homogenization.cubeCenter Qtri) (Homogenization.cubeScaleFactor Qtri) hr :
            Set (SpatialCoordinates d)))] (T omega (i omega u hu) : SpatialCoordinates d → ℝ))
    (hKtr_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ Ktr : ℝ, 0 ≤ Ktr ∧
      ∀ (u : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr))
        (_hu : (limitFormEnergy (G omega) u).toENNReal ≠ ⊤),
        (∫⁻ x, ENNReal.ofReal (J omega u x ^ 2)
            ∂((muFull omega).restrict (closure (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))))) ≤
          ENNReal.ofReal Ktr * (limitFormEnergy (G omega) u).toENNReal)
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ N omega x, Measure.map LifetimePath.ofContinuousPath (KN N (omega, x)) = L N omega x)
    (hLlocal_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      LocalDiffusion (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (L N omega))
    (RN : ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRN_formula : ∀ (N : ℕ) (omega : BilateralField d) (lam : ℝ)
        (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) (x : SpatialCoordinates d),
      RN N omega lam f x =
        ∫ path, (∫ t in Set.Ioi (0 : ℝ),
          Set.indicator
            {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
              (centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)) path}
            (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
          ∂(KN N (omega, x)))
    (hRNbound : ∀ (N : ℕ) (omega : BilateralField d) (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ x ∈ (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)),
          |RN N omega lam f x| ≤ ‖f‖ / lam)
    (hRNzero_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∀ x ∈ frontier (closure (centeredCube (Homogenization.cubeCenter Qtri)
            (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))),
            RN N omega lam f x = 0)
    (epsilon : ℝ) (hepsilon : epsilon ∈ Set.Ioo (0 : ℝ) 1)
    (hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)))
    (Region : Set (SpatialCoordinates d))
    (hNeighborhood : ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
      Metric.ball x 1 ⊆ Region)
    (hGrowth_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ Kmu : ℝ, 0 ≤ Kmu ∧
      ∀ x ∈ Region, ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        muFull omega (Metric.ball x rr) ≤ ENNReal.ofReal (Kmu * rr ^ ((d : ℝ) - epsilon)) ∧
          ∀ N, cutoffSpeedMeasure M H omega N (Metric.ball x rr) ≤
            ENNReal.ofReal (Kmu * rr ^ ((d : ℝ) - epsilon)))
    (hHolderAll_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ),
            ∀ x ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
            ∀ y ∈ closure ((centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr) : Set (SpatialCoordinates d)),
              |RN N omega lam f x - RN N omega lam f y| ≤ C * dist x y ^ (1 / 4 : ℝ))
    (SInterp : CubeFractionalInterpolationInput d hd) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      (∀ (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∀ delta : ℝ, 0 < delta → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
            ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)),
              |RN N omega lam f x -
                Filter.limsup (fun N => RN N omega lam f x) atTop| < delta) ∧
      (∀ (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ∃ ustar : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
              (Homogenization.cubeScaleFactor Qtri) hr),
            (limitFormEnergy (G omega) ustar).toENNReal ≠ ⊤ ∧
            (fun x => Filter.limsup (fun N => RN N omega lam f x) atTop) =ᵐ[volume.restrict
                (centeredCube (Homogenization.cubeCenter Qtri)
                  (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))]
              (ustar : SpatialCoordinates d → ℝ) ∧
            (∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr),
              (limitFormEnergy (G omega) w).toENNReal ≠ ⊤ →
              (limitFormEnergy (G omega) ustar).toENNReal.toReal + lam * (∫ x, J omega ustar x ^ 2 ∂(muFull omega).restrict
                  (closure (centeredCube (Homogenization.cubeCenter Qtri)
                    (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))) -
                2 * ∫ x, f x * J omega ustar x ∂(muFull omega).restrict (closure
                  (centeredCube (Homogenization.cubeCenter Qtri)
                    (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) ≤
              (limitFormEnergy (G omega) w).toENNReal.toReal + lam * (∫ x, J omega w x ^ 2 ∂(muFull omega).restrict
                  (closure (centeredCube (Homogenization.cubeCenter Qtri)
                    (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))) -
                2 * ∫ x, f x * J omega w x ∂(muFull omega).restrict (closure
                  (centeredCube (Homogenization.cubeCenter Qtri)
                    (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))) ∧
            (∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
                (Homogenization.cubeScaleFactor Qtri) hr),
              (limitFormEnergy (G omega) w).toENNReal ≠ ⊤ →
              (∀ v : DomainL2 (centeredCube (Homogenization.cubeCenter Qtri)
                  (Homogenization.cubeScaleFactor Qtri) hr),
                (limitFormEnergy (G omega) v).toENNReal ≠ ⊤ →
                (limitFormEnergy (G omega) w).toENNReal.toReal + lam * (∫ x, J omega w x ^ 2 ∂(muFull omega).restrict
                    (closure (centeredCube (Homogenization.cubeCenter Qtri)
                      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))) -
                  2 * ∫ x, f x * J omega w x ∂(muFull omega).restrict (closure
                    (centeredCube (Homogenization.cubeCenter Qtri)
                      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))) ≤
                (limitFormEnergy (G omega) v).toENNReal.toReal + lam * (∫ x, J omega v x ^ 2 ∂(muFull omega).restrict
                    (closure (centeredCube (Homogenization.cubeCenter Qtri)
                      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))) -
                  2 * ∫ x, f x * J omega v x ∂(muFull omega).restrict (closure
                    (centeredCube (Homogenization.cubeCenter Qtri)
                      (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)))) →
              w = ustar)) := by
  have hFC := aux_car_variational_hFullConv hd Sf M H hHI Qtri hr hP G hG_ae hK1_ae muFull
    hmuFull_ae K C T hT_ae hKCnn_ae i hi_ae J hJ_ae hKtr_ae KN hKN L hL hLlocal_ae RN hRN_formula
    hRNbound hRNzero_ae epsilon hepsilon hepsilon' Region hNeighborhood hGrowth_ae hHolderAll_ae
    SInterp
  filter_upwards [hFC] with omega hfc
  refine ⟨fun lam hlam f delta hdelta => ?_, fun lam hlam f => ?_⟩
  · obtain ⟨ustar, _, g, hgcont, hgzero, hglimsup, hgunif, hgustar⟩ := hfc lam hlam f
    obtain ⟨N0, hN0⟩ := hgunif delta hdelta
    refine ⟨N0, fun N hN x hx => ?_⟩
    rw [hglimsup x hx]
    exact hN0 N hN x hx
  · obtain ⟨ustar, ⟨hustar_ne, hmin, huniq⟩, g, hgcont, hgzero, hglimsup, hgunif, hgustar⟩ :=
      hfc lam hlam f
    refine ⟨ustar, hustar_ne, ?_, hmin, huniq⟩
    have hRneq : ∀ x ∈ (centeredCube (Homogenization.cubeCenter Qtri)
        (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d)),
        Filter.limsup (fun N => RN N omega lam f x) atTop = g x := fun x hx =>
      hglimsup x (subset_closure hx)
    have hae1 : (fun x => Filter.limsup (fun N => RN N omega lam f x) atTop) =ᵐ[volume.restrict
        (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr : Set (SpatialCoordinates d))] g :=
      Filter.eventuallyEq_of_mem (self_mem_ae_restrict
        (centeredCube (Homogenization.cubeCenter Qtri)
          (Homogenization.cubeScaleFactor Qtri) hr).isOpen.measurableSet) hRneq
    exact hae1.trans hgustar




open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput in
theorem aux_car_variational_hFixedCube_glue
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (Interp : CubeFractionalInterpolationInput d hd)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHI : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N)) (hin : in_crossing M H PN KN)
    (Qtri : ℕ → Homogenization.TriadicCube d)
    (hr : ∀ n : ℕ, 0 < Homogenization.cubeScaleFactor (Qtri n))
    (hP : ∀ n : ℕ, ∃ K : ℝ≥0,
        ∀ v : killedSobolevGraph (centeredCube (Homogenization.cubeCenter (Qtri n))
            (Homogenization.cubeScaleFactor (Qtri n)) (hr n)),
          ‖(v : SobolevData (centeredCube (Homogenization.cubeCenter (Qtri n))
              (Homogenization.cubeScaleFactor (Qtri n)) (hr n))).1‖ ≤
            K * ‖subspaceGradient (killedSobolevGraph (centeredCube
              (Homogenization.cubeCenter (Qtri n)) (Homogenization.cubeScaleFactor (Qtri n))
              (hr n))) v‖)
    (G : (n : ℕ) → BilateralField d →
        (DomainL2 (centeredCube (Homogenization.cubeCenter (Qtri n))
            (Homogenization.cubeScaleFactor (Qtri n)) (hr n)) →L[ℝ]
          DomainL2 (centeredCube (Homogenization.cubeCenter (Qtri n))
            (Homogenization.cubeScaleFactor (Qtri n)) (hr n))))
    (hGtendsto : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (n : ℕ) (f : DomainL2 (centeredCube (Homogenization.cubeCenter (Qtri n))
          (Homogenization.cubeScaleFactor (Qtri n)) (hr n))),
        Tendsto
          (fun N : ℕ =>
            (responseSolution (killedResponseSpace (Ω := centeredCube
                  (Homogenization.cubeCenter (Qtri n)) (Homogenization.cubeScaleFactor (Qtri n))
                  (hr n)) (hP n))
                (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                  (Homogenization.cubeCenter (Qtri n)) (hr n))
                ((sobolevVolumeLoad f).comp
                  (killedResponseSpace (Ω := centeredCube (Homogenization.cubeCenter (Qtri n))
                    (Homogenization.cubeScaleFactor (Qtri n)) (hr n)) (hP n)).space.subtypeL)).val.1)
          atTop (𝓝 (G n omega f)))
    (muFull : BilateralField d → Measure (SpatialCoordinates d))
    (hmuFull : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) (muFull omega) ∧
      (∀ n : ℕ, muFull omega (frontier (centeredCube (Homogenization.cubeCenter (Qtri n))
          (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d))) = 0) ∧
      (∀ n : ℕ, muFull omega (closure (centeredCube (Homogenization.cubeCenter (Qtri n))
          (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d))) < ⊤))
    (T : (n : ℕ) → (omega : BilateralField d) →
        CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter (Qtri n))
          (Homogenization.cubeScaleFactor (Qtri n)) (hr n) halfFractionalOrder →
        Lp ℝ 2 ((muFull omega).restrict (closure (centeredCube (Homogenization.cubeCenter (Qtri n))
          (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d)))))
    (Ktrace Ctrace : ℕ → BilateralField d → ℝ)
    (hT : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ n : ℕ, 0 ≤ Ktrace n omega ∧ 0 ≤ Ctrace n omega ∧
        MeasureTraceCharacterization hd (Qtri n) (hr n)
          ((muFull omega).restrict (closure (centeredCube (Homogenization.cubeCenter (Qtri n))
            (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d))))
          (Ktrace n omega) (Ctrace n omega) (T n omega))
    (i : (n : ℕ) → (omega : BilateralField d) →
        (u : DomainL2 (centeredCube (Homogenization.cubeCenter (Qtri n))
            (Homogenization.cubeScaleFactor (Qtri n)) (hr n))) →
        (limitFormEnergy (G n omega) u).toENNReal ≠ ⊤ →
        CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter (Qtri n))
          (Homogenization.cubeScaleFactor (Qtri n)) (hr n) halfFractionalOrder)
    (h_i_val : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (n : ℕ) (u : DomainL2 (centeredCube (Homogenization.cubeCenter (Qtri n))
            (Homogenization.cubeScaleFactor (Qtri n)) (hr n)))
        (hu : (limitFormEnergy (G n omega) u).toENNReal ≠ ⊤),
        (i n omega u hu).val 0 = u)
    (J : (n : ℕ) → BilateralField d → DomainL2 (centeredCube (Homogenization.cubeCenter (Qtri n))
        (Homogenization.cubeScaleFactor (Qtri n)) (hr n)) → SpatialCoordinates d → ℝ)
    (hJ : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (n : ℕ) (u : DomainL2 (centeredCube (Homogenization.cubeCenter (Qtri n))
            (Homogenization.cubeScaleFactor (Qtri n)) (hr n)))
        (hu : (limitFormEnergy (G n omega) u).toENNReal ≠ ⊤),
        (J n omega u) =ᵐ[(muFull omega).restrict (closure (centeredCube
            (Homogenization.cubeCenter (Qtri n)) (Homogenization.cubeScaleFactor (Qtri n))
            (hr n) : Set (SpatialCoordinates d)))]
          (T n omega (i n omega u hu) : SpatialCoordinates d → ℝ))
    (RN : ℕ → ℕ → BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRN_formula : ∀ (n N : ℕ) (omega : BilateralField d) (lam : ℝ)
        (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
        (x : SpatialCoordinates d),
      RN n N omega lam f x =
        ∫ path, (∫ t in Set.Ioi (0 : ℝ),
          Set.indicator
            {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
              (centeredCube (Homogenization.cubeCenter (Qtri n))
                (Homogenization.cubeScaleFactor (Qtri n)) (hr n) : Set (SpatialCoordinates d)) path}
            (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
          ∂(KN N (omega, x)))
    (n0 : ℕ)
    (hHolder :
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        -- Piggy-backs the `lem_as_coarse` fractional coercivity constant already computed
        -- internally below (`K1`/`hcf`), so `car_variational` gets it for free from this
        -- already-paid-for call instead of re-invoking `lem_as_coarse` at car_variational's
        -- own top level (which is expensive enough there to breach the 200000-heartbeat
        -- ceiling on the whole `car_variational` declaration; see NOTES.md).
        (∃ K1 : ℝ, 0 < K1 ∧ ∀ (N : ℕ) (v : killedSobolevGraph (centeredCube
              (Homogenization.cubeCenter (Qtri n0)) (Homogenization.cubeScaleFactor (Qtri n0))
              (hr n0))),
          cubeFractionalSqNorm hd (Homogenization.cubeCenter (Qtri n0))
              (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0) threeQuarterOrder
              (v : SobolevData (centeredCube (Homogenization.cubeCenter (Qtri n0))
                (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0))).1 ≤
            K1 * sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (Homogenization.cubeCenter (Qtri n0)) (hr n0))
              (v : SobolevData (centeredCube (Homogenization.cubeCenter (Qtri n0))
                (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0)))
              (v : SobolevData (centeredCube (Homogenization.cubeCenter (Qtri n0))
                (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0)))) ∧
        ∀ (lam0 lam1 : ℝ), 0 < lam0 → lam0 ≤ lam1 →
          ∃ Kom : ℝ, 0 < Kom ∧ ∀ (N : ℕ) (lam : ℝ), lam0 ≤ lam → lam ≤ lam1 →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ, ‖f‖ ≤ 1 →
              (∀ x ∈ closure (centeredCube (Homogenization.cubeCenter (Qtri n0))
                  (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0) : Set (SpatialCoordinates d)),
                |RN n0 N omega lam f x| ≤ Kom) ∧
              ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter (Qtri n0))
                  (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0) : Set (SpatialCoordinates d)),
              ∀ y ∈ closure (centeredCube (Homogenization.cubeCenter (Qtri n0))
                  (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0) : Set (SpatialCoordinates d)),
                |RN n0 N omega lam f x - RN n0 N omega lam f y| ≤
                  Kom * dist x y ^ (1 / 4 : ℝ)) 
    (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ N omega x, Measure.map LifetimePath.ofContinuousPath (KN N (omega, x)) = L N omega x)
    (hLlocal : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      LocalDiffusion (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (L N omega))
    (deltaGrowth : ℝ) (hMdeltaGrowth : M.delta ≤ deltaGrowth)
    (hGrowth_all : ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ deltaGrowth →
      ∃ mu : BilateralField d → Measure (SpatialCoordinates d),
        Measurable mu ∧
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          MeasuresConvergeLocally (fun N ↦ weightedChaosCutoff M H N omega) (mu omega) ∧
          IsLocallyFiniteMeasure (mu omega) ∧
          (mu omega).IsOpenPosMeasure ∧ NullSingletonClass (mu omega) ∧
          (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
            mu omega (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) = 0)) ∧
        ∀ (R : Set (SpatialCoordinates d)), Bornology.IsBounded R →
          ∃ Kmu : BilateralField d → ℝ,
            MemLp Kmu (↑(16 * d * (d + 2) + 1) : ℝ≥0∞) (chaosSampleLaw M).toMeasure ∧
            ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
              0 ≤ Kmu omega ∧
              (∀ N x, x ∈ R → ∀ r, 0 < r → r ≤ 1 →
                weightedChaosCutoff M H N omega (Metric.ball x r) ≤
                  ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - 1 / (16 * ((d : ℝ) + 2))))) ∧
              (∀ x, x ∈ R → ∀ r, 0 < r → r ≤ 1 →
                mu omega (Metric.ball x r) ≤
                  ENNReal.ofReal (Kmu omega * r ^ ((d : ℝ) - 1 / (16 * ((d : ℝ) + 2)))))) :
      let Q0 : Opens (SpatialCoordinates d) :=
        centeredCube (Homogenization.cubeCenter (Qtri n0))
          (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0)
      let mu0 : BilateralField d → Measure (SpatialCoordinates d) :=
        fun omega => (muFull omega).restrict (closure (Q0 : Set (SpatialCoordinates d)))
      let Elim0 : BilateralField d → DomainL2 Q0 → ℝ≥0∞ :=
        fun omega u => (limitFormEnergy (G n0 omega) u).toENNReal
      let Func0 : BilateralField d → ℝ →
          BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          DomainL2 Q0 → ℝ :=
        fun omega lam f u =>
          (Elim0 omega u).toReal +
            lam * (∫ x, J n0 omega u x ^ 2 ∂(mu0 omega)) -
            2 * (∫ x, f x * J n0 omega u x ∂(mu0 omega))
      ∃ Rn : BilateralField d → ℝ →
          BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          SpatialCoordinates d → ℝ,
        (∀ (lam : ℝ), 0 < lam →
          ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
            Measurable (fun p : BilateralField d × SpatialCoordinates d =>
              Rn p.1 lam f p.2)) ∧
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          (∀ (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
              ContinuousOn (Rn omega lam f) (closure (Q0 : Set (SpatialCoordinates d))) ∧
              ∀ x ∈ frontier (Q0 : Set (SpatialCoordinates d)),
                Rn omega lam f x = 0) ∧
          (∀ (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
              ∀ delta : ℝ, 0 < delta → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
                ∀ x ∈ closure (Q0 : Set (SpatialCoordinates d)),
                  |RN n0 N omega lam f x - Rn omega lam f x| < delta) ∧
          (∀ (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
              ∃ ustar : DomainL2 Q0,
                Elim0 omega ustar ≠ ⊤ ∧
                (Rn omega lam f) =ᵐ[volume.restrict (Q0 : Set (SpatialCoordinates d))]
                  (ustar : SpatialCoordinates d → ℝ) ∧
                (∀ v : DomainL2 Q0,
                  Elim0 omega v ≠ ⊤ → Func0 omega lam f ustar ≤ Func0 omega lam f v) ∧
                (∀ v : DomainL2 Q0,
                  Elim0 omega v ≠ ⊤ →
                  (∀ w : DomainL2 Q0,
                    Elim0 omega w ≠ ⊤ → Func0 omega lam f v ≤ Func0 omega lam f w) →
                  v = ustar)))  := by
    let Q0 : Opens (SpatialCoordinates d) :=
      centeredCube (Homogenization.cubeCenter (Qtri n0))
        (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0)
    let mu0 : BilateralField d → Measure (SpatialCoordinates d) :=
      fun omega => (muFull omega).restrict (closure (Q0 : Set (SpatialCoordinates d)))
    let Elim0 : BilateralField d → DomainL2 Q0 → ℝ≥0∞ :=
      fun omega u => (limitFormEnergy (G n0 omega) u).toENNReal
    let Func0 : BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → DomainL2 Q0 → ℝ :=
      fun omega lam f u =>
        (Elim0 omega u).toReal +
            lam * (∫ x, J n0 omega u x ^ 2 ∂(mu0 omega)) -
            2 * (∫ x, f x * J n0 omega u x ∂(mu0 omega))
    let epsilonGrowth : ℝ := 1 / (16 * ((d : ℝ) + 2))
    let Region : Set (SpatialCoordinates d) :=
      Metric.ball (Homogenization.cubeCenter (Qtri n0))
        (Homogenization.cubeScaleFactor (Qtri n0) / 2 + 1)
    have hRegion := aux_car_variational_hol_cube_cutoff_holder_w_hregion
      (Qtri n0) (hr n0)
    obtain ⟨muChaos, hMuChaosMeas, hRegChaos, hGrowth⟩ := hGrowth_all M H hHI hMdeltaGrowth
    have hGrowthR := hGrowth Region hRegion.1
    obtain ⟨Kmu, hKmu0, hKmuBound⟩ := hGrowthR
    have hgrowthMuFull : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ K : ℝ, 0 ≤ K ∧
        ∀ x ∈ Region, ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
          muFull omega (Metric.ball x rr) ≤ ENNReal.ofReal (K * rr ^ ((d : ℝ) - epsilonGrowth)) ∧
            ∀ N, cutoffSpeedMeasure M H omega N (Metric.ball x rr) ≤
              ENNReal.ofReal (K * rr ^ ((d : ℝ) - epsilonGrowth)) := by
      filter_upwards [hKmuBound, hRegChaos, hmuFull] with omega hKb hRc hmF
      have : IsLocallyFiniteMeasure (muChaos omega) := hRc.2.1
      have : (muChaos omega).IsOpenPosMeasure := hRc.2.2.1
      exact ⟨Kmu omega, hKb.1,
        aux_car_variational_growth_muFull_bridge M H omega epsilonGrowth Region (muFull omega)
          (muChaos omega) hmF.1 hRc.1 (Kmu omega) hKb.1 hKb.2⟩
    clear hGrowth hKmuBound hRegChaos hMuChaosMeas muChaos Kmu hKmu0
      hGrowth_all hMdeltaGrowth deltaGrowth
    have hHolderAll := aux_car_variational_holder_all Qtri hr M KN RN hRN_formula n0
      (hHolder.mono fun _ h => h.2)
    have hstart := aux_car_variational_path_start M H PN KN hin
    have hzeroOutside := aux_car_variational_RN_zero_outside M Qtri hr KN
      hstart RN hRN_formula
    have hRNzero : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (lam : ℝ), 0 < lam →
          ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
            ∀ x ∈ frontier (closure (centeredCube
              (Homogenization.cubeCenter (Qtri n0))
              (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0) : Set (SpatialCoordinates d))),
              RN n0 N omega lam f x = 0 := by
      filter_upwards [hzeroOutside] with omega hω
      intro N lam hlam f x hx
      apply hω n0 N lam hlam f x
      exact disjoint_left.1 (disjoint_frontier_iff_isOpen.mpr
        (centeredCube (Homogenization.cubeCenter (Qtri n0))
          (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0)).isOpen) (
            frontier_closure_subset hx)
    have hRNbound := aux_car_variational_RN_bound M Qtri hr KN hKN RN hRN_formula
    have hKtr_ae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∃ Ktr : ℝ, 0 ≤ Ktr ∧
        ∀ (u : DomainL2 Q0) (hu : Elim0 omega u ≠ ⊤),
          (∫⁻ x, ENNReal.ofReal (J n0 omega u x ^ 2) ∂mu0 omega) ≤
            ENNReal.ofReal Ktr * Elim0 omega u :=
      aux_car_variational_Ktr_bound hd Sf Interp M H hHI (Qtri n0) (hr n0) (hP n0) (G n0)
        (hGtendsto.mono fun omega h f => h n0 f) (hHolder.mono fun omega h => h.1) muFull
        (Ktrace n0) (Ctrace n0) (T n0) (hT.mono fun omega h => ⟨(h n0).1, (h n0).2.1⟩)
        (hT.mono fun omega h => (h n0).2.2) (i n0) (h_i_val.mono fun omega h => h n0) (J n0)
        (hJ.mono fun omega h => h n0)
    have hepsGrowth := aux_car_variational_hol_cube_cutoff_holder_eps_choice hd
    have hepsilonIoo : epsilonGrowth ∈ Set.Ioo (0 : ℝ) 1 := by
      refine ⟨hepsGrowth.1, ?_⟩
      dsimp only [epsilonGrowth]
      apply (div_lt_one (by positivity)).2
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    have hepsilon'8 : epsilonGrowth < 1 / (8 * ((d : ℝ) + 2)) := by
      dsimp only [epsilonGrowth]
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      nlinarith
    have harg_G_ae := hGtendsto.mono fun omega h f => h n0 f
    have harg_K1_ae := hHolder.mono fun omega h => h.1
    have harg_muFull_ae := hmuFull.mono fun omega h => (⟨h.1, h.2.1 n0, h.2.2 n0⟩ :
      MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) (muFull omega) ∧
      muFull omega (frontier (centeredCube (Homogenization.cubeCenter (Qtri n0))
          (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0) : Set (SpatialCoordinates d))) = 0 ∧
      muFull omega (closure (centeredCube (Homogenization.cubeCenter (Qtri n0))
          (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0) : Set (SpatialCoordinates d))) < ⊤)
    have harg_T_ae := hT.mono fun omega h => (h n0).2.2
    have harg_KCnn_ae := hT.mono fun omega h =>
      (⟨(h n0).1, (h n0).2.1⟩ : 0 ≤ Ktrace n0 omega ∧ 0 ≤ Ctrace n0 omega)
    have harg_i_ae := h_i_val.mono fun omega h => h n0
    have harg_J_ae := hJ.mono fun omega h => h n0
    clear hGtendsto hHolder hmuFull hT h_i_val hJ
    let Rn : BilateralField d → ℝ →
        BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ :=
      fun omega lam f x => limsup (fun N => RN n0 N omega lam f x) atTop
    have hUV := aux_car_variational_hUniform_hVariational hd Sf M H hHI (Qtri n0) (hr n0) (hP n0)
      (G n0) harg_G_ae harg_K1_ae muFull harg_muFull_ae (Ktrace n0) (Ctrace n0) (T n0)
      harg_T_ae harg_KCnn_ae (i n0) harg_i_ae (J n0) harg_J_ae hKtr_ae
      KN hKN L hL hLlocal (RN n0) (hRN_formula n0) (hRNbound n0) hRNzero
      epsilonGrowth hepsilonIoo hepsilon'8 Region hRegion.2 hgrowthMuFull hHolderAll Interp
    have hUniform : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ (lam : ℝ), 0 < lam →
          ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
            ∀ delta : ℝ, 0 < delta → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
              ∀ x ∈ closure (Q0 : Set (SpatialCoordinates d)),
                |RN n0 N omega lam f x - Rn omega lam f x| < delta := by
      filter_upwards [hUV] with omega huv
      exact huv.1
    have hVariational : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ (lam : ℝ), 0 < lam →
          ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
            ∃ ustar : DomainL2 Q0,
              Elim0 omega ustar ≠ ⊤ ∧
              (Rn omega lam f) =ᵐ[volume.restrict (Q0 : Set (SpatialCoordinates d))]
                (ustar : SpatialCoordinates d → ℝ) ∧
              (∀ v : DomainL2 Q0, Elim0 omega v ≠ ⊤ →
                Func0 omega lam f ustar ≤ Func0 omega lam f v) ∧
              (∀ v : DomainL2 Q0, Elim0 omega v ≠ ⊤ →
                (∀ w : DomainL2 Q0, Elim0 omega w ≠ ⊤ →
                  Func0 omega lam f v ≤ Func0 omega lam f w) →
                v = ustar) := by
      filter_upwards [hUV] with omega huv
      exact huv.2
    clear hUV harg_G_ae harg_K1_ae harg_muFull_ae harg_T_ae harg_KCnn_ae harg_i_ae harg_J_ae
      hKtr_ae hRNzero hRNbound hgrowthMuFull hRegion Region epsilonGrowth hepsilonIoo
      hepsilon'8 L hL hLlocal hepsGrowth
    have hRNmeas : ∀ (N : ℕ) (lam : ℝ)
        (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ),
        Measurable (fun p : BilateralField d × SpatialCoordinates d =>
          RN n0 N p.1 lam f p.2) := by
      intro N lam f
      have heq : (fun p : BilateralField d × SpatialCoordinates d =>
          RN n0 N p.1 lam f p.2) =
          (fun p : BilateralField d × SpatialCoordinates d =>
            ∫ path, (∫ t in Set.Ioi (0 : ℝ),
              Set.indicator
                {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                  (centeredCube (Homogenization.cubeCenter (Qtri n0))
                    (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0) :
                      Set (SpatialCoordinates d)) path}
                (fun s : ℝ => Real.exp (-lam * s) * f
                  (path (Real.toNNReal s))) t) ∂(KN N p)) := by
        funext p
        rw [hRN_formula n0 N p.1 lam f p.2]
      rw [heq]
      exact aux_car_variational_occupation_measurable KN N (hKN N)
        (centeredCube (Homogenization.cubeCenter (Qtri n0))
          (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0)) lam f
    have hRnMeas : ∀ (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        Measurable (fun p : BilateralField d × SpatialCoordinates d =>
          Rn p.1 lam f p.2) := by
      intro lam hlam f
      dsimp [Rn]
      apply Measurable.limsup
      intro N
      exact hRNmeas N lam f
    have hcontAE := aux_car_variational_RN_continuous Qtri hr RN n0 hHolderAll
    clear hP
    clear hin Ktrace
    clear PN Ctrace hstart i
    clear T hHI hHolderAll
    clear Sf Interp KN hKN hRN_formula
    have hRemaining := aux_car_variational_hRemaining_final M Q0 (Elim0)
      (Func0) (RN n0) Rn (fun omega lam f x => rfl) (hzeroOutside.mono fun omega h => h n0)
      hcontAE hUniform hVariational
    refine ⟨Rn, hRnMeas, ?_⟩
    simpa only [Q0, mu0, Elim0, Func0] using hRemaining


 

theorem car_variational
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc)
    (Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
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
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
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
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M) (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d M)
        (It : _root_.SubdiffusiveProcess.Paper.in_iteration d M Jc Sreg), M.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
      ∀ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)),
        (∀ N, IsMarkovKernel (KN N)) → in_crossing M H PN KN →
        aux_cutoff_lifetime_package_LocalInput M H KN →
      ∀ (Qtri : ℕ → Homogenization.TriadicCube d)
        (hr : ∀ n : ℕ, 0 < Homogenization.cubeScaleFactor (Qtri n)),
      let Qn : ℕ → Opens (SpatialCoordinates d) :=
        fun n => centeredCube (Homogenization.cubeCenter (Qtri n))
          (Homogenization.cubeScaleFactor (Qtri n)) (hr n);
      ∀ (hP : ∀ n : ℕ, ∃ K : ℝ≥0,
          ∀ v : killedSobolevGraph (Qn n),
            ‖(v : SobolevData (Qn n)).1‖ ≤
              K * ‖subspaceGradient (killedSobolevGraph (Qn n)) v‖),
      ∀ (G : (n : ℕ) → BilateralField d →
          (DomainL2 (Qn n) →L[ℝ] DomainL2 (Qn n))),
        (∀ n : ℕ, Measurable (G n)) →
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ (n : ℕ) (f : DomainL2 (Qn n)),
          Tendsto
            (fun N : ℕ =>
              (responseSolution (killedResponseSpace (Ω := Qn n) (hP n))
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (Homogenization.cubeCenter (Qtri n)) (hr n))
                  ((sobolevVolumeLoad f).comp
                    (killedResponseSpace (Ω := Qn n) (hP n)).space.subtypeL)).val.1)
            atTop (𝓝 (G n omega f))) →
      ∀ (muFull : BilateralField d → Measure (SpatialCoordinates d)),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) (muFull omega) ∧
          (∀ n : ℕ, muFull omega (frontier (Qn n : Set (SpatialCoordinates d))) = 0) ∧
          (∀ n : ℕ, muFull omega (closure (Qn n : Set (SpatialCoordinates d))) < ⊤)) →
      let mu : ℕ → BilateralField d → Measure (SpatialCoordinates d) :=
        fun n omega =>
          (muFull omega).restrict (closure (Qn n : Set (SpatialCoordinates d)));
      ∀ (T : (n : ℕ) → (omega : BilateralField d) →
          CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter (Qtri n))
            (Homogenization.cubeScaleFactor (Qtri n)) (hr n) halfFractionalOrder →
          Lp ℝ 2 (mu n omega)),
      ∀ (Ktrace Ctrace : ℕ → BilateralField d → ℝ),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ n : ℕ, 0 ≤ Ktrace n omega ∧ 0 ≤ Ctrace n omega ∧
            MeasureTraceCharacterization hd (Qtri n) (hr n) (mu n omega)
              (Ktrace n omega) (Ctrace n omega) (T n omega)) →
      ∀ (i : (n : ℕ) → (omega : BilateralField d) → (u : DomainL2 (Qn n)) →
          (limitFormEnergy (G n omega) u).toENNReal ≠ ⊤ →
          CubeFractionalL2 (k := 1) hd (Homogenization.cubeCenter (Qtri n))
            (Homogenization.cubeScaleFactor (Qtri n)) (hr n) halfFractionalOrder),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (n : ℕ) (u : DomainL2 (Qn n))
            (hu : (limitFormEnergy (G n omega) u).toENNReal ≠ ⊤),
            (i n omega u hu).val 0 = u) →
      ∀ (J : (n : ℕ) → BilateralField d → DomainL2 (Qn n) →
          SpatialCoordinates d → ℝ),
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (n : ℕ) (u : DomainL2 (Qn n))
            (hu : (limitFormEnergy (G n omega) u).toENNReal ≠ ⊤),
            (J n omega u) =ᵐ[mu n omega]
              (T n omega (i n omega u hu) : SpatialCoordinates d → ℝ)) →
      ∀ (RN : ℕ → ℕ → BilateralField d → ℝ →
          BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          SpatialCoordinates d → ℝ),
        (∀ (n N : ℕ) (omega : BilateralField d) (lam : ℝ)
            (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
            (x : SpatialCoordinates d),
          RN n N omega lam f x =
            ∫ path, (∫ t in Set.Ioi (0 : ℝ),
              Set.indicator
                {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
                  (Qn n : Set (SpatialCoordinates d)) path}
                (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
              ∂(KN N (omega, x))) →
      let Elim : (n : ℕ) → BilateralField d → DomainL2 (Qn n) → ℝ≥0∞ :=
        fun n omega u => (limitFormEnergy (G n omega) u).toENNReal;
      let Func : (n : ℕ) → BilateralField d → ℝ →
          BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          DomainL2 (Qn n) → ℝ :=
        fun n omega lam f u =>
          (Elim n omega u).toReal +
            lam * (∫ x, J n omega u x ^ 2 ∂(mu n omega)) -
            2 * (∫ x, f x * J n omega u x ∂(mu n omega));
      ∀ n0 : ℕ,
      ∃ Rn : BilateralField d → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
          SpatialCoordinates d → ℝ,
        (∀ (lam : ℝ), 0 < lam →
          ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
            Measurable (fun p : BilateralField d × SpatialCoordinates d => Rn p.1 lam f p.2)) ∧
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          (∀ (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
              ContinuousOn (Rn omega lam f)
                (closure (centeredCube (Homogenization.cubeCenter (Qtri n0))
                  (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0) : Set (SpatialCoordinates d))) ∧
              ∀ x ∈ frontier (centeredCube (Homogenization.cubeCenter (Qtri n0))
                  (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0) : Set (SpatialCoordinates d)),
                Rn omega lam f x = 0) ∧
          (∀ (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
              ∀ delta : ℝ, 0 < delta → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
                ∀ x ∈ closure (centeredCube (Homogenization.cubeCenter (Qtri n0))
                    (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0) : Set (SpatialCoordinates d)),
                  |RN n0 N omega lam f x - Rn omega lam f x| < delta) ∧
          (∀ (lam : ℝ), 0 < lam →
            ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
              ∃ ustar : DomainL2 (centeredCube (Homogenization.cubeCenter (Qtri n0))
                  (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0)),
                Elim n0 omega ustar ≠ ⊤ ∧
                (Rn omega lam f) =ᵐ[volume.restrict (centeredCube (Homogenization.cubeCenter (Qtri n0))
                    (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0) : Set (SpatialCoordinates d))]
                  (ustar : SpatialCoordinates d → ℝ) ∧
                (∀ v : DomainL2 (centeredCube (Homogenization.cubeCenter (Qtri n0))
                    (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0)),
                  Elim n0 omega v ≠ ⊤ → Func n0 omega lam f ustar ≤ Func n0 omega lam f v) ∧
                (∀ v : DomainL2 (centeredCube (Homogenization.cubeCenter (Qtri n0))
                    (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0)),
                  Elim n0 omega v ≠ ⊤ →
                  (∀ w : DomainL2 (centeredCube (Homogenization.cubeCenter (Qtri n0))
                      (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0)),
                    Elim n0 omega w ≠ ⊤ → Func n0 omega lam f v ≤ Func n0 omega lam f w) →
                  v = ustar))) := by
  classical
  have hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality :=
    aux_lem_band_rcJ_hES
  
  -- identical binder text to `cor_as_resolvent`).
  have hLim := limiting_local_energy d hd Jc Pc Xc Sf W Cp D hES Step Dbase
    Interp BD BDQ hcontract
  obtain ⟨deltaLim, hdeltaLim, hLim_all⟩ := hLim
  -- The cutoff transfer (HCUT) and common uniform-density event (HUNIF) inputs of
  -- `limiting_local_energy` are supplied by the countable-exhaustion lemmas below
  -- (copied from `cor_as_resolvent`'s proved `hcut_supply`/`hunif_supply`).
  obtain ⟨deltaCut, hdeltaCut, hCut_all⟩ :=
    aux_car_variational_cut_hcut_supply hd Jc Pc Xc W Cp D Sf Step Dbase Interp
  obtain ⟨deltaUnif, hdeltaUnif, hUnif_all⟩ :=
    aux_car_variational_cut_hunif_supply hd Jc Pc Xc W Cp D Sf Step Dbase Interp
  obtain ⟨deltaHol, hdeltaHol, hHol_all⟩ :=
    aux_car_variational_hol_cube_cutoff_holder hd Jc Pc Xc Sf W Cp D Interp Step Dbase
  let epsilonGrowth : ℝ := 1 / (16 * ((d : ℝ) + 2))
  have hepsGrowth := aux_car_variational_hol_cube_cutoff_holder_eps_choice hd
  have hGrowthSrc := prop_chaos_growth hd epsilonGrowth
    ⟨hepsGrowth.1, by
      dsimp [epsilonGrowth]
      apply (div_lt_one (by positivity)).2
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith⟩
    (16 * d * (d + 2) + 1) (aux_car_variational_hol_cube_cutoff_holder_p_choice hd)
  rcases hGrowthSrc with ⟨deltaGrowth, hdeltaGrowth, hGrowth_all⟩
  have hdelta_outer : 0 < min (min (min (min 1 deltaLim) deltaHol) deltaGrowth)
      (min deltaCut deltaUnif) := by
    exact lt_min (lt_min (lt_min (lt_min (by norm_num) hdeltaLim) hdeltaHol) hdeltaGrowth)
      (lt_min hdeltaCut hdeltaUnif)
  refine ⟨min (min (min (min 1 deltaLim) deltaHol) deltaGrowth) (min deltaCut deltaUnif),
    hdelta_outer, ?_⟩
  intro M Rm Sreg It hMdelta H hHI PN KN hKN hin hinput Qtri hr
  dsimp
  intro hP G hGmeas hGtendsto muFull hmuFull T Ktrace Ctrace hT i h_i_val J hJ RN hRN_formula n0
  have hLpackage := aux_cutoff_lifetime_package_local M H KN hinput
  obtain ⟨L, hL, hLlocal, hLstrong⟩ := hLpackage
  have hMdeltaLim : M.delta ≤ min 1 deltaLim := hMdelta.trans
    ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hMdeltaHol : M.delta ≤ deltaHol :=
    hMdelta.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hMdeltaGrowth : M.delta ≤ deltaGrowth :=
    hMdelta.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hMdeltaCut : M.delta ≤ deltaCut :=
    hMdelta.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hMdeltaUnif : M.delta ≤ deltaUnif :=
    hMdelta.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hHolder := hHol_all M Rm Sreg It hMdeltaHol H hHI PN KN hKN hin hinput
    Qtri hr RN hRN_formula n0
  have hHCUT : aux_limiting_local_energy_HCUT_prop M H :=
    hCut_all M Rm Sreg It H hHI hMdeltaCut
  have hHUNIF : aux_limiting_local_energy_HUNIF_prop M H hHI :=
    hUnif_all M Rm Sreg It H hHI hMdeltaUnif
  have hLimitAll := hLim_all M Rm Sreg It H hHI hMdeltaLim hHCUT hHUNIF
  have hLimitN0 := hLimitAll
    (Homogenization.cubeCenter (Qtri n0))
    (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0)
    ⟨(Qtri n0).scale, rfl⟩ (hP n0)
  obtain ⟨G0, hG0meas, hG0event⟩ := hLimitN0
  have hG0eq : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      G0 omega = G n0 omega := by
    refine mem_of_superset (inter_mem hG0event.1 hGtendsto) ?_
    intro omega hpair
    apply aux_car_variational_operator_eq
      (S := killedResponseSpace (Ω := centeredCube
        (Homogenization.cubeCenter (Qtri n0))
        (Homogenization.cubeScaleFactor (Qtri n0)) (hr n0)) (hP n0))
      (a := fun N => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
        (Homogenization.cubeCenter (Qtri n0)) (hr n0))
    · exact hpair.1.1
    · exact hpair.2 n0
  have hG0energy_eq : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ u, limitFormEnergy (G0 omega) u = limitFormEnergy (G n0 omega) u := by
    exact hG0eq.mono (fun omega hω u => by rw [hω])
  clear hHCUT hHUNIF hLimitAll G0 hG0meas hG0event hG0eq hG0energy_eq
    hMdeltaLim hMdeltaHol hMdeltaCut hMdeltaUnif
    Jc Pc Xc W Cp D Step Dbase BD BDQ hcontract hES hLim_all
    deltaLim hdeltaLim deltaCut hdeltaCut hCut_all deltaUnif hdeltaUnif hUnif_all
    deltaHol hdeltaHol hHol_all hdelta_outer Rm Sreg It hMdelta
  have hFixedCube := aux_car_variational_hFixedCube_glue hd Sf Interp M H hHI PN KN hKN hin
    Qtri hr hP G hGtendsto muFull hmuFull T Ktrace Ctrace hT i h_i_val J hJ RN hRN_formula n0
    hHolder L hL hLlocal deltaGrowth hMdeltaGrowth hGrowth_all
  exact hFixedCube

end SubdiffusiveProcess.Paper
