import SubdiffusiveProcess.Paper.prop_limit_properties_cutoff_symmetry
import SubdiffusiveProcess.Paper.in_crossing
import SubdiffusiveProcess.Paper.in_killed_energy
import SubdiffusiveProcess.Paper.killed_generator_normalization
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Main.CutoffSpeedMeasure
import SubdiffusiveProcess.Lane4.Carriers
import MarkovProcess.Path.ExitTime
import MarkovProcess.Path.ExitTimeShift
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import MarkovProcess.Restart.RationalRestart
import MarkovProcess.Restart.RationalRestrictedRestart
import MarkovProcess.Restart.ConditionalMarkov
import SubdiffusiveProcess.Lane1.TimeMarginal
import MarkovProcess.Path.Exhaustion
import MarkovProcess.Path.StoppingTimeDyadicCeiling
import MarkovProcess.Path.RandomShiftMeasurability
import SubdiffusiveProcess.Lane2.CellDirichlet
import SubdiffusiveProcess.Lane2.NativeBridge
import Homogenization.Sobolev.Truncation.MatchedTrace
import SubdiffusiveProcess.Probability.Diffusion.Packet452MollifiedGraph
import SubdiffusiveProcess.Probability.Diffusion.Packet452L2Bookkeeping
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.H10Density
import SubdiffusiveProcess.Sobolev.NativeH10
import SubdiffusiveProcess.Lane4.Bridge
import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
import Homogenization.Sobolev.Foundations.Cutoff.OpenSet
import SubdiffusiveProcess.Main.NativeInfraredLimit
import SubdiffusiveProcess.Probability.NativeCommonScaleLaw


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators

namespace Paper

section KbDefs

open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators

/-- The stopped discounted occupation integral of `hR`, for a path kernel on the spatial
coordinates. -/
noncomputable def aux_fsrkb_killedRes {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (U : Set (SpatialCoordinates d)) (lam : ℝ) (f : SpatialCoordinates d → ℝ)
    (x : SpatialCoordinates d) : ℝ :=
  ∫ path, (∫ t in Set.Ioi (0 : ℝ),
      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
        (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t) ∂(K x)

/-- The weighted-divergence generator of `hL`. -/
noncomputable def aux_fsrkb_gen {d : ℕ} (A rho : SpatialCoordinates d → ℝ)
    (phi : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d) : ℝ :=
  (rho x)⁻¹ * ∑ i : Fin d,
    (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x) (Pi.single i 1)

/-- The stopped Dynkin identity of `hstop` for one test function, one kernel, one open set. -/
def aux_fsrkb_StoppedDynkin {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (U : Set (SpatialCoordinates d)) (phi g : SpatialCoordinates d → ℝ) : Prop :=
  ∀ (x : SpatialCoordinates d) (t : ℝ≥0),
    ∫ path,
      (phi (path (ContinuousPath.exitTimeTrunc U t path)) - phi x -
        ∫ s in Set.Icc (0 : ℝ) ((ContinuousPath.exitTimeTrunc U t path) : ℝ),
          g (path (Real.toNNReal s))) ∂(K x) = 0

/-- The frozen weak equation, for a fixed environment and cutoff. -/
def aux_fsrkb_WeakEq {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (lam : ℝ) (f : SpatialCoordinates d → ℝ)
    (u : killedSobolevGraph (centeredCube z r hr)) : Prop :=
  ∀ v : killedSobolevGraph (centeredCube z r hr),
    sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr)
        (u : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr)) =
      ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        (f x - lam * ((u : SobolevData (centeredCube z r hr)).1) x) *
          ((v : SobolevData (centeredCube z r hr)).1) x ∂(cutoffSpeedMeasure M H omega N)

/-- Bounded measurable sources. -/
def aux_fsrkb_BddMeas {d : ℕ} (f : SpatialCoordinates d → ℝ) : Prop :=
  Measurable f ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |f x| ≤ B

/-- The finite-dimensional attachment of a path kernel to a semigroup (third clause of
`in_crossing`, at a fixed environment and cutoff). -/
def aux_fsrkb_Fdd {d : ℕ} (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) : Prop :=
  ∀ (I : Finset ℝ≥0) (x : SpatialCoordinates d),
    (K x).map (ContinuousPath.finsetEvaluation I) = SubMarkovKernelSemigroup.finiteSetKernel P I x

end KbDefs

section KbLinear

open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

variable {d : ℕ}

/-- The inner (pathwise) discounted occupation integral. -/
noncomputable def aux_fsrkb_occ (U : Set (SpatialCoordinates d)) (lam : ℝ)
    (f : SpatialCoordinates d → ℝ) (path : DiffusionPath d) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ),
    Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
      (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t

theorem aux_fsrkb_killedRes_eq_occ (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (U : Set (SpatialCoordinates d)) (lam : ℝ) (f : SpatialCoordinates d → ℝ)
    (x : SpatialCoordinates d) :
    aux_fsrkb_killedRes K U lam f x = ∫ path, aux_fsrkb_occ U lam f path ∂(K x) := rfl

theorem aux_fsrkb_lin_eval_measurable :
    Measurable (fun p : DiffusionPath d × ℝ => p.1 (Real.toNNReal p.2)) := by
  have hc : Continuous (fun p : DiffusionPath d × ℝ => p.1 (Real.toNNReal p.2)) := by
    have h1 : Continuous (fun p : DiffusionPath d × ℝ => (p.1, Real.toNNReal p.2)) :=
      continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd)
    exact continuous_eval.comp h1
  exact hc.measurable

theorem aux_fsrkb_lin_joint_measurable (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (lam : ℝ) (f : SpatialCoordinates d → ℝ) (hf : Measurable f) :
    Measurable (fun p : DiffusionPath d × ℝ =>
      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U p.1}
        (fun s => Real.exp (-lam * s) * f (p.1 (Real.toNNReal s))) p.2) := by
  have hset : MeasurableSet {p : DiffusionPath d × ℝ |
      ENNReal.ofReal p.2 < ContinuousPath.exitTime U p.1} :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd)
      ((ContinuousPath.measurable_exitTime U hU).comp measurable_fst)
  have hval : Measurable (fun p : DiffusionPath d × ℝ =>
      Real.exp (-lam * p.2) * f (p.1 (Real.toNNReal p.2))) :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_snd)).mul
      (hf.comp aux_fsrkb_lin_eval_measurable)
  have heq : (fun p : DiffusionPath d × ℝ =>
      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U p.1}
        (fun s => Real.exp (-lam * s) * f (p.1 (Real.toNNReal s))) p.2) =
      Set.indicator {p : DiffusionPath d × ℝ |
        ENNReal.ofReal p.2 < ContinuousPath.exitTime U p.1}
        (fun p => Real.exp (-lam * p.2) * f (p.1 (Real.toNNReal p.2))) := by
    funext p
    by_cases hp : ENNReal.ofReal p.2 < ContinuousPath.exitTime U p.1
    · rw [Set.indicator_of_mem (show p.2 ∈ {s : ℝ | ENNReal.ofReal s <
          ContinuousPath.exitTime U p.1} from hp),
        Set.indicator_of_mem (show p ∈ {p : DiffusionPath d × ℝ |
          ENNReal.ofReal p.2 < ContinuousPath.exitTime U p.1} from hp)]
    · rw [Set.indicator_of_notMem (show p.2 ∉ {s : ℝ | ENNReal.ofReal s <
          ContinuousPath.exitTime U p.1} from hp),
        Set.indicator_of_notMem (show p ∉ {p : DiffusionPath d × ℝ |
          ENNReal.ofReal p.2 < ContinuousPath.exitTime U p.1} from hp)]
  rw [heq]
  exact hval.indicator hset

theorem aux_fsrkb_occ_measurable (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (lam : ℝ) (f : SpatialCoordinates d → ℝ) (hf : Measurable f) :
    Measurable (aux_fsrkb_occ U lam f) := by
  have h := (aux_fsrkb_lin_joint_measurable U hU lam f hf).stronglyMeasurable
  exact (h.integral_prod_right' (ν := volume.restrict (Set.Ioi (0 : ℝ)))).measurable

theorem aux_fsrkb_lin_expBound_integrable (lam : ℝ) (hlam : 0 < lam) (B : ℝ) :
    IntegrableOn (fun t : ℝ => B * Real.exp (-lam * t)) (Set.Ioi 0) := by
  have h := integrableOn_exp_mul_Ioi (a := -lam) (by linarith) 0
  exact h.const_mul B

theorem aux_fsrkb_lin_expBound_integral (lam : ℝ) (hlam : 0 < lam) (B : ℝ) :
    ∫ t in Set.Ioi (0 : ℝ), B * Real.exp (-lam * t) = B / lam := by
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -lam < 0) 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp

theorem aux_fsrkb_lin_indicator_abs_le (U : Set (SpatialCoordinates d)) (lam : ℝ)
    (f : SpatialCoordinates d → ℝ) (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x, |f x| ≤ B)
    (path : DiffusionPath d) (t : ℝ) :
    ‖Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
        (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t‖ ≤
      B * Real.exp (-lam * t) := by
  by_cases ht : t ∈ {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
  · rw [Set.indicator_of_mem ht, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
      mul_comm]
    exact mul_le_mul_of_nonneg_right (hB _) (Real.exp_pos _).le
  · rw [Set.indicator_of_notMem ht, norm_zero]
    exact mul_nonneg hB0 (Real.exp_pos _).le

theorem aux_fsrkb_occ_integrableOn (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (lam : ℝ) (hlam : 0 < lam) (f : SpatialCoordinates d → ℝ) (hf : Measurable f)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x, |f x| ≤ B) (path : DiffusionPath d) :
    IntegrableOn (fun t => Set.indicator {s : ℝ | ENNReal.ofReal s <
        ContinuousPath.exitTime U path}
      (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t) (Set.Ioi 0) := by
  refine Integrable.mono' (aux_fsrkb_lin_expBound_integrable lam hlam B) ?_
    (Filter.Eventually.of_forall fun t => aux_fsrkb_lin_indicator_abs_le U lam f B hB0 hB path t)
  have hm := (aux_fsrkb_lin_joint_measurable U hU lam f hf).comp
    (measurable_const.prodMk measurable_id : Measurable fun t : ℝ => (path, t))
  exact hm.aestronglyMeasurable

theorem aux_fsrkb_occ_abs_le (U : Set (SpatialCoordinates d)) (lam : ℝ) (hlam : 0 < lam)
    (f : SpatialCoordinates d → ℝ) (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x, |f x| ≤ B)
    (path : DiffusionPath d) :
    |aux_fsrkb_occ U lam f path| ≤ B / lam := by
  rw [← aux_fsrkb_lin_expBound_integral lam hlam B, ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le (aux_fsrkb_lin_expBound_integrable lam hlam B)
    (Filter.Eventually.of_forall fun t => aux_fsrkb_lin_indicator_abs_le U lam f B hB0 hB path t)

theorem aux_fsrkb_occ_add (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (lam : ℝ) (hlam : 0 < lam) (f g : SpatialCoordinates d → ℝ)
    (hf : aux_fsrkb_BddMeas f) (hg : aux_fsrkb_BddMeas g) (path : DiffusionPath d) :
    aux_fsrkb_occ U lam (fun y => f y + g y) path =
      aux_fsrkb_occ U lam f path + aux_fsrkb_occ U lam g path := by
  obtain ⟨hfm, Bf, hBf0, hBf⟩ := hf
  obtain ⟨hgm, Bg, hBg0, hBg⟩ := hg
  unfold aux_fsrkb_occ
  rw [← integral_add (aux_fsrkb_occ_integrableOn U hU lam hlam f hfm Bf hBf0 hBf path)
    (aux_fsrkb_occ_integrableOn U hU lam hlam g hgm Bg hBg0 hBg path)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
  · simp only [Set.indicator_of_mem ht]
    ring
  · simp only [Set.indicator_of_notMem ht, add_zero]

theorem aux_fsrkb_occ_const_mul (U : Set (SpatialCoordinates d)) (lam : ℝ) (c : ℝ)
    (f : SpatialCoordinates d → ℝ) (path : DiffusionPath d) :
    aux_fsrkb_occ U lam (fun y => c * f y) path = c * aux_fsrkb_occ U lam f path := by
  unfold aux_fsrkb_occ
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
  · simp only [Set.indicator_of_mem ht]
    ring
  · simp only [Set.indicator_of_notMem ht, mul_zero]

theorem aux_fsrkb_occ_mono (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (lam : ℝ) (hlam : 0 < lam) (f g : SpatialCoordinates d → ℝ)
    (hf : aux_fsrkb_BddMeas f) (hg : aux_fsrkb_BddMeas g) (hfg : ∀ y, f y ≤ g y)
    (path : DiffusionPath d) :
    aux_fsrkb_occ U lam f path ≤ aux_fsrkb_occ U lam g path := by
  obtain ⟨hfm, Bf, hBf0, hBf⟩ := hf
  obtain ⟨hgm, Bg, hBg0, hBg⟩ := hg
  unfold aux_fsrkb_occ
  refine setIntegral_mono (aux_fsrkb_occ_integrableOn U hU lam hlam f hfm Bf hBf0 hBf path)
    (aux_fsrkb_occ_integrableOn U hU lam hlam g hgm Bg hBg0 hBg path) (fun t => ?_)
  by_cases ht : t ∈ {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
  · simp only [Set.indicator_of_mem ht]
    exact mul_le_mul_of_nonneg_left (hfg _) (Real.exp_pos _).le
  · simp only [Set.indicator_of_notMem ht, le_refl]

theorem aux_fsrkb_occ_integrable (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    [IsMarkovKernel K] (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (lam : ℝ) (hlam : 0 < lam) (f : SpatialCoordinates d → ℝ) (hf : aux_fsrkb_BddMeas f)
    (x : SpatialCoordinates d) :
    Integrable (aux_fsrkb_occ U lam f) (K x) := by
  obtain ⟨hfm, B, hB0, hB⟩ := hf
  refine Integrable.of_bound (aux_fsrkb_occ_measurable U hU lam f hfm).aestronglyMeasurable
    (B / lam) (Filter.Eventually.of_forall fun path => ?_)
  rw [Real.norm_eq_abs]
  exact aux_fsrkb_occ_abs_le U lam hlam f B hB0 hB path

theorem aux_fsrkb_killedRes_add (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    [IsMarkovKernel K] (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (lam : ℝ) (hlam : 0 < lam) (f g : SpatialCoordinates d → ℝ)
    (hf : aux_fsrkb_BddMeas f) (hg : aux_fsrkb_BddMeas g) (x : SpatialCoordinates d) :
    aux_fsrkb_killedRes K U lam (fun y => f y + g y) x =
      aux_fsrkb_killedRes K U lam f x + aux_fsrkb_killedRes K U lam g x := by
  rw [aux_fsrkb_killedRes_eq_occ, aux_fsrkb_killedRes_eq_occ, aux_fsrkb_killedRes_eq_occ,
    ← integral_add (aux_fsrkb_occ_integrable K U hU lam hlam f hf x)
      (aux_fsrkb_occ_integrable K U hU lam hlam g hg x)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun path =>
    aux_fsrkb_occ_add U hU lam hlam f g hf hg path)

theorem aux_fsrkb_killedRes_const_mul (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (U : Set (SpatialCoordinates d)) (lam : ℝ) (c : ℝ) (f : SpatialCoordinates d → ℝ)
    (x : SpatialCoordinates d) :
    aux_fsrkb_killedRes K U lam (fun y => c * f y) x = c * aux_fsrkb_killedRes K U lam f x := by
  rw [aux_fsrkb_killedRes_eq_occ, aux_fsrkb_killedRes_eq_occ, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun path =>
    aux_fsrkb_occ_const_mul U lam c f path)

theorem aux_fsrkb_BddMeas_add {f g : SpatialCoordinates d → ℝ}
    (hf : aux_fsrkb_BddMeas f) (hg : aux_fsrkb_BddMeas g) :
    aux_fsrkb_BddMeas (fun y => f y + g y) := by
  obtain ⟨hfm, Bf, hBf0, hBf⟩ := hf
  obtain ⟨hgm, Bg, hBg0, hBg⟩ := hg
  refine ⟨hfm.add hgm, Bf + Bg, add_nonneg hBf0 hBg0, fun x => ?_⟩
  exact (abs_add_le _ _).trans (add_le_add (hBf x) (hBg x))

theorem aux_fsrkb_BddMeas_const_mul (c : ℝ) {f : SpatialCoordinates d → ℝ}
    (hf : aux_fsrkb_BddMeas f) : aux_fsrkb_BddMeas (fun y => c * f y) := by
  obtain ⟨hfm, B, hB0, hB⟩ := hf
  refine ⟨measurable_const.mul hfm, |c| * B, mul_nonneg (abs_nonneg c) hB0, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hB x) (abs_nonneg c)

theorem aux_fsrkb_BddMeas_const (c : ℝ) : aux_fsrkb_BddMeas (fun _ : SpatialCoordinates d => c) :=
  ⟨measurable_const, |c|, abs_nonneg c, fun _ => le_refl _⟩

theorem aux_fsrkb_killedRes_sub (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    [IsMarkovKernel K] (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (lam : ℝ) (hlam : 0 < lam) (f g : SpatialCoordinates d → ℝ)
    (hf : aux_fsrkb_BddMeas f) (hg : aux_fsrkb_BddMeas g) (x : SpatialCoordinates d) :
    aux_fsrkb_killedRes K U lam (fun y => f y - g y) x =
      aux_fsrkb_killedRes K U lam f x - aux_fsrkb_killedRes K U lam g x := by
  have h := aux_fsrkb_killedRes_add K U hU lam hlam f (fun y => (-1) * g y) hf
    (aux_fsrkb_BddMeas_const_mul (-1) hg) x
  rw [aux_fsrkb_killedRes_const_mul] at h
  have hfun : (fun y => f y - g y) = (fun y => f y + (-1) * g y) := by
    funext y
    ring
  rw [hfun, h]
  ring

theorem aux_fsrkb_killedRes_abs_le (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    [IsMarkovKernel K] (U : Set (SpatialCoordinates d)) (lam : ℝ) (hlam : 0 < lam)
    (f : SpatialCoordinates d → ℝ) (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x, |f x| ≤ B)
    (x : SpatialCoordinates d) :
    |aux_fsrkb_killedRes K U lam f x| ≤ B / lam := by
  rw [aux_fsrkb_killedRes_eq_occ, ← Real.norm_eq_abs]
  calc ‖∫ path, aux_fsrkb_occ U lam f path ∂(K x)‖ ≤ B / lam * (K x).real Set.univ :=
        norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun path => by
          rw [Real.norm_eq_abs]
          exact aux_fsrkb_occ_abs_le U lam hlam f B hB0 hB path)
    _ = B / lam := by simp

theorem aux_fsrkb_killedRes_mono (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    [IsMarkovKernel K] (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (lam : ℝ) (hlam : 0 < lam) (f g : SpatialCoordinates d → ℝ)
    (hf : aux_fsrkb_BddMeas f) (hg : aux_fsrkb_BddMeas g) (hfg : ∀ y, f y ≤ g y)
    (x : SpatialCoordinates d) :
    aux_fsrkb_killedRes K U lam f x ≤ aux_fsrkb_killedRes K U lam g x := by
  rw [aux_fsrkb_killedRes_eq_occ, aux_fsrkb_killedRes_eq_occ]
  exact integral_mono (aux_fsrkb_occ_integrable K U hU lam hlam f hf x)
    (aux_fsrkb_occ_integrable K U hU lam hlam g hg x)
    (fun path => aux_fsrkb_occ_mono U hU lam hlam f g hf hg hfg path)

theorem aux_fsrkb_killedRes_measurable (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (lam : ℝ)
    (f : SpatialCoordinates d → ℝ) (hf : Measurable f) :
    Measurable (fun x => aux_fsrkb_killedRes K U lam f x) := by
  have h := (aux_fsrkb_occ_measurable U hU lam f hf).stronglyMeasurable
  exact (h.integral_kernel (κ := K)).measurable

end KbLinear

section KbSpeed

open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

variable {d : ℕ}

theorem aux_fsrkb_speed_density_pos (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (x : SpatialCoordinates d) : 0 < cutoffSpeedDensity M H omega N x :=
  Real.exp_pos _

theorem aux_fsrkb_speed_density_continuous (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ) :
    Continuous (cutoffSpeedDensity M H omega N) := by
  have hpot : Continuous (cutoffPotential H omega N) := by
    unfold cutoffPotential
    fun_prop
  unfold cutoffSpeedDensity
  exact Real.continuous_exp.comp (hpot.sub continuous_const)

theorem aux_fsrkb_speed_eq (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ) :
    cutoffSpeedMeasure M H omega N =
      volume.withDensity (fun x => ENNReal.ofReal (cutoffSpeedDensity M H omega N x)) := rfl

/-- Two-sided bounds of the speed density on the closed cube. -/
theorem aux_fsrkb_speed_density_bounds (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
      c ≤ cutoffSpeedDensity M H omega N x ∧ cutoffSpeedDensity M H omega N x ≤ C := by
  have hcont := aux_fsrkb_speed_density_continuous M H omega N
  have hK : IsCompact (Metric.closedBall z (r / 2)) := isCompact_closedBall z (r / 2)
  have hne : (Metric.closedBall z (r / 2)).Nonempty :=
    ⟨z, Metric.mem_closedBall_self (by linarith)⟩
  obtain ⟨xmin, _, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  obtain ⟨xmax, _, hmax⟩ := hK.exists_isMaxOn hne hcont.continuousOn
  refine ⟨cutoffSpeedDensity M H omega N xmin, cutoffSpeedDensity M H omega N xmax,
    aux_fsrkb_speed_density_pos M H omega N xmin, aux_fsrkb_speed_density_pos M H omega N xmax,
    fun x hx => ?_⟩
  have hx' : x ∈ Metric.closedBall z (r / 2) := Metric.ball_subset_closedBall hx
  exact ⟨hmin hx', hmax hx'⟩

theorem aux_fsrkb_speed_restrict_eq (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (S : Set (SpatialCoordinates d)) (hS : MeasurableSet S) :
    (cutoffSpeedMeasure M H omega N).restrict S =
      (volume.restrict S).withDensity (fun x => ENNReal.ofReal (cutoffSpeedDensity M H omega N x)) := by
  rw [aux_fsrkb_speed_eq, restrict_withDensity hS]

theorem aux_fsrkb_speed_ac (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (S : Set (SpatialCoordinates d)) (hS : MeasurableSet S) :
    (cutoffSpeedMeasure M H omega N).restrict S ≪ volume.restrict S := by
  rw [aux_fsrkb_speed_restrict_eq M H omega N S hS]
  exact withDensity_absolutelyContinuous _ _

theorem aux_fsrkb_volume_ac_speed (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (S : Set (SpatialCoordinates d)) (hS : MeasurableSet S) :
    volume.restrict S ≪ (cutoffSpeedMeasure M H omega N).restrict S := by
  rw [aux_fsrkb_speed_restrict_eq M H omega N S hS]
  refine withDensity_absolutelyContinuous' ?_ ?_
  · exact (aux_fsrkb_speed_density_continuous M H omega N).measurable.ennreal_ofReal.aemeasurable
  · exact Filter.Eventually.of_forall fun x =>
      (ENNReal.ofReal_pos.mpr (aux_fsrkb_speed_density_pos M H omega N x)).ne'

theorem aux_fsrkb_speed_isFinite (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    IsFiniteMeasure ((cutoffSpeedMeasure M H omega N).restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  have hQm : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  obtain ⟨c, C, _, hC, hb⟩ := aux_fsrkb_speed_density_bounds M H omega N z r hr
  rw [aux_fsrkb_speed_restrict_eq M H omega N _ hQm]
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal (cutoffSpeedDensity M H omega N x)
      ≤ ∫⁻ _ in (centeredCube z r hr : Set (SpatialCoordinates d)), ENNReal.ofReal C := by
        refine setLIntegral_mono measurable_const fun x hx => ?_
        exact ENNReal.ofReal_le_ofReal (hb x hx).2
    _ < ⊤ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (by rw [centeredCube_volume]; exact ENNReal.ofReal_lt_top)

/-- Integrals against the speed measure are Lebesgue integrals with the density. -/
theorem aux_fsrkb_speed_integral (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (S : Set (SpatialCoordinates d)) (hS : MeasurableSet S) (F : SpatialCoordinates d → ℝ) :
    (∫ x in S, F x ∂(cutoffSpeedMeasure M H omega N)) =
      ∫ x in S, cutoffSpeedDensity M H omega N x * F x := by
  have h1 := setIntegral_withDensity_eq_setIntegral_toReal_smul
    (μ := (volume : Measure (SpatialCoordinates d)))
    (f := fun x => ENNReal.ofReal (cutoffSpeedDensity M H omega N x))
    (aux_fsrkb_speed_density_continuous M H omega N).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) F hS
  rw [aux_fsrkb_speed_eq, h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (aux_fsrkb_speed_density_pos M H omega N x).le]

/-- Bounded measurable functions are integrable against the speed measure on the cube. -/
theorem aux_fsrkb_speed_integrable_of_bdd (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (F : SpatialCoordinates d → ℝ) (hF : AEStronglyMeasurable F
      ((cutoffSpeedMeasure M H omega N).restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (B : ℝ) (hB : ∀ x, |F x| ≤ B) :
    Integrable F ((cutoffSpeedMeasure M H omega N).restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  haveI := aux_fsrkb_speed_isFinite M H omega N z r hr
  exact Integrable.of_bound hF B (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hB x)

/-- `L²(dx)` functions on the cube are `L²(μ)` (the density is bounded). -/
theorem aux_fsrkb_speed_memLp_two (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (g : SpatialCoordinates d → ℝ)
    (hg : MemLp g 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) :
    MemLp g 2 ((cutoffSpeedMeasure M H omega N).restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  have hQm : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  obtain ⟨c, C, _, hC, hb⟩ := aux_fsrkb_speed_density_bounds M H omega N z r hr
  have hle : (cutoffSpeedMeasure M H omega N).restrict
      (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
      ENNReal.ofReal C • volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    rw [aux_fsrkb_speed_restrict_eq M H omega N _ hQm]
    refine Measure.le_iff.mpr fun s hs => ?_
    rw [withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul, Measure.restrict_restrict hs]
    calc ∫⁻ x in s ∩ (centeredCube z r hr : Set (SpatialCoordinates d)),
          ENNReal.ofReal (cutoffSpeedDensity M H omega N x)
        ≤ ∫⁻ _ in s ∩ (centeredCube z r hr : Set (SpatialCoordinates d)), ENNReal.ofReal C :=
          setLIntegral_mono measurable_const fun x hx => ENNReal.ofReal_le_ofReal (hb x hx.2).2
      _ = ENNReal.ofReal C * volume (s ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) :=
          setLIntegral_const _ _
      _ = ENNReal.ofReal C * (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) s := by
          rw [Measure.restrict_apply hs]
  exact (hg.smul_measure ENNReal.ofReal_ne_top).mono_measure hle

end KbSpeed

section KbDynkin

open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

theorem aux_fsrkb_Dynkin_trunc_coe {d : ℕ} (U : Set (SpatialCoordinates d)) (T : ℝ≥0)
    (ω : DiffusionPath d) :
    ((ContinuousPath.exitTimeTrunc U T ω : ℝ≥0) : ℝ≥0∞) =
      min (ContinuousPath.exitTime U ω) (T : ℝ≥0∞) :=
  ContinuousPath.coe_exitTimeTrunc U T ω

theorem aux_fsrkb_Dynkin_trunc_eq {d : ℕ} (U : Set (SpatialCoordinates d)) (T : ℝ≥0)
    (ω : DiffusionPath d) :
    ContinuousPath.exitTimeTrunc U T ω =
      (min (ContinuousPath.exitTime U ω) (T : ℝ≥0∞)).toNNReal := by
  rw [← aux_fsrkb_Dynkin_trunc_coe, ENNReal.toNNReal_coe]

theorem aux_fsrkb_Dynkin_trunc_of_lt {d : ℕ} (U : Set (SpatialCoordinates d)) (T : ℝ≥0)
    (ω : DiffusionPath d) (h : (T : ℝ≥0∞) < ContinuousPath.exitTime U ω) :
    ContinuousPath.exitTimeTrunc U T ω = T := by
  rw [aux_fsrkb_Dynkin_trunc_eq, min_eq_right h.le, ENNReal.toNNReal_coe]

theorem aux_fsrkb_Dynkin_trunc_of_le {d : ℕ} (U : Set (SpatialCoordinates d)) (T : ℝ≥0)
    (ω : DiffusionPath d) (h : ContinuousPath.exitTime U ω ≤ (T : ℝ≥0∞)) :
    ContinuousPath.exitTimeTrunc U T ω = (ContinuousPath.exitTime U ω).toNNReal := by
  rw [aux_fsrkb_Dynkin_trunc_eq, min_eq_left h]

theorem aux_fsrkb_Dynkin_trunc_le {d : ℕ} (U : Set (SpatialCoordinates d)) (t : ℝ) (ht : 0 ≤ t)
    (ω : DiffusionPath d) :
    ((ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω : ℝ≥0) : ℝ) ≤ t := by
  have h := ContinuousPath.exitTimeTrunc_le U (Real.toNNReal t) ω
  have h' : ((ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω : ℝ≥0) : ℝ) ≤
      ((Real.toNNReal t : ℝ≥0) : ℝ) := by exact_mod_cast h
  rwa [Real.coe_toNNReal t ht] at h'

theorem aux_fsrkb_Dynkin_measurable_trunc {d : ℕ} (U : Set (SpatialCoordinates d))
    (hU : IsOpen U) :
    Measurable fun p : DiffusionPath d × ℝ =>
      ContinuousPath.exitTimeTrunc U (Real.toNNReal p.2) p.1 := by
  have heq : (fun p : DiffusionPath d × ℝ =>
      ContinuousPath.exitTimeTrunc U (Real.toNNReal p.2) p.1) =
      fun p => (min (ContinuousPath.exitTime U p.1) (ENNReal.ofReal p.2)).toNNReal :=
    funext fun p => aux_fsrkb_Dynkin_trunc_eq U _ p.1
  rw [heq]
  exact ENNReal.measurable_toNNReal.comp
    (((ContinuousPath.measurable_exitTime U hU).comp measurable_fst).min
      (ENNReal.measurable_ofReal.comp measurable_snd))

theorem aux_fsrkb_Dynkin_measurable_setIntegral {α : Type*} [MeasurableSpace α] (a : α → ℝ)
    (ha : Measurable a) (G : α → ℝ → ℝ) (hG : Measurable (Function.uncurry G)) :
    Measurable fun p => ∫ s in Set.Icc (0 : ℝ) (a p), G p s := by
  have heq : (fun p => ∫ s in Set.Icc (0 : ℝ) (a p), G p s) =
      fun p => ∫ s, (Set.Icc (0 : ℝ) (a p)).indicator (G p) s :=
    funext fun p => (integral_indicator measurableSet_Icc).symm
  rw [heq]
  have hset : MeasurableSet {q : α × ℝ | 0 ≤ q.2 ∧ q.2 ≤ a q.1} :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (ha.comp measurable_fst))
  have hF : Measurable (Function.uncurry fun p s =>
      (Set.Icc (0 : ℝ) (a p)).indicator (G p) s) := by
    have h2 : (Function.uncurry fun p s => (Set.Icc (0 : ℝ) (a p)).indicator (G p) s) =
        {q : α × ℝ | 0 ≤ q.2 ∧ q.2 ≤ a q.1}.indicator (Function.uncurry G) := by
      funext q
      rcases q with ⟨p, s⟩
      simp only [Function.uncurry_apply_pair, Set.indicator, Set.mem_setOf_eq, Set.mem_Icc]
    rw [h2]
    exact hG.indicator hset
  exact (StronglyMeasurable.integral_prod_right hF.stronglyMeasurable).measurable

/-- The product integrand: the stopped identity at horizon `t`, weighted by `λ e^{-λ t}`. -/
noncomputable def aux_fsrkb_Dynkin_H {d : ℕ} (U : Set (SpatialCoordinates d))
    (phi g : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d) (lam : ℝ)
    (ω : DiffusionPath d) (t : ℝ) : ℝ :=
  lam * Real.exp (-lam * t) *
    (phi (ω (ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω)) - phi x -
      ∫ s in Set.Icc (0 : ℝ) ((ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω : ℝ≥0) : ℝ),
        g (ω (Real.toNNReal s)))

theorem aux_fsrkb_Dynkin_measurable_H {d : ℕ} (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (phi g : SpatialCoordinates d → ℝ) (hphi : Continuous phi) (hg : Measurable g)
    (x : SpatialCoordinates d) (lam : ℝ) :
    Measurable (Function.uncurry (aux_fsrkb_Dynkin_H U phi g x lam)) := by
  have hσ := aux_fsrkb_Dynkin_measurable_trunc U hU
  have hev : Measurable fun p : DiffusionPath d × ℝ =>
      p.1 (ContinuousPath.exitTimeTrunc U (Real.toNNReal p.2) p.1) :=
    continuous_eval.measurable.comp (measurable_fst.prodMk hσ)
  have hG : Measurable (Function.uncurry fun (p : DiffusionPath d × ℝ) (s : ℝ) =>
      g (p.1 (Real.toNNReal s))) :=
    hg.comp (continuous_eval.measurable.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_real_toNNReal.comp measurable_snd)))
  have hint := aux_fsrkb_Dynkin_measurable_setIntegral
    (fun p : DiffusionPath d × ℝ =>
      ((ContinuousPath.exitTimeTrunc U (Real.toNNReal p.2) p.1 : ℝ≥0) : ℝ))
    (measurable_coe_nnreal_real.comp hσ) _ hG
  have hexp : Measurable fun p : DiffusionPath d × ℝ => lam * Real.exp (-lam * p.2) :=
    measurable_const.mul (Real.continuous_exp.measurable.comp
      (measurable_const.mul measurable_snd))
  exact hexp.mul (((hphi.measurable.comp hev).sub measurable_const).sub hint)

theorem aux_fsrkb_Dynkin_abs_setIntegral_le (G : ℝ → ℝ) (Cg : ℝ) (hG : ∀ s, |G s| ≤ Cg)
    (a : ℝ) (ha : 0 ≤ a) :
    |∫ s in Set.Icc (0 : ℝ) a, G s| ≤ Cg * a := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (0 : ℝ) a)
    (f := G) (C := Cg) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
    (fun s _ => by rw [Real.norm_eq_abs]; exact hG s)
  rw [Real.norm_eq_abs, Real.volume_real_Icc, sub_zero, max_eq_left ha] at h
  exact h

theorem aux_fsrkb_Dynkin_abs_H_le {d : ℕ} (U : Set (SpatialCoordinates d))
    (phi g : SpatialCoordinates d → ℝ) (Cphi : ℝ)
    (hphiB : ∀ y, |phi y| ≤ Cphi) (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg)
    (x : SpatialCoordinates d) (lam : ℝ) (hlam : 0 < lam) (ω : DiffusionPath d) (t : ℝ)
    (ht : 0 ≤ t) :
    |aux_fsrkb_Dynkin_H U phi g x lam ω t| ≤
      lam * Real.exp (-lam * t) * (2 * Cphi) + lam * Cg * (t * Real.exp (-lam * t)) := by
  have hCg : 0 ≤ Cg := le_trans (abs_nonneg _) (hgB x)
  have hσ := aux_fsrkb_Dynkin_trunc_le U t ht ω
  have hσ0 : (0 : ℝ) ≤ ((ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω : ℝ≥0) : ℝ) :=
    NNReal.coe_nonneg _
  have hb := aux_fsrkb_Dynkin_abs_setIntegral_le (fun s => g (ω (Real.toNNReal s))) Cg
    (fun s => hgB _) _ hσ0
  have hb' : Cg * ((ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω : ℝ≥0) : ℝ) ≤ Cg * t :=
    mul_le_mul_of_nonneg_left hσ hCg
  have ha := hphiB (ω (ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω))
  have hx := hphiB x
  have hpos : 0 ≤ lam * Real.exp (-lam * t) := mul_nonneg hlam.le (Real.exp_pos _).le
  unfold aux_fsrkb_Dynkin_H
  rw [abs_mul, abs_of_nonneg hpos]
  have hsum : |phi (ω (ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω)) - phi x -
      ∫ s in Set.Icc (0 : ℝ) ((ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω : ℝ≥0) : ℝ),
        g (ω (Real.toNNReal s))| ≤ 2 * Cphi + Cg * t := by
    refine (abs_sub _ _).trans ?_
    have h1 := abs_sub (phi (ω (ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω))) (phi x)
    linarith only [h1, ha, hx, hb, hb']
  calc lam * Real.exp (-lam * t) * |phi (ω (ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω))
        - phi x - ∫ s in Set.Icc (0 : ℝ)
          ((ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω : ℝ≥0) : ℝ),
          g (ω (Real.toNNReal s))|
      ≤ lam * Real.exp (-lam * t) * (2 * Cphi + Cg * t) := mul_le_mul_of_nonneg_left hsum hpos
    _ = lam * Real.exp (-lam * t) * (2 * Cphi) + lam * Cg * (t * Real.exp (-lam * t)) := by ring

theorem aux_fsrkb_Dynkin_integrableOn_mul_exp (lam : ℝ) (hlam : 0 < lam) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-lam * t)) (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := lam)
    (by norm_num) le_rfl hlam
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one]

theorem aux_fsrkb_Dynkin_integrableOn_exp (lam : ℝ) (hlam : 0 < lam) :
    IntegrableOn (fun t : ℝ => Real.exp (-lam * t)) (Set.Ioi 0) :=
  integrableOn_exp_mul_Ioi (by linarith only [hlam]) 0

theorem aux_fsrkb_Dynkin_integrable_H {d : ℕ} (ν : Measure (DiffusionPath d))
    [IsProbabilityMeasure ν] (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (phi g : SpatialCoordinates d → ℝ) (hphi : Continuous phi) (Cphi : ℝ)
    (hphiB : ∀ y, |phi y| ≤ Cphi) (hg : Measurable g) (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg)
    (x : SpatialCoordinates d) (lam : ℝ) (hlam : 0 < lam) :
    Integrable (Function.uncurry (aux_fsrkb_Dynkin_H U phi g x lam))
      (ν.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
  have hbound : Integrable (fun p : DiffusionPath d × ℝ =>
      lam * Real.exp (-lam * p.2) * (2 * Cphi) + lam * Cg * (p.2 * Real.exp (-lam * p.2)))
      (ν.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    have h1 : Integrable (fun t : ℝ =>
        lam * Real.exp (-lam * t) * (2 * Cphi) + lam * Cg * (t * Real.exp (-lam * t)))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (((aux_fsrkb_Dynkin_integrableOn_exp lam hlam).const_mul lam).mul_const (2 * Cphi)).add
        ((aux_fsrkb_Dynkin_integrableOn_mul_exp lam hlam).const_mul (lam * Cg))
    exact h1.comp_snd ν
  have hsnd : ∀ᵐ p ∂(ν.prod (volume.restrict (Set.Ioi (0 : ℝ)))), p.2 ∈ Set.Ioi (0 : ℝ) :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi)
  refine hbound.mono' (aux_fsrkb_Dynkin_measurable_H U hU phi g hphi hg x lam).aestronglyMeasurable
    ?_
  filter_upwards [hsnd] with p hp
  rw [Real.norm_eq_abs]
  exact aux_fsrkb_Dynkin_abs_H_le U phi g Cphi hphiB Cg hgB x lam hlam p.1 p.2 (le_of_lt hp)

theorem aux_fsrkb_Dynkin_tail (lam : ℝ) (hlam : 0 < lam) (a : ℝ) (ha : 0 ≤ a) :
    ∫ t in Set.Ioi (0 : ℝ), (Set.Ici a).indicator (fun t => lam * Real.exp (-lam * t)) t =
      Real.exp (-lam * a) := by
  rw [setIntegral_indicator measurableSet_Ici]
  have hset : (Set.Ioi (0 : ℝ) ∩ Set.Ici a : Set ℝ) =ᵐ[volume] (Set.Ioi a : Set ℝ) := by
    rcases ha.eq_or_lt with h | h
    · rw [← h, Set.inter_eq_left.mpr Set.Ioi_subset_Ici_self]
    · rw [Set.inter_eq_right.mpr (Set.Ici_subset_Ioi.mpr h)]
      exact Ioi_ae_eq_Ici.symm
  rw [setIntegral_congr_set hset, integral_const_mul,
    integral_exp_mul_Ioi (by linarith only [hlam]) a]
  field_simp

theorem aux_fsrkb_Dynkin_integral_exp (lam : ℝ) (hlam : 0 < lam) (c : ℝ) :
    ∫ t in Set.Ioi (0 : ℝ), lam * Real.exp (-lam * t) * c = c := by
  rw [integral_mul_const, integral_const_mul, integral_exp_mul_Ioi (by linarith only [hlam]) 0]
  field_simp
  simp

theorem aux_fsrkb_Dynkin_integrableOn_exp_mul (lam : ℝ) (hlam : 0 < lam) (h : ℝ → ℝ)
    (hh : Measurable h) (C : ℝ) (hC : ∀ s, |h s| ≤ C) :
    IntegrableOn (fun s => Real.exp (-lam * s) * h s) (Set.Ioi 0) := by
  refine Integrable.mono' ((aux_fsrkb_Dynkin_integrableOn_exp lam hlam).const_mul C)
    ((Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)).mul
      hh).aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.abs_exp, mul_comm]
  exact mul_le_mul_of_nonneg_right (hC s) (Real.exp_pos _).le

/-- The first piece: the stopped value, integrated against `λ e^{-λ t} dt`. -/
theorem aux_fsrkb_Dynkin_piece_one {d : ℕ} (U : Set (SpatialCoordinates d))
    (phi : SpatialCoordinates d → ℝ) (hphi : Continuous phi) (Cphi : ℝ)
    (hphiB : ∀ y, |phi y| ≤ Cphi) (lam : ℝ) (hlam : 0 < lam) (ω : DiffusionPath d) :
    ∫ t in Set.Ioi (0 : ℝ), lam * Real.exp (-lam * t) *
        phi (ω (ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω)) =
      (∫ t in Set.Ioi (0 : ℝ),
        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U ω}
          (fun s => Real.exp (-lam * s) * (lam * phi (ω (Real.toNNReal s)))) t) +
      (if ContinuousPath.exitTime U ω = ⊤ then 0 else
        Real.exp (-lam * (ContinuousPath.exitTime U ω).toReal) *
          phi (ω (ContinuousPath.exitTime U ω).toNNReal)) := by
  set τ := ContinuousPath.exitTime U ω with hτ
  have hS : MeasurableSet {s : ℝ | ENNReal.ofReal s < τ} :=
    measurableSet_lt ENNReal.measurable_ofReal measurable_const
  have hS' : MeasurableSet {s : ℝ | τ ≤ ENNReal.ofReal s} :=
    measurableSet_le measurable_const ENNReal.measurable_ofReal
  have hcont : Continuous fun s : ℝ => phi (ω (Real.toNNReal s)) :=
    hphi.comp (ω.continuous.comp continuous_real_toNNReal)
  have hi1 : IntegrableOn (Set.indicator {s : ℝ | ENNReal.ofReal s < τ}
      (fun s => Real.exp (-lam * s) * (lam * phi (ω (Real.toNNReal s))))) (Set.Ioi 0) :=
    (aux_fsrkb_Dynkin_integrableOn_exp_mul lam hlam _
      (measurable_const.mul hcont.measurable) (lam * Cphi) (fun s => by
        rw [abs_mul, abs_of_pos hlam]
        exact mul_le_mul_of_nonneg_left (hphiB _) hlam.le)).indicator hS
  have hi2 : IntegrableOn (fun t => Set.indicator {s : ℝ | τ ≤ ENNReal.ofReal s}
      (fun s => lam * Real.exp (-lam * s)) t * phi (ω τ.toNNReal)) (Set.Ioi 0) :=
    (((aux_fsrkb_Dynkin_integrableOn_exp lam hlam).const_mul lam).indicator hS').mul_const _
  have hpt : Set.EqOn (fun t => lam * Real.exp (-lam * t) *
        phi (ω (ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω)))
      (fun t => Set.indicator {s : ℝ | ENNReal.ofReal s < τ}
          (fun s => Real.exp (-lam * s) * (lam * phi (ω (Real.toNNReal s)))) t +
        Set.indicator {s : ℝ | τ ≤ ENNReal.ofReal s}
          (fun s => lam * Real.exp (-lam * s)) t * phi (ω τ.toNNReal)) (Set.Ioi 0) := by
    intro t _
    beta_reduce
    by_cases h : ENNReal.ofReal t < τ
    · have hσ := aux_fsrkb_Dynkin_trunc_of_lt U (Real.toNNReal t) ω h
      rw [Set.indicator_of_mem (show t ∈ {s : ℝ | ENNReal.ofReal s < τ} from h),
        Set.indicator_of_notMem (show t ∉ {s : ℝ | τ ≤ ENNReal.ofReal s} from not_le.mpr h), hσ]
      ring
    · have hσ := aux_fsrkb_Dynkin_trunc_of_le U (Real.toNNReal t) ω (not_lt.mp h)
      rw [Set.indicator_of_notMem (show t ∉ {s : ℝ | ENNReal.ofReal s < τ} from h),
        Set.indicator_of_mem (show t ∈ {s : ℝ | τ ≤ ENNReal.ofReal s} from not_lt.mp h), hσ, ← hτ]
      ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add hi1 hi2, integral_mul_const]
  congr 1
  by_cases htop : τ = ⊤
  · have hempty : {s : ℝ | τ ≤ ENNReal.ofReal s} = ∅ := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, htop, top_le_iff]
      exact ENNReal.ofReal_ne_top
    rw [if_pos htop, hempty, Set.indicator_empty, integral_zero, zero_mul]
  · rw [if_neg htop]
    have heq : Set.EqOn (Set.indicator {s : ℝ | τ ≤ ENNReal.ofReal s}
        (fun s => lam * Real.exp (-lam * s)))
        ((Set.Ici τ.toReal).indicator (fun s => lam * Real.exp (-lam * s))) (Set.Ioi 0) := by
      intro s hs
      have hiff : s ∈ {s : ℝ | τ ≤ ENNReal.ofReal s} ↔ s ∈ Set.Ici τ.toReal := by
        simp only [Set.mem_setOf_eq, Set.mem_Ici]
        exact ENNReal.le_ofReal_iff_toReal_le htop (le_of_lt hs)
      by_cases hm : s ∈ Set.Ici τ.toReal
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hiff.mpr hm)]
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm (hiff.mp h))]
    rw [setIntegral_congr_fun measurableSet_Ioi heq,
      aux_fsrkb_Dynkin_tail lam hlam _ ENNReal.toReal_nonneg]

theorem aux_fsrkb_Dynkin_mem_Icc_trunc {d : ℕ} (U : Set (SpatialCoordinates d))
    (ω : DiffusionPath d) (t s : ℝ) (ht : 0 ≤ t) :
    s ∈ Set.Icc (0 : ℝ) ((ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω : ℝ≥0) : ℝ) ↔
      (0 ≤ s ∧ ENNReal.ofReal s ≤ ContinuousPath.exitTime U ω) ∧ s ≤ t := by
  have hc := aux_fsrkb_Dynkin_trunc_coe U (Real.toNNReal t) ω
  constructor
  · rintro ⟨h0, hs⟩
    have h1 : ENNReal.ofReal s ≤
        ((ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top, ENNReal.coe_toReal]
      exact hs
    rw [hc] at h1
    refine ⟨⟨h0, h1.trans (min_le_left _ _)⟩, ?_⟩
    have h2 : ENNReal.ofReal s ≤ ENNReal.ofReal t := h1.trans (min_le_right _ _)
    exact (ENNReal.ofReal_le_ofReal_iff ht).mp h2
  · rintro ⟨⟨h0, hτ⟩, hst⟩
    refine ⟨h0, ?_⟩
    have h1 : ENNReal.ofReal s ≤
        ((ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω : ℝ≥0) : ℝ≥0∞) := by
      rw [hc]
      exact le_min hτ (ENNReal.ofReal_le_ofReal hst)
    rwa [ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top, ENNReal.coe_toReal] at h1

/-- The `(t, s)` integrand of the occupation term. -/
noncomputable def aux_fsrkb_Dynkin_F {d : ℕ} (U : Set (SpatialCoordinates d))
    (g : SpatialCoordinates d → ℝ) (lam : ℝ) (ω : DiffusionPath d) (t s : ℝ) : ℝ :=
  lam * Real.exp (-lam * t) *
    (Set.Icc (0 : ℝ) ((ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω : ℝ≥0) : ℝ)).indicator
      (fun s => g (ω (Real.toNNReal s))) s

theorem aux_fsrkb_Dynkin_F_eq {d : ℕ} (U : Set (SpatialCoordinates d))
    (g : SpatialCoordinates d → ℝ) (lam : ℝ) (ω : DiffusionPath d) (t s : ℝ) (ht : 0 ≤ t) :
    aux_fsrkb_Dynkin_F U g lam ω t s =
      (Set.Ici s).indicator (fun t => lam * Real.exp (-lam * t)) t *
        {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s ≤ ContinuousPath.exitTime U ω}.indicator
          (fun s => g (ω (Real.toNNReal s))) s := by
  have hiff := aux_fsrkb_Dynkin_mem_Icc_trunc U ω t s ht
  unfold aux_fsrkb_Dynkin_F
  by_cases hs : s ∈ {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s ≤ ContinuousPath.exitTime U ω}
  · rw [Set.indicator_of_mem hs]
    by_cases hst : s ≤ t
    · rw [Set.indicator_of_mem (hiff.mpr ⟨hs, hst⟩),
        Set.indicator_of_mem (show t ∈ Set.Ici s from hst)]
    · rw [Set.indicator_of_notMem (fun h => hst (hiff.mp h).2),
        Set.indicator_of_notMem (show t ∉ Set.Ici s from hst)]
      simp
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem (fun h => hs (hiff.mp h).1)]
    simp

theorem aux_fsrkb_Dynkin_F_inner {d : ℕ} (U : Set (SpatialCoordinates d))
    (g : SpatialCoordinates d → ℝ) (lam : ℝ) (hlam : 0 < lam) (ω : DiffusionPath d) (s : ℝ) :
    ∫ t in Set.Ioi (0 : ℝ), aux_fsrkb_Dynkin_F U g lam ω t s =
      {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s ≤ ContinuousPath.exitTime U ω}.indicator
        (fun s => Real.exp (-lam * s) * g (ω (Real.toNNReal s))) s := by
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun t ht => aux_fsrkb_Dynkin_F_eq U g lam ω t s (le_of_lt ht)), integral_mul_const]
  by_cases hs : s ∈ {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s ≤ ContinuousPath.exitTime U ω}
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, aux_fsrkb_Dynkin_tail lam hlam s hs.1]
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, mul_zero]

theorem aux_fsrkb_Dynkin_measurable_F {d : ℕ} (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (g : SpatialCoordinates d → ℝ) (hg : Measurable g) (lam : ℝ) (ω : DiffusionPath d) :
    Measurable (Function.uncurry (aux_fsrkb_Dynkin_F U g lam ω)) := by
  have hσt : Measurable fun t : ℝ =>
      ((ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω : ℝ≥0) : ℝ) :=
    measurable_coe_nnreal_real.comp
      ((aux_fsrkb_Dynkin_measurable_trunc U hU).comp (measurable_const.prodMk measurable_id))
  have hset : MeasurableSet {p : ℝ × ℝ | 0 ≤ p.2 ∧
      p.2 ≤ ((ContinuousPath.exitTimeTrunc U (Real.toNNReal p.1) ω : ℝ≥0) : ℝ)} :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (hσt.comp measurable_fst))
  have hval : Measurable fun p : ℝ × ℝ => g (ω (Real.toNNReal p.2)) :=
    hg.comp (ω.continuous.measurable.comp (measurable_real_toNNReal.comp measurable_snd))
  have heq : Function.uncurry (aux_fsrkb_Dynkin_F U g lam ω) =
      fun p : ℝ × ℝ => lam * Real.exp (-lam * p.1) *
        {p : ℝ × ℝ | 0 ≤ p.2 ∧
          p.2 ≤ ((ContinuousPath.exitTimeTrunc U (Real.toNNReal p.1) ω : ℝ≥0) : ℝ)}.indicator
          (fun p : ℝ × ℝ => g (ω (Real.toNNReal p.2))) p := by
    funext p
    rcases p with ⟨t, s⟩
    simp only [Function.uncurry_apply_pair, aux_fsrkb_Dynkin_F, Set.indicator, Set.mem_setOf_eq,
      Set.mem_Icc]
  rw [heq]
  exact (measurable_const.mul (Real.continuous_exp.measurable.comp
    (measurable_const.mul measurable_fst))).mul (hval.indicator hset)

theorem aux_fsrkb_Dynkin_abs_F_le {d : ℕ} (U : Set (SpatialCoordinates d))
    (g : SpatialCoordinates d → ℝ) (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg) (lam : ℝ) (hlam : 0 < lam)
    (ω : DiffusionPath d) (t s : ℝ) (ht : 0 ≤ t) :
    |aux_fsrkb_Dynkin_F U g lam ω t s| ≤
      lam * Cg * Real.exp (-(lam / 2) * t) *
        (Set.Ici (0 : ℝ)).indicator (fun s => Real.exp (-(lam / 2) * s)) s := by
  have hCg : 0 ≤ Cg := le_trans (abs_nonneg _) (hgB (ω 0))
  have hB : 0 ≤ lam * Cg * Real.exp (-(lam / 2) * t) *
      (Set.Ici (0 : ℝ)).indicator (fun s => Real.exp (-(lam / 2) * s)) s :=
    mul_nonneg (mul_nonneg (mul_nonneg hlam.le hCg) (Real.exp_pos _).le)
      (Set.indicator_nonneg (fun s _ => (Real.exp_pos _).le) s)
  unfold aux_fsrkb_Dynkin_F
  by_cases hs : s ∈ Set.Icc (0 : ℝ)
      ((ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω : ℝ≥0) : ℝ)
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (show s ∈ Set.Ici (0 : ℝ) from hs.1)]
    have hst : s ≤ t := hs.2.trans (aux_fsrkb_Dynkin_trunc_le U t ht ω)
    have hexp : Real.exp (-lam * t) ≤
        Real.exp (-(lam / 2) * t) * Real.exp (-(lam / 2) * s) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : (lam / 2) * s ≤ (lam / 2) * t :=
        mul_le_mul_of_nonneg_left hst (by linarith only [hlam])
      linarith only [h1]
    rw [abs_mul, abs_mul, abs_of_pos hlam, Real.abs_exp]
    calc lam * Real.exp (-lam * t) * |g (ω (Real.toNNReal s))|
        ≤ lam * (Real.exp (-(lam / 2) * t) * Real.exp (-(lam / 2) * s)) * Cg := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hexp hlam.le) (hgB _) (abs_nonneg _)
          exact mul_nonneg hlam.le (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      _ = lam * Cg * Real.exp (-(lam / 2) * t) * Real.exp (-(lam / 2) * s) := by ring
  · rw [Set.indicator_of_notMem hs, mul_zero, abs_zero]
    exact hB

theorem aux_fsrkb_Dynkin_integrable_F {d : ℕ} (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (g : SpatialCoordinates d → ℝ) (hg : Measurable g) (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg)
    (lam : ℝ) (hlam : 0 < lam) (ω : DiffusionPath d) :
    Integrable (Function.uncurry (aux_fsrkb_Dynkin_F U g lam ω))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
  have hl2 : -(lam / 2) < 0 := by linarith only [hlam]
  have hf : Integrable (fun t : ℝ => lam * Cg * Real.exp (-(lam / 2) * t))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (integrableOn_exp_mul_Ioi hl2 0).const_mul (lam * Cg)
  have hg2 : Integrable ((Set.Ici (0 : ℝ)).indicator (fun s => Real.exp (-(lam / 2) * s)))
      volume :=
    (integrable_indicator_iff measurableSet_Ici).mpr
      (by rw [integrableOn_Ici_iff_integrableOn_Ioi]; exact integrableOn_exp_mul_Ioi hl2 0)
  have hfst : ∀ᵐ p ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume : Measure ℝ)),
      p.1 ∈ Set.Ioi (0 : ℝ) :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
  refine (hf.mul_prod hg2).mono' (aux_fsrkb_Dynkin_measurable_F U hU g hg lam ω).aestronglyMeasurable
    ?_
  filter_upwards [hfst] with p hp
  rw [Real.norm_eq_abs]
  exact aux_fsrkb_Dynkin_abs_F_le U g Cg hgB lam hlam ω p.1 p.2 (le_of_lt hp)

/-- The third piece: the running occupation integral, integrated against `λ e^{-λ t} dt`. -/
theorem aux_fsrkb_Dynkin_piece_three {d : ℕ} (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (g : SpatialCoordinates d → ℝ) (hg : Measurable g) (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg)
    (lam : ℝ) (hlam : 0 < lam) (ω : DiffusionPath d) :
    ∫ t in Set.Ioi (0 : ℝ), lam * Real.exp (-lam * t) *
        ∫ s in Set.Icc (0 : ℝ) ((ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω : ℝ≥0) : ℝ),
          g (ω (Real.toNNReal s)) =
      ∫ t in Set.Ioi (0 : ℝ),
        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U ω}
          (fun s => Real.exp (-lam * s) * g (ω (Real.toNNReal s))) t := by
  have h1 : ∀ t : ℝ, lam * Real.exp (-lam * t) *
      ∫ s in Set.Icc (0 : ℝ) ((ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω : ℝ≥0) : ℝ),
        g (ω (Real.toNNReal s)) = ∫ s, aux_fsrkb_Dynkin_F U g lam ω t s := by
    intro t
    unfold aux_fsrkb_Dynkin_F
    rw [integral_const_mul, integral_indicator measurableSet_Icc]
  simp only [h1]
  rw [integral_integral_swap (aux_fsrkb_Dynkin_integrable_F U hU g hg Cg hgB lam hlam ω)]
  simp only [aux_fsrkb_Dynkin_F_inner U g lam hlam ω]
  rw [← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae ?_
  filter_upwards [Measure.ae_ne volume (0 : ℝ),
    Measure.ae_ne volume (ContinuousPath.exitTime U ω).toReal] with s hs0 hsτ
  by_cases h : s ∈ {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s ≤ ContinuousPath.exitTime U ω}
  · have hpos : 0 < s := lt_of_le_of_ne h.1 (Ne.symm hs0)
    have hlt : ENNReal.ofReal s < ContinuousPath.exitTime U ω := by
      refine lt_of_le_of_ne h.2 (fun heq => hsτ ?_)
      rw [← heq, ENNReal.toReal_ofReal hpos.le]
    rw [Set.indicator_of_mem h, Set.indicator_of_mem (show s ∈ Set.Ioi (0 : ℝ) from hpos),
      Set.indicator_of_mem (show s ∈ {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U ω}
        from hlt)]
  · rw [Set.indicator_of_notMem h]
    by_cases hpos : s ∈ Set.Ioi (0 : ℝ)
    · have hS : s ∉ {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U ω} :=
        fun hS => h ⟨le_of_lt hpos, le_of_lt hS⟩
      rw [Set.indicator_of_mem hpos, Set.indicator_of_notMem hS]
    · rw [Set.indicator_of_notMem hpos]

theorem aux_fsrkb_Dynkin_A_split {d : ℕ} (U : Set (SpatialCoordinates d))
    (phi g : SpatialCoordinates d → ℝ) (hphi : Continuous phi) (Cphi : ℝ)
    (hphiB : ∀ y, |phi y| ≤ Cphi) (hg : Measurable g) (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg)
    (lam : ℝ) (hlam : 0 < lam) (ω : DiffusionPath d) :
    ∫ t in Set.Ioi (0 : ℝ),
        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U ω}
          (fun s => Real.exp (-lam * s) *
            (lam * phi (ω (Real.toNNReal s)) - g (ω (Real.toNNReal s)))) t =
      (∫ t in Set.Ioi (0 : ℝ),
        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U ω}
          (fun s => Real.exp (-lam * s) * (lam * phi (ω (Real.toNNReal s)))) t) -
      ∫ t in Set.Ioi (0 : ℝ),
        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U ω}
          (fun s => Real.exp (-lam * s) * g (ω (Real.toNNReal s))) t := by
  have hS : MeasurableSet {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U ω} :=
    measurableSet_lt ENNReal.measurable_ofReal measurable_const
  have hcont : Continuous fun s : ℝ => phi (ω (Real.toNNReal s)) :=
    hphi.comp (ω.continuous.comp continuous_real_toNNReal)
  have hi1 : IntegrableOn (Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U ω}
      (fun s => Real.exp (-lam * s) * (lam * phi (ω (Real.toNNReal s))))) (Set.Ioi 0) :=
    (aux_fsrkb_Dynkin_integrableOn_exp_mul lam hlam _
      (measurable_const.mul hcont.measurable) (lam * Cphi) (fun s => by
        rw [abs_mul, abs_of_pos hlam]
        exact mul_le_mul_of_nonneg_left (hphiB _) hlam.le)).indicator hS
  have hi3 : IntegrableOn (Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U ω}
      (fun s => Real.exp (-lam * s) * g (ω (Real.toNNReal s)))) (Set.Ioi 0) :=
    (aux_fsrkb_Dynkin_integrableOn_exp_mul lam hlam _
      (hg.comp (ω.continuous.measurable.comp measurable_real_toNNReal)) Cg
      (fun s => hgB _)).indicator hS
  rw [← integral_sub hi1 hi3]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  by_cases h : t ∈ {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U ω}
  · simp only [Set.indicator_of_mem h, mul_sub]
  · simp only [Set.indicator_of_notMem h, sub_zero]

theorem aux_fsrkb_Dynkin_integrableOn_P {d : ℕ} (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (phi : SpatialCoordinates d → ℝ) (hphi : Continuous phi) (Cphi : ℝ)
    (hphiB : ∀ y, |phi y| ≤ Cphi) (lam : ℝ) (hlam : 0 < lam) (ω : DiffusionPath d) :
    IntegrableOn (fun t : ℝ => lam * Real.exp (-lam * t) *
      phi (ω (ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω))) (Set.Ioi 0) := by
  have hσt : Measurable fun t : ℝ => ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω :=
    (aux_fsrkb_Dynkin_measurable_trunc U hU).comp (measurable_const.prodMk measurable_id)
  have hmeas : Measurable fun t : ℝ => lam * Real.exp (-lam * t) *
      phi (ω (ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω)) :=
    (measurable_const.mul (Real.continuous_exp.measurable.comp
      (measurable_const.mul measurable_id))).mul
      (hphi.measurable.comp (ω.continuous.measurable.comp hσt))
  refine Integrable.mono' ((aux_fsrkb_Dynkin_integrableOn_exp lam hlam).const_mul (lam * Cphi))
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hlam, Real.abs_exp]
  calc lam * Real.exp (-lam * t) *
        |phi (ω (ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω))|
      ≤ lam * Real.exp (-lam * t) * Cphi :=
        mul_le_mul_of_nonneg_left (hphiB _) (mul_nonneg hlam.le (Real.exp_pos _).le)
    _ = lam * Cphi * Real.exp (-lam * t) := by ring

theorem aux_fsrkb_Dynkin_integrableOn_Gt {d : ℕ} (U : Set (SpatialCoordinates d))
    (hU : IsOpen U) (g : SpatialCoordinates d → ℝ) (hg : Measurable g) (Cg : ℝ)
    (hgB : ∀ y, |g y| ≤ Cg) (lam : ℝ) (hlam : 0 < lam) (ω : DiffusionPath d) :
    IntegrableOn (fun t : ℝ => lam * Real.exp (-lam * t) *
      ∫ s in Set.Icc (0 : ℝ) ((ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω : ℝ≥0) : ℝ),
        g (ω (Real.toNNReal s))) (Set.Ioi 0) := by
  have hCg : 0 ≤ Cg := le_trans (abs_nonneg _) (hgB (ω 0))
  have hσt : Measurable fun t : ℝ =>
      ((ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω : ℝ≥0) : ℝ) :=
    measurable_coe_nnreal_real.comp
      ((aux_fsrkb_Dynkin_measurable_trunc U hU).comp (measurable_const.prodMk measurable_id))
  have hint := aux_fsrkb_Dynkin_measurable_setIntegral
    (fun t : ℝ => ((ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω : ℝ≥0) : ℝ)) hσt
    (fun (_ : ℝ) (s : ℝ) => g (ω (Real.toNNReal s)))
    (hg.comp (ω.continuous.measurable.comp (measurable_real_toNNReal.comp measurable_snd)))
  have hmeas : Measurable fun t : ℝ => lam * Real.exp (-lam * t) *
      ∫ s in Set.Icc (0 : ℝ) ((ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω : ℝ≥0) : ℝ),
        g (ω (Real.toNNReal s)) :=
    (measurable_const.mul (Real.continuous_exp.measurable.comp
      (measurable_const.mul measurable_id))).mul hint
  refine Integrable.mono'
    ((aux_fsrkb_Dynkin_integrableOn_mul_exp lam hlam).const_mul (lam * Cg))
    hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
  have ht0 : 0 ≤ t := le_of_lt ht
  have hσ := aux_fsrkb_Dynkin_trunc_le U t ht0 ω
  have hb := aux_fsrkb_Dynkin_abs_setIntegral_le (fun s => g (ω (Real.toNNReal s))) Cg
    (fun s => hgB _) _ (NNReal.coe_nonneg (ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω))
  have hb' : Cg * ((ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω : ℝ≥0) : ℝ) ≤ Cg * t :=
    mul_le_mul_of_nonneg_left hσ hCg
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hlam, Real.abs_exp]
  calc lam * Real.exp (-lam * t) * |∫ s in Set.Icc (0 : ℝ)
        ((ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω : ℝ≥0) : ℝ),
          g (ω (Real.toNNReal s))|
      ≤ lam * Real.exp (-lam * t) * (Cg * t) :=
        mul_le_mul_of_nonneg_left (hb.trans hb') (mul_nonneg hlam.le (Real.exp_pos _).le)
    _ = lam * Cg * (t * Real.exp (-lam * t)) := by ring

/-- **Pathwise identity**: integrating the weighted stopped identity over all horizons. -/
theorem aux_fsrkb_Dynkin_pathwise {d : ℕ} (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (phi g : SpatialCoordinates d → ℝ) (hphi : Continuous phi) (Cphi : ℝ)
    (hphiB : ∀ y, |phi y| ≤ Cphi) (hg : Measurable g) (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg)
    (x : SpatialCoordinates d) (lam : ℝ) (hlam : 0 < lam) (ω : DiffusionPath d) :
    ∫ t in Set.Ioi (0 : ℝ), aux_fsrkb_Dynkin_H U phi g x lam ω t =
      (∫ t in Set.Ioi (0 : ℝ),
        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U ω}
          (fun s => Real.exp (-lam * s) *
            (lam * phi (ω (Real.toNNReal s)) - g (ω (Real.toNNReal s)))) t) +
      (if ContinuousPath.exitTime U ω = ⊤ then 0 else
        Real.exp (-lam * (ContinuousPath.exitTime U ω).toReal) *
          phi (ω (ContinuousPath.exitTime U ω).toNNReal)) - phi x := by
  have hH : ∀ t : ℝ, aux_fsrkb_Dynkin_H U phi g x lam ω t =
      lam * Real.exp (-lam * t) *
        phi (ω (ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω)) -
      lam * Real.exp (-lam * t) * phi x -
      lam * Real.exp (-lam * t) *
        ∫ s in Set.Icc (0 : ℝ) ((ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω : ℝ≥0) : ℝ),
          g (ω (Real.toNNReal s)) := by
    intro t
    unfold aux_fsrkb_Dynkin_H
    ring
  simp only [hH]
  have hP := aux_fsrkb_Dynkin_integrableOn_P U hU phi hphi Cphi hphiB lam hlam ω
  have hc : IntegrableOn (fun t : ℝ => lam * Real.exp (-lam * t) * phi x) (Set.Ioi 0) :=
    ((aux_fsrkb_Dynkin_integrableOn_exp lam hlam).const_mul lam).mul_const (phi x)
  have hG := aux_fsrkb_Dynkin_integrableOn_Gt U hU g hg Cg hgB lam hlam ω
  have hPc : IntegrableOn (fun t : ℝ => lam * Real.exp (-lam * t) *
      phi (ω (ContinuousPath.exitTimeTrunc U (Real.toNNReal t) ω)) -
      lam * Real.exp (-lam * t) * phi x) (Set.Ioi 0) := hP.sub hc
  rw [integral_sub hPc hG, integral_sub hP hc,
    aux_fsrkb_Dynkin_piece_one U phi hphi Cphi hphiB lam hlam ω,
    aux_fsrkb_Dynkin_integral_exp lam hlam (phi x),
    aux_fsrkb_Dynkin_piece_three U hU g hg Cg hgB lam hlam ω,
    aux_fsrkb_Dynkin_A_split U phi g hphi Cphi hphiB hg Cg hgB lam hlam ω]
  ring

theorem aux_fsrkb_Dynkin_integrable_boundary {d : ℕ} (ν : Measure (DiffusionPath d))
    [IsProbabilityMeasure ν] (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (phi : SpatialCoordinates d → ℝ) (hphi : Continuous phi) (Cphi : ℝ)
    (hphiB : ∀ y, |phi y| ≤ Cphi) (lam : ℝ) (hlam : 0 < lam) :
    Integrable (fun ω : DiffusionPath d => if ContinuousPath.exitTime U ω = ⊤ then 0 else
        Real.exp (-lam * (ContinuousPath.exitTime U ω).toReal) *
          phi (ω (ContinuousPath.exitTime U ω).toNNReal)) ν := by
  have hτ : Measurable (ContinuousPath.exitTime U : DiffusionPath d → ℝ≥0∞) :=
    ContinuousPath.measurable_exitTime U hU
  have hev : Measurable fun ω : DiffusionPath d => ω (ContinuousPath.exitTime U ω).toNNReal :=
    continuous_eval.measurable.comp (measurable_id.prodMk (ENNReal.measurable_toNNReal.comp hτ))
  have hmeas : Measurable (fun ω : DiffusionPath d =>
      if ContinuousPath.exitTime U ω = ⊤ then 0 else
        Real.exp (-lam * (ContinuousPath.exitTime U ω).toReal) *
          phi (ω (ContinuousPath.exitTime U ω).toNNReal)) :=
    Measurable.ite (measurableSet_eq_fun hτ measurable_const) measurable_const
      ((Real.continuous_exp.measurable.comp
        (measurable_const.mul (ENNReal.measurable_toReal.comp hτ))).mul
          (hphi.measurable.comp hev))
  refine Integrable.of_bound hmeas.aestronglyMeasurable Cphi
    (Filter.Eventually.of_forall fun ω => ?_)
  have hC : 0 ≤ Cphi := le_trans (abs_nonneg _) (hphiB (ω 0))
  rw [Real.norm_eq_abs]
  split_ifs with h
  · rw [abs_zero]; exact hC
  · rw [abs_mul, Real.abs_exp]
    have he : Real.exp (-lam * (ContinuousPath.exitTime U ω).toReal) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_mul]
      exact neg_nonpos.mpr (mul_nonneg hlam.le ENNReal.toReal_nonneg)
    calc Real.exp (-lam * (ContinuousPath.exitTime U ω).toReal) *
          |phi (ω (ContinuousPath.exitTime U ω).toNNReal)|
        ≤ 1 * Cphi := mul_le_mul he (hphiB _) (abs_nonneg _) zero_le_one
      _ = Cphi := one_mul _

/-- The discounted killed occupation integral of `λ φ − g` along one path. -/
noncomputable def aux_fsrkb_Dynkin_A {d : ℕ} (U : Set (SpatialCoordinates d))
    (phi g : SpatialCoordinates d → ℝ) (lam : ℝ) (ω : DiffusionPath d) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ),
    Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U ω}
      (fun s => Real.exp (-lam * s) *
        (lam * phi (ω (Real.toNNReal s)) - g (ω (Real.toNNReal s)))) t

/-- The discounted exit boundary term along one path. -/
noncomputable def aux_fsrkb_Dynkin_Bd {d : ℕ} (U : Set (SpatialCoordinates d))
    (phi : SpatialCoordinates d → ℝ) (lam : ℝ) (ω : DiffusionPath d) : ℝ :=
  if ContinuousPath.exitTime U ω = ⊤ then 0 else
    Real.exp (-lam * (ContinuousPath.exitTime U ω).toReal) *
      phi (ω (ContinuousPath.exitTime U ω).toNNReal)

theorem aux_fsrkb_Dynkin_assembly {d : ℕ} (ν : Measure (DiffusionPath d))
    [IsProbabilityMeasure ν]
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (phi g : SpatialCoordinates d → ℝ) (hphi : Continuous phi) (Cphi : ℝ)
    (hphiB : ∀ y, |phi y| ≤ Cphi) (hg : Measurable g) (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg)
    (x : SpatialCoordinates d)
    (hdyn : ∀ t : ℝ≥0, ∫ path,
      (phi (path (ContinuousPath.exitTimeTrunc U t path)) - phi x -
        ∫ s in Set.Icc (0 : ℝ) ((ContinuousPath.exitTimeTrunc U t path) : ℝ),
          g (path (Real.toNNReal s))) ∂ν = 0)
    (lam : ℝ) (hlam : 0 < lam) :
    ∫ ω, aux_fsrkb_Dynkin_A U phi g lam ω ∂ν =
      phi x - ∫ ω, aux_fsrkb_Dynkin_Bd U phi lam ω ∂ν := by
  have hH := aux_fsrkb_Dynkin_integrable_H ν U hU phi g hphi Cphi hphiB hg Cg hgB x lam hlam
  have hswap := integral_integral_swap hH
  have hzero : ∀ t : ℝ, ∫ ω, aux_fsrkb_Dynkin_H U phi g x lam ω t ∂ν = 0 := by
    intro t
    unfold aux_fsrkb_Dynkin_H
    rw [integral_const_mul, hdyn (Real.toNNReal t), mul_zero]
  have hpath : ∀ ω : DiffusionPath d, ∫ t in Set.Ioi (0 : ℝ), aux_fsrkb_Dynkin_H U phi g x lam ω t =
      aux_fsrkb_Dynkin_A U phi g lam ω + aux_fsrkb_Dynkin_Bd U phi lam ω - phi x :=
    fun ω => aux_fsrkb_Dynkin_pathwise U hU phi g hphi Cphi hphiB hg Cg hgB x lam hlam ω
  simp only [hzero, integral_zero, hpath] at hswap
  have hsum := hH.integral_prod_left
  simp only [Function.uncurry_apply_pair, hpath] at hsum
  have hBd : Integrable (aux_fsrkb_Dynkin_Bd U phi lam) ν :=
    aux_fsrkb_Dynkin_integrable_boundary ν U hU phi hphi Cphi hphiB lam hlam
  have hA : Integrable (aux_fsrkb_Dynkin_A U phi g lam) ν := by
    refine ((hsum.sub hBd).add (integrable_const (phi x))).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [integral_sub (f := fun ω => aux_fsrkb_Dynkin_A U phi g lam ω +
      aux_fsrkb_Dynkin_Bd U phi lam ω) (hA.add hBd) (integrable_const _),
    integral_add hA hBd, integral_const, probReal_univ, one_smul] at hswap
  linarith only [hswap]

/-- **Discounted stopped Dynkin.**  For one path law `ν` and one open set `U`, the
undiscounted stopped identity at every horizon gives the discounted identity with the exit
boundary term. -/
theorem aux_fsrkb_discount {d : ℕ} (ν : Measure (DiffusionPath d)) [IsProbabilityMeasure ν]
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (phi g : SpatialCoordinates d → ℝ) (hphi : Continuous phi) (Cphi : ℝ)
    (hphiB : ∀ y, |phi y| ≤ Cphi) (hg : Measurable g) (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg)
    (x : SpatialCoordinates d)
    (hdyn : ∀ t : ℝ≥0, ∫ path,
      (phi (path (ContinuousPath.exitTimeTrunc U t path)) - phi x -
        ∫ s in Set.Icc (0 : ℝ) ((ContinuousPath.exitTimeTrunc U t path) : ℝ),
          g (path (Real.toNNReal s))) ∂ν = 0)
    (lam : ℝ) (hlam : 0 < lam) :
    ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
          (fun s => Real.exp (-lam * s) *
            (lam * phi (path (Real.toNNReal s)) - g (path (Real.toNNReal s)))) t) ∂ν =
      phi x - ∫ path, (if ContinuousPath.exitTime U path = ⊤ then 0 else
        Real.exp (-lam * (ContinuousPath.exitTime U path).toReal) *
          phi (path (ContinuousPath.exitTime U path).toNNReal)) ∂ν := by
  exact aux_fsrkb_Dynkin_assembly ν U hU phi g hphi Cphi hphiB hg Cg hgB x hdyn lam hlam

/-- At a finite exit time from an open set, the path is outside the set. -/
theorem aux_fsrkb_Dynkin_exit_notMem {d : ℕ} (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (ω : DiffusionPath d) (hfin : ContinuousPath.exitTime U ω ≠ ⊤) :
    ω (ContinuousPath.exitTime U ω).toNNReal ∉ U := by
  by_cases h0 : ω 0 ∈ U
  · have hfr := ContinuousPath.coordinate_exitTime_mem_frontier U hU ω h0 hfin
    rw [hU.frontier_eq] at hfr
    exact hfr.2
  · have hle := ContinuousPath.exitTime_le_of_notMem U ω 0 h0
    have hz : ContinuousPath.exitTime U ω = 0 := by
      rw [ENNReal.coe_zero] at hle
      exact le_antisymm hle (zero_le _)
    rw [hz, ENNReal.toNNReal_zero]
    exact h0

/-- **Discounted stopped Dynkin, zero boundary values.**  If `phi` vanishes off the open set
`U`, the boundary term disappears and the killed resolvent inverts `lam - g`. -/
theorem aux_fsrkb_killedRes_eq_of_dynkin {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (phi g : SpatialCoordinates d → ℝ) (hphi : Continuous phi) (Cphi : ℝ)
    (hphiB : ∀ y, |phi y| ≤ Cphi) (hphiU : ∀ y, y ∉ U → phi y = 0)
    (hg : Measurable g) (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg)
    (hdyn : aux_fsrkb_StoppedDynkin K U phi g) (lam : ℝ) (hlam : 0 < lam)
    (x : SpatialCoordinates d) :
    aux_fsrkb_killedRes K U lam (fun y => lam * phi y - g y) x = phi x := by
  have h := aux_fsrkb_Dynkin_assembly (K x) U hU phi g hphi Cphi hphiB hg Cg hgB x (hdyn x)
    lam hlam
  have hBd : ∀ ω : DiffusionPath d, aux_fsrkb_Dynkin_Bd U phi lam ω = 0 := by
    intro ω
    unfold aux_fsrkb_Dynkin_Bd
    split_ifs with htop
    · rfl
    · rw [hphiU _ (aux_fsrkb_Dynkin_exit_notMem U hU ω htop), mul_zero]
  simp only [hBd, integral_zero, sub_zero] at h
  exact h

/-- **Discounted stopped Dynkin, nonnegative data.**  If `phi ≥ 0`, the killed resolvent of
`lam * phi - g` is at most `phi`. -/
theorem aux_fsrkb_killedRes_le_of_dynkin {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (phi g : SpatialCoordinates d → ℝ) (hphi : Continuous phi) (Cphi : ℝ)
    (hphiB : ∀ y, |phi y| ≤ Cphi) (hphi0 : ∀ y, 0 ≤ phi y)
    (hg : Measurable g) (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg)
    (hdyn : aux_fsrkb_StoppedDynkin K U phi g) (lam : ℝ) (hlam : 0 < lam)
    (x : SpatialCoordinates d) :
    aux_fsrkb_killedRes K U lam (fun y => lam * phi y - g y) x ≤ phi x := by
  have h := aux_fsrkb_Dynkin_assembly (K x) U hU phi g hphi Cphi hphiB hg Cg hgB x (hdyn x)
    lam hlam
  have hBd : 0 ≤ ∫ ω, aux_fsrkb_Dynkin_Bd U phi lam ω ∂(K x) := by
    refine integral_nonneg fun ω => ?_
    unfold aux_fsrkb_Dynkin_Bd
    split_ifs with htop
    · exact le_rfl
    · exact mul_nonneg (Real.exp_pos _).le (hphi0 _)
  have h' : aux_fsrkb_killedRes K U lam (fun y => lam * phi y - g y) x =
      phi x - ∫ ω, aux_fsrkb_Dynkin_Bd U phi lam ω ∂(K x) := h
  rw [h']
  linarith only [hBd]

end KbDynkin

section KbRestart

open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

/-- Restriction of a rational past to the cut-augmented past coordinates (copy of a private
MarkovProcess definition). -/
noncomputable def aux_fsrkb_restart_restrictPastWithTerminal {alpha : Type*} (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) (path : Set.Iic S → alpha) :
    MixedPastFuture.pastWithTerminalFinset S I → alpha :=
  fun r ↦ path ⟨r, MixedPastFuture.le_terminal_of_mem_pastWithTerminalFinset S I r.property⟩

/-- Restriction of a future path to the strictly positive future coordinates. -/
noncomputable def aux_fsrkb_restart_restrictPositiveFuture {alpha : Type*} [TopologicalSpace alpha]
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (path : ContinuousPath alpha) : MixedPastFuture.positiveFutureFinset S I → alpha :=
  fun t ↦ path (DenseTime.castOrderEmbedding t)

/-- Reindex an ordered cut past by the cut-augmented past coordinates. -/
noncomputable def aux_fsrkb_restart_reindexCutPast {alpha : Type*} (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime))
    (path : Fin (MixedPastFuture.pastPredecessorCard S I + 1) → alpha) :
    MixedPastFuture.pastWithTerminalFinset S I → alpha :=
  fun r ↦ path (MixedPastFuture.pastCutOrderIndex S I r)

/-- Reindex an ordered positive future by the positive future coordinates. -/
noncomputable def aux_fsrkb_restart_reindexPositiveFuture {alpha : Type*} (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime))
    (path : Fin (MixedPastFuture.positiveFutureFinset S I).card → alpha) :
    MixedPastFuture.positiveFutureFinset S I → alpha :=
  fun t ↦ path (MixedPastFuture.positiveFutureOrderIndex S I t)

theorem aux_fsrkb_restart_measurable_restrictPastWithTerminal {alpha : Type*}
    [MeasurableSpace alpha] (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Measurable (aux_fsrkb_restart_restrictPastWithTerminal (alpha := alpha) S I) := by
  rw [measurable_pi_iff]
  intro r
  exact measurable_pi_apply _

theorem aux_fsrkb_restart_measurable_restrictPositiveFuture {alpha : Type*}
    [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Measurable (aux_fsrkb_restart_restrictPositiveFuture (alpha := alpha) S I) := by
  rw [measurable_pi_iff]
  intro t
  exact ContinuousPath.measurable_coordinateProcess _

theorem aux_fsrkb_restart_measurable_reindexCutPast {alpha : Type*}
    [MeasurableSpace alpha] (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Measurable (aux_fsrkb_restart_reindexCutPast (alpha := alpha) S I) := by
  rw [measurable_pi_iff]
  intro r
  exact measurable_pi_apply _

theorem aux_fsrkb_restart_measurable_reindexPositiveFuture {alpha : Type*}
    [MeasurableSpace alpha] (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Measurable (aux_fsrkb_restart_reindexPositiveFuture (alpha := alpha) S I) := by
  rw [measurable_pi_iff]
  intro t
  exact measurable_pi_apply _

theorem aux_fsrkb_restart_restrictPast_terminal {alpha : Type*} [TopologicalSpace alpha]
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    (fun z : MixedPastFuture.pastWithTerminalFinset S I → alpha ↦
      z ⟨S, Finset.mem_union_right _ (Finset.mem_singleton_self S)⟩) ∘
        aux_fsrkb_restart_restrictPastWithTerminal S I =
      ContinuousPath.densePastTerminal S := by
  funext path
  rfl

theorem aux_fsrkb_restart_reindexCutPast_terminal {alpha : Type*} (S : DenseTime)
    (I : Finset (Set.Iic S ⊕ DenseTime)) :
    (fun z : MixedPastFuture.pastWithTerminalFinset S I → alpha ↦
      z ⟨S, Finset.mem_union_right _ (Finset.mem_singleton_self S)⟩) ∘
        aux_fsrkb_restart_reindexCutPast S I =
      (fun path : Fin (MixedPastFuture.pastPredecessorCard S I + 1) → alpha ↦
        path (Fin.last (MixedPastFuture.pastPredecessorCard S I))) := by
  funext path
  apply congrArg path
  apply (MixedPastFuture.cutPastOrderedPhysicalTimes S I).injective
  rw [MixedPastFuture.cutPastOrderedPhysicalTimes_pastCutOrderIndex,
    MixedPastFuture.cutPastOrderedPhysicalTimes_last]

section Generic

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha]

omit [CompleteSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha] in
/-- Finite dense-time marginals of a kernel with the finite-dimensional laws of `P`. -/
theorem aux_fsrkb_restart_map_finiteDenseTimeSet
    (P : SubMarkovKernelSemigroup alpha)
    (Q : Kernel alpha (ContinuousPath alpha))
    (hQ : ∀ I : Finset ℝ≥0,
      Q.map (ContinuousPath.finsetEvaluation I) = SubMarkovKernelSemigroup.finiteSetKernel P I)
    (J : Finset DenseTime) :
    Q.map (fun path (t : SubMarkovKernelSemigroup.denseTimePhysicalSet J) ↦ path t) =
      SubMarkovKernelSemigroup.finiteSetKernel P
        (SubMarkovKernelSemigroup.denseTimePhysicalSet J) :=
  hQ _

omit [CompleteSpace alpha] [SecondCountableTopology alpha] [StandardBorelSpace alpha]
  [Nonempty alpha] in
theorem aux_fsrkb_restart_map_restrictPastWithTerminal
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (Q : Kernel alpha (ContinuousPath alpha))
    (hQ : ∀ I : Finset ℝ≥0,
      Q.map (ContinuousPath.finsetEvaluation I) = SubMarkovKernelSemigroup.finiteSetKernel P I)
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    (Q.map (ContinuousPath.densePastRestriction S)).map
        (aux_fsrkb_restart_restrictPastWithTerminal S I) =
      (SubMarkovKernelSemigroup.finiteTimeKernel P
        (MixedPastFuture.cutPastOrderedPhysicalTimes S I)).map
        (aux_fsrkb_restart_reindexCutPast S I) := by
  rw [← Kernel.map_comp_right]
  · let J := MixedPastFuture.pastWithTerminalFinset S I
    let E : ContinuousPath alpha → SubMarkovKernelSemigroup.denseTimePhysicalSet J → alpha :=
      fun path t ↦ path t
    have hE : Measurable E := by
      rw [measurable_pi_iff]
      intro t
      exact ContinuousPath.measurable_coordinateProcess t
    have hfun :
        aux_fsrkb_restart_restrictPastWithTerminal S I ∘
            ContinuousPath.densePastRestriction S =
          DenseTimePath.pullbackPhysicalSet J ∘ E := by
      funext path r
      rfl
    rw [hfun, Kernel.map_comp_right]
    · rw [aux_fsrkb_restart_map_finiteDenseTimeSet P Q hQ J]
      rw [SubMarkovKernelSemigroup.finiteSetKernel_eq_map]
      let e : Fin (MixedPastFuture.pastPredecessorCard S I + 1) ↪o
          Fin (MixedPastFuture.pastPhysicalFinsetWithTerminal S I).card :=
        (Fin.castOrderIso (by
          rw [MixedPastFuture.pastPhysicalFinsetWithTerminal,
            SubMarkovKernelSemigroup.denseTimePhysicalSet, Finset.card_map,
            MixedPastFuture.card_pastWithTerminalFinset])).toOrderEmbedding
      rw [show MixedPastFuture.cutPastOrderedPhysicalTimes S I =
          (SubMarkovKernelSemigroup.finiteSetTimes
            (MixedPastFuture.pastPhysicalFinsetWithTerminal S I)).restrict e
        from rfl,
        ← hP.finiteTimeKernel_map_restrictPath P _ e,
        ← Kernel.map_comp_right, ← Kernel.map_comp_right]
      · congr 1
      · exact FiniteOrderedTimes.measurable_restrictPath e
      · exact aux_fsrkb_restart_measurable_reindexCutPast S I
      · exact SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet _
      · exact DenseTimePath.measurable_pullbackPhysicalSet J
    · exact hE
    · exact DenseTimePath.measurable_pullbackPhysicalSet J
  · exact ContinuousPath.measurable_densePastRestriction S
  · exact aux_fsrkb_restart_measurable_restrictPastWithTerminal S I

omit [CompleteSpace alpha] [SecondCountableTopology alpha] [StandardBorelSpace alpha]
  [Nonempty alpha] in
theorem aux_fsrkb_restart_map_restrictPositiveFuture
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (Q : Kernel alpha (ContinuousPath alpha))
    (hQ : ∀ I : Finset ℝ≥0,
      Q.map (ContinuousPath.finsetEvaluation I) = SubMarkovKernelSemigroup.finiteSetKernel P I)
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Q.map (aux_fsrkb_restart_restrictPositiveFuture S I) =
      (SubMarkovKernelSemigroup.finiteTimeKernel P
        (MixedPastFuture.positiveFutureOrderedPhysicalTimes S I)).map
          (aux_fsrkb_restart_reindexPositiveFuture S I) := by
  let J := MixedPastFuture.positiveFutureFinset S I
  let E : ContinuousPath alpha → SubMarkovKernelSemigroup.denseTimePhysicalSet J → alpha :=
    fun path t ↦ path t
  have hE : Measurable E := by
    rw [measurable_pi_iff]
    intro t
    exact ContinuousPath.measurable_coordinateProcess t
  have hfun : aux_fsrkb_restart_restrictPositiveFuture S I =
      DenseTimePath.pullbackPhysicalSet J ∘ E := by
    funext path t
    rfl
  rw [hfun, Kernel.map_comp_right]
  · rw [aux_fsrkb_restart_map_finiteDenseTimeSet P Q hQ J]
    rw [SubMarkovKernelSemigroup.finiteSetKernel_eq_map]
    let e : Fin (MixedPastFuture.positiveFutureFinset S I).card ↪o
        Fin (SubMarkovKernelSemigroup.denseTimePhysicalSet J).card :=
      (Fin.castOrderIso (by
        simp only [J, SubMarkovKernelSemigroup.denseTimePhysicalSet,
          Finset.card_map])).toOrderEmbedding
    rw [show MixedPastFuture.positiveFutureOrderedPhysicalTimes S I =
        (SubMarkovKernelSemigroup.finiteSetTimes
          (SubMarkovKernelSemigroup.denseTimePhysicalSet J)).restrict e from rfl,
      ← hP.finiteTimeKernel_map_restrictPath P _ e,
      ← Kernel.map_comp_right, ← Kernel.map_comp_right]
    · congr 1
    · exact FiniteOrderedTimes.measurable_restrictPath e
    · exact aux_fsrkb_restart_measurable_reindexPositiveFuture S I
    · exact SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet _
    · exact DenseTimePath.measurable_pullbackPhysicalSet J
  · exact hE
  · exact DenseTimePath.measurable_pullbackPhysicalSet J

omit [CompleteSpace alpha] [SecondCountableTopology alpha]
  [StandardBorelSpace alpha] [Nonempty alpha] in
theorem aux_fsrkb_restart_map_restrict_eq_cutPullback
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime))
    (hzero : ∀ x, ∀ᵐ path ∂Q x,
      path (0 : NNReal) = x) :
    (ContinuousPath.rationalPastFutureRestartKernel Q S).map
        (I.restrict ∘ Kernel.finitePastDenseFuture) =
      (ContinuousPath.rationalPastFutureRestartKernel Q S).map
        (MixedPastFuture.pullbackCutCoordinates S I ∘
          Prod.map (aux_fsrkb_restart_restrictPastWithTerminal S I)
            (aux_fsrkb_restart_restrictPositiveFuture S I)) := by
  let F := I.restrict ∘
    Kernel.finitePastDenseFuture (index := Set.Iic S) (alpha := alpha)
  let H := MixedPastFuture.pullbackCutCoordinates (alpha := alpha) S I ∘
    Prod.map (aux_fsrkb_restart_restrictPastWithTerminal S I)
      (aux_fsrkb_restart_restrictPositiveFuture S I)
  have hF : Measurable F :=
    (Finset.measurable_restrict I).comp Kernel.measurable_finitePastDenseFuture
  have hH : Measurable H :=
    (MixedPastFuture.measurable_pullbackCutCoordinates S I).comp
      ((aux_fsrkb_restart_measurable_restrictPastWithTerminal S I).prodMap
        (aux_fsrkb_restart_measurable_restrictPositiveFuture S I))
  change (ContinuousPath.rationalPastFutureRestartKernel Q S).map F =
    (ContinuousPath.rationalPastFutureRestartKernel Q S).map H
  ext x A hA
  rw [Kernel.map_apply' _ hF x hA, Kernel.map_apply' _ hH x hA,
    ContinuousPath.rationalPastFutureRestartKernel,
    Kernel.compProd_apply (hA.preimage hF),
    Kernel.compProd_apply (hA.preimage hH)]
  congr with history
  rw [Kernel.prodMkLeft_apply', Kernel.prodMkLeft_apply']
  apply Filter.EventuallyEq.measure_eq
  filter_upwards [hzero (ContinuousPath.densePastTerminal S history)] with path hpath
  apply congrArg (fun z ↦ z ∈ A)
  funext i
  rcases i with ⟨i, hi⟩
  rcases i with r | t
  ·
      simp [F, H, Function.comp_apply, Kernel.finitePastDenseFuture,
        MixedPastFuture.pullbackCutCoordinates, MixedPastFuture.cutCoordinateIndex,
        aux_fsrkb_restart_restrictPastWithTerminal, Prod.map_apply]
  ·
      by_cases ht : t = 0
      · subst t
        have hpath' : path (DenseTime.castOrderEmbedding (0 : DenseTime)) =
            ContinuousPath.densePastTerminal S history := by
          convert hpath using 1
          norm_num [DenseTime.castOrderEmbedding, NNRat.castOrderEmbedding_apply]
        simpa [F, H, Function.comp_apply, Kernel.finitePastDenseFuture,
          MixedPastFuture.pullbackCutCoordinates, MixedPastFuture.cutCoordinateIndex,
          aux_fsrkb_restart_restrictPastWithTerminal, Prod.map_apply,
          ContinuousPath.densePastTerminal, ContinuousPath.denseRestriction_apply]
          using hpath'
      · simp [F, H, Function.comp_apply, Kernel.finitePastDenseFuture,
          MixedPastFuture.pullbackCutCoordinates, MixedPastFuture.cutCoordinateIndex,
          aux_fsrkb_restart_restrictPositiveFuture, Prod.map_apply, ht,
          ContinuousPath.denseRestriction_apply]

omit [CompleteSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha] in
/-- Starting point of a kernel with the finite-dimensional laws of `P`. -/
theorem aux_fsrkb_restart_ae_zero
    (P : SubMarkovKernelSemigroup alpha)
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (hQ : ∀ I : Finset ℝ≥0,
      Q.map (ContinuousPath.finsetEvaluation I) = SubMarkovKernelSemigroup.finiteSetKernel P I)
    (x : alpha) : ∀ᵐ path ∂Q x, path (0 : NNReal) = x := by
  let evalZero : ContinuousPath alpha → alpha := fun path ↦ path 0
  have hEvalZero : Measurable evalZero :=
    ContinuousPath.measurable_coordinateProcess 0
  have hmev : Measurable (fun w : (({(0 : ℝ≥0)} : Finset ℝ≥0)) → alpha =>
      w ⟨0, Finset.mem_singleton_self 0⟩) := measurable_pi_apply _
  have hcomp : (fun w : (({(0 : ℝ≥0)} : Finset ℝ≥0)) → alpha =>
        w ⟨0, Finset.mem_singleton_self 0⟩) ∘
      ContinuousPath.finsetEvaluation (alpha := alpha) ({(0 : ℝ≥0)} : Finset ℝ≥0) =
      evalZero := rfl
  have hmapK : Q.map evalZero = P.kernel 0 := by
    rw [← hcomp, Kernel.map_comp_right Q
      (ContinuousPath.measurable_finsetEvaluation _) hmev, hQ,
      finiteSetKernel_singleton_map_eval]
  have hmap : Measure.map evalZero (Q x) = Measure.dirac x := by
    have h := congrArg (fun K : Kernel alpha alpha ↦ K x) hmapK
    simp only at h
    rw [Kernel.map_apply Q hEvalZero x] at h
    rw [h]
    change P 0 x = _
    rw [P.zero, Kernel.id_apply]
  letI : IsProbabilityMeasure (Q x) := IsMarkovKernel.isProbabilityMeasure x
  apply (mem_ae_iff_prob_eq_one
    (hEvalZero (MeasurableSet.singleton x))).mpr
  rw [← Measure.map_apply hEvalZero (MeasurableSet.singleton x), hmap]
  simp

omit [CompleteSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha] in
theorem aux_fsrkb_restart_rationalRestart_map
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (hQ : ∀ I : Finset ℝ≥0,
      Q.map (ContinuousPath.finsetEvaluation I) = SubMarkovKernelSemigroup.finiteSetKernel P I)
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    (ContinuousPath.rationalPastFutureRestartKernel Q S).map
        (I.restrict ∘ Kernel.finitePastDenseFuture) =
      ((SubMarkovKernelSemigroup.finiteTimeKernel P
          (MixedPastFuture.cutPastOrderedPhysicalTimes S I)) ⊗ₖ
        (SubMarkovKernelSemigroup.finiteTimeKernel P
          (MixedPastFuture.positiveFutureOrderedPhysicalTimes S I)).comap
            (SubMarkovKernelSemigroup.splitPastTerminal (alpha := alpha)
              (m := MixedPastFuture.pastPredecessorCard S I))
            SubMarkovKernelSemigroup.measurable_splitPastTerminal).map
        (MixedPastFuture.pullbackCutCoordinates S I ∘
          MixedPastFuture.orderedSplitToCutCoordinates S I) := by
  let f := aux_fsrkb_restart_restrictPastWithTerminal (alpha := alpha) S I
  let g := aux_fsrkb_restart_restrictPositiveFuture (alpha := alpha) S I
  let terminal' : (MixedPastFuture.pastWithTerminalFinset S I → alpha) → alpha :=
    fun path ↦ path ⟨S, Finset.mem_union_right _ (Finset.mem_singleton_self S)⟩
  have hterminal' : Measurable terminal' := measurable_pi_apply _
  have hcompat : terminal' ∘ f = ContinuousPath.densePastTerminal S :=
    aux_fsrkb_restart_restrictPast_terminal S I
  have hrestartSplit :
      (ContinuousPath.rationalPastFutureRestartKernel Q S).map (Prod.map f g) =
        ((Q.map (ContinuousPath.densePastRestriction S)).map f) ⊗ₖ
          Kernel.prodMkLeft alpha ((Q.map g).comap terminal' hterminal') := by
    rw [ContinuousPath.rationalPastFutureRestartKernel]
    exact Kernel.map_compProd_prodMkLeft_comap
      (Q.map (ContinuousPath.densePastRestriction S)) Q
      (ContinuousPath.densePastTerminal S) terminal' hterminal' f
      (aux_fsrkb_restart_measurable_restrictPastWithTerminal S I) g
      (aux_fsrkb_restart_measurable_restrictPositiveFuture S I) hcompat
  let Kp := SubMarkovKernelSemigroup.finiteTimeKernel P
    (MixedPastFuture.cutPastOrderedPhysicalTimes S I)
  let Kf := SubMarkovKernelSemigroup.finiteTimeKernel P
    (MixedPastFuture.positiveFutureOrderedPhysicalTimes S I)
  letI : IsMarkovKernel Kp :=
    hP.isMarkovKernel_finiteTimeKernel P
      (MixedPastFuture.cutPastOrderedPhysicalTimes S I)
  letI : IsMarkovKernel Kf :=
    hP.isMarkovKernel_finiteTimeKernel P
      (MixedPastFuture.positiveFutureOrderedPhysicalTimes S I)
  let rp := aux_fsrkb_restart_reindexCutPast (alpha := alpha) S I
  let rf := aux_fsrkb_restart_reindexPositiveFuture (alpha := alpha) S I
  let last : (Fin (MixedPastFuture.pastPredecessorCard S I + 1) → alpha) → alpha :=
    fun path ↦ path (Fin.last (MixedPastFuture.pastPredecessorCard S I))
  have hlast : Measurable last := measurable_pi_apply _
  have hrcompat : terminal' ∘ rp = last :=
    aux_fsrkb_restart_reindexCutPast_terminal S I
  have hfactorSplit :
      (Kp ⊗ₖ (Kf.comap
        (SubMarkovKernelSemigroup.splitPastTerminal (alpha := alpha)
          (m := MixedPastFuture.pastPredecessorCard S I))
        SubMarkovKernelSemigroup.measurable_splitPastTerminal)).map
          (MixedPastFuture.orderedSplitToCutCoordinates S I) =
        (Kp.map rp) ⊗ₖ
          Kernel.prodMkLeft alpha ((Kf.map rf).comap terminal' hterminal') := by
    change
      (Kp ⊗ₖ Kernel.prodMkLeft alpha (Kf.comap last hlast)).map
          (Prod.map rp rf) = _
    exact Kernel.map_compProd_prodMkLeft_comap Kp Kf last terminal'
      hterminal' rp (aux_fsrkb_restart_measurable_reindexCutPast S I)
      rf (aux_fsrkb_restart_measurable_reindexPositiveFuture S I) hrcompat
  have hsplit :
      (ContinuousPath.rationalPastFutureRestartKernel Q S).map (Prod.map f g) =
        (Kp ⊗ₖ (Kf.comap
          (SubMarkovKernelSemigroup.splitPastTerminal (alpha := alpha)
            (m := MixedPastFuture.pastPredecessorCard S I))
          SubMarkovKernelSemigroup.measurable_splitPastTerminal)).map
            (MixedPastFuture.orderedSplitToCutCoordinates S I) := by
    rw [hrestartSplit,
      aux_fsrkb_restart_map_restrictPastWithTerminal P hP Q hQ S I,
      aux_fsrkb_restart_map_restrictPositiveFuture P hP Q hQ S I,
      hfactorSplit]
  have hzero : ∀ x, ∀ᵐ path ∂Q x, path (0 : NNReal) = x :=
    aux_fsrkb_restart_ae_zero P Q hQ
  rw [aux_fsrkb_restart_map_restrict_eq_cutPullback Q S I hzero]
  calc
    (ContinuousPath.rationalPastFutureRestartKernel Q S).map
        (MixedPastFuture.pullbackCutCoordinates S I ∘ Prod.map f g) =
      ((ContinuousPath.rationalPastFutureRestartKernel Q S).map
        (Prod.map f g)).map (MixedPastFuture.pullbackCutCoordinates S I) := by
        exact Kernel.map_comp_right _
          ((aux_fsrkb_restart_measurable_restrictPastWithTerminal S I).prodMap
            (aux_fsrkb_restart_measurable_restrictPositiveFuture S I))
          (MixedPastFuture.measurable_pullbackCutCoordinates S I)
    _ = ((Kp ⊗ₖ (Kf.comap
          (SubMarkovKernelSemigroup.splitPastTerminal (alpha := alpha)
            (m := MixedPastFuture.pastPredecessorCard S I))
          SubMarkovKernelSemigroup.measurable_splitPastTerminal)).map
            (MixedPastFuture.orderedSplitToCutCoordinates S I)).map
        (MixedPastFuture.pullbackCutCoordinates S I) := by rw [hsplit]
    _ = _ := (Kernel.map_comp_right _
      (MixedPastFuture.measurable_orderedSplitToCutCoordinates S I)
      (MixedPastFuture.measurable_pullbackCutCoordinates S I)).symm

omit [CompleteSpace alpha] [SecondCountableTopology alpha] [StandardBorelSpace alpha]
  [Nonempty alpha] in
/-- Mixed past/shifted-future finite marginals of a kernel with the finite laws of `P`. -/
theorem aux_fsrkb_restart_map_mixed
    (P : SubMarkovKernelSemigroup alpha)
    (Q : Kernel alpha (ContinuousPath alpha))
    (hQ : ∀ I : Finset ℝ≥0,
      Q.map (ContinuousPath.finsetEvaluation I) = SubMarkovKernelSemigroup.finiteSetKernel P I)
    (S : DenseTime) (I : Finset (Set.Iic S ⊕ DenseTime)) :
    Q.map (I.restrict ∘ ContinuousPath.mixedPastShiftedCoordinates S) =
      (SubMarkovKernelSemigroup.finiteSetKernel P
        (MixedPastFuture.absolutePhysicalFinset S I)).map
        (MixedPastFuture.pullbackAbsolutePhysical S I) := by
  let evaluateAbsolute : ContinuousPath alpha →
      MixedPastFuture.absolutePhysicalFinset S I → alpha :=
    fun path t ↦ path t
  have hEvaluateAbsolute : Measurable evaluateAbsolute := by
    rw [measurable_pi_iff]
    intro t
    exact ContinuousPath.measurable_coordinateProcess (alpha := alpha) t
  have hcoordinates :
      I.restrict ∘ ContinuousPath.mixedPastShiftedCoordinates S =
        MixedPastFuture.pullbackAbsolutePhysical S I ∘ evaluateAbsolute := by
    funext omega
    exact ContinuousPath.restrict_mixedPastShiftedCoordinates S I omega
  rw [hcoordinates, Kernel.map_comp_right]
  · change
      (Q.map
        (fun path (t : SubMarkovKernelSemigroup.denseTimePhysicalSet
          (MixedPastFuture.absoluteFinset S I)) ↦ path t)).map
          (MixedPastFuture.pullbackAbsolutePhysical S I) = _
    rw [aux_fsrkb_restart_map_finiteDenseTimeSet P Q hQ]
    rfl
  · exact hEvaluateAbsolute
  · exact MixedPastFuture.measurable_pullbackAbsolutePhysical S I

/-- The joint rational past / shifted future law of `Q` is the rational restart kernel. -/
theorem aux_fsrkb_restart_joint
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (hQ : ∀ I : Finset ℝ≥0,
      Q.map (ContinuousPath.finsetEvaluation I) = SubMarkovKernelSemigroup.finiteSetKernel P I)
    (S : DenseTime) :
    Q.map (fun omega ↦
        (ContinuousPath.densePastRestriction S omega,
          ContinuousPath.shift (DenseTime.castOrderEmbedding S) omega)) =
      ContinuousPath.rationalPastFutureRestartKernel Q S := by
  apply Kernel.eq_of_map_finitePastDenseFutureRestriction_eq
    (ContinuousMap.const NNReal (Classical.arbitrary alpha))
  intro I
  rw [← Kernel.map_comp_right]
  · have hcoordinates :
        (I.restrict ∘ Kernel.finitePastDenseFuture
          (index := Set.Iic S) (alpha := alpha)) ∘ (fun omega ↦
            (ContinuousPath.densePastRestriction S omega,
              ContinuousPath.shift (DenseTime.castOrderEmbedding S) omega)) =
          I.restrict ∘ ContinuousPath.mixedPastShiftedCoordinates S := by
        funext omega
        exact congrArg I.restrict
          (ContinuousPath.finitePastDenseFuture_densePastRestriction_shift S omega)
    rw [hcoordinates]
    rw [aux_fsrkb_restart_map_mixed P Q hQ S I]
    rw [SubMarkovKernelSemigroup.IsConservative.finiteSetKernel_map_pullbackAbsolutePhysical_eq_cutFactorized
      P hP S I]
    exact (aux_fsrkb_restart_rationalRestart_map P hP Q hQ S I).symm
  · exact (ContinuousPath.measurable_densePastRestriction S).prodMk
      (ContinuousPath.measurable_shift_fixed (DenseTime.castOrderEmbedding S))
  · exact (Finset.measurable_restrict I).comp
      (Kernel.measurable_finitePastDenseFuture
        (index := Set.Iic S) (alpha := alpha))

theorem aux_fsrkb_restart_joint_apply
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (hQ : ∀ I : Finset ℝ≥0,
      Q.map (ContinuousPath.finsetEvaluation I) = SubMarkovKernelSemigroup.finiteSetKernel P I)
    (x : alpha) (S : DenseTime) :
    (Q x).map (fun omega ↦
        (ContinuousPath.densePastRestriction S omega,
          ContinuousPath.shift (DenseTime.castOrderEmbedding S) omega)) =
      ((Q x).map (ContinuousPath.densePastRestriction S)) ⊗ₘ
        Kernel.comap Q (ContinuousPath.densePastTerminal S)
          (ContinuousPath.measurable_densePastTerminal S) := by
  have h := congrArg (fun K : Kernel alpha
      ((Set.Iic S → alpha) × ContinuousPath alpha) ↦ K x)
    (aux_fsrkb_restart_joint P hP Q hQ S)
  change (Q.map (fun omega ↦
      (ContinuousPath.densePastRestriction S omega,
        ContinuousPath.shift (DenseTime.castOrderEmbedding S) omega))) x =
    ContinuousPath.rationalPastFutureRestartKernel Q S x at h
  rw [Kernel.map_apply Q
      ((ContinuousPath.measurable_densePastRestriction S).prodMk
        (ContinuousPath.measurable_shift_fixed (DenseTime.castOrderEmbedding S))) x,
    ContinuousPath.rationalPastFutureRestartKernel_apply Q S x] at h
  exact h

end Generic

/-- **Restart at rational times.** -/
theorem aux_fsrkb_restart {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hP : P.IsConservative)
    (hfdd : aux_fsrkb_Fdd K P) (x : SpatialCoordinates d) (S : DenseTime) :
    ∀ A : Set (DiffusionPath d),
      MeasurableSet[ContinuousPath.canonicalFiltration (alpha := SpatialCoordinates d)
        (DenseTime.castOrderEmbedding S)] A →
        ((K x).restrict A).map (ContinuousPath.shift (DenseTime.castOrderEmbedding S)) =
          Kernel.comap K
              (ContinuousPath.coordinateProcess (alpha := SpatialCoordinates d)
                (DenseTime.castOrderEmbedding S))
              (ContinuousPath.measurable_coordinateProcess _) ∘ₘ
            ((K x).restrict A) := by
  have hQ : ∀ I : Finset ℝ≥0,
      K.map (ContinuousPath.finsetEvaluation I) =
        SubMarkovKernelSemigroup.finiteSetKernel P I := by
    intro I
    ext y : 1
    rw [Kernel.map_apply K (ContinuousPath.measurable_finsetEvaluation I) y]
    exact hfdd I y
  exact ContinuousPath.restrict_map_shift_eq_pathKernel_comp_of_rational_joint K x S
    (aux_fsrkb_restart_joint_apply P hP K hQ x S)

end KbRestart

section KbStopDynkin

open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

/-- The occupation integral of `g` along a path up to time `b`. -/
noncomputable def aux_fsrkb_stopDynkin_I {d : ℕ} (g : SpatialCoordinates d → ℝ) (b : ℝ≥0)
    (path : DiffusionPath d) : ℝ :=
  ∫ s in Set.Icc (0 : ℝ) (b : ℝ), g (path (Real.toNNReal s))

/-- The stopped Dynkin process `phi(X_{s ∧ τ_Q}) - ∫_0^{s ∧ τ_Q} g(X_r) dr`. -/
noncomputable def aux_fsrkb_stopDynkin_N {d : ℕ} (Q : Set (SpatialCoordinates d))
    (phi g : SpatialCoordinates d → ℝ) (s : ℝ≥0) (path : DiffusionPath d) : ℝ :=
  phi (path (ContinuousPath.exitTimeTrunc Q s path)) -
    aux_fsrkb_stopDynkin_I g (ContinuousPath.exitTimeTrunc Q s path) path

theorem aux_fsrkb_stopDynkin_measurable_integrand {d : ℕ} {g : SpatialCoordinates d → ℝ}
    (hg : Measurable g) (path : DiffusionPath d) :
    Measurable (fun s : ℝ => g (path (Real.toNNReal s))) :=
  hg.comp (path.continuous.comp continuous_real_toNNReal).measurable

theorem aux_fsrkb_stopDynkin_intervalIntegrable {d : ℕ} {g : SpatialCoordinates d → ℝ}
    (hg : Measurable g) (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg) (path : DiffusionPath d) (a b : ℝ) :
    IntervalIntegrable (fun s : ℝ => g (path (Real.toNNReal s))) volume a b := by
  refine IntervalIntegrable.mono_fun' (g := fun _ => Cg) intervalIntegrable_const
    (aux_fsrkb_stopDynkin_measurable_integrand hg path).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun s => by simpa [Real.norm_eq_abs] using hgB _)

theorem aux_fsrkb_stopDynkin_I_eq_interval {d : ℕ} (g : SpatialCoordinates d → ℝ) (b : ℝ≥0)
    (path : DiffusionPath d) :
    aux_fsrkb_stopDynkin_I g b path = ∫ s in (0 : ℝ)..(b : ℝ), g (path (Real.toNNReal s)) := by
  rw [aux_fsrkb_stopDynkin_I, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (NNReal.coe_nonneg b)]

theorem aux_fsrkb_stopDynkin_continuous_I {d : ℕ} {g : SpatialCoordinates d → ℝ}
    (hg : Measurable g) (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg) (path : DiffusionPath d) :
    Continuous (fun b : ℝ≥0 => aux_fsrkb_stopDynkin_I g b path) := by
  have h := intervalIntegral.continuous_primitive
    (aux_fsrkb_stopDynkin_intervalIntegrable hg Cg hgB path) 0
  have h2 := h.comp NNReal.continuous_coe
  refine h2.congr ?_
  intro b
  exact (aux_fsrkb_stopDynkin_I_eq_interval g b path).symm

theorem aux_fsrkb_stopDynkin_measurable_I_fixed {d : ℕ} {g : SpatialCoordinates d → ℝ}
    (hg : Measurable g) (b : ℝ≥0) :
    Measurable (fun path : DiffusionPath d => aux_fsrkb_stopDynkin_I g b path) := by
  have hjoint : Measurable (fun p : DiffusionPath d × ℝ => g (p.1 (Real.toNNReal p.2))) := by
    have hc : Continuous (fun p : DiffusionPath d × ℝ => p.1 (Real.toNNReal p.2)) :=
      ContinuousEval.continuous_eval.comp
        (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))
    exact hg.comp hc.measurable
  have h := MeasureTheory.StronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) (b : ℝ))) hjoint.stronglyMeasurable
  exact h.measurable

theorem aux_fsrkb_stopDynkin_measurable_I {d : ℕ} {g : SpatialCoordinates d → ℝ}
    (hg : Measurable g) (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg) :
    Measurable (fun p : ℝ≥0 × DiffusionPath d => aux_fsrkb_stopDynkin_I g p.1 p.2) :=
  measurable_uncurry_of_continuous_of_measurable
    (u := fun (b : ℝ≥0) (path : DiffusionPath d) => aux_fsrkb_stopDynkin_I g b path)
    (fun path => aux_fsrkb_stopDynkin_continuous_I hg Cg hgB path)
    (fun b => aux_fsrkb_stopDynkin_measurable_I_fixed hg b)

theorem aux_fsrkb_stopDynkin_abs_I_le {d : ℕ} {g : SpatialCoordinates d → ℝ}
    (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg) (b : ℝ≥0) (path : DiffusionPath d) :
    |aux_fsrkb_stopDynkin_I g b path| ≤ Cg * b := by
  rw [aux_fsrkb_stopDynkin_I_eq_interval]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := (b : ℝ)) (C := Cg) (f := fun s : ℝ => g (path (Real.toNNReal s)))
    (fun s _ => by simpa [Real.norm_eq_abs] using hgB _)
  simpa [Real.norm_eq_abs, abs_of_nonneg b.2] using h

theorem aux_fsrkb_stopDynkin_I_zero {d : ℕ} (g : SpatialCoordinates d → ℝ)
    (path : DiffusionPath d) : aux_fsrkb_stopDynkin_I g 0 path = 0 := by
  rw [aux_fsrkb_stopDynkin_I_eq_interval]
  simp

theorem aux_fsrkb_stopDynkin_I_add {d : ℕ} {g : SpatialCoordinates d → ℝ}
    (hg : Measurable g) (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg) (a b : ℝ≥0)
    (path : DiffusionPath d) :
    aux_fsrkb_stopDynkin_I g (a + b) path =
      aux_fsrkb_stopDynkin_I g a path +
        aux_fsrkb_stopDynkin_I g b (ContinuousPath.shift a path) := by
  rw [aux_fsrkb_stopDynkin_I_eq_interval, aux_fsrkb_stopDynkin_I_eq_interval,
    aux_fsrkb_stopDynkin_I_eq_interval]
  have hint := aux_fsrkb_stopDynkin_intervalIntegrable hg Cg hgB path
  rw [NNReal.coe_add]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 a) (hint a (a + b))]
  congr 1
  have hshift : ∫ s in (0 : ℝ)..(b : ℝ),
      g ((ContinuousPath.shift a path) (Real.toNNReal s)) =
      ∫ s in (0 : ℝ)..(b : ℝ), g (path (Real.toNNReal (s + a))) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs0 : 0 ≤ s := by
      rw [Set.uIcc_of_le (NNReal.coe_nonneg b)] at hs
      exact hs.1
    simp only [ContinuousPath.shift_apply]
    congr 2
    apply NNReal.eq
    have hsa : 0 ≤ s + (a : ℝ) := add_nonneg hs0 (NNReal.coe_nonneg a)
    simp [Real.coe_toNNReal _ hs0, Real.coe_toNNReal _ hsa, add_comm]
  rw [hshift, intervalIntegral.integral_comp_add_right (fun s => g (path (Real.toNNReal s)))]
  simp [add_comm]

theorem aux_fsrkb_stopDynkin_coe_trunc {d : ℕ} (U : Set (SpatialCoordinates d)) (s : ℝ≥0)
    (path : DiffusionPath d) :
    ((ContinuousPath.exitTimeTrunc U s path : ℝ≥0) : ℝ≥0∞) =
      min (ContinuousPath.exitTime U path) (s : ℝ≥0∞) :=
  ContinuousPath.coe_exitTimeTrunc U s path

theorem aux_fsrkb_stopDynkin_trunc_of_le {d : ℕ} (U : Set (SpatialCoordinates d)) (a : ℝ≥0)
    (path : DiffusionPath d) (ha : (a : ℝ≥0∞) ≤ ContinuousPath.exitTime U path) :
    ContinuousPath.exitTimeTrunc U a path = a := by
  apply ENNReal.coe_injective
  rw [aux_fsrkb_stopDynkin_coe_trunc]
  exact min_eq_right ha

theorem aux_fsrkb_stopDynkin_trunc_zero {d : ℕ} (U : Set (SpatialCoordinates d))
    (path : DiffusionPath d) : ContinuousPath.exitTimeTrunc U 0 path = 0 :=
  le_antisymm (ContinuousPath.exitTimeTrunc_le U 0 path) (zero_le _)

theorem aux_fsrkb_stopDynkin_trunc_add {d : ℕ} (U : Set (SpatialCoordinates d)) (a h : ℝ≥0)
    (path : DiffusionPath d) (ha : (a : ℝ≥0∞) < ContinuousPath.exitTime U path) :
    ContinuousPath.exitTimeTrunc U (a + h) path =
      a + ContinuousPath.exitTimeTrunc U h (ContinuousPath.shift a path) := by
  apply ENNReal.coe_injective
  rw [aux_fsrkb_stopDynkin_coe_trunc, ENNReal.coe_add, ENNReal.coe_add,
    aux_fsrkb_stopDynkin_coe_trunc,
    ← ContinuousPath.exitTime_shift_add U path a ha, add_comm (a : ℝ≥0∞) (h : ℝ≥0∞),
    min_add_add_right, add_comm]

theorem aux_fsrkb_stopDynkin_continuous_trunc {d : ℕ} (U : Set (SpatialCoordinates d))
    (path : DiffusionPath d) :
    Continuous (fun s : ℝ≥0 => ContinuousPath.exitTimeTrunc U s path) := by
  by_cases htop : ContinuousPath.exitTime U path = ⊤
  · have h : (fun s : ℝ≥0 => ContinuousPath.exitTimeTrunc U s path) = fun s => s := by
      funext s
      apply aux_fsrkb_stopDynkin_trunc_of_le
      rw [htop]
      exact le_top
    rw [h]
    exact continuous_id
  · have h : (fun s : ℝ≥0 => ContinuousPath.exitTimeTrunc U s path) =
        fun s => min (ContinuousPath.exitTime U path).toNNReal s := by
      funext s
      apply ENNReal.coe_injective
      rw [aux_fsrkb_stopDynkin_coe_trunc, ENNReal.coe_min, ENNReal.coe_toNNReal htop]
    rw [h]
    exact continuous_const.min continuous_id

theorem aux_fsrkb_stopDynkin_trunc_sub {d : ℕ} {U Q : Set (SpatialCoordinates d)}
    (hUQ : U ⊆ Q) (t : ℝ≥0) (path : DiffusionPath d) :
    ContinuousPath.exitTimeTrunc Q (ContinuousPath.exitTimeTrunc U t path) path =
      ContinuousPath.exitTimeTrunc U t path := by
  apply aux_fsrkb_stopDynkin_trunc_of_le
  rw [aux_fsrkb_stopDynkin_coe_trunc]
  exact (min_le_left _ _).trans (ContinuousPath.exitTime_mono hUQ path)

theorem aux_fsrkb_stopDynkin_lt_exit_of_lt {d : ℕ} {U Q : Set (SpatialCoordinates d)}
    (hUQ : U ⊆ Q) (t a : ℝ≥0) (path : DiffusionPath d)
    (ha : a < ContinuousPath.exitTimeTrunc U t path) :
    (a : ℝ≥0∞) < ContinuousPath.exitTime Q path := by
  have h1 : (a : ℝ≥0∞) < ((ContinuousPath.exitTimeTrunc U t path : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.coe_lt_coe.mpr ha
  rw [aux_fsrkb_stopDynkin_coe_trunc] at h1
  exact (h1.trans_le (min_le_left _ _)).trans_le (ContinuousPath.exitTime_mono hUQ path)

theorem aux_fsrkb_stopDynkin_N_zero {d : ℕ} (Q : Set (SpatialCoordinates d))
    (phi g : SpatialCoordinates d → ℝ) (path : DiffusionPath d) :
    aux_fsrkb_stopDynkin_N Q phi g 0 path = phi (path 0) := by
  rw [aux_fsrkb_stopDynkin_N, aux_fsrkb_stopDynkin_trunc_zero, aux_fsrkb_stopDynkin_I_zero,
    sub_zero]

theorem aux_fsrkb_stopDynkin_N_incr {d : ℕ} (Q : Set (SpatialCoordinates d))
    (phi : SpatialCoordinates d → ℝ) {g : SpatialCoordinates d → ℝ}
    (hg : Measurable g) (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg) (a h : ℝ≥0)
    (path : DiffusionPath d) (ha : (a : ℝ≥0∞) < ContinuousPath.exitTime Q path) :
    aux_fsrkb_stopDynkin_N Q phi g (a + h) path - aux_fsrkb_stopDynkin_N Q phi g a path =
      aux_fsrkb_stopDynkin_N Q phi g h (ContinuousPath.shift a path) -
        phi (ContinuousPath.shift a path 0) := by
  simp only [aux_fsrkb_stopDynkin_N]
  rw [aux_fsrkb_stopDynkin_trunc_add Q a h path ha, aux_fsrkb_stopDynkin_trunc_of_le Q a path ha.le,
    aux_fsrkb_stopDynkin_I_add hg Cg hgB, ContinuousPath.shift_apply, ContinuousPath.shift_apply,
    add_zero]
  ring

theorem aux_fsrkb_stopDynkin_continuous_N {d : ℕ} (Q : Set (SpatialCoordinates d))
    {phi g : SpatialCoordinates d → ℝ} (hphi : Continuous phi)
    (hg : Measurable g) (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg) (path : DiffusionPath d) :
    Continuous (fun s : ℝ≥0 => aux_fsrkb_stopDynkin_N Q phi g s path) := by
  have hT := aux_fsrkb_stopDynkin_continuous_trunc Q path
  exact (hphi.comp (path.continuous.comp hT)).sub
    ((aux_fsrkb_stopDynkin_continuous_I hg Cg hgB path).comp hT)

theorem aux_fsrkb_stopDynkin_measurable_eval_I {d : ℕ}
    {phi g : SpatialCoordinates d → ℝ} (hphi : Continuous phi)
    (hg : Measurable g) (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg)
    (T : DiffusionPath d → ℝ≥0) (hT : Measurable T) :
    Measurable (fun path : DiffusionPath d =>
      phi (path (T path)) - aux_fsrkb_stopDynkin_I g (T path) path) := by
  have h1 : Measurable (fun path : DiffusionPath d => phi (path (T path))) :=
    hphi.measurable.comp (ContinuousPath.measurable_eval_of_measurable T hT)
  have h2 : Measurable (fun path : DiffusionPath d => aux_fsrkb_stopDynkin_I g (T path) path) :=
    (aux_fsrkb_stopDynkin_measurable_I hg Cg hgB).comp (hT.prodMk measurable_id)
  exact h1.sub h2

theorem aux_fsrkb_stopDynkin_measurable_N {d : ℕ} {Q : Set (SpatialCoordinates d)}
    (hQ : IsOpen Q) {phi g : SpatialCoordinates d → ℝ} (hphi : Continuous phi)
    (hg : Measurable g) (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg) (s : ℝ≥0) :
    Measurable (fun path : DiffusionPath d => aux_fsrkb_stopDynkin_N Q phi g s path) :=
  aux_fsrkb_stopDynkin_measurable_eval_I hphi hg Cg hgB _
    (ContinuousPath.measurable_of_isStoppingTime _
      (ContinuousPath.isStoppingTime_exitTimeTrunc Q hQ s))

theorem aux_fsrkb_stopDynkin_measurable_N_joint {d : ℕ} {Q : Set (SpatialCoordinates d)}
    (hQ : IsOpen Q) {phi g : SpatialCoordinates d → ℝ} (hphi : Continuous phi)
    (hg : Measurable g) (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg) :
    Measurable (fun p : ℝ≥0 × DiffusionPath d => aux_fsrkb_stopDynkin_N Q phi g p.1 p.2) :=
  measurable_uncurry_of_continuous_of_measurable
    (u := fun (s : ℝ≥0) (path : DiffusionPath d) => aux_fsrkb_stopDynkin_N Q phi g s path)
    (fun path => aux_fsrkb_stopDynkin_continuous_N Q hphi hg Cg hgB path)
    (fun s => aux_fsrkb_stopDynkin_measurable_N hQ hphi hg Cg hgB s)

theorem aux_fsrkb_stopDynkin_abs_N_le {d : ℕ} (Q : Set (SpatialCoordinates d))
    {phi g : SpatialCoordinates d → ℝ} (Cphi : ℝ) (hphiB : ∀ y, |phi y| ≤ Cphi)
    (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg) (s : ℝ≥0) (path : DiffusionPath d) :
    |aux_fsrkb_stopDynkin_N Q phi g s path| ≤ Cphi + Cg * s := by
  have hCg : 0 ≤ Cg := (abs_nonneg _).trans (hgB 0)
  have h1 := hphiB (path (ContinuousPath.exitTimeTrunc Q s path))
  have h2 := aux_fsrkb_stopDynkin_abs_I_le Cg hgB (ContinuousPath.exitTimeTrunc Q s path) path
  have h3 : ((ContinuousPath.exitTimeTrunc Q s path : ℝ≥0) : ℝ) ≤ (s : ℝ) :=
    NNReal.coe_le_coe.mpr (ContinuousPath.exitTimeTrunc_le Q s path)
  have h4 : Cg * ((ContinuousPath.exitTimeTrunc Q s path : ℝ≥0) : ℝ) ≤ Cg * (s : ℝ) :=
    mul_le_mul_of_nonneg_left h3 hCg
  rw [aux_fsrkb_stopDynkin_N]
  exact (abs_sub _ _).trans (by linarith only [h1, h2, h4])

theorem aux_fsrkb_stopDynkin_kernel_fdd {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hfdd : aux_fsrkb_Fdd K P) :
    ∀ I : Finset ℝ≥0, K.map (ContinuousPath.finsetEvaluation I) =
      SubMarkovKernelSemigroup.finiteSetKernel P I := by
  intro I
  ext y : 1
  rw [Kernel.map_apply K (ContinuousPath.measurable_finsetEvaluation I) y]
  exact hfdd I y

theorem aux_fsrkb_stopDynkin_setIntegral_shift {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hP : P.IsConservative)
    (hfdd : aux_fsrkb_Fdd K P) (x : SpatialCoordinates d) (S : DenseTime)
    (A : Set (DiffusionPath d))
    (hA : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := SpatialCoordinates d)
        (DenseTime.castOrderEmbedding S)] A)
    (F : DiffusionPath d → ℝ) (hF : Measurable F) (C : ℝ) (hFC : ∀ η, |F η| ≤ C)
    (hzero : ∀ y, ∫ η, F η ∂(K y) = 0) :
    ∫ path in A, F (ContinuousPath.shift (DenseTime.castOrderEmbedding S) path) ∂(K x) = 0 := by
  have hce := ContinuousPath.condExp_shift_ae_eq_integral_pathKernel_of_restrict_map K x
    (DenseTime.castOrderEmbedding S) (aux_fsrkb_restart K P hP hfdd x S) F
    hF.stronglyMeasurable C (fun η => by simpa [Real.norm_eq_abs] using hFC η)
  have hint : Integrable
      (fun path => F (ContinuousPath.shift (DenseTime.castOrderEmbedding S) path)) (K x) :=
    Integrable.of_bound
      ((hF.comp (ContinuousPath.measurable_shift_fixed _)).aestronglyMeasurable) C
      (ae_of_all _ fun path => by simpa [Real.norm_eq_abs] using hFC _)
  have hm := (ContinuousPath.canonicalFiltration (alpha := SpatialCoordinates d)).le
    (DenseTime.castOrderEmbedding S)
  rw [← setIntegral_condExp hm hint hA]
  rw [setIntegral_congr_ae (hm A hA) (hce.mono fun path h _ => h)]
  simp [hzero]

theorem aux_fsrkb_stopDynkin_integral_F_zero {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hfdd : aux_fsrkb_Fdd K P) (Q : Set (SpatialCoordinates d))
    (phi g : SpatialCoordinates d → ℝ) (hstop : aux_fsrkb_StoppedDynkin K Q phi g)
    (y : SpatialCoordinates d) (h : ℝ≥0) :
    ∫ η, (aux_fsrkb_stopDynkin_N Q phi g h η - phi (η 0)) ∂(K y) = 0 := by
  have hae := aux_fsrkb_restart_ae_zero P K (aux_fsrkb_stopDynkin_kernel_fdd K P hfdd) y
  rw [← hstop y h]
  apply integral_congr_ae
  filter_upwards [hae] with η hη
  simp only [aux_fsrkb_stopDynkin_N, aux_fsrkb_stopDynkin_I, hη]
  ring

theorem aux_fsrkb_stopDynkin_grid_eq (m j : ℕ) :
    dyadicGrid m j = DenseTime.castOrderEmbedding ((j : ℚ≥0) / 2 ^ m) := by
  apply NNReal.eq
  simp [dyadicGrid, DenseTime.castOrderEmbedding, NNRat.castOrderEmbedding_apply]

theorem aux_fsrkb_stopDynkin_grid_succ (m j : ℕ) :
    dyadicGrid m (j + 1) = dyadicGrid m j + dyadicGrid m 1 := by
  apply NNReal.eq
  simp only [dyadicGrid, NNReal.coe_mk, NNReal.coe_add]
  push_cast
  ring

theorem aux_fsrkb_stopDynkin_grid_zero (m : ℕ) : dyadicGrid m 0 = 0 := by
  apply NNReal.eq
  simp [dyadicGrid]

theorem aux_fsrkb_stopDynkin_grid_lt_iff (m j : ℕ) (s : ℝ≥0) :
    dyadicGrid m j < s ↔ j < dyadicCeilingIndex m s := by
  rw [dyadicCeilingIndex, Nat.lt_ceil, ← NNReal.coe_lt_coe]
  simp only [dyadicGrid, NNReal.coe_mk]
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ m), mul_comm]

theorem aux_fsrkb_stopDynkin_ceilingIndex_mono (m : ℕ) {s t : ℝ≥0} (hst : s ≤ t) :
    dyadicCeilingIndex m s ≤ dyadicCeilingIndex m t := by
  apply Nat.ceil_mono
  exact mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hst) (by positivity)

theorem aux_fsrkb_stopDynkin_telescope (f : ℕ → ℝ) (i J : ℕ) (hiJ : i ≤ J) :
    ∑ j ∈ Finset.range J, (if j < i then f (j + 1) - f j else 0) = f i - f 0 := by
  induction J, hiJ using Nat.le_induction with
  | base =>
    rw [Finset.sum_congr rfl (fun j hj => if_pos (Finset.mem_range.mp hj))]
    exact Finset.sum_range_sub f i
  | succ J hiJ ih =>
    rw [Finset.sum_range_succ, ih, if_neg (not_lt.mpr hiJ), add_zero]

theorem aux_fsrkb_stopDynkin_pointwise {d : ℕ} (Q U : Set (SpatialCoordinates d))
    (phi g : SpatialCoordinates d → ℝ) (t : ℝ≥0) (m : ℕ) (path : DiffusionPath d) :
    aux_fsrkb_stopDynkin_N Q phi g
        (dyadicCeiling m (ContinuousPath.exitTimeTrunc U t path)) path =
      phi (path 0) + ∑ j ∈ Finset.range (dyadicCeilingIndex m t),
        Set.indicator
          {p : DiffusionPath d | dyadicGrid m j < ContinuousPath.exitTimeTrunc U t p}
          (fun p => aux_fsrkb_stopDynkin_N Q phi g (dyadicGrid m j + dyadicGrid m 1) p -
            aux_fsrkb_stopDynkin_N Q phi g (dyadicGrid m j) p) path := by
  have hsum : ∀ j ∈ Finset.range (dyadicCeilingIndex m t),
      Set.indicator
          {p : DiffusionPath d | dyadicGrid m j < ContinuousPath.exitTimeTrunc U t p}
          (fun p => aux_fsrkb_stopDynkin_N Q phi g (dyadicGrid m j + dyadicGrid m 1) p -
            aux_fsrkb_stopDynkin_N Q phi g (dyadicGrid m j) p) path =
        if j < dyadicCeilingIndex m (ContinuousPath.exitTimeTrunc U t path) then
          aux_fsrkb_stopDynkin_N Q phi g (dyadicGrid m (j + 1)) path -
            aux_fsrkb_stopDynkin_N Q phi g (dyadicGrid m j) path
        else 0 := by
    intro j _
    rw [aux_fsrkb_stopDynkin_grid_succ m j]
    simp only [Set.indicator, Set.mem_setOf_eq, aux_fsrkb_stopDynkin_grid_lt_iff]
  rw [Finset.sum_congr rfl hsum,
    aux_fsrkb_stopDynkin_telescope
      (fun k => aux_fsrkb_stopDynkin_N Q phi g (dyadicGrid m k) path) _ _
      (aux_fsrkb_stopDynkin_ceilingIndex_mono m (ContinuousPath.exitTimeTrunc_le U t path)),
    aux_fsrkb_stopDynkin_grid_zero, aux_fsrkb_stopDynkin_N_zero, dyadicGrid_ceilingIndex]
  ring

theorem aux_fsrkb_stopDynkin_term {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hP : P.IsConservative)
    (hfdd : aux_fsrkb_Fdd K P)
    (Q U : Set (SpatialCoordinates d)) (hQ : IsOpen Q) (hU : IsOpen U) (hUQ : U ⊆ Q)
    (phi g : SpatialCoordinates d → ℝ) (hphi : Continuous phi) (Cphi : ℝ)
    (hphiB : ∀ y, |phi y| ≤ Cphi) (hg : Measurable g) (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg)
    (hstop : aux_fsrkb_StoppedDynkin K Q phi g) (x : SpatialCoordinates d) (t h : ℝ≥0)
    (S : DenseTime) :
    ∫ path, Set.indicator
        {p : DiffusionPath d |
          DenseTime.castOrderEmbedding S < ContinuousPath.exitTimeTrunc U t p}
        (fun p => aux_fsrkb_stopDynkin_N Q phi g (DenseTime.castOrderEmbedding S + h) p -
          aux_fsrkb_stopDynkin_N Q phi g (DenseTime.castOrderEmbedding S) p) path ∂(K x) = 0 := by
  have hAF : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := SpatialCoordinates d)
      (DenseTime.castOrderEmbedding S)]
      {p : DiffusionPath d |
        DenseTime.castOrderEmbedding S < ContinuousPath.exitTimeTrunc U t p} := by
    have hst := ContinuousPath.isStoppingTime_exitTimeTrunc U hU t (DenseTime.castOrderEmbedding S)
    have heq : {p : DiffusionPath d |
        DenseTime.castOrderEmbedding S < ContinuousPath.exitTimeTrunc U t p} =
        {p : DiffusionPath d | ((ContinuousPath.exitTimeTrunc U t p : ℝ≥0) : WithTop ℝ≥0) ≤
          ((DenseTime.castOrderEmbedding S : ℝ≥0) : WithTop ℝ≥0)}ᶜ := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, WithTop.coe_le_coe, not_le]
    rw [heq]
    exact hst.compl
  have hA : MeasurableSet {p : DiffusionPath d |
      DenseTime.castOrderEmbedding S < ContinuousPath.exitTimeTrunc U t p} :=
    (ContinuousPath.canonicalFiltration (alpha := SpatialCoordinates d)).le _ _ hAF
  rw [integral_indicator hA]
  have hcongr : Set.EqOn
      (fun p => aux_fsrkb_stopDynkin_N Q phi g (DenseTime.castOrderEmbedding S + h) p -
          aux_fsrkb_stopDynkin_N Q phi g (DenseTime.castOrderEmbedding S) p)
      (fun p => (fun η : DiffusionPath d => aux_fsrkb_stopDynkin_N Q phi g h η - phi (η 0))
        (ContinuousPath.shift (DenseTime.castOrderEmbedding S) p))
      {p : DiffusionPath d |
        DenseTime.castOrderEmbedding S < ContinuousPath.exitTimeTrunc U t p} := by
    intro p hp
    exact aux_fsrkb_stopDynkin_N_incr Q phi hg Cg hgB _ h p
      (aux_fsrkb_stopDynkin_lt_exit_of_lt hUQ t _ p hp)
  rw [setIntegral_congr_fun hA hcongr]
  have hFm : Measurable (fun η : DiffusionPath d => aux_fsrkb_stopDynkin_N Q phi g h η - phi (η 0)) :=
    (aux_fsrkb_stopDynkin_measurable_N hQ hphi hg Cg hgB h).sub
      (hphi.measurable.comp (ContinuousPath.measurable_coordinateProcess 0))
  have hFB : ∀ η : DiffusionPath d,
      |aux_fsrkb_stopDynkin_N Q phi g h η - phi (η 0)| ≤ (Cphi + Cg * h) + Cphi := by
    intro η
    exact (abs_sub _ _).trans (add_le_add
      (aux_fsrkb_stopDynkin_abs_N_le Q Cphi hphiB Cg hgB h η) (hphiB _))
  exact aux_fsrkb_stopDynkin_setIntegral_shift K P hP hfdd x S _ hAF _ hFm _ hFB
    (fun y => aux_fsrkb_stopDynkin_integral_F_zero K P hfdd Q phi g hstop y h)

theorem aux_fsrkb_stopDynkin_integrable_N {d : ℕ}
    (μ : Measure (DiffusionPath d)) [IsFiniteMeasure μ]
    {Q : Set (SpatialCoordinates d)} (hQ : IsOpen Q)
    {phi g : SpatialCoordinates d → ℝ} (hphi : Continuous phi) (Cphi : ℝ)
    (hphiB : ∀ y, |phi y| ≤ Cphi) (hg : Measurable g) (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg)
    (s : ℝ≥0) :
    Integrable (fun path => aux_fsrkb_stopDynkin_N Q phi g s path) μ :=
  Integrable.of_bound (aux_fsrkb_stopDynkin_measurable_N hQ hphi hg Cg hgB s).aestronglyMeasurable
    (Cphi + Cg * s) (ae_of_all _ fun path => by
      rw [Real.norm_eq_abs]
      exact aux_fsrkb_stopDynkin_abs_N_le Q Cphi hphiB Cg hgB s path)

theorem aux_fsrkb_stopDynkin_integral_phi_zero {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hfdd : aux_fsrkb_Fdd K P) (phi : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d) :
    ∫ path, phi (path 0) ∂(K x) = phi x := by
  have hae := aux_fsrkb_restart_ae_zero P K (aux_fsrkb_stopDynkin_kernel_fdd K P hfdd) x
  rw [integral_congr_ae (hae.mono fun path h => congrArg phi h)]
  simp

theorem aux_fsrkb_stopDynkin_level {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hP : P.IsConservative)
    (hfdd : aux_fsrkb_Fdd K P)
    (Q U : Set (SpatialCoordinates d)) (hQ : IsOpen Q) (hU : IsOpen U) (hUQ : U ⊆ Q)
    (phi g : SpatialCoordinates d → ℝ) (hphi : Continuous phi) (Cphi : ℝ)
    (hphiB : ∀ y, |phi y| ≤ Cphi) (hg : Measurable g) (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg)
    (hstop : aux_fsrkb_StoppedDynkin K Q phi g) (x : SpatialCoordinates d) (t : ℝ≥0) (m : ℕ) :
    ∫ path, aux_fsrkb_stopDynkin_N Q phi g
      (dyadicCeiling m (ContinuousPath.exitTimeTrunc U t path)) path ∂(K x) = phi x := by
  rw [integral_congr_ae (ae_of_all _ (aux_fsrkb_stopDynkin_pointwise Q U phi g t m))]
  have hσ : Measurable (fun path : DiffusionPath d => ContinuousPath.exitTimeTrunc U t path) :=
    ContinuousPath.measurable_of_isStoppingTime _ (ContinuousPath.isStoppingTime_exitTimeTrunc U hU t)
  have hint0 : Integrable (fun path : DiffusionPath d => phi (path 0)) (K x) :=
    Integrable.of_bound
      (hphi.measurable.comp (ContinuousPath.measurable_coordinateProcess 0)).aestronglyMeasurable
      Cphi (ae_of_all _ fun path => by simpa [Real.norm_eq_abs] using hphiB _)
  have hintj : ∀ j ∈ Finset.range (dyadicCeilingIndex m t), Integrable
      (fun path => Set.indicator
          {p : DiffusionPath d | dyadicGrid m j < ContinuousPath.exitTimeTrunc U t p}
          (fun p => aux_fsrkb_stopDynkin_N Q phi g (dyadicGrid m j + dyadicGrid m 1) p -
            aux_fsrkb_stopDynkin_N Q phi g (dyadicGrid m j) p) path) (K x) := by
    intro j _
    apply Integrable.indicator _ (measurableSet_lt measurable_const hσ)
    exact (aux_fsrkb_stopDynkin_integrable_N (K x) hQ hphi Cphi hphiB hg Cg hgB _).sub
      (aux_fsrkb_stopDynkin_integrable_N (K x) hQ hphi Cphi hphiB hg Cg hgB _)
  rw [integral_add hint0 (integrable_finset_sum _ hintj), integral_finset_sum _ hintj]
  have hzero : ∀ j ∈ Finset.range (dyadicCeilingIndex m t),
      ∫ path, Set.indicator
          {p : DiffusionPath d | dyadicGrid m j < ContinuousPath.exitTimeTrunc U t p}
          (fun p => aux_fsrkb_stopDynkin_N Q phi g (dyadicGrid m j + dyadicGrid m 1) p -
            aux_fsrkb_stopDynkin_N Q phi g (dyadicGrid m j) p) path ∂(K x) = 0 := by
    intro j _
    rw [aux_fsrkb_stopDynkin_grid_eq m j]
    exact aux_fsrkb_stopDynkin_term K P hP hfdd Q U hQ hU hUQ phi g hphi Cphi hphiB hg Cg hgB
      hstop x t _ _
  rw [Finset.sum_eq_zero hzero, add_zero]
  exact aux_fsrkb_stopDynkin_integral_phi_zero K P hfdd phi x

theorem aux_fsrkb_stopDynkin_ceiling_le {d : ℕ} (U : Set (SpatialCoordinates d)) (t : ℝ≥0)
    (m : ℕ) (path : DiffusionPath d) :
    ((dyadicCeiling m (ContinuousPath.exitTimeTrunc U t path) : ℝ≥0) : ℝ) ≤ (t : ℝ) + 1 := by
  have h1 := dyadicCeiling_le_add m (ContinuousPath.exitTimeTrunc U t path)
  have h2 : ((2 : ℝ≥0) ^ m)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)
  have h3 : dyadicCeiling m (ContinuousPath.exitTimeTrunc U t path) ≤ t + 1 :=
    h1.trans (add_le_add (ContinuousPath.exitTimeTrunc_le U t path) h2)
  have h4 := NNReal.coe_le_coe.mpr h3
  simpa using h4

theorem aux_fsrkb_stopDynkin_tendsto {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (Q U : Set (SpatialCoordinates d)) (hQ : IsOpen Q) (hU : IsOpen U)
    (phi g : SpatialCoordinates d → ℝ) (hphi : Continuous phi) (Cphi : ℝ)
    (hphiB : ∀ y, |phi y| ≤ Cphi) (hg : Measurable g) (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg)
    (x : SpatialCoordinates d) (t : ℝ≥0) :
    Tendsto (fun m : ℕ => ∫ path, aux_fsrkb_stopDynkin_N Q phi g
        (dyadicCeiling m (ContinuousPath.exitTimeTrunc U t path)) path ∂(K x)) atTop
      (𝓝 (∫ path, aux_fsrkb_stopDynkin_N Q phi g
        (ContinuousPath.exitTimeTrunc U t path) path ∂(K x))) := by
  have hCg : 0 ≤ Cg := (abs_nonneg _).trans (hgB 0)
  have hjoint := aux_fsrkb_stopDynkin_measurable_N_joint hQ hphi hg Cg hgB
  refine tendsto_integral_of_dominated_convergence (fun _ => Cphi + Cg * ((t : ℝ) + 1)) ?_
    (integrable_const _) ?_ ?_
  · intro m
    have hc : Measurable
        (fun path : DiffusionPath d => dyadicCeiling m (ContinuousPath.exitTimeTrunc U t path)) :=
      ContinuousPath.measurable_of_isStoppingTime _
        (isStoppingTime_dyadicCeiling (ContinuousPath.isStoppingTime_exitTimeTrunc U hU t) m)
    exact (hjoint.comp (hc.prodMk measurable_id)).aestronglyMeasurable
  · intro m
    refine ae_of_all _ (fun path => ?_)
    rw [Real.norm_eq_abs]
    refine (aux_fsrkb_stopDynkin_abs_N_le Q Cphi hphiB Cg hgB _ path).trans ?_
    have h := mul_le_mul_of_nonneg_left (aux_fsrkb_stopDynkin_ceiling_le U t m path) hCg
    linarith only [h]
  · refine ae_of_all _ (fun path => ?_)
    exact ((aux_fsrkb_stopDynkin_continuous_N Q hphi hg Cg hgB path).tendsto _).comp
      (tendsto_dyadicCeiling _)

/-- **Dynkin at the exit of an open subset.** -/
theorem aux_fsrkb_stoppedDynkin_sub {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hP : P.IsConservative)
    (hfdd : aux_fsrkb_Fdd K P)
    (Q U : Set (SpatialCoordinates d)) (hQ : IsOpen Q) (hU : IsOpen U) (hUQ : U ⊆ Q)
    (phi g : SpatialCoordinates d → ℝ) (hphi : Continuous phi) (Cphi : ℝ)
    (hphiB : ∀ y, |phi y| ≤ Cphi) (hg : Measurable g) (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg)
    (hstop : aux_fsrkb_StoppedDynkin K Q phi g) :
    aux_fsrkb_StoppedDynkin K U phi g := by
  intro x t
  have hlim := aux_fsrkb_stopDynkin_tendsto K Q U hQ hU phi g hphi Cphi hphiB hg Cg hgB x t
  have hconst : (fun m : ℕ => ∫ path, aux_fsrkb_stopDynkin_N Q phi g
      (dyadicCeiling m (ContinuousPath.exitTimeTrunc U t path)) path ∂(K x)) =
      fun _ => phi x := by
    funext m
    exact aux_fsrkb_stopDynkin_level K P hP hfdd Q U hQ hU hUQ phi g hphi Cphi hphiB hg Cg hgB
      hstop x t m
  rw [hconst] at hlim
  have hEq : ∫ path, aux_fsrkb_stopDynkin_N Q phi g
      (ContinuousPath.exitTimeTrunc U t path) path ∂(K x) = phi x :=
    tendsto_nhds_unique hlim tendsto_const_nhds
  have hσ : Measurable (fun path : DiffusionPath d => ContinuousPath.exitTimeTrunc U t path) :=
    ContinuousPath.measurable_of_isStoppingTime _ (ContinuousPath.isStoppingTime_exitTimeTrunc U hU t)
  have hCg : 0 ≤ Cg := (abs_nonneg _).trans (hgB 0)
  have hint : Integrable (fun path => aux_fsrkb_stopDynkin_N Q phi g
      (ContinuousPath.exitTimeTrunc U t path) path) (K x) := by
    refine Integrable.of_bound
      ((aux_fsrkb_stopDynkin_measurable_N_joint hQ hphi hg Cg hgB).comp
        (hσ.prodMk measurable_id)).aestronglyMeasurable (Cphi + Cg * t) (ae_of_all _ fun path => ?_)
    rw [Real.norm_eq_abs]
    refine (aux_fsrkb_stopDynkin_abs_N_le Q Cphi hphiB Cg hgB _ path).trans ?_
    have h := mul_le_mul_of_nonneg_left
      (NNReal.coe_le_coe.mpr (ContinuousPath.exitTimeTrunc_le U t path)) hCg
    linarith only [h]
  have hpt : ∀ path : DiffusionPath d,
      phi (path (ContinuousPath.exitTimeTrunc U t path)) - phi x -
        ∫ s in Set.Icc (0 : ℝ) ((ContinuousPath.exitTimeTrunc U t path) : ℝ),
          g (path (Real.toNNReal s)) =
      aux_fsrkb_stopDynkin_N Q phi g (ContinuousPath.exitTimeTrunc U t path) path - phi x := by
    intro path
    rw [aux_fsrkb_stopDynkin_N, aux_fsrkb_stopDynkin_trunc_sub hUQ t path,
      aux_fsrkb_stopDynkin_I]
    ring
  rw [integral_congr_ae (ae_of_all _ hpt), integral_sub hint (integrable_const _), hEq]
  simp

end KbStopDynkin

section KbExhaust

open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

/-- The interior cube of side `r * (k+1)/(k+2)`. -/
noncomputable def aux_fsrkb_innerCube {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (k : ℕ) : TopologicalSpace.Opens (SpatialCoordinates d) :=
  centeredCube z (r * ((k + 1 : ℝ) / (k + 2))) (by positivity)

theorem aux_fsrkb_Exhaust_innerCube_coe {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (k : ℕ) :
    (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) =
      Metric.ball z (r * ((k + 1 : ℝ) / (k + 2)) / 2) := rfl

theorem aux_fsrkb_Exhaust_cube_coe {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    (centeredCube z r hr : Set (SpatialCoordinates d)) = Metric.ball z (r / 2) := rfl

theorem aux_fsrkb_Exhaust_radius_lt (r : ℝ) (hr : 0 < r) (k : ℕ) :
    r * ((k + 1 : ℝ) / (k + 2)) / 2 < r / 2 := by
  have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have h1 : ((k : ℝ) + 1) / (k + 2) < 1 := by
    rw [div_lt_one hk]; linarith only
  have h2 : r * (((k : ℝ) + 1) / (k + 2)) < r * 1 := mul_lt_mul_of_pos_left h1 hr
  linarith only [h2]

theorem aux_fsrkb_Exhaust_radius_eventually (r : ℝ) (hr : 0 < r) (a : ℝ) (ha : a < r / 2) :
    ∃ k : ℕ, ∀ m : ℕ, k ≤ m → a < r * ((m + 1 : ℝ) / (m + 2)) / 2 := by
  have hδ : 0 < (r / 2 - a) / (r / 2) := div_pos (by linarith only [ha]) (by linarith only [hr])
  rcases exists_nat_one_div_lt hδ with ⟨k, hk⟩
  refine ⟨k, fun m hm => ?_⟩
  have hm' : (k : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hle : 1 / ((m : ℝ) + 2) ≤ 1 / ((k : ℝ) + 1) :=
    one_div_le_one_div_of_le hkpos (by linarith only [hm'])
  have hlt : 1 / ((m : ℝ) + 2) < (r / 2 - a) / (r / 2) := lt_of_le_of_lt hle hk
  have heq : r * (((m : ℝ) + 1) / (m + 2)) / 2 = r / 2 - (r / 2) * (1 / ((m : ℝ) + 2)) := by
    field_simp
    ring
  rw [heq]
  have hmul : (r / 2) * (1 / ((m : ℝ) + 2)) < (r / 2) * ((r / 2 - a) / (r / 2)) :=
    mul_lt_mul_of_pos_left hlt (by linarith only [hr])
  have hcancel : (r / 2) * ((r / 2 - a) / (r / 2)) = r / 2 - a := by
    field_simp
  linarith only [hmul, hcancel]

theorem aux_fsrkb_innerCube_subset {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (k : ℕ) :
    closure (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  rw [aux_fsrkb_Exhaust_innerCube_coe, aux_fsrkb_Exhaust_cube_coe]
  exact (Metric.closure_ball_subset_closedBall).trans
    (Metric.closedBall_subset_ball (aux_fsrkb_Exhaust_radius_lt r hr k))

theorem aux_fsrkb_Exhaust_innerCube_sub {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (k : ℕ) :
    (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)) :=
  subset_closure.trans (aux_fsrkb_innerCube_subset z r hr k)

theorem aux_fsrkb_iUnion_innerCube {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    (⋃ k, (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d))) =
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun k => aux_fsrkb_Exhaust_innerCube_sub z r hr k
  · intro y hy
    rw [aux_fsrkb_Exhaust_cube_coe, Metric.mem_ball] at hy
    rcases aux_fsrkb_Exhaust_radius_eventually r hr (dist y z) hy with ⟨k, hk⟩
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    rw [aux_fsrkb_Exhaust_innerCube_coe, Metric.mem_ball]
    exact hk k le_rfl

/-- Before the exit time from the cube, the path is eventually inside every interior cube up to
that time. -/
theorem aux_fsrkb_Exhaust_eventually_lt_exitTime {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (ω : DiffusionPath d) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) <
      ContinuousPath.exitTime (centeredCube z r hr : Set (SpatialCoordinates d)) ω) :
    ∀ᶠ k in atTop, (t : ℝ≥0∞) <
      ContinuousPath.exitTime (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) ω := by
  have hcompact : IsCompact ((ω : ℝ≥0 → SpatialCoordinates d) '' Set.Icc 0 t) :=
    isCompact_Icc.image ω.continuous
  have hsub : (ω : ℝ≥0 → SpatialCoordinates d) '' Set.Icc 0 t ⊆ Metric.ball z (r / 2) := by
    rintro _ ⟨s, hs, rfl⟩
    have hs' : (s : ℝ≥0∞) < ContinuousPath.exitTime
        (centeredCube z r hr : Set (SpatialCoordinates d)) ω :=
      lt_of_le_of_lt (by exact_mod_cast hs.2) ht
    exact ContinuousPath.mem_of_lt_exitTime _ ω s hs'
  rcases exists_lt_subset_ball hcompact.isClosed hsub with ⟨r', hr', hsub'⟩
  rcases aux_fsrkb_Exhaust_radius_eventually r hr r' hr' with ⟨k, hk⟩
  refine Filter.eventually_atTop.mpr ⟨k, fun m hm => ?_⟩
  by_contra hle
  rw [not_lt, ContinuousPath.exitTime_le_iff_mem_hitsSetBy _
    (aux_fsrkb_innerCube z r hr m).isOpen t ω] at hle
  rcases hle with ⟨s, hs⟩
  apply hs
  rw [aux_fsrkb_Exhaust_innerCube_coe]
  exact Metric.ball_subset_ball (hk m hm).le
    (hsub' ⟨s, Set.mem_Icc.mpr ⟨zero_le _, s.2⟩, rfl⟩)


/-- Joint measurability of the killed occupation integrand. -/
theorem aux_fsrkb_Exhaust_measurable_integrand {d : ℕ} (U : Set (SpatialCoordinates d))
    (hU : IsOpen U) (lam : ℝ) (f : SpatialCoordinates d → ℝ) (hf : Measurable f) :
    Measurable (Function.uncurry fun (ω : DiffusionPath d) (t : ℝ) =>
      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U ω}
        (fun s => Real.exp (-lam * s) * f (ω (Real.toNNReal s))) t) := by
  have hset : MeasurableSet {p : DiffusionPath d × ℝ |
      ENNReal.ofReal p.2 < ContinuousPath.exitTime U p.1} :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd)
      ((ContinuousPath.measurable_exitTime U hU).comp measurable_fst)
  have hev : Measurable fun p : DiffusionPath d × ℝ => p.1 (Real.toNNReal p.2) :=
    continuous_eval.measurable.comp
      (measurable_fst.prodMk (measurable_real_toNNReal.comp measurable_snd))
  have hval : Measurable fun p : DiffusionPath d × ℝ =>
      Real.exp (-lam * p.2) * f (p.1 (Real.toNNReal p.2)) :=
    (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_snd)).mul
      (hf.comp hev)
  have heq : (Function.uncurry fun (ω : DiffusionPath d) (t : ℝ) =>
      Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U ω}
        (fun s => Real.exp (-lam * s) * f (ω (Real.toNNReal s))) t) =
      Set.indicator {p : DiffusionPath d × ℝ | ENNReal.ofReal p.2 < ContinuousPath.exitTime U p.1}
        (fun p : DiffusionPath d × ℝ => Real.exp (-lam * p.2) * f (p.1 (Real.toNNReal p.2))) := by
    funext p
    rcases p with ⟨ω, t⟩
    simp only [Function.uncurry_apply_pair, Set.indicator, Set.mem_setOf_eq]
  rw [heq]
  exact hval.indicator hset

theorem aux_fsrkb_Exhaust_norm_le {d : ℕ} (S : Set ℝ) (lam : ℝ) (f : SpatialCoordinates d → ℝ)
    (B : ℝ) (hB : ∀ y, |f y| ≤ B) (ω : DiffusionPath d) (t : ℝ) :
    ‖S.indicator (fun s => Real.exp (-lam * s) * f (ω (Real.toNNReal s))) t‖ ≤
      B * Real.exp (-lam * t) := by
  refine (norm_indicator_le_norm_self _ t).trans ?_
  rw [Real.norm_eq_abs, abs_mul, Real.abs_exp, mul_comm]
  exact mul_le_mul_of_nonneg_right (hB _) (Real.exp_pos _).le

theorem aux_fsrkb_Exhaust_integrableOn_exp (lam : ℝ) (hlam : 0 < lam) (B : ℝ) :
    IntegrableOn (fun t : ℝ => B * Real.exp (-lam * t)) (Set.Ioi 0) :=
  (integrableOn_exp_mul_Ioi (by linarith only [hlam]) 0).const_mul B

theorem aux_fsrkb_Exhaust_integral_exp (lam : ℝ) (hlam : 0 < lam) (B : ℝ) :
    ∫ t in Set.Ioi (0 : ℝ), B * Real.exp (-lam * t) = B / lam := by
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith only [hlam]) 0]
  rw [mul_zero, Real.exp_zero, neg_div, div_neg, neg_neg, mul_one_div]

theorem aux_fsrkb_Exhaust_tendsto_indicator {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (lam : ℝ) (f : SpatialCoordinates d → ℝ) (ω : DiffusionPath d) (t : ℝ) :
    Tendsto (fun k => Set.indicator {s : ℝ | ENNReal.ofReal s <
        ContinuousPath.exitTime (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) ω}
        (fun s => Real.exp (-lam * s) * f (ω (Real.toNNReal s))) t) atTop
      (𝓝 (Set.indicator {s : ℝ | ENNReal.ofReal s <
        ContinuousPath.exitTime (centeredCube z r hr : Set (SpatialCoordinates d)) ω}
        (fun s => Real.exp (-lam * s) * f (ω (Real.toNNReal s))) t)) := by
  by_cases h : ENNReal.ofReal t <
      ContinuousPath.exitTime (centeredCube z r hr : Set (SpatialCoordinates d)) ω
  · have hev := aux_fsrkb_Exhaust_eventually_lt_exitTime z r hr ω (Real.toNNReal t) h
    rw [Set.indicator_of_mem (show t ∈ {s : ℝ | ENNReal.ofReal s <
        ContinuousPath.exitTime (centeredCube z r hr : Set (SpatialCoordinates d)) ω} from h)]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with k hk
    rw [Set.indicator_of_mem (show t ∈ {s : ℝ | ENNReal.ofReal s <
        ContinuousPath.exitTime (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) ω}
        from hk)]
  · rw [Set.indicator_of_notMem (show t ∉ {s : ℝ | ENNReal.ofReal s <
        ContinuousPath.exitTime (centeredCube z r hr : Set (SpatialCoordinates d)) ω} from h)]
    refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun k => ?_)
    have hk : t ∉ {s : ℝ | ENNReal.ofReal s <
        ContinuousPath.exitTime (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) ω} := by
      intro hk
      exact h (lt_of_lt_of_le hk
        (ContinuousPath.exitTime_mono (aux_fsrkb_Exhaust_innerCube_sub z r hr k) ω))
    exact (Set.indicator_of_notMem hk _).symm

/-- **Monotone exhaustion of the killed resolvent** for a nonnegative bounded measurable source. -/
theorem aux_fsrkb_killedRes_innerCube_tendsto {d : ℕ}
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (lam : ℝ) (hlam : 0 < lam)
    (f : SpatialCoordinates d → ℝ) (hf : aux_fsrkb_BddMeas f) (hf0 : ∀ y, 0 ≤ f y)
    (x : SpatialCoordinates d) :
    Tendsto (fun k => aux_fsrkb_killedRes K (aux_fsrkb_innerCube z r hr k) lam f x) atTop
      (𝓝 (aux_fsrkb_killedRes K (centeredCube z r hr) lam f x)) := by
  have _hf0 := hf0
  rcases hf with ⟨hfm, B, _hB0, hB⟩
  unfold aux_fsrkb_killedRes
  refine tendsto_integral_of_dominated_convergence (fun _ => B / lam) (fun k => ?_)
    (integrable_const _) (fun k => Filter.Eventually.of_forall fun ω => ?_)
    (Filter.Eventually.of_forall fun ω => ?_)
  · exact (StronglyMeasurable.integral_prod_right
      (aux_fsrkb_Exhaust_measurable_integrand _ (aux_fsrkb_innerCube z r hr k).isOpen lam f
        hfm).stronglyMeasurable).aestronglyMeasurable
  · rw [← aux_fsrkb_Exhaust_integral_exp lam hlam B]
    exact norm_integral_le_of_norm_le (aux_fsrkb_Exhaust_integrableOn_exp lam hlam B)
      (Filter.Eventually.of_forall fun t => aux_fsrkb_Exhaust_norm_le _ lam f B hB ω t)
  · exact tendsto_integral_of_dominated_convergence (fun t => B * Real.exp (-lam * t))
      (fun k => ((aux_fsrkb_Exhaust_measurable_integrand _
        (aux_fsrkb_innerCube z r hr k).isOpen lam f hfm).comp
          (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (aux_fsrkb_Exhaust_integrableOn_exp lam hlam B)
      (fun k => Filter.Eventually.of_forall fun t => aux_fsrkb_Exhaust_norm_le _ lam f B hB ω t)
      (Filter.Eventually.of_forall fun t =>
        aux_fsrkb_Exhaust_tendsto_indicator z r hr lam f ω t)

end KbExhaust

section KbSymm

open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

variable {d : ℕ}

section FiniteDim

variable {α : Type*} [MeasurableSpace α]

theorem aux_fsrkb_symm_isSFiniteKernel_fTK (P : SubMarkovKernelSemigroup α) :
    ∀ {n : ℕ} (times : FiniteOrderedTimes n),
      IsSFiniteKernel (SubMarkovKernelSemigroup.finiteTimeKernel P times)
  | 0, times => by
      rw [SubMarkovKernelSemigroup.finiteTimeKernel_zero]; infer_instance
  | n + 1, times => by
      haveI : IsSFiniteKernel (SubMarkovKernelSemigroup.finiteTimeKernel P times.relativeTail) :=
        aux_fsrkb_symm_isSFiniteKernel_fTK P times.relativeTail
      haveI : IsFiniteKernel (P (times 0)) := (P.isSubMarkovKernel (times 0)).isFiniteKernel
      rw [SubMarkovKernelSemigroup.finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map]
      infer_instance

theorem aux_fsrkb_symm_lintegral_fTK_succ (P : SubMarkovKernelSemigroup α) {n : ℕ}
    (times : FiniteOrderedTimes (n + 1)) (x : α) {G : (Fin (n + 1) → α) → ℝ≥0∞}
    (hG : Measurable G) :
    ∫⁻ p, G p ∂(SubMarkovKernelSemigroup.finiteTimeKernel P times x) =
      ∫⁻ y, ∫⁻ q, G (Fin.cons y q)
        ∂(SubMarkovKernelSemigroup.finiteTimeKernel P times.relativeTail y) ∂(P (times 0) x) := by
  haveI : IsSFiniteKernel (SubMarkovKernelSemigroup.finiteTimeKernel P times.relativeTail) :=
    aux_fsrkb_symm_isSFiniteKernel_fTK P times.relativeTail
  haveI : IsFiniteKernel (P (times 0)) := (P.isSubMarkovKernel (times 0)).isFiniteKernel
  rw [SubMarkovKernelSemigroup.finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map,
    Kernel.lintegral_map _ measurable_finCons _ hG,
    Kernel.lintegral_compProd _ _ _ (f := fun z : α × (Fin n → α) => G (Fin.cons z.1 z.2))
      (hG.comp measurable_finCons)]
  simp only [Kernel.prodMkLeft_apply]

/-- Equally spaced times `(j+1) h`, `j < n`. -/
noncomputable def aux_fsrkb_symm_stepTimes (h : ℝ≥0) (hh : 0 < h) (n : ℕ) :
    FiniteOrderedTimes n :=
  OrderEmbedding.ofStrictMono (fun j : Fin n => (((j : ℕ) : ℝ≥0) + 1) * h) (by
    intro i j hij
    have h1 : ((i : ℕ) : ℝ≥0) < ((j : ℕ) : ℝ≥0) := by exact_mod_cast hij
    exact mul_lt_mul_of_pos_right (by simpa using h1) hh)

/-- Equally spaced times `i h`, `i ≤ n`. -/
noncomputable def aux_fsrkb_symm_meshTimes (h : ℝ≥0) (hh : 0 < h) (n : ℕ) :
    FiniteOrderedTimes (n + 1) :=
  OrderEmbedding.ofStrictMono (fun i : Fin (n + 1) => ((i : ℕ) : ℝ≥0) * h) (by
    intro i j hij
    have h1 : ((i : ℕ) : ℝ≥0) < ((j : ℕ) : ℝ≥0) := by exact_mod_cast hij
    exact mul_lt_mul_of_pos_right h1 hh)

theorem aux_fsrkb_symm_meshTimes_apply (h : ℝ≥0) (hh : 0 < h) (n : ℕ) (i : Fin (n + 1)) :
    aux_fsrkb_symm_meshTimes h hh n i = ((i : ℕ) : ℝ≥0) * h := rfl

theorem aux_fsrkb_symm_meshTimes_zero (h : ℝ≥0) (hh : 0 < h) (n : ℕ) :
    aux_fsrkb_symm_meshTimes h hh n 0 = 0 := by
  simp [aux_fsrkb_symm_meshTimes]

theorem aux_fsrkb_symm_stepTimes_zero (h : ℝ≥0) (hh : 0 < h) (n : ℕ) :
    aux_fsrkb_symm_stepTimes h hh (n + 1) 0 = h := by
  simp [aux_fsrkb_symm_stepTimes]

theorem aux_fsrkb_symm_relTail_meshTimes (h : ℝ≥0) (hh : 0 < h) (n : ℕ) :
    (aux_fsrkb_symm_meshTimes h hh n).relativeTail = aux_fsrkb_symm_stepTimes h hh n := by
  apply DFunLike.ext _ _
  intro j
  simp [FiniteOrderedTimes.relativeTail_apply, aux_fsrkb_symm_meshTimes, aux_fsrkb_symm_stepTimes]

theorem aux_fsrkb_symm_relTail_stepTimes (h : ℝ≥0) (hh : 0 < h) (n : ℕ) :
    (aux_fsrkb_symm_stepTimes h hh (n + 1)).relativeTail = aux_fsrkb_symm_stepTimes h hh n := by
  apply DFunLike.ext _ _
  intro j
  simp only [FiniteOrderedTimes.relativeTail_apply, aux_fsrkb_symm_stepTimes,
    OrderEmbedding.coe_ofStrictMono, Fin.val_succ, Fin.val_zero, Nat.cast_add, Nat.cast_one,
    Nat.cast_zero, zero_add, one_mul]
  rw [add_mul, add_mul, one_mul, add_tsub_cancel_right]

/-- The symmetric mesh operator `a ↦ 1_F · P_h (1_F · a)`. -/
noncomputable def aux_fsrkb_symm_S (P : SubMarkovKernelSemigroup α) (h : ℝ≥0) (F : Set α)
    (a : α → ℝ≥0∞) : α → ℝ≥0∞ :=
  F.indicator (fun x => ∫⁻ y, F.indicator a y ∂(P h x))

theorem aux_fsrkb_symm_S_apply (P : SubMarkovKernelSemigroup α) (h : ℝ≥0) (F : Set α)
    (a : α → ℝ≥0∞) (x : α) :
    aux_fsrkb_symm_S P h F a x = F.indicator (fun x => ∫⁻ y, F.indicator a y ∂(P h x)) x := rfl

theorem aux_fsrkb_symm_S_measurable (P : SubMarkovKernelSemigroup α) (h : ℝ≥0) {F : Set α}
    (hF : MeasurableSet F) {a : α → ℝ≥0∞} (ha : Measurable a) :
    Measurable (aux_fsrkb_symm_S P h F a) :=
  (Measurable.lintegral_kernel (ha.indicator hF)).indicator hF

theorem aux_fsrkb_symm_iter_measurable (P : SubMarkovKernelSemigroup α) (h : ℝ≥0) {F : Set α}
    (hF : MeasurableSet F) (n : ℕ) {a : α → ℝ≥0∞} (ha : Measurable a) :
    Measurable ((aux_fsrkb_symm_S P h F)^[n] a) := by
  induction n generalizing a with
  | zero => simpa using ha
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih (aux_fsrkb_symm_S_measurable P h hF ha)

theorem aux_fsrkb_symm_indicator_iter (P : SubMarkovKernelSemigroup α) (h : ℝ≥0) (F : Set α)
    (n : ℕ) (b : α → ℝ≥0∞) :
    F.indicator ((aux_fsrkb_symm_S P h F)^[n] (F.indicator b)) =
      (aux_fsrkb_symm_S P h F)^[n] (F.indicator b) := by
  cases n with
  | zero => simp
  | succ n =>
      rw [Function.iterate_succ_apply']
      simp [aux_fsrkb_symm_S]

omit [MeasurableSpace α] in
/-- The mesh integrand on `n+1` ordered coordinates. -/
noncomputable def aux_fsrkb_symm_G (F : Set α) (b : α → ℝ≥0∞) (n : ℕ)
    (p : Fin (n + 1) → α) : ℝ≥0∞ :=
  (∏ i, F.indicator 1 (p i)) * b (p (Fin.last n))

theorem aux_fsrkb_symm_G_measurable {F : Set α} (hF : MeasurableSet F) {b : α → ℝ≥0∞}
    (hb : Measurable b) (n : ℕ) : Measurable (aux_fsrkb_symm_G F b n) := by
  unfold aux_fsrkb_symm_G
  refine Measurable.mul ?_ (hb.comp (measurable_pi_apply _))
  exact Finset.measurable_prod _ fun i _ => (measurable_one.indicator hF).comp (measurable_pi_apply i)

omit [MeasurableSpace α] in
theorem aux_fsrkb_symm_G_cons_succ (F : Set α) (b : α → ℝ≥0∞) (n : ℕ) (y : α)
    (q : Fin (n + 1) → α) :
    aux_fsrkb_symm_G F b (n + 1) (Fin.cons y q) = F.indicator 1 y * aux_fsrkb_symm_G F b n q := by
  unfold aux_fsrkb_symm_G
  rw [Fin.prod_univ_succ, ← Fin.succ_last, Fin.cons_succ, Fin.cons_zero, mul_assoc]
  simp only [Fin.cons_succ]

omit [MeasurableSpace α] in
theorem aux_fsrkb_symm_G_cons_zero (F : Set α) (b : α → ℝ≥0∞) (y : α) (q : Fin 0 → α) :
    aux_fsrkb_symm_G F b 0 (Fin.cons y q) = F.indicator b y := by
  unfold aux_fsrkb_symm_G
  simp only [Fin.last_zero, Fin.cons_zero]
  by_cases hy : y ∈ F <;> simp [hy]

variable [MeasurableSingletonClass α]

omit [MeasurableSingletonClass α] in
theorem aux_fsrkb_symm_step_formula (P : SubMarkovKernelSemigroup α) (h : ℝ≥0) (hh : 0 < h)
    {F : Set α} (hF : MeasurableSet F) {b : α → ℝ≥0∞} (hb : Measurable b) (n : ℕ) (x : α) :
    ∫⁻ q, aux_fsrkb_symm_G F b n q
        ∂(SubMarkovKernelSemigroup.finiteTimeKernel P (aux_fsrkb_symm_stepTimes h hh (n + 1)) x) =
      ∫⁻ y, (aux_fsrkb_symm_S P h F)^[n] (F.indicator b) y ∂(P h x) := by
  induction n generalizing x with
  | zero =>
      rw [aux_fsrkb_symm_lintegral_fTK_succ P _ x (aux_fsrkb_symm_G_measurable hF hb 0),
        aux_fsrkb_symm_stepTimes_zero]
      refine lintegral_congr fun y => ?_
      simp only [aux_fsrkb_symm_G_cons_zero, SubMarkovKernelSemigroup.finiteTimeKernel_zero,
        Kernel.const_apply, lintegral_const, measure_univ, mul_one, Function.iterate_zero, id]
  | succ n ih =>
      rw [aux_fsrkb_symm_lintegral_fTK_succ P _ x (aux_fsrkb_symm_G_measurable hF hb (n + 1)),
        aux_fsrkb_symm_stepTimes_zero, aux_fsrkb_symm_relTail_stepTimes]
      refine lintegral_congr fun y => ?_
      simp only [aux_fsrkb_symm_G_cons_succ]
      rw [lintegral_const_mul _ (aux_fsrkb_symm_G_measurable hF hb n), ih y,
        Function.iterate_succ_apply', aux_fsrkb_symm_S_apply, aux_fsrkb_symm_indicator_iter]
      by_cases hy : y ∈ F <;> simp [hy]

theorem aux_fsrkb_symm_mesh_formula (P : SubMarkovKernelSemigroup α) (h : ℝ≥0) (hh : 0 < h)
    {F : Set α} (hF : MeasurableSet F) {b : α → ℝ≥0∞} (hb : Measurable b) (n : ℕ) (x : α) :
    ∫⁻ p, aux_fsrkb_symm_G F b n p
        ∂(SubMarkovKernelSemigroup.finiteTimeKernel P (aux_fsrkb_symm_meshTimes h hh n) x) =
      (aux_fsrkb_symm_S P h F)^[n] (F.indicator b) x := by
  rw [aux_fsrkb_symm_lintegral_fTK_succ P _ x (aux_fsrkb_symm_G_measurable hF hb n),
    aux_fsrkb_symm_meshTimes_zero, P.kernel_zero, Kernel.id_apply, lintegral_dirac,
    aux_fsrkb_symm_relTail_meshTimes]
  cases n with
  | zero =>
      simp only [aux_fsrkb_symm_G_cons_zero, SubMarkovKernelSemigroup.finiteTimeKernel_zero,
        Kernel.const_apply, lintegral_const, measure_univ, mul_one, Function.iterate_zero, id]
  | succ n =>
      simp only [aux_fsrkb_symm_G_cons_succ]
      rw [lintegral_const_mul _ (aux_fsrkb_symm_G_measurable hF hb n),
        aux_fsrkb_symm_step_formula P h hh hF hb n x,
        Function.iterate_succ_apply', aux_fsrkb_symm_S_apply, aux_fsrkb_symm_indicator_iter]
      by_cases hx : x ∈ F <;> simp [hx]

theorem aux_fsrkb_symm_two_mul_le (u v : ℝ≥0∞) : 2 * (u * v) ≤ u * u + v * v := by
  rcases eq_or_ne u ⊤ with rfl | hu
  · simp
  rcases eq_or_ne v ⊤ with rfl | hv
  · simp
  lift u to ℝ≥0 using hu
  lift v to ℝ≥0 using hv
  have h := two_mul_le_add_sq u v
  simp only [sq] at h
  rw [← mul_assoc]
  exact_mod_cast h

section Symmetry


theorem aux_fsrkb_symm_S_symm (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (μ : Measure (SpatialCoordinates d)) (hsym : SemigroupSymmetric P μ) (h : ℝ≥0)
    {F : Set (SpatialCoordinates d)} (hF : MeasurableSet F) {a b : SpatialCoordinates d → ℝ≥0∞}
    (ha : Measurable a) (hb : Measurable b) :
    ∫⁻ x, b x * aux_fsrkb_symm_S P h F a x ∂μ = ∫⁻ x, a x * aux_fsrkb_symm_S P h F b x ∂μ := by
  have key := hsym h (F.indicator b) (F.indicator a) (hb.indicator hF) (ha.indicator hF)
  have e1 : ∀ x, b x * aux_fsrkb_symm_S P h F a x =
      F.indicator b x * ∫⁻ y, F.indicator a y ∂(P h x) := by
    intro x; by_cases hx : x ∈ F <;> simp [aux_fsrkb_symm_S, hx]
  have e2 : ∀ x, a x * aux_fsrkb_symm_S P h F b x =
      F.indicator a x * ∫⁻ y, F.indicator b y ∂(P h x) := by
    intro x; by_cases hx : x ∈ F <;> simp [aux_fsrkb_symm_S, hx]
  simp_rw [e1, e2]
  exact key

theorem aux_fsrkb_symm_iter_symm (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (μ : Measure (SpatialCoordinates d)) (hsym : SemigroupSymmetric P μ) (h : ℝ≥0)
    {F : Set (SpatialCoordinates d)} (hF : MeasurableSet F) (n : ℕ) :
    ∀ {a b : SpatialCoordinates d → ℝ≥0∞}, Measurable a → Measurable b →
      ∫⁻ x, b x * (aux_fsrkb_symm_S P h F)^[n] a x ∂μ =
        ∫⁻ x, a x * (aux_fsrkb_symm_S P h F)^[n] b x ∂μ := by
  induction n with
  | zero =>
      intro a b _ _
      simp only [Function.iterate_zero, id]
      exact lintegral_congr fun x => mul_comm _ _
  | succ n ih =>
      intro a b ha hb
      rw [Function.iterate_succ_apply, ih (aux_fsrkb_symm_S_measurable P h hF ha) hb]
      have e : ∫⁻ x, aux_fsrkb_symm_S P h F a x * (aux_fsrkb_symm_S P h F)^[n] b x ∂μ =
          ∫⁻ x, (aux_fsrkb_symm_S P h F)^[n] b x * aux_fsrkb_symm_S P h F a x ∂μ :=
        lintegral_congr fun x => mul_comm _ _
      rw [e, aux_fsrkb_symm_S_symm P μ hsym h hF ha
        (aux_fsrkb_symm_iter_measurable P h hF n hb)]
      simp only [Function.iterate_succ_apply']

theorem aux_fsrkb_symm_iter_even (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (μ : Measure (SpatialCoordinates d)) (hsym : SemigroupSymmetric P μ) (h : ℝ≥0)
    {F : Set (SpatialCoordinates d)} (hF : MeasurableSet F) (k : ℕ)
    {a b : SpatialCoordinates d → ℝ≥0∞} (ha : Measurable a) (hb : Measurable b) :
    ∫⁻ x, b x * (aux_fsrkb_symm_S P h F)^[2 * k] a x ∂μ =
      ∫⁻ x, (aux_fsrkb_symm_S P h F)^[k] b x * (aux_fsrkb_symm_S P h F)^[k] a x ∂μ := by
  rw [two_mul, Function.iterate_add_apply,
    aux_fsrkb_symm_iter_symm P μ hsym h hF k (aux_fsrkb_symm_iter_measurable P h hF k ha) hb]
  exact lintegral_congr fun x => mul_comm _ _

theorem aux_fsrkb_symm_iter_pos (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (μ : Measure (SpatialCoordinates d)) (hsym : SemigroupSymmetric P μ) (h : ℝ≥0)
    {F : Set (SpatialCoordinates d)} (hF : MeasurableSet F) (k : ℕ)
    {a b : SpatialCoordinates d → ℝ≥0∞} (ha : Measurable a) (hb : Measurable b) :
    2 * ∫⁻ x, b x * (aux_fsrkb_symm_S P h F)^[2 * k] a x ∂μ ≤
      ∫⁻ x, a x * (aux_fsrkb_symm_S P h F)^[2 * k] a x ∂μ +
        ∫⁻ x, b x * (aux_fsrkb_symm_S P h F)^[2 * k] b x ∂μ := by
  rw [aux_fsrkb_symm_iter_even P μ hsym h hF k ha hb, aux_fsrkb_symm_iter_even P μ hsym h hF k ha ha,
    aux_fsrkb_symm_iter_even P μ hsym h hF k hb hb]
  have hu := aux_fsrkb_symm_iter_measurable P h hF k ha
  have hv := aux_fsrkb_symm_iter_measurable P h hF k hb
  rw [← lintegral_const_mul _ (hv.mul hu), ← lintegral_add_left (hu.mul hu)]
  refine lintegral_mono fun x => ?_
  have := aux_fsrkb_symm_two_mul_le ((aux_fsrkb_symm_S P h F)^[k] b x)
    ((aux_fsrkb_symm_S P h F)^[k] a x)
  rw [add_comm] at this
  exact this

end Symmetry

end FiniteDim

section PathLevel


theorem aux_fsrkb_symm_map_finiteSetTimes
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hfdd : aux_fsrkb_Fdd K P)
    (I : Finset ℝ≥0) (x : SpatialCoordinates d) :
    (K x).map (fun (path : DiffusionPath d) (j : Fin I.card) =>
        path (SubMarkovKernelSemigroup.finiteSetTimes I j)) =
      SubMarkovKernelSemigroup.finiteTimeKernel P (SubMarkovKernelSemigroup.finiteSetTimes I) x := by
  have h1 := hfdd I x
  rw [SubMarkovKernelSemigroup.finiteSetKernel_eq_map,
    Kernel.map_apply _ (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I)] at h1
  let inv : (I → SpatialCoordinates d) → (Fin I.card → SpatialCoordinates d) :=
    fun q j => q (I.orderIsoOfFin rfl j)
  have hinv : Measurable inv := measurable_pi_lambda _ (fun j => measurable_pi_apply _)
  have h2 := congrArg (Measure.map inv) h1
  rw [Measure.map_map hinv (ContinuousPath.measurable_finsetEvaluation I),
    Measure.map_map hinv (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I)] at h2
  have hid : inv ∘ SubMarkovKernelSemigroup.orderedPathToFiniteSet I = id := by
    funext p j
    simp [inv, SubMarkovKernelSemigroup.orderedPathToFiniteSet]
  have hcomp : inv ∘ ContinuousPath.finsetEvaluation I =
      fun (path : DiffusionPath d) (j : Fin I.card) =>
        path (SubMarkovKernelSemigroup.finiteSetTimes I j) := by
    funext path j
    simp only [Function.comp_apply, inv, ContinuousPath.finsetEvaluation,
      ContinuousPath.finiteEvaluation, SubMarkovKernelSemigroup.finiteSetTimes]
    rw [Finset.coe_orderIsoOfFin_apply]
  rw [hid, Measure.map_id, hcomp] at h2
  exact h2

theorem aux_fsrkb_symm_map_times
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hfdd : aux_fsrkb_Fdd K P)
    {n : ℕ} (times : FiniteOrderedTimes n) (x : SpatialCoordinates d) :
    (K x).map (fun (path : DiffusionPath d) (j : Fin n) => path (times j)) =
      SubMarkovKernelSemigroup.finiteTimeKernel P times x := by
  classical
  let I : Finset ℝ≥0 := Finset.univ.map times.toEmbedding
  have hcard : I.card = n := by simp [I]
  have key : ∀ (k : ℕ) (hk : I.card = k),
      (K x).map (fun (path : DiffusionPath d) (j : Fin k) => path (I.orderEmbOfFin hk j)) =
        SubMarkovKernelSemigroup.finiteTimeKernel P (I.orderEmbOfFin hk) x := by
    intro k hk
    subst hk
    exact aux_fsrkb_symm_map_finiteSetTimes K P hfdd I x
  have htimes : times = I.orderEmbOfFin hcard :=
    Finset.orderEmbOfFin_unique' hcard (fun j => by simp [I])
  have h3 := key n hcard
  rw [← htimes] at h3
  exact h3

theorem aux_fsrkb_symm_path_mesh_formula
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hfdd : aux_fsrkb_Fdd K P)
    (h : ℝ≥0) (hh : 0 < h) {F : Set (SpatialCoordinates d)} (hF : MeasurableSet F)
    {b : SpatialCoordinates d → ℝ≥0∞} (hb : Measurable b) (n : ℕ) (x : SpatialCoordinates d) :
    ∫⁻ path, aux_fsrkb_symm_G F b n (fun i => path (aux_fsrkb_symm_meshTimes h hh n i)) ∂(K x) =
      (aux_fsrkb_symm_S P h F)^[n] (F.indicator b) x := by
  have hmeas : Measurable (fun (path : DiffusionPath d) (i : Fin (n + 1)) =>
      path (aux_fsrkb_symm_meshTimes h hh n i)) :=
    measurable_pi_lambda _ (fun i =>
      ContinuousPath.measurable_coordinateProcess (alpha := SpatialCoordinates d) _)
  calc ∫⁻ path, aux_fsrkb_symm_G F b n (fun i => path (aux_fsrkb_symm_meshTimes h hh n i)) ∂(K x)
      = ∫⁻ p, aux_fsrkb_symm_G F b n p ∂((K x).map (fun (path : DiffusionPath d)
          (i : Fin (n + 1)) => path (aux_fsrkb_symm_meshTimes h hh n i))) :=
        (lintegral_map (aux_fsrkb_symm_G_measurable hF hb n) hmeas).symm
    _ = _ := by
        rw [aux_fsrkb_symm_map_times K P hfdd, aux_fsrkb_symm_mesh_formula P h hh hF hb n x]

/-- The dyadic mesh functional `∏_{i ≤ 2^m} 1_F(X_{i t/2^m}) · b(X_t)`. -/
noncomputable def aux_fsrkb_symm_meshFun (F : Set (SpatialCoordinates d)) (t : ℝ≥0) (m : ℕ)
    (b : SpatialCoordinates d → ℝ≥0∞) (path : DiffusionPath d) : ℝ≥0∞ :=
  (∏ i : Fin (2 ^ m + 1), F.indicator 1 (path (((i : ℕ) : ℝ≥0) * (t / 2 ^ m)))) * b (path t)

theorem aux_fsrkb_symm_meshFun_eq_G (F : Set (SpatialCoordinates d)) (t : ℝ≥0) (m : ℕ)
    (hh : 0 < t / 2 ^ m) (b : SpatialCoordinates d → ℝ≥0∞) (path : DiffusionPath d) :
    aux_fsrkb_symm_meshFun F t m b path =
      aux_fsrkb_symm_G F b (2 ^ m)
        (fun i => path (aux_fsrkb_symm_meshTimes (t / 2 ^ m) hh (2 ^ m) i)) := by
  unfold aux_fsrkb_symm_meshFun aux_fsrkb_symm_G
  simp only [aux_fsrkb_symm_meshTimes_apply, Fin.val_last]
  congr 3
  push_cast
  exact (mul_div_cancel₀ t (pow_ne_zero m two_ne_zero)).symm

theorem aux_fsrkb_symm_meshFun_measurable {F : Set (SpatialCoordinates d)} (hF : MeasurableSet F)
    (t : ℝ≥0) (m : ℕ) {b : SpatialCoordinates d → ℝ≥0∞} (hb : Measurable b) :
    Measurable (aux_fsrkb_symm_meshFun F t m b) := by
  unfold aux_fsrkb_symm_meshFun
  refine Measurable.mul ?_ (hb.comp
    (ContinuousPath.measurable_coordinateProcess (alpha := SpatialCoordinates d) t))
  exact Finset.measurable_prod _ fun i _ => (measurable_one.indicator hF).comp
    (ContinuousPath.measurable_coordinateProcess (alpha := SpatialCoordinates d) _)

theorem aux_fsrkb_symm_meshPair_eq
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hfdd : aux_fsrkb_Fdd K P)
    (μ : Measure (SpatialCoordinates d)) (U : Set (SpatialCoordinates d))
    {F : Set (SpatialCoordinates d)} (hF : MeasurableSet F) (hFU : F ⊆ U)
    (t : ℝ≥0) (ht : 0 < t) (m : ℕ) (a : SpatialCoordinates d → ℝ≥0∞)
    {b : SpatialCoordinates d → ℝ≥0∞} (hb : Measurable b) :
    ∫⁻ x in U, a x * ∫⁻ path, aux_fsrkb_symm_meshFun F t m b path ∂(K x) ∂μ =
      ∫⁻ x, F.indicator a x *
        (aux_fsrkb_symm_S P (t / 2 ^ m) F)^[2 ^ m] (F.indicator b) x ∂μ := by
  have hh : 0 < t / 2 ^ m := div_pos ht (pow_pos two_pos m)
  have e : ∀ x, a x * ∫⁻ path, aux_fsrkb_symm_meshFun F t m b path ∂(K x) =
      F.indicator a x * (aux_fsrkb_symm_S P (t / 2 ^ m) F)^[2 ^ m] (F.indicator b) x := by
    intro x
    simp_rw [aux_fsrkb_symm_meshFun_eq_G F t m hh b]
    rw [aux_fsrkb_symm_path_mesh_formula K P hfdd _ hh hF hb, ← aux_fsrkb_symm_indicator_iter]
    by_cases hx : x ∈ F <;> simp [hx]
  simp_rw [e]
  refine setLIntegral_eq_of_support_subset ?_
  intro x hx
  by_contra hxU
  apply hx
  simp [Set.indicator_of_notMem (fun h => hxU (hFU h))]

end PathLevel

section Limits


/-- Bounded measurable nonnegative functions. -/
def aux_fsrkb_symm_Bdd (a : SpatialCoordinates d → ℝ≥0∞) : Prop :=
  Measurable a ∧ ∃ C : ℝ≥0, ∀ x, a x ≤ C

/-- A symmetric pairing satisfying the Cauchy-Schwarz type inequality `2Q(a,b) ≤ Q(a,a)+Q(b,b)`. -/
def aux_fsrkb_symm_Good
    (Q : (SpatialCoordinates d → ℝ≥0∞) → (SpatialCoordinates d → ℝ≥0∞) → ℝ≥0∞) : Prop :=
  ∀ a b, aux_fsrkb_symm_Bdd a → aux_fsrkb_symm_Bdd b →
    Q a b = Q b a ∧ 2 * Q a b ≤ Q a a + Q b b

theorem aux_fsrkb_symm_good_of_tendsto
    (Qm : ℕ → (SpatialCoordinates d → ℝ≥0∞) → (SpatialCoordinates d → ℝ≥0∞) → ℝ≥0∞)
    (Q : (SpatialCoordinates d → ℝ≥0∞) → (SpatialCoordinates d → ℝ≥0∞) → ℝ≥0∞)
    (hlim : ∀ a b, aux_fsrkb_symm_Bdd a → aux_fsrkb_symm_Bdd b →
      Tendsto (fun m => Qm m a b) atTop (𝓝 (Q a b)))
    (hgood : ∀ᶠ m in atTop, aux_fsrkb_symm_Good (Qm m)) :
    aux_fsrkb_symm_Good Q := by
  intro a b ha hb
  have hab := hlim a b ha hb
  have hba := hlim b a hb ha
  have haa := hlim a a ha ha
  have hbb := hlim b b hb hb
  constructor
  · refine tendsto_nhds_unique hab (hba.congr' ?_)
    filter_upwards [hgood] with m hm
    exact ((hm a b ha hb).1).symm
  · refine le_of_tendsto_of_tendsto (ENNReal.Tendsto.const_mul hab (Or.inr ENNReal.ofNat_ne_top))
      (haa.add hbb) ?_
    filter_upwards [hgood] with m hm
    exact (hm a b ha hb).2

/-- The pairing `∫_U a(x) E_x[Φ] dμ`. -/
noncomputable def aux_fsrkb_symm_pair
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) (μ : Measure (SpatialCoordinates d))
    (U : Set (SpatialCoordinates d)) (Φ : DiffusionPath d → ℝ≥0∞)
    (a : SpatialCoordinates d → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x in U, a x * ∫⁻ path, Φ path ∂(K x) ∂μ

theorem aux_fsrkb_symm_pair_tendsto
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (μ : Measure (SpatialCoordinates d)) (U : Set (SpatialCoordinates d)) (hμU : μ U ≠ ⊤)
    (Φm : ℕ → DiffusionPath d → ℝ≥0∞) (Φ : DiffusionPath d → ℝ≥0∞)
    (hmeas : ∀ m, Measurable (Φm m)) (C : ℝ≥0) (hbound : ∀ m path, Φm m path ≤ C)
    (hlim : ∀ path, Tendsto (fun m => Φm m path) atTop (𝓝 (Φ path)))
    {a : SpatialCoordinates d → ℝ≥0∞} (ha : aux_fsrkb_symm_Bdd a) :
    Tendsto (fun m => aux_fsrkb_symm_pair K μ U (Φm m) a) atTop
      (𝓝 (aux_fsrkb_symm_pair K μ U Φ a)) := by
  rcases ha with ⟨ha_meas, Ca, hCa⟩
  have hinner : ∀ x, Tendsto (fun m => ∫⁻ path, Φm m path ∂(K x)) atTop
      (𝓝 (∫⁻ path, Φ path ∂(K x))) := by
    intro x
    refine tendsto_lintegral_of_dominated_convergence (fun _ => (C : ℝ≥0∞)) hmeas
      (fun m => ae_of_all _ (hbound m)) ?_ (ae_of_all _ hlim)
    simp
  have hbd : ∀ m x, ∫⁻ path, Φm m path ∂(K x) ≤ C := by
    intro m x
    calc ∫⁻ path, Φm m path ∂(K x) ≤ ∫⁻ _path, (C : ℝ≥0∞) ∂(K x) := lintegral_mono (hbound m)
      _ = C := by simp
  refine tendsto_lintegral_of_dominated_convergence (fun _ => (Ca : ℝ≥0∞) * C)
    (fun m => ha_meas.mul (Measurable.lintegral_kernel (hmeas m)))
    (fun m => ae_of_all _ (fun x => mul_le_mul' (hCa x) (hbd m x))) ?_ ?_
  · rw [lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top) hμU
  · refine ae_of_all _ (fun x => ENNReal.Tendsto.const_mul (hinner x) (Or.inr ?_))
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top (hCa x)

end Limits

section Approx


/-- `1{X_s ∈ F, s ≤ t} b(X_t)`. -/
noncomputable def aux_fsrkb_symm_closedFun (F : Set (SpatialCoordinates d)) (t : ℝ≥0)
    (b : SpatialCoordinates d → ℝ≥0∞) (path : DiffusionPath d) : ℝ≥0∞ :=
  {path : DiffusionPath d | ∀ s ≤ t, path s ∈ F}.indicator (fun path => b (path t)) path

/-- `1{t < τ_U} b(X_t)`. -/
noncomputable def aux_fsrkb_symm_killedFun (U : Set (SpatialCoordinates d)) (t : ℝ≥0)
    (b : SpatialCoordinates d → ℝ≥0∞) (path : DiffusionPath d) : ℝ≥0∞ :=
  {path : DiffusionPath d | (t : ℝ≥0∞) < ContinuousPath.exitTime U path}.indicator
    (fun path => b (path t)) path

theorem aux_fsrkb_symm_lt_exitTime_iff (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (t : ℝ≥0) (path : DiffusionPath d) :
    (t : ℝ≥0∞) < ContinuousPath.exitTime U path ↔ ∀ s ≤ t, path s ∈ U := by
  rw [← not_le, ContinuousPath.exitTime_le_iff_mem_hitsSetBy U hU t path]
  simp only [ContinuousPath.hitsSetBy, Set.mem_setOf_eq, Set.mem_compl_iff, not_exists, not_not]
  constructor
  · intro h s hs
    exact h ⟨s, hs⟩
  · intro h s
    exact h s s.2

theorem aux_fsrkb_symm_mesh_eventually {F : Set (SpatialCoordinates d)} (hF : IsClosed F)
    (t : ℝ≥0) (ht : 0 < t) (b : SpatialCoordinates d → ℝ≥0∞) (path : DiffusionPath d) :
    ∀ᶠ m in atTop, aux_fsrkb_symm_meshFun F t m b path = aux_fsrkb_symm_closedFun F t b path := by
  by_cases hall : ∀ s ≤ t, path s ∈ F
  · refine Eventually.of_forall fun m => ?_
    unfold aux_fsrkb_symm_meshFun aux_fsrkb_symm_closedFun
    rw [Set.indicator_of_mem (show path ∈ {path : DiffusionPath d | ∀ s ≤ t, path s ∈ F} from hall),
      Finset.prod_eq_one, one_mul]
    intro i _
    have hi : ((i : ℕ) : ℝ≥0) * (t / 2 ^ m) ≤ t := by
      have h1 : ((i : ℕ) : ℝ≥0) ≤ 2 ^ m := by
        have := Nat.lt_succ_iff.mp i.2
        exact_mod_cast this
      calc ((i : ℕ) : ℝ≥0) * (t / 2 ^ m) ≤ 2 ^ m * (t / 2 ^ m) :=
          mul_le_mul_of_nonneg_right h1 (zero_le _)
        _ = t := mul_div_cancel₀ t (pow_ne_zero m two_ne_zero)
    simp [Set.indicator_of_mem (hall _ hi)]
  · push_neg at hall
    obtain ⟨s, hst, hs⟩ := hall
    have hopen : IsOpen ((fun r : ℝ≥0 => path r) ⁻¹' Fᶜ) :=
      hF.isOpen_compl.preimage path.continuous
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen s hs
    obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt ((t : ℝ) / δ) one_lt_two
    have htM : (t : ℝ) / 2 ^ M < δ := by
      rw [div_lt_iff₀ hδ] at hM
      rw [div_lt_iff₀ (pow_pos two_pos M)]
      linarith only [hM]
    filter_upwards [eventually_ge_atTop M] with m hm
    have hnot : path ∉ {path : DiffusionPath d | ∀ s ≤ t, path s ∈ F} := by
      simp only [Set.mem_setOf_eq, not_forall]
      exact ⟨s, hst, hs⟩
    unfold aux_fsrkb_symm_meshFun aux_fsrkb_symm_closedFun
    rw [Set.indicator_of_notMem hnot]
    set h : ℝ≥0 := t / 2 ^ m with hh_def
    have hh : 0 < h := div_pos ht (pow_pos two_pos m)
    set k : ℕ := ⌊s / h⌋₊ with hk_def
    have hk1 : (k : ℝ≥0) * h ≤ s := by
      have := Nat.floor_le (zero_le (s / h))
      calc (k : ℝ≥0) * h ≤ s / h * h := mul_le_mul_of_nonneg_right this (zero_le _)
        _ = s := div_mul_cancel₀ s hh.ne'
    have hk2 : s < ((k : ℝ≥0) + 1) * h := by
      have := Nat.lt_floor_add_one (s / h)
      calc s = s / h * h := (div_mul_cancel₀ s hh.ne').symm
        _ < ((k : ℝ≥0) + 1) * h := mul_lt_mul_of_pos_right this hh
    have hk3 : k < 2 ^ m + 1 := by
      have h1 : (k : ℝ≥0) * h ≤ ((2 ^ m : ℕ) : ℝ≥0) * h := by
        calc (k : ℝ≥0) * h ≤ s := hk1
          _ ≤ t := hst
          _ = ((2 ^ m : ℕ) : ℝ≥0) * h := by
            push_cast
            exact (mul_div_cancel₀ t (pow_ne_zero m two_ne_zero)).symm
      have h2 : (k : ℝ≥0) ≤ ((2 ^ m : ℕ) : ℝ≥0) := le_of_mul_le_mul_right h1 hh
      have h3 : k ≤ 2 ^ m := by exact_mod_cast h2
      omega
    have hmem : path ((k : ℝ≥0) * h) ∈ Fᶜ := by
      apply hball
      rw [Metric.mem_ball, NNReal.dist_eq]
      have e1 : ((k : ℝ≥0) * h : ℝ≥0) ≤ s := hk1
      have e1' : (((k : ℝ≥0) * h : ℝ≥0) : ℝ) ≤ (s : ℝ) := by exact_mod_cast e1
      have e2 : (s : ℝ) < (((k : ℝ≥0) + 1) * h : ℝ≥0) := by exact_mod_cast hk2
      have e3 : ((h : ℝ≥0) : ℝ) ≤ (t : ℝ) / 2 ^ M := by
        rw [hh_def, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_two]
        exact div_le_div_of_nonneg_left t.2 (pow_pos two_pos M)
          (pow_le_pow_right₀ one_le_two hm)
      push_cast at e1' e2 ⊢
      rw [abs_sub_comm, abs_of_nonneg (by linarith only [e1'])]
      linarith only [e1', e2, e3, htM]
    rw [Finset.prod_eq_zero (i := ⟨k, hk3⟩) (Finset.mem_univ _), zero_mul]
    simp only
    rw [Set.indicator_of_notMem hmem]

theorem aux_fsrkb_symm_mesh_tendsto {F : Set (SpatialCoordinates d)} (hF : IsClosed F)
    (t : ℝ≥0) (ht : 0 < t) (b : SpatialCoordinates d → ℝ≥0∞) (path : DiffusionPath d) :
    Tendsto (fun m => aux_fsrkb_symm_meshFun F t m b path) atTop
      (𝓝 (aux_fsrkb_symm_closedFun F t b path)) :=
  tendsto_const_nhds.congr' (EventuallyEq.symm (aux_fsrkb_symm_mesh_eventually hF t ht b path))

theorem aux_fsrkb_symm_closedFun_measurable {F : Set (SpatialCoordinates d)} (hF : IsClosed F)
    (t : ℝ≥0) (ht : 0 < t) {b : SpatialCoordinates d → ℝ≥0∞} (hb : Measurable b) :
    Measurable (aux_fsrkb_symm_closedFun F t b) :=
  measurable_of_tendsto_metrizable
    (fun m => aux_fsrkb_symm_meshFun_measurable hF.measurableSet t m hb)
    (tendsto_pi_nhds.2 fun path => aux_fsrkb_symm_mesh_tendsto hF t ht b path)

theorem aux_fsrkb_symm_meshFun_le (F : Set (SpatialCoordinates d)) (t : ℝ≥0) (m : ℕ)
    {b : SpatialCoordinates d → ℝ≥0∞} {C : ℝ≥0} (hC : ∀ x, b x ≤ C) (path : DiffusionPath d) :
    aux_fsrkb_symm_meshFun F t m b path ≤ C := by
  unfold aux_fsrkb_symm_meshFun
  have hprod : (∏ i : Fin (2 ^ m + 1), F.indicator (1 : SpatialCoordinates d → ℝ≥0∞)
      (path (((i : ℕ) : ℝ≥0) * (t / 2 ^ m)))) ≤ 1 := by
    refine Finset.prod_le_one (fun _ _ => zero_le _) (fun i _ => ?_)
    by_cases hi : path (((i : ℕ) : ℝ≥0) * (t / 2 ^ m)) ∈ F <;> simp [hi]
  calc _ ≤ 1 * (C : ℝ≥0∞) := mul_le_mul' hprod (hC _)
    _ = C := one_mul _

theorem aux_fsrkb_symm_closedFun_le (F : Set (SpatialCoordinates d)) (t : ℝ≥0)
    {b : SpatialCoordinates d → ℝ≥0∞} {C : ℝ≥0} (hC : ∀ x, b x ≤ C) (path : DiffusionPath d) :
    aux_fsrkb_symm_closedFun F t b path ≤ C := by
  unfold aux_fsrkb_symm_closedFun
  by_cases hp : path ∈ {path : DiffusionPath d | ∀ s ≤ t, path s ∈ F}
  · rw [Set.indicator_of_mem hp]; exact hC _
  · rw [Set.indicator_of_notMem hp]; exact zero_le _

/-- Closed inner approximations of `U`. -/
def aux_fsrkb_symm_Fj (U : Set (SpatialCoordinates d)) (j : ℕ) : Set (SpatialCoordinates d) :=
  Metric.closedBall 0 j ∩ {y | Metric.ball y (1 / ((j : ℝ) + 1)) ⊆ U}

theorem aux_fsrkb_symm_Fj_isClosed (U : Set (SpatialCoordinates d)) (j : ℕ) :
    IsClosed (aux_fsrkb_symm_Fj U j) := by
  refine Metric.isClosed_closedBall.inter ?_
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro y hy
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.not_subset] at hy
  obtain ⟨z, hz, hzU⟩ := hy
  rw [Metric.mem_ball] at hz
  refine ⟨1 / ((j : ℝ) + 1) - dist z y, sub_pos.2 hz, fun y' hy' => ?_⟩
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.not_subset]
  refine ⟨z, ?_, hzU⟩
  rw [Metric.mem_ball] at hy' ⊢
  have := dist_triangle z y y'
  rw [dist_comm y y'] at this
  linarith only [this, hy']

theorem aux_fsrkb_symm_Fj_subset (U : Set (SpatialCoordinates d)) (j : ℕ) :
    aux_fsrkb_symm_Fj U j ⊆ U := by
  intro y hy
  exact hy.2 (Metric.mem_ball_self (by positivity))

theorem aux_fsrkb_symm_Fj_eventually (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (t : ℝ≥0) (path : DiffusionPath d) (hpath : ∀ s ≤ t, path s ∈ U) :
    ∀ᶠ j in atTop, ∀ s ≤ t, path s ∈ aux_fsrkb_symm_Fj U j := by
  have hC : IsCompact (path '' Set.Icc 0 t) := isCompact_Icc.image path.continuous
  have hCU : path '' Set.Icc 0 t ⊆ U := by
    rintro _ ⟨s, hs, rfl⟩
    exact hpath s hs.2
  obtain ⟨δ, hδ, hthick⟩ := hC.exists_thickening_subset_open hU hCU
  obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall 0
  obtain ⟨J, hJ⟩ := exists_nat_ge (max R (1 / δ))
  filter_upwards [eventually_ge_atTop J] with j hj s hs
  have hsC : path s ∈ path '' Set.Icc 0 t := ⟨s, ⟨zero_le s, hs⟩, rfl⟩
  have hjJ : (J : ℝ) ≤ j := by exact_mod_cast hj
  refine ⟨?_, ?_⟩
  · exact Metric.closedBall_subset_closedBall (le_trans (le_max_left _ _) (hJ.trans hjJ)) (hR hsC)
  · have h1 : 1 / δ < (j : ℝ) + 1 := by
      have := le_trans (le_max_right R (1 / δ)) (hJ.trans hjJ)
      linarith only [this]
    have h2 : 1 / ((j : ℝ) + 1) < δ := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hδ] at h1
      linarith only [h1]
    exact (Metric.ball_subset_ball h2.le).trans ((Metric.ball_subset_thickening hsC δ).trans hthick)

theorem aux_fsrkb_symm_closed_eventually (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (t : ℝ≥0) (b : SpatialCoordinates d → ℝ≥0∞) (path : DiffusionPath d) :
    ∀ᶠ j in atTop, aux_fsrkb_symm_closedFun (aux_fsrkb_symm_Fj U j) t b path =
      aux_fsrkb_symm_killedFun U t b path := by
  unfold aux_fsrkb_symm_closedFun aux_fsrkb_symm_killedFun
  by_cases hpath : ∀ s ≤ t, path s ∈ U
  · have hk : path ∈ {path : DiffusionPath d | (t : ℝ≥0∞) < ContinuousPath.exitTime U path} :=
      (aux_fsrkb_symm_lt_exitTime_iff U hU t path).2 hpath
    filter_upwards [aux_fsrkb_symm_Fj_eventually U hU t path hpath] with j hj
    rw [Set.indicator_of_mem hk,
      Set.indicator_of_mem (show path ∈ {path : DiffusionPath d | ∀ s ≤ t,
        path s ∈ aux_fsrkb_symm_Fj U j} from hj)]
  · have hk : path ∉ {path : DiffusionPath d | (t : ℝ≥0∞) < ContinuousPath.exitTime U path} :=
      fun h => hpath ((aux_fsrkb_symm_lt_exitTime_iff U hU t path).1 h)
    refine Eventually.of_forall fun j => ?_
    have hj : path ∉ {path : DiffusionPath d | ∀ s ≤ t, path s ∈ aux_fsrkb_symm_Fj U j} :=
      fun h => hpath fun s hs => aux_fsrkb_symm_Fj_subset U j (h s hs)
    rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hj]

end Approx

section GoodKilled


theorem aux_fsrkb_symm_good_mesh
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hfdd : aux_fsrkb_Fdd K P)
    (μ : Measure (SpatialCoordinates d)) (hsym : SemigroupSymmetric P μ)
    (U : Set (SpatialCoordinates d)) {F : Set (SpatialCoordinates d)} (hF : MeasurableSet F)
    (hFU : F ⊆ U) (t : ℝ≥0) (ht : 0 < t) (m : ℕ) (hm : 1 ≤ m) :
    aux_fsrkb_symm_Good (fun a b => aux_fsrkb_symm_pair K μ U (aux_fsrkb_symm_meshFun F t m b) a) := by
  intro a b ha hb
  have ha' : Measurable (F.indicator a) := ha.1.indicator hF
  have hb' : Measurable (F.indicator b) := hb.1.indicator hF
  simp only [aux_fsrkb_symm_pair]
  rw [aux_fsrkb_symm_meshPair_eq K P hfdd μ U hF hFU t ht m a hb.1,
    aux_fsrkb_symm_meshPair_eq K P hfdd μ U hF hFU t ht m b ha.1,
    aux_fsrkb_symm_meshPair_eq K P hfdd μ U hF hFU t ht m a ha.1,
    aux_fsrkb_symm_meshPair_eq K P hfdd μ U hF hFU t ht m b hb.1]
  refine ⟨aux_fsrkb_symm_iter_symm P μ hsym _ hF _ hb' ha', ?_⟩
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ m = 2 * k := ⟨2 ^ (m - 1), by
    rw [← pow_succ']; congr 1; omega⟩
  rw [hk, add_comm]
  exact aux_fsrkb_symm_iter_pos P μ hsym _ hF k hb' ha'

theorem aux_fsrkb_symm_good_closed
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hfdd : aux_fsrkb_Fdd K P)
    (μ : Measure (SpatialCoordinates d)) (hsym : SemigroupSymmetric P μ)
    (U : Set (SpatialCoordinates d)) (hμU : μ U ≠ ⊤) {F : Set (SpatialCoordinates d)}
    (hF : IsClosed F) (hFU : F ⊆ U) (t : ℝ≥0) (ht : 0 < t) :
    aux_fsrkb_symm_Good
      (fun a b => aux_fsrkb_symm_pair K μ U (aux_fsrkb_symm_closedFun F t b) a) := by
  refine aux_fsrkb_symm_good_of_tendsto
    (fun m a b => aux_fsrkb_symm_pair K μ U (aux_fsrkb_symm_meshFun F t m b) a) _ ?_ ?_
  · intro a b ha hb
    obtain ⟨hb_meas, C, hC⟩ := hb
    exact aux_fsrkb_symm_pair_tendsto K μ U hμU _ _
      (fun m => aux_fsrkb_symm_meshFun_measurable hF.measurableSet t m hb_meas) C
      (fun m path => aux_fsrkb_symm_meshFun_le F t m hC path)
      (fun path => aux_fsrkb_symm_mesh_tendsto hF t ht b path) ha
  · filter_upwards [eventually_ge_atTop 1] with m hm
    exact aux_fsrkb_symm_good_mesh K P hfdd μ hsym U hF.measurableSet hFU t ht m hm

theorem aux_fsrkb_symm_good_killed
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hfdd : aux_fsrkb_Fdd K P)
    (μ : Measure (SpatialCoordinates d)) (hsym : SemigroupSymmetric P μ)
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (hμU : μ U ≠ ⊤) (t : ℝ≥0) (ht : 0 < t) :
    aux_fsrkb_symm_Good
      (fun a b => aux_fsrkb_symm_pair K μ U (aux_fsrkb_symm_killedFun U t b) a) := by
  refine aux_fsrkb_symm_good_of_tendsto
    (fun j a b => aux_fsrkb_symm_pair K μ U
      (aux_fsrkb_symm_closedFun (aux_fsrkb_symm_Fj U j) t b) a) _ ?_ ?_
  · intro a b ha hb
    obtain ⟨hb_meas, C, hC⟩ := hb
    exact aux_fsrkb_symm_pair_tendsto K μ U hμU _ _
      (fun j => aux_fsrkb_symm_closedFun_measurable (aux_fsrkb_symm_Fj_isClosed U j) t ht hb_meas)
      C (fun j path => aux_fsrkb_symm_closedFun_le _ t hC path)
      (fun path => tendsto_const_nhds.congr'
        (EventuallyEq.symm (aux_fsrkb_symm_closed_eventually U hU t b path))) ha
  · exact Eventually.of_forall fun j => aux_fsrkb_symm_good_closed K P hfdd μ hsym U hμU
      (aux_fsrkb_symm_Fj_isClosed U j) (aux_fsrkb_symm_Fj_subset U j) t ht

end GoodKilled

section Resolvent


theorem aux_fsrkb_symm_killedFun_joint (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    {b : SpatialCoordinates d → ℝ≥0∞} (hb : Measurable b) :
    Measurable (fun p : ℝ × DiffusionPath d => aux_fsrkb_symm_killedFun U (Real.toNNReal p.1) b p.2) := by
  have heval : Measurable fun p : ℝ × DiffusionPath d ↦ p.2 (Real.toNNReal p.1) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hS : MeasurableSet {p : ℝ × DiffusionPath d |
      ((Real.toNNReal p.1 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U p.2} :=
    measurableSet_lt (measurable_coe_nnreal_ennreal.comp (measurable_real_toNNReal.comp measurable_fst))
      ((ContinuousPath.measurable_exitTime U hU).comp measurable_snd)
  exact (hb.comp heval).indicator hS

theorem aux_fsrkb_symm_killedFun_measurable (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (t : ℝ≥0) {b : SpatialCoordinates d → ℝ≥0∞} (hb : Measurable b) :
    Measurable (aux_fsrkb_symm_killedFun U t b) := by
  have h := (aux_fsrkb_symm_killedFun_joint U hU hb).comp
    (measurable_const.prodMk measurable_id : Measurable fun path : DiffusionPath d => ((t : ℝ), path))
  convert h using 1
  funext path
  simp [Real.toNNReal_coe]

/-- The discounted killed occupation functional of one path. -/
noncomputable def aux_fsrkb_symm_Psi (U : Set (SpatialCoordinates d)) (lam : ℝ)
    (b : SpatialCoordinates d → ℝ≥0∞) (path : DiffusionPath d) : ℝ≥0∞ :=
  ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * s)) *
    aux_fsrkb_symm_killedFun U (Real.toNNReal s) b path

/-- The `ℝ≥0∞`-valued killed resolvent. -/
noncomputable def aux_fsrkb_symm_R (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (U : Set (SpatialCoordinates d)) (lam : ℝ) (b : SpatialCoordinates d → ℝ≥0∞)
    (x : SpatialCoordinates d) : ℝ≥0∞ :=
  ∫⁻ path, aux_fsrkb_symm_Psi U lam b path ∂(K x)

theorem aux_fsrkb_symm_expWeight_measurable (lam : ℝ) :
    Measurable fun s : ℝ => ENNReal.ofReal (Real.exp (-lam * s)) :=
  ENNReal.measurable_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable

theorem aux_fsrkb_symm_Psi_joint (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (lam : ℝ)
    {b : SpatialCoordinates d → ℝ≥0∞} (hb : Measurable b) :
    Measurable (fun p : DiffusionPath d × ℝ => ENNReal.ofReal (Real.exp (-lam * p.2)) *
      aux_fsrkb_symm_killedFun U (Real.toNNReal p.2) b p.1) :=
  ((aux_fsrkb_symm_expWeight_measurable lam).comp measurable_snd).mul
    ((aux_fsrkb_symm_killedFun_joint U hU hb).comp measurable_swap)

theorem aux_fsrkb_symm_Psi_measurable (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (lam : ℝ)
    {b : SpatialCoordinates d → ℝ≥0∞} (hb : Measurable b) :
    Measurable (aux_fsrkb_symm_Psi U lam b) :=
  (aux_fsrkb_symm_Psi_joint U hU lam hb).lintegral_prod_right'

theorem aux_fsrkb_symm_R_measurable
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (lam : ℝ)
    {b : SpatialCoordinates d → ℝ≥0∞} (hb : Measurable b) :
    Measurable (aux_fsrkb_symm_R K U lam b) :=
  Measurable.lintegral_kernel (aux_fsrkb_symm_Psi_measurable U hU lam hb)

theorem aux_fsrkb_symm_E_measurable
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    {b : SpatialCoordinates d → ℝ≥0∞} (hb : Measurable b) :
    Measurable (fun q : SpatialCoordinates d × ℝ =>
      ∫⁻ path, aux_fsrkb_symm_killedFun U (Real.toNNReal q.2) b path ∂(K q.1)) := by
  have hf : Measurable (fun q : (SpatialCoordinates d × ℝ) × DiffusionPath d =>
      aux_fsrkb_symm_killedFun U (Real.toNNReal q.1.2) b q.2) :=
    (aux_fsrkb_symm_killedFun_joint U hU hb).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have h := hf.lintegral_kernel_prod_right' (κ := Kernel.prodMkRight ℝ K)
  simpa only [Kernel.prodMkRight_apply] using h

theorem aux_fsrkb_symm_R_eq_time
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (lam : ℝ)
    {b : SpatialCoordinates d → ℝ≥0∞} (hb : Measurable b) (x : SpatialCoordinates d) :
    aux_fsrkb_symm_R K U lam b x =
      ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * s)) *
        ∫⁻ path, aux_fsrkb_symm_killedFun U (Real.toNNReal s) b path ∂(K x) := by
  unfold aux_fsrkb_symm_R aux_fsrkb_symm_Psi
  rw [lintegral_lintegral_swap (aux_fsrkb_symm_Psi_joint U hU lam hb).aemeasurable]
  refine lintegral_congr fun s => ?_
  exact lintegral_const_mul _ (aux_fsrkb_symm_killedFun_measurable U hU _ hb)

/-- The `ℝ≥0∞` resolvent pairing `∫_U a R b dμ`. -/
noncomputable def aux_fsrkb_symm_RPair (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (μ : Measure (SpatialCoordinates d)) (U : Set (SpatialCoordinates d)) (lam : ℝ)
    (a b : SpatialCoordinates d → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x in U, a x * aux_fsrkb_symm_R K U lam b x ∂μ

theorem aux_fsrkb_symm_RPair_eq_time
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (μ : Measure (SpatialCoordinates d)) (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (hμU : μ U ≠ ⊤) (lam : ℝ) {a b : SpatialCoordinates d → ℝ≥0∞}
    (ha : aux_fsrkb_symm_Bdd a) (hb : Measurable b) :
    aux_fsrkb_symm_RPair K μ U lam a b =
      ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * s)) *
        aux_fsrkb_symm_pair K μ U (aux_fsrkb_symm_killedFun U (Real.toNNReal s) b) a := by
  haveI : IsFiniteMeasure (μ.restrict U) := isFiniteMeasure_restrict.2 hμU
  rcases ha with ⟨ha_meas, Ca, hCa⟩
  have hane : ∀ x, a x ≠ ⊤ := fun x => ne_top_of_le_ne_top ENNReal.coe_ne_top (hCa x)
  unfold aux_fsrkb_symm_RPair aux_fsrkb_symm_pair
  simp_rw [aux_fsrkb_symm_R_eq_time K U hU lam hb]
  have e1 : ∀ x, a x * ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * s)) *
        ∫⁻ path, aux_fsrkb_symm_killedFun U (Real.toNNReal s) b path ∂(K x) =
      ∫⁻ s in Set.Ioi (0 : ℝ), a x * (ENNReal.ofReal (Real.exp (-lam * s)) *
        ∫⁻ path, aux_fsrkb_symm_killedFun U (Real.toNNReal s) b path ∂(K x)) :=
    fun x => (lintegral_const_mul' _ _ (hane x)).symm
  simp_rw [e1]
  have hjoint : Measurable (Function.uncurry fun (x : SpatialCoordinates d) (s : ℝ) =>
      a x * (ENNReal.ofReal (Real.exp (-lam * s)) *
        ∫⁻ path, aux_fsrkb_symm_killedFun U (Real.toNNReal s) b path ∂(K x))) :=
    (ha_meas.comp measurable_fst).mul
      (((aux_fsrkb_symm_expWeight_measurable lam).comp measurable_snd).mul
        (aux_fsrkb_symm_E_measurable K U hU hb))
  rw [lintegral_lintegral_swap hjoint.aemeasurable]
  refine lintegral_congr fun s => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun x => ?_
  ring

theorem aux_fsrkb_symm_pairTime_measurable
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (μ : Measure (SpatialCoordinates d)) (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (hμU : μ U ≠ ⊤) (lam : ℝ) {a b : SpatialCoordinates d → ℝ≥0∞}
    (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun s : ℝ => ENNReal.ofReal (Real.exp (-lam * s)) *
        aux_fsrkb_symm_pair K μ U (aux_fsrkb_symm_killedFun U (Real.toNNReal s) b) a) := by
  haveI : IsFiniteMeasure (μ.restrict U) := isFiniteMeasure_restrict.2 hμU
  refine (aux_fsrkb_symm_expWeight_measurable lam).mul ?_
  unfold aux_fsrkb_symm_pair
  have hf : Measurable (fun q : ℝ × SpatialCoordinates d => a q.2 *
      ∫⁻ path, aux_fsrkb_symm_killedFun U (Real.toNNReal q.1) b path ∂(K q.2)) :=
    (ha.comp measurable_snd).mul ((aux_fsrkb_symm_E_measurable K U hU hb).comp measurable_swap)
  exact hf.lintegral_prod_right'

theorem aux_fsrkb_symm_good_R
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hfdd : aux_fsrkb_Fdd K P)
    (μ : Measure (SpatialCoordinates d)) (hsym : SemigroupSymmetric P μ)
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (hμU : μ U ≠ ⊤) (lam : ℝ) :
    aux_fsrkb_symm_Good (fun a b => aux_fsrkb_symm_RPair K μ U lam a b) := by
  intro a b ha hb
  simp only
  rw [aux_fsrkb_symm_RPair_eq_time K μ U hU hμU lam ha hb.1,
    aux_fsrkb_symm_RPair_eq_time K μ U hU hμU lam hb ha.1,
    aux_fsrkb_symm_RPair_eq_time K μ U hU hμU lam ha ha.1,
    aux_fsrkb_symm_RPair_eq_time K μ U hU hμU lam hb hb.1]
  have hgood : ∀ s ∈ Set.Ioi (0 : ℝ),
      aux_fsrkb_symm_pair K μ U (aux_fsrkb_symm_killedFun U (Real.toNNReal s) b) a =
          aux_fsrkb_symm_pair K μ U (aux_fsrkb_symm_killedFun U (Real.toNNReal s) a) b ∧
        2 * aux_fsrkb_symm_pair K μ U (aux_fsrkb_symm_killedFun U (Real.toNNReal s) b) a ≤
          aux_fsrkb_symm_pair K μ U (aux_fsrkb_symm_killedFun U (Real.toNNReal s) a) a +
            aux_fsrkb_symm_pair K μ U (aux_fsrkb_symm_killedFun U (Real.toNNReal s) b) b := by
    intro s hs
    exact aux_fsrkb_symm_good_killed K P hfdd μ hsym U hU hμU (Real.toNNReal s)
      (Real.toNNReal_pos.2 hs) a b ha hb
  constructor
  · refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    rw [(hgood s hs).1]
  · rw [← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
      ← lintegral_add_left (aux_fsrkb_symm_pairTime_measurable K μ U hU hμU lam ha.1 ha.1)]
    refine setLIntegral_mono' measurableSet_Ioi (fun s hs => ?_)
    rw [mul_left_comm, ← mul_add]
    exact mul_le_mul' le_rfl (hgood s hs).2

end Resolvent

section Bounds


theorem aux_fsrkb_symm_lintegral_exp (lam : ℝ) (hlam : 0 < lam) :
    ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * s)) = ENNReal.ofReal lam⁻¹ := by
  rw [← ofReal_integral_eq_lintegral_ofReal (exp_neg_integrableOn_Ioi 0 hlam)
    (ae_of_all _ (fun s => (Real.exp_pos _).le))]
  congr 1
  have h := integral_exp_mul_Ioi (a := -lam) (by linarith only [hlam]) 0
  rw [h, mul_zero, Real.exp_zero]
  field_simp

theorem aux_fsrkb_symm_killedFun_le (U : Set (SpatialCoordinates d)) (t : ℝ≥0)
    {b : SpatialCoordinates d → ℝ≥0∞} {C : ℝ≥0∞} (hC : ∀ x, b x ≤ C) (path : DiffusionPath d) :
    aux_fsrkb_symm_killedFun U t b path ≤ C := by
  unfold aux_fsrkb_symm_killedFun
  by_cases hp : path ∈ {path : DiffusionPath d | (t : ℝ≥0∞) < ContinuousPath.exitTime U path}
  · rw [Set.indicator_of_mem hp]; exact hC _
  · rw [Set.indicator_of_notMem hp]; exact zero_le _

theorem aux_fsrkb_symm_Psi_le (U : Set (SpatialCoordinates d)) (lam : ℝ) (hlam : 0 < lam)
    {b : SpatialCoordinates d → ℝ≥0∞} {C : ℝ≥0∞} (hC : ∀ x, b x ≤ C) (path : DiffusionPath d) :
    aux_fsrkb_symm_Psi U lam b path ≤ C * ENNReal.ofReal lam⁻¹ := by
  unfold aux_fsrkb_symm_Psi
  calc ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * s)) *
        aux_fsrkb_symm_killedFun U (Real.toNNReal s) b path
      ≤ ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * s)) * C :=
        lintegral_mono fun s => mul_le_mul' le_rfl (aux_fsrkb_symm_killedFun_le U _ hC path)
    _ = C * ENNReal.ofReal lam⁻¹ := by
        rw [lintegral_mul_const _ (aux_fsrkb_symm_expWeight_measurable lam),
          aux_fsrkb_symm_lintegral_exp lam hlam, mul_comm]

theorem aux_fsrkb_symm_R_le (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    [IsMarkovKernel K] (U : Set (SpatialCoordinates d)) (lam : ℝ) (hlam : 0 < lam)
    {b : SpatialCoordinates d → ℝ≥0∞} {C : ℝ≥0∞} (hC : ∀ x, b x ≤ C) (x : SpatialCoordinates d) :
    aux_fsrkb_symm_R K U lam b x ≤ C * ENNReal.ofReal lam⁻¹ := by
  unfold aux_fsrkb_symm_R
  calc ∫⁻ path, aux_fsrkb_symm_Psi U lam b path ∂(K x)
      ≤ ∫⁻ _path, C * ENNReal.ofReal lam⁻¹ ∂(K x) :=
        lintegral_mono fun path => aux_fsrkb_symm_Psi_le U lam hlam hC path
    _ = C * ENNReal.ofReal lam⁻¹ := by simp

theorem aux_fsrkb_symm_RPair_ne_top (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    [IsMarkovKernel K] (μ : Measure (SpatialCoordinates d)) (U : Set (SpatialCoordinates d))
    (hμU : μ U ≠ ⊤) (lam : ℝ) (hlam : 0 < lam)
    {a b : SpatialCoordinates d → ℝ≥0∞} (ha : aux_fsrkb_symm_Bdd a) (hb : aux_fsrkb_symm_Bdd b) :
    aux_fsrkb_symm_RPair K μ U lam a b ≠ ⊤ := by
  rcases ha with ⟨_, Ca, hCa⟩
  rcases hb with ⟨_, Cb, hCb⟩
  unfold aux_fsrkb_symm_RPair
  refine ne_top_of_le_ne_top ?_ (lintegral_mono (fun x => mul_le_mul' (hCa x)
    (aux_fsrkb_symm_R_le K U lam hlam hCb x)))
  rw [lintegral_const, Measure.restrict_apply_univ]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
    (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)) hμU

theorem aux_fsrkb_symm_killedFun_add (U : Set (SpatialCoordinates d)) (t : ℝ≥0)
    (b₁ b₂ : SpatialCoordinates d → ℝ≥0∞) (path : DiffusionPath d) :
    aux_fsrkb_symm_killedFun U t (fun y => b₁ y + b₂ y) path =
      aux_fsrkb_symm_killedFun U t b₁ path + aux_fsrkb_symm_killedFun U t b₂ path := by
  unfold aux_fsrkb_symm_killedFun
  by_cases hp : path ∈ {path : DiffusionPath d | (t : ℝ≥0∞) < ContinuousPath.exitTime U path}
  · simp only [Set.indicator_of_mem hp]
  · simp only [Set.indicator_of_notMem hp, add_zero]

theorem aux_fsrkb_symm_killedFun_const_mul (U : Set (SpatialCoordinates d)) (t : ℝ≥0)
    (c : ℝ≥0∞) (b : SpatialCoordinates d → ℝ≥0∞) (path : DiffusionPath d) :
    aux_fsrkb_symm_killedFun U t (fun y => c * b y) path =
      c * aux_fsrkb_symm_killedFun U t b path := by
  unfold aux_fsrkb_symm_killedFun
  by_cases hp : path ∈ {path : DiffusionPath d | (t : ℝ≥0∞) < ContinuousPath.exitTime U path}
  · simp only [Set.indicator_of_mem hp]
  · simp only [Set.indicator_of_notMem hp, mul_zero]

theorem aux_fsrkb_symm_killedFun_mono (U : Set (SpatialCoordinates d)) (t : ℝ≥0)
    {b₁ b₂ : SpatialCoordinates d → ℝ≥0∞} (h : ∀ y, b₁ y ≤ b₂ y) (path : DiffusionPath d) :
    aux_fsrkb_symm_killedFun U t b₁ path ≤ aux_fsrkb_symm_killedFun U t b₂ path := by
  unfold aux_fsrkb_symm_killedFun
  by_cases hp : path ∈ {path : DiffusionPath d | (t : ℝ≥0∞) < ContinuousPath.exitTime U path}
  · simp only [Set.indicator_of_mem hp]; exact h _
  · simp only [Set.indicator_of_notMem hp, le_refl]

theorem aux_fsrkb_symm_R_add (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (lam : ℝ)
    {b₁ b₂ : SpatialCoordinates d → ℝ≥0∞} (hb₁ : Measurable b₁) (x : SpatialCoordinates d) :
    aux_fsrkb_symm_R K U lam (fun y => b₁ y + b₂ y) x =
      aux_fsrkb_symm_R K U lam b₁ x + aux_fsrkb_symm_R K U lam b₂ x := by
  unfold aux_fsrkb_symm_R
  rw [← lintegral_add_left (aux_fsrkb_symm_Psi_measurable U hU lam hb₁)]
  refine lintegral_congr fun path => ?_
  unfold aux_fsrkb_symm_Psi
  have hm : Measurable (fun s : ℝ => ENNReal.ofReal (Real.exp (-lam * s)) *
      aux_fsrkb_symm_killedFun U (Real.toNNReal s) b₁ path) :=
    (aux_fsrkb_symm_Psi_joint U hU lam hb₁).comp (measurable_const.prodMk measurable_id)
  rw [← lintegral_add_left hm]
  refine lintegral_congr fun s => ?_
  rw [aux_fsrkb_symm_killedFun_add, mul_add]

theorem aux_fsrkb_symm_R_const_mul (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (lam : ℝ) (c : ℝ≥0∞)
    {b : SpatialCoordinates d → ℝ≥0∞} (hb : Measurable b) (x : SpatialCoordinates d) :
    aux_fsrkb_symm_R K U lam (fun y => c * b y) x = c * aux_fsrkb_symm_R K U lam b x := by
  unfold aux_fsrkb_symm_R
  rw [← lintegral_const_mul _ (aux_fsrkb_symm_Psi_measurable U hU lam hb)]
  refine lintegral_congr fun path => ?_
  unfold aux_fsrkb_symm_Psi
  have hm : Measurable (fun s : ℝ => ENNReal.ofReal (Real.exp (-lam * s)) *
      aux_fsrkb_symm_killedFun U (Real.toNNReal s) b path) :=
    (aux_fsrkb_symm_Psi_joint U hU lam hb).comp (measurable_const.prodMk measurable_id)
  rw [← lintegral_const_mul _ hm]
  refine lintegral_congr fun s => ?_
  rw [aux_fsrkb_symm_killedFun_const_mul, mul_left_comm]

theorem aux_fsrkb_symm_R_mono (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (U : Set (SpatialCoordinates d)) (lam : ℝ)
    {b₁ b₂ : SpatialCoordinates d → ℝ≥0∞} (h : ∀ y, b₁ y ≤ b₂ y) (x : SpatialCoordinates d) :
    aux_fsrkb_symm_R K U lam b₁ x ≤ aux_fsrkb_symm_R K U lam b₂ x :=
  lintegral_mono fun path => lintegral_mono fun _ =>
    mul_le_mul' le_rfl (aux_fsrkb_symm_killedFun_mono U _ h path)

end Bounds

section RealConversion


theorem aux_fsrkb_symm_inner_eq (U : Set (SpatialCoordinates d)) (lam : ℝ)
    {φ : SpatialCoordinates d → ℝ} (hφ : Measurable φ) (hφ0 : ∀ y, 0 ≤ φ y)
    (path : DiffusionPath d) :
    ∫ s in Set.Ioi (0 : ℝ),
        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
          (fun s => Real.exp (-lam * s) * φ (path (Real.toNNReal s))) s =
      (aux_fsrkb_symm_Psi U lam (fun y => ENNReal.ofReal (φ y)) path).toReal := by
  have hS : MeasurableSet {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path} :=
    measurableSet_lt ENNReal.measurable_ofReal measurable_const
  have hmeas : Measurable (fun s : ℝ => Real.exp (-lam * s) * φ (path (Real.toNNReal s))) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.mul
      (hφ.comp (path.continuous.measurable.comp measurable_real_toNNReal))
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (fun s => Set.indicator_nonneg
      (fun s _ => mul_nonneg (Real.exp_pos _).le (hφ0 _)) s))
    (hmeas.indicator hS).aestronglyMeasurable]
  congr 1
  unfold aux_fsrkb_symm_Psi
  refine lintegral_congr fun s => ?_
  unfold aux_fsrkb_symm_killedFun
  by_cases hs : ENNReal.ofReal s < ContinuousPath.exitTime U path
  · rw [Set.indicator_of_mem (show s ∈ {s : ℝ | ENNReal.ofReal s <
        ContinuousPath.exitTime U path} from hs),
      Set.indicator_of_mem (show path ∈ {path : DiffusionPath d |
        ((Real.toNNReal s : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime U path} from hs),
      ENNReal.ofReal_mul (Real.exp_pos _).le]
  · rw [Set.indicator_of_notMem (show s ∉ {s : ℝ | ENNReal.ofReal s <
        ContinuousPath.exitTime U path} from hs),
      Set.indicator_of_notMem (show path ∉ {path : DiffusionPath d |
        ((Real.toNNReal s : ℝ≥0) : ℝ≥0∞) < ContinuousPath.exitTime U path} from hs),
      mul_zero, ENNReal.ofReal_zero]

theorem aux_fsrkb_symm_inner_integrableOn (U : Set (SpatialCoordinates d)) (lam : ℝ)
    (hlam : 0 < lam) {φ : SpatialCoordinates d → ℝ} (hφ : Measurable φ) (hφ0 : ∀ y, 0 ≤ φ y)
    {B : ℝ} (hB : ∀ y, φ y ≤ B) (path : DiffusionPath d) :
    IntegrableOn (fun s => Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
          (fun s => Real.exp (-lam * s) * φ (path (Real.toNNReal s))) s) (Set.Ioi (0 : ℝ)) := by
  have hS : MeasurableSet {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path} :=
    measurableSet_lt ENNReal.measurable_ofReal measurable_const
  have hmeas : Measurable (fun s : ℝ => Real.exp (-lam * s) * φ (path (Real.toNNReal s))) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.mul
      (hφ.comp (path.continuous.measurable.comp measurable_real_toNNReal))
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hlam).const_mul B)
    (hmeas.indicator hS).aestronglyMeasurable (ae_of_all _ (fun s => ?_))
  rw [Real.norm_eq_abs]
  have h0 : 0 ≤ Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
      (fun s => Real.exp (-lam * s) * φ (path (Real.toNNReal s))) s :=
    Set.indicator_nonneg (fun s _ => mul_nonneg (Real.exp_pos _).le (hφ0 _)) s
  rw [abs_of_nonneg h0]
  refine (Set.indicator_le_self' (fun s _ => mul_nonneg (Real.exp_pos _).le (hφ0 _)) s).trans ?_
  rw [mul_comm B]
  exact mul_le_mul_of_nonneg_left (hB _) (Real.exp_pos _).le

theorem aux_fsrkb_symm_killedRes_eq
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (lam : ℝ) (hlam : 0 < lam)
    {f : SpatialCoordinates d → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ y, |f y| ≤ B)
    (x : SpatialCoordinates d) :
    aux_fsrkb_killedRes K U lam f x =
      (aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal (max (f y) 0)) x).toReal -
        (aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal (max (-f y) 0)) x).toReal := by
  have hp : Measurable (fun y => max (f y) 0) := hf.max measurable_const
  have hm : Measurable (fun y => max (-f y) 0) := hf.neg.max measurable_const
  have hp0 : ∀ y, 0 ≤ max (f y) 0 := fun y => le_max_right _ _
  have hm0 : ∀ y, 0 ≤ max (-f y) 0 := fun y => le_max_right _ _
  have hpB : ∀ y, max (f y) 0 ≤ B := fun y =>
    max_le (le_trans (le_abs_self _) (hB y)) (le_trans (abs_nonneg _) (hB y))
  have hmB : ∀ y, max (-f y) 0 ≤ B := fun y =>
    max_le (le_trans (neg_le_abs _) (hB y)) (le_trans (abs_nonneg _) (hB y))
  have hinner : ∀ path : DiffusionPath d,
      ∫ s in Set.Ioi (0 : ℝ),
        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
          (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) s =
      (aux_fsrkb_symm_Psi U lam (fun y => ENNReal.ofReal (max (f y) 0)) path).toReal -
        (aux_fsrkb_symm_Psi U lam (fun y => ENNReal.ofReal (max (-f y) 0)) path).toReal := by
    intro path
    rw [← aux_fsrkb_symm_inner_eq U lam hp hp0, ← aux_fsrkb_symm_inner_eq U lam hm hm0,
      ← integral_sub (aux_fsrkb_symm_inner_integrableOn U lam hlam hp hp0 hpB path)
        (aux_fsrkb_symm_inner_integrableOn U lam hlam hm hm0 hmB path)]
    congr 1
    funext s
    by_cases hs : s ∈ {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime U path}
    · simp only [Set.indicator_of_mem hs]
      rw [← mul_sub, max_zero_sub_max_neg_zero_eq_self]
    · simp only [Set.indicator_of_notMem hs, sub_zero]
  have hPp : Measurable (aux_fsrkb_symm_Psi U lam (fun y => ENNReal.ofReal (max (f y) 0))) :=
    aux_fsrkb_symm_Psi_measurable U hU lam (ENNReal.measurable_ofReal.comp hp)
  have hPm : Measurable (aux_fsrkb_symm_Psi U lam (fun y => ENNReal.ofReal (max (-f y) 0))) :=
    aux_fsrkb_symm_Psi_measurable U hU lam (ENNReal.measurable_ofReal.comp hm)
  have hBp : ∀ y, ENNReal.ofReal (max (f y) 0) ≤ ENNReal.ofReal B :=
    fun y => ENNReal.ofReal_le_ofReal (hpB y)
  have hBm : ∀ y, ENNReal.ofReal (max (-f y) 0) ≤ ENNReal.ofReal B :=
    fun y => ENNReal.ofReal_le_ofReal (hmB y)
  have hfin : ∀ {b : SpatialCoordinates d → ℝ≥0∞}, (∀ y, b y ≤ ENNReal.ofReal B) →
      ∫⁻ path, aux_fsrkb_symm_Psi U lam b path ∂(K x) ≠ ⊤ := by
    intro b hb
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (aux_fsrkb_symm_R_le K U lam hlam hb x)
  have hlt : ∀ {b : SpatialCoordinates d → ℝ≥0∞}, (∀ y, b y ≤ ENNReal.ofReal B) →
      ∀ᵐ path ∂(K x), aux_fsrkb_symm_Psi U lam b path < ⊤ := by
    intro b hb
    refine ae_of_all _ (fun path => lt_of_le_of_lt (aux_fsrkb_symm_Psi_le U lam hlam hb path) ?_)
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  unfold aux_fsrkb_killedRes aux_fsrkb_symm_R
  simp_rw [hinner]
  rw [integral_sub (integrable_toReal_of_lintegral_ne_top hPp.aemeasurable (hfin hBp))
      (integrable_toReal_of_lintegral_ne_top hPm.aemeasurable (hfin hBm)),
    integral_toReal hPp.aemeasurable (hlt hBp), integral_toReal hPm.aemeasurable (hlt hBm)]

end RealConversion

section Final


theorem aux_fsrkb_symm_bdd_ofReal {φ : SpatialCoordinates d → ℝ} (hφ : Measurable φ) {B : ℝ}
    (hB : ∀ y, φ y ≤ B) : aux_fsrkb_symm_Bdd (fun y => ENNReal.ofReal (φ y)) :=
  ⟨ENNReal.measurable_ofReal.comp hφ, B.toNNReal, fun y => ENNReal.ofReal_le_ofReal (hB y)⟩

theorem aux_fsrkb_symm_R_toReal_le (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    [IsMarkovKernel K] (U : Set (SpatialCoordinates d)) (lam : ℝ) (hlam : 0 < lam)
    {ψ : SpatialCoordinates d → ℝ} {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ y, ψ y ≤ B)
    (x : SpatialCoordinates d) :
    (aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal (ψ y)) x).toReal ≤ B * lam⁻¹ := by
  refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg hB0 (inv_nonneg.2 hlam.le)) ?_
  rw [ENNReal.ofReal_mul hB0]
  exact aux_fsrkb_symm_R_le K U lam hlam (fun y => ENNReal.ofReal_le_ofReal (hB y)) x

theorem aux_fsrkb_symm_R_ne_top (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    [IsMarkovKernel K] (U : Set (SpatialCoordinates d)) (lam : ℝ) (hlam : 0 < lam)
    {b : SpatialCoordinates d → ℝ≥0∞} (hb : aux_fsrkb_symm_Bdd b) (x : SpatialCoordinates d) :
    aux_fsrkb_symm_R K U lam b x ≠ ⊤ := by
  rcases hb with ⟨_, C, hC⟩
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
    (aux_fsrkb_symm_R_le K U lam hlam hC x)

theorem aux_fsrkb_symm_integrable_of_abs_le {ν : Measure (SpatialCoordinates d)}
    [IsFiniteMeasure ν] {u : SpatialCoordinates d → ℝ} (hu : Measurable u) (C : ℝ)
    (hC : ∀ x, |u x| ≤ C) : Integrable u ν :=
  Integrable.of_bound hu.aestronglyMeasurable C
    (ae_of_all _ (fun x => by rw [Real.norm_eq_abs]; exact hC x))

/-- The real pairing `(∫_U φ · R ψ dμ)` of two nonnegative bounded functions. -/
noncomputable def aux_fsrkb_symm_Jt (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    (μ : Measure (SpatialCoordinates d)) (U : Set (SpatialCoordinates d)) (lam : ℝ)
    (φ ψ : SpatialCoordinates d → ℝ) : ℝ :=
  (aux_fsrkb_symm_RPair K μ U lam (fun y => ENNReal.ofReal (φ y))
    (fun y => ENNReal.ofReal (ψ y))).toReal

theorem aux_fsrkb_symm_J_eq (K : Kernel (SpatialCoordinates d) (DiffusionPath d))
    [IsMarkovKernel K] (μ : Measure (SpatialCoordinates d)) (U : Set (SpatialCoordinates d))
    (hU : IsOpen U) (lam : ℝ) (hlam : 0 < lam)
    {φ ψ : SpatialCoordinates d → ℝ} (hφ : Measurable φ) (hφ0 : ∀ y, 0 ≤ φ y)
    (hψ : Measurable ψ) {B : ℝ} (hψB : ∀ y, ψ y ≤ B) :
    ∫ x in U, φ x * (aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal (ψ y)) x).toReal ∂μ =
      aux_fsrkb_symm_Jt K μ U lam φ ψ := by
  have hRm : Measurable (aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal (ψ y))) :=
    aux_fsrkb_symm_R_measurable K U hU lam (ENNReal.measurable_ofReal.comp hψ)
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (fun x => mul_nonneg (hφ0 x) ENNReal.toReal_nonneg))
    (hφ.mul hRm.ennreal_toReal).aestronglyMeasurable]
  unfold aux_fsrkb_symm_Jt aux_fsrkb_symm_RPair
  congr 1
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_mul (hφ0 x), ENNReal.ofReal_toReal
    (aux_fsrkb_symm_R_ne_top K U lam hlam (aux_fsrkb_symm_bdd_ofReal hψ hψB) x)]

theorem aux_fsrkb_symm_expand {ν : Measure (SpatialCoordinates d)}
    {u₁ u₂ v₁ v₂ : SpatialCoordinates d → ℝ}
    (h11 : Integrable (fun x => u₁ x * v₁ x) ν) (h12 : Integrable (fun x => u₁ x * v₂ x) ν)
    (h21 : Integrable (fun x => u₂ x * v₁ x) ν) (h22 : Integrable (fun x => u₂ x * v₂ x) ν) :
    ∫ x, (u₁ x - u₂ x) * (v₁ x - v₂ x) ∂ν =
      ∫ x, u₁ x * v₁ x ∂ν - ∫ x, u₁ x * v₂ x ∂ν - ∫ x, u₂ x * v₁ x ∂ν + ∫ x, u₂ x * v₂ x ∂ν := by
  have e : (fun x => (u₁ x - u₂ x) * (v₁ x - v₂ x)) =
      fun x => (u₁ x * v₁ x - u₁ x * v₂ x) - (u₂ x * v₁ x - u₂ x * v₂ x) := by
    funext x; ring
  rw [e, integral_sub (f := fun x => u₁ x * v₁ x - u₁ x * v₂ x)
      (g := fun x => u₂ x * v₁ x - u₂ x * v₂ x) (h11.sub h12) (h21.sub h22),
    integral_sub h11 h12, integral_sub h21 h22]
  ring

theorem aux_fsrkb_symm_pairing_expand
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (μ : Measure (SpatialCoordinates d)) (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (hμU : μ U ≠ ⊤) (lam : ℝ) (hlam : 0 < lam) {u v : SpatialCoordinates d → ℝ}
    (hu : aux_fsrkb_BddMeas u) (hv : aux_fsrkb_BddMeas v) :
    ∫ x in U, u x * aux_fsrkb_killedRes K U lam v x ∂μ =
      aux_fsrkb_symm_Jt K μ U lam (fun y => max (u y) 0) (fun y => max (v y) 0) -
      aux_fsrkb_symm_Jt K μ U lam (fun y => max (u y) 0) (fun y => max (-v y) 0) -
      aux_fsrkb_symm_Jt K μ U lam (fun y => max (-u y) 0) (fun y => max (v y) 0) +
      aux_fsrkb_symm_Jt K μ U lam (fun y => max (-u y) 0) (fun y => max (-v y) 0) := by
  haveI : IsFiniteMeasure (μ.restrict U) := isFiniteMeasure_restrict.2 hμU
  obtain ⟨hu_meas, Bu, hBu0, hBu⟩ := hu
  obtain ⟨hv_meas, Bv, hBv0, hBv⟩ := hv
  have hup : Measurable (fun y => max (u y) 0) := hu_meas.max measurable_const
  have hum : Measurable (fun y => max (-u y) 0) := hu_meas.neg.max measurable_const
  have hvp : Measurable (fun y => max (v y) 0) := hv_meas.max measurable_const
  have hvm : Measurable (fun y => max (-v y) 0) := hv_meas.neg.max measurable_const
  have hup0 : ∀ y, 0 ≤ max (u y) 0 := fun y => le_max_right _ _
  have hum0 : ∀ y, 0 ≤ max (-u y) 0 := fun y => le_max_right _ _
  have hupB : ∀ y, max (u y) 0 ≤ Bu := fun y =>
    max_le (le_trans (le_abs_self _) (hBu y)) hBu0
  have humB : ∀ y, max (-u y) 0 ≤ Bu := fun y =>
    max_le (le_trans (neg_le_abs _) (hBu y)) hBu0
  have hvpB : ∀ y, max (v y) 0 ≤ Bv := fun y =>
    max_le (le_trans (le_abs_self _) (hBv y)) hBv0
  have hvmB : ∀ y, max (-v y) 0 ≤ Bv := fun y =>
    max_le (le_trans (neg_le_abs _) (hBv y)) hBv0
  have e : ∀ x, u x * aux_fsrkb_killedRes K U lam v x =
      (max (u x) 0 - max (-u x) 0) *
        ((aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal (max (v y) 0)) x).toReal -
          (aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal (max (-v y) 0)) x).toReal) := by
    intro x
    rw [aux_fsrkb_symm_killedRes_eq K U hU lam hlam hv_meas hBv x,
      max_zero_sub_max_neg_zero_eq_self]
  simp_rw [e]
  have hint : ∀ {φ ψ : SpatialCoordinates d → ℝ}, Measurable φ → (∀ y, 0 ≤ φ y) →
      (∀ y, φ y ≤ Bu) → Measurable ψ → (∀ y, ψ y ≤ Bv) →
      Integrable (fun x => φ x *
        (aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal (ψ y)) x).toReal) (μ.restrict U) := by
    intro φ ψ hφ hφ0 hφB hψ hψB
    refine aux_fsrkb_symm_integrable_of_abs_le
      (hφ.mul (aux_fsrkb_symm_R_measurable K U hU lam
        (ENNReal.measurable_ofReal.comp hψ)).ennreal_toReal) (Bu * (Bv * lam⁻¹)) (fun x => ?_)
    rw [abs_mul, abs_of_nonneg (hφ0 x), abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul (hφB x) (aux_fsrkb_symm_R_toReal_le K U lam hlam hBv0 hψB x)
      ENNReal.toReal_nonneg hBu0
  rw [aux_fsrkb_symm_expand (hint hup hup0 hupB hvp hvpB) (hint hup hup0 hupB hvm hvmB)
    (hint hum hum0 humB hvp hvpB) (hint hum hum0 humB hvm hvmB),
    aux_fsrkb_symm_J_eq K μ U hU lam hlam hup hup0 hvp hvpB,
    aux_fsrkb_symm_J_eq K μ U hU lam hlam hup hup0 hvm hvmB,
    aux_fsrkb_symm_J_eq K μ U hU lam hlam hum hum0 hvp hvpB,
    aux_fsrkb_symm_J_eq K μ U hU lam hlam hum hum0 hvm hvmB]

theorem aux_fsrkb_symm_Jt_comm
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hfdd : aux_fsrkb_Fdd K P)
    (μ : Measure (SpatialCoordinates d)) (hsym : SemigroupSymmetric P μ)
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (hμU : μ U ≠ ⊤) (lam : ℝ)
    {φ ψ : SpatialCoordinates d → ℝ} (hφ : Measurable φ) {Bφ : ℝ} (hφB : ∀ y, φ y ≤ Bφ)
    (hψ : Measurable ψ) {Bψ : ℝ} (hψB : ∀ y, ψ y ≤ Bψ) :
    aux_fsrkb_symm_Jt K μ U lam φ ψ = aux_fsrkb_symm_Jt K μ U lam ψ φ := by
  unfold aux_fsrkb_symm_Jt
  exact congrArg ENNReal.toReal (aux_fsrkb_symm_good_R K P hfdd μ hsym U hU hμU lam _ _
    (aux_fsrkb_symm_bdd_ofReal hφ hφB) (aux_fsrkb_symm_bdd_ofReal hψ hψB)).1

theorem aux_fsrkb_symm_Jt_two_le
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hfdd : aux_fsrkb_Fdd K P)
    (μ : Measure (SpatialCoordinates d)) (hsym : SemigroupSymmetric P μ)
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (hμU : μ U ≠ ⊤) (lam : ℝ) (hlam : 0 < lam)
    {φ ψ : SpatialCoordinates d → ℝ} (hφ : Measurable φ) {Bφ : ℝ} (hφB : ∀ y, φ y ≤ Bφ)
    (hψ : Measurable ψ) {Bψ : ℝ} (hψB : ∀ y, ψ y ≤ Bψ) :
    2 * aux_fsrkb_symm_Jt K μ U lam φ ψ ≤
      aux_fsrkb_symm_Jt K μ U lam φ φ + aux_fsrkb_symm_Jt K μ U lam ψ ψ := by
  have ha := aux_fsrkb_symm_bdd_ofReal hφ hφB
  have hb := aux_fsrkb_symm_bdd_ofReal hψ hψB
  have h := (aux_fsrkb_symm_good_R K P hfdd μ hsym U hU hμU lam _ _ ha hb).2
  have hfin := ENNReal.add_ne_top.2 ⟨aux_fsrkb_symm_RPair_ne_top K μ U hμU lam hlam ha ha,
    aux_fsrkb_symm_RPair_ne_top K μ U hμU lam hlam hb hb⟩
  have h2 := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (aux_fsrkb_symm_RPair_ne_top K μ U hμU lam hlam ha ha)
    (aux_fsrkb_symm_RPair_ne_top K μ U hμU lam hlam hb hb)] at h2
  unfold aux_fsrkb_symm_Jt
  simpa using h2

theorem aux_fsrkb_symm_parts {f : SpatialCoordinates d → ℝ} (hf : aux_fsrkb_BddMeas f) :
    ∃ B : ℝ, Measurable (fun y => max (f y) 0) ∧ Measurable (fun y => max (-f y) 0) ∧
      (∀ y, max (f y) 0 ≤ B) ∧ (∀ y, max (-f y) 0 ≤ B) := by
  obtain ⟨hf_meas, B, hB0, hB⟩ := hf
  exact ⟨B, hf_meas.max measurable_const, hf_meas.neg.max measurable_const,
    fun y => max_le (le_trans (le_abs_self _) (hB y)) hB0,
    fun y => max_le (le_trans (neg_le_abs _) (hB y)) hB0⟩

theorem aux_fsrkb_symm_main_symm
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hfdd : aux_fsrkb_Fdd K P)
    (μ : Measure (SpatialCoordinates d)) (hsym : SemigroupSymmetric P μ)
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (hμU : μ U ≠ ⊤)
    (lam : ℝ) (hlam : 0 < lam) (f g : SpatialCoordinates d → ℝ)
    (hf : aux_fsrkb_BddMeas f) (hg : aux_fsrkb_BddMeas g) :
    ∫ x in U, g x * aux_fsrkb_killedRes K U lam f x ∂μ =
      ∫ x in U, f x * aux_fsrkb_killedRes K U lam g x ∂μ := by
  rw [aux_fsrkb_symm_pairing_expand K μ U hU hμU lam hlam hg hf,
    aux_fsrkb_symm_pairing_expand K μ U hU hμU lam hlam hf hg]
  obtain ⟨Bf, hfp, hfm, hfpB, hfmB⟩ := aux_fsrkb_symm_parts hf
  obtain ⟨Bg, hgp, hgm, hgpB, hgmB⟩ := aux_fsrkb_symm_parts hg
  rw [aux_fsrkb_symm_Jt_comm K P hfdd μ hsym U hU hμU lam hgp hgpB hfp hfpB,
    aux_fsrkb_symm_Jt_comm K P hfdd μ hsym U hU hμU lam hgp hgpB hfm hfmB,
    aux_fsrkb_symm_Jt_comm K P hfdd μ hsym U hU hμU lam hgm hgmB hfp hfpB,
    aux_fsrkb_symm_Jt_comm K P hfdd μ hsym U hU hμU lam hgm hgmB hfm hfmB]
  ring

theorem aux_fsrkb_symm_main_nonneg
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hfdd : aux_fsrkb_Fdd K P)
    (μ : Measure (SpatialCoordinates d)) (hsym : SemigroupSymmetric P μ)
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (hμU : μ U ≠ ⊤)
    (lam : ℝ) (hlam : 0 < lam) (f : SpatialCoordinates d → ℝ) (hf : aux_fsrkb_BddMeas f) :
    0 ≤ ∫ x in U, f x * aux_fsrkb_killedRes K U lam f x ∂μ := by
  rw [aux_fsrkb_symm_pairing_expand K μ U hU hμU lam hlam hf hf]
  obtain ⟨Bf, hfp, hfm, hfpB, hfmB⟩ := aux_fsrkb_symm_parts hf
  have hc := aux_fsrkb_symm_Jt_comm K P hfdd μ hsym U hU hμU lam hfm hfmB hfp hfpB
  have h2 := aux_fsrkb_symm_Jt_two_le K P hfdd μ hsym U hU hμU lam hlam hfp hfpB hfm hfmB
  linarith only [hc, h2]

theorem aux_fsrkb_symm_abs_le
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (lam : ℝ) (hlam : 0 < lam)
    {f : SpatialCoordinates d → ℝ} (hf : aux_fsrkb_BddMeas f) (x : SpatialCoordinates d) :
    |aux_fsrkb_killedRes K U lam f x| ≤
      (aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal |f y|) x).toReal := by
  obtain ⟨B, hfp, hfm, hfpB, hfmB⟩ := aux_fsrkb_symm_parts hf
  obtain ⟨hf_meas, B', _, hB'⟩ := hf
  rw [aux_fsrkb_symm_killedRes_eq K U hU lam hlam hf_meas hB' x]
  have hadd := aux_fsrkb_symm_R_add K U hU lam (b₁ := fun y => ENNReal.ofReal (max (f y) 0))
    (b₂ := fun y => ENNReal.ofReal (max (-f y) 0)) (ENNReal.measurable_ofReal.comp hfp) x
  have hfun : (fun y => ENNReal.ofReal (max (f y) 0) + ENNReal.ofReal (max (-f y) 0)) =
      fun y => ENNReal.ofReal |f y| := by
    funext y
    rw [← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
      max_zero_add_max_neg_zero_eq_abs_self]
  rw [hfun] at hadd
  rw [hadd, ENNReal.toReal_add
    (aux_fsrkb_symm_R_ne_top K U lam hlam (aux_fsrkb_symm_bdd_ofReal hfp hfpB) x)
    (aux_fsrkb_symm_R_ne_top K U lam hlam (aux_fsrkb_symm_bdd_ofReal hfm hfmB) x)]
  have h1 := ENNReal.toReal_nonneg
    (a := aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal (max (f y) 0)) x)
  have h2 := ENNReal.toReal_nonneg
    (a := aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal (max (-f y) 0)) x)
  rw [abs_le]
  constructor <;> linarith only [h1, h2]

theorem aux_fsrkb_symm_cs
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (lam : ℝ) (hlam : 0 < lam)
    {f : SpatialCoordinates d → ℝ} (hf : aux_fsrkb_BddMeas f) (x : SpatialCoordinates d) :
    lam * ((aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal |f y|) x).toReal) ^ 2 ≤
      (aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal (f y ^ 2)) x).toReal := by
  obtain ⟨hf_meas, B, hB0, hB⟩ := hf
  have habs : Measurable (fun y => |f y|) := continuous_abs.measurable.comp hf_meas
  have habsm : Measurable (fun y => ENNReal.ofReal |f y|) := ENNReal.measurable_ofReal.comp habs
  have hsqB : ∀ y, f y ^ 2 ≤ B ^ 2 := fun y => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB y) 2
  have hX : aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal |f y|) x ≠ ⊤ :=
    aux_fsrkb_symm_R_ne_top K U lam hlam (aux_fsrkb_symm_bdd_ofReal habs hB) x
  have hY : aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal (f y ^ 2)) x ≠ ⊤ :=
    aux_fsrkb_symm_R_ne_top K U lam hlam
      (aux_fsrkb_symm_bdd_ofReal (hf_meas.pow_const 2) hsqB) x
  set X := aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal |f y|) x with hX_def
  set Y := aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal (f y ^ 2)) x with hY_def
  obtain ⟨α, hα_def⟩ : ∃ α : ℝ≥0∞, α = ENNReal.ofReal lam * X := ⟨_, rfl⟩
  have hα : α ≠ ⊤ := hα_def ▸ ENNReal.mul_ne_top ENNReal.ofReal_ne_top hX
  have hmono : ∀ y, 2 * α * ENNReal.ofReal |f y| ≤ α * α + ENNReal.ofReal (f y ^ 2) := by
    intro y
    have hsq : ENNReal.ofReal (f y ^ 2) = ENNReal.ofReal |f y| * ENNReal.ofReal |f y| := by
      rw [← sq_abs, sq, ENNReal.ofReal_mul (abs_nonneg _)]
    rw [hsq, mul_assoc]
    exact aux_fsrkb_symm_two_mul_le α (ENNReal.ofReal |f y|)
  have hR2 : aux_fsrkb_symm_R K U lam (fun y => 2 * α * ENNReal.ofReal |f y|) x = 2 * α * X :=
    aux_fsrkb_symm_R_const_mul K U hU lam (2 * α) habsm x
  have hRs : aux_fsrkb_symm_R K U lam (fun y => α * α + ENNReal.ofReal (f y ^ 2)) x =
      aux_fsrkb_symm_R K U lam (fun _ => α * α) x + Y :=
    aux_fsrkb_symm_R_add K U hU lam (b₁ := fun _ => α * α)
      (b₂ := fun y => ENNReal.ofReal (f y ^ 2)) measurable_const x
  have hRc : aux_fsrkb_symm_R K U lam (fun _ => α * α) x ≤ α * α * ENNReal.ofReal lam⁻¹ :=
    aux_fsrkb_symm_R_le K U lam hlam (C := α * α) (fun _ => le_rfl) x
  have h : 2 * α * X ≤ α * α * ENNReal.ofReal lam⁻¹ + Y := by
    calc 2 * α * X = aux_fsrkb_symm_R K U lam (fun y => 2 * α * ENNReal.ofReal |f y|) x :=
          hR2.symm
      _ ≤ aux_fsrkb_symm_R K U lam (fun y => α * α + ENNReal.ofReal (f y ^ 2)) x :=
          aux_fsrkb_symm_R_mono K U lam hmono x
      _ = aux_fsrkb_symm_R K U lam (fun _ => α * α) x + Y := hRs
      _ ≤ α * α * ENNReal.ofReal lam⁻¹ + Y := add_le_add hRc le_rfl
  have hfin : α * α * ENNReal.ofReal lam⁻¹ + Y ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top hα hα) ENNReal.ofReal_ne_top, hY⟩
  have h2 := ENNReal.toReal_mono hfin h
  have hαr : α.toReal = lam * X.toReal := by
    rw [hα_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hlam.le]
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (ENNReal.mul_ne_top hα hα) ENNReal.ofReal_ne_top) hY]
    at h2
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 hlam.le), hαr,
    ENNReal.toReal_ofNat] at h2
  have e1 : 2 * (lam * X.toReal) * X.toReal = 2 * (lam * X.toReal ^ 2) := by ring
  have e2 : lam * X.toReal * (lam * X.toReal) * lam⁻¹ = lam * X.toReal ^ 2 := by
    field_simp
  rw [e1, e2] at h2
  linarith only [h2]

theorem aux_fsrkb_symm_int_R_sq
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hfdd : aux_fsrkb_Fdd K P)
    (μ : Measure (SpatialCoordinates d)) (hsym : SemigroupSymmetric P μ)
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (hμU : μ U ≠ ⊤)
    (lam : ℝ) (hlam : 0 < lam) {f : SpatialCoordinates d → ℝ} (hf : aux_fsrkb_BddMeas f) :
    ∫⁻ x in U, aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal (f y ^ 2)) x ∂μ ≤
      ENNReal.ofReal lam⁻¹ * ∫⁻ x in U, ENNReal.ofReal (f x ^ 2) ∂μ := by
  obtain ⟨hf_meas, B, hB0, hB⟩ := hf
  have hsqB : ∀ y, f y ^ 2 ≤ B ^ 2 := fun y => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB y) 2
  have h1 : aux_fsrkb_symm_Bdd (fun _ : SpatialCoordinates d => (1 : ℝ≥0∞)) :=
    ⟨measurable_const, 1, fun _ => by simp⟩
  have h2 := aux_fsrkb_symm_bdd_ofReal (hf_meas.pow_const 2) hsqB
  have hsymm := (aux_fsrkb_symm_good_R K P hfdd μ hsym U hU hμU lam _ _ h1 h2).1
  simp only at hsymm
  have hmeas : Measurable (fun y => ENNReal.ofReal (f y ^ 2)) :=
    ENNReal.measurable_ofReal.comp (hf_meas.pow_const 2)
  calc ∫⁻ x in U, aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal (f y ^ 2)) x ∂μ
      = aux_fsrkb_symm_RPair K μ U lam (fun _ => 1) (fun y => ENNReal.ofReal (f y ^ 2)) := by
        unfold aux_fsrkb_symm_RPair; simp only [one_mul]
    _ = aux_fsrkb_symm_RPair K μ U lam (fun y => ENNReal.ofReal (f y ^ 2)) (fun _ => 1) := hsymm
    _ ≤ ∫⁻ x in U, ENNReal.ofReal (f x ^ 2) * ENNReal.ofReal lam⁻¹ ∂μ := by
        unfold aux_fsrkb_symm_RPair
        refine lintegral_mono fun x => mul_le_mul' le_rfl ?_
        have := aux_fsrkb_symm_R_le K U lam hlam (b := fun _ => (1 : ℝ≥0∞)) (C := 1)
          (fun _ => le_rfl) x
        simpa using this
    _ = ENNReal.ofReal lam⁻¹ * ∫⁻ x in U, ENNReal.ofReal (f x ^ 2) ∂μ := by
        rw [lintegral_mul_const _ hmeas, mul_comm]

theorem aux_fsrkb_symm_main_L2
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hfdd : aux_fsrkb_Fdd K P)
    (μ : Measure (SpatialCoordinates d)) (hsym : SemigroupSymmetric P μ)
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (hμU : μ U ≠ ⊤)
    (lam : ℝ) (hlam : 0 < lam) (f : SpatialCoordinates d → ℝ) (hf : aux_fsrkb_BddMeas f) :
    ∫ x in U, (aux_fsrkb_killedRes K U lam f x) ^ 2 ∂μ ≤
      (lam⁻¹) ^ 2 * ∫ x in U, (f x) ^ 2 ∂μ := by
  haveI : IsFiniteMeasure (μ.restrict U) := isFiniteMeasure_restrict.2 hμU
  have hf' := hf
  obtain ⟨hf_meas, B, hB0, hB⟩ := hf'
  have hsqB : ∀ y, f y ^ 2 ≤ B ^ 2 := fun y => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB y) 2
  have hsqm : Measurable (fun y => f y ^ 2) := hf_meas.pow_const 2
  have hRm : Measurable (aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal (f y ^ 2))) :=
    aux_fsrkb_symm_R_measurable K U hU lam (ENNReal.measurable_ofReal.comp hsqm)
  have hRne : ∀ x, aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal (f y ^ 2)) x ≠ ⊤ :=
    fun x => aux_fsrkb_symm_R_ne_top K U lam hlam (aux_fsrkb_symm_bdd_ofReal hsqm hsqB) x
  have hlinv : 0 ≤ lam⁻¹ := inv_nonneg.2 hlam.le
  have hpt : ∀ x, (aux_fsrkb_killedRes K U lam f x) ^ 2 ≤
      lam⁻¹ * (aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal (f y ^ 2)) x).toReal := by
    intro x
    have ha := aux_fsrkb_symm_abs_le K U hU lam hlam hf x
    have hc := aux_fsrkb_symm_cs K U hU lam hlam hf x
    calc (aux_fsrkb_killedRes K U lam f x) ^ 2 = |aux_fsrkb_killedRes K U lam f x| ^ 2 :=
          (sq_abs _).symm
      _ ≤ ((aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal |f y|) x).toReal) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) ha 2
      _ = lam⁻¹ * (lam * ((aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal |f y|) x).toReal) ^ 2) := by
          field_simp
      _ ≤ lam⁻¹ * (aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal (f y ^ 2)) x).toReal :=
          mul_le_mul_of_nonneg_left hc hlinv
  have hint : Integrable (fun x => lam⁻¹ *
      (aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal (f y ^ 2)) x).toReal) (μ.restrict U) := by
    refine aux_fsrkb_symm_integrable_of_abs_le (measurable_const.mul hRm.ennreal_toReal)
      (lam⁻¹ * (B ^ 2 * lam⁻¹)) (fun x => ?_)
    rw [abs_mul, abs_of_nonneg hlinv, abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul_of_nonneg_left
      (aux_fsrkb_symm_R_toReal_le K U lam hlam (sq_nonneg B) hsqB x) hlinv
  have hfinsq : ∫⁻ x in U, ENNReal.ofReal (f x ^ 2) ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hsqB x)))
    rw [lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμU
  calc ∫ x in U, (aux_fsrkb_killedRes K U lam f x) ^ 2 ∂μ
      ≤ ∫ x in U, lam⁻¹ *
          (aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal (f y ^ 2)) x).toReal ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) hint (ae_of_all _ hpt)
    _ = lam⁻¹ * (∫⁻ x in U,
          aux_fsrkb_symm_R K U lam (fun y => ENNReal.ofReal (f y ^ 2)) x ∂μ).toReal := by
        rw [integral_const_mul, integral_toReal hRm.aemeasurable
          (ae_of_all _ fun x => (hRne x).lt_top)]
    _ ≤ lam⁻¹ * (ENNReal.ofReal lam⁻¹ * ∫⁻ x in U, ENNReal.ofReal (f x ^ 2) ∂μ).toReal :=
        mul_le_mul_of_nonneg_left (ENNReal.toReal_mono
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinsq)
          (aux_fsrkb_symm_int_R_sq K P hfdd μ hsym U hU hμU lam hlam hf)) hlinv
    _ = (lam⁻¹) ^ 2 * ∫ x in U, (f x) ^ 2 ∂μ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hlinv,
          integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg (f x))
            hsqm.aestronglyMeasurable]
        ring

end Final


theorem aux_fsrkb_killedRes_symm
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hfdd : aux_fsrkb_Fdd K P)
    (μ : Measure (SpatialCoordinates d)) (hsym : SemigroupSymmetric P μ)
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (hμU : μ U ≠ ⊤)
    (lam : ℝ) (hlam : 0 < lam) (f g : SpatialCoordinates d → ℝ)
    (hf : aux_fsrkb_BddMeas f) (hg : aux_fsrkb_BddMeas g) :
    ∫ x in U, g x * aux_fsrkb_killedRes K U lam f x ∂μ =
      ∫ x in U, f x * aux_fsrkb_killedRes K U lam g x ∂μ :=
  aux_fsrkb_symm_main_symm K P hfdd μ hsym U hU hμU lam hlam f g hf hg

theorem aux_fsrkb_killedRes_pairing_nonneg
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hfdd : aux_fsrkb_Fdd K P)
    (μ : Measure (SpatialCoordinates d)) (hsym : SemigroupSymmetric P μ)
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (hμU : μ U ≠ ⊤)
    (lam : ℝ) (hlam : 0 < lam) (f : SpatialCoordinates d → ℝ) (hf : aux_fsrkb_BddMeas f) :
    0 ≤ ∫ x in U, f x * aux_fsrkb_killedRes K U lam f x ∂μ :=
  aux_fsrkb_symm_main_nonneg K P hfdd μ hsym U hU hμU lam hlam f hf

theorem aux_fsrkb_killedRes_L2
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hfdd : aux_fsrkb_Fdd K P)
    (μ : Measure (SpatialCoordinates d)) (hsym : SemigroupSymmetric P μ)
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (hμU : μ U ≠ ⊤)
    (lam : ℝ) (hlam : 0 < lam) (f : SpatialCoordinates d → ℝ) (hf : aux_fsrkb_BddMeas f) :
    ∫ x in U, (aux_fsrkb_killedRes K U lam f x) ^ 2 ∂μ ≤
      (lam⁻¹) ^ 2 * ∫ x in U, (f x) ^ 2 ∂μ :=
  aux_fsrkb_symm_main_L2 K P hfdd μ hsym U hU hμU lam hlam f hf

end KbSymm

section KbLaxMilgram

open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology Distributions

variable {d : ℕ}

/-! ### Abstract Lax--Milgram on the killed graph -/

/-- The pair (function, gradient) with the Hilbert norm of `L² × L²(ℝᵈ)`. -/
noncomputable def aux_fsrkb_KbLaxMilgram_pairMap {Ω : TopologicalSpace.Opens (SpatialCoordinates d)} :
    SobolevData Ω →L[ℝ] WithLp 2 (DomainL2 Ω × HilbertGradient Ω) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (DomainL2 Ω) (HilbertGradient Ω)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.fst ℝ _ _).prod sobolevGradient)

theorem aux_fsrkb_KbLaxMilgram_pairMap_fst {Ω : TopologicalSpace.Opens (SpatialCoordinates d)}
    (z : SobolevData Ω) : (aux_fsrkb_KbLaxMilgram_pairMap z).fst = z.1 := rfl

theorem aux_fsrkb_KbLaxMilgram_pairMap_snd {Ω : TopologicalSpace.Opens (SpatialCoordinates d)}
    (z : SobolevData Ω) : (aux_fsrkb_KbLaxMilgram_pairMap z).snd = sobolevGradient z := rfl

/-- The Hilbert norm of the pair dominates the product norm of Sobolev data. -/
theorem aux_fsrkb_KbLaxMilgram_norm_le {Ω : TopologicalSpace.Opens (SpatialCoordinates d)}
    (z : SobolevData Ω) : ‖z‖ ≤ 1 * ‖aux_fsrkb_KbLaxMilgram_pairMap z‖ := by
  rw [one_mul]
  have hsq := WithLp.prod_norm_sq_eq_of_L2 (aux_fsrkb_KbLaxMilgram_pairMap z)
  rw [aux_fsrkb_KbLaxMilgram_pairMap_fst, aux_fsrkb_KbLaxMilgram_pairMap_snd] at hsq
  have hn := norm_nonneg (aux_fsrkb_KbLaxMilgram_pairMap z)
  have h1 : ‖z.1‖ ≤ ‖aux_fsrkb_KbLaxMilgram_pairMap z‖ := by
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) hn two_ne_zero, hsq]
    linarith only [sq_nonneg ‖sobolevGradient z‖]
  have h2 : ‖sobolevGradient z‖ ≤ ‖aux_fsrkb_KbLaxMilgram_pairMap z‖ := by
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) hn two_ne_zero, hsq]
    linarith only [sq_nonneg ‖z.1‖]
  have hgrad : ‖z.2‖ ≤ ‖sobolevGradient z‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    exact PiLp.norm_apply_le (sobolevGradient z) i
  rw [Prod.norm_def]
  exact max_le h1 (hgrad.trans h2)

/-- The coercive bilinear form `B(p,q) = E(p₂,q₂) + lam ⟨p₁,q₁⟩_w` on the pair space. -/
noncomputable def aux_fsrkb_KbLaxMilgram_pairForm {Ω : TopologicalSpace.Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (w : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (lam : ℝ) :
    WithLp 2 (DomainL2 Ω × HilbertGradient Ω) →L[ℝ]
      WithLp 2 (DomainL2 Ω × HilbertGradient Ω) →L[ℝ] ℝ :=
  (weightedGradientForm a.val).bilinearComp (WithLp.sndL 2 ℝ (DomainL2 Ω) (HilbertGradient Ω))
      (WithLp.sndL 2 ℝ (DomainL2 Ω) (HilbertGradient Ω)) +
    lam • (weightedL2Form (E := ℝ) w).bilinearComp (WithLp.fstL 2 ℝ (DomainL2 Ω) (HilbertGradient Ω))
      (WithLp.fstL 2 ℝ (DomainL2 Ω) (HilbertGradient Ω))

theorem aux_fsrkb_KbLaxMilgram_pairForm_apply {Ω : TopologicalSpace.Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (w : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (lam : ℝ) (p q : WithLp 2 (DomainL2 Ω × HilbertGradient Ω)) :
    aux_fsrkb_KbLaxMilgram_pairForm a w lam p q =
      weightedGradientForm a.val p.snd q.snd + lam * weightedL2Form w p.fst q.fst := by
  simp only [aux_fsrkb_KbLaxMilgram_pairForm, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.bilinearComp_apply, WithLp.sndL_apply,
    WithLp.fstL_apply, smul_eq_mul]

theorem aux_fsrkb_KbLaxMilgram_pairForm_lower {Ω : TopologicalSpace.Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (w : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))))
    {c : ℝ} (hc : 0 < c) (hw : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), c ≤ w x)
    {lam : ℝ} (hlam : 0 < lam) :
    ∃ m : ℝ, 0 < m ∧ ∀ p : WithLp 2 (DomainL2 Ω × HilbertGradient Ω),
      m * (‖p.fst‖ ^ 2 + ‖p.snd‖ ^ 2) ≤ aux_fsrkb_KbLaxMilgram_pairForm a w lam p p := by
  obtain ⟨ca, hca, haa⟩ := a.property
  have hcoer := weightedGradientForm_coercive a.val hca haa
  rcases hcoer with ⟨cg, hcg, hbg⟩
  refine ⟨min cg (lam * c), lt_min hcg (mul_pos hlam hc), fun p => ?_⟩
  rw [aux_fsrkb_KbLaxMilgram_pairForm_apply]
  have h1 := hbg p.snd
  have h2 := weightedL2Form_lower w hw p.fst
  have hm1 : min cg (lam * c) * ‖p.snd‖ ^ 2 ≤ cg * ‖p.snd‖ * ‖p.snd‖ := by
    rw [mul_assoc, ← pow_two]
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
  have hm2 : min cg (lam * c) * ‖p.fst‖ ^ 2 ≤ lam * (c * ‖p.fst‖ ^ 2) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
  have hm3 : lam * (c * ‖p.fst‖ ^ 2) ≤ lam * weightedL2Form w p.fst p.fst :=
    mul_le_mul_of_nonneg_left h2 hlam.le
  have hdist : min cg (lam * c) * (‖p.fst‖ ^ 2 + ‖p.snd‖ ^ 2) =
      min cg (lam * c) * ‖p.fst‖ ^ 2 + min cg (lam * c) * ‖p.snd‖ ^ 2 := mul_add _ _ _
  linarith only [hm1, hm2, hm3, h1, hdist]

/-- **Abstract Lax--Milgram through an antilipschitz embedding into a Hilbert space.** -/
theorem aux_fsrkb_KbLaxMilgram_generic {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (J : V →L[ℝ] E) {K : ℝ≥0} (hJ : AntilipschitzWith K J) (B : E →L[ℝ] E →L[ℝ] ℝ)
    {m : ℝ} (hm : 0 < m) (hB : ∀ p : E, m * ‖p‖ ^ 2 ≤ B p p) (L : V →L[ℝ] ℝ) :
    ∃! u : V, ∀ v : V, B (J u) (J v) = L v := by
  have hcl : IsClosed (Set.range J) := hJ.isClosed_range J.uniformContinuous
  have hcl' : IsClosed ((LinearMap.range J : Submodule ℝ E) : Set E) := by
    rw [LinearMap.coe_range]
    exact hcl
  haveI : CompleteSpace (LinearMap.range J) := hcl'.completeSpace_coe
  have hB' : IsCoercive (B.bilinearComp (LinearMap.range J).subtypeL (LinearMap.range J).subtypeL) := by
    refine ⟨m, hm, fun p => ?_⟩
    rw [ContinuousLinearMap.bilinearComp_apply, Submodule.subtypeL_apply, Submodule.coe_norm,
      mul_assoc, ← pow_two]
    exact hB _
  have h := existsUnique_pullback_bilin_eq_load (J.equivRange hJ.injective hcl) hB' L
  simpa only [ContinuousLinearMap.bilinearComp_apply, Submodule.subtypeL_apply,
    ContinuousLinearMap.coe_equivRange, LinearMap.codRestrict_apply,
    LinearMap.rangeRestrict] using h

/-- The pair form evaluated on the pair map is the weak-equation form. -/
theorem aux_fsrkb_KbLaxMilgram_pairForm_pairMap {Ω : TopologicalSpace.Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (w : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (lam : ℝ) (u v : SobolevData Ω) :
    aux_fsrkb_KbLaxMilgram_pairForm a w lam (aux_fsrkb_KbLaxMilgram_pairMap u)
        (aux_fsrkb_KbLaxMilgram_pairMap v) =
      sobolevCoefficientForm a u v + lam * weightedL2Form w u.1 v.1 := by
  rw [aux_fsrkb_KbLaxMilgram_pairForm_apply, aux_fsrkb_KbLaxMilgram_pairMap_fst,
    aux_fsrkb_KbLaxMilgram_pairMap_fst, aux_fsrkb_KbLaxMilgram_pairMap_snd,
    aux_fsrkb_KbLaxMilgram_pairMap_snd]
  rfl

/-- The pair map restricted to the killed graph. -/
noncomputable def aux_fsrkb_KbLaxMilgram_killedPair (Ω : TopologicalSpace.Opens (SpatialCoordinates d)) :
    killedSobolevGraph Ω →L[ℝ] WithLp 2 (DomainL2 Ω × HilbertGradient Ω) :=
  (aux_fsrkb_KbLaxMilgram_pairMap (Ω := Ω)).comp (killedSobolevGraph Ω).subtypeL

theorem aux_fsrkb_KbLaxMilgram_killedPair_antilipschitz
    (Ω : TopologicalSpace.Opens (SpatialCoordinates d)) :
    AntilipschitzWith 1 (aux_fsrkb_KbLaxMilgram_killedPair Ω) :=
  (aux_fsrkb_KbLaxMilgram_killedPair Ω).antilipschitz_of_bound
    fun v => aux_fsrkb_KbLaxMilgram_norm_le (v : SobolevData Ω)

/-- **Abstract Lax--Milgram on the killed graph.** -/
theorem aux_fsrkb_KbLaxMilgram_existsUnique {Ω : TopologicalSpace.Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (w : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))))
    {c : ℝ} (hc : 0 < c) (hw : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), c ≤ w x)
    {lam : ℝ} (hlam : 0 < lam) (L : killedSobolevGraph Ω →L[ℝ] ℝ) :
    ∃! u : killedSobolevGraph Ω, ∀ v : killedSobolevGraph Ω,
      sobolevCoefficientForm a (u : SobolevData Ω) (v : SobolevData Ω) +
        lam * weightedL2Form w (u : SobolevData Ω).1 (v : SobolevData Ω).1 = L v := by
  haveI : CompleteSpace (killedSobolevGraph Ω) :=
    (isClosed_killedSobolevGraph (Ω := Ω)).completeSpace_coe
  obtain ⟨m, hm, hlow⟩ := aux_fsrkb_KbLaxMilgram_pairForm_lower a w hc hw hlam
  have hB : ∀ p : WithLp 2 (DomainL2 Ω × HilbertGradient Ω),
      m * ‖p‖ ^ 2 ≤ aux_fsrkb_KbLaxMilgram_pairForm a w lam p p := by
    intro p
    rw [WithLp.prod_norm_sq_eq_of_L2]
    exact hlow p
  have h := aux_fsrkb_KbLaxMilgram_generic (aux_fsrkb_KbLaxMilgram_killedPair Ω)
    (aux_fsrkb_KbLaxMilgram_killedPair_antilipschitz Ω)
    (aux_fsrkb_KbLaxMilgram_pairForm a w lam) hm hB L
  have hBT : ∀ u v : killedSobolevGraph Ω,
      aux_fsrkb_KbLaxMilgram_pairForm a w lam (aux_fsrkb_KbLaxMilgram_killedPair Ω u)
          (aux_fsrkb_KbLaxMilgram_killedPair Ω v) =
        sobolevCoefficientForm a (u : SobolevData Ω) (v : SobolevData Ω) +
          lam * weightedL2Form w (u : SobolevData Ω).1 (v : SobolevData Ω).1 :=
    fun u v => aux_fsrkb_KbLaxMilgram_pairForm_pairMap a w lam (u : SobolevData Ω) (v : SobolevData Ω)
  simpa only [hBT] using h

/-! ### The speed density on the cube -/

theorem aux_fsrkb_KbLaxMilgram_rho_pos (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (x : SpatialCoordinates d) : 0 < cutoffSpeedDensity M H omega N x :=
  Real.exp_pos _

theorem aux_fsrkb_KbLaxMilgram_rho_cont (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ) :
    Continuous (cutoffSpeedDensity M H omega N) := by
  have hpot : Continuous (cutoffPotential H omega N) := by
    unfold cutoffPotential
    fun_prop
  unfold cutoffSpeedDensity
  exact Real.continuous_exp.comp (hpot.sub continuous_const)

/-- The speed density is bounded above and below by positive constants on the cube. -/
theorem aux_fsrkb_KbLaxMilgram_rho_bounds (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ c C : ℝ, 0 < c ∧ ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
      c ≤ cutoffSpeedDensity M H omega N x ∧ cutoffSpeedDensity M H omega N x ≤ C := by
  have hK : IsCompact (Metric.closedBall z (r / 2)) := isCompact_closedBall z (r / 2)
  have hne : (Metric.closedBall z (r / 2)).Nonempty :=
    ⟨z, Metric.mem_closedBall_self (by linarith only [hr])⟩
  have hcont := (aux_fsrkb_KbLaxMilgram_rho_cont M H omega N).continuousOn
    (s := Metric.closedBall z (r / 2))
  obtain ⟨x0, -, hx0⟩ := hK.exists_isMinOn hne hcont
  obtain ⟨x1, -, hx1⟩ := hK.exists_isMaxOn hne hcont
  refine ⟨cutoffSpeedDensity M H omega N x0, cutoffSpeedDensity M H omega N x1,
    aux_fsrkb_KbLaxMilgram_rho_pos M H omega N x0, fun x hx => ?_⟩
  have hx' : x ∈ Metric.closedBall z (r / 2) := Metric.ball_subset_closedBall hx
  exact ⟨hx0 hx', hx1 hx'⟩

/-- The L∞ class of the speed density on the cube, with its positive lower bound. -/
theorem aux_fsrkb_KbLaxMilgram_rhoL (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ w : Lp ℝ ∞ (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
      (∃ c : ℝ, 0 < c ∧
        ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), c ≤ w x) ∧
      (w : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
          cutoffSpeedDensity M H omega N := by
  obtain ⟨c, C, hc, hbd⟩ := aux_fsrkb_KbLaxMilgram_rho_bounds M H omega N z r hr
  have hQ : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  have hmem : MemLp (cutoffSpeedDensity M H omega N) ∞
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    refine memLp_top_of_bound
      (aux_fsrkb_KbLaxMilgram_rho_cont M H omega N).aestronglyMeasurable C ?_
    filter_upwards [ae_restrict_mem hQ] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (aux_fsrkb_KbLaxMilgram_rho_pos M H omega N x)]
    exact (hbd x hx).2
  refine ⟨hmem.toLp _, ⟨c, hc, ?_⟩, hmem.coeFn_toLp⟩
  filter_upwards [hmem.coeFn_toLp, ae_restrict_mem hQ] with x hx hxQ
  rw [hx]
  exact (hbd x hxQ).1

/-- A bounded measurable source is an `L²` class on the cube. -/
theorem aux_fsrkb_KbLaxMilgram_srcL (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (f : SpatialCoordinates d → ℝ) (hf : aux_fsrkb_BddMeas f) :
    ∃ F : DomainL2 (centeredCube z r hr),
      (F : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f := by
  rcases hf with ⟨hfm, B, -, hB⟩
  haveI : IsFiniteMeasure
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    refine isFiniteMeasure_restrict.mpr ?_
    exact (measure_ball_lt_top (μ := (volume : Measure (SpatialCoordinates d)))
      (x := z) (r := r / 2)).ne
  have hmem : MemLp f 2
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    MemLp.of_bound hfm.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)
  exact ⟨hmem.toLp f, hmem.coeFn_toLp⟩

/-- Integrals against the speed measure on the cube are Lebesgue integrals with density. -/
theorem aux_fsrkb_KbLaxMilgram_speed_integral (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h : SpatialCoordinates d → ℝ) :
    ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), h x
        ∂(cutoffSpeedMeasure M H omega N) =
      ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        cutoffSpeedDensity M H omega N x * h x := by
  have hQ : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  rw [cutoffSpeedMeasure, restrict_withDensity hQ,
    integral_withDensity_eq_integral_toReal_smul
      (f := ENNReal.ofReal ∘ cutoffSpeedDensity M H omega N)
      (aux_fsrkb_KbLaxMilgram_rho_cont M H omega N).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (aux_fsrkb_KbLaxMilgram_rho_pos M H omega N x).le]

/-- The speed-measure load of the weak equation, as `L²(Q)` weighted pairings. -/
theorem aux_fsrkb_KbLaxMilgram_load_identity (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (lam : ℝ)
    (w : Lp ℝ ∞ (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hw : (w : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
          cutoffSpeedDensity M H omega N)
    (f : SpatialCoordinates d → ℝ) (F : DomainL2 (centeredCube z r hr))
    (hF : (F : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f)
    (u1 v1 : DomainL2 (centeredCube z r hr)) :
    ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        (f x - lam * u1 x) * v1 x ∂(cutoffSpeedMeasure M H omega N) =
      weightedL2Form w F v1 - lam * weightedL2Form w u1 v1 := by
  rw [aux_fsrkb_KbLaxMilgram_speed_integral]
  have hlin : weightedL2Form w F v1 - lam * weightedL2Form w u1 v1 =
      weightedL2Form w (F - lam • u1) v1 := by
    rw [map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
  rw [hlin, weightedL2Form_apply]
  refine integral_congr_ae ?_
  filter_upwards [hw, hF, Lp.coeFn_sub F (lam • u1), Lp.coeFn_smul lam u1]
    with x hx1 hx2 hx3 hx4
  rw [hx1, hx3, Pi.sub_apply, hx4, Pi.smul_apply, hx2, smul_eq_mul]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- The weak equation, rewritten with the weighted `L²(Q)` pairings. -/
theorem aux_fsrkb_KbLaxMilgram_weakEq_iff (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (lam : ℝ)
    (w : Lp ℝ ∞ (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hw : (w : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
          cutoffSpeedDensity M H omega N)
    (f : SpatialCoordinates d → ℝ) (F : DomainL2 (centeredCube z r hr))
    (hF : (F : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f)
    (u : killedSobolevGraph (centeredCube z r hr)) :
    aux_fsrkb_WeakEq M H omega N z r hr lam f u ↔
      ∀ v : killedSobolevGraph (centeredCube z r hr),
        sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr)
            (u : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr)) +
          lam * weightedL2Form w (u : SobolevData (centeredCube z r hr)).1
            (v : SobolevData (centeredCube z r hr)).1 =
        weightedL2Form w F (v : SobolevData (centeredCube z r hr)).1 := by
  unfold aux_fsrkb_WeakEq
  constructor
  · intro hu v
    have h := hu v
    rw [aux_fsrkb_KbLaxMilgram_load_identity M H omega N z r hr lam w hw f F hF] at h
    rw [h]
    ring
  · intro hu v
    have h := hu v
    rw [aux_fsrkb_KbLaxMilgram_load_identity M H omega N z r hr lam w hw f F hF]
    rw [← h]
    ring

/-- **Existence of the weak killed solution.** -/
theorem aux_fsrkb_exists_weakEq (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (lam : ℝ) (hlam : 0 < lam)
    (f : SpatialCoordinates d → ℝ) (hf : aux_fsrkb_BddMeas f) :
    ∃ u : killedSobolevGraph (centeredCube z r hr), aux_fsrkb_WeakEq M H omega N z r hr lam f u := by
  obtain ⟨w, ⟨c, hc, hwc⟩, hw⟩ := aux_fsrkb_KbLaxMilgram_rhoL M H omega N z r hr
  obtain ⟨F, hF⟩ := aux_fsrkb_KbLaxMilgram_srcL z r hr f hf
  let L : killedSobolevGraph (centeredCube z r hr) →L[ℝ] ℝ :=
    (weightedL2Form w F).comp
      ((ContinuousLinearMap.fst ℝ _ _).comp (killedSobolevGraph (centeredCube z r hr)).subtypeL)
  have hex := aux_fsrkb_KbLaxMilgram_existsUnique
    (Lane4.cutoffPositiveCoefficient M H omega N z hr) w hc hwc hlam L
  rcases hex with ⟨u, hu, -⟩
  exact ⟨u, (aux_fsrkb_KbLaxMilgram_weakEq_iff M H omega N z r hr lam w hw f F hF u).mpr hu⟩

/-- **Uniqueness of the weak killed solution.** -/
theorem aux_fsrkb_weakEq_unique (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (lam : ℝ) (hlam : 0 < lam)
    (f : SpatialCoordinates d → ℝ) (hf : aux_fsrkb_BddMeas f)
    (u u' : killedSobolevGraph (centeredCube z r hr))
    (hu : aux_fsrkb_WeakEq M H omega N z r hr lam f u)
    (hu' : aux_fsrkb_WeakEq M H omega N z r hr lam f u') :
    ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] ((u' : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) := by
  obtain ⟨w, ⟨c, hc, hwc⟩, hw⟩ := aux_fsrkb_KbLaxMilgram_rhoL M H omega N z r hr
  obtain ⟨F, hF⟩ := aux_fsrkb_KbLaxMilgram_srcL z r hr f hf
  let L : killedSobolevGraph (centeredCube z r hr) →L[ℝ] ℝ :=
    (weightedL2Form w F).comp
      ((ContinuousLinearMap.fst ℝ _ _).comp (killedSobolevGraph (centeredCube z r hr)).subtypeL)
  have hex := aux_fsrkb_KbLaxMilgram_existsUnique
    (Lane4.cutoffPositiveCoefficient M H omega N z hr) w hc hwc hlam L
  rcases hex with ⟨u0, -, huniq⟩
  have h1 := huniq u ((aux_fsrkb_KbLaxMilgram_weakEq_iff M H omega N z r hr lam w hw f F hF u).mp hu)
  have h2 := huniq u' ((aux_fsrkb_KbLaxMilgram_weakEq_iff M H omega N z r hr lam w hw f F hF u').mp hu')
  rw [h1, h2]

/-- **Linearity of the weak killed solution.** -/
theorem aux_fsrkb_weakEq_add (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (lam : ℝ)
    (f g : SpatialCoordinates d → ℝ) (hf : aux_fsrkb_BddMeas f) (hg : aux_fsrkb_BddMeas g)
    (u w : killedSobolevGraph (centeredCube z r hr))
    (hu : aux_fsrkb_WeakEq M H omega N z r hr lam f u)
    (hw : aux_fsrkb_WeakEq M H omega N z r hr lam g w) :
    aux_fsrkb_WeakEq M H omega N z r hr lam (fun x => f x + g x) (u + w) := by
  obtain ⟨ρL, -, hρ⟩ := aux_fsrkb_KbLaxMilgram_rhoL M H omega N z r hr
  obtain ⟨F, hF⟩ := aux_fsrkb_KbLaxMilgram_srcL z r hr f hf
  obtain ⟨G, hG⟩ := aux_fsrkb_KbLaxMilgram_srcL z r hr g hg
  have hFG : ((F + G : DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        fun x => f x + g x := by
    filter_upwards [Lp.coeFn_add F G, hF, hG] with x hx h1 h2
    rw [hx, Pi.add_apply, h1, h2]
  have hu' := (aux_fsrkb_KbLaxMilgram_weakEq_iff M H omega N z r hr lam ρL hρ f F hF u).mp hu
  have hw' := (aux_fsrkb_KbLaxMilgram_weakEq_iff M H omega N z r hr lam ρL hρ g G hG w).mp hw
  refine (aux_fsrkb_KbLaxMilgram_weakEq_iff M H omega N z r hr lam ρL hρ
    (fun x => f x + g x) (F + G) hFG (u + w)).mpr fun v => ?_
  have h1 := hu' v
  have h2 := hw' v
  have hsplit : ((u + w : killedSobolevGraph (centeredCube z r hr)) :
      SobolevData (centeredCube z r hr)) =
      (u : SobolevData (centeredCube z r hr)) + (w : SobolevData (centeredCube z r hr)) := rfl
  rw [hsplit, Prod.fst_add, map_add, map_add, map_add, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
  linarith only [h1, h2]

end KbLaxMilgram

section KbMaxPrinciple

open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology Distributions

variable {d : ℕ}

/-- The positive part of a killed datum is killed, with the truncated gradient
`1_{u>0} ∇u` (upstream `H¹₀` lattice property on the convex cube). -/
theorem aux_fsrkb_KbMaxPrinciple_posPart (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (u : killedSobolevGraph (centeredCube z r hr)) :
    ∃ T : killedSobolevGraph (centeredCube z r hr),
      (((T : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
          fun x => max ((u : SobolevData (centeredCube z r hr)).1 x) 0) ∧
      ∀ i : Fin d, (((T : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
          fun x => if 0 < (u : SobolevData (centeredCube z r hr)).1 x then
            (u : SobolevData (centeredCube z r hr)).2 i x else 0) := by
  have hU := lane2_isOpenBoundedConvexDomain_centeredCube z hr
  have hnat := exists_nativeH10Function_of_killedSobolevGraph u
  rcases hnat with ⟨v, hv1, hv2⟩
  have hmax := Homogenization.exists_h1_max_sub_const hU v.toH1Function 0
  rcases hmax with ⟨p, hp1, hp2⟩
  have hmatch : Homogenization.MemH10 (centeredCube z r hr : Set (SpatialCoordinates d))
      (fun x => v.toH1Function.toFun x -
        (0 : Homogenization.H1Function (centeredCube z r hr : Set (SpatialCoordinates d))).toFun x) :=
    ⟨v, funext fun x => (sub_zero _).symm⟩
  have hm := Homogenization.memH10_max_sub_matched hU v.toH1Function 0 hmatch 0
  rcases hm with ⟨q, hq⟩
  have hqp : q.toH1Function.toFun = p.toFun := by
    rw [hq, hp1]
    funext x
    change max (v.toH1Function.toFun x - 0) 0 - max ((0 : ℝ) - 0) 0 = _
    rw [sub_self, max_self, sub_zero]
  have hT := sobolevDataOfH1_mem_killed q
  have hP := sobolevDataOfH1_mem_weak p
  have h1 : (sobolevDataOfH1 q.toH1Function).1 = (sobolevDataOfH1 p).1 := by
    apply Lp.ext
    refine (sobolevDataOfH1_fst_coeFn q.toH1Function).trans ?_
    rw [hqp]
    exact (sobolevDataOfH1_fst_coeFn p).symm
  have h2 : (sobolevDataOfH1 q.toH1Function).2 = (sobolevDataOfH1 p).2 := by
    have hTw := killedSobolevGraph_le_weakSobolevGraph hT
    refine weakSobolevGraph_gradient_unique (u := (sobolevDataOfH1 q.toH1Function).1) hTw ?_
    rw [h1]
    exact hP
  refine ⟨⟨sobolevDataOfH1 q.toH1Function, hT⟩, ?_, fun i => ?_⟩
  · refine (sobolevDataOfH1_fst_coeFn q.toH1Function).trans ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [hqp, hp1]
    change max (v.toH1Function.toFun x - 0) 0 = _
    rw [sub_zero, hv1]
  · change (((sobolevDataOfH1 q.toH1Function).2 i : DomainL2 (centeredCube z r hr)) :
      SpatialCoordinates d → ℝ) =ᵐ[_] _
    rw [h2]
    refine (sobolevDataOfH1_snd_coeFn p i).trans ?_
    filter_upwards [hp2] with x hx
    rw [hx]
    by_cases hpos : 0 < v.toH1Function.toFun x
    · have hpos' : 0 < (u : SobolevData (centeredCube z r hr)).1 x := by
        rw [hv1] at hpos
        exact hpos
      rw [Set.indicator_of_mem (show x ∈ {y | 0 < v.toH1Function.toFun y} from hpos), hv2,
        if_pos hpos']
    · have hpos' : ¬ 0 < (u : SobolevData (centeredCube z r hr)).1 x := by
        rw [hv1] at hpos
        exact hpos
      rw [Set.indicator_of_notMem (show x ∉ {y | 0 < v.toH1Function.toFun y} from hpos),
        if_neg hpos']
      rfl

/-- The negative part of a killed datum: killed, equal to `max (-u) 0`, and its gradient
pairs nonpositively with `∇u`. -/
theorem aux_fsrkb_KbMaxPrinciple_negPart (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (u : killedSobolevGraph (centeredCube z r hr)) :
    ∃ T : killedSobolevGraph (centeredCube z r hr),
      (((T : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
          fun x => max (-((u : SobolevData (centeredCube z r hr)).1 x)) 0) ∧
      ∀ i : Fin d, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        (u : SobolevData (centeredCube z r hr)).2 i x *
          (T : SobolevData (centeredCube z r hr)).2 i x ≤ 0 := by
  have hpp := aux_fsrkb_KbMaxPrinciple_posPart z r hr (-u)
  rcases hpp with ⟨T, hT1, hT2⟩
  have hneg : ((-u : killedSobolevGraph (centeredCube z r hr)) :
      SobolevData (centeredCube z r hr)) = -(u : SobolevData (centeredCube z r hr)) := rfl
  rw [hneg] at hT1 hT2
  refine ⟨T, ?_, fun i => ?_⟩
  · filter_upwards [hT1, Lp.coeFn_neg (u : SobolevData (centeredCube z r hr)).1] with x hx hn
    rw [hx]
    change max (((-(u : SobolevData (centeredCube z r hr)).1 : DomainL2 (centeredCube z r hr)) :
      SpatialCoordinates d → ℝ) x) 0 = _
    rw [hn, Pi.neg_apply]
  · filter_upwards [hT2 i, Lp.coeFn_neg ((u : SobolevData (centeredCube z r hr)).2 i)]
      with x hx hn
    rw [hx]
    split_ifs with hpos
    · change (u : SobolevData (centeredCube z r hr)).2 i x *
          ((-((u : SobolevData (centeredCube z r hr)).2 i) : DomainL2 (centeredCube z r hr)) :
            SpatialCoordinates d → ℝ) x ≤ 0
      rw [hn, Pi.neg_apply, mul_neg]
      exact neg_nonpos.mpr (mul_self_nonneg _)
    · rw [mul_zero]

/-- Testing the energy with the negative part gives a nonpositive number. -/
theorem aux_fsrkb_KbMaxPrinciple_energy_nonpos {Ω : TopologicalSpace.Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (u T : SobolevData Ω)
    (hT : ∀ i : Fin d, ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      u.2 i x * T.2 i x ≤ 0) :
    sobolevCoefficientForm a u T ≤ 0 := by
  have happ : sobolevCoefficientForm a u T = ∑ i : Fin d,
      ∫ x in (Ω : Set (SpatialCoordinates d)), a.val x * (u.2 i x * T.2 i x) :=
    weightedGradientForm_apply a.val _ _
  rw [happ]
  obtain ⟨c, hc, ha⟩ := a.property
  refine Finset.sum_nonpos fun i _ => ?_
  refine integral_nonpos_of_ae ?_
  filter_upwards [ha, hT i] with x hx hxi
  exact mul_nonpos_of_nonneg_of_nonpos (hc.le.trans hx) hxi

/-- The density-weighted load integrand is integrable on the cube. -/
theorem aux_fsrkb_KbMaxPrinciple_integrable (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (lam : ℝ)
    (w : Lp ℝ ∞ (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hw : (w : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
          cutoffSpeedDensity M H omega N)
    (f : SpatialCoordinates d → ℝ) (F : DomainL2 (centeredCube z r hr))
    (hF : (F : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f)
    (u1 v1 : DomainL2 (centeredCube z r hr)) :
    Integrable (fun x => cutoffSpeedDensity M H omega N x * ((f x - lam * u1 x) * v1 x))
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  refine (integrable_weighted_inner w (F - lam • u1) v1).congr ?_
  filter_upwards [hw, hF, Lp.coeFn_sub F (lam • u1), Lp.coeFn_smul lam u1]
    with x hx1 hx2 hx3 hx4
  rw [hx1, hx3, Pi.sub_apply, hx4, Pi.smul_apply, hx2, smul_eq_mul]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- **Nonnegative sources give nonnegative killed solutions.** -/
theorem aux_fsrkb_weakEq_nonneg (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (lam : ℝ) (hlam : 0 < lam)
    (f : SpatialCoordinates d → ℝ) (hf : aux_fsrkb_BddMeas f) (hf0 : ∀ x, 0 ≤ f x)
    (u : killedSobolevGraph (centeredCube z r hr))
    (hu : aux_fsrkb_WeakEq M H omega N z r hr lam f u) :
    ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), 0 ≤ ((u : SobolevData (centeredCube z r hr)).1) x := by
  obtain ⟨ρL, -, hρ⟩ := aux_fsrkb_KbLaxMilgram_rhoL M H omega N z r hr
  obtain ⟨F, hF⟩ := aux_fsrkb_KbLaxMilgram_srcL z r hr f hf
  obtain ⟨T, hT1, hT2⟩ := aux_fsrkb_KbMaxPrinciple_negPart z r hr u
  have hE := hu T
  rw [aux_fsrkb_KbLaxMilgram_speed_integral] at hE
  have hEle := aux_fsrkb_KbMaxPrinciple_energy_nonpos
    (Lane4.cutoffPositiveCoefficient M H omega N z hr) (u : SobolevData (centeredCube z r hr))
    (T : SobolevData (centeredCube z r hr)) hT2
  have hint := aux_fsrkb_KbMaxPrinciple_integrable M H omega N z r hr lam ρL hρ f F hF
    (u : SobolevData (centeredCube z r hr)).1 (T : SobolevData (centeredCube z r hr)).1
  have hpt : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      cutoffSpeedDensity M H omega N x *
          (lam * (max (-((u : SobolevData (centeredCube z r hr)).1 x)) 0) ^ 2) ≤
        cutoffSpeedDensity M H omega N x *
          ((f x - lam * (u : SobolevData (centeredCube z r hr)).1 x) *
            (T : SobolevData (centeredCube z r hr)).1 x) := by
    filter_upwards [hT1] with x hx
    rw [hx]
    refine mul_le_mul_of_nonneg_left ?_
      (aux_fsrkb_KbLaxMilgram_rho_pos M H omega N x).le
    have hfm : 0 ≤ f x * max (-((u : SobolevData (centeredCube z r hr)).1 x)) 0 :=
      mul_nonneg (hf0 x) (le_max_right _ _)
    have hsq : -((u : SobolevData (centeredCube z r hr)).1 x) *
        max (-((u : SobolevData (centeredCube z r hr)).1 x)) 0 =
          (max (-((u : SobolevData (centeredCube z r hr)).1 x)) 0) ^ 2 := by
      rcases le_total (-((u : SobolevData (centeredCube z r hr)).1 x)) 0 with h | h
      · rw [max_eq_right h]
        ring
      · rw [max_eq_left h]
        ring
    have hexp : (f x - lam * (u : SobolevData (centeredCube z r hr)).1 x) *
        max (-((u : SobolevData (centeredCube z r hr)).1 x)) 0 =
          f x * max (-((u : SobolevData (centeredCube z r hr)).1 x)) 0 +
            lam * (-((u : SobolevData (centeredCube z r hr)).1 x) *
              max (-((u : SobolevData (centeredCube z r hr)).1 x)) 0) := by
      ring
    rw [hexp, hsq]
    linarith only [hfm]
  have hnn : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      0 ≤ cutoffSpeedDensity M H omega N x *
          ((f x - lam * (u : SobolevData (centeredCube z r hr)).1 x) *
            (T : SobolevData (centeredCube z r hr)).1 x) := by
    filter_upwards [hpt] with x hx
    refine le_trans ?_ hx
    exact mul_nonneg (aux_fsrkb_KbLaxMilgram_rho_pos M H omega N x).le
      (mul_nonneg hlam.le (sq_nonneg _))
  have hzero : ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      cutoffSpeedDensity M H omega N x *
          ((f x - lam * (u : SobolevData (centeredCube z r hr)).1 x) *
            (T : SobolevData (centeredCube z r hr)).1 x) = 0 := by
    refine le_antisymm ?_ (integral_nonneg_of_ae hnn)
    rw [← hE]
    exact hEle
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp hzero
  filter_upwards [hae, hpt] with x hx hxp
  have hx' : cutoffSpeedDensity M H omega N x *
      ((f x - lam * (u : SobolevData (centeredCube z r hr)).1 x) *
        (T : SobolevData (centeredCube z r hr)).1 x) = 0 := hx
  rw [hx'] at hxp
  have hρpos := aux_fsrkb_KbLaxMilgram_rho_pos M H omega N x
  have hsq0 : lam * (max (-((u : SobolevData (centeredCube z r hr)).1 x)) 0) ^ 2 ≤ 0 :=
    nonpos_of_mul_nonpos_right hxp hρpos
  have hm0 : (max (-((u : SobolevData (centeredCube z r hr)).1 x)) 0) ^ 2 ≤ 0 :=
    nonpos_of_mul_nonpos_right hsq0 hlam
  have hm : max (-((u : SobolevData (centeredCube z r hr)).1 x)) 0 = 0 :=
    pow_eq_zero_iff (n := 2) two_ne_zero |>.mp (le_antisymm hm0 (sq_nonneg _))
  have hle : -((u : SobolevData (centeredCube z r hr)).1 x) ≤ 0 := by
    rw [← hm]
    exact le_max_left _ _
  linarith only [hle]

end KbMaxPrinciple

section KbIBP

open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology Distributions

variable {d : ℕ}

/-- Smooth–smooth integration by parts (copied from the private helper of
`finite_speed_resolvent_properties`). -/
theorem aux_fsrkb_ibp_smooth
    {d : Nat}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : Nat)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hC : ContDiff ℝ 1 (cutoffCoefficient M H omega N))
    (hρ : ∀ x : SpatialCoordinates d,
      cutoffSpeedDensity M H omega N x =
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N * cutoffCoefficient M H omega N x) :
    ∀ phi psi : SpatialCoordinates d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) phi → ContDiff ℝ (⊤ : ℕ∞) psi →
      HasCompactSupport phi → HasCompactSupport psi →
      Function.support phi ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      Function.support psi ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      -(∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ((cutoffSpeedDensity M H omega N x)⁻¹ *
          ∑ i : Fin d,
            (fderiv ℝ (fun y => cutoffCoefficient M H omega N y *
              (fderiv ℝ phi y) (Pi.single i 1)) x) (Pi.single i 1)) * psi x
          ∂(cutoffSpeedMeasure M H omega N)) =
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          cutoffCoefficient M H omega N x *
            (∑ i : Fin d,
              (fderiv ℝ phi x) (Pi.single i 1) *
                (fderiv ℝ psi x) (Pi.single i 1)) := by
  intro phi psi hphi hpsi hphi_compact hpsi_compact hphi_support hpsi_support
  let Q : Set (SpatialCoordinates d) := centeredCube z r hr
  let A : SpatialCoordinates d → ℝ := cutoffCoefficient M H omega N
  let rho : SpatialCoordinates d → ℝ := cutoffSpeedDensity M H omega N
  have hAcont : Continuous A := by
    dsimp [A, cutoffCoefficient]
    refine continuous_const.mul (Real.continuous_exp.comp ?_)
    unfold cutoffPotential
    fun_prop
  have hρpos : ∀ x, 0 < rho x := by
    intro x
    dsimp [rho, cutoffSpeedDensity]
    exact Real.exp_pos _
  have hρmeas : Measurable (fun x => ENNReal.ofReal (rho x)) := by
    have hρcont : Continuous rho := by
      dsimp [rho, cutoffSpeedDensity]
      have hpot : Continuous (cutoffPotential H omega N) := by
        unfold cutoffPotential
        fun_prop
      exact Real.continuous_exp.comp (hpot.sub continuous_const)
    exact hρcont.measurable.ennreal_ofReal
  have hψ_support' : Function.support psi ⊆ Metric.ball z (r / 2) := by
    simpa [Q, centeredCube] using hpsi_support
  have hψ_tsupport : tsupport psi ⊆ Metric.closedBall z (r / 2) := by
    refine closure_minimal (hψ_support'.trans Metric.ball_subset_closedBall) ?_
    exact Metric.isClosed_closedBall
  have hsphere : volume (Metric.sphere z (r / 2)) = 0 := by
    exact Measure.addHaar_sphere_of_ne_zero volume z (by linarith)
  have hderiv_ae (i : Fin d) :
      ∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)),
        x ∉ Q → (fderiv ℝ psi x) (Pi.single i 1) = 0 := by
    rw [ae_iff]
    apply measure_mono_null ?_ hsphere
    intro x hx
    have hxQ : x ∉ Q := by
      intro hxmem
      apply hx
      intro hxnot
      exact (hxnot hxmem).elim
    have hxder : (fderiv ℝ psi x) (Pi.single i 1) ≠ 0 := by
      intro hz
      apply hx
      intro _
      exact hz
    have hxclosed : x ∈ Metric.closedBall z (r / 2) := by
      by_contra hxc
      apply hxder
      have hzero := fderiv_of_notMem_tsupport ℝ (f := psi) (x := x)
      exact congrArg (fun T => T (Pi.single i 1))
        (hzero (fun hxt => hxc (hψ_tsupport hxt)))
    have hle : dist x z ≤ r / 2 := Metric.mem_closedBall.mp hxclosed
    have hnotlt : ¬ dist x z < r / 2 := by
      intro hlt
      exact hxQ (Metric.mem_ball.mpr hlt)
    exact Metric.mem_sphere.mpr (le_antisymm hle (le_of_not_gt hnotlt))
  have hpsi_zero (x : SpatialCoordinates d) (hx : x ∉ Q) : psi x = 0 := by
    by_contra hpx
    exact hx (hpsi_support (Function.mem_support.mpr hpx))
  have hAi (i : Fin d) :
      ContDiff ℝ 1 (fun x => A x * (fderiv ℝ phi x) (Pi.single i 1)) := by
    have hphid : ContDiff ℝ 1
        (fun x => (fderiv ℝ phi x) (Pi.single i 1)) := by
      have hp : ContDiff ℝ 1
          (fun p : (SpatialCoordinates d) × (SpatialCoordinates d) =>
            (fderiv ℝ phi p.1) p.2) :=
        hphi.contDiff_fderiv_apply (by norm_cast)
      have hc : ContDiff ℝ 1
          (fun x : SpatialCoordinates d =>
            (x, (Pi.single i (1 : ℝ) : SpatialCoordinates d))) :=
        by fun_prop
      simpa only [Function.comp_apply] using hp.comp hc
    exact hC.mul hphid
  have hFi_compact (i : Fin d) : HasCompactSupport
      (fun x => A x * (fderiv ℝ phi x) (Pi.single i 1)) := by
    exact (hphi_compact.fderiv_apply ℝ (Pi.single i 1)).mul_left
  have hglobal (i : Fin d) :
      (∫ x, A x * (fderiv ℝ phi x) (Pi.single i 1) *
          (fderiv ℝ psi x) (Pi.single i 1)) =
        -∫ x, (fderiv ℝ
          (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
            (Pi.single i 1) * psi x := by
    let Fi : SpatialCoordinates d → ℝ :=
      fun x => A x * (fderiv ℝ phi x) (Pi.single i 1)
    have hFi_cont : Continuous Fi := (hAi i).continuous
    have hFi_deriv_cont : Continuous (fun x =>
        (fderiv ℝ Fi x) (Pi.single i 1)) := by
      have hp := (hAi i).continuous_fderiv_apply (by simp)
      exact hp.comp (continuous_id.prodMk continuous_const)
    have hphi_deriv_cont : Continuous (fun x =>
        (fderiv ℝ psi x) (Pi.single i 1)) :=
      (hpsi.continuous_fderiv_apply (by simp)).comp
        (continuous_id.prodMk continuous_const)
    have h1 : Integrable
        (fun x => (fderiv ℝ Fi x) (Pi.single i 1) * psi x)
        (volume : Measure (SpatialCoordinates d)) :=
      (hFi_deriv_cont.mul hpsi.continuous).integrable_of_hasCompactSupport
        ((hFi_compact i).fderiv_apply ℝ (Pi.single i 1)).mul_right
    have h2 : Integrable
        (fun x => Fi x * (fderiv ℝ psi x) (Pi.single i 1))
        (volume : Measure (SpatialCoordinates d)) :=
      (hFi_cont.mul hphi_deriv_cont).integrable_of_hasCompactSupport
        (hFi_compact i).mul_right
    have h3 : Integrable (fun x => Fi x * psi x)
        (volume : Measure (SpatialCoordinates d)) :=
      (hFi_cont.mul hpsi.continuous).integrable_of_hasCompactSupport
        (hFi_compact i).mul_right
    have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (f := Fi) (g := psi)
      (v := Pi.single i 1)
      h1 h2 h3
      ((hAi i).differentiable (by simp)) (hpsi.differentiable (by simp))
    · simpa only [Fi] using hibp
  have hleft (i : Fin d) :
      (∫ x in Q, (fderiv ℝ
          (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
            (Pi.single i 1) * psi x) =
        ∫ x, (fderiv ℝ
          (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
            (Pi.single i 1) * psi x := by
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hpsi_zero x hx, mul_zero]
  have hright (i : Fin d) :
      (∫ x in Q, A x * (fderiv ℝ phi x) (Pi.single i 1) *
          (fderiv ℝ psi x) (Pi.single i 1)) =
        ∫ x, A x * (fderiv ℝ phi x) (Pi.single i 1) *
          (fderiv ℝ psi x) (Pi.single i 1) := by
    rw [← integral_indicator (centeredCube z r hr).isOpen.measurableSet]
    apply integral_congr_ae
    filter_upwards [hderiv_ae i] with x hx
    by_cases hqx : x ∈ Q
    · have hqx' : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
        simpa [Q] using hqx
      simp [Set.indicator_of_mem hqx']
    · have hqx' : x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
        simpa [Q] using hqx
      simp [Set.indicator_of_notMem hqx', hx hqx]
  have hcoord (i : Fin d) :
      -(∫ x in Q,
          (rho x)⁻¹ *
            (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
              (Pi.single i 1) * psi x
          ∂(cutoffSpeedMeasure M H omega N)) =
        ∫ x in Q, A x * (fderiv ℝ phi x) (Pi.single i 1) *
          (fderiv ℝ psi x) (Pi.single i 1) := by
    have hdens := setIntegral_withDensity_eq_setIntegral_toReal_smul
      (μ := (volume : Measure (SpatialCoordinates d)))
      (f := fun x => ENNReal.ofReal (rho x))
      hρmeas (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
      (fun x => (rho x)⁻¹ *
        (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
          (Pi.single i 1) * psi x)
      (centeredCube z r hr).isOpen.measurableSet
    have hdens' :
        (∫ x in Q, (rho x)⁻¹ *
          (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
            (Pi.single i 1) * psi x
          ∂(cutoffSpeedMeasure M H omega N)) =
          ∫ x in Q, rho x • ((rho x)⁻¹ *
            (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
              (Pi.single i 1) * psi x) := by
      rw [show cutoffSpeedMeasure M H omega N =
          volume.withDensity (fun x => ENNReal.ofReal (rho x)) by rfl]
      simpa [Q, ENNReal.toReal_ofReal (hρpos _).le, smul_eq_mul] using hdens
    rw [hdens']
    have hcancel (x : SpatialCoordinates d) :
        rho x • ((rho x)⁻¹ *
          (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
            (Pi.single i 1) * psi x) =
          (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
            (Pi.single i 1) * psi x := by
      dsimp only [smul_eq_mul]
      field_simp [ne_of_gt (hρpos x)]
    rw [integral_congr_ae (Filter.Eventually.of_forall hcancel)]
    rw [hleft i, ← hglobal i]
    exact (hright i).symm
  have hRHS_int (i : Fin d) : Integrable
      (fun x => A x * (fderiv ℝ phi x) (Pi.single i 1) *
        (fderiv ℝ psi x) (Pi.single i 1))
      (volume.restrict Q) := by
    have hcont : Continuous (fun x => A x * (fderiv ℝ phi x) (Pi.single i 1) *
        (fderiv ℝ psi x) (Pi.single i 1)) := by
      exact (hAi i).continuous.mul
        ((hpsi.continuous_fderiv_apply (by simp)).comp
          (continuous_id.prodMk continuous_const))
    have hcomp : HasCompactSupport
        (fun x => A x * (fderiv ℝ phi x) (Pi.single i 1) *
          (fderiv ℝ psi x) (Pi.single i 1)) :=
      (hFi_compact i).mul_right
    exact (hcont.integrable_of_hasCompactSupport hcomp).restrict
  have hL_int (i : Fin d) : Integrable
      (fun x => (rho x)⁻¹ *
        (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
          (Pi.single i 1) * psi x)
      ((cutoffSpeedMeasure M H omega N).restrict Q) := by
    rw [show cutoffSpeedMeasure M H omega N =
        volume.withDensity (fun x => ENNReal.ofReal (rho x)) by rfl]
    rw [restrict_withDensity (centeredCube z r hr).isOpen.measurableSet]
    rw [integrable_withDensity_iff_integrable_smul' hρmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have hDcont : Continuous (fun x =>
        (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
          (Pi.single i 1)) := by
      exact ((hAi i).continuous_fderiv_apply (by simp)).comp
        (continuous_id.prodMk continuous_const)
    have hDint : Integrable
        (fun x =>
          (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
            (Pi.single i 1) * psi x)
        (volume.restrict Q) := by
      have hglobalD : Integrable
          (fun x =>
            (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
              (Pi.single i 1) * psi x)
          (volume : Measure (SpatialCoordinates d)) :=
        (hDcont.mul hpsi.continuous).integrable_of_hasCompactSupport
          ((hFi_compact i).fderiv_apply ℝ (Pi.single i 1)).mul_right
      exact hglobalD.restrict
    apply (integrable_congr ?_).2 hDint
    filter_upwards [] with x
    rw [ENNReal.toReal_ofReal (hρpos x).le]
    dsimp only [smul_eq_mul]
    field_simp [ne_of_gt (hρpos x)]
  have hLsum :
      (∫ x in Q, (rho x)⁻¹ *
        (∑ i : Fin d,
          (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
            (Pi.single i 1)) * psi x
        ∂(cutoffSpeedMeasure M H omega N)) =
      ∑ i : Fin d, ∫ x in Q, (rho x)⁻¹ *
        (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
          (Pi.single i 1) * psi x
        ∂(cutoffSpeedMeasure M H omega N) := by
    have hsum := integral_finset_sum (μ :=
        (cutoffSpeedMeasure M H omega N).restrict Q)
      (Finset.univ : Finset (Fin d)) (fun i _ => hL_int i)
    rw [← hsum]
    apply integral_congr_ae
    filter_upwards [] with x
    calc
      ((rho x)⁻¹ * ∑ i : Fin d,
          (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
            (Pi.single i 1)) * psi x =
          (∑ i : Fin d, (rho x)⁻¹ *
            (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
              (Pi.single i 1)) * psi x := by rw [Finset.mul_sum]
      _ = ∑ i : Fin d, (rho x)⁻¹ *
          (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
            (Pi.single i 1) * psi x := by rw [Finset.sum_mul]
  have hRHSsum :
      (∫ x in Q, A x * ∑ i : Fin d,
          (fderiv ℝ phi x) (Pi.single i 1) *
            (fderiv ℝ psi x) (Pi.single i 1)) =
      ∑ i : Fin d, ∫ x in Q, A x *
        (fderiv ℝ phi x) (Pi.single i 1) *
          (fderiv ℝ psi x) (Pi.single i 1) := by
    have hsum := integral_finset_sum (μ := (volume.restrict Q))
      (Finset.univ : Finset (Fin d)) (fun i _ => hRHS_int i)
    rw [← hsum]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  calc
    -(∫ x in Q, (rho x)⁻¹ *
        (∑ i : Fin d,
          (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
            (Pi.single i 1)) * psi x
        ∂(cutoffSpeedMeasure M H omega N)) =
      -(∑ i : Fin d, ∫ x in Q, (rho x)⁻¹ *
        (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
          (Pi.single i 1) * psi x
        ∂(cutoffSpeedMeasure M H omega N)) := by rw [hLsum]
    _ = ∑ i : Fin d, (-(∫ x in Q, (rho x)⁻¹ *
        (fderiv ℝ (fun y => A y * (fderiv ℝ phi y) (Pi.single i 1)) x)
          (Pi.single i 1) * psi x
        ∂(cutoffSpeedMeasure M H omega N))) := by
      rw [Finset.sum_neg_distrib]
    _ = ∑ i : Fin d, ∫ x in Q, A x *
        (fderiv ℝ phi x) (Pi.single i 1) *
          (fderiv ℝ psi x) (Pi.single i 1) := by
      exact Finset.sum_congr rfl (fun i _ => hcoord i)
    _ = ∫ x in Q, A x * ∑ i : Fin d,
        (fderiv ℝ phi x) (Pi.single i 1) *
      (fderiv ℝ psi x) (Pi.single i 1) := hRHSsum.symm


/-- The generator of a test function is continuous. -/
theorem aux_fsrkb_gen_continuous (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hC1 : ContDiff ℝ 1 (cutoffCoefficient M H omega N))
    (phi : 𝓓(centeredCube z r hr, ℝ)) :
    Continuous (aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi) := by
  unfold aux_fsrkb_gen
  have hρc : Continuous (cutoffSpeedDensity M H omega N) := by
    have hpot : Continuous (cutoffPotential H omega N) := by
      unfold cutoffPotential
      fun_prop
    unfold cutoffSpeedDensity
    exact Real.continuous_exp.comp (hpot.sub continuous_const)
  have hρne : ∀ x, cutoffSpeedDensity M H omega N x ≠ 0 := fun x => (Real.exp_pos _).ne'
  refine (hρc.inv₀ hρne).mul (continuous_finset_sum _ fun i _ => ?_)
  have hphid : ContDiff ℝ 1 (fun x => (fderiv ℝ (phi : SpatialCoordinates d → ℝ) x) (Pi.single i 1)) := by
    have hp : ContDiff ℝ 1
        (fun p : (SpatialCoordinates d) × (SpatialCoordinates d) =>
          (fderiv ℝ (phi : SpatialCoordinates d → ℝ) p.1) p.2) :=
      phi.contDiff.contDiff_fderiv_apply (by norm_cast)
    have hc : ContDiff ℝ 1
        (fun x : SpatialCoordinates d =>
          (x, (Pi.single i (1 : ℝ) : SpatialCoordinates d))) := by fun_prop
    simpa only [Function.comp_apply] using hp.comp hc
  have hAi : ContDiff ℝ 1 (fun y => cutoffCoefficient M H omega N y *
      (fderiv ℝ (phi : SpatialCoordinates d → ℝ) y) (Pi.single i 1)) := hC1.mul hphid
  exact (hAi.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)

/-- The generator of a test function vanishes off the support of the test. -/
theorem aux_fsrkb_gen_eq_zero (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (phi : 𝓓(centeredCube z r hr, ℝ)) (x : SpatialCoordinates d) (hx : x ∉ tsupport phi) :
    aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi x = 0 := by
  have hnhds : (tsupport (phi : SpatialCoordinates d → ℝ))ᶜ ∈ 𝓝 x :=
    (isClosed_tsupport _).isOpen_compl.mem_nhds hx
  have hevd : ∀ᶠ y in 𝓝 x, fderiv ℝ (phi : SpatialCoordinates d → ℝ) y = 0 := by
    filter_upwards [hnhds] with y hy
    exact fderiv_of_notMem_tsupport ℝ hy
  have hterm : ∀ i : Fin d,
      (fderiv ℝ (fun y => cutoffCoefficient M H omega N y *
        (fderiv ℝ (phi : SpatialCoordinates d → ℝ) y) (Pi.single i 1)) x) (Pi.single i 1) = 0 := by
    intro i
    have hfun : (fun y => cutoffCoefficient M H omega N y *
        (fderiv ℝ (phi : SpatialCoordinates d → ℝ) y) (Pi.single i 1)) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hevd] with y hy
      simp [hy]
    rw [hfun.fderiv_eq]
    simp
  unfold aux_fsrkb_gen
  simp [hterm]


/-- The smooth–smooth identity, read on smooth Sobolev data. -/
theorem aux_fsrkb_ibp_smoothData (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hC1 : ContDiff ℝ 1 (cutoffCoefficient M H omega N))
    (phi psi : 𝓓(centeredCube z r hr, ℝ))
    (hcoef : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (Lane4.cutoffPositiveCoefficient M H omega N z hr).val x = cutoffCoefficient M H omega N x)
    (rhs : ℝ)
    (hrhs : rhs = -∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), aux_fsrkb_gen (cutoffCoefficient M H omega N)
          (cutoffSpeedDensity M H omega N) phi x *
            (smoothSobolevData psi).1 x ∂(cutoffSpeedMeasure M H omega N)) :
    sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr)
        (smoothSobolevData phi) (smoothSobolevData psi) = rhs := by
  classical
  have hQm : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) := (centeredCube z r hr).isOpen.measurableSet
  have hρ := (killed_generator_normalization M H omega N z r hr).1
  have hsupp : ∀ chi : 𝓓(centeredCube z r hr, ℝ),
      Function.support (chi : SpatialCoordinates d → ℝ) ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    fun chi => (subset_tsupport _).trans chi.tsupport_subset
  have hibp := aux_fsrkb_ibp_smooth M H omega N z r hr hC1 hρ phi psi phi.contDiff psi.contDiff
    phi.hasCompactSupport psi.hasCompactSupport (hsupp phi) (hsupp psi)
  -- the left side as a coordinate integral
  have hint : ∀ i : Fin d, Integrable (fun x => cutoffCoefficient M H omega N x *
      ((fderiv ℝ (phi : SpatialCoordinates d → ℝ) x) (Pi.single i 1) *
        (fderiv ℝ (psi : SpatialCoordinates d → ℝ) x) (Pi.single i 1))) (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    intro i
    have hA : Continuous (cutoffCoefficient M H omega N) := hC1.continuous
    have hdphi : Continuous (fun x => (fderiv ℝ (phi : SpatialCoordinates d → ℝ) x) (Pi.single i 1)) :=
      (phi.contDiff.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
    have hdpsi : Continuous (fun x => (fderiv ℝ (psi : SpatialCoordinates d → ℝ) x) (Pi.single i 1)) :=
      (psi.contDiff.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
    have hcs : HasCompactSupport (fun x => cutoffCoefficient M H omega N x *
        ((fderiv ℝ (phi : SpatialCoordinates d → ℝ) x) (Pi.single i 1) *
          (fderiv ℝ (psi : SpatialCoordinates d → ℝ) x) (Pi.single i 1))) :=
      ((phi.hasCompactSupport.fderiv_apply ℝ (Pi.single i 1)).mul_right).mul_left
    exact ((hA.mul (hdphi.mul hdpsi)).integrable_of_hasCompactSupport hcs).restrict
  have hleft : sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr)
      (smoothSobolevData phi) (smoothSobolevData psi) =
      ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), cutoffCoefficient M H omega N x * ∑ i : Fin d,
        (fderiv ℝ (phi : SpatialCoordinates d → ℝ) x) (Pi.single i 1) *
          (fderiv ℝ (psi : SpatialCoordinates d → ℝ) x) (Pi.single i 1) := by
    rw [sobolevCoefficientForm_apply]
    have hcoord : ∀ i : Fin d,
        (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), (Lane4.cutoffPositiveCoefficient M H omega N z hr).val x *
          ((smoothSobolevData phi).2 i x * (smoothSobolevData psi).2 i x)) =
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), cutoffCoefficient M H omega N x *
          ((fderiv ℝ (phi : SpatialCoordinates d → ℝ) x) (Pi.single i 1) *
            (fderiv ℝ (psi : SpatialCoordinates d → ℝ) x) (Pi.single i 1)) := by
      intro i
      refine integral_congr_ae ?_
      filter_upwards [hcoef, testPartialL2_coeFn phi i, testPartialL2_coeFn psi i]
        with x hx hphix hpsix
      change (Lane4.cutoffPositiveCoefficient M H omega N z hr).val x *
          ((testPartialL2 phi i) x * (testPartialL2 psi i) x) = _
      rw [hx, hphix, hpsix]
    rw [Finset.sum_congr rfl (fun i _ => hcoord i), ← integral_finset_sum _ (fun i _ => hint i)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Finset.mul_sum]
  -- the right side with the actual test function
  have hac : (cutoffSpeedMeasure M H omega N).restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ≪ volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (withDensity_absolutelyContinuous _ _).restrict _
  have hright : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), aux_fsrkb_gen (cutoffCoefficient M H omega N)
        (cutoffSpeedDensity M H omega N) phi x * (smoothSobolevData psi).1 x
          ∂(cutoffSpeedMeasure M H omega N)) =
      ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), ((cutoffSpeedDensity M H omega N x)⁻¹ *
        ∑ i : Fin d, (fderiv ℝ (fun y => cutoffCoefficient M H omega N y *
          (fderiv ℝ (phi : SpatialCoordinates d → ℝ) y) (Pi.single i 1)) x) (Pi.single i 1)) *
            psi x ∂(cutoffSpeedMeasure M H omega N) := by
    refine integral_congr_ae ?_
    filter_upwards [hac.ae_le (testL2_coeFn psi)] with x hx
    change aux_fsrkb_gen _ _ phi x * (testL2 psi) x = _
    rw [hx]
    rfl
  rw [hrhs, hright, hibp, hleft]

/-- **Integration by parts.** -/
theorem aux_fsrkb_ibp (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hC1 : ContDiff ℝ 1 (cutoffCoefficient M H omega N))
    (phi : 𝓓(centeredCube z r hr, ℝ)) (v : killedSobolevGraph (centeredCube z r hr)) :
    sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr)
        (smoothSobolevData phi) (v : SobolevData (centeredCube z r hr)) =
      -∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi x *
          ((v : SobolevData (centeredCube z r hr)).1) x ∂(cutoffSpeedMeasure M H omega N) := by
  classical
  have hQm : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) := (centeredCube z r hr).isOpen.measurableSet
  have hGc := aux_fsrkb_gen_continuous M H omega N z r hr hC1 phi
  have hGz := aux_fsrkb_gen_eq_zero M H omega N z r hr phi
  have hGcs : HasCompactSupport
      (aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi) :=
    HasCompactSupport.intro phi.hasCompactSupport hGz
  have hρc : Continuous (cutoffSpeedDensity M H omega N) := by
    have hpot : Continuous (cutoffPotential H omega N) := by
      unfold cutoffPotential
      fun_prop
    unfold cutoffSpeedDensity
    exact Real.continuous_exp.comp (hpot.sub continuous_const)
  have hρpos : ∀ x, 0 < cutoffSpeedDensity M H omega N x := fun x => Real.exp_pos _
  have hρmeas : Measurable (fun x => ENNReal.ofReal (cutoffSpeedDensity M H omega N x)) :=
    hρc.measurable.ennreal_ofReal
  let h : SpatialCoordinates d → ℝ := fun x => cutoffSpeedDensity M H omega N x *
    aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi x
  have hhc : Continuous h := hρc.mul hGc
  have hhcs : HasCompactSupport h := hGcs.mul_left
  have hmem : MemLp h 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    (hhc.memLp_of_hasCompactSupport hhcs).restrict _
  let hL : DomainL2 (centeredCube z r hr) := hmem.toLp h
  let Λ₂ : SobolevData (centeredCube z r hr) →L[ℝ] ℝ :=
    -((innerSL ℝ hL).comp (ContinuousLinearMap.fst ℝ (DomainL2 (centeredCube z r hr))
      (Fin d → DomainL2 (centeredCube z r hr))))
  let Λ₁ : SobolevData (centeredCube z r hr) →L[ℝ] ℝ :=
    sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr)
      (smoothSobolevData phi)
  -- integrals against the speed measure are Lebesgue integrals with the density
  have hdens : ∀ F : SpatialCoordinates d → ℝ,
      (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), F x ∂(cutoffSpeedMeasure M H omega N)) =
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), cutoffSpeedDensity M H omega N x * F x := by
    intro F
    have h1 := setIntegral_withDensity_eq_setIntegral_toReal_smul
      (μ := (volume : Measure (SpatialCoordinates d)))
      (f := fun x => ENNReal.ofReal (cutoffSpeedDensity M H omega N x))
      hρmeas (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) F hQm
    rw [show cutoffSpeedMeasure M H omega N =
        volume.withDensity (fun x => ENNReal.ofReal (cutoffSpeedDensity M H omega N x)) by rfl]
    rw [h1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (hρpos x).le]
  have hΛ₂ : ∀ w : SobolevData (centeredCube z r hr), Λ₂ w =
      -∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), aux_fsrkb_gen (cutoffCoefficient M H omega N)
          (cutoffSpeedDensity M H omega N) phi x * w.1 x ∂(cutoffSpeedMeasure M H omega N) := by
    intro w
    change -(inner ℝ hL w.1) = _
    rw [L2.inner_def, hdens]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hmem.coeFn_toLp] with x hx
    rw [hx]
    simp only [h, RCLike.inner_apply, conj_trivial]
    ring
  -- the coefficient class equals the coefficient a.e. on the cube
  have hcoef : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (Lane4.cutoffPositiveCoefficient M H omega N z hr).val x = cutoffCoefficient M H omega N x := by
    letI : Fact (((centeredCube z r hr : Set (SpatialCoordinates d))) ⊆ closedCube z r hr) := ⟨centeredCube_subset_closedCube z hr⟩
    filter_upwards [
      normalizedContinuousPositiveCoefficient_coeFn
        (Ω := centeredCube z r hr) (K := closedCube z r hr)
        (Lane4.cutoffCoefficientCM M H omega N z hr)
        (Lane4.cutoffCoefficientCM_pos M H omega N z hr) 1 one_pos,
      ae_restrict_mem hQm] with x hx hΩ
    have hx' := hx hΩ
    simpa [Lane4.cutoffCoefficientCM] using hx'
  have hsmooth : ∀ psi : 𝓓(centeredCube z r hr, ℝ),
      Λ₁ (smoothSobolevData psi) = Λ₂ (smoothSobolevData psi) := by
    intro psi
    exact aux_fsrkb_ibp_smoothData M H omega N z r hr hC1 phi psi hcoef _ (hΛ₂ _)
  have hker : killedSobolevGraph (centeredCube z r hr) ≤
      LinearMap.ker ((Λ₁ - Λ₂ : SobolevData (centeredCube z r hr) →L[ℝ] ℝ) :
        SobolevData (centeredCube z r hr) →ₗ[ℝ] ℝ) := by
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨psi, rfl⟩
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_sub', Pi.sub_apply,
        ContinuousLinearMap.coe_coe]
      change Λ₁ (smoothSobolevData psi) - Λ₂ (smoothSobolevData psi) = 0
      rw [hsmooth psi, sub_self]
    · exact ContinuousLinearMap.isClosed_ker (Λ₁ - Λ₂)
  have hv := hker v.2
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_sub', Pi.sub_apply,
    ContinuousLinearMap.coe_coe] at hv
  have hv' : Λ₁ (v : SobolevData (centeredCube z r hr)) = Λ₂ v := sub_eq_zero.mp hv
  rw [← hΛ₂]
  exact hv'

end KbIBP

section KbMollify

open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology Distributions Convolution

/-- Squared set integrals against a bounded density are controlled by a global `L²` bound. -/
theorem aux_fsrkb_moll_sq_tendsto {d : ℕ} (rho : SpatialCoordinates d → ℝ)
    (hrho : Measurable rho) (U : Set (SpatialCoordinates d)) (hU : MeasurableSet U) (P : ℝ)
    (hP : ∀ x ∈ U, rho x ≤ P) (R S : ℕ → SpatialCoordinates d → ℝ)
    (hRS : ∀ᶠ n in atTop, ∀ x ∈ U, |R n x| ≤ S n x)
    (hS : Tendsto (fun n => eLpNorm (S n) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in U, (R n x) ^ 2
      ∂(volume.withDensity (ENNReal.ofReal ∘ rho))) atTop (𝓝 0) := by
  have hup : Tendsto (fun n => ENNReal.ofReal P * (eLpNorm (S n) 2 volume) ^ 2) atTop
      (𝓝 0) := by
    have h2 : Tendsto (fun n => (eLpNorm (S n) 2 volume) ^ 2) atTop (𝓝 0) := by
      have h := ((ENNReal.continuous_pow 2).tendsto 0).comp hS
      simpa [Function.comp_def] using h
    simpa using ENNReal.Tendsto.const_mul h2 (Or.inr ENNReal.ofReal_ne_top)
  have hlin : Tendsto (fun n => ∫⁻ x in U, ENNReal.ofReal ‖(R n x) ^ 2‖
      ∂(volume.withDensity (ENNReal.ofReal ∘ rho))) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall fun n => zero_le _) ?_
    filter_upwards [hRS] with n hn
    calc ∫⁻ x in U, ENNReal.ofReal ‖(R n x) ^ 2‖ ∂(volume.withDensity (ENNReal.ofReal ∘ rho))
        = ∫⁻ x, ENNReal.ofReal ‖(R n x) ^ 2‖
            ∂((volume.restrict U).withDensity (ENNReal.ofReal ∘ rho)) := by
          rw [restrict_withDensity hU]
      _ ≤ ∫⁻ x, ((ENNReal.ofReal ∘ rho) * fun x => ENNReal.ofReal ‖(R n x) ^ 2‖) x
            ∂(volume.restrict U) :=
          lintegral_withDensity_le_lintegral_mul _ (ENNReal.measurable_ofReal.comp hrho) _
      _ ≤ ∫⁻ x in U, ENNReal.ofReal P * ENNReal.ofReal ((S n x) ^ 2) := by
          refine setLIntegral_mono' hU fun x hx => ?_
          simp only [Pi.mul_apply, Function.comp_apply]
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal (hP x hx)) (ENNReal.ofReal_le_ofReal ?_)
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          have h1 := hn x hx
          calc (R n x) ^ 2 = |R n x| ^ 2 := (sq_abs _).symm
            _ ≤ (S n x) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ ≤ ∫⁻ x, ENNReal.ofReal P * ENNReal.ofReal ((S n x) ^ 2) := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal P * (eLpNorm (S n) 2 volume) ^ 2 := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            SubdiffusiveProcess.Probability.Diffusion.Packet452Route.lintegral_ofReal_sq_eq_eLpNorm_sq]
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlin
  rw [ENNReal.toReal_zero] at hreal
  exact squeeze_zero_norm (fun n => norm_integral_le_lintegral_norm _) hreal

theorem aux_fsrkb_moll_eLpNorm_add {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g : ℕ → α → ℝ) (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg : ∀ n, AEStronglyMeasurable (g n) μ)
    (hf0 : Tendsto (fun n => eLpNorm (f n) 2 μ) atTop (𝓝 0))
    (hg0 : Tendsto (fun n => eLpNorm (g n) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => f n x + g n x) 2 μ) atTop (𝓝 0) := by
  have h := hf0.add hg0
  rw [add_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n => zero_le _)
    (fun n => eLpNorm_add_le (hf n) (hg n) (by norm_num))

theorem aux_fsrkb_moll_eLpNorm_sum {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ι : Type*} (s : Finset ι) (f : ι → ℕ → α → ℝ)
    (hf : ∀ i n, AEStronglyMeasurable (f i n) μ)
    (hf0 : ∀ i, Tendsto (fun n => eLpNorm (f i n) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => ∑ i ∈ s, f i n x) 2 μ) atTop (𝓝 0) := by
  have h : Tendsto (fun n => ∑ i ∈ s, eLpNorm (f i n) 2 μ) atTop (𝓝 0) := by
    have h' := tendsto_finset_sum s (fun i _ => hf0 i)
    simpa using h'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n => zero_le _)
    (fun n => ?_)
  have hle := eLpNorm_sum_le (s := s) (f := fun i => f i n) (fun i _ => hf i n)
    (p := 2) (μ := μ) (by norm_num)
  have heq : (∑ i ∈ s, f i n) = fun x => ∑ i ∈ s, f i n x := by
    funext x
    simp [Finset.sum_apply]
  rw [heq] at hle
  exact hle

theorem aux_fsrkb_moll_eLpNorm_const_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (c : ℝ) (f : ℕ → α → ℝ) (hf0 : Tendsto (fun n => eLpNorm (f n) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => c * f n x) 2 μ) atTop (𝓝 0) := by
  have h := ENNReal.Tendsto.const_mul hf0 (Or.inr (enorm_ne_top (x := c)))
  rw [mul_zero] at h
  refine h.congr fun n => ?_
  rw [← eLpNorm_const_smul]
  rfl

theorem aux_fsrkb_moll_eLpNorm_abs {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ℝ) : eLpNorm (fun x => |f x|) 2 μ = eLpNorm f 2 μ := by
  simpa [Real.norm_eq_abs] using eLpNorm_norm (p := 2) (μ := μ) f

theorem aux_fsrkb_moll_A_pos {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ) :
    ∀ x, 0 < cutoffCoefficient M H omega N x := fun _ =>
  mul_pos (inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)

theorem aux_fsrkb_moll_coeff_ae {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (Lane4.cutoffPositiveCoefficient M H omega N z hr).val x =
        cutoffCoefficient M H omega N x := by
  have h1 := @normalizedContinuousPositiveCoefficient_coeFn d (centeredCube z r hr)
    (closedCube z r hr) ⟨centeredCube_subset_closedCube z hr⟩
    (Lane4.cutoffCoefficientCM M H omega N z hr)
    (Lane4.cutoffCoefficientCM_pos M H omega N z hr) 1 one_pos
  filter_upwards [h1, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx hxm
  unfold Lane4.cutoffPositiveCoefficient
  rw [hx hxm, div_one]
  rfl

/-- The right side of the weak equation, for a test `ψ / A`. -/
theorem aux_fsrkb_moll_weak_rhs {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (lam : ℝ)
    (f g u1 v1 psi : SpatialCoordinates d → ℝ)
    (hg : ∀ y, u1 y = g y)
    (hv1 : v1 =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun y => psi y / cutoffCoefficient M H omega N y) :
    ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        (f y - lam * u1 y) * v1 y ∂(cutoffSpeedMeasure M H omega N) =
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
        ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), (f y - lam * g y) * psi y := by
  have hrho := (killed_generator_normalization M H omega N z r hr).1
  have hApos := aux_fsrkb_moll_A_pos M H omega N
  have hrhomeas : Measurable fun x => ENNReal.ofReal (cutoffSpeedDensity M H omega N x) := by
    refine ENNReal.measurable_ofReal.comp ?_
    have hc : Continuous (cutoffSpeedDensity M H omega N) := by
      have he : cutoffSpeedDensity M H omega N =
          fun x => SubdiffusiveProcess.CoarseGrainingVocab.ahom M N * cutoffCoefficient M H omega N x :=
        funext hrho
      rw [he]
      refine continuous_const.mul ?_
      refine continuous_const.mul (Real.continuous_exp.comp ?_)
      exact Continuous.sub
        (Continuous.add (H omega).continuous
          (continuous_finset_sum _ fun j _ => (omega (-(Int.ofNat j))).continuous))
        continuous_const
    exact hc.measurable
  have hdens := setIntegral_withDensity_eq_setIntegral_toReal_smul
    (μ := (volume : Measure (SpatialCoordinates d)))
    (f := fun x => ENNReal.ofReal (cutoffSpeedDensity M H omega N x))
    hrhomeas (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
    (fun y => (f y - lam * u1 y) * v1 y) (centeredCube z r hr).isOpen.measurableSet
  have hdens' : ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        (f y - lam * u1 y) * v1 y ∂(cutoffSpeedMeasure M H omega N) =
      ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        cutoffSpeedDensity M H omega N y * ((f y - lam * u1 y) * v1 y) := by
    rw [show cutoffSpeedMeasure M H omega N =
        volume.withDensity (fun x => ENNReal.ofReal (cutoffSpeedDensity M H omega N x)) by rfl]
    rw [hdens]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal (show (0 : ℝ) ≤ cutoffSpeedDensity M H omega N y from
      (Real.exp_pos _).le)]
  rw [hdens', ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hv1] with y hy
  rw [hy, hrho y, hg y]
  have hA := (hApos y).ne'
  field_simp

/-- The weak equation tested with `ψ / A`, for a smooth `ψ` compactly supported in the cube. -/
theorem aux_fsrkb_moll_weak_test {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hC1 : ContDiff ℝ 1 (cutoffCoefficient M H omega N))
    (lam : ℝ) (f : SpatialCoordinates d → ℝ)
    (u : killedSobolevGraph (centeredCube z r hr))
    (hu : aux_fsrkb_WeakEq M H omega N z r hr lam f u)
    (v : Homogenization.H10Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hv1 : (v : SpatialCoordinates d → ℝ) =
      fun x => ((u : SobolevData (centeredCube z r hr)).1) x)
    (hv2 : v.toH1Function.grad = fun x i => ((u : SobolevData (centeredCube z r hr)).2 i) x)
    (psi : SpatialCoordinates d → ℝ) (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi)
    (hpsic : HasCompactSupport psi)
    (hpsiQ : tsupport psi ⊆ (centeredCube z r hr : Set (SpatialCoordinates d))) :
    ∑ i : Fin d, ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        v.toH1Function.grad y i * (fderiv ℝ psi y (Homogenization.basisVec i) -
          psi y * fderiv ℝ (fun w => Real.log (cutoffCoefficient M H omega N w)) y
            (Homogenization.basisVec i)) =
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
        ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
          (f y - lam * v y) * psi y := by
  have hApos := aux_fsrkb_moll_A_pos M H omega N
  have h10 := SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Density.exists_h10_div_of_contDiffOn
    (U := (centeredCube z r hr : Set (SpatialCoordinates d))) (V := Set.univ)
    (centeredCube z r hr).isOpen isOpen_univ hC1.contDiffOn (fun x _ => hApos x) hpsi hpsic
    hpsiQ (Set.subset_univ _)
  rcases h10 with ⟨w, hw1, hw2⟩
  have hk := Lane4.exists_killedSobolevGraph_of_nativeH10 w
  rcases hk with ⟨vx, hvx1, hvx2⟩
  have heq := hu vx
  rw [sobolevCoefficientForm_apply] at heq
  have hL : ∀ i : Fin d,
      ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        (Lane4.cutoffPositiveCoefficient M H omega N z hr).val y *
          (((u : SobolevData (centeredCube z r hr)).2 i) y *
            ((vx : SobolevData (centeredCube z r hr)).2 i) y) =
      ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        v.toH1Function.grad y i * (fderiv ℝ psi y (Homogenization.basisVec i) -
          psi y * fderiv ℝ (fun w => Real.log (cutoffCoefficient M H omega N w)) y
            (Homogenization.basisVec i)) := by
    intro i
    refine integral_congr_ae ?_
    filter_upwards [aux_fsrkb_moll_coeff_ae M H omega N z hr, hvx2 i] with y hay hy
    rw [hay, hy, hw2, hv2]
    have hc := SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Density.coeff_mul_fderiv_div
      isOpen_univ hC1.contDiffOn (fun x _ => hApos x) hpsi (Set.subset_univ _)
      (Set.mem_univ y) i
    rw [← hc]
    ring
  rw [Finset.sum_congr rfl fun i _ => hL i] at heq
  rw [heq]
  refine aux_fsrkb_moll_weak_rhs M H omega N z r hr lam f v _ _ psi ?_ ?_
  · intro y
    rw [hv1]
  · rw [← hw1]
    exact hvx1

open SubdiffusiveProcess.Probability.Diffusion.Packet452Route in
theorem aux_fsrkb_moll_conv_apply {d : ℕ} (g k : SpatialCoordinates d → ℝ)
    (x : SpatialCoordinates d) :
    (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] k) x = ∫ y, g y * k (x - y) := by
  simp only [convolution_lsmul, smul_eq_mul]

open SubdiffusiveProcess.Probability.Diffusion.Packet452Route in
/-- Set integrals of `H¹₀` gradients are global integrals of the zero extension. -/
theorem aux_fsrkb_moll_setIntegral_grad {d : ℕ} {Ω : Set (SpatialCoordinates d)}
    (hΩ : IsOpen Ω) (v : Homogenization.H10Function Ω) (i : Fin d)
    (h : SpatialCoordinates d → ℝ) :
    ∫ y in Ω, v.toH1Function.grad y i * h y = ∫ y, v.zeroExtensionGrad y i * h y := by
  rw [← integral_indicator hΩ.measurableSet]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ Ω
  · simp only [Set.indicator_of_mem hy, v.zeroExtensionGrad_apply_of_mem hy]
  · simp only [Set.indicator_of_notMem hy, v.zeroExtensionGrad_apply_of_not_mem hy,
      Pi.zero_apply, zero_mul]

open SubdiffusiveProcess.Probability.Diffusion.Packet452Route in
/-- The gradient side of the tested weak equation is the mollified divergence form. -/
theorem aux_fsrkb_moll_conv_grad {d : ℕ} {Ω : Set (SpatialCoordinates d)} (hΩ : IsOpen Ω)
    (v : Homogenization.H10Function Ω) (b : SpatialCoordinates d → ℝ) (hb : Continuous b)
    (n : ℕ) (x : SpatialCoordinates d) (i : Fin d) :
    ∫ y in Ω, v.toH1Function.grad y i *
        (fderiv ℝ (fun y' => mollKernel d n (x - y')) y (Homogenization.basisVec i) -
          mollKernel d n (x - y) * b y) =
      -(fderiv ℝ (fun y' => fderiv ℝ (mollPhi v n) y' (Homogenization.basisVec i)) x
          (Homogenization.basisVec i)) -
        ((fun y => b y * v.zeroExtensionGrad y i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          mollKernel d n) x := by
  have hk := mollKernel_contDiff (d := d) n
  have hkc := mollKernel_hasCompactSupport (d := d) n
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun y' : SpatialCoordinates d => mollKernel d n (x - y')) :=
    contDiff_reflect hk x
  have hψc : HasCompactSupport (fun y' : SpatialCoordinates d => mollKernel d n (x - y')) :=
    hasCompactSupport_reflect _ hkc x
  have hG := memLp_zeroExtensionGrad_two hΩ v i
  have hdψ : MemLp (fun y => fderiv ℝ (fun y' => mollKernel d n (x - y')) y
      (Homogenization.basisVec i)) 2 volume :=
    ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hψc.fderiv_apply (𝕜 := ℝ) (Homogenization.basisVec i))
  have hψb : MemLp (fun y => mollKernel d n (x - y) * b y) 2 volume :=
    (hψ.continuous.mul hb).memLp_of_hasCompactSupport hψc.mul_right
  have hi1 : Integrable (fun y => v.zeroExtensionGrad y i *
      fderiv ℝ (fun y' => mollKernel d n (x - y')) y (Homogenization.basisVec i)) volume := by
    simpa only [Pi.mul_def] using hG.integrable_mul hdψ
  have hi2 : Integrable (fun y => v.zeroExtensionGrad y i *
      (mollKernel d n (x - y) * b y)) volume := by
    simpa only [Pi.mul_def] using hG.integrable_mul hψb
  rw [aux_fsrkb_moll_setIntegral_grad hΩ v i]
  simp only [mul_sub]
  rw [integral_sub hi1 hi2]
  have hfun : (fun y => fderiv ℝ (mollPhi v n) y (Homogenization.basisVec i)) =
      (fun y => v.zeroExtensionGrad y i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        mollKernel d n :=
    funext fun y => fderiv_mollPhi hΩ v n i y
  rw [hfun, fderiv_convolution_kernel (locallyIntegrable_zeroExtensionGrad hΩ v i) hk hkc
    (Homogenization.basisVec i) x, aux_fsrkb_moll_conv_apply, aux_fsrkb_moll_conv_apply,
    ← integral_neg]
  congr 1
  · refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [fderiv_reflect hk x y (Homogenization.basisVec i), mul_neg]
  · refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    ring

open SubdiffusiveProcess.Probability.Diffusion.Packet452Route in
/-- The source side of the tested weak equation is the mollified source. -/
theorem aux_fsrkb_moll_conv_rhs {d : ℕ} {Ω : Set (SpatialCoordinates d)} (hΩ : IsOpen Ω)
    (v : Homogenization.H10Function Ω) (f : SpatialCoordinates d → ℝ)
    (hf : aux_fsrkb_BddMeas f) (lam : ℝ) (n : ℕ) (x : SpatialCoordinates d) :
    ∫ y in Ω, (f y - lam * v y) * mollKernel d n (x - y) =
      (Ω.indicator f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] mollKernel d n) x -
        lam * mollPhi v n x := by
  rcases hf with ⟨hfm, B, _hB0, hB⟩
  have hk := mollKernel_contDiff (d := d) n
  have hkc := mollKernel_hasCompactSupport (d := d) n
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun y' : SpatialCoordinates d => mollKernel d n (x - y')) :=
    contDiff_reflect hk x
  have hψc : HasCompactSupport (fun y' : SpatialCoordinates d => mollKernel d n (x - y')) :=
    hasCompactSupport_reflect _ hkc x
  have hψi : Integrable (fun y : SpatialCoordinates d => mollKernel d n (x - y)) volume :=
    hψ.continuous.integrable_of_hasCompactSupport hψc
  have hψ2 : MemLp (fun y : SpatialCoordinates d => mollKernel d n (x - y)) 2 volume :=
    hψ.continuous.memLp_of_hasCompactSupport hψc
  have hi1 : Integrable (fun y => Ω.indicator f y * mollKernel d n (x - y)) volume := by
    refine hψi.bdd_mul (c := B) ((hfm.indicator hΩ.measurableSet).aestronglyMeasurable) ?_
    refine Eventually.of_forall fun y => ?_
    by_cases hy : y ∈ Ω
    · rw [Set.indicator_of_mem hy, Real.norm_eq_abs]
      exact hB y
    · rw [Set.indicator_of_notMem hy, norm_zero]
      exact _hB0
  have hi2 : Integrable (fun y => v.zeroExtension y * mollKernel d n (x - y)) volume := by
    simpa only [Pi.mul_def] using (memLp_zeroExtension_two hΩ v).integrable_mul hψ2
  have hsplit : ∫ y in Ω, (f y - lam * v y) * mollKernel d n (x - y) =
      ∫ y, (Ω.indicator f y * mollKernel d n (x - y) -
        lam * (v.zeroExtension y * mollKernel d n (x - y))) := by
    rw [← integral_indicator hΩ.measurableSet]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ Ω
    · simp only [Set.indicator_of_mem hy, v.zeroExtension_apply_of_mem hy]
      ring
    · simp only [Set.indicator_of_notMem hy, v.zeroExtension_apply_of_not_mem hy]
      ring
  rw [hsplit, integral_sub hi1 (hi2.const_mul lam), integral_const_mul, mollPhi,
    aux_fsrkb_moll_conv_apply, aux_fsrkb_moll_conv_apply]

/-- The weighted-divergence generator of a smooth function, near a point where it agrees with
a smooth `w`, in nondivergence form. -/
theorem aux_fsrkb_moll_gen_eq {d : ℕ} (A rho phi w : SpatialCoordinates d → ℝ) (ah : ℝ)
    (hah : 0 < ah) (hA : ContDiff ℝ 1 A) (hApos : ∀ x, 0 < A x)
    (hrho : ∀ x, rho x = ah * A x) (hw : ContDiff ℝ 2 w) (U : Set (SpatialCoordinates d))
    (hU : IsOpen U) (heq : ∀ y ∈ U, phi y = w y) (x : SpatialCoordinates d) (hx : x ∈ U) :
    aux_fsrkb_gen A rho phi x = ah⁻¹ * ∑ i : Fin d,
      (fderiv ℝ (fun y => fderiv ℝ w y (Homogenization.basisVec i)) x
          (Homogenization.basisVec i) +
        fderiv ℝ (fun y => Real.log (A y)) x (Homogenization.basisVec i) *
          fderiv ℝ w x (Homogenization.basisVec i)) := by
  have hbv : ∀ i : Fin d, (Pi.single i (1 : ℝ) : SpatialCoordinates d) =
      Homogenization.basisVec i := fun i => rfl
  simp only [aux_fsrkb_gen, hbv]
  have hev : ∀ i : Fin d, (fun y => A y * fderiv ℝ phi y (Homogenization.basisVec i)) =ᶠ[𝓝 x]
      (fun y => A y * fderiv ℝ w y (Homogenization.basisVec i)) := by
    intro i
    filter_upwards [hU.mem_nhds hx] with y hy
    have h1 : phi =ᶠ[𝓝 y] w := by
      filter_upwards [hU.mem_nhds hy] with t ht using heq t ht
    rw [h1.fderiv_eq]
  have hAx : A x ≠ 0 := (hApos x).ne'
  have hterm : ∀ i : Fin d,
      fderiv ℝ (fun y => A y * fderiv ℝ phi y (Homogenization.basisVec i)) x
          (Homogenization.basisVec i) =
        A x * (fderiv ℝ (fun y => fderiv ℝ w y (Homogenization.basisVec i)) x
            (Homogenization.basisVec i) +
          fderiv ℝ (fun y => Real.log (A y)) x (Homogenization.basisVec i) *
            fderiv ℝ w x (Homogenization.basisVec i)) := by
    intro i
    rw [(hev i).fderiv_eq]
    have hAd : DifferentiableAt ℝ A x := hA.differentiable le_rfl x
    have hDd : DifferentiableAt ℝ (fun y => fderiv ℝ w y (Homogenization.basisVec i)) x :=
      ((hw.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
        le_rfl x
    have hm : HasFDerivAt (fun y => A y * fderiv ℝ w y (Homogenization.basisVec i))
        (A x • fderiv ℝ (fun y => fderiv ℝ w y (Homogenization.basisVec i)) x +
          fderiv ℝ w x (Homogenization.basisVec i) • fderiv ℝ A x) x :=
      hAd.hasFDerivAt.mul hDd.hasFDerivAt
    rw [hm.fderiv]
    have hlog : HasFDerivAt (fun y => Real.log (A y)) ((A x)⁻¹ • fderiv ℝ A x) x :=
      hAd.hasFDerivAt.log hAx
    rw [hlog.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    field_simp
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum, hrho]
  field_simp

/-- The pointwise algebraic bound on the residual. -/
theorem aux_fsrkb_moll_abs_bound {d : ℕ} (R eF c : ℝ) (hc : 0 ≤ c)
    (eH eG b B : Fin d → ℝ) (hB : ∀ i, |b i| ≤ B i)
    (hR : R = eF + c * ∑ i : Fin d, (eH i - b i * eG i)) :
    |R| ≤ |eF| + c * ∑ i : Fin d, (|eH i| + B i * |eG i|) := by
  rw [hR]
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [abs_mul, abs_of_nonneg hc]
  refine mul_le_mul_of_nonneg_left ?_ hc
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hB i) (abs_nonneg _)

open SubdiffusiveProcess.Probability.Diffusion.Packet452Route in
/-- The mollification error of a function. -/
noncomputable def aux_fsrkb_moll_err {d : ℕ} (g : SpatialCoordinates d → ℝ) (n : ℕ)
    (x : SpatialCoordinates d) : ℝ :=
  (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] mollKernel d n) x - g x

open SubdiffusiveProcess.Probability.Diffusion.Packet452Route in
theorem aux_fsrkb_moll_err_aesm {d : ℕ} {g : SpatialCoordinates d → ℝ}
    (hg : MemLp g 2 volume) (n : ℕ) :
    AEStronglyMeasurable (aux_fsrkb_moll_err g n) volume :=
  (contDiff_convolution_kernel (hg.locallyIntegrable (by norm_num)) (mollKernel_contDiff n)
    (mollKernel_hasCompactSupport n)).continuous.aestronglyMeasurable.sub
      hg.aestronglyMeasurable

theorem aux_fsrkb_moll_err_tendsto {d : ℕ} {g : SpatialCoordinates d → ℝ}
    (hg : MemLp g 2 volume) :
    Tendsto (fun n => eLpNorm (aux_fsrkb_moll_err g n) 2 volume) atTop (𝓝 0) :=
  SubdiffusiveProcess.Probability.Diffusion.Packet452Route.tendsto_eLpNorm_moll hg

theorem aux_fsrkb_moll_abs_aesm {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => |f x|) μ :=
  continuous_abs.comp_aestronglyMeasurable hf

/-- The residual majorant tends to zero in `L²`. -/
theorem aux_fsrkb_moll_comb {α : Type*} [MeasurableSpace α] {μ : Measure α} {d : ℕ}
    (c : ℝ) (B : Fin d → ℝ) (eF : ℕ → α → ℝ) (eH eG : Fin d → ℕ → α → ℝ)
    (hF : ∀ n, AEStronglyMeasurable (eF n) μ) (hH : ∀ i n, AEStronglyMeasurable (eH i n) μ)
    (hG : ∀ i n, AEStronglyMeasurable (eG i n) μ)
    (hF0 : Tendsto (fun n => eLpNorm (eF n) 2 μ) atTop (𝓝 0))
    (hH0 : ∀ i, Tendsto (fun n => eLpNorm (eH i n) 2 μ) atTop (𝓝 0))
    (hG0 : ∀ i, Tendsto (fun n => eLpNorm (eG i n) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => |eF n x| +
      c * ∑ i : Fin d, (|eH i n x| + B i * |eG i n x|)) 2 μ) atTop (𝓝 0) := by
  have hFa : ∀ n, AEStronglyMeasurable (fun x => |eF n x|) μ := fun n =>
    aux_fsrkb_moll_abs_aesm (hF n)
  have hHa : ∀ i n, AEStronglyMeasurable (fun x => |eH i n x|) μ := fun i n =>
    aux_fsrkb_moll_abs_aesm (hH i n)
  have hGa : ∀ i n, AEStronglyMeasurable (fun x => B i * |eG i n x|) μ := fun i n =>
    (aux_fsrkb_moll_abs_aesm (hG i n)).const_mul (B i)
  have hterm : ∀ i n, AEStronglyMeasurable (fun x => |eH i n x| + B i * |eG i n x|) μ :=
    fun i n => (hHa i n).add (hGa i n)
  have hsum : ∀ n, AEStronglyMeasurable
      (fun x => ∑ i : Fin d, (|eH i n x| + B i * |eG i n x|)) μ := by
    intro n
    have h := Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin d))
      (fun i _ => hterm i n)
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp [Finset.sum_apply]
  have hFt : Tendsto (fun n => eLpNorm (fun x => |eF n x|) 2 μ) atTop (𝓝 0) :=
    hF0.congr fun n => (aux_fsrkb_moll_eLpNorm_abs (eF n)).symm
  have hHt : ∀ i, Tendsto (fun n => eLpNorm (fun x => |eH i n x|) 2 μ) atTop (𝓝 0) :=
    fun i => (hH0 i).congr fun n => (aux_fsrkb_moll_eLpNorm_abs (eH i n)).symm
  have hGt : ∀ i, Tendsto (fun n => eLpNorm (fun x => B i * |eG i n x|) 2 μ) atTop (𝓝 0) :=
    fun i => aux_fsrkb_moll_eLpNorm_const_mul (B i) (fun n x => |eG i n x|)
      ((hG0 i).congr fun n => (aux_fsrkb_moll_eLpNorm_abs (eG i n)).symm)
  have hTt : ∀ i, Tendsto (fun n => eLpNorm (fun x => |eH i n x| + B i * |eG i n x|) 2 μ)
      atTop (𝓝 0) := fun i =>
    aux_fsrkb_moll_eLpNorm_add (fun n x => |eH i n x|) (fun n x => B i * |eG i n x|)
      (hHa i) (hGa i) (hHt i) (hGt i)
  have hSt := aux_fsrkb_moll_eLpNorm_sum (μ := μ) Finset.univ
    (fun i n x => |eH i n x| + B i * |eG i n x|) hterm hTt
  have hCt := aux_fsrkb_moll_eLpNorm_const_mul c
    (fun n x => ∑ i : Fin d, (|eH i n x| + B i * |eG i n x|)) hSt
  exact aux_fsrkb_moll_eLpNorm_add (fun n x => |eF n x|)
    (fun n x => c * ∑ i : Fin d, (|eH i n x| + B i * |eG i n x|)) hFa
    (fun n => (hsum n).const_mul c) hFt hCt

theorem aux_fsrkb_moll_alg {d : ℕ} (lam w f Fk ah : ℝ) (hah : ah ≠ 0)
    (Lap Hk Gk b G : Fin d → ℝ)
    (hweak : ∑ i : Fin d, (-Lap i - Hk i) = ah * (Fk - lam * w)) :
    lam * w - ah⁻¹ * ∑ i : Fin d, (Lap i + b i * Gk i) - f =
      (Fk - f) + ah⁻¹ * ∑ i : Fin d, ((Hk i - b i * G i) - b i * (Gk i - G i)) := by
  have hsum : ∑ i : Fin d, ((Hk i - b i * G i) - b i * (Gk i - G i)) =
      -(∑ i : Fin d, (-Lap i - Hk i)) - ∑ i : Fin d, (Lap i + b i * Gk i) := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsum, hweak]
  field_simp
  ring

theorem aux_fsrkb_moll_logderiv_continuous {d : ℕ} (A : SpatialCoordinates d → ℝ)
    (hA : ContDiff ℝ 1 A) (hApos : ∀ x, 0 < A x) (i : Fin d) :
    Continuous (fun y => fderiv ℝ (fun w => Real.log (A w)) y (Homogenization.basisVec i)) :=
  ((hA.log fun x => (hApos x).ne').continuous_fderiv le_rfl).clm_apply continuous_const

open SubdiffusiveProcess.Probability.Diffusion.Packet452Route in
/-- The residual of the cut-off mollification at an interior point, as mollification errors. -/
theorem aux_fsrkb_moll_residual_eq {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hC1 : ContDiff ℝ 1 (cutoffCoefficient M H omega N))
    (lam : ℝ) (f : SpatialCoordinates d → ℝ) (hf : aux_fsrkb_BddMeas f)
    (u : killedSobolevGraph (centeredCube z r hr))
    (hu : aux_fsrkb_WeakEq M H omega N z r hr lam f u)
    (v : Homogenization.H10Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hv1 : (v : SpatialCoordinates d → ℝ) =
      fun x => ((u : SobolevData (centeredCube z r hr)).1) x)
    (hv2 : v.toH1Function.grad = fun x i => ((u : SobolevData (centeredCube z r hr)).2 i) x)
    (chi : SpatialCoordinates d → ℝ) (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (hUQ : U ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hchi : ∀ y ∈ U, chi y = 1) (n : ℕ) (x : SpatialCoordinates d) (hx : x ∈ U)
    (hball : Metric.closedBall x (Homogenization.unitConvexApproxScale n) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d))) :
    lam * (chi x * mollPhi v n x) -
        aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N)
          (fun y => chi y * mollPhi v n y) x - f x =
      aux_fsrkb_moll_err ((centeredCube z r hr : Set (SpatialCoordinates d)).indicator f) n x +
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ * ∑ i : Fin d,
          (aux_fsrkb_moll_err (fun y => fderiv ℝ
              (fun w => Real.log (cutoffCoefficient M H omega N w)) y
                (Homogenization.basisVec i) * v.zeroExtensionGrad y i) n x -
            fderiv ℝ (fun w => Real.log (cutoffCoefficient M H omega N w)) x
                (Homogenization.basisVec i) *
              aux_fsrkb_moll_err (fun y => v.zeroExtensionGrad y i) n x) := by
  have hQo := (centeredCube z r hr).isOpen
  have hah := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  have hApos := aux_fsrkb_moll_A_pos M H omega N
  have hrho := (killed_generator_normalization M H omega N z r hr).1
  have hw2 : ContDiff ℝ 2 (mollPhi v n) :=
    (contDiff_mollPhi hQo v n).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hgen := aux_fsrkb_moll_gen_eq _ _ (fun y => chi y * mollPhi v n y) (mollPhi v n) _
    hah hC1 hApos hrho hw2 U hU (fun y hy => by simp only [hchi y hy, one_mul]) x hx
  have hk := mollKernel_contDiff (d := d) n
  have hkc := mollKernel_hasCompactSupport (d := d) n
  have hweak := aux_fsrkb_moll_weak_test M H omega N z r hr hC1 lam f u hu v hv1 hv2
    (fun y => mollKernel d n (x - y)) (contDiff_reflect hk x)
    (hasCompactSupport_reflect _ hkc x)
    ((tsupport_reflect_subset (tsupport_mollKernel n) x).trans hball)
  rw [Finset.sum_congr rfl fun i _ => aux_fsrkb_moll_conv_grad hQo v _
      (aux_fsrkb_moll_logderiv_continuous _ hC1 hApos i) n x i,
    aux_fsrkb_moll_conv_rhs hQo v f hf lam n x] at hweak
  rw [hgen]
  have hD : ∀ i : Fin d, fderiv ℝ (mollPhi v n) x (Homogenization.basisVec i) =
      ((fun y => v.zeroExtensionGrad y i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        mollKernel d n) x := fun i => fderiv_mollPhi hQo v n i x
  simp only [hD]
  have hxQ : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) := hUQ hx
  unfold aux_fsrkb_moll_err
  simp only [Set.indicator_of_mem hxQ, hchi x hx, one_mul]
  exact aux_fsrkb_moll_alg _ _ _ _ _ hah.ne' _ _ _ _ _ hweak

theorem aux_fsrkb_moll_rho_continuous {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ) :
    Continuous (cutoffSpeedDensity M H omega N) := by
  refine Real.continuous_exp.comp ?_
  exact Continuous.sub
    (Continuous.add (H omega).continuous
      (continuous_finset_sum _ fun j _ => (omega (-(Int.ofNat j))).continuous))
    continuous_const

theorem aux_fsrkb_moll_memLp_mul {d : ℕ} {Ω : Set (SpatialCoordinates d)}
    {g b : SpatialCoordinates d → ℝ} (hg : MemLp g 2 volume) (hb : Continuous b) (C : ℝ)
    (hC : ∀ y ∈ Ω, |b y| ≤ C) (hg0 : ∀ y, y ∉ Ω → g y = 0) :
    MemLp (fun y => b y * g y) 2 volume := by
  refine (hg.const_mul |C|).of_le (hb.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ Ω
  · simp only [Real.norm_eq_abs, abs_mul, abs_abs]
    exact mul_le_mul_of_nonneg_right ((hC y hy).trans (le_abs_self C)) (abs_nonneg _)
  · simp only [hg0 y hy, mul_zero, norm_zero, le_refl]

theorem aux_fsrkb_moll_memLp_indicator {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (f : SpatialCoordinates d → ℝ) (hf : aux_fsrkb_BddMeas f) :
    MemLp ((centeredCube z r hr : Set (SpatialCoordinates d)).indicator f) 2 volume := by
  rcases hf with ⟨hfm, B, _hB0, hB⟩
  refine (memLp_indicator_iff_restrict (centeredCube z r hr).isOpen.measurableSet).2 ?_
  exact MemLp.of_bound hfm.aestronglyMeasurable B
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)

open SubdiffusiveProcess.Probability.Diffusion.Packet452Route in
/-- The generator residual of the cut-off mollifications tends to zero in `L²(U, μ)`. -/
theorem aux_fsrkb_moll_resid_tendsto {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hC1 : ContDiff ℝ 1 (cutoffCoefficient M H omega N))
    (lam : ℝ) (f : SpatialCoordinates d → ℝ) (hf : aux_fsrkb_BddMeas f)
    (u : killedSobolevGraph (centeredCube z r hr))
    (hu : aux_fsrkb_WeakEq M H omega N z r hr lam f u)
    (v : Homogenization.H10Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hv1 : (v : SpatialCoordinates d → ℝ) =
      fun x => ((u : SobolevData (centeredCube z r hr)).1) x)
    (hv2 : v.toH1Function.grad = fun x i => ((u : SobolevData (centeredCube z r hr)).2 i) x)
    (chi : SpatialCoordinates d → ℝ) (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (hUQ : closure U ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hchi : ∀ y ∈ U, chi y = 1) :
    Tendsto (fun n => ∫ x in U, (lam * (chi x * mollPhi v n x) -
        aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N)
          (fun y => chi y * mollPhi v n y) x - f x) ^ 2 ∂(cutoffSpeedMeasure M H omega N))
      atTop (𝓝 0) := by
  have hQo := (centeredCube z r hr).isOpen
  have hah := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  have hApos := aux_fsrkb_moll_A_pos M H omega N
  have hUc : IsCompact (closure U) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure
      ((centeredCube_isBounded z hr).subset hUQ)
  have hb := fun i => aux_fsrkb_moll_logderiv_continuous _ hC1 hApos i
  have hBex : ∀ i : Fin d, ∃ C : ℝ, ∀ x ∈ closure U,
      ‖fderiv ℝ (fun w => Real.log (cutoffCoefficient M H omega N w)) x
        (Homogenization.basisVec i)‖ ≤ C :=
    fun i => hUc.exists_bound_of_continuousOn (hb i).continuousOn
  choose B hB using hBex
  have hBQex : ∀ i : Fin d, ∃ C : ℝ, ∀ x ∈ Metric.closedBall z (r / 2),
      ‖fderiv ℝ (fun w => Real.log (cutoffCoefficient M H omega N w)) x
        (Homogenization.basisVec i)‖ ≤ C :=
    fun i => (isCompact_closedBall z (r / 2)).exists_bound_of_continuousOn (hb i).continuousOn
  choose BQ hBQ using hBQex
  have hrhoc := aux_fsrkb_moll_rho_continuous M H omega N
  have hPex := hUc.exists_bound_of_continuousOn hrhoc.continuousOn
  rcases hPex with ⟨P, hP⟩
  have hdel := hUc.exists_cthickening_subset_open hQo hUQ
  rcases hdel with ⟨δ, hδ, hδsub⟩
  have hev : ∀ᶠ n in atTop, Homogenization.unitConvexApproxScale n ≤ δ :=
    ((tendsto_order.1 tendsto_unitConvexApproxScale).2 δ hδ).mono fun _ h => h.le
  have hFm := aux_fsrkb_moll_memLp_indicator z r hr f hf
  have hGm : ∀ i : Fin d, MemLp (fun y => v.zeroExtensionGrad y i) 2 volume :=
    fun i => memLp_zeroExtensionGrad_two hQo v i
  have hHm : ∀ i : Fin d, MemLp (fun y => fderiv ℝ
      (fun w => Real.log (cutoffCoefficient M H omega N w)) y (Homogenization.basisVec i) *
        v.zeroExtensionGrad y i) 2 volume := by
    intro i
    refine aux_fsrkb_moll_memLp_mul (Ω := (centeredCube z r hr : Set (SpatialCoordinates d)))
      (hGm i) (hb i) (BQ i) (fun y hy => ?_) (fun y hy => ?_)
    · rw [← Real.norm_eq_abs]
      exact hBQ i y (Metric.ball_subset_closedBall hy)
    · rw [v.zeroExtensionGrad_apply_of_not_mem hy]
      rfl
  refine aux_fsrkb_moll_sq_tendsto (cutoffSpeedDensity M H omega N) hrhoc.measurable U
    hU.measurableSet P (fun x hx => (le_abs_self _).trans
      ((Real.norm_eq_abs _).symm.le.trans (hP x (subset_closure hx)))) _
    (fun n x => |aux_fsrkb_moll_err
        ((centeredCube z r hr : Set (SpatialCoordinates d)).indicator f) n x| +
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ * ∑ i : Fin d,
        (|aux_fsrkb_moll_err (fun y => fderiv ℝ
            (fun w => Real.log (cutoffCoefficient M H omega N w)) y
              (Homogenization.basisVec i) * v.zeroExtensionGrad y i) n x| +
          B i * |aux_fsrkb_moll_err (fun y => v.zeroExtensionGrad y i) n x|)) ?_ ?_
  · filter_upwards [hev] with n hn x hx
    have hball : Metric.closedBall x (Homogenization.unitConvexApproxScale n) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d)) :=
      (Metric.closedBall_subset_closedBall hn).trans
        ((Metric.closedBall_subset_cthickening (subset_closure hx) δ).trans hδsub)
    refine aux_fsrkb_moll_abs_bound _ _ _ (inv_nonneg.2 hah.le) _ _ _ B (fun i => ?_)
      (aux_fsrkb_moll_residual_eq M H omega N z r hr hC1 lam f hf u hu v hv1 hv2 chi U hU
        (subset_closure.trans hUQ) hchi n x hx hball)
    rw [← Real.norm_eq_abs]
    exact hB i x (subset_closure hx)
  · exact aux_fsrkb_moll_comb _ B _ _ _ (fun n => aux_fsrkb_moll_err_aesm hFm n)
      (fun i n => aux_fsrkb_moll_err_aesm (hHm i) n)
      (fun i n => aux_fsrkb_moll_err_aesm (hGm i) n)
      (aux_fsrkb_moll_err_tendsto hFm) (fun i => aux_fsrkb_moll_err_tendsto (hHm i))
      (fun i => aux_fsrkb_moll_err_tendsto (hGm i))

open SubdiffusiveProcess.Probability.Diffusion.Packet452Route in
/-- The cut-off mollifications converge to the solution in `L²(U, μ)`. -/
theorem aux_fsrkb_moll_value_tendsto {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (u : killedSobolevGraph (centeredCube z r hr))
    (v : Homogenization.H10Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hv1 : (v : SpatialCoordinates d → ℝ) =
      fun x => ((u : SobolevData (centeredCube z r hr)).1) x)
    (chi : SpatialCoordinates d → ℝ) (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (hUQ : closure U ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hchi : ∀ y ∈ U, chi y = 1) :
    Tendsto (fun n => ∫ x in U,
        (chi x * mollPhi v n x - ((u : SobolevData (centeredCube z r hr)).1) x) ^ 2
          ∂(cutoffSpeedMeasure M H omega N)) atTop (𝓝 0) := by
  have hQo := (centeredCube z r hr).isOpen
  have hUc : IsCompact (closure U) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure
      ((centeredCube_isBounded z hr).subset hUQ)
  have hrhoc := aux_fsrkb_moll_rho_continuous M H omega N
  have hPex := hUc.exists_bound_of_continuousOn hrhoc.continuousOn
  rcases hPex with ⟨P, hP⟩
  refine aux_fsrkb_moll_sq_tendsto (cutoffSpeedDensity M H omega N) hrhoc.measurable U
    hU.measurableSet P (fun x hx => (le_abs_self _).trans
      ((Real.norm_eq_abs _).symm.le.trans (hP x (subset_closure hx)))) _
    (fun n x => |mollPhi v n x - v.zeroExtension x|)
    (Eventually.of_forall fun n x hx => ?_) ?_
  · have hxQ : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) :=
      hUQ (subset_closure hx)
    show _ ≤ |mollPhi v n x - v.zeroExtension x|
    rw [hchi x hx, one_mul, v.zeroExtension_apply_of_mem hxQ]
    have h1 : v.toH1Function.toFun x = ((u : SobolevData (centeredCube z r hr)).1) x :=
      congrFun hv1 x
    rw [h1]
  · exact (tendsto_mollPhi hQo v).congr fun n =>
      (aux_fsrkb_moll_eLpNorm_abs (fun x => mollPhi v n x - v.zeroExtension x)).symm

open SubdiffusiveProcess.Probability.Diffusion.Packet452Route in
/-- Nonnegative data give nonnegative cut-off mollifications. -/
theorem aux_fsrkb_moll_nonneg {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (u : killedSobolevGraph (centeredCube z r hr))
    (v : Homogenization.H10Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hv1 : (v : SpatialCoordinates d → ℝ) =
      fun x => ((u : SobolevData (centeredCube z r hr)).1) x)
    (chi : SpatialCoordinates d → ℝ) (hchi : ∀ x, 0 ≤ chi x)
    (hpos : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      0 ≤ ((u : SobolevData (centeredCube z r hr)).1) x) (n : ℕ) (x : SpatialCoordinates d) :
    0 ≤ chi x * mollPhi v n x := by
  refine mul_nonneg (hchi x) ?_
  rw [mollPhi, aux_fsrkb_moll_conv_apply]
  have hpos' := (ae_restrict_iff' (centeredCube z r hr).isOpen.measurableSet).1 hpos
  refine integral_nonneg_of_ae ?_
  filter_upwards [hpos'] with y hy
  have hk : 0 ≤ mollKernel d n (x - y) :=
    Homogenization.scaledConvexApproxKernel_nonneg
      Homogenization.isConvexApproxKernel_unitConvexApproxKernel
      (unitConvexApproxScale_pos n) _
  refine mul_nonneg ?_ hk
  by_cases hyQ : y ∈ (centeredCube z r hr : Set (SpatialCoordinates d))
  · rw [v.zeroExtension_apply_of_mem hyQ]
    have h1 : v.toH1Function.toFun y = ((u : SobolevData (centeredCube z r hr)).1) y :=
      congrFun hv1 y
    rw [h1]
    exact hy hyQ
  · rw [v.zeroExtension_apply_of_not_mem hyQ]

variable {d : ℕ}

/-- **Mollified approximants.** -/
theorem aux_fsrkb_mollify (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hC1 : ContDiff ℝ 1 (cutoffCoefficient M H omega N))
    (lam : ℝ) (hlam : 0 < lam)
    (f : SpatialCoordinates d → ℝ) (hf : aux_fsrkb_BddMeas f)
    (u : killedSobolevGraph (centeredCube z r hr))
    (hu : aux_fsrkb_WeakEq M H omega N z r hr lam f u)
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U) (hUQ : closure U ⊆ (centeredCube z r hr : Set (SpatialCoordinates d))) :
    ∃ phi : ℕ → 𝓓(centeredCube z r hr, ℝ),
      ((∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), 0 ≤ ((u : SobolevData (centeredCube z r hr)).1) x) →
          ∀ n x, 0 ≤ phi n x) ∧
      Tendsto (fun n => ∫ x in U,
          (phi n x - ((u : SobolevData (centeredCube z r hr)).1) x) ^ 2
            ∂(cutoffSpeedMeasure M H omega N)) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x in U,
          (lam * phi n x -
            aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N)
              (phi n) x - f x) ^ 2 ∂(cutoffSpeedMeasure M H omega N)) atTop (𝓝 0) := by
  have _hd := hd
  have _hlam := hlam
  have hQo := (centeredCube z r hr).isOpen
  have hUc : IsCompact (closure U) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure
      ((centeredCube_isBounded z hr).subset hUQ)
  have hv := exists_nativeH10Function_of_killedSobolevGraph u
  rcases hv with ⟨v, hv1, hv2⟩
  have hχ := Homogenization.exists_contDiff_one_on_compact_tsupport_subset hUc hUQ hQo
  rcases hχ with ⟨chi, hchiS, hchiB, hchi1, hchiQ⟩
  have hchic : HasCompactSupport chi :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport chi)
      ((centeredCube_isBounded z hr).subset hchiQ)
  have hchiU : ∀ y ∈ U, chi y = 1 := fun y hy => hchi1 (subset_closure hy)
  let phi : ℕ → 𝓓(centeredCube z r hr, ℝ) := fun n =>
    ⟨fun y => chi y * SubdiffusiveProcess.Probability.Diffusion.Packet452Route.mollPhi v n y,
      hchiS.mul (SubdiffusiveProcess.Probability.Diffusion.Packet452Route.contDiff_mollPhi hQo v n),
      hchic.mul_right,
      tsupport_mul_subset_left.trans hchiQ⟩
  refine ⟨phi, ?_, ?_, ?_⟩
  · intro hpos n x
    exact aux_fsrkb_moll_nonneg z r hr u v hv1 chi (fun x => (hchiB x).1) hpos n x
  · exact aux_fsrkb_moll_value_tendsto M H omega N z r hr u v hv1 chi U hU hUQ hchiU
  · exact aux_fsrkb_moll_resid_tendsto M H omega N z r hr hC1 lam f hf u hu v hv1 hv2 chi U hU
      hUQ hchiU

end KbMollify

section KbGleT

open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology Distributions

variable {d : ℕ}


/-- Smooth approximants of a killed-graph element. -/
theorem aux_fsrkb_gleT_approx (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (u : killedSobolevGraph (centeredCube z r hr)) :
    ∃ phi : ℕ → 𝓓(centeredCube z r hr, ℝ),
      Tendsto (fun n => smoothSobolevData (phi n)) atTop
        (𝓝 (u : SobolevData (centeredCube z r hr))) := by
  have hmem : (u : SobolevData (centeredCube z r hr)) ∈
      closure (Set.range (smoothSobolevData (Ω := centeredCube z r hr))) := by
    have h := u.2
    have hc : (killedSobolevGraph (centeredCube z r hr) : Set (SobolevData (centeredCube z r hr))) =
        closure (Set.range (smoothSobolevData (Ω := centeredCube z r hr))) := by
      rw [killedSobolevGraph, Submodule.topologicalClosure_coe, LinearMap.coe_range]
      rfl
    rw [← hc]
    exact h
  rcases mem_closure_iff_seq_limit.mp hmem with ⟨w, hw, hlim⟩
  choose phi hphi using hw
  refine ⟨phi, ?_⟩
  have heq : (fun n => smoothSobolevData (phi n)) = w := funext hphi
  rw [heq]
  exact hlim

/-- The pairing against a bounded source is a continuous linear functional of the data. -/
theorem aux_fsrkb_gleT_linFun (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (f : SpatialCoordinates d → ℝ) (hf : aux_fsrkb_BddMeas f) :
    ∃ Λ : SobolevData (centeredCube z r hr) →L[ℝ] ℝ, ∀ w : SobolevData (centeredCube z r hr),
      Λ w = ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), f x * w.1 x ∂(cutoffSpeedMeasure M H omega N) := by
  obtain ⟨hfm, B, hB0, hB⟩ := hf
  have hQm : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) := (centeredCube z r hr).isOpen.measurableSet
  obtain ⟨c, C, _, hC, hb⟩ := aux_fsrkb_speed_density_bounds M H omega N z r hr
  let h : SpatialCoordinates d → ℝ := fun x => cutoffSpeedDensity M H omega N x * f x
  have hmeas : Measurable h :=
    (aux_fsrkb_speed_density_continuous M H omega N).measurable.mul hfm
  have hmem : MemLp h 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    refine MemLp.of_bound hmeas.aestronglyMeasurable (C * B) ?_
    filter_upwards [ae_restrict_mem hQm] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (aux_fsrkb_speed_density_pos M H omega N x)]
    exact mul_le_mul (hb x hx).2 (hB x) (abs_nonneg _) hC.le
  let hL : DomainL2 (centeredCube z r hr) := hmem.toLp h
  refine ⟨(innerSL ℝ hL).comp (ContinuousLinearMap.fst ℝ (DomainL2 (centeredCube z r hr))
      (Fin d → DomainL2 (centeredCube z r hr))), fun w => ?_⟩
  change inner ℝ hL w.1 = _
  rw [L2.inner_def, aux_fsrkb_speed_integral M H omega N _ hQm]
  refine integral_congr_ae ?_
  filter_upwards [hmem.coeFn_toLp] with x hx
  rw [hx]
  simp only [h, RCLike.inner_apply, conj_trivial]
  ring

theorem aux_fsrkb_gleT_bilin_continuous {Ω : TopologicalSpace.Opens (SpatialCoordinates d)}
    (Bf : DomainL2 Ω →L[ℝ] DomainL2 Ω →L[ℝ] ℝ) :
    Continuous (fun w : SobolevData Ω => Bf w.1 w.1) := by
  have h2 : Continuous (fun p : DomainL2 Ω × DomainL2 Ω => Bf p.1 p.2) := Bf.continuous₂
  have h3 : Continuous (fun w : SobolevData Ω => ((w.1, w.1) : DomainL2 Ω × DomainL2 Ω)) :=
    continuous_fst.prodMk continuous_fst
  exact h2.comp h3


theorem aux_fsrkb_gleT_bilin_continuous_full {Ω : TopologicalSpace.Opens (SpatialCoordinates d)}
    (Bf : SobolevData Ω →L[ℝ] SobolevData Ω →L[ℝ] ℝ) :
    Continuous (fun w : SobolevData Ω => Bf w w) := by
  have h2 : Continuous (fun p : SobolevData Ω × SobolevData Ω => Bf p.1 p.2) := Bf.continuous₂
  exact h2.comp (continuous_id.prodMk continuous_id)

/-- The speed-weighted `L²` energy of the function coordinate is continuous. -/
theorem aux_fsrkb_gleT_quad_continuous (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    Continuous (fun w : SobolevData (centeredCube z r hr) =>
      ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), (w.1 x) ^ 2 ∂(cutoffSpeedMeasure M H omega N)) := by
  have hQm : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) := (centeredCube z r hr).isOpen.measurableSet
  obtain ⟨c, C, _, hC, hb⟩ := aux_fsrkb_speed_density_bounds M H omega N z r hr
  have hmem : MemLp (cutoffSpeedDensity M H omega N) ⊤ (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    refine memLp_top_of_bound
      (aux_fsrkb_speed_density_continuous M H omega N).aestronglyMeasurable C ?_
    filter_upwards [ae_restrict_mem hQm] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (aux_fsrkb_speed_density_pos M H omega N x)]
    exact (hb x hx).2
  obtain ⟨ρt, hρt⟩ : ∃ ρt : Lp ℝ ⊤ (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))), ρt = hmem.toLp _ := ⟨_, rfl⟩
  have hρae : (ρt : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] cutoffSpeedDensity M H omega N := by
    rw [hρt]
    exact hmem.coeFn_toLp
  obtain ⟨Bf, hBf⟩ : ∃ Bf : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr) →L[ℝ] ℝ,
      Bf = weightedL2Form (E := ℝ) ρt := ⟨_, rfl⟩
  have hB : ∀ a : DomainL2 (centeredCube z r hr), Bf a a = ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), (a x) ^ 2 ∂(cutoffSpeedMeasure M H omega N) := by
    intro a
    rw [hBf, weightedL2Form_apply, aux_fsrkb_speed_integral M H omega N _ hQm]
    refine integral_congr_ae ?_
    filter_upwards [hρae] with x hx
    rw [hx]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  exact (aux_fsrkb_gleT_bilin_continuous Bf).congr fun w => hB w.1


/-- A test function and its generator are bounded measurable. -/
theorem aux_fsrkb_gleT_test_bdd (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (phi : 𝓓(centeredCube z r hr, ℝ)) : aux_fsrkb_BddMeas (phi : SpatialCoordinates d → ℝ) := by
  obtain ⟨C, hC⟩ := phi.contDiff.continuous.bounded_above_of_compact_support phi.hasCompactSupport
  exact ⟨phi.contDiff.continuous.measurable, max C 0, le_max_right _ _,
    fun x => (hC x).trans (le_max_left _ _)⟩

theorem aux_fsrkb_gleT_gen_bdd (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hC1 : ContDiff ℝ 1 (cutoffCoefficient M H omega N))
    (phi : 𝓓(centeredCube z r hr, ℝ)) : aux_fsrkb_BddMeas (aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi) := by
  have hc := aux_fsrkb_gen_continuous M H omega N z r hr hC1 phi
  have hcs : HasCompactSupport (aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi) :=
    HasCompactSupport.intro phi.hasCompactSupport (aux_fsrkb_gen_eq_zero M H omega N z r hr phi)
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
  exact ⟨hc.measurable, max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

/-- For one smooth test `phi`: the expanded nonnegative pairing of `f - (lam - L) phi`. -/
theorem aux_fsrkb_gleT_step (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hC1 : ContDiff ℝ 1 (cutoffCoefficient M H omega N))
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hP : P.IsConservative)
    (hfdd : aux_fsrkb_Fdd K P)
    (hsym : SemigroupSymmetric P (cutoffSpeedMeasure M H omega N))
    (hstop : ∀ phi : 𝓓(centeredCube z r hr, ℝ),
      aux_fsrkb_StoppedDynkin K (centeredCube z r hr : Set (SpatialCoordinates d)) phi
        (aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi))
    (lam : ℝ) (hlam : 0 < lam)
    (f : SpatialCoordinates d → ℝ) (hf : aux_fsrkb_BddMeas f)
    (phi : 𝓓(centeredCube z r hr, ℝ)) :
    0 ≤ (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), f x * aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x ∂(cutoffSpeedMeasure M H omega N)) -
        2 * (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), f x * phi x ∂(cutoffSpeedMeasure M H omega N)) + lam * (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), (phi x) ^ 2 ∂(cutoffSpeedMeasure M H omega N)) -
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi x * phi x ∂(cutoffSpeedMeasure M H omega N) := by
  have hQo : IsOpen (centeredCube z r hr : Set (SpatialCoordinates d)) := (centeredCube z r hr).isOpen
  have hQm : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) := hQo.measurableSet
  haveI := aux_fsrkb_speed_isFinite M H omega N z r hr
  have hμQ : (cutoffSpeedMeasure M H omega N) (centeredCube z r hr : Set (SpatialCoordinates d)) ≠ ⊤ := by
    have h := measure_lt_top ((cutoffSpeedMeasure M H omega N).restrict (centeredCube z r hr : Set (SpatialCoordinates d))) Set.univ
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at h
    exact h.ne
  have hphiB := aux_fsrkb_gleT_test_bdd z r hr phi
  have hgenB := aux_fsrkb_gleT_gen_bdd M H omega N z r hr hC1 phi
  obtain ⟨_, Cphi, _, hCphi⟩ := hphiB
  obtain ⟨hgenm, Cgen, _, hCgen⟩ := hgenB
  have hphiU : ∀ y, y ∉ (centeredCube z r hr : Set (SpatialCoordinates d)) → phi y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport (fun h => hy (phi.tsupport_subset h))
  -- the killed resolvent inverts `lam - L` on the test
  have hT : ∀ x, aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam (fun y => lam * phi y - aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi y) x = phi x :=
    fun x => aux_fsrkb_killedRes_eq_of_dynkin K (centeredCube z r hr : Set (SpatialCoordinates d)) hQo phi (aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi)
      phi.contDiff.continuous Cphi hCphi hphiU hgenm Cgen hCgen (hstop phi) lam hlam x
  have hBddSub : ∀ a b : SpatialCoordinates d → ℝ, aux_fsrkb_BddMeas a → aux_fsrkb_BddMeas b →
      aux_fsrkb_BddMeas (fun y => a y - b y) := by
    intro a b ha hb
    obtain ⟨ham, Ba, hBa0, hBa⟩ := ha
    obtain ⟨hbm, Bb, hBb0, hBb⟩ := hb
    exact ⟨ham.sub hbm, Ba + Bb, add_nonneg hBa0 hBb0,
      fun x => (abs_sub _ _).trans (add_le_add (hBa x) (hBb x))⟩
  have hBddMul : ∀ a b : SpatialCoordinates d → ℝ, aux_fsrkb_BddMeas a → aux_fsrkb_BddMeas b →
      aux_fsrkb_BddMeas (fun y => a y * b y) := by
    intro a b ha hb
    obtain ⟨ham, Ba, hBa0, hBa⟩ := ha
    obtain ⟨hbm, Bb, hBb0, hBb⟩ := hb
    refine ⟨ham.mul hbm, Ba * Bb, mul_nonneg hBa0 hBb0, fun x => ?_⟩
    rw [abs_mul]
    exact mul_le_mul (hBa x) (hBb x) (abs_nonneg _) hBa0
  have hInt : ∀ a : SpatialCoordinates d → ℝ, aux_fsrkb_BddMeas a → Integrable a ((cutoffSpeedMeasure M H omega N).restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    intro a ha
    obtain ⟨ham, Ba, _, hBa⟩ := ha
    exact aux_fsrkb_speed_integrable_of_bdd M H omega N z r hr a ham.aestronglyMeasurable Ba hBa
  have hphiBM := aux_fsrkb_gleT_test_bdd z r hr phi
  have hgenBM := aux_fsrkb_gleT_gen_bdd M H omega N z r hr hC1 phi
  have hg : aux_fsrkb_BddMeas (fun y => lam * phi y - aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi y) :=
    hBddSub _ _ (aux_fsrkb_BddMeas_const_mul lam hphiBM) hgenBM
  have hF : aux_fsrkb_BddMeas (fun y => f y - (lam * phi y - aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi y)) := hBddSub _ _ hf hg
  have hTfBM : aux_fsrkb_BddMeas (fun x => aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x) := by
    obtain ⟨hfm, Bf, hBf0, hBf⟩ := hf
    exact ⟨aux_fsrkb_killedRes_measurable K (centeredCube z r hr : Set (SpatialCoordinates d)) hQo lam f hfm, Bf / lam, div_nonneg hBf0 hlam.le,
      fun x => aux_fsrkb_killedRes_abs_le K (centeredCube z r hr : Set (SpatialCoordinates d)) lam hlam f Bf hBf0 hBf x⟩
  have hpos := aux_fsrkb_killedRes_pairing_nonneg K P hfdd (cutoffSpeedMeasure M H omega N) hsym (centeredCube z r hr : Set (SpatialCoordinates d)) hQo hμQ lam hlam _ hF
  have hTF : ∀ x, aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam (fun y => f y - (lam * phi y - aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi y)) x =
      aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x - phi x := fun x => by
    rw [aux_fsrkb_killedRes_sub K (centeredCube z r hr : Set (SpatialCoordinates d)) hQo lam hlam f _ hf hg x, hT x]
  have hsymm := aux_fsrkb_killedRes_symm K P hfdd (cutoffSpeedMeasure M H omega N) hsym (centeredCube z r hr : Set (SpatialCoordinates d)) hQo hμQ lam hlam f _ hf hg
  have hgT : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), (lam * phi x - aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi x) * aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x ∂(cutoffSpeedMeasure M H omega N)) =
      ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), f x * phi x ∂(cutoffSpeedMeasure M H omega N) := by
    rw [hsymm]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [hT x])
  have hexp : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), (f x - (lam * phi x - aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi x)) *
      aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam (fun y => f y - (lam * phi y - aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi y)) x ∂(cutoffSpeedMeasure M H omega N)) =
      (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), f x * aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x ∂(cutoffSpeedMeasure M H omega N)) -
        (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), f x * phi x ∂(cutoffSpeedMeasure M H omega N)) -
        (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), (lam * phi x - aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi x) * aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x ∂(cutoffSpeedMeasure M H omega N)) +
        ((lam * ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), (phi x) ^ 2 ∂(cutoffSpeedMeasure M H omega N)) - ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi x * phi x ∂(cutoffSpeedMeasure M H omega N)) := by
    have h1 : Integrable (fun x => f x * aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x) ((cutoffSpeedMeasure M H omega N).restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      hInt _ (hBddMul _ _ hf hTfBM)
    have h2 : Integrable (fun x => f x * phi x) ((cutoffSpeedMeasure M H omega N).restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := hInt _ (hBddMul _ _ hf hphiBM)
    have h3 : Integrable (fun x => (lam * phi x - aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi x) *
        aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x) ((cutoffSpeedMeasure M H omega N).restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := hInt _ (hBddMul _ _ hg hTfBM)
    have h5 : Integrable (fun x => lam * phi x ^ 2) ((cutoffSpeedMeasure M H omega N).restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
      have h := (hInt _ (hBddMul _ _ hphiBM hphiBM)).const_mul lam
      exact h.congr (Filter.Eventually.of_forall fun x => by simp only [sq])
    have h6 : Integrable (fun x => aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi x * phi x) ((cutoffSpeedMeasure M H omega N).restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      hInt _ (hBddMul _ _ hgenBM hphiBM)
    have h12 : Integrable (fun x => f x * aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x - f x * phi x)
        ((cutoffSpeedMeasure M H omega N).restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := h1.sub h2
    have h123 : Integrable (fun x => f x * aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x - f x * phi x -
        (lam * phi x - aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi x) * aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x) ((cutoffSpeedMeasure M H omega N).restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      h12.sub h3
    have h56 : Integrable (fun x => lam * phi x ^ 2 - aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi x * phi x) ((cutoffSpeedMeasure M H omega N).restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      h5.sub h6
    have hpt : ∀ x, (f x - (lam * phi x - aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi x)) *
        aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam (fun y => f y - (lam * phi y - aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi y)) x =
        (f x * aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x - f x * phi x -
          (lam * phi x - aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi x) * aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x) +
        (lam * phi x ^ 2 - aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi x * phi x) := by
      intro x
      rw [hTF x]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add h123 h56,
      integral_sub h12 h3, integral_sub h1 h2, integral_sub h5 h6, integral_const_mul]
  rw [hexp, hgT] at hpos
  linarith

theorem aux_fsrkb_G_le_T (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hC1 : ContDiff ℝ 1 (cutoffCoefficient M H omega N))
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hP : P.IsConservative)
    (hfdd : aux_fsrkb_Fdd K P)
    (hsym : SemigroupSymmetric P (cutoffSpeedMeasure M H omega N))
    (hstop : ∀ phi : 𝓓(centeredCube z r hr, ℝ),
      aux_fsrkb_StoppedDynkin K (centeredCube z r hr : Set (SpatialCoordinates d)) phi
        (aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi))
    (lam : ℝ) (hlam : 0 < lam)
    (f : SpatialCoordinates d → ℝ) (hf : aux_fsrkb_BddMeas f)
    (u : killedSobolevGraph (centeredCube z r hr))
    (hu : aux_fsrkb_WeakEq M H omega N z r hr lam f u) :
    ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), f x * ((u : SobolevData (centeredCube z r hr)).1) x ∂(cutoffSpeedMeasure M H omega N) ≤
      ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), f x * aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x ∂(cutoffSpeedMeasure M H omega N) := by
  classical
  have hQo : IsOpen (centeredCube z r hr : Set (SpatialCoordinates d)) := (centeredCube z r hr).isOpen
  have hQm : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) := hQo.measurableSet
  haveI := aux_fsrkb_speed_isFinite M H omega N z r hr
  have hac := aux_fsrkb_speed_ac M H omega N (centeredCube z r hr : Set (SpatialCoordinates d)) hQm
  obtain ⟨phi, hlim⟩ := aux_fsrkb_gleT_approx z r hr u
  obtain ⟨Λ, hΛ⟩ := aux_fsrkb_gleT_linFun M H omega N z r hr f hf
  set c0 : ℝ := ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), f x * aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x ∂(cutoffSpeedMeasure M H omega N) with hc0
  let Φ : SobolevData (centeredCube z r hr) → ℝ := fun w =>
    c0 - 2 * Λ w + lam * (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), (w.1 x) ^ 2 ∂(cutoffSpeedMeasure M H omega N)) +
      sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr) w w
  have hΦc : Continuous Φ := by
    have hq := aux_fsrkb_gleT_quad_continuous M H omega N z r hr
    have hE := aux_fsrkb_gleT_bilin_continuous_full
      (sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr))
    exact ((continuous_const.sub (continuous_const.mul Λ.continuous)).add
      (continuous_const.mul hq)).add hE
  have hΦn : ∀ n, 0 ≤ Φ (smoothSobolevData (phi n)) := by
    intro n
    have hstep := aux_fsrkb_gleT_step hd M H omega N z r hr hC1 K P hP hfdd hsym hstop lam hlam f hf (phi n)
    have hae : ∀ᵐ x ∂((cutoffSpeedMeasure M H omega N).restrict (centeredCube z r hr : Set (SpatialCoordinates d))), (smoothSobolevData (phi n)).1 x = phi n x :=
      hac.ae_le (testL2_coeFn (phi n))
    have e1 : Λ (smoothSobolevData (phi n)) = ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), f x * phi n x ∂(cutoffSpeedMeasure M H omega N) := by
      rw [hΛ]
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [hx]
    have e2 : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), ((smoothSobolevData (phi n)).1 x) ^ 2 ∂(cutoffSpeedMeasure M H omega N)) =
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), (phi n x) ^ 2 ∂(cutoffSpeedMeasure M H omega N) := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [hx]
    have e3 : sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr)
        (smoothSobolevData (phi n)) (smoothSobolevData (phi n)) =
        -∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (phi n) x * phi n x ∂(cutoffSpeedMeasure M H omega N) := by
      have h := aux_fsrkb_ibp M H omega N z r hr hC1 (phi n)
        ⟨smoothSobolevData (phi n), smoothSobolevData_mem_killed (phi n)⟩
      rw [h]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [hx]
    change 0 ≤ c0 - 2 * Λ (smoothSobolevData (phi n)) +
      lam * (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), ((smoothSobolevData (phi n)).1 x) ^ 2 ∂(cutoffSpeedMeasure M H omega N)) +
      sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr)
        (smoothSobolevData (phi n)) (smoothSobolevData (phi n))
    rw [e1, e2, e3]
    linarith
  have hlimΦ : 0 ≤ Φ (u : SobolevData (centeredCube z r hr)) :=
    ge_of_tendsto ((hΦc.tendsto _).comp hlim) (Filter.Eventually.of_forall hΦn)
  -- the weak equation tested with `u` itself
  have hself := hu u
  have huL2 : MemLp (((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)) 2
      ((cutoffSpeedMeasure M H omega N).restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    aux_fsrkb_speed_memLp_two M H omega N z r hr _ (Lp.memLp _)
  have hsq : Integrable (fun x => (((u : SobolevData (centeredCube z r hr)).1) x) ^ 2)
      ((cutoffSpeedMeasure M H omega N).restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := huL2.integrable_sq
  have hfu : Integrable (fun x => f x * ((u : SobolevData (centeredCube z r hr)).1) x)
      ((cutoffSpeedMeasure M H omega N).restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    obtain ⟨hfm, B, _, hB⟩ := hf
    have hu1 : Integrable (((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ))
        ((cutoffSpeedMeasure M H omega N).restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := huL2.integrable one_le_two
    exact hu1.bdd_mul hfm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)
  have hsplit : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), (f x - lam * ((u : SobolevData (centeredCube z r hr)).1) x) *
      ((u : SobolevData (centeredCube z r hr)).1) x ∂(cutoffSpeedMeasure M H omega N)) =
      (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), f x * ((u : SobolevData (centeredCube z r hr)).1) x ∂(cutoffSpeedMeasure M H omega N)) -
        lam * ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), (((u : SobolevData (centeredCube z r hr)).1) x) ^ 2 ∂(cutoffSpeedMeasure M H omega N) := by
    rw [← integral_const_mul, ← integral_sub hfu (hsq.const_mul lam)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  have hΛu := hΛ (u : SobolevData (centeredCube z r hr))
  change 0 ≤ c0 - 2 * Λ (u : SobolevData (centeredCube z r hr)) +
    lam * (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), (((u : SobolevData (centeredCube z r hr)).1) x) ^ 2 ∂(cutoffSpeedMeasure M H omega N)) +
    sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr)
      (u : SobolevData (centeredCube z r hr)) (u : SobolevData (centeredCube z r hr)) at hlimΦ
  rw [hself, hsplit, hΛu] at hlimΦ
  linarith

end KbGleT

section KbTleG

open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology Distributions

variable {d : ℕ}


/-- `L²` squeeze: a function below an `L²`-convergent sequence is below its limit a.e. -/
theorem aux_fsrkb_tleG_ae_le {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (a b : α → ℝ) (bn : ℕ → α → ℝ) (ha : AEStronglyMeasurable a ν)
    (hb : AEStronglyMeasurable b ν) (hab : ∀ n, ∀ᵐ x ∂ν, a x ≤ bn n x)
    (hint : ∀ n, Integrable (fun x => (bn n x - b x) ^ 2) ν)
    (hlim : Tendsto (fun n => ∫ x, (bn n x - b x) ^ 2 ∂ν) atTop (𝓝 0)) :
    ∀ᵐ x ∂ν, a x ≤ b x := by
  let g : α → ℝ := fun x => (max (a x - b x) 0) ^ 2
  have hgm : AEMeasurable (fun x => ENNReal.ofReal (g x)) ν :=
    (((ha.sub hb).aemeasurable.max aemeasurable_const).pow_const 2).ennreal_ofReal
  have hle : ∀ n, ∫⁻ x, ENNReal.ofReal (g x) ∂ν ≤ ENNReal.ofReal (∫ x, (bn n x - b x) ^ 2 ∂ν) := by
    intro n
    rw [ofReal_integral_eq_lintegral_ofReal (hint n)
      (Filter.Eventually.of_forall fun x => sq_nonneg _)]
    refine lintegral_mono_ae ?_
    filter_upwards [hab n] with x hx
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases hxb : a x - b x ≤ 0
    · simp only [g, max_eq_right hxb]
      norm_num
      positivity
    · push_neg at hxb
      simp only [g, max_eq_left hxb.le]
      exact pow_le_pow_left₀ hxb.le (by linarith) 2
  have hzero : ∫⁻ x, ENNReal.ofReal (g x) ∂ν = 0 := by
    have ht : Tendsto (fun n => ENNReal.ofReal (∫ x, (bn n x - b x) ^ 2 ∂ν)) atTop (𝓝 0) := by
      have := (ENNReal.continuous_ofReal.tendsto 0).comp hlim
      simpa using this
    exact le_antisymm (ge_of_tendsto' ht hle) (zero_le _)
  have hae := (lintegral_eq_zero_iff' hgm).mp hzero
  filter_upwards [hae] with x hx
  have hx' : g x ≤ 0 := by
    simpa [ENNReal.ofReal_eq_zero] using hx
  have hsq : max (a x - b x) 0 = 0 := by
    have h0 : 0 ≤ max (a x - b x) 0 := le_max_right _ _
    nlinarith [sq_nonneg (max (a x - b x) 0)]
  have := le_max_left (a x - b x) 0
  linarith

theorem aux_fsrkb_tleG_innerCube_mono {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    {k l : ℕ} (hkl : k ≤ l) :
    (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) ⊆
      (aux_fsrkb_innerCube z r hr l : Set (SpatialCoordinates d)) := by
  change Metric.ball z (r * ((k + 1 : ℝ) / (k + 2)) / 2) ⊆
    Metric.ball z (r * ((l + 1 : ℝ) / (l + 2)) / 2)
  apply Metric.ball_subset_ball
  have hkl' : (k : ℝ) ≤ l := by exact_mod_cast hkl
  have h1 : ((k + 1 : ℝ) / (k + 2)) ≤ ((l + 1 : ℝ) / (l + 2)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have := mul_le_mul_of_nonneg_left h1 hr.le
  linarith

/-- **One interior cube.**  The killed resolvent of the interior cube is below the variational
solution, a.e. on the interior cube. -/
theorem aux_fsrkb_tleG_inner (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hC1 : ContDiff ℝ 1 (cutoffCoefficient M H omega N))
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hP : P.IsConservative)
    (hfdd : aux_fsrkb_Fdd K P)
    (hsym : SemigroupSymmetric P (cutoffSpeedMeasure M H omega N))
    (hstop : ∀ phi : 𝓓(centeredCube z r hr, ℝ),
      aux_fsrkb_StoppedDynkin K (centeredCube z r hr : Set (SpatialCoordinates d)) phi
        (aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi))
    (lam : ℝ) (hlam : 0 < lam)
    (f : SpatialCoordinates d → ℝ) (hf : aux_fsrkb_BddMeas f)
    (hf0 : ∀ x, 0 ≤ f x)
    (u : killedSobolevGraph (centeredCube z r hr))
    (hu : aux_fsrkb_WeakEq M H omega N z r hr lam f u)
    (hu0 : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), 0 ≤ ((u : SobolevData (centeredCube z r hr)).1) x)
    (k : ℕ) :
    ∀ᵐ x ∂volume.restrict (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)),
      aux_fsrkb_killedRes K (aux_fsrkb_innerCube z r hr k) lam f x ≤
        ((u : SobolevData (centeredCube z r hr)).1) x := by
  classical
  have hQo : IsOpen (centeredCube z r hr : Set (SpatialCoordinates d)) := (centeredCube z r hr).isOpen
  have hUo : IsOpen (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) := (aux_fsrkb_innerCube z r hr k).isOpen
  have hUm : MeasurableSet (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) := hUo.measurableSet
  have hUcl := aux_fsrkb_innerCube_subset z r hr k
  have hUQ : (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) := subset_closure.trans hUcl
  haveI hfinQ := aux_fsrkb_speed_isFinite M H omega N z r hr
  have hμle : (cutoffSpeedMeasure M H omega N).restrict (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) ≤ (cutoffSpeedMeasure M H omega N).restrict (centeredCube z r hr : Set (SpatialCoordinates d)) := Measure.restrict_mono hUQ le_rfl
  haveI : IsFiniteMeasure ((cutoffSpeedMeasure M H omega N).restrict (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d))) := isFiniteMeasure_of_le _ hμle
  have hμU : (cutoffSpeedMeasure M H omega N) (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) ≠ ⊤ := by
    have h := measure_lt_top ((cutoffSpeedMeasure M H omega N).restrict (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d))) Set.univ
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at h
    exact h.ne
  obtain ⟨phi, hphi0, hphiL2, hresL2⟩ :=
    aux_fsrkb_mollify hd M H omega N z r hr hC1 lam hlam f hf u hu (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) hUo hUcl
  have hphinn : ∀ n x, 0 ≤ phi n x := hphi0 hu0
  have hphiB := fun n => aux_fsrkb_gleT_test_bdd z r hr (phi n)
  have hgenB := fun n => aux_fsrkb_gleT_gen_bdd M H omega N z r hr hC1 (phi n)
  -- Dynkin at the exit of the interior cube, and the resulting domination
  have hle : ∀ n x, aux_fsrkb_killedRes K (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) lam
      (fun y => lam * phi n y - aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (phi n) y) x ≤ phi n x := by
    intro n x
    obtain ⟨_, Cp, _, hCp⟩ := hphiB n
    obtain ⟨hgm, Cg, _, hCg⟩ := hgenB n
    have hdyn := aux_fsrkb_stoppedDynkin_sub K P hP hfdd (centeredCube z r hr : Set (SpatialCoordinates d)) (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) hQo hUo hUQ (phi n) (aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (phi n))
      (phi n).contDiff.continuous Cp hCp hgm Cg hCg (hstop (phi n))
    exact aux_fsrkb_killedRes_le_of_dynkin K (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) hUo (phi n) (aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (phi n))
      (phi n).contDiff.continuous Cp hCp (hphinn n) hgm Cg hCg hdyn lam hlam x
  -- the residual sources
  let h : ℕ → SpatialCoordinates d → ℝ := fun n y => lam * phi n y - aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (phi n) y - f y
  have hhB : ∀ n, aux_fsrkb_BddMeas (h n) := by
    intro n
    obtain ⟨hpm, Cp, hCp0, hCp⟩ := hphiB n
    obtain ⟨hgm, Cg, hCg0, hCg⟩ := hgenB n
    obtain ⟨hfm, Bf, hBf0, hBf⟩ := hf
    refine ⟨((measurable_const.mul hpm).sub hgm).sub hfm, |lam| * Cp + Cg + Bf, by positivity,
      fun x => ?_⟩
    calc |lam * phi n x - aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (phi n) x - f x|
        ≤ |lam * phi n x| + |aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (phi n) x| + |f x| := by
          have h1 := abs_sub (lam * phi n x - aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (phi n) x) (f x)
          have h2 := abs_sub (lam * phi n x) (aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (phi n) x)
          linarith
      _ ≤ |lam| * Cp + Cg + Bf := by
          rw [abs_mul]
          have := mul_le_mul_of_nonneg_left (hCp x) (abs_nonneg lam)
          linarith [hCg x, hBf x]
  have hsplit : ∀ n x, aux_fsrkb_killedRes K (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) lam (fun y => lam * phi n y - aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (phi n) y) x =
      aux_fsrkb_killedRes K (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) lam f x + aux_fsrkb_killedRes K (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) lam (h n) x := by
    intro n x
    rw [← aux_fsrkb_killedRes_add K (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) hUo lam hlam f (h n) hf (hhB n) x]
    congr 1
    funext y
    simp only [h]
    ring
  -- `L²` controls
  have hu2 : MemLp (((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)) 2
      ((cutoffSpeedMeasure M H omega N).restrict (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d))) :=
    (aux_fsrkb_speed_memLp_two M H omega N z r hr _ (Lp.memLp _)).mono_measure hμle
  have hTf : aux_fsrkb_BddMeas (fun x => aux_fsrkb_killedRes K (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) lam f x) := by
    obtain ⟨hfm, Bf, hBf0, hBf⟩ := hf
    exact ⟨aux_fsrkb_killedRes_measurable K (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) hUo lam f hfm, Bf / lam, div_nonneg hBf0 hlam.le,
      fun x => aux_fsrkb_killedRes_abs_le K (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) lam hlam f Bf hBf0 hBf x⟩
  have hTh : ∀ n, aux_fsrkb_BddMeas (fun x => aux_fsrkb_killedRes K (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) lam (h n) x) := by
    intro n
    obtain ⟨hhm, Bh, hBh0, hBh⟩ := hhB n
    exact ⟨aux_fsrkb_killedRes_measurable K (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) hUo lam (h n) hhm, Bh / lam,
      div_nonneg hBh0 hlam.le, fun x => aux_fsrkb_killedRes_abs_le K (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) lam hlam (h n) Bh hBh0 hBh x⟩
  have hbd2 : ∀ a : SpatialCoordinates d → ℝ, aux_fsrkb_BddMeas a → MemLp a 2 ((cutoffSpeedMeasure M H omega N).restrict (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d))) := by
    intro a ha
    obtain ⟨ham, Ba, _, hBa⟩ := ha
    exact MemLp.of_bound ham.aestronglyMeasurable Ba
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hBa x)
  have hA : ∀ n, MemLp (fun x => phi n x - ((u : SobolevData (centeredCube z r hr)).1) x) 2
      ((cutoffSpeedMeasure M H omega N).restrict (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d))) := fun n => (hbd2 _ (hphiB n)).sub hu2
  have hB : ∀ n, MemLp (fun x => aux_fsrkb_killedRes K (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) lam (h n) x) 2 ((cutoffSpeedMeasure M H omega N).restrict (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d))) :=
    fun n => hbd2 _ (hTh n)
  have hint : ∀ n, Integrable (fun x => (phi n x - aux_fsrkb_killedRes K (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) lam (h n) x -
      ((u : SobolevData (centeredCube z r hr)).1) x) ^ 2) ((cutoffSpeedMeasure M H omega N).restrict (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d))) := by
    intro n
    have hm : MemLp (fun x => (phi n x - ((u : SobolevData (centeredCube z r hr)).1) x) -
        aux_fsrkb_killedRes K (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) lam (h n) x) 2 ((cutoffSpeedMeasure M H omega N).restrict (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d))) := (hA n).sub (hB n)
    refine hm.integrable_sq.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  have hbound : ∀ n, (∫ x, (phi n x - aux_fsrkb_killedRes K (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) lam (h n) x -
      ((u : SobolevData (centeredCube z r hr)).1) x) ^ 2 ∂((cutoffSpeedMeasure M H omega N).restrict (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)))) ≤
      2 * (∫ x in (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)), (phi n x - ((u : SobolevData (centeredCube z r hr)).1) x) ^ 2 ∂(cutoffSpeedMeasure M H omega N)) +
        2 * ((lam⁻¹) ^ 2 * ∫ x in (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)), (lam * phi n x - aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (phi n) x - f x) ^ 2 ∂(cutoffSpeedMeasure M H omega N)) := by
    intro n
    have hL2 := aux_fsrkb_killedRes_L2 K P hfdd (cutoffSpeedMeasure M H omega N) hsym (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) hUo hμU lam hlam (h n) (hhB n)
    have hi1 := (hA n).integrable_sq
    have hi2 := (hB n).integrable_sq
    have hpt : ∀ x, (phi n x - aux_fsrkb_killedRes K (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) lam (h n) x -
        ((u : SobolevData (centeredCube z r hr)).1) x) ^ 2 ≤
        2 * (phi n x - ((u : SobolevData (centeredCube z r hr)).1) x) ^ 2 +
          2 * (aux_fsrkb_killedRes K (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) lam (h n) x) ^ 2 := by
      intro x
      nlinarith [sq_nonneg (phi n x - ((u : SobolevData (centeredCube z r hr)).1) x +
        aux_fsrkb_killedRes K (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) lam (h n) x)]
    calc (∫ x, (phi n x - aux_fsrkb_killedRes K (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) lam (h n) x -
          ((u : SobolevData (centeredCube z r hr)).1) x) ^ 2 ∂((cutoffSpeedMeasure M H omega N).restrict (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d))))
        ≤ ∫ x, (2 * (phi n x - ((u : SobolevData (centeredCube z r hr)).1) x) ^ 2 +
          2 * (aux_fsrkb_killedRes K (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) lam (h n) x) ^ 2) ∂((cutoffSpeedMeasure M H omega N).restrict (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d))) :=
          integral_mono (hint n) ((hi1.const_mul 2).add (hi2.const_mul 2)) hpt
      _ = 2 * (∫ x in (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)), (phi n x - ((u : SobolevData (centeredCube z r hr)).1) x) ^ 2 ∂(cutoffSpeedMeasure M H omega N)) +
          2 * ∫ x in (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)), (aux_fsrkb_killedRes K (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) lam (h n) x) ^ 2 ∂(cutoffSpeedMeasure M H omega N) := by
          rw [integral_add (hi1.const_mul 2) (hi2.const_mul 2), integral_const_mul,
            integral_const_mul]
      _ ≤ _ := by
          have : (∫ x in (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)), (h n x) ^ 2 ∂(cutoffSpeedMeasure M H omega N)) =
              ∫ x in (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)), (lam * phi n x - aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (phi n) x - f x) ^ 2 ∂(cutoffSpeedMeasure M H omega N) := rfl
          rw [this] at hL2
          linarith
  have hlim : Tendsto (fun n => ∫ x, (phi n x - aux_fsrkb_killedRes K (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) lam (h n) x -
      ((u : SobolevData (centeredCube z r hr)).1) x) ^ 2 ∂((cutoffSpeedMeasure M H omega N).restrict (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)))) atTop (𝓝 0) := by
    have hupper : Tendsto (fun n =>
        2 * (∫ x in (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)), (phi n x - ((u : SobolevData (centeredCube z r hr)).1) x) ^ 2 ∂(cutoffSpeedMeasure M H omega N)) +
          2 * ((lam⁻¹) ^ 2 * ∫ x in (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)), (lam * phi n x - aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (phi n) x - f x) ^ 2 ∂(cutoffSpeedMeasure M H omega N)))
        atTop (𝓝 0) := by
      have := (hphiL2.const_mul 2).add ((hresL2.const_mul ((lam⁻¹) ^ 2)).const_mul 2)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun n => integral_nonneg fun x => sq_nonneg _) hbound
  have hmain : ∀ᵐ x ∂((cutoffSpeedMeasure M H omega N).restrict (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d))), aux_fsrkb_killedRes K (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) lam f x ≤
      ((u : SobolevData (centeredCube z r hr)).1) x := by
    refine aux_fsrkb_tleG_ae_le ((cutoffSpeedMeasure M H omega N).restrict (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d))) _ _
      (fun n x => phi n x - aux_fsrkb_killedRes K (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) lam (h n) x)
      hTf.1.aestronglyMeasurable hu2.aestronglyMeasurable (fun n => ?_) hint hlim
    exact Filter.Eventually.of_forall fun x => by
      have h1 := hle n x
      rw [hsplit n x] at h1
      linarith
  exact (aux_fsrkb_volume_ac_speed M H omega N (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) hUm).ae_le hmain

theorem aux_fsrkb_T_le_G (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hC1 : ContDiff ℝ 1 (cutoffCoefficient M H omega N))
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hP : P.IsConservative)
    (hfdd : aux_fsrkb_Fdd K P)
    (hsym : SemigroupSymmetric P (cutoffSpeedMeasure M H omega N))
    (hstop : ∀ phi : 𝓓(centeredCube z r hr, ℝ),
      aux_fsrkb_StoppedDynkin K (centeredCube z r hr : Set (SpatialCoordinates d)) phi
        (aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi))
    (lam : ℝ) (hlam : 0 < lam)
    (f : SpatialCoordinates d → ℝ) (hf : aux_fsrkb_BddMeas f)
    (hf0 : ∀ x, 0 ≤ f x)
    (u : killedSobolevGraph (centeredCube z r hr))
    (hu : aux_fsrkb_WeakEq M H omega N z r hr lam f u)
    (hu0 : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), 0 ≤ ((u : SobolevData (centeredCube z r hr)).1) x) :
    ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x ≤ ((u : SobolevData (centeredCube z r hr)).1) x := by
  classical
  have hQm : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) := (centeredCube z r hr).isOpen.measurableSet
  have hinner : ∀ k : ℕ, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      x ∈ (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) →
        aux_fsrkb_killedRes K (aux_fsrkb_innerCube z r hr k) lam f x ≤
          ((u : SobolevData (centeredCube z r hr)).1) x := by
    intro k
    have h := aux_fsrkb_tleG_inner hd M H omega N z r hr hC1 K P hP hfdd hsym hstop lam hlam f hf
      hf0 u hu hu0 k
    have h' := (ae_restrict_iff' (aux_fsrkb_innerCube z r hr k).isOpen.measurableSet).mp h
    exact ae_restrict_of_ae h'
  rw [← ae_all_iff] at hinner
  filter_upwards [hinner, ae_restrict_mem hQm] with x hx hxQ
  have hmem : x ∈ ⋃ k, (aux_fsrkb_innerCube z r hr k : Set (SpatialCoordinates d)) := by
    rw [aux_fsrkb_iUnion_innerCube]
    exact hxQ
  obtain ⟨k0, hk0⟩ := Set.mem_iUnion.mp hmem
  have hev : ∀ᶠ k in atTop, aux_fsrkb_killedRes K (aux_fsrkb_innerCube z r hr k) lam f x ≤
      ((u : SobolevData (centeredCube z r hr)).1) x :=
    Filter.eventually_atTop.mpr ⟨k0, fun k hk => hx k (aux_fsrkb_tleG_innerCube_mono z r hr hk hk0)⟩
  exact le_of_tendsto (aux_fsrkb_killedRes_innerCube_tendsto K z r hr lam hlam f hf hf0 x) hev

end KbTleG

section KbFixed

open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology Distributions

variable {d : ℕ}


/-- For a nonnegative source, the source annihilates the difference of the two resolvents. -/
theorem aux_fsrkb_fixed_nonneg (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hC1 : ContDiff ℝ 1 (cutoffCoefficient M H omega N))
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hP : P.IsConservative)
    (hfdd : aux_fsrkb_Fdd K P)
    (hsym : SemigroupSymmetric P (cutoffSpeedMeasure M H omega N))
    (hstop : ∀ phi : 𝓓(centeredCube z r hr, ℝ),
      aux_fsrkb_StoppedDynkin K (centeredCube z r hr : Set (SpatialCoordinates d)) phi
        (aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi))
    (lam : ℝ) (hlam : 0 < lam)
    (f : SpatialCoordinates d → ℝ) (hf : aux_fsrkb_BddMeas f)
    (hf0 : ∀ x, 0 ≤ f x) (u : killedSobolevGraph (centeredCube z r hr))
    (hu : aux_fsrkb_WeakEq M H omega N z r hr lam f u) :
    ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      f x * (((u : SobolevData (centeredCube z r hr)).1) x - aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x) = 0 := by
  classical
  have hQo : IsOpen (centeredCube z r hr : Set (SpatialCoordinates d)) := (centeredCube z r hr).isOpen
  have hQm : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) := hQo.measurableSet
  haveI := aux_fsrkb_speed_isFinite M H omega N z r hr
  have hu0 := aux_fsrkb_weakEq_nonneg M H omega N z r hr lam hlam f hf hf0 u hu
  have hTG := aux_fsrkb_T_le_G hd M H omega N z r hr hC1 K P hP hfdd hsym hstop lam hlam f hf hf0 u hu hu0
  have hGT := aux_fsrkb_G_le_T hd M H omega N z r hr hC1 K P hP hfdd hsym hstop lam hlam f hf u hu
  have hac := aux_fsrkb_speed_ac M H omega N (centeredCube z r hr : Set (SpatialCoordinates d)) hQm
  have hDnn : ∀ᵐ x ∂((cutoffSpeedMeasure M H omega N).restrict (centeredCube z r hr : Set (SpatialCoordinates d))), 0 ≤ f x *
      (((u : SobolevData (centeredCube z r hr)).1) x - aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x) := by
    filter_upwards [hac.ae_le hTG] with x hx
    exact mul_nonneg (hf0 x) (sub_nonneg.mpr hx)
  obtain ⟨hfm, B, hB0, hB⟩ := hf
  have hu2 : MemLp (((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)) 2
      ((cutoffSpeedMeasure M H omega N).restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    aux_fsrkb_speed_memLp_two M H omega N z r hr _ (Lp.memLp _)
  have hfu : Integrable (fun x => f x * ((u : SobolevData (centeredCube z r hr)).1) x)
      ((cutoffSpeedMeasure M H omega N).restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    (hu2.integrable one_le_two).bdd_mul hfm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)
  have hfT : Integrable (fun x => f x * aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x) ((cutoffSpeedMeasure M H omega N).restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    refine aux_fsrkb_speed_integrable_of_bdd M H omega N z r hr _
      (hfm.mul (aux_fsrkb_killedRes_measurable K (centeredCube z r hr : Set (SpatialCoordinates d)) hQo lam f hfm)).aestronglyMeasurable
      (B * (B / lam)) fun x => ?_
    rw [abs_mul]
    exact mul_le_mul (hB x) (aux_fsrkb_killedRes_abs_le K (centeredCube z r hr : Set (SpatialCoordinates d)) lam hlam f B hB0 hB x)
      (abs_nonneg _) hB0
  have hDint : Integrable (fun x => f x *
      (((u : SobolevData (centeredCube z r hr)).1) x - aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x))
      ((cutoffSpeedMeasure M H omega N).restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    refine (hfu.sub hfT).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hDeq : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), f x *
      (((u : SobolevData (centeredCube z r hr)).1) x - aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x) ∂(cutoffSpeedMeasure M H omega N)) =
      (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), f x * ((u : SobolevData (centeredCube z r hr)).1) x ∂(cutoffSpeedMeasure M H omega N)) -
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), f x * aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x ∂(cutoffSpeedMeasure M H omega N) := by
    rw [← integral_sub hfu hfT]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  have hzero : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), f x *
      (((u : SobolevData (centeredCube z r hr)).1) x - aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x) ∂(cutoffSpeedMeasure M H omega N)) = 0 := by
    apply le_antisymm
    · rw [hDeq]
      linarith
    · exact integral_nonneg_of_ae hDnn
  have hae := (integral_eq_zero_iff_of_nonneg_ae hDnn hDint).mp hzero
  exact (aux_fsrkb_volume_ac_speed M H omega N (centeredCube z r hr : Set (SpatialCoordinates d)) hQm).ae_le hae

/-- For a source bounded below by a positive constant the two resolvents agree. -/
theorem aux_fsrkb_fixed_pos (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hC1 : ContDiff ℝ 1 (cutoffCoefficient M H omega N))
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hP : P.IsConservative)
    (hfdd : aux_fsrkb_Fdd K P)
    (hsym : SemigroupSymmetric P (cutoffSpeedMeasure M H omega N))
    (hstop : ∀ phi : 𝓓(centeredCube z r hr, ℝ),
      aux_fsrkb_StoppedDynkin K (centeredCube z r hr : Set (SpatialCoordinates d)) phi
        (aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi))
    (lam : ℝ) (hlam : 0 < lam)
    (f : SpatialCoordinates d → ℝ) (hf : aux_fsrkb_BddMeas f)
    (c : ℝ) (hc : 0 < c) (hfc : ∀ x, c ≤ f x) (u : killedSobolevGraph (centeredCube z r hr))
    (hu : aux_fsrkb_WeakEq M H omega N z r hr lam f u) :
    ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      ((u : SobolevData (centeredCube z r hr)).1) x = aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x := by
  have h := aux_fsrkb_fixed_nonneg hd M H omega N z r hr hC1 K P hP hfdd hsym hstop lam hlam f hf (fun x => hc.le.trans (hfc x)) u hu
  filter_upwards [h] with x hx
  have hfx : f x ≠ 0 := (hc.trans_le (hfc x)).ne'
  have := (mul_eq_zero.mp hx).resolve_left hfx
  linarith



theorem aux_fsrkb_fixed (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hC1 : ContDiff ℝ 1 (cutoffCoefficient M H omega N))
    (K : Kernel (SpatialCoordinates d) (DiffusionPath d)) [IsMarkovKernel K]
    (P : SubMarkovKernelSemigroup (SpatialCoordinates d)) (hP : P.IsConservative)
    (hfdd : aux_fsrkb_Fdd K P)
    (hsym : SemigroupSymmetric P (cutoffSpeedMeasure M H omega N))
    (hstop : ∀ phi : 𝓓(centeredCube z r hr, ℝ),
      aux_fsrkb_StoppedDynkin K (centeredCube z r hr : Set (SpatialCoordinates d)) phi
        (aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi))
    (lam : ℝ) (hlam : 0 < lam)
    (f : SpatialCoordinates d → ℝ) (hf : aux_fsrkb_BddMeas f) :
    ∃ u : killedSobolevGraph (centeredCube z r hr),
      (∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        ((u : SobolevData (centeredCube z r hr)).1) x = aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x) ∧
      aux_fsrkb_WeakEq M H omega N z r hr lam f u := by
  classical
  have hQo : IsOpen (centeredCube z r hr : Set (SpatialCoordinates d)) := (centeredCube z r hr).isOpen
  obtain ⟨hfm, B, hB0, hB⟩ := hf
  have hfBM : aux_fsrkb_BddMeas f := ⟨hfm, B, hB0, hB⟩
  set c : ℝ := B + 1 with hcdef
  have hc : 0 < c := by linarith
  have hcB : aux_fsrkb_BddMeas (fun _ : SpatialCoordinates d => c) := aux_fsrkb_BddMeas_const c
  have hgB : aux_fsrkb_BddMeas (fun x => f x + c) := aux_fsrkb_BddMeas_add hfBM hcB
  have hg1 : ∀ x, (1 : ℝ) ≤ f x + c := by
    intro x
    have := (abs_le.mp (hB x)).1
    linarith
  obtain ⟨u, hu⟩ := aux_fsrkb_exists_weakEq M H omega N z r hr lam hlam f hfBM
  obtain ⟨uc, huc⟩ := aux_fsrkb_exists_weakEq M H omega N z r hr lam hlam _ hcB
  have hsum := aux_fsrkb_weakEq_add M H omega N z r hr lam f _ hfBM hcB u uc hu huc
  have hEc := aux_fsrkb_fixed_pos hd M H omega N z r hr hC1 K P hP hfdd hsym hstop lam hlam _ hcB c hc (fun _ => le_rfl) uc huc
  have hEg := aux_fsrkb_fixed_pos hd M H omega N z r hr hC1 K P hP hfdd hsym hstop lam hlam _ hgB 1 one_pos hg1 (u + uc) hsum
  have hadd : ∀ x, aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam (fun x => f x + c) x =
      aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam f x + aux_fsrkb_killedRes K (centeredCube z r hr : Set (SpatialCoordinates d)) lam (fun _ => c) x :=
    fun x => aux_fsrkb_killedRes_add K (centeredCube z r hr : Set (SpatialCoordinates d)) hQo lam hlam f _ hfBM hcB x
  refine ⟨u, ?_, hu⟩
  have hcoe : (((u + uc : killedSobolevGraph (centeredCube z r hr)) : SobolevData (centeredCube z r hr)).1 :
      SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      (((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) +
        ((uc : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)) := by
    have : (((u + uc : killedSobolevGraph (centeredCube z r hr)) : SobolevData (centeredCube z r hr)).1) =
        (u : SobolevData (centeredCube z r hr)).1 + (uc : SobolevData (centeredCube z r hr)).1 := rfl
    rw [this]
    exact Lp.coeFn_add _ _
  filter_upwards [hEc, hEg, hcoe] with x hxc hxg hxs
  rw [hxs, Pi.add_apply, hadd x, hxc] at hxg
  linarith

end KbFixed

section KbRegularity

open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology Distributions

variable {d : ℕ}

theorem aux_fsrkb_potential_regular [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∃ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
        ∀ x, cutoffPotential H omega N x = g x := by
  classical
  let μ : Measure (NativeBilateralPotentialSample d) :=
    Measure.infinitePi (fun _ : ℤ =>
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)
  let F : NativeBilateralPotentialSample d →
      SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d :=
    fun omega k => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k (omega (k : ℤ))
  have hFmeas : Measurable F := by
    apply measurable_pi_lambda _
    intro k
    exact (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_triadicScale k).comp
      (measurable_pi_apply (k : ℤ))
  have hFmap : Measure.map F μ = M.P.toMeasure := by
    let μ0 : Measure (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :=
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure
    let S : Set ℤ := {j | 0 ≤ j}
    let e : ℕ ≃ {j : ℤ // j ∈ S} :=
      { toFun := fun k => ⟨(k : ℤ), by simp [S]⟩
        invFun := fun j => j.1.toNat
        left_inv := by intro k; simp
        right_inv := by
          intro j
          apply Subtype.ext
          simp [S, Int.toNat_of_nonneg j.2] }
    let R : (ℤ → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) →
        ({j : ℤ // j ∈ S} → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :=
      S.restrict
    let E : ({j : ℤ // j ∈ S} → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) →
        (ℕ → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :=
      fun x k => x (e k)
    let T : (ℕ → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) →
        (ℕ → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :=
      fun x k => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k (x k)
    have hR : Measurable R := by
      exact measurable_pi_iff.mpr fun j => measurable_pi_apply j.1
    have hE : Measurable E := by
      exact measurable_pi_lambda _ fun k => measurable_pi_apply (e k)
    have hT : Measurable T := by
      exact measurable_pi_lambda _ fun k =>
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_triadicScale k).comp
          (measurable_pi_apply k)
    have hrestrict :
        Measure.map R μ = Measure.infinitePi
          (fun _ : {j : ℤ // j ∈ S} => μ0) := by
      simpa only [R, μ, μ0] using
        (Measure.infinitePi_map_restrict' (μ := fun _ : ℤ => μ0) (I := S))
    have hreindex :
        Measure.map E (Measure.infinitePi
          (fun _ : {j : ℤ // j ∈ S} => μ0)) =
          Measure.infinitePi (fun _ : ℕ => μ0) := by
      have h := Measure.infinitePi_map_piCongrLeft
        (μ := fun _ : ℕ => μ0) e.symm
      simpa only [E, e] using h
    have hscale :
        Measure.map T (Measure.infinitePi (fun _ : ℕ => μ0)) =
          Measure.infinitePi (fun k : ℕ =>
            (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure.map
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k)) := by
      rw [Measure.infinitePi_map_pi
        (μ := fun _ : ℕ => μ0)
        (f := fun k : ℕ =>
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k)
        (fun k => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_triadicScale k)]
    have hprod : M.P.toMeasure = Measure.infinitePi
        (fun k : ℕ =>
          (SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P k).toMeasure) := by
      have hi :=
        (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
          (P := M.P.toMeasure)
          (X := fun k (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) => omega k)
          (fun k => measurable_pi_apply k)).mp M.shellPrefix.independent
      simpa only [Measure.map_id'] using hi
    have hcomp : F = T ∘ E ∘ R := by
      funext omega k
      rfl
    calc
      Measure.map F μ = Measure.map (T ∘ E ∘ R) μ := by rw [hcomp]
      _ = Measure.map T (Measure.map E (Measure.map R μ)) := by
        calc
          Measure.map (T ∘ E ∘ R) μ =
              Measure.map T (Measure.map (E ∘ R) μ) :=
            (Measure.map_map hT (hE.comp hR)).symm
          _ = Measure.map T (Measure.map E (Measure.map R μ)) := by
            rw [Measure.map_map hE hR]
      _ = M.P.toMeasure := by
        rw [hrestrict, hreindex, hscale]
        calc
          Measure.infinitePi (fun k : ℕ =>
              (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure.map
                (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k)) =
              Measure.infinitePi (fun k : ℕ =>
                (SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P k).toMeasure) := by
            congr 1
            funext k
            have hm := congrArg
              (fun Q : ProbabilityMeasure
                (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) => Q.toMeasure)
              (M.shellPrefix.marginal_scaling k)
            calc
              Measure.map
                  (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k)
                  (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure =
                  ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).map
                    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_triadicScale k).aemeasurable).toMeasure := rfl
              _ = (SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P k).toMeasure := hm.symm
          _ = M.P.toMeasure := hprod.symm
  obtain ⟨C0, hC0, hlem⟩ := exists_native_infrared_limit hd
  obtain ⟨Hn, hHnmeas, hHnObs, hHnAE, hHnLp, hHnExp⟩ := hlem M
  let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let π : NativeBilateralPotentialSample d → BilateralField d :=
    fun omega j => layerScaling d j (forget (omega j))
  have hπmeas : Measurable π := by
    apply measurable_pi_lambda
    intro j
    exact (layerScaling d j).continuous.measurable.comp
      (forget.continuous.measurable.comp (measurable_pi_apply j))
  have hπmeasure : Measure.map π μ = (chaosSampleLaw M).toMeasure := by
    simpa only [chaosSampleLaw, chaosRootFieldLaw, μ, π, Function.comp_apply] using
      (measurePreserving_nativeCopies_commonScaleLaw M).map_eq
  have hπinj : Function.Injective π := by
    have hforgetinj : Function.Injective forget := by
      intro g h hgh
      apply SubdiffusiveProcess.Frozen.Assumptions.PotentialField.ext
      intro x
      exact congrArg (fun f : C(SpatialCoordinates d, ℝ) => f x) hgh
    intro omega omega' heq
    funext j
    have hscaleinj : Function.Injective (layerScaling d j) := by
      intro f g hfg
      ext x
      have hx := congrArg (fun q : C(SpatialCoordinates d, ℝ) =>
        q ((3 : ℝ) ^ j • x)) hfg
      change f ((3 : ℝ) ^ (-j) • ((3 : ℝ) ^ j • x)) =
        g ((3 : ℝ) ^ (-j) • ((3 : ℝ) ^ j • x)) at hx
      have hp : (3 : ℝ) ^ (-j) * (3 : ℝ) ^ j = 1 := by
        rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
        simp
      have hp' : ((3 : ℝ) ^ j)⁻¹ * (3 : ℝ) ^ j = 1 :=
        inv_mul_cancel₀ (by positivity)
      simpa [smul_smul, hp, hp'] using hx
    apply hforgetinj
    apply hscaleinj
    exact congrFun heq j
  have hπemb : MeasurableEmbedding π := hπmeas.measurableEmbedding hπinj
  have hHβ : ∀ᵐ omega ∂μ,
      Tendsto (fun L => infraredPartialSum (π omega) L) atTop
        (nhds (H (π omega))) := by
    have h0 := hH.2
    rw [← hπmeasure] at h0
    exact ae_of_ae_map hπmeas.aemeasurable h0
  have hsum : ∀ omega L,
      infraredPartialSum (π omega) L =
        forget (positiveAnchoredInfraredTruncation omega L) := by
    intro omega L
    have hπpos : ∀ n,
        forget (positiveScaledNativeLayer omega n) =
          π omega (Int.ofNat (n + 1)) := by
      intro n
      ext x
      change omega (n + 1) ((3 : ℝ) ^ (-(n + 1 : ℤ)) • x) =
        omega (Int.ofNat (n + 1)) ((3 : ℝ) ^ (-Int.ofNat (n + 1)) • x)
      congr 1
    induction L with
    | zero =>
        simp [infraredPartialSum, positiveAnchoredInfraredTruncation, forget,
          zeroNativePotentialField]
    | succ L ih =>
        unfold infraredPartialSum
        rw [Finset.sum_range_succ]
        change infraredPartialSum (π omega) L +
            (π omega (Int.ofNat (L + 1)) -
              ContinuousMap.const _ ((π omega (Int.ofNat (L + 1))) 0)) = _
        rw [ih, ← hπpos L]
        ext x
        change (forget (positiveAnchoredInfraredTruncation omega L)) x +
            ((forget (positiveScaledNativeLayer omega L)) x -
              (forget (positiveScaledNativeLayer omega L)) 0) =
          (forget (positiveAnchoredInfraredTruncation omega L)) x +
            ((forget (positiveScaledNativeLayer omega L)) x -
              (forget (positiveScaledNativeLayer omega L)) 0)
        rfl
  have hnative_eq : ∀ᵐ omega ∂μ, ∀ x,
      H (π omega) x = (forget (Hn omega)) x := by
    filter_upwards [hHβ, hHnAE] with omega hbeta hnative
    intro x
    have hbeta_x :=
      ((continuous_eval_const x).tendsto (H (π omega))).comp hbeta
    have hbeta_x' : Tendsto
        (fun L => (forget (positiveAnchoredInfraredTruncation omega L)) x)
        atTop (nhds (H (π omega) x)) := by
      change Tendsto (fun L => (infraredPartialSum (π omega) L) x) atTop
        (nhds (H (π omega) x)) at hbeta_x
      rw [show (fun L => (infraredPartialSum (π omega) L) x) =
          (fun L => (forget (positiveAnchoredInfraredTruncation omega L)) x) by
        funext L
        exact congrArg (fun q : C(SpatialCoordinates d, ℝ) => q x)
          (hsum omega L)] at hbeta_x
      exact hbeta_x
    have hpt : Tendsto
        (fun L => (forget (positiveAnchoredInfraredTruncation omega L)) x)
        atTop (nhds ((forget (Hn omega)) x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      apply squeeze_zero (fun L => norm_nonneg _)
      · intro L
        let q := SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add
          (positiveAnchoredInfraredTruncation omega L)
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.scale (-1) (Hn omega))
        change ‖(forget (positiveAnchoredInfraredTruncation omega L)) x -
            (forget (Hn omega)) x‖ ≤ compactPotentialC1Norm
              (⟨{x}, isCompact_singleton⟩ : TopologicalSpace.Compacts (SpatialCoordinates d)) q
        rw [show (forget (positiveAnchoredInfraredTruncation omega L)) x -
            (forget (Hn omega)) x = q x by
              change (positiveAnchoredInfraredTruncation omega L) x - (Hn omega) x = q x
              dsimp [q]
              ring]
        unfold compactPotentialC1Norm
        exact (ContinuousMap.norm_coe_le_norm
          (⟨fun z : (⟨{x}, isCompact_singleton⟩ : TopologicalSpace.Compacts (SpatialCoordinates d)) =>
              q z.1, q.1.1.continuous.comp continuous_subtype_val⟩ :
            C((⟨{x}, isCompact_singleton⟩ : TopologicalSpace.Compacts (SpatialCoordinates d)), ℝ))
          ⟨x, Set.mem_singleton x⟩).trans
          (le_add_of_nonneg_right (by positivity))
      · simpa only [sub_zero] using
          hnative.2.1 (⟨{x}, isCompact_singleton⟩ : TopologicalSpace.Compacts (SpatialCoordinates d))
    exact tendsto_nhds_unique hbeta_x' hpt
  have hnative_final : ∀ᵐ omega ∂μ, ∀ N : ℕ,
      ∃ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
        ∀ x, cutoffPotential H (π omega) N x = g x := by
    filter_upwards [hnative_eq] with omega hEq
    intro N
    let negField : ℕ → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d := fun j =>
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale ((3 : ℝ) ^ j)
        (omega (-(Int.ofNat j)))
    let G : ℕ → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d := fun N =>
      Nat.rec
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add (Hn omega) (negField 0))
        (fun n g => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add g (negField (n + 1))) N
    refine ⟨G N, ?_⟩
    have hnegfun : ∀ j : ℕ,
        (fun x => (π omega) (-(Int.ofNat j)) x) = fun x => negField j x := by
      intro j
      funext x
      simp only [π, negField, layerScaling,
        ContinuousMap.compRightContinuousMap_apply, ContinuousMap.comp_apply,
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale_apply,
        neg_neg, Int.ofNat_eq_natCast, zpow_natCast]
      rfl
    have hfun : (fun y => H (π omega) y) = fun y => (Hn omega) y := by
      funext y
      exact hEq y
    have hcut : ∀ N,
        cutoffPotential H (π omega) N = fun x => G N x := by
      intro N
      induction N with
      | zero =>
          funext x
          calc
            cutoffPotential H (π omega) 0 x = H (π omega) x + (π omega) 0 x := by
              simp [cutoffPotential]
            _ = (Hn omega) x + (negField 0) x := by
              rw [congrFun hfun x]
              have h0 := congrFun (hnegfun 0) x
              exact congrArg (fun z => (Hn omega) x + z)
                (by simpa only [Int.ofNat_zero, neg_zero] using h0)
            _ = G 0 x := by rfl
      | succ N ih =>
          funext x
          have hstep : cutoffPotential H (π omega) (N + 1) x =
              cutoffPotential H (π omega) N x +
                (π omega) (-(Int.ofNat (N + 1))) x := by
            change H (π omega) x +
                (∑ j ∈ Finset.range ((N + 1) + 1), (π omega) (-(Int.ofNat j)) x) =
              (H (π omega) x +
                (∑ j ∈ Finset.range (N + 1), (π omega) (-(Int.ofNat j)) x)) +
                (π omega) (-(Int.ofNat (N + 1))) x
            rw [Finset.sum_range_succ]
            ring
          calc
            cutoffPotential H (π omega) (N + 1) x =
                cutoffPotential H (π omega) N x +
                  (π omega) (-(Int.ofNat (N + 1))) x := hstep
            _ = (G N) x + (π omega) (-(Int.ofNat (N + 1))) x := by
              rw [congrFun ih x]
            _ = (G (N + 1)) x := by
              rw [show G (N + 1) =
                SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add (G N) (negField (N + 1)) by rfl]
              have hn := congrFun (hnegfun (N + 1)) x
              simpa only [SubdiffusiveProcess.Frozen.Assumptions.PotentialField.add_apply] using
                congrArg (fun z => (G N) x + z) hn
    exact congrFun (hcut N)
  rw [← hπmeasure]
  exact hπemb.ae_map_iff.mpr hnative_final

theorem aux_fsrkb_coefficient_contDiff (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d)
    (hg : ∀ x, cutoffPotential H omega N x = g x) :
    ContDiff ℝ 1 (cutoffCoefficient M H omega N) := by
  have hpot : cutoffPotential H omega N = fun x => g x := by
    funext x
    exact hg x
  have hcform : cutoffCoefficient M H omega N = fun x => (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
      Real.exp (g x - (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by
    funext x
    simp only [cutoffCoefficient]
    rw [hpot]
  rw [hcform]
  exact contDiff_const.mul
    ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.contDiff_one g).sub contDiff_const).exp

end KbRegularity

section KbMain

open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Distributions

theorem aux_fsrkb_main_check
    {d : Nat} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : Nat → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : Nat → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (E : Nat → BilateralField d → SobolevData (centeredCube z r hr) →
      SobolevData (centeredCube z r hr) → ℝ)
    (hE : ∀ N omega u v, E N omega u v =
      sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr) u v)
    (R : Nat → BilateralField d → ℝ → (SpatialCoordinates d → ℝ) → SpatialCoordinates d → ℝ)
    (hR : ∀ N omega lam f x, R N omega lam f x =
      ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
          (centeredCube z r hr : Set (SpatialCoordinates d)) path}
          (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
        ∂(KN N (omega, x)))
    (L : Nat → BilateralField d → (SpatialCoordinates d → ℝ) → SpatialCoordinates d → ℝ)
    (hL : ∀ N omega phi x, L N omega phi x =
      (cutoffSpeedDensity M H omega N x)⁻¹ * ∑ i : Fin d,
        (fderiv ℝ (fun y => cutoffCoefficient M H omega N y *
          (fderiv ℝ phi y) (Pi.single i 1)) x) (Pi.single i 1))
    (hstop :
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : Nat,
        ∀ (x : SpatialCoordinates d) (phi : SpatialCoordinates d → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) phi →
          HasCompactSupport phi →
          Function.support phi ⊆
            (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ t : ℝ≥0,
            ∫ path,
              (phi (path (ContinuousPath.exitTimeTrunc
                (centeredCube z r hr : Set (SpatialCoordinates d)) t path)) -
                phi x -
                ∫ s in Set.Icc (0 : ℝ)
                    ((ContinuousPath.exitTimeTrunc
                      (centeredCube z r hr : Set (SpatialCoordinates d)) t path) : ℝ),
                  L N omega phi (path (Real.toNNReal s)))
              ∂(KN N (omega, x)) = 0)
    (hSymm : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      SemigroupSymmetric (PN N omega) (cutoffSpeedMeasure M H omega N)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : Nat,
      (∀ (lam : ℝ), 0 < lam → ∀ (f : SpatialCoordinates d → ℝ), Measurable f →
        ∀ (B : ℝ), 0 ≤ B → (∀ x, |f x| ≤ B) →
        ∃ u : killedSobolevGraph (centeredCube z r hr),
          (∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
            ((u : SobolevData (centeredCube z r hr)).1) x = R N omega lam f x) ∧
          (∀ v : killedSobolevGraph (centeredCube z r hr),
            E N omega (u : SobolevData (centeredCube z r hr))
              (v : SobolevData (centeredCube z r hr)) =
            ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
              (f x - lam * ((u : SobolevData (centeredCube z r hr)).1) x) *
                ((v : SobolevData (centeredCube z r hr)).1) x
                ∂(cutoffSpeedMeasure M H omega N))) := by
  have hreg := aux_fsrkb_potential_regular hd M H hH
  have hfddAE := hin.2.2
  filter_upwards [hreg, hfddAE, hstop, hSymm] with omega hregω hfddω hstopω hsymω
  intro N lam hlam f hf B hB hfB
  let K : Kernel (SpatialCoordinates d) (DiffusionPath d) :=
    (KN N).comap (fun x => (omega, x)) measurable_prodMk_left
  haveI : IsMarkovKernel K := by
    haveI := hKN N
    exact Kernel.IsMarkovKernel.comap _ _
  have hKx : ∀ x, K x = KN N (omega, x) := fun x => rfl
  have hfddK : aux_fsrkb_Fdd K (PN N omega) := by
    intro I x
    rw [hKx, ← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)]
    exact hfddω N I x
  obtain ⟨g, hg⟩ := hregω N
  have hC1 := aux_fsrkb_coefficient_contDiff M H omega N g hg
  have hLfun : ∀ phi : SpatialCoordinates d → ℝ, L N omega phi =
      aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi := by
    intro phi
    funext x
    rw [hL]
    rfl
  have hstopK : ∀ phi : 𝓓(centeredCube z r hr, ℝ),
      aux_fsrkb_StoppedDynkin K (centeredCube z r hr : Set (SpatialCoordinates d)) phi
        (aux_fsrkb_gen (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) phi) := by
    intro phi x t
    have h := hstopω N x phi phi.contDiff phi.hasCompactSupport
      ((subset_tsupport _).trans phi.tsupport_subset) t
    rw [← hLfun]
    exact h
  have hfBM : aux_fsrkb_BddMeas f := ⟨hf, B, hB, hfB⟩
  obtain ⟨u, hae, hweak⟩ := aux_fsrkb_fixed hd M H omega N z r hr hC1 K (PN N omega)
    (hin.2.1 N omega) hfddK (hsymω N) hstopK lam hlam f hfBM
  refine ⟨u, ?_, ?_⟩
  · filter_upwards [hae] with x hx
    rw [hx, hR]
    rfl
  · intro v
    rw [hE]
    exact hweak v

end KbMain

theorem aux_finite_speed_resolvent_killed_bridge_energy_nonneg
    {d : Nat} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (_hH : InfraredCharacterization M H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (E : Nat → BilateralField d → SobolevData (centeredCube z r hr) →
      SobolevData (centeredCube z r hr) → ℝ)
    (hE : ∀ N omega u v, E N omega u v =
      sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr) u v)
    (N : Nat) (omega : BilateralField d)
    (u : killedSobolevGraph (centeredCube z r hr)) :
    0 ≤ E N omega (u : SobolevData (centeredCube z r hr))
      (u : SobolevData (centeredCube z r hr)) := by
  rw [hE]
  exact sobolevCoefficientForm_nonneg
    (Lane4.cutoffPositiveCoefficient M H omega N z hr)
    (u : SobolevData (centeredCube z r hr))

theorem aux_finite_speed_resolvent_killed_bridge_density_normalization
    {d : Nat} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : Nat) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) :
    ∀ x : SpatialCoordinates d,
      cutoffSpeedDensity M H omega N x =
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N * cutoffCoefficient M H omega N x := by
  exact (killed_generator_normalization M H omega N z r hr).1

theorem aux_finite_speed_resolvent_killed_bridge_symmetry
    {d : Nat} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (PN : Nat → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (hSymm : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      SemigroupSymmetric (PN N omega) (cutoffSpeedMeasure M H omega N)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      SemigroupSymmetric (PN N omega) (cutoffSpeedMeasure M H omega N) := by
  exact hSymm

theorem aux_finite_speed_resolvent_killed_bridge_variational_unique
    {d : Nat} {Ω : TopologicalSpace.Opens (SpatialCoordinates d)}
    (μ : Measure (SpatialCoordinates d)) (lam : ℝ)
    (E : killedSobolevGraph Ω → killedSobolevGraph Ω → ℝ)
    (u v : killedSobolevGraph Ω)
    (hE : ∀ w, 0 ≤ E w w)
    (hId : E (u - v) (u - v) + lam *
      (∫ x, (((u : SobolevData Ω).1 x) - ((v : SobolevData Ω).1 x)) ^ 2 ∂μ) = 0)
    (hInt : Integrable
      (fun x => (((u : SobolevData Ω).1 x) - ((v : SobolevData Ω).1 x)) ^ 2) μ)
    (hlam : 0 < lam) :
    ∀ᵐ x ∂μ, ((u : SobolevData Ω).1 x) = ((v : SobolevData Ω).1 x) := by
  let g : SpatialCoordinates d → ℝ :=
    fun x => ((u : SobolevData Ω).1 x) - ((v : SobolevData Ω).1 x)
  have hnonneg : 0 ≤ E (u - v) (u - v) := hE (u - v)
  have hmass : 0 ≤ ∫ x, g x ^ 2 ∂μ := by
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall (fun x => sq_nonneg (g x)))
  have hId' : E (u - v) (u - v) + lam * (∫ x, g x ^ 2 ∂μ) = 0 := by
    simpa [g] using hId
  have hmul : 0 ≤ lam * (∫ x, g x ^ 2 ∂μ) :=
    mul_nonneg hlam.le hmass
  have hzero : (∫ x, g x ^ 2 ∂μ) = 0 := by
    nlinarith [hId', hnonneg, hmul]
  have hsq := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => sq_nonneg (g x))) hInt).mp hzero
  filter_upwards [hsq] with x hx
  have hx0 : g x = 0 := sq_eq_zero_iff.mp hx
  dsimp [g] at hx0
  exact sub_eq_zero.mp hx0





theorem finite_speed_resolvent_killed_bridge
    {d : Nat} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : Nat → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : Nat → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (E : Nat → BilateralField d → SobolevData (centeredCube z r hr) →
      SobolevData (centeredCube z r hr) → ℝ)
    (hE : ∀ N omega u v, E N omega u v =
      sobolevCoefficientForm (Lane4.cutoffPositiveCoefficient M H omega N z hr) u v)
    (R : Nat → BilateralField d → ℝ → (SpatialCoordinates d → ℝ) → SpatialCoordinates d → ℝ)
    (hR : ∀ N omega lam f x, R N omega lam f x =
      ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Set.indicator {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
          (centeredCube z r hr : Set (SpatialCoordinates d)) path}
          (fun s => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
        ∂(KN N (omega, x)))
    (L : Nat → BilateralField d → (SpatialCoordinates d → ℝ) → SpatialCoordinates d → ℝ)
    (hL : ∀ N omega phi x, L N omega phi x =
      (cutoffSpeedDensity M H omega N x)⁻¹ * ∑ i : Fin d,
        (fderiv ℝ (fun y => cutoffCoefficient M H omega N y *
          (fderiv ℝ phi y) (Pi.single i 1)) x) (Pi.single i 1))
    (hstop :
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : Nat,
        ∀ (x : SpatialCoordinates d) (phi : SpatialCoordinates d → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) phi →
          HasCompactSupport phi →
          Function.support phi ⊆
            (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ t : ℝ≥0,
            ∫ path,
              (phi (path (ContinuousPath.exitTimeTrunc
                (centeredCube z r hr : Set (SpatialCoordinates d)) t path)) -
                phi x -
                ∫ s in Set.Icc (0 : ℝ)
                    ((ContinuousPath.exitTimeTrunc
                      (centeredCube z r hr : Set (SpatialCoordinates d)) t path) : ℝ),
                  L N omega phi (path (Real.toNNReal s)))
              ∂(KN N (omega, x)) = 0)
    (hSymm : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      SemigroupSymmetric (PN N omega) (cutoffSpeedMeasure M H omega N)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : Nat,
      (∀ (lam : ℝ), 0 < lam → ∀ (f : SpatialCoordinates d → ℝ), Measurable f →
        ∀ (B : ℝ), 0 ≤ B → (∀ x, |f x| ≤ B) →
        ∃ u : killedSobolevGraph (centeredCube z r hr),
          (∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
            ((u : SobolevData (centeredCube z r hr)).1) x = R N omega lam f x) ∧
          (∀ v : killedSobolevGraph (centeredCube z r hr),
            E N omega (u : SobolevData (centeredCube z r hr))
              (v : SobolevData (centeredCube z r hr)) =
            ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
              (f x - lam * ((u : SobolevData (centeredCube z r hr)).1) x) *
                ((v : SobolevData (centeredCube z r hr)).1) x
                ∂(cutoffSpeedMeasure M H omega N))) := by
  exact aux_fsrkb_main_check hd M H hH PN KN hKN hin z r hr E hE R hR L hL hstop hSymm

end Paper
