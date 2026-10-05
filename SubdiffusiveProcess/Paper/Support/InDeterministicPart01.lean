module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.ResponseMoments.Subdivision
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.EllipticRegularity.InDetCampanatoHolder
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.lane4_deterministic_iteration_input
public import SubdiffusiveProcess.Paper.primitive_scores
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.obl_ramp
public import SubdiffusiveProcess.Paper.in_deterministic_equal_scale_b12
public import SubdiffusiveProcess.Paper.in_deterministic_good_scale_transfer
public import SubdiffusiveProcess.Paper.in_deterministic_budget_assembly
public import SubdiffusiveProcess.Paper.in_deterministic_matrix_bounds
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.lem_primitive
public import SubdiffusiveProcess.Paper.coherent_score_attachment
public import SubdiffusiveProcess.Paper.in_deterministic_budget_transfer
public import Homogenization.Book.Ch02.Matrices
public import Homogenization.Book.Ch02.MultiscaleEllipticity
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import SubdiffusiveProcess.Paper.good_event
public import SubdiffusiveProcess.Paper.cell_catalogue
public import SubdiffusiveProcess.Paper.physical_scale_dictionary
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import SubdiffusiveProcess.Paper.lem_finite_trace_holder_beta_bound
public import SubdiffusiveProcess.VariationalResponses.CellAssembly
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Convolution
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import SubdiffusiveProcess.EllipticRegularity.InDetContHalf
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.PhysicalDatumRegularity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.DilationWeakEquation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.PhysicalDirichletCarrier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsCellTransport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.Corrector
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.AffineHarmonic
public import SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumRepresentative
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.Carrier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SmallContrastBallRescaling
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.PositiveRescaling
public import SubdiffusiveProcess.Sobolev.NativeH10
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorTransport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FractionalTransport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FractionalDatum
public import SubdiffusiveProcess.EllipticRegularity.InDetIterationWindow
public import SubdiffusiveProcess.Paper.prop_folded_iteration
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Data.Int.Interval
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerReduction
public import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJDeterministic
public import SubdiffusiveProcess.EllipticRegularity.InDetLowAlphaCont


@[expose] public section

/-!
Proof support for SubdiffusiveProcess.Paper.in_deterministic, part 1.
Supports: in_deterministic
-/

section InDetCoreChunk_InDetCore_Equation




open MeasureTheory Set Metric Filter Topology TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open Homogenization hiding Vec
open scoped ENNReal NNReal Pointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- The unit cube scaled by `3^J` is the origin cube `□_J`. -/
theorem aux_in_deterministic_core_originCube_eq_smul {d : ℕ} (J : ℤ) :
    openCubeSet (originCube d J) = ((3 : ℝ) ^ J) • openCubeSet (originCube d 0) := by
  rw [openCubeSet_originCube_eq_smul_originCube_zero (d := d) J, cubeScaleFactor_originCube]

/-- **Undilation of the scalar massive equation** from `□_J` to the unit cube `□_0`: the
coefficient becomes `c(3^J x)` and the source `3^{2J} f(3^J x)`. -/
theorem aux_in_deterministic_core_massive_undilate {d : ℕ} (J : ℤ) {c f : Vec d → ℝ}
    {u : H1Function (openCubeSet (originCube d J))}
    (hu : IsMassiveWeakSolutionOn c (fun _ => 1) 0 (openCubeSet (originCube d J)) u f) :
    IsMassiveWeakSolutionOn (fun x => c (((3 : ℝ) ^ J) • x)) (fun _ => 1) 0
      (openCubeSet (originCube d 0))
      (((3 : ℝ) ^ J) • u.undilateSet (zpow_pos (by norm_num : (0 : ℝ) < 3) J)
        (aux_in_deterministic_core_originCube_eq_smul J))
      (fun x => ((3 : ℝ) ^ J) ^ 2 * f (((3 : ℝ) ^ J) • x)) := by
  intro φ
  set R : ℝ := (3 : ℝ) ^ J with hRdef
  have hR : 0 < R := zpow_pos (by norm_num) J
  have hRne : R ≠ 0 := hR.ne'
  have hsc : centeredCubeScale J = R := rfl
  have h := hu (Section6Dirichlet.centeredCubeH10RawDilation J φ)
  simp only [zero_mul, zero_add, one_mul] at h ⊢
  set F : Vec d → ℝ := fun x =>
    vecDot (c x • u.grad x) ((Section6Dirichlet.centeredCubeH10RawDilation J φ).grad x)
    with hFdef
  set G : Vec d → ℝ := fun x =>
    f x * (Section6Dirichlet.centeredCubeH10RawDilation J φ).toFun x with hGdef
  have hS := aux_in_deterministic_core_originCube_eq_smul (d := d) J
  have h2 : ∫ x in ((3 : ℝ) ^ J) • openCubeSet (originCube d 0), F x ∂volume =
      ∫ x in ((3 : ℝ) ^ J) • openCubeSet (originCube d 0), G x ∂volume := by
    rw [← hS]; exact h
  rw [Homogenization.Book.Ch01.setIntegral_smul_set_eq_comp_smul_of_pos hR,
    Homogenization.Book.Ch01.setIntegral_smul_set_eq_comp_smul_of_pos hR] at h2
  clear h
  have h := h2
  simp only [hFdef, hGdef] at h
  simp only [Section6Dirichlet.centeredCubeH10RawDilation_toFun,
    Section6Dirichlet.centeredCubeH10RawDilation_grad, hsc, smul_smul,
    inv_mul_cancel₀ hRne, one_smul, smul_eq_mul] at h
  simp only [H1Function.smul_grad, H1Function.undilateSet_grad]
  have hL' : ∀ x : Vec d, vecDot (c (R • x) • (R • u.grad (R • x))) (φ.toH1Function.grad x) =
      R ^ 2 * vecDot (c (R • x) • u.grad (R • x)) (R⁻¹ • φ.toH1Function.grad x) := by
    intro x
    rw [Homogenization.vecDot_smul_right, Homogenization.vecDot_smul_left,
      Homogenization.vecDot_smul_left, Homogenization.vecDot_smul_left]
    field_simp
  have hRd : R ^ d ≠ 0 := pow_ne_zero d hRne
  have h' : ∫ x in openCubeSet (originCube d 0),
      vecDot (c (R • x) • u.grad (R • x)) (R⁻¹ • φ.toH1Function.grad x) ∂volume =
      ∫ x in openCubeSet (originCube d 0), f (R • x) * φ.toH1Function.toFun x ∂volume := by
    have := congrArg (fun t => (R ^ d)⁻¹ * t) h
    simpa only [← mul_assoc, inv_mul_cancel₀ hRd, one_mul] using this
  calc ∫ x in openCubeSet (originCube d 0),
        vecDot (c (R • x) • (R • u.grad (R • x))) (φ.toH1Function.grad x) ∂volume
      = ∫ x in openCubeSet (originCube d 0),
          R ^ 2 * vecDot (c (R • x) • u.grad (R • x)) (R⁻¹ • φ.toH1Function.grad x) ∂volume :=
        integral_congr_ae (Filter.Eventually.of_forall hL')
    _ = R ^ 2 * ∫ x in openCubeSet (originCube d 0),
          f (R • x) * φ.toH1Function.toFun x ∂volume := by rw [integral_const_mul, h']
    _ = ∫ x in openCubeSet (originCube d 0),
          R ^ 2 * f (R • x) * φ.toH1Function.toFun x ∂volume := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

end SubdiffusiveProcess.Paper
end
end InDetCoreChunk_InDetCore_Equation

section InDetCoreChunk_InDetCore_Transport




open MeasureTheory Set Metric Filter Topology TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open Homogenization hiding Vec
open scoped ENNReal NNReal Pointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- Coefficient congruence for the scalar massive equation. -/
theorem aux_in_deterministic_core_massive_congr_coeff {d : ℕ} {W : Set (Vec d)}
    {c c' : Vec d → ℝ} (hcc : c =ᵐ[volume.restrict W] c') {u : H1Function W} {f : Vec d → ℝ}
    (h : IsMassiveWeakSolutionOn c (fun _ => 1) 0 W u f) :
    IsMassiveWeakSolutionOn c' (fun _ => 1) 0 W u f := by
  intro φ
  rw [← h φ]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hcc] with x hx
  rw [hx]

/-- The scalar massive equation (`ρ = 1`, `μ = 0`) is the scalar right-hand-side equation. -/
theorem aux_in_deterministic_core_scalarRhs_of_massive {d : ℕ} {W : Set (Vec d)}
    {c : Vec d → ℝ} {u : H1Function W} {f : Vec d → ℝ}
    (h : IsMassiveWeakSolutionOn c (fun _ => 1) 0 W u f) :
    IsScalarRhsWeakSolutionOn (scalarCoeffField c) W u f := by
  intro φ
  have h1 := h φ
  simp only [zero_mul, zero_add, one_mul] at h1
  rw [← h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [scalarCoeffField, matVecMul_scalarMatrix]

/-- `L²` norm under a dilation of the domain. -/
theorem aux_in_deterministic_core_eLpNorm_comp_smul {d : ℕ} {R : ℝ} (hR : 0 < R)
    (U : Set (Vec d)) (g : Vec d → ℝ)
    (hg : AEStronglyMeasurable g (volume.restrict (R • U))) :
    eLpNorm (fun x => g (R • x)) 2 (volume.restrict U) =
      ENNReal.ofReal ((R ^ d)⁻¹) ^ (1 / 2 : ℝ) * eLpNorm g 2 (volume.restrict (R • U)) := by
  have hmap := map_smul_volume_restrict (d := d) hR U
  have hT : AEMeasurable (fun x : Vec d => R • x) (volume.restrict U) :=
    (measurable_const_smul R).aemeasurable
  have hg' : AEStronglyMeasurable g (Measure.map (fun x : Vec d => R • x) (volume.restrict U)) := by
    rw [hmap]; exact hg.smul_measure _
  have h1 := eLpNorm_map_measure hg' hT (p := 2)
  rw [hmap, eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) g _ hg] at h1
  rw [show (fun x => g (R • x)) = g ∘ (fun x : Vec d => R • x) from rfl, ← h1, smul_eq_mul]
  congr 2
  norm_num

/-- `L²` membership under a dilation of the domain. -/
theorem aux_in_deterministic_core_memLp_comp_smul {d : ℕ} {R : ℝ} (hR : 0 < R)
    (U : Set (Vec d)) (g : Vec d → ℝ) (hg : MemLp g 2 (volume.restrict (R • U))) :
    MemLp (fun x => g (R • x)) 2 (volume.restrict U) := by
  have hmap := map_smul_volume_restrict (d := d) hR U
  have hT : AEMeasurable (fun x : Vec d => R • x) (volume.restrict U) :=
    (measurable_const_smul R).aemeasurable
  have hg' : MemLp g 2 (Measure.map (fun x : Vec d => R • x) (volume.restrict U)) := by
    rw [hmap]; exact hg.smul_measure ENNReal.ofReal_ne_top
  exact (memLp_map_measure_iff hg'.aestronglyMeasurable hT).1 hg'

/-- The transport statement with lift constant `C`. -/
def aux_in_deterministic_core_transport_prop (d : ℕ) [NeZero d] (C : ℝ) : Prop :=
    ∀ {Ω : Opens (SpatialCoordinates d)} (A : PositiveCoefficient Ω)
      (a : SpatialCoordinates d → ℝ),
    ((A.val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] a) →
    ∀ (f : SpatialCoordinates d → ℝ) (fL2 : DomainL2 Ω),
    ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] f) →
    ∀ u : weakSobolevGraph Ω,
    (∀ psi : killedSobolevGraph Ω,
      sobolevCoefficientForm A (u : SobolevData Ω) (psi : SobolevData Ω) =
        sobolevVolumeLoad fL2 (psi : SobolevData Ω)) →
    ∀ (w : SpatialCoordinates d) (J m : ℤ),
    Metric.ball w ((3 : ℝ) ^ J / 2) ⊆ (Ω : Set (SpatialCoordinates d)) →
    MemLp f 2 (volume.restrict (Metric.ball w ((3 : ℝ) ^ J / 2))) →
    ∃ (v : H1Function (openCubeSet (originCube d m)))
      (F : CubeVectorH1Function (originCube d 0)),
      (∀ y, v.toFun y = ((u : SobolevData Ω).1 : SpatialCoordinates d → ℝ)
          (((3 : ℝ) ^ J) • (((3 : ℝ) ^ m)⁻¹ • y) + w)) ∧
      IsDivFormWeakSolutionOn (fun y => a (((3 : ℝ) ^ J) • (((3 : ℝ) ^ m)⁻¹ • y) + w))
        (openCubeSet (originCube d m)) v
        (Section6Dirichlet.centeredCubeScaledVectorDilation 1 m F).toField ∧
      Section6Dirichlet.unitCubeVectorH1ENormBudget F ≤
        ENNReal.ofReal (C * (((3 : ℝ) ^ J) ^ 2 * Real.sqrt ((((3 : ℝ) ^ J) ^ d)⁻¹) *
          (eLpNorm f 2 (volume.restrict (Metric.ball w ((3 : ℝ) ^ J / 2)))).toReal))

/-- **The transport.** -/
theorem aux_in_deterministic_core_transport (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ aux_in_deterministic_core_transport_prop d C := by
  obtain ⟨C, hC, hlift⟩ :=
    Section6Dirichlet.exists_unitCubeVectorH1Function_divergence_lift_h1ENormBudget d
  refine ⟨C, hC, ?_⟩
  unfold aux_in_deterministic_core_transport_prop
  intro Ω A a ha f fL2 hfL2 u hu w J m hball hf2
  have hR : 0 < (3 : ℝ) ^ J := zpow_pos (by norm_num) J
  obtain ⟨v, hv, hvg⟩ := exists_nativeH1Function_of_weakSobolevGraph u
  have hm := aux_in_deterministic_regularity_massive_of_native A f fL2 hfL2 u hu v hv hvg
  have hm' := aux_in_deterministic_core_massive_congr_coeff ha hm
  have hVball : translateSet w (openCubeSet (originCube d J)) =
      Metric.ball w ((3 : ℝ) ^ J / 2) :=
    aux_in_deterministic_regularity_translateSet_eq_ball w J
  have hVo : IsOpen (translateSet w (openCubeSet (originCube d J))) := by
    rw [hVball]; exact Metric.isOpen_ball
  have hVΩ : translateSet w (openCubeSet (originCube d J)) ⊆ (Ω : Set (SpatialCoordinates d)) := by
    rw [hVball]; exact hball
  have hmV := aux_in_deterministic_regularity_massive_restrict Ω.isOpen hVo hVΩ hm'
  have hmJ := isMassiveWeakSolutionOn_untranslate w (v.restrict hVo hVΩ) hmV
  have hm1 := aux_in_deterministic_core_massive_undilate J hmJ
  have hs1 := aux_in_deterministic_core_scalarRhs_of_massive hm1
  -- the source on the unit cube
  have hfV : MemLp f 2 (volume.restrict (translateSet w (openCubeSet (originCube d J)))) := by
    rw [hVball]; exact hf2
  have hfJ : MemLp (fun x => f (x + w)) 2 (volume.restrict (openCubeSet (originCube d J))) :=
    hfV.comp_measurePreserving (measurePreserving_addRight_restrict_translateSet w _)
  have hfJ' : MemLp (fun x => f (x + w)) 2
      (volume.restrict (((3 : ℝ) ^ J) • openCubeSet (originCube d 0))) := by
    rw [← aux_in_deterministic_core_originCube_eq_smul J]; exact hfJ
  have hf1mem : MemLp (fun x => ((3 : ℝ) ^ J) ^ 2 * f (((3 : ℝ) ^ J) • x + w)) 2
      (volume.restrict (openCubeSet (originCube d 0))) :=
    (aux_in_deterministic_core_memLp_comp_smul hR _ (fun y => f (y + w)) hfJ').const_mul _
  obtain ⟨F, hpair, hbudget⟩ := hlift _ hf1mem
  have hcoef : (fun x : Vec d => (fun x => a (x + w)) (((3 : ℝ) ^ J) • x)) =
      fun x => (1 : ℝ)⁻¹ *
        (fun y : Vec d => a (((3 : ℝ) ^ J) • (((3 : ℝ) ^ m)⁻¹ • y) + w))
          (centeredCubeScale m • x) := by
    funext x
    simp only [inv_one, one_mul, centeredCubeScale, smul_smul,
      inv_mul_cancel₀ (zpow_ne_zero m (by norm_num : (3 : ℝ) ≠ 0)), one_smul]
  rw [hcoef] at hs1
  have hdiv := Section6Dirichlet.isDivFormWeakSolutionOn_centeredCubeRawDilation m one_pos
    (fun y : Vec d => a (((3 : ℝ) ^ J) • (((3 : ℝ) ^ m)⁻¹ • y) + w)) F hs1 hpair
  refine ⟨_, F, ?_, hdiv, ?_⟩
  · intro y
    simp only [Section6Dirichlet.centeredCubeRawDilation_toFun, H1Function.smul_toFun,
      H1Function.undilateSet_toFun, H1Function.untranslate_toFun]
    rw [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]
    change v.toFun _ = _
    rw [hv]
    rfl
  · refine hbudget.trans (ENNReal.ofReal_le_ofReal ?_)
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) hC
    have hnorm : ‖toScalarL2 hf1mem‖ =
        (eLpNorm (fun x => ((3 : ℝ) ^ J) ^ 2 * f (((3 : ℝ) ^ J) • x + w)) 2
          (volume.restrict (openCubeSet (originCube d 0)))).toReal := by
      simp [toScalarL2, Lp.norm_toLp, volumeMeasureOn]
    rw [hnorm]
    have hmeas : AEStronglyMeasurable (fun x => f (x + w))
        (volume.restrict (((3 : ℝ) ^ J) • openCubeSet (originCube d 0))) := hfJ'.aestronglyMeasurable
    have e1 : eLpNorm (fun x => ((3 : ℝ) ^ J) ^ 2 * f (((3 : ℝ) ^ J) • x + w)) 2
        (volume.restrict (openCubeSet (originCube d 0))) =
        ENNReal.ofReal (((3 : ℝ) ^ J) ^ 2) * (ENNReal.ofReal ((((3 : ℝ) ^ J) ^ d)⁻¹) ^ (1 / 2 : ℝ) *
          eLpNorm (fun x => f (x + w)) 2
            (volume.restrict (((3 : ℝ) ^ J) • openCubeSet (originCube d 0)))) := by
      rw [show (fun x => ((3 : ℝ) ^ J) ^ 2 * f (((3 : ℝ) ^ J) • x + w)) =
          ((3 : ℝ) ^ J) ^ 2 • (fun x => (fun y => f (y + w)) (((3 : ℝ) ^ J) • x)) from rfl,
        eLpNorm_const_smul, aux_in_deterministic_core_eLpNorm_comp_smul hR _ _ hmeas]
      congr 1
      rw [Real.enorm_eq_ofReal (by positivity)]
    have e2 : eLpNorm (fun x => f (x + w)) 2
        (volume.restrict (((3 : ℝ) ^ J) • openCubeSet (originCube d 0))) =
        eLpNorm f 2 (volume.restrict (Metric.ball w ((3 : ℝ) ^ J / 2))) := by
      rw [← aux_in_deterministic_core_originCube_eq_smul J, ← hVball]
      exact eLpNorm_comp_measurePreserving hfV.aestronglyMeasurable
        (measurePreserving_addRight_restrict_translateSet w _)
    rw [e1, e2, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (by positivity), ← Real.sqrt_eq_rpow]
    ring

end SubdiffusiveProcess.Paper
end
end InDetCoreChunk_InDetCore_Transport

section InDetCoreChunk_InDetCore_BoundaryHarmonic

/-!
# Boundary-continuous harmonic replacement on a cube 

For an `H¹` datum `uD` on the open cube `K = c + Q_h` which agrees a.e. with a function `Ũ`
continuous on a neighbourhood of `closure K`, the Laplace-harmonic replacement `v` of `uD`
(`v - uD ∈ H¹₀(K)`) has a representative continuous on `closure K` and equal to `Ũ` on
`∂K`.  Route: smooth uniform approximations `φ_k` of `Ũ` (mollification); the harmonic
replacements `v_k` of `φ_k` are continuous up to the boundary with boundary values `φ_k`
(`lane2_cellDirichletBoundaryContinuity`, coefficient `1`); the weak maximum principle (GMC,
with the globally clamped datum) makes them uniformly Cauchy and `v - v_k` uniformly small.
-/

open MeasureTheory Set Metric Filter Topology TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum
open Homogenization hiding Vec
open scoped ENNReal NNReal ContDiff Convolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- Re-basing a zero-trace witness on an a.e.-equal value function (same gradient). -/
def aux_in_deterministic_core_H10_ofAEEq {d : ℕ} {K : Set (Vec d)} (ρ : H10Function K)
    (g : Vec d → ℝ) (hg : g =ᵐ[volume.restrict K] ρ.toH1Function.toFun) : H10Function K where
  toH1Function := Section8Resolvent.H1Function.ofAEEq ρ.toH1Function g hg
  approx := ρ.approx
  approx_smooth := ρ.approx_smooth
  approx_hasCompactSupport := ρ.approx_hasCompactSupport
  approx_support_subset := ρ.approx_support_subset
  tendsto_approx := by
    refine ρ.tendsto_approx.congr (fun n => ?_)
    refine eLpNorm_congr_ae ?_
    filter_upwards [hg] with x hx
    simp [hx]
  tendsto_approx_grad := ρ.tendsto_approx_grad

@[simp] theorem aux_in_deterministic_core_H10_ofAEEq_toFun {d : ℕ} {K : Set (Vec d)}
    (ρ : H10Function K) (g : Vec d → ℝ) (hg : g =ᵐ[volume.restrict K] ρ.toH1Function.toFun) :
    (aux_in_deterministic_core_H10_ofAEEq ρ g hg).toH1Function.toFun = g := rfl

@[simp] theorem aux_in_deterministic_core_H10_ofAEEq_grad {d : ℕ} {K : Set (Vec d)}
    (ρ : H10Function K) (g : Vec d → ℝ) (hg : g =ᵐ[volume.restrict K] ρ.toH1Function.toFun) :
    (aux_in_deterministic_core_H10_ofAEEq ρ g hg).toH1Function.grad = ρ.toH1Function.grad := rfl

/-- `H¹₀` membership only sees the function a.e. on the domain. -/
theorem aux_in_deterministic_core_memH10_congr {d : ℕ} {K : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : MemH10 K f) (hfg : f =ᵐ[volume.restrict K] g) : MemH10 K g := by
  obtain ⟨ρ, hρ⟩ := hf
  have hv : g =ᵐ[volume.restrict K] ρ.toH1Function.toFun := by rw [hρ]; exact hfg.symm
  exact ⟨aux_in_deterministic_core_H10_ofAEEq ρ g hv, rfl⟩

/-- **Two-sided weak maximum principle with a datum bounded only on the domain.** -/
theorem aux_in_deterministic_core_harmonic_abs_le {d : ℕ} [NeZero d] {K : Set (Vec d)}
    (hK : IsOpenBoundedConvexDomain K) {w Φ : H1Function K}
    (hw : IsWeaklyHarmonicOn (fun _ => (1 : ℝ)) K w)
    (hdiff : MemH10 K (fun y => w.toFun y - Φ.toFun y)) {M : ℝ} (hM : 0 ≤ M)
    (hΦ : ∀ y ∈ K, |Φ.toFun y| ≤ M) :
    ∀ᵐ y ∂(volume.restrict K), |w.toFun y| ≤ M := by
  obtain ⟨Ψ, hΨu, hΨl, hΨeq⟩ := exists_h1_clamp hK Φ hM
  have hdiff' : MemH10 K (fun y => w.toFun y - Ψ.toFun y) := by
    refine aux_in_deterministic_core_memH10_congr hdiff ?_
    filter_upwards [ae_restrict_mem hK.isOpen.measurableSet] with y hy
    rw [hΨeq y (hΦ y hy)]
  have hup : HasBoundaryUpperBoundOn K w M := hasBoundaryUpperBoundOn_of_datum_le hK hdiff' hΨu
  have hdiffneg : MemH10 K (fun y => (-w).toFun y - (-Ψ).toFun y) := by
    have h := Homogenization.memH10_neg hdiff'
    have hfun : (fun y => -(w.toFun y - Ψ.toFun y)) =
        fun y => (-w).toFun y - (-Ψ).toFun y := by
      funext y
      rw [Homogenization.H1Function.neg_toFun, Homogenization.H1Function.neg_toFun]
      ring
    rwa [hfun] at h
  have hlow : HasBoundaryUpperBoundOn K (-w) M :=
    hasBoundaryUpperBoundOn_of_datum_le hK hdiffneg fun y => by
      rw [Homogenization.H1Function.neg_toFun]; linarith [hΨl y]
  exact ae_abs_le_of_isUnitWeaklyHarmonicOn hK
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.isUnitWeaklyHarmonicOn_iff.2 hw) hup hlow

/-- An a.e. bound on an open set propagates, by continuity, to its closure. -/
theorem aux_in_deterministic_core_abs_le_closure {d : ℕ} {K : Set (Vec d)} (hK : IsOpen K)
    {g : Vec d → ℝ} (hg : ContinuousOn g (closure K)) {M : ℝ} (hM : 0 ≤ M)
    (hae : ∀ᵐ y ∂(volume.restrict K), |g y| ≤ M) : ∀ y ∈ closure K, |g y| ≤ M := by
  set g' : Vec d → ℝ := fun y => max (-M) (min M (g y)) with hg'def
  have hgK : ContinuousOn g K := hg.mono subset_closure
  have hg'K : ContinuousOn g' K :=
    (continuous_const.max (continuous_const.min continuous_id)).comp_continuousOn hgK
  have hae' : g =ᵐ[volume.restrict K] g' := by
    filter_upwards [hae] with y hy
    rw [abs_le] at hy
    simp only [hg'def]
    rw [min_eq_right hy.2, max_eq_right hy.1]
  have heq := Measure.eqOn_open_of_ae_eq hae' hK hgK hg'K
  have hK' : K ⊆ closure K ∩ g ⁻¹' {t | |t| ≤ M} := by
    intro y hy
    refine ⟨subset_closure hy, ?_⟩
    show |g y| ≤ M
    rw [heq hy]
    simp only [hg'def]
    rw [abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have hclosed : IsClosed (closure K ∩ g ⁻¹' {t | |t| ≤ M}) :=
    hg.preimage_isClosed_of_isClosed isClosed_closure
      (isClosed_le continuous_abs continuous_const)
  intro y hy
  exact (closure_minimal hK' hclosed hy).2

open scoped Convolution in
/-- Smooth uniform approximations on a compact set of a function continuous on a
neighbourhood. -/
theorem aux_in_deterministic_core_smooth_approx {d : ℕ} {S O : Set (Vec d)} (hS : IsCompact S)
    (hO : IsOpen O) (hSO : S ⊆ O) (Ũ : Vec d → ℝ) (hŨ : ContinuousOn Ũ O) :
    ∃ φ : ℕ → Vec d → ℝ, (∀ k, ContDiff ℝ ∞ (φ k)) ∧
      ∀ k, ∀ x ∈ S, |φ k x - Ũ x| ≤ 1 / ((k : ℝ) + 1) := by
  obtain ⟨δ, hδ, hδO⟩ := hS.exists_cthickening_subset_open hO hSO
  set T : Set (Vec d) := cthickening δ S with hTdef
  have hTc : IsCompact T := hS.cthickening
  set g : Vec d → ℝ := T.indicator Ũ with hgdef
  have hgT : ContinuousOn g T :=
    (hŨ.mono hδO).congr (fun y hy => Set.indicator_of_mem hy _)
  have hgint : Integrable g volume :=
    (integrable_indicator_iff hTc.measurableSet).2
      ((hŨ.mono hδO).integrableOn_compact hTc)
  let ψ : ℕ → ContDiffBump (0 : Vec d) := fun n =>
    ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity, by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [(Nat.cast_add_one_pos n : (0 : ℝ) < (n : ℝ) + 1)]⟩
  have hψ : Tendsto (fun n => (ψ n).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set F : ℕ → Vec d → ℝ := fun n =>
    (ψ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g with hFdef
  have hFs : ∀ n, ContDiff ℝ ∞ (F n) := fun n =>
    (ψ n).hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (ψ n).contDiff_normed hgint.locallyIntegrable
  have hunif : TendstoUniformlyOn F g atTop S := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have huc : UniformContinuousOn g T := hTc.uniformContinuousOn_of_continuous hgT
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨η, hη_pos, hη⟩ := huc (ε / 2) (by linarith)
    have hlt : (0 : ℝ) < min δ η := lt_min hδ hη_pos
    filter_upwards [hψ.eventually_lt_const hlt] with n hn
    intro x₀ hx₀
    have hx₀C : x₀ ∈ T := Metric.self_subset_cthickening S hx₀
    have hbound : ∀ x ∈ Metric.ball x₀ (ψ n).rOut, dist (g x) (g x₀) ≤ ε / 2 := by
      intro x hx
      rw [Metric.mem_ball] at hx
      have hxδ : dist x x₀ ≤ δ :=
        le_of_lt (lt_of_lt_of_le (lt_trans hx hn) (min_le_left δ η))
      have hxC : x ∈ T := Metric.mem_cthickening_of_dist_le x x₀ δ S hx₀ hxδ
      have hxη : dist x x₀ < η :=
        lt_of_lt_of_le (lt_trans hx hn) (min_le_right δ η)
      exact le_of_lt (hη x hxC x₀ hx₀C hxη)
    have hmain := ContDiffBump.dist_normed_convolution_le (φ := ψ n)
      hgint.aestronglyMeasurable hbound
    rw [dist_comm]
    exact lt_of_le_of_lt hmain (by linarith)
  have hk : ∀ k : ℕ, ∃ n, ∀ x ∈ S, dist (g x) (F n x) < 1 / ((k : ℝ) + 1) := fun k =>
    (Metric.tendstoUniformlyOn_iff.1 hunif _ (by positivity)).exists
  choose n hn using hk
  refine ⟨fun k => F (n k), fun k => hFs (n k), fun k x hx => ?_⟩
  have h1 := hn k x hx
  have hgx : g x = Ũ x := Set.indicator_of_mem (Metric.self_subset_cthickening S hx) _
  rw [hgx, Real.dist_eq, abs_sub_comm] at h1
  exact h1.le

/-- Convergence from an explicit `1/(k+1)` rate. -/
theorem aux_in_deterministic_core_tendsto_of_abs_le {a : ℕ → ℝ} {L : ℝ}
    (h : ∀ k : ℕ, |a k - L| ≤ 1 / ((k : ℝ) + 1)) : Tendsto a atTop (𝓝 L) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  rw [Real.norm_eq_abs]
  exact h k

/-- **Boundary-continuous harmonic replacement** on the cube `K = ball z (h/2)` (sup metric). -/
theorem aux_in_deterministic_core_boundary_harmonic {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (z : Vec d) (h : ℝ) (hh : 0 < h) {O : Set (Vec d)} (hO : IsOpen O)
    (hKO : closure (Metric.ball z (h / 2)) ⊆ O)
    (Ũ : Vec d → ℝ) (hŨ : ContinuousOn Ũ O)
    (uD : H1Function (Metric.ball z (h / 2)))
    (huD : uD.toFun =ᵐ[volume.restrict (Metric.ball z (h / 2))] Ũ) :
    ∃ v : H1Function (Metric.ball z (h / 2)),
      IsWeaklyHarmonicOn (fun _ => (1 : ℝ)) (Metric.ball z (h / 2)) v ∧
      HasZeroTraceDifferenceOn (Metric.ball z (h / 2)) v uD ∧
      ∃ V : Vec d → ℝ, ContinuousOn V (closure (Metric.ball z (h / 2))) ∧
        V =ᵐ[volume.restrict (Metric.ball z (h / 2))] v.toFun ∧
        ∀ x ∈ frontier (Metric.ball z (h / 2)), V x = Ũ x := by
  have hKc : IsOpenBoundedConvexDomain (Metric.ball z (h / 2)) :=
    isOpenBoundedConvexDomain_ball z (half_pos hh)
  have hKo : IsOpen (Metric.ball z (h / 2)) := Metric.isOpen_ball
  have hne : (Metric.ball z (h / 2)).Nonempty := ⟨z, Metric.mem_ball_self (half_pos hh)⟩
  have hcl : IsCompact (closure (Metric.ball z (h / 2))) :=
    (Metric.isBounded_ball).isCompact_closure
  obtain ⟨φ, hφs, hφb⟩ := aux_in_deterministic_core_smooth_approx hcl hO hKO Ũ hŨ
  let Φ : ℕ → H1Function (Metric.ball z (h / 2)) := fun k =>
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain hKc ((hφs k).of_le (by simp))
  have hΦf : ∀ k, (Φ k).toFun = φ k := fun k => rfl
  have hex : ∀ k, ∃ vk : H1Function (Metric.ball z (h / 2)),
      IsWeaklyHarmonicOn (fun _ => (1 : ℝ)) (Metric.ball z (h / 2)) vk ∧
      HasZeroTraceDifferenceOn (Metric.ball z (h / 2)) vk (Φ k) := fun k =>
    exists_isWeaklyHarmonicOn_one_and_hasZeroTraceDifferenceOn hKc hne (Φ k)
  choose vk hvkH hvkZ using hex
  have hcont := (lane2_cellDirichletBoundaryContinuity (d := d) hd).continuous_up_to_boundary
  have hVex : ∀ k, ∃ V : Vec d → ℝ, ContinuousOn V (closure (Metric.ball z (h / 2))) ∧
      V =ᵐ[volume.restrict (Metric.ball z (h / 2))] (vk k).toFun ∧
      ∀ x ∈ frontier (Metric.ball z (h / 2)), V x = φ k x := by
    intro k
    obtain ⟨V, h1, h2, h3⟩ := hcont z h hh (fun _ => 1) 1 1 one_pos continuous_const
      (fun _ _ => ⟨le_rfl, le_rfl⟩) (Φ k) (vk k) (by rw [hΦf]; exact hφs k) (hvkH k) (hvkZ k)
    exact ⟨V, h1, h2, fun x hx => by rw [h3 x hx, hΦf]⟩
  choose V hVc hVae hVfr using hVex
  have hZ : ∀ k, ∃ ρ : H10Function (Metric.ball z (h / 2)),
      ∀ x, (vk k).toFun x = φ k x + ρ.toH1Function.toFun x := fun k => by
    obtain ⟨ρ, h1, -⟩ := hvkZ k
    exact ⟨ρ, fun x => by rw [h1 x, hΦf]⟩
  choose ρ hρf using hZ
  have hunit : ∀ {w : H1Function (Metric.ball z (h / 2))},
      IsWeaklyHarmonicOn (fun _ => (1 : ℝ)) (Metric.ball z (h / 2)) w →
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.IsUnitWeaklyHarmonicOn (Metric.ball z (h / 2)) w :=
    fun hw => SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.isUnitWeaklyHarmonicOn_iff.2 hw
  -- pairwise closeness of the continuous representatives
  have hpair : ∀ j k, ∀ y ∈ closure (Metric.ball z (h / 2)),
      |V j y - V k y| ≤ 1 / ((j : ℝ) + 1) + 1 / ((k : ℝ) + 1) := by
    intro j k
    have hw : IsWeaklyHarmonicOn (fun _ => (1 : ℝ)) (Metric.ball z (h / 2)) (vk j - vk k) :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.isUnitWeaklyHarmonicOn_iff.1
        (isUnitWeaklyHarmonicOn_sub (hunit (hvkH j)) (hunit (hvkH k)))
    have hfun : (fun y => (vk j - vk k).toFun y - (Φ j - Φ k).toFun y) =
        fun y => (ρ j).toH1Function.toFun y - (ρ k).toH1Function.toFun y := by
      funext y
      simp only [H1Function.sub_toFun]
      rw [hρf j y, hρf k y, hΦf, hΦf]
      ring
    have hdiff : MemH10 (Metric.ball z (h / 2))
        (fun y => (vk j - vk k).toFun y - (Φ j - Φ k).toFun y) := by
      rw [hfun]; exact Homogenization.memH10_sub ⟨ρ j, rfl⟩ ⟨ρ k, rfl⟩
    have hM : (0 : ℝ) ≤ 1 / ((j : ℝ) + 1) + 1 / ((k : ℝ) + 1) := by positivity
    have hae := aux_in_deterministic_core_harmonic_abs_le hKc hw hdiff hM (fun y hy => by
      simp only [H1Function.sub_toFun]
      rw [hΦf, hΦf]
      have h1 := hφb j y (subset_closure hy)
      have h2 := hφb k y (subset_closure hy)
      calc |φ j y - φ k y| = |(φ j y - Ũ y) - (φ k y - Ũ y)| := by ring_nf
        _ ≤ |φ j y - Ũ y| + |φ k y - Ũ y| := abs_sub _ _
        _ ≤ _ := add_le_add h1 h2)
    have hae' : ∀ᵐ y ∂volume.restrict (Metric.ball z (h / 2)),
        |V j y - V k y| ≤ 1 / ((j : ℝ) + 1) + 1 / ((k : ℝ) + 1) := by
      filter_upwards [hae, hVae j, hVae k] with y hy h1 h2
      rw [h1, h2]
      simpa only [H1Function.sub_toFun] using hy
    exact aux_in_deterministic_core_abs_le_closure hKo ((hVc j).sub (hVc k)) hM hae'
  -- the uniform limit
  have hCauchy : ∀ y ∈ closure (Metric.ball z (h / 2)), CauchySeq (fun k => V k y) := by
    intro y hy
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hnN : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hn 1
    calc |V n y - V N y| ≤ 1 / ((n : ℝ) + 1) + 1 / ((N : ℝ) + 1) := hpair n N y hy
      _ ≤ 1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) := by
          gcongr
      _ = 2 / ((N : ℝ) + 1) := by ring
      _ < ε := by
          rw [div_lt_iff₀ hN1]
          rw [div_lt_iff₀ hε] at hN
          nlinarith
  set Vlim : Vec d → ℝ := fun y => limUnder atTop (fun k => V k y) with hVdef
  have hlim : ∀ y ∈ closure (Metric.ball z (h / 2)),
      Tendsto (fun k => V k y) atTop (𝓝 (Vlim y)) := fun y hy => (hCauchy y hy).tendsto_limUnder
  have hrate : ∀ k, ∀ y ∈ closure (Metric.ball z (h / 2)),
      |V k y - Vlim y| ≤ 1 / ((k : ℝ) + 1) := by
    intro k y hy
    have hf : Tendsto (fun j => |V k y - V j y|) atTop (𝓝 (|V k y - Vlim y|)) :=
      ((continuous_abs.comp (continuous_const.sub continuous_id)).tendsto _).comp (hlim y hy)
    have hg : Tendsto (fun j : ℕ => 1 / ((k : ℝ) + 1) + 1 / ((j : ℝ) + 1)) atTop
        (𝓝 (1 / ((k : ℝ) + 1) + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    have := le_of_tendsto_of_tendsto' hf hg (fun j => hpair k j y hy)
    simpa using this
  have hunif : TendstoUniformlyOn V Vlim atTop (closure (Metric.ball z (h / 2))) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    filter_upwards [Filter.eventually_ge_atTop N] with k hk y hy
    rw [dist_comm, Real.dist_eq]
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    calc |V k y - Vlim y| ≤ 1 / ((k : ℝ) + 1) := hrate k y hy
      _ < ε := by
          rw [div_lt_iff₀ hk1]
          rw [div_lt_iff₀ hε] at hN
          have : (N : ℝ) ≤ k := by exact_mod_cast hk
          nlinarith
  have hVclim : ContinuousOn Vlim (closure (Metric.ball z (h / 2))) :=
    hunif.continuousOn (Filter.Eventually.of_forall hVc).frequently
  have hfr : ∀ x ∈ frontier (Metric.ball z (h / 2)), Vlim x = Ũ x := by
    intro x hx
    have hxc : x ∈ closure (Metric.ball z (h / 2)) := frontier_subset_closure hx
    have h2 : Tendsto (fun k => V k x) atTop (𝓝 (Ũ x)) := by
      refine aux_in_deterministic_core_tendsto_of_abs_le (fun k => ?_)
      rw [hVfr k x hx]
      exact hφb k x hxc
    exact tendsto_nhds_unique (hlim x hxc) h2
  -- the harmonic replacement of the datum
  let uD' : H1Function (Metric.ball z (h / 2)) :=
    Section8Resolvent.H1Function.ofAEEq uD Ũ huD.symm
  obtain ⟨v, hvH, hvZ⟩ := exists_isWeaklyHarmonicOn_one_and_hasZeroTraceDifferenceOn hKc hne uD'
  obtain ⟨σ, hσf, hσg⟩ := hvZ
  have hZD : HasZeroTraceDifferenceOn (Metric.ball z (h / 2)) v uD := by
    have hg : (fun x => v.toFun x - uD.toFun x) =ᵐ[volume.restrict (Metric.ball z (h / 2))]
        σ.toH1Function.toFun := by
      filter_upwards [huD] with x hx
      rw [hσf x]
      change Ũ x + σ.toH1Function.toFun x - uD.toFun x = _
      rw [hx]
      ring
    refine ⟨aux_in_deterministic_core_H10_ofAEEq σ (fun x => v.toFun x - uD.toFun x) hg,
      fun x => ?_, fun x => ?_⟩
    · change v.toFun x = uD.toFun x + (v.toFun x - uD.toFun x)
      ring
    · change v.grad x = uD.grad x + σ.toH1Function.grad x
      rw [hσg x]
      rfl
  have hvk : ∀ k, ∀ᵐ y ∂volume.restrict (Metric.ball z (h / 2)),
      |v.toFun y - (vk k).toFun y| ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    have hw : IsWeaklyHarmonicOn (fun _ => (1 : ℝ)) (Metric.ball z (h / 2)) (v - vk k) :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.isUnitWeaklyHarmonicOn_iff.1
        (isUnitWeaklyHarmonicOn_sub (hunit hvH) (hunit (hvkH k)))
    have hfun : (fun y => (v - vk k).toFun y - (uD' - Φ k).toFun y) =
        fun y => σ.toH1Function.toFun y - (ρ k).toH1Function.toFun y := by
      funext y
      simp only [H1Function.sub_toFun]
      rw [hσf y, hρf k y, hΦf]
      ring
    have hdiff : MemH10 (Metric.ball z (h / 2))
        (fun y => (v - vk k).toFun y - (uD' - Φ k).toFun y) := by
      rw [hfun]; exact Homogenization.memH10_sub ⟨σ, rfl⟩ ⟨ρ k, rfl⟩
    have hae := aux_in_deterministic_core_harmonic_abs_le (M := 1 / ((k : ℝ) + 1)) hKc hw hdiff
      (by positivity) (fun y hy => by
        simp only [H1Function.sub_toFun]
        change |Ũ y - (Φ k).toFun y| ≤ _
        rw [hΦf, abs_sub_comm]
        exact hφb k y (subset_closure hy))
    filter_upwards [hae] with y hy
    simpa only [H1Function.sub_toFun] using hy
  have hVv : Vlim =ᵐ[volume.restrict (Metric.ball z (h / 2))] v.toFun := by
    have hall : ∀ᵐ y ∂volume.restrict (Metric.ball z (h / 2)),
        ∀ k, |V k y - v.toFun y| ≤ 1 / ((k : ℝ) + 1) := by
      rw [ae_all_iff]
      intro k
      filter_upwards [hvk k, hVae k] with y h1 h2
      rw [h2, abs_sub_comm]
      exact h1
    filter_upwards [hall, ae_restrict_mem hKo.measurableSet] with y hy hyK
    exact tendsto_nhds_unique (hlim y (subset_closure hyK))
      (aux_in_deterministic_core_tendsto_of_abs_le hy)
  exact ⟨v, hvH, hZD, Vlim, hVclim, hVv, hfr⟩

end SubdiffusiveProcess.Paper
end
end InDetCoreChunk_InDetCore_BoundaryHarmonic

section InDetCoreChunk_InDetCore_Affine




open MeasureTheory Set Metric Filter Topology TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal Pointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- Volume averages are invariant under a positive dilation of the window. -/
theorem aux_in_deterministic_core_volumeAverage_smul {d : ℕ} {R : ℝ} (hR : 0 < R)
    (W : Set (Vec d)) (F : Vec d → ℝ) :
    volumeAverage (R • W) F = volumeAverage W (fun y => F (R • y)) := by
  unfold volumeAverage
  rw [Homogenization.Book.Ch01.setIntegral_smul_set_eq_comp_smul_of_pos hR,
    Measure.addHaar_smul, Module.finrank_fin_fun, abs_of_pos (pow_pos hR d), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul, mul_inv]
  have hRd : R ^ d ≠ 0 := pow_ne_zero d hR.ne'
  field_simp

/-- Normalized `L²` sizes are invariant under a positive dilation and a translation. -/
theorem aux_in_deterministic_core_normalizedL2On_affine {d : ℕ} {R : ℝ} (hR : 0 < R)
    (w : Vec d) (W : Set (Vec d)) (F : Vec d → ℝ) :
    normalizedL2On (translateSet w (R • W)) F = normalizedL2On W (fun y => F (R • y + w)) := by
  rw [Section6HarmonicApproximation.normalizedL2On_translateSet]
  unfold normalizedL2On
  rw [aux_in_deterministic_core_volumeAverage_smul hR]

/-- Averages are invariant under a positive dilation and a translation. -/
theorem aux_in_deterministic_core_volumeAverage_affine {d : ℕ} {R : ℝ} (hR : 0 < R)
    (w : Vec d) (W : Set (Vec d)) (F : Vec d → ℝ) :
    volumeAverage (translateSet w (R • W)) F = volumeAverage W (fun y => F (R • y + w)) := by
  unfold volumeAverage
  rw [volume_translateSet_eq, ← setIntegral_comp_addRight_translateSet]
  have := aux_in_deterministic_core_volumeAverage_smul hR W (fun x => F (x + w))
  unfold volumeAverage at this
  exact this

/-- Balls under the affine map. -/
theorem aux_in_deterministic_core_translateSet_smul_ball {d : ℕ} {R : ℝ} (hR : 0 < R)
    (w y : Vec d) (ρ : ℝ) :
    translateSet w (R • Metric.ball y ρ) = Metric.ball (R • y + w) (R * ρ) := by
  rw [_root_.smul_ball hR.ne', Real.norm_eq_abs, abs_of_pos hR]
  ext x
  rw [mem_translateSet_iff_sub_mem, Metric.mem_ball, Metric.mem_ball, dist_eq_norm,
    dist_eq_norm]
  congr! 2
  abel

/-- Almost-everywhere statements pull back along the affine map. -/
theorem aux_in_deterministic_core_ae_affine {d : ℕ} {R : ℝ} (hR : 0 < R) (w : Vec d)
    (W : Set (Vec d)) {P : Vec d → Prop}
    (h : ∀ᵐ p ∂(volume.restrict (translateSet w (R • W))), P p) :
    ∀ᵐ y ∂(volume.restrict W), P (R • y + w) := by
  have h1 : ∀ᵐ x ∂(volume.restrict (R • W)), P (x + w) :=
    (measurePreserving_addRight_restrict_translateSet w (R • W)).quasiMeasurePreserving.ae h
  have h2 : ∀ᵐ x ∂(Measure.map (fun y : Vec d => R • y) (volume.restrict W)), P (x + w) := by
    rw [map_smul_volume_restrict hR W]
    exact Measure.ae_smul_measure h1 _
  exact ae_of_ae_map (measurable_const_smul R).aemeasurable h2



theorem aux_in_deterministic_core_native_harmonic {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (v : H1Function (Ω : Set (SpatialCoordinates d)))
    (hv : IsWeaklyHarmonicOn (fun _ => (1 : ℝ)) (Ω : Set (SpatialCoordinates d)) v) :
    ∀ psi : killedSobolevGraph Ω,
      inner ℝ (sobolevGradient (sobolevDataOfH1 v))
        (subspaceGradient (killedSobolevGraph Ω) psi) = 0 := by
  intro psi
  obtain ⟨φ, hφ, hφg⟩ := exists_nativeH10Function_of_killedSobolevGraph psi
  have hterm : ∀ i : Fin d,
      inner ℝ ((sobolevGradient (sobolevDataOfH1 v)) i)
        ((subspaceGradient (killedSobolevGraph Ω) psi) i) =
        ∫ x in (Ω : Set (SpatialCoordinates d)), v.grad x i * φ.toH1Function.grad x i := by
    intro i
    change inner ℝ ((sobolevDataOfH1 v).2 i) ((psi : SobolevData Ω).2 i) = _
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [sobolevDataOfH1_snd_coeFn v i] with x hx
    rw [RCLike.inner_apply, conj_trivial, hx, hφg]
    ring
  rw [PiLp.inner_apply]
  simp only [hterm]
  rw [← integral_finsetSum]
  · have h0 := hv φ
    rw [← h0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [Homogenization.vecDot]
  · intro i _
    exact (v.gradMemL2 i).integrable_mul (φ.toH1Function.gradMemL2 i)

/-- Push a Laplace-harmonic `H¹` function forward along `S y = R • y + w`. -/
theorem aux_in_deterministic_core_harmonic_pushforward {d : ℕ} {K P : Set (Vec d)}
    {R : ℝ} (hR : 0 < R) (w : Vec d) (hP : P = translateSet w (R • K)) (v : H1Function K)
    (hv : IsWeaklyHarmonicOn (fun _ => (1 : ℝ)) K v) :
    ∃ v' : H1Function P, (∀ x, v'.toFun x = v.toFun (R⁻¹ • (x - w))) ∧
      IsWeaklyHarmonicOn (fun _ => (1 : ℝ)) P v' := by
  subst hP
  have h1 : IsWeaklyHarmonicOn (fun x => (fun _ => (1 : ℝ)) (R⁻¹ • x)) (R • K) (v.dilate hR) :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.isWeaklyHarmonicOn_dilate hR hv
  have h2 : IsWeaklyHarmonicOn (fun _ => (1 : ℝ)) (R • K) (R⁻¹ • v.dilate hR) := by
    intro φ
    have h := h1 φ
    have : ∫ x in R • K, vecDot ((fun _ => (1 : ℝ)) x • (R⁻¹ • v.dilate hR).grad x)
        (φ.toH1Function.grad x) ∂volume =
        R⁻¹ * ∫ x in R • K, vecDot ((fun x => (fun _ => (1 : ℝ)) (R⁻¹ • x)) x •
          (v.dilate hR).grad x) (φ.toH1Function.grad x) ∂volume := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [H1Function.smul_grad, one_smul, Homogenization.vecDot_smul_left]
    rw [this, h, mul_zero]
  have h3 := SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.isWeaklyHarmonicOn_translate w h2
  refine ⟨(R⁻¹ • v.dilate hR).translate w, fun x => ?_, h3⟩
  simp only [H1Function.translate_toFun, H1Function.smul_toFun, H1Function.dilate_toFun]
  rw [← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]

end SubdiffusiveProcess.Paper
end
end InDetCoreChunk_InDetCore_Affine

section InDetCoreChunk_InDetCore_ExcessAffine

/-!
# Affine excess under the affine change of variables 

For `S y = R • y + w` (`R > 0`), affine competitors correspond bijectively
(`ℓ ↦ ℓ ∘ S⁻¹`), so the frozen affine excess scales only through its `3^{-j}` normalizer and
the minimizers transport with slope multiplied by `R`.  The excess and the minimizers only see
the function a.e. on the window.
-/

open MeasureTheory Set Metric Filter Topology TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal Pointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- The pushforward of an affine function along `S`. -/
def aux_in_deterministic_core_affinePush {d : ℕ} (R : ℝ) (w : Vec d) (ell : Affine d) :
    Affine d :=
  ⟨ell.constant - vecDot (R⁻¹ • ell.slope) w, R⁻¹ • ell.slope⟩

/-- The pullback of an affine function along `S`. -/
def aux_in_deterministic_core_affinePull {d : ℕ} (R : ℝ) (w : Vec d) (ell : Affine d) :
    Affine d :=
  ⟨ell.constant + vecDot ell.slope w, R • ell.slope⟩

theorem aux_in_deterministic_core_affinePush_eval {d : ℕ} {R : ℝ} (hR : 0 < R) (w : Vec d)
    (ell : Affine d) (y : Vec d) :
    (aux_in_deterministic_core_affinePush R w ell).eval (R • y + w) = ell.eval y := by
  simp only [aux_in_deterministic_core_affinePush, Affine.eval]
  rw [Homogenization.vecDot_add_right, Homogenization.vecDot_smul_left,
    Homogenization.vecDot_smul_left, Homogenization.vecDot_smul_right]
  field_simp
  ring

theorem aux_in_deterministic_core_affinePull_eval {d : ℕ} (R : ℝ) (w : Vec d)
    (ell : Affine d) (y : Vec d) :
    (aux_in_deterministic_core_affinePull R w ell).eval y = ell.eval (R • y + w) := by
  simp only [aux_in_deterministic_core_affinePull, Affine.eval]
  rw [Homogenization.vecDot_add_right, Homogenization.vecDot_smul_left,
    Homogenization.vecDot_smul_right]
  ring

/-- Affine errors under `S` (pushforward competitor). -/
theorem aux_in_deterministic_core_affineError_push {d : ℕ} {R : ℝ} (hR : 0 < R) (w : Vec d)
    (W : Set (Vec d)) (F : Vec d → ℝ) (ell : Affine d) :
    affineError W (fun y => F (R • y + w)) ell =
      affineError (translateSet w (R • W)) F (aux_in_deterministic_core_affinePush R w ell) := by
  unfold affineError
  rw [aux_in_deterministic_core_normalizedL2On_affine hR]
  congr 1
  funext y
  rw [aux_in_deterministic_core_affinePush_eval hR]

/-- Affine errors under `S` (pullback competitor). -/
theorem aux_in_deterministic_core_affineError_pull {d : ℕ} {R : ℝ} (hR : 0 < R) (w : Vec d)
    (W : Set (Vec d)) (F : Vec d → ℝ) (ell : Affine d) :
    affineError (translateSet w (R • W)) F ell =
      affineError W (fun y => F (R • y + w)) (aux_in_deterministic_core_affinePull R w ell) := by
  unfold affineError
  rw [aux_in_deterministic_core_normalizedL2On_affine hR]
  congr 1
  funext y
  rw [aux_in_deterministic_core_affinePull_eval]

/-- The competitor sets agree. -/
theorem aux_in_deterministic_core_affineErrorSet {d : ℕ} {R : ℝ} (hR : 0 < R) (w : Vec d)
    (W : Set (Vec d)) (F : Vec d → ℝ) :
    {r : ℝ | ∃ ell : Affine d, r = affineError W (fun y => F (R • y + w)) ell} =
      {r : ℝ | ∃ ell : Affine d, r = affineError (translateSet w (R • W)) F ell} := by
  ext r
  constructor
  · rintro ⟨ell, rfl⟩
    exact ⟨_, aux_in_deterministic_core_affineError_push hR w W F ell⟩
  · rintro ⟨ell, rfl⟩
    exact ⟨_, aux_in_deterministic_core_affineError_pull hR w W F ell⟩

/-- **Excess under `S`.** -/
theorem aux_in_deterministic_core_excess_affine {d : ℕ} {R : ℝ} (hR : 0 < R) (w : Vec d)
    (W : Set (Vec d)) (F : Vec d → ℝ) (n n' : ℤ) :
    excess n W (fun y => F (R • y + w)) =
      (3 : ℝ) ^ (n' - n) * excess n' (translateSet w (R • W)) F := by
  unfold excess
  rw [aux_in_deterministic_core_affineErrorSet hR w W F, ← mul_assoc, ← zpow_add₀ (by norm_num)]
  congr 2
  ring

/-- **Minimizers under `S`**: the pullback of a physical minimizer is a GMC minimizer. -/
theorem aux_in_deterministic_core_affineMinimizers_pull {d : ℕ} {R : ℝ} (hR : 0 < R)
    (w : Vec d) (W : Set (Vec d)) (F : Vec d → ℝ) (ell : Affine d)
    (hell : ell ∈ affineMinimizers (translateSet w (R • W)) F) :
    aux_in_deterministic_core_affinePull R w ell ∈
      affineMinimizers W (fun y => F (R • y + w)) := by
  unfold affineMinimizers at hell ⊢
  simp only [mem_ofPred_eq] at hell ⊢
  rw [aux_in_deterministic_core_affineErrorSet hR w W F,
    ← aux_in_deterministic_core_affineError_pull hR w W F ell]
  exact hell

/-- Slope of the pullback. -/
theorem aux_in_deterministic_core_affinePull_slope {d : ℕ} {R : ℝ} (hR : 0 < R) (w : Vec d)
    (ell : Affine d) :
    Real.sqrt (vecNormSq (aux_in_deterministic_core_affinePull R w ell).slope) =
      R * Real.sqrt (vecNormSq ell.slope) := by
  simp only [aux_in_deterministic_core_affinePull]
  have h : vecNormSq (R • ell.slope) = R ^ 2 * vecNormSq ell.slope := by
    simp only [vecNormSq]
    rw [Homogenization.vecDot_smul_left, Homogenization.vecDot_smul_right]
    ring
  rw [h, Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq hR.le]

/-- Affine errors only see the function a.e. on the window. -/
theorem aux_in_deterministic_core_affineError_congr {d : ℕ} {W : Set (Vec d)}
    {f g : Vec d → ℝ} (hfg : f =ᵐ[volume.restrict W] g) (ell : Affine d) :
    affineError W f ell = affineError W g ell := by
  unfold affineError
  refine Section6ExcessDecay.normalizedL2On_congr_ae ?_
  filter_upwards [hfg] with x hx
  rw [hx]

theorem aux_in_deterministic_core_excess_congr {d : ℕ} {W : Set (Vec d)} {f g : Vec d → ℝ}
    (hfg : f =ᵐ[volume.restrict W] g) (n : ℤ) : excess n W f = excess n W g := by
  unfold excess
  simp_rw [aux_in_deterministic_core_affineError_congr hfg]

theorem aux_in_deterministic_core_affineMinimizers_congr {d : ℕ} {W : Set (Vec d)}
    {f g : Vec d → ℝ} (hfg : f =ᵐ[volume.restrict W] g) :
    affineMinimizers W f = affineMinimizers W g := by
  unfold affineMinimizers
  simp_rw [aux_in_deterministic_core_affineError_congr hfg]

end SubdiffusiveProcess.Paper
end
end InDetCoreChunk_InDetCore_ExcessAffine

section InDetCoreChunk_InDetCore_Source

/-!
# The source term of the carrier on a unit window of `□_5` 

For the raw-dilated unit-cube lift `g = 3^{-5} F(3^{-5} ·)`, the carrier's fractional source term on
a unit window inside `□_5` is bounded by `3^{5d/2}` times the unit fractional constant times the
`H¹` budget of `F`.  With the transport budget and Hölder's inequality `L² ≤ L^p` on the room cube
this is `≲ (side of qd)² · fNorm qd`.
-/

open MeasureTheory Set Metric Filter Topology TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal Pointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- Volume of a sup-norm ball. -/
theorem aux_in_deterministic_core_volume_ball {d : ℕ} (x : Vec d) {ρ : ℝ} (hρ : 0 < ρ) :
    volume (Metric.ball x ρ) = ENNReal.ofReal ((2 * ρ) ^ d) := by
  rw [Real.volume_pi_ball x hρ, Fintype.card_fin]

/-- **Fractional source term on a unit window of `□_5`.** -/
theorem aux_in_deterministic_core_source_window {d : ℕ} [NeZero d]
    (sOrder : FractionalOrder) (F : CubeVectorH1Function (originCube d 0)) (x : Vec d)
    (hx : translatedCube d 0 x ⊆ cube d 5) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : Section6Dirichlet.unitCubeVectorH1ENormBudget F ≤ ENNReal.ofReal B) :
    (fractionalSeminormOn (truncatedCube d 5 0 x) sOrder.1
        (Section6Dirichlet.centeredCubeScaledVectorDilation 1 5 F).toField).toReal ≤
      Real.sqrt (((3 : ℝ) ^ (5 : ℤ)) ^ d) *
        ((Section6Dirichlet.scaledVectorDatumFractionalConstant sOrder d).toReal * B) := by
  set g := (Section6Dirichlet.centeredCubeScaledVectorDilation 1 5 F).toField with hg
  have htr : truncatedCube d 5 0 x = translatedCube d 0 x := Set.inter_eq_left.2 hx
  have hball : translatedCube d 0 x = Metric.ball x ((3 : ℝ) ^ (0 : ℤ) / 2) :=
    aux_in_deterministic_regularity_translatedCube_eq_ball 0 x
  have hvolW : volume (truncatedCube d 5 0 x) = 1 := by
    rw [htr, hball, aux_in_deterministic_core_volume_ball x (by norm_num)]
    norm_num
  have hQ : cube d 5 = Metric.ball (0 : Vec d) ((3 : ℝ) ^ (5 : ℤ) / 2) := by
    have := aux_in_deterministic_regularity_translatedCube_eq_ball (d := d) 5 0
    rw [← this]
    ext y
    simp [translatedCube]
  have hvolQ : volume (cube d 5) = ENNReal.ofReal (((3 : ℝ) ^ (5 : ℤ)) ^ d) := by
    rw [hQ, aux_in_deterministic_core_volume_ball _ (by positivity)]
    congr 2
    ring
  have hQ0 : volume (cube d 5) ≠ 0 := by
    rw [hvolQ]; exact ENNReal.ofReal_ne_zero_iff.2 (by positivity)
  have hQtop : volume (cube d 5) ≠ ⊤ := by rw [hvolQ]; exact ENNReal.ofReal_ne_top
  have hmono := Section6HarmonicApproximation.fractionalSeminormOn_mono_set
    (show truncatedCube d 5 0 x ⊆ cube d 5 from Set.inter_subset_right) hQ0 hQtop sOrder.1 g
  rw [hvolW, inv_one, one_mul, hvolQ] at hmono
  have hid : fractionalSeminormOn (cube d 5) sOrder.1 g =
      paperFractionalSeminorm (originCube d 5) sOrder FiniteLpExponent.two g := by
    change fractionalSeminormOn (openCubeSet (originCube d 5)) sOrder.1 g = _
    have hguard := Section6HarmonicApproximation.fractionalSeminormOn_openCubeSet_eq_guarded_of_measurable
      _ _ _ (Section6Dirichlet.centeredCubeScaledVectorDilationWspField 1 5 sOrder F).kernel_aestronglyMeasurable
    have hgfield : g = (Section6Dirichlet.centeredCubeScaledVectorDilationWspField 1 5 sOrder F).toField := rfl
    rw [hgfield, hguard]
    unfold paperFractionalSeminorm
    norm_num [FiniteLpExponent.two_exponent]
  have hpaper := Section6Dirichlet.paperFractionalSeminorm_centeredCubeScaledVectorDilation_le_h1Budget
    1 5 sOrder F
  unfold Section6Dirichlet.scaledVectorDatumFractionalENormBound at hpaper
  set K := Section6Dirichlet.scaledVectorDatumFractionalConstant sOrder d with hK
  have hKtop : K ≠ ⊤ := (Section6Dirichlet.scaledVectorDatumFractionalConstant_lt_top sOrder d).ne
  have hscale1 : (ENNReal.ofReal (centeredCubeScale 5)) ^ (-sOrder.1) ≤ 1 := by
    refine ENNReal.rpow_le_one_of_one_le_of_neg ?_ (by linarith [sOrder.2.1])
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [centeredCubeScale]
    exact one_le_zpow₀ (by norm_num) (by norm_num)
  have hscale2 : ‖(1 : ℝ) * (centeredCubeScale 5)⁻¹‖ₑ ≤ 1 := by
    rw [one_mul, ← ofReal_norm, Real.norm_eq_abs, abs_inv]
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [centeredCubeScale]
    rw [abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (one_le_zpow₀ (by norm_num) (by norm_num))
  have hchain : fractionalSeminormOn (truncatedCube d 5 0 x) sOrder.1 g ≤
      (ENNReal.ofReal (((3 : ℝ) ^ (5 : ℤ)) ^ d)) ^ (1 / 2 : ℝ) * (K * ENNReal.ofReal B) := by
    refine hmono.trans (mul_le_mul_right ?_ _)
    rw [hid]
    refine hpaper.trans ?_
    calc K * (ENNReal.ofReal (centeredCubeScale 5)) ^ (-sOrder.1) *
          ‖(1 : ℝ) * (centeredCubeScale 5)⁻¹‖ₑ *
          Section6Dirichlet.unitCubeVectorH1ENormBudget F
        ≤ K * 1 * 1 * ENNReal.ofReal B := by gcongr
      _ = K * ENNReal.ofReal B := by ring
  have hfin : (ENNReal.ofReal (((3 : ℝ) ^ (5 : ℤ)) ^ d)) ^ (1 / 2 : ℝ) * (K * ENNReal.ofReal B) ≠
      ⊤ := ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
        (ENNReal.mul_ne_top hKtop ENNReal.ofReal_ne_top)
  refine (ENNReal.toReal_mono hfin hchain).trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hB0, ← Real.sqrt_eq_rpow]

/-- **Hölder on a cube**: the `L²` size, normalized by the volume, is at most the normalized
`L^p` size (`p ≥ 2`). -/
theorem aux_in_deterministic_core_L2_le_fNorm {d : ℕ} (w : Vec d) (ρ : ℝ) (hρ : 0 < ρ)
    (p : ℝ) (hp : 2 ≤ p) (f : Vec d → ℝ)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Metric.ball w (ρ / 2)))) :
    Real.sqrt ((ρ ^ d)⁻¹) * (eLpNorm f 2 (volume.restrict (Metric.ball w (ρ / 2)))).toReal ≤
      (eLpNorm f (ENNReal.ofReal p) (volume.restrict (Metric.ball w (ρ / 2)))).toReal /
        (volume.real (Metric.ball w (ρ / 2))) ^ (1 / p) := by
  have hvol : volume (Metric.ball w (ρ / 2)) = ENNReal.ofReal (ρ ^ d) := by
    rw [aux_in_deterministic_core_volume_ball w (by positivity)]
    congr 2
    ring
  have hV : 0 < ρ ^ d := by positivity
  have hvolr : volume.real (Metric.ball w (ρ / 2)) = ρ ^ d := by
    rw [Measure.real, hvol, ENNReal.toReal_ofReal hV.le]
  have hp0 : 0 < p := by linarith
  have h2p : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal hp
  have hH := eLpNorm_le_eLpNorm_mul_rpow_measure_univ h2p hf.aestronglyMeasurable
  rw [Measure.restrict_apply_univ, hvol] at hH
  have htop : eLpNorm f (ENNReal.ofReal p) (volume.restrict (Metric.ball w (ρ / 2))) ≠ ⊤ :=
    hf.eLpNorm_lt_top.ne
  have hexp : (1 / (2 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal p).toReal) = 1 / 2 - 1 / p := by
    rw [ENNReal.toReal_ofReal hp0.le]
    norm_num
  rw [hexp] at hH
  have hrhs : eLpNorm f (ENNReal.ofReal p) (volume.restrict (Metric.ball w (ρ / 2))) *
      ENNReal.ofReal (ρ ^ d) ^ (1 / 2 - 1 / p) ≠ ⊤ :=
    ENNReal.mul_ne_top htop (ENNReal.rpow_ne_top_of_nonneg (by
      have : 1 / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp
      linarith) ENNReal.ofReal_ne_top)
  have hreal := ENNReal.toReal_mono hrhs hH
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hV.le] at hreal
  rw [hvolr]
  set A := (eLpNorm f (ENNReal.ofReal p) (volume.restrict (Metric.ball w (ρ / 2)))).toReal
  set L := (eLpNorm f 2 (volume.restrict (Metric.ball w (ρ / 2)))).toReal
  have hs : Real.sqrt ((ρ ^ d)⁻¹) = (ρ ^ d) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.inv_rpow hV.le, Real.rpow_neg hV.le]
  rw [hs]
  have hpos : 0 < (ρ ^ d) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hV _
  calc (ρ ^ d) ^ (-(1 / 2 : ℝ)) * L ≤ (ρ ^ d) ^ (-(1 / 2 : ℝ)) *
        (A * (ρ ^ d) ^ (1 / 2 - 1 / p)) := mul_le_mul_of_nonneg_left hreal hpos.le
    _ = A * ((ρ ^ d) ^ (1 / 2 - 1 / p) * (ρ ^ d) ^ (-(1 / 2 : ℝ))) := by ring
    _ = A * (ρ ^ d) ^ (-(1 / p)) := by
        rw [← Real.rpow_add hV]; congr 2; ring
    _ = A / (ρ ^ d) ^ (1 / p) := by
        rw [Real.rpow_neg hV.le, div_eq_mul_inv]
        rfl

end SubdiffusiveProcess.Paper
end
end InDetCoreChunk_InDetCore_Source

section InDetCoreChunk_InDetCore_HarmGMC

/-!
# The interior harmonic comparison on the fixed GMC scale `m = 5`, `n = 0`


`aux_in_deterministic_core_harm_gmc`: from clause 2 of `lane4_deterministic_good_scale_input`
(the arbitrary-coefficient interior harmonic approximation) at `Cerr = 1`, for a GMC solution on
`□_5` with a continuous representative `Ũ`, a unit window `z + □_0` whose closure lies in `□_5`, the
boundary-continuous harmonic replacement `v` on `z + □_{-2}` satisfies the comparison with the
window oscillation and the fractional source on `z + □_0`.
-/

open MeasureTheory Set Metric Filter Topology TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal Pointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- G4 on any set equal to a sup-ball. -/
theorem aux_in_deterministic_core_boundary_harmonic' {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {K : Set (Vec d)} (z : Vec d) (h : ℝ) (hh : 0 < h) (hK : K = Metric.ball z (h / 2))
    {O : Set (Vec d)} (hO : IsOpen O) (hKO : closure K ⊆ O)
    (Ũ : Vec d → ℝ) (hŨ : ContinuousOn Ũ O) (uD : H1Function K)
    (huD : uD.toFun =ᵐ[volume.restrict K] Ũ) :
    ∃ v : H1Function K, IsWeaklyHarmonicOn (fun _ => (1 : ℝ)) K v ∧
      HasZeroTraceDifferenceOn K v uD ∧
      ∃ V : Vec d → ℝ, ContinuousOn V (closure K) ∧ V =ᵐ[volume.restrict K] v.toFun ∧
        ∀ x ∈ frontier K, V x = Ũ x := by
  subst hK
  exact aux_in_deterministic_core_boundary_harmonic hd z h hh hO hKO Ũ hŨ uD huD

/-- A translated triadic cube inside `□_m` is its own truncation. -/
theorem aux_in_deterministic_core_trunc_eq_ball {d : ℕ} (m j : ℤ) (x : Vec d)
    (hsub : Metric.ball x ((3 : ℝ) ^ j / 2) ⊆ cube d m) :
    truncatedCube d m j x = Metric.ball x ((3 : ℝ) ^ j / 2) := by
  unfold truncatedCube
  rw [aux_in_deterministic_regularity_translatedCube_eq_ball]
  exact Set.inter_eq_left.2 hsub

/-- The origin cube as a sup-ball. -/
theorem aux_in_deterministic_core_cube_eq_ball {d : ℕ} (m : ℤ) :
    cube d m = Metric.ball (0 : Vec d) ((3 : ℝ) ^ m / 2) := by
  rw [← aux_in_deterministic_regularity_translatedCube_eq_ball m (0 : Vec d)]
  ext y
  simp [translatedCube]

/-- Clause 2 of `lane4_deterministic_good_scale_input` at `Cerr = 1` with constant `CD`. -/
def aux_in_deterministic_core_clause2 (d : ℕ) [NeZero d] (CD : ℝ) : Prop :=
  ∀ s : ℝ, 0 < s → s ≤ (1 / 4 : ℝ) →
    ∀ m n : ℕ, n + 5 ≤ m → ∀ z ∈ cube d m,
    ∀ x ∈ truncatedCube d m (n - 3) z,
    ¬ BoundaryTouches (truncatedCube d m n x) (cube d m) →
    ∀ a : Vec d → ℝ, ∀ data : ScalarTriadicCoeffData (fun y => a (y + z)),
    ∀ a0 : ℝ, 0 < a0 →
    let err : ENNReal :=
      paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2) (s / 8)
        Homogenization.Book.Ch02.MultiscaleExponent.infinity
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
        data.toTriadicCoeffFamily a0;
    err ≤ ENNReal.ofReal 1 →
    ∀ (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
      IsDivFormWeakSolutionOn a (cube d m) u g →
      (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
        Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
          (originCube d m) sOrder FiniteLpExponent.two g) →
      ∀ y ∈ cube d m,
        truncatedCube d m (n - 4) x ⊆ translatedCube d (n - 2) y →
        translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x →
        ∀ uD : H1Function (translatedCube d (n - 2) y),
          (∀ q, uD.toFun q = u.toFun q) → (∀ q, uD.grad q = u.grad q) →
        (∃ v : H1Function (translatedCube d (n - 2) y),
          IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v ∧
            HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD) ∧
        (∀ v v' : H1Function (translatedCube d (n - 2) y),
          (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v ∧
              HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD) →
          (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v' ∧
              HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v' uD) →
          v.toFun =ᵐ[volume.restrict (translatedCube d (n - 2) y)] v'.toFun ∧
            v.grad =ᵐ[volume.restrict (translatedCube d (n - 2) y)] v'.grad) ∧
        ∀ (v : H1Function (translatedCube d (n - 2) y)),
          IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v →
          HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD →
          normalizedL2On (truncatedCube d m (n - 4) x)
              (fun q => u.toFun q - v.toFun q) ≤
            CD * s ^ (-3 / 2 : ℝ) * err.toReal *
                normalizedL2On (truncatedCube d m n x)
                  (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) +
              CD * s ^ (-15 / 2 : ℝ) * (a0)⁻¹ *
                (3 : ℝ) ^ ((1 + s) * n) *
                (fractionalSeminormOn (truncatedCube d m n x) s g).toReal

/-- The carrier supplies clause 2 at `Cerr = 1`. -/
theorem aux_in_deterministic_core_clause2_of_det (d : ℕ) [NeZero d]
    (D : _root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d) :
    ∃ CD : ℝ, 0 < CD ∧ aux_in_deterministic_core_clause2 d CD :=
  D.2.1 1 one_pos

/-- **GMC harmonic comparison at `m = 5`, `n = 0`.** -/
theorem aux_in_deterministic_core_harm_gmc {d : ℕ} [NeZero d] (hd : 2 ≤ d) (CD : ℝ)
    (hD : aux_in_deterministic_core_clause2 d CD)
    (s : ℝ) (hs0 : 0 < s) (hs4 : s ≤ 1 / 4)
    (z : Vec d) (hz : Metric.closedBall z (1 / 2) ⊆ cube d 5)
    (a : Vec d → ℝ) (data : ScalarTriadicCoeffData (fun y => a (y + z)))
    (a0 : ℝ) (ha0 : 0 < a0)
    (herr : paperHomogenizationError (originCube d 2) 2 (s / 8)
          Homogenization.Book.Ch02.MultiscaleExponent.infinity
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
          data.toTriadicCoeffFamily a0 ≤ ENNReal.ofReal 1)
    (u : H1Function (openCubeSet (originCube d 5))) (g : Vec d → Vec d)
    (hweak : IsDivFormWeakSolutionOn a (cube d 5) u g)
    (hg : ∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d 5) sOrder FiniteLpExponent.two g)
    (Ũ : Vec d → ℝ) (hŨ : ContinuousOn Ũ (cube d 5))
    (huŨ : u.toFun =ᵐ[volume.restrict (cube d 5)] Ũ) :
    ∃ v : H1Function (translatedCube d (((0 : ℕ) : ℤ) - 2) z),
      IsWeaklyHarmonicOn (fun _ => (1 : ℝ)) (translatedCube d (((0 : ℕ) : ℤ) - 2) z) v ∧
      ∃ V : Vec d → ℝ, ContinuousOn V (closure (Metric.ball z (1 / 18))) ∧
        V =ᵐ[volume.restrict (translatedCube d (((0 : ℕ) : ℤ) - 2) z)] v.toFun ∧
        (∀ x ∈ frontier (Metric.ball z (1 / 18)), V x = Ũ x) ∧
        normalizedL2On (Metric.ball z (1 / 162)) (fun q => Ũ q - V q) ≤
          CD * s ^ (-3 / 2 : ℝ) *
              (paperHomogenizationError (originCube d 2) 2 (s / 8)
                Homogenization.Book.Ch02.MultiscaleExponent.infinity
                (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
                data.toTriadicCoeffFamily a0).toReal *
              normalizedL2On (Metric.ball z (1 / 2))
                (fun q => Ũ q - averageOn (Metric.ball z (1 / 2)) Ũ) +
            CD * s ^ (-15 / 2 : ℝ) * (a0)⁻¹ *
              (fractionalSeminormOn (truncatedCube d 5 0 z) s g).toReal := by
  have hQ := aux_in_deterministic_core_cube_eq_ball (d := d) 5
  have hball_sub : ∀ ρ : ℝ, ρ ≤ 1 / 2 → Metric.ball z ρ ⊆ cube d 5 := fun ρ hρ =>
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hρ)).trans hz
  have hz5 : z ∈ cube d 5 := hz (Metric.mem_closedBall_self (by norm_num))
  -- the windows
  have e2 : translatedCube d (((0 : ℕ) : ℤ) - 2) z = Metric.ball z (1 / 18) := by
    rw [aux_in_deterministic_regularity_translatedCube_eq_ball]; norm_num
  have e4 : truncatedCube d 5 (((0 : ℕ) : ℤ) - 4) z = Metric.ball z (1 / 162) := by
    rw [aux_in_deterministic_core_trunc_eq_ball 5 _ z (by
      refine hball_sub _ ?_; norm_num)]
    norm_num
  have e3 : truncatedCube d 5 (((0 : ℕ) : ℤ) - 3) z = Metric.ball z (1 / 54) := by
    rw [aux_in_deterministic_core_trunc_eq_ball 5 _ z (by
      refine hball_sub _ ?_; norm_num)]
    norm_num
  have e1 : truncatedCube d 5 (((0 : ℕ) : ℤ) - 1) z = Metric.ball z (1 / 6) := by
    rw [aux_in_deterministic_core_trunc_eq_ball 5 _ z (by
      refine hball_sub _ ?_; norm_num)]
    norm_num
  have e0 : truncatedCube d 5 ((0 : ℕ) : ℤ) z = Metric.ball z (1 / 2) := by
    rw [aux_in_deterministic_core_trunc_eq_ball 5 _ z (by
      refine hball_sub _ ?_; norm_num)]
    norm_num
  have e0' : truncatedCube d 5 0 z = Metric.ball z (1 / 2) := by simpa using e0
  have hxz : z ∈ truncatedCube d 5 (((0 : ℕ) : ℤ) - 3) z := by
    rw [e3]; exact Metric.mem_ball_self (by norm_num)
  have hnbt : ¬ BoundaryTouches (truncatedCube d 5 ((0 : ℕ) : ℤ) z) (cube d 5) := by
    unfold BoundaryTouches
    rw [e0, closure_ball z (by norm_num : (1 / 2 : ℝ) ≠ 0), not_not,
      Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hy1, hy2⟩
    have hopen : IsOpen (cube d 5) := by rw [hQ]; exact Metric.isOpen_ball
    rw [hopen.frontier_eq] at hy2
    exact hy2.2 (hz hy1)
  have hsub1 : truncatedCube d 5 (((0 : ℕ) : ℤ) - 4) z ⊆ translatedCube d (((0 : ℕ) : ℤ) - 2) z := by
    rw [e4, e2]; exact Metric.ball_subset_ball (by norm_num)
  have hsub2 : translatedCube d (((0 : ℕ) : ℤ) - 2) z ⊆ truncatedCube d 5 (((0 : ℕ) : ℤ) - 1) z := by
    rw [e2, e1]; exact Metric.ball_subset_ball (by norm_num)
  have hKsub : translatedCube d (((0 : ℕ) : ℤ) - 2) z ⊆ cube d 5 := by
    rw [e2]; exact hball_sub _ (by norm_num)
  have hKo : IsOpen (translatedCube d (((0 : ℕ) : ℤ) - 2) z) := by
    rw [e2]; exact Metric.isOpen_ball
  set uD : H1Function (translatedCube d (((0 : ℕ) : ℤ) - 2) z) := u.restrict hKo hKsub with huDdef
  unfold aux_in_deterministic_core_clause2 at hD
  have hmain := hD s hs0 hs4 5 0 (by norm_num) z hz5 z hxz hnbt a data a0 ha0 herr u g hweak hg
    z hz5 hsub1 hsub2 uD (fun q => rfl) (fun q => rfl)
  -- boundary-continuous replacement on the ball form
  have hKO : closure (translatedCube d (((0 : ℕ) : ℤ) - 2) z) ⊆ cube d 5 := by
    rw [e2, closure_ball z (by norm_num : (1 / 18 : ℝ) ≠ 0)]
    exact (Metric.closedBall_subset_closedBall (by norm_num)).trans hz
  have hQo : IsOpen (cube d 5) := by rw [hQ]; exact Metric.isOpen_ball
  have huD : uD.toFun =ᵐ[volume.restrict (translatedCube d (((0 : ℕ) : ℤ) - 2) z)] Ũ :=
    ae_restrict_of_ae_restrict_of_subset hKsub huŨ
  obtain ⟨v, hvH, hvZ, V, hVc, hVae, hVfr⟩ := aux_in_deterministic_core_boundary_harmonic' hd z
    (3 ^ (((0 : ℕ) : ℤ) - 2) : ℝ) (by positivity)
    (aux_in_deterministic_regularity_translatedCube_eq_ball _ z) hQo hKO Ũ hŨ uD huD
  have hest := hmain.2.2 v hvH hvZ
  have hK162 : Metric.ball z (1 / 162) ⊆ translatedCube d (((0 : ℕ) : ℤ) - 2) z := by
    rw [e2]; exact Metric.ball_subset_ball (by norm_num)
  have hlhs : (fun q => u.toFun q - v.toFun q) =ᵐ[volume.restrict (Metric.ball z (1 / 162))]
      (fun q => Ũ q - V q) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (hball_sub _ (by norm_num)) huŨ,
      ae_restrict_of_ae_restrict_of_subset hK162 hVae] with q h1 h2
    rw [h1, h2]
  have havg : averageOn (Metric.ball z (1 / 2)) u.toFun = averageOn (Metric.ball z (1 / 2)) Ũ := by
    unfold averageOn volumeAverage
    congr 1
    exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset (hball_sub _ le_rfl) huŨ)
  have hosc : (fun q => u.toFun q - averageOn (Metric.ball z (1 / 2)) u.toFun)
      =ᵐ[volume.restrict (Metric.ball z (1 / 2))]
      (fun q => Ũ q - averageOn (Metric.ball z (1 / 2)) Ũ) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (hball_sub _ le_rfl) huŨ] with q h1
    rw [h1, havg]
  have e4n : truncatedCube d 5 (-4) z = Metric.ball z (1 / 162) := by simpa using e4
  simp only [Nat.cast_ofNat, Nat.cast_zero, zero_sub, zero_add, mul_zero, Real.rpow_zero,
    mul_one] at hest
  rw [e4n, e0'] at hest
  rw [Section6ExcessDecay.normalizedL2On_congr_ae hlhs,
    Section6ExcessDecay.normalizedL2On_congr_ae hosc] at hest
  refine ⟨v, hvH, V, ?_, hVae, ?_, ?_⟩
  · rw [← e2]; exact hVc
  · rw [← e2]; exact hVfr
  · rw [e0']
    exact hest

end SubdiffusiveProcess.Paper
end
end InDetCoreChunk_InDetCore_HarmGMC

section InDetCoreChunk_InDetCore_OneStepGMC

/-!
# The one-step excess decay on the fixed GMC scale `m = h + 5`, `n = h` 

`aux_in_deterministic_core_step d C` is the arbitrary-coefficient interior one-step excess decay
`aux_prop_folded_iteration_interior_excess_decay` (from clause 2 of the carrier) at `Cerr = 1`.
-/

open MeasureTheory Set Metric Filter Topology TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped ENNReal NNReal Pointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- The interior one-step excess decay at `Cerr = 1` with constant `C`. -/
def aux_in_deterministic_core_step (d : ℕ) [NeZero d] (C : ℝ) : Prop :=
      ∀ s : ℝ, 0 < s → s ≤ (1 / 4 : ℝ) →
      ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ 1 → ∀ k : ℕ, 0 < k →
      ∀ m n : ℕ, k ≤ n → n + 5 ≤ m →
      ∀ x ∈ cube d m, ∀ z ∈ cube d m, x ∈ truncatedCube d m (n - 3) z →
      ¬ BoundaryTouches (truncatedCube d m n x) (cube d m) →
      ∀ a : Vec d → ℝ, ∀ data : ScalarTriadicCoeffData (fun y => a (y + z)),
      ∀ a0 : ℝ, 0 < a0 →
      paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2) (s / 8)
          Homogenization.Book.Ch02.MultiscaleExponent.infinity
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
          data.toTriadicCoeffFamily a0 ≤ ENNReal.ofReal (1 * epsilon) →
      ∀ (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDivFormWeakSolutionOn a (cube d m) u g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        ∀ ell : Affine d, ell ∈ affineMinimizers (truncatedCube d m n x) u.toFun →
        excess (n - k) (truncatedCube d m (n - k) x) u.toFun ≤
          C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
              (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) * epsilon) *
              excess n (truncatedCube d m n x) u.toFun +
            C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-3 / 2 : ℝ) *
              (paperHomogenizationError (originCube d ((n : ℤ) + 2)) ((n : ℤ) + 2) (s / 8)
                Homogenization.Book.Ch02.MultiscaleExponent.infinity
                (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
                data.toTriadicCoeffFamily a0).toReal *
              Real.sqrt (vecNormSq ell.slope) +
            C * s ^ (-15 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
              (a0)⁻¹ * (3 : ℝ) ^ (s * n) *
              (fractionalSeminormOn (truncatedCube d m n x) s g).toReal

/-- The carrier supplies the step. -/
theorem aux_in_deterministic_core_step_of_det (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    (D : _root_.SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input d) :
    ∃ C : ℝ, 0 < C ∧ aux_in_deterministic_core_step d C :=
  aux_prop_folded_iteration_interior_excess_decay d hd D 1 one_pos

/-- **GMC one-step at `m = h + 5`, `n = k = h`**, read on balls for an a.e. representative. -/
theorem aux_in_deterministic_core_onestep_gmc {d : ℕ} [NeZero d] (C : ℝ)
    (hstep : aux_in_deterministic_core_step d C)
    (sD : ℝ) (hsD0 : 0 < sD) (hsD4 : sD ≤ 1 / 4) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (h : ℕ) (hh : 0 < h) (xG zG : Vec d)
    (hxG : Metric.closedBall xG ((3 : ℝ) ^ (h : ℤ) / 2) ⊆ cube d ((h + 5 : ℕ) : ℤ))
    (hzG : zG ∈ cube d ((h + 5 : ℕ) : ℤ))
    (hxz : xG ∈ Metric.ball zG ((3 : ℝ) ^ ((h : ℤ) - 3) / 2))
    (a : Vec d → ℝ) (data : ScalarTriadicCoeffData (fun y => a (y + zG))) (a0 : ℝ)
    (ha0 : 0 < a0)
    (herr : paperHomogenizationError (originCube d ((h : ℤ) + 2)) ((h : ℤ) + 2) (sD / 8)
          Homogenization.Book.Ch02.MultiscaleExponent.infinity
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
          data.toTriadicCoeffFamily a0 ≤ ENNReal.ofReal (1 * ε))
    (ut : H1Function (openCubeSet (originCube d ((h + 5 : ℕ) : ℤ)))) (g : Vec d → Vec d)
    (hdiv : IsDivFormWeakSolutionOn a (cube d ((h + 5 : ℕ) : ℤ)) ut g)
    (hg : ∃ sOrder : FractionalOrder, sOrder.1 = sD ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d ((h + 5 : ℕ) : ℤ)) sOrder FiniteLpExponent.two g)
    (Ũ : Vec d → ℝ) (hutU : ut.toFun =ᵐ[volume.restrict (cube d ((h + 5 : ℕ) : ℤ))] Ũ)
    (ell : Affine d) (hell : ell ∈ affineMinimizers (Metric.ball xG ((3 : ℝ) ^ (h : ℤ) / 2)) Ũ) :
    excess 0 (Metric.ball xG (1 / 2)) Ũ ≤
      C * ((3 : ℝ) ^ (-(h : ℝ) / 2) +
          (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) * sD ^ (-3 / 2 : ℝ) * ε) *
          excess (h : ℤ) (Metric.ball xG ((3 : ℝ) ^ (h : ℤ) / 2)) Ũ +
        C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) * sD ^ (-3 / 2 : ℝ) *
          (paperHomogenizationError (originCube d ((h : ℤ) + 2)) ((h : ℤ) + 2) (sD / 8)
            Homogenization.Book.Ch02.MultiscaleExponent.infinity
            (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
            data.toTriadicCoeffFamily a0).toReal *
          Real.sqrt (vecNormSq ell.slope) +
        C * sD ^ (-15 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) *
          (a0)⁻¹ * (3 : ℝ) ^ (sD * h) *
          (fractionalSeminormOn (truncatedCube d ((h + 5 : ℕ) : ℤ) (h : ℤ) xG) sD g).toReal := by
  have hball_sub : ∀ ρ : ℝ, ρ ≤ (3 : ℝ) ^ (h : ℤ) / 2 →
      Metric.ball xG ρ ⊆ cube d ((h + 5 : ℕ) : ℤ) := fun ρ hρ =>
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hρ)).trans hxG
  have h3h : (1 : ℝ) ≤ (3 : ℝ) ^ (h : ℤ) := one_le_zpow₀ (by norm_num) (by positivity)
  have hxc : xG ∈ cube d ((h + 5 : ℕ) : ℤ) :=
    hxG (Metric.mem_closedBall_self (by positivity))
  have eh : truncatedCube d ((h + 5 : ℕ) : ℤ) (h : ℤ) xG = Metric.ball xG ((3 : ℝ) ^ (h : ℤ) / 2) :=
    aux_in_deterministic_core_trunc_eq_ball _ _ xG (hball_sub _ le_rfl)
  have e0 : truncatedCube d ((h + 5 : ℕ) : ℤ) ((h : ℤ) - (h : ℤ)) xG =
      Metric.ball xG (1 / 2) := by
    rw [sub_self, aux_in_deterministic_core_trunc_eq_ball _ _ xG (hball_sub _ (by linarith))]
    norm_num
  have e3 : xG ∈ truncatedCube d ((h + 5 : ℕ) : ℤ) ((h : ℤ) - 3) zG := by
    refine ⟨?_, hxc⟩
    rw [aux_in_deterministic_regularity_translatedCube_eq_ball]; exact hxz
  have hnbt : ¬ BoundaryTouches (truncatedCube d ((h + 5 : ℕ) : ℤ) (h : ℤ) xG)
      (cube d ((h + 5 : ℕ) : ℤ)) := by
    unfold BoundaryTouches
    rw [eh, closure_ball xG (by positivity), not_not, Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hy1, hy2⟩
    have hopen : IsOpen (cube d ((h + 5 : ℕ) : ℤ)) := by
      rw [aux_in_deterministic_core_cube_eq_ball]; exact Metric.isOpen_ball
    rw [hopen.frontier_eq] at hy2
    exact hy2.2 (hxG hy1)
  have hutb : ∀ ρ : ℝ, ρ ≤ (3 : ℝ) ^ (h : ℤ) / 2 →
      ut.toFun =ᵐ[volume.restrict (Metric.ball xG ρ)] Ũ := fun ρ hρ =>
    ae_restrict_of_ae_restrict_of_subset (hball_sub ρ hρ) hutU
  have hell' : ell ∈ affineMinimizers (truncatedCube d ((h + 5 : ℕ) : ℤ) (h : ℤ) xG) ut.toFun := by
    rw [eh, aux_in_deterministic_core_affineMinimizers_congr (hutb _ le_rfl)]; exact hell
  unfold aux_in_deterministic_core_step at hstep
  have hmain := hstep sD hsD0 hsD4 ε hε0 hε1 h hh (h + 5) h le_rfl (by omega) xG hxc zG hzG e3
    hnbt a data a0 ha0 herr ut g hdiv hg ell hell'
  rw [e0, eh, aux_in_deterministic_core_excess_congr (hutb _ (by linarith)),
    aux_in_deterministic_core_excess_congr (hutb _ le_rfl), sub_self] at hmain
  rw [eh]
  exact hmain

end SubdiffusiveProcess.Paper
end
end InDetCoreChunk_InDetCore_OneStepGMC

section InDetCoreChunk_InDetCore_ErrTransport

/-!
# Scaled identification of the unit-chart error 

`E.err z r hr a z r a0 s 2`, the `in_J` error of the cube `z + Q_r` itself, is the paper
error on the origin cube `□_k` of any global scalar representative `a'` of the rescaled
coefficient `y ↦ a(z + r 3^{-k} y)`.  This is `aux_prop_folded_iteration_err_physical` with an
arbitrary triadic dilation ratio (there `r = 3^{j+2}` and `k = j+2`).
-/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

open SubdiffusiveProcess.CoarseGrainingVocab

open Homogenization.Book.Ch02 in
/-- **Scaled error identification.** -/
theorem aux_in_deterministic_core_err_scaled {d : ℕ} (E : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (k : ℤ)
    (a : PositiveCoefficient (centeredCube z r hr))
    (a' : SpatialCoordinates d → ℝ) (z' : SpatialCoordinates d)
    (ha' : ∀ᵐ y ∂volume.restrict
        (Homogenization.openCubeSet (Homogenization.originCube d k)),
      a' (y + z') = (a.val : SpatialCoordinates d → ℝ) (fun i => z i + r * ((3 : ℝ) ^ k)⁻¹ * y i))
    (data : ScalarTriadicCoeffData (fun y => a' (y + z')))
    (a0 : ℝ) (ha0 : 0 < a0) (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    E.err z r hr a z r a0 s 2 =
      (paperHomogenizationError
        (Homogenization.originCube d k) k s
        Homogenization.Book.Ch02.MultiscaleExponent.infinity
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
        data.toTriadicCoeffFamily a0).toReal ∧
    paperHomogenizationError
        (Homogenization.originCube d k) k s
        Homogenization.Book.Ch02.MultiscaleExponent.infinity
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
        data.toTriadicCoeffFamily a0 ≠ ⊤ := by
  have hsub : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)) := subset_rfl
  have e := E.err_eq z r hr a z r hr hsub s hs 2 (by norm_num) a0 ha0
  have efin := E.err_finite z r hr a z r hr hsub s hs 2 (by norm_num) a0 ha0
  simp only [ite_eq_right (show (2 : ℝ≥0∞) ≠ ⊤ by simp)] at e efin
  set A : TriadicCoeffFamily d := E.chart z r hr a z r with hAdef
  have hQk : Homogenization.originCube d k = dilateCube k (Homogenization.originCube d 0) := by
    simp [dilateCube, Homogenization.originCube]
  have hcoef : ∀ (jj : ℤ) (R : Homogenization.TriadicCube d),
      R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0) jj →
      (data.toTriadicCoeffFamily.coeffOn (dilateCube k R)).toCoeffField
        =ᵐ[Homogenization.volumeMeasureOn (Homogenization.openCubeSet (dilateCube k R))]
        dilateCoeffField k (A.coeffOn R).toCoeffField := by
    intro jj R hRmem
    have hk0 : jj ≤ (Homogenization.originCube d 0).scale :=
      Homogenization.descendant_scale_le_of_mem_descendantsAtScale hRmem
    have hRsub : Homogenization.openCubeSet R ⊆
        Homogenization.openCubeSet (Homogenization.originCube d 0) :=
      Homogenization.openCubeSet_subset_of_mem_descendantsAtScale
        (by simpa [Homogenization.originCube] using hk0) hRmem
    have hchart := E.chart_eq z r hr a z r hr hsub R hRsub
    have hpull := eventuallyEq_comp_undilate_of_ae_eq k (Q := R)
      (f := (A.coeffOn R).toCoeffField)
      (g := fun x => Homogenization.scalarMatrix
        ((a.val : SpatialCoordinates d → ℝ) (fun i => z i + r * x i)))
      hchart
    have hdsub : Homogenization.openCubeSet (dilateCube k R) ⊆
        Homogenization.openCubeSet (Homogenization.originCube d k) := by
      rw [hQk, openCubeSet_dilateCube, openCubeSet_dilateCube]
      exact Set.smul_set_mono hRsub
    have ha'R : ∀ᵐ y ∂Homogenization.volumeMeasureOn
        (Homogenization.openCubeSet (dilateCube k R)),
        a' (y + z') = (a.val : SpatialCoordinates d → ℝ)
          (fun i => z i + r * ((3 : ℝ) ^ k)⁻¹ * y i) :=
      ae_restrict_of_ae_restrict_of_subset hdsub ha'
    filter_upwards [hpull, ha'R] with y hy hya
    change SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField (fun y => a' (y + z')) y =
      (A.coeffOn R).toCoeffField (undilateVec k y)
    rw [hy]
    change Homogenization.scalarMatrix (a' (y + z')) = _
    rw [hya]
    congr 2
    funext i
    simp only [undilateVec, triadicDilationFactor, Pi.smul_apply, smul_eq_mul]
    ring
  have hdil := aux_prop_folded_iteration_paper_error_dilate k A data.toTriadicCoeffFamily
    (Homogenization.originCube d 0) 0 s hcoef
    Homogenization.Book.Ch02.MultiscaleExponent.infinity
    (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) a0
  rw [zero_add, ← hQk] at hdil
  have hP : paperHomogenizationError (Homogenization.originCube d k) k s
      Homogenization.Book.Ch02.MultiscaleExponent.infinity
      (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
      data.toTriadicCoeffFamily a0 =
    paperHomogenizationErrorFinite (Homogenization.originCube d 0) 0 s
      Homogenization.Book.Ch02.MultiscaleExponent.infinity (2 : ℝ≥0∞).toReal A a0 := by
    rw [hdil]
    simp only [paperHomogenizationError, ENNReal.toReal_ofNat]
  refine ⟨?_, ?_⟩
  · rw [e, hP]
  · rw [hP]
    exact efin.ne

end SubdiffusiveProcess.Paper
end
end InDetCoreChunk_InDetCore_ErrTransport

section DeterministicRegularity_Regularity_Split

/-!
# `in_deterministic`: exact R1/R2 extraction and reduction to one Campanato core


  The defs below are exact slices of
`aux_in_deterministic_assembly_remaining_at` (Assembly2, variant B); the slices reassemble to
that body byte for byte.

* `R1`   finite-horizon conclusion (Campanato at `Cbound`, harmonic comparison);
* `R2`   full-event conclusion (`IsHolderOn`, `cAlphaNorm ≤ Ctotal …`, harmonic comparison);
* `R34`  the matrix-ellipticity and trace conjuncts, in both places they occur (separate tasks);
* `core` R1's conclusion with the Campanato loss written at an analytic constant `C1`;
* `cont`, `camp`, `harm` the three exact parts of `core`.
-/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- **R1** (exact slice): for every horizon, on the horizon event with the horizon budget,
every sourced native weak solution has a continuous representative with the finite-depth
Campanato bound at loss `Cbound·3^{Cbound(k0+cbuf)}·3^{Cbound·t·D}·3^{-D}` and the harmonic
comparison. -/
def aux_in_deterministic_regularity_R1
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell epshom : ℝ)
    (Cbound eps0 lam0 delta0 : ℝ) : Prop :=
      ∀ (cbuf k0 : ℕ)
        (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hMH : InfraredCharacterization M H)
        (k : ℕ) (z : SpatialCoordinates d)
        (qside : ℝ) (hqpos : 0 < qside)
        (hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
        (qcenter : SpatialCoordinates d)
        (hqcenter : qcenter = z)
        (Enl Shift Cmp : Type)
        [Fintype Enl] [Fintype Shift] [Fintype Cmp]
        (selfE : Enl) (selfShift : Shift)
        (qRoot : Enl × Shift)
        (hqRoot : qRoot = (selfE, selfShift))
        (factor : Enl → ℕ)
        (hfactor : factor selfE = 0)
        (padE : Enl) (hpad : factor padE = 1)
        (shift : Shift → SpatialCoordinates d)
        (hshift : shift selfShift = 0)
        (rootLevel : Enl × Shift → ℤ)
        (hrootLevel : ∀ (e : Enl) (t : Shift),
          rootLevel (e, t) = (k : ℤ) - (factor e : ℤ))
        (rootSide : Enl × Shift → ℝ)
        (hrootSide : ∀ (U : Enl × Shift),
          rootSide U = (3 : ℝ) ^ (-rootLevel U))
        (rootCentre : Enl × Shift → SpatialCoordinates d)
        (hrootCentre : ∀ (e : Enl) (t : Shift),
          rootCentre (e, t) = qcenter + rootSide (e, t) • shift t)
        (rootPos : ∀ (U : Enl × Shift), 0 < rootSide U)
        (hGridCover : ∀ (x : SpatialCoordinates d),
          x ∈ Metric.closedBall z (qside / 2) →
          ∀ rho : ℝ, 0 < rho → rho ≤ qside →
            ∃ (U : Enl × Shift) (D : ℕ) (w : Fin D → OddGridIndex d 1),
              Metric.ball x (rho / 2) ⊆
                Metric.ball (descendantCenter 1 (rootCentre U) (rootSide U) D w)
                  (descendantSide 1 D (rootSide U) / 2) ∧
              descendantSide 1 D (rootSide U) ≤ 9 * rho)
        (parent : Cmp → Enl × Shift)
        (depth : Cmp → ℕ)
        (word : (c : Cmp) → Fin (depth c) → OddGridIndex d 1)
        (cmpCentre : Cmp → SpatialCoordinates d)
        (hcmpCentre : ∀ (c : Cmp),
          cmpCentre c =
            descendantCenter 1 (rootCentre (parent c)) (rootSide (parent c))
              (depth c) (word c))
        (cmpLevel : Cmp → ℤ)
        (hcmpLevel : ∀ (c : Cmp),
          cmpLevel c = rootLevel (parent c) + (depth c : ℤ))
        (cmpSide : Cmp → ℝ)
        (hcmpSide : ∀ (c : Cmp), cmpSide c = (3 : ℝ) ^ (-cmpLevel c))
        (cmpPos : ∀ (c : Cmp), 0 < cmpSide c)
        (chosen : Cmp)
        (observationCentre : ∀ (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            SpatialCoordinates d)
        (hObservationCentre : ∀ (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          observationCentre U D code =
            Sum.elim
              (fun w => descendantCenter 1 (rootCentre U) (rootSide U) D w)
              (fun V => rootCentre V) code)
        (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d),
            eta N omega i y =
              omega ((i : ℤ) - (N : ℤ))
                (((3 : ℝ) ^ (-(N : ℤ))) • y))
        (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
        (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
        (hepsSmall : eps ≤ eps0)
        (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ N : ℕ,
            primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega)
              (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega)
              (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega)
              (fun m y => rawGood N m y omega))
        (lambdaCut lambdaLim lambdaDet cdet : ℝ)
        (hThresholds :
          0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
          lambdaLim < lambdaDet ∧ lambdaDet < 1)
        (hcdet : 0 < cdet) (hcdetSmall : cdet ≤ Cbound⁻¹)
        (hlamSmall : lambdaDet ≤ lam0)
        (hdisorder : M.delta ≤ delta0)
        (prefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (prefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (hPrefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixZ N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega
                else 0
            else 0)
        (hPrefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixD N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  (Draw N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega).toReal
                else 0
            else 0)
        (hFiniteScoreGuard : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
            (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
            rootLevel U + (D : ℤ) ≤ (N : ℤ) →
            ∀ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
              (rootLevel U + (D : ℤ)),
              Draw N ((N : ℤ) - j).toNat
                (((3 : ℝ) ^ N) • observationCentre U D code) omega ≠ ⊤)
        (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
        (hsN : ∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d)
          (omega : BilateralField d),
          sN N l w omega =
            if l ≤ (N : ℤ) then
              (let kappa : ℕ → ℝ := fun J =>
                Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
               let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
                 fun ell v beta =>
                   if 0 ≤ ell then
                     ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
                   else
                     -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
               kappa ((N : ℤ) - l).toNat / kappa N *
                 Real.exp (H omega w + retained l w omega))
            else 1)
        (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
        (hEllLoN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellLoN N U omega =
            I.lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (hEllHiN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellHiN N U omega =
            I.Lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (AEN : ℕ → Enl × Shift → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (hAEN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          AEN N U omega =
            (sN N (rootLevel U) (rootCentre U) omega)⁻¹ •
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain
                  (Homogenization.originCube d 0))
                ((I.chart (rootCentre U) (rootSide U) (rootPos U)
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (rootCentre U) (rootPos U))
                  (rootCentre U) (rootSide U)).coeffOn
                  (Homogenization.originCube d 0)))
        (errN ratioN : ℕ → Cmp → BilateralField d → ℝ)
        (hErrN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          errN N c omega =
            I.err (cmpCentre c) (cmpSide c) (cmpPos c)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (cmpCentre c) (cmpPos c))
              (cmpCentre c) (cmpSide c)
              (sN N (cmpLevel c) (cmpCentre c) omega) s 2)
        (hRatioN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          ratioN N c omega =
            sN N (k : ℤ) qcenter omega /
              sN N (cmpLevel c) (cmpCentre c) omega)
        (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
        (hRootsQ : ∀ U : Enl × Shift,
          closure (centeredCube (rootCentre U) (rootSide U) (rootPos U) :
            Set (SpatialCoordinates d)) ⊆
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ,
      let Q := centeredCube Qcentre Qside hQside
      let q := centeredCube qcenter qside hqpos
      let qp : Set (SpatialCoordinates d) := Metric.ball qcenter (3 * qside / 2)
      let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))
      let psource : ℝ := (d : ℝ) / (1 - alpha)
      ∀ (N : ℕ), k + k0 ≤ N → (∀ c : Cmp, cmpLevel c ≤ (N : ℤ)) →
        let harmonicComparison (omega : BilateralField d)
            (fNorm : Set (SpatialCoordinates d) → ℝ)
            (U : SpatialCoordinates d → ℝ) : Prop :=
          (let qc := centeredCube (cmpCentre chosen) (cmpSide chosen / 81)
                   (div_pos (cmpPos chosen) (by norm_num))
                 let qi : Set (SpatialCoordinates d) :=
                   Metric.ball (cmpCentre chosen) (cmpSide chosen / 1458)
                 let qo : Set (SpatialCoordinates d) :=
                   Metric.ball (cmpCentre chosen) (cmpSide chosen / 18)
                 ∀ w : SpatialCoordinates d,
                 let qd : Set (SpatialCoordinates d) :=
                   Metric.ball w (27 * cmpSide chosen / 2)
                 Metric.closedBall (cmpCentre chosen) (cmpSide chosen / 18) ⊆ qd →
                 qd ⊆ (Q : Set (SpatialCoordinates d)) →
                 ∃ (v : weakSobolevGraph qc) (V : SpatialCoordinates d → ℝ),
                   ContinuousOn V (closure (qc : Set (SpatialCoordinates d))) ∧
                   (((v : SobolevData qc).1 : SpatialCoordinates d → ℝ) =ᵐ[
                     volume.restrict (qc : Set (SpatialCoordinates d))] V) ∧
                   (∀ x ∈ frontier (qc : Set (SpatialCoordinates d)), V x = U x) ∧
                   (∀ psi : killedSobolevGraph qc,
                     inner ℝ (sobolevGradient (v : SobolevData qc))
                       (subspaceGradient (killedSobolevGraph qc) psi) = 0) ∧
                   normalizedL2On qi (fun x => U x - V x) ≤
                     epshom * normalizedL2On qo
                       (fun x => U x - (volume.real qo)⁻¹ * ∫ y in qo, U y) +
                     Ctotal * (cmpSide chosen / 9) ^ 2 *
                       (sN N (cmpLevel chosen) (cmpCentre chosen) omega)⁻¹ * fNorm qd)
        let traceEstimate (omega : BilateralField d) : Prop :=
          (∃ Uq : ℝ,
            Uq = I.Lam qcenter qside hqpos
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
              qcenter qside sigma 2 ∧
            Cbound⁻¹ * sN N (k : ℤ) qcenter omega ≤ Uq ∧
            Uq ≤ Cbound * sN N (k : ℤ) qcenter omega ∧
            ∀ b : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta qcenter qside b →
              ∃ (extension : weakSobolevGraph q) (B : SpatialCoordinates d → ℝ),
                ContinuousOn B (closure (q : Set (SpatialCoordinates d))) ∧
                (((extension : SobolevData q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (q : Set (SpatialCoordinates d))] B) ∧
                (∀ x ∈ frontier (q : Set (SpatialCoordinates d)), B x = b x) ∧
                ∀ (Sq : ResponseSpace q), Sq.space = killedSobolevGraph q →
                  dirichletResponse Sq
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
                    extension ≤
                    Cbound * Uq * qside ^ ((d : ℝ) - 2) *
                      cellBoundaryQuotientNorm beta qcenter qside b ^ 2)
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ horizon : ℕ,
          ((∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D → D ≤ horizon →
              rootLevel U + (D : ℤ) ≤ (N : ℤ) →
              ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
                prefixZ N U D code omega < lambdaCut * (D : ℝ) ∧
                prefixD N U D code omega < lambdaCut * (D : ℝ)) ∧
           (∀ U : Enl × Shift,
              cell ≤ ellLoN N U omega ∧ ellHiN N U omega ≤ cell⁻¹) ∧
           errN N chosen omega ≤ epshom * cdet ∧
           (∀ c : Cmp, ratioN N c omega ∈ Set.Icc (1 / 2 : ℝ) 2)) →
          ((∀ (Uroot : Enl × Shift) (D : ℕ), D ≤ horizon →
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              ((Finset.filter
                (fun j : ℤ => j < rootLevel Uroot + (k0 : ℤ) ∨
                  1 ≤ Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega)
                (Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                  (rootLevel Uroot + (D : ℤ)))).card : ℝ) ≤
                (k0 : ℝ) + (cbuf : ℝ) + lambdaDet * (D : ℝ)) ∧
          (∀ (Uroot : Enl × Shift) (D : ℕ), D ≤ horizon →
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              (∑ j ∈ Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                (rootLevel Uroot + (D : ℤ)),
                if rootLevel Uroot + (k0 : ℤ) ≤ j ∧
                    Z N ((N : ℤ) - j).toNat
                      (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega < 1 then
                  let w := observationCentre Uroot D code
                  let rj := (3 : ℝ) ^ (-j)
                  I.err w rj (by positivity)
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
                    w rj (sN N j w omega) s 2
                else 0) ≤
                  Cbound * (M.delta ^ 2 + eps ^ 8 + lambdaDet) * (D : ℝ) +
                    Cbound * ((k0 : ℝ) + (cbuf : ℝ)))) →
          (∀ (f : SpatialCoordinates d → ℝ),
            MemLp f (ENNReal.ofReal psource) (volume.restrict (Q : Set (SpatialCoordinates d))) →
            ∀ (fL2 : DomainL2 Q),
              ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                (Q : Set (SpatialCoordinates d))] f) →
            let fNorm : Set (SpatialCoordinates d) → ℝ := fun W =>
              (eLpNorm f (ENNReal.ofReal psource) (volume.restrict W)).toReal /
                (volume.real W) ^ (1 / psource)
            ∀ u : weakSobolevGraph Q,
              (∀ psi : killedSobolevGraph Q,
                sobolevCoefficientForm
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
                  (u : SobolevData Q) (psi : SobolevData Q) =
                sobolevVolumeLoad fL2 (psi : SobolevData Q)) →
              ∃ U : SpatialCoordinates d → ℝ,
                ContinuousOn U (Q : Set (SpatialCoordinates d)) ∧
                (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
                (∀ (D : ℕ), D ≤ horizon →
                  ∀ x ∈ (q : Set (SpatialCoordinates d)),
                    let B : Set (SpatialCoordinates d) :=
                      Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2) ∩
                        (q : Set (SpatialCoordinates d))
                    normalizedL2On B
                      (fun y => U y - (volume.real B)⁻¹ * ∫ t in B, U t) ≤
                      Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ))) *
                        (3 : ℝ) ^ (Cbound * (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)) *
                        (3 : ℝ) ^ (-(D : ℝ)) *
                        (normalizedL2On qp
                          (fun y => U y - (volume.real qp)⁻¹ * ∫ t in qp, U t) +
                          qside ^ 2 * (sN N (k : ℤ) qcenter omega)⁻¹ * fNorm qp)) ∧
                harmonicComparison omega fNorm U)

/-- **R2** (exact slice): on the full event with the full budget, subcriticality and `D0`,
every sourced native weak solution has a continuous representative that is `IsHolderOn alpha`
on `closure q`, with the rescaled `cAlphaNorm` bound at `Ctotal`, and the harmonic
comparison. -/
def aux_in_deterministic_regularity_R2
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell epshom : ℝ)
    (Cbound eps0 lam0 delta0 : ℝ) : Prop :=
      ∀ (cbuf k0 : ℕ)
        (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hMH : InfraredCharacterization M H)
        (k : ℕ) (z : SpatialCoordinates d)
        (qside : ℝ) (hqpos : 0 < qside)
        (hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
        (qcenter : SpatialCoordinates d)
        (hqcenter : qcenter = z)
        (Enl Shift Cmp : Type)
        [Fintype Enl] [Fintype Shift] [Fintype Cmp]
        (selfE : Enl) (selfShift : Shift)
        (qRoot : Enl × Shift)
        (hqRoot : qRoot = (selfE, selfShift))
        (factor : Enl → ℕ)
        (hfactor : factor selfE = 0)
        (padE : Enl) (hpad : factor padE = 1)
        (shift : Shift → SpatialCoordinates d)
        (hshift : shift selfShift = 0)
        (rootLevel : Enl × Shift → ℤ)
        (hrootLevel : ∀ (e : Enl) (t : Shift),
          rootLevel (e, t) = (k : ℤ) - (factor e : ℤ))
        (rootSide : Enl × Shift → ℝ)
        (hrootSide : ∀ (U : Enl × Shift),
          rootSide U = (3 : ℝ) ^ (-rootLevel U))
        (rootCentre : Enl × Shift → SpatialCoordinates d)
        (hrootCentre : ∀ (e : Enl) (t : Shift),
          rootCentre (e, t) = qcenter + rootSide (e, t) • shift t)
        (rootPos : ∀ (U : Enl × Shift), 0 < rootSide U)
        (hGridCover : ∀ (x : SpatialCoordinates d),
          x ∈ Metric.closedBall z (qside / 2) →
          ∀ rho : ℝ, 0 < rho → rho ≤ qside →
            ∃ (U : Enl × Shift) (D : ℕ) (w : Fin D → OddGridIndex d 1),
              Metric.ball x (rho / 2) ⊆
                Metric.ball (descendantCenter 1 (rootCentre U) (rootSide U) D w)
                  (descendantSide 1 D (rootSide U) / 2) ∧
              descendantSide 1 D (rootSide U) ≤ 9 * rho)
        (parent : Cmp → Enl × Shift)
        (depth : Cmp → ℕ)
        (word : (c : Cmp) → Fin (depth c) → OddGridIndex d 1)
        (cmpCentre : Cmp → SpatialCoordinates d)
        (hcmpCentre : ∀ (c : Cmp),
          cmpCentre c =
            descendantCenter 1 (rootCentre (parent c)) (rootSide (parent c))
              (depth c) (word c))
        (cmpLevel : Cmp → ℤ)
        (hcmpLevel : ∀ (c : Cmp),
          cmpLevel c = rootLevel (parent c) + (depth c : ℤ))
        (cmpSide : Cmp → ℝ)
        (hcmpSide : ∀ (c : Cmp), cmpSide c = (3 : ℝ) ^ (-cmpLevel c))
        (cmpPos : ∀ (c : Cmp), 0 < cmpSide c)
        (chosen : Cmp)
        (observationCentre : ∀ (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            SpatialCoordinates d)
        (hObservationCentre : ∀ (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          observationCentre U D code =
            Sum.elim
              (fun w => descendantCenter 1 (rootCentre U) (rootSide U) D w)
              (fun V => rootCentre V) code)
        (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d),
            eta N omega i y =
              omega ((i : ℤ) - (N : ℤ))
                (((3 : ℝ) ^ (-(N : ℤ))) • y))
        (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
        (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
        (hepsSmall : eps ≤ eps0)
        (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ N : ℕ,
            primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega)
              (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega)
              (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega)
              (fun m y => rawGood N m y omega))
        (lambdaCut lambdaLim lambdaDet cdet : ℝ)
        (hThresholds :
          0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
          lambdaLim < lambdaDet ∧ lambdaDet < 1)
        (hcdet : 0 < cdet) (hcdetSmall : cdet ≤ Cbound⁻¹)
        (hlamSmall : lambdaDet ≤ lam0)
        (hdisorder : M.delta ≤ delta0)
        (prefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (prefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (hPrefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixZ N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega
                else 0
            else 0)
        (hPrefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixD N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  (Draw N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega).toReal
                else 0
            else 0)
        (hFiniteScoreGuard : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
            (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
            rootLevel U + (D : ℤ) ≤ (N : ℤ) →
            ∀ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
              (rootLevel U + (D : ℤ)),
              Draw N ((N : ℤ) - j).toNat
                (((3 : ℝ) ^ N) • observationCentre U D code) omega ≠ ⊤)
        (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
        (hsN : ∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d)
          (omega : BilateralField d),
          sN N l w omega =
            if l ≤ (N : ℤ) then
              (let kappa : ℕ → ℝ := fun J =>
                Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
               let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
                 fun ell v beta =>
                   if 0 ≤ ell then
                     ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
                   else
                     -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
               kappa ((N : ℤ) - l).toNat / kappa N *
                 Real.exp (H omega w + retained l w omega))
            else 1)
        (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
        (hEllLoN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellLoN N U omega =
            I.lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (hEllHiN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellHiN N U omega =
            I.Lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (AEN : ℕ → Enl × Shift → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (hAEN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          AEN N U omega =
            (sN N (rootLevel U) (rootCentre U) omega)⁻¹ •
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain
                  (Homogenization.originCube d 0))
                ((I.chart (rootCentre U) (rootSide U) (rootPos U)
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (rootCentre U) (rootPos U))
                  (rootCentre U) (rootSide U)).coeffOn
                  (Homogenization.originCube d 0)))
        (errN ratioN : ℕ → Cmp → BilateralField d → ℝ)
        (hErrN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          errN N c omega =
            I.err (cmpCentre c) (cmpSide c) (cmpPos c)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (cmpCentre c) (cmpPos c))
              (cmpCentre c) (cmpSide c)
              (sN N (cmpLevel c) (cmpCentre c) omega) s 2)
        (hRatioN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          ratioN N c omega =
            sN N (k : ℤ) qcenter omega /
              sN N (cmpLevel c) (cmpCentre c) omega)
        (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
        (hRootsQ : ∀ U : Enl × Shift,
          closure (centeredCube (rootCentre U) (rootSide U) (rootPos U) :
            Set (SpatialCoordinates d)) ⊆
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ,
      let Q := centeredCube Qcentre Qside hQside
      let q := centeredCube qcenter qside hqpos
      let qp : Set (SpatialCoordinates d) := Metric.ball qcenter (3 * qside / 2)
      let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))
      let psource : ℝ := (d : ℝ) / (1 - alpha)
      ∀ (N : ℕ), k + k0 ≤ N → (∀ c : Cmp, cmpLevel c ≤ (N : ℤ)) →
        let harmonicComparison (omega : BilateralField d)
            (fNorm : Set (SpatialCoordinates d) → ℝ)
            (U : SpatialCoordinates d → ℝ) : Prop :=
          (let qc := centeredCube (cmpCentre chosen) (cmpSide chosen / 81)
                   (div_pos (cmpPos chosen) (by norm_num))
                 let qi : Set (SpatialCoordinates d) :=
                   Metric.ball (cmpCentre chosen) (cmpSide chosen / 1458)
                 let qo : Set (SpatialCoordinates d) :=
                   Metric.ball (cmpCentre chosen) (cmpSide chosen / 18)
                 ∀ w : SpatialCoordinates d,
                 let qd : Set (SpatialCoordinates d) :=
                   Metric.ball w (27 * cmpSide chosen / 2)
                 Metric.closedBall (cmpCentre chosen) (cmpSide chosen / 18) ⊆ qd →
                 qd ⊆ (Q : Set (SpatialCoordinates d)) →
                 ∃ (v : weakSobolevGraph qc) (V : SpatialCoordinates d → ℝ),
                   ContinuousOn V (closure (qc : Set (SpatialCoordinates d))) ∧
                   (((v : SobolevData qc).1 : SpatialCoordinates d → ℝ) =ᵐ[
                     volume.restrict (qc : Set (SpatialCoordinates d))] V) ∧
                   (∀ x ∈ frontier (qc : Set (SpatialCoordinates d)), V x = U x) ∧
                   (∀ psi : killedSobolevGraph qc,
                     inner ℝ (sobolevGradient (v : SobolevData qc))
                       (subspaceGradient (killedSobolevGraph qc) psi) = 0) ∧
                   normalizedL2On qi (fun x => U x - V x) ≤
                     epshom * normalizedL2On qo
                       (fun x => U x - (volume.real qo)⁻¹ * ∫ y in qo, U y) +
                     Ctotal * (cmpSide chosen / 9) ^ 2 *
                       (sN N (cmpLevel chosen) (cmpCentre chosen) omega)⁻¹ * fNorm qd)
        let traceEstimate (omega : BilateralField d) : Prop :=
          (∃ Uq : ℝ,
            Uq = I.Lam qcenter qside hqpos
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
              qcenter qside sigma 2 ∧
            Cbound⁻¹ * sN N (k : ℤ) qcenter omega ≤ Uq ∧
            Uq ≤ Cbound * sN N (k : ℤ) qcenter omega ∧
            ∀ b : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta qcenter qside b →
              ∃ (extension : weakSobolevGraph q) (B : SpatialCoordinates d → ℝ),
                ContinuousOn B (closure (q : Set (SpatialCoordinates d))) ∧
                (((extension : SobolevData q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (q : Set (SpatialCoordinates d))] B) ∧
                (∀ x ∈ frontier (q : Set (SpatialCoordinates d)), B x = b x) ∧
                ∀ (Sq : ResponseSpace q), Sq.space = killedSobolevGraph q →
                  dirichletResponse Sq
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
                    extension ≤
                    Cbound * Uq * qside ^ ((d : ℝ) - 2) *
                      cellBoundaryQuotientNorm beta qcenter qside b ^ 2)
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ((∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D →
              rootLevel U + (D : ℤ) ≤ (N : ℤ) →
              ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
                prefixZ N U D code omega < lambdaCut * (D : ℝ) ∧
                prefixD N U D code omega < lambdaCut * (D : ℝ)) ∧
           (∀ U : Enl × Shift,
              cell ≤ ellLoN N U omega ∧ ellHiN N U omega ≤ cell⁻¹) ∧
           errN N chosen omega ≤ epshom * cdet ∧
           (∀ c : Cmp, ratioN N c omega ∈ Set.Icc (1 / 2 : ℝ) 2)) →
          ((∀ (Uroot : Enl × Shift) (D : ℕ),
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              ((Finset.filter
                (fun j : ℤ => j < rootLevel Uroot + (k0 : ℤ) ∨
                  1 ≤ Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega)
                (Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                  (rootLevel Uroot + (D : ℤ)))).card : ℝ) ≤
                (k0 : ℝ) + (cbuf : ℝ) + lambdaDet * (D : ℝ)) ∧
          (∀ (Uroot : Enl × Shift) (D : ℕ),
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              (∑ j ∈ Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                (rootLevel Uroot + (D : ℤ)),
                if rootLevel Uroot + (k0 : ℤ) ≤ j ∧
                    Z N ((N : ℤ) - j).toNat
                      (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega < 1 then
                  let w := observationCentre Uroot D code
                  let rj := (3 : ℝ) ^ (-j)
                  I.err w rj (by positivity)
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
                    w rj (sN N j w omega) s 2
                else 0) ≤
                  Cbound * (M.delta ^ 2 + eps ^ 8 + lambdaDet) * (D : ℝ) +
                    Cbound * ((k0 : ℝ) + (cbuf : ℝ))) ∧
          Cbound * (lambdaDet + M.delta ^ 2 + eps ^ 8) < 1 - alpha ∧
          (∃ D0 : ℕ, k0 ≤ D0 ∧ ∀ D : ℕ, D0 ≤ D →
            (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ))) *
              (3 : ℝ) ^ (Cbound * (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)) ≤
                (3 : ℝ) ^ ((1 - alpha) * (D : ℝ)))) →
          (∀ (f : SpatialCoordinates d → ℝ),
            MemLp f (ENNReal.ofReal psource) (volume.restrict (Q : Set (SpatialCoordinates d))) →
            ∀ (fL2 : DomainL2 Q),
              ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                (Q : Set (SpatialCoordinates d))] f) →
            let fNorm : Set (SpatialCoordinates d) → ℝ := fun W =>
              (eLpNorm f (ENNReal.ofReal psource) (volume.restrict W)).toReal /
                (volume.real W) ^ (1 / psource)
            ∀ u : weakSobolevGraph Q,
              (∀ psi : killedSobolevGraph Q,
                sobolevCoefficientForm
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
                  (u : SobolevData Q) (psi : SobolevData Q) =
                sobolevVolumeLoad fL2 (psi : SobolevData Q)) →
              ∃ U : SpatialCoordinates d → ℝ,
                ContinuousOn U (Q : Set (SpatialCoordinates d)) ∧
                (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
                _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closure (q : Set (SpatialCoordinates d))) U ∧
                (∃ cq : ℝ,
                  _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
                    (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
                    (fun x => U (qcenter + qside • x) - cq) ≤
                      Ctotal * (normalizedL2On qp
                        (fun x => U x - (volume.real qp)⁻¹ * ∫ y in qp, U y) +
                        qside ^ 2 * (sN N (k : ℤ) qcenter omega)⁻¹ * fNorm qp)) ∧
                harmonicComparison omega fNorm U)

/-- **Core**: R1's conclusion with the Campanato loss at the analytic constant `C1`
(prefactor and exponent); premises and the harmonic comparison stay at `Cbound`. -/
def aux_in_deterministic_regularity_core
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell epshom : ℝ)
    (Cbound eps0 lam0 delta0 : ℝ) (C1 : ℝ) : Prop :=
      ∀ (cbuf k0 : ℕ)
        (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hMH : InfraredCharacterization M H)
        (k : ℕ) (z : SpatialCoordinates d)
        (qside : ℝ) (hqpos : 0 < qside)
        (hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
        (qcenter : SpatialCoordinates d)
        (hqcenter : qcenter = z)
        (Enl Shift Cmp : Type)
        [Fintype Enl] [Fintype Shift] [Fintype Cmp]
        (selfE : Enl) (selfShift : Shift)
        (qRoot : Enl × Shift)
        (hqRoot : qRoot = (selfE, selfShift))
        (factor : Enl → ℕ)
        (hfactor : factor selfE = 0)
        (padE : Enl) (hpad : factor padE = 1)
        (shift : Shift → SpatialCoordinates d)
        (hshift : shift selfShift = 0)
        (rootLevel : Enl × Shift → ℤ)
        (hrootLevel : ∀ (e : Enl) (t : Shift),
          rootLevel (e, t) = (k : ℤ) - (factor e : ℤ))
        (rootSide : Enl × Shift → ℝ)
        (hrootSide : ∀ (U : Enl × Shift),
          rootSide U = (3 : ℝ) ^ (-rootLevel U))
        (rootCentre : Enl × Shift → SpatialCoordinates d)
        (hrootCentre : ∀ (e : Enl) (t : Shift),
          rootCentre (e, t) = qcenter + rootSide (e, t) • shift t)
        (rootPos : ∀ (U : Enl × Shift), 0 < rootSide U)
        (hGridCover : ∀ (x : SpatialCoordinates d),
          x ∈ Metric.closedBall z (qside / 2) →
          ∀ rho : ℝ, 0 < rho → rho ≤ qside →
            ∃ (U : Enl × Shift) (D : ℕ) (w : Fin D → OddGridIndex d 1),
              Metric.ball x (rho / 2) ⊆
                Metric.ball (descendantCenter 1 (rootCentre U) (rootSide U) D w)
                  (descendantSide 1 D (rootSide U) / 2) ∧
              descendantSide 1 D (rootSide U) ≤ 9 * rho)
        (parent : Cmp → Enl × Shift)
        (depth : Cmp → ℕ)
        (word : (c : Cmp) → Fin (depth c) → OddGridIndex d 1)
        (cmpCentre : Cmp → SpatialCoordinates d)
        (hcmpCentre : ∀ (c : Cmp),
          cmpCentre c =
            descendantCenter 1 (rootCentre (parent c)) (rootSide (parent c))
              (depth c) (word c))
        (cmpLevel : Cmp → ℤ)
        (hcmpLevel : ∀ (c : Cmp),
          cmpLevel c = rootLevel (parent c) + (depth c : ℤ))
        (cmpSide : Cmp → ℝ)
        (hcmpSide : ∀ (c : Cmp), cmpSide c = (3 : ℝ) ^ (-cmpLevel c))
        (cmpPos : ∀ (c : Cmp), 0 < cmpSide c)
        (chosen : Cmp)
        (observationCentre : ∀ (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            SpatialCoordinates d)
        (hObservationCentre : ∀ (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          observationCentre U D code =
            Sum.elim
              (fun w => descendantCenter 1 (rootCentre U) (rootSide U) D w)
              (fun V => rootCentre V) code)
        (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d),
            eta N omega i y =
              omega ((i : ℤ) - (N : ℤ))
                (((3 : ℝ) ^ (-(N : ℤ))) • y))
        (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
        (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
        (hepsSmall : eps ≤ eps0)
        (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ N : ℕ,
            primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega)
              (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega)
              (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega)
              (fun m y => rawGood N m y omega))
        (lambdaCut lambdaLim lambdaDet cdet : ℝ)
        (hThresholds :
          0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
          lambdaLim < lambdaDet ∧ lambdaDet < 1)
        (hcdet : 0 < cdet) (hcdetSmall : cdet ≤ Cbound⁻¹)
        (hlamSmall : lambdaDet ≤ lam0)
        (hdisorder : M.delta ≤ delta0)
        (prefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (prefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (hPrefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixZ N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega
                else 0
            else 0)
        (hPrefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixD N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  (Draw N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega).toReal
                else 0
            else 0)
        (hFiniteScoreGuard : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
            (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
            rootLevel U + (D : ℤ) ≤ (N : ℤ) →
            ∀ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
              (rootLevel U + (D : ℤ)),
              Draw N ((N : ℤ) - j).toNat
                (((3 : ℝ) ^ N) • observationCentre U D code) omega ≠ ⊤)
        (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
        (hsN : ∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d)
          (omega : BilateralField d),
          sN N l w omega =
            if l ≤ (N : ℤ) then
              (let kappa : ℕ → ℝ := fun J =>
                Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
               let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
                 fun ell v beta =>
                   if 0 ≤ ell then
                     ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
                   else
                     -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
               kappa ((N : ℤ) - l).toNat / kappa N *
                 Real.exp (H omega w + retained l w omega))
            else 1)
        (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
        (hEllLoN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellLoN N U omega =
            I.lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (hEllHiN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellHiN N U omega =
            I.Lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (AEN : ℕ → Enl × Shift → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (hAEN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          AEN N U omega =
            (sN N (rootLevel U) (rootCentre U) omega)⁻¹ •
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain
                  (Homogenization.originCube d 0))
                ((I.chart (rootCentre U) (rootSide U) (rootPos U)
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (rootCentre U) (rootPos U))
                  (rootCentre U) (rootSide U)).coeffOn
                  (Homogenization.originCube d 0)))
        (errN ratioN : ℕ → Cmp → BilateralField d → ℝ)
        (hErrN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          errN N c omega =
            I.err (cmpCentre c) (cmpSide c) (cmpPos c)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (cmpCentre c) (cmpPos c))
              (cmpCentre c) (cmpSide c)
              (sN N (cmpLevel c) (cmpCentre c) omega) s 2)
        (hRatioN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          ratioN N c omega =
            sN N (k : ℤ) qcenter omega /
              sN N (cmpLevel c) (cmpCentre c) omega)
        (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
        (hRootsQ : ∀ U : Enl × Shift,
          closure (centeredCube (rootCentre U) (rootSide U) (rootPos U) :
            Set (SpatialCoordinates d)) ⊆
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ,
      let Q := centeredCube Qcentre Qside hQside
      let q := centeredCube qcenter qside hqpos
      let qp : Set (SpatialCoordinates d) := Metric.ball qcenter (3 * qside / 2)
      let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))
      let psource : ℝ := (d : ℝ) / (1 - alpha)
      ∀ (N : ℕ), k + k0 ≤ N → (∀ c : Cmp, cmpLevel c ≤ (N : ℤ)) →
        let harmonicComparison (omega : BilateralField d)
            (fNorm : Set (SpatialCoordinates d) → ℝ)
            (U : SpatialCoordinates d → ℝ) : Prop :=
          (let qc := centeredCube (cmpCentre chosen) (cmpSide chosen / 81)
                   (div_pos (cmpPos chosen) (by norm_num))
                 let qi : Set (SpatialCoordinates d) :=
                   Metric.ball (cmpCentre chosen) (cmpSide chosen / 1458)
                 let qo : Set (SpatialCoordinates d) :=
                   Metric.ball (cmpCentre chosen) (cmpSide chosen / 18)
                 ∀ w : SpatialCoordinates d,
                 let qd : Set (SpatialCoordinates d) :=
                   Metric.ball w (27 * cmpSide chosen / 2)
                 Metric.closedBall (cmpCentre chosen) (cmpSide chosen / 18) ⊆ qd →
                 qd ⊆ (Q : Set (SpatialCoordinates d)) →
                 ∃ (v : weakSobolevGraph qc) (V : SpatialCoordinates d → ℝ),
                   ContinuousOn V (closure (qc : Set (SpatialCoordinates d))) ∧
                   (((v : SobolevData qc).1 : SpatialCoordinates d → ℝ) =ᵐ[
                     volume.restrict (qc : Set (SpatialCoordinates d))] V) ∧
                   (∀ x ∈ frontier (qc : Set (SpatialCoordinates d)), V x = U x) ∧
                   (∀ psi : killedSobolevGraph qc,
                     inner ℝ (sobolevGradient (v : SobolevData qc))
                       (subspaceGradient (killedSobolevGraph qc) psi) = 0) ∧
                   normalizedL2On qi (fun x => U x - V x) ≤
                     epshom * normalizedL2On qo
                       (fun x => U x - (volume.real qo)⁻¹ * ∫ y in qo, U y) +
                     Ctotal * (cmpSide chosen / 9) ^ 2 *
                       (sN N (cmpLevel chosen) (cmpCentre chosen) omega)⁻¹ * fNorm qd)
        let traceEstimate (omega : BilateralField d) : Prop :=
          (∃ Uq : ℝ,
            Uq = I.Lam qcenter qside hqpos
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
              qcenter qside sigma 2 ∧
            Cbound⁻¹ * sN N (k : ℤ) qcenter omega ≤ Uq ∧
            Uq ≤ Cbound * sN N (k : ℤ) qcenter omega ∧
            ∀ b : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta qcenter qside b →
              ∃ (extension : weakSobolevGraph q) (B : SpatialCoordinates d → ℝ),
                ContinuousOn B (closure (q : Set (SpatialCoordinates d))) ∧
                (((extension : SobolevData q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (q : Set (SpatialCoordinates d))] B) ∧
                (∀ x ∈ frontier (q : Set (SpatialCoordinates d)), B x = b x) ∧
                ∀ (Sq : ResponseSpace q), Sq.space = killedSobolevGraph q →
                  dirichletResponse Sq
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
                    extension ≤
                    Cbound * Uq * qside ^ ((d : ℝ) - 2) *
                      cellBoundaryQuotientNorm beta qcenter qside b ^ 2)
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ horizon : ℕ,
          ((∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D → D ≤ horizon →
              rootLevel U + (D : ℤ) ≤ (N : ℤ) →
              ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
                prefixZ N U D code omega < lambdaCut * (D : ℝ) ∧
                prefixD N U D code omega < lambdaCut * (D : ℝ)) ∧
           (∀ U : Enl × Shift,
              cell ≤ ellLoN N U omega ∧ ellHiN N U omega ≤ cell⁻¹) ∧
           errN N chosen omega ≤ epshom * cdet ∧
           (∀ c : Cmp, ratioN N c omega ∈ Set.Icc (1 / 2 : ℝ) 2)) →
          ((∀ (Uroot : Enl × Shift) (D : ℕ), D ≤ horizon →
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              ((Finset.filter
                (fun j : ℤ => j < rootLevel Uroot + (k0 : ℤ) ∨
                  1 ≤ Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega)
                (Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                  (rootLevel Uroot + (D : ℤ)))).card : ℝ) ≤
                (k0 : ℝ) + (cbuf : ℝ) + lambdaDet * (D : ℝ)) ∧
          (∀ (Uroot : Enl × Shift) (D : ℕ), D ≤ horizon →
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              (∑ j ∈ Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                (rootLevel Uroot + (D : ℤ)),
                if rootLevel Uroot + (k0 : ℤ) ≤ j ∧
                    Z N ((N : ℤ) - j).toNat
                      (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega < 1 then
                  let w := observationCentre Uroot D code
                  let rj := (3 : ℝ) ^ (-j)
                  I.err w rj (by positivity)
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
                    w rj (sN N j w omega) s 2
                else 0) ≤
                  Cbound * (M.delta ^ 2 + eps ^ 8 + lambdaDet) * (D : ℝ) +
                    Cbound * ((k0 : ℝ) + (cbuf : ℝ)))) →
          (∀ (f : SpatialCoordinates d → ℝ),
            MemLp f (ENNReal.ofReal psource) (volume.restrict (Q : Set (SpatialCoordinates d))) →
            ∀ (fL2 : DomainL2 Q),
              ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                (Q : Set (SpatialCoordinates d))] f) →
            let fNorm : Set (SpatialCoordinates d) → ℝ := fun W =>
              (eLpNorm f (ENNReal.ofReal psource) (volume.restrict W)).toReal /
                (volume.real W) ^ (1 / psource)
            ∀ u : weakSobolevGraph Q,
              (∀ psi : killedSobolevGraph Q,
                sobolevCoefficientForm
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
                  (u : SobolevData Q) (psi : SobolevData Q) =
                sobolevVolumeLoad fL2 (psi : SobolevData Q)) →
              ∃ U : SpatialCoordinates d → ℝ,
                ContinuousOn U (Q : Set (SpatialCoordinates d)) ∧
                (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
                (∀ (D : ℕ), D ≤ horizon →
                  ∀ x ∈ (q : Set (SpatialCoordinates d)),
                    let B : Set (SpatialCoordinates d) :=
                      Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2) ∩
                        (q : Set (SpatialCoordinates d))
                    normalizedL2On B
                      (fun y => U y - (volume.real B)⁻¹ * ∫ t in B, U t) ≤
                      C1 * (3 : ℝ) ^ (C1 * ((k0 : ℝ) + (cbuf : ℝ))) *
                        (3 : ℝ) ^ (C1 * (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)) *
                        (3 : ℝ) ^ (-(D : ℝ)) *
                        (normalizedL2On qp
                          (fun y => U y - (volume.real qp)⁻¹ * ∫ t in qp, U t) +
                          qside ^ 2 * (sN N (k : ℤ) qcenter omega)⁻¹ * fNorm qp)) ∧
                harmonicComparison omega fNorm U)

/-- **Cont**: every sourced native weak solution on `Q` has a continuous representative on `Q`.
No event premise: at a fixed cutoff this is a deterministic interior regularity statement. -/
def aux_in_deterministic_regularity_cont
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma _cell epshom : ℝ)
    (Cbound eps0 lam0 delta0 : ℝ) : Prop :=
      ∀ (cbuf k0 : ℕ)
        (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hMH : InfraredCharacterization M H)
        (k : ℕ) (z : SpatialCoordinates d)
        (qside : ℝ) (hqpos : 0 < qside)
        (hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
        (qcenter : SpatialCoordinates d)
        (hqcenter : qcenter = z)
        (Enl Shift Cmp : Type)
        [Fintype Enl] [Fintype Shift] [Fintype Cmp]
        (selfE : Enl) (selfShift : Shift)
        (qRoot : Enl × Shift)
        (hqRoot : qRoot = (selfE, selfShift))
        (factor : Enl → ℕ)
        (hfactor : factor selfE = 0)
        (padE : Enl) (hpad : factor padE = 1)
        (shift : Shift → SpatialCoordinates d)
        (hshift : shift selfShift = 0)
        (rootLevel : Enl × Shift → ℤ)
        (hrootLevel : ∀ (e : Enl) (t : Shift),
          rootLevel (e, t) = (k : ℤ) - (factor e : ℤ))
        (rootSide : Enl × Shift → ℝ)
        (hrootSide : ∀ (U : Enl × Shift),
          rootSide U = (3 : ℝ) ^ (-rootLevel U))
        (rootCentre : Enl × Shift → SpatialCoordinates d)
        (hrootCentre : ∀ (e : Enl) (t : Shift),
          rootCentre (e, t) = qcenter + rootSide (e, t) • shift t)
        (rootPos : ∀ (U : Enl × Shift), 0 < rootSide U)
        (hGridCover : ∀ (x : SpatialCoordinates d),
          x ∈ Metric.closedBall z (qside / 2) →
          ∀ rho : ℝ, 0 < rho → rho ≤ qside →
            ∃ (U : Enl × Shift) (D : ℕ) (w : Fin D → OddGridIndex d 1),
              Metric.ball x (rho / 2) ⊆
                Metric.ball (descendantCenter 1 (rootCentre U) (rootSide U) D w)
                  (descendantSide 1 D (rootSide U) / 2) ∧
              descendantSide 1 D (rootSide U) ≤ 9 * rho)
        (parent : Cmp → Enl × Shift)
        (depth : Cmp → ℕ)
        (word : (c : Cmp) → Fin (depth c) → OddGridIndex d 1)
        (cmpCentre : Cmp → SpatialCoordinates d)
        (hcmpCentre : ∀ (c : Cmp),
          cmpCentre c =
            descendantCenter 1 (rootCentre (parent c)) (rootSide (parent c))
              (depth c) (word c))
        (cmpLevel : Cmp → ℤ)
        (hcmpLevel : ∀ (c : Cmp),
          cmpLevel c = rootLevel (parent c) + (depth c : ℤ))
        (cmpSide : Cmp → ℝ)
        (hcmpSide : ∀ (c : Cmp), cmpSide c = (3 : ℝ) ^ (-cmpLevel c))
        (cmpPos : ∀ (c : Cmp), 0 < cmpSide c)
        (chosen : Cmp)
        (observationCentre : ∀ (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            SpatialCoordinates d)
        (hObservationCentre : ∀ (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          observationCentre U D code =
            Sum.elim
              (fun w => descendantCenter 1 (rootCentre U) (rootSide U) D w)
              (fun V => rootCentre V) code)
        (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d),
            eta N omega i y =
              omega ((i : ℤ) - (N : ℤ))
                (((3 : ℝ) ^ (-(N : ℤ))) • y))
        (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
        (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
        (hepsSmall : eps ≤ eps0)
        (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ N : ℕ,
            primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega)
              (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega)
              (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega)
              (fun m y => rawGood N m y omega))
        (lambdaCut lambdaLim lambdaDet cdet : ℝ)
        (hThresholds :
          0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
          lambdaLim < lambdaDet ∧ lambdaDet < 1)
        (hcdet : 0 < cdet) (hcdetSmall : cdet ≤ Cbound⁻¹)
        (hlamSmall : lambdaDet ≤ lam0)
        (hdisorder : M.delta ≤ delta0)
        (prefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (prefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (hPrefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixZ N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega
                else 0
            else 0)
        (hPrefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixD N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  (Draw N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega).toReal
                else 0
            else 0)
        (hFiniteScoreGuard : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
            (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
            rootLevel U + (D : ℤ) ≤ (N : ℤ) →
            ∀ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
              (rootLevel U + (D : ℤ)),
              Draw N ((N : ℤ) - j).toNat
                (((3 : ℝ) ^ N) • observationCentre U D code) omega ≠ ⊤)
        (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
        (hsN : ∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d)
          (omega : BilateralField d),
          sN N l w omega =
            if l ≤ (N : ℤ) then
              (let kappa : ℕ → ℝ := fun J =>
                Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
               let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
                 fun ell v beta =>
                   if 0 ≤ ell then
                     ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
                   else
                     -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
               kappa ((N : ℤ) - l).toNat / kappa N *
                 Real.exp (H omega w + retained l w omega))
            else 1)
        (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
        (hEllLoN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellLoN N U omega =
            I.lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (hEllHiN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellHiN N U omega =
            I.Lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (AEN : ℕ → Enl × Shift → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (hAEN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          AEN N U omega =
            (sN N (rootLevel U) (rootCentre U) omega)⁻¹ •
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain
                  (Homogenization.originCube d 0))
                ((I.chart (rootCentre U) (rootSide U) (rootPos U)
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (rootCentre U) (rootPos U))
                  (rootCentre U) (rootSide U)).coeffOn
                  (Homogenization.originCube d 0)))
        (errN ratioN : ℕ → Cmp → BilateralField d → ℝ)
        (hErrN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          errN N c omega =
            I.err (cmpCentre c) (cmpSide c) (cmpPos c)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (cmpCentre c) (cmpPos c))
              (cmpCentre c) (cmpSide c)
              (sN N (cmpLevel c) (cmpCentre c) omega) s 2)
        (hRatioN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          ratioN N c omega =
            sN N (k : ℤ) qcenter omega /
              sN N (cmpLevel c) (cmpCentre c) omega)
        (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
        (hRootsQ : ∀ U : Enl × Shift,
          closure (centeredCube (rootCentre U) (rootSide U) (rootPos U) :
            Set (SpatialCoordinates d)) ⊆
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ,
      let Q := centeredCube Qcentre Qside hQside
      let q := centeredCube qcenter qside hqpos
      let qp : Set (SpatialCoordinates d) := Metric.ball qcenter (3 * qside / 2)
      let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))
      let psource : ℝ := (d : ℝ) / (1 - alpha)
      ∀ (N : ℕ), k + k0 ≤ N → (∀ c : Cmp, cmpLevel c ≤ (N : ℤ)) →
        let harmonicComparison (omega : BilateralField d)
            (fNorm : Set (SpatialCoordinates d) → ℝ)
            (U : SpatialCoordinates d → ℝ) : Prop :=
          (let qc := centeredCube (cmpCentre chosen) (cmpSide chosen / 81)
                   (div_pos (cmpPos chosen) (by norm_num))
                 let qi : Set (SpatialCoordinates d) :=
                   Metric.ball (cmpCentre chosen) (cmpSide chosen / 1458)
                 let qo : Set (SpatialCoordinates d) :=
                   Metric.ball (cmpCentre chosen) (cmpSide chosen / 18)
                 ∀ w : SpatialCoordinates d,
                 let qd : Set (SpatialCoordinates d) :=
                   Metric.ball w (27 * cmpSide chosen / 2)
                 Metric.closedBall (cmpCentre chosen) (cmpSide chosen / 18) ⊆ qd →
                 qd ⊆ (Q : Set (SpatialCoordinates d)) →
                 ∃ (v : weakSobolevGraph qc) (V : SpatialCoordinates d → ℝ),
                   ContinuousOn V (closure (qc : Set (SpatialCoordinates d))) ∧
                   (((v : SobolevData qc).1 : SpatialCoordinates d → ℝ) =ᵐ[
                     volume.restrict (qc : Set (SpatialCoordinates d))] V) ∧
                   (∀ x ∈ frontier (qc : Set (SpatialCoordinates d)), V x = U x) ∧
                   (∀ psi : killedSobolevGraph qc,
                     inner ℝ (sobolevGradient (v : SobolevData qc))
                       (subspaceGradient (killedSobolevGraph qc) psi) = 0) ∧
                   normalizedL2On qi (fun x => U x - V x) ≤
                     epshom * normalizedL2On qo
                       (fun x => U x - (volume.real qo)⁻¹ * ∫ y in qo, U y) +
                     Ctotal * (cmpSide chosen / 9) ^ 2 *
                       (sN N (cmpLevel chosen) (cmpCentre chosen) omega)⁻¹ * fNorm qd)
        let traceEstimate (omega : BilateralField d) : Prop :=
          (∃ Uq : ℝ,
            Uq = I.Lam qcenter qside hqpos
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
              qcenter qside sigma 2 ∧
            Cbound⁻¹ * sN N (k : ℤ) qcenter omega ≤ Uq ∧
            Uq ≤ Cbound * sN N (k : ℤ) qcenter omega ∧
            ∀ b : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta qcenter qside b →
              ∃ (extension : weakSobolevGraph q) (B : SpatialCoordinates d → ℝ),
                ContinuousOn B (closure (q : Set (SpatialCoordinates d))) ∧
                (((extension : SobolevData q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (q : Set (SpatialCoordinates d))] B) ∧
                (∀ x ∈ frontier (q : Set (SpatialCoordinates d)), B x = b x) ∧
                ∀ (Sq : ResponseSpace q), Sq.space = killedSobolevGraph q →
                  dirichletResponse Sq
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
                    extension ≤
                    Cbound * Uq * qside ^ ((d : ℝ) - 2) *
                      cellBoundaryQuotientNorm beta qcenter qside b ^ 2)
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          (∀ (f : SpatialCoordinates d → ℝ),
            MemLp f (ENNReal.ofReal psource) (volume.restrict (Q : Set (SpatialCoordinates d))) →
            ∀ (fL2 : DomainL2 Q),
              ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                (Q : Set (SpatialCoordinates d))] f) →
            let fNorm : Set (SpatialCoordinates d) → ℝ := fun W =>
              (eLpNorm f (ENNReal.ofReal psource) (volume.restrict W)).toReal /
                (volume.real W) ^ (1 / psource)
            ∀ u : weakSobolevGraph Q,
              (∀ psi : killedSobolevGraph Q,
                sobolevCoefficientForm
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
                  (u : SobolevData Q) (psi : SobolevData Q) =
                sobolevVolumeLoad fL2 (psi : SobolevData Q)) →
              ∃ U : SpatialCoordinates d → ℝ,
                ContinuousOn U (Q : Set (SpatialCoordinates d)) ∧
                (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (Q : Set (SpatialCoordinates d))] U))

/-- **Camp**: on the horizon event, every continuous representative of a sourced native weak
solution satisfies the finite-depth Campanato bound at loss
`C1·3^{C1(k0+cbuf)}·3^{C1·t·D}·3^{-D}`, for `D ≤ horizon`. -/
def aux_in_deterministic_regularity_camp
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell epshom : ℝ)
    (Cbound eps0 lam0 delta0 : ℝ) (C1 : ℝ) : Prop :=
      ∀ (cbuf k0 : ℕ)
        (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hMH : InfraredCharacterization M H)
        (k : ℕ) (z : SpatialCoordinates d)
        (qside : ℝ) (hqpos : 0 < qside)
        (hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
        (qcenter : SpatialCoordinates d)
        (hqcenter : qcenter = z)
        (Enl Shift Cmp : Type)
        [Fintype Enl] [Fintype Shift] [Fintype Cmp]
        (selfE : Enl) (selfShift : Shift)
        (qRoot : Enl × Shift)
        (hqRoot : qRoot = (selfE, selfShift))
        (factor : Enl → ℕ)
        (hfactor : factor selfE = 0)
        (padE : Enl) (hpad : factor padE = 1)
        (shift : Shift → SpatialCoordinates d)
        (hshift : shift selfShift = 0)
        (rootLevel : Enl × Shift → ℤ)
        (hrootLevel : ∀ (e : Enl) (t : Shift),
          rootLevel (e, t) = (k : ℤ) - (factor e : ℤ))
        (rootSide : Enl × Shift → ℝ)
        (hrootSide : ∀ (U : Enl × Shift),
          rootSide U = (3 : ℝ) ^ (-rootLevel U))
        (rootCentre : Enl × Shift → SpatialCoordinates d)
        (hrootCentre : ∀ (e : Enl) (t : Shift),
          rootCentre (e, t) = qcenter + rootSide (e, t) • shift t)
        (rootPos : ∀ (U : Enl × Shift), 0 < rootSide U)
        (hGridCover : ∀ (x : SpatialCoordinates d),
          x ∈ Metric.closedBall z (qside / 2) →
          ∀ rho : ℝ, 0 < rho → rho ≤ qside →
            ∃ (U : Enl × Shift) (D : ℕ) (w : Fin D → OddGridIndex d 1),
              Metric.ball x (rho / 2) ⊆
                Metric.ball (descendantCenter 1 (rootCentre U) (rootSide U) D w)
                  (descendantSide 1 D (rootSide U) / 2) ∧
              descendantSide 1 D (rootSide U) ≤ 9 * rho)
        (parent : Cmp → Enl × Shift)
        (depth : Cmp → ℕ)
        (word : (c : Cmp) → Fin (depth c) → OddGridIndex d 1)
        (cmpCentre : Cmp → SpatialCoordinates d)
        (hcmpCentre : ∀ (c : Cmp),
          cmpCentre c =
            descendantCenter 1 (rootCentre (parent c)) (rootSide (parent c))
              (depth c) (word c))
        (cmpLevel : Cmp → ℤ)
        (hcmpLevel : ∀ (c : Cmp),
          cmpLevel c = rootLevel (parent c) + (depth c : ℤ))
        (cmpSide : Cmp → ℝ)
        (hcmpSide : ∀ (c : Cmp), cmpSide c = (3 : ℝ) ^ (-cmpLevel c))
        (cmpPos : ∀ (c : Cmp), 0 < cmpSide c)
        (chosen : Cmp)
        (observationCentre : ∀ (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            SpatialCoordinates d)
        (hObservationCentre : ∀ (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          observationCentre U D code =
            Sum.elim
              (fun w => descendantCenter 1 (rootCentre U) (rootSide U) D w)
              (fun V => rootCentre V) code)
        (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d),
            eta N omega i y =
              omega ((i : ℤ) - (N : ℤ))
                (((3 : ℝ) ^ (-(N : ℤ))) • y))
        (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
        (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
        (hepsSmall : eps ≤ eps0)
        (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ N : ℕ,
            primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega)
              (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega)
              (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega)
              (fun m y => rawGood N m y omega))
        (lambdaCut lambdaLim lambdaDet cdet : ℝ)
        (hThresholds :
          0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
          lambdaLim < lambdaDet ∧ lambdaDet < 1)
        (hcdet : 0 < cdet) (hcdetSmall : cdet ≤ Cbound⁻¹)
        (hlamSmall : lambdaDet ≤ lam0)
        (hdisorder : M.delta ≤ delta0)
        (prefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (prefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (hPrefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixZ N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega
                else 0
            else 0)
        (hPrefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixD N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  (Draw N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega).toReal
                else 0
            else 0)
        (hFiniteScoreGuard : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
            (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
            rootLevel U + (D : ℤ) ≤ (N : ℤ) →
            ∀ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
              (rootLevel U + (D : ℤ)),
              Draw N ((N : ℤ) - j).toNat
                (((3 : ℝ) ^ N) • observationCentre U D code) omega ≠ ⊤)
        (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
        (hsN : ∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d)
          (omega : BilateralField d),
          sN N l w omega =
            if l ≤ (N : ℤ) then
              (let kappa : ℕ → ℝ := fun J =>
                Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
               let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
                 fun ell v beta =>
                   if 0 ≤ ell then
                     ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
                   else
                     -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
               kappa ((N : ℤ) - l).toNat / kappa N *
                 Real.exp (H omega w + retained l w omega))
            else 1)
        (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
        (hEllLoN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellLoN N U omega =
            I.lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (hEllHiN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellHiN N U omega =
            I.Lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (AEN : ℕ → Enl × Shift → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (hAEN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          AEN N U omega =
            (sN N (rootLevel U) (rootCentre U) omega)⁻¹ •
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain
                  (Homogenization.originCube d 0))
                ((I.chart (rootCentre U) (rootSide U) (rootPos U)
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (rootCentre U) (rootPos U))
                  (rootCentre U) (rootSide U)).coeffOn
                  (Homogenization.originCube d 0)))
        (errN ratioN : ℕ → Cmp → BilateralField d → ℝ)
        (hErrN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          errN N c omega =
            I.err (cmpCentre c) (cmpSide c) (cmpPos c)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (cmpCentre c) (cmpPos c))
              (cmpCentre c) (cmpSide c)
              (sN N (cmpLevel c) (cmpCentre c) omega) s 2)
        (hRatioN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          ratioN N c omega =
            sN N (k : ℤ) qcenter omega /
              sN N (cmpLevel c) (cmpCentre c) omega)
        (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
        (hRootsQ : ∀ U : Enl × Shift,
          closure (centeredCube (rootCentre U) (rootSide U) (rootPos U) :
            Set (SpatialCoordinates d)) ⊆
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ,
      let Q := centeredCube Qcentre Qside hQside
      let q := centeredCube qcenter qside hqpos
      let qp : Set (SpatialCoordinates d) := Metric.ball qcenter (3 * qside / 2)
      let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))
      let psource : ℝ := (d : ℝ) / (1 - alpha)
      ∀ (N : ℕ), k + k0 ≤ N → (∀ c : Cmp, cmpLevel c ≤ (N : ℤ)) →
        let harmonicComparison (omega : BilateralField d)
            (fNorm : Set (SpatialCoordinates d) → ℝ)
            (U : SpatialCoordinates d → ℝ) : Prop :=
          (let qc := centeredCube (cmpCentre chosen) (cmpSide chosen / 81)
                   (div_pos (cmpPos chosen) (by norm_num))
                 let qi : Set (SpatialCoordinates d) :=
                   Metric.ball (cmpCentre chosen) (cmpSide chosen / 1458)
                 let qo : Set (SpatialCoordinates d) :=
                   Metric.ball (cmpCentre chosen) (cmpSide chosen / 18)
                 ∀ w : SpatialCoordinates d,
                 let qd : Set (SpatialCoordinates d) :=
                   Metric.ball w (27 * cmpSide chosen / 2)
                 Metric.closedBall (cmpCentre chosen) (cmpSide chosen / 18) ⊆ qd →
                 qd ⊆ (Q : Set (SpatialCoordinates d)) →
                 ∃ (v : weakSobolevGraph qc) (V : SpatialCoordinates d → ℝ),
                   ContinuousOn V (closure (qc : Set (SpatialCoordinates d))) ∧
                   (((v : SobolevData qc).1 : SpatialCoordinates d → ℝ) =ᵐ[
                     volume.restrict (qc : Set (SpatialCoordinates d))] V) ∧
                   (∀ x ∈ frontier (qc : Set (SpatialCoordinates d)), V x = U x) ∧
                   (∀ psi : killedSobolevGraph qc,
                     inner ℝ (sobolevGradient (v : SobolevData qc))
                       (subspaceGradient (killedSobolevGraph qc) psi) = 0) ∧
                   normalizedL2On qi (fun x => U x - V x) ≤
                     epshom * normalizedL2On qo
                       (fun x => U x - (volume.real qo)⁻¹ * ∫ y in qo, U y) +
                     Ctotal * (cmpSide chosen / 9) ^ 2 *
                       (sN N (cmpLevel chosen) (cmpCentre chosen) omega)⁻¹ * fNorm qd)
        let traceEstimate (omega : BilateralField d) : Prop :=
          (∃ Uq : ℝ,
            Uq = I.Lam qcenter qside hqpos
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
              qcenter qside sigma 2 ∧
            Cbound⁻¹ * sN N (k : ℤ) qcenter omega ≤ Uq ∧
            Uq ≤ Cbound * sN N (k : ℤ) qcenter omega ∧
            ∀ b : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta qcenter qside b →
              ∃ (extension : weakSobolevGraph q) (B : SpatialCoordinates d → ℝ),
                ContinuousOn B (closure (q : Set (SpatialCoordinates d))) ∧
                (((extension : SobolevData q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (q : Set (SpatialCoordinates d))] B) ∧
                (∀ x ∈ frontier (q : Set (SpatialCoordinates d)), B x = b x) ∧
                ∀ (Sq : ResponseSpace q), Sq.space = killedSobolevGraph q →
                  dirichletResponse Sq
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
                    extension ≤
                    Cbound * Uq * qside ^ ((d : ℝ) - 2) *
                      cellBoundaryQuotientNorm beta qcenter qside b ^ 2)
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ horizon : ℕ,
          ((∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D → D ≤ horizon →
              rootLevel U + (D : ℤ) ≤ (N : ℤ) →
              ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
                prefixZ N U D code omega < lambdaCut * (D : ℝ) ∧
                prefixD N U D code omega < lambdaCut * (D : ℝ)) ∧
           (∀ U : Enl × Shift,
              cell ≤ ellLoN N U omega ∧ ellHiN N U omega ≤ cell⁻¹) ∧
           errN N chosen omega ≤ epshom * cdet ∧
           (∀ c : Cmp, ratioN N c omega ∈ Set.Icc (1 / 2 : ℝ) 2)) →
          ((∀ (Uroot : Enl × Shift) (D : ℕ), D ≤ horizon →
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              ((Finset.filter
                (fun j : ℤ => j < rootLevel Uroot + (k0 : ℤ) ∨
                  1 ≤ Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega)
                (Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                  (rootLevel Uroot + (D : ℤ)))).card : ℝ) ≤
                (k0 : ℝ) + (cbuf : ℝ) + lambdaDet * (D : ℝ)) ∧
          (∀ (Uroot : Enl × Shift) (D : ℕ), D ≤ horizon →
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              (∑ j ∈ Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                (rootLevel Uroot + (D : ℤ)),
                if rootLevel Uroot + (k0 : ℤ) ≤ j ∧
                    Z N ((N : ℤ) - j).toNat
                      (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega < 1 then
                  let w := observationCentre Uroot D code
                  let rj := (3 : ℝ) ^ (-j)
                  I.err w rj (by positivity)
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
                    w rj (sN N j w omega) s 2
                else 0) ≤
                  Cbound * (M.delta ^ 2 + eps ^ 8 + lambdaDet) * (D : ℝ) +
                    Cbound * ((k0 : ℝ) + (cbuf : ℝ)))) →
          (∀ (f : SpatialCoordinates d → ℝ),
            MemLp f (ENNReal.ofReal psource) (volume.restrict (Q : Set (SpatialCoordinates d))) →
            ∀ (fL2 : DomainL2 Q),
              ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                (Q : Set (SpatialCoordinates d))] f) →
            let fNorm : Set (SpatialCoordinates d) → ℝ := fun W =>
              (eLpNorm f (ENNReal.ofReal psource) (volume.restrict W)).toReal /
                (volume.real W) ^ (1 / psource)
            ∀ u : weakSobolevGraph Q,
              (∀ psi : killedSobolevGraph Q,
                sobolevCoefficientForm
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
                  (u : SobolevData Q) (psi : SobolevData Q) =
                sobolevVolumeLoad fL2 (psi : SobolevData Q)) →
              ∀ U : SpatialCoordinates d → ℝ,
                ContinuousOn U (Q : Set (SpatialCoordinates d)) →
                (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (Q : Set (SpatialCoordinates d))] U) →
                (∀ (D : ℕ), D ≤ horizon →
                  ∀ x ∈ (q : Set (SpatialCoordinates d)),
                    let B : Set (SpatialCoordinates d) :=
                      Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2) ∩
                        (q : Set (SpatialCoordinates d))
                    normalizedL2On B
                      (fun y => U y - (volume.real B)⁻¹ * ∫ t in B, U t) ≤
                      C1 * (3 : ℝ) ^ (C1 * ((k0 : ℝ) + (cbuf : ℝ))) *
                        (3 : ℝ) ^ (C1 * (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)) *
                        (3 : ℝ) ^ (-(D : ℝ)) *
                        (normalizedL2On qp
                          (fun y => U y - (volume.real qp)⁻¹ * ∫ t in qp, U t) +
                          qside ^ 2 * (sN N (k : ℤ) qcenter omega)⁻¹ * fNorm qp)))



def aux_in_deterministic_regularity_harm
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell epshom : ℝ)
    (Cbound eps0 lam0 delta0 : ℝ) : Prop :=
      ∀ (cbuf k0 : ℕ)
        (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hMH : InfraredCharacterization M H)
        (k : ℕ) (z : SpatialCoordinates d)
        (qside : ℝ) (hqpos : 0 < qside)
        (hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
        (qcenter : SpatialCoordinates d)
        (hqcenter : qcenter = z)
        (Enl Shift Cmp : Type)
        [Fintype Enl] [Fintype Shift] [Fintype Cmp]
        (selfE : Enl) (selfShift : Shift)
        (qRoot : Enl × Shift)
        (hqRoot : qRoot = (selfE, selfShift))
        (factor : Enl → ℕ)
        (hfactor : factor selfE = 0)
        (padE : Enl) (hpad : factor padE = 1)
        (shift : Shift → SpatialCoordinates d)
        (hshift : shift selfShift = 0)
        (rootLevel : Enl × Shift → ℤ)
        (hrootLevel : ∀ (e : Enl) (t : Shift),
          rootLevel (e, t) = (k : ℤ) - (factor e : ℤ))
        (rootSide : Enl × Shift → ℝ)
        (hrootSide : ∀ (U : Enl × Shift),
          rootSide U = (3 : ℝ) ^ (-rootLevel U))
        (rootCentre : Enl × Shift → SpatialCoordinates d)
        (hrootCentre : ∀ (e : Enl) (t : Shift),
          rootCentre (e, t) = qcenter + rootSide (e, t) • shift t)
        (rootPos : ∀ (U : Enl × Shift), 0 < rootSide U)
        (hGridCover : ∀ (x : SpatialCoordinates d),
          x ∈ Metric.closedBall z (qside / 2) →
          ∀ rho : ℝ, 0 < rho → rho ≤ qside →
            ∃ (U : Enl × Shift) (D : ℕ) (w : Fin D → OddGridIndex d 1),
              Metric.ball x (rho / 2) ⊆
                Metric.ball (descendantCenter 1 (rootCentre U) (rootSide U) D w)
                  (descendantSide 1 D (rootSide U) / 2) ∧
              descendantSide 1 D (rootSide U) ≤ 9 * rho)
        (parent : Cmp → Enl × Shift)
        (depth : Cmp → ℕ)
        (word : (c : Cmp) → Fin (depth c) → OddGridIndex d 1)
        (cmpCentre : Cmp → SpatialCoordinates d)
        (hcmpCentre : ∀ (c : Cmp),
          cmpCentre c =
            descendantCenter 1 (rootCentre (parent c)) (rootSide (parent c))
              (depth c) (word c))
        (cmpLevel : Cmp → ℤ)
        (hcmpLevel : ∀ (c : Cmp),
          cmpLevel c = rootLevel (parent c) + (depth c : ℤ))
        (cmpSide : Cmp → ℝ)
        (hcmpSide : ∀ (c : Cmp), cmpSide c = (3 : ℝ) ^ (-cmpLevel c))
        (cmpPos : ∀ (c : Cmp), 0 < cmpSide c)
        (chosen : Cmp)
        (observationCentre : ∀ (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            SpatialCoordinates d)
        (hObservationCentre : ∀ (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          observationCentre U D code =
            Sum.elim
              (fun w => descendantCenter 1 (rootCentre U) (rootSide U) D w)
              (fun V => rootCentre V) code)
        (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d),
            eta N omega i y =
              omega ((i : ℤ) - (N : ℤ))
                (((3 : ℝ) ^ (-(N : ℤ))) • y))
        (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
        (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
        (hepsSmall : eps ≤ eps0)
        (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ N : ℕ,
            primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega)
              (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega)
              (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega)
              (fun m y => rawGood N m y omega))
        (lambdaCut lambdaLim lambdaDet cdet : ℝ)
        (hThresholds :
          0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
          lambdaLim < lambdaDet ∧ lambdaDet < 1)
        (hcdet : 0 < cdet) (hcdetSmall : cdet ≤ Cbound⁻¹)
        (hlamSmall : lambdaDet ≤ lam0)
        (hdisorder : M.delta ≤ delta0)
        (prefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (prefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (hPrefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixZ N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega
                else 0
            else 0)
        (hPrefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixD N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  (Draw N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega).toReal
                else 0
            else 0)
        (hFiniteScoreGuard : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
            (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
            rootLevel U + (D : ℤ) ≤ (N : ℤ) →
            ∀ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
              (rootLevel U + (D : ℤ)),
              Draw N ((N : ℤ) - j).toNat
                (((3 : ℝ) ^ N) • observationCentre U D code) omega ≠ ⊤)
        (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
        (hsN : ∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d)
          (omega : BilateralField d),
          sN N l w omega =
            if l ≤ (N : ℤ) then
              (let kappa : ℕ → ℝ := fun J =>
                Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
               let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
                 fun ell v beta =>
                   if 0 ≤ ell then
                     ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
                   else
                     -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
               kappa ((N : ℤ) - l).toNat / kappa N *
                 Real.exp (H omega w + retained l w omega))
            else 1)
        (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
        (hEllLoN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellLoN N U omega =
            I.lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (hEllHiN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellHiN N U omega =
            I.Lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (AEN : ℕ → Enl × Shift → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (hAEN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          AEN N U omega =
            (sN N (rootLevel U) (rootCentre U) omega)⁻¹ •
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain
                  (Homogenization.originCube d 0))
                ((I.chart (rootCentre U) (rootSide U) (rootPos U)
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (rootCentre U) (rootPos U))
                  (rootCentre U) (rootSide U)).coeffOn
                  (Homogenization.originCube d 0)))
        (errN ratioN : ℕ → Cmp → BilateralField d → ℝ)
        (hErrN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          errN N c omega =
            I.err (cmpCentre c) (cmpSide c) (cmpPos c)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (cmpCentre c) (cmpPos c))
              (cmpCentre c) (cmpSide c)
              (sN N (cmpLevel c) (cmpCentre c) omega) s 2)
        (hRatioN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          ratioN N c omega =
            sN N (k : ℤ) qcenter omega /
              sN N (cmpLevel c) (cmpCentre c) omega)
        (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
        (hRootsQ : ∀ U : Enl × Shift,
          closure (centeredCube (rootCentre U) (rootSide U) (rootPos U) :
            Set (SpatialCoordinates d)) ⊆
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ,
      let Q := centeredCube Qcentre Qside hQside
      let q := centeredCube qcenter qside hqpos
      let qp : Set (SpatialCoordinates d) := Metric.ball qcenter (3 * qside / 2)
      let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))
      let psource : ℝ := (d : ℝ) / (1 - alpha)
      ∀ (N : ℕ), k + k0 ≤ N → (∀ c : Cmp, cmpLevel c ≤ (N : ℤ)) →
        let harmonicComparison (omega : BilateralField d)
            (fNorm : Set (SpatialCoordinates d) → ℝ)
            (U : SpatialCoordinates d → ℝ) : Prop :=
          (let qc := centeredCube (cmpCentre chosen) (cmpSide chosen / 81)
                   (div_pos (cmpPos chosen) (by norm_num))
                 let qi : Set (SpatialCoordinates d) :=
                   Metric.ball (cmpCentre chosen) (cmpSide chosen / 1458)
                 let qo : Set (SpatialCoordinates d) :=
                   Metric.ball (cmpCentre chosen) (cmpSide chosen / 18)
                 ∀ w : SpatialCoordinates d,
                 let qd : Set (SpatialCoordinates d) :=
                   Metric.ball w (27 * cmpSide chosen / 2)
                 Metric.closedBall (cmpCentre chosen) (cmpSide chosen / 18) ⊆ qd →
                 qd ⊆ (Q : Set (SpatialCoordinates d)) →
                 ∃ (v : weakSobolevGraph qc) (V : SpatialCoordinates d → ℝ),
                   ContinuousOn V (closure (qc : Set (SpatialCoordinates d))) ∧
                   (((v : SobolevData qc).1 : SpatialCoordinates d → ℝ) =ᵐ[
                     volume.restrict (qc : Set (SpatialCoordinates d))] V) ∧
                   (∀ x ∈ frontier (qc : Set (SpatialCoordinates d)), V x = U x) ∧
                   (∀ psi : killedSobolevGraph qc,
                     inner ℝ (sobolevGradient (v : SobolevData qc))
                       (subspaceGradient (killedSobolevGraph qc) psi) = 0) ∧
                   normalizedL2On qi (fun x => U x - V x) ≤
                     epshom * normalizedL2On qo
                       (fun x => U x - (volume.real qo)⁻¹ * ∫ y in qo, U y) +
                     Ctotal * (cmpSide chosen / 9) ^ 2 *
                       (sN N (cmpLevel chosen) (cmpCentre chosen) omega)⁻¹ * fNorm qd)
        let traceEstimate (omega : BilateralField d) : Prop :=
          (∃ Uq : ℝ,
            Uq = I.Lam qcenter qside hqpos
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
              qcenter qside sigma 2 ∧
            Cbound⁻¹ * sN N (k : ℤ) qcenter omega ≤ Uq ∧
            Uq ≤ Cbound * sN N (k : ℤ) qcenter omega ∧
            ∀ b : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta qcenter qside b →
              ∃ (extension : weakSobolevGraph q) (B : SpatialCoordinates d → ℝ),
                ContinuousOn B (closure (q : Set (SpatialCoordinates d))) ∧
                (((extension : SobolevData q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (q : Set (SpatialCoordinates d))] B) ∧
                (∀ x ∈ frontier (q : Set (SpatialCoordinates d)), B x = b x) ∧
                ∀ (Sq : ResponseSpace q), Sq.space = killedSobolevGraph q →
                  dirichletResponse Sq
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
                    extension ≤
                    Cbound * Uq * qside ^ ((d : ℝ) - 2) *
                      cellBoundaryQuotientNorm beta qcenter qside b ^ 2)
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ horizon : ℕ,
          ((∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D → D ≤ horizon →
              rootLevel U + (D : ℤ) ≤ (N : ℤ) →
              ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
                prefixZ N U D code omega < lambdaCut * (D : ℝ) ∧
                prefixD N U D code omega < lambdaCut * (D : ℝ)) ∧
           (∀ U : Enl × Shift,
              cell ≤ ellLoN N U omega ∧ ellHiN N U omega ≤ cell⁻¹) ∧
           errN N chosen omega ≤ epshom * cdet ∧
           (∀ c : Cmp, ratioN N c omega ∈ Set.Icc (1 / 2 : ℝ) 2)) →
          ((∀ (Uroot : Enl × Shift) (D : ℕ), D ≤ horizon →
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              ((Finset.filter
                (fun j : ℤ => j < rootLevel Uroot + (k0 : ℤ) ∨
                  1 ≤ Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega)
                (Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                  (rootLevel Uroot + (D : ℤ)))).card : ℝ) ≤
                (k0 : ℝ) + (cbuf : ℝ) + lambdaDet * (D : ℝ)) ∧
          (∀ (Uroot : Enl × Shift) (D : ℕ), D ≤ horizon →
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              (∑ j ∈ Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                (rootLevel Uroot + (D : ℤ)),
                if rootLevel Uroot + (k0 : ℤ) ≤ j ∧
                    Z N ((N : ℤ) - j).toNat
                      (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega < 1 then
                  let w := observationCentre Uroot D code
                  let rj := (3 : ℝ) ^ (-j)
                  I.err w rj (by positivity)
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
                    w rj (sN N j w omega) s 2
                else 0) ≤
                  Cbound * (M.delta ^ 2 + eps ^ 8 + lambdaDet) * (D : ℝ) +
                    Cbound * ((k0 : ℝ) + (cbuf : ℝ)))) →
          (∀ (f : SpatialCoordinates d → ℝ),
            MemLp f (ENNReal.ofReal psource) (volume.restrict (Q : Set (SpatialCoordinates d))) →
            ∀ (fL2 : DomainL2 Q),
              ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                (Q : Set (SpatialCoordinates d))] f) →
            let fNorm : Set (SpatialCoordinates d) → ℝ := fun W =>
              (eLpNorm f (ENNReal.ofReal psource) (volume.restrict W)).toReal /
                (volume.real W) ^ (1 / psource)
            ∀ u : weakSobolevGraph Q,
              (∀ psi : killedSobolevGraph Q,
                sobolevCoefficientForm
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
                  (u : SobolevData Q) (psi : SobolevData Q) =
                sobolevVolumeLoad fL2 (psi : SobolevData Q)) →
              ∀ U : SpatialCoordinates d → ℝ,
                ContinuousOn U (Q : Set (SpatialCoordinates d)) →
                (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (Q : Set (SpatialCoordinates d))] U) →
                harmonicComparison omega fNorm U)

/-! ## Reductions -/

/-- `core` is exactly `cont ∧ camp ∧ harm`. -/
theorem aux_in_deterministic_regularity_core_of_parts
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell epshom : ℝ)
    (Cbound eps0 lam0 delta0 : ℝ) (C1 : ℝ)
    (hC : aux_in_deterministic_regularity_cont d I alpha beta s sigma cell epshom Cbound eps0 lam0 delta0)
    (hP : aux_in_deterministic_regularity_camp d I alpha beta s sigma cell epshom Cbound eps0 lam0 delta0 C1)
    (hH : aux_in_deterministic_regularity_harm d I alpha beta s sigma cell epshom Cbound eps0 lam0 delta0) :
    aux_in_deterministic_regularity_core d I alpha beta s sigma cell epshom Cbound eps0 lam0 delta0 C1 := by
  intro cbuf k0 M H hMH k z qside hqpos hqside qcenter hqcenter Enl Shift Cmp _ _ _
    selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift rootLevel hrootLevel
    rootSide hrootSide rootCentre hrootCentre rootPos hGridCover parent depth word cmpCentre
    hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre
    hObservationCentre eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
    lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hdisorder
    prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN hEllHiN
    AEN hAEN errN ratioN hErrN hRatioN Qcentre Qside hQside hRootsQ
    Q q qp Ctotal psource N hkN hcmp harmonicComparison traceEstimate
  have a1 := hC cbuf k0 M H hMH k z qside hqpos hqside qcenter hqcenter Enl Shift Cmp
      selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift rootLevel hrootLevel
      rootSide hrootSide rootCentre hrootCentre rootPos hGridCover parent depth word cmpCentre
      hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre
      hObservationCentre eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
      lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hdisorder
      prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN hEllHiN
      AEN hAEN errN ratioN hErrN hRatioN Qcentre Qside hQside hRootsQ N hkN hcmp
  have a2 := hP cbuf k0 M H hMH k z qside hqpos hqside qcenter hqcenter Enl Shift Cmp
      selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift rootLevel hrootLevel
      rootSide hrootSide rootCentre hrootCentre rootPos hGridCover parent depth word cmpCentre
      hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre
      hObservationCentre eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
      lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hdisorder
      prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN hEllHiN
      AEN hAEN errN ratioN hErrN hRatioN Qcentre Qside hQside hRootsQ N hkN hcmp
  have a3 := hH cbuf k0 M H hMH k z qside hqpos hqside qcenter hqcenter Enl Shift Cmp
      selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift rootLevel hrootLevel
      rootSide hrootSide rootCentre hrootCentre rootPos hGridCover parent depth word cmpCentre
      hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre
      hObservationCentre eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
      lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hdisorder
      prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN hEllHiN
      AEN hAEN errN ratioN hErrN hRatioN Qcentre Qside hQside hRootsQ N hkN hcmp
  filter_upwards [a1, a2, a3] with omega b1 b2 b3
  intro horizon hev hb f hf fL2 hfL2 fNorm u hu
  obtain ⟨U, hUc, hUae⟩ := b1 f hf fL2 hfL2 u hu
  exact ⟨U, hUc, hUae, b2 horizon hev hb f hf fL2 hfL2 u hu U hUc hUae,
    b3 horizon hev hb f hf fL2 hfL2 u hu U hUc hUae⟩

/-- The reference scalar is positive. -/
theorem aux_in_deterministic_regularity_sN_pos {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
        (hsN : ∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d)
          (omega : BilateralField d),
          sN N l w omega =
            if l ≤ (N : ℤ) then
              (let kappa : ℕ → ℝ := fun J =>
                Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
               let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
                 fun ell v beta =>
                   if 0 ≤ ell then
                     ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
                   else
                     -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
               kappa ((N : ℤ) - l).toNat / kappa N *
                 Real.exp (H omega w + retained l w omega))
            else 1) :
    ∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d) (omega : BilateralField d),
      0 < sN N l w omega := by
  intro N l w omega
  rw [hsN]
  split_ifs
  · dsimp only
    exact mul_pos (div_pos (mul_pos (Real.exp_pos _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _))
      (mul_pos (Real.exp_pos _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _))) (Real.exp_pos _)
  · exact one_pos

/-- Monotonicity of the explicit loss in the analytic constant. -/
theorem aux_in_deterministic_regularity_loss_mono (C1 Cb a t D R : ℝ) (h0 : 0 ≤ C1)
    (h1 : C1 ≤ Cb) (ha : 0 ≤ a) (ht : 0 ≤ t) (hD : 0 ≤ D) (hR : 0 ≤ R) :
    C1 * (3 : ℝ) ^ (C1 * a) * (3 : ℝ) ^ (C1 * t * D) * (3 : ℝ) ^ (-D) * R ≤
      Cb * (3 : ℝ) ^ (Cb * a) * (3 : ℝ) ^ (Cb * t * D) * (3 : ℝ) ^ (-D) * R := by
  have e1 : (3 : ℝ) ^ (C1 * a) ≤ (3 : ℝ) ^ (Cb * a) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_right h1 ha)
  have e2 : (3 : ℝ) ^ (C1 * t * D) ≤ (3 : ℝ) ^ (Cb * t * D) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 ht) hD)
  have p1 : 0 ≤ (3 : ℝ) ^ (C1 * a) := by positivity
  have p2 : 0 ≤ (3 : ℝ) ^ (C1 * t * D) := by positivity
  have p3 : 0 ≤ (3 : ℝ) ^ (-D) := by positivity
  have p4 : 0 ≤ (3 : ℝ) ^ (Cb * a) := by positivity
  have s1 : C1 * (3 : ℝ) ^ (C1 * a) ≤ Cb * (3 : ℝ) ^ (Cb * a) := mul_le_mul h1 e1 p1 (h0.trans h1)
  have s2 : C1 * (3 : ℝ) ^ (C1 * a) * (3 : ℝ) ^ (C1 * t * D) ≤
      Cb * (3 : ℝ) ^ (Cb * a) * (3 : ℝ) ^ (Cb * t * D) :=
    mul_le_mul s1 e2 p2 (mul_nonneg (h0.trans h1) p4)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right s2 p3) hR

/-- **R1 from the core**, for any analytic constant `0 ≤ C1 ≤ Cbound`. -/
theorem aux_in_deterministic_regularity_R1_of_core
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell epshom : ℝ)
    (Cbound eps0 lam0 delta0 : ℝ) (C1 : ℝ) (hC1 : 0 ≤ C1) (hC1b : C1 ≤ Cbound)
    (hcore : aux_in_deterministic_regularity_core d I alpha beta s sigma cell epshom Cbound eps0 lam0 delta0 C1) :
    aux_in_deterministic_regularity_R1 d I alpha beta s sigma cell epshom Cbound eps0 lam0 delta0 := by
  intro cbuf k0 M H hMH k z qside hqpos hqside qcenter hqcenter Enl Shift Cmp _ _ _
    selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift rootLevel hrootLevel
    rootSide hrootSide rootCentre hrootCentre rootPos hGridCover parent depth word cmpCentre
    hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre
    hObservationCentre eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
    lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hdisorder
    prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN hEllHiN
    AEN hAEN errN ratioN hErrN hRatioN Qcentre Qside hQside hRootsQ
    Q q qp Ctotal psource N hkN hcmp harmonicComparison traceEstimate
  have a1 := hcore cbuf k0 M H hMH k z qside hqpos hqside qcenter hqcenter Enl Shift Cmp
      selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift rootLevel hrootLevel
      rootSide hrootSide rootCentre hrootCentre rootPos hGridCover parent depth word cmpCentre
      hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre
      hObservationCentre eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
      lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hdisorder
      prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN hEllHiN
      AEN hAEN errN ratioN hErrN hRatioN Qcentre Qside hQside hRootsQ N hkN hcmp
  have hsNpos := aux_in_deterministic_regularity_sN_pos M H sN hsN
  have ht : 0 ≤ lambdaDet + M.delta ^ 2 + eps ^ 8 := by
    have : 0 < lambdaDet := hThresholds.1.trans (hThresholds.2.1.trans hThresholds.2.2.1)
    positivity
  filter_upwards [a1] with omega b1
  intro horizon hev hb f hf fL2 hfL2 fNorm u hu
  obtain ⟨U, hUc, hUae, hcamp, hharm⟩ := b1 horizon hev hb f hf fL2 hfL2 u hu
  refine ⟨U, hUc, hUae, fun D hD x hx => ?_, hharm⟩
  have hfN : 0 ≤ fNorm qp := div_nonneg ENNReal.toReal_nonneg
    (Real.rpow_nonneg measureReal_nonneg _)
  have hR : 0 ≤ normalizedL2On qp (fun y => U y - (volume.real qp)⁻¹ * ∫ t in qp, U t) +
      qside ^ 2 * (sN N (k : ℤ) qcenter omega)⁻¹ * fNorm qp :=
    add_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (mul_nonneg (sq_nonneg _) (inv_nonneg.2 (hsNpos _ _ _ _).le)) hfN)
  exact le_trans (hcamp D hD x hx)
    (aux_in_deterministic_regularity_loss_mono C1 Cbound _ _ _ _ hC1 hC1b
      (by positivity) ht (Nat.cast_nonneg D) hR)

/-- Oscillations on a measurable window only see the function on that window. -/
theorem aux_in_deterministic_regularity_osc_congr {d : ℕ} {W : Set (SpatialCoordinates d)}
    (hW : MeasurableSet W) {U V : SpatialCoordinates d → ℝ} (h : EqOn U V W) :
    normalizedL2On W (fun y => U y - (volume.real W)⁻¹ * ∫ t in W, U t) =
      normalizedL2On W (fun y => V y - (volume.real W)⁻¹ * ∫ t in W, V t) := by
  have hint : ∫ t in W, U t = ∫ t in W, V t := setIntegral_congr_fun hW h
  rw [hint]
  unfold normalizedL2On volumeAverage
  congr 2
  refine setIntegral_congr_fun hW ?_
  intro y hy
  simp only [h hy]



theorem aux_in_deterministic_regularity_qp_subset {d : ℕ} (k : ℕ) (qside : ℝ)
    (hqside : qside = (3 : ℝ) ^ (-(k : ℤ))) (qcenter : SpatialCoordinates d)
    (Enl Shift : Type) (selfShift : Shift) (padE : Enl) (factor : Enl → ℕ)
    (hpad : factor padE = 1) (shift : Shift → SpatialCoordinates d)
    (hshift : shift selfShift = 0) (rootLevel : Enl × Shift → ℤ)
    (hrootLevel : ∀ (e : Enl) (t : Shift), rootLevel (e, t) = (k : ℤ) - (factor e : ℤ))
    (rootSide : Enl × Shift → ℝ)
    (hrootSide : ∀ (U : Enl × Shift), rootSide U = (3 : ℝ) ^ (-rootLevel U))
    (rootCentre : Enl × Shift → SpatialCoordinates d)
    (hrootCentre : ∀ (e : Enl) (t : Shift),
      rootCentre (e, t) = qcenter + rootSide (e, t) • shift t)
    (rootPos : ∀ (U : Enl × Shift), 0 < rootSide U)
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (hRootsQ : ∀ U : Enl × Shift,
      closure (centeredCube (rootCentre U) (rootSide U) (rootPos U) :
        Set (SpatialCoordinates d)) ⊆
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) :
    Metric.ball qcenter (3 * qside / 2) ⊆
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) := by
  have hL : rootLevel (padE, selfShift) = (k : ℤ) - 1 := by
    rw [hrootLevel, hpad]; push_cast; ring
  have hS : rootSide (padE, selfShift) = 3 * qside := by
    rw [hrootSide, hL, hqside, show -((k : ℤ) - 1) = 1 + -(k : ℤ) by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
  have hC : rootCentre (padE, selfShift) = qcenter := by
    rw [hrootCentre, hshift, smul_zero, add_zero]
  intro y hy
  apply hRootsQ (padE, selfShift)
  apply subset_closure
  show y ∈ Metric.ball (rootCentre (padE, selfShift)) (rootSide (padE, selfShift) / 2)
  rw [hC, hS]
  exact hy



theorem aux_in_deterministic_regularity_glue_holder {d : ℕ} (alpha : ℝ)
    (halpha : alpha ∈ Ioo (0 : ℝ) 1)
    (Qset : Set (SpatialCoordinates d)) (hQ : IsOpen Qset)
    (qcenter : SpatialCoordinates d) (qside : ℝ) (hqpos : 0 < qside)
    (hqpQ : Metric.ball qcenter (3 * qside / 2) ⊆ Qset)
    (uf : SpatialCoordinates d → ℝ) (Uh : ℕ → SpatialCoordinates d → ℝ)
    (hUc : ∀ h, ContinuousOn (Uh h) Qset)
    (hUae : ∀ h, uf =ᵐ[volume.restrict Qset] Uh h)
    (C1 Cbound a t S : ℝ) (hC1 : 0 ≤ C1) (hC1b : C1 ≤ Cbound)
    (hCh : 2 * aux_in_deterministic_regularity_holderConst d alpha * C1 ≤ Cbound)
    (ha : 0 ≤ a) (ht : 0 ≤ t) (hsub : Cbound * t < 1 - alpha) (hS : 0 ≤ S)
    (hcamp : ∀ h : ℕ, ∀ (D : ℕ), D ≤ h →
      ∀ x ∈ (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)),
        let B : Set (SpatialCoordinates d) :=
          Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2) ∩
            (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))
        normalizedL2On B (fun y => Uh h y - (volume.real B)⁻¹ * ∫ t in B, Uh h t) ≤
          C1 * (3 : ℝ) ^ (C1 * a) * (3 : ℝ) ^ (C1 * t * (D : ℝ)) * (3 : ℝ) ^ (-(D : ℝ)) *
            (normalizedL2On (Metric.ball qcenter (3 * qside / 2))
              (fun y => Uh h y - (volume.real (Metric.ball qcenter (3 * qside / 2)))⁻¹ *
                ∫ t in Metric.ball qcenter (3 * qside / 2), Uh h t) + S)) :
    IsHolderOn alpha
        (closure (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))) (Uh 0) ∧
      cAlphaNorm alpha
          (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
          (fun x => Uh 0 (qcenter + qside • x) - Uh 0 qcenter) ≤
        Cbound * (3 : ℝ) ^ (Cbound * a) *
          (normalizedL2On (Metric.ball qcenter (3 * qside / 2))
            (fun x => Uh 0 x - (volume.real (Metric.ball qcenter (3 * qside / 2)))⁻¹ *
              ∫ y in Metric.ball qcenter (3 * qside / 2), Uh 0 y) + S) := by
  set qp : Set (SpatialCoordinates d) := Metric.ball qcenter (3 * qside / 2) with hqp
  have hq : (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) =
      Metric.ball qcenter (qside / 2) := rfl
  have hclq : closure (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) ⊆ qp := by
    rw [hq, closure_ball qcenter (by positivity : qside / 2 ≠ 0)]
    exact Metric.closedBall_subset_ball (by linarith)
  have hqQ : (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) ⊆ Qset :=
    subset_closure.trans (hclq.trans hqpQ)
  have hEq : ∀ h, EqOn (Uh h) (Uh 0) Qset := fun h =>
    Measure.eqOn_open_of_ae_eq ((hUae h).symm.trans (hUae 0)) hQ (hUc h) (hUc 0)
  set R0 := normalizedL2On qp (fun x => Uh 0 x - (volume.real qp)⁻¹ * ∫ y in qp, Uh 0 y) + S
    with hR0
  have hR0nn : 0 ≤ R0 := add_nonneg (Real.sqrt_nonneg _) hS
  set K := C1 * (3 : ℝ) ^ (C1 * a) * R0 with hK
  have hKnn : 0 ≤ K := by positivity
  have hθ : ∀ D : ℕ, (3 : ℝ) ^ (C1 * t * (D : ℝ)) * (3 : ℝ) ^ (-(D : ℝ)) ≤
      ((3 : ℝ) ^ (-alpha)) ^ D := by
    intro D
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have h1 : C1 * t ≤ Cbound * t := mul_le_mul_of_nonneg_right hC1b ht
    have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
    nlinarith
  have hcamp0 : ∀ (D : ℕ),
      ∀ x ∈ (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)),
      let B : Set (SpatialCoordinates d) :=
        Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2) ∩
          (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))
      normalizedL2On B (fun y => Uh 0 y - (volume.real B)⁻¹ * ∫ t in B, Uh 0 t) ≤
        K * ((3 : ℝ) ^ (-alpha)) ^ D := by
    intro D x hx B
    have hBm : MeasurableSet B :=
      (Metric.isOpen_ball.inter (centeredCube qcenter qside hqpos).isOpen).measurableSet
    have hBQ : B ⊆ Qset := inter_subset_right.trans hqQ
    have hc : normalizedL2On B (fun y => Uh D y - (volume.real B)⁻¹ * ∫ t in B, Uh D t) ≤
        C1 * (3 : ℝ) ^ (C1 * a) * (3 : ℝ) ^ (C1 * t * (D : ℝ)) * (3 : ℝ) ^ (-(D : ℝ)) *
          (normalizedL2On qp (fun y => Uh D y - (volume.real qp)⁻¹ * ∫ t in qp, Uh D t) + S) :=
      hcamp D D le_rfl x hx
    rw [aux_in_deterministic_regularity_osc_congr hBm (fun y hy => hEq D (hBQ hy)),
      aux_in_deterministic_regularity_osc_congr Metric.isOpen_ball.measurableSet
        (fun y hy => hEq D (hqpQ hy))] at hc
    calc _ ≤ _ := hc
      _ = K * ((3 : ℝ) ^ (C1 * t * (D : ℝ)) * (3 : ℝ) ^ (-(D : ℝ))) := by rw [hK]; ring
      _ ≤ K * ((3 : ℝ) ^ (-alpha)) ^ D := mul_le_mul_of_nonneg_left (hθ D) hKnn
  obtain ⟨hHol, -, hCa⟩ := aux_in_deterministic_regularity_campanato_holder alpha halpha
    qcenter qside hqpos (Uh 0) ((hUc 0).mono (hclq.trans hqpQ)) K hKnn hcamp0
  refine ⟨hHol, hCa.trans ?_⟩
  have hChnn := aux_in_deterministic_regularity_holderConst_nonneg d halpha.1
  have e1 : (3 : ℝ) ^ (C1 * a) ≤ (3 : ℝ) ^ (Cbound * a) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_right hC1b ha)
  calc 2 * aux_in_deterministic_regularity_holderConst d alpha * K =
        (2 * aux_in_deterministic_regularity_holderConst d alpha * C1) *
          (3 : ℝ) ^ (C1 * a) * R0 := by rw [hK]; ring
    _ ≤ Cbound * (3 : ℝ) ^ (Cbound * a) * R0 :=
        mul_le_mul_of_nonneg_right (mul_le_mul hCh e1 (by positivity)
          (hC1.trans hC1b)) hR0nn

/-- **R2 from the core**, for an analytic constant with `C1 ≤ Cbound` and
`2·Ch(d,alpha)·C1 ≤ Cbound`. -/
theorem aux_in_deterministic_regularity_R2_of_core
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell epshom : ℝ)
    (Cbound eps0 lam0 delta0 : ℝ) (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1) (C1 : ℝ) (hC1 : 0 ≤ C1) (hC1b : C1 ≤ Cbound)
    (hCh : 2 * aux_in_deterministic_regularity_holderConst d alpha * C1 ≤ Cbound)
    (hcore : aux_in_deterministic_regularity_core d I alpha beta s sigma cell epshom Cbound eps0 lam0 delta0 C1) :
    aux_in_deterministic_regularity_R2 d I alpha beta s sigma cell epshom Cbound eps0 lam0 delta0 := by
  intro cbuf k0 M H hMH k z qside hqpos hqside qcenter hqcenter Enl Shift Cmp _ _ _
    selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift rootLevel hrootLevel
    rootSide hrootSide rootCentre hrootCentre rootPos hGridCover parent depth word cmpCentre
    hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre
    hObservationCentre eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
    lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hdisorder
    prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN hEllHiN
    AEN hAEN errN ratioN hErrN hRatioN Qcentre Qside hQside hRootsQ
    Q q qp Ctotal psource N hkN hcmp harmonicComparison traceEstimate
  have a1 := hcore cbuf k0 M H hMH k z qside hqpos hqside qcenter hqcenter Enl Shift Cmp
      selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift rootLevel hrootLevel
      rootSide hrootSide rootCentre hrootCentre rootPos hGridCover parent depth word cmpCentre
      hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre
      hObservationCentre eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
      lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hdisorder
      prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN hEllHiN
      AEN hAEN errN ratioN hErrN hRatioN Qcentre Qside hQside hRootsQ N hkN hcmp
  have hsNpos := aux_in_deterministic_regularity_sN_pos M H sN hsN
  have ht : 0 ≤ lambdaDet + M.delta ^ 2 + eps ^ 8 := by
    have : 0 < lambdaDet := hThresholds.1.trans (hThresholds.2.1.trans hThresholds.2.2.1)
    positivity
  have hqpQ : qp ⊆ (Q : Set (SpatialCoordinates d)) :=
    aux_in_deterministic_regularity_qp_subset k qside hqside qcenter Enl Shift selfShift padE
      factor hpad shift hshift rootLevel hrootLevel rootSide hrootSide rootCentre hrootCentre
      rootPos Qcentre Qside hQside hRootsQ
  filter_upwards [a1] with omega b1
  intro hev hb f hf fL2 hfL2 fNorm u hu
  choose Uh hUc hUae hcamp hharm using fun h : ℕ =>
    b1 h ⟨fun U D hk _ hN code => hev.1 U D hk hN code, hev.2⟩
      ⟨fun U D _ hN code => hb.1 U D hN code, fun U D _ hN code => hb.2.1 U D hN code⟩
      f hf fL2 hfL2 u hu
  have hfN : 0 ≤ fNorm qp := div_nonneg ENNReal.toReal_nonneg
    (Real.rpow_nonneg measureReal_nonneg _)
  have hS : 0 ≤ qside ^ 2 * (sN N (k : ℤ) qcenter omega)⁻¹ * fNorm qp :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (inv_nonneg.2 (hsNpos _ _ _ _).le)) hfN
  obtain ⟨hHol, hCa⟩ := aux_in_deterministic_regularity_glue_holder alpha halpha
    (Q : Set (SpatialCoordinates d)) Q.isOpen qcenter qside hqpos hqpQ _ Uh hUc hUae C1 Cbound
    _ _ _ hC1 hC1b hCh (by positivity) ht hb.2.2.1 hS hcamp
  exact ⟨Uh 0, hUc 0, hUae 0, hHol, ⟨Uh 0 qcenter, hCa⟩, hharm 0⟩

end SubdiffusiveProcess.Paper
end
end DeterministicRegularity_Regularity_Split

section DeterministicRegularity_Regularity_CampOneStep

/-!
# `camp` from the one-step hypothesis (f) through the iteration lemma




`onestep h theta C2` is the typed residual: on the horizon event, for every continuous
representative `U` of a sourced native weak solution, every depth `1 ≤ D ≤ horizon` and every
`x ∈ q`, a bad set of scales, one-step errors `epsilon` and source defects `defect` exist such that
the paper's hypothesis (f) of `l.iteration.lemma.GMC` holds on the concentric windows `x + □_j`,
`j ∈ [-(k+D), -k]`, off the bad set, with the budgets
`#bad, Σ epsilon ≤ C2 (1 + k0 + cbuf + t D)` and
`qside Σ defect ≤ C2 3^{C2 (k0+cbuf+tD)} qside² sN⁻¹ fNorm(qp)`, `t = lambdaDet + δ² + eps⁸`.
The windows, affine minimizers and the iteration are supplied here; `camp` follows at an explicit
constant depending on `d`, the iteration constant, `h` and `C2` only.
-/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- **The one-step residual** (hypothesis (f) with its budgets); see the module docstring. -/
def aux_in_deterministic_regularity_onestep
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell epshom : ℝ)
    (Cbound eps0 lam0 delta0 : ℝ) (h : ℕ) (theta C2 : ℝ) : Prop :=
      ∀ (cbuf k0 : ℕ)
        (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hMH : InfraredCharacterization M H)
        (k : ℕ) (z : SpatialCoordinates d)
        (qside : ℝ) (hqpos : 0 < qside)
        (hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
        (qcenter : SpatialCoordinates d)
        (hqcenter : qcenter = z)
        (Enl Shift Cmp : Type)
        [Fintype Enl] [Fintype Shift] [Fintype Cmp]
        (selfE : Enl) (selfShift : Shift)
        (qRoot : Enl × Shift)
        (hqRoot : qRoot = (selfE, selfShift))
        (factor : Enl → ℕ)
        (hfactor : factor selfE = 0)
        (padE : Enl) (hpad : factor padE = 1)
        (shift : Shift → SpatialCoordinates d)
        (hshift : shift selfShift = 0)
        (rootLevel : Enl × Shift → ℤ)
        (hrootLevel : ∀ (e : Enl) (t : Shift),
          rootLevel (e, t) = (k : ℤ) - (factor e : ℤ))
        (rootSide : Enl × Shift → ℝ)
        (hrootSide : ∀ (U : Enl × Shift),
          rootSide U = (3 : ℝ) ^ (-rootLevel U))
        (rootCentre : Enl × Shift → SpatialCoordinates d)
        (hrootCentre : ∀ (e : Enl) (t : Shift),
          rootCentre (e, t) = qcenter + rootSide (e, t) • shift t)
        (rootPos : ∀ (U : Enl × Shift), 0 < rootSide U)
        (hGridCover : ∀ (x : SpatialCoordinates d),
          x ∈ Metric.closedBall z (qside / 2) →
          ∀ rho : ℝ, 0 < rho → rho ≤ qside →
            ∃ (U : Enl × Shift) (D : ℕ) (w : Fin D → OddGridIndex d 1),
              Metric.ball x (rho / 2) ⊆
                Metric.ball (descendantCenter 1 (rootCentre U) (rootSide U) D w)
                  (descendantSide 1 D (rootSide U) / 2) ∧
              descendantSide 1 D (rootSide U) ≤ 9 * rho)
        (parent : Cmp → Enl × Shift)
        (depth : Cmp → ℕ)
        (word : (c : Cmp) → Fin (depth c) → OddGridIndex d 1)
        (cmpCentre : Cmp → SpatialCoordinates d)
        (hcmpCentre : ∀ (c : Cmp),
          cmpCentre c =
            descendantCenter 1 (rootCentre (parent c)) (rootSide (parent c))
              (depth c) (word c))
        (cmpLevel : Cmp → ℤ)
        (hcmpLevel : ∀ (c : Cmp),
          cmpLevel c = rootLevel (parent c) + (depth c : ℤ))
        (cmpSide : Cmp → ℝ)
        (hcmpSide : ∀ (c : Cmp), cmpSide c = (3 : ℝ) ^ (-cmpLevel c))
        (cmpPos : ∀ (c : Cmp), 0 < cmpSide c)
        (chosen : Cmp)
        (observationCentre : ∀ (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            SpatialCoordinates d)
        (hObservationCentre : ∀ (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
          observationCentre U D code =
            Sum.elim
              (fun w => descendantCenter 1 (rootCentre U) (rootSide U) D w)
              (fun V => rootCentre V) code)
        (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N i : ℕ) (y : Vec d),
            eta N omega i y =
              omega ((i : ℤ) - (N : ℤ))
                (((3 : ℝ) ^ (-(N : ℤ))) • y))
        (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
        (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
        (hepsSmall : eps ≤ eps0)
        (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ N : ℕ,
            primitive_scores d M s eps (eta N omega)
              (fun m y => F N m y omega)
              (fun m y => Praw N m y omega)
              (fun m y => Rraw N m y omega)
              (fun m y => Draw N m y omega)
              (fun m y => Z N m y omega)
              (fun m y => rawGood N m y omega))
        (lambdaCut lambdaLim lambdaDet cdet : ℝ)
        (hThresholds :
          0 < lambdaCut ∧ lambdaCut < lambdaLim ∧
          lambdaLim < lambdaDet ∧ lambdaDet < 1)
        (hcdet : 0 < cdet) (hcdetSmall : cdet ≤ Cbound⁻¹)
        (hlamSmall : lambdaDet ≤ lam0)
        (hdisorder : M.delta ≤ delta0)
        (prefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (prefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ),
          ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
            BilateralField d → ℝ)
        (hPrefixZ : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixZ N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega
                else 0
            else 0)
        (hPrefixD : ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
          (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
          (omega : BilateralField d),
          prefixD N U D code omega =
            if rootLevel U + (D : ℤ) ≤ (N : ℤ) then
              ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
                (rootLevel U + (D : ℤ)),
                if 0 ≤ (N : ℤ) - j then
                  (Draw N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre U D code) omega).toReal
                else 0
            else 0)
        (hFiniteScoreGuard : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ (N : ℕ) (U : Enl × Shift) (D : ℕ)
            (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)),
            rootLevel U + (D : ℤ) ≤ (N : ℤ) →
            ∀ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
              (rootLevel U + (D : ℤ)),
              Draw N ((N : ℤ) - j).toNat
                (((3 : ℝ) ^ N) • observationCentre U D code) omega ≠ ⊤)
        (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
        (hsN : ∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d)
          (omega : BilateralField d),
          sN N l w omega =
            if l ≤ (N : ℤ) then
              (let kappa : ℕ → ℝ := fun J =>
                Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
               let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
                 fun ell v beta =>
                   if 0 ≤ ell then
                     ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
                   else
                     -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
               kappa ((N : ℤ) - l).toNat / kappa N *
                 Real.exp (H omega w + retained l w omega))
            else 1)
        (ellLoN ellHiN : ℕ → Enl × Shift → BilateralField d → ℝ)
        (hEllLoN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellLoN N U omega =
            I.lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (hEllHiN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          ellHiN N U omega =
            I.Lam (rootCentre U) (rootSide U) (rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (rootCentre U) (rootPos U))
              (rootCentre U) (rootSide U) sigma 2 /
              sN N (rootLevel U) (rootCentre U) omega)
        (AEN : ℕ → Enl × Shift → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (hAEN : ∀ (N : ℕ) (U : Enl × Shift) (omega : BilateralField d),
          AEN N U omega =
            (sN N (rootLevel U) (rootCentre U) omega)⁻¹ •
              Homogenization.Book.Ch02.sigmaCoarse
                (Homogenization.Book.Ch02.cubeDomain
                  (Homogenization.originCube d 0))
                ((I.chart (rootCentre U) (rootSide U) (rootPos U)
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                    (rootCentre U) (rootPos U))
                  (rootCentre U) (rootSide U)).coeffOn
                  (Homogenization.originCube d 0)))
        (errN ratioN : ℕ → Cmp → BilateralField d → ℝ)
        (hErrN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          errN N c omega =
            I.err (cmpCentre c) (cmpSide c) (cmpPos c)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N
                (cmpCentre c) (cmpPos c))
              (cmpCentre c) (cmpSide c)
              (sN N (cmpLevel c) (cmpCentre c) omega) s 2)
        (hRatioN : ∀ (N : ℕ) (c : Cmp) (omega : BilateralField d),
          ratioN N c omega =
            sN N (k : ℤ) qcenter omega /
              sN N (cmpLevel c) (cmpCentre c) omega)
        (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
        (hRootsQ : ∀ U : Enl × Shift,
          closure (centeredCube (rootCentre U) (rootSide U) (rootPos U) :
            Set (SpatialCoordinates d)) ⊆
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ,
      let Q := centeredCube Qcentre Qside hQside
      let q := centeredCube qcenter qside hqpos
      let qp : Set (SpatialCoordinates d) := Metric.ball qcenter (3 * qside / 2)
      let Ctotal := Cbound * (3 : ℝ) ^ (Cbound * ((k0 : ℝ) + (cbuf : ℝ)))
      let psource : ℝ := (d : ℝ) / (1 - alpha)
      ∀ (N : ℕ), k + k0 ≤ N → (∀ c : Cmp, cmpLevel c ≤ (N : ℤ)) →
        let harmonicComparison (omega : BilateralField d)
            (fNorm : Set (SpatialCoordinates d) → ℝ)
            (U : SpatialCoordinates d → ℝ) : Prop :=
          (let qc := centeredCube (cmpCentre chosen) (cmpSide chosen / 81)
                   (div_pos (cmpPos chosen) (by norm_num))
                 let qi : Set (SpatialCoordinates d) :=
                   Metric.ball (cmpCentre chosen) (cmpSide chosen / 1458)
                 let qo : Set (SpatialCoordinates d) :=
                   Metric.ball (cmpCentre chosen) (cmpSide chosen / 18)
                 ∀ w : SpatialCoordinates d,
                 let qd : Set (SpatialCoordinates d) :=
                   Metric.ball w (27 * cmpSide chosen / 2)
                 Metric.closedBall (cmpCentre chosen) (cmpSide chosen / 18) ⊆ qd →
                 qd ⊆ (Q : Set (SpatialCoordinates d)) →
                 ∃ (v : weakSobolevGraph qc) (V : SpatialCoordinates d → ℝ),
                   ContinuousOn V (closure (qc : Set (SpatialCoordinates d))) ∧
                   (((v : SobolevData qc).1 : SpatialCoordinates d → ℝ) =ᵐ[
                     volume.restrict (qc : Set (SpatialCoordinates d))] V) ∧
                   (∀ x ∈ frontier (qc : Set (SpatialCoordinates d)), V x = U x) ∧
                   (∀ psi : killedSobolevGraph qc,
                     inner ℝ (sobolevGradient (v : SobolevData qc))
                       (subspaceGradient (killedSobolevGraph qc) psi) = 0) ∧
                   normalizedL2On qi (fun x => U x - V x) ≤
                     epshom * normalizedL2On qo
                       (fun x => U x - (volume.real qo)⁻¹ * ∫ y in qo, U y) +
                     Ctotal * (cmpSide chosen / 9) ^ 2 *
                       (sN N (cmpLevel chosen) (cmpCentre chosen) omega)⁻¹ * fNorm qd)
        let traceEstimate (omega : BilateralField d) : Prop :=
          (∃ Uq : ℝ,
            Uq = I.Lam qcenter qside hqpos
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
              qcenter qside sigma 2 ∧
            Cbound⁻¹ * sN N (k : ℤ) qcenter omega ≤ Uq ∧
            Uq ≤ Cbound * sN N (k : ℤ) qcenter omega ∧
            ∀ b : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta qcenter qside b →
              ∃ (extension : weakSobolevGraph q) (B : SpatialCoordinates d → ℝ),
                ContinuousOn B (closure (q : Set (SpatialCoordinates d))) ∧
                (((extension : SobolevData q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (q : Set (SpatialCoordinates d))] B) ∧
                (∀ x ∈ frontier (q : Set (SpatialCoordinates d)), B x = b x) ∧
                ∀ (Sq : ResponseSpace q), Sq.space = killedSobolevGraph q →
                  dirichletResponse Sq
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N qcenter hqpos)
                    extension ≤
                    Cbound * Uq * qside ^ ((d : ℝ) - 2) *
                      cellBoundaryQuotientNorm beta qcenter qside b ^ 2)
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ horizon : ℕ,
          ((∀ (U : Enl × Shift) (D : ℕ), k0 ≤ D → D ≤ horizon →
              rootLevel U + (D : ℤ) ≤ (N : ℤ) →
              ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
                prefixZ N U D code omega < lambdaCut * (D : ℝ) ∧
                prefixD N U D code omega < lambdaCut * (D : ℝ)) ∧
           (∀ U : Enl × Shift,
              cell ≤ ellLoN N U omega ∧ ellHiN N U omega ≤ cell⁻¹) ∧
           errN N chosen omega ≤ epshom * cdet ∧
           (∀ c : Cmp, ratioN N c omega ∈ Set.Icc (1 / 2 : ℝ) 2)) →
          ((∀ (Uroot : Enl × Shift) (D : ℕ), D ≤ horizon →
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              ((Finset.filter
                (fun j : ℤ => j < rootLevel Uroot + (k0 : ℤ) ∨
                  1 ≤ Z N ((N : ℤ) - j).toNat
                    (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega)
                (Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                  (rootLevel Uroot + (D : ℤ)))).card : ℝ) ≤
                (k0 : ℝ) + (cbuf : ℝ) + lambdaDet * (D : ℝ)) ∧
          (∀ (Uroot : Enl × Shift) (D : ℕ), D ≤ horizon →
            rootLevel Uroot + (D : ℤ) ≤ (N : ℤ) →
            ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift),
              (∑ j ∈ Finset.Icc (rootLevel Uroot - (cbuf : ℤ))
                (rootLevel Uroot + (D : ℤ)),
                if rootLevel Uroot + (k0 : ℤ) ≤ j ∧
                    Z N ((N : ℤ) - j).toNat
                      (((3 : ℝ) ^ N) • observationCentre Uroot D code) omega < 1 then
                  let w := observationCentre Uroot D code
                  let rj := (3 : ℝ) ^ (-j)
                  I.err w rj (by positivity)
                    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
                    w rj (sN N j w omega) s 2
                else 0) ≤
                  Cbound * (M.delta ^ 2 + eps ^ 8 + lambdaDet) * (D : ℝ) +
                    Cbound * ((k0 : ℝ) + (cbuf : ℝ)))) →
          (∀ (f : SpatialCoordinates d → ℝ),
            MemLp f (ENNReal.ofReal psource) (volume.restrict (Q : Set (SpatialCoordinates d))) →
            ∀ (fL2 : DomainL2 Q),
              ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                (Q : Set (SpatialCoordinates d))] f) →
            let fNorm : Set (SpatialCoordinates d) → ℝ := fun W =>
              (eLpNorm f (ENNReal.ofReal psource) (volume.restrict W)).toReal /
                (volume.real W) ^ (1 / psource)
            ∀ u : weakSobolevGraph Q,
              (∀ psi : killedSobolevGraph Q,
                sobolevCoefficientForm
                  (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
                  (u : SobolevData Q) (psi : SobolevData Q) =
                sobolevVolumeLoad fL2 (psi : SobolevData Q)) →
              ∀ U : SpatialCoordinates d → ℝ,
                ContinuousOn U (Q : Set (SpatialCoordinates d)) →
                (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict (Q : Set (SpatialCoordinates d))] U) →
                (∀ (D : ℕ), 1 ≤ D → D ≤ horizon →
                  ∀ x ∈ (q : Set (SpatialCoordinates d)),
                    ∃ bad : Finset ℤ, bad ⊆ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(k : ℤ)) ∧
                    ∃ epsilon defect : ℤ → ℝ,
                      (∀ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(k : ℤ)), 0 ≤ epsilon j ∧ 0 ≤ defect j) ∧
                      (∀ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(k : ℤ)), j ∉ bad →
                        ∀ ell : Affine d, ell ∈ affineMinimizers (translatedCube d j x) U →
                          excess (j - (h : ℤ)) (translatedCube d (j - (h : ℤ)) x) U ≤
                            theta ^ h * excess j (translatedCube d j x) U +
                              epsilon j * Real.sqrt (vecNormSq ell.slope) + defect j) ∧
                      (bad.card : ℝ) ≤ C2 * (1 + (((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ))) ∧
                      ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(k : ℤ)), epsilon j ≤ C2 * (1 + (((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ))) ∧
                      qside * ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(k : ℤ)), defect j ≤
                        C2 * (3 : ℝ) ^ (C2 * (((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ))) *
                          (qside ^ 2 * (sN N (k : ℤ) qcenter omega)⁻¹ * fNorm qp)))

/-- The Campanato constant produced from the iteration constant `Cit`, the step `h` and the
budget constant `C2`. -/
def aux_in_deterministic_regularity_campConst (d : ℕ) (Cit : ℝ) (h : ℕ) (C2 : ℝ) : ℝ :=
  max (max (Real.sqrt (6 ^ d))
      (Real.sqrt (2 ^ d) * Real.exp (Cit * ((h : ℝ) + 1) * (C2 + 1) + Cit * C2) *
        (Real.sqrt (3 ^ d) + C2)))
    (Cit * C2 * ((h : ℝ) + 2) / Real.log 3 + C2)

theorem aux_in_deterministic_regularity_campConst_nonneg (d : ℕ) (Cit : ℝ) (h : ℕ) (C2 : ℝ) :
    0 ≤ aux_in_deterministic_regularity_campConst d Cit h C2 :=
  le_max_of_le_left (le_max_of_le_left (Real.sqrt_nonneg _))

/-- Depth-zero arithmetic. -/
theorem aux_in_deterministic_regularity_camp_arith0 (d : ℕ) (C1 a t osc S L qs : ℝ)
    (hC1 : Real.sqrt (6 ^ d) ≤ C1) (ha : 0 ≤ a) (hosc : 0 ≤ osc) (hS : 0 ≤ S)
    (hL : L ≤ Real.sqrt (2 ^ d) * 1 * (3 : ℝ) ^ (-((0 : ℕ) : ℝ)) *
      (Real.sqrt (3 ^ d) * osc + qs * 0)) :
    L ≤ C1 * (3 : ℝ) ^ (C1 * a) * (3 : ℝ) ^ (C1 * t * ((0 : ℕ) : ℝ)) *
      (3 : ℝ) ^ (-((0 : ℕ) : ℝ)) * (osc + S) := by
  have h6 : Real.sqrt (2 ^ d) * Real.sqrt (3 ^ d) = Real.sqrt (6 ^ d) := by
    rw [← Real.sqrt_mul (by positivity), ← mul_pow]; norm_num
  have hC10 : 0 ≤ C1 := (Real.sqrt_nonneg _).trans hC1
  have h3 : 1 ≤ (3 : ℝ) ^ (C1 * a) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg hC10 ha)
  simp only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_zero, mul_one, add_zero] at hL ⊢
  calc L ≤ Real.sqrt (2 ^ d) * (Real.sqrt (3 ^ d) * osc) := hL
    _ = Real.sqrt (6 ^ d) * osc := by rw [← h6]; ring
    _ ≤ C1 * osc := mul_le_mul_of_nonneg_right hC1 hosc
    _ ≤ C1 * (3 : ℝ) ^ (C1 * a) * (osc + S) := by
        have : osc ≤ (3 : ℝ) ^ (C1 * a) * (osc + S) := by nlinarith
        calc C1 * osc ≤ C1 * ((3 : ℝ) ^ (C1 * a) * (osc + S)) :=
              mul_le_mul_of_nonneg_left this hC10
          _ = _ := by ring



theorem aux_in_deterministic_regularity_camp_arith (d : ℕ) (Cit C2 : ℝ) (h : ℕ)
    (a t D osc S card sumε sumδ qside L : ℝ)
    (hCit : 0 ≤ Cit) (hC2 : 0 ≤ C2) (ha : 0 ≤ a) (ht : 0 ≤ t) (hD : 0 ≤ D) (hosc : 0 ≤ osc)
    (hS : 0 ≤ S) (hq : 0 ≤ qside) (hδ0 : 0 ≤ sumδ) (hcard : card ≤ C2 * (1 + (a + t * D)))
    (hε : sumε ≤ C2 * (1 + (a + t * D)))
    (hδ : qside * sumδ ≤ C2 * (3 : ℝ) ^ (C2 * (a + t * D)) * S)
    (hL : L ≤ Real.sqrt (2 ^ d) * Real.exp (Cit * ((h : ℝ) + 1) * (card + 1) + Cit * sumε) *
      (3 : ℝ) ^ (-D) * (Real.sqrt (3 ^ d) * osc + qside * sumδ)) :
    L ≤ aux_in_deterministic_regularity_campConst d Cit h C2 *
      (3 : ℝ) ^ (aux_in_deterministic_regularity_campConst d Cit h C2 * a) *
      (3 : ℝ) ^ (aux_in_deterministic_regularity_campConst d Cit h C2 * t * D) *
      (3 : ℝ) ^ (-D) * (osc + S) := by
  set C1 := aux_in_deterministic_regularity_campConst d Cit h C2 with hC1def
  set y := a + t * D with hy
  have hy0 : 0 ≤ y := by positivity
  set E0 := Cit * ((h : ℝ) + 1) * (C2 + 1) + Cit * C2 with hE0
  set G := Cit * C2 * ((h : ℝ) + 2) with hG
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have hA : Cit * ((h : ℝ) + 1) * (card + 1) + Cit * sumε ≤ E0 + G * y := by
    have e1 : Cit * ((h : ℝ) + 1) * (card + 1) ≤ Cit * ((h : ℝ) + 1) * (C2 * (1 + y) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e2 : Cit * sumε ≤ Cit * (C2 * (1 + y)) := mul_le_mul_of_nonneg_left hε hCit
    have : E0 + G * y = Cit * ((h : ℝ) + 1) * (C2 * (1 + y) + 1) + Cit * (C2 * (1 + y)) := by
      rw [hE0, hG]; ring
    linarith
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hexpG : Real.exp (G * y) = (3 : ℝ) ^ (G / Real.log 3 * y) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    field_simp
  have hexp : Real.exp (Cit * ((h : ℝ) + 1) * (card + 1) + Cit * sumε) ≤
      Real.exp E0 * (3 : ℝ) ^ (G / Real.log 3 * y) := by
    rw [← hexpG, ← Real.exp_add]
    exact Real.exp_le_exp.2 hA
  have h3C2 : 1 ≤ (3 : ℝ) ^ (C2 * y) := Real.one_le_rpow (by norm_num) (mul_nonneg hC2 hy0)
  have hsrc : Real.sqrt (3 ^ d) * osc + qside * sumδ ≤
      (Real.sqrt (3 ^ d) + C2) * (3 : ℝ) ^ (C2 * y) * (osc + S) := by
    have hs3 : 0 ≤ Real.sqrt (3 ^ d) := Real.sqrt_nonneg _
    have : Real.sqrt (3 ^ d) * osc ≤ Real.sqrt (3 ^ d) * (3 : ℝ) ^ (C2 * y) * (osc + S) := by
      have h1 : osc ≤ (3 : ℝ) ^ (C2 * y) * (osc + S) := by nlinarith
      calc Real.sqrt (3 ^ d) * osc ≤ Real.sqrt (3 ^ d) * ((3 : ℝ) ^ (C2 * y) * (osc + S)) :=
            mul_le_mul_of_nonneg_left h1 hs3
        _ = _ := by ring
    have h2 : C2 * (3 : ℝ) ^ (C2 * y) * S ≤ C2 * (3 : ℝ) ^ (C2 * y) * (osc + S) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have hK1 : Real.sqrt (2 ^ d) * Real.exp E0 * (Real.sqrt (3 ^ d) + C2) ≤ C1 :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hK2 : G / Real.log 3 + C2 ≤ C1 := le_max_right _ _
  have hC10 : 0 ≤ C1 := aux_in_deterministic_regularity_campConst_nonneg d Cit h C2
  have hpow : (3 : ℝ) ^ (G / Real.log 3 * y) * (3 : ℝ) ^ (C2 * y) ≤ (3 : ℝ) ^ (C1 * y) := by
    rw [← Real.rpow_add (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  have hsplit : (3 : ℝ) ^ (C1 * y) = (3 : ℝ) ^ (C1 * a) * (3 : ℝ) ^ (C1 * t * D) := by
    rw [← Real.rpow_add (by norm_num), hy]; congr 1; ring
  have p3D : 0 ≤ (3 : ℝ) ^ (-D) := by positivity
  have pOS : 0 ≤ osc + S := by positivity
  calc L ≤ Real.sqrt (2 ^ d) * Real.exp (Cit * ((h : ℝ) + 1) * (card + 1) + Cit * sumε) *
        (3 : ℝ) ^ (-D) * (Real.sqrt (3 ^ d) * osc + qside * sumδ) := hL
    _ ≤ Real.sqrt (2 ^ d) * (Real.exp E0 * (3 : ℝ) ^ (G / Real.log 3 * y)) *
        (3 : ℝ) ^ (-D) * ((Real.sqrt (3 ^ d) + C2) * (3 : ℝ) ^ (C2 * y) * (osc + S)) := by
        gcongr
    _ = (Real.sqrt (2 ^ d) * Real.exp E0 * (Real.sqrt (3 ^ d) + C2)) *
        ((3 : ℝ) ^ (G / Real.log 3 * y) * (3 : ℝ) ^ (C2 * y)) * (3 : ℝ) ^ (-D) * (osc + S) := by
        ring
    _ ≤ C1 * (3 : ℝ) ^ (C1 * y) * (3 : ℝ) ^ (-D) * (osc + S) := by
        gcongr
    _ = _ := by rw [hsplit]; ring

/-- The closed outer ball lies in `Q` (closure of the padded self root). -/
theorem aux_in_deterministic_regularity_qpbar_subset {d : ℕ} (k : ℕ) (qside : ℝ)
    (hqpos : 0 < qside)
    (hqside : qside = (3 : ℝ) ^ (-(k : ℤ))) (qcenter : SpatialCoordinates d)
    (Enl Shift : Type) (selfShift : Shift) (padE : Enl) (factor : Enl → ℕ)
    (hpad : factor padE = 1) (shift : Shift → SpatialCoordinates d)
    (hshift : shift selfShift = 0) (rootLevel : Enl × Shift → ℤ)
    (hrootLevel : ∀ (e : Enl) (t : Shift), rootLevel (e, t) = (k : ℤ) - (factor e : ℤ))
    (rootSide : Enl × Shift → ℝ)
    (hrootSide : ∀ (U : Enl × Shift), rootSide U = (3 : ℝ) ^ (-rootLevel U))
    (rootCentre : Enl × Shift → SpatialCoordinates d)
    (hrootCentre : ∀ (e : Enl) (t : Shift),
      rootCentre (e, t) = qcenter + rootSide (e, t) • shift t)
    (rootPos : ∀ (U : Enl × Shift), 0 < rootSide U)
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (hRootsQ : ∀ U : Enl × Shift,
      closure (centeredCube (rootCentre U) (rootSide U) (rootPos U) :
        Set (SpatialCoordinates d)) ⊆
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) :
    Metric.closedBall qcenter (3 * qside / 2) ⊆
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) := by
  have hL : rootLevel (padE, selfShift) = (k : ℤ) - 1 := by
    rw [hrootLevel, hpad]; push_cast; ring
  have hS : rootSide (padE, selfShift) = 3 * qside := by
    rw [hrootSide, hL, hqside, show -((k : ℤ) - 1) = 1 + -(k : ℤ) by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
  have hC : rootCentre (padE, selfShift) = qcenter := by
    rw [hrootCentre, hshift, smul_zero, add_zero]
  have h := hRootsQ (padE, selfShift)
  have hcl : closure (centeredCube (rootCentre (padE, selfShift)) (rootSide (padE, selfShift))
      (rootPos (padE, selfShift)) : Set (SpatialCoordinates d)) =
      Metric.closedBall qcenter (3 * qside / 2) := by
    show closure (Metric.ball (rootCentre (padE, selfShift)) (rootSide (padE, selfShift) / 2)) = _
    rw [hC, hS, closure_ball qcenter (by positivity : 3 * qside / 2 ≠ 0)]
  rw [hcl] at h
  exact h

/-- **`camp` from the one-step residual.**  The iteration constant `Cit` depends on `d` only. -/
theorem aux_in_deterministic_regularity_camp_of_onestep
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ Cit : ℝ, 0 < Cit ∧
      ∀ (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell epshom : ℝ)
        (Cbound eps0 lam0 delta0 : ℝ) (h : ℕ) (theta C2 : ℝ),
        0 < h → theta ∈ Set.Ioo (0 : ℝ) 1 → theta ^ h ∈ Set.Ioo (0 : ℝ) (3 / 5) → 0 ≤ C2 →
        aux_in_deterministic_regularity_onestep d I alpha beta s sigma cell epshom Cbound eps0 lam0 delta0 h theta C2 →
        aux_in_deterministic_regularity_camp d I alpha beta s sigma cell epshom Cbound eps0 lam0 delta0
          (aux_in_deterministic_regularity_campConst d Cit h C2) := by
  obtain ⟨Cit, hCit, hiterL⟩ := aux_in_deterministic_regularity_translatedCube_iteration d
  refine ⟨Cit, hCit, ?_⟩
  intro I alpha beta s sigma cell epshom Cbound eps0 lam0 delta0 h theta C2 hh htheta hthetah
    hC2 hone cbuf k0 M H hMH k z qside hqpos hqside qcenter hqcenter Enl Shift Cmp _ _ _
    selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift rootLevel hrootLevel
    rootSide hrootSide rootCentre hrootCentre rootPos hGridCover parent depth word cmpCentre
    hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre
    hObservationCentre eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
    lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hdisorder
    prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN hEllHiN
    AEN hAEN errN ratioN hErrN hRatioN Qcentre Qside hQside hRootsQ
    Q q qp Ctotal psource N hkN hcmp harmonicComparison traceEstimate
  have a1 := hone cbuf k0 M H hMH k z qside hqpos hqside qcenter hqcenter Enl Shift Cmp
      selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift rootLevel hrootLevel
      rootSide hrootSide rootCentre hrootCentre rootPos hGridCover parent depth word cmpCentre
      hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre
      hObservationCentre eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
      lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hdisorder
      prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN hEllHiN
      AEN hAEN errN ratioN hErrN hRatioN Qcentre Qside hQside hRootsQ N hkN hcmp
  have hsNpos := aux_in_deterministic_regularity_sN_pos M H sN hsN
  have ht : 0 ≤ lambdaDet + M.delta ^ 2 + eps ^ 8 := by
    have : 0 < lambdaDet := hThresholds.1.trans (hThresholds.2.1.trans hThresholds.2.2.1)
    positivity
  have hKQ : Metric.closedBall qcenter (3 * qside / 2) ⊆ (Q : Set (SpatialCoordinates d)) :=
    aux_in_deterministic_regularity_qpbar_subset k qside hqpos hqside qcenter Enl Shift selfShift
      padE factor hpad shift hshift rootLevel hrootLevel rootSide hrootSide rootCentre
      hrootCentre rootPos Qcentre Qside hQside hRootsQ
  filter_upwards [a1] with omega b1
  intro horizon hev hb f hf fL2 hfL2 fNorm u hu U hUc hUae D hD x hx
  have hUK : ContinuousOn U (Metric.closedBall qcenter (3 * qside / 2)) := hUc.mono hKQ
  have hfN : 0 ≤ fNorm qp := div_nonneg ENNReal.toReal_nonneg
    (Real.rpow_nonneg measureReal_nonneg _)
  have hS : 0 ≤ qside ^ 2 * (sN N (k : ℤ) qcenter omega)⁻¹ * fNorm qp :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (inv_nonneg.2 (hsNpos _ _ _ _).le)) hfN
  have hosc : 0 ≤ normalizedL2On qp (fun y => U y - (volume.real qp)⁻¹ * ∫ t in qp, U t) :=
    Real.sqrt_nonneg _
  have ha : (0 : ℝ) ≤ (k0 : ℝ) + (cbuf : ℝ) := by positivity
  rcases Nat.eq_zero_or_pos D with hD0 | hDpos
  · subst hD0
    have hc := aux_in_deterministic_regularity_camp_of_iteration qcenter qside hqpos k hqside U
      hUK x hx 0 1 0 zero_le_one (by simp)
    exact aux_in_deterministic_regularity_camp_arith0 d _ _ _ _ _ _ qside
      ((le_max_left _ _).trans (le_max_left _ _)) ha hosc hS hc
  · obtain ⟨bad, hbad, epsilon, defect, hnn, hstep, hcard, hsumε, hsumδ⟩ :=
      b1 horizon hev hb f hf fL2 hfL2 u hu U hUc hUae D hDpos hD x hx
    have hWK : translatedCube d (-(k : ℤ)) x ⊆ Metric.closedBall qcenter (3 * qside / 2) := by
      rw [aux_in_deterministic_regularity_translatedCube_eq_ball, ← hqside]
      intro y hy
      have hx' : dist x qcenter < qside / 2 := hx
      rw [Metric.mem_ball] at hy
      rw [Metric.mem_closedBall]
      have := dist_triangle y x qcenter
      linarith
    have hWm : MeasurableSet (translatedCube d (-(k : ℤ)) x) := by
      rw [aux_in_deterministic_regularity_translatedCube_eq_ball]
      exact Metric.isOpen_ball.measurableSet
    obtain ⟨Cb, hCb⟩ := (isCompact_closedBall qcenter (3 * qside / 2)).exists_bound_of_continuousOn
      hUK
    have : IsFiniteMeasure (volume.restrict (translatedCube d (-(k : ℤ)) x)) := by
      rw [aux_in_deterministic_regularity_translatedCube_eq_ball]
      exact isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    have hMem : MemLp U 2 (volume.restrict (translatedCube d (-(k : ℤ)) x)) :=
      MemLp.of_bound ((hUK.mono hWK).aestronglyMeasurable hWm) Cb
        (ae_restrict_of_forall_mem hWm fun y hy => hCb y (hWK hy))
    have hit := hiterL h hh theta htheta hthetah (-((k : ℤ) + (D : ℤ))) (-(k : ℤ))
      (by omega) x U hMem bad hbad epsilon defect hnn hstep
    have hc := aux_in_deterministic_regularity_camp_of_iteration qcenter qside hqpos k hqside U
      hUK x hx D _ _ (Real.exp_pos _).le hit
    exact aux_in_deterministic_regularity_camp_arith d Cit C2 h _ _ (D : ℝ) _ _ _ _ _ qside _
      hCit.le hC2 ha ht (Nat.cast_nonneg D) hosc hS hqpos.le
      (Finset.sum_nonneg fun j hj => (hnn j hj).2) hcard hsumε hsumδ hc

end SubdiffusiveProcess.Paper
end
end DeterministicRegularity_Regularity_CampOneStep

section DeterministicRegularity_OneStep_Defs




open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- **Per-window arbitrary-coefficient one-step estimate**; see the
module docstring. -/
def aux_in_deterministic_onestep_window (d : ℕ) [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (alpha s : ℝ) (h : ℕ) (theta Ceps Cdel E0 : ℝ) : Prop :=
  ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ)
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (c : SpatialCoordinates d) (m : ℤ),
    Metric.ball c ((3 : ℝ) ^ m / 2) ⊆
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) →
    ∀ (f : SpatialCoordinates d → ℝ),
    MemLp f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) →
    ∀ (fL2 : DomainL2 (centeredCube Qcentre Qside hQside)),
    ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] f) →
    ∀ u : weakSobolevGraph (centeredCube Qcentre Qside hQside),
    (∀ psi : killedSobolevGraph (centeredCube Qcentre Qside hQside),
        sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
          (u : SobolevData (centeredCube Qcentre Qside hQside))
          (psi : SobolevData (centeredCube Qcentre Qside hQside)) =
        sobolevVolumeLoad fL2 (psi : SobolevData (centeredCube Qcentre Qside hQside))) →
    ∀ U : SpatialCoordinates d → ℝ,
    ContinuousOn U (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) →
    (((u : SobolevData (centeredCube Qcentre Qside hQside)).1 :
        SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U) →
    ∀ (x : SpatialCoordinates d), x ∈ Metric.ball c ((3 : ℝ) ^ (m - 1) / 2) →
    ∀ (j l : ℤ), j + 5 ≤ m → j = -l - 2 →
    ∀ (w : SpatialCoordinates d), w ∈ Metric.ball c ((3 : ℝ) ^ m / 2) →
      x ∈ Metric.ball w ((3 : ℝ) ^ (j - 3) / 2) →
    ∀ (a0 : ℝ), 0 < a0 →
    I.err w ((3 : ℝ) ^ (-l)) (by positivity)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
        w ((3 : ℝ) ^ (-l)) a0 s 2 ≤ E0 →
    ∀ ell : Affine d, ell ∈ affineMinimizers (translatedCube d j x) U →
      excess (j - (h : ℤ)) (translatedCube d (j - (h : ℤ)) x) U ≤
        theta ^ h * excess j (translatedCube d j x) U +
          Ceps * I.err w ((3 : ℝ) ^ (-l)) (by positivity)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
              w ((3 : ℝ) ^ (-l)) a0 s 2 * Real.sqrt (vecNormSq ell.slope) +
          Cdel * a0⁻¹ * (3 : ℝ) ^ (alpha * (j : ℝ)) *
            (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
              (volume.restrict (Metric.ball c ((3 : ℝ) ^ m / 2)))).toReal

end SubdiffusiveProcess.Paper
end
end DeterministicRegularity_OneStep_Defs

section DeterministicRegularity_OneStep_Count




open Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Markov counting: the number of indices with `c ≤ f i` is at most `Σ f / c`. -/
theorem aux_in_deterministic_onestep_card_filter_mul_le {ι : Type*} (S : Finset ι)
    (f : ι → ℝ) (hf : ∀ i ∈ S, 0 ≤ f i) (c : ℝ) :
    ((S.filter (fun i => c ≤ f i)).card : ℝ) * c ≤ ∑ i ∈ S, f i := by
  classical
  calc ((S.filter (fun i => c ≤ f i)).card : ℝ) * c
      = ∑ _i ∈ S.filter (fun i => c ≤ f i), c := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ S.filter (fun i => c ≤ f i), f i :=
        Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp hi).2
    _ ≤ ∑ i ∈ S, f i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun i hi _ => hf i hi

/-- The reflection `j ↦ -j-2` is injective. -/
theorem aux_in_deterministic_onestep_refl_injective :
    Function.Injective (fun j : ℤ => -j - 2) := by
  intro a b hab
  simp only at hab
  omega

/-- Reindexing along the reflection `j ↦ -j-2` into a larger interval of nonnegative terms. -/
theorem aux_in_deterministic_onestep_sum_refl_le (a b A B : ℤ) (g : ℤ → ℝ)
    (hg : ∀ l ∈ Icc A B, 0 ≤ g l) (hA : A ≤ -b - 2) (hB : -a - 2 ≤ B) :
    ∑ j ∈ Icc a b, g (-j - 2) ≤ ∑ l ∈ Icc A B, g l := by
  classical
  have himg : ∑ j ∈ Icc a b, g (-j - 2) =
      ∑ l ∈ (Icc a b).image (fun j : ℤ => -j - 2), g l := by
    rw [Finset.sum_image]
    intro x _ y _ hxy
    exact aux_in_deterministic_onestep_refl_injective hxy
  rw [himg]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro l hl
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hl
    rw [Finset.mem_Icc] at hj ⊢
    constructor <;> omega
  · intro l hl _
    exact hg l hl

/-- Counting along the reflection. -/
theorem aux_in_deterministic_onestep_card_refl_le (a b A B : ℤ) (g : ℤ → ℝ)
    (hg : ∀ l ∈ Icc A B, 0 ≤ g l) (hA : A ≤ -b - 2) (hB : -a - 2 ≤ B) (c : ℝ) :
    (((Icc a b).filter (fun j => c ≤ g (-j - 2))).card : ℝ) * c ≤ ∑ l ∈ Icc A B, g l := by
  refine le_trans ?_ (aux_in_deterministic_onestep_sum_refl_le a b A B g hg hA hB)
  refine aux_in_deterministic_onestep_card_filter_mul_le (Icc a b) (fun j => g (-j - 2)) ?_ c
  intro j hj
  apply hg
  rw [Finset.mem_Icc] at hj ⊢
  constructor <;> omega

/-- Cardinality of an integer interval, as a real number. -/
theorem aux_in_deterministic_onestep_card_Icc_le (a b : ℤ) (n : ℕ) (h : b - a + 1 ≤ n) :
    ((Icc a b).card : ℝ) ≤ n := by
  rw [Int.card_Icc]
  have : (b + 1 - a).toNat ≤ n := by omega
  exact_mod_cast this

/-- Geometric bound for `Σ 3^{α j}` over an integer interval ending at `b`. -/
theorem aux_in_deterministic_onestep_geom_sum_le (alpha : ℝ) (halpha : 0 < alpha) (a b : ℤ) :
    ∑ j ∈ Icc a b, (3 : ℝ) ^ (alpha * (j : ℝ)) ≤
      (3 : ℝ) ^ (alpha * (b : ℝ)) / (1 - (3 : ℝ) ^ (-alpha)) := by
  classical
  set r : ℝ := (3 : ℝ) ^ (-alpha) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hterm : ∀ j ∈ Icc a b,
      (3 : ℝ) ^ (alpha * (j : ℝ)) = (3 : ℝ) ^ (alpha * (b : ℝ)) * r ^ ((b - j).toNat) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hcast : (((b - j).toNat : ℕ) : ℝ) = (b : ℝ) - (j : ℝ) := by
      have : ((b - j).toNat : ℤ) = b - j := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), hcast,
      ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hinj : Set.InjOn (fun j : ℤ => (b - j).toNat) (Icc a b : Set ℤ) := by
    intro x hx y hy hxy
    simp only [Finset.coe_Icc, Set.mem_Icc] at hx hy
    simp only at hxy
    omega
  have hsum : ∑ j ∈ Icc a b, r ^ ((b - j).toNat) ≤ (1 - r)⁻¹ := by
    rw [← Finset.sum_image (f := fun i : ℕ => r ^ i) hinj]
    rw [← tsum_geometric_of_lt_one hr0 hr1]
    exact Summable.sum_le_tsum _ (fun i _ => pow_nonneg hr0 i)
      (summable_geometric_of_lt_one hr0 hr1)
  have h3 : 0 ≤ (3 : ℝ) ^ (alpha * (b : ℝ)) := Real.rpow_nonneg (by norm_num) _
  calc (3 : ℝ) ^ (alpha * (b : ℝ)) * ∑ j ∈ Icc a b, r ^ ((b - j).toNat)
      ≤ (3 : ℝ) ^ (alpha * (b : ℝ)) * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left hsum h3
    _ = (3 : ℝ) ^ (alpha * (b : ℝ)) / (1 - r) := by rw [div_eq_mul_inv]

/-- **Splicing two ranges of one-step data.**  Data on `[a, m]` and on `[m+1, b]` combine to
data on `[a, b]` with added budgets. -/
theorem aux_in_deterministic_onestep_splice (a m b : ℤ) (ham : a ≤ m + 1) (hmb : m ≤ b)
    (P : ℤ → ℝ → ℝ → Prop) (B1 E1 F1 B2 E2 F2 : ℝ)
    (h1 : ∃ bad : Finset ℤ, bad ⊆ Icc a m ∧ ∃ eps del : ℤ → ℝ,
      (∀ j ∈ Icc a m, 0 ≤ eps j ∧ 0 ≤ del j) ∧
      (∀ j ∈ Icc a m, j ∉ bad → P j (eps j) (del j)) ∧
      (bad.card : ℝ) ≤ B1 ∧ ∑ j ∈ Icc a m, eps j ≤ E1 ∧ ∑ j ∈ Icc a m, del j ≤ F1)
    (h2 : ∃ bad : Finset ℤ, bad ⊆ Icc (m + 1) b ∧ ∃ eps del : ℤ → ℝ,
      (∀ j ∈ Icc (m + 1) b, 0 ≤ eps j ∧ 0 ≤ del j) ∧
      (∀ j ∈ Icc (m + 1) b, j ∉ bad → P j (eps j) (del j)) ∧
      (bad.card : ℝ) ≤ B2 ∧ ∑ j ∈ Icc (m + 1) b, eps j ≤ E2 ∧
        ∑ j ∈ Icc (m + 1) b, del j ≤ F2) :
    ∃ bad : Finset ℤ, bad ⊆ Icc a b ∧ ∃ eps del : ℤ → ℝ,
      (∀ j ∈ Icc a b, 0 ≤ eps j ∧ 0 ≤ del j) ∧
      (∀ j ∈ Icc a b, j ∉ bad → P j (eps j) (del j)) ∧
      (bad.card : ℝ) ≤ B1 + B2 ∧ ∑ j ∈ Icc a b, eps j ≤ E1 + E2 ∧
        ∑ j ∈ Icc a b, del j ≤ F1 + F2 := by
  classical
  obtain ⟨bad1, hb1, e1, d1, hnn1, hP1, hc1, hs1, ht1⟩ := h1
  obtain ⟨bad2, hb2, e2, d2, hnn2, hP2, hc2, hs2, ht2⟩ := h2
  have hsplit : Icc a b = Icc a m ∪ Icc (m + 1) b := by
    ext j; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint (Icc a m) (Icc (m + 1) b) := by
    rw [Finset.disjoint_left]
    intro j hj hj'
    rw [Finset.mem_Icc] at hj hj'
    omega
  let eps : ℤ → ℝ := fun j => if j ≤ m then e1 j else e2 j
  let del : ℤ → ℝ := fun j => if j ≤ m then d1 j else d2 j
  have hlo : ∀ j ∈ Icc a m, eps j = e1 j ∧ del j = d1 j := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact ⟨ite_eq_left hj.2, ite_eq_left hj.2⟩
  have hhi : ∀ j ∈ Icc (m + 1) b, eps j = e2 j ∧ del j = d2 j := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have : ¬ j ≤ m := by omega
    exact ⟨ite_eq_right this, ite_eq_right this⟩
  refine ⟨bad1 ∪ bad2, ?_, eps, del, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsplit]
    exact Finset.union_subset_union hb1 hb2
  · intro j hj
    rw [hsplit, Finset.mem_union] at hj
    rcases hj with hj | hj
    · rw [(hlo j hj).1, (hlo j hj).2]; exact hnn1 j hj
    · rw [(hhi j hj).1, (hhi j hj).2]; exact hnn2 j hj
  · intro j hj hnot
    rw [hsplit, Finset.mem_union] at hj
    rw [Finset.mem_union, not_or] at hnot
    rcases hj with hj | hj
    · rw [(hlo j hj).1, (hlo j hj).2]; exact hP1 j hj hnot.1
    · rw [(hhi j hj).1, (hhi j hj).2]; exact hP2 j hj hnot.2
  · calc ((bad1 ∪ bad2).card : ℝ) ≤ (bad1.card : ℝ) + bad2.card := by
          exact_mod_cast Finset.card_union_le bad1 bad2
      _ ≤ B1 + B2 := add_le_add hc1 hc2
  · rw [hsplit, Finset.sum_union hdisj,
      Finset.sum_congr rfl (fun j hj => (hlo j hj).1),
      Finset.sum_congr rfl (fun j hj => (hhi j hj).1)]
    exact add_le_add hs1 hs2
  · rw [hsplit, Finset.sum_union hdisj,
      Finset.sum_congr rfl (fun j hj => (hlo j hj).2),
      Finset.sum_congr rfl (fun j hj => (hhi j hj).2)]
    exact add_le_add ht1 ht2

end SubdiffusiveProcess.Paper

namespace SubdiffusiveProcess.Paper

/-- **Upper-range bookkeeping.**  Window scales `j ∈ [jlo, -k]`; the good candidates are
`j ∈ [-(k+DA)+4, -k-4]` whose level `l = -j-2` passed the prefix test (`k0 ≤ DA`) and has
`Z_l < 1` and `D_l ≤ c0`.  Every other window is bad.  The per-window step `hstep` supplies
the error bound, the reference comparison and the one-step property `P`. -/
theorem aux_in_deterministic_onestep_upper_core
    (k DA cbuf k0 : ℕ) (jlo : ℤ)
    (hjlo1 : jlo ≤ -((k : ℤ) + DA) + 4) (hjlo2 : -((k : ℤ) + DA) - 2 ≤ jlo)
    (Zl Dl : ℤ → ℝ) (hZ0 : ∀ l, 0 ≤ Zl l) (hD0 : ∀ l, 0 ≤ Dl l)
    (lamCut c0 Cg B Ceps Cdel F Rs alpha : ℝ)
    (hlam : 0 ≤ lamCut) (hc0 : 0 < c0) (hCg : 0 ≤ Cg) (hB : 0 ≤ B) (hCeps : 0 ≤ Ceps)
    (hCdel : 0 ≤ Cdel) (hF : 0 ≤ F) (hRs : 0 ≤ Rs)
    (hprefix : k0 ≤ DA →
      ∑ l ∈ Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA), Zl l < lamCut * DA ∧
        ∑ l ∈ Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA), Dl l < lamCut * DA)
    (err a0 : ℤ → ℝ) (herr0 : ∀ j, 0 ≤ err j) (ha0 : ∀ j, 0 < a0 j)
    (P : ℤ → ℝ → ℝ → Prop)
    (hstep : ∀ j ∈ Icc (-((k : ℤ) + DA) + 4) (-(k : ℤ) - 4), k0 ≤ DA →
      Zl (-j - 2) < 1 → Dl (-j - 2) ≤ c0 →
      err j ≤ Cg * (B + Dl (-j - 2)) ∧ (a0 j)⁻¹ ≤ Rs ∧
        P j (Ceps * err j) (Cdel * (a0 j)⁻¹ * (3 : ℝ) ^ (alpha * (j : ℝ)) * F)) :
    ∃ bad : Finset ℤ, bad ⊆ Icc jlo (-(k : ℤ)) ∧ ∃ eps del : ℤ → ℝ,
      (∀ j ∈ Icc jlo (-(k : ℤ)), 0 ≤ eps j ∧ 0 ≤ del j) ∧
      (∀ j ∈ Icc jlo (-(k : ℤ)), j ∉ bad → P j (eps j) (del j)) ∧
      (bad.card : ℝ) ≤ 10 + k0 + lamCut * DA * (1 + c0⁻¹) ∧
      ∑ j ∈ Icc jlo (-(k : ℤ)), eps j ≤ Ceps * Cg * (B * ((DA : ℝ) + 1) + lamCut * DA) ∧
      ∑ j ∈ Icc jlo (-(k : ℤ)), del j ≤
        Cdel * Rs * F * ∑ j ∈ Icc jlo (-(k : ℤ)), (3 : ℝ) ^ (alpha * (j : ℝ)) := by
  classical
  set G : Finset ℤ := Icc (-((k : ℤ) + DA) + 4) (-(k : ℤ) - 4) with hG
  let good : ℤ → Prop := fun j =>
    j ∈ G ∧ k0 ≤ DA ∧ Zl (-j - 2) < 1 ∧ Dl (-j - 2) ≤ c0
  let eps : ℤ → ℝ := fun j => if good j then Ceps * err j else 0
  let del : ℤ → ℝ := fun j =>
    if good j then Cdel * (a0 j)⁻¹ * (3 : ℝ) ^ (alpha * (j : ℝ)) * F else 0
  have hGsub : G ⊆ Icc jlo (-(k : ℤ)) := by
    intro j hj
    rw [hG, Finset.mem_Icc] at hj
    rw [Finset.mem_Icc]
    constructor <;> omega
  have h3pos : ∀ j : ℤ, 0 ≤ (3 : ℝ) ^ (alpha * (j : ℝ)) :=
    fun j => Real.rpow_nonneg (by norm_num) _
  refine ⟨(Icc jlo (-(k : ℤ))).filter (fun j => ¬ good j), Finset.filter_subset _ _,
    eps, del, ?_, ?_, ?_, ?_, ?_⟩
  · -- nonnegativity
    intro j _
    constructor
    · show 0 ≤ (if good j then Ceps * err j else 0)
      split_ifs
      · exact mul_nonneg hCeps (herr0 j)
      · exact le_rfl
    · show 0 ≤ (if good j then Cdel * (a0 j)⁻¹ * (3 : ℝ) ^ (alpha * (j : ℝ)) * F else 0)
      split_ifs
      · exact mul_nonneg (mul_nonneg (mul_nonneg hCdel (inv_nonneg.mpr (ha0 j).le))
          (h3pos j)) hF
      · exact le_rfl
  · -- the one-step property off the bad set
    intro j hj hnot
    have hgood : good j := by
      by_contra hng
      exact hnot (Finset.mem_filter.mpr ⟨hj, hng⟩)
    obtain ⟨hjG, hk0, hZ, hD⟩ := hgood
    have hst := (hstep j hjG hk0 hZ hD).2.2
    show P j (if good j then Ceps * err j else 0)
      (if good j then Cdel * (a0 j)⁻¹ * (3 : ℝ) ^ (alpha * (j : ℝ)) * F else 0)
    rw [ite_eq_left ⟨hjG, hk0, hZ, hD⟩, ite_eq_left ⟨hjG, hk0, hZ, hD⟩]
    exact hst
  · -- the count
    by_cases hk0 : k0 ≤ DA
    · obtain ⟨hZs, hDs⟩ := hprefix hk0
      have hsub : (Icc jlo (-(k : ℤ))).filter (fun j => ¬ good j) ⊆
          ((Icc jlo (-((k : ℤ) + DA) + 3) ∪ Icc (-(k : ℤ) - 3) (-(k : ℤ))) ∪
            G.filter (fun j => 1 ≤ Zl (-j - 2))) ∪ G.filter (fun j => c0 ≤ Dl (-j - 2)) := by
        intro j hj
        obtain ⟨hjI, hng⟩ := Finset.mem_filter.mp hj
        rw [Finset.mem_Icc] at hjI
        by_cases hjG : j ∈ G
        · have hor : ¬ Zl (-j - 2) < 1 ∨ ¬ Dl (-j - 2) ≤ c0 := by
            by_contra hc
            push Not at hc
            exact hng ⟨hjG, hk0, hc.1, hc.2⟩
          rcases hor with h1 | h2
          · push Not at h1
            exact Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨hjG, h1⟩))
          · push Not at h2
            exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hjG, h2.le⟩)
        · rw [hG, Finset.mem_Icc] at hjG
          refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
          rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc]
          omega
      have hcard1 : (((Icc jlo (-((k : ℤ) + DA) + 3)) ∪ Icc (-(k : ℤ) - 3) (-(k : ℤ))).card : ℝ)
          ≤ 10 := by
        have h1 := aux_in_deterministic_onestep_card_Icc_le jlo (-((k : ℤ) + DA) + 3) 6
          (by push_cast; omega)
        have h2 := aux_in_deterministic_onestep_card_Icc_le (-(k : ℤ) - 3) (-(k : ℤ)) 4
          (by push_cast; omega)
        have hu : (((Icc jlo (-((k : ℤ) + DA) + 3)) ∪ Icc (-(k : ℤ) - 3) (-(k : ℤ))).card : ℝ)
            ≤ ((Icc jlo (-((k : ℤ) + DA) + 3)).card : ℝ) + (Icc (-(k : ℤ) - 3) (-(k : ℤ))).card := by
          exact_mod_cast Finset.card_union_le _ _
        push_cast at h1 h2
        linarith
      have hcardZ : ((G.filter (fun j => 1 ≤ Zl (-j - 2))).card : ℝ) ≤ lamCut * DA := by
        have h := aux_in_deterministic_onestep_card_refl_le (-((k : ℤ) + DA) + 4) (-(k : ℤ) - 4)
          ((k : ℤ) - cbuf) ((k : ℤ) + DA) Zl (fun l _ => hZ0 l) (by omega) (by omega) 1
        rw [mul_one] at h
        exact h.trans hZs.le
      have hcardD : ((G.filter (fun j => c0 ≤ Dl (-j - 2))).card : ℝ) ≤ lamCut * DA * c0⁻¹ := by
        have h := aux_in_deterministic_onestep_card_refl_le (-((k : ℤ) + DA) + 4) (-(k : ℤ) - 4)
          ((k : ℤ) - cbuf) ((k : ℤ) + DA) Dl (fun l _ => hD0 l) (by omega) (by omega) c0
        rw [← le_div_iff₀ hc0] at h
        rw [← div_eq_mul_inv]
        exact h.trans (div_le_div_of_nonneg_right hDs.le hc0.le)
      have hcu := Finset.card_le_card hsub
      have hcu' : (((Icc jlo (-(k : ℤ))).filter (fun j => ¬ good j)).card : ℝ) ≤
          (((Icc jlo (-((k : ℤ) + DA) + 3)) ∪ Icc (-(k : ℤ) - 3) (-(k : ℤ))).card : ℝ) +
            (G.filter (fun j => 1 ≤ Zl (-j - 2))).card +
            (G.filter (fun j => c0 ≤ Dl (-j - 2))).card := by
        have h1 := Finset.card_union_le
          ((Icc jlo (-((k : ℤ) + DA) + 3) ∪ Icc (-(k : ℤ) - 3) (-(k : ℤ))) ∪
            G.filter (fun j => 1 ≤ Zl (-j - 2))) (G.filter (fun j => c0 ≤ Dl (-j - 2)))
        have h2 := Finset.card_union_le
          (Icc jlo (-((k : ℤ) + DA) + 3) ∪ Icc (-(k : ℤ) - 3) (-(k : ℤ)))
          (G.filter (fun j => 1 ≤ Zl (-j - 2)))
        have : ((Icc jlo (-(k : ℤ))).filter (fun j => ¬ good j)).card ≤
            ((Icc jlo (-((k : ℤ) + DA) + 3)) ∪ Icc (-(k : ℤ) - 3) (-(k : ℤ))).card +
            (G.filter (fun j => 1 ≤ Zl (-j - 2))).card +
            (G.filter (fun j => c0 ≤ Dl (-j - 2))).card := by omega
        exact_mod_cast this
      have hk0' : (0 : ℝ) ≤ k0 := Nat.cast_nonneg k0
      have hexp : lamCut * DA * (1 + c0⁻¹) = lamCut * DA + lamCut * DA * c0⁻¹ := by ring
      linarith
    · -- no prefix information: everything is bad, and there are at most `DA + 3 ≤ k0 + 2`
      push Not at hk0
      have hc := Finset.card_filter_le (Icc jlo (-(k : ℤ))) (fun j => ¬ good j)
      have hI := aux_in_deterministic_onestep_card_Icc_le jlo (-(k : ℤ)) (DA + 3)
        (by push_cast; omega)
      have hk : ((DA : ℝ) + 3) ≤ 10 + k0 := by
        have : DA + 3 ≤ 10 + k0 := by omega
        exact_mod_cast this
      have hnn : 0 ≤ lamCut * DA * (1 + c0⁻¹) := by positivity
      have hc' : (((Icc jlo (-(k : ℤ))).filter (fun j => ¬ good j)).card : ℝ) ≤
          ((Icc jlo (-(k : ℤ))).card : ℝ) := by exact_mod_cast hc
      push_cast at hI
      linarith
  · -- the error sum
    by_cases hk0 : k0 ≤ DA
    · obtain ⟨_, hDs⟩ := hprefix hk0
      have hzero : ∀ j ∈ Icc jlo (-(k : ℤ)), j ∉ G → eps j = 0 := by
        intro j _ hjG
        show (if good j then Ceps * err j else 0) = 0
        rw [ite_eq_right (fun hg => hjG hg.1)]
      rw [← Finset.sum_subset hGsub hzero]
      have hpt : ∀ j ∈ G, eps j ≤ Ceps * Cg * (B + Dl (-j - 2)) := by
        intro j hjG
        show (if good j then Ceps * err j else 0) ≤ Ceps * Cg * (B + Dl (-j - 2))
        split_ifs with hg
        · rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (hstep j hg.1 hg.2.1 hg.2.2.1 hg.2.2.2).1 hCeps
        · exact mul_nonneg (mul_nonneg hCeps hCg) (add_nonneg hB (hD0 _))
      have hsumD := aux_in_deterministic_onestep_sum_refl_le (-((k : ℤ) + DA) + 4) (-(k : ℤ) - 4)
        ((k : ℤ) - cbuf) ((k : ℤ) + DA) Dl (fun l _ => hD0 l) (by omega) (by omega)
      have hcardG : ((G.card : ℕ) : ℝ) ≤ (DA : ℝ) + 1 := by
        have := aux_in_deterministic_onestep_card_Icc_le (-((k : ℤ) + DA) + 4) (-(k : ℤ) - 4)
          (DA + 1) (by push_cast; omega)
        push_cast at this
        exact this
      calc ∑ j ∈ G, eps j ≤ ∑ j ∈ G, Ceps * Cg * (B + Dl (-j - 2)) := Finset.sum_le_sum hpt
        _ = Ceps * Cg * (B * (G.card : ℝ) + ∑ j ∈ G, Dl (-j - 2)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
          ring
        _ ≤ Ceps * Cg * (B * ((DA : ℝ) + 1) + lamCut * DA) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCeps hCg)
          exact add_le_add (mul_le_mul_of_nonneg_left hcardG hB) (hsumD.trans hDs.le)
    · have hzero : ∀ j ∈ Icc jlo (-(k : ℤ)), eps j = 0 := by
        intro j _
        show (if good j then Ceps * err j else 0) = 0
        rw [ite_eq_right (fun hg => hk0 hg.2.1)]
      rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
      have : (0 : ℝ) ≤ (DA : ℝ) + 1 := by positivity
      positivity
  · -- the defect sum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    show (if good j then Cdel * (a0 j)⁻¹ * (3 : ℝ) ^ (alpha * (j : ℝ)) * F else 0) ≤
      Cdel * Rs * F * (3 : ℝ) ^ (alpha * (j : ℝ))
    split_ifs with hg
    · have hR := (hstep j hg.1 hg.2.1 hg.2.2.1 hg.2.2.2).2.1
      have h1 : Cdel * (a0 j)⁻¹ ≤ Cdel * Rs := mul_le_mul_of_nonneg_left hR hCdel
      have h2 := mul_le_mul_of_nonneg_right h1 (mul_nonneg (h3pos j) hF)
      calc Cdel * (a0 j)⁻¹ * (3 : ℝ) ^ (alpha * (j : ℝ)) * F
          = Cdel * (a0 j)⁻¹ * ((3 : ℝ) ^ (alpha * (j : ℝ)) * F) := by ring
        _ ≤ Cdel * Rs * ((3 : ℝ) ^ (alpha * (j : ℝ)) * F) := h2
        _ = Cdel * Rs * F * (3 : ℝ) ^ (alpha * (j : ℝ)) := by ring
    · exact mul_nonneg (mul_nonneg (mul_nonneg hCdel hRs) hF) (h3pos j)

end SubdiffusiveProcess.Paper
end
end DeterministicRegularity_OneStep_Count

section DeterministicRegularity_OneStep_Ratio




open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization.Book
open SubdiffusiveProcess
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable



def aux_in_deterministic_onestep_sref {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N : ℕ) (l : ℤ) (w : SpatialCoordinates d) : ℝ :=
  let kappa : ℕ → ℝ := fun J =>
    Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
  let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
    fun ell v beta =>
      if 0 ≤ ell then
        ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
      else
        -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
  kappa ((N : ℤ) - l).toNat / kappa N * Real.exp (H omega w + retained l w omega)

theorem aux_in_deterministic_onestep_sref_pos {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N : ℕ) (l : ℤ) (w : SpatialCoordinates d) :
    0 < aux_in_deterministic_onestep_sref M H omega N l w := by
  unfold aux_in_deterministic_onestep_sref
  exact mul_pos (div_pos (mul_pos (Real.exp_pos _) (ahom_pos M _))
    (mul_pos (Real.exp_pos _) (ahom_pos M _))) (Real.exp_pos _)

/-- `Z ≥ 0` from the primitive scores. -/
theorem aux_in_deterministic_onestep_Z_nonneg {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s eps : ℝ)
    (g : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps g Fsc Psc Rsc Dsc Zsc goodEvt)
    (m : ℕ) (z : Vec d) : 0 ≤ Zsc m z := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hZdef, _⟩ := hPS
  exact (hZdef m z).2.1

/-- **One layer is controlled by `Draw`**: `3^{-s/8} |g_K(z)| ≤ Dsc_K(z)` for `K ≥ 1`. -/
theorem aux_in_deterministic_onestep_layer_le_draw {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s eps : ℝ)
    (g : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps g Fsc Psc Rsc Dsc Zsc goodEvt)
    (K : ℕ) (hK : 1 ≤ K) (z : Vec d) (hD : Dsc K z ≠ ⊤) :
    (3 : ℝ) ^ (-(s / 8)) * |g K z| ≤ (Dsc K z).toReal := by
  obtain ⟨_, _, _, _, _, _, _, hDdef, _, _, _⟩ := hPS
  have hDeq := hDdef K z
  have hmem : z ∈ translatedCube d (K : ℤ) z :=
    ⟨0, aux_in_deterministic_good_scale_transfer_zero_mem_cube K, by simp⟩
  have hshell : shellBlock K (K - 1) g z = g K z := by
    unfold shellBlock
    have : Finset.Icc (K - 1 + 1) K = {K} := by
      rw [Nat.sub_add_cancel hK]; exact Finset.Icc_self K
    rw [this, Finset.sum_singleton]
  have hexp : (3 : ℝ) ^ (-(s / 8) * ((K : ℝ) - ((K - 1 : ℕ) : ℝ))) = (3 : ℝ) ^ (-(s / 8)) := by
    rw [Nat.cast_sub hK]; congr 1; push_cast; ring
  have hB : ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8))) * ENNReal.ofReal |g K z| ≤ Dsc K z := by
    rw [hDeq]
    refine le_trans ?_ (le_trans le_add_self (le_trans le_self_add le_self_add))
    refine le_trans ?_ (le_sSup ⟨K - 1, Nat.sub_le K 1, rfl⟩)
    rw [hexp]
    gcongr
    refine le_sSup ⟨z, hmem, ?_⟩
    rw [hshell]
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s / 8)) := Real.rpow_nonneg (by norm_num) _
  have := ENNReal.toReal_mono hD hB
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal h3, ENNReal.toReal_ofReal (abs_nonneg _)]
    at this

/-- **Level comparison of the reference scalar at one point.** -/
theorem aux_in_deterministic_onestep_sref_level_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N : ℕ) (k l : ℤ) (hk : 0 ≤ k) (hkl : k ≤ l) (hlN : l ≤ (N : ℤ))
    (w : SpatialCoordinates d) :
    aux_in_deterministic_onestep_sref M H omega N k w ≤
      aux_in_deterministic_onestep_sref M H omega N l w *
        Real.exp (((l - k : ℤ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
          ∑ i ∈ Finset.Ico k l, |omega (-i) w|) := by
  unfold aux_in_deterministic_onestep_sref
  simp only
  rw [ite_eq_left hk, ite_eq_left (hk.trans hkl)]
  set τ := _root_.SubdiffusiveProcess.Model.tauSq M.P with hτ
  set S : ℝ := ∑ i ∈ Finset.Ico k l, omega (-i) w with hS
  set A : ℝ := ∑ i ∈ Finset.Ico k l, |omega (-i) w| with hA
  have hsplit : ∑ j ∈ Finset.Ico (0 : ℤ) l, omega (-j) w =
      ∑ j ∈ Finset.Ico (0 : ℤ) k, omega (-j) w + S := by
    rw [hS, ← Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive 0 k l),
      Finset.Ico_union_Ico_eq_Ico hk hkl]
  have hSA : -A ≤ S := by
    rw [hS, hA, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun i _ => neg_abs_le _
  set mk : ℕ := ((N : ℤ) - k).toNat with hmk
  set ml : ℕ := ((N : ℤ) - l).toNat with hml
  have hmkml : ml ≤ mk := by omega
  have hdiff : (mk : ℝ) = (ml : ℝ) + ((l - k : ℤ) : ℝ) := by
    have h1 : (mk : ℤ) = (N : ℤ) - k := Int.toNat_of_nonneg (by omega)
    have h2 : (ml : ℤ) = (N : ℤ) - l := Int.toNat_of_nonneg (by omega)
    have : (mk : ℤ) = (ml : ℤ) + (l - k) := by rw [h1, h2]; ring
    exact_mod_cast this
  have hahom : ahom M mk ≤ ahom M ml :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ahom_le_ahom_of_le M hmkml
  rw [hsplit]
  have hkN : 0 < Real.exp (((N : ℝ) + 1) * τ) * ahom M N :=
    mul_pos (Real.exp_pos _) (ahom_pos M N)
  set R0 : ℝ := ∑ j ∈ Finset.Ico (0 : ℤ) k, omega (-j) w
  -- clear the common denominator and compare numerators
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_le_div_iff_of_pos_right hkN]
  have hE : Real.exp (((mk : ℝ) + 1) * τ) =
      Real.exp (((ml : ℝ) + 1) * τ) * Real.exp (((l - k : ℤ) : ℝ) * τ) := by
    rw [← Real.exp_add, hdiff]; ring_nf
  have hexpS : Real.exp (H omega w + R0) ≤
      Real.exp (H omega w + (R0 + S)) * Real.exp A := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hp1 : 0 < Real.exp (((ml : ℝ) + 1) * τ) := Real.exp_pos _
  have hp2 : 0 < Real.exp (((l - k : ℤ) : ℝ) * τ) := Real.exp_pos _
  have hpa : 0 < ahom M mk := ahom_pos M mk
  calc Real.exp (((mk : ℝ) + 1) * τ) * ahom M mk * Real.exp (H omega w + R0)
      = Real.exp (((ml : ℝ) + 1) * τ) * Real.exp (((l - k : ℤ) : ℝ) * τ) * ahom M mk *
          Real.exp (H omega w + R0) := by rw [hE]
    _ ≤ Real.exp (((ml : ℝ) + 1) * τ) * Real.exp (((l - k : ℤ) : ℝ) * τ) * ahom M ml *
          (Real.exp (H omega w + (R0 + S)) * Real.exp A) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hahom (mul_pos hp1 hp2).le) hexpS
          (Real.exp_pos _).le (mul_pos (mul_pos hp1 hp2) (ahom_pos M ml)).le
    _ = Real.exp (((ml : ℝ) + 1) * τ) * ahom M ml * Real.exp (H omega w + (R0 + S)) *
          Real.exp (((l - k : ℤ) : ℝ) * τ + A) := by
        rw [show Real.exp (((l - k : ℤ) : ℝ) * τ + A) =
          Real.exp (((l - k : ℤ) : ℝ) * τ) * Real.exp A from Real.exp_add _ _]
        ring

/-- **Point comparison of the reference scalar at one level.**  Moving the reference point from
`w` to `w + 3^{-l} x`, `x` in the open unit cube, costs at most `exp(d · Dsc_m(3^N w))`. -/
theorem aux_in_deterministic_onestep_sref_point_le {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N : ℕ) (l : ℤ) (hl : l ≤ (N : ℤ))
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)))
    (s eps : ℝ)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (w : SpatialCoordinates d)
    (hD : Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w) ≠ ⊤)
    (x : Vec d) (hx : x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    aux_in_deterministic_onestep_sref M H omega N l (fun i => w i + (3 : ℝ) ^ (-l) * x i) ≤
      aux_in_deterministic_onestep_sref M H omega N l w *
        Real.exp ((d : ℝ) * (Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w)).toReal) := by
  set m : ℕ := ((N : ℤ) - l).toNat with hm
  set xp : SpatialCoordinates d := fun i => w i + (3 : ℝ) ^ (-l) * x i with hxp
  set z : Vec d := ((3 : ℝ) ^ N) • w with hz
  set T : ℝ := (Dsc m z).toReal with hT
  have hvec : ((3 : ℝ) ^ N) • xp = ((3 : ℝ) ^ m) • x + z := by
    funext i
    simp only [xp, z, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [mul_add, ← mul_assoc, aux_in_deterministic_good_scale_transfer_scale_pow N l hl]
    ring
  set sw := aux_in_deterministic_onestep_sref M H omega N l w with hsw
  set sx := aux_in_deterministic_onestep_sref M H omega N l xp with hsx
  have hsw0 : 0 < sw := aux_in_deterministic_onestep_sref_pos M H omega N l w
  have hsx0 : 0 < sx := aux_in_deterministic_onestep_sref_pos M H omega N l xp
  -- the exponents of the exact identity, as functions of the infrared truncation `K`
  let Sm : ℕ → ℝ := fun K => ∑ k ∈ Finset.Ico (m + 1) (N + K + 1),
    (eta k (((3 : ℝ) ^ m) • x + z) - eta k z)
  let bK : ℕ → ℝ := fun K => (H omega xp - H omega w) -
    ∑ n ∈ Finset.range K, (omega (((n + 1 : ℕ) : ℤ)) xp - omega (((n + 1 : ℕ) : ℤ)) w)
  have hKm : ∀ K, m ≤ K → ((N : ℤ) - l).toNat ≤ N + K := fun K hK => by omega
  have hcut0 : 0 < cutoffCoefficient M H omega N xp :=
    aux_in_deterministic_good_scale_transfer_cutoffCoefficient_pos M H omega N xp
  have hac0 : 0 < _root_.SubdiffusiveProcess.Model.aCutoff M m eta (((3 : ℝ) ^ N) • xp) :=
    _root_.SubdiffusiveProcess.Model.aCutoff_pos M m eta _
  have hahom : 0 < ahom M m := ahom_pos M m
  -- for every admissible `K`, `sx = sw · exp(Sm K + bK K)`
  have hXK : ∀ K, m ≤ K → sx = sw * Real.exp (Sm K + bK K) := by
    intro K hK
    have h1 := aux_in_deterministic_good_scale_transfer_log_identity M H omega N l hl eta hEta
      xp w K (hKm K hK)
    have h2 := aux_in_deterministic_good_scale_transfer_log_identity M H omega N l hl eta hEta
      xp xp K (hKm K hK)
    simp only at h1 h2
    have hE2 : (∑ k ∈ Finset.Ico (m + 1) (N + K + 1),
          (eta k (((3 : ℝ) ^ N) • xp) - eta k (((3 : ℝ) ^ N) • xp))) +
        ((H omega xp - H omega xp) -
          ∑ n ∈ Finset.range K,
            (omega (((n + 1 : ℕ) : ℤ)) xp - omega (((n + 1 : ℕ) : ℤ)) xp)) = 0 := by
      simp
    rw [hE2, Real.exp_zero, mul_one] at h2
    have hE1 : (∑ k ∈ Finset.Ico (m + 1) (N + K + 1),
          (eta k (((3 : ℝ) ^ N) • xp) - eta k (((3 : ℝ) ^ N) • w))) +
        ((H omega xp - H omega w) -
          ∑ n ∈ Finset.range K,
            (omega (((n + 1 : ℕ) : ℤ)) xp - omega (((n + 1 : ℕ) : ℤ)) w)) = Sm K + bK K := by
      simp only [Sm, bK, hvec, z]
    rw [hE1] at h1
    -- h1 : cut / sw = c * exp(...), h2 : cut / sx = c
    have h1' : cutoffCoefficient M H omega N xp / sw =
        (ahom M m)⁻¹ * _root_.SubdiffusiveProcess.Model.aCutoff M m eta (((3 : ℝ) ^ N) • xp) *
          Real.exp (Sm K + bK K) := h1
    have h2' : cutoffCoefficient M H omega N xp / sx =
        (ahom M m)⁻¹ * _root_.SubdiffusiveProcess.Model.aCutoff M m eta (((3 : ℝ) ^ N) • xp) := h2
    set c : ℝ := (ahom M m)⁻¹ * _root_.SubdiffusiveProcess.Model.aCutoff M m eta (((3 : ℝ) ^ N) • xp)
      with hc
    have hc0 : 0 < c := mul_pos (inv_pos.mpr hahom) hac0
    have e1 : cutoffCoefficient M H omega N xp = c * Real.exp (Sm K + bK K) * sw := by
      rw [div_eq_iff hsw0.ne'] at h1'; exact h1'
    have e2 : cutoffCoefficient M H omega N xp = c * sx := by
      rw [div_eq_iff hsx0.ne'] at h2'; exact h2'
    have : c * sx = c * (sw * Real.exp (Sm K + bK K)) := by rw [← e2, e1]; ring
    exact mul_left_cancel₀ hc0.ne' this
  -- the common exponent and its bound
  set X : ℝ := Sm m + bK m with hXdef
  have hXeq : ∀ K, m ≤ K → X = Sm K + bK K := by
    intro K hK
    have h0 := hXK m le_rfl
    have h1 := hXK K hK
    have : sw * Real.exp X = sw * Real.exp (Sm K + bK K) := by rw [← h0, ← h1]
    exact Real.exp_injective (mul_left_cancel₀ hsw0.ne' this)
  have hbT := aux_in_deterministic_good_scale_transfer_ir_remainder H omega hIR xp w
  have hSB : ∀ K, m ≤ K → |Sm K| ≤ (d : ℝ) * T := by
    intro K _
    have habs : |Sm K| ≤ ∑ k ∈ Finset.Ico (m + 1) (N + K + 1),
        |eta k (((3 : ℝ) ^ m) • x + z) - eta k z| := Finset.abs_sum_le_sum_abs _ _
    refine habs.trans ?_
    refine (aux_in_deterministic_good_scale_transfer_gradient_block eta m z hx _ _).trans ?_
    exact mul_le_mul_of_nonneg_left
      (aux_in_deterministic_good_scale_transfer_T_bound M s eps eta Fsc Psc Rsc Dsc Zsc
        goodEvt hPS m z hD _ _ (Nat.le_succ m))
      (Nat.cast_nonneg d)
  have hXle := aux_in_deterministic_good_scale_transfer_limit_bound X _ Sm bK m hXeq hbT hSB
  rw [hXK m le_rfl, ← hXdef]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ((le_abs_self X).trans hXle)) hsw0.le

end SubdiffusiveProcess.Paper
end
end DeterministicRegularity_OneStep_Ratio

section DeterministicRegularity_OneStep_Geo

/-!
# Self-root descendants containing a point 

  Every point of the closed cube of centre `z` and side `r` lies in the closed
depth-`D` descendant cell (odd grid, `m = 1`) of some word, and that descendant's centre is at
sup-distance at most `r/2 - side_D/2` from `z`.
-/

open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_in_deterministic_onestep_oddGridCenter_one {d : ℕ} (c : SpatialCoordinates d)
    (r : ℝ) (k : OddGridIndex d 1) (i : Fin d) :
    oddGridCenter c r 1 k i = c i + (((k i).val : ℝ) - 1) * (r / 3) := by
  unfold oddGridCenter
  norm_num

/-- One subdivision step. -/
theorem aux_in_deterministic_onestep_child_exists {d : ℕ} (c x : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (hx : ∀ i, |x i - c i| ≤ r / 2) :
    ∃ k : OddGridIndex d 1, ∀ i,
      |x i - oddGridCenter c r 1 k i| ≤ r / 6 ∧ |oddGridCenter c r 1 k i - c i| ≤ r / 3 := by
  classical
  let k : OddGridIndex d 1 := fun i =>
    if x i - c i < -(r / 6) then ⟨0, by norm_num⟩
    else if r / 6 < x i - c i then ⟨2, by norm_num⟩ else ⟨1, by norm_num⟩
  refine ⟨k, fun i => ?_⟩
  rw [aux_in_deterministic_onestep_oddGridCenter_one]
  have hxi := abs_le.mp (hx i)
  by_cases h1 : x i - c i < -(r / 6)
  · have hk : ((k i).val : ℝ) = 0 := by simp [k, h1]
    rw [hk]
    constructor
    · rw [abs_le]; constructor <;> linarith
    · rw [abs_le]; constructor <;> linarith
  · by_cases h2 : r / 6 < x i - c i
    · have hk : ((k i).val : ℝ) = 2 := by simp [k, h1, h2]
      rw [hk]
      constructor
      · rw [abs_le]; constructor <;> linarith
      · rw [abs_le]; constructor <;> linarith
    · have hk : ((k i).val : ℝ) = 1 := by simp [k, h1, h2]
      rw [hk]
      push Not at h1 h2
      constructor
      · rw [abs_le]; constructor <;> linarith
      · rw [abs_le]; constructor <;> linarith

/-- **Depth-`D` descendant containing a point.** -/
theorem aux_in_deterministic_onestep_descendant_exists {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (x : SpatialCoordinates d) (hx : ∀ i, |x i - z i| ≤ r / 2) :
    ∀ D : ℕ, ∃ w : Fin D → OddGridIndex d 1, ∀ i,
      |x i - descendantCenter 1 z r D w i| ≤ descendantSide 1 D r / 2 ∧
      |descendantCenter 1 z r D w i - z i| ≤ r / 2 - descendantSide 1 D r / 2 := by
  intro D
  induction D with
  | zero =>
    refine ⟨Fin.elim0, fun i => ?_⟩
    simp only [descendantCenter, descendantSide_zero, sub_self, abs_zero]
    exact ⟨hx i, by linarith⟩
  | succ n ih =>
    obtain ⟨w, hw⟩ := ih
    have hsn : 0 < descendantSide 1 n r := descendantSide_pos 1 n hr
    obtain ⟨k, hk⟩ := aux_in_deterministic_onestep_child_exists
      (descendantCenter 1 z r n w) x (descendantSide 1 n r) hsn (fun i => (hw i).1)
    refine ⟨Fin.snoc w k, fun i => ?_⟩
    have hc : descendantCenter 1 z r (n + 1) (Fin.snoc w k) =
        oddGridCenter (descendantCenter 1 z r n w) (descendantSide 1 n r) 1 k := by
      simp only [descendantCenter, Fin.snoc_castSucc, Fin.snoc_last]
    have hs : descendantSide 1 (n + 1) r = descendantSide 1 n r / 3 := by
      rw [descendantSide_succ]; norm_num
    rw [hc, hs]
    obtain ⟨h1, h2⟩ := hk i
    obtain ⟨_, h4⟩ := hw i
    refine ⟨by linarith, ?_⟩
    calc |oddGridCenter (descendantCenter 1 z r n w) (descendantSide 1 n r) 1 k i - z i|
        ≤ |oddGridCenter (descendantCenter 1 z r n w) (descendantSide 1 n r) 1 k i -
            descendantCenter 1 z r n w i| + |descendantCenter 1 z r n w i - z i| :=
          abs_sub_le _ _ _
      _ ≤ descendantSide 1 n r / 3 + (r / 2 - descendantSide 1 n r / 2) := add_le_add h2 h4
      _ = r / 2 - descendantSide 1 n r / 3 / 2 := by ring

theorem aux_in_deterministic_onestep_descendantSide_one (D : ℕ) (r : ℝ) :
    descendantSide 1 D r = r / 3 ^ D := by
  unfold descendantSide
  norm_num

end SubdiffusiveProcess.Paper
end
end DeterministicRegularity_OneStep_Geo

section DeterministicRegularity_OneStep_UpperAt




open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- `3^{s/8} ≤ 2` for `s ≤ 1`. -/
theorem aux_in_deterministic_onestep_three_rpow_le_two (s : ℝ) (hs : s ≤ 1) (_hs0 : 0 ≤ s) :
    (3 : ℝ) ^ (s / 8) ≤ 2 := by
  have h1 : (3 : ℝ) ^ (s / 8) ≤ (3 : ℝ) ^ ((1 : ℝ) / 8) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  refine h1.trans ?_
  rw [show (2 : ℝ) = ((2 : ℝ) ^ (8 : ℕ)) ^ ((1 : ℝ) / 8) by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num]
  exact Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)

/-- A layer of the physical field at a point is controlled by the `Draw` score of its level. -/
theorem aux_in_deterministic_onestep_omega_le_draw {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (omega : BilateralField d) (N : ℕ)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (s eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (w : SpatialCoordinates d) (i : ℤ) (hi : i < (N : ℤ))
    (hD : Dsc ((N : ℤ) - i).toNat (((3 : ℝ) ^ N) • w) ≠ ⊤) :
    |omega (-i) w| ≤ 2 * (Dsc ((N : ℤ) - i).toNat (((3 : ℝ) ^ N) • w)).toReal := by
  have hK : 1 ≤ ((N : ℤ) - i).toNat := by omega
  have h := aux_in_deterministic_onestep_layer_le_draw M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt
    hPS _ hK _ hD
  have heta : eta ((N : ℤ) - i).toNat (((3 : ℝ) ^ N) • w) = omega (-i) w := by
    rw [hEta]
    have hc : ((((N : ℤ) - i).toNat : ℕ) : ℤ) - (N : ℤ) = -i := by
      rw [Int.toNat_of_nonneg (by omega)]; ring
    rw [hc, smul_smul, _root_.zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity), one_smul]
  rw [heta] at h
  have h3 : 0 < (3 : ℝ) ^ (-(s / 8)) := Real.rpow_pos_of_pos (by norm_num) _
  have h32 := aux_in_deterministic_onestep_three_rpow_le_two s hs.2 hs.1.le
  have hinv : (3 : ℝ) ^ (s / 8) * (3 : ℝ) ^ (-(s / 8)) = 1 := by
    rw [← Real.rpow_add (by norm_num)]; simp
  have hD0 : 0 ≤ (Dsc ((N : ℤ) - i).toNat (((3 : ℝ) ^ N) • w)).toReal := ENNReal.toReal_nonneg
  calc |omega (-i) w| = (3 : ℝ) ^ (s / 8) * ((3 : ℝ) ^ (-(s / 8)) * |omega (-i) w|) := by
        rw [← mul_assoc, hinv, one_mul]
    _ ≤ (3 : ℝ) ^ (s / 8) * (Dsc ((N : ℤ) - i).toNat (((3 : ℝ) ^ N) • w)).toReal :=
        mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (by norm_num) _)
    _ ≤ 2 * (Dsc ((N : ℤ) - i).toNat (((3 : ℝ) ^ N) • w)).toReal :=
        mul_le_mul_of_nonneg_right h32 hD0

/-- **The reference comparison along the ray (paper `e.ratio.of.bs`).**  For a level `l` of
the prefix of the observation centre `w`, the coarse reference `sref(k, qcenter)` is at most
`exp((d+2) Σ Draw + (l-k) δ²)` times the fine reference `sref(l, w)`. -/
theorem aux_in_deterministic_onestep_ratio_ray {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)))
    (s eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (k : ℕ) (qcenter w : SpatialCoordinates d)
    (hwq : ∀ i, |w i - qcenter i| < (3 : ℝ) ^ (-(k : ℤ)) / 2)
    (S : Finset ℤ) (hkS : (k : ℤ) ∈ S) (l : ℤ) (hkl : (k : ℤ) ≤ l) (hlN : l ≤ (N : ℤ))
    (hIcoS : Finset.Ico (k : ℤ) l ⊆ S)
    (hfin : ∀ i ∈ S, Dsc ((N : ℤ) - i).toNat (((3 : ℝ) ^ N) • w) ≠ ⊤)
    (Sig : ℝ)
    (hSig : ∑ i ∈ S, (Dsc ((N : ℤ) - i).toNat (((3 : ℝ) ^ N) • w)).toReal ≤ Sig) :
    aux_in_deterministic_onestep_sref M H omega N k qcenter ≤
      aux_in_deterministic_onestep_sref M H omega N l w *
        Real.exp (((d : ℝ) + 2) * Sig + ((l - k : ℤ) : ℝ) * M.delta ^ 2) := by
  set Dl : ℤ → ℝ := fun i => (Dsc ((N : ℤ) - i).toNat (((3 : ℝ) ^ N) • w)).toReal with hDl
  have hD0 : ∀ i, 0 ≤ Dl i := fun i => ENNReal.toReal_nonneg
  have hkN : (k : ℤ) ≤ N := hkl.trans hlN
  -- point comparison at level `k`
  set xq : Vec d := fun i => (3 : ℝ) ^ (k : ℤ) * (qcenter i - w i) with hxq
  have hxq_mem : xq ∈ Homogenization.openCubeSet (Homogenization.originCube d 0) := by
    rw [Homogenization.mem_openCubeSet_originCube_iff]
    intro i
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (k : ℤ) := zpow_pos (by norm_num) _
    have hw := abs_lt.mp (hwq i)
    have hinv : (3 : ℝ) ^ (k : ℤ) * (3 : ℝ) ^ (-(k : ℤ)) = 1 := by
      rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]; simp
    simp only [xq, zpow_zero, mul_one]
    constructor
    · have : (3 : ℝ) ^ (k : ℤ) * (-( (3 : ℝ) ^ (-(k : ℤ)) / 2)) <
          (3 : ℝ) ^ (k : ℤ) * (qcenter i - w i) :=
        mul_lt_mul_of_pos_left (by linarith [hw.1, hw.2]) h3
      nlinarith [hinv]
    · have : (3 : ℝ) ^ (k : ℤ) * (qcenter i - w i) <
          (3 : ℝ) ^ (k : ℤ) * ((3 : ℝ) ^ (-(k : ℤ)) / 2) :=
        mul_lt_mul_of_pos_left (by linarith [hw.1, hw.2]) h3
      nlinarith [hinv]
  have hpt := aux_in_deterministic_onestep_sref_point_le M H omega N (k : ℤ) hkN eta hEta hIR
    s eps Fsc Psc Rsc Dsc Zsc goodEvt hPS w (hfin _ hkS) xq hxq_mem
  have hqc : (fun i => w i + (3 : ℝ) ^ (-(k : ℤ)) * xq i) = qcenter := by
    funext i
    simp only [xq]
    rw [← mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    simp
  rw [hqc] at hpt
  -- level comparison at `w`
  have hlev := aux_in_deterministic_onestep_sref_level_le M H omega N (k : ℤ) l
    (Nat.cast_nonneg k) hkl hlN w
  -- the layer sum
  have hlay : ∑ i ∈ Finset.Ico (k : ℤ) l, |omega (-i) w| ≤ 2 * Sig := by
    calc ∑ i ∈ Finset.Ico (k : ℤ) l, |omega (-i) w|
        ≤ ∑ i ∈ Finset.Ico (k : ℤ) l, 2 * Dl i := by
          apply Finset.sum_le_sum
          intro i hi
          have hil : i < l := (Finset.mem_Ico.mp hi).2
          exact aux_in_deterministic_onestep_omega_le_draw M omega N eta hEta s eps hs
            Fsc Psc Rsc Dsc Zsc goodEvt hPS w i (by omega) (hfin i (hIcoS hi))
      _ = 2 * ∑ i ∈ Finset.Ico (k : ℤ) l, Dl i := by rw [Finset.mul_sum]
      _ ≤ 2 * ∑ i ∈ S, Dl i := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Finset.sum_le_sum_of_subset_of_nonneg hIcoS (fun i _ _ => hD0 i)
      _ ≤ 2 * Sig := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact hSig
  have hDk : Dl k ≤ Sig :=
    (Finset.single_le_sum (fun i _ => hD0 i) hkS).trans hSig
  -- the disorder term
  have htau : ((l - k : ℤ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P ≤
      ((l - k : ℤ) : ℝ) * M.delta ^ 2 := by
    have hlk : (0 : ℝ) ≤ ((l - k : ℤ) : ℝ) := by
      have : (0 : ℤ) ≤ l - k := by omega
      exact_mod_cast this
    have ht := SubdiffusiveProcess.CoarseGrainingVocab.tauSq_le_delta_sq M
    have hl2 : Real.log 2 / 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    have : _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ M.delta ^ 2 :=
      ht.trans (by nlinarith [sq_nonneg M.delta])
    exact mul_le_mul_of_nonneg_left this hlk
  have hs0 := aux_in_deterministic_onestep_sref_pos M H omega N l w
  have hsk0 := aux_in_deterministic_onestep_sref_pos M H omega N k w
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hexp1 : (d : ℝ) * Dl k ≤ (d : ℝ) * Sig := mul_le_mul_of_nonneg_left hDk hd0
  calc aux_in_deterministic_onestep_sref M H omega N k qcenter
      ≤ aux_in_deterministic_onestep_sref M H omega N k w * Real.exp ((d : ℝ) * Dl k) := hpt
    _ ≤ (aux_in_deterministic_onestep_sref M H omega N l w *
          Real.exp (((l - k : ℤ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
            ∑ i ∈ Finset.Ico (k : ℤ) l, |omega (-i) w|)) * Real.exp ((d : ℝ) * Dl k) :=
        mul_le_mul_of_nonneg_right hlev (Real.exp_pos _).le
    _ = aux_in_deterministic_onestep_sref M H omega N l w *
          Real.exp ((d : ℝ) * Dl k + (((l - k : ℤ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
            ∑ i ∈ Finset.Ico (k : ℤ) l, |omega (-i) w|)) := by
        rw [Real.exp_add ((d : ℝ) * Dl k)]; ring
    _ ≤ aux_in_deterministic_onestep_sref M H omega N l w *
          Real.exp (((d : ℝ) + 2) * Sig + ((l - k : ℤ) : ℝ) * M.delta ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hs0.le
        apply Real.exp_le_exp.mpr
        nlinarith [hlay, htau, hexp1]

/-- **The upper range at one sample, depth and point.** -/
theorem aux_in_deterministic_onestep_upper_at
    (d : ℕ) [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha s : ℝ)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (h : ℕ) (theta Ceps Cdel E0 : ℝ) (hCeps : 0 ≤ Ceps) (hCdel : 0 ≤ Cdel)
    (hOS : aux_in_deterministic_onestep_window d I alpha s h theta Ceps Cdel E0)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)))
    (eps : ℝ)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (Cg : ℝ) (hCg : 0 ≤ Cg)
    (hG : ∀ (j : ℤ) (w : SpatialCoordinates d), j ≤ (N : ℤ) →
      Dsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) ≠ ⊤ →
      Zsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) < 1 →
      I.err w ((3 : ℝ) ^ (-j)) (by positivity)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
          w ((3 : ℝ) ^ (-j)) (aux_in_deterministic_onestep_sref M H omega N j w) s 2 ≤
        Cg * (M.delta ^ 2 + eps ^ 8 +
          (Dsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w)).toReal))
    (c0 : ℝ) (hc0 : 0 < c0) (hcap : Cg * (M.delta ^ 2 + eps ^ 8) + Cg * c0 ≤ E0)
    (k cbuf k0 DA : ℕ) (hkDA : k + DA ≤ N) (jlo : ℤ)
    (hjlo1 : jlo ≤ -((k : ℤ) + DA) + 4) (hjlo2 : -((k : ℤ) + DA) - 2 ≤ jlo)
    (qcenter x w : SpatialCoordinates d)
    (hx : x ∈ Metric.ball qcenter ((3 : ℝ) ^ (-(k : ℤ)) / 2))
    (hxw : ∀ i, |x i - w i| ≤ (3 : ℝ) ^ (-((k : ℤ) + DA)) / 2)
    (hwq : ∀ i, |w i - qcenter i| < (3 : ℝ) ^ (-(k : ℤ)) / 2)
    (lamCut : ℝ) (hlam : 0 ≤ lamCut)
    (hprefix : k0 ≤ DA →
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
          Zsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w) < lamCut * DA ∧
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
          (Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w)).toReal < lamCut * DA)
    (hfin : k0 ≤ DA → ∀ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
      Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w) ≠ ⊤)
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (hqpQ : Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2) ⊆
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
    (f : SpatialCoordinates d → ℝ)
    (hf : MemLp f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
    (fL2 : DomainL2 (centeredCube Qcentre Qside hQside))
    (hfL2 : (fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] f)
    (u : weakSobolevGraph (centeredCube Qcentre Qside hQside))
    (hu : ∀ psi : killedSobolevGraph (centeredCube Qcentre Qside hQside),
        sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
          (u : SobolevData (centeredCube Qcentre Qside hQside))
          (psi : SobolevData (centeredCube Qcentre Qside hQside)) =
        sobolevVolumeLoad fL2 (psi : SobolevData (centeredCube Qcentre Qside hQside)))
    (U : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
    (huU : ((u : SobolevData (centeredCube Qcentre Qside hQside)).1 :
        SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U) :
    ∃ bad : Finset ℤ, bad ⊆ Finset.Icc jlo (-(k : ℤ)) ∧ ∃ epsilon defect : ℤ → ℝ,
      (∀ j ∈ Finset.Icc jlo (-(k : ℤ)), 0 ≤ epsilon j ∧ 0 ≤ defect j) ∧
      (∀ j ∈ Finset.Icc jlo (-(k : ℤ)), j ∉ bad →
        ∀ ell : Affine d, ell ∈ affineMinimizers (translatedCube d j x) U →
          excess (j - (h : ℤ)) (translatedCube d (j - (h : ℤ)) x) U ≤
            theta ^ h * excess j (translatedCube d j x) U +
              epsilon j * Real.sqrt (vecNormSq ell.slope) + defect j) ∧
      (bad.card : ℝ) ≤ 10 + k0 + lamCut * DA * (1 + c0⁻¹) ∧
      ∑ j ∈ Finset.Icc jlo (-(k : ℤ)), epsilon j ≤
        Ceps * Cg * ((M.delta ^ 2 + eps ^ 8) * ((DA : ℝ) + 1) + lamCut * DA) ∧
      ∑ j ∈ Finset.Icc jlo (-(k : ℤ)), defect j ≤
        Cdel * (Real.exp (((d : ℝ) + 2) * (lamCut * DA) + (DA : ℝ) * M.delta ^ 2) *
            (aux_in_deterministic_onestep_sref M H omega N k qcenter)⁻¹) *
          (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
            (volume.restrict (Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2)))).toReal *
          ∑ j ∈ Finset.Icc jlo (-(k : ℤ)), (3 : ℝ) ^ (alpha * (j : ℝ)) := by
  set F : ℝ := (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
    (volume.restrict (Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2)))).toReal with hF
  set sk : ℝ := aux_in_deterministic_onestep_sref M H omega N k qcenter with hsk
  have hsk0 : 0 < sk := aux_in_deterministic_onestep_sref_pos M H omega N k qcenter
  set Y : ℝ := ((d : ℝ) + 2) * (lamCut * DA) + (DA : ℝ) * M.delta ^ 2 with hY
  have hRs : 0 ≤ Real.exp Y * sk⁻¹ := mul_nonneg (Real.exp_pos _).le (inv_nonneg.mpr hsk0.le)
  refine aux_in_deterministic_onestep_upper_core k DA cbuf k0 jlo hjlo1 hjlo2
    (fun l => Zsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w))
    (fun l => (Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w)).toReal)
    (fun l => aux_in_deterministic_onestep_Z_nonneg M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt hPS
      _ _)
    (fun l => ENNReal.toReal_nonneg)
    lamCut c0 Cg (M.delta ^ 2 + eps ^ 8) Ceps Cdel F (Real.exp Y * sk⁻¹) alpha
    hlam hc0 hCg (by positivity) hCeps hCdel ENNReal.toReal_nonneg hRs hprefix
    (fun j => I.err w ((3 : ℝ) ^ (-(-j - 2))) (by positivity)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
      w ((3 : ℝ) ^ (-(-j - 2))) (aux_in_deterministic_onestep_sref M H omega N (-j - 2) w) s 2)
    (fun j => aux_in_deterministic_onestep_sref M H omega N (-j - 2) w)
    (fun j => I.err_nonneg _ _ _ _ _ _ _ _ _)
    (fun j => aux_in_deterministic_onestep_sref_pos M H omega N (-j - 2) w)
    (fun j e δ => ∀ ell : Affine d, ell ∈ affineMinimizers (translatedCube d j x) U →
      excess (j - (h : ℤ)) (translatedCube d (j - (h : ℤ)) x) U ≤
        theta ^ h * excess j (translatedCube d j x) U + e * Real.sqrt (vecNormSq ell.slope) + δ)
    ?_
  intro j hj hk0 hZ hD
  rw [Finset.mem_Icc] at hj
  have hlN : -j - 2 ≤ (N : ℤ) := by omega
  have hlS : -j - 2 ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA) := by
    rw [Finset.mem_Icc]; constructor <;> omega
  have herr := hG (-j - 2) w hlN (hfin hk0 _ hlS) hZ
  refine ⟨herr, ?_, ?_⟩
  · -- the reference comparison along the ray
    have hSig := (hprefix hk0).2.le
    have hray := aux_in_deterministic_onestep_ratio_ray M H omega N eta hEta hIR s eps hs
      Fsc Psc Rsc Dsc Zsc goodEvt hPS k qcenter w hwq
      (Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA))
      (by rw [Finset.mem_Icc]; constructor <;> omega) (-j - 2) (by omega) hlN
      (by intro i hi; rw [Finset.mem_Ico] at hi; rw [Finset.mem_Icc]; constructor <;> omega)
      (hfin hk0) (lamCut * DA) hSig
    have hpos := aux_in_deterministic_onestep_sref_pos M H omega N (-j - 2) w
    have hlk : ((-j - 2 - (k : ℤ) : ℤ) : ℝ) * M.delta ^ 2 ≤ (DA : ℝ) * M.delta ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have : -j - 2 - (k : ℤ) ≤ (DA : ℤ) := by omega
      exact_mod_cast this
    have hray' : sk ≤ aux_in_deterministic_onestep_sref M H omega N (-j - 2) w * Real.exp Y := by
      refine hray.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hpos.le)
      rw [hY]; linarith
    show (aux_in_deterministic_onestep_sref M H omega N (-j - 2) w)⁻¹ ≤ Real.exp Y * sk⁻¹
    have hq : sk * (aux_in_deterministic_onestep_sref M H omega N (-j - 2) w)⁻¹ ≤
        Real.exp Y := by
      rw [← div_eq_mul_inv, div_le_iff₀ hpos]; linarith [hray']
    calc (aux_in_deterministic_onestep_sref M H omega N (-j - 2) w)⁻¹
        = sk⁻¹ * (sk * (aux_in_deterministic_onestep_sref M H omega N (-j - 2) w)⁻¹) := by
          field_simp
      _ ≤ sk⁻¹ * Real.exp Y := mul_le_mul_of_nonneg_left hq (inv_nonneg.mpr hsk0.le)
      _ = Real.exp Y * sk⁻¹ := mul_comm _ _
  · -- the one-step estimate from the per-window input
    intro ell hell
    have hE : I.err w ((3 : ℝ) ^ (-(-j - 2))) (by positivity)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
        w ((3 : ℝ) ^ (-(-j - 2))) (aux_in_deterministic_onestep_sref M H omega N (-j - 2) w) s 2
        ≤ E0 := by
      refine herr.trans ?_
      have : Cg * (M.delta ^ 2 + eps ^ 8 +
          (Dsc ((N : ℤ) - (-j - 2)).toNat (((3 : ℝ) ^ N) • w)).toReal) ≤
          Cg * (M.delta ^ 2 + eps ^ 8) + Cg * c0 := by
        have hDc := mul_le_mul_of_nonneg_left hD hCg
        rw [mul_add]; linarith
      linarith
    have hx' : x ∈ Metric.ball qcenter ((3 : ℝ) ^ (((1 : ℤ) - k) - 1) / 2) := by
      rw [show ((1 : ℤ) - k) - 1 = -(k : ℤ) by ring]; exact hx
    have hw : w ∈ Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2) := by
      rw [Metric.mem_ball, dist_pi_lt_iff (by positivity)]
      intro i
      rw [Real.dist_eq]
      refine (hwq i).trans_le ?_
      gcongr
      · norm_num
      · omega
    have hxw' : x ∈ Metric.ball w ((3 : ℝ) ^ (j - 3) / 2) := by
      rw [Metric.mem_ball, dist_pi_lt_iff (by positivity)]
      intro i
      rw [Real.dist_eq]
      refine (hxw i).trans_lt ?_
      have : (3 : ℝ) ^ (-((k : ℤ) + DA)) < (3 : ℝ) ^ (j - 3) :=
        zpow_lt_zpow_right₀ (by norm_num) (by omega)
      linarith
    exact hOS M H omega N Qcentre Qside hQside qcenter ((1 : ℤ) - k) hqpQ f hf fL2 hfL2 u hu U hU
      huU x hx' j (-j - 2) (by omega) (by ring) w hw hxw'
      (aux_in_deterministic_onestep_sref M H omega N (-j - 2) w)
      (aux_in_deterministic_onestep_sref_pos M H omega N (-j - 2) w) hE ell hell

end SubdiffusiveProcess.Paper
end
end DeterministicRegularity_OneStep_UpperAt

section DeterministicRegularity_OneStep_Budget




set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The bad-count budget. -/
theorem aux_in_deterministic_onestep_budget_card (k0 cbuf DA D lamCut lamDet t c0 C2 : ℝ)
    (hk0 : 0 ≤ k0) (hcbuf : 0 ≤ cbuf) (hDA : DA ≤ D) (hDA0 : 0 ≤ DA)
    (hlam : 0 ≤ lamCut) (hlt : lamCut ≤ lamDet) (ht : lamDet ≤ t) (hc0 : 0 < c0)
    (hC2 : 11 + c0⁻¹ ≤ C2) :
    10 + k0 + lamCut * DA * (1 + c0⁻¹) ≤ C2 * (1 + ((k0 + cbuf) + t * D)) := by
  have hD0 : 0 ≤ D := hDA0.trans hDA
  have ht0 : 0 ≤ t := hlam.trans (hlt.trans ht)
  have h1 : lamCut * DA ≤ t * D := mul_le_mul (hlt.trans ht) hDA hDA0 ht0
  have hci : 0 ≤ c0⁻¹ := inv_nonneg.mpr hc0.le
  have hX : 0 ≤ (k0 + cbuf) + t * D := by positivity
  have h2 : lamCut * DA * (1 + c0⁻¹) ≤ t * D * (1 + c0⁻¹) :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  have h3 : 10 + k0 + t * D * (1 + c0⁻¹) ≤ (11 + c0⁻¹) * (1 + ((k0 + cbuf) + t * D)) := by
    nlinarith [mul_nonneg hci hk0, mul_nonneg hci hcbuf, mul_nonneg hci (mul_nonneg ht0 hD0)]
  have h4 : (11 + c0⁻¹) * (1 + ((k0 + cbuf) + t * D)) ≤ C2 * (1 + ((k0 + cbuf) + t * D)) :=
    mul_le_mul_of_nonneg_right hC2 (by linarith)
  linarith

/-- The error-sum budget. -/
theorem aux_in_deterministic_onestep_budget_eps (k0 cbuf DA D lamCut lamDet dl ep Ceps Cg C2 : ℝ)
    (hk0 : 0 ≤ k0) (hcbuf : 0 ≤ cbuf) (hDA : DA ≤ D) (hDA0 : 0 ≤ DA)
    (hlam : 0 ≤ lamCut) (hlt : lamCut ≤ lamDet)
    (hdl0 : 0 ≤ dl) (hdl1 : dl ≤ 1) (hep0 : 0 ≤ ep) (hep1 : ep ≤ 1)
    (hCeps : 0 ≤ Ceps) (hCg : 0 ≤ Cg) (hC2 : 2 * Ceps * Cg ≤ C2) :
    Ceps * Cg * ((dl ^ 2 + ep ^ 8) * (DA + 1) + lamCut * DA) ≤
      C2 * (1 + ((k0 + cbuf) + (lamDet + dl ^ 2 + ep ^ 8) * D)) := by
  set t := lamDet + dl ^ 2 + ep ^ 8 with htdef
  have hD0 : 0 ≤ D := hDA0.trans hDA
  have hB0 : 0 ≤ dl ^ 2 + ep ^ 8 := by positivity
  have hB1 : dl ^ 2 + ep ^ 8 ≤ 2 := by
    have : dl ^ 2 ≤ 1 := by nlinarith
    have : ep ^ 8 ≤ 1 := pow_le_one₀ hep0 hep1
    linarith
  have hlamD : 0 ≤ lamDet := hlam.trans hlt
  have hA : (dl ^ 2 + ep ^ 8) * (DA + 1) + lamCut * DA ≤ 2 * (1 + t * D) := by
    have h1 : (dl ^ 2 + ep ^ 8) * DA ≤ (dl ^ 2 + ep ^ 8) * D := mul_le_mul_of_nonneg_left hDA hB0
    have h2 : lamCut * DA ≤ lamDet * D := mul_le_mul hlt hDA hDA0 hlamD
    have h3 : t * D = lamDet * D + (dl ^ 2 + ep ^ 8) * D := by rw [htdef]; ring
    nlinarith
  have hX : 0 ≤ (k0 + cbuf) + t * D := by
    have : 0 ≤ t := by rw [htdef]; positivity
    positivity
  calc Ceps * Cg * ((dl ^ 2 + ep ^ 8) * (DA + 1) + lamCut * DA)
      ≤ Ceps * Cg * (2 * (1 + t * D)) := mul_le_mul_of_nonneg_left hA (mul_nonneg hCeps hCg)
    _ = 2 * Ceps * Cg * (1 + t * D) := by ring
    _ ≤ 2 * Ceps * Cg * (1 + ((k0 + cbuf) + t * D)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ C2 * (1 + ((k0 + cbuf) + t * D)) := mul_le_mul_of_nonneg_right hC2 (by linarith)

/-- The defect budget: all the geometry and the reference comparison, collected. -/
theorem aux_in_deterministic_onestep_budget_defect (d : ℕ) (hd : 0 < d) (k : ℕ)
    (qside alpha Cdel Y sk Fq fN S X C2 T : ℝ)
    (hqside : qside = (3 : ℝ) ^ (-(k : ℤ))) (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hCdel : 0 ≤ Cdel) (hsk : 0 < sk) (hfN : 0 ≤ fN)
    (hFq : Fq = fN * ((3 * qside) ^ d) ^ (1 / ((d : ℝ) / (1 - alpha))))
    (_hS0 : 0 ≤ S) (hS : S ≤ (3 : ℝ) ^ (alpha * ((-(k : ℤ) : ℤ) : ℝ)) / (1 - (3 : ℝ) ^ (-alpha)))
    (hT : 0 ≤ T) (hY : Y ≤ ((d : ℝ) + 3) * T) (hTX : T ≤ X)
    (hC2a : 3 * Cdel / (1 - (3 : ℝ) ^ (-alpha)) ≤ C2)
    (hC2b : ((d : ℝ) + 3) / Real.log 3 ≤ C2) :
    qside * (Cdel * (Real.exp Y * sk⁻¹) * Fq * S) ≤
      C2 * (3 : ℝ) ^ (C2 * X) * (qside ^ 2 * sk⁻¹ * fN) := by
  have hq : 0 < qside := by rw [hqside]; positivity
  have hr : (3 : ℝ) ^ (-alpha) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hden : 0 < 1 - (3 : ℝ) ^ (-alpha) := by linarith
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  -- the volume factor
  have hV : ((3 * qside) ^ d) ^ (1 / ((d : ℝ) / (1 - alpha))) = (3 * qside) ^ (1 - alpha) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    field_simp
  -- the scale factor `3^{α(-k)} = qside^α`
  have hqa : (3 : ℝ) ^ (alpha * ((-(k : ℤ) : ℤ) : ℝ)) = qside ^ alpha := by
    rw [hqside, ← Real.rpow_intCast, ← Real.rpow_mul (by norm_num), mul_comm]
  have hgeo : qside * (3 * qside) ^ (1 - alpha) * qside ^ alpha = 3 ^ (1 - alpha) * qside ^ 2 := by
    rw [Real.mul_rpow (by norm_num) hq.le]
    have : qside * (3 ^ (1 - alpha) * qside ^ (1 - alpha)) * qside ^ alpha =
        3 ^ (1 - alpha) * (qside ^ (1 : ℝ) * qside ^ (1 - alpha) * qside ^ alpha) := by
      rw [Real.rpow_one]; ring
    rw [this, ← Real.rpow_add hq, ← Real.rpow_add hq]
    rw [show (1 : ℝ) + (1 - alpha) + alpha = ((2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have h3a : (3 : ℝ) ^ (1 - alpha) ≤ 3 := by
    calc (3 : ℝ) ^ (1 - alpha) ≤ (3 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 3 := Real.rpow_one 3
  have hexp : Real.exp Y ≤ (3 : ℝ) ^ (C2 * X) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    have h1 : Y ≤ Real.log 3 * (((d : ℝ) + 3) / Real.log 3 * T) := by
      have hl := hlog.ne'
      have : Real.log 3 * (((d : ℝ) + 3) / Real.log 3 * T) = ((d : ℝ) + 3) * T := by
        field_simp
      rw [this]; exact hY
    have hX0 : 0 ≤ X := hT.trans hTX
    have h2 : ((d : ℝ) + 3) / Real.log 3 * T ≤ C2 * X :=
      mul_le_mul hC2b hTX hT ((div_nonneg (by positivity) hlog.le).trans hC2b)
    nlinarith
  have hW : 0 ≤ qside ^ 2 * sk⁻¹ * fN := by positivity
  have hS' : qside * (3 * qside) ^ (1 - alpha) * S ≤
      3 ^ (1 - alpha) * qside ^ 2 / (1 - (3 : ℝ) ^ (-alpha)) := by
    have hp : 0 ≤ qside * (3 * qside) ^ (1 - alpha) := by positivity
    calc qside * (3 * qside) ^ (1 - alpha) * S
        ≤ qside * (3 * qside) ^ (1 - alpha) *
            ((3 : ℝ) ^ (alpha * ((-(k : ℤ) : ℤ) : ℝ)) / (1 - (3 : ℝ) ^ (-alpha))) :=
          mul_le_mul_of_nonneg_left hS hp
      _ = 3 ^ (1 - alpha) * qside ^ 2 / (1 - (3 : ℝ) ^ (-alpha)) := by
          rw [hqa, mul_div_assoc', hgeo]
  have hC2 : Cdel * 3 ^ (1 - alpha) / (1 - (3 : ℝ) ^ (-alpha)) ≤ C2 := by
    refine le_trans ?_ hC2a
    apply div_le_div_of_nonneg_right _ hden.le
    nlinarith
  have hC20 : 0 ≤ C2 := (div_nonneg (by positivity) hlog.le).trans hC2b
  rw [hFq, hV]
  calc qside * (Cdel * (Real.exp Y * sk⁻¹) * (fN * (3 * qside) ^ (1 - alpha)) * S)
      = (Cdel * Real.exp Y * sk⁻¹ * fN) * (qside * (3 * qside) ^ (1 - alpha) * S) := by ring
    _ ≤ (Cdel * Real.exp Y * sk⁻¹ * fN) *
          (3 ^ (1 - alpha) * qside ^ 2 / (1 - (3 : ℝ) ^ (-alpha))) :=
        mul_le_mul_of_nonneg_left hS' (by positivity)
    _ = (Cdel * 3 ^ (1 - alpha) / (1 - (3 : ℝ) ^ (-alpha))) * Real.exp Y *
          (qside ^ 2 * sk⁻¹ * fN) := by ring
    _ ≤ C2 * (3 : ℝ) ^ (C2 * X) * (qside ^ 2 * sk⁻¹ * fN) := by
        apply mul_le_mul_of_nonneg_right _ hW
        exact mul_le_mul hC2 hexp (Real.exp_pos _).le hC20

/-- Adding two budgets of the residual's form at their summed constant. -/
theorem aux_in_deterministic_onestep_budget_add (C2 Csub X W A1 A2 : ℝ)
    (hC2 : 0 ≤ C2) (hCs : 0 ≤ Csub) (hX : 0 ≤ X) (hW : 0 ≤ W)
    (h1 : A1 ≤ C2 * (3 : ℝ) ^ (C2 * X) * W) (h2 : A2 ≤ Csub * (3 : ℝ) ^ (Csub * X) * W) :
    A1 + A2 ≤ (C2 + Csub) * (3 : ℝ) ^ ((C2 + Csub) * X) * W := by
  have e1 : (3 : ℝ) ^ (C2 * X) ≤ (3 : ℝ) ^ ((C2 + Csub) * X) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  have e2 : (3 : ℝ) ^ (Csub * X) ≤ (3 : ℝ) ^ ((C2 + Csub) * X) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  have f1 : C2 * (3 : ℝ) ^ (C2 * X) * W ≤ C2 * (3 : ℝ) ^ ((C2 + Csub) * X) * W :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e1 hC2) hW
  have f2 : Csub * (3 : ℝ) ^ (Csub * X) * W ≤ Csub * (3 : ℝ) ^ ((C2 + Csub) * X) * W :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e2 hCs) hW
  have : C2 * (3 : ℝ) ^ ((C2 + Csub) * X) * W + Csub * (3 : ℝ) ^ ((C2 + Csub) * X) * W =
      (C2 + Csub) * (3 : ℝ) ^ ((C2 + Csub) * X) * W := by ring
  linarith

/-- The defect budget with a free exponent constant `κ` and an additive `1` in the exponent. -/
theorem aux_in_deterministic_onestep_budget_defect_gen (d : ℕ) (hd : 0 < d) (k : ℕ)
    (qside alpha Cdel Y sk Fq fN S X C2 T κ : ℝ)
    (hqside : qside = (3 : ℝ) ^ (-(k : ℤ))) (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hCdel : 0 ≤ Cdel) (hsk : 0 < sk) (hfN : 0 ≤ fN)
    (hFq : Fq = fN * ((3 * qside) ^ d) ^ (1 / ((d : ℝ) / (1 - alpha))))
    (hS : S ≤ (3 : ℝ) ^ (alpha * ((-(k : ℤ) : ℤ) : ℝ)) / (1 - (3 : ℝ) ^ (-alpha)))
    (hκ : 0 ≤ κ) (hT : 0 ≤ T) (hY : Y ≤ κ * T + 1) (hTX : T ≤ X)
    (hC2a : 9 * Cdel / (1 - (3 : ℝ) ^ (-alpha)) ≤ C2)
    (hC2b : κ / Real.log 3 ≤ C2) :
    qside * (Cdel * (Real.exp Y * sk⁻¹) * Fq * S) ≤
      C2 * (3 : ℝ) ^ (C2 * X) * (qside ^ 2 * sk⁻¹ * fN) := by
  have hq : 0 < qside := by rw [hqside]; positivity
  have hr : (3 : ℝ) ^ (-alpha) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hden : 0 < 1 - (3 : ℝ) ^ (-alpha) := by linarith
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hV : ((3 * qside) ^ d) ^ (1 / ((d : ℝ) / (1 - alpha))) = (3 * qside) ^ (1 - alpha) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    field_simp
  have hqa : (3 : ℝ) ^ (alpha * ((-(k : ℤ) : ℤ) : ℝ)) = qside ^ alpha := by
    rw [hqside, ← Real.rpow_intCast, ← Real.rpow_mul (by norm_num), mul_comm]
  have hgeo : qside * (3 * qside) ^ (1 - alpha) * qside ^ alpha =
      3 ^ (1 - alpha) * qside ^ 2 := by
    rw [Real.mul_rpow (by norm_num) hq.le]
    have : qside * (3 ^ (1 - alpha) * qside ^ (1 - alpha)) * qside ^ alpha =
        3 ^ (1 - alpha) * (qside ^ (1 : ℝ) * qside ^ (1 - alpha) * qside ^ alpha) := by
      rw [Real.rpow_one]; ring
    rw [this, ← Real.rpow_add hq, ← Real.rpow_add hq]
    rw [show (1 : ℝ) + (1 - alpha) + alpha = ((2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have h3a : (3 : ℝ) ^ (1 - alpha) ≤ 3 := by
    calc (3 : ℝ) ^ (1 - alpha) ≤ (3 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 3 := Real.rpow_one 3
  have hX0 : 0 ≤ X := hT.trans hTX
  have hC20 : 0 ≤ C2 := (div_nonneg hκ hlog.le).trans hC2b
  have hexp : Real.exp Y ≤ 3 * (3 : ℝ) ^ (C2 * X) := by
    have he1 : Real.exp Y ≤ Real.exp 1 * Real.exp (κ * T) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    have he2 : Real.exp 1 ≤ 3 := by
      have := Real.exp_one_lt_d9; linarith
    have he3 : Real.exp (κ * T) ≤ (3 : ℝ) ^ (C2 * X) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      apply Real.exp_le_exp.mpr
      have h1 : κ * T = Real.log 3 * (κ / Real.log 3 * T) := by
        field_simp
      have h2 : κ / Real.log 3 * T ≤ C2 * X := mul_le_mul hC2b hTX hT hC20
      rw [h1]
      exact mul_le_mul_of_nonneg_left h2 hlog.le
    calc Real.exp Y ≤ Real.exp 1 * Real.exp (κ * T) := he1
      _ ≤ 3 * (3 : ℝ) ^ (C2 * X) := mul_le_mul he2 he3 (Real.exp_pos _).le (by norm_num)
  have hW : 0 ≤ qside ^ 2 * sk⁻¹ * fN := by positivity
  have hS' : qside * (3 * qside) ^ (1 - alpha) * S ≤
      3 ^ (1 - alpha) * qside ^ 2 / (1 - (3 : ℝ) ^ (-alpha)) := by
    have hp : 0 ≤ qside * (3 * qside) ^ (1 - alpha) := by positivity
    calc qside * (3 * qside) ^ (1 - alpha) * S
        ≤ qside * (3 * qside) ^ (1 - alpha) *
            ((3 : ℝ) ^ (alpha * ((-(k : ℤ) : ℤ) : ℝ)) / (1 - (3 : ℝ) ^ (-alpha))) :=
          mul_le_mul_of_nonneg_left hS hp
      _ = 3 ^ (1 - alpha) * qside ^ 2 / (1 - (3 : ℝ) ^ (-alpha)) := by
          rw [hqa, mul_div_assoc', hgeo]
  have hC2 : Cdel * 3 ^ (1 - alpha) / (1 - (3 : ℝ) ^ (-alpha)) * 3 ≤ C2 := by
    refine le_trans ?_ hC2a
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hden.le
    nlinarith
  rw [hFq, hV]
  calc qside * (Cdel * (Real.exp Y * sk⁻¹) * (fN * (3 * qside) ^ (1 - alpha)) * S)
      = (Cdel * Real.exp Y * sk⁻¹ * fN) * (qside * (3 * qside) ^ (1 - alpha) * S) := by ring
    _ ≤ (Cdel * Real.exp Y * sk⁻¹ * fN) *
          (3 ^ (1 - alpha) * qside ^ 2 / (1 - (3 : ℝ) ^ (-alpha))) :=
        mul_le_mul_of_nonneg_left hS' (by positivity)
    _ = (Cdel * 3 ^ (1 - alpha) / (1 - (3 : ℝ) ^ (-alpha))) * Real.exp Y *
          (qside ^ 2 * sk⁻¹ * fN) := by ring
    _ ≤ (Cdel * 3 ^ (1 - alpha) / (1 - (3 : ℝ) ^ (-alpha))) * (3 * (3 : ℝ) ^ (C2 * X)) *
          (qside ^ 2 * sk⁻¹ * fN) := by
        apply mul_le_mul_of_nonneg_right _ hW
        apply mul_le_mul_of_nonneg_left hexp
        have : 0 ≤ Cdel * 3 ^ (1 - alpha) := by positivity
        exact div_nonneg this hden.le
    _ = (Cdel * 3 ^ (1 - alpha) / (1 - (3 : ℝ) ^ (-alpha)) * 3) * (3 : ℝ) ^ (C2 * X) *
          (qside ^ 2 * sk⁻¹ * fN) := by ring
    _ ≤ C2 * (3 : ℝ) ^ (C2 * X) * (qside ^ 2 * sk⁻¹ * fN) := by
        apply mul_le_mul_of_nonneg_right _ hW
        exact mul_le_mul_of_nonneg_right hC2 (by positivity)

/-- Sub-cutoff count budget. -/
theorem aux_in_deterministic_onestep_budget_card_sub (a c1 G0 X C3 : ℝ) (ha : 0 ≤ a)
    (hc1 : 0 < c1) (hG0 : 0 ≤ G0) (hGX : G0 ≤ X) (hC3 : a / c1 + 2 ≤ C3) :
    a * G0 / c1 + 2 ≤ C3 * (1 + X) := by
  have hX : 0 ≤ X := hG0.trans hGX
  have hac : 0 ≤ a / c1 := div_nonneg ha hc1.le
  have h1 : a * G0 / c1 = a / c1 * G0 := by ring
  have h2 : a / c1 * G0 ≤ a / c1 * X := mul_le_mul_of_nonneg_left hGX hac
  have h3 : a / c1 * X ≤ C3 * X := mul_le_mul_of_nonneg_right (by linarith) hX
  have h4 : 2 ≤ C3 := by linarith
  nlinarith

/-- Sub-cutoff error-sum budget. -/
theorem aux_in_deterministic_onestep_budget_eps_sub (b G0 X C3 : ℝ) (hb : 0 ≤ b)
    (hG0 : 0 ≤ G0) (hGX : G0 ≤ X) (hC3 : b ≤ C3) :
    b * G0 ≤ C3 * (1 + X) := by
  have hX : 0 ≤ X := hG0.trans hGX
  have h1 : b * G0 ≤ C3 * X := mul_le_mul hC3 hGX hG0 (hb.trans hC3)
  have hC30 : 0 ≤ C3 := hb.trans hC3
  nlinarith

end SubdiffusiveProcess.Paper
end
end DeterministicRegularity_OneStep_Budget

section DeterministicRegularity_OneStep_Bridge




open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- Volume of the padded root `qp`. -/
theorem aux_in_deterministic_onestep_volume_qp {d : ℕ} (qcenter : SpatialCoordinates d)
    (qside : ℝ) (hq : 0 < qside) :
    volume.real (Metric.ball qcenter (3 * qside / 2)) = (3 * qside) ^ d := by
  rw [measureReal_def, Real.volume_pi_ball qcenter (by positivity), Fintype.card_fin,
    ENNReal.toReal_ofReal (by positivity)]
  ring_nf

/-- **The upper range at one point, with budgets in the residual's `C2` form.** -/
theorem aux_in_deterministic_onestep_at_point_upper
    (d : ℕ) [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha s : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (h : ℕ) (theta Ceps Cdel E0 : ℝ) (hCeps : 0 ≤ Ceps) (hCdel : 0 ≤ Cdel)
    (hOS : aux_in_deterministic_onestep_window d I alpha s h theta Ceps Cdel E0)
    (Cg c0 C2 Csub : ℝ) (hCg : 0 ≤ Cg) (hc0 : 0 < c0) (_hC20 : 0 ≤ C2)
    (hC2a : 11 + c0⁻¹ ≤ C2) (hC2b : 2 * Ceps * Cg ≤ C2)
    (hC2c : 3 * Cdel / (1 - (3 : ℝ) ^ (-alpha)) ≤ C2)
    (hC2d : ((d : ℝ) + 3) / Real.log 3 ≤ C2) (_hCsub : 0 ≤ Csub)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)))
    (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (hG : ∀ (j : ℤ) (w : SpatialCoordinates d), j ≤ (N : ℤ) →
      Dsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) ≠ ⊤ →
      Zsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) < 1 →
      I.err w ((3 : ℝ) ^ (-j)) (by positivity)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
          w ((3 : ℝ) ^ (-j)) (aux_in_deterministic_onestep_sref M H omega N j w) s 2 ≤
        Cg * (M.delta ^ 2 + eps ^ 8 +
          (Dsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w)).toReal))
    (hcapE : Cg * (M.delta ^ 2 + eps ^ 8) + Cg * c0 ≤ E0)
    (hdel0 : 0 ≤ M.delta) (hdel1 : M.delta ≤ 1)
    (k cbuf k0 horizon : ℕ) (hkN : k ≤ N)
    (qside : ℝ) (hqpos : 0 < qside) (hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
    (qcenter : SpatialCoordinates d)
    (lambdaCut lambdaDet : ℝ) (hlam0 : 0 ≤ lambdaCut) (hlamlt : lambdaCut ≤ lambdaDet)
    (hpreAll : ∀ (DA : ℕ) (dword : Fin DA → OddGridIndex d 1), k0 ≤ DA → DA ≤ horizon →
      k + DA ≤ N →
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
          Zsc ((N : ℤ) - l).toNat
            (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside DA dword) < lambdaCut * DA ∧
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
          (Dsc ((N : ℤ) - l).toNat
            (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside DA dword)).toReal <
        lambdaCut * DA)
    (hfinAll : ∀ (DA : ℕ) (dword : Fin DA → OddGridIndex d 1), k + DA ≤ N →
      ∀ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
        Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside DA dword) ≠ ⊤)
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (hqp : Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2) ⊆
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
    (f : SpatialCoordinates d → ℝ)
    (hf : MemLp f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
    (fL2 : DomainL2 (centeredCube Qcentre Qside hQside))
    (hfL2 : (fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] f)
    (u : weakSobolevGraph (centeredCube Qcentre Qside hQside))
    (hu : ∀ psi : killedSobolevGraph (centeredCube Qcentre Qside hQside),
        sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
          (u : SobolevData (centeredCube Qcentre Qside hQside))
          (psi : SobolevData (centeredCube Qcentre Qside hQside)) =
        sobolevVolumeLoad fL2 (psi : SobolevData (centeredCube Qcentre Qside hQside)))
    (U : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
    (huU : ((u : SobolevData (centeredCube Qcentre Qside hQside)).1 :
        SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U)
    (sk fN : ℝ) (hsk : sk = aux_in_deterministic_onestep_sref M H omega N k qcenter)
    (hfN : 0 ≤ fN)
    (hFq : (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2)))).toReal =
      fN * ((3 * qside) ^ d) ^ (1 / ((d : ℝ) / (1 - alpha))))
    (D : ℕ) (hDh : D ≤ horizon) (x : SpatialCoordinates d)
    (hx : x ∈ Metric.ball qcenter (qside / 2))
    (jlo : ℤ) (hjlo1 : jlo ≤ -((k : ℤ) + (min D (N - k) : ℕ)) + 4)
    (hjlo2 : -((k : ℤ) + (min D (N - k) : ℕ)) - 2 ≤ jlo) :
    ∃ bad : Finset ℤ, bad ⊆ Finset.Icc jlo (-(k : ℤ)) ∧
    ∃ epsilon defect : ℤ → ℝ,
      (∀ j ∈ Finset.Icc jlo (-(k : ℤ)), 0 ≤ epsilon j ∧ 0 ≤ defect j) ∧
      (∀ j ∈ Finset.Icc jlo (-(k : ℤ)), j ∉ bad →
        ∀ ell : Affine d, ell ∈ affineMinimizers (translatedCube d j x) U →
          excess (j - (h : ℤ)) (translatedCube d (j - (h : ℤ)) x) U ≤
            theta ^ h * excess j (translatedCube d j x) U +
              epsilon j * Real.sqrt (vecNormSq ell.slope) + defect j) ∧
      (bad.card : ℝ) ≤ C2 * (1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) ∧
      ∑ j ∈ Finset.Icc jlo (-(k : ℤ)), epsilon j ≤ C2 * (1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) ∧
      ∑ j ∈ Finset.Icc jlo (-(k : ℤ)), defect j ≤
        C2 * (3 : ℝ) ^ (C2 * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN) / qside := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hxq : ∀ i, |x i - qcenter i| < qside / 2 := by
    intro i
    have hx' : dist x qcenter < qside / 2 := hx
    rw [dist_pi_lt_iff (by positivity)] at hx'
    have := hx' i
    rwa [Real.dist_eq] at this
  obtain ⟨DA, hDAdef⟩ : ∃ DA : ℕ, DA = min D (N - k) := ⟨_, rfl⟩
  obtain ⟨dword, hdw⟩ := aux_in_deterministic_onestep_descendant_exists qcenter qside hqpos x
    (fun i => (hxq i).le) DA
  obtain ⟨w, hwdef⟩ : ∃ w : SpatialCoordinates d, w = descendantCenter 1 qcenter qside DA dword :=
    ⟨_, rfl⟩
  have hside : descendantSide 1 DA qside = (3 : ℝ) ^ (-((k : ℤ) + DA)) := by
    rw [aux_in_deterministic_onestep_descendantSide_one, hqside, neg_add,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), _root_.zpow_neg (3 : ℝ) (DA : ℤ), zpow_natCast,
      div_eq_mul_inv]
  have hxw : ∀ i, |x i - w i| ≤ (3 : ℝ) ^ (-((k : ℤ) + DA)) / 2 := by
    intro i; rw [← hside, hwdef]; exact (hdw i).1
  have hwq : ∀ i, |w i - qcenter i| < (3 : ℝ) ^ (-(k : ℤ)) / 2 := by
    intro i
    have h1 := (hdw i).2
    have h2 := descendantSide_pos 1 DA hqpos
    rw [← hqside, hwdef]; linarith
  have hkDA : k + DA ≤ N := by omega
  have hpre : k0 ≤ DA →
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
          Zsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w) < lambdaCut * DA ∧
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
          (Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w)).toReal < lambdaCut * DA := by
    intro hk0
    rw [hwdef]
    exact hpreAll DA dword hk0 (by omega) hkDA
  have hfin : k0 ≤ DA → ∀ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
      Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w) ≠ ⊤ := by
    intro _ l hl
    rw [hwdef]
    exact hfinAll DA dword hkDA l hl
  have hxk : x ∈ Metric.ball qcenter ((3 : ℝ) ^ (-(k : ℤ)) / 2) := by rw [← hqside]; exact hx
  have hup := fun (jlo : ℤ) (h1 : jlo ≤ -((k : ℤ) + DA) + 4) (h2 : -((k : ℤ) + DA) - 2 ≤ jlo) =>
    aux_in_deterministic_onestep_upper_at d I alpha s hs h theta Ceps Cdel E0 hCeps hCdel hOS
      M H omega N eta hEta hIR eps Fsc Psc Rsc Dsc Zsc goodEvt hPS Cg hCg hG c0 hc0 hcapE
      k cbuf k0 DA hkDA jlo h1 h2 qcenter x w hxk hxw hwq lambdaCut hlam0 hpre hfin
      Qcentre Qside hQside hqp f hf fL2 hfL2 u hu U hU huU
  -- budget constants
  have hlamD : 0 ≤ lambdaDet := hlam0.trans hlamlt
  have ht0 : 0 ≤ lambdaDet + M.delta ^ 2 + eps ^ 8 := by positivity
  have hX0 : 0 ≤ ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ))) := by positivity
  have hDA_le : (DA : ℝ) ≤ D := by rw [hDAdef]; exact_mod_cast (min_le_left D (N - k))
  have hsk0 : 0 < sk := by rw [hsk]; exact aux_in_deterministic_onestep_sref_pos M H omega N k qcenter
  have hW : 0 ≤ qside ^ 2 * sk⁻¹ * fN := by positivity
  have htl : lambdaCut ≤ lambdaDet + M.delta ^ 2 + eps ^ 8 := by
    have : 0 ≤ M.delta ^ 2 + eps ^ 8 := by positivity
    linarith
  have htd : M.delta ^ 2 ≤ lambdaDet + M.delta ^ 2 + eps ^ 8 := by
    have : 0 ≤ eps ^ 8 := by positivity
    linarith
  have hYb : ((d : ℝ) + 2) * (lambdaCut * DA) + (DA : ℝ) * M.delta ^ 2 ≤
      ((d : ℝ) + 3) * ((lambdaDet + M.delta ^ 2 + eps ^ 8) * D) := by
    have h1 : lambdaCut * DA ≤ (lambdaDet + M.delta ^ 2 + eps ^ 8) * D :=
      mul_le_mul htl hDA_le (Nat.cast_nonneg _) ht0
    have h2 : (DA : ℝ) * M.delta ^ 2 ≤ D * (lambdaDet + M.delta ^ 2 + eps ^ 8) :=
      mul_le_mul hDA_le htd (sq_nonneg _) (Nat.cast_nonneg D)
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith
  have hTX : (lambdaDet + M.delta ^ 2 + eps ^ 8) * D ≤ ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ))) := by
    have : (0 : ℝ) ≤ (k0 : ℝ) + (cbuf : ℝ) := by positivity
    linarith
  have hdefect := fun (Sm : ℝ) (hSm0 : 0 ≤ Sm)
      (hSm : Sm ≤ (3 : ℝ) ^ (alpha * ((-(k : ℤ) : ℤ) : ℝ)) / (1 - (3 : ℝ) ^ (-alpha))) =>
    aux_in_deterministic_onestep_budget_defect d hd k qside alpha Cdel
      (((d : ℝ) + 2) * (lambdaCut * DA) + (DA : ℝ) * M.delta ^ 2)
      sk _ fN Sm ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ))) C2 ((lambdaDet + M.delta ^ 2 + eps ^ 8) * D)
      hqside halpha.1 halpha.2 hCdel hsk0 hfN hFq hSm0 hSm (by positivity) hYb hTX hC2c hC2d
  have hgeo := fun (a : ℤ) => aux_in_deterministic_onestep_geom_sum_le alpha halpha.1 a (-(k : ℤ))
  have hgeo0 := fun (a : ℤ) => Finset.sum_nonneg (fun j (_ : j ∈ Finset.Icc a (-(k : ℤ))) =>
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (alpha * (j : ℝ)))
  have hcardB := aux_in_deterministic_onestep_budget_card (k0 : ℝ) (cbuf : ℝ) (DA : ℝ) (D : ℝ)
    lambdaCut lambdaDet (lambdaDet + M.delta ^ 2 + eps ^ 8) c0 C2 (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hDA_le (Nat.cast_nonneg _) hlam0 hlamlt
    (by have : 0 ≤ M.delta ^ 2 + eps ^ 8 := by positivity
        linarith) hc0 hC2a
  have hepsB := aux_in_deterministic_onestep_budget_eps (k0 : ℝ) (cbuf : ℝ) (DA : ℝ) (D : ℝ)
    lambdaCut lambdaDet M.delta eps Ceps Cg C2 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hDA_le
    (Nat.cast_nonneg _) hlam0 hlamlt hdel0 hdel1 heps.1.le heps.2.le hCeps hCg hC2b
  obtain ⟨bad, hbad, e, dl, hnn, hP, hc, hse, hsd⟩ :=
    hup jlo (by rw [hDAdef]; exact hjlo1) (by rw [hDAdef]; exact hjlo2)
  refine ⟨bad, hbad, e, dl, hnn, hP, hc.trans hcardB, hse.trans hepsB, ?_⟩
  have hU3 := hdefect _ (hgeo0 jlo) (hgeo jlo)
  rw [← hsk] at hsd
  rw [le_div_iff₀ hqpos, mul_comm]
  exact (mul_le_mul_of_nonneg_left hsd hqpos.le).trans hU3

/-- **The one-step data at one sample, one depth and one point.**  All inputs are explicit;
`hlow` is the sub-cutoff obligation at this point (used only when `k + D ≥ N + 2`). -/
theorem aux_in_deterministic_onestep_at_point
    (d : ℕ) [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha s : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (h : ℕ) (theta Ceps Cdel E0 : ℝ) (hCeps : 0 ≤ Ceps) (hCdel : 0 ≤ Cdel)
    (hOS : aux_in_deterministic_onestep_window d I alpha s h theta Ceps Cdel E0)
    (Cg c0 C2 Csub : ℝ) (hCg : 0 ≤ Cg) (hc0 : 0 < c0) (hC20 : 0 ≤ C2)
    (hC2a : 11 + c0⁻¹ ≤ C2) (hC2b : 2 * Ceps * Cg ≤ C2)
    (hC2c : 3 * Cdel / (1 - (3 : ℝ) ^ (-alpha)) ≤ C2)
    (hC2d : ((d : ℝ) + 3) / Real.log 3 ≤ C2) (hCsub : 0 ≤ Csub)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)))
    (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (hG : ∀ (j : ℤ) (w : SpatialCoordinates d), j ≤ (N : ℤ) →
      Dsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) ≠ ⊤ →
      Zsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) < 1 →
      I.err w ((3 : ℝ) ^ (-j)) (by positivity)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
          w ((3 : ℝ) ^ (-j)) (aux_in_deterministic_onestep_sref M H omega N j w) s 2 ≤
        Cg * (M.delta ^ 2 + eps ^ 8 +
          (Dsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w)).toReal))
    (hcapE : Cg * (M.delta ^ 2 + eps ^ 8) + Cg * c0 ≤ E0)
    (hdel0 : 0 ≤ M.delta) (hdel1 : M.delta ≤ 1)
    (k cbuf k0 horizon : ℕ) (hkN : k ≤ N)
    (qside : ℝ) (hqpos : 0 < qside) (hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
    (qcenter : SpatialCoordinates d)
    (lambdaCut lambdaDet : ℝ) (hlam0 : 0 ≤ lambdaCut) (hlamlt : lambdaCut ≤ lambdaDet)
    (hpreAll : ∀ (DA : ℕ) (dword : Fin DA → OddGridIndex d 1), k0 ≤ DA → DA ≤ horizon →
      k + DA ≤ N →
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
          Zsc ((N : ℤ) - l).toNat
            (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside DA dword) < lambdaCut * DA ∧
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
          (Dsc ((N : ℤ) - l).toNat
            (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside DA dword)).toReal <
        lambdaCut * DA)
    (hfinAll : ∀ (DA : ℕ) (dword : Fin DA → OddGridIndex d 1), k + DA ≤ N →
      ∀ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
        Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside DA dword) ≠ ⊤)
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (hqp : Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2) ⊆
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
    (f : SpatialCoordinates d → ℝ)
    (hf : MemLp f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
    (fL2 : DomainL2 (centeredCube Qcentre Qside hQside))
    (hfL2 : (fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] f)
    (u : weakSobolevGraph (centeredCube Qcentre Qside hQside))
    (hu : ∀ psi : killedSobolevGraph (centeredCube Qcentre Qside hQside),
        sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
          (u : SobolevData (centeredCube Qcentre Qside hQside))
          (psi : SobolevData (centeredCube Qcentre Qside hQside)) =
        sobolevVolumeLoad fL2 (psi : SobolevData (centeredCube Qcentre Qside hQside)))
    (U : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
    (huU : ((u : SobolevData (centeredCube Qcentre Qside hQside)).1 :
        SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U)
    (sk fN : ℝ) (hsk : sk = aux_in_deterministic_onestep_sref M H omega N k qcenter)
    (hfN : 0 ≤ fN)
    (hFq : (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2)))).toReal =
      fN * ((3 * qside) ^ d) ^ (1 / ((d : ℝ) / (1 - alpha))))
    (D : ℕ) (hDh : D ≤ horizon) (x : SpatialCoordinates d)
    (hx : x ∈ Metric.ball qcenter (qside / 2))
    (hlow : N + 1 < k + D →
      ∃ bad : Finset ℤ, bad ⊆ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3) ∧
      ∃ epsilon defect : ℤ → ℝ,
        (∀ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), 0 ≤ epsilon j ∧ 0 ≤ defect j) ∧
        (∀ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), j ∉ bad →
          ∀ ell : Affine d, ell ∈ affineMinimizers (translatedCube d j x) U →
            excess (j - (h : ℤ)) (translatedCube d (j - (h : ℤ)) x) U ≤
              theta ^ h * excess j (translatedCube d j x) U +
                epsilon j * Real.sqrt (vecNormSq ell.slope) + defect j) ∧
        (bad.card : ℝ) ≤ Csub * (1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) ∧
        ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), epsilon j ≤
          Csub * (1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) ∧
        qside * ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), defect j ≤
          Csub * (3 : ℝ) ^ (Csub * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN)) :
    ∃ bad : Finset ℤ, bad ⊆ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(k : ℤ)) ∧
    ∃ epsilon defect : ℤ → ℝ,
      (∀ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(k : ℤ)), 0 ≤ epsilon j ∧ 0 ≤ defect j) ∧
      (∀ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(k : ℤ)), j ∉ bad →
        ∀ ell : Affine d, ell ∈ affineMinimizers (translatedCube d j x) U →
          excess (j - (h : ℤ)) (translatedCube d (j - (h : ℤ)) x) U ≤
            theta ^ h * excess j (translatedCube d j x) U +
              epsilon j * Real.sqrt (vecNormSq ell.slope) + defect j) ∧
      (bad.card : ℝ) ≤ (C2 + Csub) * (1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) ∧
      ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(k : ℤ)), epsilon j ≤
        (C2 + Csub) * (1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) ∧
      qside * ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(k : ℤ)), defect j ≤
        (C2 + Csub) * (3 : ℝ) ^ ((C2 + Csub) * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN) := by
  have hlamD : 0 ≤ lambdaDet := hlam0.trans hlamlt
  have ht0 : 0 ≤ lambdaDet + M.delta ^ 2 + eps ^ 8 := by positivity
  have hX0 : 0 ≤ ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ))) := by positivity
  have hsk0 : 0 < sk := by rw [hsk]; exact aux_in_deterministic_onestep_sref_pos M H omega N k qcenter
  have hW : 0 ≤ qside ^ 2 * sk⁻¹ * fN := by positivity
  have h1X : 0 ≤ 1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ))) := by linarith
  have hCs1 : 0 ≤ Csub * (1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) := mul_nonneg hCsub h1X
  have hup := fun (jlo : ℤ) (h1 : jlo ≤ -((k : ℤ) + (min D (N - k) : ℕ)) + 4)
      (h2 : -((k : ℤ) + (min D (N - k) : ℕ)) - 2 ≤ jlo) =>
    aux_in_deterministic_onestep_at_point_upper d I alpha s halpha hs h theta Ceps Cdel E0
      hCeps hCdel hOS Cg c0 C2 Csub hCg hc0 hC20 hC2a hC2b hC2c hC2d hCsub M H omega N eta hEta
      hIR eps heps Fsc Psc Rsc Dsc Zsc goodEvt hPS hG hcapE hdel0 hdel1 k cbuf k0 horizon hkN
      qside hqpos hqside qcenter lambdaCut lambdaDet hlam0 hlamlt hpreAll hfinAll Qcentre Qside
      hQside hqp f hf fL2 hfL2 u hu U hU huU sk fN hsk hfN hFq D hDh x hx jlo h1 h2
  rcases Nat.lt_or_ge (N + 1) (k + D) with hcase | hcase
  · -- below the wavelength: splice the upper range with the sub-cutoff obligation
    obtain ⟨badU, hbU, eU, dU, hnnU, hPU, hcU, hsU, htU⟩ :=
      hup (-(N : ℤ) - 3 + 1) (by omega) (by omega)
    obtain ⟨badL, hbL, eL, dL, hnnL, hPL, hcL, hsL, htL⟩ := hlow hcase
    have htL' : ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), dL j ≤
        Csub * (3 : ℝ) ^ (Csub * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN) / qside := by
      rw [le_div_iff₀ hqpos, mul_comm]; exact htL
    obtain ⟨bad, hbad, e, dl, hnn, hP, hc, hse, hsd⟩ :=
      aux_in_deterministic_onestep_splice (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3) (-(k : ℤ))
        (by omega) (by omega) (fun j e δ => ∀ ell : Affine d, ell ∈ affineMinimizers (translatedCube d j x) U →
          excess (j - (h : ℤ)) (translatedCube d (j - (h : ℤ)) x) U ≤
            theta ^ h * excess j (translatedCube d j x) U +
              e * Real.sqrt (vecNormSq ell.slope) + δ)
        _ _ _ _ _ _ ⟨badL, hbL, eL, dL, hnnL, hPL, hcL, hsL, htL'⟩
        ⟨badU, hbU, eU, dU, hnnU, hPU, hcU, hsU, htU⟩
    refine ⟨bad, hbad, e, dl, hnn, hP, ?_, ?_, ?_⟩
    · linarith only [hc]
    · linarith only [hse]
    · have hadd := aux_in_deterministic_onestep_budget_add C2 Csub ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))
        (qside ^ 2 * sk⁻¹ * fN) _ _ hC20 hCsub hX0 hW
        (le_refl (C2 * (3 : ℝ) ^ (C2 * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN)))
        (le_refl (Csub * (3 : ℝ) ^ (Csub * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN)))
      have hmul := mul_le_mul_of_nonneg_left hsd hqpos.le
      rw [mul_add, mul_div_cancel₀ _ hqpos.ne', mul_div_cancel₀ _ hqpos.ne'] at hmul
      linarith only [hmul, hadd]
  · -- at or above the wavelength: the upper range is the whole ray
    obtain ⟨bad, hbad, e, dl, hnn, hP, hc, hse, hsd⟩ :=
      hup (-((k : ℤ) + (D : ℤ))) (by omega) (by omega)
    refine ⟨bad, hbad, e, dl, hnn, hP, ?_, ?_, ?_⟩
    · linarith only [hc, hCs1]
    · linarith only [hse, hCs1]
    · have hsub0 : 0 ≤ Csub * (3 : ℝ) ^ (Csub * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN) := by
        positivity
      have hadd := aux_in_deterministic_onestep_budget_add C2 Csub ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))
        (qside ^ 2 * sk⁻¹ * fN) _ 0 hC20 hCsub hX0 hW
        (le_refl (C2 * (3 : ℝ) ^ (C2 * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN))) hsub0
      have hmul := mul_le_mul_of_nonneg_left hsd hqpos.le
      rw [mul_div_cancel₀ _ hqpos.ne'] at hmul
      linarith only [hmul, hadd]

end SubdiffusiveProcess.Paper
end
end DeterministicRegularity_OneStep_Bridge

section DeterministicRegularity_OneStep_Lip

/-!
# Cutoff-scale Lipschitz bound of the physical potential 

  At the physical cutoff `N` (GMC index `0`), the `Draw` score bounds the summed
gradients of all relabelled layers on the unit GMC cube around its centre (the fourth term of
`e.def.bfG.mhq`), including the infrared ones.  Consequently the physical potential
`cutoffPotential H omega N` is Lipschitz with constant `d · G0 · 3^N` along every segment on
which the gradient sums are bounded by `G0`; the infrared field `H` is handled through its
defining limit.
-/

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization.Book
open SubdiffusiveProcess
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

theorem aux_in_deterministic_onestep_shellGradient_continuous {d : ℕ}
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) :
    Continuous (fun Z : Vec d => Homogenization.euclideanNorm (shellGradient g Z)) := by
  have hc : ∀ i : Fin d, Continuous (fun Z : Vec d => shellGradient g Z i) := by
    intro i
    exact (_root_.SubdiffusiveProcess.Model.PotentialField.deriv g).continuous.clm_apply continuous_const
  unfold Homogenization.euclideanNorm Homogenization.vecNormSq
  refine Real.continuous_sqrt.comp ?_
  simp only [Homogenization.vecDot]
  exact continuous_finsetSum _ fun i _ => (hc i).mul (hc i)

theorem aux_in_deterministic_onestep_translatedCube_zero {d : ℕ} (z : Vec d) :
    translatedCube d 0 z = Metric.ball z (1 / 2) := by
  have h := aux_in_deterministic_regularity_translatedCube_eq_ball_local (d := d) 0 z
  simpa using h
where
  aux_in_deterministic_regularity_translatedCube_eq_ball_local {d : ℕ} (j : ℤ) (z : Vec d) :
      translatedCube d j z = Metric.ball z ((3 : ℝ) ^ j / 2) := by
    have h3 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      rw [Metric.mem_ball, dist_pi_lt_iff (by positivity)]
      intro i
      have hqi := hq i
      simp only [Homogenization.originCube, Homogenization.cubeScaleFactor, Pi.zero_apply,
        Int.cast_zero, zero_sub, zero_add] at hqi
      have hsimp : (fun x => z + x) q i - z i = q i := by simp
      rw [Real.dist_eq, hsimp, abs_lt]
      constructor <;> linarith [hqi.1, hqi.2]
    · intro hy
      refine ⟨y - z, ?_, by simp⟩
      rw [Metric.mem_ball, dist_pi_lt_iff (by positivity)] at hy
      intro i
      have hyi := hy i
      rw [Real.dist_eq, abs_lt] at hyi
      simp only [Homogenization.originCube, Homogenization.cubeScaleFactor, Pi.zero_apply,
        Int.cast_zero, zero_sub, zero_add, Pi.sub_apply]
      constructor <;> linarith [hyi.1, hyi.2]

theorem aux_in_deterministic_onestep_euclid_le_vsn {d : ℕ}
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) (z : Vec d) {Z : Vec d}
    (hZ : Z ∈ translatedCube d 0 z) :
    Homogenization.euclideanNorm (shellGradient g Z) ≤
      vectorSupNormOn (translatedCube d 0 z) (shellGradient g) := by
  unfold vectorSupNormOn
  refine le_csSup ?_ ⟨Z, hZ, rfl⟩
  obtain ⟨K, hK⟩ := (isCompact_closedBall z (1 / 2 : ℝ)).exists_bound_of_continuousOn
    (aux_in_deterministic_onestep_shellGradient_continuous g).continuousOn
  refine ⟨K, ?_⟩
  rintro a ⟨Y, hY, rfl⟩
  rw [aux_in_deterministic_onestep_translatedCube_zero] at hY
  have := hK Y (Metric.ball_subset_closedBall hY)
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this

/-- **Pointwise gradient sums at the cutoff cell** are bounded by the cutoff `Draw` score, on
the closed unit GMC cube around the cell centre. -/
theorem aux_in_deterministic_onestep_gradsum_le_draw {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s eps : ℝ)
    (g : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps g Fsc Psc Rsc Dsc Zsc goodEvt)
    (z : Vec d) (hD : Dsc 0 z ≠ ⊤) (J : ℕ) :
    ∀ Z ∈ Metric.closedBall z (1 / 2 : ℝ),
      ∑ i ∈ Finset.range J, Homogenization.euclideanNorm (shellGradient (g i) Z) ≤
        (Dsc 0 z).toReal := by
  have hT := aux_in_deterministic_good_scale_transfer_T_bound M s eps g Fsc Psc Rsc Dsc Zsc
    goodEvt hPS 0 z hD 0 J le_rfl
  simp only [pow_zero, one_mul] at hT
  have hopen : ∀ Z ∈ Metric.ball z (1 / 2 : ℝ),
      ∑ i ∈ Finset.range J, Homogenization.euclideanNorm (shellGradient (g i) Z) ≤
        (Dsc 0 z).toReal := by
    intro Z hZ
    have hZ' : Z ∈ translatedCube d 0 z := by
      rw [aux_in_deterministic_onestep_translatedCube_zero]; exact hZ
    rw [Finset.range_eq_Ico]
    exact (Finset.sum_le_sum fun i _ => aux_in_deterministic_onestep_euclid_le_vsn (g i) z hZ').trans
      hT
  have hcont : Continuous (fun Z : Vec d =>
      ∑ i ∈ Finset.range J, Homogenization.euclideanNorm (shellGradient (g i) Z)) :=
    continuous_finsetSum _ fun i _ => aux_in_deterministic_onestep_shellGradient_continuous (g i)
  have hclosed : IsClosed {Z : Vec d |
      ∑ i ∈ Finset.range J, Homogenization.euclideanNorm (shellGradient (g i) Z) ≤
        (Dsc 0 z).toReal} := isClosed_le hcont continuous_const
  have hsub : closure (Metric.ball z (1 / 2 : ℝ)) ⊆ {Z : Vec d |
      ∑ i ∈ Finset.range J, Homogenization.euclideanNorm (shellGradient (g i) Z) ≤
        (Dsc 0 z).toReal} := closure_minimal hopen hclosed
  intro Z hZ
  rw [closure_ball z (by norm_num : (1 / 2 : ℝ) ≠ 0)] at hsub
  exact hsub hZ

/-- **Lipschitz bound of the physical potential along a segment.** -/
theorem aux_in_deterministic_onestep_potential_lip {d : ℕ}
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)))
    (G0 : ℝ) (x y : SpatialCoordinates d)
    (hgrad : ∀ Z ∈ segment ℝ (((3 : ℝ) ^ N) • x) (((3 : ℝ) ^ N) • y), ∀ J : ℕ,
      ∑ i ∈ Finset.range J, Homogenization.euclideanNorm (shellGradient (eta i) Z) ≤ G0) :
    |cutoffPotential H omega N y - cutoffPotential H omega N x| ≤
      (d : ℝ) * G0 * ((3 : ℝ) ^ N * ‖y - x‖) := by
  set X : Vec d := ((3 : ℝ) ^ N) • x with hX
  set Y : Vec d := ((3 : ℝ) ^ N) • y with hY
  have hunscale : ∀ v : SpatialCoordinates d,
      ((3 : ℝ) ^ (-(N : ℤ))) • (((3 : ℝ) ^ N) • v) = v := by
    intro v
    rw [smul_smul, zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity), one_smul]
  have hG0 : 0 ≤ G0 := by
    have := hgrad X (left_mem_segment ℝ X Y) 0
    simpa using this
  -- the mean-value bound for every finite partial sum
  have hmv : ∀ J : ℕ, |∑ i ∈ Finset.range J, (eta i Y - eta i X)| ≤
      (d : ℝ) * G0 * ‖Y - X‖ := by
    intro J
    let SJ : Vec d → ℝ := fun Z => ∑ i ∈ Finset.range J, eta i Z
    let DJ : Vec d → (Vec d →L[ℝ] ℝ) := fun Z =>
      ∑ i ∈ Finset.range J, _root_.SubdiffusiveProcess.Model.PotentialField.deriv (eta i) Z
    have hder : ∀ Z, HasFDerivAt SJ (DJ Z) Z := by
      intro Z
      have := HasFDerivAt.sum (u := Finset.range J) (fun i _ => (eta i).hasFDerivAt Z)
      convert this using 1
      funext Z'
      simp only [SJ, Finset.sum_apply]
    have hbd : ∀ Z ∈ segment ℝ X Y, ‖fderiv ℝ SJ Z‖ ≤ (d : ℝ) * G0 := by
      intro Z hZ
      rw [(hder Z).fderiv]
      calc ‖DJ Z‖ ≤ ∑ i ∈ Finset.range J,
            ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv (eta i) Z‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.range J,
            (d : ℝ) * Homogenization.euclideanNorm (shellGradient (eta i) Z) :=
          Finset.sum_le_sum fun i _ =>
            SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.potentialDeriv_norm_le_dimension_mul_shellGradient
              (eta i) Z
        _ = (d : ℝ) * ∑ i ∈ Finset.range J,
            Homogenization.euclideanNorm (shellGradient (eta i) Z) := by rw [Finset.mul_sum]
        _ ≤ (d : ℝ) * G0 := mul_le_mul_of_nonneg_left (hgrad Z hZ J) (Nat.cast_nonneg d)
    have hmean := (convex_segment X Y).norm_image_sub_le_of_norm_fderiv_le
      (fun Z _ => (hder Z).differentiableAt) hbd (left_mem_segment ℝ X Y)
      (right_mem_segment ℝ X Y)
    rw [Real.norm_eq_abs] at hmean
    have hsum : SJ Y - SJ X = ∑ i ∈ Finset.range J, (eta i Y - eta i X) := by
      simp only [SJ, Finset.sum_sub_distrib]
    rw [← hsum]
    exact hmean
  have hYX : ‖Y - X‖ = (3 : ℝ) ^ N * ‖y - x‖ := by
    rw [hY, hX, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  -- identification of the partial sums with the physical layers
  have hlay : ∀ K : ℕ, ∑ i ∈ Finset.range (N + K + 1), (eta i Y - eta i X) =
      ∑ j ∈ Finset.range (N + 1), (omega (-(j : ℤ)) y - omega (-(j : ℤ)) x) +
        ∑ n ∈ Finset.range K, (omega (((n + 1 : ℕ) : ℤ)) y - omega (((n + 1 : ℕ) : ℤ)) x) := by
    intro K
    have h := aux_in_deterministic_good_scale_transfer_uv_ir_sum
      (fun i : ℤ => omega i y - omega i x) N K
    rw [← h]
    apply Finset.sum_congr rfl
    intro i _
    rw [hY, hX, hEta, hEta, hunscale, hunscale]
  have hpot : cutoffPotential H omega N y - cutoffPotential H omega N x =
      (H omega y - H omega x) +
        ∑ j ∈ Finset.range (N + 1), (omega (-(j : ℤ)) y - omega (-(j : ℤ)) x) := by
    unfold cutoffPotential
    rw [Finset.sum_sub_distrib]
    simp only [Int.ofNat_eq_natCast]
    ring
  set Xv : ℝ := cutoffPotential H omega N y - cutoffPotential H omega N x with hXv
  let T : ℕ → ℝ := fun K => ∑ i ∈ Finset.range (N + K + 1), (eta i Y - eta i X)
  let b : ℕ → ℝ := fun K => (H omega y - H omega x) -
    ∑ n ∈ Finset.range K, (omega (((n + 1 : ℕ) : ℤ)) y - omega (((n + 1 : ℕ) : ℤ)) x)
  have hXK : ∀ K, 0 ≤ K → Xv = T K + b K := by
    intro K _
    simp only [T, b]
    rw [hlay K, hpot]
    ring
  have hb := aux_in_deterministic_good_scale_transfer_ir_remainder H omega hIR y x
  have hS : ∀ K, 0 ≤ K → |T K| ≤ (d : ℝ) * G0 * ((3 : ℝ) ^ N * ‖y - x‖) := by
    intro K _
    rw [← hYX]
    exact hmv (N + K + 1)
  exact aux_in_deterministic_good_scale_transfer_limit_bound Xv _ T b 0 hXK hb hS

end SubdiffusiveProcess.Paper
end
end DeterministicRegularity_OneStep_Lip

section DeterministicRegularity_OneStep_NearConst

/-!
# The in_J error of a nearly constant physical coefficient 

  If the physical coefficient on the chart `w + r·(unit root)` deviates from the
scalar `a0` by at most `η` in both ratio directions, then `I.err ≤ √(2 η²)`.  The proof is the
probe bound `responseJ_le_scalar_ratio_energy` (GMC `CrudeJDeterministic`) on every
descendant, fed to `error_affine` of `in_deterministic_good_scale_transfer` with `c = 0`.
-/

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization.Book
open SubdiffusiveProcess
open MeasureTheory
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- A function bounded by `c` on a domain has average at most `c`. -/
theorem aux_in_deterministic_onestep_average_le {d : ℕ} (R : Homogenization.TriadicCube d)
    (f : Homogenization.Vec d → ℝ) (c : ℝ)
    (hint : IntegrableOn f (Homogenization.openCubeSet R))
    (hf : ∀ x ∈ Homogenization.openCubeSet R, f x ≤ c) :
    Ch02.average (Ch02.cubeDomain R) f ≤ c := by
  unfold Ch02.average
  have hmeas : MeasurableSet (Homogenization.openCubeSet R) :=
    Homogenization.measurableSet_openCubeSet R
  have hV : 0 < (volume (Homogenization.openCubeSet R)).toReal := by
    rw [Homogenization.volume_openCubeSet_toReal]; exact Homogenization.cubeVolume_pos R
  have hVfin : volume (Homogenization.openCubeSet R) < ⊤ :=
    Homogenization.volume_openCubeSet_lt_top R
  change (volume (Homogenization.openCubeSet R)).toReal⁻¹ *
      ∫ x in Homogenization.openCubeSet R, f x ≤ c
  have hmono : ∫ x in Homogenization.openCubeSet R, f x ≤
      ∫ _x in Homogenization.openCubeSet R, c :=
    setIntegral_mono_on hint (integrableOn_const hVfin.ne) hmeas hf
  rw [setIntegral_const, smul_eq_mul, measureReal_def] at hmono
  calc (volume (Homogenization.openCubeSet R)).toReal⁻¹ *
        ∫ x in Homogenization.openCubeSet R, f x
      ≤ (volume (Homogenization.openCubeSet R)).toReal⁻¹ *
          ((volume (Homogenization.openCubeSet R)).toReal * c) :=
        mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr hV.le)
    _ = c := by field_simp

/-- **Nearly constant coefficient ⇒ small in_J error.** -/
theorem aux_in_deterministic_onestep_err_nearconst {d : ℕ} [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (a0 : ℝ) (ha0 : 0 < a0)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (eta : ℝ) (_heta : 0 ≤ eta)
    (hratio : ∀ x ∈ Homogenization.openCubeSet (Homogenization.originCube d 0),
      |cutoffCoefficient M H omega N (fun i => w i + r * x i) / a0 - 1| ≤ eta ∧
      |a0 / cutoffCoefficient M H omega N (fun i => w i + r * x i) - 1| ≤ eta) :
    I.err w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r a0 s 2 ≤
      Real.sqrt (2 * eta ^ 2) := by
  set phys : Vec d → ℝ := fun x => cutoffCoefficient M H omega N (fun i => w i + r * x i)
    with hphys
  have hphys_cont : Continuous phys := by
    refine (aux_in_deterministic_good_scale_transfer_continuous_cutoffCoefficient
      M H omega N).comp ?_
    exact continuous_pi fun i => continuous_const.add
      (continuous_const.mul (continuous_apply i))
  have hphys_pos : ∀ x, 0 < phys x := fun x =>
    aux_in_deterministic_good_scale_transfer_cutoffCoefficient_pos M H omega N _
  have hsub : (centeredCube w r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube w r hr : Set (SpatialCoordinates d)) := subset_rfl
  have hq : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h2top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  set acoef := _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr with hacoef
  set chart := I.chart w r hr acoef w r with hchart
  set Q0 := Homogenization.originCube d 0 with hQ0
  have herr := I.err_eq w r hr acoef w r hr hsub s hs 2 hq a0 ha0
  simp only [ite_eq_right h2top] at herr
  have htwo : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [htwo] at herr
  change I.err w r hr acoef w r a0 s 2 =
    (paperHomogenizationError Q0 0 s .infinity (.finite 2) chart a0).toReal at herr
  -- per-descendant probe bound
  have hprobe : ∀ (l : ℕ) (R : Homogenization.TriadicCube d),
      R ∈ Homogenization.descendantsAtScale Q0 (0 - (l : ℤ)) →
      ∀ e : Vec d, Homogenization.vecNormSq e = 1 →
        paperScalarProbe R chart a0 e ≤ 0 * paperScalarProbe R chart a0 e + 2 * eta ^ 2 := by
    intro l R hR e he
    have hk : (0 : ℤ) - (l : ℤ) ≤ Q0.scale := by
      simp [hQ0, Homogenization.originCube]
    have hRsub : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet Q0 :=
      Homogenization.openCubeSet_subset_of_mem_descendantsAtScale hk hR
    set hP := SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.scalarCoeffOnDataOfContinuousPos
      hphys_cont hphys_pos (Ch02.cubeDomain R) with hPdef
    have hPe := aux_in_deterministic_good_scale_transfer_phys_aeeq I M H omega N w r hr R hRsub hP
    have hbound : ∀ x ∈ Homogenization.openCubeSet R,
        (phys x / a0 - 1) ^ 2 + (a0 / phys x - 1) ^ 2 ≤ 2 * eta ^ 2 := by
      intro x hx
      obtain ⟨h1, h2⟩ := hratio x (hRsub hx)
      have e1 : (phys x / a0 - 1) ^ 2 ≤ eta ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      have e2 : (a0 / phys x - 1) ^ 2 ≤ eta ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
      linarith
    have hcont2 : Continuous (fun x => (phys x / a0 - 1) ^ 2 + (a0 / phys x - 1) ^ 2) := by
      have h1 : Continuous (fun x => phys x / a0) := hphys_cont.div_const a0
      have h2 : Continuous (fun x => a0 / phys x) :=
        continuous_const.div hphys_cont (fun x => (hphys_pos x).ne')
      exact ((h1.sub continuous_const).pow 2).add ((h2.sub continuous_const).pow 2)
    have hint : IntegrableOn (fun x => (phys x / a0 - 1) ^ 2 + (a0 / phys x - 1) ^ 2)
        (Homogenization.openCubeSet R) := by
      obtain ⟨ρ, _hρ, hρ⟩ :=
        (Homogenization.isOpenBoundedConvexDomain_openCubeSet R).isBoundedDomain
      have hball : Homogenization.openCubeSet R ⊆ Metric.closedBall (0 : Vec d) ρ := by
        intro x hx
        rw [Metric.mem_closedBall, dist_zero_right,
          pi_norm_le_iff_of_nonneg (by linarith [hρ])]
        intro i
        rw [Real.norm_eq_abs]
        exact hρ x hx i
      exact (hcont2.continuousOn.integrableOn_compact (isCompact_closedBall 0 ρ)).mono_set hball
    have hJ := responseJ_le_scalar_ratio_energy (Ch02.cubeDomain R) hP ha0 hphys_pos hint e he
    have havg := aux_in_deterministic_onestep_average_le R _ (2 * eta ^ 2) hint hbound
    unfold paperScalarProbe J
    rw [Ch02.responseJ_eq_ofAEEq hPe, zero_mul, zero_add]
    exact hJ.trans havg
  have hE := aux_in_deterministic_good_scale_transfer_error_affine Q0 0 hs.1
    chart chart a0 a0 0 (2 * eta ^ 2) le_rfl (by positivity) hprobe
  rw [Real.sqrt_zero, ENNReal.ofReal_zero, zero_mul, zero_add] at hE
  rw [herr]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hE
  rwa [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at this

end SubdiffusiveProcess.Paper
end
end DeterministicRegularity_OneStep_NearConst

section DeterministicRegularity_OneStep_SubRatio

/-!
# Sub-cutoff coefficient control from the cutoff-level score 



* `…_layer0_le_draw`: the finest relabelled layer is bounded by `Draw` at GMC index `0`.
* `…_sref_N_le_coeff`: the level-`N` reference at `w'` is at most the actual coefficient at `x`
  times `exp(|Ψ(x) - Ψ(w')| + |ω_{-N}(w')| + δ²)`.
* `…_sub_osc`: on a sub-cutoff working cube around `x ∈ q`, the physical potential oscillates by
  at most `d · G0 · 3^N · r / 2`, where `G0` bounds the cutoff `Draw` of every padded-root
  cutoff cell.
* `…_sub_ratio`: `A_N(x)⁻¹ ≤ exp(Y) · sN_k(qcenter)⁻¹` from the self-root cutoff-depth prefix.
-/

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization.Book
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- The finest layer is bounded by `Draw` at GMC index `0`. -/
theorem aux_in_deterministic_onestep_layer0_le_draw {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s eps : ℝ)
    (g : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps g Fsc Psc Rsc Dsc Zsc goodEvt)
    (z : Vec d) (hD : Dsc 0 z ≠ ⊤) :
    |g 0 z| ≤ (Dsc 0 z).toReal := by
  obtain ⟨_, _, _, _, _, _, _, hDdef, _, _, _⟩ := hPS
  have hDeq := hDdef 0 z
  have hmem : z ∈ translatedCube d ((0 : ℕ) : ℤ) z :=
    ⟨0, aux_in_deterministic_good_scale_transfer_zero_mem_cube 0, by simp⟩
  have hB : ENNReal.ofReal |g 0 z| ≤ Dsc 0 z := by
    rw [hDeq]
    refine le_trans ?_ le_self_add
    refine le_trans ?_ le_add_self
    simp only [CharP.cast_eq_zero, mul_zero, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
    exact le_sSup ⟨z, hmem, rfl⟩
  have := ENNReal.toReal_mono hD hB
  rwa [ENNReal.toReal_ofReal (abs_nonneg _)] at this

theorem aux_in_deterministic_onestep_sum_Ico_int (f : ℤ → ℝ) (N : ℕ) :
    ∑ j ∈ Finset.Ico (0 : ℤ) N, f j = ∑ n ∈ Finset.range N, f n := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hsplit : Finset.Ico (0 : ℤ) ((n + 1 : ℕ) : ℤ) = Finset.Ico (0 : ℤ) n ∪ {(n : ℤ)} := by
      ext j; simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_singleton]; push_cast; omega
    have hdisj : Disjoint (Finset.Ico (0 : ℤ) n) {(n : ℤ)} := by
      rw [Finset.disjoint_singleton_right, Finset.mem_Ico]; omega
    rw [hsplit, Finset.sum_union hdisj, Finset.sum_singleton, ih, Finset.sum_range_succ]

/-- **The level-`N` reference versus the actual coefficient.** -/
theorem aux_in_deterministic_onestep_sref_N_le_coeff {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (x w' : SpatialCoordinates d) :
    aux_in_deterministic_onestep_sref M H omega N N w' ≤
      cutoffCoefficient M H omega N x *
        Real.exp (|cutoffPotential H omega N x - cutoffPotential H omega N w'| +
          |omega (-(N : ℤ)) w'| + M.delta ^ 2) := by
  set τ := _root_.SubdiffusiveProcess.Model.tauSq M.P with hτ
  have htau : τ ≤ M.delta ^ 2 := by
    have ht := SubdiffusiveProcess.CoarseGrainingVocab.tauSq_le_delta_sq M
    have hl2 : Real.log 2 / 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    nlinarith [sq_nonneg M.delta]
  have hpotw : cutoffPotential H omega N w' =
      H omega w' + ∑ j ∈ Finset.Ico (0 : ℤ) N, omega (-j) w' + omega (-(N : ℤ)) w' := by
    unfold cutoffPotential
    rw [aux_in_deterministic_onestep_sum_Ico_int (fun j => omega (-j) w') N,
      Finset.sum_range_succ]
    simp only [Int.ofNat_eq_natCast]
    ring
  unfold aux_in_deterministic_onestep_sref cutoffCoefficient
  simp only
  rw [ite_eq_left (Nat.cast_nonneg N), show ((N : ℤ) - (N : ℤ)).toNat = 0 by simp]
  have hA0 : 0 < ahom M 0 := ahom_pos M 0
  have hA0le : ahom M 0 ≤ 1 := SubdiffusiveProcess.CoarseGrainingVocab.ahom_le_one M 0
  have hAN : 0 < ahom M N := ahom_pos M N
  set Ψx := cutoffPotential H omega N x
  set Ψw := cutoffPotential H omega N w'
  set S := ∑ j ∈ Finset.Ico (0 : ℤ) N, omega (-j) w'
  set o := omega (-(N : ℤ)) w'
  have hS : H omega w' + S = Ψw - o := by rw [hpotw]; ring
  rw [hS]
  push_cast
  -- LHS = e^{τ} a0 / (e^{(N+1)τ} aN) · e^{Ψw - o};  RHS = aN⁻¹ e^{Ψx - (N+1)τ} e^{...}
  have hkey : Real.exp (((0 : ℝ) + 1) * τ) * ahom M 0 /
        (Real.exp (((N : ℝ) + 1) * τ) * ahom M N) * Real.exp (Ψw - o) =
      (ahom M N)⁻¹ * Real.exp (Ψx - ((N : ℝ) + 1) * τ) *
        (ahom M 0 * Real.exp (Ψw - Ψx - o + τ)) := by
    rw [show Ψw - o = (Ψw - Ψx - o + τ) + (Ψx - ((N : ℝ) + 1) * τ) + (((N : ℝ) + 1) * τ - τ)
      by ring]
    rw [Real.exp_add, Real.exp_add, Real.exp_sub (((N : ℝ) + 1) * τ)]
    field_simp
    ring
  rw [hkey]
  have hpos : 0 < (ahom M N)⁻¹ * Real.exp (Ψx - ((N : ℝ) + 1) * τ) := by positivity
  apply mul_le_mul_of_nonneg_left _ hpos.le
  calc ahom M 0 * Real.exp (Ψw - Ψx - o + τ) ≤ 1 * Real.exp (Ψw - Ψx - o + τ) :=
        mul_le_mul_of_nonneg_right hA0le (Real.exp_pos _).le
    _ = Real.exp (Ψw - Ψx - o + τ) := one_mul _
    _ ≤ Real.exp (|Ψx - Ψw| + |o| + M.delta ^ 2) := by
        apply Real.exp_le_exp.mpr
        have h1 : Ψw - Ψx ≤ |Ψx - Ψw| := by rw [abs_sub_comm]; exact le_abs_self _
        have h2 : -o ≤ |o| := neg_le_abs o
        linarith

/-- The side of the depth-`(N-k+1)` padded-root cell, and of the depth-`(N-k)` self-root cell,
is the physical wavelength `3^{-N}`. -/
theorem aux_in_deterministic_onestep_side_pad (k N : ℕ) (hkN : k ≤ N) (qside : ℝ)
    (hqside : qside = (3 : ℝ) ^ (-(k : ℤ))) :
    descendantSide 1 (N - k + 1) (3 * qside) = ((3 : ℝ) ^ N)⁻¹ ∧
      descendantSide 1 (N - k) qside = ((3 : ℝ) ^ N)⁻¹ := by
  rw [aux_in_deterministic_onestep_descendantSide_one,
    aux_in_deterministic_onestep_descendantSide_one, hqside, zpow_neg, zpow_natCast]
  have h1 : (3 : ℝ) ^ (N - k + 1) * (3 : ℝ) ^ k = 3 * (3 : ℝ) ^ N := by
    rw [← pow_add, show N - k + 1 + k = N + 1 by omega, pow_succ]; ring
  have h2 : (3 : ℝ) ^ (N - k) * (3 : ℝ) ^ k = (3 : ℝ) ^ N := by
    rw [← pow_add, show N - k + k = N by omega]
  have hk : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  have hN : (0 : ℝ) < (3 : ℝ) ^ N := by positivity
  constructor
  · field_simp
    linarith [h1]
  · field_simp
    linarith [h2]

/-- **Sub-cutoff oscillation of the physical potential**, from the padded-root cutoff cells. -/
theorem aux_in_deterministic_onestep_sub_osc {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)))
    (s eps : ℝ)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (k : ℕ) (hkN : k ≤ N) (qside : ℝ) (hqpos : 0 < qside)
    (hqside : qside = (3 : ℝ) ^ (-(k : ℤ))) (qcenter : SpatialCoordinates d) (G0 : ℝ)
    (hpad : ∀ pword : Fin (N - k + 1) → OddGridIndex d 1,
      Dsc 0 (((3 : ℝ) ^ N) • descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword) ≠ ⊤ ∧
      (Dsc 0 (((3 : ℝ) ^ N) •
        descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword)).toReal ≤ G0)
    (x y : SpatialCoordinates d) (hx : ∀ i, |x i - qcenter i| ≤ qside)
    (hy : ∀ i, |y i - qcenter i| ≤ qside) :
    |cutoffPotential H omega N y - cutoffPotential H omega N x| ≤
      (d : ℝ) * G0 * ((3 : ℝ) ^ N * ‖y - x‖) := by
  refine aux_in_deterministic_onestep_potential_lip H omega N eta hEta hIR G0 x y ?_
  intro Z hZ J
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hZ
  set z' : SpatialCoordinates d := a • x + b • y with hz'
  have hZz : a • (((3 : ℝ) ^ N) • x) + b • (((3 : ℝ) ^ N) • y) = ((3 : ℝ) ^ N) • z' := by
    rw [hz', smul_add, smul_comm a, smul_comm b]
  rw [hZz]
  have hz'q : ∀ i, |z' i - qcenter i| ≤ 3 * qside / 2 := by
    intro i
    have hzi : z' i - qcenter i = a * (x i - qcenter i) + b * (y i - qcenter i) := by
      simp only [hz', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have : qcenter i = a * qcenter i + b * qcenter i := by rw [← add_mul, hab, one_mul]
      linarith
    rw [hzi]
    calc |a * (x i - qcenter i) + b * (y i - qcenter i)|
        ≤ |a * (x i - qcenter i)| + |b * (y i - qcenter i)| := abs_add_le _ _
      _ = a * |x i - qcenter i| + b * |y i - qcenter i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * qside + b * qside :=
          add_le_add (mul_le_mul_of_nonneg_left (hx i) ha) (mul_le_mul_of_nonneg_left (hy i) hb)
      _ = qside := by rw [← add_mul, hab, one_mul]
      _ ≤ 3 * qside / 2 := by linarith
  obtain ⟨pword, hpw⟩ := aux_in_deterministic_onestep_descendant_exists qcenter (3 * qside)
    (by positivity) z' hz'q (N - k + 1)
  have hside := (aux_in_deterministic_onestep_side_pad k N hkN qside hqside).1
  set c := descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword with hc
  have hmem : ((3 : ℝ) ^ N) • z' ∈ Metric.closedBall (((3 : ℝ) ^ N) • c) (1 / 2 : ℝ) := by
    rw [Metric.mem_closedBall, dist_pi_le_iff (by norm_num)]
    intro i
    rw [Real.dist_eq]
    have h1 := (hpw i).1
    rw [hside] at h1
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity)]
    have hN : (0 : ℝ) < (3 : ℝ) ^ N := by positivity
    calc (3 : ℝ) ^ N * |z' i - c i| ≤ (3 : ℝ) ^ N * (((3 : ℝ) ^ N)⁻¹ / 2) :=
          mul_le_mul_of_nonneg_left h1 hN.le
      _ = 1 / 2 := by field_simp
  obtain ⟨hfin, hle⟩ := hpad pword
  exact (aux_in_deterministic_onestep_gradsum_le_draw M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt hPS
    _ hfin J _ hmem).trans hle

/-- **Sub-cutoff reference comparison**: the actual coefficient at `x ∈ q` is comparable to the
coarse reference through the self-root prefix of depth `N - k`. -/
theorem aux_in_deterministic_onestep_sub_ratio {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)))
    (s eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (k cbuf : ℕ) (hkN : k ≤ N) (qside : ℝ) (hqpos : 0 < qside)
    (hqside : qside = (3 : ℝ) ^ (-(k : ℤ))) (qcenter : SpatialCoordinates d)
    (x : SpatialCoordinates d) (hx : x ∈ Metric.ball qcenter (qside / 2))
    (Sig : ℝ)
    (hself : ∀ dword : Fin (N - k) → OddGridIndex d 1,
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + (N - k : ℕ)),
          (Dsc ((N : ℤ) - l).toNat
            (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside (N - k) dword)).toReal ≤ Sig ∧
      ∀ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + (N - k : ℕ)),
        Dsc ((N : ℤ) - l).toNat
          (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside (N - k) dword) ≠ ⊤) :
    (cutoffCoefficient M H omega N x)⁻¹ ≤
      Real.exp (((d : ℝ) + 2) * Sig + ((N - k : ℕ) : ℝ) * M.delta ^ 2 + (d : ℝ) * Sig + Sig +
        M.delta ^ 2) *
        (aux_in_deterministic_onestep_sref M H omega N k qcenter)⁻¹ := by
  have hxq : ∀ i, |x i - qcenter i| < qside / 2 := by
    intro i
    have hx' : dist x qcenter < qside / 2 := hx
    rw [dist_pi_lt_iff (by positivity)] at hx'
    have := hx' i
    rwa [Real.dist_eq] at this
  obtain ⟨dword, hdw⟩ := aux_in_deterministic_onestep_descendant_exists qcenter qside hqpos x
    (fun i => (hxq i).le) (N - k)
  set w' := descendantCenter 1 qcenter qside (N - k) dword with hw'
  have hside := (aux_in_deterministic_onestep_side_pad k N hkN qside hqside).2
  obtain ⟨hSig, hfin⟩ := hself dword
  have hkNz : (k : ℤ) + ((N - k : ℕ) : ℤ) = (N : ℤ) := by push_cast [Nat.cast_sub hkN]; ring
  have hNmem : (N : ℤ) ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + (N - k : ℕ)) := by
    rw [Finset.mem_Icc, hkNz]; constructor <;> omega
  have hD0 : ∀ l, 0 ≤ (Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w')).toReal :=
    fun _ => ENNReal.toReal_nonneg
  have hDN : (Dsc 0 (((3 : ℝ) ^ N) • w')).toReal ≤ Sig := by
    have h := Finset.single_le_sum (fun l _ => hD0 l) hNmem
    simp only [sub_self, Int.toNat_zero] at h
    exact h.trans hSig
  have hfinN : Dsc 0 (((3 : ℝ) ^ N) • w') ≠ ⊤ := by
    have := hfin _ hNmem
    simpa using this
  have hwq : ∀ i, |w' i - qcenter i| < (3 : ℝ) ^ (-(k : ℤ)) / 2 := by
    intro i
    have h1 := (hdw i).2
    have h2 := descendantSide_pos 1 (N - k) hqpos
    rw [← hqside]; linarith
  -- (a) the ray comparison down to level `N`
  have hray := aux_in_deterministic_onestep_ratio_ray M H omega N eta hEta hIR s eps hs
    Fsc Psc Rsc Dsc Zsc goodEvt hPS k qcenter w' hwq
    (Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + (N - k : ℕ)))
    (by rw [Finset.mem_Icc, hkNz]; constructor <;> omega) (N : ℤ) (by exact_mod_cast hkN) le_rfl
    (by intro i hi; rw [Finset.mem_Ico] at hi; rw [Finset.mem_Icc, hkNz]; constructor <;> omega)
    hfin Sig hSig
  have hcast : (((N : ℤ) - (k : ℤ) : ℤ) : ℝ) = ((N - k : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hkN]; ring
  rw [hcast] at hray
  -- (b) the level-`N` reference versus the coefficient at `x`
  have hcoef := aux_in_deterministic_onestep_sref_N_le_coeff M H omega N x w'
  -- (c) the potential oscillation inside the self cell
  have hosc : |cutoffPotential H omega N x - cutoffPotential H omega N w'| ≤ (d : ℝ) * Sig := by
    have hlip := aux_in_deterministic_onestep_potential_lip H omega N eta hEta hIR
      (Dsc 0 (((3 : ℝ) ^ N) • w')).toReal w' x (by
        intro Z hZ J
        refine aux_in_deterministic_onestep_gradsum_le_draw M s eps eta Fsc Psc Rsc Dsc Zsc
          goodEvt hPS _ hfinN J Z ?_
        have hconv := convex_closedBall (((3 : ℝ) ^ N) • w') (1 / 2 : ℝ)
        refine hconv.segment_subset (Metric.mem_closedBall_self (by norm_num)) ?_ hZ
        rw [Metric.mem_closedBall, dist_pi_le_iff (by norm_num)]
        intro i
        rw [Real.dist_eq]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [← mul_sub, abs_mul, abs_of_pos (by positivity)]
        have h1 := (hdw i).1
        rw [hside] at h1
        have hN : (0 : ℝ) < (3 : ℝ) ^ N := by positivity
        calc (3 : ℝ) ^ N * |x i - w' i| ≤ (3 : ℝ) ^ N * (((3 : ℝ) ^ N)⁻¹ / 2) :=
              mul_le_mul_of_nonneg_left h1 hN.le
          _ = 1 / 2 := by field_simp)
    have hnorm : (3 : ℝ) ^ N * ‖x - w'‖ ≤ 1 := by
      have : ‖x - w'‖ ≤ ((3 : ℝ) ^ N)⁻¹ / 2 := by
        rw [pi_norm_le_iff_of_nonneg (by positivity)]
        intro i
        rw [Pi.sub_apply, Real.norm_eq_abs, ← hside]
        exact (hdw i).1
      have hN : (0 : ℝ) < (3 : ℝ) ^ N := by positivity
      calc (3 : ℝ) ^ N * ‖x - w'‖ ≤ (3 : ℝ) ^ N * (((3 : ℝ) ^ N)⁻¹ / 2) :=
            mul_le_mul_of_nonneg_left this hN.le
        _ ≤ 1 := by field_simp; norm_num
    calc |cutoffPotential H omega N x - cutoffPotential H omega N w'|
        ≤ (d : ℝ) * (Dsc 0 (((3 : ℝ) ^ N) • w')).toReal * ((3 : ℝ) ^ N * ‖x - w'‖) := hlip
      _ ≤ (d : ℝ) * Sig * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hDN (Nat.cast_nonneg d)) hnorm
            (by positivity) (mul_nonneg (Nat.cast_nonneg d) (ENNReal.toReal_nonneg.trans hDN))
      _ = (d : ℝ) * Sig := mul_one _
  -- (d) the finest layer at `w'`
  have hlay : |omega (-(N : ℤ)) w'| ≤ Sig := by
    have h := aux_in_deterministic_onestep_layer0_le_draw M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt
      hPS _ hfinN
    rw [hEta] at h
    have : (((0 : ℕ) : ℤ) - (N : ℤ)) = -(N : ℤ) := by simp
    rw [this, smul_smul, zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity), one_smul] at h
    exact h.trans hDN
  -- assemble
  have hcoef0 := aux_in_deterministic_good_scale_transfer_cutoffCoefficient_pos M H omega N x
  have hsk0 := aux_in_deterministic_onestep_sref_pos M H omega N k qcenter
  set Y : ℝ := ((d : ℝ) + 2) * Sig + ((N - k : ℕ) : ℝ) * M.delta ^ 2 + (d : ℝ) * Sig + Sig +
    M.delta ^ 2 with hY
  have hsk : aux_in_deterministic_onestep_sref M H omega N k qcenter ≤
      cutoffCoefficient M H omega N x * Real.exp Y := by
    have hN0 := aux_in_deterministic_onestep_sref_pos M H omega N N w'
    have e1 := hray.trans (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le)
    refine e1.trans ?_
    rw [mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hcoef0.le
    apply Real.exp_le_exp.mpr
    rw [hY]
    linarith [hosc, hlay]
  have hq : aux_in_deterministic_onestep_sref M H omega N k qcenter *
      (cutoffCoefficient M H omega N x)⁻¹ ≤ Real.exp Y := by
    rw [← div_eq_mul_inv, div_le_iff₀ hcoef0]; linarith [hsk]
  calc (cutoffCoefficient M H omega N x)⁻¹
      = (aux_in_deterministic_onestep_sref M H omega N k qcenter)⁻¹ *
          (aux_in_deterministic_onestep_sref M H omega N k qcenter *
            (cutoffCoefficient M H omega N x)⁻¹) := by field_simp
    _ ≤ (aux_in_deterministic_onestep_sref M H omega N k qcenter)⁻¹ * Real.exp Y :=
        mul_le_mul_of_nonneg_left hq (inv_nonneg.mpr hsk0.le)
    _ = Real.exp Y * (aux_in_deterministic_onestep_sref M H omega N k qcenter)⁻¹ := mul_comm _ _

end SubdiffusiveProcess.Paper
end
end DeterministicRegularity_OneStep_SubRatio

section DeterministicRegularity_OneStep_SubCore

/-!
# Sub-cutoff bookkeeping 

  Windows `j ∈ [lo, -N-3]` strictly below the physical wavelength.  The window's
coefficient oscillation is `θ_j = A · 3^{N+j}` (geometric in the depth below the cutoff); the
window is good when `j ≤ -k-4` and `θ_j ≤ c1`.  The count of bad windows is at most
`A/c1 + 2`, and the error sum at most `Ceps · Cerr · A`.
-/

open Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Geometric bound for `Σ 3^{c+j}` over an integer interval ending at `b`. -/
theorem aux_in_deterministic_onestep_geom_zpow_le (a b c : ℤ) :
    ∑ j ∈ Icc a b, (3 : ℝ) ^ (c + j) ≤ (3 : ℝ) ^ (c + b) * (3 / 2) := by
  have h := aux_in_deterministic_onestep_geom_sum_le 1 one_pos a b
  have hconv : ∀ j : ℤ, (3 : ℝ) ^ (c + j) = (3 : ℝ) ^ c * (3 : ℝ) ^ ((1 : ℝ) * (j : ℝ)) := by
    intro j
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), one_mul, Real.rpow_intCast]
  rw [Finset.sum_congr rfl (fun j _ => hconv j), ← Finset.mul_sum]
  have h3 : (0 : ℝ) < (3 : ℝ) ^ c := zpow_pos (by norm_num) _
  calc (3 : ℝ) ^ c * ∑ j ∈ Icc a b, (3 : ℝ) ^ ((1 : ℝ) * (j : ℝ))
      ≤ (3 : ℝ) ^ c * ((3 : ℝ) ^ ((1 : ℝ) * (b : ℝ)) / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) :=
        mul_le_mul_of_nonneg_left h h3.le
    _ = (3 : ℝ) ^ (c + b) * (3 / 2) := by
        rw [one_mul, Real.rpow_intCast, Real.rpow_neg_one, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
        norm_num
        ring

/-- **Sub-cutoff bookkeeping core.** -/
theorem aux_in_deterministic_onestep_sub_core (k N : ℕ) (hkN : k ≤ N) (lo : ℤ)
    (A c1 Cerr Ceps Cdel F ainv alpha : ℝ) (hA : 0 ≤ A) (hc1 : 0 < c1) (hCerr : 0 ≤ Cerr)
    (hCeps : 0 ≤ Ceps) (hCdel : 0 ≤ Cdel) (hF : 0 ≤ F) (hainv : 0 ≤ ainv)
    (err : ℤ → ℝ) (herr0 : ∀ j, 0 ≤ err j) (P : ℤ → ℝ → ℝ → Prop)
    (hstep : ∀ j ∈ Icc lo (-(N : ℤ) - 3), j ≤ -(k : ℤ) - 4 →
      A * (3 : ℝ) ^ ((N : ℤ) + j) ≤ c1 →
      err j ≤ Cerr * (A * (3 : ℝ) ^ ((N : ℤ) + j)) ∧
        P j (Ceps * err j) (Cdel * ainv * (3 : ℝ) ^ (alpha * (j : ℝ)) * F)) :
    ∃ bad : Finset ℤ, bad ⊆ Icc lo (-(N : ℤ) - 3) ∧ ∃ eps del : ℤ → ℝ,
      (∀ j ∈ Icc lo (-(N : ℤ) - 3), 0 ≤ eps j ∧ 0 ≤ del j) ∧
      (∀ j ∈ Icc lo (-(N : ℤ) - 3), j ∉ bad → P j (eps j) (del j)) ∧
      (bad.card : ℝ) ≤ A / c1 + 2 ∧
      ∑ j ∈ Icc lo (-(N : ℤ) - 3), eps j ≤ Ceps * Cerr * A ∧
      ∑ j ∈ Icc lo (-(N : ℤ) - 3), del j ≤
        Cdel * ainv * F * ∑ j ∈ Icc lo (-(N : ℤ) - 3), (3 : ℝ) ^ (alpha * (j : ℝ)) := by
  classical
  set S : Finset ℤ := Icc lo (-(N : ℤ) - 3) with hS
  let good : ℤ → Prop := fun j => j ≤ -(k : ℤ) - 4 ∧ A * (3 : ℝ) ^ ((N : ℤ) + j) ≤ c1
  let eps : ℤ → ℝ := fun j => if good j then Ceps * err j else 0
  let del : ℤ → ℝ := fun j =>
    if good j then Cdel * ainv * (3 : ℝ) ^ (alpha * (j : ℝ)) * F else 0
  have h3pos : ∀ j : ℤ, 0 ≤ (3 : ℝ) ^ (alpha * (j : ℝ)) :=
    fun j => Real.rpow_nonneg (by norm_num) _
  have hz : ∀ j : ℤ, 0 < (3 : ℝ) ^ ((N : ℤ) + j) := fun j => zpow_pos (by norm_num) _
  refine ⟨S.filter (fun j => ¬ good j), Finset.filter_subset _ _, eps, del, ?_, ?_, ?_, ?_, ?_⟩
  · intro j _
    constructor
    · show 0 ≤ (if good j then Ceps * err j else 0)
      split_ifs
      · exact mul_nonneg hCeps (herr0 j)
      · exact le_rfl
    · show 0 ≤ (if good j then Cdel * ainv * (3 : ℝ) ^ (alpha * (j : ℝ)) * F else 0)
      split_ifs
      · exact mul_nonneg (mul_nonneg (mul_nonneg hCdel hainv) (h3pos j)) hF
      · exact le_rfl
  · intro j hj hnot
    have hg : good j := by
      by_contra hng
      exact hnot (Finset.mem_filter.mpr ⟨hj, hng⟩)
    have hst := (hstep j hj hg.1 hg.2).2
    show P j (if good j then Ceps * err j else 0)
      (if good j then Cdel * ainv * (3 : ℝ) ^ (alpha * (j : ℝ)) * F else 0)
    rw [ite_eq_left hg, ite_eq_left hg]
    exact hst
  · -- the count
    have hsub : S.filter (fun j => ¬ good j) ⊆
        S.filter (fun j => -(k : ℤ) - 4 < j) ∪ S.filter (fun j => c1 < A * (3 : ℝ) ^ ((N : ℤ) + j)) := by
      intro j hj
      obtain ⟨hjS, hng⟩ := Finset.mem_filter.mp hj
      by_cases h1 : j ≤ -(k : ℤ) - 4
      · have h2 : ¬ A * (3 : ℝ) ^ ((N : ℤ) + j) ≤ c1 := fun h2 => hng ⟨h1, h2⟩
        push Not at h2
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hjS, h2⟩)
      · push Not at h1
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hjS, h1⟩)
    have hc1' : ((S.filter (fun j => -(k : ℤ) - 4 < j)).card : ℝ) ≤ 1 := by
      have hsub1 : S.filter (fun j => -(k : ℤ) - 4 < j) ⊆ Icc (-(k : ℤ) - 3) (-(N : ℤ) - 3) := by
        intro j hj
        obtain ⟨hjS, hj'⟩ := Finset.mem_filter.mp hj
        rw [hS, Finset.mem_Icc] at hjS
        rw [Finset.mem_Icc]; constructor <;> omega
      have := aux_in_deterministic_onestep_card_Icc_le (-(k : ℤ) - 3) (-(N : ℤ) - 3) 1
        (by push_cast; omega)
      have hc := Finset.card_le_card hsub1
      push_cast at this
      calc ((S.filter (fun j => -(k : ℤ) - 4 < j)).card : ℝ)
          ≤ ((Icc (-(k : ℤ) - 3) (-(N : ℤ) - 3)).card : ℝ) := by exact_mod_cast hc
        _ ≤ 1 := this
    have hc2 : ((S.filter (fun j => c1 < A * (3 : ℝ) ^ ((N : ℤ) + j))).card : ℝ) ≤ A / c1 + 1 := by
      have hinj : Set.InjOn (fun j : ℤ => (-((N : ℤ) + j)).toNat)
          (S.filter (fun j => c1 < A * (3 : ℝ) ^ ((N : ℤ) + j)) : Set ℤ) := by
        intro a ha b hb hab
        simp only [Finset.coe_filter, hS, Finset.mem_Icc, Set.mem_ofPred_eq] at ha hb
        simp only at hab
        omega
      have himg : (S.filter (fun j => c1 < A * (3 : ℝ) ^ ((N : ℤ) + j))).image
          (fun j : ℤ => (-((N : ℤ) + j)).toNat) ⊆ Finset.range ⌈A / c1⌉₊ := by
        intro i hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨hjS, hjc⟩ := Finset.mem_filter.mp hj
        rw [hS, Finset.mem_Icc] at hjS
        rw [Finset.mem_range]
        set i' : ℕ := (-((N : ℤ) + j)).toNat with hi'
        have hi'z : ((i' : ℕ) : ℤ) = -((N : ℤ) + j) := Int.toNat_of_nonneg (by omega)
        have hpow : (3 : ℝ) ^ ((N : ℤ) + j) = ((3 : ℝ) ^ i')⁻¹ := by
          rw [← zpow_natCast, hi'z, zpow_neg, inv_inv]
        have h3i : (i' : ℝ) < (3 : ℝ) ^ i' := by
          have : i' < 3 ^ i' := Nat.lt_pow_self (by norm_num)
          exact_mod_cast this
        have h3ipos : (0 : ℝ) < (3 : ℝ) ^ i' := by positivity
        have hlt : (3 : ℝ) ^ i' < A / c1 := by
          rw [hpow] at hjc
          rw [lt_div_iff₀ hc1]
          have := mul_lt_mul_of_pos_left hjc h3ipos
          rw [mul_comm A, ← mul_assoc, mul_inv_cancel₀ h3ipos.ne', one_mul] at this
          linarith
        have : (i' : ℝ) < A / c1 := h3i.trans hlt
        exact Nat.lt_ceil.mpr this
      have hcard := Finset.card_le_card himg
      rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hcard
      have hceil : (⌈A / c1⌉₊ : ℝ) < A / c1 + 1 := Nat.ceil_lt_add_one (by positivity)
      calc ((S.filter (fun j => c1 < A * (3 : ℝ) ^ ((N : ℤ) + j))).card : ℝ)
          ≤ (⌈A / c1⌉₊ : ℝ) := by exact_mod_cast hcard
        _ ≤ A / c1 + 1 := hceil.le
    have hcu := Finset.card_le_card hsub
    have hcu2 := Finset.card_union_le (S.filter (fun j => -(k : ℤ) - 4 < j))
      (S.filter (fun j => c1 < A * (3 : ℝ) ^ ((N : ℤ) + j)))
    have : ((S.filter (fun j => ¬ good j)).card : ℝ) ≤
        ((S.filter (fun j => -(k : ℤ) - 4 < j)).card : ℝ) +
          (S.filter (fun j => c1 < A * (3 : ℝ) ^ ((N : ℤ) + j))).card := by
      exact_mod_cast hcu.trans hcu2
    linarith
  · -- the error sum
    have hpt : ∀ j ∈ S, eps j ≤ Ceps * Cerr * (A * (3 : ℝ) ^ ((N : ℤ) + j)) := by
      intro j hj
      show (if good j then Ceps * err j else 0) ≤ Ceps * Cerr * (A * (3 : ℝ) ^ ((N : ℤ) + j))
      split_ifs with hg
      · rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hstep j hj hg.1 hg.2).1 hCeps
      · exact mul_nonneg (mul_nonneg hCeps hCerr) (mul_nonneg hA (hz j).le)
    have hgeo := aux_in_deterministic_onestep_geom_zpow_le lo (-(N : ℤ) - 3) (N : ℤ)
    rw [show (N : ℤ) + (-(N : ℤ) - 3) = -3 by ring] at hgeo
    have h3 : (3 : ℝ) ^ (-3 : ℤ) * (3 / 2) ≤ 1 := by norm_num
    calc ∑ j ∈ S, eps j ≤ ∑ j ∈ S, Ceps * Cerr * (A * (3 : ℝ) ^ ((N : ℤ) + j)) :=
          Finset.sum_le_sum hpt
      _ = Ceps * Cerr * A * ∑ j ∈ S, (3 : ℝ) ^ ((N : ℤ) + j) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
      _ ≤ Ceps * Cerr * A * 1 := by
          apply mul_le_mul_of_nonneg_left (hgeo.trans h3)
          exact mul_nonneg (mul_nonneg hCeps hCerr) hA
      _ = Ceps * Cerr * A := mul_one _
  · -- the defect sum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    show (if good j then Cdel * ainv * (3 : ℝ) ^ (alpha * (j : ℝ)) * F else 0) ≤
      Cdel * ainv * F * (3 : ℝ) ^ (alpha * (j : ℝ))
    split_ifs
    · exact le_of_eq (by ring)
    · exact mul_nonneg (mul_nonneg (mul_nonneg hCdel hainv) hF) (h3pos j)

end SubdiffusiveProcess.Paper
end
end DeterministicRegularity_OneStep_SubCore

section DeterministicRegularity_OneStep_SubAt

/-!
# Sub-cutoff window data at one point 

  For windows strictly below the physical wavelength, `j ≤ -N-3`, the working cube
is centred at the point itself (`w = x`), the reference is the actual coefficient
`a0 = A_N(x)`, and the in_J error is bounded by the coefficient oscillation (`NearConst.lean`),
which the padded-root cutoff `Draw` controls geometrically in the depth below the wavelength
(`SubRatio.lean`).  The per-window input `aux_in_deterministic_onestep_window` then gives the
one-step estimate on every good window.
-/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- The coefficient ratio is the exponential of the potential difference. -/
theorem aux_in_deterministic_onestep_coeff_ratio {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (x y : SpatialCoordinates d) :
    cutoffCoefficient M H omega N y / cutoffCoefficient M H omega N x =
      Real.exp (cutoffPotential H omega N y - cutoffPotential H omega N x) := by
  unfold cutoffCoefficient
  have hA := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  rw [mul_div_mul_left _ _ (inv_ne_zero hA.ne'), ← Real.exp_sub]
  congr 1; ring

/-- The two-sided coefficient ratio on a sub-cutoff working cube around `x`. -/
theorem aux_in_deterministic_onestep_sub_window_ratio {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)))
    (s eps : ℝ)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (k : ℕ) (hkN : k ≤ N) (qside : ℝ) (hqpos : 0 < qside)
    (hqside : qside = (3 : ℝ) ^ (-(k : ℤ))) (qcenter : SpatialCoordinates d)
    (G0 : ℝ) (hG0 : 0 ≤ G0)
    (hpad : ∀ pword : Fin (N - k + 1) → OddGridIndex d 1,
      Dsc 0 (((3 : ℝ) ^ N) • descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword) ≠ ⊤ ∧
      (Dsc 0 (((3 : ℝ) ^ N) •
        descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword)).toReal ≤ G0)
    (x : SpatialCoordinates d) (hxq : ∀ i, |x i - qcenter i| < qside / 2)
    (r : ℝ) (hr0 : 0 < r) (hrq : r ≤ qside)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hθr : (d : ℝ) * G0 * ((3 : ℝ) ^ N * r) / 2 ≤ θ) :
    ∀ v ∈ Homogenization.openCubeSet (Homogenization.originCube d 0),
      |cutoffCoefficient M H omega N (fun i => x i + r * v i) /
          cutoffCoefficient M H omega N x - 1| ≤ 3 * θ ∧
      |cutoffCoefficient M H omega N x /
          cutoffCoefficient M H omega N (fun i => x i + r * v i) - 1| ≤ 3 * θ := by
  intro v hv
  set y : SpatialCoordinates d := fun i => x i + r * v i with hy
  have hvi := aux_in_deterministic_good_scale_transfer_mem_unit_root hv
  have hyx : ‖y - x‖ ≤ r / 2 := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    simp only [hy, Pi.sub_apply, add_sub_cancel_left, Real.norm_eq_abs, abs_mul,
      abs_of_pos hr0]
    have h1 := hvi i
    have h2 : |v i| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    calc r * |v i| ≤ r * (1 / 2) := mul_le_mul_of_nonneg_left h2 hr0.le
      _ = r / 2 := by ring
  have hyq : ∀ i, |y i - qcenter i| ≤ qside := by
    intro i
    have h1 : |y i - x i| ≤ r / 2 := by
      have := (pi_norm_le_iff_of_nonneg (by positivity)).mp hyx i
      simpa [Real.norm_eq_abs] using this
    calc |y i - qcenter i| ≤ |y i - x i| + |x i - qcenter i| := abs_sub_le _ _ _
      _ ≤ r / 2 + qside / 2 := add_le_add h1 (hxq i).le
      _ ≤ qside := by linarith
  have hosc := aux_in_deterministic_onestep_sub_osc M H omega N eta hEta hIR s eps
    Fsc Psc Rsc Dsc Zsc goodEvt hPS k hkN qside hqpos hqside qcenter G0 hpad x y
    (fun i => (hxq i).le.trans (by linarith)) hyq
  have hΔ : |cutoffPotential H omega N y - cutoffPotential H omega N x| ≤ θ := by
    refine hosc.trans ?_
    have h1 : (d : ℝ) * G0 * ((3 : ℝ) ^ N * ‖y - x‖) ≤ (d : ℝ) * G0 * ((3 : ℝ) ^ N * (r / 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hyx (by positivity)) (by positivity)
    have h2 : (d : ℝ) * G0 * ((3 : ℝ) ^ N * (r / 2)) = (d : ℝ) * G0 * ((3 : ℝ) ^ N * r) / 2 := by
      ring
    linarith
  set t := cutoffPotential H omega N y - cutoffPotential H omega N x with ht
  have he : Real.exp |t| ≤ 3 := by
    have : Real.exp |t| ≤ Real.exp 1 := Real.exp_le_exp.mpr (hΔ.trans hθ1)
    have h2 := Real.exp_one_lt_d9
    linarith
  have hb : ∀ t' : ℝ, |t'| = |t| → |Real.exp t' - 1| ≤ 3 * θ := by
    intro t' ht'
    refine (aux_in_deterministic_good_scale_transfer_abs_exp_sub_one t').trans ?_
    rw [ht']
    calc |t| * Real.exp |t| ≤ θ * 3 :=
          mul_le_mul hΔ he (Real.exp_pos _).le hθ0
      _ = 3 * θ := mul_comm _ _
  constructor
  · rw [aux_in_deterministic_onestep_coeff_ratio]; exact hb t rfl
  · rw [aux_in_deterministic_onestep_coeff_ratio, show cutoffPotential H omega N x -
        cutoffPotential H omega N y = -t by rw [ht]; ring]
    exact hb (-t) (abs_neg t)

/-- **Sub-cutoff window data at one point.** -/
theorem aux_in_deterministic_onestep_sub_at
    (d : ℕ) [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (h : ℕ) (theta Ceps Cdel E0 : ℝ) (hCeps : 0 ≤ Ceps) (hCdel : 0 ≤ Cdel) (hE0 : 0 < E0)
    (hOS : aux_in_deterministic_onestep_window d I alpha s h theta Ceps Cdel E0)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)))
    (eps : ℝ)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (k : ℕ) (hkN : k ≤ N) (qside : ℝ) (hqpos : 0 < qside)
    (hqside : qside = (3 : ℝ) ^ (-(k : ℤ))) (qcenter : SpatialCoordinates d)
    (G0 : ℝ) (hG0 : 0 ≤ G0)
    (hpad : ∀ pword : Fin (N - k + 1) → OddGridIndex d 1,
      Dsc 0 (((3 : ℝ) ^ N) • descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword) ≠ ⊤ ∧
      (Dsc 0 (((3 : ℝ) ^ N) •
        descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword)).toReal ≤ G0)
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (hqp : Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2) ⊆
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
    (f : SpatialCoordinates d → ℝ)
    (hf : MemLp f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
    (fL2 : DomainL2 (centeredCube Qcentre Qside hQside))
    (hfL2 : (fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] f)
    (u : weakSobolevGraph (centeredCube Qcentre Qside hQside))
    (hu : ∀ psi : killedSobolevGraph (centeredCube Qcentre Qside hQside),
        sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
          (u : SobolevData (centeredCube Qcentre Qside hQside))
          (psi : SobolevData (centeredCube Qcentre Qside hQside)) =
        sobolevVolumeLoad fL2 (psi : SobolevData (centeredCube Qcentre Qside hQside)))
    (U : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
    (huU : ((u : SobolevData (centeredCube Qcentre Qside hQside)).1 :
        SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U)
    (D : ℕ) (x : SpatialCoordinates d) (hx : x ∈ Metric.ball qcenter (qside / 2)) :
    ∃ bad : Finset ℤ, bad ⊆ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3) ∧
    ∃ epsilon defect : ℤ → ℝ,
      (∀ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), 0 ≤ epsilon j ∧ 0 ≤ defect j) ∧
      (∀ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), j ∉ bad →
        ∀ ell : Affine d, ell ∈ affineMinimizers (translatedCube d j x) U →
          excess (j - (h : ℤ)) (translatedCube d (j - (h : ℤ)) x) U ≤
            theta ^ h * excess j (translatedCube d j x) U +
              epsilon j * Real.sqrt (vecNormSq ell.slope) + defect j) ∧
      (bad.card : ℝ) ≤ (9 * d / 2 * G0) / min 1 (E0 / 5) + 2 ∧
      ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), epsilon j ≤
        Ceps * 5 * (9 * d / 2 * G0) ∧
      ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), defect j ≤
        Cdel * (cutoffCoefficient M H omega N x)⁻¹ *
          (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
            (volume.restrict (Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2)))).toReal *
          ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), (3 : ℝ) ^ (alpha * (j : ℝ)) := by
  have hc1 : 0 < min 1 (E0 / 5) := lt_min one_pos (by positivity)
  have ha0 := aux_in_deterministic_good_scale_transfer_cutoffCoefficient_pos M H omega N x
  have hxq : ∀ i, |x i - qcenter i| < qside / 2 := by
    intro i
    have hx' : dist x qcenter < qside / 2 := hx
    rw [dist_pi_lt_iff (by positivity)] at hx'
    have := hx' i
    rwa [Real.dist_eq] at this
  refine aux_in_deterministic_onestep_sub_core k N hkN (-((k : ℤ) + (D : ℤ))) (9 * d / 2 * G0)
    (min 1 (E0 / 5)) 5 Ceps Cdel _ (cutoffCoefficient M H omega N x)⁻¹ alpha (by positivity) hc1
    (by norm_num) hCeps hCdel ENNReal.toReal_nonneg (inv_nonneg.mpr ha0.le)
    (fun j => I.err x ((3 : ℝ) ^ (-(-j - 2))) (by positivity)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N x (by positivity))
      x ((3 : ℝ) ^ (-(-j - 2))) (cutoffCoefficient M H omega N x) s 2)
    (fun j => I.err_nonneg _ _ _ _ _ _ _ _ _)
    (fun j e δ => ∀ ell : Affine d, ell ∈ affineMinimizers (translatedCube d j x) U →
      excess (j - (h : ℤ)) (translatedCube d (j - (h : ℤ)) x) U ≤
        theta ^ h * excess j (translatedCube d j x) U + e * Real.sqrt (vecNormSq ell.slope) + δ)
    ?_
  intro j hj hjk hθ
  rw [Finset.mem_Icc] at hj
  set r : ℝ := (3 : ℝ) ^ (-(-j - 2)) with hr
  have hr0 : 0 < r := by positivity
  set θ : ℝ := 9 * d / 2 * G0 * (3 : ℝ) ^ ((N : ℤ) + j) with hθdef
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := hθ.trans (min_le_left _ _)
  have hθE : θ ≤ E0 / 5 := hθ.trans (min_le_right _ _)
  -- the window scale and the wavelength
  have hrN : (3 : ℝ) ^ N * r = 9 * (3 : ℝ) ^ ((N : ℤ) + j) := by
    rw [hr, ← zpow_natCast, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0),
      show (N : ℤ) + -(-j - 2) = ((N : ℤ) + j) + 2 by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num; ring
  have hrq : r ≤ qside := by
    rw [hr, hqside]
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hratio := aux_in_deterministic_onestep_sub_window_ratio M H omega N eta hEta hIR s eps
    Fsc Psc Rsc Dsc Zsc goodEvt hPS k hkN qside hqpos hqside qcenter G0 hG0 hpad x hxq r hr0 hrq
    θ hθ0 hθ1 (le_of_eq (by rw [hθdef, hrN]; ring))
  have herr := aux_in_deterministic_onestep_err_nearconst I M H omega N x r hr0
    (cutoffCoefficient M H omega N x) ha0 s hs (3 * θ) (by positivity) hratio
  have herr5 : Real.sqrt (2 * (3 * θ) ^ 2) ≤ 5 * θ := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith only [sq_nonneg θ]
  have herrθ := herr.trans herr5
  refine ⟨herrθ, ?_⟩
  intro ell hell
  have hE : I.err x ((3 : ℝ) ^ (-(-j - 2))) (by positivity)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N x (by positivity))
      x ((3 : ℝ) ^ (-(-j - 2))) (cutoffCoefficient M H omega N x) s 2 ≤ E0 := by
    have := herrθ; linarith
  have hx' : x ∈ Metric.ball qcenter ((3 : ℝ) ^ (((1 : ℤ) - k) - 1) / 2) := by
    rw [show ((1 : ℤ) - k) - 1 = -(k : ℤ) by ring, ← hqside]; exact hx
  have hw : x ∈ Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2) := by
    rw [Metric.mem_ball]
    have hx'' : dist x qcenter < qside / 2 := hx
    have : qside / 2 ≤ (3 : ℝ) ^ ((1 : ℤ) - k) / 2 := by
      rw [hqside]; gcongr
      · norm_num
      · omega
    linarith
  have hxx : x ∈ Metric.ball x ((3 : ℝ) ^ (j - 3) / 2) := Metric.mem_ball_self (by positivity)
  exact hOS M H omega N Qcentre Qside hQside qcenter ((1 : ℤ) - k) hqp f hf fL2 hfL2 u hu U hU
    huU x hx' j (-j - 2) (by omega) (by ring) x hw hxx (cutoffCoefficient M H omega N x) ha0 hE
    ell hell

end SubdiffusiveProcess.Paper
end
end DeterministicRegularity_OneStep_SubAt

section DeterministicRegularity_OneStep_Bridge2




open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- The defect part of the lower range (regime `k0 ≤ N - k`). -/
theorem aux_in_deterministic_onestep_lower_defect_at
    (d : ℕ) [NeZero d] (_I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha s : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)))
    (eps : ℝ) (_heps : eps ∈ Set.Ioo (0 : ℝ) 1)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (hdel0 : 0 ≤ M.delta) (hdel1 : M.delta ≤ 1)
    (k cbuf k0 horizon : ℕ) (hkN : k ≤ N)
    (qside : ℝ) (hqpos : 0 < qside) (hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
    (qcenter : SpatialCoordinates d)
    (lambdaCut lambdaDet : ℝ) (hlam0 : 0 ≤ lambdaCut) (hlamlt : lambdaCut ≤ lambdaDet)
    (hpreAll : ∀ (DA : ℕ) (dword : Fin DA → OddGridIndex d 1), k0 ≤ DA → DA ≤ horizon →
      k + DA ≤ N →
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
          Zsc ((N : ℤ) - l).toNat
            (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside DA dword) < lambdaCut * DA ∧
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
          (Dsc ((N : ℤ) - l).toNat
            (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside DA dword)).toReal <
        lambdaCut * DA)
    (hfinAll : ∀ (DA : ℕ) (dword : Fin DA → OddGridIndex d 1), k + DA ≤ N →
      ∀ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
        Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside DA dword) ≠ ⊤)
    (Cdel : ℝ) (hCdel : 0 ≤ Cdel) (C3 : ℝ)
    (hC3a : 9 * Cdel / (1 - (3 : ℝ) ^ (-alpha)) ≤ C3)
    (hC3b : (2 * (d : ℝ) + 4) / Real.log 3 ≤ C3)
    (f : SpatialCoordinates d → ℝ)
    (sk fN : ℝ) (hsk : sk = aux_in_deterministic_onestep_sref M H omega N k qcenter)
    (hfN : 0 ≤ fN)
    (hFq : (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2)))).toReal =
      fN * ((3 * qside) ^ d) ^ (1 / ((d : ℝ) / (1 - alpha))))
    (D : ℕ) (hDh : D ≤ horizon) (x : SpatialCoordinates d)
    (hx : x ∈ Metric.ball qcenter (qside / 2))
    (hreg : k0 ≤ N - k) (hcase : N + 1 < k + D) (Sd : ℝ)
    (hsd : Sd ≤ Cdel * (cutoffCoefficient M H omega N x)⁻¹ *
          (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
            (volume.restrict (Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2)))).toReal *
          ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), (3 : ℝ) ^ (alpha * (j : ℝ))) :
    Sd ≤ C3 * (3 : ℝ) ^ (C3 * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN) / qside := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hlamD : 0 ≤ lambdaDet := hlam0.trans hlamlt
  have ht0 : 0 ≤ lambdaDet + M.delta ^ 2 + eps ^ 8 := by positivity
  have htl : lambdaCut ≤ lambdaDet + M.delta ^ 2 + eps ^ 8 := by
    have : 0 ≤ M.delta ^ 2 + eps ^ 8 := by positivity
    linarith only [this, hlamlt]
  have htd : M.delta ^ 2 ≤ lambdaDet + M.delta ^ 2 + eps ^ 8 := by
    have : 0 ≤ eps ^ 8 := by positivity
    linarith only [this, hlamD]
  have hk0cb : (0 : ℝ) ≤ (k0 : ℝ) + (cbuf : ℝ) := by positivity
  have hTX : (lambdaDet + M.delta ^ 2 + eps ^ 8) * D ≤ ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ))) := by linarith only [hk0cb]
  set Sig : ℝ := lambdaCut * ((N - k : ℕ) : ℝ) with hSig
  have hDAh : N - k ≤ horizon := by omega
  have hself : ∀ dword : Fin (N - k) → OddGridIndex d 1,
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + (N - k : ℕ)),
          (Dsc ((N : ℤ) - l).toNat
            (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside (N - k) dword)).toReal ≤ Sig ∧
      ∀ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + (N - k : ℕ)),
        Dsc ((N : ℤ) - l).toNat
          (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside (N - k) dword) ≠ ⊤ := by
    intro dword
    exact ⟨(hpreAll (N - k) dword hreg hDAh (by omega)).2.le,
      hfinAll (N - k) dword (by omega)⟩
  have hratio := aux_in_deterministic_onestep_sub_ratio M H omega N eta hEta hIR s eps hs
    Fsc Psc Rsc Dsc Zsc goodEvt hPS k cbuf hkN qside hqpos hqside qcenter x hx Sig hself
  rw [← hsk] at hratio
  have hsk0 : 0 < sk := by rw [hsk]; exact aux_in_deterministic_onestep_sref_pos M H omega N k qcenter
  set Ysub : ℝ := ((d : ℝ) + 2) * Sig + ((N - k : ℕ) : ℝ) * M.delta ^ 2 + (d : ℝ) * Sig + Sig +
    M.delta ^ 2 with hYsub
  set S : ℝ := ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3),
    (3 : ℝ) ^ (alpha * (j : ℝ)) with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => Real.rpow_nonneg (by norm_num) _
  have hSle : S ≤ (3 : ℝ) ^ (alpha * ((-(k : ℤ) : ℤ) : ℝ)) / (1 - (3 : ℝ) ^ (-alpha)) := by
    have hg := aux_in_deterministic_onestep_geom_sum_le alpha halpha.1 (-((k : ℤ) + (D : ℤ)))
      (-(N : ℤ) - 3)
    refine hg.trans ?_
    have hr : (3 : ℝ) ^ (-alpha) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [halpha.1])
    apply div_le_div_of_nonneg_right _ (by linarith)
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    apply mul_le_mul_of_nonneg_left _ halpha.1.le
    have : (-(N : ℤ) - 3 : ℤ) ≤ -(k : ℤ) := by omega
    exact_mod_cast this
  have hYb : Ysub ≤ (2 * (d : ℝ) + 4) * ((lambdaDet + M.delta ^ 2 + eps ^ 8) * D) + 1 := by
    have hNk : ((N - k : ℕ) : ℝ) ≤ D := by exact_mod_cast (by omega : N - k ≤ D)
    have hs1 : Sig ≤ (lambdaDet + M.delta ^ 2 + eps ^ 8) * D :=
      mul_le_mul htl hNk (Nat.cast_nonneg _) ht0
    have hs2 : ((N - k : ℕ) : ℝ) * M.delta ^ 2 ≤ (lambdaDet + M.delta ^ 2 + eps ^ 8) * D := by
      rw [mul_comm (lambdaDet + M.delta ^ 2 + eps ^ 8)]
      exact mul_le_mul hNk htd (sq_nonneg _) (Nat.cast_nonneg _)
    have hδ1 : M.delta ^ 2 ≤ 1 := by
      have := mul_le_mul hdel1 hdel1 hdel0 zero_le_one
      nlinarith only [this]
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hSig0 : 0 ≤ Sig := by positivity
    have e1 : (d : ℝ) * Sig ≤ (d : ℝ) * ((lambdaDet + M.delta ^ 2 + eps ^ 8) * D) :=
      mul_le_mul_of_nonneg_left hs1 hd0
    have e2 : ((d : ℝ) + 2) * Sig ≤ ((d : ℝ) + 2) * ((lambdaDet + M.delta ^ 2 + eps ^ 8) * D) :=
      mul_le_mul_of_nonneg_left hs1 (by positivity)
    have e3 : (2 * (d : ℝ) + 4) * ((lambdaDet + M.delta ^ 2 + eps ^ 8) * D) =
        ((d : ℝ) + 2) * ((lambdaDet + M.delta ^ 2 + eps ^ 8) * D) +
          (d : ℝ) * ((lambdaDet + M.delta ^ 2 + eps ^ 8) * D) +
          (lambdaDet + M.delta ^ 2 + eps ^ 8) * D +
          (lambdaDet + M.delta ^ 2 + eps ^ 8) * D := by ring
    rw [hYsub, e3]
    linarith only [e1, e2, hs1, hs2, hδ1]
  have hmono : Sd ≤ Cdel * (Real.exp Ysub * sk⁻¹) *
        (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
          (volume.restrict (Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2)))).toReal * S := by
    refine hsd.trans ?_
    apply mul_le_mul_of_nonneg_right _ hS0
    apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
    exact mul_le_mul_of_nonneg_left hratio hCdel
  have hB := aux_in_deterministic_onestep_budget_defect_gen d hd k qside alpha Cdel Ysub sk _ fN
    S ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ))) C3 ((lambdaDet + M.delta ^ 2 + eps ^ 8) * D) (2 * (d : ℝ) + 4) hqside halpha.1 halpha.2
    hCdel hsk0 hfN hFq hSle (by positivity) (by positivity) hYb hTX hC3a hC3b
  rw [le_div_iff₀ hqpos, mul_comm]
  exact (mul_le_mul_of_nonneg_left hmono hqpos.le).trans hB

/-- **The lower (sub-cutoff) range in the regime `k0 ≤ N - k`**, budgets in `C3` form. -/
theorem aux_in_deterministic_onestep_at_point_lower
    (d : ℕ) [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha s : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (h : ℕ) (theta Ceps Cdel E0 : ℝ) (hCeps : 0 ≤ Ceps) (hCdel : 0 ≤ Cdel)
    (hOS : aux_in_deterministic_onestep_window d I alpha s h theta Ceps Cdel E0)
    (Cg c0 C3 : ℝ) (hE0 : 0 < E0)
    (hC3card : 9 * (d : ℝ) / 2 / min 1 (E0 / 5) + 2 ≤ C3)
    (hC3eps : Ceps * 5 * (9 * (d : ℝ) / 2) ≤ C3)
    (hC3a : 9 * Cdel / (1 - (3 : ℝ) ^ (-alpha)) ≤ C3)
    (hC3b : (2 * (d : ℝ) + 4) / Real.log 3 ≤ C3)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)))
    (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (_hG : ∀ (j : ℤ) (w : SpatialCoordinates d), j ≤ (N : ℤ) →
      Dsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) ≠ ⊤ →
      Zsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) < 1 →
      I.err w ((3 : ℝ) ^ (-j)) (by positivity)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
          w ((3 : ℝ) ^ (-j)) (aux_in_deterministic_onestep_sref M H omega N j w) s 2 ≤
        Cg * (M.delta ^ 2 + eps ^ 8 +
          (Dsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w)).toReal))
    (_hcapE : Cg * (M.delta ^ 2 + eps ^ 8) + Cg * c0 ≤ E0)
    (hdel0 : 0 ≤ M.delta) (hdel1 : M.delta ≤ 1)
    (k cbuf k0 horizon : ℕ) (hkN : k ≤ N)
    (qside : ℝ) (hqpos : 0 < qside) (hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
    (qcenter : SpatialCoordinates d)
    (lambdaCut lambdaDet : ℝ) (hlam0 : 0 ≤ lambdaCut) (hlamlt : lambdaCut ≤ lambdaDet)
    (hpreAll : ∀ (DA : ℕ) (dword : Fin DA → OddGridIndex d 1), k0 ≤ DA → DA ≤ horizon →
      k + DA ≤ N →
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
          Zsc ((N : ℤ) - l).toNat
            (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside DA dword) < lambdaCut * DA ∧
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
          (Dsc ((N : ℤ) - l).toNat
            (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside DA dword)).toReal <
        lambdaCut * DA)
    (hfinAll : ∀ (DA : ℕ) (dword : Fin DA → OddGridIndex d 1), k + DA ≤ N →
      ∀ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
        Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside DA dword) ≠ ⊤)
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (hqp : Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2) ⊆
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
    (f : SpatialCoordinates d → ℝ)
    (hf : MemLp f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
    (fL2 : DomainL2 (centeredCube Qcentre Qside hQside))
    (hfL2 : (fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] f)
    (u : weakSobolevGraph (centeredCube Qcentre Qside hQside))
    (hu : ∀ psi : killedSobolevGraph (centeredCube Qcentre Qside hQside),
        sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
          (u : SobolevData (centeredCube Qcentre Qside hQside))
          (psi : SobolevData (centeredCube Qcentre Qside hQside)) =
        sobolevVolumeLoad fL2 (psi : SobolevData (centeredCube Qcentre Qside hQside)))
    (U : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
    (huU : ((u : SobolevData (centeredCube Qcentre Qside hQside)).1 :
        SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U)
    (sk fN : ℝ) (hsk : sk = aux_in_deterministic_onestep_sref M H omega N k qcenter)
    (hfN : 0 ≤ fN)
    (hFq : (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2)))).toReal =
      fN * ((3 * qside) ^ d) ^ (1 / ((d : ℝ) / (1 - alpha))))
    (hpadAll : ∀ pword : Fin (N - k + 1) → OddGridIndex d 1,
      Dsc 0 (((3 : ℝ) ^ N) • descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword) ≠ ⊤ ∧
      (Dsc 0 (((3 : ℝ) ^ N) • descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword)).toReal ≤
        lambdaCut * ((N - k + 1 : ℕ) : ℝ))
    (D : ℕ) (hDh : D ≤ horizon) (x : SpatialCoordinates d)
    (hx : x ∈ Metric.ball qcenter (qside / 2))
    (hreg : k0 ≤ N - k) (hcase : N + 1 < k + D) :
    ∃ bad : Finset ℤ, bad ⊆ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3) ∧
    ∃ epsilon defect : ℤ → ℝ,
      (∀ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), 0 ≤ epsilon j ∧ 0 ≤ defect j) ∧
      (∀ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), j ∉ bad →
        ∀ ell : Affine d, ell ∈ affineMinimizers (translatedCube d j x) U →
          excess (j - (h : ℤ)) (translatedCube d (j - (h : ℤ)) x) U ≤
            theta ^ h * excess j (translatedCube d j x) U +
              epsilon j * Real.sqrt (vecNormSq ell.slope) + defect j) ∧
      (bad.card : ℝ) ≤ C3 * (1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) ∧
      ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), epsilon j ≤ C3 * (1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) ∧
      ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), defect j ≤
        C3 * (3 : ℝ) ^ (C3 * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN) / qside := by
  have hlamD : 0 ≤ lambdaDet := hlam0.trans hlamlt
  have ht0 : 0 ≤ lambdaDet + M.delta ^ 2 + eps ^ 8 := by positivity
  have htl : lambdaCut ≤ lambdaDet + M.delta ^ 2 + eps ^ 8 := by
    have : 0 ≤ M.delta ^ 2 + eps ^ 8 := by positivity
    linarith only [this, hlamlt]
  have hk0cb : (0 : ℝ) ≤ (k0 : ℝ) + (cbuf : ℝ) := by positivity
  have hG0 : 0 ≤ lambdaCut * ((N - k + 1 : ℕ) : ℝ) := by positivity
  have hDG : lambdaCut * ((N - k + 1 : ℕ) : ℝ) ≤ (lambdaDet + M.delta ^ 2 + eps ^ 8) * D := by
    have : ((N - k + 1 : ℕ) : ℝ) ≤ D := by exact_mod_cast (by omega : N - k + 1 ≤ D)
    exact mul_le_mul htl this (Nat.cast_nonneg _) ht0
  have hTX : (lambdaDet + M.delta ^ 2 + eps ^ 8) * D ≤ ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ))) := by linarith only [hk0cb]
  obtain ⟨bad, hbad, e, dl, hnn, hP, hc, hse, hsd⟩ :=
    aux_in_deterministic_onestep_sub_at d I alpha s hs h theta Ceps Cdel E0 hCeps hCdel hE0 hOS
      M H omega N eta hEta hIR eps Fsc Psc Rsc Dsc Zsc goodEvt hPS k hkN qside hqpos hqside
      qcenter (lambdaCut * ((N - k + 1 : ℕ) : ℝ)) hG0 hpadAll Qcentre Qside hQside hqp f hf fL2
      hfL2 u hu U hU huU D x hx
  refine ⟨bad, hbad, e, dl, hnn, hP, ?_, ?_, ?_⟩
  · have hc1 : 0 < min 1 (E0 / 5) := lt_min one_pos (by positivity)
    exact hc.trans (aux_in_deterministic_onestep_budget_card_sub (9 * (d : ℝ) / 2)
      (min 1 (E0 / 5)) (lambdaCut * ((N - k + 1 : ℕ) : ℝ)) ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ))) C3 (by positivity) hc1 hG0
      (hDG.trans hTX) hC3card)
  · have hb := aux_in_deterministic_onestep_budget_eps_sub (Ceps * 5 * (9 * (d : ℝ) / 2))
      (lambdaCut * ((N - k + 1 : ℕ) : ℝ)) ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ))) C3 (by positivity) hG0 (hDG.trans hTX) hC3eps
    refine hse.trans (le_trans (le_of_eq ?_) hb)
    ring
  · exact aux_in_deterministic_onestep_lower_defect_at d I alpha s halpha hs M H omega N eta
      hEta hIR eps heps Fsc Psc Rsc Dsc Zsc goodEvt hPS hdel0 hdel1 k cbuf k0 horizon hkN
      qside hqpos hqside qcenter lambdaCut lambdaDet hlam0 hlamlt hpreAll hfinAll Cdel hCdel
      C3 hC3a hC3b f sk fN hsk hfN hFq D hDh x hx hreg hcase _ hsd

/-- **The one-step data at one point, three regimes.** -/
theorem aux_in_deterministic_onestep_at_point2
    (d : ℕ) [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha s : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (h : ℕ) (theta Ceps Cdel E0 : ℝ) (hCeps : 0 ≤ Ceps) (hCdel : 0 ≤ Cdel)
    (hOS : aux_in_deterministic_onestep_window d I alpha s h theta Ceps Cdel E0)
    (Cg c0 C2 Csub : ℝ) (hCg : 0 ≤ Cg) (hc0 : 0 < c0) (hC20 : 0 ≤ C2)
    (hC2a : 11 + c0⁻¹ ≤ C2) (hC2b : 2 * Ceps * Cg ≤ C2)
    (hC2c : 3 * Cdel / (1 - (3 : ℝ) ^ (-alpha)) ≤ C2)
    (hC2d : ((d : ℝ) + 3) / Real.log 3 ≤ C2) (hCsub : 0 ≤ Csub)
    (C3 : ℝ) (hE0 : 0 < E0)
    (hC3card : 9 * (d : ℝ) / 2 / min 1 (E0 / 5) + 2 ≤ C3)
    (hC3eps : Ceps * 5 * (9 * (d : ℝ) / 2) ≤ C3)
    (hC3a : 9 * Cdel / (1 - (3 : ℝ) ^ (-alpha)) ≤ C3)
    (hC3b : (2 * (d : ℝ) + 4) / Real.log 3 ≤ C3)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)))
    (eps : ℝ) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (hG : ∀ (j : ℤ) (w : SpatialCoordinates d), j ≤ (N : ℤ) →
      Dsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) ≠ ⊤ →
      Zsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) < 1 →
      I.err w ((3 : ℝ) ^ (-j)) (by positivity)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
          w ((3 : ℝ) ^ (-j)) (aux_in_deterministic_onestep_sref M H omega N j w) s 2 ≤
        Cg * (M.delta ^ 2 + eps ^ 8 +
          (Dsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w)).toReal))
    (hcapE : Cg * (M.delta ^ 2 + eps ^ 8) + Cg * c0 ≤ E0)
    (hdel0 : 0 ≤ M.delta) (hdel1 : M.delta ≤ 1)
    (k cbuf k0 horizon : ℕ) (hkN : k ≤ N)
    (qside : ℝ) (hqpos : 0 < qside) (hqside : qside = (3 : ℝ) ^ (-(k : ℤ)))
    (qcenter : SpatialCoordinates d)
    (lambdaCut lambdaDet : ℝ) (hlam0 : 0 ≤ lambdaCut) (hlamlt : lambdaCut ≤ lambdaDet)
    (hpreAll : ∀ (DA : ℕ) (dword : Fin DA → OddGridIndex d 1), k0 ≤ DA → DA ≤ horizon →
      k + DA ≤ N →
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
          Zsc ((N : ℤ) - l).toNat
            (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside DA dword) < lambdaCut * DA ∧
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
          (Dsc ((N : ℤ) - l).toNat
            (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside DA dword)).toReal <
        lambdaCut * DA)
    (hfinAll : ∀ (DA : ℕ) (dword : Fin DA → OddGridIndex d 1), k + DA ≤ N →
      ∀ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
        Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside DA dword) ≠ ⊤)
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (hqp : Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2) ⊆
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
    (f : SpatialCoordinates d → ℝ)
    (hf : MemLp f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
    (fL2 : DomainL2 (centeredCube Qcentre Qside hQside))
    (hfL2 : (fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] f)
    (u : weakSobolevGraph (centeredCube Qcentre Qside hQside))
    (hu : ∀ psi : killedSobolevGraph (centeredCube Qcentre Qside hQside),
        sobolevCoefficientForm
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
          (u : SobolevData (centeredCube Qcentre Qside hQside))
          (psi : SobolevData (centeredCube Qcentre Qside hQside)) =
        sobolevVolumeLoad fL2 (psi : SobolevData (centeredCube Qcentre Qside hQside)))
    (U : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
    (huU : ((u : SobolevData (centeredCube Qcentre Qside hQside)).1 :
        SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U)
    (sk fN : ℝ) (hsk : sk = aux_in_deterministic_onestep_sref M H omega N k qcenter)
    (hfN : 0 ≤ fN)
    (hFq : (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2)))).toReal =
      fN * ((3 * qside) ^ d) ^ (1 / ((d : ℝ) / (1 - alpha))))
    (hpadAll : k0 ≤ N - k → N - k + 1 ≤ horizon → ∀ pword : Fin (N - k + 1) → OddGridIndex d 1,
      Dsc 0 (((3 : ℝ) ^ N) • descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword) ≠ ⊤ ∧
      (Dsc 0 (((3 : ℝ) ^ N) • descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword)).toReal ≤
        lambdaCut * ((N - k + 1 : ℕ) : ℝ))
    (D : ℕ) (hDh : D ≤ horizon) (x : SpatialCoordinates d)
    (hx : x ∈ Metric.ball qcenter (qside / 2))
    (hlow : N + 1 < k + D → N < k + k0 →
      ∃ bad : Finset ℤ, bad ⊆ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3) ∧
      ∃ epsilon defect : ℤ → ℝ,
        (∀ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), 0 ≤ epsilon j ∧ 0 ≤ defect j) ∧
        (∀ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), j ∉ bad →
          ∀ ell : Affine d, ell ∈ affineMinimizers (translatedCube d j x) U →
            excess (j - (h : ℤ)) (translatedCube d (j - (h : ℤ)) x) U ≤
              theta ^ h * excess j (translatedCube d j x) U +
                epsilon j * Real.sqrt (vecNormSq ell.slope) + defect j) ∧
        (bad.card : ℝ) ≤ Csub * (1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) ∧
        ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), epsilon j ≤
          Csub * (1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) ∧
        qside * ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), defect j ≤
          Csub * (3 : ℝ) ^ (Csub * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN)) :
    ∃ bad : Finset ℤ, bad ⊆ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(k : ℤ)) ∧
    ∃ epsilon defect : ℤ → ℝ,
      (∀ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(k : ℤ)), 0 ≤ epsilon j ∧ 0 ≤ defect j) ∧
      (∀ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(k : ℤ)), j ∉ bad →
        ∀ ell : Affine d, ell ∈ affineMinimizers (translatedCube d j x) U →
          excess (j - (h : ℤ)) (translatedCube d (j - (h : ℤ)) x) U ≤
            theta ^ h * excess j (translatedCube d j x) U +
              epsilon j * Real.sqrt (vecNormSq ell.slope) + defect j) ∧
      (bad.card : ℝ) ≤ (C2 + C3 + Csub) * (1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) ∧
      ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(k : ℤ)), epsilon j ≤
        (C2 + C3 + Csub) * (1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) ∧
      qside * ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(k : ℤ)), defect j ≤
        (C2 + C3 + Csub) * (3 : ℝ) ^ ((C2 + C3 + Csub) * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN) := by
  have hlamD : 0 ≤ lambdaDet := hlam0.trans hlamlt
  have ht0 : 0 ≤ lambdaDet + M.delta ^ 2 + eps ^ 8 := by positivity
  have hX0 : 0 ≤ ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ))) := by positivity
  have hsk0 : 0 < sk := by rw [hsk]; exact aux_in_deterministic_onestep_sref_pos M H omega N k qcenter
  have hW : 0 ≤ qside ^ 2 * sk⁻¹ * fN := by positivity
  have h1X : 0 ≤ 1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ))) := by linarith
  have hC30 : 0 ≤ C3 :=
    (by positivity : (0 : ℝ) ≤ 9 * (d : ℝ) / 2 / min 1 (E0 / 5) + 2).trans hC3card
  have hCs1 : 0 ≤ Csub * (1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) := mul_nonneg hCsub h1X
  have hC31 : 0 ≤ C3 * (1 + ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) := mul_nonneg hC30 h1X
  have hup := fun (jlo : ℤ) (h1 : jlo ≤ -((k : ℤ) + (min D (N - k) : ℕ)) + 4)
      (h2 : -((k : ℤ) + (min D (N - k) : ℕ)) - 2 ≤ jlo) =>
    aux_in_deterministic_onestep_at_point_upper d I alpha s halpha hs h theta Ceps Cdel E0
      hCeps hCdel hOS Cg c0 C2 Csub hCg hc0 hC20 hC2a hC2b hC2c hC2d hCsub M H omega N eta hEta
      hIR eps heps Fsc Psc Rsc Dsc Zsc goodEvt hPS hG hcapE hdel0 hdel1 k cbuf k0 horizon hkN
      qside hqpos hqside qcenter lambdaCut lambdaDet hlam0 hlamlt hpreAll hfinAll Qcentre Qside
      hQside hqp f hf fL2 hfL2 u hu U hU huU sk fN hsk hfN hFq D hDh x hx jlo h1 h2
  -- monotonicity of the defect budget in the constant
  have hmono : ∀ (C C' A : ℝ), 0 ≤ C → C ≤ C' →
      A ≤ C * (3 : ℝ) ^ (C * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN) →
      A ≤ C' * (3 : ℝ) ^ (C' * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN) := by
    intro C C' A hC hCC' hA
    have := aux_in_deterministic_onestep_budget_add C (C' - C) ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ))) (qside ^ 2 * sk⁻¹ * fN)
      A 0 hC (by linarith) hX0 hW hA (by
        have : 0 ≤ (C' - C) * (3 : ℝ) ^ ((C' - C) * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN) := by
          have : 0 ≤ C' - C := by linarith
          positivity
        linarith)
    rw [add_zero, show C + (C' - C) = C' by ring] at this
    exact this
  rcases Nat.lt_or_ge (N + 1) (k + D) with hcase | hcase
  · obtain ⟨badU, hbU, eU, dU, hnnU, hPU, hcU, hsU, htU⟩ :=
      hup (-(N : ℤ) - 3 + 1) (by omega) (by omega)
    by_cases hreg : k0 ≤ N - k
    · -- below the wavelength, prefix reaching the cutoff available: the proved lower range
      obtain ⟨badL, hbL, eL, dL, hnnL, hPL, hcL, hsL, htL⟩ :=
        aux_in_deterministic_onestep_at_point_lower d I alpha s halpha hs h theta Ceps Cdel E0
          hCeps hCdel hOS Cg c0 C3 hE0 hC3card hC3eps hC3a hC3b M H omega N eta hEta hIR eps heps
          Fsc Psc Rsc Dsc Zsc goodEvt hPS hG hcapE hdel0 hdel1 k cbuf k0 horizon hkN qside hqpos
          hqside qcenter lambdaCut lambdaDet hlam0 hlamlt hpreAll hfinAll Qcentre Qside hQside hqp
          f hf fL2 hfL2 u hu U hU huU sk fN hsk hfN hFq (hpadAll hreg (by omega)) D hDh x hx
          hreg hcase
      obtain ⟨bad, hbad, e, dl, hnn, hP, hc, hse, hsd⟩ :=
        aux_in_deterministic_onestep_splice (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3) (-(k : ℤ))
          (by omega) (by omega) (fun j e δ => ∀ ell : Affine d, ell ∈ affineMinimizers (translatedCube d j x) U →
          excess (j - (h : ℤ)) (translatedCube d (j - (h : ℤ)) x) U ≤
            theta ^ h * excess j (translatedCube d j x) U +
              e * Real.sqrt (vecNormSq ell.slope) + δ)
          _ _ _ _ _ _ ⟨badL, hbL, eL, dL, hnnL, hPL, hcL, hsL, htL⟩
          ⟨badU, hbU, eU, dU, hnnU, hPU, hcU, hsU, htU⟩
      refine ⟨bad, hbad, e, dl, hnn, hP, ?_, ?_, ?_⟩
      · linarith only [hc, hCs1]
      · linarith only [hse, hCs1]
      · have hadd := aux_in_deterministic_onestep_budget_add C3 C2 ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))
          (qside ^ 2 * sk⁻¹ * fN) _ _ hC30 hC20 hX0 hW
          (le_refl (C3 * (3 : ℝ) ^ (C3 * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN)))
          (le_refl (C2 * (3 : ℝ) ^ (C2 * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN)))
        have hmul := mul_le_mul_of_nonneg_left hsd hqpos.le
        rw [mul_add, mul_div_cancel₀ _ hqpos.ne', mul_div_cancel₀ _ hqpos.ne'] at hmul
        have h2 := hmono (C3 + C2) (C2 + C3 + Csub) _ (add_nonneg hC30 hC20) (by linarith)
          (hmul.trans hadd)
        exact h2
    · -- below the wavelength, no prefix reaching the cutoff: the residual obligation
      obtain ⟨badL, hbL, eL, dL, hnnL, hPL, hcL, hsL, htL⟩ := hlow hcase (by omega)
      have htL' : ∑ j ∈ Finset.Icc (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3), dL j ≤
          Csub * (3 : ℝ) ^ (Csub * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN) / qside := by
        rw [le_div_iff₀ hqpos, mul_comm]; exact htL
      obtain ⟨bad, hbad, e, dl, hnn, hP, hc, hse, hsd⟩ :=
        aux_in_deterministic_onestep_splice (-((k : ℤ) + (D : ℤ))) (-(N : ℤ) - 3) (-(k : ℤ))
          (by omega) (by omega) (fun j e δ => ∀ ell : Affine d, ell ∈ affineMinimizers (translatedCube d j x) U →
          excess (j - (h : ℤ)) (translatedCube d (j - (h : ℤ)) x) U ≤
            theta ^ h * excess j (translatedCube d j x) U +
              e * Real.sqrt (vecNormSq ell.slope) + δ)
          _ _ _ _ _ _ ⟨badL, hbL, eL, dL, hnnL, hPL, hcL, hsL, htL'⟩
          ⟨badU, hbU, eU, dU, hnnU, hPU, hcU, hsU, htU⟩
      refine ⟨bad, hbad, e, dl, hnn, hP, ?_, ?_, ?_⟩
      · linarith only [hc, hC31]
      · linarith only [hse, hC31]
      · have hadd := aux_in_deterministic_onestep_budget_add C2 Csub ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))
          (qside ^ 2 * sk⁻¹ * fN) _ _ hC20 hCsub hX0 hW
          (le_refl (C2 * (3 : ℝ) ^ (C2 * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN)))
          (le_refl (Csub * (3 : ℝ) ^ (Csub * ((((k0 : ℝ) + (cbuf : ℝ)) + (lambdaDet + M.delta ^ 2 + eps ^ 8) * (D : ℝ)))) * (qside ^ 2 * sk⁻¹ * fN)))
        have hmul := mul_le_mul_of_nonneg_left hsd hqpos.le
        rw [mul_add, mul_div_cancel₀ _ hqpos.ne', mul_div_cancel₀ _ hqpos.ne'] at hmul
        rw [add_comm C2 Csub] at hadd
        exact hmono (Csub + C2) (C2 + C3 + Csub) _ (add_nonneg hCsub hC20) (by linarith)
          (by linarith only [hmul, hadd])
  · -- at or above the wavelength: the upper range is the whole ray
    obtain ⟨bad, hbad, e, dl, hnn, hP, hc, hse, hsd⟩ :=
      hup (-((k : ℤ) + (D : ℤ))) (by omega) (by omega)
    refine ⟨bad, hbad, e, dl, hnn, hP, ?_, ?_, ?_⟩
    · linarith only [hc, hCs1, hC31]
    · linarith only [hse, hCs1, hC31]
    · have hmul := mul_le_mul_of_nonneg_left hsd hqpos.le
      rw [mul_div_cancel₀ _ hqpos.ne'] at hmul
      exact hmono C2 (C2 + C3 + Csub) _ hC20 (by linarith) hmul

end SubdiffusiveProcess.Paper
end
end DeterministicRegularity_OneStep_Bridge2

section DeterministicRegularity_OneStep_Repaired




open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- **The repaired residual from the per-window input alone.** -/
theorem aux_in_deterministic_onestep_repaired_of_window
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (alpha beta s sigma cell epshom : ℝ)
    (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsSmall : s ≤ (1 / 32 : ℝ))
    (h : ℕ) (theta Ceps Cdel E0 : ℝ) (hE0 : 0 < E0) (hCeps : 0 ≤ Ceps) (hCdel : 0 ≤ Cdel)
    (hOS : aux_in_deterministic_onestep_window d I alpha s h theta Ceps Cdel E0) :
    ∃ C2 : ℝ, 0 ≤ C2 ∧ ∃ eAn dAn : ℝ, 0 < eAn ∧ 0 < dAn ∧
      ∀ (Cbound eps0 lam0 delta0 : ℝ), eps0 ≤ eAn → delta0 ≤ dAn →
        aux_in_deterministic_regularity_onestep d I alpha beta s sigma cell epshom
          Cbound eps0 lam0 delta0 h theta C2 := by
  obtain ⟨Cg, dg, hCg, hdg, hGST⟩ := in_deterministic_good_scale_transfer d I s hs hsSmall
  have hc0 : 0 < E0 / (2 * Cg) := by positivity
  have hcap : 0 < E0 / (4 * Cg) := by positivity
  have hr3 : (3 : ℝ) ^ (-alpha) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [halpha.1])
  have hden : 0 < 1 - (3 : ℝ) ^ (-alpha) := by linarith
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  obtain ⟨C2, hC2def⟩ : ∃ C2 : ℝ, C2 = max (max (11 + (E0 / (2 * Cg))⁻¹) (2 * Ceps * Cg))
      (max (3 * Cdel / (1 - (3 : ℝ) ^ (-alpha))) (((d : ℝ) + 3) / Real.log 3)) := ⟨_, rfl⟩
  have hC2a : 11 + (E0 / (2 * Cg))⁻¹ ≤ C2 := by
    rw [hC2def]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hC2b : 2 * Ceps * Cg ≤ C2 := by
    rw [hC2def]; exact (le_max_right _ _).trans (le_max_left _ _)
  have hC2c : 3 * Cdel / (1 - (3 : ℝ) ^ (-alpha)) ≤ C2 := by
    rw [hC2def]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hC2d : ((d : ℝ) + 3) / Real.log 3 ≤ C2 := by
    rw [hC2def]; exact (le_max_right _ _).trans (le_max_right _ _)
  have hC20 : 0 ≤ C2 := (by positivity : (0 : ℝ) ≤ 11 + (E0 / (2 * Cg))⁻¹).trans hC2a
  obtain ⟨C3, hC3def⟩ : ∃ C3 : ℝ, C3 = max (max (9 * (d : ℝ) / 2 / min 1 (E0 / 5) + 2)
      (Ceps * 5 * (9 * (d : ℝ) / 2)))
      (max (9 * Cdel / (1 - (3 : ℝ) ^ (-alpha))) ((2 * (d : ℝ) + 4) / Real.log 3)) := ⟨_, rfl⟩
  have hC3card : 9 * (d : ℝ) / 2 / min 1 (E0 / 5) + 2 ≤ C3 := by
    rw [hC3def]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hC3eps : Ceps * 5 * (9 * (d : ℝ) / 2) ≤ C3 := by
    rw [hC3def]; exact (le_max_right _ _).trans (le_max_left _ _)
  have hC3a : 9 * Cdel / (1 - (3 : ℝ) ^ (-alpha)) ≤ C3 := by
    rw [hC3def]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hC3b : (2 * (d : ℝ) + 4) / Real.log 3 ≤ C3 := by
    rw [hC3def]; exact (le_max_right _ _).trans (le_max_right _ _)
  have hC30 : 0 ≤ C3 := (by
    have : (0 : ℝ) < min 1 (E0 / 5) := lt_min one_pos (by positivity)
    positivity : (0 : ℝ) ≤ 9 * (d : ℝ) / 2 / min 1 (E0 / 5) + 2).trans hC3card
  refine ⟨C2 + C3 + 0, by linarith, min 1 (E0 / (4 * Cg)), min (min 1 dg) (E0 / (4 * Cg)),
    lt_min one_pos hcap, lt_min (lt_min one_pos hdg) hcap, ?_⟩
  intro Cbound eps0 lam0 delta0 heps0 hdelta0
  have hCsub : (0 : ℝ) ≤ 0 := le_rfl
  intro cbuf k0 M H hMH k z qside hqpos hqside qcenter hqcenter Enl Shift Cmp _ _ _
    selfE selfShift qRoot hqRoot factor hfactor padE hpad shift hshift rootLevel hrootLevel
    rootSide hrootSide rootCentre hrootCentre rootPos hGridCover parent depth cword cmpCentre
    hcmpCentre cmpLevel hcmpLevel cmpSide hcmpSide cmpPos chosen observationCentre
    hObservationCentre eta hEta F Praw Rraw Draw Z rawGood eps heps hepsSmall hPrimitive
    lambdaCut lambdaLim lambdaDet cdet hThresholds hcdet hcdetSmall hlamSmall hdisorder
    prefixZ prefixD hPrefixZ hPrefixD hFiniteScoreGuard sN hsN ellLoN ellHiN hEllLoN hEllHiN
    AEN hAEN errN ratioN hErrN hRatioN Qcentre Qside hQside hRootsQ
    Q q qp Ctotal psource N hkkN hcmp harmonicComparison traceEstimate
  have hkN : k ≤ N := by omega
  have hdel0 : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
  have hdel1 : M.delta ≤ 1 :=
    hdisorder.trans (hdelta0.trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hdelg : M.delta ≤ dg :=
    hdisorder.trans (hdelta0.trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hdelc : M.delta ≤ E0 / (4 * Cg) := hdisorder.trans (hdelta0.trans (min_le_right _ _))
  have hepsc : eps ≤ E0 / (4 * Cg) := hepsSmall.trans (heps0.trans (min_le_right _ _))
  have hcapE : Cg * (M.delta ^ 2 + eps ^ 8) + Cg * (E0 / (2 * Cg)) ≤ E0 := by
    have h1 : M.delta ^ 2 ≤ E0 / (4 * Cg) := by
      calc
        M.delta ^ 2 = M.delta * M.delta := pow_two _
        _ ≤ M.delta * 1 := mul_le_mul_of_nonneg_left hdel1 hdel0
        _ = M.delta := mul_one _
        _ ≤ E0 / (4 * Cg) := hdelc
    have h2 : eps ^ 8 ≤ E0 / (4 * Cg) := by
      have : eps ^ 8 ≤ eps := by
        calc eps ^ 8 ≤ eps ^ 1 := pow_le_pow_of_le_one heps.1.le heps.2.le (by norm_num)
          _ = eps := pow_one eps
      linarith
    have h3 : Cg * (M.delta ^ 2 + eps ^ 8) ≤ Cg * (2 * (E0 / (4 * Cg))) :=
      mul_le_mul_of_nonneg_left (by linarith) hCg.le
    have h4 : Cg * (2 * (E0 / (4 * Cg))) + Cg * (E0 / (2 * Cg)) = E0 := by
      field_simp; ring
    linarith
  have hG_ae := hGST M H hMH hdelg eps heps eta F Praw Rraw Draw Z rawGood hEta hPrimitive sN hsN
  have hrl : rootLevel qRoot = (k : ℤ) := by rw [hqRoot, hrootLevel, hfactor]; simp
  have hrs : rootSide qRoot = qside := by rw [hrootSide, hrl, hqside]
  have hrc : rootCentre qRoot = qcenter := by
    rw [hqRoot, hrootCentre, hshift, smul_zero, add_zero]
  have h3q : (3 : ℝ) ^ ((1 : ℤ) - k) / 2 = 3 * qside / 2 := by
    rw [hqside, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one, _root_.zpow_neg]; ring
  have hqp : Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2) ⊆
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) := by
    rw [h3q]
    exact aux_in_deterministic_regularity_qp_subset k qside hqside qcenter Enl Shift
      selfShift padE factor hpad shift hshift rootLevel hrootLevel rootSide hrootSide rootCentre
      hrootCentre rootPos Qcentre Qside hQside hRootsQ
  have hlam0 : 0 ≤ lambdaCut := hThresholds.1.le
  have hlamlt : lambdaCut ≤ lambdaDet := (hThresholds.2.1.trans hThresholds.2.2.1).le
  have hobs : ∀ (DA : ℕ) (dword : Fin DA → OddGridIndex d 1),
      observationCentre qRoot DA (Sum.inl dword) = descendantCenter 1 qcenter qside DA dword := by
    intro DA dword
    rw [hObservationCentre]; simp only [Sum.elim_inl]; rw [hrc, hrs]
  have hsk : sN N (k : ℤ) qcenter = fun omega =>
      aux_in_deterministic_onestep_sref M H omega N k qcenter := by
    funext omega; rw [hsN, ite_eq_left (by exact_mod_cast hkN)]; rfl
  filter_upwards [hEta, hPrimitive, hFiniteScoreGuard, hMH.2, hG_ae] with
    omega hEtaω hPω hFinω hIRω hGω
  intro horizon hev hb f hf fL2 hfL2 fNorm u hu U hU huU D hD1 hDh x hx
  have hG' : ∀ (j : ℤ) (w : SpatialCoordinates d), j ≤ (N : ℤ) →
      Draw N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) omega ≠ ⊤ →
      Z N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) omega < 1 →
      I.err w ((3 : ℝ) ^ (-j)) (by positivity)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w (by positivity))
          w ((3 : ℝ) ^ (-j)) (aux_in_deterministic_onestep_sref M H omega N j w) s 2 ≤
        Cg * (M.delta ^ 2 + eps ^ 8 +
          (Draw N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) omega).toReal) := by
    intro j w hj hD hZ
    have := hGω N j w hj hD hZ
    rw [hsN, ite_eq_left hj] at this
    exact this
  have hpreAll : ∀ (DA : ℕ) (dword : Fin DA → OddGridIndex d 1), k0 ≤ DA → DA ≤ horizon →
      k + DA ≤ N →
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
          Z N ((N : ℤ) - l).toNat
            (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside DA dword) omega < lambdaCut * DA ∧
      ∑ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
          (Draw N ((N : ℤ) - l).toNat
            (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside DA dword) omega).toReal <
        lambdaCut * DA := by
    intro DA dword hk0 hDAh hkDA
    have hlev : rootLevel qRoot + (DA : ℤ) ≤ (N : ℤ) := by rw [hrl]; omega
    obtain ⟨hZp, hDp⟩ := hev.1 qRoot DA hk0 hDAh hlev (Sum.inl dword)
    rw [hPrefixZ, ite_eq_left hlev, hobs, hrl] at hZp
    rw [hPrefixD, ite_eq_left hlev, hobs, hrl] at hDp
    constructor
    · refine lt_of_eq_of_lt ?_ hZp
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_Icc] at hj
      rw [ite_eq_left (by omega)]
    · refine lt_of_eq_of_lt ?_ hDp
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_Icc] at hj
      rw [ite_eq_left (by omega)]
  have hfinAll : ∀ (DA : ℕ) (dword : Fin DA → OddGridIndex d 1), k + DA ≤ N →
      ∀ l ∈ Finset.Icc ((k : ℤ) - cbuf) ((k : ℤ) + DA),
        Draw N ((N : ℤ) - l).toNat
          (((3 : ℝ) ^ N) • descendantCenter 1 qcenter qside DA dword) omega ≠ ⊤ := by
    intro DA dword hkDA l hl
    have hlev : rootLevel qRoot + (DA : ℤ) ≤ (N : ℤ) := by rw [hrl]; omega
    have := hFinω N qRoot DA (Sum.inl dword) hlev l (by rw [hrl]; exact hl)
    rwa [hobs] at this
  have hfN : 0 ≤ fNorm qp := div_nonneg ENNReal.toReal_nonneg
    (Real.rpow_nonneg measureReal_nonneg _)
  have hFq : (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (Metric.ball qcenter ((3 : ℝ) ^ ((1 : ℤ) - k) / 2)))).toReal =
      fNorm qp * ((3 * qside) ^ d) ^ (1 / ((d : ℝ) / (1 - alpha))) := by
    rw [h3q]
    show _ = (eLpNorm f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
        (volume.restrict (Metric.ball qcenter (3 * qside / 2)))).toReal /
        (volume.real (Metric.ball qcenter (3 * qside / 2))) ^ (1 / ((d : ℝ) / (1 - alpha))) *
        ((3 * qside) ^ d) ^ (1 / ((d : ℝ) / (1 - alpha)))
    rw [aux_in_deterministic_onestep_volume_qp qcenter qside hqpos]
    have hpos : 0 < ((3 * qside) ^ d) ^ (1 / ((d : ℝ) / (1 - alpha))) := by positivity
    rw [div_mul_cancel₀ _ hpos.ne']
  have hpadAll : k0 ≤ N - k → N - k + 1 ≤ horizon →
      ∀ pword : Fin (N - k + 1) → OddGridIndex d 1,
      Draw N 0 (((3 : ℝ) ^ N) • descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword) omega ≠ ⊤ ∧
      (Draw N 0 (((3 : ℝ) ^ N) •
        descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword) omega).toReal ≤
        lambdaCut * ((N - k + 1 : ℕ) : ℝ) := by
    intro hreg hDph pword
    have hrlp : rootLevel (padE, selfShift) = (k : ℤ) - 1 := by
      rw [hrootLevel, hpad]; push_cast; ring
    have hrsp : rootSide (padE, selfShift) = 3 * qside := by
      rw [hrootSide, hrlp, hqside, show -((k : ℤ) - 1) = 1 + -(k : ℤ) by ring,
        zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
    have hrcp : rootCentre (padE, selfShift) = qcenter := by
      rw [hrootCentre, hshift, smul_zero, add_zero]
    have hobsp : observationCentre (padE, selfShift) (N - k + 1) (Sum.inl pword) =
        descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword := by
      rw [hObservationCentre]; simp only [Sum.elim_inl]; rw [hrcp, hrsp]
    have hlevp : rootLevel (padE, selfShift) + ((N - k + 1 : ℕ) : ℤ) ≤ (N : ℤ) := by
      rw [hrlp]; omega
    obtain ⟨_, hDp⟩ := hev.1 (padE, selfShift) (N - k + 1) (by omega) hDph hlevp (Sum.inl pword)
    rw [hPrefixD, ite_eq_left hlevp, hobsp, hrlp] at hDp
    have hNmem : (N : ℤ) ∈ Finset.Icc ((k : ℤ) - 1 - (cbuf : ℤ))
        ((k : ℤ) - 1 + ((N - k + 1 : ℕ) : ℤ)) := by
      rw [Finset.mem_Icc]; constructor <;> omega
    have hfinp := hFinω N (padE, selfShift) (N - k + 1) (Sum.inl pword) hlevp (N : ℤ)
      (by rw [hrlp]; exact hNmem)
    rw [hobsp, sub_self, Int.toNat_zero] at hfinp
    refine ⟨hfinp, ?_⟩
    have hterm := Finset.single_le_sum (f := fun j : ℤ => if 0 ≤ (N : ℤ) - j then
        (Draw N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) •
          descendantCenter 1 qcenter (3 * qside) (N - k + 1) pword) omega).toReal else 0)
      (fun j _ => by
        show 0 ≤ (if 0 ≤ (N : ℤ) - j then _ else 0)
        split_ifs
        · exact ENNReal.toReal_nonneg
        · exact le_rfl) hNmem
    simp only [sub_self, le_refl, ite_true, Int.toNat_zero] at hterm
    exact hterm.trans hDp.le
  exact aux_in_deterministic_onestep_at_point2 d I alpha s halpha hs h theta Ceps Cdel E0
    hCeps hCdel hOS Cg (E0 / (2 * Cg)) C2 0 hCg.le hc0 hC20 hC2a hC2b hC2c hC2d hCsub
    C3 hE0 hC3card hC3eps hC3a hC3b
    M H omega N (eta N omega) (hEtaω N) hIRω eps heps
    (fun m y => F N m y omega) (fun m y => Praw N m y omega) (fun m y => Rraw N m y omega)
    (fun m y => Draw N m y omega) (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)
    (hPω N) hG' hcapE hdel0 hdel1 k cbuf k0 horizon hkN qside hqpos hqside qcenter
    lambdaCut lambdaDet hlam0 hlamlt hpreAll hfinAll Qcentre Qside hQside hqp f hf fL2 hfL2
    u hu U hU huU (sN N (k : ℤ) qcenter omega) (fNorm qp) (by rw [hsk]) hfN hFq hpadAll D hDh x hx
    (fun _ hc' => absurd hc' (by omega))

end SubdiffusiveProcess.Paper
end
end DeterministicRegularity_OneStep_Repaired

