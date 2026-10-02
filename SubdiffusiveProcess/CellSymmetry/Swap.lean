import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredPartialSum
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
import Mathlib.Tactic
import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.TestSubmodule
import SubdiffusiveProcess.Lane4.Inputs
import Mathlib.Analysis.Matrix.Normed
import SubdiffusiveProcess.Lane3.RelativeConcentration
import SubdiffusiveProcess.Sobolev.CompactResponses
import SubdiffusiveProcess.Main.CommonScaleLaw
import Mathlib.Probability.ProductMeasure
import SubdiffusiveProcess.Sobolev.ReflectionResponses
import SubdiffusiveProcess.Lane4.Scaling
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletMatrixBridge
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletInfimumCovariance
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import SubdiffusiveProcess.Sobolev.DomainPoincare
import SubdiffusiveProcess.CellSymmetry.MatrixLaw




open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators Pointwise ContDiff Distributions

noncomputable section
namespace SubdiffusiveProcess
namespace CellSymmetry


section
variable {d : ℕ}

/-- Transpose the coordinates `a, b` about the point `z`. -/
def cs_lc_swap (z : SpatialCoordinates d) (a b : Fin d) (x : SpatialCoordinates d) :
    SpatialCoordinates d :=
  fun i => z i + (x (Equiv.swap a b i) - z (Equiv.swap a b i))

theorem cs_lc_swap_involutive (z : SpatialCoordinates d) (a b : Fin d) :
    Function.Involutive (cs_lc_swap z a b) := by
  intro x
  funext i
  simp only [cs_lc_swap, Equiv.swap_apply_self]
  ring

theorem cs_lc_swap_continuous (z : SpatialCoordinates d) (a b : Fin d) :
    Continuous (cs_lc_swap z a b) :=
  continuous_pi fun _ => continuous_const.add ((continuous_apply _).sub continuous_const)

theorem cs_lc_swap_dist_le (z : SpatialCoordinates d) (a b : Fin d)
    (x y : SpatialCoordinates d) :
    dist (cs_lc_swap z a b x) (cs_lc_swap z a b y) ≤ dist x y := by
  refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
  have h : dist (cs_lc_swap z a b x i) (cs_lc_swap z a b y i) =
      dist (x (Equiv.swap a b i)) (y (Equiv.swap a b i)) := by
    simp only [cs_lc_swap, Real.dist_eq]
    congr 1
    ring
  rw [h]
  exact dist_le_pi_dist x y _

theorem cs_lc_swap_dist (z : SpatialCoordinates d) (a b : Fin d)
    (x y : SpatialCoordinates d) :
    dist (cs_lc_swap z a b x) (cs_lc_swap z a b y) = dist x y := by
  refine le_antisymm (cs_lc_swap_dist_le z a b x y) ?_
  have h := cs_lc_swap_dist_le z a b (cs_lc_swap z a b x)
    (cs_lc_swap z a b y)
  rwa [cs_lc_swap_involutive z a b x, cs_lc_swap_involutive z a b y] at h

/-- The swap as a homeomorphism of the spatial carrier. -/
def cs_lc_swapHomeo (z : SpatialCoordinates d) (a b : Fin d) :
    SpatialCoordinates d ≃ₜ SpatialCoordinates d where
  toFun := cs_lc_swap z a b
  invFun := cs_lc_swap z a b
  left_inv := cs_lc_swap_involutive z a b
  right_inv := cs_lc_swap_involutive z a b
  continuous_toFun := cs_lc_swap_continuous z a b
  continuous_invFun := cs_lc_swap_continuous z a b

theorem cs_lc_swap_self (z : SpatialCoordinates d) (a b : Fin d) :
    cs_lc_swap z a b z = z := by
  funext i
  simp [cs_lc_swap]

/-- The swap about the centre maps the centred cube onto itself. -/
theorem cs_lc_swap_preimage_cube (z : SpatialCoordinates d) (a b : Fin d)
    {r : ℝ} (hr : 0 < r) :
    cs_lc_swap z a b ⁻¹' (centeredCube z r hr : Set (SpatialCoordinates d)) =
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  ext x
  change dist (cs_lc_swap z a b x) z < r / 2 ↔ dist x z < r / 2
  have h := cs_lc_swap_dist z a b x z
  rw [cs_lc_swap_self] at h
  rw [h]

theorem cs_lc_swap_measurePreserving (z : SpatialCoordinates d) (a b : Fin d) :
    MeasurePreserving (cs_lc_swap z a b) volume volume := by
  have h1 : MeasurePreserving (fun x : SpatialCoordinates d => x - z) volume volume :=
    measurePreserving_sub_right volume z
  have h2 : MeasurePreserving
      (MeasurableEquiv.arrowCongr' (Equiv.swap a b) (MeasurableEquiv.refl ℝ) :
        SpatialCoordinates d → SpatialCoordinates d) volume volume :=
    volume_preserving_arrowCongr' _ _ (MeasurePreserving.id volume)
  have h3 : MeasurePreserving (fun x : SpatialCoordinates d => x + z) volume volume :=
    measurePreserving_add_right volume z
  have h := h3.comp (h2.comp h1)
  convert h using 1
  funext x
  funext i
  simp only [Function.comp_apply, MeasurableEquiv.arrowCongr', Equiv.arrowCongr',
    Equiv.arrowCongr, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, MeasurableEquiv.refl,
    Equiv.symm_swap, Pi.add_apply, Pi.sub_apply, cs_lc_swap]
  rw [add_comm]
  rfl

theorem cs_lc_swap_preimage_reverse (z : SpatialCoordinates d) (a b : Fin d)
    {U Ω : Opens (SpatialCoordinates d)}
    (hU : cs_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U) :
    cs_lc_swap z a b ⁻¹' (U : Set (SpatialCoordinates d)) = Ω := by
  ext x
  have h := Set.ext_iff.mp hU (cs_lc_swap z a b x)
  simpa only [mem_preimage, cs_lc_swap_involutive z a b x] using h.symm

theorem cs_lc_swap_domain_measurePreserving (z : SpatialCoordinates d) (a b : Fin d)
    {U Ω : Opens (SpatialCoordinates d)}
    (hU : cs_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U) :
    MeasurePreserving (cs_lc_swap z a b)
      (volume.restrict (U : Set (SpatialCoordinates d)))
      (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
  have h := (cs_lc_swap_measurePreserving z a b).restrict_preimage
    Ω.isOpen.measurableSet
  rwa [hU] at h

/-! ### Smooth calculus of the swap -/

/-- The derivative of the swap: permute the coordinates of the increment. -/
def cs_lc_swapDeriv (a b : Fin d) : SpatialCoordinates d →L[ℝ] SpatialCoordinates d :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Equiv.swap a b i)

theorem cs_lc_swapDeriv_single (a b : Fin d) (i : Fin d) :
    cs_lc_swapDeriv a b (Pi.single i 1) =
      (Pi.single (Equiv.swap a b i) 1 : SpatialCoordinates d) := by
  funext j
  simp only [cs_lc_swapDeriv, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.proj_apply]
  by_cases h : j = Equiv.swap a b i
  · subst h
    rw [Equiv.swap_apply_self, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne]
    intro h'
    apply h
    rw [← h', Equiv.swap_apply_self]

theorem cs_lc_swap_hasFDerivAt (z : SpatialCoordinates d) (a b : Fin d)
    (x : SpatialCoordinates d) :
    HasFDerivAt (cs_lc_swap z a b) (cs_lc_swapDeriv a b) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  change HasFDerivAt (fun y : SpatialCoordinates d => z i + (y (Equiv.swap a b i) -
    z (Equiv.swap a b i))) (ContinuousLinearMap.proj (Equiv.swap a b i)) x
  exact ((hasFDerivAt_apply (𝕜 := ℝ) (Equiv.swap a b i) x).sub_const _).const_add _

theorem cs_lc_swap_contDiff (z : SpatialCoordinates d) (a b : Fin d) :
    ContDiff ℝ ∞ (cs_lc_swap z a b) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_const.add ((contDiff_apply ℝ ℝ _).sub contDiff_const)

theorem cs_lc_fderiv_comp_swap (z : SpatialCoordinates d) (a b : Fin d)
    {f : SpatialCoordinates d → ℝ} (hf : ContDiff ℝ ∞ f)
    (x : SpatialCoordinates d) (i : Fin d) :
    fderiv ℝ (f ∘ cs_lc_swap z a b) x (Pi.single i 1) =
      fderiv ℝ f (cs_lc_swap z a b x) (Pi.single (Equiv.swap a b i) 1) := by
  rw [fderiv_comp x (hf.differentiable (by norm_num) _)
    (cs_lc_swap_hasFDerivAt z a b x).differentiableAt,
    (cs_lc_swap_hasFDerivAt z a b x).fderiv, ContinuousLinearMap.comp_apply,
    cs_lc_swapDeriv_single]

/-! ### Lp pullback -/

end

section
variable {d : ℕ}
variable {U Ω : Opens (SpatialCoordinates d)}

def cs_lc_swapLp (z : SpatialCoordinates d) (a b : Fin d)
    (hU : cs_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    Lp ℝ p (volume.restrict (Ω : Set (SpatialCoordinates d))) →ₗᵢ[ℝ]
      Lp ℝ p (volume.restrict (U : Set (SpatialCoordinates d))) :=
  Lp.compMeasurePreservingₗᵢ ℝ (cs_lc_swap z a b)
    (cs_lc_swap_domain_measurePreserving z a b hU)

theorem cs_lc_swapLp_coeFn (z : SpatialCoordinates d) (a b : Fin d)
    (hU : cs_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp ℝ p (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    (cs_lc_swapLp z a b hU f : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (U : Set (SpatialCoordinates d))] f ∘ cs_lc_swap z a b :=
  Lp.coeFn_compMeasurePreserving f (cs_lc_swap_domain_measurePreserving z a b hU)

theorem cs_lc_swapLp_inverse (z : SpatialCoordinates d) (a b : Fin d)
    (hU : cs_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp ℝ p (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    cs_lc_swapLp z a b (cs_lc_swap_preimage_reverse z a b hU)
      (cs_lc_swapLp z a b hU f) = f := by
  apply Lp.ext
  have hm := cs_lc_swap_domain_measurePreserving z a b
    (cs_lc_swap_preimage_reverse z a b hU)
  filter_upwards [cs_lc_swapLp_coeFn z a b
    (cs_lc_swap_preimage_reverse z a b hU) (cs_lc_swapLp z a b hU f),
    hm.quasiMeasurePreserving.ae_eq (cs_lc_swapLp_coeFn z a b hU f)] with x hx hy
  exact hx.trans (hy.trans (congrArg f (cs_lc_swap_involutive z a b x)))

/-! ### Smooth tests -/

def cs_lc_swapTest (z : SpatialCoordinates d) (a b : Fin d)
    (hU : cs_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (φ : 𝓓(Ω, ℝ)) : 𝓓(U, ℝ) where
  toFun := φ ∘ cs_lc_swap z a b
  contDiff' := φ.contDiff.comp (cs_lc_swap_contDiff z a b)
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (cs_lc_swapHomeo z a b)
  tsupport_subset' := by
    change tsupport (φ ∘ (cs_lc_swapHomeo z a b)) ⊆ U
    rw [tsupport_comp_eq_preimage]
    intro x hx
    rw [← hU]
    exact φ.tsupport_subset hx

theorem cs_lc_testL2_swapTest (z : SpatialCoordinates d) (a b : Fin d)
    (hU : cs_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (φ : 𝓓(Ω, ℝ)) :
    testL2 (cs_lc_swapTest z a b hU φ) = cs_lc_swapLp z a b hU (testL2 φ) := by
  apply Lp.ext
  have hm := cs_lc_swap_domain_measurePreserving z a b hU
  filter_upwards [testL2_coeFn (cs_lc_swapTest z a b hU φ),
    cs_lc_swapLp_coeFn z a b hU (testL2 φ),
    hm.quasiMeasurePreserving.ae_eq (testL2_coeFn φ)] with x hx hy hz
  exact hx.trans (hz.symm.trans hy.symm)

theorem cs_lc_testPartialL2_swapTest (z : SpatialCoordinates d) (a b : Fin d)
    (hU : cs_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (φ : 𝓓(Ω, ℝ)) (i : Fin d) :
    testPartialL2 (cs_lc_swapTest z a b hU φ) i =
      cs_lc_swapLp z a b hU (testPartialL2 φ (Equiv.swap a b i)) := by
  apply Lp.ext
  have hm := cs_lc_swap_domain_measurePreserving z a b hU
  filter_upwards [testPartialL2_coeFn (cs_lc_swapTest z a b hU φ) i,
    cs_lc_swapLp_coeFn z a b hU (testPartialL2 φ (Equiv.swap a b i)),
    hm.quasiMeasurePreserving.ae_eq (testPartialL2_coeFn φ (Equiv.swap a b i))]
    with x hx hy hz
  simp only [Function.comp_apply] at hy hz
  rw [hx, hy, hz]
  exact cs_lc_fderiv_comp_swap z a b φ.contDiff x i

/-! ### Sobolev graphs -/

def cs_lc_swapSobolevData (z : SpatialCoordinates d) (a b : Fin d)
    (hU : cs_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U) :
    SobolevData Ω →L[ℝ] SobolevData U :=
  ((cs_lc_swapLp z a b hU).toContinuousLinearMap.comp
      (ContinuousLinearMap.fst ℝ _ _)).prod
    (ContinuousLinearMap.pi fun i =>
      ((cs_lc_swapLp z a b hU).toContinuousLinearMap.comp
        ((ContinuousLinearMap.proj (Equiv.swap a b i)).comp (ContinuousLinearMap.snd ℝ _ _))))

theorem cs_lc_swapSobolevData_smooth (z : SpatialCoordinates d) (a b : Fin d)
    (hU : cs_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (φ : 𝓓(Ω, ℝ)) :
    cs_lc_swapSobolevData z a b hU (smoothSobolevData φ) =
      smoothSobolevData (cs_lc_swapTest z a b hU φ) := by
  apply Prod.ext
  · exact (cs_lc_testL2_swapTest z a b hU φ).symm
  · funext i
    exact (cs_lc_testPartialL2_swapTest z a b hU φ i).symm

theorem cs_lc_swapSobolevData_mem_killed (z : SpatialCoordinates d) (a b : Fin d)
    (hU : cs_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    {u : SobolevData Ω} (hu : u ∈ killedSobolevGraph Ω) :
    cs_lc_swapSobolevData z a b hU u ∈ killedSobolevGraph U := by
  have hm : Set.MapsTo (cs_lc_swapSobolevData z a b hU)
      (Set.range (smoothSobolevData (Ω := Ω)))
      (killedSobolevGraph U : Set (SobolevData U)) := by
    rintro v ⟨φ, rfl⟩
    rw [cs_lc_swapSobolevData_smooth]
    exact smoothSobolevData_mem_killed _
  apply hm.closure_left (cs_lc_swapSobolevData z a b hU).continuous
    (isClosed_killedSobolevGraph (Ω := U))
  rw [← killedSobolevGraph_coe_eq_closure]
  exact hu

theorem cs_lc_swapSobolevData_inverse (z : SpatialCoordinates d) (a b : Fin d)
    (hU : cs_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (u : SobolevData Ω) :
    cs_lc_swapSobolevData z a b (cs_lc_swap_preimage_reverse z a b hU)
      (cs_lc_swapSobolevData z a b hU u) = u := by
  apply Prod.ext
  · exact cs_lc_swapLp_inverse z a b hU u.1
  · funext i
    change cs_lc_swapLp z a b (cs_lc_swap_preimage_reverse z a b hU)
      (cs_lc_swapLp z a b hU (u.2 (Equiv.swap a b (Equiv.swap a b i)))) = u.2 i
    rw [Equiv.swap_apply_self, cs_lc_swapLp_inverse]

def cs_lc_swapKilledEquiv (z : SpatialCoordinates d) (a b : Fin d)
    (hU : cs_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U) :
    killedSobolevGraph Ω ≃ killedSobolevGraph U where
  toFun u := ⟨cs_lc_swapSobolevData z a b hU u.val,
    cs_lc_swapSobolevData_mem_killed z a b hU u.property⟩
  invFun u := ⟨cs_lc_swapSobolevData z a b
      (cs_lc_swap_preimage_reverse z a b hU) u.val,
    cs_lc_swapSobolevData_mem_killed z a b
      (cs_lc_swap_preimage_reverse z a b hU) u.property⟩
  left_inv u := Subtype.ext (cs_lc_swapSobolevData_inverse z a b hU u.val)
  right_inv u := Subtype.ext (cs_lc_swapSobolevData_inverse z a b
    (cs_lc_swap_preimage_reverse z a b hU) u.val)

/-! ### Coefficients and energies -/

def cs_lc_swapCoefficient (z : SpatialCoordinates d) (a b : Fin d)
    (hU : cs_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (c : PositiveCoefficient Ω) : PositiveCoefficient U := by
  refine ⟨cs_lc_swapLp z a b hU c.val, ?_⟩
  obtain ⟨e, he, hc⟩ := c.property
  refine ⟨e, he, ?_⟩
  have hm := cs_lc_swap_domain_measurePreserving z a b hU
  filter_upwards [cs_lc_swapLp_coeFn z a b hU c.val,
    hm.quasiMeasurePreserving.ae hc] with x hx hy
  exact hx.symm ▸ hy

theorem cs_lc_swapCoefficient_coeFn (z : SpatialCoordinates d) (a b : Fin d)
    (hU : cs_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (c : PositiveCoefficient Ω) :
    ((cs_lc_swapCoefficient z a b hU c).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (U : Set (SpatialCoordinates d))] c.val ∘ cs_lc_swap z a b :=
  cs_lc_swapLp_coeFn z a b hU c.val

theorem cs_lc_swapSobolevData_gradient_coeFn (z : SpatialCoordinates d) (a b : Fin d)
    (hU : cs_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (u : SobolevData Ω) (i : Fin d) :
    ((cs_lc_swapSobolevData z a b hU u).2 i : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (U : Set (SpatialCoordinates d))]
      fun x => u.2 (Equiv.swap a b i) (cs_lc_swap z a b x) :=
  cs_lc_swapLp_coeFn z a b hU (u.2 (Equiv.swap a b i))

/-- Swapping the domain, coefficient, variation and slope preserves the affine objective. -/
theorem cs_lc_affineDirichletObjective_swap (z : SpatialCoordinates d) (a b : Fin d)
    (hU : cs_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (c : PositiveCoefficient Ω) (p : Fin d → ℝ) (u : SobolevData Ω) :
    (∑ i : Fin d, ∫ x in (U : Set (SpatialCoordinates d)),
      (cs_lc_swapCoefficient z a b hU c).val x *
        (p (Equiv.swap a b i) + (cs_lc_swapSobolevData z a b hU u).2 i x) ^ 2) =
    ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
      c.val x * (p i + u.2 i x) ^ 2 := by
  have hterm : ∀ i : Fin d, (∫ x in (U : Set (SpatialCoordinates d)),
      (cs_lc_swapCoefficient z a b hU c).val x *
        (p (Equiv.swap a b i) + (cs_lc_swapSobolevData z a b hU u).2 i x) ^ 2) =
      ∫ x in (Ω : Set (SpatialCoordinates d)),
        c.val x * (p (Equiv.swap a b i) + u.2 (Equiv.swap a b i) x) ^ 2 := by
    intro i
    calc
      _ = ∫ x in (U : Set (SpatialCoordinates d)),
          c.val (cs_lc_swap z a b x) *
            (p (Equiv.swap a b i) + u.2 (Equiv.swap a b i) (cs_lc_swap z a b x)) ^ 2 := by
        apply integral_congr_ae
        filter_upwards [cs_lc_swapCoefficient_coeFn z a b hU c,
          cs_lc_swapSobolevData_gradient_coeFn z a b hU u i] with x hc hu
        rw [hc, hu, Function.comp_apply]
      _ = _ := (cs_lc_swap_domain_measurePreserving z a b hU).integral_comp
        (cs_lc_swapHomeo z a b).measurableEmbedding
        (fun y => c.val y * (p (Equiv.swap a b i) + u.2 (Equiv.swap a b i) y) ^ 2)
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  exact Fintype.sum_equiv (Equiv.swap a b) _ _ fun i => rfl

end

section
variable {d : ℕ}
variable {U Ω : Opens (SpatialCoordinates d)}
variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
variable [IsFiniteMeasure (volume.restrict (U : Set (SpatialCoordinates d)))]

/-- The affine Dirichlet minimum is unchanged by swapping domain, coefficient and slope. -/
theorem cs_lc_affineDirichletResponse_swap (z : SpatialCoordinates d) (a b : Fin d)
    (hU : cs_lc_swap z a b ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hUb : Bornology.IsBounded (U : Set (SpatialCoordinates d)))
    (hD : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) u‖)
    (hDU : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph U,
      ‖(u : SobolevData U).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph U) u‖)
    (c : PositiveCoefficient Ω) (p : Fin d → ℝ) :
    affineDirichletResponse hUb hDU (cs_lc_swapCoefficient z a b hU c)
      (p ∘ Equiv.swap a b) = affineDirichletResponse hΩ hD c p := by
  let f : killedSobolevGraph U → ℝ := fun u =>
    ∑ i : Fin d, ∫ x in (U : Set (SpatialCoordinates d)),
      (cs_lc_swapCoefficient z a b hU c).val x *
        ((p ∘ Equiv.swap a b) i + (u : SobolevData U).2 i x) ^ 2
  have he : Set.range f = Set.range (fun u : killedSobolevGraph Ω =>
      ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
        c.val x * (p i + (u : SobolevData Ω).2 i x) ^ 2) := by
    rw [← (cs_lc_swapKilledEquiv z a b hU).surjective.range_comp f]
    congr 1
    funext u
    exact cs_lc_affineDirichletObjective_swap z a b hU c p u.val
  apply (affineDirichletResponse_isLeast hUb hDU
    (cs_lc_swapCoefficient z a b hU c) (p ∘ Equiv.swap a b)).unique
  change IsLeast (Set.range f) _
  rw [he]
  exact affineDirichletResponse_isLeast hΩ hD c p

end
end CellSymmetry
end SubdiffusiveProcess
