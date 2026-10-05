module

public import SubdiffusiveProcess.CoarseGrainingVocab.DykhneFiniteVolume
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Homogenization.Sobolev.W1p.Dilation
public import Homogenization.Sobolev.W1p.GlobalMollifierLp
public import Homogenization.Sobolev.W1p.GlobalAffineLp
public import Homogenization.Sobolev.PotentialSolenoidalExact
public import Homogenization.Sobolev.Foundations.H10Graph

@[expose] public section

/-!
# The weak planar de Rham theorem on a centered cube

`SubdiffusiveProcess/CoarseGrainingVocab/DykhneFiniteVolume.lean` isolates two planar
Poincare-lemma predicates on a domain `U ⊆ ℝ²`:

* `PlanarStreamFunctionOn U` — every `L²` field that is weakly divergence free
  (orthogonal to all `H¹₀` gradients) has a quarter-turned `H¹` potential;
* `PlanarZeroNormalStreamFunctionOn U` — every `L²` field that is weakly
  divergence free *with zero normal trace* (orthogonal to all `H¹` gradients)
  has a quarter-turned `H¹₀` potential.

The second one is what the Dykhne argument consumes; this module proves it on every
centered open cube, in three stages.

1. **Boundary half (Hilbert-space algebra).**
   `planarZeroNormalStreamFunctionOn_of_planarStreamFunctionOn` shows that on a
   bounded open convex domain the zero-trace converse follows from the interior
   one.  For `g` orthogonal to all `H¹` gradients and `s` orthogonal to all
   `H¹₀` gradients, `⟪s, Rg⟫ = -⟪Rs, g⟫ = 0` because `Rs` is an `H¹` gradient;
   hence `Rg` lies in the double orthogonal complement of the zero-trace
   potential submodule, which is closed by
   `H10GraphClosed.isClosed_range_gradientCLM` together with
   `exists_h10Function_of_mem_h10GraphClosedSubmodule`.  No boundary regularity
   beyond the closed-range `H¹₀` theorem is used.

2. **Smooth interior Poincare lemma.**
   `isPotentialOn_rot_of_differentiable_of_div_eq_zero` upgrades Mathlib's
   `Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric` (primitives of closed
   `1`-forms on convex sets) to the repository's `H¹` vocabulary: a `C¹` field
   that is divergence free on an open convex neighbourhood of `closure U` has a
   quarter-turned `H¹(U)` potential.  The primitive is cut off inside that
   neighbourhood so that `H1Function.ofContDiff` applies.

3. **Mollification.**  The zero extension of a weakly solenoidal `L²` field is
   mollified and contracted towards the centre of the cube; the contraction
   keeps the mollification ball inside `U`, so the smooth field is classically
   divergence free on a neighbourhood of `closure U` and stage 2 applies.  The
   approximants converge in `L²(U)` by the `CoarseGraining` mollifier and
   affine-expansion estimates, and the literal `H¹` potential submodule is
   closed by the Hodge converse criterion on convex domains, so the limit is
   itself a potential.

there is no planar duality argument in `Algsuperdiff`; the
orthogonal-complement bookkeeping mirrors the closed-range realization argument
of `Homogenization/Sobolev/PotentialSolenoidalL2Realization.lean`, and the
mollification geometry mirrors
`Homogenization/Sobolev/W1p/InwardMollificationGeometry.lean`.
-/
namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization
open scoped Convolution Pointwise ENNReal

noncomputable section

/-- The quarter turn is skew adjoint for the Euclidean pairing. -/
private theorem vecDot_planarQuarterTurn_left (v w : Vec 2) :
    vecDot (matVecMul planarQuarterTurn v) w =
      -vecDot v (matVecMul planarQuarterTurn w) := by
  simp [vecDot, planarQuarterTurn_mulVec, Fin.sum_univ_two]

/-- On a bounded open convex domain the literal zero-trace potential submodule
of `L²(U; ℝᵈ)` is closed: it is exactly the range of the gradient projection
from the closed `H¹₀` graph. -/
private theorem isClosed_potentialZeroTrace {d : ℕ} [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) :
    IsClosed ((PotentialSolenoidalExact.potentialZeroTrace U :
      Submodule ℝ (HilbertVectorL2 U)) : Set (HilbertVectorL2 U)) := by
  have hrange :
      ((PotentialSolenoidalExact.potentialZeroTrace U :
        Submodule ℝ (HilbertVectorL2 U)) : Set (HilbertVectorL2 U)) =
        Set.range (H10GraphClosed.gradientCLM (d := d) (U := U)) := by
    ext G
    constructor
    · intro hG
      obtain ⟨u, hu⟩ := (PotentialSolenoidalExact.mem_potentialZeroTrace_iff G).1 hG
      refine ⟨⟨(u.toH1Function.toScalarL2, u.toH1Function.gradToHilbertVectorL2),
        (Submodule.le_topologicalClosure _) (h10_pair_mem_h10GraphSubmodule u)⟩, ?_⟩
      exact hu
    · rintro ⟨z, rfl⟩
      obtain ⟨u, -, hgrad⟩ :=
        exists_h10Function_of_mem_h10GraphClosedSubmodule (U := U) hU z.2
      exact (PotentialSolenoidalExact.mem_potentialZeroTrace_iff _).2 ⟨u, hgrad⟩
  rw [hrange]
  exact H10GraphClosed.isClosed_range_gradientCLM (U := U) hU

/-- A representative vector field of an `L²` class in the Hilbert-vector
carrier. -/
private def vecFieldOfHilbertVectorL2 {d : ℕ} {U : Set (Vec d)}
    (s : HilbertVectorL2 U) : Vec d → Vec d :=
  fun x => (hilbertVectorL2ToVectorL2 (U := U) s) x

private theorem memVectorL2_vecFieldOfHilbertVectorL2 {d : ℕ} {U : Set (Vec d)}
    (s : HilbertVectorL2 U) :
    MemVectorL2 U (vecFieldOfHilbertVectorL2 s) :=
  MeasureTheory.Lp.memLp _

private theorem toHilbertVectorL2OfVecField_vecFieldOfHilbertVectorL2
    {d : ℕ} {U : Set (Vec d)} (s : HilbertVectorL2 U) :
    toHilbertVectorL2OfVecField (memVectorL2_vecFieldOfHilbertVectorL2 s) = s := by
  have h :=
    vectorL2ToHilbertVectorL2_toVectorL2 (U := U)
      (memVectorL2_vecFieldOfHilbertVectorL2 s)
  rw [← h]
  have hto :
      toVectorL2 (memVectorL2_vecFieldOfHilbertVectorL2 s) =
        hilbertVectorL2ToVectorL2 (U := U) s :=
    MeasureTheory.Lp.toLp_coeFn _ _
  rw [hto]
  exact vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2 (U := U) s

/-- **Boundary half of the planar de Rham theorem.**  On a bounded open convex
planar domain the zero-normal stream-function converse follows from the
interior one: no boundary regularity beyond the closed-range `H¹₀` theorem is
needed. -/
theorem planarZeroNormalStreamFunctionOn_of_planarStreamFunctionOn
    {U : Set (Vec 2)} (hU : IsOpenBoundedConvexDomain U)
    (hstream : PlanarStreamFunctionOn U) :
    PlanarZeroNormalStreamFunctionOn U := by
  intro g hgMem hg
  have hRgMem : MemVectorL2 U (fun x => matVecMul planarQuarterTurn (g x)) :=
    memVectorL2_planarQuarterTurn hgMem
  set K : Submodule ℝ (HilbertVectorL2 U) :=
    PotentialSolenoidalExact.potentialZeroTrace U
  have : CompleteSpace K := (isClosed_potentialZeroTrace (d := 2) hU).completeSpace_coe
  -- The rotated field is orthogonal to every weakly solenoidal field.
  have horth : toHilbertVectorL2OfVecField hRgMem ∈ Kᗮᗮ := by
    rw [Submodule.mem_orthogonal]
    intro s hs
    set sf : Vec 2 → Vec 2 := vecFieldOfHilbertVectorL2 s
    have hsfMem : MemVectorL2 U sf := memVectorL2_vecFieldOfHilbertVectorL2 s
    have hsEq : toHilbertVectorL2OfVecField hsfMem = s :=
      toHilbertVectorL2OfVecField_vecFieldOfHilbertVectorL2 s
    -- `s` is weakly solenoidal.
    have hsol : IsSolenoidalOn U sf := by
      intro φ
      have hmem : φ.toH1Function.gradToHilbertVectorL2 ∈ K :=
        (PotentialSolenoidalExact.mem_potentialZeroTrace_iff _).2 ⟨φ, rfl⟩
      have hinner :
          inner ℝ s φ.toH1Function.gradToHilbertVectorL2 = 0 :=
        (Submodule.mem_orthogonal' _ _).1 hs _ hmem
      rw [← hsEq] at hinner
      rw [← inner_toHilbertVectorL2OfVecField_eq_integral hsfMem
        φ.toH1Function.grad_memVectorL2]
      exact hinner
    -- The interior Poincare lemma gives a quarter-turned `H¹` potential.
    obtain ⟨v, hv⟩ := hstream hsfMem hsol
    have hinner :
        inner ℝ s (toHilbertVectorL2OfVecField hRgMem) =
          ∫ x in U, vecDot (sf x) (matVecMul planarQuarterTurn (g x))
            ∂MeasureTheory.volume := by
      rw [← hsEq, inner_toHilbertVectorL2OfVecField_eq_integral hsfMem hRgMem]
    rw [hinner]
    have hpt :
        ∀ x, vecDot (sf x) (matVecMul planarQuarterTurn (g x)) =
          -vecDot (g x) (v.grad x) := by
      intro x
      have hrot : v.grad x = matVecMul planarQuarterTurn (sf x) := by
        rw [hv]
      rw [hrot, ← vecDot_planarQuarterTurn_left]
      exact vecDot_comm _ _
    calc
      ∫ x in U, vecDot (sf x) (matVecMul planarQuarterTurn (g x))
          ∂MeasureTheory.volume =
          ∫ x in U, -vecDot (g x) (v.grad x) ∂MeasureTheory.volume := by
            exact MeasureTheory.integral_congr_ae
              (Filter.Eventually.of_forall fun x => hpt x)
      _ = -∫ x in U, vecDot (g x) (v.grad x) ∂MeasureTheory.volume :=
            MeasureTheory.integral_neg _
      _ = 0 := by rw [hg v]; simp
  rw [Submodule.orthogonal_orthogonal] at horth
  obtain ⟨u, hu⟩ := (PotentialSolenoidalExact.mem_potentialZeroTrace_iff _).1 horth
  have hae :
      u.toH1Function.grad =ᵐ[MeasureTheory.volume.restrict U]
        fun x => matVecMul planarQuarterTurn (g x) := by
    have hiff :=
      (toHilbertVectorL2_eq_toHilbertVectorL2_iff
        (memHilbertVectorL2_hilbertifyVecField u.toH1Function.grad_memVectorL2)
        (memHilbertVectorL2_hilbertifyVecField hRgMem)).1 hu
    filter_upwards [hiff] with x hx
    have hx' :
        HilbertVec.ofVec (u.toH1Function.grad x) =
          HilbertVec.ofVec (matVecMul planarQuarterTurn (g x)) := hx
    simpa using congrArg HilbertVec.toVec hx'
  exact IsPotentialZeroTraceOn.congr_ae hae u.isPotentialZeroTraceOn

/-- The Euclidean pairing as a continuous linear map into the dual. -/
private def dotCLM (d : ℕ) : Vec d →L[ℝ] (Vec d →L[ℝ] ℝ) :=
  ∑ i : Fin d,
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).smulRight
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i)

private theorem dotCLM_apply {d : ℕ} (v w : Vec d) : dotCLM d v w = vecDot v w := by
  simp [dotCLM, vecDot]

/-- Coordinate decomposition of a planar vector. -/
private theorem vec_two_eq (x : Vec 2) : x = x 0 • basisVec 0 + x 1 • basisVec 1 := by
  funext i
  fin_cases i <;> simp [basisVec]

/-- The `1`-form dual to a vector field. -/
private def dualForm (F : Vec 2 → Vec 2) : Vec 2 → (Vec 2 →L[ℝ] ℝ) := fun x => dotCLM 2 (F x)

private theorem hasFDerivAt_dualForm {F : Vec 2 → Vec 2} {a : Vec 2} {A : Vec 2 →L[ℝ] Vec 2}
    (hF : HasFDerivAt F A a) :
    HasFDerivAt (dualForm F) ((dotCLM 2).comp A) a :=
  (dotCLM 2).hasFDerivAt.comp a hF

private theorem fderiv_dualForm_apply {F : Vec 2 → Vec 2} {a : Vec 2}
    (hF : DifferentiableAt ℝ F a) (x y : Vec 2) :
    fderiv ℝ (dualForm F) a x y = vecDot (fderiv ℝ F a x) y := by
  rw [(hasFDerivAt_dualForm hF.hasFDerivAt).fderiv]
  simp [dotCLM_apply]

private theorem fderiv_rot {G : Vec 2 → Vec 2} {a : Vec 2} (hG : DifferentiableAt ℝ G a)
    (x : Vec 2) :
    fderiv ℝ (fun z => matVecMul planarQuarterTurn (G z)) a x =
      matVecMul planarQuarterTurn (fderiv ℝ G a x) := by
  have h : HasFDerivAt (fun z => matVecMul planarQuarterTurn (G z))
      ((matContinuousLinearMap planarQuarterTurn).comp (fderiv ℝ G a)) a := by
    simpa using (matContinuousLinearMap planarQuarterTurn).hasFDerivAt.comp a hG.hasFDerivAt
  rw [h.fderiv]
  simp

private theorem vecDot_fderiv_rot_symm {G : Vec 2 → Vec 2} {a : Vec 2}
    (hG : DifferentiableAt ℝ G a)
    (hdiv : (fderiv ℝ G a (basisVec 0)) 0 + (fderiv ℝ G a (basisVec 1)) 1 = 0)
    (x y : Vec 2) :
    vecDot (fderiv ℝ (fun z => matVecMul planarQuarterTurn (G z)) a x) y =
      vecDot (fderiv ℝ (fun z => matVecMul planarQuarterTurn (G z)) a y) x := by
  have hcoord : ∀ (z : Vec 2) (i : Fin 2),
      fderiv ℝ G a z i =
        z 0 * fderiv ℝ G a (basisVec 0) i + z 1 * fderiv ℝ G a (basisVec 1) i := by
    intro z i
    conv_lhs => rw [vec_two_eq z]
    simp
  rw [fderiv_rot hG, fderiv_rot hG]
  simp only [vecDot, planarQuarterTurn_mulVec, Fin.sum_univ_two, ite_true,
    ite_eq_right (by decide : ¬((1 : Fin 2) = 0))]
  rw [hcoord x 0, hcoord x 1, hcoord y 0, hcoord y 1]
  linear_combination (x 1 * y 0 - x 0 * y 1) * hdiv

private theorem differentiable_rot {G : Vec 2 → Vec 2} (hG : Differentiable ℝ G) :
    Differentiable ℝ (fun z => matVecMul planarQuarterTurn (G z)) := by
  intro z
  simpa using (matContinuousLinearMap planarQuarterTurn).differentiableAt.comp z (hG z)

/-- Poincare lemma for planar divergence-free `C¹` fields on an open convex set. -/
private theorem exists_hasFDerivAt_rot_of_div_eq_zero {V : Set (Vec 2)}
    (hV : Convex ℝ V) (hVopen : IsOpen V)
    {G : Vec 2 → Vec 2} (hG : Differentiable ℝ G)
    (hdiv : ∀ a ∈ V, (fderiv ℝ G a (basisVec 0)) 0 + (fderiv ℝ G a (basisVec 1)) 1 = 0) :
    ∃ psi : Vec 2 → ℝ, ∀ a ∈ V,
      HasFDerivAt psi (dualForm (fun x => matVecMul planarQuarterTurn (G x)) a) a := by
  have hRG : Differentiable ℝ (fun z => matVecMul planarQuarterTurn (G z)) :=
    differentiable_rot hG
  refine hV.exists_forall_hasFDerivAt_of_fderiv_symmetric hVopen ?_ ?_
  · intro a _
    exact ((hasFDerivAt_dualForm (hRG a).hasFDerivAt).differentiableAt).differentiableWithinAt
  · intro a ha x y
    rw [fderiv_dualForm_apply (hRG a) x y, fderiv_dualForm_apply (hRG a) y x]
    exact vecDot_fderiv_rot_symm (hG a) (hdiv a ha) x y

private theorem isPotentialOn_congr_on {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U)
    {f g : Vec d → Vec d} (hfg : ∀ x ∈ U, f x = g x) (hf : IsPotentialOn U f) :
    IsPotentialOn U g := by
  obtain ⟨u, rfl⟩ := hf
  refine ⟨{ toFun := u.toFun
            grad := g
            memL2 := u.memL2
            gradMemL2 := ?_
            hasWeakGradient := ?_ }, rfl⟩
  · intro i
    have hae : (fun x => u.grad x i) =ᵐ[MeasureTheory.volume.restrict U] fun x => g x i := by
      filter_upwards [MeasureTheory.ae_restrict_mem hU] with x hx
      rw [hfg x hx]
    exact (u.gradMemL2 i).ae_eq hae
  · intro i φ hφ hφ_supp hφ_sub
    rw [u.hasWeakGradient i φ hφ hφ_supp hφ_sub]
    congr 1
    refine MeasureTheory.setIntegral_congr_fun hU ?_
    intro x hx
    simp only [hfg x hx]

/-- Smooth planar Poincare lemma in repository vocabulary: a `C¹` field that is
divergence free on an open convex neighbourhood `V` of the closure of `U` has a
quarter-turned `H¹(U)` potential. -/
theorem isPotentialOn_rot_of_differentiable_of_div_eq_zero
    {U V W : Set (Vec 2)} (hU : IsOpenBoundedConvexDomain U)
    (hV : Convex ℝ V) (hVopen : IsOpen V)
    (hW : IsOpen W) (hUW : U ⊆ W) (hWV : W ⊆ V)
    {chi : Vec 2 → ℝ} (hchi : ContDiff ℝ (⊤ : ℕ∞) chi) (hchi_supp : HasCompactSupport chi)
    (hchi_tsupp : tsupport chi ⊆ V) (hchi_one : ∀ x ∈ W, chi x = 1)
    {G : Vec 2 → Vec 2} (hG : Differentiable ℝ G) (hGcont : Continuous G)
    (hdiv : ∀ a ∈ V, (fderiv ℝ G a (basisVec 0)) 0 + (fderiv ℝ G a (basisVec 1)) 1 = 0) :
    IsPotentialOn U (fun x => matVecMul planarQuarterTurn (G x)) := by
  classical
  obtain ⟨psi, hpsi⟩ := exists_hasFDerivAt_rot_of_div_eq_zero hV hVopen hG hdiv
  set F : Vec 2 → Vec 2 := fun x => matVecMul planarQuarterTurn (G x) with hF
  have hFcont : Continuous F := by
    simpa [hF] using! (matContinuousLinearMap planarQuarterTurn).continuous.comp hGcont
  have hdualCont : Continuous (dualForm F) := (dotCLM 2).continuous.comp hFcont
  set psit : Vec 2 → ℝ := fun x => chi x * psi x with hpsit
  have hpsiAt : ∀ a ∈ V, ContDiffAt ℝ 1 psi a := by
    intro a ha
    have h : ContDiffAt ℝ ((0 : ℕ) + 1) psi a := by
      rw [contDiffAt_succ_iff_hasFDerivAt]
      exact ⟨dualForm F, ⟨V, hVopen.mem_nhds ha, fun y hy => hpsi y hy⟩,
        (contDiff_zero.2 hdualCont).contDiffAt⟩
    simpa using h
  have hC1 : ContDiff ℝ 1 psit := by
    rw [contDiff_iff_contDiffAt]
    intro a
    by_cases ha : a ∈ V
    · exact (hchi.contDiffAt.of_le (by simp)).mul (hpsiAt a ha)
    · have hout : a ∉ tsupport chi := fun h => ha (hchi_tsupp h)
      have hchi0 : chi =ᶠ[nhds a] 0 := notMem_tsupport_iff_eventuallyEq.mp hout
      have hzero : psit =ᶠ[nhds a] fun _ => (0 : ℝ) := by
        filter_upwards [hchi0] with y hy
        simp [hpsit, show chi y = 0 from hy]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  have hsupp : HasCompactSupport psit := hchi_supp.mul_right
  have hpot : IsPotentialOn U (fun x i => (fderiv ℝ psit x) (basisVec i)) :=
    (H1Function.ofContDiff hU.isOpen hC1 hsupp).isPotentialOn
  refine isPotentialOn_congr_on hU.isOpen.measurableSet ?_ hpot
  intro x hx
  have hEq : psit =ᶠ[nhds x] psi := by
    filter_upwards [hW.mem_nhds (hUW hx)] with y hy
    simp [hpsit, hchi_one y hy]
  have hfd : fderiv ℝ psit x = dualForm F x := by
    rw [hEq.fderiv_eq]
    exact (hpsi x (hWV (hUW hx))).fderiv
  funext i
  rw [hfd]
  simpa [dualForm, dotCLM_apply] using vecDot_basisVec_right (F x) i

/-- Zero extension of a field defined on `U`. -/
private def zeroExt (U : Set (Vec 2)) (g : Vec 2 → Vec 2) : Vec 2 → Vec 2 :=
  Set.indicator U g

private theorem memLp_zeroExt_coord {U : Set (Vec 2)} (hU : MeasurableSet U)
    {g : Vec 2 → Vec 2} (hg : MemVectorL2 U g) (i : Fin 2) :
    MemLp (fun x => zeroExt U g x i) 2 volume := by
  have h : (fun x => zeroExt U g x i) = Set.indicator U (fun x => g x i) := by
    funext x
    by_cases hx : x ∈ U <;> simp [zeroExt, hx]
  rw [h, memLp_indicator_iff_restrict hU]
  exact memScalarL2_coord_of_memVectorL2 hg i

private theorem locallyIntegrable_zeroExt_coord {U : Set (Vec 2)} (hU : MeasurableSet U)
    {g : Vec 2 → Vec 2} (hg : MemVectorL2 U g) (i : Fin 2) :
    LocallyIntegrable (fun x => zeroExt U g x i) volume :=
  (memLp_zeroExt_coord hU hg i).locallyIntegrable (by norm_num)

/-- The mollification of a weakly divergence-free `L²` field is classically
divergence free at every point whose mollification ball stays inside `U`. -/
private theorem sum_fderiv_convolution_eq_zero
    {U : Set (Vec 2)} (hUopen : IsOpen U)
    {g : Vec 2 → Vec 2} (hgMem : MemVectorL2 U g) (hgsol : IsSolenoidalOn U g)
    {k : Vec 2 → ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hksupp : HasCompactSupport k)
    {y : Vec 2} {t : ℝ}
    (hkball : tsupport k ⊆ Metric.closedBall (0 : Vec 2) t)
    (hball : Metric.closedBall y t ⊆ U) :
    ∑ i : Fin 2,
      (fderiv ℝ (fun z => (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (fun w => zeroExt U g w i)) z) y) (basisVec i) = 0 := by
  classical
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  set L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ with hL
  set fi : Fin 2 → Vec 2 → ℝ := fun i w => zeroExt U g w i with hfi
  have hloc : ∀ i, LocallyIntegrable (fi i) volume := fun i =>
    locallyIntegrable_zeroExt_coord hUmeas hgMem i
  have hk1 : ContDiff ℝ 1 k := hk.of_le (by simp)
  have hdk_cont : Continuous (fderiv ℝ k) := hk1.continuous_fderiv one_ne_zero
  have hdk_supp : HasCompactSupport (fderiv ℝ k) := hksupp.fderiv ℝ
  -- the test function
  set φ : Vec 2 → ℝ := fun z => k (y - z) with hφ
  have haff : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec 2 => y - z) := by
    fun_prop
  have hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ := hk.comp haff
  have hφ_fderiv : ∀ z v, (fderiv ℝ φ z) v = -((fderiv ℝ k (y - z)) v) := by
    intro z v
    have hin : HasFDerivAt (fun z : Vec 2 => y - z) (-ContinuousLinearMap.id ℝ (Vec 2)) z := by
      simpa using (hasFDerivAt_const (𝕜 := ℝ) y z).sub (hasFDerivAt_id (𝕜 := ℝ) z)
    have h : HasFDerivAt φ ((fderiv ℝ k (y - z)).comp (-ContinuousLinearMap.id ℝ (Vec 2))) z :=
      (hk1.differentiable one_ne_zero (y - z)).hasFDerivAt.comp z hin
    rw [h.fderiv]
    simp
  have hφ_tsupport : tsupport φ ⊆ Metric.closedBall y t := by
    have hpre : tsupport φ ⊆ (fun z : Vec 2 => y - z) ⁻¹' (tsupport k) := by
      refine closure_minimal ?_ ((isClosed_tsupport k).preimage (by fun_prop))
      intro z hz
      exact subset_tsupport k hz
    intro z hz
    have hzk : y - z ∈ tsupport k := hpre hz
    have := hkball hzk
    rw [Metric.mem_closedBall, dist_zero_right] at this
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa [norm_sub_rev] using this
  have hφ_compact : HasCompactSupport φ :=
    IsCompact.of_isClosed_subset (isCompact_closedBall y t) (isClosed_tsupport φ) hφ_tsupport
  have hφ_sub : tsupport φ ⊆ U := hφ_tsupport.trans hball
  -- pointwise derivative formula for the convolution
  have hint : ∀ i, Integrable
      (fun s => (ContinuousLinearMap.precompL (Vec 2) L) (fderiv ℝ k s) (fi i (y - s))) volume :=
    fun i => hdk_supp.convolutionExists_left (ContinuousLinearMap.precompL (Vec 2) L)
      hdk_cont (hloc i) y
  have hkey : ∀ i : Fin 2,
      (fderiv ℝ (fun z => (k ⋆[L, volume] (fi i)) z) y) (basisVec i)
        = ∫ s, (fderiv ℝ k s (basisVec i)) * fi i (y - s) := by
    intro i
    rw [(hksupp.hasFDerivAt_convolution_left L hk1 (hloc i) y).fderiv, convolution_def,
      ContinuousLinearMap.integral_apply (hint i)]
    simp [hL]
  have happly : ∀ i : Fin 2,
      Integrable (fun s => (fderiv ℝ k s (basisVec i)) * fi i (y - s)) volume := by
    intro i
    have h := (hint i).apply_continuousLinearMap (basisVec i)
    simpa [hL] using h
  have hpt : ∀ s : Vec 2,
      (∑ i : Fin 2, (fderiv ℝ k s (basisVec i)) * fi i (y - s))
        = (fun z => ∑ i : Fin 2, (fderiv ℝ k (y - z) (basisVec i)) * fi i z) (y - s) := by
    intro s
    simp [sub_sub_cancel]
  have hstep1 :
      ∑ i : Fin 2, (fderiv ℝ (fun z => (k ⋆[L, volume] (fi i)) z) y) (basisVec i)
        = ∫ z, ∑ i : Fin 2, (fderiv ℝ k (y - z) (basisVec i)) * fi i z := by
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hkey i),
      ← integral_finsetSum _ (fun i (_ : i ∈ Finset.univ) => happly i)]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_sub_left_eq_self
      (fun z => ∑ i : Fin 2, (fderiv ℝ k (y - z) (basisVec i)) * fi i z) volume y
  have hstep2 : ∀ z : Vec 2,
      (∑ i : Fin 2, (fderiv ℝ k (y - z) (basisVec i)) * fi i z)
        = -vecDot (zeroExt U g z) (fun i => fderiv ℝ φ z (basisVec i)) := by
    intro z
    simp only [vecDot, hfi, Fin.sum_univ_two, hφ_fderiv]
    ring
  have hstep3 :
      ∫ z, ∑ i : Fin 2, (fderiv ℝ k (y - z) (basisVec i)) * fi i z
        = -∫ z in U, vecDot (g z) (fun i => fderiv ℝ φ z (basisVec i)) := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hstep2)]
    rw [MeasureTheory.integral_neg]
    congr 1
    have hind : (fun z => vecDot (zeroExt U g z) (fun i => fderiv ℝ φ z (basisVec i)))
        = Set.indicator U (fun z => vecDot (g z) (fun i => fderiv ℝ φ z (basisVec i))) := by
      funext z
      by_cases hz : z ∈ U
      · simp [zeroExt, hz]
      · simp [zeroExt, hz, vecDot]
    rw [hind, MeasureTheory.integral_indicator hUmeas]
  rw [hstep1, hstep3]
  have hzero := hgsol (H10Function.ofContDiff hUopen hφ_smooth hφ_compact hφ_sub)
  rw [show ((H10Function.ofContDiff hUopen hφ_smooth hφ_compact hφ_sub).toH1Function.grad)
      = (fun z => fun i => fderiv ℝ φ z (basisVec i)) from rfl] at hzero
  rw [hzero]
  simp

/-- Mollified zero extension, contracted by the factor `lam`. -/
private def mollDilate (U : Set (Vec 2)) (g : Vec 2 → Vec 2) (k : Vec 2 → ℝ) (lam : ℝ) :
    Vec 2 → Vec 2 :=
  fun x i => (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun w => zeroExt U g w i)) (lam • x)

private theorem contDiff_moll_coord {U : Set (Vec 2)} (hUmeas : MeasurableSet U)
    {g : Vec 2 → Vec 2} (hgMem : MemVectorL2 U g)
    {k : Vec 2 → ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hksupp : HasCompactSupport k) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞)
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun w => zeroExt U g w i)) :=
  hksupp.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hk
    (locallyIntegrable_zeroExt_coord hUmeas hgMem i)

private theorem differentiable_mollDilate {U : Set (Vec 2)} (hUmeas : MeasurableSet U)
    {g : Vec 2 → Vec 2} (hgMem : MemVectorL2 U g)
    {k : Vec 2 → ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hksupp : HasCompactSupport k) (lam : ℝ) :
    Differentiable ℝ (mollDilate U g k lam) := by
  apply differentiable_pi.2
  intro i
  have hlin : Differentiable ℝ (fun x : Vec 2 => lam • x) := by fun_prop
  exact ((contDiff_moll_coord hUmeas hgMem hk hksupp i).differentiable (by simp)).comp hlin

private theorem sum_fderiv_mollDilate_eq_zero {U : Set (Vec 2)} (hUopen : IsOpen U)
    {g : Vec 2 → Vec 2} (hgMem : MemVectorL2 U g) (hgsol : IsSolenoidalOn U g)
    {k : Vec 2 → ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hksupp : HasCompactSupport k)
    {t lam : ℝ} (hkball : tsupport k ⊆ Metric.closedBall (0 : Vec 2) t)
    {x : Vec 2} (hball : Metric.closedBall (lam • x) t ⊆ U) :
    (fderiv ℝ (mollDilate U g k lam) x (basisVec 0)) 0
      + (fderiv ℝ (mollDilate U g k lam) x (basisVec 1)) 1 = 0 := by
  classical
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  set L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ with hL
  set F : Fin 2 → Vec 2 → ℝ :=
    fun i => (k ⋆[L, volume] (fun w => zeroExt U g w i)) with hF
  have hlin : HasFDerivAt (fun z : Vec 2 => lam • z)
      (lam • ContinuousLinearMap.id ℝ (Vec 2)) x := by
    simpa using (hasFDerivAt_id (𝕜 := ℝ) x).const_smul lam
  have hFdiff : ∀ i, DifferentiableAt ℝ (F i) (lam • x) := fun i =>
    ((contDiff_moll_coord hUmeas hgMem hk hksupp i).differentiable (by simp)) (lam • x)
  have hcomp : ∀ i : Fin 2, HasFDerivAt (fun z => F i (lam • z))
      ((fderiv ℝ (F i) (lam • x)).comp (lam • ContinuousLinearMap.id ℝ (Vec 2))) x :=
    fun i => (hFdiff i).hasFDerivAt.comp x hlin
  have hpi : HasFDerivAt (mollDilate U g k lam)
      (ContinuousLinearMap.pi fun i =>
        (fderiv ℝ (F i) (lam • x)).comp (lam • ContinuousLinearMap.id ℝ (Vec 2))) x := by
    rw [hasFDerivAt_pi]
    intro i
    simpa [mollDilate, hF] using hcomp i
  have hval : ∀ (i : Fin 2) (v : Vec 2),
      (fderiv ℝ (mollDilate U g k lam) x v) i
        = lam * (fderiv ℝ (F i) (lam • x)) v := by
    intro i v
    rw [hpi.fderiv]
    simp [ContinuousLinearMap.pi_apply]
  rw [hval 0 (basisVec 0), hval 1 (basisVec 1), ← mul_add]
  have hzero := sum_fderiv_convolution_eq_zero hUopen hgMem hgsol hk hksupp hkball hball
  rw [Fin.sum_univ_two] at hzero
  rw [show (fderiv ℝ (F 0) (lam • x)) (basisVec 0) + (fderiv ℝ (F 1) (lam • x)) (basisVec 1) = 0
    from hzero]
  ring

private theorem tsupport_scaledConvexApproxKernel_subset {d : ℕ} {ρ : Vec d → ℝ}
    (hρ : IsConvexApproxKernel ρ) {a : ℝ} (ha : 0 < a) :
    tsupport (scaledConvexApproxKernel ρ a) ⊆ Metric.closedBall (0 : Vec d) a := by
  apply closure_minimal
  · intro z hz
    have hρ_ne : ρ (a⁻¹ • z) ≠ 0 := by
      intro hzero
      exact hz (by simp only [scaledConvexApproxKernel, hzero, mul_zero])
    have hball : a⁻¹ • z ∈ Metric.closedBall (0 : Vec d) 1 :=
      hρ.support_subset_closedBall (subset_tsupport ρ hρ_ne)
    rw [Metric.mem_closedBall, dist_zero_right] at hball ⊢
    calc
      ‖z‖ = a * (a⁻¹ * ‖z‖) := by field_simp
      _ = a * ‖a⁻¹ • z‖ := by
        rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ha]
      _ ≤ a * 1 := mul_le_mul_of_nonneg_left hball ha.le
      _ = a := mul_one _
  · exact Metric.isClosed_closedBall

private theorem openCubeSet_subset_scaledOpenCubeSet {d : ℕ} (Q : TriadicCube d) {ρ : ℝ}
    (hρ : 1 ≤ ρ) :
    openCubeSet Q ⊆ scaledOpenCubeSet Q ρ := by
  intro x hx i
  have h := hx i
  have hR : 0 < cubeRadius Q := cubeRadius_pos Q
  have hmono : cubeRadius Q ≤ ρ * cubeRadius Q := by nlinarith
  calc |x i - cubeCenter Q i| < cubeRadius Q := by
        rw [abs_lt]
        obtain ⟨h1, h2⟩ := h
        simp only [cubeCenter, cubeRadius]
        constructor <;> nlinarith [h1, h2]
    _ ≤ ρ * cubeRadius Q := hmono

private theorem scaledOpenCubeSet_mono {d : ℕ} (Q : TriadicCube d) {ρ₁ ρ₂ : ℝ} (h : ρ₁ ≤ ρ₂) :
    scaledOpenCubeSet Q ρ₁ ⊆ scaledOpenCubeSet Q ρ₂ := by
  intro x hx i
  exact lt_of_lt_of_le (hx i) (by nlinarith [cubeRadius_nonneg Q])

private theorem scaledClosedCubeSet_subset_scaledOpenCubeSet' {d : ℕ} (Q : TriadicCube d)
    {ρ₁ ρ₂ : ℝ} (h : ρ₁ < ρ₂) :
    scaledClosedCubeSet Q ρ₁ ⊆ scaledOpenCubeSet Q ρ₂ := by
  intro x hx i
  exact lt_of_le_of_lt (hx i) (by nlinarith [cubeRadius_pos Q])

private theorem cubeCenter_originCube (d : ℕ) (n : ℤ) : cubeCenter (originCube d n) = 0 := by
  funext i
  simp [cubeCenter, originCube]

private theorem mem_openCubeSet_originCube_abs_iff {d : ℕ} {n : ℤ} {x : Vec d} :
    x ∈ openCubeSet (originCube d n) ↔ ∀ i, |x i| < cubeRadius (originCube d n) := by
  rw [mem_openCubeSet_originCube_iff]
  constructor
  · intro h i
    have := h i
    rw [abs_lt]
    simp only [cubeRadius, cubeScaleFactor, originCube] at *
    constructor <;> linarith [this.1, this.2]
  · intro h i
    have := h i
    rw [abs_lt] at this
    simp only [cubeRadius, cubeScaleFactor, originCube] at *
    constructor <;> linarith [this.1, this.2]

private theorem mem_scaledOpenCubeSet_originCube_abs_iff {d : ℕ} {n : ℤ} {ρ : ℝ} {x : Vec d} :
    x ∈ scaledOpenCubeSet (originCube d n) ρ ↔
      ∀ i, |x i| < ρ * cubeRadius (originCube d n) := by
  constructor
  · intro h i
    simpa [cubeCenter_originCube] using h i
  · intro h i
    simpa [cubeCenter_originCube] using h i

private theorem isPotentialOn_rot_mollDilate {n : ℤ} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 6)
    {g : Vec 2 → Vec 2}
    (hgMem : MemVectorL2 (openCubeSet (originCube 2 n)) g)
    (hgsol : IsSolenoidalOn (openCubeSet (originCube 2 n)) g) :
    IsPotentialOn (openCubeSet (originCube 2 n))
      (fun x => matVecMul planarQuarterTurn
        (mollDilate (openCubeSet (originCube 2 n)) g
          (scaledConvexApproxKernel (unitConvexApproxKernel (d := 2))
            (δ * (cubeRadius (originCube 2 n) / 2)))
          (1 / (1 + 6 * δ)) x)) := by
  classical
  set Q : TriadicCube 2 := originCube 2 n with hQdef
  set R : ℝ := cubeRadius Q with hRdef
  have hR : 0 < R := cubeRadius_pos Q
  set t : ℝ := δ * (R / 2) with htdef
  have ht0 : 0 < t := by positivity
  set lam : ℝ := 1 / (1 + 6 * δ) with hlamdef
  have hden : 0 < 1 + 6 * δ := by linarith
  have hlam0 : 0 < lam := by positivity
  set k : Vec 2 → ℝ := scaledConvexApproxKernel (unitConvexApproxKernel (d := 2)) t with hkdef
  have hkernel : IsConvexApproxKernel (unitConvexApproxKernel (d := 2)) :=
    isConvexApproxKernel_unitConvexApproxKernel
  have hksmooth : ContDiff ℝ (⊤ : ℕ∞) k := contDiff_scaledConvexApproxKernel hkernel t
  have hkcs : HasCompactSupport k :=
    hasCompactSupport_scaledConvexApproxKernel hkernel.compactSupport ht0
  have hkball : tsupport k ⊆ Metric.closedBall (0 : Vec 2) t :=
    tsupport_scaledConvexApproxKernel_subset hkernel ht0
  have hVdom : IsOpenBoundedConvexDomain (scaledOpenCubeSet Q (1 + 5 * δ)) :=
    isOpenBoundedConvexDomain_scaledOpenCubeSet_of_pos Q (by linarith)
  have hWdom : IsOpenBoundedConvexDomain (scaledOpenCubeSet Q (1 + 3 * δ)) :=
    isOpenBoundedConvexDomain_scaledOpenCubeSet_of_pos Q (by linarith)
  refine isPotentialOn_rot_of_differentiable_of_div_eq_zero
    (isOpenBoundedConvexDomain_openCubeSet Q)
    (V := scaledOpenCubeSet Q (1 + 5 * δ)) (W := scaledOpenCubeSet Q (1 + 3 * δ))
    (chi := QuantitativeCubeCutoff.canonicalFun Q (1 + 3 * δ) (1 + 4 * δ))
    hVdom.2.2 hVdom.1 hWdom.1
    (openCubeSet_subset_scaledOpenCubeSet Q (by linarith))
    (scaledOpenCubeSet_mono Q (by linarith))
    (QuantitativeCubeCutoff.canonicalFun_smooth Q (by linarith) (by linarith))
    (QuantitativeCubeCutoff.canonicalFun_hasCompactSupport Q (by linarith) (by linarith))
    ((QuantitativeCubeCutoff.canonicalFun_tsupport_subset_scaledClosedCubeSet
      (by linarith) (by linarith)).trans
      (scaledClosedCubeSet_subset_scaledOpenCubeSet' Q (by linarith)))
    ?_
    (differentiable_mollDilate (isOpenBoundedConvexDomain_openCubeSet Q).1.measurableSet
      hgMem hksmooth hkcs lam)
    ((differentiable_mollDilate (isOpenBoundedConvexDomain_openCubeSet Q).1.measurableSet
      hgMem hksmooth hkcs lam).continuous)
    ?_
  · intro x hx
    refine QuantitativeCubeCutoff.canonicalFun_eq_one_on_inner (by linarith) (by linarith) ?_
    intro i
    exact le_of_lt (hx i)
  · intro a ha
    refine sum_fderiv_mollDilate_eq_zero (isOpenBoundedConvexDomain_openCubeSet Q).1
      hgMem hgsol hksmooth hkcs hkball ?_
    intro z hz
    have hacoord : ∀ i, |a i| < (1 + 5 * δ) * R :=
      mem_scaledOpenCubeSet_originCube_abs_iff.mp ha
    have hzcoord : ∀ i, |z i - lam * a i| ≤ t := by
      intro i
      have := dist_le_pi_dist z (lam • a) i
      rw [Metric.mem_closedBall] at hz
      have hzi : dist (z i) ((lam • a) i) ≤ t := le_trans this hz
      simpa [Real.dist_eq, Pi.smul_apply, smul_eq_mul] using hzi
    rw [mem_openCubeSet_originCube_abs_iff]
    intro i
    have h1 : |lam * a i| < lam * ((1 + 5 * δ) * R) := by
      rw [abs_mul, abs_of_pos hlam0]
      exact mul_lt_mul_of_pos_left (hacoord i) hlam0
    have habs : |z i| ≤ |z i - lam * a i| + |lam * a i| := by
      calc |z i| = |(z i - lam * a i) + lam * a i| := by ring_nf
        _ ≤ |z i - lam * a i| + |lam * a i| := abs_add_le _ _
    have hkey : lam * ((1 + 5 * δ) * R) + t ≤ R := by
      rw [hlamdef, htdef, div_mul_eq_mul_div, one_mul, div_add' _ _ _ (ne_of_gt hden),
        div_le_iff₀ hden]
      nlinarith [hR, hδ0, hδ1]
    linarith [hzcoord i, h1, habs, hkey]

private theorem eLpNorm_comp_smul_univ {d : ℕ} {a : ℝ} (ha : 0 < a) {f : Vec d → ℝ}
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm (fun x => f (a • x)) 2 volume =
      ENNReal.ofReal ((a ^ d)⁻¹) ^ (1 / (2 : ENNReal)).toReal * eLpNorm f 2 volume := by
  have huniv : a • (Set.univ : Set (Vec d)) = Set.univ := by
    ext x
    simp only [Set.mem_smul_set, Set.mem_univ, iff_true]
    exact ⟨a⁻¹ • x, trivial, by rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]⟩
  have h := W1pFunction.eLpNorm_comp_smul_eq (d := d) (U := (Set.univ : Set (Vec d))) (p := 2) ha
    (by norm_num) (f := f) (by rwa [huniv, volumeMeasureOn, MeasureTheory.Measure.restrict_univ])
  rwa [huniv, volumeMeasureOn, MeasureTheory.Measure.restrict_univ] at h

private theorem eLpNorm_dilate_sub_eq {d : ℕ} {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    {f : Vec d → ℝ} (hf : MemLp f 2 volume) :
    eLpNorm (fun x => f (lam • x) - f x) 2 volume
      = ENNReal.ofReal ((lam ^ d)⁻¹) ^ (1 / (2 : ENNReal)).toReal *
        eLpNorm ((f ∘ globalAffineExpansion (0 : Vec d) (lam⁻¹ - 1)) - f) 2 volume := by
  have hε : (0 : ℝ) ≤ lam⁻¹ - 1 := by
    have h1 : (1 : ℝ) ≤ lam⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hlam]
      simpa using hlam1
    linarith
  set v : Vec d → ℝ := (f ∘ globalAffineExpansion (0 : Vec d) (lam⁻¹ - 1)) - f with hv
  have hvmem : MemLp v 2 volume := (Homogenization.MemLp.comp_globalAffineExpansion hf 0 hε).sub hf
  have hpt : ∀ x : Vec d, f (lam • x) - f x = -(v (lam • x)) := by
    intro x
    have hscale : (1 + (lam⁻¹ - 1)) • (lam • x) = x := by
      rw [show (1 + (lam⁻¹ - 1)) = lam⁻¹ by ring, smul_smul,
        inv_mul_cancel₀ hlam.ne', one_smul]
    simp only [hv, Pi.sub_apply, Function.comp_apply, globalAffineExpansion, smul_zero, sub_zero,
      hscale]
    ring
  calc eLpNorm (fun x => f (lam • x) - f x) 2 volume
      = eLpNorm (fun x => v (lam • x)) 2 volume := by
        rw [eLpNorm_congr_ae (Filter.Eventually.of_forall hpt),
          show (fun x : Vec d => -(v (lam • x))) = -(fun x : Vec d => v (lam • x)) from rfl,
          eLpNorm_neg]
    _ = ENNReal.ofReal ((lam ^ d)⁻¹) ^ (1 / (2 : ENNReal)).toReal * eLpNorm v 2 volume :=
        eLpNorm_comp_smul_univ hlam hvmem.aestronglyMeasurable

private theorem aestronglyMeasurable_comp_smul {d : ℕ} {a : ℝ} (ha : 0 < a) {f : Vec d → ℝ}
    (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (fun x => f (a • x)) volume := by
  have huniv : a • (Set.univ : Set (Vec d)) = Set.univ := by
    ext x
    simp only [Set.mem_smul_set, Set.mem_univ, iff_true]
    exact ⟨a⁻¹ • x, trivial, by rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]⟩
  have hmap := map_smul_volume_restrict (d := d) (a := a) ha (Set.univ : Set (Vec d))
  rw [huniv, MeasureTheory.Measure.restrict_univ] at hmap
  have hf' : AEStronglyMeasurable f (Measure.map (fun x : Vec d => a • x) volume) := by
    rw [hmap]
    exact hf.mono_ac MeasureTheory.Measure.smul_absolutelyContinuous
  exact hf'.comp_aemeasurable (measurable_const_smul a).aemeasurable


private theorem tendsto_eLpNorm_mollDilate_coord (n : ℤ) {g : Vec 2 → Vec 2}
    (hgMem : MemVectorL2 (openCubeSet (originCube 2 n)) g) (i : Fin 2)
    {δ : ℕ → ℝ} (hpos : ∀ m, 0 < δ m) (hle : ∀ m, δ m ≤ 1 / 6)
    (hlim : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun m => eLpNorm (fun x =>
      mollDilate (openCubeSet (originCube 2 n)) g
        (scaledConvexApproxKernel (unitConvexApproxKernel (d := 2))
          (δ m * (cubeRadius (originCube 2 n) / 2))) (1 / (1 + 6 * δ m)) x i
      - zeroExt (openCubeSet (originCube 2 n)) g x i) 2 volume)
      Filter.atTop (nhds 0) := by
  classical
  set Q : TriadicCube 2 := originCube 2 n with hQdef
  set U : Set (Vec 2) := openCubeSet Q with hUdef
  have hUmeas : MeasurableSet U := (isOpenBoundedConvexDomain_openCubeSet Q).1.measurableSet
  have hR : 0 < cubeRadius Q := cubeRadius_pos Q
  set f : Vec 2 → ℝ := fun w => zeroExt U g w i with hfdef
  have hfmem : MemLp f 2 volume := memLp_zeroExt_coord hUmeas hgMem i
  have hkernel : IsConvexApproxKernel (unitConvexApproxKernel (d := 2)) :=
    isConvexApproxKernel_unitConvexApproxKernel
  set lam : ℕ → ℝ := fun m => 1 / (1 + 6 * δ m) with hlamdef
  have hden : ∀ m, 0 < 1 + 6 * δ m := fun m => by linarith [hpos m]
  have hlam0 : ∀ m, 0 < lam m := fun m => div_pos one_pos (hden m)
  have hlam1 : ∀ m, lam m ≤ 1 := fun m => by
    rw [hlamdef]
    rw [div_le_one (hden m)]
    linarith [hpos m]
  have hlamhalf : ∀ m, 1 / 2 ≤ lam m := fun m => by
    rw [hlamdef, le_div_iff₀ (hden m)]
    linarith [hle m]
  -- the two convergence ingredients
  set K : ℕ → Vec 2 → ℝ := fun m =>
    scaledConvexApproxKernel (unitConvexApproxKernel (d := 2)) (δ m * (cubeRadius Q / 2)) with hKdef
  have hA : Filter.Tendsto
      (fun m => eLpNorm ((K m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) - f) 2 volume)
      Filter.atTop (nhds 0) := by
    have h := tendsto_eLpNorm_sub_zero_convolution_scaledConvexApproxKernel
      (ρ := unitConvexApproxKernel (d := 2)) (g := f) (p := 2) hkernel (by norm_num) (by norm_num)
      hfmem (r := cubeRadius Q / 2) (by positivity) hlim
      (Filter.Eventually.of_forall hpos)
    refine h.congr fun m => ?_
    rfl
  have hB : Filter.Tendsto
      (fun m => eLpNorm ((f ∘ globalAffineExpansion (0 : Vec 2) ((lam m)⁻¹ - 1)) - f) 2 volume)
      Filter.atTop (nhds 0) := by
    refine tendsto_eLpNorm_comp_globalAffineExpansion_sub_zero (by norm_num) (by norm_num)
      hfmem 0 ?_ ?_
    · have hcont : Filter.Tendsto (fun m => 6 * δ m) Filter.atTop (nhds 0) := by
        simpa using hlim.const_mul (6 : ℝ)
      have hEq : ∀ m, (lam m)⁻¹ - 1 = 6 * δ m := by
        intro m
        simp only [hlamdef, one_div, inv_inv]
        ring
      simpa [hEq] using hcont
    · intro m
      have : (lam m)⁻¹ - 1 = 6 * δ m := by
        simp only [hlamdef, one_div, inv_inv]
        ring
      rw [this]
      linarith [hpos m]
  -- combine the two ingredients
  set c : ℕ → ENNReal :=
    fun m => ENNReal.ofReal (((lam m) ^ 2)⁻¹) ^ (1 / (2 : ENNReal)).toReal with hcdef
  have hconvcont : ∀ m, Continuous (K m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) := by
    intro m
    have hscale : 0 < δ m * (cubeRadius Q / 2) := mul_pos (hpos m) (by positivity)
    exact (hasCompactSupport_scaledConvexApproxKernel hkernel.compactSupport hscale
      ).continuous_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (continuous_scaledConvexApproxKernel hkernel.continuous _)
      (hfmem.locallyIntegrable (by norm_num))
  have hbound : ∀ m,
      eLpNorm (fun x => mollDilate U g (K m) (lam m) x i - f x) 2 volume
        ≤ c m * eLpNorm ((K m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) - f) 2 volume
          + c m * eLpNorm ((f ∘ globalAffineExpansion (0 : Vec 2) ((lam m)⁻¹ - 1)) - f) 2 volume :=
      by
    intro m
    have hvmeas : AEStronglyMeasurable
        ((K m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) - f) volume :=
      ((hconvcont m).aestronglyMeasurable).sub hfmem.aestronglyMeasurable
    have hpt : (fun x => mollDilate U g (K m) (lam m) x i - f x)
        = (fun x => ((K m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) - f) (lam m • x))
          + (fun x => f (lam m • x) - f x) := by
      funext x
      simp only [mollDilate, Pi.add_apply, Pi.sub_apply, hfdef]
      ring
    rw [hpt]
    refine le_trans (eLpNorm_add_le (by norm_num)) ?_
    gcongr
    · exact le_of_eq (eLpNorm_comp_smul_univ (hlam0 m) hvmeas)
    · exact le_of_eq (eLpNorm_dilate_sub_eq (hlam0 m) (hlam1 m) hfmem)
  -- uniform bound on the dilation factor
  set C : ENNReal := ENNReal.ofReal 4 ^ (1 / (2 : ENNReal)).toReal with hCdef
  have hcC : ∀ m, c m ≤ C := by
    intro m
    refine ENNReal.rpow_le_rpow ?_ (by positivity)
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (1 / 2 : ℝ) ≤ lam m := hlamhalf m
    have h2 : (0 : ℝ) < lam m := hlam0 m
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  have hCtop : C ≠ ⊤ := by
    rw [hCdef]
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (by simp)
  have hupper : Filter.Tendsto
      (fun m => C * (eLpNorm ((K m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) - f) 2 volume
        + eLpNorm ((f ∘ globalAffineExpansion (0 : Vec 2) ((lam m)⁻¹ - 1)) - f) 2 volume))
      Filter.atTop (nhds 0) := by
    have hsum := hA.add hB
    rw [add_zero] at hsum
    have := ENNReal.Tendsto.const_mul hsum (Or.inr hCtop)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun m => zero_le) (fun m => ?_)
  refine le_trans (hbound m) ?_
  rw [mul_add]
  gcongr <;> exact hcC m

private theorem isClosed_potentialSubmodule {d : ℕ} [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) :
    IsClosed ((PotentialSolenoidalExact.potential U :
      Submodule ℝ (HilbertVectorL2 U)) : Set (HilbertVectorL2 U)) := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := hU.isFiniteMeasure_restrict_volume
  rw [← closure_subset_iff_isClosed]
  intro P hP
  have hPorth : P ∈ ((PotentialSolenoidalExact.potential U)ᗮ)ᗮ := by
    rw [Submodule.orthogonal_orthogonal_eq_closure]
    have : P ∈ closure ((PotentialSolenoidalExact.potential U :
      Submodule ℝ (HilbertVectorL2 U)) : Set (HilbertVectorL2 U)) := hP
    simpa [Submodule.topologicalClosure_coe] using! this
  set p : Vec d → Vec d := vecFieldOfHilbertVectorL2 P with hpdef
  have hpMem : MemVectorL2 U p := memVectorL2_vecFieldOfHilbertVectorL2 P
  have hpEq : toHilbertVectorL2OfVecField hpMem = P :=
    toHilbertVectorL2OfVecField_vecFieldOfHilbertVectorL2 P
  have hpot : IsPotentialOn U p := by
    have : HasHodgeConverse U := hasHodgeConverse_of_isOpenBoundedConvexDomain hU
    refine IsPotentialOn.of_orthogonal_to_solenoidalZeroNormalTrace_of_memVectorL2 hpMem ?_
    intro h hhMem hhsol
    have hhmem : toHilbertVectorL2OfVecField hhMem ∈ (PotentialSolenoidalExact.potential U)ᗮ := by
      refine (PotentialSolenoidalExact.mem_solenoidalZeroNormalTrace_iff _).2 ?_
      intro u
      rw [show u.gradToHilbertVectorL2 = toHilbertVectorL2OfVecField u.grad_memVectorL2 from rfl,
        inner_toHilbertVectorL2OfVecField_eq_integral]
      exact hhsol u
    have hzero : inner ℝ (toHilbertVectorL2OfVecField hhMem) P = 0 :=
      (Submodule.mem_orthogonal _ _).1 hPorth _ hhmem
    rw [← hpEq, inner_toHilbertVectorL2OfVecField_eq_integral hhMem hpMem] at hzero
    exact hzero
  obtain ⟨u, hu⟩ := hpot
  refine (PotentialSolenoidalExact.mem_potential_iff P).2 ⟨u, ?_⟩
  rw [← hpEq]
  show toHilbertVectorL2OfVecField u.grad_memVectorL2 = toHilbertVectorL2OfVecField hpMem
  congr 1

private theorem eLpNorm_rot_diff_le {U : Set (Vec 2)} {F G : Vec 2 → Vec 2}
    (ha : AEStronglyMeasurable (fun x => F x 0 - G x 0) (volumeMeasureOn U))
    (hb : AEStronglyMeasurable (fun x => F x 1 - G x 1) (volumeMeasureOn U)) :
    eLpNorm (hilbertifyVecField (fun x => matVecMul planarQuarterTurn (F x)
        - matVecMul planarQuarterTurn (G x))) 2 (volumeMeasureOn U)
      ≤ 2 * (eLpNorm (fun x => F x 0 - G x 0) 2 (volumeMeasureOn U)
        + eLpNorm (fun x => F x 1 - G x 1) 2 (volumeMeasureOn U)) := by
  set w : Vec 2 → Vec 2 := fun x => matVecMul planarQuarterTurn (F x)
    - matVecMul planarQuarterTurn (G x) with hwdef
  set h : Vec 2 → ℝ := fun x => ‖F x 0 - G x 0‖ + ‖F x 1 - G x 1‖ with hhdef
  have hpt : ∀ x, ‖hilbertifyVecField w x‖ ≤ ‖(2 : ℝ) • h x‖ := by
    intro x
    have h1 : ‖hilbertifyVecField w x‖ ≤ (2 : ℝ) * ‖w x‖ := by
      simpa [hilbertifyVecField] using HilbertVec.norm_ofVec_le_mul_norm (w x)
    have hval : ∀ j : Fin 2, ‖w x j‖ ≤ h x := by
      intro j
      have hn0 : (0 : ℝ) ≤ ‖F x 0 - G x 0‖ := norm_nonneg _
      have hn1 : (0 : ℝ) ≤ ‖F x 1 - G x 1‖ := norm_nonneg _
      rcases (by omega : j.val = 0 ∨ j.val = 1) with hj | hj
      · have hj0 : j = 0 := Fin.ext hj
        subst hj0
        have hw0 : w x 0 = F x 1 - G x 1 := by
          simp [hwdef, planarQuarterTurn_mulVec]
        simp only [hw0, hhdef]
        linarith
      · have hj1 : j = 1 := Fin.ext hj
        subst hj1
        have hw1 : w x 1 = -(F x 0 - G x 0) := by
          simp [hwdef, planarQuarterTurn_mulVec]
          ring
        simp only [hw1, hhdef, norm_neg]
        linarith
    have h2 : ‖w x‖ ≤ h x := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 ?_
      intro i
      exact hval i
    have hh0 : 0 ≤ h x := by positivity
    calc ‖hilbertifyVecField w x‖ ≤ (2:ℝ) * ‖w x‖ := h1
      _ ≤ (2:ℝ) * h x := by nlinarith [norm_nonneg (w x)]
      _ = ‖(2 : ℝ) • h x‖ := by
          rw [norm_smul]
          simp [Real.norm_eq_abs, abs_of_nonneg hh0]
  have hwmeas : AEStronglyMeasurable w (volumeMeasureOn U) := by
    have hwEq : w = fun x => (F x 1 - G x 1) • basisVec 0
        - (F x 0 - G x 0) • basisVec 1 := by
      funext x i
      fin_cases i <;> simp [hwdef, planarQuarterTurn_mulVec, basisVec] ; ring
    rw [hwEq]
    exact (hb.smul_const _).sub (ha.smul_const _)
  have hhilbertMeas : AEStronglyMeasurable (hilbertifyVecField w) (volumeMeasureOn U) := by
    exact (HilbertVec.ofVecL 2).continuous.comp_aestronglyMeasurable hwmeas
  calc eLpNorm (hilbertifyVecField w) 2 (volumeMeasureOn U)
      ≤ eLpNorm ((2 : ℝ) • h) 2 (volumeMeasureOn U) := eLpNorm_mono hhilbertMeas hpt
    _ = ‖(2 : ℝ)‖ₑ * eLpNorm h 2 (volumeMeasureOn U) :=
        eLpNorm_const_smul (2 : ℝ) h 2 (volumeMeasureOn U)
    _ = 2 * eLpNorm h 2 (volumeMeasureOn U) := by
        congr 1
        rw [show ‖(2 : ℝ)‖ₑ = ENNReal.ofNNReal ‖(2:ℝ)‖₊ from rfl]
        norm_num
    _ ≤ 2 * (eLpNorm (fun x => F x 0 - G x 0) 2 (volumeMeasureOn U)
        + eLpNorm (fun x => F x 1 - G x 1) 2 (volumeMeasureOn U)) := by
        gcongr
        calc eLpNorm h 2 (volumeMeasureOn U)
            ≤ eLpNorm (fun x => ‖F x 0 - G x 0‖) 2 (volumeMeasureOn U)
              + eLpNorm (fun x => ‖F x 1 - G x 1‖) 2 (volumeMeasureOn U) :=
              eLpNorm_add_le (by norm_num)
          _ = eLpNorm (fun x => F x 0 - G x 0) 2 (volumeMeasureOn U)
              + eLpNorm (fun x => F x 1 - G x 1) 2 (volumeMeasureOn U) := by
              rw [eLpNorm_norm _ ha, eLpNorm_norm _ hb]

theorem planarStreamFunctionOn_openCubeSet_originCube (n : ℤ) :
    PlanarStreamFunctionOn (openCubeSet (originCube 2 n)) := by
  classical
  intro g hgMem hgsol
  set Q : TriadicCube 2 := originCube 2 n with hQdef
  set U : Set (Vec 2) := openCubeSet Q with hUdef
  have hU : IsOpenBoundedConvexDomain U := isOpenBoundedConvexDomain_openCubeSet Q
  have hUmeas : MeasurableSet U := hU.1.measurableSet
  set δ : ℕ → ℝ := fun m => (1 / 6) * (1 / ((m : ℝ) + 1)) with hδdef
  have hmpos : ∀ m : ℕ, (0 : ℝ) < (m : ℝ) + 1 := fun m => by positivity
  have hpos : ∀ m, 0 < δ m := fun m => by
    have := hmpos m
    rw [hδdef]
    positivity
  have hle : ∀ m, δ m ≤ 1 / 6 := fun m => by
    have h1 : 1 / ((m : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (hmpos m)]
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    rw [hδdef]
    nlinarith
  have hlim : Filter.Tendsto δ Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Filter.Tendsto (fun m : ℕ => (1 / 6 : ℝ) * (1 / ((m : ℝ) + 1)))
        Filter.atTop (nhds ((1 / 6 : ℝ) * 0)) := h.const_mul (1 / 6 : ℝ)
    simpa [hδdef] using h2
  set G : ℕ → Vec 2 → Vec 2 := fun m =>
    mollDilate U g (scaledConvexApproxKernel (unitConvexApproxKernel (d := 2))
      (δ m * (cubeRadius Q / 2))) (1 / (1 + 6 * δ m)) with hGdef
  have hpot : ∀ m, IsPotentialOn U (fun x => matVecMul planarQuarterTurn (G m x)) :=
    fun m => isPotentialOn_rot_mollDilate (hpos m) (hle m) hgMem hgsol
  choose u hu using hpot
  have hRgMem : MemVectorL2 U (fun x => matVecMul planarQuarterTurn (g x)) :=
    memVectorL2_planarQuarterTurn hgMem
  have hRGmem : ∀ m, MemVectorL2 U (fun x => matVecMul planarQuarterTurn (G m x)) := by
    intro m
    rw [← hu m]
    exact (u m).grad_memVectorL2
  -- coordinatewise convergence on `U`
  have hcoordconv : ∀ i : Fin 2, Filter.Tendsto
      (fun m => eLpNorm (fun x => G m x i - g x i) 2 (volumeMeasureOn U))
      Filter.atTop (nhds 0) := by
    intro i
    have hglob := tendsto_eLpNorm_mollDilate_coord n hgMem i hpos hle hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hglob
      (fun m => zero_le) (fun m => ?_)
    have hae : (fun x => G m x i - g x i)
        =ᵐ[volumeMeasureOn U] fun x => G m x i - zeroExt U g x i := by
      filter_upwards [MeasureTheory.ae_restrict_mem hUmeas] with x hx
      simp [zeroExt, hx]
    calc eLpNorm (fun x => G m x i - g x i) 2 (volumeMeasureOn U)
        = eLpNorm (fun x => G m x i - zeroExt U g x i) 2 (volumeMeasureOn U) :=
          eLpNorm_congr_ae hae
      _ ≤ eLpNorm (fun x => G m x i - zeroExt U g x i) 2 volume :=
          eLpNorm_mono_measure _ MeasureTheory.Measure.restrict_le_self
  -- convergence of the Hilbert representatives
  have hnormconv : Filter.Tendsto
      (fun m => ‖toHilbertVectorL2OfVecField (hRGmem m)
        - toHilbertVectorL2OfVecField hRgMem‖) Filter.atTop (nhds 0) := by
    have hGcoord : ∀ (m : ℕ) (i : Fin 2), MemL2On U (fun x => G m x i) := by
      intro m i
      rcases (by omega : i.val = 0 ∨ i.val = 1) with hi | hi
      · have hi0 : i = 0 := Fin.ext hi
        subst hi0
        have h := memScalarL2_coord_of_memVectorL2 (hRGmem m) 1
        have heq : (fun x => (matVecMul planarQuarterTurn (G m x)) 1)
            = fun x => -(G m x 0) := by
          funext x
          simp [planarQuarterTurn_mulVec]
        rw [heq] at h
        have hswap : (fun x => G m x 0) = -(fun x => -(G m x 0)) := by
          funext x
          simp
        rw [hswap]
        exact h.neg
      · have hi1 : i = 1 := Fin.ext hi
        subst hi1
        have h := memScalarL2_coord_of_memVectorL2 (hRGmem m) 0
        have heq : (fun x => (matVecMul planarQuarterTurn (G m x)) 0)
            = fun x => G m x 1 := by
          funext x
          simp [planarQuarterTurn_mulVec]
        rwa [heq] at h
    have hdiffmem : ∀ (m : ℕ) (i : Fin 2), MemL2On U (fun x => G m x i - g x i) :=
      fun m i => (hGcoord m i).sub (memScalarL2_coord_of_memVectorL2 hgMem i)
    have hbound : ∀ m, ‖toHilbertVectorL2OfVecField (hRGmem m)
        - toHilbertVectorL2OfVecField hRgMem‖
        ≤ 2 * (eLpNorm (fun x => G m x 0 - g x 0) 2 (volumeMeasureOn U)
            + eLpNorm (fun x => G m x 1 - g x 1) 2 (volumeMeasureOn U)).toReal := by
      intro m
      rw [show (2 : ℝ) * (eLpNorm (fun x => G m x 0 - g x 0) 2 (volumeMeasureOn U)
          + eLpNorm (fun x => G m x 1 - g x 1) 2 (volumeMeasureOn U)).toReal
          = (2 * (eLpNorm (fun x => G m x 0 - g x 0) 2 (volumeMeasureOn U)
            + eLpNorm (fun x => G m x 1 - g x 1) 2 (volumeMeasureOn U))).toReal by
        rw [ENNReal.toReal_mul]
        norm_num]
      rw [← toHilbertVectorL2OfVecField_sub (hRGmem m) hRgMem]
      rw [show toHilbertVectorL2OfVecField ((hRGmem m).sub hRgMem)
          = ((memHilbertVectorL2_hilbertifyVecField ((hRGmem m).sub hRgMem)).toLp
            (hilbertifyVecField (fun x => matVecMul planarQuarterTurn (G m x)
              - matVecMul planarQuarterTurn (g x)))) from rfl,
        MeasureTheory.Lp.norm_toLp]
      refine ENNReal.toReal_mono ?_ ?_
      · exact ENNReal.mul_ne_top (by norm_num)
          (ENNReal.add_ne_top.2 ⟨(hdiffmem m 0).eLpNorm_ne_top, (hdiffmem m 1).eLpNorm_ne_top⟩)
      · exact eLpNorm_rot_diff_le (hdiffmem m 0).aestronglyMeasurable (hdiffmem m 1).aestronglyMeasurable
    have hsum := (hcoordconv 0).add (hcoordconv 1)
    rw [add_zero] at hsum
    have hmul := ENNReal.Tendsto.const_mul hsum (Or.inr (by norm_num : (2 : ENNReal) ≠ ⊤))
    rw [mul_zero] at hmul
    have hfinal : Filter.Tendsto
        (fun m => 2 * (eLpNorm (fun x => G m x 0 - g x 0) 2 (volumeMeasureOn U)
          + eLpNorm (fun x => G m x 1 - g x 1) 2 (volumeMeasureOn U)).toReal)
        Filter.atTop (nhds 0) := by
      have h := (ENNReal.tendsto_toReal (by norm_num : (0 : ENNReal) ≠ ⊤)).comp hmul
      refine Filter.Tendsto.congr (fun m => ?_) h
      simp [Function.comp, ENNReal.toReal_mul]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hfinal
      (fun m => norm_nonneg _) hbound
  -- conclude
  have hmemP : ∀ m, toHilbertVectorL2OfVecField (hRGmem m)
      ∈ PotentialSolenoidalExact.potential U := by
    intro m
    refine (PotentialSolenoidalExact.mem_potential_iff _).2 ⟨u m, ?_⟩
    show toHilbertVectorL2OfVecField (u m).grad_memVectorL2
      = toHilbertVectorL2OfVecField (hRGmem m)
    congr 1
    · exact hu m
  have htend : Filter.Tendsto (fun m => toHilbertVectorL2OfVecField (hRGmem m))
      Filter.atTop (nhds (toHilbertVectorL2OfVecField hRgMem)) :=
    tendsto_iff_norm_sub_tendsto_zero.2 hnormconv
  have hPmem : toHilbertVectorL2OfVecField hRgMem ∈ PotentialSolenoidalExact.potential U :=
    (isClosed_potentialSubmodule hU).mem_of_tendsto htend
      (Filter.Eventually.of_forall hmemP)
  obtain ⟨v, hv⟩ := (PotentialSolenoidalExact.mem_potential_iff _).1 hPmem
  have hae : v.grad =ᵐ[MeasureTheory.volume.restrict U]
      fun x => matVecMul planarQuarterTurn (g x) := by
    have hiff :=
      (toHilbertVectorL2_eq_toHilbertVectorL2_iff
        (memHilbertVectorL2_hilbertifyVecField v.grad_memVectorL2)
        (memHilbertVectorL2_hilbertifyVecField hRgMem)).1 hv
    filter_upwards [hiff] with x hx
    have hx' : HilbertVec.ofVec (v.grad x)
        = HilbertVec.ofVec (matVecMul planarQuarterTurn (g x)) := hx
    simpa using congrArg HilbertVec.toVec hx'
  exact IsPotentialOn.congr_ae hae v.isPotentialOn

/-- Centered-cube specialization of
`planarZeroNormalStreamFunctionOn_of_planarStreamFunctionOn`. -/
theorem planarZeroNormalStreamFunctionOn_openCubeSet_originCube_of_planarStreamFunctionOn
    (n : ℤ) (hstream : PlanarStreamFunctionOn (openCubeSet (originCube 2 n))) :
    PlanarZeroNormalStreamFunctionOn (openCubeSet (originCube 2 n)) :=
  planarZeroNormalStreamFunctionOn_of_planarStreamFunctionOn
    (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)) hstream

/-- **Weak planar de Rham theorem with zero boundary trace on a centered
cube.**  Every `L²` field on the open centered planar cube that is weakly
divergence free with zero normal trace is the quarter turn of the gradient of
an `H¹₀` function. -/
theorem planarZeroNormalStreamFunctionOn_openCubeSet_originCube (n : ℤ) :
    PlanarZeroNormalStreamFunctionOn (openCubeSet (originCube 2 n)) :=
  planarZeroNormalStreamFunctionOn_openCubeSet_originCube_of_planarStreamFunctionOn n
    (planarStreamFunctionOn_openCubeSet_originCube n)


end

end SubdiffusiveProcess.CoarseGrainingVocab
