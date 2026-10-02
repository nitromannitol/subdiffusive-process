import SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness
import Homogenization.Sobolev.Foundations.H10Graph

/-!
# Existence for the scalar-forcing weak Dirichlet problem

The `Homogenization` library builds the variational solution of the
divergence-form zero-trace Dirichlet problem `-div (a grad u) = div g`, but not
of the scalar-forcing problem `-div (a grad u) = f` used by the section 6
Dirichlet theorems.

This module closes that gap by *representing* the scalar forcing as a
divergence-form forcing.  On a bounded open convex domain the zero-trace
Poincare inequality makes `∇φ ↦ ∫ f φ` a bounded linear functional on the
closed subspace `∇H¹₀(W) ⊆ L²(W;ℝᵈ)`, so the Riesz representation theorem
produces a field `g ∈ L²(W;ℝᵈ)` with `∫ f φ = ∫ g · ∇φ` for every
`φ ∈ H¹₀(W)`.  The library's divergence-form existence theorem then applies
verbatim.

The closedness of `∇H¹₀(W)` is
`Homogenization.H10GraphClosed.isClosed_range_gradientCLM`, and the
identification of the closed graph with honest `H¹₀` functions is
`Homogenization.exists_h10Function_of_mem_h10GraphClosedSubmodule`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization Homogenization.Book.Ch02

noncomputable section

private theorem aux_heartbeat_gradient_riesz {E H S : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
    (grad : E →L[ℝ] H) (value : E →L[ℝ] S)
    {K : NNReal} (hK : AntilipschitzWith K grad)
    (hclosed : IsClosed (Set.range grad)) (f : S) :
    ∃ G : H, ∀ z : E, inner ℝ G (grad z) = inner ℝ f (value z) := by
  classical
  let R : Submodule ℝ H := LinearMap.range grad
  have hRclosed : IsClosed (R : Set H) := by
    simpa only [R, LinearMap.coe_range] using hclosed
  letI : CompleteSpace R := hRclosed.completeSpace_coe
  let P : E →L[ℝ] R := grad.codRestrict R (fun z => LinearMap.mem_range_self _ z)
  have hPinj : LinearMap.ker P = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun z hz => ?_
    have hz' : grad z = 0 := congrArg Subtype.val hz
    exact hK.injective (by simpa only [map_zero] using hz')
  have hPsurj : LinearMap.range P = ⊤ := by
    refine LinearMap.range_eq_top.2 fun y => ?_
    obtain ⟨z, hz⟩ := y.2
    exact ⟨z, Subtype.ext hz⟩
  let e : E ≃L[ℝ] R := ContinuousLinearEquiv.ofBijective P hPinj hPsurj
  let ell : R →L[ℝ] ℝ :=
    (InnerProductSpace.toDual ℝ S f).comp (value.comp (e.symm : R →L[ℝ] E))
  let G : R := (InnerProductSpace.toDual ℝ R).symm ell
  refine ⟨(G : H), fun z => ?_⟩
  have hGell : inner ℝ (G : H) (P z : H) = ell (P z) := by
    rw [← Submodule.coe_inner]
    exact InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := R) (x := P z)
      (y := (ell : StrongDual ℝ R))
  have hez : e.symm (P z) = z := by
    have he : e z = P z := rfl
    rw [← he, e.symm_apply_apply]
  have hleft : ell (P z) = inner ℝ f (value z) := by
    change inner ℝ f (value (e.symm (P z))) = _
    rw [hez]
  exact hGell.trans hleft

section ScalarForcing

variable {d : ℕ} [NeZero d] {W : Set (Vec d)}

omit [NeZero d] in
/-- Pairing scalar `L²` representatives is the set integral of the pointwise
product. -/
private theorem inner_toScalarL2_eq_integral_mul' {F G : Vec d → ℝ}
    (hF : MemScalarL2 W F) (hG : MemScalarL2 W G) :
    inner ℝ (Homogenization.toScalarL2 hF) (Homogenization.toScalarL2 hG) =
      ∫ x in W, F x * G x ∂volume := by
  rw [scalarInner_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [Homogenization.coeFn_toScalarL2 hF,
    Homogenization.coeFn_toScalarL2 hG] with x hFx hGx
  rw [hFx, hGx]

omit [NeZero d] in
/-- Every Hilbert-vector `L²` element is the transport of its own vector
representative. -/
private theorem eq_toHilbertVectorL2OfVecField_coeFn (F : HilbertVectorL2 W) :
    F = toHilbertVectorL2OfVecField
      (MeasureTheory.Lp.memLp (hilbertVectorL2ToVectorL2 (U := W) F)) := by
  calc
    F = vectorL2ToHilbertVectorL2 (U := W) (hilbertVectorL2ToVectorL2 (U := W) F) := by
      symm
      exact vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2 (U := W) F
    _ = vectorL2ToHilbertVectorL2 (U := W)
          (toVectorL2 (MeasureTheory.Lp.memLp
            (hilbertVectorL2ToVectorL2 (U := W) F))) := by
          congr 1
          exact
            (MeasureTheory.Lp.toLp_coeFn (hilbertVectorL2ToVectorL2 (U := W) F)
              (MeasureTheory.Lp.memLp (hilbertVectorL2ToVectorL2 (U := W) F))).symm
    _ = toHilbertVectorL2OfVecField
          (MeasureTheory.Lp.memLp (hilbertVectorL2ToVectorL2 (U := W) F)) :=
        vectorL2ToHilbertVectorL2_toVectorL2 _

private theorem aux_heartbeat_h10_riesz
    (hW : IsOpenBoundedConvexDomain W) {f : Vec d → ℝ} (hf : MemScalarL2 W f) :
    ∃ G : HilbertVectorL2 W, ∀ z : H10GraphClosedSpace (d := d) W,
      inner ℝ G (H10GraphClosed.gradientCLM (d := d) (U := W) z) =
        inner ℝ (Homogenization.toScalarL2 hf) (H10GraphClosed.valueCLM (d := d) (U := W) z) := by
  classical
  obtain ⟨K, hK⟩ := H10GraphClosed.exists_antilipschitzWith_gradientCLM (U := W) hW
  have hRiesz : ∃ G : HilbertVectorL2 W, ∀ z : H10GraphClosedSpace (d := d) W,
      inner ℝ G (H10GraphClosed.gradientCLM (d := d) (U := W) z) =
        inner ℝ (Homogenization.toScalarL2 hf) (H10GraphClosed.valueCLM (d := d) (U := W) z) :=
    aux_heartbeat_gradient_riesz
    (E := H10GraphClosedSpace (d := d) W)
    (H := HilbertVectorL2 W) (S := ScalarL2 W)
    (H10GraphClosed.gradientCLM (d := d) (U := W))
    (H10GraphClosed.valueCLM (d := d) (U := W)) hK
    (H10GraphClosed.isClosed_range_gradientCLM (U := W) hW)
    (Homogenization.toScalarL2 hf)
  exact hRiesz

/-- **Riesz representation of a scalar forcing.**  On a bounded open convex
domain every `L²` scalar forcing is a divergence-form forcing when tested
against `H¹₀` gradients.

This is the only genuinely new analytic step needed for the scalar-forcing
Dirichlet problem; it uses the closedness of the range of the gradient
projection on the closed `H¹₀` graph, which encodes the zero-trace Poincare
inequality. -/
theorem exists_memVectorL2_integral_mul_eq_integral_vecDot
    (hW : IsOpenBoundedConvexDomain W) {f : Vec d → ℝ} (hf : MemScalarL2 W f) :
    ∃ g : Vec d → Vec d, MemVectorL2 W g ∧
      ∀ φ : H10Function W,
        ∫ x in W, f x * φ.toH1Function.toFun x ∂volume =
          ∫ x in W, vecDot (g x) (φ.toH1Function.grad x) ∂volume := by
  classical
  obtain ⟨G, hG⟩ := aux_heartbeat_h10_riesz hW hf
  refine ⟨fun x => hilbertVectorL2ToVectorL2 (U := W) G x,
    MeasureTheory.Lp.memLp _, fun φ => ?_⟩
  have hmem :
      (φ.toH1Function.toScalarL2, φ.toH1Function.gradToHilbertVectorL2) ∈
        (h10GraphClosedSubmodule W).toSubmodule :=
    Submodule.le_topologicalClosure _ (h10_pair_mem_h10GraphSubmodule (U := W) φ)
  let z : H10GraphClosedSpace (d := d) W := ⟨_, hmem⟩
  have hleft : inner ℝ (Homogenization.toScalarL2 hf)
      (H10GraphClosed.valueCLM (d := d) (U := W) z) =
      ∫ x in W, f x * φ.toH1Function.toFun x ∂volume := by
    change inner ℝ (Homogenization.toScalarL2 hf) φ.toH1Function.toScalarL2 = _
    exact inner_toScalarL2_eq_integral_mul' hf φ.toH1Function.memL2
  have hright : inner ℝ G (H10GraphClosed.gradientCLM (d := d) (U := W) z) =
      ∫ x in W, vecDot (hilbertVectorL2ToVectorL2 (U := W) G x)
        (φ.toH1Function.grad x) ∂volume := by
    change inner ℝ G φ.toH1Function.gradToHilbertVectorL2 = _
    have hGrep := eq_toHilbertVectorL2OfVecField_coeFn G
    have hφrep : φ.toH1Function.gradToHilbertVectorL2 =
        toHilbertVectorL2OfVecField φ.toH1Function.grad_memVectorL2 := rfl
    rw [hφrep]
    nth_rewrite 1 [hGrep]
    exact inner_toHilbertVectorL2OfVecField_eq_integral _ _
  exact hleft.symm.trans ((hG z).symm.trans hright)

end ScalarForcing

/-! ### Existence for the two Dirichlet-theorem shapes -/

/-- **Existence for the scalar-forcing weak Dirichlet problem.**  This is the
clause `∃ uLM, IsScalarDirichletSolutionOn ...` of the two section 6 Dirichlet
theorems. -/
theorem exists_isScalarDirichletSolutionOn {d : ℕ} [NeZero d]
    {a : CoeffField d} {lam Lam : ℝ} {Q : TriadicCube d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hD : H1Function (openCubeSet Q)) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (openCubeSet Q))) :
    ∃ u : H1Function (openCubeSet Q), IsScalarDirichletSolutionOn a Q u hD f := by
  have hWgeom : IsOpenBoundedConvexDomain (openCubeSet Q) :=
    isOpenBoundedConvexDomain_openCubeSet Q
  have hne : (openCubeSet Q).Nonempty := openCubeSet_nonempty Q
  haveI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := hWgeom.isFiniteMeasure_restrict_volume
  obtain ⟨g, hgmem, hg⟩ :=
    exists_memVectorL2_integral_mul_eq_integral_vecDot (W := openCubeSet Q) hWgeom hf
  have hDatumFlux :
      MemVectorL2 (openCubeSet Q) (fun x => matVecMul (a x) (hD.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hD.grad_memVectorL2
  have hG :
      MemVectorL2 (openCubeSet Q) (fun x => g x - matVecMul (a x) (hD.grad x)) :=
    hgmem.sub hDatumFlux
  have hRealize :
      PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization
        (openCubeSet Q) :=
    PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
      hWgeom
  obtain ⟨w, hw⟩ :=
    exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
      (a := a) (U := openCubeSet Q) (g := fun x => g x - matVecMul (a x) (hD.grad x))
      (lam := lam) (Lam := Lam) hG hRealize hne hEll
  refine ⟨hD + w.toH1Function, ⟨w, fun _ => rfl, fun _ => rfl⟩, fun φ => ?_⟩
  have hDatumInt :
      IntegrableOn
        (fun x => vecDot (matVecMul (a x) (hD.grad x)) (φ.toH1Function.grad x))
        (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hDatumFlux φ.toH1Function.grad_memVectorL2
  have hCorrFlux :
      MemVectorL2 (openCubeSet Q) (fun x => matVecMul (a x) (w.toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll w.toH1Function.grad_memVectorL2
  have hCorrInt :
      IntegrableOn
        (fun x => vecDot (matVecMul (a x) (w.toH1Function.grad x))
          (φ.toH1Function.grad x)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hCorrFlux φ.toH1Function.grad_memVectorL2
  have hgInt :
      IntegrableOn (fun x => vecDot (g x) (φ.toH1Function.grad x)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hgmem φ.toH1Function.grad_memVectorL2
  have hsplit :
      (fun x => vecDot (matVecMul (a x) ((hD + w.toH1Function).grad x))
          (φ.toH1Function.grad x)) =
        fun x =>
          vecDot (matVecMul (a x) (hD.grad x)) (φ.toH1Function.grad x) +
            vecDot (matVecMul (a x) (w.toH1Function.grad x))
              (φ.toH1Function.grad x) := by
    funext x
    simp [H1Function.add_grad, matVecMul_add, vecDot_add_left]
  have hsub :
      (fun x => vecDot (g x - matVecMul (a x) (hD.grad x)) (φ.toH1Function.grad x)) =
        fun x =>
          vecDot (g x) (φ.toH1Function.grad x) -
            vecDot (matVecMul (a x) (hD.grad x)) (φ.toH1Function.grad x) := by
    funext x
    simp [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
  have hwφ := hw φ
  rw [hsub, integral_sub hgInt hDatumInt] at hwφ
  show ∫ x in openCubeSet Q, vecDot (matVecMul (a x) ((hD + w.toH1Function).grad x))
      (φ.toH1Function.grad x) ∂volume = _
  rw [hsplit, integral_add hDatumInt hCorrInt, hwφ, hg φ]
  ring

/-- **Existence for the constant coefficient `1`.**  This is the clause
`∃ uHom, IsScalarDirichletSolutionOn (fun _ ↦ 1) ...` of the two section 6
Dirichlet theorems. -/
theorem exists_isScalarDirichletSolutionOn_one {d : ℕ} [NeZero d]
    {Q : TriadicCube d} (hD : H1Function (openCubeSet Q)) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (openCubeSet Q))) :
    ∃ u : H1Function (openCubeSet Q),
      IsScalarDirichletSolutionOn (fun _ => (1 : Mat d)) Q u hD f := by
  have hEll :
      IsEllipticFieldOn (1 : ℝ) (1 : ℝ) (openCubeSet Q) (fun _ => (1 : Mat d)) := by
    have h :=
      isEllipticFieldOn_scalarCoeffField_const (W := openCubeSet Q) (sigma := 1)
        (isOpenBoundedConvexDomain_openCubeSet Q).isOpen.measurableSet one_pos
    rwa [scalarCoeffField_one] at h
  exact exists_isScalarDirichletSolutionOn hEll hD hf

end

end SubdiffusiveProcess.CoarseGrainingVocab
