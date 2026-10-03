module

public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredPartialSum
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import Mathlib.Tactic
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.TestSubmodule
public import SubdiffusiveProcess.Lane4.Inputs
public import Mathlib.Analysis.Matrix.Normed
public import SubdiffusiveProcess.Lane3.RelativeConcentration
public import SubdiffusiveProcess.Sobolev.CompactResponses
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import Mathlib.Probability.ProductMeasure
public import SubdiffusiveProcess.Sobolev.ReflectionResponses
public import SubdiffusiveProcess.Lane4.Scaling
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletMatrixBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletInfimumCovariance
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.CellSymmetry.Swap

@[expose] public section




open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators Pointwise ContDiff Distributions

noncomputable section
namespace SubdiffusiveProcess
namespace CellSymmetry


section
variable {d : ℕ}

def cs_lc_reflAct (i : Fin d) (N : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun a b => (if a = i then -(1 : ℝ) else 1) * (if b = i then -(1 : ℝ) else 1) * N a b

theorem cs_lc_reflAct_diag (i a : Fin d) (N : Matrix (Fin d) (Fin d) ℝ) :
    cs_lc_reflAct i N a a = N a a := by
  unfold cs_lc_reflAct
  rcases eq_or_ne a i with h | h <;> simp [h]

theorem cs_lc_reflAct_symm (i : Fin d) {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.transpose = A) :
    (cs_lc_reflAct i A).transpose = cs_lc_reflAct i A := by
  have hsym : ∀ a b, A b a = A a b := by
    intro a b
    have h := congrFun (congrFun hA a) b
    simpa [Matrix.transpose_apply] using h
  funext a b
  simp only [Matrix.transpose_apply, cs_lc_reflAct]
  rw [hsym]; ring

theorem cs_lc_reflAct_trace (i : Fin d) (A : Matrix (Fin d) (Fin d) ℝ) :
    (cs_lc_reflAct i A).trace = A.trace := by
  unfold Matrix.trace Matrix.diag
  exact Finset.sum_congr rfl (fun a _ => cs_lc_reflAct_diag i a A)

theorem cs_lc_reflAct_quadForm (i : Fin d) (A : Matrix (Fin d) (Fin d) ℝ) (p : Fin d → ℝ) :
    p ⬝ᵥ (cs_lc_reflAct i A).mulVec p =
      (fun a => (if a = i then -(1 : ℝ) else 1) * p a) ⬝ᵥ
        A.mulVec (fun a => (if a = i then -(1 : ℝ) else 1) * p a) := by
  simp only [dotProduct, Matrix.mulVec, cs_lc_reflAct,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rcases eq_or_ne a i with ha | ha <;> rcases eq_or_ne b i with hb | hb <;> simp [ha, hb]

def cs_lc_permAct (σ : Equiv.Perm (Fin d)) (N : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun a b => N (σ a) (σ b)

theorem cs_lc_permAct_symm (σ : Equiv.Perm (Fin d)) {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.transpose = A) :
    (cs_lc_permAct σ A).transpose = cs_lc_permAct σ A := by
  have hsym : ∀ a b, A b a = A a b := by
    intro a b
    have h := congrFun (congrFun hA a) b
    simpa [Matrix.transpose_apply] using h
  funext a b
  simp only [Matrix.transpose_apply, cs_lc_permAct]
  rw [hsym]

theorem cs_lc_permAct_submatrix (σ : Equiv.Perm (Fin d)) (A : Matrix (Fin d) (Fin d) ℝ) :
    cs_lc_permAct σ A = A.submatrix (⇑σ) (⇑σ) := rfl

theorem cs_lc_swapAct_quadForm (a b : Fin d) (A : Matrix (Fin d) (Fin d) ℝ)
    (p : Fin d → ℝ) :
    p ⬝ᵥ (cs_lc_permAct (Equiv.swap a b) A).mulVec p =
      (p ∘ Equiv.swap a b) ⬝ᵥ A.mulVec (p ∘ Equiv.swap a b) := by
  rw [cs_lc_permAct_submatrix, Matrix.submatrix_mulVec_equiv, Equiv.symm_swap]
  rw [← comp_equiv_symm_dotProduct p (A.mulVec (p ∘ ⇑(Equiv.swap a b))) (Equiv.swap a b),
    Equiv.symm_swap]

theorem cs_lc_matrix_entry_measurable {d : ℕ} {X : Type*} [MeasurableSpace X]
    {g : X → Matrix (Fin d) (Fin d) ℝ} (hg : Measurable g) (i j : Fin d) :
    Measurable (fun x => g x i j) := by
  have h1 : Measurable (fun x => g x i) := (measurable_pi_apply i).comp hg
  exact (measurable_pi_apply j).comp h1

theorem cs_lc_trace_measurable {d : ℕ} {X : Type*} [MeasurableSpace X]
    {g : X → Matrix (Fin d) (Fin d) ℝ} (hg : Measurable g) :
    Measurable (fun x => Matrix.trace (g x)) := by
  unfold Matrix.trace Matrix.diag
  exact Finset.measurable_sum _ fun i _ => cs_lc_matrix_entry_measurable hg i i

theorem cs_lc_normpair_measurable {d : ℕ} {X : Type*} [MeasurableSpace X]
    {gE gF : X → Matrix (Fin d) (Fin d) ℝ} (hgE : Measurable gE) (hgF : Measurable gF) :
    Measurable (fun x => cs_lc_normpair (gE x) (gF x)) := by
  unfold cs_lc_normpair
  apply Measurable.prodMk
  · exact Measurable.of_eval fun j => Measurable.of_eval fun l =>
      (cs_lc_matrix_entry_measurable hgE j l).div (cs_lc_trace_measurable hgE)
  · exact Measurable.of_eval fun j => Measurable.of_eval fun l =>
      (cs_lc_matrix_entry_measurable hgF j l).div (cs_lc_trace_measurable hgE)

theorem cs_lc_reflpair_measurable {d : ℕ} {X : Type*} [MeasurableSpace X]
    {XY : X → (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)} (hXY : Measurable XY) (i : Fin d) :
    Measurable (fun x => cs_lc_reflpair i (XY x)) := by
  unfold cs_lc_reflpair
  exact Measurable.prodMk
    (Measurable.of_eval fun a => Measurable.of_eval fun b =>
      measurable_const.mul ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp hXY.fst)))
    (Measurable.of_eval fun a => Measurable.of_eval fun b =>
      measurable_const.mul ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp hXY.snd)))

theorem cs_lc_permpair_measurable {d : ℕ} {X : Type*} [MeasurableSpace X]
    {XY : X → (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)} (hXY : Measurable XY)
    (σ : Equiv.Perm (Fin d)) :
    Measurable (fun x => cs_lc_permpair σ (XY x)) := by
  unfold cs_lc_permpair
  exact Measurable.prodMk
    (Measurable.of_eval fun a => Measurable.of_eval fun b =>
      (measurable_pi_apply (σ b)).comp ((measurable_pi_apply (σ a)).comp hXY.fst))
    (Measurable.of_eval fun a => Measurable.of_eval fun b =>
      (measurable_pi_apply (σ b)).comp ((measurable_pi_apply (σ a)).comp hXY.snd))

theorem cs_lc_normpair_smul {d : ℕ} (c : ℝ) (hc : c ≠ 0)
    (A B : Matrix (Fin d) (Fin d) ℝ) :
    cs_lc_normpair (c • A) (c • B) = cs_lc_normpair A B := by
  unfold cs_lc_normpair
  rw [Matrix.trace_smul, smul_eq_mul]
  refine Prod.ext ?_ ?_ <;> funext j l <;>
    simp only [Matrix.smul_apply, smul_eq_mul] <;> exact mul_div_mul_left _ _ hc

theorem cs_lc_normpair_permAct {d : ℕ} (σ : Equiv.Perm (Fin d))
    (A B : Matrix (Fin d) (Fin d) ℝ) :
    cs_lc_normpair (cs_lc_permAct σ A) (cs_lc_permAct σ B) =
      cs_lc_permpair σ (cs_lc_normpair A B) := by
  have htr : (cs_lc_permAct σ A).trace = A.trace := by
    unfold Matrix.trace Matrix.diag cs_lc_permAct
    exact Equiv.sum_comp σ (fun c => A c c)
  unfold cs_lc_normpair cs_lc_permpair
  rw [htr]
  rfl

theorem cs_lc_normpair_reflAct {d : ℕ} (i : Fin d) (A B : Matrix (Fin d) (Fin d) ℝ) :
    cs_lc_normpair (cs_lc_reflAct i A) (cs_lc_reflAct i B) =
      cs_lc_reflpair i (cs_lc_normpair A B) := by
  simp only [cs_lc_normpair, cs_lc_reflpair, cs_lc_reflAct_trace]
  refine Prod.ext ?_ ?_ <;> funext j l <;>
    simp only [cs_lc_reflAct, cs_lc_sign] <;> ring

def cs_lc_reflLinear (i : Fin d) :
    Matrix (Fin d) (Fin d) ℝ →L[ℝ] Matrix (Fin d) (Fin d) ℝ where
  toFun := cs_lc_reflAct i
  map_add' := by
    intro A B
    ext a b
    simp only [cs_lc_reflAct, Matrix.add_apply]
    ring
  map_smul' := by
    intro c A
    ext a b
    simp only [cs_lc_reflAct, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
  cont := continuous_pi fun a => continuous_pi fun b =>
    continuous_const.mul ((continuous_apply b).comp (continuous_apply a))

def cs_lc_permLinear (s : Equiv.Perm (Fin d)) :
    Matrix (Fin d) (Fin d) ℝ →L[ℝ] Matrix (Fin d) (Fin d) ℝ where
  toFun := cs_lc_permAct s
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  cont := continuous_pi fun a => continuous_pi fun b =>
    (continuous_apply (s b)).comp (continuous_apply (s a))

/-- Law invariance under transpositions gives law invariance under all
coordinate permutations for an arbitrary measurable random matrix pair. -/
theorem cs_lc_perm_law_of_swaps
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ))
    (hX : AEMeasurable X P)
    (hswap : ∀ a b, P.map X = P.map (fun x => cs_lc_permpair (Equiv.swap a b) (X x))) :
    ∀ s : Equiv.Perm (Fin d), P.map X =
      P.map (fun x => cs_lc_permpair s (X x)) := by
  intro s
  induction s using Equiv.Perm.swap_induction_on with
  | one =>
    have h : (fun x => cs_lc_permpair (1 : Equiv.Perm (Fin d)) (X x)) = X := by
      funext x
      simp only [cs_lc_permpair, Equiv.Perm.one_apply]
    rw [h]
  | swap_mul s a b _ ih =>
    have hs : Measurable (cs_lc_permpair (d := d) s) :=
      cs_lc_permpair_measurable measurable_id s
    have hsw : Measurable (cs_lc_permpair (d := d) (Equiv.swap a b)) :=
      cs_lc_permpair_measurable measurable_id (Equiv.swap a b)
    have hcomp : (fun x => cs_lc_permpair (Equiv.swap a b * s) (X x)) =
        cs_lc_permpair s ∘
          (fun x => cs_lc_permpair (Equiv.swap a b) (X x)) := by
      funext x
      simp only [Function.comp_apply, cs_lc_permpair, Equiv.Perm.mul_apply]
    have hSX : AEMeasurable
        (fun x => cs_lc_permpair (Equiv.swap a b) (X x)) P :=
      hsw.comp_aemeasurable hX
    rw [hcomp, ← AEMeasurable.map_map_of_aemeasurable hs.aemeasurable hSX,
      ← hswap a b]
    exact ih.trans (AEMeasurable.map_map_of_aemeasurable hs.aemeasurable hX).symm

def cs_lc_reflSign (a : Fin d) (i : Fin d) : ℝ := if i = a then -1 else 1

theorem cs_lc_refl_isSigned (a : Fin d) :
    IsSignedPermutationMatrix (Matrix.diagonal (cs_lc_reflSign a) : Homogenization.Mat d) := by
  refine ⟨Equiv.refl _, cs_lc_reflSign a, fun i => ?_, fun i j => ?_⟩
  · unfold cs_lc_reflSign
    split_ifs <;> simp
  · simp only [Matrix.diagonal_apply, Equiv.refl_apply]
    split_ifs with h
    · subst h; simp
    · simp [h]

def cs_lc_swapMat (a b : Fin d) : Homogenization.Mat d :=
  fun i j => if i = Equiv.swap a b j then 1 else 0

theorem cs_lc_swap_isSigned (a b : Fin d) :
    IsSignedPermutationMatrix (cs_lc_swapMat a b) :=
  ⟨Equiv.swap a b, fun _ => 1, fun _ => Or.inl rfl, fun _ _ => rfl⟩

theorem cs_lc_matVecMul_refl (a : Fin d) (y : SpatialCoordinates d) (i : Fin d) :
    matVecMul (Matrix.diagonal (cs_lc_reflSign a) : Homogenization.Mat d) y i =
      cs_lc_reflSign a i * y i := by
  simp only [matVecMul, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

theorem cs_lc_matVecMul_swap (a b : Fin d) (y : SpatialCoordinates d) (i : Fin d) :
    matVecMul (cs_lc_swapMat a b) y i = y (Equiv.swap a b i) := by
  simp only [matVecMul, cs_lc_swapMat]
  rw [Finset.sum_eq_single (Equiv.swap a b i)]
  · simp
  · intro j _ hj
    rw [if_neg]
    · ring
    · intro h
      apply hj
      rw [h, Equiv.swap_apply_self]
  · simp

theorem cs_lc_cpc_coeFn (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (x : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {s : ℝ} (hs : 0 < s) :
    ∀ᵐ y ∂volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d)),
      y ∈ (centeredCube z s hs : Set (SpatialCoordinates d)) →
      (Lane4.cutoffPositiveCoefficient model H x N z hs).val y =
        cutoffCoefficient model H x N y := by
  haveI : Fact ((centeredCube z s hs : Set (SpatialCoordinates d)) ⊆ closedCube z s hs) :=
    ⟨centeredCube_subset_closedCube z hs⟩
  filter_upwards [normalizedContinuousPositiveCoefficient_coeFn (Ω := centeredCube z s hs)
    (closedCube z s hs) (Lane4.cutoffCoefficientCM model H x N z hs)
    (Lane4.cutoffCoefficientCM_pos model H x N z hs) 1 one_pos] with y hy hmem
  have h := hy hmem
  rw [div_one] at h
  exact h

theorem cs_lc_cpc_transform (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (x x' : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {s : ℝ} (hs : 0 < s)
    (π : SpatialCoordinates d → SpatialCoordinates d)
    (hmp : MeasurePreserving π (volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d)))
      (volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))))
    (hmaps : ∀ y ∈ (centeredCube z s hs : Set (SpatialCoordinates d)),
      π y ∈ (centeredCube z s hs : Set (SpatialCoordinates d)))
    (piCoef : PositiveCoefficient (centeredCube z s hs) →
      PositiveCoefficient (centeredCube z s hs))
    (hpi : ∀ a : PositiveCoefficient (centeredCube z s hs),
      ((piCoef a).val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))] a.val ∘ π)
    (c : ℝ)
    (hcoef : ∀ y, cutoffCoefficient model H x' N y =
      Real.exp (-c) * cutoffCoefficient model H x N (π y)) :
    Lane4.cutoffPositiveCoefficient model H x' N z hs =
      smulPositiveCoefficient (Real.exp_pos (-c))
        (piCoef (Lane4.cutoffPositiveCoefficient model H x N z hs)) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [cs_lc_cpc_coeFn model H x' N z hs,
    smulPositiveCoefficient_coeFn (Real.exp_pos (-c))
      (piCoef (Lane4.cutoffPositiveCoefficient model H x N z hs)),
    hpi (Lane4.cutoffPositiveCoefficient model H x N z hs),
    hmp.quasiMeasurePreserving.ae (cs_lc_cpc_coeFn model H x N z hs),
    ae_restrict_mem (centeredCube z s hs).isOpen.measurableSet] with y e1 e2 e3 e4 hy
  change (Lane4.cutoffPositiveCoefficient model H x' N z hs).val y =
    (smulPositiveCoefficient (Real.exp_pos (-c))
      (piCoef (Lane4.cutoffPositiveCoefficient model H x N z hs))).val y
  rw [e1 hy, e2, e3, Function.comp_apply, e4 (hmaps y hy), hcoef]

def cs_lc_reflShift (z : SpatialCoordinates d) (a : Fin d) : SpatialCoordinates d :=
  fun i => if i = a then 2 * z i else 0

theorem cs_lc_affineMap_refl (z : SpatialCoordinates d) (a : Fin d)
    (y : SpatialCoordinates d) :
    cs_affineMap (Matrix.diagonal (cs_lc_reflSign a))
      (cs_lc_reflShift z a) y = coordinateReflection z {a} y := by
  funext i
  rw [cs_affineMap_apply, Pi.add_apply, cs_lc_matVecMul_refl]
  simp only [cs_lc_reflSign, cs_lc_reflShift, coordinateReflection,
    Finset.mem_singleton]
  split_ifs <;> ring

def cs_lc_swapShift (z : SpatialCoordinates d) (a b : Fin d) : SpatialCoordinates d :=
  fun i => z i - z (Equiv.swap a b i)

theorem cs_lc_affineMap_swap (z : SpatialCoordinates d) (a b : Fin d)
    (y : SpatialCoordinates d) :
    cs_affineMap (cs_lc_swapMat a b) (cs_lc_swapShift z a b) y =
      cs_lc_swap z a b y := by
  funext i
  rw [cs_affineMap_apply, Pi.add_apply, cs_lc_matVecMul_swap]
  simp only [cs_lc_swapShift, cs_lc_swap]
  ring

theorem cs_lc_refl_self (z : SpatialCoordinates d) (a : Fin d) :
    coordinateReflection z {a} z = z := by
  funext i
  simp only [coordinateReflection]
  split_ifs <;> ring

theorem cs_lc_refl_preimage_cube (z : SpatialCoordinates d) (a : Fin d) {s : ℝ}
    (hs : 0 < s) :
    coordinateReflection z {a} ⁻¹' (centeredCube z s hs : Set (SpatialCoordinates d)) =
      (centeredCube z s hs : Set (SpatialCoordinates d)) := by
  have h := coordinateReflection_preimage_cube z {a} z hs
  rwa [cs_lc_refl_self] at h

def cs_lc_response
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (zcell : SpatialCoordinates d) {s : ℝ} (hs : 0 < s)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube zcell s hs),
      ‖(u : SobolevData (centeredCube zcell s hs)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell s hs)) u‖)
    (N : ℕ) (x : BilateralField d) (p : Fin d → ℝ) : ℝ :=
  affineDirichletResponse (centeredCube_isBounded zcell hs) hP
    (Lane4.cutoffPositiveCoefficient model H x N zcell hs) p /
      (volume (centeredCube zcell s hs : Set (SpatialCoordinates d))).toReal

theorem cs_lc_resp_refl (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (zcell : SpatialCoordinates d)
    {s : ℝ} (hs : 0 < s)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube zcell s hs),
      ‖(u : SobolevData (centeredCube zcell s hs)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell s hs)) u‖)
    (a : Fin d) (x : BilateralField d)
    (hH : H (cs_T (Matrix.diagonal (cs_lc_reflSign a))
        (cs_lc_reflShift zcell a) x) =
      cs_gauge (Matrix.diagonal (cs_lc_reflSign a))
        (cs_lc_reflShift zcell a) (H x))
    (N : ℕ) (p : Fin d → ℝ) :
    cs_lc_response model H zcell hs hP N
        (cs_T (Matrix.diagonal (cs_lc_reflSign a))
          (cs_lc_reflShift zcell a) x) p =
      Real.exp (-(H x (cs_affineMap (Matrix.diagonal (cs_lc_reflSign a))
          (cs_lc_reflShift zcell a) 0))) *
        cs_lc_response model H zcell hs hP N x (coordinateReflectionDerivative {a} p) := by
  have hU := cs_lc_refl_preimage_cube zcell a hs
  have hcpc := cs_lc_cpc_transform model H x
    (cs_T (Matrix.diagonal (cs_lc_reflSign a))
      (cs_lc_reflShift zcell a) x) N zcell hs (coordinateReflection zcell {a})
    (coordinateReflection_domain_measurePreserving zcell {a} hU)
    (fun y hy => by rw [← hU] at hy; exact hy)
    (reflectionCoefficient zcell {a} hU) (fun c => reflectionCoefficient_coeFn zcell {a} hU c)
    (H x (cs_affineMap (Matrix.diagonal (cs_lc_reflSign a))
      (cs_lc_reflShift zcell a) 0))
    (fun y => by
      rw [cs_cutoffCoefficient_T model _ _ H x hH N y,
        cs_lc_affineMap_refl zcell a y])
  unfold cs_lc_response
  rw [hcpc, affineDirichletResponse_smulCoeff, mul_div_assoc]
  congr 2
  have h := affineDirichletResponse_reflection zcell {a} hU (centeredCube_isBounded zcell hs)
    (centeredCube_isBounded zcell hs) hP hP
    (Lane4.cutoffPositiveCoefficient model H x N zcell hs) (coordinateReflectionDerivative {a} p)
  rwa [coordinateReflectionDerivative_involutive] at h

theorem cs_lc_resp_swap (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (zcell : SpatialCoordinates d)
    {s : ℝ} (hs : 0 < s)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube zcell s hs),
      ‖(u : SobolevData (centeredCube zcell s hs)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell s hs)) u‖)
    (a b : Fin d) (x : BilateralField d)
    (hH : H (cs_T (cs_lc_swapMat a b) (cs_lc_swapShift zcell a b) x) =
      cs_gauge (cs_lc_swapMat a b) (cs_lc_swapShift zcell a b) (H x))
    (N : ℕ) (p : Fin d → ℝ) :
    cs_lc_response model H zcell hs hP N
        (cs_T (cs_lc_swapMat a b) (cs_lc_swapShift zcell a b) x) p =
      Real.exp (-(H x (cs_affineMap (cs_lc_swapMat a b)
          (cs_lc_swapShift zcell a b) 0))) *
        cs_lc_response model H zcell hs hP N x (p ∘ Equiv.swap a b) := by
  have hU := cs_lc_swap_preimage_cube zcell a b hs
  have hcpc := cs_lc_cpc_transform model H x
    (cs_T (cs_lc_swapMat a b) (cs_lc_swapShift zcell a b) x) N zcell hs
    (cs_lc_swap zcell a b)
    (cs_lc_swap_domain_measurePreserving zcell a b hU)
    (fun y hy => by rw [← hU] at hy; exact hy)
    (cs_lc_swapCoefficient zcell a b hU)
    (fun c => cs_lc_swapCoefficient_coeFn zcell a b hU c)
    (H x (cs_affineMap (cs_lc_swapMat a b)
      (cs_lc_swapShift zcell a b) 0))
    (fun y => by
      rw [cs_cutoffCoefficient_T model _ _ H x hH N y,
        cs_lc_affineMap_swap zcell a b y])
  unfold cs_lc_response
  rw [hcpc, affineDirichletResponse_smulCoeff, mul_div_assoc]
  congr 2
  have h := cs_lc_affineDirichletResponse_swap zcell a b hU
    (centeredCube_isBounded zcell hs) (centeredCube_isBounded zcell hs) hP hP
    (Lane4.cutoffPositiveCoefficient model H x N zcell hs) (p ∘ Equiv.swap a b)
  have hpp : (p ∘ Equiv.swap a b) ∘ Equiv.swap a b = p := by
    funext i
    simp [Equiv.swap_apply_self]
  rwa [hpp] at h

end

theorem cs_lc_field_symmetry_preserving {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (R : Homogenization.Mat d) (hR : IsSignedPermutationMatrix R) (w : SpatialCoordinates d) :
    MeasurePreserving (cs_T R w)
      (chaosSampleLaw model).toMeasure (chaosSampleLaw model).toMeasure :=
  ⟨Measurable.of_eval (fun j =>
    (cs_precomp_measurable R w).comp (measurable_pi_apply j)),
    cs_chaos_invariant model R hR w⟩

theorem cs_lc_matrix_transform {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℝ) (hA : A.transpose = A)
    (L : Matrix (Fin d) (Fin d) ℝ →L[ℝ] Matrix (Fin d) (Fin d) ℝ)
    (hL : (L B).transpose = L B) (c : ℝ)
    (h : ∀ p : Fin d → ℝ, p ⬝ᵥ A.mulVec p = c * (p ⬝ᵥ (L B).mulVec p)) :
    A = c • L B := by
  apply cs_symmetric_matrix_ext hA
    (by rw [Matrix.transpose_smul, hL])
  intro p
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  exact h p

section
variable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (zcell : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube zcell r hr),
      ‖(u : SobolevData (centeredCube zcell r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell r hr)) u‖)

/-- Normalized matrix laws at one physical cube, obtained directly from its
two cutoff response sequences. No other cube or scale is in the hypotheses. -/
theorem cs_lc_one_cell_pair_law
    (hH : Measurable H) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (field : Ω → BilateralField d)
    (hfield : Measurable field) (hlaw : P.map field = (chaosSampleLaw model).toMeasure)
    (NE NF : ℕ → ℕ) (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hsymE : ∀ om, (AE om).transpose = AE om)
    (hsymF : ∀ om, (AF om).transpose = AF om)
    (hAE : ∀ᵐ om ∂P, cs_affine_converges model H (field om) zcell r hr NE hP (AE om))
    (hAF : ∀ᵐ om ∂P, cs_affine_converges model H (field om) zcell r hr NF hP (AF om))
    (T : BilateralField d → BilateralField d)
    (hT : MeasurePreserving T (chaosSampleLaw model).toMeasure (chaosSampleLaw model).toMeasure)
    (L : Matrix (Fin d) (Fin d) ℝ →L[ℝ] Matrix (Fin d) (Fin d) ℝ)
    (hLsym : ∀ A : Matrix (Fin d) (Fin d) ℝ, A.transpose = A → (L A).transpose = L A)
    (slope : (Fin d → ℝ) → (Fin d → ℝ))
    (hLquad : ∀ (A : Matrix (Fin d) (Fin d) ℝ) p,
      p ⬝ᵥ (L A).mulVec p = slope p ⬝ᵥ A.mulVec (slope p))
    (c : BilateralField d → ℝ)
    (hcov : ∀ᵐ x ∂(chaosSampleLaw model).toMeasure, c x ≠ 0 ∧ ∀ N p,
      cs_lc_response model H zcell hr hP N (T x) p =
        c x * cs_lc_response model H zcell hr hP N x (slope p))
    (S : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ) →
      (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ))
    (hS : Measurable S)
    (hNS : ∀ A B, cs_lc_normpair (L A) (L B) = S (cs_lc_normpair A B)) :
    P.map (fun om => cs_lc_normpair (AE om) (AF om)) =
      P.map (fun om => S (cs_lc_normpair (AE om) (AF om))) := by
  let AN := cs_cutoff_affine_matrix model H zcell hr hP
  have hAN : ∀ N, Measurable (AN N) :=
    cs_cutoff_affine_matrix_measurable model H hH zcell hr hP
  have hANE : ∀ᵐ om ∂P, Tendsto (fun n => AN (NE n) (field om)) atTop (𝓝 (AE om)) :=
    hAE.mono fun om h => cs_polar_matrix_limit _ _ (hsymE om) h
  have hANF : ∀ᵐ om ∂P, Tendsto (fun n => AN (NF n) (field om)) atTop (𝓝 (AF om)) :=
    hAF.mono fun om h => cs_polar_matrix_limit _ _ (hsymF om) h
  have hmatcov : ∀ᵐ x ∂(chaosSampleLaw model).toMeasure, c x ≠ 0 ∧
      ∀ N, AN N (T x) = c x • L (AN N x) := by
    filter_upwards [hcov] with x hc
    refine ⟨hc.1, fun N => ?_⟩
    have hsym : ∀ y, (AN N y).transpose = AN N y :=
      fun y => cs_polar_matrix_symmetric _
    apply cs_lc_matrix_transform _ _ (hsym _) L (hLsym _ (hsym _))
    intro p
    rw [hLquad]
    exact (cs_cutoff_affine_matrix_quadratic model H zcell hr hP N (T x) p).trans
      ((hc.2 N p).trans (congrArg (c x * ·)
        (cs_cutoff_affine_matrix_quadratic model H zcell hr hP N x (slope p)).symm))
  exact cs_matrix_pair_law P (chaosSampleLaw model).toMeasure field hfield hlaw T hT
    (fun n => AN (NE n)) (fun n => AN (NF n)) (fun n => hAN (NE n)) (fun n => hAN (NF n))
    AE AF hANE hANF L c
    (hmatcov.mono fun x h => ⟨h.1, fun n => ⟨h.2 (NE n), h.2 (NF n)⟩⟩)
    (fun AB => cs_lc_normpair AB.1 AB.2)
    (cs_lc_normpair_measurable measurable_fst measurable_snd) S hS
    (fun A B t ht => cs_lc_normpair_smul t ht A B) hNS

end

section
variable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hIR : InfraredCharacterization model H)
    (zcell : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube zcell r hr),
      ‖(u : SobolevData (centeredCube zcell r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube zcell r hr)) u‖)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (field : Ω → BilateralField d)
    (hfield : Measurable field) (hlaw : P.map field = (chaosSampleLaw model).toMeasure)
    (NE NF : ℕ → ℕ) (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hsymE : ∀ om, (AE om).transpose = AE om)
    (hsymF : ∀ om, (AF om).transpose = AF om)
    (hAE : ∀ᵐ om ∂P, cs_affine_converges model H (field om) zcell r hr NE hP (AE om))
    (hAF : ∀ᵐ om ∂P, cs_affine_converges model H (field om) zcell r hr NF hP (AF om))
include hIR hfield hlaw hsymE hsymF hAE hAF

theorem cs_lc_one_cell_refl_law (a : Fin d) :
    P.map (fun om => cs_lc_normpair (AE om) (AF om)) =
      P.map (fun om => cs_lc_reflpair a (cs_lc_normpair (AE om) (AF om))) := by
  let R : Homogenization.Mat d := Matrix.diagonal (cs_lc_reflSign a)
  let w := cs_lc_reflShift zcell a
  have hT := cs_lc_field_symmetry_preserving model R
    (cs_lc_refl_isSigned a) w
  have hquad (A : Matrix (Fin d) (Fin d) ℝ) (p : Fin d → ℝ) :
      p ⬝ᵥ ((cs_lc_reflLinear a) A).mulVec p =
        coordinateReflectionDerivative {a} p ⬝ᵥ A.mulVec (coordinateReflectionDerivative {a} p) := by
    have hslope : coordinateReflectionDerivative {a} p =
        (fun i => (if i = a then -(1 : ℝ) else 1) * p i) := by
      funext i
      simp only [coordinateReflectionDerivative_apply, coordinateReflectionSign,
        Finset.mem_singleton]
    rw [hslope]
    exact cs_lc_reflAct_quadForm a A p
  apply cs_lc_one_cell_pair_law model H zcell hr hP hIR.1 P field hfield hlaw
    NE NF AE AF hsymE hsymF hAE hAF (cs_T R w) hT
    (cs_lc_reflLinear a) (fun A hA => cs_lc_reflAct_symm a hA)
    (coordinateReflectionDerivative {a})
    hquad (fun x => Real.exp (-(H x (cs_affineMap R w 0))))
    ?_ (cs_lc_reflpair a)
    (cs_lc_reflpair_measurable measurable_id a)
    (fun A B => cs_lc_normpair_reflAct a A B)
  filter_upwards [hIR.2, hT.quasiMeasurePreserving.ae hIR.2] with x hx hTx
  exact ⟨Real.exp_ne_zero _, fun N p =>
    cs_lc_resp_refl model H zcell hr hP a x
      (cs_H_T R w H x hx hTx) N p⟩

theorem cs_lc_one_cell_swap_law (a b : Fin d) :
    P.map (fun om => cs_lc_normpair (AE om) (AF om)) =
      P.map (fun om => cs_lc_permpair (Equiv.swap a b)
        (cs_lc_normpair (AE om) (AF om))) := by
  let R : Homogenization.Mat d := cs_lc_swapMat a b
  let w := cs_lc_swapShift zcell a b
  have hT := cs_lc_field_symmetry_preserving model R
    (cs_lc_swap_isSigned a b) w
  apply cs_lc_one_cell_pair_law model H zcell hr hP hIR.1 P field hfield hlaw
    NE NF AE AF hsymE hsymF hAE hAF (cs_T R w) hT
    (cs_lc_permLinear (Equiv.swap a b))
    (fun A hA => cs_lc_permAct_symm (Equiv.swap a b) hA)
    (fun p => p ∘ Equiv.swap a b)
    (cs_lc_swapAct_quadForm a b)
    (fun x => Real.exp (-(H x (cs_affineMap R w 0))))
    ?_ (cs_lc_permpair (Equiv.swap a b))
    (cs_lc_permpair_measurable measurable_id (Equiv.swap a b))
    (fun A B => cs_lc_normpair_permAct (Equiv.swap a b) A B)
  filter_upwards [hIR.2, hT.quasiMeasurePreserving.ae hIR.2] with x hx hTx
  exact ⟨Real.exp_ne_zero _, fun N p =>
    cs_lc_resp_swap model H zcell hr hP a b x
      (cs_H_T R w H x hx hTx) N p⟩

/-- Signed-permutation invariance of the actual normalized limiting pair on
one cell. Its hypotheses mention no observation family at other scales. -/
theorem cs_lc_one_cell_laws :
    (∀ a : Fin d, P.map (fun om => cs_lc_normpair (AE om) (AF om)) =
      P.map (fun om => cs_lc_reflpair a (cs_lc_normpair (AE om) (AF om)))) ∧
    (∀ s : Equiv.Perm (Fin d), P.map (fun om => cs_lc_normpair (AE om) (AF om)) =
      P.map (fun om => cs_lc_permpair s (cs_lc_normpair (AE om) (AF om)))) := by
  have hmeasE := cs_matrix_limit_aemeasurable P
    (fun n om p => cs_lc_response model H zcell hr hP (NE n) (field om) p)
    (fun n p => ((cs_affine_response_measurable model H hIR.1 (NE n) zcell hr hP p).div_const _).comp hfield) AE hsymE hAE
  have hmeasF := cs_matrix_limit_aemeasurable P
    (fun n om p => cs_lc_response model H zcell hr hP (NF n) (field om) p)
    (fun n p => ((cs_affine_response_measurable model H hIR.1 (NF n) zcell hr hP p).div_const _).comp hfield) AF hsymF hAF
  have hmatE : AEMeasurable AE P := aemeasurable_pi_lambda fun i => aemeasurable_pi_lambda (hmeasE i)
  have hmatF : AEMeasurable AF P := aemeasurable_pi_lambda fun i => aemeasurable_pi_lambda (hmeasF i)
  have hX : AEMeasurable (fun om => cs_lc_normpair (AE om) (AF om)) P :=
    (cs_lc_normpair_measurable measurable_fst measurable_snd).comp_aemeasurable
      (hmatE.prodMk hmatF)
  exact ⟨cs_lc_one_cell_refl_law model H hIR zcell hr hP P field hfield hlaw
      NE NF AE AF hsymE hsymF hAE hAF,
    cs_lc_perm_law_of_swaps P _ hX
      (cs_lc_one_cell_swap_law model H hIR zcell hr hP P field hfield hlaw
        NE NF AE AF hsymE hsymF hAE hAF)⟩

end

end CellSymmetry
end SubdiffusiveProcess
