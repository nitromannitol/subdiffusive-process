module

public import SubdiffusiveProcess.Section10.RetainedPrefixCoefficient
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerInduction

@[expose] public section

/-!
# One-new-layer factorization for the arbitrary-start sparse induction

The concrete consumer is the product of the new shell's cell supremum and
the preceding retained coefficient's normalized Dirichlet minimum. The same
factorization holds on a fiber of a slope selection measurable for the new
layer. These are the probabilistic inputs to the Section 5 gluing argument
started at `ell`; no contraction or source-root closure is asserted here.
-/

namespace SubdiffusiveProcess.Section10

open Homogenization Homogenization.Book MeasureTheory ProbabilityTheory
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab (potentialIndexSigma potentialIndexSigma_le_borel)
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn

noncomputable section

variable {d : ℕ}

/-- The previous energy is measurable for exactly the retained layer block. -/
theorem measurable_retainedPrefix_dirichletInfOn_indexSigma (M : GMCModel d)
    (ell R N : ℕ) (T : KuhnCell d) (p : Vec d) :
    Measurable[potentialIndexSigma (d := d) (retainedPrefixIndices ell R N : Set ℕ)]
      fun omega : PotentialSample d =>
        dirichletInfOn (retainedPrefixCoefficient M ell R N omega) T.openCarrier p :=
  measurable_dirichletInfOn_layerCoefficient_potentialIndexSigma M _ T p

theorem measurable_retainedPrefix_dirichletInfOn (M : GMCModel d)
    (ell R N : ℕ) (T : KuhnCell d) (p : Vec d) :
    Measurable fun omega : PotentialSample d =>
      dirichletInfOn (retainedPrefixCoefficient M ell R N omega) T.openCarrier p :=
  (measurable_retainedPrefix_dirichletInfOn_indexSigma M ell R N T p).mono
    (potentialIndexSigma_le_borel _) le_rfl

/-- The affine competitor and genuine mean-one normalization give integrability
of the preceding energy, including the full-prefix base case. -/
theorem integrable_retainedPrefix_dirichletInfOn (M : GMCModel d)
    (ell R N : ℕ) (T : KuhnCell d) (p : Vec d) :
    Integrable (fun omega : PotentialSample d =>
      dirichletInfOn (retainedPrefixCoefficient M ell R N omega) T.openCarrier p)
      M.P.toMeasure := by
  have hdom : Integrable (fun omega : PotentialSample d =>
      (∫ x in T.openCarrier, retainedPrefixCoefficient M ell R N omega x) * vecNormSq p)
      M.P.toMeasure :=
    (integrable_setIntegral_retainedPrefixCoefficient M ell R N
      (isOpen_openCarrier T).measurableSet (isBounded_openCarrier T)).mul_const _
  refine hdom.mono'
    (measurable_retainedPrefix_dirichletInfOn M ell R N T p).aestronglyMeasurable
    (Filter.Eventually.of_forall fun omega => ?_)
  have hnonneg := fun x => (retainedPrefixCoefficient_pos M ell R N omega x).le
  rw [Real.norm_eq_abs, abs_of_nonneg
    (dirichletInfOn_nonneg (isOpen_openCarrier T).measurableSet hnonneg)]
  calc
    dirichletInfOn (retainedPrefixCoefficient M ell R N omega) T.openCarrier p
        ≤ ∫ x in T.openCarrier, retainedPrefixCoefficient M ell R N omega x *
            vecNormSq p :=
      dirichletInfOn_le_affine (isOpen_openCarrier T).measurableSet hnonneg
    _ = (∫ x in T.openCarrier, retainedPrefixCoefficient M ell R N omega x) *
        vecNormSq p := integral_mul_const _ _

/-- Any new-layer weight is independent of the normalized previous energy. -/
theorem indepFun_new_layer_weight_retainedPrefix_energy (M : GMCModel d)
    (ell : ℕ) {R : ℕ} (hR : 0 < R) (N : ℕ)
    {F : PotentialSample d → ℝ}
    (hF : Measurable[potentialIndexSigma (d := d)
      ({ell + (N + 1) * R} : Set ℕ)] F) (T : KuhnCell d) (p : Vec d) :
    IndepFun F (fun omega : PotentialSample d =>
      (volume T.openCarrier).toReal⁻¹ *
        dirichletInfOn (retainedPrefixCoefficient M ell R N omega) T.openCarrier p)
      M.P.toMeasure :=
  (indepFun_of_potentialIndexSigma_disjoint M
    (disjoint_retainedPrefixIndices_next_set ell hR N)
    ((measurable_retainedPrefix_dirichletInfOn_indexSigma M ell R N T p).const_mul _)
    hF).symm

/-- The one-new-layer expectation factorization used by the shifted induction. -/
theorem integral_new_layer_weight_mul_retainedPrefix_energy (M : GMCModel d)
    (ell : ℕ) {R : ℕ} (hR : 0 < R) (N : ℕ)
    {F : PotentialSample d → ℝ}
    (hF : Measurable[potentialIndexSigma (d := d)
      ({ell + (N + 1) * R} : Set ℕ)] F) (T : KuhnCell d) (p : Vec d) :
    ∫ omega, F omega * ((volume T.openCarrier).toReal⁻¹ *
        dirichletInfOn (retainedPrefixCoefficient M ell R N omega) T.openCarrier p)
      ∂M.P.toMeasure =
      (∫ omega, F omega ∂M.P.toMeasure) *
        ∫ omega, (volume T.openCarrier).toReal⁻¹ *
          dirichletInfOn (retainedPrefixCoefficient M ell R N omega) T.openCarrier p
          ∂M.P.toMeasure :=
  (indepFun_new_layer_weight_retainedPrefix_energy M ell hR N hF T p).integral_fun_mul_eq_mul_integral
      (hF.mono (potentialIndexSigma_le_borel _) le_rfl).aestronglyMeasurable
      ((measurable_retainedPrefix_dirichletInfOn M ell R N T p).const_mul _).aestronglyMeasurable

/-- Concrete application: the new shell's cell supremum factors from the
preceding retained Dirichlet energy on that cell. -/
theorem integral_cellSup_next_mul_retainedPrefix_energy (M : GMCModel d)
    (ell : ℕ) {R : ℕ} (hR : 0 < R) (N : ℕ) (T : KuhnCell d) (p : Vec d) :
    ∫ omega, cellSup (shellFactor M (ell + (N + 1) * R) omega) T *
        ((volume T.openCarrier).toReal⁻¹ *
          dirichletInfOn (retainedPrefixCoefficient M ell R N omega) T.openCarrier p)
        ∂M.P.toMeasure =
      (∫ omega, cellSup (shellFactor M (ell + (N + 1) * R) omega) T ∂M.P.toMeasure) *
        ∫ omega, (volume T.openCarrier).toReal⁻¹ *
          dirichletInfOn (retainedPrefixCoefficient M ell R N omega) T.openCarrier p
          ∂M.P.toMeasure :=
  integral_new_layer_weight_mul_retainedPrefix_energy M ell hR N
    (measurable_cellSup_shellFactor_singleton M _ T) T p

/-- The concrete product is integrable on the gluing mesh, so its expectation
factorization can be used in the induction's finite sum of cell energies. -/
theorem integrable_cellSup_next_mul_retainedPrefix_energy (M : GMCModel d)
    (ell : ℕ) {R : ℕ} (hR : 0 < R) (N : ℕ)
    (c : Fin d → ℤ) (pi : Equiv.Perm (Fin d)) {T : KuhnCell d}
    (hT : T ∈ dilatedSubMesh (ell + (N + 1) * R) R c pi) (p : Vec d) :
    Integrable (fun omega : PotentialSample d =>
      cellSup (shellFactor M (ell + (N + 1) * R) omega) T *
        ((volume T.openCarrier).toReal⁻¹ *
          dirichletInfOn (retainedPrefixCoefficient M ell R N omega) T.openCarrier p))
      M.P.toMeasure :=
  (indepFun_new_layer_weight_retainedPrefix_energy M ell hR N
    (measurable_cellSup_shellFactor_singleton M _ T) T p).integrable_mul
      (integrable_cellSup_shellFactor_mem_dilatedSubMesh M R _ c pi hT)
      ((integrable_retainedPrefix_dirichletInfOn M ell R N T p).const_mul _)

/-- The same application on a fiber of a new-layer measurable slope selection;
the frozen slope `p` is deterministic on the fiber. -/
theorem setIntegral_fiber_cellSup_next_mul_retainedPrefix_energy (M : GMCModel d)
    (ell : ℕ) {R : ℕ} (hR : 0 < R) (N : ℕ) {n : PotentialSample d → ℕ}
    (hn : Measurable[potentialIndexSigma (d := d)
      ({ell + (N + 1) * R} : Set ℕ)] n)
    (i : ℕ) (T : KuhnCell d) (p : Vec d) :
    ∫ omega in {omega | n omega = i},
      cellSup (shellFactor M (ell + (N + 1) * R) omega) T *
        ((volume T.openCarrier).toReal⁻¹ *
          dirichletInfOn (retainedPrefixCoefficient M ell R N omega) T.openCarrier p)
        ∂M.P.toMeasure =
      (∫ omega in {omega | n omega = i},
        cellSup (shellFactor M (ell + (N + 1) * R) omega) T ∂M.P.toMeasure) *
        ∫ omega, (volume T.openCarrier).toReal⁻¹ *
          dirichletInfOn (retainedPrefixCoefficient M ell R N omega) T.openCarrier p
          ∂M.P.toMeasure := by
  have hfiber : MeasurableSet {omega | n omega = i} :=
    measurableSet_index_fiber (hn.mono (potentialIndexSigma_le_borel _) le_rfl) i
  rw [setIntegral_mul_eq_integral_indicator_mul hfiber,
    integral_new_layer_weight_mul_retainedPrefix_energy M ell hR N
      (measurable_indicator_fiber_mul hn (measurable_cellSup_shellFactor_singleton M _ T) i),
    integral_indicator hfiber]

/-- On the explicit new-layer mesh the cell scale is exactly the previous
retained scale, as required to read the induction hypothesis cell by cell. -/
theorem scale_of_mem_retainedPrefix_next_subMesh (ell R N : ℕ)
    (c : Fin d → ℤ) (pi : Equiv.Perm (Fin d)) {T : KuhnCell d}
    (hT : T ∈ dilatedSubMesh (ell + (N + 1) * R) R c pi) :
    T.supportCube.scale = ((ell + N * R : ℕ) : ℤ) := by
  rw [scale_of_mem_dilatedSubMesh hT]
  push_cast
  ring

/-- A concrete, literal-set application exporting both the successor product
and the independence of its two factors, including the prefix base `N = 0`. -/
theorem retainedPrefix_one_new_layer (M : GMCModel d) (ell : ℕ) {R : ℕ}
    (hR : 0 < R) (N : ℕ) :
    (∀ omega : PotentialSample d,
      layerCoefficient M (Finset.range (ell + 1) ∪
        (Finset.range (N + 1)).image (fun j => ell + (j + 1) * R)) omega =
      fun x => shellFactor M (ell + (N + 1) * R) omega x *
        layerCoefficient M (Finset.range (ell + 1) ∪
          (Finset.range N).image (fun j => ell + (j + 1) * R)) omega x) ∧
    IndepFun (fun omega : PotentialSample d => shellFactor M (ell + (N + 1) * R) omega)
      (fun omega : PotentialSample d =>
        layerCoefficient M (Finset.range (ell + 1) ∪
          (Finset.range N).image (fun j => ell + (j + 1) * R)) omega)
      M.P.toMeasure :=
  ⟨retainedPrefixCoefficient_succ M ell hR N,
    (indepFun_retainedPrefixCoefficient_next_shellFactor M ell hR N).symm⟩

end

end SubdiffusiveProcess.Section10
