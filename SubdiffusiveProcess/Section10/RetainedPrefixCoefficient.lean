module

public import SubdiffusiveProcess.Section10.RetainedPrefixIndices
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerSigma
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.MeanOneFubini

@[expose] public section

/-!
# Actual retained-prefix coefficients on the GMC carrier

Every coefficient is the existing `layerCoefficient` on the literal index set
of `lim:lem-strict-decay`. Independence and normalization come from `GMCModel`,
without a caller-supplied law or an abstract family of coefficients.
-/

namespace SubdiffusiveProcess.Section10

open Homogenization MeasureTheory ProbabilityTheory
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab (potentialIndexSigma potentialIndexSigma_le_borel)
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- All layers through `ell`, followed by `ell + R, ..., ell + N * R`. -/
def retainedPrefixCoefficient (M : GMCModel d) (ell R N : ℕ)
    (omega : PotentialSample d) (x : Vec d) : ℝ :=
  layerCoefficient M (retainedPrefixIndices ell R N) omega x

/-- The product of the omitted layers inside cutoff `m`. -/
def omittedPrefixCoefficient (M : GMCModel d) (ell R N m : ℕ)
    (omega : PotentialSample d) (x : Vec d) : ℝ :=
  layerCoefficient M (omittedPrefixIndices ell R N m) omega x

@[simp] theorem retainedPrefixCoefficient_zero (M : GMCModel d) (ell R : ℕ)
    (omega : PotentialSample d) :
    retainedPrefixCoefficient M ell R 0 omega = aCutoff M ell omega := by
  funext x
  rw [retainedPrefixCoefficient, retainedPrefixIndices_zero,
    aCutoff_eq_layerCoefficient]

/-- The prefix is multiplied by the literal tail product, with no repetitions. -/
theorem retainedPrefixCoefficient_eq_prefix_mul_prod (M : GMCModel d)
    (ell : ℕ) {R : ℕ} (hR : 0 < R) (N : ℕ)
    (omega : PotentialSample d) (x : Vec d) :
    retainedPrefixCoefficient M ell R N omega x =
      aCutoff M ell omega x *
        ∏ j ∈ Finset.range N, shellFactor M (ell + (j + 1) * R) omega x := by
  rw [retainedPrefixCoefficient, retainedPrefixIndices,
    layerCoefficient_union M (disjoint_prefix_retained_tail ell hR N),
    ← aCutoff_eq_layerCoefficient, layerCoefficient]
  rw [Finset.prod_image (fun i _ j _ hij => retained_tail_injective ell hR hij)]

/-- The successor adds exactly one shell factor at `ell + (N+1)R`. -/
theorem retainedPrefixCoefficient_succ (M : GMCModel d) (ell : ℕ) {R : ℕ}
    (hR : 0 < R) (N : ℕ) (omega : PotentialSample d) :
    retainedPrefixCoefficient M ell R (N + 1) omega =
      fun x => shellFactor M (ell + (N + 1) * R) omega x *
        retainedPrefixCoefficient M ell R N omega x := by
  funext x
  rw [retainedPrefixCoefficient, retainedPrefixIndices_succ, layerCoefficient,
    Finset.prod_insert (next_layer_not_mem_retainedPrefixIndices ell hR N)]
  rfl

theorem retainedPrefixCoefficient_pos (M : GMCModel d) (ell R N : ℕ)
    (omega : PotentialSample d) (x : Vec d) :
    0 < retainedPrefixCoefficient M ell R N omega x :=
  layerCoefficient_pos M _ omega x

theorem omittedPrefixCoefficient_pos (M : GMCModel d) (ell R N m : ℕ)
    (omega : PotentialSample d) (x : Vec d) :
    0 < omittedPrefixCoefficient M ell R N m omega x :=
  layerCoefficient_pos M _ omega x

theorem continuous_retainedPrefixCoefficient (M : GMCModel d) (ell R N : ℕ)
    (omega : PotentialSample d) : Continuous (retainedPrefixCoefficient M ell R N omega) :=
  continuous_layerCoefficient M _ omega

theorem continuous_omittedPrefixCoefficient (M : GMCModel d) (ell R N m : ℕ)
    (omega : PotentialSample d) : Continuous (omittedPrefixCoefficient M ell R N m omega) :=
  continuous_layerCoefficient M _ omega

theorem measurable_retainedPrefixCoefficient_apply (M : GMCModel d) (ell R N : ℕ)
    (x : Vec d) :
    Measurable fun omega : PotentialSample d => retainedPrefixCoefficient M ell R N omega x :=
  measurable_layerCoefficient_apply M _ x

theorem measurable_retainedPrefixCoefficient (M : GMCModel d) (ell R N : ℕ) :
    Measurable fun omega : PotentialSample d => retainedPrefixCoefficient M ell R N omega :=
  Measurable.of_eval (measurable_retainedPrefixCoefficient_apply M ell R N)

theorem measurable_retainedPrefixCoefficient_uncurry (M : GMCModel d) (ell R N : ℕ) :
    Measurable fun z : PotentialSample d × Vec d =>
      retainedPrefixCoefficient M ell R N z.1 z.2 :=
  measurable_layerCoefficient_uncurry M _

theorem measurable_retainedPrefixCoefficient_apply_indexSigma (M : GMCModel d)
    (ell R N : ℕ) (x : Vec d) :
    Measurable[potentialIndexSigma (d := d) (retainedPrefixIndices ell R N : Set ℕ)]
      fun omega : PotentialSample d => retainedPrefixCoefficient M ell R N omega x :=
  measurable_layerCoefficient_apply_potentialIndexSigma M _ x

theorem measurable_omittedPrefixCoefficient_apply (M : GMCModel d) (ell R N m : ℕ)
    (x : Vec d) :
    Measurable fun omega : PotentialSample d => omittedPrefixCoefficient M ell R N m omega x :=
  measurable_layerCoefficient_apply M _ x

theorem measurable_omittedPrefixCoefficient (M : GMCModel d) (ell R N m : ℕ) :
    Measurable fun omega : PotentialSample d => omittedPrefixCoefficient M ell R N m omega :=
  Measurable.of_eval (measurable_omittedPrefixCoefficient_apply M ell R N m)

theorem measurable_omittedPrefixCoefficient_uncurry (M : GMCModel d) (ell R N m : ℕ) :
    Measurable fun z : PotentialSample d × Vec d =>
      omittedPrefixCoefficient M ell R N m z.1 z.2 :=
  measurable_layerCoefficient_uncurry M _

theorem measurable_omittedPrefixCoefficient_apply_indexSigma (M : GMCModel d)
    (ell R N m : ℕ) (x : Vec d) :
    Measurable[potentialIndexSigma (d := d) (omittedPrefixIndices ell R N m : Set ℕ)]
      fun omega : PotentialSample d => omittedPrefixCoefficient M ell R N m omega x :=
  measurable_layerCoefficient_apply_potentialIndexSigma M _ x

/-- The full cutoff is exactly the retained field times its omitted layers. -/
theorem aCutoff_eq_retainedPrefix_mul_omitted (M : GMCModel d)
    {ell R N m : ℕ} (hm : ell + N * R ≤ m) (omega : PotentialSample d) :
    aCutoff M m omega = fun x =>
      retainedPrefixCoefficient M ell R N omega x *
        omittedPrefixCoefficient M ell R N m omega x := by
  funext x
  rw [aCutoff_eq_layerCoefficient, ← retainedPrefixIndices_union_omitted hm,
    layerCoefficient_union M (disjoint_retainedPrefixIndices_omitted ell R N m)]
  rfl

/-- Reinsertion at an arbitrary cutoff, with the number of retained steps fixed
by the paper's floor. This includes `m = ell`. -/
theorem aCutoff_eq_retainedPrefix_floor_mul_omitted (M : GMCModel d)
    {ell m : ℕ} (hell : ell ≤ m) (R : ℕ) (omega : PotentialSample d) :
    aCutoff M m omega = fun x =>
      retainedPrefixCoefficient M ell R ((m - ell) / R) omega x *
        omittedPrefixCoefficient M ell R ((m - ell) / R) m omega x :=
  aCutoff_eq_retainedPrefix_mul_omitted M (floor_scale_le hell) omega

@[simp] theorem omittedPrefixCoefficient_zero_at_base (M : GMCModel d) (ell R : ℕ)
    (omega : PotentialSample d) :
    omittedPrefixCoefficient M ell R 0 ell omega = fun _ => 1 := by
  funext x
  simp only [omittedPrefixCoefficient, omittedPrefixIndices_zero_at_base,
    layerCoefficient, Finset.prod_empty]

theorem integral_retainedPrefixCoefficient_apply (M : GMCModel d) (ell R N : ℕ)
    (x : Vec d) :
    ∫ omega, retainedPrefixCoefficient M ell R N omega x ∂M.P.toMeasure = 1 :=
  integral_layerCoefficient_apply M _ x

/-- Every omitted product has mean one, including the empty product at the base. -/
theorem integral_omittedPrefixCoefficient_apply (M : GMCModel d) (ell R N m : ℕ)
    (x : Vec d) :
    ∫ omega, omittedPrefixCoefficient M ell R N m omega x ∂M.P.toMeasure = 1 :=
  integral_layerCoefficient_apply M _ x

theorem integrable_retainedPrefixCoefficient_apply (M : GMCModel d) (ell R N : ℕ)
    (x : Vec d) :
    Integrable (fun omega => retainedPrefixCoefficient M ell R N omega x) M.P.toMeasure :=
  MeasureTheory.integrable_of_integral_eq_one
    (integral_retainedPrefixCoefficient_apply M ell R N x)

theorem integrable_omittedPrefixCoefficient_apply (M : GMCModel d) (ell R N m : ℕ)
    (x : Vec d) :
    Integrable (fun omega => omittedPrefixCoefficient M ell R N m omega x) M.P.toMeasure :=
  MeasureTheory.integrable_of_integral_eq_one
    (integral_omittedPrefixCoefficient_apply M ell R N m x)

theorem integral_setIntegral_retainedPrefixCoefficient (M : GMCModel d) (ell R N : ℕ)
    {U : Set (Vec d)} (hU : MeasurableSet U) (hUb : Bornology.IsBounded U) :
    ∫ omega, (∫ x in U, retainedPrefixCoefficient M ell R N omega x)
      ∂M.P.toMeasure = (volume U).toReal :=
  integral_setIntegral_layerCoefficient M _ hU hUb

theorem integrable_setIntegral_retainedPrefixCoefficient (M : GMCModel d) (ell R N : ℕ)
    {U : Set (Vec d)} (hU : MeasurableSet U) (hUb : Bornology.IsBounded U) :
    Integrable (fun omega => ∫ x in U, retainedPrefixCoefficient M ell R N omega x)
      M.P.toMeasure :=
  integrable_setIntegral_layerCoefficient M _ hU hUb

theorem integral_setIntegral_omittedPrefixCoefficient (M : GMCModel d) (ell R N m : ℕ)
    {U : Set (Vec d)} (hU : MeasurableSet U) (hUb : Bornology.IsBounded U) :
    ∫ omega, (∫ x in U, omittedPrefixCoefficient M ell R N m omega x)
      ∂M.P.toMeasure = (volume U).toReal :=
  integral_setIntegral_layerCoefficient M _ hU hUb

theorem integrable_setIntegral_omittedPrefixCoefficient (M : GMCModel d) (ell R N m : ℕ)
    {U : Set (Vec d)} (hU : MeasurableSet U) (hUb : Bornology.IsBounded U) :
    Integrable (fun omega => ∫ x in U, omittedPrefixCoefficient M ell R N m omega x)
      M.P.toMeasure :=
  integrable_setIntegral_layerCoefficient M _ hU hUb

/-- The fresh shell and the preceding retained field are independent as fields. -/
theorem indepFun_retainedPrefixCoefficient_next_shellFactor (M : GMCModel d)
    (ell : ℕ) {R : ℕ} (hR : 0 < R) (N : ℕ) :
    IndepFun (fun omega : PotentialSample d => retainedPrefixCoefficient M ell R N omega)
      (fun omega : PotentialSample d => shellFactor M (ell + (N + 1) * R) omega)
      M.P.toMeasure := by
  have h := indepFun_layerCoefficient_of_disjoint M
    (disjoint_retainedPrefixIndices_next ell hR N)
  have hshell : (fun omega : PotentialSample d =>
      layerCoefficient M {ell + (N + 1) * R} omega) =
      fun omega : PotentialSample d => shellFactor M (ell + (N + 1) * R) omega := by
    funext omega x
    simp only [layerCoefficient, Finset.prod_singleton]
  rw [hshell] at h
  exact h

theorem indepFun_retainedPrefixCoefficient_omittedPrefixCoefficient (M : GMCModel d)
    (ell R N m : ℕ) :
    IndepFun (fun omega : PotentialSample d => retainedPrefixCoefficient M ell R N omega)
      (fun omega : PotentialSample d => omittedPrefixCoefficient M ell R N m omega)
      M.P.toMeasure :=
  indepFun_layerCoefficient_of_disjoint M
    (disjoint_retainedPrefixIndices_omitted ell R N m)

/-- Conditioning on retained layers removes the omitted mean-one factor. -/
theorem integral_mul_omittedPrefixCoefficient_apply (M : GMCModel d)
    (ell R N m : ℕ) {F : PotentialSample d → ℝ}
    (hF : Measurable[potentialIndexSigma (d := d)
      (retainedPrefixIndices ell R N : Set ℕ)] F) (x : Vec d) :
    ∫ omega, F omega * omittedPrefixCoefficient M ell R N m omega x ∂M.P.toMeasure =
      ∫ omega, F omega ∂M.P.toMeasure := by
  have hd : Disjoint (retainedPrefixIndices ell R N : Set ℕ)
      (omittedPrefixIndices ell R N m : Set ℕ) := by
    exact_mod_cast disjoint_retainedPrefixIndices_omitted ell R N m
  have hi := indepFun_of_potentialIndexSigma_disjoint M hd hF
    (measurable_omittedPrefixCoefficient_apply_indexSigma M ell R N m x)
  rw [hi.integral_fun_mul_eq_mul_integral
      (hF.mono (potentialIndexSigma_le_borel _) le_rfl).aestronglyMeasurable
      (measurable_omittedPrefixCoefficient_apply M ell R N m x).aestronglyMeasurable,
    integral_omittedPrefixCoefficient_apply, mul_one]

/-- The scalar conditioning identity needed when reinserting omitted layers
into a retained-block energy density. -/
theorem integral_mul_aCutoff_eq_retainedPrefix (M : GMCModel d)
    {ell R N m : ℕ} (hm : ell + N * R ≤ m) {G : PotentialSample d → ℝ}
    (hG : Measurable[potentialIndexSigma (d := d)
      (retainedPrefixIndices ell R N : Set ℕ)] G) (x : Vec d) :
    ∫ omega, G omega * aCutoff M m omega x ∂M.P.toMeasure =
      ∫ omega, G omega * retainedPrefixCoefficient M ell R N omega x ∂M.P.toMeasure := by
  have h := integral_mul_omittedPrefixCoefficient_apply M ell R N m
    (hG.mul (measurable_retainedPrefixCoefficient_apply_indexSigma M ell R N x)) x
  refine (integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)).trans h
  rw [aCutoff_eq_retainedPrefix_mul_omitted M hm omega]
  exact (mul_assoc _ _ _).symm

end

end SubdiffusiveProcess.Section10
