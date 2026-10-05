module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.RandomFactorMeasurability
public import SubdiffusiveProcess.CoarseGrainingVocab.RestrictedCoefficientSigma

@[expose] public section

/-!
# Window-restricted coefficient measurability of the cutoff response errors

`ResponseCoefficientMeasurability.lean` shows that the manuscript response errors of the cutoff
coefficient are measurable for `coefficientSigma (aCutoff M L)` (point evaluations at all
`x ∈ ℝ^d`).  The paper asks for more: the errors on a cube `𝒞` depend on `a_L|_𝒞` only, i.e.
they are measurable for `restrictedCoefficientSigma (aCutoff M L) B` with `B ⊇ 𝒞`.

We replay the countable variational reduction with the source sigma-field replaced by the
window-restricted one.  Two devices make the replay mechanical.

* `a_L(ω)` is continuous, so evaluation at a point of `closure B` is measurable for the
  `B`-restricted sigma-field (`measurable_eval_restrictedCoefficientSigma_of_mem_closure`).
* A continuous retraction `r` of `ℝ^d` into `closure B` turns the integrands
  `(ω, x) ↦ a_L(ω, x)` into the jointly measurable `(ω, x) ↦ a_L(ω, r x)`; they agree with
  the original integrand on every domain `U` that `r` fixes pointwise.
-/

namespace SubdiffusiveProcess.RestrictedResponse

open Filter MeasureTheory
open Homogenization hiding Vec TriadicCube Mat
open Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators ENNReal

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

variable {d : ℕ}

/-- A continuous retraction datum of space into `closure B`. -/
structure ClosureRetract (B : Set (Vec d)) where
  toFun : Vec d → Vec d
  continuous_toFun : Continuous toFun
  mem_closure : ∀ x, toFun x ∈ closure B

/-- For a sample-wise continuous coefficient, evaluation at a point of `closure B` is measurable
for the `B`-restricted coefficient sigma-field. -/
theorem measurable_eval_restrictedCoefficientSigma_of_mem_closure
    {Ω : Type*} {a : Ω → Vec d → ℝ} (ha : ∀ ω, Continuous (a ω))
    {B : Set (Vec d)} {x : Vec d} (hx : x ∈ closure B) :
    Measurable[restrictedCoefficientSigma a B] fun ω => a ω x := by
  let : MeasurableSpace Ω := restrictedCoefficientSigma a B
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hx
  refine measurable_of_tendsto_metrizable (f := fun n ω => a ω (u n))
    (fun n => measurable_eval_restrictedCoefficientSigma (hu n)) ?_
  exact tendsto_pi_nhds.2 fun ω => ((ha ω).tendsto x).comp hlim

/-- Joint measurability of the retracted cutoff for the `B`-restricted sigma-field. -/
theorem measurable_aCutoff_retract_uncurry
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {B : Set (Vec d)}
    (R : ClosureRetract B) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d) ℝ
      ((restrictedCoefficientSigma (_root_.SubdiffusiveProcess.Model.aCutoff M L) B).prod inferInstance)
      inferInstance
      (fun z => _root_.SubdiffusiveProcess.Model.aCutoff M L z.1 (R.toFun z.2)) := by
  let : MeasurableSpace (_root_.SubdiffusiveProcess.Model.PotentialSample d) :=
    restrictedCoefficientSigma (_root_.SubdiffusiveProcess.Model.aCutoff M L) B
  have hEvalSwap : Measurable
      (Function.uncurry fun x : Vec d =>
        fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => _root_.SubdiffusiveProcess.Model.aCutoff M L omega (R.toFun x)) :=
    measurable_uncurry_of_continuous_of_measurable
      (ι := Vec d) (α := _root_.SubdiffusiveProcess.Model.PotentialSample d) (β := ℝ)
      (fun omega => (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M L omega).comp
        R.continuous_toFun)
      (fun x => measurable_eval_restrictedCoefficientSigma_of_mem_closure
        (a := _root_.SubdiffusiveProcess.Model.aCutoff M L)
        (fun omega => _root_.SubdiffusiveProcess.Model.continuous_aCutoff M L omega)
        (R.mem_closure x))
  exact hEvalSwap.comp measurable_swap

private theorem blockEnergyDensity_scalarCoeffField {d : ℕ}
    (a : Vec d → ℝ) (ha : ∀ x, 0 < a x) (X : BlockState d) (x : Vec d) :
    blockEnergyDensity (scalarCoeffField a) X x =
      (1 / 2 : ℝ) *
        (a x * vecDot (X.potential x) (X.potential x) +
          (a x)⁻¹ * vecDot (X.flux x) (X.flux x)) := by
  have hInv : ((Homogenization.scalarMatrix (d := d) (a x))⁻¹ : Mat d) =
      Homogenization.scalarMatrix (d := d) (a x)⁻¹ := by
    rw [Homogenization.scalarMatrix,
      Homogenization.nonsing_inv_smul (a x) (ha x).ne' (by simp)]
    simp [Homogenization.scalarMatrix]
  simp [blockEnergyDensity, blockCoeffField, blockMatrixOfCoeff,
    scalarCoeffField, Homogenization.Book.Ch02.symmPart_scalarMatrix,
    Homogenization.Book.Ch02.skewPart_scalarMatrix, hInv,
    BlockState.eval, blockMatVecMul, Homogenization.matVecMul_scalarMatrix,
    Homogenization.blockVecDot, Homogenization.matVecMul,
    Homogenization.vecDot, Homogenization.matTranspose, Finset.mul_sum,
    mul_left_comm]

/-- A fixed admissible competitor has window-measurable cutoff energy. -/
theorem measurable_cutoff_fixed_blockEnergyAverage_restricted
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {B : Set (Vec d)}
    (R : ClosureRetract B) (U : Ch02.Domain d)
    (hU : ∀ x ∈ (U : Set (Vec d)), R.toFun x = x)
    (P : BlockVec d) (X : BlockState d)
    (hX : IsBlockMuAdmissible (U : Set (Vec d)) P X) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
      (restrictedCoefficientSigma (_root_.SubdiffusiveProcess.Model.aCutoff M L) B)
      inferInstance
      (fun omega => blockEnergyAverage (U : Set (Vec d))
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) X) := by
  let : MeasurableSpace (_root_.SubdiffusiveProcess.Model.PotentialSample d) :=
    restrictedCoefficientSigma (_root_.SubdiffusiveProcess.Model.aCutoff M L) B
  have hJoint := measurable_aCutoff_retract_uncurry M L R
  have hXL2 : MemBlockL2 (U : Set (Vec d)) X.eval := hX.memBlockL2_eval
  have hPotentialL2 : MemVectorL2 (U : Set (Vec d)) X.potential := by
    simpa [BlockState.eval] using
      memVectorL2_fst_of_memBlockL2 (U := (U : Set (Vec d))) hXL2
  have hFluxL2 : MemVectorL2 (U : Set (Vec d)) X.flux := by
    simpa [BlockState.eval] using
      memVectorL2_snd_of_memBlockL2 (U := (U : Set (Vec d))) hXL2
  let f : Vec d → Vec d := hPotentialL2.aestronglyMeasurable.mk X.potential
  let g : Vec d → Vec d := hFluxL2.aestronglyMeasurable.mk X.flux
  have hf : Measurable f := hPotentialL2.aestronglyMeasurable.measurable_mk
  have hg : Measurable g := hFluxL2.aestronglyMeasurable.measurable_mk
  have measurable_vecDot_self {v : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d → Vec d}
      (hv : Measurable v) : Measurable (fun z => vecDot (v z) (v z)) := by
    simp only [vecDot]
    exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp hv).mul ((measurable_pi_apply i).comp hv)
  have hPotential : Measurable (fun z : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d =>
      _root_.SubdiffusiveProcess.Model.aCutoff M L z.1 (R.toFun z.2) *
        vecDot (f z.2) (f z.2)) :=
    hJoint.mul (measurable_vecDot_self (hf.comp measurable_snd))
  have hFlux : Measurable (fun z : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d =>
      (_root_.SubdiffusiveProcess.Model.aCutoff M L z.1 (R.toFun z.2))⁻¹ *
        vecDot (g z.2) (g z.2)) :=
    hJoint.inv.mul (measurable_vecDot_self (hg.comp measurable_snd))
  have hIntegral : StronglyMeasurable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      ∫ x, (1 / 2 : ℝ) *
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega (R.toFun x) * vecDot (f x) (f x) +
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega (R.toFun x))⁻¹ * vecDot (g x) (g x))
        ∂volumeMeasureOn (U : Set (Vec d))) :=
    (measurable_const.mul (hPotential.add hFlux)).stronglyMeasurable.integral_prod_right'
  have hmem : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)), x ∈ (U : Set (Vec d)) :=
    MeasureTheory.ae_restrict_mem U.measurableSet
  have hEq : (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      blockEnergyAverage (U : Set (Vec d))
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) X) =
      fun omega => (volume (U : Set (Vec d))).toReal⁻¹ *
        ∫ x, (1 / 2 : ℝ) *
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega (R.toFun x) * vecDot (f x) (f x) +
            (_root_.SubdiffusiveProcess.Model.aCutoff M L omega (R.toFun x))⁻¹ *
              vecDot (g x) (g x))
          ∂volumeMeasureOn (U : Set (Vec d)) := by
    funext omega
    rw [blockEnergyAverage, volumeAverage]
    congr 1
    apply integral_congr_ae
    filter_upwards [hPotentialL2.aestronglyMeasurable.ae_eq_mk,
      hFluxL2.aestronglyMeasurable.ae_eq_mk, hmem] with x hfx hgx hx
    rw [hU x hx]
    simpa [f, g, hfx, hgx] using
      blockEnergyDensity_scalarCoeffField
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
        (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega) X x
  rw [hEq]
  exact measurable_const.mul hIntegral.measurable

/-- Every deterministic loading has window-measurable cutoff `Mu`. -/
theorem measurable_cutoff_Mu_restricted [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {B : Set (Vec d)}
    (R : ClosureRetract B) (U : Ch02.Domain d)
    (hU : ∀ x ∈ (U : Set (Vec d)), R.toFun x = x) (P : BlockVec d) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
      (restrictedCoefficientSigma (_root_.SubdiffusiveProcess.Model.aCutoff M L) B)
      inferInstance
      (fun omega => Mu (U : Set (Vec d)) P
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega))) := by
  let : MeasurableSpace (_root_.SubdiffusiveProcess.Model.PotentialSample d) :=
    restrictedCoefficientSigma (_root_.SubdiffusiveProcess.Model.aCutoff M L) B
  obtain ⟨X, hX, hMu⟩ := cutoffMu_countableReduction M L U P
  have hEq : (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => Mu (U : Set (Vec d)) P
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega))) =
      fun omega => ⨅ n : ℕ, blockEnergyAverage (U : Set (Vec d))
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) (X n) := by
    funext omega
    exact hMu omega
  rw [hEq]
  exact Measurable.iInf fun n =>
    measurable_cutoff_fixed_blockEnergyAverage_restricted M L R U hU P (X n) (hX n)

/-- Every fixed response probe on a window-fixed domain is window-measurable. -/
theorem measurable_cutoff_responseJ_restricted [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {B : Set (Vec d)}
    (R : ClosureRetract B) (U : Ch02.Domain d)
    (hU : ∀ x ∈ (U : Set (Vec d)), R.toFun x = x) (p q : Vec d) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
      (restrictedCoefficientSigma (_root_.SubdiffusiveProcess.Model.aCutoff M L) B)
      inferInstance
      (fun omega => J U (aCutoffCoeffOnData M L omega U).toCoeffOn p q) := by
  have hMu := measurable_cutoff_Mu_restricted M L R U hU (-p, q)
  have hEq : (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      J U (aCutoffCoeffOnData M L omega U).toCoeffOn p q) =
      fun omega => Mu (U : Set (Vec d)) (-p, q)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) - vecDot p q := by
    funext omega
    let aomega := (aCutoffCoeffOnData M L omega U).toCoeffOn
    calc
      J U aomega p q = Ch02.doubledMu U aomega (-p, q) - vecDot p q :=
        Ch02.responseJ_eq_doubledMu_neg_left_sub_vecDot U aomega p q
      _ = Mu (U : Set (Vec d)) (-p, q) aomega.toCoeffField - vecDot p q := by
        rw [Ch02.doubledMu_eq_Mu]
      _ = Mu (U : Set (Vec d)) (-p, q)
          (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) -
            vecDot p q := rfl
  rw [hEq]
  exact hMu.sub measurable_const

/-- The unit-sphere cutoff response maximum on a window-fixed domain is window-measurable. -/
theorem measurable_normalizedDefect_restricted
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {B : Set (Vec d)}
    (R : ClosureRetract B) (U : Ch02.Domain d)
    (hU : ∀ x ∈ (U : Set (Vec d)), R.toFun x = x) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ≥0∞
      (restrictedCoefficientSigma (_root_.SubdiffusiveProcess.Model.aCutoff M L) B)
      inferInstance (normalizedDefect M L U) := by
  by_cases hd : d = 0
  · subst d
    have heq : normalizedDefect M L U = fun _ => 0 := by
      funext omega
      unfold normalizedDefect paperScalarProbeMaxOn
      apply le_antisymm
      · refine iSup_le fun e => ?_
        have hfalse : False := by
          have he := e.2
          simp [vecNormSq, vecDot] at he
        exact hfalse.elim
      · exact bot_le
    rw [heq]
    exact measurable_const
  let : NeZero d := ⟨hd⟩
  have hrep : @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ≥0∞
      (restrictedCoefficientSigma (_root_.SubdiffusiveProcess.Model.aCutoff M L) B)
      inferInstance (normalizedDefectCountableRepresentative M L U) := by
    unfold normalizedDefectCountableRepresentative
    exact Measurable.iSup fun i =>
      (measurable_cutoff_responseJ_restricted M L R U hU
        ((Real.sqrt (ahom M L))⁻¹ •
          (TopologicalSpace.denseSeq (ScalarProbeUnitSphere d) i : Vec d))
        (Real.sqrt (ahom M L) •
          (TopologicalSpace.denseSeq (ScalarProbeUnitSphere d) i : Vec d))).ennreal_ofReal
  have heq : normalizedDefect M L U =
      normalizedDefectCountableRepresentative M L U := by
    funext omega
    exact normalizedDefect_eq_countableRepresentative M L U omega
  rwa [heq]

/-- A one-cube paper probe maximum is window-measurable when the cube is window-fixed. -/
theorem measurable_paperScalarProbeMax_aCutoffFamily_restricted
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {B : Set (Vec d)}
    (R : ClosureRetract B) (Q : TriadicCube d)
    (hQ : ∀ x ∈ openCubeSet Q, R.toFun x = x) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ≥0∞
      (restrictedCoefficientSigma (_root_.SubdiffusiveProcess.Model.aCutoff M L) B)
      inferInstance
      (fun omega => paperScalarProbeMax Q (aCutoffFamily M L omega) (ahom M L)) := by
  simpa [paperScalarProbeMax, paperScalarProbe, normalizedDefect,
    paperScalarProbeMaxOn, aCutoffFamily, aCutoffTriadicData,
    ScalarTriadicCoeffData.toTriadicCoeffFamily] using!
    measurable_normalizedDefect_restricted M L R (Ch02.cubeDomain Q) hQ

/-- The maximum over descendants at a fixed scale below a window-fixed cube. -/
theorem measurable_paperMaxDescendantProbeAtScale_aCutoffFamily_restricted
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {B : Set (Vec d)}
    (R : ClosureRetract B) (Q : TriadicCube d) (k : ℤ) (hk : k ≤ Q.scale)
    (hQ : ∀ x ∈ openCubeSet Q, R.toFun x = x) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ≥0∞
      (restrictedCoefficientSigma (_root_.SubdiffusiveProcess.Model.aCutoff M L) B)
      inferInstance
      (fun omega => paperMaxDescendantProbeAtScale Q k
        (aCutoffFamily M L omega) (ahom M L)) := by
  unfold paperMaxDescendantProbeAtScale
  exact Measurable.iSup fun S =>
    measurable_paperScalarProbeMax_aCutoffFamily_restricted M L R S.1 fun x hx =>
      hQ x (openCubeSet_subset_of_mem_descendantsAtScale hk S.2 hx)

/-- The `p = infinity` response aggregation at one scale is window-measurable. -/
theorem measurable_paperScaleResponseAtScale_infinity_aCutoffFamily_restricted
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {B : Set (Vec d)}
    (R : ClosureRetract B) (Q : TriadicCube d) (k : ℤ) (hk : k ≤ Q.scale)
    (hQ : ∀ x ∈ openCubeSet Q, R.toFun x = x) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ≥0∞
      (restrictedCoefficientSigma (_root_.SubdiffusiveProcess.Model.aCutoff M L) B)
      inferInstance
      (fun omega => paperScaleResponseAtScale Q k .infinity
        (aCutoffFamily M L omega) (ahom M L)) := by
  change @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ≥0∞
    (restrictedCoefficientSigma (_root_.SubdiffusiveProcess.Model.aCutoff M L) B)
    inferInstance
    (fun omega => (paperMaxDescendantProbeAtScale Q k
      (aCutoffFamily M L omega) (ahom M L)) ^ (1 / 2 : ℝ))
  exact ENNReal.continuous_rpow_const.measurable.comp
    (measurable_paperMaxDescendantProbeAtScale_aCutoffFamily_restricted
      M L R Q k hk hQ)

/-- The finite-`q` response error with spatial exponent `infinity` of a window-fixed cube is
measurable for the window-restricted sigma-field of the raw cutoff. -/
theorem measurable_paperHomogenizationError_infinity_finite_aCutoffFamily_restricted
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {B : Set (Vec d)}
    (R : ClosureRetract B) (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (hQ : ∀ x ∈ openCubeSet Q, R.toFun x = x) (s q : ℝ) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ≥0∞
      (restrictedCoefficientSigma (_root_.SubdiffusiveProcess.Model.aCutoff M L) B)
      inferInstance
      (fun omega => paperHomogenizationError Q n s .infinity (.finite q)
        (aCutoffFamily M L omega) (ahom M L)) := by
  change @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ≥0∞
    (restrictedCoefficientSigma (_root_.SubdiffusiveProcess.Model.aCutoff M L) B)
    inferInstance
    (fun omega => (∑' l : ℕ,
      ENNReal.ofReal (Ch02.geometricWeight s q l) *
        (paperScaleResponseAtScale Q (n - (l : ℤ)) .infinity
          (aCutoffFamily M L omega) (ahom M L)) ^ q) ^ (1 / q))
  let : MeasurableSpace (_root_.SubdiffusiveProcess.Model.PotentialSample d) :=
    restrictedCoefficientSigma (_root_.SubdiffusiveProcess.Model.aCutoff M L) B
  apply ENNReal.continuous_rpow_const.measurable.comp
  apply Measurable.tsum
  intro l
  exact measurable_const.mul
    (ENNReal.continuous_rpow_const.measurable.comp
      (measurable_paperScaleResponseAtScale_infinity_aCutoffFamily_restricted
        M L R Q (n - (l : ℤ)) (by have : (0 : ℤ) ≤ l := Int.natCast_nonneg l; omega) hQ))

end

end SubdiffusiveProcess.RestrictedResponse
