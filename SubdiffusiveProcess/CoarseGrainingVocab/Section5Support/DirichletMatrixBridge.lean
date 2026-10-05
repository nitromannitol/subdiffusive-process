module

public import SubdiffusiveProcess.CoarseGrainingVocab.Core
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletInfimum
public import Homogenization.Book.Ch02.Theorems

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization Homogenization.Book MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## A scaling lemma for infima -/

/-- Positive scaling commutes with the infimum of a nonempty bounded-below set
of reals. -/
private theorem sInf_const_mul_image {c : ℝ} (hc : 0 < c) {S : Set ℝ}
    (hne : S.Nonempty) (hbdd : BddBelow S) :
    sInf ((fun E => c * E) '' S) = c * sInf S := by
  have hneImage : ((fun E => c * E) '' S).Nonempty := hne.image _
  have hbddImage : BddBelow ((fun E => c * E) '' S) := by
    obtain ⟨b, hb⟩ := hbdd
    refine ⟨c * b, ?_⟩
    rintro _ ⟨E, hE, rfl⟩
    exact mul_le_mul_of_nonneg_left (hb hE) hc.le
  refine le_antisymm ?_ ?_
  · have hkey : ∀ E ∈ S, c⁻¹ * sInf ((fun E => c * E) '' S) ≤ E := by
      intro E hE
      have h := csInf_le hbddImage (Set.mem_image_of_mem (fun E => c * E) hE)
      calc
        c⁻¹ * sInf ((fun E => c * E) '' S) ≤ c⁻¹ * (c * E) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hc.le)
        _ = E := by field_simp
    have hle := le_csInf hne hkey
    calc
      sInf ((fun E => c * E) '' S) = c * (c⁻¹ * sInf ((fun E => c * E) '' S)) := by
        field_simp
      _ ≤ c * sInf S := mul_le_mul_of_nonneg_left hle hc.le
  · refine le_csInf hneImage ?_
    rintro _ ⟨E, hE, rfl⟩
    exact mul_le_mul_of_nonneg_left (csInf_le hbdd hE) hc.le

/-! ## Volume of a public domain -/

theorem volume_toReal_pos (U : Ch02.Domain d) :
    0 < (volume (U : Set (Vec d))).toReal := by
  have hpos : 0 < volume (U : Set (Vec d)) :=
    IsOpen.measure_pos volume U.isOpen U.nonempty
  have hlt : volume (U : Set (Vec d)) < ⊤ :=
    U.isDomain.isBoundedDomain.isBounded.measure_lt_top
  exact ENNReal.toReal_pos (ne_of_gt hpos) (ne_of_lt hlt)

/-! ## The energy of one competitor -/

/-- The scalar coefficient acts on a gradient by multiplication. -/
private theorem vecDot_matVecMul_scalarCoeffOnData {a : Vec d → ℝ}
    {U : Ch02.Domain d} (ha : ScalarCoeffOnData U a) (x v : Vec d) :
    vecDot v (matVecMul (ha.toCoeffOn.toCoeffField x) v) = a x * vecNormSq v := by
  show vecDot v (matVecMul (Homogenization.scalarMatrix (a x)) v) = a x * vecNormSq v
  rw [matVecMul_scalarMatrix, vecDot_smul_right]
  rfl

/-- **The energy of an admissible competitor**, written through the `H_0^1`
correction supplied by admissibility.  The source's `fint` and this file's `int`
differ by the factor `|U|`, and the library's `nu_D` carries the extra `1/2` of
`(1/2) grad u . a grad u`. -/
theorem symmetricDirichletEnergyValue_eq {a : Vec d → ℝ} {U : Ch02.Domain d}
    (ha : ScalarCoeffOnData U a) {p : Vec d}
    {u : H1Function (U : Set (Vec d))} {w : H10Function (U : Set (Vec d))}
    (hw : (fun x => u.grad x - p) =ᵐ[volume.restrict (U : Set (Vec d))]
      w.toH1Function.grad) :
    Ch02.symmetricDirichletEnergyValue U ha.toCoeffOn u =
      (2 * (volume (U : Set (Vec d))).toReal)⁻¹ *
        dirichletEnergyOn' a (U : Set (Vec d)) p w.toH1Function.grad := by
  have hint :
      ∫ x in (U : Set (Vec d)), (1 / 2 : ℝ) * vecDot (u.grad x)
          (matVecMul (ha.toCoeffOn.toCoeffField x) (u.grad x)) =
        (1 / 2 : ℝ) * ∫ x in (U : Set (Vec d)),
          a x * vecNormSq (p + w.toH1Function.grad x) := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hw] with x hx
    have hgrad : u.grad x = p + w.toH1Function.grad x := sub_eq_iff_eq_add'.mp hx
    rw [hgrad, vecDot_matVecMul_scalarCoeffOnData ha]
  show Ch02.average U _ = _
  rw [Ch02.average, hint, dirichletEnergyOn', mul_inv]
  ring

/-! ## The two competitor classes coincide -/

/-- **The admissible energies are exactly the rescaled `H_0^1` energies.**  Both
inclusions are the identification of the competitor classes: admissibility
produces the `H_0^1` correction, and `linear_p + w` is admissible for every `w`
in `H_0^1(U)`. -/
theorem symmetricDirichletValueSet_eq_image {a : Vec d → ℝ} {U : Ch02.Domain d}
    (ha : ScalarCoeffOnData U a) (p : Vec d) :
    Ch02.symmetricDirichletValueSet U ha.toCoeffOn p =
      (fun E => (2 * (volume (U : Set (Vec d))).toReal)⁻¹ * E) ''
        dirichletEnergySet a (U : Set (Vec d)) p := by
  let : IsFiniteMeasure (volume.restrict (U : Set (Vec d))) :=
    U.isDomain.isFiniteMeasure_restrict_volume
  ext E
  constructor
  · rintro ⟨u, ⟨-, w, hw⟩, rfl⟩
    exact ⟨_, ⟨w, rfl⟩, (symmetricDirichletEnergyValue_eq ha hw).symm⟩
  · rintro ⟨-, ⟨w, rfl⟩, rfl⟩
    refine ⟨H1Function.affineOnIsSobolevRegularDomain
      U.isDomain.isSobolevRegularDomain p + w.toH1Function, ?_, ?_⟩
    · have hpt : (fun x => (H1Function.affineOnIsSobolevRegularDomain
          U.isDomain.isSobolevRegularDomain p + w.toH1Function).grad x - p) =
            w.toH1Function.grad := by
        funext x
        show (p + w.toH1Function.grad x) - p = w.toH1Function.grad x
        simp
      show Ch01.PotentialZeroTraceFieldOn _ _
      rw [hpt]
      exact Ch01.potentialZeroTraceFieldOn_of_h10 w
    · refine (symmetricDirichletEnergyValue_eq ha ?_).symm
      refine Filter.EventuallyEq.of_eq ?_
      funext x
      show (p + w.toH1Function.grad x) - p = w.toH1Function.grad x
      simp

/-- `linear_p + w` is an admissible competitor for every `w` in `H_0^1(U)`. -/
theorem isSymmetricDirichletAdmissible_affine_add {U : Ch02.Domain d} (p : Vec d)
    (w : H10Function (U : Set (Vec d)))
    [IsFiniteMeasure (volume.restrict (U : Set (Vec d)))] :
    Ch02.IsSymmetricDirichletAdmissible U p
      (H1Function.affineOnIsSobolevRegularDomain
        U.isDomain.isSobolevRegularDomain p + w.toH1Function) := by
  have hpt : (fun x => (H1Function.affineOnIsSobolevRegularDomain
      U.isDomain.isSobolevRegularDomain p + w.toH1Function).grad x - p) =
        w.toH1Function.grad := by
    funext x
    show (p + w.toH1Function.grad x) - p = w.toH1Function.grad x
    simp
  show Ch01.PotentialZeroTraceFieldOn _ _
  rw [hpt]
  exact Ch01.potentialZeroTraceFieldOn_of_h10 w

/-- The energy of `linear_p + w`. -/
theorem symmetricDirichletEnergyValue_affine_add {a : Vec d → ℝ}
    {U : Ch02.Domain d} (ha : ScalarCoeffOnData U a) (p : Vec d)
    (w : H10Function (U : Set (Vec d)))
    [IsFiniteMeasure (volume.restrict (U : Set (Vec d)))] :
    Ch02.symmetricDirichletEnergyValue U ha.toCoeffOn
        (H1Function.affineOnIsSobolevRegularDomain
          U.isDomain.isSobolevRegularDomain p + w.toH1Function) =
      (2 * (volume (U : Set (Vec d))).toReal)⁻¹ *
        dirichletEnergyOn' a (U : Set (Vec d)) p w.toH1Function.grad := by
  refine symmetricDirichletEnergyValue_eq ha (Filter.EventuallyEq.of_eq ?_)
  funext x
  show (p + w.toH1Function.grad x) - p = w.toH1Function.grad x
  simp

/-! ## The two infima coincide -/

/-- **The library's Dirichlet value is the continuum minimum**, up to the
normalization `2 |U|`. -/
theorem symmetricDirichletNu_eq {a : Vec d → ℝ} {U : Ch02.Domain d}
    (ha : ScalarCoeffOnData U a) (ha0 : ∀ x, 0 ≤ a x) (p : Vec d) :
    Ch02.symmetricDirichletNu U ha.toCoeffOn p =
      (2 * (volume (U : Set (Vec d))).toReal)⁻¹ *
        dirichletInfOn a (U : Set (Vec d)) p := by
  have hc : 0 < (2 * (volume (U : Set (Vec d))).toReal)⁻¹ :=
    inv_pos.mpr (by have := volume_toReal_pos U; linarith)
  rw [Ch02.symmetricDirichletNu, symmetricDirichletValueSet_eq_image ha p,
    dirichletInfOn]
  exact sInf_const_mul_image hc (dirichletEnergySet_nonempty a _ p)
    (bddBelow_dirichletEnergySet p U.measurableSet ha0)

/-! ## The headline identity -/

/-- **`p . a(U) p = min_{u in linear_p + H_0^1(U)} fint_U a |grad u|^2`**, the
identity the source uses throughout.  The left side
is the frozen finite-volume matrix underlying `abar` and `ahom`; the right side
is the continuum Dirichlet minimum of `DirichletInfimum.lean`. -/
theorem vecDot_aMatrix_eq_dirichletInfOn {a : Vec d → ℝ} {U : Ch02.Domain d}
    (ha : ScalarCoeffOnData U a) (ha0 : ∀ x, 0 ≤ a x) (p : Vec d) :
    vecDot p (matVecMul (aMatrix U ha.toCoeffOn) p) =
      (volume (U : Set (Vec d))).toReal⁻¹ *
        dirichletInfOn a (U : Set (Vec d)) p := by
  have hTheory :=
    Ch02.responseSymmetricDirichletNeumannTheory U ha.toCoeffOn ha.isSymmetric
  have hderived : Ch02.aCoarse U ha.toCoeffOn = Ch02.sigmaCoarse U ha.toCoeffOn :=
    hTheory.derived_matrices.1
  have hnu := hTheory.dirichlet_value_by_sigma p
  rw [symmetricDirichletNu_eq ha ha0 p] at hnu
  have hvol : (volume (U : Set (Vec d))).toReal ≠ 0 :=
    ne_of_gt (volume_toReal_pos U)
  show vecDot p (matVecMul (Ch02.aCoarse U ha.toCoeffOn) p) = _
  rw [hderived]
  have h2 : vecDot p (matVecMul (Ch02.sigmaCoarse U ha.toCoeffOn) p) =
      2 * ((2 * (volume (U : Set (Vec d))).toReal)⁻¹ *
        dirichletInfOn a (U : Set (Vec d)) p) := by
    rw [hnu]; ring
  rw [h2, mul_inv]
  ring

/-! ## Attainment: the per-cell Dirichlet minimizer exists -/

/-- **The continuum Dirichlet minimum is attained.**  The existence of the per-cell minimizer is not immediate from the definition, because `dirichletInfOn` is
an `sInf`; it is in fact supplied by the library's own
`Ch02.responseSymmetricDirichletNeumannTheory`, whose `dirichlet_minimizer_exists`
field produces a minimizer of the symmetric Dirichlet energy, and the
identification of the two competitor classes transports it.

This is the object Step 3  calls *"the
`A_{N-1}^{(R)}`-Dirichlet minimizer with boundary values `v|_{dT}`"*, at boundary
values `linear_p`. -/
theorem exists_h10Function_dirichletEnergyOn'_eq_dirichletInfOn {a : Vec d → ℝ}
    {U : Ch02.Domain d} (ha : ScalarCoeffOnData U a) (ha0 : ∀ x, 0 ≤ a x)
    (p : Vec d) :
    ∃ w : H10Function (U : Set (Vec d)),
      dirichletEnergyOn' a (U : Set (Vec d)) p w.toH1Function.grad =
        dirichletInfOn a (U : Set (Vec d)) p := by
  let : IsFiniteMeasure (volume.restrict (U : Set (Vec d))) :=
    U.isDomain.isFiniteMeasure_restrict_volume
  have hc : 0 < (2 * (volume (U : Set (Vec d))).toReal)⁻¹ :=
    inv_pos.mpr (by have := volume_toReal_pos U; linarith)
  have hTheory :=
    Ch02.responseSymmetricDirichletNeumannTheory U ha.toCoeffOn ha.isSymmetric
  obtain ⟨u, hadm, hmin⟩ := hTheory.dirichlet_minimizer_exists p
  obtain ⟨-, w, hw⟩ := hadm
  refine ⟨w, le_antisymm ?_ (dirichletInfOn_le U.measurableSet ha0 w)⟩
  refine le_csInf (dirichletEnergySet_nonempty a _ p) ?_
  rintro E ⟨w', rfl⟩
  have hcmp := hmin _ (isSymmetricDirichletAdmissible_affine_add p w')
  rw [symmetricDirichletEnergyValue_eq ha hw,
    symmetricDirichletEnergyValue_affine_add ha p w'] at hcmp
  exact le_of_mul_le_mul_left hcmp hc

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
