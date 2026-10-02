import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowLocalPerCell
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.LocalComparisonDatum
import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.H1Casts




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open Homogenization.Book
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped ENNReal

noncomputable section

/-- The open stopping-cell carrier is the translated origin cube. -/
theorem fluxRowRiesz_translatedCube_eq_translateSet {d : ℕ}
    (m : ℤ) (z : Vec d) :
    translatedCube d m z = translateSet z (openCubeSet (originCube d m)) := by
  rw [translatedCube, cube,
    SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.image_add_eq_translateSet]

/-- Cast a function on the source-facing stopping cell to the literal
translated-set carrier consumed by the H1 translation API. -/
def fluxRowRieszTranslatedH1 {d : ℕ} {m : ℤ} (z : Vec d)
    (u : H1Function (translatedCube d m z)) :
    H1Function (translateSet z (openCubeSet (originCube d m))) :=
  Ch03.castH1Domain (fluxRowRiesz_translatedCube_eq_translateSet m z) u

/-- Weak equations are invariant under a definitional cast of their domain. -/
theorem fluxRowRiesz_isDivFormWeakSolutionOn_castH1Domain {d : ℕ}
    {U V : Set (Vec d)} (hUV : U = V) {a : Vec d → ℝ}
    {u : H1Function U} {g : Vec d → Vec d}
    (hu : IsDivFormWeakSolutionOn a U u g) :
    IsDivFormWeakSolutionOn a V (Ch03.castH1Domain hUV u) g := by
  subst V
  exact hu

/-- Recenter a physical H1 function from an arbitrary stopping cell. -/
def fluxRowRieszUntranslatedH1 {d : ℕ} {m : ℤ} (z : Vec d)
    (u : H1Function (translatedCube d m z)) :
    H1Function (openCubeSet (originCube d m)) :=
  H1Function.untranslate z (fluxRowRieszTranslatedH1 z u)

/-- Every translated cutoff family is symmetric.  This public version is the
coefficient-side premise needed when the centered Section 2 anchor is applied
after recentering a stopping cell. -/
theorem fluxRowRiesz_aCutoffFamily_isSymmetric {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    ∀ Q, Ch02.CoeffOn.IsSymmetric ((aCutoffFamily M L omega).coeffOn Q) := by
  intro Q
  filter_upwards with x
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp only [aCutoffFamily, aCutoffTriadicData,
    ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
    ScalarCoeffOnData.toCoeffOn, scalarCoeffField, Matrix.smul_apply]
  by_cases hij : i = j
  · subst j
    rfl
  · simp [hij, Ne.symm hij]

/-- The centered forcing field obtained from a physical field on a cell with
centre `z`. -/
def fluxRowRieszRecenteredForce {d : ℕ} {m : ℤ}
    {sigma : ℝ} (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1)
    (z : Vec d) (g : Vec d → Vec d)
    (hg : MemCubeEuclideanFullWsp (originCube d m)
      (fluxRowLocalUpperOrder sigma hsigma) FiniteLpExponent.two
      (fun x ↦ g (x + z))) :
    CubeEuclideanWspField (originCube d m)
      (fluxRowLocalUpperOrder sigma hsigma) FiniteLpExponent.two where
  toField := fun x ↦ g (x + z)
  euclideanMemLp := hg.1
  euclideanMemWsp := hg.2

@[simp] theorem fluxRowRieszRecenteredForce_toField {d : ℕ} {m : ℤ}
    {sigma : ℝ} (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1)
    (z : Vec d) (g : Vec d → Vec d)
    (hg : MemCubeEuclideanFullWsp (originCube d m)
      (fluxRowLocalUpperOrder sigma hsigma) FiniteLpExponent.two
      (fun x ↦ g (x + z))) :
    (fluxRowRieszRecenteredForce hsigma z g hg).toField =
      fun x ↦ g (x + z) := rfl

/-- The root defect produced after recentering is literally the physical
cutoff flux defect evaluated in translated coordinates. -/
theorem fluxRowRiesz_recenteredRootFlux_toField {d : ℕ} {m : ℤ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (z : Vec d)
    (alpha : ℝ) (u : H1Function (translatedCube d m z)) :
    (centeredCubeRootFluxDefectL2Field m
      ((aCutoffFamily M L (translatePotentialSample z omega)).coeffOn
        (originCube d m)) alpha
      (fluxRowRieszUntranslatedH1 z u)).toField =
      fun x ↦ matVecMul
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (x + z) -
          scalarMatrix (d := d) alpha) (u.grad (x + z)) := by
  funext x
  simp only [centeredCubeRootFluxDefectL2Field,
    fluxRowRieszUntranslatedH1, H1Function.untranslate_grad,
    fluxRowRieszTranslatedH1, Ch03.castH1Domain_grad]
  rw [show
      ((aCutoffFamily M L (translatePotentialSample z omega)).coeffOn
        (originCube d m)).toCoeffField x =
        scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (x + z) by
    rfl]

/-- **Translated per-cell flux estimate.**  One dimensional constant works
for every stopping-cell centre.  The physical equation is recentered, the
force is bundled in the precise fractional space required by the Section 2
anchor, and the scalar comparison is constructed rather than assumed.

The returned inequality is expressed in centered coordinates, with
`fluxRowRiesz_recenteredRootFlux_toField` identifying its left-hand field with
the physical translated flux. -/
theorem exists_fluxRowRiesz_translatedCell_rootFlux_le
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        (m n : ℤ), ∀ hnm : n < m, ∀ z : Vec d,
      ∀ (alpha sigma : ℝ), 0 < alpha →
      ∀ hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1,
      ∀ (g : Vec d → Vec d) (u : H1Function (translatedCube d m z)),
        MemCubeEuclideanFullWsp (originCube d m)
          (fluxRowLocalUpperOrder sigma hsigma) FiniteLpExponent.two
          (fun x ↦ g (x + z)) →
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
          (translatedCube d m z) u g →
        ∃ (g0 : CubeEuclideanWspField (originCube d m)
              (fluxRowLocalUpperOrder sigma hsigma) FiniteLpExponent.two)
          (u0 v0 : H1Function (openCubeSet (originCube d m))),
          g0.toField = (fun x ↦ g (x + z)) ∧
          u0 = fluxRowRieszUntranslatedH1 z u ∧
          IsForcedEquation (originCube d m)
            ((aCutoffFamily M L (translatePotentialSample z omega)).coeffOn
              (originCube d m)) u0 g0.toField ∧
          IsScalarForcedEquation (originCube d m) alpha v0 g0.toField ∧
          HasH10Difference (originCube d m) u0 v0 ∧
          ENNReal.ofReal (Real.rpow 3 (-sigma * (m : ℝ))) *
              paperNegativeFractionalDual (originCube d m)
                (fluxRowLocalOrder sigma hsigma) FiniteLpExponent.two
                (centeredCubeRootFluxDefectL2Field m
                  ((aCutoffFamily M L
                    (translatePotentialSample z omega)).coeffOn
                      (originCube d m)) alpha u0) ≤
            fluxRowLocalCoarseGrainingRHS C m n hnm
              (aCutoffFamily M L (translatePotentialSample z omega))
              alpha sigma hsigma g0 u0 := by
  obtain ⟨C, hC, hmain⟩ :=
    exists_fluxRowLocal_rootFlux_le_coarseGrainingRHS d hd
  refine ⟨C, hC, ?_⟩
  intro M L omega m n hnm z alpha sigma halpha hsigma g u hg hu
  let g0 := fluxRowRieszRecenteredForce hsigma z g hg
  let u0 : H1Function (openCubeSet (originCube d m)) :=
    fluxRowRieszUntranslatedH1 z u
  have hgTwo : MemLp g0.toField 2 (normalizedCubeMeasure (originCube d m)) :=
    MemCubeEuclideanFullWsp.memLpTwo (by norm_num)
      (show MemCubeEuclideanFullWsp (originCube d m)
        (fluxRowLocalUpperOrder sigma hsigma) FiniteLpExponent.two g0.toField from
        ⟨g0.euclideanMemLp, g0.euclideanMemWsp⟩)
  have hgCube : MemVectorL2 (cubeSet (originCube d m)) g0.toField :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure
      (originCube d m) hgTwo
  have hgOpen : MemVectorL2 (openCubeSet (originCube d m)) g0.toField := by
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet (originCube d m)]
      using hgCube
  let v0 : H1Function (openCubeSet (originCube d m)) :=
    sourceForcedReplacement (scalarConstantCoeffMatrix (d := d) halpha) u0 hgOpen
  have huT : IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
      (translateSet z (openCubeSet (originCube d m)))
      (fluxRowRieszTranslatedH1 z u) g := by
    exact fluxRowRiesz_isDivFormWeakSolutionOn_castH1Domain
      (fluxRowRiesz_translatedCube_eq_translateSet m z) hu
  have hu0 : IsForcedEquation (originCube d m)
      ((aCutoffFamily M L (translatePotentialSample z omega)).coeffOn
        (originCube d m)) u0 g0.toField := by
    simpa only [g0, fluxRowRieszRecenteredForce_toField, u0] using
      isForcedEquation_aCutoff_untranslate M L omega (originCube d m) z huT
  have hv0 : IsScalarForcedEquation (originCube d m) alpha v0 g0.toField :=
    isScalarForcedEquation_sourceForcedReplacement halpha u0 hgOpen
  have huv0 : HasH10Difference (originCube d m) u0 v0 :=
    hasH10Difference_sourceForcedReplacement
      (scalarConstantCoeffMatrix (d := d) halpha) u0 hgOpen
  refine ⟨g0, u0, v0, rfl, rfl, hu0, hv0, huv0, ?_⟩
  exact hmain m n hnm
    (aCutoffFamily M L (translatePotentialSample z omega))
    (fluxRowRiesz_aCutoffFamily_isSymmetric M L
      (translatePotentialSample z omega))
    alpha sigma halpha hsigma g0 u0 v0 hu0 hv0 huv0

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
