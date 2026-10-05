module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6GoodScale
public import Homogenization.CoarseGraining.Translation
public import Homogenization.Geometry.TriadicCubeTranslation
public import Homogenization.Internal.Ch02.Adapters

@[expose] public section

/-!
# The section 6 annular carrier

This module expands the frozen finite-`q = 2` error carrier
`section6HomogenizationError` into the family of local paper probes on the
scale-`n` descendants of the centered cube, and transports each of those local
probes onto the centered cube of the corresponding scale.  These are the two
purely structural steps that precede the annular decomposition of
`p.good.scale.mathcal.E`; no good-event input is used here.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Filter MeasureTheory Homogenization Homogenization.Book
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ## Expansion of the frozen error carrier -/

/-- The frozen finite-`q = 2` error carrier, expanded: the `p = ∞` scale
aggregation squares away, leaving the weighted series of descendant probe
maxima. -/
theorem paperHomogenizationError_infinity_two_eq_weighted_series
    (Q : TriadicCube d) (n : ℤ) (s : ℝ)
    (a : Ch02.TriadicCoeffFamily d) (alpha : ℝ) :
    paperHomogenizationError Q n s .infinity (.finite 2) a alpha =
      (∑' l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s 2 l) *
        paperMaxDescendantProbeAtScale Q (n - (l : ℤ)) a alpha) ^ (1 / 2 : ℝ) := by
  show paperHomogenizationErrorFinite Q n s .infinity 2 a alpha = _
  unfold paperHomogenizationErrorFinite
  congr 1
  refine tsum_congr fun l => ?_
  congr 1
  show (paperMaxDescendantProbeAtScale Q (n - (l : ℤ)) a alpha ^ (1 / 2 : ℝ))
      ^ (2 : ℝ) = _
  rw [← ENNReal.rpow_mul]
  norm_num

/-! ## Transport of the local probe onto the centered cube -/

/-- Translating the potential sample translates the cutoff coefficient. -/
theorem translateCoeffField_scalarCoeffField_aCutoff
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z : Vec d) :
    Homogenization.translateCoeffField z
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L ω)) =
      scalarCoeffField
        (_root_.SubdiffusiveProcess.Model.aCutoff M L (translatePotentialSample z ω)) := by
  funext x
  simp only [Homogenization.translateCoeffField, scalarCoeffField,
    _root_.SubdiffusiveProcess.Model.aCutoff, translatePotentialSample,
    _root_.SubdiffusiveProcess.Model.PotentialField.translate_apply]
  rfl

/-- The local paper probe on a triadic cube equals the probe on the centered
cube of the same scale, evaluated at the translated sample.  This is the
carrier form in which the frozen `section6Response` observables are stated. -/
theorem paperScalarProbe_aCutoffFamily_eq_origin
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) (alpha : ℝ) (e : Vec d) :
    paperScalarProbe Q (aCutoffFamily M L ω) alpha e =
      paperScalarProbe (Homogenization.originCube d Q.scale)
        (aCutoffFamily M L
          (translatePotentialSample (Homogenization.triadicCubeShift Q) ω))
        alpha e := by
  unfold paperScalarProbe J
  rw [Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ,
    Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ]
  show Homogenization.ResponseJ (Homogenization.openCubeSet Q) _ _
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L ω)) = _
  rw [Homogenization.openCubeSet_eq_translateSet_originCube_of_triadicCube Q,
    Homogenization.ResponseJ_translateSet_eq_translateCoeffField,
    translateCoeffField_scalarCoeffField_aCutoff]
  rfl

/-! ## The descendant index set is the paper's triadic grid in the cube -/

/-- The translation vector of a scale-`n` cube lies on the scale-`n` triadic
grid. -/
theorem onTriadicGrid_triadicCubeShift_of_scale
    {n : ℕ} {R : TriadicCube d} (hR : R.scale = (n : ℤ)) :
    OnTriadicGrid n (Homogenization.triadicCubeShift R) := by
  intro i
  refine ⟨R.index i, ?_⟩
  simp only [Homogenization.triadicCubeShift, Homogenization.cubeScaleFactor, hR,
    zpow_natCast]
  ring

/-- The translation vector of a descendant of the centered cube `□_m` lies in
the open cube `□_m`. -/
theorem triadicCubeShift_mem_cube_of_mem_descendantsAtScale
    {m : ℕ} {k : ℤ} {R : TriadicCube d} (hk : k ≤ (m : ℤ))
    (hR : R ∈ Homogenization.descendantsAtScale
      (Homogenization.originCube d (m : ℤ)) k) :
    Homogenization.triadicCubeShift R ∈ cube d (m : ℤ) := by
  have hsub : Homogenization.cubeSet R ⊆
      Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) :=
    Homogenization.cubeSet_subset_of_mem_descendantsAtScale hk hR
  set f : ℝ := Homogenization.cubeScaleFactor R with hf
  have hfpos : 0 < f := zpow_pos (by norm_num) _
  have hcenter : Homogenization.triadicCubeShift R ∈ Homogenization.cubeSet R := by
    intro i
    constructor
    · have : ((R.index i : ℝ) - 1 / 2) * f ≤ (R.index i : ℝ) * f := by nlinarith
      simpa [Homogenization.triadicCubeShift, hf] using this
    · have : (R.index i : ℝ) * f < ((R.index i : ℝ) + 1 / 2) * f := by nlinarith
      simpa [Homogenization.triadicCubeShift, hf] using this
  have hcorner : (fun i => ((R.index i : ℝ) - 1 / 2) * f) ∈
      Homogenization.cubeSet R := by
    intro i
    exact ⟨le_rfl, by nlinarith⟩
  intro i
  have h1 := hsub hcenter i
  have h2 := (hsub hcorner i).1
  simp only [Homogenization.originCube,
    Homogenization.triadicCubeShift] at h1 h2 ⊢
  constructor
  · nlinarith [h2]
  · exact h1.2

/-! ## The frozen carrier as a series of transported local probes -/

/-- The scale-`k` descendant probe maximum of the centered cube, written as a
supremum of local probes on the centered cube of scale `k` at translated
samples.  This is the exact shape in which the frozen `section6Response`
observables are indexed. -/
theorem paperMaxDescendantProbeAtScale_aCutoffFamily_eq_transported
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) (k : ℤ) (alpha : ℝ) :
    paperMaxDescendantProbeAtScale Q k (aCutoffFamily M L ω) alpha =
      ⨆ R : {R : TriadicCube d // R ∈ Homogenization.descendantsAtScale Q k},
        ⨆ e : {e : Vec d // Homogenization.vecNormSq e = 1},
          ENNReal.ofReal
            (paperScalarProbe (Homogenization.originCube d k)
              (aCutoffFamily M L
                (translatePotentialSample
                  (Homogenization.triadicCubeShift R.1) ω))
              alpha e) := by
  unfold paperMaxDescendantProbeAtScale
  refine iSup_congr fun R => ?_
  unfold paperScalarProbeMax
  refine iSup_congr fun e => ?_
  rw [paperScalarProbe_aCutoffFamily_eq_origin M L ω R.1 alpha e,
    Homogenization.scale_eq_of_mem_descendantsAtScale R.2]

/-- The frozen section 6 error carrier, fully expanded: a weighted `ℓ²`-in-scales
series of suprema of local probes on centered cubes at translated samples.

This is the deterministic starting point of the annular decomposition
(`e.mathcalE.annular.decomp.pre`).  The local probes still carry the *global*
cutoff `L` and the *global* normalization `(b_{L,m})_{□_m}`; converting them to
the frozen `section6Response M n n` atoms (local cutoff `n`, normalization
`ahom_n`) is the separate coefficient-sensitivity step. -/
theorem section6HomogenizationError_eq_transported_series
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s : ℝ) (L m : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z : Vec d) :
    section6HomogenizationError M s L m ω z =
      ((∑' l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s 2 l) *
          ⨆ R : {R : TriadicCube d //
              R ∈ Homogenization.descendantsAtScale
                (Homogenization.originCube d (m : ℤ)) ((m : ℤ) - (l : ℤ))},
            ⨆ e : {e : Vec d // Homogenization.vecNormSq e = 1},
              ENNReal.ofReal
                (paperScalarProbe
                  (Homogenization.originCube d ((m : ℤ) - (l : ℤ)))
                  (aCutoffFamily M L
                    (translatePotentialSample
                      (Homogenization.triadicCubeShift R.1)
                      (translatePotentialSample z ω)))
                  (tailCoefficientCubeAverage M L m
                    (translatePotentialSample z ω)) e))
        ^ (1 / 2 : ℝ)).toReal := by
  unfold section6HomogenizationError
  rw [paperHomogenizationError_infinity_two_eq_weighted_series]
  congr 2
  refine tsum_congr fun l => ?_
  rw [paperMaxDescendantProbeAtScale_aCutoffFamily_eq_transported]

end

end SubdiffusiveProcess.CoarseGrainingVocab
