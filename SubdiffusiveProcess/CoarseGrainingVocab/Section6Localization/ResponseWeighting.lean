module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.RatioCollapse

@[expose] public section

/-!
# Section 6 localization: weighting the transported response

This module formalizes the response-weighting step.  The cutoff-ratio error grows like
`3^(3 s t / 16)`, the local response like `3^(s t / 8)`, and the annular
weight is `3^(-3 s t / 2)`; their product is exactly `3^(-s t)`.

The proof-role split mirrors the abstract-weight assembly in
`Algsuperdiff/Section4/Provider/Annular/Ugly.lean`: exponent arithmetic is
kept separate from the model-facing sensitivity estimate.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization

open MeasureTheory Homogenization Homogenization.Book

noncomputable section

variable {d : ℕ}

/-- The outer annular weight is stronger than the residual `3^(-u)` weight
when the scale gap `u` is nonnegative. -/
theorem responseOuterWeight_le_residualWeight {u : ℝ} (hu : 0 ≤ u) :
    (3 : ℝ) ^ (-(3 / 2) * u) ≤ (3 : ℝ) ^ (-u) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  linarith

/-- Exact cancellation of the cutoff-ratio growth, the local-response growth,
and the outer annular weight. -/
theorem responseErrorWeight_identity (u : ℝ) :
    (3 : ℝ) ^ (-(3 / 2) * u) *
        ((3 : ℝ) ^ (3 * u / 16)) ^ 2 *
        (3 : ℝ) ^ (u / 8) =
      (3 : ℝ) ^ (-u) := by
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (3 * u / 16)) 2,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-- The good-response growth factor is at least one on a nonnegative scale
gap. -/
theorem one_le_responseGrowth {u : ℝ} (hu : 0 ≤ u) :
    1 ≤ (3 : ℝ) ^ (u / 8) := by
  exact Real.one_le_rpow (by norm_num) (by linarith)

/-- Abstract response-weighting assembly.  This is the small algebraic kernel
behind the model-facing theorem: `P` is the transported probe, `J` the local
response, `E` the squared ratio error, and `A`, `G`, `w`, `v` are the four
triadic weights. -/
theorem weightedTransport_of_bounds
    {P J E C A B G w v : ℝ}
    (hP : P ≤ 2 * J + 3 * E * (J + 1))
    (hE : E ≤ 2 * (C * A * B) ^ 2)
    (hJ0 : 0 ≤ J) (hJ : J ≤ G) (hG1 : 1 ≤ G)
    (hw0 : 0 ≤ w) (hwv : w ≤ v)
    (hcollapse : w * A ^ 2 * G = v) :
    w * P ≤ 2 * v * J + 12 * C ^ 2 * v * B ^ 2 := by
  have hG0 : 0 ≤ G := zero_le_one.trans hG1
  have hJone0 : 0 ≤ J + 1 := by linarith
  have hJone : J + 1 ≤ 2 * G := by linarith only [hJ, hG1]
  have hEG : E * (J + 1) ≤
      (2 * (C * A * B) ^ 2) * (2 * G) :=
    mul_le_mul hE hJone hJone0 (mul_nonneg (by norm_num) (sq_nonneg _))
  have hmain : w * (2 * J) ≤ 2 * v * J := by
    calc
      w * (2 * J) = 2 * w * J := by ring
      _ ≤ 2 * v * J := by gcongr
  have herror : w * (3 * E * (J + 1)) ≤
      12 * C ^ 2 * v * B ^ 2 := by
    calc
      w * (3 * E * (J + 1)) = 3 * w * (E * (J + 1)) := by ring
      _ ≤ 3 * w * ((2 * (C * A * B) ^ 2) * (2 * G)) := by gcongr
      _ = 12 * C ^ 2 * (w * A ^ 2 * G) * B ^ 2 := by ring
      _ = 12 * C ^ 2 * v * B ^ 2 := by rw [hcollapse]
  calc
    w * P ≤ w * (2 * J + 3 * E * (J + 1)) :=
      mul_le_mul_of_nonneg_left hP hw0
    _ = w * (2 * J) + w * (3 * E * (J + 1)) := by ring
    _ ≤ 2 * v * J + 12 * C ^ 2 * v * B ^ 2 := add_le_add hmain herror

/-- Model-facing response weighting on a scale-`n` descendant in the printed
annulus.  The conclusion deliberately retains the saturated combined-ratio
budget as one square; splitting it into field, shell, and deterministic drift
terms belongs to the next assembly layer. -/
theorem weightedPaperScalarProbe_tailAverage_le_of_goodEvent_descendant
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m n j : ℕ}
    (hnm : n ≤ m) (hmL : m ≤ L) {s : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (hj : j ≤ m) (hnj : n + 2 ≤ j)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ))
    (hann : triadicCubeShift R ∈ cube d j \ cube d (j - 1))
    {e : Vec d} (he : vecNormSq e = 1)
    (hgood : omega ∈ goodEvent M none m 0 1 s)
    (hBdd : BddAbove {a : ℝ | ∃ y ∈
      translatedCube d ((m + 1 + (m - n) : ℕ) : ℤ) 0,
        a = |(∏ i ∈ Finset.Icc (m - (m - n)) (m + (m - n)),
            Real.exp |omega i y|) +
          ∏' i : ℕ, if m + (m - n) ≤ i then
            Real.exp (4 * |omega i y - omega i 0|) else 1|}) :
    (3 : ℝ) ^ (-(3 / 2) *
          (s * ((m - n : ℕ) : ℝ))) *
        paperScalarProbe (originCube d (n : ℤ))
          (aCutoffFamily M L
            (translatePotentialSample (triadicCubeShift R) omega))
          (tailCoefficientCubeAverage M L m omega) e ≤
      2 * (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
          section6Response M n n omega (triadicCubeShift R) e +
        12 * ratioCollapseConstant d ^ 2 *
          (3 : ℝ) ^ (-(s * ((m - n : ℕ) : ℝ))) *
          (min 1 (longRatioGradientTail m omega +
            supNormOn (cube d n)
              (shellBlock m n
                (translatePotentialSample (triadicCubeShift R) omega)) +
            _root_.SubdiffusiveProcess.Model.tauSq M.P *
              ((m - n : ℕ) : ℝ))) ^ 2 := by
  let T : ℝ := ((m - n : ℕ) : ℝ)
  let u : ℝ := s * T
  let C : ℝ := ratioCollapseConstant d
  let A : ℝ := (3 : ℝ) ^ ((3 * s * T) / 16)
  let B : ℝ := min 1 (longRatioGradientTail m omega +
    supNormOn (cube d n)
      (shellBlock m n
        (translatePotentialSample (triadicCubeShift R) omega)) +
    _root_.SubdiffusiveProcess.Model.tauSq M.P * T)
  let Jloc : ℝ := section6Response M n n omega (triadicCubeShift R) e
  let E : ℝ := cutoffRatioError M n L
    (translatePotentialSample (triadicCubeShift R) omega)
    (Ch02.cubeDomain (originCube d (n : ℤ)))
    (tailCoefficientCubeAverage M L m omega)
  let P : ℝ := paperScalarProbe (originCube d (n : ℤ))
    (aCutoffFamily M L
      (translatePotentialSample (triadicCubeShift R) omega))
    (tailCoefficientCubeAverage M L m omega) e
  let G : ℝ := (3 : ℝ) ^ (u / 8)
  let w : ℝ := (3 : ℝ) ^ (-(3 / 2) * u)
  let v : ℝ := (3 : ℝ) ^ (-u)
  have hgap : (m : ℝ) - (n : ℝ) = T := by
    dsimp only [T]
    rw [Nat.cast_sub hnm]
  have hRscale : R.scale = (n : ℤ) :=
    scale_eq_of_mem_descendantsAtScale hR
  have hgrid : OnTriadicGrid n (triadicCubeShift R) :=
    onTriadicGrid_triadicCubeShift_of_scale hRscale
  have hJ : Jloc ≤ G := by
    have hraw := hgood.2.2 j n hj hnj (triadicCubeShift R)
      (by simpa using hgrid) (by simpa using hann) e he
    simpa only [Option.getD_none, min_self, one_pow, one_mul, sub_zero,
      hgap, Jloc, G, u] using hraw
  have hJ0 : 0 ≤ Jloc := by
    dsimp only [Jloc, section6Response, paperScalarProbe]
    exact Ch02.responseJ_nonneg _ _ _ _
  have hP : P ≤ 2 * Jloc + 3 * E * (Jloc + 1) := by
    exact paperScalarProbe_translatedCutoff_tailAverage_le_section6Response
      M L m n omega (triadicCubeShift R) e he
  have hE : E ≤ 2 * (C * A * B) ^ 2 := by
    exact cutoffRatioError_tailAverage_le_of_goodEvent_descendant
      M hnm hmL hsLower hsUpper omega hR hgood hBdd
  have hu0 : 0 ≤ u := by
    dsimp only [u, T]
    exact mul_nonneg (le_trans (mul_nonneg (by norm_num) (sq_nonneg M.delta)) hsLower)
      (by positivity)
  have hG1 : 1 ≤ G := one_le_responseGrowth hu0
  have hw0 : 0 ≤ w := Real.rpow_nonneg (by norm_num) _
  have hwv : w ≤ v := responseOuterWeight_le_residualWeight hu0
  have hcollapse : w * A ^ 2 * G = v := by
    dsimp only [w, A, G, v, u]
    convert responseErrorWeight_identity (s * T) using 1
    all_goals ring_nf
  have hweighted := weightedTransport_of_bounds hP hE hJ0 hJ hG1 hw0 hwv hcollapse
  simpa only [P, Jloc, C, B, w, v, u, T] using hweighted

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
