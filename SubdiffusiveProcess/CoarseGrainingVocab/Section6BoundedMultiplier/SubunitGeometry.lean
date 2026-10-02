import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.LocalSubunitReadout

/-!
# Geometry of below-scale target cubes

The target in the bounded-multiplier statement is a translated cube of scale
`m-j`.  These lemmas expose its centre and its exact radius in the project
supremum metric, ready for the concentric small-contrast readout.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

noncomputable section

variable {d : ℕ}

/-- A translated paper cube is exactly a ball for the project supremum
metric. -/
theorem translatedCube_eq_metricBall (m : ℤ) (z : Vec d) :
    translatedCube d m z =
      Metric.ball z (1 / 2 * (3 : ℝ) ^ m) := by
  have hr : 0 < (1 / 2 : ℝ) * (3 : ℝ) ^ m := by positivity
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    have huCoord : ∀ i, |u i| < 1 / 2 * (3 : ℝ) ^ m := by
      intro i
      have hi := (mem_openCubeSet_originCube_iff.mp hu) i
      exact (abs_lt.mpr ⟨by linarith [hi.1], by linarith [hi.2]⟩)
    have huNorm : ‖u‖ < 1 / 2 * (3 : ℝ) ^ m := by
      rw [pi_norm_lt_iff hr]
      intro i
      simpa only [Real.norm_eq_abs] using huCoord i
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using huNorm
  · intro hx
    have hxNorm : ‖x - z‖ < 1 / 2 * (3 : ℝ) ^ m := by
      rw [Metric.mem_ball, dist_eq_norm] at hx
      simpa only [norm_sub_rev] using hx
    refine ⟨x - z, ?_, by ext i; simp⟩
    change x - z ∈ openCubeSet (originCube d m)
    rw [mem_openCubeSet_originCube_iff]
    intro i
    have hi : |(x - z) i| < 1 / 2 * (3 : ℝ) ^ m := by
      have hcoord := (pi_norm_lt_iff hr).mp hxNorm i
      simpa only [Real.norm_eq_abs] using hcoord
    have hi' := abs_lt.mp hi
    constructor
    · calc
        -(1 / 2 : ℝ) * (3 : ℝ) ^ m =
            -(1 / 2 * (3 : ℝ) ^ m) := by ring
        _ < (x - z) i := hi'.1
    · exact hi'.2

/-- A middle-half target has a centre which is itself collared in the ambient
cube, and the whole target lies in every concentric ball whose radius is at
least its exact cube radius. -/
theorem exists_middleHalfSubcube_center_and_subset_ball
    {m : ℤ} {z : Vec d} {j : ℕ} {B' : Set (Vec d)}
    (hB' : IsMiddleHalfSubcube m z j B') :
    ∃ z' : Vec d,
      B' = translatedCube d (m - j) z' ∧
      ‖z' - z‖ ≤ (3 : ℝ) ^ m / 4 ∧
      ∀ {r : ℝ}, 1 / 2 * (3 : ℝ) ^ (m - j) ≤ r →
        B' ⊆ Metric.ball z' r := by
  rcases hB' with ⟨z', rfl, hcollar⟩
  have hr : 0 < (1 / 2 : ℝ) * (3 : ℝ) ^ (m - j) := by positivity
  have hz' : z' ∈ translatedCube d (m - j) z' := by
    rw [translatedCube_eq_metricBall]
    exact Metric.mem_ball_self hr
  refine ⟨z', rfl, hcollar z' hz', ?_⟩
  intro r hrad
  rw [translatedCube_eq_metricBall]
  exact Metric.ball_subset_ball hrad

/-- Once the target cube fits inside a triadic sub-ball of the random local
radius, its centre is a valid collared centre for the Caccioppoli-priced
small-contrast contraction, and the target-to-ball inclusion is returned in
the same package. -/
theorem exists_middleHalfSubcube_localSubunitBall_caccioppoli
    {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (m : ℤ) (z : Vec d) (j n : ℕ)
    {B' : Set (Vec d)} (hB' : IsMiddleHalfSubcube m z j B')
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {theta : Vec d → ℝ}
    (hthetaCont : ContinuousOn theta (translatedCube d m z))
    {b : ℝ} (hb : 0 < b)
    (hthetaClose : ∀ y ∈ translatedCube d m z,
      |b⁻¹ * theta y - 1| ≤ boundedMultiplierEpsilonStar d)
    {h : H1Function (translatedCube d m z)}
    (hharm : IsWeaklyHarmonicOn
      (fun y ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega y * theta y)
      (translatedCube d m z) h)
    (hfit : 1 / 2 * (3 : ℝ) ^ (m - j) ≤
      (boundedMultiplierLocalRadius M L m z omega / 2) /
          (2 * (d : ℝ)) * (3 : ℝ) ^ (-((n + 1 : ℕ) : ℝ))) :
    ∃ z' : Vec d, ∃ p ∈ shellCoverShifts d m,
      B' = translatedCube d (m - j) z' ∧
      B' ⊆ Metric.ball z'
        ((boundedMultiplierLocalRadius M L m z omega / 2) /
            (2 * (d : ℝ)) * (3 : ℝ) ^ (-((n + 1 : ℕ) : ℝ))) ∧
      z' ∈ boundedMultiplierCoverCell d m z p ∧
      euclideanBall z' (boundedMultiplierLocalRadius M L m z omega) ⊆
        boundedMultiplierCoverCell d m z p ∧
      oscillationOn
          (Metric.ball z'
            ((boundedMultiplierLocalRadius M L m z omega / 2) /
              (2 * (d : ℝ)) *
                (3 : ℝ) ^ (-((n + 1 : ℕ) : ℝ))))
          (euclideanBallAverageRepresentative h.toFun) ≤
        smallContrastSchauderConstant d *
            halfBallCaccioppoliDataPrice d z'
              (boundedMultiplierLocalRadius M L m z omega) h.toFun
              (averageOn (boundedMultiplierCoverCell d m z p) h.toFun) *
          (boundedMultiplierLocalRadius M L m z omega / 2) *
            (3 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) := by
  obtain ⟨z', hB'eq, hcollar, hsub⟩ :=
    exists_middleHalfSubcube_center_and_subset_ball hB'
  obtain ⟨p, hp, hz'cell, hballCell, hcontract⟩ :=
    exists_coverCell_localSubunitContraction_caccioppoli hd M L m z omega
      hcollar hthetaCont hb hthetaClose hharm n
  refine ⟨z', p, hp, hB'eq, hsub hfit, hz'cell, hballCell, ?_⟩
  simpa only using hcontract

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
