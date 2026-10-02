import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Geometry.CoordinateFold
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryMeanControlReduction
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Covering.Differentiation




open MeasureTheory Set Filter Topology
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}

/-- A cube of side `s ≤ r` centered at a point `x` of the larger cube `centeredCube z r hr`
meets it in at least `(s / 2) ^ d` volume — half the side length survives in *every* coordinate
regardless of how close `x` sits to `z`'s cube boundary, since each coordinate interval can be
clipped from at most one side when `s ≤ r`. The bound is independent of `x`'s position, which is
what makes it usable uniformly as `x` ranges over the whole (open) larger cube. -/
theorem aux_campanato_cube_inter_volume_ge (z x : SpatialCoordinates d)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hsr : s ≤ r)
    (hx : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d))) :
    (s / 2) ^ d ≤
      volume.real ((centeredCube x s hs : Set (SpatialCoordinates d)) ∩
        (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  have hxpi : x ∈ Set.pi Set.univ (fun i => Set.Ioo (z i - r / 2) (z i + r / 2)) := by
    rw [← centeredCube_eq_pi]; exact hx
  have hlen : ∀ i : Fin d, (s / 2 : ℝ) ≤
      min (x i + s / 2) (z i + r / 2) - max (x i - s / 2) (z i - r / 2) := by
    intro i
    have hxi := hxpi i (Set.mem_univ i)
    simp only [Set.mem_Ioo] at hxi
    obtain ⟨hxi1, hxi2⟩ := hxi
    rcases le_or_gt (s / 2) (x i - (z i - r / 2)) with ha | ha <;>
      rcases le_or_gt (s / 2) ((z i + r / 2) - x i) with hb | hb <;>
      simp only [min_def, max_def] <;> split_ifs <;> linarith
  have hinterpi : (centeredCube x s hs : Set (SpatialCoordinates d)) ∩
      (centeredCube z r hr : Set (SpatialCoordinates d)) =
      Set.pi Set.univ
        (fun i => Set.Ioo (x i - s / 2) (x i + s / 2) ∩ Set.Ioo (z i - r / 2) (z i + r / 2)) := by
    rw [centeredCube_eq_pi x hs, centeredCube_eq_pi z hr]
    ext y
    simp only [Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Ioo]
    constructor
    · intro h i; exact ⟨h.1 i, h.2 i⟩
    · intro h; exact ⟨fun i => (h i).1, fun i => (h i).2⟩
  have hvol : volume ((centeredCube x s hs : Set (SpatialCoordinates d)) ∩
      (centeredCube z r hr : Set (SpatialCoordinates d))) =
      ∏ i : Fin d,
        volume (Set.Ioo (x i - s / 2) (x i + s / 2) ∩ Set.Ioo (z i - r / 2) (z i + r / 2)) := by
    rw [hinterpi]; exact volume_pi_pi _
  have hprod : ∀ i : Fin d, ENNReal.ofReal (s / 2) ≤
      volume (Set.Ioo (x i - s / 2) (x i + s / 2) ∩ Set.Ioo (z i - r / 2) (z i + r / 2)) := by
    intro i
    rw [Set.Ioo_inter_Ioo, Real.volume_Ioo]
    exact ENNReal.ofReal_le_ofReal (hlen i)
  have hle : ENNReal.ofReal ((s / 2) ^ d) ≤ volume ((centeredCube x s hs : Set (SpatialCoordinates d)) ∩
      (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    rw [hvol, ENNReal.ofReal_pow (by positivity)]
    calc (ENNReal.ofReal (s / 2)) ^ d = ∏ _i : Fin d, ENNReal.ofReal (s / 2) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := Finset.prod_le_prod' (fun i _ => hprod i)
  have hfin : volume ((centeredCube x s hs : Set (SpatialCoordinates d)) ∩
      (centeredCube z r hr : Set (SpatialCoordinates d))) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono (Set.inter_subset_left)) ?_)
    rw [centeredCube_volume]; exact ENNReal.ofReal_lt_top
  have := ENNReal.toReal_mono hfin hle
  rwa [ENNReal.toReal_ofReal (by positivity)] at this

/-- Same conclusion as `aux_campanato_cube_inter_volume_ge`, but for `x` ranging over the
CLOSED cube `closedCube z r hr` (i.e. allowing `x` on the topological boundary of
`centeredCube z r hr`) rather than just the open cube. The small ball `centeredCube x s hs` and
the outer cube `centeredCube z r hr` in the conclusion are unchanged (still open) — only the
hypothesis on `x`'s position is weakened, which is exactly what boundary-clipped continuity (up
to the closed cube) needs. Same bound, same proof shape, with non-strict coordinate bounds
throughout instead of strict ones (equality is attained, not just approached, when `x` sits
exactly on the boundary). -/
theorem aux_campanato_cube_inter_volume_ge_closed (z x : SpatialCoordinates d)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hsr : s ≤ r)
    (hx : x ∈ (closedCube z r hr : Set (SpatialCoordinates d))) :
    (s / 2) ^ d ≤
      volume.real ((centeredCube x s hs : Set (SpatialCoordinates d)) ∩
        (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  have hxpi : ∀ i : Fin d, |x i - z i| ≤ r / 2 := by
    have hxb : x ∈ Metric.closedBall z (r / 2) := hx
    rw [Metric.mem_closedBall, dist_pi_le_iff (by positivity)] at hxb
    intro i
    have := hxb i
    rwa [Real.dist_eq] at this
  have hlen : ∀ i : Fin d, (s / 2 : ℝ) ≤
      min (x i + s / 2) (z i + r / 2) - max (x i - s / 2) (z i - r / 2) := by
    intro i
    have hxi := abs_le.mp (hxpi i)
    obtain ⟨hxi1, hxi2⟩ := hxi
    rcases le_or_gt (s / 2) (x i - (z i - r / 2)) with ha | ha <;>
      rcases le_or_gt (s / 2) ((z i + r / 2) - x i) with hb | hb <;>
      simp only [min_def, max_def] <;> split_ifs <;> linarith
  have hinterpi : (centeredCube x s hs : Set (SpatialCoordinates d)) ∩
      (centeredCube z r hr : Set (SpatialCoordinates d)) =
      Set.pi Set.univ
        (fun i => Set.Ioo (x i - s / 2) (x i + s / 2) ∩ Set.Ioo (z i - r / 2) (z i + r / 2)) := by
    rw [centeredCube_eq_pi x hs, centeredCube_eq_pi z hr]
    ext y
    simp only [Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Ioo]
    constructor
    · intro h i; exact ⟨h.1 i, h.2 i⟩
    · intro h; exact ⟨fun i => (h i).1, fun i => (h i).2⟩
  have hvol : volume ((centeredCube x s hs : Set (SpatialCoordinates d)) ∩
      (centeredCube z r hr : Set (SpatialCoordinates d))) =
      ∏ i : Fin d,
        volume (Set.Ioo (x i - s / 2) (x i + s / 2) ∩ Set.Ioo (z i - r / 2) (z i + r / 2)) := by
    rw [hinterpi]; exact volume_pi_pi _
  have hprod : ∀ i : Fin d, ENNReal.ofReal (s / 2) ≤
      volume (Set.Ioo (x i - s / 2) (x i + s / 2) ∩ Set.Ioo (z i - r / 2) (z i + r / 2)) := by
    intro i
    rw [Set.Ioo_inter_Ioo, Real.volume_Ioo]
    exact ENNReal.ofReal_le_ofReal (hlen i)
  have hle : ENNReal.ofReal ((s / 2) ^ d) ≤ volume ((centeredCube x s hs : Set (SpatialCoordinates d)) ∩
      (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    rw [hvol, ENNReal.ofReal_pow (by positivity)]
    calc (ENNReal.ofReal (s / 2)) ^ d = ∏ _i : Fin d, ENNReal.ofReal (s / 2) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := Finset.prod_le_prod' (fun i _ => hprod i)
  have hfin : volume ((centeredCube x s hs : Set (SpatialCoordinates d)) ∩
      (centeredCube z r hr : Set (SpatialCoordinates d))) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono (Set.inter_subset_left)) ?_)
    rw [centeredCube_volume]; exact ENNReal.ofReal_lt_top
  have := ENNReal.toReal_mono hfin hle
  rwa [ENNReal.toReal_ofReal (by positivity)] at this

/-- `x ↦ 1_{B(x,rad)}(y)` is locally constant near any `x₀` with `dist x₀ y ≠ rad` — the
sphere is the only place where membership in the moving ball can flip. -/
theorem aux_campanato_indicator_ball_continuousAt (u : SpatialCoordinates d → ℝ)
    (y : SpatialCoordinates d) {rad : ℝ} {x₀ : SpatialCoordinates d} (hx₀ : dist x₀ y ≠ rad) :
    ContinuousAt (fun x : SpatialCoordinates d => Set.indicator (Metric.ball x rad) u y) x₀ := by
  rcases hx₀.lt_or_gt with h | h
  · have hmem : x₀ ∈ Metric.ball y rad := by rw [Metric.mem_ball]; exact h
    have heq : (fun x : SpatialCoordinates d => Set.indicator (Metric.ball x rad) u y)
        =ᶠ[nhds x₀] (fun _ => u y) := by
      filter_upwards [(Metric.isOpen_ball).mem_nhds hmem] with x hx
      have hy : y ∈ Metric.ball x rad := by
        rw [Metric.mem_ball, dist_comm]; rwa [Metric.mem_ball] at hx
      exact Set.indicator_of_mem hy u
    exact continuousAt_const.congr heq.symm
  · have hopen : IsOpen {x : SpatialCoordinates d | rad < dist x y} :=
      isOpen_lt continuous_const (continuous_id.dist continuous_const)
    have heq : (fun x : SpatialCoordinates d => Set.indicator (Metric.ball x rad) u y)
        =ᶠ[nhds x₀] (fun _ => (0 : ℝ)) := by
      filter_upwards [hopen.mem_nhds h] with x hx
      have hy : y ∉ Metric.ball x rad := by
        rw [Metric.mem_ball, not_lt, dist_comm]; exact hx.le
      exact Set.indicator_of_notMem hy u
    exact continuousAt_const.congr heq.symm

/-- For fixed radius `rad > 0`, `x ↦ ∫ t in Metric.ball x rad ∩ Q, u t` is continuous on all of
`SpatialCoordinates d`, for any `u` integrable on `Q` — by dominated convergence: the integrand's
dependence on `x` is only through the ball's indicator, which converges pointwise (in fact is
locally constant) off the null sphere `{t | dist x₀ t = rad}`, and is dominated by `‖u‖`. -/
theorem aux_campanato_ball_integral_continuous
    (Q : Set (SpatialCoordinates d)) {rad : ℝ} (hrad : 0 < rad)
    {u : SpatialCoordinates d → ℝ} (hu : IntegrableOn u Q) :
    Continuous (fun x : SpatialCoordinates d => ∫ t in Metric.ball x rad ∩ Q, u t) := by
  have hEq : ∀ x : SpatialCoordinates d,
      ∫ t in Metric.ball x rad ∩ Q, u t = ∫ t in Q, Set.indicator (Metric.ball x rad) u t := by
    intro x
    rw [setIntegral_indicator Metric.isOpen_ball.measurableSet, Set.inter_comm]
  simp_rw [hEq]
  rw [continuous_iff_continuousAt]
  intro x₀
  have hsphere : volume (Metric.sphere x₀ rad) = 0 :=
    MeasureTheory.Measure.addHaar_sphere_of_ne_zero volume x₀ hrad.ne'
  have hae0 : ∀ᵐ t ∂volume, dist x₀ t ≠ rad := by
    rw [ae_iff]
    have hset : {t : SpatialCoordinates d | ¬ dist x₀ t ≠ rad} = Metric.sphere x₀ rad := by
      ext t; simp only [Set.mem_setOf_eq, not_not, Metric.mem_sphere, dist_comm x₀ t]
    rw [hset]; exact hsphere
  have hae : ∀ᵐ t ∂(volume.restrict Q), dist x₀ t ≠ rad :=
    MeasureTheory.ae_restrict_of_ae hae0
  exact MeasureTheory.continuousAt_of_dominated
    (Filter.Eventually.of_forall fun x =>
      hu.aestronglyMeasurable.indicator Metric.isOpen_ball.measurableSet)
    (Filter.Eventually.of_forall fun x =>
      Filter.Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, ← Real.norm_eq_abs]
        exact norm_indicator_le_norm_self u t)
    hu.norm
    (hae.mono fun t ht => aux_campanato_indicator_ball_continuousAt u t ht)

/-- For fixed radius `0 < rad` with `2 * rad ≤ r`, the boundary-clipped moving-ball Campanato
average `x ↦ ⨍_{B(x,rad) ∩ Q} u` (with `Q := centeredCube z r hr`) is continuous on the CLOSED
cube `closedCube z r hr` — including its topological boundary — for any `u` integrable on `Q`.
The denominator is bounded away from `0` on `closedCube z r hr` by
`aux_campanato_cube_inter_volume_ge_closed`, so the quotient of the two dominated-convergence
continuity facts above is continuous there. -/
theorem aux_campanato_ball_avg_continuous
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    {rad : ℝ} (hrad : 0 < rad) (hradr : 2 * rad ≤ r)
    {u : SpatialCoordinates d → ℝ}
    (hu : IntegrableOn u (centeredCube z r hr : Set (SpatialCoordinates d))) :
    ContinuousOn
      (fun x : SpatialCoordinates d =>
        (volume.real (Metric.ball x rad ∩
            (centeredCube z r hr : Set (SpatialCoordinates d))))⁻¹ *
          ∫ t in Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)), u t)
      (closedCube z r hr : Set (SpatialCoordinates d)) := by
  have hnum : Continuous (fun x : SpatialCoordinates d =>
      ∫ t in Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)), u t) :=
    aux_campanato_ball_integral_continuous _ hrad hu
  have hQfin : volume (centeredCube z r hr : Set (SpatialCoordinates d)) ≠ ⊤ := by
    rw [centeredCube_volume]; exact ENNReal.ofReal_ne_top
  have hden : Continuous (fun x : SpatialCoordinates d =>
      volume.real (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))) := by
    have hconst := aux_campanato_ball_integral_continuous
      (Q := (centeredCube z r hr : Set (SpatialCoordinates d))) hrad
      (u := fun _ => (1 : ℝ)) (integrableOn_const hQfin)
    simpa [setIntegral_const] using hconst
  have hpos : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      0 < volume.real (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    intro x hx
    have hs' : (0 : ℝ) < 2 * rad := by linarith
    have hvol := aux_campanato_cube_inter_volume_ge_closed z x hr hs' hradr hx
    have hcube : (centeredCube x (2 * rad) hs' : Set (SpatialCoordinates d)) =
        Metric.ball x rad := by
      show Metric.ball x (2 * rad / 2) = Metric.ball x rad
      norm_num
    rw [hcube] at hvol
    have hpospow : (0 : ℝ) < (2 * rad / 2) ^ d := by positivity
    linarith
  have hne : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      volume.real (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) ≠ 0 :=
    fun x hx => (hpos x hx).ne'
  exact (hden.continuousOn.inv₀ hne).mul hnum.continuousOn

/-- Two concentric boundary-clipped balls around the same `x ∈ closedCube z r hr` (allowing `x`
on the topological boundary), with `rad' ≤ rad` and `2*rad ≤ r` (so both fit inside the
boundary-clipped-volume lemma), have volume ratio bounded by the FIXED dimensional constant
`(2*rad/rad')^d` — independent of `x`'s position, even arbitrarily close to (or on) `z`'s cube
boundary. -/
theorem aux_campanato_window_ratio_le (z x : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hx : x ∈ (closedCube z r hr : Set (SpatialCoordinates d)))
    {rad rad' : ℝ} (hrad : 0 < rad) (hrad' : 0 < rad') (hradrad' : rad' ≤ rad)
    (hradr : 2 * rad ≤ r) :
    volume.real (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) ≤
      (2 * rad / rad') ^ d *
        volume.real (Metric.ball x rad' ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  have hcube : (centeredCube x (2 * rad) (by positivity) : Set (SpatialCoordinates d)) =
      Metric.ball x rad := by
    show Metric.ball x (2 * rad / 2) = Metric.ball x rad; norm_num
  have hUp : volume.real (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
      ≤ (2 * rad) ^ d := by
    calc volume.real (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
        ≤ volume.real (Metric.ball x rad) :=
          measureReal_mono Set.inter_subset_left
            (by rw [← hcube, centeredCube_volume]; exact ENNReal.ofReal_ne_top)
      _ = (2 * rad) ^ d := by rw [← hcube, centeredCube_volume_real]
  have hs' : (0 : ℝ) < 2 * rad' := by positivity
  have hsr' : 2 * rad' ≤ r := by linarith
  have hvol' := aux_campanato_cube_inter_volume_ge_closed z x hr hs' hsr' hx
  have hcube' : (centeredCube x (2 * rad') hs' : Set (SpatialCoordinates d)) =
      Metric.ball x rad' := by
    show Metric.ball x (2 * rad' / 2) = Metric.ball x rad'; norm_num
  rw [hcube'] at hvol'
  have hrewrite : (2 * rad' / 2 : ℝ) = rad' := by ring
  rw [hrewrite] at hvol'
  have hLow : (rad') ^ d ≤
      volume.real (Metric.ball x rad' ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    hvol'
  have hratiopos : (0:ℝ) < (2 * rad / rad') ^ d := by positivity
  have hkey : (2 * rad) ^ d ≤ (2 * rad / rad') ^ d * (rad') ^ d := by
    rw [div_pow, div_mul_cancel₀]
    positivity
  calc volume.real (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
      ≤ (2 * rad) ^ d := hUp
    _ ≤ (2 * rad / rad') ^ d * (rad') ^ d := hkey
    _ ≤ (2 * rad / rad') ^ d *
          volume.real (Metric.ball x rad' ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) :=
        mul_le_mul_of_nonneg_left hLow hratiopos.le

/-- Telescoping step between two concentric boundary-clipped Campanato windows: the averages
move by at most `sqrt((2*rad/rad')^d)` times the coarser window's own normalized `L²`
oscillation — combines GMC's window-comparison inequality
(`abs_volumeAverage_sub_windowAverage_le`) with the volume-ratio bound above. -/
theorem aux_campanato_ball_avg_telescope (z x : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hx : x ∈ (closedCube z r hr : Set (SpatialCoordinates d)))
    {rad rad' : ℝ} (hrad : 0 < rad) (hrad' : 0 < rad') (hradrad' : rad' ≤ rad)
    (hradr : 2 * rad ≤ r)
    {u : SpatialCoordinates d → ℝ}
    (hfV : IntegrableOn u (Metric.ball x rad' ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
      volume)
    (hfV2 : IntegrableOn
      (fun y => (u y - Homogenization.volumeAverage
          (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) u) ^ 2)
      (Metric.ball x rad' ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) volume)
    (hfW2 : IntegrableOn
      (fun y => (u y - Homogenization.volumeAverage
          (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) u) ^ 2)
      (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) volume) :
    |Homogenization.volumeAverage
          (Metric.ball x rad' ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) u -
        Homogenization.volumeAverage
          (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) u| ≤
      Real.sqrt ((2 * rad / rad') ^ d) *
        SubdiffusiveProcess.CoarseGrainingVocab.normalizedL2On
          (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (fun y => u y - Homogenization.volumeAverage
            (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) u) := by
  set W := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)) with hWdef
  set V := Metric.ball x rad' ∩ (centeredCube z r hr : Set (SpatialCoordinates d)) with hVdef
  have hVsub : V ⊆ W := by
    apply Set.inter_subset_inter_left
    exact Metric.ball_subset_ball hradrad'
  have hVm : MeasurableSet V :=
    (Metric.isOpen_ball).measurableSet.inter (centeredCube z r hr).2.measurableSet
  have hWpos : 0 < (volume W).toReal := by
    have hs' : (0 : ℝ) < 2 * rad := by positivity
    have hvol := aux_campanato_cube_inter_volume_ge_closed z x hr hs' hradr hx
    have hcube : (centeredCube x (2 * rad) hs' : Set (SpatialCoordinates d)) =
        Metric.ball x rad := by show Metric.ball x (2 * rad / 2) = Metric.ball x rad; norm_num
    rw [hcube] at hvol
    have hpospow : (0 : ℝ) < (2 * rad / 2) ^ d := by positivity
    have : (0:ℝ) < volume.real W := by rw [hWdef]; linarith
    rwa [measureReal_def] at this
  have hVpos : 0 < (volume V).toReal := by
    have hs' : (0 : ℝ) < 2 * rad' := by positivity
    have hsr' : 2 * rad' ≤ r := by linarith
    have hvol := aux_campanato_cube_inter_volume_ge_closed z x hr hs' hsr' hx
    have hcube : (centeredCube x (2 * rad') hs' : Set (SpatialCoordinates d)) =
        Metric.ball x rad' := by show Metric.ball x (2 * rad' / 2) = Metric.ball x rad'; norm_num
    rw [hcube] at hvol
    have hpospow : (0 : ℝ) < (2 * rad' / 2) ^ d := by positivity
    have : (0:ℝ) < volume.real V := by rw [hVdef]; linarith
    rwa [measureReal_def] at this
  have hVtop : volume V ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono (hVdef ▸ Set.inter_subset_right)) ?_)
    rw [centeredCube_volume]; exact ENNReal.ofReal_lt_top
  have hmain := SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.abs_volumeAverage_sub_windowAverage_le
    hVm hVsub hWpos hVpos hVtop hfV hfV2 hfW2
  have hratio : volume.real W ≤ (2 * rad / rad') ^ d * volume.real V := by
    rw [hWdef, hVdef]
    exact aux_campanato_window_ratio_le z x hr hx hrad hrad' hradrad' hradr
  have hVposR : 0 < volume.real V := by rwa [measureReal_def]
  have hsqrt_le : Real.sqrt ((volume W).toReal / (volume V).toReal) ≤
      Real.sqrt ((2 * rad / rad') ^ d) := by
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by rwa [measureReal_def] at hVposR)]
    rw [← measureReal_def, ← measureReal_def]
    linarith [hratio]
  calc |Homogenization.volumeAverage V u - Homogenization.volumeAverage W u|
      ≤ Real.sqrt ((volume W).toReal / (volume V).toReal) *
          SubdiffusiveProcess.CoarseGrainingVocab.normalizedL2On W (fun y => u y - Homogenization.volumeAverage W u) :=
        hmain
    _ ≤ Real.sqrt ((2 * rad / rad') ^ d) *
          SubdiffusiveProcess.CoarseGrainingVocab.normalizedL2On W (fun y => u y - Homogenization.volumeAverage W u) :=
        mul_le_mul_of_nonneg_right hsqrt_le
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.normalizedL2On_nonneg _ _)

/-- The `D`-th dyadic Campanato window around `x`, inside `Q := centeredCube qcenter qside hqpos`.
Matches `aux_in_deterministic_regularity_campanato_holder`'s own `hcamp` window shape exactly
(`Metric.ball x (qside * 3^(-D) / 2) ∩ Q`), so the eventual continuous representative can feed
straight back into it. -/
def campanatoWindow (qcenter : SpatialCoordinates d) {qside : ℝ} (hqpos : 0 < qside)
    (x : SpatialCoordinates d) (D : ℕ) : Set (SpatialCoordinates d) :=
  Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2) ∩
    (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))

/-- The `D`-th dyadic Campanato average of `u` around `x`. -/
def campanatoAvg (qcenter : SpatialCoordinates d) {qside : ℝ} (hqpos : 0 < qside)
    (u : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d) (D : ℕ) : ℝ :=
  Homogenization.volumeAverage (campanatoWindow qcenter hqpos x D) u

theorem campanatoAvg_eq (qcenter : SpatialCoordinates d) {qside : ℝ} (hqpos : 0 < qside)
    (u : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d) (D : ℕ) :
    campanatoAvg qcenter hqpos u x D =
      (volume.real (campanatoWindow qcenter hqpos x D))⁻¹ *
        ∫ t in campanatoWindow qcenter hqpos x D, u t := rfl

theorem campanatoWindow_rad_pos (_qcenter : SpatialCoordinates d) {qside : ℝ} (hqpos : 0 < qside)
    (D : ℕ) : (0:ℝ) < qside * (3:ℝ) ^ (-(D:ℤ)) / 2 := by positivity

theorem campanatoWindow_two_rad_le (_qcenter : SpatialCoordinates d) {qside : ℝ} (hqpos : 0 < qside)
    (D : ℕ) : 2 * (qside * (3:ℝ) ^ (-(D:ℤ)) / 2) ≤ qside := by
  have h3 : (1:ℝ) ≤ (3:ℝ) ^ D := one_le_pow₀ (by norm_num)
  have hz : (3:ℝ) ^ (-(D:ℤ)) = ((3:ℝ) ^ D)⁻¹ := by rw [zpow_neg, zpow_natCast]
  rw [hz]
  have hinv : ((3:ℝ)^D)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h3
  nlinarith [hqpos.le]

theorem campanatoWindow_succ_ratio (_qcenter : SpatialCoordinates d) {qside : ℝ} (hqpos : 0 < qside)
    (D : ℕ) :
    2 * (qside * (3:ℝ) ^ (-(D:ℤ)) / 2) / (qside * (3:ℝ) ^ (-((D:ℤ)+1)) / 2) = 6 := by
  have h3D : (3:ℝ)^D ≠ 0 := by positivity
  have hz1 : (3:ℝ) ^ (-(D:ℤ)) = ((3:ℝ) ^ D)⁻¹ := by rw [zpow_neg, zpow_natCast]
  have hz2 : (3:ℝ) ^ (-((D:ℤ)+1)) = ((3:ℝ) ^ D)⁻¹ / 3 := by
    rw [show -((D:ℤ)+1) = -(D:ℤ) + (-1) by ring, zpow_add₀ (by norm_num : (3:ℝ) ≠ 0),
      zpow_neg, zpow_natCast, zpow_neg_one]
    ring
  rw [hz1, hz2]
  field_simp
  ring

theorem campanatoWindow_succ_le (_qcenter : SpatialCoordinates d) {qside : ℝ} (hqpos : 0 < qside)
    (D : ℕ) :
    qside * (3:ℝ) ^ (-((D:ℤ)+1)) / 2 ≤ qside * (3:ℝ) ^ (-(D:ℤ)) / 2 := by
  have hz1 : (3:ℝ) ^ (-(D:ℤ)) = ((3:ℝ) ^ D)⁻¹ := by rw [zpow_neg, zpow_natCast]
  have hz2 : (3:ℝ) ^ (-((D:ℤ)+1)) = ((3:ℝ) ^ D)⁻¹ / 3 := by
    rw [show -((D:ℤ)+1) = -(D:ℤ) + (-1) by ring, zpow_add₀ (by norm_num : (3:ℝ) ≠ 0),
      zpow_neg, zpow_natCast, zpow_neg_one]
    ring
  rw [hz1, hz2]
  have h3D : (0:ℝ) < ((3:ℝ)^D)⁻¹ := by positivity
  nlinarith [hqpos.le]

theorem campanatoWindow_subset (qcenter : SpatialCoordinates d) {qside : ℝ} (hqpos : 0 < qside)
    (x : SpatialCoordinates d) (D : ℕ) :
    campanatoWindow qcenter hqpos x D ⊆ (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) :=
  Set.inter_subset_right

/-- From global `L¹`/`L²` membership of `u` on `Q`, the squared deviation from any constant is
integrable on any subset of `Q` — the integrability side-condition `abs_volumeAverage_sub_
windowAverage_le`/`aux_campanato_ball_avg_telescope` need, discharged once here for reuse. -/
theorem campanato_integrableOn_sq_sub_const (qcenter : SpatialCoordinates d) {qside : ℝ}
    (hqpos : 0 < qside) {u : SpatialCoordinates d → ℝ}
    (hu1 : IntegrableOn u (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) volume)
    (hu2 : IntegrableOn (fun y => u y ^ 2)
      (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) volume)
    {S : Set (SpatialCoordinates d)}
    (hS : S ⊆ (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))) (c : ℝ) :
    IntegrableOn (fun y => (u y - c) ^ 2) S volume := by
  have h1 : IntegrableOn u S volume := hu1.mono_set hS
  have h2 : IntegrableOn (fun y => u y ^ 2) S volume := hu2.mono_set hS
  have heq : (fun y => (u y - c) ^ 2) = (fun y => u y ^ 2 - 2 * c * u y + c ^ 2) := by
    funext y; ring
  rw [heq]
  have hfin : volume S ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono (hS.trans (fun y hy => hy))) ?_)
    rw [centeredCube_volume]; exact ENNReal.ofReal_lt_top
  exact (h2.sub (h1.const_mul (2 * c))).add (integrableOn_const hfin)

/-- The per-step move of the dyadic Campanato averages, factored out for reuse by both the
Cauchy-sequence proof and the tail-bound-to-the-limit proof below. -/
theorem aux_campanato_ball_avg_step_bound
    (qcenter : SpatialCoordinates d) {qside : ℝ} (hqpos : 0 < qside)
    {alpha : ℝ} {K : ℝ}
    {u : SpatialCoordinates d → ℝ}
    (hu1 : IntegrableOn u (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) volume)
    (hu2 : IntegrableOn (fun y => u y ^ 2)
      (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) volume)
    (hcamp : ∀ (D : ℕ), ∀ x ∈ (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)),
      SubdiffusiveProcess.CoarseGrainingVocab.normalizedL2On (campanatoWindow qcenter hqpos x D)
        (fun y => u y - campanatoAvg qcenter hqpos u x D) ≤ K * ((3 : ℝ) ^ (-alpha)) ^ D)
    (x : SpatialCoordinates d)
    (hx : x ∈ (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))) (D : ℕ) :
    dist (campanatoAvg qcenter hqpos u x D) (campanatoAvg qcenter hqpos u x (D+1)) ≤
      Real.sqrt ((6:ℝ) ^ d) * K * ((3 : ℝ) ^ (-alpha)) ^ D := by
  have hradpos : 0 < qside * (3:ℝ) ^ (-(D:ℤ)) / 2 := campanatoWindow_rad_pos qcenter hqpos D
  have hrad'pos : 0 < qside * (3:ℝ) ^ (-((D:ℤ)+1)) / 2 := campanatoWindow_rad_pos qcenter hqpos (D+1)
  have hle : qside * (3:ℝ) ^ (-((D:ℤ)+1)) / 2 ≤ qside * (3:ℝ) ^ (-(D:ℤ)) / 2 :=
    campanatoWindow_succ_le qcenter hqpos D
  have hradr : 2 * (qside * (3:ℝ) ^ (-(D:ℤ)) / 2) ≤ qside := campanatoWindow_two_rad_le qcenter hqpos D
  have hratio : (2 * (qside * (3:ℝ) ^ (-(D:ℤ)) / 2)) / (qside * (3:ℝ) ^ (-((D:ℤ)+1)) / 2) = 6 :=
    campanatoWindow_succ_ratio qcenter hqpos D
  have hSVsub : campanatoWindow qcenter hqpos x (D+1) ⊆
      (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) :=
    campanatoWindow_subset qcenter hqpos x (D+1)
  have hfV : IntegrableOn u (campanatoWindow qcenter hqpos x (D+1)) volume := hu1.mono_set hSVsub
  have hfV2 : IntegrableOn (fun y => (u y - campanatoAvg qcenter hqpos u x D) ^ 2)
      (campanatoWindow qcenter hqpos x (D+1)) volume :=
    campanato_integrableOn_sq_sub_const qcenter hqpos hu1 hu2 hSVsub _
  have hfW2 : IntegrableOn (fun y => (u y - campanatoAvg qcenter hqpos u x D) ^ 2)
      (campanatoWindow qcenter hqpos x D) volume :=
    campanato_integrableOn_sq_sub_const qcenter hqpos hu1 hu2
      (campanatoWindow_subset qcenter hqpos x D) _
  have htel := aux_campanato_ball_avg_telescope qcenter x hqpos
    (centeredCube_subset_closedCube qcenter hqpos hx) hradpos hrad'pos hle hradr
    (u := u) hfV hfV2 hfW2
  rw [hratio] at htel
  have hcampD := hcamp D x hx
  have hsqrt_nonneg : (0:ℝ) ≤ Real.sqrt ((6:ℝ)^d) := Real.sqrt_nonneg _
  have hfinal : |campanatoAvg qcenter hqpos u x (D+1) - campanatoAvg qcenter hqpos u x D| ≤
      Real.sqrt ((6:ℝ)^d) * K * ((3:ℝ)^(-alpha))^D := by
    calc |campanatoAvg qcenter hqpos u x (D+1) - campanatoAvg qcenter hqpos u x D|
        ≤ Real.sqrt ((6:ℝ)^d) *
            SubdiffusiveProcess.CoarseGrainingVocab.normalizedL2On (campanatoWindow qcenter hqpos x D)
              (fun y => u y - campanatoAvg qcenter hqpos u x D) := htel
      _ ≤ Real.sqrt ((6:ℝ)^d) * (K * ((3:ℝ)^(-alpha))^D) :=
          mul_le_mul_of_nonneg_left hcampD hsqrt_nonneg
      _ = Real.sqrt ((6:ℝ)^d) * K * ((3:ℝ)^(-alpha))^D := by ring
  rw [Real.dist_eq, abs_sub_comm]
  exact hfinal

/-- `centeredCube`'s closure is exactly `closedCube` (same center/side), since both are
literally the open/closed sup-ball. -/
theorem campanato_closure_centeredCube_eq_closedCube (qcenter : SpatialCoordinates d)
    {qside : ℝ} (hqpos : 0 < qside) :
    closure (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) =
      (closedCube qcenter qside hqpos : Set (SpatialCoordinates d)) :=
  closure_ball qcenter (by positivity : (qside / 2 : ℝ) ≠ 0)

/-- The per-step move bound extends from the open cube (where `hcamp` lives,
`aux_campanato_ball_avg_step_bound`) to the CLOSED cube — no restatement of `hcamp` at boundary
points is needed: for fixed `D`, `x ↦ dist (campanatoAvg x D) (campanatoAvg x (D+1))` is
continuous on `closedCube` (from `aux_campanato_ball_avg_continuous`, which needs no `hcamp`),
`Q` is dense in `closedCube` (`campanato_closure_centeredCube_eq_closedCube`), and `f ≤ c` is a
closed condition, so it propagates from the dense open cube to its closure (`le_on_closure`). -/
theorem aux_campanato_ball_avg_step_bound_closed
    (qcenter : SpatialCoordinates d) {qside : ℝ} (hqpos : 0 < qside)
    {alpha : ℝ} {K : ℝ}
    {u : SpatialCoordinates d → ℝ}
    (hu1 : IntegrableOn u (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) volume)
    (hu2 : IntegrableOn (fun y => u y ^ 2)
      (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) volume)
    (hcamp : ∀ (D : ℕ), ∀ x ∈ (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)),
      SubdiffusiveProcess.CoarseGrainingVocab.normalizedL2On (campanatoWindow qcenter hqpos x D)
        (fun y => u y - campanatoAvg qcenter hqpos u x D) ≤ K * ((3 : ℝ) ^ (-alpha)) ^ D)
    (x : SpatialCoordinates d)
    (hx : x ∈ (closedCube qcenter qside hqpos : Set (SpatialCoordinates d))) (D : ℕ) :
    dist (campanatoAvg qcenter hqpos u x D) (campanatoAvg qcenter hqpos u x (D+1)) ≤
      Real.sqrt ((6:ℝ) ^ d) * K * ((3 : ℝ) ^ (-alpha)) ^ D := by
  have hradr : 2 * (qside * (3:ℝ) ^ (-(D:ℤ)) / 2) ≤ qside := campanatoWindow_two_rad_le qcenter hqpos D
  have hradr' : 2 * (qside * (3:ℝ) ^ (-((D:ℤ)+1)) / 2) ≤ qside :=
    campanatoWindow_two_rad_le qcenter hqpos (D+1)
  have hcD : ContinuousOn (fun y => campanatoAvg qcenter hqpos u y D)
      (closedCube qcenter qside hqpos : Set (SpatialCoordinates d)) := by
    have hc := aux_campanato_ball_avg_continuous qcenter (r := qside) hqpos
      (rad := qside * (3:ℝ) ^ (-(D:ℤ)) / 2) (campanatoWindow_rad_pos qcenter hqpos D) hradr hu1
    simpa [campanatoAvg, campanatoWindow] using hc
  have hcD1 : ContinuousOn (fun y => campanatoAvg qcenter hqpos u y (D+1))
      (closedCube qcenter qside hqpos : Set (SpatialCoordinates d)) := by
    have hc := aux_campanato_ball_avg_continuous qcenter (r := qside) hqpos
      (rad := qside * (3:ℝ) ^ (-((D:ℤ)+1)) / 2) (campanatoWindow_rad_pos qcenter hqpos (D+1)) hradr' hu1
    simpa [campanatoAvg, campanatoWindow] using hc
  have hf : ContinuousOn
      (fun y => dist (campanatoAvg qcenter hqpos u y D) (campanatoAvg qcenter hqpos u y (D+1)))
      (closedCube qcenter qside hqpos : Set (SpatialCoordinates d)) :=
    continuous_dist.comp_continuousOn (hcD.prodMk hcD1)
  have hg : ContinuousOn (fun _ : SpatialCoordinates d => Real.sqrt ((6:ℝ) ^ d) * K * ((3 : ℝ) ^ (-alpha)) ^ D)
      (closedCube qcenter qside hqpos : Set (SpatialCoordinates d)) := continuousOn_const
  have hdense : (closedCube qcenter qside hqpos : Set (SpatialCoordinates d)) =
      closure (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) :=
    (campanato_closure_centeredCube_eq_closedCube qcenter hqpos).symm
  rw [hdense] at hf hg
  have hx' : x ∈ closure (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) := by
    rwa [hdense] at hx
  exact le_on_closure (fun y hy => aux_campanato_ball_avg_step_bound qcenter hqpos hu1 hu2 hcamp y hy D)
    hf hg hx'

/-- The dyadic Campanato averages of `u` around a fixed `x ∈ closedCube` form a Cauchy sequence
in `D`, given `hcamp`'s geometric oscillation decay (exponent `alpha ∈ (0,1)`, holding on the
open cube) and global `L¹`/`L²` membership of `u` on the open cube — valid at every `x` in the
CLOSED cube, boundary included, via `aux_campanato_ball_avg_step_bound_closed`. -/
theorem aux_campanato_ball_avg_cauchy
    (qcenter : SpatialCoordinates d) {qside : ℝ} (hqpos : 0 < qside)
    {alpha : ℝ} (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1) {K : ℝ} (hK : 0 ≤ K)
    {u : SpatialCoordinates d → ℝ}
    (hu1 : IntegrableOn u (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) volume)
    (hu2 : IntegrableOn (fun y => u y ^ 2)
      (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) volume)
    (hcamp : ∀ (D : ℕ), ∀ x ∈ (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)),
      SubdiffusiveProcess.CoarseGrainingVocab.normalizedL2On (campanatoWindow qcenter hqpos x D)
        (fun y => u y - campanatoAvg qcenter hqpos u x D) ≤ K * ((3 : ℝ) ^ (-alpha)) ^ D)
    (x : SpatialCoordinates d)
    (hx : x ∈ (closedCube qcenter qside hqpos : Set (SpatialCoordinates d))) :
    CauchySeq (campanatoAvg qcenter hqpos u x) := by
  have hr : (3 : ℝ) ^ (-alpha) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [halpha.1])
  apply cauchySeq_of_le_geometric ((3 : ℝ) ^ (-alpha)) (Real.sqrt ((6:ℝ) ^ d) * K) hr
  intro D
  exact aux_campanato_ball_avg_step_bound_closed qcenter hqpos hu1 hu2 hcamp x hx D

/-- The dyadic Campanato averages converge, uniformly in `x ∈ closedCube` (the CLOSED cube,
boundary included), to a continuous limit `U`. `U` is not yet identified with `u` almost
everywhere here — see the file docstring for the remaining piece. -/
theorem aux_campanato_continuous_limit_exists
    (qcenter : SpatialCoordinates d) {qside : ℝ} (hqpos : 0 < qside)
    {alpha : ℝ} (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1) {K : ℝ} (hK : 0 ≤ K)
    {u : SpatialCoordinates d → ℝ}
    (hu1 : IntegrableOn u (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) volume)
    (hu2 : IntegrableOn (fun y => u y ^ 2)
      (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) volume)
    (hcamp : ∀ (D : ℕ), ∀ x ∈ (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)),
      SubdiffusiveProcess.CoarseGrainingVocab.normalizedL2On (campanatoWindow qcenter hqpos x D)
        (fun y => u y - campanatoAvg qcenter hqpos u x D) ≤ K * ((3 : ℝ) ^ (-alpha)) ^ D) :
    ∃ U : SpatialCoordinates d → ℝ,
      ContinuousOn U (closedCube qcenter qside hqpos : Set (SpatialCoordinates d)) ∧
      ∀ x ∈ (closedCube qcenter qside hqpos : Set (SpatialCoordinates d)),
        Tendsto (campanatoAvg qcenter hqpos u x) atTop (𝓝 (U x)) := by
  have hr : (3 : ℝ) ^ (-alpha) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [halpha.1])
  have hexists : ∀ x ∈ (closedCube qcenter qside hqpos : Set (SpatialCoordinates d)),
      ∃ L : ℝ, Tendsto (campanatoAvg qcenter hqpos u x) atTop (𝓝 L) := fun x hx =>
    cauchySeq_tendsto_of_complete (aux_campanato_ball_avg_cauchy qcenter hqpos halpha hK hu1 hu2 hcamp x hx)
  choose! U hU using hexists
  have hbound : ∀ D : ℕ, ∀ x ∈ (closedCube qcenter qside hqpos : Set (SpatialCoordinates d)),
      dist (campanatoAvg qcenter hqpos u x D) (U x) ≤
        Real.sqrt ((6:ℝ) ^ d) * K * ((3 : ℝ) ^ (-alpha)) ^ D / (1 - (3 : ℝ) ^ (-alpha)) := by
    intro D x hx
    exact dist_le_of_le_geometric_of_tendsto ((3 : ℝ) ^ (-alpha)) (Real.sqrt ((6:ℝ) ^ d) * K) hr
      (aux_campanato_ball_avg_step_bound_closed qcenter hqpos hu1 hu2 hcamp x hx) (hU x hx) D
  have hunif : TendstoUniformlyOn (fun D x => campanatoAvg qcenter hqpos u x D) U atTop
      (closedCube qcenter qside hqpos : Set (SpatialCoordinates d)) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have h1sub : (0:ℝ) < 1 - (3:ℝ)^(-alpha) := by linarith
    have htend : Tendsto (fun D : ℕ => Real.sqrt ((6:ℝ) ^ d) * K * ((3 : ℝ) ^ (-alpha)) ^ D /
        (1 - (3 : ℝ) ^ (-alpha))) atTop (𝓝 0) := by
      have h0 : Tendsto (fun D : ℕ => ((3 : ℝ) ^ (-alpha)) ^ D) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (Real.rpow_nonneg (by norm_num) _) hr
      have := (h0.const_mul (Real.sqrt ((6:ℝ) ^ d) * K)).div_const (1 - (3:ℝ)^(-alpha))
      simpa using this
    have hev := htend.eventually (gt_mem_nhds hε)
    filter_upwards [hev] with D hD x hx
    calc dist (U x) (campanatoAvg qcenter hqpos u x D)
        = dist (campanatoAvg qcenter hqpos u x D) (U x) := dist_comm _ _
      _ ≤ Real.sqrt ((6:ℝ) ^ d) * K * ((3 : ℝ) ^ (-alpha)) ^ D / (1 - (3 : ℝ) ^ (-alpha)) :=
          hbound D x hx
      _ < ε := hD
  refine ⟨U, ?_, hU⟩
  apply hunif.continuousOn
  refine Filter.Eventually.frequently (Filter.Eventually.of_forall fun D => ?_)
  have hradr : 2 * (qside * (3:ℝ) ^ (-(D:ℤ)) / 2) ≤ qside := campanatoWindow_two_rad_le qcenter hqpos D
  have hc := aux_campanato_ball_avg_continuous qcenter (r := qside) hqpos
    (rad := qside * (3:ℝ) ^ (-(D:ℤ)) / 2) (campanatoWindow_rad_pos qcenter hqpos D) hradr hu1
  simpa [campanatoAvg, campanatoWindow] using hc

/-- Open and closed sup-balls of the same center/radius agree almost everywhere: their
symmetric difference is the sphere, which is Lebesgue-null. -/
theorem campanato_ball_ae_eq_closedBall (x : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    Metric.ball x r =ᵐ[volume] Metric.closedBall x r := by
  rw [MeasureTheory.ae_eq_set]
  refine ⟨?_, ?_⟩
  · simp [Set.diff_eq_empty.mpr Metric.ball_subset_closedBall]
  · rw [Metric.closedBall_diff_ball]
    exact MeasureTheory.Measure.addHaar_sphere_of_ne_zero volume x hr.ne'

/-- The (raw, un-normalized) window average over an open ball equals the `⨍`-average over the
corresponding closed ball, since the two balls agree almost everywhere. -/
theorem campanato_volumeAverage_ball_eq_setAverage_closedBall (x : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (f : SpatialCoordinates d → ℝ) :
    Homogenization.volumeAverage (Metric.ball x r) f =
      ⨍ y in Metric.closedBall x r, f y ∂volume := by
  have hae := campanato_ball_ae_eq_closedBall x hr
  rw [Homogenization.volumeAverage, setAverage_eq, smul_eq_mul, ← measureReal_def,
    measureReal_congr hae, setIntegral_congr_set hae]

/-- The dyadic Campanato radius sequence tends to `0` from above. -/
theorem campanatoRad_tendsto_zero (qside : ℝ) (hqpos : 0 < qside) :
    Tendsto (fun D : ℕ => qside * (3 : ℝ) ^ (-(D : ℤ)) / 2) atTop (𝓝[>] (0 : ℝ)) := by
  have hz : ∀ D : ℕ, qside * (3:ℝ) ^ (-(D:ℤ)) / 2 = qside / 2 * (1/3 : ℝ) ^ D := by
    intro D
    rw [zpow_neg, zpow_natCast, div_pow, one_pow]
    ring
  simp_rw [hz]
  have hfull : Tendsto (fun D : ℕ => qside / 2 * (1/3 : ℝ) ^ D) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds (x := qside/2)).mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/3) (by norm_num))
  exact tendsto_inf.2 ⟨hfull,
    tendsto_principal.2 (Eventually.of_forall fun D => Set.mem_Ioi.mpr (by positivity))⟩

/-- Lebesgue differentiation for the indicator of `u` on `Q`: for a.e. `x`, closed-ball averages
of `indicator Q u` tend to `indicator Q u x` as the radius shrinks to `0`. -/
theorem ae_tendsto_setAverage_indicator (qcenter : SpatialCoordinates d) {qside : ℝ}
    (hqpos : 0 < qside) {u : SpatialCoordinates d → ℝ}
    (hu1 : IntegrableOn u (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) volume) :
    ∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)),
      Tendsto (fun r : ℝ => ⨍ y in Metric.closedBall x r,
          Set.indicator (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) u y ∂volume)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Set.indicator (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) u x)) := by
  have hInt : Integrable
      (Set.indicator (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) u) volume :=
    hu1.integrable_indicator (centeredCube qcenter qside hqpos).2.measurableSet
  filter_upwards [(Besicovitch.vitaliFamily (volume : Measure (SpatialCoordinates d))).ae_tendsto_average
      hInt.locallyIntegrable] with x hx
  exact hx.comp (Besicovitch.tendsto_filterAt (volume : Measure (SpatialCoordinates d)) x)



theorem campanato_avg_eq_indicator_avg_of_ball_subset (qcenter x : SpatialCoordinates d)
    {qside rad : ℝ} (hqpos : 0 < qside) (hrad : 0 < rad) {u : SpatialCoordinates d → ℝ}
    (hsub : Metric.ball x rad ⊆ (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))) :
    Homogenization.volumeAverage (Metric.ball x rad) u =
      ⨍ y in Metric.closedBall x rad,
        Set.indicator (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) u y ∂volume := by
  rw [campanato_volumeAverage_ball_eq_setAverage_closedBall x hrad u]
  apply setAverage_congr_fun measurableSet_closedBall
  have hnull : volume (Metric.closedBall x rad \ Metric.ball x rad) = 0 := by
    rw [Metric.closedBall_diff_ball]
    exact MeasureTheory.Measure.addHaar_sphere_of_ne_zero volume x hrad.ne'
  rw [ae_iff]
  have hsubset : {y : SpatialCoordinates d |
      ¬ (y ∈ Metric.closedBall x rad → u y =
        Set.indicator (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) u y)} ⊆
      Metric.closedBall x rad \ Metric.ball x rad := by
    intro y hy
    simp only [Set.mem_setOf_eq, not_forall] at hy
    obtain ⟨hyc, hyne⟩ := hy
    refine ⟨hyc, fun hyb => hyne ?_⟩
    exact (Set.indicator_of_mem (hsub hyb) u).symm
  exact measure_mono_null hsubset hnull

/-- **Main result**: the continuous Campanato representative. `U` (from
`aux_campanato_continuous_limit_exists`) is continuous on the CLOSED cube `closedCube` (boundary
included — this is what `aux_lem_finite_source_comparison_cells_holDir`/`aux_in_deterministic_
regularity_campanato_holder` actually need, not just the open cube) AND equals `u` almost
everywhere on `Q` — ready to feed directly into
`aux_in_deterministic_regularity_campanato_holder`. -/
theorem aux_campanato_continuous_representative
    (qcenter : SpatialCoordinates d) {qside : ℝ} (hqpos : 0 < qside)
    {alpha : ℝ} (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1) {K : ℝ} (hK : 0 ≤ K)
    {u : SpatialCoordinates d → ℝ}
    (hu1 : IntegrableOn u (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) volume)
    (hu2 : IntegrableOn (fun y => u y ^ 2)
      (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) volume)
    (hcamp : ∀ (D : ℕ), ∀ x ∈ (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)),
      SubdiffusiveProcess.CoarseGrainingVocab.normalizedL2On (campanatoWindow qcenter hqpos x D)
        (fun y => u y - campanatoAvg qcenter hqpos u x D) ≤ K * ((3 : ℝ) ^ (-alpha)) ^ D) :
    ∃ U : SpatialCoordinates d → ℝ,
      ContinuousOn U (closedCube qcenter qside hqpos : Set (SpatialCoordinates d)) ∧
      ∀ᵐ x ∂(volume.restrict (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))),
        U x = u x := by
  obtain ⟨U, hUcont, hUtendsto⟩ :=
    aux_campanato_continuous_limit_exists qcenter hqpos halpha hK hu1 hu2 hcamp
  refine ⟨U, hUcont, ?_⟩
  refine (ae_restrict_iff' (centeredCube qcenter qside hqpos).2.measurableSet).mpr ?_
  have hQopen : IsOpen (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) :=
    (centeredCube qcenter qside hqpos).2
  have hradTend := campanatoRad_tendsto_zero qside hqpos
  filter_upwards [ae_tendsto_setAverage_indicator qcenter hqpos hu1] with x hx
  intro hxQ
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hQopen x hxQ
  have hev : ∀ᶠ D : ℕ in atTop, qside * (3:ℝ)^(-(D:ℤ))/2 < ε :=
    (hradTend.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds hεpos)
  have hevBall : (campanatoAvg qcenter hqpos u x) =ᶠ[atTop]
      (fun D : ℕ => ⨍ y in Metric.closedBall x (qside * (3:ℝ)^(-(D:ℤ))/2),
          Set.indicator (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) u y ∂volume) := by
    filter_upwards [hev] with D hD
    have hballsub : Metric.ball x (qside * (3:ℝ)^(-(D:ℤ))/2) ⊆
        (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) :=
      (Metric.ball_subset_ball hD.le).trans hεsub
    have hwin : campanatoWindow qcenter hqpos x D = Metric.ball x (qside * (3:ℝ)^(-(D:ℤ))/2) := by
      rw [campanatoWindow, Set.inter_eq_left]
      exact hballsub
    rw [campanatoAvg, hwin]
    exact campanato_avg_eq_indicator_avg_of_ball_subset qcenter x hqpos
      (campanatoWindow_rad_pos qcenter hqpos D) hballsub
  have heq : (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)).indicator u x = u x :=
    Set.indicator_of_mem hxQ u
  have hLeb : Tendsto (campanatoAvg qcenter hqpos u x) atTop (𝓝 (u x)) := by
    have hcomp := hx.comp hradTend
    rw [heq] at hcomp
    exact hcomp.congr' hevBall.symm
  exact tendsto_nhds_unique (hUtendsto x (centeredCube_subset_closedCube qcenter hqpos hxQ)) hLeb

end SubdiffusiveProcess
