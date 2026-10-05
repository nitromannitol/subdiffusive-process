module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.CaccioppoliEndpointPrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.NonpositiveGeometry

@[expose] public section

/-!
# Ambient-oscillation readout of the nonpositive-scale Caccioppoli datum
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory Topology Homogenization SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

private theorem oscillationWindow_eq_closedBall (m : ℤ) (z : Vec d) :
    {y : Vec d | ‖y - z‖ ≤ 3 * (3 : ℝ) ^ m / 8} =
      Metric.closedBall z (3 * (3 : ℝ) ^ m / 8) := by
  ext y
  simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_eq_norm]

private theorem oscillationWindow_subset_translatedCube
    (m : ℤ) (z : Vec d) :
    {y : Vec d | ‖y - z‖ ≤ 3 * (3 : ℝ) ^ m / 8} ⊆
      translatedCube d m z := by
  rw [oscillationWindow_eq_closedBall, translatedCube_eq_metricBall]
  apply Metric.closedBall_subset_ball
  have hpow : 0 < (3 : ℝ) ^ m := by positivity
  nlinarith

private theorem bddAbove_oscillationValues_of_continuousOn_window
    {m : ℤ} {z : Vec d} {f : Vec d → ℝ}
    (hcont : ContinuousOn f
      {y : Vec d | ‖y - z‖ ≤ 3 * (3 : ℝ) ^ m / 8}) :
    BddAbove {q : ℝ | ∃ u ∈ {y : Vec d | ‖y - z‖ ≤
        3 * (3 : ℝ) ^ m / 8},
      ∃ v ∈ {y : Vec d | ‖y - z‖ ≤ 3 * (3 : ℝ) ^ m / 8},
        q = |f u - f v|} := by
  let D := {y : Vec d | ‖y - z‖ ≤ 3 * (3 : ℝ) ^ m / 8}
  have hcompact : IsCompact D := by
    rw [show D = Metric.closedBall z (3 * (3 : ℝ) ^ m / 8) by
      exact oscillationWindow_eq_closedBall m z]
    exact isCompact_closedBall z _
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hcont.norm
  refine ⟨2 * C, ?_⟩
  rintro q ⟨u, hu, v, hv, rfl⟩
  have huC : |f u| ≤ C := by
    simpa only [Real.norm_eq_abs, abs_abs] using hC u hu
  have hvC : |f v| ≤ C := by
    simpa only [Real.norm_eq_abs, abs_abs] using hC v hv
  exact (abs_sub (f u) (f v)).trans (by linarith)

/-- At a collared point and nonpositive scale, the arbitrary-center
Caccioppoli datum is controlled directly by the ambient oscillation.
The center is the value of the canonical representative at that point. -/
theorem halfBallCaccioppoliDataPrice_nonpositive_le_ambientOscillation
    [NeZero d] {m : ℤ} (hm : m ≤ 0) {z x : Vec d}
    (hcollar : ‖x - z‖ ≤ (3 : ℝ) ^ m / 4)
    {h : H1Function (translatedCube d m z)}
    {hRep : Vec d → ℝ}
    (hRepCont : ContinuousOn hRep (translatedCube d m z))
    (hRepAE : hRep =ᵐ[volume.restrict (translatedCube d m z)] h.toFun) :
    let R := boundedMultiplierNonpositiveRadiusFloor d * (3 : ℝ) ^ m
    halfBallCaccioppoliDataPrice d x R h.toFun (hRep x) * (R / 2) ≤
      boundedMultiplierCaccioppoliEndpointConst d *
        oscillationOn {y : Vec d | ‖y - z‖ ≤
          3 * (3 : ℝ) ^ m / 8} hRep := by
  dsimp only
  let R := boundedMultiplierNonpositiveRadiusFloor d * (3 : ℝ) ^ m
  let D := {y : Vec d | ‖y - z‖ ≤ 3 * (3 : ℝ) ^ m / 8}
  have hR : 0 < R := mul_pos
    (boundedMultiplierNonpositiveRadiusFloor_pos d) (by positivity)
  obtain ⟨p, hp, hxcell, hballCell⟩ :=
    exists_coverCell_euclideanBall_subset hcollar hR
      (by simpa only [R] using
        boundedMultiplierNonpositiveRadius_mul_le_mesh (d := d) hm)
      (by simpa only [R] using
        boundedMultiplierNonpositiveRadius_mul_le_ambient (d := d) (m := m))
  have hballB : euclideanBall x R ⊆ translatedCube d m z :=
    hballCell.trans Set.inter_subset_left
  have hballD : euclideanBall x R ⊆ D := by
    simpa only [R, D] using
      euclideanBall_nonpositiveRadius_subset_oscillationWindow
        (d := d) hcollar
  have hxD : x ∈ D := by
    dsimp only [D]
    have hpow : 0 < (3 : ℝ) ^ m := by positivity
    change ‖x - z‖ ≤ 3 * (3 : ℝ) ^ m / 8
    exact hcollar.trans (by nlinarith)
  have hDsub : D ⊆ translatedCube d m z := by
    simpa only [D] using oscillationWindow_subset_translatedCube (d := d) m z
  have hRepContD : ContinuousOn hRep D := hRepCont.mono hDsub
  have hbdd : BddAbove {q : ℝ | ∃ u ∈ D, ∃ v ∈ D,
      q = |hRep u - hRep v|} := by
    simpa only [D] using
      bddAbove_oscillationValues_of_continuousOn_window hRepContD
  have hDne : D.Nonempty := ⟨x, hxD⟩
  have hOsc0 : 0 ≤ oscillationOn D hRep := by
    apply le_csSup hbdd
    exact ⟨x, hxD, x, hxD, by simp⟩
  have hmem : MemLp h.toFun 2 (volume.restrict (euclideanBall x R)) :=
    h.memL2.mono_measure (Measure.restrict_mono hballB le_rfl)
  let : IsFiniteMeasure (volume.restrict (euclideanBall x R)) :=
    Homogenization.Book.Ch01.isFiniteMeasure_volumeMeasureOn_euclideanBall x R
  have hconst : MemLp (fun _ : Vec d ↦ hRep x) 2
      (volume.restrict (euclideanBall x R)) := memLp_const (hRep x)
  have hint : IntegrableOn (fun y ↦ (h.toFun y - hRep x) ^ 2)
      (euclideanBall x R) := (hmem.sub hconst).integrable_sq
  have hRepAEBall : hRep =ᵐ[volume.restrict (euclideanBall x R)] h.toFun :=
    hRepAE.filter_mono (ae_mono (Measure.restrict_mono hballB le_rfl))
  have hbound : ∀ᵐ y ∂volume.restrict (euclideanBall x R),
      |h.toFun y - hRep x| ≤ oscillationOn D hRep := by
    filter_upwards [hRepAEBall,
      ae_restrict_mem (isOpen_euclideanBall x R).measurableSet] with y hy hyball
    rw [← hy]
    exact le_csSup hbdd ⟨y, hballD hyball, x, hxD, rfl⟩
  have hprice :=
    halfBallCaccioppoliDataPrice_mul_halfRadius_le_of_ae_abs_le
      hR hOsc0 (hRep x) hint hbound
  simpa only [R, D] using hprice

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
