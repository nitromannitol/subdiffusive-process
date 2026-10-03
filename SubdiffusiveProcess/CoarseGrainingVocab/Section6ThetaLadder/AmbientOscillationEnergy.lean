module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.OscillationEnergyReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.RepresentativeReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.TriadicMeanComparison

@[expose] public section

/-!
# Theta ladder: top-window energy from the ambient oscillation

Every moving scale-`m-2` comparison cube lies in the compact collar.  The
centered energy on that cube is therefore bounded by the literal collar
oscillation of the canonical representative.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory Topology Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

noncomputable section

variable {d : ℕ}

private def ambientOscillationWindow (m : ℤ) (z : Vec d) : Set (Vec d) :=
  {x : Vec d | ‖x - z‖ ≤ 3 * (3 : ℝ) ^ m / 8}

private theorem ambientOscillationWindow_eq_closedBall (m : ℤ) (z : Vec d) :
    ambientOscillationWindow m z =
      Metric.closedBall z (3 * (3 : ℝ) ^ m / 8) := by
  ext x
  simp only [ambientOscillationWindow, Set.mem_setOf_eq,
    Metric.mem_closedBall, dist_eq_norm]

private theorem ambientOscillationWindow_subset_parent (m : ℤ) (z : Vec d) :
    ambientOscillationWindow m z ⊆ translatedCube d m z := by
  rw [ambientOscillationWindow_eq_closedBall, translatedCube_eq_metricBall]
  apply Metric.closedBall_subset_ball
  have hpow : 0 < (3 : ℝ) ^ m := by positivity
  nlinarith

/-- The centered normalized `L²` row on any positive-volume subwindow of the
collar is bounded by the literal collar oscillation of the canonical
representative. -/
theorem normalizedL2On_centered_le_ambientOscillation
    {m : ℤ} {z : Vec d} {W : Set (Vec d)}
    (hWmeas : MeasurableSet W) (hWpos : 0 < (volume W).toReal)
    (hWtop : volume W ≠ ⊤) (hW : W.Nonempty)
    (hWsub : W ⊆ {x : Vec d | ‖x - z‖ ≤ 3 * (3 : ℝ) ^ m / 8})
    {h : H1Function (translatedCube d m z)} {hRep : Vec d → ℝ}
    (hRepCont : ContinuousOn hRep (translatedCube d m z))
    (hRepAE : hRep =ᵐ[volume.restrict (translatedCube d m z)] h.toFun) :
    normalizedL2On W
        (fun x ↦ h.toFun x - averageOn W h.toFun) ≤
      oscillationOn {x : Vec d | ‖x - z‖ ≤
        3 * (3 : ℝ) ^ m / 8} hRep := by
  let D := ambientOscillationWindow m z
  have hDsub : D ⊆ translatedCube d m z :=
    ambientOscillationWindow_subset_parent m z
  have hWparent : W ⊆ translatedCube d m z := hWsub.trans hDsub
  have hRepAEW : hRep =ᵐ[volume.restrict W] h.toFun :=
    hRepAE.filter_mono (ae_mono (Measure.restrict_mono hWparent le_rfl))
  have hbase : MemLp h.toFun 2 (volume.restrict W) :=
    h.memL2.mono_measure (Measure.restrict_mono hWparent le_rfl)
  have hRepMeas : AEStronglyMeasurable hRep (volume.restrict W) :=
    hbase.aestronglyMeasurable.congr hRepAEW.symm
  have hRepMem : MemLp hRep 2 (volume.restrict W) := by
    apply hbase.congr_norm hRepMeas
    filter_upwards [hRepAEW] with x hx
    rw [hx]
  letI : IsFiniteMeasure (volume.restrict W) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hWtop⟩
  have hf : IntegrableOn hRep W := hRepMem.integrable one_le_two
  have hf2 : IntegrableOn (fun x ↦ hRep x ^ 2) W := hRepMem.integrable_sq
  have hDcompact : IsCompact D := by
    dsimp only [D]
    rw [ambientOscillationWindow_eq_closedBall]
    exact isCompact_closedBall z _
  have hDcont : ContinuousOn hRep D := hRepCont.mono hDsub
  obtain ⟨K, hK⟩ := hDcompact.exists_bound_of_continuousOn hDcont.norm
  have hbdd : BddAbove {q : ℝ | ∃ x ∈ D, ∃ y ∈ D,
      q = |hRep x - hRep y|} := by
    refine ⟨2 * K, ?_⟩
    rintro q ⟨x, hx, y, hy, rfl⟩
    have hxK : |hRep x| ≤ K := by
      simpa only [Real.norm_eq_abs, abs_abs] using hK x hx
    have hyK : |hRep y| ≤ K := by
      simpa only [Real.norm_eq_abs, abs_abs] using hK y hy
    exact (abs_sub (hRep x) (hRep y)).trans (by linarith)
  have hrep := normalizedL2On_centered_le_oscillationOn
    hWmeas hWpos hWtop hW (by exact hWsub)
      hf hf2 hbdd
  rw [← normalizedL2On_sub_average_eq_of_ae_eq hRepAEW]
  simpa only [D, ambientOscillationWindow] using hrep

/-- A scale-`m-2` comparison cube contained in the parent has the fixed
two-scale centered-energy price `sqrt ((3^2)^d)`. -/
theorem normalizedL2On_predTwo_centered_le_parent
    {m : ℤ} {z q : Vec d} {f : Vec d → ℝ}
    (hsub : translatedCube d (m - 2) (z + q) ⊆ translatedCube d m z)
    (hf : IntegrableOn f (translatedCube d m z))
    (hf2 : IntegrableOn (fun x ↦ f x ^ 2) (translatedCube d m z)) :
    normalizedL2On (translatedCube d (m - 2) (z + q))
        (fun x ↦ f x - averageOn
          (translatedCube d (m - 2) (z + q)) f) ≤
      Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
        normalizedL2On (translatedCube d m z)
          (fun x ↦ f x - averageOn (translatedCube d m z) f) := by
  let W := translatedCube d (m - 2) (z + q)
  let Q := translatedCube d m z
  have hWmeas : MeasurableSet W := by
    dsimp only [W]
    rw [translatedCube_eq_metricBall]
    exact measurableSet_ball
  have hWpos := volume_translatedCube_toReal_pos (d := d) (m - 2) (z + q)
  have hWtop := volume_translatedCube_ne_top (d := d) (m - 2) (z + q)
  have hQpos := volume_translatedCube_toReal_pos (d := d) m z
  have hfW := hf.mono_set hsub
  have hf2W := hf2.mono_set hsub
  have hmean := Section6Iteration.normalizedL2On_sub_volumeAverage_le
    hWmeas hWpos hWtop hfW hf2W (averageOn Q f)
  have hcenterSq : IntegrableOn
      (fun x ↦ (f x - averageOn Q f) ^ 2) Q := by
    have hlinear : IntegrableOn
        (fun x ↦ 2 * averageOn Q f * f x) Q :=
      hf.const_mul (2 * averageOn Q f)
    have hconst : IntegrableOn (fun _ : Vec d ↦ averageOn Q f ^ 2) Q :=
      integrableOn_const (volume_translatedCube_ne_top m z)
    have hid : (fun x ↦ (f x - averageOn Q f) ^ 2) =
        fun x ↦ f x ^ 2 - 2 * averageOn Q f * f x +
          averageOn Q f ^ 2 := by
      funext x
      ring
    rw [hid]
    exact (hf2.sub hlinear).add hconst
  have hrestrict := Section6Iteration.normalizedL2On_le_of_subset
    hsub hQpos hWpos hcenterSq
  have hratio : Real.sqrt ((volume Q).toReal / (volume W).toReal) =
      Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) := by
    dsimp only [Q, W]
    rw [volume_translatedCube_toReal, volume_translatedCube_toReal]
    have hthree : (3 : ℝ) ≠ 0 := by norm_num
    have hpow : (3 : ℝ) ^ (m - 2) = (3 : ℝ) ^ m / (3 : ℝ) ^ (2 : ℤ) := by
      rw [zpow_sub₀ hthree]
    rw [hpow, div_pow]
    have hm0 : (3 : ℝ) ^ m ≠ 0 := zpow_ne_zero _ hthree
    congr 1
    field_simp
  rw [hratio] at hrestrict
  exact hmean.trans hrestrict

/-- The scale-`m-4` target-top mean differs from the parent mean by the fixed
four-scale volume price. -/
theorem abs_averageOn_predFour_sub_parent_le
    {m : ℤ} {z z' : Vec d} {f : Vec d → ℝ}
    (hsub : translatedCube d (m - 4) z' ⊆ translatedCube d m z)
    (hf : IntegrableOn f (translatedCube d m z))
    (hf2 : IntegrableOn (fun x ↦ f x ^ 2) (translatedCube d m z)) :
    |averageOn (translatedCube d (m - 4) z') f -
        averageOn (translatedCube d m z) f| ≤
      Real.sqrt (((3 : ℝ) ^ (4 : ℤ)) ^ d) *
        normalizedL2On (translatedCube d m z)
          (fun x ↦ f x - averageOn (translatedCube d m z) f) := by
  have hraw := abs_averageOn_subset_sub_averageOn_le
    (by rw [translatedCube_eq_metricBall]; exact measurableSet_ball)
    hsub (volume_translatedCube_ne_top m z)
    (volume_translatedCube_toReal_pos m z)
    (volume_translatedCube_toReal_pos (m - 4) z') hf hf2
  have hratio : Real.sqrt
      ((volume (translatedCube d m z)).toReal /
        (volume (translatedCube d (m - 4) z')).toReal) =
      Real.sqrt (((3 : ℝ) ^ (4 : ℤ)) ^ d) := by
    rw [volume_translatedCube_toReal, volume_translatedCube_toReal]
    have hthree : (3 : ℝ) ≠ 0 := by norm_num
    have hpow : (3 : ℝ) ^ (m - 4) = (3 : ℝ) ^ m / (3 : ℝ) ^ (4 : ℤ) := by
      rw [zpow_sub₀ hthree]
    rw [hpow, div_pow]
    have hm0 : (3 : ℝ) ^ m ≠ 0 := zpow_ne_zero _ hthree
    congr 1
    field_simp
  rwa [hratio] at hraw

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
