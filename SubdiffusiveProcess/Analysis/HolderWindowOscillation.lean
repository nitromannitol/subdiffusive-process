module

public import SubdiffusiveProcess.Analysis.NormalizedOscillation
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Geometry.CoordinateFold

@[expose] public section

/-! Holder bounds control normalized quadratic oscillation on ball-cube windows.
All constants are deterministic; no PDE regularity is inferred. -/
open MeasureTheory Set Metric SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Lane4
open Homogenization hiding Vec
open scoped ENNReal BigOperators
namespace SubdiffusiveProcess

/-- A bound on deviation from any constant bounds the mean oscillation. -/
theorem normalizedOscillation_le_of_ae_sub_bound {d : ℕ} {W : Set (Vec d)}
    (hW : MeasurableSet W) (hpos : 0 < (volume W).toReal) (hfin : volume W ≠ ⊤)
    (f : Vec d → ℝ) (hf : MemLp f 2 (volume.restrict W)) (c M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ᵐ x ∂volume.restrict W,|f x-c| ≤ M) :
    normalizedL2On W (fun x => f x-averageOn W f) ≤ M := by
  haveI hfinite : IsFiniteMeasure (volume.restrict W) := ⟨by simpa only [Measure.restrict_apply_univ] using hfin.lt_top⟩
  have hf2 : IntegrableOn (fun x => f x^2) W := hf.integrable_sq
  have hmean := Section6Iteration.normalizedL2On_sub_volumeAverage_le hW hpos hfin
    (hf.integrable (by norm_num)) hf2 c
  have hfsub2 : IntegrableOn (fun x => (f x-c)^2) W := (hf.sub (memLp_const c)).integrable_sq
  apply hmean.trans
  apply Section6Iteration.normalizedL2On_le_of_sq_le hM
  have hint : (∫ x in W,(f x-c)^2) ≤ (volume W).toReal*M^2 := by
    have hh := integral_mono_ae hfsub2 (integrable_const (M^2)) (hbound.mono fun x hx => by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (f x-c)) hx 2)
    simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul] using hh
  unfold volumeAverage
  have hh := mul_le_mul_of_nonneg_left hint (inv_pos.mpr hpos).le
  simpa only [← mul_assoc,inv_mul_cancel₀ hpos.ne',one_mul] using hh

/-- The full Holder norm bounds each Euclidean Holder increment. -/
theorem cAlphaNorm_pair_le {d : ℕ}
    (a A : ℝ) (ha : 0 < a) (S : Set (SpatialCoordinates d))
    (U : SpatialCoordinates d → ℝ)
    (hH : IsHolderOn a S U) (hA : cAlphaNorm a S U ≤ A)
    (x y : SpatialCoordinates d) (hx : x ∈ S) (hy : y ∈ S) :
    |U x - U y| ≤ A * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ a := by
  by_cases hxy : x = y
  · subst hxy
    simp only [sub_self,zero_pow (by norm_num : 2 ≠ 0),Finset.sum_const_zero,Real.sqrt_zero,Real.zero_rpow ha.ne',mul_zero,abs_zero,le_refl]
  · have hne_coord : ∃ j : Fin d, x j ≠ y j := by
      by_contra h
      push_neg at h
      exact hxy (funext h)
    obtain ⟨j, hj⟩ := hne_coord
    have hsum_pos : 0 < ∑ k : Fin d, (x k - y k) ^ 2 := by
      apply Finset.sum_pos'
      · intro k _
        positivity
      · exact ⟨j, Finset.mem_univ j, sq_pos_of_ne_zero (sub_ne_zero.mpr hj)⟩
    set ρ := Real.sqrt (∑ k : Fin d, (x k - y k) ^ 2) with hρdef
    have hρpos : 0 < ρ := by
      rw [hρdef]
      exact Real.sqrt_pos.mpr hsum_pos
    have hρa_pos : 0 < ρ ^ a := Real.rpow_pos_of_pos hρpos a
    have hmem : |U x - U y| / ρ ^ a ∈ holderRatioSet a S U := by
      refine ⟨x, hx, y, hy, hxy, ?_⟩
      rw [hρdef]
    have hle1 : |U x - U y| / ρ ^ a ≤ holderSeminorm a S U := le_csSup hH hmem
    have hfirst_nonneg : 0 ≤ sSup {v : ℝ | ∃ x ∈ S, v = |U x|} := by
      apply Real.sSup_nonneg
      intro v hv
      rcases hv with ⟨w, _, rfl⟩
      exact abs_nonneg (U w)
    have hle2 : holderSeminorm a S U ≤ cAlphaNorm a S U := by
      unfold cAlphaNorm holderSeminorm
      linarith only [hfirst_nonneg]
    have hle3 : |U x - U y| / ρ ^ a ≤ A := le_trans hle1 (le_trans hle2 hA)
    rw [div_le_iff₀ hρa_pos] at hle3
    rw [hρdef] at hle3
    exact hle3

/-- A Euclidean Holder bound controls each ball-window mean oscillation. -/
theorem holder_ball_window_oscillation_le {d : ℕ} (hd : 1 ≤ d)
    (alpha A : ℝ) (ha : 0 < alpha) (hA : 0 ≤ A)
    (U : SpatialCoordinates d → ℝ)
    (hmem : MemLp U 2 (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))))
    (hpair : ∀ x ∈ (closedCube (fun _ : Fin d => (1/2:ℝ)) 1 one_pos : Set (SpatialCoordinates d)),
      ∀ y ∈ (closedCube (fun _ : Fin d => (1/2:ℝ)) 1 one_pos : Set (SpatialCoordinates d)),
      |U x-U y| ≤ A*(Real.sqrt (∑ i : Fin d,(x i-y i)^2))^alpha)
    (w : SpatialCoordinates d) (hw : w ∈ (unitNeumannCube d : Set (SpatialCoordinates d)))
    (r : ℝ) (hr : 0 < r) :
    let W := ball w r ∩ (unitNeumannCube d : Set (SpatialCoordinates d))
    normalizedL2On W (fun y => U y-averageOn W U) ≤ A*((d:ℝ)*r)^alpha := by
  intro W
  have hWfin : volume W ≠ ⊤ := (lt_of_le_of_lt (measure_mono inter_subset_right)
    (show volume (unitNeumannCube d : Set (SpatialCoordinates d)) < ⊤ by
      rw [unitNeumannCube,centeredCube_volume]; exact ENNReal.ofReal_lt_top)).ne
  have hWpos : 0 < (volume W).toReal := ENNReal.toReal_pos
    ((isOpen_ball.inter (unitNeumannCube d).isOpen).measure_pos volume ⟨w,mem_ball_self hr,hw⟩).ne' hWfin
  apply normalizedOscillation_le_of_ae_sub_bound
    (isOpen_ball.inter (unitNeumannCube d).isOpen).measurableSet hWpos hWfin U
    (hmem.mono_measure (Measure.restrict_mono inter_subset_right le_rfl)) (U w)
    (A*((d:ℝ)*r)^alpha) (by positivity)
  filter_upwards [ae_restrict_mem (isOpen_ball.inter (unitNeumannCube d).isOpen).measurableSet] with y hy
  have hdim : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hcoords (i : Fin d) : |y i-w i| ≤ r := by
    have hh := (dist_pi_le_iff hr.le).mp (le_of_lt hy.1) i
    simpa only [Real.dist_eq] using hh
  have hs : ∑ i : Fin d,(y i-w i)^2 ≤ (d:ℝ)*r^2 := by
    have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
      pow_le_pow_left₀ (abs_nonneg _) (hcoords i) 2)
    simpa only [sq_abs,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh
  have he : Real.sqrt (∑ i : Fin d,(y i-w i)^2) ≤ (d:ℝ)*r := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    have hd2 : (d:ℝ) ≤ (d:ℝ)^2 := by nlinarith only [hdim]
    have hh := mul_le_mul_of_nonneg_right hd2 (sq_nonneg r)
    nlinarith only [hs,hh]
  exact (hpair y (centeredCube_subset_closedCube _ _ hy.2) w
    (centeredCube_subset_closedCube _ _ hw)).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Real.sqrt_nonneg _) he ha.le) hA)

end SubdiffusiveProcess
