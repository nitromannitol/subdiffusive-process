module

public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set
open SubdiffusiveProcess
open scoped ENNReal

noncomputable section
namespace Paper

theorem aux_lem_interp_averaging_holder_bound {d : ℕ} {alpha : ℝ}
    {S : Set (SpatialCoordinates d)} {v : SpatialCoordinates d → ℝ}
    (ha0 : 0 < alpha) (hv : Lane4.IsHolderOn alpha S v) :
    ∀ x ∈ S, ∀ y ∈ S,
      |v x - v y| ≤ Lane4.holderSeminorm alpha S v *
        (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by
  intro x hx y hy
  by_cases hxy : x = y
  · subst hxy
    simp [ha0.ne']
  have hmem :
      |v x - v y| /
          (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha ∈
        Lane4.holderRatioSet alpha S v := by
    refine ⟨x, hx, y, hy, hxy, rfl⟩
  have hsum : 0 < ∑ j : Fin d, (x j - y j) ^ 2 := by
    obtain ⟨j, hj⟩ : ∃ j : Fin d, x j ≠ y j := by
      by_contra h
      push_neg at h
      exact hxy (funext h)
    exact Finset.sum_pos' (fun i _ => sq_nonneg (x i - y i))
      ⟨j, Finset.mem_univ _, sq_pos_of_ne_zero (sub_ne_zero.mpr hj)⟩
  have hden : 0 < (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha :=
    Real.rpow_pos_of_pos (Real.sqrt_pos.2 hsum) _
  have hle :
      |v x - v y| /
          (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha ≤
        Lane4.holderSeminorm alpha S v := by
    unfold Lane4.IsHolderOn at hv
    unfold Lane4.holderSeminorm
    exact le_csSup hv hmem
  exact (div_le_iff₀ hden).mp hle

theorem aux_lem_interp_averaging_euclidean_le_dist {d : ℕ}
    (x y : SpatialCoordinates d) :
    Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ (d : ℝ) * dist x y := by
  have hsum : ∑ j : Fin d, (x j - y j) ^ 2 ≤
      (d : ℝ) * (dist x y) ^ 2 := by
    calc
      ∑ j : Fin d, (x j - y j) ^ 2 ≤ ∑ j : Fin d, (dist x y) ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hjdist : dist (x j) (y j) ≤ dist x y :=
          (dist_pi_le_iff (dist_nonneg)).mp (le_refl (dist x y)) j
        have hjabs : |x j - y j| ≤ dist x y := by
          simpa [Real.dist_eq] using hjdist
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _) (dist_nonneg)).2 hjabs
      _ = (d : ℝ) * (dist x y) ^ 2 := by
        simp [Finset.card_univ, nsmul_eq_mul]
  have hdprod : (d : ℝ) * (dist x y) ^ 2 ≤ ((d : ℝ) * dist x y) ^ 2 := by
    by_cases hd : d = 0
    · simp [hd]
    · have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hd)
      nlinarith [sq_nonneg (dist x y), mul_nonneg (by positivity : (0 : ℝ) ≤ d)
        (sq_nonneg (dist x y))]
  exact (Real.sqrt_le_iff).2
    ⟨mul_nonneg (by positivity) dist_nonneg, hsum.trans hdprod⟩

theorem aux_lem_interp_averaging_continuousOn {d : ℕ} {alpha : ℝ}
    {S : Set (SpatialCoordinates d)} {v : SpatialCoordinates d → ℝ}
    (ha0 : 0 < alpha) (hK : 0 ≤ Lane4.holderSeminorm alpha S v)
    (hbound : ∀ x ∈ S, ∀ y ∈ S,
      |v x - v y| ≤ Lane4.holderSeminorm alpha S v *
        (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha) :
    ContinuousOn v S := by
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  let φ : ℝ → ℝ := fun t =>
    Lane4.holderSeminorm alpha S v * ((d : ℝ) * t) ^ alpha
  have hφ : ContinuousAt φ 0 := by
    dsimp [φ]
    exact continuousAt_const.mul
      ((continuousAt_const.mul continuousAt_id).rpow_const (Or.inr ha0.le))
  obtain ⟨δ, hδ, hφδ⟩ := (Metric.continuousAt_iff.mp hφ) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro y hy hyd
  have he := aux_lem_interp_averaging_euclidean_le_dist y x
  have hepow :
      (Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2)) ^ alpha ≤
        ((d : ℝ) * dist y x) ^ alpha :=
    Real.rpow_le_rpow (Real.sqrt_nonneg _) he ha0.le
  have hmain := hbound y hy x hx
  have hmain' :
      |v y - v x| ≤ Lane4.holderSeminorm alpha S v *
        ((d : ℝ) * dist y x) ^ alpha :=
    hmain.trans (mul_le_mul_of_nonneg_left hepow hK)
  have hφlt : φ (dist y x) < ε := by
    have hdist : dist (dist y x) 0 < δ := by
      simpa [Real.dist_eq, abs_of_nonneg dist_nonneg] using hyd
    have ht := hφδ hdist
    have hnon : 0 ≤ ((d : ℝ) * dist y x) ^ alpha :=
      Real.rpow_nonneg (mul_nonneg (by positivity) dist_nonneg) _
    simpa [φ, ha0.ne', Real.dist_eq,
      abs_of_nonneg hK, abs_of_nonneg hnon, abs_mul] using ht
  simpa [Real.dist_eq] using hmain'.trans_lt hφlt

def aux_lem_interp_averaging_box {d : ℕ} (x : SpatialCoordinates d) (h : ℝ) :
    Set (SpatialCoordinates d) :=
  Set.pi Set.univ (fun i =>
    if x i ≤ 0 then Set.Ioo (x i) (x i + h / (2 * (d : ℝ)))
    else Set.Ioo (x i - h / (2 * (d : ℝ))) (x i))

theorem aux_lem_interp_averaging_closed_cube_coords {d : ℕ}
    (x : SpatialCoordinates d)
    (hx : x ∈ closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
      Set (SpatialCoordinates d))) :
    ∀ i : Fin d, x i ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
  intro i
  have hxball : x ∈ Metric.closedBall (0 : SpatialCoordinates d) (1 / 2 : ℝ) := by
    apply closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall
    exact hx
  have hxd : dist x (0 : SpatialCoordinates d) ≤ (1 / 2 : ℝ) := by
    exact hxball
  have hi : dist (x i) 0 ≤ (1 / 2 : ℝ) :=
    (dist_pi_le_iff (by norm_num)).mp hxd i
  simpa [Real.dist_eq, abs_le] using hi

theorem aux_lem_interp_averaging_box_measurable {d : ℕ} (x : SpatialCoordinates d)
    (h : ℝ) : MeasurableSet (aux_lem_interp_averaging_box x h) := by
  unfold aux_lem_interp_averaging_box
  exact MeasurableSet.pi Set.countable_univ (fun i _ => by
    split <;> exact measurableSet_Ioo)

theorem aux_lem_interp_averaging_box_subset {d : ℕ} (hd : 1 ≤ d)
    (x : SpatialCoordinates d) (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hx : x ∈ closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
      Set (SpatialCoordinates d))) :
    aux_lem_interp_averaging_box x h ⊆
      (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
        Set (SpatialCoordinates d)) := by
  intro y hy
  change y ∈ Metric.ball (0 : SpatialCoordinates d) (1 / 2 : ℝ)
  apply (dist_pi_lt_iff (by norm_num)).2
  intro i
  have hxi := aux_lem_interp_averaging_closed_cube_coords x hx i
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hrpos : 0 < h / (2 * (d : ℝ)) := by positivity
  have hrle : h / (2 * (d : ℝ)) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith
  have hyi := (Set.mem_pi.mp hy) i (Set.mem_univ i)
  by_cases hxi0 : x i ≤ 0
  · simp only [hxi0, if_pos] at hyi
    rw [Real.dist_eq]
    simp only [Pi.zero_apply]
    rw [abs_lt]
    have hxil := hxi.1
    have hxiu := hxi.2
    constructor <;> nlinarith [hyi.1, hyi.2]
  · have hxi0' : 0 < x i := lt_of_not_ge hxi0
    simp [hxi0] at hyi
    rw [Real.dist_eq]
    simp only [Pi.zero_apply]
    rw [abs_lt]
    have hxil := hxi.1
    have hxiu := hxi.2
    constructor <;> nlinarith [hyi.1, hyi.2]

theorem aux_lem_interp_averaging_box_distance {d : ℕ} (hd : 1 ≤ d)
    (x : SpatialCoordinates d) (h : ℝ) (hh : 0 < h)
    (y : SpatialCoordinates d)
    (hy : y ∈ aux_lem_interp_averaging_box x h) :
    Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2) ≤ h := by
  let r : ℝ := h / (2 * (d : ℝ))
  have hdr : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have hdrpos : 0 < (d : ℝ) := lt_of_lt_of_le (by norm_num) hdr
  have hrsq : (d : ℝ) * r ^ 2 ≤ h ^ 2 := by
    dsimp [r]
    field_simp
    nlinarith [sq_nonneg h, sq_nonneg (d : ℝ)]
  have hsum : ∑ j : Fin d, (y j - x j) ^ 2 ≤ h ^ 2 := by
    calc
      ∑ j : Fin d, (y j - x j) ^ 2 ≤ ∑ j : Fin d, r ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hyj := (Set.mem_pi.mp hy) j (Set.mem_univ j)
        have hdif : |y j - x j| ≤ r := by
          by_cases hxj : x j ≤ 0
          · simp only [aux_lem_interp_averaging_box, hxj, if_pos] at hyj
            rw [abs_le]
            constructor <;> linarith [hyj.1, hyj.2]
          · simp [aux_lem_interp_averaging_box, hxj] at hyj
            rw [abs_le]
            constructor <;> linarith [hyj.1, hyj.2]
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hdif
      _ = (d : ℝ) * r ^ 2 := by
        simp [Finset.card_univ, nsmul_eq_mul]
      _ ≤ h ^ 2 := hrsq
  exact (Real.sqrt_le_iff).2 ⟨le_of_lt hh, hsum⟩

theorem aux_lem_interp_averaging_box_volume {d : ℕ} (hd : 1 ≤ d)
    (x : SpatialCoordinates d) (h : ℝ) (hh : 0 ≤ h) :
    volume (aux_lem_interp_averaging_box x h) =
      ENNReal.ofReal ((h / (2 * (d : ℝ))) ^ d) := by
  unfold aux_lem_interp_averaging_box
  let a : Fin d → ℝ := fun i => if x i ≤ 0 then x i else x i - h / (2 * (d : ℝ))
  let b : Fin d → ℝ := fun i => if x i ≤ 0 then x i + h / (2 * (d : ℝ)) else x i
  have hset :
      Set.pi Set.univ (fun i =>
          if x i ≤ 0 then Set.Ioo (x i) (x i + h / (2 * (d : ℝ)))
          else Set.Ioo (x i - h / (2 * (d : ℝ))) (x i)) =
        Set.pi Set.univ (fun i => Set.Ioo (a i) (b i)) := by
    congr 1
    funext i
    dsimp [a, b]
    split <;> rfl
  rw [hset, Real.volume_pi_Ioo]
  have hfac : ∀ i : Fin d,
      ENNReal.ofReal (b i - a i) =
        ENNReal.ofReal (h / (2 * (d : ℝ))) := by
    intro i
    dsimp [a, b]
    split <;> simp_all
  simp_rw [hfac]
  rw [Finset.prod_const]
  rw [ENNReal.ofReal_pow]
  · simp
  · exact div_nonneg hh (by positivity)



theorem lem_interp_averaging (d : ℕ) (hd : 1 ≤ d) (alpha : ℝ)
    (ha0 : 0 < alpha) (ha : alpha ≤ 1) :
    let Q0 := centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num)
    let S := closure (Q0 : Set (SpatialCoordinates d))
    ∃ C : ℝ, 0 < C ∧
      ∀ v : SpatialCoordinates d → ℝ, Lane4.IsHolderOn alpha S v →
        MemLp v 2 (volume.restrict (Q0 : Set (SpatialCoordinates d))) ∧
          ∀ h : ℝ, 0 < h → h ≤ 1 →
            ∀ x ∈ S,
              |v x| ≤ C * h ^ (-(d : ℝ) / 2) *
                  (eLpNorm v 2 (volume.restrict (Q0 : Set (SpatialCoordinates d)))).toReal +
                Lane4.holderSeminorm alpha S v * h ^ alpha := by
  let C : ℝ := (2 * (d : ℝ)) ^ ((d : ℝ) / 2)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro v hv
    have hbound := aux_lem_interp_averaging_holder_bound ha0 hv
    have hK : 0 ≤ Lane4.holderSeminorm alpha
        (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
          Set (SpatialCoordinates d))) v := by
      unfold Lane4.IsHolderOn at hv
      unfold Lane4.holderSeminorm
      by_cases hne : (Lane4.holderRatioSet alpha
          (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
            Set (SpatialCoordinates d))) v).Nonempty
      · rcases hne with ⟨r, hr⟩
        have hmem : r ∈ Lane4.holderRatioSet alpha
            (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
              Set (SpatialCoordinates d))) v := hr
        have hr0 : 0 ≤ r := by
          rcases hmem with ⟨x, hx, y, hy, hxy, rfl⟩
          exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
        exact hr0.trans (le_csSup hv hmem)
      · rw [Set.not_nonempty_iff_eq_empty.mp hne]
        simp
    have hcont : ContinuousOn v
        (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
          Set (SpatialCoordinates d))) :=
      aux_lem_interp_averaging_continuousOn ha0 hK hbound
    have hSc : IsCompact
        (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
          Set (SpatialCoordinates d))) :=
      (centeredCube_isBounded (0 : SpatialCoordinates d) (by norm_num)).isCompact_closure
    have hSmeas : MeasurableSet
        (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
          Set (SpatialCoordinates d))) := hSc.measurableSet
    letI : IsFiniteMeasure (volume.restrict
        (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
          Set (SpatialCoordinates d)))) :=
      isFiniteMeasure_restrict.mpr (ne_of_lt hSc.measure_lt_top)
    have hvSmeas : AEStronglyMeasurable v (volume.restrict
        (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
          Set (SpatialCoordinates d)))) :=
      hcont.aestronglyMeasurable_of_isCompact hSc hSmeas
    have hvSbound : BddAbove ((fun z : SpatialCoordinates d => |v z|) ''
        (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
          Set (SpatialCoordinates d)))) :=
      hSc.bddAbove_image hcont.abs
    obtain ⟨B, hB⟩ := (bddAbove_def.mp hvSbound)
    have hvS : MemLp v 2 (volume.restrict
        (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
          Set (SpatialCoordinates d)))) := by
      apply MemLp.of_bound hvSmeas B
      filter_upwards [ae_restrict_mem hSmeas] with z hz
      exact hB _ ⟨z, hz, rfl⟩
    have hQsub :
        (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
          Set (SpatialCoordinates d)) ⊆
        closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
          Set (SpatialCoordinates d)) := subset_closure
    have hvQ : MemLp v 2 (volume.restrict
        (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
          Set (SpatialCoordinates d))) :=
      hvS.mono_measure (Measure.restrict_mono hQsub le_rfl)
    refine ⟨hvQ, ?_⟩
    intro h hh hh1 x hx
    let A := aux_lem_interp_averaging_box x h
    have hAmeas : MeasurableSet A := aux_lem_interp_averaging_box_measurable x h
    have hAsub : A ⊆
        (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
          Set (SpatialCoordinates d)) := by
      exact aux_lem_interp_averaging_box_subset hd x h hh hh1 hx
    have hvolA : volume A = ENNReal.ofReal ((h / (2 * (d : ℝ))) ^ d) := by
      exact aux_lem_interp_averaging_box_volume hd x h hh.le
    letI : IsFiniteMeasure (volume.restrict A) :=
      isFiniteMeasure_restrict.mpr (by
        rw [hvolA]
        exact ENNReal.ofReal_ne_top)
    have hvA : MemLp v 2 (volume.restrict A) :=
      hvQ.mono_measure (Measure.restrict_mono hAsub le_rfl)
    have hdiffmeas : AEStronglyMeasurable (fun y => v x - v y)
        (volume.restrict A) := aestronglyMeasurable_const.sub hvA.aestronglyMeasurable
    have hdiffbound : ∀ y ∈ A, |v x - v y| ≤
        Lane4.holderSeminorm alpha
          (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
            Set (SpatialCoordinates d))) v * h ^ alpha := by
      intro y hy
      have he := aux_lem_interp_averaging_box_distance hd x h hh y hy
      have hep := Real.rpow_le_rpow (Real.sqrt_nonneg _) he ha0.le
      have hxy := hbound x hx y (hQsub (hAsub hy))
      have hsum_eq : (∑ j : Fin d, (x j - y j) ^ 2) =
          ∑ j : Fin d, (y j - x j) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [hsum_eq] at hxy
      exact hxy.trans (mul_le_mul_of_nonneg_left hep hK)
    have hdiff : MemLp (fun y => v x - v y) 2 (volume.restrict A) := by
      apply MemLp.of_bound hdiffmeas
        (Lane4.holderSeminorm alpha
          (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
            Set (SpatialCoordinates d))) v * h ^ alpha)
      filter_upwards [ae_restrict_mem hAmeas] with y hy
      simpa [Real.norm_eq_abs] using hdiffbound y hy
    have htri : eLpNorm (fun _ : SpatialCoordinates d => v x) 2
          (volume.restrict A) ≤
        eLpNorm (fun y => v x - v y) 2 (volume.restrict A) +
          eLpNorm v 2 (volume.restrict A) := by
      calc
        eLpNorm (fun _ : SpatialCoordinates d => v x) 2 (volume.restrict A) =
            eLpNorm ((fun y => v x - v y) + v) 2 (volume.restrict A) := by
              congr 1
              funext y
              simp only [Pi.add_apply]
              ring
        _ ≤ _ := eLpNorm_add_le (by norm_num)
    have hdiffnorm : eLpNorm (fun y => v x - v y) 2 (volume.restrict A) ≤
        (volume.restrict A) Set.univ ^ (2 : ℝ≥0∞).toReal⁻¹ *
          ENNReal.ofReal (Lane4.holderSeminorm alpha
            (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
              Set (SpatialCoordinates d))) v * h ^ alpha) := by
      apply eLpNorm_le_of_ae_bound hdiffmeas
      filter_upwards [ae_restrict_mem hAmeas] with y hy
      exact (by
        simpa [Real.norm_eq_abs] using hdiffbound y hy)
    have hAuniv : (volume.restrict A) Set.univ = volume A := by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp
    have hAreal : (h / (2 * (d : ℝ))) ^ d > 0 := by positivity
    have hApos : (volume.restrict A) Set.univ ≠ 0 := by
      rw [hAuniv, hvolA]
      exact (ENNReal.ofReal_pos.mpr hAreal).ne'
    have hconst : eLpNorm (fun _ : SpatialCoordinates d => v x) 2
          (volume.restrict A) =
        ‖v x‖ₑ * (volume.restrict A) Set.univ ^ (2 : ℝ≥0∞).toReal⁻¹ := by
      simpa [one_div] using
        (eLpNorm_const' (μ := volume.restrict A) (p := (2 : ℝ≥0∞))
          (v x) (by norm_num) (by norm_num))
    have htriR := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨hdiff.eLpNorm_ne_top, hvA.eLpNorm_ne_top⟩) htri
    rw [hconst, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
      ← ofReal_norm_eq_enorm, ENNReal.toReal_ofReal (norm_nonneg _),
      hAuniv, hvolA, ENNReal.toReal_ofReal (by positivity)] at htriR
    have hpow :
        ((h / (2 * (d : ℝ))) ^ d) ^ ((1 : ℝ) / 2) =
          (h / (2 * (d : ℝ))) ^ ((d : ℝ) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1
      ring
    norm_num at htriR
    rw [hpow] at htriR
    rw [ENNReal.toReal_add hdiff.eLpNorm_ne_top hvA.eLpNorm_ne_top] at htriR
    have hdiffRtop :
        (volume.restrict A) Set.univ ^ (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ *
            ENNReal.ofReal (Lane4.holderSeminorm alpha
              (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
                Set (SpatialCoordinates d))) v * h ^ alpha) ≠ ⊤ := by
      finiteness
    have hdiffR := ENNReal.toReal_mono hdiffRtop hdiffnorm
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, hAuniv, hvolA,
      ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)] at hdiffR
    norm_num at hdiffR
    rw [hpow] at hdiffR
    have hvAle : eLpNorm v 2 (volume.restrict A) ≤
        eLpNorm v 2 (volume.restrict
          (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
            Set (SpatialCoordinates d))) :=
      eLpNorm_mono_measure v (Measure.restrict_mono hAsub le_rfl)
    have hvAR := ENNReal.toReal_mono hvQ.eLpNorm_ne_top hvAle
    have hmain :
        |v x| * (h / (2 * (d : ℝ))) ^ ((d : ℝ) / 2) ≤
          (h / (2 * (d : ℝ))) ^ ((d : ℝ) / 2) *
              (Lane4.holderSeminorm alpha
                (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
                  Set (SpatialCoordinates d))) v * h ^ alpha) +
            (eLpNorm v 2 (volume.restrict
              (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
                Set (SpatialCoordinates d)))).toReal := by
      calc
        |v x| * (h / (2 * (d : ℝ))) ^ ((d : ℝ) / 2) ≤
            (eLpNorm (fun y => v x - v y) 2 (volume.restrict A)).toReal +
              (eLpNorm v 2 (volume.restrict A)).toReal := htriR
        _ ≤ _ := add_le_add hdiffR hvAR
    have hqpos : 0 < (h / (2 * (d : ℝ))) ^ ((d : ℝ) / 2) := by positivity
    have hqinv :
        ((h / (2 * (d : ℝ))) ^ ((d : ℝ) / 2))⁻¹ =
          C * h ^ (-(d : ℝ) / 2) := by
      dsimp [C]
      rw [← Real.rpow_neg (by positivity)]
      rw [Real.div_rpow (by positivity) (by positivity)]
      rw [Real.rpow_neg (by positivity)]
      field_simp
      have hhpow : h ^ ((d : ℝ) / 2) * h ^ (-(d : ℝ) / 2) = 1 := by
        rw [← Real.rpow_add (by positivity)]
        rw [show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring]
        simp
      have hdPow : (2 * (d : ℝ)) ^ (-(d : ℝ) / 2) *
          (2 * (d : ℝ)) ^ ((d : ℝ) / 2) = 1 := by
        rw [← Real.rpow_add (by positivity)]
        rw [show -(d : ℝ) / 2 + (d : ℝ) / 2 = 0 by ring]
        simp
      calc
        1 = (h ^ ((d : ℝ) / 2) * h ^ (-(d : ℝ) / 2)) *
            ((2 * (d : ℝ)) ^ (-(d : ℝ) / 2) *
              (2 * (d : ℝ)) ^ ((d : ℝ) / 2)) := by simp [hhpow, hdPow]
        _ = _ := by ring
    have hpoint :
        |v x| ≤
          C * h ^ (-(d : ℝ) / 2) *
              (eLpNorm v 2 (volume.restrict
                (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
                  Set (SpatialCoordinates d)))).toReal +
            Lane4.holderSeminorm alpha
              (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
                Set (SpatialCoordinates d))) v * h ^ alpha := by
      have hdiv := (le_div_iff₀ hqpos).2 hmain
      rw [div_eq_mul_inv, hqinv] at hdiv
      calc
        |v x| ≤
            ((h / (2 * (d : ℝ))) ^ ((d : ℝ) / 2) *
              (Lane4.holderSeminorm alpha
                (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
                  Set (SpatialCoordinates d))) v * h ^ alpha) +
              (eLpNorm v 2 (volume.restrict
                (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) :
                  Set (SpatialCoordinates d)))).toReal) *
              (C * h ^ (-(d : ℝ) / 2)) := hdiv
        _ = _ := by
          rw [← hqinv]
          field_simp [ne_of_gt hqpos]
          ring
    exact hpoint

end Paper
