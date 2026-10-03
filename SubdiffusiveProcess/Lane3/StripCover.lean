module

public import SubdiffusiveProcess.Lane3.Subdivision
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.Tactic

@[expose] public section

/-!
# Covering a face strip by balls of the strip width

The geometric half of Lemma `mfd:lem-strips`
(`mfd:lem-strips`, proof line 1357):
"each strip inside `Q` is covered by `O(r^{-(d-1)})` balls of radius `Cr`".

In the sup metric of `SpatialCoordinates d` the cover is explicit: pin the
`i`-th coordinate to the face and round every other coordinate to the nearest
multiple of the strip width.
-/

open Finset MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess
namespace Lane3

variable {d : ℕ}

/-- Each point of a slab lies within the strip width of the centre with its
own lattice label. -/
theorem dist_slabCoverCenter_le (z : SpatialCoordinates d) (i : Fin d)
    (c wid : ℝ) (hwid : 0 < wid) (x : SpatialCoordinates d)
    (hx : |x i - c| ≤ wid) :
    dist x (slabCoverCenter z i c wid (slabCoverLabel z i wid x)) ≤ wid := by
  rw [dist_pi_le_iff hwid.le]
  intro j
  rw [Real.dist_eq]
  by_cases hji : j = i
  · subst hji
    simpa only [slabCoverCenter, slabCoverLabel, ite_true] using hx
  · simp only [slabCoverCenter, slabCoverLabel, if_neg hji]
    have hr := abs_sub_round ((x j - z j) / wid)
    have hid : x j - (z j + ((round ((x j - z j) / wid) : ℤ) : ℝ) * wid)
        = ((x j - z j) / wid - ((round ((x j - z j) / wid) : ℤ) : ℝ)) * wid := by
      field_simp
      ring
    rw [hid, abs_mul, abs_of_pos hwid]
    nlinarith [hr, hwid]

/-- The lattice label of a point of the root cube lies in the cover index. -/
theorem slabCoverLabel_mem_slabCoverIndex (z : SpatialCoordinates d) (i : Fin d)
    (rt wid : ℝ) (hrt : 0 < rt) (hwid : 0 < wid) (x : SpatialCoordinates d)
    (hx : dist x z < rt / 2) :
    slabCoverLabel z i wid x ∈ slabCoverIndex i rt wid := by
  classical
  rw [slabCoverIndex, Fintype.mem_piFinset]
  intro j
  by_cases hji : j = i
  · simp [slabCoverLabel, hji]
  · simp only [slabCoverLabel, if_neg hji, slabCoverRange, Finset.mem_Icc]
    set y : ℝ := (x j - z j) / wid with hy
    have hxj : |x j - z j| < rt / 2 := by
      have hle : dist (x j) (z j) ≤ dist x z := dist_le_pi_dist x z j
      rw [Real.dist_eq] at hle
      linarith
    have hyabs : |y| < rt / wid := by
      rw [hy, abs_div, abs_of_pos hwid]
      rw [div_lt_div_iff_of_pos_right hwid]
      linarith
    have hceil : rt / wid ≤ ((⌈rt / wid⌉ : ℤ) : ℝ) := Int.le_ceil _
    have hround := abs_sub_round y
    have hub : ((round y : ℤ) : ℝ) ≤ ((⌈rt / wid⌉ + 1 : ℤ) : ℝ) := by
      push_cast
      rcases abs_cases y with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
        rcases abs_cases (y - ((round y : ℤ) : ℝ)) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
        linarith [hyabs, hceil, hround]
    have hlb : ((-⌈rt / wid⌉ - 1 : ℤ) : ℝ) ≤ ((round y : ℤ) : ℝ) := by
      push_cast
      rcases abs_cases y with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
        rcases abs_cases (y - ((round y : ℤ) : ℝ)) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
        linarith [hyabs, hceil, hround]
    exact ⟨Int.cast_le.mp hlb, Int.cast_le.mp hub⟩

/-- The explicit cover of a slab inside the root cube. -/
theorem coordinateSlab_inter_ball_subset (z : SpatialCoordinates d) (i : Fin d)
    (c rt wid : ℝ) (hrt : 0 < rt) (hwid : 0 < wid) :
    coordinateSlab i c wid ∩ Metric.ball z (rt / 2) ⊆
      ⋃ k ∈ slabCoverIndex i rt wid,
        Metric.ball (slabCoverCenter z i c wid k) (2 * wid) := by
  rintro x ⟨hslab, hball⟩
  rw [Set.mem_iUnion₂]
  refine ⟨slabCoverLabel z i wid x,
    slabCoverLabel_mem_slabCoverIndex z i rt wid hrt hwid x (Metric.mem_ball.mp hball), ?_⟩
  rw [Metric.mem_ball]
  have hd := dist_slabCoverCenter_le z i c wid hwid x hslab
  linarith

/-- The cover has at most `N^{d-1}` balls, `N` the one-dimensional range. -/
theorem card_slabCoverIndex_le (i : Fin d) (rt wid : ℝ) :
    (slabCoverIndex i rt wid).card ≤ (slabCoverRange rt wid).card ^ (d - 1) := by
  classical
  rw [slabCoverIndex, Fintype.card_piFinset]
  have hcard : ∀ j : Fin d,
      (if j = i then ({0} : Finset ℤ) else slabCoverRange rt wid).card =
        if j = i then 1 else (slabCoverRange rt wid).card := by
    intro j; by_cases h : j = i <;> simp [h]
  rw [Finset.prod_congr rfl (fun j _ => hcard j),
    Finset.prod_eq_prod_diff_singleton_mul (Finset.mem_univ i), if_pos rfl, mul_one]
  have hne : ∀ j ∈ (Finset.univ : Finset (Fin d)) \ {i},
      (if j = i then 1 else (slabCoverRange rt wid).card) =
        (slabCoverRange rt wid).card := by
    intro j hj
    exact if_neg (Finset.notMem_singleton.mp (Finset.mem_sdiff.mp hj).2)
  rw [Finset.prod_congr rfl hne, Finset.prod_const]
  have hc : ((Finset.univ : Finset (Fin d)) \ {i}).card = d - 1 := by
    simp [Finset.card_sdiff]
  rw [hc]


/-- The finite range of faces that can meet the root cube. -/
def faceRange (m : ℕ) : Finset ℤ := Finset.Icc (-(m : ℤ) - 2) ((m : ℤ) + 1)

theorem card_faceRange (m : ℕ) : (faceRange m).card = 2 * m + 4 := by
  rw [faceRange, Int.card_Icc]
  omega

/-- Mass of one slab inside the root cube, paper line 1357. -/
theorem coordinateSlab_mass_le (z : SpatialCoordinates d) (i : Fin d)
    (c rt wid t Kc : ℝ) (hrt : 0 < rt) (hwid : 0 < wid) (h2wid : 2 * wid ≤ 1)
    (nu : Measure (SpatialCoordinates d))
    (hgrow : ∀ (x : SpatialCoordinates d) (rad : ℝ), 0 < rad → rad ≤ 1 →
      nu (Metric.ball x rad) ≤ ENNReal.ofReal (Kc * rad ^ t)) :
    nu (coordinateSlab i c wid ∩ Metric.ball z (rt / 2)) ≤
      (((slabCoverRange rt wid).card ^ (d - 1) : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (Kc * (2 * wid) ^ t) := by
  classical
  calc nu (coordinateSlab i c wid ∩ Metric.ball z (rt / 2))
      ≤ nu (⋃ k ∈ slabCoverIndex i rt wid,
          Metric.ball (slabCoverCenter z i c wid k) (2 * wid)) :=
        measure_mono (coordinateSlab_inter_ball_subset z i c rt wid hrt hwid)
    _ ≤ ∑ k ∈ slabCoverIndex i rt wid,
          nu (Metric.ball (slabCoverCenter z i c wid k) (2 * wid)) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ slabCoverIndex i rt wid, ENNReal.ofReal (Kc * (2 * wid) ^ t) :=
        Finset.sum_le_sum (fun k _ => hgrow _ _ (by linarith) h2wid)
    _ = ((slabCoverIndex i rt wid).card : ℝ≥0∞) *
          ENNReal.ofReal (Kc * (2 * wid) ^ t) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((slabCoverRange rt wid).card ^ (d - 1) : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (Kc * (2 * wid) ^ t) := by
        gcongr
        exact_mod_cast card_slabCoverIndex_le i rt wid

/-- Only the faces in `faceRange` can meet the root cube, paper line 1357. -/
theorem oddGridStrip_inter_ball_subset (z : SpatialCoordinates d) (rt wid : ℝ)
    (m : ℕ) (hrt : 0 < rt) (hwid : 0 < wid)
    (hwl : wid < rt / (2 * (m : ℝ) + 1)) :
    oddGridStrip z rt m wid ∩ Metric.ball z (rt / 2) ⊆
      ⋃ (i : Fin d), ⋃ tt ∈ faceRange m,
        (coordinateSlab i (z i + ((tt : ℝ) + 1 / 2) * (rt / (2 * (m : ℝ) + 1))) wid ∩
          Metric.ball z (rt / 2)) := by
  rintro x ⟨hstrip, hball⟩
  obtain ⟨i, tt, hit⟩ := hstrip
  have hmpos : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
  set l : ℝ := rt / (2 * (m : ℝ) + 1) with hl
  have hlpos : 0 < l := div_pos hrt hmpos
  have hlrt : (2 * (m : ℝ) + 1) * l = rt := by
    rw [hl]; field_simp
  have hxz : |x i - z i| < rt / 2 := by
    have hle : dist (x i) (z i) ≤ dist x z := dist_le_pi_dist x z i
    rw [Real.dist_eq] at hle
    have := Metric.mem_ball.mp hball
    linarith
  have hface : |((tt : ℝ) + 1 / 2) * l| < rt / 2 + l := by
    have h1 : |x i - (z i + ((tt : ℝ) + 1 / 2) * l)| ≤ wid := hit
    have hid : ((tt : ℝ) + 1 / 2) * l =
        (x i - z i) - (x i - (z i + ((tt : ℝ) + 1 / 2) * l)) := by ring
    rw [hid]
    calc |(x i - z i) - (x i - (z i + ((tt : ℝ) + 1 / 2) * l))|
        ≤ |x i - z i| + |x i - (z i + ((tt : ℝ) + 1 / 2) * l)| := abs_sub _ _
      _ < rt / 2 + l := by linarith [hwl]
  have habs : |(tt : ℝ) + 1 / 2| < (m : ℝ) + 3 / 2 := by
    rw [abs_mul, abs_of_pos hlpos] at hface
    have hkey : |(tt : ℝ) + 1 / 2| * l < ((m : ℝ) + 3 / 2) * l := by
      calc |(tt : ℝ) + 1 / 2| * l < rt / 2 + l := hface
        _ = ((2 * (m : ℝ) + 1) * l) / 2 + l := by rw [hlrt]
        _ = ((m : ℝ) + 3 / 2) * l := by ring
    exact lt_of_mul_lt_mul_right hkey hlpos.le
  have htt : tt ∈ faceRange m := by
    rw [faceRange, Finset.mem_Icc]
    rcases abs_lt.mp habs with ⟨h1, h2⟩
    constructor
    · have : (-(m : ℝ) - 2 : ℝ) ≤ (tt : ℝ) := by linarith
      exact_mod_cast this
    · have : ((tt : ℝ)) ≤ ((m : ℝ) + 1) := by linarith
      exact_mod_cast this
  exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion₂.2 ⟨tt, htt, ⟨hit, hball⟩⟩⟩


/-- The covering estimate of Lemma `mfd:lem-strips`, paper lines 1337-1364,
in the form the covering argument produces: `d` coordinate directions, at most
`2m+4` faces each, and at most `N^{d-1}` balls of radius `2·wid` per face. -/
theorem oddGridStrip_mass_le (z : SpatialCoordinates d) (rt wid t Kc : ℝ)
    (m : ℕ) (hrt : 0 < rt) (hwid : 0 < wid) (h2wid : 2 * wid ≤ 1)
    (hwl : wid < rt / (2 * (m : ℝ) + 1))
    (nu : Measure (SpatialCoordinates d))
    (hgrow : ∀ (x : SpatialCoordinates d) (rad : ℝ), 0 < rad → rad ≤ 1 →
      nu (Metric.ball x rad) ≤ ENNReal.ofReal (Kc * rad ^ t))
    (hsupp : nu (Metric.ball z (rt / 2))ᶜ = 0) :
    nu (oddGridStrip z rt m wid) ≤
      ((d * (2 * m + 4) * (slabCoverRange rt wid).card ^ (d - 1) : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (Kc * (2 * wid) ^ t) := by
  classical
  set Q : Set (SpatialCoordinates d) := Metric.ball z (rt / 2) with hQdef
  set S : Set (SpatialCoordinates d) := oddGridStrip z rt m wid with hSdef
  set B : ℝ≥0∞ := ENNReal.ofReal (Kc * (2 * wid) ^ t) with hB
  set N : ℕ := (slabCoverRange rt wid).card ^ (d - 1) with hN
  have hQm : MeasurableSet Q := Metric.isOpen_ball.measurableSet
  have hdiff : nu (S \ Q) = 0 := measure_mono_null (fun x hx => hx.2) hsupp
  have hSQ : nu S = nu (S ∩ Q) := by
    have h := measure_inter_add_diff (μ := nu) S hQm
    rw [hdiff, add_zero] at h
    exact h.symm
  have hcover := oddGridStrip_inter_ball_subset z rt wid m hrt hwid hwl
  have hstep1 : nu (S ∩ Q) ≤
      nu (⋃ i ∈ (Finset.univ : Finset (Fin d)), ⋃ tt ∈ faceRange m,
        (coordinateSlab i (z i + ((tt : ℝ) + 1 / 2) * (rt / (2 * (m : ℝ) + 1))) wid ∩ Q)) := by
    refine measure_mono (fun x hx => ?_)
    have hx' := hcover hx
    simpa [Q] using! hx'
  have hstep2 : nu (⋃ i ∈ (Finset.univ : Finset (Fin d)), ⋃ tt ∈ faceRange m,
        (coordinateSlab i (z i + ((tt : ℝ) + 1 / 2) * (rt / (2 * (m : ℝ) + 1))) wid ∩ Q)) ≤
      ∑ _i ∈ (Finset.univ : Finset (Fin d)), ((faceRange m).card : ℝ≥0∞) * ((N : ℝ≥0∞) * B) := by
    refine le_trans (measure_biUnion_finset_le _ _) (Finset.sum_le_sum (fun i _ => ?_))
    refine le_trans (measure_biUnion_finset_le _ _) ?_
    calc ∑ _tt ∈ faceRange m,
          nu (coordinateSlab i (z i + ((_tt : ℝ) + 1 / 2) * (rt / (2 * (m : ℝ) + 1))) wid ∩ Q)
        ≤ ∑ _tt ∈ faceRange m, ((N : ℝ≥0∞) * B) :=
          Finset.sum_le_sum (fun tt _ =>
            coordinateSlab_mass_le z i _ rt wid t Kc hrt hwid h2wid nu hgrow)
      _ = ((faceRange m).card : ℝ≥0∞) * ((N : ℝ≥0∞) * B) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hstep3 : ∑ _i ∈ (Finset.univ : Finset (Fin d)),
      ((faceRange m).card : ℝ≥0∞) * ((N : ℝ≥0∞) * B) =
      ((d * (2 * m + 4) * N : ℕ) : ℝ≥0∞) * B := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin,
      card_faceRange]
    push_cast
    ring
  rw [hSQ]
  calc nu (S ∩ Q) ≤ _ := hstep1
    _ ≤ _ := hstep2
    _ = ((d * (2 * m + 4) * N : ℕ) : ℝ≥0∞) * B := hstep3


/-- The core (maximum box) bound of Lemma `mfd:lem-strips`, paper line 1345:
in the sup metric a grid cell of side `ℓ` is the ball of radius `ℓ/2`, so the
growth hypothesis applies with no extra dimensional constant. -/
theorem oddGridCell_mass_le (z : SpatialCoordinates d) {rt : ℝ} (hrt : 0 < rt)
    (m : ℕ) (nu : Measure (SpatialCoordinates d)) (Kc t : ℝ)
    (hKc : 0 ≤ Kc) (ht : 0 ≤ t)
    (hgrow : ∀ (x : SpatialCoordinates d) (rad : ℝ), 0 < rad → rad ≤ 1 →
      nu (Metric.ball x rad) ≤ ENNReal.ofReal (Kc * rad ^ t))
    (hle : rt / (2 * (m : ℝ) + 1) ≤ 1) (k : OddGridIndex d m) :
    nu (oddGridCell z rt hrt m k) ≤
      ENNReal.ofReal (Kc * (rt / (2 * (m : ℝ) + 1)) ^ t) := by
  have hmpos : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
  have hl : 0 < rt / (2 * (m : ℝ) + 1) := div_pos hrt hmpos
  rw [oddGridCell_coe]
  calc nu (Metric.ball (oddGridCenter z rt m k) (rt / (2 * (m : ℝ) + 1) / 2))
      ≤ ENNReal.ofReal (Kc * (rt / (2 * (m : ℝ) + 1) / 2) ^ t) :=
        hgrow _ _ (by linarith) (by linarith)
    _ ≤ ENNReal.ofReal (Kc * (rt / (2 * (m : ℝ) + 1)) ^ t) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by linarith) (by linarith) ht) hKc


theorem card_slabCoverRange_le (rt wid : ℝ) (hwid : 0 < wid) (h1 : 1 ≤ rt / wid) :
    (((slabCoverRange rt wid).card : ℕ) : ℝ) ≤ 7 * (rt / wid) := by
  rw [slabCoverRange, Int.card_Icc]
  have hq : (0 : ℝ) < rt / wid := by linarith
  have hceil : ((⌈rt / wid⌉ : ℤ) : ℝ) ≤ rt / wid + 1 := by
    have h := Int.ceil_lt_add_one (rt / wid)
    linarith
  have hcnn : (0 : ℤ) ≤ ⌈rt / wid⌉ := Int.ceil_nonneg (by linarith)
  have heq : ((⌈rt / wid⌉ + 1) + 1 - (-⌈rt / wid⌉ - 1) : ℤ) = 2 * ⌈rt / wid⌉ + 3 := by
    ring
  rw [heq]
  have hnn : (0 : ℤ) ≤ 2 * ⌈rt / wid⌉ + 3 := by omega
  have hcast : (((2 * ⌈rt / wid⌉ + 3 : ℤ).toNat : ℕ) : ℝ) =
      ((2 * ⌈rt / wid⌉ + 3 : ℤ) : ℝ) := by
    have h := Int.toNat_of_nonneg hnn
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h
  rw [hcast]
  push_cast
  linarith

/-- The arithmetic conversion of the covering count into the form of
Lemma `mfd:lem-strips`, paper line 1345. -/
theorem strip_bound_convert (d : ℕ) (hd : 1 ≤ d) (t rt wid Kc Nr : ℝ) (m : ℕ)
    (hrt : 0 < rt) (hwid : 0 < wid) (hKc : 0 ≤ Kc) (ht0 : 0 ≤ t)
    (hN : Nr ≤ 7 * (rt / wid)) (hN0 : 0 ≤ Nr) :
    (d : ℝ) * (2 * (m : ℝ) + 4) * Nr ^ (d - 1) * (Kc * (2 * wid) ^ t) ≤
      (4 * (d : ℝ) * 7 ^ (d - 1) * 2 ^ t) * Kc * rt ^ (d : ℝ) *
        ((2 * (m : ℝ) + 1) / rt) * wid ^ (t - (d : ℝ) + 1) := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hcast : (((d - 1 : ℕ) : ℕ) : ℝ) = (d : ℝ) - 1 := by
    have : (1 : ℕ) ≤ d := hd
    push_cast [Nat.cast_sub this]
    ring
  have hq : (0 : ℝ) < rt / wid := div_pos hrt hwid
  have h2w : (2 * wid) ^ t = 2 ^ t * wid ^ t :=
    Real.mul_rpow (by norm_num) hwid.le
  have hNp : Nr ^ (d - 1) ≤ (7 * (rt / wid)) ^ (d - 1) :=
    pow_le_pow_left₀ hN0 hN (d - 1)
  have hsplit : (7 * (rt / wid)) ^ (d - 1) =
      (7 : ℝ) ^ (d - 1) * (rt ^ ((d : ℝ) - 1) / wid ^ ((d : ℝ) - 1)) := by
    rw [mul_pow, ← Real.rpow_natCast (rt / wid) (d - 1), hcast,
      Real.div_rpow hrt.le hwid.le]
  have hrtsplit : rt ^ (d : ℝ) * ((2 * (m : ℝ) + 1) / rt) =
      (2 * (m : ℝ) + 1) * rt ^ ((d : ℝ) - 1) := by
    rw [Real.rpow_sub hrt, Real.rpow_one]
    field_simp
  have hwsplit : wid ^ (t - (d : ℝ) + 1) = wid ^ t / wid ^ ((d : ℝ) - 1) := by
    rw [← Real.rpow_sub hwid]
    congr 1
    ring
  have hrtp : (0 : ℝ) < rt ^ ((d : ℝ) - 1) := Real.rpow_pos_of_pos hrt _
  have hwp : (0 : ℝ) < wid ^ ((d : ℝ) - 1) := Real.rpow_pos_of_pos hwid _
  have hwt : (0 : ℝ) ≤ wid ^ t := (Real.rpow_pos_of_pos hwid t).le
  have h2t : (0 : ℝ) < 2 ^ t := Real.rpow_pos_of_pos (by norm_num) t
  have h7 : (0 : ℝ) < (7 : ℝ) ^ (d - 1) := by positivity
  have hm4 : 2 * (m : ℝ) + 4 ≤ 4 * (2 * (m : ℝ) + 1) := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  rw [h2w]
  have hrtd : rt ^ (d : ℝ) = rt ^ ((d : ℝ) - 1) * rt := by
    rw [Real.rpow_sub hrt, Real.rpow_one]
    field_simp
  have hkey : (d : ℝ) * (2 * (m : ℝ) + 4) * Nr ^ (d - 1) * (Kc * (2 ^ t * wid ^ t)) ≤
      (d : ℝ) * (4 * (2 * (m : ℝ) + 1)) *
        ((7 : ℝ) ^ (d - 1) * (rt ^ ((d : ℝ) - 1) / wid ^ ((d : ℝ) - 1))) *
        (Kc * (2 ^ t * wid ^ t)) := by
    have hmono1 : (d : ℝ) * (2 * (m : ℝ) + 4) ≤ (d : ℝ) * (4 * (2 * (m : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hm4 (by linarith)
    have hmono2 : Nr ^ (d - 1) ≤
        (7 : ℝ) ^ (d - 1) * (rt ^ ((d : ℝ) - 1) / wid ^ ((d : ℝ) - 1)) := by
      rw [← hsplit]; exact hNp
    have hnn1 : (0 : ℝ) ≤ (d : ℝ) * (2 * (m : ℝ) + 4) := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      positivity
    have hnn2 : (0 : ℝ) ≤ Kc * (2 ^ t * wid ^ t) := by positivity
    have hnn3 : (0 : ℝ) ≤ (7 : ℝ) ^ (d - 1) *
        (rt ^ ((d : ℝ) - 1) / wid ^ ((d : ℝ) - 1)) := by positivity
    have := mul_le_mul hmono1 hmono2 (pow_nonneg hN0 _) (by linarith)
    exact mul_le_mul_of_nonneg_right this hnn2
  have hRHS : (4 * (d : ℝ) * 7 ^ (d - 1) * 2 ^ t) * Kc * rt ^ (d : ℝ) *
      ((2 * (m : ℝ) + 1) / rt) * wid ^ (t - (d : ℝ) + 1)
      = (d : ℝ) * (4 * (2 * (m : ℝ) + 1)) *
        ((7 : ℝ) ^ (d - 1) * (rt ^ ((d : ℝ) - 1) / wid ^ ((d : ℝ) - 1))) *
        (Kc * (2 ^ t * wid ^ t)) := by
    rw [hrtd, hwsplit]
    field_simp
  rw [hRHS]
  exact hkey


/-- **Lemma `mfd:lem-strips`**, paper lines 1337-1364 (proposed statement
L3-B7).  `Cd = 4 d 7^{d-1} 2^t` depends on `d` and `t` only and is fixed
before the measure, the grid and the strip width. -/
theorem strip_and_core_masses (d : ℕ) (hd : 1 ≤ d) (t : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t ≤ (d : ℝ)) :
    ∃ Cd : ℝ, 0 < Cd ∧
      ∀ (z : SpatialCoordinates d) (rt : ℝ) (hrt : 0 < rt) (m : ℕ)
        (nu : Measure (SpatialCoordinates d)) (Kc : ℝ),
        0 ≤ Kc →
        (∀ (x : SpatialCoordinates d) (rad : ℝ), 0 < rad → rad ≤ 1 →
          nu (Metric.ball x rad) ≤ ENNReal.ofReal (Kc * rad ^ t)) →
        nu ((centeredCube z rt hrt : Set (SpatialCoordinates d))ᶜ) = 0 →
        rt / (2 * (m : ℝ) + 1) ≤ 1 →
        (∀ wid : ℝ, 0 < wid → 2 * wid ≤ 1 → wid < rt / (2 * (m : ℝ) + 1) →
          nu (oddGridStrip z rt m wid) ≤
            ENNReal.ofReal (Cd * Kc * rt ^ (d : ℝ) *
              ((2 * (m : ℝ) + 1) / rt) * wid ^ (t - (d : ℝ) + 1))) ∧
        (∀ k : OddGridIndex d m,
          nu (oddGridCell z rt hrt m k) ≤
            ENNReal.ofReal (Kc * (rt / (2 * (m : ℝ) + 1)) ^ t)) := by
  classical
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have ht0 : (0 : ℝ) ≤ t := by linarith
  refine ⟨4 * (d : ℝ) * 7 ^ (d - 1) * 2 ^ t, by positivity, ?_⟩
  intro z rt hrt m nu Kc hKc hgrow hsupp hle
  have hmpos : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
  constructor
  · intro wid hwid h2wid hwl
    have hwrt : wid < rt := by
      have hlrt : rt / (2 * (m : ℝ) + 1) ≤ rt := by
        rw [div_le_iff₀ hmpos]
        nlinarith [hrt.le, Nat.cast_nonneg (α := ℝ) m]
      linarith
    have hq : (1 : ℝ) ≤ rt / wid := by
      rw [le_div_iff₀ hwid]
      linarith
    have hmass := oddGridStrip_mass_le z rt wid t Kc m hrt hwid h2wid hwl nu hgrow
      (by simpa using! hsupp)
    refine hmass.trans ?_
    have hbase : (0 : ℝ) ≤ Kc * (2 * wid) ^ t := by
      have : (0 : ℝ) < (2 * wid) ^ t := Real.rpow_pos_of_pos (by linarith) t
      positivity
    have hcast : (((d * (2 * m + 4) *
        (slabCoverRange rt wid).card ^ (d - 1) : ℕ) : ℝ≥0∞)) =
        ENNReal.ofReal ((d : ℝ) * (2 * (m : ℝ) + 4) *
          ((slabCoverRange rt wid).card : ℝ) ^ (d - 1)) := by
      rw [← ENNReal.ofReal_natCast]
      congr 1
      push_cast
      ring
    rw [hcast, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    exact strip_bound_convert d hd t rt wid Kc _ m hrt hwid hKc ht0
      (card_slabCoverRange_le rt wid hwid hq) (by positivity)
  · intro k
    exact oddGridCell_mass_le z hrt m nu Kc t hKc ht0 hgrow hle k

end Lane3
end SubdiffusiveProcess
