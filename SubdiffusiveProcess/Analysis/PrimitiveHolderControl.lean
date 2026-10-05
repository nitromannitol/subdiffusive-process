module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.EllipticRegularity.Numeric

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
noncomputable section
namespace SubdiffusiveProcess.Analysis

/-- The logarithmic modulus gives whole-cube pointwise control and a bounded
set of Hölder quotients, so its real supremum represents a finite seminorm. -/
theorem primitiveHolderControl :
  ∀ (d : ℕ), 2 ≤ d →
  ∀ (C_log : ℝ), 0 < C_log →
  ∃ C_holder C_cube : ℝ, 0 < C_holder ∧ 0 < C_cube ∧
  ∀ (R : ℝ) (hR : 0 < R) (z : SpatialCoordinates d)
    (Kf : ℝ) (g : SpatialCoordinates d → Fin d → ℝ), 0 ≤ Kf →
    (∀ x y : SpatialCoordinates d,
      Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ R →
      Real.sqrt (∑ i : Fin d, (g x i - g y i) ^ 2) ≤
        C_log * Kf * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) *
          (1 + Real.log (R / Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)))) →
    (∀ x y : SpatialCoordinates d,
      Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ R →
      C_log * Kf * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) *
          (1 + Real.log (R / Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ≤
        C_holder * Real.sqrt R * Kf *
          Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ∧
      Real.sqrt (∑ i : Fin d, (g x i - g y i) ^ 2) ≤
        C_holder * Real.sqrt R * Kf *
          Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ∧
    (∀ x ∈ (closedCube z R hR : Set (SpatialCoordinates d)),
          ∀ y ∈ (closedCube z R hR : Set (SpatialCoordinates d)),
            Real.sqrt (∑ i : Fin d, (g x i - g y i) ^ 2) ≤
              C_cube * Real.sqrt R * Kf *
                Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ∧
        BddAbove {v : ℝ | ∃ x ∈ (closedCube z R hR : Set (SpatialCoordinates d)),
          ∃ y ∈ (closedCube z R hR : Set (SpatialCoordinates d)), x ≠ y ∧
            v = Real.sqrt (∑ i : Fin d, (g x i - g y i) ^ 2) /
              Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))} ∧
        halfHolderSeminorm (closedCube z R hR : Set (SpatialCoordinates d)) g ≤
      C_cube * Real.sqrt R * Kf := by
  intro d hd C_log hC
  refine ⟨2 * C_log, 2 * C_log * (Real.sqrt d * d + 2), by positivity, by positivity, ?_⟩
  intro R hR z Kf g hKf hmod
  have key : ∀ (t : ℝ), 0 ≤ t → t ≤ R →
      C_log * Kf * t * (1 + Real.log (R / t)) ≤
        (2 * C_log) * Real.sqrt R * Kf * Real.sqrt t := by
    intro t ht0 htle
    rcases eq_or_lt_of_le ht0 with heq | htpos
    · subst heq
      simp
    · have hn := newtonian_holder_step htpos htle
      have hCK : 0 ≤ C_log * Kf := mul_nonneg hC.le hKf
      have h1 := mul_le_mul_of_nonneg_left hn hCK
      calc C_log * Kf * t * (1 + Real.log (R / t))
          = C_log * Kf * (t * (1 + Real.log (R / t))) := by ring
        _ ≤ C_log * Kf * (2 * Real.sqrt R * Real.sqrt t) := h1
        _ = (2 * C_log) * Real.sqrt R * Kf * Real.sqrt t := by ring
  constructor
  · intro x y hxy
    have h0 : 0 ≤ Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := Real.sqrt_nonneg _
    exact ⟨key _ h0 hxy, le_trans (hmod x y hxy) (key _ h0 hxy)⟩
  · have hquot : ∀ v : ℝ,
        v ∈ {v : ℝ | ∃ x ∈ (closedCube z R hR : Set (SpatialCoordinates d)),
          ∃ y ∈ (closedCube z R hR : Set (SpatialCoordinates d)), x ≠ y ∧
            v = Real.sqrt (∑ i : Fin d, (g x i - g y i) ^ 2) /
              Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))} →
        v ≤ (2 * C_log * (Real.sqrt d * d + 2)) * Real.sqrt R * Kf := by
      rintro v ⟨x, hx, y, hy, hxy_ne, hv⟩
      rw [hv]
      have hxd : dist x z ≤ R / 2 := hx
      have hyz : dist y z ≤ R / 2 := hy
      have hEpos : 0 < ∑ j : Fin d, (x j - y j) ^ 2 := by
        obtain ⟨j, hj⟩ := not_forall.mp (mt funext hxy_ne)
        exact Finset.sum_pos' (fun i _ => sq_nonneg _)
          ⟨j, Finset.mem_univ j, sq_pos_of_ne_zero (sub_ne_zero.mpr hj)⟩
      have hdenpos : 0 < Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) :=
        Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hEpos)
      rw [div_le_iff₀ hdenpos]
      have hKfR : (0 : ℝ) ≤ Real.sqrt R * Kf :=
        mul_nonneg (Real.sqrt_nonneg R) hKf
      rcases le_or_gt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) R with hle | hgt
      · have hm := hmod x y hle
        have hk := key _ (Real.sqrt_nonneg _) hle
        have h2 : (2 * C_log) ≤ 2 * C_log * (Real.sqrt d * d + 2) := by
          have hy1 : (1 : ℝ) ≤ Real.sqrt d * d + 2 := by
            have h0 : (0 : ℝ) ≤ Real.sqrt d * d :=
              mul_nonneg (Real.sqrt_nonneg d) (Nat.cast_nonneg d)
            linarith
          have h0 : (0 : ℝ) ≤ 2 * C_log := by linarith
          simpa using mul_le_mul_of_nonneg_left hy1 h0
        refine le_trans (le_trans hm hk) ?_
        have h4 : (2 * C_log) * Real.sqrt R * Kf *
                Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))
            ≤ (2 * C_log * (Real.sqrt d * d + 2)) * Real.sqrt R * Kf *
                Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) := by
          calc (2 * C_log) * Real.sqrt R * Kf *
                  Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))
              = ((2 * C_log) * (Real.sqrt R * Kf)) *
                  Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) := by ring
            _ ≤ (2 * C_log * (Real.sqrt d * d + 2) *
                  (Real.sqrt R * Kf)) *
                  Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right h2 hKfR)
                  (Real.sqrt_nonneg (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)))
            _ = (2 * C_log * (Real.sqrt d * d + 2)) * Real.sqrt R * Kf *
                  Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) := by ring
        exact h4
      · have hRle : R ≤ Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := le_of_lt hgt
        have hzy : dist z y ≤ R / 2 := by rw [dist_comm]; exact hyz
        have hdistxy : dist x y ≤ R := by
          calc dist x y ≤ dist x z + dist z y := dist_triangle x z y
            _ ≤ R / 2 + R / 2 := add_le_add hxd hzy
            _ = R := by ring
        have hcoord : ∀ i : Fin d, |x i - y i| ≤ R := by
          intro i
          have h := (dist_pi_le_iff hR.le).mp hdistxy i
          rwa [Real.dist_eq] at h
        let q : ℕ → SpatialCoordinates d :=
          fun m i => if (i : ℕ) < m then y i else x i
        have hq : ∀ (m : ℕ) (i : Fin d),
            q m i = if (i : ℕ) < m then y i else x i := fun m i => rfl
        have hq0 : q 0 = x := by funext i; simp [hq]
        have hqd : q d = y := by funext i; simp [hq, i.isLt]
        have htel : ∀ i : Fin d,
            g x i - g y i = ∑ m ∈ Finset.range d,
              (g (q m) i - g (q (m + 1)) i) := by
          intro i
          have h := Finset.sum_range_sub' (fun m => g (q m) i) d
          rw [hq0, hqd] at h
          exact h.symm
        let B : ℝ := 2 * C_log * Real.sqrt R * Kf * Real.sqrt R
        have hpiece : ∀ m ∈ Finset.range d,
            Real.sqrt (∑ i : Fin d, (q m i - q (m + 1) i) ^ 2) ≤ R := by
          intro m hm
          let im : Fin d := ⟨m, Finset.mem_range.mp hm⟩
          have hqa : q m im = x im := by simp [im, hq]
          have hqb : q (m + 1) im = y im := by simp [im, hq]
          have hsum : ∑ i : Fin d, (q m i - q (m + 1) i) ^ 2
              = (q m im - q (m + 1) im) ^ 2 := by
            refine Finset.sum_eq_single im ?_ ?_
            · intro i _ hi
              have hne : (i : ℕ) ≠ m := fun hc => hi (Fin.ext hc)
              by_cases hlt : (i : ℕ) < m
              · have h1 : q m i = y i := by simp [hq, hlt]
                have h2 : q (m + 1) i = y i := by
                  have hi1 : (i : ℕ) < m + 1 := by omega
                  simp [hq, hi1]
                rw [h1, h2, sub_self]
                ring
              · have h1 : q m i = x i := by simp [hq, hlt]
                have h2 : q (m + 1) i = x i := by
                  have hi1 : m + 1 ≤ (i : ℕ) := by omega
                  simp [hq, not_lt.mpr hi1]
                rw [h1, h2, sub_self]
                ring
            · intro hmem
              exact absurd (Finset.mem_univ _) hmem
          rw [hsum, hqa, hqb, Real.sqrt_sq_eq_abs]
          exact hcoord im
        have hstep : ∀ m ∈ Finset.range d,
            Real.sqrt (∑ i : Fin d, (g (q m) i - g (q (m + 1)) i) ^ 2) ≤ B := by
          intro m hm
          have hp := hpiece m hm
          have hm1 := hmod (q m) (q (m + 1)) hp
          have hm2 := key _ (Real.sqrt_nonneg _) hp
          have h3 : (2 * C_log) * Real.sqrt R * Kf *
                Real.sqrt (Real.sqrt (∑ i : Fin d,
                  (q m i - q (m + 1) i) ^ 2)) ≤
              (2 * C_log) * Real.sqrt R * Kf * Real.sqrt R :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hp) (by positivity)
          exact le_trans (le_trans hm1 hm2) h3
        have hcoordbound : ∀ i : Fin d, |g x i - g y i| ≤ (d : ℝ) * B := by
          intro i
          rw [htel i]
          calc |∑ m ∈ Finset.range d, (g (q m) i - g (q (m + 1)) i)|
              ≤ ∑ m ∈ Finset.range d, |g (q m) i - g (q (m + 1)) i| :=
                Finset.abs_sum_le_sum_abs
                  (fun m => g (q m) i - g (q (m + 1)) i) (Finset.range d)
            _ ≤ ∑ m ∈ Finset.range d, Real.sqrt (∑ l : Fin d,
                (g (q m) l - g (q (m + 1)) l) ^ 2) := by
                apply Finset.sum_le_sum
                intro m _
                calc |g (q m) i - g (q (m + 1)) i|
                    = Real.sqrt ((g (q m) i - g (q (m + 1)) i) ^ 2) :=
                      (Real.sqrt_sq_eq_abs _).symm
                  _ ≤ Real.sqrt (∑ l : Fin d,
                      (g (q m) l - g (q (m + 1)) l) ^ 2) :=
                      Real.sqrt_le_sqrt
                        (Finset.single_le_sum
                          (fun l _ => sq_nonneg
                            (g (q m) l - g (q (m + 1)) l))
                          (Finset.mem_univ i))
            _ ≤ ∑ m ∈ Finset.range d, B := by
                apply Finset.sum_le_sum
                intro m hm
                exact hstep m hm
            _ = (d : ℝ) * B := by
                simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hdB : (0 : ℝ) ≤ (d : ℝ) * B := by positivity
        have hsum2 : ∑ i : Fin d, (g x i - g y i) ^ 2 ≤
            ∑ i : Fin d, ((d : ℝ) * B) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          exact sq_le_sq.mpr (by rw [abs_of_nonneg hdB]; exact hcoordbound i)
        have hsum3 : ∑ i : Fin d, ((d : ℝ) * B) ^ 2 =
            (d : ℝ) * ((d : ℝ) * B) ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hfinal : Real.sqrt (∑ i : Fin d, (g x i - g y i) ^ 2) ≤
            Real.sqrt d * ((d : ℝ) * B) := by
          calc Real.sqrt (∑ i : Fin d, (g x i - g y i) ^ 2)
              ≤ Real.sqrt (∑ i : Fin d, ((d : ℝ) * B) ^ 2) :=
                Real.sqrt_le_sqrt hsum2
            _ = Real.sqrt ((d : ℝ) * ((d : ℝ) * B) ^ 2) := by rw [hsum3]
            _ = Real.sqrt d * Real.sqrt (((d : ℝ) * B) ^ 2) := by
                rw [Real.sqrt_mul (show (0 : ℝ) ≤ (d : ℝ) by positivity)
                  (((d : ℝ) * B) ^ 2)]
            _ = Real.sqrt d * ((d : ℝ) * B) := by rw [Real.sqrt_sq hdB]
        have hmain : Real.sqrt d * ((d : ℝ) * B) ≤
            2 * C_log * (Real.sqrt d * d + 2) * Real.sqrt R * Kf *
              Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) := by
          have h1 : Real.sqrt R ≤
              Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) :=
            Real.sqrt_le_sqrt hRle
          have hstep1 : (Real.sqrt d * d) * Real.sqrt R ≤
              (Real.sqrt d * d + 2) *
                Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) :=
            mul_le_mul (by linarith) h1 (Real.sqrt_nonneg R) (by positivity)
          have hstep2 : (2 * C_log * Kf) * ((Real.sqrt d * d) * Real.sqrt R) ≤
              (2 * C_log * Kf) * ((Real.sqrt d * d + 2) *
                Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) :=
            mul_le_mul_of_nonneg_left hstep1 (by positivity)
          have h3 := mul_le_mul_of_nonneg_right hstep2 (Real.sqrt_nonneg R)
          calc Real.sqrt d * ((d : ℝ) * B)
              = (2 * C_log * Kf) * ((Real.sqrt d * d) * Real.sqrt R) *
                  Real.sqrt R := by
                rw [show B = 2 * C_log * Real.sqrt R * Kf * Real.sqrt R from rfl]
                ring
            _ ≤ (2 * C_log * Kf) * ((Real.sqrt d * d + 2) *
                  Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) *
                  Real.sqrt R := h3
            _ = 2 * C_log * (Real.sqrt d * d + 2) * Real.sqrt R * Kf *
                  Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) := by ring
        exact le_trans hfinal hmain
    have hpoint : ∀ x ∈ (closedCube z R hR : Set (SpatialCoordinates d)),
        ∀ y ∈ (closedCube z R hR : Set (SpatialCoordinates d)),
          Real.sqrt (∑ i : Fin d, (g x i - g y i) ^ 2) ≤
            (2 * C_log * (Real.sqrt d * d + 2)) * Real.sqrt R * Kf *
              Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) := by
      intro x hx y hy
      by_cases hxy : x = y
      · subst y
        simp
      · have hEpos : 0 < ∑ j : Fin d, (x j - y j) ^ 2 := by
          obtain ⟨j, hj⟩ := not_forall.mp (mt funext hxy)
          exact Finset.sum_pos' (fun i _ => sq_nonneg _)
            ⟨j, Finset.mem_univ j, sq_pos_of_ne_zero (sub_ne_zero.mpr hj)⟩
        have hdenpos : 0 < Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) :=
          Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hEpos)
        exact (div_le_iff₀ hdenpos).mp
          (hquot _ ⟨x, hx, y, hy, hxy, rfl⟩)
    refine ⟨hpoint, ⟨_, hquot⟩, ?_⟩
    unfold halfHolderSeminorm
    exact Real.sSup_le hquot (by positivity)

end SubdiffusiveProcess.Analysis
