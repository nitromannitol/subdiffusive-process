import SubdiffusiveProcess.Geometry.FaceProjection
import SubdiffusiveProcess.Geometry.AdmissibleRoot
import Mathlib.Data.Finset.Max
open Set
namespace SubdiffusiveProcess
/-- Construct one boundary activation with its literal projected-ball inclusion, or an admissible terminal root. The chosen face minimizes actual inactive-face distance; every new radius is half-triadic. -/
theorem boundary_step_or_terminal
    {d : ℕ} (x : SpatialCoordinates d)
    (hx : ∀ j : Fin d, |x j| < (1 / 2 : ℝ))
    (I P : Finset (Fin d)) (hP : ∀ j : Fin d, j ∈ P ↔ 0 ≤ x j)
    (m : ℤ) (L s : ℝ) (hL : 10 ≤ L) (hs : 0 < s) :
    let δ : Fin d → ℝ := fun j => (1 / 2 : ℝ) - |x j|
    let z : Finset (Fin d) → SpatialCoordinates d := fun J j =>
      if j ∈ J then (if j ∈ P then (1 / 2 : ℝ) else -(1 / 2 : ℝ)) else x j
    let Rstar : ℝ := (3 : ℝ) ^ m / 2
    Rstar / 24 ≤ s ∨
      (8 * s < Rstar ∧ ∀ j : Fin d, j ∉ I → 4 * L * Rstar ≤ δ j) ∨
      ∃ i : Fin d, i ∉ I ∧ (∀ j : Fin d, j ∉ I → δ i ≤ δ j) ∧
        ∃ k' : ℤ, let s' : ℝ := (3 : ℝ) ^ k' / 2
          (δ i ≤ 100 * L * s ∧ s + δ i ≤ s' ∧
            s' < 3 * (1 + 100 * L) * s ∧
            Metric.ball (z I) s ⊆ Metric.ball (z (insert i I)) s') ∨
          (∃ k : ℤ, let R : ℝ := (3 : ℝ) ^ k / 2
            8 * s < R ∧ R < Rstar ∧
            (∀ j : Fin d, j ∉ I → 4 * L * R ≤ δ j) ∧
            L * R + δ i ≤ s' ∧ s' < 39 * L * R ∧
            Metric.ball (z I) (L * R) ⊆ Metric.ball (z (insert i I)) s') := by
  classical
  dsimp only
  let δ : Fin d → ℝ := fun j => (1 / 2 : ℝ) - |x j|
  let z : Finset (Fin d) → SpatialCoordinates d := fun J j =>
    if j ∈ J then (if j ∈ P then (1 / 2 : ℝ) else -(1 / 2 : ℝ)) else x j
  let Rstar : ℝ := (3 : ℝ) ^ m / 2
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hRstarpos : 0 < Rstar := by
    exact div_pos (zpow_pos (by norm_num) m) (by norm_num)
  have hround : ∀ u : ℝ, 0 < u → ∃ k' : ℤ,
      u ≤ (3 : ℝ) ^ k' / 2 ∧ (3 : ℝ) ^ k' / 2 < 3 * u := by
    intro u hu
    have h2u : 0 < (2 : ℝ) * u := mul_pos (by norm_num) hu
    obtain ⟨k, hklo, hkhi⟩ :=
      exists_mem_Ioc_zpow h2u (show (1 : ℝ) < 3 by norm_num)
    refine ⟨k + 1, ?_, ?_⟩
    · nlinarith [hkhi]
    · rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      nlinarith
  by_cases hlarge : Rstar / 24 ≤ s
  · exact Or.inl hlarge
  right
  have hsmall : s < Rstar / 24 := lt_of_not_ge hlarge
  let inactive : Finset (Fin d) := Finset.univ \ I
  by_cases hinactive : inactive.Nonempty
  · obtain ⟨i, hiinactive, hmin⟩ := inactive.exists_min_image δ hinactive
    have hi : i ∉ I := by simpa [inactive] using hiinactive
    have hmin' : ∀ j : Fin d, j ∉ I → δ i ≤ δ j := by
      intro j hj
      exact hmin j (by simp [inactive, hj])
    by_cases hclose : δ i ≤ 100 * L * s
    · right
      refine ⟨i, hi, hmin', ?_⟩
      have hu : 0 < s + δ i := by
        have hδi : 0 < δ i := sub_pos.mpr (hx i)
        linarith
      obtain ⟨k', hk'lo, hk'hi⟩ := hround (s + δ i) hu
      refine ⟨k', Or.inl ⟨hclose, hk'lo, ?_, ?_⟩⟩
      · calc
          (3 : ℝ) ^ k' / 2 < 3 * (s + δ i) := hk'hi
          _ ≤ 3 * (1 + 100 * L) * s := by nlinarith
      · have hcover :=
          (nearestFace_projection_distance_and_cover x hx I P hP i hi).2 (2 * s)
            (mul_pos (by norm_num) hs)
        have hmono : Metric.ball
              (fun j : Fin d => if j ∈ insert i I then
                (if j ∈ P then (1 / 2 : ℝ) else -(1 / 2 : ℝ)) else x j)
              ((2 * s + 2 * ((1 / 2 : ℝ) - |x i|)) / 2) ⊆
            Metric.ball
              (fun j : Fin d => if j ∈ insert i I then
                (if j ∈ P then (1 / 2 : ℝ) else -(1 / 2 : ℝ)) else x j)
              ((3 : ℝ) ^ k' / 2) := Metric.ball_subset_ball (by dsimp [δ] at hk'lo; nlinarith)
        convert hcover.trans hmono using 1 <;> ring
    · have hfar : 100 * L * s < δ i := lt_of_not_ge hclose
      obtain ⟨k, hkm, h8, hRle, hclear, hnext⟩ :=
        exists_halfTriadic_admissible_root m L s (δ i) hL hs hsmall hfar
      by_cases hkeq : k = m
      · left
        subst k
        refine ⟨h8, ?_⟩
        intro j hj
        exact hclear.trans (hmin' j hj)
      · have hkm' : k < m := lt_of_le_of_ne hkm hkeq
        have hδlt : δ i < 12 * L * ((3 : ℝ) ^ k / 2) := hnext hkm'
        have hRpos : 0 < (3 : ℝ) ^ k / 2 :=
          div_pos (zpow_pos (by norm_num) k) (by norm_num)
        have hu : 0 < L * ((3 : ℝ) ^ k / 2) + δ i := by
          have hδi : 0 < δ i := sub_pos.mpr (hx i)
          positivity
        obtain ⟨k', hk'lo, hk'hi⟩ :=
          hround (L * ((3 : ℝ) ^ k / 2) + δ i) hu
        right
        refine ⟨i, hi, hmin', k', Or.inr ⟨k, h8, ?_, ?_, hk'lo, ?_, ?_⟩⟩
        · have hp := (zpow_lt_zpow_iff_right₀ (show (1 : ℝ) < 3 by norm_num)).2 hkm'
          nlinarith
        · intro j hj
          exact hclear.trans (hmin' j hj)
        · calc
            (3 : ℝ) ^ k' / 2 < 3 * (L * ((3 : ℝ) ^ k / 2) + δ i) := hk'hi
            _ < 39 * L * ((3 : ℝ) ^ k / 2) := by nlinarith
        · have hcover :=
            (nearestFace_projection_distance_and_cover x hx I P hP i hi).2
              (2 * (L * ((3 : ℝ) ^ k / 2))) (by positivity)
          have hmono : Metric.ball
                (fun j : Fin d => if j ∈ insert i I then
                  (if j ∈ P then (1 / 2 : ℝ) else -(1 / 2 : ℝ)) else x j)
                ((2 * (L * ((3 : ℝ) ^ k / 2)) + 2 * ((1 / 2 : ℝ) - |x i|)) / 2) ⊆
              Metric.ball
                (fun j : Fin d => if j ∈ insert i I then
                  (if j ∈ P then (1 / 2 : ℝ) else -(1 / 2 : ℝ)) else x j)
                ((3 : ℝ) ^ k' / 2) := Metric.ball_subset_ball (by dsimp [δ] at hk'lo; nlinarith)
          convert hcover.trans hmono using 1 <;> ring
  · left
    refine ⟨?_, ?_⟩
    · calc
        8 * s < 8 * (Rstar / 24) := mul_lt_mul_of_pos_left hsmall (by norm_num)
        _ = Rstar / 3 := by ring
        _ < Rstar := by nlinarith
    · intro j hj
      exfalso
      exact hinactive ⟨j, by simp [inactive, hj]⟩

end SubdiffusiveProcess
