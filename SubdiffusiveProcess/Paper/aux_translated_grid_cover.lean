import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Lane3.StripCover
import SubdiffusiveProcess.Lane1.TriadicGrid
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal BigOperators

noncomputable section
namespace Paper

open SubdiffusiveProcess.Lane3

lemma aux_translated_grid_cover_strip_small
    (d : ℕ) (hd : 1 ≤ d) (Cc : ℝ) (hCc : 0 < Cc)
    (t : ℝ) (htlo : (d : ℝ) - 1 < t) (htup : t ≤ (d : ℝ))
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (a : Fin d → ℝ) (ell r : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (hr : 0 < r) (hrel : Cc * r < ell) (hsmall : 3 * (Cc * r) ≤ 1) :
    ∃ nStrip : ℕ,
      ∃ stripCenters : Fin nStrip → SpatialCoordinates d,
        ∃ stripRadii : Fin nStrip → ℝ,
          ((centeredCube z R hR : Set (SpatialCoordinates d)) ∩
            {x | ∃ i : Fin d, ∃ j : ℤ,
              |x i - (a i + (j : ℝ) * ell)| ≤ Cc * r}) ⊆
            ⋃ j : Fin nStrip, Metric.ball (stripCenters j) (stripRadii j) ∧
          (∀ j : Fin nStrip,
            stripCenters j ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
              0 < stripRadii j ∧ stripRadii j ≤ 1) ∧
          (∑ j : Fin nStrip, (stripRadii j) ^ t) ≤
            200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d * (max 1 R) ^ d * ell⁻¹ *
              r ^ (t - (d : ℝ) + 1) := by
  classical
  let w : ℝ := Cc * r
  let A : ℝ := R / (2 * ell)
  let M : ℤ := ⌈A⌉ + 2
  let j0 : Fin d → ℤ := fun i => ⌊(z i - a i) / ell⌋
  let J : Fin d → Type := fun i => {j : ℤ // j ∈ Finset.Icc (j0 i - M) (j0 i + M)}
  let K : Fin d → Type := fun i => {k : Fin d → ℤ // k ∈ slabCoverIndex i R w}
  let I : Type := Σ i : Fin d, J i × K i
  let n : ℕ := Fintype.card I
  let e : I ≃ Fin n := Fintype.equivFin I
  let raw : I → SpatialCoordinates d := fun q =>
    slabCoverCenter z q.1 (a q.1 + (q.2.1 : ℝ) * ell) w q.2.2.1
  let centersI : I → SpatialCoordinates d := fun q =>
    if h : ((centeredCube z R hR : Set (SpatialCoordinates d)) ∩
        Metric.ball (raw q) (2 * w)).Nonempty then Classical.choose h else z
  let rad : ℝ := 3 * w
  have hw : 0 < w := by dsimp [w]; positivity
  have hw1 : rad ≤ 1 := by dsimp [rad]; exact hsmall
  have hJmem : ∀ (x : SpatialCoordinates d),
      x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) →
      ∀ i : Fin d, ∀ j : ℤ,
        |x i - (a i + (j : ℝ) * ell)| ≤ w →
          j ∈ Finset.Icc (j0 i - M) (j0 i + M) := by
    intro x hx i j hstrip
    have hdist : dist (x i) (z i) ≤ dist x z := dist_le_pi_dist x z i
    have hxz : dist x z < R / 2 := Metric.mem_ball.mp hx
    rw [Real.dist_eq] at hdist
    have habs : |x i - z i| < R / 2 := lt_of_le_of_lt hdist hxz
    have hleft : -(R / 2) < x i - z i := (abs_lt.mp habs).1
    have hright : x i - z i < R / 2 := (abs_lt.mp habs).2
    have hstrip1 : -(Cc * r) ≤ x i - (a i + (j : ℝ) * ell) := (abs_le.mp hstrip).1
    have hstrip2 : x i - (a i + (j : ℝ) * ell) ≤ Cc * r := (abs_le.mp hstrip).2
    have hApos : 0 < A := by dsimp [A]; positivity
    have hdiffup : (j : ℝ) * ell - (z i - a i) < R / 2 + ell := by
      linarith [hstrip1, hright, hrel]
    have hdifflo : (z i - a i) - (j : ℝ) * ell < R / 2 + ell := by
      linarith [hstrip2, hleft, hrel]
    have hdivup' : ((j : ℝ) * ell - (z i - a i)) / ell < A + 1 := by
      apply (div_lt_iff₀ hell).2
      dsimp [A]
      field_simp
      linarith
    have hdivup : (j : ℝ) - (z i - a i) / ell < A + 1 := by
      calc
        (j : ℝ) - (z i - a i) / ell =
            ((j : ℝ) * ell - (z i - a i)) / ell := by field_simp
        _ < A + 1 := hdivup'
    have hdivlo' : ((z i - a i) - (j : ℝ) * ell) / ell < A + 1 := by
      apply (div_lt_iff₀ hell).2
      dsimp [A]
      field_simp
      linarith
    have hdivlo : (z i - a i) / ell - (j : ℝ) < A + 1 := by
      calc
        (z i - a i) / ell - (j : ℝ) =
            ((z i - a i) - (j : ℝ) * ell) / ell := by field_simp
        _ < A + 1 := hdivlo'
    have hj0 : (j0 i : ℝ) ≤ (z i - a i) / ell := Int.floor_le _
    have hfloor : (z i - a i) / ell < (j0 i : ℝ) + 1 := Int.lt_floor_add_one _
    have hjlow : (j : ℝ) - (j0 i : ℝ) ≥ -(A + 2) := by linarith
    have hjup : (j : ℝ) - (j0 i : ℝ) ≤ A + 2 := by linarith
    rw [Finset.mem_Icc]
    dsimp [M]
    have hceil : A ≤ (⌈A⌉ : ℤ) := Int.le_ceil A
    constructor
    · have hreal : ((j0 i - (⌈A⌉ + 2 : ℤ) : ℤ) : ℝ) ≤ (j : ℝ) := by
        push_cast
        linarith
      exact_mod_cast hreal
    · have hreal : (j : ℝ) ≤ ((j0 i + (⌈A⌉ + 2 : ℤ) : ℤ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast hreal
  refine ⟨n, fun q => centersI (e.symm q), fun _ => rad, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, j, hstrip⟩ := hx.2
    have hj : j ∈ Finset.Icc (j0 i - M) (j0 i + M) := hJmem x hx.1 i j hstrip
    let k : Fin d → ℤ := slabCoverLabel z i w x
    have hk : k ∈ slabCoverIndex i R w := by
      dsimp [k]
      exact slabCoverLabel_mem_slabCoverIndex z i R w hR hw x (Metric.mem_ball.mp hx.1)
    have hclose : dist x (slabCoverCenter z i (a i + (j : ℝ) * ell) w k) ≤ w := by
      dsimp [k]
      exact dist_slabCoverCenter_le z i (a i + (j : ℝ) * ell) w hw x hstrip
    have hball : x ∈ Metric.ball (slabCoverCenter z i
        (a i + (j : ℝ) * ell) w k) (2 * w) :=
      Metric.mem_ball.mpr (by linarith)
    let q : I := ⟨i, ⟨⟨j, hj⟩, ⟨k, hk⟩⟩⟩
    have hqball : x ∈ Metric.ball (raw q) (2 * w) := by
      simpa [raw, q] using hball
    have hqnonempty :
        ((centeredCube z R hR : Set (SpatialCoordinates d)) ∩
          Metric.ball (raw q) (2 * w)).Nonempty := ⟨x, ⟨hx.1, hqball⟩⟩
    rw [Set.mem_iUnion]
    refine ⟨e q, Metric.mem_ball.mpr ?_⟩
    dsimp [centersI]
    rw [show e.symm (e q) = q from e.symm_apply_apply q, dif_pos hqnonempty]
    have hchosen := Classical.choose_spec hqnonempty
    have hclose' : dist x (raw q) ≤ w := by simpa [raw, q] using hclose
    dsimp [rad]
    have hdist := Metric.mem_ball.mp hchosen.2
    rw [dist_comm] at hdist
    exact lt_of_le_of_lt (dist_triangle x (raw q) (Classical.choose hqnonempty))
      (by linarith [hclose', hdist])
  · intro q
    dsimp [centersI]
    by_cases h :
        ((centeredCube z R hR : Set (SpatialCoordinates d)) ∩
          Metric.ball (raw (e.symm q)) (2 * w)).Nonempty
    · rw [dif_pos h]
      exact ⟨(Classical.choose_spec h).1, by positivity, hw1⟩
    · rw [dif_neg h]
      exact ⟨Metric.mem_ball.mpr (by rw [dist_self]; linarith), by positivity, hw1⟩
  · have hcard : n = ∑ i : Fin d, Fintype.card (J i) * Fintype.card (K i) := by
      dsimp [n, I]
      rw [Fintype.card_sigma]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Fintype.card_prod]
    have hM0 : 0 ≤ M := by
      dsimp [M]
      have hA0 : 0 ≤ A := by dsimp [A]; positivity
      have hc0 : (0 : ℤ) ≤ ⌈A⌉ := Int.ceil_nonneg hA0
      omega
    have hMell : (1 : ℝ) ≤ max 1 R / ell := by
      rw [le_div_iff₀ hell]
      have hM : (1 : ℝ) ≤ max 1 R := le_max_left _ _
      nlinarith [hell1]
    have hRell : R / ell ≤ max 1 R / ell :=
      div_le_div_of_nonneg_right (le_max_right _ _) (le_of_lt hell)
    have hJcard : ∀ i : Fin d,
        (Fintype.card (J i) : ℝ) ≤ 8 * max 1 R / ell := by
      intro i
      dsimp [J]
      rw [Fintype.card_coe, Int.card_Icc]
      let B : ℤ := j0 i + M + 1 - (j0 i - M)
      have hB0 : 0 ≤ B := by
        dsimp [B]
        omega
      have hBcast : ((B.toNat : ℕ) : ℝ) = (B : ℤ) := by
        have hcast : (B.toNat : ℤ) = B := Int.toNat_of_nonneg hB0
        exact_mod_cast hcast
      change ((B.toNat : ℕ) : ℝ) ≤ _
      rw [hBcast]
      have hBform : (B : ℝ) = 2 * (M : ℝ) + 1 := by
        dsimp [B]
        push_cast
        ring
      rw [hBform]
      have hceil : ((⌈A⌉ : ℤ) : ℝ) < A + 1 := Int.ceil_lt_add_one A
      have hAs : 2 * A = R / ell := by
        dsimp [A]
        field_simp
      dsimp [M]
      push_cast
      calc
        2 * (((⌈A⌉ : ℤ) : ℝ) + 2) + 1 = 2 * ((⌈A⌉ : ℤ) : ℝ) + 5 := by ring
        _ ≤ 2 * (A + 1) + 5 := by linarith
        _ = R / ell + 7 := by rw [show 2 * (A + 1) = 2 * A + 2 by ring, hAs]; ring
        _ ≤ 8 * max 1 R / ell := by
          have h8 : (7 : ℝ) ≤ 7 * (max 1 R / ell) := by nlinarith [hMell]
          have heq : 8 * max 1 R / ell = 8 * (max 1 R / ell) := by ring
          rw [heq]
          linarith
    have hwle : w ≤ 1 := by
      dsimp [rad] at hw1
      linarith
    have hMw : (1 : ℝ) ≤ max 1 R / w := by
      rw [le_div_iff₀ hw]
      nlinarith [le_max_left (1 : ℝ) R, hwle]
    have hRw : R / w ≤ max 1 R / w :=
      div_le_div_of_nonneg_right (le_max_right _ _) (le_of_lt hw)
    have hrange : ((slabCoverRange R w).card : ℝ) ≤ 7 * max 1 R / w := by
      rw [slabCoverRange, Int.card_Icc]
      let B : ℤ := ⌈R / w⌉ + 1 + 1 - (-⌈R / w⌉ - 1)
      have hB0 : 0 ≤ B := by
        dsimp [B]
        have : (0 : ℤ) ≤ ⌈R / w⌉ := Int.ceil_nonneg (by positivity)
        omega
      have hBcast : ((B.toNat : ℕ) : ℝ) = (B : ℤ) := by
        have hcast : (B.toNat : ℤ) = B := Int.toNat_of_nonneg hB0
        exact_mod_cast hcast
      change ((B.toNat : ℕ) : ℝ) ≤ _
      rw [hBcast]
      have hceil : ((⌈R / w⌉ : ℤ) : ℝ) < R / w + 1 := Int.ceil_lt_add_one _
      have hform : (B : ℝ) = 2 * ((⌈R / w⌉ : ℤ) : ℝ) + 3 := by
        dsimp [B]
        push_cast
        ring
      rw [hform]
      have heq : 7 * max 1 R / w = 7 * (max 1 R / w) := by ring
      rw [heq]
      have h7 : (5 : ℝ) ≤ 5 * (max 1 R / w) := by nlinarith [hMw]
      linarith [hRw]
    have hKcard : ∀ i : Fin d,
        (Fintype.card (K i) : ℝ) ≤ (7 * max 1 R / w) ^ (d - 1) := by
      intro i
      dsimp [K]
      rw [Fintype.card_coe]
      have hc := card_slabCoverIndex_le i R w
      have hc' : ((slabCoverIndex i R w).card : ℝ) ≤
          ((slabCoverRange R w).card : ℝ) ^ (d - 1) := by exact_mod_cast hc
      exact le_trans hc' (by
        apply pow_le_pow_left₀ (by positivity) hrange)
    have hn : (n : ℝ) ≤
        (d : ℝ) * (8 * max 1 R / ell) * (7 * max 1 R / w) ^ (d - 1) := by
      rw [hcard, Nat.cast_sum]
      calc
        ∑ x : Fin d, (↑(Fintype.card (J x) * Fintype.card (K x)) : ℝ) ≤
            ∑ x : Fin d, (8 * max 1 R / ell) *
              (7 * max 1 R / w) ^ (d - 1) := by
                apply Finset.sum_le_sum
                intro i hi
                rw [Nat.cast_mul]
                exact mul_le_mul (hJcard i) (hKcard i) (by positivity) (by positivity)
        _ = (d : ℝ) * (8 * max 1 R / ell) *
              (7 * max 1 R / w) ^ (d - 1) := by
                rw [Finset.sum_const, nsmul_eq_mul]
                simp only [Finset.card_univ, Fintype.card_fin]
                ring
    change (∑ _ : Fin n, rad ^ t) ≤ _
    rw [Finset.sum_const, nsmul_eq_mul]
    simp only [Finset.card_univ, Fintype.card_fin]
    have hrad : 0 ≤ rad ^ t := by positivity
    have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      push_cast [Nat.cast_sub hd]
      ring
    have hident :
        ((8 * max 1 R / ell) * (7 * max 1 R / w) ^ (d - 1)) * rad ^ t =
          8 * 7 ^ (d - 1) * 3 ^ t * (max 1 R) ^ d * ell⁻¹ *
            w ^ (t - (d : ℝ) + 1) := by
      dsimp [rad]
      rw [Real.mul_rpow (by norm_num) hw.le]
      rw [div_pow, mul_pow]
      rw [← Real.rpow_natCast w (d - 1)]
      have hexp : t - (d : ℝ) + 1 = t - ((d - 1 : ℕ) : ℝ) := by rw [hcast]; ring
      rw [hexp, Real.rpow_sub hw t ((d - 1 : ℕ) : ℝ)]
      have hpowmax : (max 1 R) ^ d = (max 1 R) * (max 1 R) ^ (d - 1) := by
        calc
          (max 1 R) ^ d = (max 1 R) ^ ((d - 1) + 1) := by congr 1 <;> omega
          _ = (max 1 R) ^ (d - 1) * (max 1 R) := pow_succ _ _
          _ = (max 1 R) * (max 1 R) ^ (d - 1) := by ring
      rw [hpowmax]
      ring_nf
    have hbeta0 : 0 ≤ t - (d : ℝ) + 1 := by linarith
    have hbetad : t - (d : ℝ) + 1 ≤ (d : ℝ) := by linarith
    have hCcPow : Cc ^ (t - (d : ℝ) + 1) ≤ (Cc + 1) ^ d := by
      calc
        Cc ^ (t - (d : ℝ) + 1) ≤ (Cc + 1) ^ (t - (d : ℝ) + 1) :=
          Real.rpow_le_rpow hCc.le (by linarith) hbeta0
        _ ≤ (Cc + 1) ^ d := by
          rw [← Real.rpow_natCast (Cc + 1) d]
          apply Real.rpow_le_rpow_of_exponent_le
          · linarith
          · exact hbetad
    have hwpow : w ^ (t - (d : ℝ) + 1) =
        Cc ^ (t - (d : ℝ) + 1) * r ^ (t - (d : ℝ) + 1) := by
      dsimp [w]
      rw [Real.mul_rpow hCc.le hr.le]
    calc
      (n : ℝ) * rad ^ t ≤
          ((d : ℝ) * (8 * max 1 R / ell) *
            (7 * max 1 R / w) ^ (d - 1)) * rad ^ t :=
              mul_le_mul_of_nonneg_right hn hrad
      _ = (d : ℝ) * (8 * 7 ^ (d - 1) * 3 ^ t * (max 1 R) ^ d *
            ell⁻¹ * w ^ (t - (d : ℝ) + 1)) := by
        calc
          ((d : ℝ) * (8 * max 1 R / ell) *
              (7 * max 1 R / w) ^ (d - 1)) * rad ^ t =
              (d : ℝ) * ((8 * max 1 R / ell) *
                (7 * max 1 R / w) ^ (d - 1) * rad ^ t) := by ring
          _ = _ := by rw [hident]
      _ ≤ 200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d *
          (max 1 R) ^ d * ell⁻¹ * r ^ (t - (d : ℝ) + 1) := by
        rw [hwpow]
        have h3 : 3 ^ t ≤ (3 : ℝ) ^ d := by
          rw [← Real.rpow_natCast (3 : ℝ) d]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) htup
        have h7 : (7 : ℝ) ^ (d - 1) ≤ (7 : ℝ) ^ d := by
          exact pow_le_pow_right₀ (by norm_num) (by omega)
        have hconst : 8 * 7 ^ (d - 1) * 3 ^ t ≤ 200 * (21 : ℝ) ^ d := by
          have hprod : 7 ^ (d - 1) * 3 ^ t ≤ (7 : ℝ) ^ d * 3 ^ d := by
            exact mul_le_mul h7 h3 (by positivity) (by positivity)
          calc
            8 * 7 ^ (d - 1) * 3 ^ t = 8 * (7 ^ (d - 1) * 3 ^ t) := by ring
            _ ≤ 8 * ((7 : ℝ) ^ d * 3 ^ d) :=
              mul_le_mul_of_nonneg_left hprod (by norm_num)
            _ = 8 * (21 : ℝ) ^ d := by rw [← mul_pow]; norm_num
            _ ≤ 200 * (21 : ℝ) ^ d := by gcongr <;> norm_num
        have hconstCc :
            (8 * 7 ^ (d - 1) * 3 ^ t) * Cc ^ (t - (d : ℝ) + 1) ≤
              (200 * (21 : ℝ) ^ d) * (Cc + 1) ^ d := by
          exact mul_le_mul hconst hCcPow (by positivity) (by positivity)
        have hcommon : 0 ≤ (d : ℝ) * (max 1 R) ^ d * ell⁻¹ *
            r ^ (t - (d : ℝ) + 1) := by positivity
        calc
          (d : ℝ) * (8 * 7 ^ (d - 1) * 3 ^ t * (max 1 R) ^ d *
              ell⁻¹ * (Cc ^ (t - (d : ℝ) + 1) * r ^ (t - (d : ℝ) + 1))) =
              ((8 * 7 ^ (d - 1) * 3 ^ t) * Cc ^ (t - (d : ℝ) + 1)) *
                ((d : ℝ) * (max 1 R) ^ d * ell⁻¹ *
                  r ^ (t - (d : ℝ) + 1)) := by ring
          _ ≤ ((200 * (21 : ℝ) ^ d) * (Cc + 1) ^ d) *
                ((d : ℝ) * (max 1 R) ^ d * ell⁻¹ *
                  r ^ (t - (d : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right hconstCc hcommon
          _ = 200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d *
                (max 1 R) ^ d * ell⁻¹ * r ^ (t - (d : ℝ) + 1) := by ring

lemma aux_translated_grid_cover_grid
    (d : ℕ) (z : SpatialCoordinates d) (R s : ℝ) (hR : 0 < R)
    (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ n : ℕ, ∃ centers : Fin n → SpatialCoordinates d,
      (centeredCube z R hR : Set (SpatialCoordinates d)) ⊆
        ⋃ j : Fin n, Metric.ball (centers j) s ∧
      (∀ j : Fin n, centers j ∈ (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
      (n : ℝ) ≤ (6 * max 1 R / s) ^ d := by
  classical
  let A : ℝ := R / (2 * s)
  let L : ℤ := -⌈A⌉ - 1
  let U : ℤ := ⌈A⌉ + 1
  let I : Type := Fin d → {k : ℤ // k ∈ Finset.Icc L U}
  let n : ℕ := Fintype.card I
  let e : I ≃ Fin n := Fintype.equivFin I
  let cell : I → Set (SpatialCoordinates d) := fun k =>
    {x | ∀ i : Fin d,
      z i + (k i : ℝ) * s ≤ x i ∧
        x i < z i + ((k i : ℝ) + 1) * s}
  let centersI : I → SpatialCoordinates d := fun k =>
    if h : ((centeredCube z R hR : Set (SpatialCoordinates d)) ∩ cell k).Nonempty then
      Classical.choose h
    else z
  refine ⟨n, fun j => centersI (e.symm j), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨k, hk⟩ : ∃ k : I, x ∈ cell k := by
      have hfloor_mem : ∀ i : Fin d,
          ⌊(x i - z i) / s⌋ ∈ Finset.Icc L U := by
        intro i
        have hdist : dist (x i) (z i) ≤ dist x z := dist_le_pi_dist x z i
        have hxz : dist x z < R / 2 := Metric.mem_ball.mp hx
        rw [Real.dist_eq] at hdist
        have habs : |x i - z i| < R / 2 := lt_of_le_of_lt hdist hxz
        have hleft : -(R / 2) < x i - z i := (abs_lt.mp habs).1
        have hright : x i - z i < R / 2 := (abs_lt.mp habs).2
        have hfloorlow := Int.lt_floor_add_one ((x i - z i) / s)
        have hfloorup := Int.floor_le ((x i - z i) / s)
        have hceil := Int.le_ceil A
        rw [Finset.mem_Icc]
        constructor
        · dsimp [L]
          have hdiv : -A < (x i - z i) / s := by
            dsimp [A]
            apply (lt_div_iff₀ hs).2
            field_simp
            linarith
          have hreal : ((-⌈A⌉ - 1 : ℤ) : ℝ) ≤
              (⌊(x i - z i) / s⌋ : ℝ) := by
            push_cast
            linarith
          exact_mod_cast hreal
        · dsimp [U]
          have hdiv : (x i - z i) / s < A := by
            dsimp [A]
            apply (div_lt_iff₀ hs).2
            field_simp
            linarith
          have hreal : (⌊(x i - z i) / s⌋ : ℝ) ≤
              ((⌈A⌉ + 1 : ℤ) : ℝ) := by
            push_cast
            linarith
          exact_mod_cast hreal
      let k : I := fun i =>
        ⟨⌊(x i - z i) / s⌋, hfloor_mem i⟩
      refine ⟨k, ?_⟩
      intro i
      dsimp [cell, k]
      have hfloorlow := Int.lt_floor_add_one ((x i - z i) / s)
      have hfloorup := Int.floor_le ((x i - z i) / s)
      constructor
      · dsimp
        have hmul := (le_div_iff₀ hs).mp hfloorup
        linarith
      · dsimp
        have hmul := (div_lt_iff₀ hs).mp hfloorlow
        linarith
    rw [Set.mem_iUnion]
    refine ⟨e k, Metric.mem_ball.mpr ?_⟩
    have hnonempty :
        ((centeredCube z R hR : Set (SpatialCoordinates d)) ∩ cell k).Nonempty :=
      ⟨x, ⟨hx, hk⟩⟩
    have hcenter := Classical.choose_spec hnonempty
    have hcoords := hcenter.2
    dsimp [centersI]
    rw [show e.symm (e k) = k from e.symm_apply_apply k]
    rw [dif_pos hnonempty]
    rw [dist_pi_lt_iff hs]
    intro i
    rw [Real.dist_eq]
    rw [abs_lt]
    constructor <;> linarith [hk i, hcoords i]
  · intro j
    dsimp [centersI]
    by_cases h :
        ((centeredCube z R hR : Set (SpatialCoordinates d)) ∩ cell (e.symm j)).Nonempty
    · rw [dif_pos h]
      exact (Classical.choose_spec h).1
    · rw [dif_neg h]
      exact Metric.mem_ball.mpr (by rw [dist_self]; linarith)
  · have hcard : n = ∏ _ : Fin d, (U + 1 - L).toNat := by
      dsimp [n, I]
      rw [Fintype.card_pi]
      apply Finset.prod_congr rfl
      intro i hi
      rw [Fintype.card_coe]
      rw [Int.card_Icc]
    rw [hcard]
    simp only [Finset.prod_const, Finset.card_univ]
    have hB0 : 0 ≤ U + 1 - L := by
      have hA0 : 0 ≤ A := by dsimp [A]; positivity
      have hceil0 : (0 : ℤ) ≤ ⌈A⌉ := Int.ceil_nonneg hA0
      dsimp [U, L]
      omega
    have hBcast : (((U + 1 - L).toNat : ℕ) : ℝ) = (U + 1 - L : ℤ) := by
      have hcast : ((U + 1 - L).toNat : ℤ) = U + 1 - L :=
        Int.toNat_of_nonneg hB0
      exact_mod_cast hcast
    have hceil : (A : ℝ) ≤ (⌈A⌉ : ℤ) := Int.le_ceil A
    have hceillt : ((⌈A⌉ : ℤ) : ℝ) < A + 1 := Int.ceil_lt_add_one A
    have hbase : (((U + 1 - L).toNat : ℕ) : ℝ) ≤ 6 * max 1 R / s := by
      rw [hBcast]
      dsimp [U, L]
      push_cast
      have hM : (1 : ℝ) ≤ max 1 R := le_max_left _ _
      have hRs : R ≤ max 1 R := le_max_right _ _
      have hRdiv : R / s ≤ max 1 R / s :=
        div_le_div_of_nonneg_right hRs (le_of_lt hs)
      have hsM : 1 ≤ max 1 R / s := by
        rw [le_div_iff₀ hs]
        nlinarith
      have hAs : 2 * A = R / s := by
        dsimp [A]
        field_simp
      have hform :
          ((⌈A⌉ : ℤ) : ℝ) + 1 + 1 - (-((⌈A⌉ : ℤ) : ℝ) - 1) =
            2 * ((⌈A⌉ : ℤ) : ℝ) + 3 := by ring
      rw [hform]
      calc
        2 * ((⌈A⌉ : ℤ) : ℝ) + 3 ≤ 2 * (A + 1) + 3 :=
          le_of_lt (by linarith)
        _ = R / s + 5 := by
          rw [show 2 * (A + 1) = 2 * A + 2 by ring, hAs]
          ring
        _ ≤ 6 * max 1 R / s := by
          have h5 : (5 : ℝ) ≤ 5 * (max 1 R / s) := by nlinarith [hsM]
          have heq : 6 * max 1 R / s = 6 * (max 1 R / s) := by ring
          rw [heq]
          linarith
    rw [Nat.cast_pow]
    simpa only [Fintype.card_fin] using
      (pow_le_pow_left₀ (by positivity) hbase d)

lemma aux_grid_cover_key_bound (d : ℕ) (y r e : ℝ) (hy : 0 < y)
    (hyr : 1 < y * r) (he0 : 0 < e) (hed : e ≤ (d : ℝ)) :
    1 ≤ max 1 (y ^ d) * r ^ e := by
  have hyr' : (1 : ℝ) < r * y := by rw [mul_comm]; exact hyr
  have hr : 0 < r := by
    have h : 1 / y < r := (div_lt_iff₀ hy).mpr hyr'
    have h1 : 0 < 1 / y := div_pos one_pos hy
    linarith
  rcases le_or_gt 1 (y ^ d) with hy1 | hy1
  · rw [max_eq_right hy1]
    rcases le_or_gt 1 r with hr1 | hr1
    · have hre : (1 : ℝ) ≤ r ^ e := by
        simpa [Real.one_rpow] using
          Real.rpow_le_rpow (show (0 : ℝ) ≤ 1 by norm_num) hr1 he0.le
      have h' : y ^ d * 1 ≤ y ^ d * r ^ e :=
        mul_le_mul_of_nonneg_left hre (by positivity)
      rw [mul_one] at h'
      linarith
    · have hrd : r ^ d ≤ r ^ e := by
        have h := Real.rpow_le_rpow_of_exponent_ge hr hr1.le hed
        rwa [Real.rpow_natCast] at h
      have hpow : (1 : ℝ) ≤ r ^ d * y ^ d := by
        have h2 := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hyr'.le d
        rw [one_pow, mul_pow] at h2
        exact h2
      have h3 : r ^ d * y ^ d ≤ y ^ d * r ^ e := by
        rw [mul_comm (r ^ d) (y ^ d)]
        exact mul_le_mul_of_nonneg_left hrd (by positivity)
      linarith
  · rw [max_eq_left (le_of_lt hy1)]
    have hr1 : (1 : ℝ) ≤ r := by
      by_contra hcon
      push_neg at hcon
      have hry : 1 / y < r := (div_lt_iff₀ hy).mpr hyr'
      have hy1' : (1 : ℝ) < y := by
        have h : 1 / y < 1 := lt_trans hry hcon
        rw [div_lt_iff₀ hy] at h
        simpa using h
      have : (1 : ℝ) ≤ y ^ d := by
        have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) (le_of_lt hy1') d
        rwa [one_pow] at h
      linarith
    simpa [Real.one_rpow] using
      Real.rpow_le_rpow (show (0 : ℝ) ≤ 1 by norm_num) hr1 he0.le

lemma aux_cov_coeff_nonneg (d : ℕ) (Cc : ℝ) (hCc : 0 < Cc) :
    (0 : ℝ) ≤ 200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d := by positivity

lemma aux_cov_coeff_neg (d : ℕ) (Cc : ℝ) (hCc : 0 < Cc) :
    (0 : ℝ) ≤ (6 : ℝ) ^ d * max 1 ((3 * Cc) ^ d) := by positivity

lemma aux_cov_bound_strip (d : ℕ) (Cc R ell r t : ℝ) (hCc : 0 < Cc) (hell : 0 < ell)
    (hell1 : ell ≤ 1) (hr : 0 < r) :
    200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d * (max 1 R) ^ d * ell⁻¹ *
        r ^ (t - (d : ℝ) + 1) ≤
      (200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d
          + (6 : ℝ) ^ d * max 1 ((3 * Cc) ^ d) + 1) *
        (max 1 R) ^ d * ell⁻¹ * r ^ (t - (d : ℝ) + 1) := by
  have h2 := aux_cov_coeff_neg d Cc hCc
  have h3 : 200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d ≤
      200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d
        + (6 : ℝ) ^ d * max 1 ((3 * Cc) ^ d) + 1 := by linarith
  have hX : (0 : ℝ) ≤ (max 1 R) ^ d := by positivity
  have he : (0 : ℝ) ≤ ell⁻¹ := le_of_lt (inv_pos.mpr hell)
  have hp : (0 : ℝ) ≤ r ^ (t - (d : ℝ) + 1) := Real.rpow_nonneg hr.le _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hX) he) hp

lemma aux_cov_bound_cell (d : ℕ) (Cc e t : ℝ) (hCc : 0 < Cc) (he : 0 < e) :
    e ^ t ≤ (200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d
        + (6 : ℝ) ^ d * max 1 ((3 * Cc) ^ d) + 1) * e ^ t := by
  have h1 := aux_cov_coeff_nonneg d Cc hCc
  have h2 := aux_cov_coeff_neg d Cc hCc
  have h3 : (1 : ℝ) ≤ 200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d
      + (6 : ℝ) ^ d * max 1 ((3 * Cc) ^ d) + 1 := by linarith
  have hpos : (0 : ℝ) ≤ e ^ t := Real.rpow_nonneg he.le t
  calc e ^ t = 1 * e ^ t := (one_mul _).symm
    _ ≤ (200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d
          + (6 : ℝ) ^ d * max 1 ((3 * Cc) ^ d) + 1) * e ^ t :=
        mul_le_mul_of_nonneg_right h3 hpos

lemma aux_super_key (d : ℕ) (hd : 1 ≤ d) (Cc : ℝ) (hCc : 0 < Cc)
    (t : ℝ) (htlo : (d : ℝ) - 1 < t) (htup : t ≤ (d : ℝ))
    (R ell r : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (hr : 0 < r)
    (hyr : 1 < (3 * Cc) * r) :
    (6 : ℝ) ^ d * (max 1 R) ^ d ≤
      (200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d
          + (6 : ℝ) ^ d * max 1 ((3 * Cc) ^ d) + 1) *
        (max 1 R) ^ d * ell⁻¹ * r ^ (t - (d : ℝ) + 1) := by
  have he0 : 0 < t - (d : ℝ) + 1 := by linarith
  have hed : t - (d : ℝ) + 1 ≤ (d : ℝ) := by
    have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hcrux : (1 : ℝ) ≤ max 1 ((3 * Cc) ^ d) * r ^ (t - (d : ℝ) + 1) :=
    aux_grid_cover_key_bound d (3 * Cc) r (t - (d : ℝ) + 1)
      (by linarith [hCc]) hyr he0 hed
  have hP : (0 : ℝ) ≤ r ^ (t - (d : ℝ) + 1) := Real.rpow_nonneg hr.le _
  have h6 : (6 : ℝ) ^ d ≤
      (6 : ℝ) ^ d * max 1 ((3 * Cc) ^ d) * r ^ (t - (d : ℝ) + 1) := by
    have h := mul_le_mul_of_nonneg_left hcrux (pow_nonneg (by norm_num) d :
      (0 : ℝ) ≤ (6 : ℝ) ^ d)
    have h1 : (6 : ℝ) ^ d * 1 = (6 : ℝ) ^ d := mul_one _
    rw [h1] at h
    have h2 : (6 : ℝ) ^ d * (max 1 ((3 * Cc) ^ d) * r ^ (t - (d : ℝ) + 1)) =
        (6 : ℝ) ^ d * max 1 ((3 * Cc) ^ d) * r ^ (t - (d : ℝ) + 1) := by ring
    rwa [h2] at h
  have hBP : (6 : ℝ) ^ d * max 1 ((3 * Cc) ^ d) * r ^ (t - (d : ℝ) + 1) ≤
      (200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d
        + (6 : ℝ) ^ d * max 1 ((3 * Cc) ^ d) + 1) * r ^ (t - (d : ℝ) + 1) := by
    have hle : (6 : ℝ) ^ d * max 1 ((3 * Cc) ^ d) ≤
        200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d
          + (6 : ℝ) ^ d * max 1 ((3 * Cc) ^ d) + 1 := by
      have h1 := aux_cov_coeff_nonneg d Cc hCc
      have h2 := aux_cov_coeff_neg d Cc hCc
      linarith
    exact mul_le_mul_of_nonneg_right hle hP
  have he_inv : (1 : ℝ) ≤ ell⁻¹ := by
    have h : (1 : ℝ) ≤ 1 / ell := (le_div_iff₀ hell).mpr (by simpa using hell1)
    simpa [one_div] using h
  have hcoef0 : (0 : ℝ) ≤ 200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d
      + (6 : ℝ) ^ d * max 1 ((3 * Cc) ^ d) + 1 := by
    have h1 := aux_cov_coeff_nonneg d Cc hCc
    have h2 := aux_cov_coeff_neg d Cc hCc
    linarith
  have hcoef_le : 200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d
      + (6 : ℝ) ^ d * max 1 ((3 * Cc) ^ d) + 1 ≤
      (200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d
        + (6 : ℝ) ^ d * max 1 ((3 * Cc) ^ d) + 1) * ell⁻¹ := by
    have h := mul_le_mul_of_nonneg_left he_inv hcoef0
    have h1 : (200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d
        + (6 : ℝ) ^ d * max 1 ((3 * Cc) ^ d) + 1) * 1
        = 200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d
          + (6 : ℝ) ^ d * max 1 ((3 * Cc) ^ d) + 1 := mul_one _
    rwa [h1] at h
  have hCP : (200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d
        + (6 : ℝ) ^ d * max 1 ((3 * Cc) ^ d) + 1) * r ^ (t - (d : ℝ) + 1) ≤
      (200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d
        + (6 : ℝ) ^ d * max 1 ((3 * Cc) ^ d) + 1) * ell⁻¹
        * r ^ (t - (d : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right hcoef_le hP
  have hfin : (6 : ℝ) ^ d ≤
      (200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d
        + (6 : ℝ) ^ d * max 1 ((3 * Cc) ^ d) + 1) * ell⁻¹
        * r ^ (t - (d : ℝ) + 1) :=
    le_trans h6 (le_trans hBP hCP)
  have hX : (0 : ℝ) ≤ (max 1 R) ^ d := by positivity
  calc (6 : ℝ) ^ d * (max 1 R) ^ d
      ≤ ((200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d
          + (6 : ℝ) ^ d * max 1 ((3 * Cc) ^ d) + 1) * ell⁻¹
          * r ^ (t - (d : ℝ) + 1)) * (max 1 R) ^ d :=
        mul_le_mul_of_nonneg_right hfin hX
    _ = (200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d
          + (6 : ℝ) ^ d * max 1 ((3 * Cc) ^ d) + 1) * (max 1 R) ^ d
          * ell⁻¹ * r ^ (t - (d : ℝ) + 1) := by ring

lemma aux_strip_super (d : ℕ) (hd : 1 ≤ d) (Cc : ℝ) (hCc : 0 < Cc)
    (t : ℝ) (htlo : (d : ℝ) - 1 < t) (htup : t ≤ (d : ℝ))
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (a : Fin d → ℝ) (ell r : ℝ)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (hr : 0 < r) (hrel : Cc * r < ell)
    (hsmall : ¬ 3 * (Cc * r) ≤ 1) :
    ∃ nStrip : ℕ,
      ∃ sc : Fin nStrip → SpatialCoordinates d,
        ∃ sr : Fin nStrip → ℝ,
          (((centeredCube z R hR : Set (SpatialCoordinates d)) ∩
            {x | ∃ i : Fin d, ∃ j : ℤ,
              |x i - (a i + (j : ℝ) * ell)| ≤ Cc * r}) ⊆
              ⋃ j : Fin nStrip, Metric.ball (sc j) (sr j)) ∧
          (∀ j : Fin nStrip,
            sc j ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
              0 < sr j ∧ sr j ≤ 1) ∧
          (∑ j : Fin nStrip, (sr j) ^ t) ≤
            (200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d
                + (6 : ℝ) ^ d * max 1 ((3 * Cc) ^ d) + 1) *
              (max 1 R) ^ d * ell⁻¹ * r ^ (t - (d : ℝ) + 1) := by
  obtain ⟨nG, cG, hsubG, hcenG, hcardG⟩ :=
    aux_translated_grid_cover_grid d z R 1 hR one_pos le_rfl
  refine ⟨nG, cG, fun _ => (1 : ℝ), ?_, ?_, ?_⟩
  · intro x hx
    exact hsubG hx.1
  · intro j
    exact ⟨hcenG j, one_pos, le_rfl⟩
  · have hyr : (1 : ℝ) < (3 * Cc) * r := by
      have h : (1 : ℝ) < 3 * (Cc * r) := not_le.mp hsmall
      nlinarith [h]
    have hcard' : (nG : ℝ) ≤ (6 : ℝ) ^ d * (max 1 R) ^ d := by
      have h := hcardG
      rw [div_one, mul_pow] at h
      exact h
    have hkey : (6 : ℝ) ^ d * (max 1 R) ^ d ≤
        (200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d
            + (6 : ℝ) ^ d * max 1 ((3 * Cc) ^ d) + 1) *
          (max 1 R) ^ d * ell⁻¹ * r ^ (t - (d : ℝ) + 1) :=
      aux_super_key d hd Cc hCc t htlo htup R ell r hell hell1 hr hyr
    have hsum_eq : (∑ j : Fin nG, (fun _ : Fin nG => (1 : ℝ)) j ^ t) = (nG : ℝ) := by
      rw [show (fun _ : Fin nG => (1 : ℝ) ^ t) = (fun _ : Fin nG => (1 : ℝ)) from
        funext (fun _ => Real.one_rpow t)]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    calc (∑ j : Fin nG, (fun _ : Fin nG => (1 : ℝ)) j ^ t) = (nG : ℝ) := hsum_eq
      _ ≤ (6 : ℝ) ^ d * (max 1 R) ^ d := hcard'
      _ ≤ (200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d
            + (6 : ℝ) ^ d * max 1 ((3 * Cc) ^ d) + 1) *
            (max 1 R) ^ d * ell⁻¹ * r ^ (t - (d : ℝ) + 1) := hkey



theorem aux_translated_grid_cover
    (d : ℕ) (hd : 1 ≤ d) (Cc : ℝ) (hCc : 0 < Cc) :
    ∃ Ccov : ℝ, 0 < Ccov ∧
      ∀ (t : ℝ), (d : ℝ) - 1 < t → t ≤ (d : ℝ) →
        ∀ (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
          ∀ (a : Fin d → ℝ) (ell r : ℝ),
            0 < ell → ell ≤ 1 → 0 < r → Cc * r < ell →
            let Q : Opens (SpatialCoordinates d) := centeredCube z R hR
            let actualCell : (Fin d → ℤ) → Set (SpatialCoordinates d) :=
              fun idx =>
                (Q : Set (SpatialCoordinates d)) ∩
                  {x | ∀ i : Fin d,
                    a i + (idx i : ℝ) * ell ≤ x i ∧
                      x i < a i + ((idx i : ℝ) + 1) * ell}
            let strips : Set (SpatialCoordinates d) :=
              (Q : Set (SpatialCoordinates d)) ∩
                {x | ∃ i : Fin d, ∃ j : ℤ,
                  |x i - (a i + (j : ℝ) * ell)| ≤ Cc * r}
            (∃ nStrip : ℕ,
                ∃ stripCenters : Fin nStrip → SpatialCoordinates d,
                  ∃ stripRadii : Fin nStrip → ℝ,
                    (strips ⊆ ⋃ j : Fin nStrip,
                      Metric.ball (stripCenters j) (stripRadii j)) ∧
                    (∀ j : Fin nStrip,
                      stripCenters j ∈ (Q : Set (SpatialCoordinates d)) ∧
                        0 < stripRadii j ∧ stripRadii j ≤ 1) ∧
                    (∑ j : Fin nStrip, (stripRadii j) ^ t) ≤
                      Ccov * (max 1 R) ^ d * ell⁻¹ *
                        r ^ (t - (d : ℝ) + 1)) ∧
              (∃ nCell : (Fin d → ℤ) → ℕ,
                ∃ cellCenters : ∀ idx : Fin d → ℤ,
                  Fin (nCell idx) → SpatialCoordinates d,
                  ∃ cellRadii : ∀ idx : Fin d → ℤ,
                    Fin (nCell idx) → ℝ,
                    (∀ idx : Fin d → ℤ,
                      actualCell idx ⊆
                        ⋃ j : Fin (nCell idx),
                          Metric.ball (cellCenters idx j)
                            (cellRadii idx j)) ∧
                    (∀ idx : Fin d → ℤ, ∀ j : Fin (nCell idx),
                      cellCenters idx j ∈ (Q : Set (SpatialCoordinates d)) ∧
                        0 < cellRadii idx j ∧ cellRadii idx j ≤ 1) ∧
                    (∀ idx : Fin d → ℤ,
                      (∑ j : Fin (nCell idx), (cellRadii idx j) ^ t) ≤
                        Ccov * ell ^ t)) := by
  classical
  refine ⟨200 * (21 : ℝ) ^ d * (d : ℝ) * (Cc + 1) ^ d
      + (6 : ℝ) ^ d * max 1 ((3 * Cc) ^ d) + 1, by positivity, ?_⟩
  intro t htlo htup z R hR a ell r hell hell1 hr hrel
  constructor
  · by_cases hsmall : 3 * (Cc * r) ≤ 1
    · obtain ⟨nStrip, sc, sr, hsub, hctr, hsum⟩ :=
        aux_translated_grid_cover_strip_small d hd Cc hCc t htlo htup z R hR a ell r
          hell hell1 hr hrel hsmall
      exact ⟨nStrip, sc, sr, hsub, hctr,
        le_trans hsum (aux_cov_bound_strip d Cc R ell r t hCc hell hell1 hr)⟩
    · exact aux_strip_super d hd Cc hCc t htlo htup z R hR a ell r hell hell1 hr hrel hsmall
  · let cc : (Fin d → ℤ) → SpatialCoordinates d := fun idx =>
      if h : ((centeredCube z R hR : Set (SpatialCoordinates d)) ∩
          {x | ∀ i : Fin d, a i + (idx i : ℝ) * ell ≤ x i ∧
            x i < a i + ((idx i : ℝ) + 1) * ell}).Nonempty
        then Classical.choose h else z
    refine ⟨fun _ => 1, fun idx _ => cc idx, fun _ _ => ell, ?_, ?_, ?_⟩
    · intro idx x hx
      obtain ⟨hxQ, hxbox⟩ := hx
      rw [Set.mem_iUnion]
      refine ⟨0, ?_⟩
      rw [Metric.mem_ball]
      by_cases hne : ((centeredCube z R hR : Set (SpatialCoordinates d)) ∩
          {x | ∀ i : Fin d, a i + (idx i : ℝ) * ell ≤ x i ∧
            x i < a i + ((idx i : ℝ) + 1) * ell}).Nonempty
      · dsimp only [cc]
        rw [dif_pos hne]
        rw [dist_pi_lt_iff hell]
        intro i
        rw [Real.dist_eq, abs_lt]
        have hc := (Classical.choose_spec hne).2 i
        constructor <;> linarith [hxbox i, hc]
      · exact absurd ⟨x, hxQ, hxbox⟩ hne
    · intro idx j
      constructor
      · by_cases hne : ((centeredCube z R hR : Set (SpatialCoordinates d)) ∩
          {x | ∀ i : Fin d, a i + (idx i : ℝ) * ell ≤ x i ∧
            x i < a i + ((idx i : ℝ) + 1) * ell}).Nonempty
        · dsimp only [cc]
          rw [dif_pos hne]
          exact (Classical.choose_spec hne).1
        · dsimp only [cc]
          rw [dif_neg hne]
          exact Metric.mem_ball.mpr (by rw [dist_self]; positivity)
      · exact ⟨hell, hell1⟩
    · intro idx
      have hsum_eq : (∑ j : Fin 1, ell ^ t) = ell ^ t := Fin.sum_univ_one _
      exact le_trans (le_of_eq hsum_eq) (aux_cov_bound_cell d Cc ell t hCc hell)


end Paper
