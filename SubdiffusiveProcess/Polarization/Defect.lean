module

public import SubdiffusiveProcess.Polarization.Core

@[expose] public section

/-!
# Stability of the maximal normalized eigenvalue under relative errors on a polarization bank
-/

open Finset

namespace SubdiffusiveProcess.Polarization

variable {d : ℕ}

/-- The normalized diagonal defect of a pair of responses (Dirichlet at `false`, inverse Neumann at
`true`): the supremum over unit slopes of the volume-normalized response sum minus one. -/
noncomputable def defectSup (vol : ℝ) (R : Bool → (Fin d → ℝ) → ℝ) : ℝ :=
  sSup {v : ℝ | ∃ e : Fin d → ℝ, ∑ i, e i ^ 2 = 1 ∧ v = (R false e + R true e) / (2 * vol) - 1}

/-- Both responses are symmetric quadratic forms. -/
def IsQuadPair (R : Bool → (Fin d → ℝ) → ℝ) : Prop :=
  ∀ x, ∃ G : Fin d → Fin d → ℝ, (∀ i j, G i j = G j i) ∧ ∀ p, R x p = quadForm G p

theorem bddAbove_defect {vol : ℝ} {R : Bool → (Fin d → ℝ) → ℝ} (hR : IsQuadPair R) :
    BddAbove {v : ℝ | ∃ e : Fin d → ℝ, ∑ i, e i ^ 2 = 1 ∧
      v = (R false e + R true e) / (2 * vol) - 1} := by
  obtain ⟨G0, -, h0⟩ := hR false
  obtain ⟨G1, -, h1⟩ := hR true
  let A : Fin d → Fin d → ℝ := fun i j => (G0 i j + G1 i j) / (2 * vol)
  let m : ℝ := ∑ i, ∑ j, |A i j|
  refine ⟨d * m - 1, ?_⟩
  rintro v ⟨e, he, rfl⟩
  have hq : (R false e + R true e) / (2 * vol) = quadForm A e := by
    rw [h0, h1, quadForm_add, div_eq_mul_inv, mul_comm, quadForm_const_mul]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp only [A]
    ring
  rw [hq]
  have hm : ∀ i j, |A i j| ≤ m := by
    intro i j
    exact (single_le_sum (f := fun j => |A i j|) (fun _ _ => abs_nonneg _) (mem_univ j)).trans
      (single_le_sum (f := fun i => ∑ j, |A i j|) (fun i _ => sum_nonneg fun _ _ => abs_nonneg _)
        (mem_univ i))
  have := quadForm_le_of_entries A hm e he
  linarith [(abs_le.1 this).2]

theorem sq_sum_single (i : Fin d) : ∑ k, ((Pi.single i 1 : Fin d → ℝ) k) ^ 2 = 1 := by
  classical
  simp [Pi.single_apply]

theorem sq_sum_pair_le (i j : Fin d) :
    ∑ k, ((Pi.single i 1 + Pi.single j 1 : Fin d → ℝ) k) ^ 2 ≤ 4 := by
  calc _ ≤ ∑ k, (2 * ((Pi.single i 1 : Fin d → ℝ) k) ^ 2 + 2 * ((Pi.single j 1 : Fin d → ℝ) k) ^ 2) :=
        sum_le_sum fun k _ => by
          simp only [Pi.add_apply]
          nlinarith [sq_nonneg (((Pi.single i 1 : Fin d → ℝ) k) - (Pi.single j 1 : Fin d → ℝ) k)]
    _ = 4 := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum, sq_sum_single, sq_sum_single]; norm_num

/-- **Polarization of the diagonal defect.** -/
theorem polarization_defect (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (vol : ℝ), 0 < vol → ∀ (Ra Rb : Bool → (Fin d → ℝ) → ℝ) (eta : ℝ),
      0 ≤ eta → IsQuadPair Ra → IsQuadPair Rb → (∀ x p, 0 ≤ Rb x p) →
      (∀ e : Fin d → ℝ, ∑ i, e i ^ 2 = 1 → 2 * vol ≤ Rb false e + Rb true e) →
      (∀ x : Bool,
        (∀ i : Fin d, |Ra x (Pi.single i 1) - Rb x (Pi.single i 1)| ≤
          eta * (vol + Rb x (Pi.single i 1))) ∧
        (∀ i j : Fin d, |Ra x (Pi.single i 1 + Pi.single j 1) - Rb x (Pi.single i 1 + Pi.single j 1)| ≤
          eta * (vol + Rb x (Pi.single i 1 + Pi.single j 1)))) →
      |defectSup vol Ra - defectSup vol Rb| ≤ C * eta * (1 + defectSup vol Rb) := by
  classical
  refine ⟨10 * d, by positivity, ?_⟩
  intro vol hvol Ra Rb eta heta hRa hRb hnn hpd hrel
  have hRa0 := hRa
  have hRb0 := hRb
  choose GA hGAs hGAr using hRa
  choose GB hGBs hGBr using hRb
  let Q : (Bool → (Fin d → ℝ) → ℝ) → (Fin d → ℝ) → ℝ :=
    fun R p => (R false p + R true p) / (2 * vol)
  -- the difference matrix
  let Δ : Fin d → Fin d → ℝ := fun i j =>
    ((GA false i j - GB false i j) + (GA true i j - GB true i j)) / (2 * vol)
  have hΔs : ∀ i j, Δ i j = Δ j i := by
    intro i j; simp only [Δ, hGAs false i j, hGAs true i j, hGBs false i j, hGBs true i j]
  have hΔq : ∀ p, Q Ra p - Q Rb p = quadForm Δ p := by
    intro p
    have e : Q Ra p - Q Rb p = (2 * vol)⁻¹ * ((quadForm (GA false) p - quadForm (GB false) p) +
        (quadForm (GA true) p - quadForm (GB true) p)) := by
      simp only [Q, hGAr, hGBr]; ring
    rw [e, quadForm_sub, quadForm_sub, quadForm_add, quadForm_const_mul]
    congr 1
    funext i j
    simp only [Δ]
    ring
  have hbA := bddAbove_defect (vol := vol) hRa0
  have hbB := bddAbove_defect (vol := vol) hRb0
  have leJ : ∀ (R : Bool → (Fin d → ℝ) → ℝ),
      BddAbove {v : ℝ | ∃ e : Fin d → ℝ, ∑ i, e i ^ 2 = 1 ∧
        v = (R false e + R true e) / (2 * vol) - 1} →
      ∀ e : Fin d → ℝ, ∑ i, e i ^ 2 = 1 → Q R e - 1 ≤ defectSup vol R :=
    fun R hb e he => le_csSup hb ⟨e, he, rfl⟩
  let e0 : Fin d → ℝ := Pi.single ⟨0, hd⟩ 1
  have he0 : ∑ i, e0 i ^ 2 = 1 := sq_sum_single _
  have hQb1 : 1 ≤ Q Rb e0 := by
    simp only [Q]
    rw [le_div_iff₀ (by positivity)]
    linarith [hpd e0 he0]
  have hJb0 : 0 ≤ defectSup vol Rb := by
    have := leJ Rb hbB e0 he0
    linarith
  set Jb := defectSup vol Rb with hJb
  set Ja := defectSup vol Ra with hJa
  -- homogeneity of the reference quadratic form
  have hscale : ∀ p : Fin d → ℝ, Q Rb p ≤ (∑ i, p i ^ 2) * (1 + Jb) := by
    intro p
    have hs0 : 0 ≤ ∑ i, p i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
    rcases hs0.eq_or_lt with hs | hs
    · have hp : p = 0 := by
        funext i
        have := (sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (p i))).1 hs.symm i (mem_univ i)
        simpa using this
      subst hp
      simp only [Q, hGBr, quadForm, Pi.zero_apply]
      simp
    · set s := ∑ i, p i ^ 2 with hsdef
      have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
      let e : Fin d → ℝ := (Real.sqrt s)⁻¹ • p
      have he : ∑ i, e i ^ 2 = 1 := by
        simp only [e, Pi.smul_apply, smul_eq_mul, mul_pow]
        rw [← mul_sum, inv_pow, Real.sq_sqrt hs.le]
        exact inv_mul_cancel₀ hs.ne'
      have hpe : p = Real.sqrt s • e := by
        simp only [e, smul_smul, mul_inv_cancel₀ hsq.ne', one_smul]
      have hQe : Q Rb p = s * Q Rb e := by
        conv_lhs => rw [hpe]
        simp only [Q, hGBr, quadForm_smul, Real.sq_sqrt hs.le]
        ring
      rw [hQe]
      exact mul_le_mul_of_nonneg_left (by linarith [leJ Rb hbB e he]) hs.le
  -- the polarization bank
  have hbank : ∀ p : Fin d → ℝ, (∑ i, p i ^ 2) ≤ 4 →
      (∀ x : Bool, |Ra x p - Rb x p| ≤ eta * (vol + Rb x p)) →
      |quadForm Δ p| ≤ 5 * eta * (1 + Jb) := by
    intro p hp4 hrelp
    rw [← hΔq]
    have h1 := hrelp false
    have h2 := hrelp true
    have hQ : Q Rb p ≤ 4 * (1 + Jb) :=
      (hscale p).trans (mul_le_mul_of_nonneg_right hp4 (by linarith))
    have hsum : Rb false p + Rb true p = 2 * vol * Q Rb p := by
      simp only [Q]; field_simp
    have hdiff : Q Ra p - Q Rb p =
        ((Ra false p - Rb false p) + (Ra true p - Rb true p)) / (2 * vol) := by
      simp only [Q]; ring
    rw [hdiff, abs_div, abs_of_pos (by positivity : 0 < 2 * vol), div_le_iff₀ (by positivity)]
    calc |(Ra false p - Rb false p) + (Ra true p - Rb true p)|
        ≤ |Ra false p - Rb false p| + |Ra true p - Rb true p| := abs_add_le _ _
      _ ≤ eta * (vol + Rb false p) + eta * (vol + Rb true p) := add_le_add h1 h2
      _ = eta * (2 * vol + 2 * vol * Q Rb p) := by rw [← hsum]; ring
      _ ≤ eta * (2 * vol + 2 * vol * (4 * (1 + Jb))) := by
          apply mul_le_mul_of_nonneg_left _ heta
          nlinarith [hQ, hvol]
      _ ≤ 5 * eta * (1 + Jb) * (2 * vol) := by nlinarith [mul_nonneg heta hvol.le, hJb0, mul_nonneg (mul_nonneg heta hvol.le) hJb0]
  have hM1 : ∀ i, |quadForm Δ (Pi.single i 1)| ≤ 5 * eta * (1 + Jb) := fun i =>
    hbank _ (by rw [sq_sum_single]; norm_num) (fun x => (hrel x).1 i)
  have hM2 : ∀ i j, |quadForm Δ (Pi.single i 1 + Pi.single j 1)| ≤ 5 * eta * (1 + Jb) :=
    fun i j => hbank _ (sq_sum_pair_le i j) (fun x => (hrel x).2 i j)
  have hent := entry_bound Δ hΔs hM1 hM2
  have hunit : ∀ e : Fin d → ℝ, ∑ i, e i ^ 2 = 1 →
      |quadForm Δ e| ≤ 10 * d * eta * (1 + Jb) := by
    intro e he
    have := quadForm_le_of_entries Δ hent e he
    calc _ ≤ d * (2 * (5 * eta * (1 + Jb))) := this
      _ = _ := by ring
  have hne : ∀ R : Bool → (Fin d → ℝ) → ℝ, Set.Nonempty {v : ℝ | ∃ e : Fin d → ℝ, ∑ i, e i ^ 2 = 1 ∧
      v = (R false e + R true e) / (2 * vol) - 1} := fun R => ⟨_, e0, he0, rfl⟩
  have hup1 : Ja ≤ Jb + 10 * d * eta * (1 + Jb) := by
    refine csSup_le (hne Ra) ?_
    rintro v ⟨e, he, rfl⟩
    have h1 := leJ Rb hbB e he
    have h2 := (abs_le.1 (hunit e he)).2
    have h3 := hΔq e
    change Q Ra e - 1 ≤ _
    linarith
  have hup2 : Jb ≤ Ja + 10 * d * eta * (1 + Jb) := by
    refine csSup_le (hne Rb) ?_
    rintro v ⟨e, he, rfl⟩
    have h1 := leJ Ra hbA e he
    have h2 := (abs_le.1 (hunit e he)).1
    have h3 := hΔq e
    change Q Rb e - 1 ≤ _
    linarith
  rw [abs_le]
  constructor <;> nlinarith [hup1, hup2]

end SubdiffusiveProcess.Polarization
