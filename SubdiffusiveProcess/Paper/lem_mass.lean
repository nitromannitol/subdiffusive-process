module

public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.ResponseMoments.UpperDensity
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.lem_mass_grid_partition
public import SubdiffusiveProcess.Paper.lem_mass_nondoubling
public import SubdiffusiveProcess.Paper.lem_mass_interior_collar
public import SubdiffusiveProcess.Paper.lem_mass_favourable_horizons
public import SubdiffusiveProcess.Paper.lem_shifts
public import SubdiffusiveProcess.Paper.cor_integrate
public import SubdiffusiveProcess.Paper.lem_mass_average

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess MeasureTheory

namespace SubdiffusiveProcess.Paper
noncomputable section

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem aux_lem_mass_sum_const {α : Type} (s : Finset α) (c : ℝ) :
    (∑ _ ∈ s, c) = (s.card : ℝ) * c := by
  rw [Finset.sum_const, nsmul_eq_mul]

theorem aux_lem_mass_sum_le_const {α : Type} (s : Finset α) (f : α → ℝ) (c : ℝ)
    (hf : ∀ n ∈ s, f n ≤ c) :
    (∑ n ∈ s, f n) ≤ (s.card : ℝ) * c := by
  calc
    (∑ n ∈ s, f n) ≤ ∑ n ∈ s, c := Finset.sum_le_sum hf
    _ = (s.card : ℝ) * c := aux_lem_mass_sum_const s c

theorem aux_lem_mass_extract
    (X : Type) [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (qQ : ℝ) (hqQ : 0 < qQ)
    (Shift : Type) [Fintype Shift] [Nonempty Shift]
    (α : Type) [DecidableEq α]
    (J n0 : ℕ) (hJ : 0 < J) (levels : Finset ℕ)
    (Uset : ℕ → Prop)
    (hlev_n0 : ∀ n ∈ levels, n0 ≤ n)
    (hlev_one : ∀ n ∈ levels, 1 ≤ n)
    (hlev_U : ∀ n ∈ levels, Uset n)
    (hlev_card : levels.card ≤ J)
    (K : Shift → ℕ → Finset α)
    (qualifies : Shift → ℕ → α → Prop)
    (P : Shift → ℕ → α → Prop)
    (cell : Shift → ℕ → α → Set X)
    (GoodSet : ℕ → Shift → Set X)
    (hGoodSet : ∀ n sigma,
      GoodSet n sigma = ⋃ k ∈ (K sigma n).filter (qualifies sigma n), cell sigma n k)
    (hqual : ∀ n sigma k, qualifies sigma n k → P sigma n k)
    (hgood_lower :
      qQ / 4 <
        (∑ sigma : Shift, ∑ n ∈ levels, (mu (GoodSet n sigma)).toReal) /
          ((J : ℝ) * (Fintype.card Shift : ℝ))) :
    ∃ n, n0 ≤ n ∧ 1 ≤ n ∧ Uset n ∧
      ∃ sigma : Shift, ∃ G : Finset α,
        (∀ k ∈ G, P sigma n k) ∧
          qQ / 8 ≤ (mu (⋃ k ∈ G, cell sigma n k)).toReal := by
  classical
  have hcardr : (levels.card : ℝ) ≤ (J : ℝ) := by exact_mod_cast hlev_card
  by_contra hnone
  have hbound : ∀ n ∈ levels, ∀ sigma : Shift,
      (mu (GoodSet n sigma)).toReal ≤ qQ / 4 := by
    intro n hn sigma
    by_contra hnot
    apply hnone
    let G : Finset α := (K sigma n).filter (qualifies sigma n)
    refine ⟨n, hlev_n0 n hn, hlev_one n hn, hlev_U n hn, sigma, G, ?_, ?_⟩
    · intro k hk
      exact hqual n sigma k (Finset.mem_filter.mp hk).2
    · have hm : qQ / 4 < (mu (⋃ k ∈ G, cell sigma n k)).toReal := by
        simpa [G, hGoodSet n sigma] using (lt_of_not_ge hnot)
      nlinarith [hqQ, hm]
  have hsum :
      (∑ sigma : Shift, ∑ n ∈ levels, (mu (GoodSet n sigma)).toReal) ≤
        ((J : ℝ) * (Fintype.card Shift : ℝ)) * (qQ / 4) := by
    calc
      (∑ sigma : Shift, ∑ n ∈ levels, (mu (GoodSet n sigma)).toReal) ≤
          ∑ sigma : Shift, ∑ n ∈ levels, qQ / 4 := by
            apply Finset.sum_le_sum
            intro sigma hσ
            apply Finset.sum_le_sum
            intro n hn
            exact hbound n hn sigma
      _ = (Fintype.card Shift : ℝ) * (levels.card : ℝ) * (qQ / 4) := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ ((J : ℝ) * (Fintype.card Shift : ℝ)) * (qQ / 4) := by
        have hnonneg : 0 ≤ (Fintype.card Shift : ℝ) * (qQ / 4) := by positivity
        nlinarith
  have hden : 0 < (J : ℝ) * (Fintype.card Shift : ℝ) := by
    positivity
  have havg_upper :
      (∑ sigma : Shift, ∑ n ∈ levels, (mu (GoodSet n sigma)).toReal) /
          ((J : ℝ) * (Fintype.card Shift : ℝ)) ≤ qQ / 4 := by
    apply (div_le_iff₀ hden).2
    convert hsum using 1 ; ring
  exact (not_lt_of_ge havg_upper hgood_lower)

theorem aux_lem_mass_pad_total
    {X Shift : Type} [MeasurableSpace X] [Fintype Shift]
    (mu : Measure X) (levels : Finset ℕ)
    (PadSet : ℕ → Shift → Set X)
    (padCoeff qQ M : ℝ) (d : ℕ)
    (hcard : (Fintype.card Shift : ℝ) = M ^ d)
    (hpad_level : ∀ n ∈ levels,
      (∑ sigma : Shift, (mu (PadSet n sigma)).toReal) ≤
        (padCoeff * qQ) * M ^ d) :
    (∑ sigma : Shift, ∑ n ∈ levels, (mu (PadSet n sigma)).toReal) ≤
      (Fintype.card Shift : ℝ) * (levels.card : ℝ) * padCoeff * qQ := by
  classical
  have hswap :
      (∑ sigma : Shift, ∑ n ∈ levels, (mu (PadSet n sigma)).toReal) =
        ∑ n ∈ levels, ∑ sigma : Shift, (mu (PadSet n sigma)).toReal := by
    rw [Finset.sum_comm]
  rw [hswap]
  calc
    (∑ n ∈ levels, ∑ sigma : Shift, (mu (PadSet n sigma)).toReal) ≤
        ∑ n ∈ levels, (padCoeff * qQ) * M ^ d := by
      exact Finset.sum_le_sum (s := levels) (fun n hn => hpad_level n hn)
    _ = (Fintype.card Shift : ℝ) * (levels.card : ℝ) * padCoeff * qQ := by
      rw [aux_lem_mass_sum_const]
      rw [← hcard]
      ring

theorem aux_lem_mass_pad_total_eq
    {X Shift : Type} [MeasurableSpace X] [Fintype Shift]
    (mu : Measure X) (levels : Finset ℕ)
    (PadSet NonPad : ℕ → Shift → Set X)
    (hlevels : ∀ n ∈ levels, 1 ≤ n)
    (heq : ∀ n, 1 ≤ n → ∀ sigma, PadSet n sigma = NonPad n sigma)
    (padCoeff qQ M : ℝ) (d : ℕ)
    (hcard : (Fintype.card Shift : ℝ) = M ^ d)
    (hpad : ∀ n ∈ levels,
      (∑ sigma : Shift, (mu (NonPad n sigma)).toReal) ≤
        (padCoeff * qQ) * M ^ d) :
    (∑ sigma : Shift, ∑ n ∈ levels, (mu (PadSet n sigma)).toReal) ≤
      (Fintype.card Shift : ℝ) * (levels.card : ℝ) * padCoeff * qQ := by
  apply aux_lem_mass_pad_total mu levels PadSet padCoeff qQ M d hcard
  intro n hn
  calc
    (∑ sigma : Shift, (mu (PadSet n sigma)).toReal) =
        ∑ sigma : Shift, (mu (NonPad n sigma)).toReal := by
      apply Finset.sum_congr rfl
      intro sigma hσ
      rw [heq n (hlevels n hn) sigma]
    _ ≤ (padCoeff * qQ) * M ^ d := hpad n hn

theorem aux_lem_mass_pad_total_reparam
    {X Shift : Type} [MeasurableSpace X] [Fintype Shift]
    (mu : Measure X) (levels : Finset ℕ)
    (PadSet NonPad : ℕ → Shift → Set X)
    (hlevels : ∀ n ∈ levels, 1 ≤ n)
    (heq : ∀ n, 1 ≤ n → ∀ sigma, PadSet n sigma = NonPad n sigma)
    (a q padCoeff qQ M : ℝ) (d : ℕ)
    (ha : padCoeff = a) (hq : qQ = q)
    (hcard : (Fintype.card Shift : ℝ) = M ^ d)
    (hpad : ∀ n ∈ levels,
      (∑ sigma : Shift, (mu (NonPad n sigma)).toReal) ≤
        (a * q) * M ^ d) :
    (∑ sigma : Shift, ∑ n ∈ levels, (mu (PadSet n sigma)).toReal) ≤
      (Fintype.card Shift : ℝ) * (levels.card : ℝ) * padCoeff * qQ := by
  apply aux_lem_mass_pad_total_eq mu levels PadSet NonPad hlevels heq
    padCoeff qQ M d hcard
  intro n hn
  rw [ha, hq]
  exact hpad n hn

theorem aux_lem_mass_Bquot {B J : ℝ} (hJ : 0 < J) (hB : 16 * B < J) :
    B / J < (1 / 16 : ℝ) := by
  apply (div_lt_iff₀ hJ).2
  nlinarith

theorem aux_lem_mass_deficit {J c : ℝ}
    (h : (1 / 2 - (1 / 16 : ℝ)) * J ≤ c) :
    J / 2 - (1 / 16 : ℝ) * J ≤ c := by
  nlinarith

theorem aux_lem_mass_coefficient
    {theta parentRate paddingRate collarRate B J : ℝ}
    (hJ : 0 < J) (hB : B / J < (1 / 16 : ℝ))
    (hloss : theta + parentRate + paddingRate + collarRate ≤ (1 / 8 : ℝ)) :
    (1 / 4 : ℝ) <
      1 / 2 - theta - parentRate - paddingRate - collarRate - B / J -
        ((1 / 16 : ℝ) * J) / J := by
  have hcancel : ((1 / 16 : ℝ) * J) / J = (1 / 16 : ℝ) := by
    field_simp
  rw [hcancel]
  linarith

theorem aux_lem_mass_pos_mul {a q : ℝ} (ha : (1 / 4 : ℝ) < a) (hq : 0 < q) :
    q / 4 < a * q := by
  nlinarith

theorem aux_lem_mass_capture {q m : ℝ} (hq : 0 < q) (hm : q / 4 < m) :
    q / 8 ≤ m := by
  linarith

theorem aux_lem_mass_no_large_sum
    {S : Type} [Fintype S] [Nonempty S]
    (q J : ℝ) (levels : Finset ℕ) (f : S → ℕ → ℝ)
    (hq : 0 < q) (hJ : 0 < J)
    (hcard : (levels.card : ℝ) ≤ J)
    (hlower : q / 4 <
      (∑ s : S, ∑ n ∈ levels, f s n) /
        (J * (Fintype.card S : ℝ)))
    (hbound : ∀ n ∈ levels, ∀ s : S, f s n ≤ q / 4) : False := by
  have hsum :
      (∑ s : S, ∑ n ∈ levels, f s n) ≤
        (J * (Fintype.card S : ℝ)) * (q / 4) := by
    calc
      (∑ s : S, ∑ n ∈ levels, f s n) ≤
          ∑ s : S, ∑ n ∈ levels, q / 4 := by
            apply Finset.sum_le_sum
            intro s hs
            apply Finset.sum_le_sum
            intro n hn
            exact hbound n hn s
      _ = (Fintype.card S : ℝ) * (levels.card : ℝ) * (q / 4) := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ (J * (Fintype.card S : ℝ)) * (q / 4) := by
        have hq4 : 0 ≤ q / 4 := by positivity
        have hcardS : 0 ≤ (Fintype.card S : ℝ) := by positivity
        have hmul : (levels.card : ℝ) * (q / 4) ≤ J * (q / 4) :=
          mul_le_mul_of_nonneg_right hcard hq4
        calc
          (Fintype.card S : ℝ) * (levels.card : ℝ) * (q / 4) =
              (Fintype.card S : ℝ) * ((levels.card : ℝ) * (q / 4)) := by ring
          _ ≤ (Fintype.card S : ℝ) * (J * (q / 4)) :=
            mul_le_mul_of_nonneg_left hmul hcardS
          _ = (J * (Fintype.card S : ℝ)) * (q / 4) := by ring
  have hcardSpos : 0 < (Fintype.card S : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hden : 0 < J * (Fintype.card S : ℝ) := mul_pos hJ hcardSpos
  have havg :
      (∑ s : S, ∑ n ∈ levels, f s n) /
        (J * (Fintype.card S : ℝ)) ≤ q / 4 := by
    have hsum' : (∑ s : S, ∑ n ∈ levels, f s n) ≤
        (q / 4) * (J * (Fintype.card S : ℝ)) := by
      calc
        (∑ s : S, ∑ n ∈ levels, f s n) ≤
            (J * (Fintype.card S : ℝ)) * (q / 4) := hsum
        _ = (q / 4) * (J * (Fintype.card S : ℝ)) := by ring
    exact (div_le_iff₀ hden).2 hsum'
  exact (not_lt_of_ge havg hlower)

theorem aux_lem_mass_bad_integrate
    {X : Type} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (Q : Set X) (BadSet : ℕ → Set X)
    (theta B : ℝ) (htheta : 0 ≤ theta) (hB : 0 ≤ B)
    (hBad_meas : ∀ n : ℕ, MeasurableSet (BadSet n))
    (hBad_sub : ∀ n : ℕ, BadSet n ⊆ Q)
    (P : ℕ → X → Prop)
    (hmem : ∀ n : ℕ, ∀ x : X, x ∈ Q → (x ∈ BadSet n ↔ ¬ P n x))
    (hbad : ∀ x : X, x ∈ Q → ∀ J : ℕ,
      (Nat.card {n : ℕ // 1 ≤ n ∧ n ≤ J ∧ ¬ P n x} : ℝ) ≤
        theta * (J : ℝ) + B) :
    ∀ J : ℕ, 1 ≤ J →
      (∑ n ∈ Finset.Icc 1 J, (mu (BadSet n)).toReal) ≤
        (theta * (J : ℝ) + B) * (mu Q).toReal := by
  intro J hJ
  have hchain : ∀ J : ℕ, 1 ≤ J → ∀ x : X,
      (Nat.card {n : ℕ // n ∈ Finset.Icc 1 J ∧ x ∈ BadSet n} : ℝ) ≤
        theta * (J : ℝ) + B := by
    intro J' hJ' x
    by_cases hx : x ∈ Q
    · have heq : Nat.card {j : ℕ // j ∈ Finset.Icc 1 J' ∧ x ∈ BadSet j} =
          Nat.card {j : ℕ // 1 ≤ j ∧ j ≤ J' ∧ ¬ P j x} := by
        apply Nat.card_congr
        exact Equiv.subtypeEquivRight (by
          intro j
          simp only [Finset.mem_Icc]
          rw [hmem j x hx]
          tauto)
      rw [heq]
      exact hbad x hx J'
    · have hnone : ∀ n : ℕ, x ∉ BadSet n := by
        intro n hn
        exact hx (hBad_sub n hn)
      have hz : (Nat.card {j : ℕ // j ∈ Finset.Icc 1 J' ∧ x ∈ BadSet j} : ℝ) = 0 := by
        let : IsEmpty {j : ℕ // j ∈ Finset.Icc 1 J' ∧ x ∈ BadSet j} :=
          ⟨fun j => hnone j.1 j.2.2⟩
        have hz' : Nat.card {j : ℕ // j ∈ Finset.Icc 1 J' ∧ x ∈ BadSet j} = 0 :=
          Nat.card_eq_zero.mpr (Or.inl inferInstance)
        exact_mod_cast hz'
      rw [hz]
      exact add_nonneg (mul_nonneg htheta (Nat.cast_nonneg J')) hB
  let Pm : Measure Unit := Measure.dirac ()
  have hae := _root_.SubdiffusiveProcess.Paper.cor_integrate (Om := Unit) Pm
    (Q := X) theta htheta (fun _ : Unit => B)
    measurable_const (fun _ => hB) (fun (_ : Unit) (n : ℕ) => BadSet n)
    (fun _ n => hBad_meas n)
    (Filter.Eventually.of_forall (fun _ => hchain))
  let R : Prop := ∀ (lam : Measure X), IsFiniteMeasure lam →
      ∀ J : ℕ, 1 ≤ J →
        ∑ n ∈ Finset.Icc 1 J, (lam (BadSet n)).toReal ≤
          (theta * (J : ℝ) + B) * (lam Set.univ).toReal
  have hu : R := by
    have haeR : ∀ᵐ (_ : Unit) ∂Pm, R := by
      simpa only [R] using hae
    have hzero := (MeasureTheory.ae_iff.mp haeR)
    by_contra hnot
    have hmem' : () ∈ {u : Unit | ¬ R} := by simpa using hnot
    have hone : Pm {u : Unit | ¬ R} = 1 :=
      Measure.dirac_apply_of_mem hmem'
    rw [hone] at hzero
    exact one_ne_zero hzero
  have hraw := hu (mu.restrict Q) inferInstance J hJ
  have hres (n : ℕ) : (mu.restrict Q) (BadSet n) = mu (BadSet n) := by
    rw [Measure.restrict_apply (hBad_meas n)]
    congr 1
    exact Set.inter_eq_left.2 (fun x hx => hBad_sub n hx)
  simp_rw [hres] at hraw
  rw [Measure.restrict_apply_univ] at hraw
  exact hraw




theorem lem_mass
    (d : ℕ) (hd : 2 ≤ d)
    (H1 : ℕ) (hH1 : 1 ≤ H1)
    (Mm : ℕ) (hMm : 2 ≤ Mm)
    (gamma : ℝ) (hgamma : gamma ∈ Set.Ioo (0 : ℝ) 1)
    (zeta : ℝ) (hzeta : 0 < zeta)
    (Cwidth : ℝ) (hCwidth : 0 < Cwidth) :
    let L : ℝ := (3 : ℝ) ^ H1
    let w : ℝ := Cwidth * L ^ gamma
    let Cbound : ℝ := 2 * (d : ℝ) * (Cwidth + 2)
    (hcop : Nat.Coprime Mm (3 ^ H1)) →
    (hMgam : (Mm : ℝ) ^ (-1 : ℝ) ≤ L ^ (gamma - 1)) →
    let Shift : Type := Fin d → Fin Mm
    let shift : Shift → Fin d → ℝ :=
      fun sigma i => ((sigma i).val : ℝ) / (Mm : ℝ)
    let side : ℕ → ℝ := fun n => L ^ (-(n : ℝ))
    let lo : Shift → ℕ → (Fin d → Int) → Fin d → ℝ :=
      fun sigma n k i => shift sigma i + side n * (k i : ℝ)
    let cell : Shift → ℕ → (Fin d → Int) → Set (SpatialCoordinates d) :=
      fun sigma n k => Set.pi Set.univ (fun i =>
        Set.Ico (lo sigma n k i) (lo sigma n k i + side n))
    let parentIdx : (Fin d → Int) → Fin d → Int :=
      fun k i => Int.floor ((k i : ℝ) / L)
    let parent : Shift → ℕ → (Fin d → Int) → Set (SpatialCoordinates d) :=
      fun sigma n k => cell sigma (n - 1) (parentIdx k)
    let pointIdx : Shift → ℕ → SpatialCoordinates d → Fin d → Int :=
      fun sigma n x i => Int.floor ((x i - shift sigma i) / side n)
    let padded : Shift → ℕ → (Fin d → Int) → Prop :=
      fun sigma n k => (∀ i : Fin d,
        w * side n < lo sigma n k i - lo sigma (n - 1) (parentIdx k) i ∧
          w * side n <
            lo sigma (n - 1) (parentIdx k) i + side (n - 1) -
              (lo sigma n k i + side n))
    (zQ : SpatialCoordinates d) →
    (rQ : ℝ) →
    (hrQ : 0 < rQ) →
    (mu : Measure (SpatialCoordinates d)) →
    [IsFiniteMeasure mu] →
    let Q := centeredCube zQ rQ hrQ
    (hsupp : mu ((Q : Set (SpatialCoordinates d))ᶜ) = 0) →
    (hQpositive : 0 < mu (Q : Set (SpatialCoordinates d))) →
    (hfaces : ∀ (sigma : Shift) (n : ℕ) (i : Fin d) (k : Int),
      mu {x : SpatialCoordinates d |
        x i = shift sigma i + side n * (k : ℝ)} = 0) →
    (Uset : ℕ → Prop) →
    ((1 / 2 : ℝ) ≤ _root_.SubdiffusiveProcess.ResponseMoments.upperDensity Uset) →
    (Good : Shift → ℕ → (Fin d → Int) → Prop) →
    (theta : ℝ) →
    (htheta : 0 ≤ theta) →
    (epscoll : ℝ) →
    (hepscoll : 0 < epscoll) →
    (hloss : theta + L ^ (-zeta) + Cbound * L ^ (gamma - 1) + epscoll ≤
      1 / 8) →
    (B : Shift → ℝ) →
    (hB : ∀ sigma : Shift, 0 ≤ B sigma) →
    (hbad : ∀ (sigma : Shift) (x : SpatialCoordinates d),
      x ∈ (Q : Set (SpatialCoordinates d)) →
      ∀ J : ℕ,
        (Nat.card {n : ℕ // 1 ≤ n ∧ n ≤ J ∧
          ¬ Good sigma n (pointIdx sigma n x)} : ℝ) ≤
          theta * (J : ℝ) + B sigma) →
    ∀ n0 : ℕ, ∃ n : ℕ, n0 ≤ n ∧ 1 ≤ n ∧ Uset n ∧
      ∃ sigma : Shift, ∃ G : Finset (Fin d → Int),
        (∀ k ∈ G,
          Good sigma n k ∧ padded sigma n k ∧
            closure (parent sigma n k) ⊆ (Q : Set (SpatialCoordinates d)) ∧
            (mu (parent sigma n k)).toReal ≤
              L ^ ((d : ℝ) + zeta) * (mu (cell sigma n k)).toReal) ∧
        (mu (Q : Set (SpatialCoordinates d))).toReal / 8 ≤
          (mu (⋃ k ∈ G, cell sigma n k)).toReal := by
  dsimp only
  intro hcop hMgam zQ rQ hrQ mu zQinst hsupp hQpositive hfaces Uset hU Good theta htheta
    epscoll hepscoll hloss B hB hbad n0
  classical
  let L : ℝ := (3 : ℝ) ^ H1
  let Shift : Type := Fin d → Fin Mm
  have hcardShift : (Fintype.card Shift : ℝ) = (Mm : ℝ) ^ d := by
    change (Fintype.card (Fin d → Fin Mm) : ℝ) = (Mm : ℝ) ^ d
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow]
  let shift : Shift → Fin d → ℝ :=
    fun sigma i => ((sigma i).val : ℝ) / (Mm : ℝ)
  let side : ℕ → ℝ := fun n => L ^ (-(n : ℝ))
  let lo : Shift → ℕ → (Fin d → Int) → Fin d → ℝ :=
    fun sigma n k i => shift sigma i + side n * (k i : ℝ)
  let cell : Shift → ℕ → (Fin d → Int) → Set (SpatialCoordinates d) :=
    fun sigma n k => Set.pi Set.univ (fun i =>
      Set.Ico (lo sigma n k i) (lo sigma n k i + side n))
  let parentIdx : (Fin d → Int) → Fin d → Int :=
    fun k i => Int.floor ((k i : ℝ) / L)
  let parent : Shift → ℕ → (Fin d → Int) → Set (SpatialCoordinates d) :=
    fun sigma n k => cell sigma (n - 1) (parentIdx k)
  let pointIdx : Shift → ℕ → SpatialCoordinates d → Fin d → Int :=
    fun sigma n x i => Int.floor ((x i - shift sigma i) / side n)
  let padded : Shift → ℕ → (Fin d → Int) → Prop :=
    fun sigma n k => (∀ i : Fin d,
      Cwidth * L ^ gamma * side n < lo sigma n k i -
          lo sigma (n - 1) (parentIdx k) i ∧
        Cwidth * L ^ gamma * side n <
          lo sigma (n - 1) (parentIdx k) i + side (n - 1) -
            (lo sigma n k i + side n))
  let nonPadded : Shift → ℕ → SpatialCoordinates d → Prop :=
    fun sigma n x => ∃ i : Fin d,
      lo sigma n (pointIdx sigma n x) i -
            lo sigma (n - 1) (pointIdx sigma (n - 1) x) i ≤
          Cwidth * L ^ gamma * side n ∨
        lo sigma (n - 1) (pointIdx sigma (n - 1) x) i + side (n - 1) -
              (lo sigma n (pointIdx sigma n x) i + side n) ≤
          Cwidth * L ^ gamma * side n
  let Q : Set (SpatialCoordinates d) := centeredCube zQ rQ hrQ
  have hL : 0 < L := by positivity
  have hL1 : 1 < L := by
    dsimp [L]
    have : (1 : ℝ) < 3 := by norm_num
    exact one_lt_pow₀ this (by omega)
  have hQmeas : MeasurableSet Q := by
    dsimp [Q]
    exact (centeredCube zQ rQ hrQ).isOpen.measurableSet
  have hQpos : 0 < (mu Q).toReal := by
    dsimp [Q] at *
    exact ENNReal.toReal_pos (ne_of_gt hQpositive) (measure_ne_top mu _)
  have hgrid := _root_.SubdiffusiveProcess.Paper.lem_mass_grid_partition d H1 Mm hd hH1 hMm
  have hgrid_meas : ∀ (sigma : Shift) (n : ℕ) (k : Fin d → Int),
      MeasurableSet (cell sigma n k) := by
    intro sigma n k
    simpa [L, Shift, shift, side, lo, cell] using hgrid.1 sigma n k
  have hgrid_mem : ∀ (sigma : Shift) (n : ℕ) (x : SpatialCoordinates d)
      (k : Fin d → Int), x ∈ cell sigma n k ↔ k = pointIdx sigma n x := by
    intro sigma n x k
    simpa [L, Shift, shift, side, lo, cell, pointIdx] using hgrid.2.1 sigma n x k
  have hgrid_parent : ∀ (sigma : Shift) (n : ℕ), 1 ≤ n →
      ∀ (k : Fin d → Int), cell sigma n k ⊆ parent sigma n k := by
    intro sigma n hn k
    simpa [L, Shift, shift, side, lo, cell, parentIdx, parent] using
      (hgrid.2.2.1 sigma n hn k).1
  have hgrid_finite : ∀ (sigma : Shift) (n : ℕ),
      {k : Fin d → Int | (cell sigma n k ∩ Q).Nonempty}.Finite := by
    intro sigma n
    simpa [L, Shift, shift, side, lo, cell, Q] using
      hgrid.2.2.2.2 sigma n zQ rQ hrQ
  have hpoint_parent : ∀ (sigma : Shift) (n : ℕ), 1 ≤ n →
      ∀ x : SpatialCoordinates d,
        pointIdx sigma (n - 1) x = parentIdx (pointIdx sigma n x) := by
    intro sigma n hn x
    have hx : x ∈ cell sigma n (pointIdx sigma n x) :=
      (hgrid_mem sigma n x (pointIdx sigma n x)).2 rfl
    simpa [L, Shift, shift, side, lo, cell, parentIdx, pointIdx] using
      (hgrid.2.2.1 sigma n hn (pointIdx sigma n x)).2 x hx
  clear hgrid
  have hcollar : ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ sigma : Shift,
        MeasurableSet {x : SpatialCoordinates d |
          x ∈ Q ∧ ¬ closure (parent sigma n (pointIdx sigma n x)) ⊆ Q} ∧
        (mu {x : SpatialCoordinates d |
          x ∈ Q ∧ ¬ closure (parent sigma n (pointIdx sigma n x)) ⊆ Q}).toReal ≤
          epscoll * (mu Q).toReal := by
    simpa [L, Shift, shift, side, lo, cell, parentIdx, parent, pointIdx, Q] using
      (_root_.SubdiffusiveProcess.Paper.lem_mass_interior_collar d H1 Mm hd hH1 hMm zQ rQ hrQ mu
        hsupp hQpositive epscoll hepscoll)
  rcases hcollar with ⟨Ncollar, hNcollar, hcollar_spec⟩
  have hnonD : ∀ sigma : Shift, ∀ n : ℕ, 1 ≤ n →
      (mu (⋃ k ∈ {k : Fin d → Int |
        L ^ ((d : ℝ) + zeta) * (mu (cell sigma n k)).toReal <
          (mu (parent sigma n k)).toReal}, cell sigma n k)).toReal ≤
        L ^ (-zeta) * (mu Q).toReal := by
    intro sigma n hn
    exact _root_.SubdiffusiveProcess.Paper.lem_mass_nondoubling d H1 Mm hd hH1 hMm zeta hzeta zQ rQ hrQ mu
      hsupp sigma n hn
  have hpad : ∀ n : ℕ, 1 ≤ n →
      (∑ sigma : Shift, (mu {x : SpatialCoordinates d |
        x ∈ Q ∧ nonPadded sigma n x}).toReal) ≤
        ((2 * (d : ℝ) * (Cwidth + 2)) * L ^ (gamma - 1) *
          (mu Q).toReal) * (Mm : ℝ) ^ d := by
    intro n hn
    have h := (_root_.SubdiffusiveProcess.Paper.lem_shifts d H1 Mm (by omega) hH1 hMm gamma hgamma Cwidth
      hCwidth hcop hMgam).2 mu zQinst zQ rQ hrQ n hn
    simpa only [L, Q, nonPadded, pointIdx, parent, parentIdx, cell, lo, side, shift, Shift]
      using (div_le_iff₀ (by positivity : (0 : ℝ) < (Mm : ℝ) ^ d)).mp h
  let K : Shift → ℕ → Finset (Fin d → Int) :=
    fun sigma n => (hgrid_finite sigma n).toFinset
  let qualifies : Shift → ℕ → (Fin d → Int) → Prop :=
    fun sigma n k => Good sigma n k ∧ padded sigma n k ∧
      closure (parent sigma n k) ⊆ Q ∧
      (mu (parent sigma n k)).toReal ≤
        L ^ ((d : ℝ) + zeta) * (mu (cell sigma n k)).toReal
  let GoodSet : ℕ → Shift → Set (SpatialCoordinates d) :=
    fun n sigma => ⋃ k ∈ (K sigma n).filter (qualifies sigma n), cell sigma n k
  let BadSet : ℕ → Shift → Set (SpatialCoordinates d) :=
    fun n sigma => Q ∩ ⋃ k ∈ (K sigma n).filter (fun k => ¬ Good sigma n k), cell sigma n k
  let PadSet : ℕ → Shift → Set (SpatialCoordinates d) :=
    fun n sigma => Q ∩ ⋃ k ∈ (K sigma n).filter (fun k => ¬ padded sigma n k), cell sigma n k
  let CollarSet : ℕ → Shift → Set (SpatialCoordinates d) :=
    fun n sigma => {x | x ∈ Q ∧ ¬ closure (parent sigma n (pointIdx sigma n x)) ⊆ Q}
  let NDSet : ℕ → Shift → Set (SpatialCoordinates d) :=
    fun n sigma => ⋃ k ∈ {k : Fin d → Int |
      L ^ ((d : ℝ) + zeta) * (mu (cell sigma n k)).toReal <
        (mu (parent sigma n k)).toReal}, cell sigma n k
  have hKmem (sigma : Shift) (n : ℕ) (k : Fin d → Int) :
      k ∈ K sigma n ↔ (cell sigma n k ∩ Q).Nonempty := by
    exact Set.Finite.mem_toFinset (hgrid_finite sigma n)
  clear_value K
  clear hgrid_finite
  have hGood_meas (n : ℕ) (sigma : Shift) : MeasurableSet (GoodSet n sigma) := by
    apply Finset.measurableSet_biUnion
    intro k hk
    exact hgrid_meas sigma n k
  have hBad_meas (n : ℕ) (sigma : Shift) : MeasurableSet (BadSet n sigma) := by
    apply hQmeas.inter
    apply Finset.measurableSet_biUnion
    intro k hk
    exact hgrid_meas sigma n k
  have hPad_meas (n : ℕ) (sigma : Shift) : MeasurableSet (PadSet n sigma) := by
    apply hQmeas.inter
    apply Finset.measurableSet_biUnion
    intro k hk
    exact hgrid_meas sigma n k
  have hND_meas (n : ℕ) (sigma : Shift) : MeasurableSet (NDSet n sigma) := by
    apply MeasurableSet.iUnion
    intro k
    apply MeasurableSet.iUnion
    intro hk'
    exact hgrid_meas sigma n k
  have hCollar_meas (n : ℕ) (sigma : Shift) (hn : Ncollar ≤ n) :
      MeasurableSet (CollarSet n sigma) := by
    exact (hcollar_spec n hn sigma).1
  clear hgrid_meas
  have hpadset_eq (n : ℕ) (hn : 1 ≤ n) (sigma : Shift) :
      PadSet n sigma = {x : SpatialCoordinates d | x ∈ Q ∧ nonPadded sigma n x} := by
    ext x
    constructor
    · intro hx
      rcases hx.2 with hxunion
      simp only [Set.mem_iUnion] at hxunion
      rcases hxunion with ⟨k, hxunion⟩
      rcases hxunion with ⟨hk, hxcell⟩
      have hnot : ¬ padded sigma n k := by
        exact (Finset.mem_filter.mp hk).2
      have hki : k = pointIdx sigma n x := (hgrid_mem sigma n x k).mp hxcell
      subst k
      have hp := hpoint_parent sigma n hn x
      dsimp [padded] at hnot
      change x ∈ Q ∧ nonPadded sigma n x
      rw [← hp] at hnot
      refine ⟨hx.1, ?_⟩
      simpa only [not_forall, not_and_or, not_lt] using hnot
    · intro hx
      change x ∈ Q ∧ nonPadded sigma n x at hx
      have hkcell : x ∈ cell sigma n (pointIdx sigma n x) :=
        (hgrid_mem sigma n x (pointIdx sigma n x)).2 rfl
      have hkK : pointIdx sigma n x ∈ K sigma n := by
        apply (hKmem sigma n _).2
        exact ⟨x, hkcell, hx.1⟩
      have hp : ¬ padded sigma n (pointIdx sigma n x) := by
        intro hpad
        simp only [padded] at hpad
        rw [← hpoint_parent sigma n hn x] at hpad
        rcases hx.2 with ⟨i, hi | hi⟩
        · linarith [(hpad i).1]
        · linarith [(hpad i).2]
      refine ⟨hx.1, ?_⟩
      refine Set.mem_iUnion.2 ⟨pointIdx sigma n x, ?_⟩
      refine Set.mem_iUnion.2 ⟨Finset.mem_filter.mpr ⟨hkK, hp⟩, hkcell⟩
  have hpadset_meas' (n : ℕ) (hn : 1 ≤ n) (sigma : Shift) :
      MeasurableSet {x : SpatialCoordinates d | x ∈ Q ∧ nonPadded sigma n x} := by
    rw [← hpadset_eq n hn sigma]
    exact hPad_meas n sigma
  clear hpadset_meas'
  have hbad_mem (n : ℕ) (sigma : Shift) (x : SpatialCoordinates d) (hx : x ∈ Q) :
      x ∈ BadSet n sigma ↔ ¬ Good sigma n (pointIdx sigma n x) := by
    constructor
    · intro hxm
      rcases hxm.2 with hxunion
      simp only [Set.mem_iUnion] at hxunion
      rcases hxunion with ⟨k, hxunion⟩
      rcases hxunion with ⟨hk, hxcell⟩
      have hng : ¬ Good sigma n k := (Finset.mem_filter.mp hk).2
      rw [← (hgrid_mem sigma n x k).mp hxcell]
      exact hng
    · intro hng
      have hxcell : x ∈ cell sigma n (pointIdx sigma n x) :=
        (hgrid_mem sigma n x (pointIdx sigma n x)).2 rfl
      have hkK : pointIdx sigma n x ∈ K sigma n := by
        apply (hKmem sigma n _).2
        exact ⟨x, hxcell, hx⟩
      refine ⟨hx, ?_⟩
      refine Set.mem_iUnion.2 ⟨pointIdx sigma n x, ?_⟩
      refine Set.mem_iUnion.2 ⟨Finset.mem_filter.mpr ⟨hkK, hng⟩, hxcell⟩
  have hbad_integrated (sigma : Shift) (J : ℕ) (hJ : 1 ≤ J) :=
    aux_lem_mass_bad_integrate (mu := mu) (Q := Q)
      (BadSet := fun n => BadSet n sigma) theta (B sigma) htheta (hB sigma)
      (hBad_meas := fun n => hBad_meas n sigma)
      (hBad_sub := by
        intro n x hx
        change x ∈ Q ∩ _ at hx
        exact hx.1)
      (P := fun n x => Good sigma n (pointIdx sigma n x))
      (hmem := fun n x hx => hbad_mem n sigma x hx)
      (hbad := fun x hx J => hbad sigma x hx J) J hJ
  clear hbad hfaces hsupp hQpositive hcop hMgam hgrid_parent
  let sigma0 : Shift := fun _ => ⟨0, by omega⟩
  let : Nonempty Shift := ⟨sigma0⟩
  let Bbar : ℝ := (Finset.univ : Finset Shift).sup' Finset.univ_nonempty B
  have hBbar : 0 ≤ Bbar := by
    exact le_trans (hB sigma0) (Finset.le_sup' B (Finset.mem_univ sigma0))
  have hB_le (sigma : Shift) : B sigma ≤ Bbar :=
    by
      change B sigma ≤ (Finset.univ : Finset Shift).sup' Finset.univ_nonempty B
      exact Finset.le_sup' B (Finset.mem_univ sigma)
  let J0 : ℕ := max n0 (Nat.ceil (16 * Bbar) + 1)
  have hJ0big : 16 * Bbar < (J0 : ℝ) := by
    have hc : 16 * Bbar ≤ (Nat.ceil (16 * Bbar) : ℝ) := Nat.le_ceil _
    have hm : Nat.ceil (16 * Bbar) + 1 ≤ J0 := by
      exact Nat.le_max_right _ _
    have hstrict : 16 * Bbar < (Nat.ceil (16 * Bbar) : ℝ) + 1 := by
      exact hc.trans_lt (by norm_num)
    have hmr : (Nat.ceil (16 * Bbar) : ℝ) + 1 ≤ (J0 : ℝ) := by
      exact_mod_cast hm
    exact hstrict.trans_le hmr
  let Ncut : ℕ := max Ncollar n0
  have hNcut_coll : Ncollar ≤ Ncut := Nat.le_max_left _ _
  have hNcut_n0 : n0 ≤ Ncut := Nat.le_max_right _ _
  have hfav := _root_.SubdiffusiveProcess.Paper.lem_mass_favourable_horizons Uset hU Ncut J0
    (1 / 16 : ℝ) (by norm_num)
  rcases hfav with ⟨J, hJcut, hJpos, hJcutoff, hJcount⟩
  have hn0J : n0 ≤ J := le_trans (Nat.le_max_left _ _) hJcut
  have hJbig : 16 * Bbar < (J : ℝ) := by
    have hJ0r : (J0 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJcut
    exact lt_of_lt_of_le hJ0big hJ0r
  let levels : Finset ℕ := (Finset.Icc Ncut J).filter Uset
  have hlevels_sub : ∀ ⦃n : ℕ⦄, n ∈ levels → 1 ≤ n ∧ n ≤ J := by
    intro n hn
    change n ∈ (Finset.Icc Ncut J).filter Uset at hn
    have hn' := (Finset.mem_filter.mp hn).1
    have hn'' := Finset.mem_Icc.mp hn'
    have hcut : 1 ≤ Ncut := le_trans hNcollar hNcut_coll
    exact ⟨le_trans hcut hn''.1, hn''.2⟩
  have hlevels_one : ∀ n ∈ levels, 1 ≤ n := by
    intro n hn
    exact (hlevels_sub hn).1
  have hlevels_cut : ∀ n ∈ levels, Ncollar ≤ n := by
    intro n hn
    have hncut : Ncut ≤ n := by
      change n ∈ (Finset.Icc Ncut J).filter Uset at hn
      exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    exact le_trans hNcut_coll hncut
  have hlevels_card :
      ((1 / 2 - (1 / 16 : ℝ)) * (J : ℝ)) ≤ (levels.card : ℝ) := by
    have heq0 : Nat.card {n : ℕ // Ncut ≤ n ∧ 1 ≤ n ∧ n ≤ J ∧ Uset n} =
        Nat.card {n : ℕ // n ∈ levels} := by
      apply Nat.card_congr
      exact Equiv.subtypeEquivRight (by
        intro n
        constructor
        · rintro ⟨h1, h2, h3, h4⟩
          change n ∈ (Finset.Icc Ncut J).filter Uset
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1, h3⟩, h4⟩
        · intro hn
          change n ∈ levels at hn
          change n ∈ (Finset.Icc Ncut J).filter Uset at hn
          rcases Finset.mem_filter.mp hn with ⟨hnI, hU⟩
          rcases Finset.mem_Icc.mp hnI with ⟨h1, h3⟩
          exact ⟨h1, by omega, h3, hU⟩)
    have heq1 : Nat.card {n : ℕ // n ∈ levels} = levels.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    have heq : Nat.card {n : ℕ // Ncut ≤ n ∧ 1 ≤ n ∧ n ≤ J ∧ Uset n} =
        levels.card := heq0.trans heq1
    rw [← heq]
    exact hJcount
  have hbad_level (sigma : Shift) :
      (∑ n ∈ levels, (mu (BadSet n sigma)).toReal) ≤
        (theta * (J : ℝ) + Bbar) * (mu Q).toReal := by
    calc
      (∑ n ∈ levels, (mu (BadSet n sigma)).toReal) ≤
          ∑ n ∈ Finset.Icc 1 J, (mu (BadSet n sigma)).toReal := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
              (fun n hn => Finset.mem_Icc.mpr (hlevels_sub hn))
              (fun n hn hns => ENNReal.toReal_nonneg)
      _ ≤ (theta * (J : ℝ) + B sigma) * (mu Q).toReal :=
        hbad_integrated sigma J hJpos
      _ ≤ (theta * (J : ℝ) + Bbar) * (mu Q).toReal := by
        apply mul_le_mul_of_nonneg_right
        · simpa [add_comm] using add_le_add_right (hB_le sigma) (theta * (J : ℝ))
        · exact ENNReal.toReal_nonneg
  clear hB_le hbad_integrated
  have hnd_level (sigma : Shift) :
      (∑ n ∈ levels, (mu (NDSet n sigma)).toReal) ≤
        (levels.card : ℝ) * L ^ (-zeta) * (mu Q).toReal := by
    calc
      (∑ n ∈ levels, (mu (NDSet n sigma)).toReal) ≤
          ∑ n ∈ levels, L ^ (-zeta) * (mu Q).toReal := by
            apply Finset.sum_le_sum
            intro n hn
            exact hnonD sigma n (hlevels_one n hn)
      _ = (levels.card : ℝ) * L ^ (-zeta) * (mu Q).toReal := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  have hcollar_level (sigma : Shift) :
      (∑ n ∈ levels, (mu (CollarSet n sigma)).toReal) ≤
        (levels.card : ℝ) * epscoll * (mu Q).toReal := by
    calc
      (∑ n ∈ levels, (mu (CollarSet n sigma)).toReal) ≤
          ∑ n ∈ levels, epscoll * (mu Q).toReal := by
            apply Finset.sum_le_sum
            intro n hn
            exact (hcollar_spec n (hlevels_cut n hn) sigma).2
      _ = (levels.card : ℝ) * epscoll * (mu Q).toReal := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  let padCoeff : ℝ := 2 * (d : ℝ) * (Cwidth + 2) * L ^ (gamma - 1)
  let qQ : ℝ := (mu Q).toReal
  have hpad_total :
      (∑ sigma : Shift, ∑ n ∈ levels, (mu (PadSet n sigma)).toReal) ≤
        (Fintype.card Shift : ℝ) * (levels.card : ℝ) *
          padCoeff * qQ := by
    exact (aux_lem_mass_pad_total_reparam
      (mu := mu) (levels := levels) (PadSet := PadSet)
      (NonPad := fun n sigma => {x : SpatialCoordinates d |
        x ∈ Q ∧ nonPadded sigma n x})
      (hlevels := fun n hn => hlevels_one n hn) (heq := hpadset_eq)
      (a := 2 * (d : ℝ) * (Cwidth + 2) * L ^ (gamma - 1))
      (q := (mu Q).toReal)
      (padCoeff := padCoeff) (qQ := qQ) (M := (Mm : ℝ)) (d := d)
      (ha := rfl) (hq := rfl)
      (hcard := hcardShift)
      (hpad := by
        intro n hn
        exact hpad n (hlevels_one n hn)))
  have hcover (n : ℕ) (hn : n ∈ levels) (sigma : Shift) :
      Q ⊆ GoodSet n sigma ∪ BadSet n sigma ∪ NDSet n sigma ∪
        PadSet n sigma ∪ CollarSet n sigma := by
    intro x hx
    simp only [Set.mem_union]
    by_cases hb : x ∈ BadSet n sigma
    · simp only [hb, or_true, true_or]
    by_cases hc : x ∈ CollarSet n sigma
    · simp only [hb, hc, or_true]
    by_cases hp : x ∈ PadSet n sigma
    · simp only [hb, hc, hp, or_true, true_or]
    by_cases hd : x ∈ NDSet n sigma
    · simp only [hb, hc, hp, hd, or_true, true_or]
    have hkcell : x ∈ cell sigma n (pointIdx sigma n x) :=
      (hgrid_mem sigma n x (pointIdx sigma n x)).2 rfl
    have hkK : pointIdx sigma n x ∈ K sigma n := by
      apply (hKmem sigma n _).2
      exact ⟨x, hkcell, hx⟩
    have hgood : Good sigma n (pointIdx sigma n x) := by
      by_contra hng
      exact hb ((hbad_mem n sigma x hx).2 hng)
    have hpadpoint : padded sigma n (pointIdx sigma n x) := by
      by_contra hnp
      apply hp
      rw [hpadset_eq n (hlevels_one n hn) sigma]
      refine ⟨hx, ?_⟩
      dsimp [padded] at hnp
      rw [← hpoint_parent sigma n (hlevels_one n hn) x] at hnp
      simpa only [not_forall, not_and_or, not_lt] using hnp
    have hparent : closure (parent sigma n (pointIdx sigma n x)) ⊆ Q := by
      by_contra hnot
      apply hc
      exact ⟨hx, hnot⟩
    have hnd : (mu (parent sigma n (pointIdx sigma n x))).toReal ≤
          L ^ ((d : ℝ) + zeta) *
            (mu (cell sigma n (pointIdx sigma n x))).toReal := by
      by_contra hnot
      apply hd
      have hlt : L ^ ((d : ℝ) + zeta) *
            (mu (cell sigma n (pointIdx sigma n x))).toReal <
            (mu (parent sigma n (pointIdx sigma n x))).toReal :=
        lt_of_not_ge hnot
      change x ∈ ⋃ k ∈ {k : Fin d → Int |
        L ^ ((d : ℝ) + zeta) * (mu (cell sigma n k)).toReal <
          (mu (parent sigma n k)).toReal}, cell sigma n k
      exact Set.mem_iUnion.2 ⟨pointIdx sigma n x,
        Set.mem_iUnion.2 ⟨hlt, hkcell⟩⟩
    have hkqual : pointIdx sigma n x ∈
        (K sigma n).filter (qualifies sigma n) := by
      exact Finset.mem_filter.mpr ⟨hkK, ⟨hgood, hpadpoint, hparent, hnd⟩⟩
    have hgoodmem : x ∈ GoodSet n sigma := by
      change x ∈ ⋃ k ∈ (K sigma n).filter (qualifies sigma n), cell sigma n k
      exact Set.mem_iUnion.2 ⟨pointIdx sigma n x,
        Set.mem_iUnion.2 ⟨hkqual, hkcell⟩⟩
    simp only [hgoodmem, true_or]
  let CollarLoss : ℕ → Shift → Set (SpatialCoordinates d) :=
    fun m τ => if h : Ncollar ≤ m then CollarSet m τ else ∅
  have hCollarLoss_meas (m : ℕ) (τ : Shift) :
      MeasurableSet (CollarLoss m τ) := by
    by_cases hm : Ncollar ≤ m
    · simp only [CollarLoss, dite_eq_left hm]
      exact hCollar_meas m τ hm
    · simp only [CollarLoss, dite_eq_right hm]
      exact MeasurableSet.empty
  have hcover' (m : ℕ) (hm : m ∈ levels) (τ : Shift) :
      Q ⊆ GoodSet m τ ∪ BadSet m τ ∪ NDSet m τ ∪
        PadSet m τ ∪ CollarLoss m τ := by
    have hmc : Ncollar ≤ m := hlevels_cut m hm
    simpa only [CollarLoss, dite_eq_left hmc] using hcover m hm τ
  have hcollar_level' (τ : Shift) :
      (∑ m ∈ levels, (mu (CollarLoss m τ)).toReal) ≤
        (levels.card : ℝ) * epscoll * (mu Q).toReal := by
    calc
      (∑ m ∈ levels, (mu (CollarLoss m τ)).toReal) =
          ∑ m ∈ levels, (mu (CollarSet m τ)).toReal := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [show CollarLoss m τ = CollarSet m τ by
              simp only [CollarLoss, dite_eq_left (hlevels_cut m hm)]]
      _ ≤ (levels.card : ℝ) * epscoll * (mu Q).toReal := hcollar_level τ
  have hJnat : 0 < J := lt_of_lt_of_le Nat.zero_lt_one hJpos
  have hJr : 0 < (J : ℝ) := Nat.cast_pos.mpr hJnat
  have hBquot : Bbar / (J : ℝ) < (1 / 16 : ℝ) := by
    exact aux_lem_mass_Bquot hJr hJbig
  have hdeficit : (J : ℝ) / 2 - (1 / 16 : ℝ) * (J : ℝ) ≤
      (levels.card : ℝ) := by
    exact aux_lem_mass_deficit hlevels_card
  have hparentRate : 0 ≤ L ^ (-zeta) := by positivity
  have hpaddingRate : 0 ≤ padCoeff := by
    dsimp [padCoeff]
    positivity
  have havg := _root_.SubdiffusiveProcess.Paper.lem_mass_average
    (SpatialCoordinates d) mu Q hQmeas Shift J (by omega) levels
    (by
      intro n hn
      exact Finset.mem_Icc.mpr (hlevels_sub hn))
    ((1 / 16 : ℝ) * (J : ℝ)) hdeficit
    GoodSet BadSet NDSet PadSet CollarLoss
    hGood_meas hBad_meas hND_meas hPad_meas hCollarLoss_meas
    hcover' theta (L ^ (-zeta)) padCoeff epscoll Bbar htheta hparentRate
    hpaddingRate (le_of_lt hepscoll) hBbar hbad_level hnd_level hpad_total
    hcollar_level'
  have havg' :
      (1 / 2 - theta - L ^ (-zeta) - padCoeff - epscoll -
          Bbar / (J : ℝ) - ((1 / 16 : ℝ) * (J : ℝ)) / (J : ℝ)) * qQ ≤
        (∑ sigma : Shift, ∑ n ∈ levels, (mu (GoodSet n sigma)).toReal) /
          ((J : ℝ) * (Fintype.card Shift : ℝ)) := by
    simpa [qQ] using havg
  have hcoef : (1 / 4 : ℝ) <
      1 / 2 - theta - L ^ (-zeta) - padCoeff - epscoll -
        Bbar / (J : ℝ) - ((1 / 16 : ℝ) * (J : ℝ)) / (J : ℝ) := by
    have hloss' : theta + L ^ (-zeta) + padCoeff + epscoll ≤ (1 / 8 : ℝ) := by
      simpa [padCoeff] using hloss
    exact aux_lem_mass_coefficient hJr hBquot hloss'
  have hgood_lower :
      qQ / 4 <
        (∑ sigma : Shift, ∑ n ∈ levels, (mu (GoodSet n sigma)).toReal) /
          ((J : ℝ) * (Fintype.card Shift : ℝ)) := by
    have hcoefq : qQ / 4 <
        (1 / 2 - theta - L ^ (-zeta) - padCoeff - epscoll -
          Bbar / (J : ℝ) - ((1 / 16 : ℝ) * (J : ℝ)) / (J : ℝ)) * qQ := by
      exact aux_lem_mass_pos_mul hcoef hQpos
    exact hcoefq.trans_le havg'
  have hcardlevels : levels.card ≤ J := by
    have hc := Finset.card_le_card
      (s := levels) (t := Finset.Icc 1 J)
      (fun n hn => Finset.mem_Icc.mpr (hlevels_sub hn))
    simpa [Nat.card_Icc] using hc
  have hlev_n0 : ∀ m ∈ levels, n0 ≤ m := by
    intro m hm
    change m ∈ (Finset.Icc Ncut J).filter Uset at hm
    exact le_trans hNcut_n0 (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).1
  have hlev_U : ∀ m ∈ levels, Uset m := by
    intro m hm
    change m ∈ (Finset.Icc Ncut J).filter Uset at hm
    exact (Finset.mem_filter.mp hm).2
  by_contra hnone
  have hbound : ∀ m ∈ levels, ∀ τ : Shift,
      (mu (GoodSet m τ)).toReal ≤ qQ / 4 := by
    intro m hm τ
    by_contra hnot
    have hgt : qQ / 4 < (mu (GoodSet m τ)).toReal := lt_of_not_ge hnot
    apply hnone
    refine ⟨m, hlev_n0 m hm, hlevels_one m hm, hlev_U m hm, τ,
      (K τ m).filter (qualifies τ m), ?_, ?_⟩
    · intro k hk
      exact (Finset.mem_filter.mp hk).2
    · have hmass : qQ / 4 <
          (mu (⋃ k ∈ (K τ m).filter (qualifies τ m), cell τ m k)).toReal := by
        change qQ / 4 < (mu (GoodSet m τ)).toReal
        exact hgt
      dsimp [qQ] at hmass ⊢
      have hcap : qQ / 8 ≤
          (mu (⋃ k ∈ (K τ m).filter (qualifies τ m), cell τ m k)).toReal :=
        aux_lem_mass_capture hQpos hmass
      simpa only [qQ] using hcap
  have hcardr : (levels.card : ℝ) ≤ (J : ℝ) := by
    exact_mod_cast hcardlevels
  exact aux_lem_mass_no_large_sum qQ (J : ℝ) levels
    (fun τ m => (mu (GoodSet m τ)).toReal) hQpos hJr hcardr hgood_lower hbound

end
end SubdiffusiveProcess.Paper
