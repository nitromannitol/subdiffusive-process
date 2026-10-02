import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Paper.shift_strip_residues
import SubdiffusiveProcess.Paper.shift_union_bound
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic

open MeasureTheory Set
open SubdiffusiveProcess
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem aux_lem_shifts_collapse
    (d Mm : ℕ) (gamma Cwidth L : ℝ)
    (hgamma : gamma ∈ Ioo (0 : ℝ) 1) (hCwidth : 0 < Cwidth)
    (hL : 2 ≤ L)
    (hMgam : (Mm : ℝ) ^ (-1 : ℝ) ≤ L ^ (gamma - 1)) :
    2 * (d : ℝ) * ((Cwidth * L ^ gamma + 1) / L + 1 / (Mm : ℝ)) ≤
      2 * (d : ℝ) * (Cwidth + 2) * L ^ (gamma - 1) := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hL1 : (1 : ℝ) ≤ L := le_trans (by norm_num) hL
  have hLg : L ^ (gamma - 1) = L ^ gamma / L := by
    rw [Real.rpow_sub hLpos, Real.rpow_one]
  have hinvL : 1 / L ≤ L ^ (gamma - 1) := by
    have h := Real.rpow_le_rpow_of_exponent_le hL1
      (show (-(1 : ℝ)) ≤ gamma - 1 by linarith [hgamma.1])
    rwa [Real.rpow_neg_one, ← one_div] at h
  have hMgam' : 1 / (Mm : ℝ) ≤ L ^ (gamma - 1) := by
    simpa [Real.rpow_neg_one, one_div] using hMgam
  have hsum : (Cwidth * L ^ gamma + 1) / L + 1 / (Mm : ℝ) ≤
      (Cwidth + 2) * L ^ (gamma - 1) := by
    have hwL : (Cwidth * L ^ gamma + 1) / L =
        Cwidth * L ^ (gamma - 1) + 1 / L := by
      calc
        (Cwidth * L ^ gamma + 1) / L =
            Cwidth * (L ^ gamma / L) + 1 / L := by ring
        _ = Cwidth * L ^ (gamma - 1) + 1 / L := by rw [hLg]
    rw [hwL]
    calc
      Cwidth * L ^ (gamma - 1) + 1 / L + 1 / (Mm : ℝ) ≤
          Cwidth * L ^ (gamma - 1) + L ^ (gamma - 1) +
            L ^ (gamma - 1) := by linarith only [hinvL, hMgam']
      _ = (Cwidth + 2) * L ^ (gamma - 1) := by ring
  have hd0 : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
  calc
    2 * (d : ℝ) * ((Cwidth * L ^ gamma + 1) / L + 1 / (Mm : ℝ)) ≤
        2 * (d : ℝ) * ((Cwidth + 2) * L ^ (gamma - 1)) :=
      mul_le_mul_of_nonneg_left hsum hd0
    _ = 2 * (d : ℝ) * (Cwidth + 2) * L ^ (gamma - 1) := by ring

theorem aux_lem_shifts_count_rewrite (u L Mm : ℝ) :
    2 * ((u / L) * Mm + 1) =
      2 * (u * Mm / L + 1) := by
  ring

theorem aux_lem_shifts_finset_div_card_mono {α : Type}
    (s t : Finset α) (c : ℝ) (hst : s ⊆ t) (hc : 0 ≤ c) :
    (s.card : ℝ) / c ≤ (t.card : ℝ) / c := by
  exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hst) hc

theorem aux_lem_shifts_one_count
    (d Mm : ℕ) (hMm : 2 ≤ Mm) (L w : ℝ)
    (nonPadded : (Fin d → Fin Mm) → ℕ → (Fin d → ℝ) → Prop)
    (badOf : ℕ → (Fin d → ℝ) → Fin d → Finset (Fin Mm))
    (n : ℕ) (x : Fin d → ℝ)
    (hbadcount : ∀ i : Fin d,
      ((badOf n x i).card : ℝ) ≤
        2 * ((w + 1) * (Mm : ℝ) / L + 1))
    (hsub : ∀ s : Fin d → Fin Mm, nonPadded s n x →
      ∃ i : Fin d, s i ∈ badOf n x i) :
    ((Nat.card {sigma : Fin d → Fin Mm // nonPadded sigma n x}) : ℝ) /
        (Mm : ℝ) ^ d ≤
      2 * (d : ℝ) * ((w + 1) / L + 1 / (Mm : ℝ)) := by
  classical
  let Snp : Finset (Fin d → Fin Mm) :=
    Finset.univ.filter (fun s : Fin d → Fin Mm => nonPadded s n x)
  let Sun : Finset (Fin d → Fin Mm) :=
    Finset.univ.filter (fun s : Fin d → Fin Mm =>
      ∃ i : Fin d, s i ∈ badOf n x i)
  have hSsub : Snp ⊆ Sun := by
    intro s hs
    have hs' : nonPadded s n x := by
      change s ∈ Finset.univ.filter
        (fun s : Fin d → Fin Mm => nonPadded s n x) at hs
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hs
    have hex := hsub s hs'
    change s ∈ Finset.univ.filter (fun s : Fin d → Fin Mm =>
      ∃ i : Fin d, s i ∈ badOf n x i)
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hex
  have hcard_sub :
      Nat.card {sigma : Fin d → Fin Mm // nonPadded sigma n x} = Snp.card := by
    rw [Nat.card_eq_fintype_card]
    apply Fintype.card_of_subtype
    intro s
    change (s ∈ Finset.univ.filter
      (fun s : Fin d → Fin Mm => nonPadded s n x)) ↔ nonPadded s n x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hden : (0 : ℝ) ≤ (Mm : ℝ) ^ d := by
    positivity
  rw [hcard_sub]
  calc
    (Snp.card : ℝ) / (Mm : ℝ) ^ d ≤ (Sun.card : ℝ) / (Mm : ℝ) ^ d :=
      aux_lem_shifts_finset_div_card_mono Snp Sun ((Mm : ℝ) ^ d) hSsub hden
    _ ≤ 2 * (d : ℝ) * ((w + 1) / L + 1 / (Mm : ℝ)) := by
      simpa only [Sun] using
        (shift_union_bound d Mm hMm L w (badOf n x) hbadcount)

theorem aux_lem_shifts_measure_bound
    {α X : Type*} [Fintype α] [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu]
    (Q : Set X) (B : α → X → Prop) (D C : ℝ)
    (hD : 0 < D) (hC : 0 ≤ C) (hQ : MeasurableSet Q)
    (hA : ∀ a : α, MeasurableSet {x : X | x ∈ Q ∧ B a x})
    (hpoint : ∀ x : X, x ∈ Q →
      ((Nat.card {a : α // B a x} : ℕ) : ℝ) / D ≤ C) :
    (∑ a : α, (mu {x : X | x ∈ Q ∧ B a x}).toReal) / D ≤
      C * (mu Q).toReal := by
  classical
  have hcard : ∀ x : X,
      Nat.card {a : α // B a x} =
        (Finset.univ.filter (fun a : α => B a x)).card := by
    intro x
    rw [Nat.card_eq_fintype_card]
    apply Fintype.card_of_subtype
    intro a
    change (a ∈ Finset.univ.filter (fun a : α => B a x)) ↔ B a x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hpoint_indicator : ∀ x : X,
      (∑ a : α, ({x : X | x ∈ Q ∧ B a x} : Set X).indicator
        (fun _ => (1 : ℝ≥0∞)) x) ≤
        ENNReal.ofReal (C * D) *
          Q.indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro x
    by_cases hx : x ∈ Q
    · have hsum :
          (∑ a : α, ({x : X | x ∈ Q ∧ B a x} : Set X).indicator
            (fun _ => (1 : ℝ≥0∞)) x) =
            ((Finset.univ.filter (fun a : α => B a x)).card : ℝ≥0∞) := by
        simp only [Set.indicator, Set.mem_setOf_eq, hx, true_and]
        rw [Finset.sum_boole]
      calc
        (∑ a : α, ({x : X | x ∈ Q ∧ B a x} : Set X).indicator
            (fun _ => (1 : ℝ≥0∞)) x) =
            ((Finset.univ.filter (fun a : α => B a x)).card : ℝ≥0∞) := hsum
        _ ≤ ENNReal.ofReal (C * D) := by
          have hcardR := (div_le_iff₀ hD).mp (hpoint x hx)
          rw [hcard x] at hcardR
          simpa only [ENNReal.ofReal_natCast] using
            ENNReal.ofReal_le_ofReal hcardR
        _ = ENNReal.ofReal (C * D) *
            Q.indicator (fun _ => (1 : ℝ≥0∞)) x := by
          rw [Set.indicator_of_mem hx]
          simp
    · have hnot : ∀ a : α,
          x ∉ ({x : X | x ∈ Q ∧ B a x} : Set X) := by
        intro a ha
        exact hx ha.1
      have hzero :
          (∑ a : α, ({x : X | x ∈ Q ∧ B a x} : Set X).indicator
            (fun _ => (1 : ℝ≥0∞)) x) = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        exact Set.indicator_of_notMem (hnot a) _
      calc
        (∑ a : α, ({x : X | x ∈ Q ∧ B a x} : Set X).indicator
            (fun _ => (1 : ℝ≥0∞)) x) = 0 := hzero
        _ ≤ ENNReal.ofReal (C * D) *
            Q.indicator (fun _ => (1 : ℝ≥0∞)) x := by
          rw [Set.indicator_of_notMem hx]
          simp
  have hmeas : ∀ a : α,
      Measurable (({x : X | x ∈ Q ∧ B a x} : Set X).indicator
        (fun _ => (1 : ℝ≥0∞))) := by
    intro a
    exact measurable_const.indicator (hA a)
  have hI :
      (∑ a : α, mu {x : X | x ∈ Q ∧ B a x}) =
        ∫⁻ x, (∑ a : α,
          ({x : X | x ∈ Q ∧ B a x} : Set X).indicator
            (fun _ => (1 : ℝ≥0∞)) x) ∂mu := by
    rw [MeasureTheory.lintegral_finset_sum]
    · apply Finset.sum_congr rfl
      intro a ha
      exact (MeasureTheory.lintegral_indicator_one (hA a)).symm
    · intro a ha
      exact hmeas a
  have hupper :
      (∫⁻ x, (∑ a : α,
        ({x : X | x ∈ Q ∧ B a x} : Set X).indicator
          (fun _ => (1 : ℝ≥0∞)) x) ∂mu) ≤
        ENNReal.ofReal (C * D) * mu Q := by
    calc
      (∫⁻ x, (∑ a : α,
        ({x : X | x ∈ Q ∧ B a x} : Set X).indicator
          (fun _ => (1 : ℝ≥0∞)) x) ∂mu) ≤
          ∫⁻ x, ENNReal.ofReal (C * D) *
            Q.indicator (fun _ => (1 : ℝ≥0∞)) x ∂mu :=
        MeasureTheory.lintegral_mono hpoint_indicator
      _ = ∫⁻ x, Q.indicator (fun _ => ENNReal.ofReal (C * D)) x ∂mu := by
        apply congrArg (fun f : X → ℝ≥0∞ => ∫⁻ x, f x ∂mu)
        funext x
        by_cases hx : x ∈ Q
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
          simp
        · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
          simp
      _ = ENNReal.ofReal (C * D) * mu Q :=
        MeasureTheory.lintegral_indicator_const hQ _
  have hsumENN :
      (∑ a : α, mu {x : X | x ∈ Q ∧ B a x}) ≤
        ENNReal.ofReal (C * D) * mu Q := hI ▸ hupper
  have htop : ENNReal.ofReal (C * D) * mu Q ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.ofReal_ne_top
    · exact measure_ne_top _ _
  have htr := ENNReal.toReal_mono htop hsumENN
  rw [ENNReal.toReal_sum
      (fun a _ => measure_ne_top mu {x : X | x ∈ Q ∧ B a x}),
    ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg hC hD.le)] at htr
  apply (div_le_iff₀ hD).2
  calc
    (∑ a : α, (mu {x : X | x ∈ Q ∧ B a x}).toReal) ≤
        C * D * (mu Q).toReal := htr
    _ = C * (mu Q).toReal * D := by ring

theorem aux_lem_shifts_lo_measurable
    (d Mm : ℕ) (shift : (Fin d → Fin Mm) → Fin d → ℝ)
    (side : ℕ → ℝ) (sigma : Fin d → Fin Mm) (m : ℕ) (i : Fin d) :
    Measurable (fun x : SpatialCoordinates d =>
      shift sigma i + side m *
        ((Int.floor ((x i - shift sigma i) / side m)) : ℝ)) := by
  measurability

theorem aux_lem_shifts_nonpadded_measurable
    (d Mm : ℕ) (Q : Set (SpatialCoordinates d)) (hQ : MeasurableSet Q)
    (w : ℝ) (side : ℕ → ℝ)
    (lo : (Fin d → Fin Mm) → ℕ → SpatialCoordinates d → Fin d → ℝ)
    (sigma : Fin d → Fin Mm) (n : ℕ)
    (hlo : ∀ m : ℕ, ∀ i : Fin d,
      Measurable (fun x : SpatialCoordinates d => lo sigma m x i)) :
    MeasurableSet {x : SpatialCoordinates d |
      x ∈ Q ∧
        ∃ i : Fin d,
          (lo sigma n x i - lo sigma (n - 1) x i ≤ w * side n) ∨
          (lo sigma (n - 1) x i + side (n - 1) -
            (lo sigma n x i + side n) ≤ w * side n)} := by
  have hleft : ∀ i : Fin d,
      MeasurableSet {x : SpatialCoordinates d |
        lo sigma n x i - lo sigma (n - 1) x i ≤ w * side n} := by
    intro i
    exact measurableSet_le
      ((hlo n i).sub (hlo (n - 1) i)) measurable_const
  have hright : ∀ i : Fin d,
      MeasurableSet {x : SpatialCoordinates d |
        lo sigma (n - 1) x i + side (n - 1) -
            (lo sigma n x i + side n) ≤ w * side n} := by
    intro i
    apply measurableSet_le
    · exact ((hlo (n - 1) i).add measurable_const).sub
        ((hlo n i).add measurable_const)
    · exact measurable_const
  have hbad : MeasurableSet {x : SpatialCoordinates d |
      ∃ i : Fin d,
        (lo sigma n x i - lo sigma (n - 1) x i ≤ w * side n) ∨
        (lo sigma (n - 1) x i + side (n - 1) -
          (lo sigma n x i + side n) ≤ w * side n)} := by
    rw [show {x : SpatialCoordinates d |
        ∃ i : Fin d,
          (lo sigma n x i - lo sigma (n - 1) x i ≤ w * side n) ∨
          (lo sigma (n - 1) x i + side (n - 1) -
            (lo sigma n x i + side n) ≤ w * side n)} =
        ⋃ i : Fin d,
          ({x : SpatialCoordinates d |
            lo sigma n x i - lo sigma (n - 1) x i ≤ w * side n} ∪
            {x : SpatialCoordinates d |
              lo sigma (n - 1) x i + side (n - 1) -
                (lo sigma n x i + side n) ≤ w * side n}) by
      ext x
      simp]
    exact MeasurableSet.iUnion (fun i => (hleft i).union (hright i))
  exact hQ.inter hbad

theorem aux_lem_shifts_count_from_strip
    (d Mm : ℕ) (hMm : 2 ≤ Mm) (L w : ℝ) (hL : 0 < L)
    (hw : 0 ≤ w) (K : ℕ)
    (side : ℕ → ℝ)
    (shift : (Fin d → Fin Mm) → Fin d → ℝ)
    (lo : (Fin d → Fin Mm) → ℕ → SpatialCoordinates d → Fin d → ℝ)
    (nonPadded : (Fin d → Fin Mm) → ℕ → SpatialCoordinates d → Prop)
    (hKcop : Nat.Coprime K Mm)
    (hnon : ∀ (s : Fin d → Fin Mm) (n : ℕ) (x : SpatialCoordinates d),
      nonPadded s n x →
        ∃ i : Fin d,
          (lo s n x i - lo s (n - 1) x i ≤ w * side n) ∨
          (lo s (n - 1) x i + side (n - 1) -
            (lo s n x i + side n) ≤ w * side n))
    (hcoord_strip :
      ∀ (n : ℕ), 1 ≤ n → ∀ (x : SpatialCoordinates d)
        (sigma : Fin d → Fin Mm) (i : Fin d),
        ((lo sigma n x i - lo sigma (n - 1) x i ≤ w * side n) ∨
          (lo sigma (n - 1) x i + side (n - 1) -
            (lo sigma n x i + side n) ≤ w * side n)) →
        ∃ k : ℤ,
          |x i / side (n - 1) - ((K ^ (n - 1) : ℕ) : ℝ) *
              (sigma i : ℕ) / (Mm : ℝ) - (k : ℝ)| ≤ (w + 1) / L)
    (hres_count :
      ∀ (R : ℕ), Nat.Coprime R Mm → ∀ (t delta : ℝ), 0 ≤ delta →
        ∀ (bad : Finset (Fin Mm)),
          (∀ r : Fin Mm, r ∈ bad ↔
            ∃ k : ℤ, |t - (R : ℝ) * (r : ℕ) / (Mm : ℝ) - (k : ℝ)| ≤ delta) →
          (bad.card : ℝ) ≤ 2 * (delta * (Mm : ℝ) + 1)) :
    ∀ (n : ℕ), 1 ≤ n → ∀ (x : SpatialCoordinates d),
      ((Nat.card {sigma : Fin d → Fin Mm // nonPadded sigma n x}) : ℝ) /
          (Mm : ℝ) ^ d ≤
        2 * (d : ℝ) * ((w + 1) / L + 1 / (Mm : ℝ)) := by
  classical
  intro n hn x
  have hMmR : (0 : ℝ) < (Mm : ℝ) := by
    exact_mod_cast (show 0 < Mm by omega)
  have hden : (0 : ℝ) ≤ (Mm : ℝ) ^ d := pow_nonneg hMmR.le d
  let badOf : ℕ → SpatialCoordinates d → Fin d → Finset (Fin Mm) :=
    fun m y i => Finset.univ.filter (fun r =>
      ∃ k : ℤ,
        |y i / side (m - 1) - ((K ^ (m - 1) : ℕ) : ℝ) *
            (r : ℕ) / (Mm : ℝ) - (k : ℝ)| ≤ (w + 1) / L)
  have hRcop : Nat.Coprime (K ^ (n - 1)) Mm := hKcop.pow_left (n - 1)
  have hdelta : 0 ≤ (w + 1) / L := by
    positivity
  have hbadmem : ∀ (i : Fin d) (r : Fin Mm),
      r ∈ badOf n x i ↔
        ∃ k : ℤ,
          |x i / side (n - 1) - ((K ^ (n - 1) : ℕ) : ℝ) *
              (r : ℕ) / (Mm : ℝ) - (k : ℝ)| ≤ (w + 1) / L := by
    intro i r
    change (r ∈ Finset.univ.filter (fun r : Fin Mm =>
      ∃ k : ℤ,
        |x i / side (n - 1) - ((K ^ (n - 1) : ℕ) : ℝ) *
            (r : ℕ) / (Mm : ℝ) - (k : ℝ)| ≤ (w + 1) / L)) ↔ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hbadcount : ∀ i : Fin d,
      ((badOf n x i).card : ℝ) ≤
        2 * ((w + 1) * (Mm : ℝ) / L + 1) := by
    intro i
    have hh := hres_count (K ^ (n - 1)) hRcop
      (x i / side (n - 1)) ((w + 1) / L) hdelta (badOf n x i)
      (fun r => hbadmem i r)
    calc
      ((badOf n x i).card : ℝ) ≤
          2 * (((w + 1) / L) * (Mm : ℝ) + 1) := hh
      _ = 2 * ((w + 1) * (Mm : ℝ) / L + 1) :=
        aux_lem_shifts_count_rewrite (w + 1) L (Mm : ℝ)
  have hsub : ∀ s : Fin d → Fin Mm, nonPadded s n x →
      ∃ i : Fin d, s i ∈ badOf n x i := by
    intro s hs
    rcases hnon s n x hs with ⟨i, hi | hi⟩
    · refine ⟨i, ?_⟩
      exact (hbadmem i (s i)).2 (hcoord_strip n hn x s i (Or.inl hi))
    · refine ⟨i, ?_⟩
      exact (hbadmem i (s i)).2 (hcoord_strip n hn x s i (Or.inr hi))
  simpa only using
    (aux_lem_shifts_one_count d Mm hMm L w nonPadded badOf n x hbadcount hsub)

theorem aux_lem_shifts_residue_count
  (Mm : ℕ) (hMm : 2 ≤ Mm) :
    ∀ (R : ℕ), Nat.Coprime R Mm → ∀ (t delta : ℝ), 0 ≤ delta →
      ∀ (bad : Finset (Fin Mm)),
        (∀ r : Fin Mm, r ∈ bad ↔
          ∃ k : ℤ, |t - (R : ℝ) * (r : ℕ) / (Mm : ℝ) - (k : ℝ)| ≤ delta) →
        (bad.card : ℝ) ≤ 2 * (delta * (Mm : ℝ) + 1) := by
  classical
  intro R hRcop t delta hdelta bad hmem
  have hMpos : 0 < Mm := by omega
  have hMR : (0 : ℝ) < (Mm : ℝ) := by exact_mod_cast hMpos
  have hex : ∀ r : Fin Mm, ∃ k : ℤ, r ∈ bad →
      |t - (R : ℝ) * (r : ℕ) / (Mm : ℝ) - (k : ℝ)| ≤ delta := by
    intro r
    by_cases hr : r ∈ bad
    · obtain ⟨k, hk⟩ := (hmem r).mp hr
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose kf hkf using hex
  set A : ℤ := ⌈(Mm : ℝ) * t - delta * (Mm : ℝ)⌉
  set B : ℤ := ⌊(Mm : ℝ) * t + delta * (Mm : ℝ)⌋
  let F : Fin Mm → ℤ := fun r =>
    (R : ℤ) * (r : ℕ) + (Mm : ℤ) * kf r
  have hmaps : ∀ r ∈ bad, F r ∈ Finset.Icc A B := by
    intro r hr
    have hk := hkf r hr
    rw [abs_le] at hk
    obtain ⟨hk1, hk2⟩ := hk
    have eF : ((F r : ℤ) : ℝ) =
        (R : ℝ) * (r : ℕ) + (Mm : ℝ) * (kf r : ℤ) := by
      simp [F]
    have hmul1 :
        (Mm : ℝ) * t - delta * (Mm : ℝ) ≤
          (R : ℝ) * (r : ℕ) + (Mm : ℝ) * (kf r : ℤ) := by
      have hh := mul_le_mul_of_nonneg_left hk2 (le_of_lt hMR)
      have he : (Mm : ℝ) *
            (t - (R : ℝ) * (r : ℕ) / (Mm : ℝ) - (kf r : ℤ)) =
          (Mm : ℝ) * t - (R : ℝ) * (r : ℕ) -
            (Mm : ℝ) * (kf r : ℤ) := by
        field_simp
      rw [he] at hh
      calc
        (Mm : ℝ) * t - delta * (Mm : ℝ) =
            (Mm : ℝ) * t - (Mm : ℝ) * delta := by ring
        _ ≤ (R : ℝ) * (r : ℕ) + (Mm : ℝ) * (kf r : ℤ) := by
          linarith only [hh]
    have hmul2 :
        (R : ℝ) * (r : ℕ) + (Mm : ℝ) * (kf r : ℤ) ≤
          (Mm : ℝ) * t + delta * (Mm : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hk1 (le_of_lt hMR)
      have he : (Mm : ℝ) *
            (t - (R : ℝ) * (r : ℕ) / (Mm : ℝ) - (kf r : ℤ)) =
          (Mm : ℝ) * t - (R : ℝ) * (r : ℕ) -
            (Mm : ℝ) * (kf r : ℤ) := by
        field_simp
      rw [he] at hh
      calc
        (R : ℝ) * (r : ℕ) + (Mm : ℝ) * (kf r : ℤ) ≤
            (Mm : ℝ) * t + (Mm : ℝ) * delta := by
          linarith only [hh]
        _ = (Mm : ℝ) * t + delta * (Mm : ℝ) := by ring
    apply Finset.mem_Icc.mpr
    constructor
    · rw [show A = ⌈(Mm : ℝ) * t - delta * (Mm : ℝ)⌉ by rfl]
      exact Int.ceil_le.mpr (by simpa [eF] using hmul1)
    · rw [show B = ⌊(Mm : ℝ) * t + delta * (Mm : ℝ)⌋ by rfl]
      exact Int.le_floor.mpr (by simpa [eF] using hmul2)
  have hinj : Set.InjOn F bad := by
    intro r hr r' hr' heq
    have heq' : (R : ℤ) * ((r : ℕ) : ℤ) + (Mm : ℤ) * kf r =
        (R : ℤ) * ((r' : ℕ) : ℤ) + (Mm : ℤ) * kf r' := heq
    rcases le_total (r' : ℕ) (r : ℕ) with hrr | hrr
    · let q : ℕ := (r : ℕ) - (r' : ℕ)
      have hdiff : (R : ℤ) * (q : ℤ) =
          (Mm : ℤ) * (kf r' - kf r) := by
        dsimp [q]
        rw [Nat.cast_sub hrr]
        linarith
      have hdvdZ : (Mm : ℤ) ∣ (R : ℤ) * (q : ℤ) :=
        ⟨kf r' - kf r, hdiff⟩
      have hdvdN : Mm ∣ R * q := by
        apply (Int.natCast_dvd_natCast).mp
        simpa [Nat.cast_mul] using hdvdZ
      have hdvdq : Mm ∣ q := hRcop.symm.dvd_of_dvd_mul_left hdvdN
      have hq_lt : q < Mm := by
        dsimp [q]
        omega
      have hq0 : q = 0 := Nat.eq_zero_of_dvd_of_lt hdvdq hq_lt
      have hval : (r : ℕ) = (r' : ℕ) := by
        dsimp [q] at hq0
        omega
      exact Fin.ext hval
    · let q : ℕ := (r' : ℕ) - (r : ℕ)
      have hdiff : (R : ℤ) * (q : ℤ) =
          (Mm : ℤ) * (kf r - kf r') := by
        dsimp [q]
        rw [Nat.cast_sub hrr]
        linarith
      have hdvdZ : (Mm : ℤ) ∣ (R : ℤ) * (q : ℤ) :=
        ⟨kf r - kf r', hdiff⟩
      have hdvdN : Mm ∣ R * q := by
        apply (Int.natCast_dvd_natCast).mp
        simpa [Nat.cast_mul] using hdvdZ
      have hdvdq : Mm ∣ q := hRcop.symm.dvd_of_dvd_mul_left hdvdN
      have hq_lt : q < Mm := by
        dsimp [q]
        omega
      have hq0 : q = 0 := Nat.eq_zero_of_dvd_of_lt hdvdq hq_lt
      have hval : (r : ℕ) = (r' : ℕ) := by
        dsimp [q] at hq0
        omega
      exact Fin.ext hval
  have hcard : bad.card ≤ (Finset.Icc A B).card :=
    Finset.card_le_card_of_injOn F hmaps hinj
  have hBA : (B : ℝ) - (A : ℝ) ≤ 2 * (delta * (Mm : ℝ)) := by
    have hb : (B : ℝ) ≤ (Mm : ℝ) * t + delta * (Mm : ℝ) :=
      Int.floor_le _
    have ha : (Mm : ℝ) * t - delta * (Mm : ℝ) ≤ (A : ℝ) :=
      Int.le_ceil _
    linarith
  have hIcc : ((Finset.Icc A B).card : ℝ) ≤
      2 * (delta * (Mm : ℝ) + 1) := by
    rw [Int.card_Icc]
    rcases le_or_gt (B + 1 - A) 0 with h | h
    · rw [Int.toNat_of_nonpos h]
      push_cast
      nlinarith [hdelta, hMR]
    · have hz : (((B + 1 - A).toNat : ℕ) : ℤ) = B + 1 - A :=
        Int.toNat_of_nonneg (by omega)
      have hcast : (((B + 1 - A).toNat : ℕ) : ℝ) =
          (B : ℝ) - (A : ℝ) + 1 := by
        have hh := congrArg (fun z : ℤ => (z : ℝ)) hz
        push_cast at hh
        linarith
      rw [hcast]
      linarith [hBA]
  calc
    (bad.card : ℝ) ≤ ((Finset.Icc A B).card : ℝ) := by exact_mod_cast hcard
    _ ≤ 2 * (delta * (Mm : ℝ) + 1) := hIcc

theorem lem_shifts
    (d H1 Mm : ℕ) (hd : 1 ≤ d) (hH1 : 1 ≤ H1) (hMm : 2 ≤ Mm)
    (gamma : ℝ) (hgamma : gamma ∈ Ioo (0 : ℝ) 1)
    (Cwidth : ℝ) (hCwidth : 0 < Cwidth)
    (hcop : Nat.Coprime Mm (3 ^ H1))
    (hMgam : (Mm : ℝ) ^ (-1 : ℝ) ≤ ((3 : ℝ) ^ H1) ^ (gamma - 1)) :
    let L : ℝ := (3 : ℝ) ^ H1
    let w : ℝ := Cwidth * L ^ gamma
    let Cbound : ℝ := (2 : ℝ) * (d : ℝ) * (Cwidth + 2)
    let shift : (Fin d → Fin Mm) → Fin d → ℝ :=
      fun sigma i => (sigma i : ℕ) / (Mm : ℝ)
    let side : ℕ → ℝ := fun n => L ^ (-(n : ℝ))
    let lo : (Fin d → Fin Mm) → ℕ → SpatialCoordinates d → Fin d → ℝ :=
      fun sigma n x i =>
        shift sigma i + side n *
          ((Int.floor ((x i - shift sigma i) / side n)) : ℝ)
    let cell : (Fin d → Fin Mm) → ℕ → SpatialCoordinates d → Set (SpatialCoordinates d) :=
      fun sigma n x => Set.pi Set.univ (fun i =>
        Set.Ico (lo sigma n x i) (lo sigma n x i + side n))
    let nonPadded : (Fin d → Fin Mm) → ℕ → SpatialCoordinates d → Prop :=
      fun sigma n x => ∃ i : Fin d,
        (lo sigma n x i - lo sigma (n - 1) x i ≤ w * side n) ∨
        (lo sigma (n - 1) x i + side (n - 1) -
          (lo sigma n x i + side n) ≤ w * side n)
    (∀ (n : ℕ), 1 ≤ n → ∀ (x : SpatialCoordinates d),
      ((Nat.card {sigma : Fin d → Fin Mm // nonPadded sigma n x}) : ℝ) /
          (Mm : ℝ) ^ d ≤
        2 * (d : ℝ) * ((w + 1) / L + 1 / (Mm : ℝ)) ∧
      2 * (d : ℝ) * ((w + 1) / L + 1 / (Mm : ℝ)) ≤
        Cbound * L ^ (gamma - 1)) ∧
    (∀ (mu : Measure (SpatialCoordinates d)), (_hmu : IsFiniteMeasure mu) →
      ∀ (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ),
        ∀ (n : ℕ), 1 ≤ n →
          (∑ sigma : Fin d → Fin Mm,
            (mu {x : SpatialCoordinates d |
              x ∈ (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) ∧
                nonPadded sigma n x}).toReal) /
              (Mm : ℝ) ^ d ≤
              Cbound * L ^ (gamma - 1) *
              (mu (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))).toReal) := by
  classical
  let L : ℝ := (3 : ℝ) ^ H1
  let w : ℝ := Cwidth * L ^ gamma
  let Cbound : ℝ := (2 : ℝ) * (d : ℝ) * (Cwidth + 2)
  let shift : (Fin d → Fin Mm) → Fin d → ℝ :=
    fun sigma i => (sigma i : ℕ) / (Mm : ℝ)
  let side : ℕ → ℝ := fun n => L ^ (-(n : ℝ))
  let lo : (Fin d → Fin Mm) → ℕ → SpatialCoordinates d → Fin d → ℝ :=
    fun sigma n x i =>
      shift sigma i + side n *
        ((Int.floor ((x i - shift sigma i) / side n)) : ℝ)
  let nonPadded : (Fin d → Fin Mm) → ℕ → SpatialCoordinates d → Prop :=
    fun sigma n x => ∃ i : Fin d,
      (lo sigma n x i - lo sigma (n - 1) x i ≤ w * side n) ∨
      (lo sigma (n - 1) x i + side (n - 1) -
        (lo sigma n x i + side n) ≤ w * side n)
  change
    ((∀ (n : ℕ), 1 ≤ n → ∀ (x : SpatialCoordinates d),
      ((Nat.card {sigma : Fin d → Fin Mm // nonPadded sigma n x}) : ℝ) /
          (Mm : ℝ) ^ d ≤
        2 * (d : ℝ) * ((w + 1) / L + 1 / (Mm : ℝ)) ∧
      2 * (d : ℝ) * ((w + 1) / L + 1 / (Mm : ℝ)) ≤
        Cbound * L ^ (gamma - 1))) ∧
    (∀ (mu : Measure (SpatialCoordinates d)), IsFiniteMeasure mu →
      ∀ (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ),
        ∀ (n : ℕ), 1 ≤ n →
          (∑ sigma : Fin d → Fin Mm,
            (mu {x : SpatialCoordinates d |
              x ∈ (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) ∧
                nonPadded sigma n x}).toReal) /
              (Mm : ℝ) ^ d ≤
            Cbound * L ^ (gamma - 1) *
              (mu (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))).toReal)
  have hL : (2 : ℝ) ≤ L := by
    dsimp [L]
    have hpow : (3 : ℝ) ^ (1 : ℕ) ≤ (3 : ℝ) ^ H1 := by
      exact pow_le_pow_right₀ (by norm_num) hH1
    norm_num at hpow ⊢
    linarith
  have hLpos : (0 : ℝ) < L := by linarith
  let K : ℕ := 3 ^ H1
  have hLK : L = (K : ℝ) := by
    dsimp [L, K]
    norm_num
  have hKpos : 0 < K := by
    dsimp [K]
    positivity
  have hside_pos : ∀ m : ℕ, 0 < side m := by
    intro m
    dsimp [side]
    positivity
  have hside_inv : ∀ m : ℕ, 1 / side m = (K : ℝ) ^ m := by
    intro m
    dsimp [side]
    rw [Real.rpow_neg (le_of_lt hLpos), one_div, inv_inv,
      Real.rpow_natCast]
    rw [hLK]
  have hside_rel : ∀ n : ℕ, 1 ≤ n → side (n - 1) = L * side n := by
    intro n hn
    dsimp [side]
    rw [show (-(n - 1 : ℕ) : ℝ) = (1 : ℝ) + (-(n : ℝ)) by
      rw [Nat.cast_sub (by omega)]
      ring]
    rw [Real.rpow_add hLpos, Real.rpow_one]
  have hcoord_strip :
      ∀ (n : ℕ), 1 ≤ n → ∀ (x : SpatialCoordinates d)
        (sigma : Fin d → Fin Mm) (i : Fin d),
        ((lo sigma n x i - lo sigma (n - 1) x i ≤ w * side n) ∨
          (lo sigma (n - 1) x i + side (n - 1) -
            (lo sigma n x i + side n) ≤ w * side n)) →
        ∃ k : ℤ,
          |x i / side (n - 1) - ((K ^ (n - 1) : ℕ) : ℝ) * (sigma i : ℕ) /
              (Mm : ℝ) -
              (k : ℝ)| ≤ (w + 1) / L := by
    intro n hn x sigma i hbad
    let p : ℝ := side (n - 1)
    let q : ℝ := side n
    let u : ℝ := (x i - shift sigma i) / p
    let v : ℝ := (x i - shift sigma i) / q
    let R : ℕ := K ^ (n - 1)
    let a : ℤ := Int.floor u
    let b : ℤ := Int.floor v
    have hp : 0 < p := by dsimp [p]; exact hside_pos _
    have hq : 0 < q := by dsimp [q]; exact hside_pos _
    have hpq : p = L * q := by
      dsimp [p, q]
      exact hside_rel n hn
    have huv : v = (K : ℝ) * u := by
      dsimp [u, v]
      rw [hpq]
      rw [hLK]
      field_simp
    have hRpos : 0 < R := by
      dsimp [R]
      positivity
    have hpos : x i / p - (R : ℝ) * (sigma i : ℕ) / (Mm : ℝ) = u := by
      dsimp [u, shift, R, p]
      rw [Nat.cast_pow, ← hside_inv]
      field_simp
    have hleft_eq :
        lo sigma n x i - lo sigma (n - 1) x i =
          q * ((b : ℝ) - (K : ℝ) * (a : ℝ)) := by
      change (shift sigma i + q * (b : ℝ)) -
        (shift sigma i + p * (a : ℝ)) = _
      rw [hpq, hLK]
      ring
    have hright_eq :
        lo sigma (n - 1) x i + side (n - 1) -
            (lo sigma n x i + side n) =
          q * ((K : ℝ) * (a : ℝ) + (K : ℝ) - (b : ℝ) - 1) := by
      change (shift sigma i + p * (a : ℝ)) + p -
        ((shift sigma i + q * (b : ℝ)) + q) = _
      rw [hpq, hLK]
      ring
    have hua : (a : ℝ) ≤ u := by
      dsimp [a]
      exact Int.floor_le u
    have hua' : u < (a : ℝ) + 1 := by
      dsimp [a]
      exact Int.lt_floor_add_one u
    have hvb : (b : ℝ) ≤ v := by
      dsimp [b]
      exact Int.floor_le v
    have hvb' : v < (b : ℝ) + 1 := by
      dsimp [b]
      exact Int.lt_floor_add_one v
    rcases hbad with hbad | hbad
    · have hj : (b : ℝ) - (K : ℝ) * (a : ℝ) ≤ w := by
        rw [hleft_eq] at hbad
        nlinarith
      have huupper : (K : ℝ) * (u - (a : ℝ)) ≤ w + 1 := by
        rw [huv] at hvb'
        nlinarith
      have hulo : 0 ≤ u - (a : ℝ) := by linarith
      have huabs : |u - (a : ℝ)| ≤ (w + 1) / (K : ℝ) := by
        rw [abs_of_nonneg hulo]
        apply (le_div_iff₀ (by exact_mod_cast hKpos)).2
        simpa [mul_comm] using huupper
      refine ⟨a, ?_⟩
      have hpos' : x i / side (n - 1) -
          ((K ^ (n - 1) : ℕ) : ℝ) * (sigma i : ℕ) / (Mm : ℝ) = u := by
        simpa [p, R] using hpos
      rw [hpos']
      rw [show (w + 1) / L = (w + 1) / (K : ℝ) by rw [hLK]]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_comm] using huabs
    · have hj : (K : ℝ) * (a : ℝ) + (K : ℝ) - (b : ℝ) - 1 ≤ w := by
        rw [hright_eq] at hbad
        nlinarith
      have hulower : (K : ℝ) * ((a : ℝ) + 1 - u) ≤ w + 1 := by
        rw [huv] at hvb
        nlinarith
      have huupper : 0 ≤ (a : ℝ) + 1 - u := by linarith
      have huabs : |u - ((a : ℝ) + 1)| ≤ (w + 1) / (K : ℝ) := by
        rw [abs_of_nonpos (by linarith : u - ((a : ℝ) + 1) ≤ 0)]
        apply (le_div_iff₀ (by exact_mod_cast hKpos)).2
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_comm] using hulower
      refine ⟨a + 1, ?_⟩
      have hpos' : x i / side (n - 1) -
          ((K ^ (n - 1) : ℕ) : ℝ) * (sigma i : ℕ) / (Mm : ℝ) = u := by
        simpa [p, R] using hpos
      rw [hpos']
      rw [show (w + 1) / L = (w + 1) / (K : ℝ) by rw [hLK]]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_comm] using huabs
  have hres_count := aux_lem_shifts_residue_count Mm hMm
  have hKcop : Nat.Coprime K Mm := by
    simpa [K] using hcop.symm
  have hnon : ∀ (s : Fin d → Fin Mm) (m : ℕ) (y : SpatialCoordinates d),
      nonPadded s m y →
        ∃ i : Fin d,
          (lo s m y i - lo s (m - 1) y i ≤ w * side m) ∨
          (lo s (m - 1) y i + side (m - 1) -
            (lo s m y i + side m) ≤ w * side m) := by
    intro s m y hs
    change ∃ i : Fin d,
      (lo s m y i - lo s (m - 1) y i ≤ w * side m) ∨
        (lo s (m - 1) y i + side (m - 1) -
          (lo s m y i + side m) ≤ w * side m) at hs
    exact hs
  have hcount : ∀ (n : ℕ), 1 ≤ n → ∀ (x : SpatialCoordinates d),
      ((Nat.card {sigma : Fin d → Fin Mm // nonPadded sigma n x}) : ℝ) /
          (Mm : ℝ) ^ d ≤
        2 * (d : ℝ) * ((w + 1) / L + 1 / (Mm : ℝ)) := by
    intro n hn x
    have hw : 0 ≤ w := by
      dsimp [w]
      positivity
    exact aux_lem_shifts_count_from_strip d Mm hMm L w hLpos hw K side shift lo
      nonPadded hKcop hnon hcoord_strip hres_count n hn x
  have hcollapse :
      2 * (d : ℝ) * ((w + 1) / L + 1 / (Mm : ℝ)) ≤
        Cbound * L ^ (gamma - 1) := by
    have hMgam' : (Mm : ℝ) ^ (-1 : ℝ) ≤ L ^ (gamma - 1) := by
      change (Mm : ℝ) ^ (-1 : ℝ) ≤ ((3 : ℝ) ^ H1) ^ (gamma - 1)
      exact hMgam
    simpa only [w, Cbound] using
      (aux_lem_shifts_collapse d Mm gamma Cwidth L hgamma hCwidth hL hMgam')
  constructor
  · intro n hn x
    exact ⟨hcount n hn x, hcollapse⟩
  · intro mu hmu zQ rQ hrQ n hn
    letI : IsFiniteMeasure mu := hmu
    let Q : Set (SpatialCoordinates d) :=
      (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))
    have hDpos : 0 < (Mm : ℝ) ^ d := by
      have hMmR : (0 : ℝ) < (Mm : ℝ) := by
        exact_mod_cast (show 0 < Mm by omega)
      positivity
    have hCpos : 0 ≤ Cbound * L ^ (gamma - 1) := by
      dsimp [Cbound]
      positivity
    have hQmeas : MeasurableSet Q := by
      dsimp [Q]
      exact (centeredCube zQ rQ hrQ).isOpen.measurableSet
    have hlo : ∀ (sigma : Fin d → Fin Mm) (m : ℕ) (i : Fin d),
        Measurable (fun x : SpatialCoordinates d => lo sigma m x i) := by
      intro sigma m i
      exact aux_lem_shifts_lo_measurable d Mm shift side sigma m i
    have hA : ∀ sigma : Fin d → Fin Mm,
        MeasurableSet {x : SpatialCoordinates d |
          x ∈ Q ∧ nonPadded sigma n x} := by
      intro sigma
      change MeasurableSet {x : SpatialCoordinates d |
        x ∈ Q ∧
          ∃ i : Fin d,
            (lo sigma n x i - lo sigma (n - 1) x i ≤ w * side n) ∨
            (lo sigma (n - 1) x i + side (n - 1) -
              (lo sigma n x i + side n) ≤ w * side n)}
      exact aux_lem_shifts_nonpadded_measurable d Mm Q hQmeas w side lo sigma n
        (fun m i => hlo sigma m i)
    have hpoint : ∀ x : SpatialCoordinates d, x ∈ Q →
        ((Nat.card {sigma : Fin d → Fin Mm // nonPadded sigma n x} : ℕ) : ℝ) /
            (Mm : ℝ) ^ d ≤ Cbound * L ^ (gamma - 1) := by
      intro x hx
      exact (hcount n hn x).trans hcollapse
    have hmeasure :=
      aux_lem_shifts_measure_bound (α := Fin d → Fin Mm)
        (X := SpatialCoordinates d) mu Q (fun sigma x => nonPadded sigma n x)
        ((Mm : ℝ) ^ d)
        (Cbound * L ^ (gamma - 1)) hDpos hCpos hQmeas hA hpoint
    simpa only [Q] using hmeasure

end Paper
