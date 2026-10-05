module

public import SubdiffusiveProcess.Geometry.TriadicLeafCost
public import SubdiffusiveProcess.Geometry.CubePowerComparison

@[expose] public section

/-!
# Existence of the finite triadic boundary partitions

Assembles `TriadicBoundaryPartitions` from the leaf sets of the stopped refinement.
-/
open Set MeasureTheory Metric
noncomputable section
namespace SubdiffusiveProcess
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

theorem triadicPart_sum_fin_equiv {α : Type*} (L : Finset α) (f : α → ℝ) :
    ∑ i : Fin L.card, f ((L.equivFin.symm i : L) : α) = ∑ a ∈ L, f a := by
  rw [← Finset.sum_coe_sort L f]
  exact Equiv.sum_comp L.equivFin.symm (fun x : L => f x)

theorem triadicPart_iUnion_fin_equiv {α β : Type*} (L : Finset α) (F : α → Set β) :
    (⋃ i : Fin L.card, F ((L.equivFin.symm i : L) : α)) = ⋃ a ∈ L, F a := by
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨_, (L.equivFin.symm i).2, hi⟩
  · rintro ⟨a, ha, hx⟩
    exact ⟨L.equivFin ⟨a, ha⟩, by simpa using hx⟩

theorem triadicPart_three_zpow_neg_natCast (n : ℕ) : (3 : ℝ) ^ (-(n : ℤ)) = 1 / (3 : ℝ) ^ n := by
  rw [zpow_neg, zpow_natCast, one_div]

/-- The side of a leaf at depth at least `J0 + n` is at most `r 3^{-n}`. -/
theorem triadicPart_side_le_of_depth {R r : ℝ} (hR : 0 < R) (J0 n : ℕ) (h0 : R / (3 : ℝ) ^ J0 ≤ r / 4)
    (hr : 0 < r) {q : TriadicGridLabel d} (hq : J0 + n ≤ q.1) :
    triadicGridSide R q ≤ r * (3 : ℝ) ^ (-(n : ℤ)) := by
  rw [triadicGridSide_eq, triadicPart_three_zpow_neg_natCast]
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have h1 : R / (3 : ℝ) ^ q.1 ≤ R / (3 : ℝ) ^ (J0 + n) :=
    div_le_div_of_nonneg_left hR.le (by positivity) (pow_le_pow_right₀ (by norm_num) hq)
  have h2 : R / (3 : ℝ) ^ (J0 + n) = (R / (3 : ℝ) ^ J0) / (3 : ℝ) ^ n := by
    rw [pow_add, div_div]
  calc R / (3 : ℝ) ^ q.1 ≤ R / (3 : ℝ) ^ (J0 + n) := h1
    _ = (R / (3 : ℝ) ^ J0) / (3 : ℝ) ^ n := h2
    _ ≤ (r / 4) / (3 : ℝ) ^ n := by gcongr
    _ ≤ r * (1 / (3 : ℝ) ^ n) := by
      rw [div_div, mul_one_div]
      exact div_le_div_of_nonneg_left hr.le h3 (by linarith)

theorem triadicBoundaryPartitions_exists [NeZero d] (s : ℝ) (hs : (d : ℝ) - 1 < s)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (minLevel : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w : SpatialCoordinates d) (r : ℝ), 0 < r →
      Metric.ball w (r / 2) ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) →
      Nonempty (TriadicBoundaryPartitions z R hR (Metric.ball w (r / 2)) r s C minLevel) := by
  refine ⟨|triadicBaseConst d s minLevel| + |triadicDeepConst d s| + 1, by positivity, ?_⟩
  intro w r hr hB
  have hrR : r ≤ R := cube_side_le_of_subset z w R r hR hr hB
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  obtain ⟨J0, hmJ0, h0, hlow⟩ := triadicPart_exists_start_depth hR hr hrR minLevel
  set S : Set (SpatialCoordinates d) := frontier (Metric.ball w (r / 2)) with hS
  set L : ℕ → Finset (TriadicGridLabel d) := fun n => triadicLeaves z R hR S J0 n with hL
  have hcl : closure (Metric.ball w (r / 2)) ⊆
      closure (centeredCube z R hR : Set (SpatialCoordinates d)) := closure_mono hB
  have hSQ : S ⊆ closure (centeredCube z R hR : Set (SpatialCoordinates d)) :=
    frontier_subset_closure.trans hcl
  refine ⟨{
    count := fun n => (L n).card
    label := fun n i => ((L n).equivFin.symm i : TriadicGridLabel d)
    depth_ge := ?_
    disjoint := ?_
    cover := ?_
    cover_ae := ?_
    boundary := ?_
    persistence := ?_
    total := ?_
    local_bound := ?_ }⟩
  · intro n i
    have := (mem_triadicLeaves z R hR).1 ((L n).equivFin.symm i).2
    exact hmJ0.trans this.1
  · intro n i j hij
    apply triadicLeaves_disjoint z R hR S J0 n ((L n).equivFin.symm i).2
      ((L n).equivFin.symm j).2
    intro h
    exact hij ((L n).equivFin.symm.injective (Subtype.ext h))
  · intro n
    exact (triadicPart_iUnion_fin_equiv (L n) (fun ℓ => closure (triadicCell z R hR ℓ))).trans
      (triadicLeaves_closure_cover z R hR S J0 n)
  · intro n
    have h := triadicPart_iUnion_fin_equiv (L n) (fun ℓ => triadicCell z R hR ℓ)
    have h2 := triadicLeaves_cover_ae z R hR S J0 n
    rw [← h] at h2
    exact h2
  · intro n x hx
    obtain ⟨ℓ, hℓ, hxℓ, hdep⟩ := triadicLeaves_boundary z R hR S J0 n hx (hSQ hx)
    refine ⟨(L n).equivFin ⟨ℓ, hℓ⟩, ?_, ?_⟩
    · simpa using! hxℓ
    · have := triadicPart_side_le_of_depth hR J0 n h0 hr (q := ℓ) (by omega)
      simpa using this
  · intro n m hnm x hx
    rcases triadicLeaves_persistence z R hR S J0 hnm hx with
      ⟨a, ha, haL, hxa⟩ | ⟨a, ha, b, hb, hxa, hxb, hna, hnb⟩
    · left
      exact ⟨(L n).equivFin ⟨a, ha⟩, (L m).equivFin ⟨a, haL⟩, by simp, by simpa using! hxa⟩
    · right
      exact ⟨(L n).equivFin ⟨a, ha⟩, (L m).equivFin ⟨b, hb⟩, by simpa using! hxa,
        by simpa using! hxb, by simpa using triadicPart_side_le_of_depth hR J0 n h0 hr hna,
        by simpa using triadicPart_side_le_of_depth hR J0 n h0 hr hnb⟩
  · refine ⟨|((3 : ℝ) ^ J0) ^ d * (R / (3 : ℝ) ^ J0) ^ s + triadicDeepConst d s * r ^ s|,
      abs_nonneg _, ?_⟩
    intro n
    calc _ = ∑ ℓ ∈ L n, (triadicGridSide R ℓ) ^ s :=
          triadicPart_sum_fin_equiv (L n) (fun ℓ => (triadicGridSide R ℓ) ^ s)
      _ ≤ ((3 : ℝ) ^ J0) ^ d * (R / (3 : ℝ) ^ J0) ^ s + triadicDeepConst d s * r ^ s :=
          triadicPart_total_cost_le z R hR hd1 w hr J0 n h0 hs
      _ ≤ _ := le_abs_self _
  · intro n
    calc _ = ∑ ℓ ∈ L n, (if (triadicCell z R hR ℓ ∩ Metric.ball w (r / 2)).Nonempty
            then (triadicGridSide R ℓ) ^ s else 0) :=
          triadicPart_sum_fin_equiv (L n) (fun ℓ => if (triadicCell z R hR ℓ ∩ Metric.ball w (r / 2)).Nonempty
            then (triadicGridSide R ℓ) ^ s else 0)
      _ ≤ (triadicBaseConst d s minLevel + triadicDeepConst d s) * r ^ s :=
          triadicPart_local_cost_le z R hR hd1 w hr J0 n minLevel h0 hlow hs
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr.le s)
          linarith [le_abs_self (triadicBaseConst d s minLevel),
            le_abs_self (triadicDeepConst d s)]

end SubdiffusiveProcess
