import SubdiffusiveProcess.Paper.lfgc_rhs_bridge
import SubdiffusiveProcess.Paper.lfgc_sum_trunc_lp
import SubdiffusiveProcess.Paper.prefix_physical_witness

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc




open MeasureTheory Filter Topology SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
  SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal BigOperators

namespace Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]



noncomputable def aux_lfgc_p1_index_p1Centres (en nc ns : ℕ) (enDepth : Fin en → ℕ)
    (cmpShift : Fin nc → SpatialCoordinates d) (shift : Fin ns → SpatialCoordinates d)
    (k : ℕ) (z : SpatialCoordinates d) (U : Fin en × Fin ns) (D : ℕ) :
    Finset (SpatialCoordinates d) := by
  classical
  exact ((Finset.univ : Finset (Fin en × Fin ns)).image
      (fun V => z + ((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth V.1) • shift V.2)) ∪
    ((Finset.univ : Finset (Fin nc)).image (fun c => z + (3 : ℝ) ^ (-(k : ℤ)) • cmpShift c)) ∪
    ((Finset.univ : Finset (Fin D → OddGridIndex d 1)).image
      (descendantCenter 1 (z + ((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth U.1) • shift U.2)
        ((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth U.1) D))

/-- The prefix index family at depth `D`: root, catalogue centre and score tag. -/
def aux_lfgc_p1_index_p1Idx (en nc ns : ℕ) (enDepth : Fin en → ℕ) (cmpShift : Fin nc → SpatialCoordinates d)
    (shift : Fin ns → SpatialCoordinates d) (k : ℕ) (z : SpatialCoordinates d) (D : ℕ) : Type :=
  Σ U : Fin en × Fin ns, {w : SpatialCoordinates d //
    w ∈ aux_lfgc_p1_index_p1Centres en nc ns enDepth cmpShift shift k z U D} × Bool

noncomputable instance aux_lfgc_p1_index_p1Idx_fintype (en nc ns : ℕ) (enDepth : Fin en → ℕ)
    (cmpShift : Fin nc → SpatialCoordinates d) (shift : Fin ns → SpatialCoordinates d) (k : ℕ)
    (z : SpatialCoordinates d) (D : ℕ) :
    Fintype (aux_lfgc_p1_index_p1Idx en nc ns enDepth cmpShift shift k z D) := by
  unfold aux_lfgc_p1_index_p1Idx
  infer_instance

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lfgc_p1_index_card_p1Centres_le (en nc ns : ℕ) (enDepth : Fin en → ℕ)
    (cmpShift : Fin nc → SpatialCoordinates d) (shift : Fin ns → SpatialCoordinates d) (k : ℕ)
    (z : SpatialCoordinates d) (U : Fin en × Fin ns) (D : ℕ) :
    ((aux_lfgc_p1_index_p1Centres en nc ns enDepth cmpShift shift k z U D).card : ℝ) ≤
      ((en * ns + nc + 1 : ℕ) : ℝ) * (3 : ℝ) ^ (d * D) := by
  classical
  unfold aux_lfgc_p1_index_p1Centres
  have h1 := Finset.card_image_le (s := (Finset.univ : Finset (Fin en × Fin ns)))
    (f := fun V => z + ((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth V.1) • shift V.2)
  have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin nc)))
    (f := fun c => z + (3 : ℝ) ^ (-(k : ℤ)) • cmpShift c)
  have h3 := Finset.card_image_le (s := (Finset.univ : Finset (Fin D → OddGridIndex d 1)))
    (f := descendantCenter 1 (z + ((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth U.1) • shift U.2)
        ((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth U.1) D)
  have hcardFin : Fintype.card (Fin D → OddGridIndex d 1) = 3 ^ (d * D) := by
    rw [Fintype.card_pi]; simp [OddGridIndex, pow_mul]
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h1
  rw [Finset.card_univ, Fintype.card_fin] at h2
  rw [Finset.card_univ, hcardFin] at h3
  set A := (Finset.univ : Finset (Fin en × Fin ns)).image
      (fun V => z + ((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth V.1) • shift V.2) with hA
  set B := (Finset.univ : Finset (Fin nc)).image
      (fun c => z + (3 : ℝ) ^ (-(k : ℤ)) • cmpShift c) with hB
  set C := (Finset.univ : Finset (Fin D → OddGridIndex d 1)).image
      (descendantCenter 1 (z + ((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth U.1) • shift U.2)
        ((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth U.1) D) with hC
  have hu : (A ∪ B ∪ C).card ≤ A.card + B.card + C.card :=
    (Finset.card_union_le (A ∪ B) C).trans (Nat.add_le_add_right (Finset.card_union_le A B) _)
  have htot : (A ∪ B ∪ C).card ≤ (en * ns + nc + 1) * 3 ^ (d * D) := by
    have h3p : 1 ≤ 3 ^ (d * D) := Nat.one_le_pow _ _ (by norm_num)
    calc (A ∪ B ∪ C).card ≤ A.card + B.card + C.card := hu
      _ ≤ en * ns + nc + 3 ^ (d * D) := by omega
      _ ≤ (en * ns + nc + 1) * 3 ^ (d * D) := by nlinarith
  exact_mod_cast htot

theorem aux_lfgc_p1_index_card_p1Idx_le (en nc ns : ℕ) (enDepth : Fin en → ℕ)
    (cmpShift : Fin nc → SpatialCoordinates d) (shift : Fin ns → SpatialCoordinates d) (k : ℕ)
    (z : SpatialCoordinates d) (D : ℕ) :
    (Fintype.card (aux_lfgc_p1_index_p1Idx en nc ns enDepth cmpShift shift k z D) : ℝ) ≤
      (2 * (en * ns : ℕ) * ((en * ns + nc + 1 : ℕ) : ℝ)) * Real.exp ((d * Real.log 3) * D) := by
  classical
  have hexp : Real.exp ((d * Real.log 3) * D) = (3 : ℝ) ^ (d * D) := by
    rw [show (d : ℝ) * Real.log 3 * D = Real.log 3 * ((d * D : ℕ) : ℝ) by push_cast; ring,
      Real.exp_mul, Real.exp_log (by norm_num), Real.rpow_natCast]
  rw [hexp]
  unfold aux_lfgc_p1_index_p1Idx
  rw [Fintype.card_sigma]
  push_cast
  calc (∑ U : Fin en × Fin ns, (Fintype.card ({w : SpatialCoordinates d //
        w ∈ aux_lfgc_p1_index_p1Centres en nc ns enDepth cmpShift shift k z U D} × Bool) : ℝ))
      ≤ ∑ _U : Fin en × Fin ns, 2 * (((en * ns + nc + 1 : ℕ) : ℝ) * (3 : ℝ) ^ (d * D)) := by
        refine Finset.sum_le_sum fun U _ => ?_
        rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_coe]
        push_cast
        have := aux_lfgc_p1_index_card_p1Centres_le en nc ns enDepth cmpShift shift k z U D
        push_cast at this
        linarith
    _ = 2 * ((en : ℝ) * ns) * ((en * ns + nc + 1 : ℝ)) * (3 : ℝ) ^ (d * D) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- The exact physical prefix sums of the index family. -/
noncomputable def aux_lfgc_p1_index_p1T (en nc ns : ℕ) (enDepth : Fin en → ℕ)
    (cmpShift : Fin nc → SpatialCoordinates d) (shift : Fin ns → SpatialCoordinates d)
    (buffer : ℕ) (Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ) (m k : ℕ)
    (z : SpatialCoordinates d) (D : ℕ) (i : aux_lfgc_p1_index_p1Idx en nc ns enDepth cmpShift shift k z D)
    (omega : BilateralField d) : ℝ :=
  Paper.aux_prefix_physical_tail_sum (m + k) k buffer D (enDepth i.1.1) i.2.1.1 Z Draw i.2.2 omega

/-- A failed prefix conjunct gives a large prefix sum. -/
theorem lfgc_p1_index (en nc ns : ℕ) (enDepth : Fin en → ℕ)
    (cmpShift : Fin nc → SpatialCoordinates d) (shift : Fin ns → SpatialCoordinates d)
    (buffer k0 : ℕ) (lam : ℝ) (Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ) (m k : ℕ)
    (z : SpatialCoordinates d) (omega : BilateralField d)
    (h : ¬ aux_lfgc_rhs_bridge_rhsP1OK en nc ns enDepth cmpShift shift buffer k0 lam Draw Z m k z omega) :
    ∃ D, k0 ≤ D ∧ ∃ i : aux_lfgc_p1_index_p1Idx en nc ns enDepth cmpShift shift k z D,
      lam * (D : ℝ) ≤ aux_lfgc_p1_index_p1T en nc ns enDepth cmpShift shift buffer Draw Z m k z D i omega := by
  unfold aux_lfgc_rhs_bridge_rhsP1OK at h
  simp only [not_forall, not_and_or, not_lt] at h
  obtain ⟨U, D, hD, w, hw, hcase⟩ := h
  refine ⟨D, hD, ?_⟩
  rcases hcase with hZ | hDr
  · refine ⟨⟨U, ⟨w, hw⟩, false⟩, ?_⟩
    refine hZ.trans (le_of_eq ?_)
    unfold aux_lfgc_p1_index_p1T Paper.aux_prefix_physical_tail_sum
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Bool.false_eq_true, if_false]
  · refine ⟨⟨U, ⟨w, hw⟩, true⟩, ?_⟩
    refine hDr.trans (le_of_eq ?_)
    unfold aux_lfgc_p1_index_p1T Paper.aux_prefix_physical_tail_sum
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [if_true]

theorem aux_lfgc_p1_index_p1T_eq_sum (en nc ns : ℕ) (enDepth : Fin en → ℕ)
    (cmpShift : Fin nc → SpatialCoordinates d) (shift : Fin ns → SpatialCoordinates d)
    (buffer : ℕ) (Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ) (m k : ℕ)
    (z : SpatialCoordinates d) (D : ℕ) (i : aux_lfgc_p1_index_p1Idx en nc ns enDepth cmpShift shift k z D)
    (omega : BilateralField d) :
    aux_lfgc_p1_index_p1T en nc ns enDepth cmpShift shift buffer Draw Z m k z D i omega =
      ∑ j ∈ Finset.Icc ((k : ℤ) - (enDepth i.1.1 : ℤ) - (buffer : ℤ))
        (min ((m + k : ℕ) : ℤ) ((k : ℤ) - (enDepth i.1.1 : ℤ) + (D : ℤ) + (buffer : ℤ))),
        if 0 ≤ ((m + k : ℕ) : ℤ) - j then aux_lfgc_sum_band_summand i.2.2 Draw Z (m + k) j i.2.1.1 omega else 0 := by
  unfold aux_lfgc_p1_index_p1T Paper.aux_prefix_physical_tail_sum aux_lfgc_sum_band_summand
  rfl

end Paper
