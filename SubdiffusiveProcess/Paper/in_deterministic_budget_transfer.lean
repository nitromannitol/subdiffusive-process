import SubdiffusiveProcess.Lane3.Subdivision
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Paper.good_event
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.lane4_deterministic_iteration_input
import SubdiffusiveProcess.Paper.obl_ramp
import Homogenization.Book.Ch02.Matrices

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

lemma aux_in_deterministic_budget_transfer_card_low
    (a : ℤ) (k c D : ℕ) (hk : 1 ≤ k) :
    ((Finset.filter (fun j : ℤ => j < a + (k : ℤ))
      (Finset.Icc (a - (c : ℤ)) (a + (D : ℤ)))).card : ℝ) ≤
      (k : ℝ) + (c : ℝ) := by
  classical
  let F := Finset.filter (fun j : ℤ => j < a + (k : ℤ))
    (Finset.Icc (a - (c : ℤ)) (a + (D : ℤ)))
  let G := Finset.Icc (a - (c : ℤ)) (a + (k : ℤ) - 1)
  have hFG : F ⊆ G := by
    intro j hj
    have hjlt := (Finset.mem_filter.mp hj).2
    have hjF := (Finset.mem_filter.mp hj).1
    have hjI := Finset.mem_Icc.mp hjF
    apply Finset.mem_Icc.mpr
    constructor
    · exact hjI.1
    · omega
  have hle : F.card ≤ G.card := Finset.card_le_card hFG
  have hGle : a - (c : ℤ) ≤ (a + (k : ℤ) - 1) + 1 := by
    omega
  have hGcard : (G.card : ℤ) = (k : ℤ) + (c : ℤ) := by
    rw [Int.card_Icc_of_le (a - (c : ℤ)) (a + (k : ℤ) - 1) hGle]
    omega
  have hleZ : (F.card : ℤ) ≤ (G.card : ℤ) := by
    exact_mod_cast hle
  have hle' : (F.card : ℤ) ≤ (k : ℤ) + (c : ℤ) := hleZ.trans_eq hGcard
  exact_mod_cast hle'

lemma aux_in_deterministic_budget_transfer_card_score
    (a : ℤ) (k c D : ℕ) (f : ℤ → ℝ)
    (hf : ∀ j ∈ Finset.Icc (a - (c : ℤ)) (a + (D : ℤ)), 0 ≤ f j)
    (hlow :
      ((Finset.filter (fun j : ℤ => j < a + (k : ℤ))
        (Finset.Icc (a - (c : ℤ)) (a + (D : ℤ)))).card : ℝ) ≤
        (k : ℝ) + (c : ℝ)) :
    ((Finset.filter (fun j : ℤ => j < a + (k : ℤ) ∨ 1 ≤ f j)
      (Finset.Icc (a - (c : ℤ)) (a + (D : ℤ)))).card : ℝ) ≤
      (k : ℝ) + (c : ℝ) +
        ∑ j ∈ Finset.Icc (a - (c : ℤ)) (a + (D : ℤ)), f j := by
  classical
  let F := Finset.Icc (a - (c : ℤ)) (a + (D : ℤ))
  let L := F.filter (fun j : ℤ => j < a + (k : ℤ))
  let H := F.filter (fun j : ℤ => 1 ≤ f j)
  let S := F.filter (fun j : ℤ => j < a + (k : ℤ) ∨ 1 ≤ f j)
  have hSL : S ⊆ L ∪ H := by
    intro j hj
    have hjS := Finset.mem_filter.mp hj
    rcases hjS.2 with hlowj | hhj
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hjS.1, hlowj⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hjS.1, hhj⟩))
  have hScard : S.card ≤ L.card + H.card := by
    calc
      S.card ≤ (L ∪ H).card := Finset.card_le_card hSL
      _ ≤ L.card + H.card := Finset.card_union_le _ _
  have hHone : (H.card : ℝ) ≤ (∑ j ∈ H, f j) := by
    calc
      (H.card : ℝ) = ∑ j ∈ H, (1 : ℝ) := by simp
      _ ≤ ∑ j ∈ H, f j := by
        apply Finset.sum_le_sum
        intro j hj
        exact (Finset.mem_filter.mp hj).2
  have hHsum : (∑ j ∈ H, f j) ≤ (∑ j ∈ F, f j) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro j hjF hjH
    exact hf j hjF
  have hScardR : (S.card : ℝ) ≤ (L.card : ℝ) + (H.card : ℝ) := by
    exact_mod_cast hScard
  have hmain : (S.card : ℝ) ≤ (k : ℝ) + (c : ℝ) + (∑ j ∈ F, f j) := by
    calc
      (S.card : ℝ) ≤ (L.card : ℝ) + (H.card : ℝ) := hScardR
      _ ≤ (k : ℝ) + (c : ℝ) + (H.card : ℝ) := by linarith [hlow]
      _ ≤ (k : ℝ) + (c : ℝ) + ∑ j ∈ H, f j := by gcongr
      _ ≤ (k : ℝ) + (c : ℝ) + ∑ j ∈ F, f j := by gcongr
  exact hmain

lemma aux_in_deterministic_budget_transfer_sum_good
    (F G : Finset ℤ) (e g : ℤ → ℝ) (C A D P : ℝ)
    (hGF : G ⊆ F) (hcard : (G.card : ℝ) ≤ D)
    (hP : (∑ j ∈ G, g j) ≤ P)
    (he : ∀ j ∈ G, e j ≤ C * (A + g j))
    (hC : 0 ≤ C) (hA : 0 ≤ A) :
    (∑ j ∈ F, if j ∈ G then e j else 0) ≤ C * (A * D + P) := by
  classical
  have hfilter : F.filter (fun j => j ∈ G) = G := by
    apply Finset.Subset.antisymm
    · intro j hj
      exact (Finset.mem_filter.mp hj).2
    · intro j hj
      exact Finset.mem_filter.mpr ⟨hGF hj, hj⟩
  have hsum_eq : (∑ j ∈ F, if j ∈ G then e j else 0) = ∑ j ∈ G, e j := by
    rw [← Finset.sum_filter]
    rw [hfilter]
  have hsum_point : (∑ j ∈ G, e j) ≤ ∑ j ∈ G, C * (A + g j) := by
    apply Finset.sum_le_sum
    intro j hj
    exact he j hj
  have hsum_expand : (∑ j ∈ G, C * (A + g j)) =
      C * (A * (G.card : ℝ) + ∑ j ∈ G, g j) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  have hinner : A * (G.card : ℝ) + (∑ j ∈ G, g j) ≤ A * D + P := by
    exact add_le_add (mul_le_mul_of_nonneg_left hcard hA) hP
  rw [hsum_eq]
  calc
    (∑ j ∈ G, e j) ≤ ∑ j ∈ G, C * (A + g j) := hsum_point
    _ = C * (A * (G.card : ℝ) + ∑ j ∈ G, g j) := hsum_expand
    _ ≤ C * (A * D + P) := mul_le_mul_of_nonneg_left hinner hC



theorem in_deterministic_budget_transfer
    (d : ℕ) [NeZero d]
    (I : Paper.in_J d)
    (Cbound delta eps lambdaDet : ℝ)
    (hCbound : 0 ≤ Cbound) (hdelta : 0 ≤ delta) (heps : 0 ≤ eps)
    (hk0 cbuf D N : ℕ)
    (hk0_pos : 1 ≤ hk0)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Enl Shift : Type)
    (U : Enl × Shift)
    (omega : BilateralField d)
    (rootLevel : Enl × Shift → ℤ)
    (observationCentre : ∀ (V : Enl × Shift) (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (Enl × Shift)) →
        SpatialCoordinates d)
    (code : (Fin D → OddGridIndex d 1) ⊕ (Enl × Shift))
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
    (prefixZ prefixD : ℝ)
    (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
    (s : ℝ)
    (hN : rootLevel U + (D : ℤ) ≤ (N : ℤ))
    (hPrefixZ : prefixZ =
      ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
        (rootLevel U + (D : ℤ)),
        if 0 ≤ (N : ℤ) - j then
          Z N ((N : ℤ) - j).toNat
            (((3 : ℝ) ^ N) • observationCentre U D code) omega
        else 0)
    (hPrefixD : prefixD =
      ∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
        (rootLevel U + (D : ℤ)),
        if 0 ≤ (N : ℤ) - j then
          (Draw N ((N : ℤ) - j).toNat
            (((3 : ℝ) ^ N) • observationCentre U D code) omega).toReal
        else 0)
    (hPrefixZBound : prefixZ < lambdaDet * (D : ℝ))
    (hPrefixDBound : prefixD < lambdaDet * (D : ℝ))
    (hZnonneg : ∀ j : ℤ,
      0 ≤ Z N ((N : ℤ) - j).toNat
        (((3 : ℝ) ^ N) • observationCentre U D code) omega)
    (hPointwise :
      ∀ (j : ℤ),
        rootLevel U + (hk0 : ℤ) ≤ j →
        j ≤ rootLevel U + (D : ℤ) →
        0 ≤ (N : ℤ) - j →
        Z N ((N : ℤ) - j).toNat
            (((3 : ℝ) ^ N) • observationCentre U D code) omega < 1 →
        I.err (observationCentre U D code) ((3 : ℝ) ^ (-j)) (by positivity)
          (Lane4.cutoffPositiveCoefficient M H omega N
            (observationCentre U D code) (by positivity))
          (observationCentre U D code) ((3 : ℝ) ^ (-j))
          (sN N j (observationCentre U D code) omega) s 2 ≤
        Cbound * (delta ^ 2 + eps ^ 8 +
          (Draw N ((N : ℤ) - j).toNat
            (((3 : ℝ) ^ N) • observationCentre U D code) omega).toReal)) :
    ((Finset.filter
      (fun j : ℤ => j < rootLevel U + (hk0 : ℤ) ∨
        1 ≤ Z N ((N : ℤ) - j).toNat
          (((3 : ℝ) ^ N) • observationCentre U D code) omega)
      (Finset.Icc (rootLevel U - (cbuf : ℤ))
        (rootLevel U + (D : ℤ)))).card : ℝ) ≤
      (hk0 : ℝ) + (cbuf : ℝ) + lambdaDet * (D : ℝ) ∧
    (∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
        (rootLevel U + (D : ℤ)),
        if rootLevel U + (hk0 : ℤ) ≤ j ∧
            Z N ((N : ℤ) - j).toNat
              (((3 : ℝ) ^ N) • observationCentre U D code) omega < 1 then
          I.err (observationCentre U D code) ((3 : ℝ) ^ (-j)) (by positivity)
            (Lane4.cutoffPositiveCoefficient M H omega N
              (observationCentre U D code) (by positivity))
            (observationCentre U D code) ((3 : ℝ) ^ (-j))
        (sN N j (observationCentre U D code) omega) s 2
        else 0) ≤
      Cbound * (delta ^ 2 + eps ^ 8 + lambdaDet) * (D : ℝ) +
        Cbound * ((hk0 : ℝ) + (cbuf : ℝ)) := by
  classical
  let x : SpatialCoordinates d :=
    ((3 : ℝ) ^ N) • observationCentre U D code
  let z : ℤ → ℝ := fun j =>
    Z N ((N : ℤ) - j).toNat x omega
  let q : ℤ → ℝ := fun j =>
    (Draw N ((N : ℤ) - j).toNat x omega).toReal
  let F : Finset ℤ :=
    Finset.Icc (rootLevel U - (cbuf : ℤ)) (rootLevel U + (D : ℤ))
  let G : Finset ℤ := F.filter (fun j =>
    rootLevel U + (hk0 : ℤ) ≤ j ∧ z j < 1)
  let e : ℤ → ℝ := fun j =>
    I.err (observationCentre U D code) ((3 : ℝ) ^ (-j)) (by positivity)
      (Lane4.cutoffPositiveCoefficient M H omega N
        (observationCentre U D code) (by positivity))
      (observationCentre U D code) ((3 : ℝ) ^ (-j))
      (sN N j (observationCentre U D code) omega) s 2
  have hNmem : ∀ j ∈ F, 0 ≤ (N : ℤ) - j := by
    intro j hj
    have hjI := Finset.mem_Icc.mp hj
    omega
  have hZprefix : prefixZ = ∑ j ∈ F, z j := by
    rw [hPrefixZ]
    dsimp [F, z, x]
    apply Finset.sum_congr rfl
    intro j hj
    rw [if_pos]
    exact hNmem j hj
  have hDprefix : prefixD = ∑ j ∈ F, q j := by
    rw [hPrefixD]
    dsimp [F, q, x]
    apply Finset.sum_congr rfl
    intro j hj
    rw [if_pos]
    exact hNmem j hj
  have hzsum : (∑ j ∈ F, z j) < lambdaDet * (D : ℝ) := by
    calc
      (∑ j ∈ F, z j) = prefixZ := hZprefix.symm
      _ < lambdaDet * (D : ℝ) := hPrefixZBound
  have hqnonneg : ∀ j ∈ F, 0 ≤ q j := by
    intro j hj
    dsimp [q]
    exact ENNReal.toReal_nonneg
  have hZnonneg' : ∀ j ∈ F, 0 ≤ z j := by
    intro j hj
    exact hZnonneg j
  have hlow := aux_in_deterministic_budget_transfer_card_low
    (rootLevel U) hk0 cbuf D hk0_pos
  have hcard_score := aux_in_deterministic_budget_transfer_card_score
    (rootLevel U) hk0 cbuf D z hZnonneg' hlow
  have hcard :
      ((Finset.filter
        (fun j : ℤ => j < rootLevel U + (hk0 : ℤ) ∨ 1 ≤ z j) F).card : ℝ) ≤
        (hk0 : ℝ) + (cbuf : ℝ) + ∑ j ∈ F, z j := by
    exact hcard_score
  have hcard_final :
      ((Finset.filter
        (fun j : ℤ => j < rootLevel U + (hk0 : ℤ) ∨ 1 ≤ z j) F).card : ℝ) ≤
        (hk0 : ℝ) + (cbuf : ℝ) + lambdaDet * (D : ℝ) := by
    linarith [hcard, hzsum]
  have hGF : G ⊆ F := by
    exact Finset.filter_subset _ _
  have hGcard : (G.card : ℝ) ≤ (D : ℝ) := by
    let K : Finset ℤ := Finset.Icc
      (rootLevel U + (1 : ℤ)) (rootLevel U + (D : ℤ))
    have hGK : G ⊆ K := by
      intro j hj
      have hjG := Finset.mem_filter.mp hj
      have hjF := Finset.mem_Icc.mp hjG.1
      have hjgood := hjG.2
      apply Finset.mem_Icc.mpr
      constructor
      · omega
      · exact hjF.2
    have hcardGK : G.card ≤ K.card := Finset.card_le_card hGK
    have hKle : rootLevel U + (1 : ℤ) ≤
        (rootLevel U + (D : ℤ)) + 1 := by omega
    have hKcard : (K.card : ℤ) = (D : ℤ) := by
      rw [Int.card_Icc_of_le (rootLevel U + (1 : ℤ))
        (rootLevel U + (D : ℤ)) hKle]
      omega
    have hcardGK' : (G.card : ℤ) ≤ (D : ℤ) := by
      have hcardGKZ : (G.card : ℤ) ≤ (K.card : ℤ) := by
        exact_mod_cast hcardGK
      exact hcardGKZ.trans_eq hKcard
    exact_mod_cast hcardGK'
  have hGsum : (∑ j ∈ G, q j) ≤ prefixD := by
    have hsumGF : (∑ j ∈ G, q j) ≤ ∑ j ∈ F, q j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hGF
      intro j hjF hjG
      exact hqnonneg j hjF
    exact hsumGF.trans_eq hDprefix.symm
  have he : ∀ j ∈ G, e j ≤ Cbound * (delta ^ 2 + eps ^ 8 + q j) := by
    intro j hj
    have hjG := Finset.mem_filter.mp hj
    have hjF := Finset.mem_Icc.mp hjG.1
    have hjgood := hjG.2
    apply hPointwise j
    · exact hjgood.1
    · exact hjF.2
    · exact hNmem j hjG.1
    · exact hjgood.2
  have hA : 0 ≤ delta ^ 2 + eps ^ 8 := by positivity
  have hsum_good :
      (∑ j ∈ F, if j ∈ G then e j else 0) ≤
        Cbound * ((delta ^ 2 + eps ^ 8) * (D : ℝ) + prefixD) := by
    exact aux_in_deterministic_budget_transfer_sum_good F G e q Cbound
      (delta ^ 2 + eps ^ 8) (D : ℝ) prefixD hGF hGcard hGsum he hCbound hA
  constructor
  · simpa [F, z] using hcard_final
  · have hprefixDle : prefixD ≤ lambdaDet * (D : ℝ) := hPrefixDBound.le
    have hinner :
        (delta ^ 2 + eps ^ 8) * (D : ℝ) + prefixD ≤
          (delta ^ 2 + eps ^ 8 + lambdaDet) * (D : ℝ) := by
      calc
        (delta ^ 2 + eps ^ 8) * (D : ℝ) + prefixD ≤
            (delta ^ 2 + eps ^ 8) * (D : ℝ) + lambdaDet * (D : ℝ) :=
          add_le_add (le_refl _) hprefixDle
        _ = (delta ^ 2 + eps ^ 8 + lambdaDet) * (D : ℝ) := by ring
    have hmain := mul_le_mul_of_nonneg_left hinner hCbound
    have hextra : 0 ≤ Cbound * ((hk0 : ℝ) + (cbuf : ℝ)) := by positivity
    have hsum_good' :
        (∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
          (rootLevel U + (D : ℤ)),
          if rootLevel U + (hk0 : ℤ) ≤ j ∧
              Z N ((N : ℤ) - j).toNat
                (((3 : ℝ) ^ N) • observationCentre U D code) omega < 1 then
            I.err (observationCentre U D code) ((3 : ℝ) ^ (-j)) (by positivity)
              (Lane4.cutoffPositiveCoefficient M H omega N
                (observationCentre U D code) (by positivity))
              (observationCentre U D code) ((3 : ℝ) ^ (-j))
              (sN N j (observationCentre U D code) omega) s 2
          else 0) ≤
        Cbound * ((delta ^ 2 + eps ^ 8) * (D : ℝ) + prefixD) := by
      calc
        (∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
            (rootLevel U + (D : ℤ)),
            if rootLevel U + (hk0 : ℤ) ≤ j ∧
                Z N ((N : ℤ) - j).toNat
                  (((3 : ℝ) ^ N) • observationCentre U D code) omega < 1 then
              I.err (observationCentre U D code) ((3 : ℝ) ^ (-j)) (by positivity)
                (Lane4.cutoffPositiveCoefficient M H omega N
                  (observationCentre U D code) (by positivity))
                (observationCentre U D code) ((3 : ℝ) ^ (-j))
                (sN N j (observationCentre U D code) omega) s 2
            else 0) =
            (∑ j ∈ F, if j ∈ G then e j else 0) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [F, G, e, z, x, hj]
        _ ≤ Cbound * ((delta ^ 2 + eps ^ 8) * (D : ℝ) + prefixD) := hsum_good
    calc
      (∑ j ∈ Finset.Icc (rootLevel U - (cbuf : ℤ))
          (rootLevel U + (D : ℤ)),
          if rootLevel U + (hk0 : ℤ) ≤ j ∧
              Z N ((N : ℤ) - j).toNat
                (((3 : ℝ) ^ N) • observationCentre U D code) omega < 1 then
            I.err (observationCentre U D code) ((3 : ℝ) ^ (-j)) (by positivity)
              (Lane4.cutoffPositiveCoefficient M H omega N
                (observationCentre U D code) (by positivity))
              (observationCentre U D code) ((3 : ℝ) ^ (-j))
              (sN N j (observationCentre U D code) omega) s 2
          else 0) ≤
          Cbound * ((delta ^ 2 + eps ^ 8) * (D : ℝ) + prefixD) := hsum_good'
      _ ≤ Cbound * (delta ^ 2 + eps ^ 8 + lambdaDet) * (D : ℝ) := by
        simpa [mul_assoc] using hmain
      _ ≤ Cbound * (delta ^ 2 + eps ^ 8 + lambdaDet) * (D : ℝ) +
          Cbound * ((hk0 : ℝ) + (cbuf : ℝ)) := le_add_of_nonneg_right hextra

end Paper
