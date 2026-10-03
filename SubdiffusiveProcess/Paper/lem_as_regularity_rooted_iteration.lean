module

public import SubdiffusiveProcess.Paper.prop_folded_iteration

@[expose] public section

/-! A deterministic rooted energy estimate from explicit error and bad-scale
budgets. The good predicate is arbitrary and no stochastic stopping length is
assumed. Probability and the physical coefficient chart are separate inputs.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Lane4
open Homogenization hiding Vec
open Homogenization.Book
open scoped ENNReal BigOperators
noncomputable section
namespace Paper

/-- An integer iteration window omits only the initial steps and the declared bad scales. -/
theorem aux_lem_as_regularity_rooted_iteration_bad (good : ℕ → Prop)
    (n m k l h : ℕ) (hnk : n ≤ k) (hlm : l + 7 ≤ m) :
    ∃ bad : Finset ℤ,
      bad ⊆ Finset.Icc ((k + 2 : ℕ) : ℤ) ((l + 2 : ℕ) : ℤ) ∧
      (∀ j : ℕ, k + 2 ≤ j → j ≤ l + 2 → (j : ℤ) ∉ bad → h ≤ j ∧ good (j + 2)) ∧
      (bad.card : ℝ) ≤ h +
        ((@Finset.filter ℕ (fun j => ¬ good j) (Classical.decPred _) (Finset.Icc n m)).card : ℝ) := by
  classical
  let bad := ((Finset.Icc (k + 2) (l + 2)).filter
    (fun j => j < h ∨ ¬ good (j + 2))).image (fun j : ℕ => (j : ℤ))
  refine ⟨bad, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast (Finset.mem_Icc.mp
      (Finset.mem_filter.mp hi).1).1, by exact_mod_cast (Finset.mem_Icc.mp
      (Finset.mem_filter.mp hi).1).2⟩
  · intro j hjk hjl hj
    by_contra hn
    apply hj
    refine Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hjk, hjl⟩, ?_⟩, rfl⟩
    by_cases hh : h ≤ j
    · exact Or.inr (fun hg => hn ⟨hh, hg⟩)
    · exact Or.inl (lt_of_not_ge hh)
  · have hcard := Finset.card_image_le (s := (Finset.Icc (k + 2) (l + 2)).filter
      (fun j => j < h ∨ ¬ good (j + 2))) (f := fun j : ℕ => (j : ℤ))
    have hbound : ((Finset.Icc (k + 2) (l + 2)).filter
        (fun j => j < h ∨ ¬ good (j + 2))).card ≤ h +
        (@Finset.filter ℕ (fun j => ¬ good j) (Classical.decPred _) (Finset.Icc n m)).card := by
      convert aux_prop_folded_iteration_bad_card good n m k l h hnk hlm using 2
      ext j
      simp only [Finset.mem_filter]
    exact_mod_cast hcard.trans hbound

/-- Endpoint losses and the summed iteration error fit the chosen power slack. -/
theorem aux_lem_as_regularity_rooted_iteration_collapse
    (d n m k l h nb : ℕ) (hnk : n ≤ k) (hkl : k < l) (hlm : l + 7 ≤ m)
    (Cg CH CI Cc CP cC cE K C w lam base R T : ℝ)
    (hCg : 0 ≤ Cg) (hCI : 0 ≤ CI) (hCc : 0 ≤ Cc) (hCP : 0 ≤ CP)
    (hcE : 0 ≤ cE) (hcC : 1 ≤ cC) (hK : 0 < K) (hw : 0 ≤ w)
    (hlam : lam = w / (K * 2)) (hbase0 : 0 ≤ base) (hbase : base ≤ 2 * lam)
    (hR : 0 < R) (hT : 0 ≤ T)
    (score e ref W : ℕ → ℝ) (hW0 : ∀ j, 0 ≤ W j)
    (hsc0 : ∀ j, 0 ≤ score j) (he0 : ∀ j, 0 ≤ e j)
    (hsc : ∑ j ∈ Finset.Icc n m, score j ≤ lam * ((m : ℝ) - n))
    (hnb : (nb : ℝ) < 1 + lam * ((m : ℝ) - n))
    (hkn : k - n ≤ nb) (hml : m - 7 - l ≤ nb)
    (bad : Finset ℤ) (hbad : (bad.card : ℝ) ≤ h + nb)
    (he : ∀ j : ℕ, k + 2 ≤ j → j ≤ l + 2 → (j : ℤ) ∉ bad →
      e j ≤ Cg * (base + score (j + 2)))
    (hr : ∀ j : ℕ, n ≤ j → j + 5 ≤ m →
      (cC * Real.exp (cC * (lam * ((m : ℝ) - n))))⁻¹ * R ≤ ref j ∧
      ref j ≤ cC * Real.exp (cC * (lam * ((m : ℝ) - n))) * R)
    (hmono : ∀ i j : ℕ, i ≤ j → j ≤ m →
      W i ≤ Real.sqrt (((3 : ℝ) ^ j) ^ d / ((3 : ℝ) ^ i) ^ d) * W j)
    (hchain : W k ≤ Cc * (Real.sqrt (ref k) *
      Real.exp (CI * (h + 1) * (bad.card + 1) +
        CI * ∑ j ∈ Finset.Icc ((k + 2 : ℕ) : ℤ) ((l + 2 : ℕ) : ℤ),
          (if j ∈ bad then 0 else cE * e j.toNat)) *
      (CP * (Real.sqrt (ref l))⁻¹ * W (l + 2) +
        (5 / 2 : ℝ) * (CH * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
          (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h)) *
          Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 4) *
            (cC * Real.exp (cC * (lam * ((m : ℝ) - n))) * R⁻¹ * T)) +
      (Real.sqrt (ref k))⁻¹ *
        (Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 8) * T)))
    (hCH : 0 ≤ CH)
    (hKG : (d : ℝ) * Real.log 3 + (CI * (h + 1) + 3 * (cE * Cg) * CI) + 2 * cC ≤ K)
    (hC : Real.exp (7 * (d : ℝ) / 2 * Real.log 3 + CI * (h + 1) * (h + 2)) *
      cC ^ 2 * (Cc * (CP + (5 / 2 : ℝ) *
        (CH * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h)) *
          Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 4) +
        Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 8))) ≤ C) :
    W n ≤ C * (3 : ℝ) ^ (w * ((m : ℝ) - n)) * (W m + (Real.sqrt R)⁻¹ * T) := by
  classical
  have hnm : (n : ℝ) ≤ m := by exact_mod_cast (by omega : n ≤ m)
  have hN : 0 ≤ (m : ℝ) - n := sub_nonneg.mpr hnm
  have hlam0 : 0 ≤ lam := by rw [hlam]; positivity
  have hkn' : (k : ℝ) - n ≤ 1 + lam * ((m : ℝ) - n) := by
    have hh : ((k - n : ℕ) : ℝ) ≤ nb := by exact_mod_cast hkn
    rw [Nat.cast_sub hnk] at hh
    linarith only [hh, hnb]
  have hml' : (m : ℝ) - ((l + 2 : ℕ) : ℝ) ≤ 6 + lam * ((m : ℝ) - n) := by
    have hh : ((m - 7 - l : ℕ) : ℝ) ≤ nb := by exact_mod_cast hml
    rw [Nat.cast_sub (by omega : l ≤ m - 7), Nat.cast_sub (by omega : 7 ≤ m)] at hh
    norm_num only [Nat.cast_ofNat, Nat.cast_add] at hh ⊢
    linarith only [hh, hnb]
  have hPt : 1 ≤ Real.sqrt (((3 : ℝ) ^ m) ^ d / ((3 : ℝ) ^ (l + 2)) ^ d) := by
    rw [Real.one_le_sqrt, one_le_div (by positivity)]
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega)) d
  obtain ⟨heA1, heAb⟩ := aux_prop_folded_iteration_eA_bound (k + 2) (l + 2) n m h
    (by omega) (by omega) (by omega) bad e score cE Cg CI base lam nb
    hcE hCg hCI hbase0 hsc0 he0 he hbase hsc hbad hnb
  exact aux_prop_folded_iteration_final_arith (dd := (d : ℝ)) (c1 := 2) (K := K)
    (w := w) (N := (m : ℝ) - n) (cC := cC) (C := C)
    hR hcC heA1 hPt (Real.sqrt_nonneg _) hCc hCP
    (by have hF := Section6ExcessDecay.fractionalHolderConst_nonneg d; positivity)
    (by have hF := Section6ExcessDecay.fractionalHolderConst_nonneg d; positivity)
    hT (hW0 m) (hW0 (l + 2))
    (hr k hnk (by omega)).1 (hr k hnk (by omega)).2 (hr l (by omega) (by omega)).1
    (hmono n k hnk (by omega)) hchain (hmono (l + 2) m (by omega) le_rfl)
    (Nat.cast_nonneg d) le_rfl hKG hK (by positivity) hw hN
    (by rw [hlam]; ring) (mul_nonneg hlam0 hN)
    (aux_prop_folded_iteration_vol_factor d n k _ hkn')
    (aux_prop_folded_iteration_vol_factor d (l + 2) m _ hml') heAb rfl hC

/-- Explicit score and reference budgets imply rooted energy growth with prescribed power loss. -/
theorem lem_as_regularity_rooted_iteration
    (d : ℕ) [NeZero d] (Cg CH CI Cc CP cC eta K C w lam base : ℝ) (h : ℕ)
    (hCg : 0 < Cg) (hCH : 0 < CH) (hCI : 0 < CI) (hCc : 0 < Cc) (hCP : 0 < CP)
    (hcC : 1 ≤ cC) (hK : 0 < K) (hw : 0 ≤ w) (hlam : lam = w / (K * 2))
    (hlamh : lam ≤ 1 / 2) (hbase0 : 0 ≤ base) (hbase : base ≤ 2 * lam)
    (hh : 0 < h) (hth : ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ h < 3 / 5)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hthr : CH * ((3 : ℝ) ^ (-(h : ℝ) / 2) +
      (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) * (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * eta) ≤
        ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ h)
    (hchain : aux_prop_folded_iteration_chain_prop d Cg CH CI Cc CP)
    (hKG : (d : ℝ) * Real.log 3 + (CI * (h + 1) +
      3 * (CH * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) * (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * Cg) * CI) +
        2 * cC ≤ K)
    (hC : Real.exp (7 * (d : ℝ) / 2 * Real.log 3 + CI * (h + 1) * (h + 2)) * cC ^ 2 *
      (Cc * (CP + (5 / 2 : ℝ) * (CH * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
        (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h)) * Section6ExcessDecay.fractionalHolderConst d *
          Real.sqrt (1 / 4) + Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 8))) ≤ C)
    (m n : ℕ) (hnm : n + 26 ≤ m) (z : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m)
    (g : SpatialCoordinates d → Fin d → ℝ)
    (hg : MemHolder (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) (1 / 2) g)
    (a : Vec d → ℝ) (ha : ∀ y, 0 < a y) (data : ScalarTriadicCoeffData (fun y => a (y + 0)))
    (u : H1Function (openCubeSet (originCube d (m : ℤ))))
    (hu : IsDivFormWeakSolutionOn a (cube d (m : ℤ)) u (fun y => g (y + z)))
    (ref score : ℕ → ℝ) (href : ∀ j, 0 < ref j) (hscore0 : ∀ j, 0 ≤ score j)
    (good : ℕ → Prop)
    (hscore : ∑ j ∈ Finset.Icc n m, score j ≤ lam * ((m : ℝ) - n))
    (hcount : ((@Finset.filter ℕ (fun j => ¬ good j) (Classical.decPred _)
      (Finset.Icc n m)).card : ℝ) < 1 + lam * ((m : ℝ) - n))
    (herror : ∀ j : ℕ, j + 2 ≤ m → good (j + 2) →
      paperHomogenizationError (originCube d ((j : ℤ) + 2)) ((j : ℤ) + 2) (1 / 32)
        Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2)
        data.toTriadicCoeffFamily (ref j) ≤ ENNReal.ofReal (Cg * min eta (base + score (j + 2))))
    (hratio : ∀ j : ℕ, n ≤ j → j + 5 ≤ m →
      cC⁻¹ * Real.exp (-(cC * (lam * ((m : ℝ) - n)))) ≤ ref j / ref (m - 2) ∧
      ref j / ref (m - 2) ≤ cC * Real.exp (cC * (lam * ((m : ℝ) - n))))
    (hmono : ∀ i j : ℕ, i ≤ j → j ≤ m →
      vectorNormalizedL2On (openCubeSet (originCube d (i : ℤ))) (fun y => Real.sqrt (a y) • u.grad y) ≤
        Real.sqrt (((3 : ℝ) ^ j) ^ d / ((3 : ℝ) ^ i) ^ d) *
          vectorNormalizedL2On (openCubeSet (originCube d (j : ℤ))) (fun y => Real.sqrt (a y) • u.grad y)) :
    vectorNormalizedL2On (openCubeSet (originCube d (n : ℤ))) (fun y => Real.sqrt (a y) • u.grad y) ≤
      C * (3 : ℝ) ^ (w * ((m : ℝ) - n)) *
        (vectorNormalizedL2On (openCubeSet (originCube d (m : ℤ))) (fun y => Real.sqrt (a y) • u.grad y) +
          (Real.sqrt (ref (m - 2)))⁻¹ * ((3 : ℝ) ^ ((m : ℝ) / 2) *
            halfHolderSeminorm (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) g)) := by
  classical
  obtain ⟨k, l, hnk, hkl, hlm, hgk, hgl, hkn, hml⟩ :=
    aux_prop_folded_iteration_good_pair good n m hnm lam hlamh hcount
  obtain ⟨bad, hbadsub, hgood, hbadcard⟩ :=
    aux_lem_as_regularity_rooted_iteration_bad good n m k l h hnk hlm
  have hrat := fun j hnj hjm => aux_prop_folded_iteration_ratio
    (lt_of_lt_of_le zero_lt_one hcC) (href (m - 2)) (hratio j hnj hjm)
  have hsmall (j : ℕ) (hj : j + 2 ≤ m) (hgj : good (j + 2)) :=
    (herror j hj hgj).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hCg.le))
  have hcap (j : ℕ) (hj : j + 2 ≤ m) (hgj : good (j + 2)) :=
    (hsmall j hj hgj).trans (ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right hCg.le heta1))
  have hW := hchain h hh hth eta heta0 heta1 hthr m k l hkl hlm z hR g hg a ha data u hu
    ref href (cC * Real.exp (cC * (lam * ((m : ℝ) - n))) * (ref (m - 2))⁻¹)
    (fun j hjk hjl => (hrat j (by omega) (by omega)).2.2) bad hbadsub
    (fun j hjk hjl hj => ⟨(hgood j hjk hjl hj).1,
      hsmall j (by omega) (hgood j hjk hjl hj).2⟩)
    (hcap k (by omega) hgk) (hcap l (by omega) hgl)
  dsimp only at hW
  apply aux_lem_as_regularity_rooted_iteration_collapse d n m k l h _ hnk hkl hlm
    Cg CH CI Cc CP cC _ K C w lam base (ref (m - 2)) _
    hCg.le hCI.le hCc.le hCP.le (by positivity) hcC hK hw hlam hbase0 hbase
    (href (m - 2)) (mul_nonneg (by positivity) (aux_prop_folded_iteration_halfHolder_nonneg _ _))
    score (fun j => (paperHomogenizationError (originCube d ((j : ℤ) + 2)) ((j : ℤ) + 2)
      (1 / 4 / 8) Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2)
      data.toTriadicCoeffFamily (ref j)).toReal) ref
    (fun j => vectorNormalizedL2On (openCubeSet (originCube d (j : ℤ)))
      (fun y => Real.sqrt (a y) • u.grad y))
    (fun j => Real.sqrt_nonneg _) hscore0 (fun j => ENNReal.toReal_nonneg)
    hscore hcount hkn hml bad hbadcard ?_
    (fun j hjn hjm => ⟨(hrat j hjn hjm).1, (hrat j hjn hjm).2.1⟩)
    hmono hW hCH.le hKG hC
  intro j hjk hjl hj
  rw [show (1 / 4 / 8 : ℝ) = 1 / 32 by norm_num]
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hCg.le (add_nonneg hbase0 (hscore0 _)))
    ((herror j (by omega) (hgood j hjk hjl hj).2).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (min_le_right _ _) hCg.le)))

end Paper
