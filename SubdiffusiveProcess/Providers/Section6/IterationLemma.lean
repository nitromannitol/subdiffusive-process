import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.Budget
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.ScaledInterface
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.WeightedGoodRunAssembly




namespace SubdiffusiveProcess.Providers.Section6

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

/-! ### Slot algebra (pure algebra over abstract reals) -/

-- REUSE-CANDIDATE: Algsuperdiff/Section4/Provider/ExcessDecay/IterationLemmaProvider.lean
-- Adapted from Algsuperdiff/Section4/Provider/ExcessDecay/IterationLemmaProvider.lean
/-- **The three slots of conclusion (ii).**  The weighted assembly's error budget
`(5/2) M Λ (9 Ci · O + Sd)` splits into the `M · O` slot and the `M · Sd` half of the
`(1+M) Sd` slot, at the common factor `K = 1 + (45/2) Ci Λ`. -/
private theorem slotCollapse {X O Sd Lam Ci M : ℝ} (hX : 0 ≤ X) (hO : 0 ≤ O)
    (hSd : 0 ≤ Sd) (hM : 0 ≤ M) (hLam : 1 ≤ Lam) (hCi : 1 ≤ Ci) :
    X + 5 / 2 * (M * (Lam * (9 * Ci * O + Sd))) + Sd
      ≤ (1 + 45 / 2 * Ci * Lam) * (X + M * O + (1 + M) * Sd) := by
  have hLam0 : (0 : ℝ) ≤ Lam := by linarith only [hLam]
  have hMO : (0 : ℝ) ≤ M * O := mul_nonneg hM hO
  have hMSd : (0 : ℝ) ≤ M * Sd := mul_nonneg hM hSd
  have hCiLam : (1 : ℝ) ≤ Ci * Lam := by
    have h := mul_le_mul hCi hLam (by norm_num) (by linarith only [hCi])
    linarith only [h]
  have hK1 : (1 : ℝ) ≤ 1 + 45 / 2 * Ci * Lam := by
    have he : 45 / 2 * Ci * Lam = 45 / 2 * (Ci * Lam) := by ring
    linarith only [hCiLam, he]
  have t1 : X ≤ (1 + 45 / 2 * Ci * Lam) * X := by
    have h := mul_le_mul_of_nonneg_right hK1 hX
    linarith only [h]
  have t2 : 5 / 2 * (M * (Lam * (9 * Ci * O))) ≤ (1 + 45 / 2 * Ci * Lam) * (M * O) := by
    have he1 : 5 / 2 * (M * (Lam * (9 * Ci * O))) = 45 / 2 * Ci * Lam * (M * O) := by ring
    have he2 : (1 + 45 / 2 * Ci * Lam) * (M * O)
        = M * O + 45 / 2 * Ci * Lam * (M * O) := by ring
    linarith only [he1, he2, hMO]
  have t3 : 5 / 2 * (M * (Lam * Sd)) ≤ (1 + 45 / 2 * Ci * Lam) * (M * Sd) := by
    have hcoef : 5 / 2 * Lam ≤ 1 + 45 / 2 * Ci * Lam := by
      have h := mul_nonneg hLam0 (by linarith only [hCi] : (0 : ℝ) ≤ 45 / 2 * Ci - 5 / 2)
      have he : Lam * (45 / 2 * Ci - 5 / 2) = 45 / 2 * Ci * Lam - 5 / 2 * Lam := by ring
      linarith only [h, he]
    have h := mul_le_mul_of_nonneg_right hcoef hMSd
    have he1 : 5 / 2 * (M * (Lam * Sd)) = 5 / 2 * Lam * (M * Sd) := by ring
    linarith only [h, he1]
  have t4 : Sd ≤ (1 + 45 / 2 * Ci * Lam) * Sd := by
    have h := mul_le_mul_of_nonneg_right hK1 hSd
    linarith only [h]
  have hexpL : X + 5 / 2 * (M * (Lam * (9 * Ci * O + Sd))) + Sd
      = X + (5 / 2 * (M * (Lam * (9 * Ci * O))) + 5 / 2 * (M * (Lam * Sd))) + Sd := by
    ring
  have hexpR : (1 + 45 / 2 * Ci * Lam) * (X + M * O + (1 + M) * Sd)
      = (1 + 45 / 2 * Ci * Lam) * X + (1 + 45 / 2 * Ci * Lam) * (M * O)
        + (1 + 45 / 2 * Ci * Lam) * Sd + (1 + 45 / 2 * Ci * Lam) * (M * Sd) := by ring
  linarith only [t1, t2, t3, t4, hexpL, hexpR]

/-- Composing a bound `q ≤ P·W` with `W ≤ K·V` and a prefactor budget `P·K ≤ R`. -/
private theorem prefactorAbsorb {q P W K V R : ℝ} (hP : 0 ≤ P) (hV : 0 ≤ V)
    (hq : q ≤ P * W) (hW : W ≤ K * V) (hpref : P * K ≤ R) : q ≤ R * V := by
  have h1 : P * W ≤ P * (K * V) := mul_le_mul_of_nonneg_left hW hP
  have h2 : P * (K * V) = P * K * V := by ring
  have h3 : P * K * V ≤ R * V := mul_le_mul_of_nonneg_right hpref hV
  linarith only [hq, h1, h2, h3]

/-! ### The provider theorem -/

/-- **The provider for `SubdiffusiveProcess.Frozen.Section6.iteration_lemma`.**

The frozen theorem's statement verbatim, at the explicit witness
`C = iterConst d`. -/
theorem iteration_lemma (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℕ, 0 < h → ∀ theta ∈ Set.Ioo (0 : ℝ) 1,
      theta ^ h ∈ Set.Ioo (0 : ℝ) (3 / 5) → ∀ n m : ℤ, n < m →
      ∀ U : ℤ → Set (Vec d),
        (∀ j, MeasurableSet (U j) ∧ Bornology.IsBounded (U j)) →
        (∀ j ≤ m, U (j - 1) ⊆ U j) →
        (∀ j ≤ m, ∃ x y : Vec d,
          translatedCube d (j - 2) x ⊆ U j ∧ U j ⊆ translatedCube d j y) →
        ∀ u : Vec d → ℝ, MemLp u 2 (volume.restrict (U m)) →
        ∀ bad : Finset ℤ, bad ⊆ Finset.Icc n m →
        ∀ epsilon defect : ℤ → ℝ,
          (∀ j ∈ Finset.Icc n m, 0 ≤ epsilon j ∧ 0 ≤ defect j) →
          ∀ fit : ℤ → Affine d,
            (∀ j ≤ m, fit j ∈ affineMinimizers (U j) u) →
            (∀ j ∈ Finset.Icc n m, j ∉ bad →
              excess (j - h) (U (j - h)) u ≤ theta ^ h * excess j (U j) u +
                epsilon j * Real.sqrt (vecNormSq (fit j).slope) + defect j) →
            let A := C * (h + 1) * (bad.card + 1) +
              C * ∑ j ∈ Finset.Icc n m, epsilon j
            (3 : ℝ) ^ (-n) * normalizedL2On (U n)
                (fun x => u x - averageOn (U n) u) ≤
              Real.exp A * ((3 : ℝ) ^ (-m) * normalizedL2On (U m)
                (fun x => u x - averageOn (U m) u) +
                ∑ j ∈ Finset.Icc n m, defect j) ∧
            ∀ R : ℝ, 0 ≤ R → (∀ j ∈ Finset.Icc n m, epsilon j ≤ R) →
              excess n (U n) u ≤
                theta ^ (-C * (h + 1) * (bad.card + 1)) * Real.exp A *
                  (theta ^ (m - n) * excess m (U m) u +
                    R * (3 : ℝ) ^ (-m) * normalizedL2On (U m)
                      (fun x => u x - averageOn (U m) u) +
                    (1 + R) * ∑ j ∈ Finset.Icc n m, defect j) := by
  classical
  refine ⟨iterConst d, iterConst_pos d, ?_⟩
  intro h hh theta hθ01 hθh n m hnm U hUmb hnest hsand u hu bad hbad epsilon defect hed
    fit hfit hdec A
  have hA : A = iterConst d * ((h : ℝ) + 1) * ((bad.card : ℝ) + 1)
      + iterConst d * ∑ j ∈ Finset.Icc n m, epsilon j := rfl
  have hθ0 : (0 : ℝ) < theta := hθ01.1
  have hθ1 : theta ≤ 1 := le_of_lt hθ01.2
  have hθh35 : theta ^ h < 3 / 5 := hθh.2
  have hnmle : n ≤ m := le_of_lt hnm
  have hε : ∀ j : ℤ, n ≤ j → j ≤ m → 0 ≤ epsilon j := fun j h1 h2 =>
    (hed j (Finset.mem_Icc.2 ⟨h1, h2⟩)).1
  have hδ : ∀ j : ℤ, n ≤ j → j ≤ m → 0 ≤ defect j := fun j h1 h2 =>
    (hed j (Finset.mem_Icc.2 ⟨h1, h2⟩)).2
  have hSeε0 : (0 : ℝ) ≤ ∑ j ∈ Finset.Icc n m, epsilon j :=
    Finset.sum_nonneg fun j hj => hε j (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2
  have hSdε0 : (0 : ℝ) ≤ ∑ j ∈ Finset.Icc n m, defect j :=
    Finset.sum_nonneg fun j hj => hδ j (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2
  -- the window sandwich at every capped scale
  have hsandc : ∀ k : ℤ, ∃ z : Vec d × Vec d,
      axisCube z.1 ((3 : ℝ) ^ (min k m - 2)) ⊆ cappedWindows U m k ∧
        cappedWindows U m k ⊆ axisCube z.2 ((3 : ℝ) ^ (min k m)) := by
    intro k
    obtain ⟨x, y, hin, hout⟩ := hsand (min k m) (min_le_right _ _)
    obtain ⟨zin, zout, h1, h2⟩ := axisCube_sandwich_of_translateSandwich hin hout
    exact ⟨(zin, zout), h1, h2⟩
  choose z hqin hqout using hsandc
  have hLin : ∀ k : ℤ, (0 : ℝ) < (3 : ℝ) ^ (min k m - 2) :=
    fun k => zpow_pos (by norm_num) _
  have hLout : ∀ k : ℤ, (0 : ℝ) < (3 : ℝ) ^ (min k m) := fun k => zpow_pos (by norm_num) _
  have hvolc : ∀ k : ℤ, 0 < (volume (cappedWindows U m k)).toReal :=
    fun k => volume_toReal_pos_of_sandwich (hLin k) (hqin k) (hqout k)
  have hUn : cappedWindows U m n = U n := cappedWindows_of_le hnmle
  have hUm : cappedWindows U m m = U m := cappedWindows_of_le le_rfl
  have hminn : min n m = n := min_eq_left hnmle
  have hminm : min m m = m := min_self m
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- the degenerate dimension: both conclusions are `0 ≤ (nonnegative)`
    subst hd0
    have hvn : 0 < (volume (U n)).toReal := by rw [← hUn]; exact hvolc n
    have hvm : 0 < (volume (U m)).toReal := by rw [← hUm]; exact hvolc m
    have hLn : normalizedL2On (U n) (fun x => u x - averageOn (U n) u) = 0 :=
      normalizedL2On_sub_average_dim_zero hvn u
    have hLm0 : (0 : ℝ) ≤ normalizedL2On (U m) (fun x => u x - averageOn (U m) u) :=
      normalizedL2On_nonneg _ _
    refine ⟨?_, ?_⟩
    · rw [hLn, mul_zero]
      have hbr : (0 : ℝ) ≤ (3 : ℝ) ^ (-m)
            * normalizedL2On (U m) (fun x => u x - averageOn (U m) u)
          + ∑ j ∈ Finset.Icc n m, defect j := by
        have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-m)
            * normalizedL2On (U m) (fun x => u x - averageOn (U m) u) :=
          mul_nonneg (le_of_lt (zpow_pos (by norm_num) _)) hLm0
        linarith only [h1, hSdε0]
      exact mul_nonneg (le_of_lt (Real.exp_pos _)) hbr
    · intro R hR0 _
      rw [excess_dim_zero hvn n u, excess_dim_zero hvm m u]
      have hbr : (0 : ℝ) ≤ theta ^ (m - n) * 0
          + R * (3 : ℝ) ^ (-m)
              * normalizedL2On (U m) (fun x => u x - averageOn (U m) u)
          + (1 + R) * ∑ j ∈ Finset.Icc n m, defect j := by
        have h1 : (0 : ℝ) ≤ R * (3 : ℝ) ^ (-m)
            * normalizedL2On (U m) (fun x => u x - averageOn (U m) u) :=
          mul_nonneg (mul_nonneg hR0 (le_of_lt (zpow_pos (by norm_num) _))) hLm0
        have h2 : (0 : ℝ) ≤ (1 + R) * ∑ j ∈ Finset.Icc n m, defect j :=
          mul_nonneg (by linarith only [hR0]) hSdε0
        have h3 : theta ^ (m - n) * (0 : ℝ) = 0 := by ring
        linarith only [h1, h2, h3]
      exact mul_nonneg (mul_nonneg (le_of_lt (Real.rpow_pos_of_pos hθ0 _))
        (le_of_lt (Real.exp_pos _))) hbr
  -- the honest dimension
  have hd : d ≠ 0 := Nat.pos_iff_ne_zero.1 hdpos
  -- the error data, extended to all of `ℤ` by zero
  obtain ⟨εt, hεt0, hεteq⟩ : ∃ f : ℤ → ℝ, (∀ k : ℤ, 0 ≤ f k)
      ∧ ∀ j : ℤ, n ≤ j → j ≤ m → f j = epsilon j := by
    refine ⟨fun j => if n ≤ j ∧ j ≤ m then epsilon j else 0, fun k => ?_, fun j hj1 hj2 => ?_⟩
    · show (0 : ℝ) ≤ if n ≤ k ∧ k ≤ m then epsilon k else 0
      split_ifs with hcase
      · exact hε k hcase.1 hcase.2
      · exact le_rfl
    · show (if n ≤ j ∧ j ≤ m then epsilon j else 0) = epsilon j
      rw [if_pos (⟨hj1, hj2⟩ : n ≤ j ∧ j ≤ m)]
  obtain ⟨δt, hδt0, hδteq⟩ : ∃ f : ℤ → ℝ, (∀ k : ℤ, 0 ≤ f k)
      ∧ ∀ j : ℤ, n ≤ j → j ≤ m → f j = defect j := by
    refine ⟨fun j => if n ≤ j ∧ j ≤ m then defect j else 0, fun k => ?_, fun j hj1 hj2 => ?_⟩
    · show (0 : ℝ) ≤ if n ≤ k ∧ k ≤ m then defect k else 0
      split_ifs with hcase
      · exact hδ k hcase.1 hcase.2
      · exact le_rfl
    · show (if n ≤ j ∧ j ≤ m then defect j else 0) = defect j
      rw [if_pos (⟨hj1, hj2⟩ : n ≤ j ∧ j ≤ m)]
  have hSe : ∑ j ∈ Finset.Icc n m, εt j = ∑ j ∈ Finset.Icc n m, epsilon j :=
    Finset.sum_congr rfl fun j hj => by
      rw [Finset.mem_Icc] at hj
      exact hεteq j hj.1 hj.2
  have hSd : ∑ j ∈ Finset.Icc n m, δt j = ∑ j ∈ Finset.Icc n m, defect j :=
    Finset.sum_congr rfl fun j hj => by
      rw [Finset.mem_Icc] at hj
      exact hδteq j hj.1 hj.2
  have hSe0 : (0 : ℝ) ≤ ∑ j ∈ Finset.Icc n m, εt j :=
    Finset.sum_nonneg fun j _ => hεt0 j
  have hSd0 : (0 : ℝ) ≤ ∑ j ∈ Finset.Icc n m, δt j :=
    Finset.sum_nonneg fun j _ => hδt0 j
  -- the remaining measure-theoretic slots of the capped family
  have hmeasc : ∀ k : ℤ, MeasurableSet (cappedWindows U m k) := fun k => (hUmb (min k m)).1
  have hnestc : ∀ k : ℤ, cappedWindows U m k ⊆ cappedWindows U m (k + 1) :=
    cappedWindows_nest hnest
  have huc : ∀ k : ℤ, MemLp u 2 (volume.restrict (cappedWindows U m k)) :=
    fun k => memLp_restrict_of_subset (cappedWindows_subset_top hnest k) hu
  have hminc : ∀ k : ℤ, IsAffineMinimizer (cappedWindows U m k) u
      (fit (min k m)).constant (fit (min k m)).slope :=
    fun k => mem_affineMinimizers_iff.1 (hfit (min k m) (min_le_right _ _))
  have hasp : ∀ k : ℤ, (1 / 9 : ℝ) * (3 : ℝ) ^ (min k m) ≤ (3 : ℝ) ^ (min k m - 2) :=
    fun k => le_of_eq (triadic_aspect (min k m))
  have hratio : ∀ k : ℤ,
      ((volume (cappedWindows U m (k + 1))).toReal
          / (volume (cappedWindows U m k)).toReal) ^ ((d : ℝ)⁻¹ + 1 / 2)
        ≤ volumeRatioConstTriadic d :=
    volumeRatio_le_of_axisCubeSandwich (s := fun k => min k m)
      (fun k => by
        show min (k + 1) m ≤ min k m + 1
        omega) hqin hqout
  have hintc : ∀ (k : ℤ) (a : ℝ) (b : Vec d),
      IntegrableOn (fun x => (u x - affineEval a b x) ^ 2) (cappedWindows U m k) :=
    fun k a b =>
      integrableOn_sub_affineEval_sq_of_axisCubeSandwich (hLout k) (hmeasc k) (hqout k)
        (huc k) a b
  -- the two normalizer bridges
  have hbrLo : ∀ k : ℤ, affineExcessScaled (min k m) (cappedWindows U m k) u
      ≤ affineExcess (cappedWindows U m k) u :=
    fun k => affineExcessScaled_le_affineExcess_of_axisCubeSandwich hd (hqin k) (hqout k) u
  have hbrHi : ∀ k : ℤ, affineExcess (cappedWindows U m k) u
      ≤ 9 * affineExcessScaled (min k m) (cappedWindows U m k) u :=
    fun k => affineExcess_le_affineExcessScaled_of_axisCubeSandwich hd (hqin k) (hqout k) u
  -- the engine's sign slots
  have hEnn : ∀ k : ℤ, (0 : ℝ) ≤ affineExcessScaled (min k m) (cappedWindows U m k) u :=
    fun k => affineExcessScaled_nonneg _ _ _
  have hpnn : ∀ k : ℤ, (0 : ℝ) ≤ slopeMagnitude (fit (min k m)).slope :=
    fun k => slopeMagnitude_nonneg _
  have hκ1 : (1 : ℝ) ≤ iterKappa d := one_le_iterKappa d
  have hCs0 : (0 : ℝ) ≤ iterCstab d := iterCstab_nonneg d
  have hCi1 : (1 : ℝ) ≤ iterCi d := one_le_iterCi d
  have hCi0 : (0 : ℝ) ≤ iterCi d := by linarith only [hCi1]
  have hvr0 : (0 : ℝ) ≤ volumeRatioConstTriadic d :=
    le_trans zero_le_one (one_le_volumeRatioConstTriadic d)
  have hss0 : (0 : ℝ) ≤ slopeStabilityConst d (1 / 9 : ℝ) (volumeRatioConstTriadic d) :=
    slopeStabilityConst_nonneg (by norm_num) hvr0
  
  have hmonoN : ∀ k : ℤ, affineExcess (cappedWindows U m k) u
      ≤ volumeRatioConstTriadic d * affineExcess (cappedWindows U m (k + 1)) u :=
    affineExcess_quasiMonotone_of_nested (cappedWindows U m) u hnestc hvolc hintc hratio
  have hmonoE : ∀ k : ℤ, affineExcessScaled (min k m) (cappedWindows U m k) u
      ≤ iterKappa d * affineExcessScaled (min (k + 1) m) (cappedWindows U m (k + 1)) u := by
    intro k
    have h1 := hbrLo k
    have h2 := hmonoN k
    have h3 := mul_le_mul_of_nonneg_left (hbrHi (k + 1)) hvr0
    have he : volumeRatioConstTriadic d
          * (9 * affineExcessScaled (min (k + 1) m) (cappedWindows U m (k + 1)) u)
        = 9 * volumeRatioConstTriadic d
          * affineExcessScaled (min (k + 1) m) (cappedWindows U m (k + 1)) u := by ring
    rw [iterKappa]
    linarith only [h1, h2, h3, he]
  
  have hstabN : ∀ k : ℤ,
      |slopeMagnitude (fit (min k m)).slope
          - slopeMagnitude (fit (min (k - 1) m)).slope|
        ≤ slopeStabilityConst d (1 / 9 : ℝ) (volumeRatioConstTriadic d)
          * (affineExcess (cappedWindows U m k) u
            + affineExcess (cappedWindows U m (k - 1)) u) :=
    slopeStability_of_axisCubeSandwich (cappedWindows U m) u
      (fun k => (fit (min k m)).constant) (fun k => (fit (min k m)).slope)
      (θ := (1 / 9 : ℝ)) (κ := volumeRatioConstTriadic d) hdpos hLin hLout (by norm_num)
      hasp hqin hqout hmeasc hnestc huc hminc hratio
  have hstabE : ∀ k : ℤ,
      |slopeMagnitude (fit (min k m)).slope
          - slopeMagnitude (fit (min (k - 1) m)).slope|
        ≤ iterCstab d * (affineExcessScaled (min k m) (cappedWindows U m k) u
          + affineExcessScaled (min (k - 1) m) (cappedWindows U m (k - 1)) u) := by
    intro k
    have h1 := hstabN k
    have h2 := mul_le_mul_of_nonneg_left
      (add_le_add (hbrHi k) (hbrHi (k - 1))) hss0
    have he : slopeStabilityConst d (1 / 9 : ℝ) (volumeRatioConstTriadic d)
          * (9 * affineExcessScaled (min k m) (cappedWindows U m k) u
            + 9 * affineExcessScaled (min (k - 1) m) (cappedWindows U m (k - 1)) u)
        = 9 * slopeStabilityConst d (1 / 9 : ℝ) (volumeRatioConstTriadic d)
          * (affineExcessScaled (min k m) (cappedWindows U m k) u
            + affineExcessScaled (min (k - 1) m) (cappedWindows U m (k - 1)) u) := by ring
    rw [iterCstab]
    linarith only [h1, h2, he]
  
  have hendN : ∀ k : ℤ,
      oscNormOn (cappedWindows U m k) u
          ≤ endpointConst d (1 / 9 : ℝ) * (affineExcess (cappedWindows U m k) u
            + slopeMagnitude (fit (min k m)).slope)
        ∧ affineExcess (cappedWindows U m k) u + slopeMagnitude (fit (min k m)).slope
          ≤ endpointConst d (1 / 9 : ℝ) * oscNormOn (cappedWindows U m k) u :=
    fun k => endpoint_comparisons_of_axisCubeSandwich (θ := (1 / 9 : ℝ)) hdpos (hLin k)
      (hLout k) (by norm_num) (hasp k) (hmeasc k) (hqin k) (hqout k) (huc k) (hminc k)
  have hec0 : (0 : ℝ) ≤ endpointConst d (1 / 9 : ℝ) :=
    le_trans zero_le_one (one_le_endpointConst (by norm_num))
  have hoscLo : ∀ k : ℤ,
      oscScaled (min k m) (cappedWindows U m k) u ≤ oscNormOn (cappedWindows U m k) u :=
    fun k => oscScaled_le_oscNormOn_of_axisCubeSandwich hd (hqin k) (hqout k) u
  have hoscHi : ∀ k : ℤ, oscNormOn (cappedWindows U m k) u
      ≤ 9 * oscScaled (min k m) (cappedWindows U m k) u :=
    fun k => oscNormOn_le_oscScaled_of_axisCubeSandwich hd (hqin k) (hqout k) u
  have hlo : ∀ k : ℤ, oscScaled (min k m) (cappedWindows U m k) u
      ≤ iterCi d * (affineExcessScaled (min k m) (cappedWindows U m k) u
        + slopeMagnitude (fit (min k m)).slope) := by
    intro k
    have h1 := hoscLo k
    have h2 := (hendN k).1
    have h3 := mul_le_mul_of_nonneg_left (hbrHi k) hec0
    have h4 : (0 : ℝ) ≤ endpointConst d (1 / 9 : ℝ)
        * slopeMagnitude (fit (min k m)).slope := mul_nonneg hec0 (hpnn k)
    have he1 : endpointConst d (1 / 9 : ℝ) * (affineExcess (cappedWindows U m k) u
          + slopeMagnitude (fit (min k m)).slope)
        = endpointConst d (1 / 9 : ℝ) * affineExcess (cappedWindows U m k) u
          + endpointConst d (1 / 9 : ℝ) * slopeMagnitude (fit (min k m)).slope := by ring
    have he2 : endpointConst d (1 / 9 : ℝ)
          * (9 * affineExcessScaled (min k m) (cappedWindows U m k) u)
        = 9 * endpointConst d (1 / 9 : ℝ)
          * affineExcessScaled (min k m) (cappedWindows U m k) u := by ring
    have he3 : 9 * endpointConst d (1 / 9 : ℝ)
          * (affineExcessScaled (min k m) (cappedWindows U m k) u
            + slopeMagnitude (fit (min k m)).slope)
        = 9 * endpointConst d (1 / 9 : ℝ)
            * affineExcessScaled (min k m) (cappedWindows U m k) u
          + 9 * (endpointConst d (1 / 9 : ℝ)
            * slopeMagnitude (fit (min k m)).slope) := by ring
    rw [iterCi]
    linarith only [h1, h2, h3, h4, he1, he2, he3]
  have hhi : ∀ k : ℤ, affineExcessScaled (min k m) (cappedWindows U m k) u
        + slopeMagnitude (fit (min k m)).slope
      ≤ iterCi d * oscScaled (min k m) (cappedWindows U m k) u := by
    intro k
    have h1 := hbrLo k
    have h2 := (hendN k).2
    have h3 := mul_le_mul_of_nonneg_left (hoscHi k) hec0
    have he : endpointConst d (1 / 9 : ℝ)
          * (9 * oscScaled (min k m) (cappedWindows U m k) u)
        = 9 * endpointConst d (1 / 9 : ℝ)
          * oscScaled (min k m) (cappedWindows U m k) u := by ring
    rw [iterCi]
    linarith only [h1, h2, h3, he]
  -- the frozen contraction, consumed in its own normalization
  have hdecayt : ∀ j : ℤ, n ≤ j → j ≤ m → j ∉ bad →
      affineExcessScaled (min (j - (h : ℤ)) m) (cappedWindows U m (j - (h : ℤ))) u
        ≤ theta ^ h * affineExcessScaled (min j m) (cappedWindows U m j) u
          + εt j * slopeMagnitude (fit (min j m)).slope + δt j := by
    intro j hj1 hj2 hjB
    have hjhm : min (j - (h : ℤ)) m = j - (h : ℤ) := min_eq_left (by omega)
    have hjm : min j m = j := min_eq_left hj2
    simp only [cappedWindows, hjhm, hjm]
    rw [← excess_eq_affineExcessScaled, ← excess_eq_affineExcessScaled,
      hεteq j hj1 hj2, hδteq j hj1 hj2]
    exact hdec j (Finset.mem_Icc.2 ⟨hj1, hj2⟩) hjB
  -- the two run constants
  have hgcbc1 : (1 : ℝ) ≤ goodConst h (iterKappa d) (iterCstab d)
      * badConst (iterKappa d) (iterCstab d) := by
    have hg := one_le_goodConst h hκ1 hCs0
    have hb := one_le_badConst hκ1 hCs0
    have hm := mul_le_mul_of_nonneg_left hb (by linarith only [hg] :
      (0 : ℝ) ≤ goodConst h (iterKappa d) (iterCstab d))
    linarith only [hm, hg]
  have hgcbc0 : (0 : ℝ) ≤ goodConst h (iterKappa d) (iterCstab d)
      * badConst (iterKappa d) (iterCstab d) := by linarith only [hgcbc1]
  have hOn : oscScaled n (U n) u
      = (3 : ℝ) ^ (-n) * normalizedL2On (U n) (fun x => u x - averageOn (U n) u) := rfl
  have hOm : oscScaled m (U m) u
      = (3 : ℝ) ^ (-m) * normalizedL2On (U m) (fun x => u x - averageOn (U m) u) := rfl
  have hO0 : (0 : ℝ) ≤ oscScaled m (U m) u := oscScaled_nonneg _ _ _
  rw [hA]
  refine ⟨?_, ?_⟩
  · -- conclusion (i)
    have hcbi := iterationSlopeBound
      (E := fun k => affineExcessScaled (min k m) (cappedWindows U m k) u)
      (p := fun k => slopeMagnitude (fit (min k m)).slope) (ε := εt) (δ := δt)
      (θ := theta) (h := h) (κ := iterKappa d) (Cstab := iterCstab d) hθ0 hθh35 hEnn
      hpnn hεt0 hδt0 hκ1 hCs0 hmonoE hstabE hnmle bad hdecayt
      (fun k => oscScaled (min k m) (cappedWindows U m k) u) hCi1 (hlo n) (hhi m)
    simp only [hminn, hminm, hUn, hUm, hSe, hSd, Finset.inter_eq_left.2 hbad] at hcbi
    set Q : ℝ := (goodConst h (iterKappa d) (iterCstab d)
        * badConst (iterKappa d) (iterCstab d)) ^ (3 * bad.card + 3)
      * Real.exp (goodRate (iterCstab d) * ∑ j ∈ Finset.Icc n m, epsilon j) with hQdef
    have hQ0 : (0 : ℝ) ≤ Q := by
      rw [hQdef]
      exact mul_nonneg (pow_nonneg hgcbc0 _) (le_of_lt (Real.exp_pos _))
    have hCi2Q0 : (0 : ℝ) ≤ iterCi d ^ 2 * Q := mul_nonneg (by positivity) hQ0
    have hV0 : (0 : ℝ) ≤ oscScaled m (U m) u + ∑ j ∈ Finset.Icc n m, defect j := by
      linarith only [hO0, hSdε0]
    have hcbi' : oscScaled n (U n) u
        ≤ iterCi d ^ 2 * Q * (oscScaled m (U m) u + ∑ j ∈ Finset.Icc n m, defect j) := by
      rw [hQdef]
      calc oscScaled n (U n) u
          ≤ iterCi d ^ 2 * (goodConst h (iterKappa d) (iterCstab d)
              * badConst (iterKappa d) (iterCstab d)) ^ (3 * bad.card + 3)
            * Real.exp (goodRate (iterCstab d) * ∑ j ∈ Finset.Icc n m, epsilon j)
            * (oscScaled m (U m) u + ∑ j ∈ Finset.Icc n m, defect j) := hcbi
        _ = iterCi d ^ 2 * ((goodConst h (iterKappa d) (iterCstab d)
              * badConst (iterKappa d) (iterCstab d)) ^ (3 * bad.card + 3)
            * Real.exp (goodRate (iterCstab d) * ∑ j ∈ Finset.Icc n m, epsilon j))
            * (oscScaled m (U m) u + ∑ j ∈ Finset.Icc n m, defect j) := by ring
    have hb1 := iterPrefactorOne_le d hh bad.card
      (Se := ∑ j ∈ Finset.Icc n m, epsilon j) hSeε0
    have hb1' : iterCi d ^ 2 * Q
        ≤ Real.exp (iterConst d * ((h : ℝ) + 1) * ((bad.card : ℝ) + 1)
          + iterConst d * ∑ j ∈ Finset.Icc n m, epsilon j) := by
      have h9 : iterCi d ^ 2 * Q ≤ 9 * (iterCi d ^ 2 * Q) := by linarith only [hCi2Q0]
      have he : 9 * (iterCi d ^ 2 * Q) = 9 * iterCi d ^ 2 * Q := by ring
      rw [hQdef] at h9 he ⊢
      linarith only [h9, he, hb1]
    rw [← hOn, ← hOm]
    calc oscScaled n (U n) u
        ≤ iterCi d ^ 2 * Q * (oscScaled m (U m) u + ∑ j ∈ Finset.Icc n m, defect j) := hcbi'
      _ ≤ Real.exp (iterConst d * ((h : ℝ) + 1) * ((bad.card : ℝ) + 1)
            + iterConst d * ∑ j ∈ Finset.Icc n m, epsilon j)
          * (oscScaled m (U m) u + ∑ j ∈ Finset.Icc n m, defect j) :=
        mul_le_mul_of_nonneg_right hb1' hV0
  · -- conclusion (ii)
    intro R hR0 hRle
    set Lam : ℝ := (goodConst h (iterKappa d) (iterCstab d)
        * badConst (iterKappa d) (iterCstab d)) ^ (3 * bad.card + 3)
      * Real.exp (goodRate (iterCstab d) * ∑ j ∈ Finset.Icc n m, εt j) with hLamdef
    have hLam1 : (1 : ℝ) ≤ Lam := by
      have h1 : (1 : ℝ) ≤ (goodConst h (iterKappa d) (iterCstab d)
          * badConst (iterKappa d) (iterCstab d)) ^ (3 * bad.card + 3) :=
        one_le_pow₀ hgcbc1
      have h2 : (1 : ℝ) ≤ Real.exp (goodRate (iterCstab d)
          * ∑ j ∈ Finset.Icc n m, εt j) := by
        rw [Real.one_le_exp_iff]
        exact mul_nonneg (goodRate_nonneg hCs0) hSe0
      have hm := mul_le_mul h1 h2 (by norm_num) (by linarith only [h1])
      rw [hLamdef]
      linarith only [hm]
    have hLam0 : (0 : ℝ) ≤ Lam := by linarith only [hLam1]
    have hTop0 : (0 : ℝ) ≤ 9 * iterCi d * oscScaled m (U m) u
        + ∑ j ∈ Finset.Icc n m, δt j := by
      have h1 : (0 : ℝ) ≤ 9 * iterCi d * oscScaled m (U m) u :=
        mul_nonneg (by linarith only [hCi0]) hO0
      linarith only [h1, hSd0]
    -- the top-scale endpoint bound feeding the error scale
    have hEpm : affineExcessScaled (min m m) (cappedWindows U m m) u
          + slopeMagnitude (fit (min m m)).slope
        ≤ 9 * iterCi d * oscScaled m (U m) u := by
      have h1 := hhi m
      rw [hminm, hUm] at h1
      have h2 : iterCi d * oscScaled m (U m) u ≤ 9 * (iterCi d * oscScaled m (U m) u) := by
        have h3 : (0 : ℝ) ≤ iterCi d * oscScaled m (U m) u := mul_nonneg hCi0 hO0
        linarith only [h3]
      have he : 9 * (iterCi d * oscScaled m (U m) u)
          = 9 * iterCi d * oscScaled m (U m) u := by ring
      rw [hminm, hUm]
      linarith only [h1, h2, he]
    -- the uniform slope bound on `[n,m]`
    have hcbk := combinedBound
      (E := fun k => affineExcessScaled (min k m) (cappedWindows U m k) u)
      (p := fun k => slopeMagnitude (fit (min k m)).slope) (ε := εt) (δ := δt)
      (θ := theta) (h := h) (κ := iterKappa d) (Cstab := iterCstab d) hθ0 hθh35 hEnn
      hpnn hεt0 hδt0 hκ1 hCs0 hmonoE hstabE bad hdecayt
    have hpQ : ∀ j : ℤ, n ≤ j → j ≤ m →
        slopeMagnitude (fit (min j m)).slope
          ≤ Lam * (9 * iterCi d * oscScaled m (U m) u
            + ∑ j ∈ Finset.Icc n m, δt j) := by
      intro j hj1 hj2
      have hk := hcbk j hj1 hj2
      have hcard : 3 * (bad ∩ Finset.Icc j m).card + 3 ≤ 3 * bad.card + 3 := by
        have hc := Finset.card_le_card
          (Finset.inter_subset_left : bad ∩ Finset.Icc j m ⊆ bad)
        omega
      have hpowmono : (goodConst h (iterKappa d) (iterCstab d)
            * badConst (iterKappa d) (iterCstab d))
              ^ (3 * (bad ∩ Finset.Icc j m).card + 3)
          ≤ (goodConst h (iterKappa d) (iterCstab d)
            * badConst (iterKappa d) (iterCstab d)) ^ (3 * bad.card + 3) :=
        pow_le_pow_right₀ hgcbc1 hcard
      have hsubset : Finset.Icc j m ⊆ Finset.Icc n m := by
        intro x hx
        simp only [Finset.mem_Icc] at hx ⊢
        omega
      have hεsub : ∑ x ∈ Finset.Icc j m, εt x ≤ ∑ x ∈ Finset.Icc n m, εt x :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset fun x _ _ => hεt0 x
      have hδsub : ∑ x ∈ Finset.Icc j m, δt x ≤ ∑ x ∈ Finset.Icc n m, δt x :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset fun x _ _ => hδt0 x
      have hexpmono : Real.exp (goodRate (iterCstab d) * ∑ x ∈ Finset.Icc j m, εt x)
          ≤ Real.exp (goodRate (iterCstab d) * ∑ x ∈ Finset.Icc n m, εt x) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hεsub (goodRate_nonneg hCs0))
      have hpref : (goodConst h (iterKappa d) (iterCstab d)
              * badConst (iterKappa d) (iterCstab d))
              ^ (3 * (bad ∩ Finset.Icc j m).card + 3)
            * Real.exp (goodRate (iterCstab d) * ∑ x ∈ Finset.Icc j m, εt x)
          ≤ Lam := by
        rw [hLamdef]
        exact mul_le_mul hpowmono hexpmono (le_of_lt (Real.exp_pos _))
          (pow_nonneg hgcbc0 _)
      have hbase : affineExcessScaled (min m m) (cappedWindows U m m) u
            + slopeMagnitude (fit (min m m)).slope + ∑ x ∈ Finset.Icc j m, δt x
          ≤ 9 * iterCi d * oscScaled m (U m) u + ∑ x ∈ Finset.Icc n m, δt x := by
        linarith only [hEpm, hδsub]
      have hbase0 : (0 : ℝ) ≤ affineExcessScaled (min m m) (cappedWindows U m m) u
          + slopeMagnitude (fit (min m m)).slope + ∑ x ∈ Finset.Icc j m, δt x := by
        have h1 := hEnn m
        have h2 := hpnn m
        have h3 : (0 : ℝ) ≤ ∑ x ∈ Finset.Icc j m, δt x :=
          Finset.sum_nonneg fun x _ => hδt0 x
        linarith only [h1, h2, h3]
      calc slopeMagnitude (fit (min j m)).slope
          ≤ affineExcessScaled (min j m) (cappedWindows U m j) u
            + slopeMagnitude (fit (min j m)).slope := by linarith only [hEnn j]
        _ ≤ (goodConst h (iterKappa d) (iterCstab d)
                * badConst (iterKappa d) (iterCstab d))
                ^ (3 * (bad ∩ Finset.Icc j m).card + 3)
              * Real.exp (goodRate (iterCstab d) * ∑ x ∈ Finset.Icc j m, εt x)
              * (affineExcessScaled (min m m) (cappedWindows U m m) u
                + slopeMagnitude (fit (min m m)).slope
                + ∑ x ∈ Finset.Icc j m, δt x) := hk
        _ ≤ Lam * (9 * iterCi d * oscScaled m (U m) u
              + ∑ j ∈ Finset.Icc n m, δt j) :=
            mul_le_mul hpref hbase hbase0 hLam0
    -- the error scale, and the weighted assembly
    have hMp0 : (0 : ℝ) ≤ R * (Lam * (9 * iterCi d * oscScaled m (U m) u
        + ∑ j ∈ Finset.Icc n m, δt j)) := mul_nonneg hR0 (mul_nonneg hLam0 hTop0)
    have hwM : ∀ j : ℤ, n ≤ j → j ≤ m →
        εt j * slopeMagnitude (fit (min j m)).slope
          ≤ R * (Lam * (9 * iterCi d * oscScaled m (U m) u
            + ∑ j ∈ Finset.Icc n m, δt j)) := by
      intro j hj1 hj2
      have h1 : εt j ≤ R := by
        rw [hεteq j hj1 hj2]
        exact hRle j (Finset.mem_Icc.2 ⟨hj1, hj2⟩)
      exact mul_le_mul h1 (hpQ j hj1 hj2) (hpnn j) hR0
    have hasm := weightedAssemble
      (E := fun k => affineExcessScaled (min k m) (cappedWindows U m k) u) (δ := δt)
      (w := fun j => εt j * slopeMagnitude (fit (min j m)).slope) (θ := theta) (h := h)
      (κ := iterKappa d) hθ0 hθ1 hθh35 hEnn hδt0 hMp0 hκ1 hmonoE bad hwM hdecayt n
      le_rfl hnmle
    simp only [hminn, hminm, hUn, hUm, Finset.inter_eq_left.2 hbad] at hasm
    -- the three slots and the prefactor budget
    have hXeq : affineExcessScaled n (U n) u = excess n (U n) u :=
      (excess_eq_affineExcessScaled n (U n) u).symm
    have hXmeq : affineExcessScaled m (U m) u = excess m (U m) u :=
      (excess_eq_affineExcessScaled m (U m) u).symm
    rw [hXeq, hXmeq] at hasm
    have hX0 : (0 : ℝ) ≤ theta ^ (m - n) * excess m (U m) u := by
      have h1 : (0 : ℝ) ≤ excess m (U m) u := by
        rw [excess_eq_affineExcessScaled]
        exact affineExcessScaled_nonneg _ _ _
      exact mul_nonneg (le_of_lt (zpow_pos hθ0 _)) h1
    have hslot := slotCollapse (X := theta ^ (m - n) * excess m (U m) u)
      (O := oscScaled m (U m) u) (Sd := ∑ j ∈ Finset.Icc n m, δt j) (Lam := Lam)
      (Ci := iterCi d) (M := R) hX0 hO0 hSd0 hR0 hLam1 hCi1
    have hpref2 := iterPrefactorTwo_le d hh bad.card hθ0 hθ1 hSe0
    have hP0 : (0 : ℝ) ≤ (2 * (iterKappa d * theta⁻¹) ^ (h + 2)) ^ (bad.card + 1) := by
      have hb : (0 : ℝ) ≤ 2 * (iterKappa d * theta⁻¹) ^ (h + 2) := by
        have h1 : (1 : ℝ) ≤ (iterKappa d * theta⁻¹) ^ (h + 2) :=
          one_le_pow₀ (one_le_mul_inv hκ1 hθ0 hθ1)
        linarith only [h1]
      exact pow_nonneg hb _
    have hV0 : (0 : ℝ) ≤ theta ^ (m - n) * excess m (U m) u
        + R * oscScaled m (U m) u + (1 + R) * ∑ j ∈ Finset.Icc n m, δt j := by
      have h1 : (0 : ℝ) ≤ R * oscScaled m (U m) u := mul_nonneg hR0 hO0
      have h2 : (0 : ℝ) ≤ (1 + R) * ∑ j ∈ Finset.Icc n m, δt j :=
        mul_nonneg (by linarith only [hR0]) hSd0
      linarith only [hX0, h1, h2]
    have hfinal := prefactorAbsorb hP0 hV0 hasm hslot hpref2
    rw [hSd] at hfinal
    have hthetapow : theta ^ (-iterConst d * ((h : ℝ) + 1) * ((bad.card : ℝ) + 1))
        = theta ^ (-(iterConst d * ((h : ℝ) + 1) * ((bad.card : ℝ) + 1))) := by
      congr 1
      ring
    rw [hthetapow]
    calc excess n (U n) u
        ≤ theta ^ (-(iterConst d * ((h : ℝ) + 1) * ((bad.card : ℝ) + 1)))
            * Real.exp (iterConst d * ((h : ℝ) + 1) * ((bad.card : ℝ) + 1)
              + iterConst d * ∑ j ∈ Finset.Icc n m, εt j)
            * (theta ^ (m - n) * excess m (U m) u + R * oscScaled m (U m) u
              + (1 + R) * ∑ j ∈ Finset.Icc n m, defect j) := hfinal
      _ = theta ^ (-(iterConst d * ((h : ℝ) + 1) * ((bad.card : ℝ) + 1)))
            * Real.exp (iterConst d * ((h : ℝ) + 1) * ((bad.card : ℝ) + 1)
              + iterConst d * ∑ j ∈ Finset.Icc n m, epsilon j)
            * (theta ^ (m - n) * excess m (U m) u
              + R * (3 : ℝ) ^ (-m)
                * normalizedL2On (U m) (fun x => u x - averageOn (U m) u)
              + (1 + R) * ∑ j ∈ Finset.Icc n m, defect j) := by
            rw [hSe, hOm]
            ring

end

end SubdiffusiveProcess.Providers.Section6
