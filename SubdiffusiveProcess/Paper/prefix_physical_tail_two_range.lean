module

public import SubdiffusiveProcess.Paper.prefix_physical_tail

@[expose] public section

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess
open scoped BigOperators ENNReal Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Paper

theorem prefix_physical_tail_two_range (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (s eps lam A M' : ℝ) (buffer : ℕ)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
    (hlam : 0 < lam) (hA : 0 < A) (hM' : 0 < M') (hM'1 : M' < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ delta0 →
      ∀ eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ (N i : ℕ) (y : Vec d),
        eta N om i y = om ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
      ∀ (F Praw Rraw Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop),
      (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N,
        primitive_scores d M s eps (eta N om)
          (fun j z => F N j z om) (fun j z => Praw N j z om)
          (fun j z => Rraw N j z om) (fun j z => Draw N j z om)
          (fun j z => Z N j z om) (fun j z => rawGood N j z om)) →
      ∀ (m k k0 : ℕ), 1 ≤ k0 →
      ∀ (I : ℕ → Type) [∀ D, Fintype (I D)]
        (depth : (D : ℕ) → I D → ℕ)
        (centre : (D : ℕ) → I D → SpatialCoordinates d)
        (tag : (D : ℕ) → I D → Bool),
      let T : (D : ℕ) → I D → BilateralField d → ℝ := fun D i =>
        aux_prefix_physical_tail_sum (m + k) k buffer D (depth D i)
          (centre D i) Z Draw (tag D i)
      (∀ D, k0 ≤ D → ∀ i : I D,
        (chaosSampleLaw M).toMeasure {om | lam * (D : ℝ) / 4 < T D i om} ≤
          ENNReal.ofReal (2 * Real.exp (-(A * (D : ℝ))))) ∧
      (∀ D, k0 ≤ D → ∀ i : I D,
        (chaosSampleLaw M).toMeasure {om | lam * (D : ℝ) / 4 < T D i om} ≤
          ENNReal.ofReal M') := by
  have hMtwo : M' < 2 := hM'1.trans (by norm_num)
  let B : ℝ := max A (Real.log (2 / M'))
  have hB : 0 < B := hA.trans_le (le_max_left _ _)
  obtain ⟨δ0, hδ0, ht⟩ := prefix_physical_tail d s eps lam B buffer hs heps hlam hB
  refine ⟨δ0, hδ0, ?_⟩
  intro M hδ eta hEta F Praw Rraw Draw Z rawGood hPS m k k0 hk0 I inst depth centre tag
  dsimp only
  have htail := ht M hδ eta hEta F Praw Rraw Draw Z rawGood hPS
  constructor
  · intro D hD i
    refine (htail (m + k) k D (hk0.trans hD) (depth D i) (centre D i) (tag D i)).1.trans
      (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg D))
  · intro D hD i
    refine (htail (m + k) k D (hk0.trans hD) (depth D i) (centre D i) (tag D i)).1.trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hk0.trans hD
    have hBD : Real.log (2 / M') ≤ B * (D : ℝ) :=
      (le_max_right _ _).trans (le_mul_of_one_le_right hB.le hD1)
    have he := Real.exp_le_exp.mpr (neg_le_neg hBD)
    have heq : 2 * Real.exp (-Real.log (2 / M')) = M' := by
      rw [Real.exp_neg, Real.exp_log (div_pos (hM'.trans hMtwo) hM')]
      field_simp
    calc 2 * Real.exp (-(B * (D : ℝ))) ≤ 2 * Real.exp (-Real.log (2 / M')) := by linarith
      _ = M' := heq

end Paper
