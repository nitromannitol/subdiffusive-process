module

public import SubdiffusiveProcess.Paper.prefix_physical_tail_two_range
public import SubdiffusiveProcess.Paper.lem_witness

@[expose] public section

open MeasureTheory Filter SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess
open scoped BigOperators ENNReal Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Paper

theorem prefix_physical_witness (d : ℕ) [NeZero d]
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
      ∀ (B : ℕ+ → MeasurableSpace (BilateralField d))
        (bound : ℕ+ → ℝ), (∀ h, 0 ≤ bound h) →
      ∀ (w : ℕ → ℕ+), Function.Injective w →
      ∀ K : ℕ, k0 ≤ K →
      ∀ (p Merr q r K' Cgeom v : ℝ),
      0 < p → 0 ≤ Merr → 0 < q → q ≤ 1 → 0 < r → r < 1 →
      K' = lam * (1 - r) / 4 → 0 ≤ Cgeom → 0 ≤ v →
      (∀ D, (Fintype.card (I D) : ℝ) ≤ Cgeom * Real.exp (v * (D : ℝ))) →
      ∀ U : (D : ℕ) → I D → ℕ → BilateralField d → ℝ,
      (∀ D i, AEStronglyMeasurable (T D i) (chaosSampleLaw M).toMeasure) →
      (∀ D i H, AEStronglyMeasurable (U D i H) (chaosSampleLaw M).toMeasure) →
      (∀ D H, k0 ≤ D → D ≤ H → ∀ i : I D,
        eLpNorm (fun om => T D i om - U D i H om) (ENNReal.ofReal p)
          (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal ((D : ℝ) * Merr * q ^ H)) →
      (∀ D H j, k0 ≤ D → D ≤ j → j ≤ H → ∀ i : I D,
        StronglyMeasurable[B (w H)] (U D i j)) →
      (∀ H, k0 ≤ H →
        Cgeom * (M' * Real.exp (A * ((K : ℝ) - 1))) * Real.exp (-((A - v) * (H : ℝ))) +
          ((H : ℝ) + 1) * Cgeom * Real.exp (v * (H : ℝ)) *
            Paper.aux_prefix_error p Merr q r K' H ≤ (1 / 3) * bound (w H)) →
      (∀ H, K ≤ H →
        Cgeom * 2 * Real.exp (-((A - v) * (H : ℝ))) +
          ((H : ℝ) + 1) * Cgeom * Real.exp (v * (H : ℝ)) *
            Paper.aux_prefix_error p Merr q r K' H ≤ (1 / 3) * bound (w H)) →
      ∀ Sigma : Set (BilateralField d),
      (∀ om, om ∈ Sigma → ∀ D i,
        Tendsto (fun H => U D i H om) atTop (𝓝 (T D i om))) →
      ∃ W : ℕ+ → Set (BilateralField d),
        (∀ h, MeasurableSet[B h] (W h)) ∧
        (∀ h, (chaosSampleLaw M).toMeasure (W h) ≤ ENNReal.ofReal (bound h)) ∧
        Sigma ∩ {om | ∃ D, k0 ≤ D ∧ ∃ i : I D, lam * (D : ℝ) ≤ T D i om} ⊆
          ⋃ h : ℕ+, W h := by
  obtain ⟨δ0, hδ0, ht⟩ := prefix_physical_tail_two_range
    d s eps lam A M' buffer hs heps hlam hA hM' hM'1
  refine ⟨δ0, hδ0, ?_⟩
  intro M hδ eta hEta F Praw Rraw Draw Z rawGood hPS m k k0 hk0 I inst depth centre tag
  dsimp only
  intro B bound hbound w hw K hKk0 p Merr q r K' Cgeom v
    hp hMerr hq hq1 hr hr1 hKdef hCgeom hv hcard U hT hU herror hwindow
    hbudgetSmall hbudgetLarge Sigma hlimit
  obtain ⟨htail, hbaseMarkov⟩ := ht M hδ eta hEta F Praw Rraw Draw Z rawGood hPS
    m k k0 hk0 I depth centre tag
  exact aux_lem_witness_prefix_cover_two_range
    (chaosSampleLaw M).toMeasure B bound hbound w hw k0 K hk0 hKk0 I
    lam p Merr M' q r K' Cgeom v A 2
    hlam hp hMerr hM'.le hA.le hq hq1 hr hr1 hKdef hCgeom hv (by norm_num) hcard
    (fun D i => aux_prefix_physical_tail_sum (m + k) k buffer D (depth D i)
      (centre D i) Z Draw (tag D i)) U hT hU herror htail hbaseMarkov hwindow
    hbudgetSmall hbudgetLarge Sigma hlimit

end Paper
