module

public import SubdiffusiveProcess.Paper.prefix_tail_score_bridge
public import SubdiffusiveProcess.PrefixTailNumerics
public import SubdiffusiveProcess.Paper.prefix_score_window_tail
public import SubdiffusiveProcess.Paper.Foundations.PrefixFieldTransport

@[expose] public section

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess
open scoped BigOperators ENNReal Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess.Paper

theorem prefix_physical_tail (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (s eps lam A : ℝ) (buffer : ℕ)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
    (hlam : 0 < lam) (hA : 0 < A) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ delta0 →
      ∀ eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d,
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
      ∀ (N k D : ℕ), 1 ≤ D → ∀ (e : ℕ) (w : SpatialCoordinates d) (useD : Bool),
        ((chaosSampleLaw M).toMeasure {om | lam * (D : ℝ) / 4 <
            aux_prefix_physical_tail_sum N k buffer D e w Z Draw useD om} ≤
          ENNReal.ofReal (2 * Real.exp (-(A * (D : ℝ))))) ∧
        ((chaosSampleLaw M).toMeasure {om | lam * (D : ℝ) / 4 <
            aux_prefix_physical_tail_sum N k buffer D e w Z Draw useD om} ≤
          ENNReal.ofReal (1 / 2 : ℝ)) := by
  let L : ℝ := 2 * (buffer : ℝ) + 2
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨δ0, hδ0, htail⟩ := prefix_score_window_tail
    (Ω := BilateralField d) d s eps (lam / L) A hs heps (div_pos hlam hL) hA
  refine ⟨δ0, hδ0, ?_⟩
  intro M hδ eta hEta F Praw Rraw Draw Z rawGood hPS N k D hD e w useD
  let a : ℤ := (k : ℤ) - (e : ℤ) - (buffer : ℤ)
  let n : ℕ := ((N : ℤ) - min (N : ℤ) (a + (D : ℤ) + 2 * (buffer : ℤ))).toNat
  let K : ℕ := D + 2 * buffer
  let z : Vec d := (3 : ℝ) ^ N • w
  let X : ℕ → BilateralField d → ℝ := fun j om =>
    if useD then (Draw N j z om).toReal else Z N j z om
  have hPSN : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      primitive_scores d M s eps (eta N om)
        (fun j z => F N j z om) (fun j z => Praw N j z om)
        (fun j z => Rraw N j z om) (fun j z => Draw N j z om)
        (fun j z => Z N j z om) (fun j z => rawGood N j z om) :=
    hPS.mono (fun _ hp => hp N)
  have ht := htail M hδ (chaosSampleLaw M).toMeasure (eta N)
    (prefix_eta_aemeasurable M eta hEta N) (prefix_eta_law M eta hEta N)
    (F N) (Praw N) (Rraw N) (Draw N) (Z N) (rawGood N) hPSN n K z useD
  have hlen : (K : ℝ) + 1 ≤ L * (D : ℝ) := by
    have hD' : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    dsimp [K, L]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) buffer]
  have hthreshold : (lam / L) * ((K : ℝ) + 1) / 4 ≤ lam * (D : ℝ) / 4 := by
    have hh := mul_le_mul_of_nonneg_left hlen (div_pos hlam hL).le
    have heq : lam / L * (L * (D : ℝ)) = lam * (D : ℝ) := by field_simp
    rw [heq] at hh
    linarith
  have hdom : (chaosSampleLaw M).toMeasure {om | lam * (D : ℝ) / 4 <
      aux_prefix_physical_tail_sum N k buffer D e w Z Draw useD om} ≤
      (chaosSampleLaw M).toMeasure {om | (lam / L) * ((K : ℝ) + 1) / 4 <
        ∑ j ∈ Finset.Icc n (n + K), X j om} := by
    apply measure_mono_ae
    filter_upwards [hPSN] with om hp
    intro hlarge
    have hnonneg : ∀ j, 0 ≤ X j om := by
      intro j
      dsimp only [X]
      split_ifs
      · exact ENNReal.toReal_nonneg
      · obtain ⟨_, _, _, _, _, _, _, _, _, hz, _⟩ := hp
        exact (hz j z).2.1
    have hpadded := aux_prefix_physical_tail_padded_sum_le N D buffer a
      (fun j => X j om) hnonneg
    have ha : a + (D : ℤ) + 2 * (buffer : ℤ) =
        (k : ℤ) - (e : ℤ) + (D : ℤ) + (buffer : ℤ) := by dsimp [a]; ring
    have hsum : aux_prefix_physical_tail_sum N k buffer D e w Z Draw useD om ≤
        ∑ j ∈ Finset.Icc n (n + K), X j om := by
      convert hpadded using 1 <;> simp only [aux_prefix_physical_tail_sum, ha, a, n, K, X, z,
        Nat.add_assoc]
    exact lt_of_le_of_lt hthreshold (lt_of_lt_of_le hlarge hsum)
  constructor
  · refine (hdom.trans ht.1).trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Real.exp_le_exp.mpr
    have hKD : (D : ℝ) ≤ (K : ℝ) + 1 := by dsimp [K]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) buffer]
    have hh := mul_le_mul_of_nonneg_left hKD hA.le
    linarith
  · exact hdom.trans ht.2

end SubdiffusiveProcess.Paper
