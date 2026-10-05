module

public import SubdiffusiveProcess.Paper.lfgc_p1_te

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc




open MeasureTheory Filter Topology _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab
  SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem lfgc_p1_wit [NeZero d] (M : GMCModel d) (s eps : ℝ) (heps : 0 < eps)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ℝ≥0∞)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
    (hPrim : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => Praw N m y omega)
        (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
        (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    (en nc ns : ℕ) (enDepth : Fin en → ℕ) (cmpShift : Fin nc → Vec d) (shift : Fin ns → Vec d)
    (buffer m k : ℕ) (z : Vec d) (D : ℕ) (i : aux_lfgc_p1_index_p1Idx en nc ns enDepth cmpShift shift k z D) :
    AEStronglyMeasurable (aux_lfgc_p1_index_p1T en nc ns enDepth cmpShift shift buffer Draw Z m k z D i)
      (chaosSampleLaw M).toMeasure := by
  rw [aux_lfgc_p1_approx2_p1T_eq_pre]
  have key : ∀ (S : Finset ℤ) (f : ℤ → BilateralField d → ℝ),
      (∀ j ∈ S, AEStronglyMeasurable (f j) (chaosSampleLaw M).toMeasure) →
      AEStronglyMeasurable (fun omega => ∑ j ∈ S, f j omega) (chaosSampleLaw M).toMeasure := by
    intro S f hf
    have h := Finset.aestronglyMeasurable_sum S hf
    convert h using 1
    funext omega
    rw [Finset.sum_apply]
  refine key _ _ fun j _ => ?_
  by_cases hN : 0 ≤ ((m + k : ℕ) : ℤ) - j
  · simp only [hN, ite_true]
    exact lfgc_p1_help M s eps heps eta hEta F Praw Rraw Draw Z rawGood hPrim _ _ _ _
  · simp only [hN, ite_false]
    exact aestronglyMeasurable_const

theorem aux_lfgc_p1_wit_p1U_aesm [NeZero d] (M : GMCModel d) (s eps : ℝ) (heps : 0 < eps)
    (m k buffer cL L0 e : ℕ) (w : Vec d) (b : Bool)
    (Y : Bool → ℤ → Vec d → ℕ → BilateralField d → ℝ)
    (hYmeas : ∀ j h, Measurable (Y b j w h)) (D H : ℕ) :
    AEStronglyMeasurable (aux_lfgc_p1_approx_p1U M s eps m k buffer cL L0 e w b Y D H) (chaosSampleLaw M).toMeasure := by
  have hmeas : Measurable (aux_lfgc_p1_approx_p1U M s eps m k buffer cL L0 e w b Y D H) := by
    unfold aux_lfgc_p1_approx_p1U
    refine Finset.measurable_sum _ fun j _ => ?_
    split_ifs
    · exact hYmeas j H
    · exact aux_lfgc_p1_help_summandTr_measurable b M s eps heps (m + k) j w _
    · exact measurable_const
  exact hmeas.aestronglyMeasurable

end SubdiffusiveProcess.Paper
