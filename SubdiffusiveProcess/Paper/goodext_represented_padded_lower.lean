import SubdiffusiveProcess.Paper.goodext_adjacent_reference
import SubdiffusiveProcess.Paper.goodext_prefix_layer_bound
import SubdiffusiveProcess.Analysis.ReferenceLowerLimit

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4 SubdiffusiveProcess.CoarseGrainingVocab
open scoped Topology ENNReal BigOperators
noncomputable section
namespace Paper

/-- The padded lower coefficient is eventually controlled in the child reference on the strict represented prefix event. -/
theorem goodext_represented_padded_lower
    {d : ℕ} [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (k k0 cbuf : ℕ) (z : SpatialCoordinates d) (s eps order cell budget : ℝ)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hcell : 0 < cell)
    (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hEta : ∀ᵐ xi ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : SpatialCoordinates d),
        eta N xi i y = xi ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (Fsc Psc Rsc Dsc : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
    (Zsc : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (goodEvt : ℕ → ℕ → Vec d → BilateralField d → Prop)
    (hPS : ∀ᵐ xi ∂(chaosSampleLaw M).toMeasure, ∀ N,
      primitive_scores d M s eps (eta N xi) (fun m y => Fsc N m y xi)
        (fun m y => Psc N m y xi) (fun m y => Rsc N m y xi)
        (fun m y => Dsc N m y xi) (fun m y => Zsc N m y xi)
        (fun m y => goodEvt N m y xi))
    (prefixN : ℕ → BilateralField d → ℝ)
    (hPrefix : ∀ N xi, prefixN N xi =
      if (k : ℤ) - 1 + (k0 : ℤ) ≤ (N : ℤ) then
        ∑ j ∈ Finset.Icc ((k : ℤ) - 1 - (cbuf : ℤ)) ((k : ℤ) - 1 + (k0 : ℤ)),
          if 0 ≤ (N : ℤ) - j then
            (Dsc N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • z) xi).toReal else 0
      else 0)
    (hFinite : ∀ᵐ xi ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      (k : ℤ) - 1 + (k0 : ℤ) ≤ (N : ℤ) →
        Dsc N ((N : ℤ) - ((k : ℤ) - 1)).toNat (((3 : ℝ) ^ N) • z) xi ≠ ⊤)
    (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
    (hSN : ∀ N l w xi, sN N l w xi =
      if l ≤ (N : ℤ) then aux_in_deterministic_onestep_sref M H xi N l w else 1)
    {Omega : Type} [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (N : ℕ → ℕ) (hN : StrictMono N) (env : ℕ → Omega → BilateralField d)
    (hEnv : ∀ n, Measurable (env n))
    (hLaw : ∀ n, Measure.map (env n) P = (chaosSampleLaw M).toMeasure)
    (prefixLim lowerLim : Omega → ℝ)
    (hPrefixLim : TendstoInMeasure P (fun n om => prefixN (N n) (env n om)) atTop prefixLim)
    (hLowerLim : TendstoInMeasure P
      (fun n om => I.lam z ((3 : ℝ) ^ (-((k : ℤ) - 1))) (by positivity)
        (cutoffPositiveCoefficient M H (env n om) (N n) z (by positivity))
        z ((3 : ℝ) ^ (-((k : ℤ) - 1))) order 2 /
          sN (N n) ((k : ℤ) - 1) z (env n om)) atTop lowerLim) :
    ∃ seq : ℕ → ℕ, StrictMono seq ∧ ∀ᵐ om ∂P,
      cell ≤ lowerLim om → prefixLim om < budget →
      ∀ᶠ n in atTop,
        (cell / (2 * Real.exp (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P + 2 * budget))) *
          sN (N (seq n)) (k : ℤ) z (env (seq n) om) ≤
        I.lam z ((3 : ℝ) ^ (-((k : ℤ) - 1))) (by positivity)
          (cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n)) z (by positivity))
          z ((3 : ℝ) ^ (-((k : ℤ) - 1))) order 2 := by
  let Good : BilateralField d → Prop := fun xi =>
    (∀ (N i : ℕ) (y : SpatialCoordinates d),
      eta N xi i y = xi ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y)) ∧
    (∀ N, primitive_scores d M s eps (eta N xi) (fun m y => Fsc N m y xi)
      (fun m y => Psc N m y xi) (fun m y => Rsc N m y xi)
      (fun m y => Dsc N m y xi) (fun m y => Zsc N m y xi)
      (fun m y => goodEvt N m y xi)) ∧
    (∀ N : ℕ, (k : ℤ) - 1 + (k0 : ℤ) ≤ (N : ℤ) →
      Dsc N ((N : ℤ) - ((k : ℤ) - 1)).toNat (((3 : ℝ) ^ N) • z) xi ≠ ⊤)
  have hGoodLaw : ∀ᵐ xi ∂(chaosSampleLaw M).toMeasure, Good xi := by
    dsimp only [Good]
    filter_upwards [hEta, hPS, hFinite] with xi hEtaXi hPSXi hFiniteXi
    exact ⟨hEtaXi, hPSXi, hFiniteXi⟩
  have hGoodEnv : ∀ᵐ om ∂P, ∀ n, Good (env n om) := by
    rw [ae_all_iff]
    intro n
    apply ae_of_ae_map (hEnv n).aemeasurable
    rw [hLaw n]
    exact hGoodLaw
  have hTail : ∀ᶠ n : ℕ in atTop, k + k0 ≤ n := by
    exact Filter.eventually_atTop.2 ⟨k + k0, fun n hn => hn⟩
  let A : ℕ → Omega → ℝ := fun n om =>
    I.lam z ((3 : ℝ) ^ (-((k : ℤ) - 1))) (by positivity)
      (cutoffPositiveCoefficient M H (env n om) (N n) z (by positivity))
      z ((3 : ℝ) ^ (-((k : ℤ) - 1))) order 2
  let source : ℕ → Omega → ℝ := fun n om => sN (N n) (k : ℤ) z (env n om)
  let reference : ℕ → Omega → ℝ := fun n om =>
    sN (N n) ((k : ℤ) - 1) z (env n om)
  let prefixSeq : ℕ → Omega → ℝ := fun n om => prefixN (N n) (env n om)
  have hA : TendstoInMeasure P (fun n om => A n om / reference n om) atTop lowerLim := by
    exact hLowerLim
  have hRatio : ∀ᵐ om ∂P, ∀ᶠ n : ℕ in atTop,
      0 < reference n om ∧
        source n om ≤ reference n om *
          Real.exp (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P + 2 * prefixSeq n om) := by
    filter_upwards [hGoodEnv] with om hOm
    filter_upwards [hTail] with n hn
    have hIndex : n ≤ N n := hN.id_le n
    have hSelfNat : k ≤ N n := by omega
    have hSelf : (k : ℤ) ≤ (N n : ℤ) := by omega
    have hPad : (k : ℤ) - 1 ≤ (N n : ℤ) := by omega
    have hGuard : (k : ℤ) - 1 + (k0 : ℤ) ≤ (N n : ℤ) := by omega
    have hRootStrict : (k : ℤ) - 1 < (N n : ℤ) := by omega
    have hData := hOm n
    dsimp only [Good] at hData
    obtain ⟨hEtaData, hPSData, hFiniteData⟩ := hData
    have hPrefixBound :
        (∑ j ∈ Finset.Icc ((k : ℤ) - 1 - (cbuf : ℤ))
            ((k : ℤ) - 1 + (k0 : ℤ)),
          if 0 ≤ (N n : ℤ) - j then
            (Dsc (N n) ((N n : ℤ) - j).toNat (((3 : ℝ) ^ (N n)) • z)
              (env n om)).toReal else 0) ≤ prefixSeq n om := by
      dsimp only [prefixSeq]
      rw [hPrefix (N n) (env n om), if_pos hGuard]
    have hLayer := goodext_prefix_layer_bound M (env n om) (N n) (eta (N n) (env n om))
      (fun i y => hEtaData (N n) i y) s eps hs
      (fun m y => Fsc (N n) m y (env n om))
      (fun m y => Psc (N n) m y (env n om))
      (fun m y => Rsc (N n) m y (env n om))
      (fun m y => Dsc (N n) m y (env n om))
      (fun m y => Zsc (N n) m y (env n om))
      (fun m y => goodEvt (N n) m y (env n om))
      (hPSData (N n)) z ((k : ℤ) - 1) hRootStrict cbuf k0
      (hFiniteData (N n) hGuard) (prefixSeq n om) hPrefixBound
    have hAdjacent := goodext_adjacent_reference M Rm H (env n om) (N n) k hSelfNat z
    have hExp :
        Real.exp (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P +
          |(env n om) (-((k : ℤ) - 1)) z|) ≤
        Real.exp (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P + 2 * prefixSeq n om) := by
      apply Real.exp_le_exp.mpr
      linarith only [hLayer]
    have hPadPositive :=
      aux_in_deterministic_onestep_sref_pos M H (env n om) (N n) ((k : ℤ) - 1) z
    have hReferenceBound :
        aux_in_deterministic_onestep_sref M H (env n om) (N n) (k : ℤ) z ≤
          aux_in_deterministic_onestep_sref M H (env n om) (N n) ((k : ℤ) - 1) z *
            Real.exp (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P + 2 * prefixSeq n om) := by
      calc
        _ ≤ aux_in_deterministic_onestep_sref M H (env n om) (N n) ((k : ℤ) - 1) z *
            Real.exp (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P +
              |(env n om) (-((k : ℤ) - 1)) z|) := hAdjacent
        _ ≤ _ := mul_le_mul_of_nonneg_left hExp hPadPositive.le
    have hSourceEq : source n om =
        aux_in_deterministic_onestep_sref M H (env n om) (N n) (k : ℤ) z := by
      dsimp only [source]
      rw [hSN (N n) (k : ℤ) z (env n om)]
      simp only [if_pos hSelf]
    have hReferenceEq : reference n om =
        aux_in_deterministic_onestep_sref M H (env n om) (N n) ((k : ℤ) - 1) z := by
      dsimp only [reference]
      rw [hSN (N n) ((k : ℤ) - 1) z (env n om)]
      simp only [if_pos hPad]
    rw [hSourceEq, hReferenceEq]
    exact ⟨hPadPositive, hReferenceBound⟩
  exact SubdiffusiveProcess.exists_seq_eventually_lower_coefficient_of_reference_prefix
    P A source reference prefixSeq lowerLim prefixLim hA hPrefixLim
    (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) cell budget hcell hRatio
end Paper
