module

public import SubdiffusiveProcess.Paper.lfgc_good_scale_comparison
public import SubdiffusiveProcess.Paper.in_deterministic_equal_scale_b12
public import SubdiffusiveProcess.Paper.in_deterministic

@[expose] public section

/-! Uniform good-scale transfer constants for nonnegative physical levels and both infrared choices.
The primitive-score and finite-score hypotheses are retained explicitly. -/

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Raw primitive scores supply the nonnegative-level comparison bound. -/
theorem aux_lfgc_good_scale_transfer_scores
    {d : ℕ} [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) (l : ℤ) (hl : l ≤ (N : ℤ)) (hl0 : 0 ≤ l)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)) ∨ H = 0)
    (s eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (w : SpatialCoordinates d) (hr : 0 < (3 : ℝ) ^ (-l))
    (hZ : Zsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w) < 1)
    (hD : Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w) ≠ ⊤) :
    let m : ℕ := ((N : ℤ) - l).toNat
    let kappa : ℕ → ℝ := fun J =>
      Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
    let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
      fun ell v beta =>
        if 0 ≤ ell then
          ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
        else
          -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
    let a0 : ℝ := kappa m / kappa N * Real.exp (H omega w + retained l w omega)
    let e : ℝ := min (Real.log 12 / 4) ((d : ℝ) * (Dsc m (((3 : ℝ) ^ N) • w)).toReal) *
      Real.exp (Real.log 12 / 4)
    I.err w ((3 : ℝ) ^ (-l)) hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr)
        w ((3 : ℝ) ^ (-l)) a0 s 2 ≤
      Real.sqrt (2 + 6 * e ^ 2) *
          section6HomogenizationError M s m m eta (((3 : ℝ) ^ N) • w) +
        Real.sqrt (6 * e ^ 2) := by
  intro m kappa retained a0 e
  have hB : (0 : ℝ) ≤ Real.log 12 / 4 := by
    have : (0 : ℝ) ≤ Real.log 12 := Real.log_nonneg (by norm_num)
    positivity
  exact lfgc_good_scale_comparison I M H omega N l hl hl0 eta hEta hIR w hr
    s hs (Real.log 12 / 4) (Dsc m (((3 : ℝ) ^ N) • w)).toReal hB ENNReal.toReal_nonneg
    (fun x hx K => aux_in_deterministic_good_scale_transfer_P_bound M s eps eta
      Fsc Psc Rsc Dsc Zsc goodEvt hPS m _ hZ hx _ _ (Nat.le_succ m))
    (fun K => aux_in_deterministic_good_scale_transfer_T_bound M s eps eta
      Fsc Psc Rsc Dsc Zsc goodEvt hPS m _ hD _ _ (Nat.le_succ m))

/-- Raw primitive scores supply the nonnegative-level comparison bound. -/
theorem aux_lfgc_good_scale_transfer_child
    {d : ℕ} [NeZero d] (I : _root_.SubdiffusiveProcess.Paper.in_J d) (C : ℝ) (hC : 0 < C)
    (hgmc : ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s eps : ℝ),
      0 < s → s ≤ (1 / 32 : ℝ) → M.delta ≤ Real.sqrt s / 8 → eps < 1 →
      ∀ (g : _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
        (goodEvt : ℕ → Vec d → Prop),
        _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps g Fsc Psc Rsc Dsc Zsc goodEvt →
      ∀ (m : ℕ) (z : Vec d), Zsc m z < 1 → Dsc m z ≠ ⊤ →
        section6HomogenizationError M s m m g z ≤
          C * (2 * (s⁻¹ * M.delta ^ 2) + eps ^ 8 + (Dsc m z).toReal))
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) (l : ℤ) (hl : l ≤ (N : ℤ)) (hl0 : 0 ≤ l)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)) ∨ H = 0)
    (s eps : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsSmall : s ≤ (1 / 32 : ℝ))
    (hdelta : M.delta ≤ Real.sqrt s / 8) (heps : eps ∈ Set.Ioo (0 : ℝ) 1)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop)
    (hPS : _root_.SubdiffusiveProcess.Paper.primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (w : SpatialCoordinates d) (hr : 0 < (3 : ℝ) ^ (-l))
    (hZ : Zsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w) < 1)
    (hD : Dsc ((N : ℤ) - l).toNat (((3 : ℝ) ^ N) • w) ≠ ⊤) :
    let m : ℕ := ((N : ℤ) - l).toNat
    let kappa : ℕ → ℝ := fun J =>
      Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
    let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
      fun ell v beta =>
        if 0 ≤ ell then
          ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
        else
          -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
    let a0 : ℝ := kappa m / kappa N * Real.exp (H omega w + retained l w omega)
    I.err w ((3 : ℝ) ^ (-l)) hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr)
        w ((3 : ℝ) ^ (-l)) a0 s 2 ≤
      (16 * C * s⁻¹ + 8 * C + 9 * (d : ℝ) + 1) *
        (M.delta ^ 2 + eps ^ 8 + (Dsc m (((3 : ℝ) ^ N) • w)).toReal) := by
  intro m kappa retained a0
  have hpt := aux_lfgc_good_scale_transfer_scores I M H omega N l hl hl0
    eta hEta hIR s eps hs Fsc Psc Rsc Dsc Zsc goodEvt hPS w hr hZ hD
  refine hpt.trans ?_
  exact aux_in_deterministic_good_scale_transfer_numeric d C s M.delta eps _ _ hC hs.1
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    (hgmc M s eps hs.1 hsSmall hdelta heps.2 eta Fsc Psc Rsc Dsc Zsc goodEvt hPS m _ hZ hD)

/-- Uniform transfer constants control the actual error at every tested nonnegative level. -/
theorem lfgc_good_scale_transfer (d : ℕ) [NeZero d]
    (I : in_J d) (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hsSmall : s ≤ (1 / 32 : ℝ)) :
    ∃ Cg delta0 : ℝ, 0 < Cg ∧ 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
        (N : ℕ) (j : ℤ), 0 ≤ j → j ≤ (N : ℤ) → M.delta ≤ delta0 →
      ∀ (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d),
        (∀ (i : ℕ) (y : SpatialCoordinates d),
          eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y)) →
        (Tendsto (infraredPartialSum omega) atTop (nhds (H omega)) ∨ H = 0) →
      ∀ (eps : ℝ), eps ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
        (goodEvt : ℕ → Vec d → Prop),
        primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt →
      ∀ (w : SpatialCoordinates d),
        Dsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) ≠ ⊤ →
        Zsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w) < 1 →
        I.err w ((3 : ℝ) ^ (-j)) (by positivity)
          (cutoffPositiveCoefficient M H omega N w (by positivity))
          w ((3 : ℝ) ^ (-j)) (aux_in_deterministic_onestep_sref M H omega N j w) s 2 ≤
            Cg * (M.delta ^ 2 + eps ^ 8 + (Dsc ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • w)).toReal) := by
  obtain ⟨C, hC, hgmc⟩ := aux_in_deterministic_good_scale_transfer_gmc_bound_of_B12
    (in_deterministic_equal_scale_b12 d)
  have hs0 := hs.1
  refine ⟨16 * C * s⁻¹ + 8 * C + 9 * (d : ℝ) + 1, Real.sqrt s / 8,
    by positivity, by positivity, ?_⟩
  intro M H omega N j hj0 hjN hdelta eta hEta hIR eps heps Fsc Psc Rsc Dsc Zsc goodEvt hPS w hD hZ
  exact aux_lfgc_good_scale_transfer_child I C hC hgmc M H omega N j hjN hj0 eta hEta hIR
    s eps hs hsSmall hdelta heps Fsc Psc Rsc Dsc Zsc goodEvt hPS w (by positivity) hZ hD

end SubdiffusiveProcess.Paper
