module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.Sobolev.ResponseSpace
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.lem_finite_source_comparison
public import SubdiffusiveProcess.Paper.sum_errors_baseline_input
public import SubdiffusiveProcess.Paper.lem_finite_stopping
public import SubdiffusiveProcess.Paper.working_levels_ratio
public import SubdiffusiveProcess.Paper.lem_neumann_error
public import SubdiffusiveProcess.Paper.lem_load
public import SubdiffusiveProcess.Paper.neumann_load_pointwise
public import SubdiffusiveProcess.Paper.prop_as_dirichlet
public import SubdiffusiveProcess.Paper.prop_21
public import SubdiffusiveProcess.Paper.lem_coercivity
public import SubdiffusiveProcess.Paper.lem_infrared
public import SubdiffusiveProcess.Paper.lem_local_normalizations
public import SubdiffusiveProcess.Sobolev.CompactResponses
public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import SubdiffusiveProcess.EllipticRegularity.CubeDilation
public import Homogenization.Sobolev.Foundations.CoerciveH1Dilation
public import Homogenization.Sobolev.H1.Translation
public import SubdiffusiveProcess.Paper.aux_lane4_coercivity_dilation_cube_geometry
public import SubdiffusiveProcess.Paper.lane4_gagliardo_dilation_scaling
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_scale_shift
public import SubdiffusiveProcess.Paper.lane4_coercivity_dilation
public import SubdiffusiveProcess.MeyersRegularity.AffineH1
public import SubdiffusiveProcess.Sobolev.LocalEnergy
public import SubdiffusiveProcess.Paper.finite_cutoff_log_abs_majorant
public import SubdiffusiveProcess.Paper.inputs_EM_witness
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import Mathlib.MeasureTheory.Function.L2Space
public import SubdiffusiveProcess.Probability.InfraredCharacterizationCompactExponentialMoment
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

lemma aux_prop_as_response_bank_cauchy_pair_abs
    (x y q e : ℝ) (hq : 0 ≤ q - 1)
    (hxy : x ≤ q * y + e) (hyx : y ≤ q * x + e) :
    |x - y| ≤ (q - 1) * x + e := by
  by_cases h : y ≤ x
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    nlinarith
  · have h' : x ≤ y := le_of_not_ge h
    rw [abs_of_nonpos (sub_nonpos.mpr h')]
    nlinarith

lemma aux_prop_as_response_bank_cauchy_pair_event
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z W : Ω → ℝ) (q e : ℝ) (p : ℝ≥0∞) (Bad₁ Bad₂ : Set Ω)
    (hq : 0 ≤ q - 1)
    (hbad₁ : P Bad₁ ≤ p) (hbad₂ : P Bad₂ ≤ p)
    (hgood : ∀ x : Ω, x ∉ Bad₁ → x ∉ Bad₂ →
      Z x ≤ q * W x + e ∧ W x ≤ q * Z x + e) :
    P {x | (q - 1) * Z x + e < |Z x - W x|} ≤ p + p := by
  have hsub : {x | (q - 1) * Z x + e < |Z x - W x|} ⊆ Bad₁ ∪ Bad₂ := by
    intro x hx
    change (q - 1) * Z x + e < |Z x - W x| at hx
    by_contra hnot
    have h₁ : x ∉ Bad₁ := by
      intro hx₁
      exact hnot (Or.inl hx₁)
    have h₂ : x ∉ Bad₂ := by
      intro hx₂
      exact hnot (Or.inr hx₂)
    have hbound := aux_prop_as_response_bank_cauchy_pair_abs
      (Z x) (W x) q e hq (hgood x h₁ h₂).1 (hgood x h₁ h₂).2
    exact (not_lt_of_ge hbound) hx
  calc
    P {x | (q - 1) * Z x + e < |Z x - W x|} ≤ P (Bad₁ ∪ Bad₂) :=
      measure_mono hsub
    _ ≤ P Bad₁ + P Bad₂ := measure_union_le _ _
    _ ≤ p + p := add_le_add hbad₁ hbad₂

lemma aux_prop_as_response_bank_cauchy_tail_to_cauchy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → ℝ) (Cgeom : ℝ) (hCgeom : 0 < Cgeom)
    (hpair : ∀ eps : ℝ, 0 < eps →
      ∃ Ceps ceps : ℝ, ∃ N0 : ℕ,
        0 < Ceps ∧ 0 < ceps ∧
        ∀ N : ℕ, N0 ≤ N →
          ∃ M0 : ℕ, N ≤ M0 ∧
            ∀ M : ℕ, M0 ≤ M →
              P {omega |
                  |Z N omega - Z M omega| >
                    Cgeom * eps * Z N omega +
                      Ceps * (3 : ℝ) ^ (-(ceps * (N : ℝ)))} ≤
                ENNReal.ofReal (Ceps * (3 : ℝ) ^
                  (-(ceps * (N : ℝ)))))
    (htight : ∀ η : ℝ, 0 < η →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ,
        P {omega | K < Z N omega} ≤ ENNReal.ofReal η) :
    ∀ tolerance probability : ℝ, 0 < tolerance → 0 < probability →
      ∃ J : ℕ, ∀ M M' : ℕ, J ≤ M → J ≤ M' →
        P {omega | tolerance < |Z M omega - Z M' omega|} ≤
          ENNReal.ofReal probability := by
  intro tolerance probability htolerance hprobability
  obtain ⟨K, hK, hKtail⟩ := htight (probability / 4) (by linarith)
  let eps : ℝ := tolerance / (8 * Cgeom * (K + 1))
  have heps : 0 < eps := by
    dsimp [eps]
    positivity
  obtain ⟨Ceps, ceps, N0, hCeps, hceps, hpair'⟩ := hpair eps heps
  have hpow : Tendsto
      (fun N : ℕ => Ceps * (3 : ℝ) ^ (-(ceps * (N : ℝ))))
      atTop (𝓝 0) := by
    have hlin : Tendsto (fun N : ℕ => ceps * (N : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).const_mul_atTop' hceps
    have hbot : Tendsto (fun N : ℕ => -(ceps * (N : ℝ))) atTop atBot :=
      tendsto_neg_atTop_atBot.comp hlin
    have hthree : Tendsto
        (fun N : ℕ => (3 : ℝ) ^ (-(ceps * (N : ℝ))))
        atTop (𝓝 0) :=
      (tendsto_rpow_atBot_of_base_gt_one (3 : ℝ) (by norm_num)).comp hbot
    simpa using hthree.const_mul Ceps
  have hsmall : 0 < min (tolerance / 4) (probability / 8) := by
    exact lt_min (by linarith) (by linarith)
  have hev : ∀ᶠ N : ℕ in atTop,
      Ceps * (3 : ℝ) ^ (-(ceps * (N : ℝ))) <
        min (tolerance / 4) (probability / 8) :=
    hpow.eventually (Iio_mem_nhds hsmall)
  obtain ⟨Npow, hNpow⟩ := eventually_atTop.1 hev
  let Nstar := max N0 Npow
  have hN0star : N0 ≤ Nstar := le_max_left _ _
  have hNpowstar : Npow ≤ Nstar := le_max_right _ _
  obtain ⟨M0, hNM0, hpairstar⟩ := hpair' Nstar hN0star
  let J := max Nstar M0
  refine ⟨J, ?_⟩
  intro M M' hJM hJM'
  have hM0 : M0 ≤ M := le_trans (le_max_right _ _) hJM
  have hM0' : M0 ≤ M' := le_trans (le_max_right _ _) hJM'
  have hbadM := hpairstar M hM0
  have hbadM' := hpairstar M' hM0'
  have hdecay : Ceps * (3 : ℝ) ^ (-(ceps * (Nstar : ℝ))) <
      min (tolerance / 4) (probability / 8) :=
    hNpow Nstar hNpowstar
  have hbadMle : P {omega |
      |Z Nstar omega - Z M omega| >
        Cgeom * eps * Z Nstar omega +
          Ceps * (3 : ℝ) ^ (-(ceps * (Nstar : ℝ)))} ≤
      ENNReal.ofReal (probability / 8) :=
    hbadM.trans (ENNReal.ofReal_le_ofReal
      (lt_of_lt_of_le hdecay (min_le_right _ _)).le)
  have hbadM'le : P {omega |
      |Z Nstar omega - Z M' omega| >
        Cgeom * eps * Z Nstar omega +
          Ceps * (3 : ℝ) ^ (-(ceps * (Nstar : ℝ)))} ≤
      ENNReal.ofReal (probability / 8) :=
    hbadM'.trans (ENNReal.ofReal_le_ofReal
      (lt_of_lt_of_le hdecay (min_le_right _ _)).le)
  let T : Set Ω := {omega | K < Z Nstar omega}
  let E : Set Ω := {omega |
    |Z Nstar omega - Z M omega| >
      Cgeom * eps * Z Nstar omega +
        Ceps * (3 : ℝ) ^ (-(ceps * (Nstar : ℝ)))}
  let E' : Set Ω := {omega |
    |Z Nstar omega - Z M' omega| >
      Cgeom * eps * Z Nstar omega +
        Ceps * (3 : ℝ) ^ (-(ceps * (Nstar : ℝ)))}
  have hsub : {omega | tolerance < |Z M omega - Z M' omega|} ⊆
      T ∪ E ∪ E' := by
    intro omega hω
    change tolerance < |Z M omega - Z M' omega| at hω
    by_contra hnot
    have hT : omega ∉ T := by
      intro hT'
      exact hnot (Or.inl (Or.inl hT'))
    have hE : omega ∉ E := by
      intro hE'
      exact hnot (Or.inl (Or.inr hE'))
    have hE' : omega ∉ E' := by
      intro hE''
      exact hnot (Or.inr hE'')
    have hZN : Z Nstar omega ≤ K := by
      exact le_of_not_gt hT
    have hEN : |Z Nstar omega - Z M omega| ≤
        Cgeom * eps * Z Nstar omega +
          Ceps * (3 : ℝ) ^ (-(ceps * (Nstar : ℝ))) := by
      exact le_of_not_gt hE
    have hEN' : |Z Nstar omega - Z M' omega| ≤
        Cgeom * eps * Z Nstar omega +
          Ceps * (3 : ℝ) ^ (-(ceps * (Nstar : ℝ))) := by
      exact le_of_not_gt hE'
    have hcoeff : 0 ≤ Cgeom * eps := mul_nonneg hCgeom.le heps.le
    have hENK : Cgeom * eps * Z Nstar omega ≤ Cgeom * eps * K :=
      mul_le_mul_of_nonneg_left hZN hcoeff
    have hfrac : K / (K + 1) ≤ (1 : ℝ) := by
      apply (div_le_iff₀ (by linarith)).2
      linarith
    have hmain : 2 * Cgeom * eps * K ≤ tolerance / 4 := by
      calc
        2 * Cgeom * eps * K = tolerance / 4 * (K / (K + 1)) := by
          dsimp [eps]
          field_simp
          ring
        _ ≤ tolerance / 4 := by
          simpa only [mul_one] using
            (mul_le_mul_of_nonneg_left hfrac
              (by positivity : 0 ≤ tolerance / 4))
    have hbound : |Z M omega - Z M' omega| ≤ tolerance := by
      have htriangle : |Z M omega - Z M' omega| ≤
          |Z M omega - Z Nstar omega| + |Z Nstar omega - Z M' omega| := by
        calc
          |Z M omega - Z M' omega| =
              |(Z M omega - Z Nstar omega) +
                (Z Nstar omega - Z M' omega)| := by
                  congr 1 ; ring
          _ ≤ |Z M omega - Z Nstar omega| +
              |Z Nstar omega - Z M' omega| := abs_add_le _ _
      calc
        |Z M omega - Z M' omega| ≤
            |Z M omega - Z Nstar omega| + |Z Nstar omega - Z M' omega| := htriangle
        _ = |Z Nstar omega - Z M omega| + |Z Nstar omega - Z M' omega| := by
          rw [abs_sub_comm]
        _ ≤ 2 * (Cgeom * eps * Z Nstar omega +
            Ceps * (3 : ℝ) ^ (-(ceps * (Nstar : ℝ)))) := by
          nlinarith
        _ ≤ tolerance := by
          have hdecay' : Ceps * (3 : ℝ) ^ (-(ceps * (Nstar : ℝ))) <
              tolerance / 4 := lt_of_lt_of_le hdecay (min_le_left _ _)
          nlinarith
    exact (not_lt_of_ge hbound) hω
  calc
    P {omega | tolerance < |Z M omega - Z M' omega|} ≤
        P (T ∪ E ∪ E') := measure_mono hsub
    _ ≤ P T + P E + P E' := by
      calc
        P (T ∪ E ∪ E') ≤ P (T ∪ E) + P E' := measure_union_le _ _
        _ ≤ (P T + P E) + P E' := by
          exact add_le_add_left (measure_union_le T E) _
    _ ≤ ENNReal.ofReal (probability / 4) +
        ENNReal.ofReal (probability / 8) +
          ENNReal.ofReal (probability / 8) := by
      exact add_le_add (add_le_add (hKtail Nstar) hbadMle) hbadM'le
    _ = ENNReal.ofReal (probability / 2) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal probability := ENNReal.ofReal_le_ofReal (by linarith)

section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

/-- Clause 1 of the bank: each of the four concrete responses is nonnegative for every
coefficient, from the attained variational formulas. -/
lemma aux_prop_as_response_bank_cauchy_response_nonneg
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Q : Set (SpatialCoordinates d)))]
    (SD : ResponseSpace Q)
    (hP0 : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph Q,
      ‖(u : SobolevData Q).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Q) u‖)
    (SN : ResponseSpace Q) (b : weakSobolevGraph Q) (LD : SD.space →L[ℝ] ℝ)
    (LN : SN.space →L[ℝ] ℝ) (p : Fin d → ℝ) (i : Fin 4) (a : PositiveCoefficient Q) :
    0 ≤ (match i.val with
      | 0 => dirichletResponse SD a b
      | 1 => inverseResponse SD a LD
      | 2 => inverseResponse SN a LN
      | _ => affineInverseNeumannResponse hP0 a p) := by
  rcases i with ⟨i, hi⟩
  match i, hi with
  | 0, _ => exact dirichletResponse_nonneg SD a b
  | 1, _ => exact inverseResponse_nonneg SD a LD
  | 2, _ => exact inverseResponse_nonneg SN a LN
  | 3, _ => exact inverseResponse_nonneg _ a _

/-- The random potential entering the cutoff coefficient is a measurable map into the
continuous-function space. -/
lemma aux_prop_as_response_bank_cauchy_measurable_layers
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Hused : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable Hused)
    (N : ℕ) :
    Measurable (fun omega : BilateralField d =>
      Hused omega + ∑ j ∈ Finset.range (N + 1), omega (-(Int.ofNat j))) := by
  apply hH.add
  apply Finset.measurable_sum
  intro j _
  exact measurable_pi_apply _

/-- The concrete cutoff coefficient is the exponential of an explicit compact potential. -/
lemma aux_prop_as_response_bank_cauchy_coeff_eq
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Hused : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N : ℕ) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    cutoffPositiveCoefficient model Hused omega N z hr =
      expPotentialCoefficient
        (@compactPotentialToLp d (centeredCube z r hr) (closedCube z r hr)
          ⟨centeredCube_subset_closedCube z hr⟩
          ((Hused omega + ∑ j ∈ Finset.range (N + 1), omega (-(Int.ofNat j))).restrict
              (closedCube z r hr : Set (SpatialCoordinates d)) +
            ContinuousMap.const _
              (-(Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)) -
                ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P))) := by
  unfold cutoffPositiveCoefficient normalizedContinuousPositiveCoefficient
  congr 2
  ext x
  have hpos := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model N
  simp only [continuousPositiveLog, cutoffCoefficientCM, cutoffCoefficient, cutoffPotential,
    ContinuousMap.coe_mk, ContinuousMap.sub_apply, ContinuousMap.const_apply, Real.log_one,
    sub_zero]
  rw [Real.log_mul (inv_pos.2 hpos).ne' (Real.exp_pos _).ne', Real.log_inv, Real.log_exp]
  change _ = (Hused omega + ∑ j ∈ Finset.range (N + 1), omega (-(Int.ofNat j)))
      (x : SpatialCoordinates d) +
    (-(Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)) -
      ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P)
  rw [ContinuousMap.add_apply, ContinuousMap.coe_sum, Finset.sum_apply]
  ring

/-- Every response that is continuous in the compact potential is measurable in the sample. -/
lemma aux_prop_as_response_bank_cauchy_measurable_response
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Hused : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable Hused)
    (N : ℕ) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (F : PositiveCoefficient (centeredCube z r hr) → ℝ)
    (hF : Continuous (fun g : C(closedCube z r hr, ℝ) =>
      F (expPotentialCoefficient
        (@compactPotentialToLp d (centeredCube z r hr) (closedCube z r hr)
          ⟨centeredCube_subset_closedCube z hr⟩ g)))) :
    Measurable (fun omega => F (cutoffPositiveCoefficient model Hused omega N z hr)) := by
  let c : ℝ := -(Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)) -
    ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P
  have hcont : Continuous (fun G : C(SpatialCoordinates d, ℝ) =>
      F (expPotentialCoefficient
        (@compactPotentialToLp d (centeredCube z r hr) (closedCube z r hr)
          ⟨centeredCube_subset_closedCube z hr⟩
          (G.restrict (closedCube z r hr : Set (SpatialCoordinates d)) +
            ContinuousMap.const _ c)))) :=
    hF.comp ((ContinuousMap.continuous_restrict _).add continuous_const)
  have hm := hcont.measurable.comp
    (aux_prop_as_response_bank_cauchy_measurable_layers Hused hH N)
  convert hm using 2 with omega
  exact congrArg F (aux_prop_as_response_bank_cauchy_coeff_eq model Hused omega N z hr)

end

section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal BigOperators

/-- A single measurable real random variable has vanishing upper tails. -/
lemma aux_prop_as_response_bank_cauchy_single_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : Measurable f) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ K : ℝ in atTop, P {omega | K < f omega} ≤ ENNReal.ofReal η := by
  have hanti : Antitone (fun n : ℕ => {omega | (n : ℝ) < f omega}) := by
    intro m n hmn omega hω
    have hω' : (n : ℝ) < f omega := hω
    exact lt_of_le_of_lt (Nat.cast_le.2 hmn) hω'
  have hmeas : ∀ n : ℕ, NullMeasurableSet {omega | (n : ℝ) < f omega} P :=
    fun n => (measurableSet_lt measurable_const hf).nullMeasurableSet
  have hlim := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top P _⟩
  have hempty : (⋂ n : ℕ, {omega | (n : ℝ) < f omega}) = ∅ := by
    ext omega
    simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_lt]
    obtain ⟨n, hn⟩ := exists_nat_ge (f omega)
    exact ⟨n, hn⟩
  rw [hempty, measure_empty] at hlim
  have hev := hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hη))
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 hev
  filter_upwards [eventually_ge_atTop (n0 : ℝ)] with K hK
  calc P {omega | K < f omega} ≤ P {omega | (n0 : ℝ) < f omega} := by
        apply measure_mono
        intro omega hω
        exact lt_of_le_of_lt hK hω
    _ ≤ ENNReal.ofReal η := (hn0 n0 le_rfl).le

/-- Uniform tightness of a nonnegative measurable sequence from the fixed-`N`
two-cutoff estimate (applied once, at tolerance one). -/
lemma aux_prop_as_response_bank_cauchy_tight_of_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → ℝ) (hmeas : ∀ N, Measurable (Z N))
    (Cgeom : ℝ) (hCgeom : 0 < Cgeom)
    (hpair : ∀ eps : ℝ, 0 < eps →
      ∃ Ceps ceps : ℝ, ∃ N0 : ℕ,
        0 < Ceps ∧ 0 < ceps ∧
        ∀ N : ℕ, N0 ≤ N →
          ∃ M0 : ℕ, N ≤ M0 ∧
            ∀ M : ℕ, M0 ≤ M →
              P {omega |
                  |Z N omega - Z M omega| >
                    Cgeom * eps * Z N omega +
                      Ceps * (3 : ℝ) ^ (-(ceps * (N : ℝ)))} ≤
                ENNReal.ofReal (Ceps * (3 : ℝ) ^
                  (-(ceps * (N : ℝ))))) :
    ∀ η : ℝ, 0 < η →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ,
        P {omega | K < Z N omega} ≤ ENNReal.ofReal η := by
  intro η hη
  obtain ⟨C1, c1, N0, hC1, hc1, hpair1⟩ := hpair 1 one_pos
  have hpow : Tendsto (fun N : ℕ => C1 * (3 : ℝ) ^ (-(c1 * (N : ℝ)))) atTop (𝓝 0) := by
    have hlin : Tendsto (fun N : ℕ => c1 * (N : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).const_mul_atTop' hc1
    have hthree : Tendsto (fun N : ℕ => (3 : ℝ) ^ (-(c1 * (N : ℝ)))) atTop (𝓝 0) :=
      (tendsto_rpow_atBot_of_base_gt_one (3 : ℝ) (by norm_num)).comp
        (tendsto_neg_atTop_atBot.comp hlin)
    simpa using hthree.const_mul C1
  obtain ⟨Npow, hNpow⟩ := eventually_atTop.1
    (hpow.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < η / 2)))
  let Nstar := max N0 Npow
  obtain ⟨M0, hNM0, hpairstar⟩ := hpair1 Nstar (le_max_left _ _)
  have herr : C1 * (3 : ℝ) ^ (-(c1 * (Nstar : ℝ))) < η / 2 := hNpow Nstar (le_max_right _ _)
  have herr0 : 0 ≤ C1 * (3 : ℝ) ^ (-(c1 * (Nstar : ℝ))) := by positivity
  -- tails of the reference variable and of the finitely many early variables
  have hstar := aux_prop_as_response_bank_cauchy_single_tail P (Z Nstar) (hmeas Nstar)
    (η / 2) (by linarith)
  have hearly : ∀ᶠ K : ℝ in atTop, ∀ N ∈ Finset.range M0,
      P {omega | K < Z N omega} ≤ ENNReal.ofReal η :=
    (Finset.eventually_all _).2 fun N _ =>
      aux_prop_as_response_bank_cauchy_single_tail P (Z N) (hmeas N) η hη
  obtain ⟨Kstar, hKstar, hKstar0⟩ := (hstar.and (eventually_ge_atTop 0)).exists
  let Klate : ℝ := (1 + Cgeom) * Kstar + C1 * (3 : ℝ) ^ (-(c1 * (Nstar : ℝ)))
  obtain ⟨K, hKearly, hKlate⟩ :=
    (hearly.and (eventually_ge_atTop (max Klate 0))).exists
  refine ⟨K, le_trans (le_max_right _ _) hKlate, ?_⟩
  intro N
  by_cases hN : N < M0
  · exact hKearly N (Finset.mem_range.2 hN)
  · have hM0N : M0 ≤ N := le_of_not_gt hN
    have hbad := hpairstar N hM0N
    have hsub : {omega | K < Z N omega} ⊆
        {omega | Kstar < Z Nstar omega} ∪
          {omega | |Z Nstar omega - Z N omega| >
            Cgeom * 1 * Z Nstar omega + C1 * (3 : ℝ) ^ (-(c1 * (Nstar : ℝ)))} := by
      intro omega hω
      by_contra hnot
      simp only [mem_union, mem_ofPred_eq, not_or, not_lt, not_lt] at hnot
      obtain ⟨h1, h2⟩ := hnot
      have hω' : K < Z N omega := hω
      have hdiff : Z N omega - Z Nstar omega ≤
          Cgeom * 1 * Z Nstar omega + C1 * (3 : ℝ) ^ (-(c1 * (Nstar : ℝ))) := by
        have := neg_abs_le (Z Nstar omega - Z N omega)
        have h2' : |Z Nstar omega - Z N omega| ≤
            Cgeom * 1 * Z Nstar omega + C1 * (3 : ℝ) ^ (-(c1 * (Nstar : ℝ))) := h2
        linarith
      have hZle : Z N omega ≤ Klate := by
        have hmul : Cgeom * Z Nstar omega ≤ Cgeom * Kstar :=
          mul_le_mul_of_nonneg_left h1 hCgeom.le
        simp only [Klate]
        nlinarith
      linarith [le_trans (le_max_left Klate 0) hKlate]
    calc P {omega | K < Z N omega} ≤
          P {omega | Kstar < Z Nstar omega} +
            P {omega | |Z Nstar omega - Z N omega| >
              Cgeom * 1 * Z Nstar omega + C1 * (3 : ℝ) ^ (-(c1 * (Nstar : ℝ)))} :=
          (measure_mono hsub).trans (measure_union_le _ _)
      _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) :=
          add_le_add hKstar (hbad.trans (ENNReal.ofReal_le_ofReal herr.le))
      _ = ENNReal.ofReal η := by
          rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
          congr 1
          ring

/-- At a fixed `N`, the finitely many fixed-`k` normalization limits make the two-cutoff
ratio close to the fixed-`N` ratio, for every sufficiently large `M`. -/
lemma aux_prop_as_response_bank_cauchy_good_ratio
    (kap e : ℕ → ℝ) (he : ∀ k, 0 < e k)
    (hconv : ∀ k, Tendsto (fun M : ℕ => kap (M - k) / kap M) atTop (𝓝 (e k)))
    (N : ℕ) (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ M1 : ℕ, N ≤ M1 ∧ ∀ M : ℕ, M1 ≤ M → ∀ k : ℕ, k ≤ N →
      |(kap (N - k) / kap N) / e k - 1| ≤ eps →
      (kap (N - k) / kap N) / (kap (M - k) / kap M) ≤ (1 + eps) / (1 - eps) ∧
      (kap (M - k) / kap M) / (kap (N - k) / kap N) ≤ (1 + eps) / (1 - eps) := by
  have hone : ∀ k, Tendsto (fun M : ℕ => (kap (M - k) / kap M) / e k) atTop (𝓝 1) := by
    intro k
    have h := (hconv k).div_const (e k)
    rwa [div_self (he k).ne'] at h
  have hev : ∀ᶠ M : ℕ in atTop, ∀ k ∈ Finset.range (N + 1),
      |(kap (M - k) / kap M) / e k - 1| ≤ eps := by
    refine (Finset.eventually_all _).2 fun k _ => ?_
    have h := (hone k).eventually (Metric.closedBall_mem_nhds (1 : ℝ) heps)
    filter_upwards [h] with M hM
    simpa [Metric.mem_closedBall, Real.dist_eq] using hM
  obtain ⟨M2, hM2⟩ := eventually_atTop.1 hev
  refine ⟨max N M2, le_max_left _ _, ?_⟩
  intro M hM k hk hNk
  have hMk := hM2 M (le_trans (le_max_right _ _) hM) k (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
  set x := (kap (N - k) / kap N) / e k with hx
  set y := (kap (M - k) / kap M) / e k with hy
  have hxN : kap (N - k) / kap N = x * e k := by
    rw [hx, div_mul_cancel₀ _ (he k).ne']
  have hyM : kap (M - k) / kap M = y * e k := by
    rw [hy, div_mul_cancel₀ _ (he k).ne']
  have hxlo : 1 - eps ≤ x := by linarith [(abs_le.1 hNk).1]
  have hxhi : x ≤ 1 + eps := by linarith [(abs_le.1 hNk).2]
  have hylo : 1 - eps ≤ y := by linarith [(abs_le.1 hMk).1]
  have hyhi : y ≤ 1 + eps := by linarith [(abs_le.1 hMk).2]
  have hpos : 0 < 1 - eps := by linarith
  have hxpos : 0 < x := lt_of_lt_of_le hpos hxlo
  have hypos : 0 < y := lt_of_lt_of_le hpos hylo
  have hek := he k
  rw [hxN, hyM, mul_div_mul_right _ _ hek.ne', mul_div_mul_right _ _ hek.ne']
  constructor
  · rw [div_le_div_iff₀ hypos hpos]
    nlinarith
  · rw [div_le_div_iff₀ hxpos hpos]
    nlinarith

end

section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

/-- The good-level density of the normalization ratios, obtained from
`working_levels_ratio` with the concrete Dirichlet response of one fixed nonconstant affine
datum on the given cube: its convergence and positivity come from `prop_as_dirichlet` and
`lem_local_normalizations`, and its finite comparisons from the first assertion of
`lem_finite_source_comparison` (passed here as `hpart1`, verbatim). -/
lemma aux_prop_as_response_bank_cauchy_density
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1 / 3)
    (H1 : ℕ) (hH1 : 0 < H1) (Dgeom Cgeom delta0 : ℝ) (hCgeom : 0 < Cgeom)
    (hpart1 :
      let L : ℝ := (3 : ℝ) ^ H1
       ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
         (_Rm : in_responses d model) (Sreg : in_6_16 d model)
         (_It : in_iteration d model Jc Sreg)
         (H : BilateralField d → C(SpatialCoordinates d, ℝ))
         (_hH : InfraredCharacterization model H) (_hsmall : model.delta ≤ delta0)
         (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
         (_htriadic : ∃ j : ℤ, r = (3 : ℝ) ^ j),
       let Q := centeredCube z r hr
       let closedQ := closedCube z r hr
       ∀ (eta : ℝ), 0 < eta →
       ∃ (Ceta gamma : ℝ) (N0 : ℕ), 0 < Ceta ∧ 0 < gamma ∧
       ∀ (N M : ℕ), N0 ≤ N → N ≤ M →
       ∀ (c : ℝ), 0 < c → c ≤ 2 →
       ∀ (S : ℕ → Prop),
         theta * (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) ≤
           (Nat.card {n : ℕ // S n ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) →
       let kappa := fun J : ℕ =>
         Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
           SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
       ((∀ n : ℕ, S n → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N →
           (kappa (N - H1 * n) / kappa N) / (kappa (M - H1 * n) / kappa M) ≤ c) →
         ∀ hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
           ‖(u : SobolevData Q).1‖ ≤ K * ‖@subspaceGradient d Q (killedSobolevGraph Q) u‖,
         ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ phi →
         ∀ b : weakSobolevGraph Q,
           ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ)
             =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] phi →
         ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
           (chaosSampleLaw model).toMeasure Bad ≤
             ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) ∧
           ∀ omega ∉ Bad,
           let aN := cutoffPositiveCoefficient model H omega N z hr
           let aM := cutoffPositiveCoefficient model H omega M z hr
           @dirichletResponse d Q (@killedResponseSpace d Q hP) aN b ≤
             c * (1 + Cgeom * eta * L ^ Dgeom) *
               @dirichletResponse d Q (@killedResponseSpace d Q hP) aM b +
             Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) * (c2Norm closedQ phi) ^ 2) ∧
       ((∀ n : ℕ, S n → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N →
           (kappa (M - H1 * n) / kappa M) / (kappa (N - H1 * n) / kappa N) ≤ c) →
         ∀ hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
           ‖(u : SobolevData Q).1‖ ≤ K * ‖@subspaceGradient d Q (killedSobolevGraph Q) u‖,
         ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ phi →
         ∀ b : weakSobolevGraph Q,
           ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ)
             =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] phi →
         ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
           (chaosSampleLaw model).toMeasure Bad ≤
             ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) ∧
           ∀ omega ∉ Bad,
           let aN := cutoffPositiveCoefficient model H omega N z hr
           let aM := cutoffPositiveCoefficient model H omega M z hr
           @dirichletResponse d Q (@killedResponseSpace d Q hP) aM b ≤
             c * (1 + Cgeom * eta * L ^ Dgeom) *
               @dirichletResponse d Q (@killedResponseSpace d Q hP) aN b +
             Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) * (c2Norm closedQ phi) ^ 2)) :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : in_responses d model) (Sreg : in_6_16 d model) (It : in_iteration d model Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_HI : InfraredCharacterization model H),
        model.delta ≤ min 1 delta1 → model.delta ≤ delta0 →
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
          (∃ j : ℤ, r = (3 : ℝ) ^ j) →
          (∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
            ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
              K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖) →
        ∃ e : ℕ → ℝ,
          (∀ k : ℕ, 0 < e k ∧
            Tendsto (fun M : ℕ =>
              (Real.exp ((((M - k : ℕ) : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom model (M - k)) /
                (Real.exp (((M : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom model M)) atTop (𝓝 (e k))) ∧
          ∀ eps : ℝ, 0 < eps →
            ∃ Ne : ℕ, ∀ N : ℕ, Ne ≤ N →
              (1 - 2 * theta) *
                  (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ)
                < (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N ∧
                    |((Real.exp ((((N - H1 * n : ℕ) : ℝ) + 1) *
                          _root_.SubdiffusiveProcess.Model.tauSq model.P) *
                        SubdiffusiveProcess.CoarseGrainingVocab.ahom model (N - H1 * n)) /
                      (Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
                        SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)) / e (H1 * n) - 1| ≤ eps} :
                  ℝ) := by
  obtain ⟨dl, hdl, hLN⟩ :=
    lem_local_normalizations d hd Jc Pc Xc Sf W Cp D hES Step Interp (fun z r hr F => inputs_EM_witness d z r hr F) (3 / 4) (by norm_num) (by norm_num)
  obtain ⟨da, Cga, hda, hCga, hAD⟩ :=
    prop_as_dirichlet d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp (3 / 4) (by norm_num) (by norm_num)
  refine ⟨min dl da, lt_min hdl hda, ?_⟩
  intro model Rm Sreg It H HI hsmall hsmall0 z r hr htri hP
  have hsl : model.delta ≤ min 1 dl :=
    le_trans hsmall (min_le_min_left _ (min_le_left _ _))
  have hsa : model.delta ≤ min 1 da :=
    le_trans hsmall (min_le_min_left _ (min_le_right _ _))
  obtain ⟨e, RL, he, hRLconv, -, hRLpos, -, -, -⟩ := hLN model Rm Sreg It H HI hsl
  refine ⟨e, he, ?_⟩
  let kap : ℕ → ℝ := fun J =>
    Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
      SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
  have hkap : ∀ n : ℕ, 0 < kap n := fun n =>
    mul_pos (Real.exp_pos _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model n)
  -- the fixed nonconstant affine datum
  let p1 : Fin d → ℝ := fun _ => 1
  have hp1 : p1 ≠ 0 := by
    intro h
    have h0 := congrFun h ⟨0, by omega⟩
    simp [p1] at h0
  let phiA : SpatialCoordinates d → ℝ := fun x => ∑ i : Fin d, p1 i * x i
  have hphiA_eq : phiA = fun x => affineSlope p1 x := by
    funext x
    rw [affineSlope_apply]
  have hphiA : ContDiff ℝ ∞ phiA := by
    rw [hphiA_eq]
    exact (affineSlope p1).contDiff
  let bA : weakSobolevGraph (centeredCube z r hr) :=
    affineSobolev (centeredCube_isBounded z hr) p1 0
  have hbA : ((bA : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phiA := by
    filter_upwards [affineL2_coeFn (centeredCube_isBounded z hr) p1 0] with x hx
    change (affineL2 (centeredCube_isBounded z hr) p1 0 : SpatialCoordinates d → ℝ) x = _
    rw [hx, add_zero, hphiA_eq]
  obtain ⟨RLa, hRLa, -, LamE, hLamE_meas, hLamE_eq0, hLamE_conv0, -, -, -⟩ :=
    hAD model Rm Sreg It H HI hsa Unit (fun _ => z) (fun _ => r) (fun _ => hr) (fun _ => htri)
      (fun _ => phiA) (fun _ => hphiA)
  let hPcanon := aux_prop_as_dirichlet_cube_poincare_witness hd z r hr
  let bCanon : weakSobolevGraph (centeredCube z r hr) :=
    Classical.choose (aux_prop_as_dirichlet_smooth_weak_witness z r hr phiA hphiA)
  have hbCanon : ((bCanon : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phiA :=
    Classical.choose_spec (aux_prop_as_dirichlet_smooth_weak_witness z r hr phiA hphiA)
  have hLamEq : ∀ N omega,
      dirichletResponse (killedResponseSpace hPcanon)
        (cutoffPositiveCoefficient model H omega N z hr) bCanon =
      dirichletResponse (killedResponseSpace hP)
        (cutoffPositiveCoefficient model H omega N z hr) bA := by
    intro N omega
    exact (aux_prop_as_dirichlet_bridge hd z r hr hPcanon
      (cutoffPositiveCoefficient model H omega N z hr) bCanon phiA hphiA hbCanon).trans
      (aux_prop_as_dirichlet_bridge hd z r hr hP
        (cutoffPositiveCoefficient model H omega N z hr) bA phiA hphiA hbA).symm
  have hLamE_conv : ∀ u : Unit,
      TendstoInMeasure (chaosSampleLaw model).toMeasure
        (fun N omega => dirichletResponse (killedResponseSpace hP)
          (cutoffPositiveCoefficient model H omega N z hr) bA) atTop (LamE u) := by
    intro u
    have hconv := hLamE_conv0 u
    change TendstoInMeasure (chaosSampleLaw model).toMeasure
      (fun N omega => dirichletResponse (killedResponseSpace hPcanon)
        (cutoffPositiveCoefficient model H omega N z hr) bCanon) atTop (LamE u) at hconv
    simpa only [hLamEq] using hconv
  -- In-measure limits of the same boundary minima agree almost everywhere.
  have hclsA : IsCellBoundaryClass (3 / 4) z r phiA :=
    aux_prop_as_dirichlet_smooth_class (3 / 4) (by norm_num) z r phiA hphiA
  have hLamE_eq : ∀ u : Unit, LamE u =ᵐ[(chaosSampleLaw model).toMeasure]
      (fun omega => (RL z r hr omega phiA) ^ 2) := fun u =>
    (hLamE_eq0 u).trans
      (tendstoInMeasure_ae_unique (hRLa u phiA hclsA) (hRLconv z r hr phiA htri hclsA))
  let Lam : ℕ → BilateralField d → ℝ := fun N omega =>
    dirichletResponse (killedResponseSpace hP)
      (cutoffPositiveCoefficient model H omega N z hr) bA
  have hLam_meas : ∀ N : ℕ, Measurable (Lam N) := by
    intro N
    have : Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closedCube z r hr) :=
      ⟨centeredCube_subset_closedCube z hr⟩
    exact aux_prop_as_response_bank_cauchy_measurable_response model H HI.1 N z hr
      (fun a => dirichletResponse (killedResponseSpace hP) a bA)
      (continuous_dirichletResponse_compact (killedResponseSpace hP) (closedCube z r hr) bA)
  have hLamE_pos : ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, 0 < LamE () omega := by
    filter_upwards [hLamE_eq (), hRLpos z r hr p1 htri hp1] with omega h1 h2
    rw [h1]
    exact h2
  obtain ⟨B0, hB0⟩ : ∃ B0 : ℝ, B0 = c2Norm (closedCube z r hr) phiA := ⟨_, rfl⟩
  clear hLN hAD
  have hfinite : ∀ eta : ℝ, 0 < eta →
      ∃ (Ceta gamma : ℝ) (N0 : ℕ), 0 < Ceta ∧ 0 < gamma ∧
      ∀ (N M : ℕ), N0 ≤ N → N ≤ M →
      ∀ (c : ℝ), 0 < c → c ≤ 2 →
      ∀ (S : Finset ℕ),
        theta * (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ)
          ≤ (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N ∧ n ∈ S} : ℝ) →
        ((∀ n : ℕ, n ∈ S → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N →
            (kap (N - H1 * n) / kap N) / (kap (M - H1 * n) / kap M) ≤ c) →
          (chaosSampleLaw model).toMeasure
            {omega | c * (1 + (Cgeom * ((3 : ℝ) ^ H1) ^ Dgeom) * eta) * Lam M omega +
              Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) < Lam N omega}
            ≤ ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)))) ∧
        ((∀ n : ℕ, n ∈ S → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N →
            (kap (M - H1 * n) / kap M) / (kap (N - H1 * n) / kap N) ≤ c) →
          (chaosSampleLaw model).toMeasure
            {omega | c * (1 + (Cgeom * ((3 : ℝ) ^ H1) ^ Dgeom) * eta) * Lam N omega +
              Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) < Lam M omega}
            ≤ ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)))) := by
    intro eta heta
    obtain ⟨Ceta, gamma, N0, hCeta, hgamma, hbody⟩ :=
      hpart1 model Rm Sreg It H HI hsmall0 z r hr htri eta heta
    refine ⟨Ceta * (1 + B0 ^ 2), gamma, N0, by positivity, hgamma, ?_⟩
    intro N M hN hNM c hc hc2 S hS
    have hcard : (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N ∧ n ∈ S} : ℝ) =
        (Nat.card {n : ℕ // n ∈ S ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) := by
      congr 1
      exact Nat.card_congr (Equiv.subtypeEquivRight fun n => by tauto)
    obtain ⟨hup, hdown⟩ := hbody N M hN hNM c hc hc2 (fun n => n ∈ S) (hcard ▸ hS)
    have hpow_nonneg : 0 ≤ Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) := by positivity
    have hle_err : Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) * B0 ^ 2 ≤
        Ceta * (1 + B0 ^ 2) * (3 : ℝ) ^ (-gamma * (N : ℝ)) := by
      nlinarith [sq_nonneg B0]
    have hle_prob : Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) ≤
        Ceta * (1 + B0 ^ 2) * (3 : ℝ) ^ (-gamma * (N : ℝ)) := by
      nlinarith [sq_nonneg B0]
    constructor
    · intro hratio
      obtain ⟨Bad, -, hBadle, hBad⟩ := hup hratio hP phiA hphiA bA hbA
      calc (chaosSampleLaw model).toMeasure
            {omega | c * (1 + (Cgeom * ((3 : ℝ) ^ H1) ^ Dgeom) * eta) * Lam M omega +
              Ceta * (1 + B0 ^ 2) * (3 : ℝ) ^ (-gamma * (N : ℝ)) < Lam N omega}
            ≤ (chaosSampleLaw model).toMeasure Bad := by
              apply measure_mono
              intro omega homega
              by_contra hnot
              have h : Lam N omega ≤ c * (1 + Cgeom * eta * ((3 : ℝ) ^ H1) ^ Dgeom) *
                  Lam M omega + Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) * B0 ^ 2 := by
                rw [hB0]
                exact hBad omega hnot
              have homega' : c * (1 + (Cgeom * ((3 : ℝ) ^ H1) ^ Dgeom) * eta) * Lam M omega +
                  Ceta * (1 + B0 ^ 2) * (3 : ℝ) ^ (-gamma * (N : ℝ)) < Lam N omega := homega
              have hfac : c * (1 + (Cgeom * ((3 : ℝ) ^ H1) ^ Dgeom) * eta) =
                  c * (1 + Cgeom * eta * ((3 : ℝ) ^ H1) ^ Dgeom) := by ring
              rw [hfac] at homega'
              linarith
        _ ≤ ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) := hBadle
        _ ≤ ENNReal.ofReal (Ceta * (1 + B0 ^ 2) * (3 : ℝ) ^ (-gamma * (N : ℝ))) :=
              ENNReal.ofReal_le_ofReal hle_prob
    · intro hratio
      obtain ⟨Bad, -, hBadle, hBad⟩ := hdown hratio hP phiA hphiA bA hbA
      calc (chaosSampleLaw model).toMeasure
            {omega | c * (1 + (Cgeom * ((3 : ℝ) ^ H1) ^ Dgeom) * eta) * Lam N omega +
              Ceta * (1 + B0 ^ 2) * (3 : ℝ) ^ (-gamma * (N : ℝ)) < Lam M omega}
            ≤ (chaosSampleLaw model).toMeasure Bad := by
              apply measure_mono
              intro omega homega
              by_contra hnot
              have h : Lam M omega ≤ c * (1 + Cgeom * eta * ((3 : ℝ) ^ H1) ^ Dgeom) *
                  Lam N omega + Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) * B0 ^ 2 := by
                rw [hB0]
                exact hBad omega hnot
              have homega' : c * (1 + (Cgeom * ((3 : ℝ) ^ H1) ^ Dgeom) * eta) * Lam N omega +
                  Ceta * (1 + B0 ^ 2) * (3 : ℝ) ^ (-gamma * (N : ℝ)) < Lam M omega := homega
              have hfac : c * (1 + (Cgeom * ((3 : ℝ) ^ H1) ^ Dgeom) * eta) =
                  c * (1 + Cgeom * eta * ((3 : ℝ) ^ H1) ^ Dgeom) := by ring
              rw [hfac] at homega'
              linarith
        _ ≤ ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) := hBadle
        _ ≤ ENNReal.ofReal (Ceta * (1 + B0 ^ 2) * (3 : ℝ) ^ (-gamma * (N : ℝ))) :=
              ENNReal.ofReal_le_ofReal hle_prob
  exact working_levels_ratio (BilateralField d) (chaosSampleLaw model).toMeasure kap e hkap
    (fun k => (he k).1) (fun k => (he k).2) theta htheta0 htheta1 H1 hH1
    (Cgeom * ((3 : ℝ) ^ H1) ^ Dgeom) (by positivity) Lam (LamE ()) hLam_meas
    (hLamE_meas ()) hLamE_pos (hLamE_conv ()) hfinite

end

section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

/-- The scalar core of the `a⁻¹ v_N` insertion into the inverse variational formula. -/
lemma aux_prop_as_response_bank_cauchy_var_core
    (ZT ZS Lw Ew f δ e0 : ℝ) (hf : 1 ≤ f)
    (hZT : 2 * ((1 / f) * Lw) - (1 / f) * ((1 / f) * Ew) ≤ ZT)
    (hL : ZS - δ ≤ Lw) (hE : Ew ≤ f * ZS + e0) (he0 : 0 ≤ e0) :
    ZS ≤ f * ZT + (2 * δ + e0) := by
  have hf0 : 0 < f := lt_of_lt_of_le one_pos hf
  have h1 : 2 * Lw - Ew / f ≤ f * ZT := by
    have h := mul_le_mul_of_nonneg_left hZT hf0.le
    have hexp : f * (2 * ((1 / f) * Lw) - (1 / f) * ((1 / f) * Ew)) = 2 * Lw - Ew / f := by
      field_simp
    linarith
  have h2 : Ew / f ≤ ZS + e0 := by
    rw [div_le_iff₀ hf0]
    have : e0 ≤ e0 * f := le_mul_of_one_le_right he0 hf
    nlinarith
  linarith

/-- A measurable representative of a bounded source, bounded everywhere. -/
lemma aux_prop_as_response_bank_cauchy_source_rep
    {d : ℕ} {Q : Opens (SpatialCoordinates d)} (f : DomainL2 Q) (K : ℝ) (hK : 0 ≤ K)
    (hf : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      |(f : SpatialCoordinates d → ℝ) x| ≤ K) :
    ∃ F : SpatialCoordinates d → ℝ, Measurable F ∧ (∀ x, |F x| ≤ K) ∧
      F =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] (f : SpatialCoordinates d → ℝ) := by
  classical
  let g := (Lp.aestronglyMeasurable f).mk (f : SpatialCoordinates d → ℝ)
  have hg : Measurable g := (Lp.aestronglyMeasurable f).stronglyMeasurable_mk.measurable
  have hgf : (f : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] g :=
    (Lp.aestronglyMeasurable f).ae_eq_mk
  refine ⟨fun x => if |g x| ≤ K then g x else 0, ?_, ?_, ?_⟩
  · exact Measurable.ite (measurableSet_le (continuous_abs.measurable.comp hg) measurable_const)
      hg measurable_const
  · intro x
    by_cases hx : |g x| ≤ K
    · simp only [hx, ite_true]
    · simp only [hx, ite_false, abs_zero]
      exact hK
  · filter_upwards [hgf, hf] with x hx1 hx2
    have hb : |g x| ≤ K := hx1 ▸ hx2
    simp only [hb, ite_true, hx1]

/-- Zero-source Dirichlet transfer: the trial function of the sourced comparison is an
admissible competitor in the target boundary variational problem. -/
lemma aux_prop_as_response_bank_cauchy_dirichlet_transfer
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (aT aS : PositiveCoefficient (centeredCube z r hr)) (err factor : ℝ)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (b : weakSobolevGraph (centeredCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (hD : ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
           0 ≤ Kf → Measurable F → (∀ x ∈ centeredCube z r hr, |F x| ≤ Kf) →
             ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ 2 phi →
           ∀ b u : weakSobolevGraph (centeredCube z r hr),
             ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
               =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
             SolvesDirichlet aS F b u →
             ∃ (v : weakSobolevGraph (centeredCube z r hr)) (U V : SpatialCoordinates d → ℝ),
               (v : SobolevData (centeredCube z r hr)) - (b : SobolevData (centeredCube z r hr)) ∈
                 killedSobolevGraph (centeredCube z r hr) ∧
               ContinuousOn U (closedCube z r hr) ∧ ContinuousOn V (closedCube z r hr) ∧
               ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                 =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
               ((v : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                 =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] V ∧
               (∀ x ∈ closedCube z r hr,
                 |V x - U x| ≤ err * (Kf + c2Norm (closedCube z r hr) phi)) ∧
               sobolevCoefficientForm aT (v : SobolevData (centeredCube z r hr))
                   (v : SobolevData (centeredCube z r hr)) ≤
                 factor * sobolevCoefficientForm aS (u : SobolevData (centeredCube z r hr))
                   (u : SobolevData (centeredCube z r hr)) +
                 err * (Kf + c2Norm (closedCube z r hr) phi) ^ 2) :
    dirichletResponse (killedResponseSpace hP) aT b ≤
      factor * dirichletResponse (killedResponseSpace hP) aS b +
        err * (0 + c2Norm (closedCube z r hr) phi) ^ 2 := by
  let S := killedResponseSpace hP
  let u := dirichletMinimizer S aS b
  have hsolve : SolvesDirichlet aS (fun _ => 0) b u := by
    refine ⟨dirichletMinimizer_mem_affine S aS b, ?_⟩
    intro ψ
    rw [dirichletMinimizer_euler S aS b ψ]
    simp
  obtain ⟨v, U, V, hvb, -, -, -, -, -, hen⟩ :=
    hD (fun _ => 0) 0 le_rfl measurable_const (by intro x _; simp) phi
      (hphi.of_le (WithTop.coe_le_coe.2 le_top)) b u hb hsolve
  let w : S.space :=
    ⟨(v : SobolevData (centeredCube z r hr)) - (b : SobolevData (centeredCube z r hr)), hvb⟩
  have hleast : dirichletResponse S aT b ≤ sobolevCoefficientForm aT
      ((b : SobolevData (centeredCube z r hr)) + (w : SobolevData (centeredCube z r hr)))
      ((b : SobolevData (centeredCube z r hr)) + (w : SobolevData (centeredCube z r hr))) :=
    (dirichletResponse_isLeast S aT b).2 (Set.mem_range_self w)
  have hbw : (b : SobolevData (centeredCube z r hr)) + (w : SobolevData (centeredCube z r hr)) =
      (v : SobolevData (centeredCube z r hr)) := add_sub_cancel _ _
  rw [hbw] at hleast
  exact hleast.trans hen

/-- The load difference of two data with continuous representatives, bounded by the
sup distance on the closed cube. -/
lemma aux_prop_as_response_bank_cauchy_load_diff
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (f : DomainL2 (centeredCube z r hr)) (F : SpatialCoordinates d → ℝ) (K : ℝ)
    (hFb : ∀ x, |F x| ≤ K)
    (hFeq : F =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      (f : SpatialCoordinates d → ℝ))
    (x1 x2 : SobolevData (centeredCube z r hr)) (U V : SpatialCoordinates d → ℝ) (D : ℝ)
    (hU : (x2.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U)
    (hV : (x1.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] V)
    (hdist : ∀ x ∈ closedCube z r hr, |V x - U x| ≤ D) :
    |sobolevVolumeLoad f x1 - sobolevVolumeLoad f x2| ≤
      K * D * volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  rw [← map_sub, sobolevVolumeLoad_apply]
  have hcongr : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      f x * (x1 - x2).1 x) =
      ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), F x * (V x - U x) := by
    apply integral_congr_ae
    filter_upwards [hFeq, hU, hV, Lp.coeFn_sub x1.1 x2.1] with x h1 h2 h3 h4
    change f x * ((x1.1 - x2.1 : DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ) x = _
    rw [h4, Pi.sub_apply, h2, h3, h1]
  rw [hcongr]
  have hbound : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      ‖F x * (V x - U x)‖ ≤ K * D := by
    filter_upwards [ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hFb x) (hdist x (centeredCube_subset_closedCube z hr hx))
      (abs_nonneg _) ((abs_nonneg _).trans (hFb x))
  have h := norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs] at h
  simpa [Measure.real, Measure.restrict_apply_univ] using h

/-- Killed volume-source transfer : insert `a⁻¹ v` into the inverse
variational formula at the target coefficient. -/
lemma aux_prop_as_response_bank_cauchy_killed_source_transfer
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (aT aS : PositiveCoefficient (centeredCube z r hr)) (err factor : ℝ)
    (herr : 0 ≤ err) (hfactor : 1 ≤ factor)
    (fD : DomainL2 (centeredCube z r hr)) (KD : ℝ) (hKD : 0 ≤ KD)
    (hfD : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      |(fD : SpatialCoordinates d → ℝ) x| ≤ KD)
    (hD : ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
           0 ≤ Kf → Measurable F → (∀ x ∈ centeredCube z r hr, |F x| ≤ Kf) →
             ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ 2 phi →
           ∀ b u : weakSobolevGraph (centeredCube z r hr),
             ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
               =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
             SolvesDirichlet aS F b u →
             ∃ (v : weakSobolevGraph (centeredCube z r hr)) (U V : SpatialCoordinates d → ℝ),
               (v : SobolevData (centeredCube z r hr)) - (b : SobolevData (centeredCube z r hr)) ∈
                 killedSobolevGraph (centeredCube z r hr) ∧
               ContinuousOn U (closedCube z r hr) ∧ ContinuousOn V (closedCube z r hr) ∧
               ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                 =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
               ((v : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                 =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] V ∧
               (∀ x ∈ closedCube z r hr,
                 |V x - U x| ≤ err * (Kf + c2Norm (closedCube z r hr) phi)) ∧
               sobolevCoefficientForm aT (v : SobolevData (centeredCube z r hr))
                   (v : SobolevData (centeredCube z r hr)) ≤
                 factor * sobolevCoefficientForm aS (u : SobolevData (centeredCube z r hr))
                   (u : SobolevData (centeredCube z r hr)) +
                 err * (Kf + c2Norm (closedCube z r hr) phi) ^ 2) :
    inverseResponse (killedResponseSpace hP) aS
        ((sobolevVolumeLoad fD).comp (killedResponseSpace hP).space.subtypeL) ≤
      factor * inverseResponse (killedResponseSpace hP) aT
          ((sobolevVolumeLoad fD).comp (killedResponseSpace hP).space.subtypeL) +
        (2 * (KD * (err * (KD + c2Norm (closedCube z r hr : Set (SpatialCoordinates d))
            (0 : SpatialCoordinates d → ℝ))) *
            volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) +
          err * (KD + c2Norm (closedCube z r hr : Set (SpatialCoordinates d))
            (0 : SpatialCoordinates d → ℝ)) ^ 2) := by
  let S := killedResponseSpace hP
  let L : S.space →L[ℝ] ℝ := (sobolevVolumeLoad fD).comp S.space.subtypeL
  obtain ⟨F, hFm, hFb, hFeq⟩ := aux_prop_as_response_bank_cauchy_source_rep fD KD hKD hfD
  let us : S.space := responseSolution S aS L
  let u : weakSobolevGraph (centeredCube z r hr) :=
    ⟨(us : SobolevData (centeredCube z r hr)), S.le_weak us.2⟩
  have hb0 : ((0 : weakSobolevGraph (centeredCube z r hr)) : SobolevData (centeredCube z r hr)).1
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        (0 : SpatialCoordinates d → ℝ) := by
    change ((0 : DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ) =ᵐ[_] _
    exact Lp.coeFn_zero _ _ _
  have hsolve : SolvesDirichlet aS F 0 u := by
    refine ⟨?_, ?_⟩
    · change (us : SobolevData (centeredCube z r hr)) - 0 ∈ killedSobolevGraph _
      rw [sub_zero]
      exact us.2
    · intro ψ
      have h : sobolevCoefficientForm aS (us : SobolevData (centeredCube z r hr))
          (ψ : SobolevData (centeredCube z r hr)) =
          sobolevVolumeLoad fD (ψ : SobolevData (centeredCube z r hr)) :=
        responseSolution_spec S aS L ψ
      change sobolevCoefficientForm aS (us : SobolevData (centeredCube z r hr))
        (ψ : SobolevData (centeredCube z r hr)) = _
      rw [h, sobolevVolumeLoad_apply]
      apply integral_congr_ae
      filter_upwards [hFeq] with x hx
      rw [hx]
  obtain ⟨v, U, V, hv0, -, -, hU, hV, hdist, hen⟩ :=
    hD F KD hKD hFm (fun x _ => hFb x) 0 contDiff_const 0 u hb0 hsolve
  have hvk : (v : SobolevData (centeredCube z r hr)) ∈ S.space := by
    have h := hv0
    rwa [ZeroMemClass.coe_zero, sub_zero] at h
  let w : S.space := ⟨v, hvk⟩
  have hLd := aux_prop_as_response_bank_cauchy_load_diff z r hr fD F KD hFb hFeq
    (v : SobolevData (centeredCube z r hr)) (us : SobolevData (centeredCube z r hr)) U V _
    hU hV hdist
  have hLus : L us = inverseResponse S aS L := (inverseResponse_eq_load S aS L).symm
  have hLw : L w = sobolevVolumeLoad fD (v : SobolevData (centeredCube z r hr)) := rfl
  have hLus' : L us = sobolevVolumeLoad fD (us : SobolevData (centeredCube z r hr)) := rfl
  have hgreat := (inverseResponse_isGreatest S aT L).2 (Set.mem_range_self ((1 / factor) • w))
  simp only [map_smul, _root_.smul_apply, smul_eq_mul] at hgreat
  have hEw : responseForm S aT w w =
      sobolevCoefficientForm aT (v : SobolevData (centeredCube z r hr))
        (v : SobolevData (centeredCube z r hr)) := rfl
  have hEu : sobolevCoefficientForm aS (u : SobolevData (centeredCube z r hr))
      (u : SobolevData (centeredCube z r hr)) =
      inverseResponse S aS L := rfl
  rw [hEw] at hgreat
  rw [hEu] at hen
  apply aux_prop_as_response_bank_cauchy_var_core _ _ (L w) _ factor _ _ hfactor hgreat
    _ hen (by positivity)
  rw [← hLus, hLw, hLus']
  linarith [(abs_le.1 hLd).1]

/-- The response solution on the mean-zero space solves the Neumann problem against every
weak Sobolev test function, because the coefficient form ignores constants and the source
has mean zero. -/
lemma aux_prop_as_response_bank_cauchy_solves_neumann
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP0 : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (centeredCube z r hr)) u‖)
    (a : PositiveCoefficient (centeredCube z r hr))
    (f : DomainL2 (centeredCube z r hr)) (F : SpatialCoordinates d → ℝ) (K : ℝ)
    (hFm : Measurable F) (hFb : ∀ x, |F x| ≤ K)
    (hFeq : F =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      (f : SpatialCoordinates d → ℝ))
    (hFmean : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), F x) = 0) :
    SolvesNeumann a F (responseSolution (meanZeroResponseSpace hP0) a
      ((sobolevVolumeLoad f).comp (meanZeroResponseSpace hP0).space.subtypeL)) := by
  let S := meanZeroResponseSpace hP0
  let L : S.space →L[ℝ] ℝ := (sobolevVolumeLoad f).comp S.space.subtypeL
  let us : S.space := responseSolution S a L
  intro ψ
  have hvol : 0 < volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    rw [Measure.real, centeredCube_volume, ENNReal.toReal_ofReal (by positivity)]
    positivity
  set c : ℝ := (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))⁻¹ *
    ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      (ψ : SobolevData (centeredCube z r hr)).1 x with hc
  let k : SobolevData (centeredCube z r hr) :=
    (domainConstantL2 (Ω := centeredCube z r hr) c,
      fun _ => (0 : DomainL2 (centeredCube z r hr)))
  have hk_coe : ((((ψ : SobolevData (centeredCube z r hr)) - k).1 :
      DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        fun x => (ψ : SobolevData (centeredCube z r hr)).1 x - c := by
    filter_upwards [Lp.coeFn_sub ((ψ : SobolevData (centeredCube z r hr)).1)
      (domainConstantL2 (Ω := centeredCube z r hr) c),
      domainConstantL2_coeFn (Ω := centeredCube z r hr) c] with x h1 h2
    change ((((ψ : SobolevData (centeredCube z r hr)).1 -
      domainConstantL2 (Ω := centeredCube z r hr) c) : DomainL2 (centeredCube z r hr)) :
        SpatialCoordinates d → ℝ) x = _
    rw [h1, Pi.sub_apply, h2]
  have hψint : Integrable (fun x => ((ψ : SobolevData (centeredCube z r hr)).1 :
      SpatialCoordinates d → ℝ) x)
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    have h := (Lp.memLp ((ψ : SobolevData (centeredCube z r hr)).1)).integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    simpa using h
  have hmem : (ψ : SobolevData (centeredCube z r hr)) - k ∈ S.space := by
    change _ ∈ meanZeroSobolevGraph (centeredCube z r hr)
    rw [mem_meanZeroSobolevGraph_iff]
    refine ⟨Submodule.sub_mem _ ψ.property (constantSobolevData_mem_weak c), ?_⟩
    rw [integral_congr_ae hk_coe, integral_sub hψint (integrable_const c),
      MeasureTheory.setIntegral_const, hc, smul_eq_mul]
    field_simp
    ring
  let ψ0 : S.space := ⟨(ψ : SobolevData (centeredCube z r hr)) - k, hmem⟩
  have hkform : sobolevCoefficientForm a (us : SobolevData (centeredCube z r hr)) k = 0 := by
    have hgk : sobolevGradient k = 0 := by
      have h0 : (fun _ : Fin d => (0 : DomainL2 (centeredCube z r hr))) = 0 := rfl
      simp [k, sobolevGradient, h0]
    change (weightedGradientForm a.val) (sobolevGradient (us : SobolevData _))
      (sobolevGradient k) = 0
    rw [hgk, map_zero]
  have hspec : sobolevCoefficientForm a (us : SobolevData (centeredCube z r hr))
      ((ψ : SobolevData (centeredCube z r hr)) - k) =
      sobolevVolumeLoad f ((ψ : SobolevData (centeredCube z r hr)) - k) :=
    responseSolution_spec S a L ψ0
  have hsplit : (ψ : SobolevData (centeredCube z r hr)) =
      ((ψ : SobolevData (centeredCube z r hr)) - k) + k := (sub_add_cancel _ _).symm
  have hlhs : sobolevCoefficientForm a (us : SobolevData (centeredCube z r hr))
      (ψ : SobolevData (centeredCube z r hr)) =
      sobolevVolumeLoad f ((ψ : SobolevData (centeredCube z r hr)) - k) := by
    conv_lhs => rw [hsplit]
    rw [map_add, hkform, add_zero, hspec]
  change sobolevCoefficientForm a (us : SobolevData (centeredCube z r hr))
    (ψ : SobolevData (centeredCube z r hr)) = _
  rw [hlhs, sobolevVolumeLoad_apply]
  have hFint : Integrable (fun x => F x * ((ψ : SobolevData (centeredCube z r hr)).1 :
      SpatialCoordinates d → ℝ) x)
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    hψint.bdd_mul hFm.aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hFb x)
  have hFint1 : Integrable F
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    have h := (integrable_const (1 : ℝ)).bdd_mul hFm.aestronglyMeasurable
      (ae_of_all (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))
        fun x => by rw [Real.norm_eq_abs]; exact hFb x)
    simpa using h
  calc (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        f x * (((ψ : SobolevData (centeredCube z r hr)) - k).1 :
          DomainL2 (centeredCube z r hr)) x)
      = ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          F x * ((ψ : SobolevData (centeredCube z r hr)).1 x) - c * F x := by
        apply integral_congr_ae
        filter_upwards [hFeq, hk_coe] with x h1 h2
        rw [h2, ← h1]
        ring
    _ = ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          F x * (ψ : SobolevData (centeredCube z r hr)).1 x := by
        rw [integral_sub hFint (hFint1.const_mul c), integral_const_mul, hFmean, mul_zero,
          sub_zero]

/-- Mean-zero Neumann volume-source transfer. -/
lemma aux_prop_as_response_bank_cauchy_neumann_source_transfer
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP0 : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (centeredCube z r hr)) u‖)
    (aT aS : PositiveCoefficient (centeredCube z r hr)) (err factor : ℝ)
    (herr : 0 ≤ err) (hfactor : 1 ≤ factor)
    (fN : DomainL2 (centeredCube z r hr)) (KN : ℝ) (hKN : 0 ≤ KN)
    (hfN : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      |(fN : SpatialCoordinates d → ℝ) x| ≤ KN)
    (hfNmean : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      (fN : SpatialCoordinates d → ℝ) x) = 0)
    (hN : ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
           0 ≤ Kf → Measurable F → (∀ x ∈ centeredCube z r hr, |F x| ≤ Kf) →
           (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), F x) = 0 →
           ∀ u : meanZeroSobolevGraph (centeredCube z r hr), SolvesNeumann aS F u →
             ∃ (v : meanZeroSobolevGraph (centeredCube z r hr)) (U V : SpatialCoordinates d → ℝ),
               ContinuousOn U (closedCube z r hr) ∧ ContinuousOn V (closedCube z r hr) ∧
               ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                 =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
               ((v : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
                 =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] V ∧
               (∀ x ∈ closedCube z r hr, |V x - U x| ≤ err * Kf) ∧
               sobolevCoefficientForm aT (v : SobolevData (centeredCube z r hr))
                   (v : SobolevData (centeredCube z r hr)) ≤
                 factor * sobolevCoefficientForm aS (u : SobolevData (centeredCube z r hr))
                   (u : SobolevData (centeredCube z r hr)) +
                 err * Kf ^ 2) :
    inverseResponse (meanZeroResponseSpace hP0) aS
        ((sobolevVolumeLoad fN).comp (meanZeroResponseSpace hP0).space.subtypeL) ≤
      factor * inverseResponse (meanZeroResponseSpace hP0) aT
          ((sobolevVolumeLoad fN).comp (meanZeroResponseSpace hP0).space.subtypeL) +
        (2 * (KN * (err * KN) *
            volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) +
          err * KN ^ 2) := by
  let S := meanZeroResponseSpace hP0
  let L : S.space →L[ℝ] ℝ := (sobolevVolumeLoad fN).comp S.space.subtypeL
  obtain ⟨F, hFm, hFb, hFeq⟩ := aux_prop_as_response_bank_cauchy_source_rep fN KN hKN hfN
  have hFmean : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), F x) = 0 := by
    rw [integral_congr_ae hFeq, hfNmean]
  let us : S.space := responseSolution S aS L
  have hsolve : SolvesNeumann aS F us :=
    aux_prop_as_response_bank_cauchy_solves_neumann z r hr hP0 aS fN F KN hFm hFb hFeq hFmean
  obtain ⟨v, U, V, -, -, hU, hV, hdist, hen⟩ :=
    hN F KN hKN hFm (fun x _ => hFb x) hFmean us hsolve
  let w : S.space := v
  have hLd := aux_prop_as_response_bank_cauchy_load_diff z r hr fN F KN hFb hFeq
    (v : SobolevData (centeredCube z r hr)) (us : SobolevData (centeredCube z r hr)) U V _
    hU hV hdist
  have hLus : L us = inverseResponse S aS L := (inverseResponse_eq_load S aS L).symm
  have hLw : L w = sobolevVolumeLoad fN (v : SobolevData (centeredCube z r hr)) := rfl
  have hLus' : L us = sobolevVolumeLoad fN (us : SobolevData (centeredCube z r hr)) := rfl
  have hgreat := (inverseResponse_isGreatest S aT L).2 (Set.mem_range_self ((1 / factor) • w))
  simp only [map_smul, _root_.smul_apply, smul_eq_mul] at hgreat
  have hEw : responseForm S aT w w =
      sobolevCoefficientForm aT (v : SobolevData (centeredCube z r hr))
        (v : SobolevData (centeredCube z r hr)) := rfl
  have hEu : sobolevCoefficientForm aS (us : SobolevData (centeredCube z r hr))
      (us : SobolevData (centeredCube z r hr)) = inverseResponse S aS L := rfl
  rw [hEw] at hgreat
  rw [hEu] at hen
  apply aux_prop_as_response_bank_cauchy_var_core _ _ (L w) _ factor _ _ hfactor hgreat
    _ hen (by positivity)
  rw [← hLus, hLw, hLus']
  linarith [(abs_le.1 hLd).1]

end

section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

/-- The sourced Dirichlet trial clause of `lem_finite_source_comparison` (second assertion)
for a fixed target/source coefficient pair. -/
def aux_prop_as_response_bank_cauchy_DClause {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (aT aS : PositiveCoefficient (centeredCube z r hr)) (err factor : ℝ) : Prop :=
  ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
    0 ≤ Kf → Measurable F → (∀ x ∈ centeredCube z r hr, |F x| ≤ Kf) →
      ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ 2 phi →
    ∀ b u : weakSobolevGraph (centeredCube z r hr),
      ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
      SolvesDirichlet aS F b u →
      ∃ (v : weakSobolevGraph (centeredCube z r hr)) (U V : SpatialCoordinates d → ℝ),
        (v : SobolevData (centeredCube z r hr)) - (b : SobolevData (centeredCube z r hr)) ∈
          killedSobolevGraph (centeredCube z r hr) ∧
        ContinuousOn U (closedCube z r hr) ∧ ContinuousOn V (closedCube z r hr) ∧
        ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
        ((v : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] V ∧
        (∀ x ∈ closedCube z r hr, |V x - U x| ≤ err * (Kf + c2Norm (closedCube z r hr) phi)) ∧
        sobolevCoefficientForm aT (v : SobolevData (centeredCube z r hr))
            (v : SobolevData (centeredCube z r hr)) ≤
          factor * sobolevCoefficientForm aS (u : SobolevData (centeredCube z r hr))
            (u : SobolevData (centeredCube z r hr)) +
          err * (Kf + c2Norm (closedCube z r hr) phi) ^ 2

/-- The sourced mean-zero Neumann trial clause of `lem_finite_source_comparison`. -/
def aux_prop_as_response_bank_cauchy_NClause {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (aT aS : PositiveCoefficient (centeredCube z r hr)) (err factor : ℝ) : Prop :=
  ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
    0 ≤ Kf → Measurable F → (∀ x ∈ centeredCube z r hr, |F x| ≤ Kf) →
    (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), F x) = 0 →
    ∀ u : meanZeroSobolevGraph (centeredCube z r hr), SolvesNeumann aS F u →
      ∃ (v : meanZeroSobolevGraph (centeredCube z r hr)) (U V : SpatialCoordinates d → ℝ),
        ContinuousOn U (closedCube z r hr) ∧ ContinuousOn V (closedCube z r hr) ∧
        ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
        ((v : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] V ∧
        (∀ x ∈ closedCube z r hr, |V x - U x| ≤ err * Kf) ∧
        sobolevCoefficientForm aT (v : SobolevData (centeredCube z r hr))
            (v : SobolevData (centeredCube z r hr)) ≤
          factor * sobolevCoefficientForm aS (u : SobolevData (centeredCube z r hr))
            (u : SobolevData (centeredCube z r hr)) +
          err * Kf ^ 2

/-- The data-dependent multiplier of the exponential remainder, common to the three
non-affine responses. -/
def aux_prop_as_response_bank_cauchy_errMul {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (phi : SpatialCoordinates d → ℝ) (KD KN : ℝ) : ℝ :=
  (0 + c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi) ^ 2 +
    (2 * (KD * |KD + c2Norm (closedCube z r hr : Set (SpatialCoordinates d))
        (0 : SpatialCoordinates d → ℝ)| *
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) +
      (KD + c2Norm (closedCube z r hr : Set (SpatialCoordinates d))
        (0 : SpatialCoordinates d → ℝ)) ^ 2) +
    (2 * (KN * KN * volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) + KN ^ 2)

lemma aux_prop_as_response_bank_cauchy_errMul_nonneg {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (phi : SpatialCoordinates d → ℝ) (KD KN : ℝ) (hKD : 0 ≤ KD) :
    0 ≤ aux_prop_as_response_bank_cauchy_errMul z r hr phi KD KN := by
  unfold aux_prop_as_response_bank_cauchy_errMul
  have hv : 0 ≤ volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    measureReal_nonneg
  have h1 := mul_nonneg (mul_nonneg hKD (abs_nonneg (KD + c2Norm
    (closedCube z r hr : Set (SpatialCoordinates d)) (0 : SpatialCoordinates d → ℝ)))) hv
  have h2 := mul_nonneg (mul_self_nonneg KN) hv
  have h3 := sq_nonneg (0 + c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi)
  have h4 := sq_nonneg (KD + c2Norm (closedCube z r hr : Set (SpatialCoordinates d))
    (0 : SpatialCoordinates d → ℝ))
  have h5 := sq_nonneg KN
  linarith

/-- On the complement of the two exceptional events (target `N` and target `M`), each of
the three non-affine responses satisfies the two-sided multiplicative comparison. -/
lemma aux_prop_as_response_bank_cauchy_pair_omega
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (hP0 : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (centeredCube z r hr)) u‖)
    (aN aM : PositiveCoefficient (centeredCube z r hr)) (err q : ℝ)
    (herr : 0 ≤ err) (hq : 1 ≤ q)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (b : weakSobolevGraph (centeredCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (fD fN : DomainL2 (centeredCube z r hr)) (KD KN : ℝ) (hKD : 0 ≤ KD) (hKN : 0 ≤ KN)
    (hfD : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      |(fD : SpatialCoordinates d → ℝ) x| ≤ KD)
    (hfN : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      |(fN : SpatialCoordinates d → ℝ) x| ≤ KN)
    (hfNmean : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      (fN : SpatialCoordinates d → ℝ) x) = 0)
    (hDf : aux_prop_as_response_bank_cauchy_DClause z r hr aN aM err q)
    (hDt : aux_prop_as_response_bank_cauchy_DClause z r hr aM aN err q)
    (hNf : aux_prop_as_response_bank_cauchy_NClause z r hr aN aM err q)
    (hNt : aux_prop_as_response_bank_cauchy_NClause z r hr aM aN err q) :
    (|dirichletResponse (killedResponseSpace hP) aN b -
        dirichletResponse (killedResponseSpace hP) aM b| ≤
      (q - 1) * dirichletResponse (killedResponseSpace hP) aN b +
        err * aux_prop_as_response_bank_cauchy_errMul z r hr phi KD KN) ∧
    (|inverseResponse (killedResponseSpace hP) aN
          ((sobolevVolumeLoad fD).comp (killedResponseSpace hP).space.subtypeL) -
        inverseResponse (killedResponseSpace hP) aM
          ((sobolevVolumeLoad fD).comp (killedResponseSpace hP).space.subtypeL)| ≤
      (q - 1) * inverseResponse (killedResponseSpace hP) aN
          ((sobolevVolumeLoad fD).comp (killedResponseSpace hP).space.subtypeL) +
        err * aux_prop_as_response_bank_cauchy_errMul z r hr phi KD KN) ∧
    (|inverseResponse (meanZeroResponseSpace hP0) aN
          ((sobolevVolumeLoad fN).comp (meanZeroResponseSpace hP0).space.subtypeL) -
        inverseResponse (meanZeroResponseSpace hP0) aM
          ((sobolevVolumeLoad fN).comp (meanZeroResponseSpace hP0).space.subtypeL)| ≤
      (q - 1) * inverseResponse (meanZeroResponseSpace hP0) aN
          ((sobolevVolumeLoad fN).comp (meanZeroResponseSpace hP0).space.subtypeL) +
        err * aux_prop_as_response_bank_cauchy_errMul z r hr phi KD KN) := by
  have hq1 : 0 ≤ q - 1 := by linarith
  have hv : 0 ≤ volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    measureReal_nonneg
  have hEnn := aux_prop_as_response_bank_cauchy_errMul_nonneg z r hr phi KD KN hKD
  have hunf : aux_prop_as_response_bank_cauchy_errMul z r hr phi KD KN =
    (0 + c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi) ^ 2 +
    (2 * (KD * |KD + c2Norm (closedCube z r hr : Set (SpatialCoordinates d))
        (0 : SpatialCoordinates d → ℝ)| *
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) +
      (KD + c2Norm (closedCube z r hr : Set (SpatialCoordinates d))
        (0 : SpatialCoordinates d → ℝ)) ^ 2) +
    (2 * (KN * KN * volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) + KN ^ 2) :=
    rfl
  have hK1 := mul_nonneg (mul_nonneg hKD (abs_nonneg (KD + c2Norm
    (closedCube z r hr : Set (SpatialCoordinates d)) (0 : SpatialCoordinates d → ℝ)))) hv
  have hN1 := mul_nonneg (mul_self_nonneg KN) hv
  have hsqD := sq_nonneg (0 + c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi)
  have hsqK := sq_nonneg (KD + c2Norm (closedCube z r hr : Set (SpatialCoordinates d))
    (0 : SpatialCoordinates d → ℝ))
  have hsqN := sq_nonneg KN
  refine ⟨?_, ?_, ?_⟩
  · -- zero-source Dirichlet: target N from source M, and target M from source N
    have h1 := aux_prop_as_response_bank_cauchy_dirichlet_transfer z r hr hP aN aM err q
      phi hphi b hb hDf
    have h2 := aux_prop_as_response_bank_cauchy_dirichlet_transfer z r hr hP aM aN err q
      phi hphi b hb hDt
    have hmono : err * (0 + c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi) ^ 2 ≤
        err * aux_prop_as_response_bank_cauchy_errMul z r hr phi KD KN :=
      mul_le_mul_of_nonneg_left (by rw [hunf]; linarith) herr
    have hpair := aux_prop_as_response_bank_cauchy_pair_abs _ _ q _ hq1
      (h1.trans (add_le_add le_rfl hmono)) (h2.trans (add_le_add le_rfl hmono))
    exact hpair
  · -- killed volume source: source M into target N, and source N into target M
    have h1 := aux_prop_as_response_bank_cauchy_killed_source_transfer z r hr hP aN aM err q
      herr hq fD KD hKD hfD hDf
    have h2 := aux_prop_as_response_bank_cauchy_killed_source_transfer z r hr hP aM aN err q
      herr hq fD KD hKD hfD hDt
    have hsrc : 2 * (KD * (err * (KD + c2Norm (closedCube z r hr : Set (SpatialCoordinates d))
          (0 : SpatialCoordinates d → ℝ))) *
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) +
        err * (KD + c2Norm (closedCube z r hr : Set (SpatialCoordinates d))
          (0 : SpatialCoordinates d → ℝ)) ^ 2 ≤
        err * aux_prop_as_response_bank_cauchy_errMul z r hr phi KD KN := by
      have hB := mul_le_mul_of_nonneg_left (le_abs_self (KD + c2Norm
        (closedCube z r hr : Set (SpatialCoordinates d)) (0 : SpatialCoordinates d → ℝ))) herr
      have hKB := mul_le_mul_of_nonneg_left hB hKD
      have hKBv := mul_le_mul_of_nonneg_right hKB hv
      rw [hunf]
      nlinarith
    have hpair := aux_prop_as_response_bank_cauchy_pair_abs _ _ q _ hq1
      (h2.trans (add_le_add le_rfl hsrc)) (h1.trans (add_le_add le_rfl hsrc))
    exact hpair
  · -- mean-zero Neumann volume source
    have h1 := aux_prop_as_response_bank_cauchy_neumann_source_transfer z r hr hP0 aN aM err q
      herr hq fN KN hKN hfN hfNmean hNf
    have h2 := aux_prop_as_response_bank_cauchy_neumann_source_transfer z r hr hP0 aM aN err q
      herr hq fN KN hKN hfN hfNmean hNt
    have hsrc : 2 * (KN * (err * KN) *
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) + err * KN ^ 2 ≤
        err * aux_prop_as_response_bank_cauchy_errMul z r hr phi KD KN := by
      rw [hunf]
      nlinarith
    have hpair := aux_prop_as_response_bank_cauchy_pair_abs _ _ q _ hq1
      (h2.trans (add_le_add le_rfl hsrc)) (h1.trans (add_le_add le_rfl hsrc))
    exact hpair

end

section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

/-- The multiplicative factor produced by tolerance `ε'` in both the normalization ratio
and the stopping error is within `eps` of one. -/
lemma aux_prop_as_response_bank_cauchy_factor_bound (eps ε' : ℝ) (hε' : 0 < ε')
    (hε'3 : ε' ≤ 1 / 3) (hε'e : ε' ≤ eps / 5) :
    1 ≤ (1 + ε') / (1 - ε') * (1 + ε') ∧ (1 + ε') / (1 - ε') * (1 + ε') - 1 ≤ eps ∧
      0 < (1 + ε') / (1 - ε') ∧ (1 + ε') / (1 - ε') ≤ 2 := by
  have hpos : 0 < 1 - ε' := by linarith
  have hc1 : 1 ≤ (1 + ε') / (1 - ε') := by
    rw [le_div_iff₀ hpos]
    linarith
  have hc3 : (1 + ε') / (1 - ε') ≤ 1 + 3 * ε' := by
    rw [div_le_iff₀ hpos]
    nlinarith
  refine ⟨?_, ?_, by positivity, ?_⟩
  · nlinarith
  · have h : (1 + ε') / (1 - ε') * (1 + ε') ≤ (1 + 3 * ε') * (1 + ε') :=
      mul_le_mul_of_nonneg_right hc3 (by linarith)
    nlinarith
  · rw [div_le_iff₀ hpos]
    linarith

/-- The common finite-comparison input of all branches: for each tolerance, one pair of
exceptional events (target `N` and target `M`) outside which the sourced Dirichlet and Neumann
trial clauses of `lem_finite_source_comparison` hold in both directions, for both infrared
conventions, with factor within `eps` of one and remainder `Ceta 3^{-γN}`. -/
theorem aux_prop_as_response_bank_cauchy_clauses
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : in_responses d model) (Sreg : in_6_16 d model) (_It : in_iteration d model Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_HI : InfraredCharacterization model H),
        model.delta ≤ min 1 delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
        (∃ j : ℤ, r = (3 : ℝ) ^ j) →
      ∀ (_hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖),
      ∀ (eps : ℝ), 0 < eps →
        ∃ Ceta gamma : ℝ, ∃ N0 : ℕ, 0 < Ceta ∧ 0 < gamma ∧
          ∀ N : ℕ, N0 ≤ N →
            ∃ M0 : ℕ, N ≤ M0 ∧
              ∀ M : ℕ, M0 ≤ M →
                ∃ (q : ℝ) (Bf Bt : Set (BilateralField d)),
                  1 ≤ q ∧ q - 1 ≤ eps ∧
                  (chaosSampleLaw model).toMeasure Bf ≤
                    ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) ∧
                  (chaosSampleLaw model).toMeasure Bt ≤
                    ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) ∧
                  ∀ omega, omega ∉ Bf → omega ∉ Bt → ∀ infrared : Bool,
                    aux_prop_as_response_bank_cauchy_DClause z r hr
                      (cutoffPositiveCoefficient model (if infrared then H else
                        (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega N z hr)
                      (cutoffPositiveCoefficient model (if infrared then H else
                        (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega M z hr)
                      (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) q ∧
                    aux_prop_as_response_bank_cauchy_DClause z r hr
                      (cutoffPositiveCoefficient model (if infrared then H else
                        (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega M z hr)
                      (cutoffPositiveCoefficient model (if infrared then H else
                        (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega N z hr)
                      (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) q ∧
                    aux_prop_as_response_bank_cauchy_NClause z r hr
                      (cutoffPositiveCoefficient model (if infrared then H else
                        (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega N z hr)
                      (cutoffPositiveCoefficient model (if infrared then H else
                        (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega M z hr)
                      (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) q ∧
                    aux_prop_as_response_bank_cauchy_NClause z r hr
                      (cutoffPositiveCoefficient model (if infrared then H else
                        (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega M z hr)
                      (cutoffPositiveCoefficient model (if infrared then H else
                        (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega N z hr)
                      (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) q := by
  have hfsc := lem_finite_source_comparison d hd Jc Pc Xc W Cp Sf D hES Step Dbase (1 / 4) (by norm_num)
  obtain ⟨H1, Dgeom, CgF, deltaF, hH1, -, hCgF, hdeltaF, hpart1, hpart2⟩ := hfsc
  have hdens0 := aux_prop_as_response_bank_cauchy_density d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp (1 / 4)
    (by norm_num) (by norm_num) H1 hH1 Dgeom CgF deltaF hCgF hpart1
  obtain ⟨delta1, hdelta1, hdens⟩ := hdens0
  clear hpart1
  refine ⟨min deltaF delta1, lt_min hdeltaF hdelta1, ?_⟩
  intro model Rm Sreg It H HI hsmall z r hr htri hP eps heps
  have hsF : model.delta ≤ deltaF :=
    hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hs1 : model.delta ≤ min 1 delta1 :=
    hsmall.trans (min_le_min_left _ (min_le_right _ _))
  have hdn := hdens model Rm Sreg It H HI hs1 hsF z r hr htri hP
  obtain ⟨e, he, hdensity⟩ := hdn
  clear hdens
  -- tolerances
  obtain ⟨ε', hε'def⟩ : ∃ x : ℝ, x = min (eps / 5) (1 / 3) := ⟨_, rfl⟩
  have hε' : 0 < ε' := by rw [hε'def]; exact lt_min (by linarith) (by norm_num)
  have hε'3 : ε' ≤ 1 / 3 := by rw [hε'def]; exact min_le_right _ _
  have hε'e : ε' ≤ eps / 5 := by rw [hε'def]; exact min_le_left _ _
  have hLD : 0 < CgF * ((3 : ℝ) ^ H1) ^ Dgeom := by positivity
  obtain ⟨η, hηdef⟩ : ∃ x : ℝ, x = ε' / (CgF * ((3 : ℝ) ^ H1) ^ Dgeom) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; positivity
  have hηε : CgF * η * ((3 : ℝ) ^ H1) ^ Dgeom = ε' := by
    rw [hηdef]
    field_simp
  have hp2 := hpart2 model Rm Sreg It H HI hsF z r hr htri η hη
  obtain ⟨Ceta, gamma, N0F, hCeta, hgamma, hbody⟩ := hp2
  clear hpart2
  obtain ⟨Ne, hNe⟩ := hdensity ε' hε'
  obtain ⟨hq1, hqe, hc0, hc2⟩ :=
    aux_prop_as_response_bank_cauchy_factor_bound eps ε' hε' hε'3 hε'e
  refine ⟨Ceta, gamma, max N0F Ne, hCeta, hgamma, ?_⟩
  intro N hN
  have hN0F : N0F ≤ N := le_trans (le_max_left _ _) hN
  have hNe' : Ne ≤ N := le_trans (le_max_right _ _) hN
  let kap : ℕ → ℝ := fun J =>
    Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
      SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
  have hgr := aux_prop_as_response_bank_cauchy_good_ratio kap e
    (fun k => (he k).1) (fun k => (he k).2) N ε' hε' (by linarith)
  obtain ⟨M1, hNM1, hM1⟩ := hgr
  refine ⟨M1, hNM1, ?_⟩
  intro M hM
  have hNM : N ≤ M := le_trans hNM1 hM
  let S : ℕ → Prop := fun n => |(kap (N - H1 * n) / kap N) / e (H1 * n) - 1| ≤ ε'
  have hS : (1 / 4 : ℝ) *
      (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) ≤
      (Nat.card {n : ℕ // S n ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) := by
    have h := hNe N hNe'
    have hcard : (Nat.card {n : ℕ // S n ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) =
        (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N ∧
          |((Real.exp ((((N - H1 * n : ℕ) : ℝ) + 1) *
                _root_.SubdiffusiveProcess.Model.tauSq model.P) *
              SubdiffusiveProcess.CoarseGrainingVocab.ahom model (N - H1 * n)) /
            (Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
              SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)) / e (H1 * n) - 1| ≤ ε'} : ℝ) := by
      congr 1
      exact Nat.card_congr (Equiv.subtypeEquivRight fun n => by
        simp only [S, kap]
        tauto)
    rw [hcard]
    have hnn : (0 : ℝ) ≤
        (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) := Nat.cast_nonneg _
    linarith
  have hkle : ∀ n : ℕ, 4 * (H1 * n) ≤ 3 * N → H1 * n ≤ N := fun n h => by omega
  have hratio_f : ∀ n : ℕ, S n → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N →
      (kap (N - H1 * n) / kap N) / (kap (M - H1 * n) / kap M) ≤ (1 + ε') / (1 - ε') :=
    fun n hn _ h2 => (hM1 M hM (H1 * n) (hkle n h2) hn).1
  have hratio_t : ∀ n : ℕ, S n → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N →
      (kap (M - H1 * n) / kap M) / (kap (N - H1 * n) / kap N) ≤ (1 + ε') / (1 - ε') :=
    fun n hn _ h2 => (hM1 M hM (H1 * n) (hkle n h2) hn).2
  have hbf := hbody N M hN0F hNM ((1 + ε') / (1 - ε')) hc0 hc2 S hS false hratio_f
  obtain ⟨Bf, -, hBf, hf⟩ := hbf
  have hbt := hbody N M hN0F hNM ((1 + ε') / (1 - ε')) hc0 hc2 S hS true hratio_t
  obtain ⟨Bt, -, hBt, ht⟩ := hbt
  clear hbody
  have hfac : (1 + ε') / (1 - ε') * (1 + CgF * η * ((3 : ℝ) ^ H1) ^ Dgeom) =
      (1 + ε') / (1 - ε') * (1 + ε') := by rw [hηε]
  refine ⟨(1 + ε') / (1 - ε') * (1 + ε'), Bf, Bt, hq1, hqe, hBf, hBt, ?_⟩
  intro omega hof hot infrared
  exact ⟨hfac ▸ (hf omega hof infrared).1, hfac ▸ (ht omega hot infrared).1,
    hfac ▸ (hf omega hof infrared).2, hfac ▸ (ht omega hot infrared).2⟩

end

section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

/-- Two exceptional events and a pointwise two-sided comparison give the tail estimate. -/
lemma aux_prop_as_response_bank_cauchy_event_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z W : Ω → ℝ) (Bad₁ Bad₂ : Set Ω) (eps q e T p : ℝ)
    (hq : q - 1 ≤ eps) (he : e ≤ T) (hp : 0 ≤ p) (hpT : p + p ≤ T)
    (hnn : ∀ omega, 0 ≤ Z omega)
    (hbad₁ : P Bad₁ ≤ ENNReal.ofReal p) (hbad₂ : P Bad₂ ≤ ENNReal.ofReal p)
    (hgood : ∀ omega, omega ∉ Bad₁ → omega ∉ Bad₂ →
      |Z omega - W omega| ≤ (q - 1) * Z omega + e) :
    P {omega | |Z omega - W omega| > eps * Z omega + T} ≤ ENNReal.ofReal T := by
  have hsub : {omega | |Z omega - W omega| > eps * Z omega + T} ⊆ Bad₁ ∪ Bad₂ := by
    intro omega homega
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    have h := hgood omega hnot.1 hnot.2
    have hZ := hnn omega
    have hmul : (q - 1) * Z omega ≤ eps * Z omega := mul_le_mul_of_nonneg_right hq hZ
    have homega' : |Z omega - W omega| > eps * Z omega + T := homega
    linarith
  calc P {omega | |Z omega - W omega| > eps * Z omega + T} ≤ P (Bad₁ ∪ Bad₂) :=
        measure_mono hsub
    _ ≤ P Bad₁ + P Bad₂ := measure_union_le _ _
    _ ≤ ENNReal.ofReal p + ENNReal.ofReal p := add_le_add hbad₁ hbad₂
    _ = ENNReal.ofReal (p + p) := (ENNReal.ofReal_add hp hp).symm
    _ ≤ ENNReal.ofReal T := ENNReal.ofReal_le_ofReal hpT

/-- The six non-affine branches (`i = 0,1,2`, both infrared conventions) of the two-cutoff
estimate, with one common tail event pair and one constant set. The multiplicative
constant is one. -/
theorem aux_prop_as_response_bank_cauchy_tail_six
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : in_responses d model) (Sreg : in_6_16 d model) (_It : in_iteration d model Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_HI : InfraredCharacterization model H),
        model.delta ≤ min 1 delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
        (∃ j : ℤ, r = (3 : ℝ) ^ j) →
      ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖),
      ∀ (hP0 : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (meanZeroSobolevGraph (centeredCube z r hr)) u‖),
      ∀ (phi : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ phi →
      ∀ (b : weakSobolevGraph (centeredCube z r hr)),
        ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
      ∀ (fD fN : DomainL2 (centeredCube z r hr)) (KD KN : ℝ),
        0 ≤ KD → 0 ≤ KN →
        (∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
          |(fD : SpatialCoordinates d → ℝ) x| ≤ KD) →
        (∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
          |(fN : SpatialCoordinates d → ℝ) x| ≤ KN) →
        (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          (fN : SpatialCoordinates d → ℝ) x) = 0 →
      ∀ (eps : ℝ), 0 < eps →
        ∃ Ceps ceps : ℝ, ∃ N0 : ℕ,
          0 < Ceps ∧ 0 < ceps ∧
          ∀ N : ℕ, N0 ≤ N →
            ∃ M0 : ℕ, N ≤ M0 ∧
              ∀ M : ℕ, M0 ≤ M →
                ∀ infrared : Bool,
                  let a : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr) :=
                    fun K omega => cutoffPositiveCoefficient model
                      (if infrared then H else
                        (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega K z hr
                  (chaosSampleLaw model).toMeasure {omega |
                      |dirichletResponse (killedResponseSpace hP) (a N omega) b -
                        dirichletResponse (killedResponseSpace hP) (a M omega) b| >
                      eps * dirichletResponse (killedResponseSpace hP) (a N omega) b +
                        Ceps * (3 : ℝ) ^ (-(ceps * (N : ℝ)))} ≤
                    ENNReal.ofReal (Ceps * (3 : ℝ) ^ (-(ceps * (N : ℝ)))) ∧
                  (chaosSampleLaw model).toMeasure {omega |
                      |inverseResponse (killedResponseSpace hP) (a N omega)
                          ((sobolevVolumeLoad fD).comp
                            (killedResponseSpace hP).space.subtypeL) -
                        inverseResponse (killedResponseSpace hP) (a M omega)
                          ((sobolevVolumeLoad fD).comp
                            (killedResponseSpace hP).space.subtypeL)| >
                      eps * inverseResponse (killedResponseSpace hP) (a N omega)
                          ((sobolevVolumeLoad fD).comp
                            (killedResponseSpace hP).space.subtypeL) +
                        Ceps * (3 : ℝ) ^ (-(ceps * (N : ℝ)))} ≤
                    ENNReal.ofReal (Ceps * (3 : ℝ) ^ (-(ceps * (N : ℝ)))) ∧
                  (chaosSampleLaw model).toMeasure {omega |
                      |inverseResponse (meanZeroResponseSpace hP0) (a N omega)
                          ((sobolevVolumeLoad fN).comp
                            (meanZeroResponseSpace hP0).space.subtypeL) -
                        inverseResponse (meanZeroResponseSpace hP0) (a M omega)
                          ((sobolevVolumeLoad fN).comp
                            (meanZeroResponseSpace hP0).space.subtypeL)| >
                      eps * inverseResponse (meanZeroResponseSpace hP0) (a N omega)
                          ((sobolevVolumeLoad fN).comp
                            (meanZeroResponseSpace hP0).space.subtypeL) +
                        Ceps * (3 : ℝ) ^ (-(ceps * (N : ℝ)))} ≤
                    ENNReal.ofReal (Ceps * (3 : ℝ) ^ (-(ceps * (N : ℝ)))) := by
  have hcl := aux_prop_as_response_bank_cauchy_clauses d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
  obtain ⟨delta0, hdelta0, hcl'⟩ := hcl
  refine ⟨delta0, hdelta0, ?_⟩
  intro model Rm Sreg It H HI hsmall z r hr htri hP hP0 phi hphi b hb fD fN KD KN hKD hKN hfD hfN
    hfNmean eps heps
  have hc := hcl' model Rm Sreg It H HI hsmall z r hr htri hP eps heps
  obtain ⟨Ceta, gamma, N0, hCeta, hgamma, hc'⟩ := hc
  obtain ⟨E, hEdef⟩ : ∃ x : ℝ, x = aux_prop_as_response_bank_cauchy_errMul z r hr phi KD KN :=
    ⟨_, rfl⟩
  have hE : 0 ≤ E := by
    rw [hEdef]
    exact aux_prop_as_response_bank_cauchy_errMul_nonneg z r hr phi KD KN hKD
  have hCpos : 0 < 2 * Ceta * (1 + E) := mul_pos (by positivity) (by linarith)
  refine ⟨2 * Ceta * (1 + E), gamma, N0, hCpos, hgamma, ?_⟩
  intro N hN
  have hcN := hc' N hN
  obtain ⟨M0, hNM0, hcM⟩ := hcN
  refine ⟨M0, hNM0, ?_⟩
  intro M hM infrared
  have hcMM := hcM M hM
  obtain ⟨q, Bf, Bt, hq1, hqe, hBf, hBt, hgoodc⟩ := hcMM
  have herr0 : 0 ≤ Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) := by positivity
  have hgood := fun omega (hof : omega ∉ Bf) (hot : omega ∉ Bt) =>
    aux_prop_as_response_bank_cauchy_pair_omega z r hr hP hP0
      (cutoffPositiveCoefficient model
        (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ)))
        omega N z hr)
      (cutoffPositiveCoefficient model
        (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ)))
        omega M z hr)
      (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) q
      herr0 hq1 phi hphi b hb fD fN KD KN hKD hKN hfD hfN hfNmean
      (hgoodc omega hof hot infrared).1 (hgoodc omega hof hot infrared).2.1
      (hgoodc omega hof hot infrared).2.2.1 (hgoodc omega hof hot infrared).2.2.2
  have hpow : (3 : ℝ) ^ (-gamma * (N : ℝ)) = (3 : ℝ) ^ (-(gamma * (N : ℝ))) := by
    rw [neg_mul]
  have h3 : 0 ≤ (3 : ℝ) ^ (-gamma * (N : ℝ)) := by positivity
  have hx1 : 0 ≤ Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) := mul_nonneg hCeta.le h3
  have hx2 : 0 ≤ Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) * E := mul_nonneg hx1 hE
  have hexp : 2 * Ceta * (1 + E) * (3 : ℝ) ^ (-(gamma * (N : ℝ))) =
      2 * (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) +
        2 * (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) * E) := by
    rw [← hpow]
    ring
  have hT : Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) * E ≤
      2 * Ceta * (1 + E) * (3 : ℝ) ^ (-(gamma * (N : ℝ))) := by
    rw [hexp]
    linarith only [hx1, hx2]
  have hpT : Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) + Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) ≤
      2 * Ceta * (1 + E) * (3 : ℝ) ^ (-(gamma * (N : ℝ))) := by
    rw [hexp]
    linarith only [hx1, hx2]
  have hT' : Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) *
      aux_prop_as_response_bank_cauchy_errMul z r hr phi KD KN ≤
      2 * Ceta * (1 + E) * (3 : ℝ) ^ (-(gamma * (N : ℝ))) := by
    rw [← hEdef]
    exact hT
  refine ⟨?_, ?_, ?_⟩
  · exact aux_prop_as_response_bank_cauchy_event_bound _ _ _ Bf Bt eps _ _ _ _ hqe hT' herr0
      hpT (fun omega => dirichletResponse_nonneg _ _ _) hBf hBt
      (fun omega hof hot => (hgood omega hof hot).1)
  · exact aux_prop_as_response_bank_cauchy_event_bound _ _ _ Bf Bt eps _ _ _ _ hqe hT' herr0
      hpT (fun omega => inverseResponse_nonneg _ _ _) hBf hBt
      (fun omega hof hot => (hgood omega hof hot).2.1)
  · exact aux_prop_as_response_bank_cauchy_event_bound _ _ _ Bf Bt eps _ _ _ _ hqe hT' herr0
      hpT (fun omega => inverseResponse_nonneg _ _ _) hBf hBt
      (fun omega hof hot => (hgood omega hof hot).2.2)

end

section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

/-- Enlarging the multiplicative constant and the exponential remainder shrinks the event
and weakens the probability bound. -/
lemma aux_prop_as_response_bank_cauchy_tail_mono
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z W : Ω → ℝ)
    (hnn : ∀ omega, 0 ≤ Z omega) (a b T T' : ℝ) (hab : a ≤ b) (hTT : T ≤ T')
    (h : P {omega | |Z omega - W omega| > a * Z omega + T} ≤ ENNReal.ofReal T) :
    P {omega | |Z omega - W omega| > b * Z omega + T'} ≤ ENNReal.ofReal T' := by
  refine le_trans (measure_mono ?_) (h.trans (ENNReal.ofReal_le_ofReal hTT))
  intro omega homega
  have homega' : |Z omega - W omega| > b * Z omega + T' := homega
  have hmul : a * Z omega ≤ b * Z omega := mul_le_mul_of_nonneg_right hab (hnn omega)
  change |Z omega - W omega| > a * Z omega + T
  linarith

/-- Exponential remainders compare monotonically in the constant and the rate. -/
lemma aux_prop_as_response_bank_cauchy_rate_mono (C C' c c' : ℝ) (N : ℕ)
    (hC0 : 0 ≤ C) (hC : C ≤ C') (hc : c' ≤ c) :
    C * (3 : ℝ) ^ (-(c * (N : ℝ))) ≤ C' * (3 : ℝ) ^ (-(c' * (N : ℝ))) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hpow : (3 : ℝ) ^ (-(c * (N : ℝ))) ≤ (3 : ℝ) ^ (-(c' * (N : ℝ))) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have := mul_le_mul_of_nonneg_right hc hN
    linarith
  have h3 : 0 ≤ (3 : ℝ) ^ (-(c * (N : ℝ))) := by positivity
  calc C * (3 : ℝ) ^ (-(c * (N : ℝ))) ≤ C' * (3 : ℝ) ^ (-(c * (N : ℝ))) :=
        mul_le_mul_of_nonneg_right hC h3
    _ ≤ C' * (3 : ℝ) ^ (-(c' * (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hpow (hC0.trans hC)

/-- Measurability in the sample of the four concrete responses, for either infrared
convention. -/
lemma aux_prop_as_response_bank_cauchy_measurable_branches
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (hP0 : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (centeredCube z r hr)) u‖)
    (b : weakSobolevGraph (centeredCube z r hr)) (fD fN : DomainL2 (centeredCube z r hr))
    (p : Fin d → ℝ) (infrared : Bool) (N : ℕ) :
    let a : BilateralField d → PositiveCoefficient (centeredCube z r hr) := fun omega =>
      cutoffPositiveCoefficient model
        (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ)))
        omega N z hr
    Measurable (fun omega => dirichletResponse (killedResponseSpace hP) (a omega) b) ∧
    Measurable (fun omega => inverseResponse (killedResponseSpace hP) (a omega)
      ((sobolevVolumeLoad fD).comp (killedResponseSpace hP).space.subtypeL)) ∧
    Measurable (fun omega => inverseResponse (meanZeroResponseSpace hP0) (a omega)
      ((sobolevVolumeLoad fN).comp (meanZeroResponseSpace hP0).space.subtypeL)) ∧
    Measurable (fun omega => affineInverseNeumannResponse hP0 (a omega) p) := by
  intro a
  have : Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closedCube z r hr) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  have hHused : Measurable
      (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) := by
    cases infrared
    · exact measurable_const
    · exact hH
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact aux_prop_as_response_bank_cauchy_measurable_response model _ hHused N z hr
      (fun a => dirichletResponse (killedResponseSpace hP) a b)
      (continuous_dirichletResponse_compact (killedResponseSpace hP) (closedCube z r hr) b)
  · exact aux_prop_as_response_bank_cauchy_measurable_response model _ hHused N z hr
      (fun a => inverseResponse (killedResponseSpace hP) a
        ((sobolevVolumeLoad fD).comp (killedResponseSpace hP).space.subtypeL))
      (continuous_inverseResponse_compact (killedResponseSpace hP) (closedCube z r hr) _)
  · exact aux_prop_as_response_bank_cauchy_measurable_response model _ hHused N z hr
      (fun a => inverseResponse (meanZeroResponseSpace hP0) a
        ((sobolevVolumeLoad fN).comp (meanZeroResponseSpace hP0).space.subtypeL))
      (continuous_inverseResponse_compact (meanZeroResponseSpace hP0) (closedCube z r hr) _)
  · exact aux_prop_as_response_bank_cauchy_measurable_response model _ hHused N z hr
      (fun a => affineInverseNeumannResponse hP0 a p)
      (continuous_inverseResponse_compact (meanZeroResponseSpace hP0) (closedCube z r hr) _)

/-- The Cauchy-in-probability clause from the two-cutoff tail clause, for a measurable
sequence: uniform tightness comes from the tail clause itself. -/
lemma aux_prop_as_response_bank_cauchy_cauchy_of_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → ℝ) (hmeas : ∀ N, Measurable (Z N)) (Cgeom : ℝ) (hCgeom : 0 < Cgeom)
    (hpair : ∀ eps : ℝ, 0 < eps →
      ∃ Ceps ceps : ℝ, ∃ N0 : ℕ,
        0 < Ceps ∧ 0 < ceps ∧
        ∀ N : ℕ, N0 ≤ N →
          ∃ M0 : ℕ, N ≤ M0 ∧
            ∀ M : ℕ, M0 ≤ M →
              P {omega |
                  |Z N omega - Z M omega| >
                    Cgeom * eps * Z N omega +
                      Ceps * (3 : ℝ) ^ (-(ceps * (N : ℝ)))} ≤
                ENNReal.ofReal (Ceps * (3 : ℝ) ^
                  (-(ceps * (N : ℝ))))) :
    ∀ tolerance probability : ℝ, 0 < tolerance → 0 < probability →
      ∃ J : ℕ, ∀ M M' : ℕ, J ≤ M → J ≤ M' →
        P {omega | tolerance < |Z M omega - Z M' omega|} ≤
          ENNReal.ofReal probability :=
  aux_prop_as_response_bank_cauchy_tail_to_cauchy P Z Cgeom hCgeom hpair
    (aux_prop_as_response_bank_cauchy_tight_of_tail P Z hmeas Cgeom hCgeom hpair)

end

section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

/-- The quantitative input for branch `i = 3`: the two-cutoff estimate for the inverse
affine Neumann response on every triadic cube whose side satisfies `Good`, for either infrared
convention, with its own disorder threshold and multiplicative constant fixed before
the model. It is the `i = 3` slice of the principal's second clause, with the infrared
flag allowed before the tolerance; no response limit, pair estimate, or exceptional event
is assumed. -/
def aux_prop_as_response_bank_cauchy_affineTailOn (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (Jc : in_J d) (Good : ℝ → Prop) : Prop :=
  ∃ delta3 Cg3 : ℝ, 0 < delta3 ∧ 0 < Cg3 ∧
    ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (_Rm : in_responses d model) (Sreg : in_6_16 d model) (_It : in_iteration d model Jc Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ))
      (_HI : InfraredCharacterization model H),
      model.delta ≤ min 1 delta3 →
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      (∃ j : ℤ, r = (3 : ℝ) ^ j) → Good r →
    ∀ (_hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
      (hP0 : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (meanZeroSobolevGraph (centeredCube z r hr)) u‖)
      (p : Fin d → ℝ) (infrared : Bool),
    let Y : ℕ → BilateralField d → ℝ := fun K omega =>
      affineInverseNeumannResponse hP0
        (cutoffPositiveCoefficient model
          (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ)))
          omega K z hr) p
    ∀ eps : ℝ, 0 < eps →
      ∃ Ceps ceps : ℝ, ∃ N0 : ℕ, 0 < Ceps ∧ 0 < ceps ∧
        ∀ N : ℕ, N0 ≤ N →
          ∃ M0 : ℕ, N ≤ M0 ∧
            ∀ M : ℕ, M0 ≤ M →
              (chaosSampleLaw model).toMeasure {omega |
                  |Y N omega - Y M omega| >
                    Cg3 * eps * Y N omega + Ceps * (3 : ℝ) ^ (-(ceps * (N : ℝ)))} ≤
                ENNReal.ofReal (Ceps * (3 : ℝ) ^ (-(ceps * (N : ℝ))))

/-- The principal conclusion on the triadic cubes whose side satisfies `Good` (verbatim
otherwise), from the proved six non-affine branches and the affine input on those cubes. -/
theorem aux_prop_as_response_bank_cauchy_of_affineTailOn
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (Good : ℝ → Prop) (hAff : aux_prop_as_response_bank_cauchy_affineTailOn d Jc Good) :
    ∃ delta0 Cgeom : ℝ, 0 < delta0 ∧ 0 < Cgeom ∧
      ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : in_responses d model) (Sreg : in_6_16 d model) (_It : in_iteration d model Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_HI : InfraredCharacterization model H)
        (_hdelta : model.delta ≤ min 1 delta0),
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (_htriadic : ∃ j : ℤ, r = (3 : ℝ) ^ j),
      Good r →
      let Q := centeredCube z r hr
      let _closedQ := closedCube z r hr
      ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
        ‖(u : SobolevData Q).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph Q) u‖),
      ∀ (hP0 : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph Q,
        ‖(u : SobolevData Q).1‖ ≤
          K * ‖subspaceGradient (meanZeroSobolevGraph Q) u‖),
      ∀ (phi : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ phi →
      ∀ (b : weakSobolevGraph Q),
        ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (Q : Set (SpatialCoordinates d))] phi →
      ∀ (fD fN : DomainL2 Q) (KD KN : ℝ),
        0 ≤ KD → 0 ≤ KN →
        (∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
          |(fD : SpatialCoordinates d → ℝ) x| ≤ KD) →
        (∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
          |(fN : SpatialCoordinates d → ℝ) x| ≤ KN) →
        (∫ x in (Q : Set (SpatialCoordinates d)),
          (fN : SpatialCoordinates d → ℝ) x) = 0 →
      ∀ (p : Fin d → ℝ),
      let SD := killedResponseSpace hP
      let SN := meanZeroResponseSpace hP0
      let Rsp : Bool → Fin 4 → ℕ → BilateralField d → ℝ :=
        fun infrared i N omega =>
          let Hused := if infrared then H else
            (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
          let a : ℕ → BilateralField d → PositiveCoefficient Q :=
            fun N omega => cutoffPositiveCoefficient model Hused omega N z hr
          match i.val with
          | 0 => dirichletResponse SD (a N omega) b
          | 1 => inverseResponse SD (a N omega)
              ((sobolevVolumeLoad fD).comp SD.space.subtypeL)
          | 2 => inverseResponse SN (a N omega)
              ((sobolevVolumeLoad fN).comp SN.space.subtypeL)
          | _ => affineInverseNeumannResponse hP0 (a N omega) p
      let P : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure
      (∀ (infrared : Bool) (i : Fin 4) (N : ℕ),
        ∀ᵐ omega ∂P, 0 ≤ Rsp infrared i N omega) ∧
      (∀ (eps : ℝ), 0 < eps →
        ∃ Ceps ceps : ℝ, ∃ N0 : ℕ,
          0 < Ceps ∧ 0 < ceps ∧
          ∀ N : ℕ, N0 ≤ N →
            ∃ M0 : ℕ, N ≤ M0 ∧
              ∀ M : ℕ, M0 ≤ M →
                ∀ (infrared : Bool) (i : Fin 4),
                  P {omega |
                      |Rsp infrared i N omega - Rsp infrared i M omega| >
                        Cgeom * eps * Rsp infrared i N omega +
                          Ceps * (3 : ℝ) ^ (-(ceps * (N : ℝ)))} ≤
                    ENNReal.ofReal (Ceps * (3 : ℝ) ^
                      (-(ceps * (N : ℝ))))) ∧
      (∀ (infrared : Bool) (i : Fin 4) (tolerance probability : ℝ),
        0 < tolerance → 0 < probability →
        ∃ J : ℕ, ∀ M M' : ℕ, J ≤ M → J ≤ M' →
          P {omega |
              tolerance < |Rsp infrared i M omega - Rsp infrared i M' omega|} ≤
            ENNReal.ofReal probability)  := by
  have hAff' := hAff
  obtain ⟨delta3, Cg3, hdelta3, hCg3, hA⟩ := hAff'
  have h6 := aux_prop_as_response_bank_cauchy_tail_six d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
  obtain ⟨delta6, hdelta6, h6'⟩ := h6
  have hCpos : 0 < max 1 Cg3 := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨min delta6 delta3, max 1 Cg3, lt_min hdelta6 hdelta3, hCpos, ?_⟩
  intro model Rm Sreg It H HI hdelta z r hr htri hGood Q closedQ hP hP0 phi hphi b hb fD fN KD KN hKD hKN
    hfD hfN hfNmean p SD SN Rsp P
  have hd6 : model.delta ≤ min 1 delta6 :=
    hdelta.trans (min_le_min_left _ (min_le_left _ _))
  have hd3 : model.delta ≤ min 1 delta3 :=
    hdelta.trans (min_le_min_left _ (min_le_right _ _))
  have hnn : ∀ (infrared : Bool) (i : Fin 4) (N : ℕ) (omega : BilateralField d),
      0 ≤ Rsp infrared i N omega := by
    intro infrared i N omega
    rcases i with ⟨_ | _ | _ | _ | k, hi⟩
    · exact dirichletResponse_nonneg _ _ _
    · exact inverseResponse_nonneg _ _ _
    · exact inverseResponse_nonneg _ _ _
    · exact inverseResponse_nonneg _ _ _
    · omega
  have hmeas : ∀ (infrared : Bool) (i : Fin 4) (N : ℕ), Measurable (Rsp infrared i N) := by
    intro infrared i N
    have hm := aux_prop_as_response_bank_cauchy_measurable_branches model H HI.1 z r hr hP hP0
      b fD fN p infrared N
    obtain ⟨m0, m1, m2, m3⟩ := hm
    rcases i with ⟨_ | _ | _ | _ | k, hi⟩
    · exact m0
    · exact m1
    · exact m2
    · exact m3
    · omega
  have htail : ∀ (eps : ℝ), 0 < eps →
      ∃ Ceps ceps : ℝ, ∃ N0 : ℕ,
        0 < Ceps ∧ 0 < ceps ∧
        ∀ N : ℕ, N0 ≤ N →
          ∃ M0 : ℕ, N ≤ M0 ∧
            ∀ M : ℕ, M0 ≤ M →
              ∀ (infrared : Bool) (i : Fin 4),
                P {omega |
                    |Rsp infrared i N omega - Rsp infrared i M omega| >
                      max 1 Cg3 * eps * Rsp infrared i N omega +
                        Ceps * (3 : ℝ) ^ (-(ceps * (N : ℝ)))} ≤
                  ENNReal.ofReal (Ceps * (3 : ℝ) ^
                    (-(ceps * (N : ℝ)))) := by
    intro eps heps
    have hs := h6' model Rm Sreg It H HI hd6 z r hr htri hP hP0 phi hphi b hb fD fN KD KN hKD hKN
      hfD hfN hfNmean eps heps
    obtain ⟨C6, c6, N6, hC6, hc6, hs'⟩ := hs
    have hat := hA model Rm Sreg It H HI hd3 z r hr htri hGood hP hP0 p true eps heps
    obtain ⟨Ct, ct, Nt, hCt, hct, hat'⟩ := hat
    have haf := hA model Rm Sreg It H HI hd3 z r hr htri hGood hP hP0 p false eps heps
    obtain ⟨Cf, cf, Nf, hCf, hcf, haf'⟩ := haf
    refine ⟨max C6 (max Ct Cf), min c6 (min ct cf), max N6 (max Nt Nf),
      lt_of_lt_of_le hC6 (le_max_left _ _), lt_min hc6 (lt_min hct hcf), ?_⟩
    intro N hN
    have h1 := hs' N (le_trans (le_max_left _ _) hN)
    obtain ⟨M6, hNM6, hM6⟩ := h1
    have h2 := hat' N (le_trans ((le_max_left _ _).trans (le_max_right _ _)) hN)
    obtain ⟨Mt, -, hMt⟩ := h2
    have h3 := haf' N (le_trans ((le_max_right _ _).trans (le_max_right _ _)) hN)
    obtain ⟨Mf, -, hMf⟩ := h3
    refine ⟨max M6 (max Mt Mf), le_trans hNM6 (le_max_left _ _), ?_⟩
    intro M hM infrared i
    have hT6 := aux_prop_as_response_bank_cauchy_rate_mono C6 (max C6 (max Ct Cf)) c6
      (min c6 (min ct cf)) N hC6.le (le_max_left _ _) (min_le_left _ _)
    have hTt := aux_prop_as_response_bank_cauchy_rate_mono Ct (max C6 (max Ct Cf)) ct
      (min c6 (min ct cf)) N hCt.le ((le_max_left _ _).trans (le_max_right _ _))
      ((min_le_right _ _).trans (min_le_left _ _))
    have hTf := aux_prop_as_response_bank_cauchy_rate_mono Cf (max C6 (max Ct Cf)) cf
      (min c6 (min ct cf)) N hCf.le ((le_max_right _ _).trans (le_max_right _ _))
      ((min_le_right _ _).trans (min_le_right _ _))
    have ha6 : eps ≤ max 1 Cg3 * eps := le_mul_of_one_le_left heps.le (le_max_left _ _)
    have ha3 : Cg3 * eps ≤ max 1 Cg3 * eps :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) heps.le
    have hM6' := hM6 M (le_trans (le_max_left _ _) hM) infrared
    have hMt' := hMt M (le_trans ((le_max_left _ _).trans (le_max_right _ _)) hM)
    have hMf' := hMf M (le_trans ((le_max_right _ _).trans (le_max_right _ _)) hM)
    rcases i with ⟨_ | _ | _ | _ | k, hi⟩
    · exact aux_prop_as_response_bank_cauchy_tail_mono P _ _ (hnn infrared ⟨0, hi⟩ N) _ _ _ _
        ha6 hT6 hM6'.1
    · exact aux_prop_as_response_bank_cauchy_tail_mono P _ _ (hnn infrared ⟨1, hi⟩ N) _ _ _ _
        ha6 hT6 hM6'.2.1
    · exact aux_prop_as_response_bank_cauchy_tail_mono P _ _ (hnn infrared ⟨2, hi⟩ N) _ _ _ _
        ha6 hT6 hM6'.2.2
    · cases infrared
      · exact aux_prop_as_response_bank_cauchy_tail_mono P _ _ (hnn false ⟨3, hi⟩ N) _ _ _ _
          ha3 hTf hMf'
      · exact aux_prop_as_response_bank_cauchy_tail_mono P _ _ (hnn true ⟨3, hi⟩ N) _ _ _ _
          ha3 hTt hMt'
    · omega
  refine ⟨fun infrared i N => ae_of_all _ (hnn infrared i N), htail, ?_⟩
  intro infrared i tolerance probability htol hprob
  refine aux_prop_as_response_bank_cauchy_cauchy_of_tail P (Rsp infrared i) (hmeas infrared i)
    (max 1 Cg3) hCpos ?_ tolerance probability htol hprob
  intro eps heps
  have ht := htail eps heps
  obtain ⟨Ceps, ceps, N0, hC, hc, ht'⟩ := ht
  refine ⟨Ceps, ceps, N0, hC, hc, fun N hN => ?_⟩
  have ht'' := ht' N hN
  obtain ⟨M0, hNM0, hM0⟩ := ht''
  exact ⟨M0, hNM0, fun M hM => hM0 M hM infrared i⟩

end

section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

/-- Markov's inequality for the absolute value. -/
lemma aux_prop_as_response_bank_cauchy_markov_abs
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (p B T : ℝ) (hp : 0 < p) (hB : 0 ≤ B) (hT : 0 < T)
    (_hX : AEStronglyMeasurable X P)
    (hLp : eLpNorm X (ENNReal.ofReal p) P ≤ ENNReal.ofReal B) :
    P {omega | T < |X omega|} ≤ ENNReal.ofReal ((B / T) ^ p) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hT0 : ENNReal.ofReal T ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hT
  have hpReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  have hLp' : eLpNorm X (ENNReal.ofReal p) P ^ p ≤ ENNReal.ofReal B ^ p := by
    gcongr
  have hmarkov :=
    meas_ge_le_mul_pow_eLpNorm_enorm P (f := X) hp0 hptop hT0 (by simp)
  have hbound :
      P {omega | ENNReal.ofReal T ≤ ‖X omega‖ₑ} ≤
        (ENNReal.ofReal T)⁻¹ ^ p * ENNReal.ofReal B ^ p := by
    calc
      P {omega | ENNReal.ofReal T ≤ ‖X omega‖ₑ} ≤
          (ENNReal.ofReal T)⁻¹ ^ p * eLpNorm X (ENNReal.ofReal p) P ^ p := by
            simpa [hpReal] using hmarkov
      _ ≤ (ENNReal.ofReal T)⁻¹ ^ p * ENNReal.ofReal B ^ p := by
            gcongr
  have hrhs :
      (ENNReal.ofReal T)⁻¹ ^ p * ENNReal.ofReal B ^ p = ENNReal.ofReal (B / T) ^ p := by
    rw [ENNReal.ofReal_div_of_pos hT]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt hp)]
    congr 1
    rw [div_eq_mul_inv]
    simp [mul_comm]
  have hsub : {omega | T < |X omega|} ⊆ {omega | ENNReal.ofReal T ≤ ‖X omega‖ₑ} := by
    intro omega homega
    change T < |X omega| at homega
    change ENNReal.ofReal T ≤ ‖X omega‖ₑ
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal homega.le
  calc P {omega | T < |X omega|} ≤ P {omega | ENNReal.ofReal T ≤ ‖X omega‖ₑ} :=
        measure_mono hsub
    _ ≤ ENNReal.ofReal (B / T) ^ p := hbound.trans_eq hrhs
    _ = ENNReal.ofReal ((B / T) ^ p) :=
        (ENNReal.ofReal_rpow_of_nonneg (div_nonneg hB hT.le) hp.le)

/-- Absorption of the square-root smoothing error (AM–GM). -/
lemma aux_prop_as_response_bank_cauchy_amgm (C1 K h Y δ : ℝ) (hK : 0 ≤ K)
    (hh : 0 ≤ h) (hY : 0 ≤ Y) (hδ : 0 < δ) :
    C1 * Real.sqrt K * h ^ ((1 : ℝ) / 4) * Real.sqrt Y + C1 * K * h ^ ((1 : ℝ) / 2) ≤
      δ * Y + (C1 ^ 2 / (4 * δ) + C1) * K * h ^ ((1 : ℝ) / 2) := by
  have hq : (h ^ ((1 : ℝ) / 4)) ^ 2 = h ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh]
    norm_num
  have hsK : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK
  have hsY : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY
  set a := C1 * Real.sqrt K * h ^ ((1 : ℝ) / 4) with ha
  set s := Real.sqrt Y with hs
  have ha2 : a ^ 2 = C1 ^ 2 * K * h ^ ((1 : ℝ) / 2) := by
    rw [ha, mul_pow, mul_pow, hsK, hq]
  have hkey : a * s ≤ δ * Y + a ^ 2 / (4 * δ) := by
    have h4 : 0 < 4 * δ := by positivity
    have hid : δ * s ^ 2 + a ^ 2 / (4 * δ) - a * s = (2 * δ * s - a) ^ 2 / (4 * δ) := by
      field_simp
      ring
    have hnn : 0 ≤ (2 * δ * s - a) ^ 2 / (4 * δ) := div_nonneg (sq_nonneg _) h4.le
    rw [← hsY]
    linarith
  calc a * s + C1 * K * h ^ ((1 : ℝ) / 2)
      ≤ δ * Y + a ^ 2 / (4 * δ) + C1 * K * h ^ ((1 : ℝ) / 2) := by linarith
    _ = δ * Y + (C1 ^ 2 / (4 * δ) + C1) * K * h ^ ((1 : ℝ) / 2) := by
        rw [ha2]
        field_simp
        ring

/-- The three-term comparison with the smoothed responses, after absorption. -/
lemma aux_prop_as_response_bank_cauchy_affine_combine
    (YN YM YNh YMh q δ R e3 : ℝ) (hYN : 0 ≤ YN)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hq0 : 0 ≤ q - 1) (hq : q - 1 ≤ 1 / 2)
    (hR : 0 ≤ R) (he3 : 0 ≤ e3)
    (h1 : |YN - YNh| ≤ δ * YN + R) (h2 : |YM - YMh| ≤ δ * YM + R)
    (h3 : |YNh - YMh| ≤ (q - 1) * YNh + e3) :
    |YN - YM| ≤ (4 * δ + 3 * (q - 1)) * YN + (5 * R + 2 * e3) := by
  have hNh : YNh ≤ (1 + δ) * YN + R := by
    have := (abs_le.1 h1).1
    linarith
  have hD : |YN - YM| ≤ |YN - YNh| + |YNh - YMh| + |YMh - YM| := by
    calc |YN - YM| = |(YN - YNh) + (YNh - YMh) + (YMh - YM)| := by ring_nf
      _ ≤ |(YN - YNh) + (YNh - YMh)| + |YMh - YM| := abs_add_le _ _
      _ ≤ |YN - YNh| + |YNh - YMh| + |YMh - YM| := by
          gcongr
          exact abs_add_le _ _
  have hYMle : YM ≤ YN + |YN - YM| := by
    have := neg_abs_le (YN - YM)
    linarith
  have h2' : |YMh - YM| ≤ δ * (YN + |YN - YM|) + R := by
    rw [abs_sub_comm]
    exact h2.trans (by nlinarith)
  have h3' : (q - 1) * YNh ≤ (q - 1) * ((1 + δ) * YN + R) :=
    mul_le_mul_of_nonneg_left hNh hq0
  set D := |YN - YM| with hDdef
  have hmain : D * (1 - δ) ≤ (2 * δ + (q - 1) * (1 + δ)) * YN + ((2 + (q - 1)) * R + e3) := by
    nlinarith
  have hpos : 0 < 1 - δ := by linarith
  have hhalf : 1 / 2 ≤ 1 - δ := by linarith
  have hD2 : D ≤ 2 * ((2 * δ + (q - 1) * (1 + δ)) * YN + ((2 + (q - 1)) * R + e3)) := by
    have hrhs : 0 ≤ (2 * δ + (q - 1) * (1 + δ)) * YN + ((2 + (q - 1)) * R + e3) := by
      positivity
    have hD0 : 0 ≤ D := abs_nonneg _
    nlinarith
  have hc1 : (q - 1) * (1 + δ) ≤ (q - 1) * (3 / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hq0
  have hc2 : (2 + (q - 1)) * R ≤ (5 / 2) * R := mul_le_mul_of_nonneg_right (by linarith) hR
  have hYN' : 2 * ((q - 1) * (1 + δ)) * YN ≤ 3 * (q - 1) * YN := by nlinarith
  nlinarith

/-- The deterministic smoothing error of the inverse affine Neumann response
(`neumann_load_pointwise`), for a family of smoothed volume loads. -/
lemma aux_prop_as_response_bank_cauchy_smoothing_pointwise
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP0 : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (centeredCube z r hr)) u‖)
    (p : Fin d → ℝ) (Om : Type)
    (a : ℕ → Om → PositiveCoefficient (centeredCube z r hr))
    (fh : ℝ → DomainL2 (centeredCube z r hr)) (K : ℕ → Om → ℝ) (Cc : ℝ) (hCc : 0 < Cc)
    (hK : ∀ N omega, 0 < K N omega)
    (hsm : ∀ N omega (h : ℝ), 0 < h → h < 1 / 8 →
      ∀ v : meanZeroSobolevGraph (centeredCube z r hr),
        |affineNeumannLoad p (subspaceGradient (meanZeroSobolevGraph (centeredCube z r hr)) v) -
            sobolevVolumeLoad (fh h) (v : SobolevData (centeredCube z r hr))| ≤
          Cc * h ^ ((1 : ℝ) / 4) * Real.sqrt (K N omega) *
            Real.sqrt (sobolevCoefficientForm (a N omega) (v : SobolevData (centeredCube z r hr))
              (v : SobolevData (centeredCube z r hr)))) :
    ∀ N omega (h : ℝ), 0 < h → h < 1 / 8 →
      |affineInverseNeumannResponse hP0 (a N omega) p -
          inverseResponse (meanZeroResponseSpace hP0) (a N omega)
            ((sobolevVolumeLoad (fh h)).comp (meanZeroResponseSpace hP0).space.subtypeL)| ≤
        (4 * Cc + Cc ^ 2) * Real.sqrt (K N omega) * h ^ ((1 : ℝ) / 4) *
            Real.sqrt (affineInverseNeumannResponse hP0 (a N omega) p) +
          (4 * Cc + Cc ^ 2) * K N omega * h ^ ((1 : ℝ) / 2) := by
  intro N omega h hh hh8
  let SN := meanZeroResponseSpace hP0
  let Lp : SN.space →L[ℝ] ℝ :=
    (affineNeumannLoad p).comp (subspaceGradient (meanZeroSobolevGraph (centeredCube z r hr)))
  let Lh : ℝ → SN.space →L[ℝ] ℝ := fun h' =>
    (sobolevVolumeLoad (fh h')).comp SN.space.subtypeL
  exact neumann_load_pointwise Om Unit (SobolevData (centeredCube z r hr))
    (fun _ => meanZeroSobolevGraph (centeredCube z r hr))
    (fun N _ omega => (sobolevCoefficientForm (a N omega)).toLinearMap₁₂)
    (fun N _ omega u v _ _ => sobolevCoefficientForm_symm (a N omega) u v)
    (fun N _ omega v _ => sobolevCoefficientForm_nonneg (a N omega) v)
    (fun _ => ((affineNeumannLoad p).comp sobolevGradient :
      SobolevData (centeredCube z r hr) →L[ℝ] ℝ).toLinearMap)
    (fun _ h' => (sobolevVolumeLoad (fh h')).toLinearMap)
    (fun N _ omega => ((responseSolution SN (a N omega) Lp : SN.space) :
      SobolevData (centeredCube z r hr)))
    (fun N _ omega h' => ((responseSolution SN (a N omega) (Lh h') : SN.space) :
      SobolevData (centeredCube z r hr)))
    (fun N _ omega => (responseSolution SN (a N omega) Lp).2)
    (fun N _ omega h' _ _ => (responseSolution SN (a N omega) (Lh h')).2)
    (fun N _ omega v hv => responseSolution_spec SN (a N omega) Lp ⟨v, hv⟩)
    (fun N _ omega h' _ _ v hv => responseSolution_spec SN (a N omega) (Lh h') ⟨v, hv⟩)
    (fun N _ omega => affineInverseNeumannResponse hP0 (a N omega) p)
    (fun N _ omega h' => inverseResponse SN (a N omega) (Lh h'))
    (fun N _ omega => rfl) (fun N _ omega h' _ _ => rfl)
    (fun N _ omega => K N omega) (fun N _ omega => hK N omega) Cc hCc
    (fun N _ omega h' hh' hh8' v hv => hsm N omega h' hh' hh8' ⟨v, hv⟩)
    N () omega h hh hh8

/-- On one sample outside the exceptional events: the smoothing errors at `N` and `M`, the
two-sided smoothed volume-source comparison, and absorption give the affine comparison. -/
lemma aux_prop_as_response_bank_cauchy_affine_omega
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP0 : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (centeredCube z r hr)) u‖)
    (p : Fin d → ℝ) (aN aM : PositiveCoefficient (centeredCube z r hr))
    (f : DomainL2 (centeredCube z r hr)) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hf : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      |(f : SpatialCoordinates d → ℝ) x| ≤ Kf)
    (hfmean : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      (f : SpatialCoordinates d → ℝ) x) = 0)
    (err q e1 eps C1 KN KM T h : ℝ) (herr : 0 ≤ err) (hq1 : 1 ≤ q) (hqe : q - 1 ≤ e1)
    (hC1 : 0 ≤ C1)
    (he1 : 0 < e1) (he12 : e1 ≤ 1 / 2) (he1e : e1 ≤ eps)
    (hKN : 0 ≤ KN) (hKM : 0 ≤ KM) (hKNT : KN ≤ T) (hKMT : KM ≤ T) (hh : 0 ≤ h)
    (hsN : |affineInverseNeumannResponse hP0 aN p -
        inverseResponse (meanZeroResponseSpace hP0) aN
          ((sobolevVolumeLoad f).comp (meanZeroResponseSpace hP0).space.subtypeL)| ≤
      C1 * Real.sqrt KN * h ^ ((1 : ℝ) / 4) * Real.sqrt (affineInverseNeumannResponse hP0 aN p) +
        C1 * KN * h ^ ((1 : ℝ) / 2))
    (hsM : |affineInverseNeumannResponse hP0 aM p -
        inverseResponse (meanZeroResponseSpace hP0) aM
          ((sobolevVolumeLoad f).comp (meanZeroResponseSpace hP0).space.subtypeL)| ≤
      C1 * Real.sqrt KM * h ^ ((1 : ℝ) / 4) * Real.sqrt (affineInverseNeumannResponse hP0 aM p) +
        C1 * KM * h ^ ((1 : ℝ) / 2))
    (hNf : aux_prop_as_response_bank_cauchy_NClause z r hr aN aM err q)
    (hNt : aux_prop_as_response_bank_cauchy_NClause z r hr aM aN err q) :
    |affineInverseNeumannResponse hP0 aN p - affineInverseNeumannResponse hP0 aM p| ≤
      7 * eps * affineInverseNeumannResponse hP0 aN p +
        (5 * ((C1 ^ 2 / (4 * e1) + C1) * T * h ^ ((1 : ℝ) / 2)) +
          2 * (err * (2 * (Kf * Kf *
            volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) + Kf ^ 2))) := by
  have hYN : 0 ≤ affineInverseNeumannResponse hP0 aN p := inverseResponse_nonneg _ _ _
  have hYM : 0 ≤ affineInverseNeumannResponse hP0 aM p := inverseResponse_nonneg _ _ _
  have hvol : 0 ≤ volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    measureReal_nonneg
  -- the smoothed volume-source responses compare two-sidedly
  have h1 := aux_prop_as_response_bank_cauchy_neumann_source_transfer z r hr hP0 aN aM err q
    herr hq1 f Kf hKf hf hfmean hNf
  have h2 := aux_prop_as_response_bank_cauchy_neumann_source_transfer z r hr hP0 aM aN err q
    herr hq1 f Kf hKf hf hfmean hNt
  have he3eq : 2 * (Kf * (err * Kf) *
      volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) + err * Kf ^ 2 =
      err * (2 * (Kf * Kf * volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) +
        Kf ^ 2) := by ring
  rw [he3eq] at h1 h2
  have h3 := aux_prop_as_response_bank_cauchy_pair_abs _ _ q _ (by linarith) h2 h1
  -- absorption of the smoothing errors
  have hRN := aux_prop_as_response_bank_cauchy_amgm C1 KN h _ e1 hKN hh hYN he1
  have hRM := aux_prop_as_response_bank_cauchy_amgm C1 KM h _ e1 hKM hh hYM he1
  have hCR : 0 ≤ C1 ^ 2 / (4 * e1) + C1 := by positivity
  have hh2 : 0 ≤ h ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hh _
  have hTN : (C1 ^ 2 / (4 * e1) + C1) * KN * h ^ ((1 : ℝ) / 2) ≤
      (C1 ^ 2 / (4 * e1) + C1) * T * h ^ ((1 : ℝ) / 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKNT hCR) hh2
  have hTM : (C1 ^ 2 / (4 * e1) + C1) * KM * h ^ ((1 : ℝ) / 2) ≤
      (C1 ^ 2 / (4 * e1) + C1) * T * h ^ ((1 : ℝ) / 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKMT hCR) hh2
  have hR0 : 0 ≤ (C1 ^ 2 / (4 * e1) + C1) * T * h ^ ((1 : ℝ) / 2) :=
    mul_nonneg (mul_nonneg hCR (hKN.trans hKNT)) hh2
  have he30 : 0 ≤ err * (2 * (Kf * Kf *
      volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) + Kf ^ 2) := by
    have := mul_nonneg (mul_self_nonneg Kf) hvol
    positivity
  have hc := aux_prop_as_response_bank_cauchy_affine_combine _ _ _ _ q e1 _ _ hYN he1 he12
    (by linarith) (by linarith) hR0 he30
    ((hsN.trans hRN).trans (by linarith)) ((hsM.trans hRM).trans (by linarith)) h3
  have hmul : (4 * e1 + 3 * (q - 1)) * affineInverseNeumannResponse hP0 aN p ≤
      7 * eps * affineInverseNeumannResponse hP0 aN p :=
    mul_le_mul_of_nonneg_right (by linarith) hYN
  linarith

lemma aux_prop_as_response_bank_cauchy_rpow3_le (a c x : ℝ) (hx : 0 ≤ x) (hca : c ≤ a) :
    (3 : ℝ) ^ (-(a * x)) ≤ (3 : ℝ) ^ (-(c * x)) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have := mul_le_mul_of_nonneg_right hca hx
  linarith

/-- Exponent bookkeeping for the affine branch: smoothing width `3^{-γN/4}`, localization at
`3^{γN/32}`, and the resulting common rate. -/
lemma aux_prop_as_response_bank_cauchy_affine_rates (γ p0 Ceta Cf B CR vol : ℝ) (N : ℕ)
    (hγ : 0 < γ) (hCeta : 0 ≤ Ceta) (hB : 0 ≤ B) (hCR : 0 ≤ CR) (hvol : 0 ≤ vol) :
    5 * (CR * (3 : ℝ) ^ (γ / 32 * (N : ℝ)) * ((3 : ℝ) ^ (-(γ / 4 * (N : ℝ)))) ^ ((1 : ℝ) / 2)) +
        2 * (Ceta * (3 : ℝ) ^ (-γ * (N : ℝ)) *
          (2 * (Cf / (3 : ℝ) ^ (-(γ / 4 * (N : ℝ))) * (Cf / (3 : ℝ) ^ (-(γ / 4 * (N : ℝ)))) *
              vol) + (Cf / (3 : ℝ) ^ (-(γ / 4 * (N : ℝ)))) ^ 2)) ≤
      (5 * CR + 2 * Ceta * Cf ^ 2 * (2 * vol + 1) + 2 * Ceta + 2 * B + 1) *
        (3 : ℝ) ^ (-(min (3 * γ / 32) (p0 * γ / 32) * (N : ℝ))) ∧
    Ceta * (3 : ℝ) ^ (-γ * (N : ℝ)) + Ceta * (3 : ℝ) ^ (-γ * (N : ℝ)) +
        B * ((3 : ℝ) ^ (γ / 32 * (N : ℝ))) ^ (-p0) + B * ((3 : ℝ) ^ (γ / 32 * (N : ℝ))) ^ (-p0) ≤
      (5 * CR + 2 * Ceta * Cf ^ 2 * (2 * vol + 1) + 2 * Ceta + 2 * B + 1) *
        (3 : ℝ) ^ (-(min (3 * γ / 32) (p0 * γ / 32) * (N : ℝ))) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h3 : (0 : ℝ) < 3 := by norm_num
  set c := min (3 * γ / 32) (p0 * γ / 32) with hc
  set t := (3 : ℝ) ^ (-(c * (N : ℝ))) with ht
  have ht0 : 0 ≤ t := by positivity
  -- the smoothing remainder
  have hR : (3 : ℝ) ^ (γ / 32 * (N : ℝ)) * ((3 : ℝ) ^ (-(γ / 4 * (N : ℝ)))) ^ ((1 : ℝ) / 2) =
      (3 : ℝ) ^ (-(3 * γ / 32 * (N : ℝ))) := by
    rw [← Real.rpow_mul h3.le, ← Real.rpow_add h3]
    congr 1
    ring
  have hRle : (3 : ℝ) ^ (-(3 * γ / 32 * (N : ℝ))) ≤ t :=
    aux_prop_as_response_bank_cauchy_rpow3_le _ _ _ hN (min_le_left _ _)
  -- the smoothed-source remainder
  have hKf : Cf / (3 : ℝ) ^ (-(γ / 4 * (N : ℝ))) = Cf * (3 : ℝ) ^ (γ / 4 * (N : ℝ)) := by
    rw [Real.rpow_neg h3.le, div_inv_eq_mul]
  have hsq : (3 : ℝ) ^ (γ / 4 * (N : ℝ)) * (3 : ℝ) ^ (γ / 4 * (N : ℝ)) =
      (3 : ℝ) ^ (γ / 2 * (N : ℝ)) := by
    rw [← Real.rpow_add h3]
    congr 1
    ring
  have hE3 : (3 : ℝ) ^ (-γ * (N : ℝ)) * (3 : ℝ) ^ (γ / 2 * (N : ℝ)) =
      (3 : ℝ) ^ (-(γ / 2 * (N : ℝ))) := by
    rw [← Real.rpow_add h3]
    congr 1
    ring
  have hE3le : (3 : ℝ) ^ (-(γ / 2 * (N : ℝ))) ≤ t :=
    aux_prop_as_response_bank_cauchy_rpow3_le _ _ _ hN
      ((min_le_left _ _).trans (by linarith))
  have hGle : (3 : ℝ) ^ (-γ * (N : ℝ)) ≤ t := by
    rw [neg_mul]
    exact aux_prop_as_response_bank_cauchy_rpow3_le _ _ _ hN
      ((min_le_left _ _).trans (by linarith))
  have he3 : Ceta * (3 : ℝ) ^ (-γ * (N : ℝ)) *
      (2 * (Cf / (3 : ℝ) ^ (-(γ / 4 * (N : ℝ))) * (Cf / (3 : ℝ) ^ (-(γ / 4 * (N : ℝ)))) *
          vol) + (Cf / (3 : ℝ) ^ (-(γ / 4 * (N : ℝ)))) ^ 2) =
      Ceta * Cf ^ 2 * (2 * vol + 1) * (3 : ℝ) ^ (-(γ / 2 * (N : ℝ))) := by
    rw [hKf, ← hE3, ← hsq]
    ring
  -- the localization tail
  have hT : B * ((3 : ℝ) ^ (γ / 32 * (N : ℝ))) ^ (-p0) =
      B * (3 : ℝ) ^ (-(p0 * γ / 32 * (N : ℝ))) := by
    rw [← Real.rpow_mul h3.le]
    congr 2
    ring
  have hTle : (3 : ℝ) ^ (-(p0 * γ / 32 * (N : ℝ))) ≤ t :=
    aux_prop_as_response_bank_cauchy_rpow3_le _ _ _ hN (min_le_right _ _)
  have hA : 0 ≤ Ceta * Cf ^ 2 * (2 * vol + 1) := by positivity
  have hR' : CR * (3 : ℝ) ^ (γ / 32 * (N : ℝ)) *
      ((3 : ℝ) ^ (-(γ / 4 * (N : ℝ)))) ^ ((1 : ℝ) / 2) =
      CR * (3 : ℝ) ^ (-(3 * γ / 32 * (N : ℝ))) := by
    rw [mul_assoc, hR]
  constructor
  · rw [hR', he3]
    have h1 := mul_le_mul_of_nonneg_left hRle hCR
    have h2 := mul_le_mul_of_nonneg_left hE3le hA
    nlinarith
  · rw [hT]
    have h1 := mul_le_mul_of_nonneg_left hGle hCeta
    have h2 := mul_le_mul_of_nonneg_left hTle hB
    nlinarith

end

section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

lemma aux_prop_as_response_bank_cauchy_width_small (γ : ℝ) (hγ : 0 < γ) :
    ∃ Nh : ℕ, ∀ N : ℕ, Nh ≤ N → (3 : ℝ) ^ (-(γ / 4 * (N : ℝ))) < 1 / 8 := by
  have hlin : Tendsto (fun N : ℕ => γ / 4 * (N : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop :
      Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).const_mul_atTop' (by positivity)
  have hlim : Tendsto (fun N : ℕ => (3 : ℝ) ^ (-(γ / 4 * (N : ℝ)))) atTop (𝓝 0) :=
    (tendsto_rpow_atBot_of_base_gt_one (3 : ℝ) (by norm_num)).comp
      (tendsto_neg_atTop_atBot.comp hlin)
  exact eventually_atTop.1 (hlim.eventually (gt_mem_nhds (by norm_num)))

/-- Branch `i = 3` on one triadic cube, from an explicit smoothing family
`fh` (bounded by `Cf/h`, mean zero) whose load error against the affine Neumann load is
controlled by a random constant `K` with a fixed moment. The smoothing width is `3^{-γN/4}`
and `K` is localized at `3^{γN/32}`, where `γ` is the rate of the finite comparison chosen
after the tolerance. -/
theorem aux_prop_as_response_bank_cauchy_affine_of_smoothing
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : in_responses d model) (Sreg : in_6_16 d model) (_It : in_iteration d model Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_HI : InfraredCharacterization model H),
        model.delta ≤ min 1 delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
        (∃ j : ℤ, r = (3 : ℝ) ^ j) →
      ∀ (_hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
          ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
            K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
        (hP0 : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph (centeredCube z r hr),
          ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
            K * ‖subspaceGradient (meanZeroSobolevGraph (centeredCube z r hr)) u‖)
        (p : Fin d → ℝ) (infrared : Bool)
        (fh : ℝ → DomainL2 (centeredCube z r hr)) (Cf Cc B p0 : ℝ)
        (K : ℕ → BilateralField d → ℝ),
        0 ≤ Cf → 0 < Cc → 0 < p0 → 0 ≤ B →
        (∀ h : ℝ, 0 < h → h < 1 / 8 →
          ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
            |(fh h : SpatialCoordinates d → ℝ) x| ≤ Cf / h) →
        (∀ h : ℝ, 0 < h → h < 1 / 8 →
          (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            (fh h : SpatialCoordinates d → ℝ) x) = 0) →
        (∀ N omega, 0 < K N omega) →
        (∀ N omega (h : ℝ), 0 < h → h < 1 / 8 →
          ∀ v : meanZeroSobolevGraph (centeredCube z r hr),
            |affineNeumannLoad p
                (subspaceGradient (meanZeroSobolevGraph (centeredCube z r hr)) v) -
              sobolevVolumeLoad (fh h) (v : SobolevData (centeredCube z r hr))| ≤
            Cc * h ^ ((1 : ℝ) / 4) * Real.sqrt (K N omega) *
              Real.sqrt (sobolevCoefficientForm
                (cutoffPositiveCoefficient model (if infrared then H else
                  (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega N z hr)
                (v : SobolevData (centeredCube z r hr))
                (v : SobolevData (centeredCube z r hr)))) →
        (∀ N (t : ℝ), 0 < t →
          (chaosSampleLaw model).toMeasure {omega | t < K N omega} ≤
            ENNReal.ofReal (B * t ^ (-p0))) →
      ∀ eps : ℝ, 0 < eps →
        ∃ Ceps ceps : ℝ, ∃ N0 : ℕ, 0 < Ceps ∧ 0 < ceps ∧
          ∀ N : ℕ, N0 ≤ N →
            ∃ M0 : ℕ, N ≤ M0 ∧
              ∀ M : ℕ, M0 ≤ M →
                (chaosSampleLaw model).toMeasure {omega |
                    |affineInverseNeumannResponse hP0
                        (cutoffPositiveCoefficient model (if infrared then H else
                          (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega N z hr) p -
                      affineInverseNeumannResponse hP0
                        (cutoffPositiveCoefficient model (if infrared then H else
                          (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega M z hr) p| >
                    7 * eps * affineInverseNeumannResponse hP0
                        (cutoffPositiveCoefficient model (if infrared then H else
                          (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega N z hr) p +
                      Ceps * (3 : ℝ) ^ (-(ceps * (N : ℝ)))} ≤
                  ENNReal.ofReal (Ceps * (3 : ℝ) ^ (-(ceps * (N : ℝ)))) := by
  have hcl := aux_prop_as_response_bank_cauchy_clauses d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
  obtain ⟨delta0, hdelta0, hcl'⟩ := hcl
  refine ⟨delta0, hdelta0, ?_⟩
  intro model Rm Sreg It H HI hsmall z r hr htri hP hP0 p infrared fh Cf Cc B p0 K hCf hCc hp0 hB
    hfb hfmean hK hsm hKtail eps heps
  obtain ⟨e1, he1def⟩ : ∃ x : ℝ, x = min eps (1 / 2) := ⟨_, rfl⟩
  have he1 : 0 < e1 := by rw [he1def]; exact lt_min heps (by norm_num)
  have he12 : e1 ≤ 1 / 2 := by rw [he1def]; exact min_le_right _ _
  have he1e : e1 ≤ eps := by rw [he1def]; exact min_le_left _ _
  have hc := hcl' model Rm Sreg It H HI hsmall z r hr htri hP e1 he1
  obtain ⟨Ceta, gamma, N0c, hCeta, hgamma, hc'⟩ := hc
  have hC1 : 0 ≤ 4 * Cc + Cc ^ 2 := by positivity
  have hCR : 0 ≤ (4 * Cc + Cc ^ 2) ^ 2 / (4 * e1) + (4 * Cc + Cc ^ 2) := by positivity
  have hvol : 0 ≤ volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    measureReal_nonneg
  obtain ⟨Nh, hNh⟩ := aux_prop_as_response_bank_cauchy_width_small gamma hgamma
  have hCtot : 0 < 5 * ((4 * Cc + Cc ^ 2) ^ 2 / (4 * e1) + (4 * Cc + Cc ^ 2)) +
      2 * Ceta * Cf ^ 2 * (2 * volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) +
        1) + 2 * Ceta + 2 * B + 1 := by
    have : 0 ≤ 2 * Ceta * Cf ^ 2 *
        (2 * volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) + 1) := by
      positivity
    linarith
  have hceps : 0 < min (3 * gamma / 32) (p0 * gamma / 32) := lt_min (by positivity) (by positivity)
  refine ⟨_, _, max N0c Nh, hCtot, hceps, ?_⟩
  intro N hN
  have hcN := hc' N (le_trans (le_max_left _ _) hN)
  obtain ⟨M0, hNM0, hcM⟩ := hcN
  refine ⟨M0, hNM0, ?_⟩
  intro M hM
  have hcMM := hcM M hM
  obtain ⟨q, Bf, Bt, hq1, hqe, hBf, hBt, hgoodc⟩ := hcMM
  have hh0 : 0 < (3 : ℝ) ^ (-(gamma / 4 * (N : ℝ))) := by positivity
  have hh8 := hNh N (le_trans (le_max_right _ _) hN)
  have hT0 : 0 < (3 : ℝ) ^ (gamma / 32 * (N : ℝ)) := by positivity
  have herr0 : 0 ≤ Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) := by positivity
  have hspt := aux_prop_as_response_bank_cauchy_smoothing_pointwise z r hr hP0 p
    (BilateralField d)
    (fun N' omega => cutoffPositiveCoefficient model (if infrared then H else
      (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega N' z hr) fh K Cc hCc hK hsm
  have hPKN := hKtail N _ hT0
  have hPKM := hKtail M _ hT0
  have hrates := aux_prop_as_response_bank_cauchy_affine_rates gamma p0 Ceta Cf B
    ((4 * Cc + Cc ^ 2) ^ 2 / (4 * e1) + (4 * Cc + Cc ^ 2))
    (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) N hgamma hCeta.le hB hCR
    hvol
  obtain ⟨hrate1, hrate2⟩ := hrates
  have hKf : 0 ≤ Cf / (3 : ℝ) ^ (-(gamma / 4 * (N : ℝ))) := div_nonneg hCf hh0.le
  have hsub : {omega |
      |affineInverseNeumannResponse hP0
          (cutoffPositiveCoefficient model (if infrared then H else
            (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega N z hr) p -
        affineInverseNeumannResponse hP0
          (cutoffPositiveCoefficient model (if infrared then H else
            (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega M z hr) p| >
      7 * eps * affineInverseNeumannResponse hP0
          (cutoffPositiveCoefficient model (if infrared then H else
            (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega N z hr) p +
        (5 * ((4 * Cc + Cc ^ 2) ^ 2 / (4 * e1) + (4 * Cc + Cc ^ 2)) +
          2 * Ceta * Cf ^ 2 *
            (2 * volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) + 1) +
          2 * Ceta + 2 * B + 1) *
          (3 : ℝ) ^ (-(min (3 * gamma / 32) (p0 * gamma / 32) * (N : ℝ)))} ⊆
      Bf ∪ Bt ∪ {omega | (3 : ℝ) ^ (gamma / 32 * (N : ℝ)) < K N omega} ∪
        {omega | (3 : ℝ) ^ (gamma / 32 * (N : ℝ)) < K M omega} := by
    intro omega homega
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hnot
    obtain ⟨⟨⟨hof, hot⟩, hKN⟩, hKM⟩ := hnot
    have hom := aux_prop_as_response_bank_cauchy_affine_omega z r hr hP0 p
      (cutoffPositiveCoefficient model (if infrared then H else
        (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega N z hr)
      (cutoffPositiveCoefficient model (if infrared then H else
        (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega M z hr)
      (fh ((3 : ℝ) ^ (-(gamma / 4 * (N : ℝ)))))
      (Cf / (3 : ℝ) ^ (-(gamma / 4 * (N : ℝ)))) hKf (hfb _ hh0 hh8) (hfmean _ hh0 hh8)
      (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) q e1 eps (4 * Cc + Cc ^ 2) (K N omega) (K M omega)
      ((3 : ℝ) ^ (gamma / 32 * (N : ℝ))) ((3 : ℝ) ^ (-(gamma / 4 * (N : ℝ)))) herr0 hq1 hqe hC1
      he1 he12 he1e (hK N omega).le (hK M omega).le hKN hKM hh0.le
      (hspt N omega _ hh0 hh8) (hspt M omega _ hh0 hh8)
      (hgoodc omega hof hot infrared).2.2.1 (hgoodc omega hof hot infrared).2.2.2
    have homega' := homega
    simp only [mem_ofPred_eq] at homega'
    linarith
  have hsum : ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) +
      ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) +
      ENNReal.ofReal (B * ((3 : ℝ) ^ (gamma / 32 * (N : ℝ))) ^ (-p0)) +
      ENNReal.ofReal (B * ((3 : ℝ) ^ (gamma / 32 * (N : ℝ))) ^ (-p0)) =
      ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) + Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) +
        B * ((3 : ℝ) ^ (gamma / 32 * (N : ℝ))) ^ (-p0) +
        B * ((3 : ℝ) ^ (gamma / 32 * (N : ℝ))) ^ (-p0)) := by
    have hx : 0 ≤ B * ((3 : ℝ) ^ (gamma / 32 * (N : ℝ))) ^ (-p0) :=
      mul_nonneg hB (Real.rpow_nonneg hT0.le _)
    rw [ENNReal.ofReal_add (by positivity) hx, ENNReal.ofReal_add (by positivity) hx,
      ENNReal.ofReal_add herr0 herr0]
  calc _ ≤ (chaosSampleLaw model).toMeasure (Bf ∪ Bt ∪
          {omega | (3 : ℝ) ^ (gamma / 32 * (N : ℝ)) < K N omega} ∪
          {omega | (3 : ℝ) ^ (gamma / 32 * (N : ℝ)) < K M omega}) := measure_mono hsub
    _ ≤ (chaosSampleLaw model).toMeasure Bf + (chaosSampleLaw model).toMeasure Bt +
          (chaosSampleLaw model).toMeasure
            {omega | (3 : ℝ) ^ (gamma / 32 * (N : ℝ)) < K N omega} +
          (chaosSampleLaw model).toMeasure
            {omega | (3 : ℝ) ^ (gamma / 32 * (N : ℝ)) < K M omega} := by
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
    _ ≤ _ := add_le_add (add_le_add (add_le_add hBf hBt) hPKN) hPKM
    _ = _ := hsum
    _ ≤ _ := ENNReal.ofReal_le_ofReal hrate2

end

section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

/-- Load approximation (`eq:mfd-bump`) transported to every
triadic cube and every slope: a mean-zero smoothed volume load of size `O(1/h)` whose
difference from the affine Neumann load is `O(h^{1/4})` in the `H^{3/4}` seminorm of the
mean-free part. Deterministic; `lem_load` states it for `unitNeumannCube d` and unit slopes. -/
def aux_prop_as_response_bank_cauchy_loadApprox (d : ℕ) (hd : 2 ≤ d) : Prop :=
  ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), (∃ j : ℤ, r = (3 : ℝ) ^ j) →
  ∀ p : Fin d → ℝ,
  ∃ (fh : ℝ → DomainL2 (centeredCube z r hr)) (Cf Cload : ℝ), 0 ≤ Cf ∧ 0 ≤ Cload ∧
    (∀ h : ℝ, 0 < h → h < 1 / 8 →
      ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        |(fh h : SpatialCoordinates d → ℝ) x| ≤ Cf / h) ∧
    (∀ h : ℝ, 0 < h → h < 1 / 8 →
      (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        (fh h : SpatialCoordinates d → ℝ) x) = 0) ∧
    (∀ h : ℝ, 0 < h → h < 1 / 8 → ∀ v : weakSobolevGraph (centeredCube z r hr),
      |affineNeumannLoad p (subspaceGradient (weakSobolevGraph (centeredCube z r hr)) v) -
          ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            (fh h : SpatialCoordinates d → ℝ) x * (v : SobolevData (centeredCube z r hr)).1 x| ≤
        Cload * h ^ ((1 : ℝ) / 4) *
          Real.sqrt (cubeFractionalSqNorm hd z r hr threeQuarterOrder
            ((v : SobolevData (centeredCube z r hr)).1 -
              domainConstantL2 (domainMean (v : SobolevData (centeredCube z r hr)).1))))

/-- Coarse coercivity (`mfd:lem-coercivity`) on the triadic cubes whose side
satisfies `Good`, for both infrared conventions, with a fixed polynomial tail of the
coercivity constant; the
disorder threshold precedes the model. `lem_coercivity` states the mean-zero inequality and
uniform moments for cubes of side `≤ 1` and the infrared-including coefficient. -/
def aux_prop_as_response_bank_cauchy_coercivityTailOn (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (Good : ℝ → Prop) : Prop :=
  ∃ deltaK : ℝ, 0 < deltaK ∧
    ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (_Rm : in_responses d model)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ))
      (_HI : InfraredCharacterization model H),
      model.delta ≤ min 1 deltaK →
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), (∃ j : ℤ, r = (3 : ℝ) ^ j) → Good r →
    ∀ infrared : Bool,
    ∃ (K : ℕ → BilateralField d → ℝ) (B p0 : ℝ), 0 ≤ B ∧ 0 < p0 ∧
      (∀ N omega, 0 < K N omega) ∧
      (∀ N omega (v : meanZeroSobolevGraph (centeredCube z r hr)),
        cubeFractionalSqNorm hd z r hr threeQuarterOrder
            (v : SobolevData (centeredCube z r hr)).1 ≤
          K N omega * sobolevCoefficientForm
            (cutoffPositiveCoefficient model (if infrared then H else
              (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega N z hr)
            (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr))) ∧
      (∀ N (t : ℝ), 0 < t →
        (chaosSampleLaw model).toMeasure {omega | t < K N omega} ≤
          ENNReal.ofReal (B * t ^ (-p0)))

lemma aux_prop_as_response_bank_cauchy_domainConstantL2_zero {d : ℕ}
    (Q : Opens (SpatialCoordinates d))
    [IsFiniteMeasure (volume.restrict (Q : Set (SpatialCoordinates d)))] :
    domainConstantL2 (Ω := Q) 0 = 0 := by
  apply Lp.ext
  filter_upwards [domainConstantL2_coeFn (Ω := Q) (0 : ℝ),
    Lp.coeFn_zero ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d)))] with x h1 h2
  rw [h1, h2]
  rfl

/-- The mean-zero smoothing estimate of the affine branch from the two analytic inputs. -/
lemma aux_prop_as_response_bank_cauchy_smoothing_of_inputs
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (p : Fin d → ℝ) (Om : Type) (a : ℕ → Om → PositiveCoefficient (centeredCube z r hr))
    (fh : ℝ → DomainL2 (centeredCube z r hr)) (Cload : ℝ) (hCload : 0 ≤ Cload)
    (K : ℕ → Om → ℝ) (hKpos : ∀ N omega, 0 < K N omega)
    (hload : ∀ h : ℝ, 0 < h → h < 1 / 8 → ∀ v : weakSobolevGraph (centeredCube z r hr),
      |affineNeumannLoad p (subspaceGradient (weakSobolevGraph (centeredCube z r hr)) v) -
          ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            (fh h : SpatialCoordinates d → ℝ) x * (v : SobolevData (centeredCube z r hr)).1 x| ≤
        Cload * h ^ ((1 : ℝ) / 4) *
          Real.sqrt (cubeFractionalSqNorm hd z r hr threeQuarterOrder
            ((v : SobolevData (centeredCube z r hr)).1 -
              domainConstantL2 (domainMean (v : SobolevData (centeredCube z r hr)).1))))
    (hcoer : ∀ N omega (v : meanZeroSobolevGraph (centeredCube z r hr)),
      cubeFractionalSqNorm hd z r hr threeQuarterOrder
          (v : SobolevData (centeredCube z r hr)).1 ≤
        K N omega * sobolevCoefficientForm (a N omega)
          (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr))) :
    ∀ N omega (h : ℝ), 0 < h → h < 1 / 8 →
      ∀ v : meanZeroSobolevGraph (centeredCube z r hr),
        |affineNeumannLoad p (subspaceGradient (meanZeroSobolevGraph (centeredCube z r hr)) v) -
            sobolevVolumeLoad (fh h) (v : SobolevData (centeredCube z r hr))| ≤
          (Cload + 1) * h ^ ((1 : ℝ) / 4) * Real.sqrt (K N omega) *
            Real.sqrt (sobolevCoefficientForm (a N omega) (v : SobolevData (centeredCube z r hr))
              (v : SobolevData (centeredCube z r hr))) := by
  intro N omega h hh hh8 v
  have hvw : (v : SobolevData (centeredCube z r hr)) ∈ weakSobolevGraph (centeredCube z r hr) :=
    ((mem_meanZeroSobolevGraph_iff _).1 v.2).1
  have hint : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ((v : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) x) = 0 :=
    ((mem_meanZeroSobolevGraph_iff _).1 v.2).2
  have hmean : domainMean (v : SobolevData (centeredCube z r hr)).1 = 0 := by
    unfold domainMean
    rw [hint, mul_zero]
  have h1 := hload h hh hh8 ⟨(v : SobolevData (centeredCube z r hr)), hvw⟩
  rw [hmean, aux_prop_as_response_bank_cauchy_domainConstantL2_zero, sub_zero] at h1
  have hE := sobolevCoefficientForm_nonneg (a N omega) (v : SobolevData (centeredCube z r hr))
  have hsq : Real.sqrt (cubeFractionalSqNorm hd z r hr threeQuarterOrder
      (v : SobolevData (centeredCube z r hr)).1) ≤
      Real.sqrt (K N omega) * Real.sqrt (sobolevCoefficientForm (a N omega)
        (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr))) := by
    rw [← Real.sqrt_mul (hKpos N omega).le]
    exact Real.sqrt_le_sqrt (hcoer N omega v)
  have hh4 : 0 ≤ h ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hh.le _
  rw [sobolevVolumeLoad_apply]
  change |affineNeumannLoad p (subspaceGradient (weakSobolevGraph (centeredCube z r hr))
      ⟨(v : SobolevData (centeredCube z r hr)), hvw⟩) - _| ≤ _
  refine h1.trans ?_
  have hprod : 0 ≤ Real.sqrt (K N omega) * Real.sqrt (sobolevCoefficientForm (a N omega)
      (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr))) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc Cload * h ^ ((1 : ℝ) / 4) * Real.sqrt (cubeFractionalSqNorm hd z r hr threeQuarterOrder
        (v : SobolevData (centeredCube z r hr)).1)
      ≤ Cload * h ^ ((1 : ℝ) / 4) * (Real.sqrt (K N omega) *
          Real.sqrt (sobolevCoefficientForm (a N omega) (v : SobolevData (centeredCube z r hr))
            (v : SobolevData (centeredCube z r hr)))) :=
        mul_le_mul_of_nonneg_left hsq (mul_nonneg hCload hh4)
    _ ≤ (Cload + 1) * h ^ ((1 : ℝ) / 4) * (Real.sqrt (K N omega) *
          Real.sqrt (sobolevCoefficientForm (a N omega) (v : SobolevData (centeredCube z r hr))
            (v : SobolevData (centeredCube z r hr)))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hh4) hprod
    _ = _ := by ring

/-- The affine input on the cubes satisfying `Good` follows from load approximation and
coercivity on those cubes. -/
theorem aux_prop_as_response_bank_cauchy_affineTail_of_inputsOn
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (Good : ℝ → Prop) (hL : aux_prop_as_response_bank_cauchy_loadApprox d hd)
    (hK : aux_prop_as_response_bank_cauchy_coercivityTailOn d hd Good) :
    aux_prop_as_response_bank_cauchy_affineTailOn d Jc Good := by
  obtain ⟨deltaK, hdK, hK'⟩ := hK
  have hA0 := aux_prop_as_response_bank_cauchy_affine_of_smoothing d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
  obtain ⟨deltaA, hdA, hA⟩ := hA0
  refine ⟨min deltaK deltaA, 7, lt_min hdK hdA, by norm_num, ?_⟩
  intro model Rm Sreg It H HI hsmall z r hr htri hGood hP hP0 p infrared Y eps heps
  have hsK : model.delta ≤ min 1 deltaK :=
    hsmall.trans (min_le_min_left _ (min_le_left _ _))
  have hsA : model.delta ≤ min 1 deltaA :=
    hsmall.trans (min_le_min_left _ (min_le_right _ _))
  have hLz := hL z r hr htri p
  obtain ⟨fh, Cf, Cload, hCf, hCload, hfb, hfm, hload⟩ := hLz
  have hKz := hK' model Rm H HI hsK z r hr htri hGood infrared
  obtain ⟨K, B, p0, hB, hp0, hKpos, hcoer, hKtail⟩ := hKz
  have hsm := aux_prop_as_response_bank_cauchy_smoothing_of_inputs hd z r hr p
    (BilateralField d)
    (fun N omega => cutoffPositiveCoefficient model (if infrared then H else
      (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega N z hr)
    fh Cload hCload K hKpos hload hcoer
  exact hA model Rm Sreg It H HI hsA z r hr htri hP hP0 p infrared fh Cf (Cload + 1) B p0 K hCf
    (by linarith) hp0 hB hfb hfm hKpos hsm hKtail eps heps

/-- Removing the infrared field lowers the concrete cutoff coefficient by at most the
exponential of the sup norm of `H ω` on the closed cube. -/
lemma aux_prop_as_response_bank_cauchy_coeff_infrared_le
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N : ℕ) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient model H omega N z hr).val x ≤
        Real.exp ‖(H omega).restrict (closedCube z r hr : Set (SpatialCoordinates d))‖ *
          (cutoffPositiveCoefficient model
            (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega N z hr).val x := by
  have hF : Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closedCube z r hr) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  rw [aux_prop_as_response_bank_cauchy_coeff_eq model H omega N z hr,
    aux_prop_as_response_bank_cauchy_coeff_eq model 0 omega N z hr]
  filter_upwards [expPotentialCoefficient_coeFn (@compactPotentialToLp d (centeredCube z r hr)
      (closedCube z r hr) ⟨centeredCube_subset_closedCube z hr⟩
      ((H omega + ∑ j ∈ Finset.range (N + 1), omega (-(Int.ofNat j))).restrict
          (closedCube z r hr : Set (SpatialCoordinates d)) +
        ContinuousMap.const _ (-(Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)) -
          ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P))),
    expPotentialCoefficient_coeFn (@compactPotentialToLp d (centeredCube z r hr)
      (closedCube z r hr) ⟨centeredCube_subset_closedCube z hr⟩
      (((0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega +
          ∑ j ∈ Finset.range (N + 1), omega (-(Int.ofNat j))).restrict
          (closedCube z r hr : Set (SpatialCoordinates d)) +
        ContinuousMap.const _ (-(Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)) -
          ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P))),
    compactPotentialToLp_on_domain (Ω := centeredCube z r hr) (closedCube z r hr)
      ((H omega + ∑ j ∈ Finset.range (N + 1), omega (-(Int.ofNat j))).restrict
          (closedCube z r hr : Set (SpatialCoordinates d)) +
        ContinuousMap.const _ (-(Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)) -
          ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P)),
    compactPotentialToLp_on_domain (Ω := centeredCube z r hr) (closedCube z r hr)
      (((0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega +
          ∑ j ∈ Finset.range (N + 1), omega (-(Int.ofNat j))).restrict
          (closedCube z r hr : Set (SpatialCoordinates d)) +
        ContinuousMap.const _ (-(Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)) -
          ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P)),
    ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x h1 h2 h3 h4 hx
  rw [h1, h2, h3 hx, h4 hx, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have hxK : x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) :=
    centeredCube_subset_closedCube z hr hx
  have hH : H omega x ≤ ‖(H omega).restrict (closedCube z r hr : Set (SpatialCoordinates d))‖ := by
    have := ContinuousMap.norm_coe_le_norm
      ((H omega).restrict (closedCube z r hr : Set (SpatialCoordinates d))) ⟨x, hxK⟩
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  change (H omega + ∑ j ∈ Finset.range (N + 1), omega (-(Int.ofNat j))) x +
      (-(Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)) -
        ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) ≤
    ‖(H omega).restrict (closedCube z r hr : Set (SpatialCoordinates d))‖ +
      (((0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega +
          ∑ j ∈ Finset.range (N + 1), omega (-(Int.ofNat j))) x +
        (-(Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)) -
          ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P))
  simp only [ContinuousMap.add_apply, Pi.zero_apply, zero_add]
  linarith

/-- Markov's inequality for a nonnegative integrable variable. -/
lemma aux_prop_as_response_bank_cauchy_markov_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX0 : ∀ omega, 0 ≤ X omega) (hX : Integrable X P) (s : ℝ) (hs : 0 < s) :
    P {omega | s < X omega} ≤ ENNReal.ofReal ((∫ omega, X omega ∂P) / s) := by
  have h := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hX0) hX s
  have hle : P.real {omega | s < X omega} ≤ P.real {omega | s ≤ X omega} :=
    measureReal_mono (fun omega homega => le_of_lt (show s < X omega from homega))
  have hreal : P.real {omega | s < X omega} ≤ (∫ omega, X omega ∂P) / s := by
    rw [le_div_iff₀ hs]
    nlinarith [measureReal_nonneg (μ := P) (s := {omega | s < X omega})]
  rw [← ENNReal.ofReal_toReal (measure_ne_top P {omega | s < X omega})]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Consistency check of the coercivity input against the existing suppliers: on cubes of
side `≤ 1`, `lem_coercivity` (first moment) gives the positive constant, the mean-zero
inequality and a tail of order one for the infrared-including coefficient; removing the
infrared field costs the factor `exp ‖H ω‖_{C(Q̄)}`, whose first moment is
`exp_norm_restrict_pow_integrable`, giving a tail of order one half. -/
theorem aux_prop_as_response_bank_cauchy_coercivity_small_cube
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd) :
    ∃ deltaK : ℝ, 0 < deltaK ∧
      ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : in_responses d model)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_HI : InfraredCharacterization model H),
        model.delta ≤ deltaK →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ infrared : Bool,
      ∃ (K : ℕ → BilateralField d → ℝ) (B p0 : ℝ), 0 ≤ B ∧ 0 < p0 ∧
        (∀ N omega, 0 < K N omega) ∧
        (∀ N omega (v : meanZeroSobolevGraph (centeredCube z r hr)),
          cubeFractionalSqNorm hd z r hr threeQuarterOrder
              (v : SobolevData (centeredCube z r hr)).1 ≤
            K N omega * sobolevCoefficientForm
              (cutoffPositiveCoefficient model (if infrared then H else
                (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega N z hr)
              (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr))) ∧
        (∀ N (t : ℝ), 0 < t →
          (chaosSampleLaw model).toMeasure {omega | t < K N omega} ≤
            ENNReal.ofReal (B * t ^ (-p0))) := by
  have hLC0 := aux_lem_coercivity_compat d hd Jc Pc Sf
  obtain ⟨delta0f, hpos, hLC⟩ := hLC0
  refine ⟨delta0f 1, hpos 1 le_rfl, ?_⟩
  intro model Rm H HI hsmall z r hr hr1 infrared
  have hK0 := hLC model Rm H HI z r hr hr1
  obtain ⟨K, hKc, hKm⟩ := hK0
  have hKm1 := hKm 1 le_rfl hsmall
  obtain ⟨Cb, hmem, hbd⟩ := hKm1
  -- the infrared-including constant `|K| + 1` and its tail of order one
  have hcoerH : ∀ N omega (v : meanZeroSobolevGraph (centeredCube z r hr)),
      cubeFractionalSqNorm hd z r hr threeQuarterOrder
          (v : SobolevData (centeredCube z r hr)).1 ≤
        (|K N omega| + 1) * sobolevCoefficientForm (cutoffPositiveCoefficient model H omega N z hr)
          (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr)) := by
    intro N omega v
    have h1 := ((hKc N omega).2 v).2
    have hE := sobolevCoefficientForm_nonneg (cutoffPositiveCoefficient model H omega N z hr)
      (v : SobolevData (centeredCube z r hr))
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (by linarith)) hE
  have htailH : ∀ N (t : ℝ), 0 < t →
      (chaosSampleLaw model).toMeasure {omega | t < |K N omega| + 1} ≤
        ENNReal.ofReal (max 2 (2 * max Cb 0) * t ^ (-(1 : ℝ))) := by
    intro N t ht
    rw [Real.rpow_neg_one]
    by_cases ht2 : t ≤ 2
    · refine (prob_le_one).trans ?_
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [← div_eq_mul_inv, le_div_iff₀ ht]
      linarith [le_max_left 2 (2 * max Cb 0)]
    · push Not at ht2
      have hbd' : eLpNorm (K N) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤
          ENNReal.ofReal (max Cb 0) :=
        (hbd N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
      have hmk := aux_prop_as_response_bank_cauchy_markov_abs (chaosSampleLaw model).toMeasure
        (K N) 1 (max Cb 0) (t / 2) one_pos (le_max_right _ _) (by linarith)
        (hmem N).aestronglyMeasurable hbd'
      refine le_trans (measure_mono ?_) (hmk.trans (ENNReal.ofReal_le_ofReal ?_))
      · intro omega homega
        change t < |K N omega| + 1 at homega
        change t / 2 < |K N omega|
        linarith
      · rw [Real.rpow_one, div_div_eq_mul_div, ← div_eq_mul_inv]
        apply div_le_div_of_nonneg_right _ ht.le
        nlinarith [le_max_right 2 (2 * max Cb 0), le_max_right Cb 0]
  cases infrared
  · -- infrared removed: multiply by `exp ‖H ω‖` on the closed cube
    let Eh : BilateralField d → ℝ := fun omega =>
      Real.exp ‖(H omega).restrict (closedCube z r hr : Set (SpatialCoordinates d))‖
    have hEint : Integrable Eh (chaosSampleLaw model).toMeasure := by
      have h := exp_norm_restrict_pow_integrable hd model H HI (closedCube z r hr) 1
      simpa only [Nat.cast_one, one_mul] using h
    have hEpos : ∀ omega, 0 < Eh omega := fun omega => Real.exp_pos _
    refine ⟨fun N omega => (|K N omega| + 1) * Eh omega,
      max 2 (2 * max Cb 0) + ∫ omega, Eh omega ∂(chaosSampleLaw model).toMeasure, 1 / 2,
      add_nonneg (by positivity) (integral_nonneg fun omega => (hEpos omega).le),
      by norm_num, fun N omega => mul_pos (by positivity) (hEpos omega), ?_, ?_⟩
    · intro N omega v
      have hle := sobolevCoefficientForm_mono
        (cutoffPositiveCoefficient model H omega N z hr)
        (scalePositiveCoefficient (Eh omega) (hEpos omega)
          (cutoffPositiveCoefficient model 0 omega N z hr))
        (by
          filter_upwards [aux_prop_as_response_bank_cauchy_coeff_infrared_le model H omega N z hr,
            scalePositiveCoefficient_coeFn (Eh omega) (hEpos omega)
              (cutoffPositiveCoefficient model 0 omega N z hr)] with x h1 h2
          rw [h2]
          exact h1)
        (v : SobolevData (centeredCube z r hr))
      rw [sobolevCoefficientForm_scale] at hle
      refine (hcoerH N omega v).trans ?_
      change (|K N omega| + 1) * sobolevCoefficientForm
          (cutoffPositiveCoefficient model H omega N z hr) _ _ ≤
        (|K N omega| + 1) * Eh omega * sobolevCoefficientForm
          (cutoffPositiveCoefficient model 0 omega N z hr) _ _
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hle (by positivity)
    · intro N t ht
      have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
      have hsub : {omega | t < (|K N omega| + 1) * Eh omega} ⊆
          {omega | Real.sqrt t < |K N omega| + 1} ∪ {omega | Real.sqrt t < Eh omega} := by
        intro omega homega
        by_contra hnot
        simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hnot
        have homega' : t < (|K N omega| + 1) * Eh omega := homega
        have hprod : (|K N omega| + 1) * Eh omega ≤ Real.sqrt t * Real.sqrt t :=
          mul_le_mul hnot.1 hnot.2 (hEpos omega).le hst.le
        rw [Real.mul_self_sqrt ht.le] at hprod
        linarith
      have h1 := htailH N _ hst
      have h2 := aux_prop_as_response_bank_cauchy_markov_integral (chaosSampleLaw model).toMeasure
        Eh (fun omega => (hEpos omega).le) hEint _ hst
      have hsq : (Real.sqrt t) ^ (-(1 : ℝ)) = t ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
        norm_num
      have hdiv : (∫ omega, Eh omega ∂(chaosSampleLaw model).toMeasure) / Real.sqrt t =
          (∫ omega, Eh omega ∂(chaosSampleLaw model).toMeasure) * t ^ (-(1 / 2 : ℝ)) := by
        rw [← hsq, Real.rpow_neg_one, div_eq_mul_inv]
      rw [hsq] at h1
      rw [hdiv] at h2
      have hint0 : 0 ≤ ∫ omega, Eh omega ∂(chaosSampleLaw model).toMeasure :=
        integral_nonneg fun omega => (hEpos omega).le
      have hA : 0 ≤ max 2 (2 * max Cb 0) * t ^ (-(1 / 2 : ℝ)) := by positivity
      have hB : 0 ≤ (∫ omega, Eh omega ∂(chaosSampleLaw model).toMeasure) *
          t ^ (-(1 / 2 : ℝ)) := by positivity
      calc (chaosSampleLaw model).toMeasure {omega | t < (|K N omega| + 1) * Eh omega}
          ≤ (chaosSampleLaw model).toMeasure {omega | Real.sqrt t < |K N omega| + 1} +
              (chaosSampleLaw model).toMeasure {omega | Real.sqrt t < Eh omega} :=
            (measure_mono hsub).trans (measure_union_le _ _)
        _ ≤ ENNReal.ofReal (max 2 (2 * max Cb 0) * t ^ (-(1 / 2 : ℝ))) +
              ENNReal.ofReal ((∫ omega, Eh omega ∂(chaosSampleLaw model).toMeasure) *
                t ^ (-(1 / 2 : ℝ))) := add_le_add h1 h2
        _ = ENNReal.ofReal ((max 2 (2 * max Cb 0) +
              ∫ omega, Eh omega ∂(chaosSampleLaw model).toMeasure) * t ^ (-(1 / 2 : ℝ))) := by
            rw [← ENNReal.ofReal_add hA hB]
            congr 1
            ring
  · exact ⟨fun N omega => |K N omega| + 1, max 2 (2 * max Cb 0), 1, by positivity, one_pos,
      fun N omega => by positivity, hcoerH, htailH⟩

end

section
open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

/-- The unit Neumann cube is the unit origin cube translated by its centre. -/
lemma aux_prop_as_response_bank_cauchy_unit_translate (d : ℕ) (h1 : (0 : ℝ) < 1) :
    (unitNeumannCube d : Set (SpatialCoordinates d)) =
      Homogenization.translateSet (fun _ : Fin d => (1 / 2 : ℝ))
        (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)) := by
  change Metric.ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2) =
    Homogenization.translateSet (fun _ : Fin d => (1 / 2 : ℝ))
      (Metric.ball (0 : SpatialCoordinates d) (1 / 2))
  ext x
  rw [Homogenization.mem_translateSet_iff_sub_mem]
  simp only [Metric.mem_ball]
  rw [dist_eq_norm, dist_eq_norm]
  simp

/-- Affine pullback of weak Sobolev data from any cube to the unit Neumann cube
`(0,1)^d`, along `y ↦ z + r (y - ½)`. -/
theorem aux_prop_as_response_bank_cauchy_unit_pullback
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (v : weakSobolevGraph (centeredCube z r hr)) :
    ∃ w : weakSobolevGraph (unitNeumannCube d),
      (∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
        (w : SobolevData (unitNeumannCube d)).1 x =
          (v : SobolevData (centeredCube z r hr)).1
            (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x)) ∧
      (∀ i : Fin d, ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
        ((w : SobolevData (unitNeumannCube d)).2 i : SpatialCoordinates d → ℝ) x =
          r * ((v : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
            (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x)) := by
  have h1 : (0 : ℝ) < 1 := one_pos
  obtain ⟨htranslate, hscale⟩ := aux_lane4_coercivity_dilation_cube_geometry d z r hr h1
  have hU := aux_prop_as_response_bank_cauchy_unit_translate d h1
  obtain ⟨u, hu, hgrad⟩ := exists_nativeH1Function_of_weakSobolevGraph v
  let c : SpatialCoordinates d := fun _ : Fin d => (1 / 2 : ℝ)
  let uT : Homogenization.H1Function
      (Homogenization.translateSet z
        (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d))) :=
    htranslate ▸ u
  let u0 : Homogenization.H1Function
      (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) :=
    Homogenization.H1Function.untranslate z uT
  let uR : Homogenization.H1Function
      (r • (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))) :=
    hscale ▸ u0
  let u1 : Homogenization.H1Function
      (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)) :=
    Homogenization.H1Function.unscale hr uR
  let uc : Homogenization.H1Function
      (Homogenization.translateSet c
        (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))) :=
    u1.translate c
  let uU : Homogenization.H1Function (unitNeumannCube d : Set (SpatialCoordinates d)) :=
    hU ▸ uc
  obtain ⟨w, hw, hwgrad⟩ := exists_weakSobolevGraph_of_nativeH1 (Om := unitNeumannCube d) uU
  have hcube : ∀ x : SpatialCoordinates d,
      r • (x - c) + z = cubeDilation z c r x := by
    intro x
    ext j
    simp [cubeDilation, c]
    ring
  refine ⟨w, ?_, ?_⟩
  · filter_upwards [hw] with x hx
    rw [hx]
    simp only [uU, uc, u1, uR, u0, uT,
      SubdiffusiveProcess.MeyersRegularity.cast_h1_toFun, Homogenization.H1Function.translate_toFun,
      Homogenization.H1Function.unscale_toFun, Homogenization.H1Function.untranslate_toFun]
    rw [hcube x]
    simpa only [c] using! congrFun hu (cubeDilation z c r x)
  · intro i
    filter_upwards [hwgrad i] with x hx
    rw [hx]
    have hUgrad : uU.grad x i = r * u.grad (r • (x - c) + z) i := by
      simp only [uU, uc, u1, uR, u0, uT, SubdiffusiveProcess.MeyersRegularity.cast_h1_grad,
        Homogenization.H1Function.translate_grad, Homogenization.H1Function.unscale_grad,
        Homogenization.H1Function.untranslate_grad, Pi.smul_apply, smul_eq_mul]
    rw [hUgrad, hcube x]
    exact congrArg (fun t => r * t) (congrFun (congrFun hgrad _) i)

end

section
open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

/-- Change of variables between a cube and the unit Neumann cube. -/
lemma aux_prop_as_response_bank_cauchy_unit_cov
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (g : SpatialCoordinates d → ℝ) :
    ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), g x =
      r ^ d * ∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)),
        g (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r y) := by
  have hmap := map_cubeDilation_restrict z (fun _ : Fin d => (1 / 2 : ℝ)) hr one_pos
  have hrd : 0 < r ^ d := pow_pos hr d
  have hQ : volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) =
      ENNReal.ofReal (r ^ d) • Measure.map (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r)
        (volume.restrict (centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
          Set (SpatialCoordinates d))) := by
    rw [hmap, smul_smul, ← ENNReal.ofReal_mul hrd.le, abs_of_pos (inv_pos.2 hrd),
      mul_inv_cancel₀ hrd.ne', ENNReal.ofReal_one, one_smul]
  rw [hQ, integral_smul_measure, ENNReal.toReal_ofReal hrd.le, smul_eq_mul]
  congr 1
  have hT : (⇑(cubeDilationEquiv z (fun _ : Fin d => (1 / 2 : ℝ)) hr.ne')) =
      cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r := rfl
  rw [← hT]
  exact (cubeDilationEquiv z _ hr.ne').measurableEmbedding.integral_map g

lemma aux_prop_as_response_bank_cauchy_volume_real_cube
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) = r ^ d := by
  rw [Measure.real, centeredCube_volume, ENNReal.toReal_ofReal (pow_pos hr d).le]

/-- The pullback has the same mean. -/
lemma aux_prop_as_response_bank_cauchy_unit_mean
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (f : DomainL2 (centeredCube z r hr)) (g : DomainL2 (unitNeumannCube d))
    (hfg : ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      g x = f (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x)) :
    domainMean g = domainMean f := by
  unfold domainMean
  have hU : volume.real (unitNeumannCube d : Set (SpatialCoordinates d)) = 1 := by
    rw [unitNeumannCube, aux_prop_as_response_bank_cauchy_volume_real_cube]
    simp
  rw [hU, aux_prop_as_response_bank_cauchy_volume_real_cube,
    aux_prop_as_response_bank_cauchy_unit_cov z r hr, integral_congr_ae hfg]
  have hrd : (r ^ d) ≠ 0 := (pow_pos hr d).ne'
  field_simp

lemma aux_prop_as_response_bank_cauchy_grad_apply {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (u : SobolevData Ω) (i : Fin d) : (sobolevGradient u) i = u.2 i := rfl

/-- The affine Neumann load scales by `r^{d-1}` under the pullback. -/
lemma aux_prop_as_response_bank_cauchy_unit_load
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (p : Fin d → ℝ)
    (v : weakSobolevGraph (centeredCube z r hr)) (w : weakSobolevGraph (unitNeumannCube d))
    (hgrad : ∀ i : Fin d, ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      ((w : SobolevData (unitNeumannCube d)).2 i : SpatialCoordinates d → ℝ) x =
        r * ((v : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
          (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x)) :
    affineNeumannLoad p (subspaceGradient (weakSobolevGraph (centeredCube z r hr)) v) =
      r ^ (d - 1) *
        affineNeumannLoad p (subspaceGradient (weakSobolevGraph (unitNeumannCube d)) w) := by
  rw [affineNeumannLoad_apply, affineNeumannLoad_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      p i * ((v : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ) x) =
    r ^ (d - 1) * ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
      p i * ((w : SobolevData (unitNeumannCube d)).2 i : SpatialCoordinates d → ℝ) x
  rw [aux_prop_as_response_bank_cauchy_unit_cov z r hr]
  have hcongr : (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)),
      p i * ((v : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
        (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r y)) =
      r⁻¹ * ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
        p i * ((w : SobolevData (unitNeumannCube d)).2 i : SpatialCoordinates d → ℝ) x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hgrad i] with x hx
    rw [hx]
    field_simp
  rw [hcongr]
  have hd1 : 1 ≤ d ∨ d = 0 := by omega
  rcases hd1 with hd1 | hd0
  · have : r ^ d = r ^ (d - 1) * r := by
      rw [← pow_succ, Nat.sub_add_cancel hd1]
    rw [this]
    field_simp
  · subst hd0
    exact Fin.elim0 i

/-- The `H^{3/4}` norm of the pulled-back mean-free part is controlled by that on the cube. -/
lemma aux_prop_as_response_bank_cauchy_unit_frac
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (f : DomainL2 (centeredCube z r hr)) (g : DomainL2 (unitNeumannCube d))
    (hfg : ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      g x = f (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x)) :
    cubeFractionalSqNorm hd (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder g ≤
      max (r ^ ((3 : ℝ) / 2)) 1 * cubeFractionalSqNorm hd z r hr threeQuarterOrder f := by
  have hsc := lane4_gagliardo_dilation_scaling d 1 hd z (fun _ : Fin d => (1 / 2 : ℝ)) r hr
    one_pos threeQuarterOrder (fun _ => f) (fun _ => g) (fun _ => hfg)
  obtain ⟨hsemi, hl2⟩ := hsc
  unfold cubeFractionalSqNorm cubeFractionalVecSqNorm cubeFractionalVecSeminormSq
  set SQ := cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => f)
  set SU := cubeFractionalL2Seminorm hd (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos
    threeQuarterOrder (fun _ : Fin 1 => g)
  have hthree : ((threeQuarterOrder : Set.Ioo (0 : ℝ) 1) : ℝ) = 3 / 4 := rfl
  have hreal : SQ.toReal ^ 2 = r ^ (-(2 * (3 / 4 : ℝ))) * SU.toReal ^ 2 := by
    have := congrArg ENNReal.toReal hsemi
    rw [hthree] at this
    simpa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal
      (Real.rpow_nonneg hr.le _)] using this
  have hpos : 0 < r ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hr _
  have hU : SU.toReal ^ 2 = r ^ ((3 : ℝ) / 2) * SQ.toReal ^ 2 := by
    rw [hreal, ← mul_assoc, ← Real.rpow_add hr]
    norm_num
  change SU.toReal ^ 2 + (∑ _i : Fin 1, ‖g‖ ^ 2) /
      volume.real (centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
        Set (SpatialCoordinates d)) ≤ _
  have hl2' : (∑ _i : Fin 1, ‖f‖ ^ 2) /
      volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) =
      (∑ _i : Fin 1, ‖g‖ ^ 2) /
        volume.real (centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
          Set (SpatialCoordinates d)) := by
    simpa only using! hl2
  rw [← hl2', hU]
  have hA : 0 ≤ SQ.toReal ^ 2 := sq_nonneg _
  have hB : 0 ≤ (∑ _i : Fin 1, ‖f‖ ^ 2) /
      volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    apply div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) measureReal_nonneg
  have h1 : r ^ ((3 : ℝ) / 2) * SQ.toReal ^ 2 ≤ max (r ^ ((3 : ℝ) / 2)) 1 * SQ.toReal ^ 2 :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hA
  have h2 : (∑ _i : Fin 1, ‖f‖ ^ 2) /
      volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
      max (r ^ ((3 : ℝ) / 2)) 1 * ((∑ _i : Fin 1, ‖f‖ ^ 2) /
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    le_mul_of_one_le_left hB (le_max_right _ _)
  rw [mul_add]
  linarith

end

section
open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

/-- A smooth unit-mass bump supported in `(1,2)`, as `eq:mfd-bump` requires. -/
lemma aux_prop_as_response_bank_cauchy_bump :
    ∃ rho : ℝ → ℝ, ContDiff ℝ ∞ rho ∧ (∀ tau, 0 ≤ rho tau) ∧
      (∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) ∧ (∫ tau, rho tau) = 1 ∧
      Continuous rho ∧ ∃ Mρ : ℝ, 0 ≤ Mρ ∧ ∀ tau, |rho tau| ≤ Mρ := by
  let f : ContDiffBump (3 / 2 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let rho : ℝ → ℝ := f.normed volume
  have hcont : Continuous rho := f.continuous_normed
  have hsupp : ∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0 := by
    intro tau htau
    have hball : Metric.ball (3 / 2 : ℝ) f.rOut = Set.Ioo 1 2 := by
      rw [Real.ball_eq_Ioo]
      norm_num [f]
    by_contra hne
    have hmem : tau ∈ Function.support rho := hne
    rw [show Function.support rho = Metric.ball (3 / 2 : ℝ) f.rOut from
      f.support_normed_eq, hball] at hmem
    exact htau hmem
  have hcs : HasCompactSupport rho := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 2)) ?_
    intro tau htau
    exact hsupp tau (fun h => htau ⟨h.1.le, h.2.le⟩)
  obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support hcs
  refine ⟨rho, f.contDiff_normed (n := ⊤), fun tau => f.nonneg_normed tau, hsupp,
    f.integral_normed, hcont, max M 0, le_max_right _ _, fun tau => ?_⟩
  rw [← Real.norm_eq_abs]
  exact (hM tau).trans (le_max_left _ _)

lemma aux_prop_as_response_bank_cauchy_faceBump_continuous {d : ℕ} (rho : ℝ → ℝ)
    (hrho : Continuous rho) (p : Fin d → ℝ) (eps : ℝ) : Continuous (faceBump rho p eps) := by
  unfold faceBump
  apply continuous_finsetSum
  intro i _
  apply continuous_const.mul
  apply Continuous.sub
  · exact continuous_const.mul (hrho.comp
      ((continuous_const.sub (continuous_apply i)).div_const _))
  · exact continuous_const.mul (hrho.comp ((continuous_apply i).div_const _))

lemma aux_prop_as_response_bank_cauchy_faceBump_bound {d : ℕ} (rho : ℝ → ℝ) (Mρ : ℝ)
    (hM : ∀ tau, |rho tau| ≤ Mρ) (p : Fin d → ℝ) (eps : ℝ) (x : SpatialCoordinates d) :
    |faceBump rho p eps x| ≤ (2 * Mρ * ∑ i : Fin d, |p i|) * |eps⁻¹| := by
  unfold faceBump
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul]
  have h1 : |eps⁻¹ * rho ((1 - x i) / eps) - eps⁻¹ * rho (x i / eps)| ≤ 2 * Mρ * |eps⁻¹| := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul]
    have ha := hM ((1 - x i) / eps)
    have hb := hM (x i / eps)
    have he := abs_nonneg eps⁻¹
    nlinarith
  calc |p i| * |eps⁻¹ * rho ((1 - x i) / eps) - eps⁻¹ * rho (x i / eps)|
      ≤ |p i| * (2 * Mρ * |eps⁻¹|) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = 2 * Mρ * |p i| * |eps⁻¹| := by ring

/-- Each face-bump summand integrates to zero on `(0,1)^d`. -/
lemma aux_prop_as_response_bank_cauchy_faceBump_mean {d : ℕ} (rho : ℝ → ℝ)
    (hrho : Continuous rho) (Mρ : ℝ) (hM : ∀ tau, |rho tau| ≤ Mρ) (p : Fin d → ℝ)
    (eps : ℝ) :
    (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), faceBump rho p eps x) = 0 := by
  have hfin : IsFiniteMeasure (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) :=
    inferInstance
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ → ℝ, A = fun t => eps⁻¹ * rho ((1 - t) / eps) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ → ℝ, B = fun t => eps⁻¹ * rho (t / eps) := ⟨_, rfl⟩
  have hAcont : Continuous A := by
    rw [hAdef]
    exact continuous_const.mul (hrho.comp ((continuous_const.sub continuous_id).div_const _))
  have hBcont : Continuous B := by
    rw [hBdef]
    exact continuous_const.mul (hrho.comp (continuous_id.div_const _))
  have hbdd : ∀ (g : ℝ → ℝ), (∀ t, |g t| ≤ Mρ * |eps⁻¹|) → Continuous g → ∀ i : Fin d,
      Integrable (fun x : SpatialCoordinates d => g (x i))
        (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) := by
    intro g hg hgc i
    refine Integrable.of_bound (C := Mρ * |eps⁻¹|)
      ((hgc.comp (continuous_apply i)).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs]
    exact hg (x i)
  have hA : ∀ t, |A t| ≤ Mρ * |eps⁻¹| := fun t => by
    simp only [hAdef, abs_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
  have hB : ∀ t, |B t| ≤ Mρ * |eps⁻¹| := fun t => by
    simp only [hBdef, abs_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
  have hrefl : (∫ t in Set.Ioo (0 : ℝ) 1, A t) = ∫ t in Set.Ioo (0 : ℝ) 1, B t := by
    rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_of_le zero_le_one]
    have := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1) B 1
    simp only [sub_zero, sub_self] at this
    rw [← this, hAdef, hBdef]
  have hsum : (fun x : SpatialCoordinates d => faceBump rho p eps x) =
      fun x => ∑ i : Fin d, (p i * A (x i) - p i * B (x i)) := by
    funext x
    unfold faceBump
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hAdef, hBdef]
    ring
  rw [hsum, integral_finsetSum (s := Finset.univ)
    (f := fun i (x : SpatialCoordinates d) => p i * A (x i) - p i * B (x i)) (fun i _ =>
    ((hbdd A hA hAcont i).const_mul (p i)).sub ((hbdd B hB hBcont i).const_mul (p i)))]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_sub ((hbdd A hA hAcont i).const_mul (p i)) ((hbdd B hB hBcont i).const_mul (p i)),
    integral_const_mul (p i) (fun x : SpatialCoordinates d => A (x i)),
    integral_const_mul (p i) (fun x : SpatialCoordinates d => B (x i)),
    aux_lem_load_integral_coord i A, aux_lem_load_integral_coord i B, hrefl, sub_self]

end

section
open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

/-- Null sets of a cube pull back to null sets of the unit Neumann cube. -/
lemma aux_prop_as_response_bank_cauchy_unit_ae_comp
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) {P : SpatialCoordinates d → Prop}
    (h : ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), P y) :
    ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      P (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x) := by
  have hmap := map_cubeDilation_restrict z (fun _ : Fin d => (1 / 2 : ℝ)) hr one_pos
  have hmeas : AEMeasurable (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r)
      (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) :=
    (continuous_cubeDilation _ _ _).measurable.aemeasurable
  apply ae_of_ae_map hmeas
  change ∀ᵐ y ∂(Measure.map (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r)
    (volume.restrict (centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
      Set (SpatialCoordinates d)))), P y
  rw [hmap]
  exact Measure.ae_smul_measure h _

lemma aux_prop_as_response_bank_cauchy_unit_inv
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (y : SpatialCoordinates d) :
    cubeDilation (fun _ : Fin d => (1 / 2 : ℝ)) z r⁻¹
      (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r y) = y :=
  (cubeDilationEquiv z (fun _ : Fin d => (1 / 2 : ℝ)) hr.ne').left_inv y

/-- The mean-free parts correspond under the pullback. -/
lemma aux_prop_as_response_bank_cauchy_unit_meanfree
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (v : weakSobolevGraph (centeredCube z r hr)) (w : weakSobolevGraph (unitNeumannCube d))
    (hw1 : ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      (w : SobolevData (unitNeumannCube d)).1 x =
        (v : SobolevData (centeredCube z r hr)).1
          (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x)) :
    ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      ((w : SobolevData (unitNeumannCube d)).1 -
          domainConstantL2 (domainMean (w : SobolevData (unitNeumannCube d)).1) :
            DomainL2 (unitNeumannCube d)) x =
        ((v : SobolevData (centeredCube z r hr)).1 -
          domainConstantL2 (domainMean (v : SobolevData (centeredCube z r hr)).1) :
            DomainL2 (centeredCube z r hr))
          (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x) := by
  have hmean := aux_prop_as_response_bank_cauchy_unit_mean z r hr
    (v : SobolevData (centeredCube z r hr)).1 (w : SobolevData (unitNeumannCube d)).1 hw1
  have hfae : ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      ((v : SobolevData (centeredCube z r hr)).1 -
          domainConstantL2 (domainMean (v : SobolevData (centeredCube z r hr)).1) :
            DomainL2 (centeredCube z r hr)) y =
        (v : SobolevData (centeredCube z r hr)).1 y -
          domainMean (v : SobolevData (centeredCube z r hr)).1 := by
    filter_upwards [Lp.coeFn_sub (v : SobolevData (centeredCube z r hr)).1
        (domainConstantL2 (domainMean (v : SobolevData (centeredCube z r hr)).1)),
      domainConstantL2_coeFn (Ω := centeredCube z r hr)
        (domainMean (v : SobolevData (centeredCube z r hr)).1)] with y h1 h2
    rw [h1, Pi.sub_apply, h2]
  filter_upwards [aux_prop_as_response_bank_cauchy_unit_ae_comp z r hr hfae, hw1,
    Lp.coeFn_sub (w : SobolevData (unitNeumannCube d)).1
      (domainConstantL2 (domainMean (w : SobolevData (unitNeumannCube d)).1)),
    domainConstantL2_coeFn (Ω := unitNeumannCube d)
      (domainMean (w : SobolevData (unitNeumannCube d)).1)] with x h1 h2 h3 h4
  rw [h3, Pi.sub_apply, h4, h1, h2, hmean]

/-- The transported smoothed load integrates against the pullback. -/
lemma aux_prop_as_response_bank_cauchy_unit_smoothed
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : ℝ) (G : SpatialCoordinates d → ℝ)
    (f : DomainL2 (centeredCube z r hr))
    (hf : (f : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        fun x => (s / r) * G (cubeDilation (fun _ : Fin d => (1 / 2 : ℝ)) z r⁻¹ x))
    (v : weakSobolevGraph (centeredCube z r hr)) (w : weakSobolevGraph (unitNeumannCube d))
    (hw1 : ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      (w : SobolevData (unitNeumannCube d)).1 x =
        (v : SobolevData (centeredCube z r hr)).1
          (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x)) :
    (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        (f : SpatialCoordinates d → ℝ) x * (v : SobolevData (centeredCube z r hr)).1 x) =
      s * r ^ (d - 1) * ∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)),
        G y * (w : SobolevData (unitNeumannCube d)).1 y := by
  have hc1 : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      (f : SpatialCoordinates d → ℝ) x * (v : SobolevData (centeredCube z r hr)).1 x) =
      ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        (s / r) * G (cubeDilation (fun _ : Fin d => (1 / 2 : ℝ)) z r⁻¹ x) *
          (v : SobolevData (centeredCube z r hr)).1 x := by
    apply integral_congr_ae
    filter_upwards [hf] with x hx
    rw [hx]
  rw [hc1, aux_prop_as_response_bank_cauchy_unit_cov z r hr]
  have hc2 : (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)),
      (s / r) * G (cubeDilation (fun _ : Fin d => (1 / 2 : ℝ)) z r⁻¹
          (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r y)) *
        (v : SobolevData (centeredCube z r hr)).1
          (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r y)) =
      (s / r) * ∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)),
        G y * (w : SobolevData (unitNeumannCube d)).1 y := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hw1] with y hy
    rw [aux_prop_as_response_bank_cauchy_unit_inv z r hr, hy]
    ring
  rw [hc2]
  have hd1 : 1 ≤ d := by omega
  have hrd : r ^ d = r ^ (d - 1) * r := by
    rw [← pow_succ, Nat.sub_add_cancel hd1]
  rw [hrd]
  field_simp

/-- The load-approximation input holds on every cube: `lem_load` on `(0,1)^d` transported by
dilation and translation, with a normalized slope. -/
theorem aux_prop_as_response_bank_cauchy_loadApprox_holds
    (d : ℕ) (hd : 2 ≤ d) (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd) :
    aux_prop_as_response_bank_cauchy_loadApprox d hd := by
  have hlem0 := lem_load d hd Sf
  obtain ⟨C, hC, hlem⟩ := hlem0
  have hb := aux_prop_as_response_bank_cauchy_bump
  obtain ⟨rho, hsmooth, hnn, hsupp, hint, hcont, Mρ, hMρ, hM⟩ := hb
  intro z r hr _ p
  by_cases hp : p = 0
  · subst hp
    refine ⟨fun _ => 0, 0, 0, le_rfl, le_rfl, ?_, ?_, ?_⟩
    · intro h _ _
      filter_upwards [Lp.coeFn_zero ℝ 2
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))] with x hx
      rw [hx]
      simp
    · intro h _ _
      rw [integral_congr_ae (Lp.coeFn_zero ℝ 2
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))]
      simp
    · intro h _ _ v
      have h0 : affineNeumannLoad (0 : Fin d → ℝ)
          (subspaceGradient (weakSobolevGraph (centeredCube z r hr)) v) = 0 := by
        rw [affineNeumannLoad_apply]
        simp
      have h1 : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ((0 : DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ) x *
            (v : SobolevData (centeredCube z r hr)).1 x) = 0 := by
        rw [integral_congr_ae (g := fun _ => (0 : ℝ))]
        · simp
        · filter_upwards [Lp.coeFn_zero ℝ 2
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))] with x hx
          rw [hx]
          simp
      rw [h0, h1, sub_zero, abs_zero]
      simp
  -- normalized slope
  have hss : 0 < ∑ i : Fin d, (p i) ^ 2 := by
    by_contra hle
    push Not at hle
    apply hp
    funext i
    have hi : (p i) ^ 2 ≤ 0 := by
      have := Finset.single_le_sum (f := fun j => (p j) ^ 2) (fun j _ => sq_nonneg (p j))
        (Finset.mem_univ i)
      linarith
    have := sq_nonneg (p i)
    have : (p i) ^ 2 = 0 := le_antisymm hi this
    simpa using this
  set s : ℝ := Real.sqrt (∑ i : Fin d, (p i) ^ 2) with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 hss
  let ph : Fin d → ℝ := fun i => p i / s
  have hph : ∑ i : Fin d, (ph i) ^ 2 = 1 := by
    simp only [ph, div_pow]
    rw [← Finset.sum_div, Real.sq_sqrt hss.le, div_self hss.ne']
  have hpph : ∀ i, p i = s * ph i := fun i => by
    simp only [ph]
    field_simp
  -- the transported smoothed load
  let F : ℝ → SpatialCoordinates d → ℝ := fun h x =>
    (s / r) * faceBump rho ph h (cubeDilation (fun _ : Fin d => (1 / 2 : ℝ)) z r⁻¹ x)
  have hFcont : ∀ h, Continuous (F h) := fun h =>
    continuous_const.mul ((aux_prop_as_response_bank_cauchy_faceBump_continuous rho hcont ph h).comp
      (continuous_cubeDilation _ _ _))
  have hFbd : ∀ h x, |F h x| ≤ (s / r) * ((2 * Mρ * ∑ i : Fin d, |ph i|) * |h⁻¹|) := by
    intro h x
    simp only [F, abs_mul]
    rw [abs_of_pos (div_pos hs hr)]
    exact mul_le_mul_of_nonneg_left
      (aux_prop_as_response_bank_cauchy_faceBump_bound rho Mρ hM ph h _) (div_pos hs hr).le
  have hFmem : ∀ h, MemLp (F h) 2
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := fun h =>
    MemLp.of_bound (hFcont h).aestronglyMeasurable _ (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hFbd h x)
  let fh : ℝ → DomainL2 (centeredCube z r hr) := fun h => (hFmem h).toLp (F h)
  have hfh : ∀ h, (fh h : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] F h :=
    fun h => (hFmem h).coeFn_toLp
  have hsumabs : 0 ≤ ∑ i : Fin d, |ph i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hmaxpos : 0 ≤ max (r ^ ((3 : ℝ) / 2)) 1 := le_trans zero_le_one (le_max_right _ _)
  refine ⟨fh, (s / r) * (2 * Mρ * ∑ i : Fin d, |ph i|),
    s * r ^ (d - 1) * C * Real.sqrt (max (r ^ ((3 : ℝ) / 2)) 1),
    by positivity, by positivity, ?_, ?_, ?_⟩
  · -- the `O(1/h)` bound
    intro h hh _
    filter_upwards [hfh h] with x hx
    rw [hx]
    refine (hFbd h x).trans (le_of_eq ?_)
    rw [abs_inv, abs_of_pos hh]
    field_simp
  · -- mean zero
    intro h _ _
    rw [integral_congr_ae (hfh h), aux_prop_as_response_bank_cauchy_unit_cov z r hr]
    simp only [F, aux_prop_as_response_bank_cauchy_unit_inv z r hr]
    rw [integral_const_mul, aux_prop_as_response_bank_cauchy_faceBump_mean rho hcont Mρ hM ph h]
    simp
  · -- the load estimate
    intro h hh hh8 v
    have hpb := aux_prop_as_response_bank_cauchy_unit_pullback d z r hr v
    obtain ⟨w, hw1, hw2⟩ := hpb
    have hLoad := aux_prop_as_response_bank_cauchy_unit_load z r hr p v w hw2
    have hLp : affineNeumannLoad p (subspaceGradient (weakSobolevGraph (unitNeumannCube d)) w) =
        s * affineNeumannLoad ph (subspaceGradient (weakSobolevGraph (unitNeumannCube d)) w) := by
      rw [affineNeumannLoad_apply, affineNeumannLoad_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_const_mul]
      congr 1
      funext x
      rw [hpph i]
      ring
    have hsm := aux_prop_as_response_bank_cauchy_unit_smoothed hd z r hr s (faceBump rho ph h)
      (fh h) (hfh h) v w hw1
    have hfg := aux_prop_as_response_bank_cauchy_unit_meanfree z r hr v w hw1
    have hfrac := aux_prop_as_response_bank_cauchy_unit_frac hd z r hr _ _ hfg
    have hlemw := hlem rho hsmooth hnn hsupp hint ph hph h hh hh8 w
    -- combine
    rw [hsm, hLoad, hLp]
    have hkey : r ^ (d - 1) * (s * affineNeumannLoad ph
          (subspaceGradient (weakSobolevGraph (unitNeumannCube d)) w)) -
        s * r ^ (d - 1) * ∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)),
          faceBump rho ph h y * (w : SobolevData (unitNeumannCube d)).1 y =
        s * r ^ (d - 1) * (affineNeumannLoad ph
          (subspaceGradient (weakSobolevGraph (unitNeumannCube d)) w) -
          ∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)),
            faceBump rho ph h y * (w : SobolevData (unitNeumannCube d)).1 y) := by ring
    rw [hkey, abs_mul, abs_of_pos (mul_pos hs (pow_pos hr _))]
    have hsqrt := Real.sqrt_le_sqrt hfrac
    rw [Real.sqrt_mul hmaxpos] at hsqrt
    have hh4 : 0 ≤ h ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hh.le _
    have hsr : 0 ≤ s * r ^ (d - 1) := (mul_pos hs (pow_pos hr _)).le
    have hstep := mul_le_mul_of_nonneg_left hlemw hsr
    have hstep2 := mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hsr (mul_nonneg hC.le hh4))
    refine hstep.trans (le_trans (le_of_eq (by ring)) (hstep2.trans (le_of_eq (by ring))))

end

section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

/-- Coarse coercivity with a fixed polynomial tail on triadic cubes of side `> 1`,
for both infrared conventions. The proof below derives it from unit-cube coercivity
by an upward scale shift. -/
def aux_prop_as_response_bank_cauchy_coercivityLarge (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] : Prop :=
  ∃ deltaK : ℝ, 0 < deltaK ∧
    ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (_Rm : in_responses d model)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ))
      (_HI : InfraredCharacterization model H),
      model.delta ≤ min 1 deltaK →
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), (∃ j : ℤ, r = (3 : ℝ) ^ j) → 1 < r →
    ∀ infrared : Bool,
    ∃ (K : ℕ → BilateralField d → ℝ) (B p0 : ℝ), 0 ≤ B ∧ 0 < p0 ∧
      (∀ N omega, 0 < K N omega) ∧
      (∀ N omega (v : meanZeroSobolevGraph (centeredCube z r hr)),
        cubeFractionalSqNorm hd z r hr threeQuarterOrder
            (v : SobolevData (centeredCube z r hr)).1 ≤
          K N omega * sobolevCoefficientForm
            (cutoffPositiveCoefficient model (if infrared then H else
              (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega N z hr)
            (v : SobolevData (centeredCube z r hr)) (v : SobolevData (centeredCube z r hr))) ∧
      (∀ N (t : ℝ), 0 < t →
        (chaosSampleLaw model).toMeasure {omega | t < K N omega} ≤
          ENNReal.ofReal (B * t ^ (-p0)))

/-- The coercivity input on all triadic cubes: `lem_coercivity` for sides `≤ 1`, the typed
input for sides `> 1`. -/
theorem aux_prop_as_response_bank_cauchy_coercivityTail_of_large
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (hK : aux_prop_as_response_bank_cauchy_coercivityLarge d hd) :
    aux_prop_as_response_bank_cauchy_coercivityTailOn d hd (fun _ => True) := by
  have hS0 := aux_prop_as_response_bank_cauchy_coercivity_small_cube d hd Jc Pc Sf
  obtain ⟨dS, hdS, hS⟩ := hS0
  obtain ⟨dL, hdL, hL⟩ := hK
  refine ⟨min dS dL, lt_min hdS hdL, ?_⟩
  intro model Rm H HI hsmall z r hr htri _ infrared
  by_cases hr1 : r ≤ 1
  · exact hS model Rm H HI
      (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))) z r hr hr1 infrared
  · exact hL model Rm H HI (hsmall.trans (min_le_min_left _ (min_le_right _ _))) z r hr htri
      (lt_of_not_ge hr1) infrared

/-- The coercivity input on the triadic cubes of side `≤ 1`, from `lem_coercivity` and the
infrared exponential moments. -/
theorem aux_prop_as_response_bank_cauchy_coercivityTail_le_one
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd) :
    aux_prop_as_response_bank_cauchy_coercivityTailOn d hd (fun r => r ≤ 1) := by
  have hS0 := aux_prop_as_response_bank_cauchy_coercivity_small_cube d hd Jc Pc Sf
  obtain ⟨dS, hdS, hS⟩ := hS0
  refine ⟨dS, hdS, ?_⟩
  intro model Rm H HI hsmall z r hr _ hr1 infrared
  exact hS model Rm H HI (hsmall.trans (min_le_right _ _)) z r hr hr1 infrared

/-- **Bounded branch, unconditional apart from open upstream nodes:** the principal's full
conclusion (all eight branches, all three clauses) on every triadic cube of side `≤ 1`, the
range of `mfd:lem-coercivity`. The text is the frozen conclusion with `r ≤ 1 →` added after
the triadic hypothesis. -/
theorem aux_prop_as_response_bank_cauchy_side_le_one
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 Cgeom : ℝ, 0 < delta0 ∧ 0 < Cgeom ∧
      ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : in_responses d model) (Sreg : in_6_16 d model) (_It : in_iteration d model Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_HI : InfraredCharacterization model H)
        (_hdelta : model.delta ≤ min 1 delta0),
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (_htriadic : ∃ j : ℤ, r = (3 : ℝ) ^ j),
      r ≤ 1 →
      let Q := centeredCube z r hr
      let _closedQ := closedCube z r hr
      ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
        ‖(u : SobolevData Q).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph Q) u‖),
      ∀ (hP0 : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph Q,
        ‖(u : SobolevData Q).1‖ ≤
          K * ‖subspaceGradient (meanZeroSobolevGraph Q) u‖),
      ∀ (phi : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ phi →
      ∀ (b : weakSobolevGraph Q),
        ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (Q : Set (SpatialCoordinates d))] phi →
      ∀ (fD fN : DomainL2 Q) (KD KN : ℝ),
        0 ≤ KD → 0 ≤ KN →
        (∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
          |(fD : SpatialCoordinates d → ℝ) x| ≤ KD) →
        (∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
          |(fN : SpatialCoordinates d → ℝ) x| ≤ KN) →
        (∫ x in (Q : Set (SpatialCoordinates d)),
          (fN : SpatialCoordinates d → ℝ) x) = 0 →
      ∀ (p : Fin d → ℝ),
      let SD := killedResponseSpace hP
      let SN := meanZeroResponseSpace hP0
      let Rsp : Bool → Fin 4 → ℕ → BilateralField d → ℝ :=
        fun infrared i N omega =>
          let Hused := if infrared then H else
            (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
          let a : ℕ → BilateralField d → PositiveCoefficient Q :=
            fun N omega => cutoffPositiveCoefficient model Hused omega N z hr
          match i.val with
          | 0 => dirichletResponse SD (a N omega) b
          | 1 => inverseResponse SD (a N omega)
              ((sobolevVolumeLoad fD).comp SD.space.subtypeL)
          | 2 => inverseResponse SN (a N omega)
              ((sobolevVolumeLoad fN).comp SN.space.subtypeL)
          | _ => affineInverseNeumannResponse hP0 (a N omega) p
      let P : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure
      (∀ (infrared : Bool) (i : Fin 4) (N : ℕ),
        ∀ᵐ omega ∂P, 0 ≤ Rsp infrared i N omega) ∧
      (∀ (eps : ℝ), 0 < eps →
        ∃ Ceps ceps : ℝ, ∃ N0 : ℕ,
          0 < Ceps ∧ 0 < ceps ∧
          ∀ N : ℕ, N0 ≤ N →
            ∃ M0 : ℕ, N ≤ M0 ∧
              ∀ M : ℕ, M0 ≤ M →
                ∀ (infrared : Bool) (i : Fin 4),
                  P {omega |
                      |Rsp infrared i N omega - Rsp infrared i M omega| >
                        Cgeom * eps * Rsp infrared i N omega +
                          Ceps * (3 : ℝ) ^ (-(ceps * (N : ℝ)))} ≤
                    ENNReal.ofReal (Ceps * (3 : ℝ) ^
                      (-(ceps * (N : ℝ))))) ∧
      (∀ (infrared : Bool) (i : Fin 4) (tolerance probability : ℝ),
        0 < tolerance → 0 < probability →
        ∃ J : ℕ, ∀ M M' : ℕ, J ≤ M → J ≤ M' →
          P {omega |
              tolerance < |Rsp infrared i M omega - Rsp infrared i M' omega|} ≤
            ENNReal.ofReal probability) :=
  aux_prop_as_response_bank_cauchy_of_affineTailOn d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp (fun r => r ≤ 1)
    (aux_prop_as_response_bank_cauchy_affineTail_of_inputsOn d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp (fun r => r ≤ 1)
      (aux_prop_as_response_bank_cauchy_loadApprox_holds d hd Sf)
      (aux_prop_as_response_bank_cauchy_coercivityTail_le_one d hd Jc Pc Sf))

/-- The principal conclusion, exactly as frozen, from the single typed input
`aux_prop_as_response_bank_cauchy_coercivityLarge` (coercivity on cubes of side `> 1`). -/
theorem aux_prop_as_response_bank_cauchy_of_coercivityLarge
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (hK : aux_prop_as_response_bank_cauchy_coercivityLarge d hd) :
    ∃ delta0 Cgeom : ℝ, 0 < delta0 ∧ 0 < Cgeom ∧
      ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : in_responses d model) (Sreg : in_6_16 d model) (_It : in_iteration d model Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_HI : InfraredCharacterization model H)
        (_hdelta : model.delta ≤ min 1 delta0),
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (_htriadic : ∃ j : ℤ, r = (3 : ℝ) ^ j),
      let Q := centeredCube z r hr
      let _closedQ := closedCube z r hr
      ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
        ‖(u : SobolevData Q).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph Q) u‖),
      ∀ (hP0 : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph Q,
        ‖(u : SobolevData Q).1‖ ≤
          K * ‖subspaceGradient (meanZeroSobolevGraph Q) u‖),
      ∀ (phi : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ phi →
      ∀ (b : weakSobolevGraph Q),
        ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (Q : Set (SpatialCoordinates d))] phi →
      ∀ (fD fN : DomainL2 Q) (KD KN : ℝ),
        0 ≤ KD → 0 ≤ KN →
        (∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
          |(fD : SpatialCoordinates d → ℝ) x| ≤ KD) →
        (∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
          |(fN : SpatialCoordinates d → ℝ) x| ≤ KN) →
        (∫ x in (Q : Set (SpatialCoordinates d)),
          (fN : SpatialCoordinates d → ℝ) x) = 0 →
      ∀ (p : Fin d → ℝ),
      let SD := killedResponseSpace hP
      let SN := meanZeroResponseSpace hP0
      let Rsp : Bool → Fin 4 → ℕ → BilateralField d → ℝ :=
        fun infrared i N omega =>
          let Hused := if infrared then H else
            (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
          let a : ℕ → BilateralField d → PositiveCoefficient Q :=
            fun N omega => cutoffPositiveCoefficient model Hused omega N z hr
          match i.val with
          | 0 => dirichletResponse SD (a N omega) b
          | 1 => inverseResponse SD (a N omega)
              ((sobolevVolumeLoad fD).comp SD.space.subtypeL)
          | 2 => inverseResponse SN (a N omega)
              ((sobolevVolumeLoad fN).comp SN.space.subtypeL)
          | _ => affineInverseNeumannResponse hP0 (a N omega) p
      let P : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure
      (∀ (infrared : Bool) (i : Fin 4) (N : ℕ),
        ∀ᵐ omega ∂P, 0 ≤ Rsp infrared i N omega) ∧
      (∀ (eps : ℝ), 0 < eps →
        ∃ Ceps ceps : ℝ, ∃ N0 : ℕ,
          0 < Ceps ∧ 0 < ceps ∧
          ∀ N : ℕ, N0 ≤ N →
            ∃ M0 : ℕ, N ≤ M0 ∧
              ∀ M : ℕ, M0 ≤ M →
                ∀ (infrared : Bool) (i : Fin 4),
                  P {omega |
                      |Rsp infrared i N omega - Rsp infrared i M omega| >
                        Cgeom * eps * Rsp infrared i N omega +
                          Ceps * (3 : ℝ) ^ (-(ceps * (N : ℝ)))} ≤
                    ENNReal.ofReal (Ceps * (3 : ℝ) ^
                      (-(ceps * (N : ℝ))))) ∧
      (∀ (infrared : Bool) (i : Fin 4) (tolerance probability : ℝ),
        0 < tolerance → 0 < probability →
        ∃ J : ℕ, ∀ M M' : ℕ, J ≤ M → J ≤ M' →
          P {omega |
              tolerance < |Rsp infrared i M omega - Rsp infrared i M' omega|} ≤
            ENNReal.ofReal probability) := by
  have h := aux_prop_as_response_bank_cauchy_of_affineTailOn d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp (fun _ => True)
    (aux_prop_as_response_bank_cauchy_affineTail_of_inputsOn d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp (fun _ => True)
      (aux_prop_as_response_bank_cauchy_loadApprox_holds d hd Sf)
      (aux_prop_as_response_bank_cauchy_coercivityTail_of_large d hd Jc Pc Sf hK))
  obtain ⟨delta0, Cgeom, h0, h1, h2⟩ := h
  exact ⟨delta0, Cgeom, h0, h1, fun model Rm Sreg It H HI hdelta z r hr htriadic =>
    h2 model Rm Sreg It H HI hdelta z r hr htriadic trivial⟩

end

section
open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators

/-- The chart from the unit cube to a cube of side `3^k`. -/
def aux_large_cube_upMap {d : ℕ} (k : ℕ) (z : SpatialCoordinates d) :
    C(SpatialCoordinates d, SpatialCoordinates d) :=
  ⟨fun y => z + (3 : ℝ) ^ k • y,
    (by fun_prop)⟩

theorem aux_large_cube_upMap_apply {d : ℕ} (k : ℕ)
    (z y : SpatialCoordinates d) :
    aux_large_cube_upMap k z y = z + (3 : ℝ) ^ k • y := rfl

/-- Upward scale shift: read layer `j+k` in the large-cube chart. -/
def aux_large_cube_upShift {d : ℕ} (k : ℕ) (z : SpatialCoordinates d)
    (omega : BilateralField d) : BilateralField d :=
  fun j => (omega (j + k)).comp (aux_large_cube_upMap k z)

theorem aux_large_cube_upShift_apply {d : ℕ} (k : ℕ)
    (z y : SpatialCoordinates d) (omega : BilateralField d) (j : ℤ) :
    aux_large_cube_upShift k z omega j y = omega (j + k) (z + (3 : ℝ) ^ k • y) := rfl

theorem aux_large_cube_upShift_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (k : ℕ) (z : SpatialCoordinates d) :
    Measurable (aux_large_cube_upShift (d := d) k z) := by
  have hc : Measurable fun f : C(SpatialCoordinates d, ℝ) =>
      f.comp (aux_large_cube_upMap k z) := by fun_prop
  exact Measurable.of_eval fun j => hc.comp (measurable_pi_apply (j + k))

theorem aux_large_cube_upShift_downShift {d : ℕ} (k : ℕ)
    (z : SpatialCoordinates d) (omega : BilateralField d) :
    aux_large_cube_upShift k z
      (aux_lem_as_coarse_shallow_grid_scaleShift k (-((3 : ℝ) ^ (-(k : ℤ))) • z)
        omega) = omega := by
  funext j
  ext y
  simp only [aux_large_cube_upShift, aux_lem_as_coarse_shallow_grid_scaleShift,
    ContinuousMap.comp_apply, add_sub_cancel_right]
  congr 1
  ext i
  simp only [aux_lem_as_coarse_shallow_grid_cellMap, ContinuousMap.coe_mk,
    cubeDilation_apply, aux_large_cube_upMap, Pi.add_apply, Pi.smul_apply,
    Pi.zero_apply, sub_zero, smul_eq_mul, _root_.zpow_neg, zpow_natCast]
  rw [mul_add, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero k (by norm_num : (3 : ℝ) ≠ 0))]
  ring

/-- The upward shift preserves the same field law, by inversion of the downward shift. -/
theorem aux_large_cube_upShift_measurePreserving {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ) (z : SpatialCoordinates d) :
    MeasurePreserving (aux_large_cube_upShift k z)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure := by
  let down := aux_lem_as_coarse_shallow_grid_scaleShift k
    (-((3 : ℝ) ^ (-(k : ℤ))) • z)
  have hd : MeasurePreserving down (chaosSampleLaw M).toMeasure
      (chaosSampleLaw M).toMeasure :=
    lem_as_coarse_shallow_grid_scale_shift M k _
  have hcomp : aux_large_cube_upShift k z ∘ down = id := by
    funext omega
    exact aux_large_cube_upShift_downShift k z omega
  refine ⟨aux_large_cube_upShift_measurable k z, ?_⟩
  calc
    Measure.map (aux_large_cube_upShift k z) (chaosSampleLaw M).toMeasure =
        Measure.map (aux_large_cube_upShift k z)
          (Measure.map down (chaosSampleLaw M).toMeasure) := by rw [hd.map_eq]
    _ = Measure.map (aux_large_cube_upShift k z ∘ down) (chaosSampleLaw M).toMeasure :=
      Measure.map_map (aux_large_cube_upShift_measurable k z) hd.measurable
    _ = (chaosSampleLaw M).toMeasure := by rw [hcomp, Measure.map_id]

/-- Transfer an arbitrary event through the upward shift, without a measurability premise. -/
theorem aux_large_cube_upShift_prob_le {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ) (z : SpatialCoordinates d)
    (S : Set (BilateralField d)) :
    (chaosSampleLaw M).toMeasure (aux_large_cube_upShift k z ⁻¹' S) ≤
      (chaosSampleLaw M).toMeasure S := by
  set P := (chaosSampleLaw M).toMeasure
  calc
    P (aux_large_cube_upShift k z ⁻¹' S) ≤
        P (aux_large_cube_upShift k z ⁻¹' toMeasurable P S) :=
      measure_mono (Set.preimage_mono (subset_toMeasurable P S))
    _ = P (toMeasurable P S) :=
      (aux_large_cube_upShift_measurePreserving M k z).measure_preimage
        (measurableSet_toMeasurable P S).nullMeasurableSet
    _ = P S := measure_toMeasurable S

theorem aux_large_cube_upShift_fine_sum {d : ℕ} (N k : ℕ)
    (z y : SpatialCoordinates d) (omega : BilateralField d) :
    (∑ j ∈ Finset.range (N + k + 1), aux_large_cube_upShift k z omega (-(j : ℤ)) y) =
      (∑ a ∈ Finset.range k, omega ((a : ℤ) + 1) (aux_large_cube_upMap k z y)) +
        ∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) (aux_large_cube_upMap k z y) := by
  simp only [aux_large_cube_upShift, ContinuousMap.comp_apply]
  rw [show N + k + 1 = k + (N + 1) by omega, Finset.sum_range_add]
  congr 1
  · calc
      (∑ j ∈ Finset.range k, omega (-(j : ℤ) + k) (aux_large_cube_upMap k z y)) =
          ∑ j ∈ Finset.range k,
            omega (((k - 1 - j : ℕ) : ℤ) + 1) (aux_large_cube_upMap k z y) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjk := Finset.mem_range.mp hj
        congr 2
        omega
      _ = _ := Finset.sum_range_reflect
        (fun a => omega ((a : ℤ) + 1) (aux_large_cube_upMap k z y)) k
  · apply Finset.sum_congr rfl
    intro j hj
    congr 2
    push_cast
    ring

/-- Exact coefficient factorization into the old cutoff and the `k` new coarse layers. -/
theorem aux_large_cube_upShift_cutoff_factor {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N k : ℕ)
    (z y : SpatialCoordinates d) (omega : BilateralField d) :
    cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
        (aux_large_cube_upShift k z omega) (N + k) y =
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N / SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + k)) *
        Real.exp ((∑ a ∈ Finset.range k,
          omega ((a : ℤ) + 1) (aux_large_cube_upMap k z y)) -
          (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
        cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
          omega N (aux_large_cube_upMap k z y) := by
  have hsplit := aux_large_cube_upShift_fine_sum N k z y omega
  have hposN : SubdiffusiveProcess.CoarseGrainingVocab.ahom M N ≠ 0 :=
    ne_of_gt (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)
  simp only [cutoffCoefficient, cutoffPotential, ContinuousMap.zero_apply, zero_add,
    Int.ofNat_eq_natCast, hsplit, Nat.cast_add]
  rw [show (∑ a ∈ Finset.range k, omega ((a : ℤ) + 1) (aux_large_cube_upMap k z y)) +
      (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) (aux_large_cube_upMap k z y)) -
      ((N : ℝ) + k + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P =
      ((∑ a ∈ Finset.range k, omega ((a : ℤ) + 1) (aux_large_cube_upMap k z y)) -
        (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) +
      ((∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) (aux_large_cube_upMap k z y)) -
        ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) by ring,
    Real.exp_add]
  field_simp

/-- The annealed ordering controls the change in the cutoff normalizer. -/
theorem aux_large_cube_ahom_ratio_le {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M) (N k : ℕ) :
    SubdiffusiveProcess.CoarseGrainingVocab.ahom M N / SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + k) ≤
      Real.exp (2 * ((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) := by
  by_cases hk : k = 0
  · simp only [hk, Nat.add_zero, Nat.cast_zero, zero_mul, mul_zero, Real.exp_zero]
    rw [div_self (ne_of_gt (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N))]
  · have hNk : N < N + k := Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hk)
    have hord := (Rm.ahom_ordering N (N + k) hNk).2
    apply (div_le_iff₀ (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N + k))).2
    have he : 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P *
        (((N + k : ℕ) : ℝ) - (N : ℝ)) =
        2 * ((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
      push_cast
      ring
    rw [he] at hord
    exact hord

private theorem aux_large_cube_exp_factor_le {r s b t : ℝ}
    (hr : r ≤ Real.exp (2 * t)) (hs : s ≤ b) :
    r * Real.exp (s - t) ≤ Real.exp (t + b) := by
  calc
    r * Real.exp (s - t) ≤ Real.exp (2 * t) * Real.exp (s - t) :=
      mul_le_mul_of_nonneg_right hr (Real.exp_nonneg _)
    _ = Real.exp (t + s) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (t + b) := Real.exp_le_exp.mpr (add_le_add le_rfl hs)

/-- A compact restriction norm bounds the extra coarse layers uniformly in the old cutoff. -/
theorem aux_large_cube_upShift_cutoff_le {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M) (N k : ℕ)
    (z y : SpatialCoordinates d) (omega : BilateralField d)
    (K : Compacts (SpatialCoordinates d)) (hy : aux_large_cube_upMap k z y ∈ K) :
    cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
        (aux_large_cube_upShift k z omega) (N + k) y ≤
      Real.exp ((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
        ∑ a ∈ Finset.range k, ‖(omega ((a : ℤ) + 1)).restrict
          (K : Set (SpatialCoordinates d))‖) *
        cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
          omega N (aux_large_cube_upMap k z y) := by
  have hsum : (∑ a ∈ Finset.range k, omega ((a : ℤ) + 1) (aux_large_cube_upMap k z y)) ≤
      ∑ a ∈ Finset.range k,
        ‖(omega ((a : ℤ) + 1)).restrict (K : Set (SpatialCoordinates d))‖ := by
    apply Finset.sum_le_sum
    intro a ha
    exact (le_abs_self _).trans (by
      simpa only [ContinuousMap.restrict_apply, Real.norm_eq_abs] using
        ((omega ((a : ℤ) + 1)).restrict (K : Set (SpatialCoordinates d))).norm_coe_le_norm
          ⟨aux_large_cube_upMap k z y, hy⟩)
  rw [aux_large_cube_upShift_cutoff_factor]
  apply mul_le_mul_of_nonneg_right
    (aux_large_cube_exp_factor_le (aux_large_cube_ahom_ratio_le M Rm N k) hsum)
  exact mul_nonneg (inv_nonneg.mpr (le_of_lt (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)))
    (Real.exp_nonneg _)

end

section
open MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators

/-- For an expanding cube chart, the normalized fractional square norm decreases. -/
theorem aux_large_cube_fractional_le_unit
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (hr1 : 1 ≤ r)
    (f : DomainL2 (centeredCube z r hr))
    (g : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (hfg : ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      g x = f (cubeDilation z 0 r x)) :
    cubeFractionalSqNorm hd z r hr threeQuarterOrder f ≤
      cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos threeQuarterOrder g := by
  have hsc := lane4_gagliardo_dilation_scaling d 1 hd z 0 r hr one_pos
    threeQuarterOrder (fun _ => f) (fun _ => g) (fun _ => hfg)
  obtain ⟨hsemi, hl2⟩ := hsc
  have hR : r ^ (-(2 * (threeQuarterOrder : ℝ))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hr1 (by
      change -(2 * (3 / 4 : ℝ)) ≤ 0
      norm_num)
  have hreal := congrArg ENNReal.toReal hsemi
  simp only [ENNReal.toReal_pow, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hr.le _)] at hreal
  unfold cubeFractionalSqNorm cubeFractionalVecSqNorm cubeFractionalVecSeminormSq
  rw [hreal, hl2]
  exact add_le_add (mul_le_of_le_one_left (sq_nonneg _) hR) le_rfl

/-- A pointwise comparison with a coercive unit-cube coefficient transports to every
larger cube. The deterministic prefactor is allowed to depend on the fixed cube. -/
theorem aux_large_cube_coercivity_transport
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (hr1 : 1 ≤ r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (K F : ℝ) (hK : 0 ≤ K)
    (hb : ∀ w : meanZeroSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos threeQuarterOrder
        (w : SobolevData _).1 ≤ K * sobolevCoefficientForm b (w : SobolevData _) w)
    (hcoeff : ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      b.val x ≤ F * a.val (cubeDilation z 0 r x)) :
    ∀ v : meanZeroSobolevGraph (centeredCube z r hr),
      cubeFractionalSqNorm hd z r hr threeQuarterOrder (v : SobolevData _).1 ≤
        (K * F * (r ^ ((d : ℝ) - 2))⁻¹) *
          sobolevCoefficientForm a (v : SobolevData _) v := by
  obtain ⟨c, hc⟩ := lane4_dilation_coefficient_transport d z 0 r hr one_pos a
  intro v
  obtain ⟨w, hwval, hwgrad⟩ :=
    aux_lane4_coercivity_dilation_meanZero_pullback d z r hr one_pos v
  have hnorm := aux_large_cube_fractional_le_unit hd z r hr hr1
    (v : SobolevData _).1 (w : SobolevData _).1 hwval
  have henergy := aux_lane4_coercivity_dilation_energy_scaling d z r hr one_pos a c
    (v : SobolevData _) (w : SobolevData _) hc hwval hwgrad
  have hcmp : sobolevCoefficientForm b (w : SobolevData _) w ≤
      F * sobolevCoefficientForm c (w : SobolevData _) w := by
    apply weightedGradientForm_le_mul
    filter_upwards [hcoeff, hc] with x hx hcx
    rw [hcx]
    exact hx
  have hpow : r ^ ((d : ℝ) - 2) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  calc
    cubeFractionalSqNorm hd z r hr threeQuarterOrder (v : SobolevData _).1
        ≤ cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos threeQuarterOrder
          (w : SobolevData _).1 := hnorm
    _ ≤ K * sobolevCoefficientForm b (w : SobolevData _) w := hb w
    _ ≤ K * (F * sobolevCoefficientForm c (w : SobolevData _) w) :=
      mul_le_mul_of_nonneg_left hcmp hK
    _ = (K * F * (r ^ ((d : ℝ) - 2))⁻¹) * sobolevCoefficientForm a (v : SobolevData _) v := by
      rw [henergy]
      field_simp

end

section
open MeasureTheory Set TopologicalSpace ProbabilityTheory
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators

theorem aux_large_cube_exp_memLp_two
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ)
    (hX : Measurable X) (t : ℝ)
    (hI : Integrable (fun w => Real.exp ((2 * t) * X w)) μ) :
    MemLp (fun w => Real.exp (t * X w)) 2 μ := by
  apply (memLp_two_iff_integrable_sq (hX.const_mul t |>.exp.aestronglyMeasurable)).2
  convert hI using 1
  funext w
  rw [← Real.exp_nat_mul]
  congr 1
  norm_num
  ring

/-- Finite sums preserve all nonnegative exponential moments; no independence is needed. -/
theorem aux_large_cube_exp_sum_integrable
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : Finset ι) (X : ι → Ω → ℝ)
    (hXm : ∀ i ∈ S, Measurable (X i))
    (hXI : ∀ i ∈ S, ∀ t : ℝ, 0 ≤ t → Integrable (fun w => Real.exp (t * X i w)) μ) :
    ∀ t : ℝ, 0 ≤ t → Integrable (fun w => Real.exp (t * ∑ i ∈ S, X i w)) μ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro t _
      simpa only [Finset.sum_empty, mul_zero, Real.exp_zero] using
        (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ)
  | @insert i S hi ih =>
      intro t ht
      have him : Measurable (X i) := hXm i (Finset.mem_insert_self _ _)
      have hSm : Measurable (fun w => ∑ j ∈ S, X j w) :=
        Finset.measurable_sum _ fun j hj => hXm j (Finset.mem_insert_of_mem hj)
      have hII := hXI i (Finset.mem_insert_self _ _) (2 * t) (by positivity)
      have hSI := ih (fun j hj => hXm j (Finset.mem_insert_of_mem hj))
        (fun j hj => hXI j (Finset.mem_insert_of_mem hj)) (2 * t) (by positivity)
      have hprod := (aux_large_cube_exp_memLp_two μ (X i) him t hII).integrable_mul
        (aux_large_cube_exp_memLp_two μ (fun w => ∑ j ∈ S, X j w) hSm t hSI)
      convert hprod using 1
      funext w
      rw [Finset.sum_insert hi, mul_add, Real.exp_add]
      rfl

/-- A fixed compact restriction of a native root field has all exponential norm moments.
This uses a finite cover by translates of the standing `g2` observable. -/
theorem aux_large_cube_root_exp_norm_integrable
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (K : Compacts (SpatialCoordinates d))
    (D : C(SpatialCoordinates d, SpatialCoordinates d)) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
      Real.exp (t * ‖(g.1.1.comp D).restrict (K : Set (SpatialCoordinates d))‖))
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
  classical
  obtain ⟨S, hS⟩ := (K.isCompact.image D.continuous).elim_finite_subcover
    (fun z : SpatialCoordinates d => Metric.ball z (1 / 2 : ℝ))
    (fun _ => Metric.isOpen_ball) (by
      intro x hx
      exact mem_iUnion.2 ⟨x, Metric.mem_ball_self (by norm_num)⟩)
  let X : SpatialCoordinates d → _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ :=
    fun z g => _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
      (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g)
  have hXm : ∀ z, Measurable (X z) := fun z =>
    _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_measurable.comp
      (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate z)
  have hX0 : ∀ z g, 0 ≤ X z g := fun z g =>
    _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _
  have hXI : ∀ z, ∀ q : ℝ, 0 ≤ q → Integrable
      (fun g => Real.exp (q * X z g))
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
    intro z q hq
    have hT : MeasurePreserving (_root_.SubdiffusiveProcess.Model.PotentialField.translate z)
        (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
        (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure :=
      ⟨_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate z, M.G1.stationary z⟩
    have hI := (aux_finite_cutoff_log_abs_majorant_exp_of_ogamma
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
      _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
      _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_measurable
      _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg
      M.delta q M.shellPrefix.delta_pos hq M.G2.regularity_expectation).1
    exact hT.integrable_comp_of_integrable hI
  have hbound : ∀ g : _root_.SubdiffusiveProcess.Model.PotentialField d,
      ‖(g.1.1.comp D).restrict (K : Set (SpatialCoordinates d))‖ ≤ ∑ z ∈ S, X z g := by
    intro g
    apply (ContinuousMap.norm_le _ (Finset.sum_nonneg fun z _ => hX0 z g)).2
    intro x
    obtain ⟨z, hzS, hzx⟩ : ∃ z, ∃ (_ : z ∈ S), D x ∈ Metric.ball z (1 / 2 : ℝ) := by
      simpa only [mem_iUnion] using hS (mem_image_of_mem D x.2)
    have hmem : (D x - z) ∈ Homogenization.openCubeSet (Homogenization.originCube d 0) := by
      rw [← Homogenization.ball_cubeCenter_eq_openCubeSet]
      have hc : Homogenization.cubeCenter (Homogenization.originCube d 0) =
          (0 : SpatialCoordinates d) := by
        ext i
        simp [Homogenization.cubeCenter, Homogenization.originCube]
      have hr : Homogenization.cubeRadius (Homogenization.originCube d 0) = (1 / 2 : ℝ) := by
        unfold Homogenization.cubeRadius
        rw [Homogenization.cubeScaleFactor_eq_one_of_scale_eq_zero rfl, mul_one]
      rw [hc, hr]
      simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hzx
    have hx := _root_.SubdiffusiveProcess.Model.PotentialField.abs_apply_le_g2Observable
      (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g) hmem
    simp only [_root_.SubdiffusiveProcess.Model.PotentialField.translate_apply, sub_add_cancel] at hx
    change ‖g (D x)‖ ≤ _
    rw [Real.norm_eq_abs]
    exact hx.trans (Finset.single_le_sum (fun y _ => hX0 y g) hzS)
  have hI := aux_large_cube_exp_sum_integrable
    (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure S X
    (fun z _ => hXm z) (fun z _ => hXI z) t ht
  have hm : Measurable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
      Real.exp (t * ‖(g.1.1.comp D).restrict (K : Set (SpatialCoordinates d))‖)) := by
    have hc : Continuous (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d => g.1.1.comp D) := by
      fun_prop
    exact (Real.continuous_exp.comp (continuous_const.mul
      (continuous_norm.comp ((ContinuousMap.continuous_restrict _).comp hc)))).measurable
  apply hI.mono' hm.aestronglyMeasurable
  filter_upwards with g
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hbound g) ht)

end

section
open MeasureTheory Set TopologicalSpace ProbabilityTheory
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators

theorem aux_large_cube_layer_norm_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (j : ℤ) (K : Compacts (SpatialCoordinates d)) :
    Measurable (fun omega : BilateralField d =>
      ‖(omega j).restrict (K : Set (SpatialCoordinates d))‖) :=
  (continuous_norm.comp (ContinuousMap.continuous_restrict
    (K : Set (SpatialCoordinates d)))).measurable.comp (measurable_pi_apply j)

/-- Every actual bilateral layer has all compact exponential norm moments. -/
theorem aux_large_cube_layer_exp_norm_integrable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℤ)
    (K : Compacts (SpatialCoordinates d)) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun omega : BilateralField d =>
      Real.exp (t * ‖(omega j).restrict (K : Set (SpatialCoordinates d))‖))
      (chaosSampleLaw M).toMeasure := by
  let D : C(SpatialCoordinates d, SpatialCoordinates d) :=
    ⟨fun x => (3 : ℝ) ^ (-j) • x, (by fun_prop)⟩
  let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let F : C(SpatialCoordinates d, ℝ) → ℝ := fun f =>
    Real.exp (t * ‖f.restrict (K : Set (SpatialCoordinates d))‖)
  have hF : Measurable F :=
    (Real.continuous_exp.comp (continuous_const.mul
      (continuous_norm.comp (ContinuousMap.continuous_restrict
        (K : Set (SpatialCoordinates d)))))).measurable
  have hroot : Integrable (fun f : C(SpatialCoordinates d, ℝ) => F (layerScaling d j f))
      (chaosRootFieldLaw M).toMeasure := by
    change Integrable (fun f : C(SpatialCoordinates d, ℝ) => F (layerScaling d j f))
      (Measure.map forget (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)
    apply (integrable_map_measure
      (hF.comp (layerScaling d j).continuous.measurable).aestronglyMeasurable
      forget.continuous.measurable.aemeasurable).2
    exact aux_large_cube_root_exp_norm_integrable M K D t ht
  have hlayer : Integrable F (scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure := by
    change Integrable F (Measure.map (layerScaling d j) (chaosRootFieldLaw M).toMeasure)
    exact (integrable_map_measure hF.aestronglyMeasurable
      (layerScaling d j).continuous.measurable.aemeasurable).2 hroot
  exact (measurePreserving_eval_infinitePi
    (fun i : ℤ => (scaledLayerLaw d (chaosRootFieldLaw M) i).toMeasure) j).integrable_comp_of_integrable
      hlayer

/-- The finitely many coarse layers added by an upward shift have every exponential
moment on a fixed compact set. -/
theorem aux_large_cube_coarse_exp_norm_integrable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ)
    (K : Compacts (SpatialCoordinates d)) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun omega : BilateralField d =>
      Real.exp (t * ∑ a ∈ Finset.range k,
        ‖(omega ((a : ℤ) + 1)).restrict (K : Set (SpatialCoordinates d))‖))
      (chaosSampleLaw M).toMeasure := by
  exact aux_large_cube_exp_sum_integrable (chaosSampleLaw M).toMeasure (Finset.range k)
    (fun a omega => ‖(omega ((a : ℤ) + 1)).restrict (K : Set (SpatialCoordinates d))‖)
    (fun a _ => aux_large_cube_layer_norm_measurable ((a : ℤ) + 1) K)
    (fun a _ q hq => aux_large_cube_layer_exp_norm_integrable M ((a : ℤ) + 1) K q hq) t ht

end

section
open MeasureTheory Set TopologicalSpace ProbabilityTheory
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators

theorem aux_large_cube_upMap_eq {d : ℕ} (k : ℕ) (z : SpatialCoordinates d) :
    (aux_large_cube_upMap k z : SpatialCoordinates d → SpatialCoordinates d) =
      cubeDilation z 0 ((3 : ℝ) ^ k) := by
  funext y i
  simp only [aux_large_cube_upMap, ContinuousMap.coe_mk, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, cubeDilation_apply, Pi.zero_apply, sub_zero]

theorem aux_large_cube_cutoff_positive_coe
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N : ℕ) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    (fun x => (cutoffPositiveCoefficient M H omega N z hr).val x) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      cutoffCoefficient M H omega N := by
  have : Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closedCube z r hr) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  have hval := normalizedContinuousPositiveCoefficient_coeFn
    (Ω := centeredCube z r hr) (closedCube z r hr) (cutoffCoefficientCM M H omega N z hr)
    (cutoffCoefficientCM_pos M H omega N z hr) 1 one_pos
  filter_upwards [hval, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet]
    with x hx hxQ
  simpa only [cutoffPositiveCoefficient, cutoffCoefficientCM, ContinuousMap.coe_mk,
    div_one] using hx hxQ

theorem aux_large_cube_cutoff_infrared_mul
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N : ℕ) (x : SpatialCoordinates d) :
    cutoffCoefficient M H omega N x = Real.exp (H omega x) *
      cutoffCoefficient M (fun _ => 0) omega N x := by
  simp only [cutoffCoefficient, cutoffPotential, ContinuousMap.zero_apply, zero_add,
    Int.ofNat_eq_natCast]
  rw [show H omega x + (∑ j ∈ Finset.range (N + 1), omega (-↑j) x) -
      (N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P =
    H omega x + ((∑ j ∈ Finset.range (N + 1), omega (-↑j) x) -
      (N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) by ring, Real.exp_add]
  ring

/-- The finite factor used to compare a large cube with its scale-shifted unit cube. -/
def aux_large_cube_environment_factor
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (k : ℕ) (z : SpatialCoordinates d) (hr : 0 < (3 : ℝ) ^ k)
    (omega : BilateralField d) : ℝ :=
  Real.exp ((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
    (∑ a ∈ Finset.range k,
      ‖(omega ((a : ℤ) + 1)).restrict
        (closedCube z ((3 : ℝ) ^ k) hr : Set (SpatialCoordinates d))‖) +
    ‖(H (aux_large_cube_upShift k z omega)).restrict
      (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))‖ +
    ‖(H omega).restrict
      (closedCube z ((3 : ℝ) ^ k) hr : Set (SpatialCoordinates d))‖)

theorem aux_large_cube_environment_factor_pos
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (k : ℕ) (z : SpatialCoordinates d) (hr : 0 < (3 : ℝ) ^ k)
    (omega : BilateralField d) :
    0 < aux_large_cube_environment_factor M H k z hr omega := Real.exp_pos _

theorem aux_large_cube_coefficients_le
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (k : ℕ) (z : SpatialCoordinates d) (hr : 0 < (3 : ℝ) ^ k)
    (infrared : Bool) (N : ℕ) (omega : BilateralField d) :
    ∀ᵐ y ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H (aux_large_cube_upShift k z omega) (N + k) 0 one_pos).val y ≤
        aux_large_cube_environment_factor M H k z hr omega *
          (cutoffPositiveCoefficient M (if infrared then H else 0) omega N z hr).val
            (cubeDilation z 0 ((3 : ℝ) ^ k) y) := by
  have hq := lane4_dilation_quasi_measure_preserving d z 0 ((3 : ℝ) ^ k) hr one_pos
  filter_upwards [aux_large_cube_cutoff_positive_coe M H
      (aux_large_cube_upShift k z omega) (N + k) 0 one_pos,
    hq.ae (aux_large_cube_cutoff_positive_coe M (if infrared then H else 0) omega N z hr),
    ae_restrict_mem (centeredCube (0 : SpatialCoordinates d) 1 one_pos).isOpen.measurableSet]
    with y hyunit hybig hy
  rw [hyunit, hybig]
  have hyeq := congrFun (aux_large_cube_upMap_eq k z) y
  rw [← hyeq]
  have hyK := centeredCube_subset_closedCube (0 : SpatialCoordinates d) one_pos hy
  have hxK : aux_large_cube_upMap k z y ∈
      (closedCube z ((3 : ℝ) ^ k) hr : Set (SpatialCoordinates d)) := by
    rw [hyeq]
    exact centeredCube_subset_closedCube z hr (cubeDilation_mapsTo z 0 hr one_pos y hy)
  have hcoarse := aux_large_cube_upShift_cutoff_le M Rm N k z y omega
    (closedCube z ((3 : ℝ) ^ k) hr) hxK
  have hu : H (aux_large_cube_upShift k z omega) y ≤
      ‖(H (aux_large_cube_upShift k z omega)).restrict
        (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))‖ := by
    exact (le_abs_self _).trans (ContinuousMap.norm_coe_le_norm
      ((H (aux_large_cube_upShift k z omega)).restrict
        (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) ⟨y, hyK⟩)
  have hb : -((if infrared then H else 0) omega (aux_large_cube_upMap k z y)) ≤
      ‖(H omega).restrict
        (closedCube z ((3 : ℝ) ^ k) hr : Set (SpatialCoordinates d))‖ := by
    cases infrared
    · simpa only [Bool.false_eq_true, ↓reduceIte, Pi.zero_apply,
        ContinuousMap.zero_apply, neg_zero] using
        norm_nonneg ((H omega).restrict
          (closedCube z ((3 : ℝ) ^ k) hr : Set (SpatialCoordinates d)))
    · exact (neg_le_abs _).trans (ContinuousMap.norm_coe_le_norm
        ((H omega).restrict (closedCube z ((3 : ℝ) ^ k) hr : Set (SpatialCoordinates d)))
          ⟨aux_large_cube_upMap k z y, hxK⟩)
  have hremove : cutoffCoefficient M (fun _ => 0) omega N (aux_large_cube_upMap k z y) =
      Real.exp (-((if infrared then H else 0) omega (aux_large_cube_upMap k z y))) *
        cutoffCoefficient M (if infrared then H else 0) omega N (aux_large_cube_upMap k z y) := by
    rw [aux_large_cube_cutoff_infrared_mul M (if infrared then H else 0), ← mul_assoc,
      ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  rw [aux_large_cube_cutoff_infrared_mul M H]
  refine (mul_le_mul_of_nonneg_left hcoarse (Real.exp_pos _).le).trans ?_
  rw [hremove]
  have hpos : 0 ≤ cutoffCoefficient M (if infrared then H else 0) omega N
      (aux_large_cube_upMap k z y) :=
    (mul_pos (inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)).le
  rw [← mul_assoc, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_right _ hpos
  apply Real.exp_le_exp.2
  linarith only [hu, hb]

end

section
open MeasureTheory Set TopologicalSpace ProbabilityTheory
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators

private theorem aux_large_cube_exp_add_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X Y : Ω → ℝ) (hXm : Measurable X) (hYm : Measurable Y)
    (hXI : ∀ t : ℝ, 0 ≤ t → Integrable (fun w => Real.exp (t * X w)) μ)
    (hYI : ∀ t : ℝ, 0 ≤ t → Integrable (fun w => Real.exp (t * Y w)) μ)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun w => Real.exp (t * (X w + Y w))) μ := by
  have h2t : 0 ≤ 2 * t := mul_nonneg (by norm_num) ht
  have hprod := (aux_large_cube_exp_memLp_two μ X hXm t (hXI (2 * t) h2t)).integrable_mul
    (aux_large_cube_exp_memLp_two μ Y hYm t (hYI (2 * t) h2t))
  simpa only [mul_add, Real.exp_add, Pi.mul_apply] using! hprod

/-- The comparison factor is measurable for the given measurable infrared version. -/
theorem aux_large_cube_environment_factor_measurable
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H)
    (k : ℕ) (z : SpatialCoordinates d) (hr : 0 < (3 : ℝ) ^ k) :
    Measurable (aux_large_cube_environment_factor M H k z hr) := by
  unfold aux_large_cube_environment_factor
  apply Measurable.exp
  refine ((measurable_const.add ?_).add ?_).add ?_
  · exact Finset.measurable_sum _ fun a _ =>
      aux_large_cube_layer_norm_measurable ((a : ℤ) + 1) (closedCube z ((3 : ℝ) ^ k) hr)
  · exact (continuous_norm.comp (ContinuousMap.continuous_restrict _)).measurable.comp
      (HI.1.comp (aux_large_cube_upShift_measurable k z))
  · exact (continuous_norm.comp (ContinuousMap.continuous_restrict _)).measurable.comp HI.1

/-- The large-cube comparison factor is integrable, with no small-disorder requirement. -/
theorem aux_large_cube_environment_factor_integrable
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H)
    (k : ℕ) (z : SpatialCoordinates d) (hr : 0 < (3 : ℝ) ^ k) :
    Integrable (aux_large_cube_environment_factor M H k z hr)
      (chaosSampleLaw M).toMeasure := by
  let Kbig := closedCube z ((3 : ℝ) ^ k) hr
  let Kunit := closedCube (0 : SpatialCoordinates d) 1 one_pos
  let S : BilateralField d → ℝ := fun omega =>
    ∑ a ∈ Finset.range k, ‖(omega ((a : ℤ) + 1)).restrict
      (Kbig : Set (SpatialCoordinates d))‖
  let U : BilateralField d → ℝ := fun omega =>
    ‖(H (aux_large_cube_upShift k z omega)).restrict
      (Kunit : Set (SpatialCoordinates d))‖
  let B : BilateralField d → ℝ := fun omega =>
    ‖(H omega).restrict (Kbig : Set (SpatialCoordinates d))‖
  have hSm : Measurable S := Finset.measurable_sum _ fun a _ =>
    aux_large_cube_layer_norm_measurable ((a : ℤ) + 1) Kbig
  have hUm : Measurable U :=
    (continuous_norm.comp (ContinuousMap.continuous_restrict _)).measurable.comp
      (HI.1.comp (aux_large_cube_upShift_measurable k z))
  have hBm : Measurable B :=
    (continuous_norm.comp (ContinuousMap.continuous_restrict _)).measurable.comp HI.1
  have hSI : ∀ t : ℝ, 0 ≤ t → Integrable (fun w => Real.exp (t * S w))
      (chaosSampleLaw M).toMeasure :=
    fun t ht => aux_large_cube_coarse_exp_norm_integrable M k Kbig t ht
  have hUI : ∀ t : ℝ, 0 ≤ t → Integrable (fun w => Real.exp (t * U w))
      (chaosSampleLaw M).toMeasure := by
    intro t ht
    exact (aux_large_cube_upShift_measurePreserving M k z).integrable_comp_of_integrable
      (exists_compactExponentialMoment_of_infraredCharacterization hd M H HI Kunit t ht)
  have hBI : ∀ t : ℝ, 0 ≤ t → Integrable (fun w => Real.exp (t * B w))
      (chaosSampleLaw M).toMeasure :=
    fun t ht => exists_compactExponentialMoment_of_infraredCharacterization hd M H HI Kbig t ht
  have hSU := aux_large_cube_exp_add_integrable
    (chaosSampleLaw M).toMeasure S U hSm hUm hSI hUI
  have hSum := aux_large_cube_exp_add_integrable (chaosSampleLaw M).toMeasure
    (fun w => S w + U w) B (hSm.add hUm) hBm hSU hBI 1 zero_le_one
  have hfactor := hSum.const_mul (Real.exp ((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))
  change Integrable (fun w => Real.exp
    ((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P + S w + U w + B w))
      (chaosSampleLaw M).toMeasure
  simpa only [one_mul, add_assoc, Real.exp_add, mul_assoc] using hfactor

end

section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators

theorem aux_large_cube_abs_add_one_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (Cb : ℝ) (hm : AEStronglyMeasurable X P)
    (hb : eLpNorm X (ENNReal.ofReal 1) P ≤ ENNReal.ofReal Cb)
    (t : ℝ) (ht : 0 < t) :
    P {omega | t < |X omega| + 1} ≤
      ENNReal.ofReal (max 2 (2 * max Cb 0) * t ^ (-(1 : ℝ))) := by
  rw [Real.rpow_neg_one]
  by_cases ht2 : t ≤ 2
  · refine (prob_le_one).trans ?_
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    rw [← div_eq_mul_inv, le_div_iff₀ ht]
    linarith only [ht2, le_max_left 2 (2 * max Cb 0)]
  · have ht2' : 2 < t := lt_of_not_ge ht2
    have hbd : eLpNorm X (ENNReal.ofReal 1) P ≤ ENNReal.ofReal (max Cb 0) :=
      hb.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    have hmk := aux_prop_as_response_bank_cauchy_markov_abs P X
      1 (max Cb 0) (t / 2) one_pos (le_max_right _ _) (by positivity) hm hbd
    refine le_trans (measure_mono ?_) (hmk.trans (ENNReal.ofReal_le_ofReal ?_))
    · intro omega homega
      change t < |X omega| + 1 at homega
      change t / 2 < |X omega|
      linarith only [homega, ht2']
    · rw [Real.rpow_one, div_div_eq_mul_div, ← div_eq_mul_inv]
      apply div_le_div_of_nonneg_right _ ht.le
      nlinarith only [le_max_right 2 (2 * max Cb 0)]

/-- A first-moment factor times a variable with a first-order tail has a half-order tail. -/
theorem aux_large_cube_product_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X F : Ω → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hF0 : ∀ omega, 0 ≤ F omega) (hFI : Integrable F P)
    (hX : ∀ t : ℝ, 0 < t → P {omega | t < X omega} ≤
      ENNReal.ofReal (B * t ^ (-(1 : ℝ)))) :
    ∀ t : ℝ, 0 < t → P {omega | t < X omega * F omega} ≤
      ENNReal.ofReal ((B + ∫ omega, F omega ∂P) * t ^ (-(1 / 2 : ℝ))) := by
  intro t ht
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hsub : {omega | t < X omega * F omega} ⊆
      {omega | Real.sqrt t < X omega} ∪ {omega | Real.sqrt t < F omega} := by
    intro omega homega
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hnot
    have hprod : X omega * F omega ≤ Real.sqrt t * Real.sqrt t :=
      mul_le_mul hnot.1 hnot.2 (hF0 omega) hst.le
    rw [Real.mul_self_sqrt ht.le] at hprod
    exact (not_lt_of_ge hprod) homega
  have h1 := hX _ hst
  have h2 := aux_prop_as_response_bank_cauchy_markov_integral P F hF0 hFI _ hst
  have hsq : (Real.sqrt t) ^ (-(1 : ℝ)) = t ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
    norm_num
  have hdiv : (∫ omega, F omega ∂P) / Real.sqrt t =
      (∫ omega, F omega ∂P) * t ^ (-(1 / 2 : ℝ)) := by
    rw [← hsq, Real.rpow_neg_one, div_eq_mul_inv]
  rw [hsq] at h1
  rw [hdiv] at h2
  have hint0 : 0 ≤ ∫ omega, F omega ∂P := integral_nonneg hF0
  calc
    P {omega | t < X omega * F omega}
        ≤ P {omega | Real.sqrt t < X omega} + P {omega | Real.sqrt t < F omega} :=
      (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (B * t ^ (-(1 / 2 : ℝ))) +
        ENNReal.ofReal ((∫ omega, F omega ∂P) * t ^ (-(1 / 2 : ℝ))) := add_le_add h1 h2
    _ = ENNReal.ofReal ((B + ∫ omega, F omega ∂P) * t ^ (-(1 / 2 : ℝ))) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- The unit-cube coercivity supplier with an explicit first-order tail. The first
moment order is fixed before the model and before every later large cube. -/
theorem aux_large_cube_unit_coercivity
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd) :
    ∃ deltaK : ℝ, 0 < deltaK ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ deltaK →
      ∃ (K : ℕ → BilateralField d → ℝ) (B : ℝ), 0 ≤ B ∧
        (∀ N omega, 0 < K N omega) ∧
        (∀ N omega (v : meanZeroSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos)),
          cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos threeQuarterOrder
              (v : SobolevData _).1 ≤
            K N omega * sobolevCoefficientForm
              (cutoffPositiveCoefficient M H omega N 0 one_pos) (v : SobolevData _) v) ∧
        (∀ N (t : ℝ), 0 < t →
          (chaosSampleLaw M).toMeasure {omega | t < K N omega} ≤
            ENNReal.ofReal (B * t ^ (-(1 : ℝ)))) := by
  have hLC0 := aux_lem_coercivity_compat d hd Jc Pc Sf
  obtain ⟨delta0, hpos, hLC⟩ := hLC0
  refine ⟨delta0 1, hpos 1 le_rfl, ?_⟩
  intro M Rm H HI hsmall
  have hK0 := hLC M Rm H HI 0 1 one_pos le_rfl
  obtain ⟨K, hKc, hKm⟩ := hK0
  have hKm1 := hKm 1 le_rfl hsmall
  obtain ⟨Cb, hmem, hbd⟩ := hKm1
  refine ⟨fun N omega => |K N omega| + 1, max 2 (2 * max Cb 0), by positivity,
    fun _ _ => by positivity, ?_, ?_⟩
  · intro N omega v
    have h1 := ((hKc N omega).2 v).2
    have hE := sobolevCoefficientForm_nonneg (cutoffPositiveCoefficient M H omega N 0 one_pos)
      (v : SobolevData _)
    exact h1.trans (mul_le_mul_of_nonneg_right
      ((le_abs_self _).trans (le_add_of_nonneg_right zero_le_one)) hE)
  · intro N t ht
    exact aux_large_cube_abs_add_one_tail (chaosSampleLaw M).toMeasure
      (K N) Cb (hmem N).aestronglyMeasurable (hbd N) t ht

end

section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators

/-- The missing large-cube input follows from the same unit-cube first-moment threshold.
An upward scale shift adds finitely many coarse layers. Their compact norms and both
infrared restrictions have all exponential moments, with no additional disorder bound. -/
theorem aux_prop_as_response_bank_cauchy_coercivityLarge_holds
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd) :
    aux_prop_as_response_bank_cauchy_coercivityLarge d hd := by
  have hU0 := aux_large_cube_unit_coercivity d hd Jc Pc Sf
  obtain ⟨deltaK, hdeltaK, hU⟩ := hU0
  refine ⟨deltaK, hdeltaK, ?_⟩
  intro M Rm H HI hsmall z r hr htri hr1 infrared
  obtain ⟨j, hj⟩ := htri
  have hjpos : 0 < j := (one_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1
    (hj ▸ hr1)
  have hnat : r = (3 : ℝ) ^ j.toNat := by
    rw [hj, ← zpow_natCast, Int.toNat_of_nonneg hjpos.le]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, r = (3 : ℝ) ^ k := ⟨j.toNat, hnat⟩
  clear hj hjpos hnat
  subst r
  have hU1 := hU M Rm H HI (hsmall.trans (min_le_right _ _))
  obtain ⟨K, B, hB, hKpos, hKcoer, hKtail⟩ := hU1
  let D : ℝ := (((3 : ℝ) ^ k) ^ ((d : ℝ) - 2))⁻¹
  have hD : 0 < D := inv_pos.2 (Real.rpow_pos_of_pos hr _)
  let F : BilateralField d → ℝ := fun omega =>
    aux_large_cube_environment_factor M H k z hr omega * D
  have hFpos : ∀ omega, 0 < F omega := fun omega =>
    mul_pos (aux_large_cube_environment_factor_pos M H k z hr omega) hD
  have hFI : Integrable F (chaosSampleLaw M).toMeasure :=
    (aux_large_cube_environment_factor_integrable hd M H HI k z hr).mul_const D
  let Kbig : ℕ → BilateralField d → ℝ := fun N omega =>
    K (N + k) (aux_large_cube_upShift k z omega) * F omega
  refine ⟨Kbig, B + ∫ omega, F omega ∂(chaosSampleLaw M).toMeasure, 1 / 2,
    add_nonneg hB (integral_nonneg fun omega => (hFpos omega).le), by norm_num,
    fun N omega => mul_pos (hKpos _ _) (hFpos omega), ?_, ?_⟩
  · intro N omega v
    have hcmp := aux_large_cube_coefficients_le M Rm H k z hr infrared N omega
    have htr := aux_large_cube_coercivity_transport hd z ((3 : ℝ) ^ k) hr hr1.le
      (cutoffPositiveCoefficient M (if infrared then H else 0) omega N z hr)
      (cutoffPositiveCoefficient M H (aux_large_cube_upShift k z omega) (N + k) 0 one_pos)
      (K (N + k) (aux_large_cube_upShift k z omega))
      (aux_large_cube_environment_factor M H k z hr omega)
      (hKpos _ _).le (hKcoer (N + k) (aux_large_cube_upShift k z omega)) hcmp v
    simpa only [Kbig, F, D, mul_assoc] using htr
  · intro N t ht
    have hshift : ∀ s : ℝ, 0 < s →
        (chaosSampleLaw M).toMeasure
          {omega | s < K (N + k) (aux_large_cube_upShift k z omega)} ≤
          ENNReal.ofReal (B * s ^ (-(1 : ℝ))) := by
      intro s hs
      exact (aux_large_cube_upShift_prob_le M k z {omega | s < K (N + k) omega}).trans
        (hKtail (N + k) s hs)
    exact aux_large_cube_product_tail (chaosSampleLaw M).toMeasure
      (fun omega => K (N + k) (aux_large_cube_upShift k z omega)) F B hB
      (fun omega => (hFpos omega).le) hFI hshift t ht

end



theorem aux_prop_as_response_bank_cube_poincare
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) :
    let Q := centeredCube z r hr
    (∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
      ‖(u : SobolevData Q).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph Q) u‖) ∧
    (∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph Q,
      ‖(u : SobolevData Q).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph Q) u‖) := by
  have : NeZero d := ⟨by omega⟩
  let Q := centeredCube z r hr
  have hQ : Homogenization.IsOpenBoundedConvexDomain
      (Q : Set (SpatialCoordinates d)) := by
    refine ⟨Q.isOpen, ?_, ?_⟩
    · simpa [Q] using
        (Homogenization.Bornology.IsBounded.isBoundedDomain
          (centeredCube_isBounded z hr))
    · simpa [Q, centeredCube] using (convex_ball z (r / 2))
  exact exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain Q hQ

theorem prop_as_response_bank_cauchy
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 Cgeom : ℝ, 0 < delta0 ∧ 0 < Cgeom ∧
      ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : in_responses d model) (Sreg : in_6_16 d model) (_It : in_iteration d model Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_HI : InfraredCharacterization model H)
        (_hdelta : model.delta ≤ min 1 delta0),
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (_htriadic : ∃ j : ℤ, r = (3 : ℝ) ^ j),
      let Q := centeredCube z r hr
      let _closedQ := closedCube z r hr
      let hP := (aux_prop_as_response_bank_cube_poincare hd z r hr).1
      let hP0 := (aux_prop_as_response_bank_cube_poincare hd z r hr).2
      ∀ (phi : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ phi →
      ∀ (b : weakSobolevGraph Q),
        ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (Q : Set (SpatialCoordinates d))] phi →
      ∀ (fD fN : DomainL2 Q) (KD KN : ℝ),
        0 ≤ KD → 0 ≤ KN →
        (∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
          |(fD : SpatialCoordinates d → ℝ) x| ≤ KD) →
        (∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
          |(fN : SpatialCoordinates d → ℝ) x| ≤ KN) →
        (∫ x in (Q : Set (SpatialCoordinates d)),
          (fN : SpatialCoordinates d → ℝ) x) = 0 →
      ∀ (p : Fin d → ℝ),
      let SD := killedResponseSpace hP
      let SN := meanZeroResponseSpace hP0
      let Rsp : Bool → Fin 4 → ℕ → BilateralField d → ℝ :=
        fun infrared i N omega =>
          let Hused := if infrared then H else
            (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
          let a : ℕ → BilateralField d → PositiveCoefficient Q :=
            fun N omega => cutoffPositiveCoefficient model Hused omega N z hr
          match i.val with
          | 0 => dirichletResponse SD (a N omega) b
          | 1 => inverseResponse SD (a N omega)
              ((sobolevVolumeLoad fD).comp SD.space.subtypeL)
          | 2 => inverseResponse SN (a N omega)
              ((sobolevVolumeLoad fN).comp SN.space.subtypeL)
          | _ => affineInverseNeumannResponse hP0 (a N omega) p
      let P : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure
      (∀ (infrared : Bool) (i : Fin 4) (N : ℕ),
        ∀ᵐ omega ∂P, 0 ≤ Rsp infrared i N omega) ∧
      (∀ (eps : ℝ), 0 < eps →
        ∃ Ceps ceps : ℝ, ∃ N0 : ℕ,
          0 < Ceps ∧ 0 < ceps ∧
          ∀ N : ℕ, N0 ≤ N →
            ∃ M0 : ℕ, N ≤ M0 ∧
              ∀ M : ℕ, M0 ≤ M →
                ∀ (infrared : Bool) (i : Fin 4),
                  P {omega |
                      |Rsp infrared i N omega - Rsp infrared i M omega| >
                        Cgeom * eps * Rsp infrared i N omega +
                          Ceps * (3 : ℝ) ^ (-(ceps * (N : ℝ)))} ≤
                    ENNReal.ofReal (Ceps * (3 : ℝ) ^
                      (-(ceps * (N : ℝ))))) ∧
      (∀ (infrared : Bool) (i : Fin 4) (tolerance probability : ℝ),
        0 < tolerance → 0 < probability →
        ∃ J : ℕ, ∀ M M' : ℕ, J ≤ M → J ≤ M' →
          P {omega |
              tolerance < |Rsp infrared i M omega - Rsp infrared i M' omega|} ≤
            ENNReal.ofReal probability) := by
  obtain ⟨delta0, Cgeom, hdelta0, hCgeom, hresponse⟩ :=
    aux_prop_as_response_bank_cauchy_of_coercivityLarge d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
      (aux_prop_as_response_bank_cauchy_coercivityLarge_holds d hd Jc Pc Sf)
  refine ⟨delta0, Cgeom, hdelta0, hCgeom, ?_⟩
  intro model Rm Sreg It H HI hdelta z r hr htriadic
  exact hresponse model Rm Sreg It H HI hdelta z r hr htriadic
    (aux_prop_as_response_bank_cube_poincare hd z r hr).1
    (aux_prop_as_response_bank_cube_poincare hd z r hr).2

end SubdiffusiveProcess.Paper
