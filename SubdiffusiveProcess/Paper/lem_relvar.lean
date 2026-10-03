module

public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Paper.lem_relvar_weighted_measure_comparison
public import SubdiffusiveProcess.Paper.lem_relvar_localized_weighted_minimizer_difference
public import SubdiffusiveProcess.Paper.lem_relvar_weighted_response_correction_identity
public import SubdiffusiveProcess.Paper.lem_relvar_normalized_response_denominator_assembly
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.common_trace_class
public import SubdiffusiveProcess.Paper.cor_14
public import SubdiffusiveProcess.Paper.lem_borel_weights
public import SubdiffusiveProcess.Paper.lem_coercivity
public import SubdiffusiveProcess.Paper.lem_common
public import SubdiffusiveProcess.Paper.lem_diff
public import SubdiffusiveProcess.Paper.lem_relvar_sum
public import SubdiffusiveProcess.Paper.lem_sincos
public import SubdiffusiveProcess.Paper.optimal_endpoints
public import SubdiffusiveProcess.Paper.prop_boundary
public import SubdiffusiveProcess.Paper.prop_killed_consistency
public import SubdiffusiveProcess.Paper.relative_response_variation
public import SubdiffusiveProcess.Paper.thm_C0
public import SubdiffusiveProcess.Paper.energy_order_of_form_order

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

namespace Paper
noncomputable section

lemma aux_lem_relvar_signedIntegral_bound
    {X : Type*} [MeasurableSpace X] (ν : SignedMeasure X) (B : Set X)
    (hB : MeasurableSet B) (f : X → ℝ) (hf : Measurable f) (K : ℝ)
    (hK : 0 ≤ K) (hbound : ∀ x, |f x| ≤ K) :
    |DirichletForm.signedIntegralOn ν B f| ≤ K * (ν.totalVariation B).toReal := by
  obtain ⟨S, hS, hpos, hneg, hpospart, hnegpart⟩ := ν.toJordanDecomposition_spec
  let μp := ν.toJordanDecomposition.posPart
  let μn := ν.toJordanDecomposition.negPart
  have hfp : Integrable f μp :=
    Integrable.of_bound hf.aestronglyMeasurable K
      (Filter.Eventually.of_forall (fun x => by
        simpa [Real.norm_eq_abs] using hbound x))
  have hfn : Integrable f μn :=
    Integrable.of_bound hf.aestronglyMeasurable K
      (Filter.Eventually.of_forall (fun x => by
        simpa [Real.norm_eq_abs] using hbound x))
  have hpabs : |∫ x in B, f x ∂μp| ≤ K * (μp B).toReal := by
    calc
      |∫ x in B, f x ∂μp| ≤ ∫ x in B, |f x| ∂μp := abs_integral_le_integral_abs
      _ ≤ ∫ x in B, K ∂μp := by
        apply integral_mono_ae (hfp.abs.restrict)
          (integrableOn_const (μ := μp) (by finiteness))
        filter_upwards [] with x
        exact hbound x
      _ = K * (μp B).toReal := by
        simp [integral_const, Measure.real, smul_eq_mul, mul_comm]
  have hnabs : |∫ x in B, f x ∂μn| ≤ K * (μn B).toReal := by
    calc
      |∫ x in B, f x ∂μn| ≤ ∫ x in B, |f x| ∂μn := abs_integral_le_integral_abs
      _ ≤ ∫ x in B, K ∂μn := by
        apply integral_mono_ae (hfn.abs.restrict)
          (integrableOn_const (μ := μn) (by finiteness))
        filter_upwards [] with x
        exact hbound x
      _ = K * (μn B).toReal := by
        simp [integral_const, Measure.real, smul_eq_mul, mul_comm]
  have hdiff :
      |(∫ x in B, f x ∂μp) - ∫ x in B, f x ∂μn| ≤
        K * ((μp B).toReal + (μn B).toReal) := by
    calc
      |(∫ x in B, f x ∂μp) - ∫ x in B, f x ∂μn| ≤
          |∫ x in B, f x ∂μp| + |∫ x in B, f x ∂μn| := abs_sub _ _
      _ ≤ K * (μp B).toReal + K * (μn B).toReal := add_le_add hpabs hnabs
      _ = K * ((μp B).toReal + (μn B).toReal) := by ring
  have htv : ν.totalVariation B = μp B + μn B := by rfl
  rw [htv, ENNReal.toReal_add (by finiteness) (by finiteness)]
  simpa [DirichletForm.signedIntegralOn] using hdiff

lemma aux_lem_relvar_cross_totalVariation_bound
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} {E : DirichletForm.ClosedForm m}
    (Γ : DirichletForm.EnergyMeasure E) {u v : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) {B : Set X}
    (hB : MeasurableSet B) :
    ((Γ.cross u v).totalVariation B).toReal ≤
      2 * Real.sqrt ((Γ.measure u B).toReal * (Γ.measure v B).toReal) := by
  obtain ⟨S, hS, hpos, hneg, hpospart, hnegpart⟩ :=
    (Γ.cross u v).toJordanDecomposition_spec
  have hq : MeasurableSet (S ∩ B) := hS.inter hB
  have hqc : MeasurableSet (Sᶜ ∩ B) := hS.compl.inter hB
  have hcp := Γ.abs_cross_le u hu v hv (S ∩ B) hq
  have hcn := Γ.abs_cross_le u hu v hv (Sᶜ ∩ B) hqc
  have hmonu : (Γ.measure u (S ∩ B)).toReal ≤ (Γ.measure u B).toReal :=
    Γ.toReal_measure_mono hu inter_subset_right
  have hmonv : (Γ.measure v (S ∩ B)).toReal ≤ (Γ.measure v B).toReal :=
    Γ.toReal_measure_mono hv inter_subset_right
  have hmonuc : (Γ.measure u (Sᶜ ∩ B)).toReal ≤ (Γ.measure u B).toReal :=
    Γ.toReal_measure_mono hu inter_subset_right
  have hmonvc : (Γ.measure v (Sᶜ ∩ B)).toReal ≤ (Γ.measure v B).toReal :=
    Γ.toReal_measure_mono hv inter_subset_right
  have hp : Γ.cross u v (S ∩ B) ≤
      Real.sqrt ((Γ.measure u B).toReal * (Γ.measure v B).toReal) := by
    have hcp' : |Γ.cross u v (S ∩ B)| ≤
        Real.sqrt ((Γ.measure u (S ∩ B)).toReal *
          (Γ.measure v (S ∩ B)).toReal) := by
      calc
        |Γ.cross u v (S ∩ B)| ≤
            Real.sqrt (Γ.measure u (S ∩ B)).toReal *
              Real.sqrt (Γ.measure v (S ∩ B)).toReal := by
                simpa only [Γ.cross_self u hu _ hq, Γ.cross_self v hv _ hq] using hcp
        _ = Real.sqrt ((Γ.measure u (S ∩ B)).toReal *
              (Γ.measure v (S ∩ B)).toReal) := by
          rw [Real.sqrt_mul (ENNReal.toReal_nonneg)]
    have hprod : (Γ.measure u (S ∩ B)).toReal *
          (Γ.measure v (S ∩ B)).toReal ≤
        (Γ.measure u B).toReal * (Γ.measure v B).toReal :=
      mul_le_mul hmonu hmonv (ENNReal.toReal_nonneg) (ENNReal.toReal_nonneg)
    exact le_trans (le_trans (le_abs_self _) hcp') (Real.sqrt_le_sqrt hprod)
  have hn : -(Γ.cross u v (Sᶜ ∩ B)) ≤
      Real.sqrt ((Γ.measure u B).toReal * (Γ.measure v B).toReal) := by
    have hcn' : |Γ.cross u v (Sᶜ ∩ B)| ≤
        Real.sqrt ((Γ.measure u (Sᶜ ∩ B)).toReal *
          (Γ.measure v (Sᶜ ∩ B)).toReal) := by
      calc
        |Γ.cross u v (Sᶜ ∩ B)| ≤
            Real.sqrt (Γ.measure u (Sᶜ ∩ B)).toReal *
              Real.sqrt (Γ.measure v (Sᶜ ∩ B)).toReal := by
                simpa only [Γ.cross_self u hu _ hqc, Γ.cross_self v hv _ hqc] using hcn
        _ = Real.sqrt ((Γ.measure u (Sᶜ ∩ B)).toReal *
              (Γ.measure v (Sᶜ ∩ B)).toReal) := by
          rw [Real.sqrt_mul (ENNReal.toReal_nonneg)]
    have hprod : (Γ.measure u (Sᶜ ∩ B)).toReal *
          (Γ.measure v (Sᶜ ∩ B)).toReal ≤
        (Γ.measure u B).toReal * (Γ.measure v B).toReal :=
      mul_le_mul hmonuc hmonvc (ENNReal.toReal_nonneg) (ENNReal.toReal_nonneg)
    exact le_trans (neg_le_abs _) (le_trans hcn' (Real.sqrt_le_sqrt hprod))
  rw [SignedMeasure.totalVariation, Measure.add_apply, hpospart, hnegpart]
  have hp' : (((Γ.cross u v).toMeasureOfZeroLE S hS hpos) B).toReal =
      Γ.cross u v (S ∩ B) := by
    simpa [Measure.real] using
      (SignedMeasure.toMeasureOfZeroLE_real_apply (Γ.cross u v) hpos hS hB)
  have hn' : (((Γ.cross u v).toMeasureOfLEZero Sᶜ hS.compl hneg) B).toReal =
      -(Γ.cross u v (Sᶜ ∩ B)) := by
    simpa [Measure.real] using
      (SignedMeasure.toMeasureOfLEZero_real_apply (Γ.cross u v) hneg hS.compl hB)
  have hadd :
      (((Γ.cross u v).toMeasureOfZeroLE S hS hpos) B +
        (Γ.cross u v).toMeasureOfLEZero Sᶜ hS.compl hneg B).toReal =
      (((Γ.cross u v).toMeasureOfZeroLE S hS hpos) B).toReal +
        (((Γ.cross u v).toMeasureOfLEZero Sᶜ hS.compl hneg) B).toReal := by
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  rw [hadd, hp', hn']
  have hU : 0 ≤ (Γ.measure u B).toReal := ENNReal.toReal_nonneg
  have hV : 0 ≤ (Γ.measure v B).toReal := ENNReal.toReal_nonneg
  nlinarith

lemma aux_lem_relvar_weighted_cross_bound
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} {E : DirichletForm.ClosedForm m}
    (Γ : DirichletForm.EnergyMeasure E) {u v : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) {B : Set X}
    (hB : MeasurableSet B) (f : X → ℝ) (hf : Measurable f) (K : ℝ)
    (hK : 0 ≤ K) (hbound : ∀ x, |f x| ≤ K) :
    |DirichletForm.signedIntegralOn (Γ.cross u v) B f| ≤
      2 * K * Real.sqrt ((Γ.measure u B).toReal * (Γ.measure v B).toReal) := by
  have h1 := aux_lem_relvar_signedIntegral_bound (Γ.cross u v) B hB f hf K hK hbound
  have h2 := aux_lem_relvar_cross_totalVariation_bound Γ hu hv hB
  have hK' : 0 ≤ 2 * K := by positivity
  calc
    |DirichletForm.signedIntegralOn (Γ.cross u v) B f| ≤
        K * ((Γ.cross u v).totalVariation B).toReal := h1
    _ ≤ K * (2 * Real.sqrt ((Γ.measure u B).toReal * (Γ.measure v B).toReal)) :=
      mul_le_mul_of_nonneg_left h2 hK
    _ = 2 * K * Real.sqrt ((Γ.measure u B).toReal * (Γ.measure v B).toReal) := by ring

lemma aux_lem_relvar_signedIntegral_sub_smul
    {X : Type*} [MeasurableSpace X] (ν ξ : SignedMeasure X) (B : Set X)
    (hB : MeasurableSet B) (f : X → ℝ) (hf : Measurable f) (K c : ℝ)
    (hc : 0 ≤ c) (hK : 0 ≤ K) (hbound : ∀ x, |f x| ≤ K) :
    DirichletForm.signedIntegralOn (ν - c • ξ) B f =
      DirichletForm.signedIntegralOn ν B f -
        c * DirichletForm.signedIntegralOn ξ B f := by
  rw [sub_eq_add_neg, aux_cor_14_signedIntegralOn_add ν (-(c • ξ)) B hB f hf hK
    (fun x => by simpa [Real.norm_eq_abs] using hbound x),
    aux_cor_14_signedIntegralOn_neg_measure,
    aux_cor_14_signedIntegralOn_smul_nonneg ξ B f hc]
  ring

lemma aux_lem_relvar_weighted_measure_bounds
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} {E Eg : DirichletForm.ClosedForm m}
    (Gamma : DirichletForm.EnergyMeasure E)
    (Gammag : DirichletForm.EnergyMeasure Eg) (hdom : Eg.domain = E.domain)
    (g : X → ℝ) (hg : Measurable g) (G : ℝ)
    (hG : ∀ x, |g x| ≤ G)
    (hweight : ∀ u ∈ E.domain, ∀ A : Set X, MeasurableSet A →
      Gammag.measure u A =
        ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(Gamma.measure u))
    {u : Lp ℝ 2 m} (hu : u ∈ E.domain) {A : Set X}
    (hA : MeasurableSet A) :
    Real.exp (-G) * (Gamma.measure u A).toReal ≤
        (Gammag.measure u A).toReal ∧
      (Gammag.measure u A).toReal ≤
        Real.exp G * (Gamma.measure u A).toReal := by
  have huEg : u ∈ Eg.domain := by rw [hdom]; exact hu
  have hlow : ENNReal.ofReal (Real.exp (-G)) * Gamma.measure u A ≤
      Gammag.measure u A := by
    rw [hweight u hu A hA]
    calc
      ENNReal.ofReal (Real.exp (-G)) * Gamma.measure u A =
          ∫⁻ x in A, ENNReal.ofReal (Real.exp (-G)) ∂Gamma.measure u := by
            simp [MeasureTheory.lintegral_const]
      _ ≤ ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂Gamma.measure u := by
        apply MeasureTheory.lintegral_mono
        intro x
        exact ENNReal.ofReal_le_ofReal
          ((Real.exp_le_exp).2 ((abs_le.mp (hG x)).1))
  have hhigh : Gammag.measure u A ≤
      ENNReal.ofReal (Real.exp G) * Gamma.measure u A := by
    rw [hweight u hu A hA]
    calc
      ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂Gamma.measure u ≤
          ∫⁻ x in A, ENNReal.ofReal (Real.exp G) ∂Gamma.measure u := by
        apply MeasureTheory.lintegral_mono
        intro x
        exact ENNReal.ofReal_le_ofReal
          ((Real.exp_le_exp).2 ((abs_le.mp (hG x)).2))
      _ = ENNReal.ofReal (Real.exp G) * Gamma.measure u A := by
        simp [MeasureTheory.lintegral_const]
  constructor
  · calc
      Real.exp (-G) * (Gamma.measure u A).toReal =
          (ENNReal.ofReal (Real.exp (-G)) * Gamma.measure u A).toReal := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))]
      _ ≤ (Gammag.measure u A).toReal :=
        ENNReal.toReal_mono (Gammag.measure_ne_top huEg A) hlow
  · calc
      (Gammag.measure u A).toReal ≤
          (ENNReal.ofReal (Real.exp G) * Gamma.measure u A).toReal :=
        ENNReal.toReal_mono
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Gamma.measure_ne_top hu A)) hhigh
      _ = Real.exp G * (Gamma.measure u A).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))]

lemma aux_lem_relvar_measure_sub_le
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} {E : DirichletForm.ClosedForm m}
    (Gamma : DirichletForm.EnergyMeasure E)
    {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    {B : Set X} (hB : MeasurableSet B) :
    (Gamma.measure (u - v) B).toReal ≤
      2 * (Gamma.measure u B).toReal + 2 * (Gamma.measure v B).toReal := by
  have huv : u - v ∈ E.domain := E.domain.sub_mem hu hv
  have hsum : v + (u - v) = u := by abel
  have hexp := Gamma.cross_add_self_apply hv huv B
  have hcross := Gamma.abs_cross_le v hv (u - v) huv B hB
  have ha : 0 ≤ (Gamma.measure v B).toReal := ENNReal.toReal_nonneg
  have hb : 0 ≤ (Gamma.measure (u - v) B).toReal := ENNReal.toReal_nonneg
  have hsqrt :
      2 * Real.sqrt (Gamma.measure v B).toReal *
          Real.sqrt (Gamma.measure (u - v) B).toReal ≤
        (Gamma.measure v B).toReal + (Gamma.measure (u - v) B).toReal := by
    have hs := sq_nonneg
      (Real.sqrt (Gamma.measure v B).toReal -
        Real.sqrt (Gamma.measure (u - v) B).toReal)
    have hva := Real.sq_sqrt ha
    have hvb := Real.sq_sqrt hb
    nlinarith
  have hcross' :
      2 * Gamma.cross v (u - v) B ≤
        (Gamma.measure v B).toReal + (Gamma.measure (u - v) B).toReal := by
    have hle := le_trans (le_abs_self (Gamma.cross v (u - v) B)) hcross
    nlinarith
  have hneg : Gamma.measure (-v) B = Gamma.measure v B := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (Gamma.measure_ne_top (E.domain.neg_mem hv) B)
      (Gamma.measure_ne_top hv B)).mp
    have hcrossneg : Gamma.cross (-v) (-v) B = Gamma.cross v v B := by
      calc
        Gamma.cross (-v) (-v) B =
            Gamma.cross ((-1 : ℝ) • v) ((-1 : ℝ) • v) B := by simp
        _ = ((-1 : ℝ) • Gamma.cross v ((-1 : ℝ) • v)) B := by
          rw [Gamma.cross_smul_left (-1) (u := v) (v := (-1 : ℝ) • v)
            hv (E.domain.smul_mem (-1) hv)]
        _ = ((-1 : ℝ) • ((-1 : ℝ) • Gamma.cross v v)) B := by
          rw [Gamma.cross_smul_right (-1) v hv v hv]
        _ = Gamma.cross v v B := by
          simp [VectorMeasure.smul_apply, smul_eq_mul]
    calc
      (Gamma.measure (-v) B).toReal = Gamma.cross (-v) (-v) B :=
        (Gamma.cross_self (-v) (E.domain.neg_mem hv) B hB).symm
      _ = Gamma.cross v v B := hcrossneg
      _ = (Gamma.measure v B).toReal := Gamma.cross_self v hv B hB
  have hsum' : u - v = u + (-v) := by abel
  have hexp' := Gamma.cross_add_self_apply hu (E.domain.neg_mem hv) B
  have hcross' :
      2 * Gamma.cross u (-v) B ≤
        (Gamma.measure u B).toReal + (Gamma.measure (-v) B).toReal := by
    have hcrossuv := Gamma.abs_cross_le u hu (-v) (E.domain.neg_mem hv) B hB
    have hs := sq_nonneg
      (Real.sqrt (Gamma.measure u B).toReal -
        Real.sqrt (Gamma.measure (-v) B).toReal)
    have hua := Real.sq_sqrt (ENNReal.toReal_nonneg :
      0 ≤ (Gamma.measure u B).toReal)
    have hva' := Real.sq_sqrt (ENNReal.toReal_nonneg :
      0 ≤ (Gamma.measure (-v) B).toReal)
    nlinarith [le_trans (le_abs_self (Gamma.cross u (-v) B)) hcrossuv]
  calc
    (Gamma.measure (u - v) B).toReal = Gamma.cross (u - v) (u - v) B :=
      (Gamma.cross_self (u - v) huv B hB).symm
    _ = Gamma.cross (u + (-v)) (u + (-v)) B := by rw [hsum']
    _ = Gamma.cross u u B + 2 * Gamma.cross u (-v) B +
        Gamma.cross (-v) (-v) B := hexp'
    _ = (Gamma.measure u B).toReal + 2 * Gamma.cross u (-v) B +
        (Gamma.measure (-v) B).toReal := by
      rw [Gamma.cross_self u hu B hB,
        Gamma.cross_self (-v) (E.domain.neg_mem hv) B hB]
    _ = (Gamma.measure u B).toReal + 2 * Gamma.cross u (-v) B +
        (Gamma.measure v B).toReal := by rw [hneg]
    _ ≤ 2 * (Gamma.measure u B).toReal + 2 * (Gamma.measure v B).toReal := by
      rw [hneg] at hcross'
      nlinarith [hcross']

lemma aux_lem_relvar_normalized_sum_toReal
    {X ι : Type*} [MeasurableSpace X]
    (D : ℝ) (hD : 0 < D) (s : Finset ι) (μ : ι → Measure X) (B : Set X)
    (hfinite : ∀ i ∈ s, μ i B ≠ ⊤) :
    ((ENNReal.ofReal D⁻¹ • (∑ i ∈ s, μ i)) B).toReal =
      D⁻¹ * ∑ i ∈ s, (μ i B).toReal := by
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr hD)),
    Measure.finset_sum_apply, ENNReal.toReal_sum hfinite]

lemma aux_lem_relvar_sum
    (Sg Del Mc Cc nuB zeB T1 T2 T3 T4 T5 : ℝ)
    (hSg : 0 ≤ Sg) (hDel : 0 ≤ Del)
    (hnu : 0 ≤ nuB) (hze : 0 ≤ zeB)
    (h1 : |T1| ≤ Sg * Real.exp Sg * Del * nuB)
    (h2 : |T2| ≤ Sg * Real.exp Sg * (2 * Mc) * Real.sqrt (nuB * zeB))
    (h3 : |T3| ≤ Sg * Real.exp Sg * (Cc * Mc) * Real.sqrt (nuB * zeB))
    (h4 : |T4| ≤ Cc * Sg ^ 2 * Real.exp (Cc * Sg) *
      (Del * nuB + 2 * Real.sqrt (nuB * zeB)))
    (h5 : |T5| ≤ Cc * Sg * Real.exp (Cc * Sg) * Del * nuB) :
    |T1 + T2 + T3 + T4 + T5| ≤
      (Sg * Real.exp Sg + Cc * Sg ^ 2 * Real.exp (Cc * Sg) +
          Cc * Sg * Real.exp (Cc * Sg)) * (Del * nuB) +
        (Sg * Real.exp Sg * (2 * Mc + Cc * Mc) +
          2 * Cc * Sg ^ 2 * Real.exp (Cc * Sg)) * Real.sqrt (nuB * zeB) := by
  have h12 := abs_add_le T1 T2
  have h123 := abs_add_le (T1 + T2) T3
  have h1234 := abs_add_le (T1 + T2 + T3) T4
  have h12345 := abs_add_le (T1 + T2 + T3 + T4) T5
  linarith

lemma aux_lem_relvar_exp_four_mul (G X : ℝ) :
    Real.exp G * (G ^ 2 * Real.exp (3 * G) * X) =
      G ^ 2 * Real.exp (4 * G) * X := by
  have hexp : Real.exp G * Real.exp (3 * G) = Real.exp (4 * G) := by
    rw [← Real.exp_add]
    rw [show G + 3 * G = 4 * G by ring]
  calc
    Real.exp G * (G ^ 2 * Real.exp (3 * G) * X) =
        (Real.exp G * Real.exp (3 * G)) * (G ^ 2 * X) := by ring
    _ = Real.exp (4 * G) * (G ^ 2 * X) := by rw [hexp]
    _ = G ^ 2 * Real.exp (4 * G) * X := by ring

lemma aux_lem_relvar_gap_le (m M C0 : ℝ) (hm : 0 ≤ m) (hM : M ≤ C0) :
    M - m ≤ C0 := by
  linarith

lemma aux_lem_relvar_sq_exp (G : ℝ) (hG : 0 ≤ G) :
    G ^ 2 ≤ Real.exp (2 * G) := by
  have hGe : G ≤ Real.exp G := by
    exact (by linarith : G ≤ G + 1).trans (Real.add_one_le_exp G)
  have hs := mul_self_le_mul_self hG hGe
  calc
    G ^ 2 = G * G := by ring
    _ ≤ Real.exp G * Real.exp G := hs
    _ = Real.exp (2 * G) := by rw [← Real.exp_add]; congr 1 <;> ring

lemma aux_lem_relvar_cube_exp (G : ℝ) (hG : 0 ≤ G) :
    G ^ 3 ≤ Real.exp (3 * G) := by
  have hGe : G ≤ Real.exp G := by
    exact (by linarith : G ≤ G + 1).trans (Real.add_one_le_exp G)
  have hs := aux_lem_relvar_sq_exp G hG
  have hp := mul_le_mul hs hGe hG (Real.exp_nonneg (2 * G))
  calc
    G ^ 3 = G ^ 2 * G := by ring
    _ ≤ Real.exp (2 * G) * Real.exp G := hp
    _ = Real.exp (3 * G) := by rw [← Real.exp_add]; congr 1 <;> ring

lemma aux_lem_relvar_exp_lower (G x y : ℝ)
    (h : Real.exp (-G) * x ≤ y) : x ≤ Real.exp G * y := by
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos G).le
  have he : Real.exp G * Real.exp (-G) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc
    x = Real.exp G * (Real.exp (-G) * x) := by rw [← mul_assoc, he, one_mul]
    _ ≤ Real.exp G * y := hm

lemma aux_lem_relvar_two_sqrt (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * Real.sqrt (a * b) ≤ a + b := by
  rw [Real.sqrt_mul ha]
  have hsq := sq_nonneg (Real.sqrt a - Real.sqrt b)
  have ha' := Real.sq_sqrt ha
  have hb' := Real.sq_sqrt hb
  nlinarith

lemma aux_lem_relvar_sqrt_add (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have ha' := Real.sq_sqrt ha
  have hb' := Real.sq_sqrt hb
  have hp := mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  have hsq : (Real.sqrt (a + b)) ^ 2 ≤
      (Real.sqrt a + Real.sqrt b) ^ 2 := by
    rw [Real.sq_sqrt (add_nonneg ha hb)]
    nlinarith
  exact (sq_le_sq₀ (Real.sqrt_nonneg (a + b))
    (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b))).mp hsq

lemma aux_lem_relvar_scaled_sqrt (M D G nu ze : ℝ)
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hnu : 0 ≤ nu) (hze : 0 ≤ ze) :
    Real.sqrt ((M * D * ze) * (M * G ^ 2 * Real.exp (4 * G) * (D * nu))) =
      M * G * Real.exp (2 * G) * D * Real.sqrt (nu * ze) := by
  have hfac : 0 ≤ M * G * Real.exp (2 * G) * D := by positivity
  calc
    Real.sqrt ((M * D * ze) * (M * G ^ 2 * Real.exp (4 * G) * (D * nu))) =
        Real.sqrt ((M * G * Real.exp (2 * G) * D) ^ 2 * (nu * ze)) := by
      congr 1
      have hexp : Real.exp (2 * G) ^ 2 = Real.exp (4 * G) := by
        calc
          Real.exp (2 * G) ^ 2 = Real.exp (2 * G) * Real.exp (2 * G) := by ring
          _ = Real.exp (4 * G) := by rw [← Real.exp_add]; congr 1 <;> ring
      have hsq : (M * G * Real.exp (2 * G) * D) ^ 2 =
          M ^ 2 * G ^ 2 * Real.exp (4 * G) * D ^ 2 := by
        calc
          (M * G * Real.exp (2 * G) * D) ^ 2 =
              M ^ 2 * G ^ 2 * (Real.exp (2 * G)) ^ 2 * D ^ 2 := by ring
          _ = M ^ 2 * G ^ 2 * Real.exp (4 * G) * D ^ 2 := by rw [hexp]
      rw [hsq]
      ring
    _ = Real.sqrt ((M * G * Real.exp (2 * G) * D) ^ 2) *
        Real.sqrt (nu * ze) := by rw [Real.sqrt_mul (sq_nonneg _)]
    _ = M * G * Real.exp (2 * G) * D * Real.sqrt (nu * ze) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hfac]

lemma aux_lem_relvar_absorb_sq (a b G X : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hG : 0 ≤ G) (hX : 0 ≤ X)
    (hab : a + 1 ≤ b) :
    a * G ^ 2 * Real.exp (a * G) * X ≤
      b * G * Real.exp (b * G) * X := by
  have hGe : G ≤ Real.exp G := (by linarith : G ≤ G + 1).trans
    (Real.add_one_le_exp G)
  have harg : (a + 1) * G ≤ b * G :=
    mul_le_mul_of_nonneg_right hab hG
  have he : Real.exp ((a + 1) * G) ≤ Real.exp (b * G) :=
    Real.exp_le_exp.mpr harg
  have hcoef : a * Real.exp ((a + 1) * G) ≤
      b * Real.exp (b * G) := by
    have hab' : a ≤ b := by linarith
    exact mul_le_mul hab' he (Real.exp_nonneg _) hb
  calc
    a * G ^ 2 * Real.exp (a * G) * X =
        (a * Real.exp (a * G)) * (G * G) * X := by ring
    _ ≤ (a * Real.exp (a * G)) * (G * Real.exp G) * X := by
      gcongr
    _ = (a * Real.exp ((a + 1) * G)) * G * X := by
      calc
        a * Real.exp (a * G) * (G * Real.exp G) * X =
            (a * G * X) * (Real.exp (a * G) * Real.exp G) := by ring
        _ = (a * G * X) * Real.exp ((a + 1) * G) := by
          rw [← Real.exp_add]
          congr 1 <;> ring
        _ = (a * Real.exp ((a + 1) * G)) * G * X := by ring
    _ ≤ (b * Real.exp (b * G)) * G * X := by
      gcongr
    _ = b * G * Real.exp (b * G) * X := by ring

lemma aux_lem_relvar_absorb_cube (a b G X : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hG : 0 ≤ G) (hX : 0 ≤ X)
    (hab : a + 2 ≤ b) :
    a * G ^ 3 * Real.exp (a * G) * X ≤
      b * G * Real.exp (b * G) * X := by
  have hG2 : G ^ 2 ≤ Real.exp (2 * G) := aux_lem_relvar_sq_exp G hG
  have harg : (a + 2) * G ≤ b * G :=
    mul_le_mul_of_nonneg_right hab hG
  have he : Real.exp ((a + 2) * G) ≤ Real.exp (b * G) :=
    Real.exp_le_exp.mpr harg
  have hcoef : a * Real.exp ((a + 2) * G) ≤
      b * Real.exp (b * G) := by
    have hab' : a ≤ b := by linarith
    exact mul_le_mul hab' he (Real.exp_nonneg _) hb
  calc
    a * G ^ 3 * Real.exp (a * G) * X =
        (a * Real.exp (a * G)) * (G ^ 2 * G) * X := by ring
    _ ≤ (a * Real.exp (a * G)) * (Real.exp (2 * G) * G) * X := by
      gcongr
    _ = (a * Real.exp ((a + 2) * G)) * G * X := by
      calc
        a * Real.exp (a * G) * (Real.exp (2 * G) * G) * X =
            (a * G * X) * (Real.exp (a * G) * Real.exp (2 * G)) := by ring
        _ = (a * G * X) * Real.exp ((a + 2) * G) := by
          rw [← Real.exp_add]
          congr 1 <;> ring
        _ = (a * Real.exp ((a + 2) * G)) * G * X := by ring
    _ ≤ (b * Real.exp (b * G)) * G * X := by
      gcongr
    _ = b * G * Real.exp (b * G) * X := by ring

/-- Ambient data of the `lem_relvar` proof, bundled so that the stage lemmas
below can be stated without repeating the forty-odd binders of the theorem. -/
structure aux_lem_relvar_Ctx (C0 : ℝ) {d : ℕ}
    (Q : Opens (SpatialCoordinates d)) (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (slopes : Finset (Fin d → ℝ))
    (E F Eg Fg : DirichletForm.ClosedForm
      (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GammaE : DirichletForm.EnergyMeasure E)
    (GammaF : DirichletForm.EnergyMeasure F)
    (GammaEg : DirichletForm.EnergyMeasure Eg)
    (GammaFg : DirichletForm.EnergyMeasure Fg)
    (V0 : Submodule ℝ (DomainL2 Q)) (m M c : ℝ)
    (g : SpatialCoordinates d → ℝ) (B : Set (SpatialCoordinates d)) (G : ℝ)
    (uE uF uEg uFg : (Fin d → ℝ) → DomainL2 Q)
    (QE QF QEg QFg : QuadraticForm ℝ (Fin d → ℝ))
    (D Dg nu ze : ℝ)
    (IE IF : DomainL2 Q → DomainL2 Q → ℝ) : Prop where
  hC0 : 1 ≤ C0
  hd : 2 ≤ d
  hslopes : ∀ p : Fin d → ℝ,
    p ∈ slopes ↔ (∃ i : Fin d, p = Pi.single i (1 : ℝ)) ∨
      (∃ i j : Fin d, p = Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ))
  hQ : ∃ (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ),
    Q = centeredCube zQ rQ hrQ
  hinside : closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
    (Q : Set (SpatialCoordinates d))
  hdomEF : E.domain = F.domain
  hdomEg : Eg.domain = E.domain
  hdomFg : Fg.domain = E.domain
  hzero : DirichletForm.IsKilledDomain E
    (centeredCube z r hr : Set (SpatialCoordinates d)) V0
  hm : C0⁻¹ ≤ m
  hmM : m ≤ M
  hM : M ≤ C0
  hmc : m ≤ c
  hcM : c ≤ M
  horder : ∀ u ∈ E.domain, ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
    m * (GammaE.measure u A).toReal ≤ (GammaF.measure u A).toReal ∧
      (GammaF.measure u A).toReal ≤ M * (GammaE.measure u A).toReal
  hg : Measurable g
  hB : MeasurableSet B
  hBq : B ⊆ (centeredCube z r hr : Set (SpatialCoordinates d))
  hsupp : ∀ x, x ∉ B → g x = 0
  hG : IsLUB (Set.range (fun x => |g x|)) G
  hbdd : BddAbove (Set.range (fun x => |g x|))
  hweightE : ∀ u ∈ E.domain, ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
    GammaEg.measure u A =
      ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(GammaE.measure u)
  hweightF : ∀ u ∈ F.domain, ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
    GammaFg.measure u A =
      ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(GammaF.measure u)
  hweightE_cross : ∀ u ∈ E.domain, ∀ v ∈ E.domain,
    ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
      GammaEg.cross u v A =
        DirichletForm.signedIntegralOn (GammaE.cross u v) A
          (fun x => Real.exp (g x))
  hweightF_cross : ∀ u ∈ F.domain, ∀ v ∈ F.domain,
    ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
      GammaFg.cross u v A =
        DirichletForm.signedIntegralOn (GammaF.cross u v) A
          (fun x => Real.exp (g x))
  huE : ∀ p, uE p ∈ E.domain
  huF : ∀ p, uF p ∈ F.domain
  huEg : ∀ p, uEg p ∈ Eg.domain
  huFg : ∀ p, uFg p ∈ Fg.domain
  htraceF : ∀ p, uF p - uE p ∈ V0
  htraceEg : ∀ p, uEg p - uE p ∈ V0
  htraceFg : ∀ p, uFg p - uE p ∈ V0
  hminE : ∀ p, ∀ v ∈ E.domain, v - uE p ∈ V0 →
    (GammaE.measure (uE p) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
      (GammaE.measure v (centeredCube z r hr : Set (SpatialCoordinates d))).toReal
  hminF : ∀ p, ∀ v ∈ F.domain, v - uE p ∈ V0 →
    (GammaF.measure (uF p) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
      (GammaF.measure v (centeredCube z r hr : Set (SpatialCoordinates d))).toReal
  hminEg : ∀ p, ∀ v ∈ Eg.domain, v - uE p ∈ V0 →
    (GammaEg.measure (uEg p) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
      (GammaEg.measure v (centeredCube z r hr : Set (SpatialCoordinates d))).toReal
  hminFg : ∀ p, ∀ v ∈ Fg.domain, v - uE p ∈ V0 →
    (GammaFg.measure (uFg p) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
      (GammaFg.measure v (centeredCube z r hr : Set (SpatialCoordinates d))).toReal
  hQE : ∀ p, QE p =
    (GammaE.measure (uE p) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal
  hQF : ∀ p, QF p =
    (GammaF.measure (uF p) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal
  hQEg : ∀ p, QEg p =
    (GammaEg.measure (uEg p) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal
  hQFg : ∀ p, QFg p =
    (GammaFg.measure (uFg p) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal
  hDdef : D = ∑ j : Fin d, QE (Pi.single j 1)
  hD : 0 < D
  hDgdef : Dg = ∑ j : Fin d, QEg (Pi.single j 1)
  hnudef : nu = D⁻¹ * ∑ i ∈ slopes,
    ((GammaE.measure (uE i) + GammaE.measure (uF i)) B).toReal
  hzedef : ze = D⁻¹ * ∑ i ∈ slopes, (GammaE.measure (uF i - uE i) B).toReal
  hIEdef : ∀ x y, IE x y =
    DirichletForm.signedIntegralOn (GammaE.cross x y) B
      (fun t => Real.exp (g t) - 1)
  hIFdef : ∀ x y, IF x y =
    DirichletForm.signedIntegralOn (GammaF.cross x y) B
      (fun t => Real.exp (g t) - 1)

section RelvarStages

variable {C0 : ℝ} {d : ℕ} {Q : Opens (SpatialCoordinates d)}
  {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r} {slopes : Finset (Fin d → ℝ)}
  {E F Eg Fg : DirichletForm.ClosedForm
    (volume.restrict (Q : Set (SpatialCoordinates d)))}
  {GammaE : DirichletForm.EnergyMeasure E} {GammaF : DirichletForm.EnergyMeasure F}
  {GammaEg : DirichletForm.EnergyMeasure Eg} {GammaFg : DirichletForm.EnergyMeasure Fg}
  {V0 : Submodule ℝ (DomainL2 Q)} {m M c : ℝ}
  {g : SpatialCoordinates d → ℝ} {B : Set (SpatialCoordinates d)} {G : ℝ}
  {uE uF uEg uFg : (Fin d → ℝ) → DomainL2 Q}
  {QE QF QEg QFg : QuadraticForm ℝ (Fin d → ℝ)} {D Dg nu ze : ℝ}
  {IE IF : DomainL2 Q → DomainL2 Q → ℝ}

lemma aux_lem_relvar_cross_self_integral
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {mm : Measure X} {E : DirichletForm.ClosedForm mm}
    (Γ : DirichletForm.EnergyMeasure E) {u : Lp ℝ 2 mm} (hu : u ∈ E.domain)
    (B : Set X) (f : X → ℝ) :
    DirichletForm.signedIntegralOn (Γ.cross u u) B f =
      ∫ x in B, f x ∂(Γ.measure u) := by
  letI : IsFiniteMeasure (Γ.measure u) := ⟨Γ.measure_univ_lt_top u hu⟩
  have h : Γ.cross u u = (Γ.measure u).toSignedMeasure := by
    ext A hA
    rw [Γ.cross_self u hu A hA,
      MeasureTheory.Measure.toSignedMeasure_apply_measurable hA]
    simp [MeasureTheory.measureReal_def]
  rw [h, aux_cor_14_signedIntegralOn_measure]

/-- The four response identities: the weighted/unweighted response difference of
`E` and of `F`, and the two Euler identities for the cross terms. -/
lemma aux_lem_relvar_response_identity
    (ctx : aux_lem_relvar_Ctx C0 Q z r hr slopes E F Eg Fg GammaE GammaF GammaEg
      GammaFg V0 m M c g B G uE uF uEg uFg QE QF QEg QFg D Dg nu ze IE IF)
    (p : Fin d → ℝ) :
    (QEg p - QE p = IE (uE p) (uE p) -
        (GammaEg.measure (uEg p - uE p)
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) ∧
      (QFg p - QF p = IF (uF p) (uF p) -
        (GammaFg.measure (uFg p - uF p)
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) ∧
      ((GammaEg.measure (uEg p - uE p)
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal =
        -IE (uE p) (uEg p - uE p)) ∧
      (GammaFg.cross (uFg p - uF p) (uEg p - uE p)
          (centeredCube z r hr : Set (SpatialCoordinates d)) =
        -IF (uF p) (uEg p - uE p)) := by
  obtain ⟨hC0, hd, hslopes, hQ, hinside, hdomEF, hdomEg, hdomFg, hzero, hm, hmM,
    hM, hmc, hcM, horder, hg, hB, hBq, hsupp, hG, hbdd, hweightE, hweightF,
    hweightE_cross, hweightF_cross, huE, huF, huEg, huFg, htraceF, htraceEg,
    htraceFg, hminE, hminF, hminEg, hminFg, hQE, hQF, hQEg, hQFg, hDdef, hD,
    hDgdef, hnudef, hzedef, hIEdef, hIFdef⟩ := ctx
  have hqmeas : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  have hVdomF : V0 ≤ F.domain := by
    intro v hv; rw [← hdomEF]; exact hzero.le_domain hv
  have hVdomEg : V0 ≤ Eg.domain := by
    intro v hv; rw [hdomEg]; exact hzero.le_domain hv
  have hVdomFg : V0 ≤ Fg.domain := by
    intro v hv; rw [hdomFg]; exact hzero.le_domain hv
  have hdomFgF : Fg.domain = F.domain := hdomFg.trans hdomEF
  have htraceFgF : uFg p - uF p ∈ V0 := by
    rw [show uFg p - uF p = (uFg p - uE p) - (uF p - uE p) by abel]
    exact V0.sub_mem (htraceFg p) (htraceF p)
  have hminFbase : ∀ v ∈ F.domain, v - uF p ∈ V0 →
      (GammaF.measure (uF p) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        (GammaF.measure v (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
    intro v hv hv0
    apply hminF p v hv
    rw [show v - uE p = (v - uF p) + (uF p - uE p) by abel]
    exact V0.add_mem hv0 (htraceF p)
  have hminFgbase : ∀ v ∈ Fg.domain, v - uF p ∈ V0 →
      (GammaFg.measure (uFg p) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        (GammaFg.measure v (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
    intro v hv hv0
    apply hminFg p v hv
    rw [show v - uE p = (v - uF p) + (uF p - uE p) by abel]
    exact V0.add_mem hv0 (htraceF p)
  have hminEgAt : ∀ v ∈ Eg.domain, v - uEg p ∈ V0 →
      (GammaEg.measure (uEg p) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        (GammaEg.measure v (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
    intro v hv hv0
    apply hminEg p v hv
    rw [show v - uE p = (v - uEg p) + (uEg p - uE p) by abel]
    exact V0.add_mem hv0 (htraceEg p)
  have hminFgAt : ∀ v ∈ Fg.domain, v - uFg p ∈ V0 →
      (GammaFg.measure (uFg p) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        (GammaFg.measure v (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
    intro v hv hv0
    apply hminFg p v hv
    rw [show v - uE p = (v - uFg p) + (uFg p - uE p) by abel]
    exact V0.add_mem hv0 (htraceFg p)
  have hrespE := aux_cor_14_minimizer_identity GammaE GammaEg hdomEg V0 hVdomEg g hg
    G hG hweightE B (centeredCube z r hr : Set (SpatialCoordinates d)) hB hqmeas
    hBq hsupp (huE p) (huEg p) (htraceEg p) (hminEg p)
  have hrespF := aux_cor_14_minimizer_identity GammaF GammaFg hdomFgF V0 hVdomFg g hg
    G hG hweightF B (centeredCube z r hr : Set (SpatialCoordinates d)) hB hqmeas
    hBq hsupp (huF p) (huFg p) htraceFgF hminFgbase
  have hEcross0 : ∀ v ∈ V0,
      DirichletForm.signedIntegralOn (GammaE.cross (uE p) v)
        (centeredCube z r hr : Set (SpatialCoordinates d)) (fun _ => (1 : ℝ)) = 0 := by
    intro v hv
    rw [aux_cor_14_signedIntegralOn_one _ _ hqmeas]
    exact aux_cor_14_minimizer_cross_zero GammaE V0 hzero.le_domain (huE p)
      hqmeas (hminE p) v hv
  have hEgcross0 : ∀ v ∈ V0,
      DirichletForm.signedIntegralOn (GammaEg.cross (uEg p) v)
        (centeredCube z r hr : Set (SpatialCoordinates d)) (fun _ => (1 : ℝ)) = 0 := by
    intro v hv
    rw [aux_cor_14_signedIntegralOn_one _ _ hqmeas]
    exact aux_cor_14_minimizer_cross_zero GammaEg V0 hVdomEg (huEg p)
      hqmeas hminEgAt v hv
  have hFcross0 : ∀ v ∈ V0,
      DirichletForm.signedIntegralOn (GammaF.cross (uF p) v)
        (centeredCube z r hr : Set (SpatialCoordinates d)) (fun _ => (1 : ℝ)) = 0 := by
    intro v hv
    rw [aux_cor_14_signedIntegralOn_one _ _ hqmeas]
    exact aux_cor_14_minimizer_cross_zero GammaF V0 hVdomF (huF p)
      hqmeas hminFbase v hv
  have hFgcross0 : ∀ v ∈ V0,
      DirichletForm.signedIntegralOn (GammaFg.cross (uFg p) v)
        (centeredCube z r hr : Set (SpatialCoordinates d)) (fun _ => (1 : ℝ)) = 0 := by
    intro v hv
    rw [aux_cor_14_signedIntegralOn_one _ _ hqmeas]
    exact aux_cor_14_minimizer_cross_zero GammaFg V0 hVdomFg (huFg p)
      hqmeas hminFgAt v hv
  have hdiffEeq := aux_cor_14_difference_equation GammaE GammaEg hdomEg V0
    hzero.le_domain hVdomEg g hg G hG hweightE B
    (centeredCube z r hr : Set (SpatialCoordinates d)) hB hqmeas hBq hsupp
    (huE p) (huEg p) (htraceEg p) (fun _ => (0 : ℝ)) hEcross0 hEgcross0
  have hdiffFeq := aux_cor_14_difference_equation GammaF GammaFg hdomFgF V0
    hVdomF hVdomFg g hg G hG hweightF B
    (centeredCube z r hr : Set (SpatialCoordinates d)) hB hqmeas hBq hsupp
    (huF p) (huFg p) htraceFgF (fun _ => (0 : ℝ)) hFcross0 hFgcross0
  have hEcross := hdiffEeq (uEg p - uE p) (htraceEg p)
  have hFcross := hdiffFeq (uEg p - uE p) (htraceEg p)
  rw [aux_cor_14_signedIntegralOn_one _ _ hqmeas] at hEcross hFcross
  have he_Eg : uEg p - uE p ∈ Eg.domain :=
    Eg.domain.sub_mem (huEg p) (by rw [hdomEg]; exact huE p)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hQEg p, hQE p, hIEdef,
      aux_lem_relvar_cross_self_integral GammaE (huE p) B
        (fun t => Real.exp (g t) - 1)]
    exact hrespE
  · rw [hQFg p, hQF p, hIFdef,
      aux_lem_relvar_cross_self_integral GammaF (huF p) B
        (fun t => Real.exp (g t) - 1)]
    exact hrespF
  · rw [← GammaEg.cross_self (uEg p - uE p) he_Eg _ hqmeas, hIEdef]
    exact hEcross
  · rw [hIFdef]
    exact hFcross


lemma aux_lem_relvar_sIO_cross_add_left
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {mm : Measure X}
    {E : DirichletForm.ClosedForm mm} (Γ : DirichletForm.EnergyMeasure E)
    {a b v w : Lp ℝ 2 mm} (ha : a ∈ E.domain) (hb : b ∈ E.domain)
    (hv : v ∈ E.domain) (hw : w = a + b)
    (B : Set X) (hB : MeasurableSet B) (f : X → ℝ) (hf : Measurable f)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ x, ‖f x‖ ≤ K) :
    DirichletForm.signedIntegralOn (Γ.cross w v) B f =
      DirichletForm.signedIntegralOn (Γ.cross a v) B f +
        DirichletForm.signedIntegralOn (Γ.cross b v) B f := by
  subst hw
  rw [Γ.cross_add_left ha hb hv,
    aux_cor_14_signedIntegralOn_add _ _ B hB f hf hK hbound]

lemma aux_lem_relvar_sIO_cross_diag
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {mm : Measure X}
    {E : DirichletForm.ClosedForm mm} (Γ : DirichletForm.EnergyMeasure E)
    {a b w : Lp ℝ 2 mm} (ha : a ∈ E.domain) (hb : b ∈ E.domain) (hw : w = a + b)
    (B : Set X) (hB : MeasurableSet B) (f : X → ℝ) (hf : Measurable f)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ x, ‖f x‖ ≤ K) :
    DirichletForm.signedIntegralOn (Γ.cross w w) B f =
      DirichletForm.signedIntegralOn (Γ.cross a a) B f +
        2 * DirichletForm.signedIntegralOn (Γ.cross a b) B f +
        DirichletForm.signedIntegralOn (Γ.cross b b) B f := by
  subst hw
  have h1 : Γ.cross (a + b) (a + b) =
      (Γ.cross a a + Γ.cross a b) + (Γ.cross a b + Γ.cross b b) := by
    rw [Γ.cross_add_left ha hb (E.domain.add_mem ha hb),
      Γ.cross_add_right a ha a ha b hb, Γ.cross_add_right b hb a ha b hb,
      Γ.cross_symm b hb a ha]
  rw [h1, aux_cor_14_signedIntegralOn_add _ _ B hB f hf hK hbound,
    aux_cor_14_signedIntegralOn_add _ _ B hB f hf hK hbound,
    aux_cor_14_signedIntegralOn_add _ _ B hB f hf hK hbound]
  ring

lemma aux_lem_relvar_cross_pair_apply
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {mm : Measure X}
    {E : DirichletForm.ClosedForm mm} (Γ : DirichletForm.EnergyMeasure E)
    {a b w : Lp ℝ 2 mm} (ha : a ∈ E.domain) (hb : b ∈ E.domain) (hw : w = a + b)
    (A : Set X) :
    Γ.cross w a A = Γ.cross a a A + Γ.cross b a A ∧
      Γ.cross w w A = Γ.cross a a A + 2 * Γ.cross a b A + Γ.cross b b A := by
  subst hw
  refine ⟨?_, Γ.cross_add_self_apply ha hb A⟩
  rw [Γ.cross_add_left ha hb ha, VectorMeasure.add_apply]

lemma aux_lem_relvar_exp_sub_one_bound (G t : ℝ) (hG0 : 0 ≤ G) (ht : |t| ≤ G) :
    |Real.exp t - 1| ≤ G * Real.exp G := by
  have hlow : Real.exp (-G) ≤ Real.exp t := (Real.exp_le_exp).2 ((abs_le.mp ht).1)
  have hhigh : Real.exp t ≤ Real.exp G := (Real.exp_le_exp).2 ((abs_le.mp ht).2)
  by_cases hx : 1 ≤ Real.exp t
  · rw [abs_of_nonneg (sub_nonneg.mpr hx)]
    have hdiff : Real.exp t - 1 ≤ Real.exp G - 1 := by linarith
    have hlin : Real.exp G - 1 ≤ G * Real.exp G := by
      have h := Real.add_one_le_exp (-G)
      have hp := mul_le_mul_of_nonneg_right h (le_of_lt (Real.exp_pos G))
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hp
      linarith only [hp]
    exact hdiff.trans hlin
  · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge hx))]
    have hle : 1 - Real.exp t ≤ G * Real.exp G := by
      have hsum : 1 - Real.exp (-G) ≤ G := by
        have := Real.add_one_le_exp (-G)
        linarith only [this]
      have hprod' := mul_le_mul_of_nonneg_left (Real.one_le_exp hG0) hG0
      have hprod : G ≤ G * Real.exp G := by simpa using hprod'
      have hlow' : 1 - Real.exp t ≤ 1 - Real.exp (-G) := by linarith only [hlow]
      exact hlow'.trans (hsum.trans hprod)
    simpa [sub_eq_add_neg] using hle

/-- The five-term decomposition of the numerator variation.  This follows the
paper's expansion `Γ_F(u_F) - cΓ_E(u_E) = Γ_D(u_E) + 2Γ_F(u_E,w) + Γ_F(w)` with
`w = u_F - u_E` and `Γ_D = Γ_F - cΓ_E`. -/
lemma aux_lem_relvar_num_identity
    (ctx : aux_lem_relvar_Ctx C0 Q z r hr slopes E F Eg Fg GammaE GammaF GammaEg
      GammaFg V0 m M c g B G uE uF uEg uFg QE QF QEg QFg D Dg nu ze IE IF)
    (p : Fin d → ℝ) :
    (QFg p - c * QEg p) - (QF p - c * QE p) =
      (IF (uE p) (uE p) - c * IE (uE p) (uE p)) +
        2 * IF (uE p) (uF p - uE p) +
        IF (uF p - uE p) (uF p - uE p) +
        (IF (uE p) (uEg p - uE p) - c * IE (uE p) (uEg p - uE p)) +
        IF (uF p - uE p) (uEg p - uE p) -
        GammaFg.cross (uEg p - uE p) ((uFg p - uF p) - (uEg p - uE p))
          (centeredCube z r hr : Set (SpatialCoordinates d)) -
        (GammaFg.measure ((uFg p - uF p) - (uEg p - uE p))
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
  obtain ⟨hresE, hresF, hEcross_measure, hFcross_integral⟩ :=
    aux_lem_relvar_response_identity ctx p
  obtain ⟨hC0, hd, hslopes, hQ, hinside, hdomEF, hdomEg, hdomFg, hzero, hm, hmM,
    hM, hmc, hcM, horder, hg, hB, hBq, hsupp, hG, hbdd, hweightE, hweightF,
    hweightE_cross, hweightF_cross, huE, huF, huEg, huFg, htraceF, htraceEg,
    htraceFg, hminE, hminF, hminEg, hminFg, hQE, hQF, hQEg, hQFg, hDdef, hD,
    hDgdef, hnudef, hzedef, hIEdef, hIFdef⟩ := ctx
  have hqmeas : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  have hG0 : 0 ≤ G := le_trans (abs_nonneg (g (Classical.arbitrary _)))
    (hG.1 ⟨Classical.arbitrary _, rfl⟩)
  have hgbound : ∀ x, |g x| ≤ G := fun x => hG.1 ⟨x, rfl⟩
  have hf0 : Measurable (fun x : SpatialCoordinates d => Real.exp (g x) - 1) :=
    hg.exp.sub measurable_const
  have hK : (0 : ℝ) ≤ G * Real.exp G := mul_nonneg hG0 (Real.exp_nonneg _)
  have hf0norm : ∀ x : SpatialCoordinates d,
      ‖Real.exp (g x) - 1‖ ≤ G * Real.exp G := fun x => by
    simpa [Real.norm_eq_abs] using
      aux_lem_relvar_exp_sub_one_bound G (g x) hG0 (hgbound x)
  -- memberships
  have hVdomF : V0 ≤ F.domain := by
    intro v hv; rw [← hdomEF]; exact hzero.le_domain hv
  have hVdomEg : V0 ≤ Eg.domain := by
    intro v hv; rw [hdomEg]; exact hzero.le_domain hv
  have hVdomFg : V0 ≤ Fg.domain := by
    intro v hv; rw [hdomFg]; exact hzero.le_domain hv
  have hdomFgF : Fg.domain = F.domain := hdomFg.trans hdomEF
  have htraceFgF : uFg p - uF p ∈ V0 := by
    rw [show uFg p - uF p = (uFg p - uE p) - (uF p - uE p) by abel]
    exact V0.sub_mem (htraceFg p) (htraceF p)
  have hzV : (uFg p - uF p) - (uEg p - uE p) ∈ V0 :=
    V0.sub_mem htraceFgF (htraceEg p)
  have huF_E : uF p ∈ E.domain := by rw [hdomEF]; exact huF p
  have huE_F : uE p ∈ F.domain := by rw [← hdomEF]; exact huE p
  have hwE : uF p - uE p ∈ E.domain := E.domain.sub_mem huF_E (huE p)
  have hwF : uF p - uE p ∈ F.domain := hVdomF (htraceF p)
  have he_p : uEg p - uE p ∈ E.domain :=
    E.domain.sub_mem (by rw [← hdomEg]; exact huEg p) (huE p)
  have heF : uEg p - uE p ∈ F.domain := by rw [← hdomEF]; exact he_p
  have he_Fg : uEg p - uE p ∈ Fg.domain := by rw [hdomFg]; exact he_p
  have hz_Fg : (uFg p - uF p) - (uEg p - uE p) ∈ Fg.domain := hVdomFg hzV
  have hf_Fg : uFg p - uF p ∈ Fg.domain := hVdomFg htraceFgF
  have hfeq : uFg p - uF p =
      (uEg p - uE p) + ((uFg p - uF p) - (uEg p - uE p)) := by abel
  obtain ⟨hcross_fe, hcross_ff⟩ :=
    aux_lem_relvar_cross_pair_apply GammaFg he_Fg hz_Fg hfeq
      (centeredCube z r hr : Set (SpatialCoordinates d))
  have hsymm : GammaFg.cross ((uFg p - uF p) - (uEg p - uE p)) (uEg p - uE p)
        (centeredCube z r hr : Set (SpatialCoordinates d)) =
      GammaFg.cross (uEg p - uE p) ((uFg p - uF p) - (uEg p - uE p))
        (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    rw [GammaFg.cross_symm _ hz_Fg _ he_Fg]
  rw [hsymm] at hcross_fe
  have hcs_f := GammaFg.cross_self (uFg p - uF p) hf_Fg
    (centeredCube z r hr : Set (SpatialCoordinates d)) hqmeas
  have hcs_e := GammaFg.cross_self (uEg p - uE p) he_Fg
    (centeredCube z r hr : Set (SpatialCoordinates d)) hqmeas
  have hcs_z := GammaFg.cross_self ((uFg p - uF p) - (uEg p - uE p)) hz_Fg
    (centeredCube z r hr : Set (SpatialCoordinates d)) hqmeas
  -- Γ_Fg(u_Fg - u_F)(q) in terms of the cross term and the residue
  have hFg_measure_expand :
      (GammaFg.measure (uFg p - uF p)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal =
        -IF (uF p) (uEg p - uE p) +
          GammaFg.cross (uEg p - uE p) ((uFg p - uF p) - (uEg p - uE p))
            (centeredCube z r hr : Set (SpatialCoordinates d)) +
          (GammaFg.measure ((uFg p - uF p) - (uEg p - uE p))
            (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
    rw [← hcs_f, hcross_ff, ← hcs_z]
    have : GammaFg.cross (uEg p - uE p) (uEg p - uE p)
        (centeredCube z r hr : Set (SpatialCoordinates d)) =
        -IF (uF p) (uEg p - uE p) -
          GammaFg.cross (uEg p - uE p) ((uFg p - uF p) - (uEg p - uE p))
            (centeredCube z r hr : Set (SpatialCoordinates d)) := by
      linarith [hcross_fe, hFcross_integral]
    rw [this]; ring
  -- diagonal split of I_F(u_F, u_F) and of I_F(u_F, e)
  have hFdiag : IF (uF p) (uF p) =
      IF (uE p) (uE p) + 2 * IF (uE p) (uF p - uE p) +
        IF (uF p - uE p) (uF p - uE p) := by
    rw [hIFdef, hIFdef, hIFdef, hIFdef]
    exact aux_lem_relvar_sIO_cross_diag GammaF huE_F hwF
      (by abel) B hB (fun t => Real.exp (g t) - 1) hf0 hK hf0norm
  have hFcross_split : IF (uF p) (uEg p - uE p) =
      IF (uE p) (uEg p - uE p) + IF (uF p - uE p) (uEg p - uE p) := by
    rw [hIFdef, hIFdef, hIFdef]
    exact aux_lem_relvar_sIO_cross_add_left GammaF huE_F hwF heF (by abel) B hB
      (fun t => Real.exp (g t) - 1) hf0 hK hf0norm
  have hlhs : (QFg p - c * QEg p) - (QF p - c * QE p) =
      (QFg p - QF p) - c * (QEg p - QE p) := by ring
  rw [hlhs, hresF, hresE, hFg_measure_expand, hEcross_measure, hFdiag,
    hFcross_split]
  ring



/-- Normalisation facts for the two measures `nu`, `ze`. -/
lemma aux_lem_relvar_nu_basics
    (ctx : aux_lem_relvar_Ctx C0 Q z r hr slopes E F Eg Fg GammaE GammaF GammaEg
      GammaFg V0 m M c g B G uE uF uEg uFg QE QF QEg QFg D Dg nu ze IE IF) :
    0 ≤ nu ∧ 0 ≤ ze ∧
      D * nu = ∑ i ∈ slopes,
        ((GammaE.measure (uE i) + GammaE.measure (uF i)) B).toReal ∧
      D * ze = ∑ i ∈ slopes, (GammaE.measure (uF i - uE i) B).toReal ∧
      ze ≤ 2 * Real.sqrt (nu * ze) ∧
      ((ENNReal.ofReal D⁻¹ •
        (∑ i ∈ slopes, (GammaE.measure (uE i) + GammaE.measure (uF i)))) B).toReal = nu ∧
      ((ENNReal.ofReal D⁻¹ •
        (∑ i ∈ slopes, GammaE.measure (uF i - uE i))) B).toReal = ze ∧
      (∑ i : Fin d, (GammaE.measure (uE (Pi.single i 1)) B).toReal) ≤ D * nu := by
  obtain ⟨hC0, hd, hslopes, hQ, hinside, hdomEF, hdomEg, hdomFg, hzero, hm, hmM,
    hM, hmc, hcM, horder, hg, hB, hBq, hsupp, hG, hbdd, hweightE, hweightF,
    hweightE_cross, hweightF_cross, huE, huF, huEg, huFg, htraceF, htraceEg,
    htraceFg, hminE, hminF, hminEg, hminFg, hQE, hQF, hQEg, hQFg, hDdef, hD,
    hDgdef, hnudef, hzedef, hIEdef, hIFdef⟩ := ctx
  have huF_E : ∀ i, uF i ∈ E.domain := fun i => by rw [hdomEF]; exact huF i
  have hfiniteNu : ∀ i ∈ slopes,
      (GammaE.measure (uE i) + GammaE.measure (uF i)) B ≠ ⊤ := fun i _ =>
    (ENNReal.add_ne_top).2
      ⟨GammaE.measure_ne_top (huE i) B, GammaE.measure_ne_top (huF_E i) B⟩
  have hfiniteZeta : ∀ i ∈ slopes, GammaE.measure (uF i - uE i) B ≠ ⊤ := fun i _ =>
    GammaE.measure_ne_top (E.domain.sub_mem (huF_E i) (huE i)) B
  have hnu_formula :
      ((ENNReal.ofReal D⁻¹ •
        (∑ i ∈ slopes, (GammaE.measure (uE i) + GammaE.measure (uF i)))) B).toReal
        = nu := by
    rw [hnudef]
    exact aux_lem_relvar_normalized_sum_toReal D hD slopes
      (fun i => GammaE.measure (uE i) + GammaE.measure (uF i)) B hfiniteNu
  have hzeta_formula :
      ((ENNReal.ofReal D⁻¹ •
        (∑ i ∈ slopes, GammaE.measure (uF i - uE i))) B).toReal = ze := by
    rw [hzedef]
    exact aux_lem_relvar_normalized_sum_toReal D hD slopes
      (fun i => GammaE.measure (uF i - uE i)) B hfiniteZeta
  have hnu_nonneg : 0 ≤ nu := by
    rw [hnudef]; positivity
  have hze_nonneg : 0 ≤ ze := by
    rw [hzedef]; positivity
  have hDnu : D * nu = ∑ i ∈ slopes,
      ((GammaE.measure (uE i) + GammaE.measure (uF i)) B).toReal := by
    rw [hnudef]; field_simp
  have hDze : D * ze = ∑ i ∈ slopes, (GammaE.measure (uF i - uE i) B).toReal := by
    rw [hzedef]; field_simp
  have hadd : ∀ j, ((GammaE.measure (uE j) + GammaE.measure (uF j)) B).toReal =
      (GammaE.measure (uE j) B).toReal + (GammaE.measure (uF j) B).toReal := by
    intro j
    rw [Measure.add_apply, ENNReal.toReal_add (GammaE.measure_ne_top (huE j) B)
      (GammaE.measure_ne_top (huF_E j) B)]
  have hsumZe_le :
      (∑ i ∈ slopes, (GammaE.measure (uF i - uE i) B).toReal) ≤
        4 * (∑ i ∈ slopes,
          ((GammaE.measure (uE i) + GammaE.measure (uF i)) B).toReal) := by
    have hpoint : ∀ i ∈ slopes,
        (GammaE.measure (uF i - uE i) B).toReal ≤
          4 * ((GammaE.measure (uE i) + GammaE.measure (uF i)) B).toReal := by
      intro i _
      have hwi := aux_lem_relvar_measure_sub_le GammaE (huF_E i) (huE i) hB
      rw [hadd i]
      nlinarith only [hwi, ENNReal.toReal_nonneg (a := GammaE.measure (uE i) B),
        ENNReal.toReal_nonneg (a := GammaE.measure (uF i) B)]
    calc
      (∑ i ∈ slopes, (GammaE.measure (uF i - uE i) B).toReal) ≤
          ∑ i ∈ slopes,
            4 * ((GammaE.measure (uE i) + GammaE.measure (uF i)) B).toReal :=
        Finset.sum_le_sum hpoint
      _ = 4 * (∑ i ∈ slopes,
          ((GammaE.measure (uE i) + GammaE.measure (uF i)) B).toReal) := by
        rw [Finset.mul_sum]
  have hze_le : ze ≤ 4 * nu := by
    have hmul : D * ze ≤ 4 * (D * nu) := by
      rw [hDze, hDnu]; exact hsumZe_le
    nlinarith only [hmul, hD]
  have hze_sqrt : ze ≤ 2 * Real.sqrt (nu * ze) := by
    have hprod : ze ^ 2 ≤ 4 * (nu * ze) := by
      nlinarith only [hze_le, hze_nonneg]
    have hs := Real.sq_sqrt (mul_nonneg hnu_nonneg hze_nonneg)
    have hr : 0 ≤ Real.sqrt (nu * ze) := Real.sqrt_nonneg _
    nlinarith only [hprod, hs, hr, hze_nonneg]
  have hsingle_inj : Function.Injective
      (fun i : Fin d => Pi.single i (1 : ℝ)) := by
    intro i j hij
    by_contra hne
    have hh : (Pi.single i 1 : Fin d → ℝ) i = (Pi.single j 1 : Fin d → ℝ) i :=
      congrFun hij i
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at hh
    exact one_ne_zero hh
  have hscoords_sub :
      (Finset.univ.image (fun i : Fin d => Pi.single i (1 : ℝ))) ⊆ slopes := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    exact (hslopes _).2 (Or.inl ⟨i, rfl⟩)
  have hcoordE_le :
      (∑ i : Fin d, (GammaE.measure (uE (Pi.single i 1)) B).toReal) ≤ D * nu := by
    have hstep1 :
        (∑ i : Fin d, (GammaE.measure (uE (Pi.single i 1)) B).toReal) ≤
          ∑ i : Fin d,
            ((GammaE.measure (uE (Pi.single i 1)) +
              GammaE.measure (uF (Pi.single i 1))) B).toReal := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [hadd (Pi.single i 1)]
      linarith [ENNReal.toReal_nonneg
        (a := GammaE.measure (uF (Pi.single i 1)) B)]
    have hstep2 :
        (∑ i : Fin d,
          ((GammaE.measure (uE (Pi.single i 1)) +
            GammaE.measure (uF (Pi.single i 1))) B).toReal) =
          ∑ x ∈ (Finset.univ.image (fun i : Fin d => Pi.single i (1 : ℝ))),
            ((GammaE.measure (uE x) + GammaE.measure (uF x)) B).toReal := by
      rw [Finset.sum_image hsingle_inj.injOn]
    have hstep3 :
        (∑ x ∈ (Finset.univ.image (fun i : Fin d => Pi.single i (1 : ℝ))),
          ((GammaE.measure (uE x) + GammaE.measure (uF x)) B).toReal) ≤
        ∑ x ∈ slopes, ((GammaE.measure (uE x) + GammaE.measure (uF x)) B).toReal :=
      Finset.sum_le_sum_of_subset_of_nonneg hscoords_sub
        (fun _ _ _ => ENNReal.toReal_nonneg)
    calc
      (∑ i : Fin d, (GammaE.measure (uE (Pi.single i 1)) B).toReal) ≤ _ := hstep1
      _ = _ := hstep2
      _ ≤ _ := hstep3
      _ = D * nu := hDnu.symm
  exact ⟨hnu_nonneg, hze_nonneg, hDnu, hDze, hze_sqrt, hnu_formula,
    hzeta_formula, hcoordE_le⟩

/-- The three bounds at the fixed slope `p`. -/
lemma aux_lem_relvar_p_bounds
    (ctx : aux_lem_relvar_Ctx C0 Q z r hr slopes E F Eg Fg GammaE GammaF GammaEg
      GammaFg V0 m M c g B G uE uF uEg uFg QE QF QEg QFg D Dg nu ze IE IF)
    (p : Fin d → ℝ) (hp : p ∈ slopes) :
    (GammaE.measure (uE p) B).toReal ≤ D * nu ∧
      (GammaE.measure (uF p - uE p) B).toReal ≤ D * ze ∧
      Real.sqrt ((GammaE.measure (uE p) B).toReal *
        (GammaE.measure (uF p - uE p) B).toReal) ≤ D * Real.sqrt (nu * ze) := by
  obtain ⟨hnu_nonneg, hze_nonneg, hDnu, hDze, -, -, -, -⟩ :=
    aux_lem_relvar_nu_basics ctx
  obtain ⟨hC0, hd, hslopes, hQ, hinside, hdomEF, hdomEg, hdomFg, hzero, hm, hmM,
    hM, hmc, hcM, horder, hg, hB, hBq, hsupp, hG, hbdd, hweightE, hweightF,
    hweightE_cross, hweightF_cross, huE, huF, huEg, huFg, htraceF, htraceEg,
    htraceFg, hminE, hminF, hminEg, hminFg, hQE, hQF, hQEg, hQFg, hDdef, hD,
    hDgdef, hnudef, hzedef, hIEdef, hIFdef⟩ := ctx
  have huF_E : ∀ i, uF i ∈ E.domain := fun i => by rw [hdomEF]; exact huF i
  have hadd : ∀ j, ((GammaE.measure (uE j) + GammaE.measure (uF j)) B).toReal =
      (GammaE.measure (uE j) B).toReal + (GammaE.measure (uF j) B).toReal := by
    intro j
    rw [Measure.add_apply, ENNReal.toReal_add (GammaE.measure_ne_top (huE j) B)
      (GammaE.measure_ne_top (huF_E j) B)]
  have hEu_le : (GammaE.measure (uE p) B).toReal ≤ D * nu := by
    have hs0 : ((GammaE.measure (uE p) + GammaE.measure (uF p)) B).toReal ≤
        ∑ x ∈ slopes,
          ((GammaE.measure (uE x) + GammaE.measure (uF x)) B).toReal :=
      Finset.single_le_sum (f := fun j =>
        ((GammaE.measure (uE j) + GammaE.measure (uF j)) B).toReal)
        (fun _ _ => ENNReal.toReal_nonneg) hp
    rw [hadd p] at hs0
    have := ENNReal.toReal_nonneg (a := GammaE.measure (uF p) B)
    rw [hDnu]; linarith
  have hw_le_ze : (GammaE.measure (uF p - uE p) B).toReal ≤ D * ze := by
    have hs : (GammaE.measure (uF p - uE p) B).toReal ≤
        ∑ x ∈ slopes, (GammaE.measure (uF x - uE x) B).toReal :=
      Finset.single_le_sum (f := fun j => (GammaE.measure (uF j - uE j) B).toReal)
        (fun _ _ => ENNReal.toReal_nonneg) hp
    rw [hDze]; exact hs
  refine ⟨hEu_le, hw_le_ze, ?_⟩
  have hprod : (GammaE.measure (uE p) B).toReal *
      (GammaE.measure (uF p - uE p) B).toReal ≤ (D * nu) * (D * ze) :=
    mul_le_mul hEu_le hw_le_ze ENNReal.toReal_nonneg
      (mul_nonneg (le_of_lt hD) hnu_nonneg)
  calc
    Real.sqrt ((GammaE.measure (uE p) B).toReal *
        (GammaE.measure (uF p - uE p) B).toReal) ≤
        Real.sqrt ((D * nu) * (D * ze)) := Real.sqrt_le_sqrt hprod
    _ = D * Real.sqrt (nu * ze) := by
      rw [show (D * nu) * (D * ze) = D ^ 2 * (nu * ze) by ring,
        Real.sqrt_mul (sq_nonneg D), Real.sqrt_sq_eq_abs, abs_of_pos hD]


/-- The pointwise perturbation bounds supplied by `cor_14` at one slope. -/
lemma aux_lem_relvar_cor14_pointwise
    (ctx : aux_lem_relvar_Ctx C0 Q z r hr slopes E F Eg Fg GammaE GammaF GammaEg
      GammaFg V0 m M c g B G uE uF uEg uFg QE QF QEg QFg D Dg nu ze IE IF)
    (p : Fin d → ℝ) :
    (GammaEg.measure (uEg p - uE p)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        G ^ 2 * Real.exp (3 * G) * (GammaE.measure (uE p) B).toReal ∧
      |QEg p - QE p| ≤
        2 * G * Real.exp (4 * G) * (GammaE.measure (uE p) B).toReal ∧
      Real.exp (-G) * QE p ≤ QEg p ∧
      (GammaE.measure (uEg p - uE p) B).toReal ≤
        G ^ 2 * Real.exp (4 * G) * (GammaE.measure (uE p) B).toReal ∧
      (GammaE.measure (uEg p - uE p)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        G ^ 2 * Real.exp (4 * G) * (GammaE.measure (uE p) B).toReal := by
  obtain ⟨hC0, hd, hslopes, hQ, hinside, hdomEF, hdomEg, hdomFg, hzero, hm, hmM,
    hM, hmc, hcM, horder, hg, hB, hBq, hsupp, hG, hbdd, hweightE, hweightF,
    hweightE_cross, hweightF_cross, huE, huF, huEg, huFg, htraceF, htraceEg,
    htraceFg, hminE, hminF, hminEg, hminFg, hQE, hQF, hQEg, hQFg, hDdef, hD,
    hDgdef, hnudef, hzedef, hIEdef, hIFdef⟩ := ctx
  have hqmeas : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  have hgbound : ∀ x, |g x| ≤ G := fun x => hG.1 ⟨x, rfl⟩
  have hcorE := ((cor_14).2 d Q z r hr hinside E Eg GammaE GammaEg hdomEg V0 hzero
    g hg B hB hBq hsupp G hG hbdd hweightE).1 (uE p) (uEg p) (huE p) (huEg p)
    (htraceEg p) (hminE p) (hminEg p)
  have hcorE_energy := hcorE.1
  have he_p : uEg p - uE p ∈ E.domain :=
    E.domain.sub_mem (by rw [← hdomEg]; exact huEg p) (huE p)
  have he_Eg : uEg p - uE p ∈ Eg.domain :=
    Eg.domain.sub_mem (huEg p) (by rw [hdomEg]; exact huE p)
  have hboundsE : ∀ (v : DomainL2 Q), v ∈ E.domain →
      ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
        Real.exp (-G) * (GammaE.measure v A).toReal ≤
            (GammaEg.measure v A).toReal ∧
          (GammaEg.measure v A).toReal ≤
            Real.exp G * (GammaE.measure v A).toReal := fun v hv A hA =>
    aux_lem_relvar_weighted_measure_bounds GammaE GammaEg hdomEg g hg G hgbound
      hweightE hv hA
  have hEg_e_B : (GammaEg.measure (uEg p - uE p) B).toReal ≤
      (GammaEg.measure (uEg p - uE p)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal :=
    ENNReal.toReal_mono (GammaEg.measure_ne_top he_Eg _) (measure_mono hBq)
  have hEe_le : (GammaE.measure (uEg p - uE p) B).toReal ≤
      G ^ 2 * Real.exp (4 * G) * (GammaE.measure (uE p) B).toReal := by
    have hE_e_B : (GammaE.measure (uEg p - uE p) B).toReal ≤
        Real.exp G * (GammaEg.measure (uEg p - uE p) B).toReal :=
      aux_lem_relvar_exp_lower G _ _ (hboundsE _ he_p B hB).1
    calc
      (GammaE.measure (uEg p - uE p) B).toReal ≤
          Real.exp G * (GammaEg.measure (uEg p - uE p) B).toReal := hE_e_B
      _ ≤ Real.exp G * (G ^ 2 * Real.exp (3 * G) *
          (GammaE.measure (uE p) B).toReal) :=
        mul_le_mul_of_nonneg_left (hEg_e_B.trans hcorE_energy) (Real.exp_nonneg _)
      _ = G ^ 2 * Real.exp (4 * G) * (GammaE.measure (uE p) B).toReal :=
        aux_lem_relvar_exp_four_mul G _
  have hEe_q : (GammaE.measure (uEg p - uE p)
      (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
      G ^ 2 * Real.exp (4 * G) * (GammaE.measure (uE p) B).toReal := by
    calc
      (GammaE.measure (uEg p - uE p)
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
          Real.exp G * (GammaEg.measure (uEg p - uE p)
            (centeredCube z r hr : Set (SpatialCoordinates d))).toReal :=
        aux_lem_relvar_exp_lower G _ _
          (hboundsE _ he_p (centeredCube z r hr : Set (SpatialCoordinates d))
            hqmeas).1
      _ ≤ Real.exp G * (G ^ 2 * Real.exp (3 * G) *
          (GammaE.measure (uE p) B).toReal) :=
        mul_le_mul_of_nonneg_left hcorE_energy (Real.exp_nonneg _)
      _ = G ^ 2 * Real.exp (4 * G) * (GammaE.measure (uE p) B).toReal :=
        aux_lem_relvar_exp_four_mul G _
  refine ⟨hcorE_energy, ?_, ?_, hEe_le, hEe_q⟩
  · simpa only [hQEg, hQE] using hcorE.2.2.1
  · simpa only [hQEg, hQE] using hcorE.2.2.2.1.1

/-- Lower bound and variation of the weighted denominator `Dg`. -/
lemma aux_lem_relvar_Dg_bounds
    (ctx : aux_lem_relvar_Ctx C0 Q z r hr slopes E F Eg Fg GammaE GammaF GammaEg
      GammaFg V0 m M c g B G uE uF uEg uFg QE QF QEg QFg D Dg nu ze IE IF) :
    Real.exp (-G) * D ≤ Dg ∧ 0 < Dg ∧
      |Dg - D| ≤
        (10 * (C0 + 1)) * G * Real.exp ((10 * (C0 + 1)) * G) * D * nu := by
  obtain ⟨hnu_nonneg, -, -, -, -, -, -, hcoordE_le⟩ := aux_lem_relvar_nu_basics ctx
  have hpt := fun i : Fin d => aux_lem_relvar_cor14_pointwise ctx (Pi.single i 1)
  obtain ⟨hC0, hd, hslopes, hQ, hinside, hdomEF, hdomEg, hdomFg, hzero, hm, hmM,
    hM, hmc, hcM, horder, hg, hB, hBq, hsupp, hG, hbdd, hweightE, hweightF,
    hweightE_cross, hweightF_cross, huE, huF, huEg, huFg, htraceF, htraceEg,
    htraceFg, hminE, hminF, hminEg, hminFg, hQE, hQF, hQEg, hQFg, hDdef, hD,
    hDgdef, hnudef, hzedef, hIEdef, hIFdef⟩ := ctx
  have hG0 : 0 ≤ G := le_trans (abs_nonneg (g (Classical.arbitrary _)))
    (hG.1 ⟨Classical.arbitrary _, rfl⟩)
  have hC0pos : 0 < C0 := lt_of_lt_of_le zero_lt_one hC0
  have hDnu_nonneg : 0 ≤ D * nu := mul_nonneg (le_of_lt hD) hnu_nonneg
  have hDg_lower : Real.exp (-G) * D ≤ Dg := by
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
      (fun i _ => (hpt i).2.2.1)
    calc
      Real.exp (-G) * D = ∑ i : Fin d, Real.exp (-G) * QE (Pi.single i 1) := by
        rw [hDdef, Finset.mul_sum]
      _ ≤ ∑ i : Fin d, QEg (Pi.single i 1) := hsum
      _ = Dg := hDgdef.symm
  have hDg_diff : |Dg - D| ≤
      (10 * (C0 + 1)) * G * Real.exp ((10 * (C0 + 1)) * G) * D * nu := by
    have hsumabs := Finset.abs_sum_le_sum_abs
      (fun i : Fin d => QEg (Pi.single i 1) - QE (Pi.single i 1))
      (Finset.univ : Finset (Fin d))
    have hsumcorr :
        (∑ i : Fin d, |QEg (Pi.single i 1) - QE (Pi.single i 1)|) ≤
          2 * G * Real.exp (4 * G) *
            (∑ i : Fin d, (GammaE.measure (uE (Pi.single i 1)) B).toReal) := by
      refine le_trans (Finset.sum_le_sum (fun i _ => (hpt i).2.1)) ?_
      rw [Finset.mul_sum]
    have hcoef : 2 * Real.exp (4 * G) ≤
        (10 * (C0 + 1)) * Real.exp ((10 * (C0 + 1)) * G) := by
      have hconst : (2 : ℝ) ≤ 10 * (C0 + 1) := by linarith
      have hexp : Real.exp (4 * G) ≤ Real.exp ((10 * (C0 + 1)) * G) := by
        apply Real.exp_le_exp.mpr
        gcongr
        linarith
      exact mul_le_mul hconst hexp (Real.exp_nonneg _) (by positivity)
    calc
      |Dg - D| = |∑ i : Fin d, (QEg (Pi.single i 1) - QE (Pi.single i 1))| := by
        rw [hDgdef, hDdef, Finset.sum_sub_distrib]
      _ ≤ ∑ i : Fin d, |QEg (Pi.single i 1) - QE (Pi.single i 1)| := hsumabs
      _ ≤ 2 * G * Real.exp (4 * G) *
          (∑ i : Fin d, (GammaE.measure (uE (Pi.single i 1)) B).toReal) := hsumcorr
      _ ≤ 2 * G * Real.exp (4 * G) * (D * nu) :=
        mul_le_mul_of_nonneg_left hcoordE_le (by positivity)
      _ ≤ (10 * (C0 + 1)) * G * Real.exp ((10 * (C0 + 1)) * G) * D * nu := by
        calc
          2 * G * Real.exp (4 * G) * (D * nu) =
              (2 * Real.exp (4 * G)) * (G * (D * nu)) := by ring
          _ ≤ ((10 * (C0 + 1)) * Real.exp ((10 * (C0 + 1)) * G)) *
              (G * (D * nu)) :=
            mul_le_mul_of_nonneg_right hcoef (mul_nonneg hG0 hDnu_nonneg)
          _ = (10 * (C0 + 1)) * G * Real.exp ((10 * (C0 + 1)) * G) * D * nu := by
            ring
  exact ⟨hDg_lower, lt_of_lt_of_le (mul_pos (Real.exp_pos (-G)) hD) hDg_lower,
    hDg_diff⟩


/-- The setwise Cauchy–Schwarz bound for the difference form `Γ_F - cΓ_E`,
transported from `lem_diff` along the presentation `Q = centeredCube zQ rQ hrQ`. -/
lemma aux_lem_relvar_TVQ
    (ctx : aux_lem_relvar_Ctx C0 Q z r hr slopes E F Eg Fg GammaE GammaF GammaEg
      GammaFg V0 m M c g B G uE uF uEg uFg QE QF QEg QFg D Dg nu ze IE IF)
    (p : Fin d → ℝ) :
    ∀ (x y : DomainL2 Q), x ∈ E.domain → y ∈ E.domain →
      ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
        ((GammaF.cross x y - c • GammaE.cross x y).totalVariation A).toReal ≤
          (M - m) * Real.sqrt ((GammaE.measure x A).toReal *
            (GammaE.measure y A).toReal) := by
  obtain ⟨hC0, hd, hslopes, hQ, hinside, hdomEF, hdomEg, hdomFg, hzero, hm, hmM,
    hM, hmc, hcM, horder, hg, hB, hBq, hsupp, hG, hbdd, hweightE, hweightF,
    hweightE_cross, hweightF_cross, huE, huF, huEg, huFg, htraceF, htraceEg,
    htraceFg, hminE, hminF, hminEg, hminFg, hQE, hQF, hQEg, hQFg, hDdef, hD,
    hDgdef, hnudef, hzedef, hIEdef, hIFdef⟩ := ctx
  have hC0pos : 0 < C0 := lt_of_lt_of_le zero_lt_one hC0
  have hmpos : 0 < m := lt_of_lt_of_le (inv_pos.mpr hC0pos) hm
  have hVdomF : V0 ≤ F.domain := by
    intro v hv; rw [← hdomEF]; exact hzero.le_domain hv
  have hminE0 : ∀ v ∈ V0,
      (GammaE.measure (uE p) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        (GammaE.measure (uE p + v)
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
    intro v hv
    apply hminE p (uE p + v) (E.domain.add_mem (huE p) (hzero.le_domain hv))
    simpa only [add_sub_cancel_left] using hv
  have hminFbase : ∀ v ∈ F.domain, v - uF p ∈ V0 →
      (GammaF.measure (uF p) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        (GammaF.measure v (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
    intro v hv hv0
    apply hminF p v hv
    rw [show v - uE p = (v - uF p) + (uF p - uE p) by abel]
    exact V0.add_mem hv0 (htraceF p)
  obtain ⟨zQ, rQ, hrQ, hQeq⟩ := hQ
  have hinsideQ : closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d)) := by
    simpa [hQeq] using hinside
  let E0 : DirichletForm.ClosedForm
      (volume.restrict (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))) :=
    hQeq ▸ E
  let F0 : DirichletForm.ClosedForm
      (volume.restrict (centeredCube zQ rQ hrQ : Set (SpatialCoordinates d))) :=
    hQeq ▸ F
  let GammaE0 : DirichletForm.EnergyMeasure E0 := by
    dsimp [E0]; cases hQeq; exact GammaE
  let GammaF0 : DirichletForm.EnergyMeasure F0 := by
    dsimp [F0]; cases hQeq; exact GammaF
  let V00 : Submodule ℝ (DomainL2 (centeredCube zQ rQ hrQ)) := hQeq ▸ V0
  have hdomEF0 : E0.domain = F0.domain := by
    dsimp [E0, F0]; cases hQeq; exact hdomEF
  have hzero0 : DirichletForm.IsKilledDomain E0
      (centeredCube z r hr : Set (SpatialCoordinates d)) V00 := by
    dsimp [E0, V00]; cases hQeq; exact hzero
  have huE0 : (hQeq ▸ (uE p)) ∈ E0.domain := by
    dsimp [E0]; cases hQeq; exact huE p
  have huF0 : (hQeq ▸ (uF p)) ∈ F0.domain := by
    dsimp [F0]; cases hQeq; exact huF p
  have htraceF0 : (hQeq ▸ (uF p)) - (hQeq ▸ (uE p)) ∈ V00 := by
    dsimp [V00]; cases hQeq; exact htraceF p
  have hminE00 : ∀ v ∈ V00,
      (GammaE0.measure (hQeq ▸ (uE p))
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        (GammaE0.measure ((hQeq ▸ (uE p)) + v)
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
    dsimp [GammaE0, V00]; cases hQeq; exact hminE0
  have hminF00 : ∀ v ∈ V00,
      (GammaF0.measure (hQeq ▸ (uF p))
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        (GammaF0.measure ((hQeq ▸ (uF p)) + v)
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
    dsimp [GammaF0, V00]
    cases hQeq
    exact fun v hv => by
      apply hminFbase (uF p + v) (F.domain.add_mem (huF p) (hVdomF hv))
      simpa only [add_sub_cancel_left] using hv
  have hdiff := lem_diff d hd zQ rQ hrQ z r hr hinsideQ E0 F0 GammaE0 GammaF0
    hdomEF0 V00 hzero0 m M c hmpos hmc hcM (by
      intro u hu A hA
      dsimp [GammaE0, GammaF0, E0, F0]
      cases hQeq
      exact horder u hu A hA) (hQeq ▸ (uE p)) (hQeq ▸ (uF p)) huE0 huF0 htraceF0
    hminE00 hminF00
  intro x y hx hy A hA
  have ht := hdiff.2.2 (hQeq ▸ x) (hQeq ▸ y)
    (by dsimp [E0]; cases hQeq; exact hx)
    (by dsimp [E0]; cases hQeq; exact hy) A hA
  dsimp [GammaF0, GammaE0, F0, E0] at ht
  cases hQeq
  exact ht


lemma aux_lem_relvar_cs_bound (K G X zq a b : ℝ) (hK : 0 ≤ K) (hG : 0 ≤ G)
    (hX : 0 ≤ X) (hzq : 0 ≤ zq) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : a ≤ K * G ^ 2 * Real.exp (5 * G) * X)
    (hb : b ≤ K * Real.exp (2 * G) * zq) :
    Real.sqrt a * Real.sqrt b ≤
      K * G * Real.exp (4 * G) * Real.sqrt (X * zq) := by
  rw [← Real.sqrt_mul ha0]
  have key : (K * G ^ 2 * Real.exp (5 * G) * X) * (K * Real.exp (2 * G) * zq) =
      K ^ 2 * G ^ 2 * Real.exp (7 * G) * (X * zq) := by
    rw [show (7 : ℝ) * G = 5 * G + 2 * G by ring, Real.exp_add]; ring
  have key2 : (K * G * Real.exp (4 * G)) ^ 2 * (X * zq) =
      K ^ 2 * G ^ 2 * Real.exp (8 * G) * (X * zq) := by
    rw [show (8 : ℝ) * G = 4 * G + 4 * G by ring, Real.exp_add]; ring
  have hexp : Real.exp (7 * G) ≤ Real.exp (8 * G) :=
    Real.exp_le_exp.2 (by linarith)
  have hprod : a * b ≤ (K * G * Real.exp (4 * G)) ^ 2 * (X * zq) := by
    refine le_trans (mul_le_mul ha hb hb0 (by positivity)) ?_
    rw [key, key2]
    calc
      K ^ 2 * G ^ 2 * Real.exp (7 * G) * (X * zq) =
          (K ^ 2 * G ^ 2 * (X * zq)) * Real.exp (7 * G) := by ring
      _ ≤ (K ^ 2 * G ^ 2 * (X * zq)) * Real.exp (8 * G) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = K ^ 2 * G ^ 2 * Real.exp (8 * G) * (X * zq) := by ring
  calc
    Real.sqrt (a * b) ≤ Real.sqrt ((K * G * Real.exp (4 * G)) ^ 2 * (X * zq)) :=
      Real.sqrt_le_sqrt hprod
    _ = K * G * Real.exp (4 * G) * Real.sqrt (X * zq) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

/-- The unweighted numerator is controlled by the endpoint gap. -/
lemma aux_lem_relvar_base_D
    (ctx : aux_lem_relvar_Ctx C0 Q z r hr slopes E F Eg Fg GammaE GammaF GammaEg
      GammaFg V0 m M c g B G uE uF uEg uFg QE QF QEg QFg D Dg nu ze IE IF)
    (p : Fin d → ℝ) (hp : p ∈ slopes) :
    |QF p - c * QE p| ≤ (10 * (C0 + 1)) * (M - m) * D := by
  obtain ⟨hC0, hd, hslopes, hQ, hinside, hdomEF, hdomEg, hdomFg, hzero, hm, hmM,
    hM, hmc, hcM, horder, hg, hB, hBq, hsupp, hG, hbdd, hweightE, hweightF,
    hweightE_cross, hweightF_cross, huE, huF, huEg, huFg, htraceF, htraceEg,
    htraceFg, hminE, hminF, hminEg, hminFg, hQE, hQF, hQEg, hQFg, hDdef, hD,
    hDgdef, hnudef, hzedef, hIEdef, hIFdef⟩ := ctx
  have hqmeas : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  have hC0pos : 0 < C0 := lt_of_lt_of_le zero_lt_one hC0
  have hmpos : 0 < m := lt_of_lt_of_le (inv_pos.mpr hC0pos) hm
  have hdel : 0 ≤ M - m := sub_nonneg.mpr hmM
  have huF_E : uF p ∈ E.domain := by rw [hdomEF]; exact huF p
  have hQE_nonneg : ∀ v : Fin d → ℝ, 0 ≤ QE v := by
    intro v; rw [hQE]; exact ENNReal.toReal_nonneg
  have hQE_coord_le_D : ∀ i : Fin d, QE (Pi.single i 1) ≤ D := by
    intro i
    rw [hDdef]
    exact Finset.single_le_sum (f := fun j => QE (Pi.single j 1))
      (fun j _ => hQE_nonneg (Pi.single j 1)) (Finset.mem_univ i)
  have hQE_add_le : ∀ a b : Fin d → ℝ, QE (a + b) ≤ 2 * QE a + 2 * QE b := by
    intro a b
    have hminus : 0 ≤ QE (a - b) := hQE_nonneg (a - b)
    have hplus := QuadraticMap.map_add (⇑QE) a b
    have hsub := QuadraticMap.map_add (⇑QE) a (-b)
    rw [← sub_eq_add_neg, QE.map_neg, QuadraticMap.polar_neg_right] at hsub
    linarith
  have hQE_p_le : QE p ≤ 4 * D := by
    rcases (hslopes p).1 hp with ⟨i, rfl⟩ | ⟨i, j, rfl⟩
    · exact (hQE_coord_le_D i).trans (by linarith)
    · calc
        QE (Pi.single i 1 + Pi.single j 1) ≤
            2 * QE (Pi.single i 1) + 2 * QE (Pi.single j 1) := hQE_add_le _ _
        _ ≤ 4 * D := by
          have h1 := hQE_coord_le_D i
          have h2 := hQE_coord_le_D j
          linarith
  have hbase_abs : |QF p - c * QE p| ≤ (M - m) * QE p := by
    have hminF_uE := hminF p (uE p) (by rw [← hdomEF]; exact huE p)
      (by simpa only [sub_self] using V0.zero_mem)
    have hminE_uF := hminE p (uF p) huF_E (htraceF p)
    have hRF_low : m * (GammaE.measure (uE p)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        (GammaF.measure (uF p)
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
      have hmul := mul_le_mul_of_nonneg_left hminE_uF (le_of_lt hmpos)
      exact hmul.trans ((horder (uF p) huF_E
        (centeredCube z r hr : Set (SpatialCoordinates d)) hqmeas).1)
    have hRF_high : (GammaF.measure (uF p)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        M * (GammaE.measure (uE p)
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal :=
      hminF_uE.trans ((horder (uE p) (huE p)
        (centeredCube z r hr : Set (SpatialCoordinates d)) hqmeas).2)
    rw [hQF, hQE, abs_le]
    constructor <;> nlinarith only [hRF_low, hRF_high, hmc, hcM,
      ENNReal.toReal_nonneg (a := GammaE.measure (uE p)
        (centeredCube z r hr : Set (SpatialCoordinates d)))]
  calc
    |QF p - c * QE p| ≤ (M - m) * QE p := hbase_abs
    _ ≤ (M - m) * (4 * D) := mul_le_mul_of_nonneg_left hQE_p_le hdel
    _ = 4 * ((M - m) * D) := by ring
    _ ≤ (10 * (C0 + 1)) * ((M - m) * D) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hdel hD.le)
    _ = (10 * (C0 + 1)) * (M - m) * D := by ring


lemma aux_lem_relvar_sqrt_scale (K a b : ℝ) (hK : 0 ≤ K) :
    Real.sqrt ((K * a) * (K * b)) = K * Real.sqrt (a * b) := by
  rw [show (K * a) * (K * b) = K ^ 2 * (a * b) by ring,
    Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK]

lemma aux_lem_relvar_sqrt_self (a : ℝ) (ha : 0 ≤ a) :
    Real.sqrt (a * a) = a := by
  rw [show a * a = a ^ 2 by ring, Real.sqrt_sq ha]

lemma aux_lem_relvar_sqrt_pert (G a e : ℝ) (hG : 0 ≤ G) (ha : 0 ≤ a)
    (he : e ≤ G ^ 2 * Real.exp (4 * G) * a) :
    Real.sqrt (a * e) ≤ G * Real.exp (2 * G) * a := by
  have hexp : Real.exp (2 * G) ^ 2 = Real.exp (4 * G) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hle : a * e ≤ (G * Real.exp (2 * G) * a) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left he ha
    have hsq : (G * Real.exp (2 * G) * a) ^ 2 =
        G ^ 2 * Real.exp (4 * G) * a * a := by rw [← hexp]; ring
    rw [hsq]
    calc
      a * e ≤ a * (G ^ 2 * Real.exp (4 * G) * a) := h
      _ = G ^ 2 * Real.exp (4 * G) * a * a := by ring
  calc
    Real.sqrt (a * e) ≤ Real.sqrt ((G * Real.exp (2 * G) * a) ^ 2) :=
      Real.sqrt_le_sqrt hle
    _ = G * Real.exp (2 * G) * a := Real.sqrt_sq (by positivity)

/-- The five term bounds of the numerator decomposition, at the fixed slope. -/
lemma aux_lem_relvar_term_bounds
    (ctx : aux_lem_relvar_Ctx C0 Q z r hr slopes E F Eg Fg GammaE GammaF GammaEg
      GammaFg V0 m M c g B G uE uF uEg uFg QE QF QEg QFg D Dg nu ze IE IF)
    (p : Fin d → ℝ) (hp : p ∈ slopes) :
    |IF (uE p) (uE p) - c * IE (uE p) (uE p)| ≤
        G * Real.exp G * (M - m) * (D * nu) ∧
      |IF (uE p) (uF p - uE p)| ≤
        2 * G * Real.exp G * M * (D * Real.sqrt (nu * ze)) ∧
      |IF (uF p - uE p) (uF p - uE p)| ≤ 2 * G * Real.exp G * M * (D * ze) ∧
      |IF (uE p) (uEg p - uE p) - c * IE (uE p) (uEg p - uE p)| ≤
        G ^ 2 * Real.exp (3 * G) * (M - m) * (D * nu) ∧
      |IF (uF p - uE p) (uEg p - uE p)| ≤
        2 * M * G ^ 2 * Real.exp (3 * G) * (D * Real.sqrt (nu * ze)) ∧
      |GammaFg.cross (uEg p - uE p) ((uFg p - uF p) - (uEg p - uE p))
          (centeredCube z r hr : Set (SpatialCoordinates d))| ≤
        M * G * Real.exp (4 * G) *
          Real.sqrt ((D * nu) *
            (GammaEg.measure ((uFg p - uF p) - (uEg p - uE p))
              (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) ∧
      (GammaFg.measure ((uFg p - uF p) - (uEg p - uE p))
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        M * Real.exp (2 * G) *
          (GammaEg.measure ((uFg p - uF p) - (uEg p - uE p))
            (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
  have hTVQ := aux_lem_relvar_TVQ ctx p
  obtain ⟨hEu_le, hw_le_ze, hsqrt_uw⟩ := aux_lem_relvar_p_bounds ctx p hp
  obtain ⟨-, -, -, hEe_le, hEe_q⟩ := aux_lem_relvar_cor14_pointwise ctx p
  obtain ⟨hnu_nonneg, hze_nonneg, -, -, -, -, -, -⟩ := aux_lem_relvar_nu_basics ctx
  obtain ⟨hC0, hd, hslopes, hQ, hinside, hdomEF, hdomEg, hdomFg, hzero, hm, hmM,
    hM, hmc, hcM, horder, hg, hB, hBq, hsupp, hG, hbdd, hweightE, hweightF,
    hweightE_cross, hweightF_cross, huE, huF, huEg, huFg, htraceF, htraceEg,
    htraceFg, hminE, hminF, hminEg, hminFg, hQE, hQF, hQEg, hQFg, hDdef, hD,
    hDgdef, hnudef, hzedef, hIEdef, hIFdef⟩ := ctx
  have hqmeas : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  have hC0pos : 0 < C0 := lt_of_lt_of_le zero_lt_one hC0
  have hmpos : 0 < m := lt_of_lt_of_le (inv_pos.mpr hC0pos) hm
  have hcpos : 0 < c := lt_of_lt_of_le hmpos hmc
  have hMpos : 0 < M := lt_of_lt_of_le hmpos hmM
  have hM0 : (0 : ℝ) ≤ M := hMpos.le
  have hdel : 0 ≤ M - m := sub_nonneg.mpr hmM
  have hG0 : 0 ≤ G := le_trans (abs_nonneg (g (Classical.arbitrary _)))
    (hG.1 ⟨Classical.arbitrary _, rfl⟩)
  have hgbound : ∀ x, |g x| ≤ G := fun x => hG.1 ⟨x, rfl⟩
  have hf0 : Measurable (fun x : SpatialCoordinates d => Real.exp (g x) - 1) :=
    hg.exp.sub measurable_const
  have hK : (0 : ℝ) ≤ G * Real.exp G := mul_nonneg hG0 (Real.exp_nonneg _)
  have hf0bound : ∀ x : SpatialCoordinates d,
      |Real.exp (g x) - 1| ≤ G * Real.exp G := fun x =>
    aux_lem_relvar_exp_sub_one_bound G (g x) hG0 (hgbound x)
  have hexp_bound : ∀ x : SpatialCoordinates d, |Real.exp (g x)| ≤ Real.exp G := by
    intro x
    rw [abs_of_nonneg (Real.exp_nonneg _)]
    exact (Real.exp_le_exp).2 ((abs_le.mp (hgbound x)).2)
  -- memberships
  have hVdomF : V0 ≤ F.domain := by
    intro v hv; rw [← hdomEF]; exact hzero.le_domain hv
  have hVdomFg : V0 ≤ Fg.domain := by
    intro v hv; rw [hdomFg]; exact hzero.le_domain hv
  have hdomFgF : Fg.domain = F.domain := hdomFg.trans hdomEF
  have huF_E : uF p ∈ E.domain := by rw [hdomEF]; exact huF p
  have huE_F : uE p ∈ F.domain := by rw [← hdomEF]; exact huE p
  have hwE : uF p - uE p ∈ E.domain := E.domain.sub_mem huF_E (huE p)
  have hwF : uF p - uE p ∈ F.domain := hVdomF (htraceF p)
  have he_p : uEg p - uE p ∈ E.domain :=
    E.domain.sub_mem (by rw [← hdomEg]; exact huEg p) (huE p)
  have heF : uEg p - uE p ∈ F.domain := by rw [← hdomEF]; exact he_p
  have he_Fg : uEg p - uE p ∈ Fg.domain := by rw [hdomFg]; exact he_p
  have htraceFgF : uFg p - uF p ∈ V0 := by
    rw [show uFg p - uF p = (uFg p - uE p) - (uF p - uE p) by abel]
    exact V0.sub_mem (htraceFg p) (htraceF p)
  have hzV : (uFg p - uF p) - (uEg p - uE p) ∈ V0 :=
    V0.sub_mem htraceFgF (htraceEg p)
  have hz_E : (uFg p - uF p) - (uEg p - uE p) ∈ E.domain := hzero.le_domain hzV
  have hz_F : (uFg p - uF p) - (uEg p - uE p) ∈ F.domain := hVdomF hzV
  have hz_Fg : (uFg p - uF p) - (uEg p - uE p) ∈ Fg.domain := hVdomFg hzV
  -- weighted measure comparisons
  have hboundsE : ∀ (v : DomainL2 Q), v ∈ E.domain →
      ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
        Real.exp (-G) * (GammaE.measure v A).toReal ≤
            (GammaEg.measure v A).toReal ∧
          (GammaEg.measure v A).toReal ≤
            Real.exp G * (GammaE.measure v A).toReal := fun v hv A hA =>
    aux_lem_relvar_weighted_measure_bounds GammaE GammaEg hdomEg g hg G hgbound
      hweightE hv hA
  have hboundsF : ∀ (v : DomainL2 Q), v ∈ F.domain →
      ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
        Real.exp (-G) * (GammaF.measure v A).toReal ≤
            (GammaFg.measure v A).toReal ∧
          (GammaFg.measure v A).toReal ≤
            Real.exp G * (GammaF.measure v A).toReal := fun v hv A hA =>
    aux_lem_relvar_weighted_measure_bounds GammaF GammaFg hdomFgF g hg G hgbound
      hweightF hv hA
  -- the Γ_F - cΓ_E bounds
  have hpair : ∀ (x y : DomainL2 Q), x ∈ E.domain → y ∈ E.domain →
      |IF x y - c * IE x y| ≤ G * Real.exp G * (M - m) *
        Real.sqrt ((GammaE.measure x B).toReal * (GammaE.measure y B).toReal) := by
    intro x y hx hy
    have ht := hTVQ x y hx hy B hB
    have hi := aux_lem_relvar_signedIntegral_bound
      (GammaF.cross x y - c • GammaE.cross x y) B hB
      (fun t => Real.exp (g t) - 1) hf0 (G * Real.exp G) hK hf0bound
    rw [aux_lem_relvar_signedIntegral_sub_smul (GammaF.cross x y)
      (GammaE.cross x y) B hB (fun t => Real.exp (g t) - 1) hf0
      (G * Real.exp G) c (le_of_lt hcpos) hK hf0bound] at hi
    rw [hIFdef, hIEdef]
    refine hi.trans ?_
    calc
      G * Real.exp G *
          ((GammaF.cross x y - c • GammaE.cross x y).totalVariation B).toReal ≤
          G * Real.exp G * ((M - m) *
            Real.sqrt ((GammaE.measure x B).toReal *
              (GammaE.measure y B).toReal)) :=
        mul_le_mul_of_nonneg_left ht hK
      _ = G * Real.exp G * (M - m) *
          Real.sqrt ((GammaE.measure x B).toReal *
            (GammaE.measure y B).toReal) := by ring
  -- the pure F cross bounds
  have hFcross : ∀ (x y : DomainL2 Q), x ∈ F.domain → y ∈ F.domain →
      |IF x y| ≤ 2 * (G * Real.exp G) *
        Real.sqrt ((GammaF.measure x B).toReal * (GammaF.measure y B).toReal) := by
    intro x y hx hy
    rw [hIFdef]
    exact aux_lem_relvar_weighted_cross_bound GammaF hx hy hB
      (fun t => Real.exp (g t) - 1) hf0 (G * Real.exp G) hK hf0bound
  have hFwB : (GammaF.measure (uF p - uE p) B).toReal ≤ M * (D * ze) :=
    le_trans (horder (uF p - uE p) hwE B hB).2
      (mul_le_mul_of_nonneg_left hw_le_ze hM0)
  have hFuB : (GammaF.measure (uE p) B).toReal ≤ M * (D * nu) :=
    le_trans (horder (uE p) (huE p) B hB).2
      (mul_le_mul_of_nonneg_left hEu_le hM0)
  have hFeB : (GammaF.measure (uEg p - uE p) B).toReal ≤
      M * (G ^ 2 * Real.exp (4 * G) * (D * nu)) :=
    le_trans (horder (uEg p - uE p) he_p B hB).2
      (mul_le_mul_of_nonneg_left
        (hEe_le.trans (mul_le_mul_of_nonneg_left hEu_le (by positivity))) hM0)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- T1
    refine (hpair (uE p) (uE p) (huE p) (huE p)).trans ?_
    rw [aux_lem_relvar_sqrt_self _ ENNReal.toReal_nonneg]
    exact mul_le_mul_of_nonneg_left hEu_le (by positivity)
  · -- T2
    refine (hFcross (uE p) (uF p - uE p) huE_F hwF).trans ?_
    have hs : Real.sqrt ((GammaF.measure (uE p) B).toReal *
        (GammaF.measure (uF p - uE p) B).toReal) ≤ M * (D * Real.sqrt (nu * ze)) := by
      calc
        _ ≤ Real.sqrt ((M * (GammaE.measure (uE p) B).toReal) *
              (M * (GammaE.measure (uF p - uE p) B).toReal)) := by
          gcongr
          · exact (horder (uE p) (huE p) B hB).2
          · exact (horder (uF p - uE p) hwE B hB).2
        _ = M * Real.sqrt ((GammaE.measure (uE p) B).toReal *
              (GammaE.measure (uF p - uE p) B).toReal) :=
          aux_lem_relvar_sqrt_scale M _ _ hM0
        _ ≤ M * (D * Real.sqrt (nu * ze)) :=
          mul_le_mul_of_nonneg_left hsqrt_uw hM0
    calc
      2 * (G * Real.exp G) *
          Real.sqrt ((GammaF.measure (uE p) B).toReal *
            (GammaF.measure (uF p - uE p) B).toReal) ≤
          2 * (G * Real.exp G) * (M * (D * Real.sqrt (nu * ze))) := by
        exact mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 2 * G * Real.exp G * M * (D * Real.sqrt (nu * ze)) := by ring
  · -- T3
    refine (hFcross (uF p - uE p) (uF p - uE p) hwF hwF).trans ?_
    rw [aux_lem_relvar_sqrt_self _ ENNReal.toReal_nonneg]
    calc
      2 * (G * Real.exp G) * (GammaF.measure (uF p - uE p) B).toReal ≤
          2 * (G * Real.exp G) * (M * (D * ze)) :=
        mul_le_mul_of_nonneg_left hFwB (by positivity)
      _ = 2 * G * Real.exp G * M * (D * ze) := by ring
  · -- T4
    refine (hpair (uE p) (uEg p - uE p) (huE p) he_p).trans ?_
    have hs : Real.sqrt ((GammaE.measure (uE p) B).toReal *
        (GammaE.measure (uEg p - uE p) B).toReal) ≤
        G * Real.exp (2 * G) * (D * nu) := by
      refine (aux_lem_relvar_sqrt_pert G _ _ hG0 ENNReal.toReal_nonneg hEe_le).trans ?_
      exact mul_le_mul_of_nonneg_left hEu_le (by positivity)
    calc
      G * Real.exp G * (M - m) *
          Real.sqrt ((GammaE.measure (uE p) B).toReal *
            (GammaE.measure (uEg p - uE p) B).toReal) ≤
          G * Real.exp G * (M - m) * (G * Real.exp (2 * G) * (D * nu)) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = G ^ 2 * Real.exp (3 * G) * (M - m) * (D * nu) := by
        rw [show (3 : ℝ) * G = G + 2 * G by ring, Real.exp_add]; ring
  · -- T5a
    refine (hFcross (uF p - uE p) (uEg p - uE p) hwF heF).trans ?_
    have hs : Real.sqrt ((GammaF.measure (uF p - uE p) B).toReal *
        (GammaF.measure (uEg p - uE p) B).toReal) ≤
        M * G * Real.exp (2 * G) * D * Real.sqrt (nu * ze) := by
      calc
        _ ≤ Real.sqrt ((M * D * ze) *
              (M * G ^ 2 * Real.exp (4 * G) * (D * nu))) := by
          apply Real.sqrt_le_sqrt
          apply mul_le_mul
          · calc (GammaF.measure (uF p - uE p) B).toReal ≤ M * (D * ze) := hFwB
              _ = M * D * ze := by ring
          · calc (GammaF.measure (uEg p - uE p) B).toReal ≤
                  M * (G ^ 2 * Real.exp (4 * G) * (D * nu)) := hFeB
              _ = M * G ^ 2 * Real.exp (4 * G) * (D * nu) := by ring
          · exact ENNReal.toReal_nonneg
          · positivity
        _ = M * G * Real.exp (2 * G) * D * Real.sqrt (nu * ze) :=
          aux_lem_relvar_scaled_sqrt M D G nu ze hM0 hD.le hG0 hnu_nonneg hze_nonneg
    calc
      2 * (G * Real.exp G) *
          Real.sqrt ((GammaF.measure (uF p - uE p) B).toReal *
            (GammaF.measure (uEg p - uE p) B).toReal) ≤
          2 * (G * Real.exp G) *
            (M * G * Real.exp (2 * G) * D * Real.sqrt (nu * ze)) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 2 * M * G ^ 2 * Real.exp (3 * G) * (D * Real.sqrt (nu * ze)) := by
        rw [show (3 : ℝ) * G = G + 2 * G by ring, Real.exp_add]; ring
  · -- T5b : Cauchy-Schwarz for the weighted cross measure
    have hEz_q : (GammaE.measure ((uFg p - uF p) - (uEg p - uE p))
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        Real.exp G * (GammaEg.measure ((uFg p - uF p) - (uEg p - uE p))
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal :=
      aux_lem_relvar_exp_lower G _ _ (hboundsE _ hz_E _ hqmeas).1
    have hFge_q : (GammaFg.measure (uEg p - uE p)
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        M * G ^ 2 * Real.exp (5 * G) * (D * nu) := by
      have hFe_q : (GammaF.measure (uEg p - uE p)
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
          M * (G ^ 2 * Real.exp (4 * G) * (D * nu)) :=
        le_trans (horder _ he_p _ hqmeas).2
          (mul_le_mul_of_nonneg_left
            (hEe_q.trans (mul_le_mul_of_nonneg_left hEu_le (by positivity))) hM0)
      calc
        (GammaFg.measure (uEg p - uE p)
            (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
            Real.exp G * (GammaF.measure (uEg p - uE p)
              (centeredCube z r hr : Set (SpatialCoordinates d))).toReal :=
          (hboundsF _ heF _ hqmeas).2
        _ ≤ Real.exp G * (M * (G ^ 2 * Real.exp (4 * G) * (D * nu))) :=
          mul_le_mul_of_nonneg_left hFe_q (Real.exp_nonneg _)
        _ = M * G ^ 2 * Real.exp (5 * G) * (D * nu) := by
          rw [show (5 : ℝ) * G = G + 4 * G by ring, Real.exp_add]; ring
    have hFgz_q : (GammaFg.measure ((uFg p - uF p) - (uEg p - uE p))
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        M * Real.exp (2 * G) *
          (GammaEg.measure ((uFg p - uF p) - (uEg p - uE p))
            (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
      calc
        (GammaFg.measure ((uFg p - uF p) - (uEg p - uE p))
            (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
            Real.exp G * (GammaF.measure ((uFg p - uF p) - (uEg p - uE p))
              (centeredCube z r hr : Set (SpatialCoordinates d))).toReal :=
          (hboundsF _ hz_F _ hqmeas).2
        _ ≤ Real.exp G * (M * (Real.exp G *
            (GammaEg.measure ((uFg p - uF p) - (uEg p - uE p))
              (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)) := by
          gcongr
          exact le_trans (horder _ hz_E _ hqmeas).2
            (mul_le_mul_of_nonneg_left hEz_q hM0)
        _ = M * Real.exp (2 * G) *
            (GammaEg.measure ((uFg p - uF p) - (uEg p - uE p))
              (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
          rw [show (2 : ℝ) * G = G + G by ring, Real.exp_add]; ring
    refine le_trans (GammaFg.abs_cross_le _ he_Fg _ hz_Fg _ hqmeas) ?_
    exact aux_lem_relvar_cs_bound M G (D * nu) _ _ _ hM0 hG0
      (mul_nonneg hD.le hnu_nonneg) ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      ENNReal.toReal_nonneg hFge_q hFgz_q
  · -- T5c
    have hEz_q : (GammaE.measure ((uFg p - uF p) - (uEg p - uE p))
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        Real.exp G * (GammaEg.measure ((uFg p - uF p) - (uEg p - uE p))
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal :=
      aux_lem_relvar_exp_lower G _ _ (hboundsE _ hz_E _ hqmeas).1
    calc
      (GammaFg.measure ((uFg p - uF p) - (uEg p - uE p))
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
          Real.exp G * (GammaF.measure ((uFg p - uF p) - (uEg p - uE p))
            (centeredCube z r hr : Set (SpatialCoordinates d))).toReal :=
        (hboundsF _ hz_F _ hqmeas).2
      _ ≤ Real.exp G * (M * (Real.exp G *
          (GammaEg.measure ((uFg p - uF p) - (uEg p - uE p))
            (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)) := by
        gcongr
        exact le_trans (horder _ hz_E _ hqmeas).2
          (mul_le_mul_of_nonneg_left hEz_q hM0)
      _ = M * Real.exp (2 * G) *
          (GammaEg.measure ((uFg p - uF p) - (uEg p - uE p))
            (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
        rw [show (2 : ℝ) * G = G + G by ring, Real.exp_add]; ring


lemma aux_lem_relvar_R0_bound1 (k C G Ex V S T : ℝ)
    (hG : 0 ≤ G) (hk : 0 ≤ k) (hkC : k ≤ C / 10) (hEx0 : 0 ≤ Ex)
    (hEx : Ex ≤ Real.exp ((C - 1) * G)) (hV : 0 ≤ V) (hVS : V ≤ S)
    (hT : |T| ≤ k * G * Ex * V) :
    |T| ≤ (C / 10) * G * Real.exp ((C - 1) * G) * S := by
  refine hT.trans ?_
  have hC : 0 ≤ C / 10 := le_trans hk hkC
  have h1 : k * G ≤ (C / 10) * G := mul_le_mul_of_nonneg_right hkC hG
  have h2 : k * G * Ex ≤ (C / 10) * G * Real.exp ((C - 1) * G) :=
    mul_le_mul h1 hEx hEx0 (mul_nonneg hC hG)
  exact mul_le_mul h2 hVS hV
    (mul_nonneg (mul_nonneg hC hG) (Real.exp_nonneg _))

lemma aux_lem_relvar_R0_sq (k C G Ex V S T : ℝ)
    (hG : 0 ≤ G) (hk : 0 ≤ k) (hkC : k ≤ C / 10) (hEx0 : 0 ≤ Ex)
    (hEx : Real.exp G * Ex ≤ Real.exp ((C - 1) * G)) (hV : 0 ≤ V) (hVS : V ≤ S)
    (hT : |T| ≤ k * G ^ 2 * Ex * V) :
    |T| ≤ (C / 10) * G * Real.exp ((C - 1) * G) * S := by
  have hGe : G ≤ Real.exp G :=
    (by linarith : G ≤ G + 1).trans (Real.add_one_le_exp G)
  refine aux_lem_relvar_R0_bound1 k C G (Real.exp G * Ex) V S T hG hk hkC
    (by positivity) hEx hV hVS (hT.trans ?_)
  calc
    k * G ^ 2 * Ex * V = (k * Ex * V) * (G * G) := by ring
    _ ≤ (k * Ex * V) * (G * Real.exp G) := by
      have : 0 ≤ k * Ex * V := by positivity
      have hGG : G * G ≤ G * Real.exp G := mul_le_mul_of_nonneg_left hGe hG
      exact mul_le_mul_of_nonneg_left hGG this
    _ = k * G * (Real.exp G * Ex) * V := by ring

lemma aux_lem_relvar_sqrt_zq (CL G D nu ze Del zq : ℝ)
    (hCL : 0 < CL) (hG : 0 ≤ G) (hD : 0 < D) (hnu : 0 ≤ nu) (hze : 0 ≤ ze)
    (hDel : 0 ≤ Del)
    (hzq : zq ≤ CL * G ^ 2 * Real.exp (CL * G) *
      (D * ze + Del ^ 2 * (D * nu))) :
    Real.sqrt ((D * nu) * zq) ≤
      (CL + 1) * G * Real.exp (CL * G) *
        (Del * (D * nu) + D * Real.sqrt (nu * ze)) := by
  have hDnu : 0 ≤ D * nu := mul_nonneg hD.le hnu
  have hDze : 0 ≤ D * ze := mul_nonneg hD.le hze
  have hK0 : 0 ≤ CL * G ^ 2 * Real.exp (CL * G) := by positivity
  have hstep : (D * nu) * zq ≤
      (CL * G ^ 2 * Real.exp (CL * G)) * ((D * nu) * (D * ze)) +
        (CL * G ^ 2 * Real.exp (CL * G)) * (Del ^ 2 * (D * nu) ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hzq hDnu
    calc
      (D * nu) * zq ≤ (D * nu) * (CL * G ^ 2 * Real.exp (CL * G) *
          (D * ze + Del ^ 2 * (D * nu))) := h
      _ = (CL * G ^ 2 * Real.exp (CL * G)) * ((D * nu) * (D * ze)) +
          (CL * G ^ 2 * Real.exp (CL * G)) * (Del ^ 2 * (D * nu) ^ 2) := by ring
  have hsqK : Real.sqrt (CL * G ^ 2 * Real.exp (CL * G)) ≤
      (CL + 1) * G * Real.exp (CL * G) := by
    have hexp1 : (1 : ℝ) ≤ Real.exp (CL * G) :=
      Real.one_le_exp (mul_nonneg hCL.le hG)
    have hb : CL * G ^ 2 * Real.exp (CL * G) ≤
        ((CL + 1) * G * Real.exp (CL * G)) ^ 2 := by
      have h2 : CL ≤ (CL + 1) ^ 2 := by nlinarith
      have hEp : 0 < Real.exp (CL * G) := Real.exp_pos _
      nlinarith [sq_nonneg G, mul_nonneg (sq_nonneg G) hEp.le,
        mul_nonneg (mul_nonneg (sq_nonneg G) hEp.le) hEp.le]
    calc
      Real.sqrt (CL * G ^ 2 * Real.exp (CL * G)) ≤
          Real.sqrt (((CL + 1) * G * Real.exp (CL * G)) ^ 2) :=
        Real.sqrt_le_sqrt hb
      _ = (CL + 1) * G * Real.exp (CL * G) := Real.sqrt_sq (by positivity)
  have e1 : Real.sqrt ((CL * G ^ 2 * Real.exp (CL * G)) * ((D * nu) * (D * ze))) =
      Real.sqrt (CL * G ^ 2 * Real.exp (CL * G)) * (D * Real.sqrt (nu * ze)) := by
    rw [Real.sqrt_mul hK0]
    congr 1
    rw [show (D * nu) * (D * ze) = D ^ 2 * (nu * ze) by ring,
      Real.sqrt_mul (sq_nonneg D), Real.sqrt_sq hD.le]
  have e2 : Real.sqrt ((CL * G ^ 2 * Real.exp (CL * G)) *
      (Del ^ 2 * (D * nu) ^ 2)) =
      Real.sqrt (CL * G ^ 2 * Real.exp (CL * G)) * (Del * (D * nu)) := by
    rw [Real.sqrt_mul hK0]
    congr 1
    rw [show Del ^ 2 * (D * nu) ^ 2 = (Del * (D * nu)) ^ 2 by ring,
      Real.sqrt_sq (mul_nonneg hDel hDnu)]
  have hSnn : 0 ≤ Del * (D * nu) + D * Real.sqrt (nu * ze) :=
    add_nonneg (mul_nonneg hDel hDnu) (mul_nonneg hD.le (Real.sqrt_nonneg _))
  calc
    Real.sqrt ((D * nu) * zq) ≤
        Real.sqrt ((CL * G ^ 2 * Real.exp (CL * G)) * ((D * nu) * (D * ze)) +
          (CL * G ^ 2 * Real.exp (CL * G)) * (Del ^ 2 * (D * nu) ^ 2)) :=
      Real.sqrt_le_sqrt hstep
    _ ≤ Real.sqrt ((CL * G ^ 2 * Real.exp (CL * G)) * ((D * nu) * (D * ze))) +
        Real.sqrt ((CL * G ^ 2 * Real.exp (CL * G)) *
          (Del ^ 2 * (D * nu) ^ 2)) :=
      aux_lem_relvar_sqrt_add _ _ (by positivity) (by positivity)
    _ = Real.sqrt (CL * G ^ 2 * Real.exp (CL * G)) *
        (Del * (D * nu) + D * Real.sqrt (nu * ze)) := by
      rw [e1, e2]; ring
    _ ≤ ((CL + 1) * G * Real.exp (CL * G)) *
        (Del * (D * nu) + D * Real.sqrt (nu * ze)) :=
      mul_le_mul_of_nonneg_right hsqK hSnn


/-- The arithmetic assembly: the seven term bounds, the denominator estimate and
the lower bound on `Dg` give the relative-variation bound. -/
lemma aux_lem_relvar_assembly
    (C0 CL CD H C G m M D Dg nu ze zq A Ag t1 t2 t3 t4 t5a t5b t5c : ℝ)
    (hC0 : 1 ≤ C0) (hCL : 0 < CL) (hCD : 0 < CD)
    (hH : H = 1 + C0 + CL + CD) (hCdef : C = 100 * H ^ 3)
    (hG0 : 0 ≤ G) (hmpos : 0 < m) (hmM : m ≤ M) (hM : M ≤ C0)
    (hD : 0 < D) (hnu : 0 ≤ nu) (hze : 0 ≤ ze)
    (hze_sqrt : ze ≤ 2 * Real.sqrt (nu * ze))
    (hzq : zq ≤ CL * G ^ 2 * Real.exp (CL * G) *
      (D * ze + (M - m) ^ 2 * (D * nu)))
    (hnum : Ag - A = t1 + 2 * t2 + t3 + t4 + t5a - t5b - t5c)
    (h1 : |t1| ≤ G * Real.exp G * (M - m) * (D * nu))
    (h2 : |t2| ≤ 2 * G * Real.exp G * M * (D * Real.sqrt (nu * ze)))
    (h3 : |t3| ≤ 2 * G * Real.exp G * M * (D * ze))
    (h4 : |t4| ≤ G ^ 2 * Real.exp (3 * G) * (M - m) * (D * nu))
    (h5 : |t5a| ≤ 2 * M * G ^ 2 * Real.exp (3 * G) * (D * Real.sqrt (nu * ze)))
    (h6 : |t5b| ≤ M * G * Real.exp (4 * G) * Real.sqrt ((D * nu) * zq))
    (h7 : 0 ≤ t5c) (h7' : t5c ≤ M * Real.exp (2 * G) * zq)
    (hDgl : Real.exp (-G) * D ≤ Dg)
    (hden : |A / Dg - A / D| ≤ CD * G * Real.exp (CD * G) * (M - m) * nu) :
    |Ag / Dg - A / D| ≤
      C * G * Real.exp (C * G) * ((M - m) * nu + Real.sqrt (nu * ze)) := by
  have hC0pos : 0 < C0 := lt_of_lt_of_le zero_lt_one hC0
  have hMpos : 0 < M := lt_of_lt_of_le hmpos hmM
  have hM0 : (0 : ℝ) ≤ M := hMpos.le
  have hdel : 0 ≤ M - m := sub_nonneg.mpr hmM
  have hDelC0 : M - m ≤ C0 := by linarith
  have hH2 : 2 < H := by rw [hH]; linarith only [hC0, hCL, hCD]
  have hH1 : (1 : ℝ) ≤ H := by linarith only [hH2]
  have hHcube : H ≤ H ^ 3 := by
    nlinarith only [mul_nonneg (mul_nonneg (by linarith only [hH1] : (0 : ℝ) ≤ H)
      (by linarith only [hH1] : (0 : ℝ) ≤ H - 1))
      (by linarith only [hH1] : (0 : ℝ) ≤ H + 1)]
  have hH2cube : H ^ 2 ≤ H ^ 3 := by
    nlinarith only [mul_nonneg (mul_nonneg
      (by linarith only [hH1] : (0 : ℝ) ≤ H) (by linarith only [hH1] : (0 : ℝ) ≤ H))
      (by linarith only [hH1] : (0 : ℝ) ≤ H - 1)]
  have hH3 : (8 : ℝ) ≤ H ^ 3 := by
    nlinarith only [mul_nonneg (by linarith only [hH2] : (0 : ℝ) ≤ H - 2)
      (by nlinarith only [hH2, sq_nonneg H] :
        (0 : ℝ) ≤ H ^ 2 + 2 * H + 4)]
  have hCval : C / 10 = 10 * H ^ 3 := by rw [hCdef]; ring
  have hMH : M ≤ H := by rw [hH]; linarith only [hM, hCL, hCD]
  have hCLH : CL ≤ H := by rw [hH]; linarith only [hC0, hCD]
  have hCDH : CD ≤ H := by rw [hH]; linarith only [hC0, hCL]
  have hC0H : C0 ≤ H := by rw [hH]; linarith only [hCL, hCD]
  have hCpos : 0 < C := by rw [hCdef]; linarith only [hH3]
  have n1 : (1 : ℝ) ≤ C / 10 := by rw [hCval]; linarith only [hH3]
  have n2 : 4 * M ≤ C / 10 := by
    rw [hCval]; linarith only [hMH, hHcube, hH3]
  have n3 : 2 * M ≤ C / 10 := by
    rw [hCval]; linarith only [hMH, hHcube, hH3]
  have n4 : M * (CL + 1) ≤ C / 10 := by
    have a1 : M * (CL + 1) ≤ H * (H + 1) :=
      mul_le_mul hMH (by linarith only [hCLH]) (by linarith only [hCL])
        (by linarith only [hH1])
    have a2 : H * (H + 1) ≤ 2 * H ^ 3 := by nlinarith only [hH2cube, hHcube]
    rw [hCval]; linarith only [a1, a2, hH3]
  have n5 : M * CL * (2 + C0) ≤ C / 10 := by
    have a1 : M * CL ≤ H * H :=
      mul_le_mul hMH hCLH hCL.le (by linarith only [hH1])
    have a3 : M * CL * (2 + C0) ≤ (H * H) * (3 * H) :=
      mul_le_mul a1 (by linarith only [hC0H, hH1]) (by linarith only [hC0])
        (by nlinarith only [hH1])
    have a4 : (H * H) * (3 * H) = 3 * H ^ 3 := by ring
    rw [hCval]; linarith only [a3, a4, hH3]
  have n6 : CD ≤ C / 10 := by
    rw [hCval]; linarith only [hCDH, hHcube, hH3]
  have nC : CL + 5 ≤ C - 1 := by
    rw [hCdef]; linarith only [hCLH, hHcube, hH3]
  have nC2 : CL + 3 ≤ C - 1 := by linarith only [nC]
  have nC3 : (4 : ℝ) ≤ C - 1 := by rw [hCdef]; linarith only [hH3]
  have nC4 : (1 : ℝ) ≤ C - 1 := by linarith only [nC3]
  have hEmono : ∀ a b : ℝ, a ≤ b → Real.exp (a * G) ≤ Real.exp (b * G) :=
    fun a b h => Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right h hG0)
  have hexpG1 : Real.exp G ≤ Real.exp ((C - 1) * G) := by
    have h := hEmono 1 (C - 1) nC4
    rwa [one_mul] at h
  have hexp4 : Real.exp G * Real.exp (3 * G) ≤ Real.exp ((C - 1) * G) := by
    rw [← Real.exp_add, show G + 3 * G = 4 * G by ring]
    exact hEmono 4 (C - 1) nC3
  have hexpCL5 : Real.exp G * Real.exp ((CL + 4) * G) ≤
      Real.exp ((C - 1) * G) := by
    rw [← Real.exp_add, show G + (CL + 4) * G = (CL + 5) * G by ring]
    exact hEmono (CL + 5) (C - 1) nC
  have hexpCL3 : Real.exp G * Real.exp ((CL + 2) * G) ≤
      Real.exp ((C - 1) * G) := by
    rw [← Real.exp_add, show G + (CL + 2) * G = (CL + 3) * G by ring]
    exact hEmono (CL + 3) (C - 1) nC2
  have hX : (0 : ℝ) ≤ D * nu := mul_nonneg hD.le hnu
  have hY : (0 : ℝ) ≤ D * Real.sqrt (nu * ze) :=
    mul_nonneg hD.le (Real.sqrt_nonneg _)
  set Ssum : ℝ := (M - m) * (D * nu) + D * Real.sqrt (nu * ze) with hSsum
  have hSnn : 0 ≤ Ssum := by
    rw [hSsum]; exact add_nonneg (mul_nonneg hdel hX) hY
  have hDelX_le : (M - m) * (D * nu) ≤ Ssum := by rw [hSsum]; linarith
  have hY_le : D * Real.sqrt (nu * ze) ≤ Ssum := by
    rw [hSsum]; linarith [mul_nonneg hdel hX]
  have hDze_le : D * ze ≤ 2 * (D * Real.sqrt (nu * ze)) := by
    have h := mul_le_mul_of_nonneg_left hze_sqrt hD.le
    linarith
  set R0 : ℝ := (C / 10) * G * Real.exp ((C - 1) * G) * Ssum with hR0def
  have hR0nn : 0 ≤ R0 := by
    rw [hR0def]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ C / 10) hG0)
      (Real.exp_nonneg _)) hSnn
  have hcoefY : (0 : ℝ) ≤ 2 * G * Real.exp G * M :=
    mul_nonneg (mul_nonneg (by linarith) (Real.exp_nonneg G)) hM0
  have b1 : |t1| ≤ R0 := by
    rw [hR0def]
    refine aux_lem_relvar_R0_bound1 1 C G (Real.exp G) ((M - m) * (D * nu)) Ssum t1
      hG0 zero_le_one n1 (Real.exp_nonneg _) hexpG1 (mul_nonneg hdel hX)
      hDelX_le ?_
    calc
      |t1| ≤ G * Real.exp G * (M - m) * (D * nu) := h1
      _ = 1 * G * Real.exp G * ((M - m) * (D * nu)) := by ring
  have b2 : |2 * t2| ≤ R0 := by
    rw [hR0def]
    refine aux_lem_relvar_R0_bound1 (4 * M) C G (Real.exp G)
      (D * Real.sqrt (nu * ze)) Ssum (2 * t2) hG0 (by linarith) n2
      (Real.exp_nonneg _) hexpG1 hY hY_le ?_
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      2 * |t2| ≤ 2 * (2 * G * Real.exp G * M * (D * Real.sqrt (nu * ze))) := by
        linarith
      _ = 4 * M * G * Real.exp G * (D * Real.sqrt (nu * ze)) := by ring
  have b3 : |t3| ≤ R0 := by
    rw [hR0def]
    refine aux_lem_relvar_R0_bound1 (4 * M) C G (Real.exp G)
      (D * Real.sqrt (nu * ze)) Ssum t3 hG0 (by linarith) n2
      (Real.exp_nonneg _) hexpG1 hY hY_le ?_
    calc
      |t3| ≤ 2 * G * Real.exp G * M * (D * ze) := h3
      _ ≤ 2 * G * Real.exp G * M * (2 * (D * Real.sqrt (nu * ze))) :=
        mul_le_mul_of_nonneg_left hDze_le hcoefY
      _ = 4 * M * G * Real.exp G * (D * Real.sqrt (nu * ze)) := by ring
  have b4 : |t4| ≤ R0 := by
    rw [hR0def]
    refine aux_lem_relvar_R0_sq 1 C G (Real.exp (3 * G)) ((M - m) * (D * nu))
      Ssum t4 hG0 zero_le_one n1 (Real.exp_nonneg _) hexp4 (mul_nonneg hdel hX)
      hDelX_le ?_
    calc
      |t4| ≤ G ^ 2 * Real.exp (3 * G) * (M - m) * (D * nu) := h4
      _ = 1 * G ^ 2 * Real.exp (3 * G) * ((M - m) * (D * nu)) := by ring
  have b5 : |t5a| ≤ R0 := by
    rw [hR0def]
    refine aux_lem_relvar_R0_sq (2 * M) C G (Real.exp (3 * G))
      (D * Real.sqrt (nu * ze)) Ssum t5a hG0 (by linarith) n3
      (Real.exp_nonneg _) hexp4 hY hY_le ?_
    calc
      |t5a| ≤ 2 * M * G ^ 2 * Real.exp (3 * G) * (D * Real.sqrt (nu * ze)) := h5
      _ = (2 * M) * G ^ 2 * Real.exp (3 * G) * (D * Real.sqrt (nu * ze)) := by ring
  have b6 : |t5b| ≤ R0 := by
    have hsq := aux_lem_relvar_sqrt_zq CL G D nu ze (M - m) zq hCL hG0 hD hnu hze
      hdel hzq
    rw [← hSsum] at hsq
    rw [hR0def]
    refine aux_lem_relvar_R0_sq (M * (CL + 1)) C G (Real.exp ((CL + 4) * G))
      Ssum Ssum t5b hG0 (mul_nonneg hM0 (by linarith only [hCL])) n4 (Real.exp_nonneg _) hexpCL5 hSnn
      le_rfl ?_
    calc
      |t5b| ≤ M * G * Real.exp (4 * G) * Real.sqrt ((D * nu) * zq) := h6
      _ ≤ M * G * Real.exp (4 * G) *
          ((CL + 1) * G * Real.exp (CL * G) * Ssum) :=
        mul_le_mul_of_nonneg_left hsq
          (mul_nonneg (mul_nonneg hM0 hG0) (Real.exp_nonneg _))
      _ = (M * (CL + 1)) * G ^ 2 * Real.exp ((CL + 4) * G) * Ssum := by
        rw [show (CL + 4) * G = CL * G + 4 * G by ring, Real.exp_add]; ring
  have b7 : |t5c| ≤ R0 := by
    have habs : |t5c| = t5c := abs_of_nonneg h7
    have hstep2 : D * ze + (M - m) ^ 2 * (D * nu) ≤ (2 + C0) * Ssum := by
      have hA : D * ze ≤ 2 * Ssum := by linarith [hDze_le, hY_le]
      have hB : (M - m) ^ 2 * (D * nu) ≤ C0 * Ssum := by
        have hrw : (M - m) ^ 2 * (D * nu) = (M - m) * ((M - m) * (D * nu)) := by
          ring
        rw [hrw]
        calc
          (M - m) * ((M - m) * (D * nu)) ≤ C0 * ((M - m) * (D * nu)) :=
            mul_le_mul_of_nonneg_right hDelC0 (mul_nonneg hdel hX)
          _ ≤ C0 * Ssum := mul_le_mul_of_nonneg_left hDelX_le hC0pos.le
      linarith
    rw [hR0def]
    refine aux_lem_relvar_R0_sq (M * CL * (2 + C0)) C G (Real.exp ((CL + 2) * G))
      Ssum Ssum t5c hG0
      (mul_nonneg (mul_nonneg hM0 hCL.le) (by linarith only [hC0pos])) n5 (Real.exp_nonneg _) hexpCL3 hSnn
      le_rfl ?_
    rw [habs]
    calc
      t5c ≤ M * Real.exp (2 * G) * zq := h7'
      _ ≤ M * Real.exp (2 * G) * (CL * G ^ 2 * Real.exp (CL * G) *
          (D * ze + (M - m) ^ 2 * (D * nu))) :=
        mul_le_mul_of_nonneg_left hzq (mul_nonneg hM0 (Real.exp_nonneg _))
      _ ≤ M * Real.exp (2 * G) * (CL * G ^ 2 * Real.exp (CL * G) *
          ((2 + C0) * Ssum)) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hstep2 (by positivity)) ?_
        exact mul_nonneg hM0 (Real.exp_nonneg _)
      _ = (M * CL * (2 + C0)) * G ^ 2 * Real.exp ((CL + 2) * G) * Ssum := by
        rw [show (CL + 2) * G = CL * G + 2 * G by ring, Real.exp_add]; ring
  have hsum : |Ag - A| ≤ 8 * R0 := by
    rw [hnum]
    have k1 := abs_le.mp b1
    have k2 := abs_le.mp b2
    have k3 := abs_le.mp b3
    have k4 := abs_le.mp b4
    have k5 := abs_le.mp b5
    have k6 := abs_le.mp b6
    have k7 := abs_le.mp b7
    rw [abs_le]
    constructor <;> linarith [k1.1, k1.2, k2.1, k2.2, k3.1, k3.2, k4.1, k4.2,
      k5.1, k5.2, k6.1, k6.2, k7.1, k7.2]
  have hDgpos : 0 < Dg := lt_of_lt_of_le (mul_pos (Real.exp_pos _) hD) hDgl
  have hT : 0 ≤ (M - m) * nu + Real.sqrt (nu * ze) :=
    add_nonneg (mul_nonneg hdel hnu) (Real.sqrt_nonneg _)
  have hkey : 8 * R0 / (Real.exp (-G) * D) =
      (4 * C / 5) * G * Real.exp (C * G) *
        ((M - m) * nu + Real.sqrt (nu * ze)) := by
    have he : Real.exp (C * G) * Real.exp (-G) = Real.exp ((C - 1) * G) := by
      rw [← Real.exp_add]; congr 1; ring
    have hne : Real.exp (-G) * D ≠ 0 := ne_of_gt (mul_pos (Real.exp_pos _) hD)
    rw [hR0def, hSsum, div_eq_iff hne]
    calc
      8 * ((C / 10) * G * Real.exp ((C - 1) * G) *
          ((M - m) * (D * nu) + D * Real.sqrt (nu * ze))) =
          (4 * C / 5) * G * Real.exp ((C - 1) * G) * D *
            ((M - m) * nu + Real.sqrt (nu * ze)) := by ring
      _ = (4 * C / 5) * G * (Real.exp (C * G) * Real.exp (-G)) * D *
            ((M - m) * nu + Real.sqrt (nu * ze)) := by rw [he]
      _ = (4 * C / 5) * G * Real.exp (C * G) *
            ((M - m) * nu + Real.sqrt (nu * ze)) * (Real.exp (-G) * D) := by ring
  have hnum_norm : |(Ag - A) / Dg| ≤
      (4 * C / 5) * G * Real.exp (C * G) *
        ((M - m) * nu + Real.sqrt (nu * ze)) := by
    rw [abs_div, abs_of_pos hDgpos]
    calc
      |Ag - A| / Dg ≤ (8 * R0) / Dg := by gcongr
      _ ≤ (8 * R0) / (Real.exp (-G) * D) := by gcongr
      _ = _ := hkey
  have hden' : |A / Dg - A / D| ≤
      (C / 10) * G * Real.exp (C * G) *
        ((M - m) * nu + Real.sqrt (nu * ze)) := by
    refine hden.trans ?_
    have hCDC : Real.exp (CD * G) ≤ Real.exp (C * G) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) hG0)
    have h1' : CD * G ≤ (C / 10) * G := mul_le_mul_of_nonneg_right n6 hG0
    calc
      CD * G * Real.exp (CD * G) * (M - m) * nu =
          (CD * G * Real.exp (CD * G)) * ((M - m) * nu) := by ring
      _ ≤ ((C / 10) * G * Real.exp (C * G)) * ((M - m) * nu) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul h1' hCDC (Real.exp_nonneg _)
            (mul_nonneg (by linarith) hG0))
          (mul_nonneg hdel hnu)
      _ ≤ (C / 10) * G * Real.exp (C * G) *
          ((M - m) * nu + Real.sqrt (nu * ze)) := by
        refine mul_le_mul_of_nonneg_left (by linarith [Real.sqrt_nonneg (nu * ze)])
          ?_
        exact mul_nonneg (mul_nonneg (by linarith) hG0) (Real.exp_nonneg _)
  have hdecomp : Ag / Dg - A / D = (Ag - A) / Dg + (A / Dg - A / D) := by
    rw [sub_div]; ring
  rw [hdecomp]
  calc
    |(Ag - A) / Dg + (A / Dg - A / D)| ≤
        |(Ag - A) / Dg| + |A / Dg - A / D| := abs_add_le _ _
    _ ≤ (4 * C / 5) * G * Real.exp (C * G) *
          ((M - m) * nu + Real.sqrt (nu * ze)) +
        (C / 10) * G * Real.exp (C * G) *
          ((M - m) * nu + Real.sqrt (nu * ze)) := add_le_add hnum_norm hden'
    _ = (9 * C / 10) * G * Real.exp (C * G) *
          ((M - m) * nu + Real.sqrt (nu * ze)) := by ring
    _ ≤ C * G * Real.exp (C * G) * ((M - m) * nu + Real.sqrt (nu * ze)) := by
      refine mul_le_mul_of_nonneg_right ?_ hT
      have : (9 * C / 10) * G ≤ C * G :=
        mul_le_mul_of_nonneg_right (by linarith) hG0
      exact mul_le_mul_of_nonneg_right this (Real.exp_nonneg _)


end RelvarStages



theorem lem_relvar
    (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ) (hd : 2 ≤ d)
      (slopes : Finset (Fin d → ℝ))
      (hslopes : ∀ p : Fin d → ℝ,
        p ∈ slopes ↔ (∃ i : Fin d, p = Pi.single i (1 : ℝ)) ∨
          (∃ i j : Fin d, p = Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ))),
    ∀ (Q : Opens (SpatialCoordinates d)) (z : SpatialCoordinates d) (r : ℝ)
      (hr : 0 < r)
      (hQ : ∃ (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ),
        Q = centeredCube zQ rQ hrQ),
    let q := centeredCube z r hr
    ∀ (hinside : closure (q : Set (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d)))
      (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
      (hEreg : ∃ Cc : Set (DomainL2 Q),
        DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) Cc)
      (hEloc : DirichletForm.IsStronglyLocal E.toClosedForm)
      (hFreg : ∃ Cc : Set (DomainL2 Q),
        DirichletForm.IsCoreOn F.toClosedForm (Q : Set (SpatialCoordinates d)) Cc)
      (hFloc : DirichletForm.IsStronglyLocal F.toClosedForm)
      (Eg Fg : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
      (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
      (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
      (GammaEg : DirichletForm.EnergyMeasure Eg)
      (GammaFg : DirichletForm.EnergyMeasure Fg)
      (hdomEF : E.domain = F.domain)
      (hdomEg : Eg.domain = E.domain)
      (hdomFg : Fg.domain = E.domain)
      (V0 : Submodule ℝ (DomainL2 Q))
      (hzero : DirichletForm.IsKilledDomain E.toClosedForm (q : Set (SpatialCoordinates d)) V0)
      (m M c : ℝ) (hm : C0⁻¹ ≤ m) (hmM : m ≤ M) (hM : M ≤ C0)
      (hmc : m ≤ c) (hcM : c ≤ M)
      (hformorder : ∀ u ∈ E.domain,
        m * E.form u u ≤ F.form u u ∧ F.form u u ≤ M * E.form u u)
      (g : SpatialCoordinates d → ℝ) (hg : Measurable g)
      (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B)
      (hBq : B ⊆ (q : Set (SpatialCoordinates d)))
      (hsupp : ∀ x, x ∉ B → g x = 0)
      (G : ℝ) (hG : IsLUB (Set.range (fun x => |g x|)) G)
      (hbdd : BddAbove (Set.range (fun x => |g x|)))
      (hweightE : ∀ u ∈ E.domain, ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
        GammaEg.measure u A = ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(GammaE.measure u))
      (hweightF : ∀ u ∈ F.domain, ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
        GammaFg.measure u A = ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(GammaF.measure u))
      (hweightE_cross : ∀ u ∈ E.domain, ∀ v ∈ E.domain,
        ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
          GammaEg.cross u v A =
            DirichletForm.signedIntegralOn (GammaE.cross u v) A
              (fun x => Real.exp (g x)))
      (hweightF_cross : ∀ u ∈ F.domain, ∀ v ∈ F.domain,
        ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
          GammaFg.cross u v A =
            DirichletForm.signedIntegralOn (GammaF.cross u v) A
              (fun x => Real.exp (g x)))
      (uE uF uEg uFg : (Fin d → ℝ) → DomainL2 Q)
      (huE : ∀ p, uE p ∈ E.domain)
      (huF : ∀ p, uF p ∈ F.domain)
      (huEg : ∀ p, uEg p ∈ Eg.domain)
      (huFg : ∀ p, uFg p ∈ Fg.domain)
      (UE : (Fin d → ℝ) → SpatialCoordinates d → ℝ)
      (hcontUE : ∀ p, ContinuousOn (UE p) (closure (Q : Set (SpatialCoordinates d))))
      (haeUE : ∀ p, (uE p : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] UE p)
      (hbdUE : ∀ p x, x ∈ frontier (q : Set (SpatialCoordinates d)) → UE p x = ∑ j, p j * x j)
      (htraceF : ∀ p, uF p - uE p ∈ V0)
      (htraceEg : ∀ p, uEg p - uE p ∈ V0)
      (htraceFg : ∀ p, uFg p - uE p ∈ V0)
      (hminE : ∀ p, ∀ v ∈ E.domain, v - uE p ∈ V0 →
        (GammaE.measure (uE p) q).toReal ≤ (GammaE.measure v q).toReal)
      (hminF : ∀ p, ∀ v ∈ F.domain, v - uE p ∈ V0 →
        (GammaF.measure (uF p) q).toReal ≤ (GammaF.measure v q).toReal)
      (hminEg : ∀ p, ∀ v ∈ Eg.domain, v - uE p ∈ V0 →
        (GammaEg.measure (uEg p) q).toReal ≤ (GammaEg.measure v q).toReal)
      (hminFg : ∀ p, ∀ v ∈ Fg.domain, v - uE p ∈ V0 →
        (GammaFg.measure (uFg p) q).toReal ≤ (GammaFg.measure v q).toReal)
      (QE QF QEg QFg : QuadraticForm ℝ (Fin d → ℝ))
      (hQE : ∀ p, QE p = (GammaE.measure (uE p) q).toReal)
      (hQF : ∀ p, QF p = (GammaF.measure (uF p) q).toReal)
      (hQEg : ∀ p, QEg p = (GammaEg.measure (uEg p) q).toReal)
      (hQFg : ∀ p, QFg p = (GammaFg.measure (uFg p) q).toReal)
      (D : ℝ) (hDdef : D = ∑ j : Fin d, QE (Pi.single j 1)) (hD : 0 < D),
    let nu : Measure (SpatialCoordinates d) := ENNReal.ofReal D⁻¹ •
      (∑ p ∈ slopes, (GammaE.measure (uE p) + GammaE.measure (uF p)))
    let zeta : Measure (SpatialCoordinates d) := ENNReal.ofReal D⁻¹ •
      (∑ p ∈ slopes, GammaE.measure (uF p - uE p))
    let Dg : ℝ := ∑ j : Fin d, QEg (Pi.single j 1)
    ∀ p ∈ slopes,
      |(QFg p - c * QEg p) / Dg - (QF p - c * QE p) / D| ≤
        C * G * Real.exp (C * G) *
          ((M - m) * (nu B).toReal + Real.sqrt ((nu B).toReal * (zeta B).toReal)) := by
  obtain ⟨CL, hCL, hL⟩ := lem_relvar_localized_weighted_minimizer_difference C0 hC0
  have hC0pos : 0 < C0 := lt_of_lt_of_le zero_lt_one hC0
  have hKdenpos : 0 < 10 * (C0 + 1) := by linarith
  obtain ⟨CD, hCD, hDassembly⟩ :=
    lem_relvar_normalized_response_denominator_assembly (10 * (C0 + 1)) hKdenpos
  have hHpos : (0 : ℝ) < 1 + C0 + CL + CD := by linarith
  refine ⟨100 * (1 + C0 + CL + CD) ^ 3, by positivity, ?_⟩
  intro d hd slopes hslopes Q z r hr hQ
  dsimp only
  intro hinside E F hEreg hEloc hFreg hFloc Eg Fg GammaE GammaF GammaEg GammaFg
    hdomEF hdomEg hdomFg
    V0 hzero m M c hm hmM hM hmc hcM hformorder g hg B hB hBq hsupp G hG hbdd
    hweightE hweightF hweightE_cross hweightF_cross uE uF uEg uFg huE huF huEg
    huFg UE hcontUE haeUE hbdUE htraceF htraceEg htraceFg hminE hminF hminEg
    hminFg QE QF QEg QFg hQE hQF hQEg hQFg D hDdef hD p hp
  have horder := energy_order_of_form_order Q E F hEreg hEloc hFreg hFloc hdomEF
    GammaE GammaF m M (lt_of_lt_of_le (inv_pos.mpr hC0pos) hm) hformorder
  have hL_p := hL d hd slopes hslopes Q z r hr hQ hinside E.toClosedForm F.toClosedForm
    Eg Fg GammaE GammaF GammaEg GammaFg hdomEF hdomEg hdomFg V0 hzero m M c hm hmM hM hmc hcM
    horder
    g hg B hB hBq hsupp G hG hbdd hweightE hweightF hweightE_cross hweightF_cross
    uE uF uEg uFg huE huF huEg huFg htraceF htraceEg htraceFg hminE hminF hminEg
    hminFg p hp
  dsimp only at hL_p
  have ctx : aux_lem_relvar_Ctx C0 Q z r hr slopes E.toClosedForm F.toClosedForm Eg Fg
      GammaE GammaF GammaEg GammaFg V0 m M c g B G uE uF uEg uFg QE QF QEg QFg D
      (∑ j : Fin d, QEg (Pi.single j 1))
      (D⁻¹ * ∑ i ∈ slopes,
        ((GammaE.measure (uE i) + GammaE.measure (uF i)) B).toReal)
      (D⁻¹ * ∑ i ∈ slopes, (GammaE.measure (uF i - uE i) B).toReal)
      (fun x y => DirichletForm.signedIntegralOn (GammaE.cross x y) B
        (fun t => Real.exp (g t) - 1))
      (fun x y => DirichletForm.signedIntegralOn (GammaF.cross x y) B
        (fun t => Real.exp (g t) - 1)) :=
    { hC0 := hC0, hd := hd, hslopes := hslopes, hQ := hQ, hinside := hinside
      hdomEF := hdomEF, hdomEg := hdomEg, hdomFg := hdomFg, hzero := hzero
      hm := hm, hmM := hmM, hM := hM, hmc := hmc, hcM := hcM, horder := horder
      hg := hg, hB := hB, hBq := hBq, hsupp := hsupp, hG := hG, hbdd := hbdd
      hweightE := hweightE, hweightF := hweightF
      hweightE_cross := hweightE_cross, hweightF_cross := hweightF_cross
      huE := huE, huF := huF, huEg := huEg, huFg := huFg
      htraceF := htraceF, htraceEg := htraceEg, htraceFg := htraceFg
      hminE := hminE, hminF := hminF, hminEg := hminEg, hminFg := hminFg
      hQE := hQE, hQF := hQF, hQEg := hQEg, hQFg := hQFg
      hDdef := hDdef, hD := hD, hDgdef := rfl, hnudef := rfl, hzedef := rfl
      hIEdef := fun _ _ => rfl, hIFdef := fun _ _ => rfl }
  obtain ⟨hnu_nonneg, hze_nonneg, -, -, hze_sqrt, hnu_formula, hzeta_formula, -⟩ :=
    aux_lem_relvar_nu_basics ctx
  obtain ⟨hEu_le, hw_le_ze, -⟩ := aux_lem_relvar_p_bounds ctx p hp
  obtain ⟨hDg_lower, hDgpos, hDg_diff⟩ := aux_lem_relvar_Dg_bounds ctx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := aux_lem_relvar_term_bounds ctx p hp
  have hnum_id := aux_lem_relvar_num_identity ctx p
  have hbase_D := aux_lem_relvar_base_D ctx p hp
  have hmpos : 0 < m := lt_of_lt_of_le (inv_pos.mpr hC0pos) hm
  have hdel : 0 ≤ M - m := sub_nonneg.mpr hmM
  have hG0 : 0 ≤ G := le_trans (abs_nonneg (g (Classical.arbitrary _)))
    (hG.1 ⟨Classical.arbitrary _, rfl⟩)
  have hden := hDassembly G (M - m) D (∑ j : Fin d, QEg (Pi.single j 1))
    (D⁻¹ * ∑ i ∈ slopes,
      ((GammaE.measure (uE i) + GammaE.measure (uF i)) B).toReal)
    (QF p - c * QE p) hG0 hdel hD hnu_nonneg hDg_lower hbase_D hDg_diff
  have hzq : (GammaEg.measure ((uFg p - uF p) - (uEg p - uE p))
        (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
      CL * G ^ 2 * Real.exp (CL * G) *
        (D * (D⁻¹ * ∑ i ∈ slopes, (GammaE.measure (uF i - uE i) B).toReal) +
          (M - m) ^ 2 * (D * (D⁻¹ * ∑ i ∈ slopes,
            ((GammaE.measure (uE i) + GammaE.measure (uF i)) B).toReal))) := by
    refine hL_p.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    gcongr
  have hfinal := aux_lem_relvar_assembly C0 CL CD (1 + C0 + CL + CD)
    (100 * (1 + C0 + CL + CD) ^ 3) G m M D (∑ j : Fin d, QEg (Pi.single j 1))
    (D⁻¹ * ∑ i ∈ slopes,
      ((GammaE.measure (uE i) + GammaE.measure (uF i)) B).toReal)
    (D⁻¹ * ∑ i ∈ slopes, (GammaE.measure (uF i - uE i) B).toReal)
    ((GammaEg.measure ((uFg p - uF p) - (uEg p - uE p))
      (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
    (QF p - c * QE p) (QFg p - c * QEg p) _ _ _ _ _ _ _
    hC0 hCL hCD rfl rfl hG0 hmpos hmM hM hD hnu_nonneg hze_nonneg hze_sqrt hzq
    hnum_id b1 b2 b3 b4 b5 b6 ENNReal.toReal_nonneg b7 hDg_lower hden
  rw [hnu_formula, hzeta_formula]
  exact hfinal

end
