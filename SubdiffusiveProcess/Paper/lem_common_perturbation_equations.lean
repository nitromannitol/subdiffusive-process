module

public import SubdiffusiveProcess.Paper.cor_14
public import SubdiffusiveProcess.Paper.lem_borel_weights
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

namespace SubdiffusiveProcess.Paper
noncomputable section

lemma aux_lem_common_perturbation_equations_form_add_right
    {X : Type*} [MeasurableSpace X] {m : Measure X}
    (K : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m) {u v w : Lp ℝ 2 m}
    (hu : u ∈ K.domain) (hv : v ∈ K.domain) (hw : w ∈ K.domain) :
    K.form u (v + w) = K.form u v + K.form u w := by
  rw [K.form_symm u hu (v + w) (K.domain.add_mem hv hw),
    K.form_add_left v hv w hw u hu, K.form_symm v hv u hu,
    K.form_symm w hw u hu]

lemma aux_lem_common_perturbation_equations_form_smul_right
    {X : Type*} [MeasurableSpace X] {m : Measure X}
    (K : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m) (c : ℝ) {u v : Lp ℝ 2 m}
    (hu : u ∈ K.domain) (hv : v ∈ K.domain) :
    K.form u (c • v) = c * K.form u v := by
  rw [K.form_symm u hu (c • v) (K.domain.smul_mem c hv),
    K.form_smul_left c v hv u hu, K.form_symm v hv u hu]

lemma aux_lem_common_perturbation_equations_form_add_self
    {X : Type*} [MeasurableSpace X] {m : Measure X}
    (K : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m) {u v : Lp ℝ 2 m}
    (hu : u ∈ K.domain) (hv : v ∈ K.domain) :
    K.form (u + v) (u + v) = K.form u u + 2 * K.form u v + K.form v v := by
  rw [K.form_add_left u hu v hv (u + v) (K.domain.add_mem hu hv),
    aux_lem_common_perturbation_equations_form_add_right K
      (u := u) (v := u) (w := v) hu hu hv,
    aux_lem_common_perturbation_equations_form_add_right K
      (u := v) (v := u) (w := v) hv hu hv,
    K.form_symm v hv u hu]
  ring

lemma aux_lem_common_perturbation_equations_form_smul_self
    {X : Type*} [MeasurableSpace X] {m : Measure X}
    (K : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m) (c : ℝ) {u : Lp ℝ 2 m}
    (hu : u ∈ K.domain) :
    K.form (c • u) (c • u) = c ^ 2 * K.form u u := by
  rw [K.form_smul_left c u hu (c • u) (K.domain.smul_mem c hu),
    aux_lem_common_perturbation_equations_form_smul_right K c hu hu]
  ring

lemma aux_lem_common_perturbation_equations_form_sub_left
    {X : Type*} [MeasurableSpace X] {m : Measure X}
    (K : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m) {u v w : Lp ℝ 2 m}
    (hu : u ∈ K.domain) (hv : v ∈ K.domain) (hw : w ∈ K.domain) :
    K.form (u - v) w = K.form u w - K.form v w := by
  rw [show u - v = u + (-1 : ℝ) • v by rw [neg_one_smul, ← sub_eq_add_neg],
    K.form_add_left u hu ((-1 : ℝ) • v) (K.domain.smul_mem (-1) hv) w hw,
    K.form_smul_left (-1) v hv w hw]
  ring

lemma aux_lem_common_perturbation_equations_min_orthogonal
    {X : Type*} [MeasurableSpace X] {m : Measure X}
    (K : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m) (D : Submodule ℝ (Lp ℝ 2 m))
    (u : Lp ℝ 2 m) (hu : u ∈ K.domain)
    (hmin : ∀ v ∈ D, K.form u u ≤ K.form (u + v) (u + v))
    (hD : D ≤ K.domain) {v : Lp ℝ 2 m} (hv : v ∈ D) :
    K.form u v = 0 := by
  have hpos := hmin v hv
  have hneg := hmin (-v) (D.neg_mem hv)
  have hpos' : 0 ≤ 2 * K.form u v + K.form v v := by
    rw [aux_lem_common_perturbation_equations_form_add_self K hu (hD hv)] at hpos
    linarith [hpos]
  have hneg' : 0 ≤ -2 * K.form u v + K.form v v := by
    rw [aux_lem_common_perturbation_equations_form_add_self K hu (hD (D.neg_mem hv))] at hneg
    have hcross : K.form u (-v) = -K.form u v := by
      simpa [neg_one_smul] using
        (aux_lem_common_perturbation_equations_form_smul_right K (-1) hu (hD hv))
    have hself : K.form (-v) (-v) = K.form v v := by
      simpa [neg_one_smul] using
        (aux_lem_common_perturbation_equations_form_smul_self K (-1) (hD hv))
    rw [hcross, hself] at hneg
    linarith [hneg]
  have hvv : 0 ≤ K.form v v := K.form_nonneg v (hD hv)
  have htest := hmin ((-(K.form u v) / (K.form v v + 1)) • v)
    (D.smul_mem _ hv)
  have htest' : 0 ≤ 2 * (-(K.form u v) / (K.form v v + 1)) * K.form u v +
      (-(K.form u v) / (K.form v v + 1)) ^ 2 * K.form v v := by
    have hscale := K.domain.smul_mem (-(K.form u v) / (K.form v v + 1)) (hD hv)
    rw [aux_lem_common_perturbation_equations_form_add_self K hu hscale] at htest
    have hcross := aux_lem_common_perturbation_equations_form_smul_right K
      (-(K.form u v) / (K.form v v + 1)) hu (hD hv)
    have hself := aux_lem_common_perturbation_equations_form_smul_self K
      (-(K.form u v) / (K.form v v + 1)) (hD hv)
    rw [hcross, hself] at htest
    linarith [htest]
  have hden : 0 < K.form v v + 1 := by linarith
  have hden2 : 0 < (K.form v v + 1) ^ 2 := sq_pos_of_pos hden
  have hzero : K.form u v = 0 := by
    field_simp [ne_of_gt hden] at htest'
    nlinarith [sq_nonneg (K.form u v)]
  exact hzero

lemma aux_lem_common_perturbation_equations_signedIntegral_toSignedMeasure
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    (B : Set X) (f : X → ℝ) :
    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn μ.toSignedMeasure B f = ∫ x in B, f x ∂μ := by
  let j : MeasureTheory.JordanDecomposition X :=
    { posPart := μ
      negPart := 0
      posPart_finite := inferInstance
      negPart_finite := inferInstance
      mutuallySingular := MeasureTheory.Measure.MutuallySingular.zero_right }
  have hj : μ.toSignedMeasure.toJordanDecomposition = j := by
    apply MeasureTheory.SignedMeasure.toJordanDecomposition_eq
    simp [j, MeasureTheory.JordanDecomposition.toSignedMeasure]
  simp [_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn, hj, j]

lemma aux_lem_common_perturbation_equations_integral_sub_measure_of_le
    {X : Type*} [MeasurableSpace X] {μ ν : Measure X} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (f : X → ℝ) (hfμ : Integrable f μ) (hfν : Integrable f ν)
    (hle : μ ≤ ν) :
    (∫ x, f x ∂(ν - μ)) = (∫ x, f x ∂ν) - (∫ x, f x ∂μ) := by
  have hfsub : Integrable f (ν - μ) := hfν.mono_measure Measure.sub_le
  have h := integral_add_measure hfsub hfμ
  rw [Measure.sub_add_cancel_of_le hle] at h
  linarith

lemma aux_lem_common_perturbation_equations_signedIntegral_sub_toSignedMeasure
    {X : Type*} [MeasurableSpace X] {μ ν : Measure X} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (f : X → ℝ) (hfμ : Integrable f μ) (hfν : Integrable f ν) :
    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (μ.toSignedMeasure - ν.toSignedMeasure) Set.univ f =
      (∫ x, f x ∂μ) - (∫ x, f x ∂ν) := by
  obtain ⟨s, hs⟩ := MeasureTheory.exists_isHahnDecomposition μ ν
  have hμs : Integrable f (μ.restrict s) := hfμ.restrict
  have hμc : Integrable f (μ.restrict sᶜ) := hfμ.restrict
  have hνs : Integrable f (ν.restrict s) := hfν.restrict
  have hνc : Integrable f (ν.restrict sᶜ) := hfν.restrict
  have hμν : Integrable f (μ - ν) := hfμ.mono_measure Measure.sub_le
  have hνμ : Integrable f (ν - μ) := hfν.mono_measure Measure.sub_le
  have hμν_s : (μ - ν).restrict s = 0 := by
    rw [Measure.restrict_sub_eq_restrict_sub_restrict hs.measurableSet,
      Measure.sub_eq_zero_of_le hs.le_on]
  have hνμ_sc : (ν - μ).restrict sᶜ = 0 := by
    rw [Measure.restrict_sub_eq_restrict_sub_restrict hs.measurableSet.compl,
      Measure.sub_eq_zero_of_le hs.ge_on_compl]
  have hμν_sc : (μ - ν).restrict sᶜ = μ.restrict sᶜ - ν.restrict sᶜ := by
    exact Measure.restrict_sub_eq_restrict_sub_restrict hs.measurableSet.compl
  have hνμ_s : (ν - μ).restrict s = ν.restrict s - μ.restrict s := by
    exact Measure.restrict_sub_eq_restrict_sub_restrict hs.measurableSet
  have hplus :
      (∫ x, f x ∂(μ - ν)) =
        (∫ x, f x ∂(μ.restrict sᶜ)) - (∫ x, f x ∂(ν.restrict sᶜ)) := by
    have hsplit := integral_add_compl hs.measurableSet hμν
    have hz : (∫ x in s, f x ∂(μ - ν)) = 0 := by
      rw [hμν_s, integral_zero_measure]
    have hsc : (∫ x in sᶜ, f x ∂(μ - ν)) =
        (∫ x, f x ∂(μ.restrict sᶜ)) - (∫ x, f x ∂(ν.restrict sᶜ)) := by
      rw [hμν_sc]
      exact aux_lem_common_perturbation_equations_integral_sub_measure_of_le f
        hνc hμc hs.ge_on_compl
    linarith
  have hminus :
      (∫ x, f x ∂(ν - μ)) =
        (∫ x, f x ∂(ν.restrict s)) - (∫ x, f x ∂(μ.restrict s)) := by
    have hsplit := integral_add_compl hs.measurableSet hνμ
    have hzc : (∫ x in sᶜ, f x ∂(ν - μ)) = 0 := by
      rw [hνμ_sc, integral_zero_measure]
    have hs' : (∫ x in s, f x ∂(ν - μ)) =
        (∫ x, f x ∂(ν.restrict s)) - (∫ x, f x ∂(μ.restrict s)) := by
      rw [hνμ_s]
      exact aux_lem_common_perturbation_equations_integral_sub_measure_of_le f
        hμs hνs hs.le_on
    linarith
  have hμsplit := integral_add_compl hs.measurableSet hfμ
  have hνsplit := integral_add_compl hs.measurableSet hfν
  have hdiff :
      (∫ x, f x ∂(μ - ν)) - (∫ x, f x ∂(ν - μ)) =
        (∫ x, f x ∂μ) - (∫ x, f x ∂ν) := by
    rw [hplus, hminus]
    linarith
  rw [_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn]
  rw [MeasureTheory.Measure.toJordanDecomposition_toSignedMeasure_sub]
  rw [MeasureTheory.Measure.jordanDecompositionOfToSignedMeasureSub_posPart,
    MeasureTheory.Measure.jordanDecompositionOfToSignedMeasureSub_negPart,
    setIntegral_univ, setIntegral_univ]
  exact hdiff

lemma aux_lem_common_perturbation_equations_signedIntegral_smul_nonneg
    {X : Type*} [MeasurableSpace X] (ν : SignedMeasure X) (c : ℝ) (f : X → ℝ)
    (hc : 0 ≤ c) :
    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (c • ν) Set.univ f =
      c * _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ν Set.univ f := by
  rw [_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn,
    MeasureTheory.SignedMeasure.toJordanDecomposition_smul_real,
    MeasureTheory.JordanDecomposition.real_smul_posPart_nonneg _ _ hc,
    MeasureTheory.JordanDecomposition.real_smul_negPart_nonneg _ _ hc]
  simp only [setIntegral_univ, integral_smul_nnreal_measure]
  rw [NNReal.smul_def, NNReal.smul_def, Real.coe_toNNReal c hc]
  simp only [_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn, setIntegral_univ, smul_eq_mul]
  ring

lemma aux_lem_common_perturbation_equations_signedIntegral_one
    {X : Type*} [MeasurableSpace X] (ν : SignedMeasure X) :
    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ν Set.univ (fun _ => (1 : ℝ)) = ν Set.univ := by
  rw [_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn, integral_const, integral_const]
  have hν : ν Set.univ =
      ν.toJordanDecomposition.toSignedMeasure Set.univ := by
    rw [MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition]
  rw [hν, MeasureTheory.JordanDecomposition.toSignedMeasure]
  simp

lemma aux_lem_common_perturbation_equations_cross_signedIntegral_polarization
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}
    {E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m} (Γ : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (f : X → ℝ)
    (hfplus : Integrable f (Γ.measure (u + v)))
    (hfminus : Integrable f (Γ.measure (u - v))) :
    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Γ.cross u v) Set.univ f =
      (1 / 4 : ℝ) *
        ((∫ x, f x ∂(Γ.measure (u + v))) -
          (∫ x, f x ∂(Γ.measure (u - v)))) := by
  let : IsFiniteMeasure (Γ.measure (u + v)) :=
    ⟨Γ.measure_univ_lt_top (u + v) (E.domain.add_mem hu hv)⟩
  let : IsFiniteMeasure (Γ.measure (u - v)) :=
    ⟨Γ.measure_univ_lt_top (u - v) (E.domain.sub_mem hu hv)⟩
  have hcross : Γ.cross u v =
      (1 / 4 : ℝ) •
        ((Γ.measure (u + v)).toSignedMeasure -
          (Γ.measure (u - v)).toSignedMeasure) := by
    ext A hA
    rw [Γ.cross_eq_polarization hu hv A,
      Γ.cross_self (u + v) (E.domain.add_mem hu hv) A hA,
      Γ.cross_self (u - v) (E.domain.sub_mem hu hv) A hA,
      smul_apply, sub_apply,
      Measure.toSignedMeasure_apply_measurable hA,
      Measure.toSignedMeasure_apply_measurable hA]
    simp [Measure.real, smul_eq_mul]
    ring
  rw [hcross,
    aux_lem_common_perturbation_equations_signedIntegral_smul_nonneg _ _ _
      (by norm_num),
    aux_lem_common_perturbation_equations_signedIntegral_sub_toSignedMeasure f
      hfplus hfminus]

lemma aux_lem_common_perturbation_equations_exp_integrable
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    (g : X → ℝ) (hg : Measurable g) (G : ℝ)
    (hgbound : ∀ x, |g x| ≤ G) :
    Integrable (fun x => Real.exp (g x)) μ := by
  apply Integrable.of_bound hg.exp.aestronglyMeasurable (Real.exp G)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact (Real.exp_le_exp).2 (le_trans (le_abs_self _) (hgbound x))

lemma aux_lem_common_perturbation_equations_signedIntegral_sub_integrands
    {X : Type*} [MeasurableSpace X] (ν : SignedMeasure X) (f k : X → ℝ)
    (hfp : Integrable f ν.toJordanDecomposition.posPart)
    (hkp : Integrable k ν.toJordanDecomposition.posPart)
    (hfn : Integrable f ν.toJordanDecomposition.negPart)
    (hkn : Integrable k ν.toJordanDecomposition.negPart) :
    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ν Set.univ (fun x => f x - k x) =
      _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ν Set.univ f -
        _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ν Set.univ k := by
  rw [_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn, _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn,
    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn, setIntegral_univ, setIntegral_univ,
    setIntegral_univ, setIntegral_univ, setIntegral_univ, setIntegral_univ,
    integral_sub hfp hkp, integral_sub hfn hkn]
  ring

lemma aux_lem_common_perturbation_equations_signedIntegral_set_of_compl_eq_zero
    {X : Type*} [MeasurableSpace X] (ν : SignedMeasure X) (B : Set X)
    (f : X → ℝ) (_hB : MeasurableSet B) (hzero : ∀ x, x ∉ B → f x = 0) :
    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ν Set.univ f =
      _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ν B f := by
  rw [_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn, _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn,
    setIntegral_univ]
  congr 1
  · simpa only [setIntegral_univ] using
      (setIntegral_eq_integral_of_forall_compl_eq_zero
        (μ := ν.toJordanDecomposition.posPart) hzero).symm
  · simpa only [setIntegral_univ] using
      (setIntegral_eq_integral_of_forall_compl_eq_zero
        (μ := ν.toJordanDecomposition.negPart) hzero).symm

lemma aux_lem_common_perturbation_equations_weighted_measure_toReal
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}
    {E F : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m}
    (Γ : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E) (Γg : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure F)
    (hdom : F.domain = E.domain) (g : X → ℝ) (hg : Measurable g) (G : ℝ)
    (hgbound : ∀ x, |g x| ≤ G)
    (hweight : ∀ u ∈ E.domain, ∀ A : Set X, MeasurableSet A →
      Γg.measure u A =
        ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(Γ.measure u))
    {u : Lp ℝ 2 m} (hu : u ∈ E.domain) :
    (Γg.measure u Set.univ).toReal =
      ∫ x, Real.exp (g x) ∂(Γ.measure u) := by
  let : IsFiniteMeasure (Γ.measure u) :=
    ⟨Γ.measure_univ_lt_top u hu⟩
  have huF : u ∈ F.domain := hdom.symm ▸ hu
  let : IsFiniteMeasure (Γg.measure u) :=
    ⟨Γg.measure_univ_lt_top u huF⟩
  have hfi := aux_lem_common_perturbation_equations_exp_integrable g hg G hgbound
    (μ := Γ.measure u)
  have hnonneg : 0 ≤ᵐ[Γ.measure u] (fun x => Real.exp (g x)) :=
    Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)
  have hof := ofReal_integral_eq_lintegral_ofReal hfi hnonneg
  rw [hweight u hu Set.univ MeasurableSet.univ]
  simp only [setLIntegral_univ]
  rw [← hof]
  exact ENNReal.toReal_ofReal (integral_nonneg (fun x => le_of_lt (Real.exp_pos _)))

lemma aux_lem_common_perturbation_equations_weighted_cross
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}
    {E F : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m}
    (Γ : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E) (Γg : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure F)
    (hdom : F.domain = E.domain) (g : X → ℝ) (hg : Measurable g) (G : ℝ)
    (hgbound : ∀ x, |g x| ≤ G)
    (hweight : ∀ u ∈ E.domain, ∀ A : Set X, MeasurableSet A →
      Γg.measure u A =
        ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(Γ.measure u))
    {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    Γg.cross u v Set.univ =
      _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Γ.cross u v) Set.univ
        (fun x => Real.exp (g x)) := by
  have huvF : u ∈ F.domain := hdom.symm ▸ hu
  have hvF : v ∈ F.domain := hdom.symm ▸ hv
  let : IsFiniteMeasure (Γ.measure (u + v)) :=
    ⟨Γ.measure_univ_lt_top (u + v) (E.domain.add_mem hu hv)⟩
  let : IsFiniteMeasure (Γ.measure (u - v)) :=
    ⟨Γ.measure_univ_lt_top (u - v) (E.domain.sub_mem hu hv)⟩
  let : IsFiniteMeasure (Γg.measure (u + v)) :=
    ⟨Γg.measure_univ_lt_top (u + v) (F.domain.add_mem huvF hvF)⟩
  let : IsFiniteMeasure (Γg.measure (u - v)) :=
    ⟨Γg.measure_univ_lt_top (u - v) (F.domain.sub_mem huvF hvF)⟩
  have hfi_plus := aux_lem_common_perturbation_equations_exp_integrable g hg G hgbound
    (μ := Γ.measure (u + v))
  have hfi_minus := aux_lem_common_perturbation_equations_exp_integrable g hg G hgbound
    (μ := Γ.measure (u - v))
  have hplus := aux_lem_common_perturbation_equations_weighted_measure_toReal
    Γ Γg hdom g hg G hgbound hweight (E.domain.add_mem hu hv)
  have hminus := aux_lem_common_perturbation_equations_weighted_measure_toReal
    Γ Γg hdom g hg G hgbound hweight (E.domain.sub_mem hu hv)
  calc
    Γg.cross u v Set.univ =
        _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Γg.cross u v) Set.univ (fun _ => (1 : ℝ)) := by
          symm
          exact aux_lem_common_perturbation_equations_signedIntegral_one (Γg.cross u v)
    _ = (1 / 4 : ℝ) *
        ((∫ x, (1 : ℝ) ∂(Γg.measure (u + v))) -
          (∫ x, (1 : ℝ) ∂(Γg.measure (u - v)))) :=
      aux_lem_common_perturbation_equations_cross_signedIntegral_polarization
        Γg huvF hvF (fun _ => (1 : ℝ)) (integrable_const _) (integrable_const _)
    _ = (1 / 4 : ℝ) *
        ((Γg.measure (u + v) Set.univ).toReal -
          (Γg.measure (u - v) Set.univ).toReal) := by
      simp [integral_const, Measure.real]
    _ = (1 / 4 : ℝ) *
        ((∫ x, Real.exp (g x) ∂(Γ.measure (u + v))) -
          (∫ x, Real.exp (g x) ∂(Γ.measure (u - v)))) := by
      rw [hplus, hminus]
    _ = _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Γ.cross u v) Set.univ
        (fun x => Real.exp (g x)) := by
      symm
      exact aux_lem_common_perturbation_equations_cross_signedIntegral_polarization
        Γ hu hv (fun x => Real.exp (g x)) hfi_plus hfi_minus



theorem lem_common_perturbation_equations
    (d : ℕ) (_hd : 2 ≤ d)
    (Q : Opens (SpatialCoordinates d))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (_hQ : ∃ (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ),
      Q = centeredCube zQ rQ hrQ)
    (_hinside : closure ((centeredCube z r hr : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d)))
    (E F Eg Fg : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GammaE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    (GammaF : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure F)
    (GammaEg : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Eg)
    (GammaFg : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Fg)
    (hdomEF : E.domain = F.domain)
    (hdomEg : Eg.domain = E.domain)
    (hdomFg : Fg.domain = E.domain)
    (V0 : Submodule ℝ (DomainL2 Q))
    (hzero : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E
      (centeredCube z r hr : Set (SpatialCoordinates d)) V0)
    (g : SpatialCoordinates d → ℝ) (hg : Measurable g)
    (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B)
    (_hBq : B ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hsupp : ∀ x, x ∉ B → g x = 0)
    (G : ℝ) (hG : IsLUB (Set.range (fun x => |g x|)) G)
    (_hbdd : BddAbove (Set.range (fun x => |g x|)))
    (hweightE : ∀ u ∈ E.domain, ∀ A : Set (SpatialCoordinates d),
      MeasurableSet A →
        GammaEg.measure u A =
          ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(GammaE.measure u))
    (hweightF : ∀ u ∈ F.domain, ∀ A : Set (SpatialCoordinates d),
      MeasurableSet A →
        GammaFg.measure u A =
          ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(GammaF.measure u))
    (uE uF uEg uFg : DomainL2 Q)
    (huE : uE ∈ E.domain)
    (huF : uF ∈ F.domain)
    (huEg : uEg ∈ Eg.domain)
    (huFg : uFg ∈ Fg.domain)
    (_htraceF : uF - uE ∈ V0)
    (_htraceEg : uEg - uE ∈ V0)
    (_htraceFg : uFg - uE ∈ V0)
    (hminE : ∀ v ∈ V0,
      E.form uE uE ≤ E.form (uE + v) (uE + v))
    (hminF : ∀ v ∈ V0,
      F.form uF uF ≤ F.form (uF + v) (uF + v))
    (hminEg : ∀ v ∈ V0,
      Eg.form uEg uEg ≤ Eg.form (uEg + v) (uEg + v))
    (hminFg : ∀ v ∈ V0,
      Fg.form uFg uFg ≤ Fg.form (uFg + v) (uFg + v)) :
    (∀ phi ∈ V0,
      Fg.form (uFg - uF) phi =
        - _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (GammaF.cross uF phi) B
          (fun x => Real.exp (g x) - 1)) ∧
    (∀ phi ∈ V0,
      Eg.form (uEg - uE) phi =
        - _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (GammaE.cross uE phi) B
          (fun x => Real.exp (g x) - 1)) := by
  have hgbound : ∀ x, |g x| ≤ G := fun x => hG.1 ⟨x, rfl⟩
  have hV0E : V0 ≤ E.domain := hzero.le_domain
  have hV0F : V0 ≤ F.domain := by
    intro v hv
    rw [← hdomEF]
    exact hV0E hv
  have hV0Eg : V0 ≤ Eg.domain := by
    intro v hv
    rw [hdomEg]
    exact hV0E hv
  have hV0Fg : V0 ≤ Fg.domain := by
    intro v hv
    rw [hdomFg]
    exact hV0E hv
  have hFgF : Fg.domain = F.domain := hdomFg.trans hdomEF
  constructor
  · intro phi hphi
    have horthF' : F.form uF phi = 0 :=
      aux_lem_common_perturbation_equations_min_orthogonal F V0 uF huF hminF hV0F hphi
    have horthFg' : Fg.form uFg phi = 0 :=
      aux_lem_common_perturbation_equations_min_orthogonal Fg V0 uFg huFg hminFg hV0Fg hphi
    have hphiF' : phi ∈ F.domain := hV0F hphi
    have hphiFg' : phi ∈ Fg.domain := by
      rw [hdomFg]
      exact hV0E hphi
    have huF_Fg' : uF ∈ Fg.domain := by
      rw [hFgF]
      exact huF
    have hweightedF' := aux_lem_common_perturbation_equations_weighted_cross
      GammaF GammaFg hFgF g hg G hgbound hweightF huF hphiF'
    have hform_weightF' : Fg.form uF phi =
        _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (GammaF.cross uF phi) Set.univ
          (fun x => Real.exp (g x)) := by
      rw [← GammaFg.cross_univ uF huF_Fg' phi hphiFg']
      exact hweightedF'
    have hform_baseF' : F.form uF phi =
        _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (GammaF.cross uF phi) Set.univ
          (fun _ => (1 : ℝ)) := by
      rw [← GammaF.cross_univ uF huF phi hphiF']
      exact (aux_lem_common_perturbation_equations_signedIntegral_one
        (GammaF.cross uF phi)).symm
    have hzero_baseF' :
        _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (GammaF.cross uF phi) Set.univ
          (fun _ => (1 : ℝ)) = 0 := by
      rw [← hform_baseF']
      exact horthF'
    have hfi_exp_posF' := aux_lem_common_perturbation_equations_exp_integrable g hg G hgbound
      (μ := (GammaF.cross uF phi).toJordanDecomposition.posPart)
    have hfi_exp_negF' := aux_lem_common_perturbation_equations_exp_integrable g hg G hgbound
      (μ := (GammaF.cross uF phi).toJordanDecomposition.negPart)
    have hfi_one_posF' : Integrable (fun _ : SpatialCoordinates d => (1 : ℝ))
        (GammaF.cross uF phi).toJordanDecomposition.posPart := integrable_const _
    have hfi_one_negF' : Integrable (fun _ : SpatialCoordinates d => (1 : ℝ))
        (GammaF.cross uF phi).toJordanDecomposition.negPart := integrable_const _
    have hsubF' := aux_lem_common_perturbation_equations_signedIntegral_sub_integrands
      (GammaF.cross uF phi) (fun x => Real.exp (g x)) (fun _ => (1 : ℝ))
      hfi_exp_posF' hfi_one_posF' hfi_exp_negF' hfi_one_negF'
    have hsetF' := aux_lem_common_perturbation_equations_signedIntegral_set_of_compl_eq_zero
      (GammaF.cross uF phi) B (fun x => Real.exp (g x) - 1) hB
      (fun x hx => by
        rw [hsupp x hx]
        norm_num)
    have hLHS := aux_lem_common_perturbation_equations_form_sub_left Fg
      huFg huF_Fg' hphiFg'
    calc
      Fg.form (uFg - uF) phi = Fg.form uFg phi - Fg.form uF phi := hLHS
      _ = 0 - _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (GammaF.cross uF phi) Set.univ
          (fun x => Real.exp (g x)) := by rw [horthFg', hform_weightF']
      _ = -_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (GammaF.cross uF phi) Set.univ
          (fun x => Real.exp (g x) - 1) := by
        rw [hsubF', hzero_baseF']
        ring
      _ = -_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (GammaF.cross uF phi) B
          (fun x => Real.exp (g x) - 1) := by rw [hsetF']
  · intro phi hphi
    have huE_Eg : uE ∈ Eg.domain := by rw [hdomEg]; exact huE
    have hphiE : phi ∈ E.domain := hV0E hphi
    have hphiEg : phi ∈ Eg.domain := by rw [hdomEg]; exact hphiE
    have hweightedE := aux_lem_common_perturbation_equations_weighted_cross
      GammaE GammaEg hdomEg g hg G hgbound hweightE huE hphiE
    have hform_weightE : Eg.form uE phi =
        _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (GammaE.cross uE phi) Set.univ
          (fun x => Real.exp (g x)) := by
      rw [← GammaEg.cross_univ uE huE_Eg phi hphiEg]
      exact hweightedE
    have hform_baseE : E.form uE phi =
        _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (GammaE.cross uE phi) Set.univ
          (fun _ => (1 : ℝ)) := by
      rw [← GammaE.cross_univ uE huE phi hphiE]
      exact (aux_lem_common_perturbation_equations_signedIntegral_one
        (GammaE.cross uE phi)).symm
    have horthE : E.form uE phi = 0 :=
      aux_lem_common_perturbation_equations_min_orthogonal E V0 uE huE hminE hV0E hphi
    have horthEg : Eg.form uEg phi = 0 :=
      aux_lem_common_perturbation_equations_min_orthogonal Eg V0 uEg huEg hminEg hV0Eg hphi
    have hzero_baseE :
        _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (GammaE.cross uE phi) Set.univ
          (fun _ => (1 : ℝ)) = 0 := by
      rw [← hform_baseE]
      exact horthE
    have hfi_exp_posE := aux_lem_common_perturbation_equations_exp_integrable g hg G hgbound
      (μ := (GammaE.cross uE phi).toJordanDecomposition.posPart)
    have hfi_exp_negE := aux_lem_common_perturbation_equations_exp_integrable g hg G hgbound
      (μ := (GammaE.cross uE phi).toJordanDecomposition.negPart)
    have hfi_one_posE : Integrable (fun _ : SpatialCoordinates d => (1 : ℝ))
        (GammaE.cross uE phi).toJordanDecomposition.posPart := integrable_const _
    have hfi_one_negE : Integrable (fun _ : SpatialCoordinates d => (1 : ℝ))
        (GammaE.cross uE phi).toJordanDecomposition.negPart := integrable_const _
    have hsubE := aux_lem_common_perturbation_equations_signedIntegral_sub_integrands
      (GammaE.cross uE phi) (fun x => Real.exp (g x)) (fun _ => (1 : ℝ))
      hfi_exp_posE hfi_one_posE hfi_exp_negE hfi_one_negE
    have hsetE := aux_lem_common_perturbation_equations_signedIntegral_set_of_compl_eq_zero
      (GammaE.cross uE phi) B (fun x => Real.exp (g x) - 1) hB
      (fun x hx => by
        rw [hsupp x hx]
        norm_num)
    have huE_Eg' : uE ∈ Eg.domain := by rw [hdomEg]; exact huE
    have hLHS := aux_lem_common_perturbation_equations_form_sub_left Eg
      huEg huE_Eg' hphiEg
    calc
      Eg.form (uEg - uE) phi = Eg.form uEg phi - Eg.form uE phi := hLHS
      _ = 0 - _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (GammaE.cross uE phi) Set.univ
          (fun x => Real.exp (g x)) := by rw [horthEg, hform_weightE]
      _ = -_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (GammaE.cross uE phi) Set.univ
          (fun x => Real.exp (g x) - 1) := by
        rw [hsubE, hzero_baseE]
        ring
      _ = -_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (GammaE.cross uE phi) B
          (fun x => Real.exp (g x) - 1) := by rw [hsetE]

end
end SubdiffusiveProcess.Paper

