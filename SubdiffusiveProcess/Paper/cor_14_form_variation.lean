module

public import SubdiffusiveProcess.Paper.lem_localized_perturbation
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Sobolev.PotentialPerturbation
public import SubdiffusiveProcess.Sobolev.PotentialResponses
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Lane2.LimitForm
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal

namespace Paper



theorem aux_cor_14_signedIntegralOn_one {X : Type*} [MeasurableSpace X]
    (ν : SignedMeasure X) (B : Set X) (hB : MeasurableSet B) :
    DirichletForm.signedIntegralOn ν B (fun _ => (1 : ℝ)) = ν B := by
  unfold DirichletForm.signedIntegralOn
  rw [MeasureTheory.integral_const, MeasureTheory.integral_const]
  simp only [smul_eq_mul, mul_one, MeasureTheory.measureReal_def]
  have hν := congrArg (fun s : SignedMeasure X => s B)
    (MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition ν)
  simpa [hB, MeasureTheory.JordanDecomposition.toSignedMeasure,
    VectorMeasure.sub_apply, MeasureTheory.measureReal_def,
    MeasureTheory.Measure.toSignedMeasure_apply_measurable hB,
    MeasureTheory.Measure.toSignedMeasure_apply_measurable hB] using hν

theorem aux_cor_14_signedIntegralOn_measure {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (B : Set X) (f : X → ℝ) :
    DirichletForm.signedIntegralOn μ.toSignedMeasure B f =
      ∫ x in B, f x ∂μ := by
  let j : JordanDecomposition X :=
    ⟨μ, 0, MeasureTheory.Measure.MutuallySingular.zero_right⟩
  have hj : μ.toSignedMeasure = j.toSignedMeasure := by
    ext s hs
    simp [j, MeasureTheory.JordanDecomposition.toSignedMeasure,
      MeasureTheory.VectorMeasure.sub_apply,
      MeasureTheory.Measure.toSignedMeasure_apply_measurable hs]
  have hdecomp : μ.toSignedMeasure.toJordanDecomposition = j := by
    exact MeasureTheory.SignedMeasure.toJordanDecomposition_eq hj
  simp [DirichletForm.signedIntegralOn, hdecomp, j]

theorem aux_cor_14_signedIntegralOn_measure_sub {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (B : Set X) (hB : MeasurableSet B) (f : X → ℝ)
    (hfμ : Integrable f μ) (hfν : Integrable f ν) :
    DirichletForm.signedIntegralOn (μ.toSignedMeasure - ν.toSignedMeasure) B f =
      (∫ x in B, f x ∂μ) - ∫ x in B, f x ∂ν := by
  rw [DirichletForm.signedIntegralOn,
    MeasureTheory.Measure.toJordanDecomposition_toSignedMeasure_sub]
  simp only [MeasureTheory.Measure.jordanDecompositionOfToSignedMeasureSub_posPart,
    MeasureTheory.Measure.jordanDecompositionOfToSignedMeasureSub_negPart]
  let F : X → ℝ := B.indicator f
  have hFμ : Integrable F μ := hfμ.indicator hB
  have hFν : Integrable F ν := hfν.indicator hB
  have hμsub : Integrable F (μ - ν) := hFμ.mono_measure Measure.sub_le
  have hνsub : Integrable F (ν - μ) := hFν.mono_measure Measure.sub_le
  obtain ⟨s, hs⟩ := MeasureTheory.exists_isHahnDecomposition μ ν
  have hμs : Integrable F (μ.restrict s) := hFμ.restrict
  have hμsc : Integrable F (μ.restrict sᶜ) := hFμ.restrict
  have hνs : Integrable F (ν.restrict s) := hFν.restrict
  have hνsc : Integrable F (ν.restrict sᶜ) := hFν.restrict
  have hμsubs : (μ - ν).restrict s = 0 := by
    rw [MeasureTheory.Measure.restrict_sub_eq_restrict_sub_restrict hs.measurableSet,
      MeasureTheory.Measure.sub_eq_zero_of_le hs.le_on]
  have hνsubsc : (ν - μ).restrict sᶜ = 0 := by
    rw [MeasureTheory.Measure.restrict_sub_eq_restrict_sub_restrict hs.measurableSet.compl,
      MeasureTheory.Measure.sub_eq_zero_of_le hs.ge_on_compl]
  have hμsub_split := MeasureTheory.Measure.restrict_add_restrict_compl
    (μ := μ - ν) hs.measurableSet
  have hνsub_split := MeasureTheory.Measure.restrict_add_restrict_compl
    (μ := ν - μ) hs.measurableSet
  have hμsub_sc :
      (∫ x, F x ∂(μ - ν)) = ∫ x, F x ∂((μ - ν).restrict sᶜ) := by
    calc
      (∫ x, F x ∂(μ - ν)) =
          ∫ x, F x ∂((μ - ν).restrict s + (μ - ν).restrict sᶜ) := by
            rw [hμsub_split]
      _ = (∫ x, F x ∂((μ - ν).restrict s)) +
          ∫ x, F x ∂((μ - ν).restrict sᶜ) :=
            MeasureTheory.integral_add_measure hμsub.restrict hμsub.restrict
      _ = ∫ x, F x ∂((μ - ν).restrict sᶜ) := by
        rw [hμsubs, MeasureTheory.integral_zero_measure, zero_add]
  have hνsub_s :
      (∫ x, F x ∂(ν - μ)) = ∫ x, F x ∂((ν - μ).restrict s) := by
    calc
      (∫ x, F x ∂(ν - μ)) =
          ∫ x, F x ∂((ν - μ).restrict s + (ν - μ).restrict sᶜ) := by
            rw [hνsub_split]
      _ = (∫ x, F x ∂((ν - μ).restrict s)) +
          ∫ x, F x ∂((ν - μ).restrict sᶜ) :=
            MeasureTheory.integral_add_measure hνsub.restrict hνsub.restrict
      _ = ∫ x, F x ∂((ν - μ).restrict s) := by
        rw [hνsubsc, MeasureTheory.integral_zero_measure, add_zero]
  have hμsc_eq : (μ - ν).restrict sᶜ = μ.restrict sᶜ - ν.restrict sᶜ := by
    exact MeasureTheory.Measure.restrict_sub_eq_restrict_sub_restrict hs.measurableSet.compl
  have hνs_eq : (ν - μ).restrict s = ν.restrict s - μ.restrict s := by
    exact MeasureTheory.Measure.restrict_sub_eq_restrict_sub_restrict hs.measurableSet
  have hμsc_add :
      (∫ x, F x ∂(μ.restrict sᶜ)) =
        (∫ x, F x ∂((μ - ν).restrict sᶜ)) + ∫ x, F x ∂(ν.restrict sᶜ) := by
    calc
      (∫ x, F x ∂(μ.restrict sᶜ)) =
          ∫ x, F x ∂((μ - ν).restrict sᶜ + ν.restrict sᶜ) := by
            rw [hμsc_eq, MeasureTheory.Measure.sub_add_cancel_of_le hs.ge_on_compl]
      _ = (∫ x, F x ∂((μ - ν).restrict sᶜ)) +
          ∫ x, F x ∂(ν.restrict sᶜ) :=
            MeasureTheory.integral_add_measure hμsub.restrict hνsc
  have hνs_add :
      (∫ x, F x ∂(ν.restrict s)) =
        (∫ x, F x ∂((ν - μ).restrict s)) + ∫ x, F x ∂(μ.restrict s) := by
    calc
      (∫ x, F x ∂(ν.restrict s)) =
          ∫ x, F x ∂((ν - μ).restrict s + μ.restrict s) := by
            rw [hνs_eq, MeasureTheory.Measure.sub_add_cancel_of_le hs.le_on]
      _ = (∫ x, F x ∂((ν - μ).restrict s)) +
          ∫ x, F x ∂(μ.restrict s) :=
            MeasureTheory.integral_add_measure hνsub.restrict hμs
  have hμ_split := MeasureTheory.Measure.restrict_add_restrict_compl (μ := μ) hs.measurableSet
  have hν_split := MeasureTheory.Measure.restrict_add_restrict_compl (μ := ν) hs.measurableSet
  have hμ_add :
      (∫ x, F x ∂μ) = (∫ x, F x ∂(μ.restrict s)) + ∫ x, F x ∂(μ.restrict sᶜ) := by
    calc
      (∫ x, F x ∂μ) = ∫ x, F x ∂(μ.restrict s + μ.restrict sᶜ) := by
        rw [hμ_split]
      _ = (∫ x, F x ∂(μ.restrict s)) + ∫ x, F x ∂(μ.restrict sᶜ) :=
        MeasureTheory.integral_add_measure hμs hμsc
  have hν_add :
      (∫ x, F x ∂ν) = (∫ x, F x ∂(ν.restrict s)) + ∫ x, F x ∂(ν.restrict sᶜ) := by
    calc
      (∫ x, F x ∂ν) = ∫ x, F x ∂(ν.restrict s + ν.restrict sᶜ) := by
        rw [hν_split]
      _ = (∫ x, F x ∂(ν.restrict s)) + ∫ x, F x ∂(ν.restrict sᶜ) :=
        MeasureTheory.integral_add_measure hνs hνsc
  have hglobal :
      (∫ x, F x ∂(μ - ν)) - ∫ x, F x ∂(ν - μ) =
        (∫ x, F x ∂μ) - ∫ x, F x ∂ν := by
    rw [hμsub_sc, hνsub_s]
    have h1 := congrArg id hμsc_add
    have h2 := congrArg id hνs_add
    linarith [hμ_add, hν_add, h1, h2]
  simpa only [F, MeasureTheory.integral_indicator hB] using hglobal

theorem aux_cor_14_signedIntegralOn_smul_nonneg {X : Type*} [MeasurableSpace X]
    (ν : SignedMeasure X) (B : Set X) (f : X → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    DirichletForm.signedIntegralOn (c • ν) B f =
      c * DirichletForm.signedIntegralOn ν B f := by
  unfold DirichletForm.signedIntegralOn
  rw [MeasureTheory.SignedMeasure.toJordanDecomposition_smul_real,
    MeasureTheory.JordanDecomposition.real_smul_posPart_nonneg _ c hc,
    MeasureTheory.JordanDecomposition.real_smul_negPart_nonneg _ c hc,
    MeasureTheory.Measure.restrict_smul, MeasureTheory.Measure.restrict_smul]
  rw [MeasureTheory.integral_smul_nnreal_measure,
    MeasureTheory.integral_smul_nnreal_measure]
  simp only [NNReal.smul_def, smul_eq_mul]
  rw [Real.coe_toNNReal c hc]
  ring

theorem aux_cor_14_cross_integral
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} {E : DirichletForm.ClosedForm m}
    (Γ : DirichletForm.EnergyMeasure E) {u v : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) (B : Set X) (hB : MeasurableSet B)
    (f : X → ℝ) (hfplus : Integrable f (Γ.measure (u + v)))
    (hfminus : Integrable f (Γ.measure (u - v))) :
    DirichletForm.signedIntegralOn (Γ.cross u v) B f =
      ((∫ x in B, f x ∂(Γ.measure (u + v))) -
        ∫ x in B, f x ∂(Γ.measure (u - v))) / 4 := by
  letI : IsFiniteMeasure (Γ.measure (u + v)) :=
    ⟨Γ.measure_univ_lt_top (u + v) (E.domain.add_mem hu hv)⟩
  letI : IsFiniteMeasure (Γ.measure (u - v)) :=
    ⟨Γ.measure_univ_lt_top (u - v) (E.domain.sub_mem hu hv)⟩
  have hcross : Γ.cross u v =
      (1 / 4 : ℝ) •
        ((Γ.measure (u + v)).toSignedMeasure -
          (Γ.measure (u - v)).toSignedMeasure) := by
    ext A hA
    rw [Γ.cross_eq_polarization hu hv A,
      Γ.cross_self (u + v) (E.domain.add_mem hu hv) A hA,
      Γ.cross_self (u - v) (E.domain.sub_mem hu hv) A hA,
      VectorMeasure.smul_apply, VectorMeasure.sub_apply]
    change (((Γ.measure (u + v)) A).toReal -
      ((Γ.measure (u - v)) A).toReal) / 4 =
      (1 / 4 : ℝ) *
        ((Γ.measure (u + v)).toSignedMeasure A -
          (Γ.measure (u - v)).toSignedMeasure A)
    rw [MeasureTheory.Measure.toSignedMeasure_apply_measurable hA,
      MeasureTheory.Measure.toSignedMeasure_apply_measurable hA]
    simp only [MeasureTheory.measureReal_def]
    ring
  rw [hcross, aux_cor_14_signedIntegralOn_smul_nonneg _ _ _ (by norm_num),
    aux_cor_14_signedIntegralOn_measure_sub _ _ B hB f hfplus hfminus]
  ring

theorem aux_cor_14_exp_integrable
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} {E : DirichletForm.ClosedForm m}
    (Γ : DirichletForm.EnergyMeasure E) (g : X → ℝ) (hg : Measurable g)
    (S : ℝ) (hS : IsLUB (Set.range (fun x => |g x|)) S)
    {u : Lp ℝ 2 m} (hu : u ∈ E.domain) :
    Integrable (fun x => Real.exp (g x)) (Γ.measure u) := by
  letI : IsFiniteMeasure (Γ.measure u) := ⟨Γ.measure_univ_lt_top u hu⟩
  refine Integrable.of_bound hg.exp.aestronglyMeasurable (Real.exp S) ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  exact (Real.exp_le_exp.mpr
    (le_trans (le_abs_self (g x)) (hS.1 ⟨x, rfl⟩)))

theorem aux_cor_14_weighted_mass
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} {E Eg : DirichletForm.ClosedForm m}
    (Γ : DirichletForm.EnergyMeasure E) (Gammag : DirichletForm.EnergyMeasure Eg)
    (g : X → ℝ) (hg : Measurable g) (S : ℝ)
    (hS : IsLUB (Set.range (fun x => |g x|)) S)
    {u : Lp ℝ 2 m} (hu : u ∈ E.domain)
    (hweight : ∀ v ∈ E.domain, ∀ A : Set X, MeasurableSet A →
      Gammag.measure v A =
        ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(Γ.measure v))
    {A : Set X} (hA : MeasurableSet A) :
    (Gammag.measure u A).toReal =
      ∫ x in A, Real.exp (g x) ∂(Γ.measure u) := by
  rw [hweight u hu A hA]
  have hI := aux_cor_14_exp_integrable Γ g hg S hS hu
  have hI' : Integrable (fun x => Real.exp (g x))
      ((Γ.measure u).restrict A) := hI.restrict
  have hnonneg : 0 ≤ᵐ[(Γ.measure u).restrict A] (fun x => Real.exp (g x)) :=
    Filter.Eventually.of_forall (fun x => Real.exp_nonneg (g x))
  have hEq := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hI' hnonneg
  rw [← hEq]
  exact ENNReal.toReal_ofReal (integral_nonneg_of_ae hnonneg)

theorem aux_cor_14_weighted_cross_one
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} {E Eg : DirichletForm.ClosedForm m}
    (Γ : DirichletForm.EnergyMeasure E) (Gammag : DirichletForm.EnergyMeasure Eg)
    (hdom : Eg.domain = E.domain) (g : X → ℝ) (hg : Measurable g)
    (S : ℝ) (hS : IsLUB (Set.range (fun x => |g x|)) S)
    (hweight : ∀ v ∈ E.domain, ∀ A : Set X, MeasurableSet A →
      Gammag.measure v A =
        ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(Γ.measure v))
    {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    {A : Set X} (hA : MeasurableSet A) :
    DirichletForm.signedIntegralOn (Gammag.cross u v) A (fun _ => (1 : ℝ)) =
      DirichletForm.signedIntegralOn (Γ.cross u v) A
        (fun x => Real.exp (g x)) := by
  have huEg : u ∈ Eg.domain := by rw [hdom]; exact hu
  have hvEg : v ∈ Eg.domain := by rw [hdom]; exact hv
  have huvE : u + v ∈ E.domain := E.domain.add_mem hu hv
  have huvEg : u + v ∈ Eg.domain := by rw [hdom]; exact huvE
  have huvsubE : u - v ∈ E.domain := E.domain.sub_mem hu hv
  have huvsubEg : u - v ∈ Eg.domain := by rw [hdom]; exact huvsubE
  letI : IsFiniteMeasure (Gammag.measure (u + v)) :=
    ⟨Gammag.measure_univ_lt_top (u + v) huvEg⟩
  letI : IsFiniteMeasure (Gammag.measure (u - v)) :=
    ⟨Gammag.measure_univ_lt_top (u - v) huvsubEg⟩
  have hIplus := aux_cor_14_exp_integrable Γ g hg S hS huvE
  have hIminus := aux_cor_14_exp_integrable Γ g hg S hS huvsubE
  have hGplus : Integrable (fun _ : X => (1 : ℝ)) (Gammag.measure (u + v)) :=
    integrable_const _
  have hGminus : Integrable (fun _ : X => (1 : ℝ)) (Gammag.measure (u - v)) :=
    integrable_const _
  have hGplus' : (∫ x in A, (1 : ℝ) ∂(Gammag.measure (u + v))) =
      (Gammag.measure (u + v) A).toReal := by
    rw [integral_const]
    simp [MeasureTheory.measureReal_def]
  have hGminus' : (∫ x in A, (1 : ℝ) ∂(Gammag.measure (u - v))) =
      (Gammag.measure (u - v) A).toReal := by
    rw [integral_const]
    simp [MeasureTheory.measureReal_def]
  rw [aux_cor_14_cross_integral Gammag huEg hvEg A hA (fun _ => (1 : ℝ))
      hGplus hGminus,
    aux_cor_14_cross_integral Γ hu hv A hA (fun x => Real.exp (g x)) hIplus hIminus,
    ← aux_cor_14_weighted_mass Γ Gammag g hg S hS huvE
      (fun w hw C hC => hweight w hw C hC) hA,
    ← aux_cor_14_weighted_mass Γ Gammag g hg S hS huvsubE
      (fun w hw C hC => hweight w hw C hC) hA,
    hGplus', hGminus']

theorem aux_cor_14_signedIntegralOn_add
    {X : Type*} [MeasurableSpace X]
    (ν ξ : MeasureTheory.SignedMeasure X) (B : Set X) (hB : MeasurableSet B)
    (f : X → ℝ) (hf : Measurable f)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, ‖f x‖ ≤ C) :
    DirichletForm.signedIntegralOn (ν + ξ) B f =
      DirichletForm.signedIntegralOn ν B f +
        DirichletForm.signedIntegralOn ξ B f := by
  let p := ν.toJordanDecomposition.posPart
  let n := ν.toJordanDecomposition.negPart
  let q := ξ.toJordanDecomposition.posPart
  let r := ξ.toJordanDecomposition.negPart
  have hν : ν = p.toSignedMeasure - n.toSignedMeasure := by
    simpa [p, n, JordanDecomposition.toSignedMeasure] using
      (SignedMeasure.toSignedMeasure_toJordanDecomposition ν).symm
  have hξ : ξ = q.toSignedMeasure - r.toSignedMeasure := by
    simpa [q, r, JordanDecomposition.toSignedMeasure] using
      (SignedMeasure.toSignedMeasure_toJordanDecomposition ξ).symm
  have hsum0 : ν + ξ = (p.toSignedMeasure - n.toSignedMeasure) +
      (q.toSignedMeasure - r.toSignedMeasure) :=
    congrArg₂ (fun a b : MeasureTheory.SignedMeasure X => a + b) hν hξ
  have hsum : ν + ξ = (p + q).toSignedMeasure - (n + r).toSignedMeasure := by
    calc
      ν + ξ = (p.toSignedMeasure - n.toSignedMeasure) +
          (q.toSignedMeasure - r.toSignedMeasure) := hsum0
      _ = (p + q).toSignedMeasure - (n + r).toSignedMeasure := by
        rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
        abel
  have hfp : Integrable f p :=
    Integrable.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall hbound)
  have hfn : Integrable f n :=
    Integrable.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall hbound)
  have hfq : Integrable f q :=
    Integrable.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall hbound)
  have hfr : Integrable f r :=
    Integrable.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall hbound)
  have hfpq : Integrable f (p + q) :=
    Integrable.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall hbound)
  have hfnr : Integrable f (n + r) :=
    Integrable.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall hbound)
  have hsub := aux_cor_14_signedIntegralOn_measure_sub (p + q) (n + r) B hB f
    hfpq hfnr
  have hνint : DirichletForm.signedIntegralOn ν B f =
      (∫ x in B, f x ∂p) - ∫ x in B, f x ∂n := by
    calc
      DirichletForm.signedIntegralOn ν B f =
          DirichletForm.signedIntegralOn (p.toSignedMeasure - n.toSignedMeasure) B f :=
        congrArg (fun s : MeasureTheory.SignedMeasure X =>
          DirichletForm.signedIntegralOn s B f) hν
      _ = (∫ x in B, f x ∂p) - ∫ x in B, f x ∂n :=
        aux_cor_14_signedIntegralOn_measure_sub p n B hB f hfp hfn
  have hξint : DirichletForm.signedIntegralOn ξ B f =
      (∫ x in B, f x ∂q) - ∫ x in B, f x ∂r := by
    calc
      DirichletForm.signedIntegralOn ξ B f =
          DirichletForm.signedIntegralOn (q.toSignedMeasure - r.toSignedMeasure) B f :=
        congrArg (fun s : MeasureTheory.SignedMeasure X =>
          DirichletForm.signedIntegralOn s B f) hξ
      _ = (∫ x in B, f x ∂q) - ∫ x in B, f x ∂r :=
        aux_cor_14_signedIntegralOn_measure_sub q r B hB f hfq hfr
  have hsumint : DirichletForm.signedIntegralOn (ν + ξ) B f =
      DirichletForm.signedIntegralOn ((p + q).toSignedMeasure - (n + r).toSignedMeasure)
        B f :=
    congrArg (fun s : MeasureTheory.SignedMeasure X =>
      DirichletForm.signedIntegralOn s B f) hsum
  rw [hsumint, hνint, hξint]
  rw [hsub]
  change (∫ x, f x ∂((p + q).restrict B)) -
      ∫ x, f x ∂((n + r).restrict B) = _
  rw [Measure.restrict_add, Measure.restrict_add,
    integral_add_measure hfp.restrict hfq.restrict,
    integral_add_measure hfn.restrict hfr.restrict]
  ring

theorem aux_cor_14_signedIntegralOn_neg_measure
    {X : Type*} [MeasurableSpace X]
    (ν : MeasureTheory.SignedMeasure X) (B : Set X) (f : X → ℝ) :
    DirichletForm.signedIntegralOn (-ν) B f =
      -DirichletForm.signedIntegralOn ν B f := by
  simp only [DirichletForm.signedIntegralOn,
    SignedMeasure.toJordanDecomposition_neg,
    JordanDecomposition.neg_posPart, JordanDecomposition.neg_negPart,
    integral_neg]
  ring

theorem aux_cor_14_signedIntegralOn_sub_fun
    {X : Type*} [MeasurableSpace X]
    (ν : MeasureTheory.SignedMeasure X) (B : Set X) (f h : X → ℝ)
    (hfpos : Integrable f ν.toJordanDecomposition.posPart)
    (hfneg : Integrable f ν.toJordanDecomposition.negPart)
    (hhpos : Integrable h ν.toJordanDecomposition.posPart)
    (hhneg : Integrable h ν.toJordanDecomposition.negPart) :
    DirichletForm.signedIntegralOn ν B (fun x => f x - h x) =
      DirichletForm.signedIntegralOn ν B f -
        DirichletForm.signedIntegralOn ν B h := by
  simp only [DirichletForm.signedIntegralOn]
  rw [integral_sub hfpos.restrict hhpos.restrict,
    integral_sub hfneg.restrict hhneg.restrict]
  ring

theorem aux_cor_14_integral_support
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hBA : B ⊆ A) (f : X → ℝ) (hfzero : ∀ x, x ∉ B → f x = 0) :
    (∫ x in A, f x ∂μ) = ∫ x in B, f x ∂μ := by
  rw [← integral_indicator hA, ← integral_indicator hB]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    by_cases hxB : x ∈ B
    · have hxA : x ∈ A := hBA hxB
      simp [Set.indicator, hxA, hxB]
    · simp [Set.indicator, hxB, hfzero x hxB])

theorem aux_cor_14_signedIntegralOn_support
    {X : Type*} [MeasurableSpace X]
    (ν : MeasureTheory.SignedMeasure X) (A B : Set X)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hBA : B ⊆ A)
    (f : X → ℝ) (hfzero : ∀ x, x ∉ B → f x = 0) :
    DirichletForm.signedIntegralOn ν A f =
      DirichletForm.signedIntegralOn ν B f := by
  have hpart : ∀ μ : Measure X,
      (∫ x in A, f x ∂μ) = ∫ x in B, f x ∂μ := fun μ =>
    aux_cor_14_integral_support μ A B hA hB hBA f hfzero
  simp only [DirichletForm.signedIntegralOn]
  rw [hpart, hpart]

theorem aux_cor_14_difference_equation
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} {E Eg : DirichletForm.ClosedForm m}
    (Γ : DirichletForm.EnergyMeasure E) (Gammag : DirichletForm.EnergyMeasure Eg)
    (hdom : Eg.domain = E.domain) (V0 : Submodule ℝ (Lp ℝ 2 m))
    (hV0E : V0 ≤ E.domain) (hV0Eg : V0 ≤ Eg.domain)
    (g : X → ℝ) (hg : Measurable g) (S : ℝ)
    (hS : IsLUB (Set.range (fun x => |g x|)) S)
    (hweight : ∀ v ∈ E.domain, ∀ A : Set X, MeasurableSet A →
      Gammag.measure v A =
        ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(Γ.measure v))
    (B A : Set X) (hB : MeasurableSet B) (hA : MeasurableSet A) (hBA : B ⊆ A)
    (hgzero : ∀ x, x ∉ B → g x = 0)
    {u ug : Lp ℝ 2 m} (hu : u ∈ E.domain) (hug : ug ∈ Eg.domain)
    (hdiff : ug - u ∈ V0) (F : Lp ℝ 2 m → ℝ)
    (hE : ∀ v ∈ V0,
      DirichletForm.signedIntegralOn (Γ.cross u v) A (fun _ => (1 : ℝ)) = F v)
    (hG : ∀ v ∈ V0,
      DirichletForm.signedIntegralOn (Gammag.cross ug v) A (fun _ => (1 : ℝ)) = F v) :
    ∀ v ∈ V0,
      DirichletForm.signedIntegralOn (Gammag.cross (ug - u) v) A
          (fun _ => (1 : ℝ)) =
        -DirichletForm.signedIntegralOn (Γ.cross u v) B
          (fun x => Real.exp (g x) - 1) := by
  have huEg : u ∈ Eg.domain := by rw [hdom]; exact hu
  have hzero : ∀ x, x ∉ B → Real.exp (g x) - 1 = 0 := by
    intro x hx
    rw [hgzero x hx, Real.exp_zero]
    norm_num
  intro v hv
  have hvE : v ∈ E.domain := hV0E hv
  have hvEg : v ∈ Eg.domain := hV0Eg hv
  have hnegU : -u ∈ Eg.domain := Eg.domain.neg_mem huEg
  have hcrossdiff : Gammag.cross (ug - u) v =
      Gammag.cross ug v + -(Gammag.cross u v) := by
    calc
      Gammag.cross (ug - u) v = Gammag.cross (ug + -u) v := by
        rw [sub_eq_add_neg]
      _ = Gammag.cross ug v + Gammag.cross (-u) v :=
        Gammag.cross_add_left hug hnegU hvEg
      _ = Gammag.cross ug v + -(Gammag.cross u v) := by
        rw [show -u = (-1 : ℝ) • u by simp,
          Gammag.cross_smul_left (-1) huEg hvEg]
        congr 1
        ext C
        simp only [smul_apply, neg_apply, smul_eq_mul, neg_one_mul]
  have hsubint :
      DirichletForm.signedIntegralOn (Gammag.cross (ug - u) v) A
          (fun _ => (1 : ℝ)) =
        DirichletForm.signedIntegralOn (Gammag.cross ug v) A
            (fun _ => (1 : ℝ)) -
          DirichletForm.signedIntegralOn (Gammag.cross u v) A
            (fun _ => (1 : ℝ)) := by
    rw [hcrossdiff]
    calc
      DirichletForm.signedIntegralOn
          (Gammag.cross ug v + -(Gammag.cross u v)) A (fun _ => (1 : ℝ)) =
          DirichletForm.signedIntegralOn (Gammag.cross ug v) A (fun _ => (1 : ℝ)) +
            DirichletForm.signedIntegralOn (-(Gammag.cross u v)) A (fun _ => (1 : ℝ)) :=
        aux_cor_14_signedIntegralOn_add _ _ A hA (fun _ : X => (1 : ℝ))
          measurable_const (C := 1) (by norm_num) (by intro x; simp)
      _ = DirichletForm.signedIntegralOn (Gammag.cross ug v) A (fun _ => (1 : ℝ)) -
          DirichletForm.signedIntegralOn (Gammag.cross u v) A (fun _ => (1 : ℝ)) := by
        rw [aux_cor_14_signedIntegralOn_neg_measure]
        ring
  have hW_u := aux_cor_14_weighted_cross_one Γ Gammag hdom g hg S hS hweight
    hu hvE hA
  have hexp_meas : Measurable (fun x : X => Real.exp (g x)) := hg.exp
  have hexp_bound : ∀ x : X, ‖Real.exp (g x)‖ ≤ Real.exp S := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_exp.mpr (le_trans (le_abs_self (g x)) (hS.1 ⟨x, rfl⟩))
  have hexp_u_pos : Integrable (fun x : X => Real.exp (g x))
      (Γ.cross u v).toJordanDecomposition.posPart :=
    Integrable.of_bound hexp_meas.aestronglyMeasurable (Real.exp S)
      (Filter.Eventually.of_forall hexp_bound)
  have hexp_u_neg : Integrable (fun x : X => Real.exp (g x))
      (Γ.cross u v).toJordanDecomposition.negPart :=
    Integrable.of_bound hexp_meas.aestronglyMeasurable (Real.exp S)
      (Filter.Eventually.of_forall hexp_bound)
  have hone_u_pos : Integrable (fun _ : X => (1 : ℝ))
      (Γ.cross u v).toJordanDecomposition.posPart := integrable_const _
  have hone_u_neg : Integrable (fun _ : X => (1 : ℝ))
      (Γ.cross u v).toJordanDecomposition.negPart := integrable_const _
  have hsubfun := aux_cor_14_signedIntegralOn_sub_fun (Γ.cross u v) A
    (fun x : X => Real.exp (g x)) (fun _ => (1 : ℝ))
    hexp_u_pos hexp_u_neg hone_u_pos hone_u_neg
  have hlocal := aux_cor_14_signedIntegralOn_support (Γ.cross u v) A B hA hB hBA
    (fun x : X => Real.exp (g x) - 1) hzero
  rw [hsubint, hG v hv, hW_u]
  calc
    F v - DirichletForm.signedIntegralOn (Γ.cross u v) A
        (fun x => Real.exp (g x)) =
        -(DirichletForm.signedIntegralOn (Γ.cross u v) A
          (fun x => Real.exp (g x)) -
          DirichletForm.signedIntegralOn (Γ.cross u v) A (fun _ => (1 : ℝ))) := by
      rw [hE v hv]
      ring
    _ = -DirichletForm.signedIntegralOn (Γ.cross u v) A
        (fun x => Real.exp (g x) - 1) := by rw [hsubfun]
    _ = -DirichletForm.signedIntegralOn (Γ.cross u v) B
        (fun x => Real.exp (g x) - 1) := by rw [hlocal]

theorem aux_cor_14_energy_add
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} {E : DirichletForm.ClosedForm m}
    (Γ : DirichletForm.EnergyMeasure E) {u v : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) {A : Set X}
    (hA : MeasurableSet A) :
    (Γ.measure (u + v) A).toReal =
      (Γ.measure u A).toReal + 2 * Γ.cross u v A + (Γ.measure v A).toReal := by
  rw [← Γ.cross_self (u + v) (E.domain.add_mem hu hv) A hA,
    Γ.cross_add_self_apply hu hv A, Γ.cross_self u hu A hA,
    Γ.cross_self v hv A hA]

theorem aux_cor_14_energy_add_smul
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} {E : DirichletForm.ClosedForm m}
    (Γ : DirichletForm.EnergyMeasure E) {u v : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) (t : ℝ) {A : Set X}
    (hA : MeasurableSet A) :
    (Γ.measure (u + t • v) A).toReal =
      (Γ.measure u A).toReal + 2 * t * Γ.cross u v A +
        t ^ 2 * Γ.cross v v A := by
  have htv : t • v ∈ E.domain := E.domain.smul_mem t hv
  have hdiag : (Γ.measure (t • v) A).toReal = t ^ 2 * Γ.cross v v A := by
    rw [← Γ.cross_self (t • v) htv A hA,
      Γ.cross_smul_left t hv htv,
      Γ.cross_smul_right t (u := v) (v := v) hv hv, VectorMeasure.smul_apply,
      VectorMeasure.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  rw [aux_cor_14_energy_add Γ hu htv hA, hdiag,
    Γ.cross_smul_right t (u := u) (v := v) hu hv, VectorMeasure.smul_apply,
    smul_eq_mul]
  ring

theorem aux_cor_14_energy_sub
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} {E : DirichletForm.ClosedForm m}
    (Γ : DirichletForm.EnergyMeasure E) {u v : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) {A : Set X}
    (hA : MeasurableSet A) :
    (Γ.measure (u - v) A).toReal =
      (Γ.measure u A).toReal - 2 * Γ.cross u v A + (Γ.measure v A).toReal := by
  rw [← Γ.cross_self (u - v) (E.domain.sub_mem hu hv) A hA,
    Γ.cross_sub_self_apply hu hv A, Γ.cross_self u hu A hA,
    Γ.cross_self v hv A hA]

theorem aux_cor_14_quadratic_linear {A C : ℝ}
    (hA : 0 ≤ A) (h : ∀ t : ℝ, 0 ≤ 2 * t * C + t ^ 2 * A) : C = 0 := by
  by_contra hC
  have hA1 : 0 < A + 1 := by linarith
  have ht := h (-(C / (A + 1)))
  field_simp [ne_of_gt hA1] at ht
  nlinarith [sq_pos_of_ne_zero hC]

theorem aux_cor_14_minimizer_cross_zero
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} {E : DirichletForm.ClosedForm m}
    (Γ : DirichletForm.EnergyMeasure E) (V0 : Submodule ℝ (Lp ℝ 2 m))
    (hV0 : V0 ≤ E.domain) {u : Lp ℝ 2 m} (hu : u ∈ E.domain)
    {A : Set X} (hA : MeasurableSet A)
    (hmin : ∀ v ∈ E.domain, v - u ∈ V0 →
      (Γ.measure u A).toReal ≤ (Γ.measure v A).toReal) :
    ∀ w ∈ V0, Γ.cross u w A = 0 := by
  intro w hw
  apply aux_cor_14_quadratic_linear (Γ.cross_self_nonneg (hV0 hw) hA)
  intro t
  have htw : t • w ∈ V0 := V0.smul_mem t hw
  have huv : u + t • w ∈ E.domain := E.domain.add_mem hu (hV0 htw)
  have hdiff : u + t • w - u ∈ V0 := by
    rw [add_sub_cancel_left]
    exact htw
  have h := hmin (u + t • w) huv hdiff
  rw [aux_cor_14_energy_add_smul Γ hu (hV0 hw) t hA] at h
  linarith

theorem aux_cor_14_minimizer_identity
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} {E Eg : DirichletForm.ClosedForm m}
    (Γ : DirichletForm.EnergyMeasure E) (Gammag : DirichletForm.EnergyMeasure Eg)
    (hdom : Eg.domain = E.domain) (V0 : Submodule ℝ (Lp ℝ 2 m))
    (hV0Eg : V0 ≤ Eg.domain) (g : X → ℝ) (hg : Measurable g)
    (S : ℝ) (hS : IsLUB (Set.range (fun x => |g x|)) S)
    (hweight : ∀ v ∈ E.domain, ∀ A : Set X, MeasurableSet A →
      Gammag.measure v A =
        ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(Γ.measure v))
    (B A : Set X) (hB : MeasurableSet B) (hA : MeasurableSet A) (hBA : B ⊆ A)
    (hgzero : ∀ x, x ∉ B → g x = 0)
    {u ug : Lp ℝ 2 m} (hu : u ∈ E.domain) (hug : ug ∈ Eg.domain)
    (hdiff : ug - u ∈ V0)
    (hminEg : ∀ v ∈ Eg.domain, v - u ∈ V0 →
      (Gammag.measure ug A).toReal ≤ (Gammag.measure v A).toReal) :
    (Gammag.measure ug A).toReal - (Γ.measure u A).toReal =
      (∫ x in B, (Real.exp (g x) - 1) ∂(Γ.measure u)) -
        (Gammag.measure (ug - u) A).toReal := by
  have huEg : u ∈ Eg.domain := by rw [hdom]; exact hu
  have hdeltaEg : ug - u ∈ Eg.domain := Eg.domain.sub_mem hug huEg
  have hminEg' : ∀ v ∈ Eg.domain, v - ug ∈ V0 →
      (Gammag.measure ug A).toReal ≤ (Gammag.measure v A).toReal := by
    intro v hv hvg
    apply hminEg v hv
    have hvu : v - u = (v - ug) + (ug - u) := by abel
    rw [hvu]
    exact V0.add_mem hvg hdiff
  have hEuler := aux_cor_14_minimizer_cross_zero Gammag V0 hV0Eg hug hA hminEg'
    (ug - u) hdiff
  have hugu : u + (ug - u) = ug := by abel
  have hcrossrel : Gammag.cross ug (ug - u) A =
      Gammag.cross u (ug - u) A + Gammag.cross (ug - u) (ug - u) A := by
    calc
      Gammag.cross ug (ug - u) A =
          Gammag.cross (u + (ug - u)) (ug - u) A := by rw [hugu]
      _ = Gammag.cross u (ug - u) A + Gammag.cross (ug - u) (ug - u) A := by
        rw [Gammag.cross_add_left huEg hdeltaEg hdeltaEg, VectorMeasure.add_apply]
  have hcrossuδ : Gammag.cross u (ug - u) A =
      -(Gammag.measure (ug - u) A).toReal := by
    rw [hcrossrel, Gammag.cross_self (ug - u) hdeltaEg A hA] at hEuler
    linarith
  have henergy := aux_cor_14_energy_add Gammag huEg hdeltaEg hA
  rw [hugu] at henergy
  have hmassrel : (Gammag.measure ug A).toReal =
      (Gammag.measure u A).toReal - (Gammag.measure (ug - u) A).toReal := by
    rw [hcrossuδ] at henergy
    linarith
  letI : IsFiniteMeasure (Γ.measure u) :=
    ⟨Γ.measure_univ_lt_top u hu⟩
  have hGmassu := aux_cor_14_weighted_mass Γ Gammag g hg S hS hu
    (fun v hv C hC => hweight v hv C hC) hA
  have hIexp := aux_cor_14_exp_integrable Γ g hg S hS hu
  have hone : Integrable (fun _ : X => (1 : ℝ)) (Γ.measure u) := integrable_const _
  have hGammaone : (Γ.measure u A).toReal =
      ∫ x in A, (1 : ℝ) ∂(Γ.measure u) := by
    rw [integral_const]
    simp [MeasureTheory.measureReal_def]
  have hsubq : (∫ x in A, Real.exp (g x) ∂(Γ.measure u)) -
      ∫ x in A, (1 : ℝ) ∂(Γ.measure u) =
        ∫ x in A, (Real.exp (g x) - 1) ∂(Γ.measure u) := by
    exact (integral_sub hIexp.restrict hone.restrict).symm
  have hzero' : ∀ x, x ∉ B → Real.exp (g x) - 1 = 0 := by
    intro x hx
    rw [hgzero x hx, Real.exp_zero]
    norm_num
  have hlocal := aux_cor_14_integral_support (Γ.measure u) A B hA hB hBA
    (fun x : X => Real.exp (g x) - 1) hzero'
  have hbase : (Gammag.measure u A).toReal - (Γ.measure u A).toReal =
      ∫ x in B, (Real.exp (g x) - 1) ∂(Γ.measure u) := by
    rw [hGmassu, hGammaone]
    calc
      (∫ x in A, Real.exp (g x) ∂(Γ.measure u)) -
          ∫ x in A, (1 : ℝ) ∂(Γ.measure u) =
          ∫ x in A, (Real.exp (g x) - 1) ∂(Γ.measure u) := hsubq
      _ = ∫ x in B, (Real.exp (g x) - 1) ∂(Γ.measure u) := hlocal
  nlinarith [hmassrel, hbase]

theorem aux_cor_14_load_identity
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} {E Eg : DirichletForm.ClosedForm m}
    (Γ : DirichletForm.EnergyMeasure E) (Gammag : DirichletForm.EnergyMeasure Eg)
    (hdom : Eg.domain = E.domain) (V0 : Submodule ℝ (Lp ℝ 2 m))
    (g : X → ℝ) (hg : Measurable g) (S : ℝ)
    (hS : IsLUB (Set.range (fun x => |g x|)) S)
    (hweight : ∀ v ∈ E.domain, ∀ A : Set X, MeasurableSet A →
      Gammag.measure v A =
        ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(Γ.measure v))
    (B A : Set X) (hB : MeasurableSet B) (hA : MeasurableSet A) (hBA : B ⊆ A)
    (hgzero : ∀ x, x ∉ B → g x = 0)
    {f u ug : Lp ℝ 2 m} (huf : u ∈ V0) (hugf : ug ∈ V0)
    (hu : u ∈ E.domain) (hug : ug ∈ Eg.domain)
    (hE : ∀ v ∈ V0,
      DirichletForm.signedIntegralOn (Γ.cross u v) A (fun _ => (1 : ℝ)) = inner ℝ f v)
    (hG : ∀ v ∈ V0,
      DirichletForm.signedIntegralOn (Gammag.cross ug v) A (fun _ => (1 : ℝ)) = inner ℝ f v) :
    inner ℝ f ug - inner ℝ f u =
      (Gammag.measure (ug - u) A).toReal -
        (∫ x in B, (Real.exp (g x) - 1) ∂(Γ.measure u)) := by
  have huEg : u ∈ Eg.domain := by rw [hdom]; exact hu
  have hGug := hG ug hugf
  have hGu := hG u huf
  have hEu := hE u huf
  rw [aux_cor_14_signedIntegralOn_one (Gammag.cross ug ug) A hA] at hGug
  rw [aux_cor_14_signedIntegralOn_one (Gammag.cross ug u) A hA] at hGu
  rw [aux_cor_14_signedIntegralOn_one (Γ.cross u u) A hA] at hEu
  rw [Gammag.cross_self ug hug A hA] at hGug
  rw [Γ.cross_self u hu A hA] at hEu
  have hGmassu := aux_cor_14_weighted_mass Γ Gammag g hg S hS hu
    (fun v hv C hC => hweight v hv C hC) hA
  letI : IsFiniteMeasure (Γ.measure u) :=
    ⟨Γ.measure_univ_lt_top u hu⟩
  have hIexp := aux_cor_14_exp_integrable Γ g hg S hS hu
  have hone : Integrable (fun _ : X => (1 : ℝ)) (Γ.measure u) := integrable_const _
  have hGammaone : (Γ.measure u A).toReal =
      ∫ x in A, (1 : ℝ) ∂(Γ.measure u) := by
    rw [integral_const]
    simp [MeasureTheory.measureReal_def]
  have hsubq : (∫ x in A, Real.exp (g x) ∂(Γ.measure u)) -
      ∫ x in A, (1 : ℝ) ∂(Γ.measure u) =
        ∫ x in A, (Real.exp (g x) - 1) ∂(Γ.measure u) := by
    exact (integral_sub hIexp.restrict hone.restrict).symm
  have hzero' : ∀ x, x ∉ B → Real.exp (g x) - 1 = 0 := by
    intro x hx
    rw [hgzero x hx, Real.exp_zero]
    norm_num
  have hlocal := aux_cor_14_integral_support (Γ.measure u) A B hA hB hBA
    (fun x : X => Real.exp (g x) - 1) hzero'
  have hbase : (Gammag.measure u A).toReal - (Γ.measure u A).toReal =
      ∫ x in B, (Real.exp (g x) - 1) ∂(Γ.measure u) := by
    rw [hGmassu, hGammaone]
    calc
      (∫ x in A, Real.exp (g x) ∂(Γ.measure u)) -
          ∫ x in A, (1 : ℝ) ∂(Γ.measure u) =
          ∫ x in A, (Real.exp (g x) - 1) ∂(Γ.measure u) := hsubq
      _ = ∫ x in B, (Real.exp (g x) - 1) ∂(Γ.measure u) := hlocal
  rw [aux_cor_14_energy_sub Gammag hug huEg hA]
  nlinarith [hGug, hGu, hEu, hbase]

theorem cor_14_form_variation :
    (∀ (d : ℕ) (Q : Opens (SpatialCoordinates d))
        (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      let q := centeredCube z r hr;
      (closure (q : Set (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d))) →
      (∀ (E Eg : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
          (Gamma : DirichletForm.EnergyMeasure E) (Gammag : DirichletForm.EnergyMeasure Eg),
        Eg.domain = E.domain →
        ∀ (V0 : Submodule ℝ (DomainL2 Q)),
        DirichletForm.IsKilledDomain E (q : Set (SpatialCoordinates d)) V0 →
        ∀ (g : SpatialCoordinates d → ℝ), Measurable g →
        ∀ (B : Set (SpatialCoordinates d)), MeasurableSet B →
        B ⊆ (q : Set (SpatialCoordinates d)) → (∀ x, x ∉ B → g x = 0) →
        ∀ (S : ℝ), IsLUB (Set.range (fun x => |g x|)) S →
        BddAbove (Set.range (fun x => |g x|)) →
        (∀ v ∈ E.domain, ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
          Gammag.measure v A =
            ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(Gamma.measure v)) →
        (∀ (u ug : DomainL2 Q), u ∈ E.domain → ug ∈ Eg.domain → ug - u ∈ V0 →
          (∀ v ∈ E.domain, v - u ∈ V0 →
            (Gamma.measure u q).toReal ≤ (Gamma.measure v q).toReal) →
          (∀ v ∈ Eg.domain, v - u ∈ V0 →
            (Gammag.measure ug q).toReal ≤ (Gammag.measure v q).toReal) →
          (∀ v ∈ V0,
            DirichletForm.signedIntegralOn (Gammag.cross (ug - u) v)
                (q : Set (SpatialCoordinates d)) (fun _ => (1 : ℝ)) =
              -DirichletForm.signedIntegralOn (Gamma.cross u v) B
                (fun x => Real.exp (g x) - 1)) ∧
          (Gammag.measure ug q).toReal - (Gamma.measure u q).toReal =
            (∫ x in B, (Real.exp (g x) - 1) ∂(Gamma.measure u)) -
              (Gammag.measure (ug - u) q).toReal) ∧
        (∀ (f : DomainL2 Q) (u ug : DomainL2 Q), u ∈ V0 → ug ∈ V0 →
          (∀ v ∈ V0, DirichletForm.signedIntegralOn (Gamma.cross u v)
              (q : Set (SpatialCoordinates d)) (fun _ => (1 : ℝ)) = inner ℝ f v) →
          (∀ v ∈ V0, DirichletForm.signedIntegralOn (Gammag.cross ug v)
              (q : Set (SpatialCoordinates d)) (fun _ => (1 : ℝ)) = inner ℝ f v) →
          (∀ v ∈ V0,
            DirichletForm.signedIntegralOn (Gammag.cross (ug - u) v)
                (q : Set (SpatialCoordinates d)) (fun _ => (1 : ℝ)) =
              -DirichletForm.signedIntegralOn (Gamma.cross u v) B
                (fun x => Real.exp (g x) - 1)) ∧
          inner ℝ f ug - inner ℝ f u =
              (Gammag.measure (ug - u) q).toReal -
              (∫ x in B, (Real.exp (g x) - 1) ∂(Gamma.measure u))))) := by
  intro d Q z r hr q
  intro hQ E Eg Gamma Gammag hdom V0 hkill g hg B hB hBq hgzero S hS hBdd hweight
  have hq : MeasurableSet (q : Set (SpatialCoordinates d)) := by
    dsimp [q]
    exact (centeredCube z r hr).isOpen.measurableSet
  have hBq' : B ⊆ q := by simpa [q] using hBq
  have hV0E : V0 ≤ E.domain := hkill.le_domain
  have hV0Eg : V0 ≤ Eg.domain := by
    intro w hw
    rw [hdom]
    exact hV0E hw
  constructor
  · intro u ug hu hug hdiff hminE hminEg
    have hminEg' : ∀ v ∈ Eg.domain, v - ug ∈ V0 →
        (Gammag.measure ug q).toReal ≤ (Gammag.measure v q).toReal := by
      intro v hv hvg
      apply hminEg v hv
      have hvu : v - u = (v - ug) + (ug - u) := by abel
      rw [hvu]
      exact V0.add_mem hvg hdiff
    constructor
    · intro v hv
      have hE : ∀ w ∈ V0,
          DirichletForm.signedIntegralOn (Gamma.cross u w) q
              (fun _ => (1 : ℝ)) = (0 : ℝ) := by
        intro w hw
        rw [aux_cor_14_signedIntegralOn_one (Gamma.cross u w) q hq]
        exact aux_cor_14_minimizer_cross_zero Gamma V0 hV0E hu hq hminE w hw
      have hG : ∀ w ∈ V0,
          DirichletForm.signedIntegralOn (Gammag.cross ug w) q
              (fun _ => (1 : ℝ)) = (0 : ℝ) := by
        intro w hw
        rw [aux_cor_14_signedIntegralOn_one (Gammag.cross ug w) q hq]
        exact aux_cor_14_minimizer_cross_zero Gammag V0 hV0Eg hug hq hminEg' w hw
      exact (aux_cor_14_difference_equation Gamma Gammag hdom V0 hV0E hV0Eg
        g hg S hS hweight B q hB hq hBq' hgzero hu hug hdiff (fun _ => (0 : ℝ))
        hE hG) v hv
    · exact aux_cor_14_minimizer_identity Gamma Gammag hdom V0 hV0Eg g hg S hS
        hweight B q hB hq hBq' hgzero hu hug hdiff hminEg
  · intro f u ug hu hug hminE hminEg
    have huE : u ∈ E.domain := hV0E hu
    have hugEg : ug ∈ Eg.domain := hV0Eg hug
    have hdiff : ug - u ∈ V0 := V0.sub_mem hug hu
    constructor
    · intro v hv
      exact (aux_cor_14_difference_equation Gamma Gammag hdom V0 hV0E hV0Eg
        g hg S hS hweight B q hB hq hBq' hgzero
        (u := u) (ug := ug) huE hugEg hdiff (fun w => inner ℝ f w)
        hminE hminEg) v hv
    · exact aux_cor_14_load_identity Gamma Gammag hdom V0 g hg S hS hweight B q
        hB hq hBq' hgzero hu hug huE hugEg hminE hminEg

