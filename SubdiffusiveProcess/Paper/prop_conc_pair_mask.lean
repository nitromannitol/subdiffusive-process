module

public import SubdiffusiveProcess.Paper.prop_conc_pair_data
public import SubdiffusiveProcess.Paper.prop_conc_masked_response_pair
public import SubdiffusiveProcess.Paper.energy_order_of_form_order
public import SubdiffusiveProcess.Paper.relative_response_variation
public import SubdiffusiveProcess.Paper.prop_conc_masked_core_mass

@[expose] public section

/-! A bounded Borel weight `exp g` turns a pair of limiting forms into another pair of the same kind:
the weighted forms, their minimizers in the same affine trace class, and the same killed domain.
Weights compose, so the relative response of the masked pair for the weight `h` is the relative
response of the original pair for the weight `g + h`. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators
namespace SubdiffusiveProcess.Paper
noncomputable section

theorem aux_prop_conc_pair_mask_integral_order {Y : Type*} [MeasurableSpace Y] {μ ν : Measure Y}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ A : Set Y, MeasurableSet A → c * (μ A).toReal ≤ (ν A).toReal)
    (f : Y → ℝ) (hf : Measurable f) (f0 : ∀ x, 0 ≤ f x) (B : ℝ) (fb : ∀ x, f x ≤ B) :
    c * ∫ x, f x ∂μ ≤ ∫ x, f x ∂ν := by
  have hle : ENNReal.ofReal c • μ ≤ ν := by
    rw [Measure.le_iff]
    intro A hA
    rw [Measure.smul_apply, smul_eq_mul]
    have h1 := h A hA
    have hμ : μ A ≠ ⊤ := measure_ne_top μ A
    have hν : ν A ≠ ⊤ := measure_ne_top ν A
    calc ENNReal.ofReal c * μ A = ENNReal.ofReal (c * (μ A).toReal) := by
          rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_toReal hμ]
      _ ≤ ENNReal.ofReal ((ν A).toReal) := ENNReal.ofReal_le_ofReal h1
      _ = ν A := ENNReal.ofReal_toReal hν
  have hint : Integrable f ν :=
    (integrable_const B).mono' hf.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (f0 x)]; exact fb x)
  have := integral_mono_measure hle (ae_of_all _ f0) hint
  rwa [integral_smul_measure, ENNReal.toReal_ofReal hc, smul_eq_mul] at this

theorem aux_prop_conc_pair_mask_integral_order' {Y : Type*} [MeasurableSpace Y] {μ ν : Measure Y}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ A : Set Y, MeasurableSet A → (ν A).toReal ≤ c * (μ A).toReal)
    (f : Y → ℝ) (hf : Measurable f) (f0 : ∀ x, 0 ≤ f x) (B : ℝ) (fb : ∀ x, f x ≤ B) :
    ∫ x, f x ∂ν ≤ c * ∫ x, f x ∂μ := by
  have hle : ν ≤ ENNReal.ofReal c • μ := by
    rw [Measure.le_iff]
    intro A hA
    rw [Measure.smul_apply, smul_eq_mul]
    have h1 := h A hA
    have hμ : μ A ≠ ⊤ := measure_ne_top μ A
    have hν : ν A ≠ ⊤ := measure_ne_top ν A
    calc ν A = ENNReal.ofReal ((ν A).toReal) := (ENNReal.ofReal_toReal hν).symm
      _ ≤ ENNReal.ofReal (c * (μ A).toReal) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal c * μ A := by
          rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_toReal hμ]
  have : IsFiniteMeasure (ENNReal.ofReal c • μ) := Measure.smul_finite μ ENNReal.ofReal_ne_top
  have hint : Integrable f (ENNReal.ofReal c • μ) :=
    (integrable_const B).mono' hf.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (f0 x)]; exact fb x)
  have := integral_mono_measure hle (ae_of_all _ f0) hint
  rwa [integral_smul_measure, ENNReal.toReal_ofReal hc, smul_eq_mul] at this

section
variable {d : ℕ} {Q : Opens (SpatialCoordinates d)} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
  {C0 m M : ℝ}

theorem aux_prop_conc_pair_mask_mpos (X : prop_conc_pair_data Q z r hr C0 m M) : 0 < m :=
  (inv_pos.mpr (zero_lt_one.trans_le X.hC0)).trans_le X.hm

/-- The masked response-pair data of `X` for the weight `g` exist. -/
theorem aux_prop_conc_pair_mask_exists (X : prop_conc_pair_data Q z r hr C0 m M)
    (g : SpatialCoordinates d → ℝ) (hg : Measurable g) (K : ℝ) (hK : ∀ x, |g x| ≤ K) :
    Nonempty (aux_prop_conc_masked_response_pair_Data Q X.E X.F X.GammaE X.GammaF
      (centeredCube z r hr : Set (SpatialCoordinates d)) X.D X.P g K X.CE X.CF) :=
  prop_conc_masked_response_pair Q X.E X.F X.GammaE X.GammaF _ (centeredCube z r hr).isOpen X.D X.P
    X.hEc X.hFc X.hEl X.hFl m M (aux_prop_conc_pair_mask_mpos X)
    ((aux_prop_conc_pair_mask_mpos X).le.trans X.hmM) X.horder X.CE X.CF X.hCE X.hCF X.hcoE X.hcoF
    g hg K hK

variable {g : SpatialCoordinates d → ℝ} {K : ℝ}

/-- Form order of the weighted forms: the common weight preserves the order of the energy measures. -/
theorem aux_prop_conc_pair_mask_horder (X : prop_conc_pair_data Q z r hr C0 m M)
    (hg : Measurable g) (hK : ∀ x, |g x| ≤ K)
    (W : aux_prop_conc_masked_response_pair_Data Q X.E X.F X.GammaE X.GammaF
      (centeredCube z r hr : Set (SpatialCoordinates d)) X.D X.P g K X.CE X.CF) :
    ∀ v ∈ W.Edata.form.domain, m * W.Edata.form.form v v ≤ W.Fdata.form.form v v ∧
      W.Fdata.form.form v v ≤ M * W.Edata.form.form v v := by
  intro v hv
  have hvE : v ∈ X.E.domain := W.Edata.domain_eq ▸ hv
  have hvF : v ∈ X.F.domain := X.P.domain_eq ▸ hvE
  have hm := aux_prop_conc_pair_mask_mpos X
  have hM : 0 ≤ M := hm.le.trans X.hmM
  have hord := energy_order_of_form_order Q X.E X.F X.hEc X.hEl X.hFc X.hFl X.P.domain_eq
    X.GammaE X.GammaF m M hm X.horder v hvE
  have : IsFiniteMeasure (X.GammaE.measure v) := ⟨X.GammaE.measure_univ_lt_top v hvE⟩
  have : IsFiniteMeasure (X.GammaF.measure v) := ⟨X.GammaF.measure_univ_lt_top v hvF⟩
  have hexp0 : ∀ x, 0 ≤ Real.exp (g x) := fun x => (Real.exp_pos _).le
  have hexpK : ∀ x, Real.exp (g x) ≤ Real.exp K := fun x =>
    Real.exp_le_exp.mpr ((le_abs_self _).trans (hK x))
  rw [W.Edata.diagonal v hvE, W.Fdata.diagonal v hvF]
  exact ⟨aux_prop_conc_pair_mask_integral_order m hm.le (fun A hA => (hord A hA).1)
      (fun x => Real.exp (g x)) hg.exp hexp0 _ hexpK,
    aux_prop_conc_pair_mask_integral_order' M hM (fun A hA => (hord A hA).2)
      (fun x => Real.exp (g x)) hg.exp hexp0 _ hexpK⟩

/-- Positivity of the masked normalizer. -/
theorem aux_prop_conc_pair_mask_hDpos (X : prop_conc_pair_data Q z r hr C0 m M)
    (hg : Measurable g) (hK : ∀ x, |g x| ≤ K)
    (W : aux_prop_conc_masked_response_pair_Data Q X.E X.F X.GammaE X.GammaF
      (centeredCube z r hr : Set (SpatialCoordinates d)) X.D X.P g K X.CE X.CF) :
    0 < ∑ i : Fin d, W.QEg (Pi.single i 1) := by
  have hq : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  have hlow : ∀ p : Fin d → ℝ, Real.exp (-K) * X.P.QE p ≤ W.QEg p := by
    intro p
    have huE : (W.uEg p : DomainL2 Q) ∈ X.E.domain := W.Edata.domain_eq ▸ W.memEg p
    have hb := aux_lem_relvar_weighted_measure_bounds X.GammaE W.Edata.Gamma W.Edata.domain_eq g hg K
      hK W.Edata.weight huE hq
    have hmin := X.P.minE p (W.uEg p) huE (W.traceEg p)
    rw [W.responseEg p]
    calc Real.exp (-K) * X.P.QE p
        = Real.exp (-K) * (X.GammaE.measure (X.P.boundary p)
            (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by rw [X.P.responseE p]
      _ ≤ Real.exp (-K) * (X.GammaE.measure (W.uEg p)
            (centeredCube z r hr : Set (SpatialCoordinates d))).toReal :=
          mul_le_mul_of_nonneg_left hmin (Real.exp_pos _).le
      _ ≤ _ := hb.1
  calc (0 : ℝ) < Real.exp (-K) * ∑ i : Fin d, X.P.QE (Pi.single i 1) :=
        mul_pos (Real.exp_pos _) X.hDpos
    _ = ∑ i : Fin d, Real.exp (-K) * X.P.QE (Pi.single i 1) := Finset.mul_sum _ _ _
    _ ≤ _ := Finset.sum_le_sum fun i _ => hlow _

/-- The pair of weighted forms of `X` built from masked response-pair data `W`. -/
def aux_prop_conc_pair_mask_of (X : prop_conc_pair_data Q z r hr C0 m M)
    (hg : Measurable g) (hK : ∀ x, |g x| ≤ K)
    (W : aux_prop_conc_masked_response_pair_Data Q X.E X.F X.GammaE X.GammaF
      (centeredCube z r hr : Set (SpatialCoordinates d)) X.D X.P g K X.CE X.CF) :
    prop_conc_pair_data Q z r hr C0 m M where
  hd := X.hd
  hQ := X.hQ
  hinside := X.hinside
  E := W.Edata.form
  F := W.Fdata.form
  GammaE := W.Edata.Gamma
  GammaF := W.Fdata.Gamma
  D := X.D
  P :=
    { domain_eq := W.Edata.domain_eq.trans (X.P.domain_eq.trans W.Fdata.domain_eq.symm)
      killed := by
        have hcan : X.E.toClosedForm.killedCoreClosure (centeredCube z r hr : Set (SpatialCoordinates d)) = X.D :=
          (_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.isKilledDomain_killedCoreClosure _ _).eq_of_isKilledDomain X.P.killed
        have hcanE := (W.Edata.killed_eq (centeredCube z r hr : Set (SpatialCoordinates d))).trans hcan
        have h := _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.isKilledDomain_killedCoreClosure
          W.Edata.form.toClosedForm (centeredCube z r hr : Set (SpatialCoordinates d))
        rw [hcanE] at h
        exact h
      boundary := W.uEg.codRestrict W.Edata.form.domain W.memEg
      uF := fun p => (W.uFg p : DomainL2 Q)
      QE := W.QEg
      QF := W.QFg
      memF := W.memFg
      traceF := fun p => by
        change W.uFg p - W.uEg p ∈ X.D
        have h := X.D.sub_mem (W.traceFg p) (W.traceEg p)
        rw [sub_sub_sub_cancel_right] at h
        exact h
      minE := fun p v hv hvD => by
        refine W.minEg p v hv ?_
        have h := X.D.add_mem hvD (W.traceEg p)
        simpa only [LinearMap.codRestrict_apply, sub_add_sub_cancel] using h
      minF := fun p v hv hvD => by
        refine W.minFg p v hv ?_
        have h := X.D.add_mem hvD (W.traceEg p)
        simpa only [LinearMap.codRestrict_apply, sub_add_sub_cancel] using h
      responseE := W.responseEg
      responseF := fun p => W.responseFg p }
  hEc := W.Edata.core
  hFc := W.Fdata.core
  hEl := W.Edata.locality
  hFl := W.Fdata.locality
  hC0 := X.hC0
  hm := X.hm
  hmM := X.hmM
  hM := X.hM
  horder := aux_prop_conc_pair_mask_horder X hg hK W
  CE := Real.exp K * X.CE
  CF := Real.exp K * X.CF
  hCE := mul_pos (Real.exp_pos _) X.hCE
  hCF := mul_pos (Real.exp_pos _) X.hCF
  hcoE := W.Edata.coercive
  hcoF := W.Fdata.coercive
  hDpos := aux_prop_conc_pair_mask_hDpos X hg hK W

/-- The canonical masked pair of `X` for a bounded Borel weight `g`. -/
def aux_prop_conc_pair_mask_pair (X : prop_conc_pair_data Q z r hr C0 m M)
    (g : SpatialCoordinates d → ℝ) (hg : Measurable g) (K : ℝ) (hK : ∀ x, |g x| ≤ K) :
    prop_conc_pair_data Q z r hr C0 m M :=
  aux_prop_conc_pair_mask_of X hg hK (Classical.choice (aux_prop_conc_pair_mask_exists X g hg K hK))

end


section values
variable {d : ℕ} {Q : Opens (SpatialCoordinates d)} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
  {C0 m M : ℝ}

theorem aux_prop_conc_pair_mask_wenergy_zero {E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d)))}
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E) (q : Set (SpatialCoordinates d)) (v : DomainL2 Q) :
    aux_prop_conc_pair_data_wenergy Gamma q (fun _ => 0) v = (Gamma.measure v q).toReal := by
  simp only [aux_prop_conc_pair_data_wenergy, Real.exp_zero, ENNReal.ofReal_one, lintegral_const,
    one_mul, Measure.restrict_apply_univ]

/-- With the trivial weight the infimum is the minimal response of the pair. -/
theorem aux_prop_conc_pair_mask_wInfE_zero (X : prop_conc_pair_data Q z r hr C0 m M)
    (p : Fin d → ℝ) : aux_prop_conc_pair_data_wInfE X (fun _ => 0) p = X.P.QE p := by
  unfold aux_prop_conc_pair_data_wInfE
  refine IsLeast.csInf_eq ⟨⟨(X.P.boundary p : DomainL2 Q), (X.P.boundary p).property, by
      simpa only [sub_self] using X.D.zero_mem, ?_⟩, ?_⟩
  · rw [aux_prop_conc_pair_mask_wenergy_zero, X.P.responseE p]
  · rintro e ⟨v, hv, hvD, rfl⟩
    rw [aux_prop_conc_pair_mask_wenergy_zero, X.P.responseE p]
    exact X.P.minE p v hv hvD

theorem aux_prop_conc_pair_mask_wInfF_zero (X : prop_conc_pair_data Q z r hr C0 m M)
    (p : Fin d → ℝ) : aux_prop_conc_pair_data_wInfF X (fun _ => 0) p = X.P.QF p := by
  unfold aux_prop_conc_pair_data_wInfF
  refine IsLeast.csInf_eq ⟨⟨(X.P.uF p : DomainL2 Q), X.P.memF p, X.P.traceF p, ?_⟩, ?_⟩
  · rw [aux_prop_conc_pair_mask_wenergy_zero, X.P.responseF p]
  · rintro e ⟨v, hv, hvD, rfl⟩
    rw [aux_prop_conc_pair_mask_wenergy_zero, X.P.responseF p]
    exact X.P.minF p v hv hvD

/-- The relative response for the trivial weight is the relative response of the pair. -/
theorem aux_prop_conc_pair_mask_theta_zero (X : prop_conc_pair_data Q z r hr C0 m M)
    (c : ℝ) (p : Fin d → ℝ) :
    aux_prop_conc_pair_data_theta X c p (fun _ => 0) =
      (X.P.QF p - c * X.P.QE p) / ∑ i : Fin d, X.P.QE (Pi.single i 1) := by
  unfold aux_prop_conc_pair_data_theta
  simp only [aux_prop_conc_pair_mask_wInfE_zero, aux_prop_conc_pair_mask_wInfF_zero]

variable {g : SpatialCoordinates d → ℝ} {K : ℝ}

/-- The infimum for the weight `g` is the response of any masked response-pair data. -/
theorem aux_prop_conc_pair_mask_wInfE_data (X : prop_conc_pair_data Q z r hr C0 m M)
    (W : aux_prop_conc_masked_response_pair_Data Q X.E X.F X.GammaE X.GammaF
      (centeredCube z r hr : Set (SpatialCoordinates d)) X.D X.P g K X.CE X.CF)
    (p : Fin d → ℝ) : aux_prop_conc_pair_data_wInfE X g p = W.QEg p := by
  have hq : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  unfold aux_prop_conc_pair_data_wInfE
  have hw : ∀ v ∈ X.E.domain, aux_prop_conc_pair_data_wenergy X.GammaE
      (centeredCube z r hr : Set (SpatialCoordinates d)) g v =
        (W.Edata.Gamma.measure v (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
    intro v hv
    unfold aux_prop_conc_pair_data_wenergy
    rw [W.Edata.weight v hv _ hq]
  refine IsLeast.csInf_eq ⟨⟨(W.uEg p : DomainL2 Q), W.Edata.domain_eq ▸ W.memEg p, W.traceEg p, ?_⟩, ?_⟩
  · rw [hw _ (W.Edata.domain_eq ▸ W.memEg p), W.responseEg p]
  · rintro e ⟨v, hv, hvD, rfl⟩
    rw [hw v hv, W.responseEg p]
    exact W.minEg p v (W.Edata.domain_eq ▸ hv) hvD

theorem aux_prop_conc_pair_mask_wInfF_data (X : prop_conc_pair_data Q z r hr C0 m M)
    (W : aux_prop_conc_masked_response_pair_Data Q X.E X.F X.GammaE X.GammaF
      (centeredCube z r hr : Set (SpatialCoordinates d)) X.D X.P g K X.CE X.CF)
    (p : Fin d → ℝ) : aux_prop_conc_pair_data_wInfF X g p = W.QFg p := by
  have hq : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  unfold aux_prop_conc_pair_data_wInfF
  have hw : ∀ v ∈ X.F.domain, aux_prop_conc_pair_data_wenergy X.GammaF
      (centeredCube z r hr : Set (SpatialCoordinates d)) g v =
        (W.Fdata.Gamma.measure v (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
    intro v hv
    unfold aux_prop_conc_pair_data_wenergy
    rw [W.Fdata.weight v hv _ hq]
  refine IsLeast.csInf_eq ⟨⟨(W.uFg p : DomainL2 Q), W.Fdata.domain_eq ▸ W.memFg p, W.traceFg p, ?_⟩, ?_⟩
  · rw [hw _ (W.Fdata.domain_eq ▸ W.memFg p), W.responseFg p]
  · rintro e ⟨v, hv, hvD, rfl⟩
    rw [hw v hv, W.responseFg p]
    exact W.minFg p v (W.Fdata.domain_eq ▸ hv) hvD

/-- The relative response for the weight `g` is that of any masked response-pair data. -/
theorem aux_prop_conc_pair_mask_theta_data (X : prop_conc_pair_data Q z r hr C0 m M)
    (W : aux_prop_conc_masked_response_pair_Data Q X.E X.F X.GammaE X.GammaF
      (centeredCube z r hr : Set (SpatialCoordinates d)) X.D X.P g K X.CE X.CF)
    (c : ℝ) (p : Fin d → ℝ) :
    aux_prop_conc_pair_data_theta X c p g =
      (W.QFg p - c * W.QEg p) / ∑ i : Fin d, W.QEg (Pi.single i 1) := by
  unfold aux_prop_conc_pair_data_theta
  simp only [aux_prop_conc_pair_mask_wInfE_data X W, aux_prop_conc_pair_mask_wInfF_data X W]

/-- The normalized measure `ν` as the normalized sum of real masses. -/
theorem aux_prop_conc_pair_mask_nu_toReal (X : prop_conc_pair_data Q z r hr C0 m M)
    (slopes : Finset (Fin d → ℝ)) (A : Set (SpatialCoordinates d)) :
    (aux_prop_conc_pair_data_nu X slopes A).toReal =
      (∑ i : Fin d, X.P.QE (Pi.single i 1))⁻¹ * ∑ p ∈ slopes,
        ((X.GammaE.measure (X.P.boundary p) A).toReal + (X.GammaE.measure (X.P.uF p) A).toReal) :=
  aux_prop_conc_masked_core_mass_normalized_pair_mass X.GammaE
    (fun p => (X.P.boundary p : DomainL2 Q)) (fun p => (X.P.uF p : DomainL2 Q))
    (fun p => (X.P.boundary p).property)
    (fun p => X.P.domain_eq ▸ X.P.memF p) slopes _ X.hDpos A


/-- `ν` in the form used by the relative-variation context. -/
theorem aux_prop_conc_pair_mask_nu_toReal' (X : prop_conc_pair_data Q z r hr C0 m M)
    (slopes : Finset (Fin d → ℝ)) (A : Set (SpatialCoordinates d)) :
    (aux_prop_conc_pair_data_nu X slopes A).toReal =
      (∑ i : Fin d, X.P.QE (Pi.single i 1))⁻¹ * ∑ p ∈ slopes,
        ((X.GammaE.measure (X.P.boundary p) + X.GammaE.measure (X.P.uF p)) A).toReal := by
  unfold aux_prop_conc_pair_data_nu
  exact aux_relative_response_variation_normalized_sum_toReal _ X.hDpos slopes
    (fun p => X.GammaE.measure (X.P.boundary p) + X.GammaE.measure (X.P.uF p)) A
    (fun p _ => by
      rw [Measure.add_apply]
      exact (ENNReal.add_lt_top.mpr ⟨(X.GammaE.measure_ne_top (X.P.boundary p).property A).lt_top,
        (X.GammaE.measure_ne_top (X.P.domain_eq ▸ X.P.memF p) A).lt_top⟩).ne)

/-- The normalized difference measure `ζ` as a normalized sum of real masses. -/
theorem aux_prop_conc_pair_mask_zeta_toReal (X : prop_conc_pair_data Q z r hr C0 m M)
    (slopes : Finset (Fin d → ℝ)) (A : Set (SpatialCoordinates d)) :
    (aux_prop_conc_pair_data_zeta X slopes A).toReal =
      (∑ i : Fin d, X.P.QE (Pi.single i 1))⁻¹ * ∑ p ∈ slopes,
        (X.GammaE.measure ((X.P.uF p : DomainL2 Q) - (X.P.boundary p : DomainL2 Q)) A).toReal := by
  unfold aux_prop_conc_pair_data_zeta
  exact aux_relative_response_variation_normalized_sum_toReal _ X.hDpos slopes
    (fun p => X.GammaE.measure ((X.P.uF p : DomainL2 Q) - (X.P.boundary p : DomainL2 Q))) A
    (fun p _ => X.GammaE.measure_ne_top (X.E.domain.sub_mem (X.P.domain_eq ▸ X.P.memF p)
      (X.P.boundary p).property) A)

end values

/-- Composition of weights, energy version: the `exp h`-weighted energy of the masked pair on `q`
is the `exp (g + h)`-weighted energy of the original pair. -/
theorem aux_prop_conc_pair_mask_wenergy {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    {E Eg : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d)))}
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E) (Gammag : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Eg)
    (q : Set (SpatialCoordinates d))
    (hq : MeasurableSet q) (g h : SpatialCoordinates d → ℝ) (hg : Measurable g) (hh : Measurable h)
    (v : DomainL2 Q)
    (hweight : ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
      Gammag.measure v A = ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(Gamma.measure v)) :
    aux_prop_conc_pair_data_wenergy Gammag q h v =
      aux_prop_conc_pair_data_wenergy Gamma q (g + h) v := by
  have hmeas : Gammag.measure v = (Gamma.measure v).withDensity
      (fun x => ENNReal.ofReal (Real.exp (g x))) :=
    Measure.ext fun A hA => by rw [hweight A hA, withDensity_apply _ hA]
  have hf : Measurable (fun x => ENNReal.ofReal (Real.exp (g x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hg)
  have hk : Measurable (fun x => ENNReal.ofReal (Real.exp (h x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hh)
  unfold aux_prop_conc_pair_data_wenergy
  congr 1
  rw [hmeas, restrict_withDensity hq, lintegral_withDensity_eq_lintegral_mul _ hf hk]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, Pi.add_apply]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]

/-- Masking by a bounded Borel weight `exp g` produces a pair of the same kind with the same killed
domain and affine trace class, weighted energy measures, and the composition law of weights:
the relative response of the masked pair for the weight `h` is that of `X` for `g + h`. -/
theorem prop_conc_pair_mask {d : ℕ} {Q : Opens (SpatialCoordinates d)} {z : SpatialCoordinates d}
    {r : ℝ} {hr : 0 < r} {C0 m M : ℝ} (X : prop_conc_pair_data Q z r hr C0 m M)
    (g : SpatialCoordinates d → ℝ) (hg : Measurable g) (K : ℝ) (hK : ∀ x, |g x| ≤ K) :
    ∃ Y : prop_conc_pair_data Q z r hr C0 m M,
      Y.D = X.D ∧ Y.E.domain = X.E.domain ∧ Y.F.domain = X.F.domain ∧
      (∀ u ∈ X.E.domain, ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
        Y.GammaE.measure u A = ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(X.GammaE.measure u)) ∧
      (∀ u ∈ X.F.domain, ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
        Y.GammaF.measure u A = ∫⁻ x in A, ENNReal.ofReal (Real.exp (g x)) ∂(X.GammaF.measure u)) ∧
      (∀ p, (Y.P.boundary p : DomainL2 Q) - (X.P.boundary p : DomainL2 Q) ∈ X.D) ∧
      ∀ (c : ℝ) (p : Fin d → ℝ) (h : SpatialCoordinates d → ℝ), Measurable h →
        aux_prop_conc_pair_data_theta Y c p h = aux_prop_conc_pair_data_theta X c p (g + h) := by
  let W := Classical.choice (aux_prop_conc_pair_mask_exists X g hg K hK)
  have hq : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  have hdE : (aux_prop_conc_pair_mask_of X hg hK W).E.domain = X.E.domain := W.Edata.domain_eq
  have hdF : (aux_prop_conc_pair_mask_of X hg hK W).F.domain = X.F.domain := W.Fdata.domain_eq
  have hcls : ∀ (p : Fin d → ℝ) (v : DomainL2 Q),
      v - ((aux_prop_conc_pair_mask_of X hg hK W).P.boundary p : DomainL2 Q) ∈ X.D ↔
        v - (X.P.boundary p : DomainL2 Q) ∈ X.D := by
    intro p v
    have hd : (((aux_prop_conc_pair_mask_of X hg hK W).P.boundary p : DomainL2 Q) -
        (X.P.boundary p : DomainL2 Q)) ∈ X.D := W.traceEg p
    constructor
    · intro h
      have := X.D.add_mem h hd
      simpa only [sub_add_sub_cancel] using this
    · intro h
      have := X.D.sub_mem h hd
      simpa only [sub_sub_sub_cancel_right] using this
  refine ⟨aux_prop_conc_pair_mask_of X hg hK W, rfl, hdE, hdF, W.Edata.weight, W.Fdata.weight,
    fun p => W.traceEg p, ?_⟩
  intro c p h hh
  have hE : ∀ p', aux_prop_conc_pair_data_wInfE (aux_prop_conc_pair_mask_of X hg hK W) h p' =
      aux_prop_conc_pair_data_wInfE X (g + h) p' := by
    intro p'
    unfold aux_prop_conc_pair_data_wInfE
    congr 1
    ext e
    constructor
    · rintro ⟨v, hv, hvD, rfl⟩
      have hvX : v ∈ X.E.domain := hdE ▸ hv
      refine ⟨v, hvX, (hcls p' v).1 hvD, ?_⟩
      exact aux_prop_conc_pair_mask_wenergy X.GammaE W.Edata.Gamma _ hq g h hg hh v
        (W.Edata.weight v hvX)
    · rintro ⟨v, hvX, hvD, rfl⟩
      refine ⟨v, hdE ▸ hvX, (hcls p' v).2 hvD, ?_⟩
      exact (aux_prop_conc_pair_mask_wenergy X.GammaE W.Edata.Gamma _ hq g h hg hh v
        (W.Edata.weight v hvX)).symm
  have hF : ∀ p', aux_prop_conc_pair_data_wInfF (aux_prop_conc_pair_mask_of X hg hK W) h p' =
      aux_prop_conc_pair_data_wInfF X (g + h) p' := by
    intro p'
    unfold aux_prop_conc_pair_data_wInfF
    congr 1
    ext e
    constructor
    · rintro ⟨v, hv, hvD, rfl⟩
      have hvX : v ∈ X.F.domain := hdF ▸ hv
      refine ⟨v, hvX, (hcls p' v).1 hvD, ?_⟩
      exact aux_prop_conc_pair_mask_wenergy X.GammaF W.Fdata.Gamma _ hq g h hg hh v
        (W.Fdata.weight v hvX)
    · rintro ⟨v, hvX, hvD, rfl⟩
      refine ⟨v, hdF ▸ hvX, (hcls p' v).2 hvD, ?_⟩
      exact (aux_prop_conc_pair_mask_wenergy X.GammaF W.Fdata.Gamma _ hq g h hg hh v
        (W.Fdata.weight v hvX)).symm
  unfold aux_prop_conc_pair_data_theta
  simp only [hE, hF]

end
end SubdiffusiveProcess.Paper
