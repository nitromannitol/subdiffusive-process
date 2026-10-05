module

public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.EllipticRegularity.Carriers

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.DirichletForm
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

lemma aux_lem_borel_weights_closed_core_integrable
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) : Integrable f μ := by
  refine (integrable_const C).mono' hf.aestronglyMeasurable ?_
  filter_upwards with x
  simpa [Real.norm_eq_abs] using hC x

lemma aux_lem_borel_weights_closed_core_signed_representation
    {X : Type*} [MeasurableSpace X] (ν : SignedMeasure X)
    {μ η : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure η]
    {f : X → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C)
    (hν : ν = μ.toSignedMeasure - η.toSignedMeasure) :
    signedIntegralOn ν Set.univ f =
      (∫ x, f x ∂μ) - ∫ x, f x ∂η := by
  let j := ν.toJordanDecomposition
  have hcanonical : ν = j.posPart.toSignedMeasure - j.negPart.toSignedMeasure := by
    have h := (SignedMeasure.toSignedMeasure_toJordanDecomposition ν).symm
    simpa [j, JordanDecomposition.toSignedMeasure] using h
  have hdiff : μ.toSignedMeasure - η.toSignedMeasure =
      j.posPart.toSignedMeasure - j.negPart.toSignedMeasure :=
    hν.symm.trans hcanonical
  have hadd : μ.toSignedMeasure + j.negPart.toSignedMeasure =
      j.posPart.toSignedMeasure + η.toSignedMeasure := by
    exact sub_eq_sub_iff_add_eq_add.mp hdiff
  have hmeasure : μ + j.negPart = j.posPart + η := by
    apply (Measure.toSignedMeasure_eq_toSignedMeasure_iff).mp
    rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
    exact hadd
  have hμ : Integrable f μ :=
    aux_lem_borel_weights_closed_core_integrable hf hC
  have hη : Integrable f η :=
    aux_lem_borel_weights_closed_core_integrable hf hC
  have hjp : Integrable f j.posPart :=
    aux_lem_borel_weights_closed_core_integrable hf hC
  have hjn : Integrable f j.negPart :=
    aux_lem_borel_weights_closed_core_integrable hf hC
  have hi := congrArg (fun κ : Measure X => ∫ x, f x ∂κ) hmeasure
  rw [integral_add_measure hμ hjn, integral_add_measure hjp hη] at hi
  simp only [signedIntegralOn, Measure.restrict_univ]
  linarith

lemma aux_lem_borel_weights_closed_core_signed_add
    {X : Type*} [MeasurableSpace X] (ν₁ ν₂ : SignedMeasure X)
    {f : X → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) :
    signedIntegralOn (ν₁ + ν₂) Set.univ f =
      signedIntegralOn ν₁ Set.univ f + signedIntegralOn ν₂ Set.univ f := by
  let j₁ := ν₁.toJordanDecomposition
  let j₂ := ν₂.toJordanDecomposition
  have h₁ : ν₁ = j₁.posPart.toSignedMeasure - j₁.negPart.toSignedMeasure := by
    have h := (SignedMeasure.toSignedMeasure_toJordanDecomposition ν₁).symm
    simpa [j₁, JordanDecomposition.toSignedMeasure] using h
  have h₂ : ν₂ = j₂.posPart.toSignedMeasure - j₂.negPart.toSignedMeasure := by
    have h := (SignedMeasure.toSignedMeasure_toJordanDecomposition ν₂).symm
    simpa [j₂, JordanDecomposition.toSignedMeasure] using h
  have hrep : ν₁ + ν₂ =
      (j₁.posPart + j₂.posPart).toSignedMeasure -
        (j₁.negPart + j₂.negPart).toSignedMeasure := by
    rw [h₁, h₂, Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
    abel
  have hmain := aux_lem_borel_weights_closed_core_signed_representation
    (ν := ν₁ + ν₂) hf hC hrep
  have hleft := aux_lem_borel_weights_closed_core_signed_representation
    ν₁ hf hC (by simpa [j₁, JordanDecomposition.toSignedMeasure] using
      (SignedMeasure.toSignedMeasure_toJordanDecomposition ν₁).symm)
  have hright := aux_lem_borel_weights_closed_core_signed_representation
    ν₂ hf hC (by simpa [j₂, JordanDecomposition.toSignedMeasure] using
      (SignedMeasure.toSignedMeasure_toJordanDecomposition ν₂).symm)
  have hp₁ : Integrable f j₁.posPart :=
    aux_lem_borel_weights_closed_core_integrable hf hC
  have hp₂ : Integrable f j₂.posPart :=
    aux_lem_borel_weights_closed_core_integrable hf hC
  have hn₁ : Integrable f j₁.negPart :=
    aux_lem_borel_weights_closed_core_integrable hf hC
  have hn₂ : Integrable f j₂.negPart :=
    aux_lem_borel_weights_closed_core_integrable hf hC
  rw [hmain, hleft, hright, integral_add_measure hp₁ hp₂,
    integral_add_measure hn₁ hn₂]
  ring

lemma aux_lem_borel_weights_closed_core_signed_smul
    {X : Type*} [MeasurableSpace X] (ν : SignedMeasure X) (r : ℝ)
    {f : X → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) :
    signedIntegralOn (r • ν) Set.univ f =
      r * signedIntegralOn ν Set.univ f := by
  by_cases hr : 0 ≤ r
  · let j := ν.toJordanDecomposition
    have hpos := JordanDecomposition.real_smul_posPart_nonneg j r hr
    have hneg := JordanDecomposition.real_smul_negPart_nonneg j r hr
    have hi₁ : Integrable f j.posPart :=
      aux_lem_borel_weights_closed_core_integrable hf hC
    have hi₂ : Integrable f j.negPart :=
      aux_lem_borel_weights_closed_core_integrable hf hC
    simp only [signedIntegralOn, Measure.restrict_univ,
      SignedMeasure.toJordanDecomposition_smul_real]
    change (∫ x, f x ∂(r • j).posPart) - (∫ x, f x ∂(r • j).negPart) =
      r * ((∫ x, f x ∂j.posPart) - ∫ x, f x ∂j.negPart)
    rw [hpos, hneg, integral_smul_nnreal_measure, integral_smul_nnreal_measure]
    simp only [NNReal.smul_def, Real.toNNReal_of_nonneg hr, NNReal.coe_mk,
      smul_eq_mul]
    ring
  · have hr' : r < 0 := lt_of_not_ge hr
    let j := ν.toJordanDecomposition
    have hpos := JordanDecomposition.real_smul_posPart_neg j r hr'
    have hneg := JordanDecomposition.real_smul_negPart_neg j r hr'
    have hi₁ : Integrable f j.posPart :=
      aux_lem_borel_weights_closed_core_integrable hf hC
    have hi₂ : Integrable f j.negPart :=
      aux_lem_borel_weights_closed_core_integrable hf hC
    simp only [signedIntegralOn, Measure.restrict_univ,
      SignedMeasure.toJordanDecomposition_smul_real]
    change (∫ x, f x ∂(r • j).posPart) - (∫ x, f x ∂(r • j).negPart) =
      r * ((∫ x, f x ∂j.posPart) - ∫ x, f x ∂j.negPart)
    rw [hpos, hneg, integral_smul_nnreal_measure, integral_smul_nnreal_measure]
    simp only [NNReal.smul_def,
      Real.toNNReal_of_nonneg (neg_nonneg.mpr (le_of_lt hr')), NNReal.coe_mk,
      smul_eq_mul]
    ring

lemma aux_lem_borel_weights_closed_core_signed_to_measure
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) :
    signedIntegralOn μ.toSignedMeasure Set.univ f = ∫ x, f x ∂μ := by
  have h := aux_lem_borel_weights_closed_core_signed_representation
    (ν := μ.toSignedMeasure) (μ := μ) (η := 0) hf hC
      (by
        simp)
  simpa using h



theorem lem_borel_weights_closed_core
    (E : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (g : SpatialCoordinates d → ℝ) (hg : Measurable g)
    (M : ℝ) (hgbdd : ∀ x : SpatialCoordinates d, |g x| ≤ M)
    (hreg : _root_.SubdiffusiveProcess.DirichletForm.IsRegular E.toClosedForm)
    : ∃ F : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
        (volume.restrict (Q : Set (SpatialCoordinates d))),
        _root_.SubdiffusiveProcess.DirichletForm.IsWeightedForm E.toClosedForm F Gamma
          (fun x => Real.exp (g x)) ∧
        (∀ u ∈ E.toClosedForm.domain,
          Real.exp (-M) * E.toClosedForm.form u u ≤ F.form u u ∧
          F.form u u ≤ Real.exp M * E.toClosedForm.form u u) ∧
        (∀ (U : Set (SpatialCoordinates d))
            (C : Set (Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))),
          _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm U C ↔
            _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F U C) ∧
        _root_.SubdiffusiveProcess.DirichletForm.IsRegular F := by
  let w : SpatialCoordinates d → ℝ := fun x => Real.exp (g x)
  have hw : Measurable w := by
    simpa [w] using hg.exp
  have hwlower : ∀ x, Real.exp (-M) ≤ w x := by
    intro x
    dsimp [w]
    exact Real.exp_le_exp.mpr (abs_le.mp (hgbdd x)).1
  have hwupper : ∀ x, w x ≤ Real.exp M := by
    intro x
    dsimp [w]
    exact Real.exp_le_exp.mpr (abs_le.mp (hgbdd x)).2
  have hwabs : ∀ x, |w x| ≤ Real.exp M := by
    intro x
    rw [abs_of_pos (Real.exp_pos _)]
    exact hwupper x
  have hwi : ∀ u ∈ E.toClosedForm.domain,
      Integrable w (Gamma.measure u) := by
    intro u hu
    let : IsFiniteMeasure (Gamma.measure u) :=
      ⟨Gamma.measure_univ_lt_top u hu⟩
    exact aux_lem_borel_weights_closed_core_integrable hw hwabs
  let formW : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))) →
      Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))) → ℝ :=
    fun u v => signedIntegralOn (Gamma.cross u v) Set.univ w
  have hdiag : ∀ u ∈ E.toClosedForm.domain,
      formW u u = ∫ x, w x ∂(Gamma.measure u) := by
    intro u hu
    let : IsFiniteMeasure (Gamma.measure u) :=
      ⟨Gamma.measure_univ_lt_top u hu⟩
    have hcross : Gamma.cross u u = (Gamma.measure u).toSignedMeasure := by
      ext B hB
      rw [Gamma.cross_self u hu B hB,
        Measure.toSignedMeasure_apply_measurable hB]
      rfl
    dsimp [formW]
    rw [hcross]
    exact aux_lem_borel_weights_closed_core_signed_to_measure
      (Gamma.measure u) hw hwabs
  have hform_nonneg : ∀ u ∈ E.toClosedForm.domain, 0 ≤ formW u u := by
    intro u hu
    rw [hdiag u hu]
    exact integral_nonneg (fun x => le_of_lt (Real.exp_pos (g x)))
  have hlower : ∀ u ∈ E.toClosedForm.domain,
      Real.exp (-M) * E.toClosedForm.form u u ≤ formW u u := by
    intro u hu
    let : IsFiniteMeasure (Gamma.measure u) :=
      ⟨Gamma.measure_univ_lt_top u hu⟩
    calc
      Real.exp (-M) * E.toClosedForm.form u u =
          ∫ _x, Real.exp (-M) ∂(Gamma.measure u) := by
            rw [← Gamma.measure_univ u hu]
            simp [integral_const, measureReal_def, mul_comm]
      _ ≤ ∫ x, w x ∂(Gamma.measure u) :=
        integral_mono (integrable_const _) (hwi u hu) hwlower
      _ = formW u u := (hdiag u hu).symm
  have hupper : ∀ u ∈ E.toClosedForm.domain,
      formW u u ≤ Real.exp M * E.toClosedForm.form u u := by
    intro u hu
    let : IsFiniteMeasure (Gamma.measure u) :=
      ⟨Gamma.measure_univ_lt_top u hu⟩
    calc
      formW u u = ∫ x, w x ∂(Gamma.measure u) := hdiag u hu
      _ ≤ ∫ _x, Real.exp M ∂(Gamma.measure u) :=
        integral_mono (hwi u hu) (integrable_const _) hwupper
      _ = Real.exp M * E.toClosedForm.form u u := by
        rw [← Gamma.measure_univ u hu]
        simp [integral_const, measureReal_def, mul_comm]
  let F : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (Q : Set (SpatialCoordinates d))) :=
    { domain := E.toClosedForm.domain
      form := formW
      denseDomain := E.toClosedForm.denseDomain
      form_symm := by
        intro u hu v hv
        dsimp [formW]
        rw [Gamma.cross_symm u hu v hv]
      form_add_left := by
        intro u hu v hv z hz
        dsimp [formW]
        rw [Gamma.cross_add_left hu hv hz,
          aux_lem_borel_weights_closed_core_signed_add _ _ hw hwabs]
      form_smul_left := by
        intro c u hu v hv
        dsimp [formW]
        rw [Gamma.cross_smul_left c hu hv,
          aux_lem_borel_weights_closed_core_signed_smul _ _ hw hwabs]
      form_nonneg := by
        intro u hu
        exact hform_nonneg u hu
      complete := by
        intro u hu hCauchy
        have huE : ∀ n, u n ∈ E.toClosedForm.domain := hu
        have hCauchyE : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
            E.toClosedForm.form (u p - u q) (u p - u q) +
              ‖u p - u q‖ ^ 2 < ε := by
          intro ε hε
          let a := Real.exp (-M)
          have ha : 0 < a := Real.exp_pos _
          let δ := min (a * ε / 2) (ε / 2)
          have hδ : 0 < δ := by
            dsimp [δ]
            exact lt_min (by positivity) (by positivity)
          obtain ⟨N, hN⟩ := hCauchy δ hδ
          refine ⟨N, ?_⟩
          intro p hp q hq
          have hd : u p - u q ∈ E.toClosedForm.domain :=
            E.toClosedForm.domain.sub_mem (huE p) (huE q)
          have hlow := hlower (u p - u q) hd
          have hnon := hform_nonneg (u p - u q) hd
          have hnorm : 0 ≤ ‖u p - u q‖ ^ 2 := sq_nonneg _
          have hδ₁ : δ ≤ a * ε / 2 := min_le_left _ _
          have hδ₂ : δ ≤ ε / 2 := min_le_right _ _
          have hcf := hN p hp q hq
          dsimp [a] at ha hlow hδ₁ hcf ⊢
          nlinarith
        obtain ⟨z, hz, hzlim⟩ := E.toClosedForm.complete u huE hCauchyE
        refine ⟨z, hz, ?_⟩
        have hzE : z ∈ E.toClosedForm.domain := hz
        have hlim : Tendsto
            (fun n => E.toClosedForm.energyNormSq (u n - z)) atTop (𝓝 0) := hzlim
        let A := Real.exp M
        let K := max A 1
        have hA : 0 < A := by dsimp [A]; exact Real.exp_pos _
        have hK1 : (1 : ℝ) ≤ K := by dsimp [K]; exact le_max_right _ _
        have hKA : A ≤ K := by dsimp [K]; exact le_max_left _ _
        have hupperSeq : ∀ n,
            formW (u n - z) (u n - z) + ‖u n - z‖ ^ 2 ≤
              K * E.toClosedForm.energyNormSq (u n - z) := by
          intro n
          have hd : u n - z ∈ E.toClosedForm.domain :=
            E.toClosedForm.domain.sub_mem (huE n) hzE
          have hup := hupper (u n - z) hd
          have hen := E.toClosedForm.form_nonneg (u n - z) hd
          have hnorm : 0 ≤ ‖u n - z‖ ^ 2 := sq_nonneg _
          dsimp [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq]
          nlinarith
        have hKlim : Tendsto
            (fun n => K * E.toClosedForm.energyNormSq (u n - z)) atTop (𝓝 0) := by
          simpa using (tendsto_const_nhds.mul hlim)
        apply tendsto_of_tendsto_of_tendsto_of_le_of_le
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) hKlim
        · exact fun n =>
            add_nonneg (hform_nonneg (u n - z)
              (E.toClosedForm.domain.sub_mem (huE n) hzE)) (sq_nonneg _)
        · exact hupperSeq }
  have hcore : ∀ (U : Set (SpatialCoordinates d))
      (C : Set (Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))),
      _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm U C ↔
        _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F U C := by
    intro U C
    let A := Real.exp M
    let K := max A 1
    have hA : 0 < A := by dsimp [A]; exact Real.exp_pos _
    have hK : 0 < K := lt_of_lt_of_le zero_lt_one (by
      dsimp [K]
      exact le_max_right _ _)
    have hKupper : ∀ u v, u ∈ E.toClosedForm.domain → v ∈ E.toClosedForm.domain →
        F.energyNormSq (u - v) ≤ K * E.toClosedForm.energyNormSq (u - v) := by
      intro u v hu hv
      have hup := hupper (u - v) (E.toClosedForm.domain.sub_mem hu hv)
      have hen := E.toClosedForm.form_nonneg (u - v)
        (E.toClosedForm.domain.sub_mem hu hv)
      have hnorm : 0 ≤ ‖u - v‖ ^ 2 := sq_nonneg _
      have hKA : Real.exp M ≤ K := by
        dsimp [K]
        exact le_max_left _ _
      have hK1 : (1 : ℝ) ≤ K := by
        dsimp [K]
        exact le_max_right _ _
      dsimp [F, _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq]
      nlinarith
    have hKlower : ∀ u v, u ∈ E.toClosedForm.domain → v ∈ E.toClosedForm.domain →
        E.toClosedForm.energyNormSq (u - v) ≤ K * F.energyNormSq (u - v) := by
      intro u v hu hv
      have hlow := hlower (u - v) (E.toClosedForm.domain.sub_mem hu hv)
      have hprod : A * Real.exp (-M) = 1 := by
        dsimp [A]
        rw [← Real.exp_add]
        ring_nf
        simp
      have hmul := mul_le_mul_of_nonneg_left hlow (le_of_lt hA)
      have hen := E.toClosedForm.form_nonneg (u - v)
        (E.toClosedForm.domain.sub_mem hu hv)
      have hfn : 0 ≤ F.form (u - v) (u - v) :=
        hform_nonneg (u - v) (E.toClosedForm.domain.sub_mem hu hv)
      have hnorm : 0 ≤ ‖u - v‖ ^ 2 := sq_nonneg _
      have hKA : A ≤ K := by dsimp [K]; exact le_max_left _ _
      have hK1 : (1 : ℝ) ≤ K := by dsimp [K]; exact le_max_right _ _
      dsimp [F, _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq]
      rw [← mul_assoc, hprod] at hmul
      nlinarith
    constructor
    · intro h
      refine { memCoreOn := ?_, denseEnergy := ?_, denseUniform := h.denseUniform }
      · intro u hu
        simpa [F, _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.MemCoreOn] using h.memCoreOn u hu
      · intro u hu ε hε
        have huE : u ∈ E.toClosedForm.domain := by simpa [F] using hu
        obtain ⟨w₀, hw₀, hw⟩ := h.denseEnergy u huE (ε / K) (div_pos hε hK)
        refine ⟨w₀, hw₀, ?_⟩
        have hwE : w₀ ∈ E.toClosedForm.domain := by
          simpa [F] using (h.memCoreOn w₀ hw₀).1
        have hbound := hKupper u w₀ huE hwE
        calc
          F.energyNormSq (u - w₀) ≤ K * E.toClosedForm.energyNormSq (u - w₀) := hbound
          _ < K * (ε / K) := mul_lt_mul_of_pos_left hw hK
          _ = ε := by field_simp
    · intro h
      refine { memCoreOn := ?_, denseEnergy := ?_, denseUniform := h.denseUniform }
      · intro u hu
        simpa [F, _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.MemCoreOn] using h.memCoreOn u hu
      · intro u hu ε hε
        have huE : u ∈ E.toClosedForm.domain := hu
        have huF : u ∈ F.domain := by simpa [F] using huE
        obtain ⟨w₀, hw₀, hw⟩ := h.denseEnergy u huF (ε / K) (div_pos hε hK)
        refine ⟨w₀, hw₀, ?_⟩
        have hwE : w₀ ∈ E.toClosedForm.domain := by
          simpa [F] using (h.memCoreOn w₀ hw₀).1
        have hbound := hKlower u w₀ huE hwE
        calc
          E.toClosedForm.energyNormSq (u - w₀) ≤ K * F.energyNormSq (u - w₀) := hbound
          _ < K * (ε / K) := mul_lt_mul_of_pos_left hw hK
          _ = ε := by field_simp
  have hregF : _root_.SubdiffusiveProcess.DirichletForm.IsRegular F := by
    obtain ⟨U, hU, hmU, C, hC⟩ := hreg
    exact ⟨U, hU, hmU, C, (hcore U C).mp hC⟩
  refine ⟨F, ?_, ?_, hcore, hregF⟩
  · refine { domain_eq := rfl, energy_eq := ?_, form_eq := ?_ }
    · intro u hu
      exact hdiag u hu
    · intro u hu v hv
      rfl
  · intro u hu
    exact ⟨hlower u hu, hupper u hu⟩

end SubdiffusiveProcess.Paper
