
-- paper's polynomial-in-s identification and the nonnegative-test measure order.
module

public import SubdiffusiveProcess.Paper.prop_21
public import SubdiffusiveProcess.Paper.conv_energy_measure_normalization
public import SubdiffusiveProcess.Paper.obl_FOT
public import SubdiffusiveProcess.Paper.in_energy_measure
public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Lane2.BoundaryPackaging
public import SubdiffusiveProcess.Lane2.NativeBridge
public import SubdiffusiveProcess.Lane2.ResponseMarkov
public import SubdiffusiveProcess.Lane2.BoundaryResponse
public import SubdiffusiveProcess.Lane2.MeshError
public import SubdiffusiveProcess.Lane2.ExternalInputs
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

lemma aux_cor_energy_measures_density
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q) (n : ℕ)
    (w : S.space) (φ : SpatialCoordinates d → ℝ) :
    (∫ x, φ x ∂((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
      (fun y => ENNReal.ofReal ((a n).val y * ∑ i : Fin d,
        ((w : SobolevData Q).2 i y) ^ 2))) =
      ∫ x in (Q : Set (SpatialCoordinates d)), φ x *
        ((a n).val x * ∑ i : Fin d, ((w : SobolevData Q).2 i x) ^ 2)) := by
  let μ : Measure (SpatialCoordinates d) := volume.restrict (Q : Set (SpatialCoordinates d))
  let g : SpatialCoordinates d → ℝ := fun y =>
    (a n).val y * ∑ i : Fin d, ((w : SobolevData Q).2 i y) ^ 2
  have hg : AEMeasurable g μ := by
    dsimp [g, μ]
    apply AEMeasurable.mul
    · exact (Lp.aestronglyMeasurable (a n).val).aemeasurable
    · have hs := Finset.aemeasurable_sum (Finset.univ : Finset (Fin d)) (fun i hi =>
          (Lp.aestronglyMeasurable ((w : SobolevData Q).2 i)).aemeasurable.pow_const 2)
      exact hs.congr (Filter.Eventually.of_forall (fun y => by simp))
  have hdensity : AEMeasurable (fun y => ENNReal.ofReal (g y)) μ := hg.ennreal_ofReal
  have htop : ∀ᵐ y ∂μ, ENNReal.ofReal (g y) < ⊤ :=
    Filter.Eventually.of_forall (fun y => ENNReal.ofReal_lt_top)
  have hwith := integral_withDensity_eq_integral_toReal_smul₀ hdensity htop φ
  rw [hwith]
  obtain ⟨c, hc, hca⟩ := (a n).property
  have hca' : ∀ᵐ y ∂μ, 0 ≤ (a n).val y := by
    simpa [μ] using hca.mono (fun y hy => le_trans hc.le hy)
  apply integral_congr_ae
  filter_upwards [hca'] with y hy
  have hg_nonneg : 0 ≤ g y := by
    dsimp [g]
    positivity
  simp only [smul_eq_mul, ENNReal.toReal_ofReal hg_nonneg]
  dsimp [g]
  ring

lemma aux_cor_energy_measures_energy_integrable
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q) (n : ℕ)
    (w : S.space) :
    Integrable (fun x => (a n).val x * ∑ i : Fin d,
      ((w : SobolevData Q).2 i x) ^ 2)
      (volume.restrict (Q : Set (SpatialCoordinates d))) := by
  have hi : ∀ i : Fin d, Integrable (fun x => (a n).val x *
      (((w : SobolevData Q).2 i x) * ((w : SobolevData Q).2 i x)))
      (volume.restrict (Q : Set (SpatialCoordinates d))) := by
    intro i
    simpa [sobolevGradient] using
      (integrable_weighted_coordinates (a n).val
        (sobolevGradient (w : SobolevData Q)) (sobolevGradient (w : SobolevData Q)) i)
  have hs : Integrable (fun x => ∑ i : Fin d, (a n).val x *
      (((w : SobolevData Q).2 i x) * ((w : SobolevData Q).2 i x)))
      (volume.restrict (Q : Set (SpatialCoordinates d))) := by
    apply integrable_finset_sum
    intro i hi'
    exact hi i
  apply hs.congr
  filter_upwards with x
  rw [Finset.mul_sum]
  congr 1 with i
  ring

lemma aux_cor_energy_measures_energy_integral
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q) (n : ℕ)
    (w : S.space) :
    (∫ x in (Q : Set (SpatialCoordinates d)), (a n).val x * ∑ i : Fin d,
      ((w : SobolevData Q).2 i x) ^ 2) =
      responseForm S (a n) w w := by
  rw [responseForm_apply]
  rw [← integral_finset_sum]
  · apply integral_congr_ae
    filter_upwards with x
    rw [Finset.mul_sum]
    congr 1 with i
    ring
  · intro i hi
    simpa only [pow_two] using! (integrable_weighted_coordinates (a n).val
      (sobolevGradient (w : SobolevData Q)) (sobolevGradient (w : SobolevData Q)) i)

lemma aux_cor_energy_measures_affine_integral
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q) (n : ℕ)
    (w : S.space) (φ : SpatialCoordinates d → ℝ) (t C : ℝ)
    (hφ : AEStronglyMeasurable φ (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hφC : ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
      ‖φ x‖ ≤ C) :
    (∫ x in (Q : Set (SpatialCoordinates d)),
        (1 + t * φ x) * ((a n).val x * ∑ i : Fin d,
          ((w : SobolevData Q).2 i x) ^ 2)) =
      responseForm S (a n) w w + t *
        (∫ x in (Q : Set (SpatialCoordinates d)), φ x *
          ((a n).val x * ∑ i : Fin d, ((w : SobolevData Q).2 i x) ^ 2)) := by
  let μ : Measure (SpatialCoordinates d) := volume.restrict (Q : Set (SpatialCoordinates d))
  let g : SpatialCoordinates d → ℝ := fun x => (a n).val x * ∑ i : Fin d,
    ((w : SobolevData Q).2 i x) ^ 2
  have hg : Integrable g μ := by
    simpa [g, μ] using aux_cor_energy_measures_energy_integrable S a n w
  have hφg : Integrable (fun x => φ x * g x) μ := hg.bdd_mul hφ hφC
  have htg : Integrable (fun x => t * (φ x * g x)) μ := hφg.const_mul t
  have hcalc : ∀ x, (1 + t * φ x) * g x = g x + t * (φ x * g x) := by
    intro x
    ring
  calc
    (∫ x in (Q : Set (SpatialCoordinates d)),
        (1 + t * φ x) * ((a n).val x * ∑ i : Fin d,
          ((w : SobolevData Q).2 i x) ^ 2)) =
        ∫ x, g x + t * (φ x * g x) ∂μ := by
          apply integral_congr_ae
          filter_upwards with x
          exact hcalc x
    _ = (∫ x, g x ∂μ) + ∫ x, t * (φ x * g x) ∂μ := integral_add hg htg
    _ = responseForm S (a n) w w + t * (∫ x, φ x * g x ∂μ) := by
      rw [aux_cor_energy_measures_energy_integral S a n w, integral_const_mul]
    _ = responseForm S (a n) w w + t *
        (∫ x in (Q : Set (SpatialCoordinates d)), φ x *
          ((a n).val x * ∑ i : Fin d, ((w : SobolevData Q).2 i x) ^ 2)) := by
      rfl

lemma aux_cor_energy_measures_gamma_affine
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E)
    (hGammaQ : ∀ w : DomainL2 Q, w ∈ E.domain →
      Gamma.measure w (Q : Set (SpatialCoordinates d))ᶜ = 0)
    (u : DomainL2 Q) (hu : u ∈ E.domain) (φ : SpatialCoordinates d → ℝ)
    (hφ : ContinuousOn φ (closure (Q : Set (SpatialCoordinates d)))) (t C : ℝ)
    (hφC : ∀ x ∈ (Q : Set (SpatialCoordinates d)), |φ x| ≤ C) :
    (∫ x in (Q : Set (SpatialCoordinates d)), (1 + t * φ x) ∂(Gamma.measure u)) =
      E.form u u + t * (∫ x in (Q : Set (SpatialCoordinates d)), φ x ∂(Gamma.measure u)) := by
  let μ : Measure (SpatialCoordinates d) := Gamma.measure u
  have hQm : MeasurableSet (Q : Set (SpatialCoordinates d)) := Q.isOpen.measurableSet
  have hQtop : μ (Q : Set (SpatialCoordinates d)) < ⊤ := Gamma.measure_lt_top hu _
  have hφa : AEStronglyMeasurable φ (μ.restrict (Q : Set (SpatialCoordinates d))) := by
    exact (hφ.mono subset_closure).aestronglyMeasurable hQm
  have hφC' : ∀ᵐ x ∂μ.restrict (Q : Set (SpatialCoordinates d)), ‖φ x‖ ≤ C := by
    filter_upwards [ae_restrict_mem hQm] with x hx
    simpa [Real.norm_eq_abs] using hφC x hx
  have hφi : Integrable φ (μ.restrict (Q : Set (SpatialCoordinates d))) :=
    IntegrableOn.of_bound hQtop hφa C hφC'
  have h1i : Integrable (fun _ : SpatialCoordinates d => (1 : ℝ))
      (μ.restrict (Q : Set (SpatialCoordinates d))) := by
    exact IntegrableOn.of_bound hQtop measurable_const.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun _ => by norm_num))
  have hti : Integrable (fun x => t * φ x)
      (μ.restrict (Q : Set (SpatialCoordinates d))) := hφi.const_mul t
  have hmass : (μ (Q : Set (SpatialCoordinates d))).toReal = E.form u u := by
    rw [measure_of_measure_compl_eq_zero (hGammaQ u hu), Gamma.measure_univ u hu]
  calc
    (∫ x in (Q : Set (SpatialCoordinates d)), (1 + t * φ x) ∂(Gamma.measure u)) =
        (∫ x in (Q : Set (SpatialCoordinates d)), (1 : ℝ) ∂μ) +
          ∫ x in (Q : Set (SpatialCoordinates d)), t * φ x ∂μ := by
            rw [← integral_add h1i hti]
    _ = E.form u u + t * (∫ x in (Q : Set (SpatialCoordinates d)), φ x ∂μ) := by
      rw [integral_const, measureReal_restrict_apply MeasurableSet.univ, univ_inter,
        integral_const_mul]
      simp only [smul_eq_mul, mul_one]
      change (μ (Q : Set (SpatialCoordinates d))).toReal +
        t * (∫ x in (Q : Set (SpatialCoordinates d)), φ x ∂μ) = _
      rw [hmass]

lemma aux_cor_energy_measures_liminf_affine
    (q : ℝ) (hq : 0 < q) (e : ℕ → EReal) (f : ℕ → ℝ) (e0 : EReal) (b : ℝ)
    (he : Tendsto e atTop (𝓝 e0)) (he_top : e0 ≠ (⊤ : EReal))
    (he_bot : e0 ≠ (⊥ : EReal))
    (hbounded : ∃ C : ℝ, ∀ᶠ n in atTop,
      (-C : EReal) ≤ (f n : EReal) ∧ (f n : EReal) ≤ C)
    (h : (e0 : EReal) + (q : EReal) * b ≤
      liminf (fun n => e n + ((q * f n : ℝ) : EReal)) atTop) :
    (b : EReal) ≤ liminf (fun n => (f n : EReal)) atTop := by
  let F : ℕ → EReal := fun n => (f n : EReal)
  obtain ⟨C, hC⟩ := hbounded
  have hClo : ∀ᶠ n in atTop, (-C : EReal) ≤ F n := by
    simpa [F] using hC.mono (fun n hn => hn.1)
  have hCup : ∀ᶠ n in atTop, F n ≤ (C : EReal) := by
    simpa [F] using hC.mono (fun n hn => hn.2)
  have hF_lower : IsBoundedUnder (fun x y : EReal => x ≥ y) atTop F := by
    refine ⟨(-C : EReal), ?_⟩
    exact hClo
  have hF_cobdd : IsCoboundedUnder (fun x y : EReal => x ≥ y) atTop F := by
    refine ⟨(C : EReal), ?_⟩
    intro z hz
    have hz' : ∀ᶠ n in atTop, z ≤ F n := hz
    obtain ⟨n, hn⟩ := (hz'.and hCup).exists
    exact le_trans hn.1 hn.2
  have hliminf_lower : (-C : EReal) ≤ liminf F atTop :=
    le_liminf_of_le hF_cobdd hClo
  have hliminf_upper : liminf F atTop ≤ (C : EReal) := by
    apply liminf_le_of_le hF_lower
    intro z hz
    have hz' : ∀ᶠ n in atTop, z ≤ F n := hz
    obtain ⟨n, hn⟩ := (hz'.and hCup).exists
    exact le_trans hn.1 hn.2
  have hliminf_bot : liminf F atTop ≠ (⊥ : EReal) := by
    exact ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe (-C)) hliminf_lower)
  have hliminf_top : liminf F atTop ≠ (⊤ : EReal) := by
    exact ne_of_lt (lt_of_le_of_lt hliminf_upper (EReal.coe_lt_top C))
  let m : EReal → EReal := fun x => (q : EReal) * x
  have hm : Monotone m := by
    intro x y hxy
    exact mul_le_mul_of_nonneg_left hxy (EReal.coe_nonneg.mpr hq.le)
  have hm_cont : ContinuousAt m (liminf F atTop) := by
    dsimp [m]
    exact (EReal.continuousAt_mul
      (Or.inl (EReal.coe_ne_zero.mpr hq.ne'))
      (Or.inl (EReal.coe_ne_zero.mpr hq.ne'))
      (Or.inl (EReal.coe_ne_bot q)) (Or.inl (EReal.coe_ne_top q))).comp
      (continuous_const.prodMk continuous_id).continuousAt
  have hm_liminf := Monotone.map_liminf_of_continuousAt hm F hm_cont
    hF_cobdd hF_lower
  have hmul : liminf (fun n => ((q * f n : ℝ) : EReal)) atTop =
      (q : EReal) * liminf F atTop := by
    simpa [m, F, Function.comp_def, EReal.coe_mul] using hm_liminf.symm
  have hadd := EReal.liminf_add_le
    (f := atTop) (u := e) (v := fun n => ((q * f n : ℝ) : EReal))
    (by rw [he.limsup_eq]; exact Or.inl he_bot)
    (by rw [he.limsup_eq]; exact Or.inl he_top)
  have hupper : liminf (fun n => e n + ((q * f n : ℝ) : EReal)) atTop ≤
      (e0 : EReal) + (q : EReal) * liminf F atTop := by
    rw [he.limsup_eq, hmul] at hadd
    simpa [Pi.add_apply] using! hadd
  have hchain := h.trans hupper
  have hFl : liminf F atTop = ((liminf F atTop).toReal : EReal) :=
    (EReal.coe_toReal hliminf_top hliminf_bot).symm
  rw [← EReal.coe_toReal he_top he_bot, hFl] at hchain
  have hreal : e0.toReal + q * b ≤ e0.toReal + q * (liminf F atTop).toReal := by
    apply EReal.coe_le_coe_iff.mp
    simpa [EReal.coe_add, EReal.coe_mul] using hchain
  have hbreal : b ≤ (liminf F atTop).toReal := by nlinarith
  rw [← EReal.coe_toReal hliminf_top hliminf_bot]
  exact EReal.coe_le_coe_iff.mpr hbreal

lemma aux_cor_energy_measures_sequence_affine
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q) (uN : ℕ → S.space)
    (φ : SpatialCoordinates d → ℝ) (t C : ℝ)
    (hφ : AEStronglyMeasurable φ (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hφC : ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))), ‖φ x‖ ≤ C) :
    (fun n => (((∫ x in (Q : Set (SpatialCoordinates d)), (1 + t * φ x) *
      ((a n).val x * ∑ i : Fin d, ((uN n : SobolevData Q).2 i x) ^ 2)) : ℝ) : EReal)) =
    (fun n => (((responseForm S (a n) (uN n) (uN n) : ℝ) : EReal) +
      (((t * (∫ x in (Q : Set (SpatialCoordinates d)), φ x *
        ((a n).val x * ∑ i : Fin d, ((uN n : SobolevData Q).2 i x) ^ 2))) : ℝ) : EReal))) := by
  funext n
  have hh := aux_cor_energy_measures_affine_integral S a n (uN n) φ t C hφ hφC
  have hh' := congrArg (fun r : ℝ => (r : EReal)) hh
  simpa [EReal.coe_add, EReal.coe_mul] using hh'

lemma aux_cor_energy_measures_cross_absolutelyContinuous
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E)
    (u v : DomainL2 Q) (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (μ : Measure (SpatialCoordinates d))
    (hμu : Gamma.measure u ≪ μ) (hμv : Gamma.measure v ≪ μ) :
    (Gamma.cross u v).toJordanDecomposition.posPart ≪ μ ∧
      (Gamma.cross u v).toJordanDecomposition.negPart ≪ μ := by
  have hpos : (Gamma.cross u v).toJordanDecomposition.posPart ≪ μ := by
    refine Measure.AbsolutelyContinuous.mk ?_
    intro B hB hμB
    obtain ⟨I, hI, hIpos, hIneg, hp, hn⟩ :=
      (Gamma.cross u v).toJordanDecomposition_spec
    rw [hp, SignedMeasure.toMeasureOfZeroLE_apply (s := Gamma.cross u v) hIpos hI hB]
    have hu0 : Gamma.measure u (I ∩ B) = 0 :=
      measure_mono_null inter_subset_right (hμu hμB)
    have hv0 : Gamma.measure v (I ∩ B) = 0 :=
      measure_mono_null inter_subset_right (hμv hμB)
    have hc := Gamma.abs_cross_le u hu v hv (I ∩ B) (hI.inter hB)
    have hc0 : Gamma.cross u v (I ∩ B) = 0 := by
      apply abs_eq_zero.mp
      apply le_antisymm
      · simpa [hu0, hv0] using hc
      · exact abs_nonneg _
    simp [hc0]
  have hneg : (Gamma.cross u v).toJordanDecomposition.negPart ≪ μ := by
    refine Measure.AbsolutelyContinuous.mk ?_
    intro B hB hμB
    obtain ⟨I, hI, hIpos, hIneg, hp, hn⟩ :=
      (Gamma.cross u v).toJordanDecomposition_spec
    rw [hn, SignedMeasure.toMeasureOfLEZero_apply (s := Gamma.cross u v) hIneg hI.compl hB]
    have hu0 : Gamma.measure u (Iᶜ ∩ B) = 0 :=
      measure_mono_null inter_subset_right (hμu hμB)
    have hv0 : Gamma.measure v (Iᶜ ∩ B) = 0 :=
      measure_mono_null inter_subset_right (hμv hμB)
    have hc := Gamma.abs_cross_le u hu v hv (Iᶜ ∩ B) (hI.compl.inter hB)
    have hc0 : Gamma.cross u v (Iᶜ ∩ B) = 0 := by
      apply abs_eq_zero.mp
      apply le_antisymm
      · simpa [hu0, hv0] using hc
      · exact abs_nonneg _
    simp [hc0]
  exact ⟨hpos, hneg⟩

lemma aux_cor_energy_measures_signedIntegralOn_Q_eq_univ
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (ν : SignedMeasure X) (μ : Measure X) (Q : Set X) (hQ : MeasurableSet Q)
    (hpos : ν.toJordanDecomposition.posPart ≪ μ)
    (hneg : ν.toJordanDecomposition.negPart ≪ μ)
    (hμQ : μ Qᶜ = 0) (f : X → ℝ) :
    DirichletForm.signedIntegralOn ν Q f =
      DirichletForm.signedIntegralOn ν Set.univ f := by
  have hpQ : ∀ᵐ x ∂ν.toJordanDecomposition.posPart, x ∈ Q := by
    apply ae_iff.mpr
    exact hpos (by simpa using! hμQ)
  have hnQ : ∀ᵐ x ∂ν.toJordanDecomposition.negPart, x ∈ Q := by
    apply ae_iff.mpr
    exact hneg (by simpa using! hμQ)
  rw [DirichletForm.signedIntegralOn]
  congr 1
  · rw [Measure.restrict_eq_self_of_ae_mem hpQ, Measure.restrict_univ]
  · rw [Measure.restrict_eq_self_of_ae_mem hnQ, Measure.restrict_univ]

lemma aux_cor_energy_measures_strong_weak
    {wN : ℕ → DomainL2 Q} {w : DomainL2 Q}
    (h : Tendsto wN atTop (𝓝 w)) :
    ∀ f : DomainL2 Q,
      Tendsto (fun n => inner ℝ f (wN n)) atTop
        (𝓝 (inner ℝ f w)) := by
  intro f
  exact tendsto_const_nhds.inner h

lemma aux_cor_energy_measures_liminf_le_const
    (f : ℕ → ℝ) (C : ℝ) (h0 : ∀ n, 0 ≤ f n)
    (hC : ∀ n, f n ≤ C) :
    liminf (fun n => (f n : EReal)) atTop ≤ (C : EReal) := by
  calc
    liminf (fun n => (f n : EReal)) atTop ≤
        liminf (fun _ : ℕ => (C : EReal)) atTop := by
      apply Filter.liminf_le_liminf
      · filter_upwards [] with n
        exact EReal.coe_le_coe_iff.mpr (hC n)
      · apply Filter.isBoundedUnder_of_eventually_ge
        filter_upwards [] with n
        exact EReal.coe_nonneg.mpr (h0 n)
      · exact Filter.isCoboundedUnder_ge_of_le atTop (fun _ => le_rfl)
    _ = (C : EReal) := Filter.liminf_const _

lemma aux_cor_energy_measures_domain_of_bound
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q)
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hlower : ∀ (wN : ℕ → S.space) (w : DomainL2 Q),
      (∀ f : DomainL2 Q,
        Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      limitFormEnergy G w ≤
        liminf (fun n => ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal)) atTop)
    (u : DomainL2 Q) (uN : ℕ → S.space) (E0 : ℝ)
    (huconv : Tendsto (fun n => (uN n).val.1) atTop (𝓝 u))
    (hE0 : ∀ n : ℕ, responseForm S (a n) (uN n) (uN n) ≤ E0) :
    u ∈ limitFormDomain G := by
  have hweak := aux_cor_energy_measures_strong_weak
    (wN := fun n => (uN n).val.1) huconv
  have hlow := hlower uN u hweak
  have hlim := aux_cor_energy_measures_liminf_le_const
    (fun n => responseForm S (a n) (uN n) (uN n)) E0
    (fun n => responseForm_nonneg S (a n) (uN n)) hE0
  have hfin : limitFormEnergy G u ≤ (E0 : EReal) := hlow.trans hlim
  exact hfin.trans_lt (EReal.coe_lt_top E0)

lemma aux_cor_energy_measures_domain_of_energy_ne_top
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (u : DomainL2 Q) (h : E.energy u ≠ (⊤ : EReal)) : u ∈ E.domain :=
  (E.energy_lt_top_iff u).mp (lt_top_iff_ne_top.mpr h)

lemma aux_cor_energy_measures_restrict_closure
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (μ : Measure X) (Q : Set X) (hQ : μ Qᶜ = 0) :
    μ.restrict (closure Q) = μ := by
  apply Measure.restrict_eq_self_of_ae_mem
  apply mem_ae_iff.mpr
  exact measure_mono_null (compl_subset_compl.mpr subset_closure) hQ

lemma aux_cor_energy_measures_restrict_cube_closure
    (μ : Measure (SpatialCoordinates d))
    (hQ : μ (Q : Set (SpatialCoordinates d))ᶜ = 0) :
    μ.restrict (closure (Q : Set (SpatialCoordinates d))) = μ :=
  aux_cor_energy_measures_restrict_closure μ (Q : Set (SpatialCoordinates d)) hQ

lemma aux_cor_energy_measures_isFiniteMeasure
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (hμ : μ Set.univ < (⊤ : ENNReal)) : IsFiniteMeasure μ :=
  ⟨hμ⟩

lemma aux_cor_energy_measures_integrable_supported
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [T2Space X] [LocallyCompactSpace X]
    (μ : Measure X) (K : Set X) (hμ : μ Set.univ < (⊤ : ENNReal))
    (hK : μ Kᶜ = 0) (hcompact : IsCompact K)
    (f : X → ℝ) (hf : ContinuousOn f K) : Integrable f μ := by
  letI : IsFiniteMeasure μ := aux_cor_energy_measures_isFiniteMeasure μ hμ
  have hi : Integrable (Set.indicator K f) μ :=
    (hf.integrableOn_compact hcompact).integrable_indicator hcompact.measurableSet
  apply Integrable.congr hi
  filter_upwards [mem_ae_iff.mpr (by simpa using hK)] with x hx
  simp [Set.indicator_of_mem hx]

lemma aux_cor_energy_measures_integrable_const
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (hμ : μ Set.univ < (⊤ : ENNReal)) (c : ℝ) :
    Integrable (fun _ : X => c) μ := by
  letI : IsFiniteMeasure μ := aux_cor_energy_measures_isFiniteMeasure μ hμ
  exact integrable_const c

lemma aux_cor_energy_measures_continuous_domination
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (hQcube : Q = centeredCube z0 R hR)
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q)
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (Gamma : DirichletForm.EnergyMeasure E)
    (hGammaQ : ∀ w : DomainL2 Q, w ∈ E.domain →
      Gamma.measure w (Q : Set (SpatialCoordinates d))ᶜ = 0)
    (hweighted : ∀ rho : SpatialCoordinates d → ℝ,
      ContinuousOn rho (closure (Q : Set (SpatialCoordinates d))) →
      (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), 0 < rho x) →
      ∀ sigma : ℕ → ℕ, StrictMono sigma →
      ∀ (wN : ℕ → S.space) (w : DomainL2 Q), w ∈ limitFormDomain G →
      (∀ f : DomainL2 Q,
        Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      (((∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(Gamma.measure w)) : ℝ) : EReal) ≤
        liminf (fun n =>
          (((∫ x in (Q : Set (SpatialCoordinates d)), rho x *
            ((a (sigma n)).val x * ∑ i : Fin d,
              ((wN (sigma n) : SobolevData Q).2 i x) ^ 2)) : ℝ) : EReal)) atTop)
    (u : DomainL2 Q) (uN : ℕ → S.space) (nu : Measure (SpatialCoordinates d))
    (sigma : ℕ → ℕ) (hnu : nu Set.univ < (⊤ : ENNReal))
    (hnuQ : nu ((closure (Q : Set (SpatialCoordinates d)))ᶜ) = 0)
    (hsigma : StrictMono sigma) (hu : u ∈ limitFormDomain G)
    (hweak : ∀ f : DomainL2 Q,
      Tendsto (fun n => inner ℝ f (uN n).val.1) atTop
        (𝓝 (inner ℝ f u)))
    (hcluster : ∀ φ : SpatialCoordinates d → ℝ,
      ContinuousOn φ (closure (Q : Set (SpatialCoordinates d))) →
      Tendsto (fun n => ∫ x, φ x ∂(((volume.restrict
        (Q : Set (SpatialCoordinates d)))).withDensity
        (fun y => ENNReal.ofReal ((a (sigma n)).val y *
          ∑ i : Fin d, ((uN (sigma n) : SobolevData Q).2 i y) ^ 2)))) atTop
        (𝓝 (∫ x, φ x ∂nu)))
    (huE : u ∈ E.domain) :
    ∀ φ : SpatialCoordinates d → ℝ,
      ContinuousOn φ (closure (Q : Set (SpatialCoordinates d))) →
      (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), 0 ≤ φ x) →
      (∫ x, φ x ∂(Gamma.measure u)) ≤ ∫ x, φ x ∂nu := by
  intro φ hφ hφ0
  have hGammaFinite : (Gamma.measure u) Set.univ < (⊤ : ENNReal) :=
    Gamma.measure_univ_lt_top u huE
  have hGammaSupport : (Gamma.measure u).restrict (Q : Set (SpatialCoordinates d)) =
      Gamma.measure u := by
    apply Measure.restrict_eq_self_of_ae_mem
    exact mem_ae_iff.mpr (hGammaQ u huE)
  have hcompact : IsCompact (closure (Q : Set (SpatialCoordinates d))) := by
    rw [hQcube]
    exact (centeredCube_isBounded z0 hR).isCompact_closure
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hφ
  let C : ℝ := max M 0 + 1
  have hC : 0 < C := by
    dsimp [C]
    linarith [le_max_right M 0]
  have hφC : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), |φ x| ≤ C := by
    intro x hx
    have hxM : |φ x| ≤ M := by
      simpa [Real.norm_eq_abs] using hM x hx
    dsimp [C]
    linarith [le_max_left M 0]
  have hφG : Integrable φ (Gamma.measure u) := by
    apply aux_cor_energy_measures_integrable_supported (Gamma.measure u)
      (closure (Q : Set (SpatialCoordinates d))) hGammaFinite
      (measure_mono_null (compl_subset_compl.mpr subset_closure) (hGammaQ u huE))
      hcompact φ hφ
  have hφnu : Integrable φ nu := by
    apply aux_cor_energy_measures_integrable_supported nu
      (closure (Q : Set (SpatialCoordinates d))) hnu (by simpa using hnuQ)
      hcompact φ hφ
  have hineqε : ∀ ε : ℝ, 0 < ε →
      (∫ x, φ x ∂(Gamma.measure u)) ≤
        (∫ x, φ x ∂nu) + ε * (nu Set.univ).toReal := by
    intro ε hε
    have hφeps : ContinuousOn (fun x => φ x + ε)
        (closure (Q : Set (SpatialCoordinates d))) := hφ.add continuousOn_const
    have hφepspos : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), 0 < φ x + ε := by
      intro x hx
      linarith [hφ0 x hx]
    have hw := hweighted (fun x => φ x + ε) hφeps hφepspos
      sigma hsigma uN u hu hweak
    have hc := hcluster (fun x => φ x + ε) hφeps
    have hcE : Tendsto (fun n =>
        (((∫ x, (φ x + ε) ∂(((volume.restrict
          (Q : Set (SpatialCoordinates d)))).withDensity
          (fun y => ENNReal.ofReal ((a (sigma n)).val y *
            ∑ i : Fin d, ((uN (sigma n) : SobolevData Q).2 i y) ^ 2)))) : ℝ) : EReal)) atTop
        (𝓝 (((∫ x, (φ x + ε) ∂nu) : ℝ) : EReal)) := (EReal.tendsto_coe).mpr hc
    have hw' : (∫ x in (Q : Set (SpatialCoordinates d)), (φ x + ε) ∂(Gamma.measure u) : ℝ) ≤
        liminf (fun n =>
          (((∫ x, (φ x + ε) ∂(((volume.restrict
            (Q : Set (SpatialCoordinates d)))).withDensity
            (fun y => ENNReal.ofReal ((a (sigma n)).val y *
              ∑ i : Fin d, ((uN (sigma n) : SobolevData Q).2 i y) ^ 2)))) : ℝ) : EReal)) atTop := by
      convert hw using 1
      apply liminf_congr
      filter_upwards [] with n
      exact congrArg (fun r : ℝ => (r : EReal))
        (aux_cor_energy_measures_density S a (sigma n) (uN (sigma n))
          (fun x => φ x + ε))
    rw [hcE.liminf_eq] at hw'
    have hGadd : (∫ x, (φ x + ε) ∂(Gamma.measure u)) =
        (∫ x, φ x ∂(Gamma.measure u)) + ε * (Gamma.measure u Set.univ).toReal := by
      have hconstG := aux_cor_energy_measures_integrable_const (Gamma.measure u) hGammaFinite ε
      rw [integral_add hφG hconstG, integral_const]
      simp [mul_comm, measureReal_def]
    have hNadd : (∫ x, (φ x + ε) ∂nu) =
        (∫ x, φ x ∂nu) + ε * (nu Set.univ).toReal := by
      have hconstN := aux_cor_energy_measures_integrable_const nu hnu ε
      rw [integral_add hφnu hconstN, integral_const]
      simp [mul_comm, measureReal_def]
    have hw'' : (∫ x, (φ x + ε) ∂(Gamma.measure u)) ≤ ∫ x, (φ x + ε) ∂nu := by
      have hseteq : (∫ x in (Q : Set (SpatialCoordinates d)), (φ x + ε) ∂(Gamma.measure u)) =
          ∫ x, (φ x + ε) ∂(Gamma.measure u) := by
        change (∫ x, (φ x + ε) ∂((Gamma.measure u).restrict (Q : Set (SpatialCoordinates d)))) = _
        rw [hGammaSupport]
      calc
        _ = (∫ x in (Q : Set (SpatialCoordinates d)), (φ x + ε) ∂(Gamma.measure u)) := hseteq.symm
        _ ≤ ∫ x, (φ x + ε) ∂nu := EReal.coe_le_coe_iff.mp hw'
    rw [hGadd, hNadd] at hw''
    have hmass : 0 ≤ (Gamma.measure u Set.univ).toReal := ENNReal.toReal_nonneg
    have hterm : 0 ≤ ε * (Gamma.measure u Set.univ).toReal :=
      mul_nonneg (le_of_lt hε) hmass
    linarith
  refine le_of_forall_pos_le_add ?_
  intro δ hδ
  let ε : ℝ := δ / ((nu Set.univ).toReal + 1)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hh := hineqε ε hε
  have hmass : 0 ≤ (nu Set.univ).toReal := ENNReal.toReal_nonneg
  have hbound : ε * (nu Set.univ).toReal ≤ δ := by
    dsimp [ε]
    calc
      δ / ((nu Set.univ).toReal + 1) * (nu Set.univ).toReal ≤
          δ / ((nu Set.univ).toReal + 1) * ((nu Set.univ).toReal + 1) := by
            gcongr
            exact le_add_of_nonneg_right zero_le_one
      _ = δ := by field_simp
  exact hh.trans (by linarith [hbound])

lemma aux_cor_energy_measures_weak_of_space
    (S : ResponseSpace Q) (uN : ℕ → S.space) (u : DomainL2 Q)
    (h : Tendsto (fun n => (uN n).val.1) atTop (𝓝 u)) :
    ∀ f : DomainL2 Q,
      Tendsto (fun n => inner ℝ f (uN n).val.1) atTop
        (𝓝 (inner ℝ f u)) := by
  intro f
  exact tendsto_const_nhds.inner h

lemma aux_cor_energy_measures_borel_domination
    (gamma nu : Measure (SpatialCoordinates d))
    (hgamma : gamma Set.univ < (⊤ : ENNReal))
    (hnu : nu Set.univ < (⊤ : ENNReal))
    (hgammaReg : gamma.Regular)
    (K : Set (SpatialCoordinates d))
    (hcont : ∀ φ : SpatialCoordinates d → ℝ,
      ContinuousOn φ K →
      (∀ x ∈ K, 0 ≤ φ x) →
      (∫ x, φ x ∂gamma) ≤ ∫ x, φ x ∂nu) :
    ∀ B : Set (SpatialCoordinates d), MeasurableSet B → gamma B ≤ nu B := by
  letI : IsFiniteMeasure gamma := aux_cor_energy_measures_isFiniteMeasure gamma hgamma
  letI : IsFiniteMeasure nu := aux_cor_energy_measures_isFiniteMeasure nu hnu
  letI : gamma.Regular := hgammaReg
  intro B hB
  have hmeasure := DirichletForm.measure_le_of_integral_le
    (ν := gamma) (μ := nu) (C := 1) (U := Set.univ) isOpen_univ
      (fun f hfc hfs hfu hf0 hf1 => ?_) (B := B) (subset_univ B)
  · simpa using hmeasure
  · convert hcont f hfc.continuousOn (fun x hx => hf0 x) using 1 <;> norm_num

lemma aux_cor_energy_measures_clause_b
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (hQcube : Q = centeredCube z0 R hR)
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q)
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hEform : ∀ w : DomainL2 Q, E.energy w = limitFormEnergy G w)
    (Gamma : DirichletForm.EnergyMeasure E)
    (hGammaQ : ∀ w : DomainL2 Q, w ∈ E.domain →
      Gamma.measure w (Q : Set (SpatialCoordinates d))ᶜ = 0)
    (hweighted : ∀ rho : SpatialCoordinates d → ℝ,
      ContinuousOn rho (closure (Q : Set (SpatialCoordinates d))) →
      (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), 0 < rho x) →
      ∀ sigma : ℕ → ℕ, StrictMono sigma →
      ∀ (wN : ℕ → S.space) (w : DomainL2 Q), w ∈ limitFormDomain G →
      (∀ f : DomainL2 Q,
        Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      (((∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(Gamma.measure w)) : ℝ) : EReal) ≤
        liminf (fun n =>
          (((∫ x in (Q : Set (SpatialCoordinates d)), rho x *
            ((a (sigma n)).val x * ∑ i : Fin d,
              ((wN (sigma n) : SobolevData Q).2 i x) ^ 2)) : ℝ) : EReal)) atTop)
    (hlower : ∀ (wN : ℕ → S.space) (w : DomainL2 Q),
      (∀ f : DomainL2 Q,
        Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      limitFormEnergy G w ≤
        liminf (fun n => ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal)) atTop)
    (u : DomainL2 Q) (uN : ℕ → S.space) (E0 : ℝ)
    (nu : Measure (SpatialCoordinates d)) (sigma : ℕ → ℕ)
    (hnu : nu Set.univ < (⊤ : ENNReal))
    (hnuQ : nu ((closure (Q : Set (SpatialCoordinates d)))ᶜ) = 0)
    (hsigma : StrictMono sigma)
    (huconv : Tendsto (fun n => (uN n).val.1) atTop (𝓝 u))
    (hE0 : ∀ n : ℕ, responseForm S (a n) (uN n) (uN n) ≤ E0)
    (hcluster : ∀ φ : SpatialCoordinates d → ℝ,
      ContinuousOn φ (closure (Q : Set (SpatialCoordinates d))) →
      Tendsto (fun n => ∫ x, φ x ∂(((volume.restrict
        (Q : Set (SpatialCoordinates d)))).withDensity
        (fun y => ENNReal.ofReal ((a (sigma n)).val y *
          ∑ i : Fin d, ((uN (sigma n) : SobolevData Q).2 i y) ^ 2)))) atTop
        (𝓝 (∫ x, φ x ∂nu))) :
    u ∈ limitFormDomain G ∧
      ∀ B : Set (SpatialCoordinates d), MeasurableSet B → Gamma.measure u B ≤ nu B := by
  have huDom : u ∈ limitFormDomain G := by
    exact aux_cor_energy_measures_domain_of_bound S a G hlower u uN E0 huconv hE0
  have huE : u ∈ E.domain := by
    have hfin : E.energy u ≠ (⊤ : EReal) := by
      rw [hEform u]
      exact (show limitFormEnergy G u < ⊤ from huDom).ne
    exact aux_cor_energy_measures_domain_of_energy_ne_top E u hfin
  have hweak := aux_cor_energy_measures_weak_of_space S uN u huconv
  have hcont_dom :=
    aux_cor_energy_measures_continuous_domination (d := d) (Q := Q)
      z0 R hR hQcube S a E G Gamma hGammaQ hweighted u uN nu sigma
      hnu hnuQ hsigma huDom hweak hcluster huE
  have hGammaFinite : (Gamma.measure u) Set.univ < (⊤ : ENNReal) :=
    Gamma.measure_univ_lt_top u huE
  have hGammaReg : (Gamma.measure u).Regular := Gamma.regular u huE
  refine ⟨huDom, ?_⟩
  exact aux_cor_energy_measures_borel_domination (Gamma.measure u) nu
    hGammaFinite hnu hGammaReg (closure (Q : Set (SpatialCoordinates d))) hcont_dom

lemma aux_cor_energy_measures_signedIntegralOn_rnDeriv
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (s : SignedMeasure X) (μ : Measure X) (B : Set X) (f : X → ℝ)
    (hμ : μ Set.univ < (⊤ : ENNReal)) (hB : MeasurableSet B)
    (hpos : s.toJordanDecomposition.posPart ≪ μ)
    (hneg : s.toJordanDecomposition.negPart ≪ μ)
    (hf : AEStronglyMeasurable f (μ.restrict B))
    (hfb : ∃ C : ℝ, ∀ᵐ x ∂(μ.restrict B), ‖f x‖ ≤ C) :
    DirichletForm.signedIntegralOn s B f =
      ∫ x in B, s.rnDeriv μ x * f x ∂μ := by
  letI : IsFiniteMeasure μ := aux_cor_energy_measures_isFiniteMeasure μ hμ
  have htotal : s.totalVariation ≪ μ :=
    (SignedMeasure.totalVariation_absolutelyContinuous_iff s μ).2 ⟨hpos, hneg⟩
  have hac : s ≪ᵥ μ.toENNRealVectorMeasure := by
    rw [SignedMeasure.absolutelyContinuous_ennreal_iff]
    simpa only [VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure] using htotal
  have hs :=
    (SignedMeasure.absolutelyContinuous_iff_withDensityᵥ_rnDeriv_eq s μ).mp hac
  have hr : Integrable (s.rnDeriv μ) (μ.restrict B) :=
    (SignedMeasure.integrable_rnDeriv s μ).restrict
  obtain ⟨C, hC⟩ := hfb
  have hprod : Integrable (fun x => s.rnDeriv μ x * f x) (μ.restrict B) :=
    hr.mul_bdd hf hC
  have hprod_pos : Integrable (fun x => max (s.rnDeriv μ x) 0 * f x)
      (μ.restrict B) :=
    hr.pos_part.mul_bdd hf hC
  have hprod_neg : Integrable (fun x => max (-s.rnDeriv μ x) 0 * f x)
      (μ.restrict B) :=
    hr.neg_part.mul_bdd hf hC
  have hj := SignedMeasure.toJordanDecomposition_eq_of_eq_add_withDensity
    (s := s) (t := (0 : SignedMeasure X)) (μ := μ) (f := s.rnDeriv μ)
    (SignedMeasure.measurable_rnDeriv s μ) (SignedMeasure.integrable_rnDeriv s μ)
    VectorMeasure.MutuallySingular.zero_left (by simpa using hs.symm)
  rw [DirichletForm.signedIntegralOn, hj]
  simp only [SignedMeasure.toJordanDecomposition_zero,
    JordanDecomposition.zero_posPart, JordanDecomposition.zero_negPart, zero_add]
  have hpos_int :
      (∫ x in B, f x ∂μ.withDensity (fun x => ENNReal.ofReal (s.rnDeriv μ x))) =
        ∫ x in B, max (s.rnDeriv μ x) 0 * f x ∂μ := by
    rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
      (SignedMeasure.measurable_rnDeriv s μ).ennreal_ofReal
      (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)) f hB]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [smul_eq_mul]
    congr 1
  have hneg_int :
      (∫ x in B, f x ∂μ.withDensity (fun x => ENNReal.ofReal (-s.rnDeriv μ x))) =
        ∫ x in B, max (-s.rnDeriv μ x) 0 * f x ∂μ := by
    have hwd := setIntegral_withDensity_eq_setIntegral_toReal_smul (μ := μ)
      (SignedMeasure.measurable_rnDeriv s μ).neg.ennreal_ofReal
      (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)) f hB
    calc
      _ = ∫ x in B, (ENNReal.ofReal (-s.rnDeriv μ x)).toReal • f x ∂μ := by
        simpa only [Pi.neg_apply] using! hwd
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [smul_eq_mul]
        congr 1
  rw [hpos_int, hneg_int, ← integral_sub hprod_pos hprod_neg]
  apply integral_congr_ae
  filter_upwards [] with x
  have hsplit : max (s.rnDeriv μ x) 0 - max (-s.rnDeriv μ x) 0 = s.rnDeriv μ x := by
    by_cases hx : 0 ≤ s.rnDeriv μ x
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), sub_zero]
    · have hx' : s.rnDeriv μ x ≤ 0 := le_of_not_ge hx
      rw [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx')]
      ring
  calc
    max (s.rnDeriv μ x) 0 * f x - max (-s.rnDeriv μ x) 0 * f x =
        (max (s.rnDeriv μ x) 0 - max (-s.rnDeriv μ x) 0) * f x := by ring
    _ = s.rnDeriv μ x * f x := by rw [hsplit]

lemma aux_cor_energy_measures_signedIntegralOn_toSignedMeasure
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (B : Set X) (hB : MeasurableSet B) (f : X → ℝ) :
    DirichletForm.signedIntegralOn μ.toSignedMeasure B f =
      ∫ x in B, f x ∂μ := by
  let j : JordanDecomposition X :=
    { posPart := μ
      negPart := 0
      mutuallySingular := Measure.MutuallySingular.zero_right }
  have hj : (μ.toSignedMeasure).toJordanDecomposition = j := by
    apply JordanDecomposition.toSignedMeasure_injective
    rw [SignedMeasure.toSignedMeasure_toJordanDecomposition]
    simp [j, JordanDecomposition.toSignedMeasure]
  rw [DirichletForm.signedIntegralOn, hj]
  simp only [j, JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_zero,
    sub_zero]
  simp

lemma aux_cor_energy_measures_signedIntegralOn_add
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (s t : SignedMeasure X) (μ : Measure X) [IsFiniteMeasure μ]
    (B : Set X) (f : X → ℝ) (hB : MeasurableSet B)
    (hspos : s.toJordanDecomposition.posPart ≪ μ)
    (hsneg : s.toJordanDecomposition.negPart ≪ μ)
    (htpos : t.toJordanDecomposition.posPart ≪ μ)
    (htneg : t.toJordanDecomposition.negPart ≪ μ)
    (hstpos : (s + t).toJordanDecomposition.posPart ≪ μ)
    (hstneg : (s + t).toJordanDecomposition.negPart ≪ μ)
    (hf : AEStronglyMeasurable f (μ.restrict B))
    (hfb : ∃ C : ℝ, ∀ᵐ x ∂(μ.restrict B), ‖f x‖ ≤ C) :
    DirichletForm.signedIntegralOn (s + t) B f =
      DirichletForm.signedIntegralOn s B f +
        DirichletForm.signedIntegralOn t B f := by
  rw [aux_cor_energy_measures_signedIntegralOn_rnDeriv s μ B f
      (by exact IsFiniteMeasure.measure_univ_lt_top) hB hspos hsneg hf hfb]
  rw [aux_cor_energy_measures_signedIntegralOn_rnDeriv t μ B f
      (by exact IsFiniteMeasure.measure_univ_lt_top) hB htpos htneg hf hfb]
  rw [aux_cor_energy_measures_signedIntegralOn_rnDeriv (s + t) μ B f
      (by exact IsFiniteMeasure.measure_univ_lt_top) hB hstpos hstneg hf hfb]
  have hsint : Integrable (fun x => s.rnDeriv μ x * f x) (μ.restrict B) :=
    (SignedMeasure.integrable_rnDeriv s μ).restrict.mul_bdd hf hfb.choose_spec
  have htint : Integrable (fun x => t.rnDeriv μ x * f x) (μ.restrict B) :=
    (SignedMeasure.integrable_rnDeriv t μ).restrict.mul_bdd hf hfb.choose_spec
  rw [← integral_add hsint htint]
  apply integral_congr_ae
  have hderiv := ae_restrict_of_ae (s := B) (SignedMeasure.rnDeriv_add s t μ)
  filter_upwards [hderiv] with x hx
  rw [hx]
  simp only [Pi.add_apply]
  ring

lemma aux_cor_energy_measures_signedIntegralOn_smul
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (c : ℝ) (s : SignedMeasure X) (μ : Measure X) [IsFiniteMeasure μ]
    (B : Set X) (f : X → ℝ) (hB : MeasurableSet B)
    (hspos : s.toJordanDecomposition.posPart ≪ μ)
    (hsneg : s.toJordanDecomposition.negPart ≪ μ)
    (hcpos : (c • s).toJordanDecomposition.posPart ≪ μ)
    (hcneg : (c • s).toJordanDecomposition.negPart ≪ μ)
    (hf : AEStronglyMeasurable f (μ.restrict B))
    (hfb : ∃ C : ℝ, ∀ᵐ x ∂(μ.restrict B), ‖f x‖ ≤ C) :
    DirichletForm.signedIntegralOn (c • s) B f =
      c * DirichletForm.signedIntegralOn s B f := by
  rw [aux_cor_energy_measures_signedIntegralOn_rnDeriv (c • s) μ B f
      (by exact IsFiniteMeasure.measure_univ_lt_top) hB hcpos hcneg hf hfb]
  rw [aux_cor_energy_measures_signedIntegralOn_rnDeriv s μ B f
      (by exact IsFiniteMeasure.measure_univ_lt_top) hB hspos hsneg hf hfb]
  have hsint : Integrable (fun x => s.rnDeriv μ x * f x) (μ.restrict B) :=
    (SignedMeasure.integrable_rnDeriv s μ).restrict.mul_bdd hf hfb.choose_spec
  rw [← integral_const_mul]
  apply integral_congr_ae
  have hderiv := ae_restrict_of_ae (s := B) (SignedMeasure.rnDeriv_smul s μ c)
  filter_upwards [hderiv] with x hx
  rw [hx]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma aux_cor_energy_measures_signedIntegralOn_linear_combination
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (s0 s1 s2 s : SignedMeasure X) (μ : Measure X) (B : Set X) (f : X → ℝ)
    (c q : ℝ) (hμ : μ Set.univ < (⊤ : ENNReal)) (hB : MeasurableSet B)
    (hs0 : s0.totalVariation ≪ μ) (hs1 : s1.totalVariation ≪ μ)
    (hs2 : s2.totalVariation ≪ μ)
    (hc2 : (c • s1).totalVariation ≪ μ)
    (hc1 : (s0 + c • s1).totalVariation ≪ μ)
    (hq2 : (q • s2).totalVariation ≪ μ)
    (hsum : ((s0 + c • s1) + q • s2).totalVariation ≪ μ)
    (heq : s = (s0 + c • s1) + q • s2)
    (hf : AEStronglyMeasurable f (μ.restrict B))
    (hfb : ∃ C : ℝ, ∀ᵐ x ∂(μ.restrict B), ‖f x‖ ≤ C) :
    DirichletForm.signedIntegralOn s B f =
      DirichletForm.signedIntegralOn s0 B f +
        c * DirichletForm.signedIntegralOn s1 B f +
        q * DirichletForm.signedIntegralOn s2 B f := by
  letI : IsFiniteMeasure μ := ⟨hμ⟩
  have hac (r : SignedMeasure X) (hr : r.totalVariation ≪ μ) :
      r.toJordanDecomposition.posPart ≪ μ ∧
        r.toJordanDecomposition.negPart ≪ μ :=
    (SignedMeasure.totalVariation_absolutelyContinuous_iff r μ).mp hr
  obtain ⟨h0p, h0n⟩ := hac s0 hs0
  obtain ⟨h1p, h1n⟩ := hac s1 hs1
  obtain ⟨h2p, h2n⟩ := hac s2 hs2
  obtain ⟨hc1p, hc1n⟩ := hac (s0 + c • s1) hc1
  obtain ⟨hq2p, hq2n⟩ := hac (q • s2) hq2
  obtain ⟨hsp, hsn⟩ := hac ((s0 + c • s1) + q • s2) hsum
  obtain ⟨hcp, hcn⟩ := hac (c • s1) hc2
  have hqp := hq2p
  have hqn := hq2n
  rw [heq]
  rw [aux_cor_energy_measures_signedIntegralOn_add (s0 + c • s1) (q • s2) μ B f hB
      hc1p hc1n hqp hqn hsp hsn hf hfb]
  rw [aux_cor_energy_measures_signedIntegralOn_add s0 (c • s1) μ B f hB
      h0p h0n hcp hcn hc1p hc1n hf hfb]
  rw [aux_cor_energy_measures_signedIntegralOn_smul c s1 μ B f hB
      h1p h1n hcp hcn hf hfb]
  rw [aux_cor_energy_measures_signedIntegralOn_smul q s2 μ B f hB
      h2p h2n hqp hqn hf hfb]

lemma aux_cor_energy_measures_cross_self_toSignedMeasure
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E) (u : DomainL2 Q)
    (hu : u ∈ E.domain) [hfinite : IsFiniteMeasure (Gamma.measure u)] :
    Gamma.cross u u = (Gamma.measure u).toSignedMeasure := by
  apply VectorMeasure.ext
  intro B hB
  rw [Gamma.cross_self u hu B hB, Measure.toSignedMeasure_apply_measurable hB,
    measureReal_def]

lemma aux_cor_energy_measures_cross_add_self_smul
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E) (u v : DomainL2 Q)
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) (t : ℝ) :
    Gamma.cross (u + t • v) (u + t • v) =
      Gamma.cross u u + (2 * t) • Gamma.cross u v +
        (t ^ 2) • Gamma.cross v v := by
  apply VectorMeasure.ext
  intro B hB
  have htv : t • v ∈ E.domain := E.domain.smul_mem t hv
  rw [Gamma.cross_add_self_apply hu htv B]
  rw [Gamma.cross_smul_right t u hu v hv,
    Gamma.cross_smul_left t hv htv, Gamma.cross_smul_right t v hv v hv,
    VectorMeasure.add_apply, VectorMeasure.add_apply,
    VectorMeasure.smul_apply, VectorMeasure.smul_apply, VectorMeasure.smul_apply]
  simp only [VectorMeasure.add_apply, VectorMeasure.smul_apply, smul_eq_mul]
  ring

lemma aux_cor_energy_measures_gamma_weighted_expand
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E) (u v : DomainL2 Q)
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) (t : ℝ)
    (rho : SpatialCoordinates d → ℝ) (B : Set (SpatialCoordinates d))
    (μ : Measure (SpatialCoordinates d)) (hμ : μ Set.univ < (⊤ : ENNReal))
    (hB : MeasurableSet B)
    (hrho : AEStronglyMeasurable rho (μ.restrict B))
    (hrhoB : ∃ C : ℝ, ∀ᵐ x ∂(μ.restrict B), ‖rho x‖ ≤ C)
    (h0 : (Gamma.cross u u).totalVariation ≪ μ)
    (h1 : (Gamma.cross u v).totalVariation ≪ μ)
    (h2 : (Gamma.cross v v).totalVariation ≪ μ)
    (hc : ((2 * t) • Gamma.cross u v).totalVariation ≪ μ)
    (hq : ((t ^ 2) • Gamma.cross v v).totalVariation ≪ μ)
    (h01 : (Gamma.cross u u + (2 * t) • Gamma.cross u v).totalVariation ≪ μ)
    (hsum : ((Gamma.cross u u + (2 * t) • Gamma.cross u v) +
      (t ^ 2) • Gamma.cross v v).totalVariation ≪ μ) :
    (∫ x in B, rho x ∂Gamma.measure (u + t • v)) =
      (∫ x in B, rho x ∂Gamma.measure u) +
        2 * t * DirichletForm.signedIntegralOn (Gamma.cross u v) B rho +
        t ^ 2 * (∫ x in B, rho x ∂Gamma.measure v) := by
  letI : IsFiniteMeasure μ := ⟨hμ⟩
  letI : IsFiniteMeasure (Gamma.measure u) :=
    ⟨Gamma.measure_univ_lt_top u hu⟩
  letI : IsFiniteMeasure (Gamma.measure v) :=
    ⟨Gamma.measure_univ_lt_top v hv⟩
  have hw : u + t • v ∈ E.domain := E.domain.add_mem hu (E.domain.smul_mem t hv)
  letI : IsFiniteMeasure (Gamma.measure (u + t • v)) :=
    ⟨Gamma.measure_univ_lt_top (u + t • v) hw⟩
  have hcross := aux_cor_energy_measures_cross_add_self_smul E Gamma u v hu hv t
  have hlin := aux_cor_energy_measures_signedIntegralOn_linear_combination
    (Gamma.cross u u) (Gamma.cross u v) (Gamma.cross v v)
    (Gamma.cross (u + t • v) (u + t • v)) μ B rho (2 * t) (t ^ 2) hμ hB
    h0 h1 h2 hc h01 hq hsum hcross hrho hrhoB
  have hselfu := aux_cor_energy_measures_cross_self_toSignedMeasure E Gamma u hu
  have hselfv := aux_cor_energy_measures_cross_self_toSignedMeasure E Gamma v hv
  have hselfw := aux_cor_energy_measures_cross_self_toSignedMeasure E Gamma
    (u + t • v) hw
  have hwu : DirichletForm.signedIntegralOn (Gamma.cross u u) B rho =
      ∫ x in B, rho x ∂Gamma.measure u := by
    rw [hselfu]
    exact aux_cor_energy_measures_signedIntegralOn_toSignedMeasure
      (Gamma.measure u) B hB rho
  have hwv : DirichletForm.signedIntegralOn (Gamma.cross v v) B rho =
      ∫ x in B, rho x ∂Gamma.measure v := by
    rw [hselfv]
    exact aux_cor_energy_measures_signedIntegralOn_toSignedMeasure
      (Gamma.measure v) B hB rho
  have hww : DirichletForm.signedIntegralOn
      (Gamma.cross (u + t • v) (u + t • v)) B rho =
      ∫ x in B, rho x ∂Gamma.measure (u + t • v) := by
    rw [hselfw]
    exact aux_cor_energy_measures_signedIntegralOn_toSignedMeasure
      (Gamma.measure (u + t • v)) B hB rho
  rw [← hww, hlin, hwu, hwv]

lemma aux_cor_energy_measures_weighted_quadratic_expand
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q) (n : ℕ)
    (w z : S.space) (rho : SpatialCoordinates d → ℝ) (t C : ℝ)
    (hrho : AEStronglyMeasurable rho
      (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hrhoC : ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
      ‖rho x‖ ≤ C) :
    (∫ x in (Q : Set (SpatialCoordinates d)), rho x *
      ((a n).val x * ∑ i : Fin d,
        (((w + t • z : SobolevData Q).2 i x) ^ 2))) =
      (∫ x in (Q : Set (SpatialCoordinates d)), rho x *
        ((a n).val x * ∑ i : Fin d, ((w : SobolevData Q).2 i x) ^ 2)) +
      2 * t * (∫ x in (Q : Set (SpatialCoordinates d)), rho x *
        ((a n).val x * ∑ i : Fin d,
          ((w : SobolevData Q).2 i x) * ((z : SobolevData Q).2 i x))) +
      t ^ 2 * (∫ x in (Q : Set (SpatialCoordinates d)), rho x *
        ((a n).val x * ∑ i : Fin d, ((z : SobolevData Q).2 i x) ^ 2)) := by
  let μ : Measure (SpatialCoordinates d) := volume.restrict (Q : Set (SpatialCoordinates d))
  let gw : SpatialCoordinates d → ℝ := fun x => (a n).val x * ∑ i : Fin d,
    ((w : SobolevData Q).2 i x) ^ 2
  let gz : SpatialCoordinates d → ℝ := fun x => (a n).val x * ∑ i : Fin d,
    ((z : SobolevData Q).2 i x) ^ 2
  let gc : SpatialCoordinates d → ℝ := fun x => (a n).val x * ∑ i : Fin d,
    ((w : SobolevData Q).2 i x) * ((z : SobolevData Q).2 i x)
  have hw : Integrable gw μ := by
    simpa [gw, μ] using aux_cor_energy_measures_energy_integrable S a n w
  have hz : Integrable gz μ := by
    simpa [gz, μ] using aux_cor_energy_measures_energy_integrable S a n z
  have hc : Integrable gc μ := by
    have hraw : Integrable (fun x => ∑ i : Fin d, (a n).val x *
        (((w : SobolevData Q).2 i x) * ((z : SobolevData Q).2 i x))) μ := by
      apply integrable_finset_sum Finset.univ
      intro i hi
      exact integrable_weighted_coordinates (a n).val
        (sobolevGradient (w : SobolevData Q))
        (sobolevGradient (z : SobolevData Q)) i
    apply hraw.congr
    filter_upwards [] with x
    dsimp [gc]
    rw [Finset.mul_sum]
  have hwi : Integrable (fun x => rho x * gw x) μ := hw.bdd_mul hrho hrhoC
  have hzi : Integrable (fun x => rho x * gz x) μ := hz.bdd_mul hrho hrhoC
  have hci : Integrable (fun x => rho x * gc x) μ := hc.bdd_mul hrho hrhoC
  have hti : Integrable (fun x => 2 * t * (rho x * gc x)) μ :=
    hci.const_mul (2 * t)
  have htz : Integrable (fun x => t ^ 2 * (rho x * gz x)) μ :=
    hzi.const_mul (t ^ 2)
  have hcoord : ∀ i : Fin d, ∀ᵐ x ∂μ,
      ((w + t • z : SobolevData Q).2 i x) =
        (w : SobolevData Q).2 i x + t * (z : SobolevData Q).2 i x := by
    intro i
    change ⇑((w : SobolevData Q).2 i + t • (z : SobolevData Q).2 i) =ᵐ[μ] _
    filter_upwards [Lp.coeFn_add ((w : SobolevData Q).2 i)
        (t • (z : SobolevData Q).2 i),
      Lp.coeFn_smul t ((z : SobolevData Q).2 i)] with x hx hz
    rw [hx, Pi.add_apply, hz]
    simp only [Pi.smul_apply, smul_eq_mul]
  have hcoordall : ∀ᵐ x ∂μ, ∀ i : Fin d,
      ((w + t • z : SobolevData Q).2 i x) =
        (w : SobolevData Q).2 i x + t * (z : SobolevData Q).2 i x :=
    ae_all_iff.mpr hcoord
  have hpoint : ∀ᵐ x ∂μ, rho x * ((a n).val x * ∑ i : Fin d,
      (((w + t • z : SobolevData Q).2 i x) ^ 2)) =
      rho x * gw x + 2 * t * (rho x * gc x) + t ^ 2 * (rho x * gz x) := by
    filter_upwards [hcoordall] with x hx
    have hsum : (∑ i : Fin d, ((w + t • z : SobolevData Q).2 i x) ^ 2) =
        ∑ i : Fin d, ((w : SobolevData Q).2 i x +
          t * (z : SobolevData Q).2 i x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hx i]
    rw [hsum]
    dsimp [gw, gc, gz]
    have hpoly : (∑ i : Fin d, ((w : SobolevData Q).2 i x +
          t * (z : SobolevData Q).2 i x) ^ 2) =
        (∑ i : Fin d, ((w : SobolevData Q).2 i x) ^ 2) +
          2 * t * (∑ i : Fin d, ((w : SobolevData Q).2 i x) *
            ((z : SobolevData Q).2 i x)) +
          t ^ 2 * (∑ i : Fin d, ((z : SobolevData Q).2 i x) ^ 2) := by
      calc
        (∑ i : Fin d, ((w : SobolevData Q).2 i x +
            t * (z : SobolevData Q).2 i x) ^ 2) =
            ∑ i : Fin d, (((w : SobolevData Q).2 i x) ^ 2 +
              2 * t * (((w : SobolevData Q).2 i x) *
                ((z : SobolevData Q).2 i x)) +
              t ^ 2 * ((z : SobolevData Q).2 i x) ^ 2) := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
        _ = (∑ i : Fin d, ((w : SobolevData Q).2 i x) ^ 2) +
              (∑ i : Fin d, 2 * t * (((w : SobolevData Q).2 i x) *
                ((z : SobolevData Q).2 i x))) +
              (∑ i : Fin d, t ^ 2 * ((z : SobolevData Q).2 i x) ^ 2) := by
                rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        _ = _ := by
                rw [← Finset.mul_sum, ← Finset.mul_sum]
    rw [hpoly]
    calc
      rho x * ((a n).val x *
          ((∑ i : Fin d, ((w : SobolevData Q).2 i x) ^ 2) +
            2 * t * (∑ i : Fin d, ((w : SobolevData Q).2 i x) *
              ((z : SobolevData Q).2 i x)) +
            t ^ 2 * (∑ i : Fin d, ((z : SobolevData Q).2 i x) ^ 2))) =
          rho x * ((a n).val x * ∑ i : Fin d,
              ((w : SobolevData Q).2 i x) ^ 2) +
            2 * t * (rho x * ((a n).val x * ∑ i : Fin d,
              ((w : SobolevData Q).2 i x) * ((z : SobolevData Q).2 i x))) +
            t ^ 2 * (rho x * ((a n).val x * ∑ i : Fin d,
              ((z : SobolevData Q).2 i x) ^ 2)) := by ring
      _ = _ := by
        congr 1
  calc
    (∫ x in (Q : Set (SpatialCoordinates d)), rho x *
      ((a n).val x * ∑ i : Fin d,
        (((w + t • z : SobolevData Q).2 i x) ^ 2))) =
        ∫ x, rho x * gw x + 2 * t * (rho x * gc x) +
          t ^ 2 * (rho x * gz x) ∂μ := by
            apply integral_congr_ae
            exact hpoint
    _ = (∫ x, rho x * gw x ∂μ) +
        (∫ x, 2 * t * (rho x * gc x) ∂μ) +
        ∫ x, t ^ 2 * (rho x * gz x) ∂μ := by
          calc
            (∫ x, (rho x * gw x + 2 * t * (rho x * gc x)) +
              t ^ 2 * (rho x * gz x) ∂μ) =
                (∫ x, rho x * gw x + 2 * t * (rho x * gc x) ∂μ) +
                  ∫ x, t ^ 2 * (rho x * gz x) ∂μ :=
              integral_add (hwi.add hti) htz
            _ = _ := by rw [integral_add hwi hti]
    _ = (∫ x, rho x * gw x ∂μ) +
        2 * t * (∫ x, rho x * gc x ∂μ) +
        t ^ 2 * (∫ x, rho x * gz x ∂μ) := by
          rw [integral_const_mul, integral_const_mul]
    _ = _ := by rfl


lemma aux_cor_energy_measures_cross_abs_bound
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q) (n : ℕ)
    (w z : S.space) (rho : SpatialCoordinates d → ℝ) (C : ℝ)
    (hrho : AEStronglyMeasurable rho
      (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hrhoC : ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
      ‖rho x‖ ≤ C) (hC : 0 ≤ C) :
    |∫ x in (Q : Set (SpatialCoordinates d)), rho x *
        ((a n).val x * ∑ i : Fin d,
          ((w : SobolevData Q).2 i x) * ((z : SobolevData Q).2 i x))| ≤
      C / 2 * (responseForm S (a n) w w + responseForm S (a n) z z) := by
  let μ : Measure (SpatialCoordinates d) := volume.restrict (Q : Set (SpatialCoordinates d))
  let g : SpatialCoordinates d → ℝ := fun x => (a n).val x * ∑ i : Fin d,
    ((w : SobolevData Q).2 i x) * ((z : SobolevData Q).2 i x)
  let gw : SpatialCoordinates d → ℝ := fun x => (a n).val x * ∑ i : Fin d,
    ((w : SobolevData Q).2 i x) ^ 2
  let gz : SpatialCoordinates d → ℝ := fun x => (a n).val x * ∑ i : Fin d,
    ((z : SobolevData Q).2 i x) ^ 2
  have hg : Integrable g μ := by
    have hi : ∀ i : Fin d, Integrable (fun x => (a n).val x *
        (((w : SobolevData Q).2 i x) * ((z : SobolevData Q).2 i x))) μ := by
      intro i
      exact integrable_weighted_coordinates (a n).val
        (sobolevGradient (w : SobolevData Q))
        (sobolevGradient (z : SobolevData Q)) i
    have hsum : Integrable (fun x => ∑ i : Fin d,
        (a n).val x * (((w : SobolevData Q).2 i x) *
          ((z : SobolevData Q).2 i x))) μ := by
      apply integrable_finset_sum Finset.univ
      intro i hi
      exact integrable_weighted_coordinates (a n).val
        (sobolevGradient (w : SobolevData Q))
        (sobolevGradient (z : SobolevData Q)) i
    apply hsum.congr
    filter_upwards [] with x
    dsimp [g]
    rw [Finset.mul_sum]
  have hgw : Integrable gw μ := by
    simpa [gw, μ] using aux_cor_energy_measures_energy_integrable S a n w
  have hgz : Integrable gz μ := by
    simpa [gz, μ] using aux_cor_energy_measures_energy_integrable S a n z
  have hrg : Integrable (fun x => rho x * g x) μ := hg.bdd_mul hrho hrhoC
  have hright : Integrable (fun x => C / 2 * (gw x + gz x)) μ := by
    exact (hgw.add hgz).const_mul (C / 2)
  have hpoint : ∀ᵐ x ∂μ, ‖rho x * g x‖ ≤ C / 2 * (gw x + gz x) := by
    obtain ⟨c, hc, hca⟩ := (a n).property
    have ha : ∀ᵐ x ∂μ, 0 ≤ (a n).val x := hca.mono (fun x hx => le_trans hc.le hx)
    filter_upwards [hrhoC, ha] with x hxrho hxa
    have hsum : |g x| ≤ (gw x + gz x) / 2 := by
      have hterm : ∀ i : Fin d,
          |(a n).val x * (((w : SobolevData Q).2 i x) *
            ((z : SobolevData Q).2 i x))| ≤
            ((a n).val x * (((w : SobolevData Q).2 i x) ^ 2 +
              ((z : SobolevData Q).2 i x) ^ 2)) / 2 := by
        intro i
        have hyoung : 2 * |((w : SobolevData Q).2 i x) *
            ((z : SobolevData Q).2 i x)| ≤
            ((w : SobolevData Q).2 i x) ^ 2 +
              ((z : SobolevData Q).2 i x) ^ 2 := by
          by_cases h : 0 ≤ ((w : SobolevData Q).2 i x) *
              ((z : SobolevData Q).2 i x)
          · rw [abs_of_nonneg h]
            nlinarith [sq_nonneg (((w : SobolevData Q).2 i x) -
              ((z : SobolevData Q).2 i x))]
          · have h' : ((w : SobolevData Q).2 i x) *
                ((z : SobolevData Q).2 i x) ≤ 0 := le_of_not_ge h
            rw [abs_of_nonpos h']
            nlinarith [sq_nonneg (((w : SobolevData Q).2 i x) +
              ((z : SobolevData Q).2 i x))]
        calc
          |(a n).val x * (((w : SobolevData Q).2 i x) *
              ((z : SobolevData Q).2 i x))| =
              (a n).val x * |((w : SobolevData Q).2 i x) *
                ((z : SobolevData Q).2 i x)| := by
                  rw [abs_mul, abs_of_nonneg hxa]
          _ ≤ (a n).val x * ((((w : SobolevData Q).2 i x) ^ 2 +
              ((z : SobolevData Q).2 i x) ^ 2) / 2) := by
                exact mul_le_mul_of_nonneg_left (by nlinarith [hyoung]) hxa
          _ = ((a n).val x * (((w : SobolevData Q).2 i x) ^ 2 +
              ((z : SobolevData Q).2 i x) ^ 2)) / 2 := by ring
      calc
        |g x| ≤ ∑ i : Fin d, |(a n).val x *
            (((w : SobolevData Q).2 i x) * ((z : SobolevData Q).2 i x))| := by
          rw [show g x = ∑ i : Fin d, (a n).val x *
              (((w : SobolevData Q).2 i x) * ((z : SobolevData Q).2 i x)) by
            dsimp [g]
            rw [Finset.mul_sum]]
          exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin d, ((a n).val x *
            (((w : SobolevData Q).2 i x) ^ 2 +
              ((z : SobolevData Q).2 i x) ^ 2)) / 2 :=
          Finset.sum_le_sum fun i _ => hterm i
        _ = (gw x + gz x) / 2 := by
          dsimp [gw, gz]
          simp only [div_eq_mul_inv, mul_add]
          rw [← Finset.sum_mul, Finset.sum_add_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum]
    have hgw0 : 0 ≤ gw x := by
      dsimp [gw]
      positivity
    have hgz0 : 0 ≤ gz x := by
      dsimp [gz]
      positivity
    have hsum0 : 0 ≤ (gw x + gz x) / 2 := by positivity
    calc
      ‖rho x * g x‖ = |rho x| * |g x| := by simp [Real.norm_eq_abs, abs_mul]
      _ ≤ C * ((gw x + gz x) / 2) :=
        mul_le_mul hxrho hsum (abs_nonneg _) hC
      _ = C / 2 * (gw x + gz x) := by ring
  calc
    |∫ x in (Q : Set (SpatialCoordinates d)), rho x *
        ((a n).val x * ∑ i : Fin d,
          ((w : SobolevData Q).2 i x) * ((z : SobolevData Q).2 i x))| =
        |∫ x, rho x * g x ∂μ| := by rfl
    _ ≤ ∫ x, ‖rho x * g x‖ ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, C / 2 * (gw x + gz x) ∂μ :=
      integral_mono_ae hrg.norm hright hpoint
    _ = C / 2 * (∫ x, gw x ∂μ + ∫ x, gz x ∂μ) := by
      rw [integral_const_mul, integral_add hgw hgz]
        _ = C / 2 * (responseForm S (a n) w w + responseForm S (a n) z z) := by
      have hw : (∫ x, gw x ∂μ) = responseForm S (a n) w w := by
        have hw' := aux_cor_energy_measures_energy_integral S a n w
        dsimp [gw, μ]
        exact hw'
      have hz : (∫ x, gz x ∂μ) = responseForm S (a n) z z := by
        have hz' := aux_cor_energy_measures_energy_integral S a n z
        dsimp [gz, μ]
        exact hz'
      calc
        C / 2 * (∫ x, gw x ∂μ + ∫ x, gz x ∂μ) =
            C / 2 * (responseForm S (a n) w w + ∫ x, gz x ∂μ) :=
          congrArg (fun r : ℝ => C / 2 * (r + ∫ x, gz x ∂μ)) hw
        _ = C / 2 * (responseForm S (a n) w w + responseForm S (a n) z z) :=
          congrArg (fun r : ℝ => C / 2 * (responseForm S (a n) w w + r)) hz

lemma aux_cor_energy_measures_totalVariation_add
    {X : Type*} [MeasurableSpace X]
    (s t : SignedMeasure X) (μ : Measure X)
    (hs : s.totalVariation ≪ μ) (ht : t.totalVariation ≪ μ) :
    (s + t).totalVariation ≪ μ := by
  have hs' : s ≪ᵥ μ.toENNRealVectorMeasure := by
    rw [SignedMeasure.absolutelyContinuous_ennreal_iff]
    simpa only [VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure] using hs
  have ht' : t ≪ᵥ μ.toENNRealVectorMeasure := by
    rw [SignedMeasure.absolutelyContinuous_ennreal_iff]
    simpa only [VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure] using ht
  have hst' : (s + t) ≪ᵥ μ.toENNRealVectorMeasure := hs'.add ht'
  have hst :=
    (SignedMeasure.absolutelyContinuous_ennreal_iff
      (s + t) μ.toENNRealVectorMeasure).mp hst'
  simpa only [VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure] using hst

lemma aux_cor_energy_measures_totalVariation_smul
    {X : Type*} [MeasurableSpace X]
    (c : ℝ) (s : SignedMeasure X) (μ : Measure X)
    (hs : s.totalVariation ≪ μ) :
    (c • s).totalVariation ≪ μ := by
  have hs' : s ≪ᵥ μ.toENNRealVectorMeasure := by
    rw [SignedMeasure.absolutelyContinuous_ennreal_iff]
    simpa only [VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure] using hs
  have hcs' : (c • s) ≪ᵥ μ.toENNRealVectorMeasure := hs'.smul
  have hcs :=
    (SignedMeasure.absolutelyContinuous_ennreal_iff
      (c • s) μ.toENNRealVectorMeasure).mp hcs'
  simpa only [VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure] using hcs

lemma aux_cor_energy_measures_limitDomain_iff
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) (w : DomainL2 Q) :
    w ∈ limitFormDomain G ↔ limitFormEnergy G w < (⊤ : EReal) :=
  Iff.rfl

lemma aux_cor_energy_measures_limitEnergy_ne_bot
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) (w : DomainL2 Q) :
    limitFormEnergy G w ≠ (⊥ : EReal) := by
  exact ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe (0 : ℝ))
    (limitFormEnergy_nonneg G w))

def aux_cor_energy_measures_crossSeq
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q)
    (uN vN : ℕ → S.space) (rho : SpatialCoordinates d → ℝ) (n : ℕ) : ℝ :=
  ∫ x in (Q : Set (SpatialCoordinates d)), rho x *
    ((a n).val x * ∑ i : Fin d,
      ((uN n : SobolevData Q).2 i x) * ((vN n : SobolevData Q).2 i x))

def aux_cor_energy_measures_crossLimit
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E) (u v : DomainL2 Q)
    (rho : SpatialCoordinates d → ℝ) : ℝ :=
  DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ rho

lemma aux_cor_energy_measures_cross_Q_eq_univ
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E) (u v : DomainL2 Q)
    (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (hGammaQ : ∀ w : DomainL2 Q, w ∈ E.domain →
      Gamma.measure w (Q : Set (SpatialCoordinates d))ᶜ = 0)
    (rho : SpatialCoordinates d → ℝ) :
    DirichletForm.signedIntegralOn (Gamma.cross u v)
        (Q : Set (SpatialCoordinates d)) rho =
      DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ rho := by
  let μuv : Measure (SpatialCoordinates d) := Gamma.measure u + Gamma.measure v
  have hμu : Gamma.measure u ≪ μuv := by
    dsimp [μuv]
    exact Measure.AbsolutelyContinuous.add_right
      (Measure.AbsolutelyContinuous.rfl) _
  have hμv : Gamma.measure v ≪ μuv := by
    dsimp [μuv]
    simpa [add_comm] using
      (Measure.AbsolutelyContinuous.add_right
        (Measure.AbsolutelyContinuous.rfl : Gamma.measure v ≪ Gamma.measure v)
        (Gamma.measure u))
  obtain ⟨hpos, hneg⟩ :=
    aux_cor_energy_measures_cross_absolutelyContinuous E Gamma u v hu hv μuv hμu hμv
  have hμQ : μuv (Q : Set (SpatialCoordinates d))ᶜ = 0 := by
    dsimp [μuv]
    rw [hGammaQ u hu, hGammaQ v hv, add_zero]
  exact aux_cor_energy_measures_signedIntegralOn_Q_eq_univ
    (Gamma.cross u v) μuv (Q : Set (SpatialCoordinates d)) Q.isOpen.measurableSet
    hpos hneg hμQ rho

lemma aux_cor_energy_measures_crossSeq_add
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q) (n : ℕ)
    (uN vN : ℕ → S.space) (f g : SpatialCoordinates d → ℝ)
    (hf : AEStronglyMeasurable f
      (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hg : AEStronglyMeasurable g
      (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hfb : ∃ C : ℝ, ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
      ‖f x‖ ≤ C)
    (hgb : ∃ C : ℝ, ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
      ‖g x‖ ≤ C) :
    aux_cor_energy_measures_crossSeq S a uN vN (fun x => f x + g x) n =
      aux_cor_energy_measures_crossSeq S a uN vN f n +
        aux_cor_energy_measures_crossSeq S a uN vN g n := by
  let μ : Measure (SpatialCoordinates d) :=
    volume.restrict (Q : Set (SpatialCoordinates d))
  let k : SpatialCoordinates d → ℝ := fun x =>
    (a n).val x * ∑ i : Fin d,
      ((uN n : SobolevData Q).2 i x) * ((vN n : SobolevData Q).2 i x)
  have hk : Integrable k μ := by
    have hi : ∀ i : Fin d, Integrable (fun x => (a n).val x *
        (((uN n : SobolevData Q).2 i x) * ((vN n : SobolevData Q).2 i x))) μ := by
      intro i
      exact integrable_weighted_coordinates (a n).val
        (sobolevGradient (uN n : SobolevData Q))
        (sobolevGradient (vN n : SobolevData Q)) i
    have hs : Integrable (fun x => ∑ i : Fin d, (a n).val x *
        (((uN n : SobolevData Q).2 i x) * ((vN n : SobolevData Q).2 i x))) μ := by
      apply integrable_finset_sum Finset.univ
      intro i hi'
      exact hi i
    apply hs.congr
    filter_upwards [] with x
    dsimp [k]
    rw [Finset.mul_sum]
  obtain ⟨Cf, hCf⟩ := hfb
  obtain ⟨Cg, hCg⟩ := hgb
  have hfk : Integrable (fun x => f x * k x) μ := hk.bdd_mul hf hCf
  have hgk : Integrable (fun x => g x * k x) μ := hk.bdd_mul hg hCg
  dsimp [aux_cor_energy_measures_crossSeq, μ, k]
  rw [← integral_add hfk hgk]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

lemma aux_cor_energy_measures_cross_signedIntegral_add
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E) (u v : DomainL2 Q)
    (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (hGammaQ : ∀ w : DomainL2 Q, w ∈ E.domain →
      Gamma.measure w (Q : Set (SpatialCoordinates d))ᶜ = 0)
    (f g : SpatialCoordinates d → ℝ)
    (hf : ContinuousOn f (closure (Q : Set (SpatialCoordinates d))))
    (hg : ContinuousOn g (closure (Q : Set (SpatialCoordinates d))))
    (hfb : ∃ C : ℝ, ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ‖f x‖ ≤ C)
    (hgb : ∃ C : ℝ, ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ‖g x‖ ≤ C) :
    DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ (fun x => f x + g x) =
      DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ f +
        DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ g := by
  have hQm : MeasurableSet (Q : Set (SpatialCoordinates d)) := Q.isOpen.measurableSet
  let μ : Measure (SpatialCoordinates d) := Gamma.measure u + Gamma.measure v
  have hμ : μ Set.univ < (⊤ : ENNReal) := by
    dsimp [μ]
    exact ENNReal.add_lt_top.mpr ⟨Gamma.measure_univ_lt_top u hu,
      Gamma.measure_univ_lt_top v hv⟩
  have hμu : Gamma.measure u ≪ μ := by
    dsimp [μ]
    exact Measure.AbsolutelyContinuous.add_right
      (Measure.AbsolutelyContinuous.rfl) _
  have hμv : Gamma.measure v ≪ μ := by
    dsimp [μ]
    simpa [add_comm] using
      (Measure.AbsolutelyContinuous.add_right
        (Measure.AbsolutelyContinuous.rfl : Gamma.measure v ≪ Gamma.measure v)
        (Gamma.measure u))
  obtain ⟨hpos, hneg⟩ :=
    aux_cor_energy_measures_cross_absolutelyContinuous E Gamma u v hu hv μ hμu hμv
  have hμQ : μ (Q : Set (SpatialCoordinates d))ᶜ = 0 := by
    dsimp [μ]
    rw [hGammaQ u hu, hGammaQ v hv, add_zero]
  have hmeas (F : SpatialCoordinates d → ℝ)
      (hF : ContinuousOn F (closure (Q : Set (SpatialCoordinates d)))) :
      AEStronglyMeasurable F (μ.restrict (Q : Set (SpatialCoordinates d))) := by
    exact (hF.mono subset_closure).aestronglyMeasurable hQm
  have hbound (F : SpatialCoordinates d → ℝ) (hF : ContinuousOn F
      (closure (Q : Set (SpatialCoordinates d))))
      (hFB : ∃ C : ℝ, ∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
        ‖F x‖ ≤ C) :
      ∃ C : ℝ, ∀ᵐ x ∂(μ.restrict (Q : Set (SpatialCoordinates d))), ‖F x‖ ≤ C := by
    obtain ⟨C, hC⟩ := hFB
    refine ⟨C, ?_⟩
    filter_upwards [ae_restrict_mem hQm] with x hx
    exact hC x (subset_closure hx)
  have hfg : ContinuousOn (fun x => f x + g x)
      (closure (Q : Set (SpatialCoordinates d))) := hf.add hg
  obtain ⟨Cf, hCf⟩ := hbound f hf hfb
  obtain ⟨Cg, hCg⟩ := hbound g hg hgb
  have hfgb : ∃ C : ℝ, ∀ᵐ x ∂(μ.restrict (Q : Set (SpatialCoordinates d))),
      ‖(f x + g x)‖ ≤ C := by
    refine ⟨Cf + Cg, ?_⟩
    filter_upwards [hCf, hCg] with x hfx hgx
    exact (norm_add_le _ _).trans (add_le_add hfx hgx)
  have hfi : Integrable (fun x => (Gamma.cross u v).rnDeriv μ x * f x)
      (μ.restrict (Q : Set (SpatialCoordinates d))) :=
    (SignedMeasure.integrable_rnDeriv (Gamma.cross u v) μ).restrict.mul_bdd
      (hmeas f hf) hCf
  have hgi : Integrable (fun x => (Gamma.cross u v).rnDeriv μ x * g x)
      (μ.restrict (Q : Set (SpatialCoordinates d))) :=
    (SignedMeasure.integrable_rnDeriv (Gamma.cross u v) μ).restrict.mul_bdd
      (hmeas g hg) hCg
  have hQf := aux_cor_energy_measures_signedIntegralOn_Q_eq_univ
    (Gamma.cross u v) μ (Q : Set (SpatialCoordinates d)) hQm hpos hneg hμQ f
  have hQg := aux_cor_energy_measures_signedIntegralOn_Q_eq_univ
    (Gamma.cross u v) μ (Q : Set (SpatialCoordinates d)) hQm hpos hneg hμQ g
  have hQfg := aux_cor_energy_measures_signedIntegralOn_Q_eq_univ
    (Gamma.cross u v) μ (Q : Set (SpatialCoordinates d)) hQm hpos hneg hμQ
    (fun x => f x + g x)
  rw [← hQfg, ← hQf, ← hQg]
  rw [aux_cor_energy_measures_signedIntegralOn_rnDeriv (Gamma.cross u v) μ
      (Q : Set (SpatialCoordinates d)) (fun x => f x + g x) hμ hQm hpos hneg
      (hmeas _ hfg) hfgb]
  rw [aux_cor_energy_measures_signedIntegralOn_rnDeriv (Gamma.cross u v) μ
      (Q : Set (SpatialCoordinates d)) f hμ hQm hpos hneg (hmeas f hf)
      ⟨Cf, hCf⟩]
  rw [aux_cor_energy_measures_signedIntegralOn_rnDeriv (Gamma.cross u v) μ
      (Q : Set (SpatialCoordinates d)) g hμ hQm hpos hneg (hmeas g hg)
      ⟨Cg, hCg⟩]
  rw [← integral_add hfi hgi]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

lemma aux_cor_energy_measures_clause_c_extend
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (hQcube : Q = centeredCube z0 R hR)
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q)
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E)
    (u v : DomainL2 Q) (uN vN : ℕ → S.space)
    (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (hGammaQ : ∀ w : DomainL2 Q, w ∈ E.domain →
      Gamma.measure w (Q : Set (SpatialCoordinates d))ᶜ = 0)
    (hpositive : ∀ (rho : SpatialCoordinates d → ℝ),
      ContinuousOn rho (closure (Q : Set (SpatialCoordinates d))) →
      (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), 0 < rho x) →
      Tendsto (aux_cor_energy_measures_crossSeq S a uN vN rho) atTop
        (𝓝 (aux_cor_energy_measures_crossLimit E Gamma u v rho)))
    (φ : SpatialCoordinates d → ℝ)
    (hφ : ContinuousOn φ (closure (Q : Set (SpatialCoordinates d)))) :
    Tendsto (fun n => ∫ x in (Q : Set (SpatialCoordinates d)), φ x *
      ((a n).val x * ∑ i : Fin d,
        ((uN n : SobolevData Q).2 i x) * ((vN n : SobolevData Q).2 i x))) atTop
      (𝓝 (DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ φ)) := by
  let crossSeq : (SpatialCoordinates d → ℝ) → ℕ → ℝ :=
    aux_cor_energy_measures_crossSeq S a uN vN
  let crossLimit : (SpatialCoordinates d → ℝ) → ℝ :=
    aux_cor_energy_measures_crossLimit E Gamma u v
  have hcompactφ : IsCompact (closure (Q : Set (SpatialCoordinates d))) := by
    rw [hQcube]
    exact (centeredCube_isBounded z0 hR).isCompact_closure
  obtain ⟨Mφ, hMφ⟩ := hcompactφ.exists_bound_of_continuousOn hφ
  let K : ℝ := max Mφ 0 + 1
  have hK : 0 < K := by
    dsimp [K]
    linarith [le_max_right Mφ 0]
  have hφKcont : ContinuousOn (fun x => φ x + K)
      (closure (Q : Set (SpatialCoordinates d))) := hφ.add continuousOn_const
  have hφKpos : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
      0 < φ x + K := by
    intro x hx
    have hnorm : |φ x| ≤ Mφ := by
      simpa [Real.norm_eq_abs] using hMφ x hx
    have hlow : -Mφ ≤ φ x := (abs_le.mp hnorm).1
    dsimp [K]
    linarith [le_max_left Mφ 0]
  have hφbound : ∃ C : ℝ, ∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
      ‖φ x‖ ≤ C := ⟨Mφ, hMφ⟩
  have hφKbound : ∃ C : ℝ, ∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
      ‖φ x + K‖ ≤ C := by
    refine ⟨Mφ + K, ?_⟩
    intro x hx
    have hKnorm : ‖K‖ = K := by
      simp only [Real.norm_eq_abs, abs_of_pos hK]
    calc
      ‖φ x + K‖ ≤ ‖φ x‖ + ‖K‖ := norm_add_le _ _
      _ ≤ Mφ + K := by rw [hKnorm]; exact add_le_add (hMφ x hx) le_rfl
  have hKbound : ∃ C : ℝ, ∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
      ‖(fun _ : SpatialCoordinates d => K) x‖ ≤ C := by
    refine ⟨K, ?_⟩
    intro x hx
    change ‖K‖ ≤ K
    exact le_of_eq (by simp [Real.norm_eq_abs, abs_of_pos hK])
  have hplus := hpositive (fun x => φ x + K) hφKcont hφKpos
  have hconst := hpositive (fun _ : SpatialCoordinates d => K)
    continuousOn_const (fun x hx => hK)
  have hseq : ∀ n : ℕ,
      crossSeq (fun x => φ x + K) n =
        crossSeq φ n + crossSeq (fun _ : SpatialCoordinates d => K) n := by
    intro n
    have hf : AEStronglyMeasurable φ
        (volume.restrict (Q : Set (SpatialCoordinates d))) :=
      (hφ.mono subset_closure).aestronglyMeasurable Q.isOpen.measurableSet
    have hg : AEStronglyMeasurable (fun _ : SpatialCoordinates d => K)
        (volume.restrict (Q : Set (SpatialCoordinates d))) :=
      measurable_const.aestronglyMeasurable
    have hfae : ∃ C : ℝ, ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
        ‖φ x‖ ≤ C := by
      refine ⟨Mφ, ?_⟩
      filter_upwards [ae_restrict_mem Q.isOpen.measurableSet] with x hx
      exact hMφ x (subset_closure hx)
    have hgae : ∃ C : ℝ, ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
        ‖(fun _ : SpatialCoordinates d => K) x‖ ≤ C := by
      refine ⟨K, ?_⟩
      filter_upwards [] with x
      change ‖K‖ ≤ K
      exact le_of_eq (by simp [Real.norm_eq_abs, abs_of_pos hK])
    have hh := aux_cor_energy_measures_crossSeq_add (d := d) (Q := Q)
      S a n uN vN φ (fun _ : SpatialCoordinates d => K) hf hg hfae hgae
    simpa [crossSeq] using hh
  have hlimadd := aux_cor_energy_measures_cross_signedIntegral_add (d := d) (Q := Q)
    E Gamma u v hu hv hGammaQ φ (fun _ : SpatialCoordinates d => K)
      hφ continuousOn_const hφbound hKbound
  have hdiff := hplus.sub hconst
  have hlimdiff : DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ φ =
      DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ (fun x => φ x + K) -
        DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ
          (fun _ : SpatialCoordinates d => K) := by
    calc
      DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ φ =
          DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ φ +
            DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ
              (fun _ : SpatialCoordinates d => K) -
            DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ
              (fun _ : SpatialCoordinates d => K) := by ring
      _ = DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ
            (fun x => φ x + K) -
          DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ
            (fun _ : SpatialCoordinates d => K) := by rw [hlimadd]
  have hlimdiff' : aux_cor_energy_measures_crossLimit E Gamma u v φ =
      aux_cor_energy_measures_crossLimit E Gamma u v (fun x => φ x + K) -
        aux_cor_energy_measures_crossLimit E Gamma u v
          (fun _ : SpatialCoordinates d => K) := by
    dsimp [aux_cor_energy_measures_crossLimit]
    exact hlimdiff
  have hdiff' : Tendsto (fun n => crossSeq (fun x => φ x + K) n -
      crossSeq (fun _ : SpatialCoordinates d => K) n) atTop
      (𝓝 (crossLimit (fun x => φ x + K) -
        crossLimit (fun _ : SpatialCoordinates d => K))) := by
    exact hdiff
  have hlimdiff'' : crossLimit φ = crossLimit (fun x => φ x + K) -
      crossLimit (fun _ : SpatialCoordinates d => K) := by
    dsimp [crossLimit]
    exact hlimdiff
  rw [← hlimdiff''] at hdiff'
  have hfun : (fun n => crossSeq (fun x => φ x + K) n -
      crossSeq (fun _ : SpatialCoordinates d => K) n) = crossSeq φ := by
    funext n
    rw [hseq n]
    ring
  rw [hfun] at hdiff'
  change Tendsto (crossSeq φ) atTop
    (𝓝 (DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ φ))
  exact hdiff'


lemma aux_cor_energy_measures_clause_c
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (hQcube : Q = centeredCube z0 R hR)
    (S : ResponseSpace Q)
    (a : ℕ → PositiveCoefficient Q)
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hEform : ∀ w : DomainL2 Q, E.energy w = limitFormEnergy G w)
    (Gamma : DirichletForm.EnergyMeasure E)
    (hGammaQ : ∀ w : DomainL2 Q, w ∈ E.domain →
      Gamma.measure w (Q : Set (SpatialCoordinates d))ᶜ = 0)
    (hweighted : ∀ rho : SpatialCoordinates d → ℝ,
      ContinuousOn rho (closure (Q : Set (SpatialCoordinates d))) →
      (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), 0 < rho x) →
      ∀ sigma : ℕ → ℕ, StrictMono sigma →
      ∀ (wN : ℕ → S.space) (w : DomainL2 Q), w ∈ limitFormDomain G →
      (∀ f : DomainL2 Q,
        Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      (((∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(Gamma.measure w)) : ℝ)
          : EReal) ≤
        liminf (fun n =>
          (((∫ x in (Q : Set (SpatialCoordinates d)), rho x *
              ((a (sigma n)).val x * ∑ i : Fin d,
                ((wN (sigma n) : SobolevData Q).2 i x) ^ 2)) : ℝ) : EReal)) atTop)
    (hlower : ∀ (wN : ℕ → S.space) (w : DomainL2 Q),
      (∀ f : DomainL2 Q,
        Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      limitFormEnergy G w ≤
        liminf (fun n => ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal)) atTop)
    (hrecover :
      ∀ (w : DomainL2 Q) (wN : ℕ → S.space), w ∈ limitFormDomain G →
        Tendsto (fun n => ((wN n).val.1,
          ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal))) atTop
          (𝓝 (w, limitFormEnergy G w)) →
        ∀ ψ : SpatialCoordinates d → ℝ,
          ContinuousOn ψ (closure (Q : Set (SpatialCoordinates d))) →
          Tendsto (fun n => ∫ x, ψ x ∂(((volume.restrict
            (Q : Set (SpatialCoordinates d)))).withDensity
            (fun y => ENNReal.ofReal ((a n).val y *
              ∑ i : Fin d, ((wN n : SobolevData Q).2 i y) ^ 2)))) atTop
            (𝓝 (∫ x, ψ x ∂(Gamma.measure w)))) :
    (∀ (u v : DomainL2 Q) (uN vN : ℕ → S.space) (E0 : ℝ),
      Tendsto (fun n => (uN n).val.1) atTop (𝓝 u) →
      (∀ n : ℕ, responseForm S (a n) (uN n) (uN n) ≤ E0) →
      v ∈ limitFormDomain G →
      Tendsto (fun n => ((vN n).val.1,
        ((responseForm S (a n) (vN n) (vN n) : ℝ) : EReal))) atTop
        (𝓝 (v, limitFormEnergy G v)) →
      ∀ φ : SpatialCoordinates d → ℝ,
        ContinuousOn φ (closure (Q : Set (SpatialCoordinates d))) →
        Tendsto (fun n => ∫ x in (Q : Set (SpatialCoordinates d)), φ x *
          ((a n).val x * ∑ i : Fin d,
            ((uN n : SobolevData Q).2 i x) * ((vN n : SobolevData Q).2 i x)))
          atTop
          (𝓝 (DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ φ))) := by
  intro u v uN vN E0 huconv hE0 hv hvpair φ hφ
  have hvfin : limitFormEnergy G v < (⊤ : EReal) := by
    exact hv
  have hvE : v ∈ E.domain := by
    apply aux_cor_energy_measures_domain_of_energy_ne_top E v
    rw [hEform v]
    exact hvfin.ne
  have huDom :=
    aux_cor_energy_measures_domain_of_bound S a G hlower u uN E0 huconv hE0
  have huE : u ∈ E.domain := by
    have huFin := (aux_cor_energy_measures_limitDomain_iff G u).mp huDom
    apply aux_cor_energy_measures_domain_of_energy_ne_top E u
    rw [hEform u]
    exact huFin.ne
  have hE0nonneg : 0 ≤ E0 :=
    le_trans (responseForm_nonneg S (a 0) (uN 0)) (hE0 0)
  have hvconv : Tendsto (fun n => (vN n).val.1) atTop (𝓝 v) := by
    have hv' := hvpair.fst_nhds
    change Tendsto (fun n => (vN n).val.1) atTop (𝓝 v) at hv'
    exact hv'
  have hvweak := aux_cor_energy_measures_weak_of_space S vN v hvconv

  let crossSeq : (SpatialCoordinates d → ℝ) → ℕ → ℝ :=
    aux_cor_energy_measures_crossSeq S a uN vN
  let crossLimit : (SpatialCoordinates d → ℝ) → ℝ :=
    aux_cor_energy_measures_crossLimit E Gamma u v
  have hpositive : ∀ (rho : SpatialCoordinates d → ℝ),
      ContinuousOn rho (closure (Q : Set (SpatialCoordinates d))) →
      (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), 0 < rho x) →
      Tendsto (crossSeq rho) atTop (𝓝 (crossLimit rho)) := by
    intro rho hrho hrhopos
    change Tendsto (fun n => ∫ x in (Q : Set (SpatialCoordinates d)), rho x *
      ((a n).val x * ∑ i : Fin d,
        ((uN n : SobolevData Q).2 i x) * ((vN n : SobolevData Q).2 i x))) atTop
      (𝓝 (DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ rho))
    have hcompact : IsCompact (closure (Q : Set (SpatialCoordinates d))) := by
      rw [hQcube]
      exact (centeredCube_isBounded z0 hR).isCompact_closure
    obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hrho
    let C : ℝ := max M 0 + 1
    have hC : 0 < C := by
      dsimp [C]
      linarith [le_max_right M 0]
    have hrhoC : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
        ‖rho x‖ ≤ C := by
      intro x hx
      have hxM : ‖rho x‖ ≤ M := hM x hx
      change ‖rho x‖ ≤ max M 0 + 1
      calc
        ‖rho x‖ ≤ M := hxM
        _ ≤ max M 0 := le_max_left _ _
        _ ≤ max M 0 + 1 := le_add_of_nonneg_right (by norm_num)
    have hrhomeas : AEStronglyMeasurable rho
        (volume.restrict (Q : Set (SpatialCoordinates d))) :=
      (hrho.mono subset_closure).aestronglyMeasurable Q.isOpen.measurableSet
    have hrhoCae : ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
        ‖rho x‖ ≤ C := by
      filter_upwards [ae_restrict_mem Q.isOpen.measurableSet] with x hx
      exact hrhoC x (subset_closure hx)
    let A : ℕ → ℝ := fun n =>
      ∫ x in (Q : Set (SpatialCoordinates d)), rho x *
        ((a n).val x * ∑ i : Fin d,
          ((uN n : SobolevData Q).2 i x) ^ 2)
    let B : ℕ → ℝ := fun n =>
      ∫ x in (Q : Set (SpatialCoordinates d)), rho x *
        ((a n).val x * ∑ i : Fin d,
          ((uN n : SobolevData Q).2 i x) * ((vN n : SobolevData Q).2 i x))
    let Cseq : ℕ → ℝ := fun n =>
      ∫ x in (Q : Set (SpatialCoordinates d)), rho x *
        ((a n).val x * ∑ i : Fin d,
          ((vN n : SobolevData Q).2 i x) ^ 2)
    let D : ℝ := DirichletForm.signedIntegralOn (Gamma.cross u v)
      (Q : Set (SpatialCoordinates d)) rho
    have hA_nonneg : ∀ n, 0 ≤ A n := by
      intro n
      dsimp [A]
      apply integral_nonneg_of_ae
      obtain ⟨k, hk, hka⟩ := (a n).property
      have hane : 0 ≤ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
          (fun x => (a n).val x * ∑ i : Fin d,
            ((uN n : SobolevData Q).2 i x) ^ 2) := by
        filter_upwards [hka] with x hx
        have hax : 0 ≤ (a n).val x := le_trans hk.le hx
        exact mul_nonneg hax (Finset.sum_nonneg fun i hi => sq_nonneg _)
      filter_upwards [ae_restrict_mem Q.isOpen.measurableSet, hane] with x hx hg
      exact mul_nonneg (le_of_lt (hrhopos x (subset_closure hx))) hg
    have hA_upper : ∀ n, A n ≤ C * E0 := by
      intro n
      have hg := aux_cor_energy_measures_energy_integrable S a n (uN n)
      have hρg : Integrable (fun x => rho x *
          ((a n).val x * ∑ i : Fin d,
            ((uN n : SobolevData Q).2 i x) ^ 2))
          (volume.restrict (Q : Set (SpatialCoordinates d))) := by
        exact hg.bdd_mul hrhomeas hrhoCae
      have hCg : Integrable (fun x => C *
          ((a n).val x * ∑ i : Fin d,
            ((uN n : SobolevData Q).2 i x) ^ 2))
          (volume.restrict (Q : Set (SpatialCoordinates d))) :=
        hg.const_mul C
      have hmono : ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
          rho x * ((a n).val x * ∑ i : Fin d,
            ((uN n : SobolevData Q).2 i x) ^ 2) ≤
          C * ((a n).val x * ∑ i : Fin d,
            ((uN n : SobolevData Q).2 i x) ^ 2) := by
        obtain ⟨k, hk, hka⟩ := (a n).property
        filter_upwards [ae_restrict_mem Q.isOpen.measurableSet, hka] with x hx hax
        have hρ0 : 0 ≤ rho x := le_of_lt (hrhopos x (subset_closure hx))
        have hg0 : 0 ≤ (a n).val x * ∑ i : Fin d,
            ((uN n : SobolevData Q).2 i x) ^ 2 := by
          exact mul_nonneg (le_trans hk.le hax)
            (Finset.sum_nonneg fun i hi => sq_nonneg _)
        exact mul_le_mul_of_nonneg_right (by
          simpa [Real.norm_eq_abs, abs_of_nonneg hρ0] using hrhoC x
            (subset_closure hx)) hg0
      calc
        A n = ∫ x, rho x * ((a n).val x * ∑ i : Fin d,
            ((uN n : SobolevData Q).2 i x) ^ 2)
            ∂(volume.restrict (Q : Set (SpatialCoordinates d))) := by rfl
        _ ≤ ∫ x, C * ((a n).val x * ∑ i : Fin d,
            ((uN n : SobolevData Q).2 i x) ^ 2)
            ∂(volume.restrict (Q : Set (SpatialCoordinates d))) :=
          integral_mono_ae hρg hCg hmono
        _ = C * responseForm S (a n) (uN n) (uN n) := by
          rw [integral_const_mul]
          congr 1
          exact aux_cor_energy_measures_energy_integral S a n (uN n)
        _ ≤ C * E0 := by
          gcongr
          exact hE0 n
    have hCconv : Tendsto Cseq atTop
        (𝓝 (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂Gamma.measure v)) := by
      have hvrec := hrecover v vN hv hvpair rho hrho
      have heq : (fun n => ∫ x, rho x ∂(((volume.restrict
          (Q : Set (SpatialCoordinates d)))).withDensity
          (fun y => ENNReal.ofReal ((a n).val y *
            ∑ i : Fin d, ((vN n : SobolevData Q).2 i y) ^ 2)))) = Cseq := by
        funext n
        exact aux_cor_energy_measures_density S a n (vN n) rho
      rw [heq] at hvrec
      have hGammaSupport : (Gamma.measure v).restrict
          (Q : Set (SpatialCoordinates d)) = Gamma.measure v := by
        apply Measure.restrict_eq_self_of_ae_mem
        exact mem_ae_iff.mpr (hGammaQ v hvE)
      simpa [hGammaSupport] using hvrec
    let V : ℝ := (limitFormEnergy G v).toReal
    have hVnonneg : 0 ≤ V := by
      apply EReal.coe_le_coe_iff.mp
      rw [EReal.coe_toReal hvfin.ne
        (aux_cor_energy_measures_limitEnergy_ne_bot G v)]
      exact limitFormEnergy_nonneg G v
    have hV_upper : ∀ᶠ n in atTop,
        responseForm S (a n) (vN n) (vN n) ≤ V + 1 := by
      have hp := hvpair
      rw [nhds_prod_eq] at hp
      have hsnd := tendsto_snd.comp hp
      have hcoev : (V : EReal) = limitFormEnergy G v := by
        dsimp [V]
        exact (EReal.coe_toReal hvfin.ne
          (aux_cor_energy_measures_limitEnergy_ne_bot G v))
      have htarget : limitFormEnergy G v < ((V + 1 : ℝ) : EReal) := by
        rw [← hcoev]
        exact EReal.coe_lt_coe_iff.mpr (lt_add_one V)
      have hh := hsnd.eventually (Iio_mem_nhds htarget)
      filter_upwards [hh] with n hn
      have hn' : ((responseForm S (a n) (vN n) (vN n) : ℝ) : EReal) <
          ((V + 1 : ℝ) : EReal) := by
        simpa [hcoev] using hn
      exact (EReal.coe_lt_coe_iff.mp hn').le
    have hB_abs : ∀ᶠ n in atTop, |B n| ≤
        C / 2 * (E0 + (V + 1)) := by
      filter_upwards [hV_upper] with n hvn
      have hb := aux_cor_energy_measures_cross_abs_bound S a n (uN n) (vN n)
        rho C hrhomeas hrhoCae (le_of_lt hC)
      dsimp [B]
      calc
        |∫ x in (Q : Set (SpatialCoordinates d)), rho x *
            ((a n).val x * ∑ i : Fin d,
              ((uN n : SobolevData Q).2 i x) *
                ((vN n : SobolevData Q).2 i x))| ≤
            C / 2 * (responseForm S (a n) (uN n) (uN n) +
              responseForm S (a n) (vN n) (vN n)) := hb
        _ ≤ C / 2 * (E0 + (V + 1)) := by
          gcongr
          exact hE0 n
    let U : ℝ := C * E0
    let L : ℝ := C / 2 * (E0 + (V + 1))
    have hU : 0 ≤ U := by
      dsimp [U]
      exact mul_nonneg hC.le hE0nonneg
    have hL : 0 ≤ L := by
      dsimp [L]
      exact mul_nonneg (by positivity) (by linarith)
    have hBtend : Tendsto B atTop (𝓝 D) := by
      apply tendsto_of_subseq_tendsto
      intro ns hns
      obtain ⟨σ, hσ, hσns⟩ := strictMono_subseq_of_tendsto_atTop hns
      let idx : ℕ → ℕ := ns ∘ σ
      have hidx : StrictMono idx := by
        simpa [idx] using hσns
      have hmem : ∀ᶠ k in atTop,
          (A (idx k), B (idx k)) ∈ (Set.Icc (0 : ℝ) U) ×ˢ Set.Icc (-L) L := by
        have hbidx : ∀ᶠ k in atTop, |B (idx k)| ≤ L :=
          hidx.tendsto_atTop.eventually hB_abs
        filter_upwards [hbidx] with k hk
        change (0 ≤ A (idx k) ∧ A (idx k) ≤ U) ∧
          (-L ≤ B (idx k) ∧ B (idx k) ≤ L)
        exact ⟨⟨hA_nonneg _, by simpa [U] using hA_upper _⟩,
          (abs_le.mp hk).1, (abs_le.mp hk).2⟩
      obtain ⟨ab, hab, τ, hτ, hp⟩ :=
        ((isCompact_Icc.prod isCompact_Icc).tendsto_subseq' hmem.frequently)
      let κ : ℕ → ℕ := σ ∘ τ
      have hκ : StrictMono κ := by
        exact hσ.comp hτ
      have hidxκ : StrictMono (fun n => ns (κ n)) := by
        simpa [κ, idx, Function.comp_def] using hidx.comp hτ
      have hnsκ : Tendsto (fun n => ns (κ n)) atTop atTop :=
        hidxκ.tendsto_atTop
      have hAstar : Tendsto (fun n => A (ns (κ n))) atTop (𝓝 ab.1) := by
        have hh := hp.fst_nhds
        simpa [idx, κ, Function.comp_def] using hh
      have hBstar : Tendsto (fun n => B (ns (κ n))) atTop (𝓝 ab.2) := by
        have hh := hp.snd_nhds
        simpa [idx, κ, Function.comp_def] using hh
      have hCstar := hCconv.comp hnsκ
      have hcluster_eq : ab.2 = D := by
        have hQm : MeasurableSet (Q : Set (SpatialCoordinates d)) :=
          Q.isOpen.measurableSet
        let μuv : Measure (SpatialCoordinates d) :=
          Gamma.measure u + Gamma.measure v
        have hμu0 : Gamma.measure u ≪ μuv := by
          dsimp [μuv]
          exact Measure.AbsolutelyContinuous.add_right
            (Measure.AbsolutelyContinuous.rfl) _
        have hμv0 : Gamma.measure v ≪ μuv := by
          dsimp [μuv]
          simpa [add_comm] using
            (Measure.AbsolutelyContinuous.add_right
              (Measure.AbsolutelyContinuous.rfl : Gamma.measure v ≪ Gamma.measure v)
              (Gamma.measure u))
        obtain ⟨huvpos, huvneg⟩ :=
          aux_cor_energy_measures_cross_absolutelyContinuous E Gamma u v huE hvE
            μuv hμu0 hμv0
        have huvTV : (Gamma.cross u v).totalVariation ≪ μuv :=
          (SignedMeasure.totalVariation_absolutelyContinuous_iff _ _).2
            ⟨huvpos, huvneg⟩
        have hμuvQ : μuv (Q : Set (SpatialCoordinates d))ᶜ = 0 := by
          dsimp [μuv]
          rw [hGammaQ u huE, hGammaQ v hvE, add_zero]
        have hDuniv : D =
            DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ rho := by
          dsimp [D]
          exact aux_cor_energy_measures_signedIntegralOn_Q_eq_univ
            (Gamma.cross u v) μuv (Q : Set (SpatialCoordinates d)) hQm
            huvpos huvneg hμuvQ rho
        have hweakU0 := aux_cor_energy_measures_weak_of_space S uN u huconv
        have hscalar_ineq : ∀ s : ℝ,
            (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂Gamma.measure u) +
                2 * s * D + s ^ 2 *
                  (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂Gamma.measure v) ≤
              ab.1 + 2 * s * ab.2 + s ^ 2 *
                  (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂Gamma.measure v) := by
          intro s
          let wN : ℕ → S.space := fun n =>
            uN n + s • vN n
          let w : DomainL2 Q := u + s • v
          have hwE : w ∈ E.domain := by
            dsimp [w]
            exact E.domain.add_mem huE (E.domain.smul_mem s hvE)
          have hw : w ∈ limitFormDomain G := by
            have hh : E.energy w < (⊤ : EReal) :=
              (E.energy_lt_top_iff w).mpr hwE
            rw [hEform w] at hh
            exact hh
          have hwweak : ∀ f : DomainL2 Q,
              Tendsto (fun n => inner ℝ f (wN n).val.1) atTop
                (𝓝 (inner ℝ f w)) := by
            intro f
            have hu' := hweakU0 f
            have hv' := hvweak f
            have hadd := hu'.add (Tendsto.const_mul s hv')
            have heq : (fun n => inner ℝ f (wN n).val.1) =
                (fun n => inner ℝ f (uN n).val.1 +
                  s * inner ℝ f (vN n).val.1) := by
              funext n
              simp [wN, w, inner_add_right, inner_smul_right]
            rw [heq]
            simpa [w, inner_add_right, inner_smul_right] using hadd
          have hweight := hweighted rho hrho hrhopos
            (ns ∘ κ) hidxκ wN w hw hwweak
          have hρμ : AEStronglyMeasurable rho
              ((Gamma.measure u + Gamma.measure v + Gamma.measure w).restrict
                (Q : Set (SpatialCoordinates d))) := by
            exact (hrho.mono subset_closure).aestronglyMeasurable hQm
          have hρCμ : ∀ᵐ x ∂((Gamma.measure u + Gamma.measure v +
              Gamma.measure w).restrict (Q : Set (SpatialCoordinates d))),
              ‖rho x‖ ≤ C := by
            filter_upwards [ae_restrict_mem hQm] with x hx
            exact hrhoC x (subset_closure hx)
          let μ : Measure (SpatialCoordinates d) :=
            Gamma.measure u + Gamma.measure v + Gamma.measure w
          have hμ : μ Set.univ < (⊤ : ENNReal) := by
            dsimp [μ]
            exact ENNReal.add_lt_top.mpr ⟨
              ENNReal.add_lt_top.mpr ⟨
                (Gamma.measure_univ_lt_top u huE),
                (Gamma.measure_univ_lt_top v hvE)⟩,
              (Gamma.measure_univ_lt_top w hwE)⟩
          have hμu : Gamma.measure u ≪ μ := by
            dsimp [μ]
            have h₁ : Gamma.measure u ≪ Gamma.measure u + Gamma.measure v :=
              Measure.AbsolutelyContinuous.add_right
                (Measure.AbsolutelyContinuous.rfl) _
            have h₂ : Gamma.measure u + Gamma.measure v ≪
                (Gamma.measure u + Gamma.measure v) + Gamma.measure w :=
              Measure.AbsolutelyContinuous.add_right
                (Measure.AbsolutelyContinuous.rfl) _
            exact h₁.trans h₂
          have hμv : Gamma.measure v ≪ μ := by
            dsimp [μ]
            have h₁ : Gamma.measure v ≪ Gamma.measure v + Gamma.measure u :=
              Measure.AbsolutelyContinuous.add_right
                (Measure.AbsolutelyContinuous.rfl) _
            have h₂ : Gamma.measure v + Gamma.measure u ≪
                (Gamma.measure v + Gamma.measure u) + Gamma.measure w :=
              Measure.AbsolutelyContinuous.add_right
                (Measure.AbsolutelyContinuous.rfl) _
            have hadd : (Gamma.measure v + Gamma.measure u) + Gamma.measure w =
                (Gamma.measure u + Gamma.measure v) + Gamma.measure w := by
              rw [add_comm (Gamma.measure v) (Gamma.measure u)]
            exact hadd ▸ h₁.trans h₂
          have hμw : Gamma.measure w ≪ μ := by
            dsimp [μ]
            have h₁ : Gamma.measure w ≪ Gamma.measure w + Gamma.measure u :=
              Measure.AbsolutelyContinuous.add_right
                (Measure.AbsolutelyContinuous.rfl) _
            have h₂ : Gamma.measure w + Gamma.measure u ≪
                (Gamma.measure w + Gamma.measure u) + Gamma.measure v :=
              Measure.AbsolutelyContinuous.add_right
                (Measure.AbsolutelyContinuous.rfl) _
            have hadd : (Gamma.measure w + Gamma.measure u) + Gamma.measure v =
                (Gamma.measure u + Gamma.measure v) + Gamma.measure w := by
              calc
                (Gamma.measure w + Gamma.measure u) + Gamma.measure v =
                    Gamma.measure w + (Gamma.measure u + Gamma.measure v) :=
                  add_assoc _ _ _
                _ = (Gamma.measure u + Gamma.measure v) + Gamma.measure w :=
                  add_comm _ _
            exact hadd ▸ h₁.trans h₂
          have h0 : (Gamma.cross u u).totalVariation ≪ μ := by
            obtain ⟨hp, hn⟩ :=
              aux_cor_energy_measures_cross_absolutelyContinuous E Gamma u u huE huE
                μ hμu hμu
            exact (SignedMeasure.totalVariation_absolutelyContinuous_iff _ _).2
              ⟨hp, hn⟩
          have h1 : (Gamma.cross u v).totalVariation ≪ μ := by
            exact huvTV.add_right (Gamma.measure w)
          have h2 : (Gamma.cross v v).totalVariation ≪ μ := by
            obtain ⟨hp, hn⟩ :=
              aux_cor_energy_measures_cross_absolutelyContinuous E Gamma v v hvE hvE
                μ hμv hμv
            exact (SignedMeasure.totalVariation_absolutelyContinuous_iff _ _).2
              ⟨hp, hn⟩
          have hwcross : (Gamma.cross w w).totalVariation ≪ μ := by
            obtain ⟨hp, hn⟩ :=
              aux_cor_energy_measures_cross_absolutelyContinuous E Gamma w w hwE hwE
                μ hμw hμw
            exact (SignedMeasure.totalVariation_absolutelyContinuous_iff _ _).2
              ⟨hp, hn⟩
          have hc : ((2 * s) • Gamma.cross u v).totalVariation ≪ μ :=
            aux_cor_energy_measures_totalVariation_smul (2 * s)
              (Gamma.cross u v) μ h1
          have hq : ((s ^ 2) • Gamma.cross v v).totalVariation ≪ μ :=
            aux_cor_energy_measures_totalVariation_smul (s ^ 2)
              (Gamma.cross v v) μ h2
          have h01 : (Gamma.cross u u + (2 * s) • Gamma.cross u v).totalVariation ≪ μ :=
            aux_cor_energy_measures_totalVariation_add (Gamma.cross u u)
              ((2 * s) • Gamma.cross u v) μ h0 hc
          have hsum : ((Gamma.cross u u + (2 * s) • Gamma.cross u v) +
              (s ^ 2) • Gamma.cross v v).totalVariation ≪ μ :=
            aux_cor_energy_measures_totalVariation_add
              (Gamma.cross u u + (2 * s) • Gamma.cross u v)
              ((s ^ 2) • Gamma.cross v v) μ h01 hq
          have hgam := aux_cor_energy_measures_gamma_weighted_expand E Gamma u v
            huE hvE s rho (Q : Set (SpatialCoordinates d)) μ hμ hQm hρμ
            ⟨C, by simpa [μ] using hρCμ⟩
            h0 h1 h2 hc hq h01 hsum
          have hexpand : ∀ n,
              (∫ x in (Q : Set (SpatialCoordinates d)), rho x *
                  ((a (ns (κ n))).val x * ∑ i : Fin d,
                    (((wN (ns (κ n)) : SobolevData Q).2 i x) ^ 2))) =
                A (ns (κ n)) + 2 * s * B (ns (κ n)) +
                  s ^ 2 * Cseq (ns (κ n)) := by
            intro n
            simpa only [wN, A, B, Cseq] using!
              (aux_cor_energy_measures_weighted_quadratic_expand S a
                (ns (κ n)) (uN (ns (κ n))) (vN (ns (κ n))) rho s C
                hrhomeas hrhoCae)
          have hABC : Tendsto
              (fun n => A (ns (κ n)) + 2 * s * B (ns (κ n)) +
                s ^ 2 * Cseq (ns (κ n))) atTop
              (𝓝 (ab.1 + 2 * s * ab.2 + s ^ 2 *
                (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂Gamma.measure v))) := by
            have h1' := hAstar.add (Tendsto.const_mul (2 * s) hBstar)
            have h2' := hCstar.const_mul (s ^ 2)
            have hh := h1'.add h2'
            simpa only [Function.comp_apply, add_assoc] using hh
          have hABCE : Tendsto (fun n =>
              (((A (ns (κ n)) + 2 * s * B (ns (κ n)) +
                s ^ 2 * Cseq (ns (κ n))) : ℝ) : EReal)) atTop
              (𝓝 (((ab.1 + 2 * s * ab.2 + s ^ 2 *
                (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂Gamma.measure v)) : ℝ) : EReal)) :=
            (EReal.tendsto_coe).mpr hABC
          have hweight' :
              (((∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂Gamma.measure w) : ℝ) : EReal) ≤
                liminf (fun n =>
                  (((A (ns (κ n)) + 2 * s * B (ns (κ n)) +
                    s ^ 2 * Cseq (ns (κ n))) : ℝ) : EReal)) atTop := by
            convert hweight using 1
            apply liminf_congr
            filter_upwards [] with n
            simpa only [Function.comp_apply] using
              congrArg (fun r : ℝ => (r : EReal)) (hexpand n).symm
          have hlim := hABCE.liminf_eq
          rw [hlim] at hweight'
          rw [hgam] at hweight'
          apply EReal.coe_le_coe_iff.mp
          simpa [D, EReal.coe_add, EReal.coe_mul] using hweight'
        have hzero := hscalar_ineq 0
        have hnonneg : 0 ≤ ab.1 -
            (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂Gamma.measure u) := by
          linarith
        have hlinear : ∀ s : ℝ, 0 ≤
            (ab.1 - (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂Gamma.measure u)) +
              2 * s * (ab.2 - D) := by
          intro s
          have hs := hscalar_ineq s
          nlinarith
        by_contra hne
        let s0 := -((ab.1 -
          (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂Gamma.measure u)) + 1) /
            (2 * (ab.2 - D))
        have hden : 2 * (ab.2 - D) ≠ 0 := by
          exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr hne)
        have hs0 := hlinear s0
        have hcalc :
            (ab.1 - (∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂Gamma.measure u)) +
              2 * s0 * (ab.2 - D) = -1 := by
          dsimp [s0]
          have hdiff : ab.2 - D ≠ 0 := sub_ne_zero.mpr hne
          field_simp [hden, hdiff]
          ring
        linarith
      refine ⟨κ, ?_⟩
      simpa [hcluster_eq, κ, Function.comp_def] using hBstar
    have hDuniv := aux_cor_energy_measures_cross_Q_eq_univ E Gamma u v huE hvE
      hGammaQ rho
    change Tendsto (crossSeq rho) atTop
      (𝓝 (DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ rho))
    rw [← hDuniv]
    change Tendsto B atTop (𝓝 D)
    exact hBtend
  exact aux_cor_energy_measures_clause_c_extend (d := d) (Q := Q)
    z0 R hR hQcube S a E Gamma u v uN vN huE hvE hGammaQ
    hpositive φ hφ



theorem cor_energy_measures
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (hQcube : Q = centeredCube z0 R hR)
    (S : ResponseSpace Q) (hS : S.space = killedSobolevGraph Q)
    (a : ℕ → PositiveCoefficient Q)
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hEform : ∀ w : DomainL2 Q, E.energy w = limitFormEnergy G w)
    (Gamma : DirichletForm.EnergyMeasure E)
    (hGammaQ : ∀ w : DomainL2 Q, w ∈ E.domain →
      Gamma.measure w (Q : Set (SpatialCoordinates d))ᶜ = 0)
    (hweighted : ∀ rho : SpatialCoordinates d → ℝ,
      ContinuousOn rho (closure (Q : Set (SpatialCoordinates d))) →
      (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), 0 < rho x) →
      ∀ sigma : ℕ → ℕ, StrictMono sigma →
      ∀ (wN : ℕ → S.space) (w : DomainL2 Q), w ∈ limitFormDomain G →
      (∀ f : DomainL2 Q,
        Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      (((∫ x in (Q : Set (SpatialCoordinates d)), rho x ∂(Gamma.measure w)) : ℝ)
          : EReal) ≤
        liminf (fun n =>
          (((∫ x in (Q : Set (SpatialCoordinates d)), rho x *
              ((a (sigma n)).val x * ∑ i : Fin d,
                ((wN (sigma n) : SobolevData Q).2 i x) ^ 2)) : ℝ) : EReal)) atTop)
    (hlower : ∀ (wN : ℕ → S.space) (w : DomainL2 Q),
      (∀ f : DomainL2 Q,
        Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      limitFormEnergy G w ≤
        liminf (fun n => ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal)) atTop) :
    -- (a) a recovery sequence carries its energy measures weakly to `Gamma_E(u)`
    (∀ (u : DomainL2 Q) (uN : ℕ → S.space), u ∈ limitFormDomain G →
      Tendsto (fun n => ((uN n).val.1,
        ((responseForm S (a n) (uN n) (uN n) : ℝ) : EReal))) atTop
        (𝓝 (u, limitFormEnergy G u)) →
      ∀ φ : SpatialCoordinates d → ℝ,
        ContinuousOn φ (closure (Q : Set (SpatialCoordinates d))) →
        Tendsto (fun n => ∫ x, φ x ∂(((volume.restrict (Q : Set (SpatialCoordinates d)))).withDensity
          (fun y => ENNReal.ofReal ((a n).val y *
            ∑ i : Fin d, ((uN n : SobolevData Q).2 i y) ^ 2)))) atTop
          (𝓝 (∫ x, φ x ∂(Gamma.measure u)))) ∧
    -- (b) every weak cluster of the energy measures dominates `Gamma_E(u)`
    (∀ (u : DomainL2 Q) (uN : ℕ → S.space) (E0 : ℝ)
        (nu : Measure (SpatialCoordinates d)) (sigma : ℕ → ℕ),
      nu Set.univ < (⊤ : ENNReal) →
      nu ((closure (Q : Set (SpatialCoordinates d)))ᶜ) = 0 →
      StrictMono sigma →
      Tendsto (fun n => (uN n).val.1) atTop (𝓝 u) →
      (∀ n : ℕ, responseForm S (a n) (uN n) (uN n) ≤ E0) →
      (∀ φ : SpatialCoordinates d → ℝ,
        ContinuousOn φ (closure (Q : Set (SpatialCoordinates d))) →
        Tendsto (fun n => ∫ x, φ x ∂(((volume.restrict (Q : Set (SpatialCoordinates d)))).withDensity
          (fun y => ENNReal.ofReal ((a (sigma n)).val y *
            ∑ i : Fin d, ((uN (sigma n) : SobolevData Q).2 i y) ^ 2))))
          atTop (𝓝 (∫ x, φ x ∂nu))) →
      u ∈ limitFormDomain G ∧
        ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
          Gamma.measure u B ≤ nu B) ∧
    -- (c) the cross measures converge weakly to `Gamma_E(u,v)`
    (∀ (u v : DomainL2 Q) (uN vN : ℕ → S.space) (E0 : ℝ),
      Tendsto (fun n => (uN n).val.1) atTop (𝓝 u) →
      (∀ n : ℕ, responseForm S (a n) (uN n) (uN n) ≤ E0) →
      v ∈ limitFormDomain G →
      Tendsto (fun n => ((vN n).val.1,
        ((responseForm S (a n) (vN n) (vN n) : ℝ) : EReal))) atTop
        (𝓝 (v, limitFormEnergy G v)) →
      ∀ φ : SpatialCoordinates d → ℝ,
        ContinuousOn φ (closure (Q : Set (SpatialCoordinates d))) →
        Tendsto (fun n => ∫ x in (Q : Set (SpatialCoordinates d)), φ x *
          ((a n).val x * ∑ i : Fin d,
            ((uN n : SobolevData Q).2 i x) * ((vN n : SobolevData Q).2 i x)))
          atTop
          (𝓝 (DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ φ))) := by
  have h_weak_of_prod {wN : ℕ → S.space} {w : DomainL2 Q}
      (h : Tendsto (fun n => ((wN n).val.1,
        ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal))) atTop
        (𝓝 (w, limitFormEnergy G w))) :
      ∀ f : DomainL2 Q,
        Tendsto (fun n => inner ℝ f (wN n).val.1) atTop
          (𝓝 (inner ℝ f w)) := by
    intro f
    have h' := h
    rw [nhds_prod_eq] at h'
    have hfst := tendsto_fst.comp h'
    have hc : Continuous (fun x : DomainL2 Q => inner ℝ f x) :=
      (continuous_inner (𝕜 := ℝ)).comp (continuous_const.prodMk continuous_id)
    exact hc.continuousAt.tendsto.comp hfst

  have h_energy_of_prod {wN : ℕ → S.space} {w : DomainL2 Q}
      (h : Tendsto (fun n => ((wN n).val.1,
        ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal))) atTop
        (𝓝 (w, limitFormEnergy G w))) :
      Tendsto (fun n => ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal)) atTop
        (𝓝 (E.energy w)) := by
    have h' := h
    rw [nhds_prod_eq] at h'
    have hsnd := tendsto_snd.comp h'
    simpa [hEform w] using! hsnd

  have hrecover :
      ∀ (w : DomainL2 Q) (wN : ℕ → S.space), w ∈ limitFormDomain G →
        Tendsto (fun n => ((wN n).val.1,
          ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal))) atTop
          (𝓝 (w, limitFormEnergy G w)) →
        ∀ ψ : SpatialCoordinates d → ℝ,
          ContinuousOn ψ (closure (Q : Set (SpatialCoordinates d))) →
          Tendsto (fun n => ∫ x, ψ x ∂(((volume.restrict
            (Q : Set (SpatialCoordinates d)))).withDensity
            (fun y => ENNReal.ofReal ((a n).val y *
              ∑ i : Fin d, ((wN n : SobolevData Q).2 i y) ^ 2)))) atTop
            (𝓝 (∫ x, ψ x ∂(Gamma.measure w))) := by
    intro u uN hu hpair ψ hψ
    have huE : u ∈ E.domain := by
      have hfin : E.energy u ≠ (⊤ : EReal) := by
        rw [hEform u]
        exact (show limitFormEnergy G u < ⊤ from hu).ne
      by_contra hnot
      apply hfin
      simp [DirichletForm.ClosedForm.energy, hnot]
    have hweak := h_weak_of_prod hpair
    have henergy := h_energy_of_prod hpair
    have hcompact : IsCompact (closure (Q : Set (SpatialCoordinates d))) := by
      rw [hQcube]
      exact (centeredCube_isBounded z0 hR).isCompact_closure
    obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hψ
    let C : ℝ := max M 0 + 1
    have hC : 0 < C := by
      dsimp [C]
      linarith [le_max_right M 0]
    have hψC : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), |ψ x| ≤ C := by
      intro x hx
      have hxM : |ψ x| ≤ M := by
        simpa [Real.norm_eq_abs] using hM x hx
      dsimp [C]
      linarith [le_max_left M 0]
    let q : ℝ := 1 / (2 * C)
    have hq : 0 < q := by
      dsimp [q]
      positivity
    have hqC : q * C < 1 := by
      dsimp [q]
      field_simp [ne_of_gt hC]
      norm_num
    have hplus_cont : ContinuousOn (fun x => 1 + q * ψ x)
        (closure (Q : Set (SpatialCoordinates d))) :=
      continuousOn_const.add (continuousOn_const.mul hψ)
    have hminus_cont : ContinuousOn (fun x => 1 + (-q) * ψ x)
        (closure (Q : Set (SpatialCoordinates d))) :=
      continuousOn_const.add (continuousOn_const.mul hψ)
    have hplus_pos : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
        0 < 1 + q * ψ x := by
      intro x hx
      have habs : |q * ψ x| < 1 := by
        rw [abs_mul, abs_of_pos hq]
        exact (mul_le_mul_of_nonneg_left (hψC x hx) hq.le).trans_lt hqC
      linarith [abs_lt.mp habs]
    have hminus_pos : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
        0 < 1 + (-q) * ψ x := by
      intro x hx
      have habs : |q * ψ x| < 1 := by
        rw [abs_mul, abs_of_pos hq]
        exact (mul_le_mul_of_nonneg_left (hψC x hx) hq.le).trans_lt hqC
      linarith [abs_lt.mp habs]
    have hψmeas : AEStronglyMeasurable ψ
        (volume.restrict (Q : Set (SpatialCoordinates d))) :=
      (hψ.mono subset_closure).aestronglyMeasurable Q.isOpen.measurableSet
    have hψCae : ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
        ‖ψ x‖ ≤ C := by
      filter_upwards [ae_restrict_mem Q.isOpen.measurableSet] with x hx
      simpa [Real.norm_eq_abs] using hψC x (subset_closure hx)
    let c : ℕ → ℝ := fun n => responseForm S (a n) (uN n) (uN n)
    let b : ℕ → ℝ := fun n =>
      ∫ x in (Q : Set (SpatialCoordinates d)), ψ x *
        ((a n).val x * ∑ i : Fin d,
          ((uN n : SobolevData Q).2 i x) ^ 2)
    have hc : Tendsto (fun n => (c n : EReal)) atTop
        (𝓝 (E.form u u : EReal)) := by
      have heq : E.energy u = (E.form u u : EReal) := by
        simp [DirichletForm.ClosedForm.energy, huE]
      simpa [c, heq] using henergy
    have hplus := hweighted (fun x => 1 + q * ψ x) hplus_cont hplus_pos
      (fun n => n) strictMono_id uN u hu hweak
    have hminus := hweighted (fun x => 1 + (-q) * ψ x) hminus_cont hminus_pos
      (fun n => n) strictMono_id uN u hu hweak
    have hplus_n : ∀ n : ℕ,
        (∫ x in (Q : Set (SpatialCoordinates d)),
          (1 + q * ψ x) * ((a n).val x * ∑ i : Fin d,
            ((uN n : SobolevData Q).2 i x) ^ 2)) = c n + q * b n := by
      intro n
      simpa [c, b, mul_assoc] using
        (aux_cor_energy_measures_affine_integral S a n (uN n) ψ q C
          hψmeas hψCae)
    have hminus_n : ∀ n : ℕ,
        (∫ x in (Q : Set (SpatialCoordinates d)),
          (1 + (-q) * ψ x) * ((a n).val x * ∑ i : Fin d,
            ((uN n : SobolevData Q).2 i x) ^ 2)) = c n - q * b n := by
      intro n
      have hh := aux_cor_energy_measures_affine_integral S a n (uN n) ψ (-q) C
        hψmeas hψCae
      simpa [c, b, sub_eq_add_neg, mul_assoc] using hh
    let γ : ℝ := ∫ x in (Q : Set (SpatialCoordinates d)), ψ x ∂(Gamma.measure u)
    have hplus' : (E.form u u : EReal) + (q : EReal) *
        (γ : EReal) ≤
        liminf (fun n => ((c n + q * b n : ℝ) : EReal)) atTop := by
      have hgamma := aux_cor_energy_measures_gamma_affine E Gamma hGammaQ u huE ψ hψ q C
        (fun x hx => hψC x (subset_closure hx))
      rw [hgamma] at hplus
      rw [aux_cor_energy_measures_sequence_affine S a uN ψ q C hψmeas hψCae] at hplus
      have h0 :
          (((∫ x in (Q : Set (SpatialCoordinates d)), (1 + q * ψ x) ∂(Gamma.measure u)) : ℝ) : EReal) ≤
            liminf (fun n => ((c n + q * b n : ℝ) : EReal)) atTop := by
        convert! hplus using 1
        · exact congrArg (fun r : ℝ => (r : EReal)) hgamma
      calc
        (E.form u u : EReal) + (q : EReal) * (γ : EReal) =
            (((∫ x in (Q : Set (SpatialCoordinates d)), (1 + q * ψ x) ∂(Gamma.measure u)) : ℝ) : EReal) := by
              dsimp [γ]
              exact (congrArg (fun r : ℝ => (r : EReal)) hgamma).symm
        _ ≤ liminf (fun n => ((c n + q * b n : ℝ) : EReal)) atTop := h0
    have hminus' : (E.form u u : EReal) - (q : EReal) *
        (γ : EReal) ≤
        liminf (fun n => ((c n - q * b n : ℝ) : EReal)) atTop := by
      have hgamma := aux_cor_energy_measures_gamma_affine E Gamma hGammaQ u huE ψ hψ (-q) C
        (fun x hx => hψC x (subset_closure hx))
      rw [hgamma] at hminus
      rw [aux_cor_energy_measures_sequence_affine S a uN ψ (-q) C hψmeas hψCae] at hminus
      have h0 :
          (((∫ x in (Q : Set (SpatialCoordinates d)), (1 + (-q) * ψ x) ∂(Gamma.measure u)) : ℝ) : EReal) ≤
            liminf (fun n => ((c n - q * b n : ℝ) : EReal)) atTop := by
        convert hminus using 1
        · exact congrArg (fun r : ℝ => (r : EReal)) hgamma
        · apply liminf_congr
          filter_upwards [] with n
          have hh := aux_cor_energy_measures_affine_integral S a n (uN n) ψ (-q) C
            hψmeas hψCae
          have hh' := congrArg (fun r : ℝ => (r : EReal)) hh
          simpa [c, b, sub_eq_add_neg, EReal.coe_add, EReal.coe_mul] using hh'
      calc
        (E.form u u : EReal) - (q : EReal) * (γ : EReal) =
            (((∫ x in (Q : Set (SpatialCoordinates d)), (1 + (-q) * ψ x) ∂(Gamma.measure u)) : ℝ) : EReal) := by
              dsimp [γ]
              simpa [sub_eq_add_neg, EReal.coe_add, EReal.coe_mul] using
                (congrArg (fun r : ℝ => (r : EReal)) hgamma).symm
        _ ≤ liminf (fun n => ((c n - q * b n : ℝ) : EReal)) atTop := h0
    have hplus_nonneg : ∀ n : ℕ, 0 ≤ c n + q * b n := by
      intro n
      rw [← hplus_n n]
      apply integral_nonneg_of_ae
      obtain ⟨k, hk, hka⟩ := (a n).property
      have hane : 0 ≤ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
          (fun x => (a n).val x * ∑ i : Fin d,
            ((uN n : SobolevData Q).2 i x) ^ 2) := by
        filter_upwards [hka] with x hx
        have : 0 ≤ (a n).val x := le_trans hk.le hx
        exact mul_nonneg this (Finset.sum_nonneg fun i hi => sq_nonneg _)
      filter_upwards [ae_restrict_mem Q.isOpen.measurableSet, hane] with x hx hene
      exact mul_nonneg (le_of_lt (hplus_pos x (subset_closure hx))) hene
    have hminus_nonneg : ∀ n : ℕ, 0 ≤ c n - q * b n := by
      intro n
      rw [← hminus_n n]
      apply integral_nonneg_of_ae
      obtain ⟨k, hk, hka⟩ := (a n).property
      have hane : 0 ≤ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
          (fun x => (a n).val x * ∑ i : Fin d,
            ((uN n : SobolevData Q).2 i x) ^ 2) := by
        filter_upwards [hka] with x hx
        have : 0 ≤ (a n).val x := le_trans hk.le hx
        exact mul_nonneg this (Finset.sum_nonneg fun i hi => sq_nonneg _)
      filter_upwards [ae_restrict_mem Q.isOpen.measurableSet, hane] with x hx hene
      exact mul_nonneg (le_of_lt (hminus_pos x (subset_closure hx))) hene
    have hc_upper : ∀ᶠ n : ℕ in atTop, c n ≤ E.form u u + 1 := by
      have hh := hc.eventually (Iio_mem_nhds
        (EReal.coe_lt_coe_iff.mpr (lt_add_one (E.form u u))))
      filter_upwards [hh] with n hn
      exact (EReal.coe_lt_coe_iff.mp hn).le
    let B : ℝ := (E.form u u + 1) / q
    have hB : ∃ B' : ℝ, ∀ᶠ n : ℕ in atTop,
        (-B' : EReal) ≤ (b n : EReal) ∧ (b n : EReal) ≤ B' := by
      refine ⟨B, ?_⟩
      filter_upwards [hc_upper, Filter.Eventually.of_forall hplus_nonneg,
        Filter.Eventually.of_forall hminus_nonneg] with n hcn hp hm
      apply And.intro
      · apply EReal.coe_le_coe_iff.mpr
        dsimp [B]
        rw [← neg_div]
        apply (div_le_iff₀ hq).2
        linarith only [hp, hcn]
      · apply EReal.coe_le_coe_iff.mpr
        dsimp [B]
        apply (le_div_iff₀ hq).2
        linarith only [hm, hcn]
    have hBneg : ∃ B' : ℝ, ∀ᶠ n : ℕ in atTop,
        (-B' : EReal) ≤ ((-b n : ℝ) : EReal) ∧ ((-b n : ℝ) : EReal) ≤ B' := by
      obtain ⟨B', hB'⟩ := hB
      refine ⟨B', ?_⟩
      filter_upwards [hB'] with n hn
      have hnl : -B' ≤ b n := (EReal.coe_le_coe_iff.mp hn.1)
      have hnu : b n ≤ B' := (EReal.coe_le_coe_iff.mp hn.2)
      exact ⟨EReal.coe_le_coe_iff.mpr (neg_le_neg hnu),
        EReal.coe_le_coe_iff.mpr (by simpa using (neg_le_neg hnl))⟩
    have hlow₀ : (γ : EReal) ≤ liminf (fun n => (b n : EReal)) atTop :=
      aux_cor_energy_measures_liminf_affine q hq
        (fun n => (c n : EReal)) b (E.form u u) γ
        hc (EReal.coe_ne_top _) (EReal.coe_ne_bot _) hB hplus'
    have hlow : ((∫ x in (Q : Set (SpatialCoordinates d)), ψ x ∂(Gamma.measure u) : ℝ) : EReal) ≤
        liminf (fun n => (b n : EReal)) atTop := by
      simpa [γ] using hlow₀
    have hminus'' : (E.form u u : EReal) + (q : EReal) *
        ((-γ : ℝ) : EReal) ≤
        liminf (fun n => ((c n + q * (-b n) : ℝ) : EReal)) atTop := by
      simpa [sub_eq_add_neg, EReal.coe_neg, EReal.coe_add, EReal.coe_mul] using hminus'
    have hneg₀ : ((-γ : ℝ) : EReal) ≤
        liminf (fun n => ((-b n : ℝ) : EReal)) atTop :=
      aux_cor_energy_measures_liminf_affine q hq
        (fun n => (c n : EReal)) (fun n => -b n) (E.form u u)
        (-γ) hc (EReal.coe_ne_top _) (EReal.coe_ne_bot _) hBneg hminus''
    have hneg : (((-(∫ x in (Q : Set (SpatialCoordinates d)), ψ x ∂(Gamma.measure u)) : ℝ)) : EReal) ≤
        liminf (fun n => ((-b n : ℝ) : EReal)) atTop := by
      simpa [γ] using hneg₀
    have hsup : limsup (fun n => (b n : EReal)) atTop ≤
        ((∫ x in (Q : Set (SpatialCoordinates d)), ψ x ∂(Gamma.measure u) : ℝ) : EReal) := by
      have hh := hneg
      have heq : (fun n => ((-b n : ℝ) : EReal)) =
          -(fun n => (b n : EReal)) := by
        funext n
        simp
      rw [heq, EReal.liminf_neg] at hh
      apply (EReal.neg_le_neg_iff).mp
      simpa only [EReal.coe_neg] using hh
    have hbconvE : Tendsto (fun n => (b n : EReal)) atTop
        (𝓝 (((∫ x in (Q : Set (SpatialCoordinates d)), ψ x ∂(Gamma.measure u)) : ℝ) : EReal)) :=
      tendsto_of_le_liminf_of_limsup_le hlow hsup
        (by obtain ⟨B', hB'⟩ := hB; exact ⟨B', hB'.mono (fun n hn => hn.2)⟩)
        (by obtain ⟨B', hB'⟩ := hB; exact ⟨-B', hB'.mono (fun n hn => hn.1)⟩)
    have hbconv : Tendsto b atTop
        (𝓝 (∫ x in (Q : Set (SpatialCoordinates d)), ψ x ∂(Gamma.measure u))) :=
      (EReal.tendsto_coe).mp hbconvE
    have hEq : b =ᶠ[atTop] (fun n =>
        ∫ x, ψ x ∂(((volume.restrict (Q : Set (SpatialCoordinates d)))).withDensity
          (fun y => ENNReal.ofReal ((a n).val y *
            ∑ i : Fin d, ((uN n : SobolevData Q).2 i y) ^ 2)))) := by
      filter_upwards [] with n
      have hd := aux_cor_energy_measures_density S a n (uN n) ψ
      dsimp [b]
      exact hd.symm
    have hGammaSupport : (Gamma.measure u).restrict (Q : Set (SpatialCoordinates d)) =
        Gamma.measure u := by
      apply Measure.restrict_eq_self_of_ae_mem
      exact (mem_ae_iff.mpr (hGammaQ u huE))
    have hbconv' : Tendsto b atTop
        (𝓝 (∫ x, ψ x ∂(Gamma.measure u))) := by
      simpa [hGammaSupport] using hbconv
    exact hbconv'.congr' hEq

  refine ⟨hrecover, ?_, ?_⟩
  · intro u uN E0 nu sigma hnu hnuQ hsigma huconv hE0 hcluster
    exact aux_cor_energy_measures_clause_b z0 R hR hQcube S a E G hEform Gamma
      hGammaQ hweighted hlower u uN E0 nu sigma hnu hnuQ hsigma huconv hE0 hcluster
  · exact aux_cor_energy_measures_clause_c z0 R hR hQcube S a E G hEform Gamma
      hGammaQ hweighted hlower hrecover
end Paper
