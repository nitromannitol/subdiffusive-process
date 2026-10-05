module

public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.BoundaryPackaging
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.VariationalResponses.ResponseMarkov
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.VariationalResponses.MeshError
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Variational.LocalizedL2
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import SubdiffusiveProcess.Paper.prop_gluing_replacement_patch
public import SubdiffusiveProcess.Paper.prop_locality
public import SubdiffusiveProcess.Paper.obl_FOT
public import SubdiffusiveProcess.Paper.conv_energy_measure_normalization
public import SubdiffusiveProcess.Paper.lem_truncation

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

/-- Additivity of the cross energy measure, in the second argument, over a
finite sum, evaluated on a fixed set. -/
lemma aux_prop_gluing_replacement_localization_cross_sum_right
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Γ : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    (B : Set (SpatialCoordinates d)) (u : DomainL2 Q) (hu : u ∈ E.domain)
    {ι : Type*} (s : Finset ι) (f : ι → DomainL2 Q) (hf : ∀ i ∈ s, f i ∈ E.domain) :
    Γ.cross u (∑ i ∈ s, f i) B = ∑ i ∈ s, Γ.cross u (f i) B := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : Γ.cross u (0 : DomainL2 Q) = 0 := by
      have h := Γ.cross_smul_right 0 u hu (0 : DomainL2 Q) E.domain.zero_mem
      simpa using h
    simp [h0]
  | @insert a s ha ih =>
    have hus : (∑ i ∈ s, f i) ∈ E.domain :=
      E.domain.sum_mem (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      Γ.cross_add_right u hu (f a) (hf a (Finset.mem_insert_self a s)) (∑ i ∈ s, f i) hus,
      add_apply, ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

/-- Additivity of the cross energy measure, in the first argument, over a
finite sum, evaluated on a fixed set. -/
lemma aux_prop_gluing_replacement_localization_cross_sum_left
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Γ : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    (B : Set (SpatialCoordinates d)) (v : DomainL2 Q) (hv : v ∈ E.domain)
    {ι : Type*} (s : Finset ι) (f : ι → DomainL2 Q) (hf : ∀ i ∈ s, f i ∈ E.domain) :
    Γ.cross (∑ i ∈ s, f i) v B = ∑ i ∈ s, Γ.cross (f i) v B := by
  classical
  have hsum : (∑ i ∈ s, f i) ∈ E.domain := E.domain.sum_mem hf
  rw [Γ.cross_symm _ hsum v hv,
    aux_prop_gluing_replacement_localization_cross_sum_right E Γ B v hv s f hf]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Γ.cross_symm v hv (f i) (hf i hi)]

/-- Energy-norm convergence of a sequence in `D(E)` forces convergence, at a
fixed measurable set, of the energy measure. This is the Cauchy--Schwarz
continuity of `Γ.measure` along energy-norm limits. -/
lemma aux_prop_gluing_replacement_localization_measure_tendsto
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Γ : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    (u : DomainL2 Q) (hu : u ∈ E.domain)
    (w : ℕ → DomainL2 Q) (hw : ∀ n, w n ∈ E.domain)
    (hconv : Tendsto (fun n => E.energyNormSq (u - w n)) atTop (𝓝 0))
    (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B) :
    Tendsto (fun n => (Γ.measure (w n) B).toReal) atTop
      (𝓝 ((Γ.measure u B).toReal)) := by
  set e : ℕ → DomainL2 Q := fun n => w n - u with he_def
  have hedom : ∀ n, e n ∈ E.domain := fun n => E.domain.sub_mem (hw n) hu
  have hweq : ∀ n, u + e n = w n := fun n => by simp [he_def]
  have hconv' : Tendsto (fun n => E.energyNormSq (e n)) atTop (𝓝 0) := by
    have hswap : ∀ n, E.energyNormSq (e n) = E.energyNormSq (u - w n) := by
      intro n
      have hen : e n = -(u - w n) := by
        simp only [he_def]
        exact (neg_sub u (w n)).symm
      rw [hen, E.energyNormSq_neg (E.domain.sub_mem hu (hw n))]
    simpa [hswap] using hconv
  have hform_nonneg : ∀ n, 0 ≤ E.form (e n) (e n) := fun n => E.form_nonneg (e n) (hedom n)
  have hform_le : ∀ n, E.form (e n) (e n) ≤ E.energyNormSq (e n) :=
    fun _ => E.form_le_energyNormSq
  have hform_tendsto : Tendsto (fun n => E.form (e n) (e n)) atTop (𝓝 0) :=
    squeeze_zero hform_nonneg hform_le hconv'
  have hbound1 : ∀ n, |Γ.cross u (e n) B| ≤
      Real.sqrt ((Γ.measure u B).toReal) * Real.sqrt (E.form (e n) (e n)) := by
    intro n
    have h1 := Γ.abs_cross_le u hu (e n) (hedom n) B hB
    have h2 : (Γ.measure (e n) B).toReal ≤ E.form (e n) (e n) :=
      Γ.toReal_measure_le_form (hedom n) B
    have h3 : Real.sqrt ((Γ.measure (e n) B).toReal) ≤ Real.sqrt (E.form (e n) (e n)) :=
      Real.sqrt_le_sqrt h2
    calc |Γ.cross u (e n) B|
        ≤ Real.sqrt ((Γ.measure u B).toReal) * Real.sqrt ((Γ.measure (e n) B).toReal) := h1
      _ ≤ Real.sqrt ((Γ.measure u B).toReal) * Real.sqrt (E.form (e n) (e n)) := by
          gcongr
  have hbound1' : Tendsto (fun n => Real.sqrt ((Γ.measure u B).toReal) *
      Real.sqrt (E.form (e n) (e n))) atTop (𝓝 0) := by
    have hsqrt0 : Tendsto (fun n => Real.sqrt (E.form (e n) (e n))) atTop (𝓝 0) := by
      have hc := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hform_tendsto
      simpa [Function.comp_def, Real.sqrt_zero] using hc
    have := hsqrt0.const_mul (Real.sqrt ((Γ.measure u B).toReal))
    simpa using this
  have hcross1 : Tendsto (fun n => Γ.cross u (e n) B) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) hbound1'
    rw [Real.norm_eq_abs]
    exact hbound1 n
  have hbound2 : ∀ n, (Γ.measure (e n) B).toReal ≤ E.form (e n) (e n) :=
    fun n => Γ.toReal_measure_le_form (hedom n) B
  have hcross2 : Tendsto (fun n => Γ.cross (e n) (e n) B) atTop (𝓝 0) := by
    have heq : ∀ n, Γ.cross (e n) (e n) B = (Γ.measure (e n) B).toReal :=
      fun n => Γ.cross_self (e n) (hedom n) B hB
    simp only [heq]
    exact squeeze_zero (fun _ => ENNReal.toReal_nonneg) hbound2 hform_tendsto
  have hexpand : ∀ n, Γ.cross (w n) (w n) B =
      Γ.cross u u B + 2 * Γ.cross u (e n) B + Γ.cross (e n) (e n) B := by
    intro n
    have h := Γ.cross_add_self_apply hu (hedom n) B
    rw [hweq n] at h
    exact h
  have hlim : Tendsto (fun n => Γ.cross u u B + 2 * Γ.cross u (e n) B +
      Γ.cross (e n) (e n) B) atTop (𝓝 (Γ.cross u u B + 2 * 0 + 0)) :=
    (tendsto_const_nhds.add (hcross1.const_mul 2)).add hcross2
  simp only [mul_zero, add_zero] at hlim
  have hfinal : Tendsto (fun n => Γ.cross (w n) (w n) B) atTop (𝓝 (Γ.cross u u B)) := by
    simpa only [hexpand] using hlim
  have hueq : Γ.cross u u B = (Γ.measure u B).toReal := Γ.cross_self u hu B hB
  have hweq2 : ∀ n, Γ.cross (w n) (w n) B = (Γ.measure (w n) B).toReal :=
    fun n => Γ.cross_self (w n) (hw n) B hB
  simp only [hweq2] at hfinal
  simpa [hueq] using hfinal



theorem prop_gluing_replacement_localization
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Γ : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    (m : ℕ) (cent : Fin m → SpatialCoordinates d) (rad : Fin m → ℝ)
    (hrad : ∀ i : Fin m, 0 < rad i)
    (_hcellQ : ∀ i : Fin m,
      closure (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d)))
    (hdisj : Pairwise fun i j : Fin m =>
      Disjoint (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d))
        (centeredCube (cent j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (Dq : Fin m → Submodule ℝ (DomainL2 Q))
    (hDq : ∀ i : Fin m, _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) (Dq i))
    (V : DomainL2 Q) (hV : V ∈ E.domain)
    (Vc : SpatialCoordinates d → ℝ)
    (hVcont : ContinuousOn Vc (closure (Q : Set (SpatialCoordinates d))))
    (hVrep : (V : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] Vc)
    (Ui : Fin m → SpatialCoordinates d → ℝ)
    (UiL2 : Fin m → DomainL2 Q)
    (hUiDomain : ∀ i : Fin m, UiL2 i ∈ E.domain)
    (hUiRep : ∀ i : Fin m, (UiL2 i : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] Ui i)
    (hUicont : ∀ i : Fin m, ContinuousOn (Ui i)
      (closure (Q : Set (SpatialCoordinates d))))
    (hUibdry : ∀ i : Fin m,
      ∀ x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)), Ui i x = Vc x)
    (_hUiFace : ∀ i : Fin m, Γ.measure (UiL2 i)
      (frontier (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d))) = 0)
    (hZeroTrace : ∀ i : Fin m, ∀ (w : DomainL2 Q), w ∈ E.domain →
      ∀ (wc : SpatialCoordinates d → ℝ),
      ContinuousOn wc (closure (Q : Set (SpatialCoordinates d))) →
      ((w : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] wc) →
      (∀ x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)), wc x = 0) →
      ∀ (wq : DomainL2 Q),
      ((wq : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
          Set.indicator (closure (centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d))) wc) →
      wq ∈ Dq i ∧ E.form wq wq = (Γ.measure w
        (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d))).toReal)
    (V' : DomainL2 Q) (V'c : SpatialCoordinates d → ℝ)
    (hV'rep : (V' : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V'c)
    (hV'out : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
      x ∉ ⋃ i : Fin m, (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)) → V'c x = Vc x)
    (hV'in : ∀ i : Fin m,
      ∀ x ∈ (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)), V'c x = Ui i x)
    (hpatch : V' ∈ E.domain ∧
      ContinuousOn V'c (closure (Q : Set (SpatialCoordinates d)))) :
    (∀ i : Fin m, ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
        B ⊆ (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d)) →
        Γ.measure V' B = Γ.measure (UiL2 i) B) ∧
      (∀ B : Set (SpatialCoordinates d), MeasurableSet B →
        B ⊆ (Q : Set (SpatialCoordinates d)) \
          (⋃ i : Fin m, (centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d))) →
        Γ.measure V' B = Γ.measure V B) := by
  classical
  have hcellopen : ∀ i : Fin m,
      IsOpen (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) :=
    fun i => (centeredCube (cent i) (rad i) (hrad i)).isOpen
  constructor
  · -- Goal 1: agreement with the harmonic cell datum on each open cell.
    intro i B hB hBsub
    have heq : (V' : SpatialCoordinates d → ℝ)
        =ᵐ[(volume.restrict (Q : Set (SpatialCoordinates d))).restrict
            (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))]
        (UiL2 i : SpatialCoordinates d → ℝ) := by
      have h1 := ae_restrict_of_ae
        (s := (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))) hV'rep
      have h2 := ae_restrict_of_ae
        (s := (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)))
        (hUiRep i)
      have h3 := ae_restrict_mem (μ := volume.restrict (Q : Set (SpatialCoordinates d)))
        (hcellopen i).measurableSet
      filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
      rw [hx1, hx2]
      exact hV'in i x hx3
    have hloc := Γ.locality V' hpatch.1 (UiL2 i) (hUiDomain i)
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
      (hcellopen i) heq
    have hev := congrArg (fun ν : Measure (SpatialCoordinates d) => ν B) hloc
    simpa only [Measure.restrict_apply hB, Set.inter_eq_left.mpr hBsub] using hev
  · -- Goal 2: agreement with the original datum outside the open cell union.
    -- Reconstruct the correction pieces of the patched replacement.
    let corr : Fin m → DomainL2 Q := fun i =>
      localizeL2
        ((isClosed_closure : IsClosed (closure (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d)))).measurableSet)
        (UiL2 i - V)
    have hdiff : ∀ i : Fin m,
        ((UiL2 i - V : DomainL2 Q) : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
            (fun x => Ui i x - Vc x) := by
      intro i
      filter_upwards [Lp.coeFn_sub (UiL2 i) V, hUiRep i, hVrep] with x hsub hui hv
      calc
        ((UiL2 i - V : DomainL2 Q) : SpatialCoordinates d → ℝ) x =
            ((UiL2 i : DomainL2 Q) : SpatialCoordinates d → ℝ) x -
              ((V : DomainL2 Q) : SpatialCoordinates d → ℝ) x := hsub
        _ = Ui i x - Vc x := by rw [hui, hv]
    have hcorr_rep : ∀ i : Fin m,
        ((corr i : DomainL2 Q) : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
            Set.indicator
              (closure (centeredCube (cent i) (rad i) (hrad i) :
                Set (SpatialCoordinates d)))
              (fun x => Ui i x - Vc x) := by
      intro i
      let hs : MeasurableSet (closure (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d))) :=
        (isClosed_closure : IsClosed (closure (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d)))).measurableSet
      change localizeL2 hs (UiL2 i - V) =ᵐ[_] _
      filter_upwards [localizeL2_coeFn hs (UiL2 i - V), hdiff i] with x hx hxi
      rw [hx]
      by_cases hsx : x ∈ closure (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d))
      · simp only [Set.indicator_of_mem hsx]
        exact hxi
      · simp only [Set.indicator_of_notMem hsx]
    have hcorr_killed : ∀ i : Fin m, corr i ∈ Dq i := by
      intro i
      have hzero := hZeroTrace i (UiL2 i - V)
        (E.domain.sub_mem (hUiDomain i) hV)
        (fun x => Ui i x - Vc x)
        ((hUicont i).sub hVcont)
        (hdiff i)
        (by
          intro x hx
          rw [hUibdry i x hx]
          ring)
        (corr i)
        (hcorr_rep i)
      exact hzero.1
    have hcorr_domain : ∀ i : Fin m, corr i ∈ E.domain := by
      intro i
      exact (hDq i).le_domain (hcorr_killed i)
    -- Each correction has energy measure supported inside its own open cell.
    have hcorr_compl : ∀ i : Fin m,
        Γ.measure (corr i)
          ((centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d))ᶜ) = 0 := by
      intro i
      obtain ⟨wseq, hwcore, hwconv⟩ := (hDq i).exists_seq (hcorr_killed i)
      have hzero_seq : ∀ n, Γ.measure (wseq n)
          ((centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d))ᶜ) = 0 := by
        intro n
        obtain ⟨f, hfcont, _hfcs, hfsupp, hfae⟩ := (hwcore n).2
        have hmn := Γ.measure_compl_tsupport (wseq n) (hwcore n).mem_domain f hfcont hfae
        have hsub : (centeredCube (cent i) (rad i) (hrad i) :
              Set (SpatialCoordinates d))ᶜ ⊆ (tsupport f)ᶜ :=
          Set.compl_subset_compl.mpr hfsupp
        exact measure_mono_null hsub hmn
      have hBcompl : MeasurableSet
          ((centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d))ᶜ) :=
        (hcellopen i).isClosed_compl.measurableSet
      have htendsto := aux_prop_gluing_replacement_localization_measure_tendsto E Γ
        (corr i) (hcorr_domain i) wseq (fun n => (hwcore n).mem_domain) hwconv
        ((centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))ᶜ) hBcompl
      have htendsto' : Tendsto (fun n => (Γ.measure (wseq n)
          ((centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d))ᶜ)).toReal) atTop (𝓝 0) := by
        have hz : ∀ n, (Γ.measure (wseq n)
            ((centeredCube (cent i) (rad i) (hrad i) :
              Set (SpatialCoordinates d))ᶜ)).toReal = 0 := by
          intro n
          rw [hzero_seq n]
          simp
        simp [hz]
      have hval : (Γ.measure (corr i)
          ((centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d))ᶜ)).toReal = 0 :=
        tendsto_nhds_unique htendsto htendsto'
      have hne : Γ.measure (corr i)
          ((centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d))ᶜ) ≠ ⊤ :=
        Γ.measure_ne_top (hcorr_domain i) _
      rcases (ENNReal.toReal_eq_zero_iff _).mp hval with h | h
      · exact h
      · exact absurd h hne
    intro B hB hBsub
    have hB_compl : ∀ i : Fin m, B ⊆ (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d))ᶜ := by
      intro i x hxB hxc
      exact (hBsub hxB).2 (Set.mem_iUnion.mpr ⟨i, hxc⟩)
    have hcorrB : ∀ i : Fin m, Γ.measure (corr i) B = 0 := by
      intro i
      exact measure_mono_null (hB_compl i) (hcorr_compl i)
    have hcrossVcorr : ∀ i : Fin m, Γ.cross V (corr i) B = 0 := by
      intro i
      have h1 := Γ.abs_cross_le V hV (corr i) (hcorr_domain i) B hB
      rw [hcorrB i] at h1
      simp only [ENNReal.toReal_zero, Real.sqrt_zero, mul_zero] at h1
      exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
    have hcrossCC : ∀ i j : Fin m, Γ.cross (corr i) (corr j) B = 0 := by
      intro i j
      have h1 := Γ.abs_cross_le (corr i) (hcorr_domain i) (corr j) (hcorr_domain j) B hB
      rw [hcorrB i] at h1
      simp only [ENNReal.toReal_zero, Real.sqrt_zero, zero_mul] at h1
      exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
    have hSdom : (∑ i : Fin m, corr i) ∈ E.domain :=
      E.domain.sum_mem (fun i _ => hcorr_domain i)
    have hcrossVS : Γ.cross V (∑ i : Fin m, corr i) B = 0 := by
      rw [aux_prop_gluing_replacement_localization_cross_sum_right E Γ B V hV
        Finset.univ corr (fun i _ => hcorr_domain i)]
      exact Finset.sum_eq_zero (fun i _ => hcrossVcorr i)
    have hcrossSS : Γ.cross (∑ i : Fin m, corr i) (∑ i : Fin m, corr i) B = 0 := by
      rw [aux_prop_gluing_replacement_localization_cross_sum_left E Γ B
        (∑ i : Fin m, corr i) hSdom Finset.univ corr (fun i _ => hcorr_domain i)]
      apply Finset.sum_eq_zero
      intro i _
      rw [aux_prop_gluing_replacement_localization_cross_sum_right E Γ B (corr i)
        (hcorr_domain i) Finset.univ corr (fun i _ => hcorr_domain i)]
      exact Finset.sum_eq_zero (fun j _ => hcrossCC i j)
    -- Reconstruct the patched replacement `V' = V + Σ corr i`.
    let W : DomainL2 Q := V + ∑ i : Fin m, corr i
    have hsumrep :
        ((∑ i : Fin m, corr i : DomainL2 Q) : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
            (fun x => ∑ i : Fin m,
              Set.indicator
                (closure (centeredCube (cent i) (rad i) (hrad i) :
                  Set (SpatialCoordinates d)))
                (fun y => Ui i y - Vc y) x) := by
      have hsum := lane2_Lp_coeFn_sum corr (Finset.univ)
      have hall := (ae_all_iff.2 (fun i => hcorr_rep i))
      filter_upwards [hsum, hall] with x hx hxi
      rw [hx]
      apply Finset.sum_congr rfl
      intro i hi
      exact hxi i
    have hWrep :
        (W : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
            (fun x => Vc x + ∑ i : Fin m,
              Set.indicator
                (closure (centeredCube (cent i) (rad i) (hrad i) :
                  Set (SpatialCoordinates d)))
                (fun y => Ui i y - Vc y) x) := by
      have hadd := Lp.coeFn_add V (∑ i : Fin m, corr i)
      filter_upwards [hadd, hsumrep, hVrep] with x hx hsum hv
      rw [hx]
      simp only [Pi.add_apply]
      rw [hv, hsum]
    have hpoint : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
        Vc x + ∑ i : Fin m,
          Set.indicator
            (closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)))
            (fun y => Ui i y - Vc y) x = V'c x := by
      intro x hxQ
      by_cases hxu : x ∈ ⋃ i : Fin m, (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d))
      · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxu
        have hsum0 : (∑ j : Fin m,
            Set.indicator
              (closure (centeredCube (cent j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
              (fun y => Ui j y - Vc y) x) =
            Set.indicator
              (closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)))
              (fun y => Ui i y - Vc y) x := by
          refine (Finset.sum_eq_single (s := (Finset.univ : Finset (Fin m)))
            (f := fun j : Fin m =>
              Set.indicator
                (closure (centeredCube (cent j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
                (fun y => Ui j y - Vc y) x) i) ?_ ?_
          · intro j hj hji
            rw [Set.indicator_of_notMem]
            intro hxj
            exact (Set.disjoint_left.mp
              ((hdisj (Ne.symm hji)).closure_right (hcellopen i))) hxi hxj
          · simp
        have hsum : (∑ j : Fin m,
            Set.indicator
              (closure (centeredCube (cent j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
              (fun y => Ui j y - Vc y) x) = Ui i x - Vc x := by
          rw [hsum0, Set.indicator_of_mem (subset_closure hxi)]
        rw [hsum, hV'in i x hxi]
        ring
      · have hzero : ∀ i : Fin m,
            Set.indicator
                (closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)))
                (fun y => Ui i y - Vc y) x = 0 := by
          intro i
          by_cases hci : x ∈ closure (centeredCube (cent i) (rad i) (hrad i) :
              Set (SpatialCoordinates d))
          · have hni : x ∉ (centeredCube (cent i) (rad i) (hrad i) :
                Set (SpatialCoordinates d)) := by
              intro hxi
              exact hxu (Set.mem_iUnion.mpr ⟨i, hxi⟩)
            have hfront : x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) :
                Set (SpatialCoordinates d)) := by
              rw [(hcellopen i).frontier_eq]
              exact ⟨hci, hni⟩
            rw [Set.indicator_of_mem hci, sub_eq_zero.mpr (hUibdry i x hfront)]
          · exact Set.indicator_of_notMem hci _
        rw [Finset.sum_eq_zero (fun i _ => hzero i), add_zero, hV'out x hxQ hxu]
    have hWV' : W = V' := by
      apply Lp.ext
      filter_upwards [hWrep, hV'rep,
        ae_restrict_mem (Q.isOpen.measurableSet)] with x hx hxp hxQ
      rw [hx, hxp]
      exact hpoint x (subset_closure hxQ)
    -- Bilinear expansion at `B`, using the vanishing cross terms.
    have hVSdom : (V + ∑ i : Fin m, corr i) ∈ E.domain := E.domain.add_mem hV hSdom
    have hcrossexpand := Γ.cross_add_self_apply hV hSdom B
    rw [hcrossVS, hcrossSS, mul_zero, add_zero, add_zero] at hcrossexpand
    have hcsW : Γ.cross (V + ∑ i : Fin m, corr i) (V + ∑ i : Fin m, corr i) B =
        (Γ.measure (V + ∑ i : Fin m, corr i) B).toReal :=
      Γ.cross_self (V + ∑ i : Fin m, corr i) hVSdom B hB
    have hcsV : Γ.cross V V B = (Γ.measure V B).toReal := Γ.cross_self V hV B hB
    have htoReal : (Γ.measure (V + ∑ i : Fin m, corr i) B).toReal =
        (Γ.measure V B).toReal := by
      rw [← hcsW, hcrossexpand, hcsV]
    have hWeq : (V + ∑ i : Fin m, corr i : DomainL2 Q) = V' := hWV'
    rw [hWeq] at htoReal hVSdom
    have hne1 : Γ.measure V' B ≠ ⊤ := Γ.measure_ne_top hpatch.1 B
    have hne2 : Γ.measure V B ≠ ⊤ := Γ.measure_ne_top hV B
    exact (ENNReal.toReal_eq_toReal_iff' hne1 hne2).mp htoReal

end SubdiffusiveProcess.Paper
