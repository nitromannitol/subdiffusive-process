import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.conv_represented_sequence
import SubdiffusiveProcess.Paper.prop_response_compact
import SubdiffusiveProcess.Paper.prop_boundary
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Metric
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem aux_lem_local_normalizations_full_cutoff_cutoff_meas
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : Measurable H) (N : ℕ) :
    Measurable (fun p : BilateralField d × SpatialCoordinates d =>
      cutoffCoefficient M H p.1 N p.2) := by
  unfold cutoffCoefficient cutoffPotential
  have hHeval : Measurable (fun p : BilateralField d × SpatialCoordinates d =>
      (H p.1) p.2) := by
    exact ContinuousEval.continuous_eval.measurable.comp
      ((hH.comp measurable_fst).prodMk measurable_snd)
  fun_prop

theorem aux_lem_local_normalizations_full_cutoff_energy_component_meas
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : Measurable H) (P : Measure (BilateralField d)) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (u : weakSobolevGraph (centeredCube z r hr)) (i : Fin d) :
    AEStronglyMeasurable
      (fun omega : BilateralField d =>
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          (cutoffPositiveCoefficient M H omega N z hr).val x *
            ((u.val.2 i) x * (u.val.2 i) x)) P := by
  let ν : Measure (SpatialCoordinates d) :=
    volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))
  have hcut : Measurable
      (fun p : BilateralField d × SpatialCoordinates d =>
        cutoffCoefficient M H p.1 N p.2) :=
    aux_lem_local_normalizations_full_cutoff_cutoff_meas M H hH N
  have hgrad : AEStronglyMeasurable
    (fun p : BilateralField d × SpatialCoordinates d =>
        (u.val.2 i).val p.2) (P.prod ν) := by
    exact (u.val.2 i).val.aestronglyMeasurable.comp_snd
  have hprod : AEStronglyMeasurable
      (fun p : BilateralField d × SpatialCoordinates d =>
        cutoffCoefficient M H p.1 N p.2 *
          ((u.val.2 i).val p.2 * (u.val.2 i).val p.2)) (P.prod ν) := by
    exact hcut.aestronglyMeasurable.mul (hgrad.mul hgrad)
  have hint : AEStronglyMeasurable
      (fun omega : BilateralField d =>
        ∫ x, cutoffCoefficient M H omega N x *
          ((u.val.2 i) x * (u.val.2 i) x) ∂ν) P := by
    simpa only [MeasureTheory.Measure.restrict_apply_univ] using
      hprod.integral_prod_right'
  have heq : (fun omega : BilateralField d =>
      ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        (cutoffPositiveCoefficient M H omega N z hr).val x *
          ((u.val.2 i) x * (u.val.2 i) x)) =
      (fun omega : BilateralField d =>
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          cutoffCoefficient M H omega N x *
            ((u.val.2 i) x * (u.val.2 i) x)) := by
    funext omega
    letI : Fact (((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
        (closedCube z r hr : Set (SpatialCoordinates d)))) :=
      ⟨centeredCube_subset_closedCube z hr⟩
    have hnorm := normalizedContinuousPositiveCoefficient_coeFn
      (Ω := centeredCube z r hr)
      (closedCube z r hr)
      (cutoffCoefficientCM M H omega N z hr)
      (cutoffCoefficientCM_pos M H omega N z hr) 1 one_pos
    apply integral_congr_ae
    filter_upwards [hnorm, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx hxm
    have hcoef : (cutoffPositiveCoefficient M H omega N z hr).val x =
        cutoffCoefficient M H omega N x := by
      simpa [cutoffPositiveCoefficient, cutoffCoefficientCM] using hx hxm
    rw [hcoef]
  rw [heq]
  exact hint

theorem aux_lem_local_normalizations_full_cutoff_energy_meas
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : Measurable H) (P : Measure (BilateralField d)) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (u : weakSobolevGraph (centeredCube z r hr)) :
    AEStronglyMeasurable
      (fun omega : BilateralField d =>
        sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N z hr)
          u.val u.val) P := by
  change AEStronglyMeasurable
    (fun omega : BilateralField d =>
      sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N z hr)
        (u : SobolevData (centeredCube z r hr))
        (u : SobolevData (centeredCube z r hr))) P
  simp_rw [sobolevCoefficientForm_apply]
  have hsum := Finset.aestronglyMeasurable_sum (μ := P)
    (f := fun i : Fin d => fun omega : BilateralField d =>
      ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        (cutoffPositiveCoefficient M H omega N z hr).val x *
          ((u.val.2 i) x * (u.val.2 i) x))
    (Finset.univ : Finset (Fin d)) (by
      intro i hi
      exact aux_lem_local_normalizations_full_cutoff_energy_component_meas
        M H hH P N z hr u i)
  have heq :
      (∑ i : Fin d, (fun omega : BilateralField d =>
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          (cutoffPositiveCoefficient M H omega N z hr).val x *
            ((u.val.2 i) x * (u.val.2 i) x))) =
        (fun omega : BilateralField d =>
          ∑ i : Fin d,
            ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
              (cutoffPositiveCoefficient M H omega N z hr).val x *
                ((u.val.2 i) x * (u.val.2 i) x)) := by
    funext omega
    simp
  rw [← heq]
  exact hsum

theorem aux_lem_local_normalizations_full_cutoff_sInf_meas
    {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E]
    [SecondCountableTopology E]
    (P : Measure Ω) (A : Set E) (f : E → Ω → ℝ)
    (hcont : ∀ omega, Continuous (fun u => f u omega))
    (hbdd : ∀ omega, BddBelow ((fun u => f u omega) '' A))
    (hmeas : ∀ u, u ∈ A → AEStronglyMeasurable (f u) P) :
    AEStronglyMeasurable
      (fun omega => sInf ((fun u => f u omega) '' A)) P := by
  classical
  by_cases hA : A.Nonempty
  · letI : Nonempty A := hA.to_subtype
    let D : ℕ → A := TopologicalSpace.denseSeq A
    have hD : DenseRange D := TopologicalSpace.denseRange_denseSeq A
    have hEq : ∀ omega, sInf ((fun u => f u omega) '' A) =
        ⨅ n, f (D n : E) omega := by
      intro omega
      let S : Set ℝ := (fun u => f u omega) '' A
      let T : Set ℝ := Set.range (fun n => f (D n : E) omega)
      have hTsub : T ⊆ S := by
        rintro y ⟨n, rfl⟩
        exact ⟨D n, (D n).property, rfl⟩
      have hTne : T.Nonempty := ⟨f (D 0 : E) omega, ⟨0, rfl⟩⟩
      have hSne : S.Nonempty := hA.image (fun u => f u omega)
      have hTbdd : BddBelow T := (hbdd omega).mono hTsub
      have hle : sInf S ≤ sInf T :=
        csInf_le_csInf (hbdd omega) hTne hTsub
      have hge : sInf T ≤ sInf S := by
        apply le_csInf hSne
        rintro y ⟨u, hu, rfl⟩
        apply le_of_forall_pos_le_add
        intro eps heps
        have hcontA : Continuous (fun v : A => f (v : E) omega) :=
          (hcont omega).comp continuous_subtype_val
        let O : Set A := {v | f (v : E) omega < f u omega + eps}
        have hO : IsOpen O := by
          exact isOpen_lt hcontA continuous_const
        have huO : (⟨u, hu⟩ : A) ∈ O := by
          dsimp [O]
          linarith
        obtain ⟨v, ⟨n, rfl⟩, hv⟩ := hD.inter_nhds_nonempty (hO.mem_nhds huO)
        exact (csInf_le hTbdd ⟨n, rfl⟩).trans hv.le
      exact le_antisymm hle hge
    have hi : AEMeasurable (fun omega => ⨅ n, f (D n : E) omega) P := by
      exact AEMeasurable.iInf (fun n => (hmeas (D n : E) (D n).property).aemeasurable)
    have hi' : AEStronglyMeasurable (fun omega => ⨅ n, f (D n : E) omega) P :=
      hi.aestronglyMeasurable
    rw [show (fun omega => sInf ((fun u => f u omega) '' A)) =
        (fun omega => ⨅ n, f (D n : E) omega) by funext omega; exact hEq omega]
    exact hi'
  · have hzero : (fun omega => sInf ((fun u => f u omega) '' A)) =
        (fun _ => (0 : ℝ)) := by
      funext omega
      rw [not_nonempty_iff_eq_empty.mp hA]
      simp
    rw [hzero]
    fun_prop



theorem lem_local_normalizations_full_cutoff
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : Paper.in_J d)
    (Pc : Paper.in_poincare d hd Jc)
    (Xc : Paper.in_extension d hd Jc)
    (Sf : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta_lower : (1 / 2 : ℝ) < beta) (hbeta_upper : beta < 1)
    (delta0 : ℝ) (hdelta0 : 0 < delta0)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Rm : Paper.in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (HI : InfraredCharacterization M H)
    (hdelta : M.delta ≤ min 1 delta0)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (g : SpatialCoordinates d → ℝ)
    (hg : IsCellBoundaryClass beta z r g)
    (hsmooth : ContDiff ℝ ∞ g) :
    let Lam (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (N : ℕ) (omega : BilateralField d) (g : SpatialCoordinates d → ℝ) : ℝ :=
      sInf {e : ℝ | ∃ (u : weakSobolevGraph (centeredCube z r hr))
          (U : SpatialCoordinates d → ℝ),
        ContinuousOn U (closedCube z r hr : Set (SpatialCoordinates d)) ∧
        ((u.val).1 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
          (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
          U x = g x) ∧
        e = sobolevCoefficientForm
          (cutoffPositiveCoefficient M H omega N z hr) u.val u.val}
    ∀
      (hsubseq :
        ∃ Rlim : BilateralField d → ℝ,
          ∀ ψ : ℕ → ℕ, StrictMono ψ →
            ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧
              ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
                Tendsto
                  (fun n => Lam z r hr (ψ (ψ' n)) omega g) atTop
                    (𝓝 (Rlim omega))),
      ∃ Rlim : BilateralField d → ℝ,
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun N omega => Lam z r hr N omega g) atTop Rlim ∧
        (∀ R' : BilateralField d → ℝ,
          TendstoInMeasure (chaosSampleLaw M).toMeasure
            (fun N omega => Lam z r hr N omega g) atTop R' →
            R' =ᵐ[(chaosSampleLaw M).toMeasure] Rlim) := by
  dsimp
  intro hsubseq
  obtain ⟨Rlim, hRlim⟩ := hsubseq
  let μ := (chaosSampleLaw M).toMeasure
  let F : ℕ → BilateralField d → ℝ := fun N omega =>
    sInf {e : ℝ | ∃ (u : weakSobolevGraph (centeredCube z r hr))
        (U : SpatialCoordinates d → ℝ),
      ContinuousOn U (closedCube z r hr : Set (SpatialCoordinates d)) ∧
      ((u.val).1 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
      (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
        U x = g x) ∧
      e = sobolevCoefficientForm
        (cutoffPositiveCoefficient M H omega N z hr) u.val u.val}
  have hmeas : ∀ N, AEStronglyMeasurable (F N) μ := by
    intro N
    letI : MeasureTheory.IsSeparable
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := inferInstance
    letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
    letI : Fact ((2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by norm_num⟩
    letI : SecondCountableTopology
        (DomainL2 (centeredCube z r hr)) := inferInstance
    letI : SecondCountableTopology
        (Fin d → DomainL2 (centeredCube z r hr)) := inferInstance
    letI : SecondCountableTopology
        (SobolevData (centeredCube z r hr)) := inferInstance
    let A : Set (weakSobolevGraph (centeredCube z r hr)) :=
      {u | ∃ (U : SpatialCoordinates d → ℝ),
        ContinuousOn U (closedCube z r hr : Set (SpatialCoordinates d)) ∧
        ((u.val).1 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
        (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
          U x = g x)}
    let f : weakSobolevGraph (centeredCube z r hr) → BilateralField d → ℝ :=
      fun u omega => sobolevCoefficientForm
        (cutoffPositiveCoefficient M H omega N z hr) u.val u.val
    have hfcont : ∀ omega, Continuous (fun u => f u omega) := by
      intro omega
      fun_prop
    have hfbdd : ∀ omega, BddBelow ((fun u => f u omega) '' A) := by
      intro omega
      refine ⟨0, ?_⟩
      rintro e ⟨u, hu, rfl⟩
      exact sobolevCoefficientForm_nonneg
        (cutoffPositiveCoefficient M H omega N z hr) u.val
    have hfmeas : ∀ u, u ∈ A → AEStronglyMeasurable (f u) μ := by
      intro u hu
      exact aux_lem_local_normalizations_full_cutoff_energy_meas
        M H HI.1 μ N z hr u
    have hfinf := aux_lem_local_normalizations_full_cutoff_sInf_meas
      μ A f hfcont hfbdd hfmeas
    have hEq : F N = (fun omega => sInf ((fun u => f u omega) '' A)) := by
      funext omega
      dsimp [F, f, A]
      congr 1
      ext e
      constructor
      · rintro ⟨u, U, hU, hAE, hbd, rfl⟩
        exact ⟨u, ⟨U, hU, hAE, hbd⟩, rfl⟩
      · rintro ⟨u, ⟨U, hU, hAE, hbd⟩, rfl⟩
        exact ⟨u, U, hU, hAE, hbd, rfl⟩
    rw [hEq]
    exact hfinf
  have hcrit : TendstoInMeasure μ F atTop Rlim := by
    apply (exists_seq_tendstoInMeasure_atTop_iff hmeas).2
    intro ψ hψ
    simpa [F, μ] using hRlim ψ hψ
  refine ⟨Rlim, ?_, ?_⟩
  · simpa [F, μ] using hcrit
  · intro R' hR'
    exact (tendstoInMeasure_ae_unique (μ := μ) (f := F) (u := atTop)
      (g := Rlim) (h := R') hcrit hR').symm

end Paper


