import Mathlib.Tactic
import SubdiffusiveProcess.Compactness.SequentialCompactness
import SubdiffusiveProcess.DirichletForm.FOTProduct
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Sobolev.CompactResponses
import SubdiffusiveProcess.Paper.cor_energy_measures
import SubdiffusiveProcess.Paper.prop_conc_controlled_forms
import SubdiffusiveProcess.Paper.prop_conc_controlled_local_orders
import SubdiffusiveProcess.Paper.prop_conc_core_measure_data
import SubdiffusiveProcess.Paper.prop_locality_recovery

/-! Deterministic prop conc controlled weighted lower data extracted upstream of process convergence.
This module does not assert concentration or invoke the process-convergence theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators ContDiff
namespace Paper
noncomputable section

/-- Extracted positive weight coefficient argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_controlled_weighted_lower_positive_weight_coefficient
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr)) (rho : SpatialCoordinates d → ℝ)
    (hcont : ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x) :
    ∃ b : PositiveCoefficient (centeredCube z r hr),
      b.val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        fun x => rho x * a.val x := by
  obtain ⟨lo, hi, hlo, _hhi, hb⟩ := Paper.aux_prop_conc_controlled_local_orders_weight_bounds_on z r hr rho hcont hpos
  have hm : MemLp rho ∞ (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    apply memLp_top_of_bound
      ((hcont.mono subset_closure).aestronglyMeasurable (centeredCube z r hr).isOpen.measurableSet) hi
    filter_upwards [ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (hpos x (subset_closure hx))]
    exact (hb x (subset_closure hx)).2
  have hmprod : MemLp (fun x => rho x * a.val x) ∞
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    (Lp.memLp a.val).mul' hm
  let bval := hmprod.toLp (fun x => rho x * a.val x)
  have hba : (bval : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        fun x => rho x * a.val x := hmprod.coeFn_toLp
  have hbpos : ∃ c : ℝ, 0 < c ∧ ∀ᵐ x ∂volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d)), c ≤ bval x := by
    obtain ⟨c, hc, hca⟩ := a.property
    refine ⟨lo * c, mul_pos hlo hc, ?_⟩
    filter_upwards [hba, hca,
      ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hbx hax hx
    rw [hbx]
    exact mul_le_mul (hb x (subset_closure hx)).1 hax hc.le
      (hpos x (subset_closure hx)).le
  exact ⟨⟨bval, hbpos⟩, hba⟩

/-- Extracted weighted response integral argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_controlled_weighted_lower_weighted_response_integral
    {d : ℕ} {Q : Opens (SpatialCoordinates d)} (S : ResponseSpace Q)
    (a b : PositiveCoefficient Q) (rho : SpatialCoordinates d → ℝ)
    (hweight : b.val =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      fun x => rho x * a.val x) (w : S.space) :
    responseForm S b w w =
      ∫ x in (Q : Set (SpatialCoordinates d)), rho x *
        (a.val x * ∑ i : Fin d, ((w : SobolevData Q).2 i x) ^ 2) := by
  rw [← aux_cor_energy_measures_energy_integral S (fun _ => b) 0 w]
  apply integral_congr_ae
  filter_upwards [hweight] with x hx
  rw [hx, mul_assoc]

/-- Extracted le liminf of subsubsequence argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_controlled_weighted_lower_le_liminf_of_subsubsequence (f : ℕ → EReal) (L : EReal)
    (hsub : ∀ tau : ℕ → ℕ, StrictMono tau → ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      L ≤ liminf (fun n => f (tau (sigma n))) atTop) :
    L ≤ liminf f atTop := by
  apply (le_liminf_iff).mpr
  intro y hy
  by_contra hn
  have hf : ∃ᶠ n in atTop, f n ≤ y := by simpa only [Filter.Frequently, not_le] using hn
  obtain ⟨tau, htau, hftau⟩ := extraction_of_frequently_atTop hf
  obtain ⟨sigma, _hsigma, hL⟩ := hsub tau htau
  have hupper : liminf (fun n => f (tau (sigma n))) atTop ≤ y :=
    liminf_le_of_frequently_le (Frequently.of_forall fun n => hftau (sigma n))
  exact (not_le_of_gt hy) (hL.trans hupper)

variable {d : ℕ} {hd : 2 ≤ d}
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, DirichletForm.IsCoreOn F.toClosedForm
          (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      DirichletForm.HasEnergyMeasure F)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)

include BD BDQ EM hcontract

/-- Extracted controlled weighted identify argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_controlled_weighted_lower_controlled_weighted_identify
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a b : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : Paper.aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a)
    (B : Paper.aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S b)
    {G F : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
    (hA : Paper.aux_prop_conc_controlled_forms_mosco_data (centeredCube z r hr) S a G)
    (hB : Paper.aux_prop_conc_controlled_forms_mosco_data (centeredCube z r hr) S b F)
    (E EF : _root_.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hF : ∀ u, EF.energy u = limitFormEnergy F u)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (rho : SpatialCoordinates d → ℝ)
    (hcont : ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x)
    (hweight : ∀ n, (b n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => rho x * (a n).val x) :
    ∀ u ∈ limitFormDomain G, limitFormEnergy F u = (∫ x, rho x ∂(Gamma.measure u) : ℝ) := by
  obtain ⟨lo, hi, hlo, hhi, hb⟩ := Paper.aux_prop_conc_controlled_local_orders_weight_bounds_on z r hr rho hcont hpos
  obtain ⟨hdom, hfcore⟩ := Paper.aux_prop_conc_controlled_local_orders_controlled_weight_core hA hB E.toClosedForm EF.toClosedForm
    hE hF hcore rho hweight lo hi hlo hhi.le (fun x hx => hb x (subset_closure hx))
  have hlocal := Paper.aux_prop_conc_controlled_local_orders_controlled_core_locality hS B hB EF.toClosedForm hF
  have hstrong := (BD z r hr EF).isStronglyLocal_of_onCore
    (Paper.aux_prop_conc_core_measure_data_isRegular_of_core (centeredCube z r hr) EF.toClosedForm hfcore)
    (BDQ z r hr EF hfcore hlocal)
  obtain ⟨GammaF, _hsupp⟩ := Paper.aux_prop_conc_core_measure_data_energy_measure_of_locality z r hr EF
    (EM z r hr EF) hfcore hstrong
  exact Paper.prop_conc_controlled_local_orders hS A B hA hB E EF hE hF
    hcore hfcore hdom Gamma GammaF rho hcont hpos hweight

/-- Extracted controlled weighted cluster lower argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_controlled_weighted_lower_controlled_weighted_cluster_lower
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a b : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : Paper.aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a)
    (B : Paper.aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S b)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (rho : SpatialCoordinates d → ℝ)
    (hcont : ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x)
    (hweight : ∀ n, (b n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => rho x * (a n).val x)
    (wN : ℕ → S.space) (w : DomainL2 (centeredCube z r hr)) (hw : w ∈ limitFormDomain G)
    (hWeak : ∀ f, Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      (∫ x, rho x ∂(Gamma.measure w) : ℝ) ≤
        liminf (fun n => (responseForm S (b (sigma n))
          (wN (sigma n)) (wN (sigma n)) : EReal)) atTop := by
  obtain ⟨F⟩ := Paper.aux_prop_conc_controlled_forms_form_cluster_exists hS B
    (fun n => hcontract z r hr S hS (b n))
  let A' : Paper.aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S (fun n => a (F.sigma n)) :=
    Paper.aux_prop_conc_controlled_forms_controls_reindex A F.sigma
  let B' : Paper.aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S (fun n => b (F.sigma n)) :=
    Paper.aux_prop_conc_controlled_forms_controls_reindex B F.sigma
  have hA' := Paper.prop_conc_controlled_forms hS A' (fun n => GN (F.sigma n)) G
    (fun n => hGN (F.sigma n)) (hConv.comp F.sigma_strict.tendsto_atTop)
  have hB' : Paper.aux_prop_conc_controlled_forms_mosco_data (centeredCube z r hr) S
      (fun n => b (F.sigma n)) F.operator := ⟨F.symmetric, F.lower, F.recovery⟩
  have hid := Paper.aux_prop_conc_controlled_weighted_lower_controlled_weighted_identify BD BDQ EM hcontract hS A' B'
    hA' hB' E F.form hE F.energy_eq hcore Gamma rho hcont hpos
    (fun n => hweight (F.sigma n)) w hw
  refine ⟨F.sigma, F.sigma_strict, ?_⟩
  rw [← hid]
  exact F.lower (fun n => wN (F.sigma n)) w
    (fun f => (hWeak f).comp F.sigma_strict.tendsto_atTop)

/-- Extracted controlled weighted lower argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_controlled_weighted_lower_controlled_weighted_lower
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a b : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : Paper.aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (rho : SpatialCoordinates d → ℝ)
    (hcont : ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hpos : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x)
    (hweight : ∀ n, (b n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => rho x * (a n).val x)
    (wN : ℕ → S.space) (w : DomainL2 (centeredCube z r hr)) (hw : w ∈ limitFormDomain G)
    (hWeak : ∀ f, Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) :
    (∫ x, rho x ∂(Gamma.measure w) : ℝ) ≤
      liminf (fun n => (responseForm S (b n) (wN n) (wN n) : EReal)) atTop := by
  obtain ⟨lo, hi, hlo, hhi, hb⟩ := Paper.aux_prop_conc_controlled_local_orders_weight_bounds_on z r hr rho hcont hpos
  have hLower : ∀ n, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      lo * (a n).val x ≤ (b n).val x := by
    intro n
    filter_upwards [hweight n, aux_prop_locality_recovery_coeff_nonneg (a n),
      ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx hax hxQ
    rw [hx]
    exact mul_le_mul_of_nonneg_right (hb x (subset_closure hxQ)).1 hax
  have hUpper : ∀ n, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (b n).val x ≤ hi * (a n).val x := by
    intro n
    have h := Paper.aux_prop_conc_controlled_local_orders_coefficient_weight_upper (a n) (b n) rho (hweight n)
      (centeredCube z r hr : Set (SpatialCoordinates d)) hi
      (fun x hx => (hb x (subset_closure hx)).2)
    filter_upwards [h, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx hxQ
    exact hx hxQ
  obtain ⟨B⟩ : Nonempty (Paper.aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S b) :=
    ⟨Paper.aux_prop_conc_controlled_forms_analytic_controls_reindex_weight A b id lo hi hlo hhi.le hLower hUpper⟩
  apply Paper.aux_prop_conc_controlled_weighted_lower_le_liminf_of_subsubsequence
  intro tau htau
  exact Paper.aux_prop_conc_controlled_weighted_lower_controlled_weighted_cluster_lower BD BDQ EM hcontract hS
    (Paper.aux_prop_conc_controlled_forms_controls_reindex A tau) (Paper.aux_prop_conc_controlled_forms_controls_reindex B tau)
    (fun n => GN (tau n)) G (fun n => hGN (tau n)) (hConv.comp htau.tendsto_atTop)
    E hE hcore Gamma rho hcont hpos (fun n => hweight (tau n))
    (fun n => wN (tau n)) w hw (fun f => (hWeak f).comp htau.tendsto_atTop)

/-- Extracted controlled weighted input argument from the pre-convergence deterministic proof. -/
theorem prop_conc_controlled_weighted_lower
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : Paper.aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm) :
    ∀ rho : SpatialCoordinates d → ℝ,
      ContinuousOn rho (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
      (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), 0 < rho x) →
      ∀ sigma : ℕ → ℕ, StrictMono sigma →
      ∀ (wN : ℕ → S.space) (w : DomainL2 (centeredCube z r hr)), w ∈ limitFormDomain G →
      (∀ f, Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      (((∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), rho x ∂(Gamma.measure w)) : ℝ) : EReal) ≤
        liminf (fun n =>
          (((∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), rho x *
            ((a (sigma n)).val x * ∑ i : Fin d,
              ((wN (sigma n) : SobolevData (centeredCube z r hr)).2 i x) ^ 2)) : ℝ) : EReal)) atTop := by
  intro rho hcont hpos sigma hsigma wN w hw hweak
  choose b hb using fun n => Paper.aux_prop_conc_controlled_weighted_lower_positive_weight_coefficient z r hr (a n) rho hcont hpos
  have h := Paper.aux_prop_conc_controlled_weighted_lower_controlled_weighted_lower BD BDQ EM hcontract hS
    (Paper.aux_prop_conc_controlled_forms_controls_reindex A sigma) (fun n => GN (sigma n)) G
    (fun n => hGN (sigma n)) (hConv.comp hsigma.tendsto_atTop) E hE hcore Gamma
    rho hcont hpos (fun n => hb (sigma n)) (fun n => wN (sigma n)) w hw
    (fun f => (hweak f).comp hsigma.tendsto_atTop)
  have hfun : (fun n => (responseForm S (b (sigma n)) (wN (sigma n)) (wN (sigma n)) : EReal)) =
      (fun n => (((∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), rho x *
        ((a (sigma n)).val x * ∑ i : Fin d,
          ((wN (sigma n) : SobolevData (centeredCube z r hr)).2 i x) ^ 2)) : ℝ) : EReal)) := by
    funext n
    rw [Paper.aux_prop_conc_controlled_weighted_lower_weighted_response_integral S (a (sigma n)) (b (sigma n)) rho (hb (sigma n))]
  rw [hfun] at h
  obtain ⟨C, hC⟩ := hcore
  have hsupp := Paper.aux_prop_conc_core_measure_data_energy_measure_support Gamma
    (centeredCube z r hr).isOpen.measurableSet hC
    (Paper.aux_prop_conc_core_measure_data_domain_mem_of_energy E.toClosedForm G hE hw)
  simpa only [Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hsupp)] using h

end
end Paper
