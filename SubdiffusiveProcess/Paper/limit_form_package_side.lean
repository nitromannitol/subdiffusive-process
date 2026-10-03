module

public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Sobolev.ReflectionResponses
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.limit_form_package_form
public import SubdiffusiveProcess.Paper.lem_sincos
public import SubdiffusiveProcess.Paper.prop_locality_recovery

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem aux_limit_form_package_isRegular_of_core
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (F : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hcore : ∃ C, DirichletForm.IsCoreOn F (Q : Set (SpatialCoordinates d)) C) :
    DirichletForm.IsRegular F := by
  refine ⟨Q, Q.isOpen, ?_, hcore⟩
  rw [Measure.restrict_apply Q.isOpen.measurableSet.compl]
  simp only [compl_inter_self, measure_empty]

theorem aux_limit_form_package_energy_measure_of_locality
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (F : _root_.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (EM : DirichletForm.HasEnergyMeasure F)
    (hcore : ∃ C, DirichletForm.IsCoreOn F.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (hloc : DirichletForm.IsStronglyLocal F.toClosedForm) :
    ∃ Gamma : DirichletForm.EnergyMeasure F.toClosedForm,
      ∀ u ∈ F.domain,
        Gamma.measure u (centeredCube z r hr : Set (SpatialCoordinates d))ᶜ = 0 := by
  obtain ⟨Gamma⟩ := EM.exists_energyMeasure
    (aux_limit_form_package_isRegular_of_core (centeredCube z r hr) F.toClosedForm hcore) hloc
  obtain ⟨C, hC⟩ := hcore
  exact ⟨Gamma, fun u hu => aux_limit_form_package_energy_measure_support Gamma
    (centeredCube z r hr).isOpen.measurableSet hC hu⟩

/-- Coefficient comparison is needed only on the support of the gradient. -/
theorem aux_limit_form_package_responseForm_le_local
    {d : ℕ} {Q : Opens (SpatialCoordinates d)} (S : ResponseSpace Q)
    (a b : PositiveCoefficient Q) (K : ℝ) (q : Set (SpatialCoordinates d))
    (u : S.space)
    (hcoeff : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∈ q → b.val x ≤ K * a.val x)
    (hgrad : ∀ i : Fin d, ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∉ q → u.val.2 i x = 0) :
    responseForm S b u u ≤ K * responseForm S a u u := by
  rw [aux_prop_locality_recovery_responseForm_eq_sum,
    aux_prop_locality_recovery_responseForm_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [weightedL2Form_apply, weightedL2Form_apply, ← integral_const_mul]
  apply integral_mono_ae (integrable_weighted_inner b.val _ _)
    ((integrable_weighted_inner a.val _ _).const_mul K)
  filter_upwards [hcoeff, hgrad i] with x hx hg
  simp only [RCLike.inner_apply, conj_trivial]
  by_cases hxq : x ∈ q
  · simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (hx hxq) (mul_self_nonneg (u.val.2 i x))
  · rw [hg hxq]
    simp only [mul_zero, le_refl]

theorem aux_limit_form_package_modV_recovery {d : ℕ} (hd : 2 ≤ d) (hInterp : CubeFractionalInterpolationInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (S : ResponseSpace (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hLower : ∀ (wN : ℕ → S.space) (w : DomainL2 (centeredCube z r hr)),
      (∀ f : DomainL2 (centeredCube z r hr),
        Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      limitFormEnergy G w ≤
        liminf (fun n => ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal)) atTop)
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n) (Kstar : ℝ) (hKstar : ∀ n, KN n ≤ Kstar)
    (hfrac : ∀ w : S.space,
      cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
        (fun _ : Fin 1 => w.val.1) < ⊤)
    (hcoercive : ∀ n (w : S.space),
      ‖w.val.1‖ ^ 2 + volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
          (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤ KN n * responseForm S (a n) w w)
    (cut : ℕ → S.space) (B : ℝ) (hB : 0 ≤ B)
    (hcutE : ∀ n, responseForm S (a n) (cut n) (cut n) ≤ B)
    (hgrowth : ∀ n, ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal ((a n).val y * ∑ i : Fin d, ((cut n).val.2 i y) ^ 2)))
          (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t))
    (w : DomainL2 (centeredCube z r hr)) (hw : limitFormEnergy G w < ⊤)
    (Φ : ℕ → S.space) (hΦ1 : Tendsto (fun n => (Φ n).val.1) atTop (𝓝 w))
    (hΦE : Tendsto (fun n => responseForm S (a n) (Φ n) (Φ n)) atTop
      (𝓝 (limitFormEnergy G w).toReal))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (phi : ℕ → TestFunction (centeredCube z r hr) ℝ ⊤)
    (hPhi : ∀ n, (Φ n).val = smoothSobolevData (phi n))
    (hinner : ∀ n,
      (∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        0 ≤ (cut n).val.1 x ∧ (cut n).val.1 x ≤ 1) ∧
      (∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        w x ≠ 0 → (cut n).val.1 x = 1) ∧
      (∀ i, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        (cut n).val.2 i x ≠ 0 → w x = 0)) :
    Tendsto (fun n =>
      ((aux_prop_locality_recovery_modV S hS (phi n) (cut n)).val.1,
       (responseForm S (a n)
         (aux_prop_locality_recovery_modV S hS (phi n) (cut n))
         (aux_prop_locality_recovery_modV S hS (phi n) (cut n)) : EReal)))
      atTop (𝓝 (w, limitFormEnergy G w)) := by
  have hp := fun n => aux_prop_locality_recovery_modV_props S hS
    (phi n) (Φ n) (hPhi n) (cut n) w
    (hinner n).1 (hinner n).2.1 (hinner n).2.2
  exact aux_prop_locality_recovery_side hd hInterp z r hr t ht S a G
    hLower KN hKN Kstar hKstar hfrac hcoercive cut B hB hcutE hgrowth
    w hw Φ hΦ1 hΦE (fun n => aux_prop_locality_recovery_modV S hS (phi n) (cut n))
    (fun n i => aux_prop_locality_recovery_mulL
      (aux_prop_locality_recovery_testPartialLinf (phi n) i) (cut n).val.1)
    (fun n i => aux_prop_locality_recovery_mulL
      (aux_prop_locality_recovery_testLinf (phi n)) ((cut n).val.2 i))
    (fun n i => aux_prop_locality_recovery_modV_grad S hS (phi n) (cut n) i)
    (fun n => (hp n).1) (fun n => (hp n).2.1) (fun n => (hp n).2.2)

theorem aux_limit_form_package_modV_grad_zero
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (hS : S.space = killedSobolevGraph Q)
    (phi : TestFunction Q ℝ ⊤) (chi : S.space) (chic : SpatialCoordinates d → ℝ)
    (hchi : (chi.val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] chic)
    (O q : Set (SpatialCoordinates d)) (hOq : closure O ⊆ q)
    (hzero : ∀ x ∈ (Q : Set (SpatialCoordinates d)), x ∉ O → chic x = 0) :
    ∀ i : Fin d, ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∉ q → (aux_prop_locality_recovery_modV S hS phi chi).val.2 i x = 0 := by
  let Y := aux_prop_locality_recovery_modV S hS phi chi
  have hz : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∈ (closure O)ᶜ → Y.val.1 x = 0 := by
    filter_upwards [aux_prop_locality_recovery_modV_fst_ae S hS phi chi,
      hchi, ae_restrict_mem Q.isOpen.measurableSet] with x hx hcx hxQ hxO
    change (aux_prop_locality_recovery_modV S hS phi chi).val.1 x = 0
    rw [hx, hcx, hzero x hxQ (fun h => hxO (subset_closure h)), mul_zero]
  intro i
  have hg := aux_prop_locality_recovery_grad_ae_zero_of_const Y.val
    (S.le_weak Y.2) (closure O)ᶜ isClosed_closure.isOpen_compl 0 hz i
  filter_upwards [hg] with x hx hxq
  exact hx (fun hxO => hxq (hOq hxO))

/-- A core function supported in an open subregion admits a recovery sequence
whose gradients vanish outside that subregion. The cutoff error tends to zero
by the represented trace bounds. -/
theorem aux_limit_form_package_localized_recovery_base
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    let Q := centeredCube z r hr
    let H := DomainL2 Q
    ∀ (S : ResponseSpace Q) (hS : S.space = killedSobolevGraph Q)
    (a : ℕ → PositiveCoefficient Q)
    (G : H →L[ℝ] H)
    (hLower : ∀ (wN : ℕ → S.space) (w : H),
      (∀ f : H, Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      limitFormEnergy G w ≤
        liminf (fun n => ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal)) atTop)
    (hRecovery : ∀ w ∈ limitFormDomain G, ∃ wN : ℕ → S.space,
      Tendsto (fun n => ((wN n).val.1,
        ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal))) atTop
        (𝓝 (w, limitFormEnergy G w)))
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n)
    (Kstar : ℝ) (hKstar : ∀ n, KN n ≤ Kstar)
    (hfrac : ∀ w : S.space,
      cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
        (fun _ : Fin 1 => w.val.1) < ⊤)
    (hcoercive : ∀ n (w : S.space),
      ‖w.val.1‖ ^ 2 + volume.real (Q : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
          (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤ KN n * responseForm S (a n) w w)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (t : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (hcutoffs : ∀ (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ (Q : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → S.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (Q : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (Q : Set (SpatialCoordinates d)), 0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (Q : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm S (a n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((a n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (q : Set (SpatialCoordinates d)) (hq : IsOpen q)
    (hqQ : q ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (u : DomainL2 (centeredCube z r hr)) (hu : u ∈ limitFormDomain G)
    (uc : SpatialCoordinates d → ℝ) (huc : Continuous uc)
    (hucs : HasCompactSupport uc) (hucq : tsupport uc ⊆ q)
    (huae : (u : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc),
    ∃ Y : ℕ → S.space,
      Tendsto (fun n => ((Y n).val.1,
        (responseForm S (a n)
          (Y n) (Y n) : EReal))) atTop (𝓝 (u, limitFormEnergy G u)) ∧
      ∀ n (i : Fin d), ∀ᵐ x ∂volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d)),
        x ∉ q → (Y n).val.2 i x = 0 := by
  intro Q H S hS a G hLower hRecovery KN hKN Kstar hKstar hfrac hcoercive
    hInterp t ht _htd hcutoffs q hq hqQ u hu uc huc hucs hucq huae
  have hb1 := exists_open_between_and_isCompact_closure hucs.isCompact hq hucq
  obtain ⟨O, hO, hKO, hOq, _hOc⟩ := hb1
  have hb2 := hcutoffs (tsupport uc) O hucs.isCompact hO hKO (hOq.trans hqQ)
  obtain ⟨V, chi, chic, B, hV, hKV, _hVO, hB, hchi⟩ := hb2
  have hb3 := hRecovery u hu
  obtain ⟨vN, hvN⟩ := hb3
  have hb4 := aux_prop_locality_recovery_recovery_parts
    (fun n => (vN n).val.1) (fun n => responseForm S (a n) (vN n) (vN n))
    u (limitFormEnergy G u) (limitFormEnergy_nonneg G u) hu hvN
  obtain ⟨hvN1, hvNE⟩ := hb4
  have hb5 := aux_prop_locality_recovery_smooth_seq S hS a vN u _ hvN1 hvNE
  obtain ⟨phi, Phi, hPhi, hPhi1, hPhiE⟩ := hb5
  let Y := fun n => aux_prop_locality_recovery_modV S hS (phi n) (chi n)
  have hin := fun n => aux_prop_locality_recovery_inner_ae
    (chi n).val (S.le_weak (chi n).2) (chic n)
    (hchi n).2.1 (hchi n).2.2.1 V hV (hchi n).2.2.2.1
    u uc huae hKV
  have hrec := aux_limit_form_package_modV_recovery hd hInterp z r hr t ht S a G
    hLower KN hKN Kstar hKstar hfrac hcoercive chi B hB
    (fun n => (hchi n).2.2.2.2.2.1) (fun n => (hchi n).2.2.2.2.2.2)
    u hu Phi hPhi1 hPhiE hS phi hPhi hin
  refine ⟨Y, hrec, ?_⟩
  intro n
  exact aux_limit_form_package_modV_grad_zero S hS (phi n) (chi n) (chic n)
    (hchi n).2.1 O q hOq (hchi n).2.2.2.2.1

/-- Eventual coefficient order, along an actual recovery sequence, passes to
the finite limit energy. -/
theorem aux_limit_form_package_energy_order_of_recovery
    {d : ℕ} {Q : Opens (SpatialCoordinates d)} (S : ResponseSpace Q)
    (a b : ℕ → PositiveCoefficient Q)
    (GF : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hlower : ∀ (vN : ℕ → S.space) (v : DomainL2 Q),
      (∀ f : DomainL2 Q,
        Tendsto (fun n => inner ℝ f (vN n).val.1) atTop (𝓝 (inner ℝ f v))) →
      limitFormEnergy GF v ≤
        liminf (fun n => (responseForm S (b n) (vN n) (vN n) : EReal)) atTop)
    (u : DomainL2 Q) (Eu K : ℝ) (Y : ℕ → S.space)
    (hY : Tendsto (fun n => ((Y n).val.1,
      (responseForm S (a n) (Y n) (Y n) : EReal))) atTop (𝓝 (u, (Eu : EReal))))
    (horder : ∀ᶠ n in atTop,
      responseForm S (b n) (Y n) (Y n) ≤ K * responseForm S (a n) (Y n) (Y n)) :
    limitFormEnergy GF u ≤ ((K * Eu : ℝ) : EReal) := by
  have he : Tendsto (fun n => responseForm S (a n) (Y n) (Y n)) atTop (𝓝 Eu) :=
    EReal.tendsto_coe.mp hY.snd_nhds
  have hbound : Tendsto (fun n => ((K * responseForm S (a n) (Y n) (Y n) : ℝ) : EReal))
      atTop (𝓝 ((K * Eu : ℝ) : EReal)) :=
    EReal.tendsto_coe.mpr (tendsto_const_nhds.mul he)
  have hbdd : IsBoundedUnder (· ≥ ·) atTop
      (fun n => (responseForm S (b n) (Y n) (Y n) : EReal)) := by
    change ∃ bound : EReal, ∀ᶠ n : ℕ in atTop,
      (responseForm S (b n) (Y n) (Y n) : EReal) ≥ bound
    refine ⟨0, Eventually.of_forall ?_⟩
    intro n
    exact EReal.coe_nonneg.mpr (responseForm_nonneg S (b n) (Y n))
  have hlim := Filter.liminf_le_liminf
    (horder.mono (fun n hn => EReal.coe_le_coe_iff.mpr hn)) hbdd hbound.isCoboundedUnder_ge
  rw [hbound.liminf_eq] at hlim
  exact (hlower Y u (fun f => tendsto_const_nhds.inner hY.fst_nhds)).trans hlim

/-- The actual form and energy measure attached to one represented operator limit. -/
structure aux_limit_form_package_limit_side
    (d : ℕ) (hd : 2 ≤ d)

    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr)) where
  response : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)
  response_eq : ∀ n f, response n f =
    (responseSolution S (a n)
      ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1
  response_tendsto : Tendsto response atTop (𝓝 G)
  bounds : in_represented_bounds_seq d hd z r hr S a G
  form : _root_.DirichletForm
    (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))
  energy_eq : ∀ u, form.toClosedForm.energy u = limitFormEnergy G u
  core : ∃ C, DirichletForm.IsCoreOn form.toClosedForm
    (centeredCube z r hr : Set (SpatialCoordinates d)) C
  gamma : DirichletForm.EnergyMeasure form.toClosedForm

theorem aux_limit_form_package_domain_eq_of_energy
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) (hE : ∀ u, E.energy u = limitFormEnergy G u) :
    (E.domain : Set (DomainL2 Q)) = limitFormDomain G := by
  ext u
  change u ∈ E.domain ↔ limitFormEnergy G u < ⊤
  rw [← hE]
  exact (E.energy_lt_top_iff u).symm

theorem aux_limit_form_package_domain_mem_of_energy
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) (hE : ∀ u, E.energy u = limitFormEnergy G u)
    {u : DomainL2 Q} (hu : u ∈ limitFormDomain G) : u ∈ E.domain := by
  apply E.mem_domain_of_energy_lt_top
  rw [hE]
  exact hu

theorem aux_limit_form_package_form_eq_toReal_energy
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (u : DomainL2 Q) (hu : u ∈ E.domain) :
    E.form u u = (limitFormEnergy G u).toReal := by
  rw [← hE, E.energy_of_mem hu, EReal.toReal_coe]

theorem aux_limit_form_package_core_dense_of_isCoreOn
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcore : ∃ C, DirichletForm.IsCoreOn E (Q : Set (SpatialCoordinates d)) C) :
    ∀ u ∈ limitFormDomain G, ∀ eps : ℝ, 0 < eps →
      ∃ p : DomainL2 Q, MemFormCore G p ∧ ‖p - u‖ ≤ eps ∧
        limitFormEnergy G (p - u) ≤ ((eps : ℝ) : EReal) := by
  obtain ⟨C, hC⟩ := hcore
  intro u hu eps heps
  have huE : u ∈ E.domain := E.mem_domain_of_energy_lt_top (by rw [hE]; exact hu)
  obtain ⟨p, hpC, hsmall⟩ := hC.denseEnergy u huE (min (eps ^ 2) eps)
    (lt_min (sq_pos_of_pos heps) heps)
  have hp := hC.memCoreOn p hpC
  have hpu := E.domain.sub_mem hp.mem_domain huE
  rw [E.energyNormSq_sub_comm huE hp.mem_domain] at hsmall
  have hnormsq := (E.sq_norm_le_energyNormSq hpu).trans
    (hsmall.le.trans (min_le_left _ _))
  have hform := E.form_le_energyNormSq.trans (hsmall.le.trans (min_le_right _ _))
  refine ⟨p, ⟨?_, hp.2⟩, ?_, ?_⟩
  · show limitFormEnergy G p < ⊤
    rw [← hE]
    exact (E.energy_lt_top_iff p).mpr hp.mem_domain
  · nlinarith [norm_nonneg (p - u)]
  · rw [← hE, E.energy_of_mem hpu]
    exact EReal.coe_le_coe_iff.mpr hform

theorem aux_limit_form_package_local_measure_bounds
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hEreg : ∃ C, DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (hFreg : ∃ C, DirichletForm.IsCoreOn F.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (hdom : E.domain = F.domain)
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm)
    (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (q : Set (SpatialCoordinates d)) (hq : IsOpen q) (hqQ : q ⊆ Q)
    (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (hup : ∀ v, E.toClosedForm.MemCoreOn q v → F.form v v ≤ hi * E.form v v)
    (hlow : ∀ v, F.toClosedForm.MemCoreOn q v → E.form v v ≤ lo⁻¹ * F.form v v)
    (u : DomainL2 Q) (hu : E.toClosedForm.MemCore u)
    (B : Set (SpatialCoordinates d)) (hBq : B ⊆ q) :
    lo * (GammaE.measure u B).toReal ≤ (GammaF.measure u B).toReal ∧
      (GammaF.measure u B).toReal ≤ hi * (GammaE.measure u B).toReal := by
  have huF : F.toClosedForm.MemCore u := ⟨hdom ▸ hu.mem_domain, hu.2⟩
  have hupper := aux_lem_sincos_of_mul_comp E F hEreg hdom GammaE GammaF q hq hqQ
    (DirichletForm.mul_comp_mem E q) hi.toNNReal
    (by simpa only [Real.coe_toNNReal hi hhi] using hup) u hu B hBq
  have hlower := aux_lem_sincos_of_mul_comp F E hFreg hdom.symm GammaF GammaE q hq hqQ
    (DirichletForm.mul_comp_mem F q) (lo⁻¹).toNNReal
    (by simpa only [Real.coe_toNNReal _ (inv_nonneg.mpr hlo.le)] using hlow) u huF B hBq
  have hiReal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (GammaE.measure_ne_top hu.mem_domain B)) hupper
  have loReal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (GammaF.measure_ne_top huF.mem_domain B)) hlower
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, Real.coe_toNNReal hi hhi] at hiReal
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal,
    Real.coe_toNNReal _ (inv_nonneg.mpr hlo.le)] at loReal
  exact ⟨(le_inv_mul_iff₀ hlo).mp loReal, hiReal⟩

theorem aux_limit_form_package_coefficient_weight_upper
    {d : ℕ} {Q : Opens (SpatialCoordinates d)} (a b : PositiveCoefficient Q)
    (rho : SpatialCoordinates d → ℝ)
    (hweight : b.val =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      fun x => rho x * a.val x)
    (q : Set (SpatialCoordinates d)) (K : ℝ) (hK : ∀ x ∈ q, rho x ≤ K) :
    ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∈ q → b.val x ≤ K * a.val x := by
  filter_upwards [hweight, aux_prop_locality_recovery_coeff_nonneg a] with x hx hax hxq
  rw [hx]
  exact mul_le_mul_of_nonneg_right (hK x hxq) hax

theorem aux_limit_form_package_coefficient_weight_lower
    {d : ℕ} {Q : Opens (SpatialCoordinates d)} (a b : PositiveCoefficient Q)
    (rho : SpatialCoordinates d → ℝ)
    (hweight : b.val =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      fun x => rho x * a.val x)
    (q : Set (SpatialCoordinates d)) (K : ℝ) (hK : 0 < K)
    (hlow : ∀ x ∈ q, K ≤ rho x) :
    ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∈ q → a.val x ≤ K⁻¹ * b.val x := by
  filter_upwards [hweight, aux_prop_locality_recovery_coeff_nonneg a] with x hx hax hxq
  apply (le_inv_mul_iff₀ hK).mpr
  rw [hx]
  exact mul_le_mul_of_nonneg_right (hlow x hxq) hax

theorem limit_form_package_side
    {d : ℕ} (hd : 2 ≤ d)
    (z0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (Sspace0 : ResponseSpace (centeredCube z0 r0 hr0))
    (hSspace0 : Sspace0.space = killedSobolevGraph (centeredCube z0 r0 hr0))
    (a0 : ℕ → PositiveCoefficient (centeredCube z0 r0 hr0))
    (hcontract0 : ∀ (n : ℕ) (T : ℝ → ℝ),
      DirichletForm.IsNormalContraction T → ∀ u : Sspace0.space,
        ∃ v : Sspace0.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z0 r0 hr0 : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm Sspace0
              (a0 n) v v ≤
            responseForm Sspace0
              (a0 n) u u)
    (G0 : DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (GN0 : ℕ → DomainL2 (centeredCube z0 r0 hr0) →L[ℝ] DomainL2 (centeredCube z0 r0 hr0))
    (hGN0 : ∀ (n : ℕ) (f : DomainL2 (centeredCube z0 r0 hr0)), GN0 n f =
      (responseSolution Sspace0
          (a0 n)
          ((sobolevVolumeLoad f).comp Sspace0.space.subtypeL)).val.1)
    (hGN0tendsto : Tendsto GN0 atTop (𝓝 G0))
    (hbundle0 : in_represented_bounds_seq d hd z0 r0 hr0 Sspace0 a0 G0)
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
      DirichletForm.HasEnergyMeasure F) :
    Nonempty (aux_limit_form_package_limit_side d hd z0 r0 hr0 Sspace0 G0 a0) := by
  obtain ⟨F, _hFdom, hF, hcore⟩ := limit_form_package_form hd z0 r0 hr0
    Sspace0 hSspace0 a0 hcontract0 G0 GN0 hGN0 hGN0tendsto hbundle0
  have hlocal := aux_limit_form_package_form_core_locality d hd z0 r0 hr0
    Sspace0 hSspace0 G0 a0 GN0 hGN0 hGN0tendsto hbundle0 F.toClosedForm hF
  have hstrong := (BD z0 r0 hr0 F).isStronglyLocal_of_onCore
    (aux_limit_form_package_isRegular_of_core (centeredCube z0 r0 hr0) F.toClosedForm hcore)
    (BDQ z0 r0 hr0 F hcore hlocal)
  obtain ⟨Gamma, _hSupport⟩ := aux_limit_form_package_energy_measure_of_locality z0 r0 hr0 F
    (EM z0 r0 hr0 F) hcore hstrong
  exact ⟨⟨GN0, hGN0, hGN0tendsto, hbundle0, F, hF, hcore, Gamma⟩⟩

end Paper
