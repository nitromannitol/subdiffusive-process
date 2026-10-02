import SubdiffusiveProcess.Paper.lem_replace
import SubdiffusiveProcess.Paper.prop_conc_boundary_truncation
import SubdiffusiveProcess.Paper.prop_conc_local_affine_order



set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators
namespace Paper
noncomputable section

/-- The killed-variation minimum is below the continuous boundary-extension infimum. -/
theorem aux_prop_conc_weighted_identification_bridge_le
    (d : ℕ) (hd : 2 ≤ d) (zQ zq : SpatialCoordinates d)
    (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hqQ : (centeredCube zq r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR : Set (SpatialCoordinates d)))
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube zQ R hR : Set (SpatialCoordinates d)) C)
    (Dq : Submodule ℝ (DomainL2 (centeredCube zQ R hR)))
    (hkilled : DirichletForm.IsKilledDomain E.toClosedForm
      (centeredCube zq r hr : Set (SpatialCoordinates d)) Dq)
    (u : DomainL2 (centeredCube zQ R hR)) (hu : u ∈ E.domain)
    (U : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (closure (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (hurep : ⇑u =ᵐ[volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))] U)
    (b : SpatialCoordinates d → ℝ)
    (hUb : ∀ x ∈ frontier (centeredCube zq r hr : Set (SpatialCoordinates d)), U x = b x)
    (T : ℝ)
    (hT : IsLeast {t : ℝ | ∃ w : DomainL2 (centeredCube zQ R hR), w ∈ Dq ∧
      t = (Gamma.measure (u + w) (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal} T)
    (Lambda : ℝ)
    (hLambda : IsGLB (aux_thm_prop_boundary_energy_set (centeredCube zQ R hR) E.toClosedForm Gamma
      (centeredCube zq r hr : Set (SpatialCoordinates d)) b) Lambda) :
    T ≤ Lambda := by
  apply hLambda.2
  intro e he
  obtain ⟨v, V, hv, hV, hvrep, hboundary, rfl⟩ := he
  have hw : v - u ∈ E.domain := E.domain.sub_mem hv hu
  have hwrep : ⇑(v - u) =ᵐ[volume.restrict
      (centeredCube zQ R hR : Set (SpatialCoordinates d))] fun x => V x - U x := by
    filter_upwards [Lp.coeFn_sub v u, hvrep, hurep] with x hsub hvx hux
    rw [hsub, Pi.sub_apply, hvx, hux]
  have hwLp := (Lp.memLp (v - u)).ae_eq hwrep
  have hqbar : MeasurableSet (closure (centeredCube zq r hr : Set (SpatialCoordinates d))) :=
    isClosed_closure.measurableSet
  let wq := (hwLp.indicator hqbar).toLp _
  have hwqrep : ⇑wq =ᵐ[volume.restrict
      (centeredCube zQ R hR : Set (SpatialCoordinates d))]
      (closure (centeredCube zq r hr : Set (SpatialCoordinates d))).indicator
        (fun x => V x - U x) := MemLp.coeFn_toLp _
  have hwq := prop_conc_boundary_truncation d hd zQ zq R r hR hr hqQ E Gamma hcore
    Dq hkilled (v - u) hw (fun x => V x - U x) (hV.sub hU) hwrep
    (fun x hx => sub_eq_zero.mpr ((hboundary x hx).trans (hUb x hx).symm)) wq hwqrep
  have huadd : u + wq ∈ E.domain := E.domain.add_mem hu (hkilled.le_domain hwq.1)
  have hqopen := (centeredCube zq r hr).isOpen
  have hlocaleq : ⇑v =ᵐ[(volume.restrict
      (centeredCube zQ R hR : Set (SpatialCoordinates d))).restrict
        (centeredCube zq r hr : Set (SpatialCoordinates d))] ⇑(u + wq) := by
    filter_upwards [ae_restrict_mem hqopen.measurableSet,
      ae_restrict_of_ae hvrep, ae_restrict_of_ae hurep,
      ae_restrict_of_ae hwqrep, ae_restrict_of_ae (Lp.coeFn_add u wq)]
      with x hxq hvx hux hwqx hadd
    rw [Set.indicator_of_mem (subset_closure hxq)] at hwqx
    rw [hvx, hadd, Pi.add_apply, hux, hwqx]
    ring
  rw [Gamma.locality_apply hv huadd hqopen hlocaleq]
  exact hT.2 ⟨wq, hwq.1, rfl⟩

/-- Approximate the harmonic projection by core variations, keeping exact continuous boundary values. -/
theorem aux_prop_conc_weighted_identification_bridge_competitor
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E)
    (q : Set (SpatialCoordinates d)) (hq : IsOpen q)
    (Dq : Submodule ℝ (DomainL2 Q)) (hD : DirichletForm.IsKilledDomain E q Dq)
    (hcoercive : ∃ K : ℝ, 0 < K ∧ ∀ v ∈ Dq, ‖v‖ ^ 2 ≤ K * E.form v v)
    (u : DomainL2 Q) (hu : u ∈ E.domain)
    (U : SpatialCoordinates d → ℝ) (hU : ContinuousOn U (closure (Q : Set (SpatialCoordinates d))))
    (hurep : ⇑u =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U)
    (T : ℝ)
    (hT : IsLeast {t : ℝ | ∃ w : DomainL2 Q, w ∈ Dq ∧
      t = (Gamma.measure (u + w) q).toReal} T)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
      v ∈ E.domain ∧ ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
      (⇑v =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V) ∧
      (∀ x ∈ frontier q, V x = U x) ∧ (Gamma.measure v q).toReal < T + eps := by
  obtain ⟨p, hp, ho⟩ := aux_lem_replace_projection_exists E hD hcoercive u hu
  have hup : u - p ∈ E.domain := E.domain.sub_mem hu (hD.le_domain hp)
  have hmin : IsLeast {t : ℝ | ∃ w : DomainL2 Q, w ∈ Dq ∧
      t = (Gamma.measure (u + w) q).toReal}
      (Gamma.measure (u - p) q).toReal := by
    refine ⟨⟨-p, Dq.neg_mem hp, by simp [sub_eq_add_neg]⟩, ?_⟩
    rintro e ⟨w, hw, rfl⟩
    have hpw : p + w ∈ Dq := Dq.add_mem hp hw
    have hsplit := aux_lem_replace_cell_energy_split E Gamma hq hD hup hpw (ho _ hpw)
    rw [show (u - p) + (p + w) = u + w by abel] at hsplit
    rw [hsplit]
    exact le_add_of_nonneg_right (E.form_nonneg _ (hD.le_domain hpw))
  have hval : (Gamma.measure (u - p) q).toReal = T := hmin.unique hT
  obtain ⟨w, hw, hnear⟩ := hD.approx p hp eps heps
  obtain ⟨W, hW, _hcW, hsW, hwrep⟩ := hw.2
  have hpw : p - w ∈ Dq := Dq.sub_mem hp (hD.memCoreOn_mem w hw)
  have hsplit := aux_lem_replace_cell_energy_split E Gamma hq hD hup hpw (ho _ hpw)
  rw [show (u - p) + (p - w) = u - w by abel, hval] at hsplit
  refine ⟨u - w, fun x => U x - W x, E.domain.sub_mem hu hw.1,
    hU.sub hW.continuousOn, ?_, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_sub u w, hurep, hwrep] with x hsub hux hwx
    rw [hsub, Pi.sub_apply, hux, hwx]
  · intro x hx
    have hxq : x ∉ q := by
      simpa only [hq.interior_eq] using hx.2
    have hxW : x ∉ tsupport W := fun hh => hxq (hsW hh)
    change U x - W x = U x
    rw [image_eq_zero_of_notMem_tsupport hxW, sub_zero]
  · rw [hsplit]
    have hnorm := sq_nonneg ‖p - w‖
    unfold DirichletForm.ClosedForm.energyNormSq at hnear
    linarith

/-- Killed trace minimum and continuous boundary infimum coincide when the minimum is attained. -/
theorem prop_conc_weighted_identification_bridge
    (d : ℕ) (hd : 2 ≤ d) (zQ zq : SpatialCoordinates d)
    (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hqQ : (centeredCube zq r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR : Set (SpatialCoordinates d)))
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube zQ R hR : Set (SpatialCoordinates d)) C)
    (Dq : Submodule ℝ (DomainL2 (centeredCube zQ R hR)))
    (hkilled : DirichletForm.IsKilledDomain E.toClosedForm
      (centeredCube zq r hr : Set (SpatialCoordinates d)) Dq)
    (hcoercive : ∃ K : ℝ, 0 < K ∧ ∀ v ∈ Dq, ‖v‖ ^ 2 ≤ K * E.form v v)
    (u : DomainL2 (centeredCube zQ R hR)) (hu : u ∈ E.domain)
    (U : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (closure (centeredCube zQ R hR : Set (SpatialCoordinates d))))
    (hurep : ⇑u =ᵐ[volume.restrict (centeredCube zQ R hR : Set (SpatialCoordinates d))] U)
    (b : SpatialCoordinates d → ℝ)
    (hUb : ∀ x ∈ frontier (centeredCube zq r hr : Set (SpatialCoordinates d)), U x = b x)
    (Lambda : ℝ)
    (hLambda : IsGLB (aux_thm_prop_boundary_energy_set (centeredCube zQ R hR) E.toClosedForm Gamma
      (centeredCube zq r hr : Set (SpatialCoordinates d)) b) Lambda) :
    IsLeast {t : ℝ | ∃ w : DomainL2 (centeredCube zQ R hR), w ∈ Dq ∧
      t = (Gamma.measure (u + w) (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal}
      Lambda := by
  obtain ⟨p, hp, ho⟩ := aux_lem_replace_projection_exists E.toClosedForm hkilled hcoercive u hu
  have hup : u - p ∈ E.domain := E.domain.sub_mem hu (hkilled.le_domain hp)
  have hqopen := (centeredCube zq r hr).isOpen
  have hmin : IsLeast {t : ℝ | ∃ w : DomainL2 (centeredCube zQ R hR), w ∈ Dq ∧
      t = (Gamma.measure (u + w) (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal}
      (Gamma.measure (u - p) (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal := by
    refine ⟨⟨-p, Dq.neg_mem hp, by simp [sub_eq_add_neg]⟩, ?_⟩
    rintro e ⟨w, hw, rfl⟩
    have hpw : p + w ∈ Dq := Dq.add_mem hp hw
    have hsplit := aux_lem_replace_cell_energy_split E.toClosedForm Gamma hqopen hkilled hup hpw
      (ho _ hpw)
    rw [show (u - p) + (p + w) = u + w by abel] at hsplit
    rw [hsplit]
    exact le_add_of_nonneg_right (E.form_nonneg _ (hkilled.le_domain hpw))
  set T := (Gamma.measure (u - p) (centeredCube zq r hr : Set (SpatialCoordinates d))).toReal
    with hTdef
  have hle : T ≤ Lambda :=
    aux_prop_conc_weighted_identification_bridge_le d hd zQ zq R r hR hr hqQ E Gamma hcore Dq
      hkilled u hu U hU hurep b hUb T hmin Lambda hLambda
  have hge : Lambda ≤ T := by
    apply le_of_forall_pos_le_add
    intro eps heps
    obtain ⟨v, V, hv, hV, hvrep, hVb, hbound⟩ :=
      aux_prop_conc_weighted_identification_bridge_competitor (centeredCube zQ R hR)
        E.toClosedForm Gamma _ hqopen Dq hkilled hcoercive u hu U hU hurep T hmin eps heps
    exact (hLambda.1 ⟨v, V, hv, hV, hvrep,
      fun x hx => (hVb x hx).trans (hUb x hx), rfl⟩).trans hbound.le
  have hTL : T = Lambda := le_antisymm hle hge
  rw [← hTL]
  exact hmin

end
end Paper
