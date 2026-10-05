module

public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.DirichletForm.ContinuousTraceResponse

@[expose] public section

/-! Finite response witnesses pass to the form defined by a limiting killed inverse.
The energy estimate here bounds the total energy; it does not assert a localized
liminf theorem or construct the finite witnesses.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology ENNReal

noncomputable section
namespace SubdiffusiveProcess

/-- A uniformly bounded response-energy sequence has a limit in the inverse-limit form domain. -/
theorem form_bound_of_response_limits
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q)
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hE : ∀ v, E.energy v = limitFormEnergy G v)
    (hresponse : ∀ f : DomainL2 Q,
      Tendsto (fun n => inverseResponse S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop
        (𝓝 (inner ℝ f (G f))))
    (un : ℕ → S.space) (u : DomainL2 Q)
    (hL2 : Tendsto (fun n => (un n).val.1) atTop (𝓝 u))
    (K : ℝ) (hK : ∀ n, responseForm S (a n) (un n) (un n) ≤ K) :
    u ∈ E.domain ∧ E.form u u ≤ K := by
  have hweak : ∀ f : DomainL2 Q,
      Tendsto (fun n => inner ℝ f (un n).val.1) atTop (𝓝 (inner ℝ f u)) := by
    intro f
    exact tendsto_const_nhds.inner hL2
  have hlower := quadraticDual_le_liminf_responseForm S a G un u hweak hresponse
  have hupper : E.energy u ≤ (K : EReal) := by
    rw [hE]
    exact hlower.trans ((liminf_le_liminf
      (Eventually.of_forall fun n => EReal.coe_le_coe_iff.mpr (hK n))).trans_eq
        (liminf_const (K : EReal)))
  have hu := E.mem_domain_of_energy_lt_top (hupper.trans_lt (EReal.coe_lt_top K))
  refine ⟨hu, ?_⟩
  rw [E.energy_of_mem hu] at hupper
  exact EReal.coe_le_coe_iff.mp hupper

/-- A uniform trace limit of finite response witnesses gives a continuous limiting trace witness. -/
theorem continuousTraceValues_of_response_limits
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q)
    (G : DomainL2 Q →L[ℝ] DomainL2 Q)
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hE : ∀ v, E.energy v = limitFormEnergy G v)
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    (hresponse : ∀ f : DomainL2 Q,
      Tendsto (fun n => inverseResponse S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop
        (𝓝 (inner ℝ f (G f))))
    (un : ℕ → S.space) (u : DomainL2 Q)
    (hL2 : Tendsto (fun n => (un n).val.1) atTop (𝓝 u))
    (VN bN : ℕ → SpatialCoordinates d → ℝ) (V b : SpatialCoordinates d → ℝ)
    (hVN : ∀ n, ContinuousOn (VN n) (closure (Q : Set (SpatialCoordinates d))))
    (hrep : ∀ n, ((un n).val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] VN n)
    (B : Set (SpatialCoordinates d)) (hBS : frontier B ⊆ closure (Q : Set (SpatialCoordinates d)))
    (hVlim : TendstoUniformlyOn VN V atTop (closure (Q : Set (SpatialCoordinates d))))
    (hblim : TendstoUniformlyOn bN b atTop (frontier B))
    (htrace : ∀ n, EqOn (VN n) (bN n) (frontier B))
    (K : ℝ) (hK : ∀ n, responseForm S (a n) (un n) (un n) ≤ K) :
    (Gamma.continuousTraceValues (closure (Q : Set (SpatialCoordinates d))) B b).Nonempty ∧
      IsGLB (Gamma.continuousTraceValues (closure (Q : Set (SpatialCoordinates d))) B b)
        (sInf (Gamma.continuousTraceValues (closure (Q : Set (SpatialCoordinates d))) B b)) ∧
      sInf (Gamma.continuousTraceValues (closure (Q : Set (SpatialCoordinates d))) B b) ≤ K := by
  obtain ⟨hu, henergy⟩ := form_bound_of_response_limits S a G E hE hresponse un u hL2 K hK
  have hS : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∈ closure (Q : Set (SpatialCoordinates d)) := by
    filter_upwards [self_mem_ae_restrict Q.isOpen.measurableSet] with x hx
    exact subset_closure hx
  have hVc : ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) :=
    hVlim.continuousOn (Eventually.of_forall hVN).frequently
  have hVr := ae_eq_of_tendsto_Lp_of_tendstoUniformlyOn
    (closure (Q : Set (SpatialCoordinates d))) hS (fun n => (un n).val.1) u hL2 VN V hrep hVlim
  have hVb := eqOn_of_uniform_limits_of_eqOn
    (closure (Q : Set (SpatialCoordinates d))) (frontier B) hBS VN bN V b hVlim hblim htrace
  have hlocal := (Gamma.toReal_measure_le_form hu B).trans henergy
  have hmem : (Gamma.measure u B).toReal ∈
      Gamma.continuousTraceValues (closure (Q : Set (SpatialCoordinates d))) B b :=
    ⟨u, V, hu, hVc, hVr, fun x hx => hVb hx, rfl⟩
  have hbelow : BddBelow
      (Gamma.continuousTraceValues (closure (Q : Set (SpatialCoordinates d))) B b) := by
    refine ⟨0, ?_⟩
    rintro e ⟨v, W, hv, hWc, hWr, hWt, rfl⟩
    exact ENNReal.toReal_nonneg
  exact ⟨⟨_, hmem⟩, isGLB_csInf ⟨_, hmem⟩ hbelow, (csInf_le hbelow hmem).trans hlocal⟩

end SubdiffusiveProcess
