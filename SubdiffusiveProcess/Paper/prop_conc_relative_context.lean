import SubdiffusiveProcess.Paper.prop_conc_masked_response_pair
import SubdiffusiveProcess.Paper.lem_relvar

/-! Actual common-trace and masked response data satisfy the full relative-variation context.
All local-order and minimizer fields are supplied here; no concentration conclusion is assumed. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators
namespace Paper
noncomputable section

/-- The constructed masked minimizers satisfy every deterministic hypothesis of relative variation. -/
theorem prop_conc_relative_context
    {d : ℕ} (hd : 2 ≤ d) (Q : Opens (SpatialCoordinates d))
    (hQ : ∃ (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ), Q = centeredCube zQ rQ hrQ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hinside : closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d)))
    (E F : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GammaE : DirichletForm.EnergyMeasure E.toClosedForm) (GammaF : DirichletForm.EnergyMeasure F.toClosedForm)
    (D : Submodule ℝ (DomainL2 Q))
    (P : DirichletForm.LocalResponsePair (V := Fin d → ℝ) E.toClosedForm F.toClosedForm GammaE GammaF
      (centeredCube z r hr : Set (SpatialCoordinates d)) D)
    (hEc : ∃ S, DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) S)
    (hFc : ∃ S, DirichletForm.IsCoreOn F.toClosedForm (Q : Set (SpatialCoordinates d)) S)
    (C0 m M c : ℝ) (hC0 : 1 ≤ C0) (hm : C0⁻¹ ≤ m) (hmM : m ≤ M) (hM : M ≤ C0)
    (hc : c ∈ Set.Icc m M)
    (hform : ∀ u ∈ E.domain, m * E.form u u ≤ F.form u u ∧ F.form u u ≤ M * E.form u u)
    (slopes : Finset (Fin d → ℝ))
    (hslopes : ∀ p : Fin d → ℝ, p ∈ slopes ↔ (∃ i, p = Pi.single i (1 : ℝ)) ∨
      (∃ i j, p = Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ)))
    (hDpos : 0 < ∑ i : Fin d, P.QE (Pi.single i 1))
    (g : SpatialCoordinates d → ℝ) (hg : Measurable g)
    (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B)
    (hBq : B ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hsupp : ∀ x, x ∉ B → g x = 0)
    (G K CE CF : ℝ) (hG : IsLUB (Set.range (fun x => |g x|)) G)
    (hbdd : BddAbove (Set.range (fun x => |g x|)))
    (W : aux_prop_conc_masked_response_pair_Data Q E F GammaE GammaF
      (centeredCube z r hr : Set (SpatialCoordinates d)) D P g K CE CF) :
    let uE : (Fin d → ℝ) → DomainL2 Q := fun p => P.boundary p
    let D0 := ∑ i : Fin d, P.QE (Pi.single i 1)
    let Dg := ∑ i : Fin d, W.QEg (Pi.single i 1)
    let nu := D0⁻¹ * ∑ p ∈ slopes, ((GammaE.measure (uE p) + GammaE.measure (P.uF p)) B).toReal
    let ze := D0⁻¹ * ∑ p ∈ slopes, (GammaE.measure (P.uF p - uE p) B).toReal
    let IE := fun u v : DomainL2 Q => DirichletForm.signedIntegralOn (GammaE.cross u v) B
      (fun x => Real.exp (g x) - 1)
    let IF := fun u v : DomainL2 Q => DirichletForm.signedIntegralOn (GammaF.cross u v) B
      (fun x => Real.exp (g x) - 1)
    aux_lem_relvar_Ctx C0 Q z r hr slopes E.toClosedForm F.toClosedForm
      W.Edata.form.toClosedForm W.Fdata.form.toClosedForm GammaE GammaF W.Edata.Gamma W.Fdata.Gamma
      D m M c g B G uE P.uF W.uEg W.uFg P.QE P.QF W.QEg W.QFg D0 Dg nu ze IE IF := by
  have hmpos : 0 < m := (inv_pos.mpr (zero_lt_one.trans_le hC0)).trans_le hm
  have hMpos : 0 < M := hmpos.trans_le hmM
  have hlow := aux_thm_prop_endpoint_invariance_energy_order_one_sided_light
    Q E F hFc P.domain_eq GammaE GammaF m hmpos (fun u hu => (hform u hu).1)
  have hupp := aux_thm_prop_endpoint_invariance_energy_order_one_sided_light
    Q F E hEc P.domain_eq.symm GammaF GammaE M⁻¹ (inv_pos.mpr hMpos)
    (fun u hu => (inv_mul_le_iff₀ hMpos).mpr ((hform u (P.domain_eq.symm ▸ hu)).2))
  refine {
    hC0 := hC0, hd := hd, hslopes := hslopes, hQ := hQ, hinside := hinside
    hdomEF := P.domain_eq, hdomEg := W.Edata.domain_eq
    hdomFg := W.Fdata.domain_eq.trans P.domain_eq.symm
    hzero := P.killed, hm := hm, hmM := hmM, hM := hM, hmc := hc.1, hcM := hc.2
    horder := ?_
    hg := hg, hB := hB, hBq := hBq, hsupp := hsupp, hG := hG, hbdd := hbdd
    hweightE := W.Edata.weight, hweightF := W.Fdata.weight
    hweightE_cross := W.Edata.cross, hweightF_cross := W.Fdata.cross
    huE := fun p => (P.boundary p).property, huF := P.memF, huEg := W.memEg, huFg := W.memFg
    htraceF := P.traceF, htraceEg := W.traceEg, htraceFg := W.traceFg
    hminE := P.minE, hminF := P.minF, hminEg := W.minEg, hminFg := W.minFg
    hQE := P.responseE, hQF := P.responseF, hQEg := W.responseEg, hQFg := W.responseFg
    hDdef := rfl, hD := hDpos, hDgdef := rfl, hnudef := rfl, hzedef := rfl
    hIEdef := fun _ _ => rfl, hIFdef := fun _ _ => rfl }
  intro u hu A hA
  exact ⟨hlow u hu A hA, (inv_mul_le_iff₀ hMpos).mp (hupp u (P.domain_eq ▸ hu) A hA)⟩

end
end Paper
