module

public import SubdiffusiveProcess.Paper.prop_conc_controlled_weighted_convergence
public import SubdiffusiveProcess.Paper.prop_conc_local_affine_identified_order
public import SubdiffusiveProcess.Paper.prop_conc_pair_data
public import SubdiffusiveProcess.Sobolev.VolumeResponseOperator
public import Mathlib.Tactic

@[expose] public section

/-! Operator-level identification of the forms of a resampled configuration.  Let `ω` be a configuration whose
actual cutoff Green operators (killed on the padded cube `Q`) converge along a cutoff sequence `N` to `G`, with
analytic controls along a subsequence, let `η = ω[j ← y]` be the resampled configuration, whose cutoff
coefficients are `exp (y - ω_j)` times those of `ω` for every cutoff containing the layer `j`, and let the Green
operators of `η` converge along `N` to `Gp`.  If `E` has energy `limitFormEnergy G` (regular, with an energy
measure) and `E'` has energy `limitFormEnergy Gp`, then `E'` has the domain of `E` and the diagonal
`E'(u,u) = ∫ exp (y - ω_j) dΓ_E(u)`.  Applied to the `E` and `F` forms of a pair `Y` at `ω` and a tied pair
`Yc` at `η`, this supplies the form-level premises of the masked-measure identification.  No probabilistic
assertion; the classical inputs enter only through the controlled weighted convergence theorem. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology BigOperators
namespace Paper
noncomputable section

section Side

variable {d : ℕ}

/-- Weighted convergence along the coefficient sequences `a` (controlled) and `b = exp g * a` identifies the
form of the limit of the `b`-operators with the `exp g`-weighted form of the limit of the `a`-operators. -/
theorem aux_prop_conc_resampled_form_identification_side
    (hd : 2 ≤ d) (zQ : SpatialCoordinates d) (RQ : ℝ) (hRQ : 0 < RQ)
    (S : ResponseSpace (centeredCube zQ RQ hRQ))
    (hS : S.space = killedSobolevGraph (centeredCube zQ RQ hRQ))
    (a b : ℕ → PositiveCoefficient (centeredCube zQ RQ hRQ))
    (A : aux_prop_conc_controlled_forms_analytic_controls d hd zQ RQ hRQ S a)
    (G Gp : DomainL2 (centeredCube zQ RQ hRQ) →L[ℝ] DomainL2 (centeredCube zQ RQ hRQ))
    (hConvG : Tendsto (fun n => volumeResponseOperator S (a n)) atTop (𝓝 G))
    (hConvGp : Tendsto (fun n => volumeResponseOperator S (b n)) atTop (𝓝 Gp))
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.toClosedForm.energy u = limitFormEnergy G u)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d)) C)
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (g : SpatialCoordinates d → ℝ) (hg : Continuous g)
    (hweight : ∀ n, (b n).val =ᵐ[volume.restrict
        (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d))]
      fun x => Real.exp (g x) * (a n).val x)
    (E' : _root_.DirichletForm
      (volume.restrict (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d))))
    (hE' : ∀ u, E'.toClosedForm.energy u = limitFormEnergy Gp u) :
    E.domain = E'.domain ∧
      ∀ u ∈ E.domain, E'.form u u = ∫ x, Real.exp (g x) ∂(Gamma.measure u) := by
  obtain ⟨FN', F, EF, hFN', hFconv, _hFsym, _hFpos, hFE, hdomEF, _hcoreEF, hdiagEF⟩ :=
    prop_conc_controlled_weighted_convergence hd zQ RQ hRQ S hS a b A
      (fun n => volumeResponseOperator S (a n)) G
      (fun n f => volumeResponseOperator_apply S (a n) f) hConvG E hE hcore
      Gamma (fun x => Real.exp (g x))
      (Real.continuous_exp.comp hg).continuousOn (fun x _ => Real.exp_pos _) hweight
  have hFNeq : FN' = fun n => volumeResponseOperator S (b n) := by
    funext n
    apply ContinuousLinearMap.ext
    intro f
    rw [hFN' n f, volumeResponseOperator_apply S (b n) f]
  have hFGp : F = Gp := by
    rw [hFNeq] at hFconv
    exact tendsto_nhds_unique hFconv hConvGp
  subst hFGp
  have hdomE' : E.domain = E'.domain := by
    apply SetLike.coe_injective
    have h1 := aux_thm_prop_domain_eq_of_energy EF.toClosedForm F hFE
    have h2 := aux_thm_prop_domain_eq_of_energy E'.toClosedForm F hE'
    rw [hdomEF]
    exact h1.trans h2.symm
  refine ⟨hdomE', ?_⟩
  intro u hu
  have huEF : u ∈ EF.domain := hdomEF ▸ hu
  have huE' : u ∈ E'.domain := hdomE' ▸ hu
  have h1 := aux_thm_prop_form_eq_toReal_energy E'.toClosedForm F hE' u huE'
  have h2 := aux_thm_prop_form_eq_toReal_energy EF.toClosedForm F hFE u huEF
  rw [h1, ← h2, hdiagEF u hu]

/-- The same, for the actual cutoff coefficients of `ω` and of its resampling `ω[j ← y]` along a strictly
increasing cutoff sequence `N`: analytic controls along a subsequence of `N`, and the coefficient
factorization `A_N(ω[j ← y]) = exp (y - ω_j) A_N(ω)` for `N ≥ |j|`, give the weighted diagonal. -/
theorem aux_prop_conc_resampled_form_identification_cutoffs
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (zQ : SpatialCoordinates d) (RQ : ℝ) (hRQ : 0 < RQ)
    (S : ResponseSpace (centeredCube zQ RQ hRQ))
    (hS : S.space = killedSobolevGraph (centeredCube zQ RQ hRQ))
    (N : ℕ → ℕ) (hN : StrictMono N)
    (omega : BilateralField d) (y : C(SpatialCoordinates d, ℝ)) (j : ℤ)
    (G Gp : DomainL2 (centeredCube zQ RQ hRQ) →L[ℝ] DomainL2 (centeredCube zQ RQ hRQ))
    (hG : Tendsto (fun n => volumeResponseOperator S
      (cutoffPositiveCoefficient model H omega (N n) zQ hRQ)) atTop (𝓝 G))
    (hctrl : ∃ seq : ℕ → ℕ, StrictMono seq ∧
      Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd zQ RQ hRQ S
        (fun n => cutoffPositiveCoefficient model H omega (N (seq n)) zQ hRQ)))
    (hcoef : ∀ N₀ : ℕ, j.natAbs ≤ N₀ →
      (cutoffPositiveCoefficient model H (Function.update omega j y) N₀ zQ hRQ).val
        =ᵐ[volume.restrict (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d))]
        (fun x => Real.exp (y x - omega j x) *
          (cutoffPositiveCoefficient model H omega N₀ zQ hRQ).val x))
    (hGp : Tendsto (fun n => volumeResponseOperator S
      (cutoffPositiveCoefficient model H (Function.update omega j y) (N n) zQ hRQ))
      atTop (𝓝 Gp))
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.toClosedForm.energy u = limitFormEnergy G u)
    (hcore : ∃ C, DirichletForm.IsCoreOn E.toClosedForm
      (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d)) C)
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (E' : _root_.DirichletForm
      (volume.restrict (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d))))
    (hE' : ∀ u, E'.toClosedForm.energy u = limitFormEnergy Gp u) :
    E.domain = E'.domain ∧
      ∀ u ∈ E.domain, E'.form u u = ∫ x, Real.exp (y x - omega j x) ∂(Gamma.measure u) := by
  obtain ⟨seq, hseq, ⟨A⟩⟩ := hctrl
  set n0 : ℕ := j.natAbs with hn0
  have hshift : StrictMono (fun n : ℕ => n + n0) := fun a b h => by
    simp only []
    omega
  have hseq' : StrictMono (fun n => seq (n + n0)) := hseq.comp hshift
  have hA := aux_prop_conc_controlled_forms_controls_reindex A (fun n => n + n0)
  refine aux_prop_conc_resampled_form_identification_side hd zQ RQ hRQ S hS
    (fun n => cutoffPositiveCoefficient model H omega (N (seq (n + n0))) zQ hRQ)
    (fun n => cutoffPositiveCoefficient model H (Function.update omega j y)
      (N (seq (n + n0))) zQ hRQ) hA G Gp
    (hG.comp hseq'.tendsto_atTop) (hGp.comp hseq'.tendsto_atTop) E hE hcore Gamma
    (fun x => y x - omega j x) (y.continuous.sub (omega j).continuous) ?_ E' hE'
  intro n
  apply hcoef
  have h1 : n + n0 ≤ seq (n + n0) := hseq.id_le (n + n0)
  have h2 : seq (n + n0) ≤ N (seq (n + n0)) := hN.id_le (seq (n + n0))
  omega

end Side

/-- Form-level identification of a tied pair `Yc` at the resampled configuration `ω[j ← y]` with the
`exp (y - ω_j)`-weighted forms of a tied pair `Y` at `ω`, from operator-level data on both sides
(`E` along `NE`, `F` along `NF`).  These are exactly the three form-level premises of the masked-measure
identification `prop_conc_masked_measure_identification`. -/
theorem prop_conc_resampled_form_identification
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (zQ : SpatialCoordinates d) (RQ : ℝ) (hRQ : 0 < RQ)
    (zc : SpatialCoordinates d) (rc : ℝ) (hrc : 0 < rc) (C0 m M : ℝ)
    (S : ResponseSpace (centeredCube zQ RQ hRQ))
    (hS : S.space = killedSobolevGraph (centeredCube zQ RQ hRQ))
    (NE NF : ℕ → ℕ) (hNE : StrictMono NE) (hNF : StrictMono NF)
    (omega : BilateralField d) (y : C(SpatialCoordinates d, ℝ)) (j : ℤ)
    (hcoef : ∀ N₀ : ℕ, j.natAbs ≤ N₀ →
      (cutoffPositiveCoefficient model H (Function.update omega j y) N₀ zQ hRQ).val
        =ᵐ[volume.restrict (centeredCube zQ RQ hRQ : Set (SpatialCoordinates d))]
        (fun x => Real.exp (y x - omega j x) *
          (cutoffPositiveCoefficient model H omega N₀ zQ hRQ).val x))
    (Y Yc : prop_conc_pair_data (centeredCube zQ RQ hRQ) zc rc hrc C0 m M)
    (GE GF GpE GpF : DomainL2 (centeredCube zQ RQ hRQ) →L[ℝ] DomainL2 (centeredCube zQ RQ hRQ))
    (hGE : Tendsto (fun n => volumeResponseOperator S
      (cutoffPositiveCoefficient model H omega (NE n) zQ hRQ)) atTop (𝓝 GE))
    (hGF : Tendsto (fun n => volumeResponseOperator S
      (cutoffPositiveCoefficient model H omega (NF n) zQ hRQ)) atTop (𝓝 GF))
    (hctrlE : ∃ seq : ℕ → ℕ, StrictMono seq ∧
      Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd zQ RQ hRQ S
        (fun n => cutoffPositiveCoefficient model H omega (NE (seq n)) zQ hRQ)))
    (hctrlF : ∃ seq : ℕ → ℕ, StrictMono seq ∧
      Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd zQ RQ hRQ S
        (fun n => cutoffPositiveCoefficient model H omega (NF (seq n)) zQ hRQ)))
    (hGpE : Tendsto (fun n => volumeResponseOperator S
      (cutoffPositiveCoefficient model H (Function.update omega j y) (NE n) zQ hRQ))
      atTop (𝓝 GpE))
    (hGpF : Tendsto (fun n => volumeResponseOperator S
      (cutoffPositiveCoefficient model H (Function.update omega j y) (NF n) zQ hRQ))
      atTop (𝓝 GpF))
    (hYE : ∀ u, Y.E.toClosedForm.energy u = limitFormEnergy GE u)
    (hYF : ∀ u, Y.F.toClosedForm.energy u = limitFormEnergy GF u)
    (hYcE : ∀ u, Yc.E.toClosedForm.energy u = limitFormEnergy GpE u)
    (hYcF : ∀ u, Yc.F.toClosedForm.energy u = limitFormEnergy GpF u) :
    Y.E.domain = Yc.E.domain ∧
    (∀ u ∈ Y.E.domain,
      Yc.E.form u u = ∫ x, Real.exp (y x - omega j x) ∂(Y.GammaE.measure u)) ∧
    (∀ u ∈ Y.F.domain,
      Yc.F.form u u = ∫ x, Real.exp (y x - omega j x) ∂(Y.GammaF.measure u)) := by
  have hE := aux_prop_conc_resampled_form_identification_cutoffs hd model H zQ RQ hRQ S hS NE hNE
    omega y j GE GpE hGE hctrlE hcoef hGpE Y.E hYE Y.hEc Y.GammaE Yc.E hYcE
  have hF := aux_prop_conc_resampled_form_identification_cutoffs hd model H zQ RQ hRQ S hS NF hNF
    omega y j GF GpF hGF hctrlF hcoef hGpF Y.F hYF Y.hFc Y.GammaF Yc.F hYcF
  exact ⟨hE.1, hE.2, hF.2⟩

end
end Paper
