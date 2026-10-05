module

public import SubdiffusiveProcess.Paper.lem_common_perturbation_equations
public import SubdiffusiveProcess.Paper.cor_14
public import SubdiffusiveProcess.Paper.lem_borel_weights
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

namespace SubdiffusiveProcess.Paper
noncomputable section

theorem aux_lem_common_identity_step_bound {X : Type*} (g : X → ℝ) (hbdd : BddAbove (Set.range (fun x => |g x|))) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : X, ‖Real.exp (g x) - 1‖ ≤ C := by
  rcases hbdd with ⟨S, hS⟩
  refine ⟨Real.exp (max S 0) + 1, by positivity, ?_⟩
  intro x
  have hx : |g x| ≤ max S 0 :=
    le_trans (hS (Set.mem_range_self x)) (le_max_left S 0)
  have hexp_le : Real.exp (g x) ≤ Real.exp (max S 0) :=
    Real.exp_le_exp.mpr (le_trans (le_abs_self (g x)) hx)
  rw [Real.norm_eq_abs]
  apply abs_sub_le_iff.mpr
  constructor
  · linarith
  · have hpos : 0 ≤ Real.exp (max S 0) + Real.exp (g x) := by positivity
    linarith

theorem aux_lem_common_identity_step_si_combo {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X} {F Eg : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m} (GammaF : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure F) (GammaE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Eg) (uF uE phi : Lp ℝ 2 m) (huF : uF ∈ F.domain) (huE_F : uE ∈ F.domain) (hphi_F : phi ∈ F.domain) (_huE_Eg : uE ∈ Eg.domain) (_hphi_Eg : phi ∈ Eg.domain) (c : ℝ) (B : Set X) (hB : MeasurableSet B) (f : X → ℝ) (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x : X, ‖f x‖ ≤ C) : _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (GammaF.cross (uF - uE) phi + (GammaF.cross uE phi - c • GammaE.cross uE phi)) B f = _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (GammaF.cross uF phi) B f - c * _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (GammaE.cross uE phi) B f := by
  have huFsub : uF - uE ∈ F.domain := F.domain.sub_mem huF huE_F
  have hsum : GammaF.cross ((uF - uE) + uE) phi = GammaF.cross (uF - uE) phi + GammaF.cross uE phi :=
    _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure.cross_add_left GammaF huFsub huE_F hphi_F
  rw [sub_add_cancel] at hsum
  have hmeasure : GammaF.cross (uF - uE) phi + (GammaF.cross uE phi - c • GammaE.cross uE phi)
      = GammaF.cross uF phi - c • GammaE.cross uE phi := by
    rw [← add_sub_assoc, ← hsum]
  have hsmul : _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (c • GammaE.cross uE phi) B f
      = c * _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (GammaE.cross uE phi) B f := by
    rcases le_total 0 c with hc | hc
    · exact _root_.SubdiffusiveProcess.Paper.aux_cor_14_signedIntegralOn_smul_nonneg (GammaE.cross uE phi) B f hc
    · have hc' : 0 ≤ -c := by linarith
      have h2 : -((-c) • GammaE.cross uE phi) = c • GammaE.cross uE phi := by
        simpa only [neg_neg] using! congrArg Neg.neg (neg_smul c (GammaE.cross uE phi))
      rw [← h2, _root_.SubdiffusiveProcess.Paper.aux_cor_14_signedIntegralOn_neg_measure ((-c) • GammaE.cross uE phi) B f,
        _root_.SubdiffusiveProcess.Paper.aux_cor_14_signedIntegralOn_smul_nonneg (GammaE.cross uE phi) B f hc']
      ring
  rw [hmeasure, sub_eq_add_neg,
    _root_.SubdiffusiveProcess.Paper.aux_cor_14_signedIntegralOn_add (GammaF.cross uF phi) (-(c • GammaE.cross uE phi)) B hB f hf hC hbound,
    _root_.SubdiffusiveProcess.Paper.aux_cor_14_signedIntegralOn_neg_measure (c • GammaE.cross uE phi) B f,
    hsmul, sub_eq_add_neg]

/--
Fine proof step of `lem_common`.
- The Euler equations are supplied by
  `lem_common_perturbation_equations`.
- The common weighted forms and energy-measure representation are
  supplied by `cor_14` and `lem_borel_weights`.
- The common-domain equalities `hdomEF`, `hdomEg`, and `hdomFg`, the
  memberships `huE`, `huF`, `huEg`, and `huFg`, and the inclusion
  `hV0 : V0 ≤ E.domain` are carried from the formal interface of `lem_common`.  They are needed because form
  and cross-energy bilinearity is available only on the relevant domains;
  none of them is a conclusion of this proof step.
- The concrete cube, form, energy-measure, and variation carriers are
  explicit; the algebraic identity is the conclusion of this step.
- `hbdd` carries the boundedness of g required by `lem_common`. Together with `hg`, it gives
  integrability of exp(g)-1 against the finite Jordan parts; signed-integral
  linearity remains a proof step, not an assumed identity.
-/
theorem lem_common_identity_step
    (d : ℕ) (_hd : 2 ≤ d)
    (Q : Opens (SpatialCoordinates d))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (_hQ : ∃ (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ),
      Q = centeredCube zQ rQ hrQ)
    (_hinside : closure ((centeredCube z r hr : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d)))
    (E F Eg Fg : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GammaE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    (GammaF : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure F)
    (_GammaEg : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Eg)
    (_GammaFg : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Fg)
    (hdomEF : E.domain = F.domain)
    (hdomEg : Eg.domain = E.domain)
    (hdomFg : Fg.domain = E.domain)
    (V0 : Submodule ℝ (DomainL2 Q))
    (hV0 : V0 ≤ E.domain)
    (g : SpatialCoordinates d → ℝ) (hg : Measurable g)
    (hbdd : BddAbove (Set.range (fun x => |g x|)))
    (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B)
    (c : ℝ)
    (uE uF uEg uFg : DomainL2 Q)
    (huE : uE ∈ E.domain)
    (huF : uF ∈ F.domain)
    (huEg : uEg ∈ Eg.domain)
    (huFg : uFg ∈ Fg.domain)
    (hEuler :
      (∀ phi ∈ V0,
        Fg.form (uFg - uF) phi =
          - _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (GammaF.cross uF phi) B
            (fun x => Real.exp (g x) - 1)) ∧
      (∀ phi ∈ V0,
        Eg.form (uEg - uE) phi =
          - _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (GammaE.cross uE phi) B
            (fun x => Real.exp (g x) - 1))) :
    let w := uF - uE
    let vE := uEg - uE
    let vF := uFg - uF
    let z := vF - vE
    ∀ phi ∈ V0,
      Fg.form z phi =
        - _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn
          (GammaF.cross w phi +
            (GammaF.cross uE phi - c • GammaE.cross uE phi))
          B (fun x => Real.exp (g x) - 1) -
        (Fg.form vE phi - c * Eg.form vE phi) := by
  intro w vE vF zz phi hphi
  have hphiE : phi ∈ E.domain := hV0 hphi
  have huE_F : uE ∈ F.domain := hdomEF ▸ huE
  have huE_Eg : uE ∈ Eg.domain := hdomEg.symm ▸ huE
  have hphiF : phi ∈ F.domain := hdomEF ▸ hphiE
  have hphiEg : phi ∈ Eg.domain := hdomEg.symm ▸ hphiE
  have hphiFg : phi ∈ Fg.domain := hdomFg.symm ▸ hphiE
  have huF_Fg : uF ∈ Fg.domain := hdomFg.symm ▸ (hdomEF.symm ▸ huF)
  have huEg_E : uEg ∈ E.domain := hdomEg ▸ huEg
  have huEg_Fg : uEg ∈ Fg.domain := hdomFg.symm ▸ huEg_E
  have huE_Fg : uE ∈ Fg.domain := hdomFg.symm ▸ huE
  have hvF : uFg - uF ∈ Fg.domain := Fg.domain.sub_mem huFg huF_Fg
  have hvE : uEg - uE ∈ Fg.domain := Fg.domain.sub_mem huEg_Fg huE_Fg
  have hsub := Fg.form_sub_left (u := uFg - uF) (v := uEg - uE) (w := phi) hvF hvE hphiFg
  obtain ⟨Cg, hCpos, hbound⟩ := aux_lem_common_identity_step_bound g hbdd
  have hfmeas : Measurable (fun x : SpatialCoordinates d => Real.exp (g x) - 1) :=
    hg.exp.sub measurable_const
  have hSI := aux_lem_common_identity_step_si_combo
    (m := volume.restrict (Q : Set (SpatialCoordinates d)))
    (F := F) (Eg := E) GammaF GammaE uF uE phi huF huE_F hphiF huE hphiE c B hB
    (fun x => Real.exp (g x) - 1) hfmeas hCpos hbound
  rw [hsub, hEuler.1 phi hphi, hEuler.2 phi hphi, hSI]
  ring


end
end SubdiffusiveProcess.Paper
