module

public import SubdiffusiveProcess.Paper.thm_prop_base
public import SubdiffusiveProcess.Paper.conv_represented_env_interface
public import SubdiffusiveProcess.Paper.conv_represented_env_interface_grids
public import SubdiffusiveProcess.Paper.conv_represented_catalogue_grids
public import SubdiffusiveProcess.Paper.conv_represented_joint_buffered
public import SubdiffusiveProcess.Paper.conv_represented_joint_grids_buffered
public import SubdiffusiveProcess.Paper.conv_represented_limit_planes
public import SubdiffusiveProcess.Paper.limit_form_package_controls
public import SubdiffusiveProcess.Paper.limit_form_package_side
public import SubdiffusiveProcess.Paper.thm_prop_env_catalogue
public import SubdiffusiveProcess.Paper.thm_prop_env_select

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

section Part0
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- Boundary-energy sets of two nested limit sides agree on cells inside the smaller cube,
for arbitrary coefficient sequences that agree a.e. on the smaller cube. -/
theorem aux_thm_prop_env_side_boundary_restriction
    (d : ℕ) (hd : 2 ≤ d)
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
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
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasEnergyMeasure F)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)
    (zQ zq : SpatialCoordinates d) (R r : ℝ) (hR : 0 < R) (hr : 0 < r)
    (hqQ : (centeredCube zq r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR : Set (SpatialCoordinates d)))
    (SQ : ResponseSpace (centeredCube zQ R hR))
    (Sq : ResponseSpace (centeredCube zq r hr))
    (hSQ : SQ.space = killedSobolevGraph (centeredCube zQ R hR))
    (hSq : Sq.space = killedSobolevGraph (centeredCube zq r hr))
    (GQ : DomainL2 (centeredCube zQ R hR) →L[ℝ] DomainL2 (centeredCube zQ R hR))
    (Gq : DomainL2 (centeredCube zq r hr) →L[ℝ] DomainL2 (centeredCube zq r hr))
    (aQ : ℕ → PositiveCoefficient (centeredCube zQ R hR))
    (aq : ℕ → PositiveCoefficient (centeredCube zq r hr))
    (hcoeff : ∀ n, ((aQ n).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube zq r hr : Set (SpatialCoordinates d))]
        ((aq n).val : SpatialCoordinates d → ℝ))
    (A : aux_limit_form_package_limit_side d hd zQ R hR SQ GQ aQ)
    (B : aux_limit_form_package_limit_side d hd zq r hr Sq Gq aq)
    (zc : SpatialCoordinates d) (rc : ℝ) (hrc : 0 < rc)
    (hcell : closure (centeredCube zc rc hrc : Set (SpatialCoordinates d)) ⊆
      (centeredCube zq r hr : Set (SpatialCoordinates d))) :
    ∀ b : SpatialCoordinates d → ℝ,
      aux_thm_prop_boundary_energy_set (centeredCube zQ R hR) A.form.toClosedForm A.gamma
        (centeredCube zc rc hrc : Set (SpatialCoordinates d)) b =
      aux_thm_prop_boundary_energy_set (centeredCube zq r hr) B.form.toClosedForm B.gamma
        (centeredCube zc rc hrc : Set (SpatialCoordinates d)) b := by
  obtain ⟨cQ⟩ := aux_limit_form_package_controls_of_bounds hd zQ R hR SQ GQ aQ A.bounds
  obtain ⟨cq⟩ := aux_limit_form_package_controls_of_bounds hd zq r hr Sq Gq aq B.bounds
  have AQ : aux_thm_prop_analytic_controls d hd zQ R hR SQ aQ :=
    { K := cQ.K, K_pos := cQ.K_pos, coercive := cQ.coercive,
      interpolation := cQ.interpolation, sources := cQ.sources,
      sources_countable := cQ.sources_countable, sources_dense := cQ.sources_dense,
      sources_smooth := cQ.sources_smooth, mesh := cQ.mesh,
      t := cQ.t, t_lower := cQ.t_lower, t_upper := cQ.t_upper, cutoffs := cQ.cutoffs }
  have Aq : aux_thm_prop_analytic_controls d hd zq r hr Sq aq :=
    { K := cq.K, K_pos := cq.K_pos, coercive := cq.coercive,
      interpolation := cq.interpolation, sources := cq.sources,
      sources_countable := cq.sources_countable, sources_dense := cq.sources_dense,
      sources_smooth := cq.sources_smooth, mesh := cq.mesh,
      t := cq.t, t_lower := cq.t_lower, t_upper := cq.t_upper, cutoffs := cq.cutoffs }
  exact aux_thm_prop_controlled_boundary_restriction BD BDQ EM hcontract
    zQ zq R r hR hr hqQ SQ Sq hSQ hSq aQ aq hcoeff A.form B.form AQ Aq
    A.response B.response GQ Gq A.response_eq B.response_eq
    A.response_tendsto B.response_tendsto A.energy_eq B.energy_eq
    B.core A.core A.gamma B.gamma zc rc hrc hcell

end Part0

section Part1
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- Ambient affine boundary minima for the environment catalogue: for a cell `jC` with triple
parent `jP` inside the cube `jQ`, the boundary energy set of every package side of `jQ` has the
actual affine matrix as greatest lower bound. -/
theorem aux_thm_prop_env_minima
    (d : ℕ) (hd : 2 ≤ d)
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
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
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasEnergyMeasure F)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (env : ℕ → Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ)
    (hCat : aux_conv_represented_env_interface_catalogue d hd model H Ω P env env z r hr Sspace NE NF alpha eta)
    (hP : ∀ j, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (z j) (r j) (hr j)),
      ‖(u : SobolevData (centeredCube (z j) (r j) (hr j))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (z j) (r j) (hr j))) u‖)
    (AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
    (hconv : ∀ᵐ om ∂P, ∀ j,
      (∀ p : Fin d → ℝ, Tendsto (fun n =>
        affineDirichletResponse (centeredCube_isBounded (z j) (hr j)) (hP j)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NE n) (z j) (hr j)) p /
          (volume (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))).toReal)
        atTop (𝓝 (p ⬝ᵥ (AE j om).mulVec p))) ∧
      (∀ p : Fin d → ℝ, Tendsto (fun n =>
        affineDirichletResponse (centeredCube_isBounded (z j) (hr j)) (hP j)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NF n) (z j) (hr j)) p /
          (volume (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))).toReal)
        atTop (𝓝 (p ⬝ᵥ (AF j om).mulVec p))))
    (hside : ∀ᵐ om ∂P, ∀ j,
      Nonempty (aux_limit_form_package_limit_side d hd (z j) (r j) (hr j) (Sspace j) (GE j om)
        (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NE n) (z j) (hr j))) ∧
      Nonempty (aux_limit_form_package_limit_side d hd (z j) (r j) (hr j) (Sspace j) (GF j om)
        (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NF n) (z j) (hr j))))
    (hrestr : ∀ (N : ℕ → ℕ) (om : Ω) (jQ jP : ℕ)
      (_hsub : (centeredCube (z jP) (r jP) (hr jP) : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)))
      (GQ : DomainL2 (centeredCube (z jQ) (r jQ) (hr jQ)) →L[ℝ]
        DomainL2 (centeredCube (z jQ) (r jQ) (hr jQ)))
      (Gq : DomainL2 (centeredCube (z jP) (r jP) (hr jP)) →L[ℝ]
        DomainL2 (centeredCube (z jP) (r jP) (hr jP)))
      (A : aux_limit_form_package_limit_side d hd (z jQ) (r jQ) (hr jQ) (Sspace jQ) GQ
        (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (N n) (z jQ) (hr jQ)))
      (B : aux_limit_form_package_limit_side d hd (z jP) (r jP) (hr jP) (Sspace jP) Gq
        (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (N n) (z jP) (hr jP)))
      (zc : SpatialCoordinates d) (rc : ℝ) (hrc : 0 < rc)
      (_hcell : closure (centeredCube zc rc hrc : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z jP) (r jP) (hr jP) : Set (SpatialCoordinates d)))
      (b : SpatialCoordinates d → ℝ),
      aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (r jQ) (hr jQ)) A.form.toClosedForm
        A.gamma (centeredCube zc rc hrc : Set (SpatialCoordinates d)) b =
      aux_thm_prop_boundary_energy_set (centeredCube (z jP) (r jP) (hr jP)) B.form.toClosedForm
        B.gamma (centeredCube zc rc hrc : Set (SpatialCoordinates d)) b) :
    ∀ᵐ om ∂P, ∀ jQ jP jC, z jC = z jP → r jP = 3 * r jC →
      (centeredCube (z jP) (r jP) (hr jP) : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) →
      (∀ A : aux_limit_form_package_limit_side d hd (z jQ) (r jQ) (hr jQ) (Sspace jQ) (GE jQ om)
          (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NE n) (z jQ) (hr jQ)),
        ∀ (p : Fin d → ℝ) (c : ℝ),
        IsGLB (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (r jQ) (hr jQ))
          A.form.toClosedForm A.gamma (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))
          (fun x => (∑ i, p i * x i) + c))
          ((volume (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))).toReal *
            (p ⬝ᵥ (AE jC om).mulVec p)) ∧
        (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (r jQ) (hr jQ))
          A.form.toClosedForm A.gamma (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))
          (fun x => (∑ i, p i * x i) + c)).Nonempty) ∧
      (∀ A : aux_limit_form_package_limit_side d hd (z jQ) (r jQ) (hr jQ) (Sspace jQ) (GF jQ om)
          (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NF n) (z jQ) (hr jQ)),
        ∀ (p : Fin d → ℝ) (c : ℝ),
        IsGLB (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (r jQ) (hr jQ))
          A.form.toClosedForm A.gamma (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))
          (fun x => (∑ i, p i * x i) + c))
          ((volume (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))).toReal *
            (p ⬝ᵥ (AF jC om).mulVec p)) ∧
        (aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (r jQ) (hr jQ))
          A.form.toClosedForm A.gamma (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d))
          (fun x => (∑ i, p i * x i) + c)).Nonempty) := by
  obtain ⟨catalogResponse, catalogConstant, responseE, responseF, eventE, eventF,
    root, _hunitRoot, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF,
    ucellE, ucellF, Cext, beta, t, I, coercivityKey, extensionKey, lambdaKey,
    sourceResponseKey, sourceGrowthKey, sourceHolderKey, cellResponseKey, cellGrowthKey,
    cellHolderKey, origin, gridRoot, gridKey, hRepE, hRepF⟩ := hCat
  let : ∀ i, Countable (Dcat i) := hDcat
  have he : ∀ᵐ om ∂P, om ∈ eventE :=
    ae_iff.mpr hRepE.2.2.2.2.2.2.2.2.2.1.2.2.1
  have hf : ∀ᵐ om ∂P, om ∈ eventF :=
    ae_iff.mpr hRepF.2.2.2.2.2.2.2.2.2.1.2.2.1
  have hSpaces := hRepE.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  filter_upwards [he, hf, hconv, hside] with om home homf hc hs jQ jP jC hzC hrP hsub
  have hcell : closure (centeredCube (z jC) (r jC) (hr jC) : Set (SpatialCoordinates d)) ⊆
      (centeredCube (z jP) (r jP) (hr jP) : Set (SpatialCoordinates d)) := by
    intro x hx
    have hdist : dist x (z jC) ≤ r jC / 2 := Metric.closure_ball_subset_closedBall hx
    change dist x (z jP) < r jP / 2
    rw [← hzC, hrP]
    linarith [hr jC]
  have hP' : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (z jP) (r jC) (hr jC)),
      ‖(u : SobolevData (centeredCube (z jP) (r jC) (hr jC))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (z jP) (r jC) (hr jC))) u‖ :=
    killedPoincare_domain_eq (by simp only [centeredCube, hzC]) (hP jC)
  have hAff'E : ∀ p : Fin d → ℝ, Tendsto (fun n =>
        affineDirichletResponse (centeredCube_isBounded (z jP) (hr jC)) hP'
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NE n) (z jP) (hr jC)) p /
          (volume (centeredCube (z jP) (r jC) (hr jC) : Set (SpatialCoordinates d))).toReal)
        atTop (𝓝 (p ⬝ᵥ (AE jC om).mulVec p)) := by
    let P : SpatialCoordinates d → Prop := fun w => ∃ K : ℝ≥0,
      ∀ u : killedSobolevGraph (centeredCube w (r jC) (hr jC)),
        ‖(u : SobolevData (centeredCube w (r jC) (hr jC))).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube w (r jC) (hr jC))) u‖
    let F : (w : SpatialCoordinates d) → P w → Prop := fun w hPw => ∀ p : Fin d → ℝ,
      Tendsto (fun n => affineDirichletResponse (centeredCube_isBounded w (hr jC)) hPw
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NE n) w (hr jC)) p /
          (volume (centeredCube w (r jC) (hr jC) : Set (SpatialCoordinates d))).toReal)
        atTop (𝓝 (p ⬝ᵥ (AE jC om).mulVec p))
    have hM : ∀ hPw : P (z jP), F (z jP) hPw := hzC ▸ (fun hPw : P (z jC) => (hc jC).1)
    exact hM hP'
  have hAff'F : ∀ p : Fin d → ℝ, Tendsto (fun n =>
        affineDirichletResponse (centeredCube_isBounded (z jP) (hr jC)) hP'
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NF n) (z jP) (hr jC)) p /
          (volume (centeredCube (z jP) (r jC) (hr jC) : Set (SpatialCoordinates d))).toReal)
        atTop (𝓝 (p ⬝ᵥ (AF jC om).mulVec p)) := by
    let P : SpatialCoordinates d → Prop := fun w => ∃ K : ℝ≥0,
      ∀ u : killedSobolevGraph (centeredCube w (r jC) (hr jC)),
        ‖(u : SobolevData (centeredCube w (r jC) (hr jC))).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube w (r jC) (hr jC))) u‖
    let F : (w : SpatialCoordinates d) → P w → Prop := fun w hPw => ∀ p : Fin d → ℝ,
      Tendsto (fun n => affineDirichletResponse (centeredCube_isBounded w (hr jC)) hPw
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NF n) w (hr jC)) p /
          (volume (centeredCube w (r jC) (hr jC) : Set (SpatialCoordinates d))).toReal)
        atTop (𝓝 (p ⬝ᵥ (AF jC om).mulVec p))
    have hM : ∀ hPw : P (z jP), F (z jP) hPw := hzC ▸ (fun hPw : P (z jC) => (hc jC).2)
    exact hM hP'
  constructor
  · intro A p c
    obtain ⟨B⟩ := (hs jP).1
    have htransfer := hrestr NE om jQ jP hsub (GE jQ om) (GE jP om) A B (z jC) (r jC) (hr jC)
      hcell (fun x => (∑ i, p i * x i) + c)
    rw [htransfer]
    obtain ⟨controls⟩ := aux_limit_form_package_controls_of_bounds hd (z jP) (r jP) (hr jP)
      (Sspace jP) (GE jP om)
      (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NE n) (z jP) (hr jP))
      B.bounds
    have controls' : aux_thm_prop_analytic_controls d hd (z jP) (r jP) (hr jP) (Sspace jP)
        (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NE n) (z jP) (hr jP)) :=
      { K := controls.K, K_pos := controls.K_pos, coercive := controls.coercive,
        interpolation := controls.interpolation, sources := controls.sources,
        sources_countable := controls.sources_countable, sources_dense := controls.sources_dense,
        sources_smooth := controls.sources_smooth, mesh := controls.mesh, t := controls.t,
        t_lower := controls.t_lower, t_upper := controls.t_upper, cutoffs := controls.cutoffs }
    have hmin := aux_thm_prop_represented_affine_glb_on_padded_cube BD BDQ EM hcontract
      model H Ω P NE env ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
      usrcE srcRepE ucellE Cext beta alpha eta t {1} I ℕ
      (fun i n om => catalogResponse i (NE n) (env n om)) responseE
      (fun i n om => catalogConstant i (NE n) (env n om)) eventE
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey hRepE
      om home jP (r jC) (hr jC) (mul_pos (by norm_num) (hr jC)) hrP jC hzC rfl
      (r jP) (hr jP) hrP (Sspace jP) (hSpaces jP)
      controls' B.response (GE jP om) B.response_eq B.response_tendsto B.form B.gamma
      B.energy_eq B.core hP' (AE jC om) hAff'E p c
    simpa only [hzC] using hmin
  · intro A p c
    obtain ⟨B⟩ := (hs jP).2
    have htransfer := hrestr NF om jQ jP hsub (GF jQ om) (GF jP om) A B (z jC) (r jC) (hr jC)
      hcell (fun x => (∑ i, p i * x i) + c)
    rw [htransfer]
    obtain ⟨controls⟩ := aux_limit_form_package_controls_of_bounds hd (z jP) (r jP) (hr jP)
      (Sspace jP) (GF jP om)
      (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NF n) (z jP) (hr jP))
      B.bounds
    have controls' : aux_thm_prop_analytic_controls d hd (z jP) (r jP) (hr jP) (Sspace jP)
        (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NF n) (z jP) (hr jP)) :=
      { K := controls.K, K_pos := controls.K_pos, coercive := controls.coercive,
        interpolation := controls.interpolation, sources := controls.sources,
        sources_countable := controls.sources_countable, sources_dense := controls.sources_dense,
        sources_smooth := controls.sources_smooth, mesh := controls.mesh, t := controls.t,
        t_lower := controls.t_lower, t_upper := controls.t_upper, cutoffs := controls.cutoffs }
    have hmin := aux_thm_prop_represented_affine_glb_on_padded_cube BD BDQ EM hcontract
      model H Ω P NF env ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
      usrcF srcRepF ucellF Cext beta alpha eta t {1} I ℕ
      (fun i n om => catalogResponse i (NF n) (env n om)) responseF
      (fun i n om => catalogConstant i (NF n) (env n om)) eventF
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey hRepF
      om homf jP (r jC) (hr jC) (mul_pos (by norm_num) (hr jC)) hrP jC hzC rfl
      (r jP) (hr jP) hrP (Sspace jP) (hSpaces jP)
      controls' B.response (GF jP om) B.response_eq B.response_tendsto B.form B.gamma
      B.energy_eq B.core hP' (AF jC om) hAff'F p c
    simpa only [hzC] using hmin

end Part1

section Part2
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open _root_.SubdiffusiveProcess.ResponseMoments
open scoped Topology ENNReal NNReal InnerProductSpace BigOperators

/-- Every centred cube carries a killed mean-zero Poincare inequality. -/
theorem aux_thm_prop_env_hP {d : ℕ} [NeZero d] (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (j : ℕ) : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (z j) (r j) (hr j)),
      ‖(u : SobolevData (centeredCube (z j) (r j) (hr j))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (z j) (r j) (hr j))) u‖ :=
  (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
      (centeredCube (z j) (r j) (hr j))
      (lane2_isOpenBoundedConvexDomain_centeredCube (z j) (hr j))).1

/-- The restriction hypothesis of `aux_thm_prop_env_minima`, from the side boundary restriction. -/
theorem aux_thm_prop_env_hrestr
    (d : ℕ) (hd : 2 ≤ d)
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
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
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasEnergyMeasure F)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω]
    (env : ℕ → Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (hS : ∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i))) :
    ∀ (N : ℕ → ℕ) (om : Ω) (jQ jP : ℕ)
      (_hsub : (centeredCube (z jP) (r jP) (hr jP) : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)))
      (GQ : DomainL2 (centeredCube (z jQ) (r jQ) (hr jQ)) →L[ℝ]
        DomainL2 (centeredCube (z jQ) (r jQ) (hr jQ)))
      (Gq : DomainL2 (centeredCube (z jP) (r jP) (hr jP)) →L[ℝ]
        DomainL2 (centeredCube (z jP) (r jP) (hr jP)))
      (A : aux_limit_form_package_limit_side d hd (z jQ) (r jQ) (hr jQ) (Sspace jQ) GQ
        (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (N n) (z jQ) (hr jQ)))
      (B : aux_limit_form_package_limit_side d hd (z jP) (r jP) (hr jP) (Sspace jP) Gq
        (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (N n) (z jP) (hr jP)))
      (zc : SpatialCoordinates d) (rc : ℝ) (hrc : 0 < rc)
      (_hcell : closure (centeredCube zc rc hrc : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z jP) (r jP) (hr jP) : Set (SpatialCoordinates d)))
      (b : SpatialCoordinates d → ℝ),
      aux_thm_prop_boundary_energy_set (centeredCube (z jQ) (r jQ) (hr jQ)) A.form.toClosedForm
        A.gamma (centeredCube zc rc hrc : Set (SpatialCoordinates d)) b =
      aux_thm_prop_boundary_energy_set (centeredCube (z jP) (r jP) (hr jP)) B.form.toClosedForm
        B.gamma (centeredCube zc rc hrc : Set (SpatialCoordinates d)) b := by
  intro N om jQ jP hsub GQ Gq A B zc rc hrc hcell b
  refine aux_thm_prop_env_side_boundary_restriction d hd BD BDQ EM hcontract (z jQ) (z jP) (r jQ)
    (r jP) (hr jQ) (hr jP) hsub (Sspace jQ) (Sspace jP) (hS jQ) (hS jP) GQ Gq _ _ (fun n => ?_)
    A B zc rc hrc hcell b
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub
      (aux_lem_replace_large_cube_cutoff_positive_coe model H (env n om) (N n) (z jQ) (hr jQ)),
    aux_lem_replace_large_cube_cutoff_positive_coe model H (env n om) (N n) (z jP) (hr jP)]
    with x hQ hq
  exact hQ.trans hq.symm

/-- **The selection data of the environment form, from the represented catalogue.** -/
theorem thm_prop_env_prepared
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn F.toClosedForm
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
      _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.HasEnergyMeasure F)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (env : ℕ → Ω → BilateralField d) (henv : ∀ n, Measurable (env n))
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ)
    (hCat : aux_conv_represented_env_interface_catalogue d hd model H Ω P env env z r hr Sspace
      NE NF alpha eta)
    (hS : ∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i)))
    (hside : ∀ᵐ om ∂P, ∀ j,
      Nonempty (aux_limit_form_package_limit_side d hd (z j) (r j) (hr j) (Sspace j) (GE j om)
        (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NE n) (z j) (hr j))) ∧
      Nonempty (aux_limit_form_package_limit_side d hd (z j) (r j) (hr j) (Sspace j) (GF j om)
        (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NF n) (z j) (hr j))))
    (hplanes : ∀ᵐ om ∂P, ∀ j,
      (∀ A : aux_limit_form_package_limit_side d hd (z j) (r j) (hr j) (Sspace j) (GE j om)
          (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NE n) (z j) (hr j)),
        ∀ u ∈ A.form.domain, ∀ (i : Fin d) (c : ℝ),
          A.gamma.measure u {x : SpatialCoordinates d | x i = c} = 0) ∧
      (∀ A : aux_limit_form_package_limit_side d hd (z j) (r j) (hr j) (Sspace j) (GF j om)
          (fun n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NF n) (z j) (hr j)),
        ∀ u ∈ A.form.domain, ∀ (i : Fin d) (c : ℝ),
          A.gamma.measure u {x : SpatialCoordinates d | x i = c} = 0)) :
    ∃ (AE AF : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ),
      (∀ j om, (AE j om).transpose = AE j om) ∧ (∀ j om, (AF j om).transpose = AF j om) ∧
      (∀ j i k, Measurable (fun om => AE j om i k)) ∧
      (∀ j i k, Measurable (fun om => AF j om i k)) ∧
      (∀ᵐ om ∂P, ∀ j,
        (∀ p : Fin d → ℝ, Tendsto (fun n =>
          affineDirichletResponse (centeredCube_isBounded (z j) (hr j))
            (aux_thm_prop_env_hP z r hr j)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NE n) (z j) (hr j)) p /
            (volume (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))).toReal)
          atTop (𝓝 (p ⬝ᵥ (AE j om).mulVec p))) ∧
        (∀ p : Fin d → ℝ, Tendsto (fun n =>
          affineDirichletResponse (centeredCube_isBounded (z j) (hr j))
            (aux_thm_prop_env_hP z r hr j)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NF n) (z j) (hr j)) p /
            (volume (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))).toReal)
          atTop (𝓝 (p ⬝ᵥ (AF j om).mulVec p)))) ∧
      ∀ (ck : ℝ → ℝ) (m M : ℝ), ∃ prep : aux_thm_prop_env_selection_data d hd Ω P z r hr Sspace GE GF
        (fun i om n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NE n) (z i) (hr i))
        (fun i om n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (env n om) (NF n) (z i) (hr i)) m M,
        prep.AE = AE ∧ prep.AF = AF ∧ prep.ck = ck := by
  obtain ⟨AE, AF, hEsym, hFsym, hEmeas, hFmeas, hconv⟩ :=
    thm_prop_env_catalogue d hd model H Ω P env z r hr Sspace NE NF alpha eta hH henv hCat
      (aux_thm_prop_env_hP z r hr)
  have hrestr := aux_thm_prop_env_hrestr d hd BD BDQ EM hcontract model H Ω env z r hr Sspace hS
  have hmin := aux_thm_prop_env_minima d hd BD BDQ EM hcontract model H Ω P env z r hr Sspace GE GF
    NE NF alpha eta hCat (aux_thm_prop_env_hP z r hr) AE AF hconv hside hrestr
  have hmi := aux_thm_prop_env_mass_indices d hd model H Ω P env env z r hr Sspace NE NF alpha eta hCat
  refine ⟨AE, AF, hEsym, hFsym, hEmeas, hFmeas, hconv, fun ck m M => ?_⟩
  exact ⟨{ AE := AE, AF := AF, ck := ck, measurableE := hEmeas, measurableF := hFmeas
           mass_indices := hmi, minima := hmin, planes := hplanes }, rfl, rfl, rfl⟩

end Part2

end SubdiffusiveProcess.Paper
end
