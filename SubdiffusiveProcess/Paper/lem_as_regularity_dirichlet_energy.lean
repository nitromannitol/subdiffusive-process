module

public import SubdiffusiveProcess.Paper.lem_as_regularity_dirichlet_cell
public import SubdiffusiveProcess.Paper.lem_as_regularity_cell_measure
public import SubdiffusiveProcess.Paper.lem_as_regularity_dirichlet_holder
public import SubdiffusiveProcess.Sobolev.GradientEnergyMeasureIntegral

@[expose] public section

/-! Cutoff-uniform Dirichlet local energy follows from the uniform Holder and root coarse bounds.
Every radius is covered by finitely many triadic cells; no pointwise coefficient bound is used. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set Metric SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Dirichlet local energy has a common constant for all cutoffs, data and radii. -/
theorem lem_as_regularity_dirichlet_energy
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sf : SobolevFoundationalInput d hd)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (t : ℝ) (ht1 : (d:ℝ)-1 < t) (htd : t < d) :
    ∃ delta0 : ℝ,0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
      (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d,ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,∃ K : ℝ,0 < K ∧
    ∀ N : ℕ,
    ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),0 ≤ Kf →
      AEMeasurable F (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
      (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),|F y| ≤ Kf) →
    ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),ContDiff ℝ 2 phi →
      c2Norm (closedCube (fun _ : Fin d => (1/2:ℝ)) 1 one_pos : Set (SpatialCoordinates d)) phi ≤ Cphi →
    ∀ b u : weakSobolevGraph (unitNeumannCube d),
      ((b : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] phi →
      SolvesDirichlet (cutoffPositiveCoefficient M H omega N (fun _ => (1/2:ℝ)) one_pos) F b u →
    ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),∀ rad : ℝ,0 < rad →
      localGradientEnergy (cutoffPositiveCoefficient M H omega N (fun _ => (1/2:ℝ)) one_pos)
        (s := ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
        (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤ K*(Kf+Cphi)^2*rad^t := by
  let beta := ((t-(d:ℝ))+4)/4
  have hb : beta ∈ Ioo (1/2:ℝ) 1 := by dsimp only [beta]; constructor <;> linarith only [ht1,htd]
  have hmargin : 0 < (d:ℝ)-2+2*beta-t := by dsimp only [beta]; linarith only [htd]
  let e := min ((beta-1/2)/8) (((d:ℝ)-2+2*beta-t)/4)
  have he : 0 < e := lt_min (by linarith only [hb.1]) (by linarith only [hmargin])
  have hes : e < (beta-1/2)/4 := (min_le_left _ _).trans_lt (by linarith only [hb.1])
  have he1 : e ≤ 1 := hes.le.trans (by linarith only [hb.2])
  have hexp : t ≤ (d:ℝ)-2+2*beta-2*e := by
    have hh : e ≤ ((d:ℝ)-2+2*beta-t)/4 := min_le_right _ _
    linarith only [hh,hmargin]
  obtain ⟨CE,hCE,hcell⟩ := lem_as_regularity_dirichlet_cell d hd E Xc Sf beta e t hb he hes hexp htd.le
  obtain ⟨dh,hdh,hholder⟩ := lem_as_regularity_dirichlet_holder d hd E Pc Xc W Cp Sf D Step Dbase Interp beta
    (by linarith only [hb.1]) hb.2
  obtain ⟨du,hdu,hsup⟩ := lem_as_regularity_unit_sup d hd E Pc Xc W Cp Sf D Step Dbase Interp
  obtain ⟨dc,hdc,hcoarse⟩ := lem_as_coarse d hd E Pc Xc Sf W Cp D inputs_hES_witness Step Dbase Interp
    e beta ⟨he,he1⟩ hb
  obtain ⟨dg,hdg,hgrowth⟩ := prop_growth d hd E Pc Xc W Cp Sf t beta 0 (fun i => Fin.elim0 i)
    ht1 htd (by linarith only [hb.1]) hb.2 (fun i => Fin.elim0 i)
  refine ⟨min dh (min du (min dg (min 1 dc))),lt_min hdh (lt_min hdu (lt_min hdg (lt_min zero_lt_one hdc))),?_⟩
  intro M Rm Sreg It H hIR hdelta
  have hdh' := hdelta.trans (min_le_left _ _)
  have hdu' := hdelta.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdg' := hdelta.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hdc' := hdelta.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨Kg,Cg,-,-,-,hg⟩ := hgrowth M Rm Sreg It H hIR hdg' (fun _ => (1/2:ℝ)) 1 one_pos le_rfl
  filter_upwards [hholder M Rm Sreg It H hIR hdh',hsup M Rm Sreg It H hIR hdu',hg,
    hcoarse M Rm Sreg It H hIR hdc' (fun _ => (1/2:ℝ)) 1 one_pos ⟨0,by norm_num⟩]
    with omega hh hu hg hc
  obtain ⟨Kh,hKh,hh⟩ := hh
  obtain ⟨Ks,hKs,hu⟩ := hu
  obtain ⟨Kr,hKr,hc⟩ := hc
  let Kcell := CE*(Kr*Kh^2+Ks)
  have hKcell : 0 < Kcell := by dsimp only [Kcell]; positivity
  have htp : 0 ≤ t := by
    have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
    linarith only [hdR,ht1]
  refine ⟨(3:ℝ)^d*(6:ℝ)^t*Kcell,by positivity,?_⟩
  intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb0 hsol x hx rad hrad
  have hCphi0 : 0 ≤ Cphi := (aux_prop_growth_holder_assembly_c2Norm_nonneg _ _).trans hCphi
  have hdata : 0 ≤ Kf+Cphi := add_nonneg hKf hCphi0
  obtain ⟨U,hU,hrep,-,-⟩ := (hg N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb0 hsol).2
  have hroot0 := (hc true).1 2 (Or.inr rfl) N
  simp only [ite_true] at hroot0
  have hroot : E.Lam (fun _ => (1/2:ℝ)) 1 one_pos
      (cutoffPositiveCoefficient M H omega N (fun _ => (1/2:ℝ)) one_pos) (fun _ => (1/2:ℝ)) 1 e 2 ≤ Kr :=
    (le_add_of_nonneg_right (inv_pos.mpr (E.lam_pos _ _ _ _ _ _ _ _)).le).trans hroot0
  let a := cutoffPositiveCoefficient M H omega N (fun _ => (1/2:ℝ)) one_pos
  let g := sobolevGradient (u : SobolevData (unitNeumannCube d))
  let mu := gradientEnergyMeasure a g
  have hfinite : IsFiniteMeasure mu := (gradientEnergyMeasure_finite_and_real a g).1
  have hac : mu ≪ volume := (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict
  have hmass (S : Set (SpatialCoordinates d)) (hS : MeasurableSet S) :
      mu.real S = localGradientEnergy a hS g := (gradientEnergyMeasure_finite_and_real a g).2 S hS
  have hcells : ∀ j : ℕ,∀ k : Fin d → ℤ,aux_prop_growth_holder_macro_campanato_Adm j k →
      mu.real (aux_prop_growth_holder_macro_campanato_cell (fun _ => (1/2:ℝ)) j k) ≤
        (Kcell*(Kf+Cphi)^2)*aux_prop_growth_holder_macro_campanato_side j^t := by
    intro j k hk
    rw [hmass _ (aux_prop_growth_holder_macro_campanato_cell_measurable _ _ _)]
    have hc0 := hcell M H omega N Kr hKr.le hroot F Kf (Ks*(Kf+Cphi)) (Kh*(Kf+Cphi)) hKf
      (mul_nonneg hKs.le hdata) (mul_nonneg hKh.le hdata) hFm hFb b u hsol U hU hrep
      (hu N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb0 hsol U hU hrep)
      (hh N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb0 hsol U hU hrep) j k hk
    have hfc : Kf*(Ks*(Kf+Cphi)) ≤ Ks*(Kf+Cphi)^2 := by
      nlinarith only [mul_nonneg (mul_nonneg hKs.le hdata) hCphi0]
    have hcoef : CE*(Kr*(Kh*(Kf+Cphi))^2+Kf*(Ks*(Kf+Cphi))) ≤ Kcell*(Kf+Cphi)^2 := by
      dsimp only [Kcell]
      nlinarith only [mul_le_mul_of_nonneg_left hfc hCE.le]
    exact hc0.trans (mul_le_mul_of_nonneg_right hcoef
      (Real.rpow_nonneg (aux_prop_growth_holder_macro_campanato_side_pos j).le _))
  have hm := lem_as_regularity_cell_measure (fun _ => (1/2:ℝ)) mu hac t (Kcell*(Kf+Cphi)^2) htp
    (by positivity) hcells x hx rad hrad
  change mu.real (ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d))) ≤
    (3:ℝ)^d*(6:ℝ)^t*(Kcell*(Kf+Cphi)^2)*rad^t at hm
  rw [hmass _ (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)] at hm
  convert hm using 1 <;> first | rfl | ring

end SubdiffusiveProcess.Paper
