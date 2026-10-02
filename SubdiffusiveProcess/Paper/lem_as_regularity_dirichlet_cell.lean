import SubdiffusiveProcess.Paper.lem_as_regularity_cell_upper
import SubdiffusiveProcess.Paper.inputs_classical_local_source_response
import SubdiffusiveProcess.Paper.lem_extension
import SubdiffusiveProcess.Analysis.HolderPairBounds
import SubdiffusiveProcess.Analysis.DirichletCellCost
import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.DiscountBounds

/-! Root upper coarse ellipticity and Holder trace control imply local Dirichlet cell energy growth.
The proof supplies no random bound for the root or the solution norms. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set Metric SubdiffusiveProcess SubdiffusiveProcess.Lane4
open Homogenization.Book.Ch02
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace Paper

/-- Uniform root ellipticity and solution bounds control every Dirichlet cell's energy. -/
theorem lem_as_regularity_dirichlet_cell (d : ℕ) (hd : 2 ≤ d)
    (E : in_J d) (X : in_extension d hd E) (Sf : SobolevFoundationalInput d hd)
    (beta e t : ℝ) (hbeta : beta ∈ Ioo (1/2:ℝ) 1) (he : 0 < e)
    (hes : e < (beta-1/2)/4) (ht : t ≤ (d:ℝ)-2+2*beta-2*e) (htd : t ≤ d) :
    ∃ C : ℝ,0 < C ∧ ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d,ℝ)) (omega : BilateralField d) (N : ℕ),
    ∀ Kr : ℝ,0 ≤ Kr →
      E.Lam (fun _ => (1/2:ℝ)) 1 one_pos
        (cutoffPositiveCoefficient M H omega N (fun _ => (1/2:ℝ)) one_pos)
        (fun _ => (1/2:ℝ)) 1 e 2 ≤ Kr →
    ∀ (F : SpatialCoordinates d → ℝ) (Kf Ks Kh : ℝ),0 ≤ Kf → 0 ≤ Ks → 0 ≤ Kh →
      AEMeasurable F (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
      (∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),|F x| ≤ Kf) →
    ∀ b u : weakSobolevGraph (unitNeumannCube d),
      SolvesDirichlet (cutoffPositiveCoefficient M H omega N (fun _ => (1/2:ℝ)) one_pos) F b u →
    ∀ U : SpatialCoordinates d → ℝ,Continuous U →
      ((u : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U →
      (∀ x ∈ (closedCube (fun _ : Fin d => (1/2:ℝ)) 1 one_pos : Set (SpatialCoordinates d)),|U x| ≤ Ks) →
      (∀ x ∈ (closedCube (fun _ : Fin d => (1/2:ℝ)) 1 one_pos : Set (SpatialCoordinates d)),
        ∀ y ∈ (closedCube (fun _ : Fin d => (1/2:ℝ)) 1 one_pos : Set (SpatialCoordinates d)),
        |U x-U y| ≤ Kh*(Real.sqrt (∑ i : Fin d,(x i-y i)^2))^beta) →
    ∀ j : ℕ,∀ k : Fin d → ℤ,aux_prop_growth_holder_macro_campanato_Adm j k →
      localGradientEnergy (cutoffPositiveCoefficient M H omega N (fun _ => (1/2:ℝ)) one_pos)
        (aux_prop_growth_holder_macro_campanato_cell_measurable (fun _ => (1/2:ℝ)) j k)
        (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
        C*(Kr*Kh^2+Kf*Ks)*aux_prop_growth_holder_macro_campanato_side j^t := by
  haveI dimNZ : NeZero d := ⟨by omega⟩
  let s := (beta-1/2)/4
  have hes' : e < s := hes
  have hs : 0 < s := he.trans hes
  have hs1 : s ≤ 1 := by dsimp only [s]; linarith only [hbeta.2]
  obtain ⟨CE,hCE,hresponse⟩ := aux_lem_extension_boundary_half d hd E X Sf beta hbeta
  let CL := geometricDiscount s 2/geometricDiscount e 2*(1-(3:ℝ)^(-2*(s-e)))⁻¹
  have hCL : 0 < CL := by
    have hpow : (3:ℝ)^(-2*(s-e)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hes'])
    exact mul_pos (div_pos (book_geometricDiscount_pos (by positivity))
      (book_geometricDiscount_pos (by positivity))) (inv_pos.mpr (sub_pos.mpr hpow))
  refine ⟨CE*CL+2,by positivity,?_⟩
  intro M H omega N Kr hKr hroot F Kf Ks Kh hKf hKs hKh hFm hFb b u hsol U hU hrep hsup hpair j k hk
  let z := aux_prop_growth_holder_macro_campanato_center (fun _ => (1/2:ℝ)) j k
  let r := aux_prop_growth_holder_macro_campanato_side j
  have hr : 0 < r := aux_prop_growth_holder_macro_campanato_side_pos j
  have hr1 : r ≤ 1 := aux_prop_growth_holder_macro_campanato_side_le_one j
  let aq := cutoffPositiveCoefficient M H omega N z hr
  let aQ := cutoffPositiveCoefficient M H omega N (fun _ => (1/2:ℝ)) one_pos
  have hsub : centeredCube z r hr ≤ unitNeumannCube d :=
    aux_prop_growth_holder_macro_campanato_cell_subset (fun _ => (1/2:ℝ)) hk
  have ha : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),aq.val x=aQ.val x := by
    filter_upwards [(cutoffPositiveCoefficient_representative M H omega N z hr).2.2.2,
      ae_restrict_of_ae_restrict_of_subset hsub
        (cutoffPositiveCoefficient_representative M H omega N (fun _ => (1/2:ℝ)) one_pos).2.2.2]
      with x hx hy
    exact hx.trans hy.symm
  have hclosed : closure (unitNeumannCube d : Set (SpatialCoordinates d)) =
      (closedCube (fun _ : Fin d => (1/2:ℝ)) 1 one_pos : Set (SpatialCoordinates d)) := by
    exact closure_ball _ (by norm_num)
  obtain ⟨hP,-⟩ := exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
    (centeredCube z r hr) (aux_lem_extension_isOpenBoundedConvexDomain_centeredCube z hr)
  obtain ⟨v,hv,henergy⟩ := inputs_classical_local_source_response (by omega : 1 ≤ d)
    (unitNeumannCube d) aQ u F Kf Ks hKf hKs hFm hFb hsol.2 U hU hrep
    (fun x hx => hsup x (by rwa [hclosed] at hx)) z r hr hsub aq ha hP
  have hfront : frontier (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (closedCube (fun _ : Fin d => (1/2:ℝ)) 1 one_pos : Set (SpatialCoordinates d)) := by
    rw [← hclosed]
    exact frontier_subset_closure.trans (closure_mono hsub)
  obtain ⟨hHolder,hsemi⟩ := isHolderOn_and_seminorm_le_of_pairs beta Kh hKh
    (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) U
    (fun x hx y hy => hpair x (hfront hx) y (hfront hy))
  have hresp := hresponse z r hr hr1 hP aq U v hU.continuousOn hHolder hv
  have hsemipos : 0 ≤ holderSeminorm beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) U :=
    aux_lem_extension_holderSeminorm_nonneg _ _ _
  have hsq := pow_le_pow_left₀ (mul_nonneg (Real.rpow_nonneg hr.le beta) hsemipos)
    (mul_le_mul_of_nonneg_left hsemi (Real.rpow_nonneg hr.le beta)) 2
  have hresp' : dirichletResponse (killedResponseSpace hP) aq v ≤
      CE*E.Lam z r hr aq z r s 2*r^((d:ℝ)-2)*(r^beta*Kh)^2 :=
    hresp.trans (mul_le_mul_of_nonneg_left hsq (by
      have hp := E.Lam_pos z r hr aq z r s 2
      positivity))
  have hLam := lem_as_regularity_cell_upper E M H omega N s e he hes hs1 j k hk
  change E.Lam z r hr aq z r s 2 ≤ CL*(3:ℝ)^(2*e*j)*_ at hLam
  have hLam' := hLam.trans (mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ CL*(3:ℝ)^(2*e*j)))
  have hpow : (3:ℝ)^(2*e*j) = r^(-2*e) := by
    dsimp only [r,aux_prop_growth_holder_macro_campanato_side]
    rw [Real.inv_rpow (by positivity),← Real.rpow_natCast,← Real.rpow_mul (by norm_num),
      ← Real.rpow_neg (by norm_num)]
    congr 1
    ring
  rw [hpow] at hLam'
  exact dirichlet_cell_cost_le d r beta e t CE CL Kr Kh Kf Ks
    (E.Lam z r hr aq z r s 2) (dirichletResponse (killedResponseSpace hP) aq v) _
    hr hr1 hCE.le hCL.le hKr hKf hKs ht htd hLam' hresp' henergy

end Paper
