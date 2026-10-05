module

public import SubdiffusiveProcess.Paper.aux_macro_energy_recurrence
public import SubdiffusiveProcess.Paper.prop_growth_macro_energy
public import SubdiffusiveProcess.Analysis.TranslatedHolderNorm

@[expose] public section

/-! A physical Dirichlet solution supplies its exact native carrier and scaled forcing norms.
This construction gives no cutoff-uniform regularity estimate by itself. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal BigOperators Pointwise
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Transporting the Dirichlet solution and smooth datum to the native origin cube preserves all required data. -/
theorem lem_as_regularity_dirichlet_root (d : ℕ) (hd : 2 ≤ d) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ (N : ℕ) (z0 : SpatialCoordinates d)
      (h1 : (0:ℝ) < 1) (hR : (0:ℝ) < 3^N)
      (aQ : PositiveCoefficient (centeredCube z0 1 h1))
      (aT : PositiveCoefficient (centeredCube ((3:ℝ)^N • z0) ((3:ℝ)^N) hR))
      (a : SpatialCoordinates d → ℝ),
      (∀ᵐ y ∂volume.restrict (centeredCube z0 1 h1 : Set (SpatialCoordinates d)),
        aQ.val y = aT.val ((3:ℝ)^N • y)) →
      (∀ᵐ y ∂volume.restrict (openCubeSet (originCube d N)),
        a y = aT.val (y+(3:ℝ)^N • z0)) →
    ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
      AEMeasurable F (volume.restrict (centeredCube z0 1 h1 : Set (SpatialCoordinates d))) →
      (∀ᵐ y ∂volume.restrict (centeredCube z0 1 h1 : Set (SpatialCoordinates d)),|F y| ≤ Kf) →
    ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),ContDiff ℝ 2 phi →
      c2Norm (closedCube z0 1 h1 : Set (SpatialCoordinates d)) phi ≤ Cphi →
    ∀ b u : weakSobolevGraph (centeredCube z0 1 h1),
      ((b : SobolevData (centeredCube z0 1 h1)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z0 1 h1 : Set (SpatialCoordinates d))] phi →
      SolvesDirichlet aQ F b u →
    ∃ un hn : H1Function (openCubeSet (originCube d N)),∃ gn : Vec d → Vec d,
      IsDirichletSolutionOn a (originCube d N) un hn gn ∧
      (un.toFun =ᵐ[volume.restrict (openCubeSet (originCube d N))]
        fun y => ((u : SobolevData (centeredCube z0 1 h1)).1 : SpatialCoordinates d → ℝ)
          (((3:ℝ)^N)⁻¹ • y+z0)) ∧
      MemHolder (cube d N) (1/2) gn ∧ MemHolder (cube d N) (1/2) hn.grad ∧
      (3:ℝ)^((N:ℝ)/2)*holderSeminormOn (cube d N) (1/2) gn ≤
        Cp*((3:ℝ)^N)⁻¹*Kf ∧
      vectorSupNormOn (cube d N) hn.grad+
        (3:ℝ)^((N:ℝ)/2)*holderSeminormOn (cube d N) (1/2) hn.grad ≤
        ((3:ℝ)^N)⁻¹*d*Cphi := by
  obtain ⟨Cp,hCp,hphys⟩ := aux_aux_macro_energy_recurrence_physical_problem hd
  refine ⟨Cp,hCp,?_⟩
  intro N z0 h1 hR aQ aT a hcoef ha F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol
  have hT : (centeredCube ((3:ℝ)^N • z0) ((3:ℝ)^N) hR : Set (SpatialCoordinates d)) =
      (3:ℝ)^N • (centeredCube z0 1 h1 : Set (SpatialCoordinates d)) :=
    aux_aux_macro_energy_recurrence_cube_smul_one z0 hR h1 hR
  have hQT : (centeredCube z0 1 h1 : Set (SpatialCoordinates d)) =
      ((3:ℝ)^N)⁻¹ • (centeredCube ((3:ℝ)^N • z0) ((3:ℝ)^N) hR : Set (SpatialCoordinates d)) := by
    rw [hT,smul_smul,inv_mul_cancel₀ hR.ne',one_smul]
  obtain ⟨ut,hut,hutg⟩ := aux_aux_macro_energy_recurrence_weak_unscale (inv_pos.mpr hR) hQT u
  obtain ⟨bt,hbt,hbtg⟩ := aux_aux_macro_energy_recurrence_weak_unscale (inv_pos.mpr hR) hQT b
  have hDir := aux_aux_macro_energy_recurrence_dirichlet_push hR hT hQT u b hsol.1 ut bt hut hutg hbt hbtg
  obtain ⟨g,hgrad,hgi,hgH,hgS,hweak⟩ := hphys (centeredCube z0 1 h1) ((3:ℝ)^N • z0)
    ((3:ℝ)^N) hR ((3:ℝ)^N) 1 hR zero_lt_one hT aT aQ
    (by simpa only [one_mul] using hcoef) F Kf hKf hFm hFb b u hsol (ut : SobolevData _) hutg
  have hphi1 : ContDiff ℝ 1 phi := hphi.of_le (by norm_num)
  have hbgrad := aux_aux_macro_energy_recurrence_datum_grad phi hphi1 b hb
    (fun i => aux_aux_macro_energy_recurrence_memLp_fderiv (closedCube z0 1 h1)
      (centeredCube_subset_closedCube z0 h1) phi hphi1 i)
  let gh := aux_aux_macro_energy_recurrence_gh phi ((3:ℝ)^N)
  have hghtie : ∀ i : Fin d,(sobolevGradient (bt : SobolevData (centeredCube ((3:ℝ)^N • z0) ((3:ℝ)^N) hR)) i : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube ((3:ℝ)^N • z0) ((3:ℝ)^N) hR : Set (SpatialCoordinates d))]
        fun y => gh y i := by
    intro i
    have hp := aux_aux_macro_energy_recurrence_ae_push hR (centeredCube z0 1 h1).isOpen.measurableSet
      (centeredCube ((3:ℝ)^N • z0) ((3:ℝ)^N) hR).isOpen.measurableSet hT (hbgrad i)
    filter_upwards [hbtg i,hp] with y hy hp
    change (bt : SobolevData (centeredCube ((3:ℝ)^N • z0) ((3:ℝ)^N) hR)).2 i y = _
    rw [hy,hp]
    rfl
  obtain ⟨hghH,hghN⟩ := aux_aux_macro_energy_recurrence_gh_bounds (by omega) z0 h1 hR hR phi hphi Cphi hCphi
  obtain ⟨un,hn,hdir,hhn,hun,_⟩ := aux_prop_growth_macro_energy_origin_package N ((3:ℝ)^N • z0)
    hR aT a ha g hgrad hgi bt ut gh hghtie hweak hDir
  have hhnEq : hn.grad = fun y => gh (y+(3:ℝ)^N • z0) := funext hhn
  refine ⟨un,hn,(fun y => g (y+(3:ℝ)^N • z0)),hdir,?_,
    aux_prop_growth_macro_energy_memHolder_translate N _ hR g hgH,?_,?_,?_⟩
  · have hp := aux_prop_growth_macro_energy_ae_pull_translate' ((3:ℝ)^N • z0) _ _
      (aux_prop_growth_macro_energy_root_eq_translateSet N _ hR) hut
    filter_upwards [hun,hp] with y hy hp
    rw [hy,hp,smul_add,smul_smul,inv_mul_cancel₀ hR.ne',one_smul]
  · rw [hhnEq]
    exact aux_prop_growth_macro_energy_memHolder_translate N _ hR gh hghH
  · rw [folded_source_holderSeminormOn_eq]
    have hh := mul_le_mul_of_nonneg_left hgS (show 0 ≤ (3:ℝ)^((N:ℝ)/2) by positivity)
    rw [aux_aux_macro_energy_recurrence_rpow_half] at hh
    have hid : Real.sqrt ((3:ℝ)^N)*(Cp*Real.sqrt ((3:ℝ)^N)*(1⁻¹*(((3:ℝ)^N)⁻¹)^2*Kf)) =
        Cp*((3:ℝ)^N)⁻¹*Kf := by
      rw [inv_one,one_mul]
      calc _ = Cp*(Real.sqrt ((3:ℝ)^N))^2*(((3:ℝ)^N)⁻¹)^2*Kf := by ring
           _ = _ := by rw [Real.sq_sqrt hR.le]; field_simp
    rw [hid] at hh
    simpa only [aux_aux_macro_energy_recurrence_rpow_half] using hh
  · rw [hhnEq,halfHolderNorm_cube_translate]
    exact hghN

end SubdiffusiveProcess.Paper
