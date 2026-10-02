import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
import SubdiffusiveProcess.Sobolev.CoefficientRestriction
import SubdiffusiveProcess.Lane2.CellDirichlet
import Mathlib.Tactic
import SubdiffusiveProcess.Paper.lem_finite_stopping_partition

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section
namespace Paper



theorem lem_finite_stopping_gluing
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    let Q := centeredCube z r hr
    ∀ hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
      ‖(u : SobolevData Q).1‖ ≤ K * ‖@subspaceGradient d Q (killedSobolevGraph Q) u‖,
    ∀ (ncell : ℕ) (centers : Fin ncell → SpatialCoordinates d)
      (sides : Fin ncell → ℝ) (hside : ∀ i, 0 < sides i),
    let cell := fun i => centeredCube (centers i) (sides i) (hside i)
    ∀ (hle : ∀ i, cell i ≤ Q)
      (hdisjoint : Pairwise (fun i j => Disjoint
        (cell i : Set (SpatialCoordinates d)) (cell j : Set (SpatialCoordinates d))))
      (hcover : (⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume]
        (Q : Set (SpatialCoordinates d)))
      (hPcell : ∀ i, ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (cell i),
        ‖(v : SobolevData (cell i)).1‖ ≤
          K * ‖@subspaceGradient d (cell i) (killedSobolevGraph (cell i)) v‖)
      (a : PositiveCoefficient Q) (b u : weakSobolevGraph Q)
      (hu : u.val - b.val ∈ killedSobolevGraph Q),
    let bcell : ∀ i, weakSobolevGraph (cell i) := fun i =>
      ⟨sobolevDataRestrict (hle i) u.val, sobolevDataRestrict_mem_weak (hle i) u.property⟩
    let vcell := fun i =>
      @dirichletMinimizer d (cell i) (@killedResponseSpace d (cell i) (hPcell i))
        (positiveCoefficientRestrict (hle i) a) (bcell i)
    let cellEnergy := ∑ i : Fin ncell,
      @dirichletResponse d (cell i) (@killedResponseSpace d (cell i) (hPcell i))
        (positiveCoefficientRestrict (hle i) a) (bcell i)
    ∃ v : weakSobolevGraph Q,
      v.val - b.val ∈ killedSobolevGraph Q ∧
      (∀ i, sobolevDataRestrict (hle i) v.val = (vcell i).val) ∧
      sobolevCoefficientForm a v.val v.val = cellEnergy ∧
      @dirichletResponse d Q (@killedResponseSpace d Q hP) a b ≤ cellEnergy := by
  intro Q hP ncell centers sides hside cell hle hdisjoint hcover hPcell a b u hu
  dsimp only
  let bcell : ∀ i : Fin ncell, weakSobolevGraph (cell i) := fun i =>
    ⟨sobolevDataRestrict (hle i) u.val,
      sobolevDataRestrict_mem_weak (hle i) u.property⟩
  let vcell : ∀ i : Fin ncell, weakSobolevGraph (cell i) := fun i =>
    @dirichletMinimizer d (cell i) (@killedResponseSpace d (cell i) (hPcell i))
      (positiveCoefficientRestrict (hle i) a) (bcell i)
  let cellEnergy : ℝ := ∑ i : Fin ncell,
    @dirichletResponse d (cell i) (@killedResponseSpace d (cell i) (hPcell i))
      (positiveCoefficientRestrict (hle i) a) (bcell i)
  change ∃ v : weakSobolevGraph Q,
    v.val - b.val ∈ killedSobolevGraph Q ∧
      (∀ i, sobolevDataRestrict (hle i) v.val = (vcell i).val) ∧
      sobolevCoefficientForm a v.val v.val = cellEnergy ∧
      @dirichletResponse d Q (@killedResponseSpace d Q hP) a b ≤ cellEnergy
  classical
  let φS : SobolevData Q := u.val - b.val
  have hφS : φS ∈ killedSobolevGraph Q := by
    simpa [φS] using hu
  let wk : ∀ i : Fin ncell, SobolevData (cell i) := fun i =>
    (vcell i).val - (bcell i).val
  have hwk : ∀ i : Fin ncell, wk i ∈ killedSobolevGraph (cell i) := by
    intro i
    simpa [wk, vcell] using
      (dirichletMinimizer_mem_affine
        (@killedResponseSpace d (cell i) (hPcell i))
        (positiveCoefficientRestrict (hle i) a) (bcell i))
  obtain ⟨W, hW, hWcell⟩ :=
    lane2_exists_glued_killed cell hle hdisjoint φS hφS wk hwk
  let vdata : SobolevData Q := b.val + W
  have hvdata : vdata ∈ weakSobolevGraph Q := by
    exact (weakSobolevGraph Q).add_mem b.property
      (killedSobolevGraph_le_weakSobolevGraph hW)
  let v : weakSobolevGraph Q := ⟨vdata, hvdata⟩
  have hvb : v.val - b.val ∈ killedSobolevGraph Q := by
    simpa [v, vdata] using hW
  have hvalue (i : Fin ncell) :
      ((domainLpRestrict (hle i) vdata.1 : DomainL2 (cell i)) :
        SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (cell i : Set (SpatialCoordinates d))]
        (((vcell i).val.1 : DomainL2 (cell i)) : SpatialCoordinates d → ℝ) := by
    have h1 := domainLpRestrict_coeFn (hle i) vdata.1
    have h2 := ae_restrict_of_ae_restrict_of_subset (hle i)
      (Lp.coeFn_add b.val.1 W.1)
    have h3 := hWcell i
    have h4 := ae_restrict_of_ae_restrict_of_subset (hle i)
      (Lp.coeFn_sub u.val.1 b.val.1)
    have h5 := domainLpRestrict_coeFn (hle i) u.val.1
    have h6 := Lp.coeFn_sub (vcell i).val.1 (bcell i).val.1
    filter_upwards [h1, h2, h3, h4, h5, h6] with x hx1 hx2 hx3 hx4 hx5 hx6
    calc
      (domainLpRestrict (hle i) vdata.1 : SpatialCoordinates d → ℝ) x =
          (vdata.1 : SpatialCoordinates d → ℝ) x := hx1
      _ = (b.val.1 : SpatialCoordinates d → ℝ) x + (W.1 : SpatialCoordinates d → ℝ) x := by
        exact hx2
      _ = (b.val.1 : SpatialCoordinates d → ℝ) x +
          (((φS.1 : DomainL2 Q) : SpatialCoordinates d → ℝ) x +
            (((wk i).1 : DomainL2 (cell i)) : SpatialCoordinates d → ℝ) x) := by
        rw [hx3]
      _ = (b.val.1 : SpatialCoordinates d → ℝ) x +
          (((u.val.1 : DomainL2 Q) : SpatialCoordinates d → ℝ) x -
            ((b.val.1 : DomainL2 Q) : SpatialCoordinates d → ℝ) x +
            ((((vcell i).val.1 - (bcell i).val.1 : DomainL2 (cell i)) :
              SpatialCoordinates d → ℝ) x)) := by
        rw [show ((φS.1 : DomainL2 Q) : SpatialCoordinates d → ℝ) x =
          ((u.val.1 : DomainL2 Q) : SpatialCoordinates d → ℝ) x -
            ((b.val.1 : DomainL2 Q) : SpatialCoordinates d → ℝ) x by
              simpa [φS] using hx4,
          show ((wk i).1 : DomainL2 (cell i)) x =
            (((vcell i).val.1 - (bcell i).val.1 : DomainL2 (cell i)) :
              SpatialCoordinates d → ℝ) x by rfl]
      _ = (((vcell i).val.1 : DomainL2 (cell i)) : SpatialCoordinates d → ℝ) x := by
        rw [hx6]
        simp only [Pi.sub_apply]
        have hbcell : (((bcell i).val.1 : DomainL2 (cell i)) :
            SpatialCoordinates d → ℝ) x =
          ((domainLpRestrict (hle i) u.val.1 : DomainL2 (cell i)) :
            SpatialCoordinates d → ℝ) x := by
          rfl
        rw [hbcell]
        rw [hx5]
        ring
  have hdata (i : Fin ncell) :
      sobolevDataRestrict (hle i) v.val = (vcell i).val := by
    have hfirst : (sobolevDataRestrict (hle i) v.val).1 = (vcell i).val.1 := by
      apply Lp.ext
      simpa [v] using hvalue i
    have hsecond :
        (sobolevDataRestrict (hle i) v.val).2 = (vcell i).val.2 := by
      have hmem :
          ((sobolevDataRestrict (hle i) v.val).1, (vcell i).val.2) ∈
            weakSobolevGraph (cell i) := by
        rw [hfirst]
        exact (vcell i).property
      exact weakSobolevGraph_gradient_unique
        (sobolevDataRestrict_mem_weak (hle i) v.property) hmem
    exact Prod.ext hfirst hsecond
  obtain ⟨C, hC⟩ := lane2_coeff_ae_bound a
  have hameas : AEStronglyMeasurable (a.val : SpatialCoordinates d → ℝ)
      (volume.restrict (Q : Set (SpatialCoordinates d))) :=
    (Lp.memLp a.val).aestronglyMeasurable
  have hint (j : Fin d) (i : Fin ncell) :
      IntegrableOn
        (fun x => a.val x * (vdata.2 j x * vdata.2 j x))
        (cell i : Set (SpatialCoordinates d)) volume := by
    refine lane2_integrableOn_coeff_mul
      (W := cell i)
      (hameas.mono_measure (Measure.restrict_mono (hle i) le_rfl))
      (ae_restrict_of_ae_restrict_of_subset (μ := (volume : Measure (SpatialCoordinates d)))
        (hle i) hC)
      (MemLp.mono_measure (Measure.restrict_mono (hle i) le_rfl)
        (Lp.memLp (vdata.2 j)))
      (MemLp.mono_measure (Measure.restrict_mono (hle i) le_rfl)
        (Lp.memLp (vdata.2 j)))
  have hsplit (j : Fin d) :
      (∫ x in (Q : Set (SpatialCoordinates d)),
        a.val x * (vdata.2 j x * vdata.2 j x)) =
        ∑ i : Fin ncell, ∫ x in (cell i : Set (SpatialCoordinates d)),
          a.val x * (vdata.2 j x * vdata.2 j x) := by
    rw [← setIntegral_congr_set hcover]
    exact integral_iUnion_fintype
      (fun i => (cell i).isOpen.measurableSet) hdisjoint (hint j)
  have hgrad_ae (j : Fin d) (i : Fin ncell) :
      (fun x => vdata.2 j x) =ᵐ[volume.restrict (cell i : Set (SpatialCoordinates d))]
        (fun x => (vcell i).val.2 j x) := by
    have hclass : domainLpRestrict (hle i) (vdata.2 j) = (vcell i).val.2 j := by
      have hh := congrArg (fun w : SobolevData (cell i) => w.2 j) (hdata i)
      simpa [v, sobolevDataRestrict] using hh
    have hclass_ae :
        ((domainLpRestrict (hle i) (vdata.2 j) : DomainL2 (cell i)) :
          SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (cell i : Set (SpatialCoordinates d))]
          (((vcell i).val.2 j : DomainL2 (cell i)) : SpatialCoordinates d → ℝ) := by
      rw [hclass]
    exact (domainLpRestrict_coeFn (hle i) (vdata.2 j)).symm.trans hclass_ae
  have hterm (j : Fin d) (i : Fin ncell) :
      (∫ x in (cell i : Set (SpatialCoordinates d)),
        a.val x * (vdata.2 j x * vdata.2 j x)) =
      ∫ x in (cell i : Set (SpatialCoordinates d)),
        (positiveCoefficientRestrict (hle i) a).val x *
          ((vcell i).val.2 j x * (vcell i).val.2 j x) := by
    apply integral_congr_ae
    filter_upwards [positiveCoefficientRestrict_coeFn (hle i) a,
      hgrad_ae j i] with x ha hg
    rw [ha, hg]
  have hcell_energy (i : Fin ncell) :
      (∑ j : Fin d, ∫ x in (cell i : Set (SpatialCoordinates d)),
        a.val x * (vdata.2 j x * vdata.2 j x)) =
      dirichletResponse (killedResponseSpace (hPcell i))
        (positiveCoefficientRestrict (hle i) a) (bcell i) := by
    change _ = sobolevCoefficientForm (positiveCoefficientRestrict (hle i) a)
      (vcell i).val (vcell i).val
    rw [sobolevCoefficientForm_apply]
    exact Finset.sum_congr rfl (fun j _ => hterm j i)
  have henergy : sobolevCoefficientForm a v.val v.val = cellEnergy := by
    change sobolevCoefficientForm a vdata vdata = cellEnergy
    rw [sobolevCoefficientForm_apply]
    calc
      (∑ j : Fin d, ∫ x in (Q : Set (SpatialCoordinates d)),
          a.val x * (vdata.2 j x * vdata.2 j x)) =
          ∑ j : Fin d, ∑ i : Fin ncell,
            ∫ x in (cell i : Set (SpatialCoordinates d)),
              a.val x * (vdata.2 j x * vdata.2 j x) := by
        exact Finset.sum_congr rfl (fun j _ => hsplit j)
      _ = ∑ i : Fin ncell, ∑ j : Fin d,
          ∫ x in (cell i : Set (SpatialCoordinates d)),
            a.val x * (vdata.2 j x * vdata.2 j x) := by
        rw [Finset.sum_comm]
      _ = ∑ i : Fin ncell,
          dirichletResponse (killedResponseSpace (hPcell i))
            (positiveCoefficientRestrict (hle i) a) (bcell i) := by
        exact Finset.sum_congr rfl (fun i _ => hcell_energy i)
      _ = cellEnergy := by rfl
  refine ⟨v, hvb, hdata, henergy, ?_⟩
  let w : (@killedResponseSpace d Q hP).space := ⟨v.val - b.val, hvb⟩
  have hbound :=
    (dirichletResponse_isLeast (@killedResponseSpace d Q hP) a b).2
      (Set.mem_range_self w)
  change dirichletResponse (@killedResponseSpace d Q hP) a b ≤
      sobolevCoefficientForm a (b.val + w.val) (b.val + w.val) at hbound
  calc
    dirichletResponse (@killedResponseSpace d Q hP) a b ≤
        sobolevCoefficientForm a (b.val + w.val) (b.val + w.val) := hbound
    _ = sobolevCoefficientForm a v.val v.val := by
      simp [w]
    _ = cellEnergy := henergy

end Paper
