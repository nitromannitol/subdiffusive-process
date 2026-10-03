module

public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.Lane2.CellDirichlet
public import SubdiffusiveProcess.Paper.lane4_smoothed_neumann_source_scaling

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Paper



theorem aux_prop_neumann_growth_solution_bridge
    (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (a : PositiveCoefficient (unitNeumannCube d))
    (rho : ℝ → ℝ) (pvec : Fin d → ℝ) (eps : ℝ)
    (v0 : meanZeroSobolevGraph (unitNeumannCube d))
    (hsolve0 : SolvesNeumann a (faceBump rho pvec eps) v0)
    (E0 : ℝ)
    (hE0 : sobolevCoefficientForm a (v0 : SobolevData (unitNeumannCube d))
      (v0 : SobolevData (unitNeumannCube d)) ≤ E0) :
    ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
      SolvesNeumann a (faceBump rho pvec eps) v →
      sobolevCoefficientForm a (v : SobolevData (unitNeumannCube d))
        (v : SobolevData (unitNeumannCube d)) ≤ E0 := by
  have hP : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
      ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖ := by
    cases d with
    | zero =>
        refine ⟨0, ?_⟩
        intro u
        let u1 : DomainL2 (unitNeumannCube 0) :=
          (u : SobolevData (unitNeumannCube 0)).1
        let x0 : SpatialCoordinates 0 := fun i => i.elim0
        let c : ℝ := u1 x0
        have hQ : (unitNeumannCube 0 : Set (SpatialCoordinates 0)) = Set.univ := by
          ext x
          simp [unitNeumannCube, centeredCube]
        have hv : volume (unitNeumannCube 0 : Set (SpatialCoordinates 0)) = 1 := by
          simpa [unitNeumannCube] using
            (centeredCube_volume (fun i : Fin 0 => (1 / 2 : ℝ)) one_pos)
        have hvuniv : volume (Set.univ : Set (SpatialCoordinates 0)) = 1 := by
          rw [← hQ]
          exact hv
        have hconst : (u1 : SpatialCoordinates 0 → ℝ) = fun _ => c := by
          funext x
          dsimp [c, x0]
          congr 1
          funext i
          exact i.elim0
        have hu := (mem_meanZeroSobolevGraph_iff
          (u : SobolevData (unitNeumannCube 0))).mp u.property
        have hc : c = 0 := by
          have hi : ∫ x in (unitNeumannCube 0 : Set (SpatialCoordinates 0)), u1 x = c := by
            rw [integral_congr_ae (Filter.Eventually.of_forall (fun x => congrFun hconst x))]
            simp only [integral_const, Measure.real_def, Measure.restrict_apply_univ, hQ,
              hvuniv, ENNReal.toReal_one, one_smul]
          exact hi.symm.trans hu.2
        have hu0 : u1 = 0 := by
          apply Lp.ext
          filter_upwards [Lp.coeFn_zero ℝ 2
              (volume.restrict (unitNeumannCube 0 : Set (SpatialCoordinates 0)))] with x hx
          rw [hconst, hc]
          exact hx.symm
        change ‖u1‖ ≤ (0 : ℝ≥0) * ‖subspaceGradient
          (meanZeroSobolevGraph (unitNeumannCube 0)) u‖
        rw [hu0]
        simp
    | succ n =>
        letI : NeZero (Nat.succ n) := ⟨Nat.succ_ne_zero n⟩
        have hgeom : Homogenization.IsOpenBoundedConvexDomain
            (unitNeumannCube (Nat.succ n) : Set (SpatialCoordinates (Nat.succ n))) := by
          simpa [unitNeumannCube] using
            (lane2_isOpenBoundedConvexDomain_centeredCube
              (fun _ : Fin (Nat.succ n) => (1 / 2 : ℝ)) one_pos)
        exact (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
          (unitNeumannCube (Nat.succ n)) hgeom).2
  intro v hsolve
  let w : meanZeroSobolevGraph (unitNeumannCube d) := v - v0
  have hwweak : (w : SobolevData (unitNeumannCube d)) ∈
      weakSobolevGraph (unitNeumannCube d) :=
    (mem_meanZeroSobolevGraph_iff
      (w : SobolevData (unitNeumannCube d))).mp w.property |>.1
  let ψ : weakSobolevGraph (unitNeumannCube d) :=
    ⟨(w : SobolevData (unitNeumannCube d)), hwweak⟩
  have hv := hsolve ψ
  have hv0 := hsolve0 ψ
  have hdiff : sobolevCoefficientForm a
      (w : SobolevData (unitNeumannCube d))
      (w : SobolevData (unitNeumannCube d)) = 0 := by
    change sobolevCoefficientForm a
      ((v : SobolevData (unitNeumannCube d)) -
        (v0 : SobolevData (unitNeumannCube d)))
      (w : SobolevData (unitNeumannCube d)) = 0
    rw [map_sub, ContinuousLinearMap.sub_apply]
    rw [show sobolevCoefficientForm a (v : SobolevData (unitNeumannCube d))
          (w : SobolevData (unitNeumannCube d)) =
          ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
            faceBump rho pvec eps x * (w : SobolevData (unitNeumannCube d)).1 x by
          exact hv]
    rw [show sobolevCoefficientForm a (v0 : SobolevData (unitNeumannCube d))
          (w : SobolevData (unitNeumannCube d)) =
          ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
            faceBump rho pvec eps x * (w : SobolevData (unitNeumannCube d)).1 x by
          exact hv0]
    exact sub_self _
  obtain ⟨K, hPK⟩ := hP
  obtain ⟨c, hc, ha⟩ := a.property
  have hgrad : sobolevGradient (w : SobolevData (unitNeumannCube d)) = 0 := by
    apply eq_zero_of_coercive_self_le_zero (weightedGradientForm_coercive a.val hc ha)
    change sobolevCoefficientForm a
        (w : SobolevData (unitNeumannCube d))
        (w : SobolevData (unitNeumannCube d)) ≤ 0
    rw [hdiff]
  have hgrad_sub : subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) w = 0 := by
    change sobolevGradient (w : SobolevData (unitNeumannCube d)) = 0
    exact hgrad
  have hwzero : w = 0 := by
    apply (subspaceGradient_antilipschitz
      (meanZeroSobolevGraph (unitNeumannCube d)) K hPK).injective
    simpa [hgrad_sub]
  have hv_eq : v = v0 := by
    change v - v0 = 0 at hwzero
    exact sub_eq_zero.mp hwzero
  rw [hv_eq]
  exact hE0

end Paper
