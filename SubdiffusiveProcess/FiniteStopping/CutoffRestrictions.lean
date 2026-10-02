import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
import SubdiffusiveProcess.Sobolev.CoefficientRestriction
import SubdiffusiveProcess.Lane3.Subdivision
import SubdiffusiveProcess.Lane3.Interfaces
import SubdiffusiveProcess.Geometry.OddGrid
import SubdiffusiveProcess.Lane2.CellDirichlet
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Sobolev.DomainPoincare
import SubdiffusiveProcess.Lane4.Inputs
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJDeterministic
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
import SubdiffusiveProcess.Assumptions.Actions
import SubdiffusiveProcess.Main.LayerScaling
import Mathlib.Tactic
import SubdiffusiveProcess.FiniteStopping.ObservationTree

/-! This module establishes hj0 hq0 exists for finite stopping; it does not assert the full stopping theorem. -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.FiniteStopping

variable {d : ℕ}

/-- cutoffCoefficient ae in the finite stopping construction. -/
theorem cutoffCoefficient_ae
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    (cutoffPositiveCoefficient M H omega N z hr).val =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))]
      (fun x => cutoffCoefficient M H omega N x) := by
  haveI instCubeClosure : Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (closedCube z r hr : Set (SpatialCoordinates d))) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  have hval : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∀ hx : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
        (cutoffPositiveCoefficient M H omega N z hr).val x =
          cutoffCoefficientCM M H omega N z hr ⟨x, centeredCube_subset_closedCube z hr hx⟩ / 1 :=
    normalizedContinuousPositiveCoefficient_coeFn (Ω := centeredCube z r hr)
      (closedCube z r hr) (cutoffCoefficientCM M H omega N z hr)
      (cutoffCoefficientCM_pos M H omega N z hr) 1 one_pos
  filter_upwards [hval, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet]
    with x hx hxΩ
  rw [hx hxΩ, div_one]
  rfl

/-- positiveCoefficientRestrict cutoff in the finite stopping construction. -/
theorem positiveCoefficientRestrict_cutoff
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (zU : SpatialCoordinates d) {rU : ℝ} (hrU : 0 < rU)
    (hU : centeredCube zU rU hrU ≤ centeredCube z r hr) :
    positiveCoefficientRestrict hU (cutoffPositiveCoefficient M H omega N z hr) =
      cutoffPositiveCoefficient M H omega N zU hrU := by
  apply Subtype.ext
  apply MeasureTheory.Lp.ext
  filter_upwards [positiveCoefficientRestrict_coeFn hU (cutoffPositiveCoefficient M H omega N z hr),
    ae_restrict_of_ae_restrict_of_subset hU
      (SubdiffusiveProcess.FiniteStopping.cutoffCoefficient_ae M H omega N z hr),
    SubdiffusiveProcess.FiniteStopping.cutoffCoefficient_ae M H omega N zU hrU]
    with x he ha hb
  rw [he, ha, hb]

/-- root weak zero in the finite stopping construction. -/
theorem root_weak_zero
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (Nidx : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (zP : SpatialCoordinates d) {LR : ℝ} (hLR : 0 < LR)
    (hParentRoot : centeredCube zP LR hLR ≤ centeredCube z r hr)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube z r hr),
      ‖(v : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖@subspaceGradient d (centeredCube z r hr)
          (killedSobolevGraph (centeredCube z r hr)) v‖)
    (b : weakSobolevGraph (centeredCube z r hr))
    (psi : killedSobolevGraph (centeredCube zP LR hLR)) :
    sobolevCoefficientForm (cutoffPositiveCoefficient model H omega Nidx zP hLR)
        (sobolevDataRestrict hParentRoot
          (dirichletMinimizer (killedResponseSpace hP)
            (cutoffPositiveCoefficient model H omega Nidx z hr) b).val)
        (psi : SobolevData (centeredCube zP LR hLR)) =
      ∫ x in (centeredCube zP LR hLR : Set (SpatialCoordinates d)),
        (0 : ℝ) * (psi : SobolevData (centeredCube zP LR hLR)).1 x := by
  set aS := cutoffPositiveCoefficient model H omega Nidx z hr with haS
  set aP := cutoffPositiveCoefficient model H omega Nidx zP hLR with haP
  set u_root := dirichletMinimizer (killedResponseSpace hP) aS b with huroot
  have hab : (aS.val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube zP LR hLR : Set (SpatialCoordinates d))] aP.val := by
    have h1 := positiveCoefficientRestrict_coeFn hParentRoot aS
    rw [SubdiffusiveProcess.FiniteStopping.positiveCoefficientRestrict_cutoff model H omega Nidx
      z hr zP hLR hParentRoot] at h1
    exact h1.symm
  have hmemroot : zeroExtensionSobolevData hParentRoot psi.val ∈
      killedSobolevGraph (centeredCube z r hr) :=
    lane2_zeroExtensionSobolevData_mem_killed hParentRoot psi.property
  have heuler := dirichletMinimizer_euler (killedResponseSpace hP) aS b
    ⟨zeroExtensionSobolevData hParentRoot psi.val, hmemroot⟩
  have hsymm1 : sobolevCoefficientForm aS (zeroExtensionSobolevData hParentRoot psi.val)
      u_root.val = 0 := (sobolevCoefficientForm_symm aS u_root.val
    (zeroExtensionSobolevData hParentRoot psi.val)).symm.trans heuler
  have hze := sobolevCoefficientForm_zeroExtension hParentRoot aS aP hab psi.val u_root.val
  rw [hze] at hsymm1
  have hfinal : sobolevCoefficientForm aP (sobolevDataRestrict hParentRoot u_root.val)
      psi.val = 0 := (sobolevCoefficientForm_symm aP psi.val
    (sobolevDataRestrict hParentRoot u_root.val)).symm.trans hsymm1
  rw [hfinal]
  simp only [zero_mul, integral_zero]

/-- cell2 eq extended fip cell all in the finite stopping construction. -/
theorem cell2_eq_extended_fip_cell_all
    (H1 : ℕ) (hH1 : 0 < H1) (j : ℤ) (z : SpatialCoordinates d) (N B : ℕ)
    (hj0 : 0 ≤ ((H1 * SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℕ) : ℤ) + j)
    (hq0 : 0 ≤ (SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℤ) +
      SubdiffusiveProcess.FiniteStopping.rootQ H1 j)
    (w0 : Fin (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) → OddGridIndex d 1)
    (w : Fin B → OddGridIndex d (subdivisionHalfWidth H1))
    (default : OddGridIndex d (subdivisionHalfWidth H1)) :
    ∃ W : ℕ → OddGridIndex d (subdivisionHalfWidth H1),
      (∀ i : Fin B, W (SubdiffusiveProcess.FiniteStopping.obsLoZ H1 N j + i.val) = w i) ∧
      ∀ (s : ℕ) (hsB : s + 1 ≤ B),
      descendantCenter (subdivisionHalfWidth H1)
          (descendantCenter 1 z ((3 : ℝ) ^ j) (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) w0)
          (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j))
          (s + 1) (SubdiffusiveProcess.FiniteStopping.wordPrefix w (s + 1) hsB) =
        descendantCenter (subdivisionHalfWidth H1)
          (SubdiffusiveProcess.FiniteStopping.rootCell H1 j z
            (fun i => w0 (Fin.castLE (by
              rw [SubdiffusiveProcess.FiniteStopping.t0_split H1 N hH1 j hj0 hq0]; omega) i)))
          ((3 : ℝ) ^ ((H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.rootQ H1 j))
          (SubdiffusiveProcess.FiniteStopping.obsLoZ H1 N j + (s + 1))
          (fun i => W i) := by
  classical
  set obsLoZ := SubdiffusiveProcess.FiniteStopping.obsLoZ H1 N j with hobsLoZ
  set rho := SubdiffusiveProcess.FiniteStopping.rootRho H1 j with hrho
  have hsplit : SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j = rho + H1 * obsLoZ :=
    SubdiffusiveProcess.FiniteStopping.t0_split H1 N hH1 j hj0 hq0
  set blockw0 := SubdiffusiveProcess.FiniteStopping.blockWord H1 obsLoZ
    (fun i => w0 (Fin.cast hsplit.symm (Fin.natAdd rho i))) with hblockw0
  set Wfun : ℕ → OddGridIndex d (subdivisionHalfWidth H1) := fun n =>
      if h : n < obsLoZ then blockw0 ⟨n, h⟩
      else if h2 : n < obsLoZ + B then w ⟨n - obsLoZ, by omega⟩ else default with hWfun
  refine ⟨Wfun, ?_, ?_⟩
  · intro i
    show Wfun (obsLoZ + i.val) = w i
    rw [hWfun]
    dsimp only
    split_ifs with h1 h2
    · omega
    · congr 1
      apply Fin.ext
      show obsLoZ + i.val - obsLoZ = i.val
      omega
    · omega
  · intro s hsB
    have hpre : SubdiffusiveProcess.FiniteStopping.wordPrefix w (s + 1) hsB =
        fun i : Fin (s + 1) => Wfun (Fin.natAdd obsLoZ i) := by
      funext i
      show w (Fin.castLE hsB i) = Wfun (Fin.natAdd obsLoZ i)
      rw [hWfun]
      dsimp only
      have hval : (Fin.natAdd obsLoZ i : ℕ) = obsLoZ + (i : ℕ) := Fin.coe_natAdd obsLoZ i
      rw [hval]
      split_ifs with h1 h2
      · omega
      · congr 1
        apply Fin.ext
        simp only [Fin.coe_castLE]
        omega
      · omega
    have hpref : (fun i : Fin obsLoZ => Wfun (Fin.castLE (Nat.le_add_right obsLoZ (s + 1)) i)) =
        blockw0 := by
      funext i
      show Wfun (Fin.castLE (Nat.le_add_right obsLoZ (s + 1)) i) = blockw0 i
      rw [hWfun]
      dsimp only
      have hval : (Fin.castLE (Nat.le_add_right obsLoZ (s + 1)) i : ℕ) = (i : ℕ) :=
        Fin.coe_castLE _ i
      rw [hval]
      have hilt : (i : ℕ) < obsLoZ := i.isLt
      split_ifs with h1
      congr 1
    rw [SubdiffusiveProcess.FiniteStopping.initial_cell_eq_coarse_root H1 hH1 j z obsLoZ _
      hsplit w0, SubdiffusiveProcess.FiniteStopping.side_split H1 hH1 j obsLoZ _ hsplit]
    simp only [hpre]
    rw [SubdiffusiveProcess.FiniteStopping.descendantCenter_add (subdivisionHalfWidth H1) obsLoZ
        (s + 1)
        (SubdiffusiveProcess.FiniteStopping.rootCell H1 j z
          (fun i => w0 (Fin.castLE (by
            rw [SubdiffusiveProcess.FiniteStopping.t0_split H1 N hH1 j hj0 hq0]; omega) i)))
        ((3 : ℝ) ^ ((H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.rootQ H1 j))
        (fun i => Wfun i)]
    simp only [hpref]
    rfl

/-- hj0 hq0 exists in the finite stopping construction. -/
theorem hj0_hq0_exists
    (H1 : ℕ) (hH1 : 0 < H1) (j : ℤ) :
    ∃ N0 : ℕ, ∀ N, N0 ≤ N →
      0 ≤ ((H1 * SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℕ) : ℤ) + j ∧
      0 ≤ (SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℤ) +
        SubdiffusiveProcess.FiniteStopping.rootQ H1 j := by
  obtain ⟨n0, hn0⟩ := exists_nat_gt
    ((j.natAbs : ℝ) + ((SubdiffusiveProcess.FiniteStopping.rootQ H1 j).natAbs : ℝ))
  refine ⟨4 * H1 * (n0 + 1), fun N hN => ?_⟩
  have hge := SubdiffusiveProcess.FiniteStopping.H1_obsLo_ge_real hH1 N
  have hNr : (4 * H1 * (n0 + 1) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hH1r : (0 : ℝ) < (H1 : ℝ) := by exact_mod_cast hH1
  have hstep : (H1 : ℝ) * ((n0 : ℝ) + 1) ≤
      (H1 : ℝ) * SubdiffusiveProcess.FiniteStopping.obsLo H1 N := by nlinarith only [hH1, hn0, hNr, hH1r, hge, hNr]
  have hobsLoH1 : (H1 : ℝ) * ((n0 : ℝ) + 1) ≤
      (H1 : ℝ) * SubdiffusiveProcess.FiniteStopping.obsLo H1 N := hstep
  have hobsLo : ((n0 : ℝ) + 1) ≤ (SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℝ) :=
    le_of_mul_le_mul_left hstep hH1r
  have hj1 : -(j : ℝ) ≤ (j.natAbs : ℝ) := by
    have h1 : (j.natAbs : ℝ) = |(j : ℝ)| := by
      rw [Nat.cast_natAbs]
      norm_cast
    have h2 : -|(j : ℝ)| ≤ (j : ℝ) := neg_abs_le _
    linarith only [hH1, hn0, hNr, hH1r, hstep, hobsLoH1, hobsLo, h1, h2]
  have hq1 : -(SubdiffusiveProcess.FiniteStopping.rootQ H1 j : ℝ) ≤
      ((SubdiffusiveProcess.FiniteStopping.rootQ H1 j).natAbs : ℝ) := by
    have h1 : ((SubdiffusiveProcess.FiniteStopping.rootQ H1 j).natAbs : ℝ) =
        |(SubdiffusiveProcess.FiniteStopping.rootQ H1 j : ℝ)| := by
      rw [Nat.cast_natAbs]
      norm_cast
    have h2 : -|(SubdiffusiveProcess.FiniteStopping.rootQ H1 j : ℝ)| ≤
        (SubdiffusiveProcess.FiniteStopping.rootQ H1 j : ℝ) := neg_abs_le _
    linarith only [hH1, hn0, hNr, hH1r, hstep, hobsLoH1, hobsLo, hj1, h1, h2]
  have hH1r' : (1 : ℝ) ≤ (H1 : ℝ) := by exact_mod_cast hH1
  have hjlt : (j.natAbs : ℝ) < (n0 : ℝ) := by
    have : (0:ℝ) ≤ ((SubdiffusiveProcess.FiniteStopping.rootQ H1 j).natAbs : ℝ) :=
      Nat.cast_nonneg _
    linarith only [hH1, hn0, hNr, hH1r, hstep, hobsLoH1, hobsLo, hj1, hq1, hH1r', this, hn0]
  have hrootQlt : ((SubdiffusiveProcess.FiniteStopping.rootQ H1 j).natAbs : ℝ) < (n0 : ℝ) := by
    have : (0:ℝ) ≤ (j.natAbs : ℝ) := Nat.cast_nonneg _
    linarith only [hH1, hn0, hNr, hH1r, hstep, hobsLoH1, hobsLo, hj1, hq1, hH1r', hjlt, this, hn0]
  have hobsLoH1' : (n0 : ℝ) + 1 ≤ (H1 : ℝ) * SubdiffusiveProcess.FiniteStopping.obsLo H1 N := by
    nlinarith only [hH1, hn0, hNr, hH1r, hstep, hobsLoH1, hobsLo, hj1, hq1, hH1r', hjlt, hrootQlt, hobsLoH1, hH1r']
  constructor
  · have hcast : ((H1 * SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℕ) : ℝ) =
        (H1 : ℝ) * SubdiffusiveProcess.FiniteStopping.obsLo H1 N := by push_cast; ring
    have : (0 : ℝ) ≤ ((H1 * SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℕ) : ℝ) + (j : ℝ) := by
      rw [hcast]; linarith only [hH1, hn0, hNr, hH1r, hstep, hobsLoH1, hobsLo, hj1, hq1, hH1r', hjlt, hrootQlt, hobsLoH1', hcast, hobsLoH1', hj1, hjlt]
    exact_mod_cast this
  · have : (0 : ℝ) ≤ (SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℝ) +
        (SubdiffusiveProcess.FiniteStopping.rootQ H1 j : ℝ) := by
      linarith only [hH1, hn0, hNr, hH1r, hstep, hobsLoH1, hobsLo, hj1, hq1, hH1r', hjlt, hrootQlt, hobsLoH1', hobsLo, hq1, hrootQlt]
    exact_mod_cast this

end SubdiffusiveProcess.FiniteStopping
