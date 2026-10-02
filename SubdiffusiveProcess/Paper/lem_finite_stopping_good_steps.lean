import SubdiffusiveProcess.Paper.lfsgs_good_steps_constants
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
import SubdiffusiveProcess.Sobolev.CoefficientRestriction
import SubdiffusiveProcess.Lane3.Subdivision
import SubdiffusiveProcess.Geometry.OddGrid
import SubdiffusiveProcess.Lane2.CellDirichlet
import SubdiffusiveProcess.Sobolev.DomainPoincare
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.cutoff_good_scale_input
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Paper.sum_errors_baseline_input
import SubdiffusiveProcess.Lane3.Interfaces
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section
namespace Paper




variable {d : ℕ}

/-! ## The observation window (`FSP.obsLo`/`obsHi`/`obsT0`/`obsB`, `FSPWindow.lean`) -/

/-- Least window index `⌈N / (4 H1)⌉`. -/
def aux_lem_finite_stopping_good_steps_obsLo (H1 N : ℕ) : ℕ := (N + (4 * H1 - 1)) / (4 * H1)

/-- Greatest window index `⌊3N / (4 H1)⌋`. -/
def aux_lem_finite_stopping_good_steps_obsHi (H1 N : ℕ) : ℕ := 3 * N / (4 * H1)

/-- Initial triadic depth `H1 obsLo + j`. -/
def aux_lem_finite_stopping_good_steps_obsT0 (H1 N : ℕ) (j : ℤ) : ℕ :=
  (((H1 * aux_lem_finite_stopping_good_steps_obsLo H1 N : ℕ) : ℤ) + j).toNat

/-- Number of stage-2 levels. -/
def aux_lem_finite_stopping_good_steps_obsB (H1 N : ℕ) : ℕ :=
  aux_lem_finite_stopping_good_steps_obsHi H1 N - aux_lem_finite_stopping_good_steps_obsLo H1 N

/-! ## Word prefixes (`FSP.wordPrefix`, `FSPGeometry.lean`) -/

/-- The length-`k` prefix of a word of length `n`. -/
def aux_lem_finite_stopping_good_steps_wordPrefix {α : Type*} {n : ℕ} (w : Fin n → α) (k : ℕ)
    (hk : k ≤ n) : Fin k → α :=
  fun i => w (Fin.castLE hk i)

theorem aux_lem_finite_stopping_good_steps_wordPrefix_self {α : Type*} {n : ℕ} (w : Fin n → α)
    (hk : n ≤ n) :
    aux_lem_finite_stopping_good_steps_wordPrefix w n hk = w := by
  funext i
  simp only [aux_lem_finite_stopping_good_steps_wordPrefix, Fin.castLE_refl]

theorem aux_lem_finite_stopping_good_steps_wordPrefix_castSucc {α : Type*} {n : ℕ}
    (w : Fin (n + 1) → α) (k : ℕ) (hk : k ≤ n) :
    aux_lem_finite_stopping_good_steps_wordPrefix (fun i : Fin n => w i.castSucc) k hk =
      aux_lem_finite_stopping_good_steps_wordPrefix w k (hk.trans (Nat.le_succ n)) := by
  funext i
  rfl

/-! ## Every descendant cell lies in the subdivision root (`FSPGeometry.lean`) -/

theorem aux_lem_finite_stopping_good_steps_descendantCell_zero (m : ℕ) (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (w : Fin 0 → OddGridIndex d m) :
    (descendantCell m z hr 0 w : Set (SpatialCoordinates d)) = centeredCube z r hr := by
  rw [descendantCell_coe]
  change Metric.ball z (descendantSide m 0 r / 2) = Metric.ball z (r / 2)
  rw [descendantSide_zero]

theorem aux_lem_finite_stopping_good_steps_descendantCell_subset_prefix (m : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∀ (n : ℕ) (w : Fin n → OddGridIndex d m) (k : ℕ) (hk : k ≤ n),
      (descendantCell m z hr n w : Set (SpatialCoordinates d)) ⊆
        descendantCell m z hr k (aux_lem_finite_stopping_good_steps_wordPrefix w k hk) := by
  intro n
  induction n with
  | zero =>
    intro w k hk
    obtain rfl : k = 0 := by omega
    rw [aux_lem_finite_stopping_good_steps_descendantCell_zero,
      aux_lem_finite_stopping_good_steps_descendantCell_zero]
  | succ n ih =>
    intro w k hk
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · have hkn : k ≤ n := by omega
      refine (descendantCell_succ_subset m z hr n w).trans ?_
      have h := ih (fun i => w i.castSucc) k hkn
      rwa [aux_lem_finite_stopping_good_steps_wordPrefix_castSucc] at h
    · obtain rfl : k = n + 1 := by omega
      rw [aux_lem_finite_stopping_good_steps_wordPrefix_self]

theorem aux_lem_finite_stopping_good_steps_descendantCell_subset_root (m : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (n : ℕ) (w : Fin n → OddGridIndex d m) :
    (descendantCell m z hr n w : Set (SpatialCoordinates d)) ⊆ centeredCube z r hr := by
  have h := aux_lem_finite_stopping_good_steps_descendantCell_subset_prefix m z hr n w 0
    (Nat.zero_le n)
  rwa [aux_lem_finite_stopping_good_steps_descendantCell_zero] at h

/-! ## The two-stage cell and its witnesses (`FSPTwoStage.lean`, `FSPCore.lean`) -/

/-- The stage-2 cell of word `w` at depth `s` inside the initial cell `w0`. -/
def aux_lem_finite_stopping_good_steps_cell2 (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (t0 mg : ℕ) (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin s → OddGridIndex d mg) :
    Opens (SpatialCoordinates d) :=
  descendantCell mg (descendantCenter 1 z r t0 w0) (descendantSide_pos 1 t0 hr) s w

theorem aux_lem_finite_stopping_good_steps_cell2_eq_centeredCube (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (t0 mg : ℕ) (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ)
    (w : Fin s → OddGridIndex d mg) :
    aux_lem_finite_stopping_good_steps_cell2 z hr t0 mg w0 s w =
      centeredCube (descendantCenter mg (descendantCenter 1 z r t0 w0)
          (descendantSide 1 t0 r) s w)
        (descendantSide mg s (descendantSide 1 t0 r))
        (descendantSide_pos mg s (descendantSide_pos 1 t0 hr)) := rfl

theorem aux_lem_finite_stopping_good_steps_cell2_subset_initial (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (t0 mg : ℕ) (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ)
    (w : Fin s → OddGridIndex d mg) :
    (aux_lem_finite_stopping_good_steps_cell2 z hr t0 mg w0 s w : Set (SpatialCoordinates d)) ⊆
      descendantCell 1 z hr t0 w0 :=
  aux_lem_finite_stopping_good_steps_descendantCell_subset_root mg _ _ s w

theorem aux_lem_finite_stopping_good_steps_cell2_subset_root (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (t0 mg : ℕ) (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ)
    (w : Fin s → OddGridIndex d mg) :
    (aux_lem_finite_stopping_good_steps_cell2 z hr t0 mg w0 s w : Set (SpatialCoordinates d)) ⊆
      centeredCube z r hr :=
  (aux_lem_finite_stopping_good_steps_cell2_subset_initial z hr t0 mg w0 s w).trans
    (aux_lem_finite_stopping_good_steps_descendantCell_subset_root 1 z hr t0 w0)

theorem aux_lem_finite_stopping_good_steps_cell2_le_root (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (t0 mg : ℕ) (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ)
    (w : Fin s → OddGridIndex d mg) :
    aux_lem_finite_stopping_good_steps_cell2 z hr t0 mg w0 s w ≤ centeredCube z r hr :=
  aux_lem_finite_stopping_good_steps_cell2_subset_root z hr t0 mg w0 s w

/-- Every actual centred cube (hence every stage-2 cell) carries a killed-space Poincare
witness: `Sobolev/DomainPoincare.lean`'s existence theorem applied to `Lane2`'s convexity
fact for a centred cube, transported along the (`rfl`) cell/centeredCube identity above. -/
theorem aux_lem_finite_stopping_good_steps_cell2_killedPoincare [NeZero d]
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (t0 mg : ℕ)
    (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin s → OddGridIndex d mg) :
    ∃ K : ℝ≥0, ∀ v : killedSobolevGraph
        (aux_lem_finite_stopping_good_steps_cell2 z hr t0 mg w0 s w),
      ‖(v : SobolevData (aux_lem_finite_stopping_good_steps_cell2 z hr t0 mg w0 s w)).1‖ ≤
        K * ‖subspaceGradient
          (killedSobolevGraph (aux_lem_finite_stopping_good_steps_cell2 z hr t0 mg w0 s w))
          v‖ := by
  rw [aux_lem_finite_stopping_good_steps_cell2_eq_centeredCube]
  exact (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain _
    (lane2_isOpenBoundedConvexDomain_centeredCube _
      (descendantSide_pos mg s (descendantSide_pos 1 t0 hr)))).1

/-! ## Restricted target response and cell energy (`FSPCore.lean`, `FSPShape.lean`) -/

/-- Target response on a subdomain, with the literal restricted datum and coefficient. -/
def aux_lem_finite_stopping_good_steps_respOn {Q U : Opens (SpatialCoordinates d)}
    (aT : PositiveCoefficient Q) (u : weakSobolevGraph Q) (hU : U ≤ Q)
    (hPU : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph U,
      ‖(v : SobolevData U).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph U) v‖) : ℝ :=
  dirichletResponse (killedResponseSpace hPU) (positiveCoefficientRestrict hU aT)
    ⟨sobolevDataRestrict hU u.val, sobolevDataRestrict_mem_weak hU u.property⟩

/-- The root energy density integrated over a set. -/
def aux_lem_finite_stopping_good_steps_energyOn {Q : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Q) (u : SobolevData Q) (s : Set (SpatialCoordinates d)) : ℝ :=
  ∑ j : Fin d, ∫ x in s, a.val x * (u.2 j x * u.2 j x)

/-! ## Padded child labels (`FSPPad.lean`) -/

/-- `P`-padded child label. -/
def aux_lem_finite_stopping_good_steps_padLabel {m : ℕ} (P : ℕ) (k : OddGridIndex d m) : Prop :=
  ∀ i, P ≤ (k i).val ∧ (k i).val + P ≤ 2 * m

/-! ## The paper's normalizing ratio (`FSPChildren.lean`) -/

/-- The paper's normalizing sequence `κ_J`. -/
def aux_lem_finite_stopping_good_steps_kappaSeq (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (J : ℕ) : ℝ :=
  Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
    SubdiffusiveProcess.CoarseGrainingVocab.ahom model J

/-- The paper's ratio `r_{T,S}(k) = (κ_{T-k}/κ_T) / (κ_{S-k}/κ_S)` at `k = H1 n`. -/
def aux_lem_finite_stopping_good_steps_kappaRatio (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H1 target source n : ℕ) : ℝ :=
  (aux_lem_finite_stopping_good_steps_kappaSeq model (target - H1 * n) /
      aux_lem_finite_stopping_good_steps_kappaSeq model target) /
    (aux_lem_finite_stopping_good_steps_kappaSeq model (source - H1 * n) /
      aux_lem_finite_stopping_good_steps_kappaSeq model source)

open Classical in


theorem lem_finite_stopping_good_steps
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : SobolevFoundationalInput d hd) (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Step : @cutoff_good_scale_input d ⟨by omega⟩)
    (D : @lane4_deterministic_good_scale_input d ⟨by omega⟩)
    (hES : SubdiffusiveProcess.Lane3.EfronSteinMomentInequality)
    (Dbase : @sum_errors_baseline_input d ⟨by omega⟩ _ _) :
    haveI : NeZero d := ⟨by omega⟩
    ∃ P : ℕ, 1 ≤ P ∧
    ∀ θbad : ℝ, 0 < θbad → ∃ H1min : ℕ, ∀ H1 : ℕ, H1min ≤ H1 → 0 < H1 →
    ∃ Cg delta0 : ℝ, 0 < Cg ∧ 0 < delta0 ∧
    ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d model)
      (Sreg : in_6_16 d model) (_It : in_iteration d model Jc Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization model H → model.delta ≤ delta0 →
    ∀ (z : SpatialCoordinates d) (j : ℤ),
    ∀ eta : ℝ, 0 < eta → ∃ (C γ : ℝ) (N0 : ℕ), 0 < C ∧ 0 < γ ∧
    ∀ N M : ℕ, N0 ≤ N → N ≤ M → ∀ reverse : Bool,
    ∀ hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph
        (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j)),
      ‖(v : SobolevData (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j))).1‖ ≤
        K * ‖@subspaceGradient d (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j))
          (killedSobolevGraph (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j))) v‖,
    ∀ b : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j)),
    ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
      (chaosSampleLaw model).toMeasure Bad ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-γ * (N : ℝ))) ∧
      ∀ omega ∉ Bad,
      let hr : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
      let target := if reverse then M else N
      let source := if reverse then N else M
      let aT := cutoffPositiveCoefficient model H omega target z hr
      let aS := cutoffPositiveCoefficient model H omega source z hr
      let u := @dirichletMinimizer d _ (@killedResponseSpace d _ hP) aS b
      let mg := subdivisionHalfWidth H1
      let t0 := aux_lem_finite_stopping_good_steps_obsT0 H1 N j
      let B := aux_lem_finite_stopping_good_steps_obsB H1 N
      ∃ Good : (Fin t0 → OddGridIndex d 1) → (n : ℕ) → (Fin n → OddGridIndex d mg) → Prop,
        (∀ (w0 : Fin t0 → OddGridIndex d 1) (w : Fin B → OddGridIndex d mg),
          ((((Finset.univ : Finset (Fin B)).filter fun i =>
            ¬ Good w0 (i.val + 1)
              (aux_lem_finite_stopping_good_steps_wordPrefix w (i.val + 1) i.isLt)).card :
                ℕ) : ℝ) ≤
              θbad * (N : ℝ) / (H1 : ℝ)) ∧
        (∀ (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin (s + 1) → OddGridIndex d mg),
          s + 1 ≤ B → Good w0 (s + 1) w →
          aux_lem_finite_stopping_good_steps_padLabel P (w (Fin.last s)) →
          aux_lem_finite_stopping_good_steps_respOn aT u
              (aux_lem_finite_stopping_good_steps_cell2_le_root z hr t0 mg w0 (s + 1) w)
              (aux_lem_finite_stopping_good_steps_cell2_killedPoincare z hr t0 mg w0 (s + 1)
                w) ≤
            aux_lem_finite_stopping_good_steps_kappaRatio model H1 target source
                (aux_lem_finite_stopping_good_steps_obsLo H1 N + (s + 1)) *
                aux_lem_finite_stopping_good_steps_respOn aS u
                  (aux_lem_finite_stopping_good_steps_cell2_le_root z hr t0 mg w0 (s + 1) w)
                  (aux_lem_finite_stopping_good_steps_cell2_killedPoincare z hr t0 mg w0
                    (s + 1) w) +
              Cg * eta *
                aux_lem_finite_stopping_good_steps_kappaRatio model H1 target source
                  (aux_lem_finite_stopping_good_steps_obsLo H1 N + (s + 1)) *
                aux_lem_finite_stopping_good_steps_energyOn aS u.val
                  (aux_lem_finite_stopping_good_steps_cell2 z hr t0 mg w0 s
                    (fun i => w i.castSucc))) := by
  exact lfsgs_good_steps_constants d hd Jc Pc Xc Sf W Cp Step D hES Dbase

end Paper
