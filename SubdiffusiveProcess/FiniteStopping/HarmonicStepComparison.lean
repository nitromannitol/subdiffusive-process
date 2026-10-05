module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.CoefficientRestriction
public import SubdiffusiveProcess.ResponseMoments.Subdivision
public import SubdiffusiveProcess.ResponseMoments.Interfaces
public import SubdiffusiveProcess.Geometry.OddGrid
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJDeterministic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
public import SubdiffusiveProcess.Assumptions.Actions
public import SubdiffusiveProcess.Main.LayerScaling
public import Mathlib.Tactic
public import SubdiffusiveProcess.FiniteStopping.BoundaryTraceComparison
public import SubdiffusiveProcess.FiniteStopping.CellRegularity
public import SubdiffusiveProcess.FiniteStopping.CutoffRestrictions
public import SubdiffusiveProcess.FiniteStopping.ObservationStages
public import SubdiffusiveProcess.FiniteStopping.ObservationTree

@[expose] public section

/-! This module establishes comparison at stage for finite stopping; it does not assert the full stopping theorem. -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.FiniteStopping

variable {d : ℕ}

/-- domainLpRestrict ae trans in the finite stopping construction. -/
theorem domainLpRestrict_ae_trans
    {p : ℝ≥0∞} {V U Ω : Opens (SpatialCoordinates d)} (hVU : V ≤ U) (hU : U ≤ Ω)
    (f : Lp ℝ p (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (G : SpatialCoordinates d → ℝ)
    (hG : (domainLpRestrict hU f : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (V : Set (SpatialCoordinates d))] G) :
    (domainLpRestrict (hVU.trans hU) f : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (V : Set (SpatialCoordinates d))] G := by
  rw [← domainLpRestrict_trans hVU hU]
  exact (domainLpRestrict_coeFn hVU (domainLpRestrict hU f)).trans hG

/-- sobolevCoefficientForm eq energyOn in the finite stopping construction. -/
theorem sobolevCoefficientForm_eq_energyOn
    {Ω : Opens (SpatialCoordinates d)} (a : PositiveCoefficient Ω) (u : SobolevData Ω) :
    sobolevCoefficientForm a u u =
      SubdiffusiveProcess.FiniteStopping.energyOn a u (Ω : Set (SpatialCoordinates d)) := by
  unfold sobolevCoefficientForm SubdiffusiveProcess.FiniteStopping.energyOn
  rw [ContinuousLinearMap.bilinearComp_apply, weightedGradientForm_apply]
  refine Finset.sum_congr rfl fun i _ => integral_congr_ae ?_
  filter_upwards with x
  rfl

/-- energyOn restrict eq in the finite stopping construction. -/
theorem energyOn_restrict_eq
    {U Ω : Opens (SpatialCoordinates d)} (hU : U ≤ Ω)
    (a : PositiveCoefficient Ω) (u : SobolevData Ω) :
    SubdiffusiveProcess.FiniteStopping.energyOn (positiveCoefficientRestrict hU a)
        (sobolevDataRestrict hU u) (U : Set (SpatialCoordinates d)) =
      SubdiffusiveProcess.FiniteStopping.energyOn a u (U : Set (SpatialCoordinates d)) := by
  unfold SubdiffusiveProcess.FiniteStopping.energyOn sobolevDataRestrict
  refine Finset.sum_congr rfl fun i _ => integral_congr_ae ?_
  filter_upwards [positiveCoefficientRestrict_coeFn hU a,
    domainLpRestrict_coeFn hU (u.2 i)] with x ha hu
  simp only [ha, hu]

/-- boundary norm nonneg in the finite stopping construction. -/
theorem boundary_norm_nonneg
    (alpha : ℝ) (z : SpatialCoordinates d) (r : ℝ) (G : SpatialCoordinates d → ℝ) :
    0 ≤ cellBoundaryQuotientNorm alpha z r G := by
  apply le_csInf
  · exact ⟨_, 0, rfl⟩
  · rintro v ⟨c, rfl⟩
    exact SubdiffusiveProcess.FiniteStopping.cAlphaNorm_nonneg _ _ _

/-- comparison of reg trace in the finite stopping construction. -/
theorem comparison_of_reg_trace
    [NeZero d]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (alpha eta Cfin pad : ℝ) (heta : 0 < eta) (hCfin : 0 < Cfin) (hpad : 1 < pad)
    (H1 n target source : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube z r hr),
      ‖(v : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) v‖)
    (b : weakSobolevGraph (centeredCube z r hr))
    (zQ zP : SpatialCoordinates d) (rQ rP : ℝ) (hrQ : 0 < rQ) (hrP : 0 < rP)
    (hdepth : rQ = (3 : ℝ) ^ (-((H1 * n : ℕ) : ℤ)))
    (hsize : rP = (3 : ℝ) ^ H1 * rQ)
    (hQroot : centeredCube zQ rQ hrQ ≤ centeredCube z r hr)
    (hProot : centeredCube zP rP hrP ≤ centeredCube z r hr)
    (hQP : centeredCube zQ rQ hrQ ≤ centeredCube zP rP hrP)
    (idx : OddGridIndex d (subdivisionHalfWidth H1))
    (hcenter : zQ = oddGridCenter zP rP (subdivisionHalfWidth H1) idx)
    (hcontained : (closedCube zQ (pad * rQ) (mul_pos (lt_trans zero_lt_one hpad) hrQ) :
        Set (SpatialCoordinates d)) ⊆ centeredCube zP rP hrP)
    (hReg : SubdiffusiveProcess.FiniteStopping.Reg model H alpha H1 pad Cfin hpad
      source (H1 * n) zQ omega)
    (hTrace : SubdiffusiveProcess.FiniteStopping.trace_close model H alpha eta
      target source (H1 * n) zQ omega)
    (hPQ : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube zQ rQ hrQ),
      ‖(v : SobolevData (centeredCube zQ rQ hrQ)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube zQ rQ hrQ)) v‖) :
    let aT := cutoffPositiveCoefficient model H omega target z hr
    let aS := cutoffPositiveCoefficient model H omega source z hr
    let u := dirichletMinimizer (killedResponseSpace hP) aS b
    SubdiffusiveProcess.FiniteStopping.respOn aT u hQroot hPQ ≤
      SubdiffusiveProcess.FiniteStopping.kappaRatio model H1 target source n *
        SubdiffusiveProcess.FiniteStopping.respOn aS u hQroot hPQ +
      Cfin ^ 2 * eta * SubdiffusiveProcess.FiniteStopping.kappaRatio model H1 target source n *
        SubdiffusiveProcess.FiniteStopping.energyOn aS u.val (centeredCube zP rP hrP) := by
  subst rP
  subst rQ
  let aT := cutoffPositiveCoefficient model H omega target z hr
  let aS := cutoffPositiveCoefficient model H omega source z hr
  let u := dirichletMinimizer (killedResponseSpace hP) aS b
  let uP : weakSobolevGraph _ :=
    ⟨sobolevDataRestrict hProot u.val, sobolevDataRestrict_mem_weak hProot u.property⟩
  let uQ : weakSobolevGraph _ :=
    ⟨sobolevDataRestrict hQroot u.val, sobolevDataRestrict_mem_weak hQroot u.property⟩
  obtain ⟨U, c, hcont, hae, hholder, hnorm⟩ := hReg zP idx hcenter hcontained
    (fun _ => 0) 0 measurable_const le_rfl (fun _ _ => by simp only [abs_zero, le_refl]) uP
    (SubdiffusiveProcess.FiniteStopping.root_weak_zero model H omega source z hr zP hrP
      hProot hP b)
  have hclass := SubdiffusiveProcess.FiniteStopping.reg_to_boundary_class zQ _ hrQ alpha
    U c hcont hholder
  have hnorm' := SubdiffusiveProcess.FiniteStopping.cellBoundaryQuotientNorm_le zQ _ hrQ
    alpha U c _ hcont hholder hnorm
  simp only [mul_zero, add_zero] at hnorm'
  have haeQ : (fun x => uQ.val.1 x) =ᵐ[
      volume.restrict (centeredCube zQ _ hrQ : Set (SpatialCoordinates d))] U :=
    SubdiffusiveProcess.FiniteStopping.domainLpRestrict_ae_trans hQP hProot u.val.1 U hae
  have ht := hTrace hPQ uQ U hcont hclass haeQ
  have hresult := SubdiffusiveProcess.FiniteStopping.conjunct2_core _ _ _ Cfin eta
    (cellBoundaryQuotientNorm alpha zQ _ U) _ _ _ (d : ℝ) hrQ
    (SubdiffusiveProcess.FiniteStopping.reference_pos model H omega target (H1 * n) zQ)
    (SubdiffusiveProcess.FiniteStopping.reference_pos model H omega source (H1 * n) zQ)
    hCfin heta (SubdiffusiveProcess.FiniteStopping.boundary_norm_nonneg _ _ _ _)
    (sobolevCoefficientForm_nonneg _ uP.val) hnorm' ht
  have henergy : sobolevCoefficientForm
      (cutoffPositiveCoefficient model H omega source zP hrP) uP.val uP.val =
      SubdiffusiveProcess.FiniteStopping.energyOn aS u.val (centeredCube zP _ hrP) := by
    rw [SubdiffusiveProcess.FiniteStopping.sobolevCoefficientForm_eq_energyOn,
      ← SubdiffusiveProcess.FiniteStopping.positiveCoefficientRestrict_cutoff
        model H omega source z hr zP hrP hProot]
    exact SubdiffusiveProcess.FiniteStopping.energyOn_restrict_eq hProot aS u.val
  have hratio : SubdiffusiveProcess.FiniteStopping.reference model H omega target (H1 * n) zQ /
      SubdiffusiveProcess.FiniteStopping.reference model H omega source (H1 * n) zQ =
      SubdiffusiveProcess.FiniteStopping.kappaRatio model H1 target source n :=
    (SubdiffusiveProcess.FiniteStopping.kappaRatio_eq_sRatio model H H1 target source n
      zQ omega).symm
  rw [henergy, hratio] at hresult
  dsimp only
  unfold SubdiffusiveProcess.FiniteStopping.respOn
  rw [SubdiffusiveProcess.FiniteStopping.positiveCoefficientRestrict_cutoff
      model H omega target z hr zQ hrQ hQroot,
    SubdiffusiveProcess.FiniteStopping.positiveCoefficientRestrict_cutoff
      model H omega source z hr zQ hrQ hQroot]
  exact hresult

/-- comparison at stage in the finite stopping construction. -/
theorem comparison_at_stage
    [NeZero d]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (alpha eta Cfin pad : ℝ) (heta : 0 < eta) (hCfin : 0 < Cfin) (hpad : 1 < pad)
    (hpad3 : pad ≤ 3) (H1 N target source : ℕ) (hH1 : 0 < H1)
    (z : SpatialCoordinates d) (j : ℤ) (hr : (0 : ℝ) < (3 : ℝ) ^ j)
    (hj0 : 0 ≤ ((H1 * SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℕ) : ℤ) + j)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr),
      ‖(v : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr)) v‖)
    (b : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr))
    (w0 : Fin (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) → OddGridIndex d 1)
    (s : ℕ) (w : Fin (s + 1) → OddGridIndex d (subdivisionHalfWidth H1))
    (hPad : SubdiffusiveProcess.FiniteStopping.padLabel 2 (w (Fin.last s)))
    (hReg : SubdiffusiveProcess.FiniteStopping.Reg model H alpha H1 pad Cfin hpad source
      (H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + (s + 1)))
      (descendantCenter (subdivisionHalfWidth H1)
        (descendantCenter 1 z ((3 : ℝ) ^ j) (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) w0)
        (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j))
        (s + 1) w) omega)
    (hTrace : SubdiffusiveProcess.FiniteStopping.trace_close model H alpha eta target source
      (H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + (s + 1)))
      (descendantCenter (subdivisionHalfWidth H1)
        (descendantCenter 1 z ((3 : ℝ) ^ j) (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) w0)
        (descendantSide 1 (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j) ((3 : ℝ) ^ j))
        (s + 1) w) omega) :
    let t0 := SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j
    let mg := subdivisionHalfWidth H1
    let aT := cutoffPositiveCoefficient model H omega target z hr
    let aS := cutoffPositiveCoefficient model H omega source z hr
    let u := dirichletMinimizer (killedResponseSpace hP) aS b
    SubdiffusiveProcess.FiniteStopping.respOn aT u
        (SubdiffusiveProcess.FiniteStopping.cell2_le_root z hr t0 mg w0 (s + 1) w)
        (SubdiffusiveProcess.FiniteStopping.cell2_killedPoincare z hr t0 mg w0 (s + 1) w) ≤
      SubdiffusiveProcess.FiniteStopping.kappaRatio model H1 target source
          (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + (s + 1)) *
        SubdiffusiveProcess.FiniteStopping.respOn aS u
          (SubdiffusiveProcess.FiniteStopping.cell2_le_root z hr t0 mg w0 (s + 1) w)
          (SubdiffusiveProcess.FiniteStopping.cell2_killedPoincare z hr t0 mg w0 (s + 1) w) +
      Cfin ^ 2 * eta * SubdiffusiveProcess.FiniteStopping.kappaRatio model H1 target source
          (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + (s + 1)) *
        SubdiffusiveProcess.FiniteStopping.energyOn aS u.val
          (SubdiffusiveProcess.FiniteStopping.cell2 z hr t0 mg w0 s (fun i => w i.castSucc)) := by
  let t0 := SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j
  let mg := subdivisionHalfWidth H1
  let R := descendantSide 1 t0 ((3 : ℝ) ^ j)
  let z0 := descendantCenter 1 z ((3 : ℝ) ^ j) t0 w0
  let zQ := descendantCenter mg z0 R (s + 1) w
  let zP := descendantCenter mg z0 R s (fun i => w i.castSucc)
  let rQ := descendantSide mg (s + 1) R
  let rP := descendantSide mg s R
  have hrQ : 0 < rQ := descendantSide_pos mg (s + 1) (descendantSide_pos 1 t0 hr)
  have hrP : 0 < rP := descendantSide_pos mg s (descendantSide_pos 1 t0 hr)
  have hdepth : rQ = (3 : ℝ) ^
      (-((H1 * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + (s + 1)) : ℕ) : ℤ)) :=
    SubdiffusiveProcess.FiniteStopping.cell2_radius_eq H1 N hH1 j hj0 (s + 1)
  have hsize : rP = (3 : ℝ) ^ H1 * rQ :=
    SubdiffusiveProcess.FiniteStopping.cell2_parent_side_eq H1 R s
  have hcenter : zQ = oddGridCenter zP rP mg (w (Fin.last s)) :=
    SubdiffusiveProcess.FiniteStopping.cell2_succ_eq_oddGridCenter z hr t0 mg w0 s w
  have hcontained : (closedCube zQ (pad * rQ)
      (mul_pos (lt_trans zero_lt_one hpad) hrQ) : Set (SpatialCoordinates d)) ⊆
      centeredCube zP rP hrP := by
    have hc := (SubdiffusiveProcess.FiniteStopping.Reg_premises_at_stage H1 N hH1 z j hj0
      w0 s w pad hpad hpad3 hPad).2
    simpa only [hsize, hdepth] using hc
  have hQroot : centeredCube zQ rQ hrQ ≤ centeredCube z ((3 : ℝ) ^ j) hr := by
    change centeredCube
      (descendantCenter mg (descendantCenter 1 z ((3 : ℝ) ^ j) t0 w0)
        (descendantSide 1 t0 ((3 : ℝ) ^ j)) (s + 1) w)
      (descendantSide mg (s + 1) (descendantSide 1 t0 ((3 : ℝ) ^ j)))
      (descendantSide_pos mg (s + 1)
        (descendantSide_pos 1 t0 (zpow_pos (by norm_num) j))) ≤
        centeredCube z ((3 : ℝ) ^ j) hr
    rw [← SubdiffusiveProcess.FiniteStopping.cell2_eq_centeredCube z hr t0 mg w0
      (s + 1) w]
    exact SubdiffusiveProcess.FiniteStopping.cell2_le_root z hr t0 mg w0 (s + 1) w
  have hProot : centeredCube zP rP hrP ≤ centeredCube z ((3 : ℝ) ^ j) hr := by
    change centeredCube
      (descendantCenter mg (descendantCenter 1 z ((3 : ℝ) ^ j) t0 w0)
        (descendantSide 1 t0 ((3 : ℝ) ^ j)) s (fun i => w i.castSucc))
      (descendantSide mg s (descendantSide 1 t0 ((3 : ℝ) ^ j)))
      (descendantSide_pos mg s
        (descendantSide_pos 1 t0 (zpow_pos (by norm_num) j))) ≤
        centeredCube z ((3 : ℝ) ^ j) hr
    rw [← SubdiffusiveProcess.FiniteStopping.cell2_eq_centeredCube z hr t0 mg w0
      s (fun i => w i.castSucc)]
    exact SubdiffusiveProcess.FiniteStopping.cell2_le_root z hr t0 mg w0 s
      (fun i => w i.castSucc)
  have hQP : centeredCube zQ rQ hrQ ≤ centeredCube zP rP hrP := by
    change centeredCube
      (descendantCenter mg (descendantCenter 1 z ((3 : ℝ) ^ j) t0 w0)
        (descendantSide 1 t0 ((3 : ℝ) ^ j)) (s + 1) w)
      (descendantSide mg (s + 1) (descendantSide 1 t0 ((3 : ℝ) ^ j)))
      (descendantSide_pos mg (s + 1)
        (descendantSide_pos 1 t0 (zpow_pos (by norm_num) j))) ≤
      centeredCube
        (descendantCenter mg (descendantCenter 1 z ((3 : ℝ) ^ j) t0 w0)
          (descendantSide 1 t0 ((3 : ℝ) ^ j)) s (fun i => w i.castSucc))
        (descendantSide mg s (descendantSide 1 t0 ((3 : ℝ) ^ j)))
        (descendantSide_pos mg s
          (descendantSide_pos 1 t0 (zpow_pos (by norm_num) j)))
    rw [← SubdiffusiveProcess.FiniteStopping.cell2_eq_centeredCube z hr t0 mg w0
      (s + 1) w,
      ← SubdiffusiveProcess.FiniteStopping.cell2_eq_centeredCube z hr t0 mg w0
        s (fun i => w i.castSucc)]
    exact SubdiffusiveProcess.FiniteStopping.cell2_succ_le_parent z hr t0 mg w0 s w
  have hCubeQ : SubdiffusiveProcess.FiniteStopping.cell2 z hr t0 mg w0 (s + 1) w =
      centeredCube zQ rQ hrQ := by
    rw [SubdiffusiveProcess.FiniteStopping.cell2_eq_centeredCube]
  have hPQ : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube zQ rQ hrQ),
      ‖(v : SobolevData (centeredCube zQ rQ hrQ)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube zQ rQ hrQ)) v‖ := by
    simpa only [hCubeQ] using!
      SubdiffusiveProcess.FiniteStopping.cell2_killedPoincare z hr t0 mg w0 (s + 1) w
  have hQrootCell :=
    SubdiffusiveProcess.FiniteStopping.cell2_le_root z hr t0 mg w0 (s + 1) w
  have hProotCell := SubdiffusiveProcess.FiniteStopping.cell2_le_root z hr t0 mg w0 s
    (fun i => w i.castSucc)
  have hQPCell := SubdiffusiveProcess.FiniteStopping.cell2_succ_le_parent z hr t0 mg w0 s w
  have hPQCell :=
    SubdiffusiveProcess.FiniteStopping.cell2_killedPoincare z hr t0 mg w0 (s + 1) w
  have hCubeP : SubdiffusiveProcess.FiniteStopping.cell2 z hr t0 mg w0 s
      (fun i => w i.castSucc) = centeredCube zP rP hrP := by
    rw [SubdiffusiveProcess.FiniteStopping.cell2_eq_centeredCube]
  set aT := cutoffPositiveCoefficient model H omega target z hr with haT
  clear_value aT
  set aS := cutoffPositiveCoefficient model H omega source z hr with haS
  clear_value aS
  set u := dirichletMinimizer (killedResponseSpace hP) aS b with hu
  clear_value u
  have hCmp := SubdiffusiveProcess.FiniteStopping.comparison_of_reg_trace model H omega
    alpha eta Cfin pad heta hCfin hpad H1
    (SubdiffusiveProcess.FiniteStopping.obsLo H1 N + (s + 1)) target source z hr hP b
    zQ zP rQ rP hrQ hrP hdepth hsize hQroot hProot hQP
    (w (Fin.last s)) hcenter hcontained hReg hTrace hPQ
  have hrespT := SubdiffusiveProcess.FiniteStopping.respOn_eq_of_domain_eq aT u
    hCubeQ.symm hQroot hQrootCell hPQ hPQCell
  have hrespS := SubdiffusiveProcess.FiniteStopping.respOn_eq_of_domain_eq aS u
    hCubeQ.symm hQroot hQrootCell hPQ hPQCell
  have henergy := SubdiffusiveProcess.FiniteStopping.energyOn_eq_of_domain_eq aS u.val
    hCubeP.symm
  dsimp only at hCmp
  rw [← haT, ← haS, ← hu] at hCmp
  rw [hrespT, hrespS, henergy] at hCmp
  dsimp only
  rw [← hu]
  exact hCmp

end SubdiffusiveProcess.FiniteStopping
