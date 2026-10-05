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
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJDeterministic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
public import SubdiffusiveProcess.Assumptions.Actions
public import SubdiffusiveProcess.Main.LayerScaling
public import Mathlib.Tactic

@[expose] public section

/-! This module establishes trace witness union two for finite stopping; it does not assert the full stopping theorem. -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.FiniteStopping

variable {d : ℕ}

/-- holderRatioSet sub const in the finite stopping construction. -/
theorem holderRatioSet_sub_const {S : Set (SpatialCoordinates d)}
    (beta : ℝ) (f : SpatialCoordinates d → ℝ) (c : ℝ) :
    _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet beta S (fun x => f x - c) = _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet beta S f := by
  ext v
  simp only [_root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet, mem_ofPred_eq]
  constructor <;> rintro ⟨x, hx, y, hy, hxy, hv⟩ <;>
    exact ⟨x, hx, y, hy, hxy, by rw [hv]; ring_nf⟩

/-- isHolderOn sub const in the finite stopping construction. -/
theorem isHolderOn_sub_const {S : Set (SpatialCoordinates d)}
    (beta : ℝ) (f : SpatialCoordinates d → ℝ) (c : ℝ) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S (fun x => f x - c) ↔ _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S f := by
  unfold _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn
  rw [SubdiffusiveProcess.FiniteStopping.holderRatioSet_sub_const]

/-- isHolderOn mono in the finite stopping construction. -/
theorem isHolderOn_mono {S T : Set (SpatialCoordinates d)}
    (hST : T ⊆ S) (beta : ℝ) (f : SpatialCoordinates d → ℝ) (h : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S f) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta T f := by
  refine h.mono ?_
  rintro v ⟨x, hx, y, hy, hxy, hv⟩
  exact ⟨x, hST hx, y, hST hy, hxy, hv⟩

/-- reg to boundary class in the finite stopping construction. -/
theorem reg_to_boundary_class
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (alpha : ℝ)
    (U : SpatialCoordinates d → ℝ) (c : ℝ)
    (hUcont : ContinuousOn U (closedCube z r hr : Set (SpatialCoordinates d)))
    (hHolder : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)) (fun x => U (z + r • x) - c)) :
    IsCellBoundaryClass alpha z r U := by
  have hT : ∀ x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)), z + r • x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) := by
    intro x hx
    have hx' : dist x (0 : SpatialCoordinates d) ≤ 1 / 2 := by
      simpa only [closedCube, Compacts.coe_mk, Metric.mem_closedBall] using hx
    have : dist (z + r • x) z ≤ r / 2 := by
      have heq : z + r • x - z = r • x := by abel
      rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      have hx0 : dist x 0 = ‖x‖ := by rw [dist_eq_norm, sub_zero]
      rw [hx0] at hx'
      calc r * ‖x‖ ≤ r * (1 / 2) := by
            apply mul_le_mul_of_nonneg_left hx' hr.le
        _ = r / 2 := by ring
    simpa only [closedCube, Compacts.coe_mk, Metric.mem_closedBall] using this
  have hbdd : BddAbove {v : ℝ | ∃ x ∈
      (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      v = |U (z + r • x)|} := by
    have hcompact : IsCompact (closedCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)) := (closedCube (0 : SpatialCoordinates d) 1 one_pos).isCompact
    have hcont : ContinuousOn (fun x => |U (z + r • x)|)
        (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
      apply ContinuousOn.abs
      apply hUcont.comp (Continuous.continuousOn (by fun_prop))
      exact hT
    have himg : IsCompact ((fun x => |U (z + r • x)|) ''
        (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) :=
      hcompact.image_of_continuousOn hcont
    have := himg.bddAbove
    refine this.mono ?_
    rintro v ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  refine ⟨?_, ?_⟩
  · unfold rescaledDatum
    have hfr : (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d))) ⊆
        (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
      refine frontier_subset_closure.trans ?_
      exact closure_minimal (centeredCube_subset_closedCube (0 : SpatialCoordinates d) one_pos)
        (closedCube (0 : SpatialCoordinates d) 1 one_pos).isCompact.isClosed
    have h1 := (SubdiffusiveProcess.FiniteStopping.isHolderOn_sub_const alpha
      (fun x => U (z + r • x)) c).mp hHolder
    exact SubdiffusiveProcess.FiniteStopping.isHolderOn_mono hfr alpha _ h1
  · unfold rescaledDatum
    have hfr : (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d))) ⊆
        (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
      refine frontier_subset_closure.trans ?_
      exact closure_minimal (centeredCube_subset_closedCube (0 : SpatialCoordinates d) one_pos)
        (closedCube (0 : SpatialCoordinates d) 1 one_pos).isCompact.isClosed
    exact hbdd.mono (by rintro v ⟨x, hx, hv⟩; exact ⟨x, hfr hx, hv⟩)

/-- sSup nonneg of forall nonneg in the finite stopping construction. -/
theorem sSup_nonneg_of_forall_nonneg
    {s : Set ℝ} (h : ∀ v ∈ s, 0 ≤ v) : 0 ≤ sSup s := by
  by_cases hbdd : BddAbove s
  · rcases Set.eq_empty_or_nonempty s with he | ⟨v0, hv0⟩
    · rw [he, Real.sSup_empty]
    · exact (h v0 hv0).trans (le_csSup hbdd hv0)
  · rw [Real.sSup_of_not_bddAbove hbdd]

/-- sSup abs mono in the finite stopping construction. -/
theorem sSup_abs_mono {S T : Set (SpatialCoordinates d)}
    (hST : T ⊆ S) (f : SpatialCoordinates d → ℝ)
    (hbdd : BddAbove {v : ℝ | ∃ x ∈ S, v = |f x|}) :
    sSup {v : ℝ | ∃ x ∈ T, v = |f x|} ≤ sSup {v : ℝ | ∃ x ∈ S, v = |f x|} := by
  rcases Set.eq_empty_or_nonempty {v : ℝ | ∃ x ∈ T, v = |f x|} with he | hne
  · rw [he, Real.sSup_empty]
    rcases Set.eq_empty_or_nonempty {v : ℝ | ∃ x ∈ S, v = |f x|} with he2 | hne2
    · rw [he2, Real.sSup_empty]
    · obtain ⟨v0, x0, hx0, hv0eq⟩ := hne2
      have h0 : (0 : ℝ) ≤ v0 := by rw [hv0eq]; exact abs_nonneg _
      exact h0.trans (le_csSup hbdd ⟨x0, hx0, hv0eq⟩)
  · exact csSup_le_csSup hbdd hne (by rintro v ⟨x, hx, rfl⟩; exact ⟨x, hST hx, rfl⟩)

/-- holderSeminorm mono in the finite stopping construction. -/
theorem holderSeminorm_mono {S T : Set (SpatialCoordinates d)}
    (hST : T ⊆ S) (beta : ℝ) (f : SpatialCoordinates d → ℝ)
    (hbdd : BddAbove (_root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet beta S f)) :
    _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta T f ≤ _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta S f := by
  unfold _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm
  rcases Set.eq_empty_or_nonempty (_root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet beta T f) with he | hne
  · rw [he, Real.sSup_empty]
    rcases Set.eq_empty_or_nonempty (_root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet beta S f) with he2 | hne2
    · rw [he2, Real.sSup_empty]
    · obtain ⟨v0, hv0⟩ := hne2
      have h0 : (0 : ℝ) ≤ v0 := by
        obtain ⟨x, hx, y, hy, hxy, hveq⟩ := hv0
        rw [hveq]; positivity
      exact h0.trans (le_csSup hbdd hv0)
  · refine csSup_le_csSup hbdd hne ?_
    rintro v ⟨x, hx, y, hy, hxy, hv⟩
    exact ⟨x, hST hx, y, hST hy, hxy, hv⟩

/-- cAlphaNorm mono in the finite stopping construction. -/
theorem cAlphaNorm_mono {S T : Set (SpatialCoordinates d)}
    (hST : T ⊆ S) (beta : ℝ) (f : SpatialCoordinates d → ℝ)
    (hbdd1 : BddAbove {v : ℝ | ∃ x ∈ S, v = |f x|})
    (hbdd2 : BddAbove (_root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet beta S f)) :
    _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta T f ≤ _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta S f := by
  unfold _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm
  exact add_le_add (SubdiffusiveProcess.FiniteStopping.sSup_abs_mono hST f hbdd1)
    (SubdiffusiveProcess.FiniteStopping.holderSeminorm_mono hST beta f hbdd2)

/-- cAlphaNorm nonneg in the finite stopping construction. -/
theorem cAlphaNorm_nonneg (beta : ℝ)
    (S : Set (SpatialCoordinates d)) (f : SpatialCoordinates d → ℝ) :
    0 ≤ _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta S f := by
  unfold _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm
  refine add_nonneg
    (SubdiffusiveProcess.FiniteStopping.sSup_nonneg_of_forall_nonneg
      (by rintro v ⟨x, -, rfl⟩; exact abs_nonneg _))
    (SubdiffusiveProcess.FiniteStopping.sSup_nonneg_of_forall_nonneg ?_)
  rintro v ⟨x, -, y, -, -, rfl⟩
  positivity

/-- rescaled abs bddAbove in the finite stopping construction. -/
theorem rescaled_abs_bddAbove
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (U : SpatialCoordinates d → ℝ) (c : ℝ)
    (hUcont : ContinuousOn U (closedCube z r hr : Set (SpatialCoordinates d))) :
    BddAbove {v : ℝ | ∃ x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)), v = |U (z + r • x) - c|} := by
  have hT : ∀ x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)), z + r • x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) := by
    intro x hx
    have hx' : dist x (0 : SpatialCoordinates d) ≤ 1 / 2 := by
      simpa only [closedCube, Compacts.coe_mk, Metric.mem_closedBall] using hx
    have : dist (z + r • x) z ≤ r / 2 := by
      have heq : z + r • x - z = r • x := by abel
      rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      have hx0 : dist x 0 = ‖x‖ := by rw [dist_eq_norm, sub_zero]
      rw [hx0] at hx'
      calc r * ‖x‖ ≤ r * (1 / 2) := by
            apply mul_le_mul_of_nonneg_left hx' hr.le
        _ = r / 2 := by ring
    simpa only [closedCube, Compacts.coe_mk, Metric.mem_closedBall] using this
  have hcompact : IsCompact (closedCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)) := (closedCube (0 : SpatialCoordinates d) 1 one_pos).isCompact
  have hcont : ContinuousOn (fun x => |U (z + r • x) - c|)
      (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
    apply ContinuousOn.abs
    exact (hUcont.comp (Continuous.continuousOn (by fun_prop)) hT).sub continuousOn_const
  have himg : IsCompact ((fun x => |U (z + r • x) - c|) ''
      (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) :=
    hcompact.image_of_continuousOn hcont
  refine himg.bddAbove.mono ?_
  rintro v ⟨x, hx, rfl⟩
  exact ⟨x, hx, rfl⟩

/-- cellBoundaryQuotientNorm le in the finite stopping construction. -/
theorem cellBoundaryQuotientNorm_le
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (alpha : ℝ)
    (U : SpatialCoordinates d → ℝ) (c bound : ℝ)
    (hUcont : ContinuousOn U (closedCube z r hr : Set (SpatialCoordinates d)))
    (hHolder : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)) (fun x => U (z + r • x) - c))
    (hCbound : _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)) (fun x => U (z + r • x) - c) ≤ bound) :
    cellBoundaryQuotientNorm alpha z r U ≤ bound := by
  have hfr : (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d))) ⊆
      (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
    refine frontier_subset_closure.trans ?_
    exact closure_minimal (centeredCube_subset_closedCube (0 : SpatialCoordinates d) one_pos)
      (closedCube (0 : SpatialCoordinates d) 1 one_pos).isCompact.isClosed
  have hbddbelow : BddBelow {v : ℝ | ∃ c' : ℝ, v = _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
      (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
      (fun x => rescaledDatum z r U x - c')} := by
    refine ⟨0, ?_⟩
    rintro v ⟨c', rfl⟩
    exact SubdiffusiveProcess.FiniteStopping.cAlphaNorm_nonneg alpha _ _
  have hmem : _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
      (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
      (fun x => rescaledDatum z r U x - c) ∈
      {v : ℝ | ∃ c' : ℝ, v = _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
        (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
          Set (SpatialCoordinates d))) (fun x => rescaledDatum z r U x - c')} :=
    ⟨c, rfl⟩
  have hstep1 : cellBoundaryQuotientNorm alpha z r U ≤
      _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
        (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
        (fun x => rescaledDatum z r U x - c) :=
    csInf_le hbddbelow hmem
  have hrsc : (fun x => rescaledDatum z r U x - c) = (fun x => U (z + r • x) - c) := rfl
  rw [hrsc] at hstep1
  refine hstep1.trans (le_trans ?_ hCbound)
  exact SubdiffusiveProcess.FiniteStopping.cAlphaNorm_mono hfr alpha
    (fun x => U (z + r • x) - c)
    (SubdiffusiveProcess.FiniteStopping.rescaled_abs_bddAbove z r hr U c hUcont) hHolder

/-- kappaSeq in the finite stopping construction. -/
def kappaSeq (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (J : ℕ) : ℝ :=
  Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
    SubdiffusiveProcess.CoarseGrainingVocab.ahom model J

/-- reference in the finite stopping construction. -/
def reference
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N k : ℕ) (z : SpatialCoordinates d) : ℝ :=
  (SubdiffusiveProcess.FiniteStopping.kappaSeq model (N - k) /
    SubdiffusiveProcess.FiniteStopping.kappaSeq model N) *
      Real.exp (H omega z + ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z)

/-- reference pos in the finite stopping construction. -/
theorem reference_pos
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N k : ℕ) (z : SpatialCoordinates d) :
    0 < SubdiffusiveProcess.FiniteStopping.reference model H omega N k z := by
  unfold SubdiffusiveProcess.FiniteStopping.reference SubdiffusiveProcess.FiniteStopping.kappaSeq
  exact mul_pos
    (div_pos (mul_pos (Real.exp_pos _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model _))
      (mul_pos (Real.exp_pos _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model _)))
    (Real.exp_pos _)

/-- trace close in the finite stopping construction. -/
def trace_close
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (alpha eta : ℝ) (N M k : ℕ) (z : SpatialCoordinates d) (omega : BilateralField d) : Prop :=
  let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
  let hr : 0 < r := by positivity
  let Q := centeredCube z r hr
  ∀ hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph Q,
      ‖(v : SobolevData Q).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Q) v‖,
    ∀ (u : weakSobolevGraph Q) (G : SpatialCoordinates d → ℝ),
      ContinuousOn G (closedCube z r hr) → IsCellBoundaryClass alpha z r G →
      ((fun x => (u : SobolevData Q).1 x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] G) →
      |dirichletResponse (killedResponseSpace hP)
          (cutoffPositiveCoefficient model H omega N z hr) u /
          (r ^ ((d : ℝ) - 2) *
            SubdiffusiveProcess.FiniteStopping.reference model H omega N k z) -
        dirichletResponse (killedResponseSpace hP)
          (cutoffPositiveCoefficient model H omega M z hr) u /
          (r ^ ((d : ℝ) - 2) *
            SubdiffusiveProcess.FiniteStopping.reference model H omega M k z)| ≤
        eta * (cellBoundaryQuotientNorm alpha z r G) ^ 2

/-- trace close symm in the finite stopping construction. -/
theorem trace_close_symm
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (alpha eta : ℝ) (N M k : ℕ) (z : SpatialCoordinates d) (omega : BilateralField d)
    (h : SubdiffusiveProcess.FiniteStopping.trace_close model H alpha eta N M k z omega) :
    SubdiffusiveProcess.FiniteStopping.trace_close model H alpha eta M N k z omega := by
  intro hP u G hcont hclass hae
  have hc := h hP u G hcont hclass hae
  simpa only [zpow_neg, zpow_natCast, abs_sub_comm, ge_iff_le] using hc

/-- kappaRatio in the finite stopping construction. -/
def kappaRatio (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H1 target source n : ℕ) : ℝ :=
  (SubdiffusiveProcess.FiniteStopping.kappaSeq model (target - H1 * n) /
      SubdiffusiveProcess.FiniteStopping.kappaSeq model target) /
    (SubdiffusiveProcess.FiniteStopping.kappaSeq model (source - H1 * n) /
      SubdiffusiveProcess.FiniteStopping.kappaSeq model source)

/-- kappaRatio eq sRatio in the finite stopping construction. -/
theorem kappaRatio_eq_sRatio
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (H1 target source n : ℕ) (z : SpatialCoordinates d) (omega : BilateralField d) :
    SubdiffusiveProcess.FiniteStopping.kappaRatio model H1 target source n =
      ((SubdiffusiveProcess.FiniteStopping.kappaSeq model (target - H1 * n) /
          SubdiffusiveProcess.FiniteStopping.kappaSeq model target) *
        Real.exp ((H omega) z + ∑ j ∈ Finset.range (H1 * n), omega (-(j : ℤ)) z)) /
      ((SubdiffusiveProcess.FiniteStopping.kappaSeq model (source - H1 * n) /
          SubdiffusiveProcess.FiniteStopping.kappaSeq model source) *
        Real.exp ((H omega) z + ∑ j ∈ Finset.range (H1 * n), omega (-(j : ℤ)) z)) := by
  unfold SubdiffusiveProcess.FiniteStopping.kappaRatio
  have he : Real.exp ((H omega) z + ∑ j ∈ Finset.range (H1 * n), omega (-(j : ℤ)) z) ≠ 0 :=
    (Real.exp_pos _).ne'
  rw [mul_div_mul_right _ _ he]

/-- conjunct2 core in the finite stopping construction. -/
theorem conjunct2_core
    (r sT sS Cfin eta Q Eparent X Y dreal : ℝ)
    (hr : 0 < r) (hsT : 0 < sT) (hsS : 0 < sS) (_hCfin : 0 < Cfin) (heta : 0 < eta)
    (hQ0 : 0 ≤ Q) (hE0 : 0 ≤ Eparent)
    (hQ : Q ≤ Cfin * r ^ (((2 : ℝ) - dreal) / 2) * sS ^ (-(1 : ℝ) / 2) * Real.sqrt Eparent)
    (hTrace : |X / (r ^ (dreal - 2) * sT) - Y / (r ^ (dreal - 2) * sS)| ≤ eta * Q ^ 2) :
    X ≤ (sT / sS) * Y + Cfin ^ 2 * eta * (sT / sS) * Eparent := by
  set rp := r ^ (dreal - 2) with hrp_def
  have hrp : 0 < rp := Real.rpow_pos_of_pos hr _
  have hstep : X / (rp * sT) ≤ Y / (rp * sS) + eta * Q ^ 2 := by
    have h2 := (abs_le.mp hTrace).2
    linarith only [hr, hsT, hsS, _hCfin, heta, hQ0, hE0, hQ, hTrace, hrp_def, hrp, h2]
  have heqX : rp * sT * (X / (rp * sT)) = X := by
    field_simp
  have heqY : rp * sT * (Y / (rp * sS)) = (sT / sS) * Y := by
    field_simp
  have hmul : rp * sT * (X / (rp * sT)) ≤ rp * sT * (Y / (rp * sS) + eta * Q ^ 2) :=
    mul_le_mul_of_nonneg_left hstep (mul_pos hrp hsT).le
  rw [heqX, mul_add, heqY] at hmul
  have hQsq : Q ^ 2 ≤ Cfin ^ 2 * r ^ (2 - dreal) * sS⁻¹ * Eparent := by
    have hsq := pow_le_pow_left₀ hQ0 hQ 2
    have hexpand : (Cfin * r ^ (((2 : ℝ) - dreal) / 2) * sS ^ (-(1 : ℝ) / 2) *
        Real.sqrt Eparent) ^ 2 =
        Cfin ^ 2 * (r ^ (((2 : ℝ) - dreal) / 2)) ^ 2 * (sS ^ (-(1 : ℝ) / 2)) ^ 2 *
          (Real.sqrt Eparent) ^ 2 := by ring
    rw [hexpand] at hsq
    have hr2 : (r ^ (((2 : ℝ) - dreal) / 2)) ^ 2 = r ^ (2 - dreal) := by
      rw [← Real.rpow_natCast (r ^ (((2 : ℝ) - dreal) / 2)) 2, ← Real.rpow_mul hr.le]
      norm_num
    have hs2 : (sS ^ (-(1 : ℝ) / 2)) ^ 2 = sS⁻¹ := by
      rw [← Real.rpow_natCast (sS ^ (-(1 : ℝ) / 2)) 2, ← Real.rpow_mul hsS.le]
      norm_num
      rw [Real.rpow_neg hsS.le, Real.rpow_one]
    have he2 : (Real.sqrt Eparent) ^ 2 = Eparent := Real.sq_sqrt hE0
    rw [hr2, hs2, he2] at hsq
    exact hsq
  have hrr : rp * r ^ (2 - dreal) = 1 := by
    rw [hrp_def, ← Real.rpow_add hr]
    norm_num
  have herr : rp * sT * (eta * Q ^ 2) ≤ Cfin ^ 2 * eta * (sT / sS) * Eparent := by
    have hstep2 : rp * sT * (eta * Q ^ 2) ≤
        rp * sT * (eta * (Cfin ^ 2 * r ^ (2 - dreal) * sS⁻¹ * Eparent)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQsq heta.le) (mul_pos hrp hsT).le
    have heq : rp * sT * (eta * (Cfin ^ 2 * r ^ (2 - dreal) * sS⁻¹ * Eparent)) =
        Cfin ^ 2 * eta * (sT / sS) * Eparent * (rp * r ^ (2 - dreal)) := by
      rw [div_eq_mul_inv]; ring
    rw [heq, hrr, mul_one] at hstep2
    exact hstep2
  linarith only [hr, hsT, hsS, _hCfin, heta, hQ0, hE0, hQ, hTrace, hrp_def, hrp, hstep, heqX, heqY, hmul, hQsq, hrr, herr, hmul, herr]

/-- responses two sided eta4 in the finite stopping construction. -/
theorem responses_two_sided_eta4 {x y z eta : ℝ}
    (hx : |x - z| ≤ eta / 4) (hy : |y - z| ≤ eta / 4) :
    |x - y| ≤ eta / 2 := by
  calc
    |x - y| = |(x - z) + (z - y)| := by congr 1; ring
    _ ≤ |x - z| + |z - y| := abs_add_le _ _
    _ ≤ eta / 4 + eta / 4 := add_le_add hx (by rw [abs_sub_comm]; exact hy)
    _ = eta / 2 := by ring

/-- seminorm of sqrt in the finite stopping construction. -/
theorem seminorm_of_sqrt {V : Type*} [AddCommGroup V]
    [Module ℝ V] (Λ : V → ℝ) (_h0 : ∀ v, 0 ≤ Λ v) (hsmul : ∀ (c : ℝ) (v : V), Λ (c • v) = c ^ 2 * Λ v)
    (htri : ∀ v w : V, Real.sqrt (Λ (v + w)) ≤ Real.sqrt (Λ v) + Real.sqrt (Λ w)) :
    ∃ p : Seminorm ℝ V, ∀ v, p v = Real.sqrt (Λ v) := by
  refine ⟨Seminorm.of (fun v => Real.sqrt (Λ v)) htri (fun a x => ?_), fun _ => rfl⟩
  calc
    Real.sqrt (Λ (a • x)) = Real.sqrt (a ^ 2 * Λ x) := by rw [hsmul a x]
    _ = Real.sqrt (a ^ 2) * Real.sqrt (Λ x) := by rw [Real.sqrt_mul (sq_nonneg a) (Λ x)]
    _ = |a| * Real.sqrt (Λ x) := by rw [Real.sqrt_sq_eq_abs]
    _ = ‖a‖ * Real.sqrt (Λ x) := by rw [Real.norm_eq_abs]

/-- seminorm extend in the finite stopping construction. -/
theorem seminorm_extend {E : Type*} [AddCommGroup E]
    [Module ℝ E] (V : Submodule ℝ E) (p : Seminorm ℝ V) :
    ∃ q : Seminorm ℝ E, ∀ v : V, q (v : E) = p v := by
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl V
  let π := Submodule.projectionOnto V W hW
  refine ⟨p.comp π, fun v => ?_⟩
  dsimp
  change p ((V.projectionOnto W hW) (v : E)) = p v
  simpa only using! congrArg p (Submodule.projectionOnto_apply_left hW v)

/-- trace witness union two in the finite stopping construction. -/
theorem trace_witness_union_two
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (Pmeas : Measure (BilateralField d)) (k : ℤ) (Bc : ℝ) (_hBc : 0 < Bc)
    (W1 W2 : ℕ+ → Set (BilateralField d))
    (hmeas1 : ∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
        ((Set.Icc (-k - 2 * (h : ℤ)) (-k + (h : ℤ))).domRestrict)
        (inferInstance : MeasurableSpace
          ((i : Set.Icc (-k - 2 * (h : ℤ)) (-k + (h : ℤ))) → C(SpatialCoordinates d, ℝ)))]
        (W1 h))
    (hmeas2 : ∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
        ((Set.Icc (-k - 2 * (h : ℤ)) (-k + (h : ℤ))).domRestrict)
        (inferInstance : MeasurableSpace
          ((i : Set.Icc (-k - 2 * (h : ℤ)) (-k + (h : ℤ))) → C(SpatialCoordinates d, ℝ)))]
        (W2 h))
    (hP1 : ∀ h : ℕ+, Pmeas (W1 h) ≤ ENNReal.ofReal (Real.exp (-(Bc + Real.log 2) * (h : ℝ))))
    (hP2 : ∀ h : ℕ+, Pmeas (W2 h) ≤ ENNReal.ofReal (Real.exp (-(Bc + Real.log 2) * (h : ℝ)))) :
    ∃ W : ℕ+ → Set (BilateralField d),
      (∀ h : ℕ+, MeasurableSet[MeasurableSpace.comap
          ((Set.Icc (-k - 2 * (h : ℤ)) (-k + (h : ℤ))).domRestrict)
          (inferInstance : MeasurableSpace
            ((i : Set.Icc (-k - 2 * (h : ℤ)) (-k + (h : ℤ))) → C(SpatialCoordinates d, ℝ)))]
          (W h)) ∧
      (∀ h : ℕ+, Pmeas (W h) ≤ ENNReal.ofReal (Real.exp (-Bc * (h : ℝ)))) ∧
      ((⋃ h : ℕ+, W h) = (⋃ h : ℕ+, W1 h) ∪ (⋃ h : ℕ+, W2 h)) := by
  refine ⟨fun h => W1 h ∪ W2 h, fun h => (hmeas1 h).union (hmeas2 h), ?_, ?_⟩
  · intro h
    have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast h.property
    have hb2 : Real.exp (-(Real.log 2) * (h : ℝ)) ≤ (1 / 2 : ℝ) := by
      have hlog2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hstep : Real.log 2 ≤ Real.log 2 * (h : ℝ) := by nlinarith only [_hBc, hmeas1, hmeas2, hP1, hP2, hh1, hlog2]
      calc Real.exp (-(Real.log 2) * (h : ℝ)) = Real.exp (-(Real.log 2 * (h : ℝ))) := by ring_nf
        _ ≤ Real.exp (-(Real.log 2)) := Real.exp_le_exp.mpr (by linarith only [_hBc, hmeas1, hmeas2, hP1, hP2, hh1, hlog2, hstep])
        _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    have key : 2 * Real.exp (-(Bc + Real.log 2) * (h : ℝ)) ≤ Real.exp (-Bc * (h : ℝ)) := by
      have expand : Real.exp (-(Bc + Real.log 2) * (h : ℝ)) =
          Real.exp (-Bc * (h : ℝ)) * Real.exp (-(Real.log 2) * (h : ℝ)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [expand]
      calc 2 * (Real.exp (-Bc * (h : ℝ)) * Real.exp (-(Real.log 2) * (h : ℝ)))
          ≤ 2 * (Real.exp (-Bc * (h : ℝ)) * (1 / 2)) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact mul_le_mul_of_nonneg_left hb2 (Real.exp_pos _).le
        _ = Real.exp (-Bc * (h : ℝ)) := by ring
    calc Pmeas (W1 h ∪ W2 h) ≤ Pmeas (W1 h) + Pmeas (W2 h) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (Real.exp (-(Bc + Real.log 2) * (h : ℝ))) +
            ENNReal.ofReal (Real.exp (-(Bc + Real.log 2) * (h : ℝ))) := add_le_add (hP1 h) (hP2 h)
      _ = ENNReal.ofReal (2 * Real.exp (-(Bc + Real.log 2) * (h : ℝ))) := by
            rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]; congr 1; ring
      _ ≤ ENNReal.ofReal (Real.exp (-Bc * (h : ℝ))) := ENNReal.ofReal_le_ofReal key
  · ext x
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨h, hh1 | hh2⟩
      · exact Or.inl ⟨h, hh1⟩
      · exact Or.inr ⟨h, hh2⟩
    · rintro (⟨h, hh1⟩ | ⟨h, hh2⟩)
      · exact ⟨h, Or.inl hh1⟩
      · exact ⟨h, Or.inr hh2⟩

end SubdiffusiveProcess.FiniteStopping
