module

public import SubdiffusiveProcess.Paper.rem_bank
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_lfsgs_trace_moments_fifth_le
    {a1 a2 a3 a4 a5 a6 B : ℝ≥0∞}
    (h : a1 + a2 + a3 + a4 + a5 + a6 ≤ B) : a5 ≤ B := by
  refine le_trans ?_ h
  calc
    a5 = 0 + 0 + 0 + 0 + a5 + 0 := by ring
    _ ≤ a1 + a2 + a3 + a4 + a5 + a6 := by gcongr <;> exact zero_le

/-- A finite family of literal unit-cell Dirichlet responses has a common moment
bound, uniformly in the cutoff. The moment order and disorder threshold precede
the model and test family; the norm bound may depend on that fixed model and family. -/
theorem lfsgs_trace_moments
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (W : SmallPerturbationInput d) (Sf : SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d ⟨by omega⟩)
    (p : ℝ) (hp : 2 ≤ p) :
    ∃ q delta0 : ℝ, p < q ∧ 0 < delta0 ∧
    ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (_Rm : in_responses d model) (Sreg : in_6_16 d model) (_It : in_iteration d model Jc Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization model H → model.delta ≤ min 1 delta0 →
    ∀ (T : Type) [Fintype T],
    ∀ hP : ∃ K : ℝ≥0,
      ∀ v : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
        ‖(v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ ≤
          K * ‖subspaceGradient
            (killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) v‖,
    ∀ (testOf : T → SpatialCoordinates d → ℝ), (∀ t, ContDiff ℝ ∞ (testOf t)) →
    ∀ bOf : T → weakSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      (∀ t, ((bOf t).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))] testOf t) →
    ∃ Cmom : ℝ, 0 < Cmom ∧ ∀ t m,
      let R : BilateralField d → ℝ := fun omega =>
        dirichletResponse (killedResponseSpace hP)
          (cutoffPositiveCoefficient model H omega m (0 : SpatialCoordinates d) one_pos) (bOf t)
      MemLp R (ENNReal.ofReal q) (chaosSampleLaw model).toMeasure ∧
        eLpNorm R (ENNReal.ofReal q) (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal Cmom := by
  classical
  obtain ⟨aexpOf, qOf, ordersOf, thresholdOf, _, _, _, _, hmain⟩ :=
    rem_bank d hd Jc Pc Xc W Sf D ((d : ℝ) - 1 / 2) (by linarith only [hd, hp]) (by linarith only [hd, hp])
  obtain ⟨hpq, hdeltapos, _, _, _, _, hall⟩ := hmain p hp
  refine ⟨qOf p d ((d : ℝ) - 1 / 2),
    thresholdOf d ((d : ℝ) - 1 / 2) (ordersOf p d ((d : ℝ) - 1 / 2)), hpq, hdeltapos, ?_⟩
  intro model Rm Sreg It H hH hdelta T _ hP testOf hsmooth bOf hb
  obtain ⟨hdir, -, -⟩ := hall model Rm Sreg It H hH hdelta
  have hEach : ∀ t : T, ∃ Bt : ℝ, 0 ≤ Bt ∧ ∀ m,
      let R : BilateralField d → ℝ := fun omega =>
        dirichletResponse (killedResponseSpace hP)
          (cutoffPositiveCoefficient model H omega m (0 : SpatialCoordinates d) one_pos) (bOf t)
      MemLp R (ENNReal.ofReal (qOf p d ((d : ℝ) - 1 / 2))) (chaosSampleLaw model).toMeasure ∧
        eLpNorm R (ENNReal.ofReal (qOf p d ((d : ℝ) - 1 / 2)))
          (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal Bt := by
    intro t
    obtain ⟨KD, KK, Bt, hBt, -, hmem, hnorm⟩ :=
      hdir 0 1 one_pos le_rfl hP (testOf t) (hsmooth t) (bOf t) (hb t)
        (0 : SpatialCoordinates d → ℝ) contDiff_const HasCompactSupport.zero (by simp only [tsupport_zero, empty_subset])
        (domainConstantL2 (Ω := centeredCube (0 : SpatialCoordinates d) 1 one_pos) 0)
        (domainConstantL2_coeFn 0)
    exact ⟨Bt, hBt, fun m => ⟨(hmem m).2.2.2.2.1,
      aux_lfsgs_trace_moments_fifth_le (hnorm m)⟩⟩
  choose Bt hBt hEachBound using hEach
  refine ⟨1 + ∑ t, Bt t, add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun t _ => hBt t)), ?_⟩
  intro t m
  refine ⟨(hEachBound t m).1, (hEachBound t m).2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have ht : Bt t ≤ ∑ t, Bt t :=
    Finset.single_le_sum (fun t _ => hBt t) (Finset.mem_univ t)
  linarith only [ht]

end SubdiffusiveProcess.Paper

