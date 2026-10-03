module

public import SubdiffusiveProcess.Main.CutoffCoefficient
public import Homogenization.Sobolev.H1.BasicLemmas
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Lane4.CubeDilation
public import SubdiffusiveProcess.Lane4.Inputs
public import SubdiffusiveProcess.Lane2.BoundaryResponse
public import SubdiffusiveProcess.Lane2.ExternalInputs
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import Mathlib.Analysis.Seminorm
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Tactic
public import Mathlib
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.Lane4.Bridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ScalarFieldPackaging
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerReduction
public import SubdiffusiveProcess.Probability.ConditionalPullback
public import SubdiffusiveProcess.Sobolev.AffineData
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Lane3.Interfaces
public import SubdiffusiveProcess.Lnorm.BoundaryResponseFamily

@[expose] public section

/-! This module establishes LayerRegroup for the cutoff-response compactness construction;
it does not identify subsequential limits or assert local-normalization convergence. -/

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Metric
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff
noncomputable section

namespace SubdiffusiveProcess.Lnorm

section
variable (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]

/-- htilde partialSumOfSeq eq infraredPartialSum for the cutoff-response compactness construction. -/
theorem htilde_partialSumOfSeq_eq_infraredPartialSum
    (omega : BilateralField d) (L : ℕ) :
    SubdiffusiveProcess.Lnorm.htilde_partialSumOfSeq d (fun n => omega (n + 1)) L =
      infraredPartialSum omega L :=
  rfl

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] in

end

section
variable (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]

/-- htilde partialSumOfSeq continuous for the cutoff-response compactness construction. -/
theorem htilde_partialSumOfSeq_continuous (L : ℕ) :
    Continuous (fun ctail : ℕ → C(SpatialCoordinates d, ℝ) =>
      SubdiffusiveProcess.Lnorm.htilde_partialSumOfSeq d ctail L) := by
  unfold SubdiffusiveProcess.Lnorm.htilde_partialSumOfSeq
  refine continuous_finset_sum _ (fun n _ => Continuous.sub ?_ ?_)
  · exact continuous_apply n
  · exact ContinuousMap.continuous_const'.comp
      ((continuous_eval_const (0 : SpatialCoordinates d)).comp (continuous_apply n))

end

section
variable (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]

/-- htilde for the cutoff-response compactness construction. -/
noncomputable def htilde (ctail : ℕ → C(SpatialCoordinates d, ℝ)) :
    C(SpatialCoordinates d, ℝ) :=
  limUnder Filter.atTop (SubdiffusiveProcess.Lnorm.htilde_partialSumOfSeq d ctail)

end

section
variable (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]

/-- htilde measurable for the cutoff-response compactness construction. -/
theorem htilde_measurable [BorelSpace C(SpatialCoordinates d, ℝ)] :
    Measurable (SubdiffusiveProcess.Lnorm.htilde d) := by
  have hSM : ∀ L : ℕ, StronglyMeasurable
      (fun ctail : ℕ → C(SpatialCoordinates d, ℝ) => SubdiffusiveProcess.Lnorm.htilde_partialSumOfSeq d ctail L) :=
    fun L => (SubdiffusiveProcess.Lnorm.htilde_partialSumOfSeq_continuous d L).stronglyMeasurable
  unfold SubdiffusiveProcess.Lnorm.htilde
  exact (MeasureTheory.StronglyMeasurable.limUnder (l := Filter.atTop) hSM).measurable

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] in

end

section
variable (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]

/-- htilde eq of tendsto for the cutoff-response compactness construction. -/
theorem htilde_eq_of_tendsto {ctail : ℕ → C(SpatialCoordinates d, ℝ)}
    {c : C(SpatialCoordinates d, ℝ)}
    (h : Filter.Tendsto (SubdiffusiveProcess.Lnorm.htilde_partialSumOfSeq d ctail) Filter.atTop (nhds c)) :
    SubdiffusiveProcess.Lnorm.htilde d ctail = c := by
  unfold SubdiffusiveProcess.Lnorm.htilde
  exact h.limUnder_eq

end

section
variable (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]

/-- htilde eq H ae for the cutoff-response compactness construction. -/
theorem htilde_eq_H_ae [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d}
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)}
    (hH : InfraredCharacterization M H) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, SubdiffusiveProcess.Lnorm.htilde d (fun n => omega (n + 1)) = H omega := by
  filter_upwards [hH.2] with omega hten
  apply SubdiffusiveProcess.Lnorm.htilde_eq_of_tendsto
  have heq : SubdiffusiveProcess.Lnorm.htilde_partialSumOfSeq d (fun n => omega (n + 1)) =
      infraredPartialSum omega :=
    funext (SubdiffusiveProcess.Lnorm.htilde_partialSumOfSeq_eq_infraredPartialSum d omega)
  rw [heq]
  exact hten

end

section


/-- regroup apply zero for the cutoff-response compactness construction. -/
theorem regroup_apply_zero (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (omega : BilateralField d) :
    SubdiffusiveProcess.Lnorm.regroup omega 0 = (omega 0, fun n : ℕ => omega ((n : ℤ) + 1)) := by
  rfl

end

section


/-- regroup bridgeC apply for the cutoff-response compactness construction. -/
theorem regroup_bridgeC_apply (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (omega : BilateralField d) :
    SubdiffusiveProcess.Lnorm.regroup_bridge (SubdiffusiveProcess.Lnorm.regroup_ΦC omega) =
      ((fun n : ℕ => omega (Int.negSucc n), fun _ : ℕ => PUnit.unit),
        (omega 0, fun n : ℕ => omega ((n : ℤ) + 1))) := by
  rfl

end

section


/-- regroup apply succ for the cutoff-response compactness construction. -/
theorem regroup_apply_succ (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (omega : BilateralField d) (n : ℕ) :
    SubdiffusiveProcess.Lnorm.regroup omega ((n : ℤ) + 1) = omega (Int.negSucc n) := by
  show SubdiffusiveProcess.Lnorm.regroup_ΦY.symm (SubdiffusiveProcess.Lnorm.regroup_bridge (SubdiffusiveProcess.Lnorm.regroup_ΦC omega))
      ((n : ℤ) + 1) = omega (Int.negSucc n)
  rw [SubdiffusiveProcess.Lnorm.regroup_bridgeC_apply]
  show (threeBlockEquiv SubdiffusiveProcess.Lnorm.regroup_p SubdiffusiveProcess.Lnorm.regroup_q).symm
      (((MeasurableEquiv.piCongrLeft (fun i : {i : {j : ℤ // SubdiffusiveProcess.Lnorm.regroup_p j} //
              SubdiffusiveProcess.Lnorm.regroup_q i.1} => SubdiffusiveProcess.Lnorm.regroup_Y d i.1.1) SubdiffusiveProcess.Lnorm.regroup_ePos).prodCongr
          (MeasurableEquiv.piCongrLeft (fun i : {i : {j : ℤ // SubdiffusiveProcess.Lnorm.regroup_p j} //
              ¬ SubdiffusiveProcess.Lnorm.regroup_q i.1} => SubdiffusiveProcess.Lnorm.regroup_Y d i.1.1) SubdiffusiveProcess.Lnorm.regroup_eNeg)).prodCongr
        (MeasurableEquiv.piUnique
          (fun i : {i : ℤ // ¬ SubdiffusiveProcess.Lnorm.regroup_p i} => SubdiffusiveProcess.Lnorm.regroup_Y d i)).symm
        ((fun k : ℕ => omega (Int.negSucc k), fun _ : ℕ => (PUnit.unit : PUnit)),
          (omega 0, fun k : ℕ => omega ((k : ℤ) + 1))))
      ((n : ℤ) + 1) = omega (Int.negSucc n)
  show (MeasurableEquiv.piEquivPiSubtypeProd (fun j : ℤ => SubdiffusiveProcess.Lnorm.regroup_Y d j)
        SubdiffusiveProcess.Lnorm.regroup_p).symm
      (((MeasurableEquiv.piEquivPiSubtypeProd
            (fun i : {j : ℤ // SubdiffusiveProcess.Lnorm.regroup_p j} => SubdiffusiveProcess.Lnorm.regroup_Y d i.1)
            (fun i : {j : ℤ // SubdiffusiveProcess.Lnorm.regroup_p j} => SubdiffusiveProcess.Lnorm.regroup_q i.1)).prodCongr
          (MeasurableEquiv.refl _)).symm
        (((MeasurableEquiv.piCongrLeft (fun i : {i : {j : ℤ // SubdiffusiveProcess.Lnorm.regroup_p j} //
                SubdiffusiveProcess.Lnorm.regroup_q i.1} => SubdiffusiveProcess.Lnorm.regroup_Y d i.1.1) SubdiffusiveProcess.Lnorm.regroup_ePos)
              (fun k : ℕ => omega (Int.negSucc k)),
            (MeasurableEquiv.piCongrLeft (fun i : {i : {j : ℤ // SubdiffusiveProcess.Lnorm.regroup_p j} //
                ¬ SubdiffusiveProcess.Lnorm.regroup_q i.1} => SubdiffusiveProcess.Lnorm.regroup_Y d i.1.1) SubdiffusiveProcess.Lnorm.regroup_eNeg)
              (fun _ : ℕ => (PUnit.unit : PUnit))),
          (MeasurableEquiv.piUnique
            (fun i : {i : ℤ // ¬ SubdiffusiveProcess.Lnorm.regroup_p i} => SubdiffusiveProcess.Lnorm.regroup_Y d i)).symm
            (omega 0, fun k : ℕ => omega ((k : ℤ) + 1))))
      ((n : ℤ) + 1) = omega (Int.negSucc n)
  have hp' : SubdiffusiveProcess.Lnorm.regroup_p ((n : ℤ) + 1) := by
    show ((n : ℤ) + 1) ≠ 0
    omega
  have hq' : SubdiffusiveProcess.Lnorm.regroup_q (⟨(n : ℤ) + 1, hp'⟩ : {j : ℤ // SubdiffusiveProcess.Lnorm.regroup_p j}).1 := by
    show (0 : ℤ) < (n : ℤ) + 1
    omega
  simp only [MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
  rw [dif_pos hp']
  show (MeasurableEquiv.piEquivPiSubtypeProd
      (fun i : {j : ℤ // SubdiffusiveProcess.Lnorm.regroup_p j} => SubdiffusiveProcess.Lnorm.regroup_Y d i.1)
      (fun i : {j : ℤ // SubdiffusiveProcess.Lnorm.regroup_p j} => SubdiffusiveProcess.Lnorm.regroup_q i.1)).symm
    ((MeasurableEquiv.piCongrLeft (fun i : {i : {j : ℤ // SubdiffusiveProcess.Lnorm.regroup_p j} //
          SubdiffusiveProcess.Lnorm.regroup_q i.1} => SubdiffusiveProcess.Lnorm.regroup_Y d i.1.1) SubdiffusiveProcess.Lnorm.regroup_ePos)
        (fun k : ℕ => omega (Int.negSucc k)),
      (MeasurableEquiv.piCongrLeft (fun i : {i : {j : ℤ // SubdiffusiveProcess.Lnorm.regroup_p j} //
          ¬ SubdiffusiveProcess.Lnorm.regroup_q i.1} => SubdiffusiveProcess.Lnorm.regroup_Y d i.1.1) SubdiffusiveProcess.Lnorm.regroup_eNeg)
        (fun _ : ℕ => (PUnit.unit : PUnit)))
    ⟨(n : ℤ) + 1, hp'⟩ = omega (Int.negSucc n)
  simp only [MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
  rw [dif_pos hq']
  exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun i : {i : {j : ℤ // SubdiffusiveProcess.Lnorm.regroup_p j} //
        SubdiffusiveProcess.Lnorm.regroup_q i.1} => SubdiffusiveProcess.Lnorm.regroup_Y d i.1.1) SubdiffusiveProcess.Lnorm.regroup_ePos
    (fun k : ℕ => omega (Int.negSucc k)) n

end

section


/-- ennreal le of add six for the cutoff-response compactness construction. -/
theorem ennreal_le_of_add_six {a1 a2 a3 a4 a5 a6 B : ℝ≥0∞}
    (h : a1 + a2 + a3 + a4 + a5 + a6 ≤ B) :
    a3 ≤ B ∧ a5 ≤ B := by
  have e3 : a3 ≤ a1 + a2 + a3 + a4 + a5 + a6 := by
    calc a3 = 0 + 0 + a3 + 0 + 0 + 0 := by ring
      _ ≤ a1 + a2 + a3 + a4 + a5 + a6 := by gcongr <;> exact zero_le
  have e5 : a5 ≤ a1 + a2 + a3 + a4 + a5 + a6 := by
    calc a5 = 0 + 0 + 0 + 0 + a5 + 0 := by ring
      _ ≤ a1 + a2 + a3 + a4 + a5 + a6 := by gcongr <;> exact zero_le
  exact ⟨e3.trans h, e5.trans h⟩

end

end SubdiffusiveProcess.Lnorm
