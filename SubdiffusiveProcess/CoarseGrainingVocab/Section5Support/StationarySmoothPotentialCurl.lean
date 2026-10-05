module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationaryMollifiedHodge

@[expose] public section

/-!
# Curl rigidity for smooth stationary potential fields

This is the topology-free closed-potential curl argument needed on the
literal GMC sample carrier.  For a smooth curl component `C`, the vector

`(D_j C) e_i - (D_i C) e_j`

is solenoidal: its pairing with every strong gradient vanishes by stationary
integration by parts and equality of the mixed derivatives, hence the same
is true against the closure of those gradients.  Pairing this test field
with the potential field itself gives exactly `inner C C`.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- A smooth stationary potential field has zero curl.  The hypotheses expose
only the strong first- and second-gradient data needed by the energy proof. -/
theorem curlComponent_eq_zero_of_smooth_mem_stationaryPotentialSubspace
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Q : Stationary.VectorL2 d M.P.toMeasure)
    (hQpot : letI := potentialSequenceVAddInvariant M
      Q ∈ Stationary.stationaryPotentialSubspace
        (mu := M.P.toMeasure) (d := d))
    (HQ : Fin d → Stationary.VectorL2 d M.P.toMeasure)
    (hQcoord : letI := potentialSequenceVAddInvariant M
      ∀ k : Fin d,
        Stationary.HasHorizontalGradient (mu := M.P.toMeasure)
          (Stationary.vectorL2Coord (mu := M.P.toMeasure) k Q) (HQ k))
    (i j : Fin d)
    (C : Stationary.ScalarL2 M.P.toMeasure)
    (hCdef : C =
      Stationary.vectorL2Coord (mu := M.P.toMeasure) i (HQ j) -
        Stationary.vectorL2Coord (mu := M.P.toMeasure) j (HQ i))
    (GC : Stationary.VectorL2 d M.P.toMeasure)
    (hC : letI := potentialSequenceVAddInvariant M
      Stationary.HasHorizontalGradient (mu := M.P.toMeasure) C GC)
    (HGC : Fin d → Stationary.VectorL2 d M.P.toMeasure)
    (hGCcoord : letI := potentialSequenceVAddInvariant M
      ∀ k : Fin d,
        Stationary.HasHorizontalGradient (mu := M.P.toMeasure)
          (Stationary.vectorL2Coord (mu := M.P.toMeasure) k GC) (HGC k))
    (hmixed : Stationary.vectorL2Coord (mu := M.P.toMeasure) i (HGC j) =
      Stationary.vectorL2Coord (mu := M.P.toMeasure) j (HGC i)) :
    C = 0 := by
  let := potentialSequenceVAddInvariant M
  let DiC := Stationary.vectorL2Coord (mu := M.P.toMeasure) i GC
  let DjC := Stationary.vectorL2Coord (mu := M.P.toMeasure) j GC
  let V : Stationary.VectorL2 d M.P.toMeasure :=
    scalarToVectorL2 M.P.toMeasure (Pi.single i 1) DjC -
      scalarToVectorL2 M.P.toMeasure (Pi.single j 1) DiC
  let S := Stationary.horizontalGradientRange
    (mu := M.P.toMeasure) (d := d)
  let T : Stationary.VectorL2 d M.P.toMeasure →L[ℝ] ℝ :=
    innerSL ℝ V
  have hstrong : S ≤ LinearMap.ker T.toLinearMap := by
    rintro F ⟨phi, hphi⟩
    rw [LinearMap.mem_ker]
    dsimp only [T]
    change inner ℝ V F = 0
    dsimp only [V]
    rw [inner_sub_left, inner_scalarToVectorL2_basis,
      inner_scalarToVectorL2_basis]
    have hj := hphi.inner_coord_eq_neg_inner_coord (hGCcoord j) i
    have hi := hphi.inner_coord_eq_neg_inner_coord (hGCcoord i) j
    have hj' : inner ℝ DjC
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) i F) =
        -inner ℝ phi
          (Stationary.vectorL2Coord (mu := M.P.toMeasure) i (HGC j)) := by
      simpa only [DjC, real_inner_comm] using hj
    have hi' : inner ℝ DiC
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) j F) =
        -inner ℝ phi
          (Stationary.vectorL2Coord (mu := M.P.toMeasure) j (HGC i)) := by
      simpa only [DiC, real_inner_comm] using hi
    dsimp only [DjC, DiC]
    rw [hj', hi', hmixed, sub_self]
  have hkerClosed : IsClosed
      ((LinearMap.ker T.toLinearMap : Submodule ℝ
        (Stationary.VectorL2 d M.P.toMeasure)) :
          Set (Stationary.VectorL2 d M.P.toMeasure)) :=
    ContinuousLinearMap.isClosed_ker T
  have hVsol : V ∈ Stationary.stationarySolenoidalSubspace
      (mu := M.P.toMeasure) (d := d) := by
    refine (Submodule.mem_orthogonal _ _).2 fun F hF => ?_
    have hFker : F ∈ LinearMap.ker T.toLinearMap :=
      Submodule.topologicalClosure_minimal S hstrong hkerClosed hF
    rw [LinearMap.mem_ker] at hFker
    dsimp only [T] at hFker
    change inner ℝ V F = 0 at hFker
    rw [real_inner_comm]
    exact hFker
  have horth : inner ℝ Q V = 0 :=
    Stationary.inner_eq_zero_of_mem_potential_of_mem_solenoidal hQpot hVsol
  dsimp only [V] at horth
  rw [inner_sub_right, inner_scalarToVectorL2_basis_right,
    inner_scalarToVectorL2_basis_right] at horth
  have hiQ : inner ℝ
      (Stationary.vectorL2Coord (mu := M.P.toMeasure) i Q) DjC =
      -inner ℝ
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) j (HQ i)) C := by
    have h := (hQcoord i).inner_coord_eq_neg_inner_coord hC j
    dsimp only [DjC]
    linarith
  have hjQ : inner ℝ
      (Stationary.vectorL2Coord (mu := M.P.toMeasure) j Q) DiC =
      -inner ℝ
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) i (HQ j)) C := by
    have h := (hQcoord j).inner_coord_eq_neg_inner_coord hC i
    dsimp only [DiC]
    linarith
  dsimp only [DiC, DjC] at horth
  rw [hiQ, hjQ] at horth
  have hCC : inner ℝ C C = 0 := by
    calc
      inner ℝ C C = inner ℝ
          (Stationary.vectorL2Coord (mu := M.P.toMeasure) i (HQ j) -
            Stationary.vectorL2Coord (mu := M.P.toMeasure) j (HQ i)) C := by
        rw [← hCdef]
      _ = inner ℝ
          (Stationary.vectorL2Coord (mu := M.P.toMeasure) i (HQ j)) C -
        inner ℝ
          (Stationary.vectorL2Coord (mu := M.P.toMeasure) j (HQ i)) C :=
        inner_sub_left _ _ _
      _ = 0 := by linarith
  rw [real_inner_self_eq_norm_sq] at hCC
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hCC)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
