module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.HarmonicExtensionSelection
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import SubdiffusiveProcess.Sobolev.WeakGradient

@[expose] public section

open MeasureTheory Set TopologicalSpace
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

noncomputable section

namespace SubdiffusiveProcess

/-- A weakly harmonic cell function minimizes energy among all functions with the same trace. Source: `eq:mfd-18`. -/
theorem energy_eq_sInf_sameTrace_of_isWeaklyHarmonicOn
    {d : ℕ} [NeZero d] {W : Set (SpatialCoordinates d)}
    {a : SpatialCoordinates d → ℝ} {lam Lam : ℝ}
    (_hW : IsOpenBoundedConvexDomain W) (_hne : W.Nonempty)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField a))
    {w φ : H1Function W}
    (hw : IsWeaklyHarmonicOn a W w)
    (htrace : HasZeroTraceDifferenceOn W w φ) :
    energy a W w =
      sInf {e : ℝ | ∃ u : H1Function W,
        HasZeroTraceDifferenceOn W u φ ∧ e = energy a W u} := by
  have ha : ∀ x ∈ W, 0 ≤ a x := by
    intro x hx
    have hlam : 0 < lam := (hEll.2 x hx).1
    let i0 : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
    have hnorm : vecNormSq (Pi.single i0 1) = 1 := by
      rw [vecNormSq, vecDot, Finset.sum_eq_single i0]
      · simp
      · intro j _ hji
        simp [Pi.single_eq_of_ne hji]
      · simp
    have hlower := (hEll.2 x hx).2.2.1
      (Pi.single i0 1)
    have hdot : vecDot (Pi.single i0 1)
        (matVecMul (scalarCoeffField a x) (Pi.single i0 1)) = a x := by
      rw [scalarCoeffField, Homogenization.matVecMul_scalarMatrix,
        vecDot_smul_right]
      have hdotself : vecDot (Pi.single i0 1) (Pi.single i0 1) = 1 := by
        simpa only [vecNormSq] using hnorm
      rw [hdotself, mul_one]
    have hax : lam ≤ a x := by
      calc
        lam = lam * 1 := by ring
        _ = lam * vecNormSq (Pi.single i0 1) := by rw [hnorm]
        _ ≤ vecDot (Pi.single i0 1)
            (matVecMul (scalarCoeffField a x) (Pi.single i0 1)) := hlower
        _ = a x := hdot
    exact (le_of_lt hlam).trans hax
  have hmin : ∀ {u : H1Function W},
      HasZeroTraceDifferenceOn W u φ → energy a W w ≤ energy a W u := by
    intro u hu
    obtain ⟨rho, _, hrho⟩ :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.exists_h10Function_solutionDifference_sub_boundaryDifference
        htrace hu
    have h :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.integral_coefficient_mul_grad_sq_le_of_boundaryDifference
        (w := w) (h := u) hEll ha hw rho (by
          intro x
          have hrg : rho.toH1Function.grad x = w.grad x - u.grad x := by
            simpa only [sub_self, sub_zero] using hrho x
          calc
            w.grad x = u.grad x + (w.grad x - u.grad x) := by ring
            _ = u.grad x + rho.toH1Function.grad x := by rw [hrg])
    simpa [energy, vecNormSq] using h
  let S : Set ℝ := {e : ℝ | ∃ u : H1Function W,
    HasZeroTraceDifferenceOn W u φ ∧ e = energy a W u}
  have hmem : energy a W w ∈ S := ⟨w, htrace, rfl⟩
  have hbound : ∀ e ∈ S, energy a W w ≤ e := by
    intro e he
    rcases he with ⟨u, hu, rfl⟩
    exact hmin hu
  have hSbdd : BddBelow S := ⟨energy a W w, hbound⟩
  have hle : sInf S ≤ energy a W w := csInf_le hSbdd hmem
  have hge : energy a W w ≤ sInf S := le_csInf ⟨energy a W w, hmem⟩ hbound
  exact le_antisymm hge hle

end SubdiffusiveProcess
