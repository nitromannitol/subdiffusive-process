import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.CubeGeometry
import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.ZeroDatum
import SubdiffusiveProcess.Frozen.Section6.Defs.HolderRegularityConclusions




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}



theorem normalizedL2On_translatedCube_le_of_holderRegularityConclusions
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {C : ℝ} {L : ℕ}
    {ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d} {alpha : ℝ} {m X : ℕ}
    {u : H1Function (openCubeSet (originCube d m))} {n : ℕ} {z : Vec d}
    (hconc : HolderRegularityConclusions M C L ω alpha m X u u
      (fun _ ↦ (0 : Vec d)))
    (hn : (n : ℤ) ≤ (m : ℤ) - (X : ℤ))
    (hgrid : OnTriadicGrid n z)
    (hsub : translatedCube d n z ⊆ cube d ((m : ℤ) - 1)) :
    normalizedL2On (translatedCube d (n : ℤ) z)
        (fun x ↦ u.toFun x - averageOn (translatedCube d (n : ℤ) z) u.toFun) ≤
      C * (3 : ℝ) ^ (-alpha * ((m : ℝ) - (n : ℝ))) *
        normalizedL2On (cube d m)
          (fun x ↦ u.toFun x - averageOn (cube d m) u.toFun) := by
  have hzm : z ∈ cube d (m : ℤ) := mem_cube_of_translatedCube_subset_pred hsub
  have hzpred : z ∈ cube d ((m : ℤ) - 1) :=
    mem_cube_pred_of_translatedCube_subset hsub
  have hwin : truncatedCube d (m : ℤ) (n : ℤ) z = translatedCube d (n : ℤ) z :=
    truncatedCube_eq_translatedCube_of_subset_pred hsub
  -- Instantiate the first clause at `x = z`, `ℓ = n`, `y = z`.
  have hmem : z ∈ truncatedCube d (m : ℤ) (n : ℤ) z :=
    mem_truncatedCube_self (n : ℤ) hzm
  have hmain := hconc.1 n hn z hzm n le_rfl z hgrid hmem
  -- `ℓ = n` makes the left-hand gain factor one.
  rw [show alpha * ((n : ℝ) - (n : ℝ)) = 0 by ring, Real.rpow_zero,
    one_mul, hwin] at hmain
  -- `g = 0` kills the datum term; `z ∈ 𝔠_{m-1}` kills the boundary indicator.
  rw [holderSeminormOn_zero, mul_zero, if_pos hzpred, add_zero,
    add_zero] at hmain
  exact hmain



theorem vectorNormalizedL2On_translatedCube_le_of_holderRegularityConclusions
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {C : ℝ} {L : ℕ}
    {ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d} {alpha : ℝ} {m X : ℕ}
    {u : H1Function (openCubeSet (originCube d m))} {n : ℕ} {z : Vec d}
    (hconc : HolderRegularityConclusions M C L ω alpha m X u u
      (fun _ ↦ (0 : Vec d)))
    (hn : (n : ℤ) ≤ (m : ℤ) - (X : ℤ))
    (hsub : translatedCube d n z ⊆ cube d ((m : ℤ) - 1)) :
    vectorNormalizedL2On (translatedCube d (n : ℤ) z)
        (fun x ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω x) •
          u.grad x) ≤
      C * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
        vectorNormalizedL2On (cube d m)
          (fun x ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω x) •
            u.grad x) := by
  have hzm : z ∈ cube d (m : ℤ) := mem_cube_of_translatedCube_subset_pred hsub
  have hzpred : z ∈ cube d ((m : ℤ) - 1) :=
    mem_cube_pred_of_translatedCube_subset hsub
  have hwin : truncatedCube d (m : ℤ) (n : ℤ) z = translatedCube d (n : ℤ) z :=
    truncatedCube_eq_translatedCube_of_subset_pred hsub
  have hmain := hconc.2.1 n hn z hzm
  rw [hwin] at hmain
  rw [holderSeminormOn_zero, mul_zero, if_pos hzpred, add_zero,
    add_zero] at hmain
  exact hmain

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
