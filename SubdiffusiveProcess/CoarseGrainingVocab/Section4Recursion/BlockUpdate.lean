import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.InductionHypothesis
import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.TailCoefficient

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion

/-!
# Block-update arithmetic

These lemmas are the deterministic final lines of the two inductions.  Their
decomposition follows Algsuperdiff's `IterateAssembly.lean`: the gain, shell
error, and averaging estimate are supplied separately and only their numeric
absorption is performed here.
-/

/-- Push separate bounds for the old defect and shell-ratio square through the
pointwise localization update supplied by sensitivity. -/
theorem localization_update {Jnext Jold Xsq gain shell : ℝ}
    (hJold : 0 ≤ Jold) (hshell : 0 ≤ shell)
    (hupdate : Jnext ≤ 2 * Jold + 3 * Xsq * (Jold + 1))
    (hgain : Jold ≤ gain) (hX : Xsq ≤ shell) :
    Jnext ≤ 2 * gain + 3 * shell * (gain + 1) := by
  have hprod : Xsq * (Jold + 1) ≤ shell * (gain + 1) :=
    mul_le_mul hX (by linarith) (by linarith) hshell
  linarith

/-- Close the first block induction from the quarter-gain and the squared
shell-ratio moment. -/
theorem firstBlockUpdate_close {Jnext Jold X δ1 : ℝ}
    (hδ : 0 ≤ δ1) (hδ' : δ1 ≤ 1)
    (hupdate : Jnext ≤ 2 * Jold + 3 * X * (1 + Jold))
    (hgain : Jold ≤ (1 / 4 : ℝ) * δ1)
    (hshell : X ≤ (1 / 12 : ℝ) * δ1) (hJold : 0 ≤ Jold) :
    Jnext ≤ δ1 := by
  have hmul : X * Jold ≤
      ((1 / 12 : ℝ) * δ1) * ((1 / 4 : ℝ) * δ1) :=
    mul_le_mul hshell hgain hJold (by positivity)
  nlinarith

/-- Close the second induction after the color-class/Rosenthal payload has
bounded the averaged square block. -/
theorem secondBlockUpdate_close {Jnext shell δ1 : ℝ}
    (hδ : 0 ≤ δ1) (hδ' : δ1 ≤ 1)
    (hnext : Jnext ≤ shell + (1 / 2 : ℝ) * (1 + shell) * δ1)
    (hshell : shell ≤ (1 / 4 : ℝ) * δ1) :
    Jnext ≤ δ1 := by
  nlinarith

/-- The printed last-line absorption with an explicit dimensional constant. -/
theorem secondBlockUpdate_parameter_absorption {C ξ delta h δ1 : ℝ}
    (hsmall : C * ξ * delta ^ 2 * h ≤ (1 / 2 : ℝ) * δ1) :
    (1 / 2 : ℝ) * δ1 + C * ξ * delta ^ 2 * h ≤ δ1 := by
  linarith

end SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion
