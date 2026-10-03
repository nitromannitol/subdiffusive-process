module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.TopWindowEnergy
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneInstantiation

@[expose] public section

/-!
# Row 2's tail-average pairing: `sigma_n^{1/2} / sigma_{top}^{1/2}`

Row 2's Step-6 budget carries `sigma_n = (b_{L,n+2})_{z+cu_{n+2}}` on the
oscillation leg, while `TopWindowEnergy.exists_interiorTopWindowOscillationEnergy`
consumes `sigma_{top} = (b_{L,top+4})_{z+cu_{top+4}}`.  Their ratio is what the
manuscript's `e.ratio.of.bs` controls, and it is controlled **in both
directions**: `Section6Holder.stopped_tailAverage_ratio_bounds_exp` returns a
conjunction, of which `RowOneInstantiation.stoppedRatio_row` exports only the
second half.  The first half is exported here.

The pairing is then arithmetic: writing `sigma_n / sigma_top =
(sigma_n / b) * (b / sigma_top)` with `b` the domain-scale tail average, each
factor is at most `exp(C lambda (m-n))`, so the square root of the product is at
most `exp(C lambda (m-n))` too — the same `exp(C lambda (m-n))` price the
row-1 absorption already knows how to convert into a fraction of the frozen gap
gain.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- **The forward tail-average ratio row.**  The local tail average over the
domain-scale one, at the same exponential rate as `stoppedRatio_row`. -/
theorem stoppedRatio_row_forward
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (C1 C2 alpha : ℝ)
    (step m ell top L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hellm : ell < m) (hmL : m ≤ L) (htop : top + 5 ≤ m)
    (hlambda0 : 0 ≤ Section6Stopping.holderStoppingLambda C1 alpha)
    (hlambda1 : Section6Stopping.holderStoppingLambda C1 alpha < 1)
    (hepsilon : 0 ≤ Section6Stopping.holderStoppingEpsilon C2 alpha)
    (hdelta : M.delta ^ 2 ≤ Section6Stopping.holderStoppingLambda C1 alpha)
    (y : Vec d) (hy : y ∈ cube d m)
    (hstop : (Section6Stopping.measurableHolderStoppingScale M alpha
        (Section6Stopping.holderStoppingLambda C1 alpha)
        (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
      (m : ℤ) - (ell : ℤ))
    (hygrid : OnTriadicGrid ell y) :
    ∀ j ∈ Finset.Icc ell top,
      tailAverage M L (j + 2) omega (translatedCube d (j + 2 : ℕ) y) /
          tailCoefficientCubeAverage M L m omega ≤
        Real.exp (ratioRate d *
          Section6Stopping.holderStoppingLambda C1 alpha *
          ((m : ℝ) - (ell : ℝ))) := by
  intro j hj
  rw [Finset.mem_Icc] at hj
  obtain ⟨hcY, hc0⟩ := stoppedControls_pair M C1 C2 alpha step m ell omega hstop
    y hygrid hy
  have hraw := Section6Holder.stopped_tailAverage_ratio_bounds_exp
    (M := M) (L := L) (n := ell) (q := j + 2) (m := m)
    hellm (by omega) (by omega) hmL
    (Section6Stopping.holderStoppingEpsilon C2 alpha)
    Section6Stopping.holderStoppingS
    (Section6Stopping.holderStoppingLambda C1 alpha)
    hepsilon (by rw [Section6Stopping.holderStoppingS]; norm_num)
    hlambda0 hlambda1 hdelta omega y hy hcY.1 hc0.1 hcY.2 hc0.2
  dsimp only at hraw
  exact hraw.1

/-- **The pairing.**  With both ratio directions bounded by `E`, the square-root
quotient of the two local tail averages is bounded by `E`. -/
theorem sqrt_tailAverage_pairing {sigmaN sigmaTop b E : ℝ}
    (hsigmaN : 0 ≤ sigmaN) (hsigmaTop : 0 < sigmaTop) (hb : 0 < b) (hE : 0 ≤ E)
    (h1 : sigmaN / b ≤ E) (h2 : b / sigmaTop ≤ E) :
    Real.sqrt sigmaN * (Real.sqrt sigmaTop)⁻¹ ≤ E := by
  have hquot : sigmaN / sigmaTop ≤ E ^ 2 := by
    have hsplit : sigmaN / sigmaTop = (sigmaN / b) * (b / sigmaTop) := by
      field_simp
    have h1' : 0 ≤ sigmaN / b := div_nonneg hsigmaN hb.le
    have h2' : 0 ≤ b / sigmaTop := div_nonneg hb.le hsigmaTop.le
    rw [hsplit]
    calc (sigmaN / b) * (b / sigmaTop) ≤ E * E :=
          mul_le_mul h1 h2 h2' hE
      _ = E ^ 2 := by ring
  have hroot : Real.sqrt (sigmaN / sigmaTop) ≤ E := by
    have := Real.sqrt_le_sqrt hquot
    rwa [Real.sqrt_sq hE] at this
  rwa [Real.sqrt_div' _ hsigmaTop.le, div_eq_mul_inv] at hroot

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
