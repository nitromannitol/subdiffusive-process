module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.ConclusionAssembly

@[expose] public section

/-!
# Hölder Step 7: conditional final assembly

This file is strictly downstream of the recurrence and of the Step-6 energy
argument.  It converts a prepaid grid-centred long-gap estimate into the literal
arbitrary-centre excess row and joins it with the elementary short-gap case.
No hypothesis declared here is exposed by the Section-6 provider.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section
attribute [local instance] Classical.propDecidable

noncomputable def holderStepSevenFirstCoefficient
    (C : ℝ) (n ell : ℕ) : ℝ :=
  C * (3 : ℝ) ^ (-((ell : ℝ) - (n : ℝ)) / 4)

noncomputable def holderStepSevenOscillationCoefficient
    (C alpha : ℝ) (ell : ℕ) : ℝ :=
  C * Real.sqrt (1 - alpha) * (3 : ℝ) ^ (-(ell : ℝ))

noncomputable def holderStepSevenRemainder {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (C : ℝ) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (alpha : ℝ)
    (m n ell : ℕ) (x : Vec d) (h : H1Function (openCubeSet (originCube d m)))
    (g : Vec d → Vec d) : ℝ :=
  C * (tailAverage M L m omega (cube d m))⁻¹ *
      (3 : ℝ) ^ ((ell : ℝ) / 2) *
      holderSeminormOn (cube d m) (1 / 2) g +
    (if x ∈ cube d (m - 1) then 0 else
      C * ((1 - alpha) * ((m : ℝ) - (n : ℝ)) *
          vectorSupNormOn (cube d m) h.grad +
        (3 : ℝ) ^ ((ell : ℝ) / 2) *
          fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m)
            (1 / 2) h.grad))

/-- Three-budget algebra for the grid-centred iteration output.  The raw
iteration theorem has one common prefactor multiplying its excess,
oscillation, and accumulated-defect terms.  Once the three scalar coefficient
comparisons are proved, this lemma produces the exact prepaid off-grid
estimate consumed below. -/
theorem holderStepSevenGrid_of_threeBudgets
    {X pref thetaCoeff oscCoeff defect a b c E O : ℝ}
    (hE : 0 ≤ E) (hO : 0 ≤ O)
    (hraw : X ≤ pref * (thetaCoeff * E + oscCoeff * O + defect))
    (hfirst : pref * thetaCoeff ≤ a)
    (hsecond : pref * oscCoeff ≤ b)
    (hthird : pref * defect ≤ c) :
    X ≤ a * E + b * O + c := by
  have hfirst' := mul_le_mul_of_nonneg_right hfirst hE
  have hsecond' := mul_le_mul_of_nonneg_right hsecond hO
  calc
    X ≤ pref * (thetaCoeff * E + oscCoeff * O + defect) := hraw
    _ = (pref * thetaCoeff) * E + (pref * oscCoeff) * O +
        pref * defect := by ring
    _ ≤ a * E + b * O + c :=
      add_le_add (add_le_add hfirst' hsecond') hthird

/-- Step 7 after the grid-centred iteration estimate has been normalized.

The long-gap hypothesis is stated with the exact inverse geometric factors
consumed by `exists_holderOffGridExcessTransfer_scaled`.  Therefore its
conclusion is byte-for-byte the third row of
`HolderRegularityConclusions`.  The short-gap hypothesis is kept separate,
matching the manuscript's initial volume-comparison branch. -/
theorem holderStepSeven_of_short_and_scaledGrid {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (C : ℝ) (hC : 0 ≤ C)
    (L : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (alpha : ℝ) (m X : ℕ)
    (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
    (hshort :
      ∀ n : ℕ, (X : ℤ) ≤ (m : ℤ) - (n : ℤ) →
        (m : ℝ) - (n : ℝ) ≤ (1 - alpha)⁻¹ →
        ∀ ell : ℕ, n ≤ ell → ell + 5 ≤ m → ell ≤ n + 2 →
        ∀ x ∈ cube d m,
          excess n (truncatedCube d m n x) u.toFun ≤
            holderStepSevenFirstCoefficient C n ell *
                excess ell (truncatedCube d m ell x) u.toFun +
              holderStepSevenOscillationCoefficient C alpha ell *
                normalizedL2On (truncatedCube d m ell x)
                  (fun z ↦ u.toFun z -
                    averageOn (truncatedCube d m ell x) u.toFun) +
              holderStepSevenRemainder M C L omega alpha m n ell x h g)
    (hgrid :
      ∀ n : ℕ, (X : ℤ) ≤ (m : ℤ) - (n : ℤ) →
        (m : ℝ) - (n : ℝ) ≤ (1 - alpha)⁻¹ →
        ∀ ell : ℕ, n ≤ ell → ell + 5 ≤ m → n + 2 < ell →
        ∀ x ∈ cube d m, ∀ z : Vec d, OnTriadicGrid n z → z ∈ cube d m →
        truncatedCube d m n x ⊆ truncatedCube d m (n + 1) z →
        truncatedCube d m ((ell : ℤ) - 1) z ⊆ truncatedCube d m ell x →
          excess (n + 1) (truncatedCube d m (n + 1) z) u.toFun ≤
            (holderStepSevenFirstCoefficient C n ell /
                holderOffGridOuterFactor d ^ 2) *
              excess ((ell : ℤ) - 1)
                (truncatedCube d m ((ell : ℤ) - 1) z) u.toFun +
            (holderStepSevenOscillationCoefficient C alpha ell /
                (holderOffGridOuterFactor d *
                  holderOffGridOscillationFactor d)) *
              normalizedL2On (truncatedCube d m ((ell : ℤ) - 1) z)
                (fun y ↦ u.toFun y -
                  averageOn (truncatedCube d m ((ell : ℤ) - 1) z) u.toFun) +
            holderStepSevenRemainder M C L omega alpha m n ell x h g /
              holderOffGridOuterFactor d) :
    ∀ n : ℕ, (X : ℤ) ≤ (m : ℤ) - (n : ℤ) →
      (m : ℝ) - (n : ℝ) ≤ (1 - alpha)⁻¹ →
      ∀ ell : ℕ, n ≤ ell → ell + 5 ≤ m → ∀ x ∈ cube d m,
        excess n (truncatedCube d m n x) u.toFun ≤
          C * (3 : ℝ) ^ (-((ell : ℝ) - (n : ℝ)) / 4) *
              excess ell (truncatedCube d m ell x) u.toFun +
            C * Real.sqrt (1 - alpha) * (3 : ℝ) ^ (-(ell : ℝ)) *
              normalizedL2On (truncatedCube d m ell x)
                (fun z ↦ u.toFun z -
                  averageOn (truncatedCube d m ell x) u.toFun) +
            C * (tailAverage M L m omega (cube d m))⁻¹ *
              (3 : ℝ) ^ ((ell : ℝ) / 2) *
              holderSeminormOn (cube d m) (1 / 2) g +
            (if x ∈ cube d (m - 1) then 0 else
              C * ((1 - alpha) * ((m : ℝ) - (n : ℝ)) *
                  vectorSupNormOn (cube d m) h.grad +
                (3 : ℝ) ^ ((ell : ℝ) / 2) *
                  fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m)
                    (1 / 2) h.grad)) := by
  intro n hn hwindow ell hnell hellm x hx
  by_cases hlong : n + 2 < ell
  · have ha : 0 ≤ holderStepSevenFirstCoefficient C n ell := by
      unfold holderStepSevenFirstCoefficient
      positivity
    have hb : 0 ≤ holderStepSevenOscillationCoefficient C alpha ell := by
      unfold holderStepSevenOscillationCoefficient
      exact mul_nonneg
        (mul_nonneg hC (Real.sqrt_nonneg _))
        (Real.rpow_nonneg (by norm_num) _)
    have huWindow : MemLp u.toFun 2
        (volume.restrict (truncatedCube d m ell x)) :=
      u.memL2.mono_measure
        (Measure.restrict_mono (truncatedCube_subset_cube d m ell x) le_rfl)
    obtain ⟨_z, _hzgrid, _hz, hbound⟩ :=
      exists_holderOffGridExcessTransfer_scaled hx hlong (by omega) ha hb huWindow
        (by
          intro z hzgrid hz hsubN hsubEll
          exact hgrid n hn hwindow ell hnell hellm hlong x hx z hzgrid hz
            hsubN hsubEll)
    simpa only [holderStepSevenFirstCoefficient,
      holderStepSevenOscillationCoefficient, holderStepSevenRemainder,
      add_assoc] using hbound
  · have hshortGap : ell ≤ n + 2 := by omega
    simpa only [holderStepSevenFirstCoefficient,
      holderStepSevenOscillationCoefficient, holderStepSevenRemainder,
      add_assoc] using
        hshort n hn hwindow ell hnell hellm hshortGap x hx

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
