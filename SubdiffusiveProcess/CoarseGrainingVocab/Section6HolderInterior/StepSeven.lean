module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.StepSevenConditional
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.Conclusions

@[expose] public section

/-!
# Interior Hölder Step 7: the excess row of the interior package

The interior mirror of `Section6Holder.holderStepSeven_of_short_and_scaledGrid`.
The off-grid transfer it consumes
(`Section6Holder.exists_holderOffGridExcessTransfer_scaled`) is purely
geometric and already datum-free, so the only change is that the remainder
carries no boundary summand and the base points are the interior ones.

The conclusion is **byte-for-byte the third row of the
`InteriorHolderRegularityConclusions`**.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

noncomputable def interiorStepSevenFirstCoefficient
    (C : ℝ) (n ell : ℕ) : ℝ :=
  C * (3 : ℝ) ^ (-((ell : ℝ) - (n : ℝ)) / 4)

noncomputable def interiorStepSevenOscillationCoefficient
    (C alpha : ℝ) (ell : ℕ) : ℝ :=
  C * Real.sqrt (1 - alpha) * (3 : ℝ) ^ (-(ell : ℝ))

noncomputable def interiorStepSevenRemainder {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (C : ℝ) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (m ell : ℕ)
    (g : Vec d → Vec d) : ℝ :=
  C * (tailAverage M L m omega (cube d m))⁻¹ *
    (3 : ℝ) ^ ((ell : ℝ) / 2) *
    holderSeminormOn (cube d m) (1 / 2) g

/-- Interior Step 7 after the grid-centred iteration estimate has been
normalized.  The conclusion is the third interior row. -/
theorem interiorStepSeven_of_short_and_scaledGrid {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (C : ℝ) (hC : 0 ≤ C)
    (L : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (alpha : ℝ) (m X : ℕ)
    (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
    (hshort :
      ∀ n : ℕ, (X : ℤ) ≤ (m : ℤ) - (n : ℤ) →
        (m : ℝ) - (n : ℝ) ≤ (1 - alpha)⁻¹ →
        ∀ ell : ℕ, n ≤ ell → ell + 5 ≤ m → ell ≤ n + 2 →
        ∀ x ∈ cube d ((m : ℤ) - 1),
          excess n (truncatedCube d m n x) u.toFun ≤
            interiorStepSevenFirstCoefficient C n ell *
                excess ell (truncatedCube d m ell x) u.toFun +
              interiorStepSevenOscillationCoefficient C alpha ell *
                normalizedL2On (truncatedCube d m ell x)
                  (fun z ↦ u.toFun z -
                    averageOn (truncatedCube d m ell x) u.toFun) +
              interiorStepSevenRemainder M C L omega m ell g)
    (hgrid :
      ∀ n : ℕ, (X : ℤ) ≤ (m : ℤ) - (n : ℤ) →
        (m : ℝ) - (n : ℝ) ≤ (1 - alpha)⁻¹ →
        ∀ ell : ℕ, n ≤ ell → ell + 5 ≤ m → n + 2 < ell →
        ∀ x ∈ cube d ((m : ℤ) - 1), ∀ z : Vec d, OnTriadicGrid n z →
        z ∈ cube d m →
        truncatedCube d m n x ⊆ truncatedCube d m (n + 1) z →
        truncatedCube d m ((ell : ℤ) - 1) z ⊆ truncatedCube d m ell x →
          excess (n + 1) (truncatedCube d m (n + 1) z) u.toFun ≤
            (interiorStepSevenFirstCoefficient C n ell /
                holderOffGridOuterFactor d ^ 2) *
              excess ((ell : ℤ) - 1)
                (truncatedCube d m ((ell : ℤ) - 1) z) u.toFun +
            (interiorStepSevenOscillationCoefficient C alpha ell /
                (holderOffGridOuterFactor d *
                  holderOffGridOscillationFactor d)) *
              normalizedL2On (truncatedCube d m ((ell : ℤ) - 1) z)
                (fun y ↦ u.toFun y -
                  averageOn (truncatedCube d m ((ell : ℤ) - 1) z) u.toFun) +
            interiorStepSevenRemainder M C L omega m ell g /
              holderOffGridOuterFactor d) :
    ∀ n : ℕ, (X : ℤ) ≤ (m : ℤ) - (n : ℤ) →
      (m : ℝ) - (n : ℝ) ≤ (1 - alpha)⁻¹ →
      ∀ ell : ℕ, n ≤ ell → ell + 5 ≤ m → ∀ x ∈ cube d ((m : ℤ) - 1),
        excess n (truncatedCube d m n x) u.toFun ≤
          C * (3 : ℝ) ^ (-((ell : ℝ) - (n : ℝ)) / 4) *
              excess ell (truncatedCube d m ell x) u.toFun +
            C * Real.sqrt (1 - alpha) * (3 : ℝ) ^ (-(ell : ℝ)) *
              normalizedL2On (truncatedCube d m ell x)
                (fun z ↦ u.toFun z -
                  averageOn (truncatedCube d m ell x) u.toFun) +
            C * (tailAverage M L m omega (cube d m))⁻¹ *
              (3 : ℝ) ^ ((ell : ℝ) / 2) *
              holderSeminormOn (cube d m) (1 / 2) g := by
  intro n hn hwindow ell hnell hellm x hx
  by_cases hlong : n + 2 < ell
  · have ha : 0 ≤ interiorStepSevenFirstCoefficient C n ell := by
      unfold interiorStepSevenFirstCoefficient
      positivity
    have hb : 0 ≤ interiorStepSevenOscillationCoefficient C alpha ell := by
      unfold interiorStepSevenOscillationCoefficient
      exact mul_nonneg
        (mul_nonneg hC (Real.sqrt_nonneg _))
        (Real.rpow_nonneg (by norm_num) _)
    have huWindow : MemLp u.toFun 2
        (volume.restrict (truncatedCube d m ell x)) :=
      u.memL2.mono_measure
        (Measure.restrict_mono (truncatedCube_subset_cube d m ell x) le_rfl)
    obtain ⟨_z, _hzgrid, _hz, hbound⟩ :=
      exists_holderOffGridExcessTransfer_scaled (mem_cube_of_mem_cube_sub_one hx)
        hlong (by omega) ha hb huWindow
        (by
          intro z hzgrid hz hsubN hsubEll
          exact hgrid n hn hwindow ell hnell hellm hlong x hx z hzgrid hz
            hsubN hsubEll)
    simpa only [interiorStepSevenFirstCoefficient,
      interiorStepSevenOscillationCoefficient, interiorStepSevenRemainder,
      add_assoc] using hbound
  · have hshortGap : ell ≤ n + 2 := by omega
    simpa only [interiorStepSevenFirstCoefficient,
      interiorStepSevenOscillationCoefficient, interiorStepSevenRemainder,
      add_assoc] using
        hshort n hn hwindow ell hnell hellm hshortGap x hx

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
