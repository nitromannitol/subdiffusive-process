module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.NormalizedCutoffLaw
public import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffP4
public import Homogenization.Book.Ch05.Theorems.Section51.AnnealedConvergence

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- The `(P4)` moment record of the range-normalized GMC cutoff law, in the
vocabulary of `NormalizedCutoffLaw.lean`. -/
def normalizedCutoffLaw_quantitativeCoarseGrainedEllipticity [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) :
    Ch05.QuantitativeCoarseGrainedEllipticity (normalizedCutoffLaw M L) :=
  aCutoffNormalization_quantitativeCoarseGrainedEllipticity M L

/-- **Annealed algebraic contrast decay for the GMC fixed cutoff.**

For every model and cutoff level there are `C, alpha > 0` such that the annealed
coarse-grained scalar contrast of the range-normalized cutoff law decays
algebraically above the annealed entry scale.

Unconditional: the only input is the library own `(P4)` moment record. -/
theorem exists_annealed_contrast_decay_normalizedCutoffLaw [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) :
    ∃ C alpha : ℝ, 0 < C ∧ 0 < alpha ∧
      ∀ n : ℕ,
        Ch05.thetaAtScale (normalizedCutoffLaw_lawCarrier M L)
            (normalizedCutoffLaw_structuralLaw M L)
            ((Ch05.annealedAlgebraicEntryScale (normalizedCutoffLaw M L)
                (normalizedCutoffLaw_quantitativeCoarseGrainedEllipticity M L) C
              + n : ℕ) : ℤ) ≤
          1 + Real.rpow (3 : ℝ) (-alpha * (n : ℝ)) := by
  obtain ⟨C, alpha, hC, halpha, hmain⟩ :=
    Ch05.Section51.annealedConvergence_homogenizationScale
      (d := d)
      (normalizedCutoffLaw_quantitativeCoarseGrainedEllipticity M L).params
  exact ⟨C, alpha, hC, halpha,
    hmain (normalizedCutoffLaw_lawCarrier M L)
      (normalizedCutoffLaw_structuralLaw M L)
      (normalizedCutoffLaw_quantitativeCoarseGrainedEllipticity M L) rfl⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
