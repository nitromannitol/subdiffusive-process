module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.AccumulatedErrorExtraction
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.LongRatio
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Observables

@[expose] public section

/-!
# Hölder Step 3: coefficient-ratio algebra

This file isolates the exact algebra behind `e.ratio.of.bs`.  It identifies
the local lower-cutoff tail coefficient with the existing combined
ratio based at the parent cutoff.  Quantitative bounds can therefore be
assembled from the finite shell block, the annealed normalizer error, and the
two parent-suffix oscillations without re-expanding `aCutoff`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization

noncomputable section

private abbrev Sample (d : ℕ) := _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- Exact pointwise identity underlying the lower-scale/top-scale normalizer
comparison in Step 3. -/
theorem tailCoefficient_div_eq_combinedCoefficientRatio {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m q : ℕ}
    (hqm : q ≤ m) (hmL : m ≤ L) (omega : Sample d) (z x : Vec d) :
    tailCoefficient M L q (translatePotentialSample z omega) x /
        tailCoefficientCubeAverage M L m omega =
      combinedCoefficientRatio M L m q omega z x := by
  have hqL : q ≤ L := hqm.trans hmL
  have hb : tailCoefficientCubeAverage M L m omega ≠ 0 :=
    (tailCoefficientCubeAverage_pos M L m omega).ne'
  have h := normalizedCutoffRatio_eq_tailCoefficient_div_mul_exp
    M hqm hmL (translatePotentialSample z omega) x hb
  rw [show (_root_.SubdiffusiveProcess.Model.aCutoff M L
          (translatePotentialSample z omega) x /
        tailCoefficientCubeAverage M L m omega) /
        (_root_.SubdiffusiveProcess.Model.aCutoff M q
          (translatePotentialSample z omega) x / ahom M q) =
      tailCoefficient M L q (translatePotentialSample z omega) x /
        tailCoefficientCubeAverage M L m omega by
      unfold tailCoefficient
      rw [min_eq_left hqL]
      field_simp]
    at h
  simpa only [combinedCoefficientRatio] using h

/-- Reciprocal form of the same exact identity. -/
theorem tailCoefficientCubeAverage_div_eq_combinedCoefficientRatioInv {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m q : ℕ}
    (hqm : q ≤ m) (hmL : m ≤ L) (omega : Sample d) (z x : Vec d) :
    tailCoefficientCubeAverage M L m omega /
        tailCoefficient M L q (translatePotentialSample z omega) x =
      combinedCoefficientRatioInv M L m q omega z x := by
  have hforward := tailCoefficient_div_eq_combinedCoefficientRatio
    M hqm hmL omega z x
  have hlocal : 0 < tailCoefficient M L q
      (translatePotentialSample z omega) x :=
    tailCoefficient_pos_of_ahom_pos M L q (translatePotentialSample z omega)
      (ahom_pos M (min q L)) x
  have htop : 0 < tailCoefficientCubeAverage M L m omega :=
    tailCoefficientCubeAverage_pos M L m omega
  unfold combinedCoefficientRatio at hforward
  unfold combinedCoefficientRatioInv
  have htail : 0 < tailCoefficient M L m
      (translatePotentialSample z omega) x :=
    tailCoefficient_pos_of_ahom_pos M L m (translatePotentialSample z omega)
      (ahom_pos M (min m L)) x
  have hexp : 0 < Real.exp
      (shellBlock m q (translatePotentialSample z omega) x +
        normalizerLogError M m q) := Real.exp_pos _
  have hlocalEq : tailCoefficient M L q (translatePotentialSample z omega) x =
      tailCoefficient M L m (translatePotentialSample z omega) x *
        Real.exp (shellBlock m q (translatePotentialSample z omega) x +
          normalizerLogError M m q) := by
    apply (div_left_inj' htop.ne').mp
    calc
      tailCoefficient M L q (translatePotentialSample z omega) x /
          tailCoefficientCubeAverage M L m omega =
        tailCoefficient M L m (translatePotentialSample z omega) x /
            tailCoefficientCubeAverage M L m omega *
          Real.exp (shellBlock m q (translatePotentialSample z omega) x +
            normalizerLogError M m q) := hforward
      _ = (tailCoefficient M L m (translatePotentialSample z omega) x *
            Real.exp (shellBlock m q (translatePotentialSample z omega) x +
              normalizerLogError M m q)) /
          tailCoefficientCubeAverage M L m omega := by ring
  rw [hlocalEq, Real.exp_neg]
  field_simp

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
