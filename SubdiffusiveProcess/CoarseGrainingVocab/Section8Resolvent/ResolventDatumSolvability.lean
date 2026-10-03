module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumGMCDenseRange

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Topology
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions
open MarkovProcess MarkovProcess.Semigroup
open scoped ZeroAtInfty CompactlySupported

noncomputable section

variable {d : ℕ}



theorem hasC0MassiveSolutions_reversible_of_solvability [NeZero d]
    (M : GMCModel d) (L : WithTop ℕ) (omega : AnchoredC11Sample d)
    (hsolve : HasC0MassiveSolutionsOnCompactData (coefficientAt M L omega)
      (coefficientAt M L omega)) :
    HasC0MassiveSolutions (coefficientAt M L omega) (coefficientAt M L omega) :=
  hasC0MassiveSolutions_of_hasC0MassiveSolutionsOnCompactData M L omega
    (reversibleMassiveCubeBounds M L omega) hsolve



theorem hasC0MassiveSolutions_divergence_of_solvability [NeZero d]
    (M : GMCModel d) (L : WithTop ℕ) (omega : AnchoredC11Sample d)
    (hsolve : HasC0MassiveSolutionsOnCompactData (coefficientAt M L omega)
      (fun _ ↦ (1 : ℝ))) :
    HasC0MassiveSolutions (coefficientAt M L omega) (fun _ ↦ (1 : ℝ)) :=
  hasC0MassiveSolutions_of_hasC0MassiveSolutionsOnCompactData M L omega
    (divergenceMassiveCubeBounds M L omega) hsolve

/-- **`l.gmc.resolvent.datum` from whole-space solvability on compactly
supported data.**  This is the repaired gate: the frozen conclusion follows from
the existence, for each pair and each sample, of one `C₀` solution per positive
shift and per compactly supported datum.  Dense range, the resolvent identity,
linearity, positivity, the contraction and the weak elliptic characterization are
supplied by the landed material. -/
theorem exists_gmc_resolvent_data_of_solvability [NeZero d]
    (M : GMCModel d) (L : WithTop ℕ)
    (hX : ∀ omega : AnchoredC11Sample d,
      HasC0MassiveSolutionsOnCompactData (coefficientAt M L omega)
        (coefficientAt M L omega))
    (hY : ∀ omega : AnchoredC11Sample d,
      HasC0MassiveSolutionsOnCompactData (coefficientAt M L omega)
        (fun _ ↦ (1 : ℝ))) :
    ∃ DX DY : AnchoredC11Sample d → C0ResolventDatum (Vec d),
      ∀ omega,
        (∀ mu, DenseRange ((DX omega).operator mu)) ∧
        IsWeakEllipticResolvent (coefficientAt M L omega)
          (coefficientAt M L omega) (DX omega) ∧
        (∀ mu, DenseRange ((DY omega).operator mu)) ∧
        IsWeakEllipticResolvent (coefficientAt M L omega)
          (fun _ ↦ (1 : ℝ)) (DY omega) :=
  exists_gmc_resolvent_data_of_hasC0MassiveSolutions M L
    (fun omega ↦ hasC0MassiveSolutions_reversible_of_solvability M L omega (hX omega))
    (fun omega ↦ hasC0MassiveSolutions_divergence_of_solvability M L omega (hY omega))
    (fun omega ↦ hasStrongMassiveResolventLimit_of_hasDenseMassiveResolventRange
      (reversibleMassiveCubeBounds M L omega)
      (hasDenseMassiveResolventRange_reversible M L omega))
    (fun omega ↦ hasStrongMassiveResolventLimit_of_hasDenseMassiveResolventRange
      (divergenceMassiveCubeBounds M L omega)
      (hasDenseMassiveResolventRange_divergence M L omega))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
