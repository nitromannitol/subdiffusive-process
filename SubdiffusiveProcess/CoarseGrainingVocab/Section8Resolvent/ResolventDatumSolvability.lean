module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumGMCDenseRange

@[expose] public section

/-!
# The Section 8 datum from whole-space solvability

This module states the datum gate over the *existence* form
`HasC0MassiveSolutionsOnCompactData` — for every positive shift and every
compactly supported datum there is *some* `C₀` solution — which is exactly what
the reduction chain consumes.  It describes the minimal solution obtained as
the limit of Dirichlet problems on exhausting cubes.

Everything else that  needs is already a theorem: dense
range (`hasDenseMassiveResolventRange_reversible/_divergence`), the weak
elliptic characterization, the resolvent identity, linearity and positivity
(through the whole-space maximum principle).

## Main declarations

* `exists_gmc_resolvent_data_of_solvability` — the conclusion  from `HasC0MassiveSolutionsOnCompactData` for the two
  pairs, and nothing else.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Topology
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Model
open MarkovProcess MarkovProcess.Semigroup
open scoped ZeroAtInfty CompactlySupported

noncomputable section

variable {d : ℕ}

/-- The reversible pair `(c, ρ) = (a, a)`. -/
theorem hasC0MassiveSolutions_reversible_of_solvability [NeZero d]
    (M : GMCModel d) (L : WithTop ℕ) (omega : AnchoredC11Sample d)
    (hsolve : HasC0MassiveSolutionsOnCompactData (coefficientAt M L omega)
      (coefficientAt M L omega)) :
    HasC0MassiveSolutions (coefficientAt M L omega) (coefficientAt M L omega) :=
  hasC0MassiveSolutions_of_hasC0MassiveSolutionsOnCompactData M L omega
    (reversibleMassiveCubeBounds M L omega) hsolve

/-- The divergence-form pair `(c, ρ) = (a, 1)`. -/
theorem hasC0MassiveSolutions_divergence_of_solvability [NeZero d]
    (M : GMCModel d) (L : WithTop ℕ) (omega : AnchoredC11Sample d)
    (hsolve : HasC0MassiveSolutionsOnCompactData (coefficientAt M L omega)
      (fun _ ↦ (1 : ℝ))) :
    HasC0MassiveSolutions (coefficientAt M L omega) (fun _ ↦ (1 : ℝ)) :=
  hasC0MassiveSolutions_of_hasC0MassiveSolutionsOnCompactData M L omega
    (divergenceMassiveCubeBounds M L omega) hsolve

/-- ** from whole-space solvability on compactly
supported data.**  This is the repaired gate: the conclusion follows from
the existence, for each pair and each sample, of one `C₀` solution per positive
shift and per compactly supported datum.  Dense range, the resolvent identity,
linearity, positivity, the contraction and the weak elliptic characterization are
supplied by the proved material. -/
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
