module

public import SubdiffusiveProcess.VariationalResponses.MeshGeometry
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

@[expose] public section

open MeasureTheory Set TopologicalSpace
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ContDiff

noncomputable section

namespace SubdiffusiveProcess

variable {d : ℕ}

/-- **`Λ_{N,q}(b)`**, the boundary response of `eq:mfd-2`
(`eq:mfd-2` and `mfd:lem-extension`, Lemma `mfd:lem-extension`):
the infimum of the energy over the zero-trace-difference class of the datum
carrier `beta` on the cell `W`.

This is the set whose `sInf` the frozen mesh target
 already names
verbatim in its cell clauses; nothing beyond `eq:mfd-2` is introduced. -/
def cellDirichletInfimum (a : SpatialCoordinates d → ℝ)
    (W : Set (SpatialCoordinates d)) (beta : H1Function W) : ℝ :=
  sInf {e : ℝ | ∃ u : H1Function W,
    HasZeroTraceDifferenceOn W u beta ∧ e = energy a W u}

/-- The rescaled boundary datum `g(z + r·)` of `eq:mfd-2`. -/
def rescaledDatum (z : SpatialCoordinates d) (r : ℝ)
    (g : SpatialCoordinates d → ℝ) : SpatialCoordinates d → ℝ :=
  fun y => g (fun i => z i + r * y i)

/-- The `C^β(S)/ℝ` QUOTIENT seminorm of `eq:mfd-2`: the infimum over additive
constants of the `C^β` norm `SubdiffusiveProcess.EllipticRegularity.cAlphaNorm` (`SubdiffusiveProcess/EllipticRegularity/Carriers.lean`), itself
built on `SubdiffusiveProcess.EllipticRegularity.holderSeminorm`. -/
def quotientCBetaNorm (beta : ℝ) (S : Set (SpatialCoordinates d))
    (g : SpatialCoordinates d → ℝ) : ℝ :=
  sInf {v : ℝ | ∃ c : ℝ, v = _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta S (fun x => g x - c)}

/-- The boundary class of a cell: the datum lives on the frontier, and its size
is the `C^β/ℝ` quotient seminorm of the rescaled datum on the frontier of the
unit cube, exactly as `eq:mfd-2` measures it. -/
def cellBoundaryQuotientNorm (beta : ℝ) (z : SpatialCoordinates d) (r : ℝ)
    (g : SpatialCoordinates d → ℝ) : ℝ :=
  quotientCBetaNorm beta
    (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)))
    (rescaledDatum z r g)

/-- **The boundary class as a genuine Hölder class.**  `cellBoundaryQuotientNorm`
is built on `SubdiffusiveProcess.EllipticRegularity.cAlphaNorm`, hence on `SubdiffusiveProcess.EllipticRegularity.holderSeminorm = sSup
holderRatioSet`, and mathlib's `sSup` returns `0` on an unbounded set.  A datum
that is NOT `β`-Hölder therefore has quotient norm `0`, which makes any bound
with the norm on the right of `≤` refutable and any hypothesis with it on the
left vacuous.  Every consumer must carry this predicate: the rescaled datum has
a bounded Hölder ratio set and is bounded on the face, so the seminorm and the
supremum term are genuine suprema. -/
def IsCellBoundaryClass (beta : ℝ) (z : SpatialCoordinates d) (r : ℝ)
    (g : SpatialCoordinates d → ℝ) : Prop :=
  _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta
      (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d))) (rescaledDatum z r g) ∧
    BddAbove {v : ℝ | ∃ x ∈ (frontier (centeredCube (0 : SpatialCoordinates d) 1
      one_pos : Set (SpatialCoordinates d))), v = |rescaledDatum z r g x|}

end SubdiffusiveProcess
