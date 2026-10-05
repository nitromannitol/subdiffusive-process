module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingInductionChain
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingInductionCrossing
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingCrossingCertificate
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingInductionCertificateSharp

@[expose] public section

/-!
# The multiscale crossing law: the single remaining probabilistic input

`StoppingInductionCrossing.lean` proves the crossing estimate for a crossing
width `epsilon` that shrinks with the bracket, which the exterior row cannot
consume (its decay constant is proportional to `epsilon`).  What the row needs
is one `epsilon > 0` valid at every large bracket.  That statement is named
here once and for all, and the two consumers already available are derived
from it, so that the exterior conjunct of the whole-space resolvent estimates
owes exactly one Proposition.

`RepairedStoppingCrossingLaw` is the manuscript's multiscale crossing lemma (`s.fixed.coefficient`
and `mfd:sec-speed`)
transcribed on the fixed cell code.  It is a percolation statement: no union
bound over scales can prove it, because for a fixed `epsilon` a cell of side
`R / epsilon` occurs somewhere in the bracket ball with probability tending to
one.

## Source

* `s.fixed.coefficient` and `mfd:sec-speed`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d] {Omega : Type*} {base : ℤ} [MeasurableSpace Omega]

/-- **The multiscale crossing law at a fixed crossing width.**  This is the
uniform form: `epsilon` is a *parameter*, supplied before the measure, the
failure field, the base scale, the source and the radius, and only the
constants `C`, `theta` and the last bad bracket `k0` are chosen afterwards.
The exterior row consumes `epsilon` in its decay constant, so this quantifier
order — not the existential one below — is the one the v3 anchor
requires. -/
def RepairedStoppingCrossingLawAt (epsilon : ℝ) (mu : Measure Omega)
    (failure : TriadicCube d → Set Omega) (base : ℤ) (x0 : Vec d) (R : ℝ) :
    Prop :=
  ∃ (C theta : ENNReal) (k0 : ℕ),
    C ≠ ∞ ∧ theta < 1 ∧
      ∀ k, k0 ≤ k →
        mu (repairedStoppingShortCrossingCodeEvent failure base x0 R epsilon k)
          ≤ C * theta ^ k

/-- **The multiscale crossing law at a source ball.**  One fixed crossing width
`epsilon`, and a geometric bound on the fixed-code short-crossing events from
some bracket `k0` on.  This existential form is the weaker one: it lets
`epsilon` depend on everything, and is retained only because the two consumers
below are stated for it as well. -/
def RepairedStoppingCrossingLaw (mu : Measure Omega)
    (failure : TriadicCube d → Set Omega) (base : ℤ) (x0 : Vec d) (R : ℝ) :
    Prop :=
  ∃ (epsilon : ℝ) (C theta : ENNReal) (k0 : ℕ),
    0 < epsilon ∧ C ≠ ∞ ∧ theta < 1 ∧
      ∀ k, k0 ≤ k →
        mu (repairedStoppingShortCrossingCodeEvent failure base x0 R epsilon k)
          ≤ C * theta ^ k

omit [NeZero d] in
/-- The uniform law at a positive width implies the existential law. -/
theorem repairedStoppingCrossingLaw_of_at {epsilon : ℝ} (heps : 0 < epsilon)
    {mu : Measure Omega} {failure : TriadicCube d → Set Omega} {x0 : Vec d}
    {R : ℝ} (h : RepairedStoppingCrossingLawAt epsilon mu failure base x0 R) :
    RepairedStoppingCrossingLaw mu failure base x0 R := by
  obtain ⟨C, theta, k0, hC, htheta, hcross⟩ := h
  exact ⟨epsilon, C, theta, k0, heps, hC, htheta, hcross⟩

/-- **The uniform crossing law delivers the exterior row's crossing certificate
at its own width.**  The crossing width is the one handed in, so the exterior
row's decay constant is fixed by the same `epsilon`. -/
theorem ae_eventually_not_repairedStoppingShortCrossing_of_crossingLawAt
    {epsilon : ℝ} (mu : Measure Omega) (failure : TriadicCube d → Set Omega)
    (x0 : Vec d) {R : ℝ} (hR : 0 < R)
    (hlaw : RepairedStoppingCrossingLawAt epsilon mu failure base x0 R) :
    ∀ᵐ omega ∂mu,
      ∀ (hinitial : LocallyFinite fun P : StoppingBaseCube d base ↦
          cubeSet (triadicStoppingCandidate failure omega P))
        (hrepair : LocallyFinite fun P : StoppingRepairCube failure omega base ↦
          cubeSet P.1),
        ∃ K : ℕ, ∀ k, K ≤ k →
          ¬ RepairedStoppingShortCrossing
            (refinedStoppingSource hinitial hrepair x0 R)
            (refinedStoppingSource_nonempty hinitial hrepair x0 hR.le)
            x0 R epsilon k := by
  obtain ⟨C, theta, k0, hC, htheta, hcross⟩ := hlaw
  exact ae_eventually_not_repairedStoppingShortCrossing_of_codeEvent_geometric
    mu failure x0 hR k0 C theta hC htheta hcross

omit [NeZero d] in
/-- **The uniform crossing law delivers the `O_{Γ₁}` tail at its own width.** -/
theorem exists_ogammaLE_repairedStoppingFirstGoodBracket_of_crossingLawAt
    {epsilon : ℝ} (mu : Measure Omega) [IsProbabilityMeasure mu]
    (failure : TriadicCube d → Set Omega)
    (hfailure : ∀ Q, MeasurableSet (failure Q))
    (x0 : Vec d) (R : ℝ)
    (hlaw : RepairedStoppingCrossingLawAt epsilon mu failure base x0 R) :
    ∃ (k0 : ℕ) (scale : ℝ),
      SubdiffusiveProcess.OGammaLE mu 1 scale
        (fun omega ↦
          (repairedStoppingFirstGoodBracket
              failure base x0 R epsilon k0 omega : ℝ) * Real.log 3 -
            ((k0 : ℝ) + 1) * Real.log 3) := by
  obtain ⟨C, theta, k0, hC, htheta, hcross⟩ := hlaw
  exact ⟨k0, _,
    ogammaLE_repairedStoppingFirstGoodBracket_of_codeEvent_geometric
      failure hfailure x0 R epsilon k0 C theta hC htheta hcross⟩


/-! ## The law with explicit constants, and the target-scale `O_{Γ₁}` corollary

The exterior estimate needs the exterior row's `Rstar` clause at the **target** scale
`CSigma * delta ^ 2 * |log delta|`, which forces the crossing law's `C` and
`theta` to be explicit in the failure decay `q` rather than existentially
quantified.  This section names that form and derives the `O_{Γ₁}` statement at
the scale it actually produces, through the uncapped certificate of
`StoppingInductionCertificateSharp.lean` (the capped one in
`StoppingCrossingCertificate.lean` produces a scale bounded below by
`4 log 3 / log 2`, and so can never reach a target scale that tends to `0`). -/

/-- **The crossing law with explicit constants.**  Everything is a parameter:
the width, the prefactor, the ratio and the first good bracket.  This is the
form the `Rstar` clause consumes, because its `O_{Γ₁}` scale is then an
explicit function of `theta`. -/
def RepairedStoppingCrossingLawWith (epsilon : ℝ) (C theta : ENNReal) (k0 : ℕ)
    (mu : Measure Omega) (failure : TriadicCube d → Set Omega) (base : ℤ)
    (x0 : Vec d) (R : ℝ) : Prop :=
  ∀ k, k0 ≤ k →
    mu (repairedStoppingShortCrossingCodeEvent failure base x0 R epsilon k)
      ≤ C * theta ^ k

omit [NeZero d] in
/-- The explicit law implies the uniform-width existential law. -/
theorem repairedStoppingCrossingLawAt_of_with {epsilon : ℝ} {C theta : ENNReal}
    {k0 : ℕ} {mu : Measure Omega} {failure : TriadicCube d → Set Omega}
    {x0 : Vec d} {R : ℝ} (hC : C ≠ ∞) (htheta : theta < 1)
    (h : RepairedStoppingCrossingLawWith epsilon C theta k0 mu failure base x0 R) :
    RepairedStoppingCrossingLawAt epsilon mu failure base x0 R :=
  ⟨C, theta, k0, hC, htheta, h⟩

omit [NeZero d] in
/-- **The target-scale `O_{Γ₁}` corollary.**  From the explicit law with a
*positive* ratio, the first certified bracket is `O_{Γ₁}` at the scale
`log 3 * 4 * (1 + log K) / log (1 / theta)`, which tends to `0` with `theta`.
The route (B′) analysis fixes `theta` by `3 ^ (3 d) * q ≤ theta ^ 2`, so with
`q = 3 ^ (-kappa)` the rate `log (1 / theta)` is `⌊(kappa - 3 d)/2⌋ * log 3`,
linear in the free envelope exponent. -/
theorem ogammaLE_repairedStoppingFirstGoodBracket_of_crossingLawWith
    {epsilon : ℝ} {C theta : ENNReal} {k0 : ℕ} (mu : Measure Omega)
    [IsProbabilityMeasure mu] (failure : TriadicCube d → Set Omega)
    (hfailure : ∀ Q, MeasurableSet (failure Q))
    (x0 : Vec d) (R : ℝ) (hC : C ≠ ∞) (h0 : 0 < theta) (htheta : theta < 1)
    (h : RepairedStoppingCrossingLawWith epsilon C theta k0 mu failure base x0 R) :
    SubdiffusiveProcess.OGammaLE mu 1
      (Real.log 3 * depthGammaOneScaleSharp
        (stoppingSharpCertificatePrefactor C theta k0)
        (stoppingSharpCertificateRate theta))
      (fun omega ↦
        (repairedStoppingFirstGoodBracket
            failure base x0 R epsilon k0 omega : ℝ) * Real.log 3 -
          ((k0 : ℝ) + 1) * Real.log 3) :=
  ogammaLE_repairedStoppingFirstGoodBracket_of_codeEvent_geometric_sharp
    failure hfailure x0 R epsilon k0 C theta hC h0 htheta h

/-- The explicit law delivers the exterior row's crossing certificate at its own
width. -/
theorem ae_eventually_not_repairedStoppingShortCrossing_of_crossingLawWith
    {epsilon : ℝ} {C theta : ENNReal} {k0 : ℕ} (mu : Measure Omega)
    (failure : TriadicCube d → Set Omega) (x0 : Vec d) {R : ℝ} (hR : 0 < R)
    (hC : C ≠ ∞) (htheta : theta < 1)
    (h : RepairedStoppingCrossingLawWith epsilon C theta k0 mu failure base x0 R) :
    ∀ᵐ omega ∂mu,
      ∀ (hinitial : LocallyFinite fun P : StoppingBaseCube d base ↦
          cubeSet (triadicStoppingCandidate failure omega P))
        (hrepair : LocallyFinite fun P : StoppingRepairCube failure omega base ↦
          cubeSet P.1),
        ∃ K : ℕ, ∀ k, K ≤ k →
          ¬ RepairedStoppingShortCrossing
            (refinedStoppingSource hinitial hrepair x0 R)
            (refinedStoppingSource_nonempty hinitial hrepair x0 hR.le)
            x0 R epsilon k :=
  ae_eventually_not_repairedStoppingShortCrossing_of_codeEvent_geometric
    mu failure x0 hR k0 C theta hC htheta h

/-- **The crossing law delivers the exterior row's crossing certificate.**
For a.e. sample, and for every pair of local-finiteness certificates, there is
a last bad bracket beyond which no short crossing of the fixed width occurs. -/
theorem ae_eventually_not_repairedStoppingShortCrossing_of_crossingLaw
    (mu : Measure Omega) (failure : TriadicCube d → Set Omega)
    (x0 : Vec d) {R : ℝ} (hR : 0 < R)
    (hlaw : RepairedStoppingCrossingLaw mu failure base x0 R) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ᵐ omega ∂mu,
        ∀ (hinitial : LocallyFinite fun P : StoppingBaseCube d base ↦
            cubeSet (triadicStoppingCandidate failure omega P))
          (hrepair : LocallyFinite fun P : StoppingRepairCube failure omega base ↦
            cubeSet P.1),
          ∃ K : ℕ, ∀ k, K ≤ k →
            ¬ RepairedStoppingShortCrossing
              (refinedStoppingSource hinitial hrepair x0 R)
              (refinedStoppingSource_nonempty hinitial hrepair x0 hR.le)
              x0 R epsilon k := by
  obtain ⟨epsilon, C, theta, k0, heps, hC, htheta, hcross⟩ := hlaw
  exact ⟨epsilon, heps,
    ae_eventually_not_repairedStoppingShortCrossing_of_codeEvent_geometric
      mu failure x0 hR k0 C theta hC htheta hcross⟩

omit [NeZero d] in
/-- **The crossing law delivers the `O_{Γ₁}` tail of the certified bracket**,
on the measurable observable `repairedStoppingFirstGoodBracket`, which is the
random radius `Rstar = 3 ^ Kbr * R` of the exterior row. -/
theorem exists_ogammaLE_repairedStoppingFirstGoodBracket_of_crossingLaw
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (failure : TriadicCube d → Set Omega)
    (hfailure : ∀ Q, MeasurableSet (failure Q))
    (x0 : Vec d) (R : ℝ)
    (hlaw : RepairedStoppingCrossingLaw mu failure base x0 R) :
    ∃ (epsilon : ℝ) (k0 : ℕ) (scale : ℝ), 0 < epsilon ∧
      SubdiffusiveProcess.OGammaLE mu 1 scale
        (fun omega ↦
          (repairedStoppingFirstGoodBracket
              failure base x0 R epsilon k0 omega : ℝ) * Real.log 3 -
            ((k0 : ℝ) + 1) * Real.log 3) := by
  obtain ⟨epsilon, C, theta, k0, heps, hC, htheta, hcross⟩ := hlaw
  exact ⟨epsilon, k0, _, heps,
    ogammaLE_repairedStoppingFirstGoodBracket_of_codeEvent_geometric
      failure hfailure x0 R epsilon k0 C theta hC htheta hcross⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
