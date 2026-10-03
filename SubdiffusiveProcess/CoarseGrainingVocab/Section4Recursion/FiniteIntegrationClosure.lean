module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.FullBlockDilationReadout
public import Homogenization.Deterministic.WeakNormInterfaces.Localization

@[expose] public section

/-!
# Finite integration closure for the Section 4 recursion

This module integrates the coordinate two-plus-eight estimate from
`FullBlockDilationReadout.lean`.  The proof route mirrors
`Algsuperdiff/Section3/Provider/Homogenization/VarianceClosure.lean` and
`FiniteRecurrence.lean`: separate colored variance from the annealed mean,
bound the response trace by its coordinate second moments, and only then
perform the finite corridor convolution.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov
open scoped BigOperators

noncomputable section


private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-! ## Finite-average integration -/

/-- At natural scales, the geometric descendant average is the normalized
finite average used by the probability layer. -/
theorem descendantsAverage_eq_probabilityFinsetAverage_of_le
    {d L n : ℕ} (hLn : L ≤ n)
    (X : TriadicCube d → Sample d → ℝ) :
    (fun omega => descendantsAverage (originCube d (n : ℤ)) (n - L)
      (fun R => X R omega)) =
      probabilityFinsetAverage
        (descendantsAtScale (originCube d (n : ℤ)) (L : ℤ)) X := by
  funext omega
  have hscale : (L : ℤ) ≤ (originCube d (n : ℤ)).scale := by
    change (L : ℤ) ≤ (n : ℤ)
    exact_mod_cast hLn
  rw [descendantsAtScale_eq_descendantsAtDepth (originCube d (n : ℤ)) hscale]
  have hdepth : ((n : ℤ) - (L : ℤ)).toNat = n - L := by omega
  simp only [probabilityFinsetAverage, descendantsAverage]
  rw [show ((originCube d (n : ℤ)).scale - (L : ℤ)).toNat = n - L by
    change ((n : ℤ) - (L : ℤ)).toNat = n - L
    exact hdepth]

/-- Finite descendant averages preserve `L²` on an arbitrary probability
carrier. -/
theorem memLp_two_descendantsAverage
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    {X : TriadicCube d → Sample d → ℝ}
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d}
    (hX : ∀ R ∈ descendantsAtDepth Q j, MemLp (X R) 2 M.P.toMeasure) :
    MemLp (fun omega => descendantsAverage Q j (fun R => X R omega))
      2 M.P.toMeasure := by
  let D := descendantsAtDepth Q j
  simpa only [descendantsAverage, D, Finset.sum_apply] using
    (memLp_finset_sum' D (fun R hR => hX R hR)).const_mul ((D.card : ℝ)⁻¹)

/-- Finite descendant averages commute with integration on the literal sample
space. -/
theorem integral_descendantsAverage_sample_eq
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    {X : TriadicCube d → Sample d → ℝ}
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d}
    (hX : ∀ R ∈ descendantsAtDepth Q j, Integrable (X R) M.P.toMeasure) :
    ∫ omega, descendantsAverage Q j (fun R => X R omega) ∂M.P.toMeasure =
      descendantsAverage Q j (fun R => ∫ omega, X R omega ∂M.P.toMeasure) := by
  let D := descendantsAtDepth Q j
  simp only [descendantsAverage, integral_const_mul]
  rw [integral_finset_sum]
  intro R hR
  exact hX R hR

/-- Jensen plus finite integration: a uniform cellwise second-moment budget
also bounds the second moment of the descendant average. -/
theorem integral_descendantsAverage_sq_le_of_secondMoment
    {d : ℕ} {Q : TriadicCube d} {j : ℕ}
    {X : TriadicCube d → Sample d → ℝ}
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {B : ℝ}
    (hX : ∀ R ∈ descendantsAtDepth Q j, MemLp (X R) 2 M.P.toMeasure)
    (hsecond : ∀ R ∈ descendantsAtDepth Q j,
      ∫ omega, (X R omega) ^ 2 ∂M.P.toMeasure ≤ B) :
    ∫ omega, (descendantsAverage Q j (fun R => X R omega)) ^ 2
        ∂M.P.toMeasure ≤ B := by
  have havg : MemLp (fun omega => descendantsAverage Q j (fun R => X R omega))
      2 M.P.toMeasure := memLp_two_descendantsAverage hX
  have hleft : Integrable (fun omega =>
      (descendantsAverage Q j (fun R => X R omega)) ^ 2) M.P.toMeasure :=
    (memLp_two_iff_integrable_sq havg.aestronglyMeasurable).1 havg
  have hcell : ∀ R ∈ descendantsAtDepth Q j,
      Integrable (fun omega => (X R omega) ^ 2) M.P.toMeasure := by
    intro R hR
    exact (memLp_two_iff_integrable_sq (hX R hR).aestronglyMeasurable).1 (hX R hR)
  have hright : Integrable (fun omega =>
      descendantsAverage Q j (fun R => (X R omega) ^ 2)) M.P.toMeasure := by
    let D := descendantsAtDepth Q j
    have hsum : Integrable (fun omega => ∑ R ∈ D, (X R omega) ^ 2)
        M.P.toMeasure := by
      exact integrable_finset_sum D (fun R hR => hcell R (by simpa [D] using hR))
    simpa only [descendantsAverage, D] using hsum.const_mul ((D.card : ℝ)⁻¹)
  calc
    ∫ omega, (descendantsAverage Q j (fun R => X R omega)) ^ 2 ∂M.P.toMeasure ≤
        ∫ omega, descendantsAverage Q j (fun R => (X R omega) ^ 2)
          ∂M.P.toMeasure := by
      exact integral_mono hleft hright fun omega =>
        descendantsAverage_sq_le_descendantsAverage_sq Q j (fun R => X R omega)
    _ = descendantsAverage Q j
          (fun R => ∫ omega, (X R omega) ^ 2 ∂M.P.toMeasure) :=
      integral_descendantsAverage_sample_eq hcell
    _ ≤ descendantsAverage Q j (fun _R => B) :=
      descendantsAverage_le_descendantsAverage Q j hsecond
    _ = B := descendantsAverage_const_eq Q j B

/-! ## Annealed means of descendant dual entries -/

/-- The expectation of a descendant inverse-star average centered at the
scale-`n` annealed matrix is the scale-`L`/scale-`n` annealed mean gap. -/
theorem integral_descendantsAverage_centered_randomAStarInv_entry_eq
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n : ℕ) (hLn : L ≤ n)
    (i j : Fin d) :
    ∫ omega : Sample d,
        descendantsAverage (originCube d (n : ℤ)) (n - L)
          (fun R =>
            (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j -
              abarStarInv M L
                (Ch02.cubeDomain (originCube d (n : ℤ))) i j)
        ∂M.P.toMeasure =
      abarStarInv M L (Ch02.cubeDomain (originCube d (L : ℤ))) i j -
        abarStarInv M L (Ch02.cubeDomain (originCube d (n : ℤ))) i j := by
  let Q := originCube d (n : ℤ)
  let b := abarStarInv M L (Ch02.cubeDomain Q) i j
  let X : TriadicCube d → Sample d → ℝ := fun R omega =>
    (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j - b
  have hscale : (L : ℤ) ≤ Q.scale := by
    change (L : ℤ) ≤ (n : ℤ)
    exact_mod_cast hLn
  have hdepth : descendantsAtDepth Q (n - L) = descendantsAtScale Q (L : ℤ) := by
    change descendantsAtDepth (originCube d (n : ℤ)) (n - L) =
      descendantsAtScale (originCube d (n : ℤ)) (L : ℤ)
    rw [descendantsAtScale_eq_descendantsAtDepth Q hscale]
    congr 1
    change n - L = ((n : ℤ) - (L : ℤ)).toNat
    omega
  have hXint : ∀ R ∈ descendantsAtDepth Q (n - L),
      Integrable (X R) M.P.toMeasure := by
    intro R _hR
    exact (((integrable_randomAStarMatrix_inv M L (Ch02.cubeDomain R)).eval i).eval j).sub
      (integrable_const _)
  rw [integral_descendantsAverage_sample_eq hXint]
  have hterm : ∀ R ∈ descendantsAtDepth Q (n - L),
      ∫ omega, X R omega ∂M.P.toMeasure =
        abarStarInv M L (Ch02.cubeDomain (originCube d (L : ℤ))) i j - b := by
    intro R hR
    have hRscale : R.scale = (L : ℤ) := by
      apply scale_eq_of_mem_descendantsAtScale
      rw [← hdepth]
      exact hR
    dsimp only [X, b, Q]
    rw [integral_sub, integral_const]
    · rw [integral_randomAStarInv_entry_cube_eq_originCube M L R i j, hRscale]
      simp only [probReal_univ, one_smul]
      rw [← integral_matrix_apply
        (integrable_randomAStarMatrix_inv M L
          (Ch02.cubeDomain (originCube d (L : ℤ)))) i j]
      rfl
    · exact (((integrable_randomAStarMatrix_inv M L (Ch02.cubeDomain R)).eval i).eval j)
    · exact integrable_const _
  calc
    descendantsAverage Q (n - L)
        (fun R => ∫ omega, X R omega ∂M.P.toMeasure) =
        descendantsAverage Q (n - L)
          (fun _R => abarStarInv M L
            (Ch02.cubeDomain (originCube d (L : ℤ))) i j - b) := by
      apply le_antisymm
      · apply descendantsAverage_le_descendantsAverage
        intro R hR
        exact (hterm R hR).le
      · apply descendantsAverage_le_descendantsAverage
        intro R hR
        exact (hterm R hR).ge
    _ = abarStarInv M L (Ch02.cubeDomain (originCube d (L : ℤ))) i j - b :=
      descendantsAverage_const_eq Q (n - L) _
    _ = _ := rfl

/-- The annealed mean of any inverse-star entry changes by at most the two
diagonal mean-defect budgets.  Off-diagonal entries vanish by isotropy. -/
theorem sq_abarStarInv_originCube_sub_le
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m0 L n : ℕ}
    {xi delta1 : ℝ}
    (hS : inductionHypothesis M m0 xi delta1) (hLm0 : L ≤ m0)
    (hLn : L ≤ n) (i j : Fin d) :
    (abarStarInv M L (Ch02.cubeDomain (originCube d (L : ℤ))) i j -
      abarStarInv M L (Ch02.cubeDomain (originCube d (n : ℤ))) i j) ^ 2 ≤
      16 * (ahom M L)⁻¹ ^ 2 * delta1 ^ 2 := by
  by_cases hij : i = j
  · subst j
    have hL := sq_abs_abarStarInv_entry_sub_ahom_inv_le_of_inductionHypothesis
      M hS hLm0 le_rfl i
    have hn := sq_abs_abarStarInv_entry_sub_ahom_inv_le_of_inductionHypothesis
      M hS hLm0 hLn i
    rw [sq_abs] at hL hn
    have haux := sq_nonneg
      ((abarStarInv M L (Ch02.cubeDomain (originCube d (L : ℤ))) i i -
          (ahom M L)⁻¹) +
        (abarStarInv M L (Ch02.cubeDomain (originCube d (n : ℤ))) i i -
          (ahom M L)⁻¹))
    nlinarith
  · rw [abarStarInv_originCube_offdiag_eq_zero M L L i j hij,
      abarStarInv_originCube_offdiag_eq_zero M L n i j hij]
    norm_num
    positivity

/-- The uncentered squared descendant dual average splits into its colored
variance and its annealed mean gap. -/
theorem integral_descendantsAverage_centered_randomAStarInv_entry_sq_le
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m0 L n : ℕ}
    {xi delta1 : ℝ} (hxi : 2 ≤ xi)
    (hS : inductionHypothesis M m0 xi delta1) (hLm0 : L ≤ m0)
    (hLn : L ≤ n) (i j : Fin d) :
    ∫ omega : Sample d,
        (descendantsAverage (originCube d (n : ℤ)) (n - L)
          (fun R =>
            (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j -
              abarStarInv M L
                (Ch02.cubeDomain (originCube d (n : ℤ))) i j)) ^ 2
        ∂M.P.toMeasure ≤
      ((freshShellColorPeriod d ^ d : ℕ) : ℝ) *
          Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ)) *
            (48 * (ahom M L)⁻¹ ^ 2 * delta1) +
        16 * (ahom M L)⁻¹ ^ 2 * delta1 ^ 2 := by
  let X : TriadicCube d → Sample d → ℝ := fun R omega =>
    (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j -
      abarStarInv M L (Ch02.cubeDomain (originCube d (n : ℤ))) i j
  let A : Sample d → ℝ := fun omega =>
    descendantsAverage (originCube d (n : ℤ)) (n - L) (fun R => X R omega)
  have hscale : (L : ℤ) ≤ (originCube d (n : ℤ)).scale := by
    change (L : ℤ) ≤ (n : ℤ)
    exact_mod_cast hLn
  have hXLp : ∀ R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - L),
      MemLp (X R) 2 M.P.toMeasure := by
    intro R _hR
    have hrawMeas : AEStronglyMeasurable (fun omega : Sample d =>
        (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j)
        M.P.toMeasure :=
      ((((integrable_randomAStarMatrix_inv M L (Ch02.cubeDomain R)).eval i).eval j).1)
    have hraw : MemLp (fun omega : Sample d =>
        (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j)
        2 M.P.toMeasure :=
      (memLp_two_iff_integrable_sq hrawMeas).2
        (integrable_randomAStarInv_entry_sq M L (Ch02.cubeDomain R) i j)
    exact hraw.sub (memLp_const _)
  have hALp : MemLp A 2 M.P.toMeasure := by
    simpa only [A] using memLp_two_descendantsAverage hXLp
  have hvar : variance A M.P.toMeasure ≤
      ((freshShellColorPeriod d ^ d : ℕ) : ℝ) *
        Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ)) *
          (48 * (ahom M L)⁻¹ ^ 2 * delta1) := by
    have hbase := variance_descendantAverage_centered_randomAStarInv_entry_le
      M hxi hS hLm0 hLn i j
    dsimp only at hbase
    change variance (probabilityFinsetAverage
      (descendantsAtScale (originCube d (n : ℤ)) (L : ℤ)) X)
        M.P.toMeasure ≤ _ at hbase
    rw [← descendantsAverage_eq_probabilityFinsetAverage_of_le hLn X] at hbase
    exact hbase
  have hmean : ∫ omega, A omega ∂M.P.toMeasure =
      abarStarInv M L (Ch02.cubeDomain (originCube d (L : ℤ))) i j -
        abarStarInv M L (Ch02.cubeDomain (originCube d (n : ℤ))) i j := by
    simpa only [A, X] using
      integral_descendantsAverage_centered_randomAStarInv_entry_eq M L n hLn i j
  have hmeanSq := sq_abarStarInv_originCube_sub_le M hS hLm0 hLn i j
  have hvarEq := variance_eq_sub hALp
  simp only [Pi.pow_apply] at hvarEq
  have hsecondEq : ∫ omega, (A omega) ^ 2 ∂M.P.toMeasure =
      variance A M.P.toMeasure + (∫ omega, A omega ∂M.P.toMeasure) ^ 2 := by
    linarith
  change ∫ omega, (A omega) ^ 2 ∂M.P.toMeasure ≤ _
  rw [hsecondEq, hmean]
  exact add_le_add hvar hmeanSq

/-! ## Coordinate-response trace -/

/-- The square of the coordinate-response trace on one scale-`L` cube is
bounded by the sum of the landed coordinate second moments. -/
theorem integral_coordinateLocalResponseTrace_sq_le
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m0 L : ℕ}
    {xi delta1 : ℝ} (hxi : 2 ≤ xi)
    (hS : inductionHypothesis M m0 xi delta1) (hLm0 : L ≤ m0)
    (R : TriadicCube d) (hR : R.scale = (L : ℤ)) :
    ∫ omega : Sample d,
        (∑ u : Fin d, cutoffResponseOnCube M L
          ((ahom M L)⁻¹ • Pi.single u 1) (Pi.single u 1) R omega) ^ 2
        ∂M.P.toMeasure ≤
      (d : ℝ) ^ 2 * ((ahom M L)⁻¹ ^ 2 * delta1 ^ 2) := by
  let Y : Fin d → Sample d → ℝ := fun u omega =>
    cutoffResponseOnCube M L
      ((ahom M L)⁻¹ • Pi.single u 1) (Pi.single u 1) R omega
  have hYLp : ∀ u : Fin d, MemLp (Y u) 2 M.P.toMeasure := by
    intro u
    simpa only [Y] using coordinateLocalResponse_memLp_two M hxi hS hLm0 R hR u
  have hYsq : ∀ u : Fin d,
      Integrable (fun omega => (Y u omega) ^ 2) M.P.toMeasure := by
    intro u
    exact (memLp_two_iff_integrable_sq (hYLp u).aestronglyMeasurable).1 (hYLp u)
  have hsumLp : MemLp (fun omega => ∑ u : Fin d, Y u omega) 2 M.P.toMeasure := by
    have hfun : (fun omega => ∑ u : Fin d, Y u omega) = ∑ u : Fin d, Y u := by
      funext omega
      simp
    rw [hfun]
    exact memLp_finset_sum' Finset.univ (fun u _hu => hYLp u)
  have hleft : Integrable (fun omega => (∑ u : Fin d, Y u omega) ^ 2)
      M.P.toMeasure :=
    (memLp_two_iff_integrable_sq hsumLp.aestronglyMeasurable).1 hsumLp
  have hsumSq : Integrable (fun omega => ∑ u : Fin d, (Y u omega) ^ 2)
      M.P.toMeasure := integrable_finset_sum Finset.univ (fun u _hu => hYsq u)
  have hright : Integrable
      (fun omega => (d : ℝ) * ∑ u : Fin d, (Y u omega) ^ 2) M.P.toMeasure :=
    hsumSq.const_mul _
  have hpoint : ∀ omega,
      (∑ u : Fin d, Y u omega) ^ 2 ≤
        (d : ℝ) * ∑ u : Fin d, (Y u omega) ^ 2 := by
    intro omega
    simpa using
      (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
        (f := fun u => Y u omega))
  have hcoord : ∀ u : Fin d,
      ∫ omega, (Y u omega) ^ 2 ∂M.P.toMeasure ≤
        (ahom M L)⁻¹ ^ 2 * delta1 ^ 2 := by
    intro u
    simpa only [Y] using
      (coordinateLocalResponse_sq_integrable_and_integral_le
        M hxi hS hLm0 R hR u).2
  change ∫ omega, (∑ u : Fin d, Y u omega) ^ 2 ∂M.P.toMeasure ≤ _
  calc
    ∫ omega, (∑ u : Fin d, Y u omega) ^ 2 ∂M.P.toMeasure ≤
        ∫ omega, (d : ℝ) * ∑ u : Fin d, (Y u omega) ^ 2
          ∂M.P.toMeasure := integral_mono hleft hright hpoint
    _ = (d : ℝ) * ∑ u : Fin d,
          ∫ omega, (Y u omega) ^ 2 ∂M.P.toMeasure := by
      rw [integral_const_mul, integral_finset_sum]
      intro u _hu
      exact hYsq u
    _ ≤ (d : ℝ) * ∑ _u : Fin d,
          ((ahom M L)⁻¹ ^ 2 * delta1 ^ 2) := by
      gcongr with u
      exact hcoord u
    _ = (d : ℝ) ^ 2 * ((ahom M L)⁻¹ ^ 2 * delta1 ^ 2) := by
      simp
      ring

/-- Jensen transports the coordinate-response trace budget from one cell to
the finite descendant average appearing in the two-plus-eight estimate. -/
theorem integral_descendantsAverage_coordinateLocalResponseTrace_sq_le
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m0 L n : ℕ}
    {xi delta1 : ℝ} (hxi : 2 ≤ xi)
    (hS : inductionHypothesis M m0 xi delta1) (hLm0 : L ≤ m0)
    (hLn : L ≤ n) :
    ∫ omega : Sample d,
        (descendantsAverage (originCube d (n : ℤ)) (n - L)
          (fun R => ∑ u : Fin d, cutoffResponseOnCube M L
            ((ahom M L)⁻¹ • Pi.single u 1) (Pi.single u 1) R omega)) ^ 2
        ∂M.P.toMeasure ≤
      (d : ℝ) ^ 2 * ((ahom M L)⁻¹ ^ 2 * delta1 ^ 2) := by
  let X : TriadicCube d → Sample d → ℝ := fun R omega =>
    ∑ u : Fin d, cutoffResponseOnCube M L
      ((ahom M L)⁻¹ • Pi.single u 1) (Pi.single u 1) R omega
  have hscale : (L : ℤ) ≤ (originCube d (n : ℤ)).scale := by
    change (L : ℤ) ≤ (n : ℤ)
    exact_mod_cast hLn
  apply integral_descendantsAverage_sq_le_of_secondMoment
  · intro R hR
    have hRscale : R.scale = (L : ℤ) := by
      apply scale_eq_of_mem_descendantsAtScale
      rw [descendantsAtScale_eq_descendantsAtDepth
        (originCube d (n : ℤ)) hscale]
      have hdepth : ((originCube d (n : ℤ)).scale - (L : ℤ)).toNat = n - L := by
        change ((n : ℤ) - (L : ℤ)).toNat = n - L
        omega
      simpa only [hdepth] using hR
    have hfun : (fun omega => ∑ u : Fin d, cutoffResponseOnCube M L
        ((ahom M L)⁻¹ • Pi.single u 1) (Pi.single u 1) R omega) =
        ∑ u : Fin d, cutoffResponseOnCube M L
          ((ahom M L)⁻¹ • Pi.single u 1) (Pi.single u 1) R := by
      funext omega
      simp
    rw [hfun]
    exact memLp_finset_sum' Finset.univ (fun u _hu =>
      coordinateLocalResponse_memLp_two M hxi hS hLm0 R hRscale u)
  · intro R hR
    have hRscale : R.scale = (L : ℤ) := by
      apply scale_eq_of_mem_descendantsAtScale
      rw [descendantsAtScale_eq_descendantsAtDepth
        (originCube d (n : ℤ)) hscale]
      have hdepth : ((originCube d (n : ℤ)).scale - (L : ℤ)).toNat = n - L := by
        change ((n : ℤ) - (L : ℤ)).toNat = n - L
        omega
      simpa only [hdepth] using hR
    simpa only [X] using
      integral_coordinateLocalResponseTrace_sq_le M hxi hS hLm0 R hRscale

/-! ## Integrated two-plus-eight estimate -/

/-- Integrating the a.e. coordinate two-plus-eight inequality gives the
explicit colored-variance, annealed-gap, and coordinate-trace budgets. -/
theorem integral_centered_randomAStarInv_entry_sq_le_two_plus_eight
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m0 L n : ℕ}
    {xi delta1 : ℝ} (hxi : 2 ≤ xi)
    (hS : inductionHypothesis M m0 xi delta1) (hLm0 : L ≤ m0)
    (hLn : L ≤ n) (i j : Fin d) :
    ∫ omega : Sample d,
        ((randomAStarMatrix M L
            (Ch02.cubeDomain (originCube d (n : ℤ))) omega)⁻¹ i j -
          abarStarInv M L
            (Ch02.cubeDomain (originCube d (n : ℤ))) i j) ^ 2
        ∂M.P.toMeasure ≤
      2 * (d : ℝ) ^ 2 *
        (((freshShellColorPeriod d ^ d : ℕ) : ℝ) *
            Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ)) *
              (48 * (ahom M L)⁻¹ ^ 2 * delta1) +
          16 * (ahom M L)⁻¹ ^ 2 * delta1 ^ 2) +
        8 * ((d : ℝ) ^ 2 * ((ahom M L)⁻¹ ^ 2 * delta1 ^ 2)) := by
  let Dual : Fin d → Fin d → Sample d → ℝ := fun u v omega =>
    descendantsAverage (originCube d (n : ℤ)) (n - L)
      (fun R =>
        (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ u v -
          abarStarInv M L
            (Ch02.cubeDomain (originCube d (n : ℤ))) u v)
  let Trace : Sample d → ℝ := fun omega =>
    descendantsAverage (originCube d (n : ℤ)) (n - L)
      (fun R => ∑ u : Fin d, cutoffResponseOnCube M L
        ((ahom M L)⁻¹ • Pi.single u 1) (Pi.single u 1) R omega)
  let RHS : Sample d → ℝ := fun omega =>
    2 * ∑ u : Fin d, ∑ v : Fin d, (Dual u v omega) ^ 2 +
      8 * (Trace omega) ^ 2
  have hscale : (L : ℤ) ≤ (originCube d (n : ℤ)).scale := by
    change (L : ℤ) ≤ (n : ℤ)
    exact_mod_cast hLn
  have hDualLp : ∀ u v, MemLp (Dual u v) 2 M.P.toMeasure := by
    intro u v
    apply memLp_two_descendantsAverage
    intro R _hR
    have hrawMeas : AEStronglyMeasurable (fun omega : Sample d =>
        (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ u v)
        M.P.toMeasure :=
      ((((integrable_randomAStarMatrix_inv M L (Ch02.cubeDomain R)).eval u).eval v).1)
    have hraw : MemLp (fun omega : Sample d =>
        (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ u v)
        2 M.P.toMeasure :=
      (memLp_two_iff_integrable_sq hrawMeas).2
        (integrable_randomAStarInv_entry_sq M L (Ch02.cubeDomain R) u v)
    exact hraw.sub (memLp_const _)
  have hTraceLp : MemLp Trace 2 M.P.toMeasure := by
    apply memLp_two_descendantsAverage
    intro R hR
    have hRscale : R.scale = (L : ℤ) := by
      apply scale_eq_of_mem_descendantsAtScale
      rw [descendantsAtScale_eq_descendantsAtDepth
        (originCube d (n : ℤ)) hscale]
      have hdepth : ((originCube d (n : ℤ)).scale - (L : ℤ)).toNat = n - L := by
        change ((n : ℤ) - (L : ℤ)).toNat = n - L
        omega
      simpa only [hdepth] using hR
    have hfun : (fun omega => ∑ u : Fin d, cutoffResponseOnCube M L
        ((ahom M L)⁻¹ • Pi.single u 1) (Pi.single u 1) R omega) =
        ∑ u : Fin d, cutoffResponseOnCube M L
          ((ahom M L)⁻¹ • Pi.single u 1) (Pi.single u 1) R := by
      funext omega
      simp
    rw [hfun]
    exact memLp_finset_sum' Finset.univ (fun u _hu =>
      coordinateLocalResponse_memLp_two M hxi hS hLm0 R hRscale u)
  have hDualSqInt : ∀ u v,
      Integrable (fun omega => (Dual u v omega) ^ 2) M.P.toMeasure := by
    intro u v
    exact (memLp_two_iff_integrable_sq (hDualLp u v).aestronglyMeasurable).1
      (hDualLp u v)
  have hTraceSqInt : Integrable (fun omega => (Trace omega) ^ 2) M.P.toMeasure :=
    (memLp_two_iff_integrable_sq hTraceLp.aestronglyMeasurable).1 hTraceLp
  have hDualSumInt : Integrable
      (fun omega => ∑ u : Fin d, ∑ v : Fin d, (Dual u v omega) ^ 2)
      M.P.toMeasure :=
    integrable_finset_sum Finset.univ (fun u _hu =>
      integrable_finset_sum Finset.univ (fun v _hv => hDualSqInt u v))
  have hRHSInt : Integrable RHS M.P.toMeasure :=
    (hDualSumInt.const_mul 2).add (hTraceSqInt.const_mul 8)
  have hpoint := centered_randomAStarInv_entry_sq_le_two_descendantAverage_add_eight_trace_ae
    M L n i j
  have hmono :
      ∫ omega : Sample d,
          ((randomAStarMatrix M L
              (Ch02.cubeDomain (originCube d (n : ℤ))) omega)⁻¹ i j -
            abarStarInv M L
              (Ch02.cubeDomain (originCube d (n : ℤ))) i j) ^ 2
          ∂M.P.toMeasure ≤ ∫ omega, RHS omega ∂M.P.toMeasure := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun _omega => sq_nonneg _
    · exact hRHSInt
    · simpa only [RHS, Dual, Trace] using hpoint
  have hDualBound : ∀ u v,
      ∫ omega, (Dual u v omega) ^ 2 ∂M.P.toMeasure ≤
        ((freshShellColorPeriod d ^ d : ℕ) : ℝ) *
            Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ)) *
              (48 * (ahom M L)⁻¹ ^ 2 * delta1) +
          16 * (ahom M L)⁻¹ ^ 2 * delta1 ^ 2 := by
    intro u v
    simpa only [Dual] using
      integral_descendantsAverage_centered_randomAStarInv_entry_sq_le
        M hxi hS hLm0 hLn u v
  have hTraceBound : ∫ omega, (Trace omega) ^ 2 ∂M.P.toMeasure ≤
      (d : ℝ) ^ 2 * ((ahom M L)⁻¹ ^ 2 * delta1 ^ 2) := by
    simpa only [Trace] using
      integral_descendantsAverage_coordinateLocalResponseTrace_sq_le
        M hxi hS hLm0 hLn
  have hDualIntegralEq :
      ∫ omega, ∑ u : Fin d, ∑ v : Fin d, (Dual u v omega) ^ 2
          ∂M.P.toMeasure =
        ∑ u : Fin d, ∑ v : Fin d,
          ∫ omega, (Dual u v omega) ^ 2 ∂M.P.toMeasure := by
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro u _hu
      rw [integral_finset_sum]
      intro v _hv
      exact hDualSqInt u v
    · intro u _hu
      exact integrable_finset_sum Finset.univ (fun v _hv => hDualSqInt u v)
  have hRHSIntegral : ∫ omega, RHS omega ∂M.P.toMeasure =
      2 * ∑ u : Fin d, ∑ v : Fin d,
          ∫ omega, (Dual u v omega) ^ 2 ∂M.P.toMeasure +
        8 * ∫ omega, (Trace omega) ^ 2 ∂M.P.toMeasure := by
    dsimp only [RHS]
    rw [integral_add (hDualSumInt.const_mul 2) (hTraceSqInt.const_mul 8),
      integral_const_mul, integral_const_mul, hDualIntegralEq]
  have hDualSumBound :
      2 * ∑ u : Fin d, ∑ v : Fin d,
          ∫ omega, (Dual u v omega) ^ 2 ∂M.P.toMeasure ≤
        2 * ∑ _u : Fin d, ∑ _v : Fin d,
          (((freshShellColorPeriod d ^ d : ℕ) : ℝ) *
              Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ)) *
                (48 * (ahom M L)⁻¹ ^ 2 * delta1) +
            16 * (ahom M L)⁻¹ ^ 2 * delta1 ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum
    intro u _hu
    apply Finset.sum_le_sum
    intro v _hv
    exact hDualBound u v
  calc
    ∫ omega : Sample d,
        ((randomAStarMatrix M L
            (Ch02.cubeDomain (originCube d (n : ℤ))) omega)⁻¹ i j -
          abarStarInv M L
            (Ch02.cubeDomain (originCube d (n : ℤ))) i j) ^ 2
        ∂M.P.toMeasure ≤ ∫ omega, RHS omega ∂M.P.toMeasure := hmono
    _ = 2 * ∑ u : Fin d, ∑ v : Fin d,
          ∫ omega, (Dual u v omega) ^ 2 ∂M.P.toMeasure +
        8 * ∫ omega, (Trace omega) ^ 2 ∂M.P.toMeasure := hRHSIntegral
    _ ≤ 2 * ∑ _u : Fin d, ∑ _v : Fin d,
          (((freshShellColorPeriod d ^ d : ℕ) : ℝ) *
              Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ)) *
                (48 * (ahom M L)⁻¹ ^ 2 * delta1) +
            16 * (ahom M L)⁻¹ ^ 2 * delta1 ^ 2) +
        8 * ((d : ℝ) ^ 2 * ((ahom M L)⁻¹ ^ 2 * delta1 ^ 2)) := by
      exact add_le_add hDualSumBound
        (mul_le_mul_of_nonneg_left hTraceBound (by norm_num))
    _ = _ := by
      simp
      ring



noncomputable def finiteIntegrationVarianceConstant (d : ℕ) : ℝ :=
  96 * (d : ℝ) ^ 2 * ((freshShellColorPeriod d ^ d : ℕ) : ℝ) +
    40 * (d : ℝ) ^ 2

/-- Compact accepted form of the integrated parent-entry estimate. -/
theorem integral_centered_randomAStarInv_entry_sq_le_accepted
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m0 L n : ℕ}
    {xi delta1 : ℝ} (hxi : 2 ≤ xi)
    (hS : inductionHypothesis M m0 xi delta1) (hLm0 : L ≤ m0)
    (hLn : L ≤ n) (i j : Fin d) :
    ∫ omega : Sample d,
        ((randomAStarMatrix M L
            (Ch02.cubeDomain (originCube d (n : ℤ))) omega)⁻¹ i j -
          abarStarInv M L
            (Ch02.cubeDomain (originCube d (n : ℤ))) i j) ^ 2
        ∂M.P.toMeasure ≤
      finiteIntegrationVarianceConstant d * (ahom M L)⁻¹ ^ 2 * delta1 *
        (delta1 + Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ))) := by
  have hraw := integral_centered_randomAStarInv_entry_sq_le_two_plus_eight
    M hxi hS hLm0 hLn i j
  let D : ℝ := (d : ℝ) ^ 2
  let K : ℝ := ((freshShellColorPeriod d ^ d : ℕ) : ℝ)
  let A : ℝ := (ahom M L)⁻¹ ^ 2
  let r : ℝ := Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ))
  have hD : 0 ≤ D := by positivity
  have hK : 0 ≤ K := by positivity
  have hA : 0 ≤ A := by positivity
  have hr : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hdelta : 0 ≤ delta1 := hS.2.1.le
  have hextra1 : 0 ≤ 96 * D * K * A * delta1 ^ 2 := by positivity
  have hextra2 : 0 ≤ 40 * D * A * delta1 * r := by positivity
  dsimp only [finiteIntegrationVarianceConstant, D, K, A, r] at hraw ⊢
  nlinarith

/-- Consequently the literal parent inverse-star entry has the same variance
bound. -/
theorem variance_randomAStarInv_entry_originCube_le_accepted
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m0 L n : ℕ}
    {xi delta1 : ℝ} (hxi : 2 ≤ xi)
    (hS : inductionHypothesis M m0 xi delta1) (hLm0 : L ≤ m0)
    (hLn : L ≤ n) (i j : Fin d) :
    variance (fun omega : Sample d =>
        (randomAStarMatrix M L
          (Ch02.cubeDomain (originCube d (n : ℤ))) omega)⁻¹ i j)
        M.P.toMeasure ≤
      finiteIntegrationVarianceConstant d * (ahom M L)⁻¹ ^ 2 * delta1 *
        (delta1 + Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ))) := by
  let X : Sample d → ℝ := fun omega =>
    (randomAStarMatrix M L
      (Ch02.cubeDomain (originCube d (n : ℤ))) omega)⁻¹ i j
  let b : ℝ := abarStarInv M L
    (Ch02.cubeDomain (originCube d (n : ℤ))) i j
  have hXmeas : AEStronglyMeasurable X M.P.toMeasure :=
    ((((integrable_randomAStarMatrix_inv M L
      (Ch02.cubeDomain (originCube d (n : ℤ)))).eval i).eval j).1)
  have hX : MemLp X 2 M.P.toMeasure :=
    (memLp_two_iff_integrable_sq hXmeas).2
      (integrable_randomAStarInv_entry_sq M L
        (Ch02.cubeDomain (originCube d (n : ℤ))) i j)
  have hmean : ∫ omega, X omega ∂M.P.toMeasure = b := by
    dsimp only [X, b]
    rw [← integral_matrix_apply
      (integrable_randomAStarMatrix_inv M L
        (Ch02.cubeDomain (originCube d (n : ℤ)))) i j]
    rfl
  rw [variance_eq_integral hX.aemeasurable, hmean]
  simpa only [X, b] using
    integral_centered_randomAStarInv_entry_sq_le_accepted
      M hxi hS hLm0 hLn i j

/-- The annealed inverse-star mean gap between any two corridor scales obeys
the same scalar-reference comparison. -/
theorem sq_abarStarInv_originCube_sub_between_le
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m0 L n k : ℕ}
    {xi delta1 : ℝ}
    (hS : inductionHypothesis M m0 xi delta1) (hLm0 : L ≤ m0)
    (hLn : L ≤ n) (hLk : L ≤ k) (i j : Fin d) :
    (abarStarInv M L (Ch02.cubeDomain (originCube d (n : ℤ))) i j -
      abarStarInv M L (Ch02.cubeDomain (originCube d (k : ℤ))) i j) ^ 2 ≤
      16 * (ahom M L)⁻¹ ^ 2 * delta1 ^ 2 := by
  by_cases hij : i = j
  · subst j
    have hn := sq_abs_abarStarInv_entry_sub_ahom_inv_le_of_inductionHypothesis
      M hS hLm0 hLn i
    have hk := sq_abs_abarStarInv_entry_sub_ahom_inv_le_of_inductionHypothesis
      M hS hLm0 hLk i
    rw [sq_abs] at hn hk
    have haux := sq_nonneg
      ((abarStarInv M L (Ch02.cubeDomain (originCube d (n : ℤ))) i i -
          (ahom M L)⁻¹) +
        (abarStarInv M L (Ch02.cubeDomain (originCube d (k : ℤ))) i i -
          (ahom M L)⁻¹))
    nlinarith
  · rw [abarStarInv_originCube_offdiag_eq_zero M L n i j hij,
      abarStarInv_originCube_offdiag_eq_zero M L k i j hij]
    norm_num
    positivity

/-- Step 4: the finite descendant average of entrywise parent differences is
bounded by the two parent variances and their annealed mean gap. -/
theorem average_integral_randomAStarInv_entry_sub_sq_le_accepted
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m0 L n m : ℕ}
    {xi delta1 : ℝ} (hxi : 2 ≤ xi)
    (hS : inductionHypothesis M m0 xi delta1) (hLm0 : L ≤ m0)
    (hLn : L ≤ n) (hnm : n ≤ m) (i j : Fin d) :
    let s := descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)
    ((s.card : ℝ)⁻¹) * ∑ R ∈ s,
        ∫ omega,
          ((randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j -
            (randomAStarMatrix M L
              (Ch02.cubeDomain (originCube d (m : ℤ))) omega)⁻¹ i j) ^ 2
          ∂M.P.toMeasure ≤
      3 * (finiteIntegrationVarianceConstant d * (ahom M L)⁻¹ ^ 2 * delta1 *
        (delta1 + Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ)))) +
      3 * (finiteIntegrationVarianceConstant d * (ahom M L)⁻¹ ^ 2 * delta1 *
        (delta1 + Real.rpow 3 (-((d * (m - L) : ℕ) : ℝ)))) +
      48 * (ahom M L)⁻¹ ^ 2 * delta1 ^ 2 := by
  dsimp only
  have hLm : L ≤ m := hLn.trans hnm
  have hs : (descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).Nonempty := by
    rw [descendantsAtScale_eq_descendantsAtDepth (originCube d (m : ℤ)) (by
      change (n : ℤ) ≤ (m : ℤ)
      exact_mod_cast hnm)]
    exact descendantsAtDepth_nonempty _ _
  have hbase := average_integral_randomAStarInv_entry_sub_sq_le_mean_variance
    M L (descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)) hs
      (n : ℤ) (fun R hR => scale_eq_of_mem_descendantsAtScale hR)
      (originCube d (m : ℤ)) i j
  have hvn := variance_randomAStarInv_entry_originCube_le_accepted
    M hxi hS hLm0 hLn i j
  have hvm := variance_randomAStarInv_entry_originCube_le_accepted
    M hxi hS hLm0 hLm i j
  have hgap := sq_abarStarInv_originCube_sub_between_le
    M hS hLm0 hLn hLm i j
  have hmeanEqN :
      ∫ omega, (randomAStarMatrix M L
          (Ch02.cubeDomain (originCube d (n : ℤ))) omega)⁻¹ i j ∂M.P.toMeasure =
        abarStarInv M L (Ch02.cubeDomain (originCube d (n : ℤ))) i j := by
    rw [← integral_matrix_apply
      (integrable_randomAStarMatrix_inv M L
        (Ch02.cubeDomain (originCube d (n : ℤ)))) i j]
    rfl
  have hmeanEqM :
      ∫ omega, (randomAStarMatrix M L
          (Ch02.cubeDomain (originCube d (m : ℤ))) omega)⁻¹ i j ∂M.P.toMeasure =
        abarStarInv M L (Ch02.cubeDomain (originCube d (m : ℤ))) i j := by
    rw [← integral_matrix_apply
      (integrable_randomAStarMatrix_inv M L
        (Ch02.cubeDomain (originCube d (m : ℤ)))) i j]
    rfl
  change
    ((descendantsAtScale (originCube d (m : ℤ)) (n : ℤ)).card : ℝ)⁻¹ *
        ∑ Q ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ),
          ∫ omega,
            ((randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ i j -
              (randomAStarMatrix M L
                (Ch02.cubeDomain (originCube d (m : ℤ))) omega)⁻¹ i j) ^ 2
            ∂M.P.toMeasure ≤
      3 * variance (fun omega : Sample d =>
          (randomAStarMatrix M L
            (Ch02.cubeDomain (originCube d (n : ℤ))) omega)⁻¹ i j) M.P.toMeasure +
      3 * variance (fun omega : Sample d =>
          (randomAStarMatrix M L
            (Ch02.cubeDomain (originCube d (m : ℤ))) omega)⁻¹ i j) M.P.toMeasure +
      3 * ((∫ omega, (randomAStarMatrix M L
              (Ch02.cubeDomain (originCube d (n : ℤ))) omega)⁻¹ i j
              ∂M.P.toMeasure) -
            ∫ omega, (randomAStarMatrix M L
              (Ch02.cubeDomain (originCube d (m : ℤ))) omega)⁻¹ i j
              ∂M.P.toMeasure) ^ 2 at hbase
  rw [hmeanEqN, hmeanEqM] at hbase
  linarith

/-! ## Vector quadratic integrals -/

/-- Every annealed inverse-star entry has the diagonal scalar-reference
budget; the off-diagonal case is zero by isotropy. -/
theorem sq_abarStarInv_entry_sub_scalar_le
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m0 L n : ℕ}
    {xi delta1 : ℝ}
    (hS : inductionHypothesis M m0 xi delta1) (hLm0 : L ≤ m0)
    (hLn : L ≤ n) (i j : Fin d) :
    (abarStarInv M L (Ch02.cubeDomain (originCube d (n : ℤ))) i j -
      (ahom M L)⁻¹ * (1 : Mat d) i j) ^ 2 ≤
      4 * (ahom M L)⁻¹ ^ 2 * delta1 ^ 2 := by
  by_cases hij : i = j
  · subst j
    simpa [Matrix.one_apply] using
      sq_abs_abarStarInv_entry_sub_ahom_inv_le_of_inductionHypothesis
        M hS hLm0 hLn i
  · rw [abarStarInv_originCube_offdiag_eq_zero M L n i j hij]
    simp [hij]
    positivity

/-- The parent entry's second moment about the scalar reference is its
centered second moment plus the annealed scalar defect. -/
theorem integral_randomAStarInv_entry_sub_scalar_sq_le_accepted
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m0 L n : ℕ}
    {xi delta1 : ℝ} (hxi : 2 ≤ xi)
    (hS : inductionHypothesis M m0 xi delta1) (hLm0 : L ≤ m0)
    (hLn : L ≤ n) (i j : Fin d) :
    ∫ omega : Sample d,
        ((randomAStarMatrix M L
            (Ch02.cubeDomain (originCube d (n : ℤ))) omega)⁻¹ i j -
          (ahom M L)⁻¹ * (1 : Mat d) i j) ^ 2 ∂M.P.toMeasure ≤
      2 * (finiteIntegrationVarianceConstant d * (ahom M L)⁻¹ ^ 2 * delta1 *
        (delta1 + Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ)))) +
      8 * (ahom M L)⁻¹ ^ 2 * delta1 ^ 2 := by
  let X : Sample d → ℝ := fun omega =>
    (randomAStarMatrix M L
      (Ch02.cubeDomain (originCube d (n : ℤ))) omega)⁻¹ i j
  let b : ℝ := abarStarInv M L
    (Ch02.cubeDomain (originCube d (n : ℤ))) i j
  let s : ℝ := (ahom M L)⁻¹ * (1 : Mat d) i j
  have hrawMeas : AEStronglyMeasurable X M.P.toMeasure :=
    ((((integrable_randomAStarMatrix_inv M L
      (Ch02.cubeDomain (originCube d (n : ℤ)))).eval i).eval j).1)
  have hraw : MemLp X 2 M.P.toMeasure :=
    (memLp_two_iff_integrable_sq hrawMeas).2
      (integrable_randomAStarInv_entry_sq M L
        (Ch02.cubeDomain (originCube d (n : ℤ))) i j)
  have hleft : Integrable (fun omega => (X omega - s) ^ 2) M.P.toMeasure :=
    (memLp_two_iff_integrable_sq
      (hraw.sub (memLp_const s)).aestronglyMeasurable).1
        (hraw.sub (memLp_const s))
  have hcenter : Integrable (fun omega => (X omega - b) ^ 2) M.P.toMeasure :=
    (memLp_two_iff_integrable_sq
      (hraw.sub (memLp_const b)).aestronglyMeasurable).1
        (hraw.sub (memLp_const b))
  have hright : Integrable
      (fun omega => 2 * (X omega - b) ^ 2 + 2 * (b - s) ^ 2) M.P.toMeasure :=
    (hcenter.const_mul 2).add (integrable_const _)
  have hpoint : ∀ omega,
      (X omega - s) ^ 2 ≤ 2 * (X omega - b) ^ 2 + 2 * (b - s) ^ 2 := by
    intro omega
    nlinarith [sq_nonneg ((X omega - b) - (b - s))]
  have hcenterBound := integral_centered_randomAStarInv_entry_sq_le_accepted
    M hxi hS hLm0 hLn i j
  have hmeanBound := sq_abarStarInv_entry_sub_scalar_le
    M hS hLm0 hLn i j
  change ∫ omega, (X omega - s) ^ 2 ∂M.P.toMeasure ≤ _
  calc
    ∫ omega, (X omega - s) ^ 2 ∂M.P.toMeasure ≤
        ∫ omega, (2 * (X omega - b) ^ 2 + 2 * (b - s) ^ 2)
          ∂M.P.toMeasure := integral_mono hleft hright hpoint
    _ = 2 * ∫ omega, (X omega - b) ^ 2 ∂M.P.toMeasure +
        2 * (b - s) ^ 2 := by
      rw [integral_add, integral_const_mul, integral_const,
        probReal_univ, one_smul]
      · exact hcenter.const_mul 2
      · exact integrable_const _
    _ ≤ _ := by
      have hc : ∫ omega, (X omega - b) ^ 2 ∂M.P.toMeasure ≤
          finiteIntegrationVarianceConstant d * (ahom M L)⁻¹ ^ 2 * delta1 *
            (delta1 + Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ))) := by
        simpa only [X, b] using hcenterBound
      have hm : (b - s) ^ 2 ≤ 4 * (ahom M L)⁻¹ ^ 2 * delta1 ^ 2 := by
        simpa only [b, s] using hmeanBound
      linarith

/-- The parent comparison-vector integral in the expectation apex is bounded
by the coordinate parent moments. -/
theorem ahom_mul_integral_coarseScaleSeparation_le_accepted
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m0 L m : ℕ}
    {xi delta1 : ℝ} (hxi : 2 ≤ xi)
    (hS : inductionHypothesis M m0 xi delta1) (hLm0 : L ≤ m0)
    (hLm : L ≤ m) (p q : Vec d)
    (hq : q = ahom M L • p) (hqNorm : vecNormSq q ≤ ahom M L) :
    ahom M L *
        ∫ omega : Sample d,
          vecNormSq
            (coarseScaleSeparation (aCutoffRegCoeffField M L omega)
              (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
              (originCube d (m : ℤ)) p q) ∂M.P.toMeasure ≤
      (ahom M L) ^ 2 * (d : ℝ) ^ 2 *
        (2 * (finiteIntegrationVarianceConstant d * (ahom M L)⁻¹ ^ 2 * delta1 *
          (delta1 + Real.rpow 3 (-((d * (m - L) : ℕ) : ℝ)))) +
          8 * (ahom M L)⁻¹ ^ 2 * delta1 ^ 2) := by
  let S : Sample d → ℝ := fun omega =>
    vecNormSq
      (coarseScaleSeparation (aCutoffRegCoeffField M L omega)
        (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
        (originCube d (m : ℤ)) p q)
  let E : Fin d → Fin d → Sample d → ℝ := fun i j omega =>
    ((randomAStarMatrix M L
      (Ch02.cubeDomain (originCube d (m : ℤ))) omega)⁻¹ i j -
        (ahom M L)⁻¹ * (1 : Mat d) i j) ^ 2
  have hSint : Integrable S M.P.toMeasure :=
    integrable_vecNormSq_coarseScaleSeparation_aCutoff M L
      (originCube d (m : ℤ)) p q
  have hEint : ∀ i j, Integrable (E i j) M.P.toMeasure := by
    intro i j
    let X : Sample d → ℝ := fun omega =>
      (randomAStarMatrix M L
        (Ch02.cubeDomain (originCube d (m : ℤ))) omega)⁻¹ i j
    have hrawMeas : AEStronglyMeasurable X M.P.toMeasure :=
      ((((integrable_randomAStarMatrix_inv M L
        (Ch02.cubeDomain (originCube d (m : ℤ)))).eval i).eval j).1)
    have hraw : MemLp X 2 M.P.toMeasure :=
      (memLp_two_iff_integrable_sq hrawMeas).2
        (integrable_randomAStarInv_entry_sq M L
          (Ch02.cubeDomain (originCube d (m : ℤ))) i j)
    exact (memLp_two_iff_integrable_sq
      (hraw.sub (memLp_const _)).aestronglyMeasurable).1 (hraw.sub (memLp_const _))
  have hsumInt : Integrable (fun omega => ∑ i : Fin d, ∑ j : Fin d, E i j omega)
      M.P.toMeasure := integrable_finset_sum Finset.univ (fun i _hi =>
    integrable_finset_sum Finset.univ (fun j _hj => hEint i j))
  have hpoint : ∀ omega, ahom M L * S omega ≤
      (ahom M L) ^ 2 * ∑ i : Fin d, ∑ j : Fin d, E i j omega := by
    intro omega
    simpa only [S, E] using
      ahom_mul_vecNormSq_coarseScaleSeparation_aCutoff_le_entry_sum
        M L omega (originCube d (m : ℤ)) p q hq hqNorm
  have hleft : Integrable (fun omega => ahom M L * S omega) M.P.toMeasure :=
    hSint.const_mul _
  have hright : Integrable
      (fun omega => (ahom M L) ^ 2 * ∑ i : Fin d, ∑ j : Fin d, E i j omega)
      M.P.toMeasure := hsumInt.const_mul _
  have hEIntegralEq :
      ∫ omega, ∑ i : Fin d, ∑ j : Fin d, E i j omega ∂M.P.toMeasure =
        ∑ i : Fin d, ∑ j : Fin d,
          ∫ omega, E i j omega ∂M.P.toMeasure := by
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro i _hi
      rw [integral_finset_sum]
      intro j _hj
      exact hEint i j
    · intro i _hi
      exact integrable_finset_sum Finset.univ (fun j _hj => hEint i j)
  have hESumBound :
      ∑ i : Fin d, ∑ j : Fin d,
          ∫ omega, E i j omega ∂M.P.toMeasure ≤
        ∑ _i : Fin d, ∑ _j : Fin d,
          (2 * (finiteIntegrationVarianceConstant d * (ahom M L)⁻¹ ^ 2 * delta1 *
            (delta1 + Real.rpow 3 (-((d * (m - L) : ℕ) : ℝ)))) +
            8 * (ahom M L)⁻¹ ^ 2 * delta1 ^ 2) := by
    apply Finset.sum_le_sum
    intro i _hi
    apply Finset.sum_le_sum
    intro j _hj
    simpa only [E] using
      integral_randomAStarInv_entry_sub_scalar_sq_le_accepted
        M hxi hS hLm0 hLm i j
  calc
    ahom M L * ∫ omega, S omega ∂M.P.toMeasure =
        ∫ omega, ahom M L * S omega ∂M.P.toMeasure :=
      (integral_const_mul ..).symm
    _ ≤ ∫ omega, (ahom M L) ^ 2 *
          ∑ i : Fin d, ∑ j : Fin d, E i j omega ∂M.P.toMeasure :=
      integral_mono hleft hright hpoint
    _ = (ahom M L) ^ 2 * ∑ i : Fin d, ∑ j : Fin d,
          ∫ omega, E i j omega ∂M.P.toMeasure := by
      rw [integral_const_mul, hEIntegralEq]
    _ ≤ (ahom M L) ^ 2 * ∑ _i : Fin d, ∑ _j : Fin d,
          (2 * (finiteIntegrationVarianceConstant d * (ahom M L)⁻¹ ^ 2 * delta1 *
            (delta1 + Real.rpow 3 (-((d * (m - L) : ℕ) : ℝ)))) +
            8 * (ahom M L)⁻¹ ^ 2 * delta1 ^ 2) := by
      exact mul_le_mul_of_nonneg_left hESumBound (sq_nonneg _)
    _ = _ := by
      simp
      ring

/-- The descendant coarse-matrix variation integral is bounded by the two
parent entry variances and their annealed mean gap. -/
theorem ahom_mul_integral_descendantsAverage_coarseMatrixVariationSq_le_accepted
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m0 L n m : ℕ}
    {xi delta1 : ℝ} (hxi : 2 ≤ xi)
    (hS : inductionHypothesis M m0 xi delta1) (hLm0 : L ≤ m0)
    (hLn : L ≤ n) (hnm : n ≤ m) (p q : Vec d)
    (hqNorm : vecNormSq q ≤ ahom M L) :
    ahom M L *
        ∫ omega : Sample d,
          descendantsAverage (originCube d (m : ℤ)) (m - n)
            (coarseMatrixVariationSq (aCutoffRegCoeffField M L omega)
              (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
              (originCube d (m : ℤ)) p q) ∂M.P.toMeasure ≤
      (ahom M L) ^ 2 * (d : ℝ) ^ 2 *
        (3 * (finiteIntegrationVarianceConstant d * (ahom M L)⁻¹ ^ 2 * delta1 *
          (delta1 + Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ)))) +
         3 * (finiteIntegrationVarianceConstant d * (ahom M L)⁻¹ ^ 2 * delta1 *
          (delta1 + Real.rpow 3 (-((d * (m - L) : ℕ) : ℝ)))) +
         48 * (ahom M L)⁻¹ ^ 2 * delta1 ^ 2) := by
  let Q := originCube d (m : ℤ)
  let V : Sample d → ℝ := fun omega =>
    descendantsAverage Q (m - n)
      (coarseMatrixVariationSq (aCutoffRegCoeffField M L omega)
        (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
        Q p q)
  let E : TriadicCube d → Fin d → Fin d → Sample d → ℝ :=
    fun R i j omega =>
      ((randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ i j -
        (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j) ^ 2
  have hLm : L ≤ m := hLn.trans hnm
  have hscale : (n : ℤ) ≤ Q.scale := by
    change (n : ℤ) ≤ (m : ℤ)
    exact_mod_cast hnm
  have hdepth : descendantsAtDepth Q (m - n) = descendantsAtScale Q (n : ℤ) := by
    rw [descendantsAtScale_eq_descendantsAtDepth Q hscale]
    congr 1
    change m - n = ((m : ℤ) - (n : ℤ)).toNat
    omega
  have hEint : ∀ R ∈ descendantsAtDepth Q (m - n), ∀ i j,
      Integrable (E R i j) M.P.toMeasure := by
    intro R _hR i j
    have hQmeas : AEStronglyMeasurable (fun omega : Sample d =>
        (randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ i j)
        M.P.toMeasure :=
      ((((integrable_randomAStarMatrix_inv M L (Ch02.cubeDomain Q)).eval i).eval j).1)
    have hRmeas : AEStronglyMeasurable (fun omega : Sample d =>
        (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j)
        M.P.toMeasure :=
      ((((integrable_randomAStarMatrix_inv M L (Ch02.cubeDomain R)).eval i).eval j).1)
    have hQlp : MemLp (fun omega : Sample d =>
        (randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ i j)
        2 M.P.toMeasure :=
      (memLp_two_iff_integrable_sq hQmeas).2
        (integrable_randomAStarInv_entry_sq M L (Ch02.cubeDomain Q) i j)
    have hRlp : MemLp (fun omega : Sample d =>
        (randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j)
        2 M.P.toMeasure :=
      (memLp_two_iff_integrable_sq hRmeas).2
        (integrable_randomAStarInv_entry_sq M L (Ch02.cubeDomain R) i j)
    exact (memLp_two_iff_integrable_sq
      (hQlp.sub hRlp).aestronglyMeasurable).1 (hQlp.sub hRlp)
  have hEavgInt : ∀ i j, Integrable
      (fun omega => descendantsAverage Q (m - n) (fun R => E R i j omega))
      M.P.toMeasure := by
    intro i j
    let D := descendantsAtDepth Q (m - n)
    have hsum : Integrable (fun omega => ∑ R ∈ D, E R i j omega)
        M.P.toMeasure := integrable_finset_sum D (fun R hR =>
      hEint R (by simpa only [D] using hR) i j)
    simpa only [descendantsAverage, D] using hsum.const_mul ((D.card : ℝ)⁻¹)
  have hVint : Integrable V M.P.toMeasure := by
    simpa only [V, Q] using
      integrable_descendantsAverage_coarseMatrixVariationSq_aCutoff
        M L (originCube d (m : ℤ)) (m - n) p q
  have hsumInt : Integrable (fun omega => ∑ i : Fin d, ∑ j : Fin d,
      descendantsAverage Q (m - n) (fun R => E R i j omega)) M.P.toMeasure :=
    integrable_finset_sum Finset.univ (fun i _hi =>
      integrable_finset_sum Finset.univ (fun j _hj => hEavgInt i j))
  have hpoint : ∀ omega, ahom M L * V omega ≤
      (ahom M L) ^ 2 * ∑ i : Fin d, ∑ j : Fin d,
        descendantsAverage Q (m - n) (fun R => E R i j omega) := by
    intro omega
    have hcells : descendantsAverage Q (m - n)
        (fun R => ahom M L *
          coarseMatrixVariationSq (aCutoffRegCoeffField M L omega)
            (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
            Q p q R) ≤
      descendantsAverage Q (m - n)
        (fun R => (ahom M L) ^ 2 * ∑ i : Fin d, ∑ j : Fin d, E R i j omega) := by
      apply descendantsAverage_le_descendantsAverage
      intro R _hR
      simpa only [E, Q] using
        ahom_mul_coarseMatrixVariationSq_aCutoff_le_entry_sum
          M L omega Q R p q hqNorm
    calc
      ahom M L * V omega = descendantsAverage Q (m - n)
          (fun R => ahom M L *
            coarseMatrixVariationSq (aCutoffRegCoeffField M L omega)
              (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
              Q p q R) := by
        simpa only [V] using (descendantsAverage_mul_left Q (m - n) (ahom M L)
          (coarseMatrixVariationSq (aCutoffRegCoeffField M L omega)
            (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
            Q p q)).symm
      _ ≤ descendantsAverage Q (m - n)
          (fun R => (ahom M L) ^ 2 * ∑ i : Fin d, ∑ j : Fin d, E R i j omega) :=
        hcells
      _ = (ahom M L) ^ 2 * ∑ i : Fin d, ∑ j : Fin d,
          descendantsAverage Q (m - n) (fun R => E R i j omega) := by
        rw [descendantsAverage_mul_left, descendantsAverage_sum]
        apply congrArg ((ahom M L) ^ 2 * ·)
        apply Finset.sum_congr rfl
        intro i _hi
        rw [descendantsAverage_sum]
  have hcoordBound : ∀ i j,
      ∫ omega, descendantsAverage Q (m - n) (fun R => E R i j omega)
          ∂M.P.toMeasure ≤
        3 * (finiteIntegrationVarianceConstant d * (ahom M L)⁻¹ ^ 2 * delta1 *
          (delta1 + Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ)))) +
        3 * (finiteIntegrationVarianceConstant d * (ahom M L)⁻¹ ^ 2 * delta1 *
          (delta1 + Real.rpow 3 (-((d * (m - L) : ℕ) : ℝ)))) +
        48 * (ahom M L)⁻¹ ^ 2 * delta1 ^ 2 := by
    intro i j
    have havg := average_integral_randomAStarInv_entry_sub_sq_le_accepted
      M hxi hS hLm0 hLn hnm i j
    rw [integral_descendantsAverage_sample_eq (fun R hR => hEint R hR i j)]
    have hflip : (fun R => ∫ omega, E R i j omega ∂M.P.toMeasure) =
        fun R => ∫ omega,
          ((randomAStarMatrix M L (Ch02.cubeDomain R) omega)⁻¹ i j -
            (randomAStarMatrix M L (Ch02.cubeDomain Q) omega)⁻¹ i j) ^ 2
          ∂M.P.toMeasure := by
      funext R
      apply integral_congr_ae
      filter_upwards with omega
      dsimp only [E]
      ring
    rw [hflip]
    simpa only [Q, descendantsAverage, hdepth] using havg
  have hsumIntegralEq :
      ∫ omega, ∑ i : Fin d, ∑ j : Fin d,
          descendantsAverage Q (m - n) (fun R => E R i j omega) ∂M.P.toMeasure =
        ∑ i : Fin d, ∑ j : Fin d,
          ∫ omega, descendantsAverage Q (m - n) (fun R => E R i j omega)
            ∂M.P.toMeasure := by
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro i _hi
      rw [integral_finset_sum]
      intro j _hj
      exact hEavgInt i j
    · intro i _hi
      exact integrable_finset_sum Finset.univ (fun j _hj => hEavgInt i j)
  have hsumBound :
      ∑ i : Fin d, ∑ j : Fin d,
          ∫ omega, descendantsAverage Q (m - n) (fun R => E R i j omega)
            ∂M.P.toMeasure ≤
        ∑ _i : Fin d, ∑ _j : Fin d,
          (3 * (finiteIntegrationVarianceConstant d * (ahom M L)⁻¹ ^ 2 * delta1 *
            (delta1 + Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ)))) +
           3 * (finiteIntegrationVarianceConstant d * (ahom M L)⁻¹ ^ 2 * delta1 *
            (delta1 + Real.rpow 3 (-((d * (m - L) : ℕ) : ℝ)))) +
           48 * (ahom M L)⁻¹ ^ 2 * delta1 ^ 2) := by
    apply Finset.sum_le_sum
    intro i _hi
    apply Finset.sum_le_sum
    intro j _hj
    exact hcoordBound i j
  have hleft : Integrable (fun omega => ahom M L * V omega) M.P.toMeasure :=
    hVint.const_mul _
  have hright : Integrable (fun omega => (ahom M L) ^ 2 *
      ∑ i : Fin d, ∑ j : Fin d,
        descendantsAverage Q (m - n) (fun R => E R i j omega)) M.P.toMeasure :=
    hsumInt.const_mul _
  change ahom M L * ∫ omega, V omega ∂M.P.toMeasure ≤ _
  calc
    ahom M L * ∫ omega, V omega ∂M.P.toMeasure =
        ∫ omega, ahom M L * V omega ∂M.P.toMeasure :=
      (integral_const_mul ..).symm
    _ ≤ ∫ omega, (ahom M L) ^ 2 *
          ∑ i : Fin d, ∑ j : Fin d,
            descendantsAverage Q (m - n) (fun R => E R i j omega)
          ∂M.P.toMeasure := integral_mono hleft hright hpoint
    _ = (ahom M L) ^ 2 * ∑ i : Fin d, ∑ j : Fin d,
          ∫ omega, descendantsAverage Q (m - n) (fun R => E R i j omega)
            ∂M.P.toMeasure := by
      rw [integral_const_mul, hsumIntegralEq]
    _ ≤ (ahom M L) ^ 2 * ∑ _i : Fin d, ∑ _j : Fin d,
          (3 * (finiteIntegrationVarianceConstant d * (ahom M L)⁻¹ ^ 2 * delta1 *
            (delta1 + Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ)))) +
           3 * (finiteIntegrationVarianceConstant d * (ahom M L)⁻¹ ^ 2 * delta1 *
            (delta1 + Real.rpow 3 (-((d * (m - L) : ℕ) : ℝ)))) +
           48 * (ahom M L)⁻¹ ^ 2 * delta1 ^ 2) :=
      mul_le_mul_of_nonneg_left hsumBound (sq_nonneg _)
    _ = _ := by
      simp
      ring

/-! ## Natural-scale corridor convolution -/

/-- A natural printed weight is the corresponding power of `1/3`. -/
theorem rpow_three_neg_nat_eq_pow (k : ℕ) :
    Real.rpow 3 (-(k : ℝ)) = (1 / 3 : ℝ) ^ k := by
  calc
    Real.rpow 3 (-(k : ℝ)) = (Real.rpow 3 (k : ℝ))⁻¹ :=
      Real.rpow_neg (by norm_num) _
    _ = ((3 : ℝ) ^ k)⁻¹ := congrArg Inv.inv (Real.rpow_natCast 3 k)
    _ = (1 / 3 : ℝ) ^ k := by rw [← inv_pow]; norm_num

/-- Reverse the natural corridor by its lag from the terminal scale. -/
theorem sum_Icc_nat_reindex {L m : ℕ} (hLm : L ≤ m) (w : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc L m, w (m - n) =
      ∑ k ∈ Finset.range (m - L + 1), w k := by
  refine Finset.sum_nbij' (fun n : ℕ => m - n) (fun k : ℕ => m - k)
    ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    simp only [Finset.mem_range]
    omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Icc]
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    exact Nat.sub_sub_self hn.2
  · intro k hk
    simp only [Finset.mem_range] at hk
    apply Nat.sub_sub_self
    omega
  · intro n _hn
    rfl

/-- The finite geometric series with ratio `1/3` is at most `3/2`. -/
theorem sum_range_geom_third_le (N : ℕ) :
    ∑ k ∈ Finset.range N, (1 / 3 : ℝ) ^ k ≤ 3 / 2 := by
  rw [geom_sum_eq (by norm_num : (1 / 3 : ℝ) ≠ 1)]
  have hp : 0 ≤ (1 / 3 : ℝ) ^ N := by positivity
  calc
    ((1 / 3 : ℝ) ^ N - 1) / (1 / 3 - 1) =
        3 / 2 * (1 - (1 / 3 : ℝ) ^ N) := by ring
    _ ≤ 3 / 2 := by nlinarith

/-- The printed natural corridor weights sum to at most `3/2`. -/
theorem sum_Icc_nat_three_neg_le {L m : ℕ} (hLm : L ≤ m) :
    ∑ n ∈ Finset.Icc L m, Real.rpow 3 (-((m - n : ℕ) : ℝ)) ≤ 3 / 2 := by
  calc
    ∑ n ∈ Finset.Icc L m, Real.rpow 3 (-((m - n : ℕ) : ℝ)) =
        ∑ n ∈ Finset.Icc L m, (1 / 3 : ℝ) ^ (m - n) := by
      apply Finset.sum_congr rfl
      intro n _hn
      exact rpow_three_neg_nat_eq_pow (m - n)
    _ = ∑ k ∈ Finset.range (m - L + 1), (1 / 3 : ℝ) ^ k :=
      sum_Icc_nat_reindex hLm _
    _ ≤ 3 / 2 := sum_range_geom_third_le _

/-- Convolution of the printed ratio `1/3` with any ratio at most `1/9`
retains the printed terminal rate. -/
theorem sum_range_geom_conv_le {b : ℝ} (hb0 : 0 ≤ b) (hb : b ≤ 1 / 9)
    (t : ℕ) :
    ∑ k ∈ Finset.range (t + 1), (1 / 3 : ℝ) ^ k * b ^ (t - k) ≤
      3 / 2 * (1 / 3 : ℝ) ^ t := by
  have hstep : ∀ k ∈ Finset.range (t + 1),
      (1 / 3 : ℝ) ^ k * b ^ (t - k) ≤
        (1 / 3 : ℝ) ^ t * (1 / 3 : ℝ) ^ (t - k) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    have hbk : b ^ (t - k) ≤ (1 / 9 : ℝ) ^ (t - k) :=
      pow_le_pow_left₀ hb0 hb _
    have hid : (1 / 3 : ℝ) ^ k * (1 / 9 : ℝ) ^ (t - k) =
        (1 / 3 : ℝ) ^ t * (1 / 3 : ℝ) ^ (t - k) := by
      have h9 : (1 / 9 : ℝ) = (1 / 3 : ℝ) ^ 2 := by norm_num
      rw [h9, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      omega
    calc
      (1 / 3 : ℝ) ^ k * b ^ (t - k) ≤
          (1 / 3 : ℝ) ^ k * (1 / 9 : ℝ) ^ (t - k) :=
        mul_le_mul_of_nonneg_left hbk (by positivity)
      _ = _ := hid
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.mul_sum]
  have hrefl : ∑ k ∈ Finset.range (t + 1), (1 / 3 : ℝ) ^ (t - k) =
      ∑ k ∈ Finset.range (t + 1), (1 / 3 : ℝ) ^ k := by
    simpa using Finset.sum_range_reflect (fun k => (1 / 3 : ℝ) ^ k) (t + 1)
  rw [hrefl]
  have hgeom := sum_range_geom_third_le (t + 1)
  calc
    (1 / 3 : ℝ) ^ t * ∑ k ∈ Finset.range (t + 1), (1 / 3 : ℝ) ^ k ≤
        (1 / 3 : ℝ) ^ t * (3 / 2) :=
      mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = _ := by ring

/-- The dimension-`d` corridor decay convolves into the frozen one-dimensional
rate whenever `2 ≤ d`. -/
theorem sum_Icc_nat_weight_mul_dimension_decay_le
    {d L m : ℕ} (hd : 2 ≤ d) (hLm : L ≤ m) :
    ∑ n ∈ Finset.Icc L m,
        Real.rpow 3 (-((m - n : ℕ) : ℝ)) *
          Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ)) ≤
      3 / 2 * Real.rpow 3 (-((m - L : ℕ) : ℝ)) := by
  let b : ℝ := Real.rpow 3 (-(d : ℝ))
  have hb0 : 0 ≤ b := Real.rpow_nonneg (by norm_num) _
  have hb9 : b ≤ 1 / 9 := by
    have hdcast : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hexp : -(d : ℝ) ≤ -(2 : ℝ) := by linarith
    have hmono := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
    have hval : Real.rpow 3 (-(2 : ℝ)) = 1 / 9 := by
      calc
        Real.rpow 3 (-(2 : ℝ)) = (Real.rpow 3 (2 : ℝ))⁻¹ :=
          Real.rpow_neg (by norm_num) _
        _ = ((3 : ℝ) ^ (2 : ℕ))⁻¹ := congrArg Inv.inv (Real.rpow_natCast 3 2)
        _ = 1 / 9 := by norm_num
    dsimp only [b]
    exact hmono.trans_eq hval
  have hdecay : ∀ n ∈ Finset.Icc L m,
      Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ)) = b ^ (n - L) := by
    intro n _hn
    calc
      Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ)) =
          Real.rpow 3 (-(d : ℝ) * ((n - L : ℕ) : ℝ)) := by
        congr 1
        push_cast
        ring
      _ = Real.rpow (Real.rpow 3 (-(d : ℝ))) ((n - L : ℕ) : ℝ) :=
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _
      _ = b ^ (n - L) := by
        dsimp only [b]
        exact Real.rpow_natCast _ _
  calc
    ∑ n ∈ Finset.Icc L m,
        Real.rpow 3 (-((m - n : ℕ) : ℝ)) *
          Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ)) =
        ∑ n ∈ Finset.Icc L m, (1 / 3 : ℝ) ^ (m - n) * b ^ (n - L) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [rpow_three_neg_nat_eq_pow, hdecay n hn]
    _ = ∑ k ∈ Finset.range (m - L + 1),
          (1 / 3 : ℝ) ^ k * b ^ (m - L - k) := by
      refine Eq.trans ?_ (sum_Icc_nat_reindex hLm
        (fun k => (1 / 3 : ℝ) ^ k * b ^ (m - L - k)))
      apply Finset.sum_congr rfl
      intro n hn
      simp only [Finset.mem_Icc] at hn
      congr 2
      omega
    _ ≤ 3 / 2 * (1 / 3 : ℝ) ^ (m - L) :=
      sum_range_geom_conv_le hb0 hb9 (m - L)
    _ = 3 / 2 * Real.rpow 3 (-((m - L : ℕ) : ℝ)) := by
      rw [rpow_three_neg_nat_eq_pow]

/-! ## Normalized matrix blocks and their corridor sum -/

/-- Cancel the `ahom²` normalization in the descendant matrix-variation
bound. -/
theorem ahom_mul_integral_descendantsAverage_coarseMatrixVariationSq_le_normalized
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m0 L n m : ℕ}
    {xi delta1 : ℝ} (hxi : 2 ≤ xi)
    (hS : inductionHypothesis M m0 xi delta1) (hLm0 : L ≤ m0)
    (hLn : L ≤ n) (hnm : n ≤ m) (p q : Vec d)
    (hqNorm : vecNormSq q ≤ ahom M L) :
    ahom M L *
        ∫ omega : Sample d,
          descendantsAverage (originCube d (m : ℤ)) (m - n)
            (coarseMatrixVariationSq (aCutoffRegCoeffField M L omega)
              (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
              (originCube d (m : ℤ)) p q) ∂M.P.toMeasure ≤
      (d : ℝ) ^ 2 *
        (3 * finiteIntegrationVarianceConstant d * delta1 *
            (delta1 + Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ))) +
         3 * finiteIntegrationVarianceConstant d * delta1 *
            (delta1 + Real.rpow 3 (-((d * (m - L) : ℕ) : ℝ))) +
         48 * delta1 ^ 2) := by
  have h :=
    ahom_mul_integral_descendantsAverage_coarseMatrixVariationSq_le_accepted
      M hxi hS hLm0 hLn hnm p q hqNorm
  have halpha : 0 < ahom M L := ahom_pos M L
  convert h using 1
  all_goals field_simp [halpha.ne']

/-- Cancel the `ahom²` normalization in the parent comparison-vector bound. -/
theorem ahom_mul_integral_coarseScaleSeparation_le_normalized
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m0 L m : ℕ}
    {xi delta1 : ℝ} (hxi : 2 ≤ xi)
    (hS : inductionHypothesis M m0 xi delta1) (hLm0 : L ≤ m0)
    (hLm : L ≤ m) (p q : Vec d)
    (hq : q = ahom M L • p) (hqNorm : vecNormSq q ≤ ahom M L) :
    ahom M L *
        ∫ omega : Sample d,
          vecNormSq
            (coarseScaleSeparation (aCutoffRegCoeffField M L omega)
              (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
              (originCube d (m : ℤ)) p q) ∂M.P.toMeasure ≤
      (d : ℝ) ^ 2 *
        (2 * finiteIntegrationVarianceConstant d * delta1 *
          (delta1 + Real.rpow 3 (-((d * (m - L) : ℕ) : ℝ))) +
          8 * delta1 ^ 2) := by
  have h := ahom_mul_integral_coarseScaleSeparation_le_accepted
    M hxi hS hLm0 hLm p q hq hqNorm
  have halpha : 0 < ahom M L := ahom_pos M L
  convert h using 1
  all_goals field_simp [halpha.ne']

/-- Dimension decay is no slower than the frozen one-dimensional rate. -/
theorem rpow_three_dimension_decay_le {d t : ℕ} (hd : 1 ≤ d) :
    Real.rpow 3 (-((d * t : ℕ) : ℝ)) ≤ Real.rpow 3 (-(t : ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
  push_cast
  have ht : 0 ≤ (t : ℝ) := by positivity
  have hdcast : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  nlinarith

/-- Dimension-only constant for the finite corridor aggregation. -/
noncomputable def finiteIntegrationCorridorConstant (d : ℕ) : ℝ :=
  1000 * (d : ℝ) ^ 2 * (finiteIntegrationVarianceConstant d + 1)

/-- The complete matrix-variation corridor plus parent comparison-vector
block has the frozen `delta₁(delta₁ + 3^{-(m-L)})` rate. -/
theorem matrixCorridor_add_scaleSeparation_le
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m0 L m : ℕ}
    {xi delta1 : ℝ} (hxi : 2 ≤ xi)
    (hS : inductionHypothesis M m0 xi delta1) (hLm0 : L ≤ m0)
    (hLm : L ≤ m) (p q : Vec d)
    (hq : q = ahom M L • p) (hqNorm : vecNormSq q ≤ ahom M L) :
    ahom M L *
        ∑ n ∈ Finset.Icc L m,
          Real.rpow 3 (-((m - n : ℕ) : ℝ)) *
            ∫ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
              descendantsAverage (originCube d (m : ℤ)) (m - n)
                (coarseMatrixVariationSq (aCutoffRegCoeffField M L omega)
                  (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
                  (originCube d (m : ℤ)) p q) ∂M.P.toMeasure +
      ahom M L *
        ∫ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
          vecNormSq
            (coarseScaleSeparation (aCutoffRegCoeffField M L omega)
              (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
              (originCube d (m : ℤ)) p q) ∂M.P.toMeasure ≤
      finiteIntegrationCorridorConstant d * delta1 *
        (delta1 + Real.rpow 3 (-((m - L : ℕ) : ℝ))) := by
  have hd : 2 ≤ d := M.shellPrefix.dimension
  have hdelta : 0 ≤ delta1 := hS.2.1.le
  have hV0 : 0 ≤ finiteIntegrationVarianceConstant d := by
    dsimp [finiteIntegrationVarianceConstant]
    positivity
  have hD0 : 0 ≤ (d : ℝ) ^ 2 := sq_nonneg _
  have hweights := sum_Icc_nat_three_neg_le hLm
  have hconv := sum_Icc_nat_weight_mul_dimension_decay_le hd hLm
  let rM : ℝ := Real.rpow 3 (-((m - L : ℕ) : ℝ))
  let rdM : ℝ := Real.rpow 3 (-((d * (m - L) : ℕ) : ℝ))
  have hrM : 0 ≤ rM := Real.rpow_nonneg (by norm_num) _
  have hrdM : 0 ≤ rdM := Real.rpow_nonneg (by norm_num) _
  have hrdMle : rdM ≤ rM := by
    dsimp only [rdM, rM]
    exact rpow_three_dimension_decay_le (hd.trans' (by norm_num))
  let Bn : ℕ → ℝ := fun n =>
    (d : ℝ) ^ 2 *
      ((6 * finiteIntegrationVarianceConstant d + 48) * delta1 ^ 2 +
       3 * finiteIntegrationVarianceConstant d * delta1 *
          Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ)) +
       3 * finiteIntegrationVarianceConstant d * delta1 * rdM)
  have hterm : ∀ n ∈ Finset.Icc L m,
      ahom M L *
          ∫ omega : Sample d,
            descendantsAverage (originCube d (m : ℤ)) (m - n)
              (coarseMatrixVariationSq (aCutoffRegCoeffField M L omega)
                (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
                (originCube d (m : ℤ)) p q) ∂M.P.toMeasure ≤ Bn n := by
    intro n hn
    obtain ⟨hLn, hnm⟩ := Finset.mem_Icc.mp hn
    have h :=
      ahom_mul_integral_descendantsAverage_coarseMatrixVariationSq_le_normalized
        M hxi hS hLm0 hLn hnm p q hqNorm
    dsimp only [Bn, rdM]
    convert h using 1
    all_goals ring
  have hcorridor : ahom M L *
      ∑ n ∈ Finset.Icc L m,
        Real.rpow 3 (-((m - n : ℕ) : ℝ)) *
          ∫ omega : Sample d,
            descendantsAverage (originCube d (m : ℤ)) (m - n)
              (coarseMatrixVariationSq (aCutoffRegCoeffField M L omega)
                (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
                (originCube d (m : ℤ)) p q) ∂M.P.toMeasure ≤
      ∑ n ∈ Finset.Icc L m,
        Real.rpow 3 (-((m - n : ℕ) : ℝ)) * Bn n := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hw : 0 ≤ Real.rpow 3 (-((m - n : ℕ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have ht := mul_le_mul_of_nonneg_left (hterm n hn) hw
    calc
      ahom M L *
          (Real.rpow 3 (-((m - n : ℕ) : ℝ)) *
            ∫ omega : Sample d,
              descendantsAverage (originCube d (m : ℤ)) (m - n)
                (coarseMatrixVariationSq (aCutoffRegCoeffField M L omega)
                  (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
                  (originCube d (m : ℤ)) p q) ∂M.P.toMeasure) =
          Real.rpow 3 (-((m - n : ℕ) : ℝ)) *
            (ahom M L *
              ∫ omega : Sample d,
                descendantsAverage (originCube d (m : ℤ)) (m - n)
                  (coarseMatrixVariationSq (aCutoffRegCoeffField M L omega)
                    (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
                    (originCube d (m : ℤ)) p q) ∂M.P.toMeasure) := by ring
      _ ≤ Real.rpow 3 (-((m - n : ℕ) : ℝ)) * Bn n := ht
  have hscale := ahom_mul_integral_coarseScaleSeparation_le_normalized
    M hxi hS hLm0 hLm p q hq hqNorm
  have hsumIdentity :
      ∑ n ∈ Finset.Icc L m,
        Real.rpow 3 (-((m - n : ℕ) : ℝ)) * Bn n =
      (d : ℝ) ^ 2 *
        ((6 * finiteIntegrationVarianceConstant d + 48) * delta1 ^ 2 *
            ∑ n ∈ Finset.Icc L m,
              Real.rpow 3 (-((m - n : ℕ) : ℝ)) +
         3 * finiteIntegrationVarianceConstant d * delta1 *
            (∑ n ∈ Finset.Icc L m,
              Real.rpow 3 (-((m - n : ℕ) : ℝ)) *
                Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ))) +
         3 * finiteIntegrationVarianceConstant d * delta1 * rdM *
            ∑ n ∈ Finset.Icc L m,
              Real.rpow 3 (-((m - n : ℕ) : ℝ))) := by
    calc
      ∑ n ∈ Finset.Icc L m,
          Real.rpow 3 (-((m - n : ℕ) : ℝ)) * Bn n =
        ∑ n ∈ Finset.Icc L m, (d : ℝ) ^ 2 *
          (((6 * finiteIntegrationVarianceConstant d + 48) * delta1 ^ 2) *
              Real.rpow 3 (-((m - n : ℕ) : ℝ)) +
           (3 * finiteIntegrationVarianceConstant d * delta1) *
              (Real.rpow 3 (-((m - n : ℕ) : ℝ)) *
                Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ))) +
           (3 * finiteIntegrationVarianceConstant d * delta1 * rdM) *
              Real.rpow 3 (-((m - n : ℕ) : ℝ))) := by
        apply Finset.sum_congr rfl
        intro n _hn
        dsimp only [Bn]
        ring
      _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hsumIdentity] at hcorridor
  have hboundCorridor :
      (d : ℝ) ^ 2 *
        ((6 * finiteIntegrationVarianceConstant d + 48) * delta1 ^ 2 *
            ∑ n ∈ Finset.Icc L m,
              Real.rpow 3 (-((m - n : ℕ) : ℝ)) +
         3 * finiteIntegrationVarianceConstant d * delta1 *
            (∑ n ∈ Finset.Icc L m,
              Real.rpow 3 (-((m - n : ℕ) : ℝ)) *
                Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ))) +
         3 * finiteIntegrationVarianceConstant d * delta1 * rdM *
            ∑ n ∈ Finset.Icc L m,
              Real.rpow 3 (-((m - n : ℕ) : ℝ))) ≤
      100 * (d : ℝ) ^ 2 * (finiteIntegrationVarianceConstant d + 1) *
        delta1 * (delta1 + rM) := by
    have hnonnegW : 0 ≤ ∑ n ∈ Finset.Icc L m,
        Real.rpow 3 (-((m - n : ℕ) : ℝ)) :=
      Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (by norm_num) _
    have hnonnegConv : 0 ≤ ∑ n ∈ Finset.Icc L m,
        Real.rpow 3 (-((m - n : ℕ) : ℝ)) *
          Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ)) :=
      Finset.sum_nonneg fun _ _ => mul_nonneg
        (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _)
    have hA0 : 0 ≤ (6 * finiteIntegrationVarianceConstant d + 48) * delta1 ^ 2 := by
      positivity
    have hB0 : 0 ≤ 3 * finiteIntegrationVarianceConstant d * delta1 := by
      positivity
    have hC0 : 0 ≤ 3 * finiteIntegrationVarianceConstant d * delta1 * rdM := by
      positivity
    have h1 := mul_le_mul_of_nonneg_left hweights hA0
    have h2 := mul_le_mul_of_nonneg_left hconv hB0
    have h3a := mul_le_mul_of_nonneg_left hweights hC0
    have h3b :
        (3 * finiteIntegrationVarianceConstant d * delta1 * rdM) * (3 / 2) ≤
          (3 * finiteIntegrationVarianceConstant d * delta1 * rM) * (3 / 2) := by
      have hpref : 0 ≤ 3 * finiteIntegrationVarianceConstant d * delta1 := by positivity
      gcongr
    have hsum3 := add_le_add (add_le_add h1 h2) (h3a.trans h3b)
    have hinside :
        (6 * finiteIntegrationVarianceConstant d + 48) * delta1 ^ 2 *
            ∑ n ∈ Finset.Icc L m,
              Real.rpow 3 (-((m - n : ℕ) : ℝ)) +
         3 * finiteIntegrationVarianceConstant d * delta1 *
            (∑ n ∈ Finset.Icc L m,
              Real.rpow 3 (-((m - n : ℕ) : ℝ)) *
                Real.rpow 3 (-((d * (n - L) : ℕ) : ℝ))) +
         3 * finiteIntegrationVarianceConstant d * delta1 * rdM *
            ∑ n ∈ Finset.Icc L m,
              Real.rpow 3 (-((m - n : ℕ) : ℝ)) ≤
          100 * (finiteIntegrationVarianceConstant d + 1) * delta1 *
            (delta1 + rM) := by
      have hVdeltaSq : 0 ≤ finiteIntegrationVarianceConstant d * delta1 ^ 2 :=
        mul_nonneg hV0 (sq_nonneg _)
      have hVdeltaR : 0 ≤ finiteIntegrationVarianceConstant d * (delta1 * rM) :=
        mul_nonneg hV0 (mul_nonneg hdelta hrM)
      nlinarith [mul_nonneg hdelta hrM, sq_nonneg delta1]
    convert mul_le_mul_of_nonneg_left hinside hD0 using 1
    all_goals ring
  have hscale' :
      ahom M L * ∫ omega : Sample d,
          vecNormSq
            (coarseScaleSeparation (aCutoffRegCoeffField M L omega)
              (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
              (originCube d (m : ℤ)) p q) ∂M.P.toMeasure ≤
        20 * (d : ℝ) ^ 2 * (finiteIntegrationVarianceConstant d + 1) *
          delta1 * (delta1 + rM) := by
    have hrdTerm : delta1 * (delta1 + rdM) ≤ delta1 * (delta1 + rM) := by
      gcongr
    have hmain : 2 * finiteIntegrationVarianceConstant d *
        (delta1 * (delta1 + rdM)) ≤
        2 * finiteIntegrationVarianceConstant d *
          (delta1 * (delta1 + rM)) := by
      gcongr
    have hinside :
        2 * finiteIntegrationVarianceConstant d * delta1 * (delta1 + rdM) +
          8 * delta1 ^ 2 ≤
        20 * (finiteIntegrationVarianceConstant d + 1) * delta1 *
          (delta1 + rM) := by
      nlinarith [mul_nonneg hdelta hrM, sq_nonneg delta1]
    apply hscale.trans
    convert mul_le_mul_of_nonneg_left hinside hD0 using 1
    all_goals ring
  have hCeq : finiteIntegrationCorridorConstant d =
      1000 * (d : ℝ) ^ 2 * (finiteIntegrationVarianceConstant d + 1) := rfl
  have hboth := add_le_add (hcorridor.trans hboundCorridor) hscale'
  rw [hCeq]
  have hamp : 0 ≤ (d : ℝ) ^ 2 * (finiteIntegrationVarianceConstant d + 1) *
      delta1 * (delta1 + rM) := by positivity
  dsimp only [rM] at hboth ⊢
  nlinarith

/-- Public integer-to-natural corridor transport for provider assembly. -/
theorem sum_Icc_int_weighted_toNat_eq_sum_Icc_nat_public
    (L m : ℕ) (F : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc (L : ℤ) (m : ℤ),
        Real.rpow 3 (-((((m : ℤ) - n : ℤ) : ℤ) : ℝ)) * F n.toNat =
      ∑ n ∈ Finset.Icc L m,
        Real.rpow 3 (-((m - n : ℕ) : ℝ)) * F n := by
  refine Finset.sum_bij (fun n _hn => n.toNat) ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hnL, hnm⟩ := Finset.mem_Icc.mp hn
    have hn0 : 0 ≤ n := by omega
    have hcast : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn0
    apply Finset.mem_Icc.mpr
    constructor
    · change L ≤ n.toNat
      exact_mod_cast hcast.symm ▸ hnL
    · change n.toNat ≤ m
      exact_mod_cast hcast.symm ▸ hnm
  · intro a ha b hb hab
    obtain ⟨haL, _ham⟩ := Finset.mem_Icc.mp ha
    obtain ⟨hbL, _hbm⟩ := Finset.mem_Icc.mp hb
    have ha0 : 0 ≤ a := by omega
    have hb0 : 0 ≤ b := by omega
    change a.toNat = b.toNat at hab
    have hacast : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha0
    have hbcast : ((b.toNat : ℕ) : ℤ) = b := Int.toNat_of_nonneg hb0
    omega
  · intro n hn
    refine ⟨(n : ℤ), ?_, by simp⟩
    simpa using hn
  · intro n hn
    obtain ⟨hnL, hnm⟩ := Finset.mem_Icc.mp hn
    have hn0 : 0 ≤ n := by omega
    have hdiff : (((m : ℤ) - n : ℤ) : ℝ) = ((m - n.toNat : ℕ) : ℝ) := by
      congr 1
      omega
    rw [hdiff]

/-- Literal integer-corridor form consumed by the integrated expectation
apex. -/
theorem matrixCorridor_int_add_scaleSeparation_le
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m0 L m : ℕ}
    {xi delta1 : ℝ} (hxi : 2 ≤ xi)
    (hS : inductionHypothesis M m0 xi delta1) (hLm0 : L ≤ m0)
    (hLm : L ≤ m) (p q : Vec d)
    (hq : q = ahom M L • p) (hqNorm : vecNormSq q ≤ ahom M L) :
    ahom M L *
        ∑ n ∈ Finset.Icc (L : ℤ) (m : ℤ),
          Real.rpow 3 (-((((m : ℤ) - n : ℤ) : ℤ) : ℝ)) *
            ∫ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
              descendantsAverage (originCube d (m : ℤ)) (((m : ℤ) - n).toNat)
                (coarseMatrixVariationSq (aCutoffRegCoeffField M L omega)
                  (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
                  (originCube d (m : ℤ)) p q) ∂M.P.toMeasure +
      ahom M L *
        ∫ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
          vecNormSq
            (coarseScaleSeparation (aCutoffRegCoeffField M L omega)
              (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
              (originCube d (m : ℤ)) p q) ∂M.P.toMeasure ≤
      finiteIntegrationCorridorConstant d * delta1 *
        (delta1 + Real.rpow 3 (-((m - L : ℕ) : ℝ))) := by
  let F : ℕ → ℝ := fun n =>
    ∫ omega : Sample d,
      descendantsAverage (originCube d (m : ℤ)) (m - n)
        (coarseMatrixVariationSq (aCutoffRegCoeffField M L omega)
          (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
          (originCube d (m : ℤ)) p q) ∂M.P.toMeasure
  have hsum := sum_Icc_int_weighted_toNat_eq_sum_Icc_nat_public L m F
  have hdepth : ∀ n ∈ Finset.Icc (L : ℤ) (m : ℤ),
      (((m : ℤ) - n).toNat : ℕ) = m - n.toNat := by
    intro n hn
    obtain ⟨hnL, hnm⟩ := Finset.mem_Icc.mp hn
    have hn0 : 0 ≤ n := by omega
    omega
  have hsum' :
      ∑ n ∈ Finset.Icc (L : ℤ) (m : ℤ),
          Real.rpow 3 (-((((m : ℤ) - n : ℤ) : ℤ) : ℝ)) *
            ∫ omega : Sample d,
              descendantsAverage (originCube d (m : ℤ)) (((m : ℤ) - n).toNat)
                (coarseMatrixVariationSq (aCutoffRegCoeffField M L omega)
                  (aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega)
                  (originCube d (m : ℤ)) p q) ∂M.P.toMeasure =
        ∑ n ∈ Finset.Icc L m,
          Real.rpow 3 (-((m - n : ℕ) : ℝ)) * F n := by
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hdepth n hn]
  rw [hsum']
  exact matrixCorridor_add_scaleSeparation_le
    M hxi hS hLm0 hLm p q hq hqNorm

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion
