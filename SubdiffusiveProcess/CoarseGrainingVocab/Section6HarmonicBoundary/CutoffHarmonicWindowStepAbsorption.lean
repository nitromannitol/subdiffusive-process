
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.WindowStepAbsorption
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CutoffHarmonicBoundaryCellRowGood

@[expose] public section

/-!
# The window-step energy row and its collapse to the cell row, at a finite cutoff

Cutoff companions of `Section6HarmonicBoundary.BoundaryWindowEnergyStepRow` and
`Section6HarmonicBoundary.boundaryCellManuscriptRow_of_windowStepRow`: the
binder `m ≤ L` is deleted and the good event is `𝒢^{(L)}_{n+2,z}`.  The window
geometry, the cover-scale selection and the energy monotonicity are
deterministic and are quoted unchanged.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- **The window step row `(♠-a)`.**

For the frozen good-scale data, and for every pair of concentric radii
`3ⁿ/3 ≤ ρ < R ≤ 4·3ⁿ/9` (so that both windows lie inside the budget window
`U = truncatedCube d m n x`, by `boundaryWindow_subset_truncatedCube`), the
cutoff energy on the inner window is bounded by a *fixed* fraction `1/16` of
the energy on the outer window plus the four printed budgets with an inverse
cube of the radius gap.

This argument runs at cover depth
`κ = κ(R − ρ)` instead of at the single depth `n − 4`: the contraction `1/16`
is the residual-mean feedback, made small by the tile depth of
`PhysicalFaceTileCap.exists_physicalBoundaryTileResidualMeanCap`, and the
`(R − ρ)⁻³` is the interior coarse-grained Caccioppoli price at cell scale
`κ`, with one spare power of the gap for the descendant transfer of the
ellipticity caps (`TileCoarsePoincare.lambdaS_inv_descendant_le_of_cap`,
`TileEllipticityCaps.exists_localTileEllipticityCap`), whose loss is
`(3ⁿ/(R−ρ))^{2t}` with `t = s/3 ≤ 1/12`.  The factors `(3ⁿ)^d` and `(3ⁿ)^3`
are the normalizations: `windowCutoffEnergy` is an unnormalized integral, and
`harmonicPhysicalFourBudgets` already carries `3^{-2n}` on its parent leg. -/
def BoundaryWindowEnergyStepRow (d : ℕ) (Cstep : ℝ) : Prop :=
  ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (sOrder : FractionalOrder),
    sOrder.1 ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) →
  ∀ (L m n : ℕ), n + 5 ≤ m →
  ∀ (z x : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d),
    z ∈ cube d (m : ℤ) →
    x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
    omega ∈ goodEvent M (some L) (n + 2) z 1 (sOrder.1 / 8) →
  ∀ (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
    (g : Vec d → Vec d),
    IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
        (originCube d (m : ℤ)) u h g →
    Ch03.ABK26.MemCubeEuclideanFullWsp
        (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
    MemFractionalOn (cube d (m : ℤ)) sOrder.1 h.grad →
  ∀ rho R : ℝ, (3 : ℝ) ^ n / 3 ≤ rho → rho < R → R ≤ 4 * (3 : ℝ) ^ n / 9 →
    windowCutoffEnergy M L omega m x u rho ≤
      (1 / 16 : ℝ) * windowCutoffEnergy M L omega m x u R +
        Cstep * ((3 : ℝ) ^ n) ^ d * ((3 : ℝ) ^ n) ^ 3 *
          harmonicPhysicalFourBudgets M L m n z x omega sOrder.1 u h g /
          (R - rho) ^ 3

/-- **The collapse.**  The window step row alone gives the boundary-cell
manuscript row, with the explicit constant `11664 · 729^d · Cstep`.

The three numbers come from the hole-filling engine at `τ = 1/2`, `α = 3`,
`θ = 1/16 < τ³ = 1/8`: the geometric factor is
`(1 - θ/τ³)⁻¹ (1-τ)^{-3} = 2 · 8 = 16`, the radius gap is
`r₁ - r₀ = 3ⁿ/9`, contributing `729`, and the cell-to-window volume ratio is
`729^d` by `Section6ExcessDecay.volume_toReal_truncatedCube_bounds`. -/
theorem boundaryCellManuscriptRow_of_windowStepRow (d : ℕ) {Cstep : ℝ}
    (hCstep : 0 ≤ Cstep) (hrow : BoundaryWindowEnergyStepRow d Cstep) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ BoundaryCellManuscriptRow d Cb := by
  refine ⟨11664 * (729 : ℝ) ^ d * Cstep, by positivity, ?_⟩
  intro M sOrder hs L m n hnm z x q omega hz hx hq _hgate hgood u h g hdir hg hh
  -- the four printed budgets are nonnegative
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hs0 : 0 < sOrder.1 :=
    (mul_pos (by norm_num : (0 : ℝ) < 512) (pow_pos hdelta 2)).trans_le hs.1
  have hB : 0 ≤ harmonicPhysicalFourBudgets M L m n z x omega sOrder.1 u h g :=
    harmonicPhysicalFourBudgets_nonneg M L m n z x omega hs0
      (Section6ExcessDecay.tailAverage_nonneg M L (n + 2) omega _) u h g
  set N : ℝ := (3 : ℝ) ^ n with hN
  have hNpos : (0 : ℝ) < N := by positivity
  set Bud : ℝ := harmonicPhysicalFourBudgets M L m n z x omega sOrder.1 u h g
    with hBud
  set A : ℝ := Cstep * N ^ d * N ^ 3 * Bud with hA
  have hA0 : 0 ≤ A := by positivity
  -- the hole-filling collapse on the concentric family
  have hiter := Section6HarmonicLocalRow.iterate_absorb_le
    (r0 := N / 3) (r1 := 4 * N / 9) (tau := 1 / 2) (theta := 1 / 16)
    (A := A) (B := 0) (alpha := 3)
    (Mbd := ∫ p in cube d (m : ℤ), _root_.SubdiffusiveProcess.Model.aCutoff M L omega p *
      vecNormSq (u.grad p))
    (fun r => windowCutoffEnergy M L omega m x u r)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hA0 le_rfl
    (fun r _ _ => windowCutoffEnergy_le_total M L omega m x u r)
    (fun rho R h1 h2 h3 => by
      have := hrow M sOrder hs L m n hnm z x omega hz hx hgood u h g hdir hg hh
        rho R h1 h2 h3
      simpa [hA, hBud, hN, mul_comm, mul_left_comm, mul_assoc] using this)
  -- evaluate the resulting constant
  have hgap : 4 * N / 9 - N / 3 = N / 9 := by ring
  have hconst : (1 - (1 / 16 : ℝ) / (1 / 2 : ℝ) ^ 3)⁻¹ *
        (A / ((1 - (1 / 2 : ℝ)) ^ 3 * (4 * N / 9 - N / 3) ^ 3)) +
        (1 - (1 / 16 : ℝ))⁻¹ * 0
      = 11664 * (Cstep * N ^ d * Bud) := by
    rw [hgap, hA]
    field_simp
    ring
  rw [hconst] at hiter
  -- transfer the window bound to the cell
  have hqcube : q ∈ cube d (m : ℤ) := hq.2
  have hvol := Section6ExcessDecay.volume_toReal_truncatedCube_bounds
    (m := (m : ℤ)) (j := (n : ℤ) - 4) q hqcube (by omega)
  have hcellsub := truncatedCube_subset_boundaryWindow (d := d) (m := (m : ℤ))
    (n := n) (x := x) (q := q) hq
  have hcellint : ∫ p in truncatedCube d (m : ℤ) ((n : ℤ) - 4) q,
      _root_.SubdiffusiveProcess.Model.aCutoff M L omega p * vecNormSq (u.grad p) ≤
      windowCutoffEnergy M L omega m x u (N / 3) :=
    setIntegral_mono_set
      (integrableOn_cutoffEnergy_boundaryWindow M L omega m x u (N / 3))
      (Filter.Eventually.of_forall fun p => cutoffEnergyDensity_nonneg M L omega u p)
      (LE.le.eventuallySubset hcellsub)
  have hvolpow : ((3 : ℝ) ^ ((n : ℤ) - 4 - 2)) ^ d = N ^ d / (729 : ℝ) ^ d := by
    have h6 : (3 : ℝ) ^ ((n : ℤ) - 4 - 2) = N / 729 := by
      rw [hN, show (n : ℤ) - 4 - 2 = (n : ℤ) - 6 by ring,
        zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
      norm_num
    rw [h6, div_pow]
  have hvollow : N ^ d / (729 : ℝ) ^ d ≤
      (volume (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q)).toReal := by
    rw [← hvolpow]; exact hvol.1
  have hvolpos : (0 : ℝ) < N ^ d / (729 : ℝ) ^ d := by positivity
  have hinvle : (volume (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q)).toReal⁻¹ ≤
      ((729 : ℝ) ^ d) / N ^ d := by
    have hone := one_div_le_one_div_of_le hvolpos hvollow
    calc (volume (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q)).toReal⁻¹
        = 1 / (volume (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q)).toReal := by
          rw [one_div]
      _ ≤ 1 / (N ^ d / (729 : ℝ) ^ d) := hone
      _ = ((729 : ℝ) ^ d) / N ^ d := by
          rw [one_div, inv_div]
  -- assemble
  have hfinal : (volume (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q)).toReal⁻¹ *
      (∫ p in truncatedCube d (m : ℤ) ((n : ℤ) - 4) q,
        _root_.SubdiffusiveProcess.Model.aCutoff M L omega p * vecNormSq (u.grad p)) ≤
      11664 * (729 : ℝ) ^ d * Cstep * Bud := by
    have hnum : (∫ p in truncatedCube d (m : ℤ) ((n : ℤ) - 4) q,
        _root_.SubdiffusiveProcess.Model.aCutoff M L omega p * vecNormSq (u.grad p)) ≤
        11664 * (Cstep * N ^ d * Bud) := hcellint.trans hiter
    have hnum0 : 0 ≤ 11664 * (Cstep * N ^ d * Bud) := by positivity
    calc (volume (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q)).toReal⁻¹ *
          (∫ p in truncatedCube d (m : ℤ) ((n : ℤ) - 4) q,
            _root_.SubdiffusiveProcess.Model.aCutoff M L omega p * vecNormSq (u.grad p))
        ≤ (volume (truncatedCube d (m : ℤ) ((n : ℤ) - 4) q)).toReal⁻¹ *
            (11664 * (Cstep * N ^ d * Bud)) :=
          mul_le_mul_of_nonneg_left hnum (by positivity)
      _ ≤ ((729 : ℝ) ^ d / N ^ d) * (11664 * (Cstep * N ^ d * Bud)) :=
          mul_le_mul_of_nonneg_right hinvle hnum0
      _ = 11664 * (729 : ℝ) ^ d * Cstep * Bud := by
          field_simp
  simpa [normalizedSetAverage, Homogenization.volumeAverage, hBud, mul_assoc]
    using hfinal

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffHarmonic
