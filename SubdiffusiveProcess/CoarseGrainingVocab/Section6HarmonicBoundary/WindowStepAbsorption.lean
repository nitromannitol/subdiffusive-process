module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.BoundaryCellRowGood
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow.AdjustableAbsorption
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCoerciveIntegrability
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.Windows

@[expose] public section

/-!
# `(♠-a)`: the window-matched absorption, and the row it leaves

After the tile route the boundary cell row reduces to
absorbing `ε · ⨍_{P_q} aCutoff ‖∇u‖²` with `ε` free, where `P_q` is the cell's
*own* well-placed scale-`(n-2)` parent.  The union of those parents is the
scale-`(n-1)` window, not the fixed `D = translatedCube d (n-2) y` of the
v6 statement, and a fixed comparison of the two averages is
machine-refuted
(`Section6HarmonicLocalRow.CoverAbsorptionObstruction.descendantsAverage_remainder_not_le_of_pos`).

This file proves closer `(♠-a)`: the absorption is performed **between two
concentric windows** rather than against one fixed cube, which is what the free
`ε` is for.  The point is a geometric one about the manuscript's cover: the cover of `D` into `9^d` cells
`q + 𝔠_{n-4}` with projected parents `P_q` of scale `n-2` is *one member of a
family*.  Covering instead by cells of scale `κ ≤ n-4` with projected parents
of scale `κ+2` keeps the whole construction — the interior coarse-grained
Caccioppoli, the ASD lemma `l.coarse.grained.Caccioppoli.RHS.ASD`
 on the projected parent, the separation
`(q+𝔠_{κ-1}) ∩ (∂P_q ∖ ∂𝔠_m) = ∅`, and the tile price of
`PhysicalFaceTileCap.lean` — while shrinking the parents' overhang past the
window being estimated to `C 3^{κ}`.  The overhang is therefore a *free* gap,
the interior Caccioppoli price at cell scale `κ` is the corresponding
`(gap)^{-2}`, and the residual-mean feedback stays free by the tile depth.
That is exactly the hypothesis shape of the proved hole-filling engine
`Section6HarmonicLocalRow.iterate_absorb_le` (Giaquinta, Lemma V.3.1), and it
is *not* the fixed-cover comparison that `CoverAbsorptionObstruction` refutes:
here the feedback window is a strict dilation of the estimated one and the
price blows up as the dilation closes.

What is proved:

* `boundaryWindow`, `windowCutoffEnergy` — the concentric family and the
  unnormalized cutoff energy on it, with monotonicity, the containment of the
  scale-`n` window (so every radius used stays inside the budget window `U`),
  and the cell containment at the inner radius;
* `BoundaryWindowEnergyStepRow` — the single remaining analytic input, stated
  with a *fixed* contraction `1/16` and a free radius gap;
* `boundaryCellManuscriptRow_of_windowStepRow` — the collapse: that row alone
  gives `BoundaryCellManuscriptRow d Cb` with an explicit dimension-only
  constant, hence (through `ConclusionAssembly.harmonic_approximation_good_scales_of_cellRow`)
  the entire v6 anchor.

No statement is weakened: the conclusion is the committed
`BoundaryCellManuscriptRow`, and the new hypothesis is a *two-window* estimate
that the fixed-window obstruction does not touch.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- The sup-norm window of radius `r` about `x`, truncated to the domain cube
`𝔠_m`.  Unlike `truncatedCube` this family is indexed by a *real* radius, which
is what the hole-filling iteration needs. -/
def boundaryWindow (d : ℕ) (m : ℤ) (x : Vec d) (r : ℝ) : Set (Vec d) :=
  {p : Vec d | ∀ i, |p i - x i| ≤ r} ∩ cube d m

theorem boundaryWindow_subset_cube (m : ℤ) (x : Vec d) (r : ℝ) :
    boundaryWindow d m x r ⊆ cube d m := fun _ hp => hp.2

theorem boundaryWindow_mono (m : ℤ) (x : Vec d) {r r' : ℝ} (hr : r ≤ r') :
    boundaryWindow d m x r ⊆ boundaryWindow d m x r' := by
  rintro p ⟨hp1, hp2⟩
  exact ⟨fun i => (hp1 i).trans hr, hp2⟩

/-- Every window of radius `< 3ⁿ/2` sits inside the budget window
`U = truncatedCube d m n x`: the iteration never leaves the cube on which the
four printed budgets are measured. -/
theorem boundaryWindow_subset_truncatedCube {m n : ℤ} (x : Vec d) {r : ℝ}
    (hr : r < (3 : ℝ) ^ n / 2) :
    boundaryWindow d m x r ⊆ truncatedCube d m n x := by
  rintro p ⟨hp1, hp2⟩
  refine ⟨?_, hp2⟩
  rw [Section6ExcessDecay.mem_translatedCube_iff, cube,
    Homogenization.mem_openCubeSet_originCube_iff]
  intro i
  have hpi : |p i - x i| ≤ r := hp1 i
  have habs := abs_le.1 hpi
  have hsub : (p - x) i = p i - x i := by simp
  constructor
  · rw [hsub]; linarith [habs.1]
  · rw [hsub]; linarith [habs.2]

/-- The cell of the manuscript cover sits inside the inner window of radius
`3ⁿ/3`.  This is the containment that converts the window estimate into the
per-cell row. -/
theorem truncatedCube_subset_boundaryWindow {m : ℤ} {n : ℕ} {x q : Vec d}
    (hq : q ∈ truncatedCube d m ((n : ℤ) - 1) x) :
    truncatedCube d m ((n : ℤ) - 4) q ⊆ boundaryWindow d m x ((3 : ℝ) ^ n / 3) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hNpos : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hq1 : q - x ∈ cube d ((n : ℤ) - 1) :=
    (Section6ExcessDecay.mem_translatedCube_iff).1 hq.1
  rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at hq1
  rintro p ⟨hp1, hp2⟩
  refine ⟨?_, hp2⟩
  intro i
  have hp1' : p - q ∈ cube d ((n : ℤ) - 4) :=
    (Section6ExcessDecay.mem_translatedCube_iff).1 hp1
  rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at hp1'
  have hsub1 : (p - q) i = p i - q i := by simp
  have hsub2 : (q - x) i = q i - x i := by simp
  have h4 : (3 : ℝ) ^ ((n : ℤ) - 4) = (3 : ℝ) ^ n / 81 := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
    norm_num
  have h1 : (3 : ℝ) ^ ((n : ℤ) - 1) = (3 : ℝ) ^ n / 3 := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
    norm_num
  have hA := hp1' i
  have hB := hq1 i
  rw [hsub1, h4] at hA
  rw [hsub2, h1] at hB
  rw [abs_le]
  constructor <;> [linarith [hA.1, hB.1]; linarith [hA.2, hB.2]]

/-- The whole scale-`(n-1)` window — hence the outer cube
`D = translatedCube d (n-2) y` for *every* admissible `y` — sits inside the
inner window of the step row.  So a bound at the inner radius bounds the energy
on `D` for every choice of `y` at once. -/
theorem truncatedCube_pred_subset_boundaryWindow {m : ℤ} {n : ℕ} (x : Vec d) :
    truncatedCube d m ((n : ℤ) - 1) x ⊆ boundaryWindow d m x ((3 : ℝ) ^ n / 3) := by
  intro p hp
  refine ⟨?_, hp.2⟩
  intro i
  have hpx : p - x ∈ cube d ((n : ℤ) - 1) :=
    Section6ExcessDecay.sub_mem_cube_of_mem_truncatedCube hp
  rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at hpx
  have h1 : (3 : ℝ) ^ ((n : ℤ) - 1) = (3 : ℝ) ^ n / 3 := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
    norm_num
  have hi := hpx i
  have hsub : (p - x) i = p i - x i := by simp
  rw [hsub, h1] at hi
  have hpos : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  rw [abs_le]
  constructor <;> [linarith [hi.1]; linarith [hi.2]]

/-- **The overhang of a projected parent is one cell-parent side.**

For a cell centre `q` in the window of radius `ρ`, the manuscript's
coordinatewise projection `wellPlacedCentre q m k` (proved as `Section6ExcessDecay.wellPlacedCentre`) produces a parent
`P_q = q̂ + 𝔠_k` that stays inside `𝔠_m` and overhangs the window by at most
`3^{k+1}/2`.

This is the geometric heart of `(♠-a)`: at the manuscript's own cover depth
(`k = n-2`) the overhang is comparable to the window itself, which is what
makes the fixed-cover absorption impossible
(`Section6HarmonicLocalRow.CoverAbsorptionObstruction`); but the overhang is
proportional to `3^k`, and `k` is free, so at cover depth `k` the feedback
window is a *dilation by a free gap*, which is exactly what the hole-filling
iteration consumes. -/
theorem translatedCube_wellPlacedCentre_subset_boundaryWindow {m k : ℤ}
    {q x : Vec d} {rho : ℝ} (hkm : k ≤ m) (hq : q ∈ boundaryWindow d m x rho) :
    translatedCube d k (Section6ExcessDecay.wellPlacedCentre q m k) ⊆
      boundaryWindow d m x (rho + (3 : ℝ) ^ (k + 1) / 2) := by
  intro p hp
  have hqm : q ∈ cube d m := hq.2
  have hpin : p ∈ truncatedCube d m (k + 1) q := by
    have := Section6ExcessDecay.translatedCube_wellPlacedCentre_subset_truncatedCube
      (d := d) (m := m) (j := k + 1) q hqm (by omega)
    exact this (by simpa using hp)
  refine ⟨?_, hpin.2⟩
  intro i
  have hpq : p - q ∈ cube d (k + 1) :=
    Section6ExcessDecay.sub_mem_cube_of_mem_truncatedCube hpin
  rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at hpq
  have hi := hpq i
  have hsub : (p - q) i = p i - q i := by simp
  rw [hsub] at hi
  have hqi : |q i - x i| ≤ rho := hq.1 i
  have habs := abs_le.1 hqi
  rw [abs_le]
  constructor <;> [linarith [hi.1, habs.1]; linarith [hi.2, habs.2]]

/-- **A cover scale exists below every gap.**  Since the cover depth ranges
over all integers, the overhang `3^{k+1}/2` of the previous lemma can be made
smaller than any prescribed radius gap.  Together the two lemmas say that the
manuscript's projected cover, run at depth `k`, produces a feedback window
`boundaryWindow d m x R` with `R - ρ` arbitrarily small — the hypothesis shape
of `BoundaryWindowEnergyStepRow`. -/
theorem exists_coverScale_le_gap (m : ℤ) {delta : ℝ} (hdelta : 0 < delta) :
    ∃ k : ℤ, k ≤ m ∧ (3 : ℝ) ^ (k + 1) / 2 ≤ delta := by
  have h3m : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) _
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < 2 * delta / (3 : ℝ) ^ m by positivity)
    (show (1 : ℝ) / 3 < 1 by norm_num)
  refine ⟨m - (N : ℤ) - 1, by omega, ?_⟩
  have hkey : (3 : ℝ) ^ (m - (N : ℤ) - 1 + 1) = (3 : ℝ) ^ m * (1 / 3 : ℝ) ^ N := by
    rw [show m - (N : ℤ) - 1 + 1 = m - (N : ℤ) by ring,
      zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast, div_pow, one_pow]
    field_simp
  rw [hkey]
  have hlt : (3 : ℝ) ^ m * (1 / 3 : ℝ) ^ N ≤ (3 : ℝ) ^ m * (2 * delta / (3 : ℝ) ^ m) :=
    mul_le_mul_of_nonneg_left hN.le h3m.le
  have hcalc : (3 : ℝ) ^ m * (2 * delta / (3 : ℝ) ^ m) = 2 * delta := by
    field_simp
  linarith [hlt, hcalc ▸ hlt]

/-- The unnormalized cutoff energy of the solution on the window of radius
`r`. -/
def windowCutoffEnergy (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (m : ℕ) (x : Vec d)
    (u : H1Function (openCubeSet (originCube d (m : ℤ)))) (r : ℝ) : ℝ :=
  ∫ p in boundaryWindow d (m : ℤ) x r,
    _root_.SubdiffusiveProcess.Model.aCutoff M L omega p * vecNormSq (u.grad p)

theorem cutoffEnergyDensity_nonneg (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (L : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) {m : ℕ}
    (u : H1Function (openCubeSet (originCube d (m : ℤ)))) (p : Vec d) :
    0 ≤ _root_.SubdiffusiveProcess.Model.aCutoff M L omega p * vecNormSq (u.grad p) :=
  mul_nonneg (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega p).le
    (vecNormSq_nonneg _)

theorem integrableOn_cutoffEnergy_boundaryWindow
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (m : ℕ) (x : Vec d)
    (u : H1Function (openCubeSet (originCube d (m : ℤ)))) (r : ℝ) :
    IntegrableOn (fun p => _root_.SubdiffusiveProcess.Model.aCutoff M L omega p *
      vecNormSq (u.grad p)) (boundaryWindow d (m : ℤ) x r) :=
  (integrableOn_aCutoff_energy M L omega (originCube d (m : ℤ)) u).mono_set
    (boundaryWindow_subset_cube (m : ℤ) x r)

theorem windowCutoffEnergy_mono (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (m : ℕ) (x : Vec d)
    (u : H1Function (openCubeSet (originCube d (m : ℤ)))) {r r' : ℝ}
    (hr : r ≤ r') :
    windowCutoffEnergy M L omega m x u r ≤ windowCutoffEnergy M L omega m x u r' :=
  setIntegral_mono_set (integrableOn_cutoffEnergy_boundaryWindow M L omega m x u r')
    (Filter.Eventually.of_forall fun p => cutoffEnergyDensity_nonneg M L omega u p)
    (LE.le.eventuallySubset (boundaryWindow_mono (m : ℤ) x hr))

/-- The window energies are bounded by the total cutoff energy on `𝔠_m`, which
is finite because `u ∈ H¹` and the cutoff coefficient is a bounded-flux
coefficient field.  This is the `hbdd` slot of the hole-filling engine. -/
theorem windowCutoffEnergy_le_total (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (L : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (m : ℕ)
    (x : Vec d) (u : H1Function (openCubeSet (originCube d (m : ℤ)))) (r : ℝ) :
    windowCutoffEnergy M L omega m x u r ≤
      ∫ p in cube d (m : ℤ), _root_.SubdiffusiveProcess.Model.aCutoff M L omega p *
        vecNormSq (u.grad p) :=
  setIntegral_mono_set (integrableOn_aCutoff_energy M L omega (originCube d (m : ℤ)) u)
    (Filter.Eventually.of_forall fun p => cutoffEnergyDensity_nonneg M L omega u p)
    (LE.le.eventuallySubset (boundaryWindow_subset_cube (m : ℤ) x r))

/-- **The window step row `(♠-a)`.**

For the good-scale data, and for every pair of concentric radii
`3ⁿ/3 ≤ ρ < R ≤ 4·3ⁿ/9` (so that both windows lie inside the budget window
`U = truncatedCube d m n x`, by `boundaryWindow_subset_truncatedCube`), the
cutoff energy on the inner window is bounded by a *fixed* fraction `1/16` of
the energy on the outer window plus the four printed budgets with an inverse
cube of the radius gap.

This is the manuscript's  argument run at cover depth
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
  ∀ (L m n : ℕ), m ≤ L → n + 5 ≤ m →
  ∀ (z x : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d),
    z ∈ cube d (m : ℤ) →
    x ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 3) z →
    omega ∈ goodEvent M none (n + 2) z 1 (sOrder.1 / 8) →
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
  intro M sOrder hs L m n hmL hnm z x q omega hz hx hq _hgate hgood u h g hdir hg hh
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
      have := hrow M sOrder hs L m n hmL hnm z x omega hz hx hgood u h g hdir hg hh
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

/-- The v6 anchor from the window step row, through the proved
`harmonic_approximation_good_scales_of_cellRow`. -/
theorem exists_harmonicApproximationGoodScales_of_windowStepRow (d : ℕ) [NeZero d]
    {Cstep : ℝ} (hCstep : 0 ≤ Cstep) (hrow : BoundaryWindowEnergyStepRow d Cstep) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ BoundaryCellManuscriptRow d Cb :=
  boundaryCellManuscriptRow_of_windowStepRow d hCstep hrow

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
