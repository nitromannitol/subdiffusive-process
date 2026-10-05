
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowSlotsCoarseBudget
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowSlotsEnlargementMass
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionRepairedBudget

@[expose] public section

/-!
# The flux energy slot on the repaired stopping family

`FluxRowSlotsCoarseBudget.lean` closed the flux row's energy slot for a single
cell and named the one remaining family-level input,

```
FluxRowSlotsFamilyCoarseEnergyBound u eta scale centre :
  ∀ q, ∫_{z_q + □_{m_q}} a |∇u|² ≤ eta · t⁻¹ · ∫_{z_q + □_{m_q+1}} u² ,
```

together with the per-cell theorem that produces each instance,
`wholeSpaceSolution_translatedCell_coarse_energy_le_of_paper_condition`, whose
only non-mechanical hypothesis is the manuscript's coarse condition

```
t · (Λ_{1/16}^{12} λ_{1/16}^{-11}) ≤ (81 c³)⁻¹ η⁴
```

on the cell's **own** coarse ellipticity.

This file supplies that family input for the **repaired stopping family**.  The
repaired construction is parametrized by an abstract failure event
`failure : TriadicCube d → Set Omega`, and the proved certificate mechanism is

```
refinedStoppingCell_property_of_not_mem_failure :
  (∀ Q, omega ∉ failure Q → Good Q) → ∀ q, Good (refinedStoppingFailureCube q)
```

(`StoppingPartitionHalfGridRefinement.lean`; the flux-row form is
`repairedFluxRowRieszStoppingFamily_property_of_not_mem_failure`).  So the
stopping rule's threshold enters as the `Good` predicate, and the content of
this file is: *which* `Good` closes the flux energy slot, and the proof that it
does.

The answer is `FluxRowSlotsCubeCoarseEllipticity`: the selected cube carries
coarse-ellipticity constants on its **ninefold** enlargement satisfying the
manuscript's threshold.  The ninefold enlargement — not the threefold one — is
forced by the half-grid refinement: a refined cell is the selected cube's scale
paired with one of the `7^d` half-grid offsets, so its own threefold
enlargement is a cube of the same scale sitting up to `3/2 · 3^m` away from the
selected cube's centre (§1).

## Contents

* §1 `translatedCube_succ_stoppingRelativeGridCentre_subset` — the half-grid
  geometry: every refined cell's enlargement sits in the selected cube's
  ninefold enlargement.
* §2 `FluxRowSlotsCellCoarseEllipticity`, `FluxRowSlotsCubeCoarseEllipticity`,
  the transfer between them, and
  `exists_pos_fluxRowSlotsCubeCoarseEllipticity` — the certificate is
  satisfiable (contrast the refuted crude budget).
* §3 `FluxRowSlotsCellCoarseData` — the per-cell *analytic* inputs of the
  coarse Caccioppoli (mesoscopic scale, cutoff, the two mesoscopic legs,
  vanishing source), which carry no ellipticity constant; and
  `wholeSpaceSolution_translatedCell_coarse_energy_le_of_cellCertificate`,
  which consumes them together with §2.
* §4 `wholeSpaceSolution_fluxRowSlots_familyCoarseEnergyBound_refinedStoppingCell`
  — the residual of `FluxRowSlotsCoarseBudget.lean` §5, discharged for the
  repaired family from the stopping rule's own threshold.
* §5 `exists_eta_fluxRowSlots_coarse_budget_of_const` and
  `repairedStoppingCell_coarse_budget_and_scale` — the coarse replacement of
  the crude `RepairedStoppingTSmallnessBudget`, which this collection deleted from
  `StoppingPartitionRepairedBudget.lean`.
* §6 `wholeSpaceSolution_fluxRowSlots_energy_slot_coarse_const` and
  `wholeSpaceSolution_fluxRowSlots_energy_slot_coarse_repairedStoppingCell` —
  the flux energy slot on the repaired family, end to end, in the shape
  consumed by `exists_fluxRowRiesz_repairedStoppingCell_localFluxPrice`.
* §7 `wholeSpaceSolution_fluxRowSlots_energy_slot_coarse_repairedStoppingCell_of_certificate`
  — the same, with §4 chained in, so the only stopping-rule input is `hgood`.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Section8
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The half-grid geometry -/

/-- **A refined cell's enlargement sits in the selected cube's ninefold
enlargement.**

A refined stopping cell has the scale `n` of its selected cube and a centre
`c + gridCentre d n k` with `|k i| ≤ 3`, so its centre is at most `3/2 · 3^n`
from `c` in each coordinate, and its threefold enlargement — of half-width
`3/2 · 3^n` — is inside the cube of half-width `9/2 · 3^n` centred at `c`. -/
theorem translatedCube_succ_stoppingRelativeGridCentre_subset
    (n : ℤ) (c : Vec d) {k : Fin d → ℤ}
    (hk : k ∈ gridNeighbours d (0 : Fin d → ℤ)) :
    translatedCube d (n + 1) (stoppingRelativeGridCentre n c k) ⊆
      translatedCube d (n + 2) c := by
  intro x hx
  rw [mem_translatedCube_iff_abs] at hx ⊢
  intro i
  have hpow : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hki : |(k i : ℝ)| ≤ 3 := by
    have hnat : (k i - 0).natAbs ≤ 3 := (mem_gridNeighbours_iff (d := d)).mp hk i
    have hzl : (-3 : ℤ) ≤ k i := by omega
    have hzr : k i ≤ (3 : ℤ) := by omega
    have hrl : (-3 : ℝ) ≤ (k i : ℝ) := by exact_mod_cast hzl
    have hrr : (k i : ℝ) ≤ (3 : ℝ) := by exact_mod_cast hzr
    exact abs_le.mpr ⟨hrl, hrr⟩
  have hcoord : (stoppingRelativeGridCentre n c k) i =
      c i + (k i : ℝ) * gridHalfWidth n := rfl
  have hxi := hx i
  rw [hcoord] at hxi
  have habs : |(k i : ℝ) * gridHalfWidth n| ≤ 3 * ((3 : ℝ) ^ n / 2) := by
    rw [abs_mul, abs_of_pos (gridHalfWidth_pos n)]
    have hw : gridHalfWidth n = (3 : ℝ) ^ n / 2 := by
      unfold gridHalfWidth; ring
    rw [hw]
    exact mul_le_mul_of_nonneg_right hki (by positivity)
  have hsplit : |x i - c i| ≤
      |x i - (c i + (k i : ℝ) * gridHalfWidth n)| +
        |(k i : ℝ) * gridHalfWidth n| := by
    have hmid : |(c i + (k i : ℝ) * gridHalfWidth n) - c i| =
        |(k i : ℝ) * gridHalfWidth n| := by ring_nf
    have := abs_sub_le (x i) (c i + (k i : ℝ) * gridHalfWidth n) (c i)
    rwa [hmid] at this
  have hone : (3 : ℝ) ^ (n + 1) / 2 = 3 * (3 : ℝ) ^ n / 2 := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]; ring
  have htwo : (3 : ℝ) ^ (n + 2) / 2 = 9 * (3 : ℝ) ^ n / 2 := by
    rw [show (n : ℤ) + 2 = n + 1 + 1 by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0),
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  rw [hone] at hxi
  rw [htwo]
  linarith

/-! ## 2. The coarse-ellipticity certificate -/

/-- **The manuscript's coarse-ellipticity threshold on one cell, at the cell's
own scale.**

The cell `z + □_m` has coarse-ellipticity constants `lam ≤ Lam` on its
threefold enlargement satisfying the two scale-free comparisons of
`coarse_contraction_smallness_of_paper_condition` and the manuscript's
condition

```
t ℓ⁻² Λ_{1/16}^{12} λ_{1/16}^{-11} ≤ C⁻¹ η^{15/2}
```

at `ℓ = 3^m` (the repo's normalization of the
constant is `C = 81 c³` and `η^{15/2} ↦ η⁴`, fixed by
`coarse_contraction_smallness_of_paper_condition`).

`R` is the **scale-free** mesoscopic price constant: the cell's own price
constant is `R · 3^{-m}`, because `MesoscopicCrossPriceEnergyOn` prices the
cross term `|2∫ a χ u ∇u·∇χ|` and `|∇χ| ≲ 3^{-m}` on a scale-`m` cell.  So
`hRc : R² ≤ c Λ` keeps its scale-free shape and the whole scale of the
manuscript's condition is carried by the `ℓ⁻²` factor.  The cell-budget argument proves that
without this factor the stopping rule's failure event is monotone along the
ancestor chain and no geometric decay is possible. -/
def FluxRowSlotsCellCoarseEllipticity (a : Vec d → ℝ) (t eta R cst Theta : ℝ)
    (m : ℤ) (z : Vec d) : Prop :=
  ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
    IsEllipticFieldOn lam Lam (translatedCube d (m + 1) z)
      (scalarCoeffField a) ∧
    R ^ 2 ≤ cst * Lam ∧
    Theta ^ 4 * Lam ≤ Lam ^ 12 * lam⁻¹ ^ 11 ∧
    t * (((3 : ℝ) ^ m)⁻¹ ^ 2 * (Lam ^ 12 * lam⁻¹ ^ 11)) ≤
      (81 * cst ^ 3)⁻¹ * eta ^ 4

/-- **The stopping rule's threshold, as a property of the selected cube.**

This is the `Good` predicate of
`refinedStoppingCell_property_of_not_mem_failure`: the cube's *ninefold*
enlargement carries coarse-ellipticity constants meeting the manuscript's
threshold at the cube's own side length `ℓ = 3^{Q.scale}`.  The ninefold
enlargement is what §1 shows is needed to serve every one of the cube's `7^d`
half-grid refinements.

The `3^{-2·Q.scale}` in the threshold is the manuscript's `ℓ⁻²`; it is what
makes the certificate *easier* on larger cubes, so that the failure event is no
longer monotone along the ancestor chain and the manuscript's
`P[𝖥(Q)] ≤ 3^{-2q(j+1)}`  becomes possible.
See `FluxRowSlotsFailureEvent.lean` §4. -/
def FluxRowSlotsCubeCoarseEllipticity (a : Vec d → ℝ) (t eta R cst Theta : ℝ)
    (Q : TriadicCube d) : Prop :=
  ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
    IsEllipticFieldOn lam Lam
      (translatedCube d (Q.scale + 2) (cubeCenter Q)) (scalarCoeffField a) ∧
    R ^ 2 ≤ cst * Lam ∧
    Theta ^ 4 * Lam ≤ Lam ^ 12 * lam⁻¹ ^ 11 ∧
    t * (((3 : ℝ) ^ Q.scale)⁻¹ ^ 2 * (Lam ^ 12 * lam⁻¹ ^ 11)) ≤
      (81 * cst ^ 3)⁻¹ * eta ^ 4

/-- The cube certificate serves every one of the cube's half-grid cells. -/
theorem FluxRowSlotsCubeCoarseEllipticity.cell {a : Vec d → ℝ}
    {t eta R cst Theta : ℝ} {Q : TriadicCube d}
    (h : FluxRowSlotsCubeCoarseEllipticity a t eta R cst Theta Q)
    {k : Fin d → ℤ} (hk : k ∈ gridNeighbours d (0 : Fin d → ℤ)) :
    FluxRowSlotsCellCoarseEllipticity a t eta R cst Theta Q.scale
      (stoppingRelativeGridCentre Q.scale (cubeCenter Q) k) := by
  obtain ⟨lam, Lam, hlam, hlamLam, hEll, hRc, hdom, hcond⟩ := h
  refine ⟨lam, Lam, hlam, hlamLam, ?_, hRc, hdom, hcond⟩
  refine IsEllipticFieldOn.mono hEll
    (isOpenBoundedConvexDomain_translatedCube (d := d) (Q.scale + 1)
      (stoppingRelativeGridCentre Q.scale (cubeCenter Q) k)).isOpen.measurableSet
    (translatedCube_succ_stoppingRelativeGridCentre_subset Q.scale
      (cubeCenter Q) hk)


/-- **The certificate is a genuine `t`-smallness, not an empty condition.**

The crude budget it replaces had *no* solution for the repaired family
(`not_exists_fluxRowSlotsGrowthRatioBound_refinedStoppingCell_empty`,
`not_exists_uniform_stoppingCellLinearUpperBound_empty`).  This one has one on
every cube whose coefficient is elliptic on the ninefold enlargement: with the
contraction factor `eta` chosen first, the manuscript's threshold is met by
every `t` below `(81 c³)⁻¹ η⁴ / (Λ^{12} λ^{-11})`, which is positive.  That is
the manuscript's own order of quantifiers  and the reason the
condition is scale-local: nothing here is uniform over the family. -/
theorem exists_pos_fluxRowSlotsCubeCoarseEllipticity {a : Vec d → ℝ}
    {lam Lam eta R cst Theta : ℝ} {Q : TriadicCube d}
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hEll : IsEllipticFieldOn lam Lam
      (translatedCube d (Q.scale + 2) (cubeCenter Q)) (scalarCoeffField a))
    (hRc : R ^ 2 ≤ cst * Lam)
    (hdom : Theta ^ 4 * Lam ≤ Lam ^ 12 * lam⁻¹ ^ 11)
    (hc : 0 < cst) (heta : 0 < eta) :
    ∃ t0 : ℝ, 0 < t0 ∧ ∀ t : ℝ, t ≤ t0 →
      FluxRowSlotsCubeCoarseEllipticity a t eta R cst Theta Q := by
  have hLam : 0 < Lam := lt_of_lt_of_le hlam hlamLam
  have hB : 0 < (81 * cst ^ 3)⁻¹ * eta ^ 4 := by positivity
  have h3 : (0 : ℝ) < (3 : ℝ) ^ Q.scale := zpow_pos (by norm_num) _
  have hD : 0 < ((3 : ℝ) ^ Q.scale)⁻¹ ^ 2 * (Lam ^ 12 * lam⁻¹ ^ 11) := by
    positivity
  refine ⟨(81 * cst ^ 3)⁻¹ * eta ^ 4 /
    (((3 : ℝ) ^ Q.scale)⁻¹ ^ 2 * (Lam ^ 12 * lam⁻¹ ^ 11)), div_pos hB hD, ?_⟩
  intro t ht
  refine ⟨lam, Lam, hlam, hlamLam, hEll, hRc, hdom, ?_⟩
  calc t * (((3 : ℝ) ^ Q.scale)⁻¹ ^ 2 * (Lam ^ 12 * lam⁻¹ ^ 11))
      ≤ ((81 * cst ^ 3)⁻¹ * eta ^ 4 /
            (((3 : ℝ) ^ Q.scale)⁻¹ ^ 2 * (Lam ^ 12 * lam⁻¹ ^ 11))) *
          (((3 : ℝ) ^ Q.scale)⁻¹ ^ 2 * (Lam ^ 12 * lam⁻¹ ^ 11)) :=
        mul_le_mul_of_nonneg_right ht hD.le
    _ = (81 * cst ^ 3)⁻¹ * eta ^ 4 := div_mul_cancel₀ _ hD.ne'

/-! ## 3. The per-cell analytic data, and the coarse Caccioppoli from it -/

/-- **The per-cell analytic inputs of the coarse Caccioppoli.**

Everything `wholeSpaceSolution_translatedCell_coarse_energy_le_of_paper_condition`
asks about the cell `z + □_m` *except* its ellipticity constants: a mesoscopic
scale `k ≤ m - 3`, a cutoff adapted to the cell, the vanishing of the source on
the enlargement, and the two mesoscopic legs (the cross-price legs on the
triadic price cells of the box and the coarse-energy legs on the mesoscopic
cells).  None of these carries `Λ` or `λ`, which is exactly why the stopping
rule's certificate has to supply only `FluxRowSlotsCellCoarseEllipticity`.

Here `R` is the **cell's own** mesoscopic price constant, which is
dimensionful: consumers instantiate it at `R₀ · 3^{-m}` for the scale-free
constant `R₀` carried by the certificate (see
`FluxRowSlotsCellCoarseEllipticity`). -/
def FluxRowSlotsCellCoarseData {a f : Vec d → ℝ} {t : ℝ}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (P R Sc Gam0 : ℝ) (m : ℤ) (z : Vec d) : Prop :=
  ∃ (k : ℤ) (chi : Vec d → ℝ) (K : ℝ),
    k ≤ m - 3 ∧
    (∀ x ∈ translatedCube d (m + 1) z, f x = 0) ∧
    ContDiff ℝ (⊤ : ℕ∞) chi ∧
    HasCompactSupport chi ∧
    tsupport chi ⊆ {x : Vec d | ∀ i, |x i - z i| ≤ 3 / 4 * (3 : ℝ) ^ m} ∧
    (∀ x, |chi x| ≤ 1) ∧
    (∀ x ∈ translatedCube d m z, chi x = 1) ∧
    (∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤ K) ∧
    IntegrableOn (fun x => a x * chi x * u.toFun x *
      vecDot (u.grad x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)))
      (translatedCube d (m + 1) z) volume ∧
    (∀ j ∈ priceIndexBox d k z (3 / 4 * (3 : ℝ) ^ m),
      MesoscopicCrossPriceEnergyOn a (openCubeSet (priceCell d k j))
        (openCubeSet (priceCell d k j)) u.toFun u.grad chi t P R Sc) ∧
    (∀ j ∈ mesoIndexBox d k (m + 1) z,
      CoarseEnergyBoundOn a (mesoCell d k j) (mesoCore d k j) u.toFun u.grad
        t Gam0)

/-- **The coarse Caccioppoli on a cell, from the cell's certificate.**

`wholeSpaceSolution_translatedCell_coarse_energy_le_of_paper_condition` with
the ellipticity constants and the manuscript's threshold read off the
certificate, and everything else read off the analytic data.  The remaining
hypotheses are the global constants, none of which
depends on the cell. -/
theorem wholeSpaceSolution_translatedCell_coarse_energy_le_of_cellCertificate
    {a f : Vec d → ℝ} {t eta P R Sc Gam0 cst Theta : ℝ} {m : ℤ} {z : Vec d}
    (haNonneg : ∀ x, 0 ≤ a x) (ht : 0 < t) (heta : 0 < eta)
    (hP : 0 < P) (hGam0 : 0 < Gam0) (hR : 0 ≤ R) (hSc : 0 ≤ Sc)
    (hbeta1 : eta ≤ 3 * (P * (Gam0 * 27 ^ d + Sc)))
    (hc : 0 < cst) (hTheta : 1 ≤ Theta)
    (hPS : (P * (Gam0 * 27 ^ d + Sc)) ^ 2 ≤ cst * Theta ^ 3)
    (hGam : Gam0 * 27 ^ d + Sc ≤ cst * Theta)
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hdata : FluxRowSlotsCellCoarseData u P (R * ((3 : ℝ) ^ m)⁻¹) Sc Gam0 m z)
    (hcert : FluxRowSlotsCellCoarseEllipticity a t eta R cst Theta m z) :
    (∫ x in translatedCube d m z, a x * vecNormSq (u.grad x) ∂volume) ≤
      eta * t⁻¹ * ∫ x in translatedCube d (m + 1) z, u.toFun x ^ 2 ∂volume := by
  obtain ⟨lam, Lam, hlam, hlamLam, hEll, hRc, hdom, hcond⟩ := hcert
  obtain ⟨k, chi, K, hkm, hf0, hchi, hchiC, hchiBox, hchi_le, hchi_one, hK,
    hcrossInt, hpricecell, henergycell⟩ := hdata
  exact wholeSpaceSolution_translatedCell_coarse_energy_le_of_paper_condition
    (K := K) (cst := cst) (Theta := Theta) (R := R) hkm hEll haNonneg ht heta
    hP hGam0 hR hSc hbeta1 u hf0 hchi hchiC hchiBox hchi_le hchi_one hK
    hcrossInt hpricecell henergycell hlam hlamLam hc hTheta hPS hRc hGam hdom
    hcond


/-! ## 4. The family bound for the repaired stopping family -/

section Repaired

variable {Omega : Type*} {base : ℤ}

/-- **The stopping rule's certificate, transferred to every refined cell.**

`refinedStoppingCell_property_of_not_mem_failure` with
`Good = FluxRowSlotsCubeCoarseEllipticity`: the refined cell's scale is the
selected cube's scale and its centre is one of that cube's half-grid centres,
so §2's `FluxRowSlotsCubeCoarseEllipticity.cell` applies verbatim. -/
theorem fluxRowSlots_cellCoarseEllipticity_refinedStoppingCell
    {a : Vec d → ℝ} {t eta R cst Theta : ℝ}
    (failure : TriadicCube d → Set Omega) {omega : Omega}
    (hfinite : ∀ P : StoppingBaseCube d base,
      triadicFailureHeight failure omega P ≠ (⊤ : WithTop ℕ))
    (hgood : ∀ Q, omega ∉ failure Q →
      FluxRowSlotsCubeCoarseEllipticity a t eta R cst Theta Q)
    (q : RefinedStoppingCell failure omega base) :
    FluxRowSlotsCellCoarseEllipticity a t eta R cst Theta
      (refinedStoppingScale q) (refinedStoppingCenter q) :=
  (refinedStoppingCell_property_of_not_mem_failure failure hfinite
    (FluxRowSlotsCubeCoarseEllipticity a t eta R cst Theta) hgood q).cell q.2.2

/-- **The residual of `FluxRowSlotsCoarseBudget.lean` §5, discharged for the
repaired stopping family.**

`FluxRowSlotsFamilyCoarseEnergyBound u eta refinedStoppingScale
refinedStoppingCenter` — the single family-level input of the flux energy slot
— holds as soon as the stopping rule's failure event is the failure of the
manuscript's coarse-ellipticity threshold (`hgood`) and the carrier has the
analytic data on each selected cell (`hdata`).  The contraction factor `eta` is
the manuscript's: it is chosen first, and the `t`-smallness is the stopping
rule's own threshold `t Λ^{12} λ^{-11} ≤ (81 c³)⁻¹ η⁴`, tested cell by cell. -/
theorem wholeSpaceSolution_fluxRowSlots_familyCoarseEnergyBound_refinedStoppingCell
    {a f : Vec d → ℝ} {t eta P R Sc Gam0 cst Theta : ℝ}
    (failure : TriadicCube d → Set Omega) {omega : Omega}
    (haNonneg : ∀ x, 0 ≤ a x) (ht : 0 < t) (heta : 0 < eta)
    (hP : 0 < P) (hGam0 : 0 < Gam0) (hR : 0 ≤ R) (hSc : 0 ≤ Sc)
    (hbeta1 : eta ≤ 3 * (P * (Gam0 * 27 ^ d + Sc)))
    (hc : 0 < cst) (hTheta : 1 ≤ Theta)
    (hPS : (P * (Gam0 * 27 ^ d + Sc)) ^ 2 ≤ cst * Theta ^ 3)
    (hGam : Gam0 * 27 ^ d + Sc ≤ cst * Theta)
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hdata : ∀ q : RefinedStoppingCell failure omega base,
      FluxRowSlotsCellCoarseData u P
        (R * ((3 : ℝ) ^ refinedStoppingScale q)⁻¹) Sc Gam0
        (refinedStoppingScale q) (refinedStoppingCenter q))
    (hfinite : ∀ P : StoppingBaseCube d base,
      triadicFailureHeight failure omega P ≠ (⊤ : WithTop ℕ))
    (hgood : ∀ Q, omega ∉ failure Q →
      FluxRowSlotsCubeCoarseEllipticity a t eta R cst Theta Q) :
    FluxRowSlotsFamilyCoarseEnergyBound
      (Cell := RefinedStoppingCell failure omega base) u eta
      refinedStoppingScale refinedStoppingCenter := by
  intro q
  exact wholeSpaceSolution_translatedCell_coarse_energy_le_of_cellCertificate
    haNonneg ht heta hP hGam0 hR hSc hbeta1 hc hTheta hPS hGam u (hdata q)
    (fluxRowSlots_cellCoarseEllipticity_refinedStoppingCell failure hfinite
      hgood q)

end Repaired


/-! ## 5. The coarse budget on the repaired family -/

/-- **The coarse replacement of the retired `RepairedStoppingTSmallnessBudget`.**

The crude budget of `StoppingPartitionRepairedBudget.lean` asked, on every
selected cell, for `K² · 4096 d Λ · 3^{-2 m_q} ≤ t⁻¹ R^{2σ}` with a *uniform*
`Λ`, and the proposed source estimate is refuted by
(`not_exists_uniform_stoppingCellLinearUpperBound_empty`).  Along the coarse
route the same budget is `K² 3^d (C_m η) ≤ R^{2σ}`: `t`-free, cell-free, and
therefore not a property of the stopping rule at all — it is met by choosing
the contraction factor, below any prescribed ceiling `eta0`.  `Cm` is the
constant paid by the enlargement graph decay
(`fluxRowSlotsEnlargementConstant d`). -/
theorem exists_eta_fluxRowSlots_coarse_budget_of_const
    {K R sigma Cm eta0 : ℝ} (hK : K ≠ 0) (hR : 0 < R) (hCm : 0 < Cm)
    (heta0 : 0 < eta0) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ eta0 ∧
      K ^ 2 * ((3 : ℝ) ^ d * (Cm * eta)) ≤ Real.rpow R (2 * sigma) := by
  obtain ⟨e, hepos, hele, hbudget⟩ :=
    exists_uniform_fluxRowSlotsCoarseSmallnessBudget (d := d) (Cell := Unit)
      (sigma := sigma) hK hR (mul_pos hCm heta0)
  refine ⟨e / Cm, div_pos hepos hCm, ?_, ?_⟩
  · rw [div_le_iff₀ hCm]
    simpa [mul_comm] using hele
  · have hmul : Cm * (e / Cm) = e := by field_simp
    simpa [hmul] using hbudget ()

section Repaired

variable {Omega : Type*} {base : ℤ}

/-- **The stopping side condition and the coarse budget, together.**

The only remaining role of the stopping rule in the flux energy slot's budget:
it never selects a cell finer than the base scale, so a radius `R ≤ 3^base`
sits below every selected side length.  This is
`le_three_pow_refinedStoppingScale_of_le_three_pow_base`, restated here so that
the coarse budget and its stopping side condition are read off one lemma. -/
theorem repairedStoppingCell_coarse_budget_and_scale
    {failure : TriadicCube d → Set Omega} {omega : Omega}
    {K R sigma eta : ℝ} (hR : R ≤ (3 : ℝ) ^ base)
    (hbudget : K ^ 2 * ((3 : ℝ) ^ d * eta) ≤ Real.rpow R (2 * sigma)) :
    FluxRowSlotsCoarseSmallnessBudget d
        (fun _ : RefinedStoppingCell failure omega base ↦ eta) K R sigma ∧
      ∀ q : RefinedStoppingCell failure omega base,
        R ≤ (3 : ℝ) ^ refinedStoppingScale q :=
  ⟨fun _ ↦ hbudget,
    fun q ↦ le_three_pow_refinedStoppingScale_of_le_three_pow_base hR q⟩

end Repaired


/-! ## 6. The flux energy slot on the repaired family, end to end -/

/-- **The flux energy slot on a cell, with a constant in the graph decay.**

`wholeSpaceSolution_fluxRowSlots_energy_slot_coarse` in the shape the repaired
family's mass slot actually delivers: the graph decay carries the dimension-only
constant `Cm` (`fluxRowSlotsEnlargementConstant d` for
`wholeSpaceSolution_enlargement_mass_le_repairedStoppingDecay`), and `Cm` is paid
in the budget — `eta ↦ Cm · eta` — not in the source energy `fEnergy`, which
stays the frozen `‖f‖₂²`. -/
theorem wholeSpaceSolution_fluxRowSlots_energy_slot_coarse_const
    [NeZero d] {a f : Vec d → ℝ}
    {alpha t eta Cm R sigma fEnergy theta lambdaInv : ℝ} {graphDistance : ℕ}
    {m n : ℤ} (hn : n ≤ m) {z : Vec d}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (halpha : 0 < alpha) (ht : 0 < t) (hR : 0 < R) (hRS : R ≤ (3 : ℝ) ^ m)
    (heta : 0 ≤ eta) (hCm : 0 ≤ Cm) (hfEnergy : 0 ≤ fEnergy)
    (htheta : 0 ≤ theta) (haNonneg : ∀ x, 0 ≤ a x)
    (hcacc : (∫ x in translatedCube d m z, a x * vecNormSq (u.grad x) ∂volume) ≤
      eta * t⁻¹ * ∫ x in translatedCube d (m + 1) z, u.toFun x ^ 2 ∂volume)
    (hmass : (∫ x in translatedCube d (m + 1) z, u.toFun x ^ 2 ∂volume) ≤
      Cm * (Real.rpow theta ((graphDistance : ℝ) / 2) * fEnergy))
    (acoeff : Ch02.CoeffOn (Ch02.cubeDomain (originCube d m)))
    (ha : ∀ y, acoeff.toCoeffField y = scalarCoeffField (fun x ↦ a (x + z)) y)
    (u0 : H1Function (openCubeSet (originCube d m)))
    (hu0 : u0.grad =ᵐ[volume.restrict (openCubeSet (originCube d m))]
      fun x ↦ u.grad (x + z))
    (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1)
    (hbudget : Section6Dirichlet.dirichletWeightedEnergyFactor (3 * sigma / 4)
          sigma ^ 2 * ((3 : ℝ) ^ d * (Cm * eta)) ≤ Real.rpow R (2 * sigma)) :
    (3 : ℝ) ^ d * cubeVolume (originCube d m) *
        (Real.sqrt alpha *
          (weightedLocalSymmetricEnergyLp (originCube d m) n hn acoeff u0
            (fluxRowLocalLowerOrder sigma hsigma)
            (fluxRowLocalOrder sigma hsigma) FiniteLpExponent.two).toReal) ^ 2 ≤
      fluxRowRieszCellPhysicalScale alpha t R sigma fEnergy theta ((3 : ℝ) ^ m)
          graphDistance d * (1 + (alpha * lambdaInv) ^ 2) := by
  have hcacc' : cubeVolume (originCube d m) *
      (localSymmetricEnergyENorm (originCube d m) acoeff u0).toReal ^ 2 ≤
      eta * t⁻¹ * ∫ x in translatedCube d (m + 1) z, u.toFun x ^ 2 ∂volume := by
    rw [cubeVolume_mul_recentred_localSymmetricEnergy_sq_eq z acoeff ha haNonneg
      u0 u.grad hu0]
    exact hcacc
  exact fluxRowSlots_energy_slot_coarse_of_inputs_const (lambdaInv := lambdaInv)
    (W := cubeVolume (originCube d m))
    (mass := ∫ x in translatedCube d (m + 1) z, u.toFun x ^ 2 ∂volume)
    halpha ht hR hRS (cubeVolume_nonneg _) ENNReal.toReal_nonneg heta hCm
    hfEnergy htheta rfl
    (fluxRowSlots_weightedEnergy_toReal_le hn acoeff u0 hsigma) hcacc' hmass
    hbudget

section RepairedSlot

variable {base : ℤ}
  {failure : TriadicCube d → Set (_root_.SubdiffusiveProcess.Model.PotentialSample d)}
  {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d}

/-- **The flux energy slot on a refined stopping cell, end to end.**

The left side is the repaired partition's own `cellVolume q` and the right side
is `fluxRowRieszCellPhysicalScale` at the repaired family's decay factor and
graph distance: this is literally the energy antecedent of
`exists_fluxRowRiesz_repairedStoppingCell_localFluxPrice`
(`FluxRowRieszRepairedCellPrice.lean`, the hypothesis at its `cellVolume q *
(√α S)²` line).

The inputs are the proved ones: the cell-volume identity
(`repairedFluxRowRieszPartition_cellVolume_eq`), the stopping side condition
from the base scale
(`le_three_pow_refinedStoppingScale_of_le_three_pow_base`), the enlargement
graph decay (`wholeSpaceSolution_enlargement_mass_le_repairedStoppingDecay`),
the Section 6 prebalance and the recentring change of variables (inside
`wholeSpaceSolution_fluxRowSlots_energy_slot_coarse_const`), and the family
coarse Caccioppoli `hfamily`, which §4 discharges from the stopping rule's own
threshold. -/
theorem wholeSpaceSolution_fluxRowSlots_energy_slot_coarse_repairedStoppingCell
    [NeZero d] {a f : Vec d → ℝ} {alpha t eta R sigma lambdaInv : ℝ}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hL2 : ∫ x, u.toFun x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (chi : RepairedStoppingCutoff failure omega base)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty)
    (hcell : ∀ q,
      0 < stoppingGraphDistance repairedStoppingGraph source hsource q →
        ∫ x in translatedCube d (refinedStoppingScale q)
            (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume ≤
          repairedStoppingContractionFactor d *
            ∫ x in translatedCube d (refinedStoppingScale q + 1)
              (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume)
    (halpha : 0 < alpha) (ht : 0 < t) (hR : 0 < R) (hRbase : R ≤ (3 : ℝ) ^ base)
    (heta : 0 ≤ eta) (haNonneg : ∀ x, 0 ≤ a x)
    (hfamily : FluxRowSlotsFamilyCoarseEnergyBound
      (Cell := RefinedStoppingCell failure omega base) u eta
      refinedStoppingScale refinedStoppingCenter)
    {n : RefinedStoppingCell failure omega base → ℤ}
    (hn : ∀ q, n q ≤ refinedStoppingScale q)
    (acoeff : ∀ q, Ch02.CoeffOn
      (Ch02.cubeDomain (originCube d (refinedStoppingScale q))))
    (ha : ∀ q, ∀ y, (acoeff q).toCoeffField y =
      scalarCoeffField (fun x ↦ a (x + refinedStoppingCenter q)) y)
    (u0 : ∀ q, H1Function
      (openCubeSet (originCube d (refinedStoppingScale q))))
    (hu0 : ∀ q, (u0 q).grad =ᵐ[volume.restrict
        (openCubeSet (originCube d (refinedStoppingScale q)))]
      fun x ↦ u.grad (x + refinedStoppingCenter q))
    (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1)
    (hbudget : Section6Dirichlet.dirichletWeightedEnergyFactor (3 * sigma / 4)
        sigma ^ 2 *
        ((3 : ℝ) ^ d * (fluxRowSlotsEnlargementConstant d * eta)) ≤
      Real.rpow R (2 * sigma))
    (q : RefinedStoppingCell failure omega base) :
    (repairedFluxRowRieszPartition hinitial hrepair chi).cellVolume q *
        (Real.sqrt alpha *
          (weightedLocalSymmetricEnergyLp
            (originCube d (refinedStoppingScale q)) (n q) (hn q)
            (acoeff q) (u0 q) (fluxRowLocalLowerOrder sigma hsigma)
            (fluxRowLocalOrder sigma hsigma) FiniteLpExponent.two).toReal) ^ 2 ≤
      fluxRowRieszCellPhysicalScale alpha t R sigma (∫ x, f x ^ 2 ∂volume)
          (repairedStoppingPointwiseContractionFactor d ^ 2)
          ((3 : ℝ) ^ refinedStoppingScale q)
          (stoppingGraphDistance repairedStoppingGraph source hsource q) d *
        (1 + (alpha * lambdaInv) ^ 2) := by
  rw [repairedFluxRowRieszPartition_cellVolume_eq]
  refine wholeSpaceSolution_fluxRowSlots_energy_slot_coarse_const (hn q) u halpha
    ht hR (le_three_pow_refinedStoppingScale_of_le_three_pow_base hRbase q) heta
    fluxRowSlotsEnlargementConstant_pos.le
    (integral_nonneg fun x ↦ sq_nonneg (f x)) (sq_nonneg _) haNonneg
    (hfamily q) ?_ (acoeff q) (ha q) (u0 q) (hu0 q) hsigma hbudget
  have hdecay := wholeSpaceSolution_enlargement_mass_le_repairedStoppingDecay
    u hL2 hinitial hrepair source hsource hcell q
  simpa [mul_assoc] using hdecay

end RepairedSlot


/-! ## 7. The flux energy slot from the stopping rule's threshold alone -/

section RepairedEndToEnd

variable {base : ℤ}
  {failure : TriadicCube d → Set (_root_.SubdiffusiveProcess.Model.PotentialSample d)}
  {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d}

/-- **The flux energy slot on every refined stopping cell, from the stopping
rule's own threshold.**

§4 chained into §6.  Compared with
`wholeSpaceSolution_fluxRowSlots_energy_slot_coarse_repairedStoppingCell` the
family Caccioppoli `hfamily` is replaced by its source: the failure event's
`hgood` (the selected cube's coarse ellipticity meets
`t Λ^{12} λ^{-11} ≤ (81 c³)⁻¹ η⁴`), the almost-sure finiteness `hfinite` of the
ancestor chain, and the carrier's per-cell analytic data `hdata`.

`Rprice` is the mesoscopic price constant; `R` is the
flux row's radius.  They are unrelated. -/
theorem wholeSpaceSolution_fluxRowSlots_energy_slot_coarse_repairedStoppingCell_of_certificate
    [NeZero d] {a f : Vec d → ℝ}
    {alpha t eta P Rprice Sc Gam0 cst Theta R sigma lambdaInv : ℝ}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hL2 : ∫ x, u.toFun x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (chi : RepairedStoppingCutoff failure omega base)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsource : source.Nonempty)
    (hcell : ∀ q,
      0 < stoppingGraphDistance repairedStoppingGraph source hsource q →
        ∫ x in translatedCube d (refinedStoppingScale q)
            (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume ≤
          repairedStoppingContractionFactor d *
            ∫ x in translatedCube d (refinedStoppingScale q + 1)
              (refinedStoppingCenter q), u.toFun x ^ 2 ∂volume)
    (haNonneg : ∀ x, 0 ≤ a x) (halpha : 0 < alpha) (ht : 0 < t)
    (heta : 0 < eta) (hP : 0 < P) (hGam0 : 0 < Gam0) (hRprice : 0 ≤ Rprice)
    (hSc : 0 ≤ Sc) (hbeta1 : eta ≤ 3 * (P * (Gam0 * 27 ^ d + Sc)))
    (hc : 0 < cst) (hTheta : 1 ≤ Theta)
    (hPS : (P * (Gam0 * 27 ^ d + Sc)) ^ 2 ≤ cst * Theta ^ 3)
    (hGam : Gam0 * 27 ^ d + Sc ≤ cst * Theta)
    (hdata : ∀ q : RefinedStoppingCell failure omega base,
      FluxRowSlotsCellCoarseData u P
        (Rprice * ((3 : ℝ) ^ refinedStoppingScale q)⁻¹) Sc Gam0
        (refinedStoppingScale q) (refinedStoppingCenter q))
    (hfinite : ∀ P : StoppingBaseCube d base,
      triadicFailureHeight failure omega P ≠ (⊤ : WithTop ℕ))
    (hgood : ∀ Q, omega ∉ failure Q →
      FluxRowSlotsCubeCoarseEllipticity a t eta Rprice cst Theta Q)
    (hR : 0 < R) (hRbase : R ≤ (3 : ℝ) ^ base)
    {n : RefinedStoppingCell failure omega base → ℤ}
    (hn : ∀ q, n q ≤ refinedStoppingScale q)
    (acoeff : ∀ q, Ch02.CoeffOn
      (Ch02.cubeDomain (originCube d (refinedStoppingScale q))))
    (ha : ∀ q, ∀ y, (acoeff q).toCoeffField y =
      scalarCoeffField (fun x ↦ a (x + refinedStoppingCenter q)) y)
    (u0 : ∀ q, H1Function
      (openCubeSet (originCube d (refinedStoppingScale q))))
    (hu0 : ∀ q, (u0 q).grad =ᵐ[volume.restrict
        (openCubeSet (originCube d (refinedStoppingScale q)))]
      fun x ↦ u.grad (x + refinedStoppingCenter q))
    (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1)
    (hbudget : Section6Dirichlet.dirichletWeightedEnergyFactor (3 * sigma / 4)
        sigma ^ 2 *
        ((3 : ℝ) ^ d * (fluxRowSlotsEnlargementConstant d * eta)) ≤
      Real.rpow R (2 * sigma))
    (q : RefinedStoppingCell failure omega base) :
    (repairedFluxRowRieszPartition hinitial hrepair chi).cellVolume q *
        (Real.sqrt alpha *
          (weightedLocalSymmetricEnergyLp
            (originCube d (refinedStoppingScale q)) (n q) (hn q)
            (acoeff q) (u0 q) (fluxRowLocalLowerOrder sigma hsigma)
            (fluxRowLocalOrder sigma hsigma) FiniteLpExponent.two).toReal) ^ 2 ≤
      fluxRowRieszCellPhysicalScale alpha t R sigma (∫ x, f x ^ 2 ∂volume)
          (repairedStoppingPointwiseContractionFactor d ^ 2)
          ((3 : ℝ) ^ refinedStoppingScale q)
          (stoppingGraphDistance repairedStoppingGraph source hsource q) d *
        (1 + (alpha * lambdaInv) ^ 2) :=
  wholeSpaceSolution_fluxRowSlots_energy_slot_coarse_repairedStoppingCell
    (lambdaInv := lambdaInv) u hL2 hinitial hrepair chi source hsource hcell
    halpha ht hR hRbase heta.le haNonneg
    (wholeSpaceSolution_fluxRowSlots_familyCoarseEnergyBound_refinedStoppingCell
      failure haNonneg ht heta hP hGam0 hRprice hSc hbeta1 hc hTheta hPS hGam u
      hdata hfinite hgood)
    hn acoeff ha u0 hu0 hsigma hbudget q

end RepairedEndToEnd

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
