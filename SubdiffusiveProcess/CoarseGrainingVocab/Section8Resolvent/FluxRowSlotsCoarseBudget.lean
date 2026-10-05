
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowSlotsCoarseCaccioppoli
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowSlotsCellVolume

@[expose] public section

/-!
# The flux row's smallness budget in COARSE form

The crude-`Λ` budget of `FluxRowSlotsBudget.lean` asked, on every stopping cell,
for

```
K² · 4096 d Λ_Q 3^{-2 scale Q} ≤ t⁻¹ R^{2σ} ,
```

and `FluxRowSlotsGrowthRatio.lean` **refuted** the only geometric route to it
for the repaired stopping family (`fluxRowSlotsGrowthRatioBound` fails already
in the failure-free environment).  The crude route is therefore retired for the
flux energy slot.

Along the coarse route of `FluxRowSlotsCoarseCaccioppoli.lean` the Caccioppoli
constant is `Cc = eta · t⁻¹` — the contraction factor of the coarse-grained
local `L²` estimate, carrying **no `Λ` at all** — so the same budget reads

```
K² · 3^d · (eta t⁻¹) ≤ t⁻¹ R^{2σ}   ⟺   K² · 3^d · eta ≤ R^{2σ} ,
```

which is `t`-free, cell-free and coefficient-free: it is a condition on the
contraction factor alone, and it is *satisfiable by choosing `eta`*
(§3), which is exactly how the manuscript reads it (`η` is chosen first, then
`t` is taken small enough for the cell's own coarse ellipticity, `s.fixed.coefficient` and `mfd:sec-speed`).

## Contents

* §1 `FluxRowSlotsCoarseSmallnessBudget` — the budget.
* §2 `fluxRowSlots_coarse_budget_of_smallness`,
  `FluxRowSlotsCoarseSmallnessBudget.energyBudget` — the exact `hbudget`
  antecedent of `fluxRowSlots_energy_slot_enlarged_of_inputs`, discharged.
* §3 `exists_uniform_fluxRowSlotsCoarseSmallnessBudget` — the budget is
  satisfiable at any prescribed ceiling on `eta` (contrast with
  `not_exists_fluxRowSlotsGrowthRatioBound_refinedStoppingCell_empty`).
* §4 `fluxRowSlots_energy_slot_coarse_of_inputs[_const]` — the energy slot with
  the coarse Caccioppoli constant (the second form also pays the constant of the
  enlargement graph decay, in the budget).
* §5 `wholeSpaceSolution_translatedCell_coarse_energy_le_of_paper_condition` —
  the per-cell coarse Caccioppoli with the manuscript's condition
  `t Λ_{1/16}^{12} λ_{1/16}^{-11} ≤ C⁻¹ η⁴` as a literal hypothesis, and
  `FluxRowSlotsFamilyCoarseEnergyBound`, the property of the stopping family
  that is carried as a hypothesis.
* §6 `wholeSpaceSolution_fluxRowSlots_energy_slot_coarse[_family]` — the flux
  energy slot for the frozen carrier on a cell, end to end.

## Source

* `s.fixed.coefficient` and `mfd:sec-speed`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Section8
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The budget -/

/-- **The flux row's `t`-smallness budget, coarse form.**

`K` is the Section 6 prebalance factor, `eta q` the contraction factor of the
coarse-grained local `L²` estimate on the cell `q`, and `3^d` the enlargement
factor of `FluxRowSlotsCellVolume.lean`.  Compared with the crude
`FluxRowSlotsSmallnessBudget` this condition contains neither `t` nor the
cell's coefficient ceiling nor its scale. -/
def FluxRowSlotsCoarseSmallnessBudget (d : ℕ) {Cell : Type*} (eta : Cell → ℝ)
    (K R sigma : ℝ) : Prop :=
  ∀ q : Cell, K ^ 2 * ((3 : ℝ) ^ d * eta q) ≤ Real.rpow R (2 * sigma)

/-! ## 2. The budget closes the energy slot -/

/-- **The coarse Caccioppoli constant `eta t⁻¹` inside the slot's budget.**

The `t⁻¹` in the constant is the `t⁻¹` of the resolvent factor: it cancels, and
what is left is the `t`-free inequality `K² 3^d eta ≤ R^{2σ}`. -/
theorem fluxRowSlots_coarse_budget_of_smallness
    {alpha t eta R sigma cellSize K lambdaInv : ℝ}
    (halpha : 0 < alpha) (ht : 0 < t) (hR : 0 < R) (hRS : R ≤ cellSize)
    (hsmall : K ^ 2 * ((3 : ℝ) ^ d * eta) ≤ Real.rpow R (2 * sigma)) :
    alpha * K ^ 2 * ((3 : ℝ) ^ d * (eta * t⁻¹)) ≤
      alpha * t⁻¹ * Real.rpow R (2 * sigma) * (cellSize / R) ^ (d + 6) *
        (1 + (alpha * lambdaInv) ^ 2) := by
  refine fluxRowSlots_three_pow_budget_of_smallness (d := d)
    (lambdaInv := lambdaInv) halpha ht hR hRS ?_
  have hinv : (0 : ℝ) ≤ t⁻¹ := (inv_pos.mpr ht).le
  have hmul := mul_le_mul_of_nonneg_right hsmall hinv
  calc K ^ 2 * ((3 : ℝ) ^ d * (eta * t⁻¹))
      = K ^ 2 * ((3 : ℝ) ^ d * eta) * t⁻¹ := by ring
    _ ≤ Real.rpow R (2 * sigma) * t⁻¹ := hmul
    _ = t⁻¹ * Real.rpow R (2 * sigma) := by ring

/-- **The coarse budget is exactly what the energy slot needs.**  With the
stopping side condition `R ≤ 3^{scale q}`, the antecedent `hbudget` of
`fluxRowSlots_energy_slot_enlarged_of_inputs` holds at the coarse Caccioppoli
constant `Cc = eta q · t⁻¹`. -/
theorem FluxRowSlotsCoarseSmallnessBudget.energyBudget
    {Cell : Type*} {scale : Cell → ℤ} {eta : Cell → ℝ}
    {K t R sigma alpha lambdaInv : ℝ}
    (hbudget : FluxRowSlotsCoarseSmallnessBudget d eta K R sigma)
    (halpha : 0 < alpha) (ht : 0 < t) (hR : 0 < R) (q : Cell)
    (hRS : R ≤ (3 : ℝ) ^ scale q) :
    alpha * K ^ 2 * ((3 : ℝ) ^ d * (eta q * t⁻¹)) ≤
      alpha * t⁻¹ * Real.rpow R (2 * sigma) *
        ((3 : ℝ) ^ scale q / R) ^ (d + 6) * (1 + (alpha * lambdaInv) ^ 2) :=
  fluxRowSlots_coarse_budget_of_smallness (d := d) (lambdaInv := lambdaInv)
    halpha ht hR hRS (hbudget q)

/-! ## 3. The coarse budget is satisfiable -/

/-- **The coarse budget can always be met, at any prescribed ceiling on the
contraction factor.**

Take `eta = min eta0 (R^{2σ} / (K² 3^d))`.  This is the structural difference
from the crude route: `not_exists_fluxRowSlotsGrowthRatioBound_refinedStoppingCell_empty`
shows the crude condition has *no* solution for the repaired family, while the
coarse condition constrains only the contraction factor, which the caller
chooses (the price paid for a small `eta` is the smallness of `t` in
the local `L²` resolvent estimate, i.e. §5's `hcond`). -/
theorem exists_uniform_fluxRowSlotsCoarseSmallnessBudget {Cell : Type*}
    {K R sigma eta0 : ℝ} (hK : K ≠ 0) (hR : 0 < R) (heta0 : 0 < eta0) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ eta0 ∧
      FluxRowSlotsCoarseSmallnessBudget d (fun _ : Cell ↦ eta) K R sigma := by
  have hRp : (0 : ℝ) < Real.rpow R (2 * sigma) := Real.rpow_pos_of_pos hR _
  have hKsq : (0 : ℝ) < K ^ 2 := by positivity
  have hden : (0 : ℝ) < K ^ 2 * (3 : ℝ) ^ d := by positivity
  refine ⟨min eta0 (Real.rpow R (2 * sigma) / (K ^ 2 * (3 : ℝ) ^ d)),
    lt_min heta0 (div_pos hRp hden), min_le_left _ _, ?_⟩
  intro _
  have hle : min eta0 (Real.rpow R (2 * sigma) / (K ^ 2 * (3 : ℝ) ^ d)) ≤
      Real.rpow R (2 * sigma) / (K ^ 2 * (3 : ℝ) ^ d) := min_le_right _ _
  have := mul_le_mul_of_nonneg_left hle hden.le
  calc K ^ 2 * ((3 : ℝ) ^ d *
        min eta0 (Real.rpow R (2 * sigma) / (K ^ 2 * (3 : ℝ) ^ d)))
      = K ^ 2 * (3 : ℝ) ^ d *
          min eta0 (Real.rpow R (2 * sigma) / (K ^ 2 * (3 : ℝ) ^ d)) := by ring
    _ ≤ K ^ 2 * (3 : ℝ) ^ d *
          (Real.rpow R (2 * sigma) / (K ^ 2 * (3 : ℝ) ^ d)) := this
    _ = Real.rpow R (2 * sigma) := by field_simp

/-! ## 4. The energy slot with the coarse Caccioppoli constant -/

/-- **The energy slot of the local flux price estimate, coarse form.**

`fluxRowSlots_energy_slot_enlarged_of_inputs` with the Caccioppoli constant
supplied by the coarse-grained local `L²` estimate (`Cc = eta t⁻¹`) and the
budget in the `t`-free coarse form.  No coefficient ceiling occurs anywhere. -/
theorem fluxRowSlots_energy_slot_coarse_of_inputs
    {alpha t eta R sigma fEnergy theta cellSize S S0 K mass lambdaInv V W : ℝ}
    {graphDistance : ℕ}
    (halpha : 0 < alpha) (ht : 0 < t) (hR : 0 < R) (hRS : R ≤ cellSize)
    (hW : 0 ≤ W) (hS : 0 ≤ S) (heta : 0 ≤ eta) (hfEnergy : 0 ≤ fEnergy)
    (htheta : 0 ≤ theta)
    (hVW : V = (3 : ℝ) ^ d * W)
    (hSle : S ≤ K * S0)
    (hcacc : W * S0 ^ 2 ≤ eta * t⁻¹ * mass)
    (hmass : mass ≤ Real.rpow theta ((graphDistance : ℝ) / 2) * fEnergy)
    (hbudget : K ^ 2 * ((3 : ℝ) ^ d * eta) ≤ Real.rpow R (2 * sigma)) :
    V * (Real.sqrt alpha * S) ^ 2 ≤
      fluxRowRieszCellPhysicalScale alpha t R sigma fEnergy theta cellSize
          graphDistance d * (1 + (alpha * lambdaInv) ^ 2) := by
  have hCc : (0 : ℝ) ≤ eta * t⁻¹ := mul_nonneg heta (inv_pos.mpr ht).le
  exact fluxRowSlots_energy_slot_enlarged_of_inputs (Cc := eta * t⁻¹)
    halpha hW hS hCc hfEnergy htheta hVW hSle hcacc hmass
    (fluxRowSlots_coarse_budget_of_smallness (d := d) (lambdaInv := lambdaInv)
      halpha ht hR hRS hbudget)

/-- **The energy slot when the graph decay carries a constant.**

`wholeSpaceSolution_enlargement_mass_le_repairedStoppingDecay` delivers the mass
slot with the dimension-only constant `fluxRowSlotsEnlargementConstant d` in
front of `θ^{dist/2}`.  That constant is paid in the budget — not in the source
energy `fEnergy`, which stays the frozen `‖f‖₂²` — by replacing the contraction
factor `eta` with `Cm · eta`; the budget is still `t`-free and still met by
choosing `eta` (§3). -/
theorem fluxRowSlots_energy_slot_coarse_of_inputs_const
    {alpha t eta Cm R sigma fEnergy theta cellSize S S0 K mass lambdaInv V W : ℝ}
    {graphDistance : ℕ}
    (halpha : 0 < alpha) (ht : 0 < t) (hR : 0 < R) (hRS : R ≤ cellSize)
    (hW : 0 ≤ W) (hS : 0 ≤ S) (heta : 0 ≤ eta) (hCm : 0 ≤ Cm)
    (hfEnergy : 0 ≤ fEnergy) (htheta : 0 ≤ theta)
    (hVW : V = (3 : ℝ) ^ d * W)
    (hSle : S ≤ K * S0)
    (hcacc : W * S0 ^ 2 ≤ eta * t⁻¹ * mass)
    (hmass : mass ≤ Cm * (Real.rpow theta ((graphDistance : ℝ) / 2) * fEnergy))
    (hbudget : K ^ 2 * ((3 : ℝ) ^ d * (Cm * eta)) ≤ Real.rpow R (2 * sigma)) :
    V * (Real.sqrt alpha * S) ^ 2 ≤
      fluxRowRieszCellPhysicalScale alpha t R sigma fEnergy theta cellSize
          graphDistance d * (1 + (alpha * lambdaInv) ^ 2) := by
  have hnn : (0 : ℝ) ≤ eta * t⁻¹ := mul_nonneg heta (inv_pos.mpr ht).le
  have hcacc' : W * S0 ^ 2 ≤ Cm * eta * t⁻¹ *
      (Real.rpow theta ((graphDistance : ℝ) / 2) * fEnergy) := by
    refine hcacc.trans ?_
    calc eta * t⁻¹ * mass
        ≤ eta * t⁻¹ *
            (Cm * (Real.rpow theta ((graphDistance : ℝ) / 2) * fEnergy)) :=
          mul_le_mul_of_nonneg_left hmass hnn
      _ = Cm * eta * t⁻¹ *
            (Real.rpow theta ((graphDistance : ℝ) / 2) * fEnergy) := by ring
  exact fluxRowSlots_energy_slot_coarse_of_inputs (lambdaInv := lambdaInv)
    (eta := Cm * eta)
    (mass := Real.rpow theta ((graphDistance : ℝ) / 2) * fEnergy)
    halpha ht hR hRS hW hS (mul_nonneg hCm heta) hfEnergy htheta hVW hSle
    hcacc' le_rfl hbudget

/-! ## 5. The per-cell coarse condition, and what the stopping rule must supply -/

/-- **The carrier's coarse Caccioppoli on a cell, with the manuscript's
condition as a literal hypothesis.**

`wholeSpaceSolution_translatedCell_coarse_energy_le_of_cells` with `hsmall`
produced by `coarse_contraction_smallness_of_paper_condition`, so that the only
numerical hypothesis is the manuscript's

```
t ℓ⁻² Λ_{1/16}^{12}(Q;a) λ_{1/16}^{-11}(Q;a) ≤ C⁻¹ η^{15/2}
```

(`s.fixed.coefficient` and `mfd:sec-speed`) on
the cell's **own** coarse ellipticity, at `ℓ = 3^m` the cell's side length and
at the repo's arbitrary normalization `C = 81 c³`, `η^{15/2} ↦ η⁴` of
`coarse_contraction_smallness_of_paper_condition`.

**The cell scale (P-253).**  The manuscript's condition carries the factor
`ℓ⁻²`; P-247 proved that a scale-free condition makes the stopping rule's
failure event monotone along the ancestor chain and its geometric decay
unsatisfiable.  The scale sits in exactly two places, and they must move
together:

* the mesoscopic cross price constant is *dimensionful*.
  `MesoscopicCrossPriceEnergyOn` bounds `|2∫ a χ u ∇u·∇χ|` by
  `β⁻¹ R √E √M`, and `|∇χ| ≲ 3^{-m}` on a scale-`m` cell, so the cell's own
  price constant is `R · 3^{-m}` with `R` the scale-free constant.  That is
  what `hpricecell` now asks for;
* the smallness `hcond` is weakened by `ℓ⁻² = 3^{-2m}`.

The two changes cancel exactly in
`coarse_contraction_smallness_of_paper_condition`, applied at `t · 3^{-2m}`, so
the conclusion is unchanged. -/
theorem wholeSpaceSolution_translatedCell_coarse_energy_le_of_paper_condition
    {a f : Vec d → ℝ} {lam Lam t eta P R Sc Gam0 K cst Theta : ℝ} {k m : ℤ}
    {z : Vec d}
    (hkm : k ≤ m - 3)
    (hEll : IsEllipticFieldOn lam Lam (translatedCube d (m + 1) z)
      (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x) (ht : 0 < t) (heta : 0 < eta)
    (hP : 0 < P) (hGam0 : 0 < Gam0) (hR : 0 ≤ R) (hSc : 0 ≤ Sc)
    (hbeta1 : eta ≤ 3 * (P * (Gam0 * 27 ^ d + Sc)))
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hf0 : ∀ x ∈ translatedCube d (m + 1) z, f x = 0)
    {chi : Vec d → ℝ} (hchi : ContDiff ℝ (⊤ : ℕ∞) chi)
    (hchiC : HasCompactSupport chi)
    (hchiBox : tsupport chi ⊆
      {x : Vec d | ∀ i, |x i - z i| ≤ 3 / 4 * (3 : ℝ) ^ m})
    (hchi_le : ∀ x, |chi x| ≤ 1)
    (hchi_one : ∀ x ∈ translatedCube d m z, chi x = 1)
    (hK : ∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤ K)
    (hcrossInt : IntegrableOn (fun x => a x * chi x * u.toFun x *
      vecDot (u.grad x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)))
      (translatedCube d (m + 1) z) volume)
    (hpricecell : ∀ j ∈ priceIndexBox d k z (3 / 4 * (3 : ℝ) ^ m),
      MesoscopicCrossPriceEnergyOn a (openCubeSet (priceCell d k j))
        (openCubeSet (priceCell d k j)) u.toFun u.grad chi t P
        (R * ((3 : ℝ) ^ m)⁻¹) Sc)
    (henergycell : ∀ j ∈ mesoIndexBox d k (m + 1) z,
      CoarseEnergyBoundOn a (mesoCell d k j) (mesoCore d k j) u.toFun u.grad
        t Gam0)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hc : 0 < cst) (hTheta : 1 ≤ Theta)
    (hPS : (P * (Gam0 * 27 ^ d + Sc)) ^ 2 ≤ cst * Theta ^ 3)
    (hRc : R ^ 2 ≤ cst * Lam) (hGam : Gam0 * 27 ^ d + Sc ≤ cst * Theta)
    (hdom : Theta ^ 4 * Lam ≤ Lam ^ 12 * lam⁻¹ ^ 11)
    (hcond : t * (((3 : ℝ) ^ m)⁻¹ ^ 2 * (Lam ^ 12 * lam⁻¹ ^ 11)) ≤
      (81 * cst ^ 3)⁻¹ * eta ^ 4) :
    (∫ x in translatedCube d m z, a x * vecNormSq (u.grad x) ∂volume) ≤
      eta * t⁻¹ * ∫ x in translatedCube d (m + 1) z, u.toFun x ^ 2 ∂volume := by
  have hGamNonneg : (0 : ℝ) ≤ Gam0 * 27 ^ d + Sc := by positivity
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) _
  have h3inv : (0 : ℝ) < ((3 : ℝ) ^ m)⁻¹ := inv_pos.mpr h3
  have hts : (0 : ℝ) < t * ((3 : ℝ) ^ m)⁻¹ ^ 2 := by positivity
  have hcond' : t * ((3 : ℝ) ^ m)⁻¹ ^ 2 * (Lam ^ 12 * lam⁻¹ ^ 11) ≤
      (81 * cst ^ 3)⁻¹ * eta ^ 4 := by
    rw [mul_assoc]; exact hcond
  have hsmall0 := coarse_contraction_smallness_of_paper_condition (d := d)
    hts hlam hlamLam hc hTheta hGamNonneg hPS hRc hGam hdom hcond'
  have hsmall : 81 * (P * (Gam0 * 27 ^ d + Sc)) ^ 2 *
      (R * ((3 : ℝ) ^ m)⁻¹) ^ 2 * (Gam0 * 27 ^ d + Sc) * t ≤ eta ^ 4 := by
    calc 81 * (P * (Gam0 * 27 ^ d + Sc)) ^ 2 * (R * ((3 : ℝ) ^ m)⁻¹) ^ 2 *
          (Gam0 * 27 ^ d + Sc) * t
        = 81 * (P * (Gam0 * 27 ^ d + Sc)) ^ 2 * R ^ 2 *
            (Gam0 * 27 ^ d + Sc) * (t * ((3 : ℝ) ^ m)⁻¹ ^ 2) := by ring
      _ ≤ eta ^ 4 := hsmall0
  exact wholeSpaceSolution_translatedCell_coarse_energy_le_of_cells hkm hEll
    haNonneg ht heta hP hGam0 (mul_nonneg hR h3inv.le) hSc hbeta1 u hf0 hchi
    hchiC hchiBox hchi_le hchi_one hK hcrossInt hpricecell henergycell hsmall

/-- **What the stopping rule must still supply, in coarse form.**

For every cell of the family, the carrier's coarse Caccioppoli on the
cell/enlargement pair at a single contraction factor `eta`.  Each instance is
produced by
`wholeSpaceSolution_translatedCell_coarse_energy_le_of_paper_condition` from the
cell's own coarse ellipticity; this predicate is the *only* remaining input of
the flux energy slot that is not a theorem about a fixed cell. -/
def FluxRowSlotsFamilyCoarseEnergyBound {a f : Vec d → ℝ} {t : ℝ} {Cell : Type*}
    (u : WholeSpaceDivergenceResolventSolution a t f) (eta : ℝ)
    (scale : Cell → ℤ) (centre : Cell → Vec d) : Prop :=
  ∀ q : Cell,
    (∫ x in translatedCube d (scale q) (centre q),
        a x * vecNormSq (u.grad x) ∂volume) ≤
      eta * t⁻¹ * ∫ x in translatedCube d (scale q + 1) (centre q),
        u.toFun x ^ 2 ∂volume

/-! ## 6. The flux energy slot for the frozen carrier, end to end -/

/-- **The flux row's energy slot on a cell, with the cell's own coarse
constants.**

The four inputs of `fluxRowSlots_energy_slot_coarse_of_inputs` instantiated at
the frozen carrier:

* the Section 6 prebalance `fluxRowSlots_weightedEnergy_toReal_le`;
* the coarse Caccioppoli `hcacc` (§5, or
  `wholeSpaceSolution_recentredCell_localSymmetricEnergy_sq_le_coarse_of_cells`),
  transported to the origin cube by
  `cubeVolume_mul_recentred_localSymmetricEnergy_sq_eq`;
* the graph decay `hmass` on the enlargement
  (`wholeSpaceSolution_enlargement_mass_le_repairedStoppingDecay`);
* the coarse budget `hbudget`.

The left side is the partition's `cellVolume` (the enlargement's volume,
`3^d · cubeVolume`) times the prebalanced weighted energy. -/
theorem wholeSpaceSolution_fluxRowSlots_energy_slot_coarse
    [NeZero d] {a f : Vec d → ℝ}
    {alpha t eta R sigma fEnergy theta lambdaInv : ℝ} {graphDistance : ℕ}
    {m n : ℤ} (hn : n ≤ m) {z : Vec d}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (halpha : 0 < alpha) (ht : 0 < t) (hR : 0 < R) (hRS : R ≤ (3 : ℝ) ^ m)
    (heta : 0 ≤ eta) (hfEnergy : 0 ≤ fEnergy) (htheta : 0 ≤ theta)
    (haNonneg : ∀ x, 0 ≤ a x)
    (hcacc : (∫ x in translatedCube d m z, a x * vecNormSq (u.grad x) ∂volume) ≤
      eta * t⁻¹ * ∫ x in translatedCube d (m + 1) z, u.toFun x ^ 2 ∂volume)
    (hmass : (∫ x in translatedCube d (m + 1) z, u.toFun x ^ 2 ∂volume) ≤
      Real.rpow theta ((graphDistance : ℝ) / 2) * fEnergy)
    (acoeff : Ch02.CoeffOn (Ch02.cubeDomain (originCube d m)))
    (ha : ∀ y, acoeff.toCoeffField y = scalarCoeffField (fun x ↦ a (x + z)) y)
    (u0 : H1Function (openCubeSet (originCube d m)))
    (hu0 : u0.grad =ᵐ[volume.restrict (openCubeSet (originCube d m))]
      fun x ↦ u.grad (x + z))
    (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1)
    (hbudget : Section6Dirichlet.dirichletWeightedEnergyFactor (3 * sigma / 4)
          sigma ^ 2 * ((3 : ℝ) ^ d * eta) ≤ Real.rpow R (2 * sigma)) :
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
  exact fluxRowSlots_energy_slot_coarse_of_inputs (lambdaInv := lambdaInv)
    (W := cubeVolume (originCube d m))
    (mass := ∫ x in translatedCube d (m + 1) z, u.toFun x ^ 2 ∂volume)
    halpha ht hR hRS (cubeVolume_nonneg _) ENNReal.toReal_nonneg heta hfEnergy
    htheta rfl (fluxRowSlots_weightedEnergy_toReal_le hn acoeff u0 hsigma)
    hcacc' hmass hbudget

/-- The slot for every cell of a family carrying
`FluxRowSlotsFamilyCoarseEnergyBound`, with the stopping side condition
`R ≤ 3^{scale q}` and the graph decay on the enlargement. -/
theorem wholeSpaceSolution_fluxRowSlots_energy_slot_coarse_family
    [NeZero d] {a f : Vec d → ℝ} {Cell : Type*}
    {alpha t eta R sigma fEnergy theta lambdaInv : ℝ}
    {graphDistance : Cell → ℕ} {scale : Cell → ℤ} {centre : Cell → Vec d}
    {n : Cell → ℤ}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (halpha : 0 < alpha) (ht : 0 < t) (hR : 0 < R)
    (hRS : ∀ q, R ≤ (3 : ℝ) ^ scale q) (hn : ∀ q, n q ≤ scale q)
    (heta : 0 ≤ eta) (hfEnergy : 0 ≤ fEnergy) (htheta : 0 ≤ theta)
    (haNonneg : ∀ x, 0 ≤ a x)
    (hfamily : FluxRowSlotsFamilyCoarseEnergyBound u eta scale centre)
    (hmass : ∀ q, (∫ x in translatedCube d (scale q + 1) (centre q),
        u.toFun x ^ 2 ∂volume) ≤
      Real.rpow theta ((graphDistance q : ℝ) / 2) * fEnergy)
    (acoeff : ∀ q, Ch02.CoeffOn (Ch02.cubeDomain (originCube d (scale q))))
    (ha : ∀ q, ∀ y, (acoeff q).toCoeffField y =
      scalarCoeffField (fun x ↦ a (x + centre q)) y)
    (u0 : ∀ q, H1Function (openCubeSet (originCube d (scale q))))
    (hu0 : ∀ q, (u0 q).grad =ᵐ[volume.restrict
        (openCubeSet (originCube d (scale q)))]
      fun x ↦ u.grad (x + centre q))
    (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1)
    (hbudget : Section6Dirichlet.dirichletWeightedEnergyFactor (3 * sigma / 4)
        sigma ^ 2 * ((3 : ℝ) ^ d * eta) ≤ Real.rpow R (2 * sigma))
    (q : Cell) :
    (3 : ℝ) ^ d * cubeVolume (originCube d (scale q)) *
        (Real.sqrt alpha *
          (weightedLocalSymmetricEnergyLp (originCube d (scale q)) (n q) (hn q)
            (acoeff q) (u0 q) (fluxRowLocalLowerOrder sigma hsigma)
            (fluxRowLocalOrder sigma hsigma) FiniteLpExponent.two).toReal) ^ 2 ≤
      fluxRowRieszCellPhysicalScale alpha t R sigma fEnergy theta
          ((3 : ℝ) ^ scale q) (graphDistance q) d *
        (1 + (alpha * lambdaInv) ^ 2) :=
  wholeSpaceSolution_fluxRowSlots_energy_slot_coarse (hn q) u halpha ht hR
    (hRS q) heta hfEnergy htheta haNonneg (hfamily q) (hmass q) (acoeff q)
    (ha q) (u0 q) (hu0 q) hsigma hbudget

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
