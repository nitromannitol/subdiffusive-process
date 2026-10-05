
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsCoarseCellRow
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowSlotsWholeSpaceCell

@[expose] public section

/-!
# The flux energy slot's Caccioppoli, with the cell's own COARSE constants

`FluxRowSlotsWholeSpaceCell.lean` delivers the energy slot's Caccioppoli input
through the *crude*-`Λ` contraction of `WholeSpaceRowsLocalL2.lean`, whose
constant is `4096 d Λ 3^{-2m}` with `Λ = ‖a‖_{L^∞(Q̂)}`.  Reducing the
`t`-budget along that route to the geometric condition
`fluxRowSlotsGrowthRatioBound`, and `FluxRowSlotsGrowthRatio.lean` **refutes**
that condition for the repaired stopping family.  So the crude route is retired
for this slot.

This file builds the replacement the manuscript actually uses: the **coarse**
Caccioppoli, i.e. the energy half of the coarse-grained local `L²` contraction

```
∫_{Q} u² + t ∫_{Q} a |∇u|² ≤ eta ∫_{Q̂} u²        (Q = z + □_n, Q̂ = z + □_{n+1})
```

of `massive_local_l2_coarse_contraction_of_energy_price_on`.  This retains the
mass half of that inequality (for the exterior row) and discarded the energy
half; this file keeps the **energy** half, which is exactly the flux row's
`(B-1)` input:

```
|Q| ‖u‖²_{E(Q)} = ∫_{Q} a |∇u|² ≤ eta · t⁻¹ · ∫_{Q̂} u² .
```

The gain is that the constant is now the contraction factor `eta` and carries
**no `Λ` at all**: the coefficient's crude `L^∞` ceiling appears only as the
qualitative hypothesis `IsEllipticFieldOn lam Lam Q̂`, never in the constant.
The `t`-smallness that used to sit in the constant now sits in the contraction's
own hypothesis `81 (P (Gam+Sc))² R² (Gam+Sc) t ≤ eta⁴`, which
`coarse_contraction_smallness_of_paper_condition`  converts into the
manuscript's per-cell coarse condition `t Λ_{1/16}^{12} λ_{1/16}^{-11} ≤
C⁻¹ eta⁴` — a condition on the cell's *own* coarse ellipticity, which the
stopping rule certifies by construction.

## Contents

* §1 `massive_local_l2_translatedCube_coarse_energy[']` — the energy half on the
  translated-cube pair, in the `t ·` and the `t⁻¹ ·` normalizations.
* §2 `massive_local_l2_translatedCube_coarse_energy_of_cells` — the same from
  the two per-cell mesoscopic legs.
* §3 `wholeSpaceSolution_translatedCell_coarse_energy_le_of_local` — the frozen
  whole-space carrier's version, and `…_of_cells` from the per-cell legs.
* §4 `wholeSpaceSolution_recentredCell_localSymmetricEnergy_sq_le_coarse` — the
  recentred, cube-volume normalized form: the exact `(B-1)` Caccioppoli input,
  with `Cc = eta * t⁻¹`; `…_of_cells` is the same from the per-cell legs.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Section8
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ## 1. The energy half of the coarse contraction, on a `translatedCube` pair -/

/-- **The coarse-grained Caccioppoli inequality on a `translatedCube` pair.**

`massive_local_l2_coarse_contraction_of_energy_price_on` with

* `S = translatedCube d n c` the cell,
* `W = translatedCube d (n+1) c` the enlargement,
* `V = Metric.ball c ((4/5) 3^n)` the intermediate set of the intermediate-ball geometry,

and the *mass* term of the conclusion dropped (the energy term is omitted
instead).  The constant is the contraction factor `eta`; no `Λ` appears. -/
theorem massive_local_l2_translatedCube_coarse_energy
    {a : Vec d → ℝ} {lam Lam t eta P R Sc Gam K : ℝ} {n : ℤ} {c : Vec d}
    (hEll : IsEllipticFieldOn lam Lam (translatedCube d (n + 1) c)
      (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x) (ht : 0 < t) (heta : 0 < eta)
    (hP : 0 < P) (hGam : 0 < Gam) (hR : 0 ≤ R) (hSc : 0 ≤ Sc)
    (hbeta1 : eta ≤ 3 * (P * (Gam + Sc)))
    (u : H1Function (translatedCube d (n + 1) c))
    (hu : IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹
      (translatedCube d (n + 1) c) u (fun _ ↦ (0 : ℝ)))
    {chi : Vec d → ℝ} (hchi : ContDiff ℝ (⊤ : ℕ∞) chi)
    (hchiC : HasCompactSupport chi)
    (hchiBox : tsupport chi ⊆
      {x : Vec d | ∀ i, |x i - c i| ≤ 3 / 4 * (3 : ℝ) ^ n})
    (hchi_le : ∀ x, |chi x| ≤ 1)
    (hchi_one : ∀ x ∈ translatedCube d n c, chi x = 1)
    (hK : ∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤ K)
    (hprice : MesoscopicCrossPriceEnergyOn a (translatedCube d (n + 1) c)
      (Metric.ball c (4 / 5 * (3 : ℝ) ^ n)) u.toFun u.grad chi t P R Sc)
    (henergy : CoarseEnergyBoundOn a (translatedCube d (n + 1) c)
      (Metric.ball c (4 / 5 * (3 : ℝ) ^ n)) u.toFun u.grad t Gam)
    (hsmall : 81 * (P * (Gam + Sc)) ^ 2 * R ^ 2 * (Gam + Sc) * t ≤ eta ^ 4) :
    t * (∫ x in translatedCube d n c, a x * vecNormSq (u.grad x) ∂volume) ≤
      eta * ∫ x in translatedCube d (n + 1) c, u.toFun x ^ 2 ∂volume := by
  have hchiS : tsupport chi ⊆ translatedCube d (n + 1) c :=
    hchiBox.trans ((box_subset_ball d n c).trans (ball_subset_translatedCube_succ d n c))
  have hbase := massive_local_l2_coarse_contraction_of_energy_price_on
    (isOpenBoundedConvexDomain_translatedCube (n + 1) c) hEll haNonneg ht heta
    hP hGam hR hSc hbeta1 (translatedCube_subset_succ d n c)
    (isOpenBoundedConvexDomain_translatedCube n c).isOpen.measurableSet u hu
    hchi hchiC hchiS hchi_le hchi_one hK hprice henergy hsmall
  have hmass : 0 ≤ ∫ x in translatedCube d n c, u.toFun x ^ 2 ∂volume :=
    setIntegral_nonneg
      (isOpenBoundedConvexDomain_translatedCube n c).isOpen.measurableSet
      fun x _ ↦ sq_nonneg _
  linarith only [hbase, hmass]

/-- The same in the normalization the flux energy slot consumes: the Caccioppoli
constant is `eta * t⁻¹`. -/
theorem massive_local_l2_translatedCube_coarse_energy'
    {a : Vec d → ℝ} {lam Lam t eta P R Sc Gam K : ℝ} {n : ℤ} {c : Vec d}
    (hEll : IsEllipticFieldOn lam Lam (translatedCube d (n + 1) c)
      (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x) (ht : 0 < t) (heta : 0 < eta)
    (hP : 0 < P) (hGam : 0 < Gam) (hR : 0 ≤ R) (hSc : 0 ≤ Sc)
    (hbeta1 : eta ≤ 3 * (P * (Gam + Sc)))
    (u : H1Function (translatedCube d (n + 1) c))
    (hu : IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹
      (translatedCube d (n + 1) c) u (fun _ ↦ (0 : ℝ)))
    {chi : Vec d → ℝ} (hchi : ContDiff ℝ (⊤ : ℕ∞) chi)
    (hchiC : HasCompactSupport chi)
    (hchiBox : tsupport chi ⊆
      {x : Vec d | ∀ i, |x i - c i| ≤ 3 / 4 * (3 : ℝ) ^ n})
    (hchi_le : ∀ x, |chi x| ≤ 1)
    (hchi_one : ∀ x ∈ translatedCube d n c, chi x = 1)
    (hK : ∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤ K)
    (hprice : MesoscopicCrossPriceEnergyOn a (translatedCube d (n + 1) c)
      (Metric.ball c (4 / 5 * (3 : ℝ) ^ n)) u.toFun u.grad chi t P R Sc)
    (henergy : CoarseEnergyBoundOn a (translatedCube d (n + 1) c)
      (Metric.ball c (4 / 5 * (3 : ℝ) ^ n)) u.toFun u.grad t Gam)
    (hsmall : 81 * (P * (Gam + Sc)) ^ 2 * R ^ 2 * (Gam + Sc) * t ≤ eta ^ 4) :
    (∫ x in translatedCube d n c, a x * vecNormSq (u.grad x) ∂volume) ≤
      eta * t⁻¹ * ∫ x in translatedCube d (n + 1) c, u.toFun x ^ 2 ∂volume := by
  have hbase := massive_local_l2_translatedCube_coarse_energy hEll haNonneg ht
    heta hP hGam hR hSc hbeta1 u hu hchi hchiC hchiBox hchi_le hchi_one hK
    hprice henergy hsmall
  have hmul := mul_le_mul_of_nonneg_left hbase (le_of_lt (inv_pos.mpr ht))
  calc (∫ x in translatedCube d n c, a x * vecNormSq (u.grad x) ∂volume)
      = t⁻¹ * (t * ∫ x in translatedCube d n c,
          a x * vecNormSq (u.grad x) ∂volume) := by
        field_simp
    _ ≤ t⁻¹ * (eta * ∫ x in translatedCube d (n + 1) c,
          u.toFun x ^ 2 ∂volume) := hmul
    _ = eta * t⁻¹ * ∫ x in translatedCube d (n + 1) c,
          u.toFun x ^ 2 ∂volume := by ring

/-! ## 2. The energy half from the two per-cell mesoscopic legs -/

/-- **The coarse Caccioppoli from the per-cell legs.**  The estimate with the
energy conclusion: the price on the triadic price cells and the coarse energy on
the mesoscopic cells, the mesoscopic scale three triadic scales below the
cell. -/
theorem massive_local_l2_translatedCube_coarse_energy_of_cells
    {a : Vec d → ℝ} {lam Lam t eta P R Sc Gam0 K : ℝ} {k n : ℤ} {c : Vec d}
    (hkn : k ≤ n - 3)
    (hEll : IsEllipticFieldOn lam Lam (translatedCube d (n + 1) c)
      (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x) (ht : 0 < t) (heta : 0 < eta)
    (hP : 0 < P) (hGam0 : 0 < Gam0) (hR : 0 ≤ R) (hSc : 0 ≤ Sc)
    (hbeta1 : eta ≤ 3 * (P * (Gam0 * 27 ^ d + Sc)))
    (u : H1Function (translatedCube d (n + 1) c))
    (hu : IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹
      (translatedCube d (n + 1) c) u (fun _ ↦ (0 : ℝ)))
    {chi : Vec d → ℝ} (hchi : ContDiff ℝ (⊤ : ℕ∞) chi)
    (hchiC : HasCompactSupport chi)
    (hchiBox : tsupport chi ⊆
      {x : Vec d | ∀ i, |x i - c i| ≤ 3 / 4 * (3 : ℝ) ^ n})
    (hchi_le : ∀ x, |chi x| ≤ 1)
    (hchi_one : ∀ x ∈ translatedCube d n c, chi x = 1)
    (hK : ∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤ K)
    (hcrossInt : IntegrableOn (fun x => a x * chi x * u.toFun x *
      vecDot (u.grad x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)))
      (translatedCube d (n + 1) c) volume)
    (henergyInt : IntegrableOn (fun x => a x * vecNormSq (u.grad x))
      (translatedCube d (n + 1) c) volume)
    (hmassInt : IntegrableOn (fun x => u.toFun x ^ 2)
      (translatedCube d (n + 1) c) volume)
    (hpricecell : ∀ m ∈ priceIndexBox d k c (3 / 4 * (3 : ℝ) ^ n),
      MesoscopicCrossPriceEnergyOn a (openCubeSet (priceCell d k m))
        (openCubeSet (priceCell d k m)) u.toFun u.grad chi t P R Sc)
    (henergycell : ∀ m ∈ mesoIndexBox d k (n + 1) c,
      CoarseEnergyBoundOn a (mesoCell d k m) (mesoCore d k m) u.toFun u.grad
        t Gam0)
    (hsmall : 81 * (P * (Gam0 * 27 ^ d + Sc)) ^ 2 * R ^ 2 *
      (Gam0 * 27 ^ d + Sc) * t ≤ eta ^ 4) :
    (∫ x in translatedCube d n c, a x * vecNormSq (u.grad x) ∂volume) ≤
      eta * t⁻¹ * ∫ x in translatedCube d (n + 1) c, u.toFun x ^ 2 ∂volume := by
  have hprice := mesoscopicCrossPriceEnergyOn_contraction_pair_of_triadicCells
    hkn ht hP.le hR hSc haNonneg hchiBox hcrossInt henergyInt hmassInt hpricecell
  have henergy := coarseEnergyBoundOn_contraction_pair_of_mesoCells
    (by omega : k ≤ n) ht hGam0.le
    (fun x => mul_nonneg (haNonneg x) (vecNormSq_nonneg _)) henergyInt hmassInt
    henergycell
  have hGam : (0 : ℝ) < Gam0 * 27 ^ d := by positivity
  exact massive_local_l2_translatedCube_coarse_energy' hEll haNonneg ht heta
    hP hGam hR hSc hbeta1 u hu hchi hchiC hchiBox hchi_le hchi_one hK hprice
    henergy hsmall

/-! ## 3. The frozen whole-space carrier -/

/-- **The whole-space carrier inherits the coarse Caccioppoli.**

The analogue of `wholeSpaceSolution_translatedCube_mass_contraction_of_local`
for the energy: the carrier's local `H¹` solution on the enlargement agrees with
the carrier there, and its gradient agrees almost everywhere, which is all the
energy integral needs.  The datum must vanish on the enlargement (the
zero-forcing hypothesis, i.e. the manuscript's "the terms containing `f` occur
only for `Q ∈ 𝒞`"). -/
theorem wholeSpaceSolution_translatedCell_coarse_energy_le_of_local
    {a f : Vec d → ℝ} {t eta : ℝ} {n : ℤ} {z : Vec d}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hf0 : ∀ x ∈ translatedCube d (n + 1) z, f x = 0)
    (hlocal : ∀ v : H1Function (translatedCube d (n + 1) z),
      IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹
        (translatedCube d (n + 1) z) v (fun _ ↦ (0 : ℝ)) →
      (∫ x in translatedCube d n z, a x * vecNormSq (v.grad x) ∂volume) ≤
        eta * t⁻¹ * ∫ x in translatedCube d (n + 1) z, v.toFun x ^ 2 ∂volume) :
    (∫ x in translatedCube d n z, a x * vecNormSq (u.grad x) ∂volume) ≤
      eta * t⁻¹ * ∫ x in translatedCube d (n + 1) z, u.toFun x ^ 2 ∂volume := by
  classical
  have hWdom : IsOpenBoundedConvexDomain (translatedCube d (n + 1) z) :=
    isOpenBoundedConvexDomain_translatedCube (n + 1) z
  have hWmeas : MeasurableSet (translatedCube d (n + 1) z) :=
    hWdom.isOpen.measurableSet
  have hQW : translatedCube d n z ⊆ translatedCube d (n + 1) z :=
    translatedCube_subset_succ d n z
  obtain ⟨v, hval, hgrad, hsol⟩ :=
    u.locally_weak_solution (translatedCube d (n + 1) z) hWdom
  have hsol0 : IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹
      (translatedCube d (n + 1) z) v (fun _ ↦ (0 : ℝ)) := by
    intro phi
    refine (hsol phi).trans ?_
    refine setIntegral_congr_fun hWmeas fun x hx ↦ ?_
    simp [hf0 x hx]
  have hbase := hlocal v hsol0
  have hgradQ : v.grad =ᵐ[volume.restrict (translatedCube d n z)] u.grad :=
    ae_restrict_of_ae_restrict_of_subset hQW hgrad
  have hEnergy : (∫ x in translatedCube d n z,
      a x * vecNormSq (v.grad x) ∂volume) =
      ∫ x in translatedCube d n z, a x * vecNormSq (u.grad x) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hgradQ] with x hx
    rw [hx]
  have hWval : (∫ x in translatedCube d (n + 1) z, v.toFun x ^ 2 ∂volume) =
      ∫ x in translatedCube d (n + 1) z, u.toFun x ^ 2 ∂volume := by
    refine setIntegral_congr_fun hWmeas fun x hx ↦ ?_
    rw [hval x hx]
  rwa [hEnergy, hWval] at hbase

/-- **The coarse Caccioppoli for the frozen carrier, from the per-cell legs.**

With the energy conclusion: the two mesoscopic legs are assumed for the
carrier's own fields `u.toFun`, `u.grad` (the form in which the cover lemmas and
the per-cell analytic theorems are stated) and transported to the carrier's
local solution by `mesoscopicCrossPriceEnergyOn_congr` /
`coarseEnergyBoundOn_congr`. -/
theorem wholeSpaceSolution_translatedCell_coarse_energy_le_of_cells
    {a f : Vec d → ℝ} {lam Lam t eta P R Sc Gam0 K : ℝ} {k n : ℤ} {c : Vec d}
    (hkn : k ≤ n - 3)
    (hEll : IsEllipticFieldOn lam Lam (translatedCube d (n + 1) c)
      (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x) (ht : 0 < t) (heta : 0 < eta)
    (hP : 0 < P) (hGam0 : 0 < Gam0) (hR : 0 ≤ R) (hSc : 0 ≤ Sc)
    (hbeta1 : eta ≤ 3 * (P * (Gam0 * 27 ^ d + Sc)))
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hf0 : ∀ x ∈ translatedCube d (n + 1) c, f x = 0)
    {chi : Vec d → ℝ} (hchi : ContDiff ℝ (⊤ : ℕ∞) chi)
    (hchiC : HasCompactSupport chi)
    (hchiBox : tsupport chi ⊆
      {x : Vec d | ∀ i, |x i - c i| ≤ 3 / 4 * (3 : ℝ) ^ n})
    (hchi_le : ∀ x, |chi x| ≤ 1)
    (hchi_one : ∀ x ∈ translatedCube d n c, chi x = 1)
    (hK : ∀ x, vecNormSq (fun i ↦ (fderiv ℝ chi x) (basisVec i)) ≤ K)
    (hcrossInt : IntegrableOn (fun x => a x * chi x * u.toFun x *
      vecDot (u.grad x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)))
      (translatedCube d (n + 1) c) volume)
    (hpricecell : ∀ m ∈ priceIndexBox d k c (3 / 4 * (3 : ℝ) ^ n),
      MesoscopicCrossPriceEnergyOn a (openCubeSet (priceCell d k m))
        (openCubeSet (priceCell d k m)) u.toFun u.grad chi t P R Sc)
    (henergycell : ∀ m ∈ mesoIndexBox d k (n + 1) c,
      CoarseEnergyBoundOn a (mesoCell d k m) (mesoCore d k m) u.toFun u.grad
        t Gam0)
    (hsmall : 81 * (P * (Gam0 * 27 ^ d + Sc)) ^ 2 * R ^ 2 *
      (Gam0 * 27 ^ d + Sc) * t ≤ eta ^ 4) :
    (∫ x in translatedCube d n c, a x * vecNormSq (u.grad x) ∂volume) ≤
      eta * t⁻¹ * ∫ x in translatedCube d (n + 1) c, u.toFun x ^ 2 ∂volume := by
  classical
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) _
  have hrho1 : (0 : ℝ) < 4 / 5 * (3 : ℝ) ^ n := by positivity
  have hslack := price_slack_bound (k := k) (n := n) hkn
  have hWdom : IsOpenBoundedConvexDomain (translatedCube d (n + 1) c) :=
    isOpenBoundedConvexDomain_translatedCube (n + 1) c
  have hWmeas : MeasurableSet (translatedCube d (n + 1) c) :=
    hWdom.isOpen.measurableSet
  have hQmeas : MeasurableSet (translatedCube d n c) :=
    (isOpenBoundedConvexDomain_translatedCube n c).isOpen.measurableSet
  obtain ⟨v, hval, hgrad, hsol⟩ :=
    u.locally_weak_solution (translatedCube d (n + 1) c) hWdom
  have hsol0 : IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹
      (translatedCube d (n + 1) c) v (fun _ ↦ (0 : ℝ)) := by
    intro phi
    refine (hsol phi).trans ?_
    refine setIntegral_congr_fun hWmeas fun x hx ↦ ?_
    simp [hf0 x hx]
  have huv : ∀ x ∈ translatedCube d (n + 1) c, u.toFun x = v.toFun x :=
    fun x hx => (hval x hx).symm
  have hguv : u.grad =ᵐ[volume.restrict (translatedCube d (n + 1) c)] v.grad :=
    hgrad.symm
  have hpriceSub : ∀ m ∈ priceIndexBox d k c (3 / 4 * (3 : ℝ) ^ n),
      openCubeSet (priceCell d k m) ⊆ translatedCube d (n + 1) c := by
    intro m hm
    refine (openCubeSet_priceCell_subset k m).trans ?_
    exact (cubeSet_priceCell_subset_ball hrho1 hslack hm).trans
      (ball_subset_translatedCube_succ d n c)
  have hmesoSub : ∀ m ∈ mesoIndexBox d k (n + 1) c,
      mesoCell d k m ⊆ translatedCube d (n + 1) c :=
    fun m hm => mesoCell_subset_translatedCube hm
  have hpricecell' : ∀ m ∈ priceIndexBox d k c (3 / 4 * (3 : ℝ) ^ n),
      MesoscopicCrossPriceEnergyOn a (openCubeSet (priceCell d k m))
        (openCubeSet (priceCell d k m)) v.toFun v.grad chi t P R Sc := by
    intro m hm
    exact mesoscopicCrossPriceEnergyOn_congr (measurableSet_openCubeSet _)
      (subset_refl _) (fun x hx => huv x (hpriceSub m hm hx))
      (ae_mono (Measure.restrict_mono (hpriceSub m hm) le_rfl) hguv)
      (hpricecell m hm)
  have henergycell' : ∀ m ∈ mesoIndexBox d k (n + 1) c,
      CoarseEnergyBoundOn a (mesoCell d k m) (mesoCore d k m) v.toFun v.grad
        t Gam0 := by
    intro m hm
    exact coarseEnergyBoundOn_congr (measurableSet_mesoCell k m)
      (mesoCore_subset_mesoCell k m) (fun x hx => huv x (hmesoSub m hm hx))
      (ae_mono (Measure.restrict_mono (hmesoSub m hm) le_rfl) hguv)
      (henergycell m hm)
  have henergyInt : IntegrableOn (fun x => a x * vecNormSq (v.grad x))
      (translatedCube d (n + 1) c) volume := by
    refine (u.integrable_energy.restrict (s := translatedCube d (n + 1) c)).congr ?_
    filter_upwards [hguv] with x hx
    rw [hx]
  have hmassInt : IntegrableOn (fun x => v.toFun x ^ 2)
      (translatedCube d (n + 1) c) volume := by
    refine (u.memL2_toFun.integrable_sq.restrict
      (s := translatedCube d (n + 1) c)).congr ?_
    filter_upwards [(ae_restrict_iff' hWmeas).2 (Filter.Eventually.of_forall huv)]
      with x hx
    rw [hx]
  have hcrossInt' : IntegrableOn (fun x => a x * chi x * v.toFun x *
      vecDot (v.grad x) (fun i ↦ (fderiv ℝ chi x) (basisVec i)))
      (translatedCube d (n + 1) c) volume := by
    refine hcrossInt.congr ?_
    filter_upwards [(ae_restrict_iff' hWmeas).2 (Filter.Eventually.of_forall huv),
      hguv] with x hx hgx
    rw [hx, hgx]
  have hres := massive_local_l2_translatedCube_coarse_energy_of_cells hkn
    hEll haNonneg ht heta hP hGam0 hR hSc hbeta1 v hsol0 hchi hchiC hchiBox
    hchi_le hchi_one hK hcrossInt' henergyInt hmassInt hpricecell' henergycell'
    hsmall
  have hgradQ : v.grad =ᵐ[volume.restrict (translatedCube d n c)] u.grad :=
    ae_restrict_of_ae_restrict_of_subset (translatedCube_subset_succ d n c)
      hgrad
  have hEnergy : (∫ x in translatedCube d n c,
      a x * vecNormSq (v.grad x) ∂volume) =
      ∫ x in translatedCube d n c, a x * vecNormSq (u.grad x) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hgradQ] with x hx
    rw [hx]
  have hWval : (∫ x in translatedCube d (n + 1) c, v.toFun x ^ 2 ∂volume) =
      ∫ x in translatedCube d (n + 1) c, u.toFun x ^ 2 ∂volume := by
    refine setIntegral_congr_fun hWmeas fun x hx ↦ ?_
    rw [hval x hx]
  rwa [hEnergy, hWval] at hres

/-! ## 4. The recentred, normalized form: the `(B-1)` Caccioppoli input -/

/-- **The energy slot's Caccioppoli input with the cell's own coarse
constants.**

The exact analogue of
`wholeSpaceSolution_recentredCell_localSymmetricEnergy_sq_le`
(`FluxRowSlotsWholeSpaceCell.lean`) with the crude constant
`4096 d Λ 3^{-2m}` replaced by the coarse one `eta * t⁻¹`.  This is what
`fluxRowSlots_energy_slot_of_inputs` consumes as `hcacc` with
`Cc := eta * t⁻¹`, `V := cubeVolume (originCube d m)`, and it is the shape the
manuscript uses. -/
theorem wholeSpaceSolution_recentredCell_localSymmetricEnergy_sq_le_coarse
    {a f : Vec d → ℝ} {t eta : ℝ} {m : ℤ} {z : Vec d}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hf0 : ∀ x ∈ translatedCube d (m + 1) z, f x = 0)
    (haNonneg : ∀ x, 0 ≤ a x)
    (hlocal : ∀ v : H1Function (translatedCube d (m + 1) z),
      IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹
        (translatedCube d (m + 1) z) v (fun _ ↦ (0 : ℝ)) →
      (∫ x in translatedCube d m z, a x * vecNormSq (v.grad x) ∂volume) ≤
        eta * t⁻¹ * ∫ x in translatedCube d (m + 1) z, v.toFun x ^ 2 ∂volume)
    (acoeff : Ch02.CoeffOn (Ch02.cubeDomain (originCube d m)))
    (ha : ∀ y, acoeff.toCoeffField y = scalarCoeffField (fun x ↦ a (x + z)) y)
    (u0 : H1Function (openCubeSet (originCube d m)))
    (hu0 : u0.grad =ᵐ[volume.restrict (openCubeSet (originCube d m))]
      fun x ↦ u.grad (x + z)) :
    cubeVolume (originCube d m) *
        (localSymmetricEnergyENorm (originCube d m) acoeff u0).toReal ^ 2 ≤
      eta * t⁻¹ *
        ∫ x in translatedCube d (m + 1) z, u.toFun x ^ 2 ∂volume := by
  rw [cubeVolume_mul_recentred_localSymmetricEnergy_sq_eq z acoeff ha haNonneg
    u0 u.grad hu0]
  exact wholeSpaceSolution_translatedCell_coarse_energy_le_of_local u hf0 hlocal

/-- **The `(B-1)` Caccioppoli input with the cell's own coarse constants, from
the per-cell mesoscopic legs.**

`wholeSpaceSolution_recentredCell_localSymmetricEnergy_sq_le_coarse` with the
abstract local hypothesis replaced by the two mesoscopic legs of §2 for the
carrier's own fields.  This is the form the flux energy slot consumes: the left
side is `cubeVolume (originCube d m) ‖u₀‖²_{E}`, the normalization of
`localSymmetricEnergyENorm`, and the constant is `eta * t⁻¹`. -/
theorem wholeSpaceSolution_recentredCell_localSymmetricEnergy_sq_le_coarse_of_cells
    {a f : Vec d → ℝ} {lam Lam t eta P R Sc Gam0 K : ℝ} {k m : ℤ} {z : Vec d}
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
        (openCubeSet (priceCell d k j)) u.toFun u.grad chi t P R Sc)
    (henergycell : ∀ j ∈ mesoIndexBox d k (m + 1) z,
      CoarseEnergyBoundOn a (mesoCell d k j) (mesoCore d k j) u.toFun u.grad
        t Gam0)
    (hsmall : 81 * (P * (Gam0 * 27 ^ d + Sc)) ^ 2 * R ^ 2 *
      (Gam0 * 27 ^ d + Sc) * t ≤ eta ^ 4)
    (acoeff : Ch02.CoeffOn (Ch02.cubeDomain (originCube d m)))
    (ha : ∀ y, acoeff.toCoeffField y = scalarCoeffField (fun x ↦ a (x + z)) y)
    (u0 : H1Function (openCubeSet (originCube d m)))
    (hu0 : u0.grad =ᵐ[volume.restrict (openCubeSet (originCube d m))]
      fun x ↦ u.grad (x + z)) :
    cubeVolume (originCube d m) *
        (localSymmetricEnergyENorm (originCube d m) acoeff u0).toReal ^ 2 ≤
      eta * t⁻¹ *
        ∫ x in translatedCube d (m + 1) z, u.toFun x ^ 2 ∂volume := by
  rw [cubeVolume_mul_recentred_localSymmetricEnergy_sq_eq z acoeff ha haNonneg
    u0 u.grad hu0]
  exact wholeSpaceSolution_translatedCell_coarse_energy_le_of_cells hkm hEll
    haNonneg ht heta hP hGam0 hR hSc hbeta1 u hf0 hchi hchiC hchiBox hchi_le
    hchi_one hK hcrossInt hpricecell henergycell hsmall

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
