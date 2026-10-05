
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsMesoscopicRow
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceProviderGMC
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SmallContrastScalarBridge

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Model
open _root_.SubdiffusiveProcess.Section8

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ## 1. The `L²` contraction, for every carrier, almost surely -/

/-- **`hL2`, discharged.**

Almost surely, *every* whole-space divergence-resolvent carrier for the finite
cutoff coefficient satisfies the sharp `L²` contraction.  The frozen carrier
`WholeSpaceDivergenceResolventSolution` does not record the bound, and the
exterior row of `WholeSpaceRows` is quantified over every carrier; the bound is
transported from the constructed solution by the almost-sure uniqueness. -/
theorem ae_forall_wholeSpaceSolution_l2_bound [NeZero d]
    (M : GMCModel d) (L : ℕ) {t : ℝ} (ht : 0 < t) (x0 : Vec d) :
    ∀ᵐ omega ∂M.P.toMeasure, ∀ f : Vec d → ℝ, MemLp f 2 volume →
      ∀ u : WholeSpaceDivergenceResolventSolution (aCutoff M L omega) t f,
        ∫ x, u.toFun x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume := by
  refine (ae_forall_exists_finiteCutoffWholeSpaceSolution M L ht x0).mono ?_
  intro omega hex f hf u
  obtain ⟨w, huniq, hL2, _henergy⟩ := hex f hf
  have hae : w.toFun =ᵐ[volume] u.toFun := (huniq u).1
  have hsq : (fun x ↦ w.toFun x ^ 2) =ᵐ[volume] fun x ↦ u.toFun x ^ 2 :=
    hae.mono fun x hx ↦ by simp only [hx]
  have hint : ∫ x, w.toFun x ^ 2 ∂volume = ∫ x, u.toFun x ^ 2 ∂volume :=
    integral_congr_ae hsq
  rw [← hint]
  exact hL2

/-! ## 2. Ellipticity of a continuous positive coefficient on a bounded set -/

/-- **`hEll`, discharged for every continuous positive coefficient.**

On a bounded measurable set a continuous positive scalar coefficient attains a
positive minimum and a finite maximum on the (compact) closure, and the scalar
ellipticity carrier of `Section6BoundedMultiplier` then applies.  No uniformity
in the set is claimed and none is available. -/
theorem exists_isEllipticFieldOn_of_continuous_of_pos {a : Vec d → ℝ}
    (hcont : Continuous a) (hpos : ∀ x, 0 < a x) {W : Set (Vec d)}
    (hW : MeasurableSet W) (hWb : Bornology.IsBounded W) :
    ∃ lam Lam : ℝ, 0 < lam ∧
      IsEllipticFieldOn lam Lam W (scalarCoeffField a) := by
  classical
  rcases W.eq_empty_or_nonempty with hempty | hne
  · refine ⟨1, 1, one_pos,
      Section6BoundedMultiplier.isEllipticFieldOn_scalarCoeffField_of_continuousOn
        hW hcont.continuousOn one_pos ?_⟩
    intro x hx
    rw [hempty] at hx
    exact absurd hx (Set.notMem_empty x)
  · have hK : IsCompact (closure W) := hWb.isCompact_closure
    have hKne : (closure W).Nonempty := hne.mono subset_closure
    obtain ⟨xmin, _hxmin, hmin⟩ := hK.exists_isMinOn hKne hcont.continuousOn
    obtain ⟨xmax, _hxmax, hmax⟩ := hK.exists_isMaxOn hKne hcont.continuousOn
    exact ⟨a xmin, a xmax, hpos xmin,
      Section6BoundedMultiplier.isEllipticFieldOn_scalarCoeffField_of_continuousOn
        hW hcont.continuousOn (hpos xmin)
        fun x hx ↦ ⟨hmin (subset_closure hx), hmax (subset_closure hx)⟩⟩

/-- The enlargement of a stopping cell is a bounded measurable set. -/
theorem measurableSet_translatedCube (m : ℤ) (z : Vec d) :
    MeasurableSet (translatedCube d m z) :=
  (isOpenBoundedConvexDomain_translatedCube m z).isOpen.measurableSet

/-- The enlargement of a stopping cell is bounded. -/
theorem isBounded_translatedCube (m : ℤ) (z : Vec d) :
    Bornology.IsBounded (translatedCube d m z) :=
  (isOpenBoundedConvexDomain_translatedCube m z).isBoundedDomain.isBounded

/-- The ellipticity conjunct of `hcell`, for a continuous positive
coefficient. -/
theorem exists_isEllipticFieldOn_translatedCube {a : Vec d → ℝ}
    (hcont : Continuous a) (hpos : ∀ x, 0 < a x) (m : ℤ) (z : Vec d) :
    ∃ lam Lam : ℝ, 0 < lam ∧
      IsEllipticFieldOn lam Lam (translatedCube d m z) (scalarCoeffField a) :=
  exists_isEllipticFieldOn_of_continuous_of_pos hcont hpos
    (measurableSet_translatedCube m z) (isBounded_translatedCube m z)

/-! ## 3. The exterior row without the ellipticity hypothesis -/

/-- **The exterior row of `WholeSpaceRows`, for a continuous positive
coefficient.**

Identical to `wholeSpaceSolution_exterior_row_of_coarse_mesoscopic_cells`
except that the two ellipticity constants `lam`, `Lam` and the ellipticity
conjunct of `hcell` are gone: they are produced internally by
`exists_isEllipticFieldOn_translatedCube`.  This is legitimate because `lam` and
`Lam` occur in no other hypothesis and in no part of the conclusion.

Every remaining hypothesis is either a stopping-geometry certificate
(`hinitial`, `hrepair`, `hgood`), the `L²` contraction of §1, or one of the
per-cell analytic packages. -/
theorem wholeSpaceSolution_exterior_row_of_continuous_coefficient
    [NeZero d] {Omega : Type*} {base : ℤ} {failure : TriadicCube d → Set Omega}
    {omega : Omega} {a f : Vec d → ℝ} {t : ℝ} (ht : 0 < t)
    (hacont : Continuous a) (hapos : ∀ x, 0 < a x)
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hL2 : ∫ x, u.toFun x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (source : Finset (RefinedStoppingCell failure omega base))
    (hsourceNonempty : source.Nonempty) (x0 : Vec d) {R epsilon cst C : ℝ}
    {Kbr : ℕ}
    (hR : 0 < R) (heps : 0 < epsilon)
    (hcst : cst ≤ epsilon * Real.log 2 / 3)
    (hC : 2 * ((stoppingGraphLevelCells repairedStoppingGraph source
      hsourceNonempty 0).card : ℝ) ≤ C)
    (hgood : ∀ k : ℕ, Kbr ≤ k → ¬ RepairedStoppingShortCrossing source
      hsourceNonempty x0 R epsilon k)
    (scaleOf : RefinedStoppingCell failure omega base → ℤ)
    (P Rp Sc Gam0 K : RefinedStoppingCell failure omega base → ℝ)
    (chi : RefinedStoppingCell failure omega base → Vec d → ℝ)
    (hcell : ∀ q,
      0 < stoppingGraphDistance repairedStoppingGraph source hsourceNonempty q →
      scaleOf q ≤ refinedStoppingScale q - 3 ∧
      0 < P q ∧ 0 < Gam0 q ∧ 0 ≤ Rp q ∧ 0 ≤ Sc q ∧
      repairedStoppingContractionFactor d ≤
        3 * (P q * (Gam0 q * 27 ^ d + Sc q)) ∧
      (∀ x ∈ translatedCube d (refinedStoppingScale q + 1)
        (refinedStoppingCenter q), f x = 0) ∧
      ContDiff ℝ (⊤ : ℕ∞) (chi q) ∧ HasCompactSupport (chi q) ∧
      tsupport (chi q) ⊆ {x : Vec d | ∀ i,
        |x i - refinedStoppingCenter q i| ≤
          3 / 4 * (3 : ℝ) ^ refinedStoppingScale q} ∧
      (∀ x, |chi q x| ≤ 1) ∧
      (∀ x ∈ translatedCube d (refinedStoppingScale q)
        (refinedStoppingCenter q), chi q x = 1) ∧
      (∀ x, vecNormSq (fun i ↦ (fderiv ℝ (chi q) x) (basisVec i)) ≤ K q) ∧
      (∀ m ∈ priceIndexBox d (scaleOf q) (refinedStoppingCenter q)
          (3 / 4 * (3 : ℝ) ^ refinedStoppingScale q),
        ∀ v : H1Function (openCubeSet (priceCell d (scaleOf q) m)),
        IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹
          (openCubeSet (priceCell d (scaleOf q) m)) v (fun _ ↦ (0 : ℝ)) →
        MesoscopicCrossPriceEnergyOn a
          (openCubeSet (priceCell d (scaleOf q) m))
          (openCubeSet (priceCell d (scaleOf q) m)) v.toFun v.grad (chi q)
          t (P q) (Rp q) (Sc q)) ∧
      (∀ m ∈ mesoIndexBox d (scaleOf q) (refinedStoppingScale q + 1)
          (refinedStoppingCenter q),
        ∀ v : H1Function (mesoCell d (scaleOf q) m),
        IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹
          (mesoCell d (scaleOf q) m) v (fun _ ↦ (0 : ℝ)) →
        CoarseEnergyBoundOn a (mesoCell d (scaleOf q) m)
          (mesoCore d (scaleOf q) m) v.toFun v.grad t (Gam0 q)) ∧
      81 * (P q * (Gam0 q * 27 ^ d + Sc q)) ^ 2 * Rp q ^ 2 *
        (Gam0 q * 27 ^ d + Sc q) * t ≤
          repairedStoppingContractionFactor d ^ 4) :
    ∀ r, (3 : ℝ) ^ Kbr * R ≤ r →
      ∫ x in (Metric.ball x0 r)ᶜ, u.toFun x ^ 2 ∂volume ≤
        C * Real.exp (-cst * r / R) * ∫ x, f x ^ 2 ∂volume := by
  classical
  refine wholeSpaceSolution_exterior_row_of_coarse_mesoscopic_cells ht
    (fun x ↦ (hapos x).le) u hL2 hinitial hrepair source hsourceNonempty x0 hR
    heps hcst hC hgood scaleOf
    (fun q ↦ Classical.choose (exists_isEllipticFieldOn_translatedCube hacont
      hapos (refinedStoppingScale q + 1) (refinedStoppingCenter q)))
    (fun q ↦ Classical.choose (Classical.choose_spec
      (exists_isEllipticFieldOn_translatedCube hacont hapos
        (refinedStoppingScale q + 1) (refinedStoppingCenter q))))
    P Rp Sc Gam0 K chi ?_
  intro q hq
  obtain ⟨hkn, hP, hGam0, hRp, hSc, hbeta1, hf0, hchi, hchiC, hchiBox,
    hchi_le, hchi_one, hK, hpricelocal, henergylocal, hsmall⟩ := hcell q hq
  refine ⟨hkn, ?_, hP, hGam0, hRp, hSc, hbeta1, hf0, hchi, hchiC, hchiBox,
    hchi_le, hchi_one, hK, hpricelocal, henergylocal, hsmall⟩
  exact (Classical.choose_spec (Classical.choose_spec
    (exists_isEllipticFieldOn_translatedCube hacont hapos
      (refinedStoppingScale q + 1) (refinedStoppingCenter q)))).2

/-! ## 4. The vanishing of the datum on the far cells -/

/-- **`hf0`, discharged for the canonical source family.**

If the source `Finset` is the canonical one — the cells whose enlargement meets
the closed source ball (`stoppingSourceCells`) — then a cell at *positive* graph
distance from the source is not in the source, so its enlargement misses the
ball, and the datum, supported in the ball, vanishes on it.  This is the
`hf0` conjunct of `hcell`, and it is exactly what the support hypothesis
`Function.support f ⊆ Metric.ball x0 R` of `WholeSpaceRows` is for. -/
theorem eq_zero_of_mem_enlargement_of_pos_stoppingGraphDistance {I : Type*}
    {f : Vec d → ℝ} {x0 : Vec d} {R : ℝ} (G : SimpleGraph I)
    (enlargement : I → Set (Vec d)) (hlf : LocallyFinite enlargement)
    (hsourceNonempty : (stoppingSourceCells enlargement hlf x0 R).Nonempty)
    (hsupp : Function.support f ⊆ Metric.ball x0 R) {q : I}
    (hq : 0 < stoppingGraphDistance G
      (stoppingSourceCells enlargement hlf x0 R) hsourceNonempty q)
    {x : Vec d} (hx : x ∈ enlargement q) : f x = 0 := by
  by_contra hne
  have hmem : q ∈ stoppingSourceCells enlargement hlf x0 R := by
    refine (mem_stoppingSourceCells_iff enlargement hlf x0 R q).mpr ⟨x, hx, ?_⟩
    exact Metric.ball_subset_closedBall (hsupp hne)
  rw [stoppingGraphDistance_eq_zero_of_mem G hsourceNonempty hmem] at hq
  exact lt_irrefl 0 hq

/-- `hf0` in the exact conjunct shape of `hcell`, for the repaired stopping
partition with the canonical source family. -/
theorem forall_eq_zero_translatedCube_of_pos_stoppingGraphDistance
    {Omega : Type*} {base : ℤ} {failure : TriadicCube d → Set Omega}
    {omega : Omega} {f : Vec d → ℝ} {x0 : Vec d} {R : ℝ}
    (hlf : LocallyFinite fun q : RefinedStoppingCell failure omega base ↦
      translatedCube d (refinedStoppingScale q + 1) (refinedStoppingCenter q))
    (hsourceNonempty : (stoppingSourceCells
      (fun q : RefinedStoppingCell failure omega base ↦
        translatedCube d (refinedStoppingScale q + 1)
          (refinedStoppingCenter q)) hlf x0 R).Nonempty)
    (hsupp : Function.support f ⊆ Metric.ball x0 R)
    (q : RefinedStoppingCell failure omega base)
    (hq : 0 < stoppingGraphDistance repairedStoppingGraph
      (stoppingSourceCells
        (fun p : RefinedStoppingCell failure omega base ↦
          translatedCube d (refinedStoppingScale p + 1)
            (refinedStoppingCenter p)) hlf x0 R) hsourceNonempty q) :
    ∀ x ∈ translatedCube d (refinedStoppingScale q + 1)
      (refinedStoppingCenter q), f x = 0 := fun _ hx =>
  eq_zero_of_mem_enlargement_of_pos_stoppingGraphDistance repairedStoppingGraph
    _ hlf hsourceNonempty hsupp hq hx

/-! ## 5. The audited exterior row

Everything this bundle can discharge is discharged: the ellipticity of §2 and
the vanishing of the datum of §4 are gone from `hcell`, and `hL2` is supplied by
§1 for the multiscale coefficient.  What survives is exactly

* three stopping-geometry certificates — `hinitial`, `hrepair` (the director's)
  and `hlf`, the local finiteness of the *enlargement* family over the refined
  cells, which the canonical source family needs;
* the eventual short-crossing certificate `hgood` (`∀ k ≥ Kbr`), at the
  canonical source;
* the per-cell analytic package: the mesoscopic scale choice, the cutoff, the
  price leg, the energy leg and the two numerical balances.
-/

/-- **The exterior conjunct of `WholeSpaceRows`, audited.**

The conclusion is verbatim the exterior conjunct at `Rstar = 3 ^ Kbr * R`
(the frozen anchor's random radius; note `R ≤ 3 ^ Kbr * R`).  Compare
`wholeSpaceSolution_exterior_row_of_coarse_mesoscopic_cells`: the ellipticity
constants and conjunct are gone (§2), the datum-vanishing conjunct is gone (§4,
via the canonical source family), and `source` is no longer a free choice. -/
theorem wholeSpaceSolution_exterior_row_audited
    [NeZero d] {Omega : Type*} {base : ℤ} {failure : TriadicCube d → Set Omega}
    {omega : Omega} {a f : Vec d → ℝ} {t : ℝ} (ht : 0 < t)
    (hacont : Continuous a) (hapos : ∀ x, 0 < a x)
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hL2 : ∫ x, u.toFun x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (hlf : LocallyFinite fun q : RefinedStoppingCell failure omega base ↦
      translatedCube d (refinedStoppingScale q + 1) (refinedStoppingCenter q))
    (x0 : Vec d) {R epsilon cst C : ℝ} {Kbr : ℕ}
    (hsourceNonempty : (stoppingSourceCells
      (fun q : RefinedStoppingCell failure omega base ↦
        translatedCube d (refinedStoppingScale q + 1)
          (refinedStoppingCenter q)) hlf x0 R).Nonempty)
    (hsupp : Function.support f ⊆ Metric.ball x0 R)
    (hR : 0 < R) (heps : 0 < epsilon)
    (hcst : cst ≤ epsilon * Real.log 2 / 3)
    (hC : 2 * ((stoppingGraphLevelCells repairedStoppingGraph
      (stoppingSourceCells
        (fun q : RefinedStoppingCell failure omega base ↦
          translatedCube d (refinedStoppingScale q + 1)
            (refinedStoppingCenter q)) hlf x0 R)
      hsourceNonempty 0).card : ℝ) ≤ C)
    (hgood : ∀ k : ℕ, Kbr ≤ k → ¬ RepairedStoppingShortCrossing
      (stoppingSourceCells
        (fun q : RefinedStoppingCell failure omega base ↦
          translatedCube d (refinedStoppingScale q + 1)
            (refinedStoppingCenter q)) hlf x0 R)
      hsourceNonempty x0 R epsilon k)
    (scaleOf : RefinedStoppingCell failure omega base → ℤ)
    (P Rp Sc Gam0 K : RefinedStoppingCell failure omega base → ℝ)
    (chi : RefinedStoppingCell failure omega base → Vec d → ℝ)
    (hcell : ∀ q,
      0 < stoppingGraphDistance repairedStoppingGraph
        (stoppingSourceCells
          (fun p : RefinedStoppingCell failure omega base ↦
            translatedCube d (refinedStoppingScale p + 1)
              (refinedStoppingCenter p)) hlf x0 R) hsourceNonempty q →
      scaleOf q ≤ refinedStoppingScale q - 3 ∧
      0 < P q ∧ 0 < Gam0 q ∧ 0 ≤ Rp q ∧ 0 ≤ Sc q ∧
      repairedStoppingContractionFactor d ≤
        3 * (P q * (Gam0 q * 27 ^ d + Sc q)) ∧
      ContDiff ℝ (⊤ : ℕ∞) (chi q) ∧ HasCompactSupport (chi q) ∧
      tsupport (chi q) ⊆ {x : Vec d | ∀ i,
        |x i - refinedStoppingCenter q i| ≤
          3 / 4 * (3 : ℝ) ^ refinedStoppingScale q} ∧
      (∀ x, |chi q x| ≤ 1) ∧
      (∀ x ∈ translatedCube d (refinedStoppingScale q)
        (refinedStoppingCenter q), chi q x = 1) ∧
      (∀ x, vecNormSq (fun i ↦ (fderiv ℝ (chi q) x) (basisVec i)) ≤ K q) ∧
      (∀ m ∈ priceIndexBox d (scaleOf q) (refinedStoppingCenter q)
          (3 / 4 * (3 : ℝ) ^ refinedStoppingScale q),
        ∀ v : H1Function (openCubeSet (priceCell d (scaleOf q) m)),
        IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹
          (openCubeSet (priceCell d (scaleOf q) m)) v (fun _ ↦ (0 : ℝ)) →
        MesoscopicCrossPriceEnergyOn a
          (openCubeSet (priceCell d (scaleOf q) m))
          (openCubeSet (priceCell d (scaleOf q) m)) v.toFun v.grad (chi q)
          t (P q) (Rp q) (Sc q)) ∧
      (∀ m ∈ mesoIndexBox d (scaleOf q) (refinedStoppingScale q + 1)
          (refinedStoppingCenter q),
        ∀ v : H1Function (mesoCell d (scaleOf q) m),
        IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹
          (mesoCell d (scaleOf q) m) v (fun _ ↦ (0 : ℝ)) →
        CoarseEnergyBoundOn a (mesoCell d (scaleOf q) m)
          (mesoCore d (scaleOf q) m) v.toFun v.grad t (Gam0 q)) ∧
      81 * (P q * (Gam0 q * 27 ^ d + Sc q)) ^ 2 * Rp q ^ 2 *
        (Gam0 q * 27 ^ d + Sc q) * t ≤
          repairedStoppingContractionFactor d ^ 4) :
    ∀ r, (3 : ℝ) ^ Kbr * R ≤ r →
      ∫ x in (Metric.ball x0 r)ᶜ, u.toFun x ^ 2 ∂volume ≤
        C * Real.exp (-cst * r / R) * ∫ x, f x ^ 2 ∂volume := by
  refine wholeSpaceSolution_exterior_row_of_continuous_coefficient ht hacont
    hapos u hL2 hinitial hrepair _ hsourceNonempty x0 hR heps hcst hC hgood
    scaleOf P Rp Sc Gam0 K chi ?_
  intro q hq
  obtain ⟨hkn, hP, hGam0, hRp, hSc, hbeta1, hchi, hchiC, hchiBox,
    hchi_le, hchi_one, hK, hpricelocal, henergylocal, hsmall⟩ := hcell q hq
  exact ⟨hkn, hP, hGam0, hRp, hSc, hbeta1,
    forall_eq_zero_translatedCube_of_pos_stoppingGraphDistance hlf
      hsourceNonempty hsupp q hq,
    hchi, hchiC, hchiBox, hchi_le, hchi_one, hK, hpricelocal, henergylocal,
    hsmall⟩

/-! ## 6. The canonical source family is itself free

`locallyFinite_refinedStoppingCell_enlargements`
(`StoppingPartitionRepairedNeighbourCover.lean`) already derives the local
finiteness of the *enlargement* family from `hinitial` and `hrepair`, and
`iUnion_refinedStoppingCell_eq_univ` gives the cover, so both the source family
and its nonemptiness are determined by the two director certificates.  No third
certificate is needed. -/

/-- The canonical source family: the refined stopping cells whose enlargement
meets the closed source ball. -/
def refinedStoppingSource [NeZero d] {Omega : Type*} {base : ℤ}
    {failure : TriadicCube d → Set Omega} {omega : Omega}
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1) (x0 : Vec d) (R : ℝ) :
    Finset (RefinedStoppingCell failure omega base) :=
  stoppingSourceCells _
    (locallyFinite_refinedStoppingCell_enlargements hinitial hrepair) x0 R

/-- The canonical source family is nonempty. -/
theorem refinedStoppingSource_nonempty [NeZero d] {Omega : Type*} {base : ℤ}
    {failure : TriadicCube d → Set Omega} {omega : Omega}
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1) (x0 : Vec d) {R : ℝ} (hR : 0 ≤ R) :
    (refinedStoppingSource hinitial hrepair x0 R).Nonempty := by
  refine stoppingSourceCells_translatedCube_nonempty refinedStoppingScale
    refinedStoppingCenter _ ?_ x0 hR
  intro x
  have hcover := iUnion_refinedStoppingCell_eq_univ failure omega hinitial hrepair
  have hx : x ∈ ⋃ q : RefinedStoppingCell failure omega base,
      translatedCube d (refinedStoppingScale q) (refinedStoppingCenter q) := by
    rw [hcover]; trivial
  exact Set.mem_iUnion.mp hx

/-! ## 7. The exterior row from the two director certificates alone -/

/-- **The exterior conjunct of `WholeSpaceRows`, from the two director
certificates and the per-cell analytic package.**

Every stopping-geometry input other than `hinitial`, `hrepair` and the eventual
short-crossing certificate `hgood` is now internal: the source family, its
nonemptiness, the local finiteness of the enlargements, the ellipticity of the
coefficient on every enlargement, and the vanishing of the datum on the far
cells.  `hL2` is supplied by §1 for the multiscale coefficient.

The residual `hcell` is exactly the analytic per-cell package: the mesoscopic
scale choice, the cutoff, the price leg, the energy leg and the two numerical
balances. -/
theorem wholeSpaceSolution_exterior_row_of_stopping_certificates
    [NeZero d] {Omega : Type*} {base : ℤ} {failure : TriadicCube d → Set Omega}
    {omega : Omega} {a f : Vec d → ℝ} {t : ℝ} (ht : 0 < t)
    (hacont : Continuous a) (hapos : ∀ x, 0 < a x)
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hL2 : ∫ x, u.toFun x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume)
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (x0 : Vec d) {R epsilon cst C : ℝ} {Kbr : ℕ}
    (hR : 0 < R) (heps : 0 < epsilon)
    (hsupp : Function.support f ⊆ Metric.ball x0 R)
    (hcst : cst ≤ epsilon * Real.log 2 / 3)
    (hC : 2 * ((stoppingGraphLevelCells repairedStoppingGraph
      (refinedStoppingSource hinitial hrepair x0 R)
      (refinedStoppingSource_nonempty hinitial hrepair x0 hR.le) 0).card : ℝ)
        ≤ C)
    (hgood : ∀ k : ℕ, Kbr ≤ k → ¬ RepairedStoppingShortCrossing
      (refinedStoppingSource hinitial hrepair x0 R)
      (refinedStoppingSource_nonempty hinitial hrepair x0 hR.le)
      x0 R epsilon k)
    (scaleOf : RefinedStoppingCell failure omega base → ℤ)
    (P Rp Sc Gam0 K : RefinedStoppingCell failure omega base → ℝ)
    (chi : RefinedStoppingCell failure omega base → Vec d → ℝ)
    (hcell : ∀ q,
      0 < stoppingGraphDistance repairedStoppingGraph
        (refinedStoppingSource hinitial hrepair x0 R)
        (refinedStoppingSource_nonempty hinitial hrepair x0 hR.le) q →
      scaleOf q ≤ refinedStoppingScale q - 3 ∧
      0 < P q ∧ 0 < Gam0 q ∧ 0 ≤ Rp q ∧ 0 ≤ Sc q ∧
      repairedStoppingContractionFactor d ≤
        3 * (P q * (Gam0 q * 27 ^ d + Sc q)) ∧
      ContDiff ℝ (⊤ : ℕ∞) (chi q) ∧ HasCompactSupport (chi q) ∧
      tsupport (chi q) ⊆ {x : Vec d | ∀ i,
        |x i - refinedStoppingCenter q i| ≤
          3 / 4 * (3 : ℝ) ^ refinedStoppingScale q} ∧
      (∀ x, |chi q x| ≤ 1) ∧
      (∀ x ∈ translatedCube d (refinedStoppingScale q)
        (refinedStoppingCenter q), chi q x = 1) ∧
      (∀ x, vecNormSq (fun i ↦ (fderiv ℝ (chi q) x) (basisVec i)) ≤ K q) ∧
      (∀ m ∈ priceIndexBox d (scaleOf q) (refinedStoppingCenter q)
          (3 / 4 * (3 : ℝ) ^ refinedStoppingScale q),
        ∀ v : H1Function (openCubeSet (priceCell d (scaleOf q) m)),
        IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹
          (openCubeSet (priceCell d (scaleOf q) m)) v (fun _ ↦ (0 : ℝ)) →
        MesoscopicCrossPriceEnergyOn a
          (openCubeSet (priceCell d (scaleOf q) m))
          (openCubeSet (priceCell d (scaleOf q) m)) v.toFun v.grad (chi q)
          t (P q) (Rp q) (Sc q)) ∧
      (∀ m ∈ mesoIndexBox d (scaleOf q) (refinedStoppingScale q + 1)
          (refinedStoppingCenter q),
        ∀ v : H1Function (mesoCell d (scaleOf q) m),
        IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹
          (mesoCell d (scaleOf q) m) v (fun _ ↦ (0 : ℝ)) →
        CoarseEnergyBoundOn a (mesoCell d (scaleOf q) m)
          (mesoCore d (scaleOf q) m) v.toFun v.grad t (Gam0 q)) ∧
      81 * (P q * (Gam0 q * 27 ^ d + Sc q)) ^ 2 * Rp q ^ 2 *
        (Gam0 q * 27 ^ d + Sc q) * t ≤
          repairedStoppingContractionFactor d ^ 4) :
    ∀ r, (3 : ℝ) ^ Kbr * R ≤ r →
      ∫ x in (Metric.ball x0 r)ᶜ, u.toFun x ^ 2 ∂volume ≤
        C * Real.exp (-cst * r / R) * ∫ x, f x ^ 2 ∂volume :=
  wholeSpaceSolution_exterior_row_audited ht hacont hapos u hL2 hinitial hrepair
    (locallyFinite_refinedStoppingCell_enlargements hinitial hrepair) x0
    (refinedStoppingSource_nonempty hinitial hrepair x0 hR.le) hsupp hR heps
    hcst hC hgood scaleOf P Rp Sc Gam0 K chi hcell

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
