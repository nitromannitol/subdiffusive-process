
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsExteriorRow
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsPriceUniform
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionCrossingBracket

@[expose] public section

/-!
# The exterior row of `WholeSpaceRows`, from the mesoscopic per-cell data

This is the end-to-end composition of the package:

* the cross-term integrability is **gone** — it is proved from the ellipticity
  and the carrier's own `L²` and energy data
  (`WholeSpaceRowsCrossIntegrability.lean`);
* the two mesoscopic legs are assumed in the form the analytic theorems produce
  them, i.e. **for every local `H¹` solution on the cell**, and are transported
  onto the carrier's fields by `WholeSpaceRowsCarrierLegs.lean`;
* the resulting per-cell contraction feeds the repaired stopping partition, and
  `WholeSpaceRowsExteriorRow.lean` converts its discrete-radius conclusion into
  the exterior conjunct of `WholeSpaceRows`.

Nothing is scale-uniform: the mesoscopic scale, the cutoff, the ellipticity
constants and the price constants may all depend on the stopping cell.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization Homogenization.Book Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Section8

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}



theorem wholeSpaceSolution_exterior_row_of_coarse_mesoscopic_cells
    [NeZero d] {Omega : Type*} {base : ℤ} {failure : TriadicCube d → Set Omega}
    {omega : Omega} {a f : Vec d → ℝ} {t : ℝ} (ht : 0 < t)
    (haNonneg : ∀ x, 0 ≤ a x)
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
    (lam Lam P Rp Sc Gam0 K : RefinedStoppingCell failure omega base → ℝ)
    (chi : RefinedStoppingCell failure omega base → Vec d → ℝ)
    (hcell : ∀ q,
      0 < stoppingGraphDistance repairedStoppingGraph source hsourceNonempty q →
      scaleOf q ≤ refinedStoppingScale q - 3 ∧
      IsEllipticFieldOn (lam q) (Lam q)
        (translatedCube d (refinedStoppingScale q + 1)
          (refinedStoppingCenter q)) (scalarCoeffField a) ∧
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
  refine wholeSpaceSolution_exterior_row_of_repaired_stopping_cells_of_bracket
    u hL2 hinitial hrepair source hsourceNonempty x0 hR heps hcst hC hgood ?_
  intro q hq
  obtain ⟨hkn, hEll, hP, hGam0, hRp, hSc, hbeta1, hf0, hchi, hchiC, hchiBox,
    hchi_le, hchi_one, hK, hpricelocal, henergylocal, hsmall⟩ := hcell q hq
  have hcrossInt := integrableOn_cross_wholeSpaceSolution_translatedCube
    (n := refinedStoppingScale q) (c := refinedStoppingCenter q)
    hEll haNonneg hchi hchi_le hK u
  have hpricecell := mesoscopicCrossPriceEnergyOn_priceIndexBox_wholeSpaceSolution
    hkn u hf0 hpricelocal
  have henergycell := coarseEnergyBoundOn_mesoIndexBox_wholeSpaceSolution
    (k := scaleOf q) u hf0 henergylocal
  exact wholeSpaceSolution_translatedCube_coarse_mass_contraction_of_cells
    hkn hEll haNonneg ht repairedStoppingContractionFactor_pos hP hGam0 hRp hSc
    hbeta1 u hf0 hchi hchiC hchiBox hchi_le hchi_one hK hcrossInt hpricecell
    henergycell hsmall

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
