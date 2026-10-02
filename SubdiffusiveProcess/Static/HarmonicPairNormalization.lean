import SubdiffusiveProcess.Static.CutoffHarmonicCellCarrier
import SubdiffusiveProcess.Static.LocalEstimateClauses
import SubdiffusiveProcess.Frozen.Vocab.Ahom
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
import SubdiffusiveProcess.Static.HarmonicPairMomentCutoff
import SubdiffusiveProcess.Static.HarmonicPairDyadicAssembly

/-! # Uniform harmonic cutoff estimates from own-scale cell growth -/
open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

theorem exists_uniform_local_harmonic_prefix_of_cell_growth (d p : ℕ)
    (c : Fin p → Vec d) (s0 s1 : Fin p → ℝ)
    (hs : ∀ i, 0 < s0 i ∧ s0 i < s1 i)
    (hcell : ∀ q : ℝ, 1 ≤ q →
      ∃ delta0 : ℝ, 0 < delta0 ∧
        ∀ M : GMCModel d, M.delta ≤ delta0 →
          ∃ C : ℝ, 0 < C ∧
            ∀ (j : ℕ) (k : ℤ), j ≤ k.toNat → ∀ z : Vec d,
              ∃ K : PotentialSample d → ℝ, Measurable K ∧ (∀ omega, 1 ≤ K omega) ∧
                eLpNorm K (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal C ∧
                ∀ᵐ omega ∂M.P.toMeasure,
                  CutoffHarmonicCellGrowth M j k z omega (K omega)) :
    ∀ q : ℝ, 1 ≤ q →
      ∃ delta0 : ℝ, 0 < delta0 ∧
        ∀ M : GMCModel d, M.delta ≤ delta0 →
          ∃ C : ℝ, 0 < C ∧
            ∀ (j m : ℕ), j ≤ m → ∀ z : Vec d,
              ∃ K : PotentialSample d → ℝ, Measurable K ∧ (∀ omega, 1 ≤ K omega) ∧
                (∫⁻ omega, ENNReal.ofReal (K omega ^ q) ∂M.P.toMeasure) ≤
                  ENNReal.ofReal C ∧
                ∀ᵐ omega ∂M.P.toMeasure,
                  localHarmonicCutoffEstimates
                    (fun x => (ahom M j)⁻¹ * aCutoff M j omega
                      (z + (3 : ℝ) ^ m • x)) c s0 s1 (K omega) 5 := by
  classical
  intro q hq
  let R := max q (2 * (d : ℝ))
  have hqR : q ≤ R := le_max_left _ _
  have hR : 1 ≤ R := hq.trans hqR
  have hdR : 2 * (d : ℝ) ≤ R := le_max_right _ _
  have h2R : 1 ≤ 2 * R := by linarith
  obtain ⟨deltaCell, hdeltaCell, hcells⟩ := hcell (2 * R) h2R
  obtain ⟨deltaBlock, Cblock, hdeltaBlock, hCblock, hblocks⟩ :=
    exists_cutoffBlockFactor_moment_bound d (2 * R) (1 / 4) h2R (by norm_num)
  obtain ⟨deltaRatio, hdeltaRatio, hratios⟩ :=
    exists_pair_ahom_ratio_bound d (eta := 1 / 4) (by norm_num)
  obtain ⟨C0, hC0, hsmooth⟩ := exists_smooth_cube_cutoff d
  let rho := 1 + ∑ i : Fin p, |s1 i|
  have hrho : 0 ≤ rho := by dsimp only [rho]; positivity
  have houter : ∀ i, s1 i / 2 ≤ rho := by
    intro i
    have hi : |s1 i| ≤ ∑ a : Fin p, |s1 a| :=
      Finset.single_le_sum (fun a _ => abs_nonneg (s1 a)) (Finset.mem_univ i)
    have hs1 : 0 < s1 i := (hs i).1.trans (hs i).2
    have hi' := (le_abs_self (s1 i)).trans hi
    dsimp only [rho]
    linarith
  refine ⟨min deltaCell (min deltaBlock deltaRatio),
    lt_min hdeltaCell (lt_min hdeltaBlock hdeltaRatio), ?_⟩
  intro M hM
  have hMcell : M.delta ≤ deltaCell := hM.trans (min_le_left _ _)
  have hMblock : M.delta ≤ deltaBlock :=
    hM.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hMratio : M.delta ≤ deltaRatio :=
    hM.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Ccell, hCcell, hcellsM⟩ := hcells M hMcell
  let B := (8 : ℝ) ^ d * (1 + C0) ^ 2 * (3 * rho + 15) ^ 3 *
    (2 * (rho + 1)) ^ d * Cblock * Ccell
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let C := (1 + ∑ i : Fin p, ((s1 i - s0 i) / 2) ^ 2) ^ q *
    (1 + 4 * (p : ℝ) * B) ^ q
  have hC : 0 < C := by
    dsimp only [C]
    apply mul_pos <;> apply Real.rpow_pos_of_pos <;> positivity
  refine ⟨C, hC, ?_⟩
  intro j m hjm z
  apply exists_dyadic_harmonic_cutoffs_of_uniform_pairs M.P.toMeasure
    (fun omega x => (ahom M j)⁻¹ * aCutoff M j omega (z + (3 : ℝ) ^ m • x))
    c s0 s1 hs hq hB houter
  intro i R1 R2 hR1 hR12 hR2
  exact exists_pair_moment_cutoff M hq hqR hdR hCcell.le hCblock.le hrho hC0
    hcellsM (hblocks M hMblock) (hratios M hMratio) hsmooth j m hjm z
    (c i) R1 R2 hR1 hR12 hR2

end SubdiffusiveProcess.Static
