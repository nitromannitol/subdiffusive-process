import SubdiffusiveProcess.Paper.inputs_baseline_native
import SubdiffusiveProcess.Paper.sum_errors_baseline_input
import SubdiffusiveProcess.Paper.Foundations.PrefixFieldTransport

open MeasureTheory
open SubdiffusiveProcess
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- The original coupled-field baseline, with CD(q) and deltaD(q) before M. -/
theorem inputs_baseline_witness (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] : sum_errors_baseline_input d := by
  classical
  intro s eps hs _heps
  have banks := fun q : ℝ => inputs_baseline_native d hd s (max 1 q) hs (le_max_left 1 q)
  choose C delta0 hC hdelta0 hbank using banks
  refine ⟨C, delta0, fun q _ => ⟨hC q, hdelta0 q⟩, ?_⟩
  intro q hq M hsmall eta hEta F Praw Rraw Draw Z rawGood hprim N k z
  obtain ⟨_hfinite, hmem, hnorm⟩ := hbank q M hsmall k z
  rw [max_eq_right hq] at hmem hnorm
  let score : PotentialSample d → ENNReal := fun omega =>
    (sSup {v : ENNReal | ∃ j l : ℕ, j ≤ k ∧ l ≤ k ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
          OnTriadicGrid l (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
          v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ)))) *
            (min (sSup {u : ENNReal | ∃ e : Vec d, Homogenization.vecNormSq e = 1 ∧
              u = ENNReal.ofReal (section6Response M l l omega x e)}) 1) ^ (1 / 2 : ℝ)}) +
            (sSup {v : ENNReal | ∃ j : ℕ, j ≤ k ∧
          v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
            sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
              u = ENNReal.ofReal |shellBlock k j omega x|}}) +
            (ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) *
          sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
            u = ENNReal.ofReal |omega 0 x|}) +
            (∑' j : ℕ, if k ≤ j then ENNReal.ofReal ((3 : ℝ) ^ k) *
          sSup {u : ENNReal | ∃ x : Vec d, x ∈ translatedCube d k z ∧
            u = ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (omega j) x)|}
          else 0)
  let f : PotentialSample d → ℝ := fun omega => (score omega).toReal
  change MemLp f (ENNReal.ofReal q) M.P.toMeasure at hmem
  change eLpNorm f (ENNReal.ofReal q) M.P.toMeasure ≤
    ENNReal.ofReal (C q * M.delta ^ (1 / 2 : ℝ)) at hnorm
  have hmeasEta := prefix_eta_aemeasurable M eta hEta N
  have hlaw := prefix_eta_law M eta hEta N
  have hraw : (fun omega => (Draw N k z omega).toReal) =ᵐ[(chaosSampleLaw M).toMeasure]
      (f ∘ eta N) := by
    filter_upwards [hprim] with omega hprim
    obtain ⟨_, _, _, _, _, _, _, hD, _⟩ := hprim N
    exact congrArg ENNReal.toReal (hD k z)
  have hmemMap : MemLp f (ENNReal.ofReal q)
      (Measure.map (eta N) (chaosSampleLaw M).toMeasure) := by
    rw [hlaw]
    exact hmem
  have hcomp := hmemMap.comp_of_map hmeasEta
  refine ⟨(memLp_congr_ae hraw).2 hcomp, ?_⟩
  have hnormMap := eLpNorm_map_measure (p := ENNReal.ofReal q)
    hmemMap.aestronglyMeasurable hmeasEta
  rw [hlaw] at hnormMap
  exact ((eLpNorm_congr_ae hraw).trans hnormMap.symm).le.trans hnorm

end Paper
