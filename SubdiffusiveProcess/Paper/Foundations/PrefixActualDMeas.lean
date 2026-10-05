module

public import SubdiffusiveProcess.Paper.Foundations.PrefixActualPrawMeas
public import SubdiffusiveProcess.Paper.Foundations.PrefixActualFMeas
public import SubdiffusiveProcess.Paper.Foundations.PrefixActualRMeas
public import SubdiffusiveProcess.Paper.Foundations.PrefixActualDBlockMeas

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal
open SubdiffusiveProcess.CoarseGrainingVocab _root_.SubdiffusiveProcess.Model
open Homogenization hiding Vec
open SubdiffusiveProcess

namespace SubdiffusiveProcess.Paper

def dscNormOn {d : ℕ} (W : Set (Vec d)) (f : Vec d → ℝ) : ENNReal :=
  sSup {v : ENNReal | ∃ x : Vec d, x ∈ W ∧ v = ENNReal.ofReal |f x|}

private theorem dsc_spatial_sup_meas {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {W : Set (Vec d)} (hWopen : IsOpen W)
    (F : Ω → Vec d → ENNReal)
    (hcont : ∀ omega, Continuous (F omega))
    (hmeas : ∀ x, Measurable (fun omega => F omega x)) :
    Measurable (fun omega => sSup {v : ENNReal | ∃ x ∈ W, v = F omega x}) := by exact _root_.SubdiffusiveProcess.Paper.aux_dedup_d107_spatialSup_meas (d := d) (Ω := Ω) (W := W) (hWopen := hWopen) (F := F) (hcont := hcont) (hmeas := hmeas)

theorem dsc_third_summand_meas {d : ℕ} (s : ℝ) (k : ℕ) (z : Vec d) :
    Measurable (fun omega : PotentialSample d =>
      ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) *
        dscNormOn (translatedCube d k z) (omega 0)) := by
  have hinner : Measurable (fun omega : PotentialSample d =>
      dscNormOn (translatedCube d k z) (omega 0)) := by
    have hcont : ∀ omega : PotentialSample d, Continuous (fun x : Vec d =>
        ENNReal.ofReal |omega 0 x|) := by
      intro omega
      exact ENNReal.continuous_ofReal.comp ((_root_.SubdiffusiveProcess.Model.PotentialField.contDiff_one (omega 0)).continuous.abs)
    have hmeas : ∀ x : Vec d, Measurable (fun omega : PotentialSample d =>
        ENNReal.ofReal |omega 0 x|) := by
      intro x
      exact ((continuous_abs.measurable.comp ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval x).comp
        (measurable_potentialCoordinate 0))).ennreal_ofReal)
    exact dsc_spatial_sup_meas
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.isOpen_translatedCube d k z)
      (fun (omega : PotentialSample d) (x : Vec d) => ENNReal.ofReal |omega 0 x|)
      hcont hmeas
  exact Measurable.const_mul hinner _

theorem dsc_fourth_summand_meas {d : ℕ} (k : ℕ) (z : Vec d) :
    Measurable (fun omega : PotentialSample d =>
      ∑' j : ℕ, if k ≤ j then
        ENNReal.ofReal ((3 : ℝ) ^ k) *
          dscNormOn (translatedCube d k z)
            (fun x : Vec d =>
              Homogenization.euclideanNorm (shellGradient (omega j) x))
        else 0) := by
  have hinner : ∀ j : ℕ, Measurable (fun omega : PotentialSample d =>
      dscNormOn (translatedCube d k z)
        (fun x : Vec d => Homogenization.euclideanNorm (shellGradient (omega j) x))) := by
    intro j
    have hcont : ∀ omega : PotentialSample d, Continuous (fun x : Vec d =>
        ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (omega j) x)|) := by
      intro omega
      exact ENNReal.continuous_ofReal.comp
        ((SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.continuous_euclideanNorm.comp
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.continuous_shellGradient
            (omega j))).abs)
    have hmeas : ∀ x : Vec d, Measurable (fun omega : PotentialSample d =>
        ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (omega j) x)|) := by
      intro x
      exact ((continuous_abs.measurable.comp
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.continuous_euclideanNorm.measurable.comp
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.measurable_shellGradient_eval x j)))).ennreal_ofReal
    exact dsc_spatial_sup_meas
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.isOpen_translatedCube d k z)
      (fun (omega : PotentialSample d) (x : Vec d) =>
        ENNReal.ofReal |Homogenization.euclideanNorm (shellGradient (omega j) x)|)
      hcont hmeas
  apply Measurable.tsum
  intro j
  split_ifs
  · exact Measurable.const_mul (hinner j) _
  · exact measurable_const

theorem dsc_full_meas {d : ℕ} [NeZero d]
    (M : GMCModel d) (s : ℝ) (k : ℕ) (z : Vec d) :
    Measurable (fun omega : PotentialSample d =>
      sSup {v : ENNReal | ∃ j l : ℕ, j ≤ k ∧ l ≤ k ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
        OnTriadicGrid l (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ)))) *
          (min (sSup {u : ENNReal | ∃ e : Vec d, vecNormSq e = 1 ∧
            u = ENNReal.ofReal (section6Response M l l omega x e)}) 1) ^ (1 / 2 : ℝ)} +
      sSup {v : ENNReal | ∃ j : ℕ, j ≤ k ∧
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
          dscNormOn (translatedCube d k z) (shellBlock k j omega)} +
      ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) *
        dscNormOn (translatedCube d k z) (omega 0) +
      ∑' j : ℕ, if k ≤ j then
        ENNReal.ofReal ((3 : ℝ) ^ k) *
          dscNormOn (translatedCube d k z)
            (fun x : Vec d =>
              Homogenization.euclideanNorm (shellGradient (omega j) x))
        else 0) := by
  exact (((aux_lem_prefix_limit_actual_Dsc_first_meas M s k z).add
    (aux_dsc_block_meas s k z)).add
    (dsc_third_summand_meas s k z)).add
    (dsc_fourth_summand_meas k z)

theorem dsc_raw_aemeas {d : ℕ} [NeZero d] {Ω : Type*}
    [MeasurableSpace Ω]
    (M : GMCModel d) (s eps : ℝ) (μ : Measure Ω)
    (eta : ℕ → Ω → PotentialSample d)
    (hEtaMeas : ∀ N, AEMeasurable (eta N) μ)
    (F Praw Rraw Draw : ℕ → ℕ → Vec d → Ω → ENNReal)
    (Z : ℕ → ℕ → Vec d → Ω → ℝ)
    (rawGood : ℕ → ℕ → Vec d → Ω → Prop)
    (hPrimitive : ∀ᵐ omega ∂μ, ∀ N,
      primitive_scores d M s eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => Praw N m y omega)
        (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
        (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    (N k : ℕ) (z : Vec d) :
    AEMeasurable (fun omega => (Draw N k z omega).toReal) μ := by
  have hcanonical : AEMeasurable
      (fun omega => (
        sSup {v : ENNReal | ∃ j l : ℕ, j ≤ k ∧ l ≤ k ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
          OnTriadicGrid l (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
          v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ)))) *
            (min (sSup {u : ENNReal | ∃ e : Vec d, vecNormSq e = 1 ∧
              u = ENNReal.ofReal (section6Response M l l (eta N omega) x e)}) 1) ^ (1 / 2 : ℝ)} +
        sSup {v : ENNReal | ∃ j : ℕ, j ≤ k ∧
          v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ)))) *
            dscNormOn (translatedCube d k z) (shellBlock k j (eta N omega))} +
        ENNReal.ofReal ((3 : ℝ) ^ (-(s / 8) * (k : ℝ))) *
          dscNormOn (translatedCube d k z) ((eta N omega) 0) +
        ∑' j : ℕ, if k ≤ j then
          ENNReal.ofReal ((3 : ℝ) ^ k) *
            dscNormOn (translatedCube d k z)
              (fun x : Vec d =>
                Homogenization.euclideanNorm (shellGradient ((eta N omega) j) x))
          else 0).toReal) μ := by
    exact (ENNReal.measurable_toReal.comp (dsc_full_meas M s k z)).comp_aemeasurable
      (hEtaMeas N)
  apply hcanonical.congr
  filter_upwards [hPrimitive] with omega hps
  obtain ⟨_, _, _, _, _, _, _, hD, _⟩ := hps N
  exact congrArg ENNReal.toReal (hD k z).symm





end SubdiffusiveProcess.Paper
