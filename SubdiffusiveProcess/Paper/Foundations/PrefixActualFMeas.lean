module

public import SubdiffusiveProcess.Paper.Foundations.PrefixActualPrawMeas
public import SubdiffusiveProcess.Paper.primitive_scores_finite
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.LiteralSupMeasurability

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology
open SubdiffusiveProcess.CoarseGrainingVocab _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess

namespace SubdiffusiveProcess.Paper

private theorem prefixF_spatial_sup_meas {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {W : Set (Vec d)} (hWopen : IsOpen W)
    (F : Ω → Vec d → ENNReal)
    (hcont : ∀ omega, Continuous (F omega))
    (hmeas : ∀ x, Measurable (fun omega => F omega x)) :
    Measurable (fun omega => sSup {v : ENNReal | ∃ x ∈ W, v = F omega x}) := by exact _root_.SubdiffusiveProcess.Paper.aux_dedup_d107_spatialSup_meas (d := d) (Ω := Ω) (W := W) (hWopen := hWopen) (F := F) (hcont := hcont) (hmeas := hmeas)

private theorem prefixF_inner_meas {d : ℕ} (i : ℕ) (n : ℤ) (z : Vec d) :
    Measurable (fun omega : PotentialSample d =>
      sSup {w : ENNReal | ∃ x ∈ translatedCube d n z,
        w = ENNReal.ofReal |(|omega i x| + (3 : ℝ) ^ (i : ℝ) *
          Homogenization.euclideanNorm (shellGradient (omega i) x))|}) := by
  have hcont : ∀ omega : PotentialSample d, Continuous (fun x : Vec d =>
      ENNReal.ofReal |(|omega i x| + (3 : ℝ) ^ (i : ℝ) *
        Homogenization.euclideanNorm (shellGradient (omega i) x))|) := by
    intro omega
    exact ENNReal.continuous_ofReal.comp
      (((_root_.SubdiffusiveProcess.Model.PotentialField.contDiff_one (omega i)).continuous.abs.add
        (continuous_const.mul
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.continuous_euclideanNorm.comp
            (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.continuous_shellGradient
              (omega i))))).abs)
  have hmeas : ∀ x : Vec d, Measurable (fun omega : PotentialSample d =>
      ENNReal.ofReal |(|omega i x| + (3 : ℝ) ^ (i : ℝ) *
        Homogenization.euclideanNorm (shellGradient (omega i) x))|) := by
    intro x
    exact (continuous_abs.measurable.comp
      ((continuous_abs.measurable.comp ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval x).comp
      (measurable_potentialCoordinate i))).add
        (measurable_const.mul
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.continuous_euclideanNorm.measurable.comp
            (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.measurable_shellGradient_eval x i))))).ennreal_ofReal
  have h := prefixF_spatial_sup_meas
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.isOpen_translatedCube d n z)
    (fun (omega : PotentialSample d) x => ENNReal.ofReal |(|omega i x| + (3 : ℝ) ^ (i : ℝ) *
      Homogenization.euclideanNorm (shellGradient (omega i) x))|)
    hcont hmeas
  convert h using 1

def prefixF_normOn {d : ℕ} (W : Set (Vec d)) (f : Vec d → ℝ) : ENNReal :=
  sSup {v : ENNReal | ∃ x : Vec d, x ∈ W ∧ v = ENNReal.ofReal |f x|}

theorem aux_lem_prefix_limit_actual_Fsc_meas {d : ℕ} (s : ℝ) (m : ℕ) (z : Vec d) :
    Measurable (fun omega : PotentialSample d =>
      sSup {v : ENNReal | ∃ j : ℕ,
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
          ∑ i ∈ Finset.Icc (m - j) (m + j),
            prefixF_normOn (translatedCube d (m + 1 + j) z)
              (fun x : Vec d => |omega i x| + (3 : ℝ) ^ (i : ℝ) *
                Homogenization.euclideanNorm (shellGradient (omega i) x))}) := by
  have hterm : ∀ j : ℕ, Measurable (fun omega : PotentialSample d =>
      ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
        ∑ i ∈ Finset.Icc (m - j) (m + j),
          prefixF_normOn (translatedCube d (m + 1 + j) z)
            (fun x : Vec d => |omega i x| + (3 : ℝ) ^ (i : ℝ) *
              Homogenization.euclideanNorm (shellGradient (omega i) x))) := by
    intro j
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i _
    change Measurable (fun omega : PotentialSample d =>
      sSup {w : ENNReal | ∃ x ∈ translatedCube d (m + 1 + j) z,
        w = ENNReal.ofReal |(|omega i x| + (3 : ℝ) ^ (i : ℝ) *
          Homogenization.euclideanNorm (shellGradient (omega i) x))|})
    exact prefixF_inner_meas i (m + 1 + j) z
  have heq : (fun omega : PotentialSample d =>
      sSup {v : ENNReal | ∃ j : ℕ,
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
          ∑ i ∈ Finset.Icc (m - j) (m + j),
            prefixF_normOn (translatedCube d (m + 1 + j) z)
              (fun x : Vec d => |omega i x| + (3 : ℝ) ^ (i : ℝ) *
                Homogenization.euclideanNorm (shellGradient (omega i) x))}) =
      (fun omega => ⨆ j : ℕ,
        ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
          ∑ i ∈ Finset.Icc (m - j) (m + j),
            prefixF_normOn (translatedCube d (m + 1 + j) z)
              (fun x : Vec d => |omega i x| + (3 : ℝ) ^ (i : ℝ) *
                Homogenization.euclideanNorm (shellGradient (omega i) x))) := by
    funext omega
    change sSup {v : ENNReal | ∃ j : ℕ, v = _} = sSup (Set.range fun j : ℕ => _)
    congr 1
    ext v
    simp [eq_comm]
  rw [heq]
  exact Measurable.iSup hterm

theorem aux_lem_prefix_limit_actual_Fsc_raw_aemeas {d : ℕ} [NeZero d] {Ω : Type*}
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
    (N m : ℕ) (z : Vec d) :
    AEMeasurable (fun omega => (F N m z omega).toReal) μ := by
  have hcanonical : AEMeasurable
      (fun omega => (sSup {v : ENNReal | ∃ j : ℕ,
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
          ∑ i ∈ Finset.Icc (m - j) (m + j),
            prefixF_normOn (translatedCube d (m + 1 + j) z)
              (fun x : Vec d => |(eta N omega) i x| + (3 : ℝ) ^ (i : ℝ) *
                Homogenization.euclideanNorm (shellGradient ((eta N omega) i) x))}).toReal) μ := by
    exact (ENNReal.measurable_toReal.comp (aux_lem_prefix_limit_actual_Fsc_meas s m z)).comp_aemeasurable
      (hEtaMeas N)
  apply hcanonical.congr
  filter_upwards [hPrimitive] with omega hps
  obtain ⟨_, _, _, _, hF, _⟩ := hps N
  exact congrArg ENNReal.toReal (hF m z).symm



end SubdiffusiveProcess.Paper
