import SubdiffusiveProcess.Paper.Foundations.PrefixActualFMeas
import SubdiffusiveProcess.Paper.Foundations.PrefixActualPrawMeas
import SubdiffusiveProcess.Paper.Foundations.PrefixActualRMeas

noncomputable section

open MeasureTheory SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

namespace Paper

private theorem eramp_meas {α : Type*} [MeasurableSpace α]
    (a b : ℝ) {X : α → ENNReal} (hX : Measurable X) :
    Measurable (fun x =>
      (min (1 : ENNReal) ((X x - ENNReal.ofReal a) /
        ENNReal.ofReal (b - a))).toReal) := by
  exact ENNReal.measurable_toReal.comp
    (measurable_const.min ((hX.sub measurable_const).div measurable_const))


private def Fcanon {d : ℕ} (s : ℝ) (m : ℕ) (z : Vec d)
    (omega : PotentialSample d) : ENNReal :=
  sSup {v : ENNReal | ∃ j : ℕ,
    v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
      ∑ i ∈ Finset.Icc (m - j) (m + j),
        sSup {w : ENNReal | ∃ x : Vec d,
          x ∈ translatedCube d (m + 1 + j) z ∧
          w = ENNReal.ofReal |(|omega i x| + (3 : ℝ) ^ (i : ℝ) *
            Homogenization.euclideanNorm (shellGradient (omega i) x))|}}

private def Pcanon {d : ℕ} (s : ℝ) (m : ℕ) (z : Vec d)
    (omega : PotentialSample d) : ENNReal :=
  sSup {v : ENNReal | ∃ j : ℕ,
    v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
      sSup {w : ENNReal | ∃ x ∈ translatedCube d (m + 1 + j) z,
        w = (∏ i ∈ Finset.Icc (m - j) (m + j),
          ENNReal.ofReal (Real.exp |omega i x|)) +
          sSup {u : ENNReal | ∃ K : ℕ,
            u = ∏ i ∈ Finset.Icc (m + j) (m + j + K),
              ENNReal.ofReal (Real.exp (4 * |omega i x - omega i z|))}}}

private def Rcanon {d : ℕ} [NeZero d] (M : GMCModel d) (s : ℝ)
    (m : ℕ) (z : Vec d) (omega : PotentialSample d) : ENNReal :=
  sSup {v : ENNReal | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧ ∃ x : Vec d,
    OnTriadicGrid n (x - z) ∧ x - z ∈ cube d j \ cube d (j - 1) ∧
    v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * ((m : ℝ) - (n : ℝ)) / 8))) *
      sSup {u : ENNReal | ∃ e : Vec d, vecNormSq e = 1 ∧
        u = ENNReal.ofReal (section6Response M n n omega x e)}}

theorem literal_bad_score_meas {d : ℕ} [NeZero d]
    (M : GMCModel d) (s eps : ℝ) (m : ℕ) (z : Vec d) :
    Measurable (fun omega : PotentialSample d =>
      (min (1 : ENNReal) ((Fcanon s m z omega - ENNReal.ofReal (eps / 2)) /
        ENNReal.ofReal (eps - eps / 2))).toReal +
      (min (1 : ENNReal) ((Pcanon s m z omega - ENNReal.ofReal 6) /
        ENNReal.ofReal ((12 : ℝ) - 6))).toReal +
      (min (1 : ENNReal) ((Rcanon M s m z omega - ENNReal.ofReal (eps ^ 2 / 4)) /
        ENNReal.ofReal (eps ^ 2 - eps ^ 2 / 4))).toReal) := by
  have hF : Measurable (Fcanon s m z) := by
    exact aux_lem_prefix_limit_actual_Fsc_meas s m z
  have hP : Measurable (Pcanon s m z) := by
    exact aux_lem_prefix_limit_actual_Psc_meas s m z
  have hR : Measurable (Rcanon M s m z) := by
    exact aux_lem_prefix_limit_actual_Rsc_meas M s m z
  exact ((eramp_meas (eps / 2) eps hF).add (eramp_meas 6 12 hP)).add
    (eramp_meas (eps ^ 2 / 4) (eps ^ 2) hR)


theorem actual_Z_aemeas {d : ℕ} [NeZero d] {Ω : Type*}
    [MeasurableSpace Ω] (M : GMCModel d) (s eps : ℝ) (μ : Measure Ω)
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
    AEMeasurable (fun omega => Z N m z omega) μ := by
  have hcanonical : AEMeasurable (fun omega : Ω =>
      (min (1 : ENNReal) ((Fcanon s m z (eta N omega) - ENNReal.ofReal (eps / 2)) /
        ENNReal.ofReal (eps - eps / 2))).toReal +
      (min (1 : ENNReal) ((Pcanon s m z (eta N omega) - ENNReal.ofReal 6) /
        ENNReal.ofReal ((12 : ℝ) - 6))).toReal +
      (min (1 : ENNReal) ((Rcanon M s m z (eta N omega) - ENNReal.ofReal (eps ^ 2 / 4)) /
        ENNReal.ofReal (eps ^ 2 - eps ^ 2 / 4))).toReal) μ :=
    (literal_bad_score_meas M s eps m z).comp_aemeasurable (hEtaMeas N)
  apply hcanonical.congr
  filter_upwards [hPrimitive] with omega hps
  have hprim := hps N
  rw [Paper.primitive_scores] at hprim
  obtain ⟨_, _, _, _, hF, hP, hR, _, _, hZ, _⟩ := hprim
  have hFeq : F N m z omega = Fcanon s m z (eta N omega) := hF m z
  have hPeq : Praw N m z omega = Pcanon s m z (eta N omega) := hP m z
  have hReq : Rraw N m z omega = Rcanon M s m z (eta N omega) := hR m z
  have hZeq := (hZ m z).1
  dsimp only at hZeq
  rw [hFeq, hPeq, hReq] at hZeq
  exact hZeq.symm


end Paper
