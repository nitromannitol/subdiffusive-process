module

public import SubdiffusiveProcess.Paper.primitive_scores
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.LiteralSupMeasurability

@[expose] public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open SubdiffusiveProcess.CoarseGrainingVocab _root_.SubdiffusiveProcess.Model
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology

namespace SubdiffusiveProcess.Paper

theorem aux_dedup_d107_spatialSup_meas {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {W : Set (Vec d)} (hWopen : IsOpen W)
    (F : Ω → Vec d → ENNReal)
    (hcont : ∀ omega, Continuous (F omega))
    (hmeas : ∀ x, Measurable (fun omega => F omega x)) :
    Measurable (fun omega => sSup {v : ENNReal | ∃ x ∈ W, v = F omega x}) := by
  obtain ⟨Q, hQcount, hQdense⟩ := TopologicalSpace.exists_countable_dense (Vec d)
  have : Countable ↥(W ∩ Q) :=
    (hQcount.mono Set.inter_subset_right).to_subtype
  have heq : ∀ omega,
      sSup {v : ENNReal | ∃ x ∈ W, v = F omega x} =
        ⨆ x : ↥(W ∩ Q), F omega x := by
    intro omega
    apply le_antisymm
    · refine sSup_le ?_
      rintro v ⟨x, hx, rfl⟩
      let c : ENNReal := ⨆ y : ↥(W ∩ Q), F omega y
      have hc : IsClosed {y : Vec d | F omega y ≤ c} :=
        isClosed_le (hcont omega) continuous_const
      have hsub : W ∩ Q ⊆ {y : Vec d | F omega y ≤ c} := by
        intro y hy
        exact le_iSup (fun y : ↥(W ∩ Q) => F omega y) ⟨y, hy⟩
      have hdense : W ⊆ closure (W ∩ Q) :=
        hQdense.open_subset_closure_inter hWopen
      exact hc.closure_subset_iff.mpr hsub (hdense hx)
    · refine iSup_le fun y => ?_
      exact le_sSup ⟨y.1, y.2.1, rfl⟩
  simp_rw [heq]
  exact Measurable.iSup (fun y => hmeas y)

private theorem spatialSup_meas {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {W : Set (Vec d)} (hWopen : IsOpen W)
    (F : Ω → Vec d → ENNReal)
    (hcont : ∀ omega, Continuous (F omega))
    (hmeas : ∀ x, Measurable (fun omega => F omega x)) :
    Measurable (fun omega => sSup {v : ENNReal | ∃ x ∈ W, v = F omega x}) := by exact _root_.SubdiffusiveProcess.Paper.aux_dedup_d107_spatialSup_meas (d := d) (Ω := Ω) (W := W) (hWopen := hWopen) (F := F) (hcont := hcont) (hmeas := hmeas)

private def A {d : ℕ} (m j : ℕ) (omega : PotentialSample d) (x : Vec d) : ENNReal :=
  ∏ i ∈ Finset.Icc (m - j) (m + j), ENNReal.ofReal (Real.exp |omega i x|)

private def B {d : ℕ} (m j K : ℕ) (z : Vec d)
    (omega : PotentialSample d) (x : Vec d) : ENNReal :=
  ∏ i ∈ Finset.Icc (m + j) (m + j + K),
    ENNReal.ofReal (Real.exp (4 * |omega i x - omega i z|))

private theorem A_cont {d : ℕ} (m j : ℕ) (omega : PotentialSample d) :
    Continuous (A m j omega) := by
  unfold A
  have hEq : (fun x : Vec d =>
      ∏ i ∈ Finset.Icc (m - j) (m + j),
        ENNReal.ofReal (Real.exp |omega i x|)) =
      (fun x : Vec d => ENNReal.ofReal
        (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i x|)) := by
    funext x
    exact (ENNReal.ofReal_prod_of_nonneg (fun i hi => Real.exp_nonneg _)).symm
  rw [hEq]
  exact ENNReal.continuous_ofReal.comp
    (continuous_finsetProd _ fun i _ =>
      Real.continuous_exp.comp ((_root_.SubdiffusiveProcess.Model.PotentialField.contDiff_one (omega i)).continuous.abs))

private theorem B_cont {d : ℕ} (m j K : ℕ) (z : Vec d)
    (omega : PotentialSample d) : Continuous (B m j K z omega) := by
  unfold B
  have hEq : (fun x : Vec d =>
      ∏ i ∈ Finset.Icc (m + j) (m + j + K),
        ENNReal.ofReal (Real.exp (4 * |omega i x - omega i z|))) =
      (fun x : Vec d => ENNReal.ofReal
        (∏ i ∈ Finset.Icc (m + j) (m + j + K),
          Real.exp (4 * |omega i x - omega i z|))) := by
    funext x
    exact (ENNReal.ofReal_prod_of_nonneg (fun i hi => Real.exp_nonneg _)).symm
  rw [hEq]
  exact ENNReal.continuous_ofReal.comp
    (continuous_finsetProd _ fun i _ =>
      Real.continuous_exp.comp
        (continuous_const.mul
          (((_root_.SubdiffusiveProcess.Model.PotentialField.contDiff_one (omega i)).continuous).sub continuous_const).abs))

private theorem A_meas {d : ℕ} (m j : ℕ) (x : Vec d) :
    Measurable (fun omega : PotentialSample d => A m j omega x) := by
  unfold A
  exact Finset.measurable_prod _ fun i _ =>
    (Real.measurable_exp.comp
      (continuous_abs.measurable.comp
        ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval x).comp
          (measurable_potentialCoordinate i)))).ennreal_ofReal

private theorem B_meas {d : ℕ} (m j K : ℕ) (z x : Vec d) :
    Measurable (fun omega : PotentialSample d => B m j K z omega x) := by
  unfold B
  exact Finset.measurable_prod _ fun i _ =>
    (Real.measurable_exp.comp
      (measurable_const.mul
        (continuous_abs.measurable.comp
          (((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval x).comp
            (measurable_potentialCoordinate i)).sub
            ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval z).comp
              (measurable_potentialCoordinate i)))))).ennreal_ofReal

private theorem Pinner_meas {d : ℕ} (m j : ℕ) (z : Vec d) :
    Measurable (fun omega : PotentialSample d =>
      sSup {w : ENNReal | ∃ x ∈ translatedCube d (m + 1 + j) z,
        w = A m j omega x +
          sSup {u : ENNReal | ∃ K : ℕ, u = B m j K z omega x}}) := by
  let W := translatedCube d (m + 1 + j) z
  have hterm (K : ℕ) : Measurable (fun omega : PotentialSample d =>
      sSup {w : ENNReal | ∃ x ∈ W,
        w = A m j omega x + B m j K z omega x}) := by
    exact spatialSup_meas
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.isOpen_translatedCube d _ z)
      (fun omega x => A m j omega x + B m j K z omega x)
      (fun omega => (A_cont m j omega).add (B_cont m j K z omega))
      (fun x => (A_meas m j x).add (B_meas m j K z x))
  have heq (omega : PotentialSample d) :
      sSup {w : ENNReal | ∃ x ∈ W,
        w = A m j omega x +
          sSup {u : ENNReal | ∃ K : ℕ, u = B m j K z omega x}} =
      ⨆ K : ℕ, sSup {w : ENNReal | ∃ x ∈ W,
        w = A m j omega x + B m j K z omega x} := by
    have htail (x : Vec d) :
        sSup {u : ENNReal | ∃ K : ℕ, u = B m j K z omega x} =
          ⨆ K : ℕ, B m j K z omega x := by
      apply le_antisymm
      · refine sSup_le ?_
        rintro u ⟨K, rfl⟩
        exact le_iSup (fun K => B m j K z omega x) K
      · refine iSup_le fun K => ?_
        exact le_sSup ⟨K, rfl⟩
    apply le_antisymm
    · refine sSup_le ?_
      rintro w ⟨x, hx, rfl⟩
      rw [htail x, ENNReal.add_iSup]
      refine iSup_le fun K => ?_
      exact (show A m j omega x + B m j K z omega x ≤
          sSup {w : ENNReal | ∃ x ∈ W,
            w = A m j omega x + B m j K z omega x} from
            le_sSup ⟨x, hx, rfl⟩).trans
        (le_iSup (fun K => sSup {w : ENNReal | ∃ x ∈ W,
          w = A m j omega x + B m j K z omega x}) K)
    · refine iSup_le fun K => sSup_le ?_
      rintro w ⟨x, hx, rfl⟩
      exact (add_le_add_right (show B m j K z omega x ≤
          sSup {u : ENNReal | ∃ K : ℕ, u = B m j K z omega x} from
          le_sSup ⟨K, rfl⟩) _).trans
        (show A m j omega x +
          sSup {u : ENNReal | ∃ K : ℕ, u = B m j K z omega x} ≤
          sSup {w : ENNReal | ∃ x ∈ W,
            w = A m j omega x +
              sSup {u : ENNReal | ∃ K : ℕ, u = B m j K z omega x}} from
          le_sSup ⟨x, hx, rfl⟩)
  have hsup : Measurable (fun omega : PotentialSample d =>
      ⨆ K : ℕ, sSup {w : ENNReal | ∃ x ∈ W,
        w = A m j omega x + B m j K z omega x}) := Measurable.iSup hterm
  convert hsup using 1
  funext omega
  exact heq omega


theorem aux_lem_prefix_limit_actual_Psc_meas {d : ℕ} (s : ℝ) (m : ℕ) (z : Vec d) :
    Measurable (fun omega : PotentialSample d =>
      sSup {v : ENNReal | ∃ j : ℕ,
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
          sSup {w : ENNReal | ∃ x ∈ translatedCube d (m + 1 + j) z,
            w = (∏ i ∈ Finset.Icc (m - j) (m + j),
                    ENNReal.ofReal (Real.exp |omega i x|)) +
              sSup {u : ENNReal | ∃ K : ℕ,
                u = ∏ i ∈ Finset.Icc (m + j) (m + j + K),
                    ENNReal.ofReal (Real.exp (4 * |omega i x - omega i z|))}}}) := by
  have hterm (j : ℕ) : Measurable (fun omega : PotentialSample d =>
      ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
        sSup {w : ENNReal | ∃ x ∈ translatedCube d (m + 1 + j) z,
          w = A m j omega x +
            sSup {u : ENNReal | ∃ K : ℕ, u = B m j K z omega x}}) := by
    exact (Pinner_meas m j z).const_mul _
  have heq (omega : PotentialSample d) :
      sSup {v : ENNReal | ∃ j : ℕ,
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
          sSup {w : ENNReal | ∃ x ∈ translatedCube d (m + 1 + j) z,
            w = A m j omega x +
              sSup {u : ENNReal | ∃ K : ℕ, u = B m j K z omega x}}} =
      ⨆ j : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
        sSup {w : ENNReal | ∃ x ∈ translatedCube d (m + 1 + j) z,
          w = A m j omega x +
            sSup {u : ENNReal | ∃ K : ℕ, u = B m j K z omega x}} := by
    apply le_antisymm
    · refine sSup_le ?_
      rintro v ⟨j, rfl⟩
      exact le_iSup (fun j : ℕ =>
        ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
          sSup {w : ENNReal | ∃ x ∈ translatedCube d (m + 1 + j) z,
            w = A m j omega x +
              sSup {u : ENNReal | ∃ K : ℕ, u = B m j K z omega x}}) j
    · refine iSup_le fun j => ?_
      exact le_sSup ⟨j, rfl⟩
  have hsup : Measurable (fun omega : PotentialSample d =>
      ⨆ j : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
        sSup {w : ENNReal | ∃ x ∈ translatedCube d (m + 1 + j) z,
          w = A m j omega x +
            sSup {u : ENNReal | ∃ K : ℕ, u = B m j K z omega x}}) :=
    Measurable.iSup hterm
  convert hsup using 1
  funext omega
  exact heq omega


theorem aux_lem_prefix_limit_actual_Praw_raw_aemeas {d : ℕ} [NeZero d] {Ω : Type*}
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
    AEMeasurable (fun omega => (Praw N m z omega).toReal) μ := by
  have hcanonical : AEMeasurable
      (fun omega => (sSup {v : ENNReal | ∃ j : ℕ,
        v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
          sSup {w : ENNReal | ∃ x ∈ translatedCube d (m + 1 + j) z,
            w = (∏ i ∈ Finset.Icc (m - j) (m + j),
                    ENNReal.ofReal (Real.exp |(eta N omega) i x|)) +
              sSup {u : ENNReal | ∃ K : ℕ,
                u = ∏ i ∈ Finset.Icc (m + j) (m + j + K),
                    ENNReal.ofReal
                      (Real.exp (4 * |(eta N omega) i x - (eta N omega) i z|))}}}).toReal) μ := by
    exact (ENNReal.measurable_toReal.comp (aux_lem_prefix_limit_actual_Psc_meas s m z)).comp_aemeasurable
      (hEtaMeas N)
  apply hcanonical.congr
  filter_upwards [hPrimitive] with omega hps
  have hprim := hps N
  rw [_root_.SubdiffusiveProcess.Paper.primitive_scores] at hprim
  obtain ⟨_, _, _, _, _, hP, _, _, _, _, _⟩ := hprim
  exact congrArg ENNReal.toReal (hP m z).symm


end SubdiffusiveProcess.Paper
