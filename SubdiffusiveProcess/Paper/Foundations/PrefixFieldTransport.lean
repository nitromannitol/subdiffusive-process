module

public import SubdiffusiveProcess.Paper.Foundations.PrefixFieldPrePrincipal
public import SubdiffusiveProcess.Paper.relabelled_layer_law
public import SubdiffusiveProcess.Paper.lem_crossing

@[expose] public section

noncomputable section

open MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess
open scoped ENNReal BigOperators

namespace Paper

/-- The potential lift of the canonical relabelled continuous layers has the
GMC potential-sample law at every cutoff. -/
theorem prefix_relabelled_potential_law {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (N : ℕ) :
    Measure.map (fun omega : BilateralField d => fun i : ℕ =>
      aux_lem_crossing_unforget
        (SubdiffusiveProcess.layerScaling d (N : ℤ)
          (omega ((i : ℤ) - (N : ℤ)))))
      (chaosSampleLaw M).toMeasure = M.P.toMeasure := by
  let g : ℕ → BilateralField d → ℕ → C(SpatialCoordinates d, ℝ) :=
    fun N omega i => SubdiffusiveProcess.layerScaling d (N : ℤ)
      (omega ((i : ℤ) - (N : ℤ)))
  let U : (ℕ → C(SpatialCoordinates d, ℝ)) → PotentialSample d :=
    fun layers i => aux_lem_crossing_unforget (layers i)
  have hU : Measurable U := measurable_pi_iff.mpr fun i =>
    aux_lem_crossing_measurable_unforget.comp (measurable_pi_apply i)
  have hrel : Measure.map (g N) (chaosSampleLaw M).toMeasure =
      Measure.map (fun omega : BilateralField d => fun i : ℕ => omega (i : ℤ))
        (chaosSampleLaw M).toMeasure := by
    have h := relabelled_layer_law d (chaosRootFieldLaw M) g (by
      intro N omega i y
      rfl) N
    simpa only [chaosSampleLaw] using h
  have hcomp : U ∘ (fun omega : BilateralField d => fun i : ℕ => omega (i : ℤ)) =
      aux_lem_crossing_lift := rfl
  have hproj : Measurable (fun omega : BilateralField d => fun i : ℕ => omega (i : ℤ)) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply (i : ℤ)
  have hg : Measurable (g N) := measurable_pi_iff.mpr fun i =>
    (SubdiffusiveProcess.layerScaling d (N : ℤ)).continuous.measurable.comp
      (measurable_pi_apply ((i : ℤ) - (N : ℤ)))
  calc
    Measure.map (fun omega : BilateralField d => fun i : ℕ =>
      aux_lem_crossing_unforget (SubdiffusiveProcess.layerScaling d (N : ℤ)
        (omega ((i : ℤ) - (N : ℤ))))) (chaosSampleLaw M).toMeasure =
        Measure.map U (Measure.map (g N) (chaosSampleLaw M).toMeasure) := by
          rw [Measure.map_map hU hg]
          rfl
    _ = Measure.map U (Measure.map
        (fun omega : BilateralField d => fun i : ℕ => omega (i : ℤ))
          (chaosSampleLaw M).toMeasure) := by rw [hrel]
    _ = Measure.map aux_lem_crossing_lift (chaosSampleLaw M).toMeasure := by
      rw [Measure.map_map hU hproj]
      rw [hcomp]
    _ = M.P.toMeasure := (aux_lem_crossing_measurePreserving_lift M).map_eq


/-- The principal theorem's `hEta` identifies its potentially abstract
potential sample with the canonical relabelling, so its law is exactly `M.P`. -/
theorem prefix_eta_law {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N : ℕ) :
    Measure.map (eta N) (chaosSampleLaw M).toMeasure = M.P.toMeasure := by
  have heq : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      eta N omega = (fun i : ℕ => aux_lem_crossing_unforget
        (SubdiffusiveProcess.layerScaling d (N : ℤ)
          (omega ((i : ℤ) - (N : ℤ))))) := by
    filter_upwards [hEta] with omega hω
    funext i
    have hf : SubdiffusiveProcess.layerScaling d (N : ℤ)
        (omega ((i : ℤ) - (N : ℤ))) = aux_lem_crossing_forget (eta N omega i) := by
      apply ContinuousMap.ext
      intro y
      simpa [SubdiffusiveProcess.layerScaling, aux_lem_crossing_forget] using
        (hω N i y).symm
    rw [hf, aux_lem_crossing_unforget_forget]
  calc
    Measure.map (eta N) (chaosSampleLaw M).toMeasure =
      Measure.map (fun omega : BilateralField d => fun i : ℕ =>
        aux_lem_crossing_unforget
          (SubdiffusiveProcess.layerScaling d (N : ℤ)
            (omega ((i : ℤ) - (N : ℤ)))))
        (chaosSampleLaw M).toMeasure := Measure.map_congr heq
    _ = M.P.toMeasure := prefix_relabelled_potential_law M N


theorem prefix_eta_aemeasurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N : ℕ) :
    AEMeasurable (eta N) (chaosSampleLaw M).toMeasure := by
  let ηcanon : BilateralField d → PotentialSample d := fun omega i =>
    aux_lem_crossing_unforget
      (SubdiffusiveProcess.layerScaling d (N : ℤ)
        (omega ((i : ℤ) - (N : ℤ))))
  have hmeas : Measurable ηcanon := measurable_pi_iff.mpr fun i =>
    aux_lem_crossing_measurable_unforget.comp
      ((SubdiffusiveProcess.layerScaling d (N : ℤ)).continuous.measurable.comp
        (measurable_pi_apply ((i : ℤ) - (N : ℤ))))
  refine hmeas.aemeasurable.congr ?_
  filter_upwards [hEta] with omega hω
  funext i
  have hf : SubdiffusiveProcess.layerScaling d (N : ℤ)
      (omega ((i : ℤ) - (N : ℤ))) = aux_lem_crossing_forget (eta N omega i) := by
    apply ContinuousMap.ext
    intro y
    simpa [SubdiffusiveProcess.layerScaling, aux_lem_crossing_forget] using
      (hω N i y).symm
  change aux_lem_crossing_unforget _ = eta N omega i
  rw [hf, aux_lem_crossing_unforget_forget]


theorem prefix_bank_maxObs_measurable {d : ℕ} (i n : ℕ) (z : Vec d) :
    Measurable (fun omega : PotentialSample d => aux_prefix_bank_maxObs i n z omega) := by
  have h : Measurable ((aux_psf_cells d (n - i)).sup'
      (aux_psf_cells_nonempty d (n - i))
      (fun k (omega : PotentialSample d) =>
        aux_psf_cellObs 0 (0 : Vec d) (fun _ =>
          PotentialField.spatialScale ((3 : ℝ) ^ i)
            (PotentialField.translate
              (((3 : ℝ) ^ i) •
                aux_psf_center (n - i) (((3 : ℝ) ^ (-(i : ℤ))) • z) k)
              (omega i))))) :=
    Finset.measurable_sup' _ (fun k _ =>
      aux_prefix_bank_cell_measurable i
        (aux_psf_center (n - i) (((3 : ℝ) ^ (-(i : ℤ))) • z) k))
  convert h using 1
  funext omega
  unfold aux_prefix_bank_maxObs
  rw [Finset.sup'_apply]


/-- The exact bank exponential moment under the principal coupled field law. -/
theorem prefix_eta_bank_raw_window_exp_sq {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N m j i : ℕ) (hi : i ∈ Finset.Icc (m - j) (m + j)) (z : Vec d) :
    (∫⁻ omega : BilateralField d,
      ENNReal.ofReal (Real.exp
        ((aux_prefix_bank_maxObs i (m + 1 + j) z (eta N omega) /
            aux_psf_sigma M) ^ (2 : ℕ)))
          ∂(chaosSampleLaw M).toMeasure) ≤
      (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ≥0∞) * 2 := by
  let F : PotentialSample d → ENNReal := fun omega =>
    ENNReal.ofReal (Real.exp
      ((aux_prefix_bank_maxObs i (m + 1 + j) z omega / aux_psf_sigma M) ^ (2 : ℕ)))
  have hF : Measurable F :=
    (((prefix_bank_maxObs_measurable i (m + 1 + j) z).div_const _).pow_const _).exp.ennreal_ofReal
  calc
    (∫⁻ omega : BilateralField d, F (eta N omega)
        ∂(chaosSampleLaw M).toMeasure) =
      ∫⁻ potential : PotentialSample d, F potential
        ∂Measure.map (eta N) (chaosSampleLaw M).toMeasure :=
          (lintegral_map' hF.aemeasurable
            (prefix_eta_aemeasurable M eta hEta N)).symm
    _ = ∫⁻ potential : PotentialSample d, F potential ∂M.P.toMeasure := by
      rw [prefix_eta_law M eta hEta N]
    _ ≤ (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ≥0∞) * 2 :=
      aux_prefix_bank_raw_window_exp_sq M m j i hi z


/-- Exact raw field-score spatial supremum, bounded by the scale-adapted
bank without replacing the principal observable. -/
theorem prefix_bank_normOn_le {d : ℕ} (i n : ℕ) (hin : i ≤ n)
    (z : Vec d) (omega : PotentialSample d) :
    sSup {v : ENNReal | ∃ x : Vec d, x ∈ translatedCube d (n : ℤ) z ∧
      v = ENNReal.ofReal
        |(|omega i x| + (3 : ℝ) ^ (i : ℝ) *
          Homogenization.euclideanNorm (shellGradient (omega i) x))|} ≤
      ENNReal.ofReal (aux_prefix_bank_maxObs i n z omega) := by
  refine sSup_le ?_
  rintro v ⟨x, hx, rfl⟩
  have hrp : (0 : ℝ) ≤ (3 : ℝ) ^ (i : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hen : 0 ≤ Homogenization.euclideanNorm (shellGradient (omega i) x) :=
    Real.sqrt_nonneg _
  have hnn : 0 ≤ |omega i x| + (3 : ℝ) ^ (i : ℝ) *
      Homogenization.euclideanNorm (shellGradient (omega i) x) := by
    have := abs_nonneg (omega i x)
    nlinarith
  rw [abs_of_nonneg hnn]
  refine ENNReal.ofReal_le_ofReal ?_
  have hrpow : (3 : ℝ) ^ (i : ℝ) = (3 : ℝ) ^ i := by
    rw [← Real.rpow_natCast (3 : ℝ) i]
  rw [hrpow]
  exact aux_prefix_bank_le_maxObs i n hin z x omega hx


theorem prefix_raw_field_term_le_bank {d : ℕ}
    (s : ℝ) (m j : ℕ) (z : Vec d) (omega : PotentialSample d) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
      ∑ i ∈ Finset.Icc (m - j) (m + j),
        sSup {v : ENNReal | ∃ x : Vec d,
          x ∈ translatedCube d ((m + 1 + j : ℕ) : ℤ) z ∧
          v = ENNReal.ofReal
            |(|omega i x| + (3 : ℝ) ^ (i : ℝ) *
              Homogenization.euclideanNorm (shellGradient (omega i) x))|} ≤
    ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
      ∑ i ∈ Finset.Icc (m - j) (m + j),
        ENNReal.ofReal (aux_prefix_bank_maxObs i (m + 1 + j) z omega) := by
  gcongr with i hi
  have hin : i ≤ m + 1 + j := by
    have := (Finset.mem_Icc.mp hi).2
    omega
  exact prefix_bank_normOn_le i (m + 1 + j) hin z omega


/-- The exact `Fsc` raw coordinate is dominated pointwise by the discounted
supremum of the scale-adapted finite banks. -/
theorem prefix_raw_Fsc_le_bank {d : ℕ} [NeZero d]
    (M : GMCModel d) (s eps : ℝ) (omega : PotentialSample d)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal)
    (Zsc : ℕ → Vec d → ℝ) (goodEvt : ℕ → Vec d → Prop)
    (hPrimitive : primitive_scores d M s eps omega Fsc Psc Rsc Dsc Zsc goodEvt)
    (m : ℕ) (z : Vec d) :
    Fsc m z ≤ sSup {v : ENNReal | ∃ j : ℕ,
      v = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
        ∑ i ∈ Finset.Icc (m - j) (m + j),
          ENNReal.ofReal (aux_prefix_bank_maxObs i (m + 1 + j) z omega)} := by
  rcases hPrimitive with ⟨_, _, _, _, hF, _⟩
  rw [hF m z]
  refine sSup_le ?_
  rintro v ⟨j, rfl⟩
  have hcast : ((m : ℤ) + 1 + (j : ℤ)) = (((m + 1 + j : ℕ)) : ℤ) := by
    push_cast
    ring
  rw [hcast]
  exact le_sSup_of_le ⟨j, rfl⟩
    (prefix_raw_field_term_le_bank s m j z omega)


/-- First moment of the adapted bank; its cell cardinal depends only on the
scale gap. This is the input for a discounted summable majorant. -/
theorem prefix_bank_maxObs_first_moment {d : ℕ} (M : GMCModel d)
    (i n : ℕ) (z : Vec d) :
    (∫⁻ omega : PotentialSample d,
      ENNReal.ofReal (aux_prefix_bank_maxObs i n z omega) ∂M.P.toMeasure) ≤
      ENNReal.ofReal (2 * aux_psf_sigma M *
        Real.sqrt (1 + Real.log
          (2 * ((aux_psf_cells d (n - i)).card : ℝ)))) := by
  let q : ℝ := (3 : ℝ) ^ (-(i : ℤ))
  let r : ℝ := (3 : ℝ) ^ i
  let c : (Fin d → ℕ) → PotentialSample d → ℝ := fun k omega =>
    aux_psf_cellObs 0 (0 : Vec d) (fun _ =>
      PotentialField.spatialScale r
        (PotentialField.translate
          (r • aux_psf_center (n - i) (q • z) k) (omega i)))
  have hc : ∀ k omega, 0 ≤ c k omega := by
    intro k omega
    exact aux_psf_cellObs_nonneg 0 0 (fun _ =>
      PotentialField.spatialScale r
        (PotentialField.translate
          (r • aux_psf_center (n - i) (q • z) k) (omega i)))
  have hmeas : ∀ k, Measurable (c k) := by
    intro k
    exact aux_prefix_bank_cell_measurable i (aux_psf_center (n - i) (q • z) k)
  have hmom : ∀ k,
      (∫⁻ omega : PotentialSample d,
        ENNReal.ofReal (Real.exp ((c k omega / aux_psf_sigma M) ^ 2))
          ∂M.P.toMeasure) ≤ 2 := by
    intro k
    exact aux_prefix_actual_scaled_cell_exp M i (aux_psf_center (n - i) (q • z) k)
  exact aux_psf_lintegral_sup'_sqrt M.P.toMeasure (aux_psf_cells d (n - i))
    (aux_psf_cells_nonempty d (n - i)) c hc hmeas (aux_psf_sigma M)
    (aux_psf_sigma_pos M) hmom


def prefix_bank_Fmaj {d : ℕ} (s : ℝ) (m : ℕ) (z : Vec d) (j : ℕ)
    (omega : PotentialSample d) : ENNReal :=
  ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
    ∑ i ∈ Finset.Icc (m - j) (m + j),
      ENNReal.ofReal (aux_prefix_bank_maxObs i (m + 1 + j) z omega)

def prefix_bank_Fbound {d : ℕ} (M : GMCModel d) (s : ℝ) (j : ℕ) : ℝ :=
  (3 : ℝ) ^ (-(s * (j : ℝ) / 8)) * ((2 * j + 1 : ℕ) : ℝ) *
    (2 * aux_psf_sigma M * Real.sqrt (1 + Real.log
      (2 * (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ))))

theorem prefix_bank_Fmaj_measurable {d : ℕ} (s : ℝ) (m : ℕ) (z : Vec d)
    (j : ℕ) : Measurable (fun omega : PotentialSample d =>
      prefix_bank_Fmaj s m z j omega) := by
  unfold prefix_bank_Fmaj
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ ?_
  intro i _
  exact (prefix_bank_maxObs_measurable i (m + 1 + j) z).ennreal_ofReal


theorem prefix_bank_Fmaj_first_moment {d : ℕ} (M : GMCModel d)
    (s : ℝ) (m : ℕ) (z : Vec d) (j : ℕ) :
    (∫⁻ omega : PotentialSample d, prefix_bank_Fmaj s m z j omega
      ∂M.P.toMeasure) ≤ ENNReal.ofReal (prefix_bank_Fbound M s j) := by
  set K : ℝ := 2 * aux_psf_sigma M * Real.sqrt (1 + Real.log
      (2 * (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ))) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (aux_psf_sigma_pos M).le)
      (Real.sqrt_nonneg _)
  have hc0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s * (j : ℝ) / 8)) :=
    Real.rpow_nonneg (by norm_num) _
  have hmeas : Measurable fun omega : PotentialSample d =>
      ∑ i ∈ Finset.Icc (m - j) (m + j),
        ENNReal.ofReal (aux_prefix_bank_maxObs i (m + 1 + j) z omega) := by
    refine Finset.measurable_sum _ ?_
    intro i _
    exact (prefix_bank_maxObs_measurable i (m + 1 + j) z).ennreal_ofReal
  have hcard : ((Finset.Icc (m - j) (m + j)).card : ℝ) ≤
      ((2 * j + 1 : ℕ) : ℝ) := by
    have hc : (Finset.Icc (m - j) (m + j)).card = m + j + 1 - (m - j) := by
      rw [Nat.card_Icc]
    rw [hc]
    have : m + j + 1 - (m - j) ≤ 2 * j + 1 := by omega
    exact_mod_cast this
  have hsum : (∫⁻ omega : PotentialSample d,
      ∑ i ∈ Finset.Icc (m - j) (m + j),
        ENNReal.ofReal (aux_prefix_bank_maxObs i (m + 1 + j) z omega)
          ∂M.P.toMeasure) ≤
      ENNReal.ofReal (((2 * j + 1 : ℕ) : ℝ) * K) := by
    rw [lintegral_finset_sum _ (fun i _ =>
      (prefix_bank_maxObs_measurable i (m + 1 + j) z).ennreal_ofReal)]
    calc
      ∑ i ∈ Finset.Icc (m - j) (m + j),
          ∫⁻ omega : PotentialSample d,
            ENNReal.ofReal (aux_prefix_bank_maxObs i (m + 1 + j) z omega)
              ∂M.P.toMeasure ≤
        ∑ _i ∈ Finset.Icc (m - j) (m + j), ENNReal.ofReal K := by
          apply Finset.sum_le_sum
          intro i hi
          have hgap : (m + 1 + j) - i ≤ 2 * j + 1 := by
            have := (Finset.mem_Icc.mp hi).1
            omega
          have hcard' : (aux_psf_cells d ((m + 1 + j) - i)).card ≤
              (2 * 3 ^ (2 * j + 1) + 1) ^ d := by
            rw [aux_psf_cells_card]
            exact Nat.pow_le_pow_left (by
              have hp : 3 ^ ((m + 1 + j) - i) ≤ 3 ^ (2 * j + 1) :=
                Nat.pow_le_pow_right (by omega) hgap
              omega) d
          refine (prefix_bank_maxObs_first_moment M i (m + 1 + j) z).trans ?_
          apply ENNReal.ofReal_mono
          rw [hK]
          apply mul_le_mul_of_nonneg_left _
            (mul_nonneg (by norm_num) (aux_psf_sigma_pos M).le)
          apply Real.sqrt_le_sqrt
          have hcellpos : 0 < (aux_psf_cells d ((m + 1 + j) - i)).card :=
            Finset.card_pos.mpr (aux_psf_cells_nonempty d ((m + 1 + j) - i))
          have hargpos : 0 < (2 : ℝ) *
              ((aux_psf_cells d ((m + 1 + j) - i)).card : ℝ) := by
            have : 0 < ((aux_psf_cells d ((m + 1 + j) - i)).card : ℝ) :=
              Nat.cast_pos.mpr hcellpos
            positivity
          have hargle : (2 : ℝ) *
              ((aux_psf_cells d ((m + 1 + j) - i)).card : ℝ) ≤
              2 * (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ) := by
            exact_mod_cast Nat.mul_le_mul_left 2 hcard'
          have hlogle := Real.log_le_log hargpos hargle
          linarith
      _ = ((Finset.Icc (m - j) (m + j)).card : ENNReal) *
          ENNReal.ofReal K := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal (((2 * j + 1 : ℕ) : ℝ)) *
          ENNReal.ofReal K := by
            gcongr
            rw [← ENNReal.ofReal_natCast]
            exact ENNReal.ofReal_le_ofReal hcard
      _ = ENNReal.ofReal (((2 * j + 1 : ℕ) : ℝ) * K) :=
        (ENNReal.ofReal_mul (by positivity)).symm
  unfold prefix_bank_Fmaj prefix_bank_Fbound
  rw [lintegral_const_mul _ hmeas]
  calc
    ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
        ∫⁻ omega : PotentialSample d,
          ∑ i ∈ Finset.Icc (m - j) (m + j),
            ENNReal.ofReal (aux_prefix_bank_maxObs i (m + 1 + j) z omega)
              ∂M.P.toMeasure ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
        ENNReal.ofReal (((2 * j + 1 : ℕ) : ℝ) * K) := by gcongr
    _ = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8)) *
        (((2 * j + 1 : ℕ) : ℝ) * K)) := (ENNReal.ofReal_mul hc0).symm
    _ = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8)) *
        ((2 * j + 1 : ℕ) : ℝ) * K) := by ring_nf


/-- The cutoff-uniform first-moment bounds are summable in the discount
depth. They are dominated by the existing proof's geometric-series bound
sampled at even indices. -/
theorem prefix_bank_Fbound_summable {d : ℕ} (M : GMCModel d)
    (s : ℝ) (hs : 0 < s) :
    Summable (fun j : ℕ => prefix_bank_Fbound M s j) := by
  have hsource : Summable (fun j : ℕ => aux_psf_Fbound M (s / 2) 0 (2 * j)) :=
    (aux_psf_summable_Fbound M (s / 2) (by linarith) 0).comp_injective
      (by intro a b h; omega)
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hsource
  · unfold prefix_bank_Fbound
    have hsqrt : 0 ≤ Real.sqrt (1 + Real.log
        (2 * (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ))) := Real.sqrt_nonneg _
    have hsig := (aux_psf_sigma_pos M).le
    have hdisc : 0 ≤ (3 : ℝ) ^ (-(s * (j : ℝ) / 8)) :=
      Real.rpow_nonneg (by norm_num) _
    positivity
  · have hdisc : (3 : ℝ) ^ (-(s * (j : ℝ) / 8)) =
        (3 : ℝ) ^ (-((s / 2) * ((2 * j : ℕ) : ℝ) / 8)) := by
      congr 1
      push_cast
      ring
    have hfactor : ((2 * j + 1 : ℕ) : ℝ) ≤
        ((2 * (2 * j) + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 2 * j + 1 ≤ 2 * (2 * j) + 1 by omega)
    have hrest : 0 ≤ 2 * aux_psf_sigma M * Real.sqrt
        (1 + Real.log (2 * (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ))) :=
      mul_nonneg (mul_nonneg (by norm_num) (aux_psf_sigma_pos M).le)
        (Real.sqrt_nonneg _)
    have hdisc0 : 0 ≤ (3 : ℝ) ^ (-(s * (j : ℝ) / 8)) :=
      Real.rpow_nonneg (by norm_num) _
    have hmul := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hfactor hrest) hdisc0
    unfold prefix_bank_Fbound aux_psf_Fbound
    rw [← hdisc]
    simpa only [show (0 : ℕ) + 1 + 2 * j = 2 * j + 1 by omega,
      mul_assoc] using hmul


theorem prefix_bank_Fbound_nonneg {d : ℕ} (M : GMCModel d)
    (s : ℝ) (j : ℕ) : 0 ≤ prefix_bank_Fbound M s j := by
  unfold prefix_bank_Fbound
  have hsig := (aux_psf_sigma_pos M).le
  have hdisc : 0 ≤ (3 : ℝ) ^ (-(s * (j : ℝ) / 8)) :=
    Real.rpow_nonneg (by norm_num) _
  have hsqrt : 0 ≤ Real.sqrt (1 + Real.log
      (2 * (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ))) :=
    Real.sqrt_nonneg _
  positivity

theorem prefix_bank_Fmaj_tsum_ae {d : ℕ} (M : GMCModel d)
    (s : ℝ) (hs : 0 < s) (m : ℕ) (z : Vec d) :
    ∀ᵐ omega ∂M.P.toMeasure,
      (∑' j : ℕ, prefix_bank_Fmaj s m z j omega) ≠ ⊤ := by
  have hmeas : ∀ j : ℕ, AEMeasurable (fun omega : PotentialSample d =>
      prefix_bank_Fmaj s m z j omega) M.P.toMeasure :=
    fun j => (prefix_bank_Fmaj_measurable s m z j).aemeasurable
  have hint : (∫⁻ omega : PotentialSample d,
      (∑' j : ℕ, prefix_bank_Fmaj s m z j omega) ∂M.P.toMeasure) ≠ ⊤ := by
    rw [lintegral_tsum hmeas]
    have hb : ∀ j,
        (∫⁻ omega : PotentialSample d, prefix_bank_Fmaj s m z j omega
          ∂M.P.toMeasure) ≤
          ENNReal.ofReal (prefix_bank_Fbound M s j) :=
      prefix_bank_Fmaj_first_moment M s m z
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hb)
    rw [← ENNReal.ofReal_tsum_of_nonneg (prefix_bank_Fbound_nonneg M s)
      (prefix_bank_Fbound_summable M s hs)]
    exact ENNReal.ofReal_ne_top
  have hlt := ae_lt_top' (AEMeasurable.ennreal_tsum hmeas) hint
  filter_upwards [hlt] with omega h
  exact h.ne


theorem prefix_raw_Fsc_le_tsum {d : ℕ} [NeZero d]
    (M : GMCModel d) (s eps : ℝ) (omega : PotentialSample d)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal)
    (Zsc : ℕ → Vec d → ℝ) (goodEvt : ℕ → Vec d → Prop)
    (hPrimitive : primitive_scores d M s eps omega Fsc Psc Rsc Dsc Zsc goodEvt)
    (m : ℕ) (z : Vec d) :
    Fsc m z ≤ ∑' j : ℕ, prefix_bank_Fmaj s m z j omega := by
  refine (prefix_raw_Fsc_le_bank M s eps omega Fsc Psc Rsc Dsc Zsc goodEvt
    hPrimitive m z).trans ?_
  refine sSup_le ?_
  rintro v ⟨j, rfl⟩
  simpa only [prefix_bank_Fmaj] using! ENNReal.le_tsum (f := fun j => prefix_bank_Fmaj s m z j omega) j


/-- The exact coupled raw field-score coordinate is finite almost surely,
uniformly in the deterministic cutoff index. -/
theorem prefix_eta_raw_Fsc_ae_finite {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) (s eps : ℝ) (hs : 0 < s)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (F Praw Rraw Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
    (hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
      primitive_scores d M s eps (eta N omega)
        (fun m y => F N m y omega) (fun m y => Praw N m y omega)
        (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
        (fun m y => Z N m y omega) (fun m y => rawGood N m y omega))
    (N m : ℕ) (z : Vec d) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, F N m z omega ≠ ⊤ := by
  have hpush : ∀ᵐ potential ∂Measure.map (eta N) (chaosSampleLaw M).toMeasure,
      (∑' j : ℕ, prefix_bank_Fmaj s m z j potential) ≠ ⊤ := by
    rw [prefix_eta_law M eta hEta N]
    exact prefix_bank_Fmaj_tsum_ae M s hs m z
  have htail := ae_of_ae_map (prefix_eta_aemeasurable M eta hEta N) hpush
  filter_upwards [hPrimitive, htail] with omega hp ht
  have hle := prefix_raw_Fsc_le_tsum M s eps (eta N omega)
    (fun m y => F N m y omega) (fun m y => Praw N m y omega)
    (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
    (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)
    (hp N) m z
  exact ne_top_of_le_ne_top ht hle


/-- Polynomial growth against one exponential, with the threshold chosen at
least as large as the moment order. This is the elementary higher-moment
maximal inequality before inserting a bank cell count. -/
theorem prefix_pow_le_exp_tail (q : ℕ) (hq : 1 ≤ q) (b u : ℝ)
    (hb : (q : ℝ) ≤ b) (hu : 0 ≤ u) :
    u ^ q ≤ b ^ q + b ^ q / Real.exp b * Real.exp u := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hbpos : 0 < b := lt_of_lt_of_le hqpos hb
  have hbnonneg : 0 ≤ b := hbpos.le
  have htail0 : 0 ≤ b ^ q / Real.exp b * Real.exp u := by positivity
  rcases le_total u b with h | h
  · have hpow : u ^ q ≤ b ^ q := pow_le_pow_left₀ hu h q
    linarith
  · have hdelta : 0 ≤ u - b := sub_nonneg.mpr h
    have hbase : u ≤ b * Real.exp ((u - b) / q) := by
      have hexp := Real.add_one_le_exp ((u - b) / q)
      have hlinear : u ≤ b * (1 + (u - b) / q) := by
        rw [mul_add]
        have hdiv : 1 ≤ b / q := (one_le_div hqpos).mpr hb
        have hineq : u - b ≤ b * ((u - b) / q) := by
          calc
            u - b = (u - b) * 1 := by ring
            _ ≤ (u - b) * (b / q) :=
              mul_le_mul_of_nonneg_left hdiv hdelta
            _ = b * ((u - b) / q) := by ring
        linarith
      exact hlinear.trans
        (mul_le_mul_of_nonneg_left (by simpa [add_comm] using hexp) hbnonneg)
    have hpow : u ^ q ≤ (b * Real.exp ((u - b) / q)) ^ q :=
      pow_le_pow_left₀ hu hbase q
    have hrewrite : (b * Real.exp ((u - b) / q)) ^ q =
        b ^ q / Real.exp b * Real.exp u := by
      rw [mul_pow, ← Real.exp_nat_mul]
      have hqmul : (q : ℝ) * ((u - b) / q) = u - b := by
        field_simp
      rw [hqmul, Real.exp_sub]
      ring
    rw [hrewrite] at hpow
    exact hpow.trans (le_add_of_nonneg_left (pow_nonneg hbnonneg q))


theorem prefix_even_moment_of_exp_sq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : Measurable Y) (sigma : ℝ)
    (q : ℕ) (hq : 1 ≤ q) (b : ℝ) (hb : (q : ℝ) ≤ b)
    (K : ENNReal)
    (hExp : (∫⁻ ω, ENNReal.ofReal (Real.exp ((Y ω / sigma) ^ (2 : ℕ))) ∂μ) ≤ K) :
    (∫⁻ ω, ENNReal.ofReal (((Y ω / sigma) ^ (2 : ℕ)) ^ q) ∂μ) ≤
      ENNReal.ofReal (b ^ q) +
        ENNReal.ofReal (b ^ q / Real.exp b) * K := by
  have hb0 : 0 ≤ b := le_trans (Nat.cast_nonneg q) hb
  have hcoef : 0 ≤ b ^ q / Real.exp b := by positivity
  have hpt : ∀ ω : Ω,
      ENNReal.ofReal (((Y ω / sigma) ^ (2 : ℕ)) ^ q) ≤
        ENNReal.ofReal (b ^ q) +
          ENNReal.ofReal (b ^ q / Real.exp b) *
            ENNReal.ofReal (Real.exp ((Y ω / sigma) ^ (2 : ℕ))) := by
    intro ω
    have hscalar := prefix_pow_le_exp_tail q hq b
      ((Y ω / sigma) ^ (2 : ℕ)) hb (sq_nonneg _)
    calc
      ENNReal.ofReal (((Y ω / sigma) ^ (2 : ℕ)) ^ q) ≤
        ENNReal.ofReal (b ^ q + b ^ q / Real.exp b *
          Real.exp ((Y ω / sigma) ^ (2 : ℕ))) :=
            ENNReal.ofReal_le_ofReal hscalar
      _ ≤ ENNReal.ofReal (b ^ q) +
          ENNReal.ofReal (b ^ q / Real.exp b *
            Real.exp ((Y ω / sigma) ^ (2 : ℕ))) := ENNReal.ofReal_add_le
      _ = ENNReal.ofReal (b ^ q) +
          ENNReal.ofReal (b ^ q / Real.exp b) *
            ENNReal.ofReal (Real.exp ((Y ω / sigma) ^ (2 : ℕ))) := by
              rw [ENNReal.ofReal_mul hcoef]
  have hExpMeas : Measurable (fun ω =>
      ENNReal.ofReal (Real.exp ((Y ω / sigma) ^ (2 : ℕ)))) :=
    (((hY.div_const _).pow_const _).exp).ennreal_ofReal
  calc
    (∫⁻ ω, ENNReal.ofReal (((Y ω / sigma) ^ (2 : ℕ)) ^ q) ∂μ) ≤
      ∫⁻ ω, (ENNReal.ofReal (b ^ q) +
        ENNReal.ofReal (b ^ q / Real.exp b) *
          ENNReal.ofReal (Real.exp ((Y ω / sigma) ^ (2 : ℕ)))) ∂μ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (b ^ q) +
        ENNReal.ofReal (b ^ q / Real.exp b) *
          (∫⁻ ω, ENNReal.ofReal (Real.exp ((Y ω / sigma) ^ (2 : ℕ))) ∂μ) := by
            rw [lintegral_add_left measurable_const,
              lintegral_const_mul _ hExpMeas, lintegral_const,
              measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (b ^ q) +
        ENNReal.ofReal (b ^ q / Real.exp b) * K := by gcongr


/-- Every fixed even moment of the adapted maximum, with a threshold that
can be selected after its exact finite cell count. -/
theorem prefix_bank_even_moment {d : ℕ} (M : GMCModel d)
    (i n : ℕ) (z : Vec d) (q : ℕ) (hq : 1 ≤ q) (b : ℝ)
    (hb : (q : ℝ) ≤ b) :
    (∫⁻ omega : PotentialSample d,
      ENNReal.ofReal
        (((aux_prefix_bank_maxObs i n z omega / aux_psf_sigma M) ^ (2 : ℕ)) ^ q)
          ∂M.P.toMeasure) ≤
      ENNReal.ofReal (b ^ q) +
        ENNReal.ofReal (b ^ q / Real.exp b) *
          (((aux_psf_cells d (n - i)).card : ENNReal) * 2) := by
  exact prefix_even_moment_of_exp_sq M.P.toMeasure
    (fun omega => aux_prefix_bank_maxObs i n z omega)
    (prefix_bank_maxObs_measurable i n z) (aux_psf_sigma M)
    q hq b hb _ (aux_prefix_bank_maxObs_exp_sq M i n z)


/-- Optimized finite-bank maximal inequality. Every chosen even order pays
only the logarithm of the exact cell count. -/
theorem prefix_bank_even_moment_log {d : ℕ} (M : GMCModel d)
    (i n : ℕ) (z : Vec d) (q : ℕ) (hq : 1 ≤ q) :
    let C : ℝ := 2 * ((aux_psf_cells d (n - i)).card : ℝ)
    let b : ℝ := (q : ℝ) + 1 + Real.log C
    (∫⁻ omega : PotentialSample d,
      ENNReal.ofReal
        (((aux_prefix_bank_maxObs i n z omega / aux_psf_sigma M) ^ (2 : ℕ)) ^ q)
          ∂M.P.toMeasure) ≤ 2 * ENNReal.ofReal (b ^ q) := by
  dsimp
  let C : ℝ := 2 * ((aux_psf_cells d (n - i)).card : ℝ)
  let b : ℝ := (q : ℝ) + 1 + Real.log C
  have hcardpos : 0 < (aux_psf_cells d (n - i)).card :=
    Finset.card_pos.mpr (aux_psf_cells_nonempty d (n - i))
  have hCpos : 0 < C := by
    dsimp [C]
    have hc : 0 < ((aux_psf_cells d (n - i)).card : ℝ) :=
      Nat.cast_pos.mpr hcardpos
    positivity
  have hC1 : 1 ≤ C := by
    dsimp [C]
    have hc : 1 ≤ ((aux_psf_cells d (n - i)).card : ℝ) :=
      Nat.one_le_cast.mpr hcardpos
    linarith
  have hb : (q : ℝ) ≤ b := by
    dsimp [b]
    have hlog := Real.log_nonneg hC1
    linarith
  have hb0 : 0 ≤ b := le_trans (Nat.cast_nonneg q) hb
  have hcoef : 0 ≤ b ^ q / Real.exp b := by positivity
  have hCcast : (((aux_psf_cells d (n - i)).card : ENNReal) * 2) =
      ENNReal.ofReal C := by
    dsimp [C]
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast]
    norm_num [mul_comm]
  have hExp : Real.exp b = Real.exp ((q : ℝ) + 1) * C := by
    dsimp [b]
    rw [Real.exp_add, Real.exp_log hCpos]
  have hCexp : C ≤ Real.exp b := by
    rw [hExp]
    have hE : 1 ≤ Real.exp ((q : ℝ) + 1) := by
      have h := Real.add_one_le_exp ((q : ℝ) + 1)
      linarith [Nat.cast_nonneg (α := ℝ) q]
    nlinarith [hCpos.le]
  have hcoefbound : b ^ q / Real.exp b * C ≤ b ^ q := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (Real.exp_pos b)).2
    exact mul_le_mul_of_nonneg_left hCexp (pow_nonneg hb0 q)
  have hbank := prefix_bank_even_moment M i n z q hq b hb
  calc
    (∫⁻ omega : PotentialSample d,
      ENNReal.ofReal
        (((aux_prefix_bank_maxObs i n z omega / aux_psf_sigma M) ^ (2 : ℕ)) ^ q)
          ∂M.P.toMeasure) ≤
      ENNReal.ofReal (b ^ q) +
        ENNReal.ofReal (b ^ q / Real.exp b) * ENNReal.ofReal C := by
          simpa only [hCcast] using hbank
    _ = ENNReal.ofReal (b ^ q) +
        ENNReal.ofReal (b ^ q / Real.exp b * C) := by
          rw [ENNReal.ofReal_mul hcoef]
    _ ≤ ENNReal.ofReal (b ^ q) + ENNReal.ofReal (b ^ q) := by
          exact add_le_add_right (ENNReal.ofReal_le_ofReal hcoefbound) _
    _ = 2 * ENNReal.ofReal (b ^ q) := by ring


/-- Fixed even moment of every raw-window bank, uniform in the cutoff `m`.
The only size parameter on the right is the discount depth `j`. -/
theorem prefix_bank_raw_window_even_moment_log {d : ℕ}
    (M : GMCModel d) (m j i : ℕ)
    (hi : i ∈ Finset.Icc (m - j) (m + j)) (z : Vec d)
    (q : ℕ) (hq : 1 ≤ q) :
    let b : ℝ := (q : ℝ) + 1 +
      Real.log (2 * (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ))
    (∫⁻ omega : PotentialSample d,
      ENNReal.ofReal
        (((aux_prefix_bank_maxObs i (m + 1 + j) z omega /
          aux_psf_sigma M) ^ (2 : ℕ)) ^ q) ∂M.P.toMeasure) ≤
      2 * ENNReal.ofReal (b ^ q) := by
  dsimp
  let C₁ : ℝ := 2 *
    ((aux_psf_cells d ((m + 1 + j) - i)).card : ℝ)
  let C₂ : ℝ := 2 * (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ)
  let b₁ : ℝ := (q : ℝ) + 1 + Real.log C₁
  let b₂ : ℝ := (q : ℝ) + 1 + Real.log C₂
  have hcard : (aux_psf_cells d ((m + 1 + j) - i)).card ≤
      (2 * 3 ^ (2 * j + 1) + 1) ^ d := by
    rw [aux_psf_cells_card]
    exact aux_prefix_actual_scale_gap_card_bound d m j i hi
  have hC₁pos : 0 < C₁ := by
    dsimp [C₁]
    have h := Finset.card_pos.mpr
      (aux_psf_cells_nonempty d ((m + 1 + j) - i))
    have : 0 < ((aux_psf_cells d ((m + 1 + j) - i)).card : ℝ) :=
      Nat.cast_pos.mpr h
    positivity
  have hC₁le : C₁ ≤ C₂ := by
    dsimp [C₁, C₂]
    exact_mod_cast Nat.mul_le_mul_left 2 hcard
  have hb : b₁ ≤ b₂ := by
    dsimp [b₁, b₂]
    have h := Real.log_le_log hC₁pos hC₁le
    linarith
  have hb₁nonneg : 0 ≤ b₁ := by
    dsimp [b₁]
    have hC₁one : 1 ≤ C₁ := by
      dsimp [C₁]
      have h := Finset.card_pos.mpr
        (aux_psf_cells_nonempty d ((m + 1 + j) - i))
      have : 1 ≤ ((aux_psf_cells d ((m + 1 + j) - i)).card : ℝ) :=
        Nat.one_le_cast.mpr h
      linarith
    have hlog := Real.log_nonneg hC₁one
    positivity
  have hpow : b₁ ^ q ≤ b₂ ^ q := pow_le_pow_left₀ hb₁nonneg hb q
  have hbase := prefix_bank_even_moment_log M i (m + 1 + j) z q hq
  exact hbase.trans (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hpow) zero_le)


/-- The optimized fixed even moment under the actual coupled cutoff law. -/
theorem prefix_eta_bank_raw_window_even_moment_log {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N m j i : ℕ) (hi : i ∈ Finset.Icc (m - j) (m + j))
    (z : Vec d) (q : ℕ) (hq : 1 ≤ q) :
    let b : ℝ := (q : ℝ) + 1 +
      Real.log (2 * (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ))
    (∫⁻ omega : BilateralField d,
      ENNReal.ofReal
        (((aux_prefix_bank_maxObs i (m + 1 + j) z (eta N omega) /
          aux_psf_sigma M) ^ (2 : ℕ)) ^ q)
          ∂(chaosSampleLaw M).toMeasure) ≤
      2 * ENNReal.ofReal (b ^ q) := by
  dsimp
  let F : PotentialSample d → ENNReal := fun omega =>
    ENNReal.ofReal
      (((aux_prefix_bank_maxObs i (m + 1 + j) z omega /
        aux_psf_sigma M) ^ (2 : ℕ)) ^ q)
  have hF : Measurable F :=
    ((((prefix_bank_maxObs_measurable i (m + 1 + j) z).div_const _).pow_const _).pow_const _).ennreal_ofReal
  calc
    (∫⁻ omega : BilateralField d, F (eta N omega)
        ∂(chaosSampleLaw M).toMeasure) =
      ∫⁻ potential : PotentialSample d, F potential
        ∂Measure.map (eta N) (chaosSampleLaw M).toMeasure :=
          (lintegral_map' hF.aemeasurable
            (prefix_eta_aemeasurable M eta hEta N)).symm
    _ = ∫⁻ potential : PotentialSample d, F potential ∂M.P.toMeasure := by
      rw [prefix_eta_law M eta hEta N]
    _ ≤ 2 * ENNReal.ofReal ((q + 1 +
        Real.log (2 * (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ))) ^ q) :=
      prefix_bank_raw_window_even_moment_log M m j i hi z q hq


theorem prefix_even_enorm_identity (Y : ℝ) (hY : 0 ≤ Y) (q : ℕ) :
    ‖Y‖ₑ ^ (((2 * q : ℕ) : ENNReal).toReal) =
      ENNReal.ofReal ((Y ^ (2 : ℕ)) ^ q) := by
  rw [Real.enorm_eq_ofReal hY]
  have hcast : (((2 * q : ℕ) : ENNReal).toReal) = ((2 * q : ℕ) : ℝ) := by
    norm_cast
  rw [hcast, ENNReal.rpow_natCast]
  rw [← ENNReal.ofReal_pow hY]
  congr 1
  rw [← pow_mul]


theorem prefix_bank_maxObs_nonneg {d : ℕ} (i n : ℕ) (z : Vec d)
    (omega : PotentialSample d) :
    0 ≤ aux_prefix_bank_maxObs i n z omega := by
  let q : ℝ := (3 : ℝ) ^ (-(i : ℤ))
  let r : ℝ := (3 : ℝ) ^ i
  obtain ⟨k, hk⟩ := aux_psf_cells_nonempty d (n - i)
  have hcell : 0 ≤ aux_psf_cellObs 0 (0 : Vec d) (fun _ =>
      PotentialField.spatialScale r
        (PotentialField.translate
          (r • aux_psf_center (n - i) (q • z) k) (omega i))) :=
    aux_psf_cellObs_nonneg 0 0 _
  exact hcell.trans (Finset.le_sup' (f := fun k =>
    aux_psf_cellObs 0 (0 : Vec d) (fun _ =>
      PotentialField.spatialScale r
        (PotentialField.translate
          (r • aux_psf_center (n - i) (q • z) k) (omega i)))) hk)


/-- Uniform `L^(2q)` norm of the *normalized* actual coupled bank. -/
theorem prefix_eta_bank_raw_window_eLpNorm {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N m j i : ℕ) (hi : i ∈ Finset.Icc (m - j) (m + j))
    (z : Vec d) (q : ℕ) (hq : 1 ≤ q) :
    let b : ℝ := (q : ℝ) + 1 +
      Real.log (2 * (((2 * 3 ^ (2 * j + 1) + 1) ^ d : ℕ) : ℝ))
    eLpNorm (fun omega : BilateralField d =>
      aux_prefix_bank_maxObs i (m + 1 + j) z (eta N omega) / aux_psf_sigma M)
      ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
      (2 * ENNReal.ofReal (b ^ q)) ^ (1 / ((2 * q : ℕ) : ℝ)) := by
  dsimp
  let p : ENNReal := ((2 * q : ℕ) : ENNReal)
  have hp0 : p ≠ 0 := by
    dsimp [p]
    norm_cast
    omega
  have hptop : p ≠ ⊤ := by dsimp [p]; exact ENNReal.coe_ne_top
  erw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop
    ((((prefix_bank_maxObs_measurable i (m + 1 + j) z).div_const _).comp_aemeasurable
      (prefix_eta_aemeasurable M eta hEta N)).aestronglyMeasurable)]
  have hpoint : ∀ omega : BilateralField d,
      ‖aux_prefix_bank_maxObs i (m + 1 + j) z (eta N omega) /
        aux_psf_sigma M‖ₑ ^ p.toReal =
      ENNReal.ofReal (((aux_prefix_bank_maxObs i (m + 1 + j) z (eta N omega) /
        aux_psf_sigma M) ^ (2 : ℕ)) ^ q) := by
    intro omega
    have hY : 0 ≤ aux_prefix_bank_maxObs i (m + 1 + j) z (eta N omega) /
        aux_psf_sigma M :=
      div_nonneg (prefix_bank_maxObs_nonneg i (m + 1 + j) z (eta N omega))
        (aux_psf_sigma_pos M).le
    exact prefix_even_enorm_identity _ hY q
  simp only [Function.comp_apply]
  simp_rw [hpoint]
  have hmom := prefix_eta_bank_raw_window_even_moment_log M eta hEta
    N m j i hi z q hq
  exact ENNReal.rpow_le_rpow hmom (by positivity)


theorem prefix_eta_bank_aestronglyMeasurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N i n : ℕ) (z : Vec d) :
    AEStronglyMeasurable (fun omega : BilateralField d =>
      aux_prefix_bank_maxObs i n z (eta N omega) / aux_psf_sigma M)
      (chaosSampleLaw M).toMeasure := by
  exact (((prefix_bank_maxObs_measurable i n z).div_const _).comp_aemeasurable
    (prefix_eta_aemeasurable M eta hEta N)).aestronglyMeasurable


/-- The finite raw window obeys Minkowski's inequality under the exact
coupled cutoff law, before the discount depth is summed. -/
theorem prefix_eta_bank_raw_window_eLpNorm_sum {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d)
    (eta : ℕ → BilateralField d → PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (N m j : ℕ) (z : Vec d) (q : ℕ) (hq : 1 ≤ q) :
    eLpNorm (fun omega : BilateralField d =>
      ∑ i ∈ Finset.Icc (m - j) (m + j),
        aux_prefix_bank_maxObs i (m + 1 + j) z (eta N omega) /
          aux_psf_sigma M)
      ((2 * q : ℕ) : ENNReal) (chaosSampleLaw M).toMeasure ≤
      ∑ i ∈ Finset.Icc (m - j) (m + j),
        eLpNorm (fun omega : BilateralField d =>
          aux_prefix_bank_maxObs i (m + 1 + j) z (eta N omega) /
            aux_psf_sigma M) ((2 * q : ℕ) : ENNReal)
            (chaosSampleLaw M).toMeasure := by
  let p : ENNReal := ((2 * q : ℕ) : ENNReal)
  have hp : 1 ≤ p := by
    dsimp [p]
    exact_mod_cast (show 1 ≤ 2 * q by omega)
  have hmeas : ∀ i ∈ Finset.Icc (m - j) (m + j),
      AEStronglyMeasurable (fun omega : BilateralField d =>
        aux_prefix_bank_maxObs i (m + 1 + j) z (eta N omega) /
          aux_psf_sigma M) (chaosSampleLaw M).toMeasure := by
    intro i _
    exact prefix_eta_bank_aestronglyMeasurable M eta hEta N i (m + 1 + j) z
  let f : ℕ → BilateralField d → ℝ := fun i omega =>
    aux_prefix_bank_maxObs i (m + 1 + j) z (eta N omega) /
      aux_psf_sigma M
  have hsum := eLpNorm_sum_le (μ := (chaosSampleLaw M).toMeasure) (f := f) (s := Finset.Icc (m - j) (m + j)) hp
  have hfun : (∑ i ∈ Finset.Icc (m - j) (m + j), f i) =
      (fun omega => ∑ i ∈ Finset.Icc (m - j) (m + j), f i omega) := by
    funext omega
    simp only [Finset.sum_apply]
  rw [hfun] at hsum
  exact hsum


/-- A nonnegative series with almost-sure pointwise convergence inherits any
uniform bound on its finite partial-sum `Lp` norms. -/
theorem prefix_eLpNorm_tsum_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ℕ → Ω → ℝ) (p B : ENNReal)
    (hf : ∀ j, AEStronglyMeasurable (f j) μ)
    (hsum : ∀ᵐ omega ∂μ, Summable (fun j => f j omega))
    (hbound : ∀ n : ℕ,
      eLpNorm (fun omega => ∑ j ∈ Finset.range n, f j omega) p μ ≤ B) :
    eLpNorm (fun omega => ∑' j : ℕ, f j omega) p μ ≤ B := by
  apply Lp.eLpNorm_le_of_ae_tendsto (u := Filter.atTop) (C := B)
    (f := fun n omega => ∑ j ∈ Finset.range n, f j omega)
    (g := fun omega => ∑' j : ℕ, f j omega)
  · exact Filter.Eventually.of_forall hbound
  · intro n
    have hfun : (∑ j ∈ Finset.range n, f j) =
        (fun omega => ∑ j ∈ Finset.range n, f j omega) := by
      funext omega
      simp only [Finset.sum_apply]
    rw [← hfun]
    exact Finset.aestronglyMeasurable_sum _ (fun j _ => hf j)
  · apply aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (f := fun n omega => ∑ j ∈ Finset.range n, f j omega)
    · intro n
      have hfun : (∑ j ∈ Finset.range n, f j) =
          (fun omega => ∑ j ∈ Finset.range n, f j omega) := by
        funext omega
        simp only [Finset.sum_apply]
      rw [← hfun]
      exact Finset.aestronglyMeasurable_sum _ (fun j _ => hf j)
    · filter_upwards [hsum] with omega hω
      exact hω.hasSum.tendsto_sum_nat
  · filter_upwards [hsum] with omega hω
    exact hω.hasSum.tendsto_sum_nat

end Paper
