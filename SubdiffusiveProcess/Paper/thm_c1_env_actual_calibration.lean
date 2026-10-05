module

public import SubdiffusiveProcess.Paper.calib_side_boundary
public import SubdiffusiveProcess.Paper.calib_weighted_form_data
public import SubdiffusiveProcess.Paper.calibResp_integrable
public import SubdiffusiveProcess.Paper.calibResp
public import SubdiffusiveProcess.Paper.calib_h0_large_cell_bounds
public import SubdiffusiveProcess.Paper.conv_represented_calibration_package
public import SubdiffusiveProcess.Paper.conv_represented_limit_forms_package
public import SubdiffusiveProcess.Paper.conv_represented_joint_grids
public import SubdiffusiveProcess.Paper.thm_c1_env_calibration_core
public import SubdiffusiveProcess.DirichletForm.EnergyMeasureScaling

@[expose] public section

/-! **`thm_c1_env_actual_calibration`.**  For the actual model, on any represented package (the joint package, the
limit forms and the calibration coordinates) every constant `c > 0` with `F = c E` on every cube equals `1`.
The scalar calibration is the existing `aux_thm_c1_envcal_core_env`; its model inputs (weights, weighted forms,
scaling of the energy measures, boundary-response identification) are constructed from the package. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The cell-bound predicate depends only on the cube and the sequence, not on how the cube is presented. -/
theorem aux_thm_c1_env_actual_calibration_cell_bounds_congr {d : ℕ} {z z' : SpatialCoordinates d} {R R' : ℝ} {hR : 0 < R}
    {hR' : 0 < R'} (hz : z = z') (hRR : R = R') {a : ℕ → SpatialCoordinates d → ℝ} {t alpha : ℝ}
    (h : calib_h0_large_cell_bounds z R hR a t alpha) : calib_h0_large_cell_bounds z' R' hR' a t alpha := by
  subst hz; subst hRR; exact h

/-- The exponent conditions of the represented catalogue. -/
theorem aux_thm_c1_env_actual_calibration_exponents {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (envE envF : ℕ → Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ) (E : _root_.SubdiffusiveProcess.Paper.in_J d) (beta0 t0 : ℝ)
    (h : conv_represented_catalogue_grids d hd M H Ω P envE envF z r hr Sspace NE NF alpha eta E beta0 t0) :
    ((d : ℝ) - 1 < t0 ∧ t0 < (d : ℝ)) ∧ 1 / 2 < alpha ∧ alpha < 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, ⟨-, -, hteq⟩, -, -, hE, -⟩ := h
  obtain ⟨⟨ht1, ht2⟩, ⟨ha1, heta, hae⟩, -⟩ := hE
  refine ⟨?_, by linarith, ha1⟩
  rw [← hteq]
  exact ⟨ht1, ht2⟩

/-- **`c = 1` for the actual candidates.** -/
theorem thm_c1_env_actual_calibration
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H),
        M.delta ≤ δ0 →
      ∀ (alpha eta beta t : ℝ),
      ∀ (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ) (hR : ∀ i, 0 < R i)
        (Sspace : ∀ i, ResponseSpace (centeredCube (Z i) (R i) (hR i)))
        (_hcomp : ∀ (z' : SpatialCoordinates d) (r' : ℝ), (∀ c : Fin d, ∃ q : ℚ, z' c = (q : ℝ)) →
          (∃ m : ℤ, r' = (3 : ℝ) ^ m) → ∃ i, Z i = z' ∧ R i = r')
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d) (env : ℕ → Ω → BilateralField d)
        (GNE GNF : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ] DomainL2 (centeredCube (Z i) (R i) (hR i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ] DomainL2 (centeredCube (Z i) (R i) (hR i)))
        (NE NF : ℕ → ℕ),
        conv_represented_joint_grids d hd M H Ω P field env env Z R hR Sspace GNE GNF GE GF NE NF
          alpha eta E beta t →
        conv_represented_limit_forms_package d hd M H Ω P env Z R hR Sspace GE GF NE NF →
        conv_represented_calibration_package d hd M H Ω P env NE NF t alpha →
        ∀ c : ℝ, 0 < c →
          (∀ᵐ omega ∂P, ∀ i : ℕ,
            limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
            ∀ u : DomainL2 (centeredCube (Z i) (R i) (hR i)),
              u ∈ limitFormDomain (GE i omega) →
              (limitFormEnergy (GF i omega) u).toReal =
                c * (limitFormEnergy (GE i omega) u).toReal) →
          c = 1 := by
  obtain ⟨δc, hδc, hcal⟩ := aux_thm_c1_envcal_cal_env d hd E
  refine ⟨δc, hδc, ?_⟩
  intro M H hH hM alpha eta beta t Z R hR Sspace hcomp Ω _ P _ field env GNE GNF GE GF NE NF
    hjoint hforms hcalpkg c hc hprop
  have : NeZero d := ⟨by omega⟩
  have hd0 : 0 < d := by omega
  obtain ⟨e0cat, -, hcat0⟩ := hjoint.2 0
  obtain ⟨⟨ht, htd⟩, halpha, ha1⟩ := aux_thm_c1_env_actual_calibration_exponents hd M H Ω P env env (Z ∘ e0cat) (R ∘ e0cat)
    (fun j => hR (e0cat j)) (fun j => Sspace (e0cat j)) NE NF alpha eta E beta t hcat0
  obtain ⟨⟨hprob, hfm, hfmap, -, hNE, hNF, hMP, henvc, hSsp, hGNd, hGNc⟩, -⟩ := hjoint
  obtain ⟨K0, LE, LF, hinf, hLEc, hLFc, hHc, hcellE, hcellF⟩ := hcalpkg
  -- the calibration cubes are in the family
  have hIdx : ∀ m : ℕ, ∃ i, Z i = 0 ∧ R i = (3 : ℝ) ^ m := by
    intro m
    obtain ⟨i, hi1, hi2⟩ := hcomp 0 ((3 : ℝ) ^ (m : ℤ)) (fun c => ⟨0, by simp⟩) ⟨(m : ℤ), rfl⟩
    exact ⟨i, hi1, by rw [hi2, zpow_natCast]⟩
  choose idx hidxZ hidxR using hIdx
  -- the normalizers and the responses
  let vol : ℕ → ℝ := fun k => (volume (centeredCube (0 : SpatialCoordinates d)
    ((3 : ℝ) ^ (K0 + k)) (pow_pos (zero_lt_three : (0 : ℝ) < 3) (K0 + k)) :
      Set (SpatialCoordinates d))).toReal
  have hvol : ∀ k, 0 < vol k := fun k => aux_thm_c1_envcal_vol_pos _ _ _
  have hintE : ∀ k n, Integrable (fun w => calibResp d hd M (K0 + k) (NE n) (env n w) / vol k) P :=
    fun k n => ((hMP n).1.integrable_comp_of_integrable
      (calibResp_integrable d hd M (K0 + k) (NE n))).div_const _
  have hintF : ∀ k n, Integrable (fun w => calibResp d hd M (K0 + k) (NF n) (env n w) / vol k) P :=
    fun k n => ((hMP n).2.integrable_comp_of_integrable
      (calibResp_integrable d hd M (K0 + k) (NF n))).div_const _
  -- the calibration `cor_37` along both sequences
  choose Poincare hPoincare using fun k : ℕ => centeredCube_killedPoincare (0 : SpatialCoordinates d)
    (pow_pos (zero_lt_three : (0 : ℝ) < 3) k)
  have e0sq := aux_thm_c1_envcal_e0_sq d hd0
  have hcalgen : ∀ (NN : ℕ → ℕ) (hmpN : ∀ n, MeasurePreserving (env n) P (chaosSampleLaw M).toMeasure),
      ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k → ∀ n,
        ∫ w, |calibResp d hd M (K0 + k) (NN n) (env n w) / vol k - 1| ∂P ≤ eps := by
    intro NN hmpN eps heps
    obtain ⟨k0, hk0⟩ := hcal M hM Ω P env hmpN Poincare hPoincare NN
      (fun k n w => calibResp d hd M k (NN n) (env n w))
      (fun k => (volume (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
        (pow_pos (zero_lt_three : (0 : ℝ) < 3) k) : Set (SpatialCoordinates d))).toReal)
      (aux_thm_c1_envcal_e0 d hd0) (fun k => rfl)
      (Eventually.of_forall fun w k n => rfl) eps heps
    refine ⟨k0, fun k hk n => ?_⟩
    have := hk0 (K0 + k) (by omega) n
    rw [← e0sq] at this
    simpa using this
  have hcalE := hcalgen NE (fun n => (hMP n).1)
  have hcalF := hcalgen NF (fun n => (hMP n).2)
  -- the substantive step: `LF k = c * LE k`
  have hscale : ∀ k, ∀ᵐ omega ∂P, LF k omega = c * LE k omega := by
    intro k
    filter_upwards [hforms, hLEc k, hLFc k, hHc, hcellE, hcellF, hprop] with
      omega hf hLE hLF hH hcE hcF hp
    obtain ⟨LEs, LFs, hloc⟩ := hf
    obtain ⟨i, hZi, hRi⟩ : ∃ i, Z i = 0 ∧ R i = (3 : ℝ) ^ (K0 + k + 1) :=
      ⟨idx (K0 + k + 1), hidxZ _, hidxR _⟩
    have hRQm : R i = 3 * (3 : ℝ) ^ (K0 + k) := by rw [hRi, pow_succ]; ring
    have hGE : Tendsto (fun n => volumeResponseOperator (Sspace i)
        (cutoffPositiveCoefficient M H (env n omega) (NE n) (Z i) (hR i))) atTop (𝓝 (GE i omega)) := by
      refine ((LEs i).response_tendsto).congr (fun n => ?_)
      ext f
      rw [(LEs i).response_eq n f, volumeResponseOperator_apply]
    have hGF : Tendsto (fun n => volumeResponseOperator (Sspace i)
        (cutoffPositiveCoefficient M H (env n omega) (NF n) (Z i) (hR i))) atTop (𝓝 (GF i omega)) := by
      refine ((LFs i).response_tendsto).congr (fun n => ?_)
      ext f
      rw [(LFs i).response_eq n f, volumeResponseOperator_apply]
    obtain ⟨E0, G0, hwE, hcoreE0, hLEeq⟩ := calib_side_boundary d hd M H (fun n => env n omega) NE
      (hinf omega) hH (K0 + k) (Z i) (R i) (hR i) hZi hRQm (Sspace i) (hSsp i) (GE i omega) hGE
      (LEs i).bounds (LEs i).form (LEs i).energy_eq (LEs i).core (LEs i).gamma (hloc i).1 t alpha ht
      htd halpha ha1 (aux_thm_c1_env_actual_calibration_cell_bounds_congr hZi.symm (by rw [hRi]; ring) (hcE k)) (LE k omega) hLE
    obtain ⟨F0, GF0, hwF, hcoreF0, hLFeq⟩ := calib_side_boundary d hd M H (fun n => env n omega) NF
      (hinf omega) hH (K0 + k) (Z i) (R i) (hR i) hZi hRQm (Sspace i) (hSsp i) (GF i omega) hGF
      (LFs i).bounds (LFs i).form (LFs i).energy_eq (LFs i).core (LFs i).gamma (hloc i).2 t alpha ht
      htd halpha ha1 (aux_thm_c1_env_actual_calibration_cell_bounds_congr hZi.symm (by rw [hRi]; ring) (hcF k)) (LF k omega) hLF
    obtain ⟨CE, hCE⟩ := (LEs i).core
    obtain ⟨CE0, hCE0⟩ := hcoreE0
    have key := aux_thm_c1_envcal_sInf_scale (Q := centeredCube (Z i) (R i) (hR i))
      (LEs i).form.toClosedForm (LFs i).form.toClosedForm E0.toClosedForm F0.toClosedForm
      (LEs i).gamma (LFs i).gamma G0 GF0
      (fun x => Real.exp (aux_calib_weighted_form_data_G (hinf omega)
        (centeredCube (Z i) (R i) (hR i) : Set (SpatialCoordinates d)) x))
      (GE i omega) (GF i omega) hwE hwF (LEs i).energy_eq (LFs i).energy_eq c hc (hp i)
      (fun hdom hform u hu => (LEs i).gamma.measure_eq_smul_of_form_scale (LFs i).gamma
        (centeredCube (Z i) (R i) (hR i)) hCE hc hdom hform hu)
      (fun hdom hform u hu => G0.measure_eq_smul_of_form_scale GF0
        (centeredCube (Z i) (R i) (hR i)) hCE0 hc hdom hform hu)
      (fun Uc => ContinuousOn Uc (closure (centeredCube (Z i) (R i) (hR i) : Set (SpatialCoordinates d))))
      (fun U Uc => ((U : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube (Z i) (R i) (hR i) : Set (SpatialCoordinates d))] Uc))
      (fun Uc => ∀ x ∈ frontier (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ (K0 + k))
          (pow_pos (zero_lt_three : (0 : ℝ) < 3) (K0 + k)) : Set (SpatialCoordinates d)),
        Uc x = ∑ j : Fin d, aux_thm_c1_envcal_e0 d hd0 j * x j)
      (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ (K0 + k))
        (pow_pos (zero_lt_three : (0 : ℝ) < 3) (K0 + k)) : Set (SpatialCoordinates d))
    rw [hLEeq, hLFeq]
    exact key
  exact aux_thm_c1_envcal_core_env P
    (fun k n w => calibResp d hd M (K0 + k) (NE n) (env n w))
    (fun k n w => calibResp d hd M (K0 + k) (NF n) (env n w)) LE LF vol hvol 1 (one_pow 2)
    hintE hintF hLEc hLFc hcalE hcalF c hc hscale

end SubdiffusiveProcess.Paper
