import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Geometry.CoordinateFold
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.coefficient_physical_identity
import SubdiffusiveProcess.Paper.lem_infrared
import SubdiffusiveProcess.Paper.infrared_characterization_local_lipschitz_majorant
import SubdiffusiveProcess.Paper.finite_negative_layer_log_lipschitz_majorant
import SubdiffusiveProcess.Main.NativeBilateralPotentialSample
import SubdiffusiveProcess.Probability.InfraredCharacterizationUniformExponentialMoment
import SubdiffusiveProcess.Probability.FineLayerMoment
import SubdiffusiveProcess.Probability.OrliczExponentialMoment
import SubdiffusiveProcess.Probability.OrliczFiniteSum
import SubdiffusiveProcess.Probability.NativeCommonScaleLaw
import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments
import SubdiffusiveProcess.CoarseGrainingVocab.OGammaSup
import SubdiffusiveProcess.CoarseGrainingVocab.OGammaSplit
import SubdiffusiveProcess.CoarseGrainingVocab.OGammaToolkit
import SubdiffusiveProcess.CoarseGrainingVocab.ShellSensitivity
import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.LogHomogenizedBound
import Homogenization.Book.Ch04.Theorems.Concentration
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.ContinuousMap.Compact
import SubdiffusiveProcess.Main.InfraredAdmissible

open MeasureTheory Set TopologicalSpace Metric ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper


/-- The absolute value of a zero-layer potential at any point has the same
`Γ₂` scale as at the origin, by stationarity. -/
theorem aux_finite_cutoff_log_abs_majorant_ogamma_eval {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (x : Homogenization.Vec d) :
    SubdiffusiveProcess.OGammaLE (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure 2 M.delta
      (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d => |g x|) := by
  have hT : MeasurePreserving (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate x)
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure :=
    ⟨SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_translate x, M.G1.stationary x⟩
  have h := SubdiffusiveProcess.CoarseGrainingVocab.OGamma.ogammaLE_comp_measurePreserving hT
    (X := fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d => |g 0|)
    ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval
      (0 : Homogenization.Vec d)).abs.aemeasurable)
    (SubdiffusiveProcess.CoarseGrainingVocab.ogammaLE_abs_zeroPotential_at_zero M)
  convert h using 2 with g
  simp [SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate_apply]

/-- Every zero-layer potential evaluation is centred. -/
theorem aux_finite_cutoff_log_abs_majorant_mean_zero {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (x : Homogenization.Vec d) :
    ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, g x
      ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure = 0 := by
  have heval0 : Measurable
      (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d => g (0 : Homogenization.Vec d)) :=
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval 0
  have hevalK : Measurable
      (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => omega 0 (0 : Homogenization.Vec d)) :=
    heval0.comp (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate (d := d) 0)
  have hzero : ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, g (0 : Homogenization.Vec d)
      ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure = 0 := by
    have hmap := SubdiffusiveProcess.CoarseGrainingVocab.map_potentialCoordinate_apply_eq_zero M 0
      (0 : Homogenization.Vec d)
    calc ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, g (0 : Homogenization.Vec d)
          ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure
        = ∫ z : ℝ, z ∂Measure.map
            (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d => g (0 : Homogenization.Vec d))
            (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure :=
          (integral_map heval0.aemeasurable measurable_id.aestronglyMeasurable).symm
      _ = ∫ z : ℝ, z ∂Measure.map
            (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
              omega 0 (0 : Homogenization.Vec d)) M.P.toMeasure := by rw [hmap]
      _ = ∫ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
            omega 0 (0 : Homogenization.Vec d) ∂M.P.toMeasure :=
          integral_map hevalK.aemeasurable measurable_id.aestronglyMeasurable
      _ = 0 := SubdiffusiveProcess.CoarseGrainingVocab.integral_potentialCoordinate_apply_eq_zero M 0 0
  have hT : Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate x)
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure =
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := M.G1.stationary x
  calc ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, g x
        ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure
      = ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate x g) (0 : Homogenization.Vec d)
          ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
        refine integral_congr_ae ?_
        filter_upwards with g
        simp [SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate_apply]
    _ = ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, g (0 : Homogenization.Vec d)
          ∂Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate x)
            (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure :=
        (integral_map
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_translate x).aemeasurable
          heval0.aestronglyMeasurable).symm
    _ = 0 := by rw [hT]; exact hzero

/-- Exponential moment from a `Γ₂` Orlicz bound on a nonnegative observable. -/
theorem aux_finite_cutoff_log_abs_majorant_exp_of_ogamma
    {Om : Type*} [MeasurableSpace Om] (mu : Measure Om) [IsProbabilityMeasure mu]
    (X : Om → ℝ) (hXm : Measurable X) (hX0 : ∀ om, 0 ≤ X om)
    (A lam : ℝ) (hA : 0 < A) (hlam : 0 ≤ lam)
    (h : SubdiffusiveProcess.OGammaLE mu 2 A X) :
    Integrable (fun om => Real.exp (lam * X om)) mu ∧
      ∫ om, Real.exp (lam * X om) ∂mu ≤ 2 * Real.exp (A ^ 2 * lam ^ 2 / 4) := by
  refine SubdiffusiveProcess.orlicz_exp_linear_integrable_integral_le mu X A lam hXm hX0
    hA hlam ?_
  obtain ⟨hint, hle⟩ := h
  have hfun : (fun om => Real.exp ((A⁻¹ * max (X om) 0) ^ (2 : ℝ))) =
      fun om => Real.exp ((X om / A) ^ (2 : ℕ)) := by
    funext om
    rw [max_eq_left (hX0 om), inv_mul_eq_div, ← Real.rpow_natCast ((X om) / A) 2]
    norm_num
  rw [hfun] at hint hle
  have hnn : 0 ≤ᵐ[mu] fun om => Real.exp ((X om / A) ^ (2 : ℕ)) :=
    Filter.Eventually.of_forall fun om => (Real.exp_pos _).le
  calc (∫⁻ om, ENNReal.ofReal (Real.exp ((X om / A) ^ (2 : ℕ))) ∂mu)
      = ENNReal.ofReal (∫ om, Real.exp ((X om / A) ^ (2 : ℕ)) ∂mu) :=
        (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hle
    _ = 2 := by norm_num


/-- `OGammaLE` transports backwards along any measure-preserving map. -/
theorem aux_finite_cutoff_log_abs_majorant_ogamma_map
    {Om Om' : Type*} [MeasurableSpace Om] [MeasurableSpace Om']
    {mu : Measure Om} {mu' : Measure Om'} {T : Om' → Om}
    (hTm : Measurable T) (hmap : Measure.map T mu' = mu)
    {sigma A : ℝ} {X : Om → ℝ} (hX : Measurable X)
    (h : SubdiffusiveProcess.OGammaLE mu sigma A X) :
    SubdiffusiveProcess.OGammaLE mu' sigma A (fun w => X (T w)) := by
  obtain ⟨hint, hle⟩ := h
  have hmeas : AEStronglyMeasurable
      (fun om => Real.exp ((A⁻¹ * max (X om) 0) ^ sigma)) (Measure.map T mu') := by
    rw [hmap]
    exact (((measurable_const.mul (hX.max measurable_const)).pow_const
      sigma).exp).aestronglyMeasurable
  constructor
  · have hI : Integrable (fun om => Real.exp ((A⁻¹ * max (X om) 0) ^ sigma))
        (Measure.map T mu') := by rw [hmap]; exact hint
    exact (integrable_map_measure hmeas hTm.aemeasurable).mp hI
  · calc (∫ w, Real.exp ((A⁻¹ * max (X (T w)) 0) ^ sigma) ∂mu')
        = ∫ om, Real.exp ((A⁻¹ * max (X om) 0) ^ sigma) ∂(Measure.map T mu') :=
          (integral_map hTm.aemeasurable hmeas).symm
      _ ≤ 2 := by rw [hmap]; exact hle

/-- One bilateral layer evaluation has the `Γ₂` scale `δ`. -/
theorem aux_finite_cutoff_log_abs_majorant_layer_ogamma {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℤ) (x : Homogenization.Vec d) :
    SubdiffusiveProcess.OGammaLE (Measure.infinitePi (fun _ : ℤ =>
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)) 2 M.delta
      (fun w : NativeBilateralPotentialSample d => |(w j) x|) := by
  have hmap : Measure.map (fun w : NativeBilateralPotentialSample d => w j)
      (Measure.infinitePi (fun _ : ℤ =>
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)) =
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure :=
    Measure.infinitePi_map_eval _ j
  exact aux_finite_cutoff_log_abs_majorant_ogamma_map
    (T := fun w : NativeBilateralPotentialSample d => w j)
    (measurable_pi_apply j) hmap
    ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval x).abs)
    (aux_finite_cutoff_log_abs_majorant_ogamma_eval M x)

/-- One bilateral layer evaluation is centred. -/
theorem aux_finite_cutoff_log_abs_majorant_layer_mean_zero {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j : ℤ) (x : Homogenization.Vec d) :
    ∫ w : NativeBilateralPotentialSample d, (w j) x
      ∂(Measure.infinitePi (fun _ : ℤ =>
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)) = 0 := by
  have heval : Measurable
      (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d => g x) :=
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval x
  calc ∫ w : NativeBilateralPotentialSample d, (w j) x
        ∂(Measure.infinitePi (fun _ : ℤ =>
          (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure))
      = ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, g x
          ∂(Measure.map (fun w : NativeBilateralPotentialSample d => w j)
            (Measure.infinitePi (fun _ : ℤ =>
              (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure))) :=
        (integral_map (φ := fun w : NativeBilateralPotentialSample d => w j)
          (f := fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d => g x)
          (measurable_pi_apply j).aemeasurable
          heval.aestronglyMeasurable).symm
    _ = 0 := by
        rw [Measure.infinitePi_map_eval]
        exact aux_finite_cutoff_log_abs_majorant_mean_zero M x


theorem aux_finite_cutoff_log_abs_majorant_gamma_const_pos :
    0 < Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2 := by
  have h : 0 < Homogenization.IndependentSums.gammaSigmaExpRegimeConst 2 := by
    dsimp [Homogenization.IndependentSums.gammaSigmaExpRegimeConst]
    exact lt_of_lt_of_le (mul_pos (by positivity)
      (Homogenization.IndependentSums.gammaMomentConst_pos (by norm_num)))
      (le_max_left _ _)
  rw [Homogenization.Book.Ch04.gammaSigmaIndependentSumConst]
  norm_num [Homogenization.Book.Ch04.gammaSigmaExpRegimeEndpointConst,
    Homogenization.IndependentSums.gammaSigmaExpRegimeEndpointConst]
  linarith

/-- The finitely many negative bilateral layers, evaluated at arbitrary points,
are independent. -/
theorem aux_finite_cutoff_log_abs_majorant_indep {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (c : ℕ → Homogenization.Vec d) :
    iIndepFun (fun (j : ℕ) (w : NativeBilateralPotentialSample d) => (w (-(j : ℤ))) (c j))
      (Measure.infinitePi (fun _ : ℤ =>
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)) := by
  classical
  have h1 : iIndepFun
      (fun (i : ℤ) (w : NativeBilateralPotentialSample d) => (w i) (c (Int.toNat (-i))))
      (Measure.infinitePi (fun _ : ℤ =>
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)) :=
    ProbabilityTheory.iIndepFun_infinitePi
      (fun i => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval (c (Int.toNat (-i))))
  have hinj : Function.Injective (fun j : ℕ => -(j : ℤ)) := by
    intro a b hab
    simpa using hab
  have h2 := h1.precomp hinj
  have h3 : (fun (j : ℕ) (w : NativeBilateralPotentialSample d) =>
        (w (-(j : ℤ))) (c (Int.toNat (-(-(j : ℤ)))))) =
      fun (j : ℕ) (w : NativeBilateralPotentialSample d) => (w (-(j : ℤ))) (c j) := by
    funext j w
    simp
  rw [h3] at h2
  exact h2


/-- The centred sum of the `N+1` negative layers at arbitrary points has the
central-limit `Γ₂` scale `δ √(N+1)`. -/
theorem aux_finite_cutoff_log_abs_majorant_sum_ogamma {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (c : ℕ → Homogenization.Vec d) :
    SubdiffusiveProcess.OGammaLE (Measure.infinitePi (fun _ : ℤ =>
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)) 2
      ((6 * Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2 *
          ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * (M.delta * Real.sqrt ((N : ℝ) + 1)))
      (fun w : NativeBilateralPotentialSample d =>
        |∑ j ∈ Finset.range (N + 1), (w (-(j : ℤ))) (c j)|) := by
  classical
  set mu : Measure (NativeBilateralPotentialSample d) :=
    Measure.infinitePi (fun _ : ℤ =>
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure) with hmu
  set X : ℕ → NativeBilateralPotentialSample d → ℝ :=
    fun j w => (w (-(j : ℤ))) (c j) with hX
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hlog2 : (0 : ℝ) < 1 + Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith
  set L : ℝ := (1 + Real.log 2) ^ (2 : ℝ)⁻¹ with hL
  have hLpos : 0 < L := Real.rpow_pos_of_pos hlog2 _
  have hK : 0 < L * M.delta := mul_pos hLpos hdelta
  have hXmeas : ∀ j, Measurable (X j) := by
    intro j
    exact (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval (c j)).comp
      (measurable_pi_apply (-(j : ℤ)))
  have hbig : ∀ j ∈ Finset.range (N + 1),
      Homogenization.Book.Ch04.IsBigO mu (Homogenization.Book.Ch04.gammaSigma 2)
        (X j) (L * M.delta) := by
    intro j _
    have h0 : SubdiffusiveProcess.OGammaLE mu 2 M.delta (fun w => |X j w|) :=
      aux_finite_cutoff_log_abs_majorant_layer_ogamma M (-(j : ℤ)) (c j)
    have h := SubdiffusiveProcess.OGammaBridge.isBigO_gammaSigma_of_ogammaLE
      (μ := mu) (σ := 2) (A := M.delta) (X := fun w => |X j w|)
      (by norm_num) hdelta (fun _ => abs_nonneg _) h0
    simpa [Homogenization.IndependentSums.IsBigO, hL] using h
  have hzero : ∀ j ∈ Finset.range (N + 1), ∫ w, X j w ∂mu = 0 := by
    intro j _
    exact aux_finite_cutoff_log_abs_majorant_layer_mean_zero M (-(j : ℤ)) (c j)
  have hne : (Finset.range (N + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩
  have hsum := Homogenization.Book.Ch04.isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
    (μ := mu) (X := X) (s := Finset.range (N + 1)) (σ := 2) (K := L * M.delta)
    (aux_finite_cutoff_log_abs_majorant_indep M c) hXmeas hne (by norm_num) (by norm_num)
    hK hbig hzero
  have hcard : Real.sqrt ((Finset.range (N + 1)).card : ℝ) = Real.sqrt ((N : ℝ) + 1) := by
    rw [Finset.card_range]; norm_num
  rw [hcard] at hsum
  set B : ℝ := Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2 *
    Real.sqrt ((N : ℝ) + 1) * (L * M.delta) with hB
  have hBpos : 0 < B := by
    have h1 : 0 < Real.sqrt ((N : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    exact mul_pos (mul_pos aux_finite_cutoff_log_abs_majorant_gamma_const_pos h1) hK
  have habs : Homogenization.Book.Ch04.IsBigO mu (Homogenization.Book.Ch04.gammaSigma 2)
      (fun w => |∑ j ∈ Finset.range (N + 1), X j w|) B := by
    simpa [Homogenization.IndependentSums.IsBigO] using hsum
  have hmeasS : AEMeasurable
      (fun w : NativeBilateralPotentialSample d =>
        |∑ j ∈ Finset.range (N + 1), X j w|) mu :=
    ((Finset.measurable_sum _ (fun j _ => hXmeas j)).abs).aemeasurable
  have hres := SubdiffusiveProcess.CoarseGrainingVocab.OGamma.ogammaLE_of_isBigO_gammaTwo_aemeasurable
    (mu := mu) (A := B) hBpos hmeasS habs
  have hconst : 6 * B =
      (6 * Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2 * L) *
        (M.delta * Real.sqrt ((N : ℝ) + 1)) := by
    rw [hB]; ring
  rw [hconst] at hres
  exact hres


/-- Union bound: the exponential moment of a finite maximum of nonnegative
observables with a common `Γ₂` scale costs a factor of the cardinality. -/
theorem aux_finite_cutoff_log_abs_majorant_sup_exp
    {Om : Type*} [MeasurableSpace Om] (mu : Measure Om) [IsProbabilityMeasure mu]
    {iota : Type*} (S : Finset iota) (hS : S.Nonempty) (f : iota → Om → ℝ)
    (A lam : ℝ) (hA : 0 < A) (hlam : 0 ≤ lam)
    (hmeas : ∀ q, Measurable (f q)) (hnn : ∀ q w, 0 ≤ f q w)
    (h : ∀ q ∈ S, SubdiffusiveProcess.OGammaLE mu 2 A (f q)) :
    Integrable (fun w => Real.exp (lam * S.sup' hS (fun q => f q w))) mu ∧
      ∫ w, Real.exp (lam * S.sup' hS (fun q => f q w)) ∂mu ≤
        (S.card : ℝ) * (2 * Real.exp (A ^ 2 * lam ^ 2 / 4)) := by
  classical
  have hterm : ∀ q ∈ S, Integrable (fun w => Real.exp (lam * f q w)) mu ∧
      ∫ w, Real.exp (lam * f q w) ∂mu ≤ 2 * Real.exp (A ^ 2 * lam ^ 2 / 4) := by
    intro q hq
    exact aux_finite_cutoff_log_abs_majorant_exp_of_ogamma mu (f q) (hmeas q)
      (hnn q) A lam hA hlam (h q hq)
  have hsumint : Integrable (fun w => ∑ q ∈ S, Real.exp (lam * f q w)) mu :=
    integrable_finset_sum S (fun q hq => (hterm q hq).1)
  have hle : ∀ w, Real.exp (lam * S.sup' hS (fun q => f q w)) ≤
      ∑ q ∈ S, Real.exp (lam * f q w) := by
    intro w
    obtain ⟨q0, hq0S, hq0⟩ := Finset.exists_mem_eq_sup' hS (fun q => f q w)
    rw [hq0]
    exact Finset.single_le_sum (f := fun q => Real.exp (lam * f q w))
      (fun q _ => (Real.exp_pos _).le) hq0S
  have hmeasS : Measurable (fun w => Real.exp (lam * S.sup' hS (fun q => f q w))) := by
    have hs : Measurable (fun w => S.sup' hS (fun q => f q w)) := by
      have h0 : Measurable (S.sup' hS f) :=
        Finset.measurable_sup' hS (fun q _ => hmeas q)
      have h1 : (S.sup' hS f) = fun w => S.sup' hS (fun q => f q w) := by
        funext w; exact Finset.sup'_apply hS f w
      rwa [h1] at h0
    exact (measurable_const.mul hs).exp
  have hint : Integrable (fun w => Real.exp (lam * S.sup' hS (fun q => f q w))) mu := by
    refine hsumint.mono' hmeasS.aestronglyMeasurable ?_
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hle w
  refine ⟨hint, ?_⟩
  calc ∫ w, Real.exp (lam * S.sup' hS (fun q => f q w)) ∂mu
      ≤ ∫ w, ∑ q ∈ S, Real.exp (lam * f q w) ∂mu :=
        integral_mono hint hsumint (fun w => hle w)
    _ = ∑ q ∈ S, ∫ w, Real.exp (lam * f q w) ∂mu :=
        integral_finset_sum S (fun q hq => (hterm q hq).1)
    _ ≤ ∑ _q ∈ S, (2 * Real.exp (A ^ 2 * lam ^ 2 / 4)) :=
        Finset.sum_le_sum (fun q hq => (hterm q hq).2)
    _ = (S.card : ℝ) * (2 * Real.exp (A ^ 2 * lam ^ 2 / 4)) := by
        rw [Finset.sum_const, nsmul_eq_mul]


/-- The `∫⁻`-form of a `Γ₂` Orlicz bound for a nonnegative observable. -/
theorem aux_finite_cutoff_log_abs_majorant_orlicz_lint
    {Om : Type*} [MeasurableSpace Om] (mu : Measure Om)
    (X : Om → ℝ) (hX0 : ∀ om, 0 ≤ X om) (A : ℝ)
    (h : SubdiffusiveProcess.OGammaLE mu 2 A X) :
    (∫⁻ om, ENNReal.ofReal (Real.exp ((X om / A) ^ (2 : ℕ))) ∂mu) ≤ 2 := by
  obtain ⟨hint, hle⟩ := h
  have hfun : (fun om => Real.exp ((A⁻¹ * max (X om) 0) ^ (2 : ℝ))) =
      fun om => Real.exp ((X om / A) ^ (2 : ℕ)) := by
    funext om
    rw [max_eq_left (hX0 om), inv_mul_eq_div, ← Real.rpow_natCast ((X om) / A) 2]
    norm_num
  rw [hfun] at hint hle
  have hnn : 0 ≤ᵐ[mu] fun om => Real.exp ((X om / A) ^ (2 : ℕ)) :=
    Filter.Eventually.of_forall fun om => (Real.exp_pos _).le
  calc (∫⁻ om, ENNReal.ofReal (Real.exp ((X om / A) ^ (2 : ℕ))) ∂mu)
      = ENNReal.ofReal (∫ om, Real.exp ((X om / A) ^ (2 : ℕ)) ∂mu) :=
        (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hle
    _ = 2 := by norm_num

/-- Orlicz triangle inequality for a positively weighted finite sum of
nonnegative observables sharing one `Γ₂` scale. -/
theorem aux_finite_cutoff_log_abs_majorant_weighted_sum_orlicz
    {Om : Type*} [MeasurableSpace Om] (mu : Measure Om) [IsProbabilityMeasure mu]
    (N : ℕ) (f : ℕ → Om → ℝ) (A : ℝ) (hA : 0 < A) (wt : ℕ → ℝ) (hw : ∀ j, 0 < wt j)
    (hmeas : ∀ j, Measurable (f j)) (hnn : ∀ j x, 0 ≤ f j x)
    (h : ∀ j ∈ Finset.range (N + 1), SubdiffusiveProcess.OGammaLE mu 2 A (f j))
    (Atot : ℝ) (hAtot : (∑ j ∈ Finset.range (N + 1), wt j) * A ≤ Atot) :
    (∫⁻ x, ENNReal.ofReal (Real.exp
        (((∑ j ∈ Finset.range (N + 1), wt j * f j x) / Atot) ^ (2 : ℕ))) ∂mu) ≤ 2 := by
  classical
  have hne : (Finset.range (N + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩
  have hbase := SubdiffusiveProcess.lintegral_exp_sq_finset_sum_le mu
    (Finset.range (N + 1)) (fun j x => wt j * f j x) (fun j => wt j * A) hne
    (fun j _ => ((measurable_const.mul (hmeas j))).aestronglyMeasurable)
    (fun j _ => Filter.Eventually.of_forall
      (fun x => mul_nonneg (hw j).le (hnn j x)))
    (fun j _ => mul_pos (hw j) hA)
    (fun j hj => by
      have hfun : ∀ x, wt j * f j x / (wt j * A) = f j x / A := by
        intro x
        rw [mul_div_mul_left _ _ (ne_of_gt (hw j))]
      show (∫⁻ x, ENNReal.ofReal (Real.exp
        ((wt j * f j x / (wt j * A)) ^ (2 : ℕ))) ∂mu) ≤ 2
      simp only [hfun]
      exact aux_finite_cutoff_log_abs_majorant_orlicz_lint mu (f j) (hnn j) A (h j hj))
  have hsumA : (∑ j ∈ Finset.range (N + 1), wt j * A) =
      (∑ j ∈ Finset.range (N + 1), wt j) * A := by
    rw [Finset.sum_mul]
  rw [hsumA] at hbase
  have hsumpos : 0 < (∑ j ∈ Finset.range (N + 1), wt j) * A :=
    mul_pos (Finset.sum_pos (fun j _ => hw j) hne) hA
  have hX0 : ∀ x, 0 ≤ ∑ j ∈ Finset.range (N + 1), wt j * f j x := by
    intro x
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hw j).le (hnn j x))
  refine le_trans (lintegral_mono (fun x => ?_)) hbase
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hdiv : (∑ j ∈ Finset.range (N + 1), wt j * f j x) / Atot ≤
      (∑ j ∈ Finset.range (N + 1), wt j * f j x) /
        ((∑ j ∈ Finset.range (N + 1), wt j) * A) :=
    div_le_div_of_nonneg_left (hX0 x) hsumpos hAtot
  have h1 : 0 ≤ (∑ j ∈ Finset.range (N + 1), wt j * f j x) / Atot :=
    div_nonneg (hX0 x) (le_trans hsumpos.le hAtot)
  exact pow_le_pow_left₀ h1 hdiv 2


/-- The translated unit-cube `C^{1,1}` observable has the `Γ₂` scale `δ` at every
centre. -/
theorem aux_finite_cutoff_log_abs_majorant_translate_ogamma {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (a : Homogenization.Vec d) :
    SubdiffusiveProcess.OGammaLE (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure 2 M.delta
      (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate a g)) := by
  refine aux_finite_cutoff_log_abs_majorant_ogamma_map
    (T := SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate a)
    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_translate a)
    (M.G1.stationary a)
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_measurable ?_
  exact M.G2.regularity_expectation

/-- The shell-cover maximum of translated observables, which dominates the
Lipschitz constant of a layer on a large ball, has `Γ₂` scale
`δ √(5 (1 + log(2·card)))`. -/
theorem aux_finite_cutoff_log_abs_majorant_lip_ogamma {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (q : ℤ) :
    SubdiffusiveProcess.OGammaLE (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure 2
      (M.delta * Real.sqrt (5 * (1 + Real.log
        (2 * ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d q).card : ℝ)))))
      (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d q).sup'
          (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d q)
          (fun a => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
              (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g))) := by
  classical
  have hmeas : ∀ a : Fin d → ℤ, Measurable
      (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g)) := by
    intro a
    exact SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_measurable.comp
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_translate _)
  have hsupmeas : Measurable
      (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d q).sup'
          (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d q)
          (fun a => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
              (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g))) := by
    have h0 : Measurable ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d q).sup'
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d q)
        (fun a g => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g))) :=
      Finset.measurable_sup' _ (fun a _ => hmeas a)
    have h1 : ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d q).sup'
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d q)
        (fun a g => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g))) =
        fun g => (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d q).sup'
          (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d q)
          (fun a => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
              (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g)) := by
      funext g
      exact Finset.sup'_apply _ _ g
    rwa [h1] at h0
  exact SubdiffusiveProcess.CoarseGrainingVocab.OGamma.ogammaLE_sup'_log
    (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d q)
    M.shellPrefix.delta_pos hsupmeas.aemeasurable
    (fun a _ => aux_finite_cutoff_log_abs_majorant_translate_ogamma M
      (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a))


/-- Log-cardinality of the shell cover. -/
theorem aux_finite_cutoff_log_abs_majorant_card_log (d : ℕ) (q : ℤ) :
    Real.log (2 * ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d q).card : ℝ)) ≤
      Real.log 2 + (d : ℝ) * (((q + 1).toNat : ℝ) + 1) * Real.log 3 := by
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  set s : ℕ := (q + 1).toNat with hs
  have hcard : (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d q).card
      = (2 * (3 : ℕ) ^ s + 1) ^ d := by
    rw [SubdiffusiveProcess.CoarseGrainingVocab.card_shellCoverShifts,
      SubdiffusiveProcess.CoarseGrainingVocab.shellCoverRadius]
  have h3s : (1 : ℝ) ≤ (3 : ℝ) ^ s := one_le_pow₀ (by norm_num)
  have hpos : (0 : ℝ) < (2 * (3 : ℝ) ^ s + 1) := by positivity
  have hlog : Real.log (2 * (3 : ℝ) ^ s + 1) ≤ ((s : ℝ) + 1) * Real.log 3 := by
    have hb : (2 * (3 : ℝ) ^ s + 1) ≤ (3 : ℝ) ^ (s + 1) := by
      rw [pow_succ]; nlinarith [h3s]
    have hlg := Real.log_le_log hpos hb
    rwa [Real.log_pow, Nat.cast_add, Nat.cast_one] at hlg
  have hcast : ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d q).card : ℝ)
      = (2 * (3 : ℝ) ^ s + 1) ^ d := by
    rw [hcard]; push_cast; ring
  rw [hcast, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg d : (0 : ℝ) ≤ (d : ℝ))
  have hfin : (d : ℝ) * Real.log (2 * (3 : ℝ) ^ s + 1) ≤
      (d : ℝ) * (((s : ℝ) + 1) * Real.log 3) := this
  push_cast at hfin ⊢
  nlinarith [hfin]

/-- One uniform `Γ₂` scale for all the `N+1` layer Lipschitz observables. -/
theorem aux_finite_cutoff_log_abs_majorant_lip_scale (d Q0 N j : ℕ) (hj : j ≤ N) :
    5 * (1 + Real.log (2 *
        ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((j : ℤ) + (Q0 : ℤ))).card : ℝ))) ≤
      (5 * (1 + Real.log 2 + (d : ℝ) * ((Q0 : ℝ) + 3) * Real.log 3)) * ((N : ℝ) + 1) := by
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcard := aux_finite_cutoff_log_abs_majorant_card_log d ((j : ℤ) + (Q0 : ℤ))
  have htoNat : (((j : ℤ) + (Q0 : ℤ) + 1).toNat : ℝ) = (j : ℝ) + (Q0 : ℝ) + 1 := by
    have : ((j : ℤ) + (Q0 : ℤ) + 1).toNat = j + Q0 + 1 := by omega
    rw [this]; push_cast; ring
  rw [htoNat] at hcard
  have hjN : (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hj
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hQ0 : (0 : ℝ) ≤ (Q0 : ℝ) := Nat.cast_nonneg Q0
  nlinarith [mul_nonneg hd0 hlog3.le, mul_nonneg (mul_nonneg hd0 hQ0) hlog3.le,
    mul_nonneg (mul_nonneg hd0 hN0) hlog3.le, hcard]

/-- The geometric weights of the oscillation majorant sum to at most `3/2`. -/
theorem aux_finite_cutoff_log_abs_majorant_weight_sum (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (j : ℤ) * (3 : ℝ) ^ (-(N : ℤ))) ≤ 3 / 2 := by
  have hpow : (0 : ℝ) < (3 : ℝ) ^ (N : ℕ) := by positivity
  have h2 : (∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (j : ℤ) * (3 : ℝ) ^ (-(N : ℤ))) =
      (∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ j) * ((3 : ℝ) ^ (N : ℕ))⁻¹ := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [zpow_natCast, zpow_neg, zpow_natCast]
  rw [h2]
  have h1 : (∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ j) = ((3 : ℝ) ^ (N + 1) - 1) / 2 := by
    rw [geom_sum_eq (by norm_num : (3 : ℝ) ≠ 1) (N + 1)]
    norm_num
  rw [h1, pow_succ]
  have key : ((3 : ℝ) ^ N * 3 - 1) / 2 * ((3 : ℝ) ^ N)⁻¹ = 3 / 2 - ((3 : ℝ) ^ N)⁻¹ / 2 := by
    field_simp
  rw [key]
  have hinv : 0 < ((3 : ℝ) ^ N)⁻¹ := by positivity
  linarith


/-- The rescaled shell cover is a `3^{-N}`-net of any fixed ball. -/
theorem aux_finite_cutoff_log_abs_majorant_grid {d : ℕ} (N Q1 : ℕ)
    (z : SpatialCoordinates d) (rho : ℝ)
    (hQ1 : ‖z‖ + rho < (3 : ℝ) ^ (Q1 : ℕ) / 2)
    (x : SpatialCoordinates d) (hx : x ∈ Metric.closedBall z rho) :
    ∃ q ∈ SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((N : ℤ) + (Q1 : ℤ)),
      dist x ((3 : ℝ) ^ (-(N : ℤ)) • SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter q) ≤
        (3 : ℝ) ^ (-(N : ℤ)) := by
  have hpowN : (0 : ℝ) < (3 : ℝ) ^ (N : ℤ) := by positivity
  have hxz : ‖x - z‖ ≤ rho := by
    have := Metric.mem_closedBall.mp hx
    rwa [dist_eq_norm] at this
  have hxnorm : ‖x‖ ≤ ‖z‖ + rho := by
    have : ‖x‖ ≤ ‖z‖ + ‖x - z‖ := by
      calc ‖x‖ = ‖z + (x - z)‖ := by rw [add_sub_cancel]
        _ ≤ ‖z‖ + ‖x - z‖ := norm_add_le _ _
    linarith
  set y : SpatialCoordinates d := (3 : ℝ) ^ (N : ℤ) • x with hy
  have hyi : ∀ i, |y i| < 1 / 2 * (3 : ℝ) ^ ((N : ℤ) + (Q1 : ℤ)) := by
    intro i
    have hxi : |x i| ≤ ‖z‖ + rho := le_trans (by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm x i) hxnorm
    have hyiv : y i = (3 : ℝ) ^ (N : ℤ) * x i := rfl
    rw [hyiv, abs_mul, abs_of_pos hpowN]
    have hlt : |x i| < (3 : ℝ) ^ (Q1 : ℕ) / 2 := lt_of_le_of_lt hxi hQ1
    have hmul := mul_lt_mul_of_pos_left hlt hpowN
    calc (3 : ℝ) ^ (N : ℤ) * |x i| < (3 : ℝ) ^ (N : ℤ) * ((3 : ℝ) ^ (Q1 : ℕ) / 2) := hmul
      _ = 1 / 2 * (3 : ℝ) ^ ((N : ℤ) + (Q1 : ℤ)) := by
          have hsplit : (3 : ℝ) ^ ((N : ℤ) + (Q1 : ℤ)) =
              (3 : ℝ) ^ (N : ℤ) * (3 : ℝ) ^ (Q1 : ℕ) := by
            rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast (3 : ℝ) Q1]
          rw [hsplit]; ring
  have hymem : y ∈ Homogenization.openCubeSet
      (Homogenization.originCube d ((N : ℤ) + (Q1 : ℤ))) := by
    rw [Homogenization.mem_openCubeSet_originCube_iff]
    intro i
    have := abs_lt.mp (hyi i)
    constructor
    · linarith [this.1]
    · linarith [this.2]
  obtain ⟨q, hq, hmem⟩ := SubdiffusiveProcess.CoarseGrainingVocab.exists_shellCoverShift_mem hymem
  refine ⟨q, hq, ?_⟩
  rw [Homogenization.mem_translateSet_iff_sub_mem,
    Homogenization.mem_openCubeSet_originCube_iff] at hmem
  have hsub : ‖y - SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter q‖ ≤ 1 / 2 := by
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr ?_
    intro i
    have h := hmem i
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := h.1; simp only [zpow_zero] at this; linarith
    · have := h.2; simp only [zpow_zero] at this; linarith
  have hxy : x - (3 : ℝ) ^ (-(N : ℤ)) • SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter q =
      (3 : ℝ) ^ (-(N : ℤ)) • (y - SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter q) := by
    rw [smul_sub, hy, smul_smul, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    simp
  rw [dist_eq_norm, hxy, norm_smul]
  have hnn : ‖(3 : ℝ) ^ (-(N : ℤ))‖ = (3 : ℝ) ^ (-(N : ℤ)) := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hnn]
  calc (3 : ℝ) ^ (-(N : ℤ)) * ‖y - SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter q‖
      ≤ (3 : ℝ) ^ (-(N : ℤ)) * (1 / 2) := by
        exact mul_le_mul_of_nonneg_left hsub (by positivity)
    _ ≤ (3 : ℝ) ^ (-(N : ℤ)) := by
        have : (0 : ℝ) < (3 : ℝ) ^ (-(N : ℤ)) := by positivity
        linarith


/-- Weighted arithmetic–geometric mean split of an exponential of a triple sum. -/
theorem aux_finite_cutoff_log_abs_majorant_amgm3
    {Om : Type*} [MeasurableSpace Om] (mu : Measure Om) (t : ℝ)
    (A B C : Om → ℝ) (hAm : Measurable A) (hBm : Measurable B) (hCm : Measurable C)
    (ha : Integrable (fun w => Real.exp ((2 * t) * A w)) mu)
    (hb : Integrable (fun w => Real.exp ((4 * t) * B w)) mu)
    (hc : Integrable (fun w => Real.exp ((4 * t) * C w)) mu)
    (Ba Bb Bc : ℝ)
    (hA : (∫ w, Real.exp ((2 * t) * A w) ∂mu) ≤ Ba)
    (hB : (∫ w, Real.exp ((4 * t) * B w) ∂mu) ≤ Bb)
    (hC : (∫ w, Real.exp ((4 * t) * C w) ∂mu) ≤ Bc) :
    Integrable (fun w => Real.exp (t * (A w + B w + C w))) mu ∧
      (∫ w, Real.exp (t * (A w + B w + C w)) ∂mu) ≤ Ba + Bb + Bc := by
  have hsq : ∀ (a : ℝ), Real.exp ((2 * t) * a) = Real.exp (t * a) ^ 2 := by
    intro a
    rw [← Real.exp_nat_mul]
    ring_nf
  have hqu : ∀ (a : ℝ), Real.exp ((4 * t) * a) = Real.exp (t * a) ^ 4 := by
    intro a
    rw [← Real.exp_nat_mul]
    ring_nf
  have hpt : ∀ w, Real.exp (t * (A w + B w + C w)) ≤
      Real.exp ((2 * t) * A w) / 2 + Real.exp ((4 * t) * B w) / 4 +
        Real.exp ((4 * t) * C w) / 4 := by
    intro w
    have hprod : Real.exp (t * (A w + B w + C w)) =
        Real.exp (t * A w) * Real.exp (t * B w) * Real.exp (t * C w) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [hprod, hsq (A w), hqu (B w), hqu (C w)]
    have hu : 0 < Real.exp (t * A w) := Real.exp_pos _
    have hv : 0 < Real.exp (t * B w) := Real.exp_pos _
    have hw : 0 < Real.exp (t * C w) := Real.exp_pos _
    nlinarith [sq_nonneg (Real.exp (t * A w) - Real.exp (t * B w) * Real.exp (t * C w)),
      sq_nonneg (Real.exp (t * B w) ^ 2 - Real.exp (t * C w) ^ 2),
      sq_nonneg (Real.exp (t * B w) * Real.exp (t * C w)), hu.le, hv.le, hw.le]
  have hmaj : Integrable (fun w => Real.exp ((2 * t) * A w) / 2 +
      Real.exp ((4 * t) * B w) / 4 + Real.exp ((4 * t) * C w) / 4) mu :=
    ((ha.div_const 2).add (hb.div_const 4)).add (hc.div_const 4)
  have hmeas : Measurable (fun w => Real.exp (t * (A w + B w + C w))) :=
    (measurable_const.mul ((hAm.add hBm).add hCm)).exp
  have hint : Integrable (fun w => Real.exp (t * (A w + B w + C w))) mu := by
    refine hmaj.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hpt w
  refine ⟨hint, ?_⟩
  have hBa : 0 ≤ Ba := le_trans (integral_nonneg (fun w => (Real.exp_pos _).le)) hA
  have hBb : 0 ≤ Bb := le_trans (integral_nonneg (fun w => (Real.exp_pos _).le)) hB
  have hBc : 0 ≤ Bc := le_trans (integral_nonneg (fun w => (Real.exp_pos _).le)) hC
  calc (∫ w, Real.exp (t * (A w + B w + C w)) ∂mu)
      ≤ ∫ w, (Real.exp ((2 * t) * A w) / 2 + Real.exp ((4 * t) * B w) / 4 +
          Real.exp ((4 * t) * C w) / 4) ∂mu := integral_mono hint hmaj hpt
    _ = (∫ w, Real.exp ((2 * t) * A w) ∂mu) / 2 +
          (∫ w, Real.exp ((4 * t) * B w) ∂mu) / 4 +
          (∫ w, Real.exp ((4 * t) * C w) ∂mu) / 4 := by
        rw [integral_add (f := fun w => Real.exp ((2 * t) * A w) / 2 +
                Real.exp ((4 * t) * B w) / 4)
              (g := fun w => Real.exp ((4 * t) * C w) / 4)
              ((ha.div_const 2).add (hb.div_const 4)) (hc.div_const 4),
          integral_add (f := fun w => Real.exp ((2 * t) * A w) / 2)
              (g := fun w => Real.exp ((4 * t) * B w) / 4)
              (ha.div_const 2) (hb.div_const 4),
          integral_div, integral_div, integral_div]
    _ ≤ Ba + Bb + Bc := by linarith
  
/-- The scaling identity behind the exponential-moment exponents. -/
theorem aux_finite_cutoff_log_abs_majorant_sq_scale
    (a del tt s n : ℝ) (hdel : del ≠ 0) (htt : 4 * tt = 1 / del) (hs : s ^ 2 = n) :
    ((a * (del * s)) ^ 2) * (4 * tt) ^ 2 / 4 = a ^ 2 * n / 4 := by
  have h1 : (a * (del * s)) ^ 2 = a ^ 2 * del ^ 2 * n := by rw [← hs]; ring
  rw [h1, htt]
  field_simp

/-- Transport of integrability and integrals along a measure-preserving map. -/
theorem aux_finite_cutoff_log_abs_majorant_transfer
    {Om Om' : Type*} [MeasurableSpace Om] [MeasurableSpace Om']
    {mu : Measure Om} {mu' : Measure Om'} {T : Om' → Om}
    (hTm : Measurable T) (hmap : Measure.map T mu' = mu)
    (F : Om → ℝ) (hF : Measurable F) :
    (Integrable (fun w => F (T w)) mu' ↔ Integrable F mu) ∧
      (∫ om, F om ∂mu) = ∫ w, F (T w) ∂mu' := by
  have hmeas : AEStronglyMeasurable F (Measure.map T mu') := by
    rw [hmap]; exact hF.aestronglyMeasurable
  constructor
  · rw [← hmap]
    exact (integrable_map_measure hmeas hTm.aemeasurable).symm
  · rw [← hmap]
    exact integral_map hTm.aemeasurable hmeas

/-- From an exponential-moment bound to the `L^t` bound on `exp V`. -/
theorem aux_finite_cutoff_log_abs_majorant_eLpNorm_exp
    {Om : Type*} [MeasurableSpace Om] (mu : Measure Om) [IsProbabilityMeasure mu]
    (V : Om → ℝ) (hVm : Measurable V) (t : ℝ) (ht : 0 < t)
    (hint : Integrable (fun w => Real.exp (t * V w)) mu) (c : ℝ)
    (hbd : (∫ w, Real.exp (t * V w) ∂mu) ≤ Real.exp (t * c)) :
    MemLp (fun w => Real.exp (V w)) (ENNReal.ofReal t) mu ∧
      eLpNorm (fun w => Real.exp (V w)) (ENNReal.ofReal t) mu ≤
        ENNReal.ofReal (Real.exp c) := by
  have htne : (ENNReal.ofReal t) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero]; linarith
  have httop : (ENNReal.ofReal t) ≠ ⊤ := ENNReal.ofReal_ne_top
  have htoReal : (ENNReal.ofReal t).toReal = t := ENNReal.toReal_ofReal ht.le
  have hpt : ∀ w, ‖Real.exp (V w)‖ₑ ^ t = ENNReal.ofReal (Real.exp (t * V w)) := by
    intro w
    have h1 : ‖Real.exp (V w)‖ₑ = ENNReal.ofReal (Real.exp (V w)) := by
      rw [Real.enorm_eq_ofReal (Real.exp_pos _).le]
    rw [h1, ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
    ring_nf
  have hnn : 0 ≤ᵐ[mu] fun w => Real.exp (t * V w) :=
    Filter.Eventually.of_forall fun w => (Real.exp_pos _).le
  have hlint : (∫⁻ w, ‖Real.exp (V w)‖ₑ ^ (ENNReal.ofReal t).toReal ∂mu) ≤
      ENNReal.ofReal (Real.exp (t * c)) := by
    rw [htoReal]
    calc (∫⁻ w, ‖Real.exp (V w)‖ₑ ^ t ∂mu)
        = ∫⁻ w, ENNReal.ofReal (Real.exp (t * V w)) ∂mu := by
          refine lintegral_congr fun w => ?_
          rw [hpt w]
      _ = ENNReal.ofReal (∫ w, Real.exp (t * V w) ∂mu) :=
          (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
      _ ≤ ENNReal.ofReal (Real.exp (t * c)) := ENNReal.ofReal_le_ofReal hbd
  have hnorm : eLpNorm (fun w => Real.exp (V w)) (ENNReal.ofReal t) mu ≤
      ENNReal.ofReal (Real.exp c) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm htne httop, htoReal]
    have h1 : (∫⁻ w, ‖Real.exp (V w)‖ₑ ^ t ∂mu) ^ (1 / t) ≤
        (ENNReal.ofReal (Real.exp (t * c))) ^ (1 / t) := by
      refine ENNReal.rpow_le_rpow ?_ (by positivity)
      rw [htoReal] at hlint
      exact hlint
    refine le_trans h1 ?_
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
    apply le_of_eq
    congr 1
    rw [mul_comm t c, mul_assoc]
    rw [mul_one_div, div_self (ne_of_gt ht), mul_one]
  exact ⟨⟨(hVm.exp).aestronglyMeasurable, lt_of_le_of_lt hnorm ENNReal.ofReal_lt_top⟩, hnorm⟩


theorem aux_finite_cutoff_log_abs_majorant_exists_pow (y : ℝ) :
    ∃ q : ℕ, y ≤ (3 : ℝ) ^ q / 4 := by
  obtain ⟨q, hq⟩ := pow_unbounded_of_one_lt (4 * y) (by norm_num : (1 : ℝ) < 3)
  exact ⟨q, by linarith⟩

theorem aux_finite_cutoff_log_abs_majorant_exists_pow_half (y : ℝ) :
    ∃ q : ℕ, y < (3 : ℝ) ^ q / 2 := by
  obtain ⟨q, hq⟩ := pow_unbounded_of_one_lt (2 * y) (by norm_num : (1 : ℝ) < 3)
  exact ⟨q, by linarith⟩

/-- The scaled layer's difference quotients on a compact set are dominated by the
shell-cover maximum of the unit-cube observable. -/
theorem aux_finite_cutoff_log_abs_majorant_ratio_bound {d : ℕ}
    (K : Compacts (SpatialCoordinates d)) (Bnd : ℝ)
    (hBnd : ∀ x : K, ‖(x : SpatialCoordinates d)‖ ≤ Bnd)
    (c : ℝ) (hc : 0 ≤ c) (q : ℕ) (hq : c * Bnd ≤ (3 : ℝ) ^ q / 4)
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
    ∀ x y : K, x ≠ y →
      |g (c • (x : SpatialCoordinates d)) - g (c • (y : SpatialCoordinates d))| /
          dist (x : SpatialCoordinates d) (y : SpatialCoordinates d) ≤
        c * ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d (q : ℤ)).sup'
          (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d (q : ℤ))
          (fun a => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
            (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
              (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g))) := by
  have hmem : ∀ x : K, c • (x : SpatialCoordinates d) ∈
      Metric.closedBall (0 : SpatialCoordinates d) (c * Bnd) := by
    intro x
    have hnorm : ‖c • (x : SpatialCoordinates d)‖ = c * ‖(x : SpatialCoordinates d)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    simp only [Metric.mem_closedBall, dist_zero_right, hnorm]
    exact mul_le_mul_of_nonneg_left (hBnd x) hc
  have hbase := aux_finite_negative_layer_log_lipschitz_majorant_scaled_ratio hc hmem g _
    (aux_finite_negative_layer_log_lipschitz_majorant_grid_cover q hq g)
  have hcoe : (((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d (q : ℤ)).sup'
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d (q : ℤ))
        (fun a =>
          (⟨SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
                (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g),
            SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0)) : ℝ≥0) : ℝ) =
      (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d (q : ℤ)).sup'
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d (q : ℤ))
        (fun a => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g)) := by
    rw [Finset.comp_sup'_eq_sup'_comp
      (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d (q : ℤ))
      (fun x : ℝ≥0 => (x : ℝ)) (fun x y => NNReal.coe_max x y)]
    rfl
  rw [← hcoe]
  exact hbase

theorem aux_finite_cutoff_log_abs_majorant_restrict_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (K : Compacts (SpatialCoordinates d))
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) :
    Measurable (fun om : BilateralField d =>
      ‖(H om).restrict (K : Set (SpatialCoordinates d))‖) := by
  haveI : CompactSpace (K : Set (SpatialCoordinates d)) := isCompact_iff_compactSpace.mp K.isCompact
  exact ((continuous_norm.comp
    (ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d)))).measurable).comp hH


/-- Exponential moment of the grid maximum of the finite negative-layer sums. -/
theorem aux_finite_cutoff_log_abs_majorant_max_integral {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (rIdx : ℤ)
    (pts : (Fin d → ℤ) → Homogenization.Vec d) (lam : ℝ) (hlam : 0 ≤ lam) :
    Integrable (fun w : NativeBilateralPotentialSample d => Real.exp (lam *
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d rIdx).sup'
          (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d rIdx)
          (fun q => |∑ j ∈ Finset.range (N + 1),
            (w (-(j : ℤ))) ((3 : ℝ) ^ (j : ℤ) • pts q)|)))
      (Measure.infinitePi (fun _ : ℤ =>
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)) ∧
      (∫ w, Real.exp (lam *
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d rIdx).sup'
          (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d rIdx)
          (fun q => |∑ j ∈ Finset.range (N + 1),
            (w (-(j : ℤ))) ((3 : ℝ) ^ (j : ℤ) • pts q)|))
        ∂(Measure.infinitePi (fun _ : ℤ =>
          (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure))) ≤
        (((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d rIdx).card : ℝ)) *
          (2 * Real.exp ((((6 * Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2 *
              ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * (M.delta * Real.sqrt ((N : ℝ) + 1))) ^ 2) *
              lam ^ 2 / 4)) := by
  classical
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hlog2 : (0 : ℝ) < 1 + Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith
  have hApos : 0 < (6 * Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2 *
      ((1 + Real.log 2) ^ (2 : ℝ)⁻¹)) * (M.delta * Real.sqrt ((N : ℝ) + 1)) := by
    have h1 : 0 < Real.sqrt ((N : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have h2 : 0 < (1 + Real.log 2) ^ (2 : ℝ)⁻¹ := Real.rpow_pos_of_pos hlog2 _
    have h3 := aux_finite_cutoff_log_abs_majorant_gamma_const_pos
    positivity
  have hmeas : ∀ q : Fin d → ℤ, Measurable
      (fun w : NativeBilateralPotentialSample d =>
        |∑ j ∈ Finset.range (N + 1), (w (-(j : ℤ))) ((3 : ℝ) ^ (j : ℤ) • pts q)|) := by
    intro q
    refine (Finset.measurable_sum _ (fun j _ => ?_)).abs
    exact (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval
      ((3 : ℝ) ^ (j : ℤ) • pts q)).comp (measurable_pi_apply (-(j : ℤ)))
  exact aux_finite_cutoff_log_abs_majorant_sup_exp _
    (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d rIdx)
    (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d rIdx) _ _ lam hApos hlam
    hmeas (fun q w => abs_nonneg _)
    (fun q _ => aux_finite_cutoff_log_abs_majorant_sum_ogamma M N
      (fun j => (3 : ℝ) ^ (j : ℤ) • pts q))


/-- Exponential moment of the geometric-weight sum of the layer Lipschitz
observables, which majorizes the cellwise oscillation. -/
theorem aux_finite_cutoff_log_abs_majorant_osc_integral {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N Q0 : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) :
    Integrable (fun w : NativeBilateralPotentialSample d => Real.exp (lam *
        ∑ j ∈ Finset.range (N + 1), ((3 : ℝ) ^ (j : ℤ) * (3 : ℝ) ^ (-(N : ℤ))) *
          ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((j : ℤ) + (Q0 : ℤ))).sup'
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ)))
            (fun a => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
                (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) (w (-(j : ℤ))))))))
      (Measure.infinitePi (fun _ : ℤ =>
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)) ∧
      (∫ w, Real.exp (lam *
        ∑ j ∈ Finset.range (N + 1), ((3 : ℝ) ^ (j : ℤ) * (3 : ℝ) ^ (-(N : ℤ))) *
          ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((j : ℤ) + (Q0 : ℤ))).sup'
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ)))
            (fun a => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
                (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) (w (-(j : ℤ)))))))
        ∂(Measure.infinitePi (fun _ : ℤ =>
          (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure))) ≤
        2 * Real.exp (((3 / 2) * (M.delta * Real.sqrt
          ((5 * (1 + Real.log 2 + (d : ℝ) * ((Q0 : ℝ) + 3) * Real.log 3)) *
            ((N : ℝ) + 1)))) ^ 2 * lam ^ 2 / 4) := by
  classical
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  set E0 : ℝ := 5 * (1 + Real.log 2 + (d : ℝ) * ((Q0 : ℝ) + 3) * Real.log 3) with hE0
  have hE0pos : 0 < E0 := by
    rw [hE0]
    have : (0 : ℝ) ≤ (d : ℝ) * ((Q0 : ℝ) + 3) * Real.log 3 := by positivity
    linarith
  set A : ℝ := M.delta * Real.sqrt (E0 * ((N : ℝ) + 1)) with hA
  have hApos : 0 < A := by
    rw [hA]
    have : 0 < Real.sqrt (E0 * ((N : ℝ) + 1)) := Real.sqrt_pos.mpr (by positivity)
    positivity
  set W : ℕ → SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ := fun j g =>
    (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((j : ℤ) + (Q0 : ℤ))).sup'
      (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ)))
      (fun a => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
          (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g)) with hW
  have hWmeas : ∀ j, Measurable (W j) := by
    intro j
    have h0 : Measurable ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((j : ℤ) + (Q0 : ℤ))).sup'
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ)))
        (fun a g => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g))) :=
      Finset.measurable_sup' _ (fun a _ =>
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_measurable.comp
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_translate _))
    have h1 : ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((j : ℤ) + (Q0 : ℤ))).sup'
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ)))
        (fun a g => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g))) = W j := by
      funext g
      exact Finset.sup'_apply _ _ g
    rwa [h1] at h0
  have hWnn : ∀ j g, 0 ≤ W j g := by
    intro j g
    obtain ⟨a, ha⟩ := SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ))
    exact le_trans (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_nonneg _)
      (Finset.le_sup' (f := fun a => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
          (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) g)) ha)
  set f : ℕ → NativeBilateralPotentialSample d → ℝ := fun j w => W j (w (-(j : ℤ))) with hf
  have hfmeas : ∀ j, Measurable (f j) := fun j => (hWmeas j).comp (measurable_pi_apply _)
  have hfnn : ∀ j w, 0 ≤ f j w := fun j w => hWnn j _
  set wt : ℕ → ℝ := fun j => (3 : ℝ) ^ (j : ℤ) * (3 : ℝ) ^ (-(N : ℤ)) with hwt
  have hwtpos : ∀ j, 0 < wt j := by intro j; rw [hwt]; positivity
  have hOG : ∀ j ∈ Finset.range (N + 1),
      SubdiffusiveProcess.OGammaLE (Measure.infinitePi (fun _ : ℤ =>
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)) 2 A (f j) := by
    intro j hj
    have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hbase := aux_finite_cutoff_log_abs_majorant_lip_ogamma M ((j : ℤ) + (Q0 : ℤ))
    have hmap : Measure.map
        (fun w : NativeBilateralPotentialSample d => w (-(j : ℤ)))
        (Measure.infinitePi (fun _ : ℤ =>
          (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)) =
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure :=
      Measure.infinitePi_map_eval _ (-(j : ℤ))
    have htrans := aux_finite_cutoff_log_abs_majorant_ogamma_map
      (T := fun w : NativeBilateralPotentialSample d => w (-(j : ℤ)))
      (measurable_pi_apply _) hmap (hWmeas j) hbase
    refine SubdiffusiveProcess.CoarseGrainingVocab.OGamma.ogammaLE_mono_scale ?_ ?_ (by norm_num)
      (hfmeas j).aemeasurable htrans
    · have hcard : (1 : ℝ) ≤ ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d
          ((j : ℤ) + (Q0 : ℤ))).card : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr
          (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ))))
      have hlog : 0 ≤ Real.log (2 * ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d
          ((j : ℤ) + (Q0 : ℤ))).card : ℝ)) := Real.log_nonneg (by linarith)
      have : 0 < Real.sqrt (5 * (1 + Real.log (2 * ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d
          ((j : ℤ) + (Q0 : ℤ))).card : ℝ)))) := Real.sqrt_pos.mpr (by linarith)
      positivity
    · rw [hA]
      refine mul_le_mul_of_nonneg_left ?_ hdelta.le
      exact Real.sqrt_le_sqrt
        (aux_finite_cutoff_log_abs_majorant_lip_scale d Q0 N j hjN)
  have hAtot : (∑ j ∈ Finset.range (N + 1), wt j) * A ≤ (3 / 2) * A := by
    have hsum := aux_finite_cutoff_log_abs_majorant_weight_sum N
    exact mul_le_mul_of_nonneg_right hsum hApos.le
  have horl := aux_finite_cutoff_log_abs_majorant_weighted_sum_orlicz
    (Measure.infinitePi (fun _ : ℤ =>
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)) N f A hApos wt hwtpos
    hfmeas hfnn hOG ((3 / 2) * A) hAtot
  have hXmeas : Measurable (fun w : NativeBilateralPotentialSample d =>
      ∑ j ∈ Finset.range (N + 1), wt j * f j w) :=
    Finset.measurable_sum _ (fun j _ => measurable_const.mul (hfmeas j))
  have hXnn : ∀ w, 0 ≤ ∑ j ∈ Finset.range (N + 1), wt j * f j w := by
    intro w
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hwtpos j).le (hfnn j w))
  exact SubdiffusiveProcess.orlicz_exp_linear_integrable_integral_le _ _ ((3 / 2) * A) lam
    hXmeas hXnn (by positivity) hlam horl


/-- The exponential-moment bound for the logarithmic envelope at the working
exponent `t = 1/(4δ)`. -/
theorem aux_finite_cutoff_log_abs_majorant_moment {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (K : Compacts (SpatialCoordinates d)) (Bnd : ℝ)
    (hKnorm : ∀ x : K, ‖(x : SpatialCoordinates d)‖ ≤ Bnd)
    (Q0 Q1 : ℕ) (hQ0 : Bnd ≤ (3 : ℝ) ^ Q0 / 4)
    (Vr : C(SpatialCoordinates d, ℝ) → ℝ) (_hVr0 : ∀ f, 0 ≤ Vr f)
    (hVrle : ∀ (f : C(SpatialCoordinates d, ℝ)) (L : ℝ), 0 ≤ L →
      (∀ x y : K, x ≠ y →
        |f (x : SpatialCoordinates d) - f (y : SpatialCoordinates d)| /
          dist (x : SpatialCoordinates d) (y : SpatialCoordinates d) ≤ L) → Vr f ≤ L)
    (CH : ℝ) (hCH0 : 0 ≤ CH)
    (hCHb : ∀ lambda : ℝ, 0 ≤ lambda →
      Integrable (fun om => Real.exp
          (lambda * ‖(H om).restrict (K : Set (SpatialCoordinates d))‖))
        (chaosSampleLaw M).toMeasure ∧
      (∫ om, Real.exp (lambda * ‖(H om).restrict (K : Set (SpatialCoordinates d))‖)
        ∂(chaosSampleLaw M).toMeasure) ≤ 2 * Real.exp (CH * lambda ^ 2 * M.delta ^ 2))
    (Cval E0 u0 u1 t : ℝ)
    (hCvaldef : Cval = 6 * Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2 *
      ((1 + Real.log 2) ^ (2 : ℝ)⁻¹))
    (hE0def : E0 = 5 * (1 + Real.log 2 + (d : ℝ) * ((Q0 : ℝ) + 3) * Real.log 3))
    (hu1nn : 0 ≤ u1)
    (hu0a : Real.log 2 + CH / 4 ≤ u0)
    (hu0b : Real.log 2 + (d : ℝ) * ((Q1 : ℝ) + 2) * Real.log 3 + Cval ^ 2 / 4 ≤ u0)
    (hu1b : (d : ℝ) * Real.log 3 + Cval ^ 2 / 4 ≤ u1)
    (hu0c : Real.log 2 + (9 / 16) * E0 ≤ u0)
    (hu1c : (9 / 16) * E0 ≤ u1)
    (ht : t = 1 / (4 * M.delta))
    (Ah : BilateralField d → ℝ)
    (hAhdef : ∀ om, Ah om = ‖(H om).restrict (K : Set (SpatialCoordinates d))‖)
    (hAhmeas : Measurable Ah)
    (Amax : ℕ → BilateralField d → ℝ)
    (hAmaxdef : ∀ N om, Amax N om =
      (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((N : ℤ) + (Q1 : ℤ))).sup'
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((N : ℤ) + (Q1 : ℤ)))
        (fun q => |∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j))
          ((3 : ℝ) ^ (-(N : ℤ)) • SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter q)|))
    (hAmaxmeas : ∀ N, Measurable (Amax N))
    (Aosc : ℕ → BilateralField d → ℝ)
    (hAoscdef : ∀ N om, Aosc N om =
      (3 : ℝ) ^ (-(N : ℤ)) * ∑ j ∈ Finset.range (N + 1), Vr (om (-(Int.ofNat j))))
    (hAoscmeas : ∀ N, Measurable (Aosc N))
    (N : ℕ) :
    Integrable (fun om => Real.exp (t *
        (2 * ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P +
          Ah om + Amax N om + Aosc N om))) (chaosSampleLaw M).toMeasure ∧
      (∫ om, Real.exp (t *
        (2 * ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P +
          Ah om + Amax N om + Aosc N om)) ∂(chaosSampleLaw M).toMeasure) ≤
        Real.exp (t * (2 * ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P +
          4 * M.delta * (Real.log 3 + u0 + u1 * (N : ℝ)))) := by
  classical
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hdhalf : M.delta ≤ 1 / 2 := M.shellPrefix.delta_le_half
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hE0pos : 0 < E0 := by
    rw [hE0def]
    have h : (0 : ℝ) ≤ (d : ℝ) * ((Q0 : ℝ) + 3) * Real.log 3 := by positivity
    linarith
  have h4dt : 4 * M.delta * t = 1 := by rw [ht]; field_simp
  have htpos : 0 < t := by rw [ht]; positivity
  have ht2 : (0 : ℝ) ≤ 2 * t := by linarith
  have ht4 : (0 : ℝ) ≤ 4 * t := by linarith
  set mu0 : Measure (NativeBilateralPotentialSample d) :=
    Measure.infinitePi (fun _ : ℤ =>
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure) with hmu0
  set forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩ with hforget
  set pz : NativeBilateralPotentialSample d → BilateralField d :=
    fun omega j => layerScaling d j (forget (omega j)) with hpz
  have hpzmeas : Measurable pz := by
    apply measurable_pi_lambda
    intro j
    exact (layerScaling d j).continuous.measurable.comp
      (forget.continuous.measurable.comp (measurable_pi_apply j))
  have hpzmap : Measure.map pz mu0 = (chaosSampleLaw M).toMeasure := by
    simpa only [chaosSampleLaw, chaosRootFieldLaw, hmu0, hpz, hforget, Function.comp_apply] using
      (measurePreserving_nativeCopies_commonScaleLaw M).map_eq
  have hpzapp : ∀ (w : NativeBilateralPotentialSample d) (j : ℕ) (y : SpatialCoordinates d),
      (pz w) (-(Int.ofNat j)) y = (w (-(j : ℤ))) ((3 : ℝ) ^ (j : ℤ) • y) := by
    intro w j y
    show (layerScaling d (-(Int.ofNat j)) (forget (w (-(Int.ofNat j))))) y = _
    simp [layerScaling, ContinuousMap.compRightContinuousMap, hforget]
  set gpt : ℕ → (Fin d → ℤ) → SpatialCoordinates d := fun N q =>
    (3 : ℝ) ^ (-(N : ℤ)) • SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter q with hgpt
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hu1N : 0 ≤ u1 * (N : ℝ) := mul_nonneg hu1nn hNnn
  have hCvalsq : (0 : ℝ) ≤ Cval ^ 2 / 4 := by positivity
  have hE0nn : (0 : ℝ) ≤ (9 / 16) * E0 := by linarith
  have hdQ1 : (0 : ℝ) ≤ (d : ℝ) * ((Q1 : ℝ) + 2) * Real.log 3 := by positivity
  have hCHK : 0 ≤ CH := hCH0
  -- the infrared part
  obtain ⟨hIHint0, hIHbd0⟩ := hCHb (2 * t) ht2
  obtain ⟨hHiff, hHeq⟩ := aux_finite_cutoff_log_abs_majorant_transfer hpzmeas hpzmap
    (fun om => Real.exp ((2 * t) * Ah om)) ((measurable_const.mul hAhmeas).exp)
  have hAhfun : (fun om : BilateralField d => Real.exp ((2 * t) * Ah om)) =
      (fun om : BilateralField d => Real.exp ((2 * t) *
        ‖(H om).restrict (K : Set (SpatialCoordinates d))‖)) := by
    funext om
    rw [hAhdef]
  have hA0 : Integrable (fun w => Real.exp ((2 * t) * Ah (pz w))) mu0 := by
    refine hHiff.mpr ?_
    rw [hAhfun]
    exact hIHint0
  have hA1 : (∫ w, Real.exp ((2 * t) * Ah (pz w)) ∂mu0) ≤
      Real.exp (u0 + u1 * (N : ℝ)) := by
    rw [← hHeq, hAhfun]
    refine le_trans hIHbd0 ?_
    have hcalc : CH * (2 * t) ^ 2 * M.delta ^ 2 = CH / 4 := by
      rw [ht]; field_simp; ring
    rw [hcalc, show (2 : ℝ) * Real.exp (CH / 4) =
      Real.exp (Real.log 2 + CH / 4) by
        rw [Real.exp_add, Real.exp_log (by norm_num)]]
    apply Real.exp_le_exp.mpr
    linarith
  -- the grid maximum
  have hAmaxcomp : ∀ w : NativeBilateralPotentialSample d,
      Amax N (pz w) =
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((N : ℤ) + (Q1 : ℤ))).sup'
          (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((N : ℤ) + (Q1 : ℤ)))
          (fun q => |∑ j ∈ Finset.range (N + 1),
            (w (-(j : ℤ))) ((3 : ℝ) ^ (j : ℤ) • gpt N q)|) := by
    intro w
    have hfun : (fun q : Fin d → ℤ => |∑ j ∈ Finset.range (N + 1),
          (pz w) (-(Int.ofNat j)) (gpt N q)|) =
        (fun q : Fin d → ℤ => |∑ j ∈ Finset.range (N + 1),
          (w (-(j : ℤ))) ((3 : ℝ) ^ (j : ℤ) • gpt N q)|) := by
      funext q
      congr 1
      exact Finset.sum_congr rfl (fun j _ => hpzapp w j (gpt N q))
    rw [hAmaxdef]
    rw [hfun]
  obtain ⟨hIMint0, hIMbd0⟩ := aux_finite_cutoff_log_abs_majorant_max_integral M N
    ((N : ℤ) + (Q1 : ℤ)) (fun q => gpt N q) (4 * t) ht4
  rw [← hCvaldef] at hIMbd0
  have hMrw : (fun w : NativeBilateralPotentialSample d =>
      Real.exp ((4 * t) * Amax N (pz w))) =
      (fun w : NativeBilateralPotentialSample d => Real.exp ((4 * t) *
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((N : ℤ) + (Q1 : ℤ))).sup'
          (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((N : ℤ) + (Q1 : ℤ)))
          (fun q => |∑ j ∈ Finset.range (N + 1),
            (w (-(j : ℤ))) ((3 : ℝ) ^ (j : ℤ) • gpt N q)|))) := by
    funext w
    rw [hAmaxcomp w]
  have hM0 : Integrable (fun w => Real.exp ((4 * t) * Amax N (pz w))) mu0 := by
    rw [hMrw]; exact hIMint0
  have hM1 : (∫ w, Real.exp ((4 * t) * Amax N (pz w)) ∂mu0) ≤
      Real.exp (u0 + u1 * (N : ℝ)) := by
    rw [hMrw]
    refine le_trans hIMbd0 ?_
    have hsq : Real.sqrt ((N : ℝ) + 1) ^ 2 = (N : ℝ) + 1 :=
      Real.sq_sqrt (by positivity)
    have htt : 4 * t = 1 / M.delta := by rw [ht]; field_simp
    have hexp : ((Cval * (M.delta * Real.sqrt ((N : ℝ) + 1))) ^ 2) * (4 * t) ^ 2 / 4 =
        Cval ^ 2 * ((N : ℝ) + 1) / 4 :=
      aux_finite_cutoff_log_abs_majorant_sq_scale Cval M.delta t
        (Real.sqrt ((N : ℝ) + 1)) ((N : ℝ) + 1) (ne_of_gt hdelta) htt hsq
    rw [hexp]
    have hcard1 : (1 : ℝ) ≤ ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d
        ((N : ℤ) + (Q1 : ℤ))).card : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((N : ℤ) + (Q1 : ℤ))))
    have hprod : (((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d
          ((N : ℤ) + (Q1 : ℤ))).card : ℝ)) *
        (2 * Real.exp (Cval ^ 2 * ((N : ℝ) + 1) / 4)) =
        Real.exp (Real.log (2 * ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d
          ((N : ℤ) + (Q1 : ℤ))).card : ℝ)) + Cval ^ 2 * ((N : ℝ) + 1) / 4) := by
      rw [Real.exp_add, Real.exp_log (by linarith)]
      ring
    rw [hprod]
    apply Real.exp_le_exp.mpr
    have hlogcard := aux_finite_cutoff_log_abs_majorant_card_log d ((N : ℤ) + (Q1 : ℤ))
    have htoNat : ((((N : ℤ) + (Q1 : ℤ)) + 1).toNat : ℝ) = (N : ℝ) + (Q1 : ℝ) + 1 := by
      have h : (((N : ℤ) + (Q1 : ℤ)) + 1).toNat = N + Q1 + 1 := by omega
      rw [h]; push_cast; ring
    rw [htoNat] at hlogcard
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hexp2 : (d : ℝ) * ((N : ℝ) + (Q1 : ℝ) + 1 + 1) * Real.log 3
        = (d : ℝ) * ((Q1 : ℝ) + 2) * Real.log 3 + ((d : ℝ) * Real.log 3) * (N : ℝ) := by
      ring
    rw [hexp2] at hlogcard
    have hexpand : Cval ^ 2 * ((N : ℝ) + 1) / 4 =
        Cval ^ 2 / 4 + (Cval ^ 2 / 4) * (N : ℝ) := by ring
    have hprod : ((d : ℝ) * Real.log 3 + Cval ^ 2 / 4) * (N : ℝ) ≤ u1 * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hu1b hNnn
    have hprod2 : ((d : ℝ) * Real.log 3 + Cval ^ 2 / 4) * (N : ℝ) =
        ((d : ℝ) * Real.log 3) * (N : ℝ) + (Cval ^ 2 / 4) * (N : ℝ) := by ring
    rw [hprod2] at hprod
    rw [hexpand]
    linarith
  -- the oscillation
  have hOle : ∀ w : NativeBilateralPotentialSample d,
      Aosc N (pz w) ≤ ∑ j ∈ Finset.range (N + 1),
        ((3 : ℝ) ^ (j : ℤ) * (3 : ℝ) ^ (-(N : ℤ))) *
          ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((j : ℤ) + (Q0 : ℤ))).sup'
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ)))
            (fun a => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
                (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) (w (-(j : ℤ)))))) := by
    intro w
    have hterm : ∀ j ∈ Finset.range (N + 1),
        Vr ((pz w) (-(Int.ofNat j))) ≤ (3 : ℝ) ^ (j : ℤ) *
          ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((j : ℤ) + (Q0 : ℤ))).sup'
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ)))
            (fun a => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
                (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) (w (-(j : ℤ)))))) := by
      intro j _
      have hc : (0 : ℝ) ≤ (3 : ℝ) ^ (j : ℤ) := by positivity
      have hq : (3 : ℝ) ^ (j : ℤ) * Bnd ≤ (3 : ℝ) ^ (j + Q0) / 4 := by
        have h1 : (3 : ℝ) ^ (j : ℤ) * Bnd ≤ (3 : ℝ) ^ (j : ℤ) * ((3 : ℝ) ^ Q0 / 4) :=
          mul_le_mul_of_nonneg_left hQ0 hc
        have h2 : (3 : ℝ) ^ (j : ℤ) * ((3 : ℝ) ^ Q0 / 4) = (3 : ℝ) ^ (j + Q0) / 4 := by
          rw [pow_add, zpow_natCast]
          ring
        linarith
      have hratio := aux_finite_cutoff_log_abs_majorant_ratio_bound K Bnd hKnorm
        ((3 : ℝ) ^ (j : ℤ)) hc (j + Q0) hq (w (-(j : ℤ)))
      have hidx : ((j + Q0 : ℕ) : ℤ) = (j : ℤ) + (Q0 : ℤ) := by push_cast; ring
      rw [hidx] at hratio
      refine hVrle ((pz w) (-(Int.ofNat j))) _ ?_ ?_
      · refine mul_nonneg hc ?_
        obtain ⟨a, ha⟩ :=
          SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ))
        exact le_trans (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_nonneg _)
          (Finset.le_sup' (f := fun a =>
            SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
                (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) (w (-(j : ℤ))))) ha)
      · intro x y hxy
        have hval : ∀ u : SpatialCoordinates d,
            (pz w) (-(Int.ofNat j)) u = (w (-(j : ℤ))) ((3 : ℝ) ^ (j : ℤ) • u) :=
          fun u => hpzapp w j u
        rw [hval, hval]
        exact hratio x y hxy
    have hsum : (∑ j ∈ Finset.range (N + 1), Vr ((pz w) (-(Int.ofNat j)))) ≤
        ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (j : ℤ) *
          ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((j : ℤ) + (Q0 : ℤ))).sup'
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ)))
            (fun a => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
                (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) (w (-(j : ℤ)))))) :=
      Finset.sum_le_sum hterm
    rw [hAoscdef]
    have hstep : (3 : ℝ) ^ (-(N : ℤ)) *
        ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (j : ℤ) *
          ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((j : ℤ) + (Q0 : ℤ))).sup'
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ)))
            (fun a => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
                (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) (w (-(j : ℤ)))))) =
        ∑ j ∈ Finset.range (N + 1), ((3 : ℝ) ^ (j : ℤ) * (3 : ℝ) ^ (-(N : ℤ))) *
          ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((j : ℤ) + (Q0 : ℤ))).sup'
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ)))
            (fun a => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
                (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) (w (-(j : ℤ)))))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← mul_assoc, mul_comm ((3 : ℝ) ^ (-(N : ℤ)))]
    rw [← hstep]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  obtain ⟨hIOint0, hIObd0⟩ := aux_finite_cutoff_log_abs_majorant_osc_integral M N Q0
    (4 * t) ht4
  rw [← hE0def] at hIObd0
  have hOptw : ∀ w : NativeBilateralPotentialSample d,
      Real.exp ((4 * t) * Aosc N (pz w)) ≤ Real.exp ((4 * t) *
        ∑ j ∈ Finset.range (N + 1), ((3 : ℝ) ^ (j : ℤ) * (3 : ℝ) ^ (-(N : ℤ))) *
          ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((j : ℤ) + (Q0 : ℤ))).sup'
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((j : ℤ) + (Q0 : ℤ)))
            (fun a => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
                (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) (w (-(j : ℤ))))))) := by
    intro w
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hOle w) ht4)
  have hOmeas : Measurable (fun w : NativeBilateralPotentialSample d =>
      Real.exp ((4 * t) * Aosc N (pz w))) :=
    (measurable_const.mul ((hAoscmeas N).comp hpzmeas)).exp
  have hO0 : Integrable (fun w => Real.exp ((4 * t) * Aosc N (pz w))) mu0 := by
    refine hIOint0.mono' hOmeas.aestronglyMeasurable ?_
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hOptw w
  have hO1 : (∫ w, Real.exp ((4 * t) * Aosc N (pz w)) ∂mu0) ≤
      Real.exp (u0 + u1 * (N : ℝ)) := by
    refine le_trans (integral_mono hO0 hIOint0 hOptw) ?_
    refine le_trans hIObd0 ?_
    have hsq : Real.sqrt (E0 * ((N : ℝ) + 1)) ^ 2 = E0 * ((N : ℝ) + 1) := by
      refine Real.sq_sqrt ?_
      have h1 : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
      exact mul_nonneg hE0pos.le h1
    have htt : 4 * t = 1 / M.delta := by rw [ht]; field_simp
    have hexp0 := aux_finite_cutoff_log_abs_majorant_sq_scale (3 / 2) M.delta t
        (Real.sqrt (E0 * ((N : ℝ) + 1))) (E0 * ((N : ℝ) + 1)) (ne_of_gt hdelta) htt hsq
    have hexp : ((3 / 2) * (M.delta * Real.sqrt (E0 * ((N : ℝ) + 1)))) ^ 2 *
        (4 * t) ^ 2 / 4 = (9 / 16) * E0 * ((N : ℝ) + 1) := by
      rw [hexp0]; ring
    rw [hexp, show (2 : ℝ) * Real.exp ((9 / 16) * E0 * ((N : ℝ) + 1)) =
      Real.exp (Real.log 2 + (9 / 16) * E0 * ((N : ℝ) + 1)) by
        rw [Real.exp_add, Real.exp_log (by norm_num)]]
    apply Real.exp_le_exp.mpr
    have hexpand : (9 / 16) * E0 * ((N : ℝ) + 1) =
        (9 / 16) * E0 + ((9 / 16) * E0) * (N : ℝ) := by ring
    have hprod : ((9 / 16) * E0) * (N : ℝ) ≤ u1 * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hu1c hNnn
    rw [hexpand]
    linarith
  -- assemble
  obtain ⟨hint3, hbd3⟩ := aux_finite_cutoff_log_abs_majorant_amgm3 mu0 t
    (fun w => Ah (pz w)) (fun w => Amax N (pz w)) (fun w => Aosc N (pz w))
    (hAhmeas.comp hpzmeas) ((hAmaxmeas N).comp hpzmeas) ((hAoscmeas N).comp hpzmeas)
    hA0 hM0 hO0 _ _ _ hA1 hM1 hO1
  have hVVm : Measurable (fun om : BilateralField d =>
      2 * ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P + Ah om + Amax N om + Aosc N om) :=
    ((measurable_const.add hAhmeas).add (hAmaxmeas N)).add (hAoscmeas N)
  obtain ⟨hViff, hVeq⟩ := aux_finite_cutoff_log_abs_majorant_transfer hpzmeas hpzmap
    (fun om => Real.exp (t * (2 * ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P +
      Ah om + Amax N om + Aosc N om))) ((measurable_const.mul hVVm).exp)
  have hVVsplit : (fun w : NativeBilateralPotentialSample d =>
      Real.exp (t * (2 * ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P +
        Ah (pz w) + Amax N (pz w) + Aosc N (pz w)))) =
      (fun w : NativeBilateralPotentialSample d =>
        Real.exp (t * (2 * ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) *
          Real.exp (t * (Ah (pz w) + Amax N (pz w) + Aosc N (pz w)))) := by
    funext w
    rw [← Real.exp_add]
    congr 1
    ring
  have hfinal : Real.exp (t * (2 * ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) *
      (Real.exp (u0 + u1 * (N : ℝ)) + Real.exp (u0 + u1 * (N : ℝ)) +
        Real.exp (u0 + u1 * (N : ℝ))) =
      Real.exp (t * (2 * ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P +
        4 * M.delta * (Real.log 3 + u0 + u1 * (N : ℝ)))) := by
    have harg : t * (2 * ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P +
          4 * M.delta * (Real.log 3 + u0 + u1 * (N : ℝ))) =
        t * (2 * ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) +
          (Real.log 3 + u0 + u1 * (N : ℝ)) := by
      have hx : t * (4 * M.delta * (Real.log 3 + u0 + u1 * (N : ℝ))) =
          (4 * M.delta * t) * (Real.log 3 + u0 + u1 * (N : ℝ)) := by ring
      rw [mul_add, hx, h4dt, one_mul]
    have e1 : Real.exp (t * (2 * ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) +
          (Real.log 3 + u0 + u1 * (N : ℝ))) =
        Real.exp (t * (2 * ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) *
          Real.exp (Real.log 3 + u0 + u1 * (N : ℝ)) := Real.exp_add _ _
    have e2 : Real.exp (Real.log 3 + u0 + u1 * (N : ℝ)) =
        3 * Real.exp (u0 + u1 * (N : ℝ)) := by
      rw [show Real.log 3 + u0 + u1 * (N : ℝ) = Real.log 3 + (u0 + u1 * (N : ℝ)) from by ring,
        Real.exp_add (Real.log 3) (u0 + u1 * (N : ℝ)), Real.exp_log (by norm_num)]
    rw [harg, e1, e2]
    ring
  constructor
  · refine hViff.mp ?_
    rw [hVVsplit]
    exact hint3.const_mul _
  · rw [hVeq, hVVsplit, integral_const_mul, ← hfinal]
    exact mul_le_mul_of_nonneg_left hbd3 (Real.exp_pos _).le


/-- The almost-sure logarithmic envelope of the finite-cutoff coefficient. -/
theorem aux_finite_cutoff_log_abs_majorant_envelope {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (K : Compacts (SpatialCoordinates d)) (Bnd : ℝ)
    (hKnorm : ∀ x : K, ‖(x : SpatialCoordinates d)‖ ≤ Bnd)
    (hKcontains : ∀ u : SpatialCoordinates d, dist u z ≤ r / 2 + 1 →
      u ∈ (K : Set (SpatialCoordinates d)))
    (Q1 : ℕ) (hQ1 : ‖z‖ + r / 2 < (3 : ℝ) ^ Q1 / 2)
    (Vr : C(SpatialCoordinates d, ℝ) → ℝ) (hVr0 : ∀ f, 0 ≤ Vr f)
    (hVrdom : ∀ (f : C(SpatialCoordinates d, ℝ)) (L : ℝ),
      (∀ x y : K, x ≠ y →
        |f (x : SpatialCoordinates d) - f (y : SpatialCoordinates d)| /
          dist (x : SpatialCoordinates d) (y : SpatialCoordinates d) ≤ L) →
      ∀ x y : K, x ≠ y →
        |f (x : SpatialCoordinates d) - f (y : SpatialCoordinates d)| /
          dist (x : SpatialCoordinates d) (y : SpatialCoordinates d) ≤ Vr f)
    (hVrset : MeasurableSet {f : C(SpatialCoordinates d, ℝ) | ∀ x y : K, x ≠ y →
      |f (x : SpatialCoordinates d) - f (y : SpatialCoordinates d)| /
        dist (x : SpatialCoordinates d) (y : SpatialCoordinates d) ≤ Vr f})
    (Ah : BilateralField d → ℝ)
    (hAhdef : ∀ om, Ah om = ‖(H om).restrict (K : Set (SpatialCoordinates d))‖)
    (Amax : ℕ → BilateralField d → ℝ)
    (hAmaxdef : ∀ N om, Amax N om =
      (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((N : ℤ) + (Q1 : ℤ))).sup'
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((N : ℤ) + (Q1 : ℤ)))
        (fun q => |∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j))
          ((3 : ℝ) ^ (-(N : ℤ)) • SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter q)|))
    (Aosc : ℕ → BilateralField d → ℝ)
    (hAoscdef : ∀ N om, Aosc N om =
      (3 : ℝ) ^ (-(N : ℤ)) * ∑ j ∈ Finset.range (N + 1), Vr (om (-(Int.ofNat j)))) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ N x, x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
        |Real.log (cutoffCoefficient M H om N x)| ≤
          2 * ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P +
            Ah om + Amax N om + Aosc N om := by
  classical
  haveI : CompactSpace (K : Set (SpatialCoordinates d)) := isCompact_iff_compactSpace.mp K.isCompact
  set mu0 : Measure (NativeBilateralPotentialSample d) :=
    Measure.infinitePi (fun _ : ℤ =>
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure) with hmu0
  set forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩ with hforget
  set pz : NativeBilateralPotentialSample d → BilateralField d :=
    fun omega j => layerScaling d j (forget (omega j)) with hpz
  have hpzmeas : Measurable pz := by
    apply measurable_pi_lambda
    intro j
    exact (layerScaling d j).continuous.measurable.comp
      (forget.continuous.measurable.comp (measurable_pi_apply j))
  have hpzmap : Measure.map pz mu0 = (chaosSampleLaw M).toMeasure := by
    simpa only [chaosSampleLaw, chaosRootFieldLaw, hmu0, hpz, hforget, Function.comp_apply] using
      (measurePreserving_nativeCopies_commonScaleLaw M).map_eq
  set gpt : ℕ → (Fin d → ℤ) → SpatialCoordinates d := fun N q =>
    (3 : ℝ) ^ (-(N : ℤ)) • SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter q with hgpt
  have hGoodmeas : MeasurableSet {om : BilateralField d | ∀ j : ℤ,
      ∀ x y : K, x ≠ y →
        |om j x - om j y| / dist (x : SpatialCoordinates d) (y : SpatialCoordinates d) ≤
          Vr (om j)} := by
    have heq : {om : BilateralField d | ∀ j : ℤ, ∀ x y : K, x ≠ y →
          |om j x - om j y| / dist (x : SpatialCoordinates d) (y : SpatialCoordinates d) ≤
            Vr (om j)} =
        ⋂ j : ℤ, (fun om : BilateralField d => om j) ⁻¹'
          {f : C(SpatialCoordinates d, ℝ) | ∀ x y : K, x ≠ y →
            |f x - f y| / dist (x : SpatialCoordinates d) (y : SpatialCoordinates d) ≤ Vr f} := by
      ext om
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [heq]
    exact MeasurableSet.iInter (fun j => (measurable_pi_apply j) hVrset)
  have hGood : ∀ᵐ om ∂((chaosSampleLaw M).toMeasure), ∀ j : ℤ,
      ∀ x y : K, x ≠ y →
        |om j x - om j y| / dist (x : SpatialCoordinates d) (y : SpatialCoordinates d) ≤
          Vr (om j) := by
    rw [← hpzmap, ae_map_iff hpzmeas.aemeasurable hGoodmeas]
    filter_upwards with w
    intro j
    obtain ⟨q, hq⟩ :=
      aux_finite_cutoff_log_abs_majorant_exists_pow ((3 : ℝ) ^ (-j) * Bnd)
    have hc : (0 : ℝ) ≤ (3 : ℝ) ^ (-j) := by positivity
    have hratio := aux_finite_cutoff_log_abs_majorant_ratio_bound K Bnd hKnorm
      ((3 : ℝ) ^ (-j)) hc q hq (w j)
    refine hVrdom (pz w j) ((3 : ℝ) ^ (-j) *
      ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d (q : ℤ)).sup'
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d (q : ℤ))
        (fun a => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
            (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter a) (w j))))) ?_
    intro x y hxy
    have hval : ∀ u : SpatialCoordinates d,
        (pz w j) u = (w j) ((3 : ℝ) ^ (-j) • u) := fun u => rfl
    rw [hval, hval]
    exact hratio x y hxy
  filter_upwards [hGood] with om hom
  intro N x hx
  have hxd : dist x z ≤ r / 2 := hx
  have hxK : x ∈ (K : Set (SpatialCoordinates d)) := hKcontains x (by linarith)
  have hahom : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M N := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  have hlogid : Real.log (cutoffCoefficient M H om N x) =
      -Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) +
        (H om x + (∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x)
          - ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by
    rw [cutoffCoefficient, Real.log_mul (by positivity) (ne_of_gt (Real.exp_pos _)),
      Real.log_inv, Real.log_exp, cutoffPotential]
  have hlogahom1 : Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) ≤ 0 :=
    Real.log_nonpos hahom.le (Rm.ahom_le_one N)
  have hlogahom2 : -(((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ≤
      Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) := by
    have h := Rm.ahom_lower N
    have h2 := Real.log_le_log (Real.exp_pos _) h
    rw [Real.log_exp] at h2
    have : -((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P =
        -(((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by ring
    linarith [this ▸ h2]
  have hHbound : |H om x| ≤ Ah om := by
    rw [hAhdef]
    have hb : ‖((H om).restrict (K : Set (SpatialCoordinates d))) ⟨x, hxK⟩‖ ≤
        ‖(H om).restrict (K : Set (SpatialCoordinates d))‖ :=
      ContinuousMap.norm_coe_le_norm _ _
    have heq : ((H om).restrict (K : Set (SpatialCoordinates d))) ⟨x, hxK⟩ = H om x := rfl
    rw [heq, Real.norm_eq_abs] at hb
    exact hb
  obtain ⟨q, hqmem, hqdist⟩ :=
    aux_finite_cutoff_log_abs_majorant_grid N Q1 z (r / 2) hQ1 x hx
  have hy0K : gpt N q ∈ (K : Set (SpatialCoordinates d)) := by
    refine hKcontains _ ?_
    have h3 : (3 : ℝ) ^ (-(N : ℤ)) ≤ 1 := by
      rw [zpow_neg, zpow_natCast]
      have h31 : (1 : ℝ) ≤ (3 : ℝ) ^ N := one_le_pow₀ (by norm_num)
      rw [inv_le_one₀ (by positivity)]
      exact h31
    have hd1 : dist (gpt N q) x ≤ 1 := by
      have hq2 : dist x (gpt N q) ≤ (3 : ℝ) ^ (-(N : ℤ)) := hqdist
      have hq3 : dist (gpt N q) x ≤ (3 : ℝ) ^ (-(N : ℤ)) := by
        rw [dist_comm]; exact hq2
      linarith
    calc dist (gpt N q) z ≤ dist (gpt N q) x + dist x z := dist_triangle _ _ _
      _ ≤ 1 + r / 2 := by linarith
      _ ≤ r / 2 + 1 := by linarith
  have hterm : ∀ j : ℕ, |om (-(Int.ofNat j)) x - om (-(Int.ofNat j)) (gpt N q)| ≤
      Vr (om (-(Int.ofNat j))) * dist x (gpt N q) := by
    intro j
    by_cases hxy : x = gpt N q
    · rw [hxy]
      simp
    · have hne : (⟨x, hxK⟩ : (K : Set (SpatialCoordinates d))) ≠ ⟨gpt N q, hy0K⟩ := by
        intro h
        exact hxy (congrArg Subtype.val h)
      have hr0 := hom (-(Int.ofNat j)) ⟨x, hxK⟩ ⟨gpt N q, hy0K⟩ hne
      have hd0 : 0 < dist x (gpt N q) := dist_pos.mpr hxy
      exact (div_le_iff₀ hd0).mp hr0
  have hsumsplit : |∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x| ≤
      Amax N om + Aosc N om := by
    have hgrid : |∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) (gpt N q)| ≤ Amax N om := by
      rw [hAmaxdef]
      exact Finset.le_sup' (f := fun q =>
        |∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) (gpt N q)|) hqmem
    have hdiff : |(∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x) -
        ∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) (gpt N q)| ≤ Aosc N om := by
      have h1 : |(∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x) -
          ∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) (gpt N q)| ≤
          ∑ j ∈ Finset.range (N + 1),
            |om (-(Int.ofNat j)) x - om (-(Int.ofNat j)) (gpt N q)| := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.abs_sum_le_sum_abs _ _
      have h2 : (∑ j ∈ Finset.range (N + 1),
          |om (-(Int.ofNat j)) x - om (-(Int.ofNat j)) (gpt N q)|) ≤
          ∑ j ∈ Finset.range (N + 1), Vr (om (-(Int.ofNat j))) * dist x (gpt N q) :=
        Finset.sum_le_sum (fun j _ => hterm j)
      have hqdist' : dist x (gpt N q) ≤ (3 : ℝ) ^ (-(N : ℤ)) := hqdist
      have hS : 0 ≤ ∑ j ∈ Finset.range (N + 1), Vr (om (-(Int.ofNat j))) :=
        Finset.sum_nonneg (fun j _ => hVr0 _)
      have h3 : (∑ j ∈ Finset.range (N + 1), Vr (om (-(Int.ofNat j))) * dist x (gpt N q)) ≤
          Aosc N om := by
        rw [← Finset.sum_mul]
        have hmul : (∑ j ∈ Finset.range (N + 1), Vr (om (-(Int.ofNat j)))) *
            dist x (gpt N q) ≤
            (∑ j ∈ Finset.range (N + 1), Vr (om (-(Int.ofNat j)))) * (3 : ℝ) ^ (-(N : ℤ)) :=
          mul_le_mul_of_nonneg_left hqdist' hS
        have heq : (∑ j ∈ Finset.range (N + 1), Vr (om (-(Int.ofNat j)))) *
            (3 : ℝ) ^ (-(N : ℤ)) = Aosc N om := by
          rw [hAoscdef]; ring
        linarith [heq ▸ hmul]
      linarith
    have h4 : |∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x| ≤
        |∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) (gpt N q)| +
        |(∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x) -
          ∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) (gpt N q)| := by
      have hab := abs_sub_abs_le_abs_sub
        (∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x)
        (∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) (gpt N q))
      linarith
    linarith
  rw [hlogid, abs_le]
  have htau0 : 0 ≤ ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := by
    have := M.G4.tauSq_pos.le
    positivity
  have hVVexp : 2 * ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P +
      Ah om + Amax N om + Aosc N om =
      ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P +
      ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P + Ah om + Amax N om + Aosc N om := by
    ring
  have hHb := abs_le.mp hHbound
  have hSb := abs_le.mp hsumsplit
  rw [hVVexp]
  constructor
  · linarith [hHb.1, hSb.1, hlogahom1]
  · linarith [hHb.2, hSb.2, hlogahom2]


/-- Packaging of the exponential-moment bound into the `L^p` statement with the
final constants. -/
theorem aux_finite_cutoff_log_abs_majorant_lp
    {Om : Type*} [MeasurableSpace Om] (mu : Measure Om) [IsProbabilityMeasure mu]
    (V : Om → ℝ) (hVm : Measurable V) (t p : ℝ) (htpos : 0 < t) (hpt : p ≤ t)
    (delta tau2 u0 u1 : ℝ) (hdelta : 0 < delta) (hdhalf : delta ≤ 1 / 2)
    (hu0nn : 0 ≤ u0) (_hu1nn : 0 ≤ u1)
    (htau2 : tau2 ≤ Real.log 2 / 2 * delta ^ 2) (N : ℕ)
    (hint : Integrable (fun w => Real.exp (t * V w)) mu)
    (hbd : (∫ w, Real.exp (t * V w) ∂mu) ≤
      Real.exp (t * (2 * ((N : ℝ) + 1) * tau2 +
        4 * delta * (Real.log 3 + u0 + u1 * (N : ℝ))))) :
    MemLp (fun w => Real.exp (V w)) (ENNReal.ofReal p) mu ∧
      eLpNorm (fun w => Real.exp (V w)) (ENNReal.ofReal p) mu ≤
        ENNReal.ofReal
          ((Real.exp 1 * Real.exp (2 * (Real.log 3 + u0)) + Real.log 2) *
            Real.exp (((4 * u1 + 1) * delta +
              (Real.exp 1 * Real.exp (2 * (Real.log 3 + u0)) + Real.log 2) * delta ^ 2) *
              (N : ℝ))) := by
  obtain ⟨hmem, hnorm⟩ := aux_finite_cutoff_log_abs_majorant_eLpNorm_exp mu V hVm t htpos
    hint (2 * ((N : ℝ) + 1) * tau2 + 4 * delta * (Real.log 3 + u0 + u1 * (N : ℝ))) hbd
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hlogu0 : 0 ≤ Real.log 3 + u0 := by linarith
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hd2 : delta ^ 2 ≤ 1 / 4 := by
    have h := pow_le_pow_left₀ hdelta.le hdhalf 2
    norm_num at h
    linarith
  have hA : 2 * ((N : ℝ) + 1) * tau2 ≤
      Real.log 2 * delta ^ 2 + (Real.log 2 * delta ^ 2) * (N : ℝ) := by
    have h1 : (0 : ℝ) ≤ 2 * ((N : ℝ) + 1) := by linarith
    have h2 := mul_le_mul_of_nonneg_left htau2 h1
    have h3 : 2 * ((N : ℝ) + 1) * (Real.log 2 / 2 * delta ^ 2) =
        Real.log 2 * delta ^ 2 + (Real.log 2 * delta ^ 2) * (N : ℝ) := by ring
    rw [h3] at h2
    exact h2
  have hC : 4 * delta * (Real.log 3 + u0) ≤ 2 * (Real.log 3 + u0) := by
    have h4 : 4 * delta ≤ 2 := by linarith
    have h5 := mul_le_mul_of_nonneg_right h4 hlogu0
    linarith
  have hD : Real.log 2 * delta ^ 2 ≤ 1 := by
    have h := mul_le_mul hlog2le hd2 (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    linarith
  have hcNle : 2 * ((N : ℝ) + 1) * tau2 + 4 * delta * (Real.log 3 + u0 + u1 * (N : ℝ)) ≤
      (1 + 2 * (Real.log 3 + u0)) +
        (Real.log 2 * delta ^ 2 + 4 * u1 * delta) * (N : ℝ) := by
    have hB : 4 * delta * (Real.log 3 + u0 + u1 * (N : ℝ))
        = 4 * delta * (Real.log 3 + u0) + (4 * u1 * delta) * (N : ℝ) := by ring
    have hE : (Real.log 2 * delta ^ 2 + 4 * u1 * delta) * (N : ℝ)
        = (Real.log 2 * delta ^ 2) * (N : ℝ) + (4 * u1 * delta) * (N : ℝ) := by ring
    rw [hB, hE]
    linarith
  have hPpos : (0 : ℝ) < Real.exp 1 * Real.exp (2 * (Real.log 3 + u0)) := by positivity
  refine ⟨hmem.mono_exponent (ENNReal.ofReal_le_ofReal hpt), ?_⟩
  calc eLpNorm (fun w => Real.exp (V w)) (ENNReal.ofReal p) mu
      ≤ eLpNorm (fun w => Real.exp (V w)) (ENNReal.ofReal t) mu :=
        eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpt) hmem.1
    _ ≤ ENNReal.ofReal (Real.exp (2 * ((N : ℝ) + 1) * tau2 +
          4 * delta * (Real.log 3 + u0 + u1 * (N : ℝ)))) := hnorm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hsplit : Real.exp ((1 + 2 * (Real.log 3 + u0)) +
            (Real.log 2 * delta ^ 2 + 4 * u1 * delta) * (N : ℝ)) =
            Real.exp (1 + 2 * (Real.log 3 + u0)) *
              Real.exp ((Real.log 2 * delta ^ 2 + 4 * u1 * delta) * (N : ℝ)) :=
          Real.exp_add _ _
        refine le_trans (Real.exp_le_exp.mpr hcNle) ?_
        rw [hsplit]
        refine mul_le_mul ?_ ?_ (Real.exp_pos _).le (by linarith)
        · rw [Real.exp_add]
          linarith
        · refine Real.exp_le_exp.mpr ?_
          refine mul_le_mul_of_nonneg_right ?_ hNnn
          have hPd : (0 : ℝ) ≤ (Real.exp 1 * Real.exp (2 * (Real.log 3 + u0))) *
              delta ^ 2 := by positivity
          linarith [hdelta.le]




theorem finite_cutoff_log_abs_majorant :
  ∀ (d : ℕ), 2 ≤ d →
  ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)],
  ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
  ∀ (p : ℝ), 1 ≤ p →
  ∀ (Cg Cu : ℝ), 0 < Cg → 0 < Cu →
  ∃ C0 Cd cd : ℝ, 0 < C0 ∧ 0 < Cd ∧ 0 < cd ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (_Rm : in_responses d M)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredAdmissible M H → M.delta ≤ cd / p →
      ∀ (G : BilateralField d → ℝ)
        (U : ℕ → BilateralField d → ℝ),
        ((∀ om, 0 ≤ G om) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
          ∀ x y, x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
            y ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
            |H om x - H om y| ≤ G om * dist x y) ∧
        MemLp G (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
        eLpNorm G (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cg * M.delta * Real.sqrt p)) →
        ((∀ N om, 0 ≤ U N om) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
          ∀ N x y,
            x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
            y ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
            |(∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x) -
                ∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) y| ≤
              U N om * (3 : ℝ) ^ N * dist x y) ∧
        (∀ N, MemLp (U N) (ENNReal.ofReal p)
          (chaosSampleLaw M).toMeasure) ∧
        (∀ N, eLpNorm (U N) (ENNReal.ofReal p)
            (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cu * M.delta * Real.sqrt (1 + (N : ℝ))))) →
        ∃ V : ℕ → BilateralField d → ℝ,
          (∀ N om, 0 ≤ V N om) ∧
          (∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
            ∀ N x, x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
              |Real.log (cutoffCoefficient M H om N x)| ≤ V N om) ∧
          (∀ N, MemLp (fun om => Real.exp (V N om))
            (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
          (∀ N, eLpNorm (fun om => Real.exp (V N om))
              (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal
              (C0 * Real.exp ((Cd * M.delta + C0 * M.delta ^ 2) * (N : ℝ)))) := by
  classical
  intro d hd instMS instBS z r hr p hp Cg Cu hCg hCu
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hr4 : (0 : ℝ) < r + 4 := by linarith
  set K : Compacts (SpatialCoordinates d) := closedCube z (r + 4) hr4 with hKdef
  set Bnd : ℝ := ‖z‖ + (r + 4) / 2 with hBnd
  have hKnorm : ∀ x : K, ‖(x : SpatialCoordinates d)‖ ≤ Bnd := by
    intro x
    have hx : dist (x : SpatialCoordinates d) z ≤ (r + 4) / 2 := x.2
    have hx' : ‖(x : SpatialCoordinates d) - z‖ ≤ (r + 4) / 2 := by
      rwa [dist_eq_norm] at hx
    calc ‖(x : SpatialCoordinates d)‖ = ‖z + ((x : SpatialCoordinates d) - z)‖ := by
          rw [add_sub_cancel]
      _ ≤ ‖z‖ + ‖(x : SpatialCoordinates d) - z‖ := norm_add_le _ _
      _ ≤ Bnd := by rw [hBnd]; linarith
  obtain ⟨Q1, hQ1⟩ := aux_finite_cutoff_log_abs_majorant_exists_pow_half (‖z‖ + r / 2)
  obtain ⟨CHf, hCHf0, hCHfb⟩ :=
    exists_uniform_compactExponentialMoment_of_admissible hd
  obtain ⟨Vr, hVrmeas, hVr0, hVrdom, hVrle, hVrset⟩ :=
    aux_finite_negative_layer_log_lipschitz_majorant_continuous_ratio K
  obtain ⟨Q0, hQ0⟩ := aux_finite_cutoff_log_abs_majorant_exists_pow Bnd
  set Cval : ℝ := 6 * Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2 *
    ((1 + Real.log 2) ^ (2 : ℝ)⁻¹) with hCval
  set E0 : ℝ := 5 * (1 + Real.log 2 + (d : ℝ) * ((Q0 : ℝ) + 3) * Real.log 3) with hE0
  have hE0pos : 0 < E0 := by
    rw [hE0]
    have h : (0 : ℝ) ≤ (d : ℝ) * ((Q0 : ℝ) + 3) * Real.log 3 := by positivity
    linarith
  set u1 : ℝ := (d : ℝ) * Real.log 3 + Cval ^ 2 / 4 + (9 / 16) * E0 with hu1
  set u0 : ℝ := 3 * Real.log 2 + CHf K / 4 + (d : ℝ) * ((Q1 : ℝ) + 2) * Real.log 3 +
    Cval ^ 2 / 4 + (9 / 16) * E0 with hu0
  have hu1nn : 0 ≤ u1 := by
    rw [hu1]
    have h1 : (0 : ℝ) ≤ (d : ℝ) * Real.log 3 := by positivity
    have h2 : (0 : ℝ) ≤ Cval ^ 2 / 4 := by positivity
    have h3 : (0 : ℝ) ≤ (9 / 16) * E0 := by linarith
    linarith
  have hu0nn : 0 ≤ u0 := by
    rw [hu0]
    have h1 : (0 : ℝ) ≤ (d : ℝ) * ((Q1 : ℝ) + 2) * Real.log 3 := by positivity
    have h2 : (0 : ℝ) ≤ Cval ^ 2 / 4 := by positivity
    have h3 : (0 : ℝ) ≤ (9 / 16) * E0 := by linarith
    have h4 : (0 : ℝ) ≤ CHf K / 4 := by linarith [hCHf0 K]
    linarith
  refine ⟨Real.exp 1 * Real.exp (2 * (Real.log 3 + u0)) + Real.log 2, 4 * u1 + 1, 1 / 4,
    by positivity, by linarith, by norm_num, ?_⟩
  intro M Rm H hH hdel G U hGpack hUpack
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hdhalf : M.delta ≤ 1 / 2 := M.shellPrefix.delta_le_half
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  set t : ℝ := 1 / (4 * M.delta) with ht
  have htpos : 0 < t := by rw [ht]; positivity
  have hpt : p ≤ t := by
    rw [ht, le_div_iff₀ (by positivity)]
    have h1 : M.delta * p ≤ 1 / 4 := by
      have := (le_div_iff₀ hp0).mp hdel
      linarith
    linarith
  set mu0 : Measure (NativeBilateralPotentialSample d) :=
    Measure.infinitePi (fun _ : ℤ =>
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure) with hmu0
  set forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩ with hforget
  set pz : NativeBilateralPotentialSample d → BilateralField d :=
    fun omega j => layerScaling d j (forget (omega j)) with hpz
  have hpzmeas : Measurable pz := by
    apply measurable_pi_lambda
    intro j
    exact (layerScaling d j).continuous.measurable.comp
      (forget.continuous.measurable.comp (measurable_pi_apply j))
  have hpzmap : Measure.map pz mu0 = (chaosSampleLaw M).toMeasure := by
    simpa only [chaosSampleLaw, chaosRootFieldLaw, hmu0, hpz, hforget, Function.comp_apply] using
      (measurePreserving_nativeCopies_commonScaleLaw M).map_eq
  have hpzapp : ∀ (w : NativeBilateralPotentialSample d) (j : ℕ) (y : SpatialCoordinates d),
      (pz w) (-(Int.ofNat j)) y = (w (-(j : ℤ))) ((3 : ℝ) ^ (j : ℤ) • y) := by
    intro w j y
    show (layerScaling d (-(Int.ofNat j)) (forget (w (-(Int.ofNat j))))) y = _
    simp [layerScaling, ContinuousMap.compRightContinuousMap, hforget]
  set gpt : ℕ → (Fin d → ℤ) → SpatialCoordinates d := fun N q =>
    (3 : ℝ) ^ (-(N : ℤ)) • SubdiffusiveProcess.CoarseGrainingVocab.shellCoverCenter q with hgpt
  set Amax : ℕ → BilateralField d → ℝ := fun N om =>
    (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((N : ℤ) + (Q1 : ℤ))).sup'
      (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((N : ℤ) + (Q1 : ℤ)))
      (fun q => |∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) (gpt N q)|) with hAmax
  set Aosc : ℕ → BilateralField d → ℝ := fun N om =>
    (3 : ℝ) ^ (-(N : ℤ)) * ∑ j ∈ Finset.range (N + 1), Vr (om (-(Int.ofNat j))) with hAosc
  set Ah : BilateralField d → ℝ := fun om =>
    ‖(H om).restrict (K : Set (SpatialCoordinates d))‖ with hAh
  set VV : ℕ → BilateralField d → ℝ := fun N om =>
    2 * ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P + Ah om + Amax N om + Aosc N om with hVV
  -- measurability
  have hevmeas : ∀ (j : ℤ) (y : SpatialCoordinates d),
      Measurable (fun om : BilateralField d => om j y) := by
    intro j y
    exact ((continuous_eval_const y).measurable).comp (measurable_pi_apply j)
  have hAhmeas : Measurable Ah :=
    aux_finite_cutoff_log_abs_majorant_restrict_measurable K H hH.measurable
  have hAmaxmeas : ∀ N, Measurable (Amax N) := by
    intro N
    have h0 : Measurable
        ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((N : ℤ) + (Q1 : ℤ))).sup'
          (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((N : ℤ) + (Q1 : ℤ)))
          (fun q (om : BilateralField d) =>
            |∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) (gpt N q)|)) := by
      refine Finset.measurable_sup' _ (fun q _ => ?_)
      exact (Finset.measurable_sum _ (fun j _ => hevmeas (-(Int.ofNat j)) (gpt N q))).abs
    have h1 : ((SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts d ((N : ℤ) + (Q1 : ℤ))).sup'
        (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((N : ℤ) + (Q1 : ℤ)))
        (fun q (om : BilateralField d) =>
          |∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) (gpt N q)|)) = Amax N := by
      funext om
      exact Finset.sup'_apply _ _ om
    rwa [h1] at h0
  have hAoscmeas : ∀ N, Measurable (Aosc N) := by
    intro N
    refine measurable_const.mul (Finset.measurable_sum _ (fun j _ => ?_))
    exact hVrmeas.comp (measurable_pi_apply _)
  have hVVmeas : ∀ N, Measurable (VV N) := by
    intro N
    exact ((measurable_const.add hAhmeas).add (hAmaxmeas N)).add (hAoscmeas N)
  have hAmax0 : ∀ N om, 0 ≤ Amax N om := by
    intro N om
    obtain ⟨q, hq⟩ := SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d ((N : ℤ) + (Q1 : ℤ))
    exact le_trans (abs_nonneg _) (Finset.le_sup' (f := fun q =>
      |∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) (gpt N q)|) hq)
  have hAosc0 : ∀ N om, 0 ≤ Aosc N om := by
    intro N om
    rw [hAosc]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => hVr0 _))
  have hVV0 : ∀ N om, 0 ≤ VV N om := by
    intro N om
    have htau : 0 ≤ SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := M.G4.tauSq_pos.le
    have h1 : 0 ≤ 2 * ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := by positivity
    have h2 : 0 ≤ Ah om := norm_nonneg _
    have := hAmax0 N om
    have := hAosc0 N om
    rw [hVV]
    simp only
    linarith
  set cN : ℕ → ℝ := fun N => 2 * ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P +
    4 * M.delta * (Real.log 3 + u0 + u1 * (N : ℝ)) with hcN
  have h4dt : 4 * M.delta * t = 1 := by rw [ht]; field_simp
  have hu0a : Real.log 2 + CHf K / 4 ≤ u0 := by
    rw [hu0]
    have h1 : (0 : ℝ) ≤ (d : ℝ) * ((Q1 : ℝ) + 2) * Real.log 3 := by positivity
    have h2 : (0 : ℝ) ≤ Cval ^ 2 / 4 := by positivity
    have h3 : (0 : ℝ) ≤ (9 / 16) * E0 := by linarith
    linarith
  have hu0b : Real.log 2 + (d : ℝ) * ((Q1 : ℝ) + 2) * Real.log 3 + Cval ^ 2 / 4 ≤ u0 := by
    rw [hu0]
    have h3 : (0 : ℝ) ≤ (9 / 16) * E0 := by linarith
    have h4 : (0 : ℝ) ≤ CHf K / 4 := by linarith [hCHf0 K]
    linarith
  have hu1b : (d : ℝ) * Real.log 3 + Cval ^ 2 / 4 ≤ u1 := by
    rw [hu1]
    have h3 : (0 : ℝ) ≤ (9 / 16) * E0 := by linarith
    linarith
  have hu0c : Real.log 2 + (9 / 16) * E0 ≤ u0 := by
    rw [hu0]
    have h1 : (0 : ℝ) ≤ (d : ℝ) * ((Q1 : ℝ) + 2) * Real.log 3 := by positivity
    have h2 : (0 : ℝ) ≤ Cval ^ 2 / 4 := by positivity
    have h4 : (0 : ℝ) ≤ CHf K / 4 := by linarith [hCHf0 K]
    linarith
  have hu1c : (9 / 16) * E0 ≤ u1 := by
    rw [hu1]
    have h1 : (0 : ℝ) ≤ (d : ℝ) * Real.log 3 := by positivity
    have h2 : (0 : ℝ) ≤ Cval ^ 2 / 4 := by positivity
    linarith
  set cN : ℕ → ℝ := fun N => 2 * ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P +
    4 * M.delta * (Real.log 3 + u0 + u1 * (N : ℝ)) with hcN
  have hkey : ∀ N : ℕ,
      Integrable (fun om => Real.exp (t * VV N om)) (chaosSampleLaw M).toMeasure ∧
      (∫ om, Real.exp (t * VV N om) ∂(chaosSampleLaw M).toMeasure) ≤
        Real.exp (t * cN N) := by
    intro N
    exact aux_finite_cutoff_log_abs_majorant_moment M H K Bnd hKnorm Q0 Q1 hQ0 Vr hVr0 hVrle
      (CHf K) (hCHf0 K) (fun lam hlam => hCHfb M H hH K lam hlam) Cval E0 u0 u1 t
      hCval hE0 hu1nn hu0a hu0b hu1b hu0c hu1c ht Ah (fun om => rfl) hAhmeas
      Amax (fun N om => rfl) hAmaxmeas Aosc (fun N om => rfl) hAoscmeas N
  have hKcontains : ∀ u : SpatialCoordinates d, dist u z ≤ r / 2 + 1 →
      u ∈ (K : Set (SpatialCoordinates d)) := by
    intro u hu
    show dist u z ≤ (r + 4) / 2
    linarith
  refine ⟨VV, hVV0, ?_, ?_, ?_⟩
  · have henv := aux_finite_cutoff_log_abs_majorant_envelope M Rm H z r hr K Bnd hKnorm
      hKcontains Q1 hQ1 Vr hVr0 hVrdom hVrset Ah (fun om => rfl) Amax (fun N om => rfl)
      Aosc (fun N om => rfl)
    exact henv
  · intro N
    exact (aux_finite_cutoff_log_abs_majorant_lp (chaosSampleLaw M).toMeasure (VV N)
      (hVVmeas N) t p htpos hpt M.delta (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) u0 u1 hdelta
      hdhalf hu0nn hu1nn (SubdiffusiveProcess.CoarseGrainingVocab.tauSq_le_delta_sq M) N
      (hkey N).1 (hkey N).2).1
  · intro N
    exact (aux_finite_cutoff_log_abs_majorant_lp (chaosSampleLaw M).toMeasure (VV N)
      (hVVmeas N) t p htpos hpt M.delta (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) u0 u1 hdelta
      hdhalf hu0nn hu1nn (SubdiffusiveProcess.CoarseGrainingVocab.tauSq_le_delta_sq M) N
      (hkey N).1 (hkey N).2).2



end Paper
