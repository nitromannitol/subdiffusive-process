module

public import SubdiffusiveProcess.Probability.NativeLayerOrlicz
public import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedProviders
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Discharge
public import SubdiffusiveProcess.Paper.primitive_scores
public import Mathlib.Tactic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import SubdiffusiveProcess.Paper.layer_regularity_moments
public import SubdiffusiveProcess.Paper.in_responses

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section
namespace Paper

open SubdiffusiveProcess.Frozen.Assumptions

variable {d : ℕ}



theorem aux_psf_deriv_translate (z : Vec d) (g : PotentialField d) (x : Vec d) :
    PotentialField.deriv (PotentialField.translate z g) x =
      PotentialField.deriv g (x + z) := by
  have h1 : HasFDerivAt (fun y : Vec d => (g : Vec d → ℝ) (y + z))
      (PotentialField.deriv g (x + z)) x := by
    simpa using! (g.hasFDerivAt (x + z)).comp x ((hasFDerivAt_id x).add_const z)
  have h2 : HasFDerivAt (fun y : Vec d => (g : Vec d → ℝ) (y + z))
      (PotentialField.deriv (PotentialField.translate z g) x) x := by
    have := (PotentialField.translate z g).hasFDerivAt x
    simpa [PotentialField.translate_apply] using! this
  exact h2.unique h1

/-- The per-cell observable: it dominates one layer's value and scaled gradient on the
unit cell centred at `y`. -/
def aux_psf_cellObs (i : ℕ) (y : Vec d) (omega : PotentialSample d) : ℝ :=
  (PotentialField.translate y (omega i)).unitCubeValueNorm +
    (3 : ℝ) ^ i * (d : ℝ) *
      (PotentialField.translate y (omega i)).unitCubeDerivNorm

theorem aux_psf_cellObs_nonneg (i : ℕ) (y : Vec d) (omega : PotentialSample d) :
    0 ≤ aux_psf_cellObs i y omega := by
  have h1 := PotentialField.unitCubeValueNorm_nonneg
    (PotentialField.translate y (omega i))
  have h2 := PotentialField.unitCubeDerivNorm_nonneg
    (PotentialField.translate y (omega i))
  have h3 : (0:ℝ) ≤ (3 : ℝ) ^ i * (d : ℝ) := by positivity
  unfold aux_psf_cellObs
  nlinarith

theorem aux_psf_abs_le_cellObs (i : ℕ) (y x : Vec d) (omega : PotentialSample d)
    (hx : x - y ∈ cube d 0) :
    |omega i x| ≤ (PotentialField.translate y (omega i)).unitCubeValueNorm := by
  have h := PotentialField.abs_apply_le_unitCubeValueNorm
    (PotentialField.translate y (omega i)) (x := x - y) hx
  have hval : PotentialField.translate y (omega i) (x - y) = omega i x := by
    rw [PotentialField.translate_apply, sub_add_cancel]
  simpa [hval] using h

theorem aux_psf_grad_le_cellObs (i : ℕ) (y x : Vec d) (omega : PotentialSample d)
    (hx : x - y ∈ cube d 0) :
    Homogenization.euclideanNorm (shellGradient (omega i) x) ≤
      (d : ℝ) * (PotentialField.translate y (omega i)).unitCubeDerivNorm := by
  have hpi : ‖shellGradient (omega i) x‖ ≤
      ‖PotentialField.deriv (omega i) x‖ := by
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro k
    rw [Real.norm_eq_abs]
    calc
      |shellGradient (omega i) x k| =
          ‖PotentialField.deriv (omega i) x (Pi.single k (1 : ℝ) : Vec d)‖ := by
        rw [Real.norm_eq_abs]; rfl
      _ ≤ ‖PotentialField.deriv (omega i) x‖ * ‖(Pi.single k (1 : ℝ) : Vec d)‖ :=
        (PotentialField.deriv (omega i) x).le_opNorm _
      _ = ‖PotentialField.deriv (omega i) x‖ := by
        rw [Pi.norm_single]; norm_num
  have hd : ‖PotentialField.deriv (omega i) x‖ ≤
      (PotentialField.translate y (omega i)).unitCubeDerivNorm := by
    have h := PotentialField.norm_deriv_le_unitCubeDerivNorm
      (PotentialField.translate y (omega i)) (x := x - y) hx
    rwa [aux_psf_deriv_translate, sub_add_cancel] at h
  calc
    Homogenization.euclideanNorm (shellGradient (omega i) x) ≤
        (d : ℝ) * ‖shellGradient (omega i) x‖ :=
      Homogenization.euclideanNorm_le_dimension_mul_norm _
    _ ≤ (d : ℝ) * ‖PotentialField.deriv (omega i) x‖ :=
      mul_le_mul_of_nonneg_left hpi (Nat.cast_nonneg d)
    _ ≤ (d : ℝ) * (PotentialField.translate y (omega i)).unitCubeDerivNorm :=
      mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg d)

theorem aux_psf_le_cellObs (i : ℕ) (y x : Vec d) (omega : PotentialSample d)
    (hx : x - y ∈ cube d 0) :
    |omega i x| +
        (3 : ℝ) ^ i * Homogenization.euclideanNorm (shellGradient (omega i) x) ≤
      aux_psf_cellObs i y omega := by
  have h1 := aux_psf_abs_le_cellObs i y x omega hx
  have h2 := aux_psf_grad_le_cellObs i y x omega hx
  have h3 : (0:ℝ) < (3 : ℝ) ^ i := by positivity
  unfold aux_psf_cellObs
  nlinarith



theorem aux_psf_mem_translatedCube_iff {m : ℤ} {z x : Vec d} :
    x ∈ translatedCube d m z ↔ ∀ i, |x i - z i| < (3 : ℝ) ^ m / 2 := by
  constructor
  · rintro ⟨u, hu, rfl⟩ i
    rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at hu
    have := hu i
    rw [abs_lt]
    constructor <;> simp only [Pi.add_apply] <;> linarith [this.1, this.2]
  · intro hx
    refine ⟨x - z, ?_, by ext i; simp⟩
    rw [cube, Homogenization.mem_openCubeSet_originCube_iff]
    intro i
    have := hx i
    rw [abs_lt] at this
    constructor <;> simp only [Pi.sub_apply] <;> linarith [this.1, this.2]

theorem aux_psf_mem_cube_zero_iff {x : Vec d} :
    x ∈ cube d 0 ↔ ∀ i, |x i| < 1 / 2 := by
  rw [cube, Homogenization.mem_openCubeSet_originCube_iff]
  constructor
  · intro hx i
    have := hx i
    rw [abs_lt]
    norm_num at this ⊢
    exact ⟨this.1, this.2⟩
  · intro hx i
    have := hx i
    rw [abs_lt] at this
    norm_num
    exact ⟨this.1, this.2⟩

/-- Centres of the unit cells covering `translatedCube d n z`. -/
def aux_psf_center (n : ℕ) (z : Vec d) (k : Fin d → ℕ) : Vec d :=
  fun i => z i - (3 : ℝ) ^ n / 2 + (k i : ℝ) / 2

theorem aux_psf_cover (n : ℕ) (z x : Vec d)
    (hx : x ∈ translatedCube d (n : ℤ) z) :
    ∃ k : Fin d → Fin (2 * 3 ^ n + 1),
      x - aux_psf_center n z (fun i => ((k i : ℕ))) ∈ cube d 0 := by
  have hx' : ∀ i, |x i - z i| < (3 : ℝ) ^ n / 2 := by
    have := aux_psf_mem_translatedCube_iff.1 hx
    simpa only [zpow_natCast] using this
  refine ⟨fun i => ⟨⌊2 * (x i - z i + (3 : ℝ) ^ n / 2)⌋₊, ?_⟩, ?_⟩
  · have h := hx' i
    rw [abs_lt] at h
    have hnn : (0:ℝ) ≤ 2 * (x i - z i + (3 : ℝ) ^ n / 2) := by linarith [h.1]
    rw [Nat.floor_lt hnn]
    have : ((2 * 3 ^ n + 1 : ℕ) : ℝ) = 2 * (3:ℝ) ^ n + 1 := by push_cast; ring
    rw [this]
    linarith [h.2]
  · rw [aux_psf_mem_cube_zero_iff]
    intro i
    have h := hx' i
    rw [abs_lt] at h
    have hnn : (0:ℝ) ≤ 2 * (x i - z i + (3 : ℝ) ^ n / 2) := by linarith [h.1]
    have hfl : ((⌊2 * (x i - z i + (3 : ℝ) ^ n / 2)⌋₊ : ℕ) : ℝ) ≤
        2 * (x i - z i + (3 : ℝ) ^ n / 2) := Nat.floor_le hnn
    have hfu : 2 * (x i - z i + (3 : ℝ) ^ n / 2) <
        ((⌊2 * (x i - z i + (3 : ℝ) ^ n / 2)⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hval : (x - aux_psf_center n z
        (fun i => (⌊2 * (x i - z i + (3 : ℝ) ^ n / 2)⌋₊ : ℕ))) i
        = (2 * (x i - z i + (3 : ℝ) ^ n / 2) -
            ((⌊2 * (x i - z i + (3 : ℝ) ^ n / 2)⌋₊ : ℕ) : ℝ)) / 2 := by
      simp only [Pi.sub_apply, aux_psf_center]
      ring
    rw [hval, abs_lt]
    constructor <;> linarith



theorem aux_psf_deriv_spatialScale (r : ℝ) (g : PotentialField d) (x : Vec d) :
    PotentialField.deriv (PotentialField.spatialScale r g) x =
      r • PotentialField.deriv g (r • x) := by
  have h1 : HasFDerivAt (fun y : Vec d => (g : Vec d → ℝ) (r • y))
      (r • PotentialField.deriv g (r • x)) x := by
    have hc : HasFDerivAt (fun y : Vec d => r • y)
        (r • ContinuousLinearMap.id ℝ (Vec d)) x := by
      simpa using (r • ContinuousLinearMap.id ℝ (Vec d)).hasFDerivAt (x := x)
    have := (g.hasFDerivAt (r • x)).comp x hc
    simpa [ContinuousLinearMap.comp_smul] using! this
  have h2 : HasFDerivAt (fun y : Vec d => (g : Vec d → ℝ) (r • y))
      (PotentialField.deriv (PotentialField.spatialScale r g) x) x := by
    have := (PotentialField.spatialScale r g).hasFDerivAt x
    simpa [PotentialField.spatialScale_apply] using! this
  exact h2.unique h1

theorem aux_psf_smul_mem_cube_zero {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    {x : Vec d} (hx : x ∈ cube d 0) : r • x ∈ cube d 0 := by
  rw [aux_psf_mem_cube_zero_iff] at hx ⊢
  intro i
  have := hx i
  have hxi : |(r • x) i| = r * |x i| := by
    simp [abs_mul, abs_of_nonneg hr0]
  rw [hxi]
  nlinarith [abs_nonneg (x i)]

theorem aux_psf_scale_value (i : ℕ) (g : PotentialField d) :
    (PotentialField.triadicScale i g).unitCubeValueNorm ≤
      g.unitCubeValueNorm := by
  have hr0 : (0:ℝ) ≤ ((3:ℝ) ^ i)⁻¹ := by positivity
  have hr1 : ((3:ℝ) ^ i)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    exact one_le_pow₀ (by norm_num)
  rw [PotentialField.unitCubeValueNorm]
  refine csSup_le ⟨0, ⟨none, rfl⟩⟩ ?_
  rintro b ⟨o, rfl⟩
  cases o with
  | none => exact PotentialField.unitCubeValueNorm_nonneg g
  | some x =>
      have hx : ((3:ℝ) ^ i)⁻¹ • x.1 ∈ cube d 0 :=
        aux_psf_smul_mem_cube_zero hr0 hr1 x.2
      have := PotentialField.abs_apply_le_unitCubeValueNorm g (x := ((3:ℝ) ^ i)⁻¹ • x.1) hx
      simpa [PotentialField.triadicScale_apply] using this

theorem aux_psf_scale_deriv (i : ℕ) (g : PotentialField d) :
    (3:ℝ) ^ i * (PotentialField.triadicScale i g).unitCubeDerivNorm ≤
      g.unitCubeDerivNorm := by
  have hpos : (0:ℝ) < (3:ℝ) ^ i := by positivity
  have hr0 : (0:ℝ) ≤ ((3:ℝ) ^ i)⁻¹ := by positivity
  have hr1 : ((3:ℝ) ^ i)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have hkey : (PotentialField.triadicScale i g).unitCubeDerivNorm ≤
      ((3:ℝ) ^ i)⁻¹ * g.unitCubeDerivNorm := by
    rw [PotentialField.unitCubeDerivNorm]
    refine csSup_le ⟨0, ⟨none, rfl⟩⟩ ?_
    rintro b ⟨o, rfl⟩
    cases o with
    | none =>
        have := PotentialField.unitCubeDerivNorm_nonneg g
        positivity
    | some x =>
        have hx : ((3:ℝ) ^ i)⁻¹ • x.1 ∈ cube d 0 :=
          aux_psf_smul_mem_cube_zero hr0 hr1 x.2
        have hb := PotentialField.norm_deriv_le_unitCubeDerivNorm g
          (x := ((3:ℝ) ^ i)⁻¹ • x.1) hx
        have hderiv : PotentialField.deriv (PotentialField.triadicScale i g) x.1 =
            ((3:ℝ) ^ i)⁻¹ • PotentialField.deriv g (((3:ℝ) ^ i)⁻¹ • x.1) :=
          aux_psf_deriv_spatialScale _ _ _
        show ‖PotentialField.deriv (PotentialField.triadicScale i g) x.1‖ ≤
          ((3:ℝ) ^ i)⁻¹ * g.unitCubeDerivNorm
        rw [hderiv, norm_smul]
        simp only [norm_inv, Real.norm_eq_abs, abs_of_pos hpos]
        exact mul_le_mul_of_nonneg_left hb (by positivity)
  calc
    (3:ℝ) ^ i * (PotentialField.triadicScale i g).unitCubeDerivNorm ≤
        (3:ℝ) ^ i * (((3:ℝ) ^ i)⁻¹ * g.unitCubeDerivNorm) :=
      mul_le_mul_of_nonneg_left hkey hpos.le
    _ = g.unitCubeDerivNorm := by field_simp



theorem aux_psf_translate_triadicScale (i : ℕ) (y : Vec d) (g : PotentialField d) :
    PotentialField.translate y (PotentialField.triadicScale i g) =
      PotentialField.triadicScale i
        (PotentialField.translate (((3:ℝ) ^ i)⁻¹ • y) g) := by
  apply PotentialField.ext
  intro x
  simp [PotentialField.translate_apply, PotentialField.triadicScale_apply,
    smul_add]

theorem aux_psf_map_cell (M : GMCModel d) (i : ℕ) (y : Vec d) :
    Measure.map (fun omega : PotentialSample d =>
        PotentialField.translate y (omega i)) M.P.toMeasure =
      Measure.map (PotentialField.triadicScale i)
        (zeroPotentialLaw M.P).toMeasure := by
  have hcoord := measurable_potentialCoordinate (d := d) i
  have htr := PotentialField.measurable_translate (d := d) y
  have hts := PotentialField.measurable_triadicScale (d := d) i
  have hmarg : (potentialMarginalLaw M.P i).toMeasure =
      Measure.map (fun omega : PotentialSample d => omega i) M.P.toMeasure := by
    rw [potentialMarginalLaw, ProbabilityMeasure.toMeasure_map]
  calc
    Measure.map (fun omega : PotentialSample d =>
          PotentialField.translate y (omega i)) M.P.toMeasure =
        Measure.map (PotentialField.translate y)
          (Measure.map (fun omega : PotentialSample d => omega i) M.P.toMeasure) :=
      (Measure.map_map htr hcoord).symm
    _ = Measure.map (PotentialField.translate y)
          (potentialMarginalLaw M.P i).toMeasure := by rw [hmarg]
    _ = Measure.map (PotentialField.translate y)
          (Measure.map (PotentialField.triadicScale i)
            (zeroPotentialLaw M.P).toMeasure) := by
      rw [M.shellPrefix.marginal_scaling i, ProbabilityMeasure.toMeasure_map]
    _ = Measure.map (fun g => PotentialField.translate y
          (PotentialField.triadicScale i g)) (zeroPotentialLaw M.P).toMeasure :=
      Measure.map_map htr hts
    _ = Measure.map (fun g => PotentialField.triadicScale i
          (PotentialField.translate (((3:ℝ) ^ i)⁻¹ • y) g))
          (zeroPotentialLaw M.P).toMeasure := by
      congr 1
      funext g
      exact aux_psf_translate_triadicScale i y g
    _ = Measure.map (PotentialField.triadicScale i)
          (Measure.map (PotentialField.translate (((3:ℝ) ^ i)⁻¹ • y))
            (zeroPotentialLaw M.P).toMeasure) :=
      (Measure.map_map hts (PotentialField.measurable_translate _)).symm
    _ = Measure.map (PotentialField.triadicScale i)
          (zeroPotentialLaw M.P).toMeasure := by
      rw [M.G1.stationary]

theorem aux_psf_lintegral_cell (M : GMCModel d) (i : ℕ) (y : Vec d)
    {F : PotentialField d → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ omega, F (PotentialField.translate y (omega i)) ∂M.P.toMeasure =
      ∫⁻ g, F (PotentialField.triadicScale i g)
        ∂(zeroPotentialLaw M.P).toMeasure := by
  have hmap : Measurable (fun omega : PotentialSample d =>
      PotentialField.translate y (omega i)) :=
    (PotentialField.measurable_translate y).comp
      (measurable_potentialCoordinate (d := d) i)
  rw [← lintegral_map hF hmap, aux_psf_map_cell M i y,
    lintegral_map hF (PotentialField.measurable_triadicScale (d := d) i)]



theorem aux_psf_orlicz (M : GMCModel d) :
    (∫⁻ g, ENNReal.ofReal (Real.exp
        ((PotentialField.g2Observable g / M.delta) ^ (2:ℕ)))
      ∂(zeroPotentialLaw M.P).toMeasure) ≤ 2 := by
  set X : PotentialField d → ℝ := PotentialField.g2Observable with hX
  set mu : Measure (PotentialField d) := (zeroPotentialLaw M.P).toMeasure with hmu
  have hX0 : ∀ g, 0 ≤ X g := fun g => PotentialField.g2Observable_nonneg g
  have hreg : SubdiffusiveProcess.OGammaLE mu 2 M.delta X := M.G2.regularity_expectation
  rw [SubdiffusiveProcess.OGammaLE] at hreg
  have hInt : Integrable (fun g => Real.exp ((X g / M.delta) ^ (2 : ℕ))) mu := by
    convert hreg.1 using 1
    funext g
    rw [max_eq_left (hX0 g)]
    congr 1
    simp [div_eq_mul_inv, mul_comm]
  have hBound : (∫ g, Real.exp ((X g / M.delta) ^ (2 : ℕ)) ∂mu) ≤ 2 := by
    convert hreg.2 using 1
    congr 1
    funext g
    rw [max_eq_left (hX0 g)]
    congr 1
    simp [div_eq_mul_inv, mul_comm]
  have hEq := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
    (Filter.Eventually.of_forall fun g => (Real.exp_pos _).le)
  calc
    (∫⁻ g, ENNReal.ofReal (Real.exp ((X g / M.delta) ^ (2 : ℕ))) ∂mu) =
        ENNReal.ofReal (∫ g, Real.exp ((X g / M.delta) ^ (2 : ℕ)) ∂mu) := hEq.symm
    _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hBound
    _ = 2 := by norm_num



/-- The uniform sub-Gaussian scale of the per-cell observable. -/
def aux_psf_sigma (M : GMCModel d) : ℝ := (1 + (d : ℝ)) * M.delta

theorem aux_psf_sigma_pos (M : GMCModel d) : 0 < aux_psf_sigma M := by
  have hd := M.shellPrefix.delta_pos
  unfold aux_psf_sigma
  positivity

theorem aux_psf_cellObs_measurable (i : ℕ) (y : Vec d) :
    Measurable (fun omega : PotentialSample d => aux_psf_cellObs i y omega) := by
  have hmap : Measurable (fun omega : PotentialSample d =>
      PotentialField.translate y (omega i)) :=
    (PotentialField.measurable_translate y).comp
      (measurable_potentialCoordinate (d := d) i)
  exact (PotentialField.unitCubeValueNorm_measurable.comp hmap).add
    (((PotentialField.unitCubeDerivNorm_measurable.comp hmap)).const_mul _)

theorem aux_psf_cell_exp (M : GMCModel d) (i : ℕ) (y : Vec d) :
    (∫⁻ omega, ENNReal.ofReal (Real.exp
        ((aux_psf_cellObs i y omega / aux_psf_sigma M) ^ (2 : ℕ)))
      ∂M.P.toMeasure) ≤ 2 := by
  have hsig := aux_psf_sigma_pos M
  have hdelta := M.shellPrefix.delta_pos
  set psi : PotentialField d → ℝ := fun h =>
    h.unitCubeValueNorm + (3 : ℝ) ^ i * (d : ℝ) * h.unitCubeDerivNorm with hpsi
  have hF : Measurable (fun h : PotentialField d =>
      ENNReal.ofReal (Real.exp ((psi h / aux_psf_sigma M) ^ (2 : ℕ)))) := by
    have : Measurable psi :=
      PotentialField.unitCubeValueNorm_measurable.add
        (PotentialField.unitCubeDerivNorm_measurable.const_mul _)
    exact (((this.div_const _).pow_const _).exp).ennreal_ofReal
  have hrewrite : ∀ omega : PotentialSample d,
      aux_psf_cellObs i y omega = psi (PotentialField.translate y (omega i)) := by
    intro omega; rfl
  have hstep : (∫⁻ omega, ENNReal.ofReal (Real.exp
      ((aux_psf_cellObs i y omega / aux_psf_sigma M) ^ (2 : ℕ)))
      ∂M.P.toMeasure) =
      ∫⁻ g, ENNReal.ofReal (Real.exp
        ((psi (PotentialField.triadicScale i g) / aux_psf_sigma M) ^ (2 : ℕ)))
        ∂(zeroPotentialLaw M.P).toMeasure := by
    simp only [hrewrite]
    exact aux_psf_lintegral_cell M i y hF
  rw [hstep]
  refine le_trans (lintegral_mono fun g => ?_) (aux_psf_orlicz M)
  have hV : (PotentialField.triadicScale i g).unitCubeValueNorm ≤
      g.unitCubeValueNorm := aux_psf_scale_value i g
  have hD : (3 : ℝ) ^ i * (PotentialField.triadicScale i g).unitCubeDerivNorm ≤
      g.unitCubeDerivNorm := aux_psf_scale_deriv i g
  have hV0 := PotentialField.unitCubeValueNorm_nonneg g
  have hD0 := PotentialField.unitCubeDerivNorm_nonneg g
  have hL0 := PotentialField.unitCubeDerivLipschitzSeminorm_nonneg g
  have hpsi0 : 0 ≤ psi (PotentialField.triadicScale i g) := by
    have h1 := PotentialField.unitCubeValueNorm_nonneg
      (PotentialField.triadicScale i g)
    have h2 := PotentialField.unitCubeDerivNorm_nonneg
      (PotentialField.triadicScale i g)
    have h3 : (0:ℝ) ≤ (3 : ℝ) ^ i * (d : ℝ) := by positivity
    rw [hpsi]; nlinarith
  have hdle : psi (PotentialField.triadicScale i g) ≤
      (1 + (d : ℝ)) * PotentialField.g2Observable g := by
    have hDd : (3 : ℝ) ^ i * (d : ℝ) *
        (PotentialField.triadicScale i g).unitCubeDerivNorm ≤
        (d : ℝ) * g.unitCubeDerivNorm := by
      have : (d : ℝ) * ((3 : ℝ) ^ i *
          (PotentialField.triadicScale i g).unitCubeDerivNorm) ≤
          (d : ℝ) * g.unitCubeDerivNorm :=
        mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg d)
      nlinarith
    have hg2 : PotentialField.g2Observable g =
        g.unitCubeValueNorm + g.unitCubeDerivNorm +
          g.unitCubeDerivLipschitzSeminorm := rfl
    rw [hpsi, hg2]
    have hdn : (0:ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    nlinarith
  have hratio : psi (PotentialField.triadicScale i g) / aux_psf_sigma M ≤
      PotentialField.g2Observable g / M.delta := by
    rw [div_le_div_iff₀ hsig hdelta]
    have hg0 : (0:ℝ) ≤ PotentialField.g2Observable g :=
      PotentialField.g2Observable_nonneg g
    unfold aux_psf_sigma
    nlinarith
  have hsq : (psi (PotentialField.triadicScale i g) / aux_psf_sigma M) ^ (2:ℕ) ≤
      (PotentialField.g2Observable g / M.delta) ^ (2:ℕ) := by
    have h0 : 0 ≤ psi (PotentialField.triadicScale i g) / aux_psf_sigma M :=
      div_nonneg hpsi0 hsig.le
    nlinarith
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hsq)



/-- `u ≤ b e^{u-b}` for `1 ≤ b ≤ u`. -/
theorem aux_psf_le_mul_exp_sub {b u : ℝ} (hb : 1 ≤ b) (hu : b ≤ u) :
    u ≤ b * Real.exp (u - b) := by
  have h1 : u - b + 1 ≤ Real.exp (u - b) := Real.add_one_le_exp _
  have hb0 : (0:ℝ) < b := lt_of_lt_of_le zero_lt_one hb
  nlinarith [mul_le_mul_of_nonneg_left h1 hb0.le]

/-- The elementary sub-Gaussian first-moment inequality. -/
theorem aux_psf_sub_gaussian_pointwise {sigma b Y : ℝ} (hsig : 0 < sigma)
    (hb : 1 ≤ b) (hY : 0 ≤ Y) :
    Y ≤ sigma * Real.sqrt b +
      sigma * Real.sqrt b / Real.exp b * Real.exp ((Y / sigma) ^ 2) := by
  have hb0 : (0:ℝ) < b := lt_of_lt_of_le zero_lt_one hb
  have hsq : Real.sqrt b > 0 := Real.sqrt_pos.2 hb0
  set a : ℝ := sigma * Real.sqrt b with ha
  have ha0 : 0 < a := by positivity
  have hexp : 0 < Real.exp b := Real.exp_pos b
  have hterm : 0 ≤ a / Real.exp b * Real.exp ((Y / sigma) ^ 2) := by positivity
  rcases le_or_gt Y a with h | h
  · linarith
  · -- Y > a
    set u : ℝ := (Y / sigma) ^ 2 with hu
    have hasq : a ^ 2 = sigma ^ 2 * b := by
      rw [ha, mul_pow, Real.sq_sqrt hb0.le]
    have hub : b ≤ u := by
      rw [hu, div_pow]
      rw [le_div_iff₀ (by positivity)]
      nlinarith [h, ha0]
    have hkey : u ≤ b * Real.exp (u - b) := aux_psf_le_mul_exp_sub hb hub
    have hYu : Y ≤ sigma ^ 2 / a * u := by
      have hY2 : Y * a ≤ Y * Y := by nlinarith
      have : Y ≤ Y ^ 2 / a := by
        rw [le_div_iff₀ ha0]; nlinarith
      have hYsq : Y ^ 2 = sigma ^ 2 * u := by
        rw [hu, div_pow]; field_simp
      calc Y ≤ Y ^ 2 / a := this
        _ = sigma ^ 2 / a * u := by rw [hYsq]; ring
    have hexpsub : Real.exp (u - b) = Real.exp u / Real.exp b := by
      rw [Real.exp_sub]
    have hfinal : sigma ^ 2 / a * u ≤ a / Real.exp b * Real.exp u := by
      have h1 : sigma ^ 2 / a * u ≤ sigma ^ 2 / a * (b * Real.exp (u - b)) := by
        have : (0:ℝ) ≤ sigma ^ 2 / a := by positivity
        nlinarith
      have h2 : sigma ^ 2 / a * (b * Real.exp (u - b)) =
          (sigma ^ 2 * b / a) * (Real.exp u / Real.exp b) := by
        rw [hexpsub]; ring
      have h3 : sigma ^ 2 * b / a = a := by
        rw [ha]
        field_simp
        nlinarith [Real.sq_sqrt hb0.le, hsq]
      rw [h2, h3] at h1
      calc sigma ^ 2 / a * u ≤ a * (Real.exp u / Real.exp b) := h1
        _ = a / Real.exp b * Real.exp u := by ring
    linarith [hYu.trans hfinal]


theorem aux_psf_lintegral_sup' {Omega : Type} {iota : Type} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (S : Finset iota) (hne : S.Nonempty) (c : iota → Omega → ℝ)
    (hc : ∀ k omega, 0 ≤ c k omega)
    (hmeas : ∀ k, Measurable (c k))
    (sigma b : ℝ) (hsig : 0 < sigma) (hb : 1 ≤ b)
    (hmom : ∀ k, (∫⁻ omega, ENNReal.ofReal
        (Real.exp ((c k omega / sigma) ^ 2)) ∂mu) ≤ 2) :
    (∫⁻ omega, ENNReal.ofReal (S.sup' hne (fun k => c k omega)) ∂mu) ≤
      ENNReal.ofReal (sigma * Real.sqrt b) +
        ENNReal.ofReal (sigma * Real.sqrt b / Real.exp b) * (2 * (S.card : ℝ≥0∞)) := by
  have hb0 : (0:ℝ) < b := lt_of_lt_of_le zero_lt_one hb
  set a : ℝ := sigma * Real.sqrt b with ha
  have ha0 : 0 ≤ a := by positivity
  have hcoef : 0 ≤ a / Real.exp b := by positivity
  have hpt : ∀ omega, ENNReal.ofReal (S.sup' hne (fun k => c k omega)) ≤
      ENNReal.ofReal a + ENNReal.ofReal (a / Real.exp b) *
        ∑ k ∈ S, ENNReal.ofReal (Real.exp ((c k omega / sigma) ^ 2)) := by
    intro omega
    obtain ⟨k0, hk0S, hk0⟩ := S.exists_mem_eq_sup' hne (fun k => c k omega)
    have h1 : S.sup' hne (fun k => c k omega) ≤
        a + a / Real.exp b * Real.exp ((c k0 omega / sigma) ^ 2) := by
      rw [hk0]
      exact aux_psf_sub_gaussian_pointwise hsig hb (hc k0 omega)
    have h2 : Real.exp ((c k0 omega / sigma) ^ 2) ≤
        ∑ k ∈ S, Real.exp ((c k omega / sigma) ^ 2) :=
      Finset.single_le_sum (f := fun k => Real.exp ((c k omega / sigma) ^ 2))
        (fun k _ => (Real.exp_pos _).le) hk0S
    have h3 : S.sup' hne (fun k => c k omega) ≤
        a + a / Real.exp b * ∑ k ∈ S, Real.exp ((c k omega / sigma) ^ 2) := by
      refine h1.trans ?_
      have := mul_le_mul_of_nonneg_left h2 hcoef
      linarith
    calc ENNReal.ofReal (S.sup' hne (fun k => c k omega)) ≤
        ENNReal.ofReal (a + a / Real.exp b *
          ∑ k ∈ S, Real.exp ((c k omega / sigma) ^ 2)) :=
          ENNReal.ofReal_le_ofReal h3
      _ ≤ ENNReal.ofReal a + ENNReal.ofReal (a / Real.exp b *
          ∑ k ∈ S, Real.exp ((c k omega / sigma) ^ 2)) := ENNReal.ofReal_add_le
      _ = ENNReal.ofReal a + ENNReal.ofReal (a / Real.exp b) *
          ENNReal.ofReal (∑ k ∈ S, Real.exp ((c k omega / sigma) ^ 2)) := by
          rw [ENNReal.ofReal_mul hcoef]
      _ = ENNReal.ofReal a + ENNReal.ofReal (a / Real.exp b) *
          ∑ k ∈ S, ENNReal.ofReal (Real.exp ((c k omega / sigma) ^ 2)) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro k _
          exact (Real.exp_pos _).le
  have hsummeas : Measurable fun omega =>
      ∑ k ∈ S, ENNReal.ofReal (Real.exp ((c k omega / sigma) ^ 2)) := by
    refine Finset.measurable_sum S ?_
    intro k _
    exact (((hmeas k).div_const _).pow_const _).exp.ennreal_ofReal
  calc (∫⁻ omega, ENNReal.ofReal (S.sup' hne (fun k => c k omega)) ∂mu) ≤
      ∫⁻ omega, (ENNReal.ofReal a + ENNReal.ofReal (a / Real.exp b) *
        ∑ k ∈ S, ENNReal.ofReal (Real.exp ((c k omega / sigma) ^ 2))) ∂mu :=
        lintegral_mono hpt
    _ = ENNReal.ofReal a + ENNReal.ofReal (a / Real.exp b) *
        ∫⁻ omega, ∑ k ∈ S, ENNReal.ofReal
          (Real.exp ((c k omega / sigma) ^ 2)) ∂mu := by
        rw [lintegral_add_left measurable_const, lintegral_const_mul _ hsummeas,
          lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal a + ENNReal.ofReal (a / Real.exp b) * (2 * (S.card : ℝ≥0∞)) := by
        have hinner : (∫⁻ omega, ∑ k ∈ S, ENNReal.ofReal
            (Real.exp ((c k omega / sigma) ^ 2)) ∂mu) ≤ 2 * (S.card : ℝ≥0∞) := by
          rw [lintegral_finset_sum]
          · calc ∑ k ∈ S, ∫⁻ omega, ENNReal.ofReal
                  (Real.exp ((c k omega / sigma) ^ 2)) ∂mu ≤ ∑ _k ∈ S, (2 : ℝ≥0∞) :=
                Finset.sum_le_sum (fun k _ => hmom k)
              _ = (S.card : ℝ≥0∞) * 2 := by rw [Finset.sum_const, nsmul_eq_mul]
              _ = 2 * (S.card : ℝ≥0∞) := by ring
          · intro k _
            exact (((hmeas k).div_const _).pow_const _).exp.ennreal_ofReal
        gcongr


theorem aux_psf_lintegral_sup'_sqrt {Omega : Type} {iota : Type} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (S : Finset iota) (hne : S.Nonempty) (c : iota → Omega → ℝ)
    (hc : ∀ k omega, 0 ≤ c k omega)
    (hmeas : ∀ k, Measurable (c k))
    (sigma : ℝ) (hsig : 0 < sigma)
    (hmom : ∀ k, (∫⁻ omega, ENNReal.ofReal
        (Real.exp ((c k omega / sigma) ^ 2)) ∂mu) ≤ 2) :
    (∫⁻ omega, ENNReal.ofReal (S.sup' hne (fun k => c k omega)) ∂mu) ≤
      ENNReal.ofReal (2 * sigma *
        Real.sqrt (1 + Real.log (2 * (S.card : ℝ)))) := by
  have hcard : 1 ≤ (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 hne
  have h2card : (1:ℝ) ≤ 2 * (S.card : ℝ) := by linarith
  set b : ℝ := 1 + Real.log (2 * (S.card : ℝ)) with hbdef
  have hlog0 : 0 ≤ Real.log (2 * (S.card : ℝ)) := Real.log_nonneg h2card
  have hb : 1 ≤ b := by rw [hbdef]; linarith
  have hb0 : (0:ℝ) < b := lt_of_lt_of_le zero_lt_one hb
  set a : ℝ := sigma * Real.sqrt b with ha
  have ha0 : 0 ≤ a := by positivity
  have hexpb : Real.exp b = Real.exp 1 * (2 * (S.card : ℝ)) := by
    rw [hbdef, Real.exp_add, Real.exp_log (by linarith)]
  have hsecond : ENNReal.ofReal (a / Real.exp b) * (2 * (S.card : ℝ≥0∞)) ≤
      ENNReal.ofReal a := by
    have hcast : (2 * (S.card : ℝ≥0∞)) = ENNReal.ofReal (2 * (S.card : ℝ)) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast]
      norm_num
    rw [hcast, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hexpb]
    have he : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
    have h2c : (0:ℝ) < 2 * (S.card : ℝ) := by linarith
    have : a / (Real.exp 1 * (2 * (S.card : ℝ))) * (2 * (S.card : ℝ)) =
        a / Real.exp 1 := by field_simp
    rw [this]
    rw [div_le_iff₀ he]
    nlinarith [Real.add_one_le_exp (1:ℝ)]
  calc (∫⁻ omega, ENNReal.ofReal (S.sup' hne (fun k => c k omega)) ∂mu) ≤
      ENNReal.ofReal a + ENNReal.ofReal (a / Real.exp b) * (2 * (S.card : ℝ≥0∞)) :=
        aux_psf_lintegral_sup' mu S hne c hc hmeas sigma b hsig hb hmom
    _ ≤ ENNReal.ofReal a + ENNReal.ofReal a := by gcongr
    _ = ENNReal.ofReal (2 * sigma * Real.sqrt b) := by
        rw [← ENNReal.ofReal_add ha0 ha0, ha]; ring_nf



/-- The finite catalogue of unit cells covering `translatedCube d n z`. -/
def aux_psf_cells (dd n : ℕ) : Finset (Fin dd → ℕ) :=
  Fintype.piFinset (fun _ : Fin dd => Finset.range (2 * 3 ^ n + 1))

theorem aux_psf_cells_nonempty (dd n : ℕ) : (aux_psf_cells dd n).Nonempty := by
  refine ⟨fun _ => 0, ?_⟩
  rw [aux_psf_cells, Fintype.mem_piFinset]
  intro i
  exact Finset.mem_range.2 (by omega)

theorem aux_psf_cells_card (dd n : ℕ) :
    (aux_psf_cells dd n).card = (2 * 3 ^ n + 1) ^ dd := by
  rw [aux_psf_cells, Fintype.card_piFinset]
  simp

theorem aux_psf_cover' (n : ℕ) (z x : Vec d)
    (hx : x ∈ translatedCube d (n : ℤ) z) :
    ∃ k ∈ aux_psf_cells d n, x - aux_psf_center n z k ∈ cube d 0 := by
  obtain ⟨k, hk⟩ := aux_psf_cover n z x hx
  refine ⟨fun i => ((k i : ℕ)), ?_, hk⟩
  rw [aux_psf_cells, Fintype.mem_piFinset]
  intro i
  exact Finset.mem_range.2 (k i).isLt

/-- The measurable majorant of one layer's contribution on a translated cube. -/
def aux_psf_maxObs (i n : ℕ) (z : Vec d) (omega : PotentialSample d) : ℝ :=
  (aux_psf_cells d n).sup' (aux_psf_cells_nonempty d n)
    (fun k => aux_psf_cellObs i (aux_psf_center n z k) omega)

theorem aux_psf_maxObs_nonneg (i n : ℕ) (z : Vec d) (omega : PotentialSample d) :
    0 ≤ aux_psf_maxObs i n z omega := by
  obtain ⟨k, hk⟩ := aux_psf_cells_nonempty d n
  refine le_trans (aux_psf_cellObs_nonneg i (aux_psf_center n z k) omega) ?_
  exact Finset.le_sup' (f := fun k => aux_psf_cellObs i (aux_psf_center n z k) omega) hk

theorem aux_psf_maxObs_measurable (i n : ℕ) (z : Vec d) :
    Measurable (fun omega : PotentialSample d => aux_psf_maxObs i n z omega) := by
  have h : Measurable ((aux_psf_cells d n).sup' (aux_psf_cells_nonempty d n)
      (fun k (omega : PotentialSample d) =>
        aux_psf_cellObs i (aux_psf_center n z k) omega)) :=
    Finset.measurable_sup' _
      (fun k _ => aux_psf_cellObs_measurable i (aux_psf_center n z k))
  convert h using 1
  funext omega
  unfold aux_psf_maxObs
  rw [Finset.sup'_apply]

theorem aux_psf_le_maxObs (i n : ℕ) (z x : Vec d) (omega : PotentialSample d)
    (hx : x ∈ translatedCube d (n : ℤ) z) :
    |omega i x| +
        (3 : ℝ) ^ i * Homogenization.euclideanNorm (shellGradient (omega i) x) ≤
      aux_psf_maxObs i n z omega := by
  obtain ⟨k, hkmem, hk⟩ := aux_psf_cover' n z x hx
  refine (aux_psf_le_cellObs i (aux_psf_center n z k) x omega hk).trans ?_
  exact Finset.le_sup'
    (f := fun k => aux_psf_cellObs i (aux_psf_center n z k) omega) hkmem

theorem aux_psf_lintegral_maxObs (M : GMCModel d) (i n : ℕ) (z : Vec d) :
    (∫⁻ omega, ENNReal.ofReal (aux_psf_maxObs i n z omega) ∂M.P.toMeasure) ≤
      ENNReal.ofReal (2 * aux_psf_sigma M *
        Real.sqrt (1 + Real.log (2 * (((2 * 3 ^ n + 1) ^ d : ℕ) : ℝ)))) := by
  have h := aux_psf_lintegral_sup'_sqrt (Omega := PotentialSample d)
    (iota := Fin d → ℕ) M.P.toMeasure (aux_psf_cells d n)
    (aux_psf_cells_nonempty d n)
    (fun k omega => aux_psf_cellObs i (aux_psf_center n z k) omega)
    (fun k omega => aux_psf_cellObs_nonneg i (aux_psf_center n z k) omega)
    (fun k => aux_psf_cellObs_measurable i (aux_psf_center n z k))
    (aux_psf_sigma M) (aux_psf_sigma_pos M)
    (fun k => aux_psf_cell_exp M i (aux_psf_center n z k))
  rw [aux_psf_cells_card] at h
  exact h


theorem aux_psf_normOn_le (i n : ℕ) (z : Vec d) (omega : PotentialSample d) :
    sSup {v : ℝ≥0∞ | ∃ x ∈ translatedCube d (n : ℤ) z,
        v = ENNReal.ofReal
          |(|omega i x| + (3 : ℝ) ^ (i : ℝ) *
            Homogenization.euclideanNorm (shellGradient (omega i) x))|} ≤
      ENNReal.ofReal (aux_psf_maxObs i n z omega) := by
  refine sSup_le ?_
  rintro v ⟨x, hx, rfl⟩
  have hrp : (0:ℝ) ≤ (3:ℝ) ^ (i:ℝ) := Real.rpow_nonneg (by norm_num) _
  have hen : 0 ≤ Homogenization.euclideanNorm (shellGradient (omega i) x) :=
    Real.sqrt_nonneg _
  have hnn : 0 ≤ |omega i x| + (3 : ℝ) ^ (i : ℝ) *
      Homogenization.euclideanNorm (shellGradient (omega i) x) := by
    have := abs_nonneg (omega i x)
    nlinarith
  rw [abs_of_nonneg hnn]
  refine ENNReal.ofReal_le_ofReal ?_
  have hrpow : (3:ℝ) ^ (i:ℝ) = (3:ℝ) ^ i := by
    rw [← Real.rpow_natCast (3:ℝ) i]
  rw [hrpow]
  exact aux_psf_le_maxObs i n z x omega hx


/-- The measurable majorant of the `j`-th field-score term. -/
def aux_psf_Fmaj (s : ℝ) (m : ℕ) (z : Vec d) (j : ℕ)
    (omega : PotentialSample d) : ℝ≥0∞ :=
  ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
    ∑ i ∈ Finset.Icc (m - j) (m + j),
      ENNReal.ofReal (aux_psf_maxObs i (m + 1 + j) z omega)

theorem aux_psf_Fmaj_measurable (s : ℝ) (m : ℕ) (z : Vec d) (j : ℕ) :
    Measurable (fun omega : PotentialSample d => aux_psf_Fmaj s m z j omega) := by
  unfold aux_psf_Fmaj
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ ?_
  intro i _
  exact (aux_psf_maxObs_measurable i (m + 1 + j) z).ennreal_ofReal

/-- The expectation bound for one field-score term. -/
def aux_psf_Fbound (M : GMCModel d) (s : ℝ) (m j : ℕ) : ℝ :=
  (3 : ℝ) ^ (-(s * (j : ℝ) / 8)) * ((2 * j + 1 : ℕ) : ℝ) *
    (2 * aux_psf_sigma M *
      Real.sqrt (1 + Real.log (2 * (((2 * 3 ^ (m + 1 + j) + 1) ^ d : ℕ) : ℝ))))

theorem aux_psf_lintegral_Fmaj (M : GMCModel d) (s : ℝ) (m : ℕ) (z : Vec d)
    (j : ℕ) :
    (∫⁻ omega, aux_psf_Fmaj s m z j omega ∂M.P.toMeasure) ≤
      ENNReal.ofReal (aux_psf_Fbound M s m j) := by
  set K : ℝ := 2 * aux_psf_sigma M *
    Real.sqrt (1 + Real.log (2 * (((2 * 3 ^ (m + 1 + j) + 1) ^ d : ℕ) : ℝ))) with hK
  have hK0 : 0 ≤ K := by
    have := (aux_psf_sigma_pos M).le
    rw [hK]; positivity
  have hc0 : (0:ℝ) ≤ (3 : ℝ) ^ (-(s * (j : ℝ) / 8)) :=
    Real.rpow_nonneg (by norm_num) _
  have hmeas : Measurable fun omega : PotentialSample d =>
      ∑ i ∈ Finset.Icc (m - j) (m + j),
        ENNReal.ofReal (aux_psf_maxObs i (m + 1 + j) z omega) := by
    refine Finset.measurable_sum _ ?_
    intro i _
    exact (aux_psf_maxObs_measurable i (m + 1 + j) z).ennreal_ofReal
  have hcard : ((Finset.Icc (m - j) (m + j)).card : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) := by
    have : (Finset.Icc (m - j) (m + j)).card = m + j + 1 - (m - j) := by
      rw [Nat.card_Icc]
    rw [this]
    have : m + j + 1 - (m - j) ≤ 2 * j + 1 := by omega
    exact_mod_cast this
  have hsum : (∫⁻ omega, ∑ i ∈ Finset.Icc (m - j) (m + j),
      ENNReal.ofReal (aux_psf_maxObs i (m + 1 + j) z omega) ∂M.P.toMeasure) ≤
      ENNReal.ofReal (((2 * j + 1 : ℕ) : ℝ) * K) := by
    rw [lintegral_finset_sum _ (fun i _ =>
      (aux_psf_maxObs_measurable i (m + 1 + j) z).ennreal_ofReal)]
    calc ∑ i ∈ Finset.Icc (m - j) (m + j),
          ∫⁻ omega, ENNReal.ofReal (aux_psf_maxObs i (m + 1 + j) z omega)
            ∂M.P.toMeasure
        ≤ ∑ _i ∈ Finset.Icc (m - j) (m + j), ENNReal.ofReal K :=
          Finset.sum_le_sum (fun i _ => aux_psf_lintegral_maxObs M i (m + 1 + j) z)
      _ = ((Finset.Icc (m - j) (m + j)).card : ℝ≥0∞) * ENNReal.ofReal K := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal (((2 * j + 1 : ℕ) : ℝ)) * ENNReal.ofReal K := by
          gcongr
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal hcard
      _ = ENNReal.ofReal (((2 * j + 1 : ℕ) : ℝ) * K) :=
          (ENNReal.ofReal_mul (by positivity)).symm
  unfold aux_psf_Fmaj aux_psf_Fbound
  rw [lintegral_const_mul _ hmeas]
  calc ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
        ∫⁻ omega, ∑ i ∈ Finset.Icc (m - j) (m + j),
          ENNReal.ofReal (aux_psf_maxObs i (m + 1 + j) z omega) ∂M.P.toMeasure
      ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8))) *
          ENNReal.ofReal (((2 * j + 1 : ℕ) : ℝ) * K) := by gcongr
    _ = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8)) *
          (((2 * j + 1 : ℕ) : ℝ) * K)) := (ENNReal.ofReal_mul hc0).symm
    _ = ENNReal.ofReal ((3 : ℝ) ^ (-(s * (j : ℝ) / 8)) * ((2 * j + 1 : ℕ) : ℝ) * K) := by
        ring_nf


theorem aux_psf_nat_cover_bound (dd m j : ℕ) :
    2 * (2 * 3 ^ (m + 1 + j) + 1) ^ dd ≤ 3 ^ (dd * (m + 2 + j) + 1) := by
  have h1 : 2 * 3 ^ (m + 1 + j) + 1 ≤ 3 ^ (m + 2 + j) := by
    have h3 : (1:ℕ) ≤ 3 ^ (m + 1 + j) := Nat.one_le_pow _ _ (by norm_num)
    have : 3 ^ (m + 2 + j) = 3 * 3 ^ (m + 1 + j) := by
      rw [show m + 2 + j = (m + 1 + j) + 1 by omega, pow_succ]
      ring
    omega
  calc 2 * (2 * 3 ^ (m + 1 + j) + 1) ^ dd ≤ 2 * (3 ^ (m + 2 + j)) ^ dd :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 dd)
    _ = 2 * 3 ^ (dd * (m + 2 + j)) := by
        rw [← pow_mul, mul_comm (m + 2 + j) dd]
    _ ≤ 3 * 3 ^ (dd * (m + 2 + j)) := by
        exact Nat.mul_le_mul_right _ (by norm_num)
    _ = 3 ^ (dd * (m + 2 + j) + 1) := by rw [pow_succ]; ring

theorem aux_psf_sqrt_log_bound (dd m j : ℕ) :
    Real.sqrt (1 + Real.log (2 * (((2 * 3 ^ (m + 1 + j) + 1) ^ dd : ℕ) : ℝ))) ≤
      (2 + ((dd : ℝ) * ((m : ℝ) + 2) + 1) * Real.log 3) +
        ((dd : ℝ) * Real.log 3) * (j : ℝ) := by
  have hlog3 : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hnat := aux_psf_nat_cover_bound dd m j
  have hcast : (2 : ℝ) * (((2 * 3 ^ (m + 1 + j) + 1) ^ dd : ℕ) : ℝ) =
      ((2 * (2 * 3 ^ (m + 1 + j) + 1) ^ dd : ℕ) : ℝ) := by push_cast; ring
  have hle : (2 : ℝ) * (((2 * 3 ^ (m + 1 + j) + 1) ^ dd : ℕ) : ℝ) ≤
      ((3 : ℝ)) ^ (dd * (m + 2 + j) + 1) := by
    rw [hcast]
    have := (Nat.cast_le (α := ℝ)).2 hnat
    simpa using this
  have hpos : (0:ℝ) < 2 * (((2 * 3 ^ (m + 1 + j) + 1) ^ dd : ℕ) : ℝ) := by
    have : (0:ℕ) < (2 * 3 ^ (m + 1 + j) + 1) ^ dd := Nat.pow_pos (by omega)
    have := (Nat.cast_pos (α := ℝ)).2 this
    linarith
  have hlogle : Real.log (2 * (((2 * 3 ^ (m + 1 + j) + 1) ^ dd : ℕ) : ℝ)) ≤
      ((dd * (m + 2 + j) + 1 : ℕ) : ℝ) * Real.log 3 := by
    calc Real.log (2 * (((2 * 3 ^ (m + 1 + j) + 1) ^ dd : ℕ) : ℝ)) ≤
        Real.log (((3:ℝ)) ^ (dd * (m + 2 + j) + 1)) := Real.log_le_log hpos hle
      _ = ((dd * (m + 2 + j) + 1 : ℕ) : ℝ) * Real.log 3 := by
          rw [Real.log_pow]
  have hlin : ((dd * (m + 2 + j) + 1 : ℕ) : ℝ) * Real.log 3 ≤
      ((dd : ℝ) * ((m : ℝ) + 2) + 1) * Real.log 3 +
        ((dd : ℝ) * Real.log 3) * (j : ℝ) := by
    push_cast
    nlinarith [hlog3.le]
  have hsq : ∀ t : ℝ, 0 ≤ t → Real.sqrt t ≤ 1 + t := by
    intro t ht
    have h1 : Real.sqrt t ≤ Real.sqrt ((1 + t) ^ 2) := by
      apply Real.sqrt_le_sqrt
      nlinarith
    rw [Real.sqrt_sq (by linarith)] at h1
    exact h1
  have hnn : 0 ≤ Real.log (2 * (((2 * 3 ^ (m + 1 + j) + 1) ^ dd : ℕ) : ℝ)) := by
    refine Real.log_nonneg ?_
    have : (1:ℕ) ≤ (2 * 3 ^ (m + 1 + j) + 1) ^ dd := Nat.one_le_pow _ _ (by omega)
    have := (Nat.one_le_cast (α := ℝ)).2 this
    linarith
  have hL := hlogle.trans hlin
  have hs2 := hsq (1 + Real.log (2 * (((2 * 3 ^ (m + 1 + j) + 1) ^ dd : ℕ) : ℝ)))
    (by linarith)
  linarith


theorem aux_psf_summable_Fbound (M : GMCModel d) (s : ℝ) (hs0 : 0 < s) (m : ℕ) :
    Summable (fun j : ℕ => aux_psf_Fbound M s m j) := by
  have hlog3 : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hsig := aux_psf_sigma_pos M
  set r : ℝ := (3:ℝ) ^ (-(s / 8)) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := by
    rw [hr]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hrn : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1
  have hrj : ∀ j : ℕ, (3:ℝ) ^ (-(s * (j:ℝ) / 8)) = r ^ j := by
    intro j
    rw [hr, ← Real.rpow_natCast ((3:ℝ) ^ (-(s / 8))) j,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
    congr 1
    ring
  set A : ℝ := 2 + ((d : ℝ) * ((m : ℝ) + 2) + 1) * Real.log 3 with hA
  set B : ℝ := (d : ℝ) * Real.log 3 with hB
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  set C : ℝ := 4 * aux_psf_sigma M * (A + B) with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hmaj : Summable (fun j : ℕ => C * (((j:ℝ) + 1) ^ 2 * r ^ j)) := by
    have h2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hrn
    have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hrn
    have h0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 hrn
    have hbase : Summable (fun j : ℕ => ((j:ℝ) + 1) ^ 2 * r ^ j) := by
      refine ((h2.add (h1.mul_left 2)).add h0).congr ?_
      intro j
      ring
    exact hbase.mul_left C
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hmaj
  · unfold aux_psf_Fbound
    have h1 : (0:ℝ) ≤ (3 : ℝ) ^ (-(s * (j : ℝ) / 8)) :=
      Real.rpow_nonneg (by norm_num) _
    have h2 : (0:ℝ) ≤ Real.sqrt (1 + Real.log
        (2 * (((2 * 3 ^ (m + 1 + j) + 1) ^ d : ℕ) : ℝ))) := Real.sqrt_nonneg _
    have h3 : (0:ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have h4 := hsig.le
    positivity
  · unfold aux_psf_Fbound
    rw [hrj j]
    have hsqrtb := aux_psf_sqrt_log_bound d m j
    have hcard : ((2 * j + 1 : ℕ) : ℝ) ≤ 2 * ((j:ℝ) + 1) := by push_cast; linarith
    have hlin : A + B * (j:ℝ) ≤ (A + B) * ((j:ℝ) + 1) := by
      have hj : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg _
      nlinarith
    have hsq2 : Real.sqrt (1 + Real.log
        (2 * (((2 * 3 ^ (m + 1 + j) + 1) ^ d : ℕ) : ℝ))) ≤ (A + B) * ((j:ℝ) + 1) := by
      refine le_trans ?_ hlin
      rw [hA, hB]
      exact hsqrtb
    have hcard0 : (0:ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hsq0 : (0:ℝ) ≤ Real.sqrt (1 + Real.log
        (2 * (((2 * 3 ^ (m + 1 + j) + 1) ^ d : ℕ) : ℝ))) := Real.sqrt_nonneg _
    have hrpow0 : (0:ℝ) ≤ r ^ j := by positivity
    have hjj : (0:ℝ) ≤ (j:ℝ) + 1 := by positivity
    have key : ((2 * j + 1 : ℕ) : ℝ) *
        (2 * aux_psf_sigma M * Real.sqrt (1 + Real.log
          (2 * (((2 * 3 ^ (m + 1 + j) + 1) ^ d : ℕ) : ℝ)))) ≤
        C * (((j:ℝ) + 1) ^ 2) := by
      have hstep1 : (2 * aux_psf_sigma M * Real.sqrt (1 + Real.log
          (2 * (((2 * 3 ^ (m + 1 + j) + 1) ^ d : ℕ) : ℝ)))) ≤
          2 * aux_psf_sigma M * ((A + B) * ((j:ℝ) + 1)) := by
        have : (0:ℝ) ≤ 2 * aux_psf_sigma M := by positivity
        nlinarith
      have hAB0 : (0:ℝ) ≤ (A + B) := by linarith
      rw [hC]
      nlinarith [mul_le_mul hcard hstep1 (by positivity) (by positivity)]
    calc r ^ j * ((2 * j + 1 : ℕ) : ℝ) *
        (2 * aux_psf_sigma M * Real.sqrt (1 + Real.log
          (2 * (((2 * 3 ^ (m + 1 + j) + 1) ^ d : ℕ) : ℝ)))) =
        r ^ j * (((2 * j + 1 : ℕ) : ℝ) *
          (2 * aux_psf_sigma M * Real.sqrt (1 + Real.log
            (2 * (((2 * 3 ^ (m + 1 + j) + 1) ^ d : ℕ) : ℝ))))) := by ring
      _ ≤ r ^ j * (C * (((j:ℝ) + 1) ^ 2)) := mul_le_mul_of_nonneg_left key hrpow0
      _ = C * (((j:ℝ) + 1) ^ 2 * r ^ j) := by ring


theorem aux_psf_Fbound_nonneg (M : GMCModel d) (s : ℝ) (m j : ℕ) :
    0 ≤ aux_psf_Fbound M s m j := by
  have h1 : (0:ℝ) ≤ (3 : ℝ) ^ (-(s * (j : ℝ) / 8)) :=
    Real.rpow_nonneg (by norm_num) _
  have h2 : (0:ℝ) ≤ Real.sqrt (1 + Real.log
      (2 * (((2 * 3 ^ (m + 1 + j) + 1) ^ d : ℕ) : ℝ))) := Real.sqrt_nonneg _
  have h3 : (0:ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have h4 := (aux_psf_sigma_pos M).le
  unfold aux_psf_Fbound
  positivity

theorem aux_psf_Fmaj_tsum_ae (M : GMCModel d) (s : ℝ) (hs0 : 0 < s) (m : ℕ)
    (z : Vec d) :
    ∀ᵐ omega ∂M.P.toMeasure, (∑' j : ℕ, aux_psf_Fmaj s m z j omega) ≠ ⊤ := by
  have hmeas : ∀ j : ℕ, AEMeasurable (fun omega : PotentialSample d =>
      aux_psf_Fmaj s m z j omega) M.P.toMeasure :=
    fun j => (aux_psf_Fmaj_measurable s m z j).aemeasurable
  have hint : (∫⁻ omega, (∑' j : ℕ, aux_psf_Fmaj s m z j omega)
      ∂M.P.toMeasure) ≠ ⊤ := by
    rw [lintegral_tsum hmeas]
    have hb : ∀ j, (∫⁻ omega, aux_psf_Fmaj s m z j omega ∂M.P.toMeasure) ≤
        ENNReal.ofReal (aux_psf_Fbound M s m j) := aux_psf_lintegral_Fmaj M s m z
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hb)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => aux_psf_Fbound_nonneg M s m j)
      (aux_psf_summable_Fbound M s hs0 m)]
    exact ENNReal.ofReal_ne_top
  have hlt := ae_lt_top' (AEMeasurable.ennreal_tsum hmeas) hint
  filter_upwards [hlt] with omega h
  exact h.ne


theorem aux_psf_Fsc_ne_top (s : ℝ) (m : ℕ) (z : Vec d)
    (omega : PotentialSample d)
    (hfin : (∑' j : ℕ, aux_psf_Fmaj s m z j omega) ≠ ⊤) :
    sSup {v : ℝ≥0∞ | ∃ j : ℕ, v = ENNReal.ofReal ((3:ℝ) ^ (-(s * (j:ℝ) / 8))) *
        ∑ i ∈ Finset.Icc (m - j) (m + j),
          sSup {w : ℝ≥0∞ | ∃ x ∈ translatedCube d ((m:ℤ) + 1 + (j:ℤ)) z,
            w = ENNReal.ofReal |(|omega i x| + (3:ℝ) ^ (i:ℝ) *
              Homogenization.euclideanNorm (shellGradient (omega i) x))|}} ≠ ⊤ := by
  refine ne_top_of_le_ne_top hfin (sSup_le ?_)
  rintro v ⟨j, rfl⟩
  refine le_trans ?_ (ENNReal.le_tsum j)
  unfold aux_psf_Fmaj
  have hcast : ((m:ℤ) + 1 + (j:ℤ)) = (((m + 1 + j : ℕ)) : ℤ) := by push_cast; ring
  rw [hcast]
  gcongr with i _
  exact aux_psf_normOn_le i (m + 1 + j) z omega


/-- The lattice point of the scale-`n` triadic grid with integer coordinates `k`. -/
def aux_psf_Rpoint (n : ℕ) (z : Vec d) (k : Fin d → ℤ) : Vec d :=
  fun i => z i + (3 : ℝ) ^ n * ((k i : ℤ) : ℝ)

/-- The finite catalogue of scale-`n` grid points inside `z + Q_j`. -/
def aux_psf_Rindex (dd j : ℕ) : Finset (Fin dd → ℤ) :=
  Fintype.piFinset (fun _ : Fin dd => Finset.Icc (-(3 ^ j : ℤ)) (3 ^ j))

theorem aux_psf_Rpoint_mem (n j : ℕ) (z x : Vec d)
    (hgrid : OnTriadicGrid n (x - z)) (hx : x - z ∈ cube d (j : ℤ)) :
    ∃ k ∈ aux_psf_Rindex d j, x = aux_psf_Rpoint n z k := by
  choose k hk using hgrid
  refine ⟨k, ?_, ?_⟩
  · rw [aux_psf_Rindex, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at hx
    have hxi := hx i
    have hki := hk i
    simp only [Pi.sub_apply] at hki hxi
    have h3n : (1:ℝ) ≤ (3:ℝ) ^ n := one_le_pow₀ (by norm_num)
    have h3j : (0:ℝ) < (3:ℝ) ^ (j : ℤ) := zpow_pos (by norm_num) _
    have habs : |((k i : ℤ) : ℝ)| < (3:ℝ) ^ (j : ℤ) := by
      have h1 : |(3:ℝ) ^ n * ((k i : ℤ) : ℝ)| < (3:ℝ) ^ (j : ℤ) / 2 := by
        rw [← hki, abs_lt]
        constructor <;> linarith [hxi.1, hxi.2]
      have h2 : |((k i : ℤ) : ℝ)| ≤ |(3:ℝ) ^ n * ((k i : ℤ) : ℝ)| := by
        rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < (3:ℝ) ^ n)]
        nlinarith [abs_nonneg ((k i : ℤ) : ℝ)]
      linarith
    have hcast : |((k i : ℤ) : ℝ)| = (((|k i| : ℤ)) : ℝ) := Int.cast_abs.symm
    have hjcast : (3:ℝ) ^ (j : ℤ) = (((3 ^ j : ℤ)) : ℝ) := by
      push_cast; rw [zpow_natCast]
    rw [hcast, hjcast] at habs
    have hlt : |k i| < (3 ^ j : ℤ) := by exact_mod_cast habs
    exact abs_le.mp hlt.le
  · funext i
    have hki := hk i
    simp only [Pi.sub_apply] at hki
    simp only [aux_psf_Rpoint]
    linarith


/-- The matched-response supremum over the unit sphere. -/
def aux_psf_Jval (M : GMCModel d) (n : ℕ) (omega : PotentialSample d)
    (x : Vec d) : ℝ≥0∞ :=
  sSup {v : ℝ≥0∞ | ∃ e : Vec d, Homogenization.vecNormSq e = 1 ∧
    v = ENNReal.ofReal (section6Response M n n omega x e)}

theorem aux_psf_Jval_ne_top (M : GMCModel d) (n : ℕ) (omega : PotentialSample d)
    (x : Vec d) : aux_psf_Jval M n omega x ≠ ⊤ := by
  obtain ⟨B, hB⟩ := bddAbove_section6Response_unitSphere M n n omega x
  unfold aux_psf_Jval
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := B)) (sSup_le ?_)
  rintro v ⟨e, he, rfl⟩
  exact ENNReal.ofReal_le_ofReal (hB ⟨e, he, rfl⟩)

/-- The finite majorant of the annular response score. -/
def aux_psf_Rmaj (M : GMCModel d) (s : ℝ) (m : ℕ) (z : Vec d)
    (omega : PotentialSample d) : ℝ≥0∞ :=
  (Finset.range (m + 1)).sup (fun j =>
    (Finset.range (m + 1)).sup (fun n =>
      (aux_psf_Rindex d j).sup (fun k =>
        ENNReal.ofReal ((3:ℝ) ^ (-(s * ((m:ℝ) - (n:ℝ)) / 8))) *
          aux_psf_Jval M n omega (aux_psf_Rpoint n z k))))

theorem aux_psf_Rmaj_ne_top (M : GMCModel d) (s : ℝ) (m : ℕ) (z : Vec d)
    (omega : PotentialSample d) : aux_psf_Rmaj M s m z omega ≠ ⊤ := by
  have hbot : (⊥ : ℝ≥0∞) < ⊤ := by simp
  rw [← lt_top_iff_ne_top, aux_psf_Rmaj, Finset.sup_lt_iff hbot]
  intro j _
  rw [Finset.sup_lt_iff hbot]
  intro n _
  rw [Finset.sup_lt_iff hbot]
  intro k _
  rw [lt_top_iff_ne_top]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (aux_psf_Jval_ne_top M n omega (aux_psf_Rpoint n z k))

theorem aux_psf_Rsc_ne_top (M : GMCModel d) (s : ℝ) (m : ℕ) (z : Vec d)
    (omega : PotentialSample d) :
    sSup {v : ℝ≥0∞ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧ ∃ x : Vec d,
      OnTriadicGrid n (x - z) ∧ x - z ∈ cube d (j:ℤ) \ cube d ((j:ℤ) - 1) ∧
      v = ENNReal.ofReal ((3:ℝ) ^ (-(s * ((m:ℝ) - (n:ℝ)) / 8))) *
        aux_psf_Jval M n omega x} ≠ ⊤ := by
  refine ne_top_of_le_ne_top (aux_psf_Rmaj_ne_top M s m z omega) (sSup_le ?_)
  rintro v ⟨j, n, hjm, hnj, x, hgrid, hannulus, rfl⟩
  obtain ⟨k, hk, rfl⟩ := aux_psf_Rpoint_mem n j z x hgrid hannulus.1
  have hjmem : j ∈ Finset.range (m + 1) := Finset.mem_range.2 (by omega)
  have hnmem : n ∈ Finset.range (m + 1) := Finset.mem_range.2 (by omega)
  refine le_trans ?_ (Finset.le_sup (f := fun j : ℕ =>
    (Finset.range (m + 1)).sup (fun n : ℕ =>
      (aux_psf_Rindex d j).sup (fun k : Fin d → ℤ =>
        ENNReal.ofReal ((3:ℝ) ^ (-(s * ((m:ℝ) - (n:ℝ)) / 8))) *
          aux_psf_Jval M n omega (aux_psf_Rpoint n z k)))) hjmem)
  refine le_trans ?_ (Finset.le_sup (f := fun n : ℕ =>
    (aux_psf_Rindex d j).sup (fun k : Fin d → ℤ =>
      ENNReal.ofReal ((3:ℝ) ^ (-(s * ((m:ℝ) - (n:ℝ)) / 8))) *
        aux_psf_Jval M n omega (aux_psf_Rpoint n z k))) hnmem)
  exact Finset.le_sup (f := fun k : Fin d → ℤ =>
    ENNReal.ofReal ((3:ℝ) ^ (-(s * ((m:ℝ) - (n:ℝ)) / 8))) *
      aux_psf_Jval M n omega (aux_psf_Rpoint n z k)) hk


theorem aux_psf_normOn_le_of_le (n : ℕ) (z : Vec d) (f : Vec d → ℝ) (C : ℝ)
    (hf : ∀ x ∈ translatedCube d (n:ℤ) z, |f x| ≤ C) :
    sSup {v : ℝ≥0∞ | ∃ x ∈ translatedCube d (n:ℤ) z, v = ENNReal.ofReal |f x|} ≤
      ENNReal.ofReal C := by
  refine sSup_le ?_
  rintro v ⟨x, hx, rfl⟩
  exact ENNReal.ofReal_le_ofReal (hf x hx)

theorem aux_psf_abs_le_maxObs (i n : ℕ) (z x : Vec d) (omega : PotentialSample d)
    (hx : x ∈ translatedCube d (n : ℤ) z) :
    |omega i x| ≤ aux_psf_maxObs i n z omega := by
  have h := aux_psf_le_maxObs i n z x omega hx
  have hrp : (0:ℝ) ≤ (3:ℝ) ^ i := by positivity
  have hen : 0 ≤ Homogenization.euclideanNorm (shellGradient (omega i) x) :=
    Real.sqrt_nonneg _
  nlinarith

theorem aux_psf_grad_le_maxObs (i n : ℕ) (z x : Vec d) (omega : PotentialSample d)
    (hx : x ∈ translatedCube d (n : ℤ) z) :
    Homogenization.euclideanNorm (shellGradient (omega i) x) ≤
      ((3:ℝ) ^ i)⁻¹ * aux_psf_maxObs i n z omega := by
  have h := aux_psf_le_maxObs i n z x omega hx
  have hrp : (0:ℝ) < (3:ℝ) ^ i := by positivity
  have habs : 0 ≤ |omega i x| := abs_nonneg _
  rw [inv_mul_eq_div, le_div_iff₀ hrp]
  nlinarith


theorem aux_psf_Dterm1_le_one (M : GMCModel d) (s : ℝ) (hs0 : 0 < s) (k : ℕ)
    (z : Vec d) (omega : PotentialSample d) :
    sSup {v : ℝ≥0∞ | ∃ j l : ℕ, j ≤ k ∧ l ≤ k ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
      OnTriadicGrid l (x - z) ∧ x - z ∈ cube d (j:ℤ) \ cube d ((j:ℤ) - 1) ∧
      v = ENNReal.ofReal ((3:ℝ) ^ (-(s / 2) * ((k:ℝ) - (l:ℝ)))) *
        (min (aux_psf_Jval M l omega x) 1) ^ (1/2 : ℝ)} ≤ 1 := by
  refine sSup_le ?_
  rintro v ⟨j, l, hjk, hlk, hlj, x, hgrid, hann, rfl⟩
  have h1 : ENNReal.ofReal ((3:ℝ) ^ (-(s / 2) * ((k:ℝ) - (l:ℝ)))) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    have hlk' : (l:ℝ) ≤ (k:ℝ) := by exact_mod_cast hlk
    nlinarith
  have h2 : (min (aux_psf_Jval M l omega x) 1) ^ (1/2 : ℝ) ≤ 1 :=
    ENNReal.rpow_le_one (min_le_right _ _) (by norm_num)
  calc ENNReal.ofReal ((3:ℝ) ^ (-(s / 2) * ((k:ℝ) - (l:ℝ)))) *
      (min (aux_psf_Jval M l omega x) 1) ^ (1/2 : ℝ) ≤ 1 * 1 := by gcongr
    _ = 1 := by ring

/-- The finite majorant of the shell-block term of the drift score. -/
def aux_psf_Dmaj2 (s : ℝ) (k : ℕ) (z : Vec d) (omega : PotentialSample d) : ℝ≥0∞ :=
  (Finset.range (k + 1)).sup (fun j : ℕ =>
    ENNReal.ofReal ((3:ℝ) ^ (-(s / 8) * ((k:ℝ) - (j:ℝ)))) *
      ENNReal.ofReal (∑ i ∈ Finset.Icc (j + 1) k, aux_psf_maxObs i k z omega))

theorem aux_psf_Dmaj2_ne_top (s : ℝ) (k : ℕ) (z : Vec d)
    (omega : PotentialSample d) : aux_psf_Dmaj2 s k z omega ≠ ⊤ := by
  have hbot : (⊥ : ℝ≥0∞) < ⊤ := by simp
  rw [← lt_top_iff_ne_top, aux_psf_Dmaj2, Finset.sup_lt_iff hbot]
  intro j _
  rw [lt_top_iff_ne_top]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

theorem aux_psf_Dterm2_le (s : ℝ) (k : ℕ) (z : Vec d)
    (omega : PotentialSample d) :
    sSup {v : ℝ≥0∞ | ∃ j : ℕ, j ≤ k ∧
      v = ENNReal.ofReal ((3:ℝ) ^ (-(s / 8) * ((k:ℝ) - (j:ℝ)))) *
        sSup {w : ℝ≥0∞ | ∃ x ∈ translatedCube d (k:ℤ) z,
          w = ENNReal.ofReal |shellBlock k j omega x|}} ≤
      aux_psf_Dmaj2 s k z omega := by
  refine sSup_le ?_
  rintro v ⟨j, hjk, rfl⟩
  have hbound : sSup {w : ℝ≥0∞ | ∃ x ∈ translatedCube d (k:ℤ) z,
      w = ENNReal.ofReal |shellBlock k j omega x|} ≤
      ENNReal.ofReal (∑ i ∈ Finset.Icc (j + 1) k, aux_psf_maxObs i k z omega) := by
    refine aux_psf_normOn_le_of_le k z _ _ ?_
    intro x hx
    calc |shellBlock k j omega x| =
        |∑ i ∈ Finset.Icc (j + 1) k, omega i x| := rfl
      _ ≤ ∑ i ∈ Finset.Icc (j + 1) k, |omega i x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Icc (j + 1) k, aux_psf_maxObs i k z omega :=
          Finset.sum_le_sum (fun i _ => aux_psf_abs_le_maxObs i k z x omega hx)
  have hstep : ENNReal.ofReal ((3:ℝ) ^ (-(s / 8) * ((k:ℝ) - (j:ℝ)))) *
      sSup {w : ℝ≥0∞ | ∃ x ∈ translatedCube d (k:ℤ) z,
        w = ENNReal.ofReal |shellBlock k j omega x|} ≤
      ENNReal.ofReal ((3:ℝ) ^ (-(s / 8) * ((k:ℝ) - (j:ℝ)))) *
        ENNReal.ofReal (∑ i ∈ Finset.Icc (j + 1) k, aux_psf_maxObs i k z omega) := by
    gcongr
  refine hstep.trans (Finset.le_sup (f := fun j : ℕ =>
    ENNReal.ofReal ((3:ℝ) ^ (-(s / 8) * ((k:ℝ) - (j:ℝ)))) *
      ENNReal.ofReal (∑ i ∈ Finset.Icc (j + 1) k, aux_psf_maxObs i k z omega))
    (Finset.mem_range.2 (by omega : j < k + 1)))

theorem aux_psf_Dterm3_le (s : ℝ) (k : ℕ) (z : Vec d)
    (omega : PotentialSample d) :
    ENNReal.ofReal ((3:ℝ) ^ (-(s / 8) * (k:ℝ))) *
        sSup {w : ℝ≥0∞ | ∃ x ∈ translatedCube d (k:ℤ) z,
          w = ENNReal.ofReal |omega 0 x|} ≤
      ENNReal.ofReal ((3:ℝ) ^ (-(s / 8) * (k:ℝ))) *
        ENNReal.ofReal (aux_psf_maxObs 0 k z omega) := by
  gcongr
  exact aux_psf_normOn_le_of_le k z _ _
    (fun x hx => aux_psf_abs_le_maxObs 0 k z x omega hx)


/-- The measurable majorant of the gradient-tail term of the drift score. -/
def aux_psf_Dmaj4 (k : ℕ) (z : Vec d) (j : ℕ) (omega : PotentialSample d) : ℝ≥0∞ :=
  if k ≤ j then
    ENNReal.ofReal ((3:ℝ) ^ k * ((3:ℝ) ^ j)⁻¹ * aux_psf_maxObs j k z omega)
  else 0

theorem aux_psf_Dmaj4_measurable (k : ℕ) (z : Vec d) (j : ℕ) :
    Measurable (fun omega : PotentialSample d => aux_psf_Dmaj4 k z j omega) := by
  unfold aux_psf_Dmaj4
  by_cases h : k ≤ j
  · simp only [h, if_true]
    exact (((aux_psf_maxObs_measurable j k z).const_mul _)).ennreal_ofReal
  · simp only [h, if_false]
    exact measurable_const

def aux_psf_Dbound4 (M : GMCModel d) (k j : ℕ) : ℝ :=
  (3:ℝ) ^ k * ((3:ℝ) ^ j)⁻¹ * (2 * aux_psf_sigma M *
    Real.sqrt (1 + Real.log (2 * (((2 * 3 ^ k + 1) ^ d : ℕ) : ℝ))))

theorem aux_psf_Dbound4_nonneg (M : GMCModel d) (k j : ℕ) :
    0 ≤ aux_psf_Dbound4 M k j := by
  have h4 := (aux_psf_sigma_pos M).le
  have h2 : (0:ℝ) ≤ Real.sqrt (1 + Real.log
      (2 * (((2 * 3 ^ k + 1) ^ d : ℕ) : ℝ))) := Real.sqrt_nonneg _
  unfold aux_psf_Dbound4
  positivity

theorem aux_psf_lintegral_Dmaj4 (M : GMCModel d) (k : ℕ) (z : Vec d) (j : ℕ) :
    (∫⁻ omega, aux_psf_Dmaj4 k z j omega ∂M.P.toMeasure) ≤
      ENNReal.ofReal (aux_psf_Dbound4 M k j) := by
  unfold aux_psf_Dmaj4 aux_psf_Dbound4
  by_cases h : k ≤ j
  · simp only [h, if_true]
    have hc : (0:ℝ) ≤ (3:ℝ) ^ k * ((3:ℝ) ^ j)⁻¹ := by positivity
    have hstep : ∀ omega : PotentialSample d,
        ENNReal.ofReal ((3:ℝ) ^ k * ((3:ℝ) ^ j)⁻¹ * aux_psf_maxObs j k z omega) =
        ENNReal.ofReal ((3:ℝ) ^ k * ((3:ℝ) ^ j)⁻¹) *
          ENNReal.ofReal (aux_psf_maxObs j k z omega) := by
      intro omega; rw [ENNReal.ofReal_mul hc]
    simp only [hstep]
    rw [lintegral_const_mul _ (aux_psf_maxObs_measurable j k z).ennreal_ofReal]
    calc ENNReal.ofReal ((3:ℝ) ^ k * ((3:ℝ) ^ j)⁻¹) *
        ∫⁻ omega, ENNReal.ofReal (aux_psf_maxObs j k z omega) ∂M.P.toMeasure ≤
        ENNReal.ofReal ((3:ℝ) ^ k * ((3:ℝ) ^ j)⁻¹) *
          ENNReal.ofReal (2 * aux_psf_sigma M *
            Real.sqrt (1 + Real.log
              (2 * (((2 * 3 ^ k + 1) ^ d : ℕ) : ℝ)))) := by
          gcongr
          exact aux_psf_lintegral_maxObs M j k z
      _ = ENNReal.ofReal ((3:ℝ) ^ k * ((3:ℝ) ^ j)⁻¹ *
            (2 * aux_psf_sigma M * Real.sqrt (1 + Real.log
              (2 * (((2 * 3 ^ k + 1) ^ d : ℕ) : ℝ))))) :=
          (ENNReal.ofReal_mul hc).symm
  · simp only [h, if_false, lintegral_const, zero_mul]
    exact zero_le

theorem aux_psf_summable_Dbound4 (M : GMCModel d) (k : ℕ) :
    Summable (fun j : ℕ => aux_psf_Dbound4 M k j) := by
  have hgeom : Summable (fun j : ℕ => ((3:ℝ)⁻¹) ^ j) := by
    refine summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have heq : ∀ j : ℕ, aux_psf_Dbound4 M k j =
      ((3:ℝ) ^ k * (2 * aux_psf_sigma M * Real.sqrt (1 + Real.log
        (2 * (((2 * 3 ^ k + 1) ^ d : ℕ) : ℝ))))) * ((3:ℝ)⁻¹) ^ j := by
    intro j
    unfold aux_psf_Dbound4
    rw [inv_pow]
    ring
  exact (hgeom.mul_left _).congr (fun j => (heq j).symm)

theorem aux_psf_Dmaj4_tsum_ae (M : GMCModel d) (k : ℕ) (z : Vec d) :
    ∀ᵐ omega ∂M.P.toMeasure, (∑' j : ℕ, aux_psf_Dmaj4 k z j omega) ≠ ⊤ := by
  have hmeas : ∀ j : ℕ, AEMeasurable (fun omega : PotentialSample d =>
      aux_psf_Dmaj4 k z j omega) M.P.toMeasure :=
    fun j => (aux_psf_Dmaj4_measurable k z j).aemeasurable
  have hint : (∫⁻ omega, (∑' j : ℕ, aux_psf_Dmaj4 k z j omega)
      ∂M.P.toMeasure) ≠ ⊤ := by
    rw [lintegral_tsum hmeas]
    refine ne_top_of_le_ne_top ?_
      (ENNReal.tsum_le_tsum (aux_psf_lintegral_Dmaj4 M k z))
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => aux_psf_Dbound4_nonneg M k j)
      (aux_psf_summable_Dbound4 M k)]
    exact ENNReal.ofReal_ne_top
  have hlt := ae_lt_top' (AEMeasurable.ennreal_tsum hmeas) hint
  filter_upwards [hlt] with omega h
  exact h.ne

theorem aux_psf_Dterm4_le (k : ℕ) (z : Vec d) (omega : PotentialSample d) :
    (∑' j : ℕ, if k ≤ j then
        ENNReal.ofReal ((3:ℝ) ^ k) *
          sSup {w : ℝ≥0∞ | ∃ x ∈ translatedCube d (k:ℤ) z,
            w = ENNReal.ofReal
              |Homogenization.euclideanNorm (shellGradient (omega j) x)|}
      else 0) ≤ ∑' j : ℕ, aux_psf_Dmaj4 k z j omega := by
  refine ENNReal.tsum_le_tsum ?_
  intro j
  unfold aux_psf_Dmaj4
  by_cases h : k ≤ j
  · simp only [h, if_true]
    have hc : (0:ℝ) ≤ (3:ℝ) ^ k := by positivity
    have hb : sSup {w : ℝ≥0∞ | ∃ x ∈ translatedCube d (k:ℤ) z,
        w = ENNReal.ofReal
          |Homogenization.euclideanNorm (shellGradient (omega j) x)|} ≤
        ENNReal.ofReal (((3:ℝ) ^ j)⁻¹ * aux_psf_maxObs j k z omega) := by
      refine aux_psf_normOn_le_of_le k z _ _ ?_
      intro x hx
      have hnn : (0:ℝ) ≤ Homogenization.euclideanNorm (shellGradient (omega j) x) :=
        Real.sqrt_nonneg _
      rw [abs_of_nonneg hnn]
      exact aux_psf_grad_le_maxObs j k z x omega hx
    calc ENNReal.ofReal ((3:ℝ) ^ k) *
        sSup {w : ℝ≥0∞ | ∃ x ∈ translatedCube d (k:ℤ) z,
          w = ENNReal.ofReal
            |Homogenization.euclideanNorm (shellGradient (omega j) x)|} ≤
        ENNReal.ofReal ((3:ℝ) ^ k) *
          ENNReal.ofReal (((3:ℝ) ^ j)⁻¹ * aux_psf_maxObs j k z omega) := by gcongr
      _ = ENNReal.ofReal ((3:ℝ) ^ k * (((3:ℝ) ^ j)⁻¹ * aux_psf_maxObs j k z omega)) :=
          (ENNReal.ofReal_mul hc).symm
      _ = ENNReal.ofReal ((3:ℝ) ^ k * ((3:ℝ) ^ j)⁻¹ * aux_psf_maxObs j k z omega) := by
          rw [mul_assoc]
  · simp only [h, if_false]
    exact le_refl _


theorem aux_psf_lintegral_rpow_inv_le {Omega : Type} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {X : Omega → ℝ≥0∞}
    (hX : AEMeasurable X mu) {p : ℝ} (hp : 1 < p) :
    (∫⁻ omega, (X omega) ^ (1 / p) ∂mu) ≤ (∫⁻ omega, X omega ∂mu) ^ (1 / p) := by
  have hp0 : p ≠ 0 := by positivity
  have hpq : p.HolderConjugate (Real.conjExponent p) :=
    Real.HolderConjugate.conjExponent hp
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq mu hpq
    (f := fun omega => (X omega) ^ (1 / p)) (g := fun _ => (1 : ℝ≥0∞))
    (hX.pow_const _) aemeasurable_const
  have hone : (∫⁻ _omega : Omega, (1 : ℝ≥0∞) ∂mu) = 1 := by simp
  have hfp : ∀ omega, ((X omega) ^ (1 / p)) ^ p = X omega := by
    intro omega
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0, ENNReal.rpow_one]
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, hone, ENNReal.one_rpow,
    mul_one, hfp] at h
  exact h

theorem aux_psf_convex_translatedCube (n : ℤ) (z : Vec d) :
    Convex ℝ (translatedCube d n z) := by
  intro x hx y hy a b ha hb hab
  rw [aux_psf_mem_translatedCube_iff] at hx hy ⊢
  intro i
  have hxi := hx i
  have hyi := hy i
  have hval : (a • x + b • y) i - z i =
      a * (x i - z i) + b * (y i - z i) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hz : a * z i + b * z i = z i := by rw [← add_mul, hab, one_mul]
    linarith
  rw [hval]
  have hstrict : a * |x i - z i| + b * |y i - z i| < (3:ℝ) ^ n / 2 := by
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · have hb1 : b = 1 := by linarith
      have h1 : a * |x i - z i| = 0 := by rw [← ha0]; ring
      rw [h1, hb1, one_mul, zero_add]
      exact hyi
    · have h1 : a * |x i - z i| < a * ((3:ℝ) ^ n / 2) :=
        mul_lt_mul_of_pos_left hxi hapos
      have h2 : b * |y i - z i| ≤ b * ((3:ℝ) ^ n / 2) :=
        mul_le_mul_of_nonneg_left hyi.le hb
      have : a * ((3:ℝ) ^ n / 2) + b * ((3:ℝ) ^ n / 2) = (3:ℝ) ^ n / 2 := by
        rw [← add_mul, hab, one_mul]
      linarith
  calc |a * (x i - z i) + b * (y i - z i)| ≤
      |a * (x i - z i)| + |b * (y i - z i)| := abs_add_le _ _
    _ = a * |x i - z i| + b * |y i - z i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ < (3:ℝ) ^ n / 2 := hstrict

theorem aux_psf_deriv_le_maxObs (hd : (1:ℝ) ≤ (d : ℝ)) (i n : ℕ) (z x : Vec d)
    (omega : PotentialSample d) (hx : x ∈ translatedCube d (n : ℤ) z) :
    ‖PotentialField.deriv (omega i) x‖ ≤
      ((3:ℝ) ^ i)⁻¹ * aux_psf_maxObs i n z omega := by
  obtain ⟨k, hkmem, hk⟩ := aux_psf_cover' n z x hx
  set y : Vec d := aux_psf_center n z k with hy
  have hderiv : ‖PotentialField.deriv (omega i) x‖ ≤
      (PotentialField.translate y (omega i)).unitCubeDerivNorm := by
    have h := PotentialField.norm_deriv_le_unitCubeDerivNorm
      (PotentialField.translate y (omega i)) (x := x - y) hk
    rwa [aux_psf_deriv_translate, sub_add_cancel] at h
  have hcell : (3:ℝ) ^ i * (d : ℝ) *
      (PotentialField.translate y (omega i)).unitCubeDerivNorm ≤
      aux_psf_cellObs i y omega := by
    have h1 := PotentialField.unitCubeValueNorm_nonneg
      (PotentialField.translate y (omega i))
    unfold aux_psf_cellObs
    linarith
  have hmax : aux_psf_cellObs i y omega ≤ aux_psf_maxObs i n z omega :=
    Finset.le_sup' (f := fun k => aux_psf_cellObs i (aux_psf_center n z k) omega)
      hkmem
  have hD0 : 0 ≤ (PotentialField.translate y (omega i)).unitCubeDerivNorm :=
    PotentialField.unitCubeDerivNorm_nonneg _
  have h3 : (0:ℝ) < (3:ℝ) ^ i := by positivity
  rw [inv_mul_eq_div, le_div_iff₀ h3]
  have hstep1 : ‖PotentialField.deriv (omega i) x‖ * (3:ℝ) ^ i ≤
      (PotentialField.translate y (omega i)).unitCubeDerivNorm * (3:ℝ) ^ i :=
    mul_le_mul_of_nonneg_right hderiv h3.le
  have hstep2 : (PotentialField.translate y (omega i)).unitCubeDerivNorm * (3:ℝ) ^ i ≤
      (3:ℝ) ^ i * (d : ℝ) *
        (PotentialField.translate y (omega i)).unitCubeDerivNorm := by
    nlinarith [mul_nonneg (mul_nonneg h3.le hD0) (by linarith : (0:ℝ) ≤ (d:ℝ) - 1)]
  linarith


theorem aux_psf_center_mem (n : ℕ) (z : Vec d) :
    z ∈ translatedCube d (n : ℤ) z := by
  rw [aux_psf_mem_translatedCube_iff]
  intro i
  simp only [sub_self, abs_zero]
  positivity

theorem aux_psf_diff_le (hd : (1:ℝ) ≤ (d : ℝ)) (i n : ℕ) (z x : Vec d)
    (omega : PotentialSample d) (hx : x ∈ translatedCube d (n : ℤ) z) :
    |omega i x - omega i z| ≤
      ((3:ℝ) ^ i)⁻¹ * aux_psf_maxObs i n z omega * ((3:ℝ) ^ (n : ℤ) / 2) := by
  have hconv := aux_psf_convex_translatedCube (d := d) (n : ℤ) z
  have hzmem := aux_psf_center_mem (d := d) n z
  have hfd : ∀ w ∈ translatedCube d (n : ℤ) z,
      HasFDerivWithinAt (fun u : Vec d => (omega i : Vec d → ℝ) u)
        (PotentialField.deriv (omega i) w) (translatedCube d (n : ℤ) z) w :=
    fun w _ => ((omega i).hasFDerivAt w).hasFDerivWithinAt
  have hbound : ∀ w ∈ translatedCube d (n : ℤ) z,
      ‖PotentialField.deriv (omega i) w‖ ≤
        ((3:ℝ) ^ i)⁻¹ * aux_psf_maxObs i n z omega :=
    fun w hw => aux_psf_deriv_le_maxObs hd i n z w omega hw
  have hmain := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le hfd hbound
    hzmem hx
  have hnorm : ‖x - z‖ ≤ (3:ℝ) ^ (n : ℤ) / 2 := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro k
    rw [Real.norm_eq_abs]
    have := (aux_psf_mem_translatedCube_iff.1 hx) k
    simp only [Pi.sub_apply]
    linarith
  have hC0 : 0 ≤ ((3:ℝ) ^ i)⁻¹ * aux_psf_maxObs i n z omega := by
    have := aux_psf_maxObs_nonneg i n z omega
    positivity
  calc |omega i x - omega i z| = ‖(omega i : Vec d → ℝ) x - (omega i : Vec d → ℝ) z‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ((3:ℝ) ^ i)⁻¹ * aux_psf_maxObs i n z omega * ‖x - z‖ := hmain
    _ ≤ ((3:ℝ) ^ i)⁻¹ * aux_psf_maxObs i n z omega * ((3:ℝ) ^ (n : ℤ) / 2) :=
        mul_le_mul_of_nonneg_left hnorm hC0


theorem aux_psf_prod_ofReal_exp (I : Finset ℕ) (f : ℕ → ℝ) :
    ∏ i ∈ I, ENNReal.ofReal (Real.exp (f i)) =
      ENNReal.ofReal (Real.exp (∑ i ∈ I, f i)) := by
  classical
  induction I using Finset.induction with
  | empty => simp
  | insert a I ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, Real.exp_add,
        ENNReal.ofReal_mul (Real.exp_nonneg _)]

/-- The measurable majorant of the pointwise product part of the product score. -/
def aux_psf_Amaj (m : ℕ) (z : Vec d) (j : ℕ)
    (omega : PotentialSample d) : ℝ≥0∞ :=
  (aux_psf_cells d (m + 1 + j)).sup' (aux_psf_cells_nonempty d (m + 1 + j))
    (fun k => ENNReal.ofReal (Real.exp (∑ i ∈ Finset.Icc (m - j) (m + j),
      aux_psf_cellObs i (aux_psf_center (m + 1 + j) z k) omega)))

/-- The tail weight of the product score. -/
def aux_psf_lam (m j i : ℕ) : ℝ := 2 * (3:ℝ) ^ (m + 1 + j) * ((3:ℝ) ^ i)⁻¹

/-- The measurable majorant of the tail product part of the product score. -/
def aux_psf_Bmaj (m : ℕ) (z : Vec d) (j : ℕ)
    (omega : PotentialSample d) : ℝ≥0∞ :=
  ⨆ K : ℕ, ENNReal.ofReal (Real.exp (∑ i ∈ Finset.Icc (m + j) (m + j + K),
    aux_psf_lam m j i * aux_psf_maxObs i (m + 1 + j) z omega))

theorem aux_psf_Pterm_le (hd : (1:ℝ) ≤ (d : ℝ)) (m : ℕ) (z : Vec d) (j : ℕ)
    (omega : PotentialSample d) :
    sSup {w : ℝ≥0∞ | ∃ x ∈ translatedCube d ((m:ℤ) + 1 + (j:ℤ)) z,
      w = (∏ i ∈ Finset.Icc (m - j) (m + j),
            ENNReal.ofReal (Real.exp |omega i x|)) +
          sSup {u : ℝ≥0∞ | ∃ K : ℕ, u = ∏ i ∈ Finset.Icc (m + j) (m + j + K),
            ENNReal.ofReal (Real.exp (4 * |omega i x - omega i z|))}} ≤
      aux_psf_Amaj m z j omega + aux_psf_Bmaj m z j omega := by
  have hcast : ((m:ℤ) + 1 + (j:ℤ)) = (((m + 1 + j : ℕ)) : ℤ) := by push_cast; ring
  refine sSup_le ?_
  rintro w ⟨x, hx, rfl⟩
  rw [hcast] at hx
  obtain ⟨k, hkmem, hk⟩ := aux_psf_cover' (m + 1 + j) z x hx
  refine add_le_add ?_ ?_
  · rw [aux_psf_prod_ofReal_exp]
    refine le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
      (Finset.le_sup' (f := fun k : Fin d → ℕ =>
        ENNReal.ofReal (Real.exp (∑ i ∈ Finset.Icc (m - j) (m + j),
          aux_psf_cellObs i (aux_psf_center (m + 1 + j) z k) omega))) hkmem)
    refine Finset.sum_le_sum ?_
    intro i _
    have h1 := aux_psf_abs_le_cellObs i (aux_psf_center (m + 1 + j) z k) x omega hk
    have h2 := PotentialField.unitCubeDerivNorm_nonneg
      (PotentialField.translate (aux_psf_center (m + 1 + j) z k) (omega i))
    have h3 : (0:ℝ) ≤ (3:ℝ) ^ i * (d : ℝ) := by positivity
    unfold aux_psf_cellObs
    nlinarith
  · refine sSup_le ?_
    rintro u ⟨K, rfl⟩
    rw [aux_psf_prod_ofReal_exp]
    refine le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
      (le_iSup (fun K : ℕ => ENNReal.ofReal (Real.exp
        (∑ i ∈ Finset.Icc (m + j) (m + j + K),
          aux_psf_lam m j i * aux_psf_maxObs i (m + 1 + j) z omega))) K)
    refine Finset.sum_le_sum ?_
    intro i _
    have h := aux_psf_diff_le hd i (m + 1 + j) z x omega hx
    have hlam : aux_psf_lam m j i * aux_psf_maxObs i (m + 1 + j) z omega =
        4 * (((3:ℝ) ^ i)⁻¹ * aux_psf_maxObs i (m + 1 + j) z omega *
          ((3:ℝ) ^ ((m + 1 + j : ℕ) : ℤ) / 2)) := by
      unfold aux_psf_lam
      rw [zpow_natCast]
      ring
    rw [hlam]
    linarith


theorem aux_psf_cell_exp_lin (M : GMCModel d) (i : ℕ) (y : Vec d) (mu : ℝ) :
    (∫⁻ omega, ENNReal.ofReal (Real.exp (mu * aux_psf_cellObs i y omega))
      ∂M.P.toMeasure) ≤
      ENNReal.ofReal (Real.exp (mu ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2 := by
  have hsig := aux_psf_sigma_pos M
  have hs : aux_psf_sigma M ≠ 0 := ne_of_gt hsig
  have hpt : ∀ omega : PotentialSample d,
      ENNReal.ofReal (Real.exp (mu * aux_psf_cellObs i y omega)) ≤
      ENNReal.ofReal (Real.exp (mu ^ 2 * aux_psf_sigma M ^ 2 / 4)) *
        ENNReal.ofReal (Real.exp
          ((aux_psf_cellObs i y omega / aux_psf_sigma M) ^ 2)) := by
    intro omega
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    set t := aux_psf_cellObs i y omega with ht
    have key : (t / aux_psf_sigma M - mu * aux_psf_sigma M / 2) ^ 2 =
        (t / aux_psf_sigma M) ^ 2 - mu * t + mu ^ 2 * aux_psf_sigma M ^ 2 / 4 := by
      field_simp
      ring
    have hnn := sq_nonneg (t / aux_psf_sigma M - mu * aux_psf_sigma M / 2)
    rw [key] at hnn
    linarith
  have hmeas : Measurable fun omega : PotentialSample d =>
      ENNReal.ofReal (Real.exp
        ((aux_psf_cellObs i y omega / aux_psf_sigma M) ^ 2)) :=
    ((((aux_psf_cellObs_measurable i y).div_const _).pow_const _).exp).ennreal_ofReal
  calc (∫⁻ omega, ENNReal.ofReal (Real.exp (mu * aux_psf_cellObs i y omega))
      ∂M.P.toMeasure) ≤
      ∫⁻ omega, (ENNReal.ofReal (Real.exp (mu ^ 2 * aux_psf_sigma M ^ 2 / 4)) *
        ENNReal.ofReal (Real.exp
          ((aux_psf_cellObs i y omega / aux_psf_sigma M) ^ 2))) ∂M.P.toMeasure :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (Real.exp (mu ^ 2 * aux_psf_sigma M ^ 2 / 4)) *
        ∫⁻ omega, ENNReal.ofReal (Real.exp
          ((aux_psf_cellObs i y omega / aux_psf_sigma M) ^ 2)) ∂M.P.toMeasure :=
        lintegral_const_mul _ hmeas
    _ ≤ ENNReal.ofReal (Real.exp (mu ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2 := by
        gcongr
        exact aux_psf_cell_exp M i y

theorem aux_psf_indep_cellObs (M : GMCModel d) (y : Vec d) (mu : ℝ) :
    ProbabilityTheory.iIndepFun
      (fun (i : ℕ) (omega : PotentialSample d) =>
        ENNReal.ofReal (Real.exp (mu * aux_psf_cellObs i y omega)))
      M.P.toMeasure := by
  refine M.shellPrefix.independent.comp
    (fun (i : ℕ) (h : PotentialField d) =>
      ENNReal.ofReal (Real.exp (mu *
        ((PotentialField.translate y h).unitCubeValueNorm +
          (3:ℝ) ^ i * (d:ℝ) *
            (PotentialField.translate y h).unitCubeDerivNorm)))) ?_
  intro i
  refine Measurable.ennreal_ofReal ?_
  refine Real.measurable_exp.comp ?_
  refine Measurable.const_mul ?_ _
  exact (PotentialField.unitCubeValueNorm_measurable.comp
      (PotentialField.measurable_translate y)).add
    ((PotentialField.unitCubeDerivNorm_measurable.comp
      (PotentialField.measurable_translate y)).const_mul _)


theorem aux_psf_Amaj_measurable (m : ℕ) (z : Vec d) (j : ℕ) :
    Measurable (fun omega : PotentialSample d => aux_psf_Amaj m z j omega) := by
  have h : Measurable ((aux_psf_cells d (m + 1 + j)).sup'
      (aux_psf_cells_nonempty d (m + 1 + j))
      (fun k (omega : PotentialSample d) =>
        ENNReal.ofReal (Real.exp (∑ i ∈ Finset.Icc (m - j) (m + j),
          aux_psf_cellObs i (aux_psf_center (m + 1 + j) z k) omega)))) := by
    refine Finset.measurable_sup' _ (fun k _ => ?_)
    refine Measurable.ennreal_ofReal (Real.measurable_exp.comp ?_)
    exact Finset.measurable_sum _ (fun i _ =>
      aux_psf_cellObs_measurable i (aux_psf_center (m + 1 + j) z k))
  convert h using 1
  funext omega
  unfold aux_psf_Amaj
  rw [Finset.sup'_apply]

theorem aux_psf_ofReal_exp_rpow (a q : ℝ) :
    (ENNReal.ofReal (Real.exp a)) ^ q = ENNReal.ofReal (Real.exp (a * q)) := by
  rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos a), Real.exp_mul]

theorem aux_psf_lintegral_Amaj (M : GMCModel d) (m : ℕ) (z : Vec d) (j : ℕ)
    (q : ℝ) (hq : 1 < q) :
    (∫⁻ omega, aux_psf_Amaj m z j omega ∂M.P.toMeasure) ≤
      (((aux_psf_cells d (m + 1 + j)).card : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (q ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2) ^
          ((Finset.Icc (m - j) (m + j)).card)) ^ (1 / q) := by
  have hq0 : (0:ℝ) < q := by linarith
  have hAmeas := aux_psf_Amaj_measurable (d := d) m z j
  have hX : AEMeasurable (fun omega : PotentialSample d =>
      (aux_psf_Amaj m z j omega) ^ q) M.P.toMeasure :=
    (hAmeas.pow_const q).aemeasurable
  have h1 : (∫⁻ omega, aux_psf_Amaj m z j omega ∂M.P.toMeasure) ≤
      (∫⁻ omega, (aux_psf_Amaj m z j omega) ^ q ∂M.P.toMeasure) ^ (1 / q) := by
    have h := aux_psf_lintegral_rpow_inv_le (Omega := PotentialSample d)
      M.P.toMeasure (X := fun omega => (aux_psf_Amaj m z j omega) ^ q) hX hq
    have hid : ∀ omega : PotentialSample d,
        ((aux_psf_Amaj m z j omega) ^ q) ^ (1 / q) = aux_psf_Amaj m z j omega := by
      intro omega
      rw [← ENNReal.rpow_mul, mul_one_div_cancel (ne_of_gt hq0), ENNReal.rpow_one]
    simpa only [hid] using h
  refine h1.trans ?_
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  have hpt : ∀ omega : PotentialSample d, (aux_psf_Amaj m z j omega) ^ q ≤
      ∑ k ∈ aux_psf_cells d (m + 1 + j),
        ENNReal.ofReal (Real.exp (q * ∑ i ∈ Finset.Icc (m - j) (m + j),
          aux_psf_cellObs i (aux_psf_center (m + 1 + j) z k) omega)) := by
    intro omega
    obtain ⟨k0, hk0mem, hk0⟩ := (aux_psf_cells d (m + 1 + j)).exists_mem_eq_sup'
      (aux_psf_cells_nonempty d (m + 1 + j))
      (fun k => ENNReal.ofReal (Real.exp (∑ i ∈ Finset.Icc (m - j) (m + j),
        aux_psf_cellObs i (aux_psf_center (m + 1 + j) z k) omega)))
    have hrw : (aux_psf_Amaj m z j omega) ^ q =
        ENNReal.ofReal (Real.exp (q * ∑ i ∈ Finset.Icc (m - j) (m + j),
          aux_psf_cellObs i (aux_psf_center (m + 1 + j) z k0) omega)) := by
      unfold aux_psf_Amaj
      rw [hk0, aux_psf_ofReal_exp_rpow, mul_comm]
    rw [hrw]
    exact Finset.single_le_sum
      (f := fun k => ENNReal.ofReal (Real.exp (q * ∑ i ∈ Finset.Icc (m - j) (m + j),
        aux_psf_cellObs i (aux_psf_center (m + 1 + j) z k) omega)))
      (fun k _ => zero_le) hk0mem
  have hterm : ∀ k : Fin d → ℕ,
      (∫⁻ omega, ENNReal.ofReal (Real.exp
        (q * ∑ i ∈ Finset.Icc (m - j) (m + j),
          aux_psf_cellObs i (aux_psf_center (m + 1 + j) z k) omega))
        ∂M.P.toMeasure) ≤
      (ENNReal.ofReal (Real.exp (q ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2) ^
        ((Finset.Icc (m - j) (m + j)).card) := by
    intro k
    have hsplit : ∀ omega : PotentialSample d,
        ENNReal.ofReal (Real.exp (q * ∑ i ∈ Finset.Icc (m - j) (m + j),
          aux_psf_cellObs i (aux_psf_center (m + 1 + j) z k) omega)) =
        ∏ i ∈ Finset.Icc (m - j) (m + j),
          ENNReal.ofReal (Real.exp
            (q * aux_psf_cellObs i (aux_psf_center (m + 1 + j) z k) omega)) := by
      intro omega
      rw [aux_psf_prod_ofReal_exp, Finset.mul_sum]
    simp only [hsplit]
    rw [ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun
      _ _ (aux_psf_indep_cellObs M (aux_psf_center (m + 1 + j) z k) q)
      (fun i => (((aux_psf_cellObs_measurable i
        (aux_psf_center (m + 1 + j) z k)).const_mul _).exp).ennreal_ofReal)]
    calc ∏ i ∈ Finset.Icc (m - j) (m + j),
        ∫⁻ omega, ENNReal.ofReal (Real.exp
          (q * aux_psf_cellObs i (aux_psf_center (m + 1 + j) z k) omega))
          ∂M.P.toMeasure ≤
        ∏ _i ∈ Finset.Icc (m - j) (m + j),
          (ENNReal.ofReal (Real.exp (q ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2) :=
          Finset.prod_le_prod' (fun i _ =>
            aux_psf_cell_exp_lin M i (aux_psf_center (m + 1 + j) z k) q)
      _ = (ENNReal.ofReal (Real.exp (q ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2) ^
            ((Finset.Icc (m - j) (m + j)).card) := by rw [Finset.prod_const]
  refine le_trans (lintegral_mono hpt) ?_
  rw [lintegral_finset_sum _ (fun k _ => by
    refine Measurable.ennreal_ofReal (Real.measurable_exp.comp ?_)
    refine Measurable.const_mul ?_ _
    exact Finset.measurable_sum _ (fun i _ =>
      aux_psf_cellObs_measurable i (aux_psf_center (m + 1 + j) z k)))]
  calc ∑ k ∈ aux_psf_cells d (m + 1 + j),
      ∫⁻ omega, ENNReal.ofReal (Real.exp
        (q * ∑ i ∈ Finset.Icc (m - j) (m + j),
          aux_psf_cellObs i (aux_psf_center (m + 1 + j) z k) omega))
        ∂M.P.toMeasure ≤
      ∑ _k ∈ aux_psf_cells d (m + 1 + j),
        (ENNReal.ofReal (Real.exp (q ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2) ^
          ((Finset.Icc (m - j) (m + j)).card) :=
        Finset.sum_le_sum (fun k _ => hterm k)
    _ = ((aux_psf_cells d (m + 1 + j)).card : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (q ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2) ^
          ((Finset.Icc (m - j) (m + j)).card) := by
        rw [Finset.sum_const, nsmul_eq_mul]


theorem aux_psf_prod_rpow (C : ℝ≥0∞) (hC0 : C ≠ 0) (hCt : C ≠ ⊤)
    (s : Finset ℕ) (a : ℕ → ℝ) :
    ∏ i ∈ s, C ^ (a i) = C ^ (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
      rw [Finset.prod_insert hx, Finset.sum_insert hx, ih,
        ← ENNReal.rpow_add _ _ hC0 hCt]

theorem aux_psf_indep_maxObs (M : GMCModel d) (n : ℕ) (z : Vec d) (lam : ℕ → ℝ) :
    ProbabilityTheory.iIndepFun
      (fun (i : ℕ) (omega : PotentialSample d) =>
        ENNReal.ofReal (Real.exp (lam i * aux_psf_maxObs i n z omega)))
      M.P.toMeasure := by
  refine M.shellPrefix.independent.comp
    (fun (i : ℕ) (h : PotentialField d) =>
      ENNReal.ofReal (Real.exp (lam i *
        (aux_psf_cells d n).sup' (aux_psf_cells_nonempty d n)
          (fun k =>
            (PotentialField.translate (aux_psf_center n z k) h).unitCubeValueNorm +
              (3:ℝ) ^ i * (d:ℝ) *
                (PotentialField.translate (aux_psf_center n z k) h).unitCubeDerivNorm)))) ?_
  intro i
  refine Measurable.ennreal_ofReal (Real.measurable_exp.comp ?_)
  refine Measurable.const_mul ?_ _
  have h : Measurable ((aux_psf_cells d n).sup' (aux_psf_cells_nonempty d n)
      (fun k (h : PotentialField d) =>
        (PotentialField.translate (aux_psf_center n z k) h).unitCubeValueNorm +
          (3:ℝ) ^ i * (d:ℝ) *
            (PotentialField.translate (aux_psf_center n z k) h).unitCubeDerivNorm)) := by
    refine Finset.measurable_sup' _ (fun k _ => ?_)
    exact (PotentialField.unitCubeValueNorm_measurable.comp
        (PotentialField.measurable_translate _)).add
      ((PotentialField.unitCubeDerivNorm_measurable.comp
        (PotentialField.measurable_translate _)).const_mul _)
  convert h using 1
  funext hh
  rw [Finset.sup'_apply]

theorem aux_psf_maxObs_exp_lin (M : GMCModel d) (i n : ℕ) (z : Vec d) (mu : ℝ) :
    (∫⁻ omega, ENNReal.ofReal (Real.exp (mu * aux_psf_maxObs i n z omega))
      ∂M.P.toMeasure) ≤
      ((aux_psf_cells d n).card : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (mu ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2) := by
  have hpt : ∀ omega : PotentialSample d,
      ENNReal.ofReal (Real.exp (mu * aux_psf_maxObs i n z omega)) ≤
      ∑ k ∈ aux_psf_cells d n,
        ENNReal.ofReal (Real.exp
          (mu * aux_psf_cellObs i (aux_psf_center n z k) omega)) := by
    intro omega
    obtain ⟨k0, hk0mem, hk0⟩ := (aux_psf_cells d n).exists_mem_eq_sup'
      (aux_psf_cells_nonempty d n)
      (fun k => aux_psf_cellObs i (aux_psf_center n z k) omega)
    have hrw : aux_psf_maxObs i n z omega =
        aux_psf_cellObs i (aux_psf_center n z k0) omega := by
      unfold aux_psf_maxObs; exact hk0
    rw [hrw]
    exact Finset.single_le_sum
      (f := fun k => ENNReal.ofReal (Real.exp
        (mu * aux_psf_cellObs i (aux_psf_center n z k) omega)))
      (fun k _ => zero_le) hk0mem
  refine le_trans (lintegral_mono hpt) ?_
  rw [lintegral_finset_sum _ (fun k _ =>
    (((aux_psf_cellObs_measurable i (aux_psf_center n z k)).const_mul _).exp).ennreal_ofReal)]
  calc ∑ k ∈ aux_psf_cells d n,
      ∫⁻ omega, ENNReal.ofReal (Real.exp
        (mu * aux_psf_cellObs i (aux_psf_center n z k) omega)) ∂M.P.toMeasure ≤
      ∑ _k ∈ aux_psf_cells d n,
        (ENNReal.ofReal (Real.exp (mu ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2) :=
        Finset.sum_le_sum (fun k _ => aux_psf_cell_exp_lin M i (aux_psf_center n z k) mu)
    _ = ((aux_psf_cells d n).card : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (mu ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]


theorem aux_psf_maxObs_exp_holder (M : GMCModel d) (i n : ℕ) (z : Vec d)
    (theta lam : ℝ) (hlam0 : 0 < lam) (hlt : lam < theta) :
    (∫⁻ omega, ENNReal.ofReal (Real.exp (lam * aux_psf_maxObs i n z omega))
      ∂M.P.toMeasure) ≤
      (((aux_psf_cells d n).card : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (theta ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2))
        ^ (lam / theta) := by
  have hth0 : 0 < theta := lt_trans hlam0 hlt
  set p : ℝ := theta / lam with hp
  have hp1 : 1 < p := by
    rw [hp, lt_div_iff₀ hlam0]; linarith
  have hinv : 1 / p = lam / theta := by
    rw [hp, one_div_div]
  have hmeas : AEMeasurable (fun omega : PotentialSample d =>
      ENNReal.ofReal (Real.exp (theta * aux_psf_maxObs i n z omega)))
      M.P.toMeasure :=
    ((((aux_psf_maxObs_measurable i n z).const_mul _).exp).ennreal_ofReal).aemeasurable
  have hrw : ∀ omega : PotentialSample d,
      ENNReal.ofReal (Real.exp (lam * aux_psf_maxObs i n z omega)) =
      (ENNReal.ofReal (Real.exp (theta * aux_psf_maxObs i n z omega))) ^ (1 / p) := by
    intro omega
    rw [aux_psf_ofReal_exp_rpow, hinv]
    congr 1
    field_simp
  calc (∫⁻ omega, ENNReal.ofReal (Real.exp (lam * aux_psf_maxObs i n z omega))
      ∂M.P.toMeasure) =
      ∫⁻ omega, (ENNReal.ofReal (Real.exp
        (theta * aux_psf_maxObs i n z omega))) ^ (1 / p) ∂M.P.toMeasure := by
        simp only [hrw]
    _ ≤ (∫⁻ omega, ENNReal.ofReal (Real.exp
        (theta * aux_psf_maxObs i n z omega)) ∂M.P.toMeasure) ^ (1 / p) :=
        aux_psf_lintegral_rpow_inv_le M.P.toMeasure hmeas hp1
    _ ≤ (((aux_psf_cells d n).card : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (theta ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2))
        ^ (1 / p) := by
        refine ENNReal.rpow_le_rpow ?_ (by positivity)
        exact aux_psf_maxObs_exp_lin M i n z theta
    _ = (((aux_psf_cells d n).card : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (theta ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2))
        ^ (lam / theta) := by rw [hinv]

theorem aux_psf_geom_tail (a K : ℕ) :
    ∑ i ∈ Finset.Icc a (a + K), ((3:ℝ) ^ i)⁻¹ ≤ (3 / 2) * ((3:ℝ) ^ a)⁻¹ := by
  have hIcc : Finset.Icc a (a + K) = Finset.Ico a (a + K + 1) := by
    rw [← Finset.Ico_succ_right_eq_Icc]
    rfl
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  have hsimp : ∀ t : ℕ, ((3:ℝ) ^ (a + t))⁻¹ = ((3:ℝ) ^ a)⁻¹ * ((1:ℝ)/3) ^ t := by
    intro t
    rw [pow_add, mul_inv, one_div, inv_pow]
  simp only [hsimp]
  rw [← Finset.mul_sum]
  have hgeom : ∑ t ∈ Finset.range (a + K + 1 - a), ((1:ℝ)/3) ^ t ≤ 3 / 2 := by
    rw [geom_sum_eq (by norm_num)]
    have hpow : (0:ℝ) < ((1:ℝ)/3) ^ (a + K + 1 - a) := by positivity
    have heq : (((1:ℝ)/3) ^ (a + K + 1 - a) - 1) / ((1:ℝ)/3 - 1) =
        (3/2) * (1 - ((1:ℝ)/3) ^ (a + K + 1 - a)) := by
      field_simp
      ring
    rw [heq]
    nlinarith
  have hpos : (0:ℝ) ≤ ((3:ℝ) ^ a)⁻¹ := by positivity
  nlinarith

theorem aux_psf_lam_sum (m j K : ℕ) :
    ∑ i ∈ Finset.Icc (m + j) (m + j + K), aux_psf_lam m j i ≤ 9 := by
  unfold aux_psf_lam
  rw [← Finset.mul_sum]
  have h := aux_psf_geom_tail (m + j) K
  have hc : (0:ℝ) < 2 * (3:ℝ) ^ (m + 1 + j) := by positivity
  have hstep : 2 * (3:ℝ) ^ (m + 1 + j) * ∑ i ∈ Finset.Icc (m + j) (m + j + K),
      ((3:ℝ) ^ i)⁻¹ ≤ 2 * (3:ℝ) ^ (m + 1 + j) * ((3 / 2) * ((3:ℝ) ^ (m + j))⁻¹) :=
    mul_le_mul_of_nonneg_left h hc.le
  refine hstep.trans ?_
  have hpow : (3:ℝ) ^ (m + 1 + j) = 3 * (3:ℝ) ^ (m + j) := by
    rw [show m + 1 + j = (m + j) + 1 by omega, pow_succ]
    ring
  rw [hpow]
  have h3 : (0:ℝ) < (3:ℝ) ^ (m + j) := by positivity
  field_simp
  norm_num


theorem aux_psf_lam_pos (m j i : ℕ) : 0 < aux_psf_lam m j i := by
  unfold aux_psf_lam; positivity

theorem aux_psf_lam_le_six (m j i : ℕ) (hi : m + j ≤ i) :
    aux_psf_lam m j i ≤ 6 := by
  unfold aux_psf_lam
  have hmono : ((3:ℝ) ^ i)⁻¹ ≤ ((3:ℝ) ^ (m + j))⁻¹ := by
    have h1 : (0:ℝ) < (3:ℝ) ^ (m + j) := by positivity
    have h2 : (3:ℝ) ^ (m + j) ≤ (3:ℝ) ^ i := pow_le_pow_right₀ (by norm_num) hi
    exact inv_anti₀ h1 h2
  have hpow : (3:ℝ) ^ (m + 1 + j) = 3 * (3:ℝ) ^ (m + j) := by
    rw [show m + 1 + j = (m + j) + 1 by omega, pow_succ]
    ring
  have hc : (0:ℝ) < 2 * (3:ℝ) ^ (m + 1 + j) := by positivity
  have hstep : 2 * (3:ℝ) ^ (m + 1 + j) * ((3:ℝ) ^ i)⁻¹ ≤
      2 * (3:ℝ) ^ (m + 1 + j) * ((3:ℝ) ^ (m + j))⁻¹ :=
    mul_le_mul_of_nonneg_left hmono hc.le
  refine hstep.trans ?_
  rw [hpow]
  have h3 : (0:ℝ) < (3:ℝ) ^ (m + j) := by positivity
  field_simp
  norm_num

theorem aux_psf_lintegral_Bmaj (M : GMCModel d) (m : ℕ) (z : Vec d) (j : ℕ)
    (theta : ℝ) (htheta : 6 < theta) :
    (∫⁻ omega, aux_psf_Bmaj m z j omega ∂M.P.toMeasure) ≤
      (((aux_psf_cells d (m + 1 + j)).card : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (theta ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2))
        ^ (9 / theta) := by
  have hth0 : (0:ℝ) < theta := by linarith
  set C : ℝ≥0∞ := ((aux_psf_cells d (m + 1 + j)).card : ℝ≥0∞) *
    (ENNReal.ofReal (Real.exp (theta ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2) with hC
  have hcard1 : (1 : ℝ≥0∞) ≤ ((aux_psf_cells d (m + 1 + j)).card : ℝ≥0∞) := by
    have : 1 ≤ (aux_psf_cells d (m + 1 + j)).card :=
      Finset.card_pos.2 (aux_psf_cells_nonempty d (m + 1 + j))
    exact_mod_cast this
  have hexp1 : (1 : ℝ≥0∞) ≤
      ENNReal.ofReal (Real.exp (theta ^ 2 * aux_psf_sigma M ^ 2 / 4)) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (by positivity))
  have hC1 : (1 : ℝ≥0∞) ≤ C := by
    rw [hC]
    have h2 : (1 : ℝ≥0∞) ≤
        ENNReal.ofReal (Real.exp (theta ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2 := by
      have := mul_le_mul' hexp1 (by norm_num : (1:ℝ≥0∞) ≤ 2)
      simpa using this
    have := mul_le_mul' hcard1 h2
    simpa using this
  have hC0 : C ≠ 0 := by
    intro h
    rw [h] at hC1
    exact absurd hC1 (by simp)
  have hCt : C ≠ ⊤ := by
    rw [hC]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num))
  set f : ℕ → PotentialSample d → ℝ≥0∞ := fun K omega =>
    ENNReal.ofReal (Real.exp (∑ i ∈ Finset.Icc (m + j) (m + j + K),
      aux_psf_lam m j i * aux_psf_maxObs i (m + 1 + j) z omega)) with hf
  have hfmeas : ∀ K, Measurable (f K) := by
    intro K
    refine Measurable.ennreal_ofReal (Real.measurable_exp.comp ?_)
    exact Finset.measurable_sum _ (fun i _ =>
      (aux_psf_maxObs_measurable i (m + 1 + j) z).const_mul _)
  have hmono : Monotone f := by
    intro K K' hKK' omega
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · refine Finset.Icc_subset_Icc_right ?_
      omega
    · intro i _ _
      have := aux_psf_maxObs_nonneg i (m + 1 + j) z omega
      have := (aux_psf_lam_pos m j i).le
      positivity
  have hBeq : ∀ omega : PotentialSample d,
      aux_psf_Bmaj m z j omega = ⨆ K : ℕ, f K omega := fun omega => rfl
  have hterm : ∀ K : ℕ, (∫⁻ omega, f K omega ∂M.P.toMeasure) ≤ C ^ (9 / theta) := by
    intro K
    have hsplit : ∀ omega : PotentialSample d, f K omega =
        ∏ i ∈ Finset.Icc (m + j) (m + j + K),
          ENNReal.ofReal (Real.exp
            (aux_psf_lam m j i * aux_psf_maxObs i (m + 1 + j) z omega)) := by
      intro omega
      rw [hf, aux_psf_prod_ofReal_exp]
    simp only [hsplit]
    rw [ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun
      _ _ (aux_psf_indep_maxObs M (m + 1 + j) z (aux_psf_lam m j))
      (fun i => (((aux_psf_maxObs_measurable i (m + 1 + j) z).const_mul _).exp).ennreal_ofReal)]
    calc ∏ i ∈ Finset.Icc (m + j) (m + j + K),
        ∫⁻ omega, ENNReal.ofReal (Real.exp
          (aux_psf_lam m j i * aux_psf_maxObs i (m + 1 + j) z omega))
          ∂M.P.toMeasure ≤
        ∏ i ∈ Finset.Icc (m + j) (m + j + K), C ^ (aux_psf_lam m j i / theta) := by
          refine Finset.prod_le_prod' (fun i hi => ?_)
          have hi' : m + j ≤ i := (Finset.mem_Icc.1 hi).1
          exact aux_psf_maxObs_exp_holder M i (m + 1 + j) z theta
            (aux_psf_lam m j i) (aux_psf_lam_pos m j i)
            (lt_of_le_of_lt (aux_psf_lam_le_six m j i hi') htheta)
      _ = C ^ (∑ i ∈ Finset.Icc (m + j) (m + j + K), aux_psf_lam m j i / theta) :=
          aux_psf_prod_rpow C hC0 hCt _ _
      _ ≤ C ^ (9 / theta) := by
          refine ENNReal.rpow_le_rpow_of_exponent_le hC1 ?_
          rw [← Finset.sum_div]
          gcongr
          exact aux_psf_lam_sum m j K
  calc (∫⁻ omega, aux_psf_Bmaj m z j omega ∂M.P.toMeasure) =
      ∫⁻ omega, ⨆ K : ℕ, f K omega ∂M.P.toMeasure := by simp only [hBeq]
    _ = ⨆ K : ℕ, ∫⁻ omega, f K omega ∂M.P.toMeasure := lintegral_iSup hfmeas hmono
    _ ≤ C ^ (9 / theta) := iSup_le hterm


theorem aux_psf_lintegral_Amaj' (M : GMCModel d) (m : ℕ) (z : Vec d) (j : ℕ)
    (q : ℝ) (hq : 1 < q) :
    (∫⁻ omega, aux_psf_Amaj m z j omega ∂M.P.toMeasure) ≤
      ENNReal.ofReal (((((aux_psf_cells d (m + 1 + j)).card : ℝ)) *
        (2 * Real.exp (q ^ 2 * aux_psf_sigma M ^ 2 / 4)) ^
          ((Finset.Icc (m - j) (m + j)).card)) ^ (1 / q)) := by
  refine (aux_psf_lintegral_Amaj M m z j q hq).trans ?_
  have hK : (0:ℝ) < 2 * Real.exp (q ^ 2 * aux_psf_sigma M ^ 2 / 4) := by positivity
  have hbase : (0:ℝ) < ((aux_psf_cells d (m + 1 + j)).card : ℝ) *
      (2 * Real.exp (q ^ 2 * aux_psf_sigma M ^ 2 / 4)) ^
        ((Finset.Icc (m - j) (m + j)).card) := by
    have : 0 < (aux_psf_cells d (m + 1 + j)).card :=
      Finset.card_pos.2 (aux_psf_cells_nonempty d (m + 1 + j))
    have hc : (0:ℝ) < ((aux_psf_cells d (m + 1 + j)).card : ℝ) := by exact_mod_cast this
    positivity
  rw [← ENNReal.ofReal_rpow_of_pos hbase]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow hK.le]
  gcongr
  rw [ENNReal.ofReal_mul (by norm_num)]
  rw [mul_comm]
  norm_num

theorem aux_psf_lintegral_Bmaj' (M : GMCModel d) (m : ℕ) (z : Vec d) (j : ℕ)
    (theta : ℝ) (htheta : 6 < theta) :
    (∫⁻ omega, aux_psf_Bmaj m z j omega ∂M.P.toMeasure) ≤
      ENNReal.ofReal (((((aux_psf_cells d (m + 1 + j)).card : ℝ)) *
        (2 * Real.exp (theta ^ 2 * aux_psf_sigma M ^ 2 / 4))) ^ (9 / theta)) := by
  refine (aux_psf_lintegral_Bmaj M m z j theta htheta).trans ?_
  have hK : (0:ℝ) < 2 * Real.exp (theta ^ 2 * aux_psf_sigma M ^ 2 / 4) := by
    positivity
  have hbase : (0:ℝ) < ((aux_psf_cells d (m + 1 + j)).card : ℝ) *
      (2 * Real.exp (theta ^ 2 * aux_psf_sigma M ^ 2 / 4)) := by
    have : 0 < (aux_psf_cells d (m + 1 + j)).card :=
      Finset.card_pos.2 (aux_psf_cells_nonempty d (m + 1 + j))
    have hc : (0:ℝ) < ((aux_psf_cells d (m + 1 + j)).card : ℝ) := by exact_mod_cast this
    positivity
  have hth0 : (0:ℝ) < theta := by linarith
  rw [← ENNReal.ofReal_rpow_of_pos hbase]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_mul (by norm_num), mul_comm (ENNReal.ofReal 2)]
  norm_num


theorem aux_psf_rpow_geom (X Y c : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) (j : ℕ) :
    (X * Y ^ j) ^ c = X ^ c * (Y ^ c) ^ j := by
  rw [Real.mul_rpow hX (pow_nonneg hY j)]
  congr 1
  rw [← Real.rpow_natCast Y j, ← Real.rpow_mul hY,
    ← Real.rpow_natCast (Y ^ c) j, ← Real.rpow_mul hY]
  congr 1
  ring

theorem aux_psf_card_le (m j : ℕ) :
    (((aux_psf_cells d (m + 1 + j)).card : ℝ)) ≤
      (3:ℝ) ^ ((d * (m + 2) + 1) + d * j) := by
  rw [aux_psf_cells_card]
  have hnat := aux_psf_nat_cover_bound d m j
  have h1 : (2 * 3 ^ (m + 1 + j) + 1) ^ d ≤ 3 ^ (d * (m + 2 + j) + 1) := by
    omega
  have h2 : d * (m + 2 + j) + 1 = (d * (m + 2) + 1) + d * j := by ring
  rw [h2] at h1
  exact_mod_cast (Nat.cast_le (α := ℝ)).2 h1


/-- The expectation bound for one product-score term. -/
def aux_psf_Pbound (M : GMCModel d) (s q theta : ℝ) (m j : ℕ) : ℝ :=
  (3:ℝ) ^ (-(s * (j:ℝ) / 8)) *
    ((((aux_psf_cells d (m + 1 + j)).card : ℝ) *
        (2 * Real.exp (q ^ 2 * aux_psf_sigma M ^ 2 / 4)) ^
          ((Finset.Icc (m - j) (m + j)).card)) ^ (1 / q) +
      (((aux_psf_cells d (m + 1 + j)).card : ℝ) *
        (2 * Real.exp (theta ^ 2 * aux_psf_sigma M ^ 2 / 4))) ^ (9 / theta))

theorem aux_psf_Pbound_nonneg (M : GMCModel d) (s q theta : ℝ) (m j : ℕ) :
    0 ≤ aux_psf_Pbound M s q theta m j := by
  unfold aux_psf_Pbound
  have h1 : (0:ℝ) ≤ (3:ℝ) ^ (-(s * (j:ℝ) / 8)) := Real.rpow_nonneg (by norm_num) _
  have h2 : (0:ℝ) ≤ (((aux_psf_cells d (m + 1 + j)).card : ℝ) *
      (2 * Real.exp (q ^ 2 * aux_psf_sigma M ^ 2 / 4)) ^
        ((Finset.Icc (m - j) (m + j)).card)) ^ (1 / q) :=
    Real.rpow_nonneg (by positivity) _
  have h3 : (0:ℝ) ≤ (((aux_psf_cells d (m + 1 + j)).card : ℝ) *
      (2 * Real.exp (theta ^ 2 * aux_psf_sigma M ^ 2 / 4))) ^ (9 / theta) :=
    Real.rpow_nonneg (by positivity) _
  nlinarith

theorem aux_psf_summable_Pbound (M : GMCModel d) (s q theta : ℝ)
    (_hs0 : 0 < s) (hq1 : 1 < q) (hth6 : 6 < theta) (m : ℕ)
    (hA : (3:ℝ) ^ (-(s / 8)) *
        (((3:ℝ) ^ d * (2 * Real.exp (q ^ 2 * aux_psf_sigma M ^ 2 / 4)) ^ 2) ^
          (1 / q)) < 1)
    (hB : (3:ℝ) ^ (-(s / 8)) * (((3:ℝ) ^ d) ^ (9 / theta)) < 1) :
    Summable (fun j : ℕ => aux_psf_Pbound M s q theta m j) := by
  have hq0 : (0:ℝ) < q := by linarith
  have hth0 : (0:ℝ) < theta := by linarith
  set KA : ℝ := 2 * Real.exp (q ^ 2 * aux_psf_sigma M ^ 2 / 4) with hKA
  set KB : ℝ := 2 * Real.exp (theta ^ 2 * aux_psf_sigma M ^ 2 / 4) with hKB
  have hKA1 : (1:ℝ) ≤ KA := by
    rw [hKA]
    nlinarith [Real.one_le_exp (by positivity : (0:ℝ) ≤ q ^ 2 * aux_psf_sigma M ^ 2 / 4)]
  have hKB1 : (1:ℝ) ≤ KB := by
    rw [hKB]
    nlinarith [Real.one_le_exp
      (by positivity : (0:ℝ) ≤ theta ^ 2 * aux_psf_sigma M ^ 2 / 4)]
  have hKA0 : (0:ℝ) < KA := by linarith
  have hKB0 : (0:ℝ) < KB := by linarith
  set A0 : ℝ := ((3:ℝ) ^ (d * (m + 2) + 1) * KA) ^ (1 / q) with hA0def
  set B0 : ℝ := ((3:ℝ) ^ (d * (m + 2) + 1) * KB) ^ (9 / theta) with hB0def
  set rA : ℝ := (3:ℝ) ^ (-(s / 8)) * (((3:ℝ) ^ d * KA ^ 2) ^ (1 / q)) with hrAdef
  set rB : ℝ := (3:ℝ) ^ (-(s / 8)) * (((3:ℝ) ^ d) ^ (9 / theta)) with hrBdef
  have hA00 : 0 ≤ A0 := Real.rpow_nonneg (by positivity) _
  have hB00 : 0 ≤ B0 := Real.rpow_nonneg (by positivity) _
  have hrA0 : 0 ≤ rA := by
    rw [hrAdef]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (by positivity) _)
  have hrB0 : 0 ≤ rB := by
    rw [hrBdef]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (by positivity) _)
  have hmaj : Summable (fun j : ℕ => A0 * rA ^ j + B0 * rB ^ j) := by
    refine Summable.add ?_ ?_
    · exact (summable_geometric_of_lt_one hrA0 hA).mul_left A0
    · exact (summable_geometric_of_lt_one hrB0 hB).mul_left B0
  refine Summable.of_nonneg_of_le (fun j => aux_psf_Pbound_nonneg M s q theta m j)
    (fun j => ?_) hmaj
  have hcj : (3:ℝ) ^ (-(s * (j:ℝ) / 8)) = ((3:ℝ) ^ (-(s / 8))) ^ j := by
    rw [← Real.rpow_natCast ((3:ℝ) ^ (-(s / 8))) j,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
    congr 1
    ring
  have hcard := aux_psf_card_le (d := d) m j
  have hpow3 : (3:ℝ) ^ ((d * (m + 2) + 1) + d * j) =
      (3:ℝ) ^ (d * (m + 2) + 1) * ((3:ℝ) ^ d) ^ j := by
    rw [pow_add, pow_mul]
  have hT1 : (((aux_psf_cells d (m + 1 + j)).card : ℝ) *
      KA ^ ((Finset.Icc (m - j) (m + j)).card)) ^ (1 / q) ≤ A0 * (((3:ℝ) ^ d * KA ^ 2) ^ (1 / q)) ^ j := by
    have hcardI : (Finset.Icc (m - j) (m + j)).card ≤ 2 * j + 1 := by
      rw [Nat.card_Icc]; omega
    have hKApow : KA ^ ((Finset.Icc (m - j) (m + j)).card) ≤ KA ^ (2 * j + 1) :=
      pow_le_pow_right₀ hKA1 hcardI
    have hbase : ((aux_psf_cells d (m + 1 + j)).card : ℝ) *
        KA ^ ((Finset.Icc (m - j) (m + j)).card) ≤
        ((3:ℝ) ^ (d * (m + 2) + 1) * KA) * ((3:ℝ) ^ d * KA ^ 2) ^ j := by
      have hstep : ((aux_psf_cells d (m + 1 + j)).card : ℝ) *
          KA ^ ((Finset.Icc (m - j) (m + j)).card) ≤
          (3:ℝ) ^ ((d * (m + 2) + 1) + d * j) * KA ^ (2 * j + 1) := by
        have h1 : (0:ℝ) ≤ KA ^ ((Finset.Icc (m - j) (m + j)).card) := by positivity
        have h2 : (0:ℝ) ≤ (3:ℝ) ^ ((d * (m + 2) + 1) + d * j) := by positivity
        exact mul_le_mul hcard hKApow h1 h2
      refine hstep.trans (le_of_eq ?_)
      have hKAsplit : KA ^ (2 * j + 1) = (KA ^ 2) ^ j * KA := by
        rw [pow_succ, pow_mul]
      rw [hpow3, hKAsplit, mul_pow]
      ring
    calc (((aux_psf_cells d (m + 1 + j)).card : ℝ) *
        KA ^ ((Finset.Icc (m - j) (m + j)).card)) ^ (1 / q) ≤
        (((3:ℝ) ^ (d * (m + 2) + 1) * KA) * ((3:ℝ) ^ d * KA ^ 2) ^ j) ^ (1 / q) :=
          Real.rpow_le_rpow (by positivity) hbase (by positivity)
      _ = A0 * (((3:ℝ) ^ d * KA ^ 2) ^ (1 / q)) ^ j := by
          rw [hA0def]
          exact aux_psf_rpow_geom _ _ _ (by positivity) (by positivity) j
  have hT2 : (((aux_psf_cells d (m + 1 + j)).card : ℝ) * KB) ^ (9 / theta) ≤
      B0 * ((((3:ℝ) ^ d) ^ (9 / theta))) ^ j := by
    have hbase : ((aux_psf_cells d (m + 1 + j)).card : ℝ) * KB ≤
        ((3:ℝ) ^ (d * (m + 2) + 1) * KB) * ((3:ℝ) ^ d) ^ j := by
      have hstep : ((aux_psf_cells d (m + 1 + j)).card : ℝ) * KB ≤
          (3:ℝ) ^ ((d * (m + 2) + 1) + d * j) * KB :=
        mul_le_mul_of_nonneg_right hcard hKB0.le
      refine hstep.trans (le_of_eq ?_)
      rw [hpow3]
      ring
    calc (((aux_psf_cells d (m + 1 + j)).card : ℝ) * KB) ^ (9 / theta) ≤
        (((3:ℝ) ^ (d * (m + 2) + 1) * KB) * ((3:ℝ) ^ d) ^ j) ^ (9 / theta) :=
          Real.rpow_le_rpow (by positivity) hbase (by positivity)
      _ = B0 * ((((3:ℝ) ^ d) ^ (9 / theta))) ^ j := by
          rw [hB0def]
          exact aux_psf_rpow_geom _ _ _ (by positivity) (by positivity) j
  unfold aux_psf_Pbound
  rw [hcj, ← hKA, ← hKB]
  have hcpos : (0:ℝ) ≤ ((3:ℝ) ^ (-(s / 8))) ^ j := by positivity
  have hstep := mul_le_mul_of_nonneg_left (add_le_add hT1 hT2) hcpos
  refine le_trans hstep (le_of_eq ?_)
  rw [hrAdef, hrBdef]
  ring


theorem aux_psf_Bmaj_measurable (m : ℕ) (z : Vec d) (j : ℕ) :
    Measurable (fun omega : PotentialSample d => aux_psf_Bmaj m z j omega) := by
  unfold aux_psf_Bmaj
  refine Measurable.iSup (fun K => ?_)
  refine Measurable.ennreal_ofReal (Real.measurable_exp.comp ?_)
  exact Finset.measurable_sum _ (fun i _ =>
    (aux_psf_maxObs_measurable i (m + 1 + j) z).const_mul _)

/-- The measurable majorant of the `j`-th product-score term. -/
def aux_psf_Pmaj (s : ℝ) (m : ℕ) (z : Vec d) (j : ℕ)
    (omega : PotentialSample d) : ℝ≥0∞ :=
  ENNReal.ofReal ((3:ℝ) ^ (-(s * (j:ℝ) / 8))) *
    (aux_psf_Amaj m z j omega + aux_psf_Bmaj m z j omega)

theorem aux_psf_Pmaj_measurable (s : ℝ) (m : ℕ) (z : Vec d) (j : ℕ) :
    Measurable (fun omega : PotentialSample d => aux_psf_Pmaj s m z j omega) := by
  unfold aux_psf_Pmaj
  exact (show Measurable (fun omega ↦ aux_psf_Amaj m z j omega + aux_psf_Bmaj m z j omega) from
    (aux_psf_Amaj_measurable m z j).add (aux_psf_Bmaj_measurable m z j)).const_mul _

theorem aux_psf_lintegral_Pmaj (M : GMCModel d) (s : ℝ) (m : ℕ) (z : Vec d)
    (j : ℕ) (q theta : ℝ) (hq : 1 < q) (hth : 6 < theta) :
    (∫⁻ omega, aux_psf_Pmaj s m z j omega ∂M.P.toMeasure) ≤
      ENNReal.ofReal (aux_psf_Pbound M s q theta m j) := by
  have hc0 : (0:ℝ) ≤ (3:ℝ) ^ (-(s * (j:ℝ) / 8)) := Real.rpow_nonneg (by norm_num) _
  have hA := aux_psf_lintegral_Amaj' M m z j q hq
  have hB := aux_psf_lintegral_Bmaj' M m z j theta hth
  have hAB : (0:ℝ) ≤ ((((aux_psf_cells d (m + 1 + j)).card : ℝ)) *
      (2 * Real.exp (q ^ 2 * aux_psf_sigma M ^ 2 / 4)) ^
        ((Finset.Icc (m - j) (m + j)).card)) ^ (1 / q) :=
    Real.rpow_nonneg (by positivity) _
  unfold aux_psf_Pmaj aux_psf_Pbound
  rw [lintegral_const_mul (f := fun omega ↦ aux_psf_Amaj m z j omega + aux_psf_Bmaj m z j omega)
    _ (by simpa only using! (aux_psf_Amaj_measurable m z j).add (aux_psf_Bmaj_measurable m z j)),
    lintegral_add_left (aux_psf_Amaj_measurable m z j)]
  calc ENNReal.ofReal ((3:ℝ) ^ (-(s * (j:ℝ) / 8))) *
      ((∫⁻ omega, aux_psf_Amaj m z j omega ∂M.P.toMeasure) +
        ∫⁻ omega, aux_psf_Bmaj m z j omega ∂M.P.toMeasure) ≤
      ENNReal.ofReal ((3:ℝ) ^ (-(s * (j:ℝ) / 8))) *
        (ENNReal.ofReal (((((aux_psf_cells d (m + 1 + j)).card : ℝ)) *
            (2 * Real.exp (q ^ 2 * aux_psf_sigma M ^ 2 / 4)) ^
              ((Finset.Icc (m - j) (m + j)).card)) ^ (1 / q)) +
          ENNReal.ofReal (((((aux_psf_cells d (m + 1 + j)).card : ℝ)) *
            (2 * Real.exp (theta ^ 2 * aux_psf_sigma M ^ 2 / 4))) ^ (9 / theta))) := by
        gcongr
    _ = ENNReal.ofReal ((3:ℝ) ^ (-(s * (j:ℝ) / 8)) *
        (((((aux_psf_cells d (m + 1 + j)).card : ℝ)) *
            (2 * Real.exp (q ^ 2 * aux_psf_sigma M ^ 2 / 4)) ^
              ((Finset.Icc (m - j) (m + j)).card)) ^ (1 / q) +
          ((((aux_psf_cells d (m + 1 + j)).card : ℝ)) *
            (2 * Real.exp (theta ^ 2 * aux_psf_sigma M ^ 2 / 4))) ^ (9 / theta))) := by
        rw [← ENNReal.ofReal_add hAB (Real.rpow_nonneg (by positivity) _),
          ← ENNReal.ofReal_mul hc0]

theorem aux_psf_Pmaj_tsum_ae (M : GMCModel d) (s : ℝ) (m : ℕ) (z : Vec d)
    (q theta : ℝ) (hs0 : 0 < s) (hq : 1 < q) (hth : 6 < theta)
    (hA : (3:ℝ) ^ (-(s / 8)) *
        (((3:ℝ) ^ d * (2 * Real.exp (q ^ 2 * aux_psf_sigma M ^ 2 / 4)) ^ 2) ^
          (1 / q)) < 1)
    (hB : (3:ℝ) ^ (-(s / 8)) * (((3:ℝ) ^ d) ^ (9 / theta)) < 1) :
    ∀ᵐ omega ∂M.P.toMeasure, (∑' j : ℕ, aux_psf_Pmaj s m z j omega) ≠ ⊤ := by
  have hmeas : ∀ j : ℕ, AEMeasurable (fun omega : PotentialSample d =>
      aux_psf_Pmaj s m z j omega) M.P.toMeasure :=
    fun j => (aux_psf_Pmaj_measurable s m z j).aemeasurable
  have hint : (∫⁻ omega, (∑' j : ℕ, aux_psf_Pmaj s m z j omega)
      ∂M.P.toMeasure) ≠ ⊤ := by
    rw [lintegral_tsum hmeas]
    refine ne_top_of_le_ne_top ?_
      (ENNReal.tsum_le_tsum (fun j =>
        aux_psf_lintegral_Pmaj M s m z j q theta hq hth))
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun j => aux_psf_Pbound_nonneg M s q theta m j)
      (aux_psf_summable_Pbound M s q theta hs0 hq hth m hA hB)]
    exact ENNReal.ofReal_ne_top
  have hlt := ae_lt_top' (AEMeasurable.ennreal_tsum hmeas) hint
  filter_upwards [hlt] with omega h
  exact h.ne


theorem aux_psf_Psc_ne_top (hd : (1:ℝ) ≤ (d : ℝ)) (s : ℝ) (m : ℕ) (z : Vec d)
    (omega : PotentialSample d)
    (hfin : (∑' j : ℕ, aux_psf_Pmaj s m z j omega) ≠ ⊤) :
    sSup {v : ℝ≥0∞ | ∃ j : ℕ, v = ENNReal.ofReal ((3:ℝ) ^ (-(s * (j:ℝ) / 8))) *
      sSup {w : ℝ≥0∞ | ∃ x ∈ translatedCube d ((m:ℤ) + 1 + (j:ℤ)) z,
        w = (∏ i ∈ Finset.Icc (m - j) (m + j),
              ENNReal.ofReal (Real.exp |omega i x|)) +
            sSup {u : ℝ≥0∞ | ∃ K : ℕ, u = ∏ i ∈ Finset.Icc (m + j) (m + j + K),
              ENNReal.ofReal (Real.exp (4 * |omega i x - omega i z|))}}} ≠ ⊤ := by
  refine ne_top_of_le_ne_top hfin (sSup_le ?_)
  rintro v ⟨j, rfl⟩
  refine le_trans ?_ (ENNReal.le_tsum j)
  unfold aux_psf_Pmaj
  gcongr
  exact aux_psf_Pterm_le hd m z j omega

theorem aux_psf_hA_of (M : GMCModel d) (s q : ℝ) (hq0 : 0 < q)
    (hlog : (d : ℝ) * Real.log 3 +
        2 * (Real.log 2 + q ^ 2 * aux_psf_sigma M ^ 2 / 4)
      < (s * q / 8) * Real.log 3) :
    (3:ℝ) ^ (-(s / 8)) *
      (((3:ℝ) ^ d * (2 * Real.exp (q ^ 2 * aux_psf_sigma M ^ 2 / 4)) ^ 2) ^
        (1 / q)) < 1 := by
  set A : ℝ := q ^ 2 * aux_psf_sigma M ^ 2 / 4 with hAdef
  set KA : ℝ := 2 * Real.exp A with hKAdef
  have hKA0 : (0:ℝ) < KA := by rw [hKAdef]; positivity
  have hbase0 : (0:ℝ) < (3:ℝ) ^ d * KA ^ 2 := by positivity
  have hlogKA : Real.log KA = Real.log 2 + A := by
    rw [hKAdef, Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
  have hlogbase : Real.log ((3:ℝ) ^ d * KA ^ 2) =
      (d:ℝ) * Real.log 3 + 2 * Real.log KA := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    norm_num
  have h1 : ((3:ℝ) ^ d * KA ^ 2) ^ (1 / q) =
      Real.exp (Real.log ((3:ℝ) ^ d * KA ^ 2) * (1 / q)) :=
    Real.rpow_def_of_pos hbase0 _
  have h2 : (3:ℝ) ^ (-(s / 8)) = Real.exp (Real.log 3 * (-(s / 8))) :=
    Real.rpow_def_of_pos (by norm_num) _
  rw [h1, h2, ← Real.exp_add, Real.exp_lt_one_iff, hlogbase, hlogKA]
  have hkey : ((d:ℝ) * Real.log 3 + 2 * (Real.log 2 + A)) * (1 / q) <
      (s / 8) * Real.log 3 := by
    rw [mul_one_div, div_lt_iff₀ hq0]
    nlinarith [hlog]
  linarith

theorem aux_psf_hB_of (s theta : ℝ) (_hth0 : 0 < theta)
    (hlt : (d:ℝ) * (9 / theta) < s / 8) :
    (3:ℝ) ^ (-(s / 8)) * (((3:ℝ) ^ d) ^ (9 / theta)) < 1 := by
  have h1 : (((3:ℝ) ^ d) ^ (9 / theta)) =
      Real.exp (Real.log ((3:ℝ) ^ d) * (9 / theta)) :=
    Real.rpow_def_of_pos (by positivity) _
  have h2 : (3:ℝ) ^ (-(s / 8)) = Real.exp (Real.log 3 * (-(s / 8))) :=
    Real.rpow_def_of_pos (by norm_num) _
  rw [h1, h2, ← Real.exp_add, Real.exp_lt_one_iff, Real.log_pow]
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  nlinarith [hlt, hlog3]


theorem aux_psf_Dsc_ne_top (M : GMCModel d) (s : ℝ) (hs0 : 0 < s) (k : ℕ)
    (z : Vec d) (omega : PotentialSample d)
    (hfin : (∑' j : ℕ, aux_psf_Dmaj4 k z j omega) ≠ ⊤) :
    (sSup {v : ℝ≥0∞ | ∃ j l : ℕ, j ≤ k ∧ l ≤ k ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
          OnTriadicGrid l (x - z) ∧ x - z ∈ cube d (j:ℤ) \ cube d ((j:ℤ) - 1) ∧
          v = ENNReal.ofReal ((3:ℝ) ^ (-(s / 2) * ((k:ℝ) - (l:ℝ)))) *
            (min (aux_psf_Jval M l omega x) 1) ^ (1/2 : ℝ)} +
        sSup {v : ℝ≥0∞ | ∃ j : ℕ, j ≤ k ∧
          v = ENNReal.ofReal ((3:ℝ) ^ (-(s / 8) * ((k:ℝ) - (j:ℝ)))) *
            sSup {w : ℝ≥0∞ | ∃ x ∈ translatedCube d (k:ℤ) z,
              w = ENNReal.ofReal |shellBlock k j omega x|}} +
        ENNReal.ofReal ((3:ℝ) ^ (-(s / 8) * (k:ℝ))) *
          sSup {w : ℝ≥0∞ | ∃ x ∈ translatedCube d (k:ℤ) z,
            w = ENNReal.ofReal |omega 0 x|} +
        ∑' j : ℕ, if k ≤ j then
          ENNReal.ofReal ((3:ℝ) ^ k) *
            sSup {w : ℝ≥0∞ | ∃ x ∈ translatedCube d (k:ℤ) z,
              w = ENNReal.ofReal
                |Homogenization.euclideanNorm (shellGradient (omega j) x)|}
        else 0) ≠ ⊤ := by
  refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact ne_top_of_le_ne_top ENNReal.one_ne_top
      (aux_psf_Dterm1_le_one M s hs0 k z omega)
  · exact ne_top_of_le_ne_top (aux_psf_Dmaj2_ne_top s k z omega)
      (aux_psf_Dterm2_le s k z omega)
  · exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (aux_psf_Dterm3_le s k z omega)
  · exact ne_top_of_le_ne_top hfin (aux_psf_Dterm4_le k z omega)




theorem primitive_scores_finite
    (d : Nat) [NeZero d] (s : Real) (hs0 : 0 < s) (hs1 : s <= 1) :
    ∃ delta0 : Real, 0 < delta0 ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta <= delta0 →
        ∀ eps : Real, 0 < eps → eps < 1 →
          ∀ Fsc Psc Rsc Dsc :
              Nat → Vec d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ENNReal,
            ∀ Zsc :
                Nat → Vec d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → Real,
              ∀ goodEvt :
                  Nat → Vec d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → Prop,
                (∀ omega, Paper.primitive_scores d M s eps omega
                    (fun m z => Fsc m z omega)
                    (fun m z => Psc m z omega)
                    (fun m z => Rsc m z omega)
                    (fun m z => Dsc m z omega)
                    (fun m z => Zsc m z omega)
                    (fun m z => goodEvt m z omega)) →
                  ∀ (m : Nat) (z : Vec d), ∀ᵐ omega ∂M.P.toMeasure,
                    Fsc m z omega ≠ ⊤ ∧
                      Psc m z omega ≠ ⊤ ∧
                        Rsc m z omega ≠ ⊤ ∧ Dsc m z omega ≠ ⊤
  := by
  classical
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by
    have h : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
    exact_mod_cast h
  have hlog3 : (1:ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  refine ⟨s / ((1 + (d:ℝ)) * (1 + 288 * ((d:ℝ) + 2))), by positivity, ?_⟩
  intro M hdelta eps heps0 heps1 Fsc Psc Rsc Dsc Zsc goodEvt hps m z
  set q : ℝ := 24 * ((d:ℝ) + 2) / s with hqdef
  set theta : ℝ := 7 + 72 * ((d:ℝ) + 1) / s with hthdef
  have hq1 : 1 < q := by
    rw [hqdef, lt_div_iff₀ hs0]
    nlinarith
  have hq0 : (0:ℝ) < q := by linarith
  have hth6 : (6:ℝ) < theta := by
    have hpos : (0:ℝ) < 72 * ((d:ℝ) + 1) / s := by positivity
    rw [hthdef]
    linarith
  have hth0 : (0:ℝ) < theta := by linarith
  have hsig : aux_psf_sigma M ≤ s / (1 + 288 * ((d:ℝ) + 2)) := by
    have hdpos : (0:ℝ) < 1 + (d:ℝ) := by linarith
    have hden : (0:ℝ) < 1 + 288 * ((d:ℝ) + 2) := by positivity
    unfold aux_psf_sigma
    calc (1 + (d:ℝ)) * M.delta ≤
        (1 + (d:ℝ)) * (s / ((1 + (d:ℝ)) * (1 + 288 * ((d:ℝ) + 2)))) :=
        mul_le_mul_of_nonneg_left hdelta hdpos.le
      _ = s / (1 + 288 * ((d:ℝ) + 2)) := by field_simp
  have hqsig : q * aux_psf_sigma M ≤ 1 / 12 := by
    have hden : (0:ℝ) < 1 + 288 * ((d:ℝ) + 2) := by positivity
    calc q * aux_psf_sigma M ≤ q * (s / (1 + 288 * ((d:ℝ) + 2))) :=
        mul_le_mul_of_nonneg_left hsig hq0.le
      _ = 24 * ((d:ℝ) + 2) / (1 + 288 * ((d:ℝ) + 2)) := by
          rw [hqdef]; field_simp
      _ ≤ 1 / 12 := by
          rw [div_le_div_iff₀ hden (by norm_num)]
          nlinarith
  have hA : (3:ℝ) ^ (-(s / 8)) *
      (((3:ℝ) ^ d * (2 * Real.exp (q ^ 2 * aux_psf_sigma M ^ 2 / 4)) ^ 2) ^
        (1 / q)) < 1 := by
    refine aux_psf_hA_of M s q hq0 ?_
    have hsigp : (0:ℝ) < aux_psf_sigma M := aux_psf_sigma_pos M
    have hsq : q ^ 2 * aux_psf_sigma M ^ 2 ≤ 1 / 144 := by
      have h1 : (q * aux_psf_sigma M) ^ 2 ≤ (1 / 12 : ℝ) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity) hqsig
      nlinarith
    have hsq' : s * q / 8 = 3 * ((d:ℝ) + 2) := by
      rw [hqdef]; field_simp; ring
    rw [hsq']
    have hdlog : (1:ℝ) ≤ (d:ℝ) * Real.log 3 := by nlinarith
    nlinarith
  have hB : (3:ℝ) ^ (-(s / 8)) * (((3:ℝ) ^ d) ^ (9 / theta)) < 1 := by
    refine aux_psf_hB_of s theta hth0 ?_
    have h1 : (d:ℝ) * (9 / theta) = 9 * (d:ℝ) / theta := by ring
    have hexp : s * theta = 7 * s + 72 * ((d:ℝ) + 1) := by
      rw [hthdef]; field_simp
    rw [h1, div_lt_div_iff₀ hth0 (by norm_num : (0:ℝ) < 8)]
    nlinarith
  have hFae := aux_psf_Fmaj_tsum_ae M s hs0 m z
  have hPae := aux_psf_Pmaj_tsum_ae M s m z q theta hs0 hq1 hth6 hA hB
  have hDae := aux_psf_Dmaj4_tsum_ae M m z
  filter_upwards [hFae, hPae, hDae] with omega hFf hPf hDf
  have h := hps omega
  rw [Paper.primitive_scores] at h
  obtain ⟨-, -, -, -, hF, hP, hR, hD, -, -, -⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hF m z]
    exact aux_psf_Fsc_ne_top s m z omega hFf
  · rw [hP m z]
    exact aux_psf_Psc_ne_top hd1 s m z omega hPf
  · rw [hR m z]
    exact aux_psf_Rsc_ne_top M s m z omega
  · rw [hD m z]
    exact aux_psf_Dsc_ne_top M s hs0 m z omega hDf

open Homogenization hiding Vec
open SubdiffusiveProcess
open scoped BigOperators

/-- Rescale an actual physical observation cube by its shell scale. -/
theorem aux_prefix_bank_rescaled_cube {d : ℕ} (i n : ℕ) (hin : i ≤ n)
    (z x : Vec d) (hx : x ∈ translatedCube d (n : ℤ) z) :
    ((3 : ℝ) ^ (-(i : ℤ))) • x ∈
      translatedCube d ((n - i : ℕ) : ℤ)
        (((3 : ℝ) ^ (-(i : ℤ))) • z) := by
  rw [aux_psf_mem_translatedCube_iff] at hx ⊢
  intro k
  have h := hx k
  simp only [Pi.smul_apply, smul_eq_mul]
  have h3 : 0 < (3 : ℝ) ^ (-(i : ℤ)) := zpow_pos (by norm_num) _
  have hscale : (3 : ℝ) ^ (-(i : ℤ)) * ((3 : ℝ) ^ (n : ℤ) / 2) =
      (3 : ℝ) ^ (((n - i : ℕ) : ℤ)) / 2 := by
    rw [← mul_div_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    rw [Int.natCast_sub hin]
    ring
  rw [← mul_sub, abs_mul, abs_of_pos h3]
  calc
    (3 : ℝ) ^ (-(i : ℤ)) * |x k - z k| <
        (3 : ℝ) ^ (-(i : ℤ)) * ((3 : ℝ) ^ (n : ℤ) / 2) :=
      mul_lt_mul_of_pos_left h h3
    _ = _ := hscale

/-- The shell value and scaled gradient at a physical point are controlled
by the zero-layer observable of its scaled cell. -/
theorem aux_prefix_bank_scaled_cell_bound {d : ℕ} (i : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (y u : Vec d)
    (hu : u ∈ cube d 0) :
    let r : ℝ := (3 : ℝ) ^ i
    let v : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d :=
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale r
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate (r • y) (omega i))
    |omega i (r • (u + y))| + r *
      Homogenization.euclideanNorm (shellGradient (omega i) (r • (u + y))) ≤
      aux_psf_cellObs 0 (0 : Vec d) (fun _ => v) := by
  dsimp
  set r : ℝ := (3 : ℝ) ^ i with hr
  set x : Vec d := r • (u + y) with hx
  set v : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d :=
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale r
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate (r • y) (omega i)) with hv
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hval : v u = omega i x := by
    rw [hv, SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale_apply,
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate_apply, ← smul_add]
  have hder : SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv v u =
      r • SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv (omega i) x := by
    rw [hv, aux_psf_deriv_spatialScale, aux_psf_deriv_translate]
    rw [← smul_add]
  have hgrad : shellGradient v u = r • shellGradient (omega i) x := by
    funext k
    simp only [shellGradient, hder, Pi.smul_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
  have hnorm : Homogenization.euclideanNorm (shellGradient v u) =
      r * Homogenization.euclideanNorm (shellGradient (omega i) x) := by
    rw [hgrad, Homogenization.euclideanNorm_smul, abs_of_pos hrpos]
  have hunit : u - (0 : Vec d) ∈ cube d 0 := by simpa using hu
  have hbound := aux_psf_le_cellObs 0 (0 : Vec d) u (fun _ => v) hunit
  simpa only [pow_zero, one_mul, hval, hnorm] using! hbound

/-- Scale-adapted finite bank for an actual raw field-score layer. Its cell
count is `(2 * 3^(n-i) + 1)^d`, depending on the scale gap. -/
def aux_prefix_bank_maxObs {d : ℕ} (i n : ℕ) (z : Vec d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℝ :=
  (aux_psf_cells d (n - i)).sup' (aux_psf_cells_nonempty d (n - i))
    (fun k =>
      let r : ℝ := (3 : ℝ) ^ i
      let y : Vec d := aux_psf_center (n - i)
        (((3 : ℝ) ^ (-(i : ℤ))) • z) k
      aux_psf_cellObs 0 (0 : Vec d) (fun _ =>
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale r
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate (r • y) (omega i))))

/-- Every physical observation in the principal raw field-score cube is
bounded by one member of the scale-adapted finite bank. -/
theorem aux_prefix_bank_le_maxObs {d : ℕ} (i n : ℕ) (hin : i ≤ n)
    (z x : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hx : x ∈ translatedCube d (n : ℤ) z) :
    |omega i x| + (3 : ℝ) ^ i *
      Homogenization.euclideanNorm (shellGradient (omega i) x) ≤
      aux_prefix_bank_maxObs i n z omega := by
  let q : ℝ := (3 : ℝ) ^ (-(i : ℤ))
  let r : ℝ := (3 : ℝ) ^ i
  have hresc : q • x ∈ translatedCube d ((n - i : ℕ) : ℤ) (q • z) :=
    aux_prefix_bank_rescaled_cube i n hin z x hx
  obtain ⟨k, hk, hu⟩ := aux_psf_cover' (n - i) (q • z) (q • x) hresc
  let y : Vec d := aux_psf_center (n - i) (q • z) k
  let u : Vec d := q • x - y
  have hrq : r * q = 1 := by
    dsimp [r, q]
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    simp
  have hxrepr : r • (u + y) = x := by
    dsimp [u]
    rw [sub_add_cancel, smul_smul, hrq, one_smul]
  have hcell := aux_prefix_bank_scaled_cell_bound i omega y u hu
  have hle : |omega i x| + r *
      Homogenization.euclideanNorm (shellGradient (omega i) x) ≤
      aux_psf_cellObs 0 (0 : Vec d) (fun _ =>
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale r
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate (r • y) (omega i))) := by
    change |omega i (r • (u + y))| + r *
      Homogenization.euclideanNorm (shellGradient (omega i) (r • (u + y))) ≤
      aux_psf_cellObs 0 (0 : Vec d) (fun _ =>
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale r
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate (r • y) (omega i))) at hcell
    rw [hxrepr] at hcell
    exact hcell
  exact hle.trans (Finset.le_sup' (f := fun k =>
    aux_psf_cellObs 0 (0 : Vec d) (fun _ =>
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale r
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
          (r • aux_psf_center (n - i) (q • z) k) (omega i)))) hk)

/-- Exact raw field-score window: the number of adapted bank cells depends
only on the discount depth `j`, not on the cutoff `m`. -/
theorem aux_prefix_bank_raw_window {d : ℕ} (m j i : ℕ)
    (hi : i ∈ Finset.Icc (m - j) (m + j))
    (z x : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hx : x ∈ translatedCube d ((m + 1 + j : ℕ) : ℤ) z) :
    |omega i x| + (3 : ℝ) ^ i *
      Homogenization.euclideanNorm (shellGradient (omega i) x) ≤
        aux_prefix_bank_maxObs i (m + 1 + j) z omega ∧
    (aux_psf_cells d ((m + 1 + j) - i)).card ≤
      (2 * 3 ^ (2 * j + 1) + 1) ^ d := by
  have hin : i ≤ m + 1 + j := by
    have := (Finset.mem_Icc.mp hi).2
    omega
  constructor
  · exact aux_prefix_bank_le_maxObs i (m + 1 + j) hin z x omega hx
  · rw [aux_psf_cells_card]
    have hgap : (m + 1 + j) - i ≤ 2 * j + 1 := by
      have := (Finset.mem_Icc.mp hi).1
      omega
    exact Nat.pow_le_pow_left (by
      have hp : 3 ^ ((m + 1 + j) - i) ≤ 3 ^ (2 * j + 1) :=
        Nat.pow_le_pow_right (by omega) hgap
      omega) d

end Paper
