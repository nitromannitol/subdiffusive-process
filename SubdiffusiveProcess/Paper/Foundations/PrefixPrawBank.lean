module

public import SubdiffusiveProcess.Paper.primitive_scores_finite

@[expose] public section

/-!
# Scale-adapted banks for the raw product score `Psc`

The product window `∏_{i ∈ [m-j, m+j]} e^{|ω_i(x)|}` over the physical cube of side
`3^(m+1+j)` is dominated by one finite bank of cells at the finest window scale
`3^(m-j)`; its cardinal is `(2*3^((m+1+j)-(m-j))+1)^d ≤ (2*3^(2j+1)+1)^d`, independent of
the cutoff `m`.  The tail product `∏_{i ≥ m+j} e^{4|ω_i(x)-ω_i(z)|}` is dominated through
layer-adapted banks whose cardinal is at most `7^d`.
-/

noncomputable section

open MeasureTheory _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.Paper

variable {d : ℕ}

/-- Layer `i` read from the base point `t` at its own scale: `u ↦ ω_i(3^i u + t)`. -/
def aux_prefix_praw_cellField (i : ℕ) (t : Vec d) (omega : PotentialSample d) :
    PotentialField d :=
  _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale ((3 : ℝ) ^ i) (_root_.SubdiffusiveProcess.Model.PotentialField.translate t (omega i))

/-- Unit-cube value-plus-gradient observable. -/
def aux_prefix_praw_obs (g : PotentialField d) : ℝ :=
  g.unitCubeValueNorm + (d : ℝ) * g.unitCubeDerivNorm

theorem aux_prefix_praw_obs_nonneg (g : PotentialField d) : 0 ≤ aux_prefix_praw_obs g := by
  have h1 := _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeValueNorm_nonneg g
  have h2 := _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeDerivNorm_nonneg g
  unfold aux_prefix_praw_obs
  positivity

theorem aux_prefix_praw_obs_measurable :
    Measurable (fun g : PotentialField d => aux_prefix_praw_obs g) :=
  _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeValueNorm_measurable.add
    (_root_.SubdiffusiveProcess.Model.PotentialField.unitCubeDerivNorm_measurable.const_mul _)

theorem aux_prefix_praw_translate_measurable (i : ℕ) (t : Vec d) :
    Measurable (fun h : PotentialField d =>
      _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale ((3 : ℝ) ^ i) (_root_.SubdiffusiveProcess.Model.PotentialField.translate t h)) :=
  ((_root_.SubdiffusiveProcess.Model.PotentialField.continuous_spatialScale _).measurable).comp
    (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate t)

theorem aux_prefix_praw_cellField_measurable (i : ℕ) (t : Vec d) :
    Measurable (fun omega : PotentialSample d => aux_prefix_praw_cellField i t omega) :=
  (aux_prefix_praw_translate_measurable i t).comp (measurable_potentialCoordinate (d := d) i)

theorem aux_prefix_praw_cellObs_measurable (i : ℕ) (t : Vec d) :
    Measurable (fun omega : PotentialSample d =>
      aux_prefix_praw_obs (aux_prefix_praw_cellField i t omega)) :=
  aux_prefix_praw_obs_measurable.comp (aux_prefix_praw_cellField_measurable i t)

/-- Every scale-adapted cell field has exactly the zero-layer law. -/
theorem aux_prefix_praw_cellField_law (M : GMCModel d) (i : ℕ) (t : Vec d) :
    Measure.map (fun omega : PotentialSample d => aux_prefix_praw_cellField i t omega)
      M.P.toMeasure = (zeroPotentialLaw M.P).toMeasure := by
  let r : ℝ := (3 : ℝ) ^ i
  have hs : Measurable (_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale (d := d) r) :=
    (_root_.SubdiffusiveProcess.Model.PotentialField.continuous_spatialScale r).measurable
  have ht : Measurable (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale (d := d) i) :=
    _root_.SubdiffusiveProcess.Model.PotentialField.measurable_triadicScale i
  have htr : Measurable (fun omega : PotentialSample d =>
      _root_.SubdiffusiveProcess.Model.PotentialField.translate t (omega i)) :=
    (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate t).comp (measurable_potentialCoordinate (d := d) i)
  have hunscale : (fun g : PotentialField d =>
      _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale r (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale i g)) = id := by
    funext g
    apply _root_.SubdiffusiveProcess.Model.PotentialField.ext
    intro x
    rw [_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale_apply, _root_.SubdiffusiveProcess.Model.PotentialField.triadicScale_apply, smul_smul]
    rw [inv_mul_cancel₀ (by positivity : (3 : ℝ) ^ i ≠ 0), one_smul]
    rfl
  calc
    Measure.map (fun omega : PotentialSample d => aux_prefix_praw_cellField i t omega)
        M.P.toMeasure =
        Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale r)
          (Measure.map (fun omega : PotentialSample d =>
            _root_.SubdiffusiveProcess.Model.PotentialField.translate t (omega i)) M.P.toMeasure) :=
      (Measure.map_map hs htr).symm
    _ = Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale r)
          (Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale i) (zeroPotentialLaw M.P).toMeasure) := by
      rw [aux_psf_map_cell M i t]
    _ = Measure.map (fun g : PotentialField d =>
          _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale r (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale i g))
            (zeroPotentialLaw M.P).toMeasure := Measure.map_map hs ht
    _ = (zeroPotentialLaw M.P).toMeasure := by rw [hunscale, Measure.map_id]

/-- Uniform sub-Gaussian moment of every scale-adapted cell observable. -/
theorem aux_prefix_praw_cell_exp_sq (M : GMCModel d) (i : ℕ) (t : Vec d) :
    (∫⁻ omega : PotentialSample d, ENNReal.ofReal (Real.exp
      ((aux_prefix_praw_obs (aux_prefix_praw_cellField i t omega) /
        aux_psf_sigma M) ^ (2 : ℕ))) ∂M.P.toMeasure) ≤ 2 := by
  let F : PotentialField d → ℝ≥0∞ := fun g =>
    ENNReal.ofReal (Real.exp ((aux_prefix_praw_obs g / aux_psf_sigma M) ^ (2 : ℕ)))
  have hFmeas : Measurable F :=
    (((aux_prefix_praw_obs_measurable.div_const _).pow_const _).exp).ennreal_ofReal
  have hsig : 0 < aux_psf_sigma M := aux_psf_sigma_pos M
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hpoint : ∀ g : PotentialField d, F g ≤
      ENNReal.ofReal (Real.exp ((_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g / M.delta) ^ (2 : ℕ))) := by
    intro g
    have hval := _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeValueNorm_nonneg g
    have hder := _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeDerivNorm_nonneg g
    have hlip := _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeDerivLipschitzSeminorm_nonneg g
    have hg2 : _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g =
        g.unitCubeValueNorm + g.unitCubeDerivNorm +
          g.unitCubeDerivLipschitzSeminorm := rfl
    have hX0 : 0 ≤ aux_prefix_praw_obs g := aux_prefix_praw_obs_nonneg g
    have hXle : aux_prefix_praw_obs g ≤ (1 + (d : ℝ)) * _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g := by
      unfold aux_prefix_praw_obs
      rw [hg2]
      nlinarith [mul_nonneg (Nat.cast_nonneg d) hval, mul_nonneg (Nat.cast_nonneg d) hlip]
    have hratio : aux_prefix_praw_obs g / aux_psf_sigma M ≤
        _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g / M.delta := by
      rw [div_le_div_iff₀ hsig hdelta]
      have hmul := mul_le_mul_of_nonneg_right hXle hdelta.le
      unfold aux_psf_sigma
      linarith
    have hsq : (aux_prefix_praw_obs g / aux_psf_sigma M) ^ (2 : ℕ) ≤
        (_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g / M.delta) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (div_nonneg hX0 hsig.le) hratio 2
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hsq)
  change (∫⁻ omega, F (aux_prefix_praw_cellField i t omega) ∂M.P.toMeasure) ≤ 2
  calc
    (∫⁻ omega, F (aux_prefix_praw_cellField i t omega) ∂M.P.toMeasure) =
        ∫⁻ g, F g ∂Measure.map (fun omega : PotentialSample d =>
          aux_prefix_praw_cellField i t omega) M.P.toMeasure :=
      (lintegral_map hFmeas (aux_prefix_praw_cellField_measurable i t)).symm
    _ = ∫⁻ g, F g ∂(zeroPotentialLaw M.P).toMeasure := by
      rw [aux_prefix_praw_cellField_law M i t]
    _ ≤ ∫⁻ g, ENNReal.ofReal (Real.exp
        ((_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g / M.delta) ^ (2 : ℕ)))
          ∂(zeroPotentialLaw M.P).toMeasure := lintegral_mono hpoint
    _ ≤ 2 := aux_psf_orlicz M

/-- A sub-Gaussian square-exponential moment gives every linear exponential moment. -/
theorem aux_prefix_praw_exp_lin {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (hf : Measurable f) (σ : ℝ) (hσ : 0 < σ)
    (h : (∫⁻ ω, ENNReal.ofReal (Real.exp ((f ω / σ) ^ (2 : ℕ))) ∂μ) ≤ 2) (lam : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (lam * f ω)) ∂μ) ≤
      ENNReal.ofReal (Real.exp (lam ^ 2 * σ ^ 2 / 4)) * 2 := by
  have hpt : ∀ ω, ENNReal.ofReal (Real.exp (lam * f ω)) ≤
      ENNReal.ofReal (Real.exp (lam ^ 2 * σ ^ 2 / 4)) *
        ENNReal.ofReal (Real.exp ((f ω / σ) ^ (2 : ℕ))) := by
    intro ω
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have key : (f ω / σ - lam * σ / 2) ^ 2 =
        (f ω / σ) ^ 2 - lam * f ω + lam ^ 2 * σ ^ 2 / 4 := by
      field_simp
      ring
    have hnn := sq_nonneg (f ω / σ - lam * σ / 2)
    rw [key] at hnn
    linarith
  have hmeas : Measurable fun ω => ENNReal.ofReal (Real.exp ((f ω / σ) ^ (2 : ℕ))) :=
    (((hf.div_const _).pow_const _).exp).ennreal_ofReal
  calc (∫⁻ ω, ENNReal.ofReal (Real.exp (lam * f ω)) ∂μ) ≤
      ∫⁻ ω, ENNReal.ofReal (Real.exp (lam ^ 2 * σ ^ 2 / 4)) *
        ENNReal.ofReal (Real.exp ((f ω / σ) ^ (2 : ℕ))) ∂μ := lintegral_mono hpt
    _ = ENNReal.ofReal (Real.exp (lam ^ 2 * σ ^ 2 / 4)) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp ((f ω / σ) ^ (2 : ℕ))) ∂μ :=
      lintegral_const_mul _ hmeas
    _ ≤ ENNReal.ofReal (Real.exp (lam ^ 2 * σ ^ 2 / 4)) * 2 := by gcongr

/-- Linear exponential moment of one scale-adapted cell observable. -/
theorem aux_prefix_praw_cell_exp_lin (M : GMCModel d) (i : ℕ) (t : Vec d) (lam : ℝ) :
    (∫⁻ omega : PotentialSample d, ENNReal.ofReal (Real.exp
      (lam * aux_prefix_praw_obs (aux_prefix_praw_cellField i t omega))) ∂M.P.toMeasure) ≤
      ENNReal.ofReal (Real.exp (lam ^ 2 * aux_psf_sigma M ^ 2 / 4)) * 2 :=
  aux_prefix_praw_exp_lin M.P.toMeasure _ (aux_prefix_praw_cellObs_measurable i t)
    (aux_psf_sigma M) (aux_psf_sigma_pos M) (aux_prefix_praw_cell_exp_sq M i t) lam

/-- A union bound for the linear exponential moment of a finite maximum. -/
theorem aux_prefix_praw_sup_exp_lin {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Finset ι) (hs : s.Nonempty) (f : ι → Ω → ℝ) (hf : ∀ i, Measurable (f i))
    (lam : ℝ) (B : ℝ≥0∞)
    (h : ∀ i ∈ s, (∫⁻ ω, ENNReal.ofReal (Real.exp (lam * f i ω)) ∂μ) ≤ B) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (lam * s.sup' hs (fun i => f i ω))) ∂μ) ≤
      (s.card : ℝ≥0∞) * B := by
  have hpt : ∀ ω, ENNReal.ofReal (Real.exp (lam * s.sup' hs (fun i => f i ω))) ≤
      ∑ i ∈ s, ENNReal.ofReal (Real.exp (lam * f i ω)) := by
    intro ω
    obtain ⟨i, hi, heq⟩ := s.exists_mem_eq_sup' hs (fun i => f i ω)
    rw [heq]
    exact Finset.single_le_sum (f := fun i => ENNReal.ofReal (Real.exp (lam * f i ω)))
      (fun i _ => bot_le) hi
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_finsetSum _ (fun i _ => (((hf i).const_mul _).exp).ennreal_ofReal)]
  calc (∑ i ∈ s, ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * f i ω)) ∂μ) ≤ ∑ _i ∈ s, B :=
        Finset.sum_le_sum h
    _ = (s.card : ℝ≥0∞) * B := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Hölder (Jensen) interpolation of a linear exponential moment. -/
theorem aux_prefix_praw_exp_holder {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (lam theta : ℝ) (hlam : 0 < lam) (hlt : lam < theta) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ) ≤
      (∫⁻ ω, ENNReal.ofReal (Real.exp (theta * X ω)) ∂μ) ^ (lam / theta) := by
  have hth0 : 0 < theta := lt_trans hlam hlt
  set p : ℝ := theta / lam with hp
  have hp1 : 1 < p := by rw [hp, lt_div_iff₀ hlam]; linarith
  have hinv : 1 / p = lam / theta := by rw [hp, one_div_div]
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (theta * X ω))) μ :=
    (((hX.const_mul _).exp).ennreal_ofReal).aemeasurable
  have hrw : ∀ ω, ENNReal.ofReal (Real.exp (lam * X ω)) =
      (ENNReal.ofReal (Real.exp (theta * X ω))) ^ (1 / p) := by
    intro ω
    rw [aux_psf_ofReal_exp_rpow, hinv]
    congr 2
    field_simp
  calc (∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ) =
      ∫⁻ ω, (ENNReal.ofReal (Real.exp (theta * X ω))) ^ (1 / p) ∂μ := by simp only [hrw]
    _ ≤ (∫⁻ ω, ENNReal.ofReal (Real.exp (theta * X ω)) ∂μ) ^ (1 / p) :=
      aux_psf_lintegral_rpow_inv_le μ hmeas hp1
    _ = _ := by rw [hinv]

/-! ### Rescaled covers -/

/-- Rescaling a physical cube by `3^{-a}`; for `a > n` the rescaled cube lies in a unit
cube. -/
theorem aux_prefix_praw_rescaled_cube (a n : ℕ) (z x : Vec d)
    (hx : x ∈ translatedCube d (n : ℤ) z) :
    ((3 : ℝ) ^ (-(a : ℤ))) • x ∈
      translatedCube d ((n - a : ℕ) : ℤ) (((3 : ℝ) ^ (-(a : ℤ))) • z) := by
  rw [aux_psf_mem_translatedCube_iff] at hx ⊢
  intro k
  have h := hx k
  have h3 : 0 < (3 : ℝ) ^ (-(a : ℤ)) := zpow_pos (by norm_num) _
  have hscale : (3 : ℝ) ^ (-(a : ℤ)) * (3 : ℝ) ^ (n : ℤ) ≤ (3 : ℝ) ^ (((n - a : ℕ)) : ℤ) := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← mul_sub, abs_mul, abs_of_pos h3]
  calc (3 : ℝ) ^ (-(a : ℤ)) * |x k - z k| <
        (3 : ℝ) ^ (-(a : ℤ)) * ((3 : ℝ) ^ (n : ℤ) / 2) := mul_lt_mul_of_pos_left h h3
    _ ≤ (3 : ℝ) ^ (((n - a : ℕ)) : ℤ) / 2 := by linarith

/-- The finite cover of a rescaled physical cube: each point is `3^a (u + c_k)` with `u` in
the unit cube and `c_k` a bank centre. -/
theorem aux_prefix_praw_cover (a n : ℕ) (z x : Vec d)
    (hx : x ∈ translatedCube d (n : ℤ) z) :
    ∃ k ∈ aux_psf_cells d (n - a),
      ∃ u ∈ cube d 0, x = ((3 : ℝ) ^ a) • u +
        ((3 : ℝ) ^ a) • aux_psf_center (n - a) (((3 : ℝ) ^ (-(a : ℤ))) • z) k := by
  obtain ⟨k, hk, hu⟩ := aux_psf_cover' (n - a) _ _ (aux_prefix_praw_rescaled_cube a n z x hx)
  refine ⟨k, hk, _, hu, ?_⟩
  rw [← smul_add, sub_add_cancel, smul_smul]
  have h : (3 : ℝ) ^ a * (3 : ℝ) ^ (-(a : ℤ)) = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    simp
  rw [h, one_smul]

/-- A point of a finest-scale cell is seen by every coarser layer's cell observable. -/
theorem aux_prefix_praw_abs_le_obs (i a : ℕ) (hai : a ≤ i) (t u : Vec d)
    (hu : u ∈ cube d 0) (omega : PotentialSample d) :
    |omega i (((3 : ℝ) ^ a) • u + t)| ≤
      aux_prefix_praw_obs (aux_prefix_praw_cellField i t omega) := by
  set c : ℝ := ((3 : ℝ) ^ (i - a))⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hu' : c • u ∈ cube d 0 := aux_psf_smul_mem_cube_zero hc0 hc1 hu
  have hpow : (3 : ℝ) ^ i * c = (3 : ℝ) ^ a := by
    rw [hc, show i = a + (i - a) by omega, pow_add]
    rw [show a + (i - a) - a = i - a by omega]
    field_simp
  have hval : aux_prefix_praw_cellField i t omega (c • u) = omega i (((3 : ℝ) ^ a) • u + t) := by
    rw [aux_prefix_praw_cellField, _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale_apply,
      _root_.SubdiffusiveProcess.Model.PotentialField.translate_apply, smul_smul, hpow]
  have h := _root_.SubdiffusiveProcess.Model.PotentialField.abs_apply_le_unitCubeValueNorm
    (aux_prefix_praw_cellField i t omega) (x := c • u) hu'
  rw [hval] at h
  have hder := _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeDerivNorm_nonneg (aux_prefix_praw_cellField i t omega)
  unfold aux_prefix_praw_obs
  have : (0 : ℝ) ≤ (d : ℝ) * (aux_prefix_praw_cellField i t omega).unitCubeDerivNorm := by
    positivity
  linarith

/-- The scaled gradient of layer `i` on its own cell is seen by the cell observable. -/
theorem aux_prefix_praw_deriv_le_obs (hd : (1 : ℝ) ≤ (d : ℝ)) (i : ℕ) (t u : Vec d)
    (hu : u ∈ cube d 0) (omega : PotentialSample d) :
    (3 : ℝ) ^ i * ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv (omega i) (((3 : ℝ) ^ i) • u + t)‖ ≤
      aux_prefix_praw_obs (aux_prefix_praw_cellField i t omega) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ i := by positivity
  have hder : _root_.SubdiffusiveProcess.Model.PotentialField.deriv (aux_prefix_praw_cellField i t omega) u =
      ((3 : ℝ) ^ i) • _root_.SubdiffusiveProcess.Model.PotentialField.deriv (omega i) (((3 : ℝ) ^ i) • u + t) := by
    rw [aux_prefix_praw_cellField, aux_psf_deriv_spatialScale, aux_psf_deriv_translate]
  have h := _root_.SubdiffusiveProcess.Model.PotentialField.norm_deriv_le_unitCubeDerivNorm
    (aux_prefix_praw_cellField i t omega) (x := u) hu
  rw [hder, norm_smul, Real.norm_eq_abs, abs_of_pos h3] at h
  have hval := _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeValueNorm_nonneg (aux_prefix_praw_cellField i t omega)
  have hD := _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeDerivNorm_nonneg (aux_prefix_praw_cellField i t omega)
  unfold aux_prefix_praw_obs
  nlinarith

/-! ### The product-window bank -/

/-- Base point of bank cell `k` at the finest window scale `3^(m-j)`. -/
def aux_prefix_praw_Abase (m j : ℕ) (z : Vec d) (k : Fin d → ℕ) : Vec d :=
  ((3 : ℝ) ^ (m - j)) •
    aux_psf_center (m + 1 + j - (m - j)) (((3 : ℝ) ^ (-((m - j : ℕ) : ℤ))) • z) k

/-- Measurable majorant of the product window: one finite bank at the finest scale. -/
def aux_prefix_praw_Amaj (m j : ℕ) (z : Vec d) (omega : PotentialSample d) : ℝ≥0∞ :=
  (aux_psf_cells d (m + 1 + j - (m - j))).sup' (aux_psf_cells_nonempty d _)
    (fun k => ENNReal.ofReal (Real.exp (∑ i ∈ Finset.Icc (m - j) (m + j),
      aux_prefix_praw_obs (aux_prefix_praw_cellField i (aux_prefix_praw_Abase m j z k) omega))))

theorem aux_prefix_praw_Amaj_measurable (m j : ℕ) (z : Vec d) :
    Measurable (fun omega : PotentialSample d => aux_prefix_praw_Amaj m j z omega) := by
  have h : Measurable ((aux_psf_cells d (m + 1 + j - (m - j))).sup'
      (aux_psf_cells_nonempty d _)
      (fun k (omega : PotentialSample d) =>
        ENNReal.ofReal (Real.exp (∑ i ∈ Finset.Icc (m - j) (m + j),
          aux_prefix_praw_obs
            (aux_prefix_praw_cellField i (aux_prefix_praw_Abase m j z k) omega))))) := by
    refine Finset.measurable_sup' _ (fun k _ => ?_)
    exact (Real.measurable_exp.comp (Finset.measurable_sum _ (fun i _ =>
      aux_prefix_praw_cellObs_measurable i _))).ennreal_ofReal
  convert h using 1
  funext omega
  unfold aux_prefix_praw_Amaj
  rw [Finset.sup'_apply]

/-- Pointwise domination of the literal product window. -/
theorem aux_prefix_praw_prod_le_Amaj (m j : ℕ) (z x : Vec d) (omega : PotentialSample d)
    (hx : x ∈ translatedCube d ((m : ℤ) + 1 + (j : ℤ)) z) :
    (∏ i ∈ Finset.Icc (m - j) (m + j), ENNReal.ofReal (Real.exp |omega i x|)) ≤
      aux_prefix_praw_Amaj m j z omega := by
  have hcast : ((m : ℤ) + 1 + (j : ℤ)) = (((m + 1 + j : ℕ)) : ℤ) := by push_cast; ring
  rw [hcast] at hx
  obtain ⟨k, hk, u, hu, hxu⟩ := aux_prefix_praw_cover (m - j) (m + 1 + j) z x hx
  rw [aux_psf_prod_ofReal_exp]
  refine le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
    (Finset.le_sup' (f := fun k : Fin d → ℕ =>
      ENNReal.ofReal (Real.exp (∑ i ∈ Finset.Icc (m - j) (m + j),
        aux_prefix_praw_obs
          (aux_prefix_praw_cellField i (aux_prefix_praw_Abase m j z k) omega)))) hk)
  refine Finset.sum_le_sum (fun i hi => ?_)
  have hai : m - j ≤ i := (Finset.mem_Icc.mp hi).1
  have h := aux_prefix_praw_abs_le_obs i (m - j) hai (aux_prefix_praw_Abase m j z k) u hu omega
  rw [hxu]
  exact h

/-! ### The tail bank -/

/-- Layer-adapted bank for layer `i` over the physical cube of side `3^n`. -/
def aux_prefix_praw_bank (i n : ℕ) (z : Vec d) (omega : PotentialSample d) : ℝ :=
  (aux_psf_cells d (n - i)).sup' (aux_psf_cells_nonempty d (n - i))
    (fun k => aux_prefix_praw_obs (aux_prefix_praw_cellField i
      (((3 : ℝ) ^ i) • aux_psf_center (n - i) (((3 : ℝ) ^ (-(i : ℤ))) • z) k) omega))

theorem aux_prefix_praw_bank_measurable (i n : ℕ) (z : Vec d) :
    Measurable (fun omega : PotentialSample d => aux_prefix_praw_bank i n z omega) := by
  have h : Measurable ((aux_psf_cells d (n - i)).sup' (aux_psf_cells_nonempty d (n - i))
      (fun k (omega : PotentialSample d) => aux_prefix_praw_obs (aux_prefix_praw_cellField i
        (((3 : ℝ) ^ i) • aux_psf_center (n - i) (((3 : ℝ) ^ (-(i : ℤ))) • z) k) omega))) :=
    Finset.measurable_sup' _ (fun k _ => aux_prefix_praw_cellObs_measurable i _)
  convert h using 1
  funext omega
  unfold aux_prefix_praw_bank
  rw [Finset.sup'_apply]

theorem aux_prefix_praw_bank_nonneg (i n : ℕ) (z : Vec d) (omega : PotentialSample d) :
    0 ≤ aux_prefix_praw_bank i n z omega := by
  obtain ⟨k, hk⟩ := aux_psf_cells_nonempty d (n - i)
  exact (aux_prefix_praw_obs_nonneg _).trans (Finset.le_sup' (f := fun k =>
    aux_prefix_praw_obs (aux_prefix_praw_cellField i
      (((3 : ℝ) ^ i) • aux_psf_center (n - i) (((3 : ℝ) ^ (-(i : ℤ))) • z) k) omega)) hk)

/-- Gradient control of every layer on the whole physical cube through its bank. -/
theorem aux_prefix_praw_deriv_le_bank (hd : (1 : ℝ) ≤ (d : ℝ)) (i n : ℕ) (z y : Vec d)
    (omega : PotentialSample d) (hy : y ∈ translatedCube d (n : ℤ) z) :
    ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv (omega i) y‖ ≤ ((3 : ℝ) ^ i)⁻¹ * aux_prefix_praw_bank i n z omega := by
  obtain ⟨k, hk, u, hu, hyu⟩ := aux_prefix_praw_cover i n z y hy
  have h3 : (0 : ℝ) < (3 : ℝ) ^ i := by positivity
  have h := aux_prefix_praw_deriv_le_obs hd i
    (((3 : ℝ) ^ i) • aux_psf_center (n - i) (((3 : ℝ) ^ (-(i : ℤ))) • z) k) u hu omega
  rw [← hyu] at h
  have hmax : aux_prefix_praw_obs (aux_prefix_praw_cellField i
      (((3 : ℝ) ^ i) • aux_psf_center (n - i) (((3 : ℝ) ^ (-(i : ℤ))) • z) k) omega) ≤
      aux_prefix_praw_bank i n z omega :=
    Finset.le_sup' (f := fun k => aux_prefix_praw_obs (aux_prefix_praw_cellField i
      (((3 : ℝ) ^ i) • aux_psf_center (n - i) (((3 : ℝ) ^ (-(i : ℤ))) • z) k) omega)) hk
  rw [inv_mul_eq_div, le_div_iff₀ h3]
  linarith

/-- Oscillation of layer `i` between the anchor and a cube point. -/
theorem aux_prefix_praw_diff_le_bank (hd : (1 : ℝ) ≤ (d : ℝ)) (i n : ℕ) (z x : Vec d)
    (omega : PotentialSample d) (hx : x ∈ translatedCube d (n : ℤ) z) :
    |omega i x - omega i z| ≤
      ((3 : ℝ) ^ i)⁻¹ * aux_prefix_praw_bank i n z omega * ((3 : ℝ) ^ (n : ℤ) / 2) := by
  have hconv := aux_psf_convex_translatedCube (d := d) (n : ℤ) z
  have hzmem := aux_psf_center_mem (d := d) n z
  have hfd : ∀ w ∈ translatedCube d (n : ℤ) z,
      HasFDerivWithinAt (fun u : Vec d => (omega i : Vec d → ℝ) u)
        (_root_.SubdiffusiveProcess.Model.PotentialField.deriv (omega i) w) (translatedCube d (n : ℤ) z) w :=
    fun w _ => ((omega i).hasFDerivAt w).hasFDerivWithinAt
  have hbound : ∀ w ∈ translatedCube d (n : ℤ) z,
      ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv (omega i) w‖ ≤
        ((3 : ℝ) ^ i)⁻¹ * aux_prefix_praw_bank i n z omega :=
    fun w hw => aux_prefix_praw_deriv_le_bank hd i n z w omega hw
  have hmain := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le hfd hbound hzmem hx
  have hnorm : ‖x - z‖ ≤ (3 : ℝ) ^ (n : ℤ) / 2 := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro k
    rw [Real.norm_eq_abs]
    have := (aux_psf_mem_translatedCube_iff.1 hx) k
    simp only [Pi.sub_apply]
    linarith
  have hC0 : 0 ≤ ((3 : ℝ) ^ i)⁻¹ * aux_prefix_praw_bank i n z omega := by
    have := aux_prefix_praw_bank_nonneg i n z omega
    positivity
  calc |omega i x - omega i z| = ‖(omega i : Vec d → ℝ) x - (omega i : Vec d → ℝ) z‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ((3 : ℝ) ^ i)⁻¹ * aux_prefix_praw_bank i n z omega * ‖x - z‖ := hmain
    _ ≤ ((3 : ℝ) ^ i)⁻¹ * aux_prefix_praw_bank i n z omega * ((3 : ℝ) ^ (n : ℤ) / 2) :=
        mul_le_mul_of_nonneg_left hnorm hC0

/-- Measurable majorant of the tail product through the layer-adapted banks. -/
def aux_prefix_praw_Bmaj (m j : ℕ) (z : Vec d) (omega : PotentialSample d) : ℝ≥0∞ :=
  ⨆ K : ℕ, ENNReal.ofReal (Real.exp (∑ i ∈ Finset.Icc (m + j) (m + j + K),
    aux_psf_lam m j i * aux_prefix_praw_bank i (m + 1 + j) z omega))

theorem aux_prefix_praw_Bmaj_measurable (m j : ℕ) (z : Vec d) :
    Measurable (fun omega : PotentialSample d => aux_prefix_praw_Bmaj m j z omega) :=
  Measurable.iSup fun _ => (Real.measurable_exp.comp (Finset.measurable_sum _ (fun i _ =>
    (aux_prefix_praw_bank_measurable i (m + 1 + j) z).const_mul _))).ennreal_ofReal

/-- Pointwise domination of the literal product-score term by the two banks. -/
theorem aux_prefix_praw_Pterm_le (hd : (1 : ℝ) ≤ (d : ℝ)) (m j : ℕ) (z : Vec d)
    (omega : PotentialSample d) :
    sSup {w : ℝ≥0∞ | ∃ x : Vec d, x ∈ translatedCube d ((m : ℤ) + 1 + (j : ℤ)) z ∧
      w = (∏ i ∈ Finset.Icc (m - j) (m + j), ENNReal.ofReal (Real.exp |omega i x|)) +
          sSup {u : ℝ≥0∞ | ∃ K : ℕ, u = ∏ i ∈ Finset.Icc (m + j) (m + j + K),
            ENNReal.ofReal (Real.exp (4 * |omega i x - omega i z|))}} ≤
      aux_prefix_praw_Amaj m j z omega + aux_prefix_praw_Bmaj m j z omega := by
  refine sSup_le ?_
  rintro w ⟨x, hx, rfl⟩
  refine add_le_add (aux_prefix_praw_prod_le_Amaj m j z x omega hx) ?_
  have hcast : ((m : ℤ) + 1 + (j : ℤ)) = (((m + 1 + j : ℕ)) : ℤ) := by push_cast; ring
  rw [hcast] at hx
  refine sSup_le ?_
  rintro u ⟨K, rfl⟩
  rw [aux_psf_prod_ofReal_exp]
  refine le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
    (le_iSup (fun K : ℕ => ENNReal.ofReal (Real.exp
      (∑ i ∈ Finset.Icc (m + j) (m + j + K),
        aux_psf_lam m j i * aux_prefix_praw_bank i (m + 1 + j) z omega))) K)
  refine Finset.sum_le_sum (fun i _ => ?_)
  have h := aux_prefix_praw_diff_le_bank hd i (m + 1 + j) z x omega hx
  have hlam : aux_psf_lam m j i * aux_prefix_praw_bank i (m + 1 + j) z omega =
      4 * (((3 : ℝ) ^ i)⁻¹ * aux_prefix_praw_bank i (m + 1 + j) z omega *
        ((3 : ℝ) ^ ((m + 1 + j : ℕ) : ℤ) / 2)) := by
    unfold aux_psf_lam
    rw [zpow_natCast]
    ring
  rw [hlam]
  linarith

end SubdiffusiveProcess.Paper
