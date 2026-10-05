module

public import SubdiffusiveProcess.Assumptions
public import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments
public import Homogenization.Book.Ch04.Theorems.ConcentrationAEMeasurable
public import Homogenization.Probability.IndependentSums.GammaSigma.Operations
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory ProbabilityTheory
open Homogenization Homogenization.Book Homogenization.IndependentSums
open scoped BigOperators ENNReal NNReal

noncomputable section

variable {d : ℕ}

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

private abbrev Field (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialField d

/-! ## Law transport to the zero shell -/

/-- Undo the source's triadic spatial scaling on shell `j`. -/
def unscalePotential (j : ℕ) (g : _root_.SubdiffusiveProcess.Model.PotentialField d) : _root_.SubdiffusiveProcess.Model.PotentialField d :=
  _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale ((3 : ℝ) ^ j) g

theorem measurable_unscalePotential (j : ℕ) :
    Measurable (unscalePotential (d := d) j) :=
  (_root_.SubdiffusiveProcess.Model.PotentialField.continuous_spatialScale _).measurable

@[simp]
theorem unscalePotential_triadicScale (j : ℕ) (g : _root_.SubdiffusiveProcess.Model.PotentialField d) :
    unscalePotential j
        (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale j g) = g := by
  apply _root_.SubdiffusiveProcess.Model.PotentialField.ext
  intro x
  simp only [unscalePotential,
    _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale_apply,
    _root_.SubdiffusiveProcess.Model.PotentialField.triadicScale_apply]
  rw [smul_smul]
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  rw [inv_mul_cancel₀ h3.ne', one_smul]

/-- The reverse-scaled `j`th coordinate has exactly the zero-shell law. -/
theorem map_unscalePotential_coordinate_eq_zero
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) :
    Measure.map (fun ω : _root_.SubdiffusiveProcess.Model.PotentialSample d => unscalePotential j (ω j)) M.P.toMeasure =
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
  let μ₀ := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  have hcoord := _root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate (d := d) j
  have hunscale := measurable_unscalePotential (d := d) j
  calc
    Measure.map (fun ω : _root_.SubdiffusiveProcess.Model.PotentialSample d => unscalePotential j (ω j)) M.P.toMeasure =
        Measure.map (unscalePotential j)
          (_root_.SubdiffusiveProcess.Model.potentialMarginalLaw M.P j).toMeasure := by
      rw [_root_.SubdiffusiveProcess.Model.potentialMarginalLaw,
        ProbabilityMeasure.toMeasure_map, Measure.map_map hunscale hcoord]
      rfl
    _ = Measure.map (unscalePotential j)
          (Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale j) μ₀) := by
      rw [M.shellPrefix.marginal_scaling j, ProbabilityMeasure.toMeasure_map]
    _ = Measure.map
          (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d => unscalePotential j
            (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale j g)) μ₀ := by
      rw [Measure.map_map hunscale
        (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_triadicScale j)]
      rfl
    _ = Measure.map id μ₀ := by
      congr 1
      funext g
      exact unscalePotential_triadicScale j g
    _ = μ₀ := Measure.map_id

/-- Reverse scaling followed by a deterministic translation still has the
zero-shell law, by `(g1)`. -/
theorem map_translate_unscalePotential_coordinate_eq_zero
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) (z : Vec d) :
    Measure.map
        (fun ω : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
          _root_.SubdiffusiveProcess.Model.PotentialField.translate z
            (unscalePotential j (ω j))) M.P.toMeasure =
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
  let T := _root_.SubdiffusiveProcess.Model.PotentialField.translate (d := d) z
  have hT := _root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate z
  have hU : Measurable (fun ω : _root_.SubdiffusiveProcess.Model.PotentialSample d => unscalePotential j (ω j)) :=
    (measurable_unscalePotential j).comp
      (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate j)
  calc
    Measure.map (fun ω : _root_.SubdiffusiveProcess.Model.PotentialSample d => T (unscalePotential j (ω j))) M.P.toMeasure =
        Measure.map T
          (Measure.map (fun ω : _root_.SubdiffusiveProcess.Model.PotentialSample d => unscalePotential j (ω j))
            M.P.toMeasure) := by
      rw [Measure.map_map hT hU]
      rfl
    _ = Measure.map T
          (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
      rw [map_unscalePotential_coordinate_eq_zero M j]
    _ = (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
      simpa [T] using M.G1.stationary z


/-- Weak-Orlicz tails depend only on the law of a measurable observable. -/
theorem isBigOWith_of_map_eq {Omega Xi : Type*} [MeasurableSpace Omega]
    [MeasurableSpace Xi] {mu : Measure Omega} {nu : Measure Xi}
    [IsFiniteMeasure mu] [IsFiniteMeasure nu] {X : Omega → ℝ} {Y : Xi → ℝ}
    {Psi : ℝ → ℝ} {A : ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hmap : Measure.map X mu = Measure.map Y nu)
    (hYtail : IsBigOWith nu Psi Y A) :
    IsBigOWith mu Psi X A := by
  intro t ht
  have hE : MeasurableSet {x : ℝ | A * t < x} :=
    measurableSet_lt measurable_const measurable_id
  calc
    mu.real {omega | A * t < X omega} =
        (Measure.map X mu).real {x : ℝ | A * t < x} := by
      have h := congrArg ENNReal.toReal
        (Measure.map_apply_of_aemeasurable (μ := mu) hX.aemeasurable hE)
      simpa only [Measure.real, Set.preimage_ofPred_eq] using! h.symm
    _ = (Measure.map Y nu).real {x : ℝ | A * t < x} := by rw [hmap]
    _ = nu.real {omega | A * t < Y omega} := by
      have h := congrArg ENNReal.toReal
        (Measure.map_apply_of_aemeasurable (μ := nu) hY.aemeasurable hE)
      simpa only [Measure.real, Set.preimage_ofPred_eq] using! h
    _ ≤ (Psi t)⁻¹ := hYtail ht

/-- The `(g2)` observable of any reverse-scaled, translated shell. -/
def translatedShellG2 (j : ℕ) (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
    (_root_.SubdiffusiveProcess.Model.PotentialField.translate z
      (unscalePotential j (omega j)))

theorem measurable_translatedShellG2 (j : ℕ) (z : Vec d) :
    Measurable (translatedShellG2 (d := d) j z) :=
  _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_measurable.comp
    ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate z).comp
      ((measurable_unscalePotential j).comp
        (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate j)))

theorem translatedShellG2_nonneg (j : ℕ) (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ translatedShellG2 j z omega :=
  _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _

/-- Every translated own-scale `(g2)` gauge has the same `Gamma_2` scale. -/
theorem isBigOWith_gammaTwo_translatedShellG2
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) (z : Vec d) :
    IsBigOWith M.P.toMeasure (gammaSigma 2) (translatedShellG2 j z)
      ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) := by
  let G := _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable (d := d)
  let T : _root_.SubdiffusiveProcess.Model.PotentialSample d → _root_.SubdiffusiveProcess.Model.PotentialField d := fun omega =>
    _root_.SubdiffusiveProcess.Model.PotentialField.translate z
      (unscalePotential j (omega j))
  have hbase := SubdiffusiveProcess.OGammaBridge.isBigO_gammaSigma_of_ogammaLE
    (μ := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)
    (σ := 2) (A := M.delta) (X := G) (by norm_num)
    M.shellPrefix.delta_pos
    _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg
    M.G2.regularity_expectation
  have hbaseWith : IsBigOWith
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
      (gammaSigma 2) G ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) := by
    simpa [IsBigO, G, abs_of_nonneg
      (_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _)] using hbase
  have hmapT := map_translate_unscalePotential_coordinate_eq_zero M j z
  have hGT : Measurable (G ∘ T) :=
    _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_measurable.comp
      ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate z).comp
        ((measurable_unscalePotential j).comp
          (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate j)))
  have hmapG : Measure.map (G ∘ T) M.P.toMeasure =
      Measure.map G
        (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
    calc
      Measure.map (G ∘ T) M.P.toMeasure =
          Measure.map G (Measure.map T M.P.toMeasure) := by
        symm
        simpa [G, T, Function.comp_def] using (Measure.map_map
          _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_measurable
          ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate z).comp
            ((measurable_unscalePotential j).comp
              (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate j))) :
            Measure.map G (Measure.map T M.P.toMeasure) =
              Measure.map (G ∘ T) M.P.toMeasure)
      _ = Measure.map G
          (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by rw [hmapT]
  simpa [translatedShellG2, G, T, Function.comp_def] using!
    isBigOWith_of_map_eq (nu :=
        (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) hGT
      _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_measurable hmapG hbaseWith

/-! ## Deterministic cube oscillations -/

public abbrev CubePoint (d : ℕ) (k : ℤ) :=
  {x : Vec d // x ∈ openCubeSet (originCube d k)}

/-- Literal all-pairs oscillation on the open origin cube.  The `none` member
records the source convention that an oscillation is nonnegative. -/
noncomputable def cubeOscillation (k : ℤ) (f : Vec d → ℝ) : ℝ :=
  sSup (Set.range fun o : Option (CubePoint d k × CubePoint d k) =>
    match o with
    | none => 0
    | some p => f p.1.1 - f p.2.1)

theorem cubeOscillation_nonneg (k : ℤ) (f : Vec d → ℝ) :
    0 ≤ cubeOscillation k f := by
  by_cases h : BddAbove
      (Set.range fun o : Option (CubePoint d k × CubePoint d k) =>
        match o with | none => 0 | some p => f p.1.1 - f p.2.1)
  · unfold cubeOscillation
    exact le_csSup h ⟨none, rfl⟩
  · unfold cubeOscillation
    rw [csSup_of_not_bddAbove h]
    simp

theorem cubeOscillation_le_of_forall (k : ℤ) (f : Vec d → ℝ) {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ x y : Vec d, x ∈ openCubeSet (originCube d k) →
      y ∈ openCubeSet (originCube d k) → f x - f y ≤ C) :
    cubeOscillation k f ≤ C := by
  unfold cubeOscillation
  refine csSup_le (Set.range_nonempty _) ?_
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact hC
  | some p => exact h p.1.1 p.2.1 p.1.2 p.2.2

/-- Every literal pair difference is below the all-pairs oscillation for a
continuous field.  Continuity supplies the boundedness needed by `sSup`. -/
theorem sub_le_cubeOscillation_of_continuous (k : ℤ) {f : Vec d → ℝ}
    (hf : Continuous f) {x y : Vec d}
    (hx : x ∈ openCubeSet (originCube d k))
    (hy : y ∈ openCubeSet (originCube d k)) :
    f x - f y ≤ cubeOscillation k f := by
  unfold cubeOscillation
  apply le_csSup
  · obtain ⟨C, hC⟩ :=
      (isCompact_closedBall (cubeCenter (originCube d k))
        (cubeRadius (originCube d k))).exists_bound_of_continuousOn
          ((continuous_abs.comp hf).continuousOn)
    refine ⟨2 * max 0 C, ?_⟩
    rintro r ⟨o, rfl⟩
    cases o with
    | none => positivity
    | some p =>
      have hp1 : p.1.1 ∈ Metric.closedBall (cubeCenter (originCube d k))
          (cubeRadius (originCube d k)) := by
        apply Metric.ball_subset_closedBall
        rw [ball_cubeCenter_eq_openCubeSet]
        exact p.1.2
      have hp2 : p.2.1 ∈ Metric.closedBall (cubeCenter (originCube d k))
          (cubeRadius (originCube d k)) := by
        apply Metric.ball_subset_closedBall
        rw [ball_cubeCenter_eq_openCubeSet]
        exact p.2.2
      have h1 := (hC p.1.1 hp1).trans (le_max_right 0 C)
      have h2 := (hC p.2.1 hp2).trans (le_max_right 0 C)
      simp only [Function.comp_apply, Real.norm_eq_abs, abs_abs] at h1 h2
      nlinarith [le_abs_self (f p.1.1), neg_le_abs (f p.2.1)]
  · exact ⟨some ⟨⟨x, hx⟩, ⟨y, hy⟩⟩, rfl⟩

private theorem deriv_norm_le_unitCubeDerivNorm (g : _root_.SubdiffusiveProcess.Model.PotentialField d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d 0)) :
    ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x‖ ≤
      _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeDerivNorm g := by
  unfold _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeDerivNorm
  apply le_csSup
  · obtain ⟨C, hC⟩ :=
      (isCompact_closedBall (cubeCenter (originCube d 0))
        (cubeRadius (originCube d 0))).exists_bound_of_continuousOn
          ((continuous_norm.comp
            (_root_.SubdiffusiveProcess.Model.PotentialField.deriv g).continuous).continuousOn)
    refine ⟨max 0 C, ?_⟩
    rintro r ⟨o, rfl⟩
    cases o with
    | none => exact le_max_left _ _
    | some y =>
      have hy : y.1 ∈ Metric.closedBall (cubeCenter (originCube d 0))
          (cubeRadius (originCube d 0)) := by
        apply Metric.ball_subset_closedBall
        rw [ball_cubeCenter_eq_openCubeSet]
        exact y.2
      have hr := hC y.1 hy
      simpa only [Function.comp_apply, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _)] using hr.trans (le_max_right _ _)
  · exact ⟨some ⟨x, hx⟩, rfl⟩

private theorem deriv_norm_le_g2Observable (g : _root_.SubdiffusiveProcess.Model.PotentialField d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d 0)) :
    ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x‖ ≤
      _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g := by
  calc
    ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x‖ ≤
        _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeDerivNorm g :=
      deriv_norm_le_unitCubeDerivNorm g hx
    _ ≤ _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g := by
      unfold _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
      have hvalue := _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeValueNorm_nonneg g
      have hlip :=
        _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeDerivLipschitzSeminorm_nonneg g
      linarith

private theorem scaled_mem_unitCube {k : ℤ} {j : ℕ} (hkj : k ≤ (j : ℤ))
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d k)) :
    (((3 : ℝ) ^ j)⁻¹) • x ∈ openCubeSet (originCube d 0) := by
  rw [mem_openCubeSet_originCube_iff] at hx ⊢
  intro i
  have h3j : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have hscale : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ (j : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) hkj
  have hxi := hx i
  simp only [Pi.smul_apply, smul_eq_mul, zpow_zero, mul_one]
  constructor
  · rw [← div_eq_inv_mul, lt_div_iff₀ h3j]
    calc
      -(1 / 2 : ℝ) * (3 : ℝ) ^ j ≤ -(1 / 2 : ℝ) * (3 : ℝ) ^ k := by
        exact mul_le_mul_of_nonpos_left hscale (by norm_num)
      _ < x i := hxi.1
  · rw [← div_eq_inv_mul, div_lt_iff₀ h3j]
    calc
      x i < (1 / 2 : ℝ) * (3 : ℝ) ^ k := hxi.2
      _ ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ j :=
        mul_le_mul_of_nonneg_left hscale (by norm_num)

private theorem norm_scaled_sub_le_zpow {k : ℤ} {j : ℕ} (_hkj : k ≤ (j : ℤ))
    {x y : Vec d} (hx : x ∈ openCubeSet (originCube d k))
    (hy : y ∈ openCubeSet (originCube d k)) :
    ‖(((3 : ℝ) ^ j)⁻¹) • y - (((3 : ℝ) ^ j)⁻¹) • x‖ ≤
      (3 : ℝ) ^ (k - (j : ℤ)) := by
  have h3j : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have hrhs : 0 ≤ (3 : ℝ) ^ (k - (j : ℤ)) := (zpow_pos (by norm_num) _).le
  rw [pi_norm_le_iff_of_nonneg hrhs]
  intro i
  have hxi := (mem_openCubeSet_originCube_iff.mp hx) i
  have hyi := (mem_openCubeSet_originCube_iff.mp hy) i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
  rw [abs_le]
  have hzpow : (3 : ℝ) ^ (k - (j : ℤ)) = ((3 : ℝ) ^ j)⁻¹ * (3 : ℝ) ^ k := by
    rw [← zpow_natCast, ← zpow_neg, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    ring
  rw [hzpow]
  constructor <;> nlinarith

/-- On a cube no larger than the shell's correlation scale, the shell
oscillation is controlled by the reverse-scaled `(g2)` gauge. -/
theorem shell_cubeOscillation_le_small
    (j : ℕ) (k : ℤ) (hkj : k ≤ (j : ℤ)) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    cubeOscillation k (omega j) ≤
      (3 : ℝ) ^ (k - (j : ℤ)) * translatedShellG2 j 0 omega := by
  refine cubeOscillation_le_of_forall k (omega j)
    (mul_nonneg (zpow_nonneg (by norm_num) _)
      (translatedShellG2_nonneg j 0 omega)) ?_
  intro x y hx hy
  let g := unscalePotential j (omega j)
  have hx' := scaled_mem_unitCube hkj hx
  have hy' := scaled_mem_unitCube hkj hy
  have hconv : Convex ℝ (openCubeSet (originCube d 0)) := convex_openCubeSet _
  have hmean := hconv.norm_image_sub_le_of_norm_fderiv_le
    (f := fun z : Vec d => g z)
    (fun z _ => (g.hasFDerivAt z).differentiableAt)
    (fun z hz => by
      rw [(g.hasFDerivAt z).fderiv]
      exact deriv_norm_le_g2Observable g hz)
    hx' hy'
  have hdist := norm_scaled_sub_le_zpow hkj hx hy
  have hg2 : 0 ≤ translatedShellG2 j 0 omega := translatedShellG2_nonneg _ _ _
  have hvalx : g ((((3 : ℝ) ^ j)⁻¹) • x) = omega j x := by
    simp only [g, unscalePotential,
      _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale_apply, smul_smul]
    rw [mul_inv_cancel₀ (by positivity : (3 : ℝ) ^ j ≠ 0), one_smul]
  have hvaly : g ((((3 : ℝ) ^ j)⁻¹) • y) = omega j y := by
    simp only [g, unscalePotential,
      _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale_apply, smul_smul]
    rw [mul_inv_cancel₀ (by positivity : (3 : ℝ) ^ j ≠ 0), one_smul]
  have htranslateZero :
      _root_.SubdiffusiveProcess.Model.PotentialField.translate (0 : Vec d) g = g := by
    apply _root_.SubdiffusiveProcess.Model.PotentialField.ext
    intro z
    simp
  have hgauge : translatedShellG2 j 0 omega =
      _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g := by
    rw [translatedShellG2]
    exact congrArg _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable htranslateZero
  change ‖g ((((3 : ℝ) ^ j)⁻¹) • y) -
      g ((((3 : ℝ) ^ j)⁻¹) • x)‖ ≤ _ at hmean
  rw [hvaly, hvalx, Real.norm_eq_abs, ← hgauge] at hmean
  calc
    omega j x - omega j y ≤ |omega j x - omega j y| := le_abs_self _
    _ = |omega j y - omega j x| := abs_sub_comm _ _
    _ ≤ translatedShellG2 j 0 omega *
        ‖(((3 : ℝ) ^ j)⁻¹) • y - (((3 : ℝ) ^ j)⁻¹) • x‖ := hmean
    _ ≤ translatedShellG2 j 0 omega * (3 : ℝ) ^ (k - (j : ℤ)) :=
      mul_le_mul_of_nonneg_left hdist hg2
    _ = (3 : ℝ) ^ (k - (j : ℤ)) * translatedShellG2 j 0 omega := mul_comm _ _

/-- The per-layer source estimate in the regime where the observation cube is
no larger than the shell scale. -/
theorem isBigOWith_gammaTwo_shell_cubeOscillation_small
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) (k : ℤ)
    (hkj : k ≤ (j : ℤ)) :
    IsBigOWith M.P.toMeasure (gammaSigma 2)
      (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => cubeOscillation k (omega j))
      ((3 : ℝ) ^ (k - (j : ℤ)) *
        ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) := by
  have hscale : 0 ≤ (3 : ℝ) ^ (k - (j : ℤ)) :=
    (zpow_pos (by norm_num) _).le
  exact ((isBigOWith_gammaTwo_translatedShellG2 M j 0).const_mul hscale).of_le
    (shell_cubeOscillation_le_small j k hkj)

/-! ## Finite cover of a large reverse-scaled cube -/


/-- Per-coordinate radius of a `1/3`-mesh cover of `cu_r` by translates of
`cu_0`. -/
def shellCoverRadius (r : ℤ) : ℕ := 3 ^ (r + 1).toNat

def shellCoverShifts (d : ℕ) (r : ℤ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ =>
    Finset.Icc (-(shellCoverRadius r : ℤ)) (shellCoverRadius r : ℤ)

def shellCoverCenter (p : Fin d → ℤ) : Vec d :=
  fun i => (3 : ℝ)⁻¹ * (p i : ℝ)

theorem shellCoverShifts_nonempty (d : ℕ) (r : ℤ) :
    (shellCoverShifts d r).Nonempty := by
  refine ⟨fun _ => 0, ?_⟩
  rw [shellCoverShifts, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  exact ⟨neg_nonpos.2 (Int.natCast_nonneg _), Int.natCast_nonneg _⟩

theorem card_shellCoverShifts (d : ℕ) (r : ℤ) :
    (shellCoverShifts d r).card = (2 * shellCoverRadius r + 1) ^ d := by
  have hcard : (shellCoverShifts d r).card =
      ∏ _i : Fin d,
        ((shellCoverRadius r : ℤ) + 1 - -(shellCoverRadius r : ℤ)).toNat := by
    simp only [shellCoverShifts, Fintype.card_piFinset, Int.card_Icc]
  rw [hcard, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

theorem shellCoverShifts_card_ge_two (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (r : ℤ) : 2 ≤ (shellCoverShifts d r).card := by
  rw [card_shellCoverShifts]
  have hR : 1 ≤ shellCoverRadius r := Nat.one_le_pow _ _ (by norm_num)
  have hd : 1 ≤ d := le_trans (by norm_num) M.shellPrefix.dimension
  have hbase : 2 ≤ 2 * shellCoverRadius r + 1 := by omega
  exact hbase.trans (Nat.le_pow hd)

theorem exists_shellCoverShift_mem {r : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d r)) :
    ∃ p ∈ shellCoverShifts d r,
      x ∈ translateSet (shellCoverCenter p) (openCubeSet (originCube d 0)) := by
  have hstep : (0 : ℝ) < (3 : ℝ)⁻¹ := inv_pos.mpr (by norm_num)
  have hR1 : (1 : ℝ) ≤ (shellCoverRadius r : ℝ) := by
    exact_mod_cast Nat.one_le_pow (r + 1).toNat 3 (by norm_num)
  have hRpow : (3 : ℝ) ^ (r + 1) ≤ (shellCoverRadius r : ℝ) := by
    have hcast : ((shellCoverRadius r : ℕ) : ℝ) =
        (3 : ℝ) ^ (((r + 1).toNat : ℕ) : ℤ) := by
      rw [zpow_natCast, shellCoverRadius]
      norm_cast
    rw [hcast]
    exact zpow_le_zpow_right₀ (by norm_num) (Int.self_le_toNat _)
  have hquot : ∀ i : Fin d,
      |x i / (3 : ℝ)⁻¹| < (1 / 2 : ℝ) * (3 : ℝ) ^ (r + 1) := by
    intro i
    have hxi := (mem_openCubeSet_originCube_iff.mp hx) i
    have habs : |x i| < (1 / 2 : ℝ) * (3 : ℝ) ^ r :=
      abs_lt.mpr ⟨by linarith [hxi.1], hxi.2⟩
    rw [abs_div, abs_of_pos hstep, div_lt_iff₀ hstep]
    have hpow : (1 / 2 : ℝ) * (3 : ℝ) ^ (r + 1) * (3 : ℝ)⁻¹ =
        (1 / 2 : ℝ) * (3 : ℝ) ^ r := by
      rw [show (3 : ℝ)⁻¹ = (3 : ℝ) ^ (-1 : ℤ) by rw [zpow_neg_one],
        mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 2
      ring
    rw [hpow]
    exact habs
  refine ⟨fun i => round (x i / (3 : ℝ)⁻¹), ?_, ?_⟩
  · rw [shellCoverShifts, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have ht := abs_lt.mp (hquot i)
    have hd := abs_le.mp (abs_sub_round (x i / (3 : ℝ)⁻¹))
    constructor
    · have hlow : -(shellCoverRadius r : ℝ) ≤
          ((round (x i / (3 : ℝ)⁻¹) : ℤ) : ℝ) := by linarith
      exact_mod_cast hlow
    · have hhigh : ((round (x i / (3 : ℝ)⁻¹) : ℤ) : ℝ) ≤
          (shellCoverRadius r : ℝ) := by linarith
      exact_mod_cast hhigh
  · rw [mem_translateSet_iff_sub_mem, mem_openCubeSet_originCube_iff]
    intro i
    have hd := abs_le.mp (abs_sub_round (x i / (3 : ℝ)⁻¹))
    have hcoord :
        (x - shellCoverCenter (fun i => round (x i / (3 : ℝ)⁻¹))) i =
          x i - (3 : ℝ)⁻¹ *
            ((round (x i / (3 : ℝ)⁻¹) : ℤ) : ℝ) := rfl
    have hmul : x i - (3 : ℝ)⁻¹ *
        ((round (x i / (3 : ℝ)⁻¹) : ℤ) : ℝ) =
        (3 : ℝ)⁻¹ * (x i / (3 : ℝ)⁻¹ -
          ((round (x i / (3 : ℝ)⁻¹) : ℤ) : ℝ)) := by
      field_simp
    rw [hcoord, hmul]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hd.1 hstep.le]
    · nlinarith [mul_le_mul_of_nonneg_left hd.2 hstep.le]

/-- Maximum of translated own-scale `(g2)` gauges covering the reverse-scaled
observation cube. -/
def largeCubeShellG2 (j : ℕ) (r : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  (shellCoverShifts d r).sup' (shellCoverShifts_nonempty d r) fun p =>
    translatedShellG2 j (shellCoverCenter p) omega

theorem largeCubeShellG2_nonneg (j : ℕ) (r : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ largeCubeShellG2 j r omega := by
  obtain ⟨p, hp⟩ := shellCoverShifts_nonempty d r
  exact (translatedShellG2_nonneg j (shellCoverCenter p) omega).trans
    (Finset.le_sup' (fun q => translatedShellG2 j (shellCoverCenter q) omega) hp)

theorem measurable_largeCubeShellG2 (j : ℕ) (r : ℤ) :
    Measurable (largeCubeShellG2 (d := d) j r) := by
  let Y : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
    (shellCoverShifts d r).sup' (shellCoverShifts_nonempty d r) fun p =>
      translatedShellG2 j (shellCoverCenter p)
  have hY : Measurable Y := Finset.measurable_sup' (shellCoverShifts_nonempty d r)
    (fun p _ => measurable_translatedShellG2 j (shellCoverCenter p))
  have heq : Y = largeCubeShellG2 j r := by
    funext omega
    exact Finset.sup'_apply (shellCoverShifts_nonempty d r)
      (fun p => translatedShellG2 j (shellCoverCenter p)) omega
  rwa [← heq]

theorem abs_unscalePotential_apply_le_largeCubeShellG2
    (j : ℕ) (r : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d r)) :
    |unscalePotential j (omega j) x| ≤ largeCubeShellG2 j r omega := by
  obtain ⟨p, hp, hmem⟩ := exists_shellCoverShift_mem hx
  rw [mem_translateSet_iff_sub_mem] at hmem
  have hpoint := _root_.SubdiffusiveProcess.Model.PotentialField.abs_apply_le_g2Observable
    (_root_.SubdiffusiveProcess.Model.PotentialField.translate (shellCoverCenter p)
      (unscalePotential j (omega j))) hmem
  have heval :
      _root_.SubdiffusiveProcess.Model.PotentialField.translate (shellCoverCenter p)
          (unscalePotential j (omega j)) (x - shellCoverCenter p) =
        unscalePotential j (omega j) x := by
    simp only [_root_.SubdiffusiveProcess.Model.PotentialField.translate_apply, sub_add_cancel]
  rw [heval] at hpoint
  exact hpoint.trans (Finset.le_sup'
    (fun q => translatedShellG2 j (shellCoverCenter q) omega) hp)

theorem isBigOWith_gammaTwo_largeCubeShellG2
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) (r : ℤ) :
    IsBigOWith M.P.toMeasure (gammaSigma 2) (largeCubeShellG2 j r)
      (((3 * Real.log ((shellCoverShifts d r).card : ℝ)) ^ (2 : ℝ)⁻¹) *
        ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) := by
  exact isBigOWith_gammaSigma_finset_sup'
    (μ := M.P.toMeasure) (shellCoverShifts d r) (shellCoverShifts_nonempty d r)
    (by norm_num) (shellCoverShifts_card_ge_two M r)
    (fun p _ => isBigOWith_gammaTwo_translatedShellG2 M j (shellCoverCenter p))

/-- On a cube larger than the shell scale, the literal oscillation is bounded
by twice the finite-cover maximum of local `(g2)` gauges. -/
theorem shell_cubeOscillation_le_large
    (j : ℕ) (k : ℤ) (_hjk : (j : ℤ) < k) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    cubeOscillation k (omega j) ≤
      2 * largeCubeShellG2 j (k - (j : ℤ)) omega := by
  refine cubeOscillation_le_of_forall k (omega j)
    (mul_nonneg (by norm_num) (largeCubeShellG2_nonneg j _ omega)) ?_
  intro x y hx hy
  let g := unscalePotential j (omega j)
  let x' : Vec d := (((3 : ℝ) ^ j)⁻¹) • x
  let y' : Vec d := (((3 : ℝ) ^ j)⁻¹) • y
  have hx' : x' ∈ openCubeSet (originCube d (k - (j : ℤ))) := by
    rw [mem_openCubeSet_originCube_iff] at hx ⊢
    intro i
    have h3j : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
    have hpow : (3 : ℝ) ^ (k - (j : ℤ)) =
        ((3 : ℝ) ^ j)⁻¹ * (3 : ℝ) ^ k := by
      rw [← zpow_natCast, ← zpow_neg, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 1
      ring
    have hxi := hx i
    have hinv : (0 : ℝ) < ((3 : ℝ) ^ j)⁻¹ := inv_pos.mpr h3j
    have hlo := mul_lt_mul_of_pos_left hxi.1 hinv
    have hhi := mul_lt_mul_of_pos_left hxi.2 hinv
    simp only [x', Pi.smul_apply, smul_eq_mul]
    rw [hpow]
    constructor <;> nlinarith
  have hy' : y' ∈ openCubeSet (originCube d (k - (j : ℤ))) := by
    rw [mem_openCubeSet_originCube_iff] at hy ⊢
    intro i
    have hpow : (3 : ℝ) ^ (k - (j : ℤ)) =
        ((3 : ℝ) ^ j)⁻¹ * (3 : ℝ) ^ k := by
      rw [← zpow_natCast, ← zpow_neg, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 1
      ring
    have hyi := hy i
    have h3j : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
    have hinv : (0 : ℝ) < ((3 : ℝ) ^ j)⁻¹ := inv_pos.mpr h3j
    have hlo := mul_lt_mul_of_pos_left hyi.1 hinv
    have hhi := mul_lt_mul_of_pos_left hyi.2 hinv
    simp only [y', Pi.smul_apply, smul_eq_mul]
    rw [hpow]
    constructor <;> nlinarith
  have hgX := abs_unscalePotential_apply_le_largeCubeShellG2 j _ omega hx'
  have hgY := abs_unscalePotential_apply_le_largeCubeShellG2 j _ omega hy'
  have hvalx : g x' = omega j x := by
    simp only [g, x', unscalePotential,
      _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale_apply, smul_smul]
    rw [mul_inv_cancel₀ (by positivity : (3 : ℝ) ^ j ≠ 0), one_smul]
  have hvaly : g y' = omega j y := by
    simp only [g, y', unscalePotential,
      _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale_apply, smul_smul]
    rw [mul_inv_cancel₀ (by positivity : (3 : ℝ) ^ j ≠ 0), one_smul]
  rw [hvalx] at hgX
  rw [hvaly] at hgY
  linarith [le_abs_self (omega j x), neg_le_of_abs_le hgY]

/-- Exact large-cube per-layer estimate before the cover cardinality is
absorbed into the dimensional constant. -/
theorem isBigOWith_gammaTwo_shell_cubeOscillation_large_raw
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) (k : ℤ)
    (hjk : (j : ℤ) < k) :
    IsBigOWith M.P.toMeasure (gammaSigma 2)
      (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => cubeOscillation k (omega j))
      (2 * (((3 * Real.log
          ((shellCoverShifts d (k - (j : ℤ))).card : ℝ)) ^ (2 : ℝ)⁻¹) *
        ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta))) := by
  exact ((isBigOWith_gammaTwo_largeCubeShellG2 M j (k - (j : ℤ))).const_mul
    (by norm_num)).of_le (shell_cubeOscillation_le_large j k hjk)

/-- Dimensional logarithmic cover constant. -/
def shellCoverLogConst : ℝ := 3 * (1 + 3 * Real.log 3)

theorem shellCoverLogConst_pos : 0 < shellCoverLogConst := by
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [shellCoverLogConst]
  linarith

/-- The cover's Gaussian maximum cost is at most a dimensional constant times
`3^r`. -/
theorem shellCover_gaussianFactor_le_sqrt
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {r : ℤ} (hr : 0 < r) :
    (3 * Real.log ((shellCoverShifts d r).card : ℝ)) ^ (2 : ℝ)⁻¹ ≤
      Real.sqrt (shellCoverLogConst * (d : ℝ)) * Real.sqrt (r : ℝ) := by
  have hd : 1 ≤ d := le_trans (by norm_num) M.shellPrefix.dimension
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hrZ : (1 : ℤ) ≤ r := by omega
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrZ
  have hRpos : 1 ≤ 3 ^ (r + 1).toNat := Nat.one_le_pow _ _ (by norm_num)
  have hle : 2 * 3 ^ (r + 1).toNat + 1 ≤ 3 ^ ((r + 1).toNat + 1) := by
    rw [pow_succ]
    omega
  have heZ : (((r + 1).toNat : ℕ) : ℤ) = r + 1 :=
    Int.toNat_of_nonneg (by omega)
  have heR : (((r + 1).toNat : ℕ) : ℝ) = (r : ℝ) + 1 := by
    exact_mod_cast heZ
  have hcard : ((shellCoverShifts d r).card : ℝ) =
      ((2 * 3 ^ (r + 1).toNat + 1 : ℕ) : ℝ) ^ d := by
    rw [card_shellCoverShifts, shellCoverRadius, Nat.cast_pow]
  have hposbase : (0 : ℝ) < ((2 * 3 ^ (r + 1).toNat + 1 : ℕ) : ℝ) := by
    positivity
  have hmono : Real.log ((2 * 3 ^ (r + 1).toNat + 1 : ℕ) : ℝ) ≤
      Real.log (((3 : ℕ) ^ ((r + 1).toNat + 1) : ℕ) : ℝ) :=
    Real.log_le_log hposbase (by exact_mod_cast hle)
  have hpow : Real.log (((3 : ℕ) ^ ((r + 1).toNat + 1) : ℕ) : ℝ) =
      ((((r + 1).toNat : ℕ) : ℝ) + 1) * Real.log 3 := by
    have hc : ((((3 : ℕ) ^ ((r + 1).toNat + 1) : ℕ)) : ℝ) =
        (3 : ℝ) ^ ((r + 1).toNat + 1) := by norm_cast
    rw [hc, Real.log_pow]
    push_cast
    ring
  have hstep : Real.log ((2 * 3 ^ (r + 1).toNat + 1 : ℕ) : ℝ) ≤
      ((r : ℝ) + 2) * Real.log 3 := by
    calc
      Real.log ((2 * 3 ^ (r + 1).toNat + 1 : ℕ) : ℝ) ≤
          Real.log (((3 : ℕ) ^ ((r + 1).toNat + 1) : ℕ) : ℝ) := hmono
      _ = ((((r + 1).toNat : ℕ) : ℝ) + 1) * Real.log 3 := hpow
      _ = ((r : ℝ) + 2) * Real.log 3 := by rw [heR]; ring
  have hthree : ((r : ℝ) + 2) * Real.log 3 ≤
      (r : ℝ) * (3 * Real.log 3) := by
    nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)]
  have hlog : 3 * Real.log ((shellCoverShifts d r).card : ℝ) ≤
      shellCoverLogConst * (d : ℝ) * (r : ℝ) := by
    rw [hcard, Real.log_pow, shellCoverLogConst]
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
    have hraw := mul_le_mul_of_nonneg_left (hstep.trans hthree) hd0
    have hdr : 0 ≤ (d : ℝ) * (r : ℝ) :=
      mul_nonneg hd0 (zero_le_one.trans hrR)
    nlinarith [hraw]
  have hCd : 0 ≤ shellCoverLogConst * (d : ℝ) :=
    mul_nonneg shellCoverLogConst_pos.le (by positivity)
  have hsqrtRaw :
      Real.sqrt (3 * Real.log ((shellCoverShifts d r).card : ℝ)) ≤
        Real.sqrt (shellCoverLogConst * (d : ℝ) * (r : ℝ)) :=
    Real.sqrt_le_sqrt hlog
  have hsqrtMul :
      Real.sqrt (shellCoverLogConst * (d : ℝ) * (r : ℝ)) =
        Real.sqrt (shellCoverLogConst * (d : ℝ)) * Real.sqrt (r : ℝ) := by
    exact Real.sqrt_mul hCd _
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by ring, ← Real.sqrt_eq_rpow]
  rwa [hsqrtMul] at hsqrtRaw

theorem shellCover_gaussianFactor_le (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {r : ℤ} (hr : 0 < r) :
    (3 * Real.log ((shellCoverShifts d r).card : ℝ)) ^ (2 : ℝ)⁻¹ ≤
      Real.sqrt (shellCoverLogConst * (d : ℝ)) * (3 : ℝ) ^ r := by
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast (show (1 : ℤ) ≤ r by omega)
  have hsqrtR : Real.sqrt (r : ℝ) ≤ (r : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  have nat_le_three_pow : ∀ n : ℕ, n ≤ 3 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      have hp : 1 ≤ 3 ^ n := Nat.one_le_pow n 3 (by norm_num)
      omega
  have hnat : r.toNat ≤ 3 ^ r.toNat := nat_le_three_pow r.toNat
  have hrpow : (r : ℝ) ≤ (3 : ℝ) ^ r := by
    have hrnat : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hr.le
    have hcast : ((3 ^ r.toNat : ℕ) : ℝ) = (3 : ℝ) ^ r := by
      rw [← hrnat, zpow_natCast]
      norm_cast
    have hrreal : (r : ℝ) = (r.toNat : ℝ) := by exact_mod_cast hrnat.symm
    rw [hrreal, ← hcast]
    exact_mod_cast hnat
  have hroot : Real.sqrt (r : ℝ) ≤ (3 : ℝ) ^ r := hsqrtR.trans hrpow
  exact (shellCover_gaussianFactor_le_sqrt M hr).trans
    (mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _))

/-- Measurable per-layer envelope used to take the infinite cutoff supremum. -/
def shellOscillationEnvelope (j : ℕ) (k : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  if k ≤ (j : ℤ) then
    (3 : ℝ) ^ (k - (j : ℤ)) * translatedShellG2 j 0 omega
  else
    2 * largeCubeShellG2 j (k - (j : ℤ)) omega

theorem measurable_shellOscillationEnvelope (j : ℕ) (k : ℤ) :
    Measurable (shellOscillationEnvelope (d := d) j k) := by
  by_cases h : k ≤ (j : ℤ)
  · change Measurable (fun omega => if k ≤ (j : ℤ) then
        (3 : ℝ) ^ (k - (j : ℤ)) * translatedShellG2 j 0 omega else _)
    simpa only [h, ite_true, Pi.mul_def] using!
      measurable_const.mul (measurable_translatedShellG2 j 0)
  · change Measurable (fun omega => if k ≤ (j : ℤ) then _ else
        2 * largeCubeShellG2 j (k - (j : ℤ)) omega)
    simpa only [h, ite_false, Pi.mul_def] using!
      measurable_const.mul (measurable_largeCubeShellG2 j (k - (j : ℤ)))

theorem shellOscillationEnvelope_nonneg (j : ℕ) (k : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ shellOscillationEnvelope j k omega := by
  by_cases h : k ≤ (j : ℤ)
  · rw [shellOscillationEnvelope, ite_eq_left h]
    exact mul_nonneg (zpow_nonneg (by norm_num) _)
      (translatedShellG2_nonneg j 0 omega)
  · rw [shellOscillationEnvelope, ite_eq_right h]
    exact mul_nonneg (by norm_num) (largeCubeShellG2_nonneg j _ omega)

theorem cubeOscillation_le_shellOscillationEnvelope
    (j : ℕ) (k : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    cubeOscillation k (omega j) ≤ shellOscillationEnvelope j k omega := by
  by_cases h : k ≤ (j : ℤ)
  · simpa [shellOscillationEnvelope, h] using shell_cubeOscillation_le_small j k h omega
  · have hjk : (j : ℤ) < k := lt_of_not_ge h
    simpa [shellOscillationEnvelope, h] using shell_cubeOscillation_le_large j k hjk omega

theorem isBigOWith_gammaTwo_shellOscillationEnvelope
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) (k : ℤ) :
    IsBigOWith M.P.toMeasure (gammaSigma 2)
      (shellOscillationEnvelope j k)
      ((2 * max 1 (Real.sqrt (shellCoverLogConst * (d : ℝ)))) *
        (3 : ℝ) ^ (k - (j : ℤ)) *
          ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) := by
  by_cases h : k ≤ (j : ℤ)
  · change IsBigOWith M.P.toMeasure (gammaSigma 2)
      (fun omega => if k ≤ (j : ℤ) then
        (3 : ℝ) ^ (k - (j : ℤ)) * translatedShellG2 j 0 omega else _) _
    simp only [h, ite_true]
    refine ((isBigOWith_gammaTwo_translatedShellG2 M j 0).const_mul
      (zpow_nonneg (by norm_num) _)).mono_scale ?_
    have hfactor : (1 : ℝ) ≤
        2 * max 1 (Real.sqrt (shellCoverLogConst * (d : ℝ))) := by
      have := le_max_left (1 : ℝ) (Real.sqrt (shellCoverLogConst * (d : ℝ)))
      linarith
    have hz : 0 ≤ (3 : ℝ) ^ (k - (j : ℤ)) := (zpow_pos (by norm_num) _).le
    have hb : 0 ≤ (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta :=
      mul_nonneg (Real.rpow_nonneg (by
        have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        linarith) _) M.shellPrefix.delta_pos.le
    calc
      (3 : ℝ) ^ (k - (j : ℤ)) *
          ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) =
          1 * ((3 : ℝ) ^ (k - (j : ℤ)) *
            ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) := by ring
      _ ≤ (2 * max 1 (Real.sqrt (shellCoverLogConst * (d : ℝ)))) *
          ((3 : ℝ) ^ (k - (j : ℤ)) *
            ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) :=
        mul_le_mul_of_nonneg_right hfactor (mul_nonneg hz hb)
      _ = _ := by ring
  · have hjk : (j : ℤ) < k := lt_of_not_ge h
    change IsBigOWith M.P.toMeasure (gammaSigma 2)
      (fun omega => if k ≤ (j : ℤ) then _ else
        2 * largeCubeShellG2 j (k - (j : ℤ)) omega) _
    simp only [h, ite_false]
    refine ((isBigOWith_gammaTwo_largeCubeShellG2 M j (k - (j : ℤ))).const_mul
      (by norm_num)).mono_scale ?_
    have hcover := shellCover_gaussianFactor_le M (sub_pos.mpr hjk)
    have hmax : Real.sqrt (shellCoverLogConst * (d : ℝ)) ≤
        max 1 (Real.sqrt (shellCoverLogConst * (d : ℝ))) := le_max_right _ _
    have hb : 0 ≤ (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta :=
      mul_nonneg (Real.rpow_nonneg (by
        have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        linarith) _) M.shellPrefix.delta_pos.le
    have hz : 0 ≤ (3 : ℝ) ^ (k - (j : ℤ)) := (zpow_pos (by norm_num) _).le
    calc
      2 * (((3 * Real.log
          ((shellCoverShifts d (k - (j : ℤ))).card : ℝ)) ^ (2 : ℝ)⁻¹) *
        ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) ≤
          2 * ((Real.sqrt (shellCoverLogConst * (d : ℝ)) *
            (3 : ℝ) ^ (k - (j : ℤ))) *
              ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) := by gcongr
      _ ≤ 2 * ((max 1 (Real.sqrt (shellCoverLogConst * (d : ℝ))) *
            (3 : ℝ) ^ (k - (j : ℤ))) *
              ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) := by gcongr
      _ = _ := by ring

/-- Source-shaped per-layer estimate, valid in both cube-size regimes. -/
theorem isBigOWith_gammaTwo_shell_cubeOscillation
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) (k : ℤ) :
    IsBigOWith M.P.toMeasure (gammaSigma 2)
      (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => cubeOscillation k (omega j))
      ((2 * max 1 (Real.sqrt (shellCoverLogConst * (d : ℝ)))) *
        (3 : ℝ) ^ (k - (j : ℤ)) *
          ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) :=
  (isBigOWith_gammaTwo_shellOscillationEnvelope M j k).of_le
    (cubeOscillation_le_shellOscillationEnvelope j k)

/-! ## Countable Orlicz assembly -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}


/-- Continuity from below for upper tails of a nonnegative series. -/
theorem isBigOWith_tsum_of_partial_sums [IsFiniteMeasure μ]
    {Psi : ℝ → ℝ} {X : ℕ → Ω → ℝ} {A : ℝ}
    (hX_nonneg : ∀ n omega, 0 ≤ X n omega)
    (hpartial : ∀ N : ℕ,
      IsBigOWith μ Psi (fun omega => ∑ n ∈ Finset.range (N + 1), X n omega) A) :
    IsBigOWith μ Psi (fun omega => ∑' n, X n omega) A := by
  intro t ht
  have hPsi : (0 : ℝ) ≤ (Psi t)⁻¹ :=
    le_trans measureReal_nonneg (hpartial 0 ht)
  have hmono : Monotone fun N : ℕ =>
      upperTailEvent (fun omega => ∑ n ∈ Finset.range (N + 1), X n omega) (A * t) := by
    intro N L hNL omega homega
    simp only [mem_upperTailEvent] at homega ⊢
    exact homega.trans_le (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.2 (Nat.succ_le_succ hNL))
      (fun i _ _ => hX_nonneg i omega))
  have hsubset : upperTailEvent (fun omega => ∑' n, X n omega) (A * t) ⊆
      ⋃ N : ℕ, upperTailEvent
        (fun omega => ∑ n ∈ Finset.range (N + 1), X n omega) (A * t) := by
    intro omega homega
    simp only [mem_upperTailEvent] at homega
    obtain ⟨N, hN⟩ : ∃ N : ℕ, A * t < ∑ n ∈ Finset.range N, X n omega := by
      by_contra h
      push Not at h
      exact absurd homega
        (not_lt.2 (Real.tsum_le_of_sum_range_le (fun n => hX_nonneg n omega) h))
    exact Set.mem_iUnion.2 ⟨N, by
      simp only [mem_upperTailEvent]
      exact hN.trans_le (by
        rw [Finset.sum_range_succ]
        exact le_add_of_nonneg_right (hX_nonneg N omega))⟩
  have hbound : ∀ N : ℕ,
      μ (upperTailEvent
        (fun omega => ∑ n ∈ Finset.range (N + 1), X n omega) (A * t)) ≤
        ENNReal.ofReal ((Psi t)⁻¹) := fun N =>
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hPsi).2 (hpartial N ht)
  have hmeasure : μ (upperTailEvent (fun omega => ∑' n, X n omega) (A * t)) ≤
      ENNReal.ofReal ((Psi t)⁻¹) := by
    refine (measure_mono hsubset).trans ?_
    rw [hmono.measure_iUnion]
    exact iSup_le hbound
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  rwa [ENNReal.toReal_ofReal hPsi] at hreal


/-- Countable generalized triangle inequality, assembled from
CoarseGraining's finite-family theorem. -/
theorem isBigOWith_gammaSigma_tsum_nonneg [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} {a : ℕ → ℝ} {sigma : ℝ}
    (hsigma : 0 < sigma) (hX_nonneg : ∀ n omega, 0 ≤ X n omega)
    (hX_meas : ∀ n, Measurable (X n)) (ha : ∀ n, 0 < a n)
    (ha_sum : Summable a)
    (hX : ∀ n, IsBigOWith μ (gammaSigma sigma) (X n) (a n)) :
    IsBigOWith μ (gammaSigma sigma) (fun omega => ∑' n, X n omega)
      (gammaTriangleConst sigma * ∑' n, a n) := by
  have hC : 0 < gammaTriangleConst sigma := gammaTriangleConst_pos
  refine isBigOWith_tsum_of_partial_sums hX_nonneg fun N => ?_
  have hs : (Finset.range (N + 1)).Nonempty := Finset.nonempty_range_iff.2 (by omega)
  have hsymm : ∀ n, IsBigO μ (gammaSigma sigma) (X n) (a n) := by
    intro n
    simpa [IsBigO, abs_of_nonneg (hX_nonneg n _)] using hX n
  have hfinite := isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := μ) (Finset.range (N + 1)) (X := X) (a := a) (σ := sigma)
    hsigma hs (fun n _ => ha n) (fun n _ => hsymm n) (fun n _ => hX_meas n)
  have hwith : IsBigOWith μ (gammaSigma sigma)
      (fun omega => ∑ n ∈ Finset.range (N + 1), X n omega)
      (gammaTriangleConst sigma * ∑ n ∈ Finset.range (N + 1), a n) := by
    simpa [IsBigO, abs_of_nonneg (Finset.sum_nonneg fun n _ => hX_nonneg n _)]
      using hfinite
  refine hwith.mono_scale (mul_le_mul_of_nonneg_left ?_ hC.le)
  exact ha_sum.sum_le_tsum _ fun n _ => (ha n).le


/-- Summable positive `Gamma_sigma` scales force pointwise summability almost
everywhere. -/
theorem ae_summable_of_isBigOWith_gammaSigma
    [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} {a : ℕ → ℝ} {sigma : ℝ}
    (hsigma : 0 < sigma) (hX_nonneg : ∀ n omega, 0 ≤ X n omega)
    (hX_meas : ∀ n, AEMeasurable (X n) μ) (ha : ∀ n, 0 < a n)
    (ha_sum : Summable a)
    (hX : ∀ n, IsBigOWith μ (gammaSigma sigma) (X n) (a n)) :
    ∀ᵐ omega ∂μ, Summable fun n => X n omega := by
  have hInt : ∀ n, Integrable (X n) μ := by
    intro n
    have h := integrable_rpow_of_isBigOWith_gammaSigma
      (μ := μ) (Y := X n) (K := a n) (σ := sigma) (p := 1)
      hsigma (ha n) (by norm_num) (hX_nonneg n) (hX_meas n) (hX n)
    simpa only [Real.rpow_one] using h
  have hmean : ∀ n, ∫ omega, ‖X n omega‖ ∂μ ≤ gammaMomentConst sigma * a n := by
    intro n
    have h := integral_rpow_le_of_isBigOWith_gammaSigma
      (μ := μ) (Y := X n) (K := a n) (σ := sigma) (p := 1)
      hsigma (ha n) (by norm_num) (hX_nonneg n) (hX_meas n) (hX n)
    have heq : (fun omega => ‖X n omega‖) = X n := by
      funext omega
      exact Real.norm_of_nonneg (hX_nonneg n omega)
    rw [heq]
    simpa only [Real.rpow_one, Real.one_rpow, mul_one] using h
  have hmeanSum : Summable fun n => ∫ omega, ‖X n omega‖ ∂μ := by
    refine Summable.of_nonneg_of_le
      (fun n => integral_nonneg fun _ => norm_nonneg _) hmean ?_
    exact ha_sum.mul_left (gammaMomentConst sigma)
  have hlin : (∑' n, ∫⁻ omega, ‖X n omega‖ₑ ∂μ) ≠ (⊤ : ENNReal) := by
    have heq (n : ℕ) : ∫⁻ omega, ‖X n omega‖ₑ ∂μ =
        ‖∫ omega, ‖X n omega‖ ∂μ‖ₑ := by
      dsimp [enorm]
      rw [lintegral_coe_eq_integral _ (hInt n).norm, ENNReal.coe_nnreal_eq]
      congr 1
      rw [coe_nnnorm, Real.norm_eq_abs,
        abs_of_nonneg (integral_nonneg fun omega => by
          simp [abs_nonneg (X n omega)])]
      rfl
    rw [funext heq]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2
      (NNReal.summable_coe.1 hmeanSum.abs)
  have htotal : ∫⁻ omega, ∑' n, ‖X n omega‖ₑ ∂μ ≠ (⊤ : ENNReal) := by
    rw [lintegral_tsum fun n => (hInt n).1.enorm]
    exact hlin
  refine (ae_lt_top' (AEMeasurable.tsum fun n => (hInt n).1.enorm)
    htotal).mono ?_
  intro omega homega
  have hs : Summable fun n => ((‖X n omega‖₊ : NNReal) : ℝ) := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    simpa only [enorm_eq_nnnorm] using homega.ne
  simpa only [coe_nnnorm, Real.norm_of_nonneg (hX_nonneg _ omega)] using hs

/-! ## Infinite shell stream -/

/-- The `i`th shell above cutoff `n`. -/
def sensitivityShellIndex (n i : ℕ) : ℕ := n + 1 + i

def sensitivityLayer (n : ℕ) (k : ℤ) (i : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  shellOscillationEnvelope (sensitivityShellIndex n i) k omega

def sensitivityLayerConst (d : ℕ) : ℝ :=
  2 * max 1 (Real.sqrt (shellCoverLogConst * (d : ℝ)))

def sensitivityLayerStartScale
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ) (k : ℤ) : ℝ :=
  sensitivityLayerConst d * (3 : ℝ) ^ (k - ((n + 1 : ℕ) : ℤ)) *
    ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)

def sensitivityLayerScale
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ) (k : ℤ) (i : ℕ) : ℝ :=
  sensitivityLayerStartScale M n k * (1 / 3 : ℝ) ^ i

theorem sensitivityLayerStartScale_pos
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ) (k : ℤ) :
    0 < sensitivityLayerStartScale M n k := by
  unfold sensitivityLayerStartScale sensitivityLayerConst
  have hmax : 0 < max 1 (Real.sqrt (shellCoverLogConst * (d : ℝ))) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  exact mul_pos (mul_pos (mul_pos (by positivity) hmax) (zpow_pos (by norm_num) _))
    (mul_pos (Real.rpow_pos_of_pos (by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith) _) M.shellPrefix.delta_pos)

theorem sensitivityLayerScale_pos
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ) (k : ℤ) (i : ℕ) :
    0 < sensitivityLayerScale M n k i := by
  exact mul_pos (sensitivityLayerStartScale_pos M n k) (pow_pos (by norm_num) _)

private theorem sensitivity_zpow_eq (n i : ℕ) (k : ℤ) :
    (3 : ℝ) ^ (k - (sensitivityShellIndex n i : ℤ)) =
      (3 : ℝ) ^ (k - ((n + 1 : ℕ) : ℤ)) * (1 / 3 : ℝ) ^ i := by
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  rw [show (1 / 3 : ℝ) ^ i = (3 : ℝ) ^ (-(i : ℤ)) by
    rw [zpow_neg, zpow_natCast]
    rw [one_div, inv_pow]]
  rw [← zpow_add₀ h3]
  congr 1
  simp only [sensitivityShellIndex]
  omega

theorem isBigOWith_gammaTwo_sensitivityLayer
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ) (k : ℤ) (i : ℕ) :
    IsBigOWith M.P.toMeasure (gammaSigma 2) (sensitivityLayer n k i)
      (sensitivityLayerScale M n k i) := by
  have h := isBigOWith_gammaTwo_shellOscillationEnvelope M
    (sensitivityShellIndex n i) k
  change IsBigOWith M.P.toMeasure (gammaSigma 2)
    (shellOscillationEnvelope (sensitivityShellIndex n i) k)
    (sensitivityLayerScale M n k i)
  convert h using 1
  unfold sensitivityLayerScale sensitivityLayerStartScale sensitivityLayerConst
  rw [sensitivity_zpow_eq]
  ring

theorem summable_sensitivityLayerScale
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ) (k : ℤ) :
    Summable (sensitivityLayerScale M n k) := by
  unfold sensitivityLayerScale
  exact (summable_geometric_of_norm_lt_one (show ‖(1 / 3 : ℝ)‖ < 1 by norm_num)).mul_left _

theorem tsum_sensitivityLayerScale
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ) (k : ℤ) :
    ∑' i, sensitivityLayerScale M n k i =
      max 1 (Real.sqrt (shellCoverLogConst * (d : ℝ))) *
        (3 : ℝ) ^ (k - (n : ℤ)) *
          ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) := by
  rw [show (∑' i : ℕ, sensitivityLayerScale M n k i) =
      sensitivityLayerStartScale M n k * ∑' i : ℕ, (1 / 3 : ℝ) ^ i by
    simpa only [sensitivityLayerScale] using
      (tsum_mul_left : (∑' i : ℕ,
        sensitivityLayerStartScale M n k * (1 / 3 : ℝ) ^ i) = _)]
  rw [tsum_geometric_of_norm_lt_one (show ‖(1 / 3 : ℝ)‖ < 1 by norm_num)]
  unfold sensitivityLayerStartScale sensitivityLayerConst
  have hpow : (3 : ℝ) ^ (k - ((n + 1 : ℕ) : ℤ)) * (1 - 1 / 3 : ℝ)⁻¹ =
      (1 / 2 : ℝ) * (3 : ℝ) ^ (k - (n : ℤ)) := by
    rw [show (1 - 1 / 3 : ℝ)⁻¹ = 3 / 2 by norm_num]
    have h3 : (3 : ℝ) ≠ 0 := by norm_num
    rw [show k - ((n + 1 : ℕ) : ℤ) = k - (n : ℤ) - 1 by omega,
      zpow_sub_one₀ h3]
    field_simp
  calc
    2 * max 1 (Real.sqrt (shellCoverLogConst * (d : ℝ))) *
        (3 : ℝ) ^ (k - ((n + 1 : ℕ) : ℤ)) *
          ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) * (1 - 1 / 3 : ℝ)⁻¹ =
        2 * max 1 (Real.sqrt (shellCoverLogConst * (d : ℝ))) *
          ((3 : ℝ) ^ (k - ((n + 1 : ℕ) : ℤ)) * (1 - 1 / 3 : ℝ)⁻¹) *
            ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) := by ring
    _ = _ := by rw [hpow]; ring

/-- Dimensional constant in `e.sensitivity.field`. -/
def shellSensitivityConst (d : ℕ) : ℝ :=
  gammaTriangleConst 2 *
    max 1 (Real.sqrt (shellCoverLogConst * (d : ℝ))) *
      (1 + Real.log 2) ^ (2 : ℝ)⁻¹

theorem shellSensitivityConst_pos (d : ℕ) : 0 < shellSensitivityConst d := by
  unfold shellSensitivityConst
  exact mul_pos (mul_pos gammaTriangleConst_pos
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
    (Real.rpow_pos_of_pos (by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith) _)

/-- The infinite measurable envelope has the source's geometric `Gamma_2`
scale. -/
theorem isBigOWith_gammaTwo_sensitivityLayer_tsum
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ) (k : ℤ) :
    IsBigOWith M.P.toMeasure (gammaSigma 2)
      (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => ∑' i, sensitivityLayer n k i omega)
      (shellSensitivityConst d * M.delta * (3 : ℝ) ^ (k - (n : ℤ))) := by
  have h := isBigOWith_gammaSigma_tsum_nonneg (μ := M.P.toMeasure)
    (sigma := 2) (X := sensitivityLayer (d := d) n k)
    (a := sensitivityLayerScale M n k) (by norm_num)
    (fun i omega => shellOscillationEnvelope_nonneg _ _ _)
    (fun i => (measurable_shellOscillationEnvelope _ _))
    (sensitivityLayerScale_pos M n k) (summable_sensitivityLayerScale M n k)
    (isBigOWith_gammaTwo_sensitivityLayer M n k)
  rw [tsum_sensitivityLayerScale] at h
  convert h using 1
  unfold shellSensitivityConst
  ring


/-- A countable sum of nonnegative a.e.-measurable real functions is
a.e.-measurable, without a pointwise summability premise. -/
theorem aemeasurable_tsum_of_nonneg {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ i, AEMeasurable (X i) μ)
    (hX_nonneg : ∀ i omega, 0 ≤ X i omega) :
    AEMeasurable (fun omega => ∑' i, X i omega) μ := by
  have hnn :=
    (AEMeasurable.tsum (L := .unconditional ℕ) fun i =>
      (hX_meas i).real_toNNReal).coe_nnreal_real
  convert hnn using 1
  funext omega
  rw [NNReal.coe_tsum]
  apply tsum_congr
  intro i
  exact (Real.coe_toNNReal _ (hX_nonneg i omega)).symm

theorem ae_summable_sensitivityLayer
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ) (k : ℤ) :
    ∀ᵐ omega ∂M.P.toMeasure, Summable fun i => sensitivityLayer n k i omega :=
  ae_summable_of_isBigOWith_gammaSigma (μ := M.P.toMeasure) (sigma := 2)
    (by norm_num) (fun i omega => shellOscillationEnvelope_nonneg _ _ _)
    (fun i => (measurable_shellOscillationEnvelope _ _).aemeasurable)
    (sensitivityLayerScale_pos M n k) (summable_sensitivityLayerScale M n k)
    (isBigOWith_gammaTwo_sensitivityLayer M n k)

/-! ## The literal infinite-cutoff field oscillation -/

/-- The source's field oscillation, with both the cutoff supremum and the
spatial all-pairs supremum kept literal.  The `ENNReal` carrier is deliberate:
the source does not provide a global boundedness hypothesis before the
probabilistic estimate is proved. -/
noncomputable def cutoffLogRatioOscillationSup (n : ℕ) (k : ℤ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ≥0∞ :=
  ⨆ m : ℕ, ⨆ _h : n ≤ m,
    ENNReal.ofReal (cubeOscillation k
      (fun x => cutoffShellSum m (n : ℤ) x omega))

/-- Measurable majorant used as the real representative of the literal
infinite cutoff supremum. -/
noncomputable def sensitivityFieldRepresentative (n : ℕ) (k : ℤ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  ∑' i, sensitivityLayer n k i omega

/-- Literal multiplicative oscillation from
`e.infraredhom.approx.cutoffs.large.waves.field`.  For each finite cutoff the
exponential of the log oscillation is the all-pairs ratio supremum. -/
noncomputable def cutoffRatioOscillationSup (n : ℕ) (k : ℤ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ≥0∞ :=
  ⨆ m : ℕ, ⨆ _h : n ≤ m,
    ENNReal.ofReal (Real.exp (cubeOscillation k
      (fun x => cutoffShellSum m (n : ℤ) x omega)) - 1)

private theorem cutoffShellIndices_nat_eq_Ico (n m : ℕ) :
    cutoffShellIndices m (n : ℤ) = Finset.Ico (n + 1) (m + 1) := by
  unfold cutoffShellIndices
  ext j
  simp only [Finset.mem_Icc, Finset.mem_Ico]
  omega

private theorem continuous_cutoffShellSum_in_space (n m : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    Continuous (fun x : Vec d => cutoffShellSum m (n : ℤ) x omega) := by
  unfold cutoffShellSum
  fun_prop

/-- A finite cutoff block is bounded by the corresponding initial segment of
the measurable shell-envelope stream. -/
theorem cutoffShellSum_cubeOscillation_le_partial_sensitivity
    (n m : ℕ) (k : ℤ) (hnm : n ≤ m) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    cubeOscillation k (fun x => cutoffShellSum m (n : ℤ) x omega) ≤
      ∑ i ∈ Finset.range (m - n), sensitivityLayer n k i omega := by
  have hindices := cutoffShellIndices_nat_eq_Ico n m
  have hnonneg : 0 ≤ ∑ i ∈ Finset.range (m - n),
      sensitivityLayer n k i omega :=
    Finset.sum_nonneg fun i _ => shellOscillationEnvelope_nonneg _ _ _
  refine cubeOscillation_le_of_forall k _ hnonneg ?_
  intro x y hx hy
  rw [cutoffShellSum, cutoffShellSum, ← Finset.sum_sub_distrib, hindices,
    Finset.sum_Ico_eq_sum_range]
  have hterm : ∀ i ∈ Finset.range (m + 1 - (n + 1)),
      omega (n + 1 + i) x - omega (n + 1 + i) y ≤
        sensitivityLayer n k i omega := by
    intro i _hi
    calc
      omega (n + 1 + i) x - omega (n + 1 + i) y ≤
          cubeOscillation k (omega (n + 1 + i)) :=
        sub_le_cubeOscillation_of_continuous k
          (omega (n + 1 + i)).1.1.continuous hx hy
      _ ≤ shellOscillationEnvelope (n + 1 + i) k omega :=
        cubeOscillation_le_shellOscillationEnvelope _ _ _
      _ = sensitivityLayer n k i omega := by
        simp only [sensitivityLayer, sensitivityShellIndex]
  have hsub : m + 1 - (n + 1) = m - n := by omega
  rw [hsub] at hterm ⊢
  simpa only [sensitivityLayer, sensitivityShellIndex] using
    Finset.sum_le_sum hterm

/-- Every finite cutoff oscillation is below the full measurable stream. -/
theorem cutoffShellSum_cubeOscillation_le_sensitivity_tsum
    (n m : ℕ) (k : ℤ)
    (hnm : n ≤ m) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hs : Summable fun i => sensitivityLayer n k i omega) :
    cubeOscillation k (fun x => cutoffShellSum m (n : ℤ) x omega) ≤
      ∑' i, sensitivityLayer n k i omega := by
  exact (cutoffShellSum_cubeOscillation_le_partial_sensitivity n m k hnm omega).trans
    (hs.sum_le_tsum (Finset.range (m - n))
      (fun i _ => shellOscillationEnvelope_nonneg _ _ _))

/-- Pointwise domination of the literal source supremum on the a.e. event
where the envelope stream is summable. -/
theorem ae_cutoffLogRatioOscillationSup_le_sensitivity_tsum
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ) (k : ℤ) :
    ∀ᵐ omega ∂M.P.toMeasure,
      cutoffLogRatioOscillationSup n k omega ≤
        ENNReal.ofReal (∑' i, sensitivityLayer n k i omega) := by
  filter_upwards [ae_summable_sensitivityLayer M n k] with omega hs
  unfold cutoffLogRatioOscillationSup
  refine iSup_le fun m => iSup_le fun hnm => ?_
  exact ENNReal.ofReal_le_ofReal
    ((cutoffShellSum_cubeOscillation_le_partial_sensitivity n m k hnm omega).trans
      (hs.sum_le_tsum (Finset.range (m - n))
        (fun i _ => shellOscillationEnvelope_nonneg _ _ _)))

theorem aemeasurable_sensitivityFieldRepresentative (n : ℕ) (k : ℤ)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    AEMeasurable (sensitivityFieldRepresentative (d := d) n k) M.P.toMeasure :=
  aemeasurable_tsum_of_nonneg
    (fun i => (measurable_shellOscillationEnvelope (d := d)
      (sensitivityShellIndex n i) k).aemeasurable)
    (fun i omega => shellOscillationEnvelope_nonneg
      (d := d) (sensitivityShellIndex n i) k omega)

theorem sensitivityFieldRepresentative_nonneg (n : ℕ) (k : ℤ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ sensitivityFieldRepresentative n k omega := by
  unfold sensitivityFieldRepresentative
  exact tsum_nonneg fun i => shellOscillationEnvelope_nonneg _ _ _

theorem isBigOWith_gammaTwo_sensitivityFieldRepresentative
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ) (k : ℤ) :
    IsBigOWith M.P.toMeasure (gammaSigma 2)
      (sensitivityFieldRepresentative n k)
      (shellSensitivityConst d * M.delta * (3 : ℝ) ^ (k - (n : ℤ))) := by
  simpa only [sensitivityFieldRepresentative] using!
    isBigOWith_gammaTwo_sensitivityLayer_tsum M n k

theorem ae_cutoffRatioOscillationSup_le_exp_representative
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ) (k : ℤ) :
    ∀ᵐ omega ∂M.P.toMeasure,
      cutoffRatioOscillationSup n k omega ≤
        ENNReal.ofReal (Real.exp (sensitivityFieldRepresentative n k omega) - 1) := by
  filter_upwards [ae_summable_sensitivityLayer M n k] with omega hs
  unfold cutoffRatioOscillationSup sensitivityFieldRepresentative
  refine iSup_le fun m => iSup_le fun hnm => ?_
  apply ENNReal.ofReal_le_ofReal
  exact sub_le_sub_right (Real.exp_le_exp.mpr
    ((cutoffShellSum_cubeOscillation_le_partial_sensitivity n m k hnm omega).trans
      (hs.sum_le_tsum (Finset.range (m - n))
        (fun i _ => shellOscillationEnvelope_nonneg _ _ _)))) 1

/-- `e.sensitivity.field`: the literal infinite-cutoff, all-pairs field
oscillation admits a measurable `Gamma_2` dominator at scale
`C(d) delta 3^(k-n)`.  This domination-witness formulation is the rigorous
meaning of the paper's notation `X ≤ O_{Gamma_2}(A)`. -/
theorem sensitivity_field
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ) (k : ℤ) :
    ∃ Z : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ,
      AEMeasurable Z M.P.toMeasure ∧
      IsBigOWith M.P.toMeasure (gammaSigma 2) Z
        (shellSensitivityConst d * M.delta * (3 : ℝ) ^ (k - (n : ℤ))) ∧
      (∀ᵐ omega ∂M.P.toMeasure,
        cutoffLogRatioOscillationSup n k omega ≤ ENNReal.ofReal (Z omega)) := by
  refine ⟨fun omega => ∑' i, sensitivityLayer n k i omega, ?_,
    isBigOWith_gammaTwo_sensitivityLayer_tsum M n k,
    ae_cutoffLogRatioOscillationSup_le_sensitivity_tsum M n k⟩
  exact aemeasurable_tsum_of_nonneg
    (fun i => (measurable_shellOscillationEnvelope _ _).aemeasurable)
    (fun i omega => shellOscillationEnvelope_nonneg _ _ _)

/-- `e.infraredhom.approx.cutoffs.large.waves.field`, with the literal
`ENNReal` ratio supremum accompanied by its a.e.-equal-or-larger measurable
real representative.  The displayed bound is the explicit output of the
paper's lognormal transfer. -/
theorem infraredhom_approx_cutoffs_large_waves_field
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ) (k : ℤ) (xi : ℝ)
    (hxi : 1 ≤ xi) :
    let A := shellSensitivityConst d * M.delta *
      (3 : ℝ) ^ (k - (n : ℤ))
    Integrable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      (Real.exp (sensitivityFieldRepresentative n k omega) - 1) ^ xi)
        M.P.toMeasure ∧
    (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        (Real.exp (sensitivityFieldRepresentative n k omega) - 1) ^ xi
        ∂M.P.toMeasure) ^ xi⁻¹ ≤
      2 * gammaMomentConst 2 * Real.sqrt (2 * xi) * A *
        Real.exp (xi * A ^ 2) ∧
    (∀ᵐ omega ∂M.P.toMeasure,
      cutoffRatioOscillationSup n k omega ≤
        ENNReal.ofReal
          (Real.exp (sensitivityFieldRepresentative n k omega) - 1)) := by
  dsimp only
  let A := shellSensitivityConst d * M.delta * (3 : ℝ) ^ (k - (n : ℤ))
  have hA : 0 < A := mul_pos
    (mul_pos (shellSensitivityConst_pos d) M.shellPrefix.delta_pos)
    (zpow_pos (by norm_num) _)
  have hZnonneg : ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      0 ≤ sensitivityFieldRepresentative n k omega :=
    sensitivityFieldRepresentative_nonneg n k
  have hZ : IsBigO M.P.toMeasure (gammaSigma 2)
      (sensitivityFieldRepresentative n k) A := by
    simpa [IsBigO, abs_of_nonneg (hZnonneg _), A] using
      isBigOWith_gammaTwo_sensitivityFieldRepresentative M n k
  have htransfer := integral_abs_exp_sub_const_sub_one_rpow_root_le
    (mu := M.P.toMeasure) (X := sensitivityFieldRepresentative n k)
    (A := A) (p := xi) (b := 0) hA hxi
    (aemeasurable_sensitivityFieldRepresentative n k M) hZ
  have hfun : (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      (Real.exp (sensitivityFieldRepresentative n k omega) - 1) ^ xi) =
      fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        |Real.exp (sensitivityFieldRepresentative n k omega) - 1| ^ xi := by
    funext omega
    rw [abs_of_nonneg]
    exact sub_nonneg.mpr (Real.one_le_exp (hZnonneg omega))
  refine ⟨?_, ?_, ae_cutoffRatioOscillationSup_le_exp_representative M n k⟩
  · rw [hfun]
    simpa only [sub_zero] using htransfer.1
  · rw [hfun]
    simpa only [sub_zero, abs_zero, add_zero] using htransfer.2

/-! ## Translated small-cube block estimates -/

/-- The own-scale `(g2)` gauge controlling shell `j` on the physical
translate `z + cu_r`, in the regime `r ≤ j`. -/
def translatedSmallShellEnvelope (j : ℕ) (r : ℤ) (z : Vec d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  (3 : ℝ) ^ (r - (j : ℤ)) *
    translatedShellG2 j ((((3 : ℝ) ^ j)⁻¹) • z) omega

theorem translatedSmallShellEnvelope_nonneg (j : ℕ) (r : ℤ) (z : Vec d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : 0 ≤ translatedSmallShellEnvelope j r z omega :=
  mul_nonneg (zpow_nonneg (by norm_num) _)
    (translatedShellG2_nonneg _ _ _)

theorem measurable_translatedSmallShellEnvelope (j : ℕ) (r : ℤ) (z : Vec d) :
    Measurable (translatedSmallShellEnvelope (d := d) j r z) :=
  (measurable_translatedShellG2 j _).const_mul _

theorem isBigOWith_gammaTwo_translatedSmallShellEnvelope
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) (r : ℤ) (z : Vec d) :
    IsBigOWith M.P.toMeasure (gammaSigma 2)
      (translatedSmallShellEnvelope j r z)
      ((3 : ℝ) ^ (r - (j : ℤ)) *
        ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) := by
  exact (isBigOWith_gammaTwo_translatedShellG2 M j
    ((((3 : ℝ) ^ j)⁻¹) • z)).const_mul (zpow_nonneg (by norm_num) _)

private theorem translated_scaled_mem_unitCube {j : ℕ} {r : ℤ}
    (hrj : r ≤ (j : ℤ)) {z x : Vec d}
    (hx : x - z ∈ openCubeSet (originCube d r)) :
    (((3 : ℝ) ^ j)⁻¹) • (x - z) ∈ openCubeSet (originCube d 0) :=
  scaled_mem_unitCube hrj hx

/-- Deterministic translated-cube oscillation bound for one shell. -/
theorem abs_shell_sub_le_translatedSmallShellEnvelope
    (j : ℕ) (r : ℤ) (hrj : r ≤ (j : ℤ)) (z : Vec d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) {x : Vec d}
    (hx : x - z ∈ openCubeSet (originCube d r)) :
    |omega j x - omega j z| ≤ translatedSmallShellEnvelope j r z omega := by
  let z' : Vec d := (((3 : ℝ) ^ j)⁻¹) • z
  let g := _root_.SubdiffusiveProcess.Model.PotentialField.translate z'
    (unscalePotential j (omega j))
  let u : Vec d := (((3 : ℝ) ^ j)⁻¹) • (x - z)
  have hu : u ∈ openCubeSet (originCube d 0) :=
    translated_scaled_mem_unitCube hrj hx
  have hzero : (0 : Vec d) ∈ openCubeSet (originCube d 0) := by
    rw [mem_openCubeSet_originCube_iff]
    intro i
    norm_num
  have hconv : Convex ℝ (openCubeSet (originCube d 0)) := convex_openCubeSet _
  have hmean := hconv.norm_image_sub_le_of_norm_fderiv_le
    (f := fun v : Vec d => g v)
    (fun v _ => (g.hasFDerivAt v).differentiableAt)
    (fun v hv => by
      rw [(g.hasFDerivAt v).fderiv]
      exact deriv_norm_le_g2Observable g hv)
    hu hzero
  have hdist : ‖(0 : Vec d) - u‖ ≤ (3 : ℝ) ^ (r - (j : ℤ)) := by
    have hzeroR : (0 : Vec d) ∈ openCubeSet (originCube d r) := by
      rw [mem_openCubeSet_originCube_iff]
      intro i
      have hp : 0 < (3 : ℝ) ^ r := zpow_pos (by norm_num) _
      simp only [Pi.zero_apply]
      constructor <;> nlinarith
    have hraw := norm_scaled_sub_le_zpow hrj hx hzeroR
    simpa only [u, smul_zero, zero_sub, norm_neg] using hraw
  have hvalx : g u = omega j x := by
    simp only [g, u, z', _root_.SubdiffusiveProcess.Model.PotentialField.translate_apply,
      unscalePotential, _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale_apply]
    rw [← smul_add, sub_add_cancel, smul_smul]
    rw [mul_inv_cancel₀ (by positivity : (3 : ℝ) ^ j ≠ 0), one_smul]
  have hvalz : g 0 = omega j z := by
    simp only [g, z', _root_.SubdiffusiveProcess.Model.PotentialField.translate_apply,
      zero_add, unscalePotential,
      _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale_apply, smul_smul]
    rw [mul_inv_cancel₀ (by positivity : (3 : ℝ) ^ j ≠ 0), one_smul]
  change ‖g 0 - g u‖ ≤ _ at hmean
  rw [hvalz, hvalx, Real.norm_eq_abs, abs_sub_comm] at hmean
  have hg : 0 ≤ translatedShellG2 j z' omega := translatedShellG2_nonneg _ _ _
  calc
    |omega j x - omega j z| ≤
        translatedShellG2 j z' omega * ‖(0 : Vec d) - u‖ := hmean
    _ ≤ translatedShellG2 j z' omega * (3 : ℝ) ^ (r - (j : ℤ)) :=
      mul_le_mul_of_nonneg_left hdist hg
    _ = translatedSmallShellEnvelope j r z omega := by
      rw [translatedSmallShellEnvelope]
      exact mul_comm _ _

/-- Measurable majorant for a consecutive shell block on `z + cu_r`. -/
def smallCubeBlockEnvelope (lower upper : ℕ) (r : ℤ) (z : Vec d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  |cutoffShellSum upper ((lower : ℤ) - 1) z omega| +
    ∑ j ∈ Finset.Icc lower upper,
      translatedSmallShellEnvelope j r z omega

theorem smallCubeBlockEnvelope_nonneg (lower upper : ℕ) (r : ℤ) (z : Vec d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : 0 ≤ smallCubeBlockEnvelope lower upper r z omega := by
  unfold smallCubeBlockEnvelope
  exact add_nonneg (abs_nonneg _)
    (Finset.sum_nonneg fun j _ => translatedSmallShellEnvelope_nonneg _ _ _ _)

theorem measurable_smallCubeBlockEnvelope (lower upper : ℕ) (r : ℤ)
    (z : Vec d) : Measurable (smallCubeBlockEnvelope (d := d) lower upper r z) := by
  unfold smallCubeBlockEnvelope
  exact (measurable_cutoffShellSum upper ((lower : ℤ) - 1) z).norm.add
    (Finset.measurable_sum _ fun j _ =>
      measurable_translatedSmallShellEnvelope j r z)

/-- The block envelope controls every point of its translated cube. -/
theorem abs_cutoffShellSum_le_smallCubeBlockEnvelope
    (lower upper : ℕ) (r : ℤ) (z : Vec d)
    (hr : r ≤ (lower : ℤ))
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) {x : Vec d}
    (hx : x - z ∈ openCubeSet (originCube d r)) :
    |cutoffShellSum upper ((lower : ℤ) - 1) x omega| ≤
      smallCubeBlockEnvelope lower upper r z omega := by
  have hindex : cutoffShellIndices upper ((lower : ℤ) - 1) =
      Finset.Icc lower upper := by
    unfold cutoffShellIndices
    congr 1
    omega
  have hdiff : |cutoffShellSum upper ((lower : ℤ) - 1) x omega -
      cutoffShellSum upper ((lower : ℤ) - 1) z omega| ≤
      ∑ j ∈ Finset.Icc lower upper,
        translatedSmallShellEnvelope j r z omega := by
    rw [cutoffShellSum, cutoffShellSum, ← Finset.sum_sub_distrib, hindex]
    calc
      |∑ j ∈ Finset.Icc lower upper, (omega j x - omega j z)| ≤
          ∑ j ∈ Finset.Icc lower upper, |omega j x - omega j z| := by
        induction Finset.Icc lower upper using Finset.induction_on with
        | empty => simp
        | @insert a s ha ih =>
          simp only [Finset.sum_insert ha]
          exact (abs_add_le _ _).trans (add_le_add (le_refl _) ih)
      _ ≤ _ := Finset.sum_le_sum fun j hj =>
        abs_shell_sub_le_translatedSmallShellEnvelope j r
          (hr.trans (by exact_mod_cast (Finset.mem_Icc.mp hj).1)) z omega hx
  unfold smallCubeBlockEnvelope
  calc
    |cutoffShellSum upper ((lower : ℤ) - 1) x omega| ≤
        |cutoffShellSum upper ((lower : ℤ) - 1) z omega| +
          |cutoffShellSum upper ((lower : ℤ) - 1) x omega -
            cutoffShellSum upper ((lower : ℤ) - 1) z omega| := by
      let A := cutoffShellSum upper ((lower : ℤ) - 1) x omega
      let B := cutoffShellSum upper ((lower : ℤ) - 1) z omega
      change |A| ≤ |B| + |A - B|
      calc
        |A| = |B + (A - B)| := by congr 1; ring
        _ ≤ |B| + |A - B| := abs_add_le _ _
    _ ≤ _ := add_le_add (le_refl _) hdiff

/-- Tail scale of one translated shell in a small cube. -/
def translatedSmallShellScale
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) (r : ℤ) : ℝ :=
  (3 : ℝ) ^ (r - (j : ℤ)) *
    ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)

/-- Exact scale produced by the two finite `Gamma_2` assemblies in the
small-cube block estimate. -/
def smallCubeBlockScale
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (lower upper : ℕ) (r : ℤ) : ℝ :=
  gammaTriangleConst 2 *
    (cutoffGammaConst * Real.sqrt ((upper - lower + 1 : ℕ) : ℝ) * M.delta +
      gammaTriangleConst 2 *
        ∑ j ∈ Finset.Icc lower upper, translatedSmallShellScale M j r)

theorem translatedSmallShellScale_pos
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℕ) (r : ℤ) :
    0 < translatedSmallShellScale M j r := by
  unfold translatedSmallShellScale
  exact mul_pos (zpow_pos (by norm_num) _)
    (mul_pos (Real.rpow_pos_of_pos (by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith) _) M.shellPrefix.delta_pos)

theorem isBigOWith_gammaTwo_smallCubeShellSum
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (lower upper : ℕ) (r : ℤ)
    (z : Vec d) (hlu : lower ≤ upper) :
    IsBigOWith M.P.toMeasure (gammaSigma 2)
      (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        ∑ j ∈ Finset.Icc lower upper,
          translatedSmallShellEnvelope j r z omega)
      (gammaTriangleConst 2 *
        ∑ j ∈ Finset.Icc lower upper, translatedSmallShellScale M j r) := by
  have hs : (Finset.Icc lower upper).Nonempty := Finset.nonempty_Icc.mpr hlu
  have h := isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := M.P.toMeasure) (Finset.Icc lower upper)
    (X := fun j => translatedSmallShellEnvelope (d := d) j r z)
    (a := fun j => translatedSmallShellScale M j r) (σ := 2)
    (by norm_num) hs
    (fun j _ => translatedSmallShellScale_pos M j r)
    (fun j _ => by
      simpa [IsBigO, translatedSmallShellScale, abs_of_nonneg
        (translatedSmallShellEnvelope_nonneg j r z _)] using!
          isBigOWith_gammaTwo_translatedSmallShellEnvelope M j r z)
    (fun j _ => measurable_translatedSmallShellEnvelope j r z)
  simpa [IsBigO, abs_of_nonneg (Finset.sum_nonneg fun j _ =>
    translatedSmallShellEnvelope_nonneg j r z _)] using h

theorem isBigOWith_gammaTwo_smallCubeBlockEnvelope
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (lower upper : ℕ) (r : ℤ)
    (z : Vec d) (hlu : lower ≤ upper) :
    IsBigOWith M.P.toMeasure (gammaSigma 2)
      (smallCubeBlockEnvelope lower upper r z)
      (smallCubeBlockScale M lower upper r) := by
  let pointTerm : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    |cutoffShellSum upper ((lower : ℤ) - 1) z omega|
  let shellTerm : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    ∑ j ∈ Finset.Icc lower upper,
      translatedSmallShellEnvelope j r z omega
  let pointScale : ℝ :=
    cutoffGammaConst * Real.sqrt ((upper - lower + 1 : ℕ) : ℝ) * M.delta
  let shellScale : ℝ := gammaTriangleConst 2 *
    ∑ j ∈ Finset.Icc lower upper, translatedSmallShellScale M j r
  have hlowerInt : (-1 : ℤ) ≤ (lower : ℤ) - 1 := by omega
  have hupperInt : (lower : ℤ) - 1 < (upper : ℤ) := by omega
  have hcard : (((upper : ℤ) - ((lower : ℤ) - 1) : ℤ) : ℝ) =
      ((upper - lower + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show (upper : ℤ) - ((lower : ℤ) - 1) =
      (upper - lower + 1 : ℕ) by omega)
  have hpoint : IsBigO M.P.toMeasure (gammaSigma 2) pointTerm pointScale := by
    have h := isBigO_gammaTwo_cutoffShellSum_sourceScale M upper
      ((lower : ℤ) - 1) z hlowerInt hupperInt
    rw [hcard] at h
    simpa [pointTerm, pointScale, IsBigO, abs_abs] using h
  have hshellWith := isBigOWith_gammaTwo_smallCubeShellSum
    M lower upper r z hlu
  have hshell : IsBigO M.P.toMeasure (gammaSigma 2) shellTerm shellScale := by
    simpa [shellTerm, shellScale, IsBigO, abs_of_nonneg
      (Finset.sum_nonneg fun j _ =>
        translatedSmallShellEnvelope_nonneg j r z _)] using hshellWith
  have hpScale : 0 < pointScale := by
    unfold pointScale
    have hcount : 0 < ((upper - lower + 1 : ℕ) : ℝ) := by positivity
    exact mul_pos (mul_pos cutoffGammaConst_pos (Real.sqrt_pos.mpr hcount))
      M.shellPrefix.delta_pos
  have hsScale : 0 < shellScale := by
    unfold shellScale
    exact mul_pos gammaTriangleConst_pos
      (Finset.sum_pos (fun j _ => translatedSmallShellScale_pos M j r)
        (Finset.nonempty_Icc.mpr hlu))
  let X : Bool → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun b => if b then shellTerm else pointTerm
  let a : Bool → ℝ := fun b => if b then shellScale else pointScale
  have htwo := isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := M.P.toMeasure) (Finset.univ : Finset Bool) (X := X) (a := a)
    (σ := 2) (by norm_num) Finset.univ_nonempty
    (fun b _ => by cases b <;> simp [a, hpScale, hsScale])
    (fun b _ => by
      cases b
      · change IsBigO M.P.toMeasure (gammaSigma 2) pointTerm pointScale
        exact hpoint
      · change IsBigO M.P.toMeasure (gammaSigma 2) shellTerm shellScale
        exact hshell)
    (fun b _ => by
      cases b
      · simpa [X, pointTerm] using
          (measurable_cutoffShellSum upper ((lower : ℤ) - 1) z).norm
      · simpa [X, shellTerm] using Finset.measurable_sum _
          (fun j _ => measurable_translatedSmallShellEnvelope j r z))
  have hsumX : (fun omega => ∑ b ∈ (Finset.univ : Finset Bool), X b omega) =
      smallCubeBlockEnvelope lower upper r z := by
    funext omega
    simp [X, pointTerm, shellTerm, smallCubeBlockEnvelope, add_comm]
  have hsuma : ∑ b ∈ (Finset.univ : Finset Bool), a b =
      pointScale + shellScale := by simp [a, add_comm]
  rw [hsumX, hsuma] at htwo
  simpa [smallCubeBlockScale, pointScale, shellScale, IsBigO,
    abs_of_nonneg (smallCubeBlockEnvelope_nonneg lower upper r z _)] using htwo

/-- Dimension-free constant in the own-scale block estimate. -/
def smallCubeBlockConst : ℝ :=
  gammaTriangleConst 2 *
    (cutoffGammaConst + gammaTriangleConst 2 *
      (1 + Real.log 2) ^ (2 : ℝ)⁻¹)

theorem smallCubeBlockConst_pos : 0 < smallCubeBlockConst := by
  unfold smallCubeBlockConst
  exact mul_pos gammaTriangleConst_pos
    (add_pos cutoffGammaConst_pos (mul_pos gammaTriangleConst_pos
      (Real.rpow_pos_of_pos (by
        have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        linarith) _)))

private theorem sum_translatedSmallShellScale_ownScale_le
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (lower upper : ℕ) :
    ∑ j ∈ Finset.Icc lower upper,
        translatedSmallShellScale M j ((lower : ℤ) - 1) ≤
      (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta := by
  have hIcc : Finset.Icc lower upper = Finset.Ico lower (upper + 1) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  let B := (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta
  have hB : 0 ≤ B := mul_nonneg (Real.rpow_nonneg (by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith) _) M.shellPrefix.delta_pos.le
  have hterm : ∀ i : ℕ,
      translatedSmallShellScale M (lower + i) ((lower : ℤ) - 1) =
        B * (1 / 3 : ℝ) ^ (i + 1) := by
    intro i
    unfold translatedSmallShellScale
    have hpow : (3 : ℝ) ^ (((lower : ℤ) - 1) - ((lower + i : ℕ) : ℤ)) =
        (1 / 3 : ℝ) ^ (i + 1) := by
      rw [show ((lower : ℤ) - 1) - ((lower + i : ℕ) : ℤ) =
          -((i + 1 : ℕ) : ℤ) by omega,
        zpow_neg, zpow_natCast]
      rw [one_div, inv_pow]
    rw [hpow]
    dsimp [B]
    ring
  simp_rw [hterm]
  calc
    ∑ i ∈ Finset.range (upper + 1 - lower), B * (1 / 3 : ℝ) ^ (i + 1) ≤
        ∑' i : ℕ, B * (1 / 3 : ℝ) ^ (i + 1) := by
      apply Summable.sum_le_tsum
      · intro i _
        positivity
      · have hgeom : Summable (fun i : ℕ => (1 / 3 : ℝ) ^ i) :=
          summable_geometric_of_norm_lt_one
            (show ‖(1 / 3 : ℝ)‖ < 1 by norm_num)
        have hshift : Summable (fun i : ℕ => (1 / 3 : ℝ) ^ (i + 1)) :=
          (summable_nat_add_iff 1).2 hgeom
        exact hshift.mul_left B
    _ = B / 2 := by
      rw [show (∑' i : ℕ, B * (1 / 3 : ℝ) ^ (i + 1)) =
          B * ∑' i : ℕ, (1 / 3 : ℝ) ^ (i + 1) by
        exact tsum_mul_left]
      rw [show (∑' i : ℕ, (1 / 3 : ℝ) ^ (i + 1)) =
          (∑' i : ℕ, (1 / 3 : ℝ) ^ i) * (1 / 3 : ℝ) by
        simpa only [pow_succ] using
          (tsum_mul_right : (∑' i : ℕ, (1 / 3 : ℝ) ^ i * (1 / 3 : ℝ)) = _)]
      rw [tsum_geometric_of_norm_lt_one (show ‖(1 / 3 : ℝ)‖ < 1 by norm_num)]
      norm_num
      ring
    _ ≤ B := by nlinarith

theorem smallCubeBlockScale_ownScale_le
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (lower upper : ℕ) :
    smallCubeBlockScale M lower upper ((lower : ℤ) - 1) ≤
      smallCubeBlockConst *
        Real.sqrt ((upper - lower + 1 : ℕ) : ℝ) * M.delta := by
  have hsum := sum_translatedSmallShellScale_ownScale_le M lower upper
  have hcount : 1 ≤ ((upper - lower + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ upper - lower + 1 by omega)
  have hsqrt : 1 ≤ Real.sqrt ((upper - lower + 1 : ℕ) : ℝ) := by
    have hcount0 : 0 ≤ ((upper - lower + 1 : ℕ) : ℝ) := by positivity
    nlinarith [Real.sq_sqrt hcount0, Real.sqrt_nonneg
      ((upper - lower + 1 : ℕ) : ℝ)]
  have hdelta := M.shellPrefix.delta_pos.le
  unfold smallCubeBlockScale smallCubeBlockConst
  have hC : 0 ≤ gammaTriangleConst 2 :=
    (gammaTriangleConst_pos (σ := 2)).le
  have hbase : 0 ≤ (1 + Real.log 2) ^ (2 : ℝ)⁻¹ := Real.rpow_nonneg (by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith) _
  have hsecond : gammaTriangleConst 2 *
      ∑ j ∈ Finset.Icc lower upper,
        translatedSmallShellScale M j ((lower : ℤ) - 1) ≤
      gammaTriangleConst 2 *
        ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) *
          Real.sqrt ((upper - lower + 1 : ℕ) : ℝ) := by
    calc
      gammaTriangleConst 2 *
          ∑ j ∈ Finset.Icc lower upper,
            translatedSmallShellScale M j ((lower : ℤ) - 1) ≤
        gammaTriangleConst 2 *
          ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) := by gcongr
      _ ≤ gammaTriangleConst 2 *
          ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) *
            Real.sqrt ((upper - lower + 1 : ℕ) : ℝ) := by
        exact le_mul_of_one_le_right
          (mul_nonneg hC (mul_nonneg hbase hdelta)) hsqrt
  calc
    gammaTriangleConst 2 *
        (cutoffGammaConst * Real.sqrt (↑(upper - lower + 1)) * M.delta +
          gammaTriangleConst 2 *
            ∑ j ∈ Finset.Icc lower upper,
              translatedSmallShellScale M j (↑lower - 1)) ≤
      gammaTriangleConst 2 *
        (cutoffGammaConst * Real.sqrt (↑(upper - lower + 1)) * M.delta +
          gammaTriangleConst 2 *
            ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) *
              Real.sqrt (↑(upper - lower + 1))) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add (le_refl
            (cutoffGammaConst * Real.sqrt (↑(upper - lower + 1)) * M.delta))
              hsecond) hC
    _ = gammaTriangleConst 2 *
        (cutoffGammaConst + gammaTriangleConst 2 *
          (1 + Real.log 2) ^ (2 : ℝ)⁻¹) *
          Real.sqrt (↑(upper - lower + 1)) * M.delta := by ring

/-! ## The low-frequency block on a large cube -/

def physicalShellCoverCenter (n : ℕ) (p : Fin d → ℤ) : Vec d :=
  (3 : ℝ) ^ n • shellCoverCenter p

theorem exists_physicalShellCoverCenter_mem
    (n : ℕ) (k : ℤ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d k)) :
    ∃ p ∈ shellCoverShifts d (k - (n : ℤ)),
      x - physicalShellCoverCenter n p ∈ openCubeSet (originCube d (n : ℤ)) := by
  let u : Vec d := (((3 : ℝ) ^ n)⁻¹) • x
  have hu : u ∈ openCubeSet (originCube d (k - (n : ℤ))) := by
    rw [mem_openCubeSet_originCube_iff] at hx ⊢
    intro i
    have h3 : 0 < (3 : ℝ) ^ n := by positivity
    have hpow : (3 : ℝ) ^ (k - (n : ℤ)) =
        ((3 : ℝ) ^ n)⁻¹ * (3 : ℝ) ^ k := by
      rw [← zpow_natCast, ← zpow_neg,
        ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 1
      ring
    simp only [u, Pi.smul_apply, smul_eq_mul, hpow]
    constructor
    · have hi := mul_lt_mul_of_pos_left (hx i).1 (inv_pos.mpr h3)
      nlinarith
    · have hi := mul_lt_mul_of_pos_left (hx i).2 (inv_pos.mpr h3)
      nlinarith
  obtain ⟨p, hpFin, hpMem⟩ := exists_shellCoverShift_mem hu
  refine ⟨p, hpFin, ?_⟩
  rw [mem_translateSet_iff_sub_mem] at hpMem
  rw [mem_openCubeSet_originCube_iff] at hpMem ⊢
  intro i
  have h3 : 0 < (3 : ℝ) ^ n := by positivity
  have hcoord :
      (x - physicalShellCoverCenter n p) i =
        (3 : ℝ) ^ n * (u - shellCoverCenter p) i := by
    simp only [physicalShellCoverCenter, u, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    field_simp
  rw [hcoord, show (3 : ℝ) ^ (n : ℤ) = (3 : ℝ) ^ n by rw [zpow_natCast]]
  constructor
  · have hi := mul_lt_mul_of_pos_left (hpMem i).1 h3
    norm_num at hi ⊢
    nlinarith
  · have hi := mul_lt_mul_of_pos_left (hpMem i).2 h3
    norm_num at hi ⊢
    nlinarith

/-- Maximum of the translated own-scale envelopes covering `cu_k`. -/
def coveredLowBlockEnvelope (n ell : ℕ) (k : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  (shellCoverShifts d (k - (n : ℤ))).sup'
    (shellCoverShifts_nonempty d (k - (n : ℤ)))
    (fun p => smallCubeBlockEnvelope (n + 1) ell (n : ℤ)
      (physicalShellCoverCenter n p) omega)

theorem coveredLowBlockEnvelope_nonneg (n ell : ℕ) (k : ℤ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : 0 ≤ coveredLowBlockEnvelope n ell k omega := by
  unfold coveredLowBlockEnvelope
  obtain ⟨p, hp⟩ := shellCoverShifts_nonempty d (k - (n : ℤ))
  exact (smallCubeBlockEnvelope_nonneg (d := d) (n + 1) ell (n : ℤ)
    (physicalShellCoverCenter n p) omega).trans
      (Finset.le_sup'
        (fun q => smallCubeBlockEnvelope (n + 1) ell (n : ℤ)
          (physicalShellCoverCenter n q) omega) hp)

theorem measurable_coveredLowBlockEnvelope (n ell : ℕ) (k : ℤ) :
    Measurable (coveredLowBlockEnvelope (d := d) n ell k) := by
  let Y : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
    (shellCoverShifts d (k - (n : ℤ))).sup'
      (shellCoverShifts_nonempty d (k - (n : ℤ))) fun p =>
        smallCubeBlockEnvelope (n + 1) ell (n : ℤ)
          (physicalShellCoverCenter n p)
  have hY : Measurable Y := Finset.measurable_sup'
    (shellCoverShifts_nonempty d (k - (n : ℤ)))
    (fun p _ => measurable_smallCubeBlockEnvelope (d := d) (n + 1) ell
      (n : ℤ) (physicalShellCoverCenter n p))
  have heq : Y = coveredLowBlockEnvelope n ell k := by
    funext omega
    exact Finset.sup'_apply (shellCoverShifts_nonempty d (k - (n : ℤ)))
      (fun p => smallCubeBlockEnvelope (n + 1) ell (n : ℤ)
        (physicalShellCoverCenter n p)) omega
  rwa [← heq]

theorem abs_lowBlock_le_coveredLowBlockEnvelope
    (n ell : ℕ) (k : ℤ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d k)) :
    |cutoffShellSum ell (n : ℤ) x omega| ≤
      coveredLowBlockEnvelope n ell k omega := by
  obtain ⟨p, hpFin, hp⟩ := exists_physicalShellCoverCenter_mem n k hx
  have hlocal := abs_cutoffShellSum_le_smallCubeBlockEnvelope
    (d := d) (n + 1) ell (n : ℤ) (physicalShellCoverCenter n p)
    (by norm_num) omega hp
  have hparam : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
  rw [hparam] at hlocal
  exact hlocal.trans (Finset.le_sup'
    (fun q => smallCubeBlockEnvelope (n + 1) ell (n : ℤ)
      (physicalShellCoverCenter n q) omega) hpFin)

/-- Dimensional constant in the large-cube low-band maximum. -/
def coveredLowBlockConst (d : ℕ) : ℝ :=
  Real.sqrt (shellCoverLogConst * (d : ℝ)) * smallCubeBlockConst

theorem coveredLowBlockConst_pos
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) : 0 < coveredLowBlockConst d := by
  unfold coveredLowBlockConst
  exact mul_pos (Real.sqrt_pos.mpr (mul_pos shellCoverLogConst_pos
    (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1)
      (le_trans (by norm_num : 1 ≤ 2) M.shellPrefix.dimension)))))
    smallCubeBlockConst_pos

theorem isBigOWith_gammaTwo_coveredLowBlockEnvelope
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n ell : ℕ) (k : ℤ)
    (hnk : (n : ℤ) < k) (hnell : n < ell) (hellk : (ell : ℤ) ≤ k) :
    IsBigOWith M.P.toMeasure (gammaSigma 2)
      (coveredLowBlockEnvelope n ell k)
      (coveredLowBlockConst d * M.delta * (k - (n : ℤ) : ℤ)) := by
  let A := smallCubeBlockScale M (n + 1) ell (n : ℤ)
  have hlocal : ∀ p ∈ shellCoverShifts d (k - (n : ℤ)),
      IsBigOWith M.P.toMeasure (gammaSigma 2)
        (smallCubeBlockEnvelope (n + 1) ell (n : ℤ)
          (physicalShellCoverCenter n p)) A := fun p _ => by
    simpa [A, show ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) by omega] using
      isBigOWith_gammaTwo_smallCubeBlockEnvelope M (n + 1) ell (n : ℤ)
        (physicalShellCoverCenter n p) (by omega)
  have hmax := isBigOWith_gammaSigma_finset_sup'
    (μ := M.P.toMeasure) (shellCoverShifts d (k - (n : ℤ)))
    (shellCoverShifts_nonempty d (k - (n : ℤ))) (by norm_num)
    (shellCoverShifts_card_ge_two M (k - (n : ℤ)))
    hlocal
  have hscale := smallCubeBlockScale_ownScale_le M (n + 1) ell
  have hcount : ((ell - (n + 1) + 1 : ℕ) : ℝ) = ((ell : ℤ) - n : ℤ) := by
    have hnle : n ≤ ell := by omega
    have hnat : ell - (n + 1) + 1 = ell - n := by omega
    have hint : ((ell - n : ℕ) : ℤ) = (ell : ℤ) - n := by
      omega
    rw [hnat]
    exact_mod_cast hint
  rw [show ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) by omega, hcount] at hscale
  have hrpos : 0 < k - (n : ℤ) := sub_pos.mpr hnk
  have hfactor := shellCover_gaussianFactor_le_sqrt M hrpos
  have hA0 : 0 ≤ A := by
    unfold A smallCubeBlockScale
    exact mul_nonneg (gammaTriangleConst_pos (σ := 2)).le
      (add_nonneg
        (mul_nonneg (mul_nonneg cutoffGammaConst_pos.le
          (Real.sqrt_nonneg _)) M.shellPrefix.delta_pos.le)
        (mul_nonneg (gammaTriangleConst_pos (σ := 2)).le
          (Finset.sum_nonneg fun j _ =>
            (translatedSmallShellScale_pos M j (n : ℤ)).le)))
  have hr0 : 0 ≤ (k - (n : ℤ) : ℤ) := hrpos.le
  have hsqrtle : Real.sqrt (((ell : ℤ) - n : ℤ) : ℝ) ≤
      Real.sqrt ((k - (n : ℤ) : ℤ) : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast (sub_le_sub_right hellk (n : ℤ))
  have hsquares : Real.sqrt ((k - (n : ℤ) : ℤ) : ℝ) *
      Real.sqrt (((ell : ℤ) - n : ℤ) : ℝ) ≤
        ((k - (n : ℤ) : ℤ) : ℝ) := by
    calc
      Real.sqrt ((k - (n : ℤ) : ℤ) : ℝ) *
          Real.sqrt (((ell : ℤ) - n : ℤ) : ℝ) ≤
        Real.sqrt ((k - (n : ℤ) : ℤ) : ℝ) *
          Real.sqrt ((k - (n : ℤ) : ℤ) : ℝ) := by gcongr
      _ = ((k - (n : ℤ) : ℤ) : ℝ) := Real.mul_self_sqrt (by exact_mod_cast hr0)
  refine hmax.mono_scale ?_
  calc
    (3 * Real.log ((shellCoverShifts d (k - (n : ℤ))).card : ℝ)) ^
        (2 : ℝ)⁻¹ * A ≤
      (Real.sqrt (shellCoverLogConst * (d : ℝ)) *
        Real.sqrt ((k - (n : ℤ) : ℤ) : ℝ)) *
          (smallCubeBlockConst *
            Real.sqrt (((ell : ℤ) - n : ℤ) : ℝ) * M.delta) := by
      gcongr
    _ ≤ coveredLowBlockConst d * M.delta * ((k - (n : ℤ) : ℤ) : ℝ) := by
      unfold coveredLowBlockConst
      have hCd := (Real.sqrt_nonneg (shellCoverLogConst * (d : ℝ)))
      have hsmall := smallCubeBlockConst_pos.le
      calc
        (Real.sqrt (shellCoverLogConst * (d : ℝ)) *
            Real.sqrt ((k - (n : ℤ) : ℤ) : ℝ)) *
              (smallCubeBlockConst *
                Real.sqrt (((ell : ℤ) - n : ℤ) : ℝ) * M.delta) =
          (Real.sqrt (shellCoverLogConst * (d : ℝ)) *
            smallCubeBlockConst * M.delta) *
              (Real.sqrt ((k - (n : ℤ) : ℤ) : ℝ) *
                Real.sqrt (((ell : ℤ) - n : ℤ) : ℝ)) := by ring
        _ ≤ (Real.sqrt (shellCoverLogConst * (d : ℝ)) *
            smallCubeBlockConst * M.delta) *
              ((k - (n : ℤ) : ℤ) : ℝ) := by
          exact mul_le_mul_of_nonneg_left hsquares
            (mul_nonneg (mul_nonneg hCd hsmall) M.shellPrefix.delta_pos.le)
        _ = _ := by ring
    _ = _ := by norm_cast

/-! ## The finite-cutoff field display -/

/-- Literal `L^∞(cu_k)` norm of the centered finite shell block. -/
noncomputable def cutoffShellBlockLinfty (m n : ℕ) (k : ℤ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ≥0∞ :=
  ⨆ x : CubePoint d k, ENNReal.ofReal
    |cutoffShellSum m (n : ℤ) x.1 omega|

private theorem openCubeSet_origin_mono {k r : ℤ} (hkr : k ≤ r)
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d k)) :
    x ∈ openCubeSet (originCube d r) := by
  rw [mem_openCubeSet_originCube_iff] at hx ⊢
  intro i
  have hpow : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ r :=
    zpow_le_zpow_right₀ (by norm_num) hkr
  exact ⟨by nlinarith [(hx i).1], by nlinarith [(hx i).2]⟩

private theorem cutoffShellSum_split (m n ell : ℕ)
    (hnell : n ≤ ell) (hellm : ell ≤ m) (x : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    cutoffShellSum m (n : ℤ) x omega =
      cutoffShellSum ell (n : ℤ) x omega +
        cutoffShellSum m (ell : ℤ) x omega := by
  have hn : cutoffShellIndices m (n : ℤ) = Finset.Ico (n + 1) (m + 1) :=
    cutoffShellIndices_nat_eq_Ico n m
  have hnell' : cutoffShellIndices ell (n : ℤ) =
      Finset.Ico (n + 1) (ell + 1) := cutoffShellIndices_nat_eq_Ico n ell
  have hell : cutoffShellIndices m (ell : ℤ) =
      Finset.Ico (ell + 1) (m + 1) := cutoffShellIndices_nat_eq_Ico ell m
  unfold cutoffShellSum
  rw [hn, hnell', hell]
  rw [← Finset.sum_union]
  · congr 1
    ext j
    simp only [Finset.mem_union, Finset.mem_Ico]
    omega
  · exact Finset.disjoint_left.2 fun j hj1 hj2 => by
      have h1 := (Finset.mem_Ico.mp hj1).2
      have h2 := (Finset.mem_Ico.mp hj2).1
      omega

theorem isBigOWith_gammaTwo_add_nonneg
    {X Y : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ} {A B : ℝ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (hXm : Measurable X) (hYm : Measurable Y)
    (hX0 : ∀ omega, 0 ≤ X omega) (hY0 : ∀ omega, 0 ≤ Y omega)
    (hA : 0 < A) (hB : 0 < B)
    (hX : IsBigOWith M.P.toMeasure (gammaSigma 2) X A)
    (hY : IsBigOWith M.P.toMeasure (gammaSigma 2) Y B) :
    IsBigOWith M.P.toMeasure (gammaSigma 2) (fun omega => X omega + Y omega)
      (gammaTriangleConst 2 * (A + B)) := by
  let F : Bool → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun b => if b then Y else X
  let a : Bool → ℝ := fun b => if b then B else A
  have h := isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := M.P.toMeasure) (Finset.univ : Finset Bool) (X := F) (a := a)
    (σ := 2) (by norm_num) Finset.univ_nonempty
    (fun b _ => by cases b <;> simp [a, hA, hB])
    (fun b _ => by
      cases b
      · simpa [F, a, IsBigO, abs_of_nonneg (hX0 _)] using! hX
      · simpa [F, a, IsBigO, abs_of_nonneg (hY0 _)] using! hY)
    (fun b _ => by cases b <;> simp [F, hXm, hYm])
  simpa [F, a, IsBigO, add_comm,
    abs_of_nonneg (add_nonneg (hX0 _) (hY0 _))] using h

def finiteFieldConst (d : ℕ) : ℝ :=
  gammaTriangleConst 2 * (coveredLowBlockConst d + smallCubeBlockConst)

theorem finiteFieldConst_pos (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    0 < finiteFieldConst d := by
  unfold finiteFieldConst
  exact mul_pos (gammaTriangleConst_pos (σ := 2))
    (add_pos (coveredLowBlockConst_pos M) smallCubeBlockConst_pos)

private theorem one_le_gammaTriangleConst_two : 1 ≤ gammaTriangleConst 2 := by
  unfold gammaTriangleConst
  have hg : (1 : ℝ) ≤ gammaGrowthConst 2 :=
    le_trans (by norm_num) (two_le_gammaGrowthConst 2)
  have hp : (1 : ℝ) ≤ gammaGrowthConst 2 ^ (12 : ℝ) :=
    Real.one_le_rpow hg (by norm_num)
  nlinarith

/-- Source scale `sqrt(m-n) + (k-n)_+`. -/
def finiteFieldScale (m n : ℕ) (k : ℤ) : ℝ :=
  Real.sqrt ((m - n : ℕ) : ℝ) + max 0 ((k : ℝ) - n)

theorem finiteFieldScale_pos {m n : ℕ} (hnm : n < m) (k : ℤ) :
    0 < finiteFieldScale m n k := by
  unfold finiteFieldScale
  apply add_pos_of_pos_of_nonneg
  · apply Real.sqrt_pos.mpr
    exact_mod_cast (Nat.sub_pos_iff_lt.mpr hnm)
  · exact le_max_left _ _

/-- `e.infrared.approx.cutoffs.field`: the literal finite block `L^∞` norm
has a measurable `Gamma_2` dominator with exactly the paper's
`sqrt(m-n) + (k-n)_+` scale. -/
theorem infrared_approx_cutoffs_field
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m n : ℕ) (k : ℤ)
    (hnm : n < m) :
    ∃ Z : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ,
      Measurable Z ∧ (∀ omega, 0 ≤ Z omega) ∧
      IsBigOWith M.P.toMeasure (gammaSigma 2) Z
        (finiteFieldConst d * M.delta * finiteFieldScale m n k) ∧
      (∀ omega, cutoffShellBlockLinfty m n k omega ≤ ENNReal.ofReal (Z omega)) := by
  by_cases hkn : k ≤ (n : ℤ)
  · let Z : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := smallCubeBlockEnvelope (n + 1) m (n : ℤ) 0
    have hZtail := isBigOWith_gammaTwo_smallCubeBlockEnvelope M
      (n + 1) m (n : ℤ) 0 (by omega)
    have hscale := smallCubeBlockScale_ownScale_le M (n + 1) m
    have hcount : ((m - (n + 1) + 1 : ℕ) : ℝ) = ((m - n : ℕ) : ℝ) := by
      congr 1
      omega
    rw [hcount] at hscale
    have hscale' : smallCubeBlockScale M (n + 1) m (n : ℤ) ≤
        smallCubeBlockConst * Real.sqrt ((m - n : ℕ) : ℝ) * M.delta := by
      simpa using hscale
    refine ⟨Z, measurable_smallCubeBlockEnvelope _ _ _ _,
      smallCubeBlockEnvelope_nonneg _ _ _ _, ?_, ?_⟩
    · refine hZtail.mono_scale (hscale'.trans ?_)
      have hC : smallCubeBlockConst ≤ finiteFieldConst d := by
        unfold finiteFieldConst
        have hgamma : 1 ≤ gammaTriangleConst 2 := one_le_gammaTriangleConst_two
        have hcov := (coveredLowBlockConst_pos M).le
        have hsmall := smallCubeBlockConst_pos.le
        nlinarith
      have hsqrt := Real.sqrt_nonneg ((m - n : ℕ) : ℝ)
      have hdelta := M.shellPrefix.delta_pos.le
      have hmaxzero : max 0 ((k : ℝ) - n) = 0 := by
        rw [max_eq_left]
        have hkR : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
        linarith
      rw [finiteFieldScale, hmaxzero, add_zero]
      calc
        smallCubeBlockConst * Real.sqrt ((m - n : ℕ) : ℝ) * M.delta =
            smallCubeBlockConst * M.delta * Real.sqrt ((m - n : ℕ) : ℝ) := by ring
        _ ≤ finiteFieldConst d * M.delta * Real.sqrt ((m - n : ℕ) : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hC hdelta) hsqrt
    · intro omega
      unfold cutoffShellBlockLinfty
      refine iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
      have hxN := openCubeSet_origin_mono hkn x.2
      simpa [Z, show ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) by omega] using
        abs_cutoffShellSum_le_smallCubeBlockEnvelope
          (d := d) (n + 1) m (n : ℤ) 0 (by norm_num) omega
          (by simpa using hxN)
  · have hnk : (n : ℤ) < k := lt_of_not_ge hkn
    have hk0 : 0 ≤ k := le_trans (Int.natCast_nonneg n) hnk.le
    have hkcast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
    let ell : ℕ := min m k.toNat
    have hnell : n < ell := by
      dsimp [ell]
      rw [lt_min_iff]
      constructor
      · exact hnm
      · omega
    have hellm : ell ≤ m := min_le_left _ _
    have hellk : (ell : ℤ) ≤ k := by
      rw [← hkcast]
      exact_mod_cast (min_le_right m k.toNat)
    let L : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := coveredLowBlockEnvelope n ell k
    have hLtail := isBigOWith_gammaTwo_coveredLowBlockEnvelope M n ell k
      hnk hnell hellk
    by_cases helm : ell = m
    · refine ⟨L, measurable_coveredLowBlockEnvelope _ _ _,
        coveredLowBlockEnvelope_nonneg _ _ _, ?_, ?_⟩
      · refine hLtail.mono_scale ?_
        have hC : coveredLowBlockConst d ≤ finiteFieldConst d := by
          unfold finiteFieldConst
          have hgamma : 1 ≤ gammaTriangleConst 2 := one_le_gammaTriangleConst_two
          have hcov := (coveredLowBlockConst_pos M).le
          have hsmall := smallCubeBlockConst_pos.le
          nlinarith
        have hr : (0 : ℝ) ≤ (k : ℝ) - n := by exact_mod_cast (sub_nonneg.mpr hnk.le)
        rw [finiteFieldScale, max_eq_right hr]
        push_cast
        calc
          coveredLowBlockConst d * M.delta * ((k : ℝ) - n) ≤
              finiteFieldConst d * M.delta * ((k : ℝ) - n) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hC M.shellPrefix.delta_pos.le) hr
          _ ≤ finiteFieldConst d * M.delta *
              (Real.sqrt ((m - n : ℕ) : ℝ) + ((k : ℝ) - n)) := by
            exact mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_left (Real.sqrt_nonneg _))
              (mul_nonneg (finiteFieldConst_pos M).le M.shellPrefix.delta_pos.le)
      · intro omega
        unfold cutoffShellBlockLinfty
        refine iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
        simpa [L, helm] using
          abs_lowBlock_le_coveredLowBlockEnvelope (d := d) n ell k omega x.2
    · have helm' : ell < m := lt_of_le_of_ne hellm helm
      let H : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
        smallCubeBlockEnvelope (ell + 1) m (ell : ℤ) 0
      have hHtail0 := isBigOWith_gammaTwo_smallCubeBlockEnvelope M
        (ell + 1) m (ell : ℤ) 0 (by omega)
      have hHscale := smallCubeBlockScale_ownScale_le M (ell + 1) m
      have hHcount : ((m - (ell + 1) + 1 : ℕ) : ℝ) =
          ((m - ell : ℕ) : ℝ) := by congr 1; omega
      rw [hHcount] at hHscale
      have hHscale' : smallCubeBlockScale M (ell + 1) m (ell : ℤ) ≤
          smallCubeBlockConst * Real.sqrt ((m - ell : ℕ) : ℝ) * M.delta := by
        simpa using hHscale
      have hHtail := hHtail0.mono_scale hHscale'
      have hsum := isBigOWith_gammaTwo_add_nonneg M
        (measurable_coveredLowBlockEnvelope n ell k)
        (measurable_smallCubeBlockEnvelope (ell + 1) m (ell : ℤ) 0)
        (coveredLowBlockEnvelope_nonneg n ell k)
        (smallCubeBlockEnvelope_nonneg (ell + 1) m (ell : ℤ) 0)
        (mul_pos (mul_pos (coveredLowBlockConst_pos M) M.shellPrefix.delta_pos)
          (by exact_mod_cast sub_pos.mpr hnk))
        (mul_pos (mul_pos smallCubeBlockConst_pos
          (Real.sqrt_pos.mpr (by exact_mod_cast
            (Nat.sub_pos_iff_lt.mpr helm')))) M.shellPrefix.delta_pos)
        hLtail hHtail
      refine ⟨fun omega => L omega + H omega,
        (measurable_coveredLowBlockEnvelope n ell k).add
          (measurable_smallCubeBlockEnvelope (ell + 1) m (ell : ℤ) 0),
        fun omega => add_nonneg (coveredLowBlockEnvelope_nonneg _ _ _ _)
          (smallCubeBlockEnvelope_nonneg _ _ _ _ _), ?_, ?_⟩
      · refine hsum.mono_scale ?_
        have hr : (0 : ℝ) ≤ (k : ℝ) - n := by exact_mod_cast (sub_nonneg.mpr hnk.le)
        have hsqrtMono : Real.sqrt ((m - ell : ℕ) : ℝ) ≤
            Real.sqrt ((m - n : ℕ) : ℝ) := by
          apply Real.sqrt_le_sqrt
          exact_mod_cast Nat.sub_le_sub_left hnell.le m
        rw [finiteFieldScale, max_eq_right hr]
        unfold finiteFieldConst
        push_cast
        have hgamma := (gammaTriangleConst_pos (σ := 2)).le
        have hcov := (coveredLowBlockConst_pos M).le
        have hsmall := smallCubeBlockConst_pos.le
        have hdelta := M.shellPrefix.delta_pos.le
        calc
          gammaTriangleConst 2 *
              (coveredLowBlockConst d * M.delta * ((k : ℝ) - n) +
                smallCubeBlockConst * Real.sqrt ((m - ell : ℕ) : ℝ) * M.delta) ≤
            gammaTriangleConst 2 *
              (coveredLowBlockConst d * M.delta * ((k : ℝ) - n) +
                smallCubeBlockConst * Real.sqrt ((m - n : ℕ) : ℝ) * M.delta) := by
              gcongr
          _ ≤ gammaTriangleConst 2 *
              (coveredLowBlockConst d + smallCubeBlockConst) * M.delta *
                (Real.sqrt ((m - n : ℕ) : ℝ) + ((k : ℝ) - n)) := by
              have hsqrt0 := Real.sqrt_nonneg ((m - n : ℕ) : ℝ)
              have hcross1 : 0 ≤ coveredLowBlockConst d *
                  Real.sqrt ((m - n : ℕ) : ℝ) := mul_nonneg hcov hsqrt0
              have hcross2 : 0 ≤ smallCubeBlockConst * ((k : ℝ) - n) :=
                mul_nonneg hsmall hr
              have hinner : coveredLowBlockConst d * ((k : ℝ) - n) +
                    smallCubeBlockConst * Real.sqrt ((m - n : ℕ) : ℝ) ≤
                  (coveredLowBlockConst d + smallCubeBlockConst) *
                    (Real.sqrt ((m - n : ℕ) : ℝ) + ((k : ℝ) - n)) := by
                nlinarith
              calc
                gammaTriangleConst 2 *
                    (coveredLowBlockConst d * M.delta * ((k : ℝ) - n) +
                      smallCubeBlockConst * Real.sqrt ((m - n : ℕ) : ℝ) * M.delta) =
                  gammaTriangleConst 2 * M.delta *
                    (coveredLowBlockConst d * ((k : ℝ) - n) +
                      smallCubeBlockConst * Real.sqrt ((m - n : ℕ) : ℝ)) := by ring
                _ ≤ gammaTriangleConst 2 * M.delta *
                    ((coveredLowBlockConst d + smallCubeBlockConst) *
                      (Real.sqrt ((m - n : ℕ) : ℝ) + ((k : ℝ) - n))) := by
                  exact mul_le_mul_of_nonneg_left hinner (mul_nonneg hgamma hdelta)
                _ = _ := by ring
      · intro omega
        unfold cutoffShellBlockLinfty
        refine iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
        have hsplit := cutoffShellSum_split m n ell hnell.le hellm x.1 omega
        rw [hsplit]
        calc
          |cutoffShellSum ell (n : ℤ) x.1 omega +
              cutoffShellSum m (ell : ℤ) x.1 omega| ≤
            |cutoffShellSum ell (n : ℤ) x.1 omega| +
              |cutoffShellSum m (ell : ℤ) x.1 omega| := abs_add_le _ _
          _ ≤ L omega + H omega := add_le_add
            (abs_lowBlock_le_coveredLowBlockEnvelope (d := d) n ell k omega x.2)
            (by
              have hellNat : ell = k.toNat := by
                dsimp [ell] at helm ⊢
                omega
              have hxEll : x.1 ∈ openCubeSet (originCube d (ell : ℤ)) := by
                rw [hellNat, hkcast]
                exact x.2
              simpa [H, show ((ell + 1 : ℕ) : ℤ) - 1 = (ell : ℤ) by omega]
                using abs_cutoffShellSum_le_smallCubeBlockEnvelope
                  (d := d) (ell + 1) m (ell : ℤ) 0 (by norm_num) omega
                  (by simpa using hxEll))

/-! ## Lognormal transfer for the finite field bound -/

/-- Literal forward `L^∞` cutoff-ratio observable, in the exact shell
representation proved in `CutoffMoments`. -/
noncomputable def cutoffRatioLinfty (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (m n : ℕ) (k : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ≥0∞ :=
  ⨆ x : CubePoint d k, ENNReal.ofReal
    |Real.exp (cutoffShellSum m (n : ℤ) x.1 omega -
      ((m - n : ℕ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1|

/-- Literal inverse `L^∞` cutoff-ratio observable. -/
noncomputable def inverseCutoffRatioLinfty
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (m n : ℕ) (k : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ≥0∞ :=
  ⨆ x : CubePoint d k, ENNReal.ofReal
    |Real.exp (-cutoffShellSum m (n : ℤ) x.1 omega +
      ((m - n : ℕ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1|

private theorem abs_exp_sub_one_le_exp_abs_sub_one (t : ℝ) :
    |Real.exp t - 1| ≤ Real.exp |t| - 1 := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht, abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp ht))]
  · have ht0 : t ≤ 0 := le_of_not_ge ht
    rw [abs_of_nonpos ht0, abs_of_nonpos (sub_nonpos.mpr
      (Real.exp_le_one_iff.mpr ht0))]
    have hpos := Real.add_one_le_exp t
    have hneg := Real.add_one_le_exp (-t)
    nlinarith

private theorem ratio_observables_le_exp_majorant
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m n : ℕ) (k : ℤ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) {Z : ℝ} (hZ0 : 0 ≤ Z)
    (hblock : cutoffShellBlockLinfty m n k omega ≤ ENNReal.ofReal Z) :
    cutoffRatioLinfty M m n k omega ≤
        ENNReal.ofReal (Real.exp
          (Z + ((m - n : ℕ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1) ∧
      inverseCutoffRatioLinfty M m n k omega ≤
        ENNReal.ofReal (Real.exp
          (Z + ((m - n : ℕ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1) := by
  have hb0 : 0 ≤ ((m - n : ℕ) : ℝ) *
      _root_.SubdiffusiveProcess.Model.tauSq M.P := mul_nonneg (by positivity)
    M.G4.tauSq_pos.le
  have hpoint : ∀ x : CubePoint d k,
      |cutoffShellSum m (n : ℤ) x.1 omega| ≤ Z := by
    intro x
    have hx := le_iSup (fun y : CubePoint d k => ENNReal.ofReal
      |cutoffShellSum m (n : ℤ) y.1 omega|) x
    have hof := hx.trans hblock
    exact (ENNReal.ofReal_le_ofReal_iff hZ0).mp hof
  constructor
  · unfold cutoffRatioLinfty
    refine iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
    let S := cutoffShellSum m (n : ℤ) x.1 omega
    let b := ((m - n : ℕ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P
    have hSb : |S - b| ≤ Z + b := by
      calc
        |S - b| ≤ |S| + |b| := abs_sub _ _
        _ = |S| + b := by rw [abs_of_nonneg hb0]
        _ ≤ Z + b := add_le_add (hpoint x) le_rfl
    calc
      |Real.exp (S - b) - 1| ≤ Real.exp |S - b| - 1 :=
        abs_exp_sub_one_le_exp_abs_sub_one _
      _ ≤ Real.exp (Z + b) - 1 := sub_le_sub_right (Real.exp_le_exp.mpr hSb) 1
  · unfold inverseCutoffRatioLinfty
    refine iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
    let S := cutoffShellSum m (n : ℤ) x.1 omega
    let b := ((m - n : ℕ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P
    have hSb : |-S + b| ≤ Z + b := by
      calc
        |-S + b| = |S - b| := by
          rw [show -S + b = -(S - b) by ring, abs_neg]
        _ ≤ |S| + |b| := abs_sub _ _
        _ = |S| + b := by rw [abs_of_nonneg hb0]
        _ ≤ Z + b := add_le_add (hpoint x) le_rfl
    calc
      |Real.exp (-S + b) - 1| ≤ Real.exp |-S + b| - 1 :=
        abs_exp_sub_one_le_exp_abs_sub_one _
      _ ≤ Real.exp (Z + b) - 1 := sub_le_sub_right (Real.exp_le_exp.mpr hSb) 1

/-- `e.aman.Linfty.moments`: simultaneous forward and inverse finite-cutoff
field moments.  The explicit bound is the pre-absorption version of the
paper's display; `tauSq_le_delta_sq` converts it immediately to the printed
`C(d)` shape. -/
theorem aman_Linfty_moments
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m n : ℕ) (k : ℤ)
    (hnm : n < m) (xi : ℝ) (hxi : 1 ≤ xi) :
    let A := finiteFieldConst d * M.delta * finiteFieldScale m n k
    let b := ((m - n : ℕ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P
    ∃ W : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ,
      Measurable W ∧ (∀ omega, 0 ≤ W omega) ∧
      Integrable (fun omega => W omega ^ xi) M.P.toMeasure ∧
      (∫ omega, W omega ^ xi ∂M.P.toMeasure) ^ xi⁻¹ ≤
        2 * gammaMomentConst 2 * Real.sqrt (2 * xi) * (A + b) *
          Real.exp (xi * A ^ 2 + b) ∧
      (∀ omega, cutoffRatioLinfty M m n k omega ≤ ENNReal.ofReal (W omega)) ∧
      (∀ omega,
        inverseCutoffRatioLinfty M m n k omega ≤ ENNReal.ofReal (W omega)) := by
  dsimp only
  obtain ⟨Z, hZm, hZ0, hZtail, hZdom⟩ :=
    infrared_approx_cutoffs_field M m n k hnm
  let A := finiteFieldConst d * M.delta * finiteFieldScale m n k
  let b := ((m - n : ℕ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P
  let W : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega => Real.exp (Z omega + b) - 1
  have hA : 0 < A := mul_pos
    (mul_pos (finiteFieldConst_pos M) M.shellPrefix.delta_pos)
    (finiteFieldScale_pos hnm k)
  have hb0 : 0 ≤ b := mul_nonneg (by positivity)
    M.G4.tauSq_pos.le
  have hZbig : IsBigO M.P.toMeasure (gammaSigma 2) Z A := by
    simpa [IsBigO, abs_of_nonneg (hZ0 _), A] using hZtail
  have htransfer := integral_abs_exp_sub_const_sub_one_rpow_root_le
    (mu := M.P.toMeasure) (X := Z) (A := A) (p := xi) (b := -b)
    hA hxi hZm.aemeasurable hZbig
  have hWnonneg : ∀ omega, 0 ≤ W omega := fun omega =>
    sub_nonneg.mpr (Real.one_le_exp (add_nonneg (hZ0 omega) hb0))
  have hWfun : (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => W omega ^ xi) =
      fun omega => |Real.exp (Z omega - -b) - 1| ^ xi := by
    funext omega
    rw [sub_neg_eq_add, abs_of_nonneg (hWnonneg omega)]
  have hratios : ∀ omega,
      cutoffRatioLinfty M m n k omega ≤ ENNReal.ofReal (W omega) ∧
      inverseCutoffRatioLinfty M m n k omega ≤ ENNReal.ofReal (W omega) :=
    fun omega => ratio_observables_le_exp_majorant M m n k omega
      (hZ0 omega) (hZdom omega)
  refine ⟨W, (Real.measurable_exp.comp (hZm.add_const b)).sub_const 1,
    hWnonneg, ?_, ?_, fun omega => (hratios omega).1,
    fun omega => (hratios omega).2⟩
  · rw [hWfun]
    exact htransfer.1
  · rw [hWfun]
    simpa only [abs_neg, abs_of_nonneg hb0, sub_neg_eq_add] using htransfer.2

/-- Explicit prefactor constant after absorbing the deterministic drift into
the lognormal exponential. -/
def finiteFieldMomentConst (d : ℕ) : ℝ :=
  2 * gammaMomentConst 2 * Real.sqrt 2 *
    (finiteFieldConst d + Real.log 2 / 2)

/-- Explicit exponent constant in the printed source shape. -/
def finiteFieldMomentExpConst (d : ℕ) : ℝ :=
  2 * finiteFieldConst d ^ 2 + 2 * (Real.log 2 / 2) + 2

/-- The printed `C(d) sqrt(xi) delta S exp(C(d) xi delta² Q)` form of
`e.aman.Linfty.moments`, retaining the common measurable majorant for the
two literal spatial suprema. -/
theorem aman_Linfty_moments_source_bound
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m n : ℕ) (k : ℤ)
    (hnm : n < m) (xi : ℝ) (hxi : 1 ≤ xi) :
    let S := Real.sqrt ((m - n : ℕ) : ℝ) + max 0 ((k : ℝ) - n)
    let Q := ((m - n : ℕ) : ℝ) + (max 0 ((k : ℝ) - n)) ^ 2
    ∃ W : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ,
      Measurable W ∧ (∀ omega, 0 ≤ W omega) ∧
      Integrable (fun omega => W omega ^ xi) M.P.toMeasure ∧
      (∫ omega, W omega ^ xi ∂M.P.toMeasure) ^ xi⁻¹ ≤
        finiteFieldMomentConst d * Real.sqrt xi * M.delta * S *
          Real.exp (finiteFieldMomentExpConst d * xi * M.delta ^ 2 * Q) ∧
      (∀ omega, cutoffRatioLinfty M m n k omega ≤ ENNReal.ofReal (W omega)) ∧
      (∀ omega,
        inverseCutoffRatioLinfty M m n k omega ≤ ENNReal.ofReal (W omega)) := by
  dsimp only
  obtain ⟨W, hWm, hW0, hWint, hWbound, hWfwd, hWinv⟩ :=
    aman_Linfty_moments M m n k hnm xi hxi
  let L : ℝ := (m - n : ℕ)
  let r : ℝ := max 0 ((k : ℝ) - n)
  let S : ℝ := Real.sqrt L + r
  let Q : ℝ := L + r ^ 2
  let C₀ : ℝ := finiteFieldConst d
  let c : ℝ := Real.log 2 / 2
  let p : ℝ := M.delta * S
  let q : ℝ := Real.sqrt xi * p
  let A : ℝ := C₀ * p
  let b : ℝ := L * _root_.SubdiffusiveProcess.Model.tauSq M.P
  have hLpos : 0 < L := by
    dsimp [L]
    exact_mod_cast (Nat.sub_pos_iff_lt.mpr hnm)
  have hr0 : 0 ≤ r := by dsimp [r]; exact le_max_left _ _
  have hsqrtL0 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have hSpos : 0 < S := add_pos_of_pos_of_nonneg
    (Real.sqrt_pos.mpr hLpos) hr0
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hxi0 : 0 ≤ xi := zero_le_one.trans hxi
  have hsqrtXi : 1 ≤ Real.sqrt xi := by
    nlinarith [Real.sq_sqrt hxi0, Real.sqrt_nonneg xi]
  have hp0 : 0 < p := mul_pos M.shellPrefix.delta_pos hSpos
  have hq0 : 0 < q := mul_pos (lt_of_lt_of_le zero_lt_one hsqrtXi) hp0
  have hSsq : S ^ 2 ≤ 2 * Q := by
    have hsqrtSq : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt hLpos.le
    dsimp [S, Q]
    nlinarith [sq_nonneg (Real.sqrt L - r)]
  have hpSq : p ^ 2 = M.delta ^ 2 * S ^ 2 := by
    dsimp [p]
    ring
  have hqSq : q ^ 2 = xi * M.delta ^ 2 * S ^ 2 := by
    dsimp [q, p]
    rw [mul_pow, Real.sq_sqrt hxi0]
    ring
  have hdeltaL_le_pSq : M.delta ^ 2 * L ≤ p ^ 2 := by
    rw [hpSq]
    have hLS : L ≤ S ^ 2 := by
      have hsqrtSq : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt hLpos.le
      dsimp [S]
      nlinarith
    exact mul_le_mul_of_nonneg_left hLS (sq_nonneg M.delta)
  have hp_le_q : p ≤ q := by
    dsimp [q]
    exact le_mul_of_one_le_left hp0.le hsqrtXi
  have hqExp : q ≤ Real.exp (q ^ 2) := self_le_exp_sq hq0.le
  have hpExp : p ≤ p * Real.exp (q ^ 2) := by
    simpa [mul_comm] using
      (le_mul_of_one_le_left hp0.le (Real.one_le_exp (sq_nonneg q)))
  have hb : b ≤ c * p ^ 2 := by
    dsimp [b, c, L]
    calc
      ((m - n : ℕ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P ≤
          ((m - n : ℕ) : ℝ) * ((Real.log 2 / 2) * M.delta ^ 2) :=
        mul_le_mul_of_nonneg_left (tauSq_le_delta_sq M) (by positivity)
      _ = (Real.log 2 / 2) * (M.delta ^ 2 * ((m - n : ℕ) : ℝ)) := by ring
      _ ≤ (Real.log 2 / 2) * p ^ 2 := by
        gcongr
  have hpSq_le_pExp : p ^ 2 ≤ p * Real.exp (q ^ 2) := by
    calc
      p ^ 2 ≤ p * q := by
        simpa [pow_two] using mul_le_mul_of_nonneg_left hp_le_q hp0.le
      _ ≤ p * Real.exp (q ^ 2) := mul_le_mul_of_nonneg_left hqExp hp0.le
  have hAb : A + b ≤ (C₀ + c) * p * Real.exp (q ^ 2) := by
    have hC0 : 0 ≤ C₀ := (finiteFieldConst_pos M).le
    have hc0 : 0 ≤ c := by
      dsimp [c]
      positivity
    dsimp [A]
    calc
      C₀ * p + b ≤ C₀ * p + c * p ^ 2 := add_le_add (le_refl _) hb
      _ ≤ C₀ * (p * Real.exp (q ^ 2)) +
          c * (p * Real.exp (q ^ 2)) := add_le_add
        (mul_le_mul_of_nonneg_left hpExp hC0)
        (mul_le_mul_of_nonneg_left hpSq_le_pExp hc0)
      _ = (C₀ + c) * p * Real.exp (q ^ 2) := by ring
  have hExp : xi * A ^ 2 + b + q ^ 2 ≤
      (2 * C₀ ^ 2 + 2 * c + 2) * xi * M.delta ^ 2 * Q := by
    have hC0 : 0 ≤ C₀ := (finiteFieldConst_pos M).le
    have hc0 : 0 ≤ c := by dsimp [c]; positivity
    have hA2 : xi * A ^ 2 ≤ 2 * C₀ ^ 2 * xi * M.delta ^ 2 * Q := by
      calc
        xi * A ^ 2 = C₀ ^ 2 * xi * p ^ 2 := by
          dsimp [A]
          ring
        _ = C₀ ^ 2 * xi * (M.delta ^ 2 * S ^ 2) := by rw [hpSq]
        _ ≤ C₀ ^ 2 * xi * (M.delta ^ 2 * (2 * Q)) := by gcongr
        _ = 2 * C₀ ^ 2 * xi * M.delta ^ 2 * Q := by ring
    have hbQ : b ≤ 2 * c * xi * M.delta ^ 2 * Q := by
      calc
        b ≤ c * p ^ 2 := hb
        _ = c * (M.delta ^ 2 * S ^ 2) := by rw [hpSq]
        _ ≤ c * (M.delta ^ 2 * (2 * Q)) := by gcongr
        _ ≤ 2 * c * xi * M.delta ^ 2 * Q := by
          have hbase0 : 0 ≤ 2 * c * M.delta ^ 2 * Q := by positivity
          calc
            c * (M.delta ^ 2 * (2 * Q)) =
                2 * c * M.delta ^ 2 * Q := by ring
            _ ≤ (2 * c * M.delta ^ 2 * Q) * xi :=
              le_mul_of_one_le_right hbase0 hxi
            _ = _ := by ring
    have hqQ : q ^ 2 ≤ 2 * xi * M.delta ^ 2 * Q := by
      calc
        q ^ 2 = xi * M.delta ^ 2 * S ^ 2 := hqSq
        _ ≤ xi * M.delta ^ 2 * (2 * Q) :=
          mul_le_mul_of_nonneg_left hSsq
            (mul_nonneg hxi0 (sq_nonneg M.delta))
        _ = 2 * xi * M.delta ^ 2 * Q := by ring
    nlinarith [hA2, hbQ, hqQ]
  refine ⟨W, hWm, hW0, hWint, hWbound.trans ?_, hWfwd, hWinv⟩
  have hsqrtTwoXi : Real.sqrt (2 * xi) = Real.sqrt 2 * Real.sqrt xi := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hExpMono := Real.exp_le_exp.mpr hExp
  rw [hsqrtTwoXi]
  have hAeq : finiteFieldConst d * M.delta * finiteFieldScale m n k = A := by
    dsimp [A, C₀, p, S, L, r, finiteFieldScale]
    ring
  have hbeq : ((m - n : ℕ) : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P = b := by
    rfl
  rw [hAeq, hbeq]
  change 2 * gammaMomentConst 2 * (Real.sqrt 2 * Real.sqrt xi) *
      (A + b) * Real.exp (xi * A ^ 2 + b) ≤ _
  calc
    2 * gammaMomentConst 2 * (Real.sqrt 2 * Real.sqrt xi) *
        (A + b) * Real.exp (xi * A ^ 2 + b) ≤
      2 * gammaMomentConst 2 * (Real.sqrt 2 * Real.sqrt xi) *
        ((C₀ + c) * p * Real.exp (q ^ 2)) *
          Real.exp (xi * A ^ 2 + b) := by
      have hK0 : 0 ≤ 2 * gammaMomentConst 2 *
          (Real.sqrt 2 * Real.sqrt xi) :=
        mul_nonneg (mul_nonneg (by norm_num) (gammaMomentConst_pos (by norm_num)).le)
          (mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg xi))
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hAb hK0) (Real.exp_pos _).le
    _ = 2 * gammaMomentConst 2 * Real.sqrt 2 * (C₀ + c) *
          Real.sqrt xi * M.delta * S *
          Real.exp (xi * A ^ 2 + b + q ^ 2) := by
      have hexp : Real.exp (q ^ 2) * Real.exp (xi * A ^ 2 + b) =
          Real.exp (xi * A ^ 2 + b + q ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        2 * gammaMomentConst 2 * (Real.sqrt 2 * Real.sqrt xi) *
            ((C₀ + c) * p * Real.exp (q ^ 2)) * Real.exp (xi * A ^ 2 + b) =
          2 * gammaMomentConst 2 * Real.sqrt 2 * (C₀ + c) *
            Real.sqrt xi * p *
              (Real.exp (q ^ 2) * Real.exp (xi * A ^ 2 + b)) := by ring
        _ = 2 * gammaMomentConst 2 * Real.sqrt 2 * (C₀ + c) *
            Real.sqrt xi * M.delta * S *
              Real.exp (xi * A ^ 2 + b + q ^ 2) := by
          rw [hexp]
          dsimp [p]
          ring
    _ ≤ 2 * gammaMomentConst 2 * Real.sqrt 2 * (C₀ + c) *
        Real.sqrt xi * M.delta * S *
          Real.exp ((2 * C₀ ^ 2 + 2 * c + 2) * xi * M.delta ^ 2 * Q) := by
      have hpref0 : 0 ≤ 2 * gammaMomentConst 2 * Real.sqrt 2 * (C₀ + c) *
          Real.sqrt xi * M.delta * S := by
        have hc0 : 0 ≤ c := by dsimp [c]; positivity
        have hgm : 0 ≤ gammaMomentConst 2 :=
          (gammaMomentConst_pos (by norm_num)).le
        have hCsum : 0 ≤ C₀ + c :=
          add_nonneg (finiteFieldConst_pos M).le hc0
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg (by positivity) (Real.sqrt_nonneg 2)) hCsum)
              (Real.sqrt_nonneg xi))
            M.shellPrefix.delta_pos.le)
          hSpos.le
      exact mul_le_mul_of_nonneg_left hExpMono hpref0
    _ = finiteFieldMomentConst d * Real.sqrt xi * M.delta *
        (Real.sqrt ((m - n : ℕ) : ℝ) + max 0 ((k : ℝ) - n)) *
          Real.exp (finiteFieldMomentExpConst d * xi * M.delta ^ 2 *
            (((m - n : ℕ) : ℝ) + (max 0 ((k : ℝ) - n)) ^ 2)) := by
      simp only [finiteFieldMomentConst, finiteFieldMomentExpConst]
      dsimp [C₀, c, S, Q, L, r]

end

end SubdiffusiveProcess.CoarseGrainingVocab
