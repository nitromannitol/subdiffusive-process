module

public import SubdiffusiveProcess.CoarseGrainingVocab.ShellSensitivity
public import SubdiffusiveProcess.Assumptions.OGammaBridge
public import Homogenization.Book.Ch04.Theorems.Concentration
@[expose] public section

/-!
# The head of the clock fluctuation: `√(n+1)`

`clockFluctuation n ω z` (Section 11) splits as

    ∑_{k ≤ n} ω_k(0)   −   ∑'_{k > n} (ω_k(z) − ω_k(0)),

and only the first term needs independence: it is a sum of `n+1` **centred, independent**
shell values, each with a `Γ₂` tail at scale `≍ δ`, so the sum has scale `≍ δ √(n+1)` — not
`δ (n+1)`, which is all the triangle inequality gives.

Everything used here was already in the tree:

* `ShellLawPrefix.independent` — the shells are independent in `k`;
* `ShellLawG1.mean_zero` with `map_unscalePotential_coordinate_eq_zero` — each `ω_k(0)` is
  centred, since the unscaled `k`-th coordinate has exactly the zero-shell law;
* `ShellSensitivity.isBigOWith_gammaTwo_translatedShellG2` — the per-shell `Γ₂` scale,
  uniform in the shell index and the translate;
* `Homogenization.Book.Ch04.isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero`
  — **the `√card`**, for independent centred summands at `0 < σ ≤ 2`;
* `SubdiffusiveProcess.OGammaBridge.{isBigO_gammaSigma_of_ogammaLE, ogammaLE_of_isBigO_gammaSigma}` — the two
  directions between the formalization's `OGammaLE` and CoarseGraining's tail predicate.

The constant is selected before the model and before `n`, as the Section 11 anchor requires.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory _root_.SubdiffusiveProcess.Model
open Homogenization IndependentSums
open Homogenization.Book

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section11

variable {d : ℕ}

/-- Each shell value at the origin is dominated by its own translated `g₂` gauge. -/
theorem abs_shell_origin_le_translatedShellG2 (k : ℕ) (omega : PotentialSample d) :
    |omega k 0| ≤ translatedShellG2 k 0 omega := by
  have hmem : (0 : Homogenization.Vec d) ∈ Homogenization.openCubeSet
      (Homogenization.originCube d 0) := by
    intro i
    constructor <;> simp [Homogenization.cubeScaleFactor, Homogenization.originCube]
  have h := _root_.SubdiffusiveProcess.Model.PotentialField.abs_apply_le_g2Observable
    (_root_.SubdiffusiveProcess.Model.PotentialField.translate (0 : Homogenization.Vec d)
      (unscalePotential k (omega k))) hmem
  simpa [translatedShellG2, unscalePotential,
    _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale_apply, smul_zero] using h

/-- Each shell value at the origin is centred: the unscaled `k`-th coordinate has exactly the
zero-shell law, and `G1` centres that. -/
theorem integral_shell_origin_eq_zero (M : GMCModel d) (k : ℕ) :
    ∫ omega : PotentialSample d, omega k 0 ∂M.P.toMeasure = 0 := by
  have hmap := map_unscalePotential_coordinate_eq_zero M k
  have hshift : ∀ omega : PotentialSample d,
      omega k 0 = (unscalePotential k (omega k)) 0 := by
    intro omega
    simp [unscalePotential, _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale_apply, smul_zero]
  have hzero : (zeroPotentialLaw M.P).toMeasure
      = Measure.map (fun omega : PotentialSample d => omega 0) M.P.toMeasure := by
    rw [zeroPotentialLaw, potentialMarginalLaw, ProbabilityMeasure.toMeasure_map]
  calc ∫ omega : PotentialSample d, omega k 0 ∂M.P.toMeasure
      = ∫ omega : PotentialSample d, (unscalePotential k (omega k)) 0 ∂M.P.toMeasure :=
        integral_congr_ae (Filter.Eventually.of_forall hshift)
    _ = ∫ g : PotentialField d, g 0
          ∂(Measure.map (fun omega : PotentialSample d => unscalePotential k (omega k))
            M.P.toMeasure) := by
        exact (integral_map (μ := M.P.toMeasure)
          (φ := fun omega : PotentialSample d => unscalePotential k (omega k))
          (f := fun g : PotentialField d => g 0)
          ((measurable_unscalePotential k).comp
            (measurable_potentialCoordinate k)).aemeasurable
          (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval _).aestronglyMeasurable).symm
    _ = ∫ g : PotentialField d, g 0 ∂(zeroPotentialLaw M.P).toMeasure := by rw [hmap]
    _ = ∫ omega : PotentialSample d, omega 0 0 ∂M.P.toMeasure := by
        rw [hzero]
        exact integral_map (μ := M.P.toMeasure)
          (φ := fun omega : PotentialSample d => omega 0)
          (f := fun g : PotentialField d => g 0)
          (measurable_potentialCoordinate 0).aemeasurable
          (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval _).aestronglyMeasurable
    _ = 0 := M.G1.mean_zero 0

/-- The shell values at the origin are independent in the shell index. -/
theorem iIndepFun_shell_origin (M : GMCModel d) :
    iIndepFun (fun (k : ℕ) (omega : PotentialSample d) => omega k 0) M.P.toMeasure :=
  M.shellPrefix.independent.comp (fun _ (g : PotentialField d) => g 0)
    (fun _ => _root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval _)

/-- The per-shell `Γ₂` scale at the origin, uniform in the shell index. -/
theorem isBigO_gammaTwo_shell_origin (M : GMCModel d) (k : ℕ) :
    IsBigO M.P.toMeasure (gammaSigma 2)
      (fun omega : PotentialSample d => omega k 0)
      ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) := by
  have hgauge : IsBigO M.P.toMeasure (gammaSigma 2) (translatedShellG2 k 0)
      ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) := by
    simpa [IsBigO, abs_of_nonneg (translatedShellG2_nonneg k 0 _)] using
      isBigOWith_gammaTwo_translatedShellG2 M k 0
  refine hgauge.of_abs_le fun omega => ?_
  rw [abs_of_nonneg (translatedShellG2_nonneg k 0 omega)]
  exact abs_shell_origin_le_translatedShellG2 k omega

/-- **The head of the clock fluctuation has `Γ₂` scale `≍ δ √(n+1)`.**

The constant is selected before the model and before `n`.  The square root — rather than the
`n + 1` the triangle inequality would give — is bought by independence of the shells, through
CoarseGraining's exponential-regime concentration theorem. -/
theorem exists_ogammaLE_shellHead (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : GMCModel d) (n : ℕ),
      SubdiffusiveProcess.OGammaLE M.P.toMeasure 2 (C * Real.sqrt ((n : ℝ) + 1) * M.delta)
        (fun omega : PotentialSample d => ∑ k ∈ Finset.range (n + 1), omega k 0) := by
  have hconst : 0 < gammaSigmaExpRegimeEndpointConst 2 := by
    dsimp [gammaSigmaExpRegimeEndpointConst]
    rw [ite_eq_right (by norm_num : (2 : ℝ) ≠ 1)]
    have hExp : 0 < IndependentSums.gammaSigmaExpRegimeConst 2 := by
      dsimp [IndependentSums.gammaSigmaExpRegimeConst]
      exact lt_of_lt_of_le
        (mul_pos (by positivity) (IndependentSums.gammaMomentConst_pos (by norm_num)))
        (le_max_left _ _)
    linarith
  have hlog : (0 : ℝ) < (1 + Real.log 2) ^ (2 : ℝ)⁻¹ := by
    have : (0 : ℝ) < 1 + Real.log 2 := by
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); linarith
    exact Real.rpow_pos_of_pos this _
  refine ⟨2 * gammaSigmaExpRegimeEndpointConst 2 * (1 + Real.log 2) ^ (2 : ℝ)⁻¹,
    by positivity, ?_⟩
  intro M n
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hK : 0 < (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta := by positivity
  have hsum :=
    Ch04.isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero_expRegime
    (μ := M.P.toMeasure)
    (X := fun (k : ℕ) (omega : PotentialSample d) => omega k 0)
    (s := Finset.range (n + 1)) (σ := 2)
    (K := (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)
    (iIndepFun_shell_origin M)
    (fun k => (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval _).comp (measurable_potentialCoordinate k))
    (Finset.nonempty_range_add_one) (by norm_num) le_rfl hK
    (fun k _ => isBigO_gammaTwo_shell_origin M k)
    (fun k _ => integral_shell_origin_eq_zero M k)
  have hcard : ((Finset.range (n + 1)).card : ℝ) = (n : ℝ) + 1 := by
    simp
  rw [hcard] at hsum
  have hbridge := SubdiffusiveProcess.OGammaBridge.ogammaLE_of_isBigO_gammaSigma
    (μ := M.P.toMeasure) (σ := 2)
    (A := gammaSigmaExpRegimeEndpointConst 2 * Real.sqrt ((n : ℝ) + 1) *
      ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta))
    (X := fun omega : PotentialSample d => ∑ k ∈ Finset.range (n + 1), omega k 0)
    (by norm_num)
    (by positivity)
    (Finset.measurable_sum _ fun k _ =>
      (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval _).comp (measurable_potentialCoordinate k))
    hsum
  have hfour : ((4 : ℝ) ^ (2 : ℝ)⁻¹) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 2,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [hfour] at hbridge
  have hscale : 2 * gammaSigmaExpRegimeEndpointConst 2 * (1 + Real.log 2) ^ (2 : ℝ)⁻¹ *
        Real.sqrt ((n : ℝ) + 1) * M.delta
      = 2 * (gammaSigmaExpRegimeEndpointConst 2 * Real.sqrt ((n : ℝ) + 1) *
          ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) := by ring
  rw [hscale]
  exact hbridge

/-! ### Shell values at an arbitrary point, and the increments -/

/-- Every shell value is the unscaled shell value at the rescaled point. -/
theorem shell_apply_eq_unscale (k : ℕ) (omega : PotentialSample d)
    (y : Homogenization.Vec d) :
    omega k y = (unscalePotential k (omega k)) (((3 : ℝ) ^ k)⁻¹ • y) := by
  have h3 : ((3 : ℝ) ^ k) ≠ 0 := by positivity
  simp only [unscalePotential, _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale_apply, smul_smul,
    mul_inv_cancel₀ h3, one_smul]

/-- Each shell value is integrable, transported from `G1` at the zero shell. -/
theorem integrable_shell_apply (M : GMCModel d) (k : ℕ) (y : Homogenization.Vec d) :
    Integrable (fun omega : PotentialSample d => omega k y) M.P.toMeasure := by
  have hzero : (zeroPotentialLaw M.P).toMeasure
      = Measure.map (fun omega : PotentialSample d => omega 0) M.P.toMeasure := by
    rw [zeroPotentialLaw, potentialMarginalLaw, ProbabilityMeasure.toMeasure_map]
  have hbase : Integrable (fun g : PotentialField d => g (((3 : ℝ) ^ k)⁻¹ • y))
      (zeroPotentialLaw M.P).toMeasure := by
    rw [hzero]
    refine (integrable_map_measure ?_ ?_).mpr (M.G1.integrable _)
    · exact (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval _).aestronglyMeasurable
    · exact (measurable_potentialCoordinate 0).aemeasurable
  have hmap := map_unscalePotential_coordinate_eq_zero M k
  have hpull : Integrable
      (fun omega : PotentialSample d =>
        (unscalePotential k (omega k)) (((3 : ℝ) ^ k)⁻¹ • y)) M.P.toMeasure := by
    refine (integrable_map_measure ?_ ?_).mp (by rw [hmap]; exact hbase)
    · exact (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval _).aestronglyMeasurable
    · exact ((measurable_unscalePotential k).comp
        (measurable_potentialCoordinate k)).aemeasurable
  exact hpull.congr (Filter.Eventually.of_forall fun omega =>
    (shell_apply_eq_unscale k omega y).symm)

/-- Each shell value is centred, at every point. -/
theorem integral_shell_apply_eq_zero (M : GMCModel d) (k : ℕ) (y : Homogenization.Vec d) :
    ∫ omega : PotentialSample d, omega k y ∂M.P.toMeasure = 0 := by
  have hmap := map_unscalePotential_coordinate_eq_zero M k
  have hzero : (zeroPotentialLaw M.P).toMeasure
      = Measure.map (fun omega : PotentialSample d => omega 0) M.P.toMeasure := by
    rw [zeroPotentialLaw, potentialMarginalLaw, ProbabilityMeasure.toMeasure_map]
  calc ∫ omega : PotentialSample d, omega k y ∂M.P.toMeasure
      = ∫ omega : PotentialSample d,
          (unscalePotential k (omega k)) (((3 : ℝ) ^ k)⁻¹ • y) ∂M.P.toMeasure :=
        integral_congr_ae (Filter.Eventually.of_forall fun omega =>
          shell_apply_eq_unscale k omega y)
    _ = ∫ g : PotentialField d, g (((3 : ℝ) ^ k)⁻¹ • y)
          ∂(Measure.map (fun omega : PotentialSample d =>
            unscalePotential k (omega k)) M.P.toMeasure) := by
        exact (integral_map (μ := M.P.toMeasure)
          (φ := fun omega : PotentialSample d => unscalePotential k (omega k))
          (f := fun g : PotentialField d => g (((3 : ℝ) ^ k)⁻¹ • y))
          ((measurable_unscalePotential k).comp
            (measurable_potentialCoordinate k)).aemeasurable
          (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval _).aestronglyMeasurable).symm
    _ = ∫ g : PotentialField d, g (((3 : ℝ) ^ k)⁻¹ • y)
          ∂(zeroPotentialLaw M.P).toMeasure := by rw [hmap]
    _ = ∫ omega : PotentialSample d, omega 0 (((3 : ℝ) ^ k)⁻¹ • y) ∂M.P.toMeasure := by
        rw [hzero]
        exact integral_map (μ := M.P.toMeasure)
          (φ := fun omega : PotentialSample d => omega 0)
          (f := fun g : PotentialField d => g (((3 : ℝ) ^ k)⁻¹ • y))
          (measurable_potentialCoordinate 0).aemeasurable
          (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval _).aestronglyMeasurable
    _ = 0 := M.G1.mean_zero _

/-- **The shell increments are centred.**  This is what lets the tail of the clock
fluctuation use independence, and hence pick up `√(log(2+|x|))` rather than `log(2+|x|)`. -/
theorem integral_shell_increment_eq_zero (M : GMCModel d) (k : ℕ)
    (z : Homogenization.Vec d) :
    ∫ omega : PotentialSample d, (omega k z - omega k 0) ∂M.P.toMeasure = 0 := by
  rw [integral_sub (integrable_shell_apply M k z) (integrable_shell_apply M k 0),
    integral_shell_apply_eq_zero M k z, integral_shell_apply_eq_zero M k 0, sub_zero]

/-! ### The engine, abstracted

The head sum is one instance of a general fact: a family of **shell-local**, centred
functionals with a uniform `Γ₂` scale has a sum whose scale grows like `√card`.  The tail of
the clock fluctuation needs the same fact for the shell *increments* `ω_k(z) − ω_k(0)`, which
are shell-local and centred for the same reasons, so it is worth stating once. -/

/-- A shell-local functional: `F k` depends on the sample only through the `k`-th shell. -/
def ShellLocal (F : ℕ → PotentialSample d → ℝ) : Prop :=
  ∀ k, ∃ f : PotentialField d → ℝ, Measurable f ∧ ∀ omega, F k omega = f (omega k)

/-- The shell increments are shell-local. -/
theorem shellLocal_increment (z : Homogenization.Vec d) :
    ShellLocal (fun (k : ℕ) (omega : PotentialSample d) => omega k z - omega k 0) := by
  intro k
  exact ⟨fun g => g z - g 0,
    (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval z).sub (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval 0),
    fun _ => rfl⟩

theorem iIndepFun_of_shellLocal (M : GMCModel d) {F : ℕ → PotentialSample d → ℝ}
    (hF : ShellLocal F) : iIndepFun F M.P.toMeasure := by
  classical
  choose f hfmeas hfeq using hF
  have h := M.shellPrefix.independent.comp f hfmeas
  refine h.congr ?_
  intro k
  exact Filter.Eventually.of_forall fun omega => (hfeq k omega).symm

/-- **The independent-sum engine.**  A nonempty finite family of shell-local, centred
functionals with a common `Γ₂` scale `K` has a sum of scale `C √card · K`. -/
theorem exists_ogammaLE_shellFamilySum (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : GMCModel d) (F : ℕ → PotentialSample d → ℝ)
      (s : Finset ℕ) (K : ℝ), s.Nonempty → 0 < K → ShellLocal F →
      (∀ k, Measurable (F k)) →
      (∀ k ∈ s, ∫ omega, F k omega ∂M.P.toMeasure = 0) →
      (∀ k ∈ s, IsBigO M.P.toMeasure (gammaSigma 2) (F k) K) →
      SubdiffusiveProcess.OGammaLE M.P.toMeasure 2 (C * Real.sqrt (s.card : ℝ) * K)
        (fun omega => ∑ k ∈ s, F k omega) := by
  have hconst : 0 < gammaSigmaExpRegimeEndpointConst 2 := by
    dsimp [gammaSigmaExpRegimeEndpointConst]
    rw [ite_eq_right (by norm_num : (2 : ℝ) ≠ 1)]
    have hExp : 0 < IndependentSums.gammaSigmaExpRegimeConst 2 := by
      dsimp [IndependentSums.gammaSigmaExpRegimeConst]
      exact lt_of_lt_of_le
        (mul_pos (by positivity) (IndependentSums.gammaMomentConst_pos (by norm_num)))
        (le_max_left _ _)
    linarith
  refine ⟨2 * gammaSigmaExpRegimeEndpointConst 2, by positivity, ?_⟩
  intro M F s K hs hK hlocal hmeas hcen hbig
  have hsum :=
    Ch04.isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero_expRegime
    (μ := M.P.toMeasure) (X := F) (s := s) (σ := 2) (K := K)
    (iIndepFun_of_shellLocal M hlocal) hmeas hs (by norm_num) le_rfl hK hbig hcen
  have hbridge := SubdiffusiveProcess.OGammaBridge.ogammaLE_of_isBigO_gammaSigma
    (μ := M.P.toMeasure) (σ := 2)
    (A := gammaSigmaExpRegimeEndpointConst 2 * Real.sqrt (s.card : ℝ) * K)
    (X := fun omega : PotentialSample d => ∑ k ∈ s, F k omega)
    (by norm_num) (by positivity)
    (Finset.measurable_sum _ fun k _ => hmeas k) hsum
  have hfour : ((4 : ℝ) ^ (2 : ℝ)⁻¹) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 2,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [hfour] at hbridge
  have hscale : 2 * gammaSigmaExpRegimeEndpointConst 2 * Real.sqrt (s.card : ℝ) * K
      = 2 * (gammaSigmaExpRegimeEndpointConst 2 * Real.sqrt (s.card : ℝ) * K) := by ring
  rw [hscale]
  exact hbridge

/-! ### The middle-field regime of the tail

Between `3^n` and the separation, the shell increments are *not* geometrically small: each is
a full-size shell value.  What saves the estimate is that there are only about
`log₃(2+|x|)` of them and they are independent and centred, so the engine turns that count
into its square root.  Each is dominated by two translated `g₂` gauges, whose `Γ₂` scale
`isBigOWith_gammaTwo_translatedShellG2` gives **uniformly in the translate** — which is why
the per-shell scale does not grow with the separation. -/

/-- A shell value at any point is dominated by its translated `g₂` gauge. -/
theorem abs_shell_apply_le_translatedShellG2 (k : ℕ) (omega : PotentialSample d)
    (y : Homogenization.Vec d) :
    |omega k y| ≤ translatedShellG2 k (((3 : ℝ) ^ k)⁻¹ • y) omega := by
  have hmem : (0 : Homogenization.Vec d) ∈ Homogenization.openCubeSet
      (Homogenization.originCube d 0) := by
    intro i
    constructor <;> simp [Homogenization.cubeScaleFactor, Homogenization.originCube]
  have h := _root_.SubdiffusiveProcess.Model.PotentialField.abs_apply_le_g2Observable
    (_root_.SubdiffusiveProcess.Model.PotentialField.translate (((3 : ℝ) ^ k)⁻¹ • y) (unscalePotential k (omega k))) hmem
  have h3 : ((3 : ℝ) ^ k) ≠ 0 := by positivity
  have hval : (_root_.SubdiffusiveProcess.Model.PotentialField.translate (((3 : ℝ) ^ k)⁻¹ • y)
      (unscalePotential k (omega k))) 0 = omega k y := by
    simp only [_root_.SubdiffusiveProcess.Model.PotentialField.translate_apply, zero_add, unscalePotential,
      _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale_apply, smul_smul, mul_inv_cancel₀ h3, one_smul]
  rwa [hval] at h

/-- Each shell increment is dominated by two translated `g₂` gauges. -/
theorem abs_shell_increment_le_add (k : ℕ) (omega : PotentialSample d)
    (z : Homogenization.Vec d) :
    |omega k z - omega k 0|
      ≤ translatedShellG2 k (((3 : ℝ) ^ k)⁻¹ • z) omega
        + translatedShellG2 k (((3 : ℝ) ^ k)⁻¹ • (0 : Homogenization.Vec d)) omega := by
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · exact abs_shell_apply_le_translatedShellG2 k omega z
  · exact abs_shell_apply_le_translatedShellG2 k omega 0

/-- **The middle-field sum.**  Instantiating the engine at the shell increments: a finite set
of shells, each increment carrying a common `Γ₂` scale `K`, sums to scale `C √card · K`.
Centring is `integral_shell_increment_eq_zero` and locality is `shellLocal_increment`, so the
only input left to the caller is the per-shell scale, which
`isBigOWith_gammaTwo_translatedShellG2` supplies through `abs_shell_increment_le_add`. -/
theorem exists_ogammaLE_shellIncrementSum (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : GMCModel d) (z : Homogenization.Vec d)
      (s : Finset ℕ) (K : ℝ), s.Nonempty → 0 < K →
      (∀ k ∈ s, IsBigO M.P.toMeasure (gammaSigma 2)
        (fun omega : PotentialSample d => omega k z - omega k 0) K) →
      SubdiffusiveProcess.OGammaLE M.P.toMeasure 2 (C * Real.sqrt (s.card : ℝ) * K)
        (fun omega : PotentialSample d => ∑ k ∈ s, (omega k z - omega k 0)) := by
  obtain ⟨C, hC, hengine⟩ := exists_ogammaLE_shellFamilySum d
  refine ⟨C, hC, ?_⟩
  intro M z s K hs hK hbig
  refine hengine M (fun k omega => omega k z - omega k 0) s K hs hK
    (shellLocal_increment z) ?_ ?_ hbig
  · intro k
    exact ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval z).comp (measurable_potentialCoordinate k)).sub
      ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval 0).comp (measurable_potentialCoordinate k))
  · intro k _
    exact integral_shell_increment_eq_zero M k z

/-- **The negated head.**  `ogammaLE_shellMax` needs a bound on `-S_m` as well as on `S_m`,
and the negated shell values are shell-local, centred and `Γ₂` for exactly the same reasons,
so the same engine delivers it at the same scale. -/
theorem exists_ogammaLE_shellHeadNeg (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : GMCModel d) (n : ℕ),
      SubdiffusiveProcess.OGammaLE M.P.toMeasure 2 (C * Real.sqrt ((n : ℝ) + 1) * M.delta)
        (fun omega : PotentialSample d => -∑ k ∈ Finset.range (n + 1), omega k 0) := by
  obtain ⟨C, hC, hengine⟩ := exists_ogammaLE_shellFamilySum d
  refine ⟨C * (1 + Real.log 2) ^ (2 : ℝ)⁻¹, ?_, ?_⟩
  · have : (0 : ℝ) < (1 + Real.log 2) ^ (2 : ℝ)⁻¹ := by
      have h : (0:ℝ) < 1 + Real.log 2 := by
        have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2); linarith
      exact Real.rpow_pos_of_pos h _
    positivity
  intro M n
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hK : 0 < (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta := by
    have h : (0:ℝ) < 1 + Real.log 2 := by
      have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2); linarith
    have := Real.rpow_pos_of_pos h (2 : ℝ)⁻¹
    positivity
  have hres := hengine M (fun k omega => -(omega k 0)) (Finset.range (n + 1))
    ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) Finset.nonempty_range_add_one hK
    (fun k => ⟨fun g => -(g 0), (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval 0).neg, fun _ => rfl⟩)
    (fun k => ((_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval 0).comp
      (measurable_potentialCoordinate k)).neg)
    (fun k _ => by
      rw [integral_neg, integral_shell_origin_eq_zero M k, neg_zero])
    (fun k _ => (isBigO_gammaTwo_shell_origin M k).of_abs_le (fun omega => by simp))
  have hcard : ((Finset.range (n + 1)).card : ℝ) = (n : ℝ) + 1 := by simp
  rw [hcard] at hres
  have hfun : (fun omega : PotentialSample d => ∑ k ∈ Finset.range (n + 1), -(omega k 0))
      = fun omega : PotentialSample d => -∑ k ∈ Finset.range (n + 1), omega k 0 := by
    funext omega
    rw [Finset.sum_neg_distrib]
  rw [hfun] at hres
  have hscale : C * (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * Real.sqrt ((n : ℝ) + 1) * M.delta
      = C * Real.sqrt ((n : ℝ) + 1) * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) := by ring
  rw [hscale]
  exact hres

/-- **The per-shell `Γ₂` scale for an increment**, uniform in the shell index *and* in the two
points.  Each increment is dominated by two translated `g₂` gauges, and
`isBigOWith_gammaTwo_translatedShellG2` gives those a common scale regardless of the
translate — which is exactly why the increments' scale does not grow with `|z|`. -/
theorem isBigO_gammaTwo_shell_increment (M : GMCModel d) (k : ℕ)
    (z : Homogenization.Vec d) :
    IsBigO M.P.toMeasure (gammaSigma 2)
      (fun omega : PotentialSample d => omega k z - omega k 0)
      (Ch04.gammaTriangleConst 2 * (2 * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta))) := by
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hlog : (0 : ℝ) < (1 + Real.log 2) ^ (2 : ℝ)⁻¹ := by
    have h : (0:ℝ) < 1 + Real.log 2 := by
      have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2); linarith
    exact Real.rpow_pos_of_pos h _
  set w0 : Homogenization.Vec d := ((3 : ℝ) ^ k)⁻¹ • z with hw0
  set w1 : Homogenization.Vec d := ((3 : ℝ) ^ k)⁻¹ • (0 : Homogenization.Vec d) with hw1
  set G : Fin 2 → PotentialSample d → ℝ :=
    fun i => if i = 0 then translatedShellG2 k w0 else translatedShellG2 k w1 with hG
  have hGbig : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      IsBigO M.P.toMeasure (gammaSigma 2) (G i)
        ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) := by
    intro i _
    have hgen : ∀ w : Homogenization.Vec d, IsBigO M.P.toMeasure (gammaSigma 2)
        (translatedShellG2 k w) ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) := by
      intro w
      simpa [IsBigO, abs_of_nonneg (translatedShellG2_nonneg k w _)] using
        isBigOWith_gammaTwo_translatedShellG2 M k w
    by_cases hi : i = 0
    · simpa [hG, hi] using hgen w0
    · simpa [hG, hi] using hgen w1
  have hGm : ∀ i ∈ (Finset.univ : Finset (Fin 2)), Measurable (G i) := by
    intro i _
    by_cases hi : i = 0
    · simpa [hG, hi] using measurable_translatedShellG2 k w0
    · simpa [hG, hi] using measurable_translatedShellG2 k w1
  have hsum := Ch04.isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := M.P.toMeasure) (Finset.univ : Finset (Fin 2)) (σ := 2)
    (X := G) (a := fun _ => (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)
    (by norm_num) ⟨0, Finset.mem_univ 0⟩ (fun i _ => by positivity) hGbig hGm
  have hcard : ∑ _i : Fin 2, (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta
      = 2 * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) := by
    simp [Finset.sum_const]
  rw [hcard] at hsum
  refine hsum.of_abs_le fun omega => ?_
  have hsplit : ∑ i : Fin 2, G i omega
      = translatedShellG2 k w0 omega + translatedShellG2 k w1 omega := by
    rw [Fin.sum_univ_two]
    simp [hG]
  have hnn : (0:ℝ) ≤ ∑ i : Fin 2, G i omega := by
    rw [hsplit]
    exact add_nonneg (translatedShellG2_nonneg k w0 omega)
      (translatedShellG2_nonneg k w1 omega)
  rw [abs_of_nonneg hnn, hsplit]
  simpa [hw0, hw1] using abs_shell_increment_le_add k omega z

end SubdiffusiveProcess.CoarseGrainingVocab.Section11