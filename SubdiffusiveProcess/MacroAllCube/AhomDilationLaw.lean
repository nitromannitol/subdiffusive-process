module

public import SubdiffusiveProcess.CoarseGrainingVocab.AhomCharacterization
public import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedProviders
public import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedMatrixVariational
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletInfimumCovariance
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletMatrixBridge

@[expose] public section

/-!
# Law transport and annealed Dirichlet functionals under a seed dilation

Let `M, M'` be two GMC models whose seed laws satisfy
`law(M') = law(M) ∘ (spatialScale t)⁻¹` for some `t > 0`.  Then:

* `map_dilateSample`: dilating every layer by `t` carries `M.P` onto `M'.P`
  (both are the independent products of their triadic marginals, and the
  triadic and real dilations commute);
* `aCutoff_dilateSample`: the finite cutoff of `M'` at the dilated sample is the
  cutoff of `M` at the dilated point (`τ²` is unchanged);
* the annealed Dirichlet functional of `M` on the dilated cube `t • Q` is
  `t^d` times the annealed Dirichlet functional of `M'` on `Q`, i.e.
  `t^d |Q|` times the triadic scalar readout of `M'`;
* the annealed affine remainder `E ∫_R a` is `|R|` (the cutoff is mean one).

No scale invariance of the seed law is assumed anywhere.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Homogenization.Book
open Homogenization hiding Vec TriadicCube
open _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open scoped Pointwise

noncomputable section

namespace SubdiffusiveProcess.AhomDilation

variable {d : ℕ}

/-! ## Dilating a sample layer by layer -/

/-- Dilate every layer of a potential sample by the same real factor. -/
def dilateSample (t : ℝ) (ω : PotentialSample d) : PotentialSample d :=
  fun k => _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale t (ω k)

theorem measurable_dilateSample (t : ℝ) : Measurable (dilateSample (d := d) t) := by
  apply measurable_pi_iff.mpr
  intro k
  exact (_root_.SubdiffusiveProcess.Model.PotentialField.continuous_spatialScale t).measurable.comp
    (measurable_potentialCoordinate k)

theorem spatialScale_triadicScale (t : ℝ) (k : ℕ) (g : PotentialField d) :
    _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale t (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k g) =
      _root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k (_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale t g) := by
  apply _root_.SubdiffusiveProcess.Model.PotentialField.ext
  intro x
  simp only [_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale_apply, _root_.SubdiffusiveProcess.Model.PotentialField.triadicScale_apply]
  rw [smul_smul, smul_smul, mul_comm]

/-- The one-layer marginal of a model, as a pushforward of the seed. -/
theorem map_coord_eq (M : GMCModel d) (k : ℕ) :
    Measure.map (fun ω : PotentialSample d => ω k) M.P.toMeasure =
      Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k) (zeroPotentialLaw M.P).toMeasure := by
  have hscale := congrArg ProbabilityMeasure.toMeasure (M.shellPrefix.marginal_scaling k)
  change (potentialMarginalLaw M.P k).toMeasure =
    Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k) (zeroPotentialLaw M.P).toMeasure at hscale
  exact hscale

/-- **Law transport.**  If the seed of `M'` is the seed of `M` dilated by `t`, the
layerwise dilation carries the sample law of `M` onto that of `M'`. -/
theorem map_dilateSample {M M' : GMCModel d} {t : ℝ}
    (hseed : (zeroPotentialLaw M'.P).toMeasure =
      Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale t) (zeroPotentialLaw M.P).toMeasure) :
    Measure.map (dilateSample t) M.P.toMeasure = M'.P.toMeasure := by
  have hS : Measurable (_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale (d := d) t) :=
    (_root_.SubdiffusiveProcess.Model.PotentialField.continuous_spatialScale t).measurable
  have hInd : iIndepFun (fun k : ℕ => fun ω : PotentialSample d =>
      _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale t (ω k)) M.P.toMeasure :=
    M.shellPrefix.independent.comp (fun _ => _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale t) (fun _ => hS)
  have hProd := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun k : ℕ => hS.comp (measurable_potentialCoordinate (d := d) k))).mp hInd
  have hProd' := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun k : ℕ => measurable_potentialCoordinate (d := d) k)).mp
      M'.shellPrefix.independent
  have hmarg : ∀ k : ℕ,
      Measure.map (fun ω : PotentialSample d => _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale t (ω k))
          M.P.toMeasure =
        Measure.map (fun ω : PotentialSample d => ω k) M'.P.toMeasure := by
    intro k
    have hcomp : (fun ω : PotentialSample d => _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale t (ω k)) =
        _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale t ∘ (fun ω : PotentialSample d => ω k) := rfl
    rw [hcomp, ← Measure.map_map hS (measurable_potentialCoordinate k),
      map_coord_eq, map_coord_eq, hseed,
      Measure.map_map hS (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_triadicScale k),
      Measure.map_map (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_triadicScale k) hS]
    congr 1
    funext g
    exact spatialScale_triadicScale t k g
  calc Measure.map (dilateSample t) M.P.toMeasure
      = Measure.infinitePi (fun k : ℕ =>
          Measure.map (fun ω : PotentialSample d => _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale t (ω k))
            M.P.toMeasure) := hProd
    _ = Measure.infinitePi (fun k : ℕ =>
          Measure.map (fun ω : PotentialSample d => ω k) M'.P.toMeasure) := by
        congr 1
        funext k
        exact hmarg k
    _ = Measure.map (fun ω (k : ℕ) => ω k) M'.P.toMeasure := hProd'.symm
    _ = M'.P.toMeasure := Measure.map_id'

/-- The zero-point exponential moment is unchanged by a seed dilation. -/
theorem tauSq_eq_of_seed {M M' : GMCModel d} {t : ℝ}
    (hseed : (zeroPotentialLaw M'.P).toMeasure =
      Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale t) (zeroPotentialLaw M.P).toMeasure) :
    tauSq M'.P = tauSq M.P := by
  unfold tauSq
  rw [hseed, integral_map (_root_.SubdiffusiveProcess.Model.PotentialField.continuous_spatialScale t).measurable.aemeasurable
    (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval 0).exp.aestronglyMeasurable]
  simp only [_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale_apply, smul_zero]

/-- The inverse dilation: the seed of `M` is the seed of `M'` dilated by `t⁻¹`. -/
theorem seed_inv {M M' : GMCModel d} {t : ℝ} (ht : t ≠ 0)
    (hseed : (zeroPotentialLaw M'.P).toMeasure =
      Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale t) (zeroPotentialLaw M.P).toMeasure) :
    (zeroPotentialLaw M.P).toMeasure =
      Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale t⁻¹) (zeroPotentialLaw M'.P).toMeasure := by
  rw [hseed, Measure.map_map (_root_.SubdiffusiveProcess.Model.PotentialField.continuous_spatialScale t⁻¹).measurable
    (_root_.SubdiffusiveProcess.Model.PotentialField.continuous_spatialScale t).measurable]
  have hid : (_root_.SubdiffusiveProcess.Model.PotentialField.spatialScale (d := d) t⁻¹ ∘ _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale t) =
      id := by
    funext g
    apply _root_.SubdiffusiveProcess.Model.PotentialField.ext
    intro x
    simp only [Function.comp_apply, _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale_apply, smul_smul,
      mul_inv_cancel₀ ht, one_smul, id]
  rw [hid, Measure.map_id]

/-- **The cutoff at a dilated sample.** -/
theorem aCutoff_dilateSample {M M' : GMCModel d} (htau : tauSq M'.P = tauSq M.P)
    (t : ℝ) (n : ℕ) (ω : PotentialSample d) (x : Vec d) :
    aCutoff M' n (dilateSample t ω) x = aCutoff M n ω (t • x) := by
  simp only [aCutoff, dilateSample, _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale_apply, htau]

/-! ## The Dirichlet functional of a sample -/

/-- The continuum Dirichlet minimum of the cutoff coefficient of one sample. -/
def dirFun (M : GMCModel d) (n : ℕ) (U : Set (Vec d)) (p : Vec d)
    (ω : PotentialSample d) : ℝ :=
  dirichletInfOn (aCutoff M n ω) U p

theorem dirFun_nonneg (M : GMCModel d) (n : ℕ) {U : Set (Vec d)} (hU : MeasurableSet U)
    (p : Vec d) (ω : PotentialSample d) : 0 ≤ dirFun M n U p ω :=
  dirichletInfOn_nonneg hU fun x => (aCutoff_pos M n ω x).le

/-- On a triadic cube the Dirichlet minimum is the volume times the quadratic
form of the random coarse matrix. -/
theorem dirFun_cube (M : GMCModel d) (n : ℕ) (Q : TriadicCube d) (p : Vec d)
    (ω : PotentialSample d) :
    dirFun M n (openCubeSet Q) p ω =
      (volume (openCubeSet Q)).toReal *
        vecDot p (matVecMul (randomAMatrix M n (Ch02.cubeDomain Q) ω) p) := by
  have h := vecDot_aMatrix_eq_dirichletInfOn
    (aCutoffCoeffOnData M n ω (Ch02.cubeDomain Q)) (fun x => (aCutoff_pos M n ω x).le) p
  have hvol : (volume (openCubeSet Q)).toReal ≠ 0 :=
    ne_of_gt (volume_toReal_pos (Ch02.cubeDomain Q))
  have hR : randomAMatrix M n (Ch02.cubeDomain Q) ω =
      aMatrix (Ch02.cubeDomain Q) (aCutoffCoeffOnData M n ω (Ch02.cubeDomain Q)).toCoeffOn :=
    rfl
  rw [hR, h]
  change dirichletInfOn (aCutoff M n ω) (openCubeSet Q) p =
    (volume (openCubeSet Q)).toReal *
      ((volume (openCubeSet Q)).toReal⁻¹ * dirichletInfOn (aCutoff M n ω) (openCubeSet Q) p)
  field_simp

theorem measurable_quad (M : GMCModel d) (n : ℕ) (U : Ch02.Domain d) (p : Vec d) :
    Measurable (fun ω : PotentialSample d =>
      vecDot p (matVecMul (randomAMatrix M n U ω) p)) := by
  have hA := measurable_randomAMatrix M n U
  simp only [vecDot, matVecMul]
  apply Finset.measurable_sum
  intro i _
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA)).mul_const _

theorem measurable_dirFun_cube (M : GMCModel d) (n : ℕ) (Q : TriadicCube d) (p : Vec d) :
    Measurable (dirFun M n (openCubeSet Q) p) := by
  rw [funext (dirFun_cube M n Q p)]
  exact (measurable_quad M n (Ch02.cubeDomain Q) p).const_mul _

theorem integrable_dirFun_cube (M : GMCModel d) (n : ℕ) (Q : TriadicCube d) (p : Vec d) :
    Integrable (dirFun M n (openCubeSet Q) p) M.P.toMeasure := by
  rw [funext (dirFun_cube M n Q p)]
  have h := (integrable_randomAMatrix_quadratic M n (Ch02.cubeDomain Q) p).const_mul
    (2 * (volume (openCubeSet Q)).toReal)
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only
  ring

theorem integral_quad (M : GMCModel d) (n : ℕ) (U : Ch02.Domain d) (p : Vec d) :
    ∫ ω, vecDot p (matVecMul (randomAMatrix M n U ω) p) ∂M.P.toMeasure =
      vecDot p (matVecMul (abar M n U) p) := by
  have h := integral_randomAMatrix_quadratic M n U p
  rw [integral_const_mul] at h
  linarith

theorem integral_dirFun_cube (M : GMCModel d) (n : ℕ) (Q : TriadicCube d) (p : Vec d) :
    ∫ ω, dirFun M n (openCubeSet Q) p ω ∂M.P.toMeasure =
      (volume (openCubeSet Q)).toReal *
        vecDot p (matVecMul (abar M n (Ch02.cubeDomain Q)) p) := by
  rw [funext (dirFun_cube M n Q p), integral_const_mul, integral_quad]

/-- The quadratic form of `abar` on any triadic cube of scale `l` in a unit
coordinate direction is the scalar readout at scale `l`. -/
theorem quad_abar_single (M : GMCModel d) (n l : ℕ) (k : Fin d → ℤ) (i : Fin d) :
    vecDot (Pi.single i 1) (matVecMul
        (abar M n (Ch02.cubeDomain (⟨(l : ℤ), k⟩ : TriadicCube d))) (Pi.single i 1)) =
      abarScalarReadout M n l := by
  rw [abar_cube_eq_originCube]
  change vecDot (Pi.single i 1) (matVecMul
    (abar M n (Ch02.cubeDomain (originCube d (l : ℤ)))) (Pi.single i 1)) = _
  rw [abar_eq_abarScalarReadout_smul_one, matVecMul_single, vecDot_single_left]
  simp

/-! ## Dilated cubes -/

/-- **The dilated-cube functional.**  The Dirichlet minimum of the `M` cutoff on
`t • U` is `t^d` times the Dirichlet minimum of the `M'` cutoff at the dilated
sample on `U`. -/
theorem dirFun_smul {M M' : GMCModel d} (htau : tauSq M'.P = tauSq M.P) {t : ℝ}
    (ht : 0 < t) (n : ℕ) {U : Set (Vec d)} (hU : MeasurableSet U) (p : Vec d)
    (ω : PotentialSample d) :
    dirFun M n (t • U) p ω = t ^ d * dirFun M' n U p (dilateSample t ω) := by
  have h := dirichletInfOn_comp_smul (B := aCutoff M n ω) (U := U) (p := p) ht hU
    (fun x => (aCutoff_pos M n ω x).le)
  have hfun : (fun y => aCutoff M n ω (t • y)) = aCutoff M' n (dilateSample t ω) :=
    funext fun y => (aCutoff_dilateSample htau t n ω y).symm
  rw [hfun] at h
  unfold dirFun
  rw [h]
  have hpow : (t ^ d) ≠ 0 := pow_ne_zero d ht.ne'
  field_simp

theorem integrable_dirFun_smul_cube {M M' : GMCModel d} {t : ℝ} (ht : 0 < t)
    (hmap : Measure.map (dilateSample t) M.P.toMeasure = M'.P.toMeasure)
    (htau : tauSq M'.P = tauSq M.P) (n : ℕ) (Q : TriadicCube d) (p : Vec d) :
    Integrable (dirFun M n (t • openCubeSet Q) p) M.P.toMeasure := by
  have hmeasQ : MeasurableSet (openCubeSet Q) := (Ch02.cubeDomain Q).measurableSet
  rw [funext (dirFun_smul htau ht n hmeasQ p)]
  have hcomp : Integrable (fun ω => dirFun M' n (openCubeSet Q) p (dilateSample t ω))
      M.P.toMeasure := by
    have h' : Integrable (dirFun M' n (openCubeSet Q) p)
        (Measure.map (dilateSample t) M.P.toMeasure) := by
      rw [hmap]; exact integrable_dirFun_cube M' n Q p
    exact (integrable_map_measure (measurable_dirFun_cube M' n Q p).aestronglyMeasurable
      (measurable_dilateSample t).aemeasurable).mp h'
  exact hcomp.const_mul _

theorem integral_dirFun_smul_cube {M M' : GMCModel d} {t : ℝ} (ht : 0 < t)
    (hmap : Measure.map (dilateSample t) M.P.toMeasure = M'.P.toMeasure)
    (htau : tauSq M'.P = tauSq M.P) (n : ℕ) (Q : TriadicCube d) (p : Vec d) :
    ∫ ω, dirFun M n (t • openCubeSet Q) p ω ∂M.P.toMeasure =
      t ^ d * ∫ ω, dirFun M' n (openCubeSet Q) p ω ∂M'.P.toMeasure := by
  have hmeasQ : MeasurableSet (openCubeSet Q) := (Ch02.cubeDomain Q).measurableSet
  rw [funext (dirFun_smul htau ht n hmeasQ p), integral_const_mul]
  congr 1
  rw [← hmap, integral_map (measurable_dilateSample t).aemeasurable
    (measurable_dirFun_cube M' n Q p).aestronglyMeasurable]

/-! ## The affine remainder is mean one -/

theorem integrable_aCutoff_prod_restrict (M : GMCModel d) (n : ℕ) {R : Set (Vec d)}
    (hR : volume R < ⊤) :
    Integrable (fun z : PotentialSample d × Vec d => aCutoff M n z.1 z.2)
      (M.P.toMeasure.prod (volume.restrict R)) := by
  have : IsFiniteMeasure (volume.restrict R) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hR⟩
  apply (integrable_prod_iff' (measurable_cutoff_uncurry M n).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun x => integrable_aCutoff_apply M n x
  · have hEq : (fun x : Vec d => ∫ ω, ‖aCutoff M n ω x‖ ∂M.P.toMeasure) =
        fun _ => (1 : ℝ) := by
      funext x
      have hn : (fun ω : PotentialSample d => ‖aCutoff M n ω x‖) =
          fun ω => aCutoff M n ω x :=
        funext fun ω => Real.norm_of_nonneg (aCutoff_pos M n ω x).le
      rw [hn]
      exact integral_aCutoff_apply M n x
    rw [hEq]
    exact integrable_const 1

theorem integrable_setIntegral_aCutoff (M : GMCModel d) (n : ℕ) {R : Set (Vec d)}
    (hR : volume R < ⊤) :
    Integrable (fun ω => ∫ x in R, aCutoff M n ω x) M.P.toMeasure :=
  (integrable_aCutoff_prod_restrict M n hR).integral_prod_left

theorem integral_setIntegral_aCutoff (M : GMCModel d) (n : ℕ) {R : Set (Vec d)}
    (hR : volume R < ⊤) :
    ∫ ω, (∫ x in R, aCutoff M n ω x) ∂M.P.toMeasure = (volume R).toReal := by
  have : IsFiniteMeasure (volume.restrict R) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hR⟩
  have hswap := integral_integral_swap (f := fun (ω : PotentialSample d) (x : Vec d) =>
    aCutoff M n ω x) (μ := M.P.toMeasure) (ν := volume.restrict R)
    (integrable_aCutoff_prod_restrict M n hR)
  rw [hswap]
  simp_rw [integral_aCutoff_apply M n]
  rw [integral_const, smul_eq_mul, mul_one, measureReal_def,
    Measure.restrict_apply_univ]

end SubdiffusiveProcess.AhomDilation
