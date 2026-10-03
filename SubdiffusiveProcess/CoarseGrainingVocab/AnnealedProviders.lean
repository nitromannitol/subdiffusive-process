module

public import SubdiffusiveProcess.CoarseGrainingVocab.MeasurabilityProviders
public import SubdiffusiveProcess.Frozen.Vocab.Abar
public import Homogenization.Book.Ch04.Theorems.AnnealedSubadditivity.BlockLoewner
public import Homogenization.CoarseGraining.Translation
public import Homogenization.Internal.Ch02.Adapters
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

/-!
# Basic providers for annealed cutoff matrices

This module supplies the integrability and one-step subdivision inputs needed
for the finite-cutoff annealed primal matrix.

The proof-role decomposition follows
`Algsuperdiff/Section3/Provider/Annealed/Monotonicity.lean`: first establish
matrix integrability, then deterministic subdivision, then commute finite
descendant averages with expectation, and finally use a real-translation
stationary transfer.  The sequence-law stationarity proof below adapts
`Algsuperdiff/Section3/Cutoff/Symmetry.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

def translatePotentialSequence {d : ℕ} (z : Vec d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d :=
  fun k => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z (omega k)

theorem measurable_translatePotentialSequence {d : ℕ} (z : Vec d) :
    Measurable (translatePotentialSequence (d := d) z) := by
  apply measurable_pi_iff.mpr
  intro k
  exact (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_translate z).comp
    (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate k)

-- PROVENANCE: adapts `Algsuperdiff.Section3.Cutoff.triadicScale_translate`.
private theorem translate_triadicScale {d : ℕ} (k : ℕ) (z : Vec d)
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k g) =
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate
          (((3 : ℝ) ^ k)⁻¹ • z) g) := by
  apply SubdiffusiveProcess.Frozen.Assumptions.PotentialField.ext
  intro x
  simp [smul_add]

-- PROVENANCE: adapts `Algsuperdiff.Section3.Cutoff.shellMarginalLaw_stationary`.
private theorem potentialMarginalLaw_stationary {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k : ℕ) (z : Vec d) :
    Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z)
        (SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P k).toMeasure =
      (SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P k).toMeasure := by
  have hscale := congrArg ProbabilityMeasure.toMeasure
    (M.shellPrefix.marginal_scaling k)
  change (SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P k).toMeasure =
    Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k)
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure at hscale
  let w : Vec d := ((3 : ℝ) ^ k)⁻¹ • z
  calc
    Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z)
        (SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P k).toMeasure =
      Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z)
        (Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k)
          (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure) := by rw [hscale]
    _ = Measure.map
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z ∘
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k)
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure :=
      Measure.map_map
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_translate z)
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_triadicScale k)
    _ = Measure.map
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k ∘
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate w)
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
      apply congrArg (fun f : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d →
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
          Measure.map f (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)
      funext g
      exact translate_triadicScale k z g
    _ = Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k)
        (Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate w)
          (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure) :=
      (Measure.map_map
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_triadicScale k)
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_translate w)).symm
    _ = Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k)
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
      rw [M.G1.stationary w]
    _ = (SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P k).toMeasure := by
      rw [hscale]

-- PROVENANCE: adapts `Algsuperdiff.Section3.Cutoff.sequenceLaw_stationary`.
theorem potentialSequenceLaw_stationary {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (z : Vec d) :
    Measure.map (translatePotentialSequence (d := d) z) M.P.toMeasure =
      M.P.toMeasure := by
  have hprod := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun k : ℕ => SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate k)).mp
      M.shellPrefix.independent
  have htransInd : iIndepFun
      (fun k : ℕ => fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z (omega k)) M.P.toMeasure :=
    M.shellPrefix.independent.comp
      (fun _ => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z)
      (fun _ => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_translate z)
  have htransProd := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun _ : ℕ =>
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_translate z).comp
        (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate _))).mp htransInd
  calc
    Measure.map (translatePotentialSequence (d := d) z) M.P.toMeasure =
      Measure.map (fun omega (k : ℕ) =>
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z (omega k))
        M.P.toMeasure := rfl
    _ = Measure.infinitePi (fun k : ℕ =>
        Measure.map (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z (omega k))
          M.P.toMeasure) := by
      simpa only [Function.comp_def] using! htransProd
    _ = Measure.infinitePi (fun k : ℕ =>
        Measure.map (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => omega k)
          M.P.toMeasure) := by
      apply congrArg Measure.infinitePi
      funext k
      calc
        Measure.map (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
            SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z (omega k))
            M.P.toMeasure =
          Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z)
            (Measure.map (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => omega k)
              M.P.toMeasure) := by
            change Measure.map
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z ∘
                fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => omega k)
              M.P.toMeasure = _
            rw [Measure.map_map
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_translate z)
              (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate k)]
        _ = Measure.map (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => omega k)
            M.P.toMeasure := potentialMarginalLaw_stationary M k z
    _ = Measure.map (fun omega (k : ℕ) => omega k) M.P.toMeasure := hprod.symm
    _ = M.P.toMeasure := Measure.map_id'

theorem aCutoff_translatePotentialSequence {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (z : Vec d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (x : Vec d) :
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
        (translatePotentialSequence (d := d) z omega) x =
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega (x + z) := by
  simp [SubdiffusiveProcess.Frozen.Assumptions.aCutoff, translatePotentialSequence]

private theorem randomAMatrix_eq_rawSigmaCoarse {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (Q : TriadicCube d) :
    randomAMatrix M L (Ch02.cubeDomain Q) omega =
      Homogenization.sigmaCoarse (Homogenization.openCubeSet Q)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)) := by
  let hdata := aCutoffCoeffOnData M L omega (Ch02.cubeDomain Q)
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
    (Ch02.cubeDomain Q) hdata.toCoeffOn hdata.isSymmetric
  calc
    randomAMatrix M L (Ch02.cubeDomain Q) omega =
        Ch02.sigmaCoarse (Ch02.cubeDomain Q) hdata.toCoeffOn :=
      hTheory.derived_matrices.1
    _ = Homogenization.sigmaCoarse (Homogenization.openCubeSet Q)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)) := by
      simpa [hdata, ScalarCoeffOnData.toCoeffOn] using
        Homogenization.Internal.Ch02.book_sigmaCoarse_eq_sigmaCoarse
          (Ch02.cubeDomain Q) hdata.toCoeffOn

-- PROVENANCE: mirrors the real-translation covariance step in
-- `Algsuperdiff/Section3/Provider/Annealed/RealStationaryTransfer.lean`.
private theorem randomAMatrix_eq_originCube_translatePotentialSequence {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (Q : TriadicCube d) :
    randomAMatrix M L (Ch02.cubeDomain Q) omega =
      randomAMatrix M L (Ch02.cubeDomain (Homogenization.originCube d Q.scale))
        (translatePotentialSequence (Homogenization.triadicCubeShift Q) omega) := by
  rw [randomAMatrix_eq_rawSigmaCoarse, randomAMatrix_eq_rawSigmaCoarse]
  rw [Homogenization.openCubeSet_eq_translateSet_originCube_of_triadicCube Q]
  rw [Homogenization.sigmaCoarse_translateSet_eq_translateCoeffField]
  apply congrArg (Homogenization.sigmaCoarse
    (Homogenization.openCubeSet (Homogenization.originCube d Q.scale)))
  funext x
  change Homogenization.scalarMatrix
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega
        (x + Homogenization.triadicCubeShift Q)) =
    Homogenization.scalarMatrix
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
        (translatePotentialSequence (Homogenization.triadicCubeShift Q) omega) x)
  exact congrArg Homogenization.scalarMatrix
    (aCutoff_translatePotentialSequence M L
      (Homogenization.triadicCubeShift Q) omega x).symm

-- PROVENANCE: sample-carrier specialization of the expectation transfer in
-- `Algsuperdiff/Section3/Provider/Annealed/RealStationaryTransfer.lean`.
theorem abar_cube_eq_originCube {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (Q : TriadicCube d) :
    abar M L (Ch02.cubeDomain Q) =
      abar M L (Ch02.cubeDomain (Homogenization.originCube d Q.scale)) := by
  unfold abar
  calc
    ∫ omega, randomAMatrix M L (Ch02.cubeDomain Q) omega ∂M.P.toMeasure =
        ∫ omega, randomAMatrix M L
          (Ch02.cubeDomain (Homogenization.originCube d Q.scale))
          (translatePotentialSequence (Homogenization.triadicCubeShift Q) omega)
          ∂M.P.toMeasure := by
      apply integral_congr_ae
      filter_upwards with omega
      exact randomAMatrix_eq_originCube_translatePotentialSequence M L omega Q
    _ = ∫ omega, randomAMatrix M L
          (Ch02.cubeDomain (Homogenization.originCube d Q.scale)) omega
          ∂M.P.toMeasure := by
      have hmeas : Measurable (fun omega i j => randomAMatrix M L
          (Ch02.cubeDomain (Homogenization.originCube d Q.scale)) omega i j) := by
        simpa only using! measurable_randomAMatrix M L
          (Ch02.cubeDomain (Homogenization.originCube d Q.scale))
      simpa only [Function.comp_def] using!
        (Homogenization.integral_comp_eq_of_map_eq (E := Fin d → Fin d → ℝ)
          (measurable_translatePotentialSequence (Homogenization.triadicCubeShift Q))
          (potentialSequenceLaw_stationary M (Homogenization.triadicCubeShift Q))
          (fun omega i j => randomAMatrix M L
            (Ch02.cubeDomain (Homogenization.originCube d Q.scale)) omega i j)
          hmeas.aestronglyMeasurable)

private theorem integrable_exp_potentialCoordinate_apply {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k : ℕ) (x : Vec d) :
    Integrable
      (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => Real.exp (ω k x))
      M.P.toMeasure := by
  let y : Vec d := (((3 : ℝ) ^ k)⁻¹) • x
  let F : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ := fun g => Real.exp (g x)
  let F0 : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ := fun g => Real.exp (g 0)
  have hF : Measurable F :=
    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval x).exp
  have hF0 : Measurable F0 :=
    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval 0).exp
  have hAtY : Integrable
      (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d => Real.exp (g y))
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
    have hMapped : Integrable F0
        (Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate y)
          (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure) := by
      rw [M.G1.stationary y]
      exact M.G4.exponential_integrable
    have hComp := (integrable_map_measure hF0.aestronglyMeasurable
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_translate y).aemeasurable).mp hMapped
    simpa [F0, Function.comp_def] using hComp
  have hScaled : Integrable F
      (Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k)
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure) := by
    apply (integrable_map_measure hF.aestronglyMeasurable
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_triadicScale k).aemeasurable).mpr
    simpa [F, Function.comp_def, y] using hAtY
  have hMarginal : Integrable F
      (SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P k).toMeasure := by
    rw [M.shellPrefix.marginal_scaling k]
    exact hScaled
  have hCoord := (integrable_map_measure hF.aestronglyMeasurable
    (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate k).aemeasurable).mp hMarginal
  simpa [F, Function.comp_def,
    SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw] using hCoord

private theorem integral_exp_potentialCoordinate_apply {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k : ℕ) (x : Vec d) :
    ∫ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d, Real.exp (ω k x)
        ∂M.P.toMeasure =
      ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, Real.exp (g 0)
        ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
  let y : Vec d := (((3 : ℝ) ^ k)⁻¹) • x
  let F : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ := fun g => Real.exp (g x)
  let F0 : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ := fun g => Real.exp (g 0)
  have hF : Measurable F :=
    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval x).exp
  have hF0 : Measurable F0 :=
    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval 0).exp
  calc
    ∫ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d, Real.exp (ω k x)
        ∂M.P.toMeasure =
      ∫ g, F g ∂(SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P k).toMeasure := by
      rw [SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw,
        ProbabilityMeasure.toMeasure_map]
      simpa [F, Function.comp_def] using
        (integral_map
          (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate k).aemeasurable
          hF.aestronglyMeasurable).symm
    _ = ∫ g, F g ∂Measure.map
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k)
          (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
      rw [M.shellPrefix.marginal_scaling k]
      rw [ProbabilityMeasure.toMeasure_map]
    _ = ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, Real.exp (g y)
          ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
      rw [integral_map
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_triadicScale k).aemeasurable
        hF.aestronglyMeasurable]
      rfl
    _ = ∫ g, F0 g ∂Measure.map
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate y)
          (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
      simpa [F0, Function.comp_def] using
        (integral_map
          (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_translate y).aemeasurable
          hF0.aestronglyMeasurable).symm
    _ = ∫ g, F0 g ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
      rw [M.G1.stationary y]

/-- Every point evaluation of a finite cutoff is integrable. -/
theorem integrable_aCutoff_apply {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (x : Vec d) :
    Integrable (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω x) M.P.toMeasure := by
  let X : ℕ → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ :=
    fun k ω => ω k x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P
  have hIndep : iIndepFun X M.P.toMeasure := by
    simpa [X, Function.comp_def] using M.shellPrefix.independent.comp
      (fun _ g => g x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
      (fun _ => (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval x).sub
        measurable_const)
  have hMeas : ∀ k, Measurable (X k) := fun k =>
    ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval x).comp
      (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate k)).sub measurable_const
  have hTerm : ∀ k ∈ Finset.range (L + 1),
      Integrable (fun ω => Real.exp (1 * X k ω)) M.P.toMeasure := by
    intro k _hk
    have h := (integrable_exp_potentialCoordinate_apply M k x).const_mul
      (Real.exp (-SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))
    convert h using 1
    funext ω
    simp only [X, one_mul]
    rw [Real.exp_sub, Real.exp_neg]
    ring
  have hSum := hIndep.integrable_exp_mul_sum (t := (1 : ℝ)) hMeas hTerm
  simpa [X, SubdiffusiveProcess.Frozen.Assumptions.aCutoff] using hSum

/-- The normalization by `tauSq` makes every finite cutoff pointwise mean one. -/
theorem integral_aCutoff_apply {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (x : Vec d) :
    ∫ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω x ∂M.P.toMeasure = 1 := by
  let X : ℕ → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ :=
    fun k ω => ω k x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P
  have hIndep : iIndepFun X M.P.toMeasure := by
    simpa [X, Function.comp_def] using M.shellPrefix.independent.comp
      (fun _ g => g x - SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
      (fun _ => (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval x).sub
        measurable_const)
  have hMeas : ∀ k, Measurable (X k) := fun k =>
    ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval x).comp
      (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate k)).sub measurable_const
  let Z : ℝ := ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d, Real.exp (g 0)
    ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure
  have hZ_nonneg : 0 ≤ Z := integral_nonneg fun _ => (Real.exp_pos _).le
  have hZ_pos : 0 < Z := by
    have hlog : 0 < Real.log Z := by
      simpa [Z, SubdiffusiveProcess.Frozen.Assumptions.tauSq] using M.G4.tauSq_pos
    exact zero_lt_one.trans ((Real.log_pos_iff hZ_nonneg).mp hlog)
  have hexp_tau : Real.exp (SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) = Z := by
    simpa [Z, SubdiffusiveProcess.Frozen.Assumptions.tauSq] using Real.exp_log hZ_pos
  have hFactor : ∀ k, ProbabilityTheory.mgf (X k) M.P.toMeasure 1 = 1 := by
    intro k
    rw [ProbabilityTheory.mgf]
    have hRaw := integral_exp_potentialCoordinate_apply M k x
    have hIntRaw := integrable_exp_potentialCoordinate_apply M k x
    calc
      ∫ ω, Real.exp (1 * X k ω) ∂M.P.toMeasure =
          Real.exp (-SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
            ∫ ω, Real.exp (ω k x) ∂M.P.toMeasure := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with ω
        simp only [X, one_mul]
        rw [Real.exp_sub, Real.exp_neg]
        ring
      _ = Real.exp (-SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * Z := by rw [hRaw]
      _ = 1 := by rw [Real.exp_neg, hexp_tau]; field_simp
  calc
    ∫ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω x ∂M.P.toMeasure =
        ProbabilityTheory.mgf (∑ k ∈ Finset.range (L + 1), X k)
          M.P.toMeasure 1 := by
      simp [ProbabilityTheory.mgf, SubdiffusiveProcess.Frozen.Assumptions.aCutoff, X,
        Finset.sum_apply]
    _ = ∏ k ∈ Finset.range (L + 1), ProbabilityTheory.mgf (X k) M.P.toMeasure 1 :=
      hIndep.mgf_sum hMeas _
    _ = 1 := by simp [hFactor]

/-- The cutoff is jointly integrable in the sample and spatial variables on
every Chapter-2 domain. -/
theorem integrable_aCutoff_prod_volumeMeasureOn {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d) :
    Integrable
      (fun z : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d =>
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L z.1 z.2)
      (M.P.toMeasure.prod (volumeMeasureOn (U : Set (Vec d)))) := by
  have hJoint : AEStronglyMeasurable
      (fun z : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d =>
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L z.1 z.2)
      (M.P.toMeasure.prod (volumeMeasureOn (U : Set (Vec d)))) :=
    (measurable_cutoff_uncurry M L).aestronglyMeasurable
  apply (integrable_prod_iff' hJoint).mpr
  constructor
  · exact Filter.Eventually.of_forall fun x => integrable_aCutoff_apply M L x
  · have hEq :
        (fun x : Vec d =>
          ∫ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
            ‖SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω x‖ ∂M.P.toMeasure) =
          fun _ => (1 : ℝ) := by
      funext x
      rw [show (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
          ‖SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω x‖) =
          fun ω => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω x by
        funext ω
        exact Real.norm_of_nonneg (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L ω x).le]
      exact integral_aCutoff_apply M L x
    rw [hEq]
    exact integrable_const 1

/-- The spatial average of a finite cutoff is integrable in the sample. -/
theorem integrable_aCutoff_average {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d) :
    Integrable (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
      Ch02.average U (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)) M.P.toMeasure := by
  have hIntegral := (integrable_aCutoff_prod_volumeMeasureOn M L U).integral_prod_left
  have hScaled := hIntegral.const_mul
    (MeasureTheory.volume (U : Set (Vec d))).toReal⁻¹
  simpa [Ch02.average, volumeMeasureOn] using hScaled

/-- The spatial average of a finite cutoff has expectation one. -/
theorem integral_aCutoff_average {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d) :
    ∫ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
        Ch02.average U (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω) ∂M.P.toMeasure = 1 := by
  have hprod := integrable_aCutoff_prod_volumeMeasureOn M L U
  have hvol : (MeasureTheory.volume (U : Set (Vec d))).toReal ≠ 0 :=
    ne_of_gt (Homogenization.Internal.Ch02.BookCh02.domain_volume_pos U)
  unfold Ch02.average
  rw [MeasureTheory.integral_const_mul]
  change (MeasureTheory.volume (U : Set (Vec d))).toReal⁻¹ *
      (∫ ω, ∫ x, SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω x
        ∂volumeMeasureOn (U : Set (Vec d)) ∂M.P.toMeasure) = 1
  rw [MeasureTheory.integral_integral_swap hprod]
  simp_rw [integral_aCutoff_apply M L]
  rw [MeasureTheory.integral_const]
  simp only [volumeMeasureOn, MeasureTheory.Measure.restrict_apply_univ,
    MeasureTheory.measureReal_def]
  simpa using inv_mul_cancel₀ hvol

private theorem abs_randomAMatrix_apply_le_aCutoff_average {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (i j : Fin d) :
    |randomAMatrix M L U ω i j| ≤
      Ch02.average U (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω) := by
  let hdata := aCutoffCoeffOnData M L ω U
  let aω := hdata.toCoeffOn
  let c := Ch02.average U (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory U aω hdata.isSymmetric
  have hDerived := hTheory.derived_matrices
  have hApsd : (aMatrix U aω).PosSemidef := by
    change (Ch02.aCoarse U aω).PosSemidef
    rw [hDerived.1, ← hDerived.2.2]
    exact Ch02.bCoarse_posSemidef U aω
  have hAverageMat :
      Ch02.averageMat U aω.toCoeffField = c • (1 : Mat d) := by
    ext r s
    by_cases hrs : r = s
    · subst s
      simp [Ch02.averageMat, Ch02.average, aω, hdata, c,
        ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
        Homogenization.scalarMatrix]
    · simp [Ch02.averageMat, Ch02.average, aω, hdata, c,
        ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
        Homogenization.scalarMatrix, hrs]
  have hc_nonneg : 0 ≤ c := by
    exact mul_nonneg (inv_nonneg.mpr (ENNReal.toReal_nonneg))
      (integral_nonneg fun x => (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L ω x).le)
  have hBpsd : (Ch02.averageMat U aω.toCoeffField).PosSemidef := by
    rw [hAverageMat]
    exact Matrix.PosSemidef.one.smul hc_nonneg
  have hAB : MatLoewnerLE (aMatrix U aω) (Ch02.averageMat U aω.toCoeffField) := by
    change MatLoewnerLE (Ch02.aCoarse U aω) (Ch02.averageMat U aω.toCoeffField)
    simpa [aMatrix, hDerived.1] using hTheory.dirichlet_neumann_bracketing.2.2
  have hNorm := Ch02.matrixOperatorNorm_le_of_matLoewnerLE_of_posSemidef
    hApsd hBpsd hAB
  have hd_ne : d ≠ 0 := Nat.ne_of_gt
    (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)
  letI : NeZero d := ⟨hd_ne⟩
  calc
    |randomAMatrix M L U ω i j| = |aMatrix U aω i j| := rfl
    _ ≤ Ch02.matrixOperatorNorm (aMatrix U aω) :=
      Ch02.abs_entry_le_matrixOperatorNorm _ _ _
    _ ≤ Ch02.matrixOperatorNorm (Ch02.averageMat U aω.toCoeffField) := hNorm
    _ = c := by
      rw [hAverageMat]
      exact Ch02.matrixOperatorNorm_smul_one_eq_of_nonneg hc_nonneg
    _ = Ch02.average U (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω) := rfl

/-- The random finite-volume primal coarse matrix is Bochner integrable. -/
theorem integrable_randomAMatrix {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d) :
    Integrable (randomAMatrix M L U) M.P.toMeasure := by
  apply Integrable.of_eval
  intro i
  apply Integrable.of_eval
  intro j
  apply Integrable.mono' (integrable_aCutoff_average M L U)
  · exact ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp (measurable_randomAMatrix M L U))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using
        abs_randomAMatrix_apply_le_aCutoff_average M L U ω i j

private theorem matLoewnerLE_randomAMatrix_descendantsAverage {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (Q : TriadicCube d) (j : ℕ) :
    MatLoewnerLE (randomAMatrix M L (Ch02.cubeDomain Q) ω)
      (Homogenization.descendantsAverageMat Q j fun R =>
        randomAMatrix M L (Ch02.cubeDomain R) ω) := by
  let F := aCutoffFamily M L ω
  let Pcell : Ch02.DomainPartition (Ch02.cubeDomain Q) :=
    Ch02.descendantsDomainPartition Q j
  have hRestricts : ∀ i : Pcell.Cell,
      Ch02.CoeffOn.RestrictsTo (F.coeffOn Q) (F.coeffOn i.1) := by
    intro i
    exact F.restrictsTo_of_subset
      (Homogenization.openCubeSet_subset_of_mem_descendantsAtDepth i.2)
  have hBlock := (Ch02.blockCoarseMatrixTheory
    (Ch02.cubeDomain Q) (F.coeffOn Q)).block_matrix_subadditive
      Pcell (fun i : Pcell.Cell => F.coeffOn i.1) hRestricts
  have hUpper := Ch04.matLoewnerLE_upperLeft_of_blockMatLoewnerLE hBlock
  have hParent :
      Ch02.bCoarse (Ch02.cubeDomain Q) (F.coeffOn Q) =
        aMatrix (Ch02.cubeDomain Q) (F.coeffOn Q) := by
    have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
      (Ch02.cubeDomain Q) (F.coeffOn Q)
      ((aCutoffTriadicData M L ω).onCube Q).isSymmetric
    exact hTheory.derived_matrices.2.2.trans hTheory.derived_matrices.1.symm
  have hChild : ∀ R : TriadicCube d,
      Ch02.bCoarse (Ch02.cubeDomain R) (F.coeffOn R) =
        aMatrix (Ch02.cubeDomain R) (F.coeffOn R) := by
    intro R
    have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
      (Ch02.cubeDomain R) (F.coeffOn R)
      ((aCutoffTriadicData M L ω).onCube R).isSymmetric
    exact hTheory.derived_matrices.2.2.trans hTheory.derived_matrices.1.symm
  change MatLoewnerLE
    (Ch02.bCoarse (Ch02.cubeDomain Q) (F.coeffOn Q))
    (Pcell.weightedMatAverage fun i =>
      Ch02.bCoarse (Ch02.cubeDomain i.1) (F.coeffOn i.1)) at hUpper
  rw [hParent] at hUpper
  have hWeighted :
      Pcell.weightedMatAverage (fun i =>
        Ch02.bCoarse (Ch02.cubeDomain i.1) (F.coeffOn i.1)) =
      Homogenization.descendantsAverageMat Q j (fun R =>
        aMatrix (Ch02.cubeDomain R) (F.coeffOn R)) := by
    rw [show (fun i : Pcell.Cell =>
        Ch02.bCoarse (Ch02.cubeDomain i.1) (F.coeffOn i.1)) =
        fun i => aMatrix (Ch02.cubeDomain i.1) (F.coeffOn i.1) by
      funext i
      exact hChild i.1]
    simpa [Pcell] using Ch02.descendantsDomainPartition_weightedMatAverage Q j
      (fun R => aMatrix (Ch02.cubeDomain R) (F.coeffOn R))
  rw [hWeighted] at hUpper
  simpa [F, Pcell, aCutoffFamily, aCutoffTriadicData, randomAMatrix,
    ScalarTriadicCoeffData.toTriadicCoeffFamily] using! hUpper

private theorem integrable_randomAMatrix_quadratic {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (p : Vec d) :
    Integrable (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
      (1 / 2 : ℝ) * vecDot p (matVecMul (randomAMatrix M L U ω) p))
      M.P.toMeasure := by
  apply Integrable.const_mul
  simp only [vecDot, matVecMul]
  apply MeasureTheory.integrable_finset_sum Finset.univ
  intro i _hi
  apply Integrable.const_mul
  apply MeasureTheory.integrable_finset_sum Finset.univ
  intro j _hj
  exact (((integrable_randomAMatrix M L U).eval i).eval j).mul_const (p j)

private theorem integral_randomAMatrix_quadratic {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (p : Vec d) :
    ∫ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
        (1 / 2 : ℝ) * vecDot p (matVecMul (randomAMatrix M L U ω) p)
        ∂M.P.toMeasure =
      (1 / 2 : ℝ) * vecDot p (matVecMul (abar M L U) p) := by
  rw [MeasureTheory.integral_const_mul]
  congr 1
  simp only [vecDot, matVecMul]
  rw [MeasureTheory.integral_finset_sum Finset.univ]
  · congr 1
    ext i
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_finset_sum Finset.univ]
    · simp_rw [MeasureTheory.integral_mul_const]
      congr 1
      apply Finset.sum_congr rfl
      intro j _hj
      change
        (∫ ω, randomAMatrix M L U ω i j ∂M.P.toMeasure) * p j =
          (∫ ω, randomAMatrix M L U ω ∂M.P.toMeasure) i j * p j
      rw [Homogenization.integral_matrix_apply
        (integrable_randomAMatrix M L U) i j]
    · intro j _hj
      exact (((integrable_randomAMatrix M L U).eval i).eval j).mul_const (p j)
  · intro i _hi
    exact (MeasureTheory.integrable_finset_sum Finset.univ fun j _hj =>
      (((integrable_randomAMatrix M L U).eval i).eval j).mul_const (p j)).const_mul (p i)

private theorem integrable_descendantsAverage_randomAMatrix_quadratic {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (Q : TriadicCube d) (j : ℕ) (p : Vec d) :
    Integrable (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
      (1 / 2 : ℝ) * vecDot p
        (matVecMul (Homogenization.descendantsAverageMat Q j fun R =>
          randomAMatrix M L (Ch02.cubeDomain R) ω) p)) M.P.toMeasure := by
  rw [show (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
      (1 / 2 : ℝ) * vecDot p
        (matVecMul (Homogenization.descendantsAverageMat Q j fun R =>
          randomAMatrix M L (Ch02.cubeDomain R) ω) p)) =
      fun ω => Homogenization.descendantsAverage Q j fun R =>
        (1 / 2 : ℝ) * vecDot p
          (matVecMul (randomAMatrix M L (Ch02.cubeDomain R) ω) p) by
    funext ω
    rw [Homogenization.vecDot_matVecMul_descendantsAverageMat]
    simp only [Homogenization.descendantsAverage]
    rw [← Finset.mul_sum]
    ring]
  simp only [Homogenization.descendantsAverage]
  exact (MeasureTheory.integrable_finset_sum _ fun R _ =>
    integrable_randomAMatrix_quadratic M L (Ch02.cubeDomain R) p).const_mul _

/-- Annealed primal coarse matrices inherit deterministic subdivision
subadditivity before stationarity is used to identify the child expectations. -/
theorem matLoewnerLE_abar_descendantsAverage {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (Q : TriadicCube d) (j : ℕ) :
    MatLoewnerLE (abar M L (Ch02.cubeDomain Q))
      (Homogenization.descendantsAverageMat Q j fun R =>
        abar M L (Ch02.cubeDomain R)) := by
  intro p
  rw [← integral_randomAMatrix_quadratic M L (Ch02.cubeDomain Q) p]
  rw [show (1 / 2 : ℝ) * vecDot p
      (matVecMul (Homogenization.descendantsAverageMat Q j fun R =>
        abar M L (Ch02.cubeDomain R)) p) =
      ∫ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
        (1 / 2 : ℝ) * vecDot p
          (matVecMul (Homogenization.descendantsAverageMat Q j fun R =>
            randomAMatrix M L (Ch02.cubeDomain R) ω) p) ∂M.P.toMeasure by
    calc
      (1 / 2 : ℝ) * vecDot p
          (matVecMul (Homogenization.descendantsAverageMat Q j fun R =>
            abar M L (Ch02.cubeDomain R)) p) =
        Homogenization.descendantsAverage Q j (fun R =>
          (1 / 2 : ℝ) * vecDot p
            (matVecMul (abar M L (Ch02.cubeDomain R)) p)) := by
          rw [Homogenization.vecDot_matVecMul_descendantsAverageMat]
          simp only [Homogenization.descendantsAverage]
          rw [← Finset.mul_sum]
          ring
      _ = Homogenization.descendantsAverage Q j (fun R =>
          ∫ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
            (1 / 2 : ℝ) * vecDot p
              (matVecMul (randomAMatrix M L (Ch02.cubeDomain R) ω) p)
              ∂M.P.toMeasure) := by
          congr 1
          funext R
          exact (integral_randomAMatrix_quadratic M L (Ch02.cubeDomain R) p).symm
      _ = ∫ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
          Homogenization.descendantsAverage Q j (fun R =>
            (1 / 2 : ℝ) * vecDot p
              (matVecMul (randomAMatrix M L (Ch02.cubeDomain R) ω) p))
            ∂M.P.toMeasure := by
          simp only [Homogenization.descendantsAverage]
          rw [MeasureTheory.integral_const_mul]
          rw [MeasureTheory.integral_finset_sum]
          intro R _hR
          exact integrable_randomAMatrix_quadratic M L (Ch02.cubeDomain R) p
      _ = ∫ ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
          (1 / 2 : ℝ) * vecDot p
            (matVecMul (Homogenization.descendantsAverageMat Q j fun R =>
              randomAMatrix M L (Ch02.cubeDomain R) ω) p) ∂M.P.toMeasure := by
          apply integral_congr_ae
          filter_upwards with ω
          rw [Homogenization.vecDot_matVecMul_descendantsAverageMat]
          simp only [Homogenization.descendantsAverage]
          rw [← Finset.mul_sum]
          ring]
  exact integral_mono
    (integrable_randomAMatrix_quadratic M L (Ch02.cubeDomain Q) p)
    (integrable_descendantsAverage_randomAMatrix_quadratic M L Q j p)
    (fun ω => matLoewnerLE_randomAMatrix_descendantsAverage M L ω Q j p)

-- PROVENANCE: matrix-valued version of the finite-average glue in
-- `Algsuperdiff/Section3/Provider/Annealed/Monotonicity.lean`.
private theorem descendantsAverageMat_congr {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    {F G : TriadicCube d → Mat d}
    (h : ∀ R ∈ Homogenization.descendantsAtDepth Q j, F R = G R) :
    Homogenization.descendantsAverageMat Q j F =
      Homogenization.descendantsAverageMat Q j G := by
  funext i k
  simp only [Homogenization.descendantsAverageMat,
    Homogenization.descendantsAverage]
  congr 1
  apply Finset.sum_congr rfl
  intro R hR
  rw [h R hR]

private theorem descendantsAverageMat_const {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (A : Mat d) :
    Homogenization.descendantsAverageMat Q j (fun _ => A) = A := by
  funext i k
  simp only [Homogenization.descendantsAverageMat,
    Homogenization.descendantsAverage]
  have hcard : ((Homogenization.descendantsAtDepth Q j).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr
      (Homogenization.descendantsAtDepth_nonempty Q j)
  rw [Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- The annealed primal matrices on centered paper cubes are nonincreasing in
the cube scale in the Löwner order. -/
theorem matLoewnerLE_abar_originCube_succ {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L n : ℕ) :
    MatLoewnerLE
      (abar M L
        (Ch02.cubeDomain (Homogenization.originCube d ((n + 1 : ℕ) : ℤ))))
      (abar M L (Ch02.cubeDomain (Homogenization.originCube d (n : ℤ)))) := by
  let Q : TriadicCube d := Homogenization.originCube d ((n + 1 : ℕ) : ℤ)
  have hSub := matLoewnerLE_abar_descendantsAverage M L Q 1
  have hAverage :
      Homogenization.descendantsAverageMat Q 1 (fun R =>
        abar M L (Ch02.cubeDomain R)) =
      abar M L (Ch02.cubeDomain (Homogenization.originCube d (n : ℤ))) := by
    calc
      Homogenization.descendantsAverageMat Q 1 (fun R =>
          abar M L (Ch02.cubeDomain R)) =
        Homogenization.descendantsAverageMat Q 1 (fun _ =>
          abar M L (Ch02.cubeDomain (Homogenization.originCube d (n : ℤ)))) := by
            apply descendantsAverageMat_congr
            intro R hR
            have hscale : R.scale = (n : ℤ) := by
              rw [Homogenization.scale_eq_sub_of_mem_descendantsAtDepth hR]
              change ((n : ℤ) + 1) - 1 = (n : ℤ)
              omega
            calc
              abar M L (Ch02.cubeDomain R) =
                  abar M L (Ch02.cubeDomain
                    (Homogenization.originCube d R.scale)) :=
                abar_cube_eq_originCube M L R
              _ = abar M L (Ch02.cubeDomain
                    (Homogenization.originCube d (n : ℤ))) := by rw [hscale]
      _ = abar M L (Ch02.cubeDomain
          (Homogenization.originCube d (n : ℤ))) :=
        descendantsAverageMat_const Q 1 _
  rw [hAverage] at hSub
  simpa [Q] using hSub

end

end SubdiffusiveProcess.CoarseGrainingVocab
