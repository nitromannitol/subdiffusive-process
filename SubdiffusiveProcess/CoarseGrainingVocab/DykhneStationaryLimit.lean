module

public import SubdiffusiveProcess.CoarseGrainingVocab.AhomStarCharacterization
public import SubdiffusiveProcess.CoarseGrainingVocab.DykhneFiniteVolume

@[expose] public section

/-!
# Stationary limit of the planar Dykhne identity

`SubdiffusiveProcess/CoarseGrainingVocab/DykhneFiniteVolume.lean` proves the deterministic
planar reciprocal duality on the Chapter 2 carrier and transports it through
the self-dual law of the *uniformly elliptic truncation* `a_m^(N)`.  The
classical uniformly elliptic Dykhne argument uses truncation; its removal
requires a degenerate stationary primal/dual variational limit.
The deterministic argument below instead treats the raw cutoff directly,
for the planar identity in paper label `p.special.two.d.exact.formula`.  The finite-volume
identity is *deterministic* and requires only pointwise positivity of the
coefficient, which the raw cutoff `a_m` already has on every bounded domain
(`aCutoffCoeffOnData`).  This module therefore runs the whole argument on the
raw cutoff:

* `randomAMatrix_planarDualPotentialSample_of_streamFunction` — the samplewise
  identity `a(U; a_m(T omega)) = lambda_m^2 a_*(U; a_m(omega))^{-1}`;
* `abar_eq_planarLambda_sq_smul_abarStarInv_of_streamFunction` — its annealed
  form, using the already-proved law invariance and `integrable_randomAMatrix`;
* `ahom_sq_eq_planarLambda_sq_of_streamFunction` and
  `ahom_eq_planarLambda_of_streamFunction` — the infinite-volume conclusion,
  obtained from `tendsto_abar_originCube_ahom` (primal) and
  `tendsto_abarStarInv_originCube` (starred).

The deterministic route replaces truncation, an external Dykhne input, and
stationary variational semicontinuity by
the single deterministic planar stream-function converse
`PlanarZeroNormalStreamFunctionOn` on centered cubes.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Filter MeasureTheory Homogenization Homogenization.Book
open scoped Matrix.Norms.Elementwise

noncomputable section

private abbrev Sample2 := _root_.SubdiffusiveProcess.Model.PotentialSample 2

/-- The planar reciprocal sample transform attached to the quarter turn. -/
private def planarDualSample : _root_.SubdiffusiveProcess.Model.PotentialSample 2 → _root_.SubdiffusiveProcess.Model.PotentialSample 2 :=
  planarDualPotentialSample planarQuarterTurn planarQuarterTurn_isSignedPermutation

private theorem planarQuarterTurn_double_conj (A : Mat 2) :
    matTranspose planarQuarterTurn *
        (matTranspose planarQuarterTurn * A * planarQuarterTurn) *
      planarQuarterTurn = A := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d223_planarQuarterTurn_double_conjugation (A := A)

/-- The quarter-turned raw cutoff is the raw cutoff of the rotated sample, so
it inherits a uniform ellipticity package on every bounded domain. -/
private def aCutoffRotatedCoeffOnData
    (M : _root_.SubdiffusiveProcess.Model.GMCModel 2) (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample 2)
    (U : Ch02.Domain 2) :
    ScalarCoeffOnData U
      (fun x => _root_.SubdiffusiveProcess.Model.aCutoff M m omega
        (matVecMul planarQuarterTurn x)) :=
  (funext (aCutoff_rotatePotentialSample M m planarQuarterTurn
      planarQuarterTurn_isSignedPermutation omega) :
    _root_.SubdiffusiveProcess.Model.aCutoff M m
        (rotatePotentialSample planarQuarterTurn
          planarQuarterTurn_isSignedPermutation omega) =
      fun x => _root_.SubdiffusiveProcess.Model.aCutoff M m omega
        (matVecMul planarQuarterTurn x)) ▸
    aCutoffCoeffOnData M m
      (rotatePotentialSample planarQuarterTurn
        planarQuarterTurn_isSignedPermutation omega) U

/-- Samplewise planar Dykhne identity for the **untruncated** GMC cutoff on a
centered cube.  The only analytic premise is the weak zero-normal
stream-function converse; the physical rotation carried by
`planarDualPotentialSample` cancels the two matrix conjugations coming from
deterministic reciprocal duality. -/
theorem randomAMatrix_planarDualPotentialSample_of_streamFunction
    (M : _root_.SubdiffusiveProcess.Model.GMCModel 2) (m : ℕ) (n : ℤ)
    (hstream : PlanarZeroNormalStreamFunctionOn (openCubeSet (originCube 2 n)))
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample 2) :
    randomAMatrix M m (Ch02.cubeDomain (originCube 2 n))
        (planarDualPotentialSample planarQuarterTurn
          planarQuarterTurn_isSignedPermutation omega) =
      planarLambda M m ^ 2 •
        (randomAStarMatrix M m (Ch02.cubeDomain (originCube 2 n)) omega)⁻¹ := by
  let U := Ch02.cubeDomain (originCube 2 n)
  let T := planarDualPotentialSample planarQuarterTurn
    planarQuarterTurn_isSignedPermutation
  let b : Vec 2 → ℝ := _root_.SubdiffusiveProcess.Model.aCutoff M m omega
  let bRot : Vec 2 → ℝ := fun x => b (matVecMul planarQuarterTurn x)
  let hBase : ScalarCoeffOnData U b := aCutoffCoeffOnData M m omega U
  let hRot : ScalarCoeffOnData U bRot := aCutoffRotatedCoeffOnData M m omega U
  let hSampleDual :
      ScalarCoeffOnData U (_root_.SubdiffusiveProcess.Model.aCutoff M m (T omega)) :=
    aCutoffCoeffOnData M m (T omega) U
  have hdualEq : _root_.SubdiffusiveProcess.Model.aCutoff M m (T omega) =
      planarReciprocalScalarField (planarLambda M m) bRot := by
    funext x
    exact aCutoff_planarDualPotentialSample M m planarQuarterTurn
      planarQuarterTurn_isSignedPermutation omega x
  let hDual : ScalarCoeffOnData U
      (planarReciprocalScalarField (planarLambda M m) bRot) := hdualEq ▸ hSampleDual
  have hdet := aMatrix_planarReciprocal_originCube_of_planarZeroNormalStreamFunctionOn
    n hstream (planarLambda_pos M m)
    (fun x => _root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega
      (matVecMul planarQuarterTurn x)) hRot hDual
  have hcov := aStarMatrix_inv_planarQuarterTurn_originCube hBase hRot
  change aMatrix U hSampleDual.toCoeffOn =
    planarLambda M m ^ 2 • (aStarMatrix U hBase.toCoeffOn)⁻¹
  have hleft : aMatrix U hSampleDual.toCoeffOn = aMatrix U hDual.toCoeffOn := by
    apply Ch02.aCoarse_eq_ofAEEq
    filter_upwards with x
    ext i j
    change scalarMatrix (_root_.SubdiffusiveProcess.Model.aCutoff M m (T omega) x) i j =
      scalarMatrix (planarReciprocalScalarField (planarLambda M m) bRot x) i j
    rw [congrFun hdualEq x]
  rw [hleft, hdet, hcov, planarQuarterTurn_double_conj]

/-- Annealed planar Dykhne identity for the untruncated GMC cutoff on a
centered cube.  No integrability hypothesis is needed: the primal coarse observable is
already known to be Bochner integrable. -/
theorem abar_eq_planarLambda_sq_smul_abarStarInv_of_streamFunction
    (M : _root_.SubdiffusiveProcess.Model.GMCModel 2) (m : ℕ) (n : ℤ)
    (hstream : PlanarZeroNormalStreamFunctionOn (openCubeSet (originCube 2 n))) :
    abar M m (Ch02.cubeDomain (originCube 2 n)) =
      planarLambda M m ^ 2 •
        abarStarInv M m (Ch02.cubeDomain (originCube 2 n)) := by
  let U := Ch02.cubeDomain (originCube 2 n)
  let T : _root_.SubdiffusiveProcess.Model.PotentialSample 2 → _root_.SubdiffusiveProcess.Model.PotentialSample 2 := planarDualPotentialSample planarQuarterTurn
    planarQuarterTurn_isSignedPermutation
  let A : _root_.SubdiffusiveProcess.Model.PotentialSample 2 → Mat 2 := randomAMatrix M m U
  let B : _root_.SubdiffusiveProcess.Model.PotentialSample 2 → Mat 2 := fun omega => (randomAStarMatrix M m U omega)⁻¹
  have hA : Integrable A M.P.toMeasure := integrable_randomAMatrix M m U
  have hinvariant : ∫ omega, A (T omega) ∂M.P.toMeasure =
      ∫ omega, A omega ∂M.P.toMeasure :=
    by
      have hT := measurable_planarDualPotentialSample planarQuarterTurn
        planarQuarterTurn_isSignedPermutation
      have hmap : Measure.map T M.P.toMeasure = M.P.toMeasure :=
        potentialSequenceLaw_planarDual M planarQuarterTurn planarQuarterTurn_isSignedPermutation
      have hAm : AEStronglyMeasurable A (Measure.map T M.P.toMeasure) := by
        rw [hmap]
        exact hA.aestronglyMeasurable
      calc
        _ = ∫ omega, A omega ∂Measure.map T M.P.toMeasure :=
          (integral_map hT.aemeasurable hAm).symm
        _ = _ := by rw [hmap]
  calc
    abar M m U = ∫ omega, A omega ∂M.P.toMeasure := rfl
    _ = ∫ omega, A (T omega) ∂M.P.toMeasure := hinvariant.symm
    _ = ∫ omega, planarLambda M m ^ 2 • B omega ∂M.P.toMeasure := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
      exact randomAMatrix_planarDualPotentialSample_of_streamFunction M m n hstream omega
    _ = planarLambda M m ^ 2 • ∫ omega, B omega ∂M.P.toMeasure := by
      rw [MeasureTheory.integral_smul]
    _ = planarLambda M m ^ 2 • abarStarInv M m U := rfl

/-- Infinite-volume planar self-duality: the scalar homogenized coefficient
squares to `lambda_m^2`.  The primal limit is
`tendsto_abar_originCube_ahom`; the starred limit is
`tendsto_abarStarInv_originCube`. -/
theorem ahom_mul_ahom_eq_planarLambda_sq_of_streamFunction
    (M : _root_.SubdiffusiveProcess.Model.GMCModel 2) (m : ℕ)
    (hstream : ∀ n : ℤ,
      PlanarZeroNormalStreamFunctionOn (openCubeSet (originCube 2 n)))
    (hpos : 0 < ahom M m) :
    ahom M m * ahom M m = planarLambda M m ^ 2 := by
  have hprimal : Tendsto (fun k : ℕ =>
      abar M m (Ch02.cubeDomain (originCube 2 (k : ℤ))))
      atTop (nhds (ahom M m • (1 : Mat 2))) :=
    tendsto_abar_originCube_ahom M m
  have hstar : Tendsto (fun k : ℕ =>
      abar M m (Ch02.cubeDomain (originCube 2 (k : ℤ))))
      atTop (nhds (planarLambda M m ^ 2 • ((ahom M m)⁻¹ • (1 : Mat 2)))) := by
    refine ((tendsto_abarStarInv_originCube M m).const_smul
      (planarLambda M m ^ 2)).congr' ?_
    filter_upwards with k
    exact (abar_eq_planarLambda_sq_smul_abarStarInv_of_streamFunction
      M m (k : ℤ) (hstream (k : ℤ))).symm
  have hmat : ahom M m • (1 : Mat 2) =
      planarLambda M m ^ 2 • ((ahom M m)⁻¹ • (1 : Mat 2)) :=
    tendsto_nhds_unique hprimal hstar
  have hentry := congrFun (congrFun hmat 0) 0
  have hscalar : ahom M m = planarLambda M m ^ 2 * (ahom M m)⁻¹ := by
    simpa [Matrix.one_apply] using hentry
  calc
    ahom M m * ahom M m =
        planarLambda M m ^ 2 * (ahom M m)⁻¹ * ahom M m := by rw [← hscalar]
    _ = planarLambda M m ^ 2 := by
      field_simp

/-- The exact two-dimensional formula at the level of the development scalar. -/
theorem ahom_eq_planarLambda_of_streamFunction
    (M : _root_.SubdiffusiveProcess.Model.GMCModel 2) (m : ℕ)
    (hstream : ∀ n : ℤ,
      PlanarZeroNormalStreamFunctionOn (openCubeSet (originCube 2 n)))
    (hpos : 0 < ahom M m) :
    ahom M m = planarLambda M m := by
  have hsq := ahom_mul_ahom_eq_planarLambda_sq_of_streamFunction M m hstream hpos
  have hlam := planarLambda_pos M m
  have hfactor :
      (ahom M m - planarLambda M m) * (ahom M m + planarLambda M m) = 0 := by
    have hexpand :
        (ahom M m - planarLambda M m) * (ahom M m + planarLambda M m) =
          ahom M m * ahom M m - planarLambda M m ^ 2 := by ring
    rw [hexpand, hsq, sub_self]
  rcases mul_eq_zero.mp hfactor with h | h
  · linarith
  · linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab
