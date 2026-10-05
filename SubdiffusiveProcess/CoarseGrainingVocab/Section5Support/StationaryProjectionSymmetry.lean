module

public import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffRestrictionSymmetry
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepOrbitContinuity
public import Homogenization.Sobolev.H1.OriginCubeSymmetry

@[expose] public section

/-!
# Signed-coordinate symmetry of the stationary one-step forcing

This file isolates the law-transport part of the isotropic stationary
Helmholtz calculation.  Signed-coordinate
rotations of the literal potential sequence preserve its probability law,
intertwine the translation action, and leave the scalar one-step multiplier
at the origin unchanged.

The remaining analytic step is to lift these transformations through the
closed horizontal-gradient subspace and its orthogonal projection.  Keeping
the carrier facts here prevents that projection argument from duplicating
the established product-law proof.

 the separation into a measure-preserving sample transformation
and an equivariant stationary projection mirrors
`Algsuperdiff/Section3/Provider/Corrector/MollifiedDecorrelation.lean`.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


/-- A linear isometric equivalence of value spaces acts pointwise on `L²`.
Mathlib exposes the corresponding continuous linear map; this wrapper records
the exact norm equality and the inverse. -/
def liftL2CodomainLinearIsometryEquiv
    {Omega E F : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (mu : Measure Omega) (e : E ≃ₗᵢ[ℝ] F) :
    Lp E 2 mu ≃ₗᵢ[ℝ] Lp F 2 mu where
  toLinearEquiv :=
    { toFun := e.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 mu
      invFun := e.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 mu
      left_inv := by
        intro f
        apply Lp.ext
        filter_upwards
          [e.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL f,
            e.symm.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL
              (e.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 mu f)]
            with omega hforward hinverse
        rw [hinverse, hforward]
        change e.symm (e (f omega)) = f omega
        exact e.symm_apply_apply _
      right_inv := by
        intro f
        apply Lp.ext
        filter_upwards
          [e.symm.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL f,
            e.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL
              (e.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 mu f)]
            with omega hinverse hforward
        rw [hforward, hinverse]
        change e (e.symm (f omega)) = f omega
        exact e.apply_symm_apply _
      map_add' := by
        intro f g
        exact map_add _ _ _
      map_smul' := by
        intro c f
        exact map_smul _ _ _ }
  norm_map' := by
    intro f
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    filter_upwards
      [e.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL f]
        with omega homega
    change ‖(e.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 mu f :
      Omega → F) omega‖ = ‖f omega‖
    rw [homega]
    change ‖e (f omega)‖ = ‖f omega‖
    exact e.norm_map _

/-- Composition by a measure-preserving involution as a linear isometric
equivalence of `L²`. -/
def liftL2SampleInvolution
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (mu : Measure Omega) (S : Omega → Omega)
    (hS : MeasurePreserving S mu mu) (hself : ∀ omega, S (S omega) = omega) :
    Lp E 2 mu ≃ₗᵢ[ℝ] Lp E 2 mu where
  toLinearEquiv :=
    { toFun := Lp.compMeasurePreservingₗᵢ ℝ S hS
      invFun := Lp.compMeasurePreservingₗᵢ ℝ S hS
      left_inv := by
        intro f
        apply Lp.ext
        filter_upwards
          [Lp.coeFn_compMeasurePreserving
            (Lp.compMeasurePreservingₗᵢ ℝ S hS f) hS,
            hS.quasiMeasurePreserving.ae
              (Lp.coeFn_compMeasurePreserving f hS)]
            with omega houter hinner
        change ((Lp.compMeasurePreserving S hS
          (Lp.compMeasurePreserving S hS f) : Lp E 2 mu) :
            Omega → E) omega = f omega
        have houter' : ((Lp.compMeasurePreserving S hS
            (Lp.compMeasurePreserving S hS f) : Lp E 2 mu) :
              Omega → E) omega =
            (Lp.compMeasurePreserving S hS f : Omega → E) (S omega) :=
          houter
        rw [houter', hinner]
        change f (S (S omega)) = f omega
        rw [hself]
      right_inv := by
        intro f
        apply Lp.ext
        filter_upwards
          [Lp.coeFn_compMeasurePreserving
            (Lp.compMeasurePreservingₗᵢ ℝ S hS f) hS,
            hS.quasiMeasurePreserving.ae
              (Lp.coeFn_compMeasurePreserving f hS)]
            with omega houter hinner
        change ((Lp.compMeasurePreserving S hS
          (Lp.compMeasurePreserving S hS f) : Lp E 2 mu) :
            Omega → E) omega = f omega
        have houter' : ((Lp.compMeasurePreserving S hS
            (Lp.compMeasurePreserving S hS f) : Lp E 2 mu) :
              Omega → E) omega =
            (Lp.compMeasurePreserving S hS f : Omega → E) (S omega) :=
          houter
        rw [houter', hinner]
        change f (S (S omega)) = f omega
        rw [hself]
      map_add' := by
        intro f g
        exact map_add _ _ _
      map_smul' := by
        intro c f
        exact map_smul _ _ _ }
  norm_map' := by
    intro f
    exact Lp.norm_compMeasurePreserving f hS

/-- Signed-coordinate rotation of the literal shell sequence is
measure-preserving. -/
theorem measurePreserving_rotatePotentialSequenceForRestriction {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (R : Mat d)
    (hR : IsSignedPermutationMatrix R) :
    MeasurePreserving
      (rotatePotentialSequenceForRestriction (d := d) R hR)
      M.P.toMeasure M.P.toMeasure := by
  exact ⟨measurable_rotatePotentialSequenceForRestriction R hR,
    potentialSequenceLaw_isotropic_forRestriction M R hR⟩

/-- The scalar one-step multiplier at the origin is fixed pointwise by every
signed-coordinate rotation of the shell sequence. -/
theorem oneStepOriginMultiplier_rotatePotentialSequenceForRestriction
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (R : Mat d) (hR : IsSignedPermutationMatrix R) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    oneStepOriginMultiplier M n h
        (rotatePotentialSequenceForRestriction R hR omega) =
      oneStepOriginMultiplier M n h omega := by
  simp only [oneStepOriginMultiplier, cutoffRatioMinusOne, aCutoffAtInt,
    ite_eq_right (not_lt_of_ge (Int.natCast_nonneg n)), Int.toNat_natCast]
  change _root_.SubdiffusiveProcess.Model.aCutoff M (n + h)
        (rotatePotentialSequenceForRestriction R hR omega) 0 /
      _root_.SubdiffusiveProcess.Model.aCutoff M n
        (rotatePotentialSequenceForRestriction R hR omega) 0 - 1 = _
  simp [_root_.SubdiffusiveProcess.Model.aCutoff,
    rotatePotentialSequenceForRestriction, matVecMul_zero]

/-- A coordinate sign flip intertwines sequence rotation and physical
translation.  The same sign flip occurs in both variables because it is an
involution. -/
theorem rotatePotentialSequenceForRestriction_signFlip_translate {d : ℕ}
    (i : Fin d) (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    rotatePotentialSequenceForRestriction (signFlipMatrix i)
        (isSignedPermutationMatrix_signFlipMatrix i)
        (translatePotentialSequence z omega) =
      translatePotentialSequence
        (signFlipVecContinuousLinearEquiv i z)
        (rotatePotentialSequenceForRestriction (signFlipMatrix i)
          (isSignedPermutationMatrix_signFlipMatrix i) omega) := by
  funext k
  apply _root_.SubdiffusiveProcess.Model.PotentialField.ext
  intro x
  change omega k (matVecMul (signFlipMatrix i) x + z) =
    omega k (matVecMul (signFlipMatrix i)
      (x + signFlipVecContinuousLinearEquiv i z))
  have hself : matVecMul (signFlipMatrix i)
      (matVecMul (signFlipMatrix i) z) = z := by
    simpa only [signFlipVecContinuousLinearEquiv_apply] using!
      signFlipVecContinuousLinearEquiv_self_apply i z
  rw [matVecMul_add, signFlipVecContinuousLinearEquiv_apply, hself]

/-- A coordinate swap intertwines sequence rotation and physical translation.
The same swap occurs in both variables because it is an involution. -/
theorem rotatePotentialSequenceForRestriction_swap_translate {d : ℕ}
    (i j : Fin d) (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    rotatePotentialSequenceForRestriction (Matrix.swap ℝ i j)
        (isSignedPermutationMatrix_swap i j)
        (translatePotentialSequence z omega) =
      translatePotentialSequence
        (swapVecContinuousLinearEquiv i j z)
        (rotatePotentialSequenceForRestriction (Matrix.swap ℝ i j)
          (isSignedPermutationMatrix_swap i j) omega) := by
  funext k
  apply _root_.SubdiffusiveProcess.Model.PotentialField.ext
  intro x
  change omega k (matVecMul (Matrix.swap ℝ i j) x + z) =
    omega k (matVecMul (Matrix.swap ℝ i j)
      (x + swapVecContinuousLinearEquiv i j z))
  have hself : matVecMul (Matrix.swap ℝ i j)
      (matVecMul (Matrix.swap ℝ i j) z) = z := by
    simpa only [swapVecContinuousLinearEquiv_apply] using!
      swapVecContinuousLinearEquiv_self_apply i j z
  rw [matVecMul_add, swapVecContinuousLinearEquiv_apply, hself]

theorem rotatePotentialSequenceForRestriction_signFlip_self {d : ℕ}
    (i : Fin d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    rotatePotentialSequenceForRestriction (signFlipMatrix i)
        (isSignedPermutationMatrix_signFlipMatrix i)
        (rotatePotentialSequenceForRestriction (signFlipMatrix i)
          (isSignedPermutationMatrix_signFlipMatrix i) omega) = omega := by
  funext k
  apply _root_.SubdiffusiveProcess.Model.PotentialField.ext
  intro x
  change omega k (matVecMul (signFlipMatrix i)
    (matVecMul (signFlipMatrix i) x)) = omega k x
  simpa only [signFlipVecContinuousLinearEquiv_apply] using! congrArg
    (fun y : Vec d => omega k y)
    (signFlipVecContinuousLinearEquiv_self_apply i x)

theorem rotatePotentialSequenceForRestriction_swap_self {d : ℕ}
    (i j : Fin d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    rotatePotentialSequenceForRestriction (Matrix.swap ℝ i j)
        (isSignedPermutationMatrix_swap i j)
        (rotatePotentialSequenceForRestriction (Matrix.swap ℝ i j)
          (isSignedPermutationMatrix_swap i j) omega) = omega := by
  funext k
  apply _root_.SubdiffusiveProcess.Model.PotentialField.ext
  intro x
  change omega k (matVecMul (Matrix.swap ℝ i j)
    (matVecMul (Matrix.swap ℝ i j) x)) = omega k x
  simpa only [swapVecContinuousLinearEquiv_apply] using! congrArg
    (fun y : Vec d => omega k y)
    (swapVecContinuousLinearEquiv_self_apply i j x)

/-- Coordinate sign flip on the Euclidean Hilbert realization of `Vec d`. -/
def hilbertSignFlip {d : ℕ} (i : Fin d) :
    HilbertVec d ≃ₗᵢ[ℝ] HilbertVec d :=
  LinearIsometryEquiv.piLpCongrRight 2 fun j : Fin d =>
    if j = i then
      LinearIsometryEquiv.neg ℝ
    else
      LinearIsometryEquiv.refl ℝ ℝ

@[simp] theorem hilbertSignFlip_apply {d : ℕ} (i : Fin d)
    (x : HilbertVec d) :
    hilbertSignFlip i x =
      HilbertVec.ofVec (signFlipVecContinuousLinearEquiv i x.toVec) := by
  apply HilbertVec.ext
  intro j
  by_cases hji : j = i
  · subst j
    simp [hilbertSignFlip, signFlipVecContinuousLinearEquiv]
  · simp [hilbertSignFlip, signFlipVecContinuousLinearEquiv, hji]

@[simp] theorem hilbertSignFlip_self_apply {d : ℕ} (i : Fin d)
    (x : HilbertVec d) :
    hilbertSignFlip i (hilbertSignFlip i x) = x := by
  rw [hilbertSignFlip_apply, hilbertSignFlip_apply,
    HilbertVec.toVec_ofVec, signFlipVecContinuousLinearEquiv_self_apply,
    HilbertVec.ofVec_toVec]

/-- Coordinate swap on the Euclidean Hilbert realization of `Vec d`. -/
def hilbertSwap {d : ℕ} (i j : Fin d) :
    HilbertVec d ≃ₗᵢ[ℝ] HilbertVec d :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)

@[simp] theorem hilbertSwap_apply {d : ℕ} (i j : Fin d)
    (x : HilbertVec d) :
    hilbertSwap i j x =
      HilbertVec.ofVec (swapVecContinuousLinearEquiv i j x.toVec) := by
  apply HilbertVec.ext
  intro k
  change x ((Equiv.swap i j) k) =
    swapVecContinuousLinearEquiv i j x.toVec k
  rw [swapVecContinuousLinearEquiv_apply, matVecMul_swap_eq_comp]
  rfl

@[simp] theorem hilbertSwap_self_apply {d : ℕ} (i j : Fin d)
    (x : HilbertVec d) :
    hilbertSwap i j (hilbertSwap i j x) = x := by
  rw [hilbertSwap_apply, hilbertSwap_apply, HilbertVec.toVec_ofVec,
    swapVecContinuousLinearEquiv_self_apply, HilbertVec.ofVec_toVec]

/-- Pointwise covariance of the one-step forcing under a coordinate sign
flip. -/
theorem oneStepOriginForcing_rotate_signFlip {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (i : Fin d) (p : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    hilbertSignFlip i
        (oneStepOriginForcing M n h p
          (rotatePotentialSequenceForRestriction (signFlipMatrix i)
            (isSignedPermutationMatrix_signFlipMatrix i) omega)) =
      oneStepOriginForcing M n h
        (signFlipVecContinuousLinearEquiv i p) omega := by
  rw [oneStepOriginForcing,
    oneStepOriginMultiplier_rotatePotentialSequenceForRestriction,
    map_smul, hilbertSignFlip_apply]
  rfl

/-- Pointwise covariance of the one-step forcing under a coordinate swap. -/
theorem oneStepOriginForcing_rotate_swap {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (i j : Fin d) (p : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    hilbertSwap i j
        (oneStepOriginForcing M n h p
          (rotatePotentialSequenceForRestriction (Matrix.swap ℝ i j)
            (isSignedPermutationMatrix_swap i j) omega)) =
      oneStepOriginForcing M n h
        (swapVecContinuousLinearEquiv i j p) omega := by
  rw [oneStepOriginForcing,
    oneStepOriginMultiplier_rotatePotentialSequenceForRestriction,
    map_smul, hilbertSwap_apply]
  rfl

/-- Pullback on scalar or vector `L²` induced by a sample sign flip. -/
def signFlipSampleL2Action {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i : Fin d) :
    Lp E 2 M.P.toMeasure ≃ₗᵢ[ℝ] Lp E 2 M.P.toMeasure :=
  liftL2SampleInvolution M.P.toMeasure
    (rotatePotentialSequenceForRestriction (signFlipMatrix i)
      (isSignedPermutationMatrix_signFlipMatrix i))
    (measurePreserving_rotatePotentialSequenceForRestriction M
      (signFlipMatrix i) (isSignedPermutationMatrix_signFlipMatrix i))
    (rotatePotentialSequenceForRestriction_signFlip_self i)

/-- Pullback on scalar or vector `L²` induced by a sample coordinate swap. -/
def swapSampleL2Action {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i j : Fin d) :
    Lp E 2 M.P.toMeasure ≃ₗᵢ[ℝ] Lp E 2 M.P.toMeasure :=
  liftL2SampleInvolution M.P.toMeasure
    (rotatePotentialSequenceForRestriction (Matrix.swap ℝ i j)
      (isSignedPermutationMatrix_swap i j))
    (measurePreserving_rotatePotentialSequenceForRestriction M
      (Matrix.swap ℝ i j) (isSignedPermutationMatrix_swap i j))
    (rotatePotentialSequenceForRestriction_swap_self i j)

theorem coeFn_signFlipSampleL2Action {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i : Fin d)
    (F : Lp E 2 M.P.toMeasure) :
    (signFlipSampleL2Action M i F : _root_.SubdiffusiveProcess.Model.PotentialSample d → E) =ᵐ[M.P.toMeasure]
      fun omega => F
        (rotatePotentialSequenceForRestriction (signFlipMatrix i)
          (isSignedPermutationMatrix_signFlipMatrix i) omega) := by
  exact Lp.coeFn_compMeasurePreserving F
    (measurePreserving_rotatePotentialSequenceForRestriction M
      (signFlipMatrix i) (isSignedPermutationMatrix_signFlipMatrix i))

theorem coeFn_swapSampleL2Action {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i j : Fin d)
    (F : Lp E 2 M.P.toMeasure) :
    (swapSampleL2Action M i j F : _root_.SubdiffusiveProcess.Model.PotentialSample d → E) =ᵐ[M.P.toMeasure]
      fun omega => F
        (rotatePotentialSequenceForRestriction (Matrix.swap ℝ i j)
          (isSignedPermutationMatrix_swap i j) omega) := by
  exact Lp.coeFn_compMeasurePreserving F
    (measurePreserving_rotatePotentialSequenceForRestriction M
      (Matrix.swap ℝ i j) (isSignedPermutationMatrix_swap i j))

private theorem coeFn_koopman {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (z : Vec d)
    (F : Lp E 2 M.P.toMeasure) :
    letI := potentialSequenceVAddInvariant M
    Stationary.koopman (mu := M.P.toMeasure) z F =ᵐ[M.P.toMeasure]
      fun omega => F (z +ᵥ omega) := by
  let := potentialSequenceVAddInvariant M
  exact Lp.coeFn_compMeasurePreserving F
    (Stationary.measurePreserving_const_vadd (mu := M.P.toMeasure) z)

private theorem rotate_signFlip_vadd_rotated {d : ℕ}
    (i : Fin d) (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    rotatePotentialSequenceForRestriction (signFlipMatrix i)
        (isSignedPermutationMatrix_signFlipMatrix i)
        (signFlipVecContinuousLinearEquiv i z +ᵥ omega) =
      z +ᵥ rotatePotentialSequenceForRestriction (signFlipMatrix i)
        (isSignedPermutationMatrix_signFlipMatrix i) omega := by
  change rotatePotentialSequenceForRestriction (signFlipMatrix i)
      (isSignedPermutationMatrix_signFlipMatrix i)
      (translatePotentialSequence (signFlipVecContinuousLinearEquiv i z) omega) =
    translatePotentialSequence z
      (rotatePotentialSequenceForRestriction (signFlipMatrix i)
        (isSignedPermutationMatrix_signFlipMatrix i) omega)
  rw [rotatePotentialSequenceForRestriction_signFlip_translate]
  rw [signFlipVecContinuousLinearEquiv_self_apply]

private theorem rotate_swap_vadd_rotated {d : ℕ}
    (i j : Fin d) (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    rotatePotentialSequenceForRestriction (Matrix.swap ℝ i j)
        (isSignedPermutationMatrix_swap i j)
        (swapVecContinuousLinearEquiv i j z +ᵥ omega) =
      z +ᵥ rotatePotentialSequenceForRestriction (Matrix.swap ℝ i j)
        (isSignedPermutationMatrix_swap i j) omega := by
  change rotatePotentialSequenceForRestriction (Matrix.swap ℝ i j)
      (isSignedPermutationMatrix_swap i j)
      (translatePotentialSequence (swapVecContinuousLinearEquiv i j z) omega) =
    translatePotentialSequence z
      (rotatePotentialSequenceForRestriction (Matrix.swap ℝ i j)
        (isSignedPermutationMatrix_swap i j) omega)
  rw [rotatePotentialSequenceForRestriction_swap_translate]
  rw [swapVecContinuousLinearEquiv_self_apply]

/-- SubdiffusiveProcess.Model.PotentialSample sign flips conjugate Koopman translation by the corresponding
physical sign flip. -/
theorem signFlipSampleL2Action_koopman {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i : Fin d)
    (z : Vec d) (F : Lp E 2 M.P.toMeasure) :
    letI := potentialSequenceVAddInvariant M
    signFlipSampleL2Action M i
        (Stationary.koopman (mu := M.P.toMeasure) z F) =
      Stationary.koopman (mu := M.P.toMeasure)
        (signFlipVecContinuousLinearEquiv i z)
        (signFlipSampleL2Action M i F) := by
  let := potentialSequenceVAddInvariant M
  let S := rotatePotentialSequenceForRestriction (signFlipMatrix i)
    (isSignedPermutationMatrix_signFlipMatrix i)
  let hS := measurePreserving_rotatePotentialSequenceForRestriction M
    (signFlipMatrix i) (isSignedPermutationMatrix_signFlipMatrix i)
  let Rz := signFlipVecContinuousLinearEquiv i z
  let hz := Stationary.measurePreserving_const_vadd
    (mu := M.P.toMeasure) Rz
  apply Lp.ext
  filter_upwards
    [coeFn_signFlipSampleL2Action M i
      (Stationary.koopman (mu := M.P.toMeasure) z F),
      hS.quasiMeasurePreserving.ae (coeFn_koopman M z F),
      coeFn_koopman M Rz (signFlipSampleL2Action M i F),
      hz.quasiMeasurePreserving.ae (coeFn_signFlipSampleL2Action M i F)]
      with omega hleft hleftInner hright hrightInner
  rw [hleft, hleftInner, hright, hrightInner]
  exact congrArg (fun sample => F sample)
    (rotate_signFlip_vadd_rotated i z omega).symm

/-- SubdiffusiveProcess.Model.PotentialSample coordinate swaps conjugate Koopman translation by the corresponding
physical coordinate swap. -/
theorem swapSampleL2Action_koopman {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i j : Fin d)
    (z : Vec d) (F : Lp E 2 M.P.toMeasure) :
    letI := potentialSequenceVAddInvariant M
    swapSampleL2Action M i j
        (Stationary.koopman (mu := M.P.toMeasure) z F) =
      Stationary.koopman (mu := M.P.toMeasure)
        (swapVecContinuousLinearEquiv i j z)
        (swapSampleL2Action M i j F) := by
  let := potentialSequenceVAddInvariant M
  let S := rotatePotentialSequenceForRestriction (Matrix.swap ℝ i j)
    (isSignedPermutationMatrix_swap i j)
  let hS := measurePreserving_rotatePotentialSequenceForRestriction M
    (Matrix.swap ℝ i j) (isSignedPermutationMatrix_swap i j)
  let Rz := swapVecContinuousLinearEquiv i j z
  let hz := Stationary.measurePreserving_const_vadd
    (mu := M.P.toMeasure) Rz
  apply Lp.ext
  filter_upwards
    [coeFn_swapSampleL2Action M i j
      (Stationary.koopman (mu := M.P.toMeasure) z F),
      hS.quasiMeasurePreserving.ae (coeFn_koopman M z F),
      coeFn_koopman M Rz (swapSampleL2Action M i j F),
      hz.quasiMeasurePreserving.ae (coeFn_swapSampleL2Action M i j F)]
      with omega hleft hleftInner hright hrightInner
  rw [hleft, hleftInner, hright, hrightInner]
  exact congrArg (fun sample => F sample)
    (rotate_swap_vadd_rotated i j z omega).symm

/-- Simultaneous sample and value sign flip on stationary vector `L²`. -/
def signFlipVectorL2Action {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i : Fin d) :
    Stationary.VectorL2 d M.P.toMeasure ≃ₗᵢ[ℝ]
      Stationary.VectorL2 d M.P.toMeasure :=
  (signFlipSampleL2Action (E := HilbertVec d) M i).trans
    (liftL2CodomainLinearIsometryEquiv M.P.toMeasure (hilbertSignFlip i))

/-- Simultaneous sample and value coordinate swap on stationary vector `L²`. -/
def swapVectorL2Action {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i j : Fin d) :
    Stationary.VectorL2 d M.P.toMeasure ≃ₗᵢ[ℝ]
      Stationary.VectorL2 d M.P.toMeasure :=
  (swapSampleL2Action (E := HilbertVec d) M i j).trans
    (liftL2CodomainLinearIsometryEquiv M.P.toMeasure (hilbertSwap i j))

private theorem coeFn_vectorL2Coord {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : Fin d)
    (F : Stationary.VectorL2 d M.P.toMeasure) :
    (Stationary.vectorL2Coord (mu := M.P.toMeasure) k F : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ) =ᵐ[M.P.toMeasure]
      fun omega => F omega k :=
  (PiLp.proj (𝕜 := ℝ) (p := 2)
    (β := fun _ : Fin d => ℝ) k).coeFn_compLpL F

theorem coeFn_signFlipVectorL2Action {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i : Fin d)
    (F : Stationary.VectorL2 d M.P.toMeasure) :
    (signFlipVectorL2Action M i F : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d) =ᵐ[M.P.toMeasure]
      fun omega => hilbertSignFlip i
        (F (rotatePotentialSequenceForRestriction (signFlipMatrix i)
          (isSignedPermutationMatrix_signFlipMatrix i) omega)) := by
  let S := rotatePotentialSequenceForRestriction (signFlipMatrix i)
    (isSignedPermutationMatrix_signFlipMatrix i)
  let hS := measurePreserving_rotatePotentialSequenceForRestriction M
    (signFlipMatrix i) (isSignedPermutationMatrix_signFlipMatrix i)
  have hsample := Lp.coeFn_compMeasurePreserving F hS
  have hvalue :=
    (hilbertSignFlip i).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL
      (Lp.compMeasurePreservingₗᵢ ℝ S hS F)
  filter_upwards [hvalue, hsample] with omega hvalueOmega hsampleOmega
  change ((hilbertSignFlip i).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
      2 M.P.toMeasure (Lp.compMeasurePreserving S hS F) :
        _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d) omega = _
  have hvalueOmega' :
      ((hilbertSignFlip i).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
        2 M.P.toMeasure (Lp.compMeasurePreserving S hS F) :
          _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d) omega =
        (hilbertSignFlip i)
          ((Lp.compMeasurePreserving S hS F : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d) omega) :=
    hvalueOmega
  rw [hvalueOmega', hsampleOmega]
  rfl

theorem coeFn_swapVectorL2Action {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i j : Fin d)
    (F : Stationary.VectorL2 d M.P.toMeasure) :
    (swapVectorL2Action M i j F : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d) =ᵐ[M.P.toMeasure]
      fun omega => hilbertSwap i j
        (F (rotatePotentialSequenceForRestriction (Matrix.swap ℝ i j)
          (isSignedPermutationMatrix_swap i j) omega)) := by
  let S := rotatePotentialSequenceForRestriction (Matrix.swap ℝ i j)
    (isSignedPermutationMatrix_swap i j)
  let hS := measurePreserving_rotatePotentialSequenceForRestriction M
    (Matrix.swap ℝ i j) (isSignedPermutationMatrix_swap i j)
  have hsample := Lp.coeFn_compMeasurePreserving F hS
  have hvalue :=
    (hilbertSwap i j).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL
      (Lp.compMeasurePreservingₗᵢ ℝ S hS F)
  filter_upwards [hvalue, hsample] with omega hvalueOmega hsampleOmega
  change ((hilbertSwap i j).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
      2 M.P.toMeasure (Lp.compMeasurePreserving S hS F) :
        _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d) omega = _
  have hvalueOmega' :
      ((hilbertSwap i j).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
        2 M.P.toMeasure (Lp.compMeasurePreserving S hS F) :
          _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d) omega =
        (hilbertSwap i j)
          ((Lp.compMeasurePreserving S hS F : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d) omega) :=
    hvalueOmega
  rw [hvalueOmega', hsampleOmega]
  rfl

@[simp] theorem signFlipVectorL2Action_self_apply {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i : Fin d)
    (F : Stationary.VectorL2 d M.P.toMeasure) :
    signFlipVectorL2Action M i (signFlipVectorL2Action M i F) = F := by
  let S := rotatePotentialSequenceForRestriction (signFlipMatrix i)
    (isSignedPermutationMatrix_signFlipMatrix i)
  let hS := measurePreserving_rotatePotentialSequenceForRestriction M
    (signFlipMatrix i) (isSignedPermutationMatrix_signFlipMatrix i)
  apply Lp.ext
  filter_upwards
    [coeFn_signFlipVectorL2Action M i (signFlipVectorL2Action M i F),
      hS.quasiMeasurePreserving.ae (coeFn_signFlipVectorL2Action M i F)]
      with omega houter hinner
  rw [houter, hinner, rotatePotentialSequenceForRestriction_signFlip_self,
    hilbertSignFlip_self_apply]

@[simp] theorem swapVectorL2Action_self_apply {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i j : Fin d)
    (F : Stationary.VectorL2 d M.P.toMeasure) :
    swapVectorL2Action M i j (swapVectorL2Action M i j F) = F := by
  let S := rotatePotentialSequenceForRestriction (Matrix.swap ℝ i j)
    (isSignedPermutationMatrix_swap i j)
  let hS := measurePreserving_rotatePotentialSequenceForRestriction M
    (Matrix.swap ℝ i j) (isSignedPermutationMatrix_swap i j)
  apply Lp.ext
  filter_upwards
    [coeFn_swapVectorL2Action M i j (swapVectorL2Action M i j F),
      hS.quasiMeasurePreserving.ae (coeFn_swapVectorL2Action M i j F)]
      with omega houter hinner
  rw [houter, hinner, rotatePotentialSequenceForRestriction_swap_self,
    hilbertSwap_self_apply]

/-- Coordinate formula for the simultaneous sample/value sign flip. -/
theorem vectorL2Coord_signFlipVectorL2Action {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i k : Fin d)
    (F : Stationary.VectorL2 d M.P.toMeasure) :
    Stationary.vectorL2Coord (mu := M.P.toMeasure) k
        (signFlipVectorL2Action M i F) =
      (if k = i then (-1 : ℝ) else 1) •
        signFlipSampleL2Action M i
          (Stationary.vectorL2Coord (mu := M.P.toMeasure) k F) := by
  let S := rotatePotentialSequenceForRestriction (signFlipMatrix i)
    (isSignedPermutationMatrix_signFlipMatrix i)
  let hS := measurePreserving_rotatePotentialSequenceForRestriction M
    (signFlipMatrix i) (isSignedPermutationMatrix_signFlipMatrix i)
  let s : ℝ := if k = i then -1 else 1
  apply Lp.ext
  filter_upwards
    [coeFn_vectorL2Coord M k (signFlipVectorL2Action M i F),
      coeFn_signFlipVectorL2Action M i F,
      Lp.coeFn_smul s (signFlipSampleL2Action M i
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) k F)),
      coeFn_signFlipSampleL2Action M i
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) k F),
      hS.quasiMeasurePreserving.ae (coeFn_vectorL2Coord M k F)]
      with omega hcoord haction hsmul hsample hsource
  rw [hcoord, haction, hsmul]
  change (hilbertSignFlip i (F (S omega))) k =
    s * (signFlipSampleL2Action M i
      (Stationary.vectorL2Coord (mu := M.P.toMeasure) k F) :
        _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ) omega
  rw [hsample, hsource]
  change (hilbertSignFlip i (F (S omega))) k = s * F (S omega) k
  by_cases hki : k = i
  · subst k
    simp [hilbertSignFlip, s]
  · simp [hilbertSignFlip, s, hki]

/-- Coordinate formula for the simultaneous sample/value coordinate swap. -/
theorem vectorL2Coord_swapVectorL2Action {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i j k : Fin d)
    (F : Stationary.VectorL2 d M.P.toMeasure) :
    Stationary.vectorL2Coord (mu := M.P.toMeasure) k
        (swapVectorL2Action M i j F) =
      swapSampleL2Action M i j
        (Stationary.vectorL2Coord (mu := M.P.toMeasure)
          (Equiv.swap i j k) F) := by
  let S := rotatePotentialSequenceForRestriction (Matrix.swap ℝ i j)
    (isSignedPermutationMatrix_swap i j)
  let hS := measurePreserving_rotatePotentialSequenceForRestriction M
    (Matrix.swap ℝ i j) (isSignedPermutationMatrix_swap i j)
  apply Lp.ext
  filter_upwards
    [coeFn_vectorL2Coord M k (swapVectorL2Action M i j F),
      coeFn_swapVectorL2Action M i j F,
      coeFn_swapSampleL2Action M i j
        (Stationary.vectorL2Coord (mu := M.P.toMeasure)
          (Equiv.swap i j k) F),
      hS.quasiMeasurePreserving.ae
        (coeFn_vectorL2Coord M (Equiv.swap i j k) F)]
      with omega hcoord haction hsample hsource
  rw [hcoord, haction, hsample, hsource]
  change (hilbertSwap i j (F (S omega))) k =
    F (S omega) (Equiv.swap i j k)
  simp [hilbertSwap]

/-- Coordinate swaps carry full strong horizontal gradients to full strong
horizontal gradients. -/
theorem hasHorizontalGradient_swapSampleL2Action {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i j : Fin d)
    {phi : Stationary.ScalarL2 M.P.toMeasure}
    {F : Stationary.VectorL2 d M.P.toMeasure}
    (hgrad : letI := potentialSequenceVAddInvariant M
      Stationary.HasHorizontalGradient (mu := M.P.toMeasure) phi F) :
    letI := potentialSequenceVAddInvariant M
    Stationary.HasHorizontalGradient (mu := M.P.toMeasure)
      (swapSampleL2Action M i j phi) (swapVectorL2Action M i j F) := by
  let := potentialSequenceVAddInvariant M
  intro k
  let l : Fin d := Equiv.swap i j k
  have hbasis : swapVecContinuousLinearEquiv i j
      (Pi.single l 1 : Vec d) = Pi.single k 1 := by
    calc
      swapVecContinuousLinearEquiv i j (Pi.single l 1 : Vec d) =
          Pi.single (Equiv.swap i j l) 1 := by
        simpa only [basisVec] using!
          swapVecContinuousLinearEquiv_basisVec i j l
      _ = Pi.single k 1 := by simp [l]
  have hpath :
      (fun t : ℝ => Stationary.koopman (mu := M.P.toMeasure)
        (t • (Pi.single k 1 : Vec d)) (swapSampleL2Action M i j phi)) =
      fun t : ℝ => swapSampleL2Action M i j
        (Stationary.koopman (mu := M.P.toMeasure)
          (t • (Pi.single l 1 : Vec d)) phi) := by
    funext t
    symm
    calc
      swapSampleL2Action M i j
          (Stationary.koopman (mu := M.P.toMeasure)
            (t • (Pi.single l 1 : Vec d)) phi) =
        Stationary.koopman (mu := M.P.toMeasure)
          (swapVecContinuousLinearEquiv i j
            (t • (Pi.single l 1 : Vec d)))
          (swapSampleL2Action M i j phi) :=
        swapSampleL2Action_koopman M i j _ phi
      _ = Stationary.koopman (mu := M.P.toMeasure)
          (t • (Pi.single k 1 : Vec d))
          (swapSampleL2Action M i j phi) := by rw [map_smul, hbasis]
  rw [hpath, vectorL2Coord_swapVectorL2Action]
  exact (swapSampleL2Action M i j).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
    |>.comp_hasDerivAt 0 (hgrad l)

/-- Coordinate sign flips carry full strong horizontal gradients to full
strong horizontal gradients. -/
theorem hasHorizontalGradient_signFlipSampleL2Action {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i : Fin d)
    {phi : Stationary.ScalarL2 M.P.toMeasure}
    {F : Stationary.VectorL2 d M.P.toMeasure}
    (hgrad : letI := potentialSequenceVAddInvariant M
      Stationary.HasHorizontalGradient (mu := M.P.toMeasure) phi F) :
    letI := potentialSequenceVAddInvariant M
    Stationary.HasHorizontalGradient (mu := M.P.toMeasure)
      (signFlipSampleL2Action M i phi) (signFlipVectorL2Action M i F) := by
  let := potentialSequenceVAddInvariant M
  intro k
  by_cases hki : k = i
  · subst k
    have hbasis : signFlipVecContinuousLinearEquiv i
        (Pi.single i 1 : Vec d) = -(Pi.single i 1 : Vec d) := by
      rw [show (Pi.single i 1 : Vec d) = basisVec i by rfl,
        signFlipVecContinuousLinearEquiv_basisVec]
      simp
    have hpath :
        (fun t : ℝ => Stationary.koopman (mu := M.P.toMeasure)
          (t • (Pi.single i 1 : Vec d)) (signFlipSampleL2Action M i phi)) =
        fun t : ℝ => signFlipSampleL2Action M i
          (Stationary.koopman (mu := M.P.toMeasure)
            ((-t) • (Pi.single i 1 : Vec d)) phi) := by
      funext t
      symm
      calc
        signFlipSampleL2Action M i
            (Stationary.koopman (mu := M.P.toMeasure)
              ((-t) • (Pi.single i 1 : Vec d)) phi) =
          Stationary.koopman (mu := M.P.toMeasure)
            (signFlipVecContinuousLinearEquiv i
              ((-t) • (Pi.single i 1 : Vec d)))
            (signFlipSampleL2Action M i phi) :=
          signFlipSampleL2Action_koopman M i _ phi
        _ = Stationary.koopman (mu := M.P.toMeasure)
            (t • (Pi.single i 1 : Vec d))
            (signFlipSampleL2Action M i phi) := by
          rw [map_smul, hbasis]
          simp
    have hneg : HasDerivAt
        (fun t : ℝ => Stationary.koopman (mu := M.P.toMeasure)
          ((-t) • (Pi.single i 1 : Vec d)) phi)
        (-(Stationary.vectorL2Coord (mu := M.P.toMeasure) i F)) 0 := by
      have hbase : HasFDerivAt
          (fun t : ℝ => Stationary.koopman (mu := M.P.toMeasure)
            (t • (Pi.single i 1 : Vec d)) phi)
          (ContinuousLinearMap.toSpanSingleton ℝ
            (Stationary.vectorL2Coord (mu := M.P.toMeasure) i F)) (-0) := by
        simpa only [neg_zero] using! (hgrad i).hasFDerivAt
      have hcomp := hbase.comp_hasDerivAt 0 (hasDerivAt_neg (0 : ℝ))
      simpa only [Function.comp_def, neg_smul,
        ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.smulRight_apply, one_apply_eq_self,
        one_smul] using! hcomp
    rw [hpath, vectorL2Coord_signFlipVectorL2Action, ite_eq_left rfl,
      neg_one_smul]
    simpa only [Function.comp_def, map_neg] using!
      ((signFlipSampleL2Action M i).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
        |>.comp_hasDerivAt 0 hneg)
  · have hbasis : signFlipVecContinuousLinearEquiv i
        (Pi.single k 1 : Vec d) = Pi.single k 1 := by
      simpa only [basisVec, ite_eq_right hki, one_smul] using!
        signFlipVecContinuousLinearEquiv_basisVec i k
    have hpath :
        (fun t : ℝ => Stationary.koopman (mu := M.P.toMeasure)
          (t • (Pi.single k 1 : Vec d)) (signFlipSampleL2Action M i phi)) =
        fun t : ℝ => signFlipSampleL2Action M i
          (Stationary.koopman (mu := M.P.toMeasure)
            (t • (Pi.single k 1 : Vec d)) phi) := by
      funext t
      symm
      calc
        signFlipSampleL2Action M i
            (Stationary.koopman (mu := M.P.toMeasure)
              (t • (Pi.single k 1 : Vec d)) phi) =
          Stationary.koopman (mu := M.P.toMeasure)
            (signFlipVecContinuousLinearEquiv i
              (t • (Pi.single k 1 : Vec d)))
            (signFlipSampleL2Action M i phi) :=
          signFlipSampleL2Action_koopman M i _ phi
        _ = Stationary.koopman (mu := M.P.toMeasure)
            (t • (Pi.single k 1 : Vec d))
            (signFlipSampleL2Action M i phi) := by rw [map_smul, hbasis]
    rw [hpath, vectorL2Coord_signFlipVectorL2Action, ite_eq_right hki, one_smul]
    exact (signFlipSampleL2Action M i).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
      |>.comp_hasDerivAt 0 (hgrad k)

/-- The closed stationary potential subspace is invariant under a coordinate
sign flip. -/
theorem signFlipVectorL2Action_mem_stationaryPotentialSubspace {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i : Fin d)
    {F : Stationary.VectorL2 d M.P.toMeasure}
    (hF : F ∈ @Stationary.stationaryPotentialSubspace d (_root_.SubdiffusiveProcess.Model.PotentialSample d)
      inferInstance M.P.toMeasure (potentialSampleAddAction d)
      (potentialSampleMeasurableConstVAdd d)
      (potentialSequenceVAddInvariant M)) :
    signFlipVectorL2Action M i F ∈
      @Stationary.stationaryPotentialSubspace d (_root_.SubdiffusiveProcess.Model.PotentialSample d)
        inferInstance M.P.toMeasure (potentialSampleAddAction d)
        (potentialSampleMeasurableConstVAdd d)
        (potentialSequenceVAddInvariant M) := by
  let := potentialSequenceVAddInvariant M
  let S := Stationary.stationaryPotentialSubspace
    (mu := M.P.toMeasure) (d := d)
  set T : Submodule ℝ (Stationary.VectorL2 d M.P.toMeasure) :=
    Submodule.comap (signFlipVectorL2Action M i).toLinearMap S with hT
  have hsub : Stationary.horizontalGradientRange
      (mu := M.P.toMeasure) (d := d) ≤ T := by
    rintro G ⟨psi, hpsi⟩
    exact Submodule.le_topologicalClosure
      (Stationary.horizontalGradientRange (mu := M.P.toMeasure) (d := d))
      ⟨signFlipSampleL2Action M i psi,
        hasHorizontalGradient_signFlipSampleL2Action M i hpsi⟩
  have hcoe : (T : Set (Stationary.VectorL2 d M.P.toMeasure)) =
      (signFlipVectorL2Action M i) ⁻¹' (S : Set _) := rfl
  have hclosed : IsClosed (T : Set (Stationary.VectorL2 d M.P.toMeasure)) := by
    rw [hcoe]
    exact IsClosed.preimage (signFlipVectorL2Action M i).continuous
      (Submodule.isClosed_topologicalClosure
        (Stationary.horizontalGradientRange (mu := M.P.toMeasure) (d := d)))
  exact Submodule.topologicalClosure_minimal
    (Stationary.horizontalGradientRange (mu := M.P.toMeasure) (d := d))
    hsub hclosed hF

/-- The closed stationary potential subspace is invariant under a coordinate
swap. -/
theorem swapVectorL2Action_mem_stationaryPotentialSubspace {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i j : Fin d)
    {F : Stationary.VectorL2 d M.P.toMeasure}
    (hF : F ∈ @Stationary.stationaryPotentialSubspace d (_root_.SubdiffusiveProcess.Model.PotentialSample d)
      inferInstance M.P.toMeasure (potentialSampleAddAction d)
      (potentialSampleMeasurableConstVAdd d)
      (potentialSequenceVAddInvariant M)) :
    swapVectorL2Action M i j F ∈
      @Stationary.stationaryPotentialSubspace d (_root_.SubdiffusiveProcess.Model.PotentialSample d)
        inferInstance M.P.toMeasure (potentialSampleAddAction d)
        (potentialSampleMeasurableConstVAdd d)
        (potentialSequenceVAddInvariant M) := by
  let := potentialSequenceVAddInvariant M
  let S := Stationary.stationaryPotentialSubspace
    (mu := M.P.toMeasure) (d := d)
  set T : Submodule ℝ (Stationary.VectorL2 d M.P.toMeasure) :=
    Submodule.comap (swapVectorL2Action M i j).toLinearMap S with hT
  have hsub : Stationary.horizontalGradientRange
      (mu := M.P.toMeasure) (d := d) ≤ T := by
    rintro G ⟨psi, hpsi⟩
    exact Submodule.le_topologicalClosure
      (Stationary.horizontalGradientRange (mu := M.P.toMeasure) (d := d))
      ⟨swapSampleL2Action M i j psi,
        hasHorizontalGradient_swapSampleL2Action M i j hpsi⟩
  have hcoe : (T : Set (Stationary.VectorL2 d M.P.toMeasure)) =
      (swapVectorL2Action M i j) ⁻¹' (S : Set _) := rfl
  have hclosed : IsClosed (T : Set (Stationary.VectorL2 d M.P.toMeasure)) := by
    rw [hcoe]
    exact IsClosed.preimage (swapVectorL2Action M i j).continuous
      (Submodule.isClosed_topologicalClosure
        (Stationary.horizontalGradientRange (mu := M.P.toMeasure) (d := d)))
  exact Submodule.topologicalClosure_minimal
    (Stationary.horizontalGradientRange (mu := M.P.toMeasure) (d := d))
    hsub hclosed hF

theorem stationaryPotentialSubspace_map_signFlipVectorL2Action {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i : Fin d) :
    letI := potentialSequenceVAddInvariant M
    (Stationary.stationaryPotentialSubspace
        (mu := M.P.toMeasure) (d := d)).map
      (signFlipVectorL2Action M i).toLinearMap =
      Stationary.stationaryPotentialSubspace
        (mu := M.P.toMeasure) (d := d) := by
  let := potentialSequenceVAddInvariant M
  apply le_antisymm
  · rintro G ⟨F, hF, rfl⟩
    exact signFlipVectorL2Action_mem_stationaryPotentialSubspace M i hF
  · intro F hF
    refine ⟨signFlipVectorL2Action M i F,
      signFlipVectorL2Action_mem_stationaryPotentialSubspace M i hF, ?_⟩
    exact signFlipVectorL2Action_self_apply M i F

theorem stationaryPotentialSubspace_map_swapVectorL2Action {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i j : Fin d) :
    letI := potentialSequenceVAddInvariant M
    (Stationary.stationaryPotentialSubspace
        (mu := M.P.toMeasure) (d := d)).map
      (swapVectorL2Action M i j).toLinearMap =
      Stationary.stationaryPotentialSubspace
        (mu := M.P.toMeasure) (d := d) := by
  let := potentialSequenceVAddInvariant M
  apply le_antisymm
  · rintro G ⟨F, hF, rfl⟩
    exact swapVectorL2Action_mem_stationaryPotentialSubspace M i j hF
  · intro F hF
    refine ⟨swapVectorL2Action M i j F,
      swapVectorL2Action_mem_stationaryPotentialSubspace M i j hF, ?_⟩
    exact swapVectorL2Action_self_apply M i j F

theorem signFlipVectorL2Action_mem_stationarySolenoidalSubspace {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i : Fin d)
    {F : Stationary.VectorL2 d M.P.toMeasure}
    (hF : F ∈ @Stationary.stationarySolenoidalSubspace d (_root_.SubdiffusiveProcess.Model.PotentialSample d)
      inferInstance M.P.toMeasure (potentialSampleAddAction d)
      (potentialSampleMeasurableConstVAdd d)
      (potentialSequenceVAddInvariant M)) :
    signFlipVectorL2Action M i F ∈
      @Stationary.stationarySolenoidalSubspace d (_root_.SubdiffusiveProcess.Model.PotentialSample d)
        inferInstance M.P.toMeasure (potentialSampleAddAction d)
        (potentialSampleMeasurableConstVAdd d)
        (potentialSequenceVAddInvariant M) := by
  let := potentialSequenceVAddInvariant M
  refine (Submodule.mem_orthogonal _ _).2 fun u hu => ?_
  have hu' := signFlipVectorL2Action_mem_stationaryPotentialSubspace M i hu
  have hzero := (Submodule.mem_orthogonal _ _).1 hF _ hu'
  calc
    inner ℝ u (signFlipVectorL2Action M i F) =
        inner ℝ
          (signFlipVectorL2Action M i (signFlipVectorL2Action M i u))
          (signFlipVectorL2Action M i F) := by
      rw [signFlipVectorL2Action_self_apply]
    _ = inner ℝ (signFlipVectorL2Action M i u) F :=
      (signFlipVectorL2Action M i).inner_map_map _ _
    _ = 0 := hzero

theorem swapVectorL2Action_mem_stationarySolenoidalSubspace {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i j : Fin d)
    {F : Stationary.VectorL2 d M.P.toMeasure}
    (hF : F ∈ @Stationary.stationarySolenoidalSubspace d (_root_.SubdiffusiveProcess.Model.PotentialSample d)
      inferInstance M.P.toMeasure (potentialSampleAddAction d)
      (potentialSampleMeasurableConstVAdd d)
      (potentialSequenceVAddInvariant M)) :
    swapVectorL2Action M i j F ∈
      @Stationary.stationarySolenoidalSubspace d (_root_.SubdiffusiveProcess.Model.PotentialSample d)
        inferInstance M.P.toMeasure (potentialSampleAddAction d)
        (potentialSampleMeasurableConstVAdd d)
        (potentialSequenceVAddInvariant M) := by
  let := potentialSequenceVAddInvariant M
  refine (Submodule.mem_orthogonal _ _).2 fun u hu => ?_
  have hu' := swapVectorL2Action_mem_stationaryPotentialSubspace M i j hu
  have hzero := (Submodule.mem_orthogonal _ _).1 hF _ hu'
  calc
    inner ℝ u (swapVectorL2Action M i j F) =
        inner ℝ
          (swapVectorL2Action M i j (swapVectorL2Action M i j u))
          (swapVectorL2Action M i j F) := by
      rw [swapVectorL2Action_self_apply]
    _ = inner ℝ (swapVectorL2Action M i j u) F :=
      (swapVectorL2Action M i j).inner_map_map _ _
    _ = 0 := hzero

/-- Orthogonal stationary-potential projection commutes with coordinate sign
flips. -/
theorem signFlipVectorL2Action_stationaryPotentialProjection {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i : Fin d)
    (F : Stationary.VectorL2 d M.P.toMeasure) :
    letI := potentialSequenceVAddInvariant M
    signFlipVectorL2Action M i
        (Stationary.stationaryPotentialProjection
          (mu := M.P.toMeasure) F) =
      Stationary.stationaryPotentialProjection (mu := M.P.toMeasure)
        (signFlipVectorL2Action M i F) := by
  let := potentialSequenceVAddInvariant M
  apply Stationary.eq_stationaryPotentialProjection_of_mem_of_sub_mem_orthogonal
  · exact signFlipVectorL2Action_mem_stationaryPotentialSubspace M i
      (Stationary.stationaryPotentialProjection_mem F)
  · rw [← map_sub]
    exact signFlipVectorL2Action_mem_stationarySolenoidalSubspace M i
      (Stationary.sub_stationaryPotentialProjection_mem_orthogonal F)

/-- Orthogonal stationary-potential projection commutes with coordinate
swaps. -/
theorem swapVectorL2Action_stationaryPotentialProjection {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i j : Fin d)
    (F : Stationary.VectorL2 d M.P.toMeasure) :
    letI := potentialSequenceVAddInvariant M
    swapVectorL2Action M i j
        (Stationary.stationaryPotentialProjection
          (mu := M.P.toMeasure) F) =
      Stationary.stationaryPotentialProjection (mu := M.P.toMeasure)
        (swapVectorL2Action M i j F) := by
  let := potentialSequenceVAddInvariant M
  apply Stationary.eq_stationaryPotentialProjection_of_mem_of_sub_mem_orthogonal
  · exact swapVectorL2Action_mem_stationaryPotentialSubspace M i j
      (Stationary.stationaryPotentialProjection_mem F)
  · rw [← map_sub]
    exact swapVectorL2Action_mem_stationarySolenoidalSubspace M i j
      (Stationary.sub_stationaryPotentialProjection_mem_orthogonal F)

/-- Exact covariance of the `L²` one-step forcing under a coordinate sign
flip. -/
theorem signFlipVectorL2Action_oneStepOriginForcingL2 {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (i : Fin d) (p : Vec d) (hh : 0 < h) :
    signFlipVectorL2Action M i (oneStepOriginForcingL2 M n h p hh) =
      oneStepOriginForcingL2 M n h
        (signFlipVecContinuousLinearEquiv i p) hh := by
  apply Lp.ext
  filter_upwards
    [coeFn_signFlipVectorL2Action M i
      (oneStepOriginForcingL2 M n h p hh),
      (measurePreserving_rotatePotentialSequenceForRestriction M
        (signFlipMatrix i)
        (isSignedPermutationMatrix_signFlipMatrix i)).quasiMeasurePreserving.ae
          (MemLp.coeFn_toLp (memLp_two_oneStepOriginForcing M n h p hh)),
      MemLp.coeFn_toLp (memLp_two_oneStepOriginForcing M n h
        (signFlipVecContinuousLinearEquiv i p) hh)]
      with omega haction hsource htarget
  rw [haction]
  change hilbertSignFlip i
      (((memLp_two_oneStepOriginForcing M n h p hh).toLp
        (oneStepOriginForcing M n h p) : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d)
          (rotatePotentialSequenceForRestriction (signFlipMatrix i)
            (isSignedPermutationMatrix_signFlipMatrix i) omega)) =
    ((memLp_two_oneStepOriginForcing M n h
      (signFlipVecContinuousLinearEquiv i p) hh).toLp
        (oneStepOriginForcing M n h
          (signFlipVecContinuousLinearEquiv i p)) : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d) omega
  rw [hsource, htarget]
  exact oneStepOriginForcing_rotate_signFlip M n h i p omega

/-- Exact covariance of the `L²` one-step forcing under a coordinate swap. -/
theorem swapVectorL2Action_oneStepOriginForcingL2 {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (i j : Fin d) (p : Vec d) (hh : 0 < h) :
    swapVectorL2Action M i j (oneStepOriginForcingL2 M n h p hh) =
      oneStepOriginForcingL2 M n h
        (swapVecContinuousLinearEquiv i j p) hh := by
  apply Lp.ext
  filter_upwards
    [coeFn_swapVectorL2Action M i j
      (oneStepOriginForcingL2 M n h p hh),
      (measurePreserving_rotatePotentialSequenceForRestriction M
        (Matrix.swap ℝ i j)
        (isSignedPermutationMatrix_swap i j)).quasiMeasurePreserving.ae
          (MemLp.coeFn_toLp (memLp_two_oneStepOriginForcing M n h p hh)),
      MemLp.coeFn_toLp (memLp_two_oneStepOriginForcing M n h
        (swapVecContinuousLinearEquiv i j p) hh)]
      with omega haction hsource htarget
  rw [haction]
  change hilbertSwap i j
      (((memLp_two_oneStepOriginForcing M n h p hh).toLp
        (oneStepOriginForcing M n h p) : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d)
          (rotatePotentialSequenceForRestriction (Matrix.swap ℝ i j)
            (isSignedPermutationMatrix_swap i j) omega)) =
    ((memLp_two_oneStepOriginForcing M n h
      (swapVecContinuousLinearEquiv i j p) hh).toLp
        (oneStepOriginForcing M n h
          (swapVecContinuousLinearEquiv i j p)) : _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d) omega
  rw [hsource, htarget]
  exact oneStepOriginForcing_rotate_swap M n h i j p omega

/-- Covariance of the projected one-step forcing under a coordinate sign
flip. -/
theorem signFlipVectorL2Action_oneStepPotentialProjection {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (i : Fin d) (p : Vec d) (hh : 0 < h) :
    signFlipVectorL2Action M i
        (oneStepPotentialProjection M n h p hh) =
      oneStepPotentialProjection M n h
        (signFlipVecContinuousLinearEquiv i p) hh := by
  let := potentialSequenceVAddInvariant M
  change signFlipVectorL2Action M i
      (Stationary.stationaryPotentialProjection (mu := M.P.toMeasure)
        (oneStepOriginForcingL2 M n h p hh)) =
    Stationary.stationaryPotentialProjection (mu := M.P.toMeasure)
      (oneStepOriginForcingL2 M n h
        (signFlipVecContinuousLinearEquiv i p) hh)
  rw [signFlipVectorL2Action_stationaryPotentialProjection,
    signFlipVectorL2Action_oneStepOriginForcingL2]

/-- Covariance of the projected one-step forcing under a coordinate swap. -/
theorem swapVectorL2Action_oneStepPotentialProjection {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (i j : Fin d) (p : Vec d) (hh : 0 < h) :
    swapVectorL2Action M i j
        (oneStepPotentialProjection M n h p hh) =
      oneStepPotentialProjection M n h
        (swapVecContinuousLinearEquiv i j p) hh := by
  let := potentialSequenceVAddInvariant M
  change swapVectorL2Action M i j
      (Stationary.stationaryPotentialProjection (mu := M.P.toMeasure)
        (oneStepOriginForcingL2 M n h p hh)) =
    Stationary.stationaryPotentialProjection (mu := M.P.toMeasure)
      (oneStepOriginForcingL2 M n h
        (swapVecContinuousLinearEquiv i j p) hh)
  rw [swapVectorL2Action_stationaryPotentialProjection,
    swapVectorL2Action_oneStepOriginForcingL2]

/-- Signed-coordinate reflection forces distinct coordinate components of
the projected one-step forcing to be orthogonal. -/
theorem inner_oneStepPotentialProjection_basis_ne_eq_zero {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (i j : Fin d) (hij : i ≠ j) (hh : 0 < h) :
    inner ℝ
        (oneStepPotentialProjection M n h (Pi.single i 1) hh)
        (oneStepPotentialProjection M n h (Pi.single j 1) hh) = 0 := by
  let P_i := oneStepPotentialProjection M n h (Pi.single i 1) hh
  let P_j := oneStepPotentialProjection M n h (Pi.single j 1) hh
  let A := signFlipVectorL2Action M i
  have hbi : signFlipVecContinuousLinearEquiv i
      (Pi.single i 1 : Vec d) = -(Pi.single i 1 : Vec d) := by
    rw [show (Pi.single i 1 : Vec d) = basisVec i by rfl,
      signFlipVecContinuousLinearEquiv_basisVec]
    simp
  have hbj : signFlipVecContinuousLinearEquiv i
      (Pi.single j 1 : Vec d) = Pi.single j 1 := by
    simpa only [basisVec, ite_eq_right (Ne.symm hij), one_smul] using!
      signFlipVecContinuousLinearEquiv_basisVec i j
  have hAi : A P_i = -P_i := by
    calc
      A P_i = oneStepPotentialProjection M n h
          (signFlipVecContinuousLinearEquiv i (Pi.single i 1)) hh :=
        signFlipVectorL2Action_oneStepPotentialProjection M n h i _ hh
      _ = oneStepPotentialProjection M n h (-(Pi.single i 1)) hh := by rw [hbi]
      _ = -P_i := by
        change oneStepPotentialProjectionLinear M n h hh (-(Pi.single i 1)) =
          -oneStepPotentialProjectionLinear M n h hh (Pi.single i 1)
        exact map_neg _ _
  have hAj : A P_j = P_j := by
    calc
      A P_j = oneStepPotentialProjection M n h
          (signFlipVecContinuousLinearEquiv i (Pi.single j 1)) hh :=
        signFlipVectorL2Action_oneStepPotentialProjection M n h i _ hh
      _ = P_j := by rw [hbj]
  have hinner := A.inner_map_map P_i P_j
  have hneg : -inner ℝ P_i P_j = inner ℝ P_i P_j := by
    simpa only [hAi, hAj, inner_neg_left] using! hinner
  change inner ℝ P_i P_j = 0
  linarith

/-- Coordinate permutation forces all diagonal projected energies to agree. -/
theorem norm_sq_oneStepPotentialProjection_basis_eq {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (i j : Fin d) (hh : 0 < h) :
    ‖oneStepPotentialProjection M n h (Pi.single i 1) hh‖ ^ 2 =
      ‖oneStepPotentialProjection M n h (Pi.single j 1) hh‖ ^ 2 := by
  by_cases hij : i = j
  · subst j
    rfl
  · let P_i := oneStepPotentialProjection M n h (Pi.single i 1) hh
    let P_j := oneStepPotentialProjection M n h (Pi.single j 1) hh
    let A := swapVectorL2Action M i j
    have hbij : swapVecContinuousLinearEquiv i j
        (Pi.single i 1 : Vec d) = Pi.single j 1 := by
      calc
        swapVecContinuousLinearEquiv i j (Pi.single i 1 : Vec d) =
            Pi.single (Equiv.swap i j i) 1 := by
          simpa only [basisVec] using!
            swapVecContinuousLinearEquiv_basisVec i j i
        _ = Pi.single j 1 := by rw [Equiv.swap_apply_left]
    have hAi : A P_i = P_j := by
      calc
        A P_i = oneStepPotentialProjection M n h
            (swapVecContinuousLinearEquiv i j (Pi.single i 1)) hh :=
          swapVectorL2Action_oneStepPotentialProjection M n h i j _ hh
        _ = P_j := by rw [hbij]
    calc
      ‖P_i‖ ^ 2 = ‖A P_i‖ ^ 2 := by rw [A.norm_map]
      _ = ‖P_j‖ ^ 2 := by rw [hAi]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
