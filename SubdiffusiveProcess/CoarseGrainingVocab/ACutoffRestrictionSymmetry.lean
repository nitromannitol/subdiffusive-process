module

public import SubdiffusiveProcess.CoarseGrainingVocab.AhomCharacterization
public import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffRestrictionLaw
public import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedProviders
public import Homogenization.Book.Ch04.Theorems.DilationLaw

@[expose] public section

/-!
# Structural symmetries of the finite-cutoff restriction law

Stationarity, signed-coordinate isotropy, and adjoint invariance are transported
from the shell-sequence law to the literal scalar cutoff law.

The sequence-law arguments reuse the GMC product-law proofs for annealed scalarization.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- Componentwise signed-coordinate rotation of the potential sequence. -/
def rotatePotentialSequenceForRestriction {d : ℕ} (R : Mat d)
    (hR : IsSignedPermutationMatrix R) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : _root_.SubdiffusiveProcess.Model.PotentialSample d :=
  fun k => _root_.SubdiffusiveProcess.Model.PotentialField.rotate R hR (omega k)

theorem measurable_rotatePotentialSequenceForRestriction {d : ℕ} (R : Mat d)
    (hR : IsSignedPermutationMatrix R) :
    Measurable (rotatePotentialSequenceForRestriction (d := d) R hR) := by
  apply measurable_pi_iff.mpr
  intro k
  exact (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_rotate R hR).comp
    (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate k)

private theorem rotate_triadicScale {d : ℕ} (R : Mat d)
    (hR : IsSignedPermutationMatrix R) (k : ℕ)
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) :
    _root_.SubdiffusiveProcess.Model.PotentialField.rotate R hR
        (_root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k g) =
      _root_.SubdiffusiveProcess.Model.PotentialField.triadicScale k
        (_root_.SubdiffusiveProcess.Model.PotentialField.rotate R hR g) := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d094_rotate_triadicScale (d := d) (R := R) (hR := hR) (k := k) (g := g)

private theorem potentialMarginalLaw_isotropic {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ) (R : Mat d)
    (hR : IsSignedPermutationMatrix R) :
    Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.rotate R hR)
        (_root_.SubdiffusiveProcess.Model.potentialMarginalLaw M.P k).toMeasure =
      (_root_.SubdiffusiveProcess.Model.potentialMarginalLaw M.P k).toMeasure := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d099_potentialMarginalLaw_isotropic (d := d) (M := M) (k := k) (R := R) (hR := hR)

theorem potentialSequenceLaw_isotropic_forRestriction {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (R : Mat d)
    (hR : IsSignedPermutationMatrix R) :
    Measure.map (rotatePotentialSequenceForRestriction (d := d) R hR)
        M.P.toMeasure = M.P.toMeasure := by
  have hprod := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun k : ℕ => _root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate k)).mp
      M.shellPrefix.independent
  have hrotInd : iIndepFun
      (fun k : ℕ => fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        _root_.SubdiffusiveProcess.Model.PotentialField.rotate R hR (omega k))
      M.P.toMeasure :=
    M.shellPrefix.independent.comp
      (fun _ => _root_.SubdiffusiveProcess.Model.PotentialField.rotate R hR)
      (fun _ => _root_.SubdiffusiveProcess.Model.PotentialField.measurable_rotate R hR)
  have hrotProd := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun _ : ℕ =>
      (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_rotate R hR).comp
        (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate _))).mp hrotInd
  calc
    Measure.map (rotatePotentialSequenceForRestriction (d := d) R hR)
        M.P.toMeasure =
      Measure.infinitePi (fun k : ℕ =>
        Measure.map (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
          _root_.SubdiffusiveProcess.Model.PotentialField.rotate R hR (omega k))
          M.P.toMeasure) := by
      simpa only [rotatePotentialSequenceForRestriction, Function.comp_def] using! hrotProd
    _ = Measure.infinitePi (fun k : ℕ =>
        Measure.map (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => omega k) M.P.toMeasure) := by
      apply congrArg Measure.infinitePi
      funext k
      calc
        Measure.map (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
            _root_.SubdiffusiveProcess.Model.PotentialField.rotate R hR (omega k))
            M.P.toMeasure =
          Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.rotate R hR)
            (Measure.map (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => omega k) M.P.toMeasure) := by
              change Measure.map
                (_root_.SubdiffusiveProcess.Model.PotentialField.rotate R hR ∘
                  fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => omega k) M.P.toMeasure = _
              rw [Measure.map_map
                (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_rotate R hR)
                (_root_.SubdiffusiveProcess.Model.measurable_potentialCoordinate k)]
        _ = Measure.map (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => omega k) M.P.toMeasure :=
          potentialMarginalLaw_isotropic M k R hR
    _ = Measure.map (fun omega (k : ℕ) => omega k) M.P.toMeasure := hprod.symm
    _ = M.P.toMeasure := Measure.map_id'

private theorem aCutoff_rotatePotentialSequenceForRestriction {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (R : Mat d)
    (hR : IsSignedPermutationMatrix R) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) :
    _root_.SubdiffusiveProcess.Model.aCutoff M L
        (rotatePotentialSequenceForRestriction R hR omega) x =
      _root_.SubdiffusiveProcess.Model.aCutoff M L omega (matVecMul R x) := by
  simp [_root_.SubdiffusiveProcess.Model.aCutoff,
    rotatePotentialSequenceForRestriction]

private theorem aCutoffRegCoeffField_rotate {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (R : Mat d)
    (hR : IsSignedPermutationMatrix R) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    aCutoffRegCoeffField M L
        (rotatePotentialSequenceForRestriction R hR omega) =
      rotateReg R hR (aCutoffRegCoeffField M L omega) := by
  apply RegCoeffField.ext
  intro x
  rw [aCutoffRegCoeffField_apply, rotateReg_apply,
    aCutoffRegCoeffField_apply,
    aCutoff_rotatePotentialSequenceForRestriction M L R hR omega x]
  simp [scalarMatrix, hR.transpose_mul_self]

/-- Translation covariance of the regular finite-cutoff coefficient field. -/
theorem aCutoffRegCoeffField_translate {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (z : Vec d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    aCutoffRegCoeffField M L (translatePotentialSequence z omega) =
      translateReg z (aCutoffRegCoeffField M L omega) := by
  apply RegCoeffField.ext
  intro x
  rw [aCutoffRegCoeffField_apply, translateReg_apply,
    aCutoffRegCoeffField_apply,
    aCutoff_translatePotentialSequence M L z omega x]

/-- The finite-cutoff restriction law is stationary under integer shifts. -/
theorem aCutoffRestrictionLaw_stationary {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) :
    Ch04.RestrictionStationaryLaw (aCutoffRestrictionLaw M L) := by
  intro z
  let w : Vec d := intVecToRealVec z
  rw [aCutoffRestrictionLaw_eq_map,
    Measure.map_map (measurable_translateReg w)
      (measurable_aCutoffRegCoeffField M L)]
  calc
    Measure.map (translateReg w ∘ aCutoffRegCoeffField M L) M.P.toMeasure =
        Measure.map (aCutoffRegCoeffField M L ∘ translatePotentialSequence w)
          M.P.toMeasure := by
      apply congrArg (fun f : _root_.SubdiffusiveProcess.Model.PotentialSample d → RegCoeffField d =>
        Measure.map f M.P.toMeasure)
      funext omega
      exact (aCutoffRegCoeffField_translate M L w omega).symm
    _ = Measure.map (aCutoffRegCoeffField M L)
        (Measure.map (translatePotentialSequence w) M.P.toMeasure) :=
      (Measure.map_map (measurable_aCutoffRegCoeffField M L)
        (measurable_translatePotentialSequence w)).symm
    _ = Measure.map (aCutoffRegCoeffField M L) M.P.toMeasure := by
      rw [potentialSequenceLaw_stationary M w]

/-- The finite-cutoff restriction law is invariant under signed-coordinate
permutations. -/
theorem aCutoffRestrictionLaw_isotropic {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) :
    Ch04.RestrictionIsotropicLaw (aCutoffRestrictionLaw M L) := by
  intro R hR
  rw [aCutoffRestrictionLaw_eq_map,
    Measure.map_map (measurable_rotateReg R hR)
      (measurable_aCutoffRegCoeffField M L)]
  calc
    Measure.map (rotateReg R hR ∘ aCutoffRegCoeffField M L) M.P.toMeasure =
        Measure.map (aCutoffRegCoeffField M L ∘
          rotatePotentialSequenceForRestriction R hR) M.P.toMeasure := by
      apply congrArg (fun f : _root_.SubdiffusiveProcess.Model.PotentialSample d → RegCoeffField d =>
        Measure.map f M.P.toMeasure)
      funext omega
      exact (aCutoffRegCoeffField_rotate M L R hR omega).symm
    _ = Measure.map (aCutoffRegCoeffField M L)
        (Measure.map (rotatePotentialSequenceForRestriction R hR)
          M.P.toMeasure) :=
      (Measure.map_map (measurable_aCutoffRegCoeffField M L)
        (measurable_rotatePotentialSequenceForRestriction R hR)).symm
    _ = Measure.map (aCutoffRegCoeffField M L) M.P.toMeasure := by
      rw [potentialSequenceLaw_isotropic_forRestriction M R hR]

private theorem adjoint_aCutoffRegCoeffField {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    adjointReg (aCutoffRegCoeffField M L omega) =
      aCutoffRegCoeffField M L omega := by
  apply RegCoeffField.ext
  intro x
  simp [aCutoffRegCoeffField_apply, scalarMatrix]

/-- The scalar finite-cutoff restriction law is adjoint invariant. -/
theorem aCutoffRestrictionLaw_adjoint_invariant {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) :
    Ch04.RestrictionAdjointInvariantLaw (aCutoffRestrictionLaw M L) := by
  rw [aCutoffRestrictionLaw_eq_map]
  change Measure.map adjointReg
      (Measure.map (aCutoffRegCoeffField M L) M.P.toMeasure) =
    Measure.map (aCutoffRegCoeffField M L) M.P.toMeasure
  rw [Measure.map_map measurable_adjointReg
    (measurable_aCutoffRegCoeffField M L)]
  apply congrArg (fun f : _root_.SubdiffusiveProcess.Model.PotentialSample d → RegCoeffField d =>
    Measure.map f M.P.toMeasure)
  funext omega
  exact adjoint_aCutoffRegCoeffField M L omega

end

end SubdiffusiveProcess.CoarseGrainingVocab
