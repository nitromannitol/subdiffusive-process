module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepProjectionOrbit
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-!
# Rigidity of a stationary scalar field with zero horizontal derivatives

This file supplies the elementary final step in the weak stationary Hodge
argument.  If every coordinate orbit of a scalar `L²` field has derivative
zero, then the orbit is constant on each coordinate line and hence the field
is fixed by every spatial translation.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


namespace Stationary

variable {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
variable {mu : Measure Omega}
variable [AddAction (Vec d) Omega]
variable [MeasurableConstVAdd (Vec d) Omega]
variable [VAddInvariantMeasure (Vec d) Omega mu]

/-- A scalar `L²` field whose coordinate Koopman orbits have derivative zero
is fixed by every translation along a coordinate axis. -/
theorem koopman_smul_single_eq_of_hasDerivAt_zero
    (Y : ScalarL2 mu)
    (hzero : ∀ (i : Fin d) (t : ℝ),
      HasDerivAt
        (fun s : ℝ => koopman (mu := mu)
          (s • (Pi.single i 1 : Vec d)) Y)
        0 t) :
    ∀ (i : Fin d) (t : ℝ),
      koopman (mu := mu) (t • (Pi.single i 1 : Vec d)) Y = Y := by
  intro i t
  let f : ℝ → ScalarL2 mu := fun s =>
    koopman (mu := mu) (s • (Pi.single i 1 : Vec d)) Y
  have hf : Differentiable ℝ f := fun s => (hzero i s).differentiableAt
  have hfzero : ∀ s : ℝ, deriv f s = 0 := fun s => (hzero i s).deriv
  have hconst := is_const_of_deriv_eq_zero hf hfzero t 0
  simpa only [f, zero_smul, koopman_zero] using! hconst

/-- Coordinate-axis invariance implies invariance under an arbitrary
finite-dimensional translation. -/
theorem koopman_eq_of_koopman_smul_single_eq
    (Y : ScalarL2 mu)
    (hcoord : ∀ (i : Fin d) (t : ℝ),
      koopman (mu := mu) (t • (Pi.single i 1 : Vec d)) Y = Y) :
    ∀ z : Vec d, koopman (mu := mu) z Y = Y := by
  classical
  intro z
  have hsum : (∑ i : Fin d, z i • (Pi.single i 1 : Vec d)) = z := by
    ext j
    rw [Finset.sum_apply]
    change (∑ i : Fin d, z i *
      (Pi.single i (1 : ℝ) : Vec d) j) = z j
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hne
      rw [Pi.single_eq_of_ne (Ne.symm hne)]
      simp
    · simp
  rw [← hsum]
  generalize (Finset.univ : Finset (Fin d)) = s
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, koopman_zero]
  | @insert i s his ih =>
      rw [Finset.sum_insert his]
      rw [← koopman_koopman]
      rw [hcoord, ih]

/-- Zero derivatives of all coordinate Koopman orbits imply global
translation invariance. -/
theorem isGloballyTranslationInvariant_of_hasDerivAt_zero
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Y : ScalarL2 M.P.toMeasure)
    (hzero : letI := potentialSequenceVAddInvariant M
      ∀ (i : Fin d) (t : ℝ),
        HasDerivAt
          (fun s : ℝ => koopman (mu := M.P.toMeasure)
            (s • (Pi.single i 1 : Vec d)) Y)
          0 t) :
    IsGloballyTranslationInvariant M Y := by
  let := potentialSequenceVAddInvariant M
  exact koopman_eq_of_koopman_smul_single_eq Y
    (koopman_smul_single_eq_of_hasDerivAt_zero Y hzero)

/-- A zero coordinate generator at the identity remains zero at every point
of the same one-parameter Koopman orbit. -/
theorem hasDerivAt_koopman_smul_single_zero_of_hasDerivAt_zero
    (Y : ScalarL2 mu) (i : Fin d)
    (hzero : HasDerivAt
      (fun s : ℝ => koopman (mu := mu)
        (s • (Pi.single i 1 : Vec d)) Y) 0 0)
    (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => koopman (mu := mu)
        (s • (Pi.single i 1 : Vec d)) Y) 0 t := by
  have hshift : HasDerivAt (fun s : ℝ => s - t) 1 t :=
    (hasDerivAt_id t).sub_const t
  have hinner : HasDerivAt
      (fun s : ℝ => koopman (mu := mu)
        ((s - t) • (Pi.single i 1 : Vec d)) Y) 0 t := by
    have hzero' : HasDerivAt
        (fun s : ℝ => koopman (mu := mu)
          (s • (Pi.single i 1 : Vec d)) Y) 0 (t - t) := by
      simpa using! hzero
    simpa only [one_smul, Function.comp_def] using!
      hzero'.scomp (h := fun s : ℝ => s - t) t hshift
  have hout := (koopman (mu := mu)
    (t • (Pi.single i 1 : Vec d))).toContinuousLinearMap.hasFDerivAt
      |>.comp_hasDerivAt t hinner
  simp only [map_zero] at hout
  convert hout using 1
  funext s
  change koopman (mu := mu) (s • (Pi.single i 1 : Vec d)) Y =
    koopman (mu := mu) (t • (Pi.single i 1 : Vec d))
      (koopman (mu := mu) ((s - t) • (Pi.single i 1 : Vec d)) Y)
  rw [koopman_koopman]
  congr 2
  module

/-- A scalar stationary field with a literal zero strong horizontal gradient
is globally translation-invariant. -/
theorem isGloballyTranslationInvariant_of_hasHorizontalGradient_zero
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Y : ScalarL2 M.P.toMeasure)
    (hY : letI := potentialSequenceVAddInvariant M
      HasHorizontalGradient (mu := M.P.toMeasure) Y
        (0 : VectorL2 d M.P.toMeasure)) :
    IsGloballyTranslationInvariant M Y := by
  let := potentialSequenceVAddInvariant M
  apply isGloballyTranslationInvariant_of_hasDerivAt_zero M Y
  intro i t
  apply hasDerivAt_koopman_smul_single_zero_of_hasDerivAt_zero
    (mu := M.P.toMeasure) (d := d) Y i
  simpa only [map_zero] using! hY i

/-- Weak form of the preceding rigidity theorem.  It is enough that every
real Hilbert pairing of each coordinate orbit have derivative zero.  This is
the form produced by the curl-free/solenoidal calculation in the stationary
Hodge argument. -/
theorem isGloballyTranslationInvariant_of_inner_hasDerivAt_zero
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Y : ScalarL2 M.P.toMeasure)
    (hzero : letI := potentialSequenceVAddInvariant M
      ∀ (i : Fin d) (t : ℝ) (Z : ScalarL2 M.P.toMeasure),
        HasDerivAt
          (fun s : ℝ => inner ℝ
            (koopman (mu := M.P.toMeasure)
              (s • (Pi.single i 1 : Vec d)) Y) Z)
          0 t) :
    IsGloballyTranslationInvariant M Y := by
  let := potentialSequenceVAddInvariant M
  apply koopman_eq_of_koopman_smul_single_eq Y
  intro i t
  apply ext_inner_right ℝ
  intro Z
  let f : ℝ → ℝ := fun s => inner ℝ
    (koopman (mu := M.P.toMeasure)
      (s • (Pi.single i 1 : Vec d)) Y) Z
  have hf : Differentiable ℝ f := fun s => (hzero i s Z).differentiableAt
  have hfzero : ∀ s : ℝ, deriv f s = 0 := fun s => (hzero i s Z).deriv
  have hconst := is_const_of_deriv_eq_zero hf hfzero t 0
  simpa only [f, zero_smul, koopman_zero] using! hconst

end Stationary

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
