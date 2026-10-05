module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationaryProjectionTraceField
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section

/-!
# Invariant scalar fields and the stationary projection trace

This file develops the zero-mode half of the identity
`trace (P (X I)) = X`.  A globally translation-invariant scalar field pairs
to zero with every coordinate of a stationary potential field.  The literal
one-step multiplier also pairs to zero with every such invariant field by
finite-range decorrelation and the mean ergodic theorem.

The argument uses Koopman algebra.
-/

open Filter MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


namespace Stationary

variable {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
variable {mu : Measure Omega}
variable [AddAction (Vec d) Omega]
variable [MeasurableConstVAdd (Vec d) Omega]
variable [VAddInvariantMeasure (Vec d) Omega mu]

section KoopmanAlgebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Koopman translate is represented by translating an `L²`
representative. -/
theorem coeFn_koopman (x : Vec d) (F : Lp E 2 mu) :
    koopman (mu := mu) x F =ᵐ[mu] fun omega => F (x +ᵥ omega) :=
  Lp.coeFn_compMeasurePreserving (E := E) (p := 2) F
    (measurePreserving_const_vadd (mu := mu) x)

/-- Koopman operators compose according to the manuscript's right-translation
convention. -/
theorem koopman_koopman (x y : Vec d) (F : Lp E 2 mu) :
    koopman (mu := mu) x (koopman (mu := mu) y F) =
      koopman (mu := mu) (y + x) F := by
  refine Lp.ext ?_
  have hyPull : ∀ᵐ omega ∂mu,
      (koopman (mu := mu) y F) (x +ᵥ omega) = F (y +ᵥ (x +ᵥ omega)) :=
    (measurePreserving_const_vadd (mu := mu) x).quasiMeasurePreserving.ae
      (coeFn_koopman (mu := mu) y F)
  filter_upwards [coeFn_koopman (mu := mu) x (koopman (mu := mu) y F),
    hyPull, coeFn_koopman (mu := mu) (y + x) F] with omega h1 h2 h3
  rw [h1, h2, h3, vadd_vadd]

@[simp] theorem koopman_zero (F : Lp E 2 mu) :
    koopman (mu := mu) (0 : Vec d) F = F := by
  refine Lp.ext ?_
  filter_upwards [coeFn_koopman (mu := mu) (0 : Vec d) F] with omega h
  simpa only [zero_vadd] using! h

end KoopmanAlgebra

section KoopmanInner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem inner_map_map_real
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →ₗᵢ[ℝ] H) (u v : H) :
    inner ℝ (T u) (T v) = inner ℝ u v :=
  T.inner_map_map u v

/-- Move a Koopman translation across the real Hilbert inner product. -/
theorem inner_koopman_right (x : Vec d) (F G : Lp E 2 mu) :
    inner ℝ F (koopman (mu := mu) x G) =
      inner ℝ (koopman (mu := mu) (-x) F) G := by
  have hF : koopman (mu := mu) x (koopman (mu := mu) (-x) F) = F := by
    rw [koopman_koopman, neg_add_cancel, koopman_zero]
  calc
    inner ℝ F (koopman (mu := mu) x G) =
        inner ℝ (koopman (mu := mu) x (koopman (mu := mu) (-x) F))
          (koopman (mu := mu) x G) := by rw [hF]
    _ = inner ℝ (koopman (mu := mu) (-x) F) G :=
      inner_map_map_real (H := Lp E 2 mu)
        (koopman (mu := mu) (E := E) x)
        (koopman (mu := mu) (-x) F) G

/-- Move a Koopman translation from the left side of the real Hilbert inner
product to the right side. -/
theorem inner_koopman_left (x : Vec d) (F G : Lp E 2 mu) :
    inner ℝ (koopman (mu := mu) x F) G =
      inner ℝ F (koopman (mu := mu) (-x) G) := by
  rw [real_inner_comm, inner_koopman_right, real_inner_comm]

end KoopmanInner

section KoopmanSplitting

/-- Coordinate extraction commutes with stationary translation. -/
theorem koopman_vectorL2Coord (z : Vec d) (i : Fin d)
    (F : VectorL2 d mu) :
    koopman (mu := mu) z (vectorL2Coord (mu := mu) i F) =
      vectorL2Coord (mu := mu) i (koopman (mu := mu) z F) := by
  refine Lp.ext ?_
  have hpull : ∀ᵐ omega ∂mu,
      (vectorL2Coord (mu := mu) i F) (z +ᵥ omega) = (F (z +ᵥ omega)) i :=
    (measurePreserving_const_vadd (mu := mu) z).quasiMeasurePreserving.ae
      ((PiLp.proj (𝕜 := ℝ) (p := 2)
        (β := fun _ : Fin d => ℝ) i).coeFn_compLpL F)
  filter_upwards
    [coeFn_koopman (mu := mu) z (vectorL2Coord (mu := mu) i F), hpull,
      (PiLp.proj (𝕜 := ℝ) (p := 2)
        (β := fun _ : Fin d => ℝ) i).coeFn_compLpL
          (koopman (mu := mu) z F),
      coeFn_koopman (mu := mu) z F]
    with omega h1 h2 h3 h4
  rw [h1, h2]
  exact (h3.trans (by rw [h4]; rfl)).symm

/-- Koopman translation transports strong horizontal gradients. -/
theorem hasHorizontalGradient_koopman (z : Vec d)
    {phi : ScalarL2 mu} {F : VectorL2 d mu}
    (hF : HasHorizontalGradient (mu := mu) phi F) :
    HasHorizontalGradient (mu := mu)
      (koopman (mu := mu) z phi) (koopman (mu := mu) z F) := by
  intro i
  have hcomm : (fun t : ℝ => koopman (mu := mu)
      (t • (Pi.single i 1 : Vec d)) (koopman (mu := mu) z phi)) =
      fun t : ℝ => koopman (mu := mu) z
        (koopman (mu := mu) (t • (Pi.single i 1 : Vec d)) phi) := by
    funext t
    rw [koopman_koopman, koopman_koopman, add_comm]
  rw [hcomm, ← koopman_vectorL2Coord]
  exact (koopman (mu := mu) z).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
    0 (hF i)

/-- The stationary potential subspace is Koopman invariant. -/
theorem koopman_mem_stationaryPotentialSubspace (z : Vec d)
    {F : VectorL2 d mu}
    (hF : F ∈ stationaryPotentialSubspace (mu := mu) (d := d)) :
    koopman (mu := mu) z F ∈
      stationaryPotentialSubspace (mu := mu) (d := d) := by
  set T : Submodule ℝ (VectorL2 d mu) :=
    Submodule.comap (koopman (mu := mu) (E := HilbertVec d) z).toLinearMap
      (stationaryPotentialSubspace (mu := mu) (d := d)) with hT
  have hsub : horizontalGradientRange (mu := mu) (d := d) ≤ T := by
    rintro G ⟨psi, hpsi⟩
    exact Submodule.le_topologicalClosure
      (horizontalGradientRange (mu := mu) (d := d))
      ⟨koopman (mu := mu) z psi,
        hasHorizontalGradient_koopman z hpsi⟩
  have hcoe : (T : Set (VectorL2 d mu)) =
      (koopman (mu := mu) (E := HilbertVec d) z) ⁻¹'
        (stationaryPotentialSubspace (mu := mu) (d := d) :
          Set (VectorL2 d mu)) := rfl
  have hclosed : IsClosed (T : Set (VectorL2 d mu)) := by
    rw [hcoe]
    exact IsClosed.preimage
      (koopman (mu := mu) (E := HilbertVec d) z).continuous
      (Submodule.isClosed_topologicalClosure
        (horizontalGradientRange (mu := mu) (d := d)))
  exact Submodule.topologicalClosure_minimal
    (horizontalGradientRange (mu := mu) (d := d)) hsub hclosed hF

/-- The stationary solenoidal subspace is Koopman invariant. -/
theorem koopman_mem_stationarySolenoidalSubspace (z : Vec d)
    {F : VectorL2 d mu}
    (hF : F ∈ stationarySolenoidalSubspace (mu := mu) (d := d)) :
    koopman (mu := mu) z F ∈
      stationarySolenoidalSubspace (mu := mu) (d := d) := by
  refine (Submodule.mem_orthogonal _ _).2 fun u hu => ?_
  have hu' : koopman (mu := mu) (-z) u ∈
      stationaryPotentialSubspace (mu := mu) (d := d) :=
    koopman_mem_stationaryPotentialSubspace (-z) hu
  have hzero : inner ℝ (koopman (mu := mu) (-z) u) F = 0 :=
    (Submodule.mem_orthogonal _ _).1 hF _ hu'
  rwa [inner_koopman_left, neg_neg] at hzero

/-- Orthogonal stationary-potential projection commutes with every Koopman
translation. -/
theorem koopman_stationaryPotentialProjection (z : Vec d)
    (F : VectorL2 d mu) :
    koopman (mu := mu) z (stationaryPotentialProjection (mu := mu) F) =
      stationaryPotentialProjection (mu := mu) (koopman (mu := mu) z F) := by
  apply eq_stationaryPotentialProjection_of_mem_of_sub_mem_orthogonal
  · exact koopman_mem_stationaryPotentialSubspace z
      (stationaryPotentialProjection_mem F)
  · rw [← map_sub]
    exact koopman_mem_stationarySolenoidalSubspace z
      (sub_stationaryPotentialProjection_mem_orthogonal F)

end KoopmanSplitting

/-- Identity-continuity of one Koopman orbit propagates to every base point
by the representation law and isometry. -/
theorem continuous_koopmanOrbit_of_continuousAt_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Lp E 2 mu)
    (hzero : ContinuousAt (fun z : Vec d => koopman (mu := mu) z X) 0) :
    Continuous (fun z : Vec d => koopman (mu := mu) z X) := by
  apply continuous_iff_continuousAt.mpr
  intro z₀
  have hshift : ContinuousAt (fun z : Vec d => z - z₀) z₀ :=
    continuousAt_id.sub continuousAt_const
  have hinner : ContinuousAt
      (fun z : Vec d => koopman (mu := mu) (z - z₀) X) z₀ :=
    hzero.comp_of_eq hshift (sub_self z₀)
  have hcomp : ContinuousAt
      (fun z : Vec d => koopman (mu := mu) z₀
        (koopman (mu := mu) (z - z₀) X)) z₀ :=
    (koopman (mu := mu) z₀).continuous.continuousAt.comp hinner
  convert hcomp using 1
  funext z
  rw [koopman_koopman]
  congr 2
  abel

end Stationary

/-- A scalar stationary `L²` field fixed by every spatial translation. -/
def IsGloballyTranslationInvariant {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Y : Stationary.ScalarL2 M.P.toMeasure) : Prop :=
  letI := potentialSequenceVAddInvariant M
  ∀ z : Vec d, Stationary.koopman (mu := M.P.toMeasure) z Y = Y

private theorem inner_vectorL2Coord_eq_zero_of_hasHorizontalGradient_of_invariant
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {phi : Stationary.ScalarL2 M.P.toMeasure}
    {F : Stationary.VectorL2 d M.P.toMeasure}
    (hF : letI := potentialSequenceVAddInvariant M
      Stationary.HasHorizontalGradient (mu := M.P.toMeasure) phi F)
    {Y : Stationary.ScalarL2 M.P.toMeasure}
    (hY : IsGloballyTranslationInvariant M Y) (i : Fin d) :
    inner ℝ
      (Stationary.vectorL2Coord (mu := M.P.toMeasure) i F) Y = 0 := by
  let := potentialSequenceVAddInvariant M
  have hpairConst : (fun t : ℝ => inner ℝ Y
      (Stationary.koopman (mu := M.P.toMeasure)
        (t • (Pi.single i 1 : Vec d)) phi)) = fun _ => inner ℝ Y phi := by
    funext t
    rw [Stationary.inner_koopman_right]
    rw [hY (-(t • (Pi.single i 1 : Vec d)))]
  have hderiv : HasDerivAt (fun t : ℝ => inner ℝ Y
      (Stationary.koopman (mu := M.P.toMeasure)
        (t • (Pi.single i 1 : Vec d)) phi))
      (inner ℝ Y
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) i F)) 0 := by
    exact (innerSL ℝ Y).hasFDerivAt.comp_hasDerivAt 0 (hF i)
  rw [hpairConst] at hderiv
  have hzero : inner ℝ Y
      (Stationary.vectorL2Coord (mu := M.P.toMeasure) i F) = 0 :=
    hderiv.unique (hasDerivAt_const (x := (0 : ℝ)) (c := inner ℝ Y phi))
  simpa only [real_inner_comm] using! hzero

/-- Every coordinate of a stationary potential field is orthogonal to every
globally translation-invariant scalar field. -/
theorem inner_vectorL2Coord_eq_zero_of_mem_stationaryPotential_of_invariant
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {F : Stationary.VectorL2 d M.P.toMeasure}
    (hF : letI := potentialSequenceVAddInvariant M
      F ∈ Stationary.stationaryPotentialSubspace
        (mu := M.P.toMeasure) (d := d))
    {Y : Stationary.ScalarL2 M.P.toMeasure}
    (hY : IsGloballyTranslationInvariant M Y) (i : Fin d) :
    inner ℝ
      (Stationary.vectorL2Coord (mu := M.P.toMeasure) i F) Y = 0 := by
  let := potentialSequenceVAddInvariant M
  let L : Stationary.VectorL2 d M.P.toMeasure →L[ℝ] ℝ :=
    (innerSL ℝ Y).comp
      (Stationary.vectorL2Coord (mu := M.P.toMeasure) i)
  have hsub : Stationary.horizontalGradientRange
      (mu := M.P.toMeasure) (d := d) ≤ LinearMap.ker L.toLinearMap := by
    rintro G ⟨phi, hphi⟩
    change inner ℝ Y
      (Stationary.vectorL2Coord (mu := M.P.toMeasure) i G) = 0
    rw [real_inner_comm]
    exact
      inner_vectorL2Coord_eq_zero_of_hasHorizontalGradient_of_invariant
        M hphi hY i
  have hclosed : IsClosed (LinearMap.ker L.toLinearMap :
      Set (Stationary.VectorL2 d M.P.toMeasure)) :=
    ContinuousLinearMap.isClosed_ker L
  have hmem : F ∈ LinearMap.ker L.toLinearMap :=
    Submodule.topologicalClosure_minimal
      (Stationary.horizontalGradientRange (mu := M.P.toMeasure) (d := d))
      hsub hclosed hF
  change inner ℝ Y
    (Stationary.vectorL2Coord (mu := M.P.toMeasure) i F) = 0 at hmem
  simpa only [real_inner_comm] using! hmem

/-- The coordinate trace of the projected matrix field is orthogonal to every
globally invariant scalar field. -/
theorem inner_oneStepPotentialTraceL2_eq_zero_of_invariant
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (hh : 0 < h) {Y : Stationary.ScalarL2 M.P.toMeasure}
    (hY : IsGloballyTranslationInvariant M Y) :
    inner ℝ (oneStepPotentialTraceL2 M n h hh) Y = 0 := by
  unfold oneStepPotentialTraceL2
  rw [sum_inner]
  apply Finset.sum_eq_zero
  intro i _
  exact inner_vectorL2Coord_eq_zero_of_mem_stationaryPotential_of_invariant
    M (oneStepPotentialProjection_mem_stationaryPotentialSubspace
      M n h (Pi.single i 1) hh) hY i

/-- Finite-range decorrelation makes the one-step multiplier orthogonal to
every globally translation-invariant scalar field. -/
theorem inner_oneStepMultiplierAtL2_eq_zero_of_invariant
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (hh : 0 < h) {Y : Stationary.ScalarL2 M.P.toMeasure}
    (hY : IsGloballyTranslationInvariant M Y) :
    inner ℝ (oneStepMultiplierAtL2 M n h 0 hh) Y = 0 := by
  let := potentialSequenceVAddInvariant M
  let rho : ℝ := Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n + h)
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  let i : Fin d := ⟨0, hd⟩
  let z : Vec d := (rho + 1) • Pi.single i 1
  have hrho0 : 0 ≤ rho := by
    dsimp only [rho]
    positivity
  have hz : rho < ‖z‖ := by
    dsimp only [z]
    rw [norm_smul, Pi.norm_single]
    simp only [norm_one, mul_one, Real.norm_eq_abs]
    rw [abs_of_pos (by linarith)]
    linarith
  let K := LinearMap.eqLocus
    (Stationary.koopman (mu := M.P.toMeasure) (E := ℝ) z).toContinuousLinearMap.toLinearMap (ContinuousLinearMap.id ℝ (Lp ℝ 2 M.P.toMeasure)).toLinearMap
  have hproj :=
    orthogonalProjection_eqLocus_koopman_oneStepMultiplierAtL2_eq_zero
      M n h hh hz
  change K.orthogonalProjectionOnto
      (oneStepMultiplierAtL2 M n h 0 hh) = 0 at hproj
  have hstar : K.starProjection
      (oneStepMultiplierAtL2 M n h 0 hh) = 0 := by
    change ((K.orthogonalProjectionOnto
      (oneStepMultiplierAtL2 M n h 0 hh) : K) :
        Stationary.ScalarL2 M.P.toMeasure) = 0
    exact congrArg Subtype.val hproj
  have hYmem : Y ∈ K := by
    change (Stationary.koopman
      (mu := M.P.toMeasure) (E := ℝ) z).toContinuousLinearMap Y = Y
    exact hY z
  have horth := K.starProjection_inner_eq_zero
    (oneStepMultiplierAtL2 M n h 0 hh) Y hYmem
  rw [hstar, sub_zero] at horth
  exact horth

/-- If the coordinate-trace defect is globally invariant, it vanishes.  This
is the no-zero-mode closure of the weak stationary Hodge identity. -/
theorem oneStepPotentialTraceL2_eq_multiplier_of_invariant_defect
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (hh : 0 < h)
    (hinv : IsGloballyTranslationInvariant M
      (oneStepMultiplierAtL2 M n h 0 hh -
        oneStepPotentialTraceL2 M n h hh)) :
    oneStepPotentialTraceL2 M n h hh =
      oneStepMultiplierAtL2 M n h 0 hh := by
  let Y := oneStepMultiplierAtL2 M n h 0 hh -
    oneStepPotentialTraceL2 M n h hh
  have hYX : inner ℝ (oneStepMultiplierAtL2 M n h 0 hh) Y = 0 :=
    inner_oneStepMultiplierAtL2_eq_zero_of_invariant M n h hh hinv
  have hTY : inner ℝ (oneStepPotentialTraceL2 M n h hh) Y = 0 :=
    inner_oneStepPotentialTraceL2_eq_zero_of_invariant M n h hh hinv
  have hYY : inner ℝ Y Y = 0 := by
    dsimp only [Y]
    rw [inner_sub_left]
    simpa only [real_inner_comm] using! sub_eq_zero.mpr (hYX.trans hTY.symm)
  have hYzero : Y = 0 := by
    rw [real_inner_self_eq_norm_sq] at hYY
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hYY)
  exact sub_eq_zero.mp hYzero |>.symm

/-- The weak-Hodge invariance of the trace defect implies the exact one-step
stationary Helmholtz trace. -/
theorem oneStep_stationaryHelmholtz_trace_of_invariant_defect
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (hh : 0 < h)
    (hinv : IsGloballyTranslationInvariant M
      (oneStepMultiplierAtL2 M n h 0 hh -
        oneStepPotentialTraceL2 M n h hh)) :
    ∑ i : Fin d,
        ‖oneStepPotentialProjection M n h (Pi.single i 1) hh‖ ^ 2 =
      (oneShellCenteredExpTwoMoment M) ^ h - 1 := by
  apply oneStep_stationaryHelmholtz_trace_of_traceField_eq M n h hh
  exact oneStepPotentialTraceL2_eq_multiplier_of_invariant_defect
    M n h hh hinv

/-- Exact projected energy for every deterministic probe, conditional only on
the weak-Hodge invariance of the scalar trace defect. -/
theorem oneStepProjectedEnergy_eq_suffixVariance_div_dimension_of_invariant_defect
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h)
    (hinv : IsGloballyTranslationInvariant M
      (oneStepMultiplierAtL2 M n h 0 hh -
        oneStepPotentialTraceL2 M n h hh)) :
    oneStepProjectedEnergy M n h p hh =
      (((oneShellCenteredExpTwoMoment M) ^ h - 1) / (d : ℝ)) *
        vecNormSq p := by
  apply oneStepProjectedEnergy_eq_suffixVariance_div_dimension_of_trace
  exact oneStep_stationaryHelmholtz_trace_of_invariant_defect M n h hh hinv

/-- Unit-probe specialization used by both one-step variational lanes. -/
theorem oneStepProjectedEnergy_eq_suffixVariance_div_dimension_unit_of_invariant_defect
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h) (hp : vecNormSq p = 1)
    (hinv : IsGloballyTranslationInvariant M
      (oneStepMultiplierAtL2 M n h 0 hh -
        oneStepPotentialTraceL2 M n h hh)) :
    oneStepProjectedEnergy M n h p hh =
      ((oneShellCenteredExpTwoMoment M) ^ h - 1) / (d : ℝ) := by
  rw [oneStepProjectedEnergy_eq_suffixVariance_div_dimension_of_invariant_defect
    M n h p hh hinv, hp, mul_one]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
