module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepZeroMode
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationaryProjectionTrace

@[expose] public section

/-!
# Coordinate trace of the stationary one-step projection

This file rewrites the trace-one part of the stationary Helmholtz calculation
at  as a scalar `L²` field identity.  Orthogonality
of the potential projection gives

`sum_i ‖P(X e_i)‖² = inner (sum_i (P(X e_i))_i) X`.

Consequently the manuscript's energy trace follows once the coordinate trace
of the projected matrix field is identified with `X`.  This separates the
Hilbert projection algebra from that final stationary differential identity.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


/-- The scalar coordinate trace of the matrix whose `i`th column is the
stationary potential projection of `X e_i`. -/
def oneStepPotentialTraceL2 {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (hh : 0 < h) :
    Stationary.ScalarL2 M.P.toMeasure :=
  ∑ i : Fin d,
    Stationary.vectorL2Coord (mu := M.P.toMeasure) i
      (oneStepPotentialProjection M n h (Pi.single i 1) hh)

theorem inner_vectorL2_oneStepOriginForcing_basis_eq_coord_inner
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (F : Stationary.VectorL2 d M.P.toMeasure) (i : Fin d) (hh : 0 < h) :
    inner ℝ F (oneStepOriginForcingL2 M n h (Pi.single i 1) hh) =
      inner ℝ
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) i F)
        (oneStepMultiplierAtL2 M n h 0 hh) := by
  rw [L2.inner_def, L2.inner_def]
  have hcoord :
      (Stationary.vectorL2Coord (mu := M.P.toMeasure) i F : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ)
        =ᵐ[M.P.toMeasure] fun omega => F omega i :=
    (PiLp.proj (𝕜 := ℝ) (p := 2)
      (β := fun _ : Fin d => ℝ) i).coeFn_compLpL F
  have hforcing := MemLp.coeFn_toLp
    (memLp_two_oneStepOriginForcing M n h (Pi.single i 1) hh)
  have hmultiplier := MemLp.coeFn_toLp
    (memLp_two_oneStepMultiplierAt M n h 0 hh)
  apply integral_congr_ae
  filter_upwards [hcoord, hforcing, hmultiplier] with omega hc hf hx
  have hf' :
      (oneStepOriginForcingL2 M n h (Pi.single i 1) hh :
          _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d) omega =
        oneStepOriginForcing M n h (Pi.single i 1) omega := by
    simpa only [oneStepOriginForcingL2] using hf
  have hx' :
      (oneStepMultiplierAtL2 M n h 0 hh : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ) omega =
        oneStepOriginMultiplier M n h omega := by
    simpa only [oneStepMultiplierAtL2, oneStepMultiplierAt,
      oneStepOriginMultiplier] using hx
  rw [hf', hc, hx']
  change inner ℝ (F omega)
      (oneStepOriginMultiplier M n h omega •
        HilbertVec.ofVec (Pi.single i 1)) =
    inner ℝ (F omega i) (oneStepOriginMultiplier M n h omega)
  rw [HilbertVec.inner_def]
  simp only [HilbertVec.toVec, HilbertVec.ofVec, vecDot, PiLp.smul_apply,
    RCLike.inner_apply, conj_trivial]
  rw [Finset.sum_eq_single i]
  · simp [mul_comm]
  · intro j _ hji
    simp [hji]
  · simp

/-- Each coordinate projected energy pairs the scalar multiplier with the
matching coordinate of the projected vector field. -/
theorem norm_sq_oneStepPotentialProjection_basis_eq_coord_inner
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (i : Fin d) (hh : 0 < h) :
    ‖oneStepPotentialProjection M n h (Pi.single i 1) hh‖ ^ 2 =
      inner ℝ
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) i
          (oneStepPotentialProjection M n h (Pi.single i 1) hh))
        (oneStepMultiplierAtL2 M n h 0 hh) := by
  let q := oneStepPotentialProjection M n h (Pi.single i 1) hh
  let f := oneStepOriginForcingL2 M n h (Pi.single i 1) hh
  have horth :=
    inner_oneStepPotentialProjection_solenoidalRemainder_eq_zero
      M n h (Pi.single i 1) hh
  have hqf : inner ℝ q f = ‖q‖ ^ 2 := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq] at horth
    dsimp only [q, f] at horth ⊢
    linarith
  rw [← hqf]
  exact inner_vectorL2_oneStepOriginForcing_basis_eq_coord_inner
    M n h q i hh

/-- The finite trace of the projected coordinate energies is the pairing of
the scalar multiplier with the coordinate trace field. -/
theorem sum_norm_sq_oneStepPotentialProjection_basis_eq_trace_inner
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (hh : 0 < h) :
    ∑ i : Fin d,
        ‖oneStepPotentialProjection M n h (Pi.single i 1) hh‖ ^ 2 =
      inner ℝ (oneStepPotentialTraceL2 M n h hh)
        (oneStepMultiplierAtL2 M n h 0 hh) := by
  unfold oneStepPotentialTraceL2
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  exact norm_sq_oneStepPotentialProjection_basis_eq_coord_inner M n h i hh

/-- The concrete trace-field equation implies the manuscript's scalar
stationary Helmholtz trace identity. -/
theorem oneStep_stationaryHelmholtz_trace_of_traceField_eq
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (hh : 0 < h)
    (htraceField : oneStepPotentialTraceL2 M n h hh =
      oneStepMultiplierAtL2 M n h 0 hh) :
    ∑ i : Fin d,
        ‖oneStepPotentialProjection M n h (Pi.single i 1) hh‖ ^ 2 =
      (oneShellCenteredExpTwoMoment M) ^ h - 1 := by
  rw [sum_norm_sq_oneStepPotentialProjection_basis_eq_trace_inner,
    htraceField, real_inner_self_eq_norm_sq,
    norm_sq_oneStepMultiplierAtL2 M n h 0 hh]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
