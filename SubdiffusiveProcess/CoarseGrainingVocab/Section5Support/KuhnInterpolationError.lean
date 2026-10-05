module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn.CellEnvelope
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SimplexEulerRigidity

@[expose] public section

/-!
# The `C^1` interpolation estimate on a Kuhn cell

Step 2 of the strict-decay proposition (paper label `p.homogenized.coefficient.strict.decay`) asserts
that *conforming piecewise-affine functions are dense in `H_0^1(spx_0^pi)`*.
The analytic core of that assertion is the classical interpolation estimate: on
a cell `T` of the mesh, the constant gradient of the affine interpolant of a
`C^1` function differs from the true gradient by at most the modulus of
continuity of `nabla u` at the mesh scale.

This file proves that estimate.  `Kuhn/Interpolation.lean` already supplies the
combinatorial half (`vecNormSq_kuhnSlope_sub_le_of_vertex_oscillation`: the
gradient error is controlled by the vertex oscillation of `u - linear_p` over
the cube side); what is added here is the *analytic* half, namely that for a
`C^1` function and `p = nabla u(x)` with `x` in the cell, that oscillation is at
most `eta * 3^{scale}`, where `eta` bounds the oscillation of `nabla u` on the
cell.

* `fderiv_eq_linearFnCLM_gradVec` -- the Fréchet derivative is the linear form of
  the coordinate gradient, which is what lets the source's `linear_p` serve as
  the first-order Taylor polynomial;
* `abs_vertex_oscillation_le` -- the mean-value step on the convex closed cell;
* `vecNormSq_kuhnSlope_sub_gradVec_le` -- the cellwise estimate
  `|nabla v|_T - nabla u(x)|^2 <= d * eta^2`;
* `exists_scale_forall_vecNormSq_kuhnSlope_sub_gradVec_le` -- its uniform form:
  for a `C^1` function and a compact set `K`, every cell of small enough scale
  inside `K` has gradient error at most `eps`.  This is the statement the
  density argument of (S2a) consumes, `eta` being supplied by the uniform
  continuity of `nabla u` on `K`.

Scope.  Nothing here is probabilistic, and nothing refers to a mesh: every
statement is about a single Kuhn cell.  The assembly into an `L^2` estimate over
a mesh, and the `H_0^1` membership of the assembled competitor, are the
remaining halves of (S2a) and are not proved here.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization Kuhn Metric Set

noncomputable section

variable {d : ℕ}

/-! ## The derivative as the linear form of the coordinate gradient -/

/-- The Fréchet derivative of `u` at `x` is the source's `linear_{nabla u(x)}`.
This identifies the first-order Taylor polynomial of `u` at `x` with an
admissible affine datum for `Kuhn/Interpolation.lean`. -/
theorem fderiv_eq_linearFnCLM_gradVec (u : Vec d → ℝ) (x : Vec d) :
    fderiv ℝ u x = linearFnCLM (gradVec u x) := by
  ext p
  rw [linearFnCLM_apply, vecDot_comm, vecDot_gradVec_eq_fderiv]

/-! ## The mean-value step -/

/-- **The vertex oscillation of `u - linear_p` on one cell.**  If the derivative
of `u` varies by at most `eta` on the closed cell and `p = nabla u(x)` for a
point `x` of that cell, then `u - linear_p` oscillates by at most
`eta * 3^{scale}` over the cell's `d + 1` corners.  The argument is the
mean-value inequality on the convex closed cell, whose diameter is the cube
side. -/
theorem abs_vertex_oscillation_le {u : Vec d → ℝ} (hu : Differentiable ℝ u)
    (T : KuhnCell d) {x : Vec d} (hx : x ∈ T.closedCarrier) {eta : ℝ}
    (hbound : ∀ y ∈ T.closedCarrier, ‖fderiv ℝ u y - fderiv ℝ u x‖ ≤ eta)
    (k l : Fin (d + 1)) :
    |(u (T.vertex k) - linearFn (gradVec u x) (T.vertex k)) -
        (u (T.vertex l) - linearFn (gradVec u x) (T.vertex l))| ≤
      eta * cubeScaleFactor T.supportCube := by
  have heta : 0 ≤ eta := by simpa using hbound x hx
  set p : Vec d := gradVec u x with hp
  set w : Vec d → ℝ := fun y => u y - linearFn p y with hw
  have hwderiv : ∀ y : Vec d,
      HasFDerivWithinAt w (fderiv ℝ u y - fderiv ℝ u x) T.closedCarrier y := by
    intro y
    have h1 : HasFDerivAt u (fderiv ℝ u y) y := (hu y).hasFDerivAt
    have h2 : HasFDerivAt (linearFn p) (linearFnCLM p) y := hasFDerivAt_linearFn p y
    have h3 : HasFDerivAt w (fderiv ℝ u y - linearFnCLM p) y := h1.sub h2
    rw [hp, ← fderiv_eq_linearFnCLM_gradVec] at h3
    exact h3.hasFDerivWithinAt
  have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := w) (C := eta) (s := T.closedCarrier)
    (fun y _ => hwderiv y) (fun y hy => hbound y hy) (convex_closedCarrier T)
    (T.vertex_mem_closedCarrier l) (T.vertex_mem_closedCarrier k)
  have hdiam : ‖T.vertex k - T.vertex l‖ ≤ cubeScaleFactor T.supportCube := by
    rw [← dist_eq_norm]
    exact dist_le_cubeScaleFactor_of_mem_closedCarrier T
      (T.vertex_mem_closedCarrier k) (T.vertex_mem_closedCarrier l)
  calc
    |(u (T.vertex k) - linearFn (gradVec u x) (T.vertex k)) -
        (u (T.vertex l) - linearFn (gradVec u x) (T.vertex l))|
        = ‖w (T.vertex k) - w (T.vertex l)‖ := by
          rw [Real.norm_eq_abs, hw]
    _ ≤ eta * ‖T.vertex k - T.vertex l‖ := hmv
    _ ≤ eta * cubeScaleFactor T.supportCube := by
          exact mul_le_mul_of_nonneg_left hdiam heta

/-! ## The cellwise gradient estimate -/

/-- **The interpolation estimate on one cell.**  If `nabla u` varies by at most
`eta` on the closed cell, then the constant gradient `nabla v|_T` of the affine
interpolant differs from `nabla u(x)` by at most `sqrt d * eta` in Euclidean
length.  The cube side cancels: the vertex oscillation scales like the side, and
the Kuhn difference quotients divide by it. -/
theorem vecNormSq_kuhnSlope_sub_gradVec_le {u : Vec d → ℝ} (hu : Differentiable ℝ u)
    (T : KuhnCell d) {x : Vec d} (hx : x ∈ T.closedCarrier) {eta : ℝ}
    (hbound : ∀ y ∈ T.closedCarrier, ‖fderiv ℝ u y - fderiv ℝ u x‖ ≤ eta) :
    vecNormSq (kuhnSlope T u - gradVec u x) ≤ (d : ℝ) * eta ^ 2 := by
  have hs : (0 : ℝ) < cubeScaleFactor T.supportCube := zpow_pos (by norm_num) _
  have h := vecNormSq_kuhnSlope_sub_le_of_vertex_oscillation T u (gradVec u x)
    (B := eta * cubeScaleFactor T.supportCube)
    (fun k l => abs_vertex_oscillation_le hu T hx hbound k l)
  have hcancel :
      eta * cubeScaleFactor T.supportCube / cubeScaleFactor T.supportCube = eta := by
    field_simp
  rwa [hcancel] at h

/-! ## The uniform form -/

/-- **(S2a), analytic core.**  For a `C^1` function `u` and a compact set `K`
there is a scale `s₀` below which *every* Kuhn cell inside `K` has its
interpolant gradient within `eps` of `nabla u` at every point of the cell.

This is exactly the input the density argument needs: applied to the smooth
compactly supported approximations that the `H_0^1` package carries, it makes
the piecewise-affine interpolant converge in `H^1`.  The proof combines
`vecNormSq_kuhnSlope_sub_gradVec_le` with the uniform continuity of `nabla u` on
`K` and the mesh diameter `3^{scale}`. -/
theorem exists_scale_forall_vecNormSq_kuhnSlope_sub_gradVec_le {u : Vec d → ℝ}
    (hu : ContDiff ℝ 1 u) {K : Set (Vec d)} (hK : IsCompact K) {eps : ℝ}
    (heps : 0 < eps) :
    ∃ s₀ : ℤ, ∀ T : KuhnCell d, T.supportCube.scale ≤ s₀ → T.closedCarrier ⊆ K →
      ∀ x ∈ T.closedCarrier, vecNormSq (kuhnSlope T u - gradVec u x) ≤ eps := by
  have hcont : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  set eta : ℝ := Real.sqrt (eps / ((d : ℝ) + 1)) with heta_def
  have hetapos : 0 < eta := Real.sqrt_pos.mpr (by positivity)
  have hetasq : eta ^ 2 = eps / ((d : ℝ) + 1) := Real.sq_sqrt (by positivity)
  obtain ⟨delta, hdelta, hunif⟩ :=
    uniformContinuousOn_iff.mp
      (hK.uniformContinuousOn_of_continuous hcont.continuousOn) eta hetapos
  obtain ⟨s₀, hs₀⟩ := Kuhn.exists_zpow_three_lt hdelta
  refine ⟨s₀, fun T hscale hsub x hx => ?_⟩
  have hside : cubeScaleFactor T.supportCube ≤ (3 : ℝ) ^ s₀ := by
    rw [cubeScaleFactor]
    exact zpow_le_zpow_right₀ (by norm_num) hscale
  have hbound : ∀ y ∈ T.closedCarrier, ‖fderiv ℝ u y - fderiv ℝ u x‖ ≤ eta := by
    intro y hy
    have hdist : dist y x < delta :=
      lt_of_le_of_lt
        ((dist_le_cubeScaleFactor_of_mem_closedCarrier T hy hx).trans hside) hs₀
    have hlt := hunif y (hsub hy) x (hsub hx) hdist
    rw [dist_eq_norm] at hlt
    exact hlt.le
  refine (vecNormSq_kuhnSlope_sub_gradVec_le (hu.differentiable one_ne_zero) T hx hbound).trans ?_
  rw [hetasq, mul_div_assoc', div_le_iff₀ hd1]
  nlinarith [heps.le]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
