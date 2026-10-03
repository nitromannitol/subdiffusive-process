module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationaryInvariantTrace

@[expose] public section

/-!
# Strong translation orbit of the one-step projected trace

The scalar one-step multiplier already has a strongly continuous translation
orbit.  This file transports that fact through the fixed-vector embedding,
the stationary Helmholtz projection, coordinate extraction, and the finite
trace.  It supplies the continuity half needed to turn the weak Hodge identity
for the trace defect into literal translation invariance.
-/

open Filter MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


/-- Embed a scalar stationary `L²` field as a vector field in one fixed
deterministic direction. -/
def scalarToVectorL2 {d : ℕ} (mu : Measure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) (p : Vec d) :
    Stationary.ScalarL2 mu →L[ℝ] Stationary.VectorL2 d mu :=
  (ContinuousLinearMap.toSpanSingleton ℝ (HilbertVec.ofVec p)).compLpL 2 mu

theorem coeFn_scalarToVectorL2 {d : ℕ}
    (mu : Measure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) (p : Vec d)
    (X : Stationary.ScalarL2 mu) :
    (scalarToVectorL2 mu p X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → HilbertVec d) =ᵐ[mu]
      fun omega => X omega • HilbertVec.ofVec p := by
  simpa only [scalarToVectorL2, ContinuousLinearMap.toSpanSingleton_apply]
    using (ContinuousLinearMap.toSpanSingleton ℝ
      (HilbertVec.ofVec p)).coeFn_compLpL X

/-- Coordinate extraction from the fixed-vector scalar embedding. -/
theorem vectorL2Coord_scalarToVectorL2 {d : ℕ}
    (mu : Measure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)) (p : Vec d)
    (X : Stationary.ScalarL2 mu) (i : Fin d) :
    Stationary.vectorL2Coord (mu := mu) i
        (scalarToVectorL2 mu p X) =
      p i • X := by
  apply Lp.ext
  filter_upwards
    [(PiLp.proj (𝕜 := ℝ) (p := 2)
      (β := fun _ : Fin d => ℝ) i).coeFn_compLpL
        (scalarToVectorL2 mu p X),
      coeFn_scalarToVectorL2 mu p X,
      Lp.coeFn_smul (p i) X]
    with omega hcoord hembed hsmul
  have hcoord' :
      (Stationary.vectorL2Coord (mu := mu) i
        (scalarToVectorL2 mu p X) : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ) omega =
        (scalarToVectorL2 mu p X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → HilbertVec d) omega i := by
    simpa only [Stationary.vectorL2Coord] using! hcoord
  rw [hcoord', hembed, hsmul]
  simp only [PiLp.smul_apply, HilbertVec.ofVec, smul_eq_mul, mul_comm]
  rfl

/-- The literal origin forcing is the fixed-vector embedding of the scalar
one-step multiplier. -/
theorem oneStepOriginForcingL2_eq_scalarToVectorL2 {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h) :
    oneStepOriginForcingL2 M n h p hh =
      scalarToVectorL2 M.P.toMeasure p
        (oneStepMultiplierAtL2 M n h 0 hh) := by
  apply Lp.ext
  filter_upwards
    [MemLp.coeFn_toLp (memLp_two_oneStepOriginForcing M n h p hh),
      coeFn_scalarToVectorL2 M.P.toMeasure p
        (oneStepMultiplierAtL2 M n h 0 hh),
      MemLp.coeFn_toLp (memLp_two_oneStepMultiplierAt M n h 0 hh)]
    with omega hf hl hx
  have hf' :
      (oneStepOriginForcingL2 M n h p hh : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → HilbertVec d) omega =
        oneStepOriginForcing M n h p omega := by
    simpa only [oneStepOriginForcingL2] using hf
  have hx' :
      (oneStepMultiplierAtL2 M n h 0 hh : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ) omega =
        oneStepMultiplierAt M n h 0 omega := by
    simpa only [oneStepMultiplierAtL2] using hx
  rw [hf', hl, hx']
  rfl

/-- Coordinate form of a basis one-step forcing column. -/
theorem vectorL2Coord_oneStepOriginForcingL2_basis {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (i j : Fin d) (hh : 0 < h) :
    Stationary.vectorL2Coord (mu := M.P.toMeasure) i
        (oneStepOriginForcingL2 M n h (Pi.single j 1) hh) =
      (Pi.single j 1 : Vec d) i •
        oneStepMultiplierAtL2 M n h 0 hh := by
  rw [oneStepOriginForcingL2_eq_scalarToVectorL2,
    vectorL2Coord_scalarToVectorL2]

/-- Fixed-vector scalar embedding commutes with stationary translation. -/
theorem koopman_scalarToVectorL2 {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (z : Vec d) (p : Vec d)
    (X : Stationary.ScalarL2 M.P.toMeasure) :
    letI := potentialSequenceVAddInvariant M
    Stationary.koopman (mu := M.P.toMeasure) z
        (scalarToVectorL2 M.P.toMeasure p X) =
      scalarToVectorL2 M.P.toMeasure p
        (Stationary.koopman (mu := M.P.toMeasure) z X) := by
  letI := potentialSequenceVAddInvariant M
  apply Lp.ext
  have hleftPull : ∀ᵐ omega ∂M.P.toMeasure,
      (scalarToVectorL2 M.P.toMeasure p X) (z +ᵥ omega) =
        X (z +ᵥ omega) • HilbertVec.ofVec p :=
    (Stationary.measurePreserving_const_vadd
      (mu := M.P.toMeasure) z).quasiMeasurePreserving.ae
        (coeFn_scalarToVectorL2 M.P.toMeasure p X)
  filter_upwards
    [Stationary.coeFn_koopman (mu := M.P.toMeasure) z
      (scalarToVectorL2 M.P.toMeasure p X), hleftPull,
      coeFn_scalarToVectorL2 M.P.toMeasure p
        (Stationary.koopman (mu := M.P.toMeasure) z X),
      Stationary.coeFn_koopman (mu := M.P.toMeasure) z X]
    with omega hleft hpull hright hx
  rw [hleft, hpull, hright, hx]

/-- The translated literal forcing is the embedded translated scalar
multiplier. -/
theorem koopman_oneStepOriginForcingL2 {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (z p : Vec d) (hh : 0 < h) :
    letI := potentialSequenceVAddInvariant M
    Stationary.koopman (mu := M.P.toMeasure) z
        (oneStepOriginForcingL2 M n h p hh) =
      scalarToVectorL2 M.P.toMeasure p
        (oneStepMultiplierAtL2 M n h z hh) := by
  letI := potentialSequenceVAddInvariant M
  rw [oneStepOriginForcingL2_eq_scalarToVectorL2,
    koopman_scalarToVectorL2, koopman_oneStepMultiplierAtL2_zero]

/-- The translation orbit of the literal one-step forcing is continuous at
the origin. -/
theorem continuousAt_koopman_oneStepOriginForcingL2_zero {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h) :
    letI := potentialSequenceVAddInvariant M
    ContinuousAt (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z
        (oneStepOriginForcingL2 M n h p hh)) 0 := by
  letI := potentialSequenceVAddInvariant M
  have hscalar := continuousAt_koopman_oneStepMultiplierAtL2_zero M n h hh
  have hlift := (scalarToVectorL2 M.P.toMeasure p).continuous.continuousAt.comp
    hscalar
  convert hlift using 1
  funext z
  simpa only [Function.comp_apply, oneStepOriginForcingL2_eq_scalarToVectorL2] using!
    koopman_scalarToVectorL2 M z p (oneStepMultiplierAtL2 M n h 0 hh)

/-- The translation orbit of the stationary potential projection is
continuous at the origin. -/
theorem continuousAt_koopman_oneStepPotentialProjection_zero {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h) :
    letI := potentialSequenceVAddInvariant M
    ContinuousAt (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z
        (oneStepPotentialProjection M n h p hh)) 0 := by
  letI := potentialSequenceVAddInvariant M
  have hforcing :=
    continuousAt_koopman_oneStepOriginForcingL2_zero M n h p hh
  have hprojected :=
    Stationary.stationaryPotentialProjection.continuous.continuousAt.comp
      hforcing
  convert hprojected using 1
  funext z
  exact Stationary.koopman_stationaryPotentialProjection z
    (oneStepOriginForcingL2 M n h p hh)

/-- The coordinate-trace field of the projected one-step forcing has a
continuous translation orbit at the origin. -/
theorem continuousAt_koopman_oneStepPotentialTraceL2_zero {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (hh : 0 < h) :
    letI := potentialSequenceVAddInvariant M
    ContinuousAt (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z
        (oneStepPotentialTraceL2 M n h hh)) 0 := by
  letI := potentialSequenceVAddInvariant M
  unfold oneStepPotentialTraceL2
  simp_rw [map_sum]
  have hterm : ∀ i : Fin d, ContinuousAt (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) i
          (oneStepPotentialProjection M n h (Pi.single i 1) hh))) 0 := by
    intro i
    have hc := (Stationary.vectorL2Coord
      (mu := M.P.toMeasure) i).continuous.continuousAt.comp
        (continuousAt_koopman_oneStepPotentialProjection_zero
          M n h (Pi.single i 1) hh)
    convert hc using 1
    funext z
    exact Stationary.koopman_vectorL2Coord z i
      (oneStepPotentialProjection M n h (Pi.single i 1) hh)
  classical
  have hsum : ∀ s : Finset (Fin d), ContinuousAt (fun z : Vec d =>
      ∑ i ∈ s, Stationary.koopman (mu := M.P.toMeasure) z
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) i
          (oneStepPotentialProjection M n h (Pi.single i 1) hh))) 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using
        (continuousAt_const : ContinuousAt
          (fun _ : Vec d => (0 : Stationary.ScalarL2 M.P.toMeasure)) 0)
    | @insert i s his ih =>
        simp only [Finset.sum_insert his]
        exact (hterm i).add ih
  simpa only [Finset.sum_const_zero, Finset.sum_apply] using
    hsum Finset.univ

/-- The scalar trace defect has a continuous translation orbit at the
origin. -/
theorem continuousAt_koopman_oneStepTraceDefect_zero {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (hh : 0 < h) :
    letI := potentialSequenceVAddInvariant M
    ContinuousAt (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z
        (oneStepMultiplierAtL2 M n h 0 hh -
          oneStepPotentialTraceL2 M n h hh)) 0 := by
  letI := potentialSequenceVAddInvariant M
  simp_rw [map_sub]
  exact (continuousAt_koopman_oneStepMultiplierAtL2_zero M n h hh).sub
    (continuousAt_koopman_oneStepPotentialTraceL2_zero M n h hh)

/-- The literal forcing-column Koopman orbit is strongly continuous globally. -/
theorem continuous_koopman_oneStepOriginForcingL2 {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h) :
    letI := potentialSequenceVAddInvariant M
    Continuous (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z
        (oneStepOriginForcingL2 M n h p hh)) := by
  letI := potentialSequenceVAddInvariant M
  exact Stationary.continuous_koopmanOrbit_of_continuousAt_zero _
    (continuousAt_koopman_oneStepOriginForcingL2_zero M n h p hh)

/-- The projected-column Koopman orbit is strongly continuous globally. -/
theorem continuous_koopman_oneStepPotentialProjection {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h) :
    letI := potentialSequenceVAddInvariant M
    Continuous (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z
        (oneStepPotentialProjection M n h p hh)) := by
  letI := potentialSequenceVAddInvariant M
  exact Stationary.continuous_koopmanOrbit_of_continuousAt_zero _
    (continuousAt_koopman_oneStepPotentialProjection_zero M n h p hh)

/-- The solenoidal remainder of one forcing column has a globally strongly
continuous Koopman orbit. -/
theorem continuous_koopman_oneStepSolenoidalRemainder {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h) :
    letI := potentialSequenceVAddInvariant M
    Continuous (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z
        (oneStepOriginForcingL2 M n h p hh -
          oneStepPotentialProjection M n h p hh)) := by
  letI := potentialSequenceVAddInvariant M
  apply Stationary.continuous_koopmanOrbit_of_continuousAt_zero
  simp_rw [map_sub]
  exact (continuousAt_koopman_oneStepOriginForcingL2_zero M n h p hh).sub
    (continuousAt_koopman_oneStepPotentialProjection_zero M n h p hh)

/-- The projected coordinate-trace Koopman orbit is strongly continuous
globally. -/
theorem continuous_koopman_oneStepPotentialTraceL2 {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (hh : 0 < h) :
    letI := potentialSequenceVAddInvariant M
    Continuous (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z
        (oneStepPotentialTraceL2 M n h hh)) := by
  letI := potentialSequenceVAddInvariant M
  exact Stationary.continuous_koopmanOrbit_of_continuousAt_zero _
    (continuousAt_koopman_oneStepPotentialTraceL2_zero M n h hh)

/-- The one-step trace-defect Koopman orbit is strongly continuous globally. -/
theorem continuous_koopman_oneStepTraceDefect {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (hh : 0 < h) :
    letI := potentialSequenceVAddInvariant M
    Continuous (fun z : Vec d =>
      Stationary.koopman (mu := M.P.toMeasure) z
        (oneStepMultiplierAtL2 M n h 0 hh -
          oneStepPotentialTraceL2 M n h hh)) := by
  letI := potentialSequenceVAddInvariant M
  exact Stationary.continuous_koopmanOrbit_of_continuousAt_zero _
    (continuousAt_koopman_oneStepTraceDefect_zero M n h hh)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
