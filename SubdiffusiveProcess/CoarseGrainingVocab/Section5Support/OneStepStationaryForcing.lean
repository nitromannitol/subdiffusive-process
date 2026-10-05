module

public import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedProviders
public import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationaryProjection

@[expose] public section

/-!
# Stationary forcing for the Section 5 one-step corrector

This file puts the literal GMC potential-sequence law on the stationary
Hilbert-space carrier and constructs the `L²` forcing
`(a_{n+h} a_n^{-1} - 1) p` at the origin.  It is the carrier prefix of
`l.laplacian.corrector.energy` (`l.laplacian.corrector.energy`).

The construction uses an action and a projection. The forcing is the GMC
cutoff block, and its square integrability is discharged by the established
fixed-point cutoff moment theorem.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- Real translations act on every potential layer in the manuscript
convention `g(x) -> g(x + z)`. -/
noncomputable instance potentialSampleAddAction (d : ℕ) :
    AddAction (Vec d) (_root_.SubdiffusiveProcess.Model.PotentialSample d) where
  vadd := translatePotentialSequence
  zero_vadd := by
    intro omega
    funext k
    apply _root_.SubdiffusiveProcess.Model.PotentialField.ext
    intro x
    change omega k (x + 0) = omega k x
    rw [add_zero]
  add_vadd := by
    intro z w omega
    funext k
    apply _root_.SubdiffusiveProcess.Model.PotentialField.ext
    intro x
    change omega k (x + (z + w)) = omega k ((x + z) + w)
    rw [add_assoc]

/-- Fixed translations of the sequence carrier are measurable. -/
noncomputable instance potentialSampleMeasurableConstVAdd (d : ℕ) :
    MeasurableConstVAdd (Vec d) (_root_.SubdiffusiveProcess.Model.PotentialSample d) where
  measurable_const_vadd := fun z => measurable_translatePotentialSequence z

/-- The proved stationarity of the product sequence law supplies the invariant
measure structure used by the stationary projection. -/
noncomputable abbrev potentialSequenceVAddInvariant {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    VAddInvariantMeasure (Vec d) (_root_.SubdiffusiveProcess.Model.PotentialSample d) M.P.toMeasure where
  measure_preimage_vadd := by
    intro z s hs
    change M.P.toMeasure ((translatePotentialSequence z) ⁻¹' s) =
      M.P.toMeasure s
    rw [← Measure.map_apply (measurable_translatePotentialSequence z) hs]
    exact congrArg (fun mu : Measure (_root_.SubdiffusiveProcess.Model.PotentialSample d) => mu s)
      (potentialSequenceLaw_stationary M z)

/-- The multiplicative suffix block at the spatial origin, minus one. -/
def oneStepOriginMultiplier {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
  fun omega => cutoffRatioMinusOne M (n + h) (n : ℤ) omega 0

theorem measurable_oneStepOriginMultiplier {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) :
    Measurable (oneStepOriginMultiplier M n h) := by
  have hmeas : Measurable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      _root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega 0 /
        _root_.SubdiffusiveProcess.Model.aCutoff M n omega 0 - 1) :=
    ((_root_.SubdiffusiveProcess.Model.measurable_aCutoff M (n + h) 0).div
      (_root_.SubdiffusiveProcess.Model.measurable_aCutoff M n 0)).sub
        (measurable_const : Measurable fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d => (1 : ℝ))
  simpa only [oneStepOriginMultiplier, cutoffRatioMinusOne, aCutoffAtInt,
    Int.natCast_nonneg, ↓reduceIte] using! hmeas

/-- A nonempty suffix block has a square-integrable origin multiplier. -/
theorem memLp_two_oneStepOriginMultiplier {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (hh : 0 < h) :
    MemLp (oneStepOriginMultiplier M n h) 2 M.P.toMeasure := by
  have hnm : (n : ℤ) < ((n + h : ℕ) : ℤ) := by
    exact_mod_cast (Nat.lt_add_of_pos_right hh)
  have hint :=
    (integral_abs_cutoffRatioMinusOne_rpow_root_le_raw
      M (n + h) (n : ℤ) 0 2 (by norm_num) (by omega) hnm).1
  apply (memLp_two_iff_integrable_sq
    (measurable_oneStepOriginMultiplier M n h).aestronglyMeasurable).2
  simpa only [oneStepOriginMultiplier, Real.rpow_two, sq_abs] using hint

/-- The vector forcing `X p` used in the stationary Weyl decomposition. -/
def oneStepOriginForcing {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d) :
    _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d :=
  fun omega => oneStepOriginMultiplier M n h omega • HilbertVec.ofVec p

theorem measurable_oneStepOriginForcing {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d) :
    Measurable (oneStepOriginForcing M n h p) := by
  exact (measurable_oneStepOriginMultiplier M n h).smul_const _

/-- The literal one-step origin forcing belongs to stationary vector `L²`. -/
theorem memLp_two_oneStepOriginForcing {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (hh : 0 < h) :
    MemLp (oneStepOriginForcing M n h p) 2 M.P.toMeasure := by
  have hscalar := memLp_two_oneStepOriginMultiplier M n h hh
  have hint := hscalar.integrable_sq
  apply (memLp_two_iff_integrable_sq_norm
    (measurable_oneStepOriginForcing M n h p).aestronglyMeasurable).2
  have hconst := hint.const_mul (‖HilbertVec.ofVec p‖ ^ 2)
  apply hconst.congr
  filter_upwards with omega
  simp only [oneStepOriginForcing, norm_smul, Real.norm_eq_abs]
  rw [mul_pow, sq_abs]
  ring

/-- The canonical `L²` representative of the one-step forcing. -/
def oneStepOriginForcingL2 {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (hh : 0 < h) :
    Stationary.VectorL2 d M.P.toMeasure :=
  (memLp_two_oneStepOriginForcing M n h p hh).toLp
    (oneStepOriginForcing M n h p)

/-- The literal one-step forcing is additive in its deterministic probe. -/
theorem oneStepOriginForcingL2_add {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p q : Vec d) (hh : 0 < h) :
    oneStepOriginForcingL2 M n h (p + q) hh =
      oneStepOriginForcingL2 M n h p hh +
        oneStepOriginForcingL2 M n h q hh := by
  have hadd :
      oneStepOriginForcingL2 M n h p hh +
          oneStepOriginForcingL2 M n h q hh =
        ((memLp_two_oneStepOriginForcing M n h p hh).add
          (memLp_two_oneStepOriginForcing M n h q hh)).toLp
            (oneStepOriginForcing M n h p +
              oneStepOriginForcing M n h q) :=
    (MemLp.toLp_add _ _).symm
  rw [hadd]
  exact (MemLp.toLp_eq_toLp_iff _ _).2
    (Filter.Eventually.of_forall fun omega => by
      change oneStepOriginMultiplier M n h omega •
          HilbertVec.ofVec (p + q) =
        oneStepOriginMultiplier M n h omega • HilbertVec.ofVec p +
          oneStepOriginMultiplier M n h omega • HilbertVec.ofVec q
      rw [show HilbertVec.ofVec (p + q) =
        HilbertVec.ofVec p + HilbertVec.ofVec q by rfl, smul_add])

/-- The literal one-step forcing commutes with scalar multiplication of its
deterministic probe. -/
theorem oneStepOriginForcingL2_smul {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (c : ℝ) (p : Vec d) (hh : 0 < h) :
    oneStepOriginForcingL2 M n h (c • p) hh =
      c • oneStepOriginForcingL2 M n h p hh := by
  have hsmul :
      c • oneStepOriginForcingL2 M n h p hh =
        ((memLp_two_oneStepOriginForcing M n h p hh).const_smul c).toLp
          (c • oneStepOriginForcing M n h p) :=
    (MemLp.toLp_const_smul _ _).symm
  rw [hsmul]
  exact (MemLp.toLp_eq_toLp_iff _ _).2
    (Filter.Eventually.of_forall fun omega => by
      change oneStepOriginMultiplier M n h omega •
          HilbertVec.ofVec (c • p) =
        c • (oneStepOriginMultiplier M n h omega • HilbertVec.ofVec p)
      rw [show HilbertVec.ofVec (c • p) =
        c • HilbertVec.ofVec p by rfl, smul_smul, smul_smul]
      ring_nf)

/-- The one-step origin forcing as a genuine linear map of the deterministic
probe. -/
def oneStepOriginForcingL2Linear {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (hh : 0 < h) :
    Vec d →ₗ[ℝ] Stationary.VectorL2 d M.P.toMeasure where
  toFun := fun p => oneStepOriginForcingL2 M n h p hh
  map_add' := fun p q => oneStepOriginForcingL2_add M n h p q hh
  map_smul' := fun c p => oneStepOriginForcingL2_smul M n h c p hh

/-- The stationary potential component of the one-step forcing. -/
def oneStepPotentialProjection {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (hh : 0 < h) : Stationary.VectorL2 d M.P.toMeasure := by
  letI := potentialSequenceVAddInvariant M
  exact Stationary.stationaryPotentialProjection
    (oneStepOriginForcingL2 M n h p hh)

/-- The stationary potential component is a genuine linear map of the
deterministic probe. -/
def oneStepPotentialProjectionLinear {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (hh : 0 < h) :
    Vec d →ₗ[ℝ] Stationary.VectorL2 d M.P.toMeasure := by
  letI := potentialSequenceVAddInvariant M
  exact Stationary.stationaryPotentialProjection.toLinearMap.comp
    (oneStepOriginForcingL2Linear M n h hh)

@[simp] theorem oneStepPotentialProjectionLinear_apply {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h) :
    oneStepPotentialProjectionLinear M n h hh p =
      oneStepPotentialProjection M n h p hh :=
  rfl

/-- Orthogonal projection does not increase the stationary `L²` norm. -/
theorem norm_oneStepPotentialProjection_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (hh : 0 < h) :
    ‖oneStepPotentialProjection M n h p hh‖ ≤
      ‖oneStepOriginForcingL2 M n h p hh‖ := by
  let := potentialSequenceVAddInvariant M
  change
    ‖Stationary.stationaryPotentialProjection
        (oneStepOriginForcingL2 M n h p hh)‖ ≤
      ‖oneStepOriginForcingL2 M n h p hh‖
  exact (Stationary.stationaryPotentialSubspace
    (mu := M.P.toMeasure) (d := d)).norm_starProjection_apply_le _

/-- The one-step stationary projection is a stationary potential field. -/
theorem oneStepPotentialProjection_mem_stationaryPotentialSubspace {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h) :
    oneStepPotentialProjection M n h p hh ∈
      @Stationary.stationaryPotentialSubspace d (_root_.SubdiffusiveProcess.Model.PotentialSample d) inferInstance
        M.P.toMeasure (potentialSampleAddAction d)
        (potentialSampleMeasurableConstVAdd d)
        (potentialSequenceVAddInvariant M) := by
  let := potentialSequenceVAddInvariant M
  change Stationary.stationaryPotentialProjection
      (oneStepOriginForcingL2 M n h p hh) ∈
    Stationary.stationaryPotentialSubspace
      (mu := M.P.toMeasure) (d := d)
  exact Stationary.stationaryPotentialProjection_mem
    (oneStepOriginForcingL2 M n h p hh)

/-- The remainder after removing the stationary potential projection is a
stationary solenoidal field. -/
theorem oneStepOriginForcingL2_sub_projection_mem_stationarySolenoidalSubspace
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h) :
    oneStepOriginForcingL2 M n h p hh -
        oneStepPotentialProjection M n h p hh ∈
      @Stationary.stationarySolenoidalSubspace d (_root_.SubdiffusiveProcess.Model.PotentialSample d) inferInstance
        M.P.toMeasure (potentialSampleAddAction d)
        (potentialSampleMeasurableConstVAdd d)
        (potentialSequenceVAddInvariant M) := by
  let := potentialSequenceVAddInvariant M
  change oneStepOriginForcingL2 M n h p hh -
      Stationary.stationaryPotentialProjection
        (oneStepOriginForcingL2 M n h p hh) ∈
    Stationary.stationarySolenoidalSubspace
      (mu := M.P.toMeasure) (d := d)
  exact Stationary.sub_stationaryPotentialProjection_mem_orthogonal
    (oneStepOriginForcingL2 M n h p hh)

/-- The potential and solenoidal components of the literal one-step forcing
are orthogonal in stationary `L²`. -/
theorem inner_oneStepPotentialProjection_solenoidalRemainder_eq_zero {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h) :
    inner ℝ (oneStepPotentialProjection M n h p hh)
      (oneStepOriginForcingL2 M n h p hh -
        oneStepPotentialProjection M n h p hh) = 0 := by
  let := potentialSequenceVAddInvariant M
  exact Submodule.inner_right_of_mem_orthogonal
    (Stationary.stationaryPotentialProjection_mem
      (oneStepOriginForcingL2 M n h p hh))
    (Stationary.sub_stationaryPotentialProjection_mem_orthogonal
      (oneStepOriginForcingL2 M n h p hh))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
