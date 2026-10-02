import SubdiffusiveProcess.CoarseGrainingVocab.CutoffRatioSup
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepStationaryForcing
import Mathlib.MeasureTheory.Integral.DominatedConvergence




open MeasureTheory Homogenization Homogenization.Book Filter

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- The one-step suffix multiplier evaluated at a spatial point. -/
def oneStepMultiplierAt {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (x : Vec d) : Sample d → ℝ :=
  fun omega => cutoffRatioMinusOne M (n + h) (n : ℤ) omega x

theorem measurable_oneStepMultiplierAt {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (x : Vec d) :
    Measurable (oneStepMultiplierAt M n h x) := by
  exact ((measurable_cutoff_uncurry M (n + h)).comp
      (measurable_id.prodMk measurable_const)).div
        ((measurable_cutoff_uncurry M n).comp
          (measurable_id.prodMk measurable_const)) |>.sub measurable_const

theorem continuous_oneStepMultiplierAt_sample {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (omega : Sample d) :
    Continuous (fun x => oneStepMultiplierAt M n h x omega) := by
  exact ((SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M (n + h) omega).div
      (SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M n omega)
      (fun x => (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M n omega x).ne')).sub
        continuous_const

/-- Every spatial evaluation of a nonempty suffix multiplier is in `L²`. -/
theorem memLp_two_oneStepMultiplierAt {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (x : Vec d) (hh : 0 < h) :
    MemLp (oneStepMultiplierAt M n h x) 2 M.P.toMeasure := by
  have hnm : (n : ℤ) < ((n + h : ℕ) : ℤ) := by
    exact_mod_cast (Nat.lt_add_of_pos_right hh)
  have hint :=
    (integral_abs_cutoffRatioMinusOne_rpow_root_le_raw
      M (n + h) (n : ℤ) x 2 (by norm_num) (by omega) hnm).1
  apply (memLp_two_iff_integrable_sq
    (measurable_oneStepMultiplierAt M n h x).aestronglyMeasurable).2
  simpa only [oneStepMultiplierAt, Real.rpow_two, sq_abs] using hint

/-- The canonical scalar `L²` realization of a spatial suffix evaluation. -/
def oneStepMultiplierAtL2 {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (x : Vec d) (hh : 0 < h) :
    Stationary.ScalarL2 M.P.toMeasure :=
  (memLp_two_oneStepMultiplierAt M n h x hh).toLp
    (oneStepMultiplierAt M n h x)

private theorem zero_mem_originCubeDomain {d : ℕ} :
    (0 : Vec d) ∈
      ((Ch02.cubeDomain (originCube d 0) : Ch02.Domain d) : Set (Vec d)) := by
  rw [Ch02.cubeDomain_coe, mem_openCubeSet_originCube_iff]
  intro i
  norm_num

/-- The literal squared difference of the translated suffix multiplier tends
to zero in expectation as the translation tends to zero. -/
theorem tendsto_integral_oneStepMultiplierAt_sub_zero_sq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (hh : 0 < h) :
    Tendsto
      (fun x : Vec d => ∫ omega : Sample d,
        (oneStepMultiplierAt M n h x omega -
          oneStepMultiplierAt M n h 0 omega) ^ 2 ∂M.P.toMeasure)
      (nhds 0) (nhds 0) := by
  let U : Ch02.Domain d := Ch02.cubeDomain (originCube d 0)
  let R : Sample d → ℝ := cutoffRatioSup M (n + h) n U
  let B : Sample d → ℝ := fun omega => 4 * R omega ^ 2
  have hnh : n < n + h := Nat.lt_add_of_pos_right hh
  have hRmem : MemLp R 2 M.P.toMeasure := by
    simpa only [R] using memLp_two_cutoffRatioSup_forward M hnh U
  have hBint : Integrable B M.P.toMeasure := by
    simpa only [B] using hRmem.integrable_sq.const_mul 4
  have hUmem : U.carrier ∈ nhds (0 : Vec d) := by
    exact U.isOpen.mem_nhds (by
      simpa only [U] using zero_mem_originCubeDomain (d := d))
  have hmeas : ∀ᶠ x : Vec d in nhds 0,
      AEStronglyMeasurable
        (fun omega : Sample d =>
          (oneStepMultiplierAt M n h x omega -
            oneStepMultiplierAt M n h 0 omega) ^ 2)
        M.P.toMeasure := by
    filter_upwards with x
    exact ((measurable_oneStepMultiplierAt M n h x).sub
      (measurable_oneStepMultiplierAt M n h 0)).pow_const 2 |>.aestronglyMeasurable
  have hbound : ∀ᶠ x : Vec d in nhds 0, ∀ᵐ omega : Sample d ∂M.P.toMeasure,
      ‖(oneStepMultiplierAt M n h x omega -
          oneStepMultiplierAt M n h 0 omega) ^ 2‖ ≤ B omega := by
    filter_upwards [hUmem] with x hx
    filter_upwards with omega
    have hxR := cutoffRatio_le_cutoffRatioSup M (n + h) n U omega hx
    have h0R := cutoffRatio_le_cutoffRatioSup M (n + h) n U omega
      (by simpa only [U] using zero_mem_originCubeDomain (d := d))
    have hx0 : 0 ≤ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega x /
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega x :=
      (div_pos (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M (n + h) omega x)
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M n omega x)).le
    have h00 : 0 ≤ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega 0 /
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega 0 :=
      (div_pos (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M (n + h) omega 0)
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M n omega 0)).le
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    dsimp only [oneStepMultiplierAt, cutoffRatioMinusOne, aCutoffAtInt]
    simp only [if_neg (not_lt_of_ge (Int.natCast_nonneg n)), Int.toNat_natCast]
    dsimp only [B, R]
    nlinarith [sq_nonneg
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega x /
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega x -
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h) omega 0 /
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n omega 0)]
  have hlim : ∀ᵐ omega : Sample d ∂M.P.toMeasure,
      Tendsto
        (fun x : Vec d =>
          (oneStepMultiplierAt M n h x omega -
            oneStepMultiplierAt M n h 0 omega) ^ 2)
        (nhds 0) (nhds 0) := by
    filter_upwards with omega
    have hc : Continuous (fun x : Vec d =>
        (oneStepMultiplierAt M n h x omega -
          oneStepMultiplierAt M n h 0 omega) ^ 2) :=
      ((continuous_oneStepMultiplierAt_sample M n h omega).sub
        continuous_const).pow 2
    have hc0 := (hc.continuousAt : ContinuousAt _ (0 : Vec d))
    change Tendsto _ (nhds (0 : Vec d))
      (nhds ((oneStepMultiplierAt M n h 0 omega -
        oneStepMultiplierAt M n h 0 omega) ^ 2)) at hc0
    simpa using hc0
  simpa only [integral_zero] using
    tendsto_integral_filter_of_dominated_convergence B hmeas hbound hBint hlim

/-- The one-step suffix multiplier has a strongly continuous scalar `L²`
orbit at the identity translation.  This is proved directly on the literal GMC
carrier, without the unavailable `R1Space`/`BorelSpace` instances required by
the generic Koopman theorem. -/
theorem continuousAt_oneStepMultiplierAtL2_zero {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (hh : 0 < h) :
    ContinuousAt (fun x : Vec d => oneStepMultiplierAtL2 M n h x hh) 0 := by
  let D : Vec d → Sample d → ℝ := fun x omega =>
    oneStepMultiplierAt M n h x omega -
      oneStepMultiplierAt M n h 0 omega
  have hDmem : ∀ x, MemLp (D x) 2 M.P.toMeasure := fun x =>
    (memLp_two_oneStepMultiplierAt M n h x hh).sub
      (memLp_two_oneStepMultiplierAt M n h 0 hh)
  have hint : Tendsto
      (fun x : Vec d => ∫ omega : Sample d, (D x omega) ^ 2 ∂M.P.toMeasure)
      (nhds 0) (nhds 0) := by
    simpa only [D] using
      tendsto_integral_oneStepMultiplierAt_sub_zero_sq M n h hh
  have hnormReal : Tendsto
      (fun x : Vec d => (eLpNorm (D x) 2 M.P.toMeasure).toReal)
      (nhds 0) (nhds 0) := by
    have heq : (fun x : Vec d =>
        (eLpNorm (D x) 2 M.P.toMeasure).toReal) =
        fun x => Real.sqrt (∫ omega : Sample d,
          (D x omega) ^ 2 ∂M.P.toMeasure) := by
      funext x
      rw [← Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq (hDmem x),
        Real.sqrt_sq (ENNReal.toReal_nonneg)]
    rw [heq]
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp hint
  have hnorm : Tendsto
      (fun x : Vec d => eLpNorm (D x) 2 M.P.toMeasure)
      (nhds 0) (nhds 0) :=
    (ENNReal.tendsto_toReal_zero_iff
      (fun x => (hDmem x).eLpNorm_ne_top)).1 hnormReal
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm
    (fun x : Vec d => oneStepMultiplierAtL2 M n h x hh)
    (oneStepMultiplierAt M n h 0)
    (memLp_two_oneStepMultiplierAt M n h 0 hh)).2
  have heq : (fun x : Vec d => eLpNorm
      ((oneStepMultiplierAtL2 M n h x hh : Sample d → ℝ) -
        oneStepMultiplierAt M n h 0) 2 M.P.toMeasure) =
      fun x => eLpNorm (D x) 2 M.P.toMeasure := by
    funext x
    apply eLpNorm_congr_ae
    filter_upwards [MemLp.coeFn_toLp
      (memLp_two_oneStepMultiplierAt M n h x hh)] with omega homega
    have homega' :
        (oneStepMultiplierAtL2 M n h x hh : Sample d → ℝ) omega =
          oneStepMultiplierAt M n h x omega := by
      simpa only [oneStepMultiplierAtL2] using homega
    change (oneStepMultiplierAtL2 M n h x hh : Sample d → ℝ) omega -
        oneStepMultiplierAt M n h 0 omega = D x omega
    rw [homega']
  rw [heq]
  exact hnorm

/-- The Koopman translate of a spatial multiplier evaluation is the evaluation
at the correspondingly translated point. -/
theorem koopman_oneStepMultiplierAtL2 {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (x y : Vec d) (hh : 0 < h) :
    letI := potentialSequenceVAddInvariant M
    Stationary.koopman (mu := M.P.toMeasure) x
        (oneStepMultiplierAtL2 M n h y hh) =
      oneStepMultiplierAtL2 M n h (y + x) hh := by
  letI := potentialSequenceVAddInvariant M
  change Lp.compMeasurePreserving (fun omega : Sample d => x +ᵥ omega)
      (Stationary.measurePreserving_const_vadd
        (mu := M.P.toMeasure) x)
      ((memLp_two_oneStepMultiplierAt M n h y hh).toLp
        (oneStepMultiplierAt M n h y)) =
    (memLp_two_oneStepMultiplierAt M n h (y + x) hh).toLp
      (oneStepMultiplierAt M n h (y + x))
  rw [Lp.toLp_compMeasurePreserving]
  apply (MemLp.toLp_eq_toLp_iff _ _).2
  exact Filter.Eventually.of_forall fun omega => by
    dsimp only [oneStepMultiplierAt, cutoffRatioMinusOne, aCutoffAtInt,
      Function.comp_apply, potentialSampleAddAction]
    simp only [if_neg (not_lt_of_ge (Int.natCast_nonneg n)), Int.toNat_natCast]
    change SubdiffusiveProcess.Frozen.Assumptions.aCutoff M (n + h)
          (translatePotentialSequence x omega) y /
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n
          (translatePotentialSequence x omega) y - 1 = _
    rw [aCutoff_translatePotentialSequence M (n + h) x omega y,
      aCutoff_translatePotentialSequence M n x omega y]

/-- Translating the origin multiplier by the Koopman action is exactly spatial
evaluation of the same suffix multiplier. -/
theorem koopman_oneStepMultiplierAtL2_zero {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (x : Vec d) (hh : 0 < h) :
    letI := potentialSequenceVAddInvariant M
    Stationary.koopman (mu := M.P.toMeasure) x
        (oneStepMultiplierAtL2 M n h 0 hh) =
      oneStepMultiplierAtL2 M n h x hh := by
  letI := potentialSequenceVAddInvariant M
  simpa only [zero_add] using
    koopman_oneStepMultiplierAtL2 M n h x 0 hh

/-- Strong continuity at the identity for the actual Koopman orbit of the
one-step suffix multiplier. -/
theorem continuousAt_koopman_oneStepMultiplierAtL2_zero {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (hh : 0 < h) :
    letI := potentialSequenceVAddInvariant M
    ContinuousAt
      (fun x : Vec d => Stationary.koopman (mu := M.P.toMeasure) x
        (oneStepMultiplierAtL2 M n h 0 hh)) 0 := by
  letI := potentialSequenceVAddInvariant M
  have heq : (fun x : Vec d => Stationary.koopman (mu := M.P.toMeasure) x
      (oneStepMultiplierAtL2 M n h 0 hh)) =
      fun x => oneStepMultiplierAtL2 M n h x hh := by
    funext x
    exact koopman_oneStepMultiplierAtL2_zero M n h x hh
  rw [heq]
  exact continuousAt_oneStepMultiplierAtL2_zero M n h hh

/-- The direct identity-continuity result extends to the full Koopman orbit by
the group law and the isometry of every fixed translation. -/
theorem continuous_koopman_oneStepMultiplierAtL2 {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (hh : 0 < h) :
    letI := potentialSequenceVAddInvariant M
    Continuous
      (fun x : Vec d => Stationary.koopman (mu := M.P.toMeasure) x
        (oneStepMultiplierAtL2 M n h 0 hh)) := by
  letI := potentialSequenceVAddInvariant M
  apply continuous_iff_continuousAt.mpr
  intro x₀
  let f := oneStepMultiplierAtL2 M n h 0 hh
  let orbit : Vec d → Stationary.ScalarL2 M.P.toMeasure := fun x =>
    Stationary.koopman (mu := M.P.toMeasure) x f
  have hzero : ContinuousAt orbit 0 := by
    simpa only [orbit, f] using
      continuousAt_koopman_oneStepMultiplierAtL2_zero M n h hh
  have hshift : ContinuousAt (fun x : Vec d => x - x₀) x₀ :=
    continuousAt_id.sub continuousAt_const
  have hinner : ContinuousAt (fun x : Vec d => orbit (x - x₀)) x₀ := by
    exact hzero.comp_of_eq hshift (sub_self x₀)
  have houter : Continuous
      (Stationary.koopman (mu := M.P.toMeasure) x₀ :
        Stationary.ScalarL2 M.P.toMeasure →
          Stationary.ScalarL2 M.P.toMeasure) :=
    (Stationary.koopman (mu := M.P.toMeasure) x₀).continuous
  have hcomp : ContinuousAt
      (fun x : Vec d => Stationary.koopman (mu := M.P.toMeasure) x₀
        (orbit (x - x₀))) x₀ :=
    houter.continuousAt.comp hinner
  have heq : (fun x : Vec d => Stationary.koopman (mu := M.P.toMeasure) x₀
      (orbit (x - x₀))) = orbit := by
    funext x
    dsimp only [orbit, f]
    rw [koopman_oneStepMultiplierAtL2_zero M n h (x - x₀) hh,
      koopman_oneStepMultiplierAtL2_zero M n h x hh]
    simpa only [sub_add_cancel] using
      koopman_oneStepMultiplierAtL2 M n h x₀ (x - x₀) hh
  rw [heq] at hcomp
  exact hcomp

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
