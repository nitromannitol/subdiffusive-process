module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.ProbeMomentUniform
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.LpMoment

@[expose] public section

/-!
# Moments of the probe form at nonpositive cube scales

`ProbeMomentUniform.lean` bounds the probe moment at every **nonnegative** scale
by the unit-cube moment, using subdivision subadditivity — which only points
downwards.  The rows of `Ch02.HomogenizationErrorFinite` run over `k = N - l`
for every `l : ℕ`, so nonpositive scales occur too and need their own uniform
bound.

They are much easier: a triadic cube centred at the origin of scale `k ≤ 0` sits
inside the *unit* cube, so the origin-cube cover depth of `ACutoffP4Bounds.lean`
is at most `1`, and the pathwise envelope bound of
`CoarseResponseMoments.lean` therefore uses one of only **two** deterministic
envelope scales.  Both have every exponential moment
(`integrable_exp_mul_aCutoffCubeLogEnvelope`), so a single dominating variable
serves all `k ≤ 0`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## The cover depth of small centred cubes -/

theorem isClosed_halfBox (d : ℕ) :
    IsClosed {x : Vec d | ∀ i, |x i| ≤ (1 / 2 : ℝ)} := by
  have hset : {x : Vec d | ∀ i, |x i| ≤ (1 / 2 : ℝ)} =
      ⋂ i : Fin d, {x : Vec d | |x i| ≤ (1 / 2 : ℝ)} := by
    ext x
    simp
  rw [hset]
  exact isClosed_iInter fun i =>
    isClosed_le ((continuous_apply i).abs) continuous_const

theorem openCubeSet_originCube_subset_halfBox [NeZero d] {k : ℤ} (hk : k ≤ 0) :
    openCubeSet (originCube d k) ⊆ {x : Vec d | ∀ i, |x i| ≤ (1 / 2 : ℝ)} := by
  intro x hx i
  have hxi := (Homogenization.mem_openCubeSet_originCube_iff.mp hx) i
  have h3 : (3 : ℝ) ^ k ≤ 1 := by
    have := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hk
    simpa using this
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  rw [abs_le]
  constructor <;> nlinarith [hxi.1, hxi.2]

theorem halfBox_subset_openCubeSet_one [NeZero d] :
    {x : Vec d | ∀ i, |x i| ≤ (1 / 2 : ℝ)} ⊆
      openCubeSet (originCube d ((1 : ℕ) : ℤ)) := by
  intro x hx
  rw [Homogenization.mem_openCubeSet_originCube_iff]
  intro i
  have hxi : |x i| ≤ (1 / 2 : ℝ) := hx i
  have habs := abs_le.mp hxi
  have h3 : (3 : ℝ) ^ ((1 : ℕ) : ℤ) = 3 := by norm_num
  rw [h3]
  constructor <;> linarith [habs.1, habs.2]

/-- The origin-cube cover depth of a centred cube of nonpositive scale is at
most one. -/
theorem aCutoffCubeOriginCoverDepth_originCube_le_one [NeZero d] {k : ℤ}
    (hk : k ≤ 0) :
    aCutoffCubeOriginCoverDepth (originCube d k) ≤ 1 := by
  classical
  refine Nat.find_le ?_
  refine subset_trans ?_ (halfBox_subset_openCubeSet_one (d := d))
  exact closure_minimal (openCubeSet_originCube_subset_halfBox hk)
    (isClosed_halfBox d)

/-! ## A single dominating variable for all nonpositive scales -/

/-- The exponential of the cube logarithmic envelope has every moment. -/
theorem memLp_exp_aCutoffCubeLogEnvelope [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (j : ℤ) {xi : ℝ}
    (hxi : 1 ≤ xi) :
    MemLp (fun omega => Real.exp (aCutoffCubeLogEnvelope M L j omega))
      (ENNReal.ofReal xi) M.P.toMeasure := by
  have hxi0 : 0 < xi := lt_of_lt_of_le zero_lt_one hxi
  have hint := integrable_exp_mul_aCutoffCubeLogEnvelope M L j (q := xi) hxi0
  have hmeas : AEStronglyMeasurable
      (fun omega => Real.exp (aCutoffCubeLogEnvelope M L j omega))
      M.P.toMeasure :=
    ((measurable_aCutoffCubeLogEnvelope M L j).exp).aestronglyMeasurable
  change eLpNorm _ _ _ < ⊤
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by simpa using (ENNReal.ofReal_pos.mpr hxi0).ne') ENNReal.ofReal_ne_top hmeas]
  have hrw : ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      ‖Real.exp (aCutoffCubeLogEnvelope M L j omega)‖ₑ ^
          (ENNReal.ofReal xi).toReal =
        ENNReal.ofReal
          (Real.exp (xi * aCutoffCubeLogEnvelope M L j omega)) := by
    intro omega
    rw [ENNReal.toReal_ofReal hxi0.le, Real.enorm_eq_ofReal (Real.exp_pos _).le,
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hxi0.le]
    congr 1
    rw [← Real.exp_mul, mul_comm]
  simp only [hrw]
  have hfin := hint.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun omega => (Real.exp_pos _).le)] at hfin
  exact hfin

/-- **Uniform moments at nonpositive scales.** -/
theorem exists_uniform_probe_moment_nonpos [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (alpha : ℝ) (v : Vec d)
    {xi : ℝ} (hxi : 1 ≤ xi) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℤ, k ≤ 0 →
      (∫ omega, (cutoffProbeForm M L alpha (originCube d k) omega v) ^ xi
        ∂M.P.toMeasure) ≤ B := by
  classical
  have hxi0 : 0 < xi := lt_of_lt_of_le zero_lt_one hxi
  set p : Vec d := (Real.sqrt alpha)⁻¹ • v with hp
  set q : Vec d := Real.sqrt alpha • v with hq
  set Kv : ℝ := (1 / 2 : ℝ) * absCoordSum p * absCoordSum p +
    (1 / 2 : ℝ) * absCoordSum q * absCoordSum q with hKv
  have hKv0 : 0 ≤ Kv := by
    have := absCoordSum_nonneg p
    have := absCoordSum_nonneg q
    rw [hKv]; positivity
  set Z : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun omega =>
    Kv * (Real.exp (aCutoffCubeLogEnvelope M L 0 omega) +
      Real.exp (aCutoffCubeLogEnvelope M L 1 omega)) + |vecDot p q| with hZ
  have hZmem : MemLp Z (ENNReal.ofReal xi) M.P.toMeasure := by
    have h0 := memLp_exp_aCutoffCubeLogEnvelope M L 0 hxi
    have h1 := memLp_exp_aCutoffCubeLogEnvelope M L 1 hxi
    exact ((h0.add h1).const_mul Kv).add (memLp_const _)
  have hZint : Integrable (fun omega => |Z omega| ^ xi) M.P.toMeasure :=
    integrable_abs_rpow_of_memLp hxi0 hZmem
  refine ⟨∫ omega, |Z omega| ^ xi ∂M.P.toMeasure,
    integral_nonneg fun omega => Real.rpow_nonneg (abs_nonneg _) _, ?_⟩
  intro k hk
  have hdom : ∀ omega,
      (cutoffProbeForm M L alpha (originCube d k) omega v) ^ xi ≤
        |Z omega| ^ xi := by
    intro omega
    have hcpf0 := cutoffProbeForm_nonneg M L alpha (originCube d k) omega v
    have hbase := abs_cutoffResponseOnCube_le_exp_envelope M L p q
      (originCube d k) omega
    have hdepth := aCutoffCubeOriginCoverDepth_originCube_le_one
      (d := d) hk
    have hcover : aCutoffCubeOriginCoverScale (originCube d k) = 0 ∨
        aCutoffCubeOriginCoverScale (originCube d k) = 1 := by
      have hcases : aCutoffCubeOriginCoverDepth (originCube d k) = 0 ∨
          aCutoffCubeOriginCoverDepth (originCube d k) = 1 := by omega
      rcases hcases with h | h
      · left; rw [aCutoffCubeOriginCoverScale, h]; rfl
      · right; rw [aCutoffCubeOriginCoverScale, h]; rfl
    have hle : cutoffProbeForm M L alpha (originCube d k) omega v ≤ Z omega := by
      have habs : |cutoffResponseOnCube M L p q (originCube d k) omega| ≤
          Kv * Real.exp (aCutoffCubeLogEnvelope M L
            (aCutoffCubeOriginCoverScale (originCube d k)) omega) +
            |vecDot p q| := by
        simpa [hKv] using hbase
      have hstep : cutoffProbeForm M L alpha (originCube d k) omega v ≤
          Kv * Real.exp (aCutoffCubeLogEnvelope M L
            (aCutoffCubeOriginCoverScale (originCube d k)) omega) +
            |vecDot p q| :=
        le_trans (le_abs_self _) habs
      refine le_trans hstep ?_
      have hexp0 : (0 : ℝ) < Real.exp (aCutoffCubeLogEnvelope M L 0 omega) :=
        Real.exp_pos _
      have hexp1 : (0 : ℝ) < Real.exp (aCutoffCubeLogEnvelope M L 1 omega) :=
        Real.exp_pos _
      rcases hcover with h | h <;> rw [h, hZ] <;> nlinarith [hKv0, hexp0, hexp1]
    have hZ0 : 0 ≤ Z omega := le_trans hcpf0 hle
    refine Real.rpow_le_rpow hcpf0 ?_ hxi0.le
    rw [abs_of_nonneg hZ0]
    exact hle
  exact integral_mono
    (integrable_cutoffProbeForm_rpow M L alpha (originCube d k) v hxi)
    hZint hdom


/-! ## A single moment bound valid on every triadic cube -/

/-- **Uniform moments over all triadic cubes.**  For a fixed probe direction the
`xi`-th moment of the probe form is bounded by one constant, simultaneously over
every triadic cube of every scale. -/
theorem exists_uniform_cutoffProbeForm_moment [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {alpha : ℝ}
    (halpha : 0 < alpha) (u : Vec d) {xi : ℝ} (hxi : 1 ≤ xi) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ R : TriadicCube d,
      (∫ omega, (cutoffProbeForm M L alpha R omega u) ^ xi ∂M.P.toMeasure) ≤
        B := by
  classical
  obtain ⟨Bneg, hBneg0, hBneg⟩ :=
    exists_uniform_probe_moment_nonpos M L alpha u hxi
  set Bpos : ℝ := ∫ omega,
    (cutoffProbeForm M L alpha (originCube d (0 : ℤ)) omega u) ^ xi
      ∂M.P.toMeasure with hBpos
  have hBpos0 : 0 ≤ Bpos :=
    integral_nonneg fun omega =>
      Real.rpow_nonneg (cutoffProbeForm_nonneg M L alpha _ omega u) _
  refine ⟨max Bpos Bneg, le_trans hBpos0 (le_max_left _ _), ?_⟩
  intro R
  have hR : (∫ omega, (cutoffProbeForm M L alpha R omega u) ^ xi
      ∂M.P.toMeasure) =
      ∫ omega, (cutoffProbeForm M L alpha (originCube d R.scale) omega u) ^ xi
        ∂M.P.toMeasure :=
    integral_cutoffProbeForm_rpow_eq_originCube M L alpha R u xi
  rw [hR]
  rcases le_or_gt (0 : ℤ) R.scale with hs | hs
  · have hnat : R.scale = ((R.scale.toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg hs).symm
    rw [hnat]
    refine le_trans ?_ (le_max_left Bpos Bneg)
    exact integral_cutoffProbeForm_rpow_originCube_le M L halpha
      R.scale.toNat u hxi
  · exact le_trans (hBneg R.scale (le_of_lt hs)) (le_max_right Bpos Bneg)


/-- `lpMoment` of the probe form is the plain moment root. -/
theorem lpMoment_cutoffProbeForm_eq [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (alpha : ℝ)
    (R : TriadicCube d) (u : Vec d) (xi : ℝ) :
    lpMoment M.P.toMeasure xi (fun omega => cutoffProbeForm M L alpha R omega u) =
      (∫ omega, (cutoffProbeForm M L alpha R omega u) ^ xi
        ∂M.P.toMeasure) ^ xi⁻¹ := by
  simp only [lpMoment]
  congr 2
  funext omega
  rw [abs_of_nonneg (cutoffProbeForm_nonneg M L alpha R omega u)]

/-- **A single `L^xi` bound for the whole finite probe sum, valid on every
triadic cube.**  This is the per-cube input of the union bound over a descendant
family. -/
theorem exists_uniform_lpMoment_finiteProbeSum [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {alpha : ℝ}
    (halpha : 0 < alpha) {xi : ℝ} (hxi : 1 ≤ xi) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ R : TriadicCube d,
      lpMoment M.P.toMeasure xi
        (fun omega => finiteProbeSum M L alpha R omega) ≤ B := by
  classical
  have hxi0 : 0 < xi := lt_of_lt_of_le zero_lt_one hxi
  have hall : ∀ u : Vec d, ∃ B : ℝ, 0 ≤ B ∧ ∀ R : TriadicCube d,
      (∫ omega, (cutoffProbeForm M L alpha R omega u) ^ xi
        ∂M.P.toMeasure) ≤ B :=
    fun u => exists_uniform_cutoffProbeForm_moment M L halpha u hxi
  choose Bu hBu0 hBu using hall
  set root : Vec d → ℝ := fun u => (Bu u) ^ xi⁻¹ with hroot
  have hroot0 : ∀ u, 0 ≤ root u := fun u => Real.rpow_nonneg (hBu0 u) _
  refine ⟨∑ i : Fin d, ∑ j : Fin d, (1 / 2 : ℝ) *
      (root ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)) +
        root (Pi.single i (1 : ℝ) : Vec d) +
        root (Pi.single j (1 : ℝ) : Vec d)), ?_, ?_⟩
  · refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    have h1 := hroot0 ((Pi.single i (1 : ℝ) : Vec d) +
      (Pi.single j (1 : ℝ) : Vec d))
    have h2 := hroot0 (Pi.single i (1 : ℝ) : Vec d)
    have h3 := hroot0 (Pi.single j (1 : ℝ) : Vec d)
    linarith
  · intro R
    have hcpfmem : ∀ u : Vec d, MemLp
        (fun omega => cutoffProbeForm M L alpha R omega u)
        (ENNReal.ofReal xi) M.P.toMeasure :=
      fun u => memLp_cutoffResponseOnCube M L _ _ _ hxi
    have hbound : ∀ u : Vec d,
        lpMoment M.P.toMeasure xi
          (fun omega => cutoffProbeForm M L alpha R omega u) ≤ root u := by
      intro u
      rw [lpMoment_cutoffProbeForm_eq M L alpha R u xi, hroot]
      exact Real.rpow_le_rpow
        (integral_nonneg fun omega =>
          Real.rpow_nonneg (cutoffProbeForm_nonneg M L alpha R omega u) _)
        (hBu u R) (by positivity)
    have hijmem : ∀ i j : Fin d, MemLp (fun omega => (1 / 2 : ℝ) *
        (cutoffProbeForm M L alpha R omega
            ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)) +
          cutoffProbeForm M L alpha R omega (Pi.single i (1 : ℝ) : Vec d) +
          cutoffProbeForm M L alpha R omega (Pi.single j (1 : ℝ) : Vec d)))
        (ENNReal.ofReal xi) M.P.toMeasure :=
      fun i j => (((hcpfmem _).add (hcpfmem _)).add (hcpfmem _)).const_mul _
    have himem : ∀ i : Fin d, MemLp (fun omega => ∑ j : Fin d, (1 / 2 : ℝ) *
        (cutoffProbeForm M L alpha R omega
            ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)) +
          cutoffProbeForm M L alpha R omega (Pi.single i (1 : ℝ) : Vec d) +
          cutoffProbeForm M L alpha R omega (Pi.single j (1 : ℝ) : Vec d)))
        (ENNReal.ofReal xi) M.P.toMeasure :=
      fun i => memLp_finset_sum _ fun j _ => hijmem i j
    have houter := lpMoment_finsetSum_le (mu := M.P.toMeasure)
      (Finset.univ : Finset (Fin d))
      (F := fun i omega => ∑ j : Fin d, (1 / 2 : ℝ) *
        (cutoffProbeForm M L alpha R omega
            ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)) +
          cutoffProbeForm M L alpha R omega (Pi.single i (1 : ℝ) : Vec d) +
          cutoffProbeForm M L alpha R omega (Pi.single j (1 : ℝ) : Vec d)))
      hxi (fun i _ => himem i)
    refine le_trans houter ?_
    refine Finset.sum_le_sum fun i _ => ?_
    have hinner := lpMoment_finsetSum_le (mu := M.P.toMeasure)
      (Finset.univ : Finset (Fin d))
      (F := fun j omega => (1 / 2 : ℝ) *
        (cutoffProbeForm M L alpha R omega
            ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)) +
          cutoffProbeForm M L alpha R omega (Pi.single i (1 : ℝ) : Vec d) +
          cutoffProbeForm M L alpha R omega (Pi.single j (1 : ℝ) : Vec d)))
      hxi (fun j _ => hijmem i j)
    refine le_trans hinner ?_
    refine Finset.sum_le_sum fun j _ => ?_
    have hhalf : lpMoment M.P.toMeasure xi (fun omega => (1 / 2 : ℝ) *
        (cutoffProbeForm M L alpha R omega
            ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)) +
          cutoffProbeForm M L alpha R omega (Pi.single i (1 : ℝ) : Vec d) +
          cutoffProbeForm M L alpha R omega (Pi.single j (1 : ℝ) : Vec d))) =
        (1 / 2 : ℝ) * lpMoment M.P.toMeasure xi (fun omega =>
          cutoffProbeForm M L alpha R omega
              ((Pi.single i (1 : ℝ) : Vec d) +
                (Pi.single j (1 : ℝ) : Vec d)) +
            cutoffProbeForm M L alpha R omega (Pi.single i (1 : ℝ) : Vec d) +
            cutoffProbeForm M L alpha R omega
              (Pi.single j (1 : ℝ) : Vec d)) := by
      rw [lpMoment_const_mul hxi0]
      norm_num
    rw [hhalf]
    have hadd12 : MemLp (fun omega =>
        cutoffProbeForm M L alpha R omega
            ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)) +
          cutoffProbeForm M L alpha R omega (Pi.single i (1 : ℝ) : Vec d))
        (ENNReal.ofReal xi) M.P.toMeasure := (hcpfmem _).add (hcpfmem _)
    have htri1 := lpMoment_add_le (mu := M.P.toMeasure) hxi hadd12
      (hcpfmem (Pi.single j (1 : ℝ) : Vec d))
    have htri2 := lpMoment_add_le (mu := M.P.toMeasure) hxi
      (hcpfmem ((Pi.single i (1 : ℝ) : Vec d) + (Pi.single j (1 : ℝ) : Vec d)))
      (hcpfmem (Pi.single i (1 : ℝ) : Vec d))
    have hb1 := hbound ((Pi.single i (1 : ℝ) : Vec d) +
      (Pi.single j (1 : ℝ) : Vec d))
    have hb2 := hbound (Pi.single i (1 : ℝ) : Vec d)
    have hb3 := hbound (Pi.single j (1 : ℝ) : Vec d)
    linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge
