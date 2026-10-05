module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingInductionBallFailure
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingCrossingMeasurableEvent

@[expose] public section

/-!
# The scale-graded crossing estimate

Combining the deterministic reach bound
(`not_repairedStoppingShortCrossing_of_scaleCap`) with the failure-tail union
bound of `StoppingInductionBallFailure.lean` gives a geometric measure bound
for the fixed-code short-crossing event at bracket `k`, valid for every
threshold `j` with `j + 5 ≤ k`, provided the crossing width satisfies
`epsilon ≤ 3 ^ (-j) / 210`.

The two hypotheses interlock exactly as the manuscript's induction step does:
the deterministic step says that a crossing of `epsilon * 3 ^ k` cells to
radius `3 ^ k R` needs a cell of side at least `R / (210 epsilon)`, and the
probabilistic step says that a cell of side `3 ^ (base + j)` near the bracket
ball costs `q ^ j` times the number of scale-`(base + j)` cubes in that ball.
Since the ball has `≈ 3 ^ (k d)` such cubes, the product decays geometrically
in `k` only when `j` is a positive fraction of `k` — hence `epsilon` shrinks
with `k`.  A *fixed* `epsilon`, which is what the exterior row consumes, is
not obtainable from this union bound.

## Source

* `s.fixed.coefficient` and `mfd:sec-speed`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d] {Omega : Type*} {base : ℤ}

/-! ## 1. The deterministic exclusion -/

/-- **No large cell near the bracket ball forbids a short crossing.**

The threshold `j` enters twice: it caps the cell sides at `3 ^ (base + j)` and
it caps the crossing width at `3 ^ (-j) / 210`.  The gap `j + 5 ≤ k` is what
the reach bound's margin `2 R + 240 S ≤ 3 ^ k R` costs. -/
theorem not_repairedStoppingShortCrossing_of_not_mem_stoppingBallFailureTailEvent
    {failure : TriadicCube d → Set Omega} {omega : Omega}
    (hfinite : ∀ P : StoppingBaseCube d base,
      triadicFailureHeight failure omega P ≠ (⊤ : WithTop ℕ))
    (hinitial : LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q))
    (hrepair : LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
      cubeSet Q.1)
    (x0 : Vec d) {R epsilon : ℝ} {j k : ℕ}
    (hbase : (3 : ℝ) ^ base ≤ R) (hjk : j + 5 ≤ k)
    (heps : epsilon ≤ (3 : ℝ) ^ (-(j : ℤ)) / 210)
    (hgood : omega ∉ stoppingBallFailureTailEvent failure base x0
      ((3 : ℝ) ^ k * R) j) :
    ¬ RepairedStoppingShortCrossing
        (repairedStoppingSourceCells hinitial hrepair x0 R)
        (repairedStoppingSourceCells_nonempty hinitial hrepair x0
          (le_trans (le_of_lt (zpow_pos (by norm_num) base)) hbase))
        x0 R epsilon k := by
  set S : ℝ := (3 : ℝ) ^ (base + (j : ℤ)) with hS
  have hSpos : 0 < S := zpow_pos (by norm_num) _
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le (zpow_pos (by norm_num) base) hbase
  have hpowk : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hrhoR : R ≤ (3 : ℝ) ^ k * R := le_mul_of_one_le_left hRpos.le hpowk
  -- every cell whose centre is not too far has small scale
  have hscalecap : ∀ p : RefinedStoppingCell failure omega base,
      dist (refinedStoppingCenter p) x0 ≤
        (3 : ℝ) ^ k * R + 6 * (3 : ℝ) ^ refinedStoppingScale p →
        refinedStoppingScale p ≤ base + (j : ℤ) := by
    intro p hp
    by_contra hcon
    exact hgood (mem_stoppingBallFailureTailEvent_of_refinedStoppingCell hfinite
      x0 ((3 : ℝ) ^ k * R) j p (by omega) hp)
  have hcap : ∀ p : RefinedStoppingCell failure omega base,
      dist (refinedStoppingCenter p) x0 ≤ (3 : ℝ) ^ k * R →
        cubeScaleFactor (refinedStoppingFailureCube p) ≤ S := by
    intro p hp
    have hpow : (0 : ℝ) < (3 : ℝ) ^ refinedStoppingScale p :=
      zpow_pos (by norm_num) _
    have hle := hscalecap p (by linarith)
    show (3 : ℝ) ^ refinedStoppingScale p ≤ S
    exact zpow_le_zpow_right₀ (by norm_num) hle
  have hsrc : ∀ s ∈ repairedStoppingSourceCells hinitial hrepair x0 R,
      dist (refinedStoppingCenter s) x0 ≤ R + 3 / 2 * S := by
    intro s hs
    obtain ⟨z, hzcell, hzball⟩ :=
      (mem_repairedStoppingSourceCells_iff hinitial hrepair x0 R s).mp hs
    have hz := dist_refinedStoppingCenter_lt_of_mem_enlargement hzcell
    have hzR : dist z x0 ≤ R := Metric.mem_closedBall.mp hzball
    have htri : dist (refinedStoppingCenter s) x0 ≤
        dist (refinedStoppingCenter s) z + dist z x0 := dist_triangle _ _ _
    have hsf : cubeScaleFactor (refinedStoppingFailureCube s)
        = (3 : ℝ) ^ refinedStoppingScale s := rfl
    rw [hsf] at hz
    have hpow : (0 : ℝ) < (3 : ℝ) ^ refinedStoppingScale s :=
      zpow_pos (by norm_num) _
    have hle := hscalecap s (by linarith)
    have hside : (3 : ℝ) ^ refinedStoppingScale s ≤ S :=
      zpow_le_zpow_right₀ (by norm_num) hle
    linarith
  have hsmall : 210 * S * epsilon ≤ R := by
    have hSval : S * (3 : ℝ) ^ (-(j : ℤ)) = (3 : ℝ) ^ base := by
      rw [hS, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      norm_num
    have hstep : 210 * S * epsilon ≤ 210 * S * ((3 : ℝ) ^ (-(j : ℤ)) / 210) := by
      have : (0 : ℝ) < 210 * S := by linarith
      exact mul_le_mul_of_nonneg_left heps this.le
    have hfinal : 210 * S * ((3 : ℝ) ^ (-(j : ℤ)) / 210) = (3 : ℝ) ^ base := by
      rw [← hSval]
      ring
    rw [hfinal] at hstep
    linarith
  have hfar : 2 * R + 240 * S ≤ (3 : ℝ) ^ k * R := by
    have hSj : S ≤ (3 : ℝ) ^ j * R := by
      have hexp : S = (3 : ℝ) ^ base * (3 : ℝ) ^ (j : ℤ) := by
        rw [hS, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      have hjpos : (0 : ℝ) < (3 : ℝ) ^ (j : ℤ) := zpow_pos (by norm_num) _
      have hcast : (3 : ℝ) ^ (j : ℤ) = (3 : ℝ) ^ j := zpow_natCast 3 j
      rw [hexp, hcast]
      have : (3 : ℝ) ^ base * (3 : ℝ) ^ j ≤ R * (3 : ℝ) ^ j := by
        have hp : (0 : ℝ) ≤ (3 : ℝ) ^ j := by positivity
        exact mul_le_mul_of_nonneg_right hbase hp
      linarith [this]
    have hkj : (243 : ℝ) * (3 : ℝ) ^ j ≤ (3 : ℝ) ^ k := by
      have hle : (3 : ℝ) ^ (j + 5) ≤ (3 : ℝ) ^ k :=
        pow_le_pow_right₀ (by norm_num) hjk
      have hexp : (3 : ℝ) ^ (j + 5) = 243 * (3 : ℝ) ^ j := by
        rw [pow_add]; ring
      linarith [hexp ▸ hle]
    have hone : (1 : ℝ) ≤ (3 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    nlinarith [hSj, hkj, hone, hRpos]
  exact not_repairedStoppingShortCrossing_of_scaleCap hinitial hrepair _ _ x0
    hSpos hsrc hcap hsmall hfar

/-! ## 2. The measure bound for the fixed-code event -/

variable [MeasurableSpace Omega]

/-- **The scale-graded crossing estimate.**  For every threshold `j` at
distance at least `5` below the bracket `k`, and every crossing width
`epsilon ≤ 3 ^ (-j) / 210`, the fixed-code short-crossing event is contained,
up to a null set, in the failure tail above scale `base + j`. -/
theorem measure_repairedStoppingShortCrossingCodeEvent_le_of_scale_gap
    (mu : Measure Omega) (failure : TriadicCube d → Set Omega)
    (C q : ENNReal) (hC : C ≠ ∞) (hq : q < 1)
    (hmeasure : ∀ (P : TriadicCube d) (n : ℕ), P.scale = base + (n : ℤ) →
      mu (failure P) ≤ C * q ^ n)
    (x0 : Vec d) {R epsilon : ℝ} {j k : ℕ}
    (hbase : (3 : ℝ) ^ base ≤ R) (hjk : j + 5 ≤ k)
    (heps : epsilon ≤ (3 : ℝ) ^ (-(j : ℤ)) / 210) :
    mu (repairedStoppingShortCrossingCodeEvent failure base x0 R epsilon k) ≤
      ((2 * ⌈((3 : ℝ) ^ k * R + ‖x0‖) / (3 : ℝ) ^ base⌉₊ + 131) ^ d : ℕ) *
        (C * q ^ j) * (1 - q)⁻¹ := by
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le (zpow_pos (by norm_num) base) hbase
  have hpowk : (0 : ℝ) ≤ (3 : ℝ) ^ k := by positivity
  have hrho : (0 : ℝ) ≤ (3 : ℝ) ^ k * R := by positivity
  have hcert := ae_locallyFinite_stoppingCertificates_of_le_geometric
    (base := base) mu failure C q hC hq hmeasure
  have hfin := ae_forall_triadicFailureHeight_ne_top_of_le_geometric
    (base := base) mu failure C q hC hq
    (fun Q n ↦ hmeasure (ancestorCube n Q.1) n (by rw [ancestorCube_scale, Q.2]))
  have hsubset : repairedStoppingShortCrossingCodeEvent failure base x0 R
      epsilon k ≤ᵐ[mu]
      stoppingBallFailureTailEvent failure base x0 ((3 : ℝ) ^ k * R) j := by
    filter_upwards [hcert, hfin] with omega hcert hfin homega
    by_contra hcon
    have hcross := (mem_repairedStoppingShortCrossingCodeEvent_iff hcert.1
      hcert.2 x0 R epsilon hRpos.le k).mp homega
    exact not_repairedStoppingShortCrossing_of_not_mem_stoppingBallFailureTailEvent
      hfin hcert.1 hcert.2 x0 hbase hjk heps hcon hcross
  exact le_trans (measure_mono_ae hsubset)
    (measure_stoppingBallFailureTailEvent_le mu failure C q hmeasure x0
      ((3 : ℝ) ^ k * R) hrho j)

/-- **The scale-graded crossing estimate in geometric form.**

Taking the threshold `j` to be half the bracket turns the previous bound into
a genuine geometric decay in `k`, with ratio `3 ^ (2 d) * q`: the bracket ball
holds `≈ 3 ^ (k d)` cubes of the threshold scale, and each fails with
probability `q ^ (k / 2)`.  The price is that the admissible crossing width
`epsilon` shrinks like `3 ^ (-k / 2)`, which is exactly why this estimate does
**not** close the exterior row: that row needs one `epsilon` for all large `k`
(its decay constant is `c ≤ epsilon * log 2 / 3`). -/
theorem measure_repairedStoppingShortCrossingCodeEvent_le_geometric
    (mu : Measure Omega) (failure : TriadicCube d → Set Omega)
    (C q : ENNReal) (hC : C ≠ ∞) (hq : q < 1)
    (hmeasure : ∀ (P : TriadicCube d) (n : ℕ), P.scale = base + (n : ℤ) →
      mu (failure P) ≤ C * q ^ n)
    (x0 : Vec d) {R epsilon : ℝ} {k : ℕ}
    (hbase : (3 : ℝ) ^ base ≤ R) (hR : R ≤ (3 : ℝ) ^ (base + 1))
    (hk : 10 ≤ k)
    (heps : epsilon ≤ (3 : ℝ) ^ (-((k / 2 : ℕ) : ℤ)) / 210) :
    mu (repairedStoppingShortCrossingCodeEvent failure base x0 R epsilon k) ≤
      (((2 * ⌈‖x0‖ / (3 : ℝ) ^ base⌉₊ + 137) ^ d * 3 ^ d : ℕ) : ENNReal) *
        (C * ((3 : ENNReal) ^ (2 * d) * q) ^ (k / 2)) * (1 - q)⁻¹ := by
  set j : ℕ := k / 2 with hj
  set A : ℕ := ⌈‖x0‖ / (3 : ℝ) ^ base⌉₊ with hA
  have hjk : j + 5 ≤ k := by omega
  have hstep := measure_repairedStoppingShortCrossingCodeEvent_le_of_scale_gap
    mu failure C q hC hq hmeasure x0 hbase hjk heps
  -- the cube count of the bracket ball
  have hbasepos : (0 : ℝ) < (3 : ℝ) ^ base := zpow_pos (by norm_num) _
  have hceil : ⌈((3 : ℝ) ^ k * R + ‖x0‖) / (3 : ℝ) ^ base⌉₊ ≤ 3 * 3 ^ k + A := by
    have hnum : ((3 : ℝ) ^ k * R + ‖x0‖) / (3 : ℝ) ^ base ≤
        (3 * 3 ^ k : ℕ) + ‖x0‖ / (3 : ℝ) ^ base := by
      rw [div_le_iff₀ hbasepos]
      have h1 : (3 : ℝ) ^ k * R ≤ (3 * 3 ^ k : ℕ) * (3 : ℝ) ^ base := by
        have hR' : R ≤ 3 * (3 : ℝ) ^ base := by
          rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one] at hR
          linarith
        have hp : (0 : ℝ) ≤ (3 : ℝ) ^ k := by positivity
        have : (3 : ℝ) ^ k * R ≤ (3 : ℝ) ^ k * (3 * (3 : ℝ) ^ base) := by
          exact mul_le_mul_of_nonneg_left hR' hp
        push_cast
        linarith
      have h2 : ‖x0‖ / (3 : ℝ) ^ base * (3 : ℝ) ^ base = ‖x0‖ := by
        field_simp
      nlinarith [h1, h2]
    calc ⌈((3 : ℝ) ^ k * R + ‖x0‖) / (3 : ℝ) ^ base⌉₊
        ≤ ⌈(3 * 3 ^ k : ℕ) + ‖x0‖ / (3 : ℝ) ^ base⌉₊ := Nat.ceil_le_ceil hnum
      _ = 3 * 3 ^ k + A := by
          rw [add_comm, Nat.ceil_add_natCast
            (by positivity : (0 : ℝ) ≤ ‖x0‖ / (3 : ℝ) ^ base), hA]
          omega
  have hcount : (2 * ⌈((3 : ℝ) ^ k * R + ‖x0‖) / (3 : ℝ) ^ base⌉₊ + 131) ^ d ≤
      (2 * A + 137) ^ d * 3 ^ (k * d) := by
    have hone : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
    have hlin : 2 * ⌈((3 : ℝ) ^ k * R + ‖x0‖) / (3 : ℝ) ^ base⌉₊ + 131 ≤
        (2 * A + 137) * 3 ^ k := by
      have : 2 * (3 * 3 ^ k + A) + 131 ≤ (2 * A + 137) * 3 ^ k := by
        nlinarith [hone]
      omega
    calc (2 * ⌈((3 : ℝ) ^ k * R + ‖x0‖) / (3 : ℝ) ^ base⌉₊ + 131) ^ d
        ≤ ((2 * A + 137) * 3 ^ k) ^ d := Nat.pow_le_pow_left hlin d
      _ = (2 * A + 137) ^ d * 3 ^ (k * d) := by
          rw [Nat.mul_pow, ← pow_mul]
  refine le_trans hstep ?_
  have hcast : (((2 * ⌈((3 : ℝ) ^ k * R + ‖x0‖) / (3 : ℝ) ^ base⌉₊ + 131) ^ d : ℕ)
      : ENNReal) ≤ (((2 * A + 137) ^ d * 3 ^ (k * d) : ℕ) : ENNReal) :=
    Nat.cast_le.mpr hcount
  have hpowsplit : (3 : ENNReal) ^ (k * d) * q ^ j ≤
      (3 : ENNReal) ^ d * ((3 : ENNReal) ^ (2 * d) * q) ^ j := by
    rw [mul_pow, ← pow_mul]
    have hk2 : k ≤ 1 + 2 * j := by omega
    have hexp : k * d ≤ d + 2 * d * j := by
      calc k * d ≤ (1 + 2 * j) * d := Nat.mul_le_mul_right d hk2
        _ = d + 2 * d * j := by ring
    calc (3 : ENNReal) ^ (k * d) * q ^ j
        ≤ (3 : ENNReal) ^ (d + 2 * d * j) * q ^ j := by
          exact mul_le_mul'
            (pow_le_pow_right₀ (by norm_num : (1 : ENNReal) ≤ 3) hexp) le_rfl
      _ = (3 : ENNReal) ^ d * (3 : ENNReal) ^ (2 * d * j) * q ^ j := by
          rw [pow_add]
      _ = (3 : ENNReal) ^ d * ((3 : ENNReal) ^ (2 * d * j) * q ^ j) := by
          rw [mul_assoc]
  calc (((2 * ⌈((3 : ℝ) ^ k * R + ‖x0‖) / (3 : ℝ) ^ base⌉₊ + 131) ^ d : ℕ) : ENNReal) *
        (C * q ^ j) * (1 - q)⁻¹
      ≤ (((2 * A + 137) ^ d * 3 ^ (k * d) : ℕ) : ENNReal) *
          (C * q ^ j) * (1 - q)⁻¹ := by gcongr
    _ = (((2 * A + 137) ^ d : ℕ) : ENNReal) * C *
          ((3 : ENNReal) ^ (k * d) * q ^ j) * (1 - q)⁻¹ := by
        push_cast
        ring
    _ ≤ (((2 * A + 137) ^ d : ℕ) : ENNReal) * C *
          ((3 : ENNReal) ^ d * ((3 : ENNReal) ^ (2 * d) * q) ^ j) * (1 - q)⁻¹ := by
        gcongr
    _ = (((2 * A + 137) ^ d * 3 ^ d : ℕ) : ENNReal) *
          (C * ((3 : ENNReal) ^ (2 * d) * q) ^ j) * (1 - q)⁻¹ := by
        push_cast
        ring


end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
