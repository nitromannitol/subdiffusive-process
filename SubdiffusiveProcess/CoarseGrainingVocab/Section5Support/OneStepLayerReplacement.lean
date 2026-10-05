module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCellEnergy
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletEnergyContinuity

@[expose] public section

/-!
# Deterministic layer replacement and quadratic-error bounds

This module isolates the pointwise algebra in Step 3 of the one-step upper
proof (paper label `l.one.step.upper`).  The first estimate compares a cellwise
constant slope energy with the literal exponentially weighted field.  The
second controls the nonlinear remainder after the corrector is split into its
linear and higher-order pieces.

The stochastic Holder estimates, fresh-shell independence, and cell-average
aggregation are intentionally downstream.  The statements here contain no
probabilistic assumptions and expose exactly the quantities those arguments
must estimate.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- The real exponential is locally Lipschitz with the sharp segment
envelope. -/
theorem abs_exp_sub_exp_le_exp_max_mul_abs_sub (s t : ℝ) :
    |Real.exp s - Real.exp t| ≤
      Real.exp (max s t) * |s - t| := by
  wlog hst : s ≤ t generalizing s t
  · have hts : t ≤ s := le_of_not_ge hst
    simpa [abs_sub_comm, max_comm] using this t s hts
  have hu0 : 0 ≤ t - s := sub_nonneg.mpr hst
  have hexpOrder : Real.exp s ≤ Real.exp t := Real.exp_le_exp.mpr hst
  have hrem : Real.exp (t - s) - 1 ≤ (t - s) * Real.exp (t - s) := by
    have hbase := Real.add_one_le_exp (s - t)
    have hmul := mul_le_mul_of_nonneg_right hbase (Real.exp_pos (t - s)).le
    rw [← Real.exp_add] at hmul
    have hz : s - t + (t - s) = 0 := by ring
    rw [hz, Real.exp_zero] at hmul
    linarith
  have hid : Real.exp t - Real.exp s =
      Real.exp s * (Real.exp (t - s) - 1) := by
    rw [mul_sub, ← Real.exp_add]
    ring_nf
  rw [abs_sub_comm (Real.exp s) (Real.exp t),
    abs_of_nonneg (sub_nonneg.mpr hexpOrder), hid,
    max_eq_right hst, abs_sub_comm s t,
    abs_of_nonneg (sub_nonneg.mpr hst)]
  calc
    Real.exp s * (Real.exp (t - s) - 1) ≤
        Real.exp s * ((t - s) * Real.exp (t - s)) :=
      mul_le_mul_of_nonneg_left hrem (Real.exp_pos s).le
    _ = (t - s) * (Real.exp s * Real.exp (t - s)) := by ring
    _ = (t - s) * Real.exp t := by
      rw [← Real.exp_add]
      congr 2
      ring
    _ = Real.exp t * (t - s) := by ring

/-- Pointwise replacement estimate behind
paper label `l.one.step.upper`.  Here `p` is the cell mean, `F` its centered
fluctuation, and `s,t` are the cell supremum and pointwise shell values. -/
theorem oneStep_exp_cellEnergy_replacement {d : ℕ}
    (s t : ℝ) (p F : Vec d) :
    |Real.exp s * vecNormSq p -
        Real.exp t * vecNormSq (p + F)| ≤
      Real.exp (max s t) *
        (|s - t| * vecNormSq p +
          Real.sqrt (vecNormSq F) *
            Real.sqrt (vecNormSq (p + (p + F)))) := by
  have hExp0 : 0 ≤ Real.exp t := (Real.exp_pos t).le
  have hMax0 : 0 ≤ Real.exp (max s t) := (Real.exp_pos _).le
  have htmax : Real.exp t ≤ Real.exp (max s t) :=
    Real.exp_le_exp.mpr (le_max_right s t)
  have hsplit : Real.exp s * vecNormSq p -
      Real.exp t * vecNormSq (p + F) =
      (Real.exp s - Real.exp t) * vecNormSq p +
        Real.exp t * (vecNormSq p - vecNormSq (p + F)) := by ring
  have hnorm :
      |vecNormSq p - vecNormSq (p + F)| ≤
        Real.sqrt (vecNormSq F) *
          Real.sqrt (vecNormSq (p + (p + F))) := by
    rw [vecNormSq_sub_vecNormSq]
    have hdiff : p - (p + F) = -F := by
      ext i
      simp
    rw [hdiff]
    have hnegSq : vecNormSq (-F) = vecNormSq F := by
      simp only [vecNormSq, vecDot, Pi.neg_apply]
      congr 1
      funext i
      ring
    simpa only [hnegSq] using
      abs_vecDot_le_sqrt_mul_sqrt (-F) (p + (p + F))
  rw [hsplit]
  calc
    |(Real.exp s - Real.exp t) * vecNormSq p +
        Real.exp t * (vecNormSq p - vecNormSq (p + F))| ≤
        |Real.exp s - Real.exp t| * vecNormSq p +
          Real.exp t * |vecNormSq p - vecNormSq (p + F)| := by
      calc
        _ ≤ |(Real.exp s - Real.exp t) * vecNormSq p| +
              |Real.exp t * (vecNormSq p - vecNormSq (p + F))| :=
          abs_add_le _ _
        _ = _ := by
          rw [abs_mul, abs_mul, abs_of_nonneg (vecNormSq_nonneg p),
            abs_of_nonneg hExp0]
    _ ≤ (Real.exp (max s t) * |s - t|) * vecNormSq p +
          Real.exp (max s t) *
            (Real.sqrt (vecNormSq F) *
              Real.sqrt (vecNormSq (p + (p + F)))) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right
          (abs_exp_sub_exp_le_exp_max_mul_abs_sub s t)
          (vecNormSq_nonneg p))
        (mul_le_mul htmax hnorm (abs_nonneg _) hMax0)
    _ = Real.exp (max s t) *
        (|s - t| * vecNormSq p +
          Real.sqrt (vecNormSq F) *
            Real.sqrt (vecNormSq (p + (p + F)))) := by ring

/-- Exact algebraic split of the nonlinear weighted-energy error. -/
theorem oneStep_quadraticError_identity {d : ℕ}
    (v r : Vec d) (s : ℝ) :
    vecNormSq (v + r) * (Real.exp s - 1) - vecNormSq v * s =
      (vecNormSq (v + r) - vecNormSq v) * s +
        vecNormSq (v + r) * (Real.exp s - 1 - s) := by
  ring

/-- Quadratic-error estimate used after `w = v + wbar`.  On the small
Taylor range, the nonlinear exponential remainder is quadratic and the
change of square energy is controlled by one Euclidean Cauchy--Schwarz
factor. -/
theorem abs_oneStep_quadraticError_le {d : ℕ}
    (v r : Vec d) {s : ℝ} (hs : |s| ≤ 1) :
    |vecNormSq (v + r) * (Real.exp s - 1) - vecNormSq v * s| ≤
      Real.sqrt (vecNormSq r) *
          Real.sqrt (vecNormSq ((v + r) + v)) * |s| +
        vecNormSq (v + r) * s ^ 2 := by
  rw [oneStep_quadraticError_identity]
  have hnorm :
      |vecNormSq (v + r) - vecNormSq v| ≤
        Real.sqrt (vecNormSq r) *
          Real.sqrt (vecNormSq ((v + r) + v)) := by
    rw [vecNormSq_sub_vecNormSq]
    have hdiff : (v + r) - v = r := by
      ext i
      simp
    rw [hdiff]
    exact abs_vecDot_le_sqrt_mul_sqrt r ((v + r) + v)
  have hrem := Real.abs_exp_sub_one_sub_id_le hs
  calc
    |(vecNormSq (v + r) - vecNormSq v) * s +
        vecNormSq (v + r) * (Real.exp s - 1 - s)| ≤
        |vecNormSq (v + r) - vecNormSq v| * |s| +
          vecNormSq (v + r) * |Real.exp s - 1 - s| := by
      calc
        _ ≤ |(vecNormSq (v + r) - vecNormSq v) * s| +
              |vecNormSq (v + r) * (Real.exp s - 1 - s)| :=
          abs_add_le _ _
        _ = _ := by
          rw [abs_mul, abs_mul,
            abs_of_nonneg (vecNormSq_nonneg (v + r))]
    _ ≤
        (Real.sqrt (vecNormSq r) *
          Real.sqrt (vecNormSq ((v + r) + v))) * |s| +
          vecNormSq (v + r) * s ^ 2 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hnorm (abs_nonneg s))
        (mul_le_mul_of_nonneg_left hrem (vecNormSq_nonneg (v + r)))
    _ = _ := by ring

/-- The spatial quadratic remainder used in the weighted-energy identity. -/
def oneStepQuadraticRemainderOn {d : ℕ} (U : Set (Vec d))
    (b : Vec d → ℝ) (G : Vec d → Vec d) : ℝ :=
  ∫ x in U, (b x - 1) * vecNormSq (G x) ∂MeasureTheory.volume

/-- Deterministic weighted-energy identity before taking expectation in the
fresh shell.  The first term becomes `volume(U) * |p|^2` after using
`E[exp H] = 1`; the remaining two terms are exactly those displayed at
paper label `l.one.step.upper`.

Only the two genuinely weighted remainders are assumed integrable.  All
unweighted gradient terms follow from the `H¹₀` carrier. -/
theorem oneStep_weightedDirichletEnergy_identity {d : ℕ}
    {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {b : Vec d → ℝ} {w : H10Function U} (p : Vec d)
    (hb0 : MeasureTheory.IntegrableOn (fun x => b x * vecNormSq p) U)
    (hcrossRem : MeasureTheory.IntegrableOn
      (fun x => (b x - 1) * vecDot p (w.toH1Function.grad x)) U)
    (hquadRem : MeasureTheory.IntegrableOn
      (fun x => (b x - 1) * vecNormSq (w.toH1Function.grad x)) U)
    (hw : IsZeroTraceDirichletRhsWeakSolution (identityCoeffField d) U w
      (fun x => -((b x - 1) • p))) :
    ∫ (x : Vec d) in U, b x * vecNormSq (p + w.toH1Function.grad x)
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Vec d)) =
      (∫ (x : Vec d) in U, b x * vecNormSq p
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Vec d))) -
        (∫ (x : Vec d) in U, vecNormSq (w.toH1Function.grad x)
          ∂(MeasureTheory.volume : MeasureTheory.Measure (Vec d))) +
        oneStepQuadraticRemainderOn U b w.toH1Function.grad := by
  unfold oneStepQuadraticRemainderOn
  let G : Vec d → Vec d := fun x => w.toH1Function.grad x
  have hGsq : MeasureTheory.IntegrableOn (fun x => vecNormSq (G x)) U :=
    integrableOn_vecNormSq_zeroTraceGrad w
  have hpG : MeasureTheory.IntegrableOn (fun x => vecDot p (G x)) U := by
    have hp : MemVectorL2 U (fun _ : Vec d => p) :=
      MeasureTheory.memLp_const p
    exact integrableOn_vecDot_of_memVectorL2 hp
      w.toH1Function.grad_memVectorL2
  have hbCross : MeasureTheory.IntegrableOn
      (fun x => b x * vecDot p (G x)) U := by
    have hEq : (fun x => b x * vecDot p (G x)) =
        fun x => vecDot p (G x) + (b x - 1) * vecDot p (G x) := by
      funext x
      ring
    rw [hEq]
    exact hpG.add hcrossRem
  have hbGsq : MeasureTheory.IntegrableOn
      (fun x => b x * vecNormSq (G x)) U := by
    have hEq : (fun x => b x * vecNormSq (G x)) =
        fun x => vecNormSq (G x) + (b x - 1) * vecNormSq (G x) := by
      funext x
      ring
    rw [hEq]
    exact hGsq.add hquadRem
  have hmean : ∫ x in U, vecDot p (G x) ∂volume = 0 := by
    simpa only [G] using integral_vecDot_const_zeroTraceGrad_eq_zero w p
  have hweak := hw w
  have henergy :
      ∫ x in U, vecNormSq (G x) ∂volume =
        -∫ x in U, (b x - 1) * vecDot p (G x) ∂volume := by
    calc
      ∫ x in U, vecNormSq (G x) ∂volume =
          ∫ x in U,
            vecDot (matVecMul (identityCoeffField d x) (G x)) (G x) ∂volume := by
        apply integral_congr_ae
        filter_upwards with x
        rw [matVecMul_identityCoeffField]
        rfl
      _ = ∫ x in U, vecDot (-((b x - 1) • p)) (G x) ∂volume := by
        simpa only [G] using hweak
      _ = -∫ x in U, (b x - 1) * vecDot p (G x) ∂volume := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards with x
        rw [vecDot_neg_left, vecDot_smul_left]
  have hbCrossEq :
      ∫ x in U, b x * vecDot p (G x) ∂volume =
        -∫ x in U, vecNormSq (G x) ∂volume := by
    have hEq : (fun x => b x * vecDot p (G x)) =
        fun x => vecDot p (G x) + (b x - 1) * vecDot p (G x) := by
      funext x
      ring
    rw [hEq, integral_add hpG hcrossRem, hmean, zero_add]
    linarith [henergy]
  have hbGsqEq :
      ∫ x in U, b x * vecNormSq (G x) ∂volume =
        (∫ x in U, vecNormSq (G x) ∂volume) +
          ∫ x in U, (b x - 1) * vecNormSq (G x) ∂volume := by
    have hEq : (fun x => b x * vecNormSq (G x)) =
        fun x => vecNormSq (G x) + (b x - 1) * vecNormSq (G x) := by
      funext x
      ring
    rw [hEq, integral_add hGsq hquadRem]
  have hpoint : (fun x => b x * vecNormSq (p + G x)) =
      fun x => b x * vecNormSq p +
        2 * (b x * vecDot p (G x)) + b x * vecNormSq (G x) := by
    funext x
    simp only [vecNormSq, vecDot_add_left, vecDot_add_right]
    rw [vecDot_comm (G x) p]
    ring
  have hsplitOuter :
      ∫ x in U, (b x * vecNormSq p + 2 * (b x * vecDot p (G x))) +
          b x * vecNormSq (G x) ∂volume =
        (∫ x in U, b x * vecNormSq p + 2 * (b x * vecDot p (G x)) ∂volume) +
          ∫ x in U, b x * vecNormSq (G x) ∂volume := by
    simpa only [Pi.add_apply] using
      integral_add (hb0.add (hbCross.const_mul 2)) hbGsq
  have hsplitInner :
      ∫ x in U, b x * vecNormSq p + 2 * (b x * vecDot p (G x)) ∂volume =
        (∫ x in U, b x * vecNormSq p ∂volume) +
          ∫ x in U, 2 * (b x * vecDot p (G x)) ∂volume := by
    simpa only [Pi.add_apply] using integral_add hb0 (hbCross.const_mul 2)
  change (∫ x in U, b x * vecNormSq (p + G x) ∂volume) = _
  rw [hpoint, hsplitOuter, hsplitInner, integral_const_mul,
    hbCrossEq, hbGsqEq]
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
