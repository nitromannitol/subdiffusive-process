module

public import SubdiffusiveProcess.Section10.PhysicalExitChainingTransport

@[expose] public section

/-!
Uniform quenched modulus from the actual strong-Markov lifetime kernel.

The successive-exit argument is the fixed-environment argument, `tight:prop-tightness`, Step 3. The Laplace-weight
bound controls the number of exits geometrically; a finite union bound then
controls short gaps. All numerical choices precede the law quantifier.
-/

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalExitChaining

theorem uniform_modulus_bound_of_local_exit {d : ℕ}
    (R r T K epsilon : ℝ)
    (hR : 0 < R) (hr : 0 < r) (hT : 0 < T)
    (hK : 0 ≤ K) (hepsilon : 0 < epsilon) :
    ∃ delta : ENNReal, 0 < delta ∧
      ∀ law : Kernel (Vec d) (Path d), StrongMarkov law →
        (∀ x : Vec d, ∀ᵐ w ∂law x, w.lifetime = ⊤) →
        (∀ t : ℝ, 0 < t → ∀ x ∈ Metric.ball (0 : Vec d) R,
          law x {w | LifetimePath.exitTime (Metric.ball x (r / 4)) w ≤ ENNReal.ofReal t} ≤
            ENNReal.ofReal (K * Real.sqrt t)) →
        ∀ x ∈ Metric.ball (0 : Vec d) R,
          (law x).map (LifetimePath.continuousPathExtension
            (ContinuousMap.const NNReal (0 : Vec d)))
            (ContinuousPath.modulusSet (Real.toNNReal T) delta (ENNReal.ofReal r))ᶜ ≤
              law x {w | LifetimePath.exitTime (Metric.ball (0 : Vec d) R) w ≤ ENNReal.ofReal T} +
                ENNReal.ofReal epsilon := by
  have hK1 : 0 < K + 1 := by linarith
  have hR1 : 0 < R + 1 := by linarith
  let a : ℝ := 1 / (8 * ((K + 1) * (R + 1)))
  have ha : 0 < a := by dsimp [a]; positivity
  let h0 : ℝ := a ^ 2
  have hh0 : 0 < h0 := by dsimp [h0]; positivity
  have hsqrt0 : Real.sqrt h0 = a := by
    dsimp only [h0]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos ha]
  have hsmall0 : K * Real.sqrt h0 ≤ 1 / 8 := by
    rw [hsqrt0]
    calc
      K * a ≤ ((K + 1) * (R + 1)) * a :=
        mul_le_mul_of_nonneg_right (by nlinarith) ha.le
      _ = 1 / 8 := by dsimp [a]; field_simp
  let h : ℝ := h0 / 2
  have hh : 0 < h := by dsimp [h]; positivity
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
    (16 * Real.exp (T / h) / epsilon) (by norm_num : (1 : ℝ) < 2)
  let b : ℝ := epsilon / (16 * ((n : ℝ) + 1) * (K + 1))
  have hb : 0 < b := by dsimp [b]; positivity
  let delta : ENNReal := ENNReal.ofReal (b ^ 2)
  let deltaN : NNReal := ⟨b ^ 2, sq_nonneg b⟩
  have hdelta : 0 < delta := ENNReal.ofReal_pos.mpr (by positivity)
  have hdeltaN : (deltaN : ENNReal) = delta := by
    exact (ENNReal.ofReal_eq_coe_nnreal (sq_nonneg b)).symm
  have hsqrtb : Real.sqrt (b ^ 2) = b := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hb]
  have hsmallb : K * Real.sqrt (b ^ 2) ≤ epsilon / (16 * ((n : ℝ) + 1)) := by
    rw [hsqrtb]
    calc
      K * b ≤ (K + 1) * b := mul_le_mul_of_nonneg_right (by linarith) hb.le
      _ = epsilon / (16 * ((n : ℝ) + 1)) := by dsimp [b]; field_simp
  have hgeometric : ENNReal.ofReal (Real.exp (T / h)) * ENNReal.ofReal (1 / 2 : ℝ) ^ n ≤
      ENNReal.ofReal (epsilon / 16) :=
    geometric_error_le hepsilon (Real.exp_pos _).le n hn
  have hgap : (n : ENNReal) * ENNReal.ofReal (epsilon / (16 * ((n : ℝ) + 1))) ≤
      ENNReal.ofReal (epsilon / 16) := short_gap_error_le hepsilon.le n
  refine ⟨delta, hdelta, ?_⟩
  intro law hSM hcons hlocal x hx
  let k := continuousKernel law
  let : IsMarkovKernel k := continuousKernel_isMarkov law hSM
  have hgamma : ∀ y ∈ Metric.ball (0 : Vec d) R,
      (∫⁻ p, exitWeight h (ContinuousPath.exitTime (Metric.ball y (r / 4)) p) ∂k y) ≤
        ENNReal.ofReal (1 / 2) := by
    intro y hy
    apply exitWeight_integral_le_half k y _ Metric.isOpen_ball h0 hh0
    rw [continuousKernel_exit law hcons y _ Metric.isOpen_ball]
    exact (hlocal h0 hh0 y hy).trans (ENNReal.ofReal_le_ofReal hsmall0)
  have hbeta : ∀ y ∈ Metric.ball (0 : Vec d) R,
      k y {p | ContinuousPath.exitTime (Metric.ball y (r / 4)) p ≤ (deltaN : ENNReal)} ≤
        ENNReal.ofReal (epsilon / (16 * ((n : ℝ) + 1))) := by
    intro y hy
    rw [hdeltaN, continuousKernel_exit law hcons y _ Metric.isOpen_ball]
    exact (hlocal (b ^ 2) (by positivity) y hy).trans (ENNReal.ofReal_le_ofReal hsmallb)
  have hbound := modulus_bound_of_restart_estimates k law
    (continuousKernel_attachment law hcons) hSM (continuousKernel_start law hSM hcons)
    (Metric.ball (0 : Vec d) R) Metric.isOpen_ball.measurableSet
    (by positivity : 0 < r / 4) (Real.toNNReal T) deltaN hh
    (ENNReal.ofReal (1 / 2)) hgamma
    (ENNReal.ofReal (epsilon / (16 * ((n : ℝ) + 1)))) hbeta n x
  have hmod : ContinuousPath.modulusSet (alpha := Vec d) (Real.toNNReal T)
      (deltaN : ENNReal) (ENNReal.ofReal (3 * (r / 4))) ⊆
      ContinuousPath.modulusSet (Real.toNNReal T) delta (ENNReal.ofReal r) := by
    rw [hdeltaN]
    exact ContinuousPath.modulusSet_mono (ENNReal.ofReal_le_ofReal (by linarith))
  have hcontain := continuousKernel_containment_le law hcons x R T
  have herror : ENNReal.ofReal (Real.exp ((Real.toNNReal T : ℝ) / h)) *
        ENNReal.ofReal (1 / 2 : ℝ) ^ n +
        (n : ENNReal) * ENNReal.ofReal (epsilon / (16 * ((n : ℝ) + 1))) ≤
      ENNReal.ofReal epsilon := by
    rw [Real.coe_toNNReal T hT.le]
    calc
      _ ≤ ENNReal.ofReal (epsilon / 16) + ENNReal.ofReal (epsilon / 16) :=
        add_le_add hgeometric hgap
      _ ≤ ENNReal.ofReal epsilon := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by linarith)
  rw [← continuousKernel_apply]
  calc
    _ ≤ k x (ContinuousPath.modulusSet (Real.toNNReal T) (deltaN : ENNReal)
        (ENNReal.ofReal (3 * (r / 4))))ᶜ := measure_mono (Set.compl_subset_compl.mpr hmod)
    _ ≤ _ := hbound
    _ ≤ law x {w | LifetimePath.exitTime (Metric.ball (0 : Vec d) R) w ≤ ENNReal.ofReal T} +
        ENNReal.ofReal epsilon := by
      rw [add_assoc]
      exact add_le_add hcontain herror

end SubdiffusiveProcess.Section10.PhysicalExitChaining
