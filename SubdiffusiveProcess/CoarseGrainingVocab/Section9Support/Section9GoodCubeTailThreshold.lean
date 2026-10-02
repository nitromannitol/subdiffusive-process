import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeTailGauge
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeEllipticPackage




set_option autoImplicit false

open MeasureTheory ProbabilityTheory Homogenization Set
open Homogenization.IndependentSums
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.Section9 (centeredAxisCube)

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open SubdiffusiveProcess.Frozen.Assumptions

variable {d : ℕ}

/-! ## The per-shell cover depth, deviation and threshold -/

/-- The cover depth shell `k` needs on the native box of side `3^n`: the box is
`3^{n-k}` wavelengths wide, so one extra triadic step covers it. -/
def shellCoverDepth (n k : ℕ) : ℤ := ((n - k : ℕ) : ℤ) + 1

/-- The deviation at which shell `k` is tested.  The excess `n - k` over the
common index `tailIndex M` is what makes the union bound over the `n+1` shells
converge geometrically, uniformly in `n`. -/
def shellDeviation (M : GMCModel d) (n k : ℕ) : ℝ :=
  Real.sqrt (tailIndex M ^ 2 + ((n - k : ℕ) : ℝ))

theorem one_le_shellDeviation (M : GMCModel d) (n k : ℕ) :
    1 ≤ shellDeviation M n k := by
  have h1 : (1 : ℝ) ≤ tailIndex M ^ 2 := by
    have := one_le_tailIndex M
    nlinarith
  have h2 : (1 : ℝ) ≤ tailIndex M ^ 2 + ((n - k : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ ((n - k : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  rw [shellDeviation]
  exact Real.one_le_sqrt.mpr h2

theorem shellDeviation_sq (M : GMCModel d) (n k : ℕ) :
    shellDeviation M n k ^ 2 = tailIndex M ^ 2 + ((n - k : ℕ) : ℝ) := by
  have hnn : (0 : ℝ) ≤ tailIndex M ^ 2 + ((n - k : ℕ) : ℝ) := by positivity
  rw [shellDeviation, Real.sq_sqrt hnn]



def logLipschitzThreshold (M : GMCModel d) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    ((3 : ℝ) ^ k)⁻¹ *
      (coverEntropyScale M (shellCoverDepth n k) * shellDeviation M n k)

theorem logLipschitzThreshold_nonneg (M : GMCModel d) (n : ℕ) :
    0 ≤ logLipschitzThreshold M n := by
  refine Finset.sum_nonneg fun k _ => ?_
  have h1 : (0 : ℝ) ≤ ((3 : ℝ) ^ k)⁻¹ := by positivity
  have h2 : (0 : ℝ) ≤ coverEntropyScale M (shellCoverDepth n k) :=
    coverEntropyScale_nonneg M _
  have h3 : (0 : ℝ) ≤ shellDeviation M n k :=
    le_trans zero_le_one (one_le_shellDeviation M n k)
  exact mul_nonneg h1 (mul_nonneg h2 h3)

/-! ## The geometry of the layer-zero box -/

theorem goodCubeCentre_zero_lattice (n : ℕ) :
    goodCubeCentre n (0 : Lattice d) = (0 : Vec d) := by
  funext i
  simp [goodCubeCentre]

/-- The layer-zero observation box, as a closed ball centred at the origin. -/
theorem nativeBox_one_subset_closedBall (n : ℕ) :
    nativeBox n 1 (0 : Lattice d) ⊆
      Metric.closedBall (0 : Vec d) ((3 : ℝ) ^ n / 2) := by
  intro x hx
  have h : x ∈ centeredAxisCube (goodCubeCentre n (0 : Lattice d)) (1 * (3 : ℝ) ^ n) := hx
  rw [goodCubeCentre_zero_lattice, one_mul] at h
  exact centeredAxisCube_subset_closedBall (0 : Vec d) (by positivity) h

/-! ## The per-shell gradient readout on the layer-zero box -/

/-- The gradient of shell `k ≤ n` on the layer-zero box, read off the cover at
depth `n - k + 1`.  Unlike the layer events `j ≥ 1`, the box is *wider* than the
wavelength, and the depth is what absorbs the excess. -/
theorem norm_deriv_shell_le_coverShellG2 {n k : ℕ} (hk : k ≤ n)
    (omega : PotentialSample d) {w : Vec d}
    (hw : w ∈ Metric.closedBall (0 : Vec d) ((3 : ℝ) ^ n / 2)) :
    ‖PotentialField.deriv (omega k) w‖ ≤
      ((3 : ℝ) ^ k)⁻¹ * coverShellG2 k (0 : Vec d) (shellCoverDepth n k) omega := by
  have hpow : (3 : ℝ) ^ k * (3 : ℝ) ^ (shellCoverDepth n k) = (3 : ℝ) ^ (n + 1) := by
    rw [shellCoverDepth, ← zpow_natCast (3 : ℝ) k,
      ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), ← zpow_natCast (3 : ℝ) (n + 1)]
    congr 1
    have : ((n - k : ℕ) : ℤ) = (n : ℤ) - (k : ℤ) := by
      omega
    push_cast [this]
    ring
  have hgeom : 2 * ((3 : ℝ) ^ n / 2) < (3 : ℝ) ^ k * (3 : ℝ) ^ (shellCoverDepth n k) := by
    rw [hpow]
    have h1 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
    have : (3 : ℝ) ^ (n + 1) = 3 * (3 : ℝ) ^ n := by ring
    rw [this]
    linarith
  have hbox := boxDerivNorm_le_coverShellG2 (d := d) hgeom omega (0 : Vec d)
    (K := Metric.closedBall (0 : Vec d) ((3 : ℝ) ^ n / 2)) (subset_refl _)
  rw [smul_zero] at hbox
  refine le_trans ?_ hbox
  exact le_supWithZero
    (bddAbove_boxDerivNorm_family Metric.isBounded_closedBall (omega k)) ⟨w, hw⟩

/-- The shell increment on the layer-zero box, by the mean value inequality. -/
theorem abs_shell_sub_le_coverShellG2 {n k : ℕ} (hk : k ≤ n)
    (omega : PotentialSample d) {x y : Vec d}
    (hx : x ∈ Metric.closedBall (0 : Vec d) ((3 : ℝ) ^ n / 2))
    (hy : y ∈ Metric.closedBall (0 : Vec d) ((3 : ℝ) ^ n / 2)) :
    |omega k y - omega k x| ≤
      ((3 : ℝ) ^ k)⁻¹ * coverShellG2 k (0 : Vec d) (shellCoverDepth n k) omega *
        ‖y - x‖ := by
  have hmean := (convex_closedBall (0 : Vec d) ((3 : ℝ) ^ n / 2)).norm_image_sub_le_of_norm_fderiv_le
    (f := fun z : Vec d => omega k z)
    (fun z _ => ((omega k).hasFDerivAt z).differentiableAt)
    (fun z hz => by
      rw [((omega k).hasFDerivAt z).fderiv]
      exact norm_deriv_shell_le_coverShellG2 hk omega hz)
    hx hy
  rwa [Real.norm_eq_abs] at hmean

/-! ## The log-Lipschitz bad predicate -/

/-- The failure of the log-Lipschitz bound at rate `Θ` on the layer-zero box.
This is a property of the restricted coefficient observation alone, hence a
legitimate raw bad predicate for the frozen clause 7a. -/
def badLogLipschitz (d n : ℕ) (Theta : ℝ) :
    Set (nativeBox n 1 (0 : Lattice d) → ℝ) :=
  {f | ¬ ∀ x y : nativeBox n (1 : ℝ) (0 : Lattice d),
    f x ≤ Real.exp (Theta * ‖x.1 - y.1‖) * f y}



def goodCubeBad (M : GMCModel d) (n : ℕ) :
    Set (nativeBox n 1 (0 : Lattice d) → ℝ) :=
  badLogLipschitz d n (logLipschitzThreshold M n)

/-- **The deterministic core.**  If every shell `k ≤ n` has its covering gauge
below its own threshold, then `log a_n` is Lipschitz on the layer-zero box with
constant `logLipschitzThreshold M n`. -/
theorem aCutoff_le_exp_mul_of_forall_coverShellG2_le (M : GMCModel d) (n : ℕ)
    (omega : PotentialSample d)
    (h : ∀ k ∈ Finset.range (n + 1),
      coverShellG2 k (0 : Vec d) (shellCoverDepth n k) omega ≤
        coverEntropyScale M (shellCoverDepth n k) * shellDeviation M n k)
    {x y : Vec d}
    (hx : x ∈ Metric.closedBall (0 : Vec d) ((3 : ℝ) ^ n / 2))
    (hy : y ∈ Metric.closedBall (0 : Vec d) ((3 : ℝ) ^ n / 2)) :
    aCutoff M n omega x ≤
      Real.exp (logLipschitzThreshold M n * ‖x - y‖) * aCutoff M n omega y := by
  set S : Vec d → ℝ := fun w =>
    ∑ k ∈ Finset.range (n + 1), (omega k w - tauSq M.P) with hS
  have hgap : S x - S y ≤ logLipschitzThreshold M n * ‖x - y‖ := by
    have hsub : S x - S y = ∑ k ∈ Finset.range (n + 1), (omega k x - omega k y) := by
      rw [hS]
      simp only
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have habs : |∑ k ∈ Finset.range (n + 1), (omega k x - omega k y)| ≤
        ∑ k ∈ Finset.range (n + 1), |omega k x - omega k y| :=
      Finset.abs_sum_le_sum_abs _ _
    have hterm : ∀ k ∈ Finset.range (n + 1),
        |omega k x - omega k y| ≤
          ((3 : ℝ) ^ k)⁻¹ *
            (coverEntropyScale M (shellCoverDepth n k) * shellDeviation M n k) *
            ‖x - y‖ := by
      intro k hkmem
      have hk : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkmem)
      have hstep := abs_shell_sub_le_coverShellG2 hk omega hy hx
      refine hstep.trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_left (h k hkmem) (by positivity)
    have hsum : ∑ k ∈ Finset.range (n + 1), |omega k x - omega k y| ≤
        logLipschitzThreshold M n * ‖x - y‖ := by
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [logLipschitzThreshold, Finset.sum_mul]
    rw [hsub]
    exact le_trans (le_abs_self _) (habs.trans hsum)
  have hexp : Real.exp (S x) ≤ Real.exp (logLipschitzThreshold M n * ‖x - y‖ + S y) :=
    Real.exp_le_exp.mpr (by linarith)
  calc aCutoff M n omega x = Real.exp (S x) := rfl
    _ ≤ Real.exp (logLipschitzThreshold M n * ‖x - y‖ + S y) := hexp
    _ = Real.exp (logLipschitzThreshold M n * ‖x - y‖) * aCutoff M n omega y := by
        rw [Real.exp_add]
        rfl

/-- **The layer-zero pathwise inclusion.**  The concrete bad predicate is
covered by the `n + 1` per-shell gauge events. -/
theorem observation_goodCubeBad_subset (M : GMCModel d) (n : ℕ) :
    restrictedCoefficientObservation (aCutoff M n) (nativeBox n 1 (0 : Lattice d)) ⁻¹'
        goodCubeBad M n ⊆
      ⋃ k ∈ Finset.range (n + 1),
        upperTailEvent (coverShellG2 k (0 : Vec d) (shellCoverDepth n k))
          (coverEntropyScale M (shellCoverDepth n k) * shellDeviation M n k) := by
  intro omega homega
  by_contra hnot
  refine homega ?_
  have h : ∀ k ∈ Finset.range (n + 1),
      coverShellG2 k (0 : Vec d) (shellCoverDepth n k) omega ≤
        coverEntropyScale M (shellCoverDepth n k) * shellDeviation M n k := by
    intro k hk
    by_contra hlt
    exact hnot (Set.mem_iUnion₂.mpr ⟨k, hk, not_le.mp hlt⟩)
  intro x y
  exact aCutoff_le_exp_mul_of_forall_coverShellG2_le M n omega h
    (nativeBox_one_subset_closedBall n x.2) (nativeBox_one_subset_closedBall n y.2)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
