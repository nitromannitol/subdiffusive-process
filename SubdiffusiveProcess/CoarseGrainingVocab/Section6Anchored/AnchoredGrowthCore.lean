import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.MeasurableEnvelope
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellSeries




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored

open Homogenization Homogenization.IndependentSums
open SubdiffusiveProcess.Frozen.Assumptions
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## The two geometric constants -/

/-- `∑_k 3^{-k} √(k+1)`: the price of the gradient series. -/
def gradSeriesConst : ℝ := geomSqrtConst (1 / 3)

/-- `∑_k (2/3)^k √(k+1)`: the price of the high-scale tail. -/
def tailSeriesConst : ℝ := geomSqrtConst (2 / 3)

theorem gradSeriesConst_nonneg : (0 : ℝ) ≤ gradSeriesConst :=
  geomSqrtConst_nonneg (by norm_num)

theorem tailSeriesConst_nonneg : (0 : ℝ) ≤ tailSeriesConst :=
  geomSqrtConst_nonneg (by norm_num)

theorem inv_pow_three_eq (k : ℕ) : (((3 : ℝ) ^ k)⁻¹) = (1 / 3 : ℝ) ^ k := by
  rw [one_div, inv_pow]

/-! ## Geometry: the growing ball, the unit cube, the lattice -/

theorem mem_closedBall_growingBallRadius {n : ℕ} {y : Vec d}
    (h : ‖y‖ ≤ (2 : ℝ) ^ n) :
    y ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n) := by
  rw [Metric.mem_closedBall, dist_zero_right, growingBallRadius]
  refine h.trans ?_
  have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hstep : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by ring
  linarith

theorem norm_le_half_of_mem_unitCube {u : Vec d}
    (hu : u ∈ openCubeSet (originCube d 0)) : ‖u‖ ≤ 1 / 2 := by
  rw [mem_openCubeSet_originCube_iff] at hu
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
  have h := hu i
  rw [zpow_zero] at h
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [h.1, h.2]

/-- The coordinatewise rounding of a point. -/
def nearestLattice (x : Vec d) : Fin d → ℤ := fun i => round (x i)

theorem norm_sub_latticePoint_le (x : Vec d) :
    ‖x - latticePoint (nearestLattice x)‖ ≤ 1 / 2 := by
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
  have h : |x i - (round (x i) : ℝ)| ≤ 1 / 2 := abs_sub_round (x i)
  simpa [latticePoint, nearestLattice, Real.norm_eq_abs] using h

theorem norm_latticePoint_le (x : Vec d) :
    ‖latticePoint (nearestLattice x)‖ ≤ ‖x‖ + 1 / 2 := by
  have h : ‖latticePoint (nearestLattice x) - x‖ ≤ 1 / 2 := by
    rw [← norm_neg]
    simpa using norm_sub_latticePoint_le x
  have := norm_add_le (latticePoint (nearestLattice x) - x) x
  simp only [sub_add_cancel] at this
  linarith

theorem nearestLattice_mem_latticeBox {x : Vec d} {n : ℕ}
    (hx : ‖x‖ ≤ (2 : ℝ) ^ n) : nearestLattice x ∈ latticeBox d n := by
  rw [latticeBox, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  simp only [nearestLattice]
  have hxi : |x i| ≤ (2 : ℝ) ^ n := by
    have := norm_le_pi_norm x i
    rw [Real.norm_eq_abs] at this
    linarith [this.trans hx]
  have hround : |x i - (round (x i) : ℝ)| ≤ 1 / 2 := abs_sub_round (x i)
  have hcast : (((2 : ℤ) ^ n : ℤ) : ℝ) = (2 : ℝ) ^ n := by push_cast; ring
  have habs := abs_le.mp hxi
  have hround' := abs_le.mp hround
  constructor
  · have hlt : (-((2 : ℤ) ^ n) : ℝ) - 1 < (round (x i) : ℝ) := by
      push_cast
      linarith [hround'.1, hround'.2, habs.1]
    have : (-((2 : ℤ) ^ n) : ℤ) - 1 < round (x i) := by exact_mod_cast hlt
    omega
  · have hlt : (round (x i) : ℝ) < (((2 : ℤ) ^ n : ℤ) : ℝ) + 1 := by
      rw [hcast]
      linarith [hround'.1, hround'.2, habs.2]
    have : round (x i) < (2 : ℤ) ^ n + 1 := by exact_mod_cast hlt
    omega

/-! ## An upper bound for the frozen unit-cube gradient Lipschitz seminorm -/

/-- A uniform pairwise gradient bound on the open unit cube bounds the frozen
`sSup` seminorm.  (The `none` index of the frozen family contributes `0`, which
is why nonnegativity of the bound is required.) -/
theorem unitCubeDerivLipschitzSeminorm_le {g : PotentialField d} {B : ℝ}
    (hB : 0 ≤ B)
    (h : ∀ u ∈ openCubeSet (originCube d 0), ∀ v ∈ openCubeSet (originCube d 0),
      ‖PotentialField.deriv g u - PotentialField.deriv g v‖ ≤ B * ‖u - v‖) :
    PotentialField.unitCubeDerivLipschitzSeminorm g ≤ B := by
  rw [PotentialField.unitCubeDerivLipschitzSeminorm]
  refine csSup_le ⟨0, ⟨none, rfl⟩⟩ ?_
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact hB
  | some p =>
      have hne : p.1.1.1 ≠ p.1.2.1 := fun hh => p.2 (Subtype.ext hh)
      have hpos : (0 : ℝ) < dist p.1.1.1 p.1.2.1 := dist_pos.2 hne
      rw [div_le_iff₀ hpos, dist_eq_norm, dist_eq_norm]
      exact h p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2

/-! ## The gradient and seminorm bounds -/

variable {omega : PotentialSample d} {n : ℕ} {C : ℝ}

/-- **The gradient series** (printed `step .5`).  Summing the growing-ball
gradient bound over the scales costs one geometric constant. -/
theorem norm_deriv_anchoredPartialSumField_le (hC : 0 ≤ C)
    (hgrad : ∀ k : ℕ, ∀ y ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n),
      ‖PotentialField.deriv (omega k) y‖ ≤
        C * ((((3 : ℝ) ^ k)⁻¹) * Real.sqrt ((n : ℝ) + (k : ℝ) + 1)))
    (L : ℕ) {x : Vec d}
    (hx : x ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n)) :
    ‖PotentialField.deriv (anchoredPartialSumField omega L) x‖ ≤
      C * gradSeriesConst * Real.sqrt ((n : ℝ) + 1) := by
  rw [deriv_anchoredPartialSumField]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ k ∈ Finset.range (L + 1),
      ‖PotentialField.deriv (omega k) x‖ ≤
        C * ((1 / 3 : ℝ) ^ k * Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) := by
    intro k _
    have h := hgrad k x hx
    rwa [inv_pow_three_eq] at h
  calc ∑ k ∈ Finset.range (L + 1), ‖PotentialField.deriv (omega k) x‖
      ≤ ∑ k ∈ Finset.range (L + 1),
          C * ((1 / 3 : ℝ) ^ k * Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) :=
        Finset.sum_le_sum hterm
    _ = C * ∑ k ∈ Finset.range (L + 1),
          (1 / 3 : ℝ) ^ k * Real.sqrt ((n : ℝ) + (k : ℝ) + 1) := by
        rw [Finset.mul_sum]
    _ ≤ C * (geomSqrtConst (1 / 3) * Real.sqrt ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left
          (sum_geom_sqrt_le (by norm_num) (by norm_num) n _) hC
    _ = C * gradSeriesConst * Real.sqrt ((n : ℝ) + 1) := by
        rw [gradSeriesConst]; ring

/-- **The gradient Lipschitz series** (printed `step .5`, the `C^{1,1}`
representative of `∇² log ã_L`).  The `3^{-2k}` factor is discarded down to
`3^{-k}`, so the same geometric constant serves. -/
theorem unitCubeDerivLipschitzSeminorm_translate_le (hC : 0 ≤ C)
    (hlip : ∀ k : ℕ, ∀ y ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n),
      ∀ y' ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n),
        ‖PotentialField.deriv (omega k) y - PotentialField.deriv (omega k) y'‖ ≤
          C * ((((3 : ℝ) ^ k)⁻¹ * ((3 : ℝ) ^ k)⁻¹) *
            Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) * ‖y - y'‖)
    (L : ℕ) {x : Vec d} (hx : ‖x‖ + 1 / 2 ≤ (2 : ℝ) ^ n) :
    PotentialField.unitCubeDerivLipschitzSeminorm
        (PotentialField.translate x (anchoredPartialSumField omega L)) ≤
      C * gradSeriesConst * Real.sqrt ((n : ℝ) + 1) := by
  have hB : (0 : ℝ) ≤ C * gradSeriesConst * Real.sqrt ((n : ℝ) + 1) := by
    have := gradSeriesConst_nonneg
    have h2 := Real.sqrt_nonneg ((n : ℝ) + 1)
    positivity
  refine unitCubeDerivLipschitzSeminorm_le hB ?_
  intro u hu v hv
  have hball : ∀ w : Vec d, w ∈ openCubeSet (originCube d 0) →
      w + x ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n) := by
    intro w hw
    refine mem_closedBall_growingBallRadius ?_
    have hwn := norm_le_half_of_mem_unitCube hw
    have := norm_add_le w x
    linarith
  have hu' := hball u hu
  have hv' := hball v hv
  rw [deriv_translate, deriv_translate, deriv_anchoredPartialSumField,
    deriv_anchoredPartialSumField, ← Finset.sum_sub_distrib]
  have hdiff : (u + x) - (v + x) = u - v := by abel
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ k ∈ Finset.range (L + 1),
      ‖PotentialField.deriv (omega k) (u + x) -
          PotentialField.deriv (omega k) (v + x)‖ ≤
        C * ((1 / 3 : ℝ) ^ k * Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) * ‖u - v‖ := by
    intro k _
    have h := hlip k (u + x) hu' (v + x) hv'
    rw [hdiff] at h
    refine h.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine mul_le_mul_of_nonneg_left ?_ hC
    refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    rw [inv_pow_three_eq]
    have hle : (1 / 3 : ℝ) ^ k ≤ 1 := by
      exact pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ (1/3:ℝ)) k]
  calc ∑ k ∈ Finset.range (L + 1),
        ‖PotentialField.deriv (omega k) (u + x) -
          PotentialField.deriv (omega k) (v + x)‖
      ≤ ∑ k ∈ Finset.range (L + 1),
          C * ((1 / 3 : ℝ) ^ k * Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) * ‖u - v‖ :=
        Finset.sum_le_sum hterm
    _ = (C * ∑ k ∈ Finset.range (L + 1),
          (1 / 3 : ℝ) ^ k * Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) * ‖u - v‖ := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ (C * (geomSqrtConst (1 / 3) * Real.sqrt ((n : ℝ) + 1))) * ‖u - v‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left
          (sum_geom_sqrt_le (by norm_num) (by norm_num) n _) hC
    _ = C * gradSeriesConst * Real.sqrt ((n : ℝ) + 1) * ‖u - v‖ := by
        rw [gradSeriesConst]; ring

/-! ## The value bound: lattice interpolation and the high-scale tail -/

/-- The mean value step: the increment of one shell between two points of the
growing ball. -/
theorem abs_sub_le_of_gradBound (k : ℕ)
    (hgrad : ∀ y ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n),
      ‖PotentialField.deriv (omega k) y‖ ≤
        C * ((((3 : ℝ) ^ k)⁻¹) * Real.sqrt ((n : ℝ) + (k : ℝ) + 1)))
    {a b : Vec d} (ha : a ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n))
    (hb : b ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n)) :
    |omega k b - omega k a| ≤
      C * ((((3 : ℝ) ^ k)⁻¹) * Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) * ‖b - a‖ := by
  have hconv : Convex ℝ (Metric.closedBall (0 : Vec d) (growingBallRadius n)) :=
    convex_closedBall _ _
  have hmean := hconv.norm_image_sub_le_of_norm_fderiv_le
    (f := fun z : Vec d => omega k z)
    (fun z _ => ((omega k).hasFDerivAt z).differentiableAt)
    (fun z hz => by
      rw [((omega k).hasFDerivAt z).fderiv]
      exact hgrad z hz)
    ha hb
  rwa [Real.norm_eq_abs] at hmean

/-- **The value bound** (printed `step .4`).  Lattice interpolation for the
scales `k ≤ N(n)` and the mean value inequality along `[0,x]` for `k > N(n)`. -/
theorem abs_anchoredPartialSum_le (hC : 0 ≤ C) {A : ℝ}
    (hval : ∀ z : Fin d → ℤ, z ∈ latticeBox d n → ∀ K : ℕ, K ≤ maxCutoffLevel n →
      |anchoredPartialSum omega K (latticePoint z)| ≤ A)
    (hgrad : ∀ k : ℕ, ∀ y ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n),
      ‖PotentialField.deriv (omega k) y‖ ≤
        C * ((((3 : ℝ) ^ k)⁻¹) * Real.sqrt ((n : ℝ) + (k : ℝ) + 1)))
    (L : ℕ) {x : Vec d} (hx : 2 + ‖x‖ ≤ (2 : ℝ) ^ n) :
    |anchoredPartialSum omega L x| ≤
      A + C * (gradSeriesConst + tailSeriesConst) * Real.sqrt ((n : ℝ) + 1) / 2 := by
  classical
  set z : Fin d → ℤ := nearestLattice x with hz_def
  have hxnorm : ‖x‖ ≤ (2 : ℝ) ^ n := by linarith
  have hxball : x ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n) :=
    mem_closedBall_growingBallRadius hxnorm
  have hzball : latticePoint z ∈
      Metric.closedBall (0 : Vec d) (growingBallRadius n) := by
    refine mem_closedBall_growingBallRadius ?_
    have := norm_latticePoint_le x
    rw [← hz_def] at this
    linarith
  have hzero : (0 : Vec d) ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n) := by
    simpa using (growingBallRadius_pos n).le
  have hzbox : z ∈ latticeBox d n := nearestLattice_mem_latticeBox hxnorm
  set m : ℕ := min L (maxCutoffLevel n) with hm_def
  have hmL : m + 1 ≤ L + 1 := by
    have : m ≤ L := min_le_left _ _
    omega
  -- the splitting of the cutoff range
  have hsplit : anchoredPartialSum omega L x =
      anchoredPartialSum omega m x +
        ∑ k ∈ Finset.Ico (m + 1) (L + 1), (omega k x - omega k 0) := by
    simp only [anchoredPartialSum, Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive (fun k => omega k x - omega k 0)
      (Nat.zero_le (m + 1)) hmL).symm
  -- the lattice interpolation of the low scales
  have hinterp : anchoredPartialSum omega m x -
      anchoredPartialSum omega m (latticePoint z) =
      ∑ k ∈ Finset.range (m + 1), (omega k x - omega k (latticePoint z)) := by
    rw [anchoredPartialSum, anchoredPartialSum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hlow : |anchoredPartialSum omega m x| ≤
      A + C * gradSeriesConst * Real.sqrt ((n : ℝ) + 1) / 2 := by
    have hlat : |anchoredPartialSum omega m (latticePoint z)| ≤ A :=
      hval z hzbox m (min_le_right _ _)
    have hgap : |anchoredPartialSum omega m x -
        anchoredPartialSum omega m (latticePoint z)| ≤
        C * gradSeriesConst * Real.sqrt ((n : ℝ) + 1) / 2 := by
      rw [hinterp]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ k ∈ Finset.range (m + 1),
          |omega k x - omega k (latticePoint z)| ≤
            C * ((1 / 3 : ℝ) ^ k * Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) * (1 / 2) := by
        intro k _
        have h := abs_sub_le_of_gradBound k (hgrad k) hzball hxball
        have hxz : ‖x - latticePoint z‖ ≤ 1 / 2 := by
          have := norm_sub_latticePoint_le x
          rw [← hz_def] at this
          exact this
        have hnn : (0 : ℝ) ≤ C * ((((3 : ℝ) ^ k)⁻¹) *
            Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) := by positivity
        have := h.trans (mul_le_mul_of_nonneg_left hxz hnn)
        rwa [inv_pow_three_eq] at this
      calc ∑ k ∈ Finset.range (m + 1), |omega k x - omega k (latticePoint z)|
          ≤ ∑ k ∈ Finset.range (m + 1),
              C * ((1 / 3 : ℝ) ^ k * Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) * (1 / 2) :=
            Finset.sum_le_sum hterm
        _ = (C * ∑ k ∈ Finset.range (m + 1),
              (1 / 3 : ℝ) ^ k * Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) * (1 / 2) := by
            rw [Finset.mul_sum, Finset.sum_mul]
        _ ≤ (C * (geomSqrtConst (1 / 3) * Real.sqrt ((n : ℝ) + 1))) * (1 / 2) := by
            refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
            exact mul_le_mul_of_nonneg_left
              (sum_geom_sqrt_le (by norm_num) (by norm_num) n _) hC
        _ = C * gradSeriesConst * Real.sqrt ((n : ℝ) + 1) / 2 := by
            rw [gradSeriesConst]; ring
    have := abs_sub_abs_le_abs_sub (anchoredPartialSum omega m x)
      (anchoredPartialSum omega m (latticePoint z))
    linarith
  -- the high-scale tail
  have htail : |∑ k ∈ Finset.Ico (m + 1) (L + 1), (omega k x - omega k 0)| ≤
      C * tailSeriesConst * Real.sqrt ((n : ℝ) + 1) / 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hk2 : ∀ k ∈ Finset.Ico (m + 1) (L + 1), n + 2 ≤ k := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hm1 : m ≤ L := min_le_left _ _
      have hm3 := min_choice L (maxCutoffLevel n)
      rw [← hm_def] at hm3
      simp only [maxCutoffLevel] at hm3
      omega
    have hterm : ∀ k ∈ Finset.Ico (m + 1) (L + 1),
        |omega k x - omega k 0| ≤
          C * ((2 / 3 : ℝ) ^ k * Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) * (1 / 2) := by
      intro k hk
      have h := abs_sub_le_of_gradBound k (hgrad k) hzero hxball
      have hxn : ‖x - (0 : Vec d)‖ ≤ growingBallRadius n := by
        simpa [growingBallRadius] using
          (mem_closedBall_growingBallRadius (d := d) hxnorm)
      have hnn : (0 : ℝ) ≤ C * ((((3 : ℝ) ^ k)⁻¹) *
          Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) := by positivity
      have hstep := h.trans (mul_le_mul_of_nonneg_left hxn hnn)
      have hgeo := growingRadius_mul_inv_pow_le (hk2 k hk)
      have hs : (0 : ℝ) ≤ Real.sqrt ((n : ℝ) + (k : ℝ) + 1) := Real.sqrt_nonneg _
      have hfinal : C * ((((3 : ℝ) ^ k)⁻¹) *
          Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) * growingBallRadius n ≤
          C * ((2 / 3 : ℝ) ^ k * Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) * (1 / 2) := by
        rw [growingBallRadius]
        nlinarith [mul_le_mul_of_nonneg_right hgeo hs,
          mul_nonneg hC hs]
      exact hstep.trans hfinal
    calc ∑ k ∈ Finset.Ico (m + 1) (L + 1), |omega k x - omega k 0|
        ≤ ∑ k ∈ Finset.Ico (m + 1) (L + 1),
            C * ((2 / 3 : ℝ) ^ k * Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) * (1 / 2) :=
          Finset.sum_le_sum hterm
      _ = (C * ∑ k ∈ Finset.Ico (m + 1) (L + 1),
            (2 / 3 : ℝ) ^ k * Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) * (1 / 2) := by
          rw [Finset.mul_sum, Finset.sum_mul]
      _ ≤ (C * (geomSqrtConst (2 / 3) * Real.sqrt ((n : ℝ) + 1))) * (1 / 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_left
            (sum_geom_sqrt_le (by norm_num) (by norm_num) n _) hC
      _ = C * tailSeriesConst * Real.sqrt ((n : ℝ) + 1) / 2 := by
          rw [tailSeriesConst]; ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have hring : A + C * gradSeriesConst * Real.sqrt ((n : ℝ) + 1) / 2 +
      C * tailSeriesConst * Real.sqrt ((n : ℝ) + 1) / 2 =
      A + C * (gradSeriesConst + tailSeriesConst) * Real.sqrt ((n : ℝ) + 1) / 2 := by
    ring
  linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
