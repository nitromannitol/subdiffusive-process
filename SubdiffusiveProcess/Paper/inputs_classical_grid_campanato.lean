import SubdiffusiveProcess.Paper.inputs_Cp_holder
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Analysis.NormalizedOscillation
import SubdiffusiveProcess.Lane1.TriadicGrid
import SubdiffusiveProcess.Lane1.ChaosBasic
import SubdiffusiveProcess.Analysis.NormalizedMeanMinimizer

/-! The classical Campanato criterion tested on a fixed dense triadic mesh.
This statement concerns arbitrary continuous functions and no PDE or random coefficient.
Reference: Campanato (1963), §§1–2, combined with ball containment and mean minimization. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess SubdiffusiveProcess.Lane4 SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators ENNReal
namespace Paper


/-- The unit cube is the sup-norm ball of radius `1/2` around its centre. -/
theorem aux_inputs_classical_grid_campanato_cube_eq_ball (d : ℕ) :
    (unitNeumannCube d : Set (SpatialCoordinates d)) =
      Metric.ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2) := by
  unfold unitNeumannCube
  rw [centeredCube_coe_eq_ball]

/-- Sup-norm balls meet the unit cube in volume at least `rad^d`. -/
theorem aux_inputs_classical_grid_campanato_density (d : ℕ) (x : SpatialCoordinates d) (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1)
    (rad : ℝ) (hrad : 0 < rad) (hrad1 : rad ≤ 1) :
    ENNReal.ofReal (1 * rad ^ d) ≤
      volume (Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d))) := by
  set c : SpatialCoordinates d := fun i => max (rad / 2) (min (x i) (1 - rad / 2)) with hc
  have hci : ∀ i, rad / 2 ≤ c i ∧ c i ≤ 1 - rad / 2 := by
    intro i
    refine ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have hcx : ∀ i, |c i - x i| ≤ rad / 2 := by
    intro i
    obtain ⟨h0, h1⟩ := hx i
    have hrad1' := hrad1
    simp only [hc, max_def, min_def]
    split_ifs <;> (rw [abs_le]; constructor <;> linarith)
  have hsub : Metric.ball c (rad / 2) ⊆
      Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)) := by
    intro z hz
    rw [Metric.mem_ball, dist_pi_lt_iff (by positivity)] at hz
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_pi_lt_iff hrad]
      intro i
      have := hz i
      have h2 := hcx i
      rw [Real.dist_eq] at this ⊢
      rw [abs_lt] at this ⊢
      rw [abs_le] at h2
      constructor <;> linarith [this.1, this.2, h2.1, h2.2]
    · rw [aux_inputs_classical_grid_campanato_cube_eq_ball, Metric.mem_ball, dist_pi_lt_iff (by norm_num)]
      intro i
      have := hz i
      obtain ⟨h1, h2⟩ := hci i
      rw [Real.dist_eq] at this ⊢
      rw [abs_lt] at this ⊢
      constructor <;> linarith [this.1, this.2]
  calc ENNReal.ofReal (1 * rad ^ d) = volume (Metric.ball c (rad / 2)) := by
        rw [Real.volume_pi_ball c (by positivity)]
        simp only [Fintype.card_fin]
        congr 1
        ring
    _ ≤ _ := measure_mono hsub



/-- A triadic grid point of the unit cube within one mesh width of a point of the open cube. -/
theorem aux_inputs_classical_grid_campanato_gridpoint (d : ℕ) (k : ℕ) (x : SpatialCoordinates d)
    (hx : ∀ i, x i ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ gridIndices d 1 (k + 1),
      gridPoint (k + 1) a ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) ∧
      dist (gridPoint (k + 1) a) x < (3 : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) := by
  classical
  set N : ℤ := (3 : ℤ) ^ (k + 1) with hN
  have hN3 : (3 : ℤ) ≤ N := by
    rw [hN]
    calc (3 : ℤ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  set s : ℝ := (N : ℝ) with hs
  have hs3 : (3 : ℝ) ≤ s := by rw [hs]; exact_mod_cast hN3
  have hspos : 0 < s := by linarith
  have hinv : (3 : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) = s⁻¹ := by
    rw [zpow_neg, zpow_natCast, hs, hN]; push_cast; rfl
  let a : Fin d → ℤ := fun i => max ⌊x i * s⌋ 1
  have key : ∀ i, 1 ≤ a i ∧ a i ≤ N - 1 ∧ |(a i : ℝ) * s⁻¹ - x i| < s⁻¹ := by
    intro i
    have hxi := hx i
    have hfl := Int.floor_le (x i * s)
    have hlt := Int.lt_floor_add_one (x i * s)
    have h1 : 1 ≤ a i := le_max_right _ _
    have hxs : x i * s < s := by nlinarith [hxi.2]
    have h2 : ⌊x i * s⌋ < N := by
      rw [Int.floor_lt]; exact hxs
    refine ⟨h1, max_le (by omega) (by omega), ?_⟩
    have hsinv : 0 < s⁻¹ := by positivity
    have hss : s * s⁻¹ = 1 := by field_simp
    by_cases hc : 1 ≤ ⌊x i * s⌋
    · have : a i = ⌊x i * s⌋ := max_eq_left hc
      rw [this, abs_lt]
      constructor
      · nlinarith [mul_pos hsinv hsinv]
      · nlinarith [mul_pos hsinv hsinv]
    · have hle : ⌊x i * s⌋ ≤ 0 := by omega
      have : a i = 1 := max_eq_right (by omega)
      have hfl0 : ((⌊x i * s⌋ : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hle
      have hxs1 : x i * s < 1 := by linarith
      rw [this, abs_lt]
      simp only [Int.cast_one, one_mul]
      have hx0 : 0 < x i * s := mul_pos hxi.1 hspos
      constructor
      · nlinarith [mul_pos hsinv hsinv]
      · nlinarith [mul_pos hsinv hsinv]
  refine ⟨a, ?_, ?_, ?_⟩
  · rw [gridIndices, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have hceil : ⌈(1 : ℝ) * (3 : ℝ) ^ ((k + 1 : ℕ) : ℤ)⌉ = N := by
      rw [one_mul, zpow_natCast, hN]
      exact_mod_cast Int.ceil_natCast ((3 : ℕ) ^ (k + 1))
    rw [hceil]
    obtain ⟨h1, h2, -⟩ := key i
    constructor <;> omega
  · rw [aux_inputs_classical_grid_campanato_cube_eq_ball, Metric.mem_ball, dist_pi_lt_iff (by norm_num)]
    intro i
    obtain ⟨h1, h2, h3⟩ := key i
    have hsinv : 0 < s⁻¹ := by positivity
    have hss : s * s⁻¹ = 1 := by field_simp
    have h1' : (1 : ℝ) ≤ (a i : ℝ) := by exact_mod_cast h1
    have h2' : (a i : ℝ) ≤ s - 1 := by
      have : ((a i : ℤ) : ℝ) ≤ ((N - 1 : ℤ) : ℝ) := by exact_mod_cast h2
      simpa [hs] using this
    have hw0 : 0 < (a i : ℝ) * s⁻¹ := by positivity
    have hw1 : (a i : ℝ) * s⁻¹ < 1 := by nlinarith
    show dist ((a i : ℝ) * (3 : ℝ) ^ (-((k + 1 : ℕ) : ℤ))) ((1 / 2 : ℝ)) < 1 / 2
    rw [hinv, Real.dist_eq, abs_lt]
    constructor <;> linarith
  · rw [dist_pi_lt_iff (by rw [hinv]; positivity)]
    intro i
    obtain ⟨-, -, h3⟩ := key i
    show dist ((a i : ℝ) * (3 : ℝ) ^ (-((k + 1 : ℕ) : ℤ))) (x i) < _
    rw [hinv, Real.dist_eq]
    exact h3



theorem aux_inputs_classical_grid_campanato_osc (d : ℕ) (alpha : ℝ) (ha : 0 < alpha)
    (U : SpatialCoordinates d → ℝ) (hU : Continuous U) (K : ℝ) (hK : 0 ≤ K)
    (H : ∀ k : ℕ, ∀ a ∈ gridIndices d 1 (k + 1),
        gridPoint (k + 1) a ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
        let W := Metric.ball (gridPoint (k + 1) a) ((9 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) ∩
          (unitNeumannCube d : Set (SpatialCoordinates d))
        normalizedL2On W (fun y => U y - averageOn W U) ≤ K * (3 : ℝ) ^ (-(alpha * k)))
    (x : SpatialCoordinates d) (hx : x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)))
    (rad : ℝ) (hrad : 0 < rad) (hrad1 : rad ≤ 1) :
    ∫ y in Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
      (U y - (volume.real (Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d))))⁻¹ *
        ∫ q in Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)), U q) ^ 2 ≤
      (Real.sqrt ((27 / 4 : ℝ) ^ d) * K) ^ 2 * rad ^ (2 * alpha) *
        volume.real (Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d))) := by
  classical
  set Q : Set (SpatialCoordinates d) := (unitNeumannCube d : Set (SpatialCoordinates d)) with hQ
  set B' := Metric.ball x rad ∩ Q with hB'
  have hxQ : ∀ i, x i ∈ Ioo (0 : ℝ) 1 := by
    intro i
    rw [hQ, aux_inputs_classical_grid_campanato_cube_eq_ball, Metric.mem_ball, dist_pi_lt_iff (by norm_num)] at hx
    have := hx i
    rw [Real.dist_eq, abs_lt] at this
    constructor <;> linarith [this.1, this.2]
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near
    (show (1 : ℝ) ≤ 4 / rad by rw [le_div_iff₀ hrad]; linarith) (by norm_num : (1 : ℝ) < 3)
  obtain ⟨a, ha_mem, ha_Q, ha_dist⟩ := aux_inputs_classical_grid_campanato_gridpoint d k x hxQ
  have hH := H k a ha_mem ha_Q
  set w := gridPoint (k + 1) a with hw
  set t : ℝ := (3 : ℝ) ^ (-(k : ℤ)) with ht
  have h3k : (0 : ℝ) < 3 ^ k := by positivity
  have htk : t = ((3 : ℝ) ^ k)⁻¹ := by rw [ht, zpow_neg, zpow_natCast]
  have htpos : 0 < t := by rw [htk]; positivity
  have hrad_le : rad ≤ 4 * t := by
    rw [htk]
    rw [le_div_iff₀ hrad] at hk1
    rw [← div_eq_mul_inv, le_div_iff₀ h3k]
    nlinarith
  have ht_lt : t < 3 * rad / 4 := by
    rw [htk, inv_lt_comm₀ h3k (by positivity)]
    rw [div_lt_iff₀ hrad] at hk2
    rw [pow_succ] at hk2
    have : 4 / (3 * rad) < 3 ^ k := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    calc ((3 * rad / 4 : ℝ))⁻¹ = 4 / (3 * rad) := by field_simp
      _ < _ := this
  have hstep : (3 : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) = t / 3 := by
    rw [ht, show (-((k + 1 : ℕ) : ℤ)) = -(k : ℤ) + (-1) by push_cast; ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num [div_eq_mul_inv, mul_comm]
  set W := Metric.ball w ((9 / 2 : ℝ) * t) ∩ Q with hW
  have hBW : B' ⊆ W := by
    intro z hz
    refine ⟨?_, hz.2⟩
    have h1 : dist z x < rad := Metric.mem_ball.1 hz.1
    have h2 : dist w x < t / 3 := by rw [← hstep]; exact ha_dist
    have h3 : dist z w ≤ dist z x + dist x w := dist_triangle z x w
    rw [dist_comm x w] at h3
    rw [Metric.mem_ball]
    linarith
  have hball_fin : ∀ (c : SpatialCoordinates d) (r : ℝ), volume (Metric.ball c r) ≠ ⊤ :=
    fun c r => measure_ball_lt_top.ne
  have hWfin : volume W ≠ ⊤ :=
    ne_top_of_le_ne_top (hball_fin w _) (measure_mono inter_subset_left)
  have hB'fin : volume B' ≠ ⊤ := ne_top_of_le_ne_top hWfin (measure_mono hBW)
  have hdens := aux_inputs_classical_grid_campanato_density d x (fun i => ⟨(hxQ i).1.le, (hxQ i).2.le⟩) rad hrad hrad1
  have hdens' : rad ^ d ≤ (volume B').toReal := by
    have := ENNReal.toReal_mono hB'fin hdens
    rwa [ENNReal.toReal_ofReal (by positivity), one_mul] at this
  have hvolW : (volume W).toReal ≤ (9 * t) ^ d := by
    have h1 : volume W ≤ volume (Metric.ball w ((9 / 2 : ℝ) * t)) := measure_mono inter_subset_left
    rw [Real.volume_pi_ball w (by positivity)] at h1
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rw [ENNReal.toReal_ofReal (by positivity), Fintype.card_fin] at this
    have e : 2 * ((9 / 2 : ℝ) * t) = 9 * t := by ring
    rwa [e] at this
  have hK0 : IsCompact (Metric.closedBall (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2)) :=
    isCompact_closedBall _ _
  have hQsub : Q ⊆ Metric.closedBall (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2) := by
    rw [hQ, aux_inputs_classical_grid_campanato_cube_eq_ball]; exact Metric.ball_subset_closedBall
  have hsqK : IntegrableOn (fun y => U y ^ 2)
      (Metric.closedBall (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2)) :=
    (hU.pow 2).continuousOn.integrableOn_compact hK0
  have hMem : ∀ S : Set (SpatialCoordinates d), S ⊆ Q → MemLp U 2 (volume.restrict S) :=
    fun S hS => (memLp_two_iff_integrable_sq hU.aestronglyMeasurable).2
      (hsqK.mono_set (hS.trans hQsub))
  have hWQ : W ⊆ Q := inter_subset_right
  have hB'Q : B' ⊆ Q := inter_subset_right
  haveI : IsFiniteMeasure (volume.restrict W) := isFiniteMeasure_restrict.mpr hWfin
  set c : ℝ := averageOn W U with hc
  have step1 := integral_sq_sub_average_le_integral_sq_sub_const B' hB'fin U (hMem B' hB'Q) c
  have hfW : IntegrableOn (fun y => (U y - c) ^ 2) W :=
    ((hMem W hWQ).sub (memLp_const c)).integrable_sq
  have step2 : ∫ y in B', (U y - c) ^ 2 ≤ ∫ y in W, (U y - c) ^ 2 :=
    setIntegral_mono_set hfW (Filter.Eventually.of_forall fun y => sq_nonneg _)
      (HasSubset.Subset.eventuallyLE hBW)
  have hpos : 0 < (volume W).toReal :=
    lt_of_lt_of_le (lt_of_lt_of_le (pow_pos hrad d) hdens')
      (ENNReal.toReal_mono hWfin (measure_mono hBW))
  set t' : ℝ := (3 : ℝ) ^ (-(alpha * k)) with ht'
  have hsq : ∫ y in W, (U y - c) ^ 2 ≤ (volume W).toReal * (K * t') ^ 2 := by
    have h : normalizedL2On W (fun y => U y - averageOn W U) ≤ K * t' := hH
    rw [normalizedL2On_eq_sqrt_volumeAverage, Real.sqrt_le_iff] at h
    have h2 := h.2
    unfold Homogenization.volumeAverage at h2
    rw [inv_mul_le_iff₀ hpos] at h2
    exact h2
  have ht'le : t' ≤ rad ^ alpha := by
    have e1 : t' = t ^ alpha := by
      rw [ht, ht', ← Real.rpow_intCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      push_cast
      ring
    rw [e1]
    exact Real.rpow_le_rpow htpos.le (by linarith) ha.le
  have ht'0 : 0 ≤ t' := by positivity
  have hKt : (K * t') ^ 2 ≤ K ^ 2 * rad ^ (2 * alpha) := by
    have e2 : rad ^ (2 * alpha) = (rad ^ alpha) ^ 2 := by
      rw [show 2 * alpha = alpha * (2 : ℕ) by push_cast; ring, Real.rpow_mul hrad.le,
        Real.rpow_natCast]
    rw [e2, mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht'0 ht'le 2) (sq_nonneg K)
  have h9 : (9 * t) ^ d ≤ (27 / 4 : ℝ) ^ d * (volume B').toReal := by
    calc (9 * t) ^ d ≤ ((27 / 4 : ℝ) * rad) ^ d :=
          pow_le_pow_left₀ (by positivity) (by linarith) d
      _ = (27 / 4 : ℝ) ^ d * rad ^ d := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hdens' (by positivity)
  have hsqrt : (Real.sqrt ((27 / 4 : ℝ) ^ d) * K) ^ 2 = (27 / 4 : ℝ) ^ d * K ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [hsqrt]
  calc _ ≤ ∫ y in B', (U y - c) ^ 2 := step1
    _ ≤ ∫ y in W, (U y - c) ^ 2 := step2
    _ ≤ (volume W).toReal * (K * t') ^ 2 := hsq
    _ ≤ (9 * t) ^ d * (K ^ 2 * rad ^ (2 * alpha)) :=
        mul_le_mul hvolW hKt (sq_nonneg _) (by positivity)
    _ ≤ ((27 / 4 : ℝ) ^ d * (volume B').toReal) * (K ^ 2 * rad ^ (2 * alpha)) :=
        mul_le_mul_of_nonneg_right h9 (by positivity)
    _ = _ := by rw [Measure.real]; ring


/-- Classical quadratic Campanato embedding, with testing windows on a dense triadic mesh. -/
theorem inputs_classical_grid_campanato (d : ℕ) (hd : 1 ≤ d)
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ,0 < C ∧ ∀ (U : SpatialCoordinates d → ℝ),Continuous U →
    ∀ K : ℝ,0 ≤ K →
      (∀ k : ℕ,∀ a ∈ gridIndices d 1 (k+1),
        gridPoint (k+1) a ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
        let W := Metric.ball (gridPoint (k+1) a) ((9/2:ℝ)*(3:ℝ)^(-(k:ℤ))) ∩
          (unitNeumannCube d : Set (SpatialCoordinates d))
        normalizedL2On W (fun y => U y-averageOn W U) ≤ K*(3:ℝ)^(-(alpha*k))) →
      ∀ x ∈ (closedCube (fun _ : Fin d => (1/2:ℝ)) 1 one_pos : Set (SpatialCoordinates d)),
      ∀ y ∈ (closedCube (fun _ : Fin d => (1/2:ℝ)) 1 one_pos : Set (SpatialCoordinates d)),
        |U x-U y| ≤ C*K*(Real.sqrt (∑ i : Fin d,(x i-y i)^2))^alpha := by
  classical
  obtain ⟨C0, hC0, hCp⟩ := inputs_Cp_holder d alpha ha ha1
  set c2 : ℝ := (27 / 4 : ℝ) ^ d with hc2
  refine ⟨C0 * Real.sqrt c2, by positivity, ?_⟩
  intro U hU K hK H x hx y hy
  set z : SpatialCoordinates d := fun _ : Fin d => (1 / 2 : ℝ) with hz
  set Q : Set (SpatialCoordinates d) := (unitNeumannCube d : Set (SpatialCoordinates d)) with hQ
  have hQball : Q = Metric.ball z (1 / 2) :=
    aux_inputs_classical_grid_campanato_cube_eq_ball d
  have hopen : IsOpen Q := by rw [hQball]; exact Metric.isOpen_ball
  have hclQ : closure Q = Metric.closedBall z (1 / 2) := by
    rw [hQball]; exact closure_ball _ (by norm_num)
  have hK0 : IsCompact (Metric.closedBall z (1 / 2)) := isCompact_closedBall _ _
  have hsqK : IntegrableOn (fun w => U w ^ 2) (Metric.closedBall z (1 / 2)) :=
    (hU.pow 2).continuousOn.integrableOn_compact hK0
  have hMem : MemLp U 2 (volume.restrict Q) :=
    (memLp_two_iff_integrable_sq hU.aestronglyMeasurable).2
      (hsqK.mono_set (by rw [hQball]; exact Metric.ball_subset_closedBall))
  -- the `L²` class of `U` on the unit cube
  let u : DomainL2 (centeredCube z 1 one_pos) := hMem.toLp U
  have hu : (u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict Q] U := hMem.coeFn_toLp
  have hosc : ∀ p ∈ centeredCube z 1 one_pos, ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
      ∫ w in Metric.ball p rad ∩ (centeredCube z 1 one_pos : Set (SpatialCoordinates d)),
          (u w - setAverage
            (Metric.ball p rad ∩ (centeredCube z 1 one_pos : Set (SpatialCoordinates d))) u) ^ 2
          ∂volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d)) ≤
        (Real.sqrt c2 * K) ^ 2 * rad ^ (2 * alpha) *
          volume.real (Metric.ball p rad ∩
            (centeredCube z 1 one_pos : Set (SpatialCoordinates d))) := by
    intro p hp rad hrad hrad1
    change ∫ w in Metric.ball p rad ∩ Q,
          (u w - setAverage (Metric.ball p rad ∩ Q) u) ^ 2
          ∂volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d)) ≤
        (Real.sqrt c2 * K) ^ 2 * rad ^ (2 * alpha) * volume.real (Metric.ball p rad ∩ Q)
    have hS : Metric.ball p rad ∩ Q ⊆ (centeredCube z 1 one_pos : Set (SpatialCoordinates d)) :=
      Set.inter_subset_right
    have hae : ∀ᵐ w ∂volume.restrict (Metric.ball p rad ∩ Q),
        (u : SpatialCoordinates d → ℝ) w = U w :=
      ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right hu
    have hosc0 := aux_inputs_classical_grid_campanato_osc d alpha ha U hU K hK H p hp rad hrad hrad1
    have havg : setAverage (Metric.ball p rad ∩ Q) u =
        (volume.real (Metric.ball p rad ∩ Q))⁻¹ * ∫ q in Metric.ball p rad ∩ Q, U q ∂volume := by
      rw [aux_inputs_Cp_holder_setAverage_eq_volume (Metric.ball p rad ∩ Q) u hS]
      congr 1
      exact integral_congr_ae hae
    rw [aux_inputs_Cp_holder_setIntegral_eq_volume (Metric.ball p rad ∩ Q) _ hS, havg]
    refine le_trans (le_of_eq ?_) hosc0
    refine integral_congr_ae ?_
    filter_upwards [hae] with w hw
    rw [hw]
  obtain ⟨V, hVc, hVae, hVhol, hVsem⟩ :=
    hCp z 1 one_pos le_rfl u (Real.sqrt c2 * K) (by positivity) hosc
  have hUV : U =ᵐ[volume.restrict Q] V := hu.symm.trans hVae
  have hEq : Set.EqOn U V Q :=
    Measure.eqOn_open_of_ae_eq hUV hopen hU.continuousOn hVc.continuousOn
  have hEqcl : closure Q ⊆ {w | U w = V w} := closure_minimal hEq (isClosed_eq hU hVc)
  have hxcl : x ∈ closure Q := by rw [hclQ]; exact hx
  have hycl : y ∈ closure Q := by rw [hclQ]; exact hy
  have hUx : U x = V x := hEqcl hxcl
  have hUy : U y = V y := hEqcl hycl
  rw [hUx, hUy]
  by_cases hxy : x = y
  · subst hxy
    simp only [sub_self, abs_zero]
    positivity
  · have hmem : |V x - V y| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha ∈
        holderRatioSet alpha (closedCube z 1 one_pos : Set (SpatialCoordinates d)) V :=
      ⟨x, hx, y, hy, hxy, rfl⟩
    have hle := (le_csSup hVhol hmem).trans hVsem
    have hdiff : x - y ≠ (0 : SpatialCoordinates d) := sub_ne_zero.mpr hxy
    have hpos : 0 < (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by
      have hs : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
        apply Real.sqrt_pos.2
        have : ∃ j, x j ≠ y j := by
          by_contra hcon
          push_neg at hcon
          exact hxy (funext hcon)
        obtain ⟨j, hj⟩ := this
        exact lt_of_lt_of_le (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 hj))))
          (Finset.single_le_sum (f := fun i : Fin d => (x i - y i) ^ 2)
            (fun i _ => sq_nonneg _) (Finset.mem_univ j))
      exact Real.rpow_pos_of_pos hs _
    rw [div_le_iff₀ hpos] at hle
    calc |V x - V y| ≤ C0 * (Real.sqrt c2 * K) * (Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)) ^ alpha :=
          hle
      _ = C0 * Real.sqrt c2 * K * (Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)) ^ alpha := by ring

end Paper
