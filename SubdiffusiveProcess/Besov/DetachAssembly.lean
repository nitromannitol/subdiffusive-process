module

public import SubdiffusiveProcess.Besov.DetachGeom
public import SubdiffusiveProcess.Besov.DetachLocal
public import SubdiffusiveProcess.Besov.DetachMink
public import SubdiffusiveProcess.Besov.DetachReal

@[expose] public section

/-!
# Depth-wise bound for the overlap oscillations (detach inequality)

`depth_bound`: for `H ∈ H¹(Q₀)` and every depth `j`, the root mean square over the overlap centres of the
`L²`-oscillations is at most `Cd d * Σ_{m > j} 3^{-m} X_m`, with `X_m = gradX H m`.
-/

open MeasureTheory
open Homogenization

namespace SubdiffusiveProcess.Besov.Detach

noncomputable section

/-- `X_m = (mean_R |(∇H)_R|²)^{1/2}` over the depth-`m` descendants of the unit cube. -/
def gradX {d : ℕ} (H : H1Function (openCubeSet (originCube d 0))) (m : ℕ) : ℝ :=
  Real.sqrt (∑ i : Fin d, theta (originCube d 0) m (fun x => H.grad x i))

/-- The block quantity for the overlap centre `S` and coordinate `i`. -/
def blockTheta {d : ℕ} (H : H1Function (openCubeSet (originCube d 0))) (S : TriadicCube d)
    (i : Fin d) (k : ℕ) : ℝ :=
  theta (originCube d (S.scale + 1)) (k + 1) (fun x => H.grad (x + cubeCenter S) i)

/-- The constant of the depth bound. -/
def Cd (d : ℕ) [NeZero d] : ℝ :=
  4 * (d : ℝ) * SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov.oscillationMultiscalePoincareConstant d *
    Real.sqrt ((3 : ℝ) ^ d)

theorem Cd_nonneg (d : ℕ) [NeZero d] : 0 ≤ Cd d := by
  unfold Cd
  have h1 : (0:ℝ) ≤ 4 := by norm_num
  have h2 : (0:ℝ) ≤ (d:ℝ) := by positivity
  have h3 : 0 ≤ SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov.oscillationMultiscalePoincareConstant d :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov.oscillationMultiscalePoincareConstant_nonneg d
  have h4 : (0:ℝ) ≤ Real.sqrt ((3:ℝ)^d) := Real.sqrt_nonneg _
  positivity

theorem grad_memLp_cube {d : ℕ} (H : H1Function (openCubeSet (originCube d 0))) (i : Fin d) :
    MemLp (fun x => H.grad x i) 2 (volume.restrict (cubeSet (originCube d 0))) := by
  have h := H.gradMemL2 i
  unfold MemL2On at h
  rw [Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet (originCube d 0))]
  exact h

theorem integrableOn_grad_cube {d : ℕ} (H : H1Function (openCubeSet (originCube d 0))) (i : Fin d) :
    IntegrableOn (fun x => H.grad x i) (cubeSet (originCube d 0)) volume := by
  have : IsFiniteMeasure (volume.restrict (cubeSet (originCube d 0))) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (isBounded_cubeSet (originCube d 0)).measure_lt_top⟩
  exact (grad_memLp_cube H i).integrable one_le_two

theorem gradX_nonneg {d : ℕ} (H : H1Function (openCubeSet (originCube d 0))) (m : ℕ) :
    0 ≤ gradX H m := by
  unfold gradX
  exact Real.sqrt_nonneg _

theorem gradX_mono {d : ℕ} (H : H1Function (openCubeSet (originCube d 0))) (m : ℕ) :
    gradX H m ≤ gradX H (m + 1) := by
  unfold gradX
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum fun i _ => theta_mono _ m _ (integrableOn_grad_cube H i)

theorem gradX_bdd {d : ℕ} (H : H1Function (openCubeSet (originCube d 0))) :
    ∃ G : ℝ, ∀ m, gradX H m ≤ G := by
  refine ⟨Real.sqrt (∑ i : Fin d, cubeAverage (originCube d 0) (fun x => (H.grad x i) ^ 2)),
    fun m => ?_⟩
  unfold gradX
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum fun i _ => theta_le_cubeAverage_sq _ m _ (grad_memLp_cube H i)

theorem sqrt_theta_le_gradX {d : ℕ} (H : H1Function (openCubeSet (originCube d 0))) (i : Fin d)
    (m : ℕ) :
    Real.sqrt (theta (originCube d 0) m (fun x => H.grad x i)) ≤ gradX H m := by
  unfold gradX
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (f := fun i : Fin d => theta (originCube d 0) m (fun x => H.grad x i))
    (fun j _ => theta_nonneg _ _ _) (Finset.mem_univ i)

theorem blockTheta_nonneg {d : ℕ} (H : H1Function (openCubeSet (originCube d 0))) (S : TriadicCube d)
    (i : Fin d) (k : ℕ) : 0 ≤ blockTheta H S i k := by
  unfold blockTheta
  exact theta_nonneg _ _ _

theorem memLp_grad_nbr {d : ℕ} (H : H1Function (openCubeSet (originCube d 0))) {j : ℕ}
    {S : TriadicCube d} (hS : S ∈ ScalarOverlap.centersAtDepth (originCube d 0) j) (i : Fin d)
    (δ : Fin d → Fin 3) :
    MemLp (fun x => H.grad x i) 2 (volume.restrict (cubeSet (nbr S δ))) := by
  have hsub : cubeSet (nbr S δ) ⊆ cubeSet (originCube d 0) :=
    subset_trans (cubeSet_nbr_subset_overlap S δ)
      (ScalarOverlap.mem_centersAtDepth_iff.mp hS).2
  have hle : volume.restrict (cubeSet (nbr S δ)) ≤ volume.restrict (cubeSet (originCube d 0)) :=
    Measure.restrict_mono hsub le_rfl
  exact MemLp.mono_measure hle (grad_memLp_cube H i)

theorem blockTheta_bdd {d : ℕ} (H : H1Function (openCubeSet (originCube d 0))) {j : ℕ}
    {S : TriadicCube d} (hS : S ∈ ScalarOverlap.centersAtDepth (originCube d 0) j) (i : Fin d) :
    ∃ B : ℝ, ∀ k, blockTheta H S i k ≤ B := by
  refine ⟨((3 : ℝ) ^ d)⁻¹ * ∑ δ : Fin d → Fin 3,
    cubeAverage (nbr S δ) (fun x => (H.grad x i) ^ 2), fun k => ?_⟩
  unfold blockTheta
  rw [theta_block S k (fun x => H.grad x i)]
  gcongr with δ _
  exact theta_le_cubeAverage_sq _ _ _ (memLp_grad_nbr H hS i δ)

theorem integrableOn_grad_translate {d : ℕ} (H : H1Function (openCubeSet (originCube d 0))) {j : ℕ}
    {S : TriadicCube d} (hS : S ∈ ScalarOverlap.centersAtDepth (originCube d 0) j) (i : Fin d) :
    IntegrableOn (fun x => H.grad (x + cubeCenter S) i)
      (cubeSet (originCube d (S.scale + 1))) volume := by
  have hg : IntegrableOn (fun x => H.grad x i) (ScalarOverlap.cubeSet S) volume :=
    (integrableOn_grad_cube H i).mono_set (ScalarOverlap.mem_centersAtDepth_iff.mp hS).2
  rw [cubeSet_overlap_eq_translate S] at hg
  have hmp := measurePreserving_add_right (volume : Measure (Vec d)) (cubeCenter S)
  have hme : MeasurableEmbedding (fun x : Vec d => x + cubeCenter S) :=
    (Homeomorph.addRight (cubeCenter S)).measurableEmbedding
  have h := (hmp.integrableOn_comp_preimage hme (f := fun x => H.grad x i)
    (s := translateSet (cubeCenter S) (cubeSet (originCube d (S.scale + 1))))).mpr hg
  rwa [preimage_addRight_translateSet_eq] at h

theorem partial_circ_le {d : ℕ} (H : H1Function (openCubeSet (originCube d 0))) {j : ℕ}
    {S : TriadicCube d} (hS : S ∈ ScalarOverlap.centersAtDepth (originCube d 0) j) (i : Fin d)
    (N : ℕ) :
    ∑ k ∈ Finset.range (N + 2),
        (cubeScaleFactor (originCube d (S.scale + 1)) / (3 : ℝ) ^ k) *
          Real.sqrt (theta (originCube d (S.scale + 1)) k
            (fun x => H.grad (x + cubeCenter S) i)) ≤
      ∑ k ∈ Finset.range (N + 1), 4 * ((3 : ℝ) ^ (j + 1 + k))⁻¹ * Real.sqrt (blockTheta H S i k) := by
  set Q' := originCube d (S.scale + 1) with hQ'
  set g : Vec d → ℝ := fun x => H.grad (x + cubeCenter S) i with hg
  have hsc : cubeScaleFactor Q' = ((3 : ℝ) ^ j)⁻¹ := by
    have h1 := centers_scale hS
    have h2 : S.scale + 1 = -(j : ℤ) := h1
    simp only [hQ', cubeScaleFactor_originCube, h2, zpow_neg, zpow_natCast]
  set T : ℕ → ℝ := fun k => ((3 : ℝ) ^ (j + 1 + k))⁻¹ * Real.sqrt (blockTheta H S i k) with hT
  have hT0 : ∀ k, 0 ≤ T k := fun k => mul_nonneg (inv_nonneg.mpr (by positivity)) (Real.sqrt_nonneg _)
  have hblock : ∀ k, blockTheta H S i k = theta Q' (k + 1) g := fun k => rfl
  have hmono : theta Q' 0 g ≤ theta Q' 1 g :=
    theta_mono Q' 0 g (integrableOn_grad_translate H hS i)
  rw [Finset.sum_range_succ']
  have hterm : ∀ k : ℕ, (cubeScaleFactor Q' / (3 : ℝ) ^ (k + 1)) * Real.sqrt (theta Q' (k + 1) g) = T k := by
    intro k
    rw [hsc, hT]
    simp only [hblock]
    rw [pow_add (3 : ℝ) (j + 1) k, pow_succ (3 : ℝ) j, pow_succ (3 : ℝ) k]
    field_simp
  have hzero : (cubeScaleFactor Q' / (3 : ℝ) ^ 0) * Real.sqrt (theta Q' 0 g) ≤ 3 * T 0 := by
    have h1 : Real.sqrt (theta Q' 0 g) ≤ Real.sqrt (theta Q' 1 g) := Real.sqrt_le_sqrt hmono
    have h2 : (cubeScaleFactor Q' / (3 : ℝ) ^ 0) = 3 * ((3 : ℝ) ^ (j + 1 + 0))⁻¹ := by
      rw [hsc]; simp only [pow_zero, div_one, add_zero, pow_succ]; field_simp
    rw [h2, hT]
    simp only [hblock, zero_add]
    calc 3 * ((3 : ℝ) ^ (j + 1 + 0))⁻¹ * Real.sqrt (theta Q' 0 g)
        ≤ 3 * ((3 : ℝ) ^ (j + 1 + 0))⁻¹ * Real.sqrt (theta Q' 1 g) := by gcongr
      _ = 3 * (((3 : ℝ) ^ (j + 1 + 0))⁻¹ * Real.sqrt (theta Q' 1 g)) := by ring
  have hsum : ∑ k ∈ Finset.range (N + 1),
      (cubeScaleFactor Q' / (3 : ℝ) ^ (k + 1)) * Real.sqrt (theta Q' (k + 1) g) =
      ∑ k ∈ Finset.range (N + 1), T k := Finset.sum_congr rfl fun k _ => hterm k
  have hT0le : T 0 ≤ ∑ k ∈ Finset.range (N + 1), T k :=
    Finset.single_le_sum (f := T) (fun k _ => hT0 k) (Finset.mem_range.mpr (Nat.succ_pos N))
  calc ∑ k ∈ Finset.range (N + 1),
        (cubeScaleFactor Q' / (3 : ℝ) ^ (k + 1)) * Real.sqrt (theta Q' (k + 1) g) +
        (cubeScaleFactor Q' / (3 : ℝ) ^ 0) * Real.sqrt (theta Q' 0 g)
      ≤ ∑ k ∈ Finset.range (N + 1), T k + 3 * T 0 := by rw [hsum]; gcongr
    _ ≤ ∑ k ∈ Finset.range (N + 1), T k + 3 * ∑ k ∈ Finset.range (N + 1), T k := by gcongr
    _ = ∑ k ∈ Finset.range (N + 1), 4 * ((3 : ℝ) ^ (j + 1 + k))⁻¹ * Real.sqrt (blockTheta H S i k) := by
      rw [show ∑ k ∈ Finset.range (N + 1), 4 * ((3 : ℝ) ^ (j + 1 + k))⁻¹ * Real.sqrt (blockTheta H S i k)
          = 4 * ∑ k ∈ Finset.range (N + 1), T k by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by rw [hT]; ring]
      ring

theorem series_term_summable {d : ℕ} (H : H1Function (openCubeSet (originCube d 0))) (j : ℕ)
    (S : TriadicCube d) (hS : S ∈ ScalarOverlap.centersAtDepth (originCube d 0) j) (i : Fin d) :
    Summable (fun k : ℕ => 4 * ((3 : ℝ) ^ (j + 1 + k))⁻¹ * Real.sqrt (blockTheta H S i k)) := by
  obtain ⟨B, hB⟩ := blockTheta_bdd H hS i
  have hg : Summable (fun k : ℕ =>
      (4 * Real.sqrt B * ((3 : ℝ) ^ (j + 1))⁻¹) * ((1 / 3 : ℝ) ^ k)) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hg
  · positivity
  · have h1 : Real.sqrt (blockTheta H S i k) ≤ Real.sqrt B := Real.sqrt_le_sqrt (hB k)
    calc 4 * ((3 : ℝ) ^ (j + 1 + k))⁻¹ * Real.sqrt (blockTheta H S i k)
        ≤ 4 * ((3 : ℝ) ^ (j + 1 + k))⁻¹ * Real.sqrt B := by gcongr
      _ = (4 * Real.sqrt B * ((3 : ℝ) ^ (j + 1))⁻¹) * ((1 / 3 : ℝ) ^ k) := by
        rw [pow_add (3 : ℝ) (j + 1) k, mul_inv, one_div, inv_pow]
        ring

theorem circNorm_le_tsum {d : ℕ} (H : H1Function (openCubeSet (originCube d 0))) {j : ℕ}
    {S : TriadicCube d} (hS : S ∈ ScalarOverlap.centersAtDepth (originCube d 0) j) (i : Fin d) :
    cubeBesovCircNorm (originCube d (S.scale + 1)) 1 2 1 (fun x => H.grad (x + cubeCenter S) i) ≤
      ∑' k : ℕ, 4 * ((3 : ℝ) ^ (j + 1 + k))⁻¹ * Real.sqrt (blockTheta H S i k) := by
  refine cubeBesovCircNorm_le _ _ _ (fun N => (partial_circ_le H hS i N).trans ?_)
  exact (series_term_summable H j S hS i).sum_le_tsum (Finset.range (N + 1))
    (fun k _ => mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr (by positivity)))
      (Real.sqrt_nonneg _))

theorem osc_le_tsum {d : ℕ} [NeZero d] (H : H1Function (openCubeSet (originCube d 0))) {j : ℕ}
    {S : TriadicCube d} (hS : S ∈ ScalarOverlap.centersAtDepth (originCube d 0) j) :
    cubeBesovOverlapOscillation S 2 H.toFun ≤
      SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov.oscillationMultiscalePoincareConstant d *
        ∑ i : Fin d, ∑' k : ℕ, 4 * ((3 : ℝ) ^ (j + 1 + k))⁻¹ * Real.sqrt (blockTheta H S i k) := by
  have hsub : ScalarOverlap.openCubeSet S ⊆ openCubeSet (originCube d 0) :=
    ScalarOverlap.openCubeSet_subset_openCubeSet_of_mem_centersAtDepth hS
  refine (overlap_local_poincare (isOpen_openCubeSet _) H S hsub).trans ?_
  apply mul_le_mul_of_nonneg_left _
    (SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov.oscillationMultiscalePoincareConstant_nonneg d)
  exact Finset.sum_le_sum fun i _ => circNorm_le_tsum H hS i

theorem block_avg_le {d : ℕ} (H : H1Function (openCubeSet (originCube d 0))) (j : ℕ) (i : Fin d)
    (k : ℕ) :
    ((ScalarOverlap.centersAtDepth (originCube d 0) j).card : ℝ)⁻¹ *
        ∑ S ∈ ScalarOverlap.centersAtDepth (originCube d 0) j, blockTheta H S i k ≤
      (3 : ℝ) ^ d * theta (originCube d 0) (j + 1 + k) (fun x => H.grad x i) :=
  avg_theta_block_le j k (fun x => H.grad x i)

/-- Root mean square over the centres of one series term. -/
theorem block_rms_le {d : ℕ} (H : H1Function (openCubeSet (originCube d 0))) (j : ℕ) (i : Fin d)
    (k : ℕ) :
    Real.sqrt (((ScalarOverlap.centersAtDepth (originCube d 0) j).card : ℝ)⁻¹ *
        ∑ S ∈ ScalarOverlap.centersAtDepth (originCube d 0) j,
          (4 * ((3 : ℝ) ^ (j + 1 + k))⁻¹ * Real.sqrt (blockTheta H S i k)) ^ 2) ≤
      4 * ((3 : ℝ) ^ (j + 1 + k))⁻¹ * Real.sqrt ((3 : ℝ) ^ d) * gradX H (j + 1 + k) := by
  set 𝒮 := ScalarOverlap.centersAtDepth (originCube d 0) j with h𝒮
  set w : ℝ := ((3 : ℝ) ^ (j + 1 + k))⁻¹ with hw
  have hw0 : 0 ≤ w := inv_nonneg.mpr (by positivity)
  have hsq : ∀ S : TriadicCube d,
      (4 * w * Real.sqrt (blockTheta H S i k)) ^ 2 = (4 * w) ^ 2 * blockTheta H S i k := by
    intro S
    rw [mul_pow, Real.sq_sqrt (blockTheta_nonneg H S i k)]
  simp_rw [hsq]
  rw [← Finset.mul_sum]
  have hav := block_avg_le H j i k
  have hθ := sqrt_theta_le_gradX H i (j + 1 + k)
  have hinner : ((𝒮.card : ℕ) : ℝ)⁻¹ * ((4 * w) ^ 2 * ∑ S ∈ 𝒮, blockTheta H S i k) ≤
      (4 * w) ^ 2 * ((3 : ℝ) ^ d * theta (originCube d 0) (j + 1 + k) (fun x => H.grad x i)) := by
    calc ((𝒮.card : ℕ) : ℝ)⁻¹ * ((4 * w) ^ 2 * ∑ S ∈ 𝒮, blockTheta H S i k)
        = (4 * w) ^ 2 * (((𝒮.card : ℕ) : ℝ)⁻¹ * ∑ S ∈ 𝒮, blockTheta H S i k) := by ring
      _ ≤ (4 * w) ^ 2 * ((3 : ℝ) ^ d * theta (originCube d 0) (j + 1 + k) (fun x => H.grad x i)) :=
          mul_le_mul_of_nonneg_left hav (sq_nonneg _)
  refine (Real.sqrt_le_sqrt hinner).trans ?_
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity),
    Real.sqrt_mul (by positivity)]
  calc 4 * w * (Real.sqrt ((3 : ℝ) ^ d) *
        Real.sqrt (theta (originCube d 0) (j + 1 + k) (fun x => H.grad x i)))
      ≤ 4 * w * (Real.sqrt ((3 : ℝ) ^ d) * gradX H (j + 1 + k)) := by gcongr
    _ = 4 * w * Real.sqrt ((3 : ℝ) ^ d) * gradX H (j + 1 + k) := by ring

theorem rms_series_summable {d : ℕ} (H : H1Function (openCubeSet (originCube d 0))) (j : ℕ)
    (_i : Fin d) :
    Summable (fun k : ℕ => 4 * ((3 : ℝ) ^ (j + 1 + k))⁻¹ * Real.sqrt ((3 : ℝ) ^ d) *
      gradX H (j + 1 + k)) := by
  obtain ⟨G, hG⟩ := gradX_bdd H
  have h := (summable_shift j (gradX H) (gradX_nonneg H) G hG).mul_left
    (4 * Real.sqrt ((3 : ℝ) ^ d))
  refine h.congr (fun k => ?_)
  ring

/-- **Depth bound.** -/
theorem depth_bound {d : ℕ} [NeZero d] (H : H1Function (openCubeSet (originCube d 0))) (j : ℕ) :
    Real.sqrt (ScalarOverlap.centersAverage (originCube d 0) j
        (fun S => (cubeBesovOverlapOscillation S 2 H.toFun) ^ 2)) ≤
      Cd d * ∑' k : ℕ, ((3 : ℝ) ^ (j + 1 + k))⁻¹ * gradX H (j + 1 + k) := by
  classical
  set 𝒮 := ScalarOverlap.centersAtDepth (originCube d 0) j with h𝒮
  set c : ℝ := ((𝒮.card : ℕ) : ℝ)⁻¹ with hc
  have hc0 : 0 ≤ c := inv_nonneg.mpr (Nat.cast_nonneg _)
  set Cp : ℝ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov.oscillationMultiscalePoincareConstant d with hCp
  have hCp0 : 0 ≤ Cp :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov.oscillationMultiscalePoincareConstant_nonneg d
  -- the series along each centre and coordinate
  let a : Fin d → ℕ → TriadicCube d → ℝ := fun i k S =>
    4 * ((3 : ℝ) ^ (j + 1 + k))⁻¹ * Real.sqrt (blockTheta H S i k)
  have ha0 : ∀ i k S, 0 ≤ a i k S := fun i k S =>
    mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr (by positivity))) (Real.sqrt_nonneg _)
  have hoscnn : ∀ S, 0 ≤ cubeBesovOverlapOscillation S 2 H.toFun := fun S =>
    cubeBesovOverlapOscillation_nonneg S 2 H.toFun
  -- step 1: pointwise bound for the oscillations
  have h1 : Real.sqrt (ScalarOverlap.centersAverage (originCube d 0) j
        (fun S => (cubeBesovOverlapOscillation S 2 H.toFun) ^ 2)) ≤
      Real.sqrt (c * ∑ S ∈ 𝒮, (Cp * ∑ i : Fin d, ∑' k, a i k S) ^ 2) := by
    apply Real.sqrt_le_sqrt
    unfold ScalarOverlap.centersAverage
    apply mul_le_mul_of_nonneg_left _ hc0
    apply Finset.sum_le_sum
    intro S hS
    exact pow_le_pow_left₀ (hoscnn S) (osc_le_tsum H hS) 2
  -- step 2: Minkowski over the coordinates
  have h2 : Real.sqrt (c * ∑ S ∈ 𝒮, (Cp * ∑ i : Fin d, ∑' k, a i k S) ^ 2) ≤
      Cp * ∑ i : Fin d, Real.sqrt (c * ∑ S ∈ 𝒮, (∑' k, a i k S) ^ 2) := by
    have := sqrt_weighted_sq_sum_le 𝒮 (Finset.univ : Finset (Fin d)) c hc0
      (fun i S => ∑' k, a i k S)
    calc Real.sqrt (c * ∑ S ∈ 𝒮, (Cp * ∑ i : Fin d, ∑' k, a i k S) ^ 2)
        = Cp * Real.sqrt (c * ∑ S ∈ 𝒮, (∑ i : Fin d, ∑' k, a i k S) ^ 2) :=
          sqrt_weighted_mul_left 𝒮 c Cp hc0 hCp0 _
      _ ≤ Cp * ∑ i : Fin d, Real.sqrt (c * ∑ S ∈ 𝒮, (∑' k, a i k S) ^ 2) :=
          mul_le_mul_of_nonneg_left this hCp0
  -- step 3: Minkowski over the series and the block bound
  have h3 : ∀ i : Fin d, Real.sqrt (c * ∑ S ∈ 𝒮, (∑' k, a i k S) ^ 2) ≤
      ∑' k : ℕ, 4 * ((3 : ℝ) ^ (j + 1 + k))⁻¹ * Real.sqrt ((3 : ℝ) ^ d) *
        gradX H (j + 1 + k) := by
    intro i
    have hb : Summable (fun k => Real.sqrt (c * ∑ S ∈ 𝒮, (a i k S) ^ 2)) :=
      Summable.of_nonneg_of_le (fun k => Real.sqrt_nonneg _)
        (fun k => block_rms_le H j i k) (rms_series_summable H j i)
    refine (sqrt_weighted_sq_tsum_le 𝒮 c hc0 (a i) (fun k S => ha0 i k S)
      (fun S hS => series_term_summable H j S hS i) hb).trans ?_
    exact hb.tsum_le_tsum (fun k => block_rms_le H j i k) (rms_series_summable H j i)
  -- step 4: sum over the coordinates and factor the constants
  have h4 : ∑' k : ℕ, 4 * ((3 : ℝ) ^ (j + 1 + k))⁻¹ * Real.sqrt ((3 : ℝ) ^ d) *
        gradX H (j + 1 + k) =
      4 * Real.sqrt ((3 : ℝ) ^ d) * ∑' k : ℕ, ((3 : ℝ) ^ (j + 1 + k))⁻¹ * gradX H (j + 1 + k) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    ring
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ Cp * ∑ _i : Fin d, (4 * Real.sqrt ((3 : ℝ) ^ d) *
          ∑' k : ℕ, ((3 : ℝ) ^ (j + 1 + k))⁻¹ * gradX H (j + 1 + k)) := by
        apply mul_le_mul_of_nonneg_left _ hCp0
        apply Finset.sum_le_sum
        intro i _
        rw [← h4]
        exact h3 i
    _ = Cd d * ∑' k : ℕ, ((3 : ℝ) ^ (j + 1 + k))⁻¹ * gradX H (j + 1 + k) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        unfold Cd
        ring

end

end SubdiffusiveProcess.Besov.Detach
