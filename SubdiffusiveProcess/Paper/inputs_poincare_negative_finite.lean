module

public import SubdiffusiveProcess.Paper.in_poincare
public import Homogenization.Book.Ch03.Theorems.CoarsePoincare.Finite
public import Homogenization.Deterministic.CoarsePoincareRHS.TerminalBounds

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise
open SubdiffusiveProcess
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

private theorem aux_inputs_poincare_negative_finite_pullback_memLp
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (f : DomainL2 (centeredCube z r hr)) :
    MeasureTheory.MemLp (fun x : SpatialCoordinates d =>
      f (fun j => z j + r * x j)) (2 : ℝ≥0∞)
      (Homogenization.normalizedCubeMeasure (Homogenization.originCube d 0)) := by
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d 0
  let O : Set (SpatialCoordinates d) := Homogenization.openCubeSet Q
  let T : SpatialCoordinates d → SpatialCoordinates d :=
    fun x j => z j + r * x j
  have hset : Homogenization.translateSet z (r • O) =
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    rw [centeredCube_eq_pi z hr]
    ext x
    rw [Homogenization.mem_translateSet_iff_sub_mem]
    constructor
    · intro hx
      rw [Set.mem_smul_set] at hx
      rcases hx with ⟨y, hy, hxy⟩
      intro i _
      have hyi := (Homogenization.mem_openCubeSet_originCube_iff
        (m := 0) (x := y)).mp hy i
      have hx_i : r * y i = x i - z i := by
        simpa [Pi.smul_apply, smul_eq_mul] using congrFun hxy i
      norm_num at hyi
      constructor
      · have hlo := mul_lt_mul_of_pos_left hyi.1 hr
        linarith
      · have hhi := mul_lt_mul_of_pos_left hyi.2 hr
        linarith
    · intro hx
      rw [Set.mem_smul_set]
      refine ⟨fun i => (x i - z i) / r, ?_, ?_⟩
      · apply (Homogenization.mem_openCubeSet_originCube_iff
          (m := 0) (x := fun i => (x i - z i) / r)).mpr
        intro i
        rcases hx i (Set.mem_univ i) with ⟨hlo, hhi⟩
        constructor
        · have h : (-1 / 2 : ℝ) < (x i - z i) / r :=
            (lt_div_iff₀ hr).2 (by linarith)
          norm_num at h ⊢
          exact h
        · have h : (x i - z i) / r < (1 / 2 : ℝ) :=
            (div_lt_iff₀ hr).2 (by linarith)
          norm_num at h ⊢
          exact h
      · ext i
        simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
        field_simp [hr.ne']
  have hmap_scale := Homogenization.map_smul_volume_restrict
    (d := d) (a := r) hr O
  have hmap_translate :=
    (Homogenization.measurePreserving_addRight_restrict_translateSet z (r • O)).map_eq
  have hT_eq : T = (fun y : SpatialCoordinates d => y + z) ∘
      (fun x : SpatialCoordinates d => r • x) := by
    funext x
    ext i
    simp [T, Pi.smul_apply, smul_eq_mul, add_comm]
  have hTmeas : Measurable T := by
    rw [hT_eq]
    exact (measurable_id.add_const z).comp (measurable_const_smul r)
  have hmap : MeasureTheory.Measure.map T
      (MeasureTheory.volume.restrict O) =
        ENNReal.ofReal ((r ^ d)⁻¹) •
          MeasureTheory.volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    let A : SpatialCoordinates d → SpatialCoordinates d := fun y => y + z
    let S : SpatialCoordinates d → SpatialCoordinates d := fun x => r • x
    calc
      MeasureTheory.Measure.map T (MeasureTheory.volume.restrict O) =
          MeasureTheory.Measure.map (A ∘ S) (MeasureTheory.volume.restrict O) := by
            rw [hT_eq]
      _ = MeasureTheory.Measure.map A
          (MeasureTheory.Measure.map S (MeasureTheory.volume.restrict O)) := by
            symm
            exact MeasureTheory.Measure.map_map (measurable_id.add_const z)
              (measurable_const_smul r)
      _ = MeasureTheory.Measure.map A
          (ENNReal.ofReal ((r ^ d)⁻¹) • MeasureTheory.volume.restrict (r • O)) := by
            rw [hmap_scale]
      _ = ENNReal.ofReal ((r ^ d)⁻¹) •
          MeasureTheory.Measure.map A (MeasureTheory.volume.restrict (r • O)) := by
            rw [MeasureTheory.Measure.map_smul _ (show Measurable A from by simpa only [A] using! measurable_id.add_const z).aemeasurable]
      _ = ENNReal.ofReal ((r ^ d)⁻¹) •
          MeasureTheory.volume.restrict (Homogenization.translateSet z (r • O)) := by
            rw [show A = (fun y : SpatialCoordinates d => y + z) by rfl,
              hmap_translate]
      _ = ENNReal.ofReal ((r ^ d)⁻¹) •
          MeasureTheory.volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d)) := by rw [hset]
  have hroot :
      Homogenization.normalizedCubeMeasure Q = MeasureTheory.volume.restrict O := by
    rw [Homogenization.normalizedCubeMeasure, Homogenization.cubeVolume_originCube_zero]
    simp only [inv_one, ENNReal.ofReal_one, one_smul, Homogenization.cubeMeasure]
    exact Homogenization.volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q
  have hf : MeasureTheory.MemLp f (2 : ℝ≥0∞)
      (MeasureTheory.volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d))) := Lp.memLp f
  have hfc : MeasureTheory.MemLp f (2 : ℝ≥0∞)
      (ENNReal.ofReal ((r ^ d)⁻¹) • MeasureTheory.volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    hf.smul_measure ENNReal.ofReal_ne_top
  rw [← hmap] at hfc
  have hpull : MeasureTheory.MemLp (f ∘ T) (2 : ℝ≥0∞)
      (MeasureTheory.volume.restrict O) :=
    hfc.comp_of_map hTmeas.aemeasurable
  rw [← hroot] at hpull
  simpa [T, Function.comp_def] using hpull

private theorem aux_inputs_poincare_negative_finite_bddAbove
    {d : ℕ} [NeZero d] (F : Homogenization.Vec d → Homogenization.Vec d)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞)
      (Homogenization.normalizedCubeMeasure (Homogenization.originCube d 0)))
    (s q : ℝ) (hs : 0 < s) (hq : 1 ≤ q) :
    BddAbove (Set.range (fun N : ℕ =>
      Homogenization.Book.Ch03.negativeBesovVectorPartialNormFinite
        (Homogenization.originCube d 0) s q N F)) := by
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d 0
  let E : ℝ := Homogenization.cubeAverage Q
    (fun x => Homogenization.vecNormSq (F x))
  let W : ℕ → ℝ := fun n => Homogenization.Book.Ch02.geometricWeight s q n
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hsq : 0 < s * q := mul_pos hs hqpos
  have hE : 0 ≤ E := by
    apply Homogenization.cubeAverage_nonneg_of_nonneg_on
    intro x hx
    exact Homogenization.vecNormSq_nonneg (F x)
  have hdepth (j : ℕ) :
      Homogenization.Book.Ch03.negativeBesovVectorDepthAverage Q F j ≤ E := by
    simpa [E, Q,
      Homogenization.Book.Ch03.negativeBesovVectorDepthAverage_eq_old] using
      (Homogenization.cubeBesovNegativeVectorDepthAverage_le_cubeAverage_vecNormSq_of_memLp
        Q F j hF)
  have hW_nonneg (n : ℕ) : 0 ≤ W n := by
    dsimp [W]
    have h := Homogenization.geometricWeight_nonneg n (mul_nonneg hs.le hqpos.le)
    simpa [Homogenization.Book.Ch02.geometricWeight_eq_old] using h
  have hsumW : Summable W := by
    simpa [W, Homogenization.Book.Ch02.geometricWeight_eq_old] using! Homogenization.summable_geometricWeight hsq
  have htsumW : (∑' n : ℕ, W n) = 1 := by
    simpa [W, Homogenization.Book.Ch02.geometricWeight_eq_old] using! Homogenization.tsum_geometricWeight_eq_one hsq
  have hdisc_pos : 0 < Homogenization.Book.Ch02.geometricDiscount s q := by
    exact Homogenization.Book.Ch02.book_geometricDiscount_pos hsq
  let B : ℝ := Real.rpow
    ((Homogenization.Book.Ch02.geometricDiscount s q)⁻¹ *
      Real.rpow E (q / 2)) (1 / q)
  refine ⟨B, ?_⟩
  rintro y ⟨N, rfl⟩
  have hterm (j : ℕ) :
      Real.rpow (Homogenization.Book.Ch03.negativeBesovVectorDepthSeminorm
        Q s F j) q ≤
        (Homogenization.Book.Ch02.geometricDiscount s q)⁻¹ * W j *
          Real.rpow E (q / 2) := by
    have hweight : 0 ≤ Real.rpow (3 : ℝ) (-s * (j : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hdepth_le :
        Homogenization.Book.Ch03.negativeBesovVectorDepthSeminorm Q s F j ≤
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) * Real.sqrt E := by
      unfold Homogenization.Book.Ch03.negativeBesovVectorDepthSeminorm
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hdepth j)) hweight
    have hpow_weight :
        Real.rpow (Real.rpow (3 : ℝ) (-s * (j : ℝ))) q =
          Real.rpow (3 : ℝ) (-s * (j : ℝ) * q) := by
      exact (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) (-s * (j : ℝ)) q).symm
    have hsqrt_pow : Real.rpow (Real.sqrt E) q = Real.rpow E (q / 2) := by
      calc
        Real.rpow (Real.sqrt E) q = Real.rpow (Real.rpow E (1 / 2 : ℝ)) q := by
          exact congrArg (fun t => Real.rpow t q) (Real.sqrt_eq_rpow E)
        _ = Real.rpow E ((1 / 2 : ℝ) * q) := by
          exact (Real.rpow_mul hE (1 / 2 : ℝ) q).symm
        _ = Real.rpow E (q / 2) := by congr 1; ring
    calc
      Real.rpow (Homogenization.Book.Ch03.negativeBesovVectorDepthSeminorm
          Q s F j) q ≤
        Real.rpow (Real.rpow (3 : ℝ) (-s * (j : ℝ)) * Real.sqrt E) q :=
          Real.rpow_le_rpow
            (Homogenization.Book.Ch03.negativeBesovVectorDepthSeminorm_nonneg Q s F j)
            hdepth_le hqpos.le
      _ = Real.rpow (Real.rpow (3 : ℝ) (-s * (j : ℝ))) q *
          Real.rpow (Real.sqrt E) q :=
        Real.mul_rpow hweight (Real.sqrt_nonneg E)
      _ = (Homogenization.Book.Ch02.geometricDiscount s q)⁻¹ * W j *
          Real.rpow E (q / 2) := by
        rw [hpow_weight, hsqrt_pow,
          Homogenization.Book.Ch03.rpow_inv_geometricDiscount_mul_geometricWeight hs hqpos j]
  have hfinite_le_tsum (N : ℕ) :
      Finset.sum (Finset.range (N + 1)) W ≤ ∑' n : ℕ, W n :=
    hsumW.sum_le_tsum (Finset.range (N + 1)) (fun n _ => hW_nonneg n)
  have hsum_le (N : ℕ) :
      Finset.sum (Finset.range (N + 1))
          (fun j => Real.rpow
            (Homogenization.Book.Ch03.negativeBesovVectorDepthSeminorm Q s F j) q) ≤
        (Homogenization.Book.Ch02.geometricDiscount s q)⁻¹ *
          Real.rpow E (q / 2) := by
    calc
      Finset.sum (Finset.range (N + 1))
          (fun j => Real.rpow
            (Homogenization.Book.Ch03.negativeBesovVectorDepthSeminorm Q s F j) q) ≤
          Finset.sum (Finset.range (N + 1))
            (fun j => (Homogenization.Book.Ch02.geometricDiscount s q)⁻¹ *
              W j * Real.rpow E (q / 2)) :=
        Finset.sum_le_sum (fun j _ => hterm j)
      _ = (Homogenization.Book.Ch02.geometricDiscount s q)⁻¹ *
          Finset.sum (Finset.range (N + 1)) W * Real.rpow E (q / 2) := by
        calc
          _ = Finset.sum (Finset.range (N + 1))
              (fun j => ((Homogenization.Book.Ch02.geometricDiscount s q)⁻¹ *
                Real.rpow E (q / 2)) * W j) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = ((Homogenization.Book.Ch02.geometricDiscount s q)⁻¹ *
                Real.rpow E (q / 2)) * Finset.sum (Finset.range (N + 1)) W := by
            rw [Finset.mul_sum]
          _ = (Homogenization.Book.Ch02.geometricDiscount s q)⁻¹ *
              Finset.sum (Finset.range (N + 1)) W * Real.rpow E (q / 2) := by ring
      _ ≤ (Homogenization.Book.Ch02.geometricDiscount s q)⁻¹ *
          (∑' n : ℕ, W n) * Real.rpow E (q / 2) := by
        have hscaled := mul_le_mul_of_nonneg_left (hfinite_le_tsum N)
          (inv_nonneg.mpr hdisc_pos.le)
        exact mul_le_mul_of_nonneg_right hscaled (Real.rpow_nonneg hE _)
      _ = (Homogenization.Book.Ch02.geometricDiscount s q)⁻¹ *
          Real.rpow E (q / 2) := by rw [htsumW]; ring
  unfold Homogenization.Book.Ch03.negativeBesovVectorPartialNormFinite
  have hleft : 0 ≤ Finset.sum (Finset.range (N + 1))
      (fun j => Real.rpow
        (Homogenization.Book.Ch03.negativeBesovVectorDepthSeminorm Q s F j) q) :=
    Finset.sum_nonneg (fun j _ => Real.rpow_nonneg
      (Homogenization.Book.Ch03.negativeBesovVectorDepthSeminorm_nonneg Q s F j) _)
  have hpow := Real.rpow_le_rpow hleft (hsum_le N) (one_div_nonneg.mpr hqpos.le)
  simpa [B, Q] using hpow

theorem inputs_poincare_negative_finite (d : ℕ) (hd : 2 ≤ d) :
    (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (u : SobolevData (centeredCube z r hr)) (s : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ (q : ℝ), 1 ≤ q →
    BddAbove (Set.range (fun N : ℕ =>
      Homogenization.Book.Ch03.negativeBesovVectorPartialNormFinite
        (Homogenization.originCube d 0) s q N
        (fun x i => u.2 i (fun j => z j + r * x j))))) := by
  intro z r hr u s hs q hq
  let F : Homogenization.Vec d → Homogenization.Vec d :=
    fun x i => u.2 i (fun j => z j + r * x j)
  have hFhilbert : MeasureTheory.MemLp
      (fun x => Homogenization.HilbertVec.ofVec (F x)) (2 : ℝ≥0∞)
      (Homogenization.normalizedCubeMeasure (Homogenization.originCube d 0)) := by
    rw [MeasureTheory.memLp_piLp_iff]
    intro i
    simpa only [F, Homogenization.HilbertVec.ofVec, PiLp.toLp_apply] using
      aux_inputs_poincare_negative_finite_pullback_memLp d z r hr (u.2 i)
  have hF : MeasureTheory.MemLp F (2 : ℝ≥0∞)
      (Homogenization.normalizedCubeMeasure (Homogenization.originCube d 0)) := by
    simpa [F, Homogenization.HilbertVec.continuousLinearEquivVec_apply,
      Homogenization.HilbertVec.toVec, Homogenization.HilbertVec.ofVec] using
      hFhilbert.continuousLinearMap_comp
        (Homogenization.HilbertVec.continuousLinearEquivVec d).toContinuousLinearMap
  let : NeZero d := ⟨by omega⟩
  exact aux_inputs_poincare_negative_finite_bddAbove F hF s q hs.1 hq

end SubdiffusiveProcess.Paper

