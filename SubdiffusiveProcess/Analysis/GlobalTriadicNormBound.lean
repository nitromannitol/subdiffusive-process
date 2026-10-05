module

public import SubdiffusiveProcess.Analysis.GlobalTriadicSummableIncrements
public import SubdiffusiveProcess.Analysis.GlobalTriadicAverages
public import SubdiffusiveProcess.Analysis.TriadicGrowthCoefficient
public import SubdiffusiveProcess.Main.CubeFractionalL2Norm
public import SubdiffusiveProcess.Main.HalfFractionalOrder
public import SubdiffusiveProcess.Analysis.GlobalTriadicL2Limit
public import Mathlib


@[expose] public section

namespace SubdiffusiveProcess

theorem trace_norm_two_term_bound
    (r V M n I L A G N : ℝ)
    (hr : 0 < r) (hV : 0 < V) (hM : 0 ≤ M) (hn : 0 ≤ n) (hnM : n ≤ M)
    (_hI : 0 ≤ I) (hL : 0 ≤ L) (hA : 0 ≤ A) (hG : 0 ≤ G)
    (hN : N = Real.sqrt I / (Real.sqrt 2 * Real.sqrt V) +
      L / (Real.sqrt r * Real.sqrt V))
    (hbound : G ≤ Real.sqrt (n / V) * L + Real.sqrt (M * I) * A) :
    G ^ 2 ≤ (Real.sqrt r + Real.sqrt (2 * V) * A) ^ 2 * M * N ^ 2 := by
  have hsqrtr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hsqrtV : 0 < Real.sqrt V := Real.sqrt_pos.2 hV
  have hsqrt2 : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hdenI : 0 < Real.sqrt 2 * Real.sqrt V := mul_pos hsqrt2 hsqrtV
  have hdenL : 0 < Real.sqrt r * Real.sqrt V := mul_pos hsqrtr hsqrtV
  have htermI : 0 ≤ Real.sqrt I / (Real.sqrt 2 * Real.sqrt V) :=
    div_nonneg (Real.sqrt_nonneg _) (le_of_lt hdenI)
  have htermL : 0 ≤ L / (Real.sqrt r * Real.sqrt V) :=
    div_nonneg hL (le_of_lt hdenL)
  have hNI : Real.sqrt I / (Real.sqrt 2 * Real.sqrt V) ≤ N := by
    rw [hN]
    linarith
  have hNL : L / (Real.sqrt r * Real.sqrt V) ≤ N := by
    rw [hN]
    linarith
  have hNnonneg : 0 ≤ N := le_trans htermI hNI
  have hIroot : Real.sqrt I ≤ Real.sqrt 2 * Real.sqrt V * N := by
    have h := (div_le_iff₀ hdenI).mp hNI
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have hLroot : L ≤ Real.sqrt r * Real.sqrt V * N := by
    have h := (div_le_iff₀ hdenL).mp hNL
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have hnmroot : Real.sqrt n ≤ Real.sqrt M := Real.sqrt_le_sqrt hnM
  have hsqrt_div : Real.sqrt (n / V) = Real.sqrt n / Real.sqrt V := by
    rw [Real.sqrt_div hn]
  have hsqrt_MI : Real.sqrt (M * I) = Real.sqrt M * Real.sqrt I := by
    rw [Real.sqrt_mul hM]
  have hsqrt_2V : Real.sqrt (2 * V) = Real.sqrt 2 * Real.sqrt V := by
    rw [Real.sqrt_mul (by norm_num)]
  have hfirst : Real.sqrt (n / V) * L ≤ Real.sqrt M * Real.sqrt r * N := by
    calc
      Real.sqrt (n / V) * L = (Real.sqrt n / Real.sqrt V) * L := by
        rw [hsqrt_div]
      _ ≤ (Real.sqrt n / Real.sqrt V) *
          (Real.sqrt r * Real.sqrt V * N) :=
        mul_le_mul_of_nonneg_left hLroot
          (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ = Real.sqrt n * Real.sqrt r * N := by
        field_simp [ne_of_gt hsqrtV]
      _ ≤ Real.sqrt M * Real.sqrt r * N := by
        have h := mul_le_mul_of_nonneg_right hnmroot
          (mul_nonneg (Real.sqrt_nonneg r) hNnonneg)
        calc
          Real.sqrt n * Real.sqrt r * N =
              Real.sqrt n * (Real.sqrt r * N) := by ring
          _ ≤ Real.sqrt M * (Real.sqrt r * N) := h
          _ = Real.sqrt M * Real.sqrt r * N := by ring
  have hsecond : Real.sqrt (M * I) * A ≤
      Real.sqrt M * Real.sqrt (2 * V) * A * N := by
    calc
      Real.sqrt (M * I) * A = Real.sqrt M * Real.sqrt I * A := by
        rw [hsqrt_MI]
      _ ≤ Real.sqrt M * (Real.sqrt 2 * Real.sqrt V * N) * A := by
        have h := mul_le_mul_of_nonneg_left hIroot
          (mul_nonneg (Real.sqrt_nonneg M) hA)
        calc
          Real.sqrt M * Real.sqrt I * A =
              (Real.sqrt M * A) * Real.sqrt I := by ring
          _ ≤ (Real.sqrt M * A) * (Real.sqrt 2 * Real.sqrt V * N) := h
          _ = Real.sqrt M * (Real.sqrt 2 * Real.sqrt V * N) * A := by ring
      _ = Real.sqrt M * Real.sqrt (2 * V) * A * N := by
        rw [hsqrt_2V]
        ring
  have hupper : G ≤ Real.sqrt M *
      (Real.sqrt r + Real.sqrt (2 * V) * A) * N := by
    calc
      G ≤ Real.sqrt (n / V) * L + Real.sqrt (M * I) * A := hbound
      _ ≤ Real.sqrt M * Real.sqrt r * N +
          Real.sqrt M * Real.sqrt (2 * V) * A * N :=
        add_le_add hfirst hsecond
      _ = Real.sqrt M * (Real.sqrt r + Real.sqrt (2 * V) * A) * N := by
        ring
  calc
    G ^ 2 ≤ (Real.sqrt M * (Real.sqrt r + Real.sqrt (2 * V) * A) * N) ^ 2 :=
      pow_le_pow_left₀ hG hupper 2
    _ = (Real.sqrt r + Real.sqrt (2 * V) * A) ^ 2 * M * N ^ 2 := by
      calc
        (Real.sqrt M * (Real.sqrt r + Real.sqrt (2 * V) * A) * N) ^ 2 =
            (Real.sqrt M) ^ 2 *
              (Real.sqrt r + Real.sqrt (2 * V) * A) ^ 2 * N ^ 2 := by ring
        _ = (Real.sqrt r + Real.sqrt (2 * V) * A) ^ 2 * M * N ^ 2 := by
          rw [Real.sq_sqrt hM]
          ring


end SubdiffusiveProcess


open MeasureTheory Set TopologicalSpace Filter
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess

theorem globalTriadicAverages_L2_limit_norm_bound
    {d : ℕ} (hd : 2 ≤ d) (Q : Homogenization.TriadicCube d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hroot : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      closure (Homogenization.openCubeSet Q))
    (t : ℝ) (ht : (d : ℝ) - 1 < t) :
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (K : ℝ), 0 ≤ K →
    ∀ (ν : Measure (SpatialCoordinates d)), IsFiniteMeasure ν →
    ν (closure (Homogenization.openCubeSet Q))ᶜ = 0 →
    (∀ x ∈ closure (Homogenization.openCubeSet Q), ∀ ρ : ℝ,
      0 < ρ → ρ ≤ 1 → ν (Metric.ball x ρ) ≤ ENNReal.ofReal (K * ρ ^ t)) →
    ∀ (u : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder),
    MemLp (u.val 0) 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
    (∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal (((u.val 0) y - (u.val 0) x) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ i : Fin d, (y i - x i) ^ 2))) ^ ((d : ℝ) + 1)) ≠ ⊤ →
    let E : ℕ → SpatialCoordinates d → ℝ := fun m x =>
      ∑ k : OddGridIndex d (triadicHalf m),
        (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)).indicator
          (fun _ => averageOn
            (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)) (u.val 0)) x
    ∀ (_hE : ∀ n : ℕ, MemLp (E n) 2 ν)
      (g : SpatialCoordinates d → ℝ), MemLp g 2 ν →
      Tendsto (fun n => eLpNorm (fun x => E n x - g x) 2 ν) atTop (nhds 0) →
      (eLpNorm g 2 ν).toReal ^ 2 ≤
        C * (K + (ν (closure (Homogenization.openCubeSet Q))).toReal) *
          (cubeFractionalL2Norm hd z r hr halfFractionalOrder u) ^ 2 := by
  let a : ℕ → ℝ := fun n => Real.sqrt
      ((((r / (3 : ℝ) ^ n) / 3) ^ t) *
        ((((r / (3 : ℝ) ^ n) / 3) ^ d) *
          ((r / (3 : ℝ) ^ n) ^ d))⁻¹ *
        (Real.sqrt (d : ℝ) * (r / (3 : ℝ) ^ n)) ^ ((d : ℝ) + 1))
  let A : ℝ := ∑' n, a n
  let C : ℝ := (Real.sqrt r +
    Real.sqrt (2 * volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) * A) ^ 2
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro K hK ν hν hsupp hgrowth u hf hI E hE g hg hgtendsto
    let I : ℝ≥0∞ := ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal (((u.val 0) y - (u.val 0) x) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ i : Fin d, (y i - x i) ^ 2))) ^ ((d : ℝ) + 1)
    let Clocal : ℝ := Real.sqrt ((K + ν.real Set.univ) * I.toReal)
    have hkernel :
        (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ENNReal.ofReal (((u.val 0) x - (u.val 0) y) ^ 2) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
              ((d : ℝ) + 1)) = I := by
      unfold I
      rfl
    let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
    have hsum : Summable (fun n : ℕ =>
        (eLpNorm (fun x => E (n + 1) x - E n x) 2 ν).toReal) := by
      simpa only [I] using
        (globalTriadicAverages_summable_increment_eLpNorm_of_finite_kernel
          hd Q z hr hroot K t hK ht ν hν hsupp hgrowth (u.val 0) hf hI)
    have hcoef : Summable a := by
      simpa [a] using (summable_triadicGrowthCoefficients hd r t hr ht)
    have hbound : ∀ n : ℕ,
        (eLpNorm (fun x => E (n + 1) x - E n x) 2 ν).toReal ≤ Clocal * a n := by
      intro n
      let Δ : SpatialCoordinates d → ℝ := fun x => E (n + 1) x - E n x
      have hinc := globalTriadicAverages_memLp_and_increment_bound
        hd Q z hr hroot K t hK ht n ν hν hsupp hgrowth (u.val 0) hf
      dsimp only at hinc
      have hmem : MemLp Δ 2 ν := by simpa [Δ] using hinc.2.1
      have hsq := hinc.2.2
      have hden : 2 * (triadicHalf n : ℝ) + 1 = (3 : ℝ) ^ n :=
        triadic_denominator n
      have hell : r / (2 * (triadicHalf n : ℝ) + 1) = r / (3 : ℝ) ^ n := by
        rw [hden]
      have hsq' : eLpNorm Δ 2 ν ^ (2 : ℕ) ≤
          ENNReal.ofReal ((K + ν.real Set.univ) *
            (((r / (3 : ℝ) ^ n) / 3) ^ t) *
              ((((r / (3 : ℝ) ^ n) / 3) ^ d) *
                ((r / (3 : ℝ) ^ n) ^ d))⁻¹) *
            (ENNReal.ofReal (Real.sqrt d * (r / (3 : ℝ) ^ n))) ^ ((d : ℝ) + 1) * I := by
        simpa [I, hell] using hsq
      let R : ℝ≥0∞ := ENNReal.ofReal ((K + ν.real Set.univ) *
            (((r / (3 : ℝ) ^ n) / 3) ^ t) *
              ((((r / (3 : ℝ) ^ n) / 3) ^ d) *
                ((r / (3 : ℝ) ^ n) ^ d))⁻¹) *
            (ENNReal.ofReal (Real.sqrt d * (r / (3 : ℝ) ^ n))) ^ ((d : ℝ) + 1)
      have hsqR : eLpNorm Δ 2 ν ^ (2 : ℕ) ≤ R * I := by
        simpa [R] using hsq'
      have hRtop : R * I ≠ ⊤ := by
        apply ENNReal.mul_ne_top
        · apply ENNReal.mul_ne_top
          · simp
          · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (by finiteness)
        · exact hI
      have hsqreal : (eLpNorm Δ 2 ν).toReal ^ (2 : ℕ) ≤ (R * I).toReal := by
        rw [← ENNReal.toReal_pow]
        exact (ENNReal.toReal_le_toReal (ENNReal.pow_ne_top hmem.eLpNorm_lt_top.ne) hRtop).mpr hsqR
      have hsqrt : (eLpNorm Δ 2 ν).toReal ≤ Real.sqrt (R * I).toReal := by
        exact Real.le_sqrt_of_sq_le hsqreal
      have hRreal : (R * I).toReal =
          ((K + ν.real Set.univ) * I.toReal) * (a n) ^ (2 : ℕ) := by
        dsimp [R, a]
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal, ← ENNReal.toReal_rpow,
          ENNReal.toReal_ofReal]
        rw [Real.sq_sqrt (by positivity)]
        · ring
        · positivity
        · positivity
      calc
        (eLpNorm (fun x => E (n + 1) x - E n x) 2 ν).toReal =
            (eLpNorm Δ 2 ν).toReal := by rfl
        _ ≤ Real.sqrt (R * I).toReal := hsqrt
        _ = Clocal * a n := by
          rw [hRreal, Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]
          rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    have hdist : ∀ n : ℕ,
        dist ((hE n).toLp (E n)) ((hE (n + 1)).toLp (E (n + 1))) =
          (eLpNorm (fun x => E (n + 1) x - E n x) 2 ν).toReal := by
      intro n
      rw [dist_comm, Lp.dist_def]
      congr 1
      apply eLpNorm_congr_ae
      filter_upwards [(hE (n + 1)).coeFn_toLp, (hE n).coeFn_toLp] with x hx1 hx0
      simp only [Pi.sub_apply, hx1, hx0]
    let v : ℕ → Lp ℝ 2 ν := fun n => (hE n).toLp (E n)
    let gv : Lp ℝ 2 ν := hg.toLp g
    have hdist' : ∀ n : ℕ,
        dist (v n) gv = (eLpNorm (fun x => E n x - g x) 2 ν).toReal := by
      intro n
      rw [Lp.dist_def]
      congr 1
      apply eLpNorm_congr_ae
      filter_upwards [(hE n).coeFn_toLp, hg.coeFn_toLp] with x hx hy
      simp only [v, gv, Pi.sub_apply, hx, hy]
    have hfin : ∀ n : ℕ, eLpNorm (fun x => E n x - g x) 2 ν ≠ ⊤ :=
      fun n => ((hE n).sub hg).eLpNorm_lt_top.ne
    have hvtendsto : Tendsto v atTop (nhds gv) := by
      simpa only [v, gv] using
        ((MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm'' E hE g hg).mpr hgtendsto)
    have htel : dist (v 0) gv ≤ ∑' n, (eLpNorm (fun x => E (n + 1) x - E n x) 2 ν).toReal := by
      apply dist_le_tsum_of_dist_le_of_tendsto₀
        (fun n => (eLpNorm (fun x => E (n + 1) x - E n x) 2 ν).toReal)
      · intro n
        simpa only [Nat.succ_eq_add_one] using (hdist n).le
      · exact hsum
      · simpa only [v] using hvtendsto
    have hseries : (∑' n, (eLpNorm (fun x => E (n + 1) x - E n x) 2 ν).toReal) ≤
        Clocal * A := by
      calc
        _ ≤ ∑' n, Clocal * a n := hsum.tsum_le_tsum hbound (hcoef.mul_left Clocal)
        _ = Clocal * A := by
          rw [tsum_mul_left]

    have htel' : (eLpNorm (fun x => E 0 x - g x) 2 ν).toReal ≤ Clocal * A := by
      rw [← hdist' 0]
      exact htel.trans hseries
    let U : Set (SpatialCoordinates d) := (centeredCube z r hr : Set (SpatialCoordinates d))
    let k0 : OddGridIndex d (triadicHalf 0) := fun _ => ⟨0, by norm_num [triadicHalf]⟩
    have hk0 : ∀ k : OddGridIndex d (triadicHalf 0), k = k0 := by
      intro k
      funext i
      apply Fin.ext
      have hi := (k i).isLt
      norm_num [triadicHalf] at hi
      simpa [k0, triadicHalf] using hi
    have hcell0 : oddGridCell z r hr (triadicHalf 0) k0 = centeredCube z r hr := by
      have hz : oddGridCenter z r (triadicHalf 0) k0 = z := by
        funext i
        simp only [oddGridCenter, k0, triadicHalf, pow_zero, Nat.reduceDiv,
          Nat.cast_zero, sub_self, zero_mul, add_zero]
      unfold oddGridCell
      rw [hz]
      congr 1
      norm_num [triadicHalf]
    have hE0ae : E 0 =ᵐ[ν] U.indicator (fun _ =>
        averageOn U (u.val 0)) := by
      filter_upwards with x
      by_cases hx : x ∈ U
      · have hsum0 := sum_indicator_triadicCell_eq z hr (triadicHalf 0) x
          (fun k : OddGridIndex d (triadicHalf 0) =>
            averageOn (oddGridCell z r hr (triadicHalf 0) k : Set (SpatialCoordinates d))
              (u.val 0)) k0 (by simpa [U, hcell0] using hx)
        rw [hcell0] at hsum0
        have hx' : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) := hx
        simpa only [E, U, Set.indicator_of_mem hx'] using hsum0
      · have hsum0 := sum_indicator_triadicCell_eq_zero_of_not_mem_root z hr
          (triadicHalf 0) x
          (fun k : OddGridIndex d (triadicHalf 0) =>
            averageOn (oddGridCell z r hr (triadicHalf 0) k : Set (SpatialCoordinates d))
              (u.val 0)) (by simpa [U] using hx)
        rw [Set.indicator_of_notMem hx]
        simpa [E] using hsum0
    have hUmeas : MeasurableSet U := (centeredCube z r hr).isOpen.measurableSet
    have hUtop : ν U ≠ ⊤ := by finiteness
    have hUvoltop : volume U ≠ ⊤ := by
      rw [centeredCube_volume]
      exact ENNReal.ofReal_ne_top
    have hUvolpos : 0 < (volume U).toReal := by
      dsimp [U]
      exact centeredCube_volume_pos z hr
    have hsemi :
        (cubeFractionalL2Seminorm hd z r hr halfFractionalOrder u.val).toReal =
          Real.sqrt (I.toReal) / (Real.sqrt 2 * Real.sqrt (volume.real U)) := by
      have hraw : cubeFractionalL2Seminorm hd z r hr halfFractionalOrder u.val =
          (ENNReal.ofReal ((1 : ℝ) / 2) / volume U * I) ^ (1 / 2 : ℝ) := by
        unfold cubeFractionalL2Seminorm
        apply congrArg (fun q : ℝ≥0∞ => q ^ (1 / 2 : ℝ))
        dsimp [halfFractionalOrder, U, I]
        simp only [Fin.sum_univ_one]
        simp only [show (d : ℝ) + 2 * (1 / 2) = (d : ℝ) + 1 by ring]
      rw [hraw, ← ENNReal.toReal_rpow, ENNReal.toReal_mul,
        ENNReal.toReal_div, ENNReal.toReal_ofReal]
      rw [← Real.sqrt_eq_rpow]
      rw [div_eq_mul_inv, Real.sqrt_mul (by positivity),
        Real.sqrt_mul (by positivity)]
      rw [Real.sqrt_inv, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
      have hsqrtV : Real.sqrt (volume.real U) ≠ 0 :=
        Real.sqrt_ne_zero'.mpr hUvolpos
      simp only [measureReal_def] at hsqrtV ⊢
      field_simp [hsqrtV] ; ring
      all_goals norm_num
    have hnormN :
        cubeFractionalL2Norm hd z r hr halfFractionalOrder u =
          (cubeFractionalL2Seminorm hd z r hr halfFractionalOrder u.val).toReal +
            (eLpNorm (u.val 0) 2 (volume.restrict U)).toReal /
              (Real.sqrt r * Real.sqrt (volume.real U)) := by
      unfold cubeFractionalL2Norm
      simp only [Fin.sum_univ_one]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Lp.norm_def]
      have hs : (halfFractionalOrder : ℝ) = (1 / 2 : ℝ) := by
        rfl
      rw [hs]
      rw [Real.rpow_neg (le_of_lt hr)]
      rw [← Real.sqrt_eq_rpow]
      field_simp [hr.ne', hUvolpos.ne']
      ring
    have hUvolne : volume U ≠ 0 := by
      have hp : 0 < volume U := by
        rw [centeredCube_volume]
        exact ENNReal.ofReal_pos.mpr (by positivity)
      exact ne_of_gt hp
    have hfU : IntegrableOn (u.val 0) U volume := by
      exact hf.integrable (by norm_num)
    have hUavg : averageOn U (u.val 0) = ⨍ x in U, (u.val 0) x := by
      unfold averageOn Homogenization.volumeAverage
      rw [MeasureTheory.average_eq]
      simp [smul_eq_mul]
      exact Or.inl rfl
    have hUavgsq : (⨍ x in U, (u.val 0 x) ^ 2) =
        (volume U).toReal⁻¹ * ∫ x in U, (u.val 0 x) ^ 2 := by
      rw [MeasureTheory.average_eq]
      simp [smul_eq_mul]
      exact Or.inl rfl
    have havg_sq : (averageOn U (u.val 0)) ^ 2 ≤
        (volume U).toReal⁻¹ * ∫ x in U, (u.val 0 x) ^ 2 := by
      have hconv : ConvexOn ℝ (Set.univ : Set ℝ) (fun x : ℝ => x ^ 2) :=
        Even.convexOn_pow (𝕜 := ℝ) (n := 2) (by norm_num)
      have hj := hconv.map_set_average_le (μ := volume) (t := U) (f := u.val 0)
        (continuousOn_pow 2) isClosed_univ hUvolne hUvoltop (by simp) hfU
        (by simpa [Function.comp_def, U, IntegrableOn] using hf.integrable_sq)
      rw [hUavg, ← hUavgsq]
      exact hj
    have hE0norm : (eLpNorm (E 0) 2 ν).toReal ≤
        Real.sqrt (ν.real U / (volume U).toReal) *
          (eLpNorm (u.val 0) 2 (volume.restrict U)).toReal := by
      rw [eLpNorm_congr_ae hE0ae, eLpNorm_indicator_const (p := 2) hUmeas.nullMeasurableSet (by norm_num) (by finiteness)]
      rw [ENNReal.toReal_mul]
      simp only [toReal_enorm, measureReal_def]
      simp only [ENNReal.toReal_ofNat]
      rw [← ENNReal.toReal_rpow]
      change ‖averageOn U (u.val 0)‖ * (ν.real U) ^ (1 / (2 : ℝ)) ≤
        Real.sqrt (ν.real U / (volume U).toReal) *
          (eLpNorm (u.val 0) 2 (volume.restrict U)).toReal
      have hnonneg : 0 ≤ averageOn U (u.val 0) ^ 2 := sq_nonneg _
      have hroot : Real.sqrt (ν.real U * (volume U).toReal⁻¹) =
          Real.sqrt (ν.real U / (volume U).toReal) := by rw [div_eq_mul_inv]
      rw [Real.norm_eq_abs]
      rw [← Real.sqrt_eq_rpow]
      have hLp_sq : (eLpNorm (u.val 0) 2 (volume.restrict U)).toReal ^ 2 =
          (∫ x in U, (u.val 0 x) ^ 2) := by
        rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)] ;
          try positivity
        have hi : 0 ≤ ∫ x in U, (u.val 0 x) ^ 2 :=
          integral_nonneg (fun x => sq_nonneg _)
        rw [ENNReal.toReal_ofReal]
        simp [U]
        rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
        rw [Real.sq_sqrt hi]
        all_goals
          exact Real.rpow_nonneg
            (integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)) _
      have hnonnegLp : 0 ≤ (eLpNorm (u.val 0) 2 (volume.restrict U)).toReal :=
        ENNReal.toReal_nonneg
      have hnonnegν : 0 ≤ ν.real U := measureReal_nonneg
      have hnonnegvol : 0 ≤ (volume U).toReal := measureReal_nonneg
      have hmul : 0 ≤ Real.sqrt (ν.real U / (volume U).toReal) := Real.sqrt_nonneg _
      have hsqratio := Real.sq_sqrt (div_nonneg hnonnegν hnonnegvol)
      have hsqrtnu := Real.sq_sqrt hnonnegν
      let X := Real.sqrt (ν.real U / (volume U).toReal) *
        (eLpNorm (u.val 0) 2 (volume.restrict U)).toReal
      let Y := |averageOn U (u.val 0)| * Real.sqrt (ν.real U)
      have hX : 0 ≤ X := by dsimp [X]; positivity
      have hY : 0 ≤ Y := by dsimp [Y]; positivity
      have hXsq : X ^ 2 = (ν.real U / (volume U).toReal) *
          (eLpNorm (u.val 0) 2 (volume.restrict U)).toReal ^ 2 := by
        dsimp [X]
        rw [mul_pow, hsqratio]
      have hYsq : Y ^ 2 = (averageOn U (u.val 0)) ^ 2 * ν.real U := by
        dsimp [Y]
        rw [mul_pow, sq_abs, hsqrtnu]
      have havg_mul := mul_le_mul_of_nonneg_left havg_sq hnonnegν
      have hsqle : Y ^ 2 ≤ X ^ 2 := by
        rw [hYsq, hXsq, hLp_sq]
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using havg_mul
      have hXY : X ≥ Y := by
        by_contra hnot
        have hlt : X < Y := lt_of_not_ge hnot
        have hYpos : 0 < Y := lt_of_le_of_lt hX hlt
        have hsumpos : 0 < Y + X := add_pos_of_pos_of_nonneg hYpos hX
        have hprod : 0 < (Y - X) * (Y + X) :=
          mul_pos (sub_pos.mpr hlt) hsumpos
        have hsq_lt : X ^ 2 < Y ^ 2 := by nlinarith only [hprod]
        exact (not_lt_of_ge hsqle hsq_lt)
      exact hXY
    have hnormg : (eLpNorm g 2 ν).toReal ≤
        (eLpNorm (E 0) 2 ν).toReal + (eLpNorm (fun x => E 0 x - g x) 2 ν).toReal := by
      have htri := eLpNorm_sub_le (f := E 0) (g := fun x => E 0 x - g x) (μ := ν)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have htri' : eLpNorm (fun x => E 0 x - (E 0 x - g x)) 2 ν ≤
          eLpNorm (E 0) 2 ν + eLpNorm (fun x => E 0 x - g x) 2 ν := by
        simpa only [Pi.sub_def] using htri
      have hrewrite : (fun x => g x) = (fun x => E 0 x - (E 0 x - g x)) := by
        funext x
        ring
      change (eLpNorm (fun x => g x) 2 ν).toReal ≤ _
      rw [hrewrite]
      have hne : eLpNorm (E 0) 2 ν +
          eLpNorm (fun x => E 0 x - g x) 2 ν ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨(hE 0).eLpNorm_lt_top.ne, hfin 0⟩
      have hto := ENNReal.toReal_mono hne htri'
      calc
        (eLpNorm (fun x => E 0 x - (E 0 x - g x)) 2 ν).toReal ≤
            (eLpNorm (E 0) 2 ν + eLpNorm (fun x => E 0 x - g x) 2 ν).toReal := hto
        _ = (eLpNorm (E 0) 2 ν).toReal +
            (eLpNorm (fun x => E 0 x - g x) 2 ν).toReal := by
          exact ENNReal.toReal_add (hE 0).eLpNorm_lt_top.ne (hfin 0)
    have hmass : ν.real Set.univ =
        (ν (closure (Homogenization.openCubeSet Q))).toReal := by
      rw [measureReal_def]
      exact congrArg ENNReal.toReal
        (measure_of_measure_compl_eq_zero hsupp).symm
    have hMnonneg : 0 ≤ K + ν.real Set.univ :=
      add_nonneg hK ENNReal.toReal_nonneg
    have hnu_le : ν.real U ≤ K + ν.real Set.univ :=
      (measureReal_mono (Set.subset_univ U)).trans (le_add_of_nonneg_left hK)
    have hA_nonneg : 0 ≤ A := by
      exact tsum_nonneg (fun n => Real.sqrt_nonneg _)
    have hNexact := hnormN
    rw [hsemi] at hNexact
    have hupper : (eLpNorm g 2 ν).toReal ≤
        Real.sqrt (ν.real U / volume.real U) *
          (eLpNorm (u.val 0) 2 (volume.restrict U)).toReal +
            Real.sqrt ((K + ν.real Set.univ) * I.toReal) * A := by
      exact hnormg.trans (add_le_add
        (by simpa only [measureReal_def] using hE0norm)
        (by simpa only [Clocal] using htel'))
    have hfinal := trace_norm_two_term_bound r (volume.real U)
      (K + ν.real Set.univ) (ν.real U) I.toReal
      (eLpNorm (u.val 0) 2 (volume.restrict U)).toReal A
      (eLpNorm g 2 ν).toReal
      (cubeFractionalL2Norm hd z r hr halfFractionalOrder u)
      hr hUvolpos hMnonneg ENNReal.toReal_nonneg hnu_le
      ENNReal.toReal_nonneg ENNReal.toReal_nonneg hA_nonneg
      ENNReal.toReal_nonneg hNexact hupper
    simpa only [C, U, hmass] using hfinal

end SubdiffusiveProcess
