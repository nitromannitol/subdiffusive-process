import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane2.NativeBridge
import SubdiffusiveProcess.Lane1.ChaosBasic
import SubdiffusiveProcess.Geometry.UpstreamCube
import Mathlib.MeasureTheory.Measure.Support




open Filter MeasureTheory ProbabilityTheory Topology SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.Analysis

theorem local_campanato_glue {d : ℕ} {W : Set (SpatialCoordinates d)}
    (hW : IsOpen W) {f g : SpatialCoordinates d → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : f =ᵐ[volume.restrict W] g) : Set.EqOn f g (closure W) := by
  have hWmeas : MeasurableSet W := hW.measurableSet
  have hWeq : Set.EqOn f g W := by
    intro x hx
    by_contra hne
    set c : ℝ := |f x - g x| / 2 with hcdef
    have hcpos : 0 < |f x - g x| := abs_pos.mpr (sub_ne_zero.mpr hne)
    have hc : 0 < c := by rw [hcdef]; linarith
    have hcontabs : Continuous (fun w => |f w - g w|) := (hf.sub hg).abs
    have hWx : IsOpen (W ∩ (fun w => |f w - g w|) ⁻¹' (Set.Ioi c)) :=
      hW.inter (hcontabs.isOpen_preimage _ isOpen_Ioi)
    have hxW : x ∈ W ∩ (fun w => |f w - g w|) ⁻¹' (Set.Ioi c) := by
      refine ⟨hx, ?_⟩
      simp only [Set.mem_preimage, Set.mem_Ioi, hcdef]
      linarith
    have hWpos : 0 < volume (W ∩ (fun w => |f w - g w|) ⁻¹' (Set.Ioi c)) :=
      hWx.measure_pos volume ⟨x, hxW⟩
    have hbad : volume (W ∩ {w | f w ≠ g w}) = 0 := by
      have h1 : volume.restrict W {w | f w ≠ g w} = 0 := ae_iff.mp hfg
      rwa [Measure.restrict_apply' hWmeas, Set.inter_comm] at h1
    have hsub : W ∩ (fun w => |f w - g w|) ⁻¹' (Set.Ioi c) ⊆ W ∩ {w | f w ≠ g w} := by
      rintro w ⟨hw1, hw2⟩
      refine ⟨hw1, ?_⟩
      simp only [Set.mem_preimage, Set.mem_Ioi] at hw2
      intro heq
      rw [heq] at hw2
      simp at hw2
      linarith
    have : volume (W ∩ (fun w => |f w - g w|) ⁻¹' (Set.Ioi c)) ≤
        volume (W ∩ {w | f w ≠ g w}) := measure_mono hsub
    rw [hbad] at this
    exact absurd (le_antisymm this (zero_le _)) (ne_of_gt hWpos)
  exact hWeq.closure hf hg

/-- The Euclidean coordinate distance is controlled by `Real.sqrt d` times the ambient
(sup-norm) `dist`. -/
theorem local_campanato_euclid_le {d : ℕ} (x y : SpatialCoordinates d) :
    Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt d * dist x y := by
  have hcoord : ∀ j : Fin d, (x j - y j) ^ 2 ≤ (dist x y) ^ 2 := by
    intro j
    have hj : dist (x j) (y j) ≤ dist x y := dist_le_pi_dist x y j
    rw [Real.dist_eq] at hj
    have h0 : 0 ≤ |x j - y j| := abs_nonneg _
    calc (x j - y j) ^ 2 = |x j - y j| ^ 2 := (sq_abs _).symm
      _ ≤ (dist x y) ^ 2 := pow_le_pow_left₀ h0 hj 2
  have hsum : (∑ j : Fin d, (x j - y j) ^ 2) ≤ (d : ℝ) * (dist x y) ^ 2 := by
    calc (∑ j : Fin d, (x j - y j) ^ 2) ≤ ∑ _j : Fin d, (dist x y) ^ 2 :=
          Finset.sum_le_sum fun j _ => hcoord j
      _ = (d : ℝ) * (dist x y) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt ((d : ℝ) * (dist x y) ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d * dist x y := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq dist_nonneg]

/-- Pointwise Hölder increment on a closed cube of side `r ≤ 1`, in terms of the ambient
`dist` (sup-norm) rather than the Euclidean coordinate distance baked into
`holderSeminorm`. -/
theorem local_campanato_holder_pt {d : ℕ} (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) {alpha : ℝ} (ha0 : 0 < alpha)
    {U : SpatialCoordinates d → ℝ}
    (hH : IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U)
    {K : ℝ} (hKle : holderSeminorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤ K)
    (hK0 : 0 ≤ K)
    {x y : SpatialCoordinates d}
    (hx : x ∈ (closedCube z r hr : Set (SpatialCoordinates d)))
    (hy : y ∈ (closedCube z r hr : Set (SpatialCoordinates d))) :
    |U x - U y| ≤ K * (Real.sqrt d) ^ alpha * dist x y ^ alpha := by
  by_cases hxy : x = y
  · subst hxy
    simp only [sub_self, abs_zero]
    positivity
  · set e := Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) with hedef
    have he0 : 0 < e := by
      rw [hedef, Real.sqrt_pos]
      obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
        by_contra h
        push_neg at h
        exact hxy (funext h)
      have hjpos : 0 < (x j - y j) ^ 2 := by
        have hne : x j - y j ≠ 0 := sub_ne_zero.mpr hj
        positivity
      exact lt_of_lt_of_le hjpos
        (Finset.single_le_sum (f := fun j => (x j - y j) ^ 2) (fun j _ => sq_nonneg _)
          (Finset.mem_univ j))
    have hea : 0 < e ^ alpha := Real.rpow_pos_of_pos he0 _
    have hratio : |U x - U y| / e ^ alpha ≤
        holderSeminorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U :=
      le_csSup hH ⟨x, hx, y, hy, hxy, rfl⟩
    have h1 : |U x - U y| ≤
        holderSeminorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U * e ^ alpha :=
      (div_le_iff₀ hea).mp hratio
    have h2 : holderSeminorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U * e ^ alpha
        ≤ K * e ^ alpha := mul_le_mul_of_nonneg_right hKle hea.le
    have hele := local_campanato_euclid_le x y
    have he3 : e ^ alpha ≤ (Real.sqrt d * dist x y) ^ alpha :=
      Real.rpow_le_rpow he0.le hele ha0.le
    have he4 : (Real.sqrt d * dist x y) ^ alpha =
        (Real.sqrt d) ^ alpha * (dist x y) ^ alpha :=
      Real.mul_rpow (Real.sqrt_nonneg _) dist_nonneg
    calc |U x - U y| ≤
          holderSeminorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U * e ^ alpha :=
          h1
      _ ≤ K * e ^ alpha := h2
      _ ≤ K * (Real.sqrt d * dist x y) ^ alpha := mul_le_mul_of_nonneg_left he3 hK0
      _ = K * ((Real.sqrt d) ^ alpha * (dist x y) ^ alpha) := by rw [he4]
      _ = K * (Real.sqrt d) ^ alpha * dist x y ^ alpha := by ring


/-- Elementary 1-D interval overlap: a ball of radius `rad ≤ r` centred anywhere in the
open interval of half-width `r/2` around `c` meets that interval in a set of length at
least `rad`. -/
theorem local_campanato_overlap1d {c t r rad : ℝ}
    (hrad : 0 < rad) (hle : rad ≤ r) (ht0 : c - r / 2 < t) (ht1 : t < c + r / 2) :
    rad ≤ min (t + rad) (c + r / 2) - max (t - rad) (c - r / 2) := by
  rcases le_total (t + rad) (c + r / 2) with h1 | h1 <;>
    rcases le_total (t - rad) (c - r / 2) with h2 | h2 <;>
    simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, h1, h2] <;>
    linarith

/-- `d`-dimensional density: the (sup-norm) ball of radius `rad ≤ 1` around an interior
point `x'` of the unit-side cube centred at `c` meets that cube in a set whose volume is
at least `2⁻ᵈ` times the volume of the whole ball. -/
theorem local_campanato_density {d : ℕ} (c x' : SpatialCoordinates d) {rad : ℝ}
    (hrad : 0 < rad) (hrad1 : rad ≤ 1)
    (hx' : x' ∈ (centeredCube c 1 one_pos : Set (SpatialCoordinates d))) :
    volume.real (Metric.ball x' rad) ≤
      (2 : ℝ) ^ d * volume.real (Metric.ball x' rad ∩
        (centeredCube c 1 one_pos : Set (SpatialCoordinates d))) := by
  have hballpi : Metric.ball x' rad = Set.pi Set.univ (fun i => Set.Ioo (x' i - rad) (x' i + rad)) := by
    rw [ball_pi x' hrad]
    congr 1
    funext i
    rw [Real.ball_eq_Ioo]
  have hcubepi : (centeredCube c 1 one_pos : Set (SpatialCoordinates d)) =
      Set.pi Set.univ (fun i => Set.Ioo (c i - 1 / 2) (c i + 1 / 2)) := by
    rw [centeredCube_eq_pi]
  have hinterpi : Metric.ball x' rad ∩ (centeredCube c 1 one_pos : Set (SpatialCoordinates d)) =
      Set.pi Set.univ (fun i => Set.Ioo (x' i - rad) (x' i + rad) ∩
        Set.Ioo (c i - 1 / 2) (c i + 1 / 2)) := by
    rw [hballpi, hcubepi]
    ext p
    simp only [Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, true_implies, forall_and]
  have hx'i : ∀ i, c i - 1 / 2 < x' i ∧ x' i < c i + 1 / 2 := by
    intro i
    have h := hx'
    rw [hcubepi] at h
    exact Set.mem_univ_pi.mp h i
  have hover : ∀ i, rad ≤ volume.real (Set.Ioo (x' i - rad) (x' i + rad) ∩
      Set.Ioo (c i - 1 / 2) (c i + 1 / 2)) := by
    intro i
    rw [Set.Ioo_inter_Ioo, Measure.real, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by
        have := local_campanato_overlap1d (c := c i) (t := x' i) (r := 1) (rad := rad)
          hrad hrad1 (hx'i i).1 (hx'i i).2
        linarith)]
    exact local_campanato_overlap1d (c := c i) (t := x' i) (r := 1) (rad := rad)
      hrad hrad1 (hx'i i).1 (hx'i i).2
  have hballvol : volume.real (Metric.ball x' rad) = (2 * rad) ^ d := by
    rw [Measure.real, hballpi, volume_pi_pi]
    have : ∀ i : Fin d, volume (Set.Ioo (x' i - rad) (x' i + rad)) =
        ENNReal.ofReal (2 * rad) := by
      intro i; rw [Real.volume_Ioo]; ring_nf
    rw [Finset.prod_congr rfl (fun i _ => this i)]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow (by linarith)]
    exact ENNReal.toReal_ofReal (by positivity)
  have hinterval : volume.real (Metric.ball x' rad ∩
      (centeredCube c 1 one_pos : Set (SpatialCoordinates d))) =
      ∏ i : Fin d, volume.real (Set.Ioo (x' i - rad) (x' i + rad) ∩
        Set.Ioo (c i - 1 / 2) (c i + 1 / 2)) := by
    rw [Measure.real, hinterpi, volume_pi_pi, ENNReal.toReal_prod]
    rfl
  have hprodle : (rad : ℝ) ^ d ≤ ∏ i : Fin d, volume.real (Set.Ioo (x' i - rad) (x' i + rad) ∩
      Set.Ioo (c i - 1 / 2) (c i + 1 / 2)) := by
    calc (rad : ℝ) ^ d = ∏ _i : Fin d, rad := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := Finset.prod_le_prod (fun i _ => hrad.le) (fun i _ => hover i)
  rw [hballvol, hinterval]
  calc (2 * rad) ^ d = (2:ℝ) ^ d * rad ^ d := by ring
    _ ≤ (2:ℝ) ^ d * ∏ i : Fin d, volume.real (Set.Ioo (x' i - rad) (x' i + rad) ∩
        Set.Ioo (c i - 1 / 2) (c i + 1 / 2)) :=
      mul_le_mul_of_nonneg_left hprodle (by positivity)


/-- The mean minimizes the `L²` oscillation: for any competitor constant `c`, the
`L²(S)` distance to the mean of `u` over `S` is at most the `L²(S)` distance to `c`. -/
theorem local_campanato_variance {d : ℕ} {S : Set (SpatialCoordinates d)}
    (hSfin : volume S ≠ ⊤)
    {u : SpatialCoordinates d → ℝ} (hu : IntegrableOn u S volume)
    (hu2 : IntegrableOn (fun x => u x ^ 2) S volume) (c : ℝ) :
    (∫ y in S, (u y - (volume.real S)⁻¹ * ∫ w in S, u w) ^ 2) ≤ ∫ y in S, (u y - c) ^ 2 := by
  set m : ℝ := (volume.real S)⁻¹ * ∫ w in S, u w with hmdef
  by_cases hS0 : volume.real S = 0
  · have hSz : volume S = 0 := by
      rwa [Measure.real, ENNReal.toReal_eq_zero_iff, or_iff_left hSfin] at hS0
    have hRz : volume.restrict S = 0 := Measure.restrict_eq_zero.mpr hSz
    simp [hRz]
  · have hconstInt : ∀ k : ℝ, IntegrableOn (fun _ : SpatialCoordinates d => k) S volume :=
      fun k => integrableOn_const hSfin
    have hmuInt : IntegrableOn (fun y => m * u y) S volume := hu.const_mul m
    have hu_m_sq : IntegrableOn (fun y => (u y - m) ^ 2) S volume := by
      have hEq : (fun y => (u y - m) ^ 2) =
          (fun y => u y ^ 2 - 2 * m * u y + m ^ 2) := funext fun y => by ring
      rw [hEq]
      exact ((hu2.sub ((hu.const_mul (2 * m)))).add (hconstInt (m ^ 2)))
    have hu_c_sq : IntegrableOn (fun y => (u y - c) ^ 2) S volume := by
      have hEq : (fun y => (u y - c) ^ 2) =
          (fun y => u y ^ 2 - 2 * c * u y + c ^ 2) := funext fun y => by ring
      rw [hEq]
      exact ((hu2.sub ((hu.const_mul (2 * c)))).add (hconstInt (c ^ 2)))
    have hInt2u : IntegrableOn (fun y => 2 * u y - (c + m)) S volume :=
      (hu.const_mul 2).sub (hconstInt (c + m))
    have hdiffPt : ∀ y, (u y - c) ^ 2 - (u y - m) ^ 2 = (m - c) * (2 * u y - (c + m)) := by
      intro y; ring
    have hSumEq : (fun y => (u y - c) ^ 2) =
        (fun y => (u y - m) ^ 2 + (m - c) * (2 * u y - (c + m))) := by
      funext y; have := hdiffPt y; linarith
    have hInt3 : IntegrableOn (fun y => (m - c) * (2 * u y - (c + m))) S volume :=
      hInt2u.const_mul (m - c)
    have hsplit : (∫ y in S, (u y - c) ^ 2) =
        (∫ y in S, (u y - m) ^ 2) + ∫ y in S, (m - c) * (2 * u y - (c + m)) := by
      rw [hSumEq]
      exact integral_add hu_m_sq hInt3
    have hcrossVal : (∫ y in S, (m - c) * (2 * u y - (c + m))) = (m - c) ^ 2 * volume.real S := by
      rw [integral_const_mul]
      have hInt2uEq : (∫ y in S, (2 * u y - (c + m))) =
          2 * (∫ y in S, u y) - (c + m) * volume.real S := by
        rw [integral_sub (hu.const_mul 2) (hconstInt (c + m)), integral_const_mul,
          MeasureTheory.setIntegral_const]
        simp [Measure.real, smul_eq_mul, mul_comm]
      rw [hInt2uEq]
      have hmuEq : (∫ y in S, u y) = m * volume.real S := by
        rw [hmdef]; field_simp
      rw [hmuEq]; ring
    rw [hsplit, hcrossVal]
    have hnn : 0 ≤ (m - c) ^ 2 * volume.real S := by positivity
    linarith


/-- A locally integrable function with locally integrable square is `MemLp 2` on any
cube. -/
theorem local_campanato_memLp {d : ℕ} {u : SpatialCoordinates d → ℝ}
    (hLIu : LocallyIntegrable u volume) (hLIu2 : LocallyIntegrable (fun x => u x ^ 2) volume)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    MemLp u 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  have hIntClosed : IntegrableOn u (closedCube z r hr : Set (SpatialCoordinates d)) volume :=
    hLIu.integrableOn_isCompact (closedCube z r hr).isCompact
  have hInt2Closed : IntegrableOn (fun x => u x ^ 2) (closedCube z r hr : Set (SpatialCoordinates d))
      volume := hLIu2.integrableOn_isCompact (closedCube z r hr).isCompact
  have hsub : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (closedCube z r hr : Set (SpatialCoordinates d)) := centeredCube_subset_closedCube z hr
  have hInt2 : IntegrableOn (fun x => u x ^ 2) (centeredCube z r hr : Set (SpatialCoordinates d))
      volume := hInt2Closed.mono_set hsub
  have hMeas : AEStronglyMeasurable u (volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    (hIntClosed.mono_set hsub).aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq hMeas).mpr hInt2


/-- Transfer the whole-space (unintersected-ball) `L²` oscillation hypothesis to the
Campanato hypothesis on a side-`1` cube, at a centre `x'` inside the cube and any radius
`rad ≤ 1`: the mean-minimizing property (`variance`) plus the `2^d` density bound. -/
theorem local_campanato_osc1 {d : ℕ} {u : SpatialCoordinates d → ℝ} {A alpha : ℝ}
    (hLIu : LocallyIntegrable u volume) (hLIu2 : LocallyIntegrable (fun x => u x ^ 2) volume)
    (hosc : ∀ (x : SpatialCoordinates d) (rad : ℝ), 0 < rad → rad ≤ 1 →
      (∫ y in Metric.ball x rad, (u y - (volume.real (Metric.ball x rad))⁻¹ *
        ∫ w in Metric.ball x rad, u w) ^ 2) ≤
        A ^ 2 * volume.real (Metric.ball x rad) * rad ^ (2 * alpha))
    (c : SpatialCoordinates d) (x' : SpatialCoordinates d)
    (hx' : x' ∈ (centeredCube c 1 one_pos : Set (SpatialCoordinates d)))
    (rad : ℝ) (hrad : 0 < rad) (hrad1 : rad ≤ 1) :
    (∫ y in Metric.ball x' rad ∩ (centeredCube c 1 one_pos : Set (SpatialCoordinates d)),
        (u y - (volume.real (Metric.ball x' rad ∩
              (centeredCube c 1 one_pos : Set (SpatialCoordinates d))))⁻¹ *
            ∫ w in Metric.ball x' rad ∩ (centeredCube c 1 one_pos : Set (SpatialCoordinates d)),
              u w) ^ 2) ≤
      (A * (2 : ℝ) ^ ((d : ℝ) / 2)) ^ 2 * rad ^ (2 * alpha) *
        volume.real (Metric.ball x' rad ∩
          (centeredCube c 1 one_pos : Set (SpatialCoordinates d))) := by
  set B : Set (SpatialCoordinates d) := Metric.ball x' rad with hBdef
  set S : Set (SpatialCoordinates d) := B ∩ (centeredCube c 1 one_pos : Set (SpatialCoordinates d))
    with hSdef
  set mB : ℝ := (volume.real B)⁻¹ * ∫ w in B, u w with hmBdef
  have hBfin : volume B ≠ ⊤ := (measure_ball_lt_top).ne
  have hSfin : volume S ≠ ⊤ :=
    ne_top_of_le_ne_top hBfin (measure_mono (hSdef ▸ Set.inter_subset_left))
  have hIntBClosed : IntegrableOn u (Metric.closedBall x' rad) volume :=
    hLIu.integrableOn_isCompact (isCompact_closedBall x' rad)
  have hInt2BClosed : IntegrableOn (fun x => u x ^ 2) (Metric.closedBall x' rad) volume :=
    hLIu2.integrableOn_isCompact (isCompact_closedBall x' rad)
  have hBsub : B ⊆ Metric.closedBall x' rad := Metric.ball_subset_closedBall
  have hIntB : IntegrableOn u B volume := hIntBClosed.mono_set hBsub
  have hInt2B : IntegrableOn (fun x => u x ^ 2) B volume := hInt2BClosed.mono_set hBsub
  have hSsub : S ⊆ B := hSdef ▸ Set.inter_subset_left
  have hIntS : IntegrableOn u S volume := hIntB.mono_set hSsub
  have hInt2S : IntegrableOn (fun x => u x ^ 2) S volume := hInt2B.mono_set hSsub
  have hconstIntB : IntegrableOn (fun _ : SpatialCoordinates d => mB) B volume :=
    integrableOn_const hBfin
  have hsqIntB : IntegrableOn (fun y => (u y - mB) ^ 2) B volume := by
    have hEq : (fun y => (u y - mB) ^ 2) = (fun y => u y ^ 2 - 2 * mB * u y + mB ^ 2) :=
      funext fun y => by ring
    rw [hEq]
    exact ((hInt2B.sub (hIntB.const_mul (2 * mB))).add (integrableOn_const hBfin))
  -- Step 1: the mean over `S` minimizes the `L²(S)` distance among all constants,
  -- in particular the competitor `mB`.
  have hstep1 := local_campanato_variance (S := S) hSfin hIntS hInt2S mB
  -- Step 2: extending the domain of integration from `S` to `B ⊇ S` only adds a
  -- nonnegative amount (the integrand is a square).
  have hstep2 : (∫ y in S, (u y - mB) ^ 2) ≤ ∫ y in B, (u y - mB) ^ 2 :=
    setIntegral_mono_set hsqIntB
      (Filter.Eventually.of_forall fun y => sq_nonneg _) hSsub.eventuallyLE
  -- Step 3: the global hypothesis at the centre `x'`, radius `rad`.
  have hstep3 : (∫ y in B, (u y - mB) ^ 2) ≤ A ^ 2 * volume.real B * rad ^ (2 * alpha) :=
    hosc x' rad hrad hrad1
  -- Step 4: `2^d`-density of `S` inside `B`.
  have hstep4 : volume.real B ≤ (2 : ℝ) ^ d * volume.real S :=
    local_campanato_density c x' hrad hrad1 hx'
  have hA2nn : (0:ℝ) ≤ A ^ 2 := sq_nonneg _
  have hradnn : (0:ℝ) ≤ rad ^ (2 * alpha) := by positivity
  have hchain : (∫ y in S, (u y - (volume.real S)⁻¹ * ∫ w in S, u w) ^ 2) ≤
      A ^ 2 * ((2 : ℝ) ^ d * volume.real S) * rad ^ (2 * alpha) := by
    calc (∫ y in S, (u y - (volume.real S)⁻¹ * ∫ w in S, u w) ^ 2)
        ≤ ∫ y in S, (u y - mB) ^ 2 := hstep1
      _ ≤ ∫ y in B, (u y - mB) ^ 2 := hstep2
      _ ≤ A ^ 2 * volume.real B * rad ^ (2 * alpha) := hstep3
      _ ≤ A ^ 2 * ((2:ℝ) ^ d * volume.real S) * rad ^ (2 * alpha) := by
          have := mul_le_mul_of_nonneg_left hstep4 hA2nn
          exact mul_le_mul_of_nonneg_right this hradnn
  have hfinal : A ^ 2 * ((2:ℝ) ^ d * volume.real S) * rad ^ (2 * alpha) =
      (A * (2:ℝ) ^ ((d:ℝ)/2)) ^ 2 * rad ^ (2 * alpha) * volume.real S := by
    have h2d : ((2:ℝ) ^ ((d:ℝ)/2)) ^ 2 = (2:ℝ) ^ d := by
      rw [← Real.rpow_natCast (2:ℝ) d, ← Real.rpow_two, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rw [mul_pow]
    rw [h2d]
    ring
  rw [hfinal] at hchain
  exact hchain


/-- The Campanato representative on a single side-`1` cube centred at `c`, built from
`Cp` and the whole-space oscillation hypothesis, with the `2^{d/2}`-inflated seminorm
bound. -/
theorem local_campanato_cell {d : ℕ} (Cp : Lane4.CampanatoInput d)
    {alpha : ℝ} (ha0 : 0 < alpha) (ha1 : alpha < 1)
    {u : SpatialCoordinates d → ℝ} {A : ℝ} (hA0 : 0 ≤ A)
    (hLIu : LocallyIntegrable u volume) (hLIu2 : LocallyIntegrable (fun x => u x ^ 2) volume)
    (hosc : ∀ (x : SpatialCoordinates d) (rad : ℝ), 0 < rad → rad ≤ 1 →
      (∫ y in Metric.ball x rad, (u y - (volume.real (Metric.ball x rad))⁻¹ *
        ∫ w in Metric.ball x rad, u w) ^ 2) ≤
        A ^ 2 * volume.real (Metric.ball x rad) * rad ^ (2 * alpha))
    (c : SpatialCoordinates d) :
    ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
      U =ᵐ[volume.restrict (centeredCube c 1 one_pos : Set (SpatialCoordinates d))] u ∧
      IsHolderOn alpha (closedCube c 1 one_pos : Set (SpatialCoordinates d)) U ∧
      holderSeminorm alpha (closedCube c 1 one_pos : Set (SpatialCoordinates d)) U ≤
        Cp.C alpha * (A * (2 : ℝ) ^ ((d : ℝ) / 2)) := by
  have hMemLp := local_campanato_memLp hLIu hLIu2 c 1 one_pos
  set uk : DomainL2 (centeredCube c 1 one_pos) := hMemLp.toLp u with hukdef
  have hukAE : (uk : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube c 1 one_pos : Set (SpatialCoordinates d))] u := by
    rw [hukdef]; exact MemLp.coeFn_toLp hMemLp
  have hAK0 : (0:ℝ) ≤ A * (2:ℝ) ^ ((d:ℝ)/2) := by positivity
  have hoscHyp : ∀ x ∈ (centeredCube c 1 one_pos : Set (SpatialCoordinates d)),
      ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
      (∫ y in Metric.ball x rad ∩ (centeredCube c 1 one_pos : Set (SpatialCoordinates d)),
          (uk y - setAverage (Metric.ball x rad ∩
              (centeredCube c 1 one_pos : Set (SpatialCoordinates d))) uk) ^ 2
          ∂volume.restrict (centeredCube c 1 one_pos : Set (SpatialCoordinates d))) ≤
        (A * (2:ℝ) ^ ((d:ℝ)/2)) ^ 2 * rad ^ (2 * alpha) *
          volume.real (Metric.ball x rad ∩
            (centeredCube c 1 one_pos : Set (SpatialCoordinates d))) := by
    intro x hx rad hrad hrad1
    set S : Set (SpatialCoordinates d) :=
      Metric.ball x rad ∩ (centeredCube c 1 one_pos : Set (SpatialCoordinates d)) with hSdef
    have hSsub : S ⊆ (centeredCube c 1 one_pos : Set (SpatialCoordinates d)) :=
      hSdef ▸ Set.inter_subset_right
    have hukAES : (uk : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict S] u :=
      ae_restrict_of_ae_restrict_of_subset hSsub hukAE
    have hRestr : (volume.restrict (centeredCube c 1 one_pos : Set (SpatialCoordinates d))).restrict
        S = volume.restrict S := Measure.restrict_restrict_of_subset hSsub
    have hAvgEq : setAverage S uk = (volume.real S)⁻¹ * ∫ w in S, u w := by
      unfold setAverage
      rw [hRestr, integral_congr_ae hukAES]
    have hintEq : (∫ y in S, (uk y - setAverage S uk) ^ 2
        ∂volume.restrict (centeredCube c 1 one_pos : Set (SpatialCoordinates d))) =
        ∫ y in S, (u y - (volume.real S)⁻¹ * ∫ w in S, u w) ^ 2 := by
      rw [hRestr, hAvgEq]
      exact integral_congr_ae (hukAES.mono fun y hy => by simp only [hy])
    rw [hintEq]
    exact local_campanato_osc1 hLIu hLIu2 hosc c x hx rad hrad hrad1
  obtain ⟨U, hUcont, hUae, hUholder, hUsemi⟩ := Cp.holder_of_campanato alpha ha0 ha1 c 1 one_pos
    le_rfl uk (A * (2:ℝ) ^ ((d:ℝ)/2)) hAK0 hoscHyp
  exact ⟨U, hUcont, hUae.symm.trans hukAE, hUholder, hUsemi⟩


/-- If `x` lies in an open set `A` and in the closure of `B`, it lies in the closure of
`A ∩ B`. (No delicate boundary/tangency argument needed: `IsOpen.closure_inter` does the
work.) -/
theorem local_campanato_mem_closure_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} {x : X} (hA : IsOpen A) (hxA : x ∈ A) (hxB : x ∈ closure B) :
    x ∈ closure (A ∩ B) := by
  have hmem : x ∈ closure (B ∩ A) := (hA.closure_inter (s := B)) ⟨hxB, hxA⟩
  rwa [Set.inter_comm] at hmem


/-- Two Campanato representatives on side-`1` cells that both approximate the same `u`
agree pointwise at any point `x` that lies in the (open) first cell and in the closure
of the second. -/
theorem local_campanato_bridge {d : ℕ} {u : SpatialCoordinates d → ℝ}
    {k1 k2 : SpatialCoordinates d} {U1 U2 : SpatialCoordinates d → ℝ}
    (hU1cont : Continuous U1) (hU2cont : Continuous U2)
    (hU1ae : U1 =ᵐ[volume.restrict (centeredCube k1 1 one_pos : Set (SpatialCoordinates d))] u)
    (hU2ae : U2 =ᵐ[volume.restrict (centeredCube k2 1 one_pos : Set (SpatialCoordinates d))] u)
    {x : SpatialCoordinates d} (hx1 : x ∈ (centeredCube k1 1 one_pos : Set (SpatialCoordinates d)))
    (hx2 : x ∈ closure (centeredCube k2 1 one_pos : Set (SpatialCoordinates d))) :
    U1 x = U2 x := by
  have hW : IsOpen ((centeredCube k1 1 one_pos : Set (SpatialCoordinates d)) ∩
      (centeredCube k2 1 one_pos : Set (SpatialCoordinates d))) :=
    (centeredCube k1 1 one_pos).isOpen.inter (centeredCube k2 1 one_pos).isOpen
  have hxW : x ∈ closure ((centeredCube k1 1 one_pos : Set (SpatialCoordinates d)) ∩
      (centeredCube k2 1 one_pos : Set (SpatialCoordinates d))) :=
    local_campanato_mem_closure_inter (centeredCube k1 1 one_pos).isOpen hx1 hx2
  have h1 : U1 =ᵐ[volume.restrict ((centeredCube k1 1 one_pos : Set (SpatialCoordinates d)) ∩
      (centeredCube k2 1 one_pos : Set (SpatialCoordinates d)))] u :=
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left hU1ae
  have h2 : U2 =ᵐ[volume.restrict ((centeredCube k1 1 one_pos : Set (SpatialCoordinates d)) ∩
      (centeredCube k2 1 one_pos : Set (SpatialCoordinates d)))] u :=
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right hU2ae
  exact local_campanato_glue hW hU1cont hU2cont (h1.trans h2.symm) hxW


/-- Two points at sup-norm distance `≤ 1` both lie in the closure of the side-`1` cube
centred at their coordinatewise midpoint. -/
theorem local_campanato_midpoint_mem {d : ℕ} (x y : SpatialCoordinates d)
    (hxy : dist x y ≤ 1) :
    x ∈ closure (centeredCube (fun i => (x i + y i) / 2) 1 one_pos :
        Set (SpatialCoordinates d)) ∧
    y ∈ closure (centeredCube (fun i => (x i + y i) / 2) 1 one_pos :
        Set (SpatialCoordinates d)) := by
  set m : SpatialCoordinates d := fun i => (x i + y i) / 2 with hmdef
  have hclos : closure (centeredCube m 1 one_pos : Set (SpatialCoordinates d)) =
      (closedCube m 1 one_pos : Set (SpatialCoordinates d)) := by
    show closure (Metric.ball m (1 / 2)) = Metric.closedBall m (1 / 2)
    exact closure_ball m (by norm_num)
  have hxyi : ∀ i, |x i - y i| ≤ dist x y := by
    intro i
    have h := dist_le_pi_dist x y i
    rwa [Real.dist_eq] at h
  have hdxm : dist x m ≤ 1 / 2 := by
    rw [dist_pi_le_iff (by norm_num : (0:ℝ) ≤ 1/2)]
    intro i
    rw [Real.dist_eq]
    have hxi : x i - m i = (x i - y i) / 2 := by rw [hmdef]; ring
    rw [hxi, abs_div]
    have h2 : |(2:ℝ)| = 2 := by norm_num
    rw [h2]
    linarith [hxyi i]
  have hdym : dist y m ≤ 1 / 2 := by
    rw [dist_pi_le_iff (by norm_num : (0:ℝ) ≤ 1/2)]
    intro i
    rw [Real.dist_eq]
    have hyi : y i - m i = -(x i - y i) / 2 := by rw [hmdef]; ring
    rw [hyi, abs_div, abs_neg]
    have h2 : |(2:ℝ)| = 2 := by norm_num
    rw [h2]
    linarith [hxyi i]
  refine ⟨hclos ▸ ?_, hclos ▸ ?_⟩
  · exact Metric.mem_closedBall.mpr hdxm
  · exact Metric.mem_closedBall.mpr hdym


/-- The lattice index of `x` on the spacing-`1/3` grid (`Fin d → ℤ` is countable — this
is what keeps the assembled `v` a.e. equal to `u`: a countable union of null sets is
null, but a per-point-own-cell construction would not have this property since its
index set (all of `SpatialCoordinates d`) is uncountable). -/
def localCampanatoIndex {d : ℕ} (x : SpatialCoordinates d) : Fin d → ℤ :=
  fun i => round (3 * x i)

/-- The real centre of lattice cell `k`. -/
def localCampanatoCenter {d : ℕ} (k : Fin d → ℤ) : SpatialCoordinates d :=
  fun i => ((k i : ℤ) : ℝ) / 3

/-- The "home" cell centre of `x`: rounding each coordinate of `3x` to the nearest
integer and dividing by `3` lands strictly inside the open side-`1` cell centred there
(margin `1/2 - 1/6 = 1/3 > 0`, so no boundary/tie case is an issue, unlike a
spacing-`1/2` grid). -/
def localCampanatoHome {d : ℕ} (x : SpatialCoordinates d) : SpatialCoordinates d :=
  localCampanatoCenter (localCampanatoIndex x)

theorem localCampanatoHome_mem {d : ℕ} (x : SpatialCoordinates d) :
    x ∈ (centeredCube (localCampanatoHome x) 1 one_pos :
        Set (SpatialCoordinates d)) := by
  show x ∈ Metric.ball (localCampanatoHome x) (1 / 2)
  rw [Metric.mem_ball, dist_pi_lt_iff (by norm_num : (0:ℝ) < 1 / 2)]
  intro i
  rw [Real.dist_eq]
  have hr := abs_sub_round (3 * x i)
  have heq : x i - localCampanatoHome x i =
      (3 * x i - ((round (3 * x i) : ℤ) : ℝ)) / 3 := by
    unfold localCampanatoHome localCampanatoCenter
      localCampanatoIndex
    ring
  rw [heq, abs_div]
  have h3 : |(3:ℝ)| = 3 := by norm_num
  rw [h3]
  linarith


/-- Assembling cellwise-a.e.-equal representatives along `localCampanatoIndex`
gives a globally a.e.-equal function, because the index set `Fin d → ℤ` is countable. -/
theorem local_campanato_ae_of_cellwise {d : ℕ} {u : SpatialCoordinates d → ℝ}
    {Uf : (Fin d → ℤ) → SpatialCoordinates d → ℝ}
    (hUfae : ∀ k : Fin d → ℤ, Uf k =ᵐ[volume.restrict
        (centeredCube (localCampanatoCenter k) 1 one_pos :
          Set (SpatialCoordinates d))] u) :
    (fun x => Uf (localCampanatoIndex x) x) =ᵐ[volume] u := by
  apply ae_iff.mpr
  have hsub : {x | ¬ Uf (localCampanatoIndex x) x = u x} ⊆
      ⋃ k : Fin d → ℤ, {x | localCampanatoIndex x = k} ∩
        {x | ¬ Uf k x = u x} := by
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨localCampanatoIndex x, rfl, hx⟩
  have hnull : ∀ k : Fin d → ℤ, volume ({x | localCampanatoIndex x = k} ∩
      {x | ¬ Uf k x = u x}) = 0 := by
    intro k
    have hsub2 : {x | localCampanatoIndex x = k} ∩ {x | ¬ Uf k x = u x} ⊆
        (centeredCube (localCampanatoCenter k) 1 one_pos :
          Set (SpatialCoordinates d)) ∩ {x | ¬ Uf k x = u x} := by
      rintro x ⟨hx1, hx2⟩
      refine ⟨?_, hx2⟩
      have hhome := localCampanatoHome_mem x
      unfold localCampanatoHome at hhome
      rwa [hx1] at hhome
    have hnull2 : volume ((centeredCube (localCampanatoCenter k) 1 one_pos :
        Set (SpatialCoordinates d)) ∩ {x | ¬ Uf k x = u x}) = 0 := by
      have h := ae_iff.mp (hUfae k)
      rwa [Measure.restrict_apply' (centeredCube (localCampanatoCenter k) 1
        one_pos).isOpen.measurableSet, Set.inter_comm] at h
    exact measure_mono_null hsub2 hnull2
  exact measure_mono_null hsub (measure_iUnion_null hnull)


/-- Final assembly: Campanato's criterion in the whole-space, plain-function form
consumed by `torsion_bound` (the `aux_mfd_convergence_hcamp` hole). -/
theorem exists_zero_extension_holder_of_mean_oscillation {d : ℕ} (Cp : Lane4.CampanatoInput d) :
    ∀ alpha : ℝ, alpha ∈ Set.Ioo (0 : ℝ) 1 →
          ∃ C : ℝ, 0 < C ∧
            ∀ (z : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
              (u : SpatialCoordinates d → ℝ) (A : ℝ), 0 ≤ A →
              LocallyIntegrable u volume → LocallyIntegrable (fun x => (u x) ^ 2) volume →
              (∀ x ∉ (centeredCube z rQ hrQ : Set (SpatialCoordinates d)), u x = 0) →
              (∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
                (∫ y in Metric.ball x r,
                    (u y - (volume.real (Metric.ball x r))⁻¹ *
                      ∫ w in Metric.ball x r, u w) ^ 2) ≤
                  A ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * alpha)) →
              ∃ v : SpatialCoordinates d → ℝ,
                v =ᵐ[volume] u ∧
                (∀ x y : SpatialCoordinates d, dist x y ≤ 1 →
                  |v x - v y| ≤ C * A * dist x y ^ alpha) ∧
                ∀ x ∉ (centeredCube z rQ hrQ : Set (SpatialCoordinates d)), v x = 0 := by
  intro alpha halpha
  obtain ⟨ha0, ha1⟩ := halpha
  refine ⟨Cp.C alpha * (2 : ℝ) ^ ((d : ℝ) / 2) * (Real.sqrt d + 1) ^ alpha, ?_, ?_⟩
  · have hCpos := Cp.C_pos alpha ha0 ha1
    have hsd1 : (0:ℝ) < Real.sqrt d + 1 := by positivity
    have hrp : (0:ℝ) < (Real.sqrt d + 1) ^ alpha := Real.rpow_pos_of_pos hsd1 alpha
    positivity
  intro z rQ hrQ u A hA0 hLIu hLIu2 hvanish hosc
  have hcell : ∀ k : SpatialCoordinates d, ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
      U =ᵐ[volume.restrict (centeredCube k 1 one_pos : Set (SpatialCoordinates d))] u ∧
      IsHolderOn alpha (closedCube k 1 one_pos : Set (SpatialCoordinates d)) U ∧
      holderSeminorm alpha (closedCube k 1 one_pos : Set (SpatialCoordinates d)) U ≤
        Cp.C alpha * (A * (2 : ℝ) ^ ((d : ℝ) / 2)) :=
    fun k => local_campanato_cell Cp ha0 ha1 hA0 hLIu hLIu2 hosc k
  choose Uf hUfcont hUfae hUfholder hUfsemi using hcell
  set v : SpatialCoordinates d → ℝ :=
    fun x => Uf (localCampanatoCenter (localCampanatoIndex x)) x with hvdef
  have hAK0 : (0:ℝ) ≤ A * (2:ℝ) ^ ((d:ℝ)/2) := by positivity
  refine ⟨v, ?_, ?_, ?_⟩
  · exact local_campanato_ae_of_cellwise
      (u := u) (Uf := fun k => Uf (localCampanatoCenter k))
      (fun k => hUfae (localCampanatoCenter k))
  · intro x y hxy
    obtain ⟨hxm, hym⟩ := local_campanato_midpoint_mem x y hxy
    set m : SpatialCoordinates d := fun i => (x i + y i) / 2 with hmdef
    have hvx : v x = Uf m x :=
      local_campanato_bridge (hUfcont _) (hUfcont m) (hUfae _) (hUfae m)
        (localCampanatoHome_mem x) hxm
    have hvy : v y = Uf m y :=
      local_campanato_bridge (hUfcont _) (hUfcont m) (hUfae _) (hUfae m)
        (localCampanatoHome_mem y) hym
    have hclos : closure (centeredCube m 1 one_pos : Set (SpatialCoordinates d)) =
        (closedCube m 1 one_pos : Set (SpatialCoordinates d)) := by
      show closure (Metric.ball m (1 / 2)) = Metric.closedBall m (1 / 2)
      exact closure_ball m (by norm_num)
    have hxclosed : x ∈ (closedCube m 1 one_pos : Set (SpatialCoordinates d)) := hclos ▸ hxm
    have hyclosed : y ∈ (closedCube m 1 one_pos : Set (SpatialCoordinates d)) := hclos ▸ hym
    have hCK0 : (0:ℝ) ≤ Cp.C alpha * (A * (2:ℝ) ^ ((d:ℝ)/2)) := by
      have := Cp.C_pos alpha ha0 ha1
      positivity
    have hpt := local_campanato_holder_pt m one_pos ha0
      (hUfholder m) (hUfsemi m) hCK0 hxclosed hyclosed
    rw [hvx, hvy]
    have hmono : (Real.sqrt d) ^ alpha ≤ (Real.sqrt d + 1) ^ alpha :=
      Real.rpow_le_rpow (Real.sqrt_nonneg _) (by linarith) ha0.le
    have hdxynn : (0:ℝ) ≤ dist x y ^ alpha := by positivity
    calc |Uf m x - Uf m y|
        ≤ Cp.C alpha * (A * (2:ℝ) ^ ((d:ℝ)/2)) * (Real.sqrt d) ^ alpha * dist x y ^ alpha := hpt
      _ ≤ Cp.C alpha * (A * (2:ℝ) ^ ((d:ℝ)/2)) * (Real.sqrt d + 1) ^ alpha * dist x y ^ alpha := by
          gcongr
      _ = Cp.C alpha * (2:ℝ) ^ ((d:ℝ)/2) * (Real.sqrt d + 1) ^ alpha * A * dist x y ^ alpha := by
          ring
  · intro x hx
    have hhome := localCampanatoHome_mem x
    set k : SpatialCoordinates d := localCampanatoHome x with hkdef
    -- `x ≠ z`, since `x` is outside the open cube but `z` is its centre.
    have hxz : x ≠ z := by
      rintro rfl
      exact hx (Metric.mem_ball_self (by positivity))
    haveI : Nontrivial (SpatialCoordinates d) := ⟨x, z, hxz⟩
    -- the interior of the closed support cube is exactly the open support cube.
    have hint : interior (closedCube z rQ hrQ : Set (SpatialCoordinates d)) =
        (centeredCube z rQ hrQ : Set (SpatialCoordinates d)) :=
      interior_closedBall' z (rQ / 2)
    have hxclB : x ∈ closure ((closedCube z rQ hrQ : Set (SpatialCoordinates d))ᶜ) := by
      rw [closure_compl, hint]
      exact hx
    set W : Set (SpatialCoordinates d) :=
      (centeredCube k 1 one_pos : Set (SpatialCoordinates d)) ∩
        (closedCube z rQ hrQ : Set (SpatialCoordinates d))ᶜ with hWdef
    have hWopen : IsOpen W :=
      (centeredCube k 1 one_pos).isOpen.inter (closedCube z rQ hrQ).isCompact.isClosed.isOpen_compl
    have hxW : x ∈ closure W :=
      local_campanato_mem_closure_inter (centeredCube k 1 one_pos).isOpen hhome hxclB
    have hsub : (closedCube z rQ hrQ : Set (SpatialCoordinates d))ᶜ ⊆
        (centeredCube z rQ hrQ : Set (SpatialCoordinates d))ᶜ :=
      Set.compl_subset_compl.mpr (centeredCube_subset_closedCube z hrQ)
    have huW : ∀ y ∈ W, u y = 0 := fun y hy => hvanish y (hsub hy.2)
    have hUf0 : Uf k =ᵐ[volume.restrict W] (fun _ : SpatialCoordinates d => (0:ℝ)) := by
      have h1 : Uf k =ᵐ[volume.restrict W] u :=
        ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left (hUfae k)
      refine h1.trans ?_
      apply ae_iff.mpr
      have hz0 : W ∩ {y | ¬ u y = (0:ℝ)} = ∅ := by
        ext y
        simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, Set.mem_setOf_eq]
        rintro ⟨hyW, hyne⟩
        exact hyne (huW y hyW)
      rw [Measure.restrict_apply' hWopen.measurableSet, Set.inter_comm, hz0]
      exact measure_empty
    have hUfzero : Set.EqOn (Uf k) (fun _ => (0:ℝ)) (closure W) :=
      local_campanato_glue hWopen (hUfcont k) continuous_const hUf0
    exact hUfzero hxW


end SubdiffusiveProcess.Analysis
