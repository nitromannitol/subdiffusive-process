import SubdiffusiveProcess.Lane2.ExternalInputs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace Paper

private lemma aux_large_origin_cube
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ Q : Homogenization.TriadicCube d, 0 < Homogenization.cubeScaleFactor Q ∧
      (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ⊆
        Homogenization.openCubeSet Q := by
  let A : ℝ := max (2 * ‖z‖ + r) 1
  have hA : (1 : ℝ) ≤ A := by
    exact le_max_right _ _
  obtain ⟨m, hmle, hmlt⟩ :=
    exists_nat_pow_near hA (by norm_num : (1 : ℝ) < (3 : ℝ))
  let Q : Homogenization.TriadicCube d :=
    Homogenization.originCube d ((m + 1 : ℕ) : ℤ)
  have hscale : (3 : ℝ) ^ (m + 1) = Homogenization.cubeScaleFactor Q := by
    dsimp [Q, Homogenization.originCube, Homogenization.cubeScaleFactor]
    have hcast : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by omega
    rw [← hcast, zpow_natCast]
  have hbig : 2 * ‖z‖ + r < Homogenization.cubeScaleFactor Q := by
    rw [← hscale]
    exact lt_of_le_of_lt (le_max_left _ _) hmlt
  have hQpos : 0 < Homogenization.cubeScaleFactor Q := by
    rw [← hscale]
    positivity
  refine ⟨Q, hQpos, ?_⟩
  rw [show (centeredCube z r hr : Set (SpatialCoordinates d)) = Metric.ball z (r / 2) by rfl]
  intro x hx
  have hx' : x ∈ Metric.closedBall z (r / 2) :=
    Metric.closure_ball_subset_closedBall hx
  have hdist : dist x z ≤ r / 2 := Metric.mem_closedBall.mp hx'
  have hxi : dist x (0 : SpatialCoordinates d) ≤ dist x z + ‖z‖ := by
    calc
      dist x (0 : SpatialCoordinates d) ≤ dist x z + dist z 0 := dist_triangle _ _ _
      _ = dist x z + ‖z‖ := by simp
  have hnorm : dist x (0 : SpatialCoordinates d) < Homogenization.cubeScaleFactor Q / 2 := by
    nlinarith [hbig]
  rw [Homogenization.mem_openCubeSet_originCube_iff]
  intro i
  have hcoord : |x i| ≤ dist x (0 : SpatialCoordinates d) := by
    letI : ∀ j : Fin d, SeminormedAddGroup ℝ := fun _ => inferInstance
    simpa [dist_eq_norm] using
      (norm_le_pi_norm (G := fun _ : Fin d => ℝ) (f := x) i)
  have habs : |x i| < Homogenization.cubeScaleFactor Q / 2 :=
    lt_of_le_of_lt hcoord hnorm
  simpa [Homogenization.cubeScaleFactor, div_eq_mul_inv, mul_comm] using
    (abs_lt.mp habs)

private lemma aux_measure_univ_eq_of_compl_null
    {α : Type*} [MeasurableSpace α] (ν : Measure α) (S : Set α) (hS : MeasurableSet S)
    (hnull : ν Sᶜ = 0) : ν Set.univ = ν S := by
  rw [← measure_add_measure_compl hS, hnull, add_zero]

private lemma aux_extend_ball_growth
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (t K : ℝ) (ht : (d : ℝ) - 1 < t) (hK : 0 ≤ K)
    (ν : Measure (SpatialCoordinates d))
    (hν : ν Set.univ < (⊤ : ℝ≥0∞))
    (S : Set (SpatialCoordinates d)) (hS : MeasurableSet S)
    (hSgrowth : ∀ x ∈ S, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      ν (Metric.ball x ρ) ≤ ENNReal.ofReal (K * ρ ^ t))
    (hsupp : ν Sᶜ = 0) (Q : Homogenization.TriadicCube d)
    (hroot : S ⊆ closure (Homogenization.openCubeSet Q)) :
    ∀ x ∈ closure (Homogenization.openCubeSet Q), ∀ ρ : ℝ,
      0 < ρ → ρ ≤ 1 →
        ν (Metric.ball x ρ) ≤
          ENNReal.ofReal (((2 : ℝ) ^ t) * (K + (ν Set.univ).toReal) * ρ ^ t) := by
  have htpos : 0 < t := by
    have hdpos : (1 : ℝ) ≤ d := by
      exact_mod_cast (le_trans (by norm_num) hd)
    linarith
  have hM : 0 ≤ (ν Set.univ).toReal := ENNReal.toReal_nonneg
  intro x hx ρ hρ hρ1
  let M : ℝ := (ν Set.univ).toReal
  let B : ℝ := (2 : ℝ) ^ t * (K + M)
  by_cases hsmall : 2 * ρ ≤ 1
  · by_cases hball0 : ν (Metric.ball x ρ) = 0
    · simp [hball0]
    · have hnonempty : (Metric.ball x ρ ∩ S).Nonempty := by
        by_contra hne
        have hsub : Metric.ball x ρ ⊆ Sᶜ := by
          intro y hy hyS
          exact hne ⟨y, hy, hyS⟩
        exact hball0 (measure_mono_null hsub hsupp)
      obtain ⟨y, hyB, hyS⟩ := hnonempty
      have hsubball : Metric.ball x ρ ⊆ Metric.ball y (2 * ρ) := by
        intro w hw
        rw [Metric.mem_ball]
        calc
          dist w y ≤ dist w x + dist x y := dist_triangle _ _ _
          _ = dist w x + dist y x := by rw [dist_comm x y]
          _ < ρ + ρ := add_lt_add (Metric.mem_ball.mp hw) (Metric.mem_ball.mp hyB)
          _ = 2 * ρ := by ring
      have htarget := hSgrowth y hyS (2 * ρ) (by positivity) hsmall
      have hpow : (2 * ρ) ^ t = (2 : ℝ) ^ t * ρ ^ t :=
        Real.mul_rpow (by norm_num) hρ.le
      have hreal : K * (2 * ρ) ^ t ≤ B * ρ ^ t := by
        dsimp [B, M]
        rw [hpow]
        calc
          K * ((2 : ℝ) ^ t * ρ ^ t) ≤
              ((ν Set.univ).toReal + K) * ((2 : ℝ) ^ t * ρ ^ t) := by
                gcongr
                linarith
          _ = (2 : ℝ) ^ t * (K + (ν Set.univ).toReal) * ρ ^ t := by ring
      exact (measure_mono hsubball |>.trans htarget).trans
        (ENNReal.ofReal_le_ofReal hreal)
  · have hlarge : 1 < 2 * ρ := lt_of_not_ge hsmall
    have hpow : 1 ≤ (2 * ρ) ^ t :=
      Real.one_le_rpow (le_of_lt hlarge) htpos.le
    have hreal : (ν Set.univ).toReal ≤ B * ρ ^ t := by
      dsimp [B, M]
      calc
        (ν Set.univ).toReal ≤ K + (ν Set.univ).toReal := by linarith
        _ ≤ (K + (ν Set.univ).toReal) * (2 * ρ) ^ t := by
          rw [← one_mul (K + (ν Set.univ).toReal)]
          simpa [one_mul, mul_comm] using
            (mul_le_mul_of_nonneg_left hpow (add_nonneg hK hM))
        _ = (2 : ℝ) ^ t * (K + (ν Set.univ).toReal) * ρ ^ t := by
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hρ.le]
          ring
    calc
      ν (Metric.ball x ρ) ≤ ν Set.univ := measure_mono (subset_univ _)
      _ = ENNReal.ofReal (ν Set.univ).toReal :=
        (ENNReal.ofReal_toReal (ne_of_lt hν)).symm
      _ ≤ ENNReal.ofReal (B * ρ ^ t) := ENNReal.ofReal_le_ofReal hreal

/-- Arbitrary-centered-cube Frostman trace estimate, paper 1897–1919.
Carried-input tick list:
- SOURCE: d, the positive-side centered cube z,r, t > d - 1, finite nu,
  support in the closed cube, K >= 0 and the ball-growth hypothesis are the
  hypotheses in paper 1883–1885.
- SOURCE: f is an ambient smooth datum and v is a half-fractional class
  representing f volume-a.e. on the cube.
- CONCLUDED HERE: smooth f belongs to L2(nu) and its L2(nu) representative
  obeys the squared Frostman trace estimate with the normalized cube
  half-fractional norm of v.
The proof obligations are the grid-face nullity, Jensen increment estimate,
geometric summation and initial-average bound in paper 1897–1919. The
constant is chosen before nu, K, f and v; no trace estimate is assumed. -/
theorem lem_19_arbitrary_cube_frostman_trace
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : (d : ℝ) - 1 < t) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (nu : Measure (SpatialCoordinates d)) (K : ℝ),
        nu Set.univ < (⊤ : ℝ≥0∞) →
        nu (closure (centeredCube z r hr : Set (SpatialCoordinates d)))ᶜ = 0 →
        0 ≤ K →
        (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            nu (Metric.ball x rr) ≤ ENNReal.ofReal (K * rr ^ t)) →
        ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
          MemLp f 2 nu ∧
            ∀ (v : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder),
              (v.val 0 : SpatialCoordinates d → ℝ) =ᵐ[
                volume.restrict
                  (centeredCube z r hr : Set (SpatialCoordinates d))] f →
              ∀ hf : MemLp f 2 nu,
                ‖hf.toLp f‖ ^ 2 ≤
                  C * (K + (nu (closure
                    (centeredCube z r hr : Set (SpatialCoordinates d)))).toReal) *
                    (cubeFractionalL2Norm hd z r hr halfFractionalOrder v) ^ 2 := by
  have htpos : 0 < t := by
    have hdpos : (1 : ℝ) ≤ d := by
      exact_mod_cast (le_trans (by norm_num) hd)
    linarith
  obtain ⟨Q, hQpos, hQclosed⟩ := aux_large_origin_cube d z r hr
  have hroot : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      closure (Homogenization.openCubeSet Q) := by
    intro x hx
    exact subset_closure (hQclosed (subset_closure hx))
  obtain ⟨C₀, hC₀, hCbound⟩ :=
    SubdiffusiveProcess.globalTriadicAverages_L2_limit_norm_bound
      hd Q z hr hroot t ht
  let a : ℝ := (2 : ℝ) ^ t
  have ha1 : 1 ≤ a := by
    dsimp [a]
    exact Real.one_le_rpow (by norm_num) htpos.le
  refine ⟨C₀ * (a + 1), mul_nonneg hC₀ (by linarith), ?_⟩
  intro ν K hν hsupp hK hgrowth f hfcont
  let S : Set (SpatialCoordinates d) :=
    closure (centeredCube z r hr : Set (SpatialCoordinates d))
  have hSmeas : MeasurableSet S := by
    dsimp [S]
    exact isClosed_closure.measurableSet
  have hsuppS : ν Sᶜ = 0 := by
    simpa [S] using hsupp
  have hrootS : S ⊆ closure (Homogenization.openCubeSet Q) := by
    intro x hx
    exact subset_closure (hQclosed hx)
  have hQsupp : ν (closure (Homogenization.openCubeSet Q))ᶜ = 0 := by
    refine measure_mono_null (s := (closure (Homogenization.openCubeSet Q))ᶜ)
      (t := Sᶜ) ?_ hsuppS
    intro x hxQ hxS
    exact hxQ (subset_closure (hQclosed hxS))
  have hSgrowth : ∀ x ∈ S, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      ν (Metric.ball x ρ) ≤ ENNReal.ofReal (K * ρ ^ t) := by
    intro x hx ρ hρ hρ1
    exact hgrowth x hx ρ hρ hρ1
  have hQgrowth := aux_extend_ball_growth d hd z r hr t K ht hK ν hν S hSmeas
    hSgrowth hsuppS Q hrootS
  letI : IsFiniteMeasure ν := ⟨hν⟩
  have hmass : ν Set.univ = ν S :=
    aux_measure_univ_eq_of_compl_null ν S hSmeas hsuppS
  have hmassreal : (ν Set.univ).toReal = (ν S).toReal :=
    congrArg ENNReal.toReal hmass
  have hfν : MemLp f 2 ν :=
    SubdiffusiveProcess.contDiff_memLp_of_finiteMeasure_supported_closure
      Q hQpos ν hQsupp f hfcont
  refine ⟨hfν, ?_⟩
  intro v hv
  intro hf
  let KQ : ℝ := a * (K + (ν Set.univ).toReal)
  have hKQ : 0 ≤ KQ := by
    dsimp [KQ]
    positivity
  let traceAverage {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
      (g : SpatialCoordinates d → ℝ) (n : ℕ) (x : SpatialCoordinates d) : ℝ :=
    ∑ k : OddGridIndex d (triadicHalf n),
      (oddGridCell z r hr (triadicHalf n) k : Set (SpatialCoordinates d)).indicator
        (fun _ => averageOn
          (oddGridCell z r hr (triadicHalf n) k : Set (SpatialCoordinates d)) g) x
  have huv : MemLp (v.val 0) 2
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    Lp.memLp (v.val 0)
  have hkernel := (scalar_halfFractional_kernel_lt_top hd z r hr v).ne
  have hE : ∀ n : ℕ, MemLp (traceAverage z hr (v.val 0) n) 2 ν := by
    simpa only [traceAverage] using
      (SubdiffusiveProcess.globalTriadicAverages_memLp_and_increment_bound
        hd Q z hr hroot KQ t hKQ ht 0 ν inferInstance hQsupp hQgrowth
        (v.val 0) huv).1
  have hsum : Summable (fun n : ℕ =>
      (eLpNorm (fun x => traceAverage z hr (v.val 0) (n + 1) x -
        traceAverage z hr (v.val 0) n x) 2 ν).toReal) := by
    simpa only [traceAverage] using
      (SubdiffusiveProcess.globalTriadicAverages_summable_increment_eLpNorm_of_finite_kernel
        hd Q z hr hroot KQ t hKQ ht ν inferInstance hQsupp hQgrowth
        (v.val 0) huv hkernel)
  obtain ⟨g, hg, hgt⟩ :=
    SubdiffusiveProcess.globalTriadicAverages_exists_L2_limit_of_summable_increments
      z hr ν (v.val 0)
      (by simpa only [traceAverage] using hE)
      (by simpa only [traceAverage] using hsum)
  have hplanes : ∀ (i : Fin d) (c : ℝ), ν {x | x i = c} = 0 :=
    (SubdiffusiveProcess.growth_cube_boundary_noAtoms hd Q ν inferInstance KQ t
      hKQ ht hQsupp hQgrowth).1
  have heq : ∀ n : ℕ, traceAverage z hr f n = traceAverage z hr (v.val 0) n := by
    intro n
    simpa only [traceAverage] using
      (SubdiffusiveProcess.globalTriadicAverages_congr_ae z hr n f (v.val 0) hv.symm)
  have hEf : ∀ n : ℕ, MemLp (traceAverage z hr f n) 2 ν := by
    intro n
    rw [heq n]
    exact hE n
  have hgtf : Tendsto (fun n => eLpNorm
      (fun x => traceAverage z hr f n x - g x) 2 ν) atTop (nhds 0) := by
    simpa only [heq] using hgt
  have hgaeq : g =ᵐ[ν]
      (centeredCube z r hr : Set (SpatialCoordinates d)).indicator f := by
    apply SubdiffusiveProcess.globalTriadicAverages_L2_limit_eq_ae_indicator_of_continuousOn
      hd z hr ν hplanes f hfcont.continuous.continuousOn g
    · simpa only [traceAverage] using hEf
    · exact hg
    · simpa only [traceAverage] using hgtf
  have hSae : ∀ᵐ x ∂ν, x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    SubdiffusiveProcess.ae_mem_centeredCube_of_support_closure_of_hyperplanes_null
      z hr ν hsupp hplanes
  have hgf : g =ᵐ[ν] f := by
    filter_upwards [hgaeq, hSae] with x hxg hxS
    rw [hxg, Set.indicator_of_mem]
    exact hxS
  have hbound := hCbound KQ hKQ ν inferInstance hQsupp hQgrowth v huv hkernel
  dsimp only at hbound
  have hgbound := hbound hE g hg hgt
  have hQmass : (ν (closure (Homogenization.openCubeSet Q))).toReal ≤
      (ν Set.univ).toReal := by
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))
  have hcoeff : KQ + (ν (closure (Homogenization.openCubeSet Q))).toReal ≤
      (a + 1) * (K + (ν S).toReal) := by
    dsimp [KQ]
    calc
      a * (K + (ν Set.univ).toReal) +
          (ν (closure (Homogenization.openCubeSet Q))).toReal ≤
          a * (K + (ν Set.univ).toReal) + (ν Set.univ).toReal :=
        add_le_add (le_refl _) hQmass
      _ = a * (K + (ν S).toReal) + (ν S).toReal := by rw [hmassreal]
      _ ≤ a * (K + (ν S).toReal) + (K + (ν S).toReal) := by
        gcongr
        linarith
      _ = (a + 1) * (K + (ν S).toReal) := by ring
  calc
    ‖hf.toLp f‖ ^ 2 = (eLpNorm f 2 ν).toReal ^ 2 := by
      rw [Lp.norm_toLp]
    _ = (eLpNorm g 2 ν).toReal ^ 2 := by
      rw [eLpNorm_congr_ae hgf]
    _ ≤ C₀ * (KQ + (ν (closure (Homogenization.openCubeSet Q))).toReal) *
        (cubeFractionalL2Norm hd z r hr halfFractionalOrder v) ^ 2 := hgbound
    _ ≤ C₀ * ((a + 1) * (K + (ν S).toReal)) *
        (cubeFractionalL2Norm hd z r hr halfFractionalOrder v) ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcoeff hC₀) (sq_nonneg _)
    _ = C₀ * (a + 1) * (K +
        (ν (closure (centeredCube z r hr : Set (SpatialCoordinates d)))).toReal) *
        (cubeFractionalL2Norm hd z r hr halfFractionalOrder v) ^ 2 := by
      dsimp [S]
      ring

end Paper
