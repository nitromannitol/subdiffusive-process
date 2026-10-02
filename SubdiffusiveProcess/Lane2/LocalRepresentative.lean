import SubdiffusiveProcess.Lane2.KilledTransport
import SubdiffusiveProcess.Lane2.VecDotForm
import SubdiffusiveProcess.Lane2.OddVanishing
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.Interior.InhomogeneousLocalRegularity
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.Interior.InhomogeneousGlobalRepresentative

/-!
# The local continuous representative at a boundary point

The transported datum on the doubled box solves a forced divergence-form
equation whose coefficient is continuous with contrast `1` at `x₀`.  GMC's
small-contrast Schauder estimate therefore produces a continuous representative
on a Euclidean ball about `x₀`, and the datum's oddness about the plane through
`x₀` forces that representative to vanish at `x₀`.
-/

open MeasureTheory Set TopologicalSpace Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

noncomputable section

namespace SubdiffusiveProcess

variable {d : ℕ}

/-- A single-coordinate reflection about `x₀` preserves the Euclidean distance
to `x₀`. -/
theorem lane2_euclideanSqDist_coordinateReflection (x₀ y : SpatialCoordinates d)
    (i : Fin d) :
    euclideanSqDist (coordinateReflection x₀ {i} y) x₀ = euclideanSqDist y x₀ := by
  simp only [euclideanSqDist, vecNormSq, vecDot]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hj : j = i
  · subst hj
    have h1 : (coordinateReflection x₀ {j} y - x₀) j = -(y j - x₀ j) := by
      simp only [Pi.sub_apply, coordinateReflection_single_apply_self]
      ring
    have h2 : (y - x₀) j = y j - x₀ j := rfl
    rw [h1, h2]
    ring
  · have h1 : (coordinateReflection x₀ {i} y - x₀) j = (y - x₀) j := by
      simp only [Pi.sub_apply, coordinateReflection_single_apply_of_ne _ hj]
    rw [h1]

/-- Euclidean balls centred at `x₀` are invariant under reflection about `x₀`. -/
theorem lane2_coordinateReflection_preimage_euclideanBall (x₀ : SpatialCoordinates d)
    (i : Fin d) (R : ℝ) :
    coordinateReflection x₀ {i} ⁻¹' euclideanBall x₀ R = euclideanBall x₀ R := by
  ext y
  simp only [Set.mem_preimage, euclideanBall, Set.mem_setOf_eq,
    lane2_euclideanSqDist_coordinateReflection]

/-- The divergence-form weak equation only sees the coefficient's `L^∞` class. -/
theorem lane2_isDivFormWeakSolutionOn_congr_coefficient {W : Set (SpatialCoordinates d)}
    {a b : SpatialCoordinates d → ℝ} (hab : a =ᵐ[volume.restrict W] b)
    {u : H1Function W} {g : SpatialCoordinates d → SpatialCoordinates d}
    (hu : IsDivFormWeakSolutionOn a W u g) : IsDivFormWeakSolutionOn b W u g := by
  intro φ
  rw [← hu φ]
  refine integral_congr_ae ?_
  filter_upwards [hab] with x hx
  rw [hx]

/-- Small contrast on a small ball for any continuous positive coefficient. -/
theorem lane2_exists_ball_smallContrast {s : SpatialCoordinates d → ℝ}
    (hs : Continuous s) (x₀ : SpatialCoordinates d) (hpos : 0 < s x₀)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ rho : ℝ, 0 < rho ∧
      ∀ y ∈ Metric.ball x₀ rho, |(s x₀)⁻¹ * s y - 1| ≤ delta := by
  have hcont : Continuous (fun y => (s x₀)⁻¹ * s y - 1) :=
    (continuous_const.mul hs).sub continuous_const
  have hval : (s x₀)⁻¹ * s x₀ - 1 = 0 := by
    rw [inv_mul_cancel₀ (ne_of_gt hpos), sub_self]
  have hev : ∀ᶠ y in nhds x₀, |(s x₀)⁻¹ * s y - 1| ≤ delta := by
    have h0 : Filter.Tendsto (fun y => (s x₀)⁻¹ * s y - 1) (nhds x₀) (nhds 0) := by
      have h1 := hcont.continuousAt (x := x₀)
      rw [ContinuousAt, hval] at h1
      exact h1
    have := h0 (Metric.closedBall_mem_nhds (0 : ℝ) hdelta)
    filter_upwards [this] with y hy
    simpa [Real.dist_eq, abs_sub_comm] using hy
  obtain ⟨rho, hrho, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  exact ⟨rho, hrho, hball⟩

/-- `smallContrastThreshold` is positive below the endpoint exponent. -/
theorem lane2_smallContrastThreshold_pos (d : ℕ) {alpha : ℝ} (h : alpha < 1) :
    0 < smallContrastThreshold d alpha := by
  rw [smallContrastThreshold]
  have h1 : (0 : ℝ) < (2 : ℝ) ^ (-(3 + (d : ℝ) / 2)) := Real.rpow_pos_of_pos (by norm_num) _
  nlinarith [h1]

theorem lane2_euclideanBall_subset_ball (x₀ : SpatialCoordinates d) (R : ℝ)
    (hR : 0 ≤ R) : euclideanBall x₀ R ⊆ Metric.ball x₀ R := by
  intro x hx
  have hsq : euclideanDist x x₀ ^ 2 < R ^ 2 := by
    have hmem : euclideanSqDist x x₀ < R ^ 2 := hx
    rwa [euclideanSqDist_eq_euclideanDist_sq] at hmem
  have hnn : 0 ≤ euclideanDist x x₀ := euclideanDist_nonneg x x₀
  have hlt : euclideanDist x x₀ < R := by nlinarith [hsq, hnn, hR]
  have hle : ‖x - x₀‖ ≤ euclideanDist x x₀ := by
    rw [euclideanDist]
    exact norm_le_euclideanNorm _
  rw [Metric.mem_ball, dist_eq_norm]
  linarith

theorem lane2_euclideanBall_mono (x₀ : SpatialCoordinates d) {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r ≤ R) : euclideanBall x₀ r ⊆ euclideanBall x₀ R := by
  intro y hy
  have hy' : euclideanSqDist y x₀ < r ^ 2 := hy
  have : r ^ 2 ≤ R ^ 2 := by nlinarith
  exact lt_of_lt_of_le hy' this

theorem lane2_mem_euclideanBall_self (x₀ : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    x₀ ∈ euclideanBall x₀ r := by
  show euclideanSqDist x₀ x₀ < r ^ 2
  rw [euclideanSqDist_self]
  positivity

/-- **The local continuous representative at the boundary point.**  The
transported datum solves a forced divergence-form equation whose coefficient is
continuous with contrast `1` at `x₀`; GMC's small-contrast Schauder estimate
gives a continuous representative on a Euclidean ball about `x₀`, and the
datum's oddness about the plane through `x₀` forces it to vanish there. -/
theorem lane2_exists_local_odd_representative
    [NeZero d] (hd : 2 ≤ d)
    (B : Opens (SpatialCoordinates d))
    (x₀ : SpatialCoordinates d) (hx₀ : x₀ ∈ (B : Set (SpatialCoordinates d)))
    (i₀ : Fin d)
    (s : SpatialCoordinates d → ℝ) (hs : Continuous s) (hspos : 0 < s x₀)
    (A : PositiveCoefficient B)
    (hA : (A.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (B : Set (SpatialCoordinates d))] s)
    (w : SobolevData B) (hw : w ∈ weakSobolevGraph B)
    (g : SpatialCoordinates d → SpatialCoordinates d)
    (alpha : ℝ) (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hgLp : MemVectorLpOn (B : Set (SpatialCoordinates d))
      (schauderSourceExponent d alpha) g)
    (hsolve : lane2_SolvesOn A w (fun v => -∫ x in (B : Set (SpatialCoordinates d)),
      ∑ i : Fin d, g x i * ((v.2 i : DomainL2 B) : SpatialCoordinates d → ℝ) x))
    (hint : ∀ (u v : H1Function (B : Set (SpatialCoordinates d))) (i : Fin d),
      IntegrableOn (fun x => (A.val : SpatialCoordinates d → ℝ) x *
        (u.grad x i * v.grad x i)) (B : Set (SpatialCoordinates d)) volume)
    (hodd : ∀ᵐ x ∂(volume.restrict (B : Set (SpatialCoordinates d))),
      ((w.1 : DomainL2 B) : SpatialCoordinates d → ℝ)
          (coordinateReflection x₀ {i₀} x)
        = -(((w.1 : DomainL2 B) : SpatialCoordinates d → ℝ) x)) :
    ∃ (rho : ℝ) (v : SpatialCoordinates d → ℝ), 0 < rho ∧
      euclideanBall x₀ rho ⊆ (B : Set (SpatialCoordinates d)) ∧
      ContinuousOn v (euclideanBall x₀ rho) ∧
      (v =ᵐ[volume.restrict (euclideanBall x₀ rho)]
        ((w.1 : DomainL2 B) : SpatialCoordinates d → ℝ)) ∧
      v x₀ = 0 := by
  classical
  -- read the datum as an upstream `H¹` function
  obtain ⟨u, huval, hugrad⟩ :=
    exists_nativeH1Function_of_weakSobolevGraph (Ω := B) ⟨w, hw⟩
  have hwu : sobolevDataOfH1 u = w := by
    have hval : u.toFun = ((w.1 : DomainL2 B) : SpatialCoordinates d → ℝ) := huval
    have hgr : ∀ i : Fin d, (fun x => u.grad x i)
        = ((w.2 i : DomainL2 B) : SpatialCoordinates d → ℝ) := by
      intro i
      funext x
      rw [hugrad]
    have h1 : (sobolevDataOfH1 u).1 = w.1 := by
      show MemLp.toLp u.toFun u.memL2 = w.1
      simp only [hval]
      exact Lp.toLp_coeFn w.1 _
    have h2 : (sobolevDataOfH1 u).2 = w.2 := by
      funext i
      show MemLp.toLp (fun x => u.grad x i) (u.gradMemL2 i) = w.2 i
      simp only [hgr i]
      exact Lp.toLp_coeFn (w.2 i) _
    exact Prod.ext h1 h2
  -- the forced equation in GMC's divergence form
  have hdiv : IsDivFormWeakSolutionOn (A.val : SpatialCoordinates d → ℝ)
      (B : Set (SpatialCoordinates d)) u g := by
    refine isDivFormWeakSolutionOn_of_weak_equation A u g (fun v i => hint u v i) ?_
    intro φ
    rw [hwu, hsolve _ (sobolevDataOfH1_mem_killed φ), neg_inj]
    refine integral_congr_ae ?_
    have hall : ∀ᵐ x ∂(volume.restrict (B : Set (SpatialCoordinates d))),
        ∀ i : Fin d,
          (((sobolevDataOfH1 φ.toH1Function).2 i : DomainL2 B) :
            SpatialCoordinates d → ℝ) x = φ.toH1Function.grad x i :=
      ae_all_iff.2 (fun i => sobolevDataOfH1_snd_coeFn φ.toH1Function i)
    filter_upwards [hall] with x hx
    rw [vecDot]
    exact Finset.sum_congr rfl (fun i _ => by rw [hx i])
  have hdivs : IsDivFormWeakSolutionOn s (B : Set (SpatialCoordinates d)) u g :=
    lane2_isDivFormWeakSolutionOn_congr_coefficient hA hdiv
  -- choose the contrast parameter and the radius
  set delta : ℝ := min (smallContrastThreshold d alpha) (1 / 2) with hdeltadef
  have hdeltapos : 0 < delta :=
    lt_min (lane2_smallContrastThreshold_pos d halpha.2) (by norm_num)
  obtain ⟨r1, hr1, hclose1⟩ := lane2_exists_ball_smallContrast hs x₀ hspos hdeltapos
  obtain ⟨r2, hr2, hsub2⟩ := Metric.isOpen_iff.mp B.isOpen x₀ hx₀
  set rho : ℝ := min r1 r2 with hrhodef
  have hrho : 0 < rho := lt_min hr1 hr2
  have hballB : euclideanBall x₀ rho ⊆ (B : Set (SpatialCoordinates d)) := by
    refine Set.Subset.trans ?_ hsub2
    refine Set.Subset.trans (lane2_euclideanBall_subset_ball x₀ rho hrho.le) ?_
    exact Metric.ball_subset_ball (min_le_right r1 r2)
  have hclose : ∀ y ∈ euclideanBall x₀ rho, |(s x₀)⁻¹ * s y - 1| ≤ delta := by
    intro y hy
    refine hclose1 y ?_
    exact Metric.ball_subset_ball (min_le_left r1 r2)
      (lane2_euclideanBall_subset_ball x₀ rho hrho.le hy)
  -- GMC's small-contrast Schauder estimate
  obtain ⟨uRep, hcontRep, haeRep, -, -⟩ :=
    exists_physicalBallRepresentative_smallContrast_inhomogeneous
      (W := (B : Set (SpatialCoordinates d))) B.isOpen hs.continuousOn hdivs hrho hballB
      (s x₀) delta alpha hd halpha hdeltapos.le (min_le_left _ _)
      (lt_of_le_of_lt (min_le_right _ _) (by norm_num)) hclose hgLp
  refine ⟨rho / 2, uRep, by positivity, ?_, hcontRep, ?_, ?_⟩
  · exact Set.Subset.trans
      (lane2_euclideanBall_mono x₀ (by positivity) (by linarith)) hballB
  · refine haeRep.trans ?_
    rw [show u.toFun = fun x => ((w.1 : DomainL2 B) : SpatialCoordinates d → ℝ) x from huval]
  · -- oddness of the representative forces the value at `x₀`
    have hS : coordinateReflection x₀ {i₀} ⁻¹'
        (euclideanBall x₀ (rho / 2)) = euclideanBall x₀ (rho / 2) :=
      lane2_coordinateReflection_preimage_euclideanBall x₀ i₀ (rho / 2)
    have hsub : euclideanBall x₀ (rho / 2) ⊆ (B : Set (SpatialCoordinates d)) :=
      Set.Subset.trans (lane2_euclideanBall_mono x₀ (by positivity) (by linarith)) hballB
    have hoddS : ∀ᵐ x ∂(volume.restrict (euclideanBall x₀ (rho / 2))),
        uRep (coordinateReflection x₀ {i₀} x) = -(uRep x) := by
      refine lane2_ae_odd_of_ae_eq (S := ⟨euclideanBall x₀ (rho / 2),
        isOpen_euclideanBall x₀ (rho / 2)⟩) x₀ {i₀} hS
        (f := uRep)
        (g := ((w.1 : DomainL2 B) : SpatialCoordinates d → ℝ)) ?_ ?_
      · refine haeRep.trans ?_
        rw [show u.toFun
          = fun x => ((w.1 : DomainL2 B) : SpatialCoordinates d → ℝ) x from huval]
      · exact ae_restrict_of_ae_restrict_of_subset
          (μ := (volume : Measure (SpatialCoordinates d))) hsub hodd
    refine lane2_eq_zero_of_ae_odd_of_continuousOn
      (isOpen_euclideanBall x₀ (rho / 2)) x₀ {i₀} ?_ hcontRep hoddS
      (lane2_mem_euclideanBall_self x₀ (by positivity)) ?_
    · intro y hy
      have hpre : y ∈ coordinateReflection x₀ {i₀} ⁻¹'
          (euclideanBall x₀ (rho / 2)) := by
        rw [hS]; exact hy
      exact hpre
    · exact coordinateReflection_single_eq_self x₀ i₀ rfl

/-- A weakly harmonic function is a divergence-form weak solution with zero
source. -/
theorem lane2_isDivFormWeakSolutionOn_of_weaklyHarmonic
    {W : Set (SpatialCoordinates d)} {a : SpatialCoordinates d → ℝ}
    {u : H1Function W} (hharm : IsWeaklyHarmonicOn a W u) :
    IsDivFormWeakSolutionOn a W u 0 := by
  intro φ
  rw [hharm φ]
  simp [vecDot]

/-- **The interior continuous representative.**  A weakly harmonic function with
a continuous positive coefficient has a continuous canonical representative on
the whole open carrier, equal to it almost everywhere.  This is GMC's
`continuousOn_and_ae_eq_euclideanBallAverageRepresentative_inhomogeneous` with
zero source; no Hölder or oscillation input is used. -/
theorem lane2_interior_continuous_representative [NeZero d] (hd : 2 ≤ d)
    {W : Set (SpatialCoordinates d)} (hW : IsOpen W)
    {a : SpatialCoordinates d → ℝ} (ha : ContinuousOn a W)
    (hapos : ∀ x ∈ W, 0 < a x)
    {u : H1Function W} (hharm : IsWeaklyHarmonicOn a W u) :
    ContinuousOn (euclideanBallAverageRepresentative u.toFun) W ∧
      euclideanBallAverageRepresentative u.toFun
        =ᵐ[volume.restrict W] u.toFun := by
  have hg : MemVectorLpOn W (schauderSourceExponent d (1 / 2))
      (0 : SpatialCoordinates d → SpatialCoordinates d) := by
    have : (fun x : SpatialCoordinates d =>
        HilbertVec.ofVec ((0 : SpatialCoordinates d → SpatialCoordinates d) x))
        = fun _ => (0 : HilbertVec d) := by
      funext x
      simp [HilbertVec.ofVec]
    rw [MemVectorLpOn, this]
    exact MemLp.zero
  exact continuousOn_and_ae_eq_euclideanBallAverageRepresentative_inhomogeneous
    hd hW ha hapos (lane2_isDivFormWeakSolutionOn_of_weaklyHarmonic hharm) hg

/-- **The Schauder source condition is an integrability condition, not a Hölder
one.**  `schauderSourceExponent d alpha = d / (1 - alpha)` is finite, so a field
that is bounded on a bounded carrier lies in the class: at `alpha = 1/2` the
exponent is `2d`, and the forcing `A_N ∇φ` of a cell problem is bounded there
because the coefficient is bounded and `φ` is smooth. -/
theorem lane2_memVectorLpOn_of_bounded {W : Set (SpatialCoordinates d)}
    (hWb : Bornology.IsBounded W)
    {g : SpatialCoordinates d → SpatialCoordinates d}
    (hmeas : AEStronglyMeasurable (fun x => HilbertVec.ofVec (g x))
      (volume.restrict W))
    {M : ℝ} (hbound : ∀ᵐ x ∂(volume.restrict W),
      ‖HilbertVec.ofVec (g x)‖ ≤ M) (p : ℝ) :
    MemVectorLpOn W p g := by
  have hWfin : volume W ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono subset_closure)
      hWb.isCompact_closure.measure_lt_top)
  haveI : IsFiniteMeasure (volume.restrict W) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_ne le_top hWfin
  have htop : MemLp (fun x => HilbertVec.ofVec (g x)) (⊤ : ENNReal)
      (volume.restrict W) :=
    memLp_top_of_bound hmeas M hbound
  exact htop.mono_exponent le_top

end SubdiffusiveProcess
