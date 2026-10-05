module

public import SubdiffusiveProcess.EllipticRegularity.InDetContHalf
public import SubdiffusiveProcess.EllipticRegularity.InDetLowAlphaLift

@[expose] public section

/-!
# Continuous representatives of sourced native weak solutions, `0 < alpha < 1`

The native equation is converted to GMC's massive equation, restricted to small translated
triadic cubes, given a small-contrast Schauder representative, and glued over a countable cover.
The residual lift `aux_in_deterministic_lowalpha_lift_twoD_translateSet` places `g` in
`L^{2d}` for every source exponent `q ≥ 2d/3`; here `q = d/(1-alpha) > d`, allowing
the full range `0 < alpha < 1`.
-/

open MeasureTheory Set Metric Filter Topology TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open Homogenization hiding Vec

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- **Local continuity, `0 < alpha < 1`.**  Around every point of an open set on which the
scalar equation holds with a continuous positive coefficient (up to an a.e. change) and a
source in `L^{d/(1-alpha)}`, the canonical ball-average representative is continuous and
equal to the solution a.e. on a neighbourhood. -/
theorem aux_in_deterministic_lowalpha_local_cont {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {W : Set (Vec d)} (hW : IsOpen W) {c s : Vec d → ℝ} (hcs : c =ᵐ[volume.restrict W] s)
    (hs : ContinuousOn s W) (hspos : ∀ x ∈ W, 0 < s x)
    {u : H1Function W} {f : Vec d → ℝ} (alpha : ℝ) (halpha : 0 < alpha)
    (halpha1 : alpha < 1)
    (hf : MemLp f (ENNReal.ofReal ((d : ℝ) / (1 - alpha))) (volume.restrict W))
    (hu : IsMassiveWeakSolutionOn c (fun _ => 1) 0 W u f)
    (x0 : Vec d) (hx0 : x0 ∈ W) :
    ∃ T : Set (Vec d), IsOpen T ∧ x0 ∈ T ∧ T ⊆ W ∧
      ContinuousOn (euclideanBallAverageRepresentative u.toFun) T ∧
      euclideanBallAverageRepresentative u.toFun =ᵐ[volume.restrict T] u.toFun := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hW x0 hx0
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (show (1 / 3 : ℝ) < 1 by norm_num)
  set m : ℤ := -(n : ℤ) with hm
  set T : Set (Vec d) := translateSet x0 (openCubeSet (originCube d m)) with hTdef
  have hTball : T = Metric.ball x0 ((3 : ℝ) ^ m / 2) :=
    aux_in_deterministic_regularity_translateSet_eq_ball x0 m
  have h3m : (3 : ℝ) ^ m = (1 / 3 : ℝ) ^ n := by
    rw [hm, zpow_neg, zpow_natCast, one_div, inv_pow]
  have hTopen : IsOpen T := by rw [hTball]; exact Metric.isOpen_ball
  have hxT : x0 ∈ T := by rw [hTball]; exact Metric.mem_ball_self (by positivity)
  have hTW : T ⊆ W := by
    rw [hTball]
    refine (Metric.ball_subset_ball ?_).trans hball
    rw [h3m]; linarith [pow_pos (show (0 : ℝ) < 1 / 3 by norm_num) n]
  -- the equation on `T`
  set uT := u.restrict hTopen hTW with huT
  have huT' : IsMassiveWeakSolutionOn c (fun _ => 1) 0 T uT f :=
    aux_in_deterministic_regularity_massive_restrict hW hTopen hTW hu
  -- the source exponent `q = d/(1-alpha) > d`
  have h1a : 0 < 1 - alpha := by linarith
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hqd : (d : ℝ) < (d : ℝ) / (1 - alpha) := by
    rw [lt_div_iff₀ h1a]
    nlinarith
  have hq2 : (2 : ℝ) < (d : ℝ) / (1 - alpha) := lt_of_le_of_lt hd2 hqd
  let q : FiniteLpExponent :=
    { exponent := ENNReal.ofReal ((d : ℝ) / (1 - alpha))
      one_lt := by
        rw [ENNReal.one_lt_ofReal]; linarith
      lt_top := ENNReal.ofReal_lt_top }
  have hqReal : q.exponent.toReal = (d : ℝ) / (1 - alpha) := by
    change (ENNReal.ofReal ((d : ℝ) / (1 - alpha))).toReal = _
    rw [ENNReal.toReal_ofReal (by positivity)]
  have hq3 : ENNReal.ofReal (2 * (d : ℝ) / 3) ≤ q.exponent := by
    change ENNReal.ofReal (2 * (d : ℝ) / 3) ≤ ENNReal.ofReal ((d : ℝ) / (1 - alpha))
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have : IsFiniteMeasure (volume.restrict T) := by
    rw [hTball]; exact isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hfT : MemLp f (ENNReal.ofReal ((d : ℝ) / (1 - alpha))) (volume.restrict T) :=
    hf.mono_measure (Measure.restrict_mono hTW le_rfl)
  have hf2 : MemL2On T f := by
    refine hfT.mono_exponent ?_
    rw [show (2 : ENNReal) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal hq2.le
  have hres : MemLp (massiveResidual (fun _ => (1 : ℝ)) 0 uT f) q.exponent
      (volume.restrict T) := by
    have : massiveResidual (fun _ => (1 : ℝ)) 0 uT f = f := by
      funext x; simp [massiveResidual]
    rw [this]; exact hfT
  obtain ⟨g, -, hdiv, hgLp⟩ :=
    aux_in_deterministic_lowalpha_lift_twoD_translateSet d hd q
      (by rw [hqReal]; exact hq2) hq3 x0 (rhoMax := 1)
      (aestronglyMeasurable_const) (Eventually.of_forall fun _ => by simp) hf2 hres huT'
  have hdiv' : IsDivFormWeakSolutionOn s T uT g :=
    isDivFormWeakSolutionOn_congr_coefficient
      (ae_restrict_of_ae_restrict_of_subset hTW hcs) hdiv
  have hg : MemVectorLpOn T (schauderSourceExponent d (1 / 2)) g := by
    have : schauderSourceExponent d (1 / 2) = 2 * (d : ℝ) := by
      unfold schauderSourceExponent; ring
    rw [this]; exact hgLp
  obtain ⟨hcont, hae⟩ := continuousOn_and_ae_eq_euclideanBallAverageRepresentative_inhomogeneous
    hd hTopen (hs.mono hTW) (fun x hx => hspos x (hTW hx)) hdiv' hg
  exact ⟨T, hTopen, hxT, hTW, hcont, hae⟩

/-- **Continuity for `0 < alpha < 1`**: every native weak solution on `Q` of the actual cutoff
equation with a scalar source in `L^{d/(1-alpha)}(Q)` has a continuous representative on `Q`.
Same statement as `aux_in_deterministic_regularity_cont_half`, with `1/2 ≤ alpha` replaced by
`0 < alpha`. -/
theorem aux_in_deterministic_lowalpha_cont {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (alpha : ℝ) (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (f : SpatialCoordinates d → ℝ)
    (hf : MemLp f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
    (fL2 : DomainL2 (centeredCube Qcentre Qside hQside))
    (hfL2 : ((fL2 : SpatialCoordinates d → ℝ)) =ᵐ[volume.restrict
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] f)
    (u : weakSobolevGraph (centeredCube Qcentre Qside hQside))
    (hu : ∀ psi : killedSobolevGraph (centeredCube Qcentre Qside hQside),
      sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
        (u : SobolevData (centeredCube Qcentre Qside hQside))
        (psi : SobolevData (centeredCube Qcentre Qside hQside)) =
      sobolevVolumeLoad fL2 (psi : SobolevData (centeredCube Qcentre Qside hQside))) :
    ∃ U : SpatialCoordinates d → ℝ,
      ContinuousOn U (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) ∧
      (((u : SobolevData (centeredCube Qcentre Qside hQside)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U) := by
  obtain ⟨v, hv, hvg⟩ := exists_nativeH1Function_of_weakSobolevGraph u
  have hmass := aux_in_deterministic_regularity_massive_of_native
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside) f fL2 hfL2 u hu v hv hvg
  have : Fact (((centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ⊆
      (closedCube Qcentre Qside hQside : Set (SpatialCoordinates d))) :=
    ⟨centeredCube_subset_closedCube Qcentre hQside⟩
  have hval : ∀ᵐ x ∂volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)),
      ∀ hx : x ∈ (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)),
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside).val x =
          _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM M H omega N Qcentre hQside
            ⟨x, centeredCube_subset_closedCube Qcentre hQside hx⟩ / 1 :=
    normalizedContinuousPositiveCoefficient_coeFn (Ω := centeredCube Qcentre Qside hQside)
      (closedCube Qcentre Qside hQside) (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM M H omega N Qcentre hQside)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM_pos M H omega N Qcentre hQside) 1 one_pos
  have hcoef : (fun x => (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside).val x)
      =ᵐ[volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))]
        cutoffCoefficient M H omega N := by
    filter_upwards [hval, ae_restrict_mem (centeredCube Qcentre Qside hQside).isOpen.measurableSet]
      with x hx hxΩ
    rw [hx hxΩ, div_one]
    rfl
  have hloc := fun x0 hx0 => aux_in_deterministic_lowalpha_local_cont hd
    (centeredCube Qcentre Qside hQside).isOpen hcoef
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous M H omega N).continuousOn
    (fun x _ => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos M H omega N x) alpha halpha halpha1 hf hmass x0 hx0
  obtain ⟨hC, hA⟩ := aux_in_deterministic_regularity_glue_local
    (euclideanBallAverageRepresentative v.toFun) v.toFun hloc
  refine ⟨euclideanBallAverageRepresentative v.toFun, hC, ?_⟩
  have hvf : v.toFun = fun x => (u : SobolevData (centeredCube Qcentre Qside hQside)).1 x := hv
  rw [hvf] at hA ⊢
  exact hA.symm

end SubdiffusiveProcess.Paper
