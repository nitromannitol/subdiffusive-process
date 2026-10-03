module

public import SubdiffusiveProcess.Geometry.CubeEuclideanDiameter
public import SubdiffusiveProcess.Sobolev.NativeH10
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6MeasurableMaxPrinciple
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.Corrector
public import Homogenization.HighContrast.Coupled.Stampacchia.LevelEnergy
@[expose] public section

open MeasureTheory Set TopologicalSpace
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ContDiff
noncomputable section

namespace SubdiffusiveProcess

theorem harmonic_cell_error_le
    {d : ℕ} [NeZero d]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ)
    (hlam : 0 < lam) (ha : Continuous a)
    (habounds : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
      lam ≤ a x ∧ a x ≤ Lam)
    (u φ : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hu : IsWeaklyHarmonicOn a
      (centeredCube z r hr : Set (SpatialCoordinates d)) u)
    (htrace : HasZeroTraceDifferenceOn
      (centeredCube z r hr : Set (SpatialCoordinates d)) u φ)
    (hucont : ContinuousOn u.toFun
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hφsmooth : ContDiff ℝ ∞ φ.toFun)
    (L : ℝ) (hL : 0 ≤ L)
    (hφderiv : ∀ y ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
      ‖fderiv ℝ φ.toFun y‖ ≤ L) :
    ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
      |u.toFun x - φ.toFun x| ≤ 2 * Real.sqrt d * r * L := by
  let W : Set (SpatialCoordinates d) := centeredCube z r hr
  have hWopen : IsOpen W := (centeredCube z r hr).isOpen
  have hWdom : IsOpenBoundedConvexDomain W := by
    simpa [W, centeredCube] using
      (Homogenization.isOpenBoundedConvexDomain_ball z (half_pos hr))
  have hzW : z ∈ W := by
    exact Metric.mem_ball_self (half_pos hr)
  have hWclosure : closure W = Metric.closedBall z (r / 2) := by
    change closure (Metric.ball z (r / 2)) = Metric.closedBall z (r / 2)
    exact closure_ball z (ne_of_gt (half_pos hr))
  have hWconv : Convex ℝ (closure W) := by
    rw [hWclosure]
    exact convex_closedBall z (r / 2)
  have hφosc : ∀ y ∈ W, |φ.toFun y - φ.toFun z| ≤ Real.sqrt d * r * L := by
    intro y hy
    have hmvt := hWconv.norm_image_sub_le_of_norm_fderiv_le
      (fun q hq => hφsmooth.differentiable (by simp) q)
      (fun q hq => hφderiv q hq)
      (show z ∈ closure W from subset_closure hzW)
      (show y ∈ closure W from subset_closure hy)
    have hdist : ‖y - z‖ ≤ Real.sqrt d * r := by
      calc
        ‖y - z‖ ≤ Homogenization.euclideanNorm (y - z) :=
          Homogenization.norm_le_euclideanNorm _
        _ = Real.sqrt (∑ i : Fin d, (y i - z i) ^ 2) := by
          simp only [Homogenization.euclideanNorm, Homogenization.vecNormSq,
            Homogenization.vecDot, Pi.sub_apply, pow_two]
        _ ≤ Real.sqrt d * r := by
          simpa [W] using
            (euclideanDist_le_sqrt_dim_mul_side_of_mem_centeredCube z hr hy hzW)
    have hmul : L * ‖y - z‖ ≤ L * (Real.sqrt d * r) :=
      mul_le_mul_of_nonneg_left hdist hL
    rw [Real.norm_eq_abs] at hmvt
    calc
      |φ.toFun y - φ.toFun z| ≤ L * ‖y - z‖ := hmvt
      _ ≤ L * (Real.sqrt d * r) := hmul
      _ = Real.sqrt d * r * L := by ring
  let c : H1Function W := H1Function.const (φ.toFun z)
  let uc : H1Function W := u - c
  let pc : H1Function W := φ - c
  let M : ℝ := Real.sqrt d * r * L
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hpc_bound : ∀ y ∈ W, |pc.toFun y| ≤ M := by
    intro y hy
    simpa [pc, c, Homogenization.H1Function.sub_toFun, M] using hφosc y hy
  have huc_harm : IsWeaklyHarmonicOn a W uc := by
    intro ψ
    have hh := hu ψ
    simpa [uc, c, Homogenization.H1Function.sub_grad,
      Homogenization.H1Function.const] using hh
  obtain ⟨w₀, hw₀val, hw₀grad⟩ := htrace
  have hdiff : MemH10 W (fun y => uc.toFun y - pc.toFun y) := by
    refine ⟨w₀, ?_⟩
    funext y
    simp only [uc, pc, Homogenization.H1Function.sub_toFun]
    have hw : w₀.toH1Function.toFun y = u.toFun y - φ.toFun y := by
      rw [hw₀val y]
      ring
    rw [hw]
    ring
  obtain ⟨Ψ, hΨup, hΨlow, hΨeq⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.exists_h1_clamp hWdom pc hM
  have hdiff_clamp : MemH10 W (fun y => uc.toFun y - Ψ.toFun y) := by
    have htmp : MemH10 W (uc - Ψ).toFun := by
      apply Homogenization.memH10_of_ae_eq_h10 hWdom (uc - Ψ) w₀
      filter_upwards [ae_restrict_mem hWopen.measurableSet] with y hy
      have heq := hΨeq y (hpc_bound y hy)
      rw [Homogenization.H1Function.sub_toFun]
      change uc.toFun y - Ψ.toFun y = w₀.toH1Function.toFun y
      rw [heq]
      have hw := hw₀val y
      simp only [uc, pc, Homogenization.H1Function.sub_toFun] at hw ⊢
      rw [hw]
      ring
    simpa only [Homogenization.H1Function.sub_toFun] using htmp
  have hupper :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.hasBoundaryUpperBoundOn_of_datum_le
      hWdom hdiff_clamp hΨup
  have hdiff_neg : MemH10 W (fun y => (-uc).toFun y - (-Ψ).toFun y) := by
    have hn := Homogenization.memH10_neg hdiff_clamp
    rcases hn with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    funext y
    have hvy := congrFun hv y
    simp only [Homogenization.H1Function.neg_toFun] at hvy ⊢
    calc
      v.toH1Function.toFun y = -(uc.toFun y - Ψ.toFun y) := hvy
      _ = -uc.toFun y - -Ψ.toFun y := by ring
  have hΨneg : ∀ y, (-Ψ).toFun y ≤ M := by
    intro y
    rw [Homogenization.H1Function.neg_toFun]
    linarith [hΨlow y]
  have hlower :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.hasBoundaryUpperBoundOn_of_datum_le
      hWdom hdiff_neg hΨneg
  have hameas : AEStronglyMeasurable a (volumeMeasureOn W) := by
    exact ha.aestronglyMeasurable.restrict
  have hbounds : ∀ᵐ y ∂(volumeMeasureOn W), lam ≤ a y ∧ a y ≤ Lam := by
    filter_upwards [ae_restrict_mem hWopen.measurableSet] with y hy
    exact habounds y hy
  have hae_uc : ∀ᵐ y ∂(volumeMeasureOn W), |uc.toFun y| ≤ M :=
    SubdiffusiveProcess.CoarseGrainingVocab.ae_abs_le_of_isWeaklyHarmonicOn
      hWdom hlam hameas hbounds huc_harm hupper hlower
  have huc_cont : ContinuousOn uc.toFun W := by
    simpa [uc, c, Homogenization.H1Function.sub_toFun] using
      hucont.fun_sub continuousOn_const
  have hpoint_uc : ∀ y ∈ W, |uc.toFun y| ≤ M := by
    intro y hy
    let q : SpatialCoordinates d → ℝ := fun x => max (|uc.toFun x| - M) 0
    have hqae : q =ᵐ[volumeMeasureOn W] 0 := by
      filter_upwards [hae_uc] with x hx
      dsimp [q]
      rw [max_eq_right]
      linarith
    have hqcont : ContinuousOn q W := by
      dsimp [q]
      rw [continuousOn_iff_continuous_restrict]
      exact (continuousOn_iff_continuous_restrict.mp huc_cont).norm.sub
        continuous_const |>.max continuous_const
    have hqeq := Measure.eqOn_open_of_ae_eq hqae hWopen hqcont continuousOn_const
    have hzero := hqeq hy
    have hle : |uc.toFun y| - M ≤ 0 := by
      calc
        |uc.toFun y| - M ≤ q y := le_max_left _ _
        _ = 0 := hzero
    linarith
  intro x hx
  have hucx := hpoint_uc x hx
  have hpcx := hpc_bound x hx
  have htriangle : |uc.toFun x - pc.toFun x| ≤
      |uc.toFun x| + |pc.toFun x| := by
    simpa [sub_eq_add_neg, abs_neg] using
      (abs_add_le (uc.toFun x) (-pc.toFun x))
  calc
    |u.toFun x - φ.toFun x| = |uc.toFun x - pc.toFun x| := by
      simp only [uc, pc, Homogenization.H1Function.sub_toFun]
      ring_nf
    _ ≤ |uc.toFun x| + |pc.toFun x| := htriangle
    _ ≤ M + M := add_le_add hucx hpcx
    _ = 2 * Real.sqrt d * r * L := by dsimp [M]; ring

end SubdiffusiveProcess
