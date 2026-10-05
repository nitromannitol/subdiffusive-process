module

public import SubdiffusiveProcess.Paper.lfgc_single_theorem

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc




open MeasureTheory Filter Topology SubdiffusiveProcess Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem lfgc_root_bridge
    [_portSection0 : MeasurableSpace C(SpatialCoordinates d, ℝ)] [_portSection1 : BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (sigma : ℝ)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) (omega : BilateralField d) (N : ℕ)
    (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (m' : ℤ) (hr' : r = (3 : ℝ) ^ (-m'))
    (ref : ℝ) (href : ref = _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_reference M H N m' w omega) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / (4 * d))
    (hn : aux_lfgc_near_tests_NearChart sigma (aux_lfgc_root_stat_rootChart I M H omega N m' w)
      (_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_reference M H N m' w omega) θ) :
    2 / 3 ≤ I.lam w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r sigma 2 / ref ∧
    I.Lam w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r sigma 2 / ref ≤ 3 / 2 ∧
    (∀ x : Fin d → ℝ, (2 * (d : ℝ))⁻¹ *
        Matrix.trace (fun i j => Homogenization.Book.Ch02.sigmaCoarse
          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
          ((I.chart w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r).coeffOn
            (Homogenization.originCube d 0)) i j / ref : Matrix (Fin d) (Fin d) ℝ) * (x ⬝ᵥ x) ≤
      x ⬝ᵥ Matrix.mulVec (fun i j => Homogenization.Book.Ch02.sigmaCoarse
          (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d 0))
          ((I.chart w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r).coeffOn
            (Homogenization.originCube d 0)) i j / ref : Matrix (Fin d) (Fin d) ℝ) x) ∧
    I.err w r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w r ref sigma 2 ≤ θ := by
  subst hr'
  subst href
  have hrefpos := _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_reference_pos M H N m' w omega
  have hlampos : 0 < _root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lamF sigma (aux_lfgc_root_stat_rootChart I M H omega N m' w) := by
    have := I.lam_pos w ((3 : ℝ) ^ (-m')) hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N w hr) w
      ((3 : ℝ) ^ (-m')) sigma 2
    rwa [_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lam_eq I w _ hr _ sigma hsigma] at this
  obtain ⟨t1, t2, t3, t4⟩ := _root_.SubdiffusiveProcess.Paper.aux_lfgc_near_tests_NearChart.tests hd hrefpos hlampos hθ0 hθ hn
  refine ⟨?_, ?_, t3, ?_⟩
  · rw [_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_lam_eq I w _ hr _ sigma hsigma]; exact t1
  · rw [_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_Lam_eq I w _ hr _ sigma hsigma]; exact t2
  · rw [_root_.SubdiffusiveProcess.Paper.aux_lem_band_U2_err_eq I w _ hr _ _ hrefpos sigma hsigma]; exact t4

end SubdiffusiveProcess.Paper
