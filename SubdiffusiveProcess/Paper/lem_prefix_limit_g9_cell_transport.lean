import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_descendant_rechart
import SubdiffusiveProcess.Paper.lem_extension_cell_moment
import SubdiffusiveProcess.Paper.lem_prefix_limit_g9_chart_transport
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.CutoffCoefficient

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory SubdiffusiveProcess Homogenization Homogenization.Book.Ch02
open scoped ENNReal NNReal

noncomputable section
namespace Paper

theorem aux_lem_prefix_limit_g9_cell_transport_centeredCube_eq_openCubeSet {d : ℕ}
    (R : Homogenization.TriadicCube d) (hρpos : 0 < Homogenization.cubeScaleFactor R) :
    (SubdiffusiveProcess.centeredCube (Homogenization.cubeCenter R)
        (Homogenization.cubeScaleFactor R) hρpos : Set (SpatialCoordinates d)) =
      Homogenization.openCubeSet R := by
  rw [SubdiffusiveProcess.centeredCube_eq_pi]
  ext x
  simp only [Set.mem_pi, Set.mem_univ, Set.Ioo, Set.mem_setOf_eq, forall_true_left,
    Homogenization.openCubeSet, Homogenization.cubeCenter]
  constructor
  · intro h i
    obtain ⟨h1, h2⟩ := h i
    constructor <;> linarith
  · intro h i
    obtain ⟨h1, h2⟩ := h i
    constructor <;> linarith

/-- For `R` a triadic sub-cube of the origin, `R.scale ≤ 0`: a cube of side `3^{R.scale}` fitting
inside the origin cube (side `3^0 = 1`) can only have side `≤ 1` (via a volume comparison), forcing
`R.scale ≤ 0`. -/
theorem aux_lem_prefix_limit_g9_cell_transport_scale_nonpos {d : ℕ} [NeZero d]
    (R : Homogenization.TriadicCube d)
    (hR : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    R.scale ≤ 0 := by
  set ρ : ℝ := Homogenization.cubeScaleFactor R with hρdef
  have hρpos : 0 < ρ := by rw [hρdef, Homogenization.cubeScaleFactor]; exact zpow_pos (by norm_num) _
  have hsubw0 : (SubdiffusiveProcess.centeredCube (Homogenization.cubeCenter R) ρ hρpos :
      Set (SpatialCoordinates d)) ⊆
      (SubdiffusiveProcess.centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set _) := by
    rw [aux_lem_prefix_limit_g9_cell_transport_centeredCube_eq_openCubeSet R hρpos]
    have hb0 : (SubdiffusiveProcess.centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)) = Homogenization.openCubeSet (Homogenization.originCube d 0) := by
      simpa using SubdiffusiveProcess.Lane4.centeredCube_zero_eq_openCubeSet_originCube (d := d) 0
        (by norm_num)
    rw [hb0]; exact hR
  have hvol : volume (SubdiffusiveProcess.centeredCube (Homogenization.cubeCenter R) ρ hρpos :
      Set (SpatialCoordinates d)) ≤
      volume (SubdiffusiveProcess.centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)) := measure_mono hsubw0
  rw [SubdiffusiveProcess.centeredCube_volume, SubdiffusiveProcess.centeredCube_volume,
    one_pow] at hvol
  have hρ1 : ρ ^ d ≤ 1 := (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1)).1 hvol
  have hρle : ρ ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have hgt : (1 : ℝ) < ρ ^ d := one_lt_pow₀ hcon (NeZero.ne d)
    linarith
  rw [hρdef, Homogenization.cubeScaleFactor] at hρle
  by_contra hcon
  push_neg at hcon
  have hgt : (1 : ℝ) < (3 : ℝ) ^ R.scale := one_lt_zpow₀ (by norm_num) hcon
  linarith

/-- Geometric rechart, combined directly with the outer-anchor swap: for every fixed `omega`, the
identity chart's `sigmaCoarse`/`sigmaStarInvCoarse`/`coarseBMatrixNorm`/`coarseSigmaStarInvMatrixNorm`
on `R` agree with the SAME quantities of the chart re-anchored (both outer and inner) at `R`'s own
centre/side, restricted to the origin cube -- the exact shape `aux_U2_T4_chart_identity` needs on its
right. (Extends `lem_prefix_limit_g9_cell_rechart`, which lands on the `(0,1)`-outer-anchored form
instead; same underlying `aux_lem_extension_cell_moment_chart_scalar_identity` + `aux_rechart_*`
machinery, applied with the second inner call also as the outer anchor.) -/
theorem aux_lem_prefix_limit_g9_cell_transport_rechart {d : ℕ} [NeZero d]
    (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (K : ℕ)
    (R : Homogenization.TriadicCube d)
    (hR : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    ∃ (hρpos : 0 < Homogenization.cubeScaleFactor R),
      Book.Ch02.sigmaCoarse (Book.Ch02.cubeDomain R)
          ((aux_U2_unitChart I M H omega K).coeffOn R) =
        Book.Ch02.sigmaCoarse (Book.Ch02.cubeDomain (Homogenization.originCube d 0))
          ((I.chart (Homogenization.cubeCenter R) (Homogenization.cubeScaleFactor R) hρpos
              (Lane4.cutoffPositiveCoefficient M H omega K (Homogenization.cubeCenter R) hρpos)
              (Homogenization.cubeCenter R) (Homogenization.cubeScaleFactor R)).coeffOn
            (Homogenization.originCube d 0)) ∧
      Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain R)
          ((aux_U2_unitChart I M H omega K).coeffOn R) =
        Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain (Homogenization.originCube d 0))
          ((I.chart (Homogenization.cubeCenter R) (Homogenization.cubeScaleFactor R) hρpos
              (Lane4.cutoffPositiveCoefficient M H omega K (Homogenization.cubeCenter R) hρpos)
              (Homogenization.cubeCenter R) (Homogenization.cubeScaleFactor R)).coeffOn
            (Homogenization.originCube d 0)) ∧
      Book.Ch02.coarseBMatrixNorm R (aux_U2_unitChart I M H omega K) =
        Book.Ch02.coarseBMatrixNorm (Homogenization.originCube d 0)
          (I.chart (Homogenization.cubeCenter R) (Homogenization.cubeScaleFactor R) hρpos
            (Lane4.cutoffPositiveCoefficient M H omega K (Homogenization.cubeCenter R) hρpos)
            (Homogenization.cubeCenter R) (Homogenization.cubeScaleFactor R)) ∧
      Book.Ch02.coarseSigmaStarInvMatrixNorm R (aux_U2_unitChart I M H omega K) =
        Book.Ch02.coarseSigmaStarInvMatrixNorm (Homogenization.originCube d 0)
          (I.chart (Homogenization.cubeCenter R) (Homogenization.cubeScaleFactor R) hρpos
            (Lane4.cutoffPositiveCoefficient M H omega K (Homogenization.cubeCenter R) hρpos)
            (Homogenization.cubeCenter R) (Homogenization.cubeScaleFactor R)) := by
  set w0 : SpatialCoordinates d := Homogenization.cubeCenter R with hw0def
  set ρ : ℝ := Homogenization.cubeScaleFactor R with hρdef
  have hρpos : 0 < ρ := by rw [hρdef, Homogenization.cubeScaleFactor]; exact zpow_pos (by norm_num) _
  refine ⟨hρpos, ?_⟩
  set a₀ := Lane4.cutoffPositiveCoefficient M H omega K (0 : SpatialCoordinates d) one_pos
    with ha₀def
  set aw0 := Lane4.cutoffPositiveCoefficient M H omega K w0 hρpos with haw0def
  set G : Homogenization.Vec d → Homogenization.Mat d :=
    fun x => Homogenization.scalarMatrix (cutoffCoefficient M H omega K x) with hGdef
  have hsub00 : (SubdiffusiveProcess.centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)) ⊆
      (SubdiffusiveProcess.centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set _) :=
    subset_rfl
  have hA := aux_lem_extension_cell_moment_chart_scalar_identity I M H omega K
    (0 : SpatialCoordinates d) 1 one_pos (0 : SpatialCoordinates d) 1 one_pos hsub00 R hR
  have hCaseB := aux_lem_extension_cell_moment_chart_scalar_identity I M H omega K
    w0 ρ hρpos w0 ρ hρpos subset_rfl (Homogenization.originCube d 0) subset_rfl
  have hA' : (I.chart 0 1 one_pos a₀ 0 1).coeffOn R |>.toCoeffField
      =ᵐ[volumeMeasureOn (Homogenization.openCubeSet R)] G := by
    filter_upwards [hA] with x hx
    have hfeq : (fun i => (0 : SpatialCoordinates d) i + 1 * x i) = x := by funext i; simp
    rw [hx, hfeq]
  have hCaseB' : (I.chart w0 ρ hρpos aw0 w0 ρ).coeffOn (Homogenization.originCube d 0) |>.toCoeffField
      =ᵐ[volumeMeasureOn (Homogenization.openCubeSet (Homogenization.originCube d 0))]
      fun y => G (w0 + ρ • y) := by
    filter_upwards [hCaseB] with y hy
    rw [hy, hGdef]
    congr 1
  have hJ := aux_rechart_responseJ_eq _ _ G hA' hCaseB'
  refine ⟨aux_rechart_sigmaCoarse_of_responseJ hJ, aux_rechart_sigmaStarInvCoarse_of_responseJ hJ,
    ?_, ?_⟩
  · unfold Book.Ch02.coarseBMatrixNorm
    exact congrArg Book.Ch02.matrixNorm (aux_rechart_bCoarse_of_responseJ hJ)
  · unfold Book.Ch02.coarseSigmaStarInvMatrixNorm
    exact congrArg Book.Ch02.matrixNorm (aux_rechart_sigmaStarInvCoarse_of_responseJ hJ)

/-- Full geometric + scale transport: the identity chart's coarse quantities on an arbitrary
triadic sub-cube `R` of the origin equal the SAME quantities of the identity chart on the origin
cube itself, evaluated at the depth-reindexed cutoff and the measure-preserving-transported chaos
sample, times the deterministic-in-`omega`-law reference scalar to the appropriate power. Combines
`aux_lem_prefix_limit_g9_cell_transport_rechart` (geometric rechart, `R` to the re-anchored chart on
the origin) with `aux_U2_T4_chart_identity` (the `Θ`-transport, from
`lem_prefix_limit_g9_chart_transport`) and `aux_U2_sigF_scaled`/`aux_U2_sigStarInvF_scaled`/
`aux_U2_bCoarse_scaled`/`aux_U2_sigmaStarInvCoarse_scaled` (the homogeneity pull-out, same file). -/
theorem lem_prefix_limit_g9_cell_transport {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (K : ℕ) (R : Homogenization.TriadicCube d)
    (hR : Homogenization.openCubeSet R ⊆ Homogenization.openCubeSet (Homogenization.originCube d 0))
    (hmK : -R.scale ≤ (K : ℤ)) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      0 < aux_g9chart_transport_reference M H K (-R.scale) (Homogenization.cubeCenter R) omega ∧
      (∀ i j : Fin d,
        Book.Ch02.sigmaCoarse (Book.Ch02.cubeDomain R)
            ((aux_U2_unitChart I M H omega K).coeffOn R) i j =
          aux_g9chart_transport_reference M H K (-R.scale) (Homogenization.cubeCenter R) omega *
            Book.Ch02.sigmaCoarse (Book.Ch02.cubeDomain (Homogenization.originCube d 0))
              ((aux_U2_unitChart I M H
                  (aux_g9chart_transport_S (-R.scale) (Homogenization.cubeCenter R) omega)
                  (((K : ℤ) + R.scale).toNat)).coeffOn (Homogenization.originCube d 0)) i j) ∧
      (∀ i j : Fin d,
        Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain R)
            ((aux_U2_unitChart I M H omega K).coeffOn R) i j =
          (aux_g9chart_transport_reference M H K (-R.scale) (Homogenization.cubeCenter R) omega)⁻¹ *
            Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain (Homogenization.originCube d 0))
              ((aux_U2_unitChart I M H
                  (aux_g9chart_transport_S (-R.scale) (Homogenization.cubeCenter R) omega)
                  (((K : ℤ) + R.scale).toNat)).coeffOn (Homogenization.originCube d 0)) i j) ∧
      Book.Ch02.coarseBMatrixNorm R (aux_U2_unitChart I M H omega K) =
        aux_g9chart_transport_reference M H K (-R.scale) (Homogenization.cubeCenter R) omega *
          Book.Ch02.coarseBMatrixNorm (Homogenization.originCube d 0)
            (aux_U2_unitChart I M H
              (aux_g9chart_transport_S (-R.scale) (Homogenization.cubeCenter R) omega)
              (((K : ℤ) + R.scale).toNat)) ∧
      Book.Ch02.coarseSigmaStarInvMatrixNorm R (aux_U2_unitChart I M H omega K) =
        (aux_g9chart_transport_reference M H K (-R.scale) (Homogenization.cubeCenter R) omega)⁻¹ *
          Book.Ch02.coarseSigmaStarInvMatrixNorm (Homogenization.originCube d 0)
            (aux_U2_unitChart I M H
              (aux_g9chart_transport_S (-R.scale) (Homogenization.cubeCenter R) omega)
              (((K : ℤ) + R.scale).toNat)) := by
  set w0 : SpatialCoordinates d := Homogenization.cubeCenter R with hw0def
  set ρ : ℝ := Homogenization.cubeScaleFactor R with hρdef
  have hρpos : 0 < ρ := by rw [hρdef, Homogenization.cubeScaleFactor]; exact zpow_pos (by norm_num) _
  set m : ℤ := -R.scale with hmdef
  have hreq : (3 : ℝ) ^ (-m) = ρ := by rw [hmdef, neg_neg, hρdef, Homogenization.cubeScaleFactor]
  have hr : 0 < (3 : ℝ) ^ (-m) := by rw [hreq]; exact hρpos
  have hT4 := aux_U2_T4_chart_identity I M H hH K m hmK w0 hr
  filter_upwards [hT4] with omega hscaled0
  have hK'eq : (((K : ℤ) + R.scale).toNat) = (((K : ℤ) - m).toNat) := by
    congr 1
    rw [hmdef]
    ring
  rw [hK'eq]
  set G : Homogenization.Book.Ch02.TriadicCoeffFamily d :=
    aux_U2_unitChart I M H (aux_g9chart_transport_S m w0 omega) ((K : ℤ) - m).toNat with hGdef
  set F : Homogenization.Book.Ch02.TriadicCoeffFamily d :=
    I.chart w0 ((3 : ℝ) ^ (-m)) hr
      (Lane4.cutoffPositiveCoefficient M H omega K w0 hr) w0 ((3 : ℝ) ^ (-m)) with hFdef
  obtain ⟨hρpos', hSig, hSigStar, hB, hBStar⟩ :=
    aux_lem_prefix_limit_g9_cell_transport_rechart I M H omega K R hR
  rw [← hw0def] at hSig hSigStar hB hBStar
  have hreq2 : (3 : ℝ) ^ (-m) = Homogenization.cubeScaleFactor R := hreq.trans hρdef
  revert hρpos' hSig hSigStar hB hBStar
  rw [← hreq2]
  intro hρpos' hSig hSigStar hB hBStar
  have href_pos := aux_g9chart_transport_reference_pos M H K m w0 omega
  refine ⟨href_pos, ?_, ?_, ?_, ?_⟩
  · intro i j
    rw [hSig]
    have hh := aux_U2_sigF_scaled (aux_g9chart_transport_reference M H K m w0 omega) href_pos G F
      hscaled0 i j
    unfold aux_U2_sigF at hh
    exact hh
  · intro i j
    rw [hSigStar]
    have hh := aux_U2_sigStarInvF_scaled (aux_g9chart_transport_reference M H K m w0 omega) href_pos
      G F hscaled0 i j
    unfold aux_U2_sigStarInvF at hh
    exact hh
  · rw [hB]
    unfold Book.Ch02.coarseBMatrixNorm
    have hh := aux_U2_bCoarse_scaled (aux_g9chart_transport_reference M H K m w0 omega) href_pos
      (G.coeffOn (Homogenization.originCube d 0)) (F.coeffOn (Homogenization.originCube d 0))
      (hscaled0 (Homogenization.originCube d 0) subset_rfl)
    rw [hh, aux_U2_matrixNorm_smul, abs_of_pos href_pos]
  · rw [hBStar]
    unfold Book.Ch02.coarseSigmaStarInvMatrixNorm
    have hh := aux_U2_sigmaStarInvCoarse_scaled (aux_g9chart_transport_reference M H K m w0 omega)
      href_pos (G.coeffOn (Homogenization.originCube d 0)) (F.coeffOn (Homogenization.originCube d 0))
      (hscaled0 (Homogenization.originCube d 0) subset_rfl)
    rw [hh, aux_U2_matrixNorm_smul, abs_of_pos (inv_pos.mpr href_pos)]

end Paper
