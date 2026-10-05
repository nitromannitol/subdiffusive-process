module

public import SubdiffusiveProcess.Paper.lem_as_regularity_dirichlet_root
public import SubdiffusiveProcess.Analysis.NormalizedOscillation
public import SubdiffusiveProcess.Geometry.DirichletWindows

@[expose] public section



set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open Homogenization hiding Vec
open scoped ENNReal BigOperators Pointwise
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Native Dirichlet iteration and a supremum bound control physical ball-window oscillation. -/
theorem lem_as_regularity_dirichlet_window (d : ℕ) (hd : 2 ≤ d) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ (N k : ℕ),26 ≤ k → k ≤ N →
    ∀ (z0 w : SpatialCoordinates d),w ∈ (centeredCube z0 1 zero_lt_one : Set (SpatialCoordinates d)) →
    ∀ (aQ : PositiveCoefficient (centeredCube z0 1 zero_lt_one))
      (aT : PositiveCoefficient (centeredCube ((3:ℝ)^N • z0) ((3:ℝ)^N) (by positivity)))
      (a : SpatialCoordinates d → ℝ),
      (∀ᵐ y ∂volume.restrict (centeredCube z0 1 zero_lt_one : Set (SpatialCoordinates d)),
        aQ.val y = aT.val ((3:ℝ)^N • y)) →
      (∀ᵐ y ∂volume.restrict (openCubeSet (originCube d N)),
        a y = aT.val (y+(3:ℝ)^N • z0)) →
    ∀ B ref : ℝ,0 ≤ B → 0 < ref →
      (∀ (un hn : H1Function (openCubeSet (originCube d N))) (gn : Vec d → Vec d),
        IsDirichletSolutionOn a (originCube d N) un hn gn →
        MemHolder (cube d N) (1/2) gn → MemHolder (cube d N) (1/2) hn.grad →
        (3:ℝ)^(-((N-k+2:ℕ):ℤ))*normalizedL2On (truncatedCube d N (N-k+2:ℕ) ((3:ℝ)^N • (w-z0)))
          (fun x => un.toFun x-averageOn (truncatedCube d N (N-k+2:ℕ) ((3:ℝ)^N • (w-z0))) un.toFun) ≤
        B*((3:ℝ)^(-((N-5:ℕ):ℤ))*normalizedL2On (truncatedCube d N (N-5:ℕ) ((3:ℝ)^N • (w-z0)))
          (fun x => un.toFun x-averageOn (truncatedCube d N (N-5:ℕ) ((3:ℝ)^N • (w-z0))) un.toFun) +
          vectorSupNormOn (cube d N) hn.grad +
          ref⁻¹*(3:ℝ)^((N:ℝ)/2)*holderSeminormOn (cube d N) (1/2) gn +
          (3:ℝ)^((N:ℝ)/2)*holderSeminormOn (cube d N) (1/2) hn.grad)) →
    ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),0 ≤ Kf →
      AEMeasurable F (volume.restrict (centeredCube z0 1 zero_lt_one : Set (SpatialCoordinates d))) →
      (∀ᵐ y ∂volume.restrict (centeredCube z0 1 zero_lt_one : Set (SpatialCoordinates d)),|F y| ≤ Kf) →
    ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),ContDiff ℝ 2 phi →
      c2Norm (closedCube z0 1 zero_lt_one : Set (SpatialCoordinates d)) phi ≤ Cphi →
    ∀ b u : weakSobolevGraph (centeredCube z0 1 zero_lt_one),
      ((b : SobolevData (centeredCube z0 1 zero_lt_one)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z0 1 zero_lt_one : Set (SpatialCoordinates d))] phi →
      SolvesDirichlet aQ F b u →
    ∀ Ks : ℝ,0 ≤ Ks →
      (∀ᵐ y ∂volume.restrict (centeredCube z0 1 zero_lt_one : Set (SpatialCoordinates d)),
        |((u : SobolevData (centeredCube z0 1 zero_lt_one)).1 : SpatialCoordinates d → ℝ) y| ≤ Ks) →
      let W := Metric.ball w ((9/2:ℝ)*(3:ℝ)^(-(k:ℤ))) ∩
        (centeredCube z0 1 zero_lt_one : Set (SpatialCoordinates d))
      normalizedL2On W (fun y => (u : SobolevData (centeredCube z0 1 zero_lt_one)).1 y-
        averageOn W ((u : SobolevData (centeredCube z0 1 zero_lt_one)).1 : SpatialCoordinates d → ℝ)) ≤
        9*B*(3:ℝ)^(-(k:ℤ))*(243*Ks+(d:ℝ)*Cphi+ref⁻¹*Cp*Kf) := by
  obtain ⟨Cp,hCp,hroot⟩ := lem_as_regularity_dirichlet_root d hd
  refine ⟨Cp,hCp,?_⟩
  intro N k hk hkN z0 w hw aQ aT a hcoef ha B ref hB href hiter F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol Ks hKs hsup W
  have hR : (0:ℝ) < 3^N := by positivity
  obtain ⟨un,hn,gn,hdir,hun,hgn,hhn,hgS,hhN⟩ :=
    hroot N z0 zero_lt_one hR aQ aT a hcoef ha F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol
  let zn := (3:ℝ)^N • (w-z0)
  have hzn : zn ∈ cube d N := cutoff_nativeCentre_mem_cube N w z0 hw
  let uf : SpatialCoordinates d → ℝ := (u : SobolevData (centeredCube z0 1 zero_lt_one)).1
  have hmp := (measurePreserving_add_right volume z0).quasiMeasurePreserving.comp
    (Measure.quasiMeasurePreserving_smul volume (inv_ne_zero hR.ne'))
  have hmaps : MapsTo (fun y : SpatialCoordinates d => ((3:ℝ)^N)⁻¹ • y+z0)
      (cube d N) (centeredCube z0 1 zero_lt_one : Set (SpatialCoordinates d)) :=
    fun y hy => cutoff_affine_mem_cube N z0 y hy
  have hbound : ∀ᵐ y ∂volume.restrict (cube d N),|un.toFun y| ≤ Ks := by
    have hp := (hmp.restrict hmaps).ae hsup
    filter_upwards [hun,hp] with y hy hp
    rw [hy]
    exact hp
  let Wt := truncatedCube d N (N-5:ℕ) zn
  have hWt : Wt ⊆ cube d N := truncatedCube_subset_cube _ _ _ _
  have hmem : MemLp un.toFun 2 (volume.restrict Wt) := un.memL2.mono_measure (Measure.restrict_mono hWt le_rfl)
  have htop := normalizedOscillation_le_of_ae_bound (measurableSet_truncatedCube d N (N-5:ℕ) zn)
    (volume_toReal_truncatedCube_pos zn hzn (by omega)) (volume_truncatedCube_lt_top d N (N-5:ℕ) zn).ne
    un.toFun hmem Ks hKs (ae_restrict_of_ae_restrict_of_subset hWt hbound)
  have hraw := hiter un hn gn hdir hgn hhn
  have htopscale : (3:ℝ)^(-((N-5:ℕ):ℤ)) = 243*((3:ℝ)^N)⁻¹ := by
    rw [show -((N-5:ℕ):ℤ) = (5:ℤ)-(N:ℤ) by omega,zpow_sub₀ (by norm_num),zpow_natCast]
    norm_num [div_eq_mul_inv]
  have hbracket : (3:ℝ)^(-((N-5:ℕ):ℤ))*normalizedL2On Wt
      (fun x => un.toFun x-averageOn Wt un.toFun)+vectorSupNormOn (cube d N) hn.grad+
      ref⁻¹*(3:ℝ)^((N:ℝ)/2)*holderSeminormOn (cube d N) (1/2) gn+
      (3:ℝ)^((N:ℝ)/2)*holderSeminormOn (cube d N) (1/2) hn.grad ≤
        ((3:ℝ)^N)⁻¹*(243*Ks+(d:ℝ)*Cphi+ref⁻¹*Cp*Kf) := by
    have ht := mul_le_mul_of_nonneg_left htop (show 0 ≤ (3:ℝ)^(-((N-5:ℕ):ℤ)) by positivity)
    have hg := mul_le_mul_of_nonneg_left hgS (inv_pos.mpr href).le
    rw [htopscale] at ht ⊢
    nlinarith only [ht,hg,hhN]
  have hest := hraw.trans (mul_le_mul_of_nonneg_left hbracket hB)
  have hsmallscale : ((3:ℝ)^N)⁻¹*(3:ℝ)^((N-k+2:ℕ):ℤ) = 9*(3:ℝ)^(-(k:ℤ)) := by
    rw [show ((3:ℝ)^N)⁻¹=(3:ℝ)^(-(N:ℤ)) by rw [zpow_neg,zpow_natCast],
      ← zpow_add₀ (by norm_num),show -(N:ℤ)+((N-k+2:ℕ):ℤ) = (2:ℤ)+(-(k:ℤ)) by omega,
      zpow_add₀ (by norm_num)]
    norm_num
  have himage : translateSet z0 (((3:ℝ)^N)⁻¹ • truncatedCube d N (N-k+2:ℕ) zn) = W := by
    rw [cutoff_truncatedCube_affine,hsmallscale]
    dsimp only [W]
    congr 2
    ring
  have htransport := normalizedOscillation_affine ((3:ℝ)^N)⁻¹ (inv_pos.mpr hR) z0
    (truncatedCube d N (N-k+2:ℕ) zn) uf
  rw [himage] at htransport
  have hae := ae_restrict_of_ae_restrict_of_subset (truncatedCube_subset_cube d N (N-k+2:ℕ) zn) hun
  have hosc := Section6BoundedMultiplier.normalizedL2On_sub_average_eq_of_ae_eq hae
  have hh := mul_le_mul_of_nonneg_left hest (show 0 ≤ (3:ℝ)^((N-k+2:ℕ):ℤ) by positivity)
  have hcancel : (3:ℝ)^((N-k+2:ℕ):ℤ)*(3:ℝ)^(-((N-k+2:ℕ):ℤ)) = 1 := by
    rw [← zpow_add₀ (by norm_num),add_neg_cancel,zpow_zero]
  rw [← mul_assoc,hcancel,one_mul,hosc,← htransport] at hh
  have hid : (3:ℝ)^((N-k+2:ℕ):ℤ)*(B*(((3:ℝ)^N)⁻¹*(243*Ks+(d:ℝ)*Cphi+ref⁻¹*Cp*Kf))) =
      9*B*(3:ℝ)^(-(k:ℤ))*(243*Ks+(d:ℝ)*Cphi+ref⁻¹*Cp*Kf) := by
    calc _ = B*(((3:ℝ)^N)⁻¹*(3:ℝ)^((N-k+2:ℕ):ℤ))*(243*Ks+(d:ℝ)*Cphi+ref⁻¹*Cp*Kf) := by ring
         _ = _ := by rw [hsmallscale]; ring
  rw [hid] at hh
  exact hh

end SubdiffusiveProcess.Paper
