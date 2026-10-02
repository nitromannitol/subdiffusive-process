import SubdiffusiveProcess.Paper.lnorm_test_rembank_rd_moments
import SubdiffusiveProcess.Paper.lnorm_test_prop16_rd_band
import SubdiffusiveProcess.Paper.prop_response_compact
import SubdiffusiveProcess.Lnorm.RegroupedBoundaryCompactness
import SubdiffusiveProcess.Lnorm.BoundaryMomentAlgebra
import SubdiffusiveProcess.Lnorm.LpClusters

/-! Smooth nonconstant boundary responses are relatively compact in `L²` at small disorder.
The threshold is fixed before the cube, datum, and model; uniqueness is not asserted here. -/

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Metric
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.Lnorm
open scoped ENNReal NNReal BigOperators ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

local instance instLnormSmoothLpTwo : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2) :=
  ⟨by norm_num⟩

/-- Uniform moments and the finite-band error bound imply compactness of actual boundary responses. -/
theorem aux_lnorm_smooth_dirichlet_response_compact_of_bounds
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
      ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (b : weakSobolevGraph (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (Cmom6 Cband aD : ℝ) (hCmom6 : 0 ≤ Cmom6) (hCband : 0 < Cband) (haD : 0 < aD)
    (hRDmoment6 : ∀ N, MemLp (proxy_RD z r hr hP b M H N)
      (ENNReal.ofReal 6) (chaosSampleLaw M).toMeasure)
    (hRDbound6 : ∀ N, eLpNorm (proxy_RD z r hr hP b M H N)
      (ENNReal.ofReal 6) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cmom6)
    (hbandN : ∀ h N : ℕ,
      eLpNorm (fun omega => proxy_RD z r hr hP b M H N omega -
        ((chaosSampleLaw M).toMeasure[proxy_RD z r hr hP b M H N |
          bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) omega)
        (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Cband * M.delta * (3 : ℝ) ^ (-aD * (h : ℝ)))) :
    ∃ hmem : ∀ N, MemLp (proxy_RD z r hr hP b M H N)
        (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure,
      IsCompact (closure (range (fun N =>
        (hmem N).toLp (proxy_RD z r hr hP b M H N)))) := by
  haveI instLpTwo : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 2) := ⟨by norm_num⟩
  have hpq : (ENNReal.ofReal (2 : ℝ)) < ENNReal.ofReal (6 : ℝ) :=
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 6)).mpr (by norm_num)
  have hRfmomAll : ∀ N, MemLp (SubdiffusiveProcess.Lnorm.proxy_Rf z r hr hP b M N)
      (ENNReal.ofReal 6) (Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_laws M)) ∧
      eLpNorm (SubdiffusiveProcess.Lnorm.proxy_Rf z r hr hP b M N) (ENNReal.ofReal 6)
        (Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_laws M)) ≤
      ENNReal.ofReal Cmom6 := fun N =>
    SubdiffusiveProcess.Lnorm.proxy_hmom z r hr hP b M H hH (ENNReal.ofReal 6) N Cmom6
      hCmom6 (hRDmoment6 N) (hRDbound6 N)
  obtain ⟨hcompactRf, -, -, -, -⟩ :=
    Paper.prop_response_compact d (SubdiffusiveProcess.Lnorm.regroup_Y d)
      (SubdiffusiveProcess.Lnorm.regroup_laws M) Unit Empty
      (fun _ N => SubdiffusiveProcess.Lnorm.proxy_Rf z r hr hP b M N)
      (fun e _ _ => e.elim)
      (ENNReal.ofReal 2) (ENNReal.ofReal 6) hpq ENNReal.ofReal_ne_top
      aD M.delta haD M.shellPrefix.delta_pos
      (fun _ => Cband) (fun _ => hCband.le)
      (fun _ => ENNReal.ofReal Cmom6) (fun _ => ENNReal.ofReal_ne_top)
      (fun _ N => by dsimp only; exact (hRfmomAll N).1)
      (fun _ N => by dsimp only; exact (hRfmomAll N).2)
      (fun _ Hband N _ => by
        dsimp only
        simpa only [neg_mul] using SubdiffusiveProcess.Lnorm.proxy_hband z r hr hP b M H hH
          Cband aD Cmom6 hRDmoment6 hbandN Hband N)
      (fun _ Hband => by
        dsimp only
        exact SubdiffusiveProcess.Lnorm.proxy_hsplit z r hr hP b M Hband)
      (fun e => e.elim) (fun e => e.elim)
      (fun e _ _ => e.elim)
  have hRDmem2 : ∀ N, MemLp (SubdiffusiveProcess.Lnorm.proxy_RD z r hr hP b M H N)
      (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure :=
    fun N => (hRDmoment6 N).mono_exponent hpq.le
  have hRfmem2 : ∀ N, MemLp (SubdiffusiveProcess.Lnorm.proxy_Rf z r hr hP b M N)
      (ENNReal.ofReal 2) (Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_laws M)) :=
    fun N => ((hRfmomAll N).1).mono_exponent hpq.le
  have hcompact2 : IsCompact (closure (Set.range (fun N =>
      (hRfmem2 N).toLp (SubdiffusiveProcess.Lnorm.proxy_Rf z r hr hP b M N)))) := by
    have hEq : (fun N => (hRfmem2 N).toLp (SubdiffusiveProcess.Lnorm.proxy_Rf z r hr hP b M N)) =
        (fun N => (((hRfmomAll N).1).mono_exponent hpq.le).toLp
          (SubdiffusiveProcess.Lnorm.proxy_Rf z r hr hP b M N)) := rfl
    rw [hEq]
    exact hcompactRf ()
  have hcompactRD := SubdiffusiveProcess.Lnorm.proxy_compact_transport z r hr hP b M H hH
    (p := ENNReal.ofReal 2) hRDmem2 hRfmem2 hcompact2
  exact ⟨hRDmem2, hcompactRD⟩


/-- The band exponent used for smooth response compactness is positive in dimension at least two. -/
theorem aux_lnorm_smooth_dirichlet_response_compact_exponent (d : ℕ) (hd : 2 ≤ d) :
    0 < prop16_aD d := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hA : (0 : ℝ) < (d : ℝ) - 1 / 2 := by linarith only [hd']
  have hB : (d : ℝ) - 1 / 2 - (d : ℝ) + 1 = 1 / 2 := by ring
  have hC : (0 : ℝ) < (d : ℝ) - 1 / 2 + 1 := by linarith only [hd']
  unfold prop16_aD
  rw [hB]
  exact div_pos (div_pos (mul_pos hA (by norm_num)) hC)
    (mul_pos (by norm_num) (Real.log_pos (by norm_num)))

/-- A single disorder threshold gives `L²` compactness for every smooth nonconstant cube trace. -/
theorem lnorm_smooth_dirichlet_response_compact
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (W : SmallPerturbationInput d) (Sf : SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d ⟨by omega⟩) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ min 1 δ →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
          ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
            K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
        (g : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ g →
        (∃ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∃ y ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), g x ≠ g y) →
      ∀ b : weakSobolevGraph (centeredCube z r hr),
        ((b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] g) →
      ∃ hmem : ∀ N, MemLp (fun omega => dirichletResponse (killedResponseSpace hP)
          (cutoffPositiveCoefficient M H omega N z hr) b)
          (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure,
        IsCompact (closure (range (fun N => (hmem N).toLp (fun omega =>
          dirichletResponse (killedResponseSpace hP)
            (cutoffPositiveCoefficient M H omega N z hr) b)))) := by
  obtain ⟨q, δmom, hq, hδmom, hmom⟩ :=
    lnorm_test_rembank_rd_moments d hd Jc Pc Xc W Sf D
  obtain ⟨δband, hδband, hband⟩ := lnorm_test_prop16_rd_band d hd Jc Pc Xc W Sf D
  refine ⟨min δmom δband, lt_min hδmom hδband, ?_⟩
  intro M Rm Sreg It H hH hM z r hr hrle hP g hg hn b hb
  have hMmom := hM.trans (min_le_min_left 1 (min_le_left δmom δband))
  have hMband := hM.trans (min_le_min_left 1 (min_le_right δmom δband))
  obtain ⟨Cm, hCm, hm⟩ := hmom z r hr hrle hP g hg b hb M Rm Sreg It H hH hMmom
  obtain ⟨Cb, hCb, hbnd⟩ := hband z r hr hrle hP g hg hn b hb M Rm Sreg It H hH hMband
  exact aux_lnorm_smooth_dirichlet_response_compact_of_bounds z r hr hP b M H hH
    Cm Cb (prop16_aD d) hCm hCb (aux_lnorm_smooth_dirichlet_response_compact_exponent d hd)
    (fun N => (hm N).1) (fun N => (hm N).2.2.1) hbnd

end Paper
