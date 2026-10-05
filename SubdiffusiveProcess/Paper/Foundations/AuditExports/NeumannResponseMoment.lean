module

public import SubdiffusiveProcess.Paper.mfd_prop_16
public import SubdiffusiveProcess.Paper.lem_cell_ellipticity
public import SubdiffusiveProcess.Paper.cor_neumann_source
public import SubdiffusiveProcess.Paper.inputs_J_witness
public import SubdiffusiveProcess.Paper.inputs_responses_witness
public import SubdiffusiveProcess.EllipticRegularity.CutoffCoefficientRepresentative
public import SubdiffusiveProcess.Sobolev.DomainPoincare

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace Metric
open SubdiffusiveProcess SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.Paper SubdiffusiveProcess.ResponseMoments
open Homogenization Homogenization.Book.Ch02
open scoped ENNReal NNReal BigOperators ContDiff Topology

noncomputable section
namespace SubdiffusiveProcess.AuditExports

/-- The affine inverse Neumann response is bounded by the zeroth term of the
coarse lower ellipticity norm. The unit cube is `(0,1)^d`; its chart is translated
to the centered triadic unit cube before the matrix estimate is applied. -/
theorem affine_neumann_response_le_lower_ellipticity
    {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (M : SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) (e : Fin d → ℝ)
    (he : (∑ i : Fin d, (e i) ^ 2) = 1)
    (hP : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
      ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖) :
    inverseResponse (meanZeroResponseSpace hP)
      (cutoffPositiveCoefficient M H omega N (fun _ => (1 / 2 : ℝ)) one_pos)
      ((affineNeumannLoad e).comp
        (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))) ≤
      (E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos
        (cutoffPositiveCoefficient M H omega N (fun _ => (1 / 2 : ℝ)) one_pos)
        (fun _ => (1 / 2 : ℝ)) 1 1 1)⁻¹ := by
  let c : SpatialCoordinates d := fun _ => (1 / 2 : ℝ)
  let Q := unitNeumannCube d
  let a := cutoffPositiveCoefficient M H omega N c one_pos
  let g : SpatialCoordinates d → ℝ := cutoffCoefficient M H omega N
  let f : SpatialCoordinates d → ℝ := fun x => g (x + c)
  have hdom : IsOpenBoundedConvexDomain (Q : Set (SpatialCoordinates d)) := by
    exact isOpenBoundedConvexDomain_centeredCube c one_pos
  have hne : (Q : Set (SpatialCoordinates d)).Nonempty := by
    refine ⟨c, ?_⟩
    change c ∈ unitNeumannCube d
    change c ∈ (centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d))
    rw [centeredCube_eq_pi]
    intro i hi
    constructor <;> norm_num [c]
  let U : Domain d := ⟨(Q : Set (SpatialCoordinates d)), hdom, hne⟩
  let V : Domain d := cubeDomain (originCube d 0)
  obtain ⟨dataU⟩ := SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.exists_scalarCoeffOnData_of_continuous_pos
    (cutoffCoefficient_continuous M H omega N) (cutoffCoefficient_pos M H omega N) U
  obtain ⟨dataV⟩ := SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.exists_scalarCoeffOnData_of_continuous_pos
    ((cutoffCoefficient_continuous M H omega N).comp (continuous_id.add continuous_const))
    (fun x => cutoffCoefficient_pos M H omega N (x + c)) V
  have hset : (U : Set (SpatialCoordinates d)) = translateSet c (V : Set (SpatialCoordinates d)) := by
    simpa [U, V, Q, c, unitNeumannCube] using!
      aux_neumann_response_defect_transport_physical_set d 0
  let translated := aux_neumann_response_defect_transport_translateCoeffOn V U c hset dataV.toCoeffOn
  have hAE : translated.AEEq dataU.toCoeffOn := by
    filter_upwards [] with x
    change scalarMatrix (f (x + -c)) = scalarMatrix (g x)
    dsimp only [f]
    rw [neg_add_cancel_right]
  have hmatU : Homogenization.Book.Ch02.sigmaStarInvCoarse U dataU.toCoeffOn = Homogenization.Book.Ch02.sigmaStarInvCoarse V dataV.toCoeffOn := by
    exact ((aux_lem_as_coarse_ms_coarse_congr
      (fun p q => responseJ_eq_ofAEEq hAE p q)).2).symm.trans
      (aux_neumann_response_defect_transport_sigma_translate V U c hset dataV.toCoeffOn)
  let chart := E.chart c 1 one_pos a c 1
  have hchart : (chart.coeffOn (originCube d 0)).AEEq dataV.toCoeffOn := by
    filter_upwards [aux_lem_extension_cell_moment_chart_scalar_identity E M H omega N
      c 1 one_pos c 1 one_pos subset_rfl (originCube d 0) subset_rfl] with x hx
    change (chart.coeffOn (originCube d 0)).toCoeffField x = scalarMatrix (f x)
    rw [hx]
    congr 1
    dsimp only [f]
    congr 1
    funext i
    simp only [Pi.add_apply, one_mul, add_comm]
  have hmatV : Homogenization.Book.Ch02.sigmaStarInvCoarse V dataV.toCoeffOn =
      Homogenization.Book.Ch02.sigmaStarInvCoarse V (chart.coeffOn (originCube d 0)) :=
    ((aux_lem_as_coarse_ms_coarse_congr
      (fun p q => responseJ_eq_ofAEEq hchart p q)).2).symm
  have ha : (a.val : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (Q : Set (SpatialCoordinates d))] g :=
    (cutoffPositiveCoefficient_representative M H omega N c one_pos).2.2.2
  have hvolume : volume.real (Q : Set (SpatialCoordinates d)) = 1 := by
    change volume.real (unitNeumannCube d : Set (SpatialCoordinates d)) = 1
    rw [unitNeumannCube, centeredCube_volume_real]
    simp only [one_pow]
  have hbridge := symmetricNeumannNu_eq_affineInverseNeumannResponse hdom hne
    dataU hP a ha (hvolume.symm ▸ zero_lt_one) e
  have htheory := responseSymmetricDirichletNeumannTheory U dataU.toCoeffOn dataU.isSymmetric
  have hresponse : affineInverseNeumannResponse hP a e =
      vecDot e (matVecMul (Homogenization.Book.Ch02.sigmaStarInvCoarse U dataU.toCoeffOn) e) := by
    rw [hvolume, htheory.neumann_value_by_sigmaStarInv] at hbridge
    linarith only [hbridge]
  have hnorme : vecNormSq e = 1 := by
    simpa only [vecNormSq, vecDot, pow_two] using he
  have hquad := abs_vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq
    (Homogenization.Book.Ch02.sigmaStarInvCoarse V (chart.coeffOn (originCube d 0))) e
  rw [hnorme, mul_one, ← matrixNorm_eq_matrixOperatorNorm] at hquad
  have hcoarse := oneCube_sigmaStarInv_le_lambdaSq_finite_inv
    (originCube d 0) chart (s := (1 : ℝ)) (q := (1 : ℝ)) zero_lt_one le_rfl
  have hlam := E.lam_eq c 1 one_pos a c 1 one_pos subset_rfl 1
    (show (1 : ℝ) ∈ Ioc (0 : ℝ) 1 from ⟨zero_lt_one, le_rfl⟩) 1 le_rfl
  simp only [ENNReal.one_ne_top, ite_false, ENNReal.toReal_one] at hlam
  change affineInverseNeumannResponse hP a e ≤ _
  rw [hresponse, hmatU, hmatV, hlam]
  exact (le_abs_self _).trans (hquad.trans hcoarse)

/-- Unit-cube affine Neumann responses have every fixed finite moment below the
cell-ellipticity disorder threshold. The bound is a conclusion, uniform in `N`. -/
theorem affine_neumann_response_moment
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (e : Fin d → ℝ) (he : (∑ i : Fin d, (e i) ^ 2) = 1)
    (hP : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
      ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖)
    (q : ℝ) (hq : 1 ≤ q) :
    ∃ deltaq : ℝ, 0 < deltaq ∧
      ∀ (M : SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ deltaq →
        ∃ B : ℝ, 0 < B ∧ ∀ N : ℕ,
          MemLp (fun om => affineInverseNeumannResponse hP
            (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos) e)
            (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
          eLpNorm (fun om => affineInverseNeumannResponse hP
            (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos) e)
            (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Cd, _hCd, hcell⟩ := lem_cell_ellipticity d hd E
  obtain ⟨deltaq, hdq, hmom⟩ := hcell 1 ⟨one_pos, le_rfl⟩ 1 (Or.inl rfl) q hq
  refine ⟨deltaq, hdq, ?_⟩
  intro M Rm H hH hdelta
  obtain ⟨B, hB, hbound⟩ := hmom M Rm H hH hdelta (fun _ => (1 / 2 : ℝ)) 1 one_pos
  refine ⟨B, hB, ?_⟩
  intro N
  have hcell0 : centeredCube (fun _ : Fin d => (1 / 2 : ℝ))
      ((3 : ℝ) ^ (-((0 : ℕ) : ℤ))) (by positivity) ≤
      centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos := by
    simp only [Nat.cast_zero, neg_zero, zpow_zero, le_refl]
  have hm := hbound N 0 (Nat.zero_le N) (fun _ => (1 / 2 : ℝ)) hcell0
  simp only [Nat.cast_zero, neg_zero, zpow_zero, mul_zero, Real.exp_zero, mul_one] at hm
  let a := fun om => cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos
  let y := fun om => affineInverseNeumannResponse hP (a om) e
  let F := fun om => E.Lam (fun _ => (1 / 2 : ℝ)) 1 one_pos (a om)
      (fun _ => (1 / 2 : ℝ)) 1 1 1 +
    (E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos (a om) (fun _ => (1 / 2 : ℝ)) 1 1 1)⁻¹
  have hFm : MemLp F (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure :=
    hm.2.trans_lt ENNReal.ofReal_lt_top
  have hym : AEStronglyMeasurable y (chaosSampleLaw M).toMeasure :=
    (aux_neumann_centered_response_meas M H hH.1 (meanZeroResponseSpace hP)
      ((affineNeumannLoad e).comp
        (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))) N).aestronglyMeasurable
  have hpoint : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ‖y om‖ ≤ F om := by
    exact ae_of_all _ fun om => by
      have hy0 : 0 ≤ y om := inverseResponse_nonneg _ _ _
      rw [Real.norm_eq_abs, abs_of_nonneg hy0]
      exact (affine_neumann_response_le_lower_ellipticity E M H om N e he hP).trans
        (le_add_of_nonneg_left (E.Lam_pos _ _ _ _ _ _ _ _).le)
  exact ⟨hFm.mono' hym hpoint, (eLpNorm_mono_ae_real hym hpoint).trans hm.2⟩

/-- The mean-zero response carrier on the unit cube is constructed from its geometry. -/
theorem unit_neumann_poincare {d : ℕ} (hd : 2 ≤ d) :
    ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
      ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖ := by
  let : NeZero d := ⟨by omega⟩
  exact (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain _
    (isOpenBoundedConvexDomain_centeredCube (fun _ => (1 / 2 : ℝ)) one_pos)).2

/-- The smooth face-bump is an actual square-integrable source on the unit cube. -/
theorem face_bump_memLp {d : ℕ} (rho : ℝ → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (e : Fin d → ℝ) (eps : ℝ) :
    MemLp (faceBump rho e eps) 2
      (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) := by
  have hrhoC := hrho.continuous
  have hf : Continuous (faceBump rho e eps) := by
    unfold faceBump
    fun_prop
  let K : Compacts (SpatialCoordinates d) := closedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos
  let f : C(K, ℝ) := ⟨fun x => faceBump rho e eps x, hf.comp continuous_subtype_val⟩
  apply MemLp.of_bound hf.measurable.aestronglyMeasurable ‖f‖
  filter_upwards [ae_restrict_mem (unitNeumannCube d).isOpen.measurableSet] with x hx
  exact f.norm_coe_le_norm ⟨x, centeredCube_subset_closedCube _ one_pos hx⟩

/-- The literal `L²` representative of the paper's smooth face-bump. -/
def face_bump_L2 {d : ℕ} (rho : ℝ → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (e : Fin d → ℝ) (eps : ℝ) : DomainL2 (unitNeumannCube d) :=
  (face_bump_memLp rho hrho e eps).toLp (faceBump rho e eps)

/-- This source has exactly the intended almost-everywhere representative. -/
theorem face_bump_L2_coeFn {d : ℕ} (rho : ℝ → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (e : Fin d → ℝ) (eps : ℝ) :
    (face_bump_L2 rho hrho e eps : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] faceBump rho e eps :=
  (face_bump_memLp rho hrho e eps).coeFn_toLp

/-- Neumann conditioning on finite field windows, with the unsmoothed response
moment derived from cell ellipticity. The response space and the `in_J` witness
are constructed internally. A function of the derived numerical moment bound `Bu`
is chosen before the model and infrared field; evaluating it at `Bu` gives the
final constant before `K`, `N` and the window. -/
theorem neumann_conditioning_of_cell_moments :
  ∀ (d : ℕ) (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cresp : ℝ) (_hCresp : 0 < Cresp)
    (rho : ℝ → ℝ),
    ∀ (hrho : ContDiff ℝ ∞ rho),
    (∀ tau, 0 ≤ rho tau) →
    (∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) →
    (∫ tau, rho tau) = 1 →
    ∀ (pvec : Fin d → ℝ),
      (∑ i : Fin d, (pvec i) ^ 2) = 1 →
    let hP := unit_neumann_poincare _hd
    let Q := unitNeumannCube d
    let S := meanZeroResponseSpace hP
    let L0 : S.space →L[ℝ] ℝ :=
      (affineNeumannLoad pvec).comp (subspaceGradient (meanZeroSobolevGraph Q))
    let fL2 : ℝ → DomainL2 Q := fun eps => face_bump_L2 rho hrho pvec eps
    let Leps : ℝ → S.space →L[ℝ] ℝ := fun eps =>
      (sobolevVolumeLoad (fL2 eps)).comp S.space.subtypeL
        ∀ (t p B : ℝ),
          ((d : ℝ) - 1 < t ∧ t < (d : ℝ) ∧ 2 ≤ p ∧ 0 ≤ B) →
          ∃ (delta0 : ℝ) (C : ℝ → ℝ),
            0 < delta0 ∧ delta0 ≤ 1 ∧ (∀ Bu, 0 < C Bu) ∧
            ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d),
              (0 < M.delta ∧ M.delta ≤ delta0) →
              ∀ (Rinput : _root_.SubdiffusiveProcess.Paper.in_responses d M),
                Rinput.C ≤ Cresp →
                4 * p ≤ Cresp⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
                ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
                InfraredCharacterization M H →
                let P : Measure (BilateralField d) :=
                  (chaosSampleLaw M).toMeasure
                let aN : ℕ → BilateralField d → PositiveCoefficient Q := fun N om =>
                  cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos
                let yN : ℕ → BilateralField d → ℝ := fun N om =>
                  inverseResponse S (aN N om) L0
                let yeps : ℝ → ℕ → BilateralField d → ℝ := fun eps N om =>
                  inverseResponse S (aN N om) (Leps eps)
                let ueps : ℝ → ℕ → BilateralField d → S.space := fun eps N om =>
                  responseSolution S (aN N om) (Leps eps)
                (∃ Bu : ℝ, 0 < Bu ∧
                  ∀ N,
                    MemLp (yN N) (ENNReal.ofReal (4 * p)) P ∧
                      eLpNorm (yN N) (ENNReal.ofReal (4 * p)) P ≤ ENNReal.ofReal Bu) ∧
                ∀ Bu : ℝ, 0 < Bu →
                (∀ N,
                    MemLp (yN N) (ENNReal.ofReal (4 * p)) P ∧
                      eLpNorm (yN N) (ENNReal.ofReal (4 * p)) P ≤ ENNReal.ofReal Bu) →
                (∀ (K : ℕ → BilateralField d → ℝ),
                  (∀ N, AEStronglyMeasurable (K N) P) →
                  (∀ᵐ om ∂P, ∀ N, 0 ≤ K N om) →
                  (∀ᵐ om ∂P,
                    ∀ (N : ℕ) (eps : ℝ),
                      (0 < eps ∧ eps < 1 / 8) →
                      ∀ (x : SpatialCoordinates d) (rad : ℝ),
                        x ∈ Q → (0 < rad ∧ rad ≤ 1) →
                        localGradientEnergy (aN N om)
                            (s := Metric.ball x rad ∩ (Q : Set (SpatialCoordinates d)))
                            (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
                            (subspaceGradient S.space (ueps eps N om)) ≤
                          K N om * eps ^ (-2 : ℝ) * rad ^ t) →
                  (∀ N,
                    MemLp (K N) (ENNReal.ofReal (3 * p)) P ∧
                      eLpNorm (K N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
                  (∀ N eps, (0 < eps ∧ eps < 1 / 8) →
                    MemLp (yeps eps N) (ENNReal.ofReal (3 * p)) P ∧
                      eLpNorm (yeps eps N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
                  (∀ N eps, (0 < eps ∧ eps < 1 / 8) →
                    eLpNorm (fun om => yN N om - yeps eps N om)
                      (ENNReal.ofReal p) P ≤
                      ENNReal.ofReal (B * eps ^ (1 / 4 : ℝ))) →
                  (∀ h N : ℕ,
                    let sigma_h := bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h
                    eLpNorm
                      (fun om => yN N om - (P[yN N | sigma_h]) om)
                      (ENNReal.ofReal p) P ≤
                    ENNReal.ofReal
                      (C Bu * Real.sqrt M.delta *
                        (3 : ℝ) ^
                          (-((t * (t - (d : ℝ) + 1) / (t + 1) /
                              8 / 32) * (h : ℝ))))) ∧
                  (∀ h N : ℕ, N < h →
                    let sigma_h := bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h
                    eLpNorm
                      (fun om => yN N om - (P[yN N | sigma_h]) om)
                      (ENNReal.ofReal p) P ≤
                    ENNReal.ofReal
                      (C Bu * M.delta * (3 : ℝ) ^ (-(h : ℝ)))))
    := by
  intro d hd instM instB Cresp hCresp rho hrho1 hrho2 hrho3 hrho4 pvec hpvec hP Q S L0
    fL2 Leps t p Binput htpB
  have hfL2 : ∀ eps : ℝ, (0 < eps ∧ eps < 1 / 8) →
      (fL2 eps : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (Q : Set (SpatialCoordinates d))] faceBump rho pvec eps :=
    fun eps _ => face_bump_L2_coeFn rho hrho1 pvec eps
  obtain ⟨ht_lower, ht_upper, hp, hBinput⟩ := htpB
  let I : in_J d := Classical.choice (inputs_J_witness d hd)
  obtain ⟨deltaCent, Cc, hdeltaCent, hdeltaCent1, hCc, hcent⟩ :=
    neumann_centered_response d hd I Cresp hCresp p hp pvec hpvec hP
  obtain ⟨deltaCell, hdeltaCell, hmom⟩ := affine_neumann_response_moment d hd I
    pvec hpvec hP (4 * p) (by linarith)
  have hBall : ∀ Bu : ℝ, 0 ≤ Binput + max Bu 0 := by
    intro Bu
    exact add_nonneg hBinput (le_max_right _ _)
  have hInfluence := fun Bu : ℝ => aux_mfd_prop_16_neumann_influence d hd rho hrho1 hrho2
    hrho3 hrho4 pvec hpvec hP fL2 hfL2 t p (Binput + max Bu 0)
      ⟨ht_lower, ht_upper, hp, hBall Bu⟩
  choose CnAll hCnAll hn15All using hInfluence
  have hCoarse := fun Bu : ℝ => prop_16_coarse_block_neumann d hd Cresp hCresp pvec hpvec hP
    p (Binput + max Bu 0) hp (hBall Bu)
  choose CcnAll hCcnAll hcbnAll using hCoarse
  obtain ⟨ha0, ha1⟩ := SubdiffusiveProcess.Section9LiveRate.influence_exponent_pos_le_one d hd t ht_lower ht_upper
  set a := t * (t - (d : ℝ) + 1) / (t + 1) / 8 with ha_def
  have hr1 : (3 : ℝ) ^ (-a) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h1r : 0 < 1 - (3 : ℝ) ^ (-a) := by linarith
  let C : ℝ → ℝ := fun Bu =>
    Real.sqrt (4 * (CcnAll Bu + 2 * (Binput + max Bu 0) +
      CnAll Bu / (1 - (3 : ℝ) ^ (-a))) * Cc) + 8 * Cc + CcnAll Bu + 1
  have hC : ∀ Bu, 0 < C Bu := by
    intro Bu
    have := hCcnAll Bu
    dsimp only [C]
    positivity
  refine ⟨min deltaCent deltaCell, C, lt_min hdeltaCent hdeltaCell,
    (min_le_left _ _).trans hdeltaCent1, hC, ?_⟩
  intro M hM Rinput hRC hscale H hH P aN yN yeps ueps
  have hδ0 : 0 < M.delta := hM.1
  have hδcent : M.delta ≤ deltaCent := hM.2.trans (min_le_left _ _)
  have hδcell : M.delta ≤ deltaCell := hM.2.trans (min_le_right _ _)
  have hδ1 : M.delta ≤ 1 := hδcent.trans hdeltaCent1
  obtain ⟨Bu0, hBu0, hyBu0⟩ := hmom M Rinput H hH hδcell
  refine ⟨⟨Bu0, hBu0, hyBu0⟩, ?_⟩
  intro Bu hBu hyBu
  let B := Binput + Bu
  have hB : 0 ≤ B := by dsimp [B]; linarith
  have hBinputB : Binput ≤ B := by dsimp [B]; linarith
  have hBuB : Bu ≤ B := by dsimp [B]; linarith
  let Cn := CnAll Bu
  have hCn : 0 < Cn := hCnAll Bu
  have hn15 := hn15All Bu
  rw [max_eq_left hBu.le] at hn15
  let Ccn := CcnAll Bu
  have hCcn : 0 < Ccn := hCcnAll Bu
  have hcbn := hcbnAll Bu
  rw [max_eq_left hBu.le] at hcbn
  dsimp only [C]
  rw [max_eq_left hBu.le]
  intro K hKm hK0 hgrowth hKinput hyepsInput hsmoothInput
  have hKmom : ∀ N, MemLp (K N) (ENNReal.ofReal (3 * p)) P ∧
      eLpNorm (K N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B :=
    fun N => ⟨(hKinput N).1, (hKinput N).2.trans (ENNReal.ofReal_mono hBinputB)⟩
  have hyeps : ∀ N eps, (0 < eps ∧ eps < 1 / 8) →
      MemLp (yeps eps N) (ENNReal.ofReal (3 * p)) P ∧
      eLpNorm (yeps eps N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B :=
    fun N eps heps => ⟨(hyepsInput N eps heps).1,
      (hyepsInput N eps heps).2.trans (ENNReal.ofReal_mono hBinputB)⟩
  have hyN : ∀ N, MemLp (yN N) (ENNReal.ofReal (4 * p)) P ∧
      eLpNorm (yN N) (ENNReal.ofReal (4 * p)) P ≤ ENNReal.ofReal B :=
    fun N => ⟨(hyBu N).1, (hyBu N).2.trans (ENNReal.ofReal_mono hBuB)⟩
  have hsmooth : ∀ N eps, (0 < eps ∧ eps < 1 / 8) →
      eLpNorm (fun om => yN N om - yeps eps N om) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (B * eps ^ (1 / 4 : ℝ)) := by
    intro N eps heps
    exact (hsmoothInput N eps heps).trans (ENNReal.ofReal_mono
      (mul_le_mul_of_nonneg_right hBinputB (Real.rpow_nonneg heps.1.le _)))
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ p)
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) := fun j =>
    (scaledLayerLaw d (chaosRootFieldLaw M) j : Measure C(SpatialCoordinates d, ℝ))
  have hc := hcent M ⟨hδ0, hδcent⟩ Rinput hRC hscale H hH (fun N => aux_prop_16_relab N)
    (fun N => aux_prop_16_relab_mp M N)
    (ae_of_all _ fun om N i x => aux_prop_16_relab_apply N om i x)
  let G : Set (BilateralField d) :=
    {om | Tendsto (infraredPartialSum om) atTop (𝓝 (H om))}
  have hG : ∀ᵐ om ∂(Measure.infinitePi laws), om ∈ G := hH.2
  have hdetA : ∀ N : ℕ, ∀ ω₁ ∈ G, ∀ ω₂ ∈ G, (∀ j : ℤ, -(N : ℤ) ≤ j → ω₁ j = ω₂ j) →
      aN N ω₁ = aN N ω₂ := by
    intro N ω₁ h1 ω₂ h2 hagree
    have hH12 := aux_prop_16_infrared_eq H ω₁ ω₂ h1 h2 (fun j hj => hagree j (by omega))
    exact aux_prop_16_cpc_eq M H ω₁ ω₂ N _ one_pos
      (aux_prop_16_cutoff_eq H ω₁ ω₂ N hH12 hagree)
  have hdetN : ∀ N : ℕ, ∀ ω₁ ∈ G, ∀ ω₂ ∈ G, (∀ j : ℤ, -(N : ℤ) ≤ j → ω₁ j = ω₂ j) →
      yN N ω₁ = yN N ω₂ := by
    intro N ω₁ h1 ω₂ h2 hagree
    show inverseResponse S (aN N ω₁) L0 = inverseResponse S (aN N ω₂) L0
    rw [hdetA N ω₁ h1 ω₂ h2 hagree]
  have hyNm : ∀ N, AEStronglyMeasurable (yN N) (Measure.infinitePi laws) := fun N =>
    (hyN N).1.aestronglyMeasurable
  have hyNint : ∀ N, Integrable (yN N) (Measure.infinitePi laws) := fun N =>
    (hyN N).1.integrable (by
      simpa using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ 4 * p))
  have hFCmp : ∀ h : ℕ, MeasurePreserving
      (fun q : BilateralField d × BilateralField d => fun j =>
        if j < -(h : ℤ) then q.2 j else q.1 j)
      ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) (Measure.infinitePi laws) :=
    fun h => measurePreserving_copy_infinitePi_block laws {j : ℤ | j < -(h : ℤ)}
  have hCCmp : ∀ h : ℕ, MeasurePreserving
      (fun q : BilateralField d × BilateralField d => fun j =>
        if (h : ℤ) < j then q.2 j else q.1 j)
      ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) (Measure.infinitePi laws) :=
    fun h => measurePreserving_copy_infinitePi_block laws {j : ℤ | (h : ℤ) < j}
  have hcoarse : ∀ h N : ℕ,
      eLpNorm (fun q : BilateralField d × BilateralField d =>
          yN N q.1 - yN N (fun j => if (h : ℤ) < j then q.2 j else q.1 j))
        (ENNReal.ofReal p) ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) ≤
      ENNReal.ofReal (Ccn * M.delta * (3 : ℝ) ^ (-(h : ℝ))) := by
    intro h N
    have hmeas : AEStronglyMeasurable (fun q : BilateralField d × BilateralField d =>
        yN N q.1 - yN N (fun j => if (h : ℤ) < j then q.2 j else q.1 j))
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) :=
      ((hyNm N).comp_measurePreserving measurePreserving_fst).sub
        ((hyNm N).comp_measurePreserving (hCCmp h))
    exact (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (by linarith))).trans (hcbn M ⟨hδ0, hδ1⟩ Rinput hRC hscale H hH hyN h N)
  have hfine0 : ∀ h N : ℕ, N ≤ h →
      eLpNorm (fun q : BilateralField d × BilateralField d =>
          yN N q.1 - yN N (fun j => if j < -(h : ℤ) then q.2 j else q.1 j))
        (ENNReal.ofReal p) ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) ≤ 0 := by
    intro h N hNh
    have htel := aux_prop_16_fine_telescope laws hp1 (yN N) (hyNm N) G hG h N (hdetN N)
      (fun _ => 0) (fun k hk hkN => absurd (lt_of_lt_of_le hk hkN) (by omega))
    simpa using htel
  have hfine : ∀ h N : ℕ, ∀ ε : ℝ, 0 < ε ∧ ε < 1 / 8 →
      eLpNorm (fun q : BilateralField d × BilateralField d =>
          yN N q.1 - yN N (fun j => if j < -(h : ℤ) then q.2 j else q.1 j))
        (ENNReal.ofReal p) ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) ≤
      ENNReal.ofReal (2 * B * ε ^ (1 / 4 : ℝ) + Cn * M.delta * ε ^ (-2 : ℝ) *
        (3 : ℝ) ^ (-a * (h : ℝ)) / (1 - (3 : ℝ) ^ (-a))) := by
    intro h N ε hε
    have hyem : AEStronglyMeasurable (yeps ε N) (Measure.infinitePi laws) :=
      (hyeps N ε hε).1.aestronglyMeasurable
    have hdiff : eLpNorm (fun om => yN N om - yeps ε N om) (ENNReal.ofReal p)
        (Measure.infinitePi laws) ≤ ENNReal.ofReal (B * ε ^ (1 / 4 : ℝ)) := hsmooth N ε hε
    have hdetE : ∀ ω₁ ∈ G, ∀ ω₂ ∈ G, (∀ j : ℤ, -(N : ℤ) ≤ j → ω₁ j = ω₂ j) →
        yeps ε N ω₁ = yeps ε N ω₂ := by
      intro ω₁ h1 ω₂ h2 hagree
      show inverseResponse S (aN N ω₁) (Leps ε) = inverseResponse S (aN N ω₂) (Leps ε)
      rw [hdetA N ω₁ h1 ω₂ h2 hagree]
    have htel := aux_prop_16_fine_telescope laws hp1 (yeps ε N) hyem G hG h N hdetE
      (fun k => ENNReal.ofReal (Cn * M.delta * ε ^ (-2 : ℝ) * (3 : ℝ) ^ (-(a * (k : ℝ)))))
      (fun k _ hkN => hn15 M ⟨hδ0, hδ1⟩ H hH K hKm hK0 hgrowth hKmom hyeps hyN hsmooth
        ε hε N k hkN)
    have hgeo := aux_prop_16_geom_neg a ha0 (Cn * M.delta * ε ^ (-2 : ℝ))
      (by have : 0 ≤ ε ^ (-2 : ℝ) := Real.rpow_nonneg hε.1.le _; positivity) h N
    let FC : BilateralField d × BilateralField d → BilateralField d := fun q j =>
      if j < -(h : ℤ) then q.2 j else q.1 j
    have m1 : AEStronglyMeasurable (fun q : BilateralField d × BilateralField d =>
        yN N q.1 - yeps ε N q.1)
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) :=
      ((hyNm N).sub hyem).comp_measurePreserving measurePreserving_fst
    have m2 : AEStronglyMeasurable (fun q : BilateralField d × BilateralField d =>
        yeps ε N q.1 - yeps ε N (FC q))
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) :=
      (hyem.comp_measurePreserving measurePreserving_fst).sub
        (hyem.comp_measurePreserving (hFCmp h))
    have m3 : AEStronglyMeasurable (fun q : BilateralField d × BilateralField d =>
        yN N (FC q) - yeps ε N (FC q))
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) :=
      ((hyNm N).sub hyem).comp_measurePreserving (hFCmp h)
    have hsplit : (fun q : BilateralField d × BilateralField d => yN N q.1 - yN N (FC q)) =
        ((fun q => yN N q.1 - yeps ε N q.1) + (fun q => yeps ε N q.1 - yeps ε N (FC q))) -
          (fun q => yN N (FC q) - yeps ε N (FC q)) := by
      funext q
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    change eLpNorm (fun q : BilateralField d × BilateralField d => yN N q.1 - yN N (FC q))
      (ENNReal.ofReal p) ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) ≤ _
    rw [hsplit]
    refine (eLpNorm_sub_le hp1).trans ?_
    refine (add_le_add (eLpNorm_add_le hp1) le_rfl).trans ?_
    let gd : BilateralField d → ℝ := fun om => yN N om - yeps ε N om
    have hgd : AEStronglyMeasurable gd (Measure.infinitePi laws) := (hyNm N).sub hyem
    have e1 := aux_prop_16_eLpNorm_mp (ENNReal.ofReal p) Prod.fst
      (measurePreserving_fst : MeasurePreserving Prod.fst
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) (Measure.infinitePi laws))
      gd hgd
    have e3 := aux_prop_16_eLpNorm_mp (ENNReal.ofReal p) FC (hFCmp h) gd hgd
    change eLpNorm (fun q : BilateralField d × BilateralField d => gd q.1)
        (ENNReal.ofReal p) ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) +
      eLpNorm (fun q : BilateralField d × BilateralField d =>
        yeps ε N q.1 - yeps ε N (FC q)) (ENNReal.ofReal p)
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) +
      eLpNorm (fun q : BilateralField d × BilateralField d => gd (FC q))
        (ENNReal.ofReal p) ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) ≤ _
    rw [e1, e3]
    have hB0 : 0 ≤ B * ε ^ (1 / 4 : ℝ) := by
      have : 0 ≤ ε ^ (1 / 4 : ℝ) := Real.rpow_nonneg hε.1.le _
      positivity
    have hF0 : 0 ≤ Cn * M.delta * ε ^ (-2 : ℝ) * (3 : ℝ) ^ (-a * (h : ℝ)) /
        (1 - (3 : ℝ) ^ (-a)) := by
      have : 0 ≤ ε ^ (-2 : ℝ) := Real.rpow_nonneg hε.1.le _
      positivity
    calc eLpNorm (fun om => yN N om - yeps ε N om) (ENNReal.ofReal p) (Measure.infinitePi laws) +
          eLpNorm (fun q : BilateralField d × BilateralField d =>
            yeps ε N q.1 - yeps ε N (FC q)) (ENNReal.ofReal p)
            ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) +
          eLpNorm (fun om => yN N om - yeps ε N om) (ENNReal.ofReal p) (Measure.infinitePi laws)
        ≤ ENNReal.ofReal (B * ε ^ (1 / 4 : ℝ)) +
            ENNReal.ofReal (Cn * M.delta * ε ^ (-2 : ℝ) * (3 : ℝ) ^ (-a * (h : ℝ)) /
              (1 - (3 : ℝ) ^ (-a))) +
            ENNReal.ofReal (B * ε ^ (1 / 4 : ℝ)) :=
          add_le_add (add_le_add hdiff (htel.trans hgeo)) hdiff
      _ = ENNReal.ofReal (2 * B * ε ^ (1 / 4 : ℝ) + Cn * M.delta * ε ^ (-2 : ℝ) *
            (3 : ℝ) ^ (-a * (h : ℝ)) / (1 - (3 : ℝ) ^ (-a))) := by
          rw [← ENNReal.ofReal_add hB0 hF0, ← ENNReal.ofReal_add (by positivity) hB0]
          congr 1
          ring
  have hcentE : ∀ h N : ℕ,
      eLpNorm (fun om => yN N om -
          ((Measure.infinitePi laws)[yN N | bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ))
            h]) om) (ENNReal.ofReal p) (Measure.infinitePi laws) ≤
        ENNReal.ofReal (4 * Cc * M.delta) := by
    intro h N
    have hcN := (hc N).2.2.2.2
    refine (aux_prop_16_band_split laws h hp1 ENNReal.ofReal_ne_top (hyNint N)).trans ?_
    have c1 := aux_prop_16_copy_centered laws hp1 (yN N) (hyNm N) _ (hCCmp h)
      (∫ om, yN N om ∂(Measure.infinitePi laws))
    have c2 := aux_prop_16_copy_centered laws hp1 (yN N) (hyNm N) _ (hFCmp h)
      (∫ om, yN N om ∂(Measure.infinitePi laws))
    have hx : 0 ≤ Cc * M.delta := by positivity
    calc _ ≤ 2 * eLpNorm (fun om => yN N om - ∫ om, yN N om ∂(Measure.infinitePi laws))
            (ENNReal.ofReal p) (Measure.infinitePi laws) +
          2 * eLpNorm (fun om => yN N om - ∫ om, yN N om ∂(Measure.infinitePi laws))
            (ENNReal.ofReal p) (Measure.infinitePi laws) := add_le_add c1 c2
      _ ≤ 2 * ENNReal.ofReal (Cc * M.delta) + 2 * ENNReal.ofReal (Cc * M.delta) := by
          gcongr <;> exact hcN
      _ = ENNReal.ofReal (4 * Cc * M.delta) := by
          rw [two_mul, ← ENNReal.ofReal_add hx hx, ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
          congr 1
          ring
  refine ⟨fun h N => ?_, fun h N hNh => ?_⟩
  · have hE1 : ∀ ε : ℝ, 0 < ε ∧ ε < 1 / 8 →
        eLpNorm (fun om => yN N om -
          ((Measure.infinitePi laws)[yN N | bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ))
            h]) om) (ENNReal.ofReal p) (Measure.infinitePi laws) ≤
        ENNReal.ofReal (Ccn * M.delta * (3 : ℝ) ^ (-(h : ℝ)) + 2 * B * ε ^ (1 / 4 : ℝ) +
          Cn * M.delta * ε ^ (-2 : ℝ) * (3 : ℝ) ^ (-a * (h : ℝ)) / (1 - (3 : ℝ) ^ (-a))) := by
      intro ε hε
      refine (aux_prop_16_band_split laws h hp1 ENNReal.ofReal_ne_top (hyNint N)).trans ?_
      refine (add_le_add (hcoarse h N) (hfine h N ε hε)).trans ?_
      have hF0 : 0 ≤ 2 * B * ε ^ (1 / 4 : ℝ) + Cn * M.delta * ε ^ (-2 : ℝ) *
          (3 : ℝ) ^ (-a * (h : ℝ)) / (1 - (3 : ℝ) ^ (-a)) := by
        have : 0 ≤ ε ^ (-2 : ℝ) := Real.rpow_nonneg hε.1.le _
        have : 0 ≤ ε ^ (1 / 4 : ℝ) := Real.rpow_nonneg hε.1.le _
        positivity
      rw [← ENNReal.ofReal_add (by positivity) hF0]
      apply ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
    have hnum := aux_prop_16_neumann_numeric a ha0 ha1 h M.delta hδ0 hδ1 Ccn B Cn Cc hCcn.le hB
      hCn.le hCc.le _ hE1 (hcentE h N)
    refine hnum.trans (ENNReal.ofReal_le_ofReal ?_)
    have hsd : 0 ≤ Real.sqrt M.delta := Real.sqrt_nonneg _
    have he : 0 ≤ (3 : ℝ) ^ (-((a / 32) * (h : ℝ))) := by positivity
    apply mul_le_mul_of_nonneg_right _ he
    apply mul_le_mul_of_nonneg_right _ hsd
    linarith
  · refine (aux_prop_16_band_split laws h hp1 ENNReal.ofReal_ne_top (hyNint N)).trans ?_
    refine (add_le_add (hcoarse h N) (hfine0 h N hNh.le)).trans ?_
    rw [add_zero]
    apply ENNReal.ofReal_le_ofReal
    have h2 : 0 ≤ Real.sqrt (4 * (Ccn + 2 * B + Cn / (1 - (3 : ℝ) ^ (-a))) * Cc) + 8 * Cc := by
      positivity
    have he : 0 ≤ (3 : ℝ) ^ (-(h : ℝ)) := by positivity
    apply mul_le_mul_of_nonneg_right _ he
    apply mul_le_mul_of_nonneg_right _ hδ0.le
    linarith


/-- The Neumann clause of `mfd:prop-16`. Its threshold constructs both the
published response moment bank at `4p` and the cell-ellipticity moment bound.
No response-space, coarse-response package, or unsmoothed moment bound is assumed.
`C Bu` records the paper's dependence on the derived numerical bound `Bu`. -/
theorem neumann_conditioning :
  ∀ (d : ℕ) (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (rho : ℝ → ℝ),
    ∀ (hrho : ContDiff ℝ ∞ rho),
    (∀ tau, 0 ≤ rho tau) →
    (∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) →
    (∫ tau, rho tau) = 1 →
    ∀ (pvec : Fin d → ℝ),
      (∑ i : Fin d, (pvec i) ^ 2) = 1 →
    let hP := unit_neumann_poincare _hd
    let Q := unitNeumannCube d
    let S := meanZeroResponseSpace hP
    let L0 : S.space →L[ℝ] ℝ :=
      (affineNeumannLoad pvec).comp (subspaceGradient (meanZeroSobolevGraph Q))
    let fL2 : ℝ → DomainL2 Q := fun eps => face_bump_L2 rho hrho pvec eps
    let Leps : ℝ → S.space →L[ℝ] ℝ := fun eps =>
      (sobolevVolumeLoad (fL2 eps)).comp S.space.subtypeL
        ∀ (t p B : ℝ),
          ((d : ℝ) - 1 < t ∧ t < (d : ℝ) ∧ 2 ≤ p ∧ 0 ≤ B) →
          ∃ (delta0 : ℝ) (C : ℝ → ℝ),
            0 < delta0 ∧ delta0 ≤ 1 ∧ (∀ Bu, 0 < C Bu) ∧
            ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d),
              M.delta ≤ delta0 →
                ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
                InfraredCharacterization M H →
                let P : Measure (BilateralField d) :=
                  (chaosSampleLaw M).toMeasure
                let aN : ℕ → BilateralField d → PositiveCoefficient Q := fun N om =>
                  cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos
                let yN : ℕ → BilateralField d → ℝ := fun N om =>
                  inverseResponse S (aN N om) L0
                let yeps : ℝ → ℕ → BilateralField d → ℝ := fun eps N om =>
                  inverseResponse S (aN N om) (Leps eps)
                let ueps : ℝ → ℕ → BilateralField d → S.space := fun eps N om =>
                  responseSolution S (aN N om) (Leps eps)
                (∃ Bu : ℝ, 0 < Bu ∧
                  ∀ N,
                    MemLp (yN N) (ENNReal.ofReal (4 * p)) P ∧
                      eLpNorm (yN N) (ENNReal.ofReal (4 * p)) P ≤ ENNReal.ofReal Bu) ∧
                ∀ Bu : ℝ, 0 < Bu →
                (∀ N,
                    MemLp (yN N) (ENNReal.ofReal (4 * p)) P ∧
                      eLpNorm (yN N) (ENNReal.ofReal (4 * p)) P ≤ ENNReal.ofReal Bu) →
                (∀ (K : ℕ → BilateralField d → ℝ),
                  (∀ᵐ om ∂P,
                    ∀ (N : ℕ) (eps : ℝ),
                      (0 < eps ∧ eps < 1 / 8) →
                      ∀ (x : SpatialCoordinates d) (rad : ℝ),
                        x ∈ Q → (0 < rad ∧ rad ≤ 1) →
                        localGradientEnergy (aN N om)
                            (s := Metric.ball x rad ∩ (Q : Set (SpatialCoordinates d)))
                            (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
                            (subspaceGradient S.space (ueps eps N om)) ≤
                          K N om * eps ^ (-2 : ℝ) * rad ^ t) →
                  (∀ N,
                    MemLp (K N) (ENNReal.ofReal (3 * p)) P ∧
                      eLpNorm (K N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
                  (∀ N eps, (0 < eps ∧ eps < 1 / 8) →
                    MemLp (yeps eps N) (ENNReal.ofReal (3 * p)) P ∧
                      eLpNorm (yeps eps N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
                  (∀ N eps, (0 < eps ∧ eps < 1 / 8) →
                    eLpNorm (fun om => yN N om - yeps eps N om)
                      (ENNReal.ofReal p) P ≤
                      ENNReal.ofReal (B * eps ^ (1 / 4 : ℝ))) →
                  (∀ h N : ℕ,
                    let sigma_h := bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h
                    eLpNorm
                      (fun om => yN N om - (P[yN N | sigma_h]) om)
                      (ENNReal.ofReal p) P ≤
                    ENNReal.ofReal
                      (C Bu * Real.sqrt M.delta *
                        (3 : ℝ) ^
                          (-((t * (t - (d : ℝ) + 1) / (t + 1) /
                              8 / 32) * (h : ℝ))))) ∧
                  (∀ h N : ℕ, N < h →
                    let sigma_h := bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h
                    eLpNorm
                      (fun om => yN N om - (P[yN N | sigma_h]) om)
                      (ENNReal.ofReal p) P ≤
                    ENNReal.ofReal
                      (C Bu * M.delta * (3 : ℝ) ^ (-(h : ℝ)))))
    := by
  intro d hd instM instB rho hrho hrhoNonneg hrhoSupport hrhoIntegral pvec hpvec hP Q S L0
    fL2 Leps t p B htpB
  have hp4 : 1 ≤ 4 * p := by linarith [htpB.2.2.1]
  obtain ⟨Cresp, deltaResp, hCresp, hdeltaResp, hwitness⟩ :=
    inputs_responses_witness d hd (4 * p) hp4
  obtain ⟨deltaCore, C, hdeltaCore, hdeltaCore1, hC, hcore⟩ :=
    neumann_conditioning_of_cell_moments d hd Cresp hCresp rho hrho hrhoNonneg hrhoSupport
      hrhoIntegral pvec hpvec t p B htpB
  let deltaRange : ℝ := 1 / (Cresp * (4 * p) + 1)
  have hdeltaRange : 0 < deltaRange := by dsimp only [deltaRange]; positivity
  refine ⟨min deltaCore (min deltaResp deltaRange), C,
    lt_min hdeltaCore (lt_min hdeltaResp hdeltaRange),
    (min_le_left _ _).trans hdeltaCore1, hC, ?_⟩
  intro M hdelta H hH P aN yN yeps ueps
  have hCore : M.delta ≤ deltaCore := hdelta.trans (min_le_left _ _)
  have hResp : M.delta ≤ deltaResp :=
    hdelta.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRange : M.delta ≤ deltaRange :=
    hdelta.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Rm, hRC, _horders⟩ := hwitness M hResp
  have hscale : 4 * p ≤ Cresp⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ :=
    aux_rbpf_order_admissible Cresp (4 * p) M.delta hCresp hp4 M.shellPrefix.delta_pos
      M.shellPrefix.delta_le_half hRange
  obtain ⟨hex, hall⟩ :=
    hcore M ⟨M.shellPrefix.delta_pos, hCore⟩ Rm hRC hscale H hH
  refine ⟨hex, ?_⟩
  intro Bu hBu hyBu K hgrowth hKmom hyeps hsmooth
  have hKm : ∀ N, AEStronglyMeasurable (K N) P :=
    fun N => (hKmom N).1.aestronglyMeasurable
  have hK0 : ∀ᵐ om ∂P, ∀ N, 0 ≤ K N om := by
    filter_upwards [hgrowth] with om hom N
    let c : SpatialCoordinates d := fun _ => (1 / 2 : ℝ)
    have hc : c ∈ Q := by
      change c ∈ (centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
        Set (SpatialCoordinates d))
      rw [centeredCube_eq_pi]
      intro i hi
      constructor <;> norm_num [c]
    have heps : 0 < (1 / 16 : ℝ) ∧ (1 / 16 : ℝ) < 1 / 8 := by norm_num
    have hE0 := localGradientEnergy_nonneg (aN N om)
      (s := Metric.ball c 1 ∩ (Q : Set (SpatialCoordinates d)))
      (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
      (subspaceGradient S.space (ueps (1 / 16) N om))
    have hbound := hom N (1 / 16) heps c 1 hc ⟨one_pos, le_rfl⟩
    simp only [Real.one_rpow, mul_one] at hbound
    have hp : 0 < (1 / 16 : ℝ) ^ (-2 : ℝ) :=
      Real.rpow_pos_of_pos (by norm_num) _
    nlinarith [hE0.trans hbound]
  exact hall Bu hBu hyBu K hKm hK0 hgrowth hKmom hyeps hsmooth

end SubdiffusiveProcess.AuditExports
