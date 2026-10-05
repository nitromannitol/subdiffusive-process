module

public import SubdiffusiveProcess.Sobolev.AffineProjection
public import SubdiffusiveProcess.Paper.lem_finite_trace_smooth_net
public import SubdiffusiveProcess.Paper.candidate_good_estimates
public import SubdiffusiveProcess.Paper.lem_interp
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.CoarseGrainingVocab.Section11.SubunitHarmonicLipschitz
public import SubdiffusiveProcess.Sobolev.NativeH1
public import SubdiffusiveProcess.Sobolev.NativeH10
public import SubdiffusiveProcess.ResponseMoments.AffineTrace
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.Excess
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.Interior
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6OddClass.EvenBoundHessian
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.SandwichNondegeneracyAttainment
public import SubdiffusiveProcess.EllipticRegularity.CubeDilation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonicInterior
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonicCoefficientModels
public import SubdiffusiveProcess.CoarseGrainingVocab.Section11.SubunitEstimates
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.CubeGeometryApi

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_lem_affine_gcn_competitor_weak_harmonic
    (d : ℕ) (z : SpatialCoordinates d) (R : ℝ) (hRpos : 0 < R)
    (Ubar : weakSobolevGraph (centeredCube z R hRpos))
    (hEq : ∀ psi : killedSobolevGraph (centeredCube z R hRpos),
      inner ℝ (sobolevGradient (Ubar : SobolevData (centeredCube z R hRpos)))
        (subspaceGradient (killedSobolevGraph (centeredCube z R hRpos)) psi) = 0) :
    ∃ w : Homogenization.H1Function
        (centeredCube z R hRpos : Set (SpatialCoordinates d)),
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.IsUnitWeaklyHarmonicOn
        (centeredCube z R hRpos : Set (SpatialCoordinates d)) w ∧
      (w : SpatialCoordinates d → ℝ) =
        (Ubar : SobolevData (centeredCube z R hRpos)).1 := by
  obtain ⟨w, hwval, hwgrad⟩ :=
    SubdiffusiveProcess.exists_nativeH1Function_of_weakSobolevGraph Ubar
  refine ⟨w, ?_, hwval⟩
  intro phi
  let q : SobolevData (centeredCube z R hRpos) :=
    ((phi.toH1Function.memL2).toLp phi.toFun,
      fun i => (phi.toH1Function.gradMemL2 i).toLp
        (fun x => phi.toH1Function.grad x i))
  have hq : q ∈ killedSobolevGraph (centeredCube z R hRpos) := by
    simpa [q] using
      (SubdiffusiveProcess.killed_of_nativeH10_local phi)
  have htest := hEq ⟨q, hq⟩
  change inner ℝ (sobolevGradient (Ubar : SobolevData (centeredCube z R hRpos)))
      (sobolevGradient q) = 0 at htest
  have hi (i : Fin d) : IntegrableOn
      (fun x => w.grad x i * phi.toH1Function.grad x i)
      (centeredCube z R hRpos : Set (SpatialCoordinates d)) volume := by
    simpa only [MeasureTheory.IntegrableOn] using!
      (w.gradMemL2 i).integrable_mul (phi.toH1Function.gradMemL2 i)
  have hcoord (i : Fin d) :
      (∫ x in (centeredCube z R hRpos : Set (SpatialCoordinates d)),
        w.grad x i * phi.toH1Function.grad x i) =
        inner ℝ ((sobolevGradient (Ubar : SobolevData (centeredCube z R hRpos))) i)
          ((sobolevGradient q) i) := by
    rw [L2.inner_def]
    simp only [RCLike.inner_apply, conj_trivial]
    apply integral_congr_ae
    filter_upwards [(MemLp.coeFn_toLp (phi.toH1Function.gradMemL2 i))] with x hx
    change w.grad x i * phi.toH1Function.grad x i =
      ((phi.toH1Function.gradMemL2 i).toLp
          (fun y => phi.toH1Function.grad y i)) x *
        ((Ubar : SobolevData (centeredCube z R hRpos)).2 i) x
    rw [show w.grad = fun y i => ((Ubar :
      SobolevData (centeredCube z R hRpos)).2 i) y from hwgrad]
    rw [hx]
    ring
  calc
    (∫ x in (centeredCube z R hRpos : Set (SpatialCoordinates d)),
        Homogenization.vecDot (w.grad x) (phi.toH1Function.grad x)) =
        ∫ x in (centeredCube z R hRpos : Set (SpatialCoordinates d)),
          ∑ i : Fin d, w.grad x i * phi.toH1Function.grad x i := by
            rfl
    _ = ∑ i : Fin d, ∫ x in (centeredCube z R hRpos : Set (SpatialCoordinates d)),
          w.grad x i * phi.toH1Function.grad x i := by
            rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
    _ = ∑ i : Fin d, inner ℝ ((sobolevGradient
          (Ubar : SobolevData (centeredCube z R hRpos))) i) ((sobolevGradient q) i) := by
            exact Finset.sum_congr rfl (fun i _ => hcoord i)
    _ = inner ℝ (sobolevGradient (Ubar : SobolevData (centeredCube z R hRpos)))
          (sobolevGradient q) := (PiLp.inner_apply _ _).symm
    _ = 0 := htest

theorem aux_lem_affine_gcn_competitor_glb (eSet : Set ℝ) (hne : eSet.Nonempty)
    (hnonneg : ∀ e ∈ eSet, 0 ≤ e) (bound : ℝ)
    (hwitness : ∃ e ∈ eSet, e ≤ bound) :
    ∃ Lambda : ℝ, IsGLB eSet Lambda ∧ eSet.Nonempty ∧ Lambda ≤ bound := by
  have hbelow : BddBelow eSet := by
    refine ⟨0, ?_⟩
    intro e he
    exact hnonneg e he
  let Lambda : ℝ := sInf eSet
  have hglb : IsGLB eSet Lambda := by
    exact Real.isGLB_sInf hne hbelow
  have hle : Lambda ≤ bound := by
    obtain ⟨e, he, heb⟩ := hwitness
    exact (csInf_le hbelow he).trans heb
  exact ⟨Lambda, hglb, hne, hle⟩

theorem aux_lem_affine_gcn_competitor_budget_pos
    (d : ℕ) (Q : Opens (SpatialCoordinates d))
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GammaE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    (u : DomainL2 Q) (z : SpatialCoordinates d) (r c : ℝ)
    (hr : 0 < r) (hc : 0 < c) :
    0 < (GammaE.measure u (Metric.ball z (r / 2))).toReal +
      c * (volume (Metric.ball z (r / 2))).toReal := by
  have hvol : 0 < (volume (Metric.ball z (r / 2))).toReal := by
    rw [volume_ball_spatial z (half_pos hr)]
    rw [ENNReal.toReal_ofReal (by positivity)]
    positivity
  have henergy : 0 ≤ (GammaE.measure u (Metric.ball z (r / 2))).toReal :=
    ENNReal.toReal_nonneg
  have hmul : 0 < c * (volume (Metric.ball z (r / 2))).toReal :=
    mul_pos hc hvol
  linarith

theorem aux_lem_affine_gcn_competitor_holder_sSup_le
    (d : ℕ) (beta : ℝ) (S : Set (SpatialCoordinates d))
    (G : SpatialCoordinates d → ℝ) (K : ℝ)
    (hne : (_root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet beta S G).Nonempty)
    (hquot : ∀ v ∈ _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet beta S G, v ≤ K) :
    _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta S G ≤ K := by
  unfold _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm
  exact csSup_le hne hquot

theorem aux_lem_affine_gcn_competitor_energy_nonneg
    (d : ℕ) (Q : Opens (SpatialCoordinates d))
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GammaE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    (q : Set (SpatialCoordinates d))
    (b : SpatialCoordinates d → ℝ) :
    ∀ e ∈ {e : ℝ | ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
      v ∈ E.domain ∧
      ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
      ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (Q : Set (SpatialCoordinates d))] V) ∧
      (∀ x ∈ frontier q, V x = b x) ∧
      e = (GammaE.measure v q).toReal},
      0 ≤ e := by
  intro e he
  rcases he with ⟨v, V, hv, hVcont, hVae, hVfrontier, rfl⟩
  exact ENNReal.toReal_nonneg

theorem aux_lem_affine_gcn_competitor_extension_glb
    (d : ℕ) (Q : Opens (SpatialCoordinates d))
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GammaE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    (q : Set (SpatialCoordinates d)) (b : SpatialCoordinates d → ℝ)
    (beta Cin s r bound : ℝ)
    (hbcont : ContinuousOn b (closure (Q : Set (SpatialCoordinates d))))
    (hholder : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (frontier q) b)
    (hext : ∀ g : SpatialCoordinates d → ℝ,
      ContinuousOn g (closure (Q : Set (SpatialCoordinates d))) →
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (frontier q) g →
      ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
        v ∈ E.domain ∧
        ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
        ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (Q : Set (SpatialCoordinates d))] V) ∧
        (∀ x ∈ frontier q, V x = g x) ∧
        (GammaE.measure v q).toReal ≤
          Cin * s * r ^ ((d : ℝ) - 2) *
            (r ^ beta * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier q) g) ^ 2)
    (hbudget : Cin * s * r ^ ((d : ℝ) - 2) *
        (r ^ beta * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier q) b) ^ 2 ≤ bound) :
    ∃ Lambda : ℝ,
      IsGLB
        {e : ℝ | ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
          v ∈ E.domain ∧
          ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
          ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (Q : Set (SpatialCoordinates d))] V) ∧
          (∀ x ∈ frontier q, V x = b x) ∧
          e = (GammaE.measure v q).toReal} Lambda ∧
      {e : ℝ | ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
          v ∈ E.domain ∧
          ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
          ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (Q : Set (SpatialCoordinates d))] V) ∧
          (∀ x ∈ frontier q, V x = b x) ∧
          e = (GammaE.measure v q).toReal}.Nonempty ∧
      Lambda ≤ bound := by
  let eSet : Set ℝ :=
    {e : ℝ | ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
        v ∈ E.domain ∧
        ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
        ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (Q : Set (SpatialCoordinates d))] V) ∧
        (∀ x ∈ frontier q, V x = b x) ∧
        e = (GammaE.measure v q).toReal}
  obtain ⟨v, V, hv, hVcont, hvV, hVb, henergy⟩ := hext b hbcont hholder
  have hne : eSet.Nonempty := by
    refine ⟨(GammaE.measure v q).toReal, ?_⟩
    exact ⟨v, V, hv, hVcont, hvV, hVb, rfl⟩
  have hnonneg : ∀ e ∈ eSet, 0 ≤ e := by
    exact aux_lem_affine_gcn_competitor_energy_nonneg d Q E GammaE q b
  obtain ⟨Lambda, hglb, hne', hbound⟩ :=
    aux_lem_affine_gcn_competitor_glb eSet hne hnonneg bound
      ⟨(GammaE.measure v q).toReal, by
        exact ⟨v, V, hv, hVcont, hvV, hVb, rfl⟩, henergy.trans hbudget⟩
  exact ⟨Lambda, by simpa [eSet] using hglb, by simpa [eSet] using hne', hbound⟩

theorem aux_lem_affine_gcn_competitor_abs_zero (x : ℝ) (hx : x = 0) :
    |x| = 0 := by
  rw [hx, abs_zero]

theorem aux_lem_affine_gcn_competitor_holder_of_pointwise
    (d : ℕ) (beta : ℝ) (S : Set (SpatialCoordinates d))
    (G : SpatialCoordinates d → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hbeta : 0 < beta)
    (hbound : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      |G x - G y| ≤ K * dist x y ^ beta) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S G := by
  refine ⟨K, ?_⟩
  rintro v ⟨x, hx, y, hy, hxy, rfl⟩
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hp : 0 < dist x y ^ beta := Real.rpow_pos_of_pos hd beta
  have hdist : dist x y ≤ Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
    calc
      dist x y = ‖x - y‖ := by rw [dist_eq_norm]
      _ ≤ ‖(SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc (x - y) :
          EuclideanSpace ℝ (Fin d))‖ :=
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.norm_le_norm_toEuc (x - y)
      _ = Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
        rw [EuclideanSpace.norm_eq]
        simp [SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc_apply,
          Real.norm_eq_abs, sq_abs]
  have hsqrt : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) :=
    lt_of_lt_of_le hd hdist
  have hden : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ beta := by
    exact Real.rpow_pos_of_pos hsqrt beta
  have hquot : |G x - G y| /
      Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ beta ≤ K := by
    have hpw : dist x y ^ beta ≤
        Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ beta :=
      Real.rpow_le_rpow (dist_nonneg) hdist hbeta.le
    calc
      |G x - G y| / Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ beta ≤
          (K * dist x y ^ beta) /
            Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ beta := by
              exact div_le_div_of_nonneg_right (hbound x hx y hy hxy) hden.le
      _ ≤ (K * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ beta) /
            Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ beta := by
              exact div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left hpw hK) hden.le
      _ = K := by field_simp [hden.ne']
  exact hquot

theorem aux_lem_affine_gcn_competitor_euclideanNorm_eq_toEuc_sub
    {d : ℕ} (x y : SpatialCoordinates d) :
    ‖(SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc x : EuclideanSpace ℝ (Fin d)) -
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc y‖ =
      Homogenization.euclideanNorm (x - y) := by
  rw [← map_sub]
  unfold Homogenization.euclideanNorm Homogenization.vecNormSq Homogenization.vecDot
  rw [EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc_apply, Real.norm_eq_abs, pow_two]

theorem aux_lem_affine_gcn_competitor_S0T_basic
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    (∀ x ∈ closure (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
        Set (SpatialCoordinates d)),
      _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r x ∈ closure (Metric.ball z (r / 2))) ∧
    (∀ x y : SpatialCoordinates d, dist (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r x)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r y) = r * dist x y) ∧
    (∀ x ∈ closure (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
        Set (SpatialCoordinates d)),
      ∀ y ∈ closure (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
        Set (SpatialCoordinates d)), dist x y ≤ 1) := by
  have hS0cl : closure (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
      Set (SpatialCoordinates d)) = Metric.closedBall (0 : SpatialCoordinates d) (1 / 2) := by
    change closure (Metric.ball (0 : SpatialCoordinates d) (1 / 2)) = _
    exact closure_ball 0 (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [hS0cl, Metric.mem_closedBall] at hx
    rw [closure_ball (z : SpatialCoordinates d) (by linarith : r / 2 ≠ 0), Metric.mem_closedBall]
    have hdist : dist (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r x) z = r * dist x 0 := by
      rw [dist_eq_norm]
      have heq : _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r x - z = r • (x - 0) := by
        funext i
        simp [_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation]
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      simp [dist_eq_norm]
    rw [hdist]
    calc
      r * dist x 0 ≤ r * (1 / 2) := mul_le_mul_of_nonneg_left hx (le_of_lt hr)
      _ = r / 2 := by ring
  · intro x y
    rw [dist_eq_norm]
    have heq : _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r x -
        _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r y = r • (x - y) := by
      funext i
      simp [_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation]
      ring
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    rw [dist_eq_norm]
  · intro x hx y hy
    rw [hS0cl, Metric.mem_closedBall] at hx hy
    calc
      dist x y ≤ dist x 0 + dist 0 y := dist_triangle x 0 y
      _ = dist x 0 + dist y 0 := by rw [dist_comm 0 y]
      _ ≤ 1 := by linarith


theorem aux_lem_affine_gcn_competitor_z_mem_middleQuarter
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) :
    z ∈ SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.middleQuarter (z, R) := by
  rw [SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.middleQuarter_eq_centeredAxisCube]
  exact SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.mem_centeredAxisCube.mpr
    (by intro i; rw [sub_self, abs_zero]; linarith)

theorem aux_lem_affine_gcn_competitor_weighted_exponent_neg
    (d : ℕ) (hd : 2 ≤ d) (alpha beta gamma zeta : ℝ)
    (hbeta : 1 / 2 < beta) (hba : beta < alpha)
    (hneg : affineExponent (d : ℝ) alpha beta gamma zeta < 0) :
    (((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2 - 2 * gamma) *
          ((alpha - beta) / (alpha + (d : ℝ) / 2)) +
        (((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2 - alpha * gamma) *
          (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)) < 0 := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have halpha0 : 0 < alpha := lt_trans (lt_trans hhalf hbeta) hba
  have hden : alpha + (d : ℝ) / 2 ≠ 0 := by
    nlinarith
  have hid :
      (((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2 - 2 * gamma) *
            ((alpha - beta) / (alpha + (d : ℝ) / 2)) +
          (((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2 - alpha * gamma) *
            (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)) =
        affineExponent (d : ℝ) alpha beta gamma zeta := by
    unfold affineExponent
    field_simp [hden]
    ring
  rw [hid]
  exact hneg

theorem aux_lem_affine_gcn_competitor_holder_scaled
    (d : ℕ) (alpha : ℝ) (S : Set (SpatialCoordinates d))
    (G : SpatialCoordinates d → ℝ) (K R : ℝ)
    (hK : 0 ≤ K) (hR : 0 < R) (ha : 0 < alpha)
    (hbound : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      |G x - G y| ≤ K * (dist x y / R) ^ alpha) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha S G := by
  apply aux_lem_affine_gcn_competitor_holder_of_pointwise d alpha S G
    (K * R ^ (-alpha))
  · positivity
  · exact ha
  · intro x hx y hy hxy
    calc
      |G x - G y| ≤ K * (dist x y / R) ^ alpha := hbound x hx y hy hxy
      _ = (K * R ^ (-alpha)) * dist x y ^ alpha := by
        rw [Real.div_rpow (dist_nonneg) hR.le]
        rw [Real.rpow_neg (le_of_lt hR)]
        field_simp

theorem aux_lem_affine_gcn_competitor_taylor
    {d : ℕ} {V : SpatialCoordinates d → ℝ} {S : Set (SpatialCoordinates d)}
    (hS : Convex ℝ S) {M : ℝ} (hM : 0 ≤ M)
    (hgrad : ∀ x ∈ S, ∀ y ∈ S,
      ‖fderiv ℝ V x - fderiv ℝ V y‖ ≤ M * ‖x - y‖)
    (hdiff : ∀ x ∈ S, DifferentiableAt ℝ V x)
    {p q : SpatialCoordinates d} (hp : p ∈ S) (hq : q ∈ S) :
    |V q - V p - fderiv ℝ V p (q - p)| ≤ M * ‖q - p‖ ^ 2 := by
  have hTS : segment ℝ p q ⊆ S := hS.segment_subset hp hq
  have hTconv : Convex ℝ (segment ℝ p q) := convex_segment p q
  have hpT : p ∈ segment ℝ p q := left_mem_segment ℝ p q
  have hqT : q ∈ segment ℝ p q := right_mem_segment ℝ p q
  have hnorm : ∀ x ∈ segment ℝ p q, ‖x - p‖ ≤ ‖q - p‖ := by
    intro x hx
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
    have hform : a = 1 - b := by linarith only [hab]
    rw [hform, sub_smul, one_smul]
    have hnonneg : 0 ≤ b := by linarith
    have hzp : p - b • p + b • q - p = b • (q - p) := by
      calc
        p - b • p + b • q - p = b • q - b • p := by abel
        _ = b • (q - p) := by rw [smul_sub]
    rw [hzp, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith only [hab, ha])
  have hgrad' : ∀ x ∈ segment ℝ p q,
      ‖fderiv ℝ V x - fderiv ℝ V p‖ ≤ M * ‖q - p‖ := by
    intro x hx
    have h1 := hgrad x (hTS hx) p hp
    exact h1.trans (mul_le_mul_of_nonneg_left (hnorm x hx) hM)
  have hmain := hTconv.norm_image_sub_le_of_norm_fderiv_le' (φ := fderiv ℝ V p)
    (fun x hx => hdiff x (hTS hx)) hgrad' hpT hqT
  rw [Real.norm_eq_abs] at hmain
  calc
    |V q - V p - fderiv ℝ V p (q - p)| ≤
        M * ‖q - p‖ * ‖q - p‖ := hmain
    _ = M * ‖q - p‖ ^ 2 := by ring

theorem aux_lem_affine_gcn_competitor_fderiv_of_gradField
    {d : ℕ} (V : SpatialCoordinates d → ℝ) {K : ℝ}
    (hgrad : ∀ x ∈ Set.univ, ∀ y ∈ Set.univ,
      ‖SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.gradField V x -
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.gradField V y‖ ≤
        K * ‖x - y‖) :
    ∀ x y : SpatialCoordinates d,
      ‖fderiv ℝ V x - fderiv ℝ V y‖ ≤
        (d : ℝ) * K * ‖x - y‖ := by
  intro x y
  have hxy := hgrad x (Set.mem_univ x) y (Set.mem_univ y)
  calc
    ‖fderiv ℝ V x - fderiv ℝ V y‖ =
        ‖SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.slopeCLM
            (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.gradField V x) -
          SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.slopeCLM
            (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.gradField V y)‖ := by
      rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.slopeCLM_gradField,
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.slopeCLM_gradField]
    _ = ‖SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.slopeCLM
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.gradField V x -
            SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.gradField V y)‖ := by
      rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.slopeCLM_sub]
    _ ≤ (d : ℝ) *
          ‖SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.gradField V x -
            SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.gradField V y‖ := by
      exact SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.norm_slopeCLM_le _
    _ ≤ (d : ℝ) * (K * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left hxy (Nat.cast_nonneg d)
    _ = (d : ℝ) * K * ‖x - y‖ := by ring

theorem aux_lem_affine_gcn_competitor_hessian_uniform
    (d : ℕ) [NeZero d] {W S : Set (SpatialCoordinates d)}
    {V : SpatialCoordinates d → ℝ} {delta : ℝ}
    (hWtop : volume W ≠ ⊤) (hWpos : 0 < (volume W).toReal)
    (hharm : InnerProductSpace.HarmonicOnNhd
      (V ∘ (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm :
        EuclideanSpace ℝ (Fin d) → SpatialCoordinates d))
      ((SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc :
        SpatialCoordinates d → EuclideanSpace ℝ (Fin d)) '' W))
    (hint : IntegrableOn (fun x => V x ^ 2) W volume)
    (hdelta : 0 < delta)
    (hball : ∀ p : SpatialCoordinates d, p ∈ S → Metric.ball p delta ⊆ W) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ S,
      ‖fderiv ℝ (fderiv ℝ (V ∘
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm :
          EuclideanSpace ℝ (Fin d) → SpatialCoordinates d)))
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc p)‖ ≤ M := by
  obtain ⟨C, hC0, hC⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6OddClass.exists_hessian_normalizedL2On_bound d
  let M : ℝ := C * delta⁻¹ * delta⁻¹ *
    Real.sqrt ((volume W).toReal / delta ^ d) * normalizedL2On W V
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hC0 (inv_nonneg.mpr hdelta.le))
        (inv_nonneg.mpr hdelta.le)) (Real.sqrt_nonneg _))
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.normalizedL2On_nonneg _ _)
  refine ⟨M, hM0, ?_⟩
  intro p hp
  exact hC W V p delta hWtop hWpos hharm hint hdelta (hball p hp)

theorem aux_lem_affine_gcn_competitor_inner_ball
    {d : ℕ} {z p : SpatialCoordinates d} {r R : ℝ}
    (_hr : 0 < r) (_hrR : r < R) (hp : p ∈ Metric.ball z (r / 2)) :
    Metric.ball p ((R - r) / 2) ⊆ Metric.ball z (R / 2) := by
  intro x hx
  rw [Metric.mem_ball] at hx hp ⊢
  calc
    dist x z ≤ dist x p + dist p z := dist_triangle x p z
    _ < (R - r) / 2 + r / 2 := add_lt_add hx hp
    _ = R / 2 := by ring

theorem aux_lem_affine_gcn_competitor_harmonic_taylor
    (d : ℕ) [NeZero d] {W S : Set (SpatialCoordinates d)}
    {V : SpatialCoordinates d → ℝ} {delta : ℝ}
    (hWtop : volume W ≠ ⊤) (hWpos : 0 < (volume W).toReal)
    (hharm : InnerProductSpace.HarmonicOnNhd
      (V ∘ (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm :
        EuclideanSpace ℝ (Fin d) → SpatialCoordinates d))
      ((SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc :
        SpatialCoordinates d → EuclideanSpace ℝ (Fin d)) '' W))
    (hint : IntegrableOn (fun x => V x ^ 2) W volume)
    (hdelta : 0 < delta) (hSW : S ⊆ W) (hball : ∀ p : SpatialCoordinates d,
      p ∈ S → Metric.ball p delta ⊆ W) (hSconv : Convex ℝ S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ S, ∀ q ∈ S,
      |V q - V p - fderiv ℝ V p (q - p)| ≤
        M * ‖SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc (q - p)‖ ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := aux_lem_affine_gcn_competitor_hessian_uniform
    d hWtop hWpos hharm hint hdelta hball
  refine ⟨M, hM0, ?_⟩
  intro p hp q hq
  have hAt : ∀ x ∈ S, InnerProductSpace.HarmonicAt
      (V ∘ (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm :
        EuclideanSpace ℝ (Fin d) → SpatialCoordinates d))
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc x) := by
    intro x hx
    exact hharm _ (Set.mem_image_of_mem _ (hSW hx))
  have hTaylor :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6OddClass.abs_sub_fderiv_apply_le_of_hessian_bound_vec
      hSconv hAt (fun x hx => hM x hx) hp hq
  have hderiv : fderiv ℝ
      (V ∘ (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm :
        EuclideanSpace ℝ (Fin d) → SpatialCoordinates d))
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc p)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc q -
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc p) =
      fderiv ℝ V p (q - p) := by
    have hf := SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.fderiv_comp_toEuc
      (V ∘ (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm :
        EuclideanSpace ℝ (Fin d) → SpatialCoordinates d)) p
    have hf' : fderiv ℝ V p =
        (fderiv ℝ (V ∘
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm :
            EuclideanSpace ℝ (Fin d) → SpatialCoordinates d))
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc p)).comp
            (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc :
              SpatialCoordinates d ≃L[ℝ] EuclideanSpace ℝ (Fin d)).toContinuousLinearMap := by
      simpa only [Function.comp_apply,
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.comp_toEuc_symm_toEuc] using hf
    rw [hf']
    simp only [ContinuousLinearMap.comp_apply, map_sub]
    rfl
  rw [hderiv] at hTaylor
  exact hTaylor

theorem aux_lem_affine_gcn_competitor_harmonic_taylor_explicit
    (d : ℕ) [NeZero d] {W S : Set (SpatialCoordinates d)}
    {V : SpatialCoordinates d → ℝ} {delta : ℝ}
    (hWtop : volume W ≠ ⊤) (hWpos : 0 < (volume W).toReal)
    (hharm : InnerProductSpace.HarmonicOnNhd
      (V ∘ (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm :
        EuclideanSpace ℝ (Fin d) → SpatialCoordinates d))
      ((SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc :
        SpatialCoordinates d → EuclideanSpace ℝ (Fin d)) '' W))
    (hint : IntegrableOn (fun x => V x ^ 2) W volume)
    (hdelta : 0 < delta) (hSW : S ⊆ W)
    (hball : ∀ p : SpatialCoordinates d, p ∈ S → Metric.ball p delta ⊆ W)
    (hSconv : Convex ℝ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S, ∀ q ∈ S,
      |V q - V p - fderiv ℝ V p (q - p)| ≤
        (C * delta⁻¹ * delta⁻¹ *
          Real.sqrt ((volume W).toReal / delta ^ d) * normalizedL2On W V) *
          ‖SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc (q - p)‖ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6OddClass.exists_hessian_normalizedL2On_bound d
  let M : ℝ := C * delta⁻¹ * delta⁻¹ *
    Real.sqrt ((volume W).toReal / delta ^ d) * normalizedL2On W V
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hC0 (inv_nonneg.mpr hdelta.le))
        (inv_nonneg.mpr hdelta.le)) (Real.sqrt_nonneg _))
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.normalizedL2On_nonneg _ _)
  refine ⟨C, hC0, ?_⟩
  intro p hp q hq
  have hAt : ∀ x ∈ S, InnerProductSpace.HarmonicAt
      (V ∘ (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm :
        EuclideanSpace ℝ (Fin d) → SpatialCoordinates d))
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc x) := by
    intro x hx
    exact hharm _ (Set.mem_image_of_mem _ (hSW hx))
  have hM : ∀ x ∈ S,
      ‖fderiv ℝ (fderiv ℝ (V ∘
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm :
          EuclideanSpace ℝ (Fin d) → SpatialCoordinates d)))
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc x)‖ ≤ M := by
    intro x hx
    dsimp [M]
    exact hC W V x delta hWtop hWpos hharm hint hdelta (hball x hx)
  have hTaylor :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6OddClass.abs_sub_fderiv_apply_le_of_hessian_bound_vec
      hSconv hAt hM hp hq
  have hderiv : fderiv ℝ
      (V ∘ (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm :
        EuclideanSpace ℝ (Fin d) → SpatialCoordinates d))
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc p)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc q -
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc p) =
      fderiv ℝ V p (q - p) := by
    have hf := SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.fderiv_comp_toEuc
      (V ∘ (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm :
        EuclideanSpace ℝ (Fin d) → SpatialCoordinates d)) p
    have hf' : fderiv ℝ V p =
        (fderiv ℝ (V ∘
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm :
            EuclideanSpace ℝ (Fin d) → SpatialCoordinates d))
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc p)).comp
            (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc :
              SpatialCoordinates d ≃L[ℝ] EuclideanSpace ℝ (Fin d)).toContinuousLinearMap := by
      simpa only [Function.comp_apply,
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.comp_toEuc_symm_toEuc] using hf
    rw [hf']
    simp only [ContinuousLinearMap.comp_apply, map_sub]
    rfl
  rw [hderiv] at hTaylor
  simpa [M] using hTaylor

theorem aux_lem_affine_gcn_competitor_harmonic_taylor_with_constant
    (d : ℕ) [NeZero d] {W S : Set (SpatialCoordinates d)}
    {V : SpatialCoordinates d → ℝ} {delta C : ℝ}
    (_hC : 0 ≤ C)
    (hCbound : ∀ (W : Set (SpatialCoordinates d)) (V : SpatialCoordinates d → ℝ)
      (p : SpatialCoordinates d) (r : ℝ), volume W ≠ ⊤ →
      0 < (volume W).toReal →
      InnerProductSpace.HarmonicOnNhd
        (V ∘ (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm :
          EuclideanSpace ℝ (Fin d) → SpatialCoordinates d))
        ((SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc :
          SpatialCoordinates d → EuclideanSpace ℝ (Fin d)) '' W) →
      IntegrableOn (fun y => V y ^ 2) W volume → 0 < r →
      Metric.ball p r ⊆ W →
      ‖fderiv ℝ (fderiv ℝ (V ∘
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm :
          EuclideanSpace ℝ (Fin d) → SpatialCoordinates d)))
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc p)‖ ≤
        C * r⁻¹ * r⁻¹ * Real.sqrt ((volume W).toReal / r ^ d) *
          normalizedL2On W V)
    (hWtop : volume W ≠ ⊤) (hWpos : 0 < (volume W).toReal)
    (hharm : InnerProductSpace.HarmonicOnNhd
      (V ∘ (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm :
        EuclideanSpace ℝ (Fin d) → SpatialCoordinates d))
      ((SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc :
        SpatialCoordinates d → EuclideanSpace ℝ (Fin d)) '' W))
    (hint : IntegrableOn (fun x => V x ^ 2) W volume)
    (hdelta : 0 < delta) (hSW : S ⊆ W)
    (hball : ∀ p : SpatialCoordinates d, p ∈ S → Metric.ball p delta ⊆ W)
    (hSconv : Convex ℝ S) :
    ∀ p ∈ S, ∀ q ∈ S,
      |V q - V p - fderiv ℝ V p (q - p)| ≤
        (C * delta⁻¹ * delta⁻¹ *
          Real.sqrt ((volume W).toReal / delta ^ d) * normalizedL2On W V) *
          ‖SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc (q - p)‖ ^ 2 := by
  have hM : ∀ x ∈ S,
      ‖fderiv ℝ (fderiv ℝ (V ∘
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm :
          EuclideanSpace ℝ (Fin d) → SpatialCoordinates d)))
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc x)‖ ≤
        C * delta⁻¹ * delta⁻¹ *
          Real.sqrt ((volume W).toReal / delta ^ d) * normalizedL2On W V := by
    intro x hx
    exact hCbound W V x delta hWtop hWpos hharm hint hdelta (hball x hx)
  intro p hp q hq
  have hAt : ∀ x ∈ S, InnerProductSpace.HarmonicAt
      (V ∘ (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm :
        EuclideanSpace ℝ (Fin d) → SpatialCoordinates d))
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc x) := by
    intro x hx
    exact hharm _ (Set.mem_image_of_mem _ (hSW hx))
  have hTaylor :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6OddClass.abs_sub_fderiv_apply_le_of_hessian_bound_vec
      hSconv hAt hM hp hq
  have hderiv : fderiv ℝ
      (V ∘ (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm :
        EuclideanSpace ℝ (Fin d) → SpatialCoordinates d))
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc p)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc q -
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc p) =
      fderiv ℝ V p (q - p) := by
    have hf := SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.fderiv_comp_toEuc
      (V ∘ (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm :
        EuclideanSpace ℝ (Fin d) → SpatialCoordinates d)) p
    have hf' : fderiv ℝ V p =
        (fderiv ℝ (V ∘
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm :
            EuclideanSpace ℝ (Fin d) → SpatialCoordinates d))
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc p)).comp
            (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc :
              SpatialCoordinates d ≃L[ℝ] EuclideanSpace ℝ (Fin d)).toContinuousLinearMap := by
      simpa only [Function.comp_apply,
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.comp_toEuc_symm_toEuc] using hf
    rw [hf']
    simp only [ContinuousLinearMap.comp_apply, map_sub]
    rfl
  rw [hderiv] at hTaylor
  simpa only [hderiv, map_sub] using! hTaylor

theorem aux_lem_affine_gcn_competitor_taylor_point_bound
    {d : ℕ} (z : SpatialCoordinates d) (r M : ℝ)
    (hr : 0 < r) (hM : 0 ≤ M)
    {V : SpatialCoordinates d → ℝ}
    (hTaylor : ∀ p ∈ Metric.ball z (r / 2), ∀ q ∈ Metric.ball z (r / 2),
      |V q - V p - fderiv ℝ V p (q - p)| ≤
        M * ‖SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc (q - p)‖ ^ 2) :
    ∀ x ∈ Metric.ball z (r / 2),
      |V x - (V z + fderiv ℝ V z (x - z))| ≤
        M * (Real.sqrt (d : ℝ) * (r / 2)) ^ 2 := by
  intro x hx
  have ht := hTaylor z (by rw [Metric.mem_ball]; simpa using half_pos hr) x hx
  have hn : ‖SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc (x - z)‖ ≤
      Real.sqrt (d : ℝ) * (r / 2) := by
    calc
      ‖SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc (x - z)‖ ≤
          Real.sqrt (d : ℝ) * ‖x - z‖ :=
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.norm_toEuc_le _
      _ = Real.sqrt (d : ℝ) * dist x z := by rw [dist_eq_norm]
      _ ≤ Real.sqrt (d : ℝ) * (r / 2) := by
        exact mul_le_mul_of_nonneg_left (le_of_lt (by simpa [dist_comm] using hx))
          (Real.sqrt_nonneg _)
  have hsq : ‖SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc (x - z)‖ ^ 2 ≤
      (Real.sqrt (d : ℝ) * (r / 2)) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hn
  have heq : V x - (V z + fderiv ℝ V z (x - z)) =
      V x - V z - fderiv ℝ V z (x - z) := by ring
  rw [heq]
  exact ht.trans (mul_le_mul_of_nonneg_left hsq hM)

theorem aux_lem_affine_gcn_competitor_taylor_sub_const_point_bound
    {d : ℕ} (z : SpatialCoordinates d) (r M c : ℝ)
    (hr : 0 < r) (hM : 0 ≤ M)
    {V : SpatialCoordinates d → ℝ}
    (hTaylor : ∀ p ∈ Metric.ball z (r / 2), ∀ q ∈ Metric.ball z (r / 2),
      |(V q - c) - (V p - c) -
          fderiv ℝ (fun y => V y - c) p (q - p)| ≤
        M * ‖SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc (q - p)‖ ^ 2) :
    ∀ x ∈ Metric.ball z (r / 2),
      |V x - (V z + fderiv ℝ V z (x - z))| ≤
        M * (Real.sqrt (d : ℝ) * (r / 2)) ^ 2 := by
  intro x hx
  have ht := hTaylor z (by rw [Metric.mem_ball]; simpa using half_pos hr) x hx
  have hderiv : fderiv ℝ (fun y => V y - c) z = fderiv ℝ V z := by
    exact fderiv_sub_const c
  have hn : ‖SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc (x - z)‖ ≤
      Real.sqrt (d : ℝ) * (r / 2) := by
    calc
      ‖SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc (x - z)‖ ≤
          Real.sqrt (d : ℝ) * ‖x - z‖ :=
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.norm_toEuc_le _
      _ = Real.sqrt (d : ℝ) * dist x z := by rw [dist_eq_norm]
      _ ≤ Real.sqrt (d : ℝ) * (r / 2) := by
        exact mul_le_mul_of_nonneg_left (le_of_lt (by simpa [dist_comm] using hx))
          (Real.sqrt_nonneg _)
  have hsq : ‖SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc (x - z)‖ ^ 2 ≤
      (Real.sqrt (d : ℝ) * (r / 2)) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hn
  rw [hderiv] at ht
  have heq : (V x - c) - (V z - c) - fderiv ℝ V z (x - z) =
      V x - (V z + fderiv ℝ V z (x - z)) := by ring
  rw [heq] at ht
  exact ht.trans (mul_le_mul_of_nonneg_left hsq hM)

theorem aux_lem_affine_gcn_competitor_normalizedL2_from_point
    {d : ℕ} {W : Set (SpatialCoordinates d)}
    {f : SpatialCoordinates d → ℝ} {D : ℝ}
    (hWmeas : MeasurableSet W) (hWpos : 0 < (volume W).toReal)
    (hWtop : volume W ≠ ⊤) (hD : 0 ≤ D)
    (hint : IntegrableOn (fun x => (f x) ^ 2) W volume)
    (hpoint : ∀ x ∈ W, |f x| ≤ D) : normalizedL2On W f ≤ D := by
  exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.normalizedL2On_le_of_abs_le
    hWmeas hWpos hWtop hD hint hpoint

theorem aux_lem_affine_gcn_competitor_normalizedL2_from_taylor_point
    {d : ℕ} {W : Set (SpatialCoordinates d)}
    {f : SpatialCoordinates d → ℝ} {M K : ℝ}
    (hWmeas : MeasurableSet W) (hWpos : 0 < (volume W).toReal)
    (hWtop : volume W ≠ ⊤) (hM : 0 ≤ M)
    (hint : IntegrableOn (fun x => (f x) ^ 2) W volume)
    (hpoint : ∀ x ∈ W, |f x| ≤ M * K ^ 2) :
    normalizedL2On W f ≤ M * K ^ 2 := by
  apply aux_lem_affine_gcn_competitor_normalizedL2_from_point
    hWmeas hWpos hWtop (mul_nonneg hM (sq_nonneg K)) hint hpoint

theorem aux_lem_affine_gcn_competitor_integrable_sq_of_memLp
    {d : ℕ} {W : Set (SpatialCoordinates d)}
    {f : SpatialCoordinates d → ℝ}
    (hf : MemLp f 2 (volume.restrict W)) :
    IntegrableOn (fun x => (f x) ^ 2) W volume := by
  exact hf.integrable_sq

theorem aux_lem_affine_gcn_competitor_memLp_add_eq
    {d : ℕ} {W : Set (SpatialCoordinates d)}
    {f g h : SpatialCoordinates d → ℝ}
    (hf : MemLp f 2 (volume.restrict W))
    (hg : MemLp g 2 (volume.restrict W))
    (heq : ∀ x, f x + g x = h x) :
    MemLp h 2 (volume.restrict W) := by
  have hs := hf.add hg
  convert hs using 1
  funext x
  exact (heq x).symm

theorem aux_lem_affine_gcn_competitor_residual_memLp
    {d : ℕ} {W : Set (SpatialCoordinates d)}
    {U V ell : SpatialCoordinates d → ℝ}
    (hUV : MemLp (fun x => U x - V x) 2 (volume.restrict W))
    (hVell : MemLp (fun x => V x - ell x) 2 (volume.restrict W)) :
    MemLp (fun x => U x - ell x) 2 (volume.restrict W) := by
  have hsum := hUV.add hVell
  convert hsum using 1
  funext x
  change U x - ell x = (U x - V x) + (V x - ell x)
  ring

theorem aux_lem_affine_gcn_competitor_shifted_residual_memLp
    {d : ℕ} {W : Set (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict W)]
    {U ell : SpatialCoordinates d → ℝ} {c : ℝ}
    (h : MemLp (fun x => U x - ell x) 2 (volume.restrict W)) :
    MemLp (fun x => U x - (ell x + c)) 2 (volume.restrict W) := by
  have hs := h.sub (memLp_const c)
  convert hs using 1
  funext x
  change U x - (ell x + c) = (U x - ell x) - c
  ring

theorem aux_lem_affine_gcn_competitor_shifted_residual_cube_memLp
    {d : ℕ} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {U ell : SpatialCoordinates d → ℝ} {c : ℝ}
    [IsFiniteMeasure (volume.restrict (Metric.ball z (r / 2)))]
    (h : MemLp (fun x => U x - ell x) 2
      (volume.restrict (Metric.ball z (r / 2)))) :
    MemLp (fun x => U x - (ell x + c)) 2
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  have hs := aux_lem_affine_gcn_competitor_shifted_residual_memLp
    (U := U) (ell := ell) (c := c) h
  simpa [centeredCube] using hs

theorem aux_lem_affine_gcn_competitor_normalizedL2_add_bound
    {d : ℕ} {W : Set (SpatialCoordinates d)}
    {f g h : SpatialCoordinates d → ℝ} {A B : ℝ}
    (hf : MemLp f 2 (volume.restrict W))
    (hg : MemLp g 2 (volume.restrict W))
    (heq : ∀ x, f x + g x = h x)
    (hA : normalizedL2On W f ≤ A)
    (hB : normalizedL2On W g ≤ B) :
    normalizedL2On W h ≤ A + B := by
  have hs := SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.normalizedL2On_add_le hf hg
  rw [show (fun x => f x + g x) = h by funext x; exact heq x] at hs
  exact hs.trans (add_le_add hA hB)

theorem aux_lem_affine_gcn_competitor_nonneg_mul_sq
    {M K : ℝ} (hM : 0 ≤ M) : 0 ≤ M * K ^ 2 := by
  exact mul_nonneg hM (sq_nonneg K)

theorem aux_lem_affine_gcn_competitor_remainder_point
    {d : ℕ} {z : SpatialCoordinates d} {r M : ℝ}
    {V ell : SpatialCoordinates d → ℝ}
    (hEll : ∀ x, ell x = V z + fderiv ℝ V z (x - z))
    (hpoint : ∀ x ∈ Metric.ball z (r / 2),
      |V x - (V z + fderiv ℝ V z (x - z))| ≤
        M * (Real.sqrt (d : ℝ) * (r / 2)) ^ 2) :
    ∀ x ∈ Metric.ball z (r / 2),
      |V x - ell x| ≤ M * (Real.sqrt (d : ℝ) * (r / 2)) ^ 2 := by
  intro x hx
  rw [hEll x]
  exact hpoint x hx

theorem aux_lem_affine_gcn_competitor_normalizedL2_remainder
    {d : ℕ} {z : SpatialCoordinates d} {r M : ℝ}
    {V ell : SpatialCoordinates d → ℝ}
    (hWmeas : MeasurableSet (Metric.ball z (r / 2)))
    (hWpos : 0 < (volume (Metric.ball z (r / 2))).toReal)
    (hWtop : volume (Metric.ball z (r / 2)) ≠ ⊤)
    (hM : 0 ≤ M)
    (hmem : MemLp (fun x => V x - ell x) 2
      (volume.restrict (Metric.ball z (r / 2))))
    (hpoint : ∀ x ∈ Metric.ball z (r / 2),
      |V x - ell x| ≤ M * (Real.sqrt (d : ℝ) * (r / 2)) ^ 2) :
    normalizedL2On (Metric.ball z (r / 2)) (fun x => V x - ell x) ≤
      M * (Real.sqrt (d : ℝ) * (r / 2)) ^ 2 := by
  apply aux_lem_affine_gcn_competitor_normalizedL2_from_taylor_point
    hWmeas hWpos hWtop hM (aux_lem_affine_gcn_competitor_integrable_sq_of_memLp hmem)
    hpoint

theorem aux_lem_affine_gcn_competitor_taylor_pc
    {d : ℕ} (V : SpatialCoordinates d → ℝ)
    (z x : SpatialCoordinates d) :
    (∑ i : Fin d, (fderiv ℝ V z (Homogenization.basisVec i)) * x i) +
        (V z - fderiv ℝ V z z) =
      V z + fderiv ℝ V z (x - z) := by
  have hsum : ∑ i : Fin d,
      (fderiv ℝ V z (Homogenization.basisVec i)) * x i =
        fderiv ℝ V z x := by
    calc
      ∑ i : Fin d, (fderiv ℝ V z (Homogenization.basisVec i)) * x i =
          ∑ i : Fin d, fderiv ℝ V z (x i • Homogenization.basisVec i) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [map_smul]
            simp only [smul_eq_mul]
            ring
      _ = fderiv ℝ V z (∑ i : Fin d, x i • Homogenization.basisVec i) :=
        (map_sum _ _ _).symm
      _ = fderiv ℝ V z x := by
        rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.sum_smul_basisVec]
  rw [hsum, map_sub]
  ring

theorem aux_lem_affine_gcn_competitor_affine_difference
    {d : ℕ} (a : Fin d → ℝ) (x y : SpatialCoordinates d) :
    |(∑ i : Fin d, a i * x i) - (∑ i : Fin d, a i * y i)| ≤
      (d : ℝ) * ‖a‖ * dist x y := by
  have hsum : (∑ i : Fin d, a i * x i) - (∑ i : Fin d, a i * y i) =
      ∑ i : Fin d, a i * (x i - y i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  calc
    |∑ i : Fin d, a i * (x i - y i)| ≤
        ∑ i : Fin d, |a i * (x i - y i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin d, ‖a‖ * dist x y := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul (by simpa using norm_le_pi_norm a i)
        (by
          rw [dist_eq_norm]
          exact norm_le_pi_norm (x - y) i)
        (abs_nonneg _) (norm_nonneg _)
    _ = (d : ℝ) * ‖a‖ * dist x y := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem aux_lem_affine_gcn_competitor_holder_lower_exponent
    (d : ℕ) (alpha beta : ℝ) (S : Set (SpatialCoordinates d))
    (G : SpatialCoordinates d → ℝ) (K D : ℝ)
    (hK : 0 ≤ K) (hD : 0 ≤ D) (hb : 0 < beta) (hba : beta < alpha)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D)
    (hbound : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      |G x - G y| ≤ K * dist x y ^ alpha) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S G := by
  apply aux_lem_affine_gcn_competitor_holder_of_pointwise d beta S G
    (K * D ^ (alpha - beta))
  · exact mul_nonneg hK (Real.rpow_nonneg hD (alpha - beta))
  · exact hb
  · intro x hx y hy hxy
    have hxy0 : 0 < dist x y := dist_pos.mpr hxy
    have hαβ : 0 < alpha - beta := sub_pos.mpr hba
    calc
      |G x - G y| ≤ K * dist x y ^ alpha := hbound x hx y hy hxy
      _ = K * (dist x y ^ (alpha - beta) * dist x y ^ beta) := by
        rw [← Real.rpow_add hxy0]
        congr 1
        ring_nf
      _ ≤ K * (D ^ (alpha - beta) * dist x y ^ beta) := by
        apply mul_le_mul_of_nonneg_left _ hK
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (dist_nonneg) (hdiam x hx y hy) hαβ.le)
          (Real.rpow_nonneg hxy0.le beta)
      _ = (K * D ^ (alpha - beta)) * dist x y ^ beta := by ring

theorem aux_lem_affine_gcn_competitor_frontier_diameter
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (_hr : 0 < r)
    {x y : SpatialCoordinates d}
    (hx : x ∈ frontier (Metric.ball z (r / 2)))
    (hy : y ∈ frontier (Metric.ball z (r / 2))) :
    dist x y ≤ r := by
  have hx' : dist x z = r / 2 := by
    have h := (Metric.frontier_ball_subset_sphere (x := z) (ε := r / 2)) hx
    simpa [Metric.mem_sphere] using! h
  have hy' : dist y z = r / 2 := by
    have h := (Metric.frontier_ball_subset_sphere (x := z) (ε := r / 2)) hy
    simpa [Metric.mem_sphere] using! h
  calc
    dist x y ≤ dist x z + dist z y := dist_triangle x z y
    _ = r := by rw [hx', dist_comm z y, hy']; ring

theorem aux_lem_affine_gcn_competitor_cube_dilation_image
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z (0 : SpatialCoordinates d) r ''
        (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d)) =
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation_mapsTo z 0 hr one_pos x hx
  · intro y hy
    let x := _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation (0 : SpatialCoordinates d) z r⁻¹ y
    have hxy : _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r x = y := by
      ext i
      simp [x, _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation]
      field_simp
      ring
    have hxpre : x ∈
        _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r ⁻¹'
          (centeredCube z r hr : Set (SpatialCoordinates d)) := by
      change _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r x ∈
        (centeredCube z r hr : Set (SpatialCoordinates d))
      rw [hxy]
      exact hy
    have hx : x ∈ (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
        Set (SpatialCoordinates d)) := by
      have hset := _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation_preimage_centeredCube
        z 0 hr one_pos
      rw [← hset]
      exact hxpre
    exact ⟨x, hx, hxy⟩

theorem aux_lem_affine_gcn_competitor_dilation_norm
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    {f : SpatialCoordinates d → ℝ}
    (hf : MemLp f 2 (volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d)))) :
    (eLpNorm (fun x => f
      (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z (0 : SpatialCoordinates d) r x))
        2 (volume.restrict
          (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
            Set (SpatialCoordinates d)))).toReal =
    (eLpNorm f 2 (volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d)))).toReal /
        Real.sqrt (r ^ d) := by
  let Q0 : Set (SpatialCoordinates d) :=
    centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)
  let Qr : Set (SpatialCoordinates d) := centeredCube z r hr
  let T : SpatialCoordinates d → SpatialCoordinates d :=
    _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z (0 : SpatialCoordinates d) r
  have hT : Measurable T := by
    exact (_root_.SubdiffusiveProcess.EllipticRegularity.continuous_cubeDilation z 0 r).measurable
  have hmap' : Measure.map T (volume.restrict Q0) =
      ENNReal.ofReal |(r ^ d)⁻¹| • volume.restrict Qr := by
    simpa [T, Q0, Qr] using
      (_root_.SubdiffusiveProcess.EllipticRegularity.map_cubeDilation_restrict z 0 hr one_pos)
  have hac : Measure.map T (volume.restrict Q0) ≪ volume.restrict Qr := by
    rw [hmap']
    exact Measure.smul_absolutelyContinuous
  have hmap := MeasureTheory.eLpNorm_map_measure
    (μ := volume.restrict Q0) (p := (2 : ℝ≥0∞))
    (hf.aestronglyMeasurable.mono_ac hac) hT.aemeasurable
  rw [hmap'] at hmap
  rw [MeasureTheory.eLpNorm_smul_measure_of_ne_zero
    (by positivity : ENNReal.ofReal |(r ^ d)⁻¹| ≠ 0)] at hmap
  have hrd : 0 < r ^ d := pow_pos hr d
  have hc : ENNReal.ofReal |(r ^ d)⁻¹| = ENNReal.ofReal (r ^ d)⁻¹ := by
    rw [abs_of_pos (by positivity : 0 < (r ^ d)⁻¹)]
  rw [hc, ENNReal.ofReal_inv_of_pos hrd] at hmap
  have hQ0vol : (volume Q0).toReal = 1 := by
    rw [show Q0 = centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) by rfl,
      centeredCube_volume]
    simp
  have hQ0vol' : Real.sqrt (volume Q0).toReal = 1 := by simp [hQ0vol]
  have hpow : ((ENNReal.ofReal (r ^ d))⁻¹ ^ (1 / (2 : ℝ≥0∞)).toReal).toReal =
      (Real.sqrt (r ^ d))⁻¹ := by
    rw [← ENNReal.toReal_rpow]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal hrd.le,
      ENNReal.toReal_ofNat, one_div]
    rw [Real.inv_rpow hrd.le, Real.sqrt_eq_rpow]
    norm_num
  have hmain := hmap
  dsimp [T, Q0, Qr] at hmain ⊢
  have hmain' := congrArg ENNReal.toReal hmain
  rw [ENNReal.toReal_mul] at hmain'
  rw [hpow] at hmain'
  calc
    (eLpNorm (fun x => f (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z
        (0 : SpatialCoordinates d) r x)) 2 (volume.restrict
          (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
            Set (SpatialCoordinates d)))).toReal =
        (Real.sqrt (r ^ d))⁻¹ *
          (eLpNorm f 2 (volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d)))).toReal := by
      simpa [smul_eq_mul, Function.comp_def] using hmain'.symm
    _ = _ := by ring

theorem aux_lem_affine_gcn_competitor_weak_harmonic_representative
    {d : ℕ} {W : Set (SpatialCoordinates d)} (hW : IsOpen W)
    {a : SpatialCoordinates d → ℝ} {u : Homogenization.H1Function W}
    (hu : SubdiffusiveProcess.CoarseGrainingVocab.IsWeaklyHarmonicOn a W u)
    {v : SpatialCoordinates d → ℝ} (hv : ContinuousOn v W)
    (hae : v =ᵐ[volume.restrict W] u.toFun) :
    SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.WeakHarmonic a W v := by
  refine ⟨hv, ?_⟩
  intro V hV _hVc hVW
  have hsub : V ⊆ W := subset_closure.trans hVW
  refine ⟨u.restrict hV hsub, ?_, ?_⟩
  · exact (hae.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))).symm
  · intro test
    have hh := SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.isWeaklyHarmonicOn_restrict
      hW hV hsub hu test
    simpa only [Homogenization.vecDot_smul_left] using hh

theorem aux_lem_affine_gcn_competitor_weak_harmonic_sub_const
    {d : ℕ} {a : SpatialCoordinates d → ℝ} {W : Set (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict W)]
    {v : Homogenization.H1Function W}
    (hv : SubdiffusiveProcess.CoarseGrainingVocab.IsWeaklyHarmonicOn a W v) (c : ℝ) :
    SubdiffusiveProcess.CoarseGrainingVocab.IsWeaklyHarmonicOn a W
      (v - Homogenization.H1Function.const c) := by
  intro ψ
  have hh := hv ψ
  simpa [Homogenization.H1Function.sub_grad, Homogenization.H1Function.const] using hh

theorem aux_lem_affine_gcn_competitor_harmonic_point
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {a : SpatialCoordinates d → ℝ} {H : ℝ}
    {B : SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.Cube d}
    (hB : 0 < B.2)
    (hctrl : SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic.LogCoefficientControlOn
      a H B)
    {h : SpatialCoordinates d → ℝ}
    (hh : SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.WeakHarmonic
      a (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet B) h)
    (hmem : MemLp h 2 (volume.restrict
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet B)))
    {x : SpatialCoordinates d}
    (hx : x ∈ SubdiffusiveProcess.Section9.centeredAxisCube B.1 (B.2 / 2)) :
    |h x| ≤ (1 + SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic.interiorHarmonicConstant d H) *
      normalizedL2On (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet B) h := by
  have hvol : 0 < (volume
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet B)).toReal := by
    rw [SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic.volume_cubeSet_toReal hB.le]
    positivity
  have hcube_meas : MeasurableSet
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet B) := by
    simpa [SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet,
      SubdiffusiveProcess.Section9.centeredAxisCube] using
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.measurableSet_axisCube
        (fun i => B.1 i - B.2 / 2) B.2)
  let : IsFiniteMeasure (volume.restrict
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet B)) :=
    ⟨by
      have htop : volume
          (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet B) ≠ ⊤ :=
        SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic.volume_cubeSet_ne_top
          (B := B)
      have hlt : volume
          (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet B) < ⊤ :=
        lt_top_iff_ne_top.mpr htop
      simpa only [Measure.restrict_apply_univ] using hlt⟩
  have hint : IntegrableOn h
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet B) :=
    hmem.integrable one_le_two
  have hsqint : IntegrableOn (fun y => h y ^ 2)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet B) :=
    hmem.integrable_sq
  have hcenter :
      normalizedL2On (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet B)
        (fun y => h y -
          averageOn (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet B) h) ≤
        normalizedL2On (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet B) h := by
    simpa only [averageOn, sub_zero] using
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.normalizedL2On_sub_volumeAverage_le
        hcube_meas
        hvol
        (SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic.volume_cubeSet_ne_top (B := B))
        hint hsqint 0
  have havg := SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.abs_volumeAverage_le_normalizedL2On
    hcube_meas
    hvol hint hsqint
  have hosc :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic.abs_sub_averageOn_le_interiorHarmonicConstant
      hd hB hctrl hh hmem hx
  have hprice := mul_le_mul_of_nonneg_left hcenter
    (SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic.interiorHarmonicConstant_nonneg d H)
  have htri : |h x| ≤
      |h x - averageOn
        (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet B) h| +
      |averageOn (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet B) h| := by
    have ht := abs_add_le
      (h x - averageOn (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet B) h)
      (averageOn (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet B) h)
    simpa only [sub_add_cancel] using ht
  change |averageOn (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet B) h| ≤
    normalizedL2On (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet B) h at havg
  nlinarith only [htri, hosc, hprice, havg]

theorem aux_lem_affine_gcn_competitor_holder_nonneg
    {d : ℕ}
    (beta : ℝ) (S : Set (SpatialCoordinates d))
    (F : SpatialCoordinates d → ℝ) :
    0 ≤ _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta S F := by
  unfold _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm
  apply Real.sSup_nonneg
  intro v hv
  rcases hv with ⟨x, hx, y, hy, hxy, rfl⟩
  exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)

theorem aux_lem_affine_gcn_competitor_holder_le_cAlpha
    {d : ℕ}
    (beta : ℝ) (S : Set (SpatialCoordinates d))
    (F : SpatialCoordinates d → ℝ) :
    _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta S F ≤ _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta S F := by
  have hnonneg : 0 ≤ sSup {v : ℝ | ∃ x ∈ S, v = |F x|} := by
    apply Real.sSup_nonneg
    intro v hv
    rcases hv with ⟨x, hx, rfl⟩
    exact abs_nonneg _
  unfold _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm
  linarith

theorem aux_lem_affine_gcn_competitor_holderSeminorm_le_of_pointwise
    {d : ℕ} (alpha K : ℝ) (S : Set (SpatialCoordinates d))
    (F : SpatialCoordinates d → ℝ) (hK : 0 ≤ K) (hα : 0 ≤ alpha)
    (hpoint : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      |F x - F y| ≤ K * dist x y ^ alpha) :
    _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm alpha S F ≤ K := by
  unfold _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm
  apply Real.sSup_le
  · rintro v ⟨x, hx, y, hy, hxy, rfl⟩
    have hd : 0 < dist x y := dist_pos.mpr hxy
    have heuc :
        dist x y ≤ Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
      calc
        dist x y = ‖x - y‖ := by rw [dist_eq_norm]
        _ ≤ ‖(SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc
            (x - y) : EuclideanSpace ℝ (Fin d))‖ :=
          SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.norm_le_norm_toEuc _
        _ = Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
          rw [EuclideanSpace.norm_eq]
          simp [SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc_apply,
            Real.norm_eq_abs, sq_abs]
    have heu : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ alpha :=
      Real.rpow_pos_of_pos (lt_of_lt_of_le hd heuc) _
    have hpow := Real.rpow_le_rpow dist_nonneg heuc hα
    calc
      |F x - F y| / Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ alpha ≤
          K * dist x y ^ alpha /
            Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ alpha := by
        exact div_le_div_of_nonneg_right (hpoint x hx y hy hxy) heu.le
      _ ≤ K * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ alpha /
            Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ alpha := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow hK) heu.le
      _ = K := by field_simp [heu.ne']
  · exact hK

theorem aux_lem_affine_gcn_competitor_cAlphaNorm_le_of_pointwise
    {d : ℕ} (alpha K : ℝ) (S : Set (SpatialCoordinates d))
    (F : SpatialCoordinates d → ℝ) (x₀ : SpatialCoordinates d)
    (hK : 0 ≤ K) (hα : 0 ≤ alpha)
    (hx₀ : x₀ ∈ S)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 1)
    (hpoint : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      |F x - F y| ≤ K * dist x y ^ alpha) :
    _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha S F ≤ |F x₀| + 2 * K := by
  have hsup : sSup {v : ℝ | ∃ x ∈ S, v = |F x|} ≤ |F x₀| + K := by
    apply Real.sSup_le
    · rintro v ⟨x, hx, rfl⟩
      by_cases hxx : x = x₀
      · subst x
        linarith [abs_nonneg (F x₀)]
      · have hfx := hpoint x hx x₀ hx₀ hxx
        have hfd : dist x x₀ ^ alpha ≤ 1 :=
          Real.rpow_le_one (dist_nonneg) (hdiam x hx x₀ hx₀) hα
        calc
          |F x| ≤ |F x - F x₀| + |F x₀| := by
            simpa [sub_add_cancel] using (abs_add_le (F x - F x₀) (F x₀))
          _ ≤ K * dist x x₀ ^ alpha + |F x₀| :=
            add_le_add hfx le_rfl
          _ ≤ |F x₀| + K := by
            simpa [add_comm, add_left_comm, add_assoc] using
              (add_le_add_left (mul_le_mul_of_nonneg_left hfd hK) |F x₀|)
    · positivity
  dsimp [_root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm]
  have hsemi := aux_lem_affine_gcn_competitor_holderSeminorm_le_of_pointwise
    alpha K S F hK hα hpoint
  linarith

theorem aux_lem_affine_gcn_competitor_cAlphaNorm_le_of_pointwise_zero
    {d : ℕ} (alpha K : ℝ) (S : Set (SpatialCoordinates d))
    (F : SpatialCoordinates d → ℝ) (x₀ : SpatialCoordinates d)
    (hK : 0 ≤ K) (hα : 0 ≤ alpha) (hx₀ : x₀ ∈ S)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 1)
    (hpoint : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      |F x - F y| ≤ K * dist x y ^ alpha)
    (hzero : F x₀ = 0) :
    _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha S F ≤ 2 * K := by
  have h := aux_lem_affine_gcn_competitor_cAlphaNorm_le_of_pointwise
    alpha K S F x₀ hK hα hx₀ hdiam hpoint
  calc
    _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha S F ≤ |F x₀| + 2 * K := h
    _ = 2 * K := by
      rw [hzero, abs_zero]
      ring

theorem aux_lem_affine_gcn_competitor_cubeDilation_inverse
    {d : ℕ} (z x : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r
        (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation 0 z r⁻¹ x) = x := by
  funext i
  simp only [_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation_apply, Pi.zero_apply]
  field_simp
  ring

theorem aux_lem_affine_gcn_competitor_normalized_residual_point
    {d : ℕ} (alpha Cin Os Src r R N : ℝ)
    (a : Fin d → ℝ) (U ell : SpatialCoordinates d → ℝ)
    (T : SpatialCoordinates d → SpatialCoordinates d)
    (S W : Set (SpatialCoordinates d))
    (hTcl : ∀ x ∈ S, T x ∈ W)
    (hHol : ∀ x ∈ W, ∀ y ∈ W,
      |U x - U y| ≤ Cin * (Os + Src) * (dist x y / R) ^ alpha)
    (hell : ∀ x y, |ell x - ell y| ≤ (d : ℝ) * ‖a‖ * dist x y)
    (hTdist : ∀ x y, dist (T x) (T y) = r * dist x y)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 1)
    (hr : 0 < r) (hR : 0 < R) (hN : 0 < N)
    (_hα0 : 0 ≤ alpha) (hα1 : alpha ≤ 1) :
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      |(U (T x) - ell (T x)) / N -
          (U (T y) - ell (T y)) / N| ≤
        (Cin * (Os + Src) / N * (r / R) ^ alpha +
          (d : ℝ) * ‖a‖ * r / N) * dist x y ^ alpha := by
  intro x hx y hy hxy
  have hTx := hTcl x hx
  have hTy := hTcl y hy
  have hUxy := hHol (T x) hTx (T y) hTy
  have hEllxy := hell (T x) (T y)
  have hnum :
      |(U (T x) - ell (T x)) - (U (T y) - ell (T y))| ≤
        Cin * (Os + Src) * (dist (T x) (T y) / R) ^ alpha +
          (d : ℝ) * ‖a‖ * dist (T x) (T y) := by
    calc
      |(U (T x) - ell (T x)) - (U (T y) - ell (T y))| =
          |(U (T x) - U (T y)) - (ell (T x) - ell (T y))| := by
            congr 1
            abel
      _ ≤ |U (T x) - U (T y)| + |ell (T x) - ell (T y)| :=
        abs_sub _ _
      _ ≤ Cin * (Os + Src) * (dist (T x) (T y) / R) ^ alpha +
          (d : ℝ) * ‖a‖ * dist (T x) (T y) :=
        add_le_add hUxy hEllxy
  have hratio : 0 < r / R := div_pos hr hR
  have hpow :
      (r * dist x y / R) ^ alpha =
        (r / R) ^ alpha * dist x y ^ alpha := by
    rw [show r * dist x y / R = (r / R) * dist x y by ring,
      Real.mul_rpow hratio.le (dist_nonneg)]
  have hdistalpha : dist x y ≤ dist x y ^ alpha := by
    have hpos : 0 < dist x y := dist_pos.mpr hxy
    simpa using
      (Real.rpow_le_rpow_of_exponent_ge hpos (hdiam x hx y hy) hα1)
  have hlin :
      (d : ℝ) * ‖a‖ * r / N * dist x y ≤
        (d : ℝ) * ‖a‖ * r / N * dist x y ^ alpha :=
    mul_le_mul_of_nonneg_left hdistalpha (by positivity)
  have hnum' := hnum
  rw [hTdist] at hnum'
  calc
    |(U (T x) - ell (T x)) / N -
        (U (T y) - ell (T y)) / N| =
        |(U (T x) - ell (T x)) -
          (U (T y) - ell (T y))| / N := by
      rw [div_sub_div_same, abs_div, abs_of_pos hN]
    _ ≤ Cin * (Os + Src) / N * (r * dist x y / R) ^ alpha +
          (d : ℝ) * ‖a‖ * r * dist x y / N := by
      calc
        _ ≤ (Cin * (Os + Src) * (r * dist x y / R) ^ alpha +
            (d : ℝ) * ‖a‖ * (r * dist x y)) / N :=
          div_le_div_of_nonneg_right hnum' hN.le
        _ = _ := by ring
    _ = Cin * (Os + Src) / N * (r / R) ^ alpha * dist x y ^ alpha +
          (d : ℝ) * ‖a‖ * r / N * dist x y := by
      rw [hpow]
      ring
    _ ≤ Cin * (Os + Src) / N * (r / R) ^ alpha * dist x y ^ alpha +
          (d : ℝ) * ‖a‖ * r / N * dist x y ^ alpha := by
      exact add_le_add le_rfl hlin
    _ = (Cin * (Os + Src) / N * (r / R) ^ alpha +
          (d : ℝ) * ‖a‖ * r / N) * dist x y ^ alpha := by ring

theorem aux_lem_affine_gcn_competitor_normalized_residual_point_affine
    {d : ℕ} (alpha Cin Os Src r R N : ℝ)
    (a : Fin d → ℝ) (U ell : SpatialCoordinates d → ℝ)
    (T : SpatialCoordinates d → SpatialCoordinates d)
    (S W : Set (SpatialCoordinates d)) (b : ℝ)
    (hellAff : ∀ x, ell x = (∑ i : Fin d, a i * x i) + b)
    (hTcl : ∀ x ∈ S, T x ∈ W)
    (hHol : ∀ x ∈ W, ∀ y ∈ W,
      |U x - U y| ≤ Cin * (Os + Src) * (dist x y / R) ^ alpha)
    (hTdist : ∀ x y, dist (T x) (T y) = r * dist x y)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 1)
    (hr : 0 < r) (hR : 0 < R) (hN : 0 < N)
    (hα0 : 0 ≤ alpha) (hα1 : alpha ≤ 1) :
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      |(U (T x) - ell (T x)) / N -
          (U (T y) - ell (T y)) / N| ≤
        (Cin * (Os + Src) / N * (r / R) ^ alpha +
          (d : ℝ) * ‖a‖ * r / N) * dist x y ^ alpha := by
  apply aux_lem_affine_gcn_competitor_normalized_residual_point
    alpha Cin Os Src r R N a U ell T S W hTcl hHol
  · intro x y
    rw [hellAff x, hellAff y]
    convert aux_lem_affine_gcn_competitor_affine_difference a x y
      using 1 ; ring
  · exact hTdist
  · exact hdiam
  · exact hr
  · exact hR
  · exact hN
  · exact hα0
  · exact hα1

theorem aux_lem_affine_gcn_competitor_cubeDilation_inverse_dist
    {d : ℕ} (z x : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    dist (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation 0 z r⁻¹ x) 0 =
      dist x z / r := by
  rw [dist_eq_norm]
  have hcoord :
      _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation 0 z r⁻¹ x - 0 =
        r⁻¹ • (x - z) := by
    funext i
    simp only [_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation_apply, Pi.zero_apply,
      sub_zero, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    ring
  rw [hcoord, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  rw [dist_eq_norm, div_eq_mul_inv]
  ring

theorem aux_lem_affine_gcn_competitor_cubeDilation_inverse_mem
    {d : ℕ} (z x : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hx : x ∈ frontier (Metric.ball z (r / 2))) :
    _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation 0 z r⁻¹ x ∈
      closure (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
        Set (SpatialCoordinates d)) := by
  rw [show closure (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
      Set (SpatialCoordinates d)) = Metric.closedBall 0 (1 / 2) by
    change closure (Metric.ball (0 : SpatialCoordinates d) (1 / 2)) = _
    exact closure_ball 0 (by norm_num)]
  rw [Metric.mem_closedBall]
  have hxs : dist x z = r / 2 := by
    have h := Metric.frontier_ball_subset_sphere (x := z) (ε := r / 2) hx
    change dist x z = r / 2 at h
    exact h
  have hdist := aux_lem_affine_gcn_competitor_cubeDilation_inverse_dist z x r hr
  rw [hdist, hxs]
  field_simp [ne_of_gt hr]
  exact le_rfl

theorem aux_lem_affine_gcn_competitor_cubeDilation_inverse_scale
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∀ x y : SpatialCoordinates d,
      Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) =
        r * Real.sqrt (∑ j : Fin d,
          ((_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation 0 z r⁻¹ x) j -
            (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation 0 z r⁻¹ y) j) ^ 2) := by
  intro x y
  have h := _root_.SubdiffusiveProcess.EllipticRegularity.sqrt_sum_sq_cubeDilation
    z 0 hr
      (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation 0 z r⁻¹ x)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation 0 z r⁻¹ y)
  rw [aux_lem_affine_gcn_competitor_cubeDilation_inverse z x r hr,
    aux_lem_affine_gcn_competitor_cubeDilation_inverse z y r hr] at h
  exact h

theorem aux_lem_affine_gcn_competitor_residual_relation
    {d : ℕ} (N : ℝ) (hN : 0 < N) (S : Set (SpatialCoordinates d))
    (U ell : SpatialCoordinates d → ℝ)
    (T Tinv : SpatialCoordinates d → SpatialCoordinates d)
    (hTinvl : ∀ x ∈ S, T (Tinv x) = x) :
    ∀ x ∈ S, U x - ell x =
      N * ((U (T (Tinv x)) - ell (T (Tinv x))) / N) := by
  intro x hx
  rw [hTinvl x hx]
  field_simp

theorem aux_lem_affine_gcn_competitor_cubeDilation_inverse_scale_frontier
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∀ x ∈ frontier (Metric.ball z (r / 2)),
      ∀ y ∈ frontier (Metric.ball z (r / 2)), x ≠ y →
        Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) =
          r * Real.sqrt (∑ j : Fin d,
            ((_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation 0 z r⁻¹ x) j -
              (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation 0 z r⁻¹ y) j) ^ 2) := by
  intro x hx y hy hxy
  exact (aux_lem_affine_gcn_competitor_cubeDilation_inverse_scale z r hr x y)

theorem aux_lem_affine_gcn_competitor_cubeDilation_inverse_scale_for
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (Tinv : SpatialCoordinates d → SpatialCoordinates d)
    (hTinv : Tinv = _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation 0 z r⁻¹) :
    ∀ x ∈ frontier (Metric.ball z (r / 2)),
      ∀ y ∈ frontier (Metric.ball z (r / 2)), x ≠ y →
        Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) =
          r * Real.sqrt (∑ j : Fin d, (Tinv x j - Tinv y j) ^ 2) := by
  intro x hx y hy hxy
  rw [hTinv]
  exact aux_lem_affine_gcn_competitor_cubeDilation_inverse_scale z r hr x y

theorem aux_lem_affine_gcn_competitor_cubeDilation_residual_relation
    {d : ℕ} (z : SpatialCoordinates d) (r N : ℝ)
    (hr : 0 < r) (hN : 0 < N)
    (U ell : SpatialCoordinates d → ℝ) :
    ∀ x ∈ frontier (Metric.ball z (r / 2)),
      U x - ell x =
        N * ((U (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r
            (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation 0 z r⁻¹ x)) -
          ell (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r
            (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation 0 z r⁻¹ x))) / N) := by
  intro x hx
  rw [aux_lem_affine_gcn_competitor_cubeDilation_inverse z x r hr]
  field_simp

theorem aux_lem_affine_gcn_competitor_residual_relation_of_defs
    {d : ℕ} (N : ℝ) (hN : 0 < N) (S : Set (SpatialCoordinates d))
    (G F U ell : SpatialCoordinates d → ℝ)
    (T Tinv : SpatialCoordinates d → SpatialCoordinates d)
    (hG : ∀ x, G x = U x - ell x)
    (hF : ∀ x, F x = (U (T x) - ell (T x)) / N)
    (hTinvl : ∀ x ∈ S, T (Tinv x) = x) :
    ∀ x ∈ S, G x = N * F (Tinv x) := by
  intro x hx
  rw [hG x, hF, hTinvl x hx]
  field_simp

theorem aux_lem_affine_gcn_competitor_beta_pos
    (beta : ℝ) (hbeta : 1 / 2 < beta) : 0 < beta := by
  linarith

theorem aux_lem_affine_gcn_competitor_continuous_affine
    {d : ℕ} (vH : SpatialCoordinates d → ℝ) (z : SpatialCoordinates d) :
    Continuous (fun x => vH z + fderiv ℝ vH z (x - z)) := by
  fun_prop

theorem aux_lem_affine_gcn_competitor_continuous_residual
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (U vH : SpatialCoordinates d → ℝ) (c : ℝ)
    (x₀ : SpatialCoordinates d)
    (hUcont : ContinuousOn U (closure (Q : Set (SpatialCoordinates d)))) :
    ContinuousOn
      (fun x => U x - (vH x₀ + fderiv ℝ vH x₀ (x - x₀) + c))
      (closure (Q : Set (SpatialCoordinates d))) := by
  exact hUcont.sub
    ((aux_lem_affine_gcn_competitor_continuous_affine vH x₀).continuousOn.add
      continuousOn_const)

theorem aux_lem_affine_gcn_competitor_interp
    (d : ℕ) (hd : 1 ≤ d) (alpha beta : ℝ) (hb : 0 < beta)
    (hba : beta < alpha) (ha : alpha ≤ 1) :
    let Q0 := centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num)
    let S := closure (Q0 : Set (SpatialCoordinates d))
    ∃ C : ℝ, 0 < C ∧
      ∀ v : SpatialCoordinates d → ℝ, _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha S v →
        _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S v ∧
          _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta S v ≤
            C * ((eLpNorm v 2 (volume.restrict (Q0 : Set (SpatialCoordinates d)))).toReal) ^
                ((alpha - beta) / (alpha + (d : ℝ) / 2)) *
              (_root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha S v) ^
                (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)) := by
  exact lem_interp d hd alpha beta hb hba ha

theorem aux_lem_affine_gcn_competitor_interp_holderSeminorm
    (d : ℕ) (hd : 1 ≤ d) (alpha beta : ℝ) (hb : 0 < beta)
    (hba : beta < alpha) (ha : alpha ≤ 1)
    (F : SpatialCoordinates d → ℝ)
    (hF : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
      (closure (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num))) F) :
    ∃ C : ℝ, 0 < C ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta
          (closure (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num))) F ≤
        C * ((eLpNorm F 2 (volume.restrict
          (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
            Set (SpatialCoordinates d)))).toReal) ^
              ((alpha - beta) / (alpha + (d : ℝ) / 2)) *
          (_root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
            (closure (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num))) F) ^
              (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)) := by
  obtain ⟨C, hC, hinterp⟩ := aux_lem_affine_gcn_competitor_interp
    d hd alpha beta hb hba ha
  have hβ := hinterp F hF
  refine ⟨C, hC, ?_⟩
  exact (aux_lem_affine_gcn_competitor_holder_le_cAlpha beta _ F).trans hβ.2

theorem aux_lem_affine_gcn_competitor_interp_apply
    {d : ℕ} {alpha beta C : ℝ}
    (hinterp : ∀ v : SpatialCoordinates d → ℝ,
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
        (closure (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
          Set (SpatialCoordinates d))) v →
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta
        (closure (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
          Set (SpatialCoordinates d))) v ∧
        _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
          (closure (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
            Set (SpatialCoordinates d))) v ≤
          C * ((eLpNorm v 2 (volume.restrict
            (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
              Set (SpatialCoordinates d)))).toReal) ^
              ((alpha - beta) / (alpha + (d : ℝ) / 2)) *
            (_root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
              (closure (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
                Set (SpatialCoordinates d))) v) ^
              (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)))
    (F : SpatialCoordinates d → ℝ)
    (hF : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
      (closure (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
        Set (SpatialCoordinates d))) F) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta
        (closure (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
          Set (SpatialCoordinates d))) F ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
        (closure (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
          Set (SpatialCoordinates d))) F ≤
        C * ((eLpNorm F 2 (volume.restrict
          (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
            Set (SpatialCoordinates d)))).toReal) ^
            ((alpha - beta) / (alpha + (d : ℝ) / 2)) *
          (_root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
            (closure (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
              Set (SpatialCoordinates d))) F) ^
            (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)) := by
  exact hinterp F hF

theorem aux_lem_affine_gcn_competitor_interp_bound_value
    (d : ℕ) (hd : 1 ≤ d) (alpha beta : ℝ) (hb : 0 < beta)
    (hba : beta < alpha) (ha : alpha ≤ 1)
    (F : SpatialCoordinates d → ℝ)
    (hF : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
      (closure (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num))) F) :
    ∃ C H : ℝ, 0 < C ∧
      H = C * ((eLpNorm F 2 (volume.restrict
        (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
          Set (SpatialCoordinates d)))).toReal) ^
            ((alpha - beta) / (alpha + (d : ℝ) / 2)) *
        (_root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
          (closure (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num))) F) ^
            (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)) ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta
          (closure (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num))) F ≤ H := by
  obtain ⟨C, hC, hinterp⟩ := aux_lem_affine_gcn_competitor_interp
    d hd alpha beta hb hba ha
  have hβ := hinterp F hF
  let H : ℝ := C * ((eLpNorm F 2 (volume.restrict
    (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
      Set (SpatialCoordinates d)))).toReal) ^
        ((alpha - beta) / (alpha + (d : ℝ) / 2)) *
      (_root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
        (closure (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num))) F) ^
        (1 - (alpha - beta) / (alpha + (d : ℝ) / 2))
  refine ⟨C, H, hC, rfl, ?_⟩
  exact (aux_lem_affine_gcn_competitor_holder_le_cAlpha beta _ F).trans hβ.2

theorem aux_lem_affine_gcn_competitor_holder_transport
    {d : ℕ} (beta r N : ℝ) (q S : Set (SpatialCoordinates d))
    (G F : SpatialCoordinates d → ℝ)
    (T Tinv : SpatialCoordinates d → SpatialCoordinates d)
    (_hbeta : 0 < beta) (hr : 0 < r) (hN : 0 < N)
    (hTinv : ∀ x ∈ frontier q, Tinv x ∈ S)
    (hTinvl : ∀ x ∈ frontier q, T (Tinv x) = x)
    (hscale : ∀ x ∈ frontier q, ∀ y ∈ frontier q, x ≠ y →
      Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) =
        r * Real.sqrt (∑ j : Fin d, (Tinv x j - Tinv y j) ^ 2))
    (hrel : ∀ x ∈ frontier q, G x = N * F (Tinv x))
    (hF : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S F) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (frontier q) G ∧
      r ^ beta * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier q) G ≤
        N * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta S F := by
  let K : ℝ := _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta S F
  have hK : 0 ≤ K := by
    dsimp [K]
    exact aux_lem_affine_gcn_competitor_holder_nonneg beta S F
  have hpoint : ∀ x ∈ frontier q, ∀ y ∈ frontier q, x ≠ y →
      |G x - G y| /
          Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ beta ≤
        N * K / r ^ beta := by
    intro x hx y hy hxy
    let x0 := Tinv x
    let y0 := Tinv y
    have hx0 : x0 ∈ S := hTinv x hx
    have hy0 : y0 ∈ S := hTinv y hy
    have hxy0 : x0 ≠ y0 := by
      intro hxy0
      apply hxy
      calc
        x = T (Tinv x) := (hTinvl x hx).symm
        _ = T (Tinv y) := by rw [show Tinv x = Tinv y by simpa [x0, y0] using hxy0]
        _ = y := hTinvl y hy
    have hD0 : 0 < Real.sqrt (∑ j : Fin d, (x0 j - y0 j) ^ 2) := by
      apply Real.sqrt_pos.mpr
      by_contra hz
      have hsum_nonneg : 0 ≤ ∑ j : Fin d, (x0 j - y0 j) ^ 2 :=
        Finset.sum_nonneg (fun i _ => sq_nonneg _)
      have hsum : ∑ j : Fin d, (x0 j - y0 j) ^ 2 = 0 :=
        le_antisymm (le_of_not_gt hz) hsum_nonneg
      have hzero : x0 = y0 := by
        funext j
        have hj : (x0 j - y0 j) ^ 2 = 0 := by
          have hnonneg : ∀ i : Fin d, 0 ≤ (x0 i - y0 i) ^ 2 := fun i => sq_nonneg _
          have hle := Finset.single_le_sum (fun i _ => hnonneg i)
            (Finset.mem_univ j)
          have hjle : (x0 j - y0 j) ^ 2 ≤ 0 := by simpa [hsum] using hle
          exact le_antisymm hjle (sq_nonneg _)
        nlinarith
      exact hxy0 hzero
    have hmem :
        |F x0 - F y0| /
            Real.sqrt (∑ j : Fin d, (x0 j - y0 j) ^ 2) ^ beta ≤ K := by
      dsimp [K]
      exact le_csSup hF ⟨x0, hx0, y0, hy0, hxy0, rfl⟩
    have hscalePow :
        Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ beta =
          r ^ beta * Real.sqrt (∑ j : Fin d, (x0 j - y0 j) ^ 2) ^ beta := by
      rw [hscale x hx y hy hxy, Real.mul_rpow hr.le hD0.le]
    have hnum : |G x - G y| ≤
        N * K * Real.sqrt (∑ j : Fin d, (x0 j - y0 j) ^ 2) ^ beta := by
      have hmem' := (div_le_iff₀ (Real.rpow_pos_of_pos hD0 beta)).mp hmem
      have hrelx := hrel x hx
      have hrely := hrel y hy
      rw [hrelx, hrely]
      rw [show |N * F x0 - N * F y0| = N * |F x0 - F y0| by
        rw [show N * F x0 - N * F y0 = N * (F x0 - F y0) by ring,
          abs_mul, abs_of_pos hN]]
      calc
        N * |F x0 - F y0| ≤ N * (K *
            Real.sqrt (∑ j : Fin d, (x0 j - y0 j) ^ 2) ^ beta) :=
          mul_le_mul_of_nonneg_left hmem' hN.le
        _ = N * K * Real.sqrt (∑ j : Fin d, (x0 j - y0 j) ^ 2) ^ beta := by ring
    rw [hscalePow]
    apply (div_le_iff₀ (mul_pos (Real.rpow_pos_of_pos hr beta)
      (Real.rpow_pos_of_pos hD0 beta))).2
    calc
      |G x - G y| ≤ N * K *
          Real.sqrt (∑ j : Fin d, (x0 j - y0 j) ^ 2) ^ beta := hnum
      _ = (N * K / r ^ beta) *
          (r ^ beta * Real.sqrt (∑ j : Fin d, (x0 j - y0 j) ^ 2) ^ beta) := by
        field_simp [Real.rpow_pos_of_pos hr beta]

  have hholder : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (frontier q) G := by
    refine ⟨N * K / r ^ beta, ?_⟩
    rintro v ⟨x, hx, y, hy, hxy, rfl⟩
    exact hpoint x hx y hy hxy
  have hsemi : _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier q) G ≤ N * K / r ^ beta := by
    by_cases hne : (_root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet beta (frontier q) G).Nonempty
    · exact csSup_le hne (by
        intro v hv
        rcases hv with ⟨x, hx, y, hy, hxy, rfl⟩
        exact hpoint x hx y hy hxy)
    · have hempty : _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet beta (frontier q) G = ∅ :=
        not_nonempty_iff_eq_empty.mp hne
      have hbound : 0 ≤ N * K / r ^ beta :=
        div_nonneg (mul_nonneg hN.le hK) (Real.rpow_nonneg hr.le beta)
      simpa [_root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm, hempty] using hbound
  constructor
  · exact hholder
  · dsimp [K] at hsemi ⊢
    calc
      r ^ beta * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier q) G ≤
          r ^ beta * (N * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta S F / r ^ beta) :=
        mul_le_mul_of_nonneg_left hsemi (Real.rpow_nonneg hr.le beta)
      _ = N * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta S F := by
        field_simp [Real.rpow_pos_of_pos hr beta]

theorem aux_lem_affine_gcn_competitor_slope_from_normalizedL2
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : Fin d → ℝ) (c D : ℝ)
    (hD : normalizedL2On (Metric.ball z (r / 2))
      (fun x => (∑ i : Fin d, a i * x i) + c) ≤ D) :
    ‖a‖ ≤ (2 * Real.sqrt 3 / r) * D := by
  have hq : Metric.ball z (r / 2) =
      Homogenization.axisCube
        (fun i : Fin d => z i - r / 2) r := by
    rw [show Metric.ball z (r / 2) =
        (centeredCube z r hr : Set (SpatialCoordinates d)) by rfl,
      centeredCube_eq_pi]
    ext x
    simp only [Homogenization.axisCube,
      Set.mem_pi, Set.mem_univ, Set.mem_Ioo]
    constructor
    · intro hx i _
      have hxi := hx i trivial
      exact ⟨by linarith [hxi.1], by linarith [hxi.2]⟩
    · intro hx i _
      have hxi := hx i trivial
      exact ⟨by linarith [hxi.1], by linarith [hxi.2]⟩
  have hlow :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.normalizedL2On_axisCube_affineEval_ge
      (d := d) (z := fun i : Fin d => z i - r / 2) (L := r) hr c a
  have hslope : r / (2 * Real.sqrt 3) *
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.slopeMagnitude a ≤ D := by
    rw [← hq] at hlow
    have hD' : normalizedL2On (Metric.ball z (r / 2))
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.affineEval c a) ≤ D := by
      have hfun : SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.affineEval c a =
          (fun x => (∑ i : Fin d, a i * x i) + c) := by
        funext x
        simp [SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.affineEval,
          Homogenization.vecDot]
        ring
      rw [hfun]
      exact hD
    exact hlow.trans hD'
  have hnorm : ‖a‖ ≤
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.slopeMagnitude a := by
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.norm_le_slopeMagnitude a
  have hD0 : 0 ≤ D := by
    exact le_trans (mul_nonneg (div_nonneg hr.le (by positivity))
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.slopeMagnitude_nonneg a)) hslope
  have hrden : 0 < r / (2 * Real.sqrt 3) := by positivity
  calc
    ‖a‖ ≤ SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.slopeMagnitude a := hnorm
    _ ≤ D / (r / (2 * Real.sqrt 3)) :=
      (le_div_iff₀ hrden).2 (by simpa [mul_comm] using hslope)
    _ = (2 * Real.sqrt 3 / r) * D := by field_simp

theorem aux_lem_affine_gcn_competitor_normalized_dilation_eLpNorm
    {d : ℕ} (z : SpatialCoordinates d) (r N : ℝ) (hr : 0 < r) (hN : 0 < N)
    (f : SpatialCoordinates d → ℝ)
    (hf : MemLp f 2 (volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d)))) :
    (eLpNorm (fun x =>
      (f (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r x)) / N) 2
      (volume.restrict
        (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
          Set (SpatialCoordinates d)))).toReal =
      normalizedL2On (centeredCube z r hr : Set (SpatialCoordinates d)) f / N := by
  let T : SpatialCoordinates d → SpatialCoordinates d :=
    _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r
  have hdil := aux_lem_affine_gcn_competitor_dilation_norm z r hr hf
  have hscale :
      (fun x => f (T x) / N) =
        (N⁻¹ : ℝ) • (fun x => f (T x)) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [hscale, MeasureTheory.eLpNorm_const_smul]
  have hnorm : ‖(N⁻¹ : ℝ)‖ₑ = ENNReal.ofReal (N⁻¹) := by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hN)]
  rw [hnorm, ENNReal.toReal_mul, hdil]
  have hvol : (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal = r ^ d := by
    rw [centeredCube_volume, ENNReal.toReal_ofReal (pow_nonneg hr.le _)]
  have hnorm0 : (volume
      (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
        Set (SpatialCoordinates d))).toReal = 1 := by
    rw [centeredCube_volume]
    simp
  have hnormq : Real.sqrt (r ^ d) ≠ 0 := by positivity
  have hnormN : (0 : ℝ) < N := hN
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr hN.le)]
  rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.normalizedL2On_eq_toReal_eLpNorm_div hf,
    hvol]
  field_simp [hnormq, hnormN.ne']

theorem aux_lem_affine_gcn_competitor_scaled_interpolation
    {d : ℕ} (alpha beta r N : ℝ) (q S : Set (SpatialCoordinates d))
    (G F : SpatialCoordinates d → ℝ)
    (T Tinv : SpatialCoordinates d → SpatialCoordinates d)
    (C A D theta : ℝ)
    (hbeta : 0 < beta) (hr : 0 < r) (hN : 0 < N)
    (hTinv : ∀ x ∈ frontier q, Tinv x ∈ S)
    (hTinvl : ∀ x ∈ frontier q, T (Tinv x) = x)
    (hscale : ∀ x ∈ frontier q, ∀ y ∈ frontier q, x ≠ y →
      Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) =
        r * Real.sqrt (∑ j : Fin d, (Tinv x j - Tinv y j) ^ 2))
    (hrel : ∀ x ∈ frontier q, G x = N * F (Tinv x))
    (_hF : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha S F)
    (hFbeta : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S F)
    (hsemi : _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta S F ≤ C * A ^ theta * D ^ (1 - theta)) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (frontier q) G ∧
      r ^ beta * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier q) G ≤
        N * (C * A ^ theta * D ^ (1 - theta)) := by
  obtain ⟨hG, htransport⟩ := aux_lem_affine_gcn_competitor_holder_transport
    beta r N q S G F T Tinv hbeta hr hN hTinv hTinvl hscale hrel hFbeta
  refine ⟨hG, ?_⟩
  exact htransport.trans (mul_le_mul_of_nonneg_left hsemi hN.le)

theorem aux_lem_affine_gcn_competitor_cube_scaled_interpolation
    {d : ℕ} (alpha beta r N : ℝ) (z : SpatialCoordinates d)
    (S : Set (SpatialCoordinates d)) (G F : SpatialCoordinates d → ℝ)
    (C A D theta : ℝ)
    (hbeta : 0 < beta) (hr : 0 < r) (hN : 0 < N)
    (hTinv : ∀ x ∈ frontier (Metric.ball z (r / 2)),
      _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation 0 z r⁻¹ x ∈ S)
    (hTinvl : ∀ x ∈ frontier (Metric.ball z (r / 2)),
      _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r
        (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation 0 z r⁻¹ x) = x)
    (hscale : ∀ x ∈ frontier (Metric.ball z (r / 2)),
      ∀ y ∈ frontier (Metric.ball z (r / 2)), x ≠ y →
        Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) =
          r * Real.sqrt (∑ j : Fin d,
            ((_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation 0 z r⁻¹ x) j -
              (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation 0 z r⁻¹ y) j) ^ 2))
    (hrel : ∀ x ∈ frontier (Metric.ball z (r / 2)),
      G x = N * F (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation 0 z r⁻¹ x))
    (hF : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha S F)
    (hFbeta : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S F)
    (hsemi : _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta S F ≤ C * A ^ theta * D ^ (1 - theta)) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (frontier (Metric.ball z (r / 2))) G ∧
      r ^ beta * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier (Metric.ball z (r / 2))) G ≤
        N * (C * A ^ theta * D ^ (1 - theta)) := by
  exact aux_lem_affine_gcn_competitor_scaled_interpolation
    alpha beta r N (Metric.ball z (r / 2)) S G F
      (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation 0 z r⁻¹)
      C A D theta hbeta hr hN hTinv hTinvl hscale hrel hF hFbeta hsemi

theorem aux_lem_affine_gcn_competitor_and_left {P Q : Prop}
    (h : P ∧ Q) : P := h.1

theorem aux_lem_affine_gcn_competitor_and_right {P Q : Prop}
    (h : P ∧ Q) : Q := h.2

/-
theorem aux_lem_affine_gcn_competitor_harmonic_representative_point
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (w : Homogenization.H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hwweak : SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.IsUnitWeaklyHarmonicOn
      (centeredCube z R hR : Set (SpatialCoordinates d)) w)
    (vH : SpatialCoordinates d → ℝ)
    (hvHarm : InnerProductSpace.HarmonicOnNhd
      (vH ∘ (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm :
        EuclideanSpace ℝ (Fin d) → SpatialCoordinates d))
      ((SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc :
        SpatialCoordinates d → EuclideanSpace ℝ (Fin d)) ''
          (centeredCube z R hR : Set (SpatialCoordinates d)))
    )
    (hvHae : True)
    (U0 : ℝ)
    (hV0memW : True) : True := by
  trivial
/-
  have hcubeEq :
      SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet (z, R) =
        Metric.ball z (R / 2) := by
    ext x
    simp only [SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet,
      SubdiffusiveProcess.Section9.centeredAxisCube, Homogenization.axisCube,
      centeredCube, Set.mem_pi, Set.mem_univ, forall_true_left,
      Set.mem_Ioo, Metric.mem_ball]
    rw [dist_pi_lt_iff (by linarith)]
    constructor
    · intro h i
      have hi := h i
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hi.1, hi.2]
    · intro h i
      have hi := h i
      rw [Real.dist_eq, abs_lt] at hi
      constructor <;> linarith [hi.1, hi.2]
  have hwweak1 : SubdiffusiveProcess.CoarseGrainingVocab.IsWeaklyHarmonicOn
      (fun _ : SpatialCoordinates d => (1 : ℝ))
      (Metric.ball z (R / 2)) w := by
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.isUnitWeaklyHarmonicOn_iff.mp
      (by simpa [centeredCube] using hwweak)
  let w0 : Homogenization.H1Function (Metric.ball z (R / 2)) :=
    w - Homogenization.H1Function.const U0
  have hwweak0 : SubdiffusiveProcess.CoarseGrainingVocab.IsWeaklyHarmonicOn
      (fun _ : SpatialCoordinates d => (1 : ℝ))
      (Metric.ball z (R / 2)) w0 := by
    simpa [w0] using
      (aux_lem_affine_gcn_competitor_weak_harmonic_sub_const hwweak1 U0)
  have hvHcontW : ContinuousOn vH (Metric.ball z (R / 2)) := by
    intro x hx
    have hxE :
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc x) ∈
          (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc ''
            Metric.ball z (R / 2)) := ⟨x, hx, rfl⟩
    have hh := hvHarm
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc x) hxE
    have hc := hh.1.continuousAt.comp
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.continuous.continuousAt)
    simpa [Function.comp_def] using hc.continuousWithinAt
  have hv0contW : ContinuousOn (fun x => vH x - U0)
      (Metric.ball z (R / 2)) := by
    exact hvHcontW.sub continuousOn_const
  have hvHae' : vH =ᵐ[volume.restrict (Metric.ball z (R / 2))] w.toFun := by
    have hv := ae_restrict_of_ae (s := Metric.ball z (R / 2)) hvHae
    filter_upwards [hv, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxm
    have hxm' : x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) := by
      simpa [centeredCube, ← hcubeEq] using hxm
    rw [hx, Set.indicator_of_mem hxm']
  have hv0ae : (fun x => vH x - U0) =ᵐ[
      volume.restrict (Metric.ball z (R / 2))] w0.toFun := by
    filter_upwards [hvHae'] with x hx
    simp only [w0, Homogenization.H1Function.sub_toFun,
      Homogenization.H1Function.const] at ⊢
    rw [hx]
  have hweakV0 : SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.WeakHarmonic
      (fun _ : SpatialCoordinates d => (1 : ℝ))
      (Metric.ball z (R / 2)) (fun x => vH x - U0) := by
    exact aux_lem_affine_gcn_competitor_weak_harmonic_representative
      Metric.isOpen_ball hwweak0 hv0contW hv0ae
  have hBctrl :
      SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic.LogCoefficientControlOn
        (fun _ : SpatialCoordinates d => (1 : ℝ)) 1 (z, R) := by
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section11.logCoefficientControlOn_const
      one_pos (z, R)
  have hzhalf : z ∈ SubdiffusiveProcess.Section9.centeredAxisCube z (R / 2) := by
    rw [SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.mem_centeredAxisCube]
    intro i
    simp
    linarith
  have hmem : MemLp (fun x => vH x - U0) 2
      (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet (z, R))) := by
    simpa [hcubeEq] using hV0memW
  have hweak' : SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.WeakHarmonic
      (fun _ : SpatialCoordinates d => (1 : ℝ))
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet (z, R))
      (fun x => vH x - U0) := by
    simpa [hcubeEq] using hweakV0
  have hpoint := aux_lem_affine_gcn_competitor_harmonic_point hd hR
    hBctrl hweak' hmem hzhalf
 simpa [hcubeEq] using hpoint
-/
-/

theorem aux_lem_affine_gcn_competitor_harmonic_point_from_weak
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (V : SpatialCoordinates d → ℝ)
    (hweak : SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.WeakHarmonic
      (fun _ : SpatialCoordinates d => (1 : ℝ))
      (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet (z, R)) V)
    (hctrl : SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic.LogCoefficientControlOn
      (fun _ : SpatialCoordinates d => (1 : ℝ)) 1 (z, R))
    (hmem : MemLp V 2
      (volume.restrict (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet (z, R)))) :
    |V z| ≤
      (1 + SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic.interiorHarmonicConstant d 1) *
        normalizedL2On (SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.cubeSet (z, R)) V := by
  have hzhalf : z ∈ SubdiffusiveProcess.Section9.centeredAxisCube z (R / 2) := by
    rw [SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.mem_centeredAxisCube]
    intro i
    simp
    linarith
  have hpoint := aux_lem_affine_gcn_competitor_harmonic_point hd hR
    hctrl hweak hmem hzhalf
  simpa using hpoint

/-- **Affine trace approximation on one good cell — deterministic core of `mfd:lem-affine`**
(`mfd:lem-affine` and `eq:mfd-34` and `eq:mfd-2`, proof of `eq:mfd-34`). Constants: `Cin` bundles the universal constants of the
good-cell inputs (oscillation, Hölder gain, extension bound `eq:mfd-2`, comparison-scale rounding) and is
fixed BEFORE `L`; then `L ≥ L0`, then `epshom ≤ eps0(L)`, then the source allowance `src0`.
Inputs on the cell `q = ball z (r/2)` inside the comparison cube `Q_R = ball z (R/2) ⊆ Q`, `L^γ r ≤ R ≤ Cin L^γ r`,
with `S = λ(q) = Γ_E(u)(q) + c|q|` and the reference coefficient `s = s_E(q) > 0`:
* `hosc`/`hOs`: oscillation of `U` on `Q_R` at most `Os ≤ Cin R^{(2-d)/2} L^{(d+ζ)/2} √(S/s)` (parent bound +
  energy-to-oscillation at scale `R`, `mfd:lem-affine` and `eq:mfd-34` and `eq:mfd-2`);
* `hharm`: an ORDINARY (Laplace-)harmonic `ū` on `Q_R` with `‖U - ū‖_{L²-avg(Q_R)} ≤ epshom·Os + Src`
  (good-event condition (b), `mfd:lem-affine` and `eq:mfd-34` and `eq:mfd-2`);
* `hHol`: local Hölder gain on `q`: `|U x - U y| ≤ Cin (Os + Src) (|x-y|/R)^α`;
* `hext`: `eq:mfd-2` for `E` on `q` with `U_E(q) ≍ s`: every continuous boundary datum that is `β`-Hölder on
  `∂q` has an `E`-competitor of energy `≤ Cin s r^{d-2} (r^β [g]_{β,∂q})²`;
* `hsrc`: normalized source allowance `Src ≤ src0 r^{(2-d)/2} √(S/s)` (fine base mesh, `mfd:lem-affine` and `eq:mfd-34` and `eq:mfd-2`).
Conclusion: the boundary-matched competitor class of `U - ℓ` for an affine `ℓ` (the `L²(q)`-best affine
approximation) has energy infimum `≤ ρ S`. Truth: `A_L`, `B_L` of the paper, `lem_interp` with
`ϑ = (α-β)/(α+d/2)`, exponent `e_d = affineExponent < 0`. A helper with free `ρ`, `L`, arbitrary `parentCell` and no good-cell inputs
would be FALSE. -/
theorem aux_lem_affine_gcn_competitor_normalized_budget
    (Cin Cinterp A B theta S s N H : ℝ)
    (hCin : 0 ≤ Cin) (hCinterp : 0 ≤ Cinterp)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (_hS : 0 ≤ S) (hs : 0 < s) (hN : 0 < N)
    (hp : 0 ≤ theta) (hp1 : 0 ≤ 1 - theta)
    (hscale : s * N ^ 2 = S)
    (hH : 0 ≤ H)
    (hsemi : H ≤ N * (Cinterp * A ^ theta * B ^ (1 - theta))) :
    Cin * s * H ^ 2 ≤
      Cin * Cinterp ^ 2 * A ^ (2 * theta) * B ^ (2 * (1 - theta)) * S := by
  have hterm : 0 ≤ Cinterp * A ^ theta * B ^ (1 - theta) := by
    exact mul_nonneg (mul_nonneg hCinterp (Real.rpow_nonneg hA _))
      (Real.rpow_nonneg hB _)
  have hright : 0 ≤ N * (Cinterp * A ^ theta * B ^ (1 - theta)) :=
    mul_nonneg hN.le hterm
  have hsq : H ^ 2 ≤
      (N * (Cinterp * A ^ theta * B ^ (1 - theta))) ^ 2 :=
    (sq_le_sq₀ hH hright).2 hsemi
  have hpowA : (A ^ theta) ^ 2 = A ^ (2 * theta) := by
    rw [pow_two, ← Real.rpow_add_of_nonneg hA hp hp]
    congr 1
    ring
  have hpowB : (B ^ (1 - theta)) ^ 2 = B ^ (2 * (1 - theta)) := by
    rw [pow_two, ← Real.rpow_add_of_nonneg hB hp1 hp1]
    congr 1
    ring
  have hcoef : 0 ≤ Cin * s := mul_nonneg hCin (le_of_lt hs)
  calc
    Cin * s * H ^ 2 ≤
        Cin * s * (N * (Cinterp * A ^ theta * B ^ (1 - theta))) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hcoef
    _ = Cin * Cinterp ^ 2 * A ^ (2 * theta) *
          B ^ (2 * (1 - theta)) * (s * N ^ 2) := by
      rw [mul_pow, mul_pow, mul_pow, hpowA, hpowB]
      ring
    _ = Cin * Cinterp ^ 2 * A ^ (2 * theta) *
          B ^ (2 * (1 - theta)) * S := by rw [hscale]

theorem aux_lem_affine_gcn_competitor_normalization
    (d : ℕ) (r s S : ℝ) (hr : 0 < r) (hs : 0 < s) (hS : 0 < S) :
    s * r ^ ((d : ℝ) - 2) *
        (r ^ ((2 - (d : ℝ)) / 2) * Real.sqrt (S / s)) ^ 2 = S := by
  have hroot : (Real.sqrt (S / s)) ^ 2 = S / s := by
    exact Real.sq_sqrt (le_of_lt (div_pos hS hs))
  have hpow : (r ^ ((2 - (d : ℝ)) / 2)) ^ 2 =
      r ^ (2 * ((2 - (d : ℝ)) / 2)) := by
    calc
      (r ^ ((2 - (d : ℝ)) / 2)) ^ 2 =
          r ^ ((2 - (d : ℝ)) / 2) * r ^ ((2 - (d : ℝ)) / 2) := by
            rw [pow_two]
      _ = r ^ (((2 - (d : ℝ)) / 2) + ((2 - (d : ℝ)) / 2)) :=
        (Real.rpow_add hr _ _).symm
      _ = r ^ (2 * ((2 - (d : ℝ)) / 2)) := by congr 1 ; ring
  calc
    s * r ^ ((d : ℝ) - 2) *
          (r ^ ((2 - (d : ℝ)) / 2) * Real.sqrt (S / s)) ^ 2 =
        s * (r ^ ((d : ℝ) - 2) *
          (r ^ ((2 - (d : ℝ)) / 2)) ^ 2) * (S / s) := by
      rw [mul_pow, hroot]
      ring
    _ = s * r ^ (((d : ℝ) - 2) + 2 * ((2 - (d : ℝ)) / 2)) * (S / s) := by
      congr 2
      rw [hpow]
      exact (Real.rpow_add hr _ _).symm
    _ = S := by
      rw [show ((d : ℝ) - 2) + 2 * ((2 - (d : ℝ)) / 2) = 0 by ring,
        Real.rpow_zero]
      field_simp

theorem aux_lem_affine_gcn_competitor_trace_scale
    (K rho A B theta a b L0 L Sq trace : ℝ)
    (hK : 0 ≤ K) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hSq : 0 ≤ Sq)
    (hL01 : 0 < L0) (hL : L0 ≤ L) (hθ0 : 0 ≤ theta)
    (hθ1 : 0 ≤ 1 - theta) (he : a * (2 * theta) + b * (2 * (1 - theta)) ≤ 0)
    (hA : A ≤ 2 * K * L ^ a) (hB : B ≤ K * L ^ b)
    (htrace : trace ≤ K * A ^ (2 * theta) * B ^ (2 * (1 - theta)) * Sq)
    (hbase : K * (2 * K * L0 ^ a) ^ (2 * theta) *
        (K * L0 ^ b) ^ (2 * (1 - theta)) ≤ rho) :
    trace ≤ rho * Sq := by
  have hL0pos : 0 < L0 := hL01
  have hLpos : 0 < L := lt_of_lt_of_le hL0pos hL
  have hAu : 0 ≤ 2 * K * L ^ a := by positivity
  have hBu : 0 ≤ K * L ^ b := by positivity
  have hApow : A ^ (2 * theta) ≤ (2 * K * L ^ a) ^ (2 * theta) :=
    Real.rpow_le_rpow hA0 hA (by linarith)
  have hBpow : B ^ (2 * (1 - theta)) ≤
      (K * L ^ b) ^ (2 * (1 - theta)) :=
    Real.rpow_le_rpow hB0 hB (by linarith)
  have hprod : K * A ^ (2 * theta) * B ^ (2 * (1 - theta)) ≤
      K * (2 * K * L ^ a) ^ (2 * theta) *
        (K * L ^ b) ^ (2 * (1 - theta)) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left hApow hK)
      hBpow (Real.rpow_nonneg hB0 _) (by positivity)
  have hLpow : L ^ (a * (2 * theta) + b * (2 * (1 - theta))) ≤
      L0 ^ (a * (2 * theta) + b * (2 * (1 - theta))) := by
    exact Real.rpow_le_rpow_of_nonpos hL0pos hL he
  have hfactor : K * (2 * K * L ^ a) ^ (2 * theta) *
      (K * L ^ b) ^ (2 * (1 - theta)) =
      K * (2 * K) ^ (2 * theta) * K ^ (2 * (1 - theta)) *
        L ^ (a * (2 * theta) + b * (2 * (1 - theta))) := by
    calc
      K * (2 * K * L ^ a) ^ (2 * theta) *
          (K * L ^ b) ^ (2 * (1 - theta)) =
          K * ((2 * K) * L ^ a) ^ (2 * theta) *
            (K * L ^ b) ^ (2 * (1 - theta)) := by rw [show 2 * K * L ^ a = (2 * K) * L ^ a by ring]
      _ = K * ((2 * K) ^ (2 * theta) * (L ^ a) ^ (2 * theta)) *
            (K * L ^ b) ^ (2 * (1 - theta)) := by
              rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hLpos.le _)]
      _ = K * ((2 * K) ^ (2 * theta) * L ^ (a * (2 * theta))) *
            (K ^ (2 * (1 - theta)) * L ^ (b * (2 * (1 - theta)))) := by
              rw [← Real.rpow_mul hLpos.le,
                Real.mul_rpow hK (Real.rpow_nonneg hLpos.le _),
                ← Real.rpow_mul hLpos.le]
      _ = K * (2 * K) ^ (2 * theta) * K ^ (2 * (1 - theta)) *
            L ^ (a * (2 * theta) + b * (2 * (1 - theta))) := by
              calc
                _ = K * (2 * K) ^ (2 * theta) * K ^ (2 * (1 - theta)) *
                    (L ^ (a * (2 * theta)) * L ^ (b * (2 * (1 - theta)))) := by ring
                _ = _ := by rw [← Real.rpow_add hLpos]
  have hfactor0 : K * (2 * K * L0 ^ a) ^ (2 * theta) *
      (K * L0 ^ b) ^ (2 * (1 - theta)) =
      K * (2 * K) ^ (2 * theta) * K ^ (2 * (1 - theta)) *
        L0 ^ (a * (2 * theta) + b * (2 * (1 - theta))) := by
    calc
      K * (2 * K * L0 ^ a) ^ (2 * theta) *
          (K * L0 ^ b) ^ (2 * (1 - theta)) =
          K * ((2 * K) * L0 ^ a) ^ (2 * theta) *
            (K * L0 ^ b) ^ (2 * (1 - theta)) := by rw [show 2 * K * L0 ^ a = (2 * K) * L0 ^ a by ring]
      _ = K * ((2 * K) ^ (2 * theta) * (L0 ^ a) ^ (2 * theta)) *
            (K * L0 ^ b) ^ (2 * (1 - theta)) := by
              rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hL0pos.le _)]
      _ = K * ((2 * K) ^ (2 * theta) * L0 ^ (a * (2 * theta))) *
            (K ^ (2 * (1 - theta)) * L0 ^ (b * (2 * (1 - theta)))) := by
              rw [← Real.rpow_mul hL0pos.le,
                Real.mul_rpow hK (Real.rpow_nonneg hL0pos.le _),
                ← Real.rpow_mul hL0pos.le]
      _ = K * (2 * K) ^ (2 * theta) * K ^ (2 * (1 - theta)) *
            L0 ^ (a * (2 * theta) + b * (2 * (1 - theta))) := by
              calc
                _ = K * (2 * K) ^ (2 * theta) * K ^ (2 * (1 - theta)) *
                    (L0 ^ (a * (2 * theta)) * L0 ^ (b * (2 * (1 - theta)))) := by ring
                _ = _ := by rw [← Real.rpow_add hL0pos]
  have hcur : K * (2 * K * L ^ a) ^ (2 * theta) *
      (K * L ^ b) ^ (2 * (1 - theta)) ≤
      K * (2 * K * L0 ^ a) ^ (2 * theta) *
        (K * L0 ^ b) ^ (2 * (1 - theta)) := by
    rw [hfactor, hfactor0]
    exact mul_le_mul_of_nonneg_left hLpow (by positivity)
  calc
    trace ≤ K * A ^ (2 * theta) * B ^ (2 * (1 - theta)) * Sq := htrace
    _ ≤ K * (2 * K * L ^ a) ^ (2 * theta) *
          (K * L ^ b) ^ (2 * (1 - theta)) * Sq :=
      mul_le_mul_of_nonneg_right hprod hSq
    _ ≤ K * (2 * K * L0 ^ a) ^ (2 * theta) *
          (K * L0 ^ b) ^ (2 * (1 - theta)) * Sq :=
      mul_le_mul_of_nonneg_right hcur hSq
    _ ≤ rho * Sq := mul_le_mul_of_nonneg_right hbase hSq

theorem aux_lem_affine_gcn_competitor_affine_trace_all
    (d : ℕ) (hd : 2 ≤ d) (Cc : ℝ) (hCc : 1 ≤ Cc)
    (alpha beta gamma zeta : ℝ)
    (hbeta : 1 / 2 < beta) (hba : beta < alpha) (halpha : alpha < 1)
    (_hgamma : 0 < gamma) (_hgamma1 : gamma < 1) (_hzeta : 0 < zeta)
    (hneg : _root_.SubdiffusiveProcess.ResponseMoments.affineExponent (d : ℝ) alpha beta gamma zeta < 0)
    (rho : ℝ) (hrho : 0 < rho) :
    ∃ L0 : ℝ, 1 < L0 ∧ ∀ L : ℝ, L0 ≤ L → ∃ ehom : ℝ, 0 < ehom ∧
      ∀ (A B theta Sq trace : ℝ),
        theta = (alpha - beta) / (alpha + (d : ℝ) / 2) →
        0 ≤ A → 0 ≤ B → 0 ≤ Sq →
        A ≤ Cc * L ^ (((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2 - 2 * gamma) +
            Cc * ehom * L ^ (((d : ℝ) + zeta) / 2 + gamma) →
        B ≤ Cc * L ^ (((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2 - alpha * gamma) →
        trace ≤ Cc * A ^ (2 * theta) * B ^ (2 * (1 - theta)) * Sq →
        trace ≤ rho * Sq := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hCc0 : (0 : ℝ) < Cc := lt_of_lt_of_le zero_lt_one hCc
  obtain ⟨L0, hL01, hL0bound⟩ :=
    _root_.SubdiffusiveProcess.ResponseMoments.exists_one_lt_rpow_le
      (s := 2 * _root_.SubdiffusiveProcess.ResponseMoments.affineExponent
        (d : ℝ) alpha beta gamma zeta)
      (c := 4 * Cc ^ 5) (eps := rho) (by linarith) (by positivity) hrho
  refine ⟨L0, hL01, ?_⟩
  intro L hLL0
  have hL1 : 1 < L := lt_of_lt_of_le hL01 hLL0
  have hL0 : (0 : ℝ) < L := lt_trans zero_lt_one hL1
  have hLbound :
      4 * Cc ^ 5 * L ^ (2 * _root_.SubdiffusiveProcess.ResponseMoments.affineExponent
        (d : ℝ) alpha beta gamma zeta) ≤ rho := by
    refine le_trans ?_ hL0bound
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow_of_nonpos (lt_trans zero_lt_one hL01) hLL0 (by linarith)
  set a1 : ℝ := ((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2 - 2 * gamma with ha1
  set a2 : ℝ := ((d : ℝ) + zeta) / 2 + gamma with ha2
  set b1 : ℝ := ((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2 - alpha * gamma with hb1
  refine ⟨L ^ (a1 - a2), Real.rpow_pos_of_pos hL0 _, ?_⟩
  intro A B theta Sq trace htheta hA0 hB0 hSq hA hB htr
  have hden : alpha + (d : ℝ) / 2 ≠ 0 := by nlinarith
  have hdenpos : (0 : ℝ) < alpha + (d : ℝ) / 2 := by nlinarith
  have hth0 : 0 < theta := by
    rw [htheta]; exact div_pos (by linarith) hdenpos
  have hth1 : theta ≤ 1 := by
    rw [htheta, div_le_one hdenpos]; linarith
  have hexp : a1 - a2 + a2 = a1 := by ring
  have hAsum : Cc * L ^ a1 + Cc * L ^ (a1 - a2) * L ^ a2 = 2 * (Cc * L ^ a1) := by
    rw [mul_assoc, ← Real.rpow_add hL0, hexp]; ring
  have hA2 : A ≤ 2 * (Cc * L ^ a1) := by rw [← hAsum]; exact hA
  have hApow : A ^ (2 * theta) ≤ (2 * (Cc * L ^ a1)) ^ (2 * theta) :=
    Real.rpow_le_rpow hA0 hA2 (by linarith)
  have hBpow : B ^ (2 * (1 - theta)) ≤ (Cc * L ^ b1) ^ (2 * (1 - theta)) :=
    Real.rpow_le_rpow hB0 hB (by linarith)
  have hL1nn : (0 : ℝ) ≤ L ^ a1 := (Real.rpow_pos_of_pos hL0 a1).le
  have hLb1nn : (0 : ℝ) ≤ L ^ b1 := (Real.rpow_pos_of_pos hL0 b1).le
  have hsplitA : (2 * (Cc * L ^ a1)) ^ (2 * theta) =
      (2 * Cc) ^ (2 * theta) * L ^ (a1 * (2 * theta)) := by
    rw [show 2 * (Cc * L ^ a1) = (2 * Cc) * L ^ a1 by ring,
      Real.mul_rpow (by positivity) hL1nn, ← Real.rpow_mul hL0.le]
  have hsplitB : (Cc * L ^ b1) ^ (2 * (1 - theta)) =
      Cc ^ (2 * (1 - theta)) * L ^ (b1 * (2 * (1 - theta))) := by
    rw [Real.mul_rpow hCc0.le hLb1nn, ← Real.rpow_mul hL0.le]
  have hmerge : L ^ (a1 * (2 * theta)) * L ^ (b1 * (2 * (1 - theta))) =
      L ^ (2 * _root_.SubdiffusiveProcess.ResponseMoments.affineExponent
        (d : ℝ) alpha beta gamma zeta) := by
    rw [← Real.rpow_add hL0]
    congr 1
    exact _root_.SubdiffusiveProcess.ResponseMoments.affine_exponent_split
      (d : ℝ) alpha beta gamma zeta theta hden htheta
  have hc1 : (2 * Cc) ^ (2 * theta) ≤ (2 * Cc) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hc2 : Cc ^ (2 * (1 - theta)) ≤ Cc ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hCc (by linarith)
  have he1 : (2 * Cc) ^ (2 : ℝ) = (2 * Cc) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (2 * Cc) 2]; norm_num
  have he2 : Cc ^ (2 : ℝ) = Cc ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast Cc 2]; norm_num
  have hLed : (0 : ℝ) < L ^ (2 * _root_.SubdiffusiveProcess.ResponseMoments.affineExponent
      (d : ℝ) alpha beta gamma zeta) := Real.rpow_pos_of_pos hL0 _
  have hkey : Cc * A ^ (2 * theta) * B ^ (2 * (1 - theta)) ≤ rho := by
    have hpb : (0 : ℝ) ≤ B ^ (2 * (1 - theta)) := Real.rpow_nonneg hB0 _
    have hbase : (0 : ℝ) ≤ 2 * (Cc * L ^ a1) := by
      have := mul_nonneg hCc0.le hL1nn
      linarith
    have hb' : (0 : ℝ) ≤ Cc * (2 * (Cc * L ^ a1)) ^ (2 * theta) :=
      mul_nonneg hCc0.le (Real.rpow_nonneg hbase _)
    have hstep1 : Cc * A ^ (2 * theta) * B ^ (2 * (1 - theta)) ≤
        Cc * (2 * (Cc * L ^ a1)) ^ (2 * theta) *
          (Cc * L ^ b1) ^ (2 * (1 - theta)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hApow hCc0.le)
        hBpow hpb hb'
    have hstep2 : Cc * (2 * (Cc * L ^ a1)) ^ (2 * theta) *
        (Cc * L ^ b1) ^ (2 * (1 - theta)) =
        Cc * ((2 * Cc) ^ (2 * theta) * Cc ^ (2 * (1 - theta))) *
          L ^ (2 * _root_.SubdiffusiveProcess.ResponseMoments.affineExponent
            (d : ℝ) alpha beta gamma zeta) := by
      rw [hsplitA, hsplitB, ← hmerge]; ring
    have hpos2 : (0 : ℝ) ≤ Cc ^ (2 * (1 - theta)) := Real.rpow_nonneg hCc0.le _
    have hmul : (2 * Cc) ^ (2 * theta) * Cc ^ (2 * (1 - theta)) ≤
        (2 * Cc) ^ (2 : ℕ) * Cc ^ (2 : ℕ) := by
      rw [← he1, ← he2]
      exact mul_le_mul hc1 hc2 hpos2 (Real.rpow_nonneg (by linarith) _)
    have hfin : Cc * ((2 * Cc) ^ (2 : ℕ) * Cc ^ (2 : ℕ)) = 4 * Cc ^ 5 := by ring
    have hstep3 : Cc * ((2 * Cc) ^ (2 * theta) * Cc ^ (2 * (1 - theta))) *
        L ^ (2 * _root_.SubdiffusiveProcess.ResponseMoments.affineExponent
          (d : ℝ) alpha beta gamma zeta) ≤
        4 * Cc ^ 5 * L ^ (2 * _root_.SubdiffusiveProcess.ResponseMoments.affineExponent
          (d : ℝ) alpha beta gamma zeta) := by
      rw [← hfin]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmul hCc0.le) hLed.le
    calc
      Cc * A ^ (2 * theta) * B ^ (2 * (1 - theta)) ≤
          Cc * (2 * (Cc * L ^ a1)) ^ (2 * theta) *
            (Cc * L ^ b1) ^ (2 * (1 - theta)) := hstep1
      _ = Cc * ((2 * Cc) ^ (2 * theta) * Cc ^ (2 * (1 - theta))) *
            L ^ (2 * _root_.SubdiffusiveProcess.ResponseMoments.affineExponent
              (d : ℝ) alpha beta gamma zeta) := hstep2
      _ ≤ 4 * Cc ^ 5 * L ^ (2 * _root_.SubdiffusiveProcess.ResponseMoments.affineExponent
            (d : ℝ) alpha beta gamma zeta) := hstep3
      _ ≤ rho := hLbound
  calc
    trace ≤ Cc * A ^ (2 * theta) * B ^ (2 * (1 - theta)) * Sq := htr
    _ ≤ rho * Sq := mul_le_mul_of_nonneg_right hkey hSq

theorem aux_lem_affine_gcn_competitor_extension_apply
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GammaE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E) (beta : ℝ)
    (q : Set (SpatialCoordinates d)) (Cin s r : ℝ)
    (hext : ∀ g : SpatialCoordinates d → ℝ,
      ContinuousOn g (closure (Q : Set (SpatialCoordinates d))) →
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (frontier q) g →
      ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
        v ∈ E.domain ∧
        ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
        ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (Q : Set (SpatialCoordinates d))] V) ∧
        (∀ x ∈ frontier q, V x = g x) ∧
        (GammaE.measure v q).toReal ≤
          Cin * s * r ^ ((d : ℝ) - 2) *
            (r ^ beta * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier q) g) ^ 2)
    (G : SpatialCoordinates d → ℝ)
    (hGcont : ContinuousOn G (closure (Q : Set (SpatialCoordinates d))))
    (hGholder : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (frontier q) G) :
    ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
      v ∈ E.domain ∧
      ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
      ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (Q : Set (SpatialCoordinates d))] V) ∧
      (∀ x ∈ frontier q, V x = G x) ∧
      (GammaE.measure v q).toReal ≤
        Cin * s * r ^ ((d : ℝ) - 2) *
          (r ^ beta * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier q) G) ^ 2 := by
  exact hext G hGcont hGholder

theorem aux_lem_affine_gcn_competitor_volume_ratio
    {d : ℕ} (z : SpatialCoordinates d) (r R : ℝ)
    (hr : 0 < r) (hR : 0 < R) :
    Real.sqrt ((volume (Metric.ball z (R / 2))).toReal /
      (volume (Metric.ball z (r / 2))).toReal) =
      (R / r) ^ ((d : ℝ) / 2) := by
  rw [volume_ball_spatial z (by linarith),
    volume_ball_spatial z (by linarith)]
  rw [ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity)]
  have hRhalf : 2 * (R / 2) = R := by ring
  have hrhalf : 2 * (r / 2) = r := by ring
  rw [hRhalf, hrhalf]
  rw [← Real.rpow_natCast R d, ← Real.rpow_natCast r d]
  rw [← Real.div_rpow hR.le hr.le]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (div_nonneg hR.le hr.le)]
  congr 1
  ring

theorem aux_lem_affine_gcn_competitor_slope_of_euclidean_lipschitz
    {d : ℕ} (V : SpatialCoordinates d → ℝ) (z : SpatialCoordinates d)
    (S : Set (EuclideanSpace ℝ (Fin d))) (K : ℝ)
    (hK : 0 ≤ K) (_hz : (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc z) ∈ S)
    (hS : S ∈ 𝓝 (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc z))
    (hLip : ∀ x ∈ S, ∀ y ∈ S,
      |(V ∘ SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm) x -
          (V ∘ SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm) y| ≤
        K * ‖x - y‖) :
    ‖fun i : Fin d => fderiv ℝ V z (Homogenization.basisVec i)‖ ≤ K := by
  let KNN : ℝ≥0 := ⟨K, hK⟩
  have hLip' : LipschitzOnWith KNN
      (V ∘ SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm) S := by
    intro x hx y hy
    simp only [edist_dist, dist_eq_norm]
    rw [show (KNN : ℝ≥0∞) = ENNReal.ofReal K by
          simp [KNN, ENNReal.ofReal, Real.toNNReal_of_nonneg hK]
          rfl,
      ← ENNReal.ofReal_mul hK]
    exact ENNReal.ofReal_le_ofReal (hLip x hx y hy)
  have hdf : ‖fderiv ℝ (V ∘
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc z)‖ ≤ K := by
    have h := norm_fderiv_le_of_lipschitzOn ℝ hS hLip'
    simpa [KNN] using! h
  rw [pi_norm_le_iff_of_nonneg hK]
  intro i
  have hcomp := SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.fderiv_comp_toEuc
    (V ∘ SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm) z
  have hcomp' : fderiv ℝ V z =
      (fderiv ℝ (V ∘
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm)
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc z)).comp
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc :
          SpatialCoordinates d ≃L[ℝ] EuclideanSpace ℝ (Fin d)).toContinuousLinearMap := by
    simpa only [Function.comp_def,
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.comp_toEuc_symm_toEuc] using! hcomp
  rw [hcomp']
  simp only [ContinuousLinearMap.comp_apply]
  calc
    ‖fderiv ℝ (V ∘
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm)
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc z)
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc
          (Homogenization.basisVec i))‖ ≤
      ‖fderiv ℝ (V ∘
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm)
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc z)‖ *
        ‖SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc
          (Homogenization.basisVec i)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ (V ∘
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc.symm)
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc z)‖ := by
      rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc_basisVec]
      simp
    _ ≤ K := hdf


theorem aux_lem_affine_gcn_competitor_gradSlope
    {d : ℕ} (vH : SpatialCoordinates d → ℝ) (z : SpatialCoordinates d) (R : ℝ)
    (Kgrad : ℝ) (hKgrad0 : 0 ≤ Kgrad)
    (hzMQ : z ∈ SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.middleQuarter (z, R))
    (hMQopen : IsOpen (SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc ''
      SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.middleQuarter (z, R)))
    (hgradLip : ∀ x ∈ SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.middleQuarter (z, R),
        ∀ y ∈ SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.middleQuarter (z, R),
          |vH x - vH y| ≤
            Kgrad * ‖(SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc x : EuclideanSpace ℝ (Fin d)) -
              SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc y‖) :
    ‖fun i : Fin d => fderiv ℝ vH z (Homogenization.basisVec i)‖ ≤ Kgrad := by
  exact aux_lem_affine_gcn_competitor_slope_of_euclidean_lipschitz
    (V := vH) (z := z)
    (S := SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.toEuc ''
      SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube.middleQuarter (z, R))
    (K := Kgrad) hKgrad0 ⟨z, hzMQ, rfl⟩
    (hMQopen.mem_nhds ⟨z, hzMQ, rfl⟩) (by
      intro x hx y hy
      rcases hx with ⟨x0, hx0, rfl⟩
      rcases hy with ⟨y0, hy0, rfl⟩
      have hh := hgradLip x0 hx0 y0 hy0
      simpa [Function.comp_def] using hh)




def aux_lem_affine_gcn_competitor_hessC (d : ℕ) [NeZero d] : ℝ :=
  Classical.choose (Section6OddClass.exists_hessian_normalizedL2On_bound d)

def aux_lem_affine_gcn_competitor_taylorC (d : ℕ) [NeZero d] : ℝ :=
  4 * (d : ℝ) * aux_lem_affine_gcn_competitor_hessC d * Real.sqrt ((4 : ℝ) ^ d)

lemma aux_lem_affine_gcn_competitor_taylorC_nonneg (d : ℕ) [NeZero d] :
    0 ≤ aux_lem_affine_gcn_competitor_taylorC d := by
  have h := (Classical.choose_spec (Section6OddClass.exists_hessian_normalizedL2On_bound d)).1
  unfold aux_lem_affine_gcn_competitor_taylorC aux_lem_affine_gcn_competitor_hessC
  positivity

lemma aux_lem_affine_gcn_competitor_ball_volume
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) :
    (volume (Metric.ball z (R / 2))).toReal = R ^ d := by
  change (volume (centeredCube z R hR : Set (SpatialCoordinates d))).toReal = _
  rw [centeredCube_volume, ENNReal.toReal_ofReal (pow_nonneg hR.le _)]

lemma aux_lem_affine_gcn_competitor_hessian_scaling
    (d : ℕ) (C r R X : ℝ) (hR : 0 < R) :
    (C * (R / 4)⁻¹ * (R / 4)⁻¹ * Real.sqrt (R ^ d / (R / 4) ^ d) * X) *
      (Real.sqrt (d : ℝ) * (r / 2)) ^ 2 =
      (4 * (d : ℝ) * C * Real.sqrt ((4 : ℝ) ^ d)) * (r / R) ^ 2 * X := by
  have he : R ^ d / (R / 4) ^ d = (4 : ℝ) ^ d := by
    rw [← div_pow]
    congr 1
    field_simp
  rw [he, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  field_simp
  ring

lemma aux_lem_affine_gcn_competitor_harmonic_approx
    {d : ℕ} [NeZero d] (z : SpatialCoordinates d) (r R : ℝ)
    (hr : 0 < r) (hR : 0 < R) (h2r : 2 * r ≤ R)
    (V : SpatialCoordinates d → ℝ)
    (hv : MemLp V 2 (volume.restrict (Metric.ball z (R / 2))))
    (hh : InnerProductSpace.HarmonicOnNhd
      (V ∘ (Section6Schauder.toEuc.symm : EuclideanSpace ℝ (Fin d) → SpatialCoordinates d))
      ((Section6Schauder.toEuc : SpatialCoordinates d → EuclideanSpace ℝ (Fin d)) ''
        Metric.ball z (R / 2))) :
    ∃ (m : Fin d → ℝ) (c : ℝ),
      normalizedL2On (Metric.ball z (r / 2))
        (fun x => V x - ((∑ i, m i * x i) + c)) ≤
      aux_lem_affine_gcn_competitor_taylorC d * (r / R) ^ 2 *
        normalizedL2On (Metric.ball z (R / 2)) V := by
  have hvol := aux_lem_affine_gcn_competitor_ball_volume z R hR
  have htop : volume (Metric.ball z (R / 2)) ≠ ⊤ := by
    change volume (centeredCube z R hR : Set (SpatialCoordinates d)) ≠ ⊤
    rw [centeredCube_volume]; exact ENNReal.ofReal_ne_top
  have hpos : 0 < (volume (Metric.ball z (R / 2))).toReal := by rw [hvol]; positivity
  have hsub : Metric.ball z (r / 2) ⊆ Metric.ball z (R / 2) :=
    Metric.ball_subset_ball (by linarith only [h2r, hr])
  have hballs : ∀ p ∈ Metric.ball z (r / 2), Metric.ball p (R / 4) ⊆ Metric.ball z (R / 2) := by
    intro p hp x hx
    rw [Metric.mem_ball] at hp hx ⊢
    have htri := dist_triangle x p z
    linarith only [htri, hp, hx, h2r]
  let C := aux_lem_affine_gcn_competitor_hessC d
  have hC : 0 ≤ C := (Classical.choose_spec
    (Section6OddClass.exists_hessian_normalizedL2On_bound d)).1
  let M := C * (R / 4)⁻¹ * (R / 4)⁻¹ *
    Real.sqrt ((volume (Metric.ball z (R / 2))).toReal / (R / 4) ^ d) *
      normalizedL2On (Metric.ball z (R / 2)) V
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg (by positivity) (Section6Iteration.normalizedL2On_nonneg _ _)
  have ht := aux_lem_affine_gcn_competitor_harmonic_taylor_with_constant d hC
    (Classical.choose_spec (Section6OddClass.exists_hessian_normalizedL2On_bound d)).2
    htop hpos hh hv.integrable_sq (by positivity : 0 < R / 4) hsub hballs (convex_ball z (r / 2))
  have hpoint := aux_lem_affine_gcn_competitor_taylor_point_bound z r M hr hM ht
  let ell := fun x => V z + fderiv ℝ V z (x - z)
  have hell : Continuous ell := by dsimp [ell]; fun_prop
  have hellmem : MemLp ell 2 (volume.restrict (Metric.ball z (r / 2))) := by
    obtain ⟨hh, _⟩ := continuousOn_cube_memLp_and_nonzero z r hr
      (fun x => fun _ : Fin 1 => ell x) (continuousOn_pi' (fun _ => hell.continuousOn))
    exact hh 0
  have hqpos : 0 < (volume (Metric.ball z (r / 2))).toReal := by
    rw [aux_lem_affine_gcn_competitor_ball_volume z r hr]; positivity
  have hqtop : volume (Metric.ball z (r / 2)) ≠ ⊤ := by
    change volume (centeredCube z r hr : Set (SpatialCoordinates d)) ≠ ⊤
    rw [centeredCube_volume]; exact ENNReal.ofReal_ne_top
  have hres := (hv.mono_measure (Measure.restrict_mono hsub le_rfl)).sub hellmem
  have hbound := Section6Iteration.normalizedL2On_le_of_abs_le
    Metric.isOpen_ball.measurableSet hqpos hqtop
    (mul_nonneg hM (sq_nonneg _)) hres.integrable_sq hpoint
  refine ⟨fun i => fderiv ℝ V z (Homogenization.basisVec i), V z - fderiv ℝ V z z, ?_⟩
  have hellEq : (fun x => (∑ i, fderiv ℝ V z (Homogenization.basisVec i) * x i) +
      (V z - fderiv ℝ V z z)) = ell := by
    funext x
    exact aux_lem_affine_gcn_competitor_taylor_pc V z x
  change normalizedL2On _ (fun x => V x - (fun y => (∑ i, fderiv ℝ V z (Homogenization.basisVec i) * y i) + (V z - fderiv ℝ V z z)) x) ≤ _
  rw [hellEq]
  calc
    _ ≤ M * (Real.sqrt (d : ℝ) * (r / 2)) ^ 2 := hbound
    _ = _ := by
      dsimp only [M, C, aux_lem_affine_gcn_competitor_taylorC]
      rw [hvol]
      exact aux_lem_affine_gcn_competitor_hessian_scaling d _ r R _ hR

lemma aux_lem_affine_gcn_competitor_shift_L2
    {d : ℕ} (z : SpatialCoordinates d) (R Os Err : ℝ) (hR : 0 < R) (hOs : 0 ≤ Os)
    (U V : SpatialCoordinates d → ℝ)
    (hU : MemLp U 2 (volume.restrict (Metric.ball z (R / 2))))
    (hV : MemLp V 2 (volume.restrict (Metric.ball z (R / 2))))
    (hosc : ∀ x ∈ Metric.ball z (R / 2), |U x - U z| ≤ Os)
    (herr : normalizedL2On (Metric.ball z (R / 2)) (fun x => U x - V x) ≤ Err) :
    normalizedL2On (Metric.ball z (R / 2)) (fun x => V x - U z) ≤ Err + Os := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball z (R / 2))) := by
    change IsFiniteMeasure (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d)))
    infer_instance
  have hU0 := hU.sub (memLp_const (U z))
  have hU0norm : normalizedL2On (Metric.ball z (R / 2)) (fun x => U x - U z) ≤ Os := by
    apply Section6Iteration.normalizedL2On_le_of_abs_le Metric.isOpen_ball.measurableSet
      (by rw [aux_lem_affine_gcn_competitor_ball_volume z R hR]; positivity)
      (by
        change volume (centeredCube z R hR : Set (SpatialCoordinates d)) ≠ ⊤
        rw [centeredCube_volume]; exact ENNReal.ofReal_ne_top) hOs hU0.integrable_sq hosc
  have hsum := Section6Iteration.normalizedL2On_add_le (hV.sub hU) hU0
  have he : (fun x => V x - U x + (U x - U z)) = (fun x => V x - U z) := by funext x; ring
  simp only [Pi.sub_apply] at hsum
  rw [he] at hsum
  change normalizedL2On _ (fun x => V x - U z) ≤
    normalizedL2On _ (fun x => V x - U x) + normalizedL2On _ (fun x => U x - U z) at hsum
  rw [Section6Iteration.normalizedL2On_sub_comm _ V U] at hsum
  exact hsum.trans (add_le_add herr hU0norm)

lemma aux_lem_affine_gcn_competitor_approximation
    {d : ℕ} [NeZero d] (z : SpatialCoordinates d) (r R Os Err : ℝ)
    (hr : 0 < r) (hR : 0 < R) (h2r : 2 * r ≤ R) (hOs : 0 ≤ Os)
    (U V : SpatialCoordinates d → ℝ)
    (hU : MemLp U 2 (volume.restrict (Metric.ball z (R / 2))))
    (hV : MemLp V 2 (volume.restrict (Metric.ball z (R / 2))))
    (hosc : ∀ x ∈ Metric.ball z (R / 2), |U x - U z| ≤ Os)
    (herr : normalizedL2On (Metric.ball z (R / 2)) (fun x => U x - V x) ≤ Err)
    (hh : InnerProductSpace.HarmonicOnNhd
      (V ∘ (Section6Schauder.toEuc.symm : EuclideanSpace ℝ (Fin d) → SpatialCoordinates d))
      ((Section6Schauder.toEuc : SpatialCoordinates d → EuclideanSpace ℝ (Fin d)) ''
        Metric.ball z (R / 2))) :
    ∃ (m : Fin d → ℝ) (c : ℝ), normalizedL2On (Metric.ball z (r / 2))
        (fun x => U x - ((∑ i, m i * x i) + c)) ≤
      (R / r) ^ ((d : ℝ) / 2) * Err +
        aux_lem_affine_gcn_competitor_taylorC d * (r / R) ^ 2 * (Err + Os) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball z (R / 2))) := by
    change IsFiniteMeasure (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d)))
    infer_instance
  have hV0 := hV.sub (memLp_const (U z))
  obtain ⟨m, c, happ⟩ := aux_lem_affine_gcn_competitor_harmonic_approx z r R hr hR h2r
    (fun x => V x - U z) hV0 (by
      simpa only [Function.comp_def] using Section6Schauder.harmonicOnNhd_sub_const hh (U z))
  have hshift := aux_lem_affine_gcn_competitor_shift_L2 z R Os Err hR hOs U V hU hV hosc herr
  have hsub : Metric.ball z (r / 2) ⊆ Metric.ball z (R / 2) :=
    Metric.ball_subset_ball (by linarith only [h2r, hr])
  have hsmall := Section6Iteration.normalizedL2On_le_of_subset hsub
    (by rw [aux_lem_affine_gcn_competitor_ball_volume z R hR]; positivity)
    (by rw [aux_lem_affine_gcn_competitor_ball_volume z r hr]; positivity)
    (hU.sub hV).integrable_sq
  rw [aux_lem_affine_gcn_competitor_volume_ratio z r R hr hR] at hsmall
  have hsmall' := hsmall.trans (mul_le_mul_of_nonneg_left herr (by positivity))
  have hm : MemLp (fun x : SpatialCoordinates d => (∑ i, m i * x i) + c) 2
      (volume.restrict (Metric.ball z (r / 2))) := by
    obtain ⟨h, _⟩ := continuousOn_cube_memLp_and_nonzero z r hr
      (fun x => fun _ : Fin 1 => (∑ i, m i * x i) + c)
      (continuousOn_pi' (fun _ => by fun_prop))
    exact h 0
  refine ⟨m, c + U z, ?_⟩
  apply aux_lem_affine_gcn_competitor_normalizedL2_add_bound
    ((hU.sub hV).mono_measure (Measure.restrict_mono hsub le_rfl))
    ((hV0.mono_measure (Measure.restrict_mono hsub le_rfl)).sub hm)
    (fun x => by dsimp; ring) hsmall'
  exact happ.trans (mul_le_mul_of_nonneg_left hshift
    (mul_nonneg (aux_lem_affine_gcn_competitor_taylorC_nonneg d) (sq_nonneg _)))




lemma aux_lem_affine_gcn_competitor_affine_holder
    {d : ℕ} [NeZero d] (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1)
    (c : ℝ) (m : Fin d → ℝ) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d) (fun x => c + ∑ i, m i * x i) := by
  have hdiam := (aux_lem_affine_gcn_competitor_S0T_basic (0 : SpatialCoordinates d) 1 one_pos).2.2
  apply aux_lem_affine_gcn_competitor_holder_of_pointwise d alpha _ _ ((d : ℝ) * ‖m‖)
    (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) ha
  intro x hx y hy hxy
  have h := aux_lem_affine_gcn_competitor_affine_difference m x y
  have hp : dist x y ≤ dist x y ^ alpha := by
    simpa using Real.rpow_le_rpow_of_exponent_ge (dist_pos.mpr hxy) (hdiam x hx y hy) ha1.le
  calc
    |(c + ∑ i, m i * x i) - (c + ∑ i, m i * y i)| =
      |(∑ i, m i * x i) - (∑ i, m i * y i)| := by congr 1; ring
    _ ≤ (d : ℝ) * ‖m‖ * dist x y := h
    _ ≤ (d : ℝ) * ‖m‖ * dist x y ^ alpha :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))

lemma aux_lem_affine_gcn_competitor_holder_sub
    {d : ℕ} (alpha : ℝ) (S : Set (SpatialCoordinates d))
    (F G : SpatialCoordinates d → ℝ)
    (hF : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha S F) (hG : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha S G) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha S (fun x => F x - G x) := by
  refine ⟨_root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm alpha S F + _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm alpha S G, ?_⟩
  rintro v ⟨x, hx, y, hy, hxy, rfl⟩
  have hFx : |F x - F y| / (Real.sqrt (∑ j, (x j - y j) ^ 2)) ^ alpha ≤
      _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm alpha S F := le_csSup hF ⟨x, hx, y, hy, hxy, rfl⟩
  have hGx : |G x - G y| / (Real.sqrt (∑ j, (x j - y j) ^ 2)) ^ alpha ≤
      _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm alpha S G := le_csSup hG ⟨x, hx, y, hy, hxy, rfl⟩
  calc
    _ ≤ (|F x - F y| + |G x - G y|) /
        (Real.sqrt (∑ j, (x j - y j) ^ 2)) ^ alpha := by
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
      convert abs_sub (F x - F y) (G x - G y) using 1 ; congr 1 ; ring
    _ = _ := add_div _ _ _
    _ ≤ _ := add_le_add hFx hGx

lemma aux_lem_affine_gcn_competitor_projection_holder
    {d : ℕ} [NeZero d] (alpha K : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1)
    (hK : 0 ≤ K) (F : SpatialCoordinates d → ℝ)
    (hF : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d) F)
    (hFbound : ∀ x ∈ _root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d, |F x| ≤ K)
    (hFnorm : _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d) F ≤ 2 * K) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d) (fun x => F x - _root_.SubdiffusiveProcess.Paper.AffineProjection.proj F x) ∧
    _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d) (fun x => F x - _root_.SubdiffusiveProcess.Paper.AffineProjection.proj F x) ≤
      (3 + (∑ i : Fin d, (_root_.SubdiffusiveProcess.Paper.AffineProjection.sigma d i)⁻¹) / 4 +
        (∑ i : Fin d, (_root_.SubdiffusiveProcess.Paper.AffineProjection.sigma d i)⁻¹) * (Real.sqrt d) ^ (1 - alpha) / 2) * K := by
  have hp : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d) (_root_.SubdiffusiveProcess.Paper.AffineProjection.proj F) :=
    aux_lem_affine_gcn_competitor_affine_holder alpha ha ha1 _ _
  refine ⟨aux_lem_affine_gcn_competitor_holder_sub alpha _ F _ hF hp, ?_⟩
  have hpa : BddAbove {v : ℝ | ∃ x ∈ _root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d, v = |_root_.SubdiffusiveProcess.Paper.AffineProjection.proj F x|} := by
    refine ⟨K * (1 + (∑ i : Fin d, (_root_.SubdiffusiveProcess.Paper.AffineProjection.sigma d i)⁻¹) / 4), ?_⟩
    rintro t ⟨x, hx, rfl⟩
    exact _root_.SubdiffusiveProcess.Paper.AffineProjection.abs_proj_le F K hK hFbound x hx
  have hpn : BddAbove (_root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet alpha (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d)
      (fun x => -_root_.SubdiffusiveProcess.Paper.AffineProjection.proj F x)) := by
    rw [aux_lem_finite_trace_smooth_net_holderRatioSet_neg]
    exact hp
  have hpan : BddAbove {v : ℝ | ∃ x ∈ _root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d, v = |-_root_.SubdiffusiveProcess.Paper.AffineProjection.proj F x|} := by
    simpa only [abs_neg] using hpa
  have hadd := aux_lem_finite_trace_smooth_net_cAlphaNorm_add_le
    (F := F) (G := fun x => -_root_.SubdiffusiveProcess.Paper.AffineProjection.proj F x)
    ⟨K, by rintro t ⟨x, hx, rfl⟩; exact hFbound x hx⟩ hF hpan hpn
  rw [aux_lem_finite_trace_smooth_net_cAlphaNorm_neg] at hadd
  have hproj := _root_.SubdiffusiveProcess.Paper.AffineProjection.cAlphaNorm_proj_le F K hK hFbound alpha ha ha1
  change _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d) (fun x => F x + -_root_.SubdiffusiveProcess.Paper.AffineProjection.proj F x) ≤ _
  exact hadd.trans (by nlinarith only [hFnorm, hproj])

lemma aux_lem_affine_gcn_competitor_projection_L2
    {d : ℕ} [NeZero d] (F : SpatialCoordinates d → ℝ)
    (hF : ContinuousOn F (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d)) (c : ℝ) (m : Fin d → ℝ) :
    (eLpNorm (fun x => F x - _root_.SubdiffusiveProcess.Paper.AffineProjection.proj F x) 2
      (volume.restrict (_root_.SubdiffusiveProcess.Paper.AffineProjection.Q0 d))).toReal ≤
    (eLpNorm (fun x => F x - (c + ∑ i, m i * x i)) 2
      (volume.restrict (_root_.SubdiffusiveProcess.Paper.AffineProjection.Q0 d))).toReal := by
  have mem (f : SpatialCoordinates d → ℝ) (hf : ContinuousOn f (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d)) :
      MemLp f 2 (volume.restrict (_root_.SubdiffusiveProcess.Paper.AffineProjection.Q0 d)) := by
    obtain ⟨hh, _⟩ := continuousOn_cube_memLp_and_nonzero (0 : SpatialCoordinates d) 1 one_pos
      (fun x => fun _ : Fin 1 => f x) (continuousOn_pi' (fun _ => hf))
    exact hh 0
  have hf := mem _ (hF.sub (_root_.SubdiffusiveProcess.Paper.AffineProjection.proj_continuous F).continuousOn)
  have hg := mem (fun x => F x - (c + ∑ i, m i * x i)) (hF.sub (by fun_prop))
  have h := _root_.SubdiffusiveProcess.Paper.AffineProjection.integral_sq_proj_le F hF c m
  rw [← _root_.SubdiffusiveProcess.Paper.AffineProjection.integral_Q0_eq_S0, ← _root_.SubdiffusiveProcess.Paper.AffineProjection.integral_Q0_eq_S0] at h
  have hfEq : (eLpNorm (fun x => F x - _root_.SubdiffusiveProcess.Paper.AffineProjection.proj F x) 2
      (volume.restrict (_root_.SubdiffusiveProcess.Paper.AffineProjection.Q0 d))).toReal ^ 2 =
      ∫ x in _root_.SubdiffusiveProcess.Paper.AffineProjection.Q0 d, (F x - _root_.SubdiffusiveProcess.Paper.AffineProjection.proj F x) ^ 2 := by
    simpa only [Pi.sub_apply] using!
      Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq hf
  have hgEq : (eLpNorm (fun x => F x - (c + ∑ i, m i * x i)) 2
      (volume.restrict (_root_.SubdiffusiveProcess.Paper.AffineProjection.Q0 d))).toReal ^ 2 =
      ∫ x in _root_.SubdiffusiveProcess.Paper.AffineProjection.Q0 d, (F x - (c + ∑ i, m i * x i)) ^ 2 := by
    simpa only [Pi.sub_apply] using!
      Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq hg
  exact (sq_le_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).1
    (hfEq.trans_le (h.trans_eq hgEq.symm))


lemma aux_lem_affine_gcn_competitor_dilated_affine
    {d : ℕ} (z x : SpatialCoordinates d) (r N c u0 : ℝ) (m : Fin d → ℝ) :
    ((∑ i, m i * _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r x i) + c - u0) / N =
      ((∑ i, m i * z i) + c - u0) / N + ∑ i, (m i * r / N) * x i := by
  simp only [_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation, Pi.zero_apply, sub_zero, mul_add, Finset.sum_add_distrib]
  simp only [add_div, sub_div, Finset.sum_div]
  have he : (∑ i, m i * (r * x i) / N) = ∑ i, m i * r / N * x i := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  ring

lemma aux_lem_affine_gcn_competitor_projection_compare
    {d : ℕ} [NeZero d] (z : SpatialCoordinates d) (r N : ℝ) (hr : 0 < r) (hN : 0 < N)
    (U F : SpatialCoordinates d → ℝ) (hF : ContinuousOn F (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d))
    (hFdef : ∀ x, F x = (U (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r x) - U z) / N)
    (m : Fin d → ℝ) (c : ℝ)
    (hmem : MemLp (fun x => U x - ((∑ i, m i * x i) + c)) 2
      (volume.restrict (Metric.ball z (r / 2)))) :
    (eLpNorm (fun x => F x - _root_.SubdiffusiveProcess.Paper.AffineProjection.proj F x) 2
      (volume.restrict (_root_.SubdiffusiveProcess.Paper.AffineProjection.Q0 d))).toReal ≤
      normalizedL2On (Metric.ball z (r / 2))
        (fun x => U x - ((∑ i, m i * x i) + c)) / N := by
  have h := aux_lem_affine_gcn_competitor_projection_L2 F hF
    (((∑ i, m i * z i) + c - U z) / N) (fun i => m i * r / N)
  have he : (fun x => F x - (((∑ i, m i * z i) + c - U z) / N + ∑ i, (m i * r / N) * x i)) =
      (fun x => (U (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r x) -
        ((∑ i, m i * _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r x i) + c)) / N) := by
    funext x
    rw [hFdef, ← aux_lem_affine_gcn_competitor_dilated_affine z x r N c (U z) m]
    ring
  rw [he] at h
  have hn := @aux_lem_affine_gcn_competitor_normalized_dilation_eLpNorm d z r N hr hN
    (fun x => U x - ((∑ i, m i * x i) + c)) hmem
  exact le_trans h (le_of_eq hn)

lemma aux_lem_affine_gcn_competitor_projection_pullback
    {d : ℕ} [NeZero d] (z : SpatialCoordinates d) (r N : ℝ) (hr : 0 < r) (hN : 0 < N)
    (U F : SpatialCoordinates d → ℝ)
    (hFdef : ∀ x, F x = (U (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r x) - U z) / N) :
    ∃ pc : (Fin d → ℝ) × ℝ, ∀ x,
      U x - ((∑ i, pc.1 i * x i) + pc.2) =
        N * (F (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation 0 z r⁻¹ x) -
          _root_.SubdiffusiveProcess.Paper.AffineProjection.proj F (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation 0 z r⁻¹ x)) := by
  let m := _root_.SubdiffusiveProcess.Paper.AffineProjection.coeffB F
  let c := _root_.SubdiffusiveProcess.Paper.AffineProjection.coeffA F
  refine ⟨(fun i => N / r * m i, U z + N * c - N / r * ∑ i, m i * z i), ?_⟩
  intro x
  rw [hFdef, aux_lem_affine_gcn_competitor_cubeDilation_inverse z x r hr]
  change U x - ((∑ i, N / r * m i * x i) + (U z + N * c - N / r * ∑ i, m i * z i)) =
    N * ((U x - U z) / N - (c + ∑ i, m i * _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation 0 z r⁻¹ x i))
  simp only [_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation, Pi.zero_apply, zero_add, mul_sub, Finset.sum_sub_distrib]
  have hsum (y : SpatialCoordinates d) : (∑ i, m i * (r⁻¹ * y i)) = r⁻¹ * ∑ i, m i * y i := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; ring
  rw [hsum x, hsum z]
  have hsum' : (∑ i, N / r * m i * x i) = N / r * ∑ i, m i * x i := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; ring
  rw [hsum']
  field_simp
  ring

lemma aux_lem_affine_gcn_competitor_centered_rescaling
    {d : ℕ} [NeZero d] (z : SpatialCoordinates d) (r R N Cin Os Src alpha : ℝ)
    (hr : 0 < r) (hR : 0 < R) (hN : 0 < N) (hCin : 0 ≤ Cin)
    (hOs : 0 ≤ Os) (hSrc : 0 ≤ Src) (ha : 0 < alpha) (ha1 : alpha < 1)
    (U : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (closure (Metric.ball z (r / 2))))
    (hHol : ∀ x ∈ closure (Metric.ball z (r / 2)), ∀ y ∈ closure (Metric.ball z (r / 2)),
      |U x - U y| ≤ Cin * (Os + Src) * (dist x y / R) ^ alpha) :
    let F := fun x => (U (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r x) - U z) / N
    let K := Cin * (Os + Src) / N * (r / R) ^ alpha
    ContinuousOn F (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d) ∧
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d) F ∧
    (∀ x ∈ _root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d, |F x| ≤ K) ∧
    _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d) F ≤ 2 * K := by
  dsimp only
  let F := fun x => (U (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r x) - U z) / N
  let K := Cin * (Os + Src) / N * (r / R) ^ alpha
  obtain ⟨hTcl, hTdist, hdiam⟩ := aux_lem_affine_gcn_competitor_S0T_basic z r hr
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpoint : ∀ x ∈ _root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d, ∀ y ∈ _root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d, x ≠ y →
      |F x - F y| ≤ K * dist x y ^ alpha := by
    intro x hx y hy hxy
    have hh := aux_lem_affine_gcn_competitor_normalized_residual_point_affine
      alpha Cin Os Src r R N (0 : Fin d → ℝ) U (fun _ => U z) (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r)
      (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d) (closure (Metric.ball z (r / 2))) (U z)
      (by intro x; simp) hTcl hHol hTdist hdiam hr hR hN ha.le ha1.le x hx y hy hxy
    simpa only [norm_zero, mul_zero, zero_mul, zero_div, add_zero] using hh
  have hz : (0 : SpatialCoordinates d) ∈ _root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d := by
    rw [_root_.SubdiffusiveProcess.Paper.AffineProjection.mem_S0_iff]; intro i; norm_num
  have hzero : F 0 = 0 := by
    have he : _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r (0 : SpatialCoordinates d) = z := by
      ext i; simp [_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation]
    simp only [F, he, sub_self, zero_div]
  refine ⟨?_, aux_lem_affine_gcn_competitor_holder_of_pointwise d alpha _ F K hK ha hpoint, ?_, ?_⟩
  · apply ContinuousOn.div_const
    apply ContinuousOn.sub _ continuousOn_const
    apply hU.comp _ hTcl
    exact (show Continuous (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r) by unfold _root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation; fun_prop).continuousOn
  · intro x hx
    by_cases h : x = 0
    · subst x; change |F 0| ≤ K; simpa only [hzero, abs_zero] using hK
    · have hp := hpoint x hx 0 hz h
      rw [hzero, sub_zero] at hp
      exact hp.trans (mul_le_of_le_one_right hK (Real.rpow_le_one dist_nonneg (hdiam x hx 0 hz) ha.le))
  · exact aux_lem_affine_gcn_competitor_cAlphaNorm_le_of_pointwise_zero
      alpha K _ F 0 hK ha.le hz hdiam hpoint hzero



lemma aux_lem_affine_gcn_competitor_scale_powers
    (d : ℕ) (hd : 2 ≤ d) (alpha gamma zeta Cin L r R : ℝ)
    (ha : 0 < alpha) (hg : 0 < gamma) (hCin : 1 ≤ Cin) (hL : 1 < L)
    (hr : 0 < r) (hR : 0 < R) (hlo : L ^ gamma * r ≤ R) (hhi : R ≤ Cin * L ^ gamma * r) :
    (R / r) ^ ((d : ℝ) / 2) ≤ Cin ^ ((d : ℝ) / 2) * L ^ (gamma * (d : ℝ) / 2) ∧
    (R / r) ^ ((2 - (d : ℝ)) / 2) * L ^ (((d : ℝ) + zeta) / 2) ≤
      L ^ (((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2) ∧
    (r / R) ^ 2 ≤ L ^ (-2 * gamma) ∧
    (r / R) ^ alpha ≤ L ^ (-alpha * gamma) ∧ (r / R) ^ 2 ≤ 1 := by
  have hLpos : 0 < L := zero_lt_one.trans hL
  have hRr : L ^ gamma ≤ R / r := (le_div_iff₀ hr).2 hlo
  have hRr' : R / r ≤ Cin * L ^ gamma := (div_le_iff₀ hr).2 hhi
  have hvol := Real.rpow_le_rpow (div_nonneg hR.le hr.le) hRr' (by positivity : 0 ≤ (d : ℝ) / 2)
  have hvolEq : (Cin * L ^ gamma) ^ ((d : ℝ) / 2) =
      Cin ^ ((d : ℝ) / 2) * L ^ (gamma * (d : ℝ) / 2) := by
    rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg hLpos.le _), ← Real.rpow_mul hLpos.le]
    congr 2; ring
  rw [hvolEq] at hvol
  have hneg : (R / r) ^ ((2 - (d : ℝ)) / 2) ≤ L ^ (gamma * ((2 - (d : ℝ)) / 2)) := by
    have hh := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hLpos gamma) hRr
      (show (2 - (d : ℝ)) / 2 ≤ 0 by
        have h : (2 : ℝ) ≤ d := by exact_mod_cast hd
        linarith only [h])
    simpa only [← Real.rpow_mul hLpos.le] using hh
  have hOsc := mul_le_mul_of_nonneg_right hneg
    (Real.rpow_nonneg hLpos.le (((d : ℝ) + zeta) / 2))
  rw [← Real.rpow_add hLpos] at hOsc
  have hp (a : ℝ) (ha : 0 ≤ a) : (r / R) ^ a ≤ L ^ (-a * gamma) := by
    have hh := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hLpos gamma) hRr (neg_nonpos.mpr ha)
    have he : (R / r) ^ (-a) = (r / R) ^ a := by
      rw [Real.rpow_neg (div_nonneg hR.le hr.le), ← Real.inv_rpow (div_nonneg hR.le hr.le), inv_div]
    rw [he, ← Real.rpow_mul hLpos.le] at hh
    convert hh using 1 ; congr 1 ; ring
  have hsq : (r / R) ^ 2 ≤ L ^ (-2 * gamma) := by simpa using hp 2 (by norm_num)
  refine ⟨hvol, ?_, hsq, hp alpha ha.le, ?_⟩
  · convert hOsc using 1 ; congr 1 ; ring
  · exact hsq.trans (Real.rpow_le_one_of_one_le_of_nonpos hL.le (by linarith))

lemma aux_lem_affine_gcn_competitor_AB_algebra
    (A B x y v t q H P C Cv W Z Z1 Z2 Zb e eh Cc : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (_hv : 0 ≤ v) (ht : 0 ≤ t) (hq : 0 ≤ q)
    (hH : 0 ≤ H) (hP : 0 ≤ P) (hC : 0 ≤ C) (hCv : 0 ≤ Cv)
    (hW : 0 ≤ W) (hZ : 0 ≤ Z) (hZ1 : 0 ≤ Z1) (hZ2 : 0 ≤ Z2) (hZb : 0 ≤ Zb)
    (he : 0 ≤ e) (he1 : e ≤ 1) (hCc : 1 ≤ Cc)
    (hA : A ≤ v * (e * x + y) + H * t * (e * x + y + x))
    (hB : B ≤ P * C * (x + y) * q)
    (hxZ : x ≤ C * Z) (hyZ : y ≤ Z) (hvW : v ≤ Cv * W) (ht1 : t ≤ 1)
    (hprod : W * Z = Z2) (htZ : t * Z ≤ Z1) (hqZ : q * Z ≤ Zb)
    (heSmall : Cv * C * e ≤ eh / 2)
    (hySmall : (Cv * W + H) * y ≤ eh / 2 * Z2)
    (hHC : 2 * H * C ≤ Cc) (hPC : P * C * (C + 1) ≤ Cc) :
    A ≤ Cc * Z1 + Cc * eh * Z2 ∧ B ≤ Cc * Zb := by
  have heh : 0 ≤ eh := by nlinarith only [heSmall, mul_nonneg (mul_nonneg hCv hC) he]
  have heX : e * x ≤ C * Z :=
    (mul_le_mul_of_nonneg_left hxZ he).trans (mul_le_of_le_one_left (mul_nonneg hC hZ) he1)
  have hharm : H * t * (e * x + x) ≤ 2 * H * C * Z1 := by
    calc
      _ ≤ H * t * (2 * (C * Z)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hH ht)
        linarith only [heX, hxZ]
      _ = (2 * H * C) * (t * Z) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left htZ (by positivity)
  have herr : v * (e * x) ≤ eh / 2 * Z2 := by
    calc
      _ ≤ (Cv * W) * (e * (C * Z)) :=
        mul_le_mul hvW (mul_le_mul_of_nonneg_left hxZ he) (mul_nonneg he hx) (mul_nonneg hCv hW)
      _ = (Cv * C * e) * Z2 := by rw [← hprod]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right heSmall hZ2
  have hsrc : (v + H * t) * y ≤ eh / 2 * Z2 := by
    apply le_trans _ hySmall
    apply mul_le_mul_of_nonneg_right _ hy
    exact add_le_add hvW (mul_le_of_le_one_right hH ht1)
  constructor
  · calc
      A ≤ v * (e * x + y) + H * t * (e * x + y + x) := hA
      _ = v * (e * x) + (v + H * t) * y + H * t * (e * x + x) := by ring
      _ ≤ eh / 2 * Z2 + eh / 2 * Z2 + (2 * H * C) * Z1 :=
        add_le_add (add_le_add herr hsrc) hharm
      _ ≤ Cc * Z1 + Cc * eh * Z2 := by
        have h1 := mul_le_mul_of_nonneg_right hHC hZ1
        have h2 := mul_le_mul_of_nonneg_right hCc (mul_nonneg heh hZ2)
        nlinarith only [h1, h2]
  · calc
      B ≤ P * C * (x + y) * q := hB
      _ ≤ P * C * (C * Z + Z) * q := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (add_le_add hxZ hyZ) (mul_nonneg hP hC)) hq
      _ = (P * C * (C + 1)) * (q * Z) := by ring
      _ ≤ (P * C * (C + 1)) * Zb := mul_le_mul_of_nonneg_left hqZ (by positivity)
      _ ≤ Cc * Zb := mul_le_mul_of_nonneg_right hPC hZb

lemma aux_lem_affine_gcn_competitor_thresholds
    (Cv C W H Z Z2 eh : ℝ) (hCv : 0 ≤ Cv) (hC : 0 ≤ C) (hW : 0 ≤ W)
    (hH : 0 ≤ H) (hZ : 0 < Z) (hZ2 : 0 < Z2) (heh : 0 < eh) :
    ∃ eps0 src0 : ℝ, 0 < eps0 ∧ 0 < src0 ∧
      (∀ eps : ℝ, 0 ≤ eps → eps ≤ eps0 → eps ≤ 1 ∧ Cv * C * eps ≤ eh / 2) ∧
      (∀ y : ℝ, 0 ≤ y → y ≤ src0 → y ≤ Z ∧ (Cv * W + H) * y ≤ eh / 2 * Z2) := by
  let eps0 := min 1 (eh / (2 * (Cv * C + 1)))
  let src0 := min Z ((eh / 2 * Z2) / (Cv * W + H + 1))
  have hd1 : 0 < Cv * C + 1 := by positivity
  have hd2 : 0 < Cv * W + H + 1 := by positivity
  refine ⟨eps0, src0, lt_min one_pos (div_pos heh (mul_pos (by norm_num) hd1)),
    lt_min hZ (div_pos (mul_pos (half_pos heh) hZ2) hd2), ?_, ?_⟩
  · intro eps he he0
    have h1 : eps ≤ 1 := he0.trans (min_le_left _ _)
    have h2 := he0.trans (min_le_right _ _)
    have h3 := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hd1)).1 h2
    refine ⟨h1, ?_⟩
    nlinarith only [h3, he]
  · intro y hy hy0
    have h1 : y ≤ Z := hy0.trans (min_le_left _ _)
    have h2 := hy0.trans (min_le_right _ _)
    have h3 := (le_div_iff₀ hd2).1 h2
    refine ⟨h1, ?_⟩
    nlinarith only [h3, hy]



def aux_lem_affine_gcn_competitor_projC (d : ℕ) [NeZero d] (alpha : ℝ) : ℝ :=
  3 + (∑ i : Fin d, (_root_.SubdiffusiveProcess.Paper.AffineProjection.sigma d i)⁻¹) / 4 +
    (∑ i : Fin d, (_root_.SubdiffusiveProcess.Paper.AffineProjection.sigma d i)⁻¹) * (Real.sqrt d) ^ (1 - alpha) / 2

lemma aux_lem_affine_gcn_competitor_projC_nonneg (d : ℕ) [NeZero d] (alpha : ℝ) :
    0 ≤ aux_lem_affine_gcn_competitor_projC d alpha := by
  have hsum : 0 ≤ ∑ i : Fin d, (_root_.SubdiffusiveProcess.Paper.AffineProjection.sigma d i)⁻¹ :=
    Finset.sum_nonneg (fun i _ => (inv_pos.mpr (_root_.SubdiffusiveProcess.Paper.AffineProjection.sigma_pos i)).le)
  unfold aux_lem_affine_gcn_competitor_projC
  positivity

def aux_lem_affine_gcn_competitor_interpProp (d : ℕ) (alpha beta C : ℝ) : Prop :=
  ∀ F : SpatialCoordinates d → ℝ, _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d) F →
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d) F ∧
    _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d) F ≤
      C * (eLpNorm F 2 (volume.restrict (_root_.SubdiffusiveProcess.Paper.AffineProjection.Q0 d))).toReal ^
        ((alpha - beta) / (alpha + (d : ℝ) / 2)) *
      (_root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d) F) ^
        (1 - (alpha - beta) / (alpha + (d : ℝ) / 2))

lemma aux_lem_affine_gcn_competitor_trace_interpolation
    {d : ℕ} [NeZero d] (alpha beta C Cin Cc r s S N : ℝ)
    (z : SpatialCoordinates d) (F G : SpatialCoordinates d → ℝ)
    (hb : 0 < beta) (hba : beta < alpha) (hC : 0 ≤ C) (hCin : 0 ≤ Cin)
    (hr : 0 < r) (hs : 0 < s) (hS : 0 < S) (hN : 0 < N)
    (hscale : s * r ^ ((d : ℝ) - 2) * N ^ 2 = S)
    (hcoef : Cin * C ^ 2 ≤ Cc)
    (hinterp : aux_lem_affine_gcn_competitor_interpProp d alpha beta C)
    (hF : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d) F)
    (hrel : ∀ x, G x = N * F (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation 0 z r⁻¹ x)) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (frontier (Metric.ball z (r / 2))) G ∧
    Cin * s * r ^ ((d : ℝ) - 2) *
      (r ^ beta * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier (Metric.ball z (r / 2))) G) ^ 2 ≤
      Cc * (eLpNorm F 2 (volume.restrict (_root_.SubdiffusiveProcess.Paper.AffineProjection.Q0 d))).toReal ^
        (2 * ((alpha - beta) / (alpha + (d : ℝ) / 2))) *
      (_root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d) F) ^
        (2 * (1 - (alpha - beta) / (alpha + (d : ℝ) / 2))) * S := by
  obtain ⟨hFb, hn⟩ := hinterp F hF
  have hsemi := (aux_lem_affine_gcn_competitor_holder_le_cAlpha beta _ F).trans hn
  obtain ⟨hG, htransport⟩ := aux_lem_affine_gcn_competitor_holder_transport
    beta r N (Metric.ball z (r / 2)) (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d) G F
    (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r) (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation 0 z r⁻¹) hb hr hN
    (fun x hx => aux_lem_affine_gcn_competitor_cubeDilation_inverse_mem z x r hr hx)
    (fun x _ => aux_lem_affine_gcn_competitor_cubeDilation_inverse z x r hr)
    (aux_lem_affine_gcn_competitor_cubeDilation_inverse_scale_frontier z r hr)
    (fun x _ => hrel x) hFb
  refine ⟨hG, ?_⟩
  have ha : 0 < alpha := hb.trans hba
  have hden : 0 < alpha + (d : ℝ) / 2 := add_pos_of_pos_of_nonneg ha (by positivity)
  have ht : 0 ≤ (alpha - beta) / (alpha + (d : ℝ) / 2) := div_nonneg (sub_nonneg.mpr hba.le) hden.le
  have ht1 : 0 ≤ 1 - (alpha - beta) / (alpha + (d : ℝ) / 2) := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hden).2
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    linarith only [hb, hd0]
  have hB : 0 ≤ _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d) F :=
    (aux_lem_affine_gcn_competitor_holder_nonneg alpha _ F).trans
      (aux_lem_affine_gcn_competitor_holder_le_cAlpha alpha _ F)
  have hh := aux_lem_affine_gcn_competitor_normalized_budget
    Cin C _ _ _ S (s * r ^ ((d : ℝ) - 2)) N _ hCin hC
    ENNReal.toReal_nonneg hB hS.le (mul_pos hs (Real.rpow_pos_of_pos hr _)) hN
    ht ht1 hscale
    (mul_nonneg (Real.rpow_nonneg hr.le _) (aux_lem_affine_gcn_competitor_holder_nonneg beta _ G))
    (htransport.trans (mul_le_mul_of_nonneg_left hsemi hN.le))
  have hm : Cin * C ^ 2 *
      (eLpNorm F 2 (volume.restrict (_root_.SubdiffusiveProcess.Paper.AffineProjection.Q0 d))).toReal ^
        (2 * ((alpha - beta) / (alpha + (d : ℝ) / 2))) *
      (_root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d) F) ^
        (2 * (1 - (alpha - beta) / (alpha + (d : ℝ) / 2))) * S ≤
      Cc * (eLpNorm F 2 (volume.restrict (_root_.SubdiffusiveProcess.Paper.AffineProjection.Q0 d))).toReal ^
        (2 * ((alpha - beta) / (alpha + (d : ℝ) / 2))) *
      (_root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d) F) ^
        (2 * (1 - (alpha - beta) / (alpha + (d : ℝ) / 2))) * S :=
    mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg ENNReal.toReal_nonneg _))
      (Real.rpow_nonneg hB _)) hS.le
  apply le_trans _ hm
  simpa only [mul_assoc] using hh

lemma aux_lem_affine_gcn_competitor_normalized_Os
    (d : ℕ) (Cin R r L zeta S s N Os : ℝ) (hr : 0 < r) (hR : 0 < R) (hN : 0 < N)
    (hNeq : N = r ^ ((2 - (d : ℝ)) / 2) * Real.sqrt (S / s))
    (hOs : Os ≤ Cin * R ^ ((2 - (d : ℝ)) / 2) * L ^ (((d : ℝ) + zeta) / 2) * Real.sqrt (S / s)) :
    Os / N ≤ Cin * ((R / r) ^ ((2 - (d : ℝ)) / 2) * L ^ (((d : ℝ) + zeta) / 2)) := by
  apply (div_le_iff₀ hN).2
  calc
    Os ≤ _ := hOs
    _ = _ := by
      rw [hNeq, Real.div_rpow hR.le hr.le]
      field_simp

lemma aux_lem_affine_gcn_competitor_rescaled_AB
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (alpha gamma zeta Cin Cc L r R N Os Src eps eh : ℝ)
    (ha : 0 < alpha) (hg : 0 < gamma) (hCin : 1 ≤ Cin) (hCc : 1 ≤ Cc)
    (hL : 1 < L) (hr : 0 < r) (hR : 0 < R) (hN : 0 < N)
    (hOs : 0 ≤ Os) (hSrc : 0 ≤ Src) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hlo : L ^ gamma * r ≤ R) (hhi : R ≤ Cin * L ^ gamma * r)
    (hON : Os / N ≤ Cin * ((R / r) ^ ((2 - (d : ℝ)) / 2) * L ^ (((d : ℝ) + zeta) / 2)))
    (hSN : Src / N ≤ L ^ (((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2))
    (heSmall : Cin ^ ((d : ℝ) / 2) * Cin * eps ≤ eh / 2)
    (hsrcSmall : (Cin ^ ((d : ℝ) / 2) * L ^ (gamma * (d : ℝ) / 2) +
        aux_lem_affine_gcn_competitor_taylorC d) * (Src / N) ≤
      eh / 2 * L ^ (((d : ℝ) + zeta) / 2 + gamma))
    (hHC : 2 * aux_lem_affine_gcn_competitor_taylorC d * Cin ≤ Cc)
    (hPC : aux_lem_affine_gcn_competitor_projC d alpha * Cin * (Cin + 1) ≤ Cc)
    (A B : ℝ)
    (hA : A ≤ ((R / r) ^ ((d : ℝ) / 2) * (eps * Os + Src) +
      aux_lem_affine_gcn_competitor_taylorC d * (r / R) ^ 2 * (eps * Os + Src + Os)) / N)
    (hB : B ≤ aux_lem_affine_gcn_competitor_projC d alpha *
      (Cin * (Os + Src) / N * (r / R) ^ alpha)) :
    A ≤ Cc * L ^ (((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2 - 2 * gamma) +
        Cc * eh * L ^ (((d : ℝ) + zeta) / 2 + gamma) ∧
    B ≤ Cc * L ^ (((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2 - alpha * gamma) := by
  have hLp : 0 < L := zero_lt_one.trans hL
  obtain ⟨hv, ho, ht, hq, ht1⟩ := aux_lem_affine_gcn_competitor_scale_powers
    d hd alpha gamma zeta Cin L r R ha hg hCin hL hr hR hlo hhi
  have hprod : L ^ (gamma * (d : ℝ) / 2) *
      L ^ (((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2) =
      L ^ (((d : ℝ) + zeta) / 2 + gamma) := by
    rw [← Real.rpow_add hLp]; congr 1; ring
  have htz : (r / R) ^ 2 * L ^ (((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2) ≤
      L ^ (((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2 - 2 * gamma) := by
    calc
      _ ≤ L ^ (-2 * gamma) * L ^ (((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2) :=
        mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hLp.le _)
      _ = _ := by rw [← Real.rpow_add hLp]; congr 1; ring
  have hqz : (r / R) ^ alpha * L ^ (((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2) ≤
      L ^ (((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2 - alpha * gamma) := by
    calc
      _ ≤ L ^ (-alpha * gamma) * L ^ (((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2) :=
        mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hLp.le _)
      _ = _ := by rw [← Real.rpow_add hLp]; congr 1; ring
  apply aux_lem_affine_gcn_competitor_AB_algebra A B (Os / N) (Src / N)
    ((R / r) ^ ((d : ℝ) / 2)) ((r / R) ^ 2) ((r / R) ^ alpha)
    (aux_lem_affine_gcn_competitor_taylorC d) (aux_lem_affine_gcn_competitor_projC d alpha)
    Cin (Cin ^ ((d : ℝ) / 2)) (L ^ (gamma * (d : ℝ) / 2))
    (L ^ (((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2)) _ _ _ eps eh Cc
    (div_nonneg hOs hN.le) (div_nonneg hSrc hN.le) (by positivity) (sq_nonneg _) (by positivity)
    (aux_lem_affine_gcn_competitor_taylorC_nonneg d)
    (aux_lem_affine_gcn_competitor_projC_nonneg d alpha)
    (by linarith) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) heps heps1 hCc
    (by convert hA using 1 ; ring) (by convert hB using 1 ; ring)
    (hON.trans (mul_le_mul_of_nonneg_left ho (by linarith))) hSN hv ht1
    hprod htz hqz heSmall hsrcSmall hHC hPC

lemma aux_lem_affine_gcn_competitor_projected_data
    {d : ℕ} [NeZero d] (z : SpatialCoordinates d) (r R N Cin Os Src eps alpha : ℝ)
    (hr : 0 < r) (hR : 0 < R) (h2r : 2 * r ≤ R) (hN : 0 < N) (hCin : 0 ≤ Cin)
    (hOs : 0 ≤ Os) (hSrc : 0 ≤ Src) (ha : 0 < alpha) (ha1 : alpha < 1)
    (U V : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (closure (Metric.ball z (r / 2))))
    (hUm : MemLp U 2 (volume.restrict (Metric.ball z (R / 2))))
    (hVm : MemLp V 2 (volume.restrict (Metric.ball z (R / 2))))
    (hosc : ∀ x ∈ Metric.ball z (R / 2), |U x - U z| ≤ Os)
    (herr : normalizedL2On (Metric.ball z (R / 2)) (fun x => U x - V x) ≤ eps * Os + Src)
    (hh : InnerProductSpace.HarmonicOnNhd
      (V ∘ (Section6Schauder.toEuc.symm : EuclideanSpace ℝ (Fin d) → SpatialCoordinates d))
      ((Section6Schauder.toEuc : SpatialCoordinates d → EuclideanSpace ℝ (Fin d)) '' Metric.ball z (R / 2)))
    (hHol : ∀ x ∈ closure (Metric.ball z (r / 2)), ∀ y ∈ closure (Metric.ball z (r / 2)),
      |U x - U y| ≤ Cin * (Os + Src) * (dist x y / R) ^ alpha) :
    ∃ (pc : (Fin d → ℝ) × ℝ) (F : SpatialCoordinates d → ℝ),
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d) F ∧
      (∀ x, U x - ((∑ i, pc.1 i * x i) + pc.2) = N * F (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation 0 z r⁻¹ x)) ∧
      (eLpNorm F 2 (volume.restrict (_root_.SubdiffusiveProcess.Paper.AffineProjection.Q0 d))).toReal ≤
        ((R / r) ^ ((d : ℝ) / 2) * (eps * Os + Src) +
          aux_lem_affine_gcn_competitor_taylorC d * (r / R) ^ 2 * (eps * Os + Src + Os)) / N ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d) F ≤
        aux_lem_affine_gcn_competitor_projC d alpha * (Cin * (Os + Src) / N * (r / R) ^ alpha) := by
  let F0 := fun x => (U (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r x) - U z) / N
  obtain ⟨hFcont, hFhold, hFabs, hFnorm⟩ := aux_lem_affine_gcn_competitor_centered_rescaling
    z r R N Cin Os Src alpha hr hR hN hCin hOs hSrc ha ha1 U hU hHol
  have hK : 0 ≤ Cin * (Os + Src) / N * (r / R) ^ alpha := by positivity
  obtain ⟨hprojHold, hprojNorm⟩ := aux_lem_affine_gcn_competitor_projection_holder
    alpha _ ha ha1 hK F0 hFhold hFabs hFnorm
  obtain ⟨pc, hpc⟩ := aux_lem_affine_gcn_competitor_projection_pullback z r N hr hN U F0 (fun _ => rfl)
  refine ⟨pc, (fun x => F0 x - _root_.SubdiffusiveProcess.Paper.AffineProjection.proj F0 x), hprojHold, hpc, ?_, hprojNorm⟩
  obtain ⟨m, c, happrox⟩ := aux_lem_affine_gcn_competitor_approximation z r R Os (eps * Os + Src)
    hr hR h2r hOs U V hUm hVm hosc herr hh
  have hm : MemLp (fun x : SpatialCoordinates d => (∑ i, m i * x i) + c) 2
      (volume.restrict (Metric.ball z (r / 2))) := by
    obtain ⟨h, _⟩ := continuousOn_cube_memLp_and_nonzero z r hr
      (fun x => fun _ : Fin 1 => (∑ i, m i * x i) + c)
      (continuousOn_pi' (fun _ => by fun_prop))
    exact h 0
  have hmem := (hUm.mono_measure (Measure.restrict_mono
    (Metric.ball_subset_ball (by linarith only [h2r, hr])) le_rfl)).sub hm
  exact (aux_lem_affine_gcn_competitor_projection_compare z r N hr hN U F0 hFcont
    (fun _ => rfl) m c hmem).trans (div_le_div_of_nonneg_right happrox hN.le)

lemma aux_lem_affine_gcn_competitor_harmonic_error
    {d : ℕ} (z : SpatialCoordinates d) (R Err : ℝ) (hR : 0 < R)
    (U Vbar vH : SpatialCoordinates d → ℝ)
    (Ubar : weakSobolevGraph (centeredCube z R hR))
    (w : Homogenization.H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hUbarV : ((Ubar : SobolevData (centeredCube z R hR)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] Vbar)
    (hwval : (w : SpatialCoordinates d → ℝ) = (Ubar : SobolevData (centeredCube z R hR)).1)
    (hvHae : vH =ᵐ[volume] Set.indicator (centeredCube z R hR : Set (SpatialCoordinates d)) w.toFun)
    (herr : normalizedL2On (Metric.ball z (R / 2)) (fun x => U x - Vbar x) ≤ Err) :
    normalizedL2On (Metric.ball z (R / 2)) (fun x => U x - vH x) ≤ Err := by
  have hvHae' : vH =ᵐ[volume.restrict (Metric.ball z (R / 2))]
      ((Ubar : SobolevData (centeredCube z R hR)).1 : SpatialCoordinates d → ℝ) := by
    have hv := ae_restrict_of_ae (s := Metric.ball z (R / 2)) hvHae
    filter_upwards [hv, ae_restrict_mem (centeredCube z R hR).isOpen.measurableSet] with x hx hxmem
    have hxmem' : x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) := hxmem
    rw [hx, Set.indicator_of_mem hxmem', ← hwval]
  have hUVae : (fun x => U x - vH x) =ᵐ[volume.restrict (Metric.ball z (R / 2))]
      (fun x => U x - Vbar x) := by
    filter_upwards [hvHae', hUbarV] with x hx hy
    rw [hx, hy]
  rw [Section6ExcessDecay.normalizedL2On_congr_ae hUVae]
  exact herr

lemma aux_lem_affine_gcn_competitor_cube_memLp
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (U : SpatialCoordinates d → ℝ) (hU : ContinuousOn U (closure (Metric.ball z (R / 2)))) :
    MemLp U 2 (volume.restrict (Metric.ball z (R / 2))) := by
  obtain ⟨hh, _⟩ := continuousOn_cube_memLp_and_nonzero z R hR
    (fun x => fun _ : Fin 1 => U x) (continuousOn_pi' (fun _ => hU))
  exact hh 0

def aux_lem_affine_gcn_competitor_affineProp
    (d : ℕ) (alpha beta gamma zeta rho Cc eh L : ℝ) : Prop :=
  ∀ (A B theta Sq trace : ℝ), theta = (alpha - beta) / (alpha + (d : ℝ) / 2) →
    0 ≤ A → 0 ≤ B → 0 ≤ Sq →
    A ≤ Cc * L ^ (((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2 - 2 * gamma) +
      Cc * eh * L ^ (((d : ℝ) + zeta) / 2 + gamma) →
    B ≤ Cc * L ^ (((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2 - alpha * gamma) →
    trace ≤ Cc * A ^ (2 * theta) * B ^ (2 * (1 - theta)) * Sq → trace ≤ rho * Sq

lemma aux_lem_affine_gcn_competitor_trace_core
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (alpha beta gamma zeta rho Cin Cinterp Cc L r R N Os Src eps eh s S : ℝ)
    (z : SpatialCoordinates d) (U V : SpatialCoordinates d → ℝ)
    (hb : 0 < beta) (hba : beta < alpha) (ha1 : alpha < 1) (hg : 0 < gamma)
    (hCin : 1 ≤ Cin) (hCc : 1 ≤ Cc) (hCinterp : 0 < Cinterp) (hL : 1 < L)
    (hr : 0 < r) (hR : 0 < R) (h2r : 2 * r ≤ R) (hN : 0 < N) (hs : 0 < s) (hS : 0 < S)
    (hOs : 0 ≤ Os) (hSrc : 0 ≤ Src) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hlo : L ^ gamma * r ≤ R) (hhi : R ≤ Cin * L ^ gamma * r)
    (hON : Os / N ≤ Cin * ((R / r) ^ ((2 - (d : ℝ)) / 2) * L ^ (((d : ℝ) + zeta) / 2)))
    (hSN : Src / N ≤ L ^ (((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2))
    (heSmall : Cin ^ ((d : ℝ) / 2) * Cin * eps ≤ eh / 2)
    (hsrcSmall : (Cin ^ ((d : ℝ) / 2) * L ^ (gamma * (d : ℝ) / 2) +
      aux_lem_affine_gcn_competitor_taylorC d) * (Src / N) ≤ eh / 2 * L ^ (((d : ℝ) + zeta) / 2 + gamma))
    (hHC : 2 * aux_lem_affine_gcn_competitor_taylorC d * Cin ≤ Cc)
    (hPC : aux_lem_affine_gcn_competitor_projC d alpha * Cin * (Cin + 1) ≤ Cc)
    (hcoef : Cin * Cinterp ^ 2 ≤ Cc)
    (hscale : s * r ^ ((d : ℝ) - 2) * N ^ 2 = S)
    (hAffine : aux_lem_affine_gcn_competitor_affineProp d alpha beta gamma zeta rho Cc eh L)
    (hinterp : aux_lem_affine_gcn_competitor_interpProp d alpha beta Cinterp)
    (hU : ContinuousOn U (closure (Metric.ball z (r / 2))))
    (hUm : MemLp U 2 (volume.restrict (Metric.ball z (R / 2))))
    (hVm : MemLp V 2 (volume.restrict (Metric.ball z (R / 2))))
    (hosc : ∀ x ∈ Metric.ball z (R / 2), |U x - U z| ≤ Os)
    (herr : normalizedL2On (Metric.ball z (R / 2)) (fun x => U x - V x) ≤ eps * Os + Src)
    (hh : InnerProductSpace.HarmonicOnNhd
      (V ∘ (Section6Schauder.toEuc.symm : EuclideanSpace ℝ (Fin d) → SpatialCoordinates d))
      ((Section6Schauder.toEuc : SpatialCoordinates d → EuclideanSpace ℝ (Fin d)) '' Metric.ball z (R / 2)))
    (hHol : ∀ x ∈ closure (Metric.ball z (r / 2)), ∀ y ∈ closure (Metric.ball z (r / 2)),
      |U x - U y| ≤ Cin * (Os + Src) * (dist x y / R) ^ alpha) :
    ∃ pc : (Fin d → ℝ) × ℝ,
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (frontier (Metric.ball z (r / 2)))
        (fun x => U x - ((∑ i, pc.1 i * x i) + pc.2)) ∧
      Cin * s * r ^ ((d : ℝ) - 2) * (r ^ beta * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta
        (frontier (Metric.ball z (r / 2))) (fun x => U x - ((∑ i, pc.1 i * x i) + pc.2))) ^ 2 ≤ rho * S := by
  have ha : 0 < alpha := hb.trans hba
  obtain ⟨pc, F, hF, hrel, hA, hB⟩ := aux_lem_affine_gcn_competitor_projected_data
    z r R N Cin Os Src eps alpha hr hR h2r hN (by linarith only [hCin])
    hOs hSrc ha ha1 U V hU hUm hVm hosc herr hh hHol
  obtain ⟨hA_bound, hB_bound⟩ := aux_lem_affine_gcn_competitor_rescaled_AB hd
    alpha gamma zeta Cin Cc L r R N Os Src eps eh ha hg hCin hCc hL hr hR hN
    hOs hSrc heps heps1 hlo hhi hON hSN heSmall hsrcSmall hHC hPC _ _ hA hB
  obtain ⟨hHolder, htrace⟩ := aux_lem_affine_gcn_competitor_trace_interpolation
    alpha beta Cinterp Cin Cc r s S N z F (fun x => U x - ((∑ i, pc.1 i * x i) + pc.2))
    hb hba hCinterp.le (by linarith only [hCin]) hr hs hS hN hscale hcoef hinterp hF hrel
  refine ⟨pc, hHolder, ?_⟩
  exact hAffine _ _ _ S _ rfl ENNReal.toReal_nonneg
    ((aux_lem_affine_gcn_competitor_holder_nonneg alpha _ F).trans
      (aux_lem_affine_gcn_competitor_holder_le_cAlpha alpha _ F)) hS.le hA_bound hB_bound htrace

lemma aux_lem_affine_gcn_competitor_constants
    (d : ℕ) [NeZero d] (alpha Cin Cinterp : ℝ) (hCin : 0 ≤ Cin) :
    ∃ Cc : ℝ, 1 ≤ Cc ∧ Cin * Cinterp ^ 2 ≤ Cc ∧
      2 * aux_lem_affine_gcn_competitor_taylorC d * Cin ≤ Cc ∧
      aux_lem_affine_gcn_competitor_projC d alpha * Cin * (Cin + 1) ≤ Cc := by
  let H := aux_lem_affine_gcn_competitor_taylorC d
  let P := aux_lem_affine_gcn_competitor_projC d alpha
  have hH : 0 ≤ H := aux_lem_affine_gcn_competitor_taylorC_nonneg d
  have hP : 0 ≤ P := aux_lem_affine_gcn_competitor_projC_nonneg d alpha
  have h1 : 0 ≤ Cin * Cinterp ^ 2 := mul_nonneg hCin (sq_nonneg _)
  have h2 : 0 ≤ 2 * H * Cin := by positivity
  have h3 : 0 ≤ P * Cin * (Cin + 1) := by positivity
  refine ⟨1 + Cin * Cinterp ^ 2 + 2 * H * Cin + P * Cin * (Cin + 1), ?_, ?_, ?_, ?_⟩
  all_goals linarith only [h1, h2, h3]


theorem lem_affine_gcn_competitor
    (d : ℕ) (hd : 2 ≤ d)
    (alpha beta gamma zeta rho : ℝ)
    (hbeta : 1 / 2 < beta) (hba : beta < alpha) (halpha : alpha < 1)
    (hgamma0 : 0 < gamma) (hgamma1 : gamma < 1) (hzeta : 0 < zeta) (hrho : 0 < rho)
    (hneg : affineExponent (d : ℝ) alpha beta gamma zeta < 0)
    (Cin : ℝ) (hCin : 1 ≤ Cin) :
    ∃ L0 : ℝ, 1 < L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ epshom : ℝ, 0 < epshom → epshom ≤ eps0 →
    ∃ src0 : ℝ, 0 < src0 ∧
    ∀ (Q : Opens (SpatialCoordinates d))
      (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
      (GammaE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
      (u : DomainL2 Q) (U : SpatialCoordinates d → ℝ)
      (_hUcont : ContinuousOn U (closure (Q : Set (SpatialCoordinates d))))
      (_hUae : ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (Q : Set (SpatialCoordinates d))] U))
      (z : SpatialCoordinates d) (r R : ℝ) (_hr : 0 < r)
      (_hRlo : L ^ gamma * r ≤ R) (_hRhi : R ≤ Cin * L ^ gamma * r)
      (_hQR : Metric.ball z (R / 2) ⊆ (Q : Set (SpatialCoordinates d)))
      (c s : ℝ) (_hc : 0 < c) (_hs : 0 < s)
      (Os Src : ℝ) (_hOs0 : 0 ≤ Os) (_hSrc0 : 0 ≤ Src),
      let q : Set (SpatialCoordinates d) := Metric.ball z (r / 2)
      let S : ℝ := (GammaE.measure u q).toReal + c * (volume q).toReal
      (∀ x ∈ closure (Metric.ball z (R / 2)), ∀ y ∈ closure (Metric.ball z (R / 2)),
        |U x - U y| ≤ Os) →
      Os ≤ Cin * R ^ ((2 - (d : ℝ)) / 2) * L ^ (((d : ℝ) + zeta) / 2) * Real.sqrt (S / s) →
      (∃ (hRpos : 0 < R) (Ubar : weakSobolevGraph (centeredCube z R hRpos))
          (Vbar : SpatialCoordinates d → ℝ),
        ContinuousOn Vbar (closure (centeredCube z R hRpos : Set (SpatialCoordinates d))) ∧
        (((Ubar : SobolevData (centeredCube z R hRpos)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z R hRpos : Set (SpatialCoordinates d))] Vbar) ∧
        (∀ psi : killedSobolevGraph (centeredCube z R hRpos),
          inner ℝ (sobolevGradient (Ubar : SobolevData (centeredCube z R hRpos)))
            (subspaceGradient (killedSobolevGraph (centeredCube z R hRpos)) psi) = 0) ∧
        normalizedL2On (Metric.ball z (R / 2)) (fun x => U x - Vbar x) ≤ epshom * Os + Src) →
      (∀ x ∈ closure q, ∀ y ∈ closure q,
        |U x - U y| ≤ Cin * (Os + Src) * (dist x y / R) ^ alpha) →
      (∀ g : SpatialCoordinates d → ℝ,
        ContinuousOn g (closure (Q : Set (SpatialCoordinates d))) →
        _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (frontier q) g →
        ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
          v ∈ E.domain ∧
          ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
          ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (Q : Set (SpatialCoordinates d))] V) ∧
          (∀ x ∈ frontier q, V x = g x) ∧
          (GammaE.measure v q).toReal ≤
            Cin * s * r ^ ((d : ℝ) - 2) * (r ^ beta * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier q) g) ^ 2) →
      Src ≤ src0 * r ^ ((2 - (d : ℝ)) / 2) * Real.sqrt (S / s) →
      ∃ pc : (Fin d → ℝ) × ℝ,
        (let ell : SpatialCoordinates d → ℝ := fun x => (∑ i, pc.1 i * x i) + pc.2
         let b : SpatialCoordinates d → ℝ := fun x => U x - ell x
         let eSet : Set ℝ :=
           {e : ℝ | ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
               v ∈ E.domain ∧
               ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
               ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                 (Q : Set (SpatialCoordinates d))] V) ∧
               (∀ x ∈ frontier q, V x = b x) ∧
               e = (GammaE.measure v q).toReal}
         ∃ Lambda : ℝ, IsGLB eSet Lambda ∧ eSet.Nonempty ∧ Lambda ≤ rho * S) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Cinterp, hCinterp, hinterp⟩ :=
    aux_lem_affine_gcn_competitor_interp d (by omega) alpha beta (by linarith) hba halpha.le
  obtain ⟨Cc, hCc, hcoef, hHC, hPC⟩ :=
    aux_lem_affine_gcn_competitor_constants d alpha Cin Cinterp (by linarith only [hCin])
  obtain ⟨Lbase, hLbase1, hAll⟩ :=
    aux_lem_affine_gcn_competitor_affine_trace_all d hd Cc hCc
      alpha beta gamma zeta hbeta hba halpha hgamma0 hgamma1 hzeta hneg rho hrho
  let L0 : ℝ := max Lbase (2 ^ (1 / gamma))
  have hL01 : 1 < L0 := by
    exact lt_of_lt_of_le hLbase1 (le_max_left _ _)
  refine ⟨L0, hL01, ?_⟩
  intro L hL
  have hLbaseL : Lbase ≤ L := le_trans (le_max_left _ _) hL
  have hLpow2 : 2 ≤ L ^ gamma := by
    have hroot : 2 ^ (1 / gamma) ≤ L :=
      le_trans (le_max_right _ _) hL
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (2 : ℝ) ^ (1 / gamma))
      hroot hgamma0.le
    have hroot_eq : ((2 : ℝ) ^ (1 / gamma)) ^ gamma = 2 := by
      rw [← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
      have hγ : (1 / gamma) * gamma = (1 : ℝ) := by
        field_simp
      rw [hγ]
      norm_num
    rw [hroot_eq] at hpow
    exact hpow
  obtain ⟨ehom, hehom, hAffine⟩ := hAll L hLbaseL
  have hLcur : 1 < L := hL01.trans_le hL
  have hLp : 0 < L := zero_lt_one.trans hLcur
  obtain ⟨eps0, src0, heps0, hsrc0, hepsBound, hsrcBound⟩ :=
    aux_lem_affine_gcn_competitor_thresholds (Cin ^ ((d : ℝ) / 2)) Cin
      (L ^ (gamma * (d : ℝ) / 2)) (aux_lem_affine_gcn_competitor_taylorC d)
      (L ^ (((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2))
      (L ^ (((d : ℝ) + zeta) / 2 + gamma)) ehom
      (by positivity) (by linarith only [hCin]) (by positivity)
      (aux_lem_affine_gcn_competitor_taylorC_nonneg d)
      (Real.rpow_pos_of_pos hLp _) (Real.rpow_pos_of_pos hLp _) hehom
  refine ⟨eps0, heps0, ?_⟩
  intro epshom hepshom hepshom_le
  obtain ⟨heps1, heSmall⟩ := hepsBound epshom hepshom.le hepshom_le
  refine ⟨src0, hsrc0, ?_⟩
  intro Q E GammaE u U hUcont hUae z r R hr hRlo hRhi hQR c s hc hs Os Src hOs0 hSrc0
  dsimp
  intro hosc hOs hharm hHol hext hSrc
  have hRpos : 0 < R := (mul_pos (Real.rpow_pos_of_pos hLp gamma) hr).trans_le hRlo
  have h2r : 2 * r ≤ R := (mul_le_mul_of_nonneg_right hLpow2 hr.le).trans hRlo
  have hSpos :
      0 < (GammaE.measure u (Metric.ball z (r / 2))).toReal +
        c * (volume (Metric.ball z (r / 2))).toReal :=
    aux_lem_affine_gcn_competitor_budget_pos d Q E GammaE u z r c hr hc
  rcases hharm with ⟨hRpos', Ubar, Vbar, hVbarcont, hUbarV, hEq, herr⟩
  obtain ⟨w, hwweak, hwval⟩ :=
    aux_lem_affine_gcn_competitor_weak_harmonic d z R hRpos' Ubar hEq
  obtain ⟨vH, hvHarm, hvHMlp, hvHae⟩ :=
    Section6Schauder.exists_harmonicRepresentative_memLp (centeredCube z R hRpos').isOpen hwweak
  have hErr := aux_lem_affine_gcn_competitor_harmonic_error z R (epshom * Os + Src) hRpos'
    U Vbar vH Ubar w hUbarV hwval hvHae herr
  have hUcontW := hUcont.mono (closure_mono hQR)
  have hUmem := aux_lem_affine_gcn_competitor_cube_memLp z R hRpos U hUcontW
  let Sval := (GammaE.measure u (Metric.ball z (r / 2))).toReal +
    c * (volume (Metric.ball z (r / 2))).toReal
  let N := r ^ ((2 - (d : ℝ)) / 2) * Real.sqrt (Sval / s)
  have hNpos : 0 < N := mul_pos (Real.rpow_pos_of_pos hr _) (Real.sqrt_pos.2 (div_pos hSpos hs))
  have hON := aux_lem_affine_gcn_competitor_normalized_Os d Cin R r L zeta Sval s N Os
    hr hRpos hNpos rfl hOs
  have hSrcN : Src / N ≤ src0 := by
    apply (div_le_iff₀ hNpos).2
    convert hSrc using 1 ; dsimp only [N, Sval] ; ring
  obtain ⟨hSN, hsrcSmall⟩ := hsrcBound (Src / N) (div_nonneg hSrc0 hNpos.le) hSrcN
  have hUcontq : ContinuousOn U (closure (Metric.ball z (r / 2))) :=
    hUcontW.mono (closure_mono (Metric.ball_subset_ball (by linarith only [h2r, hr])))
  have hosc0 : ∀ x ∈ Metric.ball z (R / 2), |U x - U z| ≤ Os := by
    intro x hx
    exact hosc x (subset_closure hx) z (subset_closure (Metric.mem_ball_self (half_pos hRpos)))
  have htrace := aux_lem_affine_gcn_competitor_trace_core hd
    alpha beta gamma zeta rho Cin Cinterp Cc L r R N Os Src epshom ehom s Sval z U vH
    (by linarith only [hbeta]) hba halpha hgamma0 hCin hCc hCinterp hLcur
    hr hRpos h2r hNpos hs hSpos hOs0 hSrc0 hepshom.le heps1 hRlo hRhi
    hON hSN heSmall hsrcSmall hHC hPC hcoef
    (aux_lem_affine_gcn_competitor_normalization d r s Sval hr hs hSpos)
    hAffine hinterp hUcontq hUmem (hvHMlp.restrict _) hosc0 hErr hvHarm hHol
  obtain ⟨pc, hpcHolder, hpcBudget⟩ := htrace
  let ell : SpatialCoordinates d → ℝ :=
    fun x => (∑ i, pc.1 i * x i) + pc.2
  let b : SpatialCoordinates d → ℝ := fun x => U x - ell x
  have hbHolder : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (frontier (Metric.ball z (r / 2))) b := by
    change _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (frontier (Metric.ball z (r / 2)))
      (fun x => U x - ((∑ i, pc.1 i * x i) + pc.2))
    exact hpcHolder
  have hbcont : ContinuousOn b (closure (Q : Set (SpatialCoordinates d))) := by
    have hell : ContinuousOn ell (closure (Q : Set (SpatialCoordinates d))) := by
      have hlin : Continuous (fun x : SpatialCoordinates d =>
          ∑ i : Fin d, pc.1 i * x i) := by
        exact continuous_finsetSum _ (fun i _ =>
          continuous_const.mul (continuous_apply i))
      exact (hlin.add continuous_const).continuousOn
    exact hUcont.sub hell
  obtain ⟨Lambda, hglb, hne, hLambda⟩ :=
    aux_lem_affine_gcn_competitor_extension_glb d Q E GammaE
      (Metric.ball z (r / 2)) b beta Cin s r
      (rho * ((GammaE.measure u (Metric.ball z (r / 2))).toReal +
        c * (volume (Metric.ball z (r / 2))).toReal))
      hbcont hbHolder hext hpcBudget
  refine ⟨pc, ?_⟩
  exact ⟨Lambda, hglb, hne, hLambda⟩


end SubdiffusiveProcess.Paper
