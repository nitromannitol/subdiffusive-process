import SubdiffusiveProcess.Lane2.BoundaryResponse
import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.SmoothRepresentative
import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.PointwiseBounds
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess
open Filter MeasureTheory Set TopologicalSpace Metric
open Homogenization
open scoped ContDiff
open scoped NNReal
open scoped Topology
open scoped ENNReal

namespace Paper

lemma aux_lem_finite_trace_smooth_density_extend
    {d : ℕ} (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (K : ℝ≥0)
    (f : SpatialCoordinates d → ℝ) (S : Set (SpatialCoordinates d))
    (hf : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ (K : ℝ) * (dist x y)^a) :
    ∃ F : SpatialCoordinates d → ℝ,
      (∀ x y, |F x - F y| ≤ (K : ℝ) * (dist x y)^a) ∧ EqOn F f S := by
  let D : SpatialCoordinates d → SpatialCoordinates d → ℝ := fun x y => dist x y
  let inst : PseudoMetricSpace (SpatialCoordinates d) :=
    { dist := fun x y => (D x y) ^ a
      dist_self := by intro x; simp [D, Real.zero_rpow ha.ne']
      dist_comm := by intro x y; simp [D, dist_comm]
      dist_triangle := by
        intro x y z
        rw [show D x z = dist x z from rfl]
        calc
          (dist x z)^a ≤ (dist x y + dist y z)^a := by
            gcongr
            exact dist_triangle _ _ _
          _ ≤ (dist x y)^a + (dist y z)^a := by
            exact Real.rpow_add_le_add_rpow (dist_nonneg) (dist_nonneg) ha.le ha1 }
  letI : PseudoMetricSpace (SpatialCoordinates d) := inst
  letI : PseudoEMetricSpace (SpatialCoordinates d) := inst.toPseudoEMetricSpace
  have hlip : LipschitzOnWith (K : ℝ≥0) f S := by
    intro x hx y hy
    rw [edist_dist, @edist_dist _ inst x y, ENNReal.coe_nnreal_eq]
    change ENNReal.ofReal (dist (f x) (f y)) ≤
      ENNReal.ofReal (K : ℝ) * ENNReal.ofReal (@dist _ inst.toDist x y)
    rw [← ENNReal.ofReal_mul K.coe_nonneg]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.dist_eq]
    simpa [D] using hf x hx y hy
  obtain ⟨F, hF, hFs⟩ :=
    LipschitzOnWith.extend_real (α := SpatialCoordinates d) hlip
  refine ⟨F, ?_, hFs.symm⟩
  intro x y
  have hh := hF x y
  change |F x - F y| ≤ (K : ℝ) * (D x y)^a
  rw [edist_dist, @edist_dist _ inst x y, ENNReal.coe_nnreal_eq,
    ← ENNReal.ofReal_mul K.coe_nonneg,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hh
  simpa [Real.dist_eq, D, mul_comm] using hh

lemma aux_lem_finite_trace_smooth_density_holderOnWith
    {d : ℕ} {A : Set (SpatialCoordinates d)} {f : SpatialCoordinates d → ℝ}
    {C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r)
    (h : ∀ x ∈ A, ∀ y ∈ A, |f x - f y| ≤ C * (dist x y)^r) :
    HolderOnWith ⟨C, hC⟩ ⟨r, hr⟩ f A := by
  intro x hx y hy
  rw [edist_dist, edist_dist]
  rw [ENNReal.coe_nnreal_eq]
  simp only [NNReal.coe_mk]
  change ENNReal.ofReal (dist (f x) (f y)) ≤
    ENNReal.ofReal C * ENNReal.ofReal (dist x y) ^ r
  rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg hr,
    ← ENNReal.ofReal_mul hC]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.dist_eq]
  exact h x hx y hy

lemma aux_lem_finite_trace_smooth_density_smooth
    {d : ℕ} {U S : Set (SpatialCoordinates d)}
    (hU : IsOpenBoundedConvexDomain U) (hSU : S ⊆ U)
    (hball : Metric.closedBall (0 : SpatialCoordinates d) 1 ⊆ U)
    (F : SpatialCoordinates d → ℝ) (hFc : Continuous F)
    (alpha : ℝ) (ha : 0 < alpha) (K : ℝ) (hK : 0 ≤ K)
    (hF : ∀ x y, |F x - F y| ≤ K * (dist x y) ^ alpha)
    (hFmem : MemLpOn U 1 F) (rho : SpatialCoordinates d → ℝ)
    (hrho : IsConvexApproxKernel rho) {eps : ℝ}
    (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ h : SpatialCoordinates d → ℝ,
      ContDiff ℝ ∞ h ∧
      (∀ x ∈ S, |h x - F x| ≤
        K * (eps * (2 * Classical.choose hU.isBoundedDomain)) ^ alpha) ∧
      (∀ x ∈ S, ∀ y ∈ S, |h x - h y| ≤ K * (dist x y) ^ alpha) := by
  let M : ℝ := 2 * Classical.choose hU.isBoundedDomain
  let h := convexApproxSmoothRepresentative U rho F 0 1 eps
  have hcont : ContDiff ℝ ∞ h := by
    simpa [h] using
      (contDiff_convexApproxSmoothRepresentative hU.isOpen.measurableSet hrho
        (le_refl 1) hFmem one_pos heps)
  refine ⟨h, hcont, ?_, ?_⟩
  · intro x hx
    have hxeq := convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
      (u := F) hU hrho (hSU hx) hball one_pos heps heps1
    change |convexApproxSmoothRepresentative U rho F 0 1 eps x - F x| ≤ _
    rw [hxeq]
    apply abs_convexApproxSmoothing_sub_le_of_modulus hU hrho hFc
      (hx := hSU hx) (hball := hball) (by norm_num) heps.le (le_of_lt heps1)
    intro y hy hdist
    have hxy : dist y x ≤ eps * M := by
      rw [dist_eq_norm]
      simpa [M, norm_sub_rev] using hdist
    have hpow : (dist y x) ^ alpha ≤ (eps * M) ^ alpha :=
      Real.rpow_le_rpow dist_nonneg hxy ha.le
    exact (hF y x).trans (mul_le_mul_of_nonneg_left hpow hK)
  · intro x hx y hy
    have hxeq := convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
      (u := F) hU hrho (hSU hx) hball one_pos heps heps1
    have hyeq := convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
      (u := F) hU hrho (hSU hy) hball one_pos heps heps1
    change |convexApproxSmoothRepresentative U rho F 0 1 eps x -
      convexApproxSmoothRepresentative U rho F 0 1 eps y| ≤ _
    rw [hxeq, hyeq]
    let Ix := fun z => convexApproxIntegrand rho F 0 1 eps x z
    let Iy := fun z => convexApproxIntegrand rho F 0 1 eps y z
    have hIx : Integrable Ix := by
      dsimp [Ix]
      exact integrable_convexApproxIntegrand hrho.continuous hrho.compactSupport hFc 0 1 eps x
    have hIy : Integrable Iy := by
      dsimp [Iy]
      exact integrable_convexApproxIntegrand hrho.continuous hrho.compactSupport hFc 0 1 eps y
    have hdiff :
        (∫ z in tsupport rho, Ix z) - ∫ z in tsupport rho, Iy z =
          ∫ z in tsupport rho, (Ix z - Iy z) := by
      rw [← MeasureTheory.integral_sub hIx.integrableOn hIy.integrableOn]
    change |(∫ z in tsupport rho, Ix z) - ∫ z in tsupport rho, Iy z| ≤ _
    rw [hdiff]
    calc
      |∫ z in tsupport rho, (Ix z - Iy z)| ≤
          ∫ z in tsupport rho, |Ix z - Iy z| := by
            simpa using
              (MeasureTheory.abs_integral_le_integral_abs
                (μ := volume.restrict (tsupport rho))
                (f := fun z => Ix z - Iy z))
      _ ≤ ∫ z in tsupport rho, rho z * (K * (dist x y) ^ alpha) := by
        have hIleft : IntegrableOn (fun z => |Ix z - Iy z|) (tsupport rho) :=
          (hIx.sub hIy).norm.integrableOn
        have hIright : IntegrableOn
            (fun z => rho z * (K * (dist x y) ^ alpha)) (tsupport rho) :=
          (integrable_convexApproxKernelMulConst hrho.continuous hrho.compactSupport
            (K * (dist x y) ^ alpha)).integrableOn
        apply setIntegral_mono_on hIleft hIright
          (isClosed_tsupport (f := rho)).measurableSet
        intro z hz
        dsimp [Ix, Iy, convexApproxIntegrand]
        rw [← mul_sub, abs_mul, abs_of_nonneg (hrho.nonneg z)]
        apply mul_le_mul_of_nonneg_left
        · have hsample :
              dist (convexApproxSample 0 z 1 eps x)
                  (convexApproxSample 0 z 1 eps y) ≤ dist x y := by
            rw [dist_eq_norm, dist_eq_norm]
            have heq :
                convexApproxSample 0 z 1 eps x - convexApproxSample 0 z 1 eps y =
                  (1 - eps) • (x - y) := by
              simp [convexApproxSample]
              module
            rw [heq, norm_smul, Real.norm_eq_abs,
              abs_of_nonneg (sub_nonneg.mpr heps1.le)]
            exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [heps])
          exact (hF _ _).trans
            (mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow dist_nonneg hsample ha.le) hK)
        · exact hrho.nonneg z
      _ = K * (dist x y) ^ alpha := by
        rw [integral_mul_const, hrho.setIntegral_one, one_mul]

lemma aux_lem_finite_trace_smooth_density_pi_holder
    {d : ℕ} (hd : 2 ≤ d) (alpha : ℝ) (ha : 0 < alpha)
    (S : Set (SpatialCoordinates d)) (G : SpatialCoordinates d → ℝ)
    (hG : BddAbove (Lane4.holderRatioSet alpha S G)) :
    ∃ K : ℝ≥0, ∀ x ∈ S, ∀ y ∈ S,
      |G x - G y| ≤ (K : ℝ) * (dist x y)^alpha := by
  let C : ℝ := Classical.choose hG
  have hC : ∀ v ∈ Lane4.holderRatioSet alpha S G, v ≤ C :=
    Classical.choose_spec hG
  let K : ℝ≥0 := ⟨max C 0 * (d : ℝ) ^ alpha, by positivity⟩
  refine ⟨K, ?_⟩
  intro x hx y hy
  by_cases hxy : x = y
  · simp [hxy, Real.zero_rpow ha.ne']
  · let E : ℝ := Real.sqrt (∑ i : Fin d, (x i - y i)^2)
    have hEpos : 0 < E := by
      dsimp [E]
      apply Real.sqrt_pos.mpr
      have hne : ∃ i : Fin d, x i - y i ≠ 0 := by
        by_contra hn
        apply hxy
        funext i
        have hi : x i - y i = 0 := by
          by_contra hi
          exact hn ⟨i, hi⟩
        linarith
      obtain ⟨i, hi⟩ := hne
      apply Finset.sum_pos'
      · intro j _
        exact sq_nonneg _
      · exact ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
    have hratio : |G x - G y| / E ^ alpha ≤ C := by
      apply hC
      exact ⟨x, hx, y, hy, hxy, rfl⟩
    have hraw : |G x - G y| ≤ C * E^alpha :=
      (div_le_iff₀ (Real.rpow_pos_of_pos hEpos alpha)).mp hratio
    have hED : E ≤ (d : ℝ) * dist x y := by
      simpa [E, Homogenization.euclideanNorm, Homogenization.vecNormSq,
        Homogenization.vecDot, dist_eq_norm, Pi.sub_apply, pow_two] using
        (Homogenization.euclideanNorm_le_dimension_mul_norm (x - y))
    have hpow : E^alpha ≤ ((d : ℝ) * dist x y)^alpha :=
      Real.rpow_le_rpow hEpos.le hED ha.le
    have hraw' : |G x - G y| ≤ max C 0 * ((d : ℝ) * dist x y)^alpha := by
      calc
        _ ≤ C * E^alpha := hraw
        _ ≤ max C 0 * E^alpha := by
          gcongr
          exact le_max_left C 0
        _ ≤ max C 0 * ((d : ℝ) * dist x y)^alpha := by
          gcongr
    calc
      |G x - G y| ≤ max C 0 * ((d : ℝ) * dist x y)^alpha := hraw'
      _ = (K : ℝ) * (dist x y)^alpha := by
        dsimp [K]
        rw [Real.mul_rpow (by positivity) dist_nonneg]
        ring

lemma aux_lem_finite_trace_smooth_density_cAlpha_bound
    {d : ℕ} (b : ℝ) (hb : 0 < b) (S : Set (SpatialCoordinates d))
    (q : SpatialCoordinates d → ℝ) (E C : ℝ) (hE : 0 ≤ E) (hC : 0 ≤ C)
    (hval : ∀ x ∈ S, |q x| ≤ E)
    (hpair : ∀ x ∈ S, ∀ y ∈ S,
      |q x - q y| ≤ C * (dist x y)^b) :
    Lane4.cAlphaNorm b S q ≤ E + C := by
  unfold Lane4.cAlphaNorm Lane4.holderSeminorm
  apply add_le_add
  · apply Real.sSup_le
    · intro v hv
      rcases hv with ⟨x, hx, rfl⟩
      exact hval x hx
    · exact hE
  · apply Real.sSup_le
    · intro v hv
      rcases hv with ⟨x, hx, y, hy, hxy, rfl⟩
      let R : ℝ := Real.sqrt (∑ i : Fin d, (x i - y i)^2)
      have hRpos : 0 < R := by
        dsimp [R]
        apply Real.sqrt_pos.mpr
        have hne : ∃ i : Fin d, x i - y i ≠ 0 := by
          by_contra hn
          apply hxy
          funext i
          have hi : x i - y i = 0 := by
            by_contra hi
            exact hn ⟨i, hi⟩
          linarith
        obtain ⟨i, hi⟩ := hne
        apply Finset.sum_pos'
        · intro j _
          exact sq_nonneg _
        · exact ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
      have hRE : dist x y ≤ R := by
        simpa [R, Homogenization.euclideanNorm, Homogenization.vecNormSq,
          Homogenization.vecDot, dist_eq_norm, Pi.sub_apply, pow_two] using
          (Homogenization.norm_le_euclideanNorm (x - y))
      have hquot : |q x - q y| / R ^ b ≤ C := by
        apply (div_le_iff₀ (Real.rpow_pos_of_pos hRpos b)).2
        exact (hpair x hx y hy).trans
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow dist_nonneg hRE (le_of_lt hb)) hC)
      exact hquot
    · exact hC

lemma aux_lem_finite_trace_smooth_density_direct_isHolderOn
    {d : ℕ} {b : ℝ} (hb : 0 < b) (S : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hpair : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ C * (dist x y)^b) :
    Lane4.IsHolderOn b S f := by
  unfold Lane4.IsHolderOn
  refine ⟨C, ?_⟩
  intro v hv
  rcases hv with ⟨x, hx, y, hy, hxy, rfl⟩
  let R : ℝ := Real.sqrt (∑ i : Fin d, (x i - y i)^2)
  have hRpos : 0 < R := by
    dsimp [R]
    apply Real.sqrt_pos.mpr
    have hne : ∃ i : Fin d, x i - y i ≠ 0 := by
      by_contra hn
      apply hxy
      funext i
      have hi : x i - y i = 0 := by
        by_contra hi
        exact hn ⟨i, hi⟩
      linarith
    obtain ⟨i, hi⟩ := hne
    apply Finset.sum_pos'
    · intro j _
      exact sq_nonneg _
    · exact ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
  have hRE : dist x y ≤ R := by
    simpa [R, Homogenization.euclideanNorm, Homogenization.vecNormSq,
      Homogenization.vecDot, dist_eq_norm, Pi.sub_apply, pow_two] using
      (Homogenization.norm_le_euclideanNorm (x - y))
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hRpos b)).2
  exact (hpair x hx y hy).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow dist_nonneg hRE hb.le) hC)

lemma aux_lem_finite_trace_smooth_density_holderOnWith_direct
    {d : ℕ} {A : Set (SpatialCoordinates d)} {f : SpatialCoordinates d → ℝ}
    {C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r)
    (h : HolderOnWith ⟨C, hC⟩ ⟨r, hr⟩ f A) :
    ∀ x ∈ A, ∀ y ∈ A, |f x - f y| ≤ C * (dist x y)^r := by
  intro x hx y hy
  have hh := h x hx y hy
  rw [edist_dist, edist_dist, ENNReal.coe_nnreal_eq] at hh
  simp only [NNReal.coe_mk] at hh
  change ENNReal.ofReal (dist (f x) (f y)) ≤
    ENNReal.ofReal C * ENNReal.ofReal (dist x y) ^ r at hh
  rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg hr,
    ← ENNReal.ofReal_mul hC] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh



theorem lem_finite_trace_smooth_density
    (d : ℕ) (hd : 2 ≤ d)
    (beta alpha : ℝ) (hbeta : 1 / 2 < beta) (hba : beta < alpha) (halpha : alpha < 1)
    (g : SpatialCoordinates d → ℝ)
    (hg : IsCellBoundaryClass alpha 0 1 g)
    (hunit : cellBoundaryQuotientNorm alpha 0 1 g ≤ 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ h : SpatialCoordinates d → ℝ,
      ContDiff ℝ ∞ h ∧ IsCellBoundaryClass beta 0 1 h ∧
      IsCellBoundaryClass beta 0 1 (fun x => g x - h x) ∧
      cellBoundaryQuotientNorm beta 0 1 (fun x => g x - h x) ≤ epsilon := by
  classical
  have hbeta0 : 0 < beta := by linarith
  have halpha0 : 0 < alpha := by linarith
  let S : Set (SpatialCoordinates d) :=
    frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d))
  let G : SpatialCoordinates d → ℝ := rescaledDatum 0 1 g
  have hg' : Lane4.IsHolderOn alpha S G ∧
      BddAbove {v : ℝ | ∃ x ∈ S, v = |G x|} := by
    simpa [S, G, IsCellBoundaryClass] using hg
  have hSsub : S ⊆ (closedCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)) := by
    dsimp [S]
    have hclosed : IsClosed (closedCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)) :=
      (closedCube (0 : SpatialCoordinates d) 1 one_pos).isCompact.isClosed
    exact frontier_subset_closure.trans
      (hclosed.closure_subset_iff.mpr (centeredCube_subset_closedCube 0 one_pos))
  let U : Set (SpatialCoordinates d) :=
    centeredCube (0 : SpatialCoordinates d) 4 (by norm_num)
  have hU : IsOpenBoundedConvexDomain U := by
    dsimp [U]
    refine ⟨(centeredCube (0 : SpatialCoordinates d) 4 (by norm_num)).isOpen, ?_, ?_⟩
    · apply Bornology.IsBounded.isBoundedDomain
      show Bornology.IsBounded (Metric.ball (0 : SpatialCoordinates d) (4 / 2))
      exact Metric.isBounded_ball
    · show Convex ℝ (Metric.ball (0 : SpatialCoordinates d) (4 / 2))
      exact convex_ball 0 (4 / 2)
  have hSU : S ⊆ U := by
    intro x hx
    have hx' := hSsub hx
    change dist x (0 : SpatialCoordinates d) ≤ (1 : ℝ) / 2 at hx'
    change dist x (0 : SpatialCoordinates d) < (4 : ℝ) / 2
    linarith
  have hball : Metric.closedBall (0 : SpatialCoordinates d) 1 ⊆ U := by
    intro x hx
    change dist x (0 : SpatialCoordinates d) < (4 : ℝ) / 2
    exact lt_of_le_of_lt hx (by norm_num)
  obtain ⟨K, hKG⟩ :=
    aux_lem_finite_trace_smooth_density_pi_holder hd alpha halpha0 S G hg'.1
  have hK : 0 ≤ (K : ℝ) := K.coe_nonneg
  obtain ⟨F, hF, hFS⟩ :=
    aux_lem_finite_trace_smooth_density_extend alpha halpha0 (by linarith [halpha]) K G S hKG
  have hFc : Continuous F := by
    have hH : HolderWith K ⟨alpha, halpha0.le⟩ F := by
      apply holderOnWith_univ.mp
      apply aux_lem_finite_trace_smooth_density_holderOnWith
        (A := Set.univ) (f := F) K.coe_nonneg halpha0.le
      intro x _ y _
      simpa using hF x y
    exact hH.continuous (by exact_mod_cast halpha0)
  let Bdom : ℝ := Classical.choose hU.isBoundedDomain
  have hBpos : 0 ≤ Bdom := (Classical.choose_spec hU.isBoundedDomain).1.le
  have hcoord : ∀ ⦃x⦄, x ∈ U → ∀ i : Fin d, |x i| ≤ Bdom := by
    intro x hx i
    exact (Classical.choose_spec hU.isBoundedDomain).2 x hx i
  have hzeroU : (0 : SpatialCoordinates d) ∈ U := by
    change dist (0 : SpatialCoordinates d) 0 < (4 : ℝ) / 2
    simp
  let boundF : ℝ := |F 0| + (K : ℝ) * Bdom ^ alpha
  letI : IsFiniteMeasure (volume.restrict U) := hU.isFiniteMeasure_restrict_volume
  have hFmem : MemLpOn U 1 F := by
    rw [MemLpOn]
    apply MemLp.of_bound hFc.aestronglyMeasurable boundF
    filter_upwards [ae_restrict_mem hU.isOpen.measurableSet] with x hx
    rw [Real.norm_eq_abs]
    have hdist : dist x 0 ≤ Bdom := by
      rw [dist_zero_right]
      apply (pi_norm_le_iff_of_nonneg hBpos).2
      intro i
      simpa only [Real.norm_eq_abs] using hcoord hx i
    have hval := hF x 0
    have hpow : (dist x 0)^alpha ≤ Bdom^alpha :=
      Real.rpow_le_rpow dist_nonneg hdist (le_of_lt halpha0)
    have habs : |F x - F 0| ≤ (K : ℝ) * Bdom^alpha :=
      hval.trans (mul_le_mul_of_nonneg_left hpow hK)
    have habs' : |F x| ≤ |F x - F 0| + |F 0| := by
      calc
        |F x| = |(F x - F 0) + F 0| := by congr 1 <;> ring
        _ ≤ |F x - F 0| + |F 0| := abs_add_le _ _
    dsimp [boundF]
    linarith
  let rho : SpatialCoordinates d → ℝ := unitConvexApproxKernel (d := d)
  have hrho : IsConvexApproxKernel rho := by
    simpa [rho] using (isConvexApproxKernel_unitConvexApproxKernel (d := d))
  let scale : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  have hscale_pos : ∀ n, 0 < scale n := by
    intro n
    dsimp [scale]
    positivity
  have hscale_lt : ∀ n, scale n < 1 := by
    intro n
    dsimp [scale]
    have hn : 0 ≤ (n : ℝ) := by positivity
    have : (1 : ℝ) < (n : ℝ) + 2 := by linarith
    exact (div_lt_iff₀ (by positivity)).2 (by simpa using this)
  have hscale : Tendsto scale atTop (𝓝 (0 : ℝ)) := by
    dsimp [scale]
    have hshift : Tendsto (fun n : ℕ => n + 1) atTop (atTop : Filter ℕ) := by
      refine tendsto_atTop.2 ?_
      intro b
      exact eventually_atTop.2 ⟨b, fun n hn => by omega⟩
    have hbase := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hcomp := hbase.comp hshift
    convert hcomp using 1
    funext n
    norm_num [Function.comp_def, Nat.cast_add]
    ring
  let err : ℕ → ℝ := fun n =>
    (K : ℝ) * (scale n * (2 * Bdom)) ^ alpha
  let A : ℝ := 2 * (K : ℝ)
  let t₁ : ℝ := beta / alpha
  let t₂ : ℝ := 1 - t₁
  have ht₁ : 0 < t₁ := by
    dsimp [t₁]
    positivity
  have ht₁_le : t₁ ≤ 1 := by
    dsimp [t₁]
    exact (div_le_iff₀ halpha0).2 (by simpa using (le_of_lt hba))
  have ht₂ : 0 < t₂ := by
    have ht₁_lt : t₁ < 1 := by
      dsimp [t₁]
      exact (div_lt_iff₀ halpha0).2 (by simpa using hba)
    dsimp [t₂]
    exact sub_pos.mpr ht₁_lt
  let interp : ℕ → ℝ := fun n => A ^ t₁ * (2 * err n) ^ t₂
  have herr : Tendsto err atTop (𝓝 (0 : ℝ)) := by
    have hsm : Tendsto (fun n => scale n * (2 * Bdom)) atTop (𝓝 (0 : ℝ)) := by
      simpa using hscale.mul tendsto_const_nhds
    have hp := hsm.rpow (tendsto_const_nhds : Tendsto (fun _ : ℕ => alpha) atTop (𝓝 alpha))
      (Or.inr halpha0)
    have hc : Tendsto (fun _ : ℕ => (K : ℝ)) atTop (𝓝 (K : ℝ)) := tendsto_const_nhds
    have hh := hc.mul hp
    simpa [err, Real.zero_rpow halpha0.ne'] using hh
  have hinterp : Tendsto interp atTop (𝓝 (0 : ℝ)) := by
    have htwo : Tendsto (fun n => 2 * err n) atTop (𝓝 (0 : ℝ)) := by
      convert herr.const_mul 2 using 1 <;> simp [err]
    have hp := htwo.rpow
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => t₂) atTop (𝓝 t₂))
      (Or.inr ht₂)
    have hc : Tendsto (fun _ : ℕ => A ^ t₁) atTop (𝓝 (A ^ t₁)) := tendsto_const_nhds
    have hh := hc.mul hp
    simpa [interp, Real.zero_rpow ht₂.ne'] using hh
  have hsmall : ∃ n : ℕ, err n + interp n < epsilon := by
    have hsum : Tendsto (fun n => err n + interp n) atTop (𝓝 (0 : ℝ)) := by
      convert herr.add hinterp using 1 <;> simp
    have hev : ∀ᶠ n : ℕ in atTop, err n + interp n < epsilon :=
      hsum.eventually (eventually_lt_nhds hepsilon)
    exact hev.exists
  obtain ⟨n, hn⟩ := hsmall
  obtain ⟨h, hcont, herrh, hhh⟩ :=
    aux_lem_finite_trace_smooth_density_smooth hU hSU hball F hFc alpha halpha0
      (K : ℝ) hK hF hFmem rho hrho (hscale_pos n) (hscale_lt n)

  have hSdist : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 1 := by
    intro x hx y hy
    have hx' := hSsub hx
    have hy' := hSsub hy
    change dist x (0 : SpatialCoordinates d) ≤ (1 : ℝ) / 2 at hx'
    change dist y (0 : SpatialCoordinates d) ≤ (1 : ℝ) / 2 at hy'
    calc
      dist x y ≤ dist x 0 + dist 0 y := dist_triangle _ _ _
      _ = dist x 0 + dist y 0 := by simp only [dist_zero_left, dist_zero_right]
      _ ≤ 1 := by linarith
  have hholderHalpha : HolderOnWith K ⟨alpha, halpha0.le⟩ h S := by
    simpa using
      (aux_lem_finite_trace_smooth_density_holderOnWith
        (A := S) (f := h) (C := (K : ℝ)) (r := alpha) hK halpha0.le hhh)
  have hSdistE : ∀ x ∈ S, ∀ y ∈ S,
      edist x y ≤ (1 : ℝ≥0∞) := by
    intro x hx y hy
    rw [edist_dist]
    exact_mod_cast hSdist x hx y hy
  have hholderHbeta :
      HolderOnWith (K * (1 : ℝ≥0) ^ ((alpha - beta : ℝ)))
        ⟨beta, hbeta0.le⟩ h S := by
    apply HolderOnWith.of_le (A := S) (C := K) (r := ⟨alpha, halpha0.le⟩)
      (s := ⟨beta, hbeta0.le⟩) (D := (1 : ℝ≥0)) hSdistE hholderHalpha
    exact_mod_cast hba.le
  have hHdirect : ∀ x ∈ S, ∀ y ∈ S,
      |h x - h y| ≤
        ((K * (1 : ℝ≥0) ^ ((alpha - beta : ℝ))) : ℝ) * (dist x y)^beta := by
    exact aux_lem_finite_trace_smooth_density_holderOnWith_direct
      (hC := by positivity) (hr := hbeta0.le) hholderHbeta
  have hHratio : Lane4.IsHolderOn beta S h := by
    exact aux_lem_finite_trace_smooth_density_direct_isHolderOn hbeta0 S h
      ((K * (1 : ℝ≥0) ^ ((alpha - beta : ℝ))) : ℝ) (by positivity) hHdirect
  obtain ⟨BG, hBG⟩ := hg'.2
  have hGerr : ∀ x ∈ S, |G x - h x| ≤ err n := by
    intro x hx
    have hh := herrh x hx
    calc
      |G x - h x| = |h x - G x| := abs_sub_comm _ _
      _ = |h x - F x| := by rw [← hFS hx]
      _ ≤ (K : ℝ) * (scale n * (2 * Bdom)) ^ alpha := by
        simpa [Bdom] using hh
      _ = err n := by rfl
  have hHval : BddAbove {v : ℝ | ∃ x ∈ S, v = |h x|} := by
    refine ⟨BG + err n, ?_⟩
    rintro v ⟨x, hx, rfl⟩
    have hgv := hBG ⟨x, hx, rfl⟩
    have hqv := hGerr x hx
    calc
      |h x| ≤ |h x - G x| + |G x| := by
        calc
          |h x| = |(h x - G x) + G x| := by congr 1 <;> ring
          _ ≤ |h x - G x| + |G x| := abs_add_le _ _
      _ ≤ err n + BG := add_le_add (by simpa [abs_sub_comm] using hqv) hgv
      _ = BG + err n := by ring
  have hclassH : IsCellBoundaryClass beta 0 1 h := by
    have hres : rescaledDatum (0 : SpatialCoordinates d) 1 h = h := by
      funext x
      simp [rescaledDatum]
    unfold IsCellBoundaryClass
    rw [hres]
    constructor
    · simpa [S] using hHratio
    · simpa [S] using hHval

  let Q : SpatialCoordinates d → ℝ := fun x => G x - h x
  have herr_nonneg : 0 ≤ err n := by
    dsimp [err]
    positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hQval : ∀ x ∈ S, |Q x| ≤ err n := by
    intro x hx
    simpa [Q] using hGerr x hx
  have hQpairAlpha : ∀ x ∈ S, ∀ y ∈ S,
      |Q x - Q y| ≤ A * (dist x y)^alpha := by
    intro x hx y hy
    calc
      |Q x - Q y| = |(G x - G y) - (h x - h y)| := by
        congr 1
        dsimp [Q]
        ring
      _ ≤ |G x - G y| + |h x - h y| := by
        calc
          |(G x - G y) - (h x - h y)| =
              |(G x - G y) + (-(h x - h y))| := by congr 1 <;> ring
          _ ≤ |G x - G y| + |-(h x - h y)| := abs_add_le _ _
          _ = |G x - G y| + |h x - h y| := by rw [abs_neg]
      _ ≤ (K : ℝ) * (dist x y)^alpha +
          (K : ℝ) * (dist x y)^alpha := add_le_add (hKG x hx y hy) (hhh x hx y hy)
      _ = A * (dist x y)^alpha := by
        dsimp [A]
        ring
  let KA : ℝ≥0 := ⟨A, hA⟩
  let KE : ℝ≥0 := ⟨2 * err n, by positivity⟩
  let alphaN : ℝ≥0 := ⟨alpha, halpha0.le⟩
  let betaN : ℝ≥0 := ⟨beta, hbeta0.le⟩
  let t1N : ℝ≥0 := ⟨t₁, ht₁.le⟩
  let t2N : ℝ≥0 := ⟨t₂, ht₂.le⟩
  have hQalpha : HolderOnWith KA alphaN Q S := by
    simpa [KA] using
      (aux_lem_finite_trace_smooth_density_holderOnWith
        (A := S) (f := Q) (C := A) (r := alpha) hA halpha0.le hQpairAlpha)
  have hQzero : HolderOnWith KE 0 Q S := by
    apply aux_lem_finite_trace_smooth_density_holderOnWith
      (C := 2 * err n) (r := 0) (hC := by positivity) (hr := by norm_num)
    intro x hx y hy
    calc
      |Q x - Q y| ≤ |Q x| + |Q y| := by
        calc
          |Q x - Q y| = |Q x + (-Q y)| := by congr 1 <;> ring
          _ ≤ |Q x| + |-Q y| := abs_add_le _ _
          _ = |Q x| + |Q y| := by rw [abs_neg]
      _ ≤ err n + err n := add_le_add (hQval x hx) (hQval y hy)
      _ = (2 * err n) * (dist x y)^(0 : ℝ) := by
        rw [Real.rpow_zero]
        ring
  have ht : t1N + t2N = 1 := by
    apply Subtype.ext
    dsimp [t1N, t2N, t₂]
    ring
  have hQinterp0 := hQalpha.interpolate hQzero ht
  have hexp :
      (alphaN * t1N) +
          ((0 : ℝ≥0) * t2N) = (⟨beta, hbeta0.le⟩ : ℝ≥0) := by
    apply Subtype.ext
    dsimp [alphaN, t1N, t₂, t₁]
    field_simp
    ring
  have hQinterp : HolderOnWith
      (KA ^ (t1N : ℝ) * KE ^ (t2N : ℝ)) betaN Q S := by
    rw [hexp] at hQinterp0
    exact hQinterp0
  let Cq : ℝ≥0 := KA ^ (t1N : ℝ) * KE ^ (t2N : ℝ)
  have hCq : (Cq : ℝ) = interp n := by
    simp [Cq, KA, KE, t1N, t2N, interp, A, NNReal.coe_mul, NNReal.coe_rpow,
      Real.zero_rpow ht₂.ne']
  have hQpairBeta : ∀ x ∈ S, ∀ y ∈ S,
      |Q x - Q y| ≤ interp n * (dist x y)^beta := by
    have htmp := aux_lem_finite_trace_smooth_density_holderOnWith_direct
      (hC := Cq.coe_nonneg) (hr := hbeta0.le) hQinterp
    simpa [Cq, hCq] using htmp
  have hQratio : Lane4.IsHolderOn beta S Q := by
    exact aux_lem_finite_trace_smooth_density_direct_isHolderOn hbeta0 S Q
      (interp n) (by positivity) hQpairBeta
  have hQvalB : BddAbove {v : ℝ | ∃ x ∈ S, v = |Q x|} := by
    refine ⟨err n, ?_⟩
    rintro v ⟨x, hx, rfl⟩
    exact hQval x hx
  have hclassQ : IsCellBoundaryClass beta 0 1 (fun x => g x - h x) := by
    have hres : rescaledDatum (0 : SpatialCoordinates d) 1
        (fun x => g x - h x) = (fun x => g x - h x) := by
      funext x
      simp [rescaledDatum]
    unfold IsCellBoundaryClass
    rw [hres]
    have hGres : rescaledDatum (0 : SpatialCoordinates d) 1 g = g := by
      funext x
      simp [rescaledDatum]
    have hQratio' : Lane4.IsHolderOn beta S (fun x => g x - h x) := by
      simpa [Q, G, hGres] using hQratio
    have hQvalB' : BddAbove {v : ℝ | ∃ x ∈ S, v = |g x - h x|} := by
      simpa [Q, G, hGres] using hQvalB
    constructor
    · simpa [S] using hQratio'
    · simpa [S] using hQvalB'
  have hQnorm : Lane4.cAlphaNorm beta S Q ≤ err n + interp n := by
    apply aux_lem_finite_trace_smooth_density_cAlpha_bound beta hbeta0 S Q
      (err n) (interp n) herr_nonneg (by positivity) hQval
    exact hQpairBeta
  have hqbelow : BddBelow {v : ℝ | ∃ c : ℝ,
      v = Lane4.cAlphaNorm beta S (fun x => Q x - c)} := by
    refine ⟨0, ?_⟩
    rintro v ⟨c, rfl⟩
    unfold Lane4.cAlphaNorm Lane4.holderSeminorm
    apply add_nonneg
    · apply Real.sSup_nonneg
      intro w hw
      rcases hw with ⟨x, hx, rfl⟩
      exact abs_nonneg _
    · apply Real.sSup_nonneg
      intro w hw
      rcases hw with ⟨x, hx, y, hy, hxy, rfl⟩
      exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  have hquotQ : quotientCBetaNorm beta S Q ≤ epsilon := by
    calc
      quotientCBetaNorm beta S Q ≤ Lane4.cAlphaNorm beta S Q := by
        unfold quotientCBetaNorm
        apply csInf_le hqbelow
        exact ⟨0, by simp⟩
      _ ≤ err n + interp n := hQnorm
      _ ≤ epsilon := le_of_lt hn
  refine ⟨h, hcont, hclassH, hclassQ, ?_⟩
  simpa [Q, S, G, cellBoundaryQuotientNorm, quotientCBetaNorm, rescaledDatum] using hquotQ

end Paper
