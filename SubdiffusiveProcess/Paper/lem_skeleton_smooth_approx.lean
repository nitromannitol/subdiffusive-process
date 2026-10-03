module

public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Lane2.BoundaryResponse
public import SubdiffusiveProcess.Lane4.Carriers
public import Homogenization.Sobolev.W1p.InwardMollificationGeometry
public import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.PointwiseBounds

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff Convolution

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

lemma aux_lem_skeleton_smooth_approx_conv {d : ℕ} {ρ g : SpatialCoordinates d → ℝ} {A : SpatialCoordinates d}
    {a : ℝ} (ha : 0 < a) :
    (scaledConvexApproxKernel ρ a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) A =
      ∫ z in tsupport ρ, ρ z * g (A - a • z) := by
  have h := convolution_scaledConvexApproxKernel_indicator_eq_setIntegral
    (ρ := ρ) (u := g) (U := Set.univ) (x0 := (2 : ℝ) • A)
    (x := (0 : SpatialCoordinates d)) (r := 2 * a) (ε := (1 / 2 : ℝ))
    (by positivity) (by norm_num)
  rw [show (A : SpatialCoordinates d) = (1 - (1/2 : ℝ)) • (0 : SpatialCoordinates d) +
      (1/2 : ℝ) • ((2 : ℝ) • A) by ext i <;> simp]
  simpa [Set.indicator_univ] using! h

lemma aux_lem_skeleton_smooth_approx_holderOnWith
    {d : ℕ} {A : Set (SpatialCoordinates d)} {f : SpatialCoordinates d → ℝ}
    {C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r)
    (h : ∀ x ∈ A, ∀ y ∈ A, |f x - f y| ≤ C * (dist x y)^r) :
    HolderOnWith ⟨C, hC⟩ ⟨r, hr⟩ f A := by
  suffices hout : HolderOnWith (NNReal.mk C hC) (NNReal.mk r hr) f A by exact hout
  intro x hx y hy
  rw [edist_dist, edist_dist]
  have hc : (↑(NNReal.mk C hC) : ENNReal) = ENNReal.ofReal C := by
    exact ENNReal.coe_nnreal_eq _
  have hr' : (↑(NNReal.mk r hr) : ℝ) = r := rfl
  rw [hc, hr']
  change ENNReal.ofReal (dist (f x) (f y)) ≤
    ENNReal.ofReal C * ENNReal.ofReal (dist x y) ^ r
  rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg hr,
    ← ENNReal.ofReal_mul hC]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.dist_eq]
  exact h x hx y hy

lemma aux_lem_skeleton_smooth_approx_pi_holder
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
  · simp +instances [hxy, Real.zero_rpow ha.ne']
  · let E : ℝ := Real.sqrt (∑ i : Fin d, (x i - y i)^2)
    have hEpos : 0 < E := by
      dsimp +instances [E]
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
        Homogenization.vecDot, dist_eq_norm, Pi.sub_apply, pow_two] using!
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
        have hK : (K : ℝ) = max C 0 * (d : ℝ) ^ alpha := rfl
        rw [hK]
        rw [Real.mul_rpow (by positivity) dist_nonneg]
        ring

lemma aux_lem_skeleton_smooth_approx_cAlpha_bound
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
        dsimp +instances [R]
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
          Homogenization.vecDot, dist_eq_norm, Pi.sub_apply, pow_two] using!
          (Homogenization.norm_le_euclideanNorm (x - y))
      have hquot : |q x - q y| / R ^ b ≤ C := by
        apply (div_le_iff₀ (Real.rpow_pos_of_pos hRpos b)).2
        exact (hpair x hx y hy).trans
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow dist_nonneg hRE (le_of_lt hb)) hC)
      exact hquot
    · exact hC

lemma aux_lem_skeleton_smooth_approx_holderOnWith_direct
    {d : ℕ} {A : Set (SpatialCoordinates d)} {f : SpatialCoordinates d → ℝ}
    {C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r)
    (h : HolderOnWith ⟨C, hC⟩ ⟨r, hr⟩ f A) :
    ∀ x ∈ A, ∀ y ∈ A, |f x - f y| ≤ C * (dist x y)^r := by
  intro x hx y hy
  have htyped : HolderOnWith (NNReal.mk C hC) (NNReal.mk r hr) f A := h
  have hh := htyped x hx y hy
  rw [edist_dist, edist_dist] at hh
  have hc : (↑(NNReal.mk C hC) : ENNReal) = ENNReal.ofReal C := by
    exact ENNReal.coe_nnreal_eq _
  have hr' : (↑(NNReal.mk r hr) : ℝ) = r := rfl
  rw [hc, hr'] at hh
  rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg hr,
    ← ENNReal.ofReal_mul hC] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh




theorem lem_skeleton_smooth_approx
    (hd : 2 ≤ d)
    (hQcube : ∃ (z : SpatialCoordinates d) (R : ℝ), 0 < R ∧
      (Q : Set (SpatialCoordinates d)) = Metric.ball z (R / 2))
    (alpha : ℝ) (halpha : 1 / 2 < alpha)
    (b : SpatialCoordinates d → ℝ)
    (hbcont : ContinuousOn b (closure (Q : Set (SpatialCoordinates d))))
    (hbh : ∀ theta : ℝ, 1 / 2 < theta → theta < min alpha 1 →
      Lane4.IsHolderOn theta (closure (Q : Set (SpatialCoordinates d))) b)
    (hbvanish : ∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), b x = 0)
    (beta : ℝ) (hbeta : 1 / 2 < beta) (hbetaalpha : beta < min alpha 1) :
    ∃ bseq : ℕ → SpatialCoordinates d → ℝ,
      (∀ k : ℕ, ContDiff ℝ ∞ (bseq k)) ∧
      (∀ k : ℕ, HasCompactSupport (bseq k)) ∧
      (∀ k : ℕ, tsupport (bseq k) ⊆ (Q : Set (SpatialCoordinates d))) ∧
      Tendsto
        (fun k : ℕ => Lane4.cAlphaNorm beta
          (closure (Q : Set (SpatialCoordinates d)))
          (fun x => bseq k x - b x)) atTop (𝓝 0) := by
  classical
  letI : NeZero d := ⟨by omega⟩
  rcases hQcube with ⟨z, R, hR, hQ⟩
  let S : Set (SpatialCoordinates d) := closure (Q : Set (SpatialCoordinates d))
  let theta : ℝ := (beta + min alpha 1) / 2
  have htheta0 : 0 < theta := by
    dsimp +instances [theta]
    have : 0 < beta := by linarith
    have : 0 < min alpha 1 := by positivity
    linarith
  have hbetatheta : beta < theta := by
    dsimp +instances [theta]
    linarith
  have hthetaalpha : theta < min alpha 1 := by
    dsimp +instances [theta]
    linarith
  obtain ⟨K, hK⟩ :=
      aux_lem_skeleton_smooth_approx_pi_holder hd theta htheta0 S b
      (hbh theta (by linarith) hthetaalpha)
  have hK0 : 0 ≤ (K : ℝ) := K.coe_nonneg
  let g : SpatialCoordinates d → ℝ := fun x => if x ∈ (Q : Set (SpatialCoordinates d)) then b x else 0
  have hQopen : IsOpen (Q : Set (SpatialCoordinates d)) := Q.isOpen
  have hQne : (Q : Set (SpatialCoordinates d)) ≠ Set.univ := by
    intro h
    have hbddQ : Bornology.IsBounded (Q : Set (SpatialCoordinates d)) := by
      rw [hQ]
      exact Metric.isBounded_ball
    have hbdd : Bornology.IsBounded (Set.univ : Set (SpatialCoordinates d)) := by
      rw [← h]
      exact hbddQ
    exact (NormedSpace.unbounded_univ ℝ (SpatialCoordinates d)) hbdd
  have hglobal : ∀ x y : SpatialCoordinates d,
      |g x - g y| ≤ (K : ℝ) * (dist x y)^theta := by
    intro x y
    by_cases hx : x ∈ (Q : Set (SpatialCoordinates d))
    · by_cases hy : y ∈ (Q : Set (SpatialCoordinates d))
      · change |(if x ∈ (Q : Set (SpatialCoordinates d)) then b x else 0) -
          (if y ∈ (Q : Set (SpatialCoordinates d)) then b y else 0)| ≤ _
        simp +instances only [if_pos hx, if_pos hy]
        exact hK x (subset_closure hx) y (subset_closure hy)
      · have hyc : y ∈ (Q : Set (SpatialCoordinates d))ᶜ := hy
        obtain ⟨p, hp, hpx⟩ :=
          exists_mem_frontier_infDist_compl_eq_dist (x := x)
            (s := (Q : Set (SpatialCoordinates d))) hx hQne
        have hpnQ : p ∉ (Q : Set (SpatialCoordinates d)) := by
          intro hpQ
          have hnot : p ∉ interior (Q : Set (SpatialCoordinates d)) := hp.2
          exact hnot (by simpa [hQopen.interior_eq] using! hpQ)
        have hpcl : p ∈ S := frontier_subset_closure hp
        have hdist : dist x p ≤ dist x y := by
          rw [← hpx]
          exact Metric.infDist_le_dist_of_mem hyc
        have hbound : |b x| ≤ (K : ℝ) * (dist x y)^theta := by
          calc
          |b x| = |b x - b p| := by rw [hbvanish p hp]; ring_nf
          _ ≤ (K : ℝ) * (dist x p)^theta := hK x (subset_closure hx) p hpcl
          _ ≤ (K : ℝ) * (dist x y)^theta := by
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow dist_nonneg hdist (le_of_lt htheta0)) hK0
        change |(if x ∈ (Q : Set (SpatialCoordinates d)) then b x else 0) -
          (if y ∈ (Q : Set (SpatialCoordinates d)) then b y else 0)| ≤ _
        simp +instances only [if_pos hx, if_neg hy]
        simpa [sub_zero] using! hbound
    · by_cases hy : y ∈ (Q : Set (SpatialCoordinates d))
      · have hxc : x ∈ (Q : Set (SpatialCoordinates d))ᶜ := hx
        obtain ⟨p, hp, hpy⟩ :=
          exists_mem_frontier_infDist_compl_eq_dist (x := y)
            (s := (Q : Set (SpatialCoordinates d))) hy hQne
        have hpnQ : p ∉ (Q : Set (SpatialCoordinates d)) := by
          intro hpQ
          have hnot : p ∉ interior (Q : Set (SpatialCoordinates d)) := hp.2
          exact hnot (by simpa [hQopen.interior_eq] using! hpQ)
        have hpcl : p ∈ S := frontier_subset_closure hp
        have hdist : dist y p ≤ dist y x := by
          rw [← hpy]
          exact Metric.infDist_le_dist_of_mem hxc
        have hbound : |b y| ≤ (K : ℝ) * (dist y x)^theta := by
          calc
          |b y| = |b y - b p| := by rw [hbvanish p hp]; ring_nf
          _ ≤ (K : ℝ) * (dist y p)^theta := hK y (subset_closure hy) p hpcl
          _ ≤ (K : ℝ) * (dist y x)^theta := by
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow dist_nonneg hdist (le_of_lt htheta0)) hK0
        change |(if x ∈ (Q : Set (SpatialCoordinates d)) then b x else 0) -
          (if y ∈ (Q : Set (SpatialCoordinates d)) then b y else 0)| ≤ _
        simp +instances only [if_neg hx, if_pos hy, zero_sub, abs_neg]
        exact hbound.trans_eq (by rw [dist_comm])
      · change |(if x ∈ (Q : Set (SpatialCoordinates d)) then b x else 0) -
          (if y ∈ (Q : Set (SpatialCoordinates d)) then b y else 0)| ≤ _
        simp +instances only [if_neg hx, if_neg hy, sub_self, abs_zero]
        positivity
  have hH : HolderWith K ⟨theta, htheta0.le⟩ g := by
    apply holderOnWith_univ.mp
    exact aux_lem_skeleton_smooth_approx_holderOnWith
      (A := Set.univ) (f := g) (C := (K : ℝ)) (r := theta)
      hK0 htheta0.le (by
        intro x _ y _
        exact hglobal x y)
  have hgcont : Continuous g := hH.continuous (by exact_mod_cast htheta0)
  have hsupport : tsupport g ⊆ S := by
    apply closure_minimal
    · intro x hx
      by_contra hxQ
      have hxQ' : x ∉ (Q : Set (SpatialCoordinates d)) := by
        intro hxq
        exact hxQ (subset_closure hxq)
      have hxzero : g x = 0 := by
        dsimp +instances [g]
        simp +instances [hxQ']
      exact hx hxzero
    · exact isClosed_closure
  have hU : IsOpenBoundedConvexDomain (Q : Set (SpatialCoordinates d)) := by
    rw [hQ]
    refine ⟨Metric.isOpen_ball, ?_, ?_⟩
    · exact Bornology.IsBounded.isBoundedDomain Metric.isBounded_ball
    · exact convex_ball z (R / 2)
  have hball : Metric.closedBall z (R / 4) ⊆ (Q : Set (SpatialCoordinates d)) := by
    rw [hQ]
    intro x hx
    rw [Metric.mem_ball]
    have hx' : dist x z ≤ R / 4 := by simpa [Metric.mem_closedBall, dist_comm] using! hx
    linarith
  let rho : SpatialCoordinates d → ℝ := unitConvexApproxKernel (d := d)
  have hrho : IsConvexApproxKernel rho := by
    simpa [rho] using! (isConvexApproxKernel_unitConvexApproxKernel (d := d))
  let r : ℝ := R / 4
  have hr : 0 < r := by dsimp +instances [r]; linarith
  have hscale : ∀ n : ℕ, 0 < (1 / ((n : ℝ) + 1)) := by intro n; positivity
  let f : ℕ → SpatialCoordinates d → ℝ := fun n =>
    inwardMollification rho g z r (1 / ((n : ℝ) + 1))
  have hclosedQ : ∀ x ∈ S, dist x z ≤ R / 2 := by
    intro x hx
    dsimp +instances [S] at hx
    rw [hQ, closure_ball z (by linarith : R / 2 ≠ 0)] at hx
    simpa [Metric.mem_closedBall, dist_comm] using! hx
  have hsample_bound : ∀ (n : ℕ) (x : SpatialCoordinates d), x ∈ S →
      ∀ w ∈ tsupport rho,
        ‖convexApproxSample z w (-r) (-(1 / ((n : ℝ) + 1))) x - x‖ ≤
          (1 / ((n : ℝ) + 1)) * (R / 2 + r) := by
    intro n x hx w hw
    have hw' : ‖w‖ ≤ 1 := by
      exact norm_le_one_of_mem_closedBall_zero_one (hrho.support_subset_closedBall hw)
    have he : 0 ≤ (1 / ((n : ℝ) + 1)) := by positivity
    rw [norm_convexApproxSample_sub]
    rw [abs_neg, abs_of_nonneg he]
    have heq : z - (-r) • w - x = z + r • w - x := by
      simp +instances [smul_neg]
    rw [heq]
    have htri : ‖z + r • w - x‖ ≤ dist x z + r := by
      calc
        ‖z + r • w - x‖ = ‖(z - x) + r • w‖ := by congr 1 <;> abel
        _ ≤ ‖z - x‖ + ‖r • w‖ := norm_add_le _ _
        _ = dist x z + r * ‖w‖ := by
          simp +instances [dist_comm, dist_eq_norm, norm_smul, abs_of_nonneg (le_of_lt hr)]
        _ ≤ dist x z + r := by
          calc
            dist x z + r * ‖w‖ ≤ dist x z + r * 1 :=
              (by simpa [add_comm] using!
                add_le_add_left (mul_le_mul_of_nonneg_left hw' (le_of_lt hr)) (dist x z))
            _ = dist x z + r := by ring
    have hdistxz : dist x z ≤ R / 2 := hclosedQ x hx
    calc
      (1 / ((n : ℝ) + 1)) * ‖z + r • w - x‖ ≤
          (1 / ((n : ℝ) + 1)) * (dist x z + r) :=
        mul_le_mul_of_nonneg_left htri he
      _ ≤ (1 / ((n : ℝ) + 1)) * (R / 2 + r) := by
        gcongr
  have hconv_repr : ∀ (n : ℕ) (x : SpatialCoordinates d),
      f n x = ∫ w in tsupport rho,
        rho w * g (((1 + (1 / ((n : ℝ) + 1))) • x) -
          (1 / ((n : ℝ) + 1)) • z -
          ((1 / ((n : ℝ) + 1)) * r) • w) := by
    intro n x
    dsimp +instances [f]
    rw [aux_lem_skeleton_smooth_approx_conv (ρ := rho) (g := g) (A :=
      (1 + (1 / ((n : ℝ) + 1))) • x - (1 / ((n : ℝ) + 1)) • z)
      (a := (1 / ((n : ℝ) + 1)) * r) (by positivity)]
  have hval : ∀ n x, x ∈ S →
      |f n x - g x| ≤ (K : ℝ) *
        ((1 / ((n : ℝ) + 1)) * (R / 2 + r)) ^ theta := by
    intro n x hx
    rw [hconv_repr n x]
    have hIx : IntegrableOn
        (fun w => rho w * g (((1 + (1 / ((n : ℝ) + 1))) • x) -
          (1 / ((n : ℝ) + 1)) • z -
          ((1 / ((n : ℝ) + 1)) * r) • w)) (tsupport rho) := by
      have hi := integrable_convexApproxIntegrand hrho.continuous hrho.compactSupport
        hgcont z (-r) (-(1 / ((n : ℝ) + 1))) x
      convert hi.integrableOn using 1
      funext w
      congr 2
      ext i
      simp
      ring
    have hIy : IntegrableOn (fun w => rho w * g x) (tsupport rho) := by
      exact (integrable_convexApproxKernelMulConst hrho.continuous hrho.compactSupport
        (g x)).integrableOn
    have hIright : IntegrableOn
        (fun w => rho w * ((K : ℝ) *
          ((1 / ((n : ℝ) + 1)) * (R / 2 + r)) ^ theta)) (tsupport rho) := by
      exact (integrable_convexApproxKernelMulConst hrho.continuous hrho.compactSupport
        ((K : ℝ) * ((1 / ((n : ℝ) + 1)) * (R / 2 + r)) ^ theta)).integrableOn
    have hconst : ∫ w in tsupport rho, rho w * g x = g x := by
      rw [integral_mul_const, hrho.setIntegral_one, one_mul]
    have hdiff :
        (∫ w in tsupport rho, rho w * g (((1 + (1 / ((n : ℝ) + 1))) • x) -
          (1 / ((n : ℝ) + 1)) • z -
          ((1 / ((n : ℝ) + 1)) * r) • w)) -
          ∫ w in tsupport rho, rho w * g x =
        ∫ w in tsupport rho, rho w * (g (((1 + (1 / ((n : ℝ) + 1))) • x) -
          (1 / ((n : ℝ) + 1)) • z -
          ((1 / ((n : ℝ) + 1)) * r) • w) - g x) := by
      rw [← MeasureTheory.integral_sub hIx hIy]
      congr 1
      funext w
      ring
    rw [← hconst, hdiff]
    calc
      |∫ w in tsupport rho, rho w * (g (((1 + (1 / ((n : ℝ) + 1))) • x) -
          (1 / ((n : ℝ) + 1)) • z -
          ((1 / ((n : ℝ) + 1)) * r) • w) - g x)| ≤
          ∫ w in tsupport rho, |rho w * (g (((1 + (1 / ((n : ℝ) + 1))) • x) -
          (1 / ((n : ℝ) + 1)) • z -
          ((1 / ((n : ℝ) + 1)) * r) • w) - g x)| := by
            simpa using! (abs_integral_le_integral_abs
              (μ := volume.restrict (tsupport rho))
              (f := fun w => rho w * (g (((1 + (1 / ((n : ℝ) + 1))) • x) -
                (1 / ((n : ℝ) + 1)) • z -
                ((1 / ((n : ℝ) + 1)) * r) • w) - g x)))
      _ ≤ ∫ w in tsupport rho, rho w *
          ((K : ℝ) * ((1 / ((n : ℝ) + 1)) * (R / 2 + r)) ^ theta) := by
        have hleft : IntegrableOn (fun w =>
                ‖rho w * g (((1 + (1 / ((n : ℝ) + 1))) • x) -
                  (1 / ((n : ℝ) + 1)) • z -
                  ((1 / ((n : ℝ) + 1)) * r) • w) - rho w * g x‖)
            (tsupport rho) volume := by
          simpa only [Pi.sub_apply] using! (hIx.sub hIy).norm
        have hmono :
            ∫ w in tsupport rho,
                ‖rho w * g (((1 + (1 / ((n : ℝ) + 1))) • x) -
                  (1 / ((n : ℝ) + 1)) • z -
                  ((1 / ((n : ℝ) + 1)) * r) • w) - rho w * g x‖ ≤
              ∫ w in tsupport rho, rho w *
                ((K : ℝ) * ((1 / ((n : ℝ) + 1)) * (R / 2 + r)) ^ theta) := by
          apply setIntegral_mono_on (μ := volume) hleft hIright
            (isClosed_tsupport rho).measurableSet
          intro w hw
          rw [← mul_sub]
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hrho.nonneg w)]
          apply mul_le_mul_of_nonneg_left _ (hrho.nonneg w)
          have hs := hglobal
            (convexApproxSample z w (-r) (-(1 / ((n : ℝ) + 1))) x) x
          have hnorm := hsample_bound n x hx w hw
          have hdist : dist (convexApproxSample z w (-r) (-(1 / ((n : ℝ) + 1))) x) x ≤
              (1 / ((n : ℝ) + 1)) * (R / 2 + r) := by
            simpa [dist_eq_norm] using! hnorm
          have hs' := hs.trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow dist_nonneg hdist (le_of_lt htheta0)) hK0)
          simpa [convexApproxSample, sub_eq_add_neg, smul_eq_mul,
            mul_add, smul_smul, add_assoc, add_left_comm, add_comm, Real.norm_eq_abs] using! hs' 
        simpa [← mul_sub, Real.norm_eq_abs] using! hmono
      _ = (K : ℝ) * ((1 / ((n : ℝ) + 1)) * (R / 2 + r)) ^ theta := by
        rw [integral_mul_const, hrho.setIntegral_one, one_mul]
  have hfpair : ∀ n x, x ∈ S → ∀ y, y ∈ S →
      |f n x - f n y| ≤ (K : ℝ) *
        (1 + (1 / ((n : ℝ) + 1))) ^ theta * (dist x y)^theta := by
    intro n x hx y hy
    rw [hconv_repr n x, hconv_repr n y]
    have hIx : IntegrableOn
        (fun w => rho w * g (((1 + (1 / ((n : ℝ) + 1))) • x) -
          (1 / ((n : ℝ) + 1)) • z -
          ((1 / ((n : ℝ) + 1)) * r) • w)) (tsupport rho) := by
      have hi := integrable_convexApproxIntegrand hrho.continuous hrho.compactSupport
        hgcont z (-r) (-(1 / ((n : ℝ) + 1))) x
      convert hi.integrableOn using 1
      funext w
      congr 2
      ext i
      simp
      ring
    have hIy : IntegrableOn
        (fun w => rho w * g (((1 + (1 / ((n : ℝ) + 1))) • y) -
          (1 / ((n : ℝ) + 1)) • z -
          ((1 / ((n : ℝ) + 1)) * r) • w)) (tsupport rho) := by
      have hi := integrable_convexApproxIntegrand hrho.continuous hrho.compactSupport
        hgcont z (-r) (-(1 / ((n : ℝ) + 1))) y
      convert hi.integrableOn using 1
      funext w
      congr 2
      ext i
      simp
      ring
    have hdiff :
        (∫ w in tsupport rho, rho w * g (((1 + (1 / ((n : ℝ) + 1))) • x) -
          (1 / ((n : ℝ) + 1)) • z -
          ((1 / ((n : ℝ) + 1)) * r) • w)) -
          ∫ w in tsupport rho, rho w * g (((1 + (1 / ((n : ℝ) + 1))) • y) -
          (1 / ((n : ℝ) + 1)) • z -
          ((1 / ((n : ℝ) + 1)) * r) • w) =
        ∫ w in tsupport rho, (rho w * g (((1 + (1 / ((n : ℝ) + 1))) • x) -
          (1 / ((n : ℝ) + 1)) • z -
          ((1 / ((n : ℝ) + 1)) * r) • w) -
          rho w * g (((1 + (1 / ((n : ℝ) + 1))) • y) -
          (1 / ((n : ℝ) + 1)) • z -
          ((1 / ((n : ℝ) + 1)) * r) • w)) := by
      rw [← MeasureTheory.integral_sub hIx hIy]
    rw [hdiff]
    calc
      |∫ w in tsupport rho, (rho w * g (((1 + (1 / ((n : ℝ) + 1))) • x) -
          (1 / ((n : ℝ) + 1)) • z -
          ((1 / ((n : ℝ) + 1)) * r) • w) -
          rho w * g (((1 + (1 / ((n : ℝ) + 1))) • y) -
          (1 / ((n : ℝ) + 1)) • z -
          ((1 / ((n : ℝ) + 1)) * r) • w))| ≤
          ∫ w in tsupport rho, |rho w * g (((1 + (1 / ((n : ℝ) + 1))) • x) -
          (1 / ((n : ℝ) + 1)) • z -
          ((1 / ((n : ℝ) + 1)) * r) • w) -
          rho w * g (((1 + (1 / ((n : ℝ) + 1))) • y) -
          (1 / ((n : ℝ) + 1)) • z -
          ((1 / ((n : ℝ) + 1)) * r) • w)| := by
            simpa using! (abs_integral_le_integral_abs
              (μ := volume.restrict (tsupport rho))
              (f := fun w => rho w * g (((1 + (1 / ((n : ℝ) + 1))) • x) -
                (1 / ((n : ℝ) + 1)) • z -
                ((1 / ((n : ℝ) + 1)) * r) • w) -
                rho w * g (((1 + (1 / ((n : ℝ) + 1))) • y) -
                (1 / ((n : ℝ) + 1)) • z -
                ((1 / ((n : ℝ) + 1)) * r) • w)))
      _ ≤ ∫ w in tsupport rho, rho w *
          ((K : ℝ) * (1 + (1 / ((n : ℝ) + 1))) ^ theta * (dist x y)^theta) := by
        have hleft : IntegrableOn (fun w =>
            ‖rho w * g (((1 + (1 / ((n : ℝ) + 1))) • x) -
              (1 / ((n : ℝ) + 1)) • z -
              ((1 / ((n : ℝ) + 1)) * r) • w) -
              rho w * g (((1 + (1 / ((n : ℝ) + 1))) • y) -
              (1 / ((n : ℝ) + 1)) • z -
              ((1 / ((n : ℝ) + 1)) * r) • w)‖) (tsupport rho) volume := by
          simpa only [Pi.sub_apply] using! (hIx.sub hIy).norm
        have hright : IntegrableOn (fun w => rho w *
            ((K : ℝ) * (1 + (1 / ((n : ℝ) + 1))) ^ theta * (dist x y)^theta))
            (tsupport rho) := by
          exact (integrable_convexApproxKernelMulConst hrho.continuous hrho.compactSupport
            ((K : ℝ) * (1 + (1 / ((n : ℝ) + 1))) ^ theta * (dist x y)^theta)).integrableOn
        have hmono :
            ∫ w in tsupport rho, ‖rho w * g (((1 + (1 / ((n : ℝ) + 1))) • x) -
              (1 / ((n : ℝ) + 1)) • z -
              ((1 / ((n : ℝ) + 1)) * r) • w) -
              rho w * g (((1 + (1 / ((n : ℝ) + 1))) • y) -
              (1 / ((n : ℝ) + 1)) • z -
              ((1 / ((n : ℝ) + 1)) * r) • w)‖ ≤
            ∫ w in tsupport rho, rho w *
              ((K : ℝ) * (1 + (1 / ((n : ℝ) + 1))) ^ theta * (dist x y)^theta) := by
          apply setIntegral_mono_on (μ := volume) hleft hright
            (isClosed_tsupport rho).measurableSet
          intro w hw
          rw [← mul_sub, norm_mul, Real.norm_eq_abs,
            abs_of_nonneg (hrho.nonneg w)]
          apply mul_le_mul_of_nonneg_left _ (hrho.nonneg w)
          have hs := hglobal
            (convexApproxSample z w (-r) (-(1 / ((n : ℝ) + 1))) x)
            (convexApproxSample z w (-r) (-(1 / ((n : ℝ) + 1))) y)
          have heq :
              convexApproxSample z w (-r) (-(1 / ((n : ℝ) + 1))) x -
                convexApproxSample z w (-r) (-(1 / ((n : ℝ) + 1))) y =
                (1 + (1 / ((n : ℝ) + 1))) • (x - y) := by
            simp +instances [convexApproxSample]
            module
          have hdist :
              dist (convexApproxSample z w (-r) (-(1 / ((n : ℝ) + 1))) x)
                  (convexApproxSample z w (-r) (-(1 / ((n : ℝ) + 1))) y) =
                (1 + (1 / ((n : ℝ) + 1))) * dist x y := by
            rw [dist_eq_norm, dist_eq_norm, heq, norm_smul,
              Real.norm_eq_abs, abs_of_pos (by positivity)]
          have hs' := hs.trans (by rw [hdist, Real.mul_rpow (by positivity) (dist_nonneg)])
          calc
            |g (((1 + (1 / ((n : ℝ) + 1))) • x) -
                (1 / ((n : ℝ) + 1)) • z -
                ((1 / ((n : ℝ) + 1)) * r) • w) -
                g (((1 + (1 / ((n : ℝ) + 1))) • y) -
                (1 / ((n : ℝ) + 1)) • z -
                ((1 / ((n : ℝ) + 1)) * r) • w)| ≤
                (K : ℝ) * ((1 + (1 / ((n : ℝ) + 1))) ^ theta * (dist x y)^theta) := by
              simpa [convexApproxSample, sub_eq_add_neg, smul_eq_mul, smul_smul,
                mul_add, add_assoc, add_left_comm, add_comm, Real.norm_eq_abs] using! hs'
            _ = (K : ℝ) * (1 + (1 / ((n : ℝ) + 1))) ^ theta * (dist x y)^theta := by ring
        simpa [← mul_sub, Real.norm_eq_abs] using! hmono
      _ = (K : ℝ) * (1 + (1 / ((n : ℝ) + 1))) ^ theta * (dist x y)^theta := by
        rw [integral_mul_const, hrho.setIntegral_one, one_mul]
  have hgb : ∀ x ∈ S, g x = b x := by
    intro x hx
    by_cases hxQ : x ∈ (Q : Set (SpatialCoordinates d))
    · dsimp +instances [g]
      rw [if_pos hxQ]
    · have hxf : x ∈ frontier (Q : Set (SpatialCoordinates d)) := by
        rw [frontier]
        refine ⟨hx, ?_⟩
        simpa [hQopen.interior_eq] using! hxQ
      have hb0 := hbvanish x hxf
      dsimp +instances [g]
      rw [if_neg hxQ]
      exact hb0.symm
  let q : ℕ → SpatialCoordinates d → ℝ := fun n x => f n x - b x
  let E : ℕ → ℝ := fun n => (K : ℝ) *
    ((1 / ((n : ℝ) + 1)) * (R / 2 + r)) ^ theta
  have hE0 : ∀ n, 0 ≤ E n := by
    intro n
    dsimp +instances [E]
    positivity
  have hqval : ∀ n x, x ∈ S → |q n x| ≤ E n := by
    intro n x hx
    dsimp +instances [q]
    rw [← hgb x hx]
    simpa [E] using! hval n x hx
  have hqpairTheta : ∀ n x, x ∈ S → ∀ y, y ∈ S →
      |q n x - q n y| ≤
        (K : ℝ) * ((1 + (1 / ((n : ℝ) + 1))) ^ theta + 1) *
          (dist x y)^theta := by
    intro n x hx y hy
    have hf := hfpair n x hx y hy
    have hb := hK x hx y hy
    dsimp +instances [q]
    calc
      |(f n x - b x) - (f n y - b y)| =
          |(f n x - f n y) - (b x - b y)| := by congr 1 <;> ring
      _ ≤ |f n x - f n y| + |b x - b y| := by
        calc
          |(f n x - f n y) - (b x - b y)| =
              |(f n x - f n y) + (-(b x - b y))| := by congr 1 <;> ring
          _ ≤ |f n x - f n y| + |-(b x - b y)| := abs_add_le _ _
          _ = |f n x - f n y| + |b x - b y| := by rw [abs_neg]
      _ ≤ (K : ℝ) * (1 + (1 / ((n : ℝ) + 1))) ^ theta * (dist x y)^theta +
          (K : ℝ) * (dist x y)^theta := add_le_add hf hb
      _ = (K : ℝ) * ((1 + (1 / ((n : ℝ) + 1))) ^ theta + 1) *
          (dist x y)^theta := by ring
  let B : ℝ := (K : ℝ) * (2 ^ theta + 1)
  have hB0 : 0 ≤ B := by
    dsimp +instances [B]
    positivity
  have he0 : ∀ n : ℕ, 0 ≤ (1 / ((n : ℝ) + 1)) := by intro n; positivity
  have he1 : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    exact (div_le_iff₀ (by positivity)).2 (by linarith)
  have hqpairB : ∀ n x, x ∈ S → ∀ y, y ∈ S →
      |q n x - q n y| ≤ B * (dist x y)^theta := by
    intro n x hx y hy
    have hbase : (1 + (1 / ((n : ℝ) + 1))) ^ theta ≤ (2 : ℝ) ^ theta := by
      apply Real.rpow_le_rpow
      · positivity
      · linarith [he1 n]
      · exact htheta0.le
    have hnonnegdist : 0 ≤ (dist x y)^theta := Real.rpow_nonneg (dist_nonneg) _
    calc
      |q n x - q n y| ≤
          (K : ℝ) * ((1 + (1 / ((n : ℝ) + 1))) ^ theta + 1) *
            (dist x y)^theta := hqpairTheta n x hx y hy
      _ ≤ B * (dist x y)^theta := by
        dsimp +instances [B]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (by simpa [add_comm] using! add_le_add_right hbase 1) hK0)
          hnonnegdist
  have hbeta0 : 0 < beta := by linarith
  have ht1 : 0 < beta / theta := by positivity
  have ht1le : beta / theta ≤ 1 := by
    exact (div_le_iff₀ htheta0).2 (by simpa using! hbetatheta.le)
  have ht2 : 0 < 1 - beta / theta := by
    exact sub_pos.mpr ((div_lt_iff₀ htheta0).2 (by simpa using! hbetatheta))
  let betaN : ℝ≥0 := ⟨beta, hbeta0.le⟩
  let thetaN : ℝ≥0 := ⟨theta, htheta0.le⟩
  let t1N : ℝ≥0 := ⟨beta / theta, ht1.le⟩
  let t2N : ℝ≥0 := ⟨1 - beta / theta, ht2.le⟩
  have ht : t1N + t2N = 1 := by
    apply NNReal.coe_injective
    have he : beta / theta + (1 - beta / theta) = 1 := by ring
    simpa only [NNReal.coe_add, NNReal.coe_mk, NNReal.coe_one, t1N, t2N] using! he
  have hexp : thetaN * t1N + (0 : ℝ≥0) * t2N = betaN := by
    apply NNReal.coe_injective
    have he : theta * (beta / theta) = beta := by field_simp
    simpa only [zero_mul, add_zero, NNReal.coe_mul, NNReal.coe_mk, thetaN, t1N, betaN] using! he
  let I : ℕ → ℝ := fun n =>
    B ^ (beta / theta) * (2 * E n) ^ (1 - beta / theta)
  have hqpairI : ∀ n x, x ∈ S → ∀ y, y ∈ S →
      |q n x - q n y| ≤ I n * (dist x y)^beta := by
    intro n x hx y hy
    have hqtheta : HolderOnWith ⟨B, hB0⟩ thetaN (q n) S := by
      exact aux_lem_skeleton_smooth_approx_holderOnWith
        (A := S) (f := q n) (C := B) (r := theta) hB0 htheta0.le
          (hqpairB n)
    have hqzero : HolderOnWith ⟨2 * E n, by positivity⟩ 0 (q n) S := by
      exact aux_lem_skeleton_smooth_approx_holderOnWith
        (A := S) (f := q n) (C := 2 * E n) (r := 0) (by positivity) (by norm_num) (by
          intro u hu v hv
          calc
            |q n u - q n v| ≤ |q n u| + |q n v| := by
              calc
                |q n u - q n v| = |q n u + (-q n v)| := by congr 1 <;> ring
                _ ≤ |q n u| + |-q n v| := abs_add_le _ _
                _ = |q n u| + |q n v| := by rw [abs_neg]
            _ ≤ E n + E n := add_le_add (hqval n u hu) (hqval n v hv)
            _ = (2 * E n) * (dist u v) ^ (0 : ℝ) := by
              rw [Real.rpow_zero]
              ring)
    have hi := hqtheta.interpolate hqzero ht
    rw [hexp] at hi
    let Cq : ℝ≥0 := ⟨B, hB0⟩ ^ (t1N : ℝ) *
      ⟨2 * E n, by positivity⟩ ^ (t2N : ℝ)
    have hd := aux_lem_skeleton_smooth_approx_holderOnWith_direct
      (A := S) (f := q n) (C := (Cq : ℝ)) (r := beta)
      (Cq.coe_nonneg) betaN.coe_nonneg hi
    have hCq : (Cq : ℝ) = I n := by
      have h1 : (t1N : ℝ) = beta / theta := rfl
      have h2 : (t2N : ℝ) = 1 - beta / theta := rfl
      have hB : (↑(NNReal.mk B hB0) : ℝ) = B := rfl
      have hE : (↑(NNReal.mk (2 * E n) (by positivity)) : ℝ) = 2 * E n := rfl
      have he := NNReal.coe_mul ((NNReal.mk B hB0) ^ (t1N : ℝ)) ((NNReal.mk (2 * E n) (by positivity)) ^ (t2N : ℝ))
      rw [NNReal.coe_rpow, NNReal.coe_rpow, h1, h2, hB, hE] at he
      simpa only [Cq, I] using! he
    simpa [hCq] using! hd x hx y hy
  have hcnorm : ∀ n, Lane4.cAlphaNorm beta S (q n) ≤ E n + I n := by
    intro n
    exact aux_lem_skeleton_smooth_approx_cAlpha_bound beta hbeta0 S (q n)
      (E n) (I n) (hE0 n) (by positivity) (hqval n) (hqpairI n)
  have he_tendsto : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hEtendsto : Tendsto E atTop (𝓝 (0 : ℝ)) := by
    have hs := he_tendsto.mul_const (R / 2 + r)
    have hp := hs.rpow
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => theta) atTop (𝓝 theta))
      (Or.inr htheta0)
    have hk : Tendsto (fun _ : ℕ => (K : ℝ)) atTop (𝓝 (K : ℝ)) := tendsto_const_nhds
    have hm := hk.mul hp
    simpa [E, Real.zero_rpow htheta0.ne'] using! hm
  have hItendsto : Tendsto I atTop (𝓝 (0 : ℝ)) := by
    have htwo : Tendsto (fun n => 2 * E n) atTop (𝓝 (0 : ℝ)) := by
      convert hEtendsto.const_mul 2 using 1 <;> simp
    have hp := htwo.rpow
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => 1 - beta / theta) atTop
        (𝓝 (1 - beta / theta))) (Or.inr ht2)
    have hc : Tendsto (fun _ : ℕ => B ^ (beta / theta)) atTop
        (𝓝 (B ^ (beta / theta))) := tendsto_const_nhds
    have hm := hc.mul hp
    simpa [I, Real.zero_rpow ht2.ne'] using! hm
  have hsum : Tendsto (fun n => E n + I n) atTop (𝓝 (0 : ℝ)) := by
    simpa using! hEtendsto.add hItendsto
  have hnonnegNorm : ∀ n, 0 ≤ Lane4.cAlphaNorm beta S (q n) := by
    intro n
    unfold Lane4.cAlphaNorm
    apply add_nonneg
    · apply Real.sSup_nonneg
      intro v hv
      rcases hv with ⟨x, hx, rfl⟩
      exact abs_nonneg _
    · apply Real.sSup_nonneg
      intro v hv
      rcases hv with ⟨x, hx, y, hy, hxy, rfl⟩
      exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  have hfinal : Tendsto (fun n => Lane4.cAlphaNorm beta S (q n)) atTop (𝓝 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hsum
      (Filter.Eventually.of_forall (fun n => hnonnegNorm n))
      (Filter.Eventually.of_forall (fun n => hcnorm n))
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (contDiff_inwardMollification hrho hgcont.locallyIntegrable hr (hscale n)).of_le (by simp)
  · intro n
    exact hasCompactSupport_inwardMollification hU hrho hsupport hball hr (hscale n)
  · intro n
    exact tsupport_inwardMollification_subset hU hrho hsupport hball hr (hscale n)
  · simpa [q, S] using! hfinal

end Paper
