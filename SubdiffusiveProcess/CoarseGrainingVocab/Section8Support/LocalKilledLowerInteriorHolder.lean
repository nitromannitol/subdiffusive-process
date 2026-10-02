import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.Interior.InhomogeneousLocalRegularity
import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput




set_option autoImplicit false

open MeasureTheory Topology Homogenization Set
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower

variable {d : ℕ}

/-! ### Elementary Euclidean-ball facts -/

/-- Membership in an explicit Euclidean ball, in distance form. -/
theorem mem_euclideanBall_iff_euclideanDist_lt {x y : Vec d} {r : ℝ} (hr : 0 < r) :
    y ∈ euclideanBall x r ↔ euclideanDist y x < r := by
  have h0 : 0 ≤ euclideanDist y x := euclideanNorm_nonneg _
  constructor
  · intro hy
    have hy' : euclideanDist y x ^ 2 < r ^ 2 := by
      simpa [euclideanSqDist_eq_euclideanDist_sq] using hy
    nlinarith
  · intro hy
    have : euclideanDist y x ^ 2 < r ^ 2 := by nlinarith
    simpa [euclideanBall, euclideanSqDist_eq_euclideanDist_sq] using this

/-- The triangle inequality for the explicit Euclidean distance. -/
theorem euclideanDist_triangle (x y z : Vec d) :
    euclideanDist x z ≤ euclideanDist x y + euclideanDist y z := by
  simp only [euclideanDist_eq_norm_sub_ofVec]
  simpa using
    norm_sub_le_norm_sub_add_norm_sub (HilbertVec.ofVec x) (HilbertVec.ofVec y)
      (HilbertVec.ofVec z)

/-! ### A continuous function almost everywhere bounded on an open set is bounded -/

/-- A function continuous on an open set and almost everywhere equal there to a
bounded function is bounded everywhere on that set.  (`volume` on `Vec d` gives
positive mass to every nonempty open set, so a nonempty open exceptional set is
impossible.) -/
theorem abs_le_of_continuousOn_of_ae_le {V : Set (Vec d)} (hV : IsOpen V)
    {w f : Vec d → ℝ} (hcont : ContinuousOn w V)
    (hae : w =ᵐ[volume.restrict V] f) {M : ℝ}
    (hf : ∀ᵐ z ∂(volume.restrict V), |f z| ≤ M) :
    ∀ z ∈ V, |w z| ≤ M := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨z₀, hz₀V, hz₀⟩ := hcon
  set S : Set (Vec d) := V ∩ (fun z => |w z|) ⁻¹' Ioi M with hS
  have hSopen : IsOpen S :=
    hcont.abs.isOpen_inter_preimage hV isOpen_Ioi
  have hSne : S.Nonempty := ⟨z₀, hz₀V, hz₀⟩
  have hSpos : 0 < volume S := hSopen.measure_pos volume hSne
  have hSsub : S ⊆ V := fun _ hz => hz.1
  have hzero : volume.restrict V S = 0 := by
    refine measure_mono_null (fun z hz => ?_) (?_ : volume.restrict V {z | M < |w z|} = 0)
    · exact hz.2
    · have hb : ∀ᵐ z ∂(volume.restrict V), |w z| ≤ M := by
        filter_upwards [hae, hf] with z hz1 hz2
        rw [hz1]; exact hz2
      rw [ae_iff] at hb
      simpa [not_le] using hb
  rw [Measure.restrict_apply₀' hV.measurableSet.nullMeasurableSet,
    Set.inter_eq_self_of_subset_left hSsub] at hzero
  exact absurd hzero hSpos.ne'

/-! ### The frozen ball, with its Hölder constant kept -/

/-- **One frozen ball, with its constant.**  Around every point of the carrier
there is a ball on which the canonical shrinking-ball-average representative of
an inhomogeneous divergence-form weak solution is continuous, agrees a.e. with
the solution, and is Hölder-`1/2` with an explicit finite constant.

This is `exists_physicalBallRepresentative_smallContrast_inhomogeneous` with the
freezing radius supplied by continuity of the coefficient — the same argument as
the private `exists_localContinuousRepresentative_inhomogeneous`, except that the
Hölder clause is **kept** rather than discarded. -/
theorem exists_frozenBall_euclideanHolderBoundOn [NeZero d] (hd : 2 ≤ d)
    {W : Set (Vec d)} (hW : IsOpen W) {s : Vec d → ℝ}
    (hs : ContinuousOn s W) (hspos : ∀ x ∈ W, 0 < s x)
    {u : H1Function W} {g : Vec d → Vec d}
    (hu : IsDivFormWeakSolutionOn s W u g)
    (hg : MemVectorLpOn W (schauderSourceExponent d (1 / 2)) g)
    {x : Vec d} (hx : x ∈ W) :
    ∃ r : ℝ, 0 < r ∧ euclideanBall x r ⊆ W ∧ ∃ C : ℝ, 0 ≤ C ∧
      EuclideanHolderBoundOn (euclideanBall x r) (1 / 2) C
        (euclideanBallAverageRepresentative u.toFun) ∧
      ContinuousOn (euclideanBallAverageRepresentative u.toFun) (euclideanBall x r) ∧
      (euclideanBallAverageRepresentative u.toFun)
        =ᵐ[volume.restrict (euclideanBall x r)] u.toFun := by
  set delta := smallContrastThreshold d (1 / 2) with hdeltadef
  have hdelta : 0 < delta := by
    rw [hdeltadef]
    dsimp only [smallContrastThreshold]
    exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num)
  have hdelta1 : delta < 1 :=
    (smallContrastThreshold_le_eighth_gap d (by norm_num)).trans_lt (by norm_num)
  have hsx : 0 < s x := hspos x hx
  have htcont : ContinuousAt (fun y => (s x)⁻¹ * s y) x :=
    continuousAt_const.mul (hs.continuousAt (hW.mem_nhds hx))
  obtain ⟨eta, heta, hcloseEta⟩ := (Metric.continuousAt_iff.1 htcont) delta hdelta
  obtain ⟨etaW, hetaW, hballW⟩ := Metric.isOpen_iff.1 hW x hx
  set rho := min eta etaW with hrhodef
  have hrho : 0 < rho := lt_min heta hetaW
  have houter : euclideanBall x rho ⊆ W := by
    intro y hy
    exact hballW ((euclideanBall_subset_metricBall hrho hy).trans_le (min_le_right eta etaW))
  have hcenter : (s x)⁻¹ * s x = 1 := inv_mul_cancel₀ hsx.ne'
  have hclose : ∀ y ∈ euclideanBall x rho, |(s x)⁻¹ * s y - 1| ≤ delta := by
    intro y hy
    have hydist : dist y x < eta :=
      (euclideanBall_subset_metricBall hrho hy).trans_le (min_le_left eta etaW)
    have h := hcloseEta hydist
    rw [Real.dist_eq, hcenter] at h
    exact h.le
  obtain ⟨uRep, huCont, huAE, huHolder, huCanon⟩ :=
    exists_physicalBallRepresentative_smallContrast_inhomogeneous
      hW hs hu hrho houter (s x) delta (1 / 2) hd
      (by constructor <;> norm_num) hdelta.le le_rfl hdelta1 hclose hg
  have hballsub : euclideanBall x (rho / 2) ⊆ euclideanBall x rho :=
    euclideanBall_subset_euclideanBall (by positivity) (by linarith)
  refine ⟨rho / 2, by positivity, hballsub.trans houter, ?_⟩
  refine ⟨max 0 (smallContrastSchauderConstant d *
      smallContrastDataSize d (1 / 2)
        (ballToUnitH1 x hrho (u.restrict (isOpen_euclideanBall x rho) houter))
        (ballToUnitSource g x rho (s x)) * rho ^ (1 - (1 / 2 : ℝ))),
    le_max_left _ _, ?_, ?_, ?_⟩
  · intro y hy z hz
    have hy' := huCanon y hy
    have hz' := huCanon z hz
    rw [hy', hz']
    refine (huHolder y hy z hz).trans ?_
    gcongr
    · exact Real.rpow_nonneg (euclideanNorm_nonneg _) _
    · exact le_max_right _ _
  · exact huCont.congr fun y hy => huCanon y hy
  · refine huAE.mp ?_
    refine (ae_restrict_iff' (isOpen_euclideanBall x (rho / 2)).measurableSet).2 ?_
    exact Filter.Eventually.of_forall fun y hy hy2 => (huCanon y hy).trans hy2

/-! ### The uniform bound on a compact subset -/

/-- Finitely many local Hölder bounds and an almost-everywhere bound give one
Hölder constant on a compact set. -/
theorem exists_euclideanHolderBoundOn_compact_of_local
    {W K : Set (Vec d)} {u w : Vec d → ℝ} {M : ℝ}
    (hM : ∀ᵐ z ∂(volume.restrict W), |u z| ≤ M)
    (hK : IsCompact K)
    (hball : ∀ x ∈ K, ∃ r : ℝ, 0 < r ∧ euclideanBall x r ⊆ W ∧
      ∃ C : ℝ, 0 ≤ C ∧ EuclideanHolderBoundOn (euclideanBall x r) (1 / 2) C w ∧
        ContinuousOn w (euclideanBall x r) ∧
        w =ᵐ[volume.restrict (euclideanBall x r)] u) :
    ∃ C : ℝ, 0 ≤ C ∧ EuclideanHolderBoundOn K (1 / 2) C w := by
  rcases Set.eq_empty_or_nonempty K with rfl | hKne
  · exact ⟨0, le_rfl, by simp [EuclideanHolderBoundOn]⟩
  choose! r hrpos hrsub C hCnn hCholder hCcont hCae using hball
  -- the balls of half the frozen radius cover `K`
  have hcover : K ⊆ ⋃ x ∈ K, euclideanBall x (r x / 2) := by
    intro y hy
    refine Set.mem_biUnion hy ?_
    have hry : 0 < r y := hrpos y hy
    show euclideanSqDist y y < (r y / 2) ^ 2
    rw [euclideanSqDist_self]
    positivity
  obtain ⟨T, hTK, hTfin, hTcover⟩ :=
    hK.elim_finite_subcover_image (fun x _ => isOpen_euclideanBall x (r x / 2)) hcover
  set F := hTfin.toFinset with hFdef
  have hmemF : ∀ {x : Vec d}, x ∈ F ↔ x ∈ T := by
    intro x; rw [hFdef, Set.Finite.mem_toFinset]
  have hpick : ∀ y ∈ K, ∃ x, x ∈ F ∧ y ∈ euclideanBall x (r x / 2) := by
    intro y hy
    obtain ⟨x, hxT, hyx⟩ := Set.mem_iUnion₂.1 (hTcover hy)
    exact ⟨x, hmemF.2 hxT, hyx⟩
  have hFne : F.Nonempty := by
    obtain ⟨y, hy⟩ := hKne
    obtain ⟨x, hxF, -⟩ := hpick y hy
    exact ⟨x, hxF⟩
  -- a positive Lebesgue radius for the finite subcover
  set lam := F.inf' hFne (fun x => r x / 2) with hlamdef
  have hlam : 0 < lam := by
    rw [hlamdef, Finset.lt_inf'_iff]
    intro x hx
    have := hrpos x (hTK (hmemF.1 hx))
    linarith
  -- the sup bound transported to the representative
  have hsup : ∀ y ∈ K, |w y| ≤ M := by
    intro y hy
    obtain ⟨x, hxF, hyx⟩ := hpick y hy
    have hxK : x ∈ K := hTK (hmemF.1 hxF)
    have hyball : y ∈ euclideanBall x (r x) :=
      euclideanBall_subset_euclideanBall (by have := hrpos x hxK; positivity)
        (by have := hrpos x hxK; linarith) hyx
    refine abs_le_of_continuousOn_of_ae_le (isOpen_euclideanBall x (r x))
      (hCcont x hxK) (hCae x hxK) ?_ y hyball
    exact ae_restrict_of_ae_restrict_of_subset (hrsub x hxK) hM
  -- the constant
  set Csum := ∑ x ∈ F, C x with hCsumdef
  have hCsumnn : 0 ≤ Csum := Finset.sum_nonneg fun x hx => hCnn x (hTK (hmemF.1 hx))
  have hCle : ∀ x ∈ F, C x ≤ Csum := fun x hx =>
    Finset.single_le_sum (fun y hy => hCnn y (hTK (hmemF.1 hy))) hx
  set Mplus := max M 0 with hMplusdef
  have hMplus : 0 ≤ Mplus := le_max_right _ _
  have hlampow : 0 < lam ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hlam _
  refine ⟨Csum + 2 * Mplus / lam ^ ((1 : ℝ) / 2), by positivity, ?_⟩
  intro y hy z hz
  rcases lt_or_ge (euclideanDist y z) lam with hnear | hfar
  · -- a common frozen ball
    obtain ⟨x, hxF, hyx⟩ := hpick y hy
    have hxK : x ∈ K := hTK (hmemF.1 hxF)
    have hrx : 0 < r x := hrpos x hxK
    have hlamle : lam ≤ r x / 2 := by
      rw [hlamdef]; exact Finset.inf'_le _ hxF
    have hyd : euclideanDist y x < r x / 2 :=
      (mem_euclideanBall_iff_euclideanDist_lt (by positivity)).1 hyx
    have hzd : euclideanDist z x < r x := by
      have h1 : euclideanDist z x ≤ euclideanDist z y + euclideanDist y x :=
        euclideanDist_triangle z y x
      rw [euclideanDist_comm z y] at h1
      linarith
    have hyball : y ∈ euclideanBall x (r x) :=
      euclideanBall_subset_euclideanBall (by positivity) (by linarith) hyx
    have hzball : z ∈ euclideanBall x (r x) :=
      (mem_euclideanBall_iff_euclideanDist_lt hrx).2 hzd
    refine (hCholder x hxK y hyball z hzball).trans ?_
    have hpow : (0 : ℝ) ≤ euclideanNorm (y - z) ^ ((1 : ℝ) / 2) :=
      Real.rpow_nonneg (euclideanNorm_nonneg _) _
    have : C x ≤ Csum + 2 * Mplus / lam ^ ((1 : ℝ) / 2) := by
      have := hCle x hxF
      have h2 : (0 : ℝ) ≤ 2 * Mplus / lam ^ ((1 : ℝ) / 2) := by positivity
      linarith
    exact mul_le_mul_of_nonneg_right this hpow
  · -- far apart: use the `L^∞` bound
    have hMy := hsup y hy
    have hMz := hsup z hz
    have hMnn : 0 ≤ M := le_trans (abs_nonneg _) hMy
    have hdiff : |w y - w z| ≤ 2 * Mplus := by
      have : |w y - w z| ≤ |w y| + |w z| := abs_sub _ _
      have hMM : M ≤ Mplus := le_max_left _ _
      linarith
    have hpowmono : lam ^ ((1 : ℝ) / 2) ≤ euclideanNorm (y - z) ^ ((1 : ℝ) / 2) := by
      refine Real.rpow_le_rpow hlam.le ?_ (by norm_num)
      simpa [euclideanDist] using hfar
    have hstep : 2 * Mplus ≤ (2 * Mplus / lam ^ ((1 : ℝ) / 2)) *
        euclideanNorm (y - z) ^ ((1 : ℝ) / 2) := by
      have h1 : (2 * Mplus / lam ^ ((1 : ℝ) / 2)) * lam ^ ((1 : ℝ) / 2) = 2 * Mplus := by
        field_simp
      calc 2 * Mplus = (2 * Mplus / lam ^ ((1 : ℝ) / 2)) * lam ^ ((1 : ℝ) / 2) := h1.symm
        _ ≤ (2 * Mplus / lam ^ ((1 : ℝ) / 2)) * euclideanNorm (y - z) ^ ((1 : ℝ) / 2) := by
            have hnn : (0 : ℝ) ≤ 2 * Mplus / lam ^ ((1 : ℝ) / 2) := by positivity
            exact mul_le_mul_of_nonneg_left hpowmono hnn
    refine hdiff.trans (hstep.trans ?_)
    have hpow : (0 : ℝ) ≤ euclideanNorm (y - z) ^ ((1 : ℝ) / 2) :=
      Real.rpow_nonneg (euclideanNorm_nonneg _) _
    have : 2 * Mplus / lam ^ ((1 : ℝ) / 2) ≤ Csum + 2 * Mplus / lam ^ ((1 : ℝ) / 2) := by
      linarith
    exact mul_le_mul_of_nonneg_right this hpow



theorem exists_euclideanHolderBoundOn_compact [NeZero d] (hd : 2 ≤ d)
    {W : Set (Vec d)} (hW : IsOpen W) {s : Vec d → ℝ}
    (hs : ContinuousOn s W) (hspos : ∀ x ∈ W, 0 < s x)
    {u : H1Function W} {g : Vec d → Vec d}
    (hu : IsDivFormWeakSolutionOn s W u g)
    (hg : MemVectorLpOn W (schauderSourceExponent d (1 / 2)) g)
    {M : ℝ} (hM : ∀ᵐ z ∂(volume.restrict W), |u.toFun z| ≤ M)
    {K : Set (Vec d)} (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ C : ℝ, 0 ≤ C ∧
      EuclideanHolderBoundOn K (1 / 2) C
        (euclideanBallAverageRepresentative u.toFun) := by
  apply exists_euclideanHolderBoundOn_compact_of_local hM hK
  intro x hx
  exact exists_frozenBall_euclideanHolderBoundOn hd hW hs hspos hu hg (hKW hx)



theorem exists_euclideanHolderBoundOn_of_coefficientC11On [NeZero d] (hd : 2 ≤ d)
    {W : Set (Vec d)} (hW : IsOpen W) {s : Vec d → ℝ}
    (hs : CoefficientC11On W s) (hspos : ∀ x ∈ W, 0 < s x)
    {u : H1Function W} {g : Vec d → Vec d}
    (hu : IsDivFormWeakSolutionOn s W u g)
    (hg : MemVectorLpOn W (schauderSourceExponent d (1 / 2)) g)
    {M : ℝ} (hM : ∀ᵐ z ∂(volume.restrict W), |u.toFun z| ≤ M)
    {K : Set (Vec d)} (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ C : ℝ, 0 ≤ C ∧
      EuclideanHolderBoundOn K (1 / 2) C
        (euclideanBallAverageRepresentative u.toFun) := by
  obtain ⟨Ds, hDs, -⟩ := hs
  refine exists_euclideanHolderBoundOn_compact hd hW ?_ hspos hu hg hM hK hKW
  intro x hx
  exact ((hDs x hx).differentiableAt.continuousAt).continuousWithinAt

/-! ### The shape `holder_repr` asks for -/

/-- The Euclidean Hölder bound rewritten in the ambient (sup) metric of `Vec d`,
which is the metric `HeatKernelRegularity.ResolventRegularityDatum.holder_repr`
uses (`dist x y ^ a`).  Only the two-sided norm comparison
`euclideanNorm z ≤ d * ‖z‖` is involved. -/
theorem holder_dist_of_euclideanHolderBoundOn {K : Set (Vec d)} {C : ℝ} (hC : 0 ≤ C)
    {w : Vec d → ℝ} (h : EuclideanHolderBoundOn K (1 / 2) C w) :
    ∀ x ∈ K, ∀ y ∈ K,
      |w x - w y| ≤ (C * (d : ℝ) ^ ((1 : ℝ) / 2)) * dist x y ^ ((1 : ℝ) / 2) := by
  intro x hx y hy
  refine (h x hx y hy).trans ?_
  have hdist : dist x y = ‖x - y‖ := (dist_eq_norm x y)
  have hle : euclideanNorm (x - y) ≤ (d : ℝ) * dist x y := by
    rw [hdist]; exact euclideanNorm_le_dimension_mul_norm _
  have hpow : euclideanNorm (x - y) ^ ((1 : ℝ) / 2)
      ≤ ((d : ℝ) * dist x y) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow (euclideanNorm_nonneg _) hle (by norm_num)
  have hsplit : ((d : ℝ) * dist x y) ^ ((1 : ℝ) / 2)
      = (d : ℝ) ^ ((1 : ℝ) / 2) * dist x y ^ ((1 : ℝ) / 2) :=
    Real.mul_rpow (by positivity) dist_nonneg
  calc C * euclideanNorm (x - y) ^ ((1 : ℝ) / 2)
      ≤ C * ((d : ℝ) * dist x y) ^ ((1 : ℝ) / 2) := by
        exact mul_le_mul_of_nonneg_left hpow hC
    _ = (C * (d : ℝ) ^ ((1 : ℝ) / 2)) * dist x y ^ ((1 : ℝ) / 2) := by
        rw [hsplit]; ring

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower
