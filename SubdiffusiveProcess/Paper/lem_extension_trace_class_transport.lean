import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Sobolev.NativeH1
import SubdiffusiveProcess.Lane4.Bridge
import Homogenization.Sobolev.Truncation.Basic
import Homogenization.Sobolev.Truncation.H10Limit
import Homogenization.Sobolev.Truncation.LevelSets
open MeasureTheory Set TopologicalSpace Filter Homogenization SubdiffusiveProcess
  SubdiffusiveProcess.Lane4
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper


theorem lem_extension_trace_class_transport
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (u : weakSobolevGraph (centeredCube z r hr))
    (U : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (closedCube z r hr))
    (hrep : ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U)
    (hzero : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0) :
    (u : SobolevData (centeredCube z r hr)) ∈ killedSobolevGraph (centeredCube z r hr) := by
  classical
  let C : Set (SpatialCoordinates d) := closedCube z r hr
  let W : SpatialCoordinates d → ℝ := fun x => if x ∈ C then U x else 0
  have hCcompact : IsCompact C := by
    change IsCompact (Metric.closedBall z (r / 2))
    exact isCompact_closedBall z (r / 2)
  have hCclosed : IsClosed C := hCcompact.isClosed
  have hΩC : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ C := by
    exact centeredCube_subset_closedCube z hr
  have hW_U : W =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U := by
    filter_upwards [ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx
    simp only [W]
    rw [if_pos (hΩC hx)]
  obtain ⟨v₀, hv₀val, hv₀grad⟩ :=
    SubdiffusiveProcess.exists_nativeH1Function_of_weakSobolevGraph u
  have hrepW : (fun x => u.val.1 x) =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))] W :=
    hrep.trans hW_U.symm
  have hv₀W : v₀.toFun =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] W := by
    rw [hv₀val]
    exact hrepW
  have hWmem : MemLp W 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    exact (memLp_congr_ae hv₀W).mp v₀.memL2
  have hWweak : HasWeakGradientOn (centeredCube z r hr : Set (SpatialCoordinates d))
      W v₀.grad := by
    intro i φ hφ hφcomp hφsub
    have h0 := v₀.hasWeakGradient i φ hφ hφcomp hφsub
    calc
      ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          W x * (fderiv ℝ φ x) (basisVec i) ∂volume =
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          v₀.toFun x * (fderiv ℝ φ x) (basisVec i) ∂volume := by
            apply integral_congr_ae
            filter_upwards [hv₀W] with x hx
            rw [hx]
      _ = -∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          v₀.grad x i * φ x ∂volume := h0
  let v : Homogenization.H1Function (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    { toFun := W
      grad := v₀.grad
      memL2 := hWmem
      gradMemL2 := v₀.gradMemL2
      hasWeakGradient := hWweak }
  have hv_toFun : v.toFun = W := rfl
  have hv_grad : v.grad = v₀.grad := rfl
  have hDom : Homogenization.IsOpenBoundedConvexDomain
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    change Homogenization.IsOpenBoundedConvexDomain (Metric.ball z (r / 2))
    exact Homogenization.isOpenBoundedConvexDomain_ball z (by linarith)
  let c : ℕ → ℝ := fun n => 1 / (n + 1)
  have hcpos : ∀ n, 0 < c n := by
    intro n
    dsimp [c]
    positivity
  have hclim : Tendsto c atTop (nhds 0) := by
    simpa [c] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (nhds 0))
  let K : ℕ → Set (SpatialCoordinates d) := fun n =>
    (C ∩ U ⁻¹' Set.Ici (c n)) ∪
      (C ∩ (fun x => -U x) ⁻¹' Set.Ici (c n))
  have hKcompact : ∀ n, IsCompact (K n) := by
    intro n
    apply IsCompact.union
    · apply IsCompact.of_isClosed_subset hCcompact
        (hU.preimage_isClosed_of_isClosed hCclosed isClosed_Ici)
      exact inter_subset_left
    · apply IsCompact.of_isClosed_subset hCcompact
        (hU.neg.preimage_isClosed_of_isClosed hCclosed isClosed_Ici)
      exact inter_subset_left
  have hKsub : ∀ n, K n ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    intro n x hx
    rcases hx with hx | hx
    · have hxC : x ∈ Metric.closedBall z (r / 2) := by
        exact hx.1
      by_contra hxΩ
      have hxfront : x ∈ frontier (Metric.ball z (r / 2)) := by
        rw [frontier_ball z (by positivity : r / 2 ≠ 0)]
        rw [← Metric.closedBall_diff_ball]
        exact ⟨hxC, hxΩ⟩
      have hxzero : U x = 0 := hzero x (by simpa [centeredCube] using hxfront)
      have hcx : c n ≤ U x := hx.2
      linarith [hcpos n]
    · have hxC : x ∈ Metric.closedBall z (r / 2) := by
        exact hx.1
      by_contra hxΩ
      have hxfront : x ∈ frontier (Metric.ball z (r / 2)) := by
        rw [frontier_ball z (by positivity : r / 2 ≠ 0)]
        rw [← Metric.closedBall_diff_ball]
        exact ⟨hxC, hxΩ⟩
      have hxzero : U x = 0 := hzero x (by simpa [centeredCube] using hxfront)
      have hcx : c n ≤ -U x := hx.2
      linarith [hcpos n]
  have hexp : ∀ n, ∃ q : Homogenization.H1Function
      (centeredCube z r hr : Set (SpatialCoordinates d)),
      q.toFun = (fun x => max (v.toFun x - c n) 0) ∧
      (∀ᵐ x ∂volumeMeasureOn (centeredCube z r hr : Set (SpatialCoordinates d)),
        q.grad x = {y | c n < v.toFun y}.indicator v.grad x) := by
    intro n
    exact Homogenization.exists_h1_max_sub_const hDom v (c n)
  choose p hp hpgrad using hexp
  have hexq : ∀ n, ∃ w : Homogenization.H1Function
      (centeredCube z r hr : Set (SpatialCoordinates d)),
      w.toFun = (fun x => max ((-v).toFun x - c n) 0) ∧
      (∀ᵐ x ∂volumeMeasureOn (centeredCube z r hr : Set (SpatialCoordinates d)),
        w.grad x = {y | c n < (-v).toFun y}.indicator (-v).grad x) := by
    intro n
    exact Homogenization.exists_h1_max_sub_const hDom (-v) (c n)
  choose q hq hqgrad using hexq
  let F : ℕ → Homogenization.H1Function
      (centeredCube z r hr : Set (SpatialCoordinates d)) := fun n => p n - q n
  have hFval : ∀ n, (F n).toFun = fun x =>
      max (v.toFun x - c n) 0 - max ((-v).toFun x - c n) 0 := by
    intro n
    simp only [F, Homogenization.H1Function.sub_toFun, hp n, hq n]
  have hFmem : ∀ n, Homogenization.MemH10
      (centeredCube z r hr : Set (SpatialCoordinates d)) (F n).toFun := by
    intro n
    apply Homogenization.memH10_of_compactSupport hDom (F n) (hKcompact n) (hKsub n)
    intro x hx
    rw [hFval n]
    by_cases hxC : x ∈ C
    · have hxU1 : ¬ c n ≤ U x := by
        intro hxc
        exact hx (Or.inl ⟨hxC, hxc⟩)
      have hxU2 : ¬ c n ≤ -U x := by
        intro hxc
        exact hx (Or.inr ⟨hxC, hxc⟩)
      simp only [hv_toFun, W, if_pos hxC, Homogenization.H1Function.neg_toFun]
      rw [max_eq_right (by linarith), max_eq_right (by linarith)]
      ring
    · simp only [hv_toFun, W, if_neg hxC, Homogenization.H1Function.neg_toFun]
      have hc : 0 ≤ c n := (hcpos n).le
      rw [max_eq_right (by linarith), max_eq_right (by linarith)]
      ring
  have hFval' : ∀ n, (F n).toFun = fun x =>
      max (v.toFun x - c n) 0 - max (-v.toFun x - c n) 0 := by
    intro n
    rw [hFval n]
    funext x
    simp only [Homogenization.H1Function.neg_toFun]
  have hsoft_bound : ∀ (a b : ℝ), 0 ≤ b →
      |max (a - b) 0 - max (-a - b) 0| ≤ |a| := by
    intro a b hb
    by_cases ha : 0 ≤ a
    · have hneg : max (-a - b) 0 = 0 := max_eq_right (by linarith)
      rw [hneg, sub_zero, abs_of_nonneg (le_max_right _ _), abs_of_nonneg ha]
      exact max_le (by linarith) (by linarith)
    · have ha' : a ≤ 0 := le_of_not_ge ha
      have hpos : max (a - b) 0 = 0 := max_eq_right (by linarith)
      rw [hpos, zero_sub, abs_neg, abs_of_nonneg (le_max_right _ _), abs_of_nonpos ha']
      exact max_le (by linarith) (by linarith)
  have hsoft_tendsto : ∀ a : ℝ,
      Tendsto (fun n => max (a - c n) 0 - max (-a - c n) 0) atTop (nhds a) := by
    intro a
    have h₁ : Tendsto (fun n => max (a - c n) 0) atTop (nhds (max a 0)) := by
      simpa only [sub_zero] using
        (((tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (nhds a)).sub hclim).max
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)))
    have h₂ : Tendsto (fun n => max (-a - c n) 0) atTop (nhds (max (-a) 0)) := by
      simpa only [sub_zero] using
        (((tendsto_const_nhds : Tendsto (fun _ : ℕ => -a) atTop (nhds (-a))).sub hclim).max
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)))
    have h := h₁.sub h₂
    have hid : max a 0 - max (-a) 0 = a := by
      rcases le_total 0 a with ha | ha <;> simp [max_eq_left, max_eq_right, ha]
    simpa [hid] using h
  have hF_aesm : ∀ n, AEStronglyMeasurable (F n).toFun
      (volumeMeasureOn (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    intro n
    exact (F n).memL2.1
  have hF_bound : ∀ n, ∀ᵐ x ∂volumeMeasureOn
      (centeredCube z r hr : Set (SpatialCoordinates d)),
      ‖(F n).toFun x‖ ≤ ‖v.toFun x‖ := by
    intro n
    filter_upwards with x
    rw [hFval' n, Real.norm_eq_abs, Real.norm_eq_abs]
    exact hsoft_bound _ _ (hcpos n).le
  have hF_tendsto : ∀ᵐ x ∂volumeMeasureOn
      (centeredCube z r hr : Set (SpatialCoordinates d)),
      Tendsto (fun n => (F n).toFun x) atTop (nhds (v.toFun x)) := by
    filter_upwards with x
    rw [show v.toFun x = v.toFun x from rfl]
    simpa [hFval'] using hsoft_tendsto (v.toFun x)
  have hfun : Tendsto
      (fun n => eLpNorm (fun x => v.toFun x - (F n).toFun x) 2
        (volumeMeasureOn (centeredCube z r hr : Set (SpatialCoordinates d))))
      atTop (nhds 0) := by
    have h := Homogenization.tendsto_eLpNorm_two_of_tendsto_ae_of_dominated
      hF_aesm v.memL2 v.memL2.norm hF_bound hF_tendsto
    rw [show (fun n => eLpNorm (fun x => v.toFun x - (F n).toFun x) 2
        (volumeMeasureOn (centeredCube z r hr : Set (SpatialCoordinates d)))) =
        (fun n => eLpNorm (fun x => (F n).toFun x - v.toFun x) 2
          (volumeMeasureOn (centeredCube z r hr : Set (SpatialCoordinates d)))) from by
          funext n
          exact Homogenization.eLpNorm_sub_swap v.toFun (F n).toFun]
    exact h
  have hgrad_aesm : ∀ n i, AEStronglyMeasurable (fun x => (F n).grad x i)
      (volumeMeasureOn (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    intro n i
    exact (F n).gradMemL2 i |>.1
  have hgrad_bound : ∀ n i, ∀ᵐ x ∂volumeMeasureOn
      (centeredCube z r hr : Set (SpatialCoordinates d)),
      ‖(F n).grad x i‖ ≤ ‖v.grad x i‖ := by
    intro n i
    filter_upwards [hpgrad n, hqgrad n] with x hpX hqX
    have hpI := congrFun hpX i
    have hqI := congrFun hqX i
    simp only [F, Homogenization.H1Function.sub_grad, Pi.sub_apply]
    rw [hpI, hqI]
    simp only [Set.indicator_apply]
    by_cases h₁ : c n < v.toFun x
    · have h₂ : ¬c n < (-v).toFun x := by
        simp only [Homogenization.H1Function.neg_toFun]
        linarith [hcpos n]
      have h₂' : ¬c n < -v.toFun x := by
        simpa only [Homogenization.H1Function.neg_toFun] using h₂
      simp [h₁, h₂']
    · by_cases h₂ : c n < (-v).toFun x
      · have h₂' : c n < -v.toFun x := by
          simpa only [Homogenization.H1Function.neg_toFun] using h₂
        simp only [Homogenization.H1Function.neg_grad]
        simp [h₁, h₂']
      · have h₂' : ¬c n < -v.toFun x := by
          simpa only [Homogenization.H1Function.neg_toFun] using h₂
        simp [h₁, h₂']
  have hpgrad_all : ∀ᵐ x ∂volumeMeasureOn
      (centeredCube z r hr : Set (SpatialCoordinates d)), ∀ n,
      (p n).grad x = {y | c n < v.toFun y}.indicator v.grad x :=
    ae_all_iff.mpr hpgrad
  have hqgrad_all : ∀ᵐ x ∂volumeMeasureOn
      (centeredCube z r hr : Set (SpatialCoordinates d)), ∀ n,
      (q n).grad x = {y | c n < (-v).toFun y}.indicator (-v).grad x :=
    ae_all_iff.mpr hqgrad
  have hzero_grad : ∀ᵐ x ∂volumeMeasureOn
      (centeredCube z r hr : Set (SpatialCoordinates d)),
      v.toFun x = 0 → v.grad x = 0 :=
    Homogenization.grad_ae_zero_on_level_set hDom v 0
  have hFgrad_eq : ∀ᵐ x ∂volumeMeasureOn
      (centeredCube z r hr : Set (SpatialCoordinates d)), ∀ n i,
      (F n).grad x i =
        (if c n < v.toFun x then v.grad x i else 0) -
          (if c n < -v.toFun x then -v.grad x i else 0) := by
    filter_upwards [hpgrad_all, hqgrad_all] with x hpX hqX n i
    have hpI := congrFun (hpX n) i
    have hqI := congrFun (hqX n) i
    simp only [F, Homogenization.H1Function.sub_grad, Pi.sub_apply]
    rw [hpI, hqI]
    simp only [Set.indicator_apply, Set.mem_setOf_eq,
      Homogenization.H1Function.neg_toFun,
      Homogenization.H1Function.neg_grad]
    by_cases h₁ : c n < v.toFun x <;>
      by_cases h₂ : c n < -v.toFun x <;>
      simp [h₁, h₂]
  have hgrad_tendsto : ∀ i, ∀ᵐ x ∂volumeMeasureOn
      (centeredCube z r hr : Set (SpatialCoordinates d)),
      Tendsto (fun n => (F n).grad x i) atTop (nhds (v.grad x i)) := by
    intro i
    filter_upwards [hFgrad_eq, hzero_grad] with x hFx hzeroX
    have hFx' : ∀ n, (F n).grad x i =
        (if c n < v.toFun x then v.grad x i else 0) -
          (if c n < -v.toFun x then -v.grad x i else 0) :=
      fun n => hFx n i
    rcases lt_trichotomy 0 (v.toFun x) with ha | ha | ha
    · have hc_event : ∀ᶠ n in atTop, c n < v.toFun x :=
        hclim.eventually (Iio_mem_nhds ha)
      have hqfalse : ∀ n, ¬c n < -v.toFun x := by
        intro n hn
        linarith [hcpos n]
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [hc_event] with n hn
      rw [hFx' n]
      simp [hn, hqfalse n]
    · have hgzero : v.grad x i = 0 := congrFun (hzeroX ha.symm) i
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [] with n
      rw [hFx' n, hgzero]
      have hpfalse : ¬c n < v.toFun x := by linarith [hcpos n]
      have hqfalse : ¬c n < -v.toFun x := by linarith [hcpos n]
      simp [hpfalse, hqfalse]
    · have hc_event : ∀ᶠ n in atTop, c n < -v.toFun x :=
        hclim.eventually (Iio_mem_nhds (neg_pos.mpr ha))
      have hpfalse : ∀ n, ¬c n < v.toFun x := by
        intro n hn
        linarith [hcpos n]
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [hc_event] with n hn
      rw [hFx' n]
      simp [hn, hpfalse n]
  have hgrad : ∀ i, Tendsto
      (fun n => eLpNorm (fun x => v.grad x i - (F n).grad x i) 2
        (volumeMeasureOn (centeredCube z r hr : Set (SpatialCoordinates d))))
      atTop (nhds 0) := by
    intro i
    have h' : Tendsto
        (fun n => eLpNorm (fun x => (F n).grad x i - v.grad x i) 2
          (volumeMeasureOn (centeredCube z r hr : Set (SpatialCoordinates d))))
        atTop (nhds 0) :=
      Homogenization.tendsto_eLpNorm_two_of_tendsto_ae_of_dominated
        (f := fun n x => (F n).grad x i) (g := fun x => v.grad x i)
        (h := fun x => ‖v.grad x i‖) (fun n => hgrad_aesm n i)
        (v.gradMemL2 i) (v.gradMemL2 i).norm (fun n => hgrad_bound n i)
        (hgrad_tendsto i)
    exact h'.congr' (Filter.Eventually.of_forall fun n =>
      Homogenization.eLpNorm_sub_swap (fun x => (F n).grad x i) (fun x => v.grad x i))
  have hvH10 : Homogenization.MemH10
      (centeredCube z r hr : Set (SpatialCoordinates d)) v.toFun :=
    Homogenization.memH10_of_tendsto_H1 hDom v F hFmem hfun hgrad
  obtain ⟨w, hw⟩ := hvH10
  obtain ⟨k, hkval, hkgrad⟩ :=
    SubdiffusiveProcess.Lane4.exists_killedSobolevGraph_of_nativeH10 w
  have hwgrad : ∀ i, (fun x => w.toH1Function.grad x i) =ᵐ[volumeMeasureOn
      (centeredCube z r hr : Set (SpatialCoordinates d))] (fun x => v.grad x i) := by
    intro i
    have hloc : ∀ (a : Homogenization.H1Function
        (centeredCube z r hr : Set (SpatialCoordinates d))),
        LocallyIntegrableOn (fun x => a.grad x i)
          (centeredCube z r hr : Set (SpatialCoordinates d)) volume := by
      intro a
      exact locallyIntegrableOn_of_locallyIntegrable_restrict
        ((a.gradMemL2 i).locallyIntegrable (by norm_num))
    have hwweak := w.toH1Function.hasWeakGradient i
    rw [hw] at hwweak
    exact HasWeakPartialDerivOn.ae_eq hDom.isOpen (hloc w.toH1Function) (hloc v)
      hwweak (v.hasWeakGradient i)
  have huval : (fun x => u.val.1 x) =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))] (w : SpatialCoordinates d → ℝ) := by
    have hWw : W = w.toH1Function.toFun := by
      calc
        W = v.toFun := hv_toFun.symm
        _ = w.toH1Function.toFun := hw.symm
    exact hrepW.trans (Filter.Eventually.of_forall (fun x => hWw.symm ▸ rfl))
  have hugrad : ∀ i, (fun x => u.val.2 i x) =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))]
      (fun x => w.toH1Function.grad x i) := by
    intro i
    have huv : (fun x => u.val.2 i x) =ᵐ[volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d))]
        (fun x => v.grad x i) := by
      filter_upwards [] with x
      exact (congrFun (congrFun hv₀grad.symm x) i).trans
        (congrFun (congrFun hv_grad x) i).symm
    exact huv.trans (hwgrad i).symm
  have hdata : (u : SobolevData (centeredCube z r hr)) = (k : SobolevData (centeredCube z r hr)) := by
    apply Prod.ext
    · apply Lp.ext
      exact huval.trans hkval.symm
    · funext i
      apply Lp.ext
      exact (hugrad i).trans (hkgrad i).symm
  rw [hdata]
  exact k.property
end Paper

