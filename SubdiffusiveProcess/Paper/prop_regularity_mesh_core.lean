import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Compactness.PointwiseExtraction
import SubdiffusiveProcess.Lane2.MeshGeometry
import Mathlib.Topology.UniformSpace.Ascoli

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

lemma aux_prop_regularity_mesh_core_sSup_nonneg
    {d : ℕ} {S : Set (SpatialCoordinates d)} {G : SpatialCoordinates d → ℝ} :
    0 ≤ sSup {v : ℝ | ∃ x ∈ S, v = |G x|} := by
  apply Real.sSup_nonneg
  intro v hv
  obtain ⟨x, hx, rfl⟩ := hv
  exact abs_nonneg _

lemma aux_prop_regularity_mesh_core_holder_nonneg
    {d : ℕ} {alpha : ℝ} {S : Set (SpatialCoordinates d)}
    {G : SpatialCoordinates d → ℝ} :
    0 ≤ Lane4.holderSeminorm alpha S G := by
  unfold Lane4.holderSeminorm
  apply Real.sSup_nonneg
  intro v hv
  obtain ⟨x, hx, y, hy, hxy, rfl⟩ := hv
  positivity

lemma aux_prop_regularity_mesh_core_sup_le_cAlphaNorm
    {d : ℕ} {alpha : ℝ} {S : Set (SpatialCoordinates d)}
    {G : SpatialCoordinates d → ℝ} :
    sSup {v : ℝ | ∃ x ∈ S, v = |G x|} ≤ Lane4.cAlphaNorm alpha S G := by
  unfold Lane4.cAlphaNorm
  have h := aux_prop_regularity_mesh_core_sSup_nonneg (S := S) (G := G)
  have h' := aux_prop_regularity_mesh_core_holder_nonneg (alpha := alpha) (S := S) (G := G)
  linarith

lemma aux_prop_regularity_mesh_core_holder_bound
    {d : ℕ} {alpha : ℝ} (halpha : 0 ≤ alpha)
    {S : Set (SpatialCoordinates d)} {G : SpatialCoordinates d → ℝ}
    (hG : Lane4.IsHolderOn alpha S G) :
    ∀ x ∈ S, ∀ y ∈ S,
      |G x - G y| ≤ Lane4.holderSeminorm alpha S G *
        (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by
  intro x hx y hy
  by_cases hxy : x = y
  · subst y
    have hnonneg := aux_prop_regularity_mesh_core_holder_nonneg
      (alpha := alpha) (S := S) (G := G)
    by_cases ha : alpha = 0
    · rw [ha] at hnonneg ⊢
      simpa using hnonneg
    · have ha' : 0 < alpha := lt_of_le_of_ne halpha (Ne.symm ha)
      simp [Real.zero_rpow ha'.ne']
  have hdist : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
    apply Real.sqrt_pos.2
    obtain ⟨j, hj⟩ : ∃ j : Fin d, x j ≠ y j := by
      by_contra h
      apply hxy
      funext j
      by_contra hj'
      exact h ⟨j, hj'⟩
    have hterm : 0 < (x j - y j) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hj)
    have hle : (x j - y j) ^ 2 ≤ ∑ i : Fin d, (x i - y i) ^ 2 := by
      simpa using (Finset.single_le_sum (s := Finset.univ)
        (f := fun i : Fin d => (x i - y i) ^ 2)
        (fun i hi => sq_nonneg _) (Finset.mem_univ j))
    exact lt_of_lt_of_le hterm hle
  have hratio :
      |G x - G y| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha ∈
        Lane4.holderRatioSet alpha S G := by
    exact ⟨x, hx, y, hy, hxy, rfl⟩
  have hle := le_csSup hG hratio
  have hpow : 0 < (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha :=
    Real.rpow_pos_of_pos hdist _
  exact (div_le_iff₀ hpow).mp hle

lemma aux_prop_regularity_mesh_core_euclidean_le_dist
    {d : ℕ} (hd : 2 ≤ d) (x y : SpatialCoordinates d) :
    Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt (d : ℝ) * dist x y := by
  have hsum :
      (∑ j : Fin d, (x j - y j) ^ 2) ≤ (d : ℝ) * (dist x y) ^ 2 := by
    calc
      (∑ j : Fin d, (x j - y j) ^ 2) ≤
          ∑ j : Fin d, (dist x y) ^ 2 := by
            apply Finset.sum_le_sum
            intro j hj
            have hj' : |x j - y j| ≤ dist x y := by
              have h := norm_le_pi_norm (x - y) j
              simpa [dist_eq_norm, Real.norm_eq_abs] using h
            have hsq := (sq_le_sq₀ (abs_nonneg (x j - y j))
              (dist_nonneg (x := x) (y := y))).2 hj'
            simpa [sq_abs] using hsq
      _ = (d : ℝ) * (dist x y) ^ 2 := by simp
  rw [← Real.sqrt_sq (dist_nonneg (x := x) (y := y)), ← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt hsum

lemma aux_prop_regularity_mesh_core_holder_dist_bound
    {d : ℕ} (hd : 2 ≤ d) {alpha : ℝ} (halpha : 0 ≤ alpha)
    {S : Set (SpatialCoordinates d)} {G : SpatialCoordinates d → ℝ}
    (hG : Lane4.IsHolderOn alpha S G) {M : ℝ} (hM : 0 ≤ M)
    (hGM : Lane4.cAlphaNorm alpha S G ≤ M) :
    ∀ x ∈ S, ∀ y ∈ S,
      |G x - G y| ≤ M * (Real.sqrt (d : ℝ)) ^ alpha * (dist x y) ^ alpha := by
  have hholder := aux_prop_regularity_mesh_core_holder_nonneg
    (alpha := alpha) (S := S) (G := G)
  have hseminorm : Lane4.holderSeminorm alpha S G ≤ M := by
    exact (le_add_of_nonneg_left
      (aux_prop_regularity_mesh_core_sSup_nonneg (S := S) (G := G))).trans hGM
  intro x hx y hy
  have hquot := aux_prop_regularity_mesh_core_holder_bound halpha hG x hx y hy
  have hdist := aux_prop_regularity_mesh_core_euclidean_le_dist hd x y
  have hpow := Real.rpow_le_rpow (Real.sqrt_nonneg _) hdist halpha
  have hmul := mul_le_mul_of_nonneg_left hpow hholder
  calc
    |G x - G y| ≤ Lane4.holderSeminorm alpha S G *
        (Real.sqrt (d : ℝ) * dist x y) ^ alpha := hquot.trans hmul
    _ = Lane4.holderSeminorm alpha S G *
        ((Real.sqrt (d : ℝ)) ^ alpha * (dist x y) ^ alpha) := by
          rw [Real.mul_rpow (Real.sqrt_nonneg _) (dist_nonneg)]
    _ ≤ M * ((Real.sqrt (d : ℝ)) ^ alpha * (dist x y) ^ alpha) := by
      gcongr
    _ = M * (Real.sqrt (d : ℝ)) ^ alpha * (dist x y) ^ alpha := by ring



theorem prop_regularity_mesh_core
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (a : ℕ → PositiveCoefficient (centeredCube z R hR))
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))))
    (hLower : ∀ (vN : ℕ → S.space) (v : DomainL2 (centeredCube z R hR)),
      (∀ f : DomainL2 (centeredCube z R hR),
        Tendsto (fun n => inner ℝ f (vN n).val.1) atTop (𝓝 (inner ℝ f v))) →
      E.toClosedForm.energy v ≤
        liminf (fun n => ((responseForm S (a n) (vN n) (vN n) : ℝ) : EReal)) atTop)
    (D : Submodule ℚ (DomainL2 (centeredCube z R hR)))
    [Countable D]
    (phi : D → H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hPhi : ∀ f : D,
      ContDiff ℝ (⊤ : ℕ∞) (phi f).toFun ∧
      HasCompactSupport (phi f).toFun ∧
      tsupport (phi f).toFun ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)))
    (alpha : ℝ) (halpha_gt : 1 / 2 < alpha) (halpha_lt : alpha < 1)
    (hFiniteMesh : ∀ f : D, ∃ Cphi : ℝ, 0 ≤ Cphi ∧ ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ vN : ℕ → S.space, ∃ vcN : ℕ → SpatialCoordinates d → ℝ,
      ∃ Kset : Set (SpatialCoordinates d),
        IsCompact Kset ∧ Kset ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
        ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
          (vN n).val.1
            =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] vcN n ∧
          Continuous (vcN n) ∧
          HasCompactSupport (vcN n) ∧
          tsupport (vcN n) ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
          ContinuousOn (vcN n)
            (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
          (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) \ Kset, vcN n x = 0) ∧
          Lane4.IsHolderOn alpha
            (closure (centeredCube z R hR : Set (SpatialCoordinates d))) (vcN n) ∧
          Lane4.cAlphaNorm alpha
            (closure (centeredCube z R hR : Set (SpatialCoordinates d))) (vcN n) ≤ M ∧
          responseForm S (a n) (vN n) (vN n) ≤ M ∧
          ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
            |vcN n x - (phi f).toFun x| ≤ Cphi * (R / (3 : ℝ) ^ k)) :
    ∀ f : D, ∃ Cphi : ℝ, 0 ≤ Cphi ∧ ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ v : DomainL2 (centeredCube z R hR),
      ∃ vc : SpatialCoordinates d → ℝ,
        E.toClosedForm.MemCoreOn
          (centeredCube z R hR : Set (SpatialCoordinates d)) v ∧
        Continuous vc ∧ HasCompactSupport vc ∧
        tsupport vc ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
        (v : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] vc ∧
        ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
          |vc x - (phi f).toFun x| ≤ Cphi * (R / (3 : ℝ) ^ k) := by
  classical
  intro f
  obtain ⟨Cphi, hCphi, k0, hk⟩ := hFiniteMesh f
  refine ⟨Cphi, hCphi, k0, ?_⟩
  intro k hkk
  obtain ⟨vN, vcN, Kset, hKc, hKsub, M, hM, hprops⟩ := hk k hkk
  let Q : Set (SpatialCoordinates d) := (centeredCube z R hR : Set (SpatialCoordinates d))
  have hQopen : IsOpen Q := by
    dsimp [Q]
    exact (centeredCube z R hR).isOpen
  have hQc : IsCompact (closure Q) := by
    dsimp [Q]
    exact lane2_isCompact_closure_centeredCube z hR
  have hQne : (closure Q).Nonempty := by
    refine ⟨z, subset_closure ?_⟩
    exact Metric.mem_ball_self (half_pos hR)
  letI : CompactSpace (closure Q) := isCompact_iff_compactSpace.mp hQc
  letI : Nonempty (closure Q) := ⟨⟨z, subset_closure (Metric.mem_ball_self (half_pos hR))⟩⟩
  have halpha_pos : 0 < alpha := by linarith
  let F : ℕ → (closure Q) → ℝ := fun n x => vcN n x
  have hFcont : ∀ n, Continuous (F n) := by
    intro n
    simpa [F, Function.comp_def] using
      (hprops n).2.1.comp continuous_subtype_val
  have hFdifference : ∀ n (x y : closure Q),
      dist (F n x) (F n y) ≤
        (M * (Real.sqrt (d : ℝ)) ^ alpha) * (dist x y) ^ alpha := by
    intro n x y
    obtain ⟨hae, hcont, hcs, htsupp, hcontOn, hzero, hholder, hcAlpha, hresp, herr⟩ :=
      hprops n
    have hb := aux_prop_regularity_mesh_core_holder_dist_bound hd
      halpha_pos.le hholder hM hcAlpha x.1 x.2 y.1 y.2
    simpa [F, Real.dist_eq] using hb
  have hFdifference_modulus :
      Tendsto (fun t : ℝ => (M * (Real.sqrt (d : ℝ)) ^ alpha) * t ^ alpha)
        (𝓝 0) (𝓝 0) := by
    have ht := (Real.continuousAt_rpow_const 0 alpha
      (Or.inr halpha_pos.le)).tendsto
    simpa [Real.zero_rpow halpha_pos.ne']
      using ht.const_mul (M * (Real.sqrt (d : ℝ)) ^ alpha)
  have hFeq : Equicontinuous F := by
    exact Metric.uniformEquicontinuous_of_continuity_modulus _
      hFdifference_modulus F (fun x y n => hFdifference n x y) |>.equicontinuous
  have hFbound : ∀ x : closure Q, ∃ B : ℝ, ∀ n, ‖F n x‖ ≤ B := by
    intro x
    refine ⟨M, ?_⟩
    intro n
    obtain ⟨hae, hcont, hcs, htsupp, hcontOn, hzero, hholder, hcAlpha, hresp, herr⟩ :=
      hprops n
    have hset : {v : ℝ | ∃ y ∈ closure Q, v = |vcN n y|} =
        (fun y => |vcN n y|) '' closure Q := by
      ext v
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
    have hBdd : BddAbove {v : ℝ | ∃ y ∈ closure Q, v = |vcN n y|} := by
      rw [hset]
      exact hQc.bddAbove_image (hcont.abs).continuousOn
    have hsup : |vcN n x| ≤ sSup {v : ℝ | ∃ y ∈ closure Q, v = |vcN n y|} := by
      have hBdd' : BddAbove ((fun y => |vcN n y|) '' closure Q) := by
        rw [← hset]
        exact hBdd
      rw [hset]
      exact le_csSup hBdd' ⟨x, x.2, rfl⟩
    have hsupM := aux_prop_regularity_mesh_core_sup_le_cAlphaNorm
      (alpha := alpha) (S := closure Q) (G := vcN n)
    have habs : |vcN n x| ≤ M := hsup.trans (hsupM.trans hcAlpha)
    simpa [F, Real.norm_eq_abs] using habs
  obtain ⟨g, ψ, hψ, hg, hlim⟩ :=
    SubdiffusiveProcess.exists_pointwise_subseq_of_equicontinuous hFeq hFbound
  let Fψ : ℕ → (closure Q) → ℝ := fun n => F (ψ n)
  have hFpoint : Tendsto Fψ atTop (𝓝 g) := tendsto_pi_nhds.mpr hlim
  have hFψeq : Equicontinuous Fψ := hFeq.comp ψ
  have hFuniformFun :
      Tendsto (fun n => UniformOnFun.ofFun {Set.univ} (Fψ n)) atTop
        (𝓝 (UniformOnFun.ofFun {Set.univ} g)) := by
    apply (EquicontinuousOn.tendsto_uniformOnFun_iff_pi
      (fun K hK => by
        have : K = (Set.univ : Set (closure Q)) := by simpa using hK
        rw [this]
        exact CompactSpace.isCompact_univ)
      (by simp) (fun K hK => by
        have : K = (Set.univ : Set (closure Q)) := by simpa using hK
        rw [this]
        exact hFψeq.equicontinuousOn Set.univ) atTop g).2
    exact hFpoint
  have hFuniform : TendstoUniformlyOn Fψ g atTop (Set.univ : Set (closure Q)) := by
    have h' := (UniformOnFun.tendsto_iff_tendstoUniformlyOn.mp hFuniformFun)
      Set.univ (by simp)
    simpa using h'
  let gExt : SpatialCoordinates d → ℝ := fun x =>
    if hx : x ∈ closure Q then g ⟨x, hx⟩ else 0
  have hgExt_on : ContinuousOn gExt (closure Q) := by
    rw [continuousOn_iff_continuous_restrict]
    convert hg using 1
    funext x
    simp [gExt]
  have hg_zero_off_K : ∀ x ∈ closure Q, x ∉ Kset → gExt x = 0 := by
    intro x hxQ hxK
    have hzero : ∀ n, vcN (ψ n) x = 0 := by
      intro n
      obtain ⟨hae, hcont, hcs, htsupp, hcontOn, hzero, hholder, hcAlpha, hresp, herr⟩ :=
        hprops (ψ n)
      by_cases hxopen : x ∈ Q
      · exact hzero x ⟨hxopen, hxK⟩
      · apply image_eq_zero_of_notMem_tsupport
        intro hxt
        exact hxopen (htsupp hxt)
    have hlimzero : Tendsto (fun n => Fψ n ⟨x, hxQ⟩) atTop (𝓝 0) := by
      simpa [Fψ, F, hzero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    have hgval : g ⟨x, hxQ⟩ = 0 :=
      tendsto_nhds_unique (hlim ⟨x, hxQ⟩) hlimzero
    simp [gExt, hxQ, hgval]
  have hgExt_frontier : ∀ x ∈ frontier (closure Q), gExt x = 0 := by
    intro x hx
    rw [hQc.isClosed.frontier_eq] at hx
    apply hg_zero_off_K x hx.1
    intro hxK
    have hxQ : x ∈ Q := hKsub hxK
    have hxi : x ∈ interior (closure Q) := interior_maximal subset_closure hQopen hxQ
    exact (hx.2 hxi).elim
  let vc : SpatialCoordinates d → ℝ := (closure Q).piecewise gExt 0
  have hgExt_on' : ContinuousOn gExt (closure (closure Q)) := by
    rw [hQc.isClosed.closure_eq]
    exact hgExt_on
  have hvc_cont : Continuous vc := by
    apply continuous_piecewise hgExt_frontier hgExt_on' continuousOn_const
  have hvc_support : Function.support vc ⊆ Kset := by
    intro x hx
    change vc x ≠ 0 at hx
    by_contra hxK
    by_cases hxQ : x ∈ closure Q
    · have hz : gExt x = 0 := hg_zero_off_K x hxQ hxK
      have hvz : vc x = 0 := by
        change (closure Q).piecewise gExt 0 x = 0
        rw [Set.piecewise_eq_of_mem _ _ _ hxQ]
        exact hz
      exact hx hvz
    · have hvz : vc x = 0 := by
        change (closure Q).piecewise gExt 0 x = 0
        rw [Set.piecewise_eq_of_notMem _ _ _ hxQ]
        simp
      exact hx hvz
  have hvc_cs : HasCompactSupport vc := by
    apply HasCompactSupport.of_support_subset_isCompact hKc
    exact hvc_support
  have hvc_tsupport : tsupport vc ⊆ Kset :=
    closure_minimal hvc_support hKc.isClosed
  have hvc_Q : tsupport vc ⊆ Q := hvc_tsupport.trans hKsub
  have hmem : MemLp vc (2 : ℝ≥0∞) (volume.restrict Q) := by
    exact hvc_cont.memLp_of_hasCompactSupport hvc_cs
  let v : DomainL2 (centeredCube z R hR) := by
    simpa [Q] using (hmem.toLp vc)
  have hv_aeQ : (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict Q] vc := by
    simpa [v] using hmem.coeFn_toLp
  have hv_ae : (v : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] vc := by
    simpa [Q] using hv_aeQ
  have hQmeas : MeasurableSet Q := hQopen.measurableSet
  have hQsub : Q ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) := by
    simpa [Q]
  have hQfin : (volume.restrict Q) Q ≠ (⊤ : ℝ≥0∞) := measure_ne_top _ _
  have hnorm_tendsto :
      Tendsto (fun n => ‖(vN (ψ n)).val.1 - v‖) atTop (𝓝 0) := by
    apply (Metric.tendsto_nhds).2
    intro ε hε
    let L : ℝ := Real.sqrt ((volume.restrict Q) Q).toReal
    have hL : 0 ≤ L := Real.sqrt_nonneg _
    let δ : ℝ := ε / (L + 1)
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    have hδbound : δ * L < ε := by
      have hden : 0 < L + 1 := by linarith
      have heq : δ * (L + 1) = ε := by
        dsimp [δ]
        field_simp
      calc
        δ * L < δ * (L + 1) := by
          gcongr
          linarith
        _ = ε := heq
    have hevent : ∀ᶠ n in atTop, ∀ x ∈ (Set.univ : Set (closure Q)),
        dist (g x) (Fψ n x) < δ :=
      (Metric.tendstoUniformlyOn_iff.mp hFuniform) δ hδ
    filter_upwards [hevent] with n hn
    have haediff :
        (vN (ψ n)).val.1 - v =ᵐ[volume.restrict Q]
          (fun x => vcN (ψ n) x - vc x) := by
      filter_upwards [Lp.coeFn_sub (vN (ψ n)).val.1 v,
        ae_restrict_of_ae_restrict_of_subset hQsub (hprops (ψ n)).1, hv_aeQ]
        with x hsub hN hv
      calc
        ((vN (ψ n)).val.1 - v) x =
            ((vN (ψ n)).val.1) x - v x := hsub
        _ = vcN (ψ n) x - vc x := by rw [hN, hv]
    have hbound : ∀ᵐ x ∂volume.restrict Q,
        ‖((vN (ψ n)).val.1 - v) x‖ ≤ Q.indicator (fun _ => δ) x := by
      filter_upwards [haediff, ae_restrict_mem hQmeas] with x hx hxQ
      rw [hx, Real.norm_eq_abs, Set.indicator_of_mem hxQ]
      have hxcl : x ∈ closure Q := subset_closure hxQ
      have hdist := hn ⟨x, hxcl⟩ (by simp)
      have hvcx : vc x = g ⟨x, hxcl⟩ := by
        change (closure Q).piecewise gExt 0 x = g ⟨x, hxcl⟩
        rw [Set.piecewise_eq_of_mem _ _ _ hxcl]
        simp [gExt, hxcl]
      have hdist' : |vcN (ψ n) x - vc x| < δ := by
        simpa [Fψ, F, hvcx,
          Real.dist_eq, abs_sub_comm] using hdist
      exact hdist'.le
    have hnorm := DirichletForm.ClosedForm.norm_le_of_ae_indicator_bound
      hQmeas hQfin hδ.le hbound
    have hlt := hnorm.trans_lt (by simpa [L] using hδbound)
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hlt
  have hdiff :
      Tendsto (fun n => (vN (ψ n)).val.1 - v) atTop (𝓝 0) := by
    apply (Metric.tendsto_nhds).2
    intro ε hε
    have hN' := (Metric.tendsto_nhds.1 hnorm_tendsto) ε hε
    obtain ⟨N, hN⟩ := (eventually_atTop.1 hN')
    exact eventually_atTop.2 ⟨N, fun n hn => by
      simpa [dist_eq_norm] using hN n hn⟩
  have hweak : ∀ w : DomainL2 (centeredCube z R hR),
      Tendsto (fun n => inner ℝ w (vN (ψ n)).val.1) atTop
        (𝓝 (inner ℝ w v)) := by
    intro w
    have hpair :
        Tendsto (fun n => (w, (vN (ψ n)).val.1 - v)) atTop (𝓝 (w, 0)) := by
      exact tendsto_const_nhds.prodMk_nhds hdiff
    have hinner0 :
        Tendsto (fun n => inner ℝ w ((vN (ψ n)).val.1 - v)) atTop (𝓝 0) := by
      have hc : Continuous
          (fun p : DomainL2 (centeredCube z R hR) × DomainL2 (centeredCube z R hR) =>
            inner ℝ p.1 p.2) := continuous_inner
      simpa [Function.comp_apply] using (hc.tendsto (w, 0)).comp hpair
    have hadd := hinner0.add_const (inner ℝ w v)
    simpa [inner_sub_right, sub_add_cancel] using hadd
  have hψ_ge : ∀ n : ℕ, n ≤ ψ n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
        have hlt : ψ n < ψ (Nat.succ n) := hψ (Nat.lt_succ_self n)
        exact (Nat.succ_le_succ ih).trans (Nat.succ_le_of_lt hlt)
  let wN : ℕ → S.space := fun n =>
    if n ∈ Set.range ψ then vN n else vN (ψ n)
  have hw_norm :
      Tendsto (fun n => ‖(wN n).val.1 - v‖) atTop (𝓝 0) := by
    apply (Metric.tendsto_nhds).2
    intro ε hε
    have hN' := (Metric.tendsto_nhds.1 hnorm_tendsto) ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp hN'
    apply eventually_atTop.mpr
    refine ⟨ψ N, ?_⟩
    intro n hn
    by_cases hnr : n ∈ Set.range ψ
    · obtain ⟨j, rfl⟩ := hnr
      have hjN : N ≤ j := by
        by_contra hnot
        have hjlt : j < N := Nat.lt_of_not_ge hnot
        exact (Nat.not_lt_of_ge (le_trans hn (by rfl))) (hψ hjlt)
      have hmem : ψ j ∈ Set.range ψ := ⟨j, rfl⟩
      simpa [wN, hmem] using hN j hjN
    · have hnN : N ≤ n := le_trans (hψ_ge N) hn
      dsimp [wN]
      rw [if_neg hnr]
      exact hN n hnN
  have hw_diff :
      Tendsto (fun n => (wN n).val.1 - v) atTop (𝓝 0) := by
    apply (Metric.tendsto_nhds).2
    intro ε hε
    have hN' := (Metric.tendsto_nhds.1 hw_norm) ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp hN'
    exact eventually_atTop.mpr ⟨N, fun n hn => by
      simpa [dist_eq_norm] using hN n hn⟩
  have hw_weak : ∀ w : DomainL2 (centeredCube z R hR),
      Tendsto (fun n => inner ℝ w (wN n).val.1) atTop
        (𝓝 (inner ℝ w v)) := by
    intro w
    have hpair :
        Tendsto (fun n => (w, (wN n).val.1 - v)) atTop (𝓝 (w, 0)) := by
      exact tendsto_const_nhds.prodMk_nhds hw_diff
    have hinner0 :
        Tendsto (fun n => inner ℝ w ((wN n).val.1 - v)) atTop (𝓝 0) := by
      have hc : Continuous
          (fun p : DomainL2 (centeredCube z R hR) × DomainL2 (centeredCube z R hR) =>
            inner ℝ p.1 p.2) := continuous_inner
      simpa [Function.comp_apply] using (hc.tendsto (w, 0)).comp hpair
    have hadd := hinner0.add_const (inner ℝ w v)
    simpa [inner_sub_right, sub_add_cancel] using hadd
  have hliminf :
      liminf (fun n => ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal)) atTop
        ≤ (M : EReal) := by
    have hbounded : IsBoundedUnder (· ≥ ·) atTop
        (fun n => ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal)) := by
      apply isBoundedUnder_of_eventually_ge (a := (0 : EReal))
      exact Eventually.of_forall (fun n =>
        EReal.coe_nonneg.mpr (responseForm_nonneg S (a n) (wN n)))
    apply liminf_le_of_frequently_le (hu := hbounded)
    apply frequently_atTop.mpr
    intro N
    refine ⟨ψ N, hψ_ge N, ?_⟩
    have hmem : ψ N ∈ Set.range ψ := ⟨N, rfl⟩
    have hresp := (hprops (ψ N)).2.2.2.2.2.2.2.2.1
    simpa only [wN, if_pos hmem] using (EReal.coe_le_coe_iff.mpr hresp)
  have henergy_le := hLower wN v hw_weak
  have henergy_lt : E.toClosedForm.energy v < (⊤ : EReal) := by
    calc
      E.toClosedForm.energy v ≤
          liminf (fun n => ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal)) atTop :=
        henergy_le
      _ ≤ (M : EReal) := hliminf
      _ < ⊤ := EReal.coe_lt_top M
  have hvdom : v ∈ E.toClosedForm.domain :=
    E.toClosedForm.mem_domain_of_energy_lt_top henergy_lt
  have hmemcore : E.toClosedForm.MemCoreOn
      (centeredCube z R hR : Set (SpatialCoordinates d)) v := by
    refine ⟨hvdom, ?_⟩
    exact ⟨vc, hvc_cont, hvc_cs, (by simpa [Q] using hvc_Q), hv_ae⟩
  have hvc_on : ∀ (x : SpatialCoordinates d) (hx : x ∈ closure Q),
      vc x = g ⟨x, hx⟩ := by
    intro x hx
    change (closure Q).piecewise gExt 0 x = g ⟨x, hx⟩
    rw [Set.piecewise_eq_of_mem _ _ _ hx]
    simp [gExt, hx]
  refine ⟨v, vc, hmemcore, hvc_cont, hvc_cs, ?_, hv_ae, ?_⟩
  · simpa [Q] using hvc_Q
  · intro x hx
    have hxQ : x ∈ closure Q := by simpa [Q] using hx
    have hscalar :
        Tendsto (fun n => |vcN (ψ n) x - (phi f).toFun x|) atTop
          (𝓝 |g ⟨x, hxQ⟩ - (phi f).toFun x|) := by
      have hscalar' :=
        ((continuous_abs.comp
          (continuous_id.sub (continuous_const : Continuous (fun _ : ℝ => (phi f).toFun x)))).tendsto
          (g ⟨x, hxQ⟩)).comp (hlim ⟨x, hxQ⟩)
      simpa [Fψ, F] using hscalar'
    have herr : ∀ n, |vcN (ψ n) x - (phi f).toFun x| ≤ Cphi * (R / (3 : ℝ) ^ k) := by
      intro n
      obtain ⟨hae, hcont, hcs, htsupp, hcontOn, hzero, hholder, hcAlpha, hresp, herr⟩ :=
        hprops (ψ n)
      exact herr x hx
    have hle : |g ⟨x, hxQ⟩ - (phi f).toFun x| ≤ Cphi * (R / (3 : ℝ) ^ k) :=
      le_of_tendsto hscalar (Eventually.of_forall herr)
    rw [← hvc_on x hxQ] at hle
    exact hle

end Paper

