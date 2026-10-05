module

public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.EllipticRegularity.Carriers

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

lemma aux_prop_regularity_product_limit_holder_data
    {d : ℕ} {alpha K : ℝ} {T : Set (SpatialCoordinates d)}
    {g : SpatialCoordinates d → ℝ}
    (hT : IsCompact T) (hg : ContinuousOn g T)
    (hholder : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha T g)
    (hnorm : _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha T g ≤ K) (halpha : 0 < alpha) :
    (∀ x ∈ T, |g x| ≤ K) ∧
      (∀ x ∈ T, ∀ y ∈ T,
        |g x - g y| ≤ K *
          (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha) := by
  let V : Set ℝ := {v : ℝ | ∃ x ∈ T, v = |g x|}
  let H : Set ℝ := _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet alpha T g
  have hV : BddAbove V := by
    rcases hT.bddAbove_image hg.abs with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro v ⟨x, hx, rfl⟩
    exact hC ⟨x, hx, rfl⟩
  have hVnonneg : 0 ≤ sSup V := by
    by_cases hne : T.Nonempty
    · rcases hne with ⟨x, hx⟩
      exact le_trans (abs_nonneg (g x)) (le_csSup hV ⟨x, hx, rfl⟩)
    · have hne' : V = ∅ := by
        ext v
        constructor
        · rintro ⟨x, hx, hv⟩
          exact (hne ⟨x, hx⟩).elim
        · simp
      simp [hne']
  have hHnonneg : 0 ≤ sSup H := by
    by_cases hne : H.Nonempty
    · obtain ⟨v, hv⟩ := hne
      have hv0 : 0 ≤ v := by
        rcases hv with ⟨x, hx, y, hy, hxy, rfl⟩
        exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
      exact le_trans hv0 (le_csSup hholder hv)
    · have hne' : H = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      simp [hne']
  have hHle : sSup H ≤ K := by
    have hVle : sSup V ≤ K - sSup H := by
      have h := hnorm
      change sSup V + sSup H ≤ K at h
      linarith
    linarith
  have hVle : sSup V ≤ K := by
    have h := hnorm
    change sSup V + sSup H ≤ K at h
    linarith
  have hK : 0 ≤ K := hVnonneg.trans hVle
  have hval : ∀ x ∈ T, |g x| ≤ K := by
    intro x hx
    exact (le_csSup hV ⟨x, hx, rfl⟩).trans hVle
  refine ⟨hval, ?_⟩
  intro x hx y hy
  by_cases hxy : x = y
  · subst y
    simp [halpha.ne']
  · have hmem : |g x - g y| /
        (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha ∈ H := by
      exact ⟨x, hx, y, hy, hxy, rfl⟩
    have hquot : |g x - g y| /
        (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha ≤ K :=
      (le_csSup hholder hmem).trans hHle
    have hex : ∃ j : Fin d, x j ≠ y j := by
      by_contra h
      apply hxy
      funext j
      by_contra hj
      exact h ⟨j, hj⟩
    have hsum : 0 < ∑ j : Fin d, (x j - y j) ^ 2 := by
      apply Finset.sum_pos' (fun j _ => sq_nonneg _)
      rcases hex with ⟨j, hj⟩
      refine ⟨j, Finset.mem_univ _, ?_⟩
      exact sq_pos_of_ne_zero (sub_ne_zero.mpr hj)
    have hden : 0 <
        (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha :=
      Real.rpow_pos_of_pos (Real.sqrt_pos.2 hsum) _
    exact (div_le_iff₀ hden).mp hquot

lemma aux_prop_regularity_product_limit_euclidean_le
    {d : ℕ} (hd : 2 ≤ d) (x y : SpatialCoordinates d) :
    Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤
      Real.sqrt (d : ℝ) * dist x y := by
  have hd0 : 0 ≤ (d : ℝ) := by positivity
  have hsum : (∑ j : Fin d, (x j - y j) ^ 2) ≤
      (d : ℝ) * (dist x y) ^ 2 := by
    calc
      (∑ j : Fin d, (x j - y j) ^ 2) ≤
          ∑ j : Fin d, (dist x y) ^ 2 := by
            apply Finset.sum_le_sum
            intro j hj
            have hj' : |x j - y j| ≤ dist x y := by
              have h := norm_le_pi_norm (x - y) j
              simpa [Real.norm_eq_abs, dist_eq_norm] using h
            exact (sq_le_sq).2 (by
              simpa [abs_of_nonneg dist_nonneg] using hj')
      _ = (d : ℝ) * (dist x y) ^ 2 := by
        simp [Finset.sum_const, Fintype.card_fin]
  calc
    Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤
        Real.sqrt ((d : ℝ) * (dist x y) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (d : ℝ) * dist x y := by
      rw [Real.sqrt_mul hd0, Real.sqrt_sq_eq_abs, abs_of_nonneg dist_nonneg]



theorem prop_regularity_product_limit
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (_hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (_a : ℕ → PositiveCoefficient (centeredCube z R hR))
    (G : DomainL2 (centeredCube z R hR) →L[ℝ] DomainL2 (centeredCube z R hR))
    (D : Submodule ℚ (DomainL2 (centeredCube z R hR)))
    [Countable D]
    (alpha : ℝ) (halpha_gt : 1 / 2 < alpha) (halpha_lt : alpha < 1)
    (u : DomainL2 (centeredCube z R hR) → ℕ → S.space)
    (uc : DomainL2 (centeredCube z R hR) → ℕ → SpatialCoordinates d → ℝ)
    (_hUrep : ∀ (f : DomainL2 (centeredCube z R hR)) (n : ℕ),
      (u f n).val.1
        =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
          uc f n)
    (_hUconv : ∀ f : DomainL2 (centeredCube z R hR),
      Tendsto (fun n => (u f n).val.1) atTop (𝓝 (G f)))
    (hUholder : ∀ f : D, ∃ Kf : ℝ, 0 ≤ Kf ∧ ∀ n : ℕ,
      ContinuousOn (uc f.val n)
        (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
        (closure (centeredCube z R hR : Set (SpatialCoordinates d))) (uc f.val n) ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
        (closure (centeredCube z R hR : Set (SpatialCoordinates d))) (uc f.val n) ≤ Kf ∧
      ∀ x ∈ frontier (centeredCube z R hR : Set (SpatialCoordinates d)), uc f.val n x = 0)
    (rho : ℕ → ℝ) (hrho : ∀ k : ℕ, rho k = R / (10 * (3 : ℝ) ^ k))
    (chi : ℕ → ℕ → SpatialCoordinates d → ℝ)
    (hChi : ∀ k : ℕ, ∃ Kchi : ℝ, 0 ≤ Kchi ∧ ∀ n : ℕ,
      ContinuousOn (chi k n)
        (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
        (closure (centeredCube z R hR : Set (SpatialCoordinates d))) (chi k n) ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
        (closure (centeredCube z R hR : Set (SpatialCoordinates d))) (chi k n) ≤ Kchi ∧
      (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
        0 ≤ chi k n x ∧ chi k n x ≤ 1) ∧
      (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
        Metric.infDist x ((centeredCube z R hR : Set (SpatialCoordinates d))ᶜ) ≤ rho k →
          chi k n x = 0) ∧
      (∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
        3 * rho k ≤ Metric.infDist x ((centeredCube z R hR : Set (SpatialCoordinates d))ᶜ) →
          chi k n x = 1))
    (w : DomainL2 (centeredCube z R hR) → ℕ → ℕ → S.space)
    (hW : ∀ (f : D) (k n : ℕ),
      ((w f.val k n).val.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
          (fun x => uc f.val n x * chi k n x)) :
    ∀ f : D, ∀ k : ℕ,
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∃ v : DomainL2 (centeredCube z R hR),
        ∃ vc : SpatialCoordinates d → ℝ,
          Continuous vc ∧ HasCompactSupport vc ∧
          tsupport vc ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] vc ∧
          Tendsto
            (fun n => ‖(w f.val k (σ n)).val.1 - v‖) atTop (𝓝 0) := by
  classical
  intro f k
  let Q : Set (SpatialCoordinates d) := centeredCube z R hR
  let C : Set (SpatialCoordinates d) := closure Q
  have hQopen : IsOpen Q := by
    dsimp [Q, centeredCube]
    exact Metric.isOpen_ball
  have hzQ : z ∈ Q := by
    dsimp [Q, centeredCube]
    exact Metric.mem_ball_self (by positivity)
  have hCcomp : IsCompact C := by
    dsimp [C, Q]
    exact Bornology.IsBounded.isCompact_closure (centeredCube_isBounded z hR)
  have hCne : C.Nonempty := ⟨z, subset_closure hzQ⟩
  let : Nonempty C := ⟨⟨z, subset_closure hzQ⟩⟩
  let : CompactSpace C := isCompact_iff_compactSpace.mp hCcomp
  have halpha : 0 < alpha := lt_trans (by norm_num) halpha_gt
  obtain ⟨Kf, hKf, huf⟩ := hUholder f
  obtain ⟨Kchi, hKchi, hchif⟩ := hChi k
  have hucdata : ∀ n : ℕ, ∀ x ∈ C, |uc f.val n x| ≤ Kf ∧
      ∀ y ∈ C, |uc f.val n x - uc f.val n y| ≤ Kf *
        (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by
    intro n x hx
    have hn := huf n
    have hdta := aux_prop_regularity_product_limit_holder_data
      (T := C) hCcomp (by simpa [C, Q] using hn.1) hn.2.1 hn.2.2.1 halpha
    exact ⟨hdta.1 x hx, fun y hy => hdta.2 x hx y hy⟩
  have hchidata : ∀ n : ℕ, ∀ x ∈ C, |chi k n x| ≤ 1 ∧
      ∀ y ∈ C, |chi k n x - chi k n y| ≤ Kchi *
        (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by
    intro n x hx
    have hn := hchif n
    have hdta := aux_prop_regularity_product_limit_holder_data
      (T := C) hCcomp (by simpa [C, Q] using hn.1) hn.2.1 hn.2.2.1 halpha
    have hx01 := hn.2.2.2.1 x hx
    exact ⟨by simpa [abs_of_nonneg hx01.1] using hx01.2,
      fun y hy => hdta.2 x hx y hy⟩
  let F : ℕ → C → ℝ := fun n x => uc f.val n x * chi k n x
  have hFbound : ∀ x : C, ∃ M : ℝ, ∀ n, ‖F n x‖ ≤ M := by
    intro x
    refine ⟨Kf, ?_⟩
    intro n
    have hu := (hucdata n x x.property).1
    have hc := (hchidata n x x.property).1
    have hc0 : 0 ≤ |chi k n x| := abs_nonneg _
    calc
      ‖F n x‖ = |uc f.val n x| * |chi k n x| := by
        simp only [F, Real.norm_eq_abs, abs_mul]
      _ ≤ Kf * 1 := by
        exact (mul_le_mul hu hc hc0 hKf)
      _ = Kf := by ring
  let Kprod : ℝ := Kf + Kf * Kchi
  have hKprod : 0 ≤ Kprod := by
    dsimp [Kprod]
    positivity
  let Cprod : ℝ := Kprod * (Real.sqrt (d : ℝ)) ^ alpha
  have hCprod : 0 ≤ Cprod := by
    dsimp [Cprod]
    positivity
  have hFholder : ∀ n : ℕ, ∀ x y : C,
      |F n x - F n y| ≤ Cprod * (dist x y) ^ alpha := by
    intro n x y
    have hux := (hucdata n x x.property).1
    have huy := (hucdata n y y.property).1
    have hcx := (hchidata n x x.property).1
    have hcy := (hchidata n y y.property).1
    have hdu := (hucdata n x x.property).2 y y.property
    have hdc := (hchidata n x x.property).2 y y.property
    let E : ℝ := Real.sqrt (∑ j : Fin d,
      ((x : SpatialCoordinates d) j - (y : SpatialCoordinates d) j) ^ 2)
    have hE : 0 ≤ E := by dsimp [E]; positivity
    have hEα : 0 ≤ E ^ alpha := Real.rpow_nonneg hE _
    have hdu' : |uc f.val n x - uc f.val n y| ≤ Kf * E ^ alpha := by
      simpa [E] using hdu
    have hdc' : |chi k n x - chi k n y| ≤ Kchi * E ^ alpha := by
      simpa [E] using hdc
    have hcx' : |chi k n x| ≤ 1 := hcx
    have huy' : |uc f.val n y| ≤ Kf := huy
    have hprod : |F n x - F n y| ≤ Kprod * E ^ alpha := by
      calc
        |F n x - F n y| =
            |(uc f.val n x - uc f.val n y) * chi k n x +
              uc f.val n y * (chi k n x - chi k n y)| := by
                congr 1
                dsimp [F]
                ring
        _ ≤ |uc f.val n x - uc f.val n y| * |chi k n x| +
              |uc f.val n y| * |chi k n x - chi k n y| := by
                calc
                  _ ≤ |(uc f.val n x - uc f.val n y) * chi k n x| +
                      |uc f.val n y * (chi k n x - chi k n y)| :=
                    abs_add_le _ _
                  _ = _ := by rw [abs_mul, abs_mul]
        _ ≤ (Kf * E ^ alpha) * 1 + Kf * (Kchi * E ^ alpha) := by
          gcongr
        _ = Kprod * E ^ alpha := by
          dsimp [Kprod]
          ring
    have hxyE : E ≤ Real.sqrt (d : ℝ) * dist x y := by
      simpa [E] using! aux_prop_regularity_product_limit_euclidean_le hd
        (x : SpatialCoordinates d) (y : SpatialCoordinates d)
    have hpow : E ^ alpha ≤ (Real.sqrt (d : ℝ) * dist x y) ^ alpha :=
      Real.rpow_le_rpow hE hxyE halpha.le
    calc
      |F n x - F n y| ≤ Kprod * E ^ alpha := hprod
      _ ≤ Kprod * (Real.sqrt (d : ℝ) * dist x y) ^ alpha :=
        mul_le_mul_of_nonneg_left hpow hKprod
      _ = Cprod * (dist x y) ^ alpha := by
        dsimp [Cprod]
        rw [Real.mul_rpow (Real.sqrt_nonneg _) dist_nonneg]
        ring
  have hFeq : Equicontinuous F := by
    intro x₀
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    rcases eq_or_lt_of_le hCprod with hzero | hpos
    · refine ⟨1, one_pos, ?_⟩
      intro x hx n
      rw [Real.dist_eq]
      have hh := hFholder n x₀ x
      have hzero' : Cprod = 0 := hzero.symm
      rw [hzero', zero_mul] at hh
      exact lt_of_le_of_lt hh hε
    · refine ⟨(ε / Cprod) ^ (1 / alpha), by positivity, ?_⟩
      intro x hx n
      rw [Real.dist_eq]
      have hh := hFholder n x₀ x
      have hx' : dist x₀ x < (ε / Cprod) ^ (1 / alpha) := by
        simpa [dist_comm] using hx
      have hdx : 0 ≤ dist x₀ x := dist_nonneg
      have hlt : (dist x₀ x) ^ alpha < ε / Cprod := by
        have hmono := Real.rpow_lt_rpow hdx hx' halpha
        rwa [← Real.rpow_mul (by positivity), one_div,
          inv_mul_cancel₀ (ne_of_gt halpha), Real.rpow_one] at hmono
      calc
        dist (F n x₀) (F n x) = |F n x₀ - F n x| := Real.dist_eq _ _
        _ ≤ Cprod * dist x₀ x ^ alpha := hh
        _ < Cprod * (ε / Cprod) :=
          mul_lt_mul_of_pos_left hlt hpos
        _ = ε := by field_simp
  obtain ⟨g, σ, hσ, hgcont, hgpoint⟩ :=
    SubdiffusiveProcess.exists_pointwise_subseq_of_equicontinuous hFeq hFbound
  have hFuniformPoint : Tendsto (fun n => F (σ n)) atTop (𝓝 g) :=
    tendsto_pi_nhds.mpr hgpoint
  have hFuniform : Tendsto
      (UniformFun.ofFun ∘ (fun n => F (σ n))) atTop
      (𝓝 (UniformFun.ofFun g)) :=
    (Equicontinuous.tendsto_uniformFun_iff_pi (hFeq.comp σ) atTop g).2
      hFuniformPoint
  have hUniform : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop, ∀ x : C, |F (σ n) x - g x| ≤ δ := by
    intro δ hδ
    have hev :=
      ((UniformFun.hasBasis_nhds_of_basis C ℝ (UniformFun.ofFun g)
        uniformity_basis_edist_le).tendsto_right_iff).1 hFuniform
        (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ)
    filter_upwards [hev] with n hn x
    have hx := hn x
    have hδ0 : 0 ≤ δ := hδ.le
    simpa [UniformFun.gen, Function.comp_def, edist_dist,
      ENNReal.ofReal_le_ofReal_iff hδ0, Real.dist_eq, abs_sub_comm] using hx
  let gext : SpatialCoordinates d → ℝ := fun x =>
    if hx : x ∈ C then g ⟨x, hx⟩ else 0
  have hgextC : ContinuousOn gext C := by
    apply (continuousOn_iff_continuous_domRestrict).2
    have heq : C.domRestrict gext = g := by
      funext x
      simp [gext]
    rw [heq]
    exact hgcont
  have hgzero_boundary : ∀ x ∈ frontier Q, gext x = 0 := by
    intro x hx
    have hxC : x ∈ C := frontier_subset_closure hx
    have hzero : ∀ n : ℕ, F (σ n) ⟨x, hxC⟩ = 0 := by
      intro n
      dsimp [F]
      rw [huf (σ n) |>.2.2.2 x (by simpa [C, Q] using hx)]
      ring
    have hlimzero : Tendsto (fun n => F (σ n) ⟨x, hxC⟩) atTop (𝓝 0) := by
      simpa only [hzero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    have hgzero : g ⟨x, hxC⟩ = 0 :=
      tendsto_nhds_unique (hgpoint ⟨x, hxC⟩) hlimzero
    simp [gext, hxC, hgzero]
  let vc : SpatialCoordinates d → ℝ := Q.piecewise gext 0
  have hvccont : Continuous vc := by
    apply continuous_piecewise hgzero_boundary hgextC
    exact continuous_const.continuousOn
  have hrhok : 0 < rho k := by
    rw [hrho]
    positivity
  let U : Set (SpatialCoordinates d) :=
    {x | Metric.infDist x (Qᶜ) < rho k}
  have hUopen : IsOpen U := by
    dsimp [U]
    exact isOpen_lt (Metric.continuous_infDist_pt _) continuous_const
  have hvc_zero_U : ∀ x ∈ U, vc x = 0 := by
    intro x hxU
    by_cases hxQ : x ∈ Q
    · have hxC : x ∈ C := subset_closure hxQ
      have hgzero : gext x = 0 := by
        have : Metric.infDist x (Qᶜ) ≤ rho k := le_of_lt hxU
        dsimp [gext]
        rw [dite_eq_left hxC]
        have hlimzero : Tendsto (fun n => F (σ n) ⟨x, hxC⟩) atTop (𝓝 0) := by
          have hzero : ∀ n : ℕ, F (σ n) ⟨x, hxC⟩ = 0 := by
            intro n
            dsimp [F]
            rw [hchif (σ n) |>.2.2.2.2.1 x (by simpa [C, Q] using hxC) this]
            simp
          simpa only [hzero] using
            (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
        have hgzero : g ⟨x, hxC⟩ = 0 :=
          tendsto_nhds_unique (hgpoint ⟨x, hxC⟩) hlimzero
        exact hgzero
      simp [vc, hxQ, hgzero]
    · simp [vc, hxQ]
  have hvc_cs : HasCompactSupport vc := by
    apply HasCompactSupport.intro hCcomp
    intro x hxC
    have hxQ : x ∉ Q := fun hxQ => hxC (subset_closure hxQ)
    simp [vc, hxQ]
  have htsupport : tsupport vc ⊆ Q := by
    have hsupp : Function.support vc ⊆ Uᶜ := by
      intro x hx hxU
      exact hx (hvc_zero_U x hxU)
    have hcl : IsClosed Uᶜ := hUopen.isClosed_compl
    have hsub : tsupport vc ⊆ Uᶜ := by
      change closure (Function.support vc) ⊆ Uᶜ
      exact closure_minimal hsupp hcl
    intro x hx
    by_contra hxQ
    have hxU : x ∈ U := by
      dsimp [U]
      have hxQ' : x ∈ Qᶜ := hxQ
      rw [Metric.infDist_zero_of_mem hxQ']
      exact hrhok
    exact (hsub hx) hxU
  let μ : Measure (SpatialCoordinates d) := volume.restrict Q
  let : IsFiniteMeasure μ := by
    dsimp [μ, Q]
    exact centeredCube_isFiniteMeasure z R hR
  have hμne : μ ≠ 0 := by
    intro hzero
    have hzero' : volume Q = 0 := by
      exact Measure.restrict_eq_zero.mp (by simpa [μ] using hzero)
    have hpos : 0 < volume Q := hQopen.measure_pos volume ⟨z, hzQ⟩
    exact (ne_of_gt hpos) hzero'
  have hvc_mem : MemLp vc (2 : ℝ≥0∞) μ := by
    obtain ⟨M, hM⟩ := _root_.SubdiffusiveProcess.DirichletForm.exists_bound_of_hasCompactSupport hvc_cs hvccont
    apply MemLp.of_bound hvccont.aestronglyMeasurable M
    exact Eventually.of_forall (fun x => hM x)
  let v : DomainL2 (centeredCube z R hR) := MemLp.toLp vc (by simpa [μ, Q] using hvc_mem)
  have hvrep : (v : SpatialCoordinates d → ℝ) =ᵐ[μ] vc := by
    simpa [v] using hvc_mem.coeFn_toLp
  let A : ℝ := μ.real univ ^ (1 / (2 : ℝ≥0∞).toReal)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hnorm_bound : ∀ (n : ℕ) (δ : ℝ), 0 ≤ δ →
      (∀ᵐ x ∂μ, |((w f.val k (σ n)).val.1 x - (v : SpatialCoordinates d → ℝ) x)| ≤ δ) →
      ‖(w f.val k (σ n)).val.1 - v‖ ≤ δ * A := by
    intro n δ hδ hae
    rw [Lp.norm_def]
    have hae' : ∀ᵐ x ∂μ,
        ‖((w f.val k (σ n)).val.1 x - (v : SpatialCoordinates d → ℝ) x)‖ ≤
          ‖(fun _ : SpatialCoordinates d => δ) x‖ := by
      filter_upwards [hae] with x hx
      simpa [Real.norm_eq_abs, abs_of_nonneg hδ] using hx
    have hle := eLpNorm_mono_ae (p := (2 : ℝ≥0∞))
      ((Lp.aestronglyMeasurable (w f.val k (σ n)).val.1).sub (Lp.aestronglyMeasurable v)) hae'
    have hle_sub : eLpNorm (↑↑((w f.val k (σ n)).val.1 - v))
        (2 : ℝ≥0∞) μ ≤ eLpNorm (fun _ : SpatialCoordinates d => δ)
        (2 : ℝ≥0∞) μ := by
      calc
        eLpNorm (↑↑((w f.val k (σ n)).val.1 - v)) (2 : ℝ≥0∞) μ =
            eLpNorm (fun x => (w f.val k (σ n)).val.1 x - v x)
              (2 : ℝ≥0∞) μ :=
          eLpNorm_congr_ae (Lp.coeFn_sub ((w f.val k (σ n)).val.1) v)
        _ ≤ eLpNorm (fun _ : SpatialCoordinates d => δ) (2 : ℝ≥0∞) μ := hle
    have htop : eLpNorm (fun _ : SpatialCoordinates d => δ) (2 : ℝ≥0∞) μ ≠ ⊤ := by
      rw [eLpNorm_const (δ : ℝ) (by norm_num) hμne]
      finiteness
    have hconst : (eLpNorm (fun _ : SpatialCoordinates d => δ)
        (2 : ℝ≥0∞) μ).toReal = ‖(Lp.const (2 : ℝ≥0∞) μ) δ‖ := by
      rw [Lp.norm_def]
      exact congrArg ENNReal.toReal
        (eLpNorm_congr_ae (Lp.coeFn_const (2 : ℝ≥0∞) μ δ).symm)
    calc
      (eLpNorm (↑↑((w f.val k (σ n)).val.1 - v)) (2 : ℝ≥0∞)
        (volume.restrict (centeredCube z R hR))).toReal =
          (eLpNorm (↑↑((w f.val k (σ n)).val.1 - v))
            (2 : ℝ≥0∞) μ).toReal := by simp [μ, Q]
      _ ≤ (eLpNorm (fun _ : SpatialCoordinates d => δ)
          (2 : ℝ≥0∞) μ).toReal := ENNReal.toReal_mono htop hle_sub
      _ = ‖(Lp.const (2 : ℝ≥0∞) μ) δ‖ := hconst
      _ ≤ ‖δ‖ * A := by
        simpa [A] using Lp.norm_const_le (2 : ℝ≥0∞) μ δ
      _ = δ * A := by rw [Real.norm_eq_abs, abs_of_nonneg hδ]

  have hae_diff : ∀ (n : ℕ) (δ : ℝ), 0 < δ →
      (∀ x : C, |F (σ n) x - g x| ≤ δ) →
      ∀ᵐ x ∂μ, |((w f.val k (σ n)).val.1 x - (v : SpatialCoordinates d → ℝ) x)| ≤ δ := by
    intro n δ hδ hunif
    have hw : ((w f.val k (σ n)).val.1 : SpatialCoordinates d → ℝ) =ᵐ[μ]
        (fun x => uc f.val (σ n) x * chi k (σ n) x) := by
      simpa [μ, Q] using hW f k (σ n)
    filter_upwards [hw, hvrep, ae_restrict_mem hQopen.measurableSet] with x hxw hxv hxQ
    have hxC : x ∈ C := subset_closure hxQ
    have hvcx : vc x = g ⟨x, hxC⟩ := by
      simp [vc, gext, hxQ, hxC]
    have hfx := hunif ⟨x, hxC⟩
    rw [hxw, hxv, hvcx]
    simpa [F, Real.dist_eq, abs_sub_comm] using hfx
  refine ⟨σ, hσ, v, vc, hvccont, hvc_cs, ?_, ?_, ?_⟩
  · simpa [Q] using htsupport
  · simpa [μ, Q] using hvrep
  · rw [tendsto_order]
    constructor
    · intro b hb
      filter_upwards [] with n
      linarith [norm_nonneg ((w f.val k (σ n)).val.1 - v)]
    · intro ε hε
      have hden : 0 < A + 1 := by linarith
      have hδ : 0 < ε / (A + 1) := div_pos hε hden
      have hev := hUniform (ε / (A + 1)) hδ
      filter_upwards [hev] with n hn
      have hnorm := hnorm_bound n (ε / (A + 1)) hδ.le
        (hae_diff n (ε / (A + 1)) hδ hn)
      have hsmall : ε / (A + 1) * A < ε := by
        rw [div_mul_eq_mul_div]
        apply (div_lt_iff₀ hden).2
        nlinarith
      exact lt_of_le_of_lt hnorm hsmall

end SubdiffusiveProcess.Paper
