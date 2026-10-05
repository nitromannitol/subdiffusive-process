module

public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.BoundaryPackaging
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.VariationalResponses.ResponseMarkov
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.VariationalResponses.MeshGluing
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Paper.prop_regularity_product_limit
public import SubdiffusiveProcess.Paper.prop_regularity_collar_core
public import SubdiffusiveProcess.Paper.prop_regularity_form_core_density
public import SubdiffusiveProcess.Paper.prop_regularity_mesh_core

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

lemma aux_prop_regularity_rpow_scale
    {R p q : ℝ} (hR : 0 < R) (_hp : 0 < p) (hq : 0 < q)
    (rho : ℕ → ℝ) (hrho : ∀ k : ℕ, rho k = R / (10 * (3 : ℝ) ^ k)) :
    ∀ k : ℕ, (rho k) ^ (p + q) ≤ (max R 1) ^ q * (rho k) ^ p := by
  intro k
  have hrho_pos : 0 < rho k := by
    rw [hrho]
    positivity
  have hrho_le : rho k ≤ max R 1 := by
    apply le_trans (show rho k ≤ R by
      rw [hrho]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 10 * (3 : ℝ) ^ k)).2
      have hp3 : (1 : ℝ) ≤ (3 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      have hden : (1 : ℝ) ≤ 10 * (3 : ℝ) ^ k := by nlinarith
      have hmul : R * 1 ≤ R * (10 * (3 : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left hden hR.le
      simpa [mul_assoc, mul_comm, mul_left_comm] using hmul)
    exact le_max_left _ _
  calc
    (rho k) ^ (p + q) = (rho k) ^ p * (rho k) ^ q := by
      rw [Real.rpow_add hrho_pos]
    _ ≤ (rho k) ^ p * (max R 1) ^ q := by
      gcongr
    _ = (max R 1) ^ q * (rho k) ^ p := by ring



theorem prop_regularity
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (a : ℕ → PositiveCoefficient (centeredCube z R hR))
    (E : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))))
    (G : DomainL2 (centeredCube z R hR) →L[ℝ] DomainL2 (centeredCube z R hR))
    (_hE : ∀ v : DomainL2 (centeredCube z R hR),
      E.toClosedForm.energy v = limitFormEnergy G v)
    (hGmem : ∀ f : DomainL2 (centeredCube z R hR), G f ∈ E.toClosedForm.domain)
    (hLower : ∀ (vN : ℕ → S.space) (v : DomainL2 (centeredCube z R hR)),
      (∀ f : DomainL2 (centeredCube z R hR),
        Tendsto (fun n => inner ℝ f (vN n).val.1) atTop (𝓝 (inner ℝ f v))) →
      E.toClosedForm.energy v ≤
        liminf (fun n => ((responseForm S (a n) (vN n) (vN n) : ℝ) : EReal)) atTop)
    (D : Submodule ℚ (DomainL2 (centeredCube z R hR)))
    [Countable D]
    (_hDdense : Dense (D : Set (DomainL2 (centeredCube z R hR))))
    (phi : D → H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hPhi : ∀ f : D, ContDiff ℝ (⊤ : ℕ∞) (phi f).toFun ∧
      HasCompactSupport (phi f).toFun ∧
      tsupport (phi f).toFun ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
      (sobolevDataOfH1 (phi f)).1 = f.val)
    (hGdense : ∀ v ∈ E.toClosedForm.domain, ∀ ε : ℝ, 0 < ε →
      ∃ f : D, E.toClosedForm.energyNormSq (v - G f.val) < ε)
    (alpha eta t : ℝ)
    (halpha_gt : 1 / 2 < alpha) (halpha_lt : alpha < 1)
    (heta_pos : 0 < eta)
    (ht : (d : ℝ) - 1 < t)
    (heta_lt : 1 + eta < 2 * alpha)
    (u : DomainL2 (centeredCube z R hR) → ℕ → S.space)
    (uc : DomainL2 (centeredCube z R hR) → ℕ → SpatialCoordinates d → ℝ)
    (_hU : ∀ (f : DomainL2 (centeredCube z R hR)) (n : ℕ),
      u f n = responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL))
    (hUrep : ∀ (f : DomainL2 (centeredCube z R hR)) (n : ℕ),
      (u f n).val.1
        =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] uc f n)
    (hUconv : ∀ f : DomainL2 (centeredCube z R hR),
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
          (fun x => uc f.val n x * chi k n x))
    (hCollarError : ∀ f : D, ∃ Kf : ℝ, 0 ≤ Kf ∧ ∀ k n : ℕ,
      responseForm S (a n) (u f.val n - w f.val k n) (u f.val n - w f.val k n) ≤
        Kf * ((rho k) ^ (t - (d : ℝ) + 1) + (rho k) ^ (2 * alpha - 1 - eta)))
    (hFiniteMesh : ∀ f : D, ∃ Cphi : ℝ, 0 ≤ Cphi ∧ ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ vN : ℕ → S.space, ∃ vcN : ℕ → SpatialCoordinates d → ℝ,
      ∃ Kset : Set (SpatialCoordinates d),
        IsCompact Kset ∧ Kset ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
        ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
          (vN n).val.1
            =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] vcN n ∧
          ContinuousOn (vcN n)
            (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
          (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) \ Kset, vcN n x = 0) ∧
          _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
            (closure (centeredCube z R hR : Set (SpatialCoordinates d))) (vcN n) ∧
          _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
            (closure (centeredCube z R hR : Set (SpatialCoordinates d))) (vcN n) ≤ M ∧
          responseForm S (a n) (vN n) (vN n) ≤ M ∧
          ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
            |vcN n x - (phi f).toFun x| ≤ Cphi * (R / (3 : ℝ) ^ k))
    (hsmooth : ∀ f : SpatialCoordinates d → ℝ, Continuous f → HasCompactSupport f →
      tsupport f ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) →
      ∀ ε : ℝ, 0 < ε →
      ∃ g : D, ∀ x : SpatialCoordinates d, |(phi g).toFun x - f x| ≤ ε) :
    (∃ C : Set (DomainL2 (centeredCube z R hR)),
      _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm
        (centeredCube z R hR : Set (SpatialCoordinates d)) C) ∧
    _root_.SubdiffusiveProcess.DirichletForm.IsRegular E.toClosedForm := by
  classical
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  let : Nontrivial (SpatialCoordinates d) := inferInstance
  let Q : Set (SpatialCoordinates d) := (centeredCube z R hR : Set (SpatialCoordinates d))
  have hQopen : IsOpen Q := by
    dsimp [Q]
    exact (centeredCube z R hR).isOpen
  have hQmeas : MeasurableSet Q := hQopen.measurableSet
  have hQcomp : IsCompact (closure Q) := by
    dsimp [Q]
    exact isCompact_closure_centeredCube z hR
  have hQne : Q ≠ (Set.univ : Set (SpatialCoordinates d)) := by
    intro hQ
    have hb : Bornology.IsBounded (Set.univ : Set (SpatialCoordinates d)) := by
      rw [← hQ]
      exact centeredCube_isBounded z hR
    exact (NormedSpace.unbounded_univ ℝ (SpatialCoordinates d)) hb
  have hQfin : (volume.restrict Q) Q ≠ (⊤ : ℝ≥0∞) := measure_ne_top _ _
  have hQfull : (volume.restrict Q) Qᶜ = 0 := by
    rw [MeasureTheory.Measure.restrict_apply hQmeas.compl]
    simp
  have halpha_pos : 0 < alpha := by linarith
  have hp : 0 < 2 * alpha - 1 - eta := by linarith
  have hq : 0 < 1 + eta := by linarith

  have hCollarCore : ∀ f : D, ∃ Kf : ℝ, 0 ≤ Kf ∧ ∀ k : ℕ,
      ∃ v : DomainL2 (centeredCube z R hR),
        E.toClosedForm.MemCoreOn Q v ∧
        E.toClosedForm.energyNormSq (G f.val - v) ≤
          Kf * ((rho k) ^ (t - (d : ℝ) + 1) +
            (rho k) ^ (2 * alpha - 1 - eta)) := by
    intro f
    obtain ⟨Kf, hKf, huf⟩ := hUholder f
    obtain ⟨K0, hK0, hcollar⟩ := hCollarError f
    let L : ℝ :=
      (Kf * (Real.sqrt (d : ℝ) * 3) ^ alpha *
        Real.sqrt ((volume.restrict Q) Q).toReal) ^ 2 *
        (max R 1) ^ (1 + eta)
    refine ⟨K0 + L, ?_, ?_⟩
    · positivity
    · intro k
      obtain ⟨σ, hσ, v, vc, hvc, hvccomp, hvsub, hvae, hvconv⟩ :=
        prop_regularity_product_limit d hd z R hR S hS a G D alpha
          halpha_gt halpha_lt u uc hUrep hUconv hUholder rho hrho chi hChi w hW f k
      let x : ℕ → S.space := fun n => u f.val (σ n) - w f.val k (σ n)
      have huσ : Tendsto (fun n => (u f.val (σ n)).val.1) atTop (𝓝 (G f.val)) :=
        (hUconv f.val).comp hσ.tendsto_atTop
      have hw : Tendsto (fun n => (w f.val k (σ n)).val.1) atTop (𝓝 v) := by
        apply tendsto_iff_norm_sub_tendsto_zero.mpr
        simpa only [sub_eq_add_neg] using hvconv
      have hx : Tendsto (fun n => (x n).val.1) atTop (𝓝 (G f.val - v)) := by
        change Tendsto
          (fun n => (u f.val (σ n)).val.1 - (w f.val k (σ n)).val.1) atTop
            (𝓝 (G f.val - v))
        exact huσ.sub hw
      have hσid : ∀ n : ℕ, n ≤ σ n := by
        intro n
        induction n with
        | zero => exact Nat.zero_le _
        | succ n ih =>
            exact (Nat.succ_le_succ ih).trans
              (Nat.succ_le_of_lt (hσ (Nat.lt_succ_self n)))
      let hm : ∀ n : ℕ, ∃ m : ℕ, n ≤ σ m := fun n => ⟨n, hσid n⟩
      let τ : ℕ → ℕ := fun n => Nat.find (hm n)
      have hτspec : ∀ n : ℕ, n ≤ σ (τ n) := by
        intro n
        exact Nat.find_spec (hm n)
      have hτσ : ∀ n : ℕ, τ (σ n) = n := by
        intro n
        apply Nat.le_antisymm
        · exact Nat.find_min' (hm (σ n)) (le_refl _)
        · by_contra hnot
          have hlt : τ (σ n) < n := Nat.lt_of_not_ge hnot
          exact (not_lt_of_ge (hτspec (σ n))) (hσ hlt)
      have hτtop : Tendsto τ atTop atTop := by
        refine tendsto_atTop.2 fun N => ?_
        filter_upwards [eventually_ge_atTop (σ N)] with n hn
        by_contra hnot
        have hlt : τ n < N := Nat.lt_of_not_ge hnot
        exact (not_lt_of_ge (hτspec n)) (lt_of_lt_of_le (hσ hlt) hn)
      let y : ℕ → S.space := fun n => x (τ n)
      have hy : Tendsto (fun n => (y n).val.1) atTop (𝓝 (G f.val - v)) := by
        simpa only [y] using! hx.comp hτtop
      have hysub : ∀ n : ℕ, y (σ n) = x n := by
        intro n
        simp only [y, hτσ]
      have hweakY : ∀ g : DomainL2 (centeredCube z R hR),
          Tendsto (fun n => inner ℝ g (y n).val.1) atTop
            (𝓝 (inner ℝ g (G f.val - v))) := by
        intro g
        simpa only using
          (Filter.Tendsto.inner
            (tendsto_const_nhds : Tendsto (fun _ : ℕ => g) atTop (𝓝 g)) hy)
      have henergy := hLower y (G f.val - v) hweakY
      let Ck : ℝ := K0 * ((rho k) ^ (t - (d : ℝ) + 1) +
        (rho k) ^ (2 * alpha - 1 - eta))
      have hpoint : ∀ n : ℕ,
          (((responseForm S (a (σ n)) (x n) (x n) : ℝ) : EReal)) ≤ (Ck : EReal) := by
        intro n
        have hr := hcollar k (σ n)
        exact_mod_cast (show responseForm S (a (σ n)) (x n) (x n) ≤ Ck by
          simpa [x, Ck] using hr)
      have hfreq : ∃ᶠ n in atTop,
          (((responseForm S (a n) (y n) (y n) : ℝ) : EReal)) ≤ (Ck : EReal) := by
        rw [frequently_atTop]
        intro N
        refine ⟨σ N, hσid N, ?_⟩
        simpa only [hysub N] using hpoint N
      have hliminf :
          liminf (fun n => (((responseForm S (a n) (y n) (y n) : ℝ) : EReal))) atTop
            ≤ (Ck : EReal) :=
        liminf_le_of_frequently_le hfreq
      have henergy_le : E.toClosedForm.energy (G f.val - v) ≤ (Ck : EReal) :=
        henergy.trans hliminf
      have hdiffmem : G f.val - v ∈ E.toClosedForm.domain := by
        apply E.toClosedForm.mem_domain_of_energy_lt_top
        exact henergy_le.trans_lt (EReal.coe_lt_top Ck)
      have hform : E.toClosedForm.form (G f.val - v) (G f.val - v) ≤ Ck := by
        rw [E.toClosedForm.energy_of_mem hdiffmem] at henergy_le
        exact_mod_cast henergy_le

      obtain ⟨Kchi, hKchi, hchif⟩ := hChi k
      have hucdata : ∀ n : ℕ, ∀ q ∈ closure Q, |uc f.val n q| ≤ Kf ∧
          ∀ r ∈ closure Q, |uc f.val n q - uc f.val n r| ≤ Kf *
            (Real.sqrt (∑ j : Fin d, (q j - r j) ^ 2)) ^ alpha := by
        intro n q hqQ
        have hn := huf n
        have hdta := aux_prop_regularity_product_limit_holder_data hQcomp hn.1 hn.2.1
          hn.2.2.1 halpha_pos
        exact ⟨hdta.1 q hqQ, fun r hr => hdta.2 q hqQ r hr⟩
      have hrho_pos : 0 < rho k := by
        rw [hrho]
        positivity
      let V : ℝ := Real.sqrt ((volume.restrict Q) Q).toReal
      let A : ℝ := Kf * (Real.sqrt (d : ℝ) * 3) ^ alpha * V
      have hA_nonneg : 0 ≤ A := by
        dsimp [A, V]
        positivity
      have hscale := aux_prop_regularity_rpow_scale hR hp hq rho hrho k
      have hnorm_bound : ∀ n : ℕ,
          ‖(x n).val.1‖ ≤
            Kf * (Real.sqrt (d : ℝ) * (3 * rho k)) ^ alpha * V := by
        intro n
        have hxeq : ((x n).val.1 : SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict Q]
            (fun q => uc f.val (σ n) q - uc f.val (σ n) q * chi k (σ n) q) := by
          filter_upwards [Lp.coeFn_sub (u f.val (σ n)).val.1
              (w f.val k (σ n)).val.1, hUrep f.val (σ n), hW f k (σ n)]
            with q hsub hu hw
          calc
            ((x n).val.1) q = (u f.val (σ n)).val.1 q -
                (w f.val k (σ n)).val.1 q := hsub
            _ = uc f.val (σ n) q - uc f.val (σ n) q * chi k (σ n) q := by
              rw [hu, hw]
        have hbound : ∀ᵐ q ∂volume.restrict Q,
            ‖((x n).val.1) q‖ ≤ Q.indicator
              (fun _ => Kf * (Real.sqrt (d : ℝ) * (3 * rho k)) ^ alpha) q := by
          filter_upwards [hxeq, ae_restrict_mem hQmeas] with q hqeq hqQ
          rw [hqeq, Set.indicator_of_mem hqQ]
          obtain ⟨hcont, hholder, hcnorm, h01, hzero, hone⟩ := hchif (σ n)
          have hqcl : q ∈ closure Q := subset_closure hqQ
          by_cases hχ : chi k (σ n) q = 1
          · simp [hχ]
            positivity
          · have hdistlt : Metric.infDist q Qᶜ < 3 * rho k := by
              apply lt_of_not_ge
              intro hge
              exact hχ (hone q hqcl hge)
            obtain ⟨r, hrfront, hrdist⟩ :=
              exists_mem_frontier_infDist_compl_eq_dist hqQ hQne
            have hdist : dist q r < 3 * rho k := by
              rw [← hrdist]
              exact hdistlt
            have heuclid := aux_prop_regularity_product_limit_euclidean_le hd q r
            have heuclid' : Real.sqrt (∑ j : Fin d, (q j - r j) ^ 2) <
                Real.sqrt (d : ℝ) * (3 * rho k) := by
              calc
                Real.sqrt (∑ j : Fin d, (q j - r j) ^ 2) ≤
                    Real.sqrt (d : ℝ) * dist q r := heuclid
                _ < Real.sqrt (d : ℝ) * (3 * rho k) := by
                  gcongr
            have hpow : (Real.sqrt (∑ j : Fin d, (q j - r j) ^ 2)) ^ alpha <
                (Real.sqrt (d : ℝ) * (3 * rho k)) ^ alpha :=
              Real.rpow_lt_rpow (by positivity) heuclid' halpha_pos
            have huq : |uc f.val (σ n) q| ≤ Kf *
                (Real.sqrt (d : ℝ) * (3 * rho k)) ^ alpha := by
              have hdiff := (hucdata (σ n) q hqcl).2 r
                (frontier_subset_closure hrfront)
              have hz := (huf (σ n)).2.2.2 r hrfront
              calc
                |uc f.val (σ n) q| =
                    |uc f.val (σ n) q - uc f.val (σ n) r| := by rw [hz, sub_zero]
                _ ≤ Kf * (Real.sqrt (∑ j : Fin d, (q j - r j) ^ 2)) ^ alpha := hdiff
                _ ≤ Kf * (Real.sqrt (d : ℝ) * (3 * rho k)) ^ alpha := by
                  gcongr
            have hχ0 : 0 ≤ chi k (σ n) q := (h01 q hqcl).1
            have hχ1 : chi k (σ n) q ≤ 1 := (h01 q hqcl).2
            calc
              ‖uc f.val (σ n) q - uc f.val (σ n) q * chi k (σ n) q‖ =
                  |uc f.val (σ n) q| * |1 - chi k (σ n) q| := by
                    rw [Real.norm_eq_abs]
                    rw [show uc f.val (σ n) q - uc f.val (σ n) q * chi k (σ n) q =
                      uc f.val (σ n) q * (1 - chi k (σ n) q) by ring]
                    rw [abs_mul]
              _ ≤ |uc f.val (σ n) q| * 1 := by
                gcongr
                rw [abs_of_nonneg (sub_nonneg.mpr hχ1)]
                linarith
              _ ≤ Kf * (Real.sqrt (d : ℝ) * (3 * rho k)) ^ alpha := by simpa using huq
        exact _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.norm_le_of_ae_indicator_bound hQmeas hQfin
          (by positivity) hbound
      have hnormsq : ‖G f.val - v‖ ^ 2 ≤
          (Kf * (Real.sqrt (d : ℝ) * (3 * rho k)) ^ alpha * V) ^ 2 := by
        apply le_of_tendsto' (hx.norm.pow 2)
        intro n
        exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (hnorm_bound n)
      have hscale_norm :
          Kf * (Real.sqrt (d : ℝ) * (3 * rho k)) ^ alpha * V ≤
            A * (rho k) ^ alpha := by
        dsimp [A]
        rw [show Real.sqrt (d : ℝ) * (3 * rho k) =
            (Real.sqrt (d : ℝ) * 3) * rho k by ring,
          Real.mul_rpow (by positivity) hrho_pos.le]
        simp [mul_assoc, mul_left_comm, mul_comm]
      have hnormsq' : ‖G f.val - v‖ ^ 2 ≤ (A * (rho k) ^ alpha) ^ 2 := by
        exact hnormsq.trans ((sq_le_sq₀ (by positivity) (by positivity)).2 hscale_norm)
      have hnormfinal : ‖G f.val - v‖ ^ 2 ≤
          L * (rho k) ^ (2 * alpha - 1 - eta) := by
        calc
          ‖G f.val - v‖ ^ 2 ≤ (A * (rho k) ^ alpha) ^ 2 := hnormsq'
          _ = A ^ 2 * (rho k) ^ (2 * alpha) := by
            rw [mul_pow, ← Real.rpow_natCast (rho k ^ alpha) 2,
              ← Real.rpow_mul hrho_pos.le]
            congr 2 ; ring
          _ = A ^ 2 * (rho k) ^ ((2 * alpha - 1 - eta) + (1 + eta)) := by
            congr 2 ; ring
          _ ≤ A ^ 2 * ((max R 1) ^ (1 + eta) *
              (rho k) ^ (2 * alpha - 1 - eta)) := by
            exact mul_le_mul_of_nonneg_left hscale (sq_nonneg A)
          _ = L * (rho k) ^ (2 * alpha - 1 - eta) := by
            simp [L, A, V, mul_assoc, mul_left_comm, mul_comm]
      have hvdom : v ∈ E.toClosedForm.domain := by
        have heq : v = G f.val - (G f.val - v) := by abel
        rw [heq]
        exact E.toClosedForm.domain.sub_mem (hGmem f.val) hdiffmem
      have hcore : E.toClosedForm.MemCoreOn Q v := by
        refine ⟨hvdom, ?_⟩
        exact ⟨vc, hvc, hvccomp, hvsub, hvae⟩
      refine ⟨v, hcore, ?_⟩
      have hnorm_form : E.toClosedForm.energyNormSq (G f.val - v) ≤
          Ck + L * (rho k) ^ (2 * alpha - 1 - eta) := by
        simp only [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq]
        exact add_le_add hform hnormfinal
      calc
        E.toClosedForm.energyNormSq (G f.val - v) ≤ Ck +
            L * (rho k) ^ (2 * alpha - 1 - eta) := hnorm_form
        _ ≤ (K0 + L) *
            ((rho k) ^ (t - (d : ℝ) + 1) +
              (rho k) ^ (2 * alpha - 1 - eta)) := by
          dsimp [Ck]
          let x : ℝ := (rho k) ^ (t - (d : ℝ) + 1)
          let y : ℝ := (rho k) ^ (2 * alpha - 1 - eta)
          have hx : 0 ≤ x := by
            dsimp [x]
            positivity
          have hy : 0 ≤ y := by
            dsimp [y]
            positivity
          have hL : 0 ≤ L := by
            dsimp [L]
            positivity
          change K0 * (x + y) + L * y ≤ (K0 + L) * (x + y)
          calc
            K0 * (x + y) + L * y = K0 * x + (K0 + L) * y := by ring
            _ ≤ (K0 + L) * x + (K0 + L) * y := by
              exact add_le_add
                (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hL) hx) le_rfl
            _ = (K0 + L) * (x + y) := by ring

  have hFormCore : ∀ f : D, ∀ ε : ℝ, 0 < ε →
      ∃ v : DomainL2 (centeredCube z R hR),
        E.toClosedForm.MemCoreOn Q v ∧
        E.toClosedForm.energyNormSq (G f.val - v) < ε := by
    intro f ε hε
    exact prop_regularity_form_core_density d hd z R hR E G D alpha eta t
      halpha_gt halpha_lt heta_pos ht heta_lt rho hrho hCollarCore f ε hε

  have hFiniteMesh' : ∀ f : D, ∃ Cphi : ℝ, 0 ≤ Cphi ∧ ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
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
          _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
            (closure (centeredCube z R hR : Set (SpatialCoordinates d))) (vcN n) ∧
          _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
            (closure (centeredCube z R hR : Set (SpatialCoordinates d))) (vcN n) ≤ M ∧
          responseForm S (a n) (vN n) (vN n) ≤ M ∧
          ∀ x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)),
            |vcN n x - (phi f).toFun x| ≤ Cphi * (R / (3 : ℝ) ^ k) := by
    intro f
    have hfmesh := hFiniteMesh f
    obtain ⟨Cphi, hCphi, k0, hk⟩ := hfmesh
    refine ⟨Cphi, hCphi, k0, ?_⟩
    intro k hk0
    have hmesh := hk k hk0
    obtain ⟨vN, vcN, Kset, hKc, hKsub, M, hM, hprops⟩ := hmesh
    have hKsubQ : Kset ⊆ Q := by
      simpa [Q] using hKsub
    have hcut : ∃ χ : SpatialCoordinates d → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧
        (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ EqOn χ 1 Kset ∧ tsupport χ ⊆ Q :=
      Homogenization.exists_contDiff_one_on_compact_tsupport_subset
        (E := SpatialCoordinates d) (K := Kset) (U := Q) hKc hKsubQ hQopen
    obtain ⟨χ, hχsmooth, hχ01, hχK, hχsupp⟩ := hcut
    let vc : ℕ → SpatialCoordinates d → ℝ := fun n =>
      (closure Q).piecewise (fun x => χ x * vcN n x) 0
    have hzero_cl : ∀ n : ℕ, ∀ x ∈ closure Q \ Kset, vcN n x = 0 := by
      intro n x hx
      obtain ⟨hae, hcont, hzero, hholder, hcAlpha, hresp, herr⟩ := hprops n
      have hsub : Q \ Kset ⊆ closure Q \ Kset := by
        intro y hy
        exact ⟨subset_closure hy.1, hy.2⟩
      have hts : closure Q \ Kset ⊆ closure (Q \ Kset) := by
        intro y hy
        rw [mem_closure_iff]
        intro o ho hoy
        have hopen : IsOpen (o ∩ Ksetᶜ) := ho.inter hKc.isClosed.isOpen_compl
        have hoy' : y ∈ o ∩ Ksetᶜ := ⟨hoy, hy.2⟩
        obtain ⟨w, hw⟩ := (mem_closure_iff.mp hy.1) (o ∩ Ksetᶜ) hopen hoy'
        exact ⟨w, hw.1.1, ⟨hw.2, hw.1.2⟩⟩
      have hz : Set.EqOn (vcN n) 0 (Q \ Kset) := by
        intro y hy
        exact hzero y hy
      have hcont' : ContinuousOn (vcN n) (closure Q \ Kset) := hcont.mono sdiff_subset
      exact (Set.EqOn.of_subset_closure (s := Q \ Kset) (t := closure Q \ Kset)
        hz hcont' continuousOn_const hsub hts) hx
    have hvc_eq : ∀ n : ℕ, ∀ x ∈ closure Q, vc n x = vcN n x := by
      intro n x hx
      obtain ⟨hae, hcont, hzero, hholder, hcAlpha, hresp, herr⟩ := hprops n
      by_cases hxK : x ∈ Kset
      · have hxQ : x ∈ Q := hKsub hxK
        change (closure Q).piecewise (fun y => χ y * vcN n y) 0 x = vcN n x
        rw [Set.piecewise_eq_of_mem _ _ _ hx]
        simp [hχK hxK]
      · have hz := hzero_cl n x ⟨hx, hxK⟩
        by_cases hxQ : x ∈ Q
        · change (closure Q).piecewise (fun y => χ y * vcN n y) 0 x = vcN n x
          rw [Set.piecewise_eq_of_mem _ _ _ hx]
          rw [hzero x ⟨hxQ, hxK⟩]
          simp
        · have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxQ (hχsupp h))
          change (closure Q).piecewise (fun y => χ y * vcN n y) 0 x = vcN n x
          rw [Set.piecewise_eq_of_mem _ _ _ hx, hχ0]
          simp [hz]
    have hvc_cont : ∀ n : ℕ, Continuous (vc n) := by
      intro n
      obtain ⟨hae, hcont, hzero, hholder, hcAlpha, hresp, herr⟩ := hprops n
      have hfront : ∀ x ∈ frontier (closure Q), χ x * vcN n x = 0 := by
        intro x hx
        have hxQ : x ∉ Q := by
          intro hxQ
          exact hx.2 (hQopen.subset_interior_closure hxQ)
        have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxQ (hχsupp h))
        simp [hχ0]
      apply continuous_piecewise hfront
      · rw [hQcomp.isClosed.closure_eq]
        exact hχsmooth.continuous.continuousOn.mul hcont
      · exact continuousOn_const
    have hvc_support : ∀ n : ℕ, Function.support (vc n) ⊆ Kset := by
      intro n x hx
      by_contra hxK
      by_cases hxQ : x ∈ closure Q
      · have hz := hzero_cl n x ⟨hxQ, hxK⟩
        have heq := hvc_eq n x hxQ
        exact hx (heq.trans hz)
      · have hv0 : vc n x = 0 := by
          change (closure Q).piecewise (fun y => χ y * vcN n y) 0 x = 0
          rw [Set.piecewise_eq_of_notMem _ _ _ hxQ]
          simp
        exact hx hv0
    have hvc_cs : ∀ n : ℕ, HasCompactSupport (vc n) := by
      intro n
      exact HasCompactSupport.of_support_subset_isCompact hKc (hvc_support n)
    have hvc_tsupport : ∀ n : ℕ, tsupport (vc n) ⊆ Q := by
      intro n
      exact (closure_minimal (hvc_support n) hKc.isClosed).trans hKsub
    refine ⟨vN, vc, Kset, hKc, hKsub, M, hM, ?_⟩
    intro n
    have hn := hprops n
    obtain ⟨hae, hcont, hzero, hholder, hcAlpha, hresp, herr⟩ := hn
    have hae' : (vN n).val.1 =ᵐ[volume.restrict Q] vc n := by
      filter_upwards [hae, MeasureTheory.ae_restrict_mem hQmeas] with x hx hQx
      exact hx.trans (hvc_eq n x (subset_closure hQx)).symm
    have hholder' : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (closure Q) (vc n) := by
      have hratio : _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet alpha (closure Q) (vc n) =
          _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet alpha (closure Q) (vcN n) := by
        ext b
        constructor <;> rintro ⟨x, hx, y, hy, hxy, rfl⟩
        · exact ⟨x, hx, y, hy, hxy, by rw [hvc_eq n x hx, hvc_eq n y hy]⟩
        · exact ⟨x, hx, y, hy, hxy, by rw [hvc_eq n x hx, hvc_eq n y hy]⟩
      rw [_root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn, hratio]
      exact hholder
    have hcAlpha' : _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha (closure Q) (vc n) ≤ M := by
      have habs : {b : ℝ | ∃ x ∈ closure Q, b = |vc n x|} =
          {b : ℝ | ∃ x ∈ closure Q, b = |vcN n x|} := by
        ext b
        constructor <;> rintro ⟨x, hx, rfl⟩
        · exact ⟨x, hx, by rw [hvc_eq n x hx]⟩
        · exact ⟨x, hx, by rw [hvc_eq n x hx]⟩
      have hratio : _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet alpha (closure Q) (vc n) =
          _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet alpha (closure Q) (vcN n) := by
        ext b
        constructor <;> rintro ⟨x, hx, y, hy, hxy, rfl⟩
        · exact ⟨x, hx, y, hy, hxy, by rw [hvc_eq n x hx, hvc_eq n y hy]⟩
        · exact ⟨x, hx, y, hy, hxy, by rw [hvc_eq n x hx, hvc_eq n y hy]⟩
      rw [_root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm, habs, _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm, hratio]
      exact hcAlpha
    refine ⟨hae', hvc_cont n, hvc_cs n, hvc_tsupport n, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [Q] using (hvc_cont n).continuousOn
    · intro x hx
      have hxcl : x ∈ closure Q := by simpa [Q] using (subset_closure hx.1)
      rw [hvc_eq n x hxcl]
      exact hzero x hx
    · exact hholder'
    · exact hcAlpha'
    · exact hresp
    · intro x hx
      have hxcl : x ∈ closure Q := by simpa [Q] using hx
      rw [hvc_eq n x hxcl]
      exact herr x hx

  let C : Set (DomainL2 (centeredCube z R hR)) :=
    {v | E.toClosedForm.MemCoreOn Q v}
  have hcore : _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm Q C := by
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      exact hv
    · intro v hv ε hε
      obtain ⟨f, hf⟩ := hGdense v hv (ε / 16) (by positivity)
      obtain ⟨w, hw, hwe⟩ := hFormCore f (ε / 16) (by positivity)
      refine ⟨w, hw, ?_⟩
      have htri := E.toClosedForm.sqrt_energyNormSq_sub_le hv
        (hGmem f.val) hw.1
      have hsqrt : Real.sqrt (E.toClosedForm.energyNormSq (v - w)) <
          Real.sqrt ε := by
        have h1 : Real.sqrt (E.toClosedForm.energyNormSq (v - G f.val)) <
            Real.sqrt (ε / 16) := by
          exact Real.sqrt_lt_sqrt (E.toClosedForm.energyNormSq_nonneg
            (E.toClosedForm.domain.sub_mem hv (hGmem f.val))) hf
        have h2 : Real.sqrt (E.toClosedForm.energyNormSq (G f.val - w)) <
            Real.sqrt (ε / 16) := by
          exact Real.sqrt_lt_sqrt (E.toClosedForm.energyNormSq_nonneg
            (E.toClosedForm.domain.sub_mem (hGmem f.val) hw.1)) hwe
        have hsq : Real.sqrt (ε / 16) + Real.sqrt (ε / 16) < Real.sqrt ε := by
          have hsεpos : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
          have hsδeq : Real.sqrt (ε / 16) = Real.sqrt ε / 4 := by
            rw [show ε / 16 = ε * (1 / 16 : ℝ) by ring,
              Real.sqrt_mul (by positivity)]
            rw [show (1 / 16 : ℝ) = (1 / 4 : ℝ) ^ 2 by norm_num,
              Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 4)]
            ring
          rw [hsδeq]
          nlinarith only [hsεpos]
        exact htri.trans_lt ((add_lt_add h1 h2).trans hsq)
      have hsq := (sq_lt_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).2 hsqrt
      have hnon : 0 ≤ E.toClosedForm.energyNormSq (v - w) :=
        E.toClosedForm.energyNormSq_nonneg (E.toClosedForm.domain.sub_mem hv hw.1)
      simpa only [Real.sq_sqrt hnon, Real.sq_sqrt hε.le] using hsq
    · intro f hf hcs hsupp ε hε
      obtain ⟨g, hg⟩ := hsmooth f hf hcs hsupp (ε / 2) (by positivity)
      obtain ⟨Cphi, hCphi, k0, hk⟩ :=
        prop_regularity_mesh_core d hd z R hR S hS a E hLower D
          phi
          (fun q => ⟨(hPhi q).1, (hPhi q).2.1, (hPhi q).2.2.1⟩)
          alpha halpha_gt halpha_lt hFiniteMesh' g
      have hpow : Tendsto (fun k : ℕ => (3 : ℝ) ^ k) atTop atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
      have hratio : Tendsto (fun k : ℕ => R / (3 : ℝ) ^ k) atTop (𝓝 0) :=
        hpow.const_div_atTop R
      have herr : Tendsto (fun k : ℕ => Cphi * (R / (3 : ℝ) ^ k)) atTop (𝓝 0) := by
        simpa only [mul_zero] using hratio.const_mul Cphi
      have hev : ∀ᶠ k : ℕ in atTop, Cphi * (R / (3 : ℝ) ^ k) < ε / 2 :=
        herr.eventually (Iio_mem_nhds (by linarith))
      obtain ⟨k, hk0, hkerr⟩ :=
        ((eventually_ge_atTop k0).and hev).exists
      obtain ⟨v, vc, hvcore, hvccont, hvcs, hvtsupp, hvae, hvbound⟩ := hk k hk0
      refine ⟨v, hvcore, vc, hvccont, hvcs, hvtsupp, hvae, ?_⟩
      intro x
      by_cases hx : x ∈ closure Q
      · have h1 := hvbound x hx
        have h2 := hg x
        have h1' : |vc x - (phi g).toFun x| < ε / 2 :=
          lt_of_le_of_lt h1 hkerr
        calc
          |vc x - f x| ≤ |vc x - (phi g).toFun x| +
              |(phi g).toFun x - f x| := abs_sub_le _ _ _
          _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le h1' h2
          _ = ε := by ring
      · have hvc0 : vc x = 0 := image_eq_zero_of_notMem_tsupport
          (fun h => hx (subset_closure (hvtsupp h)))
        have hf0 : f x = 0 := image_eq_zero_of_notMem_tsupport
          (fun h => hx (subset_closure (hsupp h)))
        simpa [hvc0, hf0] using hε
  constructor
  · exact ⟨C, by simpa [Q] using hcore⟩
  · refine ⟨Q, hQopen, hQfull, C, ?_⟩
    simpa [Q] using hcore

end SubdiffusiveProcess.Paper
