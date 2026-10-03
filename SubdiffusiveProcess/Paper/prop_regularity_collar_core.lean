module

public import SubdiffusiveProcess.Paper.prop_regularity_product_limit
public import SubdiffusiveProcess.Paper.conv_represented_estimates
public import SubdiffusiveProcess.Paper.lem_coercivity
public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Lane4.Carriers

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem prop_regularity_collar_core
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (S : ResponseSpace (centeredCube z R hR))
    (hS : S.space = killedSobolevGraph (centeredCube z R hR))
    (a : ℕ → PositiveCoefficient (centeredCube z R hR))
    (hUniformL2 : ∃ Kcoer : ℝ, 0 ≤ Kcoer ∧
      ∀ n : ℕ, ∀ v : S.space,
        ‖v.val.1‖ ^ 2 ≤ Kcoer * responseForm S (a n) v v)
    (E : _root_.DirichletForm
      (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))))
    (G : DomainL2 (centeredCube z R hR) →L[ℝ] DomainL2 (centeredCube z R hR))
    (hGmem : ∀ f : DomainL2 (centeredCube z R hR), G f ∈ E.toClosedForm.domain)
    (hLower : ∀ (vN : ℕ → S.space) (v : DomainL2 (centeredCube z R hR)),
      (∀ f : DomainL2 (centeredCube z R hR),
        Tendsto (fun n => inner ℝ f (vN n).val.1) atTop (𝓝 (inner ℝ f v))) →
      E.toClosedForm.energy v ≤
        liminf (fun n => ((responseForm S (a n) (vN n) (vN n) : ℝ) : EReal)) atTop)
    (D : Submodule ℚ (DomainL2 (centeredCube z R hR)))
    [Countable D]
    (alpha eta t : ℝ)
    (halpha_gt : 1 / 2 < alpha) (halpha_lt : alpha < 1)
    (heta_pos : 0 < eta)
    (ht : (d : ℝ) - 1 < t)
    (heta_lt : 1 + eta < 2 * alpha)
    (u : DomainL2 (centeredCube z R hR) → ℕ → S.space)
    (hUconv : ∀ f : DomainL2 (centeredCube z R hR),
      Tendsto (fun n => (u f n).val.1) atTop (𝓝 (G f)))
    (rho : ℕ → ℝ) (hrho : ∀ k : ℕ, rho k = R / (10 * (3 : ℝ) ^ k))
    (w : DomainL2 (centeredCube z R hR) → ℕ → ℕ → S.space)
    (hCollarError : ∀ f : D, ∃ Kf : ℝ, 0 ≤ Kf ∧ ∀ k n : ℕ,
      responseForm S (a n) (u f.val n - w f.val k n) (u f.val n - w f.val k n) ≤
        Kf * ((rho k) ^ (t - (d : ℝ) + 1) + (rho k) ^ (2 * alpha - 1 - eta)))
    (hProductLimit : ∀ f : D, ∀ k : ℕ,
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∃ v : DomainL2 (centeredCube z R hR),
        ∃ vc : SpatialCoordinates d → ℝ,
          Continuous vc ∧ HasCompactSupport vc ∧
          tsupport vc ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] vc ∧
          Tendsto
            (fun n => ‖(w f.val k (σ n)).val.1 - v‖) atTop (𝓝 0)) :
    ∀ f : D, ∃ Kf : ℝ, 0 ≤ Kf ∧ ∀ k : ℕ,
      ∃ v : DomainL2 (centeredCube z R hR),
        E.toClosedForm.MemCoreOn
          (centeredCube z R hR : Set (SpatialCoordinates d)) v ∧
        E.toClosedForm.energyNormSq (G f.val - v) ≤
          Kf * ((rho k) ^ (t - (d : ℝ) + 1) +
            (rho k) ^ (2 * alpha - 1 - eta)) := by
  obtain ⟨Kcoer, hKcoer, hcoer⟩ := hUniformL2
  intro f
  obtain ⟨K0, hK0, hcollar⟩ := hCollarError f
  refine ⟨(1 + Kcoer) * K0, by positivity, ?_⟩
  intro k
  obtain ⟨σ, hσ, v, vc, hvc, hvccomp, hvsub, hvae, hvconv⟩ :=
    hProductLimit f k
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
        ≤ (Ck : EReal) := by
    exact liminf_le_of_frequently_le hfreq
  have henergy_le : E.toClosedForm.energy (G f.val - v) ≤ (Ck : EReal) :=
    henergy.trans hliminf
  have hdiffmem : G f.val - v ∈ E.toClosedForm.domain := by
    apply E.toClosedForm.mem_domain_of_energy_lt_top
    exact henergy_le.trans_lt (EReal.coe_lt_top Ck)
  have hform : E.toClosedForm.form (G f.val - v) (G f.val - v) ≤ Ck := by
    rw [E.toClosedForm.energy_of_mem hdiffmem] at henergy_le
    exact_mod_cast henergy_le
  have hnorm : Tendsto (fun n => ‖(x n).val.1‖ ^ 2) atTop
      (𝓝 (‖G f.val - v‖ ^ 2)) := by
    simpa only using hx.norm.pow 2
  have hnorm_le : ∀ n : ℕ, ‖(x n).val.1‖ ^ 2 ≤ Kcoer * Ck := by
    intro n
    exact (hcoer (σ n) (x n)).trans
      (mul_le_mul_of_nonneg_left (by
        simpa only [x, Ck] using hcollar k (σ n)) hKcoer)
  have hnorm_bound : ‖G f.val - v‖ ^ 2 ≤ Kcoer * Ck :=
    le_of_tendsto' hnorm hnorm_le
  have hvdom : v ∈ E.toClosedForm.domain := by
    have heq : v = G f.val - (G f.val - v) := by abel
    rw [heq]
    exact E.toClosedForm.domain.sub_mem (hGmem f.val) hdiffmem
  have hcore : E.toClosedForm.MemCoreOn
      (centeredCube z R hR : Set (SpatialCoordinates d)) v := by
    refine ⟨hvdom, ?_⟩
    exact ⟨vc, hvc, hvccomp, hvsub, hvae⟩
  refine ⟨v, hcore, ?_⟩
  have hnorm_form :
      E.toClosedForm.energyNormSq (G f.val - v) ≤ Ck + Kcoer * Ck := by
    simp only [DirichletForm.ClosedForm.energyNormSq]
    exact add_le_add hform hnorm_bound
  calc
    E.toClosedForm.energyNormSq (G f.val - v) ≤ Ck + Kcoer * Ck := hnorm_form
    _ = (1 + Kcoer) * K0 *
        ((rho k) ^ (t - (d : ℝ) + 1) + (rho k) ^ (2 * alpha - 1 - eta)) := by
      simp only [Ck]
      ring

end Paper
