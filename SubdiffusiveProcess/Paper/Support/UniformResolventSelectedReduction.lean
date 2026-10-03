module

public import SubdiffusiveProcess.Paper.prop_uniform_resolvent
public import SubdiffusiveProcess.Analysis.LocalHolderChain

@[expose] public section

/-!
Internal proof support for the unconditional killed-resolvent proposition.
These declarations are not paper statement principals.
Supports: mfd_prop_uniform_resolvent
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Topology Set SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace Paper

theorem aux_mfd_prop_uniform_resolvent_selected_reduction
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (z : SpatialCoordinates d) (s : ℝ) (hs : 0 < s) (β : ℝ) (hβ : 1 / 4 ≤ β)
    (RN : ℕ → Ω → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      SpatialCoordinates d → ℝ)
    (w : ℕ → Ω → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      DomainL2 (centeredCube z s hs))
    (ustar : Ω → ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
      DomainL2 (centeredCube z s hs))
    (Kcoer Khol : ℕ → Ω → ℝ)
    (hmeasK : ∀ N, Measurable (Kcoer N) ∧ Measurable (Khol N))
    (hRNmeas : ∀ (N : ℕ) (lam : ℝ) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
      (x : SpatialCoordinates d), Measurable (fun ω => RN N ω lam f x))
    (htight : ∀ rho : ℝ, 0 < rho → ∃ Mb : ℕ, ∀ N,
      P {ω | ¬ (Kcoer N ω ≤ Mb ∧ Khol N ω ≤ Mb)} ≤ ENNReal.ofReal rho)
    (hcampK : ∀ᵐ ω ∂P, ∀ Mb : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ N : ℕ, Kcoer N ω ≤ Mb → Khol N ω ≤ Mb →
      ∀ lam : ℝ, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ x : SpatialCoordinates d, ∀ r : ℝ, 0 < r → r ≤ 1 →
          (∫ y in Metric.ball x r,
            (Set.indicator (centeredCube z s hs : Set (SpatialCoordinates d))
                (fun y => w N ω lam f y) y -
              (volume.real (Metric.ball x r))⁻¹ *
                ∫ w' in Metric.ball x r,
                  Set.indicator (centeredCube z s hs : Set (SpatialCoordinates d))
                    (fun y => w N ω lam f y) w') ^ 2) ≤
            (K * ‖f‖) ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * β))
    (hfin : ∀ᵐ ω ∂P, ∀ (N : ℕ) (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        (RN N ω lam f =ᵐ[volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))]
          (w N ω lam f : SpatialCoordinates d → ℝ)) ∧
        ∀ x ∈ (centeredCube z s hs : Set (SpatialCoordinates d)), |RN N ω lam f x| ≤ ‖f‖ / lam)
    (hcamp : ∀ alpha : ℝ, alpha ∈ Set.Ioo (0 : ℝ) 1 →
        ∃ C : ℝ, 0 < C ∧
          ∀ (z : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ)
            (u : SpatialCoordinates d → ℝ) (A : ℝ), 0 ≤ A →
            LocallyIntegrable u volume → LocallyIntegrable (fun x => (u x) ^ 2) volume →
            (∀ x ∉ (centeredCube z rQ hrQ :
                Set (SpatialCoordinates d)), u x = 0) →
            (∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
              (∫ y in Metric.ball x r,
                  (u y - (volume.real (Metric.ball x r))⁻¹ *
                    ∫ w in Metric.ball x r, u w) ^ 2) ≤
                A ^ 2 * volume.real (Metric.ball x r) * r ^ (2 * alpha)) →
            ∃ v : SpatialCoordinates d → ℝ,
              v =ᵐ[volume] u ∧
              (∀ x y : SpatialCoordinates d, dist x y ≤ 1 →
                |v x - v y| ≤ C * A * dist x y ^ alpha) ∧
              ∀ x ∉ (centeredCube z rQ hrQ :
                  Set (SpatialCoordinates d)), v x = 0)
    (hpoint : ∀ᵐ ω ∂P, ∀ (N : ℕ) (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ v : SpatialCoordinates d → ℝ, Continuous v →
        (v =ᵐ[volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))] RN N ω lam f) →
        (∀ x ∉ (centeredCube z s hs : Set (SpatialCoordinates d)), v x = 0) →
        ∀ x ∈ closure (centeredCube z s hs : Set (SpatialCoordinates d)), RN N ω lam f x = v x)
    (hident : ∀ᵐ ω ∂P, ∀ lam : ℝ, 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ g : C(SpatialCoordinates d, ℝ), ∀ Mb : ℕ,
        (∃ σ : ℕ → ℕ, StrictMono σ ∧ (∀ k, Kcoer (σ k) ω ≤ Mb ∧ Khol (σ k) ω ≤ Mb) ∧
            ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
              ∀ x ∈ closure (centeredCube z s hs : Set (SpatialCoordinates d)),
                |RN (σ k) ω lam f x - g x| < eps) →
        ((g : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))]
          (ustar ω lam f : SpatialCoordinates d → ℝ)))
    (B : Ω → ℝ)
    (hstrong : ∀ᵐ ω ∂P, ∃ Mb : ℕ,
      (∃ᶠ N in atTop, Kcoer N ω ≤ Mb ∧ Khol N ω ≤ Mb) ∧
      ∀ N, Kcoer N ω ≤ Mb → Khol N ω ≤ Mb →
      ∀ lam : ℝ, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        (∀ x ∈ closure (centeredCube z s hs : Set (SpatialCoordinates d)),
          |RN N ω lam f x| ≤ B ω * ‖f‖) ∧
        (∀ x ∈ closure (centeredCube z s hs : Set (SpatialCoordinates d)),
          ∀ y ∈ closure (centeredCube z s hs : Set (SpatialCoordinates d)),
          |RN N ω lam f x - RN N ω lam f y| ≤
            B ω * ‖f‖ * dist x y ^ (1 / 4 : ℝ))) :
    ∃ R : ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
        Ω → C(SpatialCoordinates d, ℝ),
      (∀ᵐ omega ∂P, ∀ (N : ℕ) (lam : ℝ), 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          ContinuousOn (RN N omega lam f)
            (closure ((centeredCube z s hs) : Set (SpatialCoordinates d))) ∧
          ∀ x ∈ frontier ((centeredCube z s hs) : Set (SpatialCoordinates d)),
            RN N omega lam f x = 0) ∧
      (∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
          Measurable (R lam f)) ∧
      (∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
          ∃ N0 : ℕ, ∀ N, N0 ≤ N →
            P {omega : Ω |
                ∃ x ∈ closure ((centeredCube z s hs) : Set (SpatialCoordinates d)),
                  eps ≤ |RN N omega lam f x - R lam f omega x|} ≤
              ENNReal.ofReal rho) ∧
      (∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ᵐ omega ∂P,
          ((R lam f omega : SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict ((centeredCube z s hs) : Set (SpatialCoordinates d))]
            (ustar omega lam f : SpatialCoordinates d → ℝ)) ∧
          (∃ CH : ℝ, 0 < CH ∧
            (∀ x ∈ closure ((centeredCube z s hs) : Set (SpatialCoordinates d)),
              ∀ y ∈ closure ((centeredCube z s hs) : Set (SpatialCoordinates d)),
                |R lam f omega x - R lam f omega y| ≤
                  CH * ‖f‖ * dist x y ^ (1 / 4 : ℝ)) ∧
            ∀ x ∉ ((centeredCube z s hs) : Set (SpatialCoordinates d)),
              R lam f omega x = 0)) ∧
      (∀ lam : ℝ, 0 < lam →
        ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ∀ᵐ omega ∂P, ∀ x ∈ closure ((centeredCube z s hs) : Set (SpatialCoordinates d)),
          |R lam f omega x| ≤ ‖f‖ / lam) ∧
      (∀ᵐ ω ∂P, ∀ lam : ℝ, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        (∀ x ∈ closure (centeredCube z s hs : Set (SpatialCoordinates d)),
          |R lam f ω x| ≤ B ω * ‖f‖) ∧
        (∀ x ∈ closure (centeredCube z s hs : Set (SpatialCoordinates d)),
          ∀ y ∈ closure (centeredCube z s hs : Set (SpatialCoordinates d)),
          |R lam f ω x - R lam f ω y| ≤ B ω * ‖f‖ * dist x y ^ (1 / 4 : ℝ))) ∧
      (∀ᵐ omega ∂P, ∀ lam : ℝ, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ((R lam f omega : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube z s hs : Set (SpatialCoordinates d))]
          (ustar omega lam f : SpatialCoordinates d → ℝ)) ∧
        (∀ x ∉ (centeredCube z s hs : Set (SpatialCoordinates d)), R lam f omega x = 0) ∧
        ∀ x ∈ closure (centeredCube z s hs : Set (SpatialCoordinates d)),
          |R lam f omega x| ≤ ‖f‖ / lam) := by
  classical
  have hQne : (centeredCube z s hs : Set (SpatialCoordinates d)).Nonempty :=
    ⟨z, by change z ∈ Metric.ball z (s / 2); exact Metric.mem_ball_self (half_pos hs)⟩
  have hK : IsCompact (closure (centeredCube z s hs : Set (SpatialCoordinates d))) :=
    (centeredCube_isBounded z hs).isCompact_closure
  set Q : Set (SpatialCoordinates d) := (centeredCube z s hs : Set (SpatialCoordinates d))
    with hQdef
  have hQo : IsOpen Q := (centeredCube z s hs).isOpen
  have hQm : MeasurableSet Q := hQo.measurableSet
  have hQK : Q ⊆ closure Q := subset_closure
  have hfrK : frontier Q ⊆ closure Q := frontier_subset_closure
  have hfrQ : ∀ x ∈ frontier Q, x ∉ Q := fun x hx => by
    rw [hQo.frontier_eq] at hx; exact hx.2
  have hKQ : ∀ x ∈ closure Q, x ∉ Q → x ∈ frontier Q := fun x hx hxQ => by
    rw [hQo.frontier_eq]; exact ⟨hx, hxQ⟩
  obtain ⟨Cc, hCc0, hCc⟩ := hcamp (1 / 4) ⟨by norm_num, by norm_num⟩
  let good : ℕ → ℕ → Ω → Prop := fun Mb N ω => Kcoer N ω ≤ Mb ∧ Khol N ω ≤ Mb
  -- Step A: level-uniform Holder package of the ACTUAL occupation resolvents
  have hHold : ∀ᵐ ω ∂P, ∀ Mb : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ N, good Mb N ω →
      ∀ lam : ℝ, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ContinuousOn (RN N ω lam f) (closure Q) ∧ (∀ x ∈ frontier Q, RN N ω lam f x = 0) ∧
        (∀ x ∈ closure Q, |RN N ω lam f x| ≤ ‖f‖ / lam) ∧
        ∀ x ∈ closure Q, ∀ y ∈ closure Q, dist x y ≤ 1 →
          |RN N ω lam f x - RN N ω lam f y| ≤ C * ‖f‖ * dist x y ^ (1 / 4 : ℝ) := by
    filter_upwards [hcampK, hfin, hpoint] with ω hK' hf hp
    intro Mb
    obtain ⟨Kω, hK0, hKb⟩ := hK' Mb
    refine ⟨Cc * Kω, mul_nonneg hCc0.le hK0, fun N hN lam hlam f => ?_⟩
    obtain ⟨v, hvc, hvae, hvH, hv0⟩ := aux_prop_uniform_resolvent_camp_holder z s hs Cc hCc β hβ
      (Kω * ‖f‖) (mul_nonneg hK0 (norm_nonneg f)) (w N ω lam f) (hKb N hN.1 hN.2 lam hlam f)
    have hvRN : v =ᵐ[volume.restrict Q] RN N ω lam f := by
      have h1 : v =ᵐ[volume.restrict Q] (w N ω lam f : SpatialCoordinates d → ℝ) := by
        filter_upwards [ae_restrict_of_ae hvae, ae_restrict_mem hQm] with x hx1 hx2
        rw [hx1, Set.indicator_of_mem hx2]
      exact h1.trans (hf N lam hlam f).1.symm
    have hEq : ∀ x ∈ closure Q, RN N ω lam f x = v x := hp N lam hlam f v hvc hvRN hv0
    refine ⟨hvc.continuousOn.congr (fun x hx => hEq x hx), fun x hx => ?_, fun x hx => ?_,
      fun x hx y hy hxy => ?_⟩
    · rw [hEq x (hfrK hx)]; exact hv0 x (hfrQ x hx)
    · by_cases hxQ : x ∈ Q
      · exact (hf N lam hlam f).2 x hxQ
      · rw [hEq x hx, hv0 x hxQ, abs_zero]; exact div_nonneg (norm_nonneg f) hlam.le
    · rw [hEq x hx, hEq y hy]
      calc |v x - v y| ≤ Cc * (Kω * ‖f‖) * dist x y ^ (1 / 4 : ℝ) := hvH x y hxy
        _ = Cc * Kω * ‖f‖ * dist x y ^ (1 / 4 : ℝ) := by ring
  -- first frozen output: every cutoff, via the level `⌈max (Kcoer N) (Khol N)⌉`
  have hA : ∀ᵐ ω ∂P, ∀ (N : ℕ) (lam : ℝ), 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ContinuousOn (RN N ω lam f) (closure Q) ∧ ∀ x ∈ frontier Q, RN N ω lam f x = 0 := by
    filter_upwards [hHold] with ω hH N lam hlam f
    obtain ⟨C, -, hC⟩ := hH ⌈max (Kcoer N ω) (Khol N ω)⌉₊
    have hN : good ⌈max (Kcoer N ω) (Khol N ω)⌉₊ N ω :=
      ⟨(le_max_left _ _).trans (Nat.le_ceil _), (le_max_right _ _).trans (Nat.le_ceil _)⟩
    exact ⟨(hC N hN lam hlam f).1, (hC N hN lam hlam f).2.1⟩
  -- Step C: levels, the good sample set, the random represented subsequence
  have hgoodmeas : ∀ Mb N, MeasurableSet {ω | good Mb N ω} := fun Mb N =>
    (measurableSet_le (hmeasK N).1 measurable_const).inter
      (measurableSet_le (hmeasK N).2 measurable_const)
  have hfreq : ∀ᵐ ω ∂P, ∃ Mb : ℕ, ∃ᶠ N in atTop, good Mb N ω :=
    aux_prop_uniform_resolvent_tight_frequently P good htight
  let pω : Ω → Prop := fun ω =>
    (∀ Mb : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ N, good Mb N ω →
      ∀ lam : ℝ, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        ContinuousOn (RN N ω lam f) (closure Q) ∧ (∀ x ∈ frontier Q, RN N ω lam f x = 0) ∧
        (∀ x ∈ closure Q, |RN N ω lam f x| ≤ ‖f‖ / lam) ∧
        ∀ x ∈ closure Q, ∀ y ∈ closure Q, dist x y ≤ 1 →
          |RN N ω lam f x - RN N ω lam f y| ≤ C * ‖f‖ * dist x y ^ (1 / 4 : ℝ)) ∧
    (∃ Mb : ℕ, ∃ᶠ N in atTop, good Mb N ω) ∧
    (∀ lam : ℝ, 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∀ g : C(SpatialCoordinates d, ℝ), ∀ Mb : ℕ,
        (∃ σ : ℕ → ℕ, StrictMono σ ∧ (∀ k, good Mb (σ k) ω) ∧
            ∀ eps : ℝ, 0 < eps → ∃ k0 : ℕ, ∀ k, k0 ≤ k →
              ∀ x ∈ closure Q, |RN (σ k) ω lam f x - g x| < eps) →
        ((g : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict Q]
          (ustar ω lam f : SpatialCoordinates d → ℝ))) ∧
    (∃ Mb : ℕ, (∃ᶠ N in atTop, good Mb N ω) ∧
      ∀ N, good Mb N ω → ∀ lam : ℝ, 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
        (∀ x ∈ closure Q, |RN N ω lam f x| ≤ B ω * ‖f‖) ∧
        (∀ x ∈ closure Q, ∀ y ∈ closure Q,
          |RN N ω lam f x - RN N ω lam f y| ≤
            B ω * ‖f‖ * dist x y ^ (1 / 4 : ℝ)))
  have hpae : ∀ᵐ ω ∂P, pω ω := by
    filter_upwards [hHold, hfreq, hident, hstrong] with ω h1 h2 h3 h4
    obtain ⟨Mb, hf, hb⟩ := h4
    exact ⟨h1, h2, h3, Mb, hf, fun N hN => hb N hN.1 hN.2⟩
  set Good : Set Ω := (toMeasurable P {ω | ¬ pω ω})ᶜ with hGood
  have hGoodmeas : MeasurableSet Good := (measurableSet_toMeasurable P _).compl
  have hGoodzero : P Goodᶜ = 0 := by
    rw [hGood, compl_compl, measure_toMeasurable]
    exact ae_iff.mp hpae
  have hGood_ae : ∀ᵐ ω ∂P, ω ∈ Good := by
    rw [ae_iff]
    simpa only using! hGoodzero
  have hGood_p : ∀ ω ∈ Good, pω ω := fun ω hω => by
    by_contra hc
    exact hω (subset_toMeasurable P _ hc)
  have hFr : ∀ Mb, MeasurableSet {ω | ∃ᶠ N in atTop, good Mb N ω} := fun Mb =>
    aux_prop_uniform_resolvent_det_measurableSet_frequently (fun N ω => good Mb N ω)
      (fun N => hgoodmeas Mb N)
  have hq : ∀ ω, ∃ Mb : ℕ, (∃ᶠ N in atTop, good Mb N ω) ∨
      ¬ ∃ Mb' : ℕ, ∃ᶠ N in atTop, good Mb' N ω := by
    intro ω
    by_cases h : ∃ Mb' : ℕ, ∃ᶠ N in atTop, good Mb' N ω
    · obtain ⟨Mb', h'⟩ := h
      exact ⟨Mb', Or.inl h'⟩
    · exact ⟨0, Or.inr h⟩
  let lev : Ω → ℕ := fun ω => Nat.find (hq ω)
  have hlev : Measurable lev := by
    refine measurable_find hq (fun k => ?_)
    have heq : {x | (∃ᶠ N in atTop, good k N x) ∨ ¬ ∃ Mb' : ℕ, ∃ᶠ N in atTop, good Mb' N x} =
        {x | ∃ᶠ N in atTop, good k N x} ∪ (⋃ Mb', {x | ∃ᶠ N in atTop, good Mb' N x})ᶜ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff, Set.mem_iUnion]
    rw [heq]
    exact (hFr k).union (MeasurableSet.iUnion hFr).compl
  have hlev_spec : ∀ ω, (∃ Mb' : ℕ, ∃ᶠ N in atTop, good Mb' N ω) →
      ∃ᶠ N in atTop, good (lev ω) N ω := by
    intro ω h
    rcases Nat.find_spec (hq ω) with h1 | h1
    · exact h1
    · exact absurd h h1
  have hr : ∀ ω (k : ℕ), ∃ N : ℕ, (k ≤ N ∧ good (lev ω) N ω) ∨
      ¬ ∃ᶠ M in atTop, good (lev ω) M ω := by
    intro ω k
    by_cases h : ∃ᶠ M in atTop, good (lev ω) M ω
    · obtain ⟨N, hN, hg⟩ := Filter.frequently_atTop.1 h k
      exact ⟨N, Or.inl ⟨hN, hg⟩⟩
    · exact ⟨0, Or.inr h⟩
  let nxt : Ω → ℕ → ℕ := fun ω k => Nat.find (hr ω k)
  have hnxt : ∀ k, Measurable (fun ω => nxt ω k) := by
    intro k
    exact measurable_find (fun ω => hr ω k) (fun N =>
      aux_prop_uniform_resolvent_det_measurableSet_index
        (fun m ω => (k ≤ N ∧ good m N ω) ∨ ¬ ∃ᶠ M in atTop, good m M ω)
        (fun m => ((MeasurableSet.const (k ≤ N)).inter (hgoodmeas m N)).union (hFr m).compl)
        lev hlev)
  have hnxt_spec : ∀ ω, (∃ᶠ M in atTop, good (lev ω) M ω) → ∀ k,
      k ≤ nxt ω k ∧ good (lev ω) (nxt ω k) ω := by
    intro ω h k
    rcases Nat.find_spec (hr ω k) with h1 | h1
    · exact h1
    · exact absurd h h1
  -- Step D: one sample
  have hmain : ∀ ω ∈ Good, ∀ lam : ℝ, 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∃ g : SpatialCoordinates d → ℝ, ContinuousOn g (closure Q) ∧
        (∀ x ∈ frontier Q, g x = 0) ∧ (∀ x ∈ closure Q, |g x| ≤ ‖f‖ / lam) ∧
        (∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ closure Q, ∀ y ∈ closure Q,
          |g x - g y| ≤ C * dist x y ^ (1 / 4 : ℝ)) ∧
        (g =ᵐ[volume.restrict Q] (ustar ω lam f : SpatialCoordinates d → ℝ)) ∧
        (∀ Mb : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → good Mb N ω →
          ∀ x ∈ closure Q, |RN N ω lam f x - g x| < ε) ∧
        (∀ x ∈ closure Q, limsup (fun k => RN (nxt ω k) ω lam f x) atTop = g x) := by
    intro ω hω lam hlam f
    obtain ⟨hH, hF, hI, -⟩ := hGood_p ω hω
    have hlevF := hlev_spec ω hF
    obtain ⟨g, hgc, hgfr, hgS, hgH, hgae, hgconv⟩ := aux_prop_uniform_resolvent_core Q hQo hQne hK
      (fun N => RN N ω lam f) (fun Mb N => good Mb N ω) (‖f‖ / lam)
      (div_nonneg (norm_nonneg f) hlam.le)
      (fun Mb => by
        obtain ⟨C, hC0, hC⟩ := hH Mb
        exact ⟨C * ‖f‖, mul_nonneg hC0 (norm_nonneg f), fun N hN => hC N hN lam hlam f⟩)
      (lev ω) hlevF (ustar ω lam f) (fun Mb g hg => hI lam hlam f g Mb hg)
    refine ⟨g, hgc, hgfr, hgS, hgH, hgae, hgconv, fun x hx => ?_⟩
    apply Tendsto.limsup_eq
    rw [Metric.tendsto_atTop]
    intro e he
    obtain ⟨N0, hN0⟩ := hgconv (lev ω) e he
    refine ⟨N0, fun k hk => ?_⟩
    obtain ⟨hk1, hk2⟩ := hnxt_spec ω hlevF k
    rw [Real.dist_eq]
    exact hN0 (nxt ω k) (hk.trans hk1) hk2 x hx
  -- Step E: the measurable limit
  let Rfun : ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ → Ω →
      SpatialCoordinates d → ℝ := fun lam f ω x =>
    if ω ∈ Good ∧ 0 < lam then
      (if x ∈ closure Q then limsup (fun k => RN (nxt ω k) ω lam f x) atTop else 0) else 0
  have hRcont : ∀ lam f ω, Continuous (Rfun lam f ω) := by
    intro lam f ω
    by_cases hc : ω ∈ Good ∧ 0 < lam
    · obtain ⟨g, hgc, hgfr, -, -, -, -, hlim⟩ := hmain ω hc.1 lam hc.2 f
      have heq : Rfun lam f ω = fun x => if x ∈ closure Q then g x else 0 := by
        funext x
        simp only [Rfun, if_pos hc]
        by_cases hx : x ∈ closure Q
        · rw [if_pos hx, if_pos hx, hlim x hx]
        · rw [if_neg hx, if_neg hx]
      rw [heq]
      exact aux_prop_uniform_resolvent_subsequence_bridge_zero_extend_continuous (closure Q) g
        isClosed_closure hgc (fun x hx => hgfr x (frontier_closure_subset hx))
    · have heq : Rfun lam f ω = fun _ => 0 := by
        funext x
        simp only [Rfun, if_neg hc]
      rw [heq]
      exact continuous_const
  let R : ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ → Ω →
      C(SpatialCoordinates d, ℝ) := fun lam f ω => ⟨Rfun lam f ω, hRcont lam f ω⟩
  have hRg : ∀ ω ∈ Good, ∀ lam : ℝ, 0 < lam →
      ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ, ∀ x ∈ closure Q,
        R lam f ω x = limsup (fun k => RN (nxt ω k) ω lam f x) atTop := by
    intro ω hω lam hlam f x hx
    change Rfun lam f ω x = _
    simp only [Rfun, if_pos (And.intro hω hlam), if_pos hx]
  have hRout : ∀ ω ∉ Good, ∀ lam f x, R lam f ω x = 0 := by
    intro ω hω lam f x
    change Rfun lam f ω x = 0
    simp only [Rfun]
    rw [if_neg (fun h => hω h.1)]
  have hRmeas_eval : ∀ lam f (x : SpatialCoordinates d), Measurable (fun ω => R lam f ω x) := by
    intro lam f x
    change Measurable (fun ω => if ω ∈ Good ∧ 0 < lam then
      (if x ∈ closure Q then limsup (fun k => RN (nxt ω k) ω lam f x) atTop else 0) else 0)
    have hseq : ∀ k, Measurable (fun ω => RN (nxt ω k) ω lam f x) := fun k =>
      aux_prop_uniform_resolvent_det_measurable_index (fun n ω => RN n ω lam f x)
        (fun n => hRNmeas n lam f x) (fun ω => nxt ω k) (hnxt k)
    have hin : Measurable (fun ω => if x ∈ closure Q then
        limsup (fun k => RN (nxt ω k) ω lam f x) atTop else 0) := by
      by_cases hx : x ∈ closure Q
      · simp only [if_pos hx]; exact Measurable.limsup hseq
      · simp only [if_neg hx]; exact measurable_const
    exact Measurable.ite (hGoodmeas.inter (MeasurableSet.const (0 < lam))) hin measurable_const
  refine ⟨R, hA, fun lam _ f => aux_prop_uniform_resolvent_det_measurable_contmap_of_eval (R lam f)
    (hRmeas_eval lam f), ?_, ?_, ?_, ?_, ?_⟩
  · intro lam hlam f
    exact aux_prop_uniform_resolvent_mask_prob_bound P (closure Q) hK
      (fun N ω x => RN N ω lam f x) (fun ω x => R lam f ω x)
      (fun N x => hRNmeas N lam f x) (hRmeas_eval lam f)
      (by filter_upwards [hA] with ω h N; exact (h N lam hlam f).1)
      (ae_of_all _ (fun ω => (R lam f ω).continuous.continuousOn))
      good hgoodmeas htight
      (by
        filter_upwards [hGood_ae] with ω hω
        intro Mb ε hε
        obtain ⟨g, -, -, -, -, -, hgconv, hlim⟩ := hmain ω hω lam hlam f
        obtain ⟨N0, hN0⟩ := hgconv Mb ε hε
        refine ⟨N0, fun N hN hg x hx => ?_⟩
        rw [hRg ω hω lam hlam f x hx, hlim x hx]
        exact hN0 N hN hg x hx)
  · intro lam hlam f
    filter_upwards [hGood_ae] with ω hω
    obtain ⟨g, -, hgfr, hgS, ⟨C, hC0, hgH⟩, hgae, -, hlim⟩ := hmain ω hω lam hlam f
    have hRx : ∀ x ∈ closure Q, R lam f ω x = g x := fun x hx => by
      rw [hRg ω hω lam hlam f x hx, hlim x hx]
    refine ⟨?_, ?_⟩
    · have h1 : (R lam f ω : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict Q] g := by
        rw [Filter.EventuallyEq, ae_restrict_iff' hQm]
        exact Filter.Eventually.of_forall (fun x hx => hRx x (hQK hx))
      exact h1.trans hgae
    · have hzero : ∀ x ∉ Q, R lam f ω x = 0 := by
        intro x hx
        by_cases hxK : x ∈ closure Q
        · rw [hRx x hxK]; exact hgfr x (hKQ x hxK hx)
        · change Rfun lam f ω x = 0
          simp only [Rfun, if_pos (And.intro hω hlam), if_neg hxK]
      by_cases hf0 : ‖f‖ = 0
      · refine ⟨1, one_pos, fun x hx y hy => ?_, hzero⟩
        have hgx : g x = 0 := by
          have := hgS x hx; rw [hf0, zero_div] at this; exact abs_nonpos_iff.1 this
        have hgy : g y = 0 := by
          have := hgS y hy; rw [hf0, zero_div] at this; exact abs_nonpos_iff.1 this
        rw [hRx x hx, hRx y hy, hgx, hgy, hf0]
        simp
      · have hfpos : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg f) (Ne.symm hf0)
        refine ⟨C / ‖f‖ + 1, by positivity, fun x hx y hy => ?_, hzero⟩
        rw [hRx x hx, hRx y hy]
        calc |g x - g y| ≤ C * dist x y ^ (1 / 4 : ℝ) := hgH x hx y hy
          _ ≤ (C / ‖f‖ + 1) * ‖f‖ * dist x y ^ (1 / 4 : ℝ) := by
              apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg dist_nonneg _)
              rw [add_mul, div_mul_cancel₀ C hf0]
              linarith
  · intro lam hlam f
    filter_upwards [hGood_ae] with ω hω x hx
    obtain ⟨g, -, -, hgS, -, -, -, hlim⟩ := hmain ω hω lam hlam f
    rw [hRg ω hω lam hlam f x hx, hlim x hx]
    exact hgS x hx

  · filter_upwards [hGood_ae] with ω hω
    obtain ⟨Mb, hfreqB, hb⟩ := (hGood_p ω hω).2.2.2
    obtain ⟨σ, hσ, hσgood⟩ := Filter.extraction_of_frequently_atTop hfreqB
    intro lam hlam f
    obtain ⟨g, -, -, -, -, -, hgconv, hlim⟩ := hmain ω hω lam hlam f
    have htc : ∀ x ∈ closure Q,
        Tendsto (fun k => RN (σ k) ω lam f x) atTop (𝓝 (R lam f ω x)) := by
      intro x hx
      rw [hRg ω hω lam hlam f x hx, hlim x hx]
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N0, hN0⟩ := hgconv Mb ε hε
      obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.1
        (hσ.tendsto_atTop.eventually (Filter.eventually_ge_atTop N0))
      exact ⟨k0, fun k hk => by
        rw [Real.dist_eq]
        exact hN0 (σ k) (hk0 k hk) (hσgood k) x hx⟩
    exact ⟨fun x hx => le_of_tendsto' (htc x hx).abs
      (fun k => (hb (σ k) (hσgood k) lam hlam f).1 x hx),
      fun x hx y hy => le_of_tendsto' ((htc x hx).sub (htc y hy)).abs
        (fun k => (hb (σ k) (hσgood k) lam hlam f).2 x hx y hy)⟩

  · filter_upwards [hGood_ae] with omega hω
    intro lam hlam f
    obtain ⟨g, -, hgfr, hgS, -, hgae, -, hlim⟩ := hmain omega hω lam hlam f
    have hRx : ∀ x ∈ closure Q, R lam f omega x = g x := fun x hx => by
      rw [hRg omega hω lam hlam f x hx, hlim x hx]
    refine ⟨?_, ?_, fun x hx => by rw [hRx x hx]; exact hgS x hx⟩
    · have h1 : (R lam f omega : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict Q] g := by
        rw [Filter.EventuallyEq, ae_restrict_iff' hQm]
        exact Eventually.of_forall fun x hx => hRx x (subset_closure hx)
      exact h1.trans hgae
    · intro x hx
      by_cases hxK : x ∈ closure Q
      · rw [hRx x hxK]
        exact hgfr x (hKQ x hxK hx)
      · change Rfun lam f omega x = 0
        simp only [Rfun, if_pos (And.intro hω hlam), if_neg hxK]

end Paper
