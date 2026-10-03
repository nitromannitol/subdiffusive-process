module

public import Mathlib

@[expose] public section

/-! Classical separability of compact-support smooth test-function spaces supplies
a countable bank dense with one common compact support for each approximating sequence. -/

open Filter Set Topology
open scoped ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Paper

/-- The multilinear maps on `ℝ^d` form a finite-dimensional space. -/
instance aux_classical_countable_smooth_test_bank_fd (d k : ℕ) :
    FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin d → ℝ) ℝ) := by
  haveI : Module.Finite ℝ (MultilinearMap ℝ (fun _ : Fin k => Fin d → ℝ) ℝ) := inferInstance
  exact Module.Finite.of_injective
    (ContinuousMultilinearMap.toMultilinearMapLinear :
      ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin d → ℝ) ℝ →ₗ[ℝ]
        MultilinearMap ℝ (fun _ : Fin k => Fin d → ℝ) ℝ)
    (fun a b h => by
      ext v; exact congrArg (fun f => f v) h)

/-- The compact exhaustion of an open set. -/
def aux_classical_countable_smooth_test_bank_K {d : ℕ} (U : Set (Fin d → ℝ)) (m : ℕ) :
    Set (Fin d → ℝ) :=
  Metric.closedBall 0 m ∩ {x | ∀ y ∈ Uᶜ, 1 / ((m : ℝ) + 1) ≤ dist x y}

theorem aux_classical_countable_smooth_test_bank_K_compact {d : ℕ} (U : Set (Fin d → ℝ))
    (m : ℕ) : IsCompact (aux_classical_countable_smooth_test_bank_K U m) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · refine Metric.isClosed_closedBall.inter ?_
    have : {x : Fin d → ℝ | ∀ y ∈ Uᶜ, 1 / ((m : ℝ) + 1) ≤ dist x y} =
        ⋂ y ∈ Uᶜ, {x : Fin d → ℝ | 1 / ((m : ℝ) + 1) ≤ dist x y} := by
      ext x; simp
    rw [this]
    exact isClosed_biInter fun y _ => isClosed_le continuous_const (continuous_id.dist continuous_const)
  · exact Metric.isBounded_closedBall.subset inter_subset_left

theorem aux_classical_countable_smooth_test_bank_K_subset {d : ℕ} (U : Set (Fin d → ℝ))
    (m : ℕ) : aux_classical_countable_smooth_test_bank_K U m ⊆ U := by
  intro x hx
  by_contra hxU
  have := hx.2 x hxU
  rw [dist_self] at this
  have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  linarith

theorem aux_classical_countable_smooth_test_bank_exists_K {d : ℕ} {U : Set (Fin d → ℝ)}
    (hU : IsOpen U) {C : Set (Fin d → ℝ)} (hC : IsCompact C) (hCU : C ⊆ U) :
    ∃ m : ℕ, C ⊆ aux_classical_countable_smooth_test_bank_K U m := by
  obtain ⟨δ, hδ, hth⟩ := hC.exists_thickening_subset_open hU hCU
  obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall (0 : Fin d → ℝ)
  obtain ⟨m, hm⟩ := exists_nat_ge (max R (1 / δ))
  refine ⟨m, fun x hx => ⟨?_, fun y hy => ?_⟩⟩
  · exact Metric.closedBall_subset_closedBall ((le_max_left _ _).trans hm) (hR hx)
  · by_contra hlt
    rw [not_le] at hlt
    have hyth : y ∈ Metric.thickening δ C := by
      rw [Metric.mem_thickening_iff]
      refine ⟨x, hx, ?_⟩
      have h1 : 1 / ((m : ℝ) + 1) ≤ δ := by
        have h2 : 1 ≤ (m : ℝ) * δ := (div_le_iff₀ hδ).1 ((le_max_right _ _).trans hm)
        rw [div_le_iff₀ (by positivity)]; nlinarith
      rw [dist_comm]
      exact lt_of_lt_of_le hlt h1
    exact hy (hth hyth)

open scoped Classical in
/-- The jets of a smooth function, as an element of a countable product of spaces of continuous
maps on a compact set. -/
noncomputable def aux_classical_countable_smooth_test_bank_emb {d : ℕ} (K : Set (Fin d → ℝ))
    (φ : (Fin d → ℝ) → ℝ) :
    ∀ k : ℕ, C(K, ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin d → ℝ) ℝ) := fun k =>
  if h : ContDiff ℝ ∞ φ then
    ⟨fun x => iteratedFDeriv ℝ k φ x,
      (h.continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top)).comp continuous_subtype_val⟩
  else 0

theorem aux_classical_countable_smooth_test_bank_emb_apply {d : ℕ} (K : Set (Fin d → ℝ))
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) (k : ℕ) (x : K) :
    aux_classical_countable_smooth_test_bank_emb K φ k x = iteratedFDeriv ℝ k φ x := by
  classical
  unfold aux_classical_countable_smooth_test_bank_emb
  rw [dif_pos hφ]; rfl

/-- For each compact `K` there is a countable bank in `C_K^∞` dense in the jet topology. -/
theorem aux_classical_countable_smooth_test_bank_bank {d : ℕ} {K : Set (Fin d → ℝ)}
    (hK : IsCompact K) :
    ∃ g : ℕ → (Fin d → ℝ) → ℝ,
      (∀ n, ContDiff ℝ ∞ (g n) ∧ tsupport (g n) ⊆ K) ∧
      ∀ φ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ φ → tsupport φ ⊆ K →
        ∃ ix : ℕ → ℕ, Tendsto (fun n => aux_classical_countable_smooth_test_bank_emb K (g (ix n)))
          atTop (𝓝 (aux_classical_countable_smooth_test_bank_emb K φ)) := by
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  set S : Set ((Fin d → ℝ) → ℝ) := {φ | ContDiff ℝ ∞ φ ∧ tsupport φ ⊆ K} with hS
  have h0 : (fun _ : Fin d → ℝ => (0 : ℝ)) ∈ S := by
    refine ⟨contDiff_const, ?_⟩
    simp
  set I := aux_classical_countable_smooth_test_bank_emb K '' S with hI
  obtain ⟨s0, hs0count, hs0dense⟩ := TopologicalSpace.exists_countable_dense I
  set c : Set (∀ k : ℕ, C(K, ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin d → ℝ) ℝ)) :=
    Subtype.val '' s0 with hc
  have hccount : c.Countable := hs0count.image _
  have hcI : c ⊆ I := Subtype.coe_image_subset _ _
  have hIc : I ⊆ closure c := fun y hy => closure_subtype.1 (hs0dense ⟨y, hy⟩)
  have hcne : c.Nonempty := by
    have : aux_classical_countable_smooth_test_bank_emb K (fun _ => (0 : ℝ)) ∈ closure c :=
      hIc ⟨_, h0, rfl⟩
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, closure_empty] at this
    exact this
  obtain ⟨a, ha⟩ := hccount.exists_eq_range hcne
  have hpre : ∀ n, ∃ φ ∈ S, aux_classical_countable_smooth_test_bank_emb K φ = a n := by
    intro n
    have : a n ∈ c := by rw [ha]; exact mem_range_self n
    exact hcI this
  choose g hgS hgeq using hpre
  refine ⟨g, fun n => hgS n, fun φ hφ hφK => ?_⟩
  have hmem : aux_classical_countable_smooth_test_bank_emb K φ ∈ closure (range a) := by
    rw [← ha]; exact hIc ⟨φ, ⟨hφ, hφK⟩, rfl⟩
  obtain ⟨x, hx, hxlim⟩ := mem_closure_iff_seq_limit.1 hmem
  choose ix hix using hx
  refine ⟨ix, ?_⟩
  refine hxlim.congr fun n => ?_
  rw [hgeq, hix]

/-- An open Euclidean set admits a countable smooth test bank dense in the test-function topology. -/
theorem classical_countable_smooth_test_bank
    (d : ℕ) (U : Set (Fin d → ℝ)) (hU : IsOpen U) :
    ∃ f : ℕ → (Fin d → ℝ) → ℝ,
      (∀ n, ContDiff ℝ ∞ (f n) ∧ HasCompactSupport (f n) ∧ tsupport (f n) ⊆ U) ∧
      ∀ phi : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
        tsupport phi ⊆ U →
        ∃ K : Set (Fin d → ℝ), ∃ index : ℕ → ℕ,
          IsCompact K ∧ K ⊆ U ∧ tsupport phi ⊆ K ∧
          (∀ n, tsupport (f (index n)) ⊆ K) ∧
          ∀ k : ℕ, TendstoUniformly
            (fun n x => iteratedFDeriv ℝ k (fun y => f (index n) y - phi y) x)
            (fun _ => 0) atTop := by
  classical
  choose g hg1 hg2 using fun m => aux_classical_countable_smooth_test_bank_bank
    (aux_classical_countable_smooth_test_bank_K_compact U m)
  refine ⟨fun N => g (Nat.unpair N).1 (Nat.unpair N).2, ?_, ?_⟩
  · intro N
    have h := hg1 (Nat.unpair N).1 (Nat.unpair N).2
    refine ⟨h.1, ?_, h.2.trans (aux_classical_countable_smooth_test_bank_K_subset U _)⟩
    exact IsCompact.of_isClosed_subset (aux_classical_countable_smooth_test_bank_K_compact U _)
      (isClosed_tsupport _) h.2
  · intro φ hφ hφc hφU
    obtain ⟨m, hm⟩ := aux_classical_countable_smooth_test_bank_exists_K hU hφc hφU
    obtain ⟨ix, hix⟩ := hg2 m φ hφ hm
    have hKc := aux_classical_countable_smooth_test_bank_K_compact U m
    refine ⟨aux_classical_countable_smooth_test_bank_K U m, fun n => Nat.pair m (ix n), hKc,
      aux_classical_countable_smooth_test_bank_K_subset U m, hm, ?_, ?_⟩
    · intro n
      simp only [Nat.unpair_pair]
      exact (hg1 m (ix n)).2
    · intro k
      haveI : CompactSpace (aux_classical_countable_smooth_test_bank_K U m) :=
        isCompact_iff_compactSpace.1 hKc
      have hk := tendsto_pi_nhds.1 hix k
      have hu := ContinuousMap.tendsto_iff_tendstoUniformly.1 hk
      rw [Metric.tendstoUniformly_iff] at hu ⊢
      intro ε hε
      filter_upwards [hu ε hε] with n hn x
      simp only [Nat.unpair_pair]
      have hgs := (hg1 m (ix n)).1
      have hsub : iteratedFDeriv ℝ k (fun y => g m (ix n) y - φ y) x =
          iteratedFDeriv ℝ k (g m (ix n)) x - iteratedFDeriv ℝ k φ x := by
        have e : (fun y => g m (ix n) y - φ y) = g m (ix n) + (-φ) := by
          funext y; simp [sub_eq_add_neg]
        have hle : ((k : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
        rw [e, iteratedFDeriv_add_apply (hgs.of_le hle).contDiffAt ((show ContDiff ℝ ∞ (-φ) from hφ.neg).of_le hle).contDiffAt,
          iteratedFDeriv_neg_apply, ← sub_eq_add_neg]
      by_cases hx : x ∈ aux_classical_countable_smooth_test_bank_K U m
      · have := hn ⟨x, hx⟩
        rw [aux_classical_countable_smooth_test_bank_emb_apply _ hgs,
          aux_classical_countable_smooth_test_bank_emb_apply _ hφ] at this
        rw [hsub, dist_zero_left]
        rw [dist_eq_norm] at this
        rwa [norm_sub_rev] at this
      · have h1 : iteratedFDeriv ℝ k (g m (ix n)) x = 0 :=
          image_eq_zero_of_notMem_tsupport fun hxt =>
            hx ((hg1 m (ix n)).2 (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) k hxt))
        have h2 : iteratedFDeriv ℝ k φ x = 0 :=
          image_eq_zero_of_notMem_tsupport fun hxt =>
            hx (hm (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) k hxt))
        rw [hsub, h1, h2]
        simpa using hε

end Paper
