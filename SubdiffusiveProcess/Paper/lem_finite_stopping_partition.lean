module

public import SubdiffusiveProcess.ResponseMoments.Subdivision
public import SubdiffusiveProcess.Geometry.OddGrid
public import SubdiffusiveProcess.Geometry.OddGridPartition
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.CoefficientRestriction
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.VariationalResponses.CellAssembly
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import Mathlib
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.sum_errors_baseline_input
public import SubdiffusiveProcess.ResponseMoments.Interfaces
public import SubdiffusiveProcess.Paper.lem_finite_stopping_crude_cost
public import SubdiffusiveProcess.Paper.lem_finite_stopping_good_steps
public import SubdiffusiveProcess.Paper.lem_finite_stopping_partition_tree

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false




open MeasureTheory Filter TopologicalSpace Topology Finset
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper


variable {d : ℕ}
/-- **Stopping-time partition.**  For every stopping rule and final depth, the
leaves of the `(2m+1)`-adic tree give a finite family of actual cells, each a
descendant cube of the root, pairwise disjoint, covering the root up to a null
set, and exhausting all leaves. -/
theorem aux_lem_finite_stopping_partition_stopping_partition (m : ℕ) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (stop : (n : ℕ) → (Fin n → OddGridIndex d m) → Prop) (nmax : ℕ) :
    ∃ (ncell : ℕ) (depth : Fin ncell → ℕ)
      (word : (i : Fin ncell) → Fin (depth i) → OddGridIndex d m),
      (∀ i, aux_lem_finite_stopping_partition_IsLeaf stop nmax (depth i) (word i)) ∧
      (∀ (n : ℕ) (w : Fin n → OddGridIndex d m), aux_lem_finite_stopping_partition_IsLeaf stop nmax n w →
        ∃ i, (⟨depth i, word i⟩ : Σ k, Fin k → OddGridIndex d m) = ⟨n, w⟩) ∧
      Pairwise (fun i j =>
        Disjoint (descendantCell m z hr (depth i) (word i) : Set (SpatialCoordinates d))
          (descendantCell m z hr (depth j) (word j) : Set (SpatialCoordinates d))) ∧
      ((⋃ i, (descendantCell m z hr (depth i) (word i) : Set (SpatialCoordinates d)))
        =ᵐ[volume] (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  classical
  let F := aux_lem_finite_stopping_partition_leafFinset stop nmax
  let e : F ≃ Fin F.card := F.equivFin
  let leaf : Fin F.card → Σ n : Fin (nmax + 1), Fin n → OddGridIndex d m :=
    fun i => (e.symm i).1
  have hleaf : ∀ i, aux_lem_finite_stopping_partition_IsLeaf stop nmax (leaf i).1 (leaf i).2 := fun i =>
    (aux_lem_finite_stopping_partition_mem_leafFinset stop nmax _).1 (e.symm i).2
  refine ⟨F.card, fun i => (leaf i).1, fun i => (leaf i).2, hleaf, ?_, ?_, ?_⟩
  · intro n w hw
    have hn : n < nmax + 1 := Nat.lt_succ_of_le hw.1
    let p : Σ n : Fin (nmax + 1), Fin n → OddGridIndex d m := ⟨⟨n, hn⟩, w⟩
    have hp : p ∈ F := (aux_lem_finite_stopping_partition_mem_leafFinset stop nmax p).2 hw
    refine ⟨e ⟨p, hp⟩, ?_⟩
    have hl : leaf (e ⟨p, hp⟩) = p := by
      simp only [leaf]
      rw [e.symm_apply_apply]
    beta_reduce
    rw [hl]
  · intro i j hij
    apply aux_lem_finite_stopping_partition_leaf_cells_disjoint z hr stop nmax (hleaf i) (hleaf j)
    intro heq
    apply hij
    apply e.symm.injective
    apply Subtype.ext
    change leaf i = leaf j
    generalize leaf i = p at heq ⊢
    generalize leaf j = q at heq ⊢
    rcases p with ⟨⟨a, ha⟩, u⟩
    rcases q with ⟨⟨b, hb⟩, v⟩
    simp only [Sigma.mk.inj_iff] at heq
    obtain ⟨rfl, h⟩ := heq
    obtain rfl := eq_of_heq h
    rfl
  · -- cover: the union is inside the root and contains a.e. point of the root
    have hsub : (⋃ i, (descendantCell m z hr (leaf i).1 (leaf i).2 :
        Set (SpatialCoordinates d))) ⊆ centeredCube z r hr :=
      Set.iUnion_subset fun i => aux_lem_finite_stopping_partition_descendantCell_subset_root m z hr _ _
    have hD := aux_lem_finite_stopping_partition_descendantCells_union_ae_eq m z hr nmax
    have hsup : (⋃ w : Fin nmax → OddGridIndex d m,
        (descendantCell m z hr nmax w : Set (SpatialCoordinates d))) ⊆
        ⋃ i, (descendantCell m z hr (leaf i).1 (leaf i).2 : Set (SpatialCoordinates d)) := by
      intro x hx
      obtain ⟨w, hxw⟩ := Set.mem_iUnion.1 hx
      obtain ⟨n, v, hv, hxv⟩ := aux_lem_finite_stopping_partition_exists_leaf_of_mem z hr stop nmax w x hxw
      have hn : n < nmax + 1 := Nat.lt_succ_of_le hv.1
      let p : Σ n : Fin (nmax + 1), Fin n → OddGridIndex d m := ⟨⟨n, hn⟩, v⟩
      have hp : p ∈ F := (aux_lem_finite_stopping_partition_mem_leafFinset stop nmax p).2 hv
      refine Set.mem_iUnion.2 ⟨e ⟨p, hp⟩, ?_⟩
      have hl : leaf (e ⟨p, hp⟩) = p := by
        simp only [leaf]
        rw [e.symm_apply_apply]
      rw [hl]
      exact hxv
    rw [ae_eq_set]
    constructor
    · rw [Set.sdiff_eq_empty.2 hsub, measure_empty]
    · refine measure_mono_null (Set.sdiff_subset_sdiff_right hsup) ?_
      exact (ae_eq_set.1 hD).2


variable {d : ℕ}

/-! ## Poincare witnesses and triadic sides -/

theorem aux_lem_finite_stopping_partition_centeredCube_isOpenBoundedConvexDomain (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) :
    Homogenization.IsOpenBoundedConvexDomain
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  refine ⟨(centeredCube z r hr).isOpen, ?_, ?_⟩
  · refine Homogenization.Bornology.IsBounded.isBoundedDomain ?_
    show Bornology.IsBounded (Metric.ball z (r / 2))
    exact Metric.isBounded_ball
  · show Convex ℝ (Metric.ball z (r / 2))
    exact convex_ball z (r / 2)

/-- Every actual centred cube carries a killed-space Poincare witness. -/
theorem aux_lem_finite_stopping_partition_centeredCube_killedPoincare [NeZero d] (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) :
    ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖ :=
  (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain _
    (aux_lem_finite_stopping_partition_centeredCube_isOpenBoundedConvexDomain z hr)).1

/-- Descendant sides of a triadic root in a `3^h`-adic tree are triadic. -/
theorem aux_lem_finite_stopping_partition_descendantSide_zpow (h m : ℕ) (hm : 2 * m + 1 = 3 ^ h) (j : ℤ) (n : ℕ) :
    descendantSide m n ((3 : ℝ) ^ j) = (3 : ℝ) ^ (j - ((h * n : ℕ) : ℤ)) := by
  unfold descendantSide
  have hcast : (2 * (m : ℝ) + 1) = (3 : ℝ) ^ h := by exact_mod_cast hm
  rw [hcast, ← pow_mul, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]

/-! ## Refinement of partitions -/

/-- A partition of every cell of a partition is a partition. -/
theorem aux_lem_finite_stopping_partition_partition_refine {X : Type*} [MeasurableSpace X] {μ : Measure X} {Q : Set X}
    {ι : Type*} [Countable ι] (R : ι → Set X)
    (hRdisj : Pairwise (fun a b => Disjoint (R a) (R b)))
    (hRcov : (⋃ a, R a) =ᵐ[μ] Q)
    {κ : ι → Type*} [∀ a, Countable (κ a)] (q : (a : ι) → κ a → Set X)
    (hqR : ∀ a b, q a b ⊆ R a)
    (hqdisj : ∀ a, Pairwise (fun b b' => Disjoint (q a b) (q a b')))
    (hqcov : ∀ a, (⋃ b, q a b) =ᵐ[μ] R a) :
    Pairwise (fun p p' : (Σ a, κ a) => Disjoint (q p.1 p.2) (q p'.1 p'.2)) ∧
      (⋃ p : (Σ a, κ a), q p.1 p.2) =ᵐ[μ] Q := by
  constructor
  · rintro ⟨a, b⟩ ⟨a', b'⟩ hne
    by_cases haa : a = a'
    · subst haa
      have hbb : b ≠ b' := fun h => hne (by rw [h])
      exact hqdisj a hbb
    · exact (hRdisj haa).mono (hqR a b) (hqR a' b')
  · rw [Set.iUnion_sigma]
    exact (EventuallyEqSet.countable_iUnion hqcov).trans hRcov

/-! ## Actual cell energies -/

variable {Q U : Opens (SpatialCoordinates d)}

/-- The root energy density integrated over a set. -/
def aux_lem_finite_stopping_partition_energyOn (a : PositiveCoefficient Q) (u : SobolevData Q)
    (s : Set (SpatialCoordinates d)) : ℝ :=
  ∑ j : Fin d, ∫ x in s, a.val x * (u.2 j x * u.2 j x)

theorem aux_lem_finite_stopping_partition_integrableOn_energy_integrand (a : PositiveCoefficient Q) (u : SobolevData Q)
    (j : Fin d) :
    IntegrableOn (fun x => a.val x * (u.2 j x * u.2 j x)) (Q : Set (SpatialCoordinates d))
      volume := by
  obtain ⟨C, hC⟩ := coeff_ae_bound a
  exact integrableOn_coeff_mul (Lp.memLp a.val).aestronglyMeasurable hC
    (Lp.memLp (u.2 j)) (Lp.memLp (u.2 j))

theorem aux_lem_finite_stopping_partition_energy_integrand_nonneg_ae (a : PositiveCoefficient Q) (u : SobolevData Q)
    (j : Fin d) :
    ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      0 ≤ a.val x * (u.2 j x * u.2 j x) := by
  obtain ⟨c, hc, ha⟩ := a.property
  filter_upwards [ha] with x hx
  exact mul_nonneg (hc.le.trans hx) (mul_self_nonneg _)

theorem aux_lem_finite_stopping_partition_sobolevCoefficientForm_self_eq_energyOn (a : PositiveCoefficient Q)
    (u : SobolevData Q) :
    sobolevCoefficientForm a u u = aux_lem_finite_stopping_partition_energyOn a u (Q : Set (SpatialCoordinates d)) :=
  sobolevCoefficientForm_apply a u u

/-- The literal restricted energy is the set integral of the root density. -/
theorem aux_lem_finite_stopping_partition_restrict_energy_eq (hU : U ≤ Q) (a : PositiveCoefficient Q) (u : SobolevData Q) :
    sobolevCoefficientForm (positiveCoefficientRestrict hU a) (sobolevDataRestrict hU u)
      (sobolevDataRestrict hU u) = aux_lem_finite_stopping_partition_energyOn a u (U : Set (SpatialCoordinates d)) := by
  rw [sobolevCoefficientForm_apply]
  unfold aux_lem_finite_stopping_partition_energyOn
  refine Finset.sum_congr rfl fun j _ => ?_
  apply integral_congr_ae
  filter_upwards [positiveCoefficientRestrict_coeFn hU a,
    domainLpRestrict_coeFn hU (u.2 j)] with x ha hu
  change (positiveCoefficientRestrict hU a).val x *
      ((domainLpRestrict hU (u.2 j)) x * (domainLpRestrict hU (u.2 j)) x) = _
  rw [ha, hu]

theorem aux_lem_finite_stopping_partition_energyOn_nonneg (a : PositiveCoefficient Q) (u : SobolevData Q)
    {s : Set (SpatialCoordinates d)} (hs : s ⊆ Q) : 0 ≤ aux_lem_finite_stopping_partition_energyOn a u s := by
  refine Finset.sum_nonneg fun j _ => integral_nonneg_of_ae ?_
  exact ae_restrict_of_ae_restrict_of_subset hs (aux_lem_finite_stopping_partition_energy_integrand_nonneg_ae a u j)

theorem aux_lem_finite_stopping_partition_energyOn_mono (a : PositiveCoefficient Q) (u : SobolevData Q)
    {s t : Set (SpatialCoordinates d)} (hst : s ⊆ t) (ht : t ⊆ Q) :
    aux_lem_finite_stopping_partition_energyOn a u s ≤ aux_lem_finite_stopping_partition_energyOn a u t := by
  refine Finset.sum_le_sum fun j _ => ?_
  exact setIntegral_mono_set ((aux_lem_finite_stopping_partition_integrableOn_energy_integrand a u j).mono_set ht)
    (ae_restrict_of_ae_restrict_of_subset ht (aux_lem_finite_stopping_partition_energy_integrand_nonneg_ae a u j))
    (Eventually.of_forall hst)

/-- Energies of disjoint measurable subsets add below the root energy. -/
theorem aux_lem_finite_stopping_partition_energyOn_sum_le {ι : Type*} (F : Finset ι) (a : PositiveCoefficient Q)
    (u : SobolevData Q) (s : ι → Set (SpatialCoordinates d))
    (hs : ∀ i, MeasurableSet (s i)) (hsQ : ∀ i, s i ⊆ Q)
    (hdisj : (F : Set ι).PairwiseDisjoint s) :
    (∑ i ∈ F, aux_lem_finite_stopping_partition_energyOn a u (s i)) ≤ aux_lem_finite_stopping_partition_energyOn a u (Q : Set (SpatialCoordinates d)) := by
  have hunion : (∑ i ∈ F, aux_lem_finite_stopping_partition_energyOn a u (s i)) = aux_lem_finite_stopping_partition_energyOn a u (⋃ i ∈ F, s i) := by
    unfold aux_lem_finite_stopping_partition_energyOn
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_biUnion_finset F (fun i _ => hs i) hdisj
      (fun i _ => (aux_lem_finite_stopping_partition_integrableOn_energy_integrand a u j).mono_set (hsQ i))]
  rw [hunion]
  exact aux_lem_finite_stopping_partition_energyOn_mono a u (Set.iUnion₂_subset fun i _ => hsQ i) le_rfl

/-- On an a.e. partition, the cell energies sum exactly to the root energy. -/
theorem aux_lem_finite_stopping_partition_energyOn_sum_eq {ι : Type*} [Fintype ι] (a : PositiveCoefficient Q)
    (u : SobolevData Q) (s : ι → Set (SpatialCoordinates d))
    (hs : ∀ i, MeasurableSet (s i)) (hsQ : ∀ i, s i ⊆ Q)
    (hdisj : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hcov : (⋃ i, s i) =ᵐ[volume] (Q : Set (SpatialCoordinates d))) :
    (∑ i, aux_lem_finite_stopping_partition_energyOn a u (s i)) = aux_lem_finite_stopping_partition_energyOn a u (Q : Set (SpatialCoordinates d)) := by
  unfold aux_lem_finite_stopping_partition_energyOn
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← setIntegral_congr_set hcov]
  exact (integral_iUnion_fintype hs hdisj
    (fun i => (aux_lem_finite_stopping_partition_integrableOn_energy_integrand a u j).mono_set (hsQ i))).symm

/-- Volumes of disjoint measurable subsets add below the root volume. -/
theorem aux_lem_finite_stopping_partition_volume_sum_le {ι : Type*} (F : Finset ι) (s : ι → Set (SpatialCoordinates d))
    (hs : ∀ i, MeasurableSet (s i)) (hsQ : ∀ i, s i ⊆ Q)
    (hdisj : (F : Set ι).PairwiseDisjoint s)
    (hQ : volume (Q : Set (SpatialCoordinates d)) ≠ ⊤) :
    (∑ i ∈ F, volume.real (s i)) ≤ volume.real (Q : Set (SpatialCoordinates d)) := by
  rw [← measureReal_biUnion_finset hdisj (fun i _ => hs i)
    (fun i _ => ne_top_of_le_ne_top hQ (measure_mono (hsQ i)))]
  exact measureReal_mono (Set.iUnion₂_subset fun i _ => hsQ i) hQ

/-- The Dirichlet principle on a cell: the response with the literal restricted
datum is at most the literal restricted energy. -/
theorem aux_lem_finite_stopping_partition_dirichletResponse_restrict_le_energyOn (hU : U ≤ Q)
    (hPU : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph U,
      ‖(v : SobolevData U).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph U) v‖)
    (a : PositiveCoefficient Q) (u : weakSobolevGraph Q) :
    dirichletResponse (killedResponseSpace hPU) (positiveCoefficientRestrict hU a)
        ⟨sobolevDataRestrict hU u.val, sobolevDataRestrict_mem_weak hU u.property⟩ ≤
      aux_lem_finite_stopping_partition_energyOn a u.val (U : Set (SpatialCoordinates d)) := by
  have h := (dirichletResponse_isLeast (killedResponseSpace hPU)
    (positiveCoefficientRestrict hU a)
    ⟨sobolevDataRestrict hU u.val, sobolevDataRestrict_mem_weak hU u.property⟩).2
    (Set.mem_range_self (0 : (killedResponseSpace hPU).space))
  simp only [ZeroMemClass.coe_zero, add_zero] at h
  rw [← aux_lem_finite_stopping_partition_restrict_energy_eq hU a u.val]
  exact h

/-- The response of the root is the root energy of its minimizer. -/
theorem aux_lem_finite_stopping_partition_dirichletResponse_eq_energyOn (S : ResponseSpace Q) (a : PositiveCoefficient Q)
    (b : weakSobolevGraph Q) :
    dirichletResponse S a b =
      aux_lem_finite_stopping_partition_energyOn a (dirichletMinimizer S a b).val (Q : Set (SpatialCoordinates d)) :=
  aux_lem_finite_stopping_partition_sobolevCoefficientForm_self_eq_energyOn a _


/-- Least window index `⌈N / (4 H1)⌉`. -/
def aux_lem_finite_stopping_partition_obsLo (H1 N : ℕ) : ℕ := (N + (4 * H1 - 1)) / (4 * H1)

/-- Greatest window index `⌊3N / (4 H1)⌋`. -/
def aux_lem_finite_stopping_partition_obsHi (H1 N : ℕ) : ℕ := 3 * N / (4 * H1)

/-- Initial triadic depth `H1 aux_lem_finite_stopping_partition_obsLo + j`. -/
def aux_lem_finite_stopping_partition_obsT0 (H1 N : ℕ) (j : ℤ) : ℕ := (((H1 * aux_lem_finite_stopping_partition_obsLo H1 N : ℕ) : ℤ) + j).toNat

/-- Number of stage-2 levels. -/
def aux_lem_finite_stopping_partition_obsB (H1 N : ℕ) : ℕ := aux_lem_finite_stopping_partition_obsHi H1 N - aux_lem_finite_stopping_partition_obsLo H1 N

theorem aux_lem_finite_stopping_partition_obsLo_le_iff {H1 : ℕ} (hH1 : 0 < H1) (N n : ℕ) :
    aux_lem_finite_stopping_partition_obsLo H1 N ≤ n ↔ N ≤ 4 * (H1 * n) := by
  have hK : 0 < 4 * H1 := by omega
  unfold aux_lem_finite_stopping_partition_obsLo
  rw [Nat.div_le_iff_le_mul_add_pred hK, ← mul_assoc]
  generalize 4 * H1 * n = X
  omega

theorem aux_lem_finite_stopping_partition_le_obsHi_iff {H1 : ℕ} (hH1 : 0 < H1) (N n : ℕ) :
    n ≤ aux_lem_finite_stopping_partition_obsHi H1 N ↔ 4 * (H1 * n) ≤ 3 * N := by
  have hK : 0 < 4 * H1 := by omega
  unfold aux_lem_finite_stopping_partition_obsHi
  rw [Nat.le_div_iff_mul_le hK]
  constructor <;> intro h <;> linarith [mul_comm n (4 * H1), mul_assoc 4 H1 n]

theorem aux_lem_finite_stopping_partition_window_iff {H1 : ℕ} (hH1 : 0 < H1) (N n : ℕ) :
    (N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N) ↔ n ∈ Finset.Icc (aux_lem_finite_stopping_partition_obsLo H1 N) (aux_lem_finite_stopping_partition_obsHi H1 N) := by
  rw [Finset.mem_Icc, aux_lem_finite_stopping_partition_obsLo_le_iff hH1, aux_lem_finite_stopping_partition_le_obsHi_iff hH1]

theorem aux_lem_finite_stopping_partition_four_H1_obsLo_ge {H1 : ℕ} (hH1 : 0 < H1) (N : ℕ) : N ≤ 4 * (H1 * aux_lem_finite_stopping_partition_obsLo H1 N) :=
  (aux_lem_finite_stopping_partition_obsLo_le_iff hH1 N _).1 le_rfl

theorem aux_lem_finite_stopping_partition_four_H1_obsHi_le {H1 : ℕ} (hH1 : 0 < H1) (N : ℕ) : 4 * (H1 * aux_lem_finite_stopping_partition_obsHi H1 N) ≤ 3 * N :=
  (aux_lem_finite_stopping_partition_le_obsHi_iff hH1 N _).1 le_rfl

theorem aux_lem_finite_stopping_partition_four_H1_obsLo_le {H1 : ℕ} (hH1 : 0 < H1) (N : ℕ) :
    4 * (H1 * aux_lem_finite_stopping_partition_obsLo H1 N) ≤ N + 4 * H1 := by
  have h := Nat.div_mul_le_self (N + (4 * H1 - 1)) (4 * H1)
  unfold aux_lem_finite_stopping_partition_obsLo
  have : (N + (4 * H1 - 1)) / (4 * H1) * (4 * H1) = 4 * (H1 * ((N + (4 * H1 - 1)) / (4 * H1))) := by
    ring
  omega

theorem aux_lem_finite_stopping_partition_four_H1_obsHi_gt {H1 : ℕ} (hH1 : 0 < H1) (N : ℕ) :
    3 * N < 4 * (H1 * aux_lem_finite_stopping_partition_obsHi H1 N) + 4 * H1 := by
  have hK : 0 < 4 * H1 := by omega
  have h := Nat.lt_mul_div_succ (3 * N) hK
  unfold aux_lem_finite_stopping_partition_obsHi
  have : 4 * H1 * (3 * N / (4 * H1) + 1) = 4 * (H1 * (3 * N / (4 * H1))) + 4 * H1 := by ring
  omega

theorem aux_lem_finite_stopping_partition_obsLo_le_obsHi {H1 : ℕ} (hH1 : 0 < H1) {N : ℕ} (hN : 4 * H1 ≤ N) :
    aux_lem_finite_stopping_partition_obsLo H1 N ≤ aux_lem_finite_stopping_partition_obsHi H1 N := by
  rw [aux_lem_finite_stopping_partition_obsLo_le_iff hH1]
  have h1 := aux_lem_finite_stopping_partition_four_H1_obsHi_gt hH1 N
  omega

theorem aux_lem_finite_stopping_partition_obsT0_eq {H1 : ℕ} (hH1 : 0 < H1) {N : ℕ} {j : ℤ} (hN : 4 * j.natAbs ≤ N) :
    (aux_lem_finite_stopping_partition_obsT0 H1 N j : ℤ) = ((H1 * aux_lem_finite_stopping_partition_obsLo H1 N : ℕ) : ℤ) + j := by
  unfold aux_lem_finite_stopping_partition_obsT0
  apply Int.toNat_of_nonneg
  have h := aux_lem_finite_stopping_partition_four_H1_obsLo_ge hH1 N
  have h2 : j.natAbs ≤ H1 * aux_lem_finite_stopping_partition_obsLo H1 N := by omega
  have h3 : -(j.natAbs : ℤ) ≤ j := by omega
  omega

/-- The window has `B + 1` levels. -/
theorem aux_lem_finite_stopping_partition_card_window {H1 : ℕ} (hH1 : 0 < H1) {N : ℕ} (hN : 4 * H1 ≤ N) :
    Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} = aux_lem_finite_stopping_partition_obsB H1 N + 1 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (aux_lem_finite_stopping_partition_window_iff hH1 N)), Nat.card_eq_fintype_card,
    Fintype.card_coe, Nat.card_Icc, aux_lem_finite_stopping_partition_obsB]
  have := aux_lem_finite_stopping_partition_obsLo_le_obsHi hH1 hN
  omega

open Classical in
/-- The selected window levels: at most one more than the selected stage-2 levels. -/
theorem aux_lem_finite_stopping_partition_card_selected_window_le {H1 : ℕ} (hH1 : 0 < H1) (N : ℕ) (S : ℕ → Prop) :
    Nat.card {n : ℕ // S n ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} ≤
      ((Finset.univ : Finset (Fin (aux_lem_finite_stopping_partition_obsB H1 N))).filter
        (fun i => S (aux_lem_finite_stopping_partition_obsLo H1 N + (i.val + 1)))).card + 1 := by
  classical
  set a := aux_lem_finite_stopping_partition_obsLo H1 N
  set b := aux_lem_finite_stopping_partition_obsHi H1 N
  have hiff : ∀ n, (S n ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N) ↔
      n ∈ (Finset.Icc a b).filter S := by
    intro n
    rw [Finset.mem_filter, ← aux_lem_finite_stopping_partition_window_iff hH1]
    tauto
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff), Nat.card_eq_fintype_card,
    Fintype.card_coe]
  have hsub : (Finset.Icc a b).filter S ⊆
      insert a (((Finset.univ : Finset (Fin (aux_lem_finite_stopping_partition_obsB H1 N))).filter
        (fun i => S (a + (i.val + 1)))).image (fun i => a + (i.val + 1))) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rcases Nat.eq_or_lt_of_le hn.1.1 with h | h
    · exact Finset.mem_insert.2 (Or.inl h.symm)
    · refine Finset.mem_insert.2 (Or.inr ?_)
      rw [Finset.mem_image]
      have hlt : n - a - 1 < aux_lem_finite_stopping_partition_obsB H1 N := by unfold aux_lem_finite_stopping_partition_obsB; omega
      refine ⟨⟨n - a - 1, hlt⟩, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have : a + (n - a - 1 + 1) = n := by omega
        simp only [this]
        exact hn.2
      · simp only
        omega
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_insert_le _ _
    _ ≤ _ := Nat.add_le_add_right Finset.card_image_le _

/-- Stage-2 sides are the absolute triadic sides `3^(-H1 (aux_lem_finite_stopping_partition_obsLo + s))`. -/
theorem aux_lem_finite_stopping_partition_stage_side_eq {H1 : ℕ} (hH1 : 0 < H1) {N : ℕ} {j : ℤ} (hN : 4 * j.natAbs ≤ N)
    (s : ℕ) :
    descendantSide (subdivisionHalfWidth H1) s
        (descendantSide 1 (aux_lem_finite_stopping_partition_obsT0 H1 N j) ((3 : ℝ) ^ j)) =
      (3 : ℝ) ^ (-((H1 * (aux_lem_finite_stopping_partition_obsLo H1 N + s) : ℕ) : ℤ)) := by
  rw [aux_lem_finite_stopping_partition_descendantSide_zpow 1 1 (by norm_num) j, aux_lem_finite_stopping_partition_descendantSide_zpow H1 _
    (two_mul_subdivisionHalfWidth_add_one H1)]
  congr 1
  have h := aux_lem_finite_stopping_partition_obsT0_eq hH1 (N := N) (j := j) hN
  push_cast at h ⊢
  rw [one_mul, h]
  ring


variable {d : ℕ}

/-- The stage-2 cell of word `w` at depth `s` inside the initial cell `w0`. -/
def aux_lem_finite_stopping_partition_cell2 (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (t0 mg : ℕ)
    (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin s → OddGridIndex d mg) :
    Opens (SpatialCoordinates d) :=
  descendantCell mg (descendantCenter 1 z r t0 w0) (descendantSide_pos 1 t0 hr) s w

theorem aux_lem_finite_stopping_partition_cell2_eq_centeredCube (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (t0 mg : ℕ)
    (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin s → OddGridIndex d mg) :
    aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 s w =
      centeredCube (descendantCenter mg (descendantCenter 1 z r t0 w0)
        (descendantSide 1 t0 r) s w)
        (descendantSide mg s (descendantSide 1 t0 r))
        (descendantSide_pos mg s (descendantSide_pos 1 t0 hr)) := rfl

theorem aux_lem_finite_stopping_partition_cell2_subset_initial (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (t0 mg : ℕ)
    (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin s → OddGridIndex d mg) :
    (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 s w : Set (SpatialCoordinates d)) ⊆
      descendantCell 1 z hr t0 w0 :=
  aux_lem_finite_stopping_partition_descendantCell_subset_root mg _ _ s w

theorem aux_lem_finite_stopping_partition_cell2_subset_root (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (t0 mg : ℕ)
    (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin s → OddGridIndex d mg) :
    (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 s w : Set (SpatialCoordinates d)) ⊆ centeredCube z r hr :=
  (aux_lem_finite_stopping_partition_cell2_subset_initial z hr t0 mg w0 s w).trans (aux_lem_finite_stopping_partition_descendantCell_subset_root 1 z hr t0 w0)

theorem aux_lem_finite_stopping_partition_cell2_le_root (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (t0 mg : ℕ)
    (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin s → OddGridIndex d mg) :
    aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 s w ≤ centeredCube z r hr :=
  aux_lem_finite_stopping_partition_cell2_subset_root z hr t0 mg w0 s w

/-- The two-stage leaf index type. -/
abbrev aux_lem_finite_stopping_partition_LeafIdx (d t0 mg B : ℕ) :=
  (Fin t0 → OddGridIndex d 1) × (Σ s : Fin (B + 1), Fin s → OddGridIndex d mg)

/-- The two-stage leaves. -/
def aux_lem_finite_stopping_partition_leaves2 {t0 mg : ℕ}
    (stop : (Fin t0 → OddGridIndex d 1) → (n : ℕ) → (Fin n → OddGridIndex d mg) → Prop)
    (B : ℕ) : Finset (aux_lem_finite_stopping_partition_LeafIdx d t0 mg B) := by
  classical
  exact Finset.univ.filter fun p => aux_lem_finite_stopping_partition_IsLeaf (stop p.1) B p.2.1 p.2.2

theorem aux_lem_finite_stopping_partition_mem_leaves2 {t0 mg : ℕ}
    (stop : (Fin t0 → OddGridIndex d 1) → (n : ℕ) → (Fin n → OddGridIndex d mg) → Prop)
    (B : ℕ) (p : aux_lem_finite_stopping_partition_LeafIdx d t0 mg B) :
    p ∈ aux_lem_finite_stopping_partition_leaves2 stop B ↔ aux_lem_finite_stopping_partition_IsLeaf (stop p.1) B p.2.1 p.2.2 := by
  classical
  simp [aux_lem_finite_stopping_partition_leaves2]

/-- The cell of a two-stage leaf index. -/
def aux_lem_finite_stopping_partition_leafCell (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) {t0 mg B : ℕ}
    (p : aux_lem_finite_stopping_partition_LeafIdx d t0 mg B) : Opens (SpatialCoordinates d) :=
  aux_lem_finite_stopping_partition_cell2 z hr t0 mg p.1 p.2.1 p.2.2

theorem aux_lem_finite_stopping_partition_leaves2_pairwiseDisjoint (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    {t0 mg : ℕ}
    (stop : (Fin t0 → OddGridIndex d 1) → (n : ℕ) → (Fin n → OddGridIndex d mg) → Prop)
    (B : ℕ) :
    ((aux_lem_finite_stopping_partition_leaves2 stop B : Finset (aux_lem_finite_stopping_partition_LeafIdx d t0 mg B)) : Set (aux_lem_finite_stopping_partition_LeafIdx d t0 mg B)).PairwiseDisjoint
      (fun p => (aux_lem_finite_stopping_partition_leafCell z hr p : Set (SpatialCoordinates d))) := by
  rintro ⟨w0, q⟩ hp ⟨w0', q'⟩ hp' hne
  simp only [Finset.mem_coe, aux_lem_finite_stopping_partition_mem_leaves2] at hp hp'
  show Disjoint (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 q.1 q.2 : Set (SpatialCoordinates d))
    (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0' q'.1 q'.2 : Set (SpatialCoordinates d))
  by_cases hw0 : w0 = w0'
  · subst hw0
    have hqq : q ≠ q' := fun h => hne (by rw [h])
    apply aux_lem_finite_stopping_partition_leaf_cells_disjoint _ _ (stop w0) B hp hp'
    intro heq
    apply hqq
    rcases q with ⟨⟨a, ha⟩, v⟩
    rcases q' with ⟨⟨b, hb⟩, v'⟩
    simp only [Sigma.mk.inj_iff] at heq
    obtain ⟨rfl, h⟩ := heq
    obtain rfl := eq_of_heq h
    rfl
  · rw [Set.disjoint_left]
    intro x hx hx'
    exact hw0 (aux_lem_finite_stopping_partition_descendantCell_word_eq_of_mem 1 z hr t0 w0 w0' x
      (aux_lem_finite_stopping_partition_cell2_subset_initial z hr t0 mg w0 _ _ hx) (aux_lem_finite_stopping_partition_cell2_subset_initial z hr t0 mg w0' _ _ hx'))

theorem aux_lem_finite_stopping_partition_leaves2_cover (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) {t0 mg : ℕ}
    (stop : (Fin t0 → OddGridIndex d 1) → (n : ℕ) → (Fin n → OddGridIndex d mg) → Prop)
    (B : ℕ) :
    (⋃ p ∈ aux_lem_finite_stopping_partition_leaves2 stop B, (aux_lem_finite_stopping_partition_leafCell z hr p : Set (SpatialCoordinates d))) =ᵐ[volume]
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  classical
  have h1 := aux_lem_finite_stopping_partition_descendantCells_union_ae_eq 1 z hr t0
  have h2 : ∀ w0 : Fin t0 → OddGridIndex d 1,
      (⋃ w : Fin B → OddGridIndex d mg,
        (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 B w : Set (SpatialCoordinates d))) =ᵐ[volume]
        (descendantCell 1 z hr t0 w0 : Set (SpatialCoordinates d)) := fun w0 =>
    aux_lem_finite_stopping_partition_descendantCells_union_ae_eq mg _ (descendantSide_pos 1 t0 hr) B
  have h3 := (EventuallyEqSet.countable_iUnion h2).trans h1
  have hsub : (⋃ p ∈ aux_lem_finite_stopping_partition_leaves2 stop B, (aux_lem_finite_stopping_partition_leafCell z hr p : Set (SpatialCoordinates d))) ⊆
      centeredCube z r hr :=
    Set.iUnion₂_subset fun p _ => aux_lem_finite_stopping_partition_cell2_subset_root z hr t0 mg _ _ _
  have hsup : (⋃ w0 : Fin t0 → OddGridIndex d 1, ⋃ w : Fin B → OddGridIndex d mg,
      (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 B w : Set (SpatialCoordinates d))) ⊆
      ⋃ p ∈ aux_lem_finite_stopping_partition_leaves2 stop B, (aux_lem_finite_stopping_partition_leafCell z hr p : Set (SpatialCoordinates d)) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨w0, w, hxw⟩ := hx
    obtain ⟨n, v, hv, hxv⟩ := aux_lem_finite_stopping_partition_exists_leaf_of_mem _ (descendantSide_pos 1 t0 hr)
      (stop w0) B w x hxw
    have hn : n < B + 1 := Nat.lt_succ_of_le hv.1
    let p : aux_lem_finite_stopping_partition_LeafIdx d t0 mg B := (w0, ⟨⟨n, hn⟩, v⟩)
    have hp : p ∈ aux_lem_finite_stopping_partition_leaves2 stop B := (aux_lem_finite_stopping_partition_mem_leaves2 stop B p).2 hv
    exact Set.mem_biUnion hp hxv
  rw [ae_eq_set]
  constructor
  · rw [Set.sdiff_eq_empty.2 hsub, measure_empty]
  · exact measure_mono_null (Set.sdiff_subset_sdiff_right hsup) (ae_eq_set.1 h3).2


variable {d : ℕ}

/-- The regularized mass `λ = Γ(u) + fl dx` of a set. -/
def aux_lem_finite_stopping_partition_massOn {Q : Opens (SpatialCoordinates d)} (a : PositiveCoefficient Q) (u : SobolevData Q)
    (fl : ℝ) (s : Set (SpatialCoordinates d)) : ℝ :=
  aux_lem_finite_stopping_partition_energyOn a u s + fl * volume.real s

theorem aux_lem_finite_stopping_partition_energyOn_le_massOn {Q : Opens (SpatialCoordinates d)} (a : PositiveCoefficient Q)
    (u : SobolevData Q) {fl : ℝ} (hfl : 0 ≤ fl) (s : Set (SpatialCoordinates d)) :
    aux_lem_finite_stopping_partition_energyOn a u s ≤ aux_lem_finite_stopping_partition_massOn a u fl s :=
  le_add_of_nonneg_right (mul_nonneg hfl measureReal_nonneg)

theorem aux_lem_finite_stopping_partition_massOn_mono {Q : Opens (SpatialCoordinates d)} (a : PositiveCoefficient Q)
    (u : SobolevData Q) {fl : ℝ} (hfl : 0 ≤ fl) {s t : Set (SpatialCoordinates d)}
    (hst : s ⊆ t) (ht : t ⊆ Q) (hQ : volume (Q : Set (SpatialCoordinates d)) ≠ ⊤) :
    aux_lem_finite_stopping_partition_massOn a u fl s ≤ aux_lem_finite_stopping_partition_massOn a u fl t :=
  add_le_add (aux_lem_finite_stopping_partition_energyOn_mono a u hst ht) (mul_le_mul_of_nonneg_left
    (measureReal_mono hst (ne_top_of_le_ne_top hQ (measure_mono ht))) hfl)

/-- Target response on a subdomain, with the literal restricted datum and coefficient. -/
def aux_lem_finite_stopping_partition_respOn {Q U : Opens (SpatialCoordinates d)} (aT : PositiveCoefficient Q)
    (u : weakSobolevGraph Q) (hU : U ≤ Q)
    (hPU : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph U,
      ‖(v : SobolevData U).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph U) v‖) : ℝ :=
  dirichletResponse (killedResponseSpace hPU) (positiveCoefficientRestrict hU aT)
    ⟨sobolevDataRestrict hU u.val, sobolevDataRestrict_mem_weak hU u.property⟩

theorem aux_lem_finite_stopping_partition_cell2_killedPoincare [NeZero d] (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (t0 mg : ℕ) (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin s → OddGridIndex d mg) :
    ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 s w),
      ‖(v : SobolevData (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 s w)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 s w)) v‖ :=
  aux_lem_finite_stopping_partition_centeredCube_killedPoincare _ (descendantSide_pos mg s (descendantSide_pos 1 t0 hr))

section Core

open Classical

variable [NeZero d] (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (t0 mg B : ℕ)
  (aT aS : PositiveCoefficient (centeredCube z r hr))
  (u : weakSobolevGraph (centeredCube z r hr)) (fl LD : ℝ)
  (Sel : ℕ → Prop)
  (Good : (Fin t0 → OddGridIndex d 1) → (n : ℕ) → (Fin n → OddGridIndex d mg) → Prop)
  (Pad : OddGridIndex d mg → Prop)

/-- The regularized mass of a stage-2 cell. -/
def aux_lem_finite_stopping_partition_mass2 (w0 : Fin t0 → OddGridIndex d 1) (n : ℕ) (w : Fin n → OddGridIndex d mg) : ℝ :=
  aux_lem_finite_stopping_partition_massOn aS u.val fl (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 n w : Set (SpatialCoordinates d))

/-- The actual two-stage stopping rule. -/
def aux_lem_finite_stopping_partition_stop2 (w0 : Fin t0 → OddGridIndex d 1) : (n : ℕ) → (Fin n → OddGridIndex d mg) → Prop :=
  aux_lem_finite_stopping_partition_stopRule Sel (Good w0) Pad (aux_lem_finite_stopping_partition_mass2 z hr t0 mg aS u fl w0) LD

omit [NeZero d] in
theorem aux_lem_finite_stopping_partition_volume_centeredCube_ne_top' :
    volume (centeredCube z r hr : Set (SpatialCoordinates d)) ≠ ⊤ := by
  rw [centeredCube_volume]
  exact ENNReal.ofReal_ne_top

omit [NeZero d] in
/-- On a branch with no stopped prefix, the non-padded steps are at least the
selected steps minus the bad steps and the mass drops. -/
theorem aux_lem_finite_stopping_partition_residual_hits (hfl : 0 < fl) (hLD : 1 < LD) (nsel nbad g : ℕ)
    (w0 : Fin t0 → OddGridIndex d 1) (w : Fin B → OddGridIndex d mg)
    (hno : ∀ (k : ℕ) (hk : k ≤ B),
      ¬ aux_lem_finite_stopping_partition_stop2 z hr t0 mg aS u fl LD Sel Good Pad w0 k (aux_lem_finite_stopping_partition_wordPrefix w k hk))
    (hbad : ((Finset.univ : Finset (Fin B)).filter fun i =>
      ¬ Good w0 (i.val + 1) (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt)).card ≤ nbad)
    (hsel : nsel ≤ ((Finset.univ : Finset (Fin B)).filter fun i => Sel (i.val + 1)).card)
    (hmassQ : aux_lem_finite_stopping_partition_massOn aS u.val fl (centeredCube z r hr : Set (SpatialCoordinates d)) <
      LD ^ (g + 1) * (fl * (descendantSide mg B (descendantSide 1 t0 r)) ^ d)) :
    nsel - nbad - g ≤ ((Finset.univ : Finset (Fin B)).filter fun i =>
      w i ∈ (Finset.univ.filter fun l => ¬ Pad l)).card := by
  classical
  have hQ := aux_lem_finite_stopping_partition_volume_centeredCube_ne_top' z hr
  let mass := aux_lem_finite_stopping_partition_mass2 z hr t0 mg aS u fl w0
  let lam : ℕ → ℝ := fun k => if hk : k ≤ B then mass k (aux_lem_finite_stopping_partition_wordPrefix w k hk) else mass B w
  have hlam : ∀ k (hk : k ≤ B), lam k = mass k (aux_lem_finite_stopping_partition_wordPrefix w k hk) := fun k hk => dite_eq_left hk
  have hmassmono : ∀ k (hk : k + 1 ≤ B),
      mass (k + 1) (aux_lem_finite_stopping_partition_wordPrefix w (k + 1) hk) ≤ mass k (aux_lem_finite_stopping_partition_wordPrefix w k (by omega)) := by
    intro k hk
    apply aux_lem_finite_stopping_partition_massOn_mono aS u.val hfl.le _ (aux_lem_finite_stopping_partition_cell2_subset_root z hr t0 mg w0 _ _) hQ
    have h := aux_lem_finite_stopping_partition_descendantCell_subset_prefix mg (descendantCenter 1 z r t0 w0)
      (descendantSide_pos 1 t0 hr) (k + 1)
      (aux_lem_finite_stopping_partition_wordPrefix w (k + 1) hk) k (Nat.le_succ k)
    rwa [aux_lem_finite_stopping_partition_wordPrefix_wordPrefix] at h
  have hmono : ∀ k, lam (k + 1) ≤ lam k := by
    intro k
    by_cases hk : k + 1 ≤ B
    · rw [hlam (k + 1) hk, hlam k (by omega)]
      exact hmassmono k hk
    · have h1 : lam (k + 1) = mass B w := dite_eq_right hk
      by_cases hk' : k ≤ B
      · have hkB : k = B := by omega
        subst hkB
        rw [h1, hlam k hk', aux_lem_finite_stopping_partition_wordPrefix_self]
      · rw [h1, show lam k = mass B w from dite_eq_right hk']
  have hside : volume.real (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 B w : Set (SpatialCoordinates d)) =
      (descendantSide mg B (descendantSide 1 t0 r)) ^ d := by
    rw [aux_lem_finite_stopping_partition_cell2_eq_centeredCube, centeredCube_volume_real]
  have hfinal : fl * (descendantSide mg B (descendantSide 1 t0 r)) ^ d ≤ lam B := by
    rw [hlam B le_rfl, aux_lem_finite_stopping_partition_wordPrefix_self]
    change fl * _ ≤ aux_lem_finite_stopping_partition_energyOn aS u.val _ + fl * _
    rw [hside]
    exact le_add_of_nonneg_left
      (aux_lem_finite_stopping_partition_energyOn_nonneg aS u.val (aux_lem_finite_stopping_partition_cell2_subset_root z hr t0 mg w0 B w))
  have hinit : lam 0 < LD ^ (g + 1) * (fl * (descendantSide mg B (descendantSide 1 t0 r)) ^ d) :=
    lt_of_le_of_lt (by
      rw [hlam 0 (Nat.zero_le B)]
      exact aux_lem_finite_stopping_partition_massOn_mono aS u.val hfl.le (aux_lem_finite_stopping_partition_cell2_subset_root z hr t0 mg w0 _ _) le_rfl hQ) hmassQ
  have hflpos : 0 < fl * (descendantSide mg B (descendantSide 1 t0 r)) ^ d :=
    mul_pos hfl (pow_pos (descendantSide_pos mg B (descendantSide_pos 1 t0 hr)) d)
  have hdrop := aux_lem_finite_stopping_partition_dropCount_le lam LD _ hLD hflpos hmono B g hfinal hinit
  -- classification of a selected unstopped step
  have hclass : ∀ i ∈ (Finset.univ : Finset (Fin B)), Sel (i.val + 1) →
      ¬ Good w0 (i.val + 1) (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt) ∨
        w i ∈ (Finset.univ.filter fun l => ¬ Pad l) ∨ LD * lam (i.val + 1) < lam i.val := by
    intro i _ hSel
    have hns := hno (i.val + 1) i.isLt
    have hlast : aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt (Fin.last i.val) = w i :=
      congrArg w (Fin.ext rfl)
    have hinit' : (fun j : Fin i.val => aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt j.castSucc) =
        aux_lem_finite_stopping_partition_wordPrefix w i.val (Nat.le_of_lt i.isLt) := by
      funext j
      rfl
    simp only [aux_lem_finite_stopping_partition_stop2, aux_lem_finite_stopping_partition_stopRule, not_and, not_le] at hns
    by_cases hG : Good w0 (i.val + 1) (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt)
    · by_cases hP : Pad (w i)
      · right; right
        have h := hns hSel hG (by rw [hlast]; exact hP)
        rw [hlam (i.val + 1) i.isLt, hlam i.val (Nat.le_of_lt i.isLt)]
        rw [hinit'] at h
        exact h
      · right; left
        simp [hP]
    · exact Or.inl hG
  have hcount := aux_lem_finite_stopping_partition_card_filter_le_three (Finset.univ : Finset (Fin B))
    (fun i => Sel (i.val + 1))
    (fun i => ¬ Good w0 (i.val + 1) (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt))
    (fun i => w i ∈ (Finset.univ.filter fun l => ¬ Pad l))
    (fun i => LD * lam (i.val + 1) < lam i.val) hclass
  have hdropeq : ((Finset.univ : Finset (Fin B)).filter
      (fun i => LD * lam (i.val + 1) < lam i.val)).card = aux_lem_finite_stopping_partition_dropCount lam LD B :=
    aux_lem_finite_stopping_partition_card_filter_fin_eq_range B (fun s => LD * lam (s + 1) < lam s)
  omega

omit [NeZero d] in
/-- **Residual-leaf count** : the unstopped final-depth leaves
number at most `3^(d t0) 2^B |NP|^T L^(d(B-T))`, `T = nsel - nbad - g`. -/
theorem aux_lem_finite_stopping_partition_residual_card_le (hfl : 0 < fl) (hLD : 1 < LD) (nsel nbad g : ℕ)
    (hbad : ∀ (w0 : Fin t0 → OddGridIndex d 1) (w : Fin B → OddGridIndex d mg),
      ((Finset.univ : Finset (Fin B)).filter fun i =>
        ¬ Good w0 (i.val + 1) (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt)).card ≤ nbad)
    (hsel : nsel ≤ ((Finset.univ : Finset (Fin B)).filter fun i => Sel (i.val + 1)).card)
    (hmassQ : aux_lem_finite_stopping_partition_massOn aS u.val fl (centeredCube z r hr : Set (SpatialCoordinates d)) <
      LD ^ (g + 1) * (fl * (descendantSide mg B (descendantSide 1 t0 r)) ^ d)) :
    ((aux_lem_finite_stopping_partition_leaves2 (aux_lem_finite_stopping_partition_stop2 z hr t0 mg aS u fl LD Sel Good Pad) B).filter
        (fun p => ¬ aux_lem_finite_stopping_partition_stop2 z hr t0 mg aS u fl LD Sel Good Pad p.1 p.2.1 p.2.2)).card ≤
      (3 ^ d) ^ t0 * (2 ^ B * (Finset.univ.filter fun l => ¬ Pad l).card ^ (nsel - nbad - g) *
        ((2 * mg + 1) ^ d) ^ (B - (nsel - nbad - g))) := by
  classical
  set T := nsel - nbad - g with hT
  set NP := (Finset.univ.filter fun l : OddGridIndex d mg => ¬ Pad l) with hNP
  let Hs := (Finset.univ : Finset (Fin B → OddGridIndex d mg)).filter
    (fun w => T ≤ ((Finset.univ : Finset (Fin B)).filter fun i => w i ∈ NP).card)
  let f : (Fin t0 → OddGridIndex d 1) × (Fin B → OddGridIndex d mg) → aux_lem_finite_stopping_partition_LeafIdx d t0 mg B :=
    fun x => (x.1, ⟨⟨B, Nat.lt_succ_self B⟩, x.2⟩)
  have hsub : (aux_lem_finite_stopping_partition_leaves2 (aux_lem_finite_stopping_partition_stop2 z hr t0 mg aS u fl LD Sel Good Pad) B).filter
      (fun p => ¬ aux_lem_finite_stopping_partition_stop2 z hr t0 mg aS u fl LD Sel Good Pad p.1 p.2.1 p.2.2) ⊆
      ((Finset.univ : Finset (Fin t0 → OddGridIndex d 1)) ×ˢ Hs).image f := by
    intro p hp
    rw [Finset.mem_filter, aux_lem_finite_stopping_partition_mem_leaves2] at hp
    obtain ⟨hleaf, hnstop⟩ := hp
    rcases p with ⟨w0, ⟨⟨s, hs⟩, w⟩⟩
    have hsB : s = B := hleaf.2.1.resolve_left hnstop
    subst hsB
    rw [Finset.mem_image]
    refine ⟨(w0, w), ?_, rfl⟩
    rw [Finset.mem_product]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    apply aux_lem_finite_stopping_partition_residual_hits z hr t0 mg _ aS u fl LD Sel Good Pad hfl hLD nsel nbad g w0 w
    · intro k hk
      rcases Nat.lt_or_ge k _ with hlt | hge
      · exact hleaf.2.2 k hlt
      · obtain rfl : k = _ := le_antisymm hk hge
        rw [aux_lem_finite_stopping_partition_wordPrefix_self]
        exact hnstop
    · exact hbad w0 w
    · exact hsel
    · exact hmassQ
  have hHs : Hs.card ≤ 2 ^ B * NP.card ^ T * ((2 * mg + 1) ^ d) ^ (B - T) := by
    have h := aux_lem_finite_stopping_partition_card_many_hits_le B T NP
    simpa [Fintype.card_fun, Fintype.card_fin] using h
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_image_le
    _ = (3 ^ d) ^ t0 * Hs.card := by
        rw [Finset.card_product, Finset.card_univ]
        simp [Fintype.card_fin]
    _ ≤ _ := Nat.mul_le_mul_left _ hHs

/-- One stopped cell costs at most `c Γ(q) + A c L^D λ(q)`. -/
theorem aux_lem_finite_stopping_partition_stopped_leaf_le (hfl : 0 ≤ fl) (A c : ℝ) (hA : 0 ≤ A) (ρ : ℕ → ℝ)
    (hρ : ∀ s, Sel s → 0 ≤ ρ s ∧ ρ s ≤ c)
    (hcell : ∀ (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin (s + 1) → OddGridIndex d mg),
      s + 1 ≤ B → Sel (s + 1) → Good w0 (s + 1) w → Pad (w (Fin.last s)) →
      aux_lem_finite_stopping_partition_respOn aT u (aux_lem_finite_stopping_partition_cell2_le_root z hr t0 mg w0 (s + 1) w)
          (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr t0 mg w0 (s + 1) w) ≤
        ρ (s + 1) * aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 (s + 1) w) +
          A * ρ (s + 1) * aux_lem_finite_stopping_partition_energyOn aS u.val
            (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 s (fun i => w i.castSucc)))
    (p : aux_lem_finite_stopping_partition_LeafIdx d t0 mg B)
    (hstop : aux_lem_finite_stopping_partition_stop2 z hr t0 mg aS u fl LD Sel Good Pad p.1 p.2.1 p.2.2) :
    aux_lem_finite_stopping_partition_respOn aT u (aux_lem_finite_stopping_partition_cell2_le_root z hr t0 mg p.1 p.2.1 p.2.2)
        (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr t0 mg p.1 p.2.1 p.2.2) ≤
      c * aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_cell2 z hr t0 mg p.1 p.2.1 p.2.2) +
        A * c * LD * aux_lem_finite_stopping_partition_massOn aS u.val fl (aux_lem_finite_stopping_partition_cell2 z hr t0 mg p.1 p.2.1 p.2.2) := by
  rcases p with ⟨w0, ⟨⟨s, hs⟩, w⟩⟩
  cases s with
  | zero => exact absurd hstop (by simp [aux_lem_finite_stopping_partition_stop2, aux_lem_finite_stopping_partition_stopRule])
  | succ s =>
    simp only [aux_lem_finite_stopping_partition_stop2, aux_lem_finite_stopping_partition_stopRule] at hstop
    obtain ⟨hSel, hG, hP, hM⟩ := hstop
    have h1 := hcell w0 s w (by omega) hSel hG hP
    obtain ⟨hρ0, hρc⟩ := hρ (s + 1) hSel
    have hq0 : 0 ≤ aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 (s + 1) w) :=
      aux_lem_finite_stopping_partition_energyOn_nonneg aS u.val (aux_lem_finite_stopping_partition_cell2_subset_root z hr t0 mg w0 _ _)
    have hp0 : 0 ≤ aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 s (fun i => w i.castSucc)) :=
      aux_lem_finite_stopping_partition_energyOn_nonneg aS u.val (aux_lem_finite_stopping_partition_cell2_subset_root z hr t0 mg w0 _ _)
    have hpm : aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 s (fun i => w i.castSucc)) ≤
        LD * aux_lem_finite_stopping_partition_massOn aS u.val fl (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 (s + 1) w) :=
      (aux_lem_finite_stopping_partition_energyOn_le_massOn aS u.val hfl _).trans hM
    have hc0 : 0 ≤ c := hρ0.trans hρc
    calc _ ≤ _ := h1
      _ ≤ c * aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 (s + 1) w) +
            A * c * (LD * aux_lem_finite_stopping_partition_massOn aS u.val fl (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 (s + 1) w)) := by
          gcongr
      _ = _ := by ring

omit [NeZero d] in
theorem aux_lem_finite_stopping_partition_volume_sum_cells_le (F : Finset (aux_lem_finite_stopping_partition_LeafIdx d t0 mg B))
    (hdisj : (F : Set (aux_lem_finite_stopping_partition_LeafIdx d t0 mg B)).PairwiseDisjoint
      (fun p => (aux_lem_finite_stopping_partition_leafCell z hr p : Set (SpatialCoordinates d)))) :
    (∑ p ∈ F, aux_lem_finite_stopping_partition_massOn aS u.val fl (aux_lem_finite_stopping_partition_leafCell z hr p : Set (SpatialCoordinates d))) ≤
      aux_lem_finite_stopping_partition_massOn aS u.val fl (centeredCube z r hr : Set (SpatialCoordinates d)) ∨ fl < 0 := by
  by_cases hfl : fl < 0
  · exact Or.inr hfl
  · left
    push Not at hfl
    unfold aux_lem_finite_stopping_partition_massOn
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    exact add_le_add
      (aux_lem_finite_stopping_partition_energyOn_sum_le F aS u.val _ (fun p => (aux_lem_finite_stopping_partition_leafCell z hr p).isOpen.measurableSet)
        (fun p => aux_lem_finite_stopping_partition_cell2_subset_root z hr t0 mg _ _ _) hdisj)
      (mul_le_mul_of_nonneg_left
        (aux_lem_finite_stopping_partition_volume_sum_le F _ (fun p => (aux_lem_finite_stopping_partition_leafCell z hr p).isOpen.measurableSet)
          (fun p => aux_lem_finite_stopping_partition_cell2_subset_root z hr t0 mg _ _ _) hdisj
          (aux_lem_finite_stopping_partition_volume_centeredCube_ne_top' z hr)) hfl)

/-- **Stopped-cell budget**. -/
theorem aux_lem_finite_stopping_partition_stopped_sum_le (hfl : 0 ≤ fl) (A c : ℝ) (hA : 0 ≤ A) (hc : 0 ≤ c) (hLD0 : 0 ≤ LD)
    (ρ : ℕ → ℝ) (hρ : ∀ s, Sel s → 0 ≤ ρ s ∧ ρ s ≤ c)
    (hcell : ∀ (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin (s + 1) → OddGridIndex d mg),
      s + 1 ≤ B → Sel (s + 1) → Good w0 (s + 1) w → Pad (w (Fin.last s)) →
      aux_lem_finite_stopping_partition_respOn aT u (aux_lem_finite_stopping_partition_cell2_le_root z hr t0 mg w0 (s + 1) w)
          (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr t0 mg w0 (s + 1) w) ≤
        ρ (s + 1) * aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 (s + 1) w) +
          A * ρ (s + 1) * aux_lem_finite_stopping_partition_energyOn aS u.val
            (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 s (fun i => w i.castSucc))) :
    (∑ p ∈ (aux_lem_finite_stopping_partition_leaves2 (aux_lem_finite_stopping_partition_stop2 z hr t0 mg aS u fl LD Sel Good Pad) B).filter
        (fun p => aux_lem_finite_stopping_partition_stop2 z hr t0 mg aS u fl LD Sel Good Pad p.1 p.2.1 p.2.2),
      aux_lem_finite_stopping_partition_respOn aT u (aux_lem_finite_stopping_partition_cell2_le_root z hr t0 mg p.1 p.2.1 p.2.2)
        (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr t0 mg p.1 p.2.1 p.2.2)) ≤
      c * aux_lem_finite_stopping_partition_energyOn aS u.val (centeredCube z r hr : Set (SpatialCoordinates d)) +
        A * c * LD * aux_lem_finite_stopping_partition_massOn aS u.val fl (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  classical
  set F := (aux_lem_finite_stopping_partition_leaves2 (aux_lem_finite_stopping_partition_stop2 z hr t0 mg aS u fl LD Sel Good Pad) B).filter
    (fun p => aux_lem_finite_stopping_partition_stop2 z hr t0 mg aS u fl LD Sel Good Pad p.1 p.2.1 p.2.2) with hF
  have hdisj : (F : Set (aux_lem_finite_stopping_partition_LeafIdx d t0 mg B)).PairwiseDisjoint
      (fun p => (aux_lem_finite_stopping_partition_leafCell z hr p : Set (SpatialCoordinates d))) :=
    (aux_lem_finite_stopping_partition_leaves2_pairwiseDisjoint z hr _ B).subset (Finset.coe_subset.2 (Finset.filter_subset _ _))
  have hE := aux_lem_finite_stopping_partition_energyOn_sum_le F aS u.val (fun p => (aux_lem_finite_stopping_partition_leafCell z hr p : Set (SpatialCoordinates d)))
    (fun p => (aux_lem_finite_stopping_partition_leafCell z hr p).isOpen.measurableSet)
    (fun p => aux_lem_finite_stopping_partition_cell2_subset_root z hr t0 mg _ _ _) hdisj
  have hM := (aux_lem_finite_stopping_partition_volume_sum_cells_le z hr t0 mg B aS u fl F hdisj).resolve_right (not_lt.2 hfl)
  calc _ ≤ ∑ p ∈ F, (c * aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_leafCell z hr p : Set (SpatialCoordinates d)) +
          A * c * LD * aux_lem_finite_stopping_partition_massOn aS u.val fl (aux_lem_finite_stopping_partition_leafCell z hr p : Set (SpatialCoordinates d))) := by
        refine Finset.sum_le_sum fun p hp => ?_
        exact aux_lem_finite_stopping_partition_stopped_leaf_le z hr t0 mg B aT aS u fl LD Sel Good Pad hfl A c hA ρ hρ hcell p
          (Finset.mem_filter.1 hp).2
    _ = c * ∑ p ∈ F, aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_leafCell z hr p : Set (SpatialCoordinates d)) +
          A * c * LD * ∑ p ∈ F, aux_lem_finite_stopping_partition_massOn aS u.val fl (aux_lem_finite_stopping_partition_leafCell z hr p : Set (SpatialCoordinates d)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := by
        have hAcL : 0 ≤ A * c * LD := mul_nonneg (mul_nonneg hA hc) hLD0
        gcongr

/-- **Per-sample finite stopping partition** (one sample).
The conclusion has exactly the partition/sum shape of the parent. -/
theorem aux_lem_finite_stopping_partition_core_partition (hfl : 0 < fl) (hLD : 1 < LD) (A c Kc : ℝ) (hA : 0 ≤ A) (hc : 0 ≤ c)
    (ρ : ℕ → ℝ) (hρ : ∀ s, Sel s → 0 ≤ ρ s ∧ ρ s ≤ c)
    (hcell : ∀ (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin (s + 1) → OddGridIndex d mg),
      s + 1 ≤ B → Sel (s + 1) → Good w0 (s + 1) w → Pad (w (Fin.last s)) →
      aux_lem_finite_stopping_partition_respOn aT u (aux_lem_finite_stopping_partition_cell2_le_root z hr t0 mg w0 (s + 1) w)
          (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr t0 mg w0 (s + 1) w) ≤
        ρ (s + 1) * aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 (s + 1) w) +
          A * ρ (s + 1) * aux_lem_finite_stopping_partition_energyOn aS u.val
            (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 s (fun i => w i.castSucc)))
    (nsel nbad g : ℕ)
    (hbad : ∀ (w0 : Fin t0 → OddGridIndex d 1) (w : Fin B → OddGridIndex d mg),
      ((Finset.univ : Finset (Fin B)).filter fun i =>
        ¬ Good w0 (i.val + 1) (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt)).card ≤ nbad)
    (hsel : nsel ≤ ((Finset.univ : Finset (Fin B)).filter fun i => Sel (i.val + 1)).card)
    (hmassQ : aux_lem_finite_stopping_partition_massOn aS u.val fl (centeredCube z r hr : Set (SpatialCoordinates d)) <
      LD ^ (g + 1) * (fl * (descendantSide mg B (descendantSide 1 t0 r)) ^ d))
    (hcrude : ∀ (w0 : Fin t0 → OddGridIndex d 1) (w : Fin B → OddGridIndex d mg),
      aux_lem_finite_stopping_partition_respOn aT u (aux_lem_finite_stopping_partition_cell2_le_root z hr t0 mg w0 B w) (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr t0 mg w0 B w) ≤
        Kc) :
    ∃ (ncell : ℕ) (centers : Fin ncell → SpatialCoordinates d)
      (sides : Fin ncell → ℝ) (hside : ∀ i, 0 < sides i),
    let cell := fun i => centeredCube (centers i) (sides i) (hside i)
    ∃ hle : ∀ i, cell i ≤ centeredCube z r hr,
    (∀ i, ∃ s ≤ B, sides i = descendantSide mg s (descendantSide 1 t0 r)) ∧
    Pairwise (fun i j => Disjoint (cell i : Set (SpatialCoordinates d))
      (cell j : Set (SpatialCoordinates d))) ∧
    ((⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume]
      (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
    ∃ hPcell : ∀ i, ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (cell i),
      ‖(v : SobolevData (cell i)).1‖ ≤
        K * ‖@subspaceGradient d (cell i) (killedSobolevGraph (cell i)) v‖,
    let bcell : ∀ i, weakSobolevGraph (cell i) := fun i =>
      ⟨sobolevDataRestrict (hle i) u.val, sobolevDataRestrict_mem_weak (hle i) u.property⟩
    ∃ R : ℕ, R ≤ (3 ^ d) ^ t0 * (2 ^ B * (Finset.univ.filter fun l => ¬ Pad l).card ^
            (nsel - nbad - g) * ((2 * mg + 1) ^ d) ^ (B - (nsel - nbad - g))) ∧
    (∑ i : Fin ncell,
      @dirichletResponse d (cell i) (@killedResponseSpace d (cell i) (hPcell i))
        (positiveCoefficientRestrict (hle i) aT) (bcell i)) ≤
      c * aux_lem_finite_stopping_partition_energyOn aS u.val (centeredCube z r hr : Set (SpatialCoordinates d)) +
        A * c * LD * aux_lem_finite_stopping_partition_massOn aS u.val fl (centeredCube z r hr : Set (SpatialCoordinates d)) +
        (R : ℝ) * Kc := by
  classical
  set stop := aux_lem_finite_stopping_partition_stop2 z hr t0 mg aS u fl LD Sel Good Pad with hstopdef
  set F := aux_lem_finite_stopping_partition_leaves2 stop B with hFdef
  let e : F ≃ Fin F.card := F.equivFin
  let leaf : Fin F.card → aux_lem_finite_stopping_partition_LeafIdx d t0 mg B := fun i => (e.symm i).1
  have hleafmem : ∀ i, leaf i ∈ F := fun i => (e.symm i).2
  have hleaf_e : ∀ (p : aux_lem_finite_stopping_partition_LeafIdx d t0 mg B) (hp : p ∈ F), leaf (e ⟨p, hp⟩) = p := by
    intro p hp
    simp only [leaf]
    rw [e.symm_apply_apply]
  let resp : aux_lem_finite_stopping_partition_LeafIdx d t0 mg B → ℝ := fun p =>
    aux_lem_finite_stopping_partition_respOn aT u (aux_lem_finite_stopping_partition_cell2_le_root z hr t0 mg p.1 p.2.1 p.2.2)
      (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr t0 mg p.1 p.2.1 p.2.2)
  refine ⟨F.card,
    fun i => descendantCenter mg (descendantCenter 1 z r t0 (leaf i).1)
      (descendantSide 1 t0 r) (leaf i).2.1 (leaf i).2.2,
    fun i => descendantSide mg (leaf i).2.1 (descendantSide 1 t0 r),
    fun i => descendantSide_pos mg _ (descendantSide_pos 1 t0 hr), ?_⟩
  refine ⟨fun i => aux_lem_finite_stopping_partition_cell2_le_root z hr t0 mg (leaf i).1 (leaf i).2.1 (leaf i).2.2,
    ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(leaf i).2.1, Nat.lt_succ_iff.1 (leaf i).2.1.isLt, rfl⟩
  · intro i j hij
    have hne : leaf i ≠ leaf j := fun h => hij (e.symm.injective (Subtype.ext h))
    exact aux_lem_finite_stopping_partition_leaves2_pairwiseDisjoint z hr stop B (hleafmem i) (hleafmem j) hne
  · have hset : (⋃ i, (aux_lem_finite_stopping_partition_leafCell z hr (leaf i) : Set (SpatialCoordinates d))) =
        ⋃ p ∈ F, (aux_lem_finite_stopping_partition_leafCell z hr p : Set (SpatialCoordinates d)) := by
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨i, hx⟩
        exact ⟨leaf i, hleafmem i, hx⟩
      · rintro ⟨p, hp, hx⟩
        refine ⟨e ⟨p, hp⟩, ?_⟩
        rw [hleaf_e p hp]
        exact hx
    have h := aux_lem_finite_stopping_partition_leaves2_cover z hr stop B
    rw [← hset] at h
    exact h
  · refine ⟨fun i => aux_lem_finite_stopping_partition_cell2_killedPoincare z hr t0 mg (leaf i).1 (leaf i).2.1 (leaf i).2.2,
      (F.filter (fun p => ¬ stop p.1 p.2.1 p.2.2)).card,
      aux_lem_finite_stopping_partition_residual_card_le z hr t0 mg B aS u fl LD Sel Good Pad hfl hLD nsel nbad g hbad hsel hmassQ,
      ?_⟩
    show (∑ i : Fin F.card, resp (leaf i)) ≤ _
    have hsum : (∑ i : Fin F.card, resp (leaf i)) = ∑ p ∈ F, resp p := by
      rw [← Finset.sum_coe_sort F]
      exact Equiv.sum_comp e.symm (fun x : F => resp x.1)
    rw [hsum, ← Finset.sum_filter_add_sum_filter_not F (fun p => stop p.1 p.2.1 p.2.2)]
    have h1 := aux_lem_finite_stopping_partition_stopped_sum_le z hr t0 mg B aT aS u fl LD Sel Good Pad hfl.le A c hA hc
      (by linarith) ρ hρ hcell
    have hres : ∀ p ∈ F.filter (fun p => ¬ stop p.1 p.2.1 p.2.2), resp p ≤ Kc := by
      intro p hp
      rw [Finset.mem_filter, hFdef, aux_lem_finite_stopping_partition_mem_leaves2] at hp
      obtain ⟨hleaf, hnstop⟩ := hp
      rcases p with ⟨w0, ⟨⟨s, hs⟩, w⟩⟩
      have hsB : s = B := hleaf.2.1.resolve_left hnstop
      subst hsB
      exact hcrude w0 w
    have h2 := Finset.sum_le_card_nsmul _ _ Kc hres
    rw [nsmul_eq_mul] at h2
    exact add_le_add h1 h2

end Core


variable {d : ℕ}
/-- Natural-number bound of the residual count by one power of three. -/
theorem aux_lem_finite_stopping_partition_rcount_le_pow (d t0 B T H1 a0 NP m : ℕ) (hm : 2 * m + 1 = 3 ^ H1)
    (hNP : NP ≤ 3 ^ a0 * (2 * m + 1) ^ (d - 1)) :
    (3 ^ d) ^ t0 * (2 ^ B * NP ^ T * ((2 * m + 1) ^ d) ^ (B - T)) ≤
      3 ^ (d * t0 + B + (a0 + H1 * (d - 1)) * T + H1 * d * (B - T)) := by
  have h2 : 2 ^ B ≤ 3 ^ B := Nat.pow_le_pow_left (by norm_num) B
  have hNP' : NP ^ T ≤ (3 ^ (a0 + H1 * (d - 1))) ^ T := by
    apply Nat.pow_le_pow_left
    calc NP ≤ 3 ^ a0 * (2 * m + 1) ^ (d - 1) := hNP
      _ = 3 ^ (a0 + H1 * (d - 1)) := by rw [hm, ← pow_mul, ← pow_add]
  calc (3 ^ d) ^ t0 * (2 ^ B * NP ^ T * ((2 * m + 1) ^ d) ^ (B - T)) ≤
        (3 ^ d) ^ t0 * (3 ^ B * (3 ^ (a0 + H1 * (d - 1))) ^ T * ((2 * m + 1) ^ d) ^ (B - T)) := by
        gcongr
    _ = 3 ^ (d * t0 + B + (a0 + H1 * (d - 1)) * T + H1 * d * (B - T)) := by
        rw [hm]
        simp only [← pow_mul, ← pow_add]
        ring_nf

/-- The exponent inequality, in real atoms. -/
theorem aux_lem_finite_stopping_partition_exponent_ineq (θ H1 a0 σ ε D d N n1 B T nsel nbad g c2 t0 j : ℝ)
    (hθ : 0 < θ) (hH1 : 1 ≤ H1) (hH1θ : 12 ≤ θ * H1) (ha0H : 8 * a0 ≤ H1)
    (hσ : σ = θ / 16) (hε : ε = θ / 64) (hD : 0 < D) (hDθ : ε + 1 + 3 * d / 4 ≤ θ * D / 16)
    (hd : 0 ≤ d) (hN : 0 ≤ N)
    (h_t0 : t0 + H1 * B = H1 * n1 + j) (hn1 : 4 * (H1 * n1) ≤ 3 * N)
    (hB0 : 0 ≤ B) (hBn1 : B ≤ n1) (hsel : θ * (B + 1) ≤ nsel + 1)
    (hHB : N / 2 - H1 ≤ H1 * (B + 1)) (hbad : H1 * nbad ≤ θ * N / 16)
    (hg : H1 * g ≤ ((ε + 1) * N + d * (H1 * n1) + c2) / D + H1)
    (hT : nsel - nbad - g ≤ T) (hT0 : 0 ≤ T) :
    d * t0 + B + a0 * T + H1 * d * B - H1 * T + ε * N - (d - σ) * (H1 * n1) ≤
      d * j + (7 / 8) * (θ * H1 + 2 * H1 + c2 / D) - (13 / 64) * θ * N := by
  -- the left side after the telescoping `t0 + H1 B = H1 n1 + j`
  have hL : d * t0 + B + a0 * T + H1 * d * B - H1 * T + ε * N - (d - σ) * (H1 * n1) =
      d * j + B + a0 * T - H1 * T + ε * N + σ * (H1 * n1) := by
    have : d * t0 + H1 * d * B = d * (H1 * n1) + d * j := by
      rw [show H1 * d * B = d * (H1 * B) by ring, ← mul_add, h_t0]; ring
    linarith
  rw [hL]
  have hH1nn : (0 : ℝ) ≤ H1 := by linarith
  -- a0 T ≤ H1 T / 8
  have ha0T : a0 * T ≤ H1 * T / 8 := by
    have := mul_le_mul_of_nonneg_right ha0H hT0
    linarith
  -- lower bound on H1 * nsel
  have hH1sel : θ * (N / 2 - H1) - H1 ≤ H1 * nsel := by
    have h1 : H1 * (θ * (B + 1)) ≤ H1 * (nsel + 1) := mul_le_mul_of_nonneg_left hsel hH1nn
    have h2 : θ * (N / 2 - H1) ≤ θ * (H1 * (B + 1)) := mul_le_mul_of_nonneg_left hHB hθ.le
    have h3 : H1 * (θ * (B + 1)) = θ * (H1 * (B + 1)) := by ring
    have h4 : H1 * (nsel + 1) = H1 * nsel + H1 := by ring
    linarith
  -- upper bound on H1 * g
  have hdn1 : d * (H1 * n1) ≤ 3 * d * N / 4 := by
    have := mul_le_mul_of_nonneg_left hn1 hd
    linarith
  have hnum : (ε + 1) * N + d * (H1 * n1) + c2 ≤ θ * N * D / 16 + c2 := by
    have h1 : (ε + 1 + 3 * d / 4) * N ≤ θ * D / 16 * N := mul_le_mul_of_nonneg_right hDθ hN
    have h2 : (ε + 1 + 3 * d / 4) * N = (ε + 1) * N + 3 * d * N / 4 := by ring
    have h3 : θ * D / 16 * N = θ * N * D / 16 := by ring
    linarith
  have hfrac : ((ε + 1) * N + d * (H1 * n1) + c2) / D ≤ θ * N / 16 + c2 / D := by
    calc ((ε + 1) * N + d * (H1 * n1) + c2) / D ≤ (θ * N * D / 16 + c2) / D :=
          div_le_div_of_nonneg_right hnum hD.le
      _ = θ * N / 16 + c2 / D := by
          rw [add_div]
          congr 1
          field_simp
  have hH1g : H1 * g ≤ θ * N / 16 + c2 / D + H1 := by linarith
  -- lower bound on H1 * T
  have hH1T : H1 * nsel - H1 * nbad - H1 * g ≤ H1 * T := by
    have := mul_le_mul_of_nonneg_left hT hH1nn
    have h2 : H1 * (nsel - nbad - g) = H1 * nsel - H1 * nbad - H1 * g := by ring
    linarith
  -- B and σ H1 n1 are small
  have hθn1 : θ * (H1 * n1) ≤ 3 * θ * N / 4 := by
    have := mul_le_mul_of_nonneg_left hn1 hθ.le
    linarith
  have hBsmall : B ≤ θ * N / 16 := by
    have h1 : B * 12 ≤ B * (θ * H1) := mul_le_mul_of_nonneg_left hH1θ hB0
    have h2 : θ * (H1 * B) ≤ θ * (H1 * n1) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBn1 hH1nn) hθ.le
    have h3 : B * (θ * H1) = θ * (H1 * B) := by ring
    linarith
  have hσn1 : σ * (H1 * n1) ≤ 3 * θ * N / 64 := by
    rw [hσ]
    have : θ / 16 * (H1 * n1) = θ * (H1 * n1) / 16 := by ring
    linarith
  rw [hε]
  have hθH1 : (7 / 8) * (θ * (N / 2 - H1)) = (7 / 16) * (θ * N) - (7 / 8) * (θ * H1) := by ring
  have hθN : θ * N / 16 = (1 / 16) * (θ * N) := by ring
  have hθN2 : 3 * θ * N / 64 = (3 / 64) * (θ * N) := by ring
  have hθN3 : θ / 64 * N = (1 / 64) * (θ * N) := by ring
  have hθN4 : (13 / 64) * θ * N = (13 / 64) * (θ * N) := by ring
  linarith [ha0T, hH1T, hH1sel, hbad, hH1g, hBsmall, hσn1]


theorem aux_lem_finite_stopping_partition_rpow3_anti {a b : ℝ} (h : a ≤ b) : (3 : ℝ) ^ a ≤ (3 : ℝ) ^ b :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h

theorem aux_lem_finite_stopping_partition_prob_union_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A B : Set Ω)
    (CA CB γA γB γ Ceta N : ℝ) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hγA : γ ≤ γA) (hγB : γ ≤ γB)
    (hN : 0 ≤ N) (hC : CA + CB ≤ Ceta)
    (hA : μ A ≤ ENNReal.ofReal (CA * (3 : ℝ) ^ (-γA * N)))
    (hB : μ B ≤ ENNReal.ofReal (CB * (3 : ℝ) ^ (-γB * N))) :
    μ (A ∪ B) ≤ ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-γ * N)) := by
  have h3A : (3 : ℝ) ^ (-γA * N) ≤ (3 : ℝ) ^ (-γ * N) := aux_lem_finite_stopping_partition_rpow3_anti (by nlinarith)
  have h3B : (3 : ℝ) ^ (-γB * N) ≤ (3 : ℝ) ^ (-γ * N) := aux_lem_finite_stopping_partition_rpow3_anti (by nlinarith)
  have hpos : (0 : ℝ) ≤ (3 : ℝ) ^ (-γ * N) := Real.rpow_nonneg (by norm_num) _
  calc μ (A ∪ B) ≤ μ A + μ B := measure_union_le A B
    _ ≤ ENNReal.ofReal (CA * (3 : ℝ) ^ (-γA * N)) + ENNReal.ofReal (CB * (3 : ℝ) ^ (-γB * N)) :=
        add_le_add hA hB
    _ = ENNReal.ofReal (CA * (3 : ℝ) ^ (-γA * N) + CB * (3 : ℝ) ^ (-γB * N)) :=
        (ENNReal.ofReal_add (mul_nonneg hCA (Real.rpow_nonneg (by norm_num) _))
          (mul_nonneg hCB (Real.rpow_nonneg (by norm_num) _))).symm
    _ ≤ ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-γ * N)) := by
        apply ENNReal.ofReal_le_ofReal
        calc CA * (3 : ℝ) ^ (-γA * N) + CB * (3 : ℝ) ^ (-γB * N) ≤
              CA * (3 : ℝ) ^ (-γ * N) + CB * (3 : ℝ) ^ (-γ * N) :=
              add_le_add (mul_le_mul_of_nonneg_left h3A hCA) (mul_le_mul_of_nonneg_left h3B hCB)
          _ = (CA + CB) * (3 : ℝ) ^ (-γ * N) := by ring
          _ ≤ Ceta * (3 : ℝ) ^ (-γ * N) := mul_le_mul_of_nonneg_right hC hpos

/-- The regularized mass is below `L^(D(g+1))` times the final floor mass. -/
theorem aux_lem_finite_stopping_partition_mass_lt_drops (Γ φ2 rd ε N c2 a K : ℝ) (hφ : 0 < φ2)
    (hΓ : Γ ≤ (3 : ℝ) ^ (ε * N) * φ2) (hrd : 0 ≤ rd) (hc2 : 1 + rd ≤ (3 : ℝ) ^ c2)
    (hεN : -N ≤ ε * N) (hX : (ε + 1) * N + a + c2 < K) :
    Γ + (3 : ℝ) ^ (-N) * φ2 * rd < (3 : ℝ) ^ K * ((3 : ℝ) ^ (-N) * φ2 * (3 : ℝ) ^ (-a)) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hmN : (3 : ℝ) ^ (-N) ≤ (3 : ℝ) ^ (ε * N) := aux_lem_finite_stopping_partition_rpow3_anti hεN
  have hrhs : (3 : ℝ) ^ K * ((3 : ℝ) ^ (-N) * φ2 * (3 : ℝ) ^ (-a)) =
      (3 : ℝ) ^ (K + (-N) + (-a)) * φ2 := by
    rw [Real.rpow_add h3, Real.rpow_add h3]
    ring
  rw [hrhs]
  have hlt : (3 : ℝ) ^ (ε * N + c2) < (3 : ℝ) ^ (K + (-N) + (-a)) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hmid : Γ + (3 : ℝ) ^ (-N) * φ2 * rd ≤ (3 : ℝ) ^ (ε * N + c2) * φ2 := by
    rw [Real.rpow_add h3]
    have h1 : (3 : ℝ) ^ (-N) * φ2 * rd ≤ (3 : ℝ) ^ (ε * N) * φ2 * rd :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmN hφ.le) hrd
    have h2 : (3 : ℝ) ^ (ε * N) * φ2 * (1 + rd) ≤ (3 : ℝ) ^ (ε * N) * φ2 * (3 : ℝ) ^ c2 :=
      mul_le_mul_of_nonneg_left hc2 (mul_nonneg (Real.rpow_nonneg h3.le _) hφ.le)
    nlinarith
  exact lt_of_le_of_lt hmid (mul_lt_mul_of_pos_right hlt hφ)

/-- The residual count times the crude cost is bounded by one power of three. -/
theorem aux_lem_finite_stopping_partition_remainder_le (R E : ℕ) (hR : R ≤ 3 ^ E) (ε N σ d a φ2 bound : ℝ) (hφ : 0 ≤ φ2)
    (hE : (E : ℝ) + ε * N - (d - σ) * a ≤ bound) :
    (R : ℝ) * ((3 : ℝ) ^ (ε * N) * ((3 : ℝ) ^ (-a)) ^ (d - σ) * φ2) ≤
      (3 : ℝ) ^ bound * φ2 := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hRr : (R : ℝ) ≤ (3 : ℝ) ^ (E : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hR
  have hside : ((3 : ℝ) ^ (-a)) ^ (d - σ) = (3 : ℝ) ^ (-(d - σ) * a) := by
    rw [← Real.rpow_mul h3.le]
    ring_nf
  have hprod : (3 : ℝ) ^ (E : ℝ) * ((3 : ℝ) ^ (ε * N) * (3 : ℝ) ^ (-(d - σ) * a)) =
      (3 : ℝ) ^ ((E : ℝ) + ε * N - (d - σ) * a) := by
    have hsplit : (E : ℝ) + ε * N - (d - σ) * a = (E : ℝ) + (ε * N + (-(d - σ) * a)) := by ring
    rw [hsplit, Real.rpow_add h3, Real.rpow_add h3]
  rw [hside]
  calc (R : ℝ) * ((3 : ℝ) ^ (ε * N) * (3 : ℝ) ^ (-(d - σ) * a) * φ2) =
        (R : ℝ) * ((3 : ℝ) ^ (ε * N) * (3 : ℝ) ^ (-(d - σ) * a)) * φ2 := by ring
    _ ≤ (3 : ℝ) ^ (E : ℝ) * ((3 : ℝ) ^ (ε * N) * (3 : ℝ) ^ (-(d - σ) * a)) * φ2 := by
        gcongr
    _ = (3 : ℝ) ^ ((E : ℝ) + ε * N - (d - σ) * a) * φ2 := by rw [hprod]
    _ ≤ (3 : ℝ) ^ bound * φ2 := mul_le_mul_of_nonneg_right (aux_lem_finite_stopping_partition_rpow3_anti hE) hφ

/-- The paper's normalizing sequence `κ_J`. -/
def aux_lem_finite_stopping_partition_kappaSeq {d : ℕ} (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (J : ℕ) : ℝ :=
  Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
    SubdiffusiveProcess.CoarseGrainingVocab.ahom model J

theorem aux_lem_finite_stopping_partition_kappaSeq_pos {d : ℕ} (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (J : ℕ) :
    0 < aux_lem_finite_stopping_partition_kappaSeq model J :=
  mul_pos (Real.exp_pos _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model J)

/-- The paper's ratio `r_{T,S}(k) = (κ_{T-k}/κ_T) / (κ_{S-k}/κ_S)` at `k = H1 n`. -/
def aux_lem_finite_stopping_partition_kappaRatio {d : ℕ} (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (H1 target source n : ℕ) : ℝ :=
  (aux_lem_finite_stopping_partition_kappaSeq model (target - H1 * n) / aux_lem_finite_stopping_partition_kappaSeq model target) /
    (aux_lem_finite_stopping_partition_kappaSeq model (source - H1 * n) / aux_lem_finite_stopping_partition_kappaSeq model source)

theorem aux_lem_finite_stopping_partition_kappaRatio_nonneg {d : ℕ} (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H1 target source n : ℕ) : 0 ≤ aux_lem_finite_stopping_partition_kappaRatio model H1 target source n := by
  unfold aux_lem_finite_stopping_partition_kappaRatio
  have h := aux_lem_finite_stopping_partition_kappaSeq_pos model
  exact div_nonneg (div_nonneg (h _).le (h _).le) (div_nonneg (h _).le (h _).le)

theorem aux_lem_finite_stopping_partition_c2Norm_nonneg {d : ℕ} (S : Set (SpatialCoordinates d)) (f : SpatialCoordinates d → ℝ) :
    0 ≤ c2Norm S f := by
  unfold c2Norm
  refine add_nonneg (add_nonneg ?_ ?_) ?_ <;>
    exact Real.sSup_nonneg (by rintro _ ⟨x, _, rfl⟩; positivity)



theorem aux_lem_finite_stopping_partition_window_numerics {H1 N : ℕ} (hH1 : 0 < H1) {j : ℤ} (hNH : 4 * H1 ≤ N)
    (hNj : 4 * j.natAbs ≤ N) :
    ((aux_lem_finite_stopping_partition_obsT0 H1 N j : ℕ) : ℝ) + (H1 : ℝ) * (aux_lem_finite_stopping_partition_obsB H1 N : ℝ) =
        (H1 : ℝ) * (aux_lem_finite_stopping_partition_obsHi H1 N : ℝ) + (j : ℝ) ∧
      4 * ((H1 : ℝ) * (aux_lem_finite_stopping_partition_obsHi H1 N : ℝ)) ≤ 3 * (N : ℝ) ∧
      (aux_lem_finite_stopping_partition_obsB H1 N : ℝ) ≤ aux_lem_finite_stopping_partition_obsHi H1 N ∧
      (N : ℝ) / 2 - H1 ≤ (H1 : ℝ) * ((aux_lem_finite_stopping_partition_obsB H1 N : ℝ) + 1) := by
  have hlo := aux_lem_finite_stopping_partition_obsLo_le_obsHi hH1 hNH
  have ht0 := aux_lem_finite_stopping_partition_obsT0_eq hH1 (N := N) (j := j) hNj
  have hB : (aux_lem_finite_stopping_partition_obsB H1 N : ℝ) = (aux_lem_finite_stopping_partition_obsHi H1 N : ℝ) - (aux_lem_finite_stopping_partition_obsLo H1 N : ℝ) := by
    unfold aux_lem_finite_stopping_partition_obsB; rw [Nat.cast_sub hlo]
  have h1 := aux_lem_finite_stopping_partition_four_H1_obsHi_le hH1 N
  have h2 := aux_lem_finite_stopping_partition_four_H1_obsLo_le hH1 N
  have h3 := aux_lem_finite_stopping_partition_four_H1_obsHi_gt hH1 N
  have h1r : 4 * ((H1 : ℝ) * (aux_lem_finite_stopping_partition_obsHi H1 N : ℝ)) ≤ 3 * (N : ℝ) := by exact_mod_cast h1
  have h2r : 4 * ((H1 : ℝ) * (aux_lem_finite_stopping_partition_obsLo H1 N : ℝ)) ≤ (N : ℝ) + 4 * H1 := by exact_mod_cast h2
  have h3r : 3 * (N : ℝ) < 4 * ((H1 : ℝ) * (aux_lem_finite_stopping_partition_obsHi H1 N : ℝ)) + 4 * H1 := by exact_mod_cast h3
  have ht0r : ((aux_lem_finite_stopping_partition_obsT0 H1 N j : ℕ) : ℝ) = (H1 : ℝ) * (aux_lem_finite_stopping_partition_obsLo H1 N : ℝ) + (j : ℝ) := by
    have : (((aux_lem_finite_stopping_partition_obsT0 H1 N j : ℕ) : ℤ) : ℝ) = (((H1 * aux_lem_finite_stopping_partition_obsLo H1 N : ℕ) : ℤ) : ℝ) + (j : ℝ) := by
      rw [ht0]; push_cast; ring
    push_cast at this
    exact this
  refine ⟨?_, h1r, ?_, ?_⟩
  · rw [ht0r, hB]; ring
  · rw [hB]; have : (0 : ℝ) ≤ aux_lem_finite_stopping_partition_obsLo H1 N := Nat.cast_nonneg _; linarith
  · rw [hB]
    nlinarith

open Classical in
theorem aux_lem_finite_stopping_partition_nsel_lower {H1 N : ℕ} (hH1 : 0 < H1) (hNH : 4 * H1 ≤ N) (S : ℕ → Prop) (theta : ℝ)
    (hS : theta * (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) ≤
      (Nat.card {n : ℕ // S n ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ))
    (nsel : ℕ)
    (hnsel : ((Finset.univ : Finset (Fin (aux_lem_finite_stopping_partition_obsB H1 N))).filter
      (fun i => S (aux_lem_finite_stopping_partition_obsLo H1 N + (i.val + 1)))).card ≤ nsel) :
    theta * ((aux_lem_finite_stopping_partition_obsB H1 N : ℝ) + 1) ≤ (nsel : ℝ) + 1 := by
  have h1 := aux_lem_finite_stopping_partition_card_window hH1 hNH
  have h2 := aux_lem_finite_stopping_partition_card_selected_window_le hH1 N S
  rw [h1] at hS
  have h3 : (Nat.card {n : ℕ // S n ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) ≤
      (nsel : ℝ) + 1 := by exact_mod_cast h2.trans (Nat.add_le_add_right hnsel 1)
  push_cast at hS
  linarith

theorem aux_lem_finite_stopping_partition_final_side_rpow {H1 N : ℕ} (hH1 : 0 < H1) {j : ℤ} (hNH : 4 * H1 ≤ N)
    (hNj : 4 * j.natAbs ≤ N) :
    descendantSide (subdivisionHalfWidth H1) (aux_lem_finite_stopping_partition_obsB H1 N)
        (descendantSide 1 (aux_lem_finite_stopping_partition_obsT0 H1 N j) ((3 : ℝ) ^ j)) =
      (3 : ℝ) ^ (-((H1 : ℝ) * (aux_lem_finite_stopping_partition_obsHi H1 N : ℝ))) := by
  rw [aux_lem_finite_stopping_partition_stage_side_eq hH1 hNj]
  have hlo := aux_lem_finite_stopping_partition_obsLo_le_obsHi hH1 hNH
  have : aux_lem_finite_stopping_partition_obsLo H1 N + aux_lem_finite_stopping_partition_obsB H1 N = aux_lem_finite_stopping_partition_obsHi H1 N := by unfold aux_lem_finite_stopping_partition_obsB; omega
  rw [this, ← Real.rpow_intCast]
  push_cast
  ring_nf

/-- Final combination of the stopped budget and the residual remainder. -/
theorem aux_lem_finite_stopping_partition_final_combine (c Λ A LD fl rd RKc Cres g13 γ N φ2 CA CB : ℝ)
    (hc2 : c ≤ 2) (hA : 0 ≤ A) (hLD : 0 ≤ LD) (hrd : 0 ≤ rd) (hφ : 0 ≤ φ2)
    (hN : 0 ≤ N) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hCres : 0 ≤ Cres)
    (hfl : fl = (3 : ℝ) ^ (-N) * φ2) (hγ1 : γ ≤ 1) (hγ13 : γ ≤ g13)
    (hR : RKc ≤ Cres * (3 : ℝ) ^ (-(g13 * N)) * φ2) :
    c * Λ + A * c * LD * (Λ + fl * rd) + RKc ≤
      c * (1 + A * LD) * Λ +
        (CA + CB + 2 * A * LD * rd + Cres) * (3 : ℝ) ^ (-γ * N) * φ2 := by
  have h3N : (3 : ℝ) ^ (-N) ≤ (3 : ℝ) ^ (-γ * N) := aux_lem_finite_stopping_partition_rpow3_anti (by nlinarith)
  have h3g : (3 : ℝ) ^ (-(g13 * N)) ≤ (3 : ℝ) ^ (-γ * N) := aux_lem_finite_stopping_partition_rpow3_anti (by nlinarith)
  have hpos : 0 ≤ (3 : ℝ) ^ (-γ * N) := Real.rpow_nonneg (by norm_num) _
  have hpos2 : 0 ≤ (3 : ℝ) ^ (-N) := Real.rpow_nonneg (by norm_num) _
  have hstop : A * c * LD * (fl * rd) ≤ 2 * A * LD * rd * ((3 : ℝ) ^ (-γ * N) * φ2) := by
    rw [hfl]
    have hALr : 0 ≤ A * LD * rd := by positivity
    have h1 : c * ((3 : ℝ) ^ (-N) * φ2) ≤ 2 * ((3 : ℝ) ^ (-γ * N) * φ2) :=
      mul_le_mul hc2 (mul_le_mul_of_nonneg_right h3N hφ) (by positivity) (by norm_num)
    have := mul_le_mul_of_nonneg_left h1 hALr
    nlinarith
  have hres : RKc ≤ Cres * ((3 : ℝ) ^ (-γ * N) * φ2) := by
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3g hφ) hCres
    nlinarith
  have hrest : 0 ≤ (CA + CB) * ((3 : ℝ) ^ (-γ * N) * φ2) := by positivity
  nlinarith


theorem aux_lem_finite_stopping_partition_stage_sides_ok {H1 N : ℕ} (hH1 : 0 < H1) {j : ℤ} (hNH : 4 * H1 ≤ N)
    (hNj : 4 * j.natAbs ≤ N) (x : ℝ)
    (hx : ∃ s ≤ aux_lem_finite_stopping_partition_obsB H1 N, x = descendantSide (subdivisionHalfWidth H1) s
      (descendantSide 1 (aux_lem_finite_stopping_partition_obsT0 H1 N j) ((3 : ℝ) ^ j))) :
    (∃ j' : ℤ, x = (3 : ℝ) ^ j') ∧ (3 : ℝ) ^ (-(N : ℤ)) ≤ x := by
  obtain ⟨s, hs, rfl⟩ := hx
  rw [aux_lem_finite_stopping_partition_stage_side_eq hH1 hNj s]
  refine ⟨⟨_, rfl⟩, zpow_le_zpow_right₀ (by norm_num) ?_⟩
  have h1 := aux_lem_finite_stopping_partition_four_H1_obsHi_le hH1 N
  have h2 := aux_lem_finite_stopping_partition_obsLo_le_obsHi hH1 hNH
  have h3 : aux_lem_finite_stopping_partition_obsLo H1 N + s ≤ aux_lem_finite_stopping_partition_obsHi H1 N := by unfold aux_lem_finite_stopping_partition_obsB at hs; omega
  have h4 : H1 * (aux_lem_finite_stopping_partition_obsLo H1 N + s) ≤ H1 * aux_lem_finite_stopping_partition_obsHi H1 N := Nat.mul_le_mul_left _ h3
  have h5 : H1 * (aux_lem_finite_stopping_partition_obsLo H1 N + s) ≤ N := by omega
  have h6 : ((H1 * (aux_lem_finite_stopping_partition_obsLo H1 N + s) : ℕ) : ℤ) ≤ (N : ℤ) := by exact_mod_cast h5
  omega

/-- The regularized mass drops at most `g` times. -/
theorem aux_lem_finite_stopping_partition_aux_mass_budget {d : ℕ} (z : SpatialCoordinates d) (j : ℤ) (hr : 0 < (3 : ℝ) ^ j)
    (H1 : ℕ) (hH1 : 0 < H1) (N : ℕ) (hNH : 4 * H1 ≤ N) (hNj : 4 * j.natAbs ≤ N)
    (theta D : ℝ) (htheta : 0 < theta) (hD : 0 < D) (c2n : ℕ)
    (hc2n : 1 + ((3 : ℝ) ^ j) ^ d < (3 : ℝ) ^ c2n) (g : ℕ)
    (hg1 : ((theta / 64 + 1) * (N : ℝ) + (d : ℝ) * ((H1 : ℝ) * (aux_lem_finite_stopping_partition_obsHi H1 N : ℝ)) +
        (c2n : ℝ)) / ((H1 : ℝ) * D) ≤ g)
    (aS : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ j) hr))
    (u : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr)) (φ : ℝ) (hφ : 0 < φ)
    (hglob : aux_lem_finite_stopping_partition_energyOn aS u.val (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) ≤
      (3 : ℝ) ^ (theta / 64 * (N : ℝ)) * (φ * φ)) :
    aux_lem_finite_stopping_partition_massOn aS u.val ((3 : ℝ) ^ (-(N : ℝ)) * (φ * φ))
        (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) <
      (((3 : ℝ) ^ H1) ^ D) ^ (g + 1) * ((3 : ℝ) ^ (-(N : ℝ)) * (φ * φ) *
        (descendantSide (subdivisionHalfWidth H1) (aux_lem_finite_stopping_partition_obsB H1 N)
          (descendantSide 1 (aux_lem_finite_stopping_partition_obsT0 H1 N j) ((3 : ℝ) ^ j))) ^ d) := by
  have hH1D : 0 < (H1 : ℝ) * D := mul_pos (by exact_mod_cast hH1) hD
  have hmv : aux_lem_finite_stopping_partition_massOn aS u.val ((3 : ℝ) ^ (-(N : ℝ)) * (φ * φ))
      (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) =
      aux_lem_finite_stopping_partition_energyOn aS u.val (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) +
        (3 : ℝ) ^ (-(N : ℝ)) * (φ * φ) * ((3 : ℝ) ^ j) ^ d := by
    unfold aux_lem_finite_stopping_partition_massOn
    rw [centeredCube_volume_real]
  have hLDg : (((3 : ℝ) ^ H1) ^ D) ^ (g + 1) = (3 : ℝ) ^ ((H1 : ℝ) * D * ((g : ℝ) + 1)) := by
    rw [← Real.rpow_natCast (3 : ℝ) H1, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast _ (g + 1), ← Real.rpow_mul (by norm_num)]
    push_cast
    ring_nf
  have hsd : (descendantSide (subdivisionHalfWidth H1) (aux_lem_finite_stopping_partition_obsB H1 N)
      (descendantSide 1 (aux_lem_finite_stopping_partition_obsT0 H1 N j) ((3 : ℝ) ^ j))) ^ d =
      (3 : ℝ) ^ (-((d : ℝ) * ((H1 : ℝ) * (aux_lem_finite_stopping_partition_obsHi H1 N : ℝ)))) := by
    rw [aux_lem_finite_stopping_partition_final_side_rpow hH1 hNH hNj, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    ring_nf
  rw [hmv, hLDg, hsd]
  have hc2r : 1 + ((3 : ℝ) ^ j) ^ d ≤ (3 : ℝ) ^ (c2n : ℝ) := by
    rw [Real.rpow_natCast]
    exact hc2n.le
  have hXK : (theta / 64 + 1) * (N : ℝ) + (d : ℝ) * ((H1 : ℝ) * (aux_lem_finite_stopping_partition_obsHi H1 N : ℝ)) +
      (c2n : ℝ) < (H1 : ℝ) * D * ((g : ℝ) + 1) := by
    have h1 := (div_le_iff₀ hH1D).1 hg1
    nlinarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  exact aux_lem_finite_stopping_partition_mass_lt_drops _ _ _ (theta / 64) (N : ℝ) (c2n : ℝ) _ _ (mul_pos hφ hφ) hglob
    (by positivity) hc2r (by nlinarith) hXK

/-- The residual remainder is exponentially small. -/
theorem aux_lem_finite_stopping_partition_aux_remainder {d : ℕ} (hd : 2 ≤ d) (j : ℤ) (H1 : ℕ) (hH1 : 0 < H1) (P a0 : ℕ)
    (ha0 : d * (2 * P) ≤ 3 ^ a0) (h8a0 : 8 * a0 ≤ H1) (theta : ℝ) (htheta : 0 < theta)
    (hH1θ : 12 ≤ theta * (H1 : ℝ)) (D : ℝ) (hD : 0 < D)
    (hDθ : theta / 64 + 1 + 3 * (d : ℝ) / 4 ≤ theta * D / 16) (c2n : ℕ)
    (N : ℕ) (hNH : 4 * H1 ≤ N) (hNj : 4 * j.natAbs ≤ N)
    (nsel nbad g : ℕ) (hnselB : nsel ≤ aux_lem_finite_stopping_partition_obsB H1 N)
    (hnselθ : theta * ((aux_lem_finite_stopping_partition_obsB H1 N : ℝ) + 1) ≤ (nsel : ℝ) + 1)
    (hnb1 : (nbad : ℝ) ≤ theta / 16 * (N : ℝ) / (H1 : ℝ))
    (hg2 : (g : ℝ) < ((theta / 64 + 1) * (N : ℝ) + (d : ℝ) * ((H1 : ℝ) * (aux_lem_finite_stopping_partition_obsHi H1 N : ℝ)) +
          (c2n : ℝ)) / ((H1 : ℝ) * D) + 1)
    (NP R : ℕ)
    (hNP : NP ≤ d * (2 * P) * (2 * subdivisionHalfWidth H1 + 1) ^ (d - 1))
    (hR : R ≤ (3 ^ d) ^ aux_lem_finite_stopping_partition_obsT0 H1 N j * (2 ^ aux_lem_finite_stopping_partition_obsB H1 N * NP ^ (nsel - nbad - g) *
      ((2 * subdivisionHalfWidth H1 + 1) ^ d) ^ (aux_lem_finite_stopping_partition_obsB H1 N - (nsel - nbad - g))))
    (φ : ℝ) :
    (R : ℝ) * ((3 : ℝ) ^ (theta / 64 * (N : ℝ)) *
        (descendantSide (subdivisionHalfWidth H1) (aux_lem_finite_stopping_partition_obsB H1 N)
          (descendantSide 1 (aux_lem_finite_stopping_partition_obsT0 H1 N j) ((3 : ℝ) ^ j))) ^ ((d : ℝ) - theta / 16) *
        (φ * φ)) ≤
      (3 : ℝ) ^ ((d : ℝ) * (j : ℝ) + (7 / 8) * (theta * H1 + 2 * H1 + (c2n : ℝ) / D)) *
        (3 : ℝ) ^ (-(13 / 64 * theta * (N : ℝ))) * φ ^ 2 := by
  have hwin := aux_lem_finite_stopping_partition_window_numerics hH1 hNH hNj (j := j)
  obtain ⟨hwt0, hwn1, hwBn1, hwHB⟩ := hwin
  set T : ℕ := nsel - nbad - g with hT
  have hTB : T ≤ aux_lem_finite_stopping_partition_obsB H1 N := by omega
  have hNP' : NP ≤ 3 ^ a0 * (2 * subdivisionHalfWidth H1 + 1) ^ (d - 1) :=
    hNP.trans (Nat.mul_le_mul_right _ ha0)
  have hRE := hR.trans (aux_lem_finite_stopping_partition_rcount_le_pow d (aux_lem_finite_stopping_partition_obsT0 H1 N j) (aux_lem_finite_stopping_partition_obsB H1 N) T H1 a0 NP
    (subdivisionHalfWidth H1) (two_mul_subdivisionHalfWidth_add_one H1) hNP')
  have hd1 : 1 ≤ d := by omega
  have hEcast : ((d * aux_lem_finite_stopping_partition_obsT0 H1 N j + aux_lem_finite_stopping_partition_obsB H1 N + (a0 + H1 * (d - 1)) * T +
      H1 * d * (aux_lem_finite_stopping_partition_obsB H1 N - T) : ℕ) : ℝ) =
      (d : ℝ) * (aux_lem_finite_stopping_partition_obsT0 H1 N j : ℝ) + (aux_lem_finite_stopping_partition_obsB H1 N : ℝ) + (a0 : ℝ) * (T : ℝ) +
        (H1 : ℝ) * (d : ℝ) * (aux_lem_finite_stopping_partition_obsB H1 N : ℝ) - (H1 : ℝ) * (T : ℝ) := by
    push_cast [Nat.cast_sub hd1, Nat.cast_sub hTB]
    ring
  have hTge : (nsel : ℝ) - nbad - g ≤ (T : ℝ) := by
    have h : nsel ≤ T + nbad + g := by omega
    have h' : (nsel : ℝ) ≤ (T : ℝ) + nbad + g := by exact_mod_cast h
    linarith
  have hH1r : (1 : ℝ) ≤ H1 := by exact_mod_cast hH1
  have hbad : (H1 : ℝ) * nbad ≤ theta * N / 16 := by
    have h := mul_le_mul_of_nonneg_left hnb1 (by linarith : (0 : ℝ) ≤ H1)
    have e : (H1 : ℝ) * (theta / 16 * (N : ℝ) / (H1 : ℝ)) = theta * N / 16 := by
      field_simp
    linarith
  have hgH : (H1 : ℝ) * g ≤ ((theta / 64 + 1) * (N : ℝ) + (d : ℝ) * ((H1 : ℝ) * (aux_lem_finite_stopping_partition_obsHi H1 N : ℝ)) +
      (c2n : ℝ)) / D + H1 := by
    have h := mul_le_mul_of_nonneg_left hg2.le (by linarith : (0 : ℝ) ≤ H1)
    have e : (H1 : ℝ) * (((theta / 64 + 1) * (N : ℝ) + (d : ℝ) * ((H1 : ℝ) * (aux_lem_finite_stopping_partition_obsHi H1 N : ℝ)) +
        (c2n : ℝ)) / ((H1 : ℝ) * D) + 1) = ((theta / 64 + 1) * (N : ℝ) +
          (d : ℝ) * ((H1 : ℝ) * (aux_lem_finite_stopping_partition_obsHi H1 N : ℝ)) + (c2n : ℝ)) / D + H1 := by
      field_simp
    linarith
  have hexp := aux_lem_finite_stopping_partition_exponent_ineq theta H1 a0 (theta / 16) (theta / 64) D d N (aux_lem_finite_stopping_partition_obsHi H1 N) (aux_lem_finite_stopping_partition_obsB H1 N)
    T nsel nbad g c2n (aux_lem_finite_stopping_partition_obsT0 H1 N j) j htheta hH1r hH1θ (by exact_mod_cast h8a0) rfl rfl hD hDθ
    (Nat.cast_nonneg d) (Nat.cast_nonneg N) hwt0 hwn1 (Nat.cast_nonneg _) hwBn1 hnselθ hwHB hbad
    hgH hTge (Nat.cast_nonneg T)
  rw [← hEcast] at hexp
  rw [aux_lem_finite_stopping_partition_final_side_rpow hH1 hNH hNj]
  have hmain := aux_lem_finite_stopping_partition_remainder_le R _ hRE (theta / 64) N (theta / 16) d ((H1 : ℝ) * (aux_lem_finite_stopping_partition_obsHi H1 N : ℝ))
    (φ * φ) _ (mul_self_nonneg φ) hexp
  have hsplit : (3 : ℝ) ^ ((d : ℝ) * (j : ℝ) + 7 / 8 * (theta * H1 + 2 * H1 + (c2n : ℝ) / D) -
      13 / 64 * theta * (N : ℝ)) =
      (3 : ℝ) ^ ((d : ℝ) * (j : ℝ) + (7 / 8) * (theta * H1 + 2 * H1 + (c2n : ℝ) / D)) *
        (3 : ℝ) ^ (-(13 / 64 * theta * (N : ℝ))) := by
    rw [← Real.rpow_add (by norm_num)]
    ring_nf
  rw [hsplit] at hmain
  rw [sq]
  exact hmain

/-- Filter-count monotonicity with an arbitrary (unified, not synthesized) instance on the
right. -/
theorem aux_lem_finite_stopping_partition_card_filter_mono_inst {α : Type*} [Fintype α] (p q : α → Prop) [DecidablePred p]
    (instq : DecidablePred q) (h : ∀ a, p a → q a) :
    ((Finset.univ : Finset α).filter p).card ≤ (@Finset.filter α q instq Finset.univ).card :=
  Finset.card_le_card (fun a ha => by
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, h a ha.2⟩)

open Classical in
/-- The one-sample positive-datum step. -/
theorem aux_lem_finite_stopping_partition_omega_positive {d : ℕ} (hd : 2 ≤ d) [NeZero d] (z : SpatialCoordinates d) (j : ℤ)
    (hr : 0 < (3 : ℝ) ^ j)
    (H1 : ℕ) (hH1 : 0 < H1) (P a0 : ℕ) (ha0 : d * (2 * P) ≤ 3 ^ a0) (h8a0 : 8 * a0 ≤ H1)
    (theta : ℝ) (htheta : 0 < theta) (hH1θ : 12 ≤ theta * (H1 : ℝ)) (D : ℝ) (hD : 0 < D)
    (hDθ : theta / 64 + 1 + 3 * (d : ℝ) / 4 ≤ theta * D / 16)
    (Cg eta : ℝ) (hCg : 0 < Cg) (heta : 0 < eta) (c2n : ℕ)
    (hc2n : 1 + ((3 : ℝ) ^ j) ^ d < (3 : ℝ) ^ c2n)
    (CA CB γ : ℝ) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hγ1 : γ ≤ 1) (hγ13 : γ ≤ 13 / 64 * theta)
    (N : ℕ) (hNH : 4 * H1 ≤ N) (hNj : 4 * j.natAbs ≤ N)
    (c : ℝ) (hc : 0 < c) (hc2 : c ≤ 2) (S : ℕ → Prop)
    (hS : theta * (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) ≤
      (Nat.card {n : ℕ // S n ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ))
    (φ : ℝ) (hφ : 0 < φ)
    (ρ : ℕ → ℝ) (hρ0 : ∀ n, 0 ≤ ρ n)
    (hratio : ∀ n : ℕ, S n → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N → ρ n ≤ c)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr),
      ‖(v : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr)).1‖ ≤
        K * ‖@subspaceGradient d (centeredCube z ((3 : ℝ) ^ j) hr)
          (killedSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr)) v‖)
    (b : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr))
    (aT aS : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ j) hr))
    (u : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr))
    (hΛ : @dirichletResponse d _ (@killedResponseSpace d _ hP) aS b =
      aux_lem_finite_stopping_partition_energyOn aS u.val (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)))
    (Good : (Fin (aux_lem_finite_stopping_partition_obsT0 H1 N j) → OddGridIndex d 1) → (n : ℕ) →
      (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Prop)
    (hbranch : ∀ (w0 : Fin (aux_lem_finite_stopping_partition_obsT0 H1 N j) → OddGridIndex d 1)
      (w : Fin (aux_lem_finite_stopping_partition_obsB H1 N) → OddGridIndex d (subdivisionHalfWidth H1)),
      ((((Finset.univ : Finset (Fin (aux_lem_finite_stopping_partition_obsB H1 N))).filter fun i =>
        ¬ Good w0 (i.val + 1) (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt)).card : ℕ) : ℝ) ≤
          theta / 16 * (N : ℝ) / (H1 : ℝ))
    (hcomp : ∀ (w0 : Fin (aux_lem_finite_stopping_partition_obsT0 H1 N j) → OddGridIndex d 1) (s : ℕ)
      (w : Fin (s + 1) → OddGridIndex d (subdivisionHalfWidth H1)),
      s + 1 ≤ aux_lem_finite_stopping_partition_obsB H1 N → Good w0 (s + 1) w → aux_lem_finite_stopping_partition_padLabel P (w (Fin.last s)) →
      aux_lem_finite_stopping_partition_respOn aT u (aux_lem_finite_stopping_partition_cell2_le_root z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (s + 1) w)
          (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (s + 1) w) ≤
        ρ (aux_lem_finite_stopping_partition_obsLo H1 N + (s + 1)) *
            aux_lem_finite_stopping_partition_respOn aS u (aux_lem_finite_stopping_partition_cell2_le_root z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (s + 1) w)
              (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (s + 1) w) +
          Cg * eta * ρ (aux_lem_finite_stopping_partition_obsLo H1 N + (s + 1)) *
            aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_cell2 z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 s
              (fun i => w i.castSucc)))
    (hcrude : ∀ (w0 : Fin (aux_lem_finite_stopping_partition_obsT0 H1 N j) → OddGridIndex d 1)
      (w : Fin (aux_lem_finite_stopping_partition_obsB H1 N) → OddGridIndex d (subdivisionHalfWidth H1)),
      aux_lem_finite_stopping_partition_respOn aT u (aux_lem_finite_stopping_partition_cell2_le_root z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (aux_lem_finite_stopping_partition_obsB H1 N) w)
          (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (aux_lem_finite_stopping_partition_obsB H1 N) w) ≤
        (3 : ℝ) ^ (theta / 64 * (N : ℝ)) *
          (descendantSide (subdivisionHalfWidth H1) (aux_lem_finite_stopping_partition_obsB H1 N)
            (descendantSide 1 (aux_lem_finite_stopping_partition_obsT0 H1 N j) ((3 : ℝ) ^ j))) ^ ((d : ℝ) - theta / 16) *
          (φ * φ))
    (hglobal : @dirichletResponse d _ (@killedResponseSpace d _ hP) aS b ≤
      (3 : ℝ) ^ (theta / 64 * (N : ℝ)) * (φ * φ)) :
    ∃ (ncell : ℕ) (centers : Fin ncell → SpatialCoordinates d)
      (sides : Fin ncell → ℝ) (hside : ∀ i, 0 < sides i),
    let cell := fun i => centeredCube (centers i) (sides i) (hside i)
    ∃ hle : ∀ i, cell i ≤ centeredCube z ((3 : ℝ) ^ j) hr,
    (∀ i, (∃ j : ℤ, sides i = (3 : ℝ) ^ j) ∧
      (3 : ℝ) ^ (-(N : ℤ)) ≤ sides i) ∧
    Pairwise (fun i j => Disjoint (cell i : Set (SpatialCoordinates d))
      (cell j : Set (SpatialCoordinates d))) ∧
    ((⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume]
      (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d))) ∧
    ∃ hPcell : ∀ i, ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (cell i),
      ‖(v : SobolevData (cell i)).1‖ ≤
        K * ‖@subspaceGradient d (cell i) (killedSobolevGraph (cell i)) v‖,
    let bcell : ∀ i, weakSobolevGraph (cell i) := fun i =>
      ⟨sobolevDataRestrict (hle i) u.val, sobolevDataRestrict_mem_weak (hle i) u.property⟩
    (∑ i : Fin ncell,
      @dirichletResponse d (cell i) (@killedResponseSpace d (cell i) (hPcell i))
        (positiveCoefficientRestrict (hle i) aT) (bcell i)) ≤
      c * (1 + Cg * eta * ((3 : ℝ) ^ H1) ^ D) *
          @dirichletResponse d _ (@killedResponseSpace d _ hP) aS b +
        (CA + CB + 2 * (Cg * eta) * ((3 : ℝ) ^ H1) ^ D * ((3 : ℝ) ^ j) ^ d +
          (3 : ℝ) ^ ((d : ℝ) * (j : ℝ) + (7 / 8) * (theta * H1 + 2 * H1 + (c2n : ℝ) / D))) *
          (3 : ℝ) ^ (-γ * (N : ℝ)) * φ ^ 2 := by
  classical
  have hH1D : 0 < (H1 : ℝ) * D := mul_pos (by exact_mod_cast hH1) hD
  have hX0 : 0 ≤ (theta / 64 + 1) * (N : ℝ) + (d : ℝ) * ((H1 : ℝ) * (aux_lem_finite_stopping_partition_obsHi H1 N : ℝ)) +
      (c2n : ℝ) := by positivity
  have hgex : ∃ g : ℕ, ((theta / 64 + 1) * (N : ℝ) + (d : ℝ) * ((H1 : ℝ) * (aux_lem_finite_stopping_partition_obsHi H1 N : ℝ)) +
      (c2n : ℝ)) / ((H1 : ℝ) * D) ≤ g ∧ (g : ℝ) < ((theta / 64 + 1) * (N : ℝ) +
        (d : ℝ) * ((H1 : ℝ) * (aux_lem_finite_stopping_partition_obsHi H1 N : ℝ)) + (c2n : ℝ)) / ((H1 : ℝ) * D) + 1 :=
    ⟨_, Nat.le_ceil _, Nat.ceil_lt_add_one (div_nonneg hX0 hH1D.le)⟩
  obtain ⟨g, hg1, hg2⟩ := hgex
  have hnbex : ∃ nbad : ℕ, (nbad : ℝ) ≤ theta / 16 * (N : ℝ) / (H1 : ℝ) ∧
      ∀ m : ℕ, (m : ℝ) ≤ theta / 16 * (N : ℝ) / (H1 : ℝ) → m ≤ nbad :=
    ⟨_, Nat.floor_le (by positivity), fun m hm => Nat.le_floor hm⟩
  obtain ⟨nbad, hnb1, hnb2⟩ := hnbex
  have hnselex : ∃ nsel : ℕ, nsel = ((Finset.univ : Finset (Fin (aux_lem_finite_stopping_partition_obsB H1 N))).filter
      (fun i => S (aux_lem_finite_stopping_partition_obsLo H1 N + (i.val + 1)))).card := ⟨_, rfl⟩
  obtain ⟨nsel, hnsel⟩ := hnselex
  have hnselB : nsel ≤ aux_lem_finite_stopping_partition_obsB H1 N := by
    rw [hnsel]
    exact (Finset.card_le_univ _).trans (by simp)
  have hnselθ : theta * ((aux_lem_finite_stopping_partition_obsB H1 N : ℝ) + 1) ≤ (nsel : ℝ) + 1 :=
    aux_lem_finite_stopping_partition_nsel_lower hH1 hNH S theta hS nsel hnsel.ge
  have hglob : aux_lem_finite_stopping_partition_energyOn aS u.val (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) ≤
      (3 : ℝ) ^ (theta / 64 * (N : ℝ)) * (φ * φ) := hΛ ▸ hglobal
  have hmassQ := aux_lem_finite_stopping_partition_aux_mass_budget z j hr H1 hH1 N hNH hNj theta D htheta hD c2n hc2n g hg1 aS u
    φ hφ hglob
  have hL1 : (1 : ℝ) < (3 : ℝ) ^ H1 := one_lt_pow₀ (by norm_num) hH1.ne'
  have hLD1 : (1 : ℝ) < ((3 : ℝ) ^ H1) ^ D := Real.one_lt_rpow hL1 hD
  have hcell' : ∀ (w0 : Fin (aux_lem_finite_stopping_partition_obsT0 H1 N j) → OddGridIndex d 1) (s : ℕ)
      (w : Fin (s + 1) → OddGridIndex d (subdivisionHalfWidth H1)),
      s + 1 ≤ aux_lem_finite_stopping_partition_obsB H1 N →
      (S (aux_lem_finite_stopping_partition_obsLo H1 N + (s + 1)) ∧ 1 ≤ s + 1 ∧ s + 1 ≤ aux_lem_finite_stopping_partition_obsB H1 N) →
      Good w0 (s + 1) w → aux_lem_finite_stopping_partition_padLabel P (w (Fin.last s)) →
      aux_lem_finite_stopping_partition_respOn aT u (aux_lem_finite_stopping_partition_cell2_le_root z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (s + 1) w)
          (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (s + 1) w) ≤
        ρ (aux_lem_finite_stopping_partition_obsLo H1 N + (s + 1)) *
            aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_cell2 z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (s + 1) w) +
          Cg * eta * ρ (aux_lem_finite_stopping_partition_obsLo H1 N + (s + 1)) *
            aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_cell2 z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 s
              (fun i => w i.castSucc)) := by
    intro w0 s w hsB _ hG hPd
    have h1 := hcomp w0 s w hsB hG hPd
    have h2 : aux_lem_finite_stopping_partition_respOn aS u
          (aux_lem_finite_stopping_partition_cell2_le_root z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (s + 1) w)
          (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (s + 1) w) ≤
        aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_cell2 z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (s + 1) w) :=
      aux_lem_finite_stopping_partition_dirichletResponse_restrict_le_energyOn _ _ _ _
    have h3 := mul_le_mul_of_nonneg_left h2 (hρ0 (aux_lem_finite_stopping_partition_obsLo H1 N + (s + 1)))
    linarith
  have hρ' : ∀ s, (S (aux_lem_finite_stopping_partition_obsLo H1 N + s) ∧ 1 ≤ s ∧ s ≤ aux_lem_finite_stopping_partition_obsB H1 N) →
      0 ≤ ρ (aux_lem_finite_stopping_partition_obsLo H1 N + s) ∧ ρ (aux_lem_finite_stopping_partition_obsLo H1 N + s) ≤ c := by
    intro s hs
    refine ⟨hρ0 _, ?_⟩
    have hw1 : N ≤ 4 * (H1 * (aux_lem_finite_stopping_partition_obsLo H1 N + s)) :=
      (aux_lem_finite_stopping_partition_obsLo_le_iff hH1 N _).1 (Nat.le_add_right _ _)
    have hw2 : 4 * (H1 * (aux_lem_finite_stopping_partition_obsLo H1 N + s)) ≤ 3 * N := by
      apply (aux_lem_finite_stopping_partition_le_obsHi_iff hH1 N _).1
      have := hs.2.2
      unfold aux_lem_finite_stopping_partition_obsB at this
      omega
    exact hratio (aux_lem_finite_stopping_partition_obsLo H1 N + s) hs.1 hw1 hw2
  have hfl : (0 : ℝ) < (3 : ℝ) ^ (-(N : ℝ)) * (φ * φ) :=
    mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (mul_pos hφ hφ)
  have hcore := aux_lem_finite_stopping_partition_core_partition z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) (aux_lem_finite_stopping_partition_obsB H1 N) aT aS u
    ((3 : ℝ) ^ (-(N : ℝ)) * (φ * φ)) (((3 : ℝ) ^ H1) ^ D)
    (fun s => S (aux_lem_finite_stopping_partition_obsLo H1 N + s) ∧ 1 ≤ s ∧ s ≤ aux_lem_finite_stopping_partition_obsB H1 N) Good (aux_lem_finite_stopping_partition_padLabel P) hfl hLD1
    (Cg * eta) c _ (by positivity) hc.le (fun s => ρ (aux_lem_finite_stopping_partition_obsLo H1 N + s)) hρ' hcell' nsel nbad g
    (fun w0 w => hnb2 _ (by convert hbranch w0 w))
    (by
      rw [hnsel]
      exact aux_lem_finite_stopping_partition_card_filter_mono_inst _ _ _ (fun i hi => ⟨hi, by omega, by have := i.isLt; omega⟩))
    hmassQ hcrude
  obtain ⟨ncell, centers, sides, hside, hle, hsides, hdisj, hcov, hPcell, hsum⟩ := hcore
  refine ⟨ncell, centers, sides, hside, hle,
    fun i => aux_lem_finite_stopping_partition_stage_sides_ok hH1 hNH hNj _ (hsides i), hdisj, hcov, hPcell, ?_⟩
  intro bcell
  obtain ⟨R, hRle, hsum'⟩ := hsum
  refine le_trans hsum' ?_
  have hmv : aux_lem_finite_stopping_partition_massOn aS u.val ((3 : ℝ) ^ (-(N : ℝ)) * (φ * φ))
      (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) =
      aux_lem_finite_stopping_partition_energyOn aS u.val (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) +
        (3 : ℝ) ^ (-(N : ℝ)) * (φ * φ) * ((3 : ℝ) ^ j) ^ d := by
    unfold aux_lem_finite_stopping_partition_massOn
    rw [centeredCube_volume_real]
  rw [hmv, ← hΛ]
  have hRK := aux_lem_finite_stopping_partition_aux_remainder hd j H1 hH1 P a0 ha0 h8a0 theta htheta hH1θ D hD hDθ c2n N hNH hNj
    nsel nbad g hnselB hnselθ hnb1 hg2 _ R (by convert aux_lem_finite_stopping_partition_card_not_padLabel_le _ P) hRle φ
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  exact aux_lem_finite_stopping_partition_final_combine c _ (Cg * eta) (((3 : ℝ) ^ H1) ^ D) ((3 : ℝ) ^ (-(N : ℝ)) * (φ * φ))
    (((3 : ℝ) ^ j) ^ d) _ _ (13 / 64 * theta) γ N (φ ^ 2) CA CB hc2 (by positivity)
    (by positivity) (by positivity) (sq_nonneg φ) hN0 hCA hCB (by positivity) (by rw [sq])
    hγ1 hγ13 hRK

open Classical in
/-- The one-sample zero-datum step. -/
theorem aux_lem_finite_stopping_partition_omega_zero {d : ℕ} [NeZero d] (z : SpatialCoordinates d) (j : ℤ)
    (hr : 0 < (3 : ℝ) ^ j)
    (H1 : ℕ) (hH1 : 0 < H1) (P a0 : ℕ) (_ha0 : d * (2 * P) ≤ 3 ^ a0) (_h8a0 : 8 * a0 ≤ H1)
    (theta : ℝ) (_htheta : 0 < theta) (_hH1θ : 12 ≤ theta * (H1 : ℝ)) (D : ℝ) (hD : 0 < D)
    (_hDθ : theta / 64 + 1 + 3 * (d : ℝ) / 4 ≤ theta * D / 16)
    (Cg eta : ℝ) (hCg : 0 < Cg) (heta : 0 < eta) (c2n : ℕ)
    (_hc2n : 1 + ((3 : ℝ) ^ j) ^ d < (3 : ℝ) ^ c2n)
    (CA CB γ : ℝ) (_hCA : 0 ≤ CA) (_hCB : 0 ≤ CB) (_hγ1 : γ ≤ 1) (_hγ13 : γ ≤ 13 / 64 * theta)
    (N : ℕ) (hNH : 4 * H1 ≤ N) (hNj : 4 * j.natAbs ≤ N)
    (c : ℝ) (hc : 0 < c) (_hc2 : c ≤ 2) (S : ℕ → Prop)
    (_hS : theta * (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) ≤
      (Nat.card {n : ℕ // S n ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ))
    (φ : ℝ) (hφ : φ = 0)
    (ρ : ℕ → ℝ) (_hρ0 : ∀ n, 0 ≤ ρ n)
    (_hratio : ∀ n : ℕ, S n → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N → ρ n ≤ c)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr),
      ‖(v : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr)).1‖ ≤
        K * ‖@subspaceGradient d (centeredCube z ((3 : ℝ) ^ j) hr)
          (killedSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr)) v‖)
    (b : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr))
    (aT aS : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ j) hr))
    (u : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr))
    (hΛ : @dirichletResponse d _ (@killedResponseSpace d _ hP) aS b =
      aux_lem_finite_stopping_partition_energyOn aS u.val (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)))
    (Good : (Fin (aux_lem_finite_stopping_partition_obsT0 H1 N j) → OddGridIndex d 1) → (n : ℕ) →
      (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Prop)
    (_hbranch : ∀ (w0 : Fin (aux_lem_finite_stopping_partition_obsT0 H1 N j) → OddGridIndex d 1)
      (w : Fin (aux_lem_finite_stopping_partition_obsB H1 N) → OddGridIndex d (subdivisionHalfWidth H1)),
      ((((Finset.univ : Finset (Fin (aux_lem_finite_stopping_partition_obsB H1 N))).filter fun i =>
        ¬ Good w0 (i.val + 1) (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt)).card : ℕ) : ℝ) ≤
          theta / 16 * (N : ℝ) / (H1 : ℝ))
    (_hcomp : ∀ (w0 : Fin (aux_lem_finite_stopping_partition_obsT0 H1 N j) → OddGridIndex d 1) (s : ℕ)
      (w : Fin (s + 1) → OddGridIndex d (subdivisionHalfWidth H1)),
      s + 1 ≤ aux_lem_finite_stopping_partition_obsB H1 N → Good w0 (s + 1) w → aux_lem_finite_stopping_partition_padLabel P (w (Fin.last s)) →
      aux_lem_finite_stopping_partition_respOn aT u (aux_lem_finite_stopping_partition_cell2_le_root z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (s + 1) w)
          (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (s + 1) w) ≤
        ρ (aux_lem_finite_stopping_partition_obsLo H1 N + (s + 1)) *
            aux_lem_finite_stopping_partition_respOn aS u (aux_lem_finite_stopping_partition_cell2_le_root z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (s + 1) w)
              (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (s + 1) w) +
          Cg * eta * ρ (aux_lem_finite_stopping_partition_obsLo H1 N + (s + 1)) *
            aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_cell2 z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 s
              (fun i => w i.castSucc)))
    (hcrude : ∀ (w0 : Fin (aux_lem_finite_stopping_partition_obsT0 H1 N j) → OddGridIndex d 1)
      (w : Fin (aux_lem_finite_stopping_partition_obsB H1 N) → OddGridIndex d (subdivisionHalfWidth H1)),
      aux_lem_finite_stopping_partition_respOn aT u (aux_lem_finite_stopping_partition_cell2_le_root z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (aux_lem_finite_stopping_partition_obsB H1 N) w)
          (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (aux_lem_finite_stopping_partition_obsB H1 N) w) ≤
        (3 : ℝ) ^ (theta / 64 * (N : ℝ)) *
          (descendantSide (subdivisionHalfWidth H1) (aux_lem_finite_stopping_partition_obsB H1 N)
            (descendantSide 1 (aux_lem_finite_stopping_partition_obsT0 H1 N j) ((3 : ℝ) ^ j))) ^ ((d : ℝ) - theta / 16) *
          (φ * φ))
    (_hglobal : @dirichletResponse d _ (@killedResponseSpace d _ hP) aS b ≤
      (3 : ℝ) ^ (theta / 64 * (N : ℝ)) * (φ * φ)) :
    ∃ (ncell : ℕ) (centers : Fin ncell → SpatialCoordinates d)
      (sides : Fin ncell → ℝ) (hside : ∀ i, 0 < sides i),
    let cell := fun i => centeredCube (centers i) (sides i) (hside i)
    ∃ hle : ∀ i, cell i ≤ centeredCube z ((3 : ℝ) ^ j) hr,
    (∀ i, (∃ j : ℤ, sides i = (3 : ℝ) ^ j) ∧
      (3 : ℝ) ^ (-(N : ℤ)) ≤ sides i) ∧
    Pairwise (fun i j => Disjoint (cell i : Set (SpatialCoordinates d))
      (cell j : Set (SpatialCoordinates d))) ∧
    ((⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume]
      (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d))) ∧
    ∃ hPcell : ∀ i, ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (cell i),
      ‖(v : SobolevData (cell i)).1‖ ≤
        K * ‖@subspaceGradient d (cell i) (killedSobolevGraph (cell i)) v‖,
    let bcell : ∀ i, weakSobolevGraph (cell i) := fun i =>
      ⟨sobolevDataRestrict (hle i) u.val, sobolevDataRestrict_mem_weak (hle i) u.property⟩
    (∑ i : Fin ncell,
      @dirichletResponse d (cell i) (@killedResponseSpace d (cell i) (hPcell i))
        (positiveCoefficientRestrict (hle i) aT) (bcell i)) ≤
      c * (1 + Cg * eta * ((3 : ℝ) ^ H1) ^ D) *
          @dirichletResponse d _ (@killedResponseSpace d _ hP) aS b +
        (CA + CB + 2 * (Cg * eta) * ((3 : ℝ) ^ H1) ^ D * ((3 : ℝ) ^ j) ^ d +
          (3 : ℝ) ^ ((d : ℝ) * (j : ℝ) + (7 / 8) * (theta * H1 + 2 * H1 + (c2n : ℝ) / D))) *
          (3 : ℝ) ^ (-γ * (N : ℝ)) * φ ^ 2 := by
  classical
  have hL1 : (1 : ℝ) < (3 : ℝ) ^ H1 := one_lt_pow₀ (by norm_num) hH1.ne'
  have hLD1 : (1 : ℝ) < ((3 : ℝ) ^ H1) ^ D := Real.one_lt_rpow hL1 hD
  have hr0 : (0 : ℝ) < (3 : ℝ) ^ j := hr
  have hsd : 0 < (descendantSide (subdivisionHalfWidth H1) (aux_lem_finite_stopping_partition_obsB H1 N)
      (descendantSide 1 (aux_lem_finite_stopping_partition_obsT0 H1 N j) ((3 : ℝ) ^ j))) ^ d :=
    pow_pos (descendantSide_pos _ _ (descendantSide_pos _ _ hr0)) d
  have hmass' : ∃ g : ℕ, aux_lem_finite_stopping_partition_massOn aS u.val 1
      (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) /
        (descendantSide (subdivisionHalfWidth H1) (aux_lem_finite_stopping_partition_obsB H1 N)
          (descendantSide 1 (aux_lem_finite_stopping_partition_obsT0 H1 N j) ((3 : ℝ) ^ j))) ^ d < (((3 : ℝ) ^ H1) ^ D) ^ g :=
    pow_unbounded_of_one_lt _ hLD1
  obtain ⟨g, hg⟩ := hmass'
  have hmassQ : aux_lem_finite_stopping_partition_massOn aS u.val 1
      (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) <
      (((3 : ℝ) ^ H1) ^ D) ^ (g + 1) * (1 * (descendantSide (subdivisionHalfWidth H1) (aux_lem_finite_stopping_partition_obsB H1 N)
        (descendantSide 1 (aux_lem_finite_stopping_partition_obsT0 H1 N j) ((3 : ℝ) ^ j))) ^ d) := by
    rw [div_lt_iff₀ hsd] at hg
    rw [one_mul]
    calc _ < (((3 : ℝ) ^ H1) ^ D) ^ g * _ := hg
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hLD1.le (Nat.le_succ g)) hsd.le
  have hcore := aux_lem_finite_stopping_partition_core_partition z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) (aux_lem_finite_stopping_partition_obsB H1 N)
    aT aS u 1 (((3 : ℝ) ^ H1) ^ D) (fun _ => False) Good (aux_lem_finite_stopping_partition_padLabel P) one_pos hLD1 0 c 0
    le_rfl hc.le (fun _ => 0) (fun s h => h.elim) (fun w0 s w _ h => h.elim) 0 (aux_lem_finite_stopping_partition_obsB H1 N) g
    (fun w0 w => (Finset.card_le_univ _).trans (by simp)) (Nat.zero_le _) hmassQ
    (fun w0 w => by
      have h := hcrude w0 w
      rw [hφ, mul_zero, mul_zero] at h
      exact h)
  obtain ⟨ncell, centers, sides, hside, hle, hsides, hdisj, hcov, hPcell, hsum⟩ := hcore
  refine ⟨ncell, centers, sides, hside, hle,
    fun i => aux_lem_finite_stopping_partition_stage_sides_ok hH1 hNH hNj _ (hsides i), hdisj, hcov, hPcell, ?_⟩
  intro bcell
  obtain ⟨R, -, hsum'⟩ := hsum
  refine le_trans hsum' ?_
  rw [← hΛ, hφ]
  have hΛ0 : 0 ≤ @dirichletResponse d _ (@killedResponseSpace d _ hP) aS b :=
    dirichletResponse_nonneg _ _ _
  have hX : 0 ≤ Cg * eta * ((3 : ℝ) ^ H1) ^ D := by positivity
  have h1 : c * @dirichletResponse d _ (@killedResponseSpace d _ hP) aS b * 1 ≤
      c * @dirichletResponse d _ (@killedResponseSpace d _ hP) aS b *
        (1 + Cg * eta * ((3 : ℝ) ^ H1) ^ D) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hX) (mul_nonneg hc.le hΛ0)
  simp only [zero_mul, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow]
  linarith

open Classical in
/-- **Refined child A with the stated standing inputs** (the ChildA proposition with `in_responses`,
`in_6_16`, `in_iteration` after the model).  Not proved here. -/
def aux_lem_finite_stopping_partition_ChildAIn (d : ℕ) (hd : 2 ≤ d) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) : Prop :=
  haveI : NeZero d := ⟨by omega⟩
  ∃ P : ℕ, 1 ≤ P ∧
  ∀ θbad : ℝ, 0 < θbad → ∃ H1min : ℕ, ∀ H1 : ℕ, H1min ≤ H1 → 0 < H1 →
  ∃ Cg delta0 : ℝ, 0 < Cg ∧ 0 < delta0 ∧
  ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model)
    (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d model) (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d model Jc Sreg)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
    InfraredCharacterization model H → model.delta ≤ delta0 →
  ∀ (z : SpatialCoordinates d) (j : ℤ),
  ∀ eta : ℝ, 0 < eta → ∃ (C γ : ℝ) (N0 : ℕ), 0 < C ∧ 0 < γ ∧
  ∀ N M : ℕ, N0 ≤ N → N ≤ M → ∀ reverse : Bool,
  ∀ hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph
      (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j)),
    ‖(v : SobolevData (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j))).1‖ ≤
      K * ‖@subspaceGradient d (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j))
        (killedSobolevGraph (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j))) v‖,
  ∀ b : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ j) (zpow_pos (by norm_num) j)),
  ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
    (chaosSampleLaw model).toMeasure Bad ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-γ * (N : ℝ))) ∧
    ∀ omega ∉ Bad,
    let hr : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
    let target := if reverse then M else N
    let source := if reverse then N else M
    let aT := cutoffPositiveCoefficient model H omega target z hr
    let aS := cutoffPositiveCoefficient model H omega source z hr
    let u := @dirichletMinimizer d _ (@killedResponseSpace d _ hP) aS b
    let mg := subdivisionHalfWidth H1
    let t0 := aux_lem_finite_stopping_partition_obsT0 H1 N j
    let B := aux_lem_finite_stopping_partition_obsB H1 N
    ∃ Good : (Fin t0 → OddGridIndex d 1) → (n : ℕ) → (Fin n → OddGridIndex d mg) → Prop,
      (∀ (w0 : Fin t0 → OddGridIndex d 1) (w : Fin B → OddGridIndex d mg),
        ((((Finset.univ : Finset (Fin B)).filter fun i =>
          ¬ Good w0 (i.val + 1) (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt)).card : ℕ) : ℝ) ≤
            θbad * (N : ℝ) / (H1 : ℝ)) ∧
      (∀ (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin (s + 1) → OddGridIndex d mg),
        s + 1 ≤ B → Good w0 (s + 1) w → aux_lem_finite_stopping_partition_padLabel P (w (Fin.last s)) →
        aux_lem_finite_stopping_partition_respOn aT u (aux_lem_finite_stopping_partition_cell2_le_root z hr t0 mg w0 (s + 1) w)
            (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr t0 mg w0 (s + 1) w) ≤
          aux_lem_finite_stopping_partition_kappaRatio model H1 target source (aux_lem_finite_stopping_partition_obsLo H1 N + (s + 1)) *
              aux_lem_finite_stopping_partition_respOn aS u (aux_lem_finite_stopping_partition_cell2_le_root z hr t0 mg w0 (s + 1) w)
                (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr t0 mg w0 (s + 1) w) +
            Cg * eta * aux_lem_finite_stopping_partition_kappaRatio model H1 target source (aux_lem_finite_stopping_partition_obsLo H1 N + (s + 1)) *
              aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 s (fun i => w i.castSucc)))


theorem aux_lem_finite_stopping_partition_lem_finite_stopping_partition_of_children_in
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) (_Pc : _root_.SubdiffusiveProcess.Paper.in_poincare d hd Jc) (_Xc : _root_.SubdiffusiveProcess.Paper.in_extension d hd Jc)
    (_Sf : SobolevFoundationalInput d hd) (_W : SmallPerturbationInput d) (_Cp : CampanatoInput d)
    (_Step : @_root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d ⟨by omega⟩)
    (hA : aux_lem_finite_stopping_partition_ChildAIn d hd Jc) (hB : _root_.SubdiffusiveProcess.Paper.aux_lem_finite_stopping_crude_cost_ChildBIn d hd Jc)
    (theta : ℝ) (htheta : 0 < theta) :
    ∃ (H1 : ℕ) (Dgeom Cgeom delta0 : ℝ),
      0 < H1 ∧ 0 < Dgeom ∧ 0 < Cgeom ∧ 0 < delta0 ∧
      let L : ℝ := (3 : ℝ) ^ H1
      ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model)
        (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d model) (It : _root_.SubdiffusiveProcess.Paper.in_iteration d model Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hH : InfraredCharacterization model H) (hsmall : model.delta ≤ delta0)
        (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (htriadic : ∃ j : ℤ, r = (3 : ℝ) ^ j),
      let Q := centeredCube z r hr
      let closedQ := closedCube z r hr
      ∀ (eta : ℝ), 0 < eta →
      ∃ (Ceta gamma : ℝ) (N0 : ℕ), 0 < Ceta ∧ 0 < gamma ∧
      ∀ (N M : ℕ), N0 ≤ N → N ≤ M →
      ∀ (c : ℝ), 0 < c → c ≤ 2 →
      ∀ (S : ℕ → Prop),
        theta * (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) ≤
          (Nat.card {n : ℕ // S n ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) →
      let kappa := fun J : ℕ =>
        Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
      ∀ reverse : Bool,
      let target := if reverse then M else N
      let source := if reverse then N else M
      (∀ n : ℕ, S n → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N →
        (kappa (target - H1 * n) / kappa target) /
          (kappa (source - H1 * n) / kappa source) ≤ c) →
      ∀ hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
        ‖(u : SobolevData Q).1‖ ≤ K * ‖@subspaceGradient d Q (killedSobolevGraph Q) u‖,
      ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ phi →
      ∀ b : weakSobolevGraph Q,
        ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] phi →
      ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
        (chaosSampleLaw model).toMeasure Bad ≤
          ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) ∧
        ∀ omega ∉ Bad,
        let aTarget := cutoffPositiveCoefficient model H omega target z hr
        let aSource := cutoffPositiveCoefficient model H omega source z hr
        let u := @dirichletMinimizer d Q (@killedResponseSpace d Q hP) aSource b
        ∃ (ncell : ℕ) (centers : Fin ncell → SpatialCoordinates d)
          (sides : Fin ncell → ℝ) (hside : ∀ i, 0 < sides i),
        let cell := fun i => centeredCube (centers i) (sides i) (hside i)
        ∃ hle : ∀ i, cell i ≤ Q,
        (∀ i, (∃ j : ℤ, sides i = (3 : ℝ) ^ j) ∧
          (3 : ℝ) ^ (-(N : ℤ)) ≤ sides i) ∧
        Pairwise (fun i j => Disjoint (cell i : Set (SpatialCoordinates d))
          (cell j : Set (SpatialCoordinates d))) ∧
        ((⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume]
          (Q : Set (SpatialCoordinates d))) ∧
        ∃ hPcell : ∀ i, ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (cell i),
          ‖(v : SobolevData (cell i)).1‖ ≤
            K * ‖@subspaceGradient d (cell i) (killedSobolevGraph (cell i)) v‖,
        let bcell : ∀ i, weakSobolevGraph (cell i) := fun i =>
          ⟨sobolevDataRestrict (hle i) u.val, sobolevDataRestrict_mem_weak (hle i) u.property⟩
        (∑ i : Fin ncell,
          @dirichletResponse d (cell i) (@killedResponseSpace d (cell i) (hPcell i))
            (positiveCoefficientRestrict (hle i) aTarget) (bcell i)) ≤
          c * (1 + Cgeom * eta * L ^ Dgeom) *
            @dirichletResponse d Q (@killedResponseSpace d Q hP) aSource b +
          Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) * (c2Norm closedQ phi) ^ 2     := by
  have : NeZero d := ⟨by omega⟩
  unfold aux_lem_finite_stopping_partition_ChildAIn at hA
  unfold _root_.SubdiffusiveProcess.Paper.aux_lem_finite_stopping_crude_cost_ChildBIn at hB
  obtain ⟨P, hP1, hA1⟩ := hA
  have hA1' := hA1 (theta / 16) (by positivity)
  clear hA1
  obtain ⟨H1min, hA2⟩ := hA1'
  have hB' := hB (theta / 16) (by positivity)
  clear hB
  obtain ⟨delta0B, hδB, hB1⟩ := hB'
  have hHθ' : ∃ n : ℕ, 12 / theta ≤ (n : ℝ) := exists_nat_ge _
  obtain ⟨Hθ, hHθ⟩ := hHθ'
  have ha0' : ∃ a0 : ℕ, d * (2 * P) ≤ 3 ^ a0 := ⟨_, (Nat.lt_pow_self (by norm_num)).le⟩
  obtain ⟨a0, ha0⟩ := ha0'
  have hH1' : ∃ H1 : ℕ, 0 < H1 ∧ H1min ≤ H1 ∧ 8 * a0 ≤ H1 ∧ Hθ ≤ H1 :=
    ⟨max (max H1min 1) (max (8 * a0) Hθ), by omega, by omega, by omega, by omega⟩
  obtain ⟨H1, hH1pos, hH1min, h8a0, hHθH1⟩ := hH1'
  have hH1θ : 12 ≤ theta * (H1 : ℝ) := by
    have h1 : (Hθ : ℝ) ≤ H1 := by exact_mod_cast hHθH1
    have h2 : 12 / theta * theta = 12 := div_mul_cancel₀ _ htheta.ne'
    nlinarith
  have hA2' := hA2 H1 hH1min hH1pos
  clear hA2
  obtain ⟨Cg, delta0A, hCg, hδA, hA3⟩ := hA2'
  have hD' : ∃ D : ℝ, 0 < D ∧ theta / 64 + 1 + 3 * (d : ℝ) / 4 ≤ theta * D / 16 := by
    refine ⟨16 * (theta / 64 + 1 + 3 * (d : ℝ) / 4) / theta + 1, by positivity, ?_⟩
    have h : theta * (16 * (theta / 64 + 1 + 3 * (d : ℝ) / 4) / theta + 1) / 16 =
        (theta / 64 + 1 + 3 * (d : ℝ) / 4) + theta / 16 := by
      field_simp
    rw [h]
    linarith
  obtain ⟨D, hD, hDθ⟩ := hD'
  refine ⟨H1, D, Cg, min delta0A delta0B, hH1pos, hD, hCg, lt_min hδA hδB, ?_⟩
  intro L model Rm Sreg It H hH hsmall z r hr htriadic
  obtain ⟨j, rfl⟩ := htriadic
  intro Q closedQ eta heta
  have hA4' := hA3 model Rm Sreg It H hH (hsmall.trans (min_le_left _ _)) z j eta heta
  clear hA3
  obtain ⟨CA, γA, N0A, hCA, hγA, hA4⟩ := hA4'
  have hB4' := hB1 model Rm Sreg It H hH (hsmall.trans (min_le_right _ _)) z j H1 hH1pos (theta / 64)
    (by positivity)
  clear hB1
  obtain ⟨CB, γB, N0B, hCB, hγB, hB4⟩ := hB4'
  have hc2' : ∃ c2n : ℕ, 1 + ((3 : ℝ) ^ j) ^ d < (3 : ℝ) ^ c2n :=
    pow_unbounded_of_one_lt _ (by norm_num)
  obtain ⟨c2n, hc2n⟩ := hc2'
  have hLdef : L = (3 : ℝ) ^ H1 := rfl
  have hLpos : (0 : ℝ) < L := by rw [hLdef]; positivity
  have hLD0 : (0 : ℝ) ≤ L ^ D := Real.rpow_nonneg hLpos.le D
  have hr0 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  refine ⟨CA + CB + 2 * (Cg * eta) * L ^ D * ((3 : ℝ) ^ j) ^ d +
      (3 : ℝ) ^ ((d : ℝ) * (j : ℝ) + (7 / 8) * (theta * H1 + 2 * H1 + (c2n : ℝ) / D)),
    min (min γA γB) (min 1 (13 / 64 * theta)),
    max (max N0A N0B) (max (4 * H1) (4 * j.natAbs)), ?_, ?_, ?_⟩
  · have : 0 ≤ 2 * (Cg * eta) * L ^ D * ((3 : ℝ) ^ j) ^ d := by positivity
    have : 0 < (3 : ℝ) ^ ((d : ℝ) * (j : ℝ) + (7 / 8) * (theta * H1 + 2 * H1 + (c2n : ℝ) / D)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    linarith
  · exact lt_min (lt_min hγA hγB) (lt_min one_pos (by positivity))
  intro N M hN hNM c hc hc2 S hS kappa reverse target source hratio hP phi hphi b hb
  have hNA : N0A ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNB : N0B ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNH : 4 * H1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNj : 4 * j.natAbs ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hA5' := hA4 N M hNA hNM reverse hP b
  clear hA4
  obtain ⟨BadA, hBadA, hPA, hA5⟩ := hA5'
  have hB5' := hB4 N M hNB hNM reverse hP phi hphi b hb
  clear hB4
  obtain ⟨BadB, hBadB, hPB, hB5⟩ := hB5'
  refine ⟨BadA ∪ BadB, hBadA.union hBadB, ?_, ?_⟩
  · apply aux_lem_finite_stopping_partition_prob_union_le _ _ _ CA CB γA γB _ _ _ hCA.le hCB.le
      ((min_le_left _ _).trans (min_le_left _ _)) ((min_le_left _ _).trans (min_le_right _ _))
      (Nat.cast_nonneg N) _ hPA hPB
    have : 0 ≤ 2 * (Cg * eta) * L ^ D * ((3 : ℝ) ^ j) ^ d := by positivity
    have : 0 < (3 : ℝ) ^ ((d : ℝ) * (j : ℝ) + (7 / 8) * (theta * H1 + 2 * H1 + (c2n : ℝ) / D)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    linarith
  intro omega homega
  have hωA : omega ∉ BadA := fun h => homega (Or.inl h)
  have hωB : omega ∉ BadB := fun h => homega (Or.inr h)
  have hA6 := hA5 omega hωA
  have hB6 := hB5 omega hωB
  clear hA5 hB5
  obtain ⟨Good, hbranch, hcomp⟩ := hA6
  obtain ⟨hcrude, hglobal⟩ := hB6
  intro aTarget aSource u
  have hΛ : @dirichletResponse d _ (@killedResponseSpace d _ hP) aSource b =
      aux_lem_finite_stopping_partition_energyOn aSource u.val (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) :=
    aux_lem_finite_stopping_partition_dirichletResponse_eq_energyOn _ _ _
  have hφ0 : 0 ≤ c2Norm (closedQ : Set (SpatialCoordinates d)) phi := aux_lem_finite_stopping_partition_c2Norm_nonneg _ _
  have hγ1 : min (min γA γB) (min 1 (13 / 64 * theta)) ≤ 1 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hγ13 : min (min γA γB) (min 1 (13 / 64 * theta)) ≤ 13 / 64 * theta :=
    (min_le_right _ _).trans (min_le_right _ _)
  by_cases hφ : c2Norm (closedQ : Set (SpatialCoordinates d)) phi = 0
  · exact aux_lem_finite_stopping_partition_omega_zero z j hr H1 hH1pos P a0 ha0 h8a0 theta htheta hH1θ D hD hDθ Cg eta hCg heta
      c2n hc2n CA CB _ hCA.le hCB.le hγ1 hγ13 N hNH hNj c hc hc2 S hS
      (c2Norm (closedQ : Set (SpatialCoordinates d)) phi) hφ
      (fun n => aux_lem_finite_stopping_partition_kappaRatio model H1 target source n) (fun n => aux_lem_finite_stopping_partition_kappaRatio_nonneg _ _ _ _ _)
      hratio hP b aTarget aSource u hΛ Good hbranch hcomp hcrude hglobal
  · exact aux_lem_finite_stopping_partition_omega_positive hd z j hr H1 hH1pos P a0 ha0 h8a0 theta htheta hH1θ D hD hDθ Cg eta hCg
      heta c2n hc2n CA CB _ hCA.le hCB.le hγ1 hγ13 N hNH hNj c hc hc2 S hS
      (c2Norm (closedQ : Set (SpatialCoordinates d)) phi) (lt_of_le_of_ne hφ0 (Ne.symm hφ))
      (fun n => aux_lem_finite_stopping_partition_kappaRatio model H1 target source n) (fun n => aux_lem_finite_stopping_partition_kappaRatio_nonneg _ _ _ _ _)
      hratio hP b aTarget aSource u hΛ Good hbranch hcomp hcrude hglobal





theorem lem_finite_stopping_partition
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : SobolevFoundationalInput d hd) (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Step : @cutoff_good_scale_input d ⟨by omega⟩)
    (D : @deterministic_good_scale_input d ⟨by omega⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Dbase : @sum_errors_baseline_input d ⟨by omega⟩ _ _)
    (theta : ℝ) (htheta : 0 < theta) :
    ∃ (H1 : ℕ) (Dgeom Cgeom delta0 : ℝ),
      0 < H1 ∧ 0 < Dgeom ∧ 0 < Cgeom ∧ 0 < delta0 ∧
      let L : ℝ := (3 : ℝ) ^ H1
      ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d model)
        (Sreg : in_6_16 d model) (It : in_iteration d model Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hH : InfraredCharacterization model H) (hsmall : model.delta ≤ delta0)
        (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (htriadic : ∃ j : ℤ, r = (3 : ℝ) ^ j),
      let Q := centeredCube z r hr
      let closedQ := closedCube z r hr
      ∀ (eta : ℝ), 0 < eta →
      ∃ (Ceta gamma : ℝ) (N0 : ℕ), 0 < Ceta ∧ 0 < gamma ∧
      ∀ (N M : ℕ), N0 ≤ N → N ≤ M →
      ∀ (c : ℝ), 0 < c → c ≤ 2 →
      ∀ (S : ℕ → Prop),
        theta * (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) ≤
          (Nat.card {n : ℕ // S n ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) →
      let kappa := fun J : ℕ =>
        Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
      ∀ reverse : Bool,
      let target := if reverse then M else N
      let source := if reverse then N else M
      (∀ n : ℕ, S n → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N →
        (kappa (target - H1 * n) / kappa target) /
          (kappa (source - H1 * n) / kappa source) ≤ c) →
      ∀ hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
        ‖(u : SobolevData Q).1‖ ≤ K * ‖@subspaceGradient d Q (killedSobolevGraph Q) u‖,
      ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ phi →
      ∀ b : weakSobolevGraph Q,
        ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] phi →
      ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
        (chaosSampleLaw model).toMeasure Bad ≤
          ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) ∧
        ∀ omega ∉ Bad,
        let aTarget := cutoffPositiveCoefficient model H omega target z hr
        let aSource := cutoffPositiveCoefficient model H omega source z hr
        let u := @dirichletMinimizer d Q (@killedResponseSpace d Q hP) aSource b
        ∃ (ncell : ℕ) (centers : Fin ncell → SpatialCoordinates d)
          (sides : Fin ncell → ℝ) (hside : ∀ i, 0 < sides i),
        let cell := fun i => centeredCube (centers i) (sides i) (hside i)
        ∃ hle : ∀ i, cell i ≤ Q,
        (∀ i, (∃ j : ℤ, sides i = (3 : ℝ) ^ j) ∧
          (3 : ℝ) ^ (-(N : ℤ)) ≤ sides i) ∧
        Pairwise (fun i j => Disjoint (cell i : Set (SpatialCoordinates d))
          (cell j : Set (SpatialCoordinates d))) ∧
        ((⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume]
          (Q : Set (SpatialCoordinates d))) ∧
        ∃ hPcell : ∀ i, ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (cell i),
          ‖(v : SobolevData (cell i)).1‖ ≤
            K * ‖@subspaceGradient d (cell i) (killedSobolevGraph (cell i)) v‖,
        let bcell : ∀ i, weakSobolevGraph (cell i) := fun i =>
          ⟨sobolevDataRestrict (hle i) u.val, sobolevDataRestrict_mem_weak (hle i) u.property⟩
        (∑ i : Fin ncell,
          @dirichletResponse d (cell i) (@killedResponseSpace d (cell i) (hPcell i))
            (positiveCoefficientRestrict (hle i) aTarget) (bcell i)) ≤
          c * (1 + Cgeom * eta * L ^ Dgeom) *
            @dirichletResponse d Q (@killedResponseSpace d Q hP) aSource b +
          Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) * (c2Norm closedQ phi) ^ 2 :=
  aux_lem_finite_stopping_partition_lem_finite_stopping_partition_of_children_in
    d hd Jc Pc Xc Sf W Cp Step
    (_root_.SubdiffusiveProcess.Paper.lem_finite_stopping_good_steps d hd Jc Pc Xc Sf W Cp Step D hES Dbase)
    (_root_.SubdiffusiveProcess.Paper.lem_finite_stopping_crude_cost d hd Jc Pc Xc Sf W Cp)
    theta htheta

end SubdiffusiveProcess.Paper
