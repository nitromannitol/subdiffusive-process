import SubdiffusiveProcess.Paper.density_residual_hits
import SubdiffusiveProcess.Paper.density_residual_card
open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
open Classical

/-- A residual leaf is identified with its full-depth word. -/
theorem aux_density_stopping_cost_residual_card
    (d m J : ℕ) (stop : (n : ℕ) → (Fin n → OddGridIndex d m) → Prop)
    (Pad : OddGridIndex d m → Prop) (eta : ℝ)
    (hhits : ∀ w : Fin J → OddGridIndex d m,
      (∀ (k : ℕ) (hk : k ≤ J), ¬ stop k (aux_lem_finite_stopping_partition_wordPrefix w k hk)) →
      (eta / 3) * (J : ℝ) ≤
        (((Finset.univ : Finset (Fin J)).filter fun i => ¬ Pad (w i)).card : ℝ)) :
    ((aux_lem_finite_stopping_partition_leafFinset stop J).filter (fun p => ¬ stop p.1 p.2)).card ≤
      ((Finset.univ : Finset (Fin J → OddGridIndex d m)).filter (fun w =>
        (eta / 3) * (J : ℝ) ≤
          (((Finset.univ : Finset (Fin J)).filter fun i => ¬ Pad (w i)).card : ℝ))).card := by
  let Hs := (Finset.univ : Finset (Fin J → OddGridIndex d m)).filter (fun w =>
    (eta / 3) * (J : ℝ) ≤ (((Finset.univ : Finset (Fin J)).filter fun i => ¬ Pad (w i)).card : ℝ))
  let inject : (Fin J → OddGridIndex d m) → Σ n : Fin (J + 1), Fin n → OddGridIndex d m :=
    fun w => ⟨⟨J, Nat.lt_succ_self J⟩, w⟩
  have hsub : (aux_lem_finite_stopping_partition_leafFinset stop J).filter (fun p => ¬ stop p.1 p.2) ⊆ Hs.image inject := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp, hnstop⟩
    have hleaf := (aux_lem_finite_stopping_partition_mem_leafFinset stop J p).mp hp
    rcases p with ⟨⟨s, hs⟩, w⟩
    have hsJ : s = J := hleaf.2.1.resolve_left hnstop
    subst s
    apply Finset.mem_image.mpr
    refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhits w ?_⟩, rfl⟩
    intro k hk
    rcases lt_or_eq_of_le hk with hlt | rfl
    · exact hleaf.2.2 k hlt
    · simpa only [aux_lem_finite_stopping_partition_wordPrefix_self] using hnstop
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- The residual-count exponent is smaller than the local crude-cost exponent. -/
theorem aux_density_stopping_cost_decay
    (L r K dim eta s : ℝ) (hL : 1 < L) (hr : 0 < r) (hs : dim - eta / 8 < s) :
    Tendsto (fun J : ℕ => L ^ ((dim - eta / 8) * (J : ℝ)) *
      (K * (r / L ^ J) ^ s)) atTop (𝓝 0) := by
  have hL0 : 0 < L := zero_lt_one.trans hL
  have hbase0 : 0 ≤ L ^ (dim - eta / 8 - s) := Real.rpow_nonneg hL0.le _
  have hbase1 : L ^ (dim - eta / 8 - s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hL (by linarith)
  have hpow : Tendsto (fun J : ℕ => (L ^ (dim - eta / 8 - s)) ^ J) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase0 hbase1
  have heq : ∀ J : ℕ, L ^ ((dim - eta / 8) * (J : ℝ)) * (K * (r / L ^ J) ^ s) =
      (K * r ^ s) * (L ^ (dim - eta / 8 - s)) ^ J := by
    intro J
    rw [Real.div_rpow hr.le (pow_nonneg hL0.le _),
      Real.rpow_mul_natCast hL0.le, ← Real.rpow_natCast L J,
      ← Real.rpow_mul hL0.le, mul_comm (J : ℝ) s,
      Real.rpow_mul_natCast hL0.le,
      Real.rpow_sub hL0 (dim - eta / 8) s, div_pow]
    ring
  simpa only [← heq, mul_zero] using hpow.const_mul (K * r ^ s)

/-- Quantitative finite stopping cost for the literal regularized measure.
The two local cost estimates are explicit inputs to this deterministic step;
the model application must supply them from good extension and the crude bound. -/
theorem density_stopping_cost
    (d m : ℕ) (hm : 0 < m) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (nu : Measure (SpatialCoordinates d)) [IsFiniteMeasure nu]
    (c D eta theta Bbad Cd s C K : ℝ)
    (hc : 0 < c) (hD : 0 < D) (heta : 0 < eta) (heta3 : eta ≤ 3)
    (hDim : (d : ℝ) / D ≤ eta / 8) (htheta : theta ≤ eta / 8)
    (hCd : 0 < Cd) (hs : (d : ℝ) - eta / 8 < s) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (S : ℕ → Prop) (hS : eta ≤ upperDensity S) (base : ℕ)
    (Good : (n : ℕ) → (Fin n → OddGridIndex d m) → Prop)
    (Pad : OddGridIndex d m → Prop)
    (hbad : ∀ (J : ℕ) (w : Fin J → OddGridIndex d m),
      (((Finset.univ : Finset (Fin J)).filter fun i =>
        ¬ Good (i.val + 1) (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt)).card : ℝ) ≤
          theta * (J : ℝ) + Bbad) :
    let mu := nu + ENNReal.ofReal c • volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))
    let mass := fun n w => mu.real (descendantCell m z hr n w : Set (SpatialCoordinates d))
    let L : ℝ := 2 * (m : ℝ) + 1
    let stop := aux_lem_finite_stopping_partition_stopRule (fun n => S (base + n)) Good Pad mass (L ^ D)
    (((Finset.univ : Finset (OddGridIndex d m)).filter fun l => ¬ Pad l).card : ℝ) ≤
      Cd * L ^ ((d : ℝ) - 1) →
    2 * Cd ^ (eta / 3) ≤ L ^ (eta / 3 - eta / 8) →
    ∀ cost : (n : ℕ) → (Fin n → OddGridIndex d m) → ℝ,
      (∀ n w, stop n w → cost n w ≤ C * mass n w) →
      (∀ n w, cost n w ≤ K * (descendantSide m n r) ^ s) →
    ∀ eps : ℝ, 0 < eps → ∃ᶠ J : ℕ in atTop,
      (∑ p ∈ aux_lem_finite_stopping_partition_leafFinset stop J, cost p.1 p.2) ≤
        C * mu.real (centeredCube z r hr : Set (SpatialCoordinates d)) + eps := by
  intro mu mass L stop hNP hLarge cost hstopCost hcrude eps heps
  obtain ⟨hfinite, _hmono, _hfloor⟩ := aux_density_stopping_measure_properties d m z r hr nu c hc
  letI : IsFiniteMeasure mu := hfinite
  have hL : 1 < L := by dsimp [L]; exact_mod_cast (by omega : 1 < 2 * m + 1)
  have hL0 : 0 < L := zero_lt_one.trans hL
  have hfreq := density_residual_hits d m hm z r hr nu c D eta theta Bbad hc hD heta hDim htheta
    S hS base Good Pad hbad
  have hdecay := aux_density_stopping_cost_decay L r K (d : ℝ) eta s hL hr hs
  have hevent : ∀ᶠ J : ℕ in atTop,
      L ^ (((d : ℝ) - eta / 8) * (J : ℝ)) * (K * (r / L ^ J) ^ s) ≤ eps :=
    (hdecay.eventually (gt_mem_nhds heps)).mono (fun _ h => h.le)
  apply (hfreq.and_eventually hevent).mono
  intro J hJ
  rcases hJ with ⟨hhits, hepsJ⟩
  let leaves := aux_lem_finite_stopping_partition_leafFinset stop J
  let stopped := leaves.filter (fun p => stop p.1 p.2)
  let residual := leaves.filter (fun p => ¬ stop p.1 p.2)
  have hcount : (residual.card : ℝ) ≤ L ^ (((d : ℝ) - eta / 8) * (J : ℝ)) := by
    have h1 := aux_density_stopping_cost_residual_card d m J stop Pad eta hhits
    have h2 := density_residual_card (OddGridIndex d m)
      (Finset.univ.filter fun l => ¬ Pad l) L Cd (d : ℝ) eta hL hCd heta heta3
      (by simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_add, Nat.cast_mul,
            Nat.cast_ofNat, Nat.cast_one, Real.rpow_natCast]; exact le_rfl) hNP hLarge J
    have h1r := (Nat.cast_le (α := ℝ)).mpr h1
    exact h1r.trans (by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h2)
  have hsumMass : (∑ p ∈ stopped, mass p.1 p.2) ≤
      mu.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => ENNReal.toReal_nonneg))
    exact aux_density_stopping_measure_sum d m z r hr mu stop J
  have hstop : (∑ p ∈ stopped, cost p.1 p.2) ≤
      C * mu.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    calc _ ≤ ∑ p ∈ stopped, C * mass p.1 p.2 :=
          Finset.sum_le_sum (fun p hp => hstopCost p.1 p.2 (Finset.mem_filter.mp hp).2)
      _ = C * ∑ p ∈ stopped, mass p.1 p.2 := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsumMass hC
  have hres : (∑ p ∈ residual, cost p.1 p.2) ≤ eps := by
    have hdepth : ∀ p ∈ residual, (p.1 : ℕ) = J := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hleaf, hnstop⟩
      exact ((aux_lem_finite_stopping_partition_mem_leafFinset stop J p).mp hleaf).2.1.resolve_left hnstop
    calc _ ≤ ∑ _p ∈ residual, K * (descendantSide m J r) ^ s :=
          Finset.sum_le_sum (fun p hp => (hcrude p.1 p.2).trans_eq (by rw [hdepth p hp]))
      _ = (residual.card : ℝ) * (K * (descendantSide m J r) ^ s) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ L ^ (((d : ℝ) - eta / 8) * (J : ℝ)) * (K * (descendantSide m J r) ^ s) :=
          mul_le_mul_of_nonneg_right hcount (mul_nonneg hK (Real.rpow_nonneg (descendantSide_pos m J hr).le _))
      _ ≤ eps := hepsJ
  have hsplit : (∑ p ∈ leaves, cost p.1 p.2) =
      (∑ p ∈ stopped, cost p.1 p.2) + (∑ p ∈ residual, cost p.1 p.2) :=
    (Finset.sum_filter_add_sum_filter_not leaves (fun p => stop p.1 p.2) (fun p => cost p.1 p.2)).symm
  rw [hsplit]
  exact add_le_add hstop hres

end Paper
