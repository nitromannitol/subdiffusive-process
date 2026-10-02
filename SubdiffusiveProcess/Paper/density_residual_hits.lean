import SubdiffusiveProcess.Paper.density_stopping_measure
import SubdiffusiveProcess.Paper.density_selected_depths
import SubdiffusiveProcess.Paper.density_mass_drop_bound
open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
open Classical

/-- The three possible reasons a selected step fails to stop. -/
theorem aux_density_residual_hits_classify
    (d m J : ℕ) (mass : (n : ℕ) → (Fin n → OddGridIndex d m) → ℝ)
    (Sel : ℕ → Prop) (Good : (n : ℕ) → (Fin n → OddGridIndex d m) → Prop)
    (Pad : OddGridIndex d m → Prop) (LD : ℝ) (w : Fin J → OddGridIndex d m)
    (lam : ℕ → ℝ)
    (hlam : ∀ k (hk : k ≤ J), lam k = mass k (aux_lem_finite_stopping_partition_wordPrefix w k hk))
    (hno : ∀ (k : ℕ) (hk : k ≤ J),
      ¬ aux_lem_finite_stopping_partition_stopRule Sel Good Pad mass LD k
        (aux_lem_finite_stopping_partition_wordPrefix w k hk)) :
    ((Finset.univ : Finset (Fin J)).filter fun i => Sel (i.val + 1)).card ≤
      ((Finset.univ : Finset (Fin J)).filter fun i =>
        ¬ Good (i.val + 1) (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt)).card +
      ((Finset.univ : Finset (Fin J)).filter fun i => ¬ Pad (w i)).card +
      aux_lem_finite_stopping_partition_dropCount lam LD J := by
  have hclass : ∀ i ∈ (Finset.univ : Finset (Fin J)), Sel (i.val + 1) →
      ¬ Good (i.val + 1) (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt) ∨
        w i ∈ (Finset.univ.filter fun l => ¬ Pad l) ∨ LD * lam (i.val + 1) < lam i.val := by
    intro i _ hSel
    have hns := hno (i.val + 1) i.isLt
    have hlast : aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt (Fin.last i.val) = w i :=
      congrArg w (Fin.ext rfl)
    have hinitw : (fun j : Fin i.val => aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt j.castSucc) =
        aux_lem_finite_stopping_partition_wordPrefix w i.val (Nat.le_of_lt i.isLt) := by
      funext j
      rfl
    simp only [aux_lem_finite_stopping_partition_stopRule, not_and, not_le] at hns
    by_cases hG : Good (i.val + 1) (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt)
    · by_cases hP : Pad (w i)
      · right; right
        have h := hns hSel hG (by rw [hlast]; exact hP)
        rw [hlam (i.val + 1) i.isLt, hlam i.val (Nat.le_of_lt i.isLt)]
        rw [hinitw] at h
        exact h
      · right; left
        simp [hP]
    · exact Or.inl hG
  have hcount := aux_lem_finite_stopping_partition_card_filter_le_three (Finset.univ : Finset (Fin J))
    (fun i => Sel (i.val + 1))
    (fun i => ¬ Good (i.val + 1) (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt))
    (fun i => w i ∈ (Finset.univ.filter fun l => ¬ Pad l))
    (fun i => LD * lam (i.val + 1) < lam i.val) hclass
  have hdropeq : ((Finset.univ : Finset (Fin J)).filter
      (fun i => LD * lam (i.val + 1) < lam i.val)).card = aux_lem_finite_stopping_partition_dropCount lam LD J :=
    aux_lem_finite_stopping_partition_card_filter_fin_eq_range J (fun s => LD * lam (s + 1) < lam s)
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, hdropeq] using hcount

/-- Positive-density selected levels force a positive proportion of non-padded
steps on every unstopped branch, for arbitrarily large common horizons. All
mass comparisons use the actual regularized finite measure on descendant cubes. -/
theorem density_residual_hits
    (d m : ℕ) (hm : 0 < m) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (nu : Measure (SpatialCoordinates d)) [IsFiniteMeasure nu]
    (c D eta theta Bbad : ℝ) (hc : 0 < c) (hD : 0 < D) (heta : 0 < eta)
    (hDim : (d : ℝ) / D ≤ eta / 8) (htheta : theta ≤ eta / 8)
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
    ∃ᶠ J : ℕ in atTop, ∀ w : Fin J → OddGridIndex d m,
      (∀ (k : ℕ) (hk : k ≤ J), ¬ stop k (aux_lem_finite_stopping_partition_wordPrefix w k hk)) →
      (eta / 3) * (J : ℝ) ≤
        (((Finset.univ : Finset (Fin J)).filter fun i => ¬ Pad (w i)).card : ℝ) := by
  intro mu mass L stop
  obtain ⟨hfinite, hmono, hfloor⟩ := aux_density_stopping_measure_properties d m z r hr nu c hc
  letI : IsFiniteMeasure mu := hfinite
  have hL : 1 < L := by dsimp [L]; exact_mod_cast (by omega : 1 < 2 * m + 1)
  have hL0 : 0 < L := zero_lt_one.trans hL
  have hside : ∀ J : ℕ, c * r ^ d * L ^ (-(d : ℝ) * (J : ℝ)) = c * (descendantSide m J r) ^ d := by
    intro J
    rw [neg_mul, Real.rpow_neg hL0.le, Real.rpow_mul_natCast hL0.le,
      Real.rpow_natCast]
    simp only [descendantSide, div_pow, div_eq_mul_inv]
    have hp : (L ^ d) ^ J = (L ^ J) ^ d := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [hp]
    simp only [mul_pow, inv_pow]
    dsimp only [L]
    ring
  obtain ⟨Bdrop, hBdrop, hDrops⟩ := density_mass_drop_bound L D (d : ℝ)
    (mu.real (centeredCube z r hr : Set (SpatialCoordinates d))) (c * r ^ d)
    hL hD (mul_pos hc (pow_pos hr d))
  have hfreq := density_selected_depths S eta heta hS base (Bbad + Bdrop)
  apply hfreq.mono
  intro J hselected w hno
  let lam : ℕ → ℝ := fun k => if hk : k ≤ J then
    mass k (aux_lem_finite_stopping_partition_wordPrefix w k hk) else mass J w
  have hlam : ∀ k (hk : k ≤ J),
      lam k = mass k (aux_lem_finite_stopping_partition_wordPrefix w k hk) := fun k hk => dif_pos hk
  have hmono' : ∀ k, lam (k + 1) ≤ lam k := by
    intro k
    by_cases hk : k + 1 ≤ J
    · rw [hlam (k + 1) hk, hlam k (by omega)]
      exact hmono k (aux_lem_finite_stopping_partition_wordPrefix w (k + 1) hk)
    · have h1 : lam (k + 1) = mass J w := dif_neg hk
      by_cases hk' : k ≤ J
      · have hkJ : k = J := by omega
        subst hkJ
        rw [h1, hlam k hk', aux_lem_finite_stopping_partition_wordPrefix_self]
      · rw [h1, show lam k = mass J w from dif_neg hk']
  have hroot : lam 0 ≤ mu.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    rw [hlam 0 (Nat.zero_le J)]
    exact measureReal_mono (aux_lem_finite_stopping_partition_descendantCell_subset_root m z hr 0 _)
      (measure_ne_top mu _)
  have hfinal : c * r ^ d * L ^ (-(d : ℝ) * (J : ℝ)) ≤ lam J := by
    rw [hlam J le_rfl, aux_lem_finite_stopping_partition_wordPrefix_self, hside]
    exact hfloor J w
  have hdrops := hDrops J lam hmono' hroot hfinal
  have hclass := aux_density_residual_hits_classify d m J mass (fun n => S (base + n)) Good Pad
    (L ^ D) w lam hlam hno
  have hselEq : ((Finset.univ : Finset (Fin J)).filter fun i => S (base + (i.val + 1))).card =
      ((Finset.range J).filter fun n => S (base + n + 1)).card := by
    simpa only [Nat.add_assoc] using
      aux_lem_finite_stopping_partition_card_filter_fin_eq_range J (fun n => S (base + n + 1))
  rw [hselEq] at hclass
  have hclassR : ((((Finset.range J).filter fun n => S (base + n + 1)).card : ℝ)) ≤
      (((Finset.univ : Finset (Fin J)).filter fun i =>
        ¬ Good (i.val + 1) (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt)).card : ℝ) +
      (((Finset.univ : Finset (Fin J)).filter fun i => ¬ Pad (w i)).card : ℝ) +
      (aux_lem_finite_stopping_partition_dropCount lam (L ^ D) J : ℝ) := by
    exact_mod_cast hclass
  have hbad' := hbad J w
  have hdim' := mul_le_mul_of_nonneg_right hDim (Nat.cast_nonneg J : (0 : ℝ) ≤ J)
  have htheta' := mul_le_mul_of_nonneg_right htheta (Nat.cast_nonneg J : (0 : ℝ) ≤ J)
  nlinarith [mul_nonneg heta.le (Nat.cast_nonneg J : (0 : ℝ) ≤ J)]

end Paper
