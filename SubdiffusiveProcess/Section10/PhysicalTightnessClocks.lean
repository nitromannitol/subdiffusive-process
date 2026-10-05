module

public import SubdiffusiveProcess.Section10.PhysicalTightnessEnvironment
public import SubdiffusiveProcess.Frozen.Section3.AnnealedMatrixBounds

@[expose] public section

/-!
# Relative local clocks in the two rescaled physical families

These are numerical consequences of the already established raw clocks and
annealed ordering, not a new rescaling theorem. Large cubes above a finite
cutoff keep active cutoff `N`; top uses `N+j`. Small cubes at `N-k` have the same
clock in both branches. The normalized clock retains `ahom_0` through the
existing `PhysicalLocalTransport.normalizedClock_eq`.
-/

open Homogenization
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness
open PhysicalLocalTransport

variable {d : ℕ}

/-- Local time unit measured in the base rescaled clock. -/
def relativeClock (M : GMCModel d) (L : WithTop ℕ) (N m : ℕ) : ℝ :=
  (rawClock M L m : ℝ) / (rawClock M L N : ℝ)

theorem relativeClock_pos (M : GMCModel d) (L : WithTop ℕ) (N m : ℕ) :
    0 < relativeClock M L N m :=
  div_pos (rawClock_pos M L m) (rawClock_pos M L N)

/-- Exact ratio for arbitrary local scale, including `m>N`. -/
theorem relativeClock_eq (M : GMCModel d) (L : WithTop ℕ) (N m : ℕ)
    (hactive : activeScale L N = N) :
    relativeClock M L N m =
      (3 : ℝ) ^ (2 * ((m : ℤ) - (N : ℤ))) * ahom M N / ahom M (activeScale L m) := by
  unfold relativeClock
  change ((3 : ℝ) ^ (2 * m) / ahom M (activeScale L m)) /
    ((3 : ℝ) ^ (2 * N) / ahom M (activeScale L N)) = _
  rw [hactive]
  rw [mul_sub, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
  norm_cast
  field_simp [(ahom_pos M N).ne', (ahom_pos M (activeScale L m)).ne']

/-- Large cubes in the finite branch have exactly the diffusive clock. -/
theorem finite_relativeClock_large (M : GMCModel d) (N j : ℕ) :
    relativeClock M (N : WithTop ℕ) N (N + j) = (3 : ℝ) ^ (2 * j) := by
  rw [relativeClock_eq M _ N (N + j) (by rw [activeScale_coe, min_self])]
  simp only [activeScale_coe, min_eq_right (Nat.le_add_right N j)]
  have he : (2 * (((N + j : ℕ) : ℤ) - (N : ℤ))) = ((2 * j : ℕ) : ℤ) := by omega
  rw [he, zpow_natCast]
  field_simp [(ahom_pos M N).ne']

/-- Top's larger active cutoff makes its large-cube clock at least as large. -/
theorem top_relativeClock_large (M : GMCModel d) (N j : ℕ) :
    (3 : ℝ) ^ (2 * j) ≤ relativeClock M ⊤ N (N + j) := by
  by_cases hj : j = 0
  · subst j
    simp [relativeClock, (rawClock_pos M ⊤ N).ne']
  rw [relativeClock_eq M _ N (N + j) (by simp [activeScale])]
  simp only [activeScale, WithTop.untopD_top, min_self]
  have he : (2 * (((N + j : ℕ) : ℤ) - (N : ℤ))) = ((2 * j : ℕ) : ℤ) := by omega
  rw [he, zpow_natCast]
  have ho := (SubdiffusiveProcess.Frozen.Section3.annealed_matrix_bounds.2 M (N + j) N
    (by omega)).1
  exact (le_div_iff₀ (ahom_pos M (N + j))).2
    (mul_le_mul_of_nonneg_left ho (by positivity))

/-- The small-cube ratio is identical for finite and top branches. -/
theorem relativeClock_small_eq (M : GMCModel d) (L : WithTop ℕ) {N k : ℕ}
    (hk : k ≤ N) (hactive : activeScale L N = N)
    (hsmall : activeScale L (N - k) = N - k) :
    relativeClock M L N (N - k) =
      (3 : ℝ) ^ (-(2 * k : ℤ)) * ahom M N / ahom M (N - k) := by
  rw [relativeClock_eq M L N (N - k) hactive, hsmall]
  have he : 2 * (((N - k : ℕ) : ℤ) - (N : ℤ)) = -(2 * k : ℤ) := by omega
  rw [he]

/-- A strictly positive small-cube lower bound independent of the base cutoff. -/
theorem relativeClock_small_lower (M : GMCModel d) (L : WithTop ℕ) {N k : ℕ}
    (hk : k ≤ N) (hactive : activeScale L N = N)
    (hsmall : activeScale L (N - k) = N - k) :
    (3 : ℝ) ^ (-(2 * k : ℤ)) / Real.exp (2 * tauSq M.P * (k : ℝ)) ≤
      relativeClock M L N (N - k) := by
  by_cases hk0 : k = 0
  · subst k
    simp [relativeClock, (rawClock_pos M L N).ne']
  rw [relativeClock_small_eq M L hk hactive hsmall]
  have ho := (SubdiffusiveProcess.Frozen.Section3.annealed_matrix_bounds.2 M N (N - k)
    (by omega)).2
  have hdiff : N - (N - k) = k := by omega
  rw [hdiff] at ho
  have hr : (1 : ℝ) / Real.exp (2 * tauSq M.P * (k : ℝ)) ≤
      ahom M N / ahom M (N - k) := by
    apply (div_le_div_iff₀ (Real.exp_pos _) (ahom_pos M (N - k))).2
    simpa only [one_mul, mul_comm] using ho
  simpa only [div_eq_mul_inv, mul_one, one_mul, mul_assoc] using
    mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ (3 : ℝ) ^ (-(2 * k : ℤ)))

/-- Explicit finite-branch projection of the uniform small-cube lower bound. -/
theorem finite_relativeClock_small_lower (M : GMCModel d) {N k : ℕ} (hk : k ≤ N) :
    (3 : ℝ) ^ (-(2 * k : ℤ)) / Real.exp (2 * tauSq M.P * (k : ℝ)) ≤
      relativeClock M (N : WithTop ℕ) N (N - k) :=
  relativeClock_small_lower M _ hk (by rw [activeScale_coe, min_self])
    (by rw [activeScale_coe, min_eq_left (Nat.sub_le N k)])

/-- Explicit top-branch projection of the same lower bound. -/
theorem top_relativeClock_small_lower (M : GMCModel d) {N k : ℕ} (hk : k ≤ N) :
    (3 : ℝ) ^ (-(2 * k : ℤ)) / Real.exp (2 * tauSq M.P * (k : ℝ)) ≤
      relativeClock M ⊤ N (N - k) :=
  relativeClock_small_lower M _ hk (by simp [activeScale]) (by simp [activeScale])

end SubdiffusiveProcess.Section10.PhysicalTightness
