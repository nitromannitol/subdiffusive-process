import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open Set
noncomputable section
namespace SubdiffusiveProcess.Nash

/-- A scalar Nash differential inequality on an interval where the orbit stays positive. -/
theorem decay_rpow (u v : ℝ → ℝ) (d c t : ℝ) (hd : 0 < d) (hc : 0 < c) (ht : 0 < t)
    (hu : ContinuousOn u (Icc 0 t))
    (hpos : ∀ s ∈ Icc 0 t, 0 < u s)
    (hder : ∀ s ∈ Ioo 0 t, HasDerivAt u (v s) s)
    (hineq : ∀ s ∈ Ioo 0 t, v s ≤ -(d * c) * u s ^ (1 + 1 / d)) :
    u t ≤ (c * t) ^ (-d) := by
  have hd0 : d ≠ 0 := hd.ne'
  have hp (s : ℝ) (hs : s ∈ Icc 0 t) : u s ≠ 0 := (hpos s hs).ne'
  have hg : ContinuousOn (fun s => u s ^ (-(1 / d))) (Icc 0 t) :=
    hu.rpow_const fun s hs => Or.inl (hp s hs)
  have hgd (s : ℝ) (hs : s ∈ Ioo 0 t) :
      HasDerivAt (fun s => u s ^ (-(1 / d)))
        (v s * (-(1 / d)) * u s ^ (-(1 / d) - 1)) s := by
    convert (hder s hs).rpow_const (Or.inl (hp s (Ioo_subset_Icc_self hs))) using 1
  have hgineq (s : ℝ) (hs : s ∈ Ioo 0 t) :
      c ≤ v s * (-(1 / d)) * u s ^ (-(1 / d) - 1) := by
    have hup : 0 < u s := hpos s (Ioo_subset_Icc_self hs)
    have hpow : u s ^ (1 + 1 / d) * u s ^ (-(1 / d) - 1) = 1 := by
      rw [← Real.rpow_add hup]
      rw [show 1 + 1 / d + (-(1 / d) - 1) = 0 by ring, Real.rpow_zero]
    have hm := mul_le_mul_of_nonpos_right (hineq s hs) (neg_nonpos.mpr (by positivity : 0 ≤ 1 / d))
    have hm' := mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hup.le (-(1 / d) - 1))
    have heq : (-(d * c) * u s ^ (1 + 1 / d) * (-(1 / d))) *
        u s ^ (-(1 / d) - 1) = c := by
      calc
        _ = (d / d) * c * (u s ^ (1 + 1 / d) * u s ^ (-(1 / d) - 1)) := by ring
        _ = c := by rw [hpow, div_self hd0]; ring
    rwa [heq] at hm'
  have hinc := (convex_Icc (0 : ℝ) t).mul_sub_le_image_sub_of_le_deriv hg
    (fun s hs => (hgd s (by simpa only [interior_Icc] using hs)).differentiableAt.differentiableWithinAt)
    (fun s hs => by
      rw [(hgd s (by simpa only [interior_Icc] using hs)).deriv]
      exact hgineq s (by simpa only [interior_Icc] using hs))
    0 ⟨le_rfl, ht.le⟩ t ⟨ht.le, le_rfl⟩ ht.le
  have hlow : c * t ≤ u t ^ (-(1 / d)) := by
    have := Real.rpow_nonneg (hpos 0 ⟨le_rfl, ht.le⟩).le (-(1 / d))
    simpa only [sub_zero] using (show c * (t - 0) ≤ u t ^ (-(1 / d)) by linarith)
  have hh := Real.rpow_le_rpow_of_nonpos (mul_pos hc ht) hlow (show -d ≤ 0 by linarith)
  have heq : (u t ^ (-(1 / d))) ^ (-d) = u t := by
    rw [← Real.rpow_mul (hpos t ⟨ht.le, le_rfl⟩).le]
    have : -(1 / d) * -d = 1 := by field_simp
    rw [this, Real.rpow_one]
  rwa [heq] at hh

end SubdiffusiveProcess.Nash
