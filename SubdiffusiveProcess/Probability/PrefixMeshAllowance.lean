import SubdiffusiveProcess.Probability.PrefixAllowance
import SubdiffusiveProcess.Probability.AffineMeshAllowance

/-! A common allowance for all prefix events on a growing mesh.  The proof
combines the measurable last-exception construction with the finite mesh
envelope.  The exponential prefix estimate and mesh cardinality remain explicit
premises; no PDE or finite-to-limit response transfer is asserted here.
-/

open MeasureTheory Set
open scoped ENNReal Topology

namespace SubdiffusiveProcess

/-- Exponential prefix estimates beat spatial entropy precisely when their
rate times the allowed depth loss exceeds the mesh growth rate. -/
theorem exists_common_prefix_allowance
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (k : ℕ → ℕ) (d b : ℕ) (Ccount Ctail A xi : ℝ)
    (hCcount : 0 ≤ Ccount) (hCtail : 0 ≤ Ctail)
    (hA : 0 < A) (hxi : 0 < xi)
    (hrate : (d : ℝ) * Real.log 3 < A * xi)
    (hcard : ∀ n : ℕ, (k n : ℝ) ≤
      Ccount * ((n : ℝ) + 1) ^ b * (3 : ℝ) ^ ((d : ℝ) * n))
    (bad : ∀ n : ℕ, Fin (k n) → ℕ → Set Omega)
    (hbad : ∀ n i m, MeasurableSet (bad n i m))
    (htail : ∀ n i m, mu (bad n i m) ≤
      ENNReal.ofReal (Ctail * Real.exp (-A * (m : ℝ)))) :
    ∀ᵐ omega ∂mu, ∃ B0 : ℝ, 0 < B0 ∧
      ∀ (n : ℕ) (i : Fin (k n)) (m : ℕ),
        xi * (n : ℝ) + B0 ≤ (m : ℝ) → omega ∉ bad n i m := by
  have hlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hgap : (d : ℝ) * Real.log 3 / xi < A := (div_lt_iff₀ hxi).2 hrate
  obtain ⟨t, hlo, hhi⟩ := exists_between hgap
  have ht : 0 < t := lt_of_le_of_lt
    (div_nonneg (mul_nonneg (Nat.cast_nonneg d) hlog) hxi.le) hlo
  have hrate' : (d : ℝ) * Real.log 3 < t * xi := (div_lt_iff₀ hxi).1 hlo
  have hallow n i := exists_prefix_allowance_of_exponential_tails mu
    (bad n i) (hbad n i) Ctail A hCtail hA (htail n i)
  choose B hBm hBt hBg using hallow
  have hden : 0 < 1 - Real.exp (-A) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hA))
  have hcommon := exists_affine_mesh_allowance_of_exponential_tails mu k d b
    Ccount (Ctail / (1 - Real.exp (-A))) A t xi hCcount
    (div_nonneg hCtail hden.le) ht hhi hrate' hcard B hBm hBt
  have hgood : ∀ᵐ omega ∂mu, ∀ n i m, B n i omega ≤ m → omega ∉ bad n i m :=
    ae_all_iff.2 (fun n => ae_all_iff.2 (fun i => hBg n i))
  filter_upwards [hcommon, hgood] with omega homega hgoodomega
  obtain ⟨B0, hB0, hB⟩ := homega
  refine ⟨B0, hB0, ?_⟩
  intro n i m hm
  have hle : B n i omega ≤ m := by exact_mod_cast (hB n i).trans hm
  exact hgoodomega n i m hle

end SubdiffusiveProcess
