import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Balanced strip and core exponents

The algebra in Lemma 29, (E037). This module does not prove the geometric
covering estimate for a measure. The dimension is real here, so the result
also applies to the natural-number dimensions in the dossier.
-/

namespace SubdiffusiveProcess

/-- Exponent of the core side length as a power of the layer wavelength. -/
noncomputable def stripMeshExponent (d t : ℝ) : ℝ := (t - d + 1) / (t + 1)

/-- Common exponent of the strip mass and maximum core mass. -/
noncomputable def stripMassExponent (d t : ℝ) : ℝ := t * (t - d + 1) / (t + 1)

theorem strip_mesh_exponent_pos {d t : ℝ} (hd : 1 ≤ d) (ht : d - 1 < t) :
    0 < stripMeshExponent d t := by
  unfold stripMeshExponent
  apply div_pos <;> linarith

theorem strip_mesh_exponent_lt_one {d t : ℝ} (hd : 1 ≤ d) (ht : d - 1 < t) :
    stripMeshExponent d t < 1 := by
  unfold stripMeshExponent
  apply (div_lt_one (by linarith : 0 < t + 1)).2
  linarith

theorem strip_mass_exponent_pos {d t : ℝ} (hd : 1 ≤ d) (ht : d - 1 < t) :
    0 < stripMassExponent d t := by
  unfold stripMassExponent
  exact div_pos (mul_pos (by linarith) (by linarith)) (by linarith)

theorem strip_core_exponents_equal {d t : ℝ} (ht : t + 1 ≠ 0) :
    t - d + 1 - stripMeshExponent d t = stripMassExponent d t ∧
      t * stripMeshExponent d t = stripMassExponent d t := by
  unfold stripMeshExponent stripMassExponent
  constructor
  · field_simp
    ring
  · exact (mul_div_assoc _ _ _).symm

end SubdiffusiveProcess
