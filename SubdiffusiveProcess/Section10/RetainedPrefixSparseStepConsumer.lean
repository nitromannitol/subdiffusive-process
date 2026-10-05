module

public import SubdiffusiveProcess.Section10.RetainedPrefixSparseStep

@[expose] public section

/-!
# Induction consumer with one explicit initial bound

The single-step helper is applied at each generation. Its base is the actual
full cutoff at `ell`, and the constants are `kap * qq^N`, including `N = 0`.
This is an internal conditional induction, not a source-root premise or proof.
-/

namespace SubdiffusiveProcess.Section10

open Homogenization MeasureTheory
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn

noncomputable section

variable {d : ℕ}

/-- Iteration of the proved retained-prefix step, with the base bound paid once. -/
theorem retainedPrefixSparseBound_pow (M : GMCModel d) (ell : ℕ) {R : ℕ}
    (hR : 0 < R) {kap qq : ℝ} (hkap : 0 ≤ kap) (hqq : 0 ≤ qq)
    (hbase : RetainedPrefixSparseBound M ell R 0 kap)
    (hqR : ∀ pi : Equiv.Perm (Fin d),
      qRCell M (unitMesh d (-(R : ℤ))) (originKuhnCell d pi 0) ≤ qq) (N : ℕ) :
    RetainedPrefixSparseBound M ell R N (kap * qq ^ N) := by
  induction N with
  | zero => simpa only [pow_zero, mul_one] using hbase
  | succ N ih =>
      have h := retainedPrefixSparseBound_succ M ell hR N
        (mul_nonneg hkap (pow_nonneg hqq N)) ih hqR
      simpa only [pow_succ, mul_assoc] using h

/-- An actual induction consumer: the only initial energy premise is explicitly
the full cutoff `aCutoff M ell` on all scale-ell translated/permuted cells.
The conclusion literally uses the retained range-union-image set. -/
theorem retainedPrefix_sparse_induction_of_initial (M : GMCModel d) (ell : ℕ)
    {R : ℕ} (hR : 0 < R) {kap qq : ℝ} (hkap : 0 ≤ kap) (hqq : 0 ≤ qq)
    (hbase : ∀ (c : Fin d → ℤ) (pi : Equiv.Perm (Fin d)) (p : Vec d),
      ∫ omega, (volume (dilatedCell ell c pi).openCarrier).toReal⁻¹ *
        dirichletInfOn (aCutoff M ell omega) (dilatedCell ell c pi).openCarrier p
        ∂M.P.toMeasure ≤ kap * vecNormSq p)
    (hqR : ∀ pi : Equiv.Perm (Fin d),
      qRCell M (unitMesh d (-(R : ℤ))) (originKuhnCell d pi 0) ≤ qq)
    (N : ℕ) (c : Fin d → ℤ) (pi : Equiv.Perm (Fin d)) (p : Vec d) :
    ∫ omega, (volume (dilatedCell (ell + N * R) c pi).openCarrier).toReal⁻¹ *
      dirichletInfOn (layerCoefficient M (Finset.range (ell + 1) ∪
        (Finset.range N).image (fun j => ell + (j + 1) * R)) omega)
        (dilatedCell (ell + N * R) c pi).openCarrier p ∂M.P.toMeasure ≤
      (kap * qq ^ N) * vecNormSq p := by
  have hbase' : RetainedPrefixSparseBound M ell R 0 kap := by
    intro c pi p
    simpa only [retainedPrefixEnergy, retainedPrefixCoefficient_zero,
      Nat.zero_mul, Nat.add_zero] using hbase c pi p
  exact retainedPrefixSparseBound_pow M ell hR hkap hqq hbase' hqR N c pi p

end

end SubdiffusiveProcess.Section10
