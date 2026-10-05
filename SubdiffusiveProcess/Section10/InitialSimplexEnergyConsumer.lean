module

public import SubdiffusiveProcess.Section10.InitialSimplexEnergyStationarity
public import SubdiffusiveProcess.Section10.RetainedPrefixSparseStep

@[expose] public section

/-!
# Applying the initial energy supplier to the actual retained-prefix induction

This module consumes the actual retained coefficient and the proved
successor contraction. The starting constant is multiplied by q^N, and is
paid once. The all-scale statement has only the geometric packing input;
the ell=0 application constructs that packing internally.
-/

namespace SubdiffusiveProcess.Section10

open Homogenization Homogenization.Book MeasureTheory
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec Mat TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn

noncomputable section

variable {d : ℕ}

/-- Generic induction that preserves linear dependence on the initial bound. -/
theorem linear_bound_induction {P : ℕ → ℝ → Prop} {A q : ℝ}
    (hA : 0 ≤ A) (hq : 0 ≤ q) (hzero : P 0 A)
    (hstep : ∀ N kap, 0 ≤ kap → P N kap → P (N + 1) (kap * q)) (N : ℕ) :
    P N (A * q ^ N) := by
  induction N with
  | zero => simpa only [pow_zero, mul_one] using hzero
  | succ N ih =>
      have h := hstep N (A * q ^ N) (mul_nonneg hA (pow_nonneg hq N)) ih
      simpa only [pow_succ, mul_assoc] using h

/-- Literal base-case identity with the actual retained-prefix energy. -/
theorem integral_retainedPrefixEnergy_zero_eq_initial (M : GMCModel d)
    (ell R : ℕ) (T : KuhnCell d) (hT : T.supportCube.scale = (ell : ℤ)) (p : Vec d) :
    (∫ omega, retainedPrefixEnergy M ell R 0 T omega p ∂M.P.toMeasure) =
      initialSimplexExpectedEnergy M ell T.order p := by
  have hpoint : ∀ omega,
      retainedPrefixEnergy M ell R 0 T omega p =
        vecDot p (matVecMul (randomAMatrix M ell (kuhnCellDomain T) omega) p) := by
    intro omega
    rw [retainedPrefixEnergy, retainedPrefixCoefficient_zero]
    exact (vecDot_aMatrix_eq_dirichletInfOn (aCutoffCoeffOnData M ell omega (kuhnCellDomain T))
      (fun _ => (Real.exp_pos _).le) p).symm
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  exact expectedAffineDirichletEnergy_simplex_eq_origin M ell T hT p

/-- Actual retained-prefix sparse induction initialized by the source-derived
simplex bound, with a single initial constant. No assumed initial energy
estimate occurs: the sole supplied object is geometric packing. -/
theorem exists_retainedPrefixSparseBound_of_initial_packing (d : ℕ) (K : ℝ) (hK : 1 ≤ K) :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∀ ell : ℕ, (∀ pi : Equiv.Perm (Fin d), Nonempty (InitialSimplexCubePacking ell pi K)) →
      ∀ R : ℕ, 0 < R → ∀ qq : ℝ, 0 ≤ qq →
        (∀ pi : Equiv.Perm (Fin d),
          qRCell M (unitMesh d (-(R : ℤ))) (originKuhnCell d pi 0) ≤ qq) →
      ∀ N : ℕ, RetainedPrefixSparseBound M ell R N (C * ahom M ell * qq ^ N) := by
  obtain ⟨delta0, C, hdelta0, hC, henergy⟩ :=
    exists_initialSimplexEnergy_constants_of_packing d K hK
  refine ⟨delta0, C, hdelta0, hC, ?_⟩
  intro M hM ell hpack R hR qq hqq hqR N
  have hbase : RetainedPrefixSparseBound M ell R 0 (C * ahom M ell) := by
    intro c pi p
    rw [show ell + 0 * R = ell by omega,
      integral_retainedPrefixEnergy_zero_eq_initial M ell R (dilatedCell ell c pi) rfl p]
    exact henergy M hM ell pi (Classical.choice (hpack pi)) p
  exact linear_bound_induction (P := fun N kap => RetainedPrefixSparseBound M ell R N kap)
    (mul_nonneg hC.le (ahom_pos M ell).le) hqq hbase
    (fun N kap hkap hIH => retainedPrefixSparseBound_succ M ell hR N hkap hIH hqR) N

/-- A concrete generic-induction application to the actual retained-prefix
coefficient, with explicit initial constant 2 and no geometry premise. -/
theorem retainedPrefixSparseBound_two_ahom_zero (M : GMCModel d) {R : ℕ} (hR : 0 < R)
    {qq : ℝ} (hqq : 0 ≤ qq)
    (hqR : ∀ pi : Equiv.Perm (Fin d),
      qRCell M (unitMesh d (-(R : ℤ))) (originKuhnCell d pi 0) ≤ qq) (N : ℕ) :
    RetainedPrefixSparseBound M 0 R N (2 * ahom M 0 * qq ^ N) := by
  have hbase : RetainedPrefixSparseBound M 0 R 0 (2 * ahom M 0) := by
    intro c pi p
    rw [show 0 + 0 * R = 0 by omega,
      integral_retainedPrefixEnergy_zero_eq_initial M 0 R (dilatedCell 0 c pi) rfl p]
    exact initialSimplexExpectedEnergy_zero_le M pi p
  exact linear_bound_induction (P := fun N kap => RetainedPrefixSparseBound M 0 R N kap)
    (mul_nonneg (by norm_num) (ahom_pos M 0).le) hqq hbase
    (fun N kap hkap hIH => retainedPrefixSparseBound_succ M 0 hR N hkap hIH hqR) N

/-- Complete genuine-model induction application at ell=0: its geometric
packing is constructed here, so no packing or initial energy premise remains. -/
theorem exists_retainedPrefixSparseBound_zero_initial (d : ℕ) :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∀ R : ℕ, 0 < R → ∀ qq : ℝ, 0 ≤ qq →
        (∀ pi : Equiv.Perm (Fin d),
          qRCell M (unitMesh d (-(R : ℤ))) (originKuhnCell d pi 0) ≤ qq) →
      ∀ N : ℕ, RetainedPrefixSparseBound M 0 R N (C * ahom M 0 * qq ^ N) := by
  obtain ⟨delta0, C, hdelta0, hC, hbound⟩ :=
    exists_retainedPrefixSparseBound_of_initial_packing d 1 (le_refl _)
  refine ⟨delta0, C, hdelta0, hC, ?_⟩
  intro M hM R hR qq hqq hqR N
  exact hbound M hM 0 (fun pi => ⟨initialSimplexCubePacking_zero pi (le_refl _)⟩)
    R hR qq hqq hqR N

end
end SubdiffusiveProcess.Section10
