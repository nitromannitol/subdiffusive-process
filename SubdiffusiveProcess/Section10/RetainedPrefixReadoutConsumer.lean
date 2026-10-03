module

public import SubdiffusiveProcess.Section10.RetainedPrefixReadout
public import SubdiffusiveProcess.Section10.RetainedPrefixSparseStepConsumer
public import SubdiffusiveProcess.Section10.InitialSimplexEnergyConsumer

@[expose] public section




namespace SubdiffusiveProcess.Section10

open Homogenization MeasureTheory
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab (ahom)
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn

noncomputable section

variable {d : ℕ}

/-- D2's actual initial-cutoff induction followed by D3's arbitrary-cutoff
readout. The initial constant remains linear and is paid once. -/
theorem ahom_le_retainedPrefix_pow_of_initial (M : GMCModel d) (ell : ℕ)
    {R : ℕ} (hR : 0 < R) {kap qq : ℝ} (hkap : 0 ≤ kap) (hqq : 0 ≤ qq)
    (hbase : ∀ (c : Fin d → ℤ) (pi : Equiv.Perm (Fin d)) (p : Vec d),
      ∫ omega, (volume (dilatedCell ell c pi).openCarrier).toReal⁻¹ *
        dirichletInfOn (aCutoff M ell omega) (dilatedCell ell c pi).openCarrier p
        ∂M.P.toMeasure ≤ kap * vecNormSq p)
    (hqR : ∀ pi : Equiv.Perm (Fin d),
      qRCell M (unitMesh d (-(R : ℤ))) (originKuhnCell d pi 0) ≤ qq)
    {N m : ℕ} (hm : ell + N * R ≤ m) : ahom M m ≤ kap * qq ^ N := by
  exact ahom_le_of_retainedPrefixSparseBound M hm
    (retainedPrefix_sparse_induction_of_initial M ell hR hkap hqq hbase hqR N)



theorem ahom_le_two_ahom_zero_mul_pow (M : GMCModel d) {R : ℕ} (hR : 0 < R)
    {qq : ℝ} (hqq : 0 ≤ qq)
    (hqR : ∀ pi : Equiv.Perm (Fin d),
      qRCell M (unitMesh d (-(R : ℤ))) (originKuhnCell d pi 0) ≤ qq)
    {N m : ℕ} (hm : N * R ≤ m) : ahom M m ≤ 2 * ahom M 0 * qq ^ N :=
  ahom_le_of_retainedPrefixSparseBound M (by simpa only [Nat.zero_add] using hm)
    (retainedPrefixSparseBound_two_ahom_zero M hR hqq hqR N)

end

end SubdiffusiveProcess.Section10
