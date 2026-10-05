module

public import SubdiffusiveProcess.Section10.InitialSimplexEnergyScalar
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ShellLawTransport

@[expose] public section

/-!
# Stationary initial simplex energy on every translated simplex

The retained-prefix induction uses all triadic translations of a simplex.
Transport the genuine full-cutoff minimum through the stationary sequence
law, including volume normalization. No new geometric packing is needed for
translated cells.
-/

namespace SubdiffusiveProcess.Section10

open Homogenization Homogenization.Book MeasureTheory Set
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec Mat TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn

noncomputable section

variable {d : ℕ}

/-- The normalized cutoff minimum on any scale-ell triadic simplex has the
same expectation as the source's origin simplex of the same order. -/
theorem expectedAffineDirichletEnergy_simplex_eq_origin (M : GMCModel d) (ell : ℕ)
    (T : KuhnCell d) (hT : T.supportCube.scale = (ell : ℤ)) (p : Vec d) :
    expectedAffineDirichletEnergy M ell (kuhnCellDomain T) p =
      initialSimplexExpectedEnergy M ell T.order p := by
  let U := kuhnCellDomain (initialSimplex ell T.order)
  let z := cubeCenter T.supportCube
  have hTU : T.openCarrier = translateSet z (U : Set (Vec d)) := by
    have h := openCarrier_eq_translateSet_originKuhnCell T
    rw [hT] at h
    exact h
  have hvol : volume T.openCarrier = volume (U : Set (Vec d)) := by
    rw [hTU]
    exact volume_translateSet_eq z _
  have hpoint : ∀ omega : PotentialSample d,
      dirichletInfOn (aCutoff M ell omega) T.openCarrier p =
        dirichletInfOn (aCutoff M ell (translatePotentialSequence z omega))
          (U : Set (Vec d)) p := by
    intro omega
    have hfield : aCutoff M ell (translatePotentialSequence z omega) =
        fun x => aCutoff M ell omega (x + z) := by
      funext x
      exact (aCutoff_translatePotentialSequence M ell z omega x).symm
    rw [hfield, dirichletInfOn_comp_add_right (B := aCutoff M ell omega) (p := p) z U.measurableSet
      (fun _ => (Real.exp_pos _).le), ← hTU]
  have hmean : (∫ omega, dirichletInfOn (aCutoff M ell omega) T.openCarrier p
      ∂M.P.toMeasure) =
      ∫ omega, dirichletInfOn (aCutoff M ell omega) (U : Set (Vec d)) p ∂M.P.toMeasure := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    exact Homogenization.integral_comp_eq_of_map_eq
      (measurable_translatePotentialSequence z) (potentialSequenceLaw_stationary M z)
      (fun omega => dirichletInfOn (aCutoff M ell omega) (U : Set (Vec d)) p)
      (integrable_dirichletInfOn_aCutoff M ell U p).aestronglyMeasurable
  have hleft : expectedAffineDirichletEnergy M ell (kuhnCellDomain T) p =
      (volume T.openCarrier).toReal⁻¹ *
        ∫ omega, dirichletInfOn (aCutoff M ell omega) T.openCarrier p ∂M.P.toMeasure := by
    unfold expectedAffineDirichletEnergy
    simp_rw [randomAMatrix, vecDot_aMatrix_eq_dirichletInfOn
      (aCutoffCoeffOnData M ell _ (kuhnCellDomain T)) (fun _ => (Real.exp_pos _).le) p]
    exact integral_const_mul _ _
  have hright : initialSimplexExpectedEnergy M ell T.order p =
      (volume (U : Set (Vec d))).toReal⁻¹ *
        ∫ omega, dirichletInfOn (aCutoff M ell omega) (U : Set (Vec d)) p ∂M.P.toMeasure := by
    change expectedAffineDirichletEnergy M ell U p = _
    unfold expectedAffineDirichletEnergy
    simp_rw [randomAMatrix, vecDot_aMatrix_eq_dirichletInfOn
      (aCutoffCoeffOnData M ell _ U) (fun _ => (Real.exp_pos _).le) p]
    exact integral_const_mul _ _
  rw [hleft, hright, hvol, hmean]

/-- Literal export for a retained-prefix induction at its initial scale.
The only unconstructed input is an origin-simplex geometric packing for each
permutation; stationarity supplies every triadic translation. -/
theorem exists_initialSimplexEnergy_all_cells_of_packing (d : ℕ) (K : ℝ) (hK : 1 ≤ K) :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∀ ell : ℕ, (∀ pi : Equiv.Perm (Fin d), Nonempty (InitialSimplexCubePacking ell pi K)) →
      ∀ (T : KuhnCell d), T.supportCube.scale = (ell : ℤ) → ∀ p : Vec d,
        (∫ omega, vecDot p (matVecMul
          (randomAMatrix M ell (kuhnCellDomain T) omega) p) ∂M.P.toMeasure) ≤
          C * ahom M ell * vecNormSq p := by
  obtain ⟨delta0, C, hdelta0, hC, henergy⟩ :=
    exists_initialSimplexEnergy_constants_of_packing d K hK
  refine ⟨delta0, C, hdelta0, hC, ?_⟩
  intro M hM ell hpack T hT p
  change expectedAffineDirichletEnergy M ell (kuhnCellDomain T) p ≤ _
  rw [expectedAffineDirichletEnergy_simplex_eq_origin M ell T hT p]
  exact henergy M hM ell T.order (Classical.choice (hpack T.order)) p

end
end SubdiffusiveProcess.Section10
