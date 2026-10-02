import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEnergy
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryRegularity

/-!
# Boundary-cell energy for the harmonic-approximation cover

This is the local analytic payload of the manuscript's boundary-cell argument.
The rough Dirichlet problem is transported to the well-placed cube, its datum
is lifted by the Chapter-3 Dirichlet theory, and boundary Caccioppoli is applied
at the admissible parameters `(1/2, s/3)`.  This is the slot used by the
mirrored Algsuperdiff assembly: its finite-`2` companion is `s/6`, exactly the
local-control index supplied by the manuscript's good-scale estimate.

PROVENANCE: this is the GMC specialization of the composition split across
`Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryEnergyRebaseWindow.lean`
and `AssemblyEnergyLeg.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

/-- Boundary Caccioppoli on one well-placed cube, with the exact transported
inhomogeneous fractional data retained in the Chapter-3 RHS. -/
theorem exists_projectedBoundaryCellEnergy (d : ℕ) [NeZero d] :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        (m : ℕ) (k : ℤ) (q : Vec d) (sOrder : FractionalOrder)
        (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d),
        IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (originCube d (m : ℤ)) u h g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two h.grad →
        k ≤ (m : ℤ) → q ∈ cube d (m : ℤ) →
        ∃ g0 : Vec d → Vec d,
          ∃ u0 h0 : H1Function (openCubeSet (originCube d k)),
          ∃ v : DirichletForcedCubeSolution
              (originCube d k)
              (aCutoffFamily M L
                (translatePotentialSample
                  (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) omega))
              (fun x ↦ -g0 x),
            (∀ x, g0 x = g (x +
              Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)) ∧
            (∀ x, u0.toFun x = u.toFun (x +
              Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)) ∧
            Ch03.ABK26.MemCubeEuclideanFullWsp (originCube d k) sOrder
              FiniteLpExponent.two (fun x => g (x +
                Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)) ∧
            (∀ x, u0.grad x = u.grad (x +
              Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)) ∧
            IsForcedEquation (originCube d k)
                (aCutoffFamily M L
                  (translatePotentialSample
                    (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) omega))
                u0 (fun x ↦ -g0 x) ∧
            v.boundaryData = h0 ∧
            (∀ x, h0.toFun x = h.toFun (x +
              Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)) ∧
            (∀ x, h0.grad x = h.grad (x +
              Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)) ∧
            Ch03.ABK26.MemCubeEuclideanFullWsp (originCube d k) sOrder
              FiniteLpExponent.two (fun x => h.grad (x +
                Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)) ∧
            Ch01.LocalizedZeroTraceFunctionOn
                (openCubeSet (originCube d k))
                (openCubeAtScale
                  (q - Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) (k - 1))
                (fun y ↦ u0.toFun y - v.toH1.toFun y) ∧
            ForceBesovRegularity (originCube d k) sOrder.1 (fun x ↦ -g0 x) ∧
            ForceBesovRegularity (originCube d k) sOrder.1
              (dirichletBoundaryGradientField v) ∧
            localizedCoeffEnergyValue
                (caccioppoliCoreSet (originCube d k)
                  (q - Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k))
                ((aCutoffFamily M L
                  (translatePotentialSample
                    (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) omega)).coeffOn
                      (originCube d k)) u0 ≤
              2 * (caccioppoliWithRHSPrefactor C₁ (originCube d k)
                    (aCutoffFamily M L
                      (translatePotentialSample
                        (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) omega))
                    (1 / 2) (sOrder.1 / 3) *
                (Ch02.lambdaS (originCube d k) (sOrder.1 / 3)
                    (aCutoffFamily M L
                      (translatePotentialSample
                        (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) omega)) *
                  (3 : ℝ) ^ (-(2 * k)) *
                  normalizedL2SqOnSet (openCubeSet (originCube d k))
                    (fun y ↦ u0.toFun y - v.toH1.toFun y))) +
                2 * ((18 : ℝ) ^ d *
                  dirichletEnergyWithRHSRHS C₂ (originCube d k)
                    (aCutoffFamily M L
                      (translatePotentialSample
                        (Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) omega))
                    sOrder.1 (fun x ↦ -g0 x) v ^ 2) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, henergy⟩ :=
    exists_boundaryCaccioppoliEnergy_withBoundaryDatum d
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro M L omega m k q sOrder u h g hdir hg hh hkm hq
  obtain ⟨g0, u0, h0, v, hg0point, hu0val, hgLocal, hu0grad, hu0, hvh0,
      hh0val, hh0grad, hhLocal, htrace, hgBesov, hhBesov⟩ :=
    exists_projectedBoundaryDatum_regular M L omega m k q sOrder u h g
      hdir hg hh hkm
  let c : Vec d := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
  let Q : TriadicCube d := originCube d k
  let A : CoeffFamily d := aCutoffFamily M L (translatePotentialSample c omega)
  have hqtrunc : q ∈ truncatedCube d (m : ℤ) (k - 1) q :=
    Section6ExcessDecay.mem_truncatedCube_self (k - 1) hq
  have hqtranslated : q ∈ translatedCube d k c := by
    exact Section6ExcessDecay.truncatedCube_subset_translatedCube_wellPlacedCentre q
      hkm (by omega) hqtrunc
  have hx : q - c ∈ openCubeSet Q := by
    exact Section6ExcessDecay.mem_translatedCube_iff.mp hqtranslated
  have hs0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hs01 : (1 / 2 : ℝ) < 1 := by norm_num
  have ht : 0 < sOrder.1 / 3 := div_pos sOrder.2.1 (by norm_num)
  have ht2 : sOrder.1 / 3 < (1 : ℝ) / 2 := by
    have hs1 : sOrder.1 < 1 := sOrder.2.2
    linarith
  have hst : (1 / 2 : ℝ) + sOrder.1 / 3 < 1 := by
    have hs1 : sOrder.1 < 1 := sOrder.2.2
    linarith
  have hr := sOrder.2.1
  have hr1 := sOrder.2.2
  have hbound := henergy u0 v hu0 htrace hs0 hs01 ht ht2 hst
    hr hr1 hgBesov hhBesov hx
  exact ⟨g0, u0, h0, v, hg0point, hu0val, hgLocal, hu0grad, hu0, hvh0,
    hh0val, hh0grad, hhLocal, htrace, hgBesov, hhBesov, hbound⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
