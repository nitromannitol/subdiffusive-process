module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.AnchorInterior
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.ExcessDecayAdapter

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6SealAdapters

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

noncomputable section

/-- **The exact residue of link 2.**  Every interior weak solution on `□_m`
admits a Dirichlet datum with Hölder gradient.

This is *not* free: the only two canonical candidates both fail.  `h := u`
satisfies the zero-trace requirement (the difference is the zero
`H10Function`) but then demands `MemHolder (cube d m) (1/2) u.grad`, Hölder
continuity of the solution's own gradient on all of `□_m` — which is what the
Hölder ladder consuming this input exists to prove, so taking it here is
circular.  `h := 0` satisfies the Hölder requirement but demands that `u`
itself have zero trace on `∂□_m`, which no hypothesis of
`InteriorHolderExcessDecayInput` provides. -/
def InteriorExcessDecayDatum (d : ℕ) : Prop :=
  ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (u : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
    IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω) (cube d m) u g →
    ∃ h : H1Function (openCubeSet (originCube d m)),
      IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω)
          (originCube d m) u h g ∧
        MemHolder (cube d m) (1 / 2) h.grad

/-- **Link 2 reduces to the datum and nothing else.**  Hypothesis-shaped on the
harmonic-approximation input in exactly the way the excess-decay provider is,
so that when the harmonic input is supplied, `hharm` is discharged by the same term through
`Section6SealAdapters.harmonicApproximationInput_of_neZero`. -/
theorem interiorHolderExcessDecayInput_of_anchors_of_datum (d : ℕ)
    (hharm : HarmonicApproximationInput d) (hcap : MathcalECapInput d)
    (hdatum : InteriorExcessDecayDatum d) :
    InteriorHolderExcessDecayInput d := by
  obtain ⟨C, hC, hstep⟩ := excess_decay_good_scales_interior d hharm hcap
  refine ⟨C, hC, ?_⟩
  intro M s hs epsilon heps k hk L m n hkn hmL hnm x hx z hz hxz hnbt ω u g
    hsol hg ell hell
  obtain ⟨h, hdir, hhold⟩ := hdatum M L m ω u g hsol
  have hgate : translatedCube d ((n : ℤ) - 4) x ⊆ cube d m :=
    translatedCube_subset_cube_of_not_boundaryTouches hx (by omega) hnbt
  have hmain := hstep M s hs epsilon heps k hk L m n hkn hmL hnm x hx z hz hxz
    hgate ω u h g hdir hg hhold ell hell
  simpa only [ite_eq_right hnbt, add_zero] using hmain

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6SealAdapters
