import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.TopGoodScale
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.TopGoodScale
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.EnergyScaleTransfer
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.EnergyIntegrability
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.WindowDomain
import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.CubeGeometry
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows.OscillationEnergyWindow

/-!
# Row 2's `hO` leg at the selected top window, against the **global** energy

Three landed facts turn `OscillationEnergyWindow.exists_interiorOscillationEnergyWindow_cut`
into the shape row 2's assembly consumes.

* At an interior centre and a window scale at least five below the domain the
  truncation collapses, `truncatedCube d m top z = translatedCube d top z`, and
  the window is `translateSet z (openCubeSet (originCube d top))` — so the leg's
  domain *is* the frozen window (`Section6TheoremC.truncatedCube_eq_translatedCube`,
  `Section6SchauderDatum.image_add_eq_translateSet`).
* The frozen solution restricts to it with `H1Function.restrict`, whose value
  and gradient are definitionally the original ones.
* The window energy is dominated by the **domain** energy at the cross-centre
  volume ratio (`Section6Holder.normalizedL2On_truncatedCube_crossCentre_le`
  with the second centre at the origin, where `truncatedCube d m m 0 = cube d m`).

The result is the manuscript's

```text
  (b_{L,m'+2})^{1/2} 3^{-m'} ‖u - (u)_{U_{m,m'}(z)}‖ ≤ C 3^{d(m-m')/2}
      ‖a_L^{1/2} ∇u‖_{L²(cu_m)} ,
```

with `m - m' ≤ K + 5` from the top good-scale selection, so the geometric price
is of the `exp(C lambda (m-n))` type the ladder already absorbs.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows

open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}
variable {L : ℕ}

/-- The centred cube is its own translate at the origin. -/
theorem translatedCube_zero_eq_cube_cut (d : ℕ) (k : ℤ) :
    translatedCube d k 0 = cube d k := by
  unfold translatedCube
  simp

/-- The own-scale truncated window at the origin is the domain cube. -/
theorem truncatedCube_self_zero_cut (d : ℕ) (m : ℤ) :
    truncatedCube d m m 0 = cube d m := by
  rw [Section6ExcessDecay.truncatedCube_eq, translatedCube_zero_eq_cube_cut,
    Set.inter_self]

/-- The frozen window at an interior centre is a translate of an origin cube. -/
theorem truncatedCube_eq_translateSet_of_interior_cut {m top : ℤ} {z : Vec d}
    (hz : z ∈ cube d (m - 1)) (htop : top ≤ m - 5) :
    truncatedCube d m top z = translateSet z (openCubeSet (originCube d top)) := by
  have hsub : translatedCube d top z ⊆ cube d m :=
    translatedCube_subset_cube_of_interior hz htop le_rfl
  rw [Section6TheoremC.truncatedCube_eq_translatedCube hsub]
  unfold translatedCube
  rw [Section6SchauderDatum.image_add_eq_translateSet]
  rfl

/-- **Row 2's oscillation leg at the selected top window.** -/
theorem exists_interiorTopWindowOscillationEnergy_cut (d : ℕ) [NeZero d] :
    ∃ Kosc : ℝ, 0 ≤ Kosc ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
        64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ C1 C2 alpha : ℝ,
        0 ≤ Section6Stopping.holderStoppingEpsilon C2 alpha →
        Section6Stopping.holderStoppingEpsilon C2 alpha ≤ 1 →
      ∀ step L m n K : ℕ, ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d,
      ∀ z : Vec d, OnTriadicGrid n z → z ∈ cube d ((m : ℤ) - 1) →
        (Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
            (Section6Stopping.holderStoppingLambda C1 alpha)
            (Section6Stopping.holderStoppingEpsilon C2 alpha) step m omega : ℤ) ≤
          (m : ℤ) - (n : ℤ) →
        n + K + 5 ≤ m →
        1 + Section6Stopping.holderStoppingLambda C1 alpha *
          ((m : ℝ) - (n : ℝ)) ≤ (K : ℝ) + 1 →
      ∀ u : H1Function (openCubeSet (originCube d (m : ℤ))),
        ∃ top : ℕ, n ≤ top ∧ top + 5 ≤ m ∧ m ≤ top + K + 5 ∧
          Real.sqrt (tailAverage M L (top + 4) omega
              (translatedCube d ((top : ℤ) + 4) z)) *
              ((3 : ℝ) ^ (-(top : ℤ)) *
                normalizedL2On (truncatedCube d (m : ℤ) (top : ℤ) z)
                  (fun p ↦ u.toFun p -
                    averageOn (truncatedCube d (m : ℤ) (top : ℤ) z) u.toFun)) ≤
            Kosc * scaleTransferPrice d ((m : ℤ) - (top : ℤ)) *
              vectorNormalizedL2On (cube d (m : ℤ))
                (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
                  u.grad p) := by
  obtain ⟨Kosc, hKosc0, hleg⟩ := exists_interiorOscillationEnergyWindow_cut d
  refine ⟨Kosc, hKosc0, ?_⟩
  intro M hsmall C1 C2 alpha heps0 heps1 step L m n K omega z hzgrid hz
    hstop hwin hroom u
  have hzm : z ∈ cube d (m : ℤ) := mem_cube_of_mem_cube_sub_one hz
  obtain ⟨top, hntop, htopm, hmtop, hgood⟩ :=
    exists_topGoodScale_cut M C1 C2 alpha step m n K omega z hzgrid hzm hstop
      heps0 heps1 hwin hroom
  refine ⟨top, hntop, htopm, hmtop, ?_⟩
  -- the window is a translate of an origin cube
  have htop5 : (top : ℤ) ≤ (m : ℤ) - 5 := by
    have : (top : ℤ) + 5 ≤ (m : ℤ) := by exact_mod_cast htopm
    omega
  have hWeq : truncatedCube d (m : ℤ) (top : ℤ) z =
      translateSet z (openCubeSet (originCube d (top : ℤ))) :=
    truncatedCube_eq_translateSet_of_interior_cut hz htop5
  have hWopen : IsOpen (translateSet z (openCubeSet (originCube d (top : ℤ)))) :=
    ((Homogenization.isOpenBoundedConvexDomain_openCubeSet
      (originCube d (top : ℤ))).translateSet z).isOpen
  have hWsub : translateSet z (openCubeSet (originCube d (top : ℤ))) ⊆
      openCubeSet (originCube d (m : ℤ)) := by
    rw [← hWeq]
    exact Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ) (top : ℤ) z
  -- the leg, on the restriction of the frozen solution
  have hgood' : omega ∈ goodEvent M (some L) (top + 4) z 1 ((1 / 4 : ℝ) / 8) := by
    have : (1 / 4 : ℝ) / 8 = Section6Stopping.holderStoppingS := by
      norm_num [Section6Stopping.holderStoppingS]
    rw [this]
    exact hgood
  have hs : (1 / 4 : ℝ) ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ) := by
    refine ⟨?_, le_rfl⟩
    have := hsmall
    rw [Section6Stopping.holderStoppingS] at this
    linarith only [this]
  have hlegApplied := hleg M (1 / 4 : ℝ) hs L top omega z hgood'
    (u.restrict hWopen hWsub)
  -- the window energy against the domain energy
  have hzero : (0 : Vec d) ∈ cube d (m : ℤ) := by
    have : (0 : Vec d) ∈ translatedCube d (m : ℤ) 0 :=
      Section6TheoremC.mem_translatedCube_self d (m : ℤ) 0
    rwa [translatedCube_zero_eq_cube_cut] at this
  have hint := integrableOn_weightedGrad_sq M L omega (m : ℤ) u (m : ℤ) 0
  have henergy :
      vectorNormalizedL2On (truncatedCube d (m : ℤ) (top : ℤ) z)
          (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
            u.grad p) ≤
        scaleTransferPrice d ((m : ℤ) - (top : ℤ)) *
          vectorNormalizedL2On (cube d (m : ℤ))
            (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
              u.grad p) := by
    have hraw := Section6Holder.normalizedL2On_truncatedCube_crossCentre_le
      (d := d) (m := (m : ℤ)) (j := (top : ℤ)) (ell := (m : ℤ)) (x := z) (z := 0)
      (f := fun p ↦ Homogenization.euclideanNorm
        (Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) • u.grad p))
      hzm hzero (by omega) (by omega)
      (by rw [truncatedCube_self_zero_cut]
          exact Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ) (top : ℤ) z)
      (by rw [truncatedCube_self_zero_cut]
          simpa [truncatedCube_self_zero_cut] using hint)
    rw [truncatedCube_self_zero_cut] at hraw
    have hcast : ((m : ℤ) - (top : ℤ) + 2) = (m : ℤ) - (top : ℤ) + 2 := rfl
    simpa [vectorNormalizedL2On, scaleTransferPrice, hcast] using hraw
  rw [hWeq]
  refine hlegApplied.trans ?_
  have hgradEq : (u.restrict hWopen hWsub).grad = u.grad := rfl
  rw [hgradEq, ← hWeq]
  calc Kosc *
        vectorNormalizedL2On (truncatedCube d (m : ℤ) (top : ℤ) z)
          (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
            u.grad p)
      ≤ Kosc * (scaleTransferPrice d ((m : ℤ) - (top : ℤ)) *
          vectorNormalizedL2On (cube d (m : ℤ))
            (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
              u.grad p)) := mul_le_mul_of_nonneg_left henergy hKosc0
    _ = Kosc * scaleTransferPrice d ((m : ℤ) - (top : ℤ)) *
          vectorNormalizedL2On (cube d (m : ℤ))
            (fun p ↦ Real.sqrt (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p) •
              u.grad p) := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows
