module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.OscillationEnergyFrame

@[expose] public section

/-!
# Row 2's `hO` leg at the *interior* good scale: the centre is its own comparator

`ss.good.scale.estimates` and `ss.regularity.iteration` fixes a comparison point `y'` with
`U_{m,m'}(z) ⊆ y' + cu_{m'} ⊆ cu_m` because in general the truncated window is
not a translate of a cube.  **On the interior branch that detour is
unnecessary**: at a base point one scale inside the domain and a window scale at
least five below it, the window does not touch the boundary, so

```text
  truncatedCube d m top z = translatedCube d top z ,
```

and the comparator may be taken to be `z` itself.  The off-grid containment
hypothesis of `OscillationEnergyFrame.exists_interiorOscillationEnergyFrame` then
degenerates to `translateSet 0 _ ⊆ _`, i.e. to the scale monotonicity of the
half-open cubes.

This is the form row 2's assembly consumes: the *good scale* is `top + 4` (the
harmonic-approximation anchor sits two scales above the comparison cube, whose
own index is two below the anchor's), and the conclusion is stated with the
frozen normalization `3 ^ (-top)`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open Homogenization hiding Vec
open Homogenization.Book

noncomputable section

variable {d : ℕ}

/-- The Besov scale weight at exponent `1` on an origin cube is the frozen
normalization `3 ^ (-k)`. -/
theorem cubeBesovScaleWeight_one_originCube (d : ℕ) (k : ℤ) :
    cubeBesovScaleWeight (1 : ℝ) (originCube d k) = (3 : ℝ) ^ (-k) := by
  unfold cubeBesovScaleWeight
  rw [cubeScaleFactor_originCube, ← Real.rpow_intCast (3 : ℝ) k,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    ← Real.rpow_intCast (3 : ℝ) (-k)]
  congr 1
  push_cast
  ring

/-- The half-open origin cubes are nested in the scale. -/
theorem cubeSet_originCube_subset_of_le {d : ℕ} {k l : ℤ} (hkl : k ≤ l) :
    cubeSet (originCube d k) ⊆ cubeSet (originCube d l) := by
  intro x hx
  rw [mem_cubeSet_originCube_iff] at hx ⊢
  intro i
  have h := hx i
  have hpow : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ l :=
    zpow_le_zpow_right₀ (by norm_num) hkl
  constructor
  · linarith only [h.1, hpow]
  · linarith only [h.2, hpow]

/-- **Row 2's oscillation leg at an interior good scale.**  The comparator is the
centre itself, and the conclusion carries the frozen normalization. -/
theorem exists_interiorOscillationEnergyWindow (d : ℕ) [NeZero d] :
    ∃ Kosc : ℝ, 0 ≤ Kosc ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L top : ℕ, top + 4 ≤ L →
      ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, ∀ z : Vec d,
        omega ∈ goodEvent M none (top + 4) z 1 (s / 8) →
      ∀ v : H1Function (translateSet z (openCubeSet (originCube d (top : ℤ)))),
        Real.sqrt
            (tailAverage M L (top + 4) omega
              (translatedCube d ((top : ℤ) + 4) z)) *
            ((3 : ℝ) ^ (-(top : ℤ)) *
              normalizedL2On
                (translateSet z (openCubeSet (originCube d (top : ℤ))))
                (fun p ↦ v.toFun p -
                  volumeAverage
                    (translateSet z (openCubeSet (originCube d (top : ℤ))))
                    v.toFun)) ≤
          Kosc *
            vectorNormalizedL2On
              (translateSet z (openCubeSet (originCube d (top : ℤ))))
              (fun p ↦ Real.sqrt (_root_.SubdiffusiveProcess.Model.aCutoff M L omega p) •
                v.grad p) := by
  obtain ⟨Kosc, hKosc0, hleg⟩ := exists_interiorOscillationEnergyFrame d
  refine ⟨Kosc, hKosc0, ?_⟩
  intro M s hs L top hL omega z hgoodEvent v
  have hn2 : (((top + 2 : ℕ) : ℤ) - 2) = (top : ℤ) := by push_cast; ring
  have hn2' : (((top + 2 : ℕ) : ℤ) + 2) = (top : ℤ) + 4 := by push_cast; ring
  have hcontain :
      translateSet (z - z) (cubeSet (originCube d (((top + 2 : ℕ) : ℤ) - 2))) ⊆
        cubeSet (originCube d (((top + 2 : ℕ) : ℤ) + 2)) := by
    rw [sub_self, translateSet_zero, hn2, hn2']
    exact cubeSet_originCube_subset_of_le (by omega)
  have hgood' : omega ∈ goodEvent M none ((top + 2) + 2) z 1 (s / 8) := by
    simpa [show (top + 2) + 2 = top + 4 by omega] using hgoodEvent
  have h := hleg M s hs L (top + 2) (by omega) omega z z hcontain hgood'
  rw [hn2, hn2'] at h
  have h' := h v
  rwa [cubeBesovScaleWeight_one_originCube d (top : ℤ)] at h'

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
