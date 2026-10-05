module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCoerciveIntegrability

@[expose] public section

/-!
# Cross-scale localized boundary energy profile

The ambient weak equation is posed on a scale-`m` cube, whereas the boundary
cutoff in harmonic approximation is centered at a scale-`n` projected cell.
This module separates those two cubes.  The normalization remains the ambient
volume, so the standard radius iteration applies before the final bounded
volume-ratio conversion.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Ambient-volume-normalized energy in a local cube based on a separate
reference scale. -/
def boundaryCrossScaleEnergyProfile (Q R : TriadicCube d) (center : Vec d)
    (rho : ℝ) (energy : Vec d → ℝ) : ℝ :=
  volumeAverage (openCubeSet Q)
    ((coarseCaccioppoliLocalClosedCube R center rho).indicator energy)

/-- The cross-scale local profile is bounded by the squared canonical-cutoff
energy. -/
theorem boundaryCrossScaleEnergyProfile_le_boundaryCoerciveMain
    {Q R : TriadicCube d} {center : Vec d} {rhoInner rhoOuter : ℝ}
    {a : Vec d → ℝ} {u : H1Function (openCubeSet Q)}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (ha : ∀ x ∈ openCubeSet Q, 0 ≤ a x)
    (henergy : IntegrableOn (fun x => a x * vecNormSq (u.grad x))
      (openCubeSet Q))
    (hmain : IntegrableOn
      (boundaryCoerciveMainDensity a
        (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter) u.grad)
      (openCubeSet Q)) :
    boundaryCrossScaleEnergyProfile Q R center rhoInner
        (fun x => a x * vecNormSq (u.grad x)) ≤
      volumeAverage (openCubeSet Q)
        (boundaryCoerciveMainDensity a
          (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter)
          u.grad) := by
  apply volumeAverage_le_volumeAverage_of_le_on (measurableSet_openCubeSet Q)
    (henergy.indicator
      (measurableSet_coarseCaccioppoliLocalClosedCube R center rhoInner))
    hmain
  intro x hxQ
  by_cases hx : x ∈ coarseCaccioppoliLocalClosedCube R center rhoInner
  · have heta := coarseCaccioppoliLocalCanonicalFun_eq_one_on_inner
      hinner hinnerOuter hx
    simp [Set.indicator_of_mem hx, boundaryCoerciveMainDensity, heta]
  · rw [Set.indicator_of_notMem hx]
    exact mul_nonneg (mul_nonneg (ha x hxQ) (sq_nonneg _))
      (vecNormSq_nonneg _)

/-- Localized nonzero-datum coercivity with the cutoff scale independent of
the ambient equation scale. -/
theorem boundaryCrossScaleEnergyProfile_le_aCutoff_coerciveTerms
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {Q R : TriadicCube d} {center : Vec d} {rhoInner rhoOuter : ℝ}
    {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hweak : IsDivFormWeakSolutionOn
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (openCubeSet Q) u g)
    (hg : MemVectorL2 (openCubeSet Q) g)
    {V : Set (Vec d)}
    (hzero : LocalizedZeroTraceFunctionOn (openCubeSet Q) V
      (fun y => u.toFun y - h.toFun y))
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (houterV : coarseCaccioppoliLocalClosedCube R center rhoOuter ⊆ V) :
    boundaryCrossScaleEnergyProfile Q R center rhoInner
        (fun x => _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
          vecNormSq (u.grad x)) ≤
      4 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveDatumDensity
            (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter)
            h.grad) +
        14 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveCutoffDensity
            (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter)
            (fun y => u.toFun y - h.toFun y)) +
        8 * volumeAverage (openCubeSet Q)
          (boundaryCoerciveForceDensity
            (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter) g) := by
  let eta := coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter
  have heta : ContDiff ℝ (⊤ : ℕ∞) eta :=
    coarseCaccioppoliLocalCanonicalFun_smooth R center hinner hinnerOuter
  have hetaCompact : HasCompactSupport eta :=
    coarseCaccioppoliLocalCanonicalFun_hasCompactSupport R center hinner hinnerOuter
  have hetaSupport : tsupport eta ⊆ V :=
    (coarseCaccioppoliLocalCanonicalFun_tsupport_subset_localClosedCube
      hinner hinnerOuter).trans houterV
  have henergy := integrableOn_aCutoff_energy M L omega Q u
  have hmain : IntegrableOn
      (boundaryCoerciveMainDensity
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta u.grad)
      (openCubeSet Q) := by
    simpa only [boundaryCoerciveMainDensity] using!
      integrableOn_aCutoff_sqCutoff_vecNormSq M L omega u.grad_memVectorL2
        heta hetaCompact
  have hlower := boundaryCrossScaleEnergyProfile_le_boundaryCoerciveMain
    hinner hinnerOuter
    (fun x _ => (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x).le)
    henergy hmain
  have hcoercive :=
    setIntegral_aCutoff_boundaryCoerciveMain_le_of_localizedZeroTrace
      M L omega hweak hg hzero heta hetaCompact hetaSupport
  unfold volumeAverage at hlower ⊢
  have hvol : 0 ≤ (volume (openCubeSet Q)).toReal⁻¹ :=
    inv_nonneg.mpr ENNReal.toReal_nonneg
  have hscaled := mul_le_mul_of_nonneg_left hcoercive hvol
  exact hlower.trans (hscaled.trans_eq (by ring))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
