module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCrossScalePrices

@[expose] public section

/-!
# Integrated prices for the canonical boundary cutoff

These lemmas record the elementary endpoint of each separated density leg
under scalar coefficient caps.  The good-scale consumer must replace the
pointwise caps by the manuscript's multiscale ellipticity estimates; these
results do not make that replacement silently.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem integrableOn_const_mul_vecNormSq
    {Q : TriadicCube d} {F : Vec d → Vec d} (hF : MemVectorL2 (openCubeSet Q) F)
    (c : ℝ) :
    IntegrableOn (fun x ↦ c * vecNormSq (F x)) (openCubeSet Q) := by
  have hsq : IntegrableOn (fun x ↦ vecNormSq (F x)) (openCubeSet Q) := by
    simpa [vecNormSq] using integrableOn_vecDot_of_memVectorL2 hF hF
  exact hsq.const_mul c

private theorem integrableOn_const_mul_sq
    {Q : TriadicCube d} {f : Vec d → ℝ} (hf : MemScalarL2 (openCubeSet Q) f)
    (c : ℝ) :
    IntegrableOn (fun x ↦ c * f x ^ 2) (openCubeSet Q) := by
  have hsq : IntegrableOn (fun x ↦ f x ^ 2) (openCubeSet Q) := by
    simpa [pow_two, IntegrableOn, volumeMeasureOn] using! hf.integrable_mul hf
  exact hsq.const_mul c

/-- Datum density under an upper scalar-coefficient cap. -/
theorem volumeAverage_boundaryCoerciveDatumDensity_localCanonicalFun_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q R : TriadicCube d) (center : Vec d) {rhoInner rhoOuter Lam : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (h : H1Function (openCubeSet Q))
    (hLam : ∀ x ∈ openCubeSet Q,
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x ≤ Lam) :
    volumeAverage (openCubeSet Q)
        (boundaryCoerciveDatumDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
          (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter)
          h.grad) ≤
      volumeAverage (openCubeSet Q) (fun x ↦ Lam * vecNormSq (h.grad x)) := by
  apply volumeAverage_boundaryCoerciveDatumDensity_le
    (measurableSet_openCubeSet Q)
  · simpa only [boundaryCoerciveDatumDensity] using!
      integrableOn_aCutoff_sqCutoff_vecNormSq M L omega h.grad_memVectorL2
        (coarseCaccioppoliLocalCanonicalFun_smooth R center hinner hinnerOuter)
        (coarseCaccioppoliLocalCanonicalFun_hasCompactSupport R center hinner
          hinnerOuter)
  · exact integrableOn_const_mul_vecNormSq h.grad_memVectorL2 Lam
  · intro x _
    exact (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le
  · exact hLam
  · intro x _
    exact coarseCaccioppoliLocalCanonicalFun_nonneg R center rhoInner rhoOuter x
  · intro x _
    exact coarseCaccioppoliLocalCanonicalFun_le_one R center rhoInner rhoOuter x

/-- Cutoff-gradient density under an upper scalar-coefficient cap, with the
canonical cutoff's explicit squared-gradient factor. -/
theorem volumeAverage_boundaryCoerciveCutoffDensity_localCanonicalFun_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q R : TriadicCube d) (center : Vec d) {rhoInner rhoOuter Lam : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (w : Vec d → ℝ) (hw : MemScalarL2 (openCubeSet Q) w)
    (hLam : ∀ x ∈ openCubeSet Q,
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x ≤ Lam) :
    volumeAverage (openCubeSet Q)
        (boundaryCoerciveCutoffDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
          (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter) w) ≤
      volumeAverage (openCubeSet Q) (fun x ↦
        Lam * ((d : ℝ) *
          (quantitativeCubeCutoffGradientConst d /
            ((rhoOuter - rhoInner) * (cubeRadius R / 3))) ^ 2) * w x ^ 2) := by
  apply volumeAverage_le_volumeAverage_of_le_on (measurableSet_openCubeSet Q)
  · exact integrableOn_aCutoff_boundaryCoerciveCutoffDensity M L omega hw
      (coarseCaccioppoliLocalCanonicalFun_smooth R center hinner hinnerOuter)
      (coarseCaccioppoliLocalCanonicalFun_hasCompactSupport R center hinner
        hinnerOuter)
  · exact integrableOn_const_mul_sq hw
      (Lam * ((d : ℝ) *
        (quantitativeCubeCutoffGradientConst d /
          ((rhoOuter - rhoInner) * (cubeRadius R / 3))) ^ 2))
  · intro x hx
    exact boundaryCoerciveCutoffDensity_localCanonicalFun_le R center
      hinner hinnerOuter (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le
      (hLam x hx)

/-- Force density under a positive lower scalar-coefficient cap. -/
theorem volumeAverage_boundaryCoerciveForceDensity_localCanonicalFun_le
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q R : TriadicCube d) (center : Vec d) {rhoInner rhoOuter lam : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (g : Vec d → Vec d) (hg : MemVectorL2 (openCubeSet Q) g)
    (hlam : 0 < lam)
    (hlower : ∀ x ∈ openCubeSet Q,
      lam ≤ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) :
    volumeAverage (openCubeSet Q)
        (boundaryCoerciveForceDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
          (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter) g) ≤
      volumeAverage (openCubeSet Q) (fun x ↦ lam⁻¹ * vecNormSq (g x)) := by
  apply volumeAverage_boundaryCoerciveForceDensity_le
    (measurableSet_openCubeSet Q)
  · exact integrableOn_aCutoff_boundaryCoerciveForceDensity M L omega hg
      (coarseCaccioppoliLocalCanonicalFun_smooth R center hinner hinnerOuter)
      (coarseCaccioppoliLocalCanonicalFun_hasCompactSupport R center hinner
        hinnerOuter)
  · exact integrableOn_const_mul_vecNormSq hg lam⁻¹
  · exact hlam
  · exact hlower
  · intro x _
    exact coarseCaccioppoliLocalCanonicalFun_nonneg R center rhoInner rhoOuter x
  · intro x _
    exact coarseCaccioppoliLocalCanonicalFun_le_one R center rhoInner rhoOuter x

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
