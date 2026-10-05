module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCellCover
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCrossScaleCutoff
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCorrectedFluxRecurrence
public import Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.DescendantSummation.Averages
public import Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.QuantitativeCutoff.Basic

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- A descendant disjoint from the local cutoff support contributes no
corrected-flux pairing. -/
theorem cubeAverage_boundaryCorrectedFluxCutoffPairingDensity_eq_zero_of_disjoint
    {Q S : TriadicCube d} {center : Vec d} {rhoInner rhoOuter : ℝ}
    {a w : Vec d → ℝ} {U G : Vec d → Vec d}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (hdisjoint : ¬ ∃ x ∈ cubeSet S,
      x ∈ coarseCaccioppoliLocalClosedCube Q center rhoOuter) :
    cubeAverage S
        (boundaryCorrectedFluxCutoffPairingDensity a
          (coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter)
          w U G) = 0 := by
  rw [← cubeAverage_const (Q := S) (c := 0)]
  apply cubeAverage_congr_on_cubeSet
  intro x hx
  have hxOuter : x ∉ coarseCaccioppoliLocalClosedCube Q center rhoOuter := by
    intro hxMem
    exact hdisjoint ⟨x, hx, hxMem⟩
  let eta := coarseCaccioppoliLocalCanonicalFun Q center rhoInner rhoOuter
  have heta : ContDiff ℝ (⊤ : ℕ∞) eta :=
    coarseCaccioppoliLocalCanonicalFun_smooth Q center hinner hinnerOuter
  have hgrad : scalarCutoffGradientField eta x = 0 :=
    scalarCutoffGradientField_coarseCaccioppoliLocalCanonicalFun_eq_zero_of_notMem_localClosedCube
      hinner hinnerOuter hxOuter
  have hpoint := boundaryCorrectedFluxCutoffPairingDensity_eq
    (a := a) (eta := eta) (w := w) (U := U) (G := G) heta x
  rw [hpoint]
  have hEuclidean : euclideanGradient eta x = 0 := hgrad
  simp [hEuclidean, vecDot]

/-- The finite average of descendant energies localized by a projected
outer cube is exactly the ambient-normalized cross-scale energy profile. -/
theorem descendantsAverage_cubeAverage_indicator_localClosedCube_eq_crossScaleProfile
    (Q R : TriadicCube d) (center : Vec d) (j : ℕ) (rho : ℝ)
    (energy : Vec d → ℝ)
    (henergy : IntegrableOn energy (cubeSet Q) volume) :
    descendantsAverage Q j (fun S ↦
        cubeAverage S
          ((coarseCaccioppoliLocalClosedCube R center rho).indicator energy)) =
      boundaryCrossScaleEnergyProfile Q R center rho energy := by
  have hlocalized : IntegrableOn
      ((coarseCaccioppoliLocalClosedCube R center rho).indicator energy)
      (cubeSet Q) volume :=
    (henergy.indicator
      (measurableSet_coarseCaccioppoliLocalClosedCube R center rho))
  rw [boundaryCrossScaleEnergyProfile,
    volumeAverage_openCubeSet_eq_cubeAverage]
  exact
    (cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
      Q j
        ((coarseCaccioppoliLocalClosedCube R center rho).indicator energy)
        hlocalized).symm

/-- Finite Cauchy for a scalar local factor times the square root of a
cross-scale localized energy.  The resulting energy is the outer-radius
profile based on `R`, while the scalar `L²` norm remains normalized on `Q`. -/
theorem descendantsAverage_cubeLpNorm_two_mul_sqrt_indicator_le_crossScaleProfile
    (Q R : TriadicCube d) (center : Vec d) (j : ℕ) (rho : ℝ)
    (f energy : Vec d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (henergyNonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy : IntegrableOn energy (cubeSet Q) volume) :
    descendantsAverage Q j (fun S ↦
        cubeLpNorm S (2 : ℝ≥0∞) f *
          Real.sqrt (cubeAverage S
            ((coarseCaccioppoliLocalClosedCube R center rho).indicator energy))) ≤
      cubeLpNorm Q (2 : ℝ≥0∞) f *
        Real.sqrt (boundaryCrossScaleEnergyProfile Q R center rho energy) := by
  let localized : Vec d → ℝ :=
    (coarseCaccioppoliLocalClosedCube R center rho).indicator energy
  have hlocalizedNonneg : ∀ x ∈ cubeSet Q, 0 ≤ localized x := by
    intro x hx
    by_cases hmem : x ∈ coarseCaccioppoliLocalClosedCube R center rho
    · simpa [localized, Set.indicator_of_mem hmem] using henergyNonneg x hx
    · simp [localized, Set.indicator_of_notMem hmem]
  have hlocalized : IntegrableOn localized (cubeSet Q) volume :=
    henergy.indicator
      (measurableSet_coarseCaccioppoliLocalClosedCube R center rho)
  have hraw := descendantsAverage_cubeLpNorm_two_mul_sqrt_cubeAverage_le
    Q j f localized hf hlocalizedNonneg hlocalized
  have hprofile : cubeAverage Q localized =
      boundaryCrossScaleEnergyProfile Q R center rho energy := by
    rw [boundaryCrossScaleEnergyProfile,
      volumeAverage_openCubeSet_eq_cubeAverage]
  simpa only [localized, hprofile] using hraw

/-- Abstract finite-cell absorption.  Once every descendant pairing is
priced by one quarter of its outer-localized energy plus a local remainder,
the ambient pairing is priced by one quarter of the cross-scale outer profile
plus the finite average of those remainders. -/
theorem abs_cubeAverage_le_quarter_crossScaleProfile_add_descendantsAverage
    (Q R : TriadicCube d) (center : Vec d) (j : ℕ) (rho : ℝ)
    (pair energy : Vec d → ℝ) (remainder : TriadicCube d → ℝ)
    (hpair : IntegrableOn pair (cubeSet Q) volume)
    (henergy : IntegrableOn energy (cubeSet Q) volume)
    (hlocal : ∀ S ∈ descendantsAtDepth Q j,
      |cubeAverage S pair| ≤
        (1 / 4 : ℝ) * cubeAverage S
          ((coarseCaccioppoliLocalClosedCube R center rho).indicator energy) +
        remainder S) :
    |cubeAverage Q pair| ≤
      (1 / 4 : ℝ) * boundaryCrossScaleEnergyProfile Q R center rho energy +
        descendantsAverage Q j remainder := by
  have hsum := abs_cubeAverage_le_descendantsAverage_of_local_abs_bounds
    Q j pair (fun S ↦
      (1 / 4 : ℝ) * cubeAverage S
          ((coarseCaccioppoliLocalClosedCube R center rho).indicator energy) +
        remainder S) hpair hlocal
  rw [descendantsAverage_add_local] at hsum
  have hconst : descendantsAverage Q j (fun S ↦
      (1 / 4 : ℝ) * cubeAverage S
        ((coarseCaccioppoliLocalClosedCube R center rho).indicator energy)) =
      (1 / 4 : ℝ) * boundaryCrossScaleEnergyProfile Q R center rho energy := by
    rw [descendantsAverage_mul_left]
    congr 1
    exact
      descendantsAverage_cubeAverage_indicator_localClosedCube_eq_crossScaleProfile
        Q R center j rho energy henergy
  rw [hconst] at hsum
  exact hsum

/-- Support-buffer form of the finite-cell absorption theorem.  A descendant
which meets the cutoff support is contained in the slightly larger outer
profile; descendants which do not meet the support contribute zero.  Thus a
local estimate containing the *full* energy of each active descendant sums to
the localized outer profile, not to the full energy of `Q`. -/
theorem abs_cubeAverage_le_quarter_crossScaleProfile_of_supportBuffer
    (Q R : TriadicCube d) (center : Vec d) (j : ℕ)
    {rhoSupport rhoOuter : ℝ}
    (pair energy : Vec d → ℝ) (remainder : TriadicCube d → ℝ)
    (hpair : IntegrableOn pair (cubeSet Q) volume)
    (henergyNonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x)
    (henergy : IntegrableOn energy (cubeSet Q) volume)
    (hbuffer : ∀ S ∈ descendantsAtDepth Q j,
      cubeScaleFactor S ≤
        (rhoOuter - rhoSupport) * (cubeRadius R / 3))
    (hremainder : ∀ S ∈ descendantsAtDepth Q j, 0 ≤ remainder S)
    (hactive : ∀ S ∈ descendantsAtDepth Q j,
      (∃ y ∈ cubeSet S,
        y ∈ coarseCaccioppoliLocalClosedCube R center rhoSupport) →
      |cubeAverage S pair| ≤
        (1 / 4 : ℝ) * cubeAverage S energy + remainder S)
    (hinactive : ∀ S ∈ descendantsAtDepth Q j,
      ¬ (∃ y ∈ cubeSet S,
        y ∈ coarseCaccioppoliLocalClosedCube R center rhoSupport) →
      cubeAverage S pair = 0) :
    |cubeAverage Q pair| ≤
      (1 / 4 : ℝ) *
          boundaryCrossScaleEnergyProfile Q R center rhoOuter energy +
        descendantsAverage Q j remainder := by
  apply abs_cubeAverage_le_quarter_crossScaleProfile_add_descendantsAverage
    Q R center j rhoOuter pair energy remainder hpair henergy
  intro S hS
  by_cases hmeet : ∃ y ∈ cubeSet S,
      y ∈ coarseCaccioppoliLocalClosedCube R center rhoSupport
  · have hsubset : cubeSet S ⊆
        coarseCaccioppoliLocalClosedCube R center rhoOuter :=
      cubeSet_subset_coarseCaccioppoliLocalClosedCube_of_intersects_of_scaleFactor_le_gap
        (hbuffer S hS) hmeet
    have hlocalized : cubeAverage S
          ((coarseCaccioppoliLocalClosedCube R center rhoOuter).indicator energy) =
        cubeAverage S energy := by
      apply cubeAverage_congr_on_cubeSet
      intro x hx
      simp [Set.indicator_of_mem (hsubset hx)]
    rw [hlocalized]
    exact hactive S hS hmeet
  · rw [hinactive S hS hmeet, abs_zero]
    have hlocalizedNonneg : 0 ≤ cubeAverage S
        ((coarseCaccioppoliLocalClosedCube R center rhoOuter).indicator energy) := by
      apply cubeAverage_nonneg_of_nonneg_on
      intro x hx
      by_cases hmem : x ∈ coarseCaccioppoliLocalClosedCube R center rhoOuter
      · simpa [Set.indicator_of_mem hmem] using
          henergyNonneg x (cubeSet_subset_of_mem_descendantsAtDepth hS hx)
      · simp [Set.indicator_of_notMem hmem]
    exact add_nonneg
      (mul_nonneg (by norm_num) hlocalizedNonneg) (hremainder S hS)

/-- The support-buffer summation in the literal corrected-flux density and
open-cube normalization consumed by the radius recurrence. -/
theorem volumeAverage_boundaryCorrectedFluxCutoffPairing_le_outerProfile_of_localCells
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q R : TriadicCube d) (center : Vec d) (j : ℕ)
    {rhoInner rhoSupport rhoOuter : ℝ}
    (u h : H1Function (openCubeSet Q)) (g : Vec d → Vec d)
    (remainder : TriadicCube d → ℝ)
    (hrhoInner : 0 < rhoInner) (hrhoSupport : rhoInner < rhoSupport)
    (hpair : IntegrableOn
      (boundaryCorrectedFluxCutoffPairingDensity
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
        (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoSupport)
        (fun y ↦ u.toFun y - h.toFun y) u.grad g)
      (cubeSet Q) volume)
    (henergy : IntegrableOn (fun x ↦
      _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (u.grad x))
      (cubeSet Q) volume)
    (hbuffer : ∀ S ∈ descendantsAtDepth Q j,
      cubeScaleFactor S ≤
        (rhoOuter - rhoSupport) * (cubeRadius R / 3))
    (hremainder : ∀ S ∈ descendantsAtDepth Q j, 0 ≤ remainder S)
    (hactive : ∀ S ∈ descendantsAtDepth Q j,
      (∃ y ∈ cubeSet S,
        y ∈ coarseCaccioppoliLocalClosedCube R center rhoSupport) →
      |cubeAverage S
          (boundaryCorrectedFluxCutoffPairingDensity
            (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoSupport)
            (fun y ↦ u.toFun y - h.toFun y) u.grad g)| ≤
        (1 / 4 : ℝ) * cubeAverage S (fun x ↦
          _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (u.grad x)) +
        remainder S) :
    |volumeAverage (openCubeSet Q)
        (boundaryCorrectedFluxCutoffPairingDensity
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
          (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoSupport)
          (fun y ↦ u.toFun y - h.toFun y) u.grad g)| ≤
      (1 / 4 : ℝ) * boundaryCrossScaleEnergyProfile Q R center rhoOuter
        (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
          vecNormSq (u.grad x)) +
        descendantsAverage Q j remainder := by
  rw [volumeAverage_openCubeSet_eq_cubeAverage]
  exact abs_cubeAverage_le_quarter_crossScaleProfile_of_supportBuffer
    Q R center j
      (boundaryCorrectedFluxCutoffPairingDensity
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
        (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoSupport)
        (fun y ↦ u.toFun y - h.toFun y) u.grad g)
      (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
        vecNormSq (u.grad x)) remainder hpair
      (fun x _ ↦ mul_nonneg
        (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x).le
        (vecNormSq_nonneg _)) henergy hbuffer hremainder hactive
      (fun S _ hdisjoint ↦
        cubeAverage_boundaryCorrectedFluxCutoffPairingDensity_eq_zero_of_disjoint
          hrhoInner hrhoSupport hdisjoint)

/-- The adaptive translated-cell summation used at one radius step.  A
triadic gap-scale choice supplies the exact depth `k+1`; the extra generation
is the local-patch factor `cubeRadius R / 3`.  Thus the absorbable full-cell
energies of all active cells sum to the consecutive-radius outer profile. -/
theorem volumeAverage_boundaryCorrectedFluxCutoffPairing_le_outerProfile_of_triadicGapChoice
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q R : TriadicCube d) (center : Vec d) {rhoInner rhoOuter : ℝ}
    (k : ℕ)
    (u h : H1Function (openCubeSet Q)) (g : Vec d → Vec d)
    (remainder : TriadicCube d → ℝ)
    (hrhoInner : 0 < rhoInner)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter)
    (hQR : cubeRadius Q ≤ cubeRadius R)
    (hpair : IntegrableOn
      (boundaryCorrectedFluxCutoffPairingDensity
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
        (coarseCaccioppoliLocalCanonicalFun R center rhoInner
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter))
        (fun y ↦ u.toFun y - h.toFun y) u.grad g)
      (cubeSet Q) volume)
    (henergy : IntegrableOn (fun x ↦
      _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (u.grad x))
      (cubeSet Q) volume)
    (hremainder : ∀ S ∈ descendantsAtDepth Q (k + 1), 0 ≤ remainder S)
    (hactive : ∀ S ∈ descendantsAtDepth Q (k + 1),
      (∃ y ∈ cubeSet S,
        y ∈ coarseCaccioppoliLocalClosedCube R center
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) →
      |cubeAverage S
          (boundaryCorrectedFluxCutoffPairingDensity
            (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner
              (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter))
            (fun y ↦ u.toFun y - h.toFun y) u.grad g)| ≤
        (1 / 4 : ℝ) * cubeAverage S (fun x ↦
          _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (u.grad x)) +
        remainder S) :
    |volumeAverage (openCubeSet Q)
        (boundaryCorrectedFluxCutoffPairingDensity
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
          (coarseCaccioppoliLocalCanonicalFun R center rhoInner
            (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter))
          (fun y ↦ u.toFun y - h.toFun y) u.grad g)| ≤
      (1 / 4 : ℝ) * boundaryCrossScaleEnergyProfile Q R center rhoOuter
        (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
          vecNormSq (u.grad x)) +
        descendantsAverage Q (k + 1) remainder := by
  have hlt : rhoInner < rhoOuter := by
    have hpow : 0 < ((3 : ℝ) ^ k)⁻¹ := by positivity
    have := hchoice.2
    linarith
  apply volumeAverage_boundaryCorrectedFluxCutoffPairing_le_outerProfile_of_localCells
    M L omega Q R center (k + 1) u h g remainder
      hrhoInner (coarseCaccioppoliBufferedCutoffRadius_between hlt).1
      hpair henergy
  · intro S hS
    have hbase :=
      cubeScaleFactor_le_local_buffer_of_mem_descendantsAtDepth_succ_of_triadicGapScaleChoice
        hS hchoice le_rfl
    have hgap : 0 ≤ rhoOuter -
        coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter := by
      rw [coarseCaccioppoliBufferedCutoffRadius_outer_gap]
      linarith
    exact hbase.trans (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hQR (by norm_num)) hgap)
  · exact hremainder
  · exact hactive

/-- The cross-scale energy profile is monotone in its radius. -/
theorem boundaryCrossScaleEnergyProfile_mono
    {Q R : TriadicCube d} {center : Vec d} {rho₁ rho₂ : ℝ}
    {energy : Vec d → ℝ} (hrho : rho₁ ≤ rho₂)
    (henergyNonneg : ∀ x ∈ openCubeSet Q, 0 ≤ energy x)
    (henergy : IntegrableOn energy (openCubeSet Q) volume) :
    boundaryCrossScaleEnergyProfile Q R center rho₁ energy ≤
      boundaryCrossScaleEnergyProfile Q R center rho₂ energy := by
  apply volumeAverage_le_volumeAverage_of_le_on (measurableSet_openCubeSet Q)
    (henergy.indicator
      (measurableSet_coarseCaccioppoliLocalClosedCube R center rho₁))
    (henergy.indicator
      (measurableSet_coarseCaccioppoliLocalClosedCube R center rho₂))
  intro x hxQ
  by_cases hx₁ : x ∈ coarseCaccioppoliLocalClosedCube R center rho₁
  · have hx₂ : x ∈ coarseCaccioppoliLocalClosedCube R center rho₂ := by
      intro i
      exact (hx₁ i).trans
        (mul_le_mul_of_nonneg_right hrho
          (div_nonneg (cubeRadius_nonneg R) (by norm_num)))
    simp [Set.indicator_of_mem hx₁, Set.indicator_of_mem hx₂]
  · rw [Set.indicator_of_notMem hx₁]
    by_cases hx₂ : x ∈ coarseCaccioppoliLocalClosedCube R center rho₂
    · rw [Set.indicator_of_mem hx₂]
      exact henergyNonneg x hxQ
    · simp [Set.indicator_of_notMem hx₂]

/-- Midpoint-buffered radius step.  The weak test ends at the buffered
midpoint, and monotonicity prices its main energy by the next full radius.
The translated-cell summation may therefore spend its quarter on that same
outer profile. -/
theorem boundaryCrossScale_bufferedHalfAbsorbable_of_correctedFluxPairing
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {Q R : TriadicCube d} {center : Vec d} {rhoInner rhoOuter : ℝ}
    {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hweak : IsDivFormWeakSolutionOn
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (openCubeSet Q) u g)
    (hg : MemVectorL2 (openCubeSet Q) g)
    (hzero : LocalizedZeroTraceFunctionOn (openCubeSet Q)
      (coarseCaccioppoliLocalOpenCube R center 1)
      (fun y ↦ u.toFun y - h.toFun y))
    (hinner : 0 < rhoInner) (hlt : rhoInner < rhoOuter) (houter : rhoOuter < 1)
    {Ad Ac Ag : ℝ}
    (hdatum : volumeAverage (openCubeSet Q)
        (boundaryCoerciveDatumDensity
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
          (coarseCaccioppoliLocalCanonicalFun R center rhoInner
            (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) h.grad) ≤ Ad)
    (hforce : volumeAverage (openCubeSet Q)
        (boundaryCoerciveForceDensity
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
          (coarseCaccioppoliLocalCanonicalFun R center rhoInner
            (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) g) ≤ Ag)
    (hpair : |volumeAverage (openCubeSet Q)
        (boundaryCorrectedFluxCutoffPairingDensity
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
          (coarseCaccioppoliLocalCanonicalFun R center rhoInner
            (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter))
          (fun y ↦ u.toFun y - h.toFun y) u.grad g)| ≤
        (1 / 4 : ℝ) * boundaryCrossScaleEnergyProfile Q R center rhoOuter
          (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
            vecNormSq (u.grad x)) + Ac) :
    boundaryCrossScaleEnergyProfile Q R center rhoInner
        (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
          vecNormSq (u.grad x)) ≤
      (1 / 2 : ℝ) * boundaryCrossScaleEnergyProfile Q R center rhoOuter
        (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
          vecNormSq (u.grad x)) +
        (5 / 2 : ℝ) * Ad + Ac + (5 / 2 : ℝ) * Ag := by
  have hbetween := coarseCaccioppoliBufferedCutoffRadius_between hlt
  have hbase := boundaryCrossScaleEnergyProfile_le_correctedFluxTerms
    M L omega hweak hg hzero hinner hbetween.1
      ((coarseCaccioppoliLocalClosedCube_subset_localOpenCube_one_of_lt_one
        (hbetween.2.trans houter)))
  let energy : Vec d → ℝ := fun x ↦
    _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (u.grad x)
  have henergyNonneg : ∀ x ∈ openCubeSet Q, 0 ≤ energy x := by
    intro x _
    exact mul_nonneg (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x).le
      (vecNormSq_nonneg _)
  have henergy : IntegrableOn energy (openCubeSet Q) volume := by
    simpa only [energy] using integrableOn_aCutoff_energy M L omega Q u
  have hmono := boundaryCrossScaleEnergyProfile_mono
    (Q := Q) (R := R) (center := center)
      (rho₁ := coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
      (rho₂ := rhoOuter) hbetween.2.le henergyNonneg henergy
  dsimp only [energy] at hmono
  linarith only [hbase, hdatum, hforce, hpair, hmono]



theorem boundaryCrossScaleEnergyProfile_oneThird_le_of_adaptiveLocalCells
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {Q R : TriadicCube d} {center : Vec d}
    {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hweak : IsDivFormWeakSolutionOn
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (openCubeSet Q) u g)
    (hg : MemVectorL2 (openCubeSet Q) g)
    (hzero : LocalizedZeroTraceFunctionOn (openCubeSet Q)
      (coarseCaccioppoliLocalOpenCube R center 1)
      (fun y ↦ u.toFun y - h.toFun y))
    (hQR : cubeRadius Q ≤ cubeRadius R)
    {Ad Ac Ag beta : ℝ}
    (hAd : 0 ≤ Ad) (hAc : 0 ≤ Ac) (hAg : 0 ≤ Ag) (hbeta : 0 ≤ beta)
    (hdatum : ∀ j : ℕ,
      let rhoInner := coarseCaccioppoliRadiusSequence j
      let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
      volumeAverage (openCubeSet Q)
          (boundaryCoerciveDatumDensity
            (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner
              (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) h.grad) ≤
        Ad * Real.rpow (rhoOuter - rhoInner) (-beta))
    (hforce : ∀ j : ℕ,
      let rhoInner := coarseCaccioppoliRadiusSequence j
      let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
      volumeAverage (openCubeSet Q)
          (boundaryCoerciveForceDensity
            (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner
              (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) g) ≤
        Ag * Real.rpow (rhoOuter - rhoInner) (-beta))
    (hlocal : ∀ j : ℕ,
      let rhoInner := coarseCaccioppoliRadiusSequence j
      let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
      ∃ k : ℕ, ∃ remainder : TriadicCube d → ℝ,
        CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter ∧
        (∀ S ∈ descendantsAtDepth Q (k + 1), 0 ≤ remainder S) ∧
        (∀ S ∈ descendantsAtDepth Q (k + 1),
          (∃ y ∈ cubeSet S,
            y ∈ coarseCaccioppoliLocalClosedCube R center
              (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) →
          |cubeAverage S
              (boundaryCorrectedFluxCutoffPairingDensity
                (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
                (coarseCaccioppoliLocalCanonicalFun R center rhoInner
                  (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter))
                (fun y ↦ u.toFun y - h.toFun y) u.grad g)| ≤
            (1 / 4 : ℝ) * cubeAverage S (fun x ↦
              _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (u.grad x)) +
            remainder S) ∧
        descendantsAverage Q (k + 1) remainder ≤
          Ac * Real.rpow (rhoOuter - rhoInner) (-beta)) :
    boundaryCrossScaleEnergyProfile Q R center (1 / 3 : ℝ)
        (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
          vecNormSq (u.grad x)) ≤
      ((5 / 2 : ℝ) * Ad + Ac + (5 / 2 : ℝ) * Ag) *
        coarseCaccioppoliRadiusIterationConst beta := by
  let energy : Vec d → ℝ := fun x ↦
    _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (u.grad x)
  let F : ℝ → ℝ := fun rho ↦
    boundaryCrossScaleEnergyProfile Q R center rho energy
  let A : ℝ := (5 / 2 : ℝ) * Ad + Ac + (5 / 2 : ℝ) * Ag
  have henergy : IntegrableOn energy (openCubeSet Q) volume := by
    simpa only [energy] using integrableOn_aCutoff_energy M L omega Q u
  have henergyCube : IntegrableOn energy (cubeSet Q) volume :=
    integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr henergy
  have henergyNonneg : ∀ x ∈ openCubeSet Q, 0 ≤ energy x := by
    intro x _
    exact mul_nonneg (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x).le
      (vecNormSq_nonneg _)
  have hbounded : CoarseCaccioppoliRadiusBoundedAbove F := by
    simpa only [F] using
      boundaryCrossScaleEnergyProfile_boundedAbove henergyNonneg henergy
  have hrec : CoarseCaccioppoliRadiusSequenceRecurrence F A beta := by
    intro j
    let rhoInner := coarseCaccioppoliRadiusSequence j
    let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
    have hrhoInner : 0 < rhoInner := by
      exact lt_of_lt_of_le (by norm_num)
        (coarseCaccioppoliRadiusSequence_mem_Icc j).1
    have hlt : rhoInner < rhoOuter :=
      coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self j)
    have houter : rhoOuter < 1 :=
      coarseCaccioppoliRadiusSequence_lt_one (j + 1)
    obtain ⟨k, remainder, hchoice, hrem, hactive, hremAvg⟩ := hlocal j
    have heta : ContDiff ℝ (⊤ : ℕ∞)
        (coarseCaccioppoliLocalCanonicalFun R center rhoInner
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) :=
      coarseCaccioppoliLocalCanonicalFun_smooth R center hrhoInner
        (coarseCaccioppoliBufferedCutoffRadius_between hlt).1
    have hetaCompact : HasCompactSupport
        (coarseCaccioppoliLocalCanonicalFun R center rhoInner
          (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) :=
      coarseCaccioppoliLocalCanonicalFun_hasCompactSupport R center hrhoInner
        (coarseCaccioppoliBufferedCutoffRadius_between hlt).1
    have hpairOpen := integrableOn_aCutoff_boundaryCorrectedFluxCutoffPairing
      M L omega u h hg heta hetaCompact
    have hpairCube :=
      integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr hpairOpen
    have hpairSum :=
      volumeAverage_boundaryCorrectedFluxCutoffPairing_le_outerProfile_of_triadicGapChoice
        M L omega Q R center k u h g remainder hrhoInner hchoice hQR
          hpairCube henergyCube hrem hactive
    have hpair : |volumeAverage (openCubeSet Q)
        (boundaryCorrectedFluxCutoffPairingDensity
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
          (coarseCaccioppoliLocalCanonicalFun R center rhoInner
            (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter))
          (fun y ↦ u.toFun y - h.toFun y) u.grad g)| ≤
        (1 / 4 : ℝ) * boundaryCrossScaleEnergyProfile Q R center rhoOuter
          energy + Ac * Real.rpow (rhoOuter - rhoInner) (-beta) :=
      hpairSum.trans (by
        simpa only [rhoInner, rhoOuter, energy] using
          add_le_add_right hremAvg
            ((1 / 4 : ℝ) * boundaryCrossScaleEnergyProfile Q R center
              (coarseCaccioppoliRadiusSequence (j + 1))
              (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
                vecNormSq (u.grad x))))
    have hstep := boundaryCrossScale_bufferedHalfAbsorbable_of_correctedFluxPairing
      M L omega hweak hg hzero hrhoInner hlt houter
        (hdatum j) (hforce j) hpair
    dsimp only [F, A, energy, rhoInner, rhoOuter]
    convert hstep using 1
    ring
  have hAnonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  simpa only [F, A, energy] using
    coarseCaccioppoli_radius_iteration_of_sequenceRecurrence
      hbeta hAnonneg hbounded hrec

/-- Radius-iteration endpoint for the corrected-flux decomposition.  The
datum and force prices remain external, while the cutoff pairing spends the
second quarter of the outer profile supplied by the finite-cell summation. -/
theorem boundaryCrossScaleEnergyProfile_oneThird_le_of_correctedFluxPrices
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {Q R : TriadicCube d} {center : Vec d}
    {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hweak : IsDivFormWeakSolutionOn
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (openCubeSet Q) u g)
    (hg : MemVectorL2 (openCubeSet Q) g)
    (hzero : LocalizedZeroTraceFunctionOn (openCubeSet Q)
      (coarseCaccioppoliLocalOpenCube R center 1)
      (fun y ↦ u.toFun y - h.toFun y))
    {Ad Ac Ag beta : ℝ}
    (hAd : 0 ≤ Ad) (hAc : 0 ≤ Ac) (hAg : 0 ≤ Ag) (hbeta : 0 ≤ beta)
    (hdatum : ∀ j : ℕ,
      let rhoInner := coarseCaccioppoliRadiusSequence j
      let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
      volumeAverage (openCubeSet Q)
          (boundaryCoerciveDatumDensity
            (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter)
            h.grad) ≤ Ad * Real.rpow (rhoOuter - rhoInner) (-beta))
    (hforce : ∀ j : ℕ,
      let rhoInner := coarseCaccioppoliRadiusSequence j
      let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
      volumeAverage (openCubeSet Q)
          (boundaryCoerciveForceDensity
            (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter) g) ≤
        Ag * Real.rpow (rhoOuter - rhoInner) (-beta))
    (hpair : ∀ j : ℕ,
      let rhoInner := coarseCaccioppoliRadiusSequence j
      let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
      |volumeAverage (openCubeSet Q)
          (boundaryCorrectedFluxCutoffPairingDensity
            (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter)
            (fun y ↦ u.toFun y - h.toFun y) u.grad g)| ≤
        (1 / 4 : ℝ) * boundaryCrossScaleEnergyProfile Q R center rhoOuter
          (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
            vecNormSq (u.grad x)) +
          Ac * Real.rpow (rhoOuter - rhoInner) (-beta)) :
    boundaryCrossScaleEnergyProfile Q R center (1 / 3 : ℝ)
        (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
          vecNormSq (u.grad x)) ≤
      ((5 / 2 : ℝ) * Ad + Ac + (5 / 2 : ℝ) * Ag) *
        coarseCaccioppoliRadiusIterationConst beta := by
  let energy : Vec d → ℝ := fun x ↦
    _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (u.grad x)
  let F : ℝ → ℝ := fun rho ↦
    boundaryCrossScaleEnergyProfile Q R center rho energy
  let A : ℝ := (5 / 2 : ℝ) * Ad + Ac + (5 / 2 : ℝ) * Ag
  have henergyNonneg : ∀ x ∈ openCubeSet Q, 0 ≤ energy x := by
    intro x hx
    exact mul_nonneg (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x).le
      (vecNormSq_nonneg _)
  have henergy : IntegrableOn energy (openCubeSet Q) volume := by
    simpa only [energy] using integrableOn_aCutoff_energy M L omega Q u
  have hbounded : CoarseCaccioppoliRadiusBoundedAbove F := by
    simpa only [F] using
      boundaryCrossScaleEnergyProfile_boundedAbove henergyNonneg henergy
  have hrec : CoarseCaccioppoliRadiusSequenceRecurrence F A beta := by
    have hraw := boundaryCrossScale_sequenceHalfAbsorbable_of_correctedFluxPairing
      M L omega hweak hg hzero hdatum hforce hpair
    intro j
    simpa only [F, A, energy] using hraw j
  have hAnonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  simpa only [F, A, energy] using
    coarseCaccioppoli_radius_iteration_of_sequenceRecurrence
      hbeta hAnonneg hbounded hrec

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
