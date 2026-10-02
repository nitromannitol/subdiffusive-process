import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCorrectedFluxCutoff
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCrossScalePrices

/-!
# Half-absorbable boundary recurrence from the corrected flux

This file converts the corrected-flux weak estimate into the radius recurrence
used by harmonic approximation.  One quarter of the outer energy comes from
the non-cutoff Young terms; a second quarter is reserved for the multiscale
cutoff-product estimate.  No pointwise upper cap on `aCutoff` is used.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem volumeAverage_correctedFlux_of_setIntegral
    {V : Set (Vec d)} {main datum force pair : Vec d → ℝ}
    (hset :
      ∫ x in V, main x ∂volume ≤
        (1 / 4 : ℝ) * ∫ x in V, main x ∂volume +
          (5 / 2 : ℝ) * ∫ x in V, datum x ∂volume +
          (5 / 2 : ℝ) * ∫ x in V, force x ∂volume +
          |∫ x in V, pair x ∂volume|) :
    volumeAverage V main ≤
      (1 / 4 : ℝ) * volumeAverage V main +
        (5 / 2 : ℝ) * volumeAverage V datum +
        (5 / 2 : ℝ) * volumeAverage V force +
        |volumeAverage V pair| := by
  let c : ℝ := (volume V).toReal⁻¹
  have hc : 0 ≤ c := inv_nonneg.mpr ENNReal.toReal_nonneg
  have hs := mul_le_mul_of_nonneg_left hset hc
  have habs : c * |∫ x in V, pair x ∂volume| =
      |c * ∫ x in V, pair x ∂volume| := by
    rw [abs_mul, abs_of_nonneg hc]
  unfold volumeAverage
  dsimp only [c] at hs habs ⊢
  rw [← habs]
  linarith only [hs]

/-- The squared canonical cutoff energy is bounded by the outer-radius energy
profile. -/
theorem volumeAverage_boundaryCoerciveMain_localCanonicalFun_le_outerProfile
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
    volumeAverage (openCubeSet Q)
        (boundaryCoerciveMainDensity a
          (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter) u.grad) ≤
      boundaryCrossScaleEnergyProfile Q R center rhoOuter
        (fun x => a x * vecNormSq (u.grad x)) := by
  apply volumeAverage_le_volumeAverage_of_le_on (measurableSet_openCubeSet Q)
    hmain
    (henergy.indicator
      (measurableSet_coarseCaccioppoliLocalClosedCube R center rhoOuter))
  intro x hxQ
  let eta := coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter
  by_cases hx : x ∈ coarseCaccioppoliLocalClosedCube R center rhoOuter
  · rw [Set.indicator_of_mem hx]
    have heta0 : 0 ≤ eta x :=
      coarseCaccioppoliLocalCanonicalFun_nonneg R center rhoInner rhoOuter x
    have heta1 : eta x ≤ 1 :=
      coarseCaccioppoliLocalCanonicalFun_le_one R center rhoInner rhoOuter x
    have hetaSq : eta x ^ 2 ≤ 1 := by nlinarith only [heta0, heta1]
    have hnonneg : 0 ≤ a x * vecNormSq (u.grad x) :=
      mul_nonneg (ha x hxQ) (vecNormSq_nonneg _)
    unfold boundaryCoerciveMainDensity
    nlinarith only [hetaSq, hnonneg]
  · rw [Set.indicator_of_notMem hx]
    have heta : eta x = 0 := by
      by_contra hne
      exact hx
        (coarseCaccioppoliLocalCanonicalFun_tsupport_subset_localClosedCube
          hinner hinnerOuter (subset_closure hne))
    change a x * eta x ^ 2 * vecNormSq (u.grad x) ≤ 0
    rw [heta]
    norm_num

/-- The localized direct weak test in the form consumed by the radius step.
The positive cutoff density has disappeared; only the corrected-flux pairing
remains. -/
theorem boundaryCrossScaleEnergyProfile_le_correctedFluxTerms
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {Q R : TriadicCube d} {center : Vec d} {rhoInner rhoOuter : ℝ}
    {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hweak : IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) u g)
    (hg : MemVectorL2 (openCubeSet Q) g)
    {V : Set (Vec d)}
    (hzero : LocalizedZeroTraceFunctionOn (openCubeSet Q) V
      (fun y => u.toFun y - h.toFun y))
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (houterV : coarseCaccioppoliLocalClosedCube R center rhoOuter ⊆ V) :
    boundaryCrossScaleEnergyProfile Q R center rhoInner
        (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
          vecNormSq (u.grad x)) ≤
      (1 / 4 : ℝ) * boundaryCrossScaleEnergyProfile Q R center rhoOuter
          (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (u.grad x)) +
        (5 / 2 : ℝ) * volumeAverage (openCubeSet Q)
          (boundaryCoerciveDatumDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter)
            h.grad) +
        (5 / 2 : ℝ) * volumeAverage (openCubeSet Q)
          (boundaryCoerciveForceDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter) g) +
        |volumeAverage (openCubeSet Q)
          (boundaryCorrectedFluxCutoffPairingDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter)
            (fun y => u.toFun y - h.toFun y) u.grad g)| := by
  let eta := coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter
  have heta : ContDiff ℝ (⊤ : ℕ∞) eta :=
    coarseCaccioppoliLocalCanonicalFun_smooth R center hinner hinnerOuter
  have hetaCompact : HasCompactSupport eta :=
    coarseCaccioppoliLocalCanonicalFun_hasCompactSupport R center hinner hinnerOuter
  have hetaSupport : tsupport eta ⊆ V :=
    (coarseCaccioppoliLocalCanonicalFun_tsupport_subset_localClosedCube
      hinner hinnerOuter).trans houterV
  have hset :=
    setIntegral_aCutoff_boundaryCoerciveMain_le_correctedFluxPairing_of_localizedZeroTrace
      M L omega hweak hg hzero heta hetaCompact hetaSupport
  have havg := volumeAverage_correctedFlux_of_setIntegral hset
  have henergy := integrableOn_aCutoff_energy M L omega Q u
  have hmain : IntegrableOn
      (boundaryCoerciveMainDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta u.grad)
      (openCubeSet Q) := by
    simpa only [boundaryCoerciveMainDensity] using
      integrableOn_aCutoff_sqCutoff_vecNormSq M L omega u.grad_memVectorL2
        heta hetaCompact
  have hinnerMain := boundaryCrossScaleEnergyProfile_le_boundaryCoerciveMain
    hinner hinnerOuter
    (fun x _ => (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le)
    henergy hmain
  have hmainOuter :=
    volumeAverage_boundaryCoerciveMain_localCanonicalFun_le_outerProfile
      hinner hinnerOuter
      (fun x _ => (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le)
      henergy hmain
  dsimp only [eta] at havg hinnerMain hmainOuter ⊢
  linarith only [havg, hinnerMain, hmainOuter]

/-- The promised one-half-absorbable consecutive-radius estimate.  Its only
new analytic premise is the corrected-flux cutoff-product bound; datum and
force remain explicit external prices. -/
theorem boundaryCrossScale_sequenceHalfAbsorbable_of_correctedFluxPairing
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    {Q R : TriadicCube d} {center : Vec d}
    {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hweak : IsDivFormWeakSolutionOn
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) (openCubeSet Q) u g)
    (hg : MemVectorL2 (openCubeSet Q) g)
    (hzero : LocalizedZeroTraceFunctionOn (openCubeSet Q)
      (coarseCaccioppoliLocalOpenCube R center 1)
      (fun y => u.toFun y - h.toFun y))
    {Ad Ac Ag beta : ℝ}
    (hdatum : ∀ j : ℕ,
      let rhoInner := coarseCaccioppoliRadiusSequence j
      let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
      volumeAverage (openCubeSet Q)
          (boundaryCoerciveDatumDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter)
            h.grad) ≤ Ad * Real.rpow (rhoOuter - rhoInner) (-beta))
    (hforce : ∀ j : ℕ,
      let rhoInner := coarseCaccioppoliRadiusSequence j
      let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
      volumeAverage (openCubeSet Q)
          (boundaryCoerciveForceDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter) g) ≤
        Ag * Real.rpow (rhoOuter - rhoInner) (-beta))
    (hpair : ∀ j : ℕ,
      let rhoInner := coarseCaccioppoliRadiusSequence j
      let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
      |volumeAverage (openCubeSet Q)
          (boundaryCorrectedFluxCutoffPairingDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
            (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter)
            (fun y => u.toFun y - h.toFun y) u.grad g)| ≤
        (1 / 4 : ℝ) * boundaryCrossScaleEnergyProfile Q R center rhoOuter
          (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (u.grad x)) +
          Ac * Real.rpow (rhoOuter - rhoInner) (-beta)) :
    ∀ j : ℕ,
      let rhoInner := coarseCaccioppoliRadiusSequence j
      let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
      boundaryCrossScaleEnergyProfile Q R center rhoInner
          (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (u.grad x)) ≤
        (1 / 2 : ℝ) * boundaryCrossScaleEnergyProfile Q R center rhoOuter
          (fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
            vecNormSq (u.grad x)) +
          ((5 / 2 : ℝ) * Ad + Ac + (5 / 2 : ℝ) * Ag) *
            Real.rpow (rhoOuter - rhoInner) (-beta) := by
  intro j
  dsimp only
  have hinner : 0 < coarseCaccioppoliRadiusSequence j :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 3)
      (coarseCaccioppoliRadiusSequence_mem_Icc j).1
  have hlt : coarseCaccioppoliRadiusSequence j <
      coarseCaccioppoliRadiusSequence (j + 1) :=
    coarseCaccioppoliRadiusSequence_strictMono (Nat.lt_succ_self j)
  have houter1 : coarseCaccioppoliRadiusSequence (j + 1) < 1 :=
    coarseCaccioppoliRadiusSequence_lt_one (j + 1)
  have hbase := boundaryCrossScaleEnergyProfile_le_correctedFluxTerms
    M L omega hweak hg hzero hinner hlt
      (coarseCaccioppoliLocalClosedCube_subset_localOpenCube_one_of_lt_one houter1)
  have hd := hdatum j
  have hg' := hforce j
  have hp := hpair j
  dsimp only at hd hg' hp
  linarith only [hbase, hd, hg', hp]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
