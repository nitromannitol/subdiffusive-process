module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section12Cutoff.CutoffClock
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonicCoefficientControl
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.StoppingLocalBoundsWithLoss
public import SubdiffusiveProcess.CoarseGrainingVocab.Section45Support
public import SubdiffusiveProcess.CoarseGrainingVocab.Defect
public import SubdiffusiveProcess.CoarseGrainingVocab.Section13.Displacement

@[expose] public section




set_option autoImplicit false

open Filter SubdiffusiveProcess SubdiffusiveProcess.Frozen.Assumptions Homogenization MeasureTheory ProbabilityTheory
open MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
open SubdiffusiveProcess.CoarseGrainingVocab.Section12Cutoff
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic
open SubdiffusiveProcess.CoarseGrainingVocab.Section13
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section12.FiniteCutoffVocab



structure FiniteCutoffLocalTemplate (d : ℕ) where
  grid : Finset (Vec d)
  j1 : ℕ
  j2 : ℕ
  pairs : Set (Cube d × Cube d)
  cubes : Set (Cube d)
  overlaps : Set (Cube d)
  geometry : IsLocalCubeGeometry grid j1 j2 (0, 1) pairs cubes overlaps
  vertex_overlap : ∀ pr ∈ pairs, ∃ A ∈ overlaps,
    cubeSet A ⊆ cubeSet pr.1 ∩ middleQuarter (0, 1)



def finiteCutoffTransportLocalTemplateCube {d : ℕ} (U Q : Cube d) : Cube d :=
  (U.1 + U.2 • Q.1, U.2 * Q.2)



def finiteCutoffLocalCubes {d : ℕ} (T : FiniteCutoffLocalTemplate d) (U : Cube d) : Set (Cube d) :=
  finiteCutoffTransportLocalTemplateCube U '' T.cubes



def finiteCutoffLocalPairs {d : ℕ} (T : FiniteCutoffLocalTemplate d) (U : Cube d) : Set (Cube d × Cube d) :=
  (fun pr => (finiteCutoffTransportLocalTemplateCube U pr.1, finiteCutoffTransportLocalTemplateCube U pr.2)) '' T.pairs



def finiteCutoffLocalOverlaps {d : ℕ} (T : FiniteCutoffLocalTemplate d) (U : Cube d) : Set (Cube d) :=
  finiteCutoffTransportLocalTemplateCube U '' T.overlaps



def finiteCutoffExponent {d : ℕ} (cq : ℝ) (M : GMCModel d) : ℝ :=
  cq / (M.delta ^ 2 * |Real.log M.delta| ^ 2)



def FiniteCutoffContinuousDensity {d : ℕ} (U : Set (Vec d))
    (p : ℝ → Vec d → Vec d → ℝ) : Prop :=
  ContinuousOn (fun z : ℝ × Vec d × Vec d => p z.1 z.2.1 z.2.2)
    (Ioi 0 ×ˢ U ×ˢ U)



def FiniteCutoffLocalMasses {d : ℕ} (T : FiniteCutoffLocalTemplate d) (a : Vec d → ℝ)
    (c : ℝ) (U : Cube d) : Prop :=
  ENNReal.ofReal c * weightedMeasure a (cubeSet U) ≤ weightedMeasure a (middleQuarter U) ∧
  (∀ B' ∈ finiteCutoffLocalCubes T U, ∀ B ∈ finiteCutoffLocalCubes T U,
    CompactlyInside B' B →
      ENNReal.ofReal c * weightedMeasure a (cubeSet B) ≤ weightedMeasure a (cubeSet B')) ∧
  (∀ A ∈ finiteCutoffLocalOverlaps T U,
    ENNReal.ofReal c * weightedMeasure a (cubeSet U) ≤ weightedMeasure a (cubeSet A))



def FiniteCutoffBothSobolev {d : ℕ} (a rho : Vec d → ℝ) (p0 B F : ℝ) (Q : Cube d) : Prop :=
  (∀ f : H10Function (cubeSet Q),
    lpSq rho (cubeSet Q) p0 f.toH1Function.toFun ≤
      ENNReal.ofReal (B * F) * weightedMeasure rho (cubeSet Q) ^ (-(1 - 2 / p0)) *
        ENNReal.ofReal (energy a (cubeSet Q) f.toH1Function)) ∧
  (∀ f : H1Function (cubeSet Q),
    (∫ x in cubeSet Q, rho x * f.toFun x) = 0 →
    lpSq rho (cubeSet Q) p0 f.toFun ≤
      ENNReal.ofReal (B * F) * weightedMeasure rho (cubeSet Q) ^ (-(1 - 2 / p0)) *
        ENNReal.ofReal (energy a (cubeSet Q) f))



def FiniteCutoffLocalKilledUpper {d : ℕ} (a : Vec d → ℝ) (law : Kernel (Vec d) (Path d))
    (p0 B F : ℝ) (Q : Cube d) : Prop :=
  ∀ p : ℝ → Vec d → Vec d → ℝ,
    IsKilledDensity law a (cubeSet Q) p → FiniteCutoffContinuousDensity (cubeSet Q) p →
    ∀ s : ℝ, 0 < s → ∀ x ∈ cubeSet Q,
      p s x x ≤ B / (weightedMeasure a (cubeSet Q)).toReal *
        (1 + F / s) ^ (1 - 2 / p0)⁻¹



def FiniteCutoffLocalGood {d : ℕ} (T : FiniteCutoffLocalTemplate d) (a : Vec d → ℝ)
    (clock : ℝ → ℝ) (p0 c C eps0 : ℝ) (U : Cube d) : Prop :=
  FiniteCutoffLocalMasses T a c U ∧
  LocalHarmonicOscillation a eps0 (finiteCutoffLocalPairs T U) ∧
  (∀ Q ∈ finiteCutoffLocalCubes T U, ∀ f : H10Function (cubeSet Q),
    lpSq a (cubeSet Q) p0 f.toH1Function.toFun ≤
      ENNReal.ofReal C * weightedMeasure a (cubeSet Q) ^ (-(1 - 2 / p0)) *
        ENNReal.ofReal (clock Q.2 * energy a (cubeSet Q) f.toH1Function)) ∧
  (∀ B' ∈ finiteCutoffLocalCubes T U, ∀ B ∈ finiteCutoffLocalCubes T U,
    cubeSet B' ⊆ centeredAxisCube B.1 (B.2 / 2) →
    (∀ h : Vec d → ℝ, WeakHarmonic a (cubeSet B) h →
      MemLp h 2 (volume.restrict (cubeSet B)) → ∀ x ∈ cubeSet B',
      |h x - averageOn (cubeSet B) h| ≤
        C * normalizedL2On (cubeSet B) (fun y => h y - averageOn (cubeSet B) h)) ∧
    (∀ s : ℝ, c * clock B.2 ≤ s → 0 < s →
      ∀ v : H1Function (cubeSet B),
        Section8Resolvent.IsMassiveWeakSolutionOn a a s⁻¹ (cubeSet B) v (fun _ => 0) →
        ∀ vc : Vec d → ℝ, ContinuousOn vc (cubeSet B) →
          (∀ᵐ x ∂volume.restrict (cubeSet B), vc x = v.toFun x) →
          ∀ x ∈ cubeSet B', ENNReal.ofReal |vc x| ≤
            ENNReal.ofReal C * weightedMeasure a (cubeSet B) ^ (-(1 / 2) : ℝ) *
              eLpNorm v.toFun 2 ((weightedMeasure a).restrict (cubeSet B)))) ∧
  (∀ law : Kernel (Vec d) (Path d), LocalDiffusionData a a law →
    LocalTorsionEstimates a law clock p0 c C U (finiteCutoffLocalCubes T U) (finiteCutoffLocalOverlaps T U) ∧
    (∀ Q ∈ finiteCutoffLocalCubes T U, FiniteCutoffLocalKilledUpper a law p0 C (clock Q.2) Q) ∧
    (∀ p : ℝ → Vec d → Vec d → ℝ,
      IsKilledDensity law a (cubeSet U) p → FiniteCutoffContinuousDensity (cubeSet U) p →
      ∀ s : ℝ, C * clock U.2 ≤ s → 0 < s →
        ∀ z ∈ middleQuarter U, ∀ w ∈ middleQuarter U,
          c / (weightedMeasure a (cubeSet U)).toReal * Real.exp (-(C * s / clock U.2))
            ≤ p s z w))



def FiniteCutoffLocalConditioned {d : ℕ} (T : FiniteCutoffLocalTemplate d) (a : Vec d → ℝ)
    (clock : ℝ → ℝ) (p0 C h : ℝ) (J : ℕ) (U : Cube d) : Prop :=
  let B := Real.exp (C * h)
  FiniteCutoffLocalMasses T a B⁻¹ U ∧
  (∀ Q ∈ finiteCutoffLocalCubes T U, FiniteCutoffLocalMasses T a B⁻¹ Q) ∧
  (∀ Q ∈ finiteCutoffLocalCubes T U, FiniteCutoffBothSobolev a a p0 B (B * clock Q.2) Q) ∧
  (∀ law : Kernel (Vec d) (Path d), LocalDiffusionData a a law →
    ∀ Q ∈ finiteCutoffLocalCubes T U,
      (∀ x ∈ cubeSet Q, meanExit law (cubeSet Q) x ≤ ENNReal.ofReal (B * clock Q.2)) ∧
      FiniteCutoffLocalKilledUpper a law p0 B (B * clock Q.2) Q) ∧
  (∀ B' ∈ finiteCutoffLocalCubes T U, ∀ Q ∈ finiteCutoffLocalCubes T U,
    cubeSet B' ⊆ centeredAxisCube Q.1 (Q.2 / 2) →
    ∀ s : ℝ, 0 < s → ∀ v : H1Function (cubeSet Q),
      Section8Resolvent.IsMassiveWeakSolutionOn a a s⁻¹ (cubeSet Q) v (fun _ => 0) →
      ∀ vc : Vec d → ℝ, ContinuousOn vc (cubeSet Q) →
        (∀ᵐ x ∂volume.restrict (cubeSet Q), vc x = v.toFun x) →
        ∀ x ∈ cubeSet B', ENNReal.ofReal |vc x| ≤
          ENNReal.ofReal (B * (1 + clock Q.2 / s) ^ J) *
            weightedMeasure a (cubeSet Q) ^ (-(1 / 2) : ℝ) *
              eLpNorm v.toFun 2 ((weightedMeasure a).restrict (cubeSet Q)))



def finiteCutoffLocalSigma {d : ℕ} (L : ℕ) (B : Set (Vec d)) :
    MeasurableSpace (PotentialSample d) := ⨆ k : Fin (L + 1), shellLocalSigma k.val B



def finiteCutoffLocalFactor {d : ℕ} (M : GMCModel d) (L k : ℕ)
    (omega : PotentialSample d) (Q : Cube d) : ℝ :=
  if k < L then aCutoff M L omega Q.1 / aCutoff M k omega Q.1 else 1



def finiteCutoffContinuousLift {d : ℕ} (B : Set C(NNReal, Vec d)) : Set (Path d) :=
  {w | ∃ v ∈ B, ∀ t : NNReal, LifetimePath.coordinate t w = Sum.inl (v t)}



def FiniteCutoffLocalScaleQuantitiesLE {d : ℕ} (M : GMCModel d) (L : ℕ) (omega : PotentialSample d)
    (clock : ℝ → ℝ) (n : ℕ) (y : Vec d) (B : ℝ) : Prop :=
  ∀ hb : ExactCircIntegrable (originCube d (n : ℤ))
      (fun z => aCutoff M (min n L) (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y omega) z /
        cubeAverage (originCube d (n : ℤ))
          (aCutoff M (min n L) (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y omega)) - 1),
    ∀ coeff : Homogenization.Book.Ch02.TriadicCoeffFamily d,
      (∀ᵐ z ∂(volume.restrict (openCubeSet (originCube d (n : ℤ)))),
          (coeff.coeffOn (originCube d (n : ℤ))).toCoeffField z =
            scalarMatrix (aCutoff M (min n L)
              (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y omega) z)) →
        ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 8 : ℝ) * (n : ℝ))) *
            SubdiffusiveProcess.CoarseGrainingVocab.paperNegativeBesovCircDiagonal (originCube d (n : ℤ))
              (1 / 8) (4 * (d : ℝ))
              (fun z => aCutoff M (min n L) (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y omega) z /
                cubeAverage (originCube d (n : ℤ))
                  (aCutoff M (min n L) (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y omega)) - 1) hb +
            ENNReal.ofReal ((3 : ℝ) ^ (2 * (n : ℝ)) *
              cubeAverage (originCube d (n : ℤ))
                (aCutoff M (min n L) (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y omega)) /
              (clock ((3 : ℝ) ^ n) *
                Homogenization.Book.Ch02.lambdaSq (originCube d (n : ℤ)) (1 / 2)
                  (.finite 1) coeff)) +
            ENNReal.ofReal (cubeAverage (originCube d (n : ℤ))
              (aCutoff M (min n L) (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y omega))) +
            ENNReal.ofReal (cubeAverage (originCube d (n : ℤ))
              (aCutoff M (min n L) (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y omega)))⁻¹ ≤
          ENNReal.ofReal B




def FiniteCutoffIsHolderMinimalScaleAt {d : ℕ} (M : GMCModel d) (L : ℕ) (C : ℝ) (n : ℕ) (y : Vec d)
    (omega : PotentialSample d) (Lval : ℕ) : Prop :=
  ∀ (u h : H1Function (openCubeSet (originCube d (n : ℤ)))) (g : Vec d → Vec d),
    IsDirichletSolutionOn
        (aCutoff M L (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y omega))
        (originCube d (n : ℤ)) u h g →
      MemHolder (cube d (n : ℤ)) (1 / 2) g →
      MemHolder (cube d (n : ℤ)) (1 / 2) h.grad →
        SubdiffusiveProcess.CoarseGrainingVocab.HolderRegularityConclusions M C L
          (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y omega) stoppingAlphaZero n Lval u h g




def finiteCutoffProfile {d : ℕ} (M : GMCModel d) (L : ℕ) (omega : PotentialSample d)
    (n : ℕ) (x : Vec d) : ℝ :=
  stoppingMassProfile (aCutoff M L omega) (aCutoff M (min n L) omega) n x



def finiteCutoffLongWave {d : ℕ} (_M : GMCModel d) (L : ℕ) (omega : PotentialSample d)
    (n : ℕ) (z : Vec d) : ℝ :=
  ∑ k ∈ Finset.Icc (min n L + 1) L, omega k z




def FiniteCutoffStoppingDerivativeBoundAt {d : ℕ} (M : GMCModel d) (L : ℕ) (omega : PotentialSample d)
    (C : ℝ) (y : Vec d) (B : ℝ) : Prop :=
  ∃ G Kap : ℝ, 0 ≤ G ∧ 0 ≤ Kap ∧
    (∀ z ∈ centeredAxisCube y C,
        euclideanNorm (euclideanGradient (fun w => Real.log (aCutoff M L omega w)) z) ≤ G) ∧
    SubdiffusiveProcess.CoarseGrainingVocab.HolderSeminormBoundOn (centeredAxisCube y C) 1 Kap
      (euclideanGradient (fun w => Real.log (aCutoff M L omega w))) ∧
    1 + G ^ 2 + Kap ≤ B




structure FiniteCutoffStoppingGradedBounds {d : ℕ} (M : GMCModel d) (L : ℕ) (omega : PotentialSample d)
    (clock : ℝ → ℝ) (grid : Finset (Vec d)) (A CA C : ℝ) (m : ℕ) (x : Vec d) (K : ℝ)
    (j : ℕ) : Prop where
  local_scale : ∀ n : ℕ, (n : ℝ) ≤ (m : ℝ) + A * Real.log K + (j : ℝ) → ∀ y : Vec d,
    IsGridCube grid y ((3 : ℝ) ^ n) →
    euclideanNorm (y - x) ≤
        ((m : ℝ) + 2) ^ A * K ^ A * Real.exp (j : ℝ) * (3 : ℝ) ^ n →
      FiniteCutoffLocalScaleQuantitiesLE M L omega clock n y (K ^ CA * Real.exp (C * (j : ℝ)))
  minimal_scale : ∀ n : ℕ, (n : ℝ) ≤ (m : ℝ) + A * Real.log K + (j : ℝ) → ∀ y : Vec d,
    IsGridCube grid y ((3 : ℝ) ^ n) →
    euclideanNorm (y - x) ≤
        ((m : ℝ) + 2) ^ A * K ^ A * Real.exp (j : ℝ) * (3 : ℝ) ^ n →
      ∃ Lval : ℕ, FiniteCutoffIsHolderMinimalScaleAt M L C n y omega Lval ∧
        (Lval : ℝ≥0∞) +
            oscillation (centeredAxisCube y ((3 : ℝ) ^ n)) (finiteCutoffLongWave M L omega n) ≤
          ENNReal.ofReal (CA * Real.log K + C * (j : ℝ))
  scale_zero : ∀ y : Vec d, IsGridCube grid y 1 →
    euclideanNorm (y - x) ≤ ((m : ℝ) + 2) ^ A * K ^ A * Real.exp (j : ℝ) →
      FiniteCutoffStoppingDerivativeBoundAt M L omega C y (CA * Real.log K + C * (j : ℝ))
  mass_profile : ∀ n : ℕ, (n : ℝ) ≤ (m : ℝ) + A * Real.log K + (j : ℝ) → ∀ y : Vec d,
    IsGridCube grid y ((3 : ℝ) ^ n) →
    euclideanNorm (y - x) ≤
        ((m : ℝ) + 2) ^ A * K ^ A * Real.exp (j : ℝ) * (3 : ℝ) ^ n →
      ENNReal.ofReal (K ^ (-CA) * Real.exp (-(C * (j : ℝ))) * finiteCutoffProfile M L omega n x) ≤
          weightedMeasure (aCutoff M L omega) (centeredAxisCube y ((3 : ℝ) ^ n)) ∧
        weightedMeasure (aCutoff M L omega) (centeredAxisCube y ((3 : ℝ) ^ n)) ≤
          ENNReal.ofReal (K ^ CA * Real.exp (C * (j : ℝ)) * finiteCutoffProfile M L omega n x)
  relative_mass : ∀ N : ℕ, (N : ℝ) ≤ (m : ℝ) + A * Real.log K → ∀ y : Vec d,
    IsGridCube grid y ((3 : ℝ) ^ N) →
    euclideanNorm (y - x) ≤ ((m : ℝ) + 2) ^ A * K ^ A * (3 : ℝ) ^ N →
      ∀ (w : Vec d) (r : ℝ), IsGridCube grid w r → 1 ≤ r → r ≤ (3 : ℝ) ^ N →
        centeredAxisCube w r ⊆ centeredAxisCube y ((3 : ℝ) ^ N) →
          ENNReal.ofReal (K ^ (-CA) * (r / (3 : ℝ) ^ N) ^ C) *
              weightedMeasure (aCutoff M L omega) (centeredAxisCube y ((3 : ℝ) ^ N)) ≤
            weightedMeasure (aCutoff M L omega) (centeredAxisCube w r)




structure FiniteCutoffStoppingLocalBounds {d : ℕ} (M : GMCModel d) (L : ℕ) (omega : PotentialSample d)
    (clock : ℝ → ℝ) (grid : Finset (Vec d)) (p0 A CA C : ℝ) (m : ℕ) (x : Vec d) (K : ℝ) :
    Prop where
  local_scale : ∀ n : ℕ, (n : ℝ) ≤ (m : ℝ) + A * Real.log K → ∀ y : Vec d,
    IsGridCube grid y ((3 : ℝ) ^ n) →
    euclideanNorm (y - x) ≤ ((m : ℝ) + 2) ^ A * K ^ A * (3 : ℝ) ^ n →
      FiniteCutoffLocalScaleQuantitiesLE M L omega clock n y (K ^ CA)
  minimal_scale : ∀ n : ℕ, (n : ℝ) ≤ (m : ℝ) + A * Real.log K → ∀ y : Vec d,
    IsGridCube grid y ((3 : ℝ) ^ n) →
    euclideanNorm (y - x) ≤ ((m : ℝ) + 2) ^ A * K ^ A * (3 : ℝ) ^ n →
      ∃ Lval : ℕ, FiniteCutoffIsHolderMinimalScaleAt M L C n y omega Lval ∧
        (Lval : ℝ≥0∞) +
            oscillation (centeredAxisCube y ((3 : ℝ) ^ n)) (finiteCutoffLongWave M L omega n) ≤
          ENNReal.ofReal (CA * Real.log K)
  scale_zero : ∀ y : Vec d, IsGridCube grid y 1 →
    euclideanNorm (y - x) ≤ C * ((m : ℝ) + 2) ^ A * K ^ A →
      FiniteCutoffStoppingDerivativeBoundAt M L omega C y (CA * Real.log K)
  scale_profile : ∀ i j : ℕ, i ≤ j → (j : ℝ) ≤ (m : ℝ) + A * Real.log K →
    K ^ (-CA) * Real.exp (-(C * ((j : ℝ) - (i : ℝ)))) * finiteCutoffProfile M L omega i x ≤
        finiteCutoffProfile M L omega j x ∧
      finiteCutoffProfile M L omega j x ≤
        K ^ CA * Real.exp (C * ((j : ℝ) - (i : ℝ))) * finiteCutoffProfile M L omega i x
  exit_upper_inputs : ∀ n : ℕ, (n : ℝ) ≤ (m : ℝ) + A * Real.log K → ∀ y : Vec d,
    IsGridCube grid y ((3 : ℝ) ^ n) →
    euclideanNorm (y - x) ≤ ((m : ℝ) + 2) ^ A * K ^ A * (3 : ℝ) ^ n →
      SobolevAssumption (aCutoff M L omega) (aCutoff M L omega)
          (centeredAxisCube y ((3 : ℝ) ^ n)) p0 (K ^ CA) (clock ((3 : ℝ) ^ n)) ∧
        PoincareAssumption (aCutoff M L omega) (aCutoff M L omega)
          (centeredAxisCube y ((3 : ℝ) ^ n)) (K ^ CA) (clock ((3 : ℝ) ^ n))




def FiniteCutoffAboveQuantitiesLE {d : ℕ} (M : GMCModel d) (L : ℕ) (omega : PotentialSample d)
    (n : ℕ) (y : Vec d) (B : ℝ) : Prop :=
  ∀ hb : ExactCircIntegrable (originCube d (n : ℤ))
      (fun z => aCutoff M L (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y omega) z /
        cubeAverage (originCube d (n : ℤ))
          (aCutoff M L (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y omega)) - 1),
    ∀ coeff : Homogenization.Book.Ch02.TriadicCoeffFamily d,
      (∀ᵐ z ∂(volume.restrict (openCubeSet (originCube d (n : ℤ)))),
          (coeff.coeffOn (originCube d (n : ℤ))).toCoeffField z =
            scalarMatrix (aCutoff M L
              (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y omega) z)) →
        ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 8 : ℝ) * (n : ℝ))) *
            SubdiffusiveProcess.CoarseGrainingVocab.paperNegativeBesovCircDiagonal (originCube d (n : ℤ))
              (1 / 8) (4 * (d : ℝ))
              (fun z => aCutoff M L (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y omega) z /
                cubeAverage (originCube d (n : ℤ))
                  (aCutoff M L (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y omega)) - 1) hb +
            ENNReal.ofReal (ahom M L /
              Homogenization.Book.Ch02.lambdaSq (originCube d (n : ℤ)) (1 / 2)
                (.finite 1) coeff) +
            ENNReal.ofReal (cubeAverage (originCube d (n : ℤ))
              (aCutoff M L (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y omega))) +
            ENNReal.ofReal (cubeAverage (originCube d (n : ℤ))
              (aCutoff M L (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y omega)))⁻¹ ≤
          ENNReal.ofReal B




def FiniteCutoffCrossoverLocalEvents {d : ℕ} (M : GMCModel d) (T : FiniteCutoffLocalTemplate d)
    (cq c C p0 eps0 : ℝ) (J : ℕ)
    (G : ℕ → Cube d → Set (PotentialSample d))
    (D : ℕ → Cube d → ℝ → Set (PotentialSample d)) : Prop :=
  ∀ (L : ℕ) (n : ℤ) (z : Vec d),
    let U : Cube d := (z, (3 : ℝ) ^ n)
    let clock := cutoffTimeScale (ahom M) L
    MeasurableSet (G L U) ∧ (∀ h, MeasurableSet (D L U h)) ∧
    M.P.toMeasure (G L U)ᶜ ≤ ENNReal.ofReal (C * Real.exp (-(c * finiteCutoffExponent cq M))) ∧
    (∀ h : ℝ, 1 ≤ h → M.P.toMeasure (D L U h)ᶜ ≤
      ENNReal.ofReal (C * Real.exp (-(c * finiteCutoffExponent cq M * h)))) ∧
    (∀ omega ∈ G L U,
      FiniteCutoffLocalGood T (aCutoff M L omega) clock p0 c C eps0 U ∧
      (∀ Q ∈ finiteCutoffLocalCubes T U, FiniteCutoffLocalGood T (aCutoff M L omega) clock p0 c C eps0 Q) ∧
      (∀ Q ∈ finiteCutoffLocalCubes T U, Q.2 < 1 →
        LogCoefficientControlOn (aCutoff M L omega) C Q)) ∧
    (∀ h : ℝ, 1 ≤ h → ∀ omega ∈ D L U h,
      FiniteCutoffLocalConditioned T (aCutoff M L omega) clock p0 C h J U ∧
      (∀ Q ∈ finiteCutoffLocalCubes T U, Q.2 < 1 →
        LogCoefficientControlOn (aCutoff M L omega) (C * h) Q))



def FiniteCutoffFixedClockSolution {d : ℕ} (a : Vec d → ℝ)
    (X : Vec d → C(NNReal, Vec d) → C(NNReal, Vec d)) : Prop :=
  ∀ (x : Vec d) (w : C(NNReal, Vec d)), w 0 = 0 → ∀ t : NNReal,
    X x w t = x + Real.sqrt 2 • w t +
      ∫ s in (0 : ℝ)..(t : ℝ),
        euclideanGradient (fun y => Real.log (a y)) (X x w (Real.toNNReal s))



def FiniteCutoffBrownianDriver {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal mΩ) (W : Ω → C(NNReal, Vec d)) : Prop :=
  Measurable W ∧ (∀ᵐ w ∂P, W w 0 = 0) ∧ Adapted F (fun t w => W w t) ∧
  ∀ s t : NNReal, s ≤ t →
    HasLaw (fun w => W w t - W w s) (Measure.pi fun _ : Fin d => gaussianReal 0 (t - s)) P ∧
    Indep (F s) (MeasurableSpace.comap (fun w => W w t - W w s) inferInstance) P



def finiteCutoffItoSum {d : ℕ} {Ω : Type} (a : Vec d → ℝ)
    (W Y : Ω → C(NNReal, Vec d)) (t : NNReal) (n : ℕ) (w : Ω) : Vec d :=
  ∑ k ∈ Finset.range (2 ^ n),
    Real.sqrt (2 * a (Y w (t * (k : NNReal) / (2 : NNReal) ^ n))) •
      (W w (t * ((k + 1 : ℕ) : NNReal) / (2 : NNReal) ^ n) -
        W w (t * (k : NNReal) / (2 : NNReal) ^ n))



def FiniteCutoffDivergenceSolution {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω]
    (a : Vec d → ℝ) (P : Measure Ω) (F : Filtration NNReal mΩ)
    (W : Ω → C(NNReal, Vec d)) (Y : Vec d → Ω → C(NNReal, Vec d)) : Prop :=
  ∀ x : Vec d, Measurable (Y x) ∧ Adapted F (fun t w => Y x w t) ∧
    (∀ᵐ w ∂P, Y x w 0 = x) ∧
    ∀ t : NNReal,
      TendstoInMeasure P
        (fun n w => x + finiteCutoffItoSum a W (Y x) t n w +
          ∫ s in (0 : ℝ)..(t : ℝ), euclideanGradient a (Y x w (Real.toNNReal s)))
        atTop (fun w => Y x w t)

end SubdiffusiveProcess.CoarseGrainingVocab.Section12.FiniteCutoffVocab
