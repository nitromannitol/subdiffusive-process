module

public import SubdiffusiveProcess.Assumptions.AnchoredCoefficient
public import SubdiffusiveProcess.CoarseGrainingVocab.Section3Support
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GoodSetMeasurable
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellSummable
public import SubdiffusiveProcess.Frozen.Vocab.Ahom
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.IntrinsicClock
public import SubdiffusiveProcess.Frozen.Assumptions.ACutoff
public import SubdiffusiveProcess.Frozen.Assumptions.OGammaLE
public import SubdiffusiveProcess.Frozen.Section6.Defs.HolderRegularityConclusions
@[expose] public section

set_option autoImplicit false
open Filter SubdiffusiveProcess SubdiffusiveProcess.Frozen.Assumptions Homogenization MeasureTheory ProbabilityTheory
open MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal NNReal
noncomputable section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping

def stoppingScaleLength (m : ℕ) : ℝ := 1 + Real.log ((m : ℝ) + 2)

def stoppingAlphaZero : ℝ := 1 / 2

def stoppingMassProfile {d : ℕ} (a an : Vec d → ℝ) (n : ℕ) (x : Vec d) : ℝ :=
  (volume (euclideanBall (0 : Vec d) 1)).toReal * (3 : ℝ) ^ (d * n) * a x / an x

def SemigroupBlockNormLE {d : ℕ} (rho : Vec d → ℝ) (law : Kernel (Vec d) (Path d))
    (t : ℝ) (E F : Set (Vec d)) (B : ℝ) : Prop :=
  ∀ f : Vec d → ℝ, MemLp f 2 (weightedMeasure rho) →
    eLpNorm (F.indicator (fun z => ∫ w,
        (LifetimePath.coordinate (Real.toNNReal t) w).elim (E.indicator f) (fun _ => 0) ∂law z)) 2
        (weightedMeasure rho) ≤
      ENNReal.ofReal B * eLpNorm f 2 (weightedMeasure rho)

def StoppingTailBound {d : ℕ} {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
    (delta C : ℝ) (X : ℕ → Vec d → Omega → ℝ) : Prop :=
  ∃ Z1 Z2 : ℕ → Vec d → Omega → ℝ,
    (∀ m x, SubdiffusiveProcess.OGammaLE mu 1 (C * delta ^ 2 * |Real.log delta| ^ 2) (Z1 m x)) ∧
    (∀ m x, SubdiffusiveProcess.OGammaLE mu 2 (C * delta * Real.sqrt (stoppingScaleLength m)) (Z2 m x)) ∧
    ∀ m x, ∀ᵐ omega ∂mu, ∀ z ∈ euclideanBall x 1,
      Real.log (X m z omega) ≤
        C * (1 + delta * stoppingScaleLength m) + Z2 m x omega + Z1 m x omega

structure StoppingBallEstimates {d : ℕ} (a : Vec d → ℝ) (clock : ℝ → ℝ)
    (law : Kernel (Vec d) (Path d)) (c C : ℝ) (X : ℕ → Vec d → ℝ)
    (m : ℕ) (x : Vec d) (t : ℝ) (R : ℝ) : Prop where
  two_ball : ∀ y : Vec d, euclideanNorm (x - y) = R →
    ∀ rho : ℝ, 0 < rho → rho ≤ R / 4 → ∀ r : ℝ, 0 < r → r ≤ R / C →
      SemigroupBlockNormLE a law t (euclideanBall x rho) (euclideanBall y rho)
        (C * max (X m x) (X m y) *
          Real.exp (C * max (X m x) (X m y) * t / clock r - c * R / r))
  exit : ∀ r : ℝ, 0 < r → r ≤ R / C →
    law x {w | LifetimePath.exitTime (euclideanBall x R) w ≤ ENNReal.ofReal t} ≤
      ENNReal.ofReal (C * X m x * Real.exp (C * X m x * t / clock r - c * R / r))
  exterior : ∀ r : ℝ, 0 < r → r ≤ R / C →
    SemigroupBlockNormLE a law t (euclideanBall x 1) (euclideanBall x R)ᶜ
      (C * X m x * Real.exp (C * X m x * t / clock r - c * R / r))
  thick_annulus : ∀ r : ℝ, 0 < r → r ≤ R / C →
    SemigroupBlockNormLE a law t (euclideanBall x (R / 3)) (euclideanBall x R)ᶜ
      (C * X m x * Real.exp (C * X m x * t / clock r - c * R / r))
  mean_exit : ∀ z ∈ euclideanBall x R,
    meanExit law (euclideanBall x R) z ≤ ENNReal.ofReal (C * X m x ^ C * clock R)

structure StoppingExtendedRange {d : ℕ} (a : Vec d → ℝ) (clock : ℝ → ℝ)
    (law : Kernel (Vec d) (Path d)) (c C : ℝ) (X : ℕ → Vec d → ℝ)
    (m : ℕ) (x : Vec d) (t : ℝ) : Prop where
  exit : ∀ n : ℕ, n ≤ m → ∀ Rhat : ℝ, C * (3 : ℝ) ^ n ≤ Rhat →
    law x {w | LifetimePath.exitTime (euclideanBall x Rhat) w ≤ ENNReal.ofReal t} ≤
      ENNReal.ofReal (C * X m x *
        Real.exp (C * X m x * t / clock ((3 : ℝ) ^ n) - c * Rhat / (3 : ℝ) ^ n))
  exterior : ∀ n : ℕ, n ≤ m → ∀ Rhat : ℝ, C * (3 : ℝ) ^ n ≤ Rhat →
    SemigroupBlockNormLE a law t (euclideanBall x 1) (euclideanBall x Rhat)ᶜ
      (C * X m x * Real.exp (C * X m x * t / clock ((3 : ℝ) ^ n) - c * Rhat / (3 : ℝ) ^ n))
  thick_annulus : ∀ n : ℕ, n ≤ m → ∀ Rhat : ℝ, C * (3 : ℝ) ^ n ≤ Rhat →
    SemigroupBlockNormLE a law t (euclideanBall x (Rhat / 3)) (euclideanBall x Rhat)ᶜ
      (C * X m x * Real.exp (C * X m x * t / clock ((3 : ℝ) ^ n) - c * Rhat / (3 : ℝ) ^ n))
  two_ball : ∀ n : ℕ, n ≤ m → ∀ Rhat : ℝ, C * (3 : ℝ) ^ n ≤ Rhat →
    ∀ y : Vec d, euclideanNorm (x - y) = Rhat →
      ∀ rho : ℝ, 1 ≤ rho → rho ≤ Rhat / 4 →
        SemigroupBlockNormLE a law t (euclideanBall x rho) (euclideanBall y rho)
          (C * max (X m x) (X m y) *
            Real.exp (C * max (X m x) (X m y) * t / clock ((3 : ℝ) ^ n) -
              c * Rhat / (3 : ℝ) ^ n))

def IsControlledShape {d : ℕ} (grid : Finset (Vec d)) (x : Vec d) (n : ℕ) (rad : ℝ)
    (E : Set (Vec d)) : Prop :=
  ∃ y : Vec d, euclideanNorm (y - x) ≤ rad * (3 : ℝ) ^ n ∧
    ((∃ s : ℝ, (3 : ℝ) ^ n ≤ s ∧ s ≤ rad * (3 : ℝ) ^ n ∧ E = euclideanBall y s) ∨
      (∃ side : ℝ, IsGridCube grid y side ∧ (3 : ℝ) ^ n ≤ side ∧ side ≤ rad * (3 : ℝ) ^ n ∧
        E = centeredAxisCube y side))

def LocalScaleQuantitiesLE {d : ℕ} (M : GMCModel d) (omega : PotentialSample d)
    (clock : ℝ → ℝ) (n : ℕ) (y : Vec d) (B : ℝ) : Prop :=
  ∀ hb : ExactCircIntegrable (originCube d (n : ℤ))
      (fun z => aCutoff M n (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y omega) z /
        cubeAverage (originCube d (n : ℤ))
          (aCutoff M n (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y omega)) - 1),
    ∀ coeff : Homogenization.Book.Ch02.TriadicCoeffFamily d,
      (∀ᵐ z ∂(volume.restrict (openCubeSet (originCube d (n : ℤ)))),
          (coeff.coeffOn (originCube d (n : ℤ))).toCoeffField z =
            scalarMatrix (aCutoff M n
              (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y omega) z)) →
        ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 8 : ℝ) * (n : ℝ))) *
            SubdiffusiveProcess.CoarseGrainingVocab.paperNegativeBesovCircDiagonal (originCube d (n : ℤ))
              (1 / 8) (4 * (d : ℝ))
              (fun z => aCutoff M n (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y omega) z /
                cubeAverage (originCube d (n : ℤ))
                  (aCutoff M n (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y omega)) - 1) hb +
            ENNReal.ofReal ((3 : ℝ) ^ (2 * (n : ℝ)) *
              cubeAverage (originCube d (n : ℤ))
                (aCutoff M n (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y omega)) /
              (clock ((3 : ℝ) ^ n) *
                Homogenization.Book.Ch02.lambdaSq (originCube d (n : ℤ)) (1 / 2)
                  (.finite 1) coeff)) +
            ENNReal.ofReal (cubeAverage (originCube d (n : ℤ))
              (aCutoff M n (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y omega))) +
            ENNReal.ofReal (cubeAverage (originCube d (n : ℤ))
              (aCutoff M n (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y omega)))⁻¹ ≤
          ENNReal.ofReal B

def IsHolderMinimalScaleAt {d : ℕ} (M : GMCModel d) (C : ℝ) (n : ℕ) (y : Vec d)
    (omega : PotentialSample d) (Lval : ℕ) : Prop :=
  ∀ (u h : H1Function (openCubeSet (originCube d (n : ℤ)))) (g : Vec d → Vec d),
    IsDirichletSolutionOn
        (aCutoff M n (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y omega))
        (originCube d (n : ℤ)) u h g →
      MemHolder (cube d (n : ℤ)) (1 / 2) g →
      MemHolder (cube d (n : ℤ)) (1 / 2) h.grad →
        SubdiffusiveProcess.CoarseGrainingVocab.HolderRegularityConclusions M C n
          (SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSample y omega) stoppingAlphaZero n Lval u h g

def stoppingLogRatio {d : ℕ} (M : GMCModel d) (omega : AnchoredC11Sample d) (n : ℕ)
    (z : Vec d) : ℝ :=
  Real.log (aAnchored M omega z) - Real.log (aCutoff M n omega.val z)

def stoppingProfileAt {d : ℕ} (M : GMCModel d) (omega : AnchoredC11Sample d) (n : ℕ)
    (x : Vec d) : ℝ :=
  stoppingMassProfile (aAnchored M omega) (aCutoff M n omega.val) n x

def StoppingDerivativeBoundAt {d : ℕ} (M : GMCModel d) (omega : AnchoredC11Sample d)
    (C : ℝ) (y : Vec d) (B : ℝ) : Prop :=
  ∃ G Kap : ℝ, 0 ≤ G ∧ 0 ≤ Kap ∧
    (∀ z ∈ centeredAxisCube y C,
        euclideanNorm (euclideanGradient (fun w => Real.log (aAnchored M omega w)) z) ≤ G) ∧
    SubdiffusiveProcess.CoarseGrainingVocab.HolderSeminormBoundOn (centeredAxisCube y C) 1 Kap
      (euclideanGradient (fun w => Real.log (aAnchored M omega w))) ∧
    1 + G ^ 2 + Kap ≤ B

structure StoppingLocalBounds {d : ℕ} (M : GMCModel d) (omega : AnchoredC11Sample d)
    (clock : ℝ → ℝ) (grid : Finset (Vec d)) (p0 A C : ℝ) (m : ℕ) (x : Vec d) (K : ℝ) :
    Prop where
  local_scale : ∀ n : ℕ, (n : ℝ) ≤ (m : ℝ) + A * Real.log K → ∀ y : Vec d,
    IsGridCube grid y ((3 : ℝ) ^ n) →
    euclideanNorm (y - x) ≤ ((m : ℝ) + 2) ^ A * K ^ A * (3 : ℝ) ^ n →
      LocalScaleQuantitiesLE M omega.val clock n y (K ^ C)
  minimal_scale : ∀ n : ℕ, (n : ℝ) ≤ (m : ℝ) + A * Real.log K → ∀ y : Vec d,
    IsGridCube grid y ((3 : ℝ) ^ n) →
    euclideanNorm (y - x) ≤ ((m : ℝ) + 2) ^ A * K ^ A * (3 : ℝ) ^ n →
      ∃ Lval : ℕ, IsHolderMinimalScaleAt M C n y omega.val Lval ∧
        (Lval : ℝ≥0∞) +
            oscillation (centeredAxisCube y ((3 : ℝ) ^ n)) (stoppingLogRatio M omega n) ≤
          ENNReal.ofReal (C * Real.log K)
  scale_zero : ∀ y : Vec d, IsGridCube grid y 1 →
    euclideanNorm (y - x) ≤ C * ((m : ℝ) + 2) ^ A * K ^ A →
      StoppingDerivativeBoundAt M omega C y (C * Real.log K)
  scale_profile : ∀ i j : ℕ, i ≤ j → (j : ℝ) ≤ (m : ℝ) + A * Real.log K →
    K ^ (-C) * Real.exp (-(C * ((j : ℝ) - (i : ℝ)))) * stoppingProfileAt M omega i x ≤
        stoppingProfileAt M omega j x ∧
      stoppingProfileAt M omega j x ≤
        K ^ C * Real.exp (C * ((j : ℝ) - (i : ℝ))) * stoppingProfileAt M omega i x
  exit_upper_inputs : ∀ n : ℕ, (n : ℝ) ≤ (m : ℝ) + A * Real.log K → ∀ y : Vec d,
    IsGridCube grid y ((3 : ℝ) ^ n) →
    euclideanNorm (y - x) ≤ ((m : ℝ) + 2) ^ A * K ^ A * (3 : ℝ) ^ n →
      SobolevAssumption (aAnchored M omega) (aAnchored M omega)
          (centeredAxisCube y ((3 : ℝ) ^ n)) p0 (K ^ C) (clock ((3 : ℝ) ^ n)) ∧
        PoincareAssumption (aAnchored M omega) (aAnchored M omega)
          (centeredAxisCube y ((3 : ℝ) ^ n)) (K ^ C) (clock ((3 : ℝ) ^ n))

structure StoppingGradedBounds {d : ℕ} (M : GMCModel d) (omega : AnchoredC11Sample d)
    (clock : ℝ → ℝ) (grid : Finset (Vec d)) (A CA C : ℝ) (m : ℕ) (x : Vec d) (K : ℝ)
    (j : ℕ) : Prop where
  local_scale : ∀ n : ℕ, (n : ℝ) ≤ (m : ℝ) + A * Real.log K + (j : ℝ) → ∀ y : Vec d,
    IsGridCube grid y ((3 : ℝ) ^ n) →
    euclideanNorm (y - x) ≤
        ((m : ℝ) + 2) ^ A * K ^ A * Real.exp (j : ℝ) * (3 : ℝ) ^ n →
      LocalScaleQuantitiesLE M omega.val clock n y (K ^ CA * Real.exp (C * (j : ℝ)))
  minimal_scale : ∀ n : ℕ, (n : ℝ) ≤ (m : ℝ) + A * Real.log K + (j : ℝ) → ∀ y : Vec d,
    IsGridCube grid y ((3 : ℝ) ^ n) →
    euclideanNorm (y - x) ≤
        ((m : ℝ) + 2) ^ A * K ^ A * Real.exp (j : ℝ) * (3 : ℝ) ^ n →
      ∃ Lval : ℕ, IsHolderMinimalScaleAt M C n y omega.val Lval ∧
        (Lval : ℝ≥0∞) +
            oscillation (centeredAxisCube y ((3 : ℝ) ^ n)) (stoppingLogRatio M omega n) ≤
          ENNReal.ofReal (CA * Real.log K + C * (j : ℝ))
  scale_zero : ∀ y : Vec d, IsGridCube grid y 1 →
    euclideanNorm (y - x) ≤ ((m : ℝ) + 2) ^ A * K ^ A * Real.exp (j : ℝ) →
      StoppingDerivativeBoundAt M omega C y (CA * Real.log K + C * (j : ℝ))
  mass_profile : ∀ n : ℕ, (n : ℝ) ≤ (m : ℝ) + A * Real.log K + (j : ℝ) → ∀ y : Vec d,
    IsGridCube grid y ((3 : ℝ) ^ n) →
    euclideanNorm (y - x) ≤
        ((m : ℝ) + 2) ^ A * K ^ A * Real.exp (j : ℝ) * (3 : ℝ) ^ n →
      ENNReal.ofReal (K ^ (-CA) * Real.exp (-(C * (j : ℝ))) * stoppingProfileAt M omega n x) ≤
          weightedMeasure (aAnchored M omega) (centeredAxisCube y ((3 : ℝ) ^ n)) ∧
        weightedMeasure (aAnchored M omega) (centeredAxisCube y ((3 : ℝ) ^ n)) ≤
          ENNReal.ofReal (K ^ CA * Real.exp (C * (j : ℝ)) * stoppingProfileAt M omega n x)
  relative_mass : ∀ N : ℕ, (N : ℝ) ≤ (m : ℝ) + A * Real.log K → ∀ y : Vec d,
    IsGridCube grid y ((3 : ℝ) ^ N) →
    euclideanNorm (y - x) ≤ ((m : ℝ) + 2) ^ A * K ^ A * (3 : ℝ) ^ N →
      ∀ (w : Vec d) (r : ℝ), IsGridCube grid w r → 1 ≤ r → r ≤ (3 : ℝ) ^ N →
        centeredAxisCube w r ⊆ centeredAxisCube y ((3 : ℝ) ^ N) →
          ENNReal.ofReal (K ^ (-CA) * (r / (3 : ℝ) ^ N) ^ C) *
              weightedMeasure (aAnchored M omega) (centeredAxisCube y ((3 : ℝ) ^ N)) ≤
            weightedMeasure (aAnchored M omega) (centeredAxisCube w r)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
