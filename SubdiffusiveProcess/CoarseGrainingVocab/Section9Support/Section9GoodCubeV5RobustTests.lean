import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeFiniteLocalTests




set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The positive continuous multiplier condition, modulo one positive constant.
The observation set must contain all the cubes on which tests are consumed. -/
def GoodCubeV5AdmissibleMultiplier {d : ℕ} (S : Set (Vec d)) (epsilon : ℝ)
    (theta : Vec d → ℝ) : Prop :=
  ContinuousOn theta S ∧ (∀ x ∈ S, 0 < theta x) ∧
    ∃ k > 0, ∀ x ∈ S, |k⁻¹ * theta x - 1| ≤ epsilon

/-- A coefficient-local, law-independent interface retaining the multiplier.
`A`, `eps`, and `massFraction` include the perturbation losses; they need not
equal the constants of the unperturbed input tests.  In particular, this is
stronger than `GoodCubeFiniteLocalTests a ...`. -/
def GoodCubeV5RobustFiniteLocalTests {d : ℕ} (a : Vec d → ℝ)
    (S : Set (Vec d)) (epsilon p A sigma eps epsH massFraction : ℝ)
    (clock : ℝ → ℝ) (G : Finset (ℤ × Vec d))
    (Pairs : Set (Cube d × Cube d)) : Prop :=
  ∀ theta : Vec d → ℝ, GoodCubeV5AdmissibleMultiplier S epsilon theta →
    GoodCubeFiniteLocalTests (fun x => a x * theta x)
      p A sigma eps epsH massFraction clock G Pairs

/-- The exported pairs retain their own contraction tolerance, separately from
the auxiliary torsion-cover tolerance in the finite tests.  This is the first
display of the printed robust regularity event at 13039-13051. -/
def GoodCubeV5RobustHarmonicOscillation {d : ℕ} (a : Vec d → ℝ)
    (S : Set (Vec d)) (epsilon eps0 : ℝ) (Pfam : Set (Cube d × Cube d)) : Prop :=
  ∀ theta : Vec d → ℝ, GoodCubeV5AdmissibleMultiplier S epsilon theta →
    LocalHarmonicOscillation (fun x => a x * theta x) eps0 Pfam

/-- Read the robust contraction on the actual coefficient with the same tolerance. -/
theorem goodCubeV5RobustHarmonicOscillation_of_eqOn {d : ℕ}
    {a b theta : Vec d → ℝ} {S : Set (Vec d)} {epsilon eps0 : ℝ}
    {Pfam : Set (Cube d × Cube d)}
    (h : GoodCubeV5RobustHarmonicOscillation a S epsilon eps0 Pfam)
    (htheta : GoodCubeV5AdmissibleMultiplier S epsilon theta)
    (hab : EqOn (fun x => a x * theta x) b S)
    (hpairs : ∀ q ∈ Pfam, cubeSet q.2 ⊆ S) :
    LocalHarmonicOscillation b eps0 Pfam :=
  (goodCube_localHarmonicOscillation_congr_coeff hab hpairs).mp (h theta htheta)

/-- Robust tests retain the unperturbed tests without asking for a diffusion law. -/
theorem goodCubeV5RobustFiniteLocalTests_cutoff {d : ℕ} {a : Vec d → ℝ}
    {S : Set (Vec d)} {epsilon p A sigma eps epsH massFraction : ℝ}
    {clock : ℝ → ℝ} {G : Finset (ℤ × Vec d)} {Pairs : Set (Cube d × Cube d)}
    (hepsilon : 0 ≤ epsilon)
    (h : GoodCubeV5RobustFiniteLocalTests a S epsilon
      p A sigma eps epsH massFraction clock G Pairs) :
    GoodCubeFiniteLocalTests a p A sigma eps epsH massFraction clock G Pairs := by
  simpa using h (fun _ => 1)
    ⟨continuousOn_const, fun _ _ => one_pos,
      1, one_pos, fun _ _ => by simpa using hepsilon⟩

/-- All four tests can be read on any coefficient represented locally by an
admissible multiplier.  This is equality on the observation set, not a change
of the process law. -/
theorem goodCubeV5RobustFiniteLocalTests_of_eqOn {d : ℕ}
    {a b theta : Vec d → ℝ} {S : Set (Vec d)}
    {epsilon p A sigma eps epsH massFraction : ℝ} {clock : ℝ → ℝ}
    {G : Finset (ℤ × Vec d)} {Pairs : Set (Cube d × Cube d)}
    (h : GoodCubeV5RobustFiniteLocalTests a S epsilon
      p A sigma eps epsH massFraction clock G Pairs)
    (htheta : GoodCubeV5AdmissibleMultiplier S epsilon theta)
    (hab : EqOn (fun x => a x * theta x) b S)
    (hinside : ∀ q ∈ G, cubeSet (q.2, (3 : ℝ)^q.1) ⊆ S)
    (hpairs : ∀ q ∈ Pairs, cubeSet q.2 ⊆ S) :
    GoodCubeFiniteLocalTests b p A sigma eps epsH massFraction clock G Pairs :=
  (goodCube_finiteLocalTests_congr_coeff hab p A sigma eps epsH massFraction
    clock G Pairs hinside hpairs).mp (h theta htheta)

/-- The robust package is itself coefficient-local on the common observation. -/
theorem goodCubeV5RobustFiniteLocalTests_congr_coeff {d : ℕ}
    {a b : Vec d → ℝ} {S : Set (Vec d)} (hab : EqOn a b S)
    (epsilon p A sigma eps epsH massFraction : ℝ) (clock : ℝ → ℝ)
    (G : Finset (ℤ × Vec d)) (Pairs : Set (Cube d × Cube d))
    (hinside : ∀ q ∈ G, cubeSet (q.2, (3 : ℝ)^q.1) ⊆ S)
    (hpairs : ∀ q ∈ Pairs, cubeSet q.2 ⊆ S) :
    GoodCubeV5RobustFiniteLocalTests a S epsilon
        p A sigma eps epsH massFraction clock G Pairs ↔
      GoodCubeV5RobustFiniteLocalTests b S epsilon
        p A sigma eps epsH massFraction clock G Pairs := by
  have hprod (theta : Vec d → ℝ) : EqOn (fun x => a x * theta x)
      (fun x => b x * theta x) S := fun x hx => congrArg (· * theta x) (hab hx)
  constructor
  · intro h theta htheta
    exact (goodCube_finiteLocalTests_congr_coeff (hprod theta)
      p A sigma eps epsH massFraction clock G Pairs hinside hpairs).mp (h theta htheta)
  · intro h theta htheta
    exact (goodCube_finiteLocalTests_congr_coeff (hprod theta)
      p A sigma eps epsH massFraction clock G Pairs hinside hpairs).mpr (h theta htheta)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
