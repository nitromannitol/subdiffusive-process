module

public import Homogenization.Ambient.HilbertFinite
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule

@[expose] public section




open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Stationary

noncomputable section

variable {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
variable {mu : Measure Omega}
variable [AddAction (Vec d) Omega]
variable [MeasurableConstVAdd (Vec d) Omega]
variable [VAddInvariantMeasure (Vec d) Omega mu]

/-- A fixed stationary translation is measure-preserving. -/
theorem measurePreserving_const_vadd (x : Vec d) :
    MeasurePreserving (fun omega : Omega => x +ᵥ omega) mu mu := by
  refine ⟨measurable_const_vadd x, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_const_vadd x) hs]
  exact VAddInvariantMeasure.measure_preimage_vadd x hs

/-- Scalar stationary square-integrable random variables. -/
abbrev ScalarL2 (mu : Measure Omega) := Lp ℝ 2 mu

/-- Vector-valued stationary square-integrable random variables. -/
abbrev VectorL2 (d : ℕ) (mu : Measure Omega) := Lp (HilbertVec d) 2 mu

/-- The Koopman isometry induced by a measure-preserving translation. -/
def koopman {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : Vec d) : Lp E 2 mu →ₗᵢ[ℝ] Lp E 2 mu :=
  Lp.compMeasurePreservingₗᵢ ℝ (x +ᵥ ·)
    (measurePreserving_const_vadd (mu := mu) x)

/-- The `i`th coordinate of a vector-valued stationary `L²` variable. -/
def vectorL2Coord (i : Fin d) : VectorL2 d mu →L[ℝ] ScalarL2 mu :=
  (PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) i).compLpL 2 mu

/-- `F` is the full strong horizontal gradient of `phi`. -/
def HasHorizontalGradient (phi : ScalarL2 mu) (F : VectorL2 d mu) : Prop :=
  ∀ i : Fin d,
    HasDerivAt
      (fun t : ℝ =>
        koopman (mu := mu) (t • (Pi.single i 1 : Vec d)) phi)
      (vectorL2Coord (mu := mu) i F) 0

theorem hasHorizontalGradient_zero :
    HasHorizontalGradient (mu := mu) (d := d) 0 0 := by
  intro i
  simpa only [map_zero] using
    (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ScalarL2 mu)))

theorem HasHorizontalGradient.add {phi psi : ScalarL2 mu}
    {F G : VectorL2 d mu}
    (hphi : HasHorizontalGradient (mu := mu) phi F)
    (hpsi : HasHorizontalGradient (mu := mu) psi G) :
    HasHorizontalGradient (mu := mu) (phi + psi) (F + G) := by
  intro i
  convert (hphi i).add (hpsi i) using 1
  · funext t
    exact map_add
      (koopman (mu := mu) (t • (Pi.single i 1 : Vec d))) phi psi
  · exact (vectorL2Coord (mu := mu) i).map_add F G

theorem HasHorizontalGradient.sub {phi psi : ScalarL2 mu}
    {F G : VectorL2 d mu}
    (hphi : HasHorizontalGradient (mu := mu) phi F)
    (hpsi : HasHorizontalGradient (mu := mu) psi G) :
    HasHorizontalGradient (mu := mu) (phi - psi) (F - G) := by
  intro i
  convert (hphi i).sub (hpsi i) using 1
  · funext t
    exact map_sub
      (koopman (mu := mu) (t • (Pi.single i 1 : Vec d))) phi psi
  · exact (vectorL2Coord (mu := mu) i).map_sub F G

theorem HasHorizontalGradient.smul (c : ℝ) {phi : ScalarL2 mu}
    {F : VectorL2 d mu}
    (hphi : HasHorizontalGradient (mu := mu) phi F) :
    HasHorizontalGradient (mu := mu) (c • phi) (c • F) := by
  intro i
  convert (hphi i).const_smul c using 1
  · funext t
    exact map_smul
      (koopman (mu := mu) (t • (Pi.single i 1 : Vec d))) c phi
  · exact (vectorL2Coord (mu := mu) i).map_smul c F

/-- The linear range of all full strong horizontal gradients. -/
def horizontalGradientRange : Submodule ℝ (VectorL2 d mu) where
  carrier := {F | ∃ phi, HasHorizontalGradient (mu := mu) phi F}
  zero_mem' := ⟨0, hasHorizontalGradient_zero (mu := mu) (d := d)⟩
  add_mem' := by
    rintro F G ⟨phi, hphi⟩ ⟨psi, hpsi⟩
    exact ⟨phi + psi, hphi.add hpsi⟩
  smul_mem' := by
    rintro c F ⟨phi, hphi⟩
    exact ⟨c • phi, hphi.smul c⟩

/-- The closed stationary potential subspace. -/
def stationaryPotentialSubspace : Submodule ℝ (VectorL2 d mu) :=
  (horizontalGradientRange (mu := mu) (d := d)).topologicalClosure

/-- The stationary solenoidal subspace. -/
def stationarySolenoidalSubspace : Submodule ℝ (VectorL2 d mu) :=
  (stationaryPotentialSubspace (mu := mu) (d := d))ᗮ

instance stationaryPotentialSubspace_hasOrthogonalProjection :
    (stationaryPotentialSubspace (mu := mu) (d := d)).HasOrthogonalProjection := by
  letI : CompleteSpace (stationaryPotentialSubspace (mu := mu) (d := d)) := by
    change CompleteSpace
      (horizontalGradientRange (mu := mu) (d := d)).topologicalClosure
    infer_instance
  infer_instance

/-- Orthogonal projection onto stationary potential fields. -/
def stationaryPotentialProjection : VectorL2 d mu →L[ℝ] VectorL2 d mu :=
  (stationaryPotentialSubspace (mu := mu) (d := d)).starProjection

theorem stationaryPotentialProjection_mem (F : VectorL2 d mu) :
    stationaryPotentialProjection (mu := mu) F ∈
      stationaryPotentialSubspace (mu := mu) (d := d) :=
  Submodule.starProjection_apply_mem _ _

/-- Every stationary potential field is approximated in `L²` by an actual
strong horizontal gradient of a stationary scalar `L²` potential.  This is
the density input for finite-volume cutoff competitors. -/
theorem exists_hasHorizontalGradient_norm_sub_lt
    {F : VectorL2 d mu}
    (hF : F ∈ stationaryPotentialSubspace (mu := mu) (d := d))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ phi : ScalarL2 mu, ∃ G : VectorL2 d mu,
      HasHorizontalGradient (mu := mu) phi G ∧ ‖F - G‖ < epsilon := by
  have hclosure : F ∈ closure
      (horizontalGradientRange (mu := mu) (d := d) : Set (VectorL2 d mu)) := by
    exact hF
  obtain ⟨G, hG, hdist⟩ :=
    Metric.mem_closure_iff.1 hclosure epsilon hepsilon
  rcases hG with ⟨phi, hphi⟩
  exact ⟨phi, G, hphi, by simpa only [dist_eq_norm] using hdist⟩

theorem sub_stationaryPotentialProjection_mem_orthogonal
    (F : VectorL2 d mu) :
    F - stationaryPotentialProjection (mu := mu) F ∈
      stationarySolenoidalSubspace (mu := mu) (d := d) :=
  Submodule.sub_starProjection_mem_orthogonal
    (K := stationaryPotentialSubspace (mu := mu) (d := d)) F

/-- Potential membership and the weak divergence identity characterize the
stationary potential projection. -/
theorem eq_stationaryPotentialProjection_of_mem_of_sub_mem_orthogonal
    {F q : VectorL2 d mu}
    (hq : q ∈ stationaryPotentialSubspace (mu := mu) (d := d))
    (hFq : F - q ∈ stationarySolenoidalSubspace (mu := mu) (d := d)) :
    q = stationaryPotentialProjection (mu := mu) F := by
  exact (Submodule.eq_starProjection_of_mem_orthogonal hq hFq).symm

section ContinuousAction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace Omega] [R1Space Omega] [BorelSpace Omega]
variable [ContinuousVAdd (Vec d) Omega]
variable [IsLocallyFiniteMeasure mu] [mu.InnerRegularCompactLTTop]

/-- Every Koopman orbit is strongly continuous under the standard topological
hypotheses on the stationary carrier.  This is the continuity input required
by the spectral representation of the translation action. -/
theorem continuous_koopman_orbit (f : Lp E 2 mu) :
    Continuous (fun x : Vec d => koopman (mu := mu) x f) := by
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  change Continuous (fun x : Vec d => DomAddAct.mk x +ᵥ f)
  exact DomAddAct.continuous_mk.vadd continuous_const

end ContinuousAction

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Stationary
