module

public import SubdiffusiveProcess.DirichletForm.FOTCapacity
public import SubdiffusiveProcess.DirichletForm.FOTCoreCalculus
public import SubdiffusiveProcess.DirichletForm.FOTQuasiContinuousAgreement

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

def QuasiContinuousOn (F : _root_.SubdiffusiveProcess.DirichletForm m) (U : Set X) (f : X → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ O : Set X, IsOpen O ∧ O ⊆ U ∧
    coreCapacity F U O < ENNReal.ofReal ε ∧ ContinuousOn f (U \ O)

/-- One Borel representative family produced by quasi-uniform core approximation. -/
structure RepresentativeFamily {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X}
    (Γ : EnergyFamily F U) where
  rep : ∀ (u : Lp ℝ 2 m), u ∈ F.domain → X → ℝ
  measurable : ∀ (u : Lp ℝ 2 m) (hu : u ∈ F.domain), Measurable (rep u hu)
  ae_rep : ∀ (u : Lp ℝ 2 m) (hu : u ∈ F.domain), ⇑u =ᵐ[m] rep u hu
  quasiContinuous : ∀ (u : Lp ℝ 2 m) (hu : u ∈ F.domain), QuasiContinuousOn F U (rep u hu)
  continuous_agree : ∀ (u : Lp ℝ 2 m) (hu : u ∈ F.domain), ∀ f : X → ℝ, Continuous f → ⇑u =ᵐ[m] f →
    ∀ w ∈ F.domain, rep u hu =ᵐ[Γ.measure w] f
  approx_ae : ∀ (u : Lp ℝ 2 m) (hu : u ∈ F.domain), ∀ un : ℕ → Lp ℝ 2 m,
    (∀ n, F.toClosedForm.MemCoreOn U (un n)) →
    ∀ fn : ℕ → X → ℝ,
      (∀ n, Continuous (fn n) ∧ HasCompactSupport (fn n) ∧ tsupport (fn n) ⊆ U ∧
        ⇑(un n) =ᵐ[m] fn n) →
      Tendsto (fun n => F.energyNormSq (un n - u)) atTop (𝓝 0) →
      ∃ seq : ℕ → ℕ, StrictMono seq ∧
        ∀ w ∈ F.domain, ∀ᵐ x ∂Γ.measure w,
          Tendsto (fun n => fn (seq n) x) atTop (𝓝 (rep u hu x))

theorem exists_representativeFamily [T2Space X] [LocallyCompactSpace X] [BorelSpace X]
    [SecondCountableTopology X] {F : _root_.SubdiffusiveProcess.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) : Nonempty (RepresentativeFamily Γ) := by
  classical
  let q : ∀ (u : Lp ℝ 2 m), u ∈ F.domain → CoreRepresentative F U u :=
    fun u hu => Classical.choice (exists_coreRepresentative F h hu)
  refine ⟨{
    rep := fun u hu => (q u hu).toFun
    measurable := fun u hu => (q u hu).measurable
    ae_rep := fun u hu => (q u hu).ae_rep
    quasiContinuous := fun u hu => (q u hu).quasiContinuous
    continuous_agree := ?_
    approx_ae := ?_ }⟩
  · intro u hu f hf hfae
    exact (q u hu).continuous_agree h Γ hu hf hfae
  · intro u hu un hun fn hfn henergy
    exact (q u hu).approx_ae h Γ un hun fn hfn henergy

end SubdiffusiveProcess.DirichletForm.FOTConstruction
