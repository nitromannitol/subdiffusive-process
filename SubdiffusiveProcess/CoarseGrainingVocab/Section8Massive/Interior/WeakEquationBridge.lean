module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.ScalarDivergenceLift
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WeightedMassiveSolution

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- The scalar residual left after moving the zeroth-order term of the massive
equation to the right-hand side. -/
def massiveResidual (rho : Vec d → ℝ) (mu : ℝ) {W : Set (Vec d)}
    (u : H1Function W) (f : Vec d → ℝ) : Vec d → ℝ :=
  fun x ↦ rho x * (f x - mu * u.toFun x)

/-- A vector field realizes the massive residual as a weak divergence.  This
functional spelling is meaningful without separately asserting integrability
of the pointwise residual expression. -/
def IsMassiveResidualLiftOn (rho : Vec d → ℝ) (mu : ℝ) (W : Set (Vec d))
    (u : H1Function W) (f : Vec d → ℝ) (g : Vec d → Vec d) : Prop :=
  ∀ phi : H10Function W,
    (∫ x in W, rho x * f x * phi.toH1Function.toFun x ∂volume) -
        mu * ∫ x in W, rho x * u.toFun x * phi.toH1Function.toFun x ∂volume =
      -∫ x in W, vecDot (g x) (phi.toH1Function.grad x) ∂volume

/-- The exact regularity upgrade needed to feed the massive residual into the
frozen Section 6 interior Hölder anchor.  The existing Riesz and cube-Poisson
lifts establish the first conjunct only; they do not establish `MemHolder`. -/
def HasHolderMassiveResidualLiftOn (rho : Vec d → ℝ) (mu : ℝ)
    (W : Set (Vec d)) (u : H1Function W) (f : Vec d → ℝ) : Prop :=
  ∃ g : Vec d → Vec d,
    IsMassiveResidualLiftOn rho mu W u f g ∧ MemHolder W (1 / 2) g

/-- A massive weak solution is a divergence-form weak solution once the
massive scalar residual has a weak divergence lift. -/
theorem isDivFormWeakSolutionOn_of_isMassiveWeakSolutionOn
    {W : Set (Vec d)} {c rho : Vec d → ℝ} {mu : ℝ}
    {u : H1Function W} {f : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : IsMassiveWeakSolutionOn c rho mu W u f)
    (hg : IsMassiveResidualLiftOn rho mu W u f g) :
    IsDivFormWeakSolutionOn c W u g := by
  intro phi
  have huPhi := hu phi
  have hgPhi := hg phi
  linarith

/-- A Hölder massive-residual lift packages exactly the divergence-form weak
solution and datum hypotheses consumed by the Section 6 interior anchor. -/
theorem exists_divFormWeakSolutionOn_and_memHolder_of_massive
    {W : Set (Vec d)} {c rho : Vec d → ℝ} {mu : ℝ}
    {u : H1Function W} {f : Vec d → ℝ}
    (hu : IsMassiveWeakSolutionOn c rho mu W u f)
    (hLift : HasHolderMassiveResidualLiftOn rho mu W u f) :
    ∃ g : Vec d → Vec d,
      IsDivFormWeakSolutionOn c W u g ∧ MemHolder W (1 / 2) g := by
  obtain ⟨g, hgLift, hgHolder⟩ := hLift
  exact ⟨g, isDivFormWeakSolutionOn_of_isMassiveWeakSolutionOn hu hgLift,
    hgHolder⟩

/-- The pointwise residual pairing gives the functional massive-residual lift.
The boundedness assumptions are used only to justify splitting its integral. -/
theorem isMassiveResidualLiftOn_of_integral_pairing
    {W : Set (Vec d)} {rho : Vec d → ℝ} {mu rhoMax : ℝ}
    {u : H1Function W} {f : Vec d → ℝ} {g : Vec d → Vec d}
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict W))
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict W), |rho x| ≤ rhoMax)
    (hf : MemL2On W f)
    (hg : ∀ phi : H10Function W,
      ∫ x in W, massiveResidual rho mu u f x * phi.toH1Function.toFun x ∂volume =
        -∫ x in W, vecDot (g x) (phi.toH1Function.grad x) ∂volume) :
    IsMassiveResidualLiftOn rho mu W u f g := by
  intro phi
  have hmassF : IntegrableOn
      (fun x ↦ rho x * f x * phi.toH1Function.toFun x) W :=
    integrableOn_mass_term hrhoMeas hrhoBdd hf phi.toH1Function.memL2
  have hmassU : IntegrableOn
      (fun x ↦ rho x * u.toFun x * phi.toH1Function.toFun x) W :=
    integrableOn_mass_term hrhoMeas hrhoBdd u.memL2 phi.toH1Function.memL2
  have hresidual :
      (∫ x in W, massiveResidual rho mu u f x * phi.toH1Function.toFun x ∂volume) =
        (∫ x in W, rho x * f x * phi.toH1Function.toFun x ∂volume) -
          mu * ∫ x in W, rho x * u.toFun x * phi.toH1Function.toFun x ∂volume := by
    calc
      (∫ x in W, massiveResidual rho mu u f x * phi.toH1Function.toFun x ∂volume) =
          ∫ x in W,
            (rho x * f x * phi.toH1Function.toFun x) -
              mu * (rho x * u.toFun x * phi.toH1Function.toFun x) ∂volume := by
            apply integral_congr_ae
            filter_upwards with x
            simp only [massiveResidual]
            ring
      _ = (∫ x in W, rho x * f x * phi.toH1Function.toFun x ∂volume) -
          ∫ x in W, mu * (rho x * u.toFun x * phi.toH1Function.toFun x) ∂volume := by
            rw [integral_sub hmassF (hmassU.const_mul mu)]
      _ = (∫ x in W, rho x * f x * phi.toH1Function.toFun x ∂volume) -
          mu * ∫ x in W, rho x * u.toFun x * phi.toH1Function.toFun x ∂volume := by
            rw [integral_const_mul]
  rw [← hresidual]
  exact hg phi



theorem exists_h1_divergence_lift_of_isMassiveWeakSolutionOn
    (d : ℕ) [NeZero d] {m : ℕ} {c rho : Vec d → ℝ} {mu rhoMax : ℝ}
    {u : H1Function (openCubeSet (originCube d m))} {f : Vec d → ℝ}
    (hrhoMeas : AEStronglyMeasurable rho
      (volume.restrict (openCubeSet (originCube d m))))
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
      |rho x| ≤ rhoMax)
    (hf : MemL2On (openCubeSet (originCube d m)) f)
    (hu : IsMassiveWeakSolutionOn c rho mu (cube d m) u f) :
    ∃ G : CubeVectorH1Function (originCube d m),
      IsMassiveResidualLiftOn rho mu (cube d m) u f G.toField ∧
        IsDivFormWeakSolutionOn c (cube d m) u G.toField := by
  have hdiff : MemL2On (cube d m) (fun x ↦ f x - mu * u.toFun x) :=
    hf.sub (u.memL2.const_mul mu)
  have hresidual : MemL2On (cube d m) (massiveResidual rho mu u f) :=
    memL2On_mul_of_bounded hrhoMeas hrhoBdd hdiff
  obtain ⟨C, _hCnonneg, hC⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.exists_cubeVectorH1Function_divergence_lift d
  obtain ⟨G, hpairing, _hGbound⟩ :=
    hC (originCube d m) (massiveResidual rho mu u f) hresidual
  have hLift : IsMassiveResidualLiftOn rho mu (cube d m) u f G.toField :=
    isMassiveResidualLiftOn_of_integral_pairing hrhoMeas hrhoBdd hf hpairing
  exact ⟨G, hLift,
    isDivFormWeakSolutionOn_of_isMassiveWeakSolutionOn hu hLift⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
