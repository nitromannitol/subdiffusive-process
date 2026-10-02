import SubdiffusiveProcess.Probability.Diffusion.AnalyticInput
import SubdiffusiveProcess.DirichletForm.Regular
import SubdiffusiveProcess.DirichletForm.Resolvent
import MarkovProcess.Main



open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.E7

/-- The restriction of an `L²(m)` class to `L²(m|U)`. -/
def restrictLp {X : Type*} [MeasurableSpace X] {m : Measure X} (U : Set X)
    (u : Lp ℝ 2 m) : Lp ℝ 2 (m.restrict U) :=
  ((Lp.memLp u).restrict U).toLp u

/-- `u` lies in the domain of `E` and is an energy-norm limit of core functions of `E` supported in
`U` (so, in particular, `u` vanishes almost everywhere outside `U`). -/
def IsCoreLimitOn {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}
    (E : DirichletForm.ClosedForm m) (U : Set X) (u : Lp ℝ 2 m) : Prop :=
  u ∈ E.domain ∧ ∃ w : ℕ → Lp ℝ 2 m, (∀ n, E.MemCoreOn U (w n)) ∧
    Tendsto (fun n => E.energyNormSq (u - w n)) atTop (𝓝 0)

/-- The part of the closed form `E` on `U`, as a form on `L²(m|U)`: its domain is the set of
restrictions of energy-norm limits of core functions supported in `U`, and it agrees with `E` on
those limits. -/
structure IsPartFormOn {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}
    (E : DirichletForm.ClosedForm m) (U : Set X) (F : DirichletForm.ClosedForm (m.restrict U)) :
    Prop where
  mem_domain_iff : ∀ v : Lp ℝ 2 (m.restrict U), v ∈ F.domain ↔
    ∃ u : Lp ℝ 2 m, IsCoreLimitOn E U u ∧ restrictLp U u = v
  form_eq : ∀ u v : Lp ℝ 2 m, IsCoreLimitOn E U u → IsCoreLimitOn E U v →
    F.form (restrictLp U u) (restrictLp U v) = E.form u v

/-- **Feller ⇒ strong Markov**, in restart form for the lifetime-path law of a continuous-path
realization (Revuz–Yor, *Continuous Martingales and Brownian Motion*, Thm III.3.1;
Kallenberg, *Foundations of Modern Probability*, Thm 19.17). -/
def FellerStrongMarkov : Prop :=
  ∀ (d : ℕ) (P : SubMarkovKernelSemigroup (Fin d → ℝ)), P.IsConservative →
    P.IsFellerKernelSemigroup →
    ∀ K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ)), IsMarkovKernel K →
      (∀ I x, K.map (ContinuousPath.finsetEvaluation I) x =
        SubMarkovKernelSemigroup.finiteSetKernel P I x) →
      SubdiffusiveProcess.Probability.Diffusion.Input.Restart (K.map LifetimePath.ofContinuousPath)

/-- The killed occupation resolvent of a nonnegative function, as an extended-real integral:
`x ↦ E_x ∫_0^{τ_U} e^{-αt} f(X_t) dt`. -/
def killedOcc {d : ℕ} (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ))) (U : Set (Fin d → ℝ))
    (α : ℝ) (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-α * t)) *
    ∫⁻ w in {w | ENNReal.ofReal t < LifetimePath.exitTime U w},
      ENNReal.ofReal (f (SubdiffusiveProcess.Probability.Diffusion.Input.stateAt (Real.toNNReal t) w))
        ∂(K.map LifetimePath.ofContinuousPath x)

/-- **FOT, part of a Hunt process on an open set** (Fukushima–Oshima–Takeda, 2nd ed.,
Thm 4.4.2 and Thm 4.4.3), for a conservative Feller diffusion `K` associated with a regular
Dirichlet form `E` on `L²(m)` (`m` a Radon measure with full support): the part form of `E` on the open set `U` (domain: the energy-norm
closure of the core functions supported in `U`) is a closed form on `L²(m|U)`, and for every
nonnegative `f ∈ L²(m|U)` the killed occupation resolvent `x ↦ E_x ∫_0^{τ_U} e^{-αt} f(X_t) dt` of
`K` is finite `m`-a.e. on `U` and is a version of the resolvent `G^U_α f` of the part form.
Association is required on continuous compactly supported data at the level of resolvents. -/
def FOTPartProcess : Prop :=
  ∀ (d : ℕ) (m : Measure (Fin d → ℝ)), IsLocallyFiniteMeasure m → m.IsOpenPosMeasure →
    ∀ E : _root_.DirichletForm m, DirichletForm.IsRegular E.toClosedForm →
    ∀ (P : SubMarkovKernelSemigroup (Fin d → ℝ)), P.IsConservative → P.IsFellerKernelSemigroup →
    ∀ K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ)), IsMarkovKernel K →
      (∀ I x, K.map (ContinuousPath.finsetEvaluation I) x =
        SubMarkovKernelSemigroup.finiteSetKernel P I x) →
      (∀ (μ : ℝ), 0 < μ → ∀ G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m,
        DirichletForm.IsResolvent E.toClosedForm μ G →
        ∀ (g : (Fin d → ℝ) → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g)
          (hgL : MemLp g 2 m),
          (fun x => ∫ t in Ioi (0 : ℝ), Real.exp (-μ * t) *
              ∫ w, g (w (Real.toNNReal t)) ∂(K x)) =ᵐ[m] ⇑(G (hgL.toLp g))) →
      ∀ U : Set (Fin d → ℝ), IsOpen U →
        ∃ F : DirichletForm.ClosedForm (m.restrict U), IsPartFormOn E.toClosedForm U F ∧
          ∀ (α : ℝ), 0 < α → ∀ G : Lp ℝ 2 (m.restrict U) →L[ℝ] Lp ℝ 2 (m.restrict U),
            DirichletForm.IsResolvent F α G →
            ∀ (f : (Fin d → ℝ) → ℝ), Measurable f → (∀ x, 0 ≤ f x) →
              ∀ hf : MemLp f 2 (m.restrict U),
                (∀ᵐ x ∂(m.restrict U), killedOcc K U α f x < ⊤) ∧
                (fun x => (killedOcc K U α f x).toReal) =ᵐ[m.restrict U] ⇑(G (hf.toLp f))

end SubdiffusiveProcess.E7
