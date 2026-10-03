module

public import SubdiffusiveProcess.Paper.t_A_short
public import SubdiffusiveProcess.Paper.t_A
public import SubdiffusiveProcess.Paper.t_B
public import SubdiffusiveProcess.Paper.t_C

@[expose] public section

/-! The main theorems of Armstrong, Bou-Rabee and Kuusi. -/

noncomputable section

open Filter MeasureTheory ProbabilityTheory Topology Asymptotics SubdiffusiveProcess MarkovProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Paper

/-- **Theorem A (introduction, `t.A`).** -/
theorem _root_.SubdiffusiveProcess.process_convergence
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        0 < M.delta → M.delta ≤ delta0 →
        let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ)) :=
          ⟨fun g ↦ g.1.1, continuous_subtype_val.fst⟩
        let nu := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).map forget
        let law := (commonScaleLaw d nu).toMeasure
        ∃ C eta : ℝ, 0 < eta ∧
        (d = 2 → eta = SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P / Real.log 3) ∧
        ∃ H : BilateralField d → C(SpatialCoordinates d, ℝ), Measurable H ∧
        ∃ PN : ℕ → BilateralField d →
            SubMarkovKernelSemigroup (SpatialCoordinates d),
        ∃ _hPN : ∀ N omega, (PN N omega).IsConservative,
        ∃ P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d),
        ∃ _hP : ∀ omega, (P omega).IsConservative,
        ∃ KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d),
        ∃ _hKN : ∀ N, IsMarkovKernel (KN N),
        ∃ K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d),
        ∃ hK : IsMarkovKernel K,
          (∀ omega : BilateralField d,
            Continuous (fun x ↦ jointPathProbabilityMeasure K hK omega x)) ∧
          (∀ᵐ omega ∂law,
            Tendsto (infraredPartialSum omega) atTop (nhds (H omega)) ∧
            (∀ N, ∃ D :
                SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum
                  (SpatialCoordinates d),
              (∀ mu, DenseRange (D.operator mu)) ∧
              SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
                (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) D ∧
              ∀ (mu : Semigroup.PositiveShift)
                (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ)
                (x : SpatialCoordinates d),
                D.solution mu f x =
                  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
                    kernelIntegral (PN N omega (Real.toNNReal t)) f x) ∧
            (∀ N I x,
              (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
                SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x) ∧
            (∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
              SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x) ∧
            HasStrongMarkovRestart K omega) ∧
          -- (i) Annealed convergence of the physical rescaled process.
          (∀ (x : SpatialCoordinates d) (F : BoundedContinuousFunction (DiffusionPath d) ℝ),
            Tendsto
              (fun N ↦ ∫ omega,
                (∫ path, F (physicalRescaledPath M N path)
                  ∂(KN 0 (omega, (3 : ℝ) ^ N • x))) ∂law)
              atTop
              (nhds (∫ omega, (∫ path, F path ∂(K (omega, x))) ∂law))) ∧
          -- (ii), (iv) The same reversible singular measure governs the marginals.
          (∃ Mlim : BilateralField d → Measure (SpatialCoordinates d), Measurable Mlim ∧
            ∀ᵐ omega ∂law,
              let mu := (Mlim omega).withDensity
                (fun y ↦ ENNReal.ofReal (Real.exp (H omega y)))
              MeasuresConvergeLocally (fun N ↦ chaosCutoff M N omega) (Mlim omega) ∧
              MeasuresConvergeLocally (fun N ↦ cutoffSpeedMeasure M H omega N) mu ∧
              IsLocallyFiniteMeasure (Mlim omega) ∧ IsLocallyFiniteMeasure mu ∧
              SemigroupSymmetric (P omega) mu ∧ mu ⟂ₘ volume ∧
              ∀ (x : SpatialCoordinates d) (t : ℝ≥0), 0 < t →
                (K (omega, x)).map (fun w : DiffusionPath d ↦ w t) ≪ mu ∧
                ¬ IsGaussian ((K (omega, x)).map (fun w : DiffusionPath d ↦ w t))) ∧
          -- (iii) Exit times for every side length in (0,1].
          (∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
            ∫⁻ omega, (∫⁻ w, ContinuousPath.exitTime
                (Metric.ball (w 0) (r / 2)) w ∂(K (omega, x))) ∂law ≤
              ENNReal.ofReal (C * r ^ (2 + eta))) ∧
          ∀ x : SpatialCoordinates d, ∀ᵐ omega ∂law,
            ∀ᵐ w ∂(K (omega, x)), ∀ gamma : ℝ, 1 / (2 + eta) < gamma →
              Filter.limsup
                (fun t : ℝ≥0 ↦ ENNReal.ofReal
                  ((t : ℝ) ^ (-gamma) * ‖w t - w 0‖)) (𝓝[>] 0) = ∞ := by
  exact t_A_short d hd

end Paper
end

noncomputable section

open Filter MeasureTheory ProbabilityTheory Topology Asymptotics
open MarkovProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false


namespace Paper

/-- **Scaling limit (precise form, `t.scaling.limit`).** -/
theorem _root_.SubdiffusiveProcess.process_convergence_precise
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        0 < M.delta → M.delta ≤ delta0 →
        let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ)) :=
          ⟨fun g ↦ g.1.1, continuous_subtype_val.fst⟩
        let nu := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).map
          forget
        let law := (commonScaleLaw d nu).toMeasure
        ∃ C eta : ℝ, 1 ≤ C ∧ 0 < eta ∧
        (d = 2 → eta = SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P / Real.log 3) ∧
        (∀ l m : ℕ, l ≤ m →
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M m / SubdiffusiveProcess.CoarseGrainingVocab.ahom M l ≤
            C * (3 : ℝ) ^ (-(eta * ((m : ℝ) - (l : ℝ))))) ∧
        ∃ H : BilateralField d → C(SpatialCoordinates d, ℝ), Measurable H ∧
        ∃ PN : ℕ → BilateralField d →
            SubMarkovKernelSemigroup (SpatialCoordinates d),
        ∃ hPN : ∀ N omega, (PN N omega).IsConservative,
        ∃ P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d),
        ∃ hP : ∀ omega, (P omega).IsConservative,
        ∃ KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d),
        ∃ hKN : ∀ N, IsMarkovKernel (KN N),
        ∃ K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d),
        ∃ hK : IsMarkovKernel K,
          (∀ omega : BilateralField d,
            Continuous (fun x ↦ jointPathProbabilityMeasure K hK omega x)) ∧
          (∀ᵐ omega ∂law,
            Tendsto (infraredPartialSum omega) atTop (nhds (H omega)) ∧
            (∀ N, ∃ D :
                SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum
                  (SpatialCoordinates d),
              (∀ mu, DenseRange (D.operator mu)) ∧
              SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
                (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) D ∧
              ∀ (mu : Semigroup.PositiveShift)
                (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ)
                (x : SpatialCoordinates d),
                D.solution mu f x =
                  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
                    kernelIntegral (PN N omega (Real.toNNReal t)) f x) ∧
            (∀ N I x,
              (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
                SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x) ∧
            (∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
              SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x) ∧
            Continuous (fun x ↦ jointPathProbabilityMeasure K hK omega x) ∧
            (∀ B : Set (SpatialCoordinates d), IsCompact B →
              ∀ epsilon : ℝ, 0 < epsilon → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
                ∀ x ∈ B,
                  pathLevyProkhorovDist
                    (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                    (jointPathProbabilityMeasure K hK omega x) < epsilon) ∧
            (∀ (t : ℝ≥0) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ),
              Continuous (kernelIntegral (P omega t) f)) ∧
            (∃ mu : Measure (SpatialCoordinates d),
              MeasuresConvergeLocally (fun N ↦ cutoffSpeedMeasure M H omega N) mu ∧
              IsLocallyFiniteMeasure mu ∧ NoAtoms mu ∧ mu.IsOpenPosMeasure ∧
              SemigroupSymmetric (P omega) mu) ∧
            HasStrongMarkovRestart K omega ∧ HasFiniteMeanExits K omega) ∧
          (∀ (x : SpatialCoordinates d) (F : BoundedContinuousFunction (DiffusionPath d) ℝ),
            Tendsto
              (fun N ↦ ∫ omega,
                (∫ path, F (physicalRescaledPath M N path)
                  ∂(KN 0 (omega, (3 : ℝ) ^ N • x))) ∂law)
              atTop
              (nhds (∫ omega, (∫ path, F path ∂(K (omega, x))) ∂law))) ∧
          -- (ii) the limiting measures `M = lim M_N` and `μ = e^H M`, reversibility's invariance
          (∃ Mlim : BilateralField d → Measure (SpatialCoordinates d), Measurable Mlim ∧
            (∀ᵐ omega ∂law,
              let mu := (Mlim omega).withDensity
                (fun y ↦ ENNReal.ofReal (Real.exp (H omega y)))
              MeasuresConvergeLocally (fun N ↦ chaosCutoff M N omega) (Mlim omega) ∧
              MeasuresConvergeLocally (fun N ↦ cutoffSpeedMeasure M H omega N) mu ∧
              IsLocallyFiniteMeasure (Mlim omega) ∧ NoAtoms (Mlim omega) ∧
              (Mlim omega).IsOpenPosMeasure ∧ Mlim omega ⟂ₘ volume ∧
              IsLocallyFiniteMeasure mu ∧ NoAtoms mu ∧ mu.IsOpenPosMeasure ∧ mu ⟂ₘ volume ∧
              (∀ (t : ℝ≥0) (f : SpatialCoordinates d → ℝ≥0∞), Measurable f →
                ∫⁻ x, (∫⁻ w, f (w t) ∂(K (omega, x))) ∂mu = ∫⁻ x, f x ∂mu) ∧
              -- (iv) positive-time transition laws: absolutely continuous, non-Gaussian
              ∀ (x : SpatialCoordinates d) (t : ℝ≥0), 0 < t →
                (K (omega, x)).map (fun w : DiffusionPath d ↦ w t) ≪ mu ∧
                ¬ IsGaussian ((K (omega, x)).map (fun w : DiffusionPath d ↦ w t))) ∧
            (¬ ∃ m : Measure (SpatialCoordinates d), ∀ᵐ omega ∂law, Mlim omega = m) ∧
            (∀ A : Set (SpatialCoordinates d), MeasurableSet A →
              ∫⁻ omega, Mlim omega A ∂law = volume A) ∧
            ∀ y : SpatialCoordinates d,
              law.map (fun omega ↦ (Mlim omega).map (fun z ↦ z + y)) = law.map Mlim) ∧
          -- (iii) annealed small-cube exits, Brownian singularity, pointwise Hölder bound
          (∀ (x : SpatialCoordinates d) (k : ℕ),
            ∫⁻ omega, (∫⁻ w, ContinuousPath.exitTime
                (Metric.ball (w 0) ((3 : ℝ) ^ (-(k : ℤ)) / 2)) w ∂(K (omega, x))) ∂law ≤
              ENNReal.ofReal (C * (3 : ℝ) ^ (-((2 + eta) * (k : ℝ))))) ∧
          ∀ x : SpatialCoordinates d, ∀ᵐ omega ∂law,
            (∀ Q : Measure (DiffusionPath d), lim_brownian_law Q → K (omega, x) ⟂ₘ Q) ∧
            (∀ (Θ : Type) [MeasurableSpace Θ] (nu' : Measure Θ) [IsProbabilityMeasure nu']
                (kappa : Kernel Θ (DiffusionPath d)), (∀ θ, lim_brownian_law (kappa θ)) →
              K (omega, x) ⟂ₘ nu'.bind kappa) ∧
            ∀ᵐ w ∂(K (omega, x)), ∀ gamma : ℝ, 0 ≤ gamma →
              (fun t : ℝ≥0 ↦ ‖w t - w 0‖) =O[𝓝[>] 0] (fun t : ℝ≥0 ↦ (t : ℝ) ^ gamma) →
              gamma ≤ 1 / (2 + eta) := by
  exact t_A d hd

end Paper
end

noncomputable section



open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false


namespace Paper

/-- **Theorem B (quantitative homogenization of the Dirichlet problem).** -/
theorem _root_.SubdiffusiveProcess.quantitative_homogenization (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    (∀ vartheta q : ℝ, vartheta ∈ Set.Ioo (0 : ℝ) 1 → 1 ≤ q →
           ∃ delta0 C : ℝ, 0 < delta0 ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
             (M.delta ≤ delta0 →
             ∃ Z : ℕ → ℕ → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ,
               (∀ L N, L ≤ N →
                 CoefficientMeasurable
                   (fun omega ↦ rescaledCutoffCoefficient M L N omega) (Z L N)) ∧
               (∀ L N omega, L ≤ N → 1 ≤ Z L N omega) ∧
               (∀ L N, L ≤ N →
                 eLpNorm (Z L N) (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal C) ∧
               ∀ᵐ omega ∂M.P.toMeasure, ∀ L N : ℕ, L ≤ N →
                 ∀ (f : Vec d → ℝ),
                   MemLp f 2 (volume.restrict (openCubeSet (originCube d 0))) →
                 ∀ h : H2Datum (originCube d 0),
                   (∃ uLM : H1Function (openCubeSet (originCube d 0)),
                     IsScalarDirichletSolutionOn
                       (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                       (originCube d 0) uLM h.toH1 f) ∧
                   (∀ uLM uLM' : H1Function (openCubeSet (originCube d 0)),
                     IsScalarDirichletSolutionOn
                         (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                         (originCube d 0) uLM h.toH1 f →
                     IsScalarDirichletSolutionOn
                         (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                         (originCube d 0) uLM' h.toH1 f →
                     uLM.toFun =ᵐ[volume.restrict (openCubeSet (originCube d 0))] uLM'.toFun ∧
                       uLM.grad =ᵐ[volume.restrict (openCubeSet (originCube d 0))] uLM'.grad) ∧
                   (∃ uHom : H1Function (openCubeSet (originCube d 0)),
                     IsScalarDirichletSolutionOn (fun _ ↦ 1)
                       (originCube d 0) uHom h.toH1 f) ∧
                   (∀ uHom uHom' : H1Function (openCubeSet (originCube d 0)),
                     IsScalarDirichletSolutionOn (fun _ ↦ 1)
                         (originCube d 0) uHom h.toH1 f →
                     IsScalarDirichletSolutionOn (fun _ ↦ 1)
                         (originCube d 0) uHom' h.toH1 f →
                     uHom.toFun =ᵐ[volume.restrict (openCubeSet (originCube d 0))] uHom'.toFun ∧
                       uHom.grad =ᵐ[volume.restrict (openCubeSet (originCube d 0))] uHom'.grad) ∧
                   ∀ (uLM uHom : H1Function (openCubeSet (originCube d 0))),
                     IsScalarDirichletSolutionOn
                         (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                         (originCube d 0) uLM h.toH1 f →
                     IsScalarDirichletSolutionOn (fun _ ↦ 1)
                         (originCube d 0) uHom h.toH1 f →
                     ∃ gradDifference fluxDifference : L2VectorField (originCube d 0),
                       (∀ x, gradDifference.toFun x = uLM.grad x - uHom.grad x) ∧
                       (∀ x, fluxDifference.toFun x =
                         rescaledCutoffCoefficient M L N omega x • uLM.grad x - uHom.grad x) ∧
                       l2Size (originCube d 0) (fun x ↦ uLM.toFun x - uHom.toFun x) +
                             ordinaryVectorHMinusOne (originCube d 0) gradDifference +
                           ordinaryVectorHMinusOne (originCube d 0) fluxDifference ≤
                         ENNReal.ofReal (Z L N omega * M.delta ^ vartheta) *
                           (l2Size (originCube d 0) f + h.norm) ∧
                         (f = 0 →
                         l2Size (originCube d 0) (fun x ↦ uLM.toFun x - uHom.toFun x) +
                               ordinaryVectorHMinusOne (originCube d 0) gradDifference +
                             ordinaryVectorHMinusOne (originCube d 0) fluxDifference ≤
                           ENNReal.ofReal (Z L N omega * C * M.delta) * h.norm))) ∧
    (∃ alphaHom : ℝ, 0 < alphaHom ∧
           ∀ L : ℕ, ∀ q : ℝ, 1 ≤ q → ∀ delta : ℝ,
             ∃ C : ℝ, 0 < C ∧
               ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta = delta →
               ∃ Y : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ,
               CoefficientMeasurable (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L) Y ∧
                 (∀ omega, 1 ≤ Y omega) ∧
                 eLpNorm Y (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal C ∧
                 ∀ᵐ omega ∂M.P.toMeasure, ∀ N : ℕ, L ≤ N →
                   ∀ (f : Vec d → ℝ),
                     MemLp f 2 (volume.restrict (openCubeSet (originCube d 0))) →
                   ∀ h : H2Datum (originCube d 0),
                     (∃ uLM : H1Function (openCubeSet (originCube d 0)),
                       IsScalarDirichletSolutionOn
                         (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                         (originCube d 0) uLM h.toH1 f) ∧
                     (∀ uLM uLM' : H1Function (openCubeSet (originCube d 0)),
                       IsScalarDirichletSolutionOn
                           (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                           (originCube d 0) uLM h.toH1 f →
                       IsScalarDirichletSolutionOn
                           (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                           (originCube d 0) uLM' h.toH1 f →
                       uLM.toFun =ᵐ[volume.restrict (openCubeSet (originCube d 0))] uLM'.toFun ∧
                         uLM.grad =ᵐ[volume.restrict (openCubeSet (originCube d 0))] uLM'.grad) ∧
                     (∃ uHom : H1Function (openCubeSet (originCube d 0)),
                       IsScalarDirichletSolutionOn (fun _ ↦ 1)
                         (originCube d 0) uHom h.toH1 f) ∧
                     (∀ uHom uHom' : H1Function (openCubeSet (originCube d 0)),
                       IsScalarDirichletSolutionOn (fun _ ↦ 1)
                           (originCube d 0) uHom h.toH1 f →
                       IsScalarDirichletSolutionOn (fun _ ↦ 1)
                           (originCube d 0) uHom' h.toH1 f →
                       uHom.toFun =ᵐ[volume.restrict (openCubeSet (originCube d 0))] uHom'.toFun ∧
                         uHom.grad =ᵐ[volume.restrict (openCubeSet (originCube d 0))] uHom'.grad) ∧
                     ∀ (uLM uHom : H1Function (openCubeSet (originCube d 0))),
                       IsScalarDirichletSolutionOn
                           (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                           (originCube d 0) uLM h.toH1 f →
                       IsScalarDirichletSolutionOn (fun _ ↦ 1)
                           (originCube d 0) uHom h.toH1 f →
                       ∃ gradDifference fluxDifference : L2VectorField (originCube d 0),
                         (∀ x, gradDifference.toFun x = uLM.grad x - uHom.grad x) ∧
                         (∀ x, fluxDifference.toFun x =
                           rescaledCutoffCoefficient M L N omega x • uLM.grad x - uHom.grad x) ∧
                         l2Size (originCube d 0) (fun x ↦ uLM.toFun x - uHom.toFun x) +
                               ordinaryVectorHMinusOne (originCube d 0) gradDifference +
                             ordinaryVectorHMinusOne (originCube d 0) fluxDifference ≤
                           ENNReal.ofReal
                               (Y omega * (3 : ℝ) ^ (-alphaHom * ((N : ℝ) - (L : ℝ)))) *
                             (l2Size (originCube d 0) f + h.norm)) := by
  exact t_B d hd

end Paper
end

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter SubdiffusiveProcess SubdiffusiveProcess.Frozen.Assumptions MeasureTheory ProbabilityTheory
open Homogenization hiding Vec
open Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
open scoped ENNReal NNReal Topology


namespace Paper

/-- **Theorem C (anomalous Hölder regularity).** -/
theorem _root_.SubdiffusiveProcess.anomalous_holder_regularity (d : ℕ) (hd : 2 ≤ d) :
    ∃ delta0 C0 C : ℝ, 0 < delta0 ∧ 0 < C0 ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
        let mu := (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
          (measure_anchoredC11GoodSet_eq_one M)).toMeasure
        gammaReg C0 M.delta ∈ Set.Ioo (1 / 2 : ℝ) 1 ∧
        ∀ gamma ∈ Set.Icc (1 / 2 : ℝ) (gammaReg C0 M.delta),
          ∃ Lscale : WithTop ℕ → ℕ → AnchoredC11Sample d → ℕ,
            (∀ (L : WithTop ℕ) (m : ℕ), Measurable (Lscale L m)) ∧
            (∀ (L : WithTop ℕ) (m k : ℕ), 0 < k →
              mu {omega | k < Lscale L m omega} ≤
                ENNReal.ofReal (C * Real.exp (
                  -((1 - gamma) ^ 2 * max ((k : ℝ) - C) 0) /
                    (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ᵐ omega ∂mu,
              (∀ (L : WithTop ℕ) (m : ℕ), 0 < m →
                ∀ u : H1Function (openCubeSet (originCube d m)),
                  IsWeaklyHarmonicOn (coefficientAt M L omega) (cube d m) u →
                  ∀ n : ℕ, (n : ℤ) ≤ (m : ℤ) - (Lscale L m omega : ℤ) →
                    ∀ z : Vec d, OnTriadicGrid n z →
                    translatedCube d n z ⊆ cube d (m - 1) →
                      normalizedL2On (translatedCube d n z)
                          (fun x => u.toFun x - averageOn (translatedCube d n z) u.toFun) ≤
                        C * (3 : ℝ) ^ (-gamma * ((m : ℝ) - (n : ℝ))) *
                          normalizedL2On (cube d m)
                            (fun x => u.toFun x - averageOn (cube d m) u.toFun) ∧
                      vectorNormalizedL2On (translatedCube d n z)
                          (fun x => Real.sqrt (coefficientAt M L omega x) • u.grad x) ≤
                        C * (3 : ℝ) ^ ((1 - gamma) * ((m : ℝ) - (n : ℝ))) *
                          vectorNormalizedL2On (cube d m)
                            (fun x => Real.sqrt (coefficientAt M L omega x) • u.grad x)) ∧
              (∀ (L : WithTop ℕ) (u : Vec d → ℝ),
                (∀ m : ℤ, ∃ um : H1Function (openCubeSet (originCube d m)),
                  (∀ x, um.toFun x = u x) ∧
                    IsWeaklyHarmonicOn (coefficientAt M L omega) (cube d m) um) →
                (∀ eps > 0, ∃ᶠ R : ℝ in atTop, R ^ (-gammaReg C0 M.delta) *
                    sInf {r : ℝ | ∃ c : ℝ,
                      r = normalizedL2On (Metric.ball (0 : Vec d) R) (fun x => u x - c)} < eps) →
                ∃ uRep : Vec d → ℝ,
                  Continuous uRep ∧ uRep =ᵐ[volume] u ∧
                  (∀ m : ℤ, ∀ um : H1Function (openCubeSet (originCube d m)),
                    (∀ x, um.toFun x = u x) →
                    IsWeaklyHarmonicOn (coefficientAt M L omega) (cube d m) um →
                    uRep =ᵐ[volume.restrict (openCubeSet (originCube d m))] um.toFun) ∧
                  ∃ c : ℝ, ∀ x, uRep x = c) := by
  exact t_C d hd

end Paper
end
