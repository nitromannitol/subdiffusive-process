import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCanonicalCorrectors
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepHarmonicCellEstimate
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNeumannInteriorEquation
import Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.OneCube




open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- A zero-Dirichlet divergence solution solves the corresponding scalar
Poisson equation with right-hand side equal to the weak divergence. -/
theorem weakPoissonEquationOn_of_cubeDirichletDivergenceProblem
    {d : ℕ} (Q : TriadicCube d) (G : CubeVectorH1Function Q)
    (u : H10Function (openCubeSet Q))
    (hu : CubeDirichletDivergenceProblem Q u G.toField) :
    WeakPoissonEquationOn (openCubeSet Q) u.toH1Function G.divergence := by
  intro phi hphi hphiSupport hphiSub
  let phi0 : H10Function (openCubeSet Q) :=
    H10Function.ofContDiff (isOpen_openCubeSet Q)
      (hphi.of_le (by simp)) hphiSupport hphiSub
  have hweak := hu phi0
  have hparts := G.integral_divergence_mul_zeroTrace_eq_neg_integral_vecDot phi0
  have hleft :
      ∫ x in openCubeSet Q,
          vecDot (u.toH1Function.grad x) (euclideanGradient phi x) ∂volume =
        ∫ x in openCubeSet Q,
          vecDot (u.toH1Function.grad x) (phi0.toH1Function.grad x) ∂volume := by
    apply integral_congr_ae
    filter_upwards with x
    congr 1
  have hright :
      ∫ x in openCubeSet Q, G.divergence x * phi x ∂volume =
        ∫ x in openCubeSet Q,
          G.divergence x * phi0.toH1Function x ∂volume := by
    apply integral_congr_ae
    filter_upwards with x
    rfl
  calc
    ∫ x in openCubeSet Q,
        vecDot (u.toH1Function.grad x) (euclideanGradient phi x) ∂volume =
      ∫ x in openCubeSet Q,
        vecDot (u.toH1Function.grad x) (phi0.toH1Function.grad x) ∂volume := hleft
    _ = -∫ x in openCubeSet Q,
        vecDot (G.toField x) (phi0.toH1Function.grad x) ∂volume := hweak
    _ = ∫ x in openCubeSet Q,
        G.divergence x * phi0.toH1Function x ∂volume := hparts.symm
    _ = ∫ x in openCubeSet Q, G.divergence x * phi x ∂volume := hright.symm

/-- Subtracting two weak Poisson solutions with the same right-hand side
produces a weakly harmonic `H¹` function. -/
theorem WeakPoissonEquationOn.sub_same_rhs
    {d : ℕ} {U : Set (Vec d)} {u v : H1Function U} {f : Vec d → ℝ}
    (hU : IsOpen U)
    (hu : WeakPoissonEquationOn U u f)
    (hv : WeakPoissonEquationOn U v f) :
    WeakPoissonEquationOn U (u - v) (fun _ ↦ 0) := by
  intro phi hphi hphiSupport hphiSub
  have hu' := hu phi hphi hphiSupport hphiSub
  have hv' := hv phi hphi hphiSupport hphiSub
  let phi0 : H10Function U :=
    H10Function.ofContDiff hU (hphi.of_le (by simp)) hphiSupport hphiSub
  have huInt : IntegrableOn
      (fun x ↦ vecDot (u.grad x) (euclideanGradient phi x)) U := by
    simpa only [phi0, H10Function.ofContDiff, H1Function.ofContDiff] using
      integrableOn_vecDot_of_memVectorL2 u.grad_memVectorL2
        phi0.toH1Function.grad_memVectorL2
  have hvInt : IntegrableOn
      (fun x ↦ vecDot (v.grad x) (euclideanGradient phi x)) U := by
    simpa only [phi0, H10Function.ofContDiff, H1Function.ofContDiff] using
      integrableOn_vecDot_of_memVectorL2 v.grad_memVectorL2
        phi0.toH1Function.grad_memVectorL2
  have hleft :
      ∫ x in U, vecDot ((u - v).grad x) (euclideanGradient phi x) ∂volume =
        ∫ x in U, vecDot (u.grad x) (euclideanGradient phi x) ∂volume -
          ∫ x in U, vecDot (v.grad x) (euclideanGradient phi x) ∂volume := by
    rw [← integral_sub huInt hvInt]
    apply integral_congr_ae
    filter_upwards with x
    simp only [H1Function.sub_grad, vecDot]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    change (u.grad x i - v.grad x i) * euclideanGradient phi x i = _
    ring
  rw [hleft, hu', hv']
  simp

/-- The literal Neumann corrector minus the zero-Dirichlet corrector with the
same shell datum is harmonic on the whole cube. -/
theorem oneStepShell_neumann_sub_dirichlet_harmonic
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h)
    (uN : H1MeanZeroFunction (openCubeSet Q))
    (huN : IsMeanZeroNeumannRhsWeakSolution
      (identityCoeffField d) (openCubeSet Q) uN
      (fun x ↦ -(oneStepShellForcingH1 M n h omega p Q hh).toField x))
    (uD : H10Function (openCubeSet Q))
    (huD : CubeDirichletDivergenceProblem Q uD
      (oneStepShellForcingH1 M n h omega p Q hh).toField) :
    WeakPoissonEquationOn (openCubeSet Q)
      (uN.toH1Function - uD.toH1Function) (fun _ ↦ 0) := by
  exact WeakPoissonEquationOn.sub_same_rhs (isOpen_openCubeSet Q)
    (weakPoissonEquationOn_oneStepShellNeumann
      M n h omega p Q hh uN huN)
    (weakPoissonEquationOn_of_cubeDirichletDivergenceProblem Q
      (oneStepShellForcingH1 M n h omega p Q hh) uD huD)

/-- Fixed-radius, high-exponent Hessian package for the harmonic remainder in
the Neumann/Dirichlet decomposition.  The depth and constant depend only on
the dimension, and the parent-gradient term is the literal difference of the
two correctors. -/
theorem exists_oneStepShell_neumannDirichlet_harmonicHessian_highExponent
    (d : ℕ) (hd : 3 ≤ d) :
    ∃ depth : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (p : Vec d)
        (Q : TriadicCube d) (hh : 0 < h)
        (uN : H1MeanZeroFunction (openCubeSet Q))
        (_huN : IsMeanZeroNeumannRhsWeakSolution
          (identityCoeffField d) (openCubeSet Q) uN
          (fun x ↦ -(oneStepShellForcingH1 M n h omega p Q hh).toField x))
        (uD : H10Function (openCubeSet Q))
        (_huD : CubeDirichletDivergenceProblem Q uD
          (oneStepShellForcingH1 M n h omega p Q hh).toField),
        ∃ uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)),
          uS.toFun = (uN.toH1Function - uD.toH1Function).toFun ∧
          uS.grad = (uN.toH1Function - uD.toH1Function).grad ∧
          ∃ H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS,
            ∀ i j : Fin d,
              MemLp (fun x ↦ H.hess i j x)
                (oneStepHarmonicExponent d hd).exponent
                (normalizedCubeMeasure
                  (CubeCalderonZygmund.centralDescendant
                    (CubeCalderonZygmund.centralChild Q) depth)) ∧
              cubeLpNorm
                  (CubeCalderonZygmund.centralDescendant
                    (CubeCalderonZygmund.centralChild Q) depth)
                  (oneStepHarmonicExponent d hd).exponent
                  (fun x ↦ H.hess i j x) ≤
                C * (cubeScaleFactor Q)⁻¹ *
                  ∑ k : Fin d, cubeLpNorm Q 2
                    (fun x ↦ (uN.toH1Function - uD.toH1Function).grad x k) := by
  obtain ⟨depth, C, hC, hreg⟩ :=
    exists_harmonic_fixedInterior_hessian_highExponent_bound d hd
  refine ⟨depth, C, hC, ?_⟩
  intro M n h omega p Q hh uN huN uD huD
  exact hreg Q (uN.toH1Function - uD.toH1Function)
    (oneStepShell_neumann_sub_dirichlet_harmonic
      M n h omega p Q hh uN huN uD huD)



theorem oneStepCellGradientOscillation_le_add_of_grad_eq
    {d : ℕ} (R : TriadicCube d)
    (u v w : H1Function (openCubeSet R))
    (hgrad : u.grad = fun x => v.grad x + w.grad x) :
    oneStepCellGradientOscillation R u ≤
      oneStepCellGradientOscillation R v +
        oneStepCellGradientOscillation R w := by
  have hcoord : ∀ i : Fin d,
      cubeBesovOscillation R 2 (fun x => u.grad x i) ≤
        cubeBesovOscillation R 2 (fun x => v.grad x i) +
          cubeBesovOscillation R 2 (fun x => w.grad x i) := by
    intro i
    have hv : MemLp (fun x => v.grad x i) 2 (normalizedCubeMeasure R) :=
      v.grad_memL2_normalizedCubeMeasure i
    have hw : MemLp (fun x => w.grad x i) 2 (normalizedCubeMeasure R) :=
      w.grad_memL2_normalizedCubeMeasure i
    have hvInt : Integrable (fun x => v.grad x i) (normalizedCubeMeasure R) :=
      hv.integrable (by norm_num)
    have hwInt : Integrable (fun x => w.grad x i) (normalizedCubeMeasure R) :=
      hw.integrable (by norm_num)
    have havg : cubeAverage R (fun x => v.grad x i + w.grad x i) =
        cubeAverage R (fun x => v.grad x i) + cubeAverage R (fun x => w.grad x i) := by
      simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
      exact integral_add hvInt hwInt
    have hfluct : cubeFluctuation R (fun x => u.grad x i) =
        fun x => cubeFluctuation R (fun y => v.grad y i) x +
          cubeFluctuation R (fun y => w.grad y i) x := by
      have hfun : (fun x => u.grad x i) =
          fun x => v.grad x i + w.grad x i := by
        funext x
        exact congrArg (fun z : Vec d => z i) (congrFun hgrad x)
      funext x
      rw [hfun]
      simp only [cubeFluctuation, havg]
      ring
    unfold cubeBesovOscillation
    rw [hfluct]
    exact cubeLpNorm_add_le R 2
      (cubeFluctuation R fun y => v.grad y i)
      (cubeFluctuation R fun y => w.grad y i)
      (by simpa [cubeFluctuation] using
        hv.sub (memLp_const (cubeAverage R fun y => v.grad y i)))
      (by simpa [cubeFluctuation] using
        hw.sub (memLp_const (cubeAverage R fun y => w.grad y i)))
      (by norm_num)
  unfold oneStepCellGradientOscillation
  calc
    ∑ i : Fin d, cubeBesovOscillation R 2 (fun x => u.grad x i) ≤
        ∑ i : Fin d,
          (cubeBesovOscillation R 2 (fun x => v.grad x i) +
            cubeBesovOscillation R 2 (fun x => w.grad x i)) :=
      Finset.sum_le_sum fun i _ => hcoord i
    _ = (∑ i : Fin d, cubeBesovOscillation R 2 (fun x => v.grad x i)) +
        ∑ i : Fin d, cubeBesovOscillation R 2 (fun x => w.grad x i) := by
      rw [Finset.sum_add_distrib]

/-- Fixed-radius Neumann cell reduction.  On the canonical interior central
cell, the Neumann gradient oscillation is bounded by the Dirichlet oscillation
plus the high-exponent harmonic-remainder estimate.  Unlike a direct global
Neumann `W^{2,4}` assertion, every term here is supplied by an existing
coercive or harmonic theorem. -/
theorem exists_oneStepShell_neumann_cellOscillation_reduction
    (d : ℕ) (hd : 3 ≤ d) :
    ∃ depth : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (p : Vec d)
        (Q : TriadicCube d) (hh : 0 < h)
        (uN : H1MeanZeroFunction (openCubeSet Q))
        (_huN : IsMeanZeroNeumannRhsWeakSolution
          (identityCoeffField d) (openCubeSet Q) uN
          (fun x ↦ -(oneStepShellForcingH1 M n h omega p Q hh).toField x))
        (uD : H10Function (openCubeSet Q))
        (_huD : CubeDirichletDivergenceProblem Q uD
          (oneStepShellForcingH1 M n h omega p Q hh).toField)
        (cellDepth : ℕ),
        let D := CubeCalderonZygmund.centralDescendant
          (CubeCalderonZygmund.centralChild Q) depth
        let R := CubeCalderonZygmund.centralDescendant D cellDepth
        let hRQ : openCubeSet R ⊆ openCubeSet Q :=
          (CubeCalderonZygmund.centralDescendant_openCubeSet_subset D cellDepth).trans
            ((CubeCalderonZygmund.centralDescendant_openCubeSet_subset
              (CubeCalderonZygmund.centralChild Q) depth).trans
              (CubeCalderonZygmund.centralDescendant_openCubeSet_subset Q 1))
        oneStepCellGradientOscillation R
            (uN.toH1Function.restrict (isOpen_openCubeSet R) hRQ) ≤
          oneStepCellGradientOscillation R
              (uD.toH1Function.restrict (isOpen_openCubeSet R) hRQ) +
            (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
              cubeScaleFactor R *
                ((d : ℝ) ^ 2 *
                  ((((3 ^ d) ^ cellDepth : ℕ) : ℝ) ^
                    (1 / (oneStepHarmonicExponent d hd).exponent).toReal) *
                  (C * (cubeScaleFactor Q)⁻¹ *
                    ∑ k : Fin d, cubeLpNorm Q 2
                      (fun x =>
                        (uN.toH1Function - uD.toH1Function).grad x k))) := by
  obtain ⟨depth, C, hC, hreg⟩ :=
    exists_oneStepShell_neumannDirichlet_harmonicHessian_highExponent d hd
  refine ⟨depth, C, hC, ?_⟩
  intro M n h omega p Q hh uN huN uD huD cellDepth
  obtain ⟨uS, huSfun, huSgrad, H, hH⟩ :=
    hreg M n h omega p Q hh uN huN uD huD
  let D := CubeCalderonZygmund.centralDescendant
    (CubeCalderonZygmund.centralChild Q) depth
  let R := CubeCalderonZygmund.centralDescendant D cellDepth
  have hDhalf : openCubeSet D ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ) := by
    intro x hx
    exact CubeCalderonZygmund.centralChild_cubeSet_subset_scaledOpenInnerHalf Q
      (CubeCalderonZygmund.centralDescendant_cubeSet_subset
        (CubeCalderonZygmund.centralChild Q) depth
        (by exact openCubeSet_subset_cubeSet D hx))
  have hRD : openCubeSet R ⊆ openCubeSet D :=
    CubeCalderonZygmund.centralDescendant_openCubeSet_subset D cellDepth
  have hDQ : openCubeSet D ⊆ openCubeSet Q :=
    (CubeCalderonZygmund.centralDescendant_openCubeSet_subset
      (CubeCalderonZygmund.centralChild Q) depth).trans
      (CubeCalderonZygmund.centralDescendant_openCubeSet_subset Q 1)
  have hRQ : openCubeSet R ⊆ openCubeSet Q := hRD.trans hDQ
  let uH : H1Function (openCubeSet D) :=
    uS.restrict (isOpen_openCubeSet D) hDhalf
  let HD : HasWeakHessianOn (openCubeSet D) uH :=
    H.restrict (isOpen_openCubeSet D) hDhalf
  have hmem : ∀ i j : Fin d,
      MemLp (fun x => HD.hess i j x)
        (oneStepHarmonicExponent d hd).exponent
        (normalizedCubeMeasure D) := by
    intro i j
    simpa only [D, HD, HasWeakHessianOn.restrict] using (hH i j).1
  have hbound : ∀ i j : Fin d,
      cubeLpNorm D (oneStepHarmonicExponent d hd).exponent
          (fun x => HD.hess i j x) ≤
        C * (cubeScaleFactor Q)⁻¹ *
          ∑ k : Fin d, cubeLpNorm Q 2
            (fun x => (uN.toH1Function - uD.toH1Function).grad x k) := by
    intro i j
    simpa only [D, HD, HasWeakHessianOn.restrict] using (hH i j).2
  have hharm := harmonic_cellGradientOscillation_le_highExponent
    hd D cellDepth uH HD
      (C * (cubeScaleFactor Q)⁻¹ *
        ∑ k : Fin d, cubeLpNorm Q 2
          (fun x => (uN.toH1Function - uD.toH1Function).grad x k))
      hmem hbound
  let uNR : H1Function (openCubeSet R) :=
    uN.toH1Function.restrict (isOpen_openCubeSet R) hRQ
  let uDR : H1Function (openCubeSet R) :=
    uD.toH1Function.restrict (isOpen_openCubeSet R) hRQ
  let uHR : H1Function (openCubeSet R) :=
    uH.restrict (isOpen_openCubeSet R) hRD
  have hgrad : uNR.grad = fun x => uDR.grad x + uHR.grad x := by
    funext x
    dsimp only [uNR, uDR, uHR, uH, H1Function.restrict]
    rw [huSgrad]
    simp only [H1Function.sub_grad]
    apply funext
    intro i
    change uN.toH1Function.grad x i =
      uD.toH1Function.grad x i +
        (uN.toH1Function.grad x i - uD.toH1Function.grad x i)
    ring
  have htri := oneStepCellGradientOscillation_le_add_of_grad_eq
    R uNR uDR uHR hgrad
  dsimp only [D, R] at hharm ⊢
  have hharm' : oneStepCellGradientOscillation R uHR ≤
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
        cubeScaleFactor R *
          ((d : ℝ) ^ 2 *
            ((((3 ^ d) ^ cellDepth : ℕ) : ℝ) ^
              (1 / (oneStepHarmonicExponent d hd).exponent).toReal) *
            (C * (cubeScaleFactor Q)⁻¹ *
              ∑ k : Fin d, cubeLpNorm Q 2
                (fun x =>
                  (uN.toH1Function - uD.toH1Function).grad x k))) := by
    simpa [uHR, uH, H1Function.restrictToOpenSubcube] using hharm
  exact htri.trans (add_le_add le_rfl hharm')

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
