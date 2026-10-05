module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepMultiplierDerivative
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ScalarDivergenceGradientW1p
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.NeumannEndpoint

@[expose] public section

/-!
# Literal `H¹`/`W¹,⁴` packaging of the one-step shell forcing

The manuscript's vector datum `(exp(h)-1) p` is represented simultaneously
on the identical pointwise field in the `H¹` and `W¹,⁴` cube carriers.  This
is the exact paired input required by the finite-exponent scalar-divergence
Calderon--Zygmund theorem.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


/-- The exponent four used by the printed interior `W^{2,4}` estimate. -/
noncomputable def oneStepFourExponent : FiniteLpExponent where
  exponent := 4
  one_lt := by norm_num
  lt_top := by norm_num

@[simp] theorem oneStepFourExponent_exponent :
    oneStepFourExponent.exponent = 4 := rfl

/-- The literal suffix multiplier is continuously differentiable in space. -/
theorem contDiff_one_oneStepMultiplierAt {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    ContDiff ℝ 1 (fun x => oneStepMultiplierAt M n h x omega) := by
  have hn : (-1 : ℤ) ≤ (n : ℤ) := by omega
  have hnm : (n : ℤ) < ((n + h : ℕ) : ℤ) := by
    exact_mod_cast Nat.lt_add_of_pos_right hh
  have hdiff : ((((n + h : ℕ) : ℤ) - (n : ℤ) : ℤ) : ℝ) = h := by
    push_cast
    ring
  have hsum : ContDiff ℝ 1
      (fun x => cutoffShellSum (n + h) (n : ℤ) x omega) := by
    unfold cutoffShellSum
    classical
    induction cutoffShellIndices (n + h) (n : ℤ) using Finset.induction_on with
    | empty => simpa using (contDiff_const : ContDiff ℝ 1 (fun _ : Vec d => (0 : ℝ)))
    | @insert k s hk ih =>
        simpa [Finset.sum_insert hk] using
          (_root_.SubdiffusiveProcess.Model.PotentialField.contDiff_one (omega k)).add ih
  have hcentered : ContDiff ℝ 1 (fun x =>
      cutoffShellSum (n + h) (n : ℤ) x omega -
        (h : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) :=
    hsum.sub contDiff_const
  have hexp : ContDiff ℝ 1 (fun x => Real.exp
      (cutoffShellSum (n + h) (n : ℤ) x omega -
        (h : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1) :=
    hcentered.exp.sub contDiff_const
  have heq : (fun x => oneStepMultiplierAt M n h x omega) =
      fun x => Real.exp
        (cutoffShellSum (n + h) (n : ℤ) x omega -
          (h : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1 := by
    funext x
    rw [oneStepMultiplierAt, cutoffRatioMinusOne_eq_exp_shell
      M (n + h) (n : ℤ) omega x hn hnm, hdiff]
  rw [heq]
  exact hexp

/-- Coordinate function of the literal vector forcing. -/
def oneStepShellForcingCoord {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p : Vec d) (i : Fin d) : Vec d → ℝ :=
  fun x => oneStepMultiplierAt M n h x omega * p i

theorem contDiff_one_oneStepShellForcingCoord {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p : Vec d) (i : Fin d) (hh : 0 < h) :
    ContDiff ℝ 1 (oneStepShellForcingCoord M n h omega p i) := by
  exact (contDiff_one_oneStepMultiplierAt M n h omega hh).mul contDiff_const

/-- `H¹` realization of the literal vector suffix forcing on a cube. -/
noncomputable def oneStepShellForcingH1 {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p : Vec d) (Q : TriadicCube d) (hh : 0 < h) :
    CubeVectorH1Function Q where
  coord i := H1Function.ofContDiffOnIsOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_openCubeSet Q)
    (contDiff_one_oneStepShellForcingCoord M n h omega p i hh)

/-- `W¹,⁴` realization of the same literal vector suffix forcing. -/
noncomputable def oneStepShellForcingW14 {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p : Vec d) (Q : TriadicCube d) (hh : 0 < h) :
    CubeVectorW1pFunction Q oneStepFourExponent where
  coord i := W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_openCubeSet Q)
    (contDiff_one_oneStepShellForcingCoord M n h omega p i hh)

/-- Both Sobolev carriers represent literally the same vector field. -/
theorem oneStepShellForcing_paired_toField {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p : Vec d) (Q : TriadicCube d) (hh : 0 < h) :
    (oneStepShellForcingH1 M n h omega p Q hh).toField =
      (oneStepShellForcingW14 M n h omega p Q hh).toField := by
  funext x i
  rfl

/-- The paired witnesses also store byte-identical weak-gradient
representatives, so the Calderon--Zygmund pairing hypothesis is exact. -/
theorem oneStepShellForcing_paired_jacobian {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p : Vec d) (Q : TriadicCube d) (hh : 0 < h) :
    ∀ (x : Vec d) (i j : Fin d),
      ((oneStepShellForcingH1 M n h omega p Q hh).coord i).grad x j =
        (oneStepShellForcingW14 M n h omega p Q hh).jacobian x i j := by
  intro x i j
  rfl

/-- Pointwise field readout in the manuscript's notation. -/
theorem oneStepShellForcingW14_toField_apply {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p : Vec d) (Q : TriadicCube d) (hh : 0 < h)
    (x : Vec d) :
    (oneStepShellForcingW14 M n h omega p Q hh).toField x =
      oneStepMultiplierAt M n h x omega • p := by
  funext i
  rfl

/-- The literal paired shell forcing can be fed directly to the library's
finite-exponent scalar-divergence Calderon--Zygmund theorem. -/
theorem exists_oneStepShell_scalarDivergence_cz (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (p : Vec d) (m : ℤ) (hh : 0 < h)
        (u : H10Function (openCubeSet (originCube d m))),
        CubeDirichletDivergenceProblem (originCube d m) u
          (oneStepShellForcingH1 M n h omega p (originCube d m) hh).toField →
        ∃ V : CubeVectorW1pFunction (originCube d m) oneStepFourExponent,
          V.toField = u.toH1Function.grad ∧
          eLpNorm (fun x => HilbertMat.ofMat (V.jacobian x)) 4
              (normalizedCubeMeasure (originCube d m)) ≤
            C * eLpNorm (fun x => HilbertMat.ofMat
              ((oneStepShellForcingW14 M n h omega p
                (originCube d m) hh).jacobian x)) 4
              (normalizedCubeMeasure (originCube d m)) := by
  obtain ⟨C, hCtop, hC⟩ :=
    CubeCalderonZygmund.exists_cubeVectorW1p_scalarDivergence_cz_of_paired
      d oneStepFourExponent
  refine ⟨C, hCtop, ?_⟩
  intro M n h omega p m hh u hu
  have h := hC m
    (oneStepShellForcingH1 M n h omega p (originCube d m) hh)
    (oneStepShellForcingW14 M n h omega p (originCube d m) hh)
    (oneStepShellForcing_paired_toField M n h omega p (originCube d m) hh)
    (oneStepShellForcing_paired_jacobian M n h omega p (originCube d m) hh)
    u hu
  simpa only [oneStepFourExponent_exponent] using h

/-- Neumann counterpart of the literal shell specialization.  It is the
finite-`p` input for the manuscript's field `exp(h) q - grad W`; the harmless
constant vector `q` is added after this gradient estimate. -/
theorem exists_oneStepShell_neumannDivergence_cz (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (q : Vec d) (Q : TriadicCube d) (hh : 0 < h)
        (u : H1MeanZeroFunction (openCubeSet Q)),
        IsMeanZeroNeumannRhsWeakSolution
          (fun _ : Vec d => (1 : Mat d)) (openCubeSet Q) u
          (fun x =>
            -(oneStepShellForcingW14 M n h omega q Q hh).toField x) →
        MemLp u.toH1Function.grad 4 (normalizedCubeMeasure Q) ∧
          cubeLpNorm Q 4 u.toH1Function.grad ≤
            C * cubeLpNorm Q 4
              (oneStepShellForcingW14 M n h omega q Q hh).toField := by
  obtain ⟨C, hCpos, hC⟩ :=
    CubeCalderonZygmund.exists_cubeH1MeanZeroNeumannDivergence_cz
      d oneStepFourExponent
  refine ⟨C, hCpos, ?_⟩
  intro M n h omega q Q hh u hu
  let G := oneStepShellForcingW14 M n h omega q Q hh
  have hGhilbert : MemLp (fun x => HilbertVec.ofVec (G.toField x)) 4
      (normalizedCubeMeasure Q) := by
    simpa only [oneStepFourExponent_exponent] using G.euclideanMemLp
  have hGraw : MemLp G.toField 4 (normalizedCubeMeasure Q) := by
    simpa only [Function.comp_apply,
      HilbertVec.continuousLinearEquivVec_apply, HilbertVec.toVec_ofVec] using!
      (HilbertVec.continuousLinearEquivVec d).toContinuousLinearMap.comp_memLp'
        hGhilbert
  have h := hC Q G.toField hGraw u hu
  simpa only [oneStepFourExponent_exponent, G] using h

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
