module

public import SubdiffusiveProcess.Static.CutoffMassGrowth
public import SubdiffusiveProcess.Static.CutoffHarmonicGrowth
public import SubdiffusiveProcess.Static.CutoffNestedCoercivity
public import SubdiffusiveProcess.Static.UniformSupplierAssembly
public import SubdiffusiveProcess.Frozen.Section6.Defs.CoefficientAt
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GoodSetMeasurable
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellSummable
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import SubdiffusiveProcess.Frozen.Vocab.Ahom

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.Paper

/-- The three estimates of Lemma `tight:lem-static` (σ = 1/2, t = 3/4) for a speed density `b`,
a coefficient `A`, a reference cube `ball y0 (ρ0/2)` and finitely many concentric pairs
`V_0 ⋐ V_1`, pair `i` having centre `c i` and sides `s0 i < s1 i` (sup-norm balls are cubes); the nested family
is `V_{i,k,n}` of side `(1 - k/2ⁿ) s0 i + (k/2ⁿ) s1 i`, `0 ≤ k ≤ 2ⁿ`:
1. mass bounds `K⁻¹ r^{d+σ} ≤ μ(B_r(x)) ≤ K r^{d-σ}`, `μ = b dx`, for balls of radius `0 < r ≤ 1` in the reference cube;
2. `H^t` coercivity `‖v‖²_{H^t(V)} ≤ K 2^{Bn} (𝓔(v;V) + ‖v‖²_{L²(V,dx)})` on `V_{i,k,n}` (level `n = 0` gives the constant `K`),
   and without the `L²` term on `H¹₀(V)`; written with the unnormalized lower integrals
   `∫∫ (v x − v z)²/|x − z|^{d+3/2} + ∫ v²` (the normalizations differ by factors depending only on the fixed
   reference geometry, absorbed in `K`);
3. cutoffs `χ ∈ H¹₀(V_{i,k+1,n})`, `0 ≤ χ ≤ 1`, `χ = 1` on `V_{i,k,n}`, vanishing near the boundary of the larger
   cube, with `Γ_χ(B_r(x)) = ∫_{B_r(x)} A|∇χ|² ≤ K a^{-B} r^{d-σ}`, `a` the gap `(s1 i − s0 i) 2^{-n}/2`. -/
def aux_tight_lem_static_estimates {d : ℕ} (b A : Vec d → ℝ) (y0 : Vec d) (ρ0 : ℝ) {p : ℕ}
    (c : Fin p → Vec d) (s0 s1 : Fin p → ℝ) (K B : ℝ) : Prop :=
  (∀ (x : Vec d) (r : ℝ), 0 < r → r ≤ 1 → Metric.ball x r ⊆ Metric.ball y0 (ρ0 / 2) →
      ENNReal.ofReal (K⁻¹ * r ^ ((d : ℝ) + 1 / 2)) ≤
          volume.withDensity (fun z => ENNReal.ofReal (b z)) (Metric.ball x r) ∧
        volume.withDensity (fun z => ENNReal.ofReal (b z)) (Metric.ball x r) ≤
          ENNReal.ofReal (K * r ^ ((d : ℝ) - 1 / 2))) ∧
  (∀ (i : Fin p) (n k : ℕ), k ≤ 2 ^ n →
      (∀ v : Homogenization.H1Function
            (Metric.ball (c i) (((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i) / 2)),
        (∫⁻ x in Metric.ball (c i) (((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i) / 2),
            ∫⁻ z in Metric.ball (c i) (((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i) / 2),
              ENNReal.ofReal ((v.toFun x - v.toFun z) ^ 2) /
                ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))) +
          ∫⁻ x in Metric.ball (c i) (((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i) / 2),
            ENNReal.ofReal (v.toFun x ^ 2) ≤
        ENNReal.ofReal (K * (2 : ℝ) ^ (B * n)) *
          ((∫⁻ x in Metric.ball (c i) (((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i) / 2),
              ENNReal.ofReal (A x * Homogenization.vecDot (v.grad x) (v.grad x))) +
            ∫⁻ x in Metric.ball (c i) (((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i) / 2),
              ENNReal.ofReal (v.toFun x ^ 2))) ∧
      (∀ v : Homogenization.H10Function
            (Metric.ball (c i) (((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i) / 2)),
        (∫⁻ x in Metric.ball (c i) (((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i) / 2),
            ∫⁻ z in Metric.ball (c i) (((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i) / 2),
              ENNReal.ofReal ((v.toFun x - v.toFun z) ^ 2) /
                ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))) +
          ∫⁻ x in Metric.ball (c i) (((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i) / 2),
            ENNReal.ofReal (v.toFun x ^ 2) ≤
        ENNReal.ofReal (K * (2 : ℝ) ^ (B * n)) *
          ∫⁻ x in Metric.ball (c i) (((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i) / 2),
            ENNReal.ofReal (A x * Homogenization.vecDot (v.grad x) (v.grad x)))) ∧
  (∀ (i : Fin p) (n k : ℕ), k < 2 ^ n →
      ∃ chi : Homogenization.H10Function
          (Metric.ball (c i) (((1 - ((k + 1 : ℕ) : ℝ) / 2 ^ n) * s0 i +
            (((k + 1 : ℕ) : ℝ) / 2 ^ n) * s1 i) / 2)),
        (∀ x, 0 ≤ chi.toFun x ∧ chi.toFun x ≤ 1) ∧
        (∀ x ∈ Metric.ball (c i) (((1 - (k : ℝ) / 2 ^ n) * s0 i + ((k : ℝ) / 2 ^ n) * s1 i) / 2),
          chi.toFun x = 1) ∧
        tsupport chi.toFun ⊆ Metric.ball (c i) (((1 - ((k + 1 : ℕ) : ℝ) / 2 ^ n) * s0 i +
            (((k + 1 : ℕ) : ℝ) / 2 ^ n) * s1 i) / 2) ∧
        ∀ (x : Vec d) (r : ℝ), 0 < r → r ≤ 1 →
          ∫⁻ z in Metric.ball x r ∩ Metric.ball (c i) (((1 - ((k + 1 : ℕ) : ℝ) / 2 ^ n) * s0 i +
              (((k + 1 : ℕ) : ℝ) / 2 ^ n) * s1 i) / 2),
              ENNReal.ofReal (A z * Homogenization.vecDot (chi.grad z) (chi.grad z)) ≤
            ENNReal.ofReal (K * ((s1 i - s0 i) / 2 ^ n / 2) ^ (-B) * r ^ ((d : ℝ) - 1 / 2)))



theorem tight_lem_static (d : ℕ) (y0 : Vec d) (ρ0 : ℝ) (hρ0 : 0 < ρ0) (p : ℕ)
    (c : Fin p → Vec d) (s0 s1 : Fin p → ℝ)
    (hs : ∀ i, 0 < s0 i ∧ s0 i < s1 i)
    (_hin : ∀ i, Metric.ball (c i) (s1 i / 2) ⊆ Metric.ball y0 (ρ0 / 2)) :
    ∃ B : ℝ, 0 < B ∧ ∀ q : ℝ, 1 ≤ q →
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ delta0 →
        ∃ C : ℝ, 0 < C ∧
          ∀ (L : WithTop ℕ) (m : ℕ) (z : Vec d),
            ∃ K : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d → ℝ, Measurable K ∧
              (∀ ω, 1 ≤ K ω) ∧
              (∫⁻ ω, ENNReal.ofReal (K ω ^ q)
                ∂(_root_.SubdiffusiveProcess.Model.anchoredC11SampleLaw M
                  (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measurableSet_anchoredC11GoodSet d)
                  (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measure_anchoredC11GoodSet_eq_one M)).toMeasure) ≤
                ENNReal.ofReal C ∧
              ∀ᵐ ω ∂(_root_.SubdiffusiveProcess.Model.anchoredC11SampleLaw M
                  (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measurableSet_anchoredC11GoodSet d)
                  (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measure_anchoredC11GoodSet_eq_one M)).toMeasure,
                let j : ℕ := match L with
                  | ⊤ => m
                  | (n : ℕ) => min m n
                let cz : ℝ := coefficientAt M L ω z /
                  _root_.SubdiffusiveProcess.Model.aCutoff M j ω.1 z
                let b : Vec d → ℝ := fun x => cz⁻¹ * coefficientAt M L ω (z + (3 : ℝ) ^ m • x)
                aux_tight_lem_static_estimates b (fun x => (ahom M j)⁻¹ * b x) y0 ρ0 c s0 s1 (K ω) B := by
  refine ⟨5, by norm_num, ?_⟩
  intro q hq
  have hm : SubdiffusiveProcess.Static.UniformLocalMomentSupplier q (fun M L m z ω K =>
      SubdiffusiveProcess.Static.localMassEstimates
        (SubdiffusiveProcess.Static.localDensity M L m z ω) y0 ρ0 K) :=
    SubdiffusiveProcess.Static.exists_uniform_local_mass d y0 ρ0 hρ0 q hq
  have hc : SubdiffusiveProcess.Static.UniformLocalMomentSupplier q (fun M L m z ω K =>
      SubdiffusiveProcess.Static.localCoercivityEstimates
        (SubdiffusiveProcess.Static.localCoefficient M L m z ω) c s0 s1 K 5) :=
    SubdiffusiveProcess.Static.exists_uniform_local_coercivity d p c s0 s1 hs q hq
  have hh : SubdiffusiveProcess.Static.UniformLocalMomentSupplier q (fun M L m z ω K =>
      SubdiffusiveProcess.Static.localHarmonicCutoffEstimates
        (SubdiffusiveProcess.Static.localCoefficient M L m z ω) c s0 s1 K 5) :=
    SubdiffusiveProcess.Static.exists_uniform_local_harmonic_cutoffs d p c s0 s1 hs q hq
  exact SubdiffusiveProcess.Static.uniformLocalMomentSupplier_estimates y0 ρ0 c s0 s1 hs q 5 hm hc hh

end SubdiffusiveProcess.Paper
