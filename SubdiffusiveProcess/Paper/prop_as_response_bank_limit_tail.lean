import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic
import SubdiffusiveProcess.Paper.prop_as_response_bank_cauchy
import SubdiffusiveProcess.Paper.prop_as_response_bank_limit_completion

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

lemma aux_prop_as_response_bank_limit_tail_threshold
    {k m D x y z : ℝ} (hk : 0 < k) (hD : 0 < D)
    (hm : m = k / (2 * (1 + k))) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : k * y + 4 * D < |x - y|) (hz : |z - y| < D / 2) :
    m * x + D < |x - z| := by
  have h1 : 0 < 1 + k := by linarith
  have hm0 : 0 ≤ m := by
    rw [hm]
    positivity
  have hm1 : m < 1 := by
    rw [hm]
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith
  have hxle : x ≤ |x - y| + y := by
    calc
      x = (x - y) + y := by ring
      _ ≤ |x - y| + y := by
        gcongr
        exact le_abs_self (x - y)
  have hbound : m * x + D + |z - y| ≤
      m * (|x - y| + y) + D + D / 2 := by
    gcongr
  have hmain : m * (|x - y| + y) + D + D / 2 < |x - y| := by
    rw [hm]
    field_simp
    have hscaled := mul_lt_mul_of_pos_left hxy (by nlinarith : 0 < 2 + k)
    ring_nf at hscaled ⊢
    nlinarith [hscaled]
  have hxy_z : |x - y| ≤ |x - z| + |z - y| := by
    calc
      |x - y| = |(x - z) + (z - y)| := by congr 1 <;> ring
      _ ≤ |x - z| + |z - y| := abs_add_le _ _
  linarith

/--
Docstring tick list: `hpair` is the fixed-`N`/large-`M` summable comparison
from `prop_as_response_bank_cauchy`; `hconv` is the measurable limit in
probability from `prop_as_response_bank_limit_completion`; the finite response
family and limiting family use the same probability space and index. The
limit-relative summable tail is concluded here, including the strict-threshold
slack used in paper 4452--4454.
-/
theorem prop_as_response_bank_limit_tail
    {Ω I : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] [Countable I]
    (Z : I → ℕ → Ω → ℝ) (L : I → Ω → ℝ)
    (hZ : ∀ i N, Measurable (Z i N))
    (hL : ∀ i, Measurable (L i))
    (hZnonneg : ∀ i N ω, 0 ≤ Z i N ω)
    (hLnonneg : ∀ i ω, 0 ≤ L i ω)
    (Cgeom : ℝ) (hCgeom : 0 < Cgeom)
    (hpair : ∀ i : I, ∀ eps : ℝ, 0 < eps →
      ∃ Ce ce : ℝ, ∃ Ne : ℕ,
        0 < Ce ∧ 0 < ce ∧
        ∀ N : ℕ, Ne ≤ N →
          ∃ M0 : ℕ, N ≤ M0 ∧ ∀ M : ℕ, M0 ≤ M →
            P {ω |
                Cgeom * eps * Z i N ω +
                    Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
                  |Z i N ω - Z i M ω|} ≤
              ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ)))))
    (hconv : ∀ i, TendstoInMeasure P (Z i) atTop (L i)) :
    ∀ i : I, ∀ eps : ℝ, 0 < eps →
      ∃ Ce ce : ℝ, ∃ Ne : ℕ,
        0 < Ce ∧ 0 < ce ∧
        ∀ N : ℕ, Ne ≤ N →
          P {ω |
              Cgeom * eps * L i ω +
                  Ce * (3 : ℝ) ^ (-(ce * (N : ℝ))) <
                |Z i N ω - L i ω|} ≤
            ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (N : ℝ)))) := by
  intro i eps heps
  let eps₀ : ℝ := eps / (2 * (1 + Cgeom * eps))
  have hk : 0 < Cgeom * eps := mul_pos hCgeom heps
  have heps₀ : 0 < eps₀ := by
    dsimp [eps₀]
    positivity
  obtain ⟨Ce, ce, Ne, hCe, hce, hNe⟩ := hpair i eps₀ heps₀
  refine ⟨4 * Ce, ce, Ne, by positivity, hce, ?_⟩
  intro N hN
  obtain ⟨M₀, hNM₀, hM₀⟩ := hNe N hN
  let D : ℝ := Ce * (3 : ℝ) ^ (-(ce * (N : ℝ)))
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hm : Cgeom * eps₀ = (Cgeom * eps) / (2 * (1 + Cgeom * eps)) := by
    dsimp [eps₀]
    field_simp
  have hclose_tendsto :
      Tendsto (fun M : ℕ =>
        P {ω | D / 2 ≤ dist (Z i M ω) (L i ω)}) atTop (𝓝 0) := by
    exact (tendstoInMeasure_iff_dist.mp (hconv i)) (D / 2) (by positivity)
  rw [ENNReal.tendsto_atTop_zero] at hclose_tendsto
  obtain ⟨M₁, hM₁⟩ := hclose_tendsto (ENNReal.ofReal D)
    (ENNReal.ofReal_pos.mpr hD)
  let M : ℕ := max M₀ M₁
  have hMge₀ : M₀ ≤ M := le_max_left _ _
  have hMge₁ : M₁ ≤ M := le_max_right _ _
  let A : Set Ω := {ω |
    Cgeom * eps * L i ω + 4 * D < |Z i N ω - L i ω|}
  let B : Set Ω := {ω |
    Cgeom * eps₀ * Z i N ω + D < |Z i N ω - Z i M ω|}
  let C : Set Ω := {ω | D / 2 ≤ |Z i M ω - L i ω|}
  have hB : P B ≤ ENNReal.ofReal D := by
    simpa [B, D] using hM₀ M hMge₀
  have hC : P C ≤ ENNReal.ofReal D := by
    simpa [C, Real.dist_eq] using hM₁ M hMge₁
  have hsubset : A ⊆ B ∪ C := by
    intro ω hω
    by_cases hωC : ω ∈ C
    · exact Or.inr hωC
    · left
      have hclose : |Z i M ω - L i ω| < D / 2 := by
        exact lt_of_not_ge hωC
      apply aux_prop_as_response_bank_limit_tail_threshold hk hD
        (by simpa [hm] using hm) (hZnonneg i N ω) (hLnonneg i ω)
      · simpa [A] using hω
      · exact hclose
  have hAB : P A ≤ P B + P C :=
    (measure_mono hsubset).trans (measure_union_le B C)
  have hsum : P B + P C ≤ ENNReal.ofReal D + ENNReal.ofReal D :=
    add_le_add hB hC
  have htail : ENNReal.ofReal D + ENNReal.ofReal D ≤
      ENNReal.ofReal (4 * D) := by
    calc
      ENNReal.ofReal D + ENNReal.ofReal D = ENNReal.ofReal (D + D) :=
        (ENNReal.ofReal_add hD.le hD.le).symm
      _ ≤ ENNReal.ofReal (4 * D) :=
        ENNReal.ofReal_mono (by linarith)
  have hbound : P A ≤ ENNReal.ofReal (4 * D) :=
    hAB.trans (hsum.trans htail)
  simpa [A, D, mul_assoc] using hbound

end Paper
