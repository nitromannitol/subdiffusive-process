module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsForcedBridge
public import Homogenization.Book.Ch01.Theorems.CutoffProduct
public import Homogenization.Book.Ch01.Theorems.BesovPairing

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-- The `L²`-normalized cube membership of a component of an `L²` field. -/
private theorem memLp_component_of_memLp_vec {Q : TriadicCube d}
    {F : Vec d → Vec d} (hF : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (i : Fin d) :
    MemLp (fun x => F x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hF

/-- The scalar product of an `L²` component with an `L²` scalar is integrable. -/
private theorem integrable_mul_of_memLp_two {Q : TriadicCube d}
    {f g : Vec d → ℝ}
    (hf : MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hg : MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    Integrable (fun x => f x * g x) (normalizedCubeMeasure Q) := by
  have := MemLp.integrable_mul hf hg
  simpa only [Pi.mul_def] using! this

/-- The cutoff-product duality price for the **fluctuation** scalar.

This is `[AK.HC, Lemma A.1]` composed with the Besov duality of
`[AK.HC, Lemma A.3]`, in the development's committed disjoint-cube circ norms. -/
theorem abs_cubeBesovPairing_cutoffProduct_fluctuation_le
    [NeZero d] (Q : TriadicCube d) (s : ℝ)
    (flux : Vec d → Vec d) (u : H1Function (openCubeSet Q)) (ξ : Vec d → Vec d)
    {B : ℝ} (hB : 0 ≤ B)
    (hflux : MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MemLp ξ (∞ : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q,
      ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hs0 : 0 < s) (hs1 : s < 1) (i : Fin d) :
    |cubeBesovPairing Q (fun x => flux x i)
        (fun x => cubeFluctuation Q (fun y => u y) x * ξ x i)| ≤
      ((3 : ℝ) ^ ((d : ℝ) + s) *
          Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => flux x i)) *
        ((2 * cubeScaleFactor Q * B + 3 * cubeLpNorm Q ∞ ξ) *
          ((Book.Ch01.Legacy.fullVectorPoincareConstant Q *
              (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ∑ j : Fin d,
              Book.Ch01.Legacy.circNegativeBesovNorm Q (1 - s)
                (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u.grad x j))) := by
  classical
  set P : ℝ :=
    (Book.Ch01.Legacy.fullVectorPoincareConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ∑ j : Fin d,
        Book.Ch01.Legacy.circNegativeBesovNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => u.grad x j) with hPdef
  set Bg : ℝ := (2 * cubeScaleFactor Q * B + 3 * cubeLpNorm Q ∞ ξ) * P with hBgdef
  have hfluxi : MemLp (fun x => flux x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_component_of_memLp_vec hflux i
  -- the product is in `L²`, hence a legitimate local dual test
  have hu2 : MemLp (fun x => u x) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    u.memL2_normalizedCubeMeasure
  have hv2 : MemLp (cubeFluctuation Q (fun y => u y)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
    simpa [cubeFluctuation, Pi.sub_def] using!
      hu2.sub (MeasureTheory.memLp_const (cubeAverage Q (fun y => u y)))
  have hprod2 :
      MemLp (fun x => cubeFluctuation Q (fun y => u y) x * ξ x i) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := by
    have hξi : MemLp (fun x => ξ x i) (∞ : ℝ≥0∞) (normalizedCubeMeasure Q) := by
      simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hξLp
    let : ENNReal.HolderTriple (2 : ℝ≥0∞) ∞ (2 : ℝ≥0∞) := by infer_instance
    simpa [smul_eq_mul, Pi.smul_def, Pi.mul_def, mul_comm, cubeFluctuation] using!
      hξi.smul (p := ∞) (q := (2 : ℝ≥0∞)) (r := (2 : ℝ≥0∞)) hv2
  have hmem :
      CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞)
        (fun x => cubeFluctuation Q (fun y => u y) x * ξ x i) :=
    cubeBesovDualLocalMemLpGlobal_of_memLp_two Q _ hprod2
  have hq : cubeBesovConjExponent (1 : ℝ≥0∞) = ∞ := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (1 : ℝ≥0∞)) (q := (∞ : ℝ≥0∞)))
  have hpConj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hnorm : ∀ N : ℕ,
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => cubeFluctuation Q (fun y => u y) x * ξ x i) ≤ Bg := by
    intro N
    rw [cubeBesovDualTestNorm_of_conjExponent_eq_top Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N _ hq,
      hpConj]
    simpa [hBgdef, hPdef, smul_eq_mul] using
      Book.Ch01.Legacy.cutoffProduct_component_partialNormTop_le_gradient_rhs
        Q s N u ξ hB hξLp hξ hderiv hs0 hs1 i
  have hBg : 0 ≤ Bg := by
    have h0 := hnorm 0
    rw [cubeBesovDualTestNorm_of_conjExponent_eq_top Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) 0 _ hq,
      hpConj] at h0
    exact le_trans
      (cubeBesovPartialNormTop_nonneg Q s (2 : ℝ≥0∞) 0
        (fun x => cubeFluctuation Q (fun y => u y) x * ξ x i)) h0
  exact Book.Ch01.Legacy.cubeBesovPairing_two_one_le_circNorm_mul_testBound
    Q s (fun x => flux x i) _ hs0 hfluxi hBg hnorm hmem

/-- The cutoff-product duality price for the **mean** piece.

The scalar is the constant `⟨u⟩_Q`, so the positive Besov factor is the
smooth-field endpoint of
`cubeBesovDualTestNorm_two_one_le_scaleWeight_mul_of_contDiff_bound_of_le_one`,
valid for every `s ≤ 1`. -/
theorem abs_cubeBesovPairing_cutoffProduct_mean_le
    (Q : TriadicCube d) (s : ℝ) (c : ℝ)
    (flux : Vec d → Vec d) (ξ : Vec d → Vec d)
    {B : ℝ} (hB : 0 ≤ B)
    (hflux : MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MemLp ξ (∞ : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q,
      ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (i : Fin d) :
    |cubeBesovPairing Q (fun x => flux x i) (fun x => c * ξ x i)| ≤
      ((3 : ℝ) ^ ((d : ℝ) + s) *
          Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => flux x i)) *
        (‖c‖ *
          (cubeBesovScaleWeight s Q *
            (cubeScaleFactor Q * B + cubeLpNorm Q ∞ ξ))) := by
  classical
  set Bg : ℝ :=
    ‖c‖ * (cubeBesovScaleWeight s Q * (cubeScaleFactor Q * B + cubeLpNorm Q ∞ ξ))
    with hBgdef
  have hξi : MemLp (fun x => ξ x i) (∞ : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hξLp
  have hfluxi : MemLp (fun x => flux x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_component_of_memLp_vec hflux i
  have hprod2 :
      MemLp (fun x => c * ξ x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    have : MemLp (fun x => c * ξ x i) (∞ : ℝ≥0∞) (normalizedCubeMeasure Q) := by
      simpa [smul_eq_mul, Pi.smul_def, Pi.mul_def, mul_comm, cubeFluctuation] using! hξi.const_smul c
    exact this.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ ∞)
  have hmem :
      CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (fun x => c * ξ x i) :=
    cubeBesovDualLocalMemLpGlobal_of_memLp_two Q _ hprod2
  have hsmooth : ∀ N : ℕ,
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => ξ x i) ≤
        cubeBesovScaleWeight s Q * (cubeScaleFactor Q * B + cubeLpNorm Q ∞ ξ) := by
    intro N
    refine le_trans
      (cubeBesovDualTestNorm_two_one_le_scaleWeight_mul_of_contDiff_bound_of_le_one
        Q (fun x => ξ x i) N hs1 hB hξi (hξ i) (fun z hz => hderiv i z hz)) ?_
    exact mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (cubeLpNorm_component_le_cubeLpNorm Q ∞ ξ i hξLp))
      (cubeBesovScaleWeight_nonneg s Q)
  have hnorm : ∀ N : ℕ,
      cubeBesovDualTestNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => c * ξ x i) ≤ Bg := by
    intro N
    refine le_trans (cubeBesovDualTestNorm_two_one_const_mul_le Q s N c _) ?_
    exact mul_le_mul_of_nonneg_left (hsmooth N) (norm_nonneg c)
  have hBg : 0 ≤ Bg := by
    refine mul_nonneg (norm_nonneg c) (mul_nonneg (cubeBesovScaleWeight_nonneg s Q) ?_)
    exact add_nonneg (mul_nonneg (cubeScaleFactor_nonneg Q) hB) (cubeLpNorm_nonneg Q ∞ ξ)
  exact Book.Ch01.Legacy.cubeBesovPairing_two_one_le_circNorm_mul_testBound
    Q s (fun x => flux x i) _ hs0 hfluxi hBg hnorm hmem

/-- **The cutoff-product Besov duality price.**

This is the composite form of `[AK.HC, Lemmas A.1 and A.3]` that the proof of
`l.local.L2.resolvent`  consumes: the
pairing of an arbitrary `L²` field `flux` against the product of an `H¹`
function with a smooth field `xi`, priced by the concrete circ negative Besov
norms of `flux` and of `∇u` — both of which are exactly the left-hand sides of
the two clauses of `SubdiffusiveProcess.Frozen.Section2.coarse_grained_poincare`. -/
theorem abs_cubeAverage_vecDot_cutoffProduct_le
    [NeZero d] (Q : TriadicCube d) (s : ℝ)
    (flux : Vec d → Vec d) (u : H1Function (openCubeSet Q)) (ξ : Vec d → Vec d)
    {B : ℝ} (hB : 0 ≤ B)
    (hflux : MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MemLp ξ (∞ : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q,
      ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hs0 : 0 < s) (hs1 : s < 1) :
    |cubeAverage Q (fun x => vecDot (flux x) ((u x) • ξ x))| ≤
      ((3 : ℝ) ^ ((d : ℝ) + s) *
          ∑ i : Fin d,
            Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (fun x => flux x i)) *
        ((2 * cubeScaleFactor Q * B + 3 * cubeLpNorm Q ∞ ξ) *
            ((Book.Ch01.Legacy.fullVectorPoincareConstant Q *
                (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ∑ j : Fin d,
                Book.Ch01.Legacy.circNegativeBesovNorm Q (1 - s)
                  (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u.grad x j)) +
          ‖cubeAverage Q (fun y => u y)‖ *
            (cubeBesovScaleWeight s Q *
              (cubeScaleFactor Q * B + cubeLpNorm Q ∞ ξ))) := by
  classical
  set c : ℝ := cubeAverage Q (fun y => u y) with hcdef
  set Bfl : ℝ :=
    (2 * cubeScaleFactor Q * B + 3 * cubeLpNorm Q ∞ ξ) *
      ((Book.Ch01.Legacy.fullVectorPoincareConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        ∑ j : Fin d,
          Book.Ch01.Legacy.circNegativeBesovNorm Q (1 - s) (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => u.grad x j)) with hBfldef
  set Bmn : ℝ :=
    ‖c‖ * (cubeBesovScaleWeight s Q * (cubeScaleFactor Q * B + cubeLpNorm Q ∞ ξ))
    with hBmndef
  have hu2 : MemLp (fun x => u x) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    u.memL2_normalizedCubeMeasure
  have hv2 : MemLp (cubeFluctuation Q (fun y => u y)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
    simpa [cubeFluctuation, Pi.sub_def] using!
      hu2.sub (MeasureTheory.memLp_const (cubeAverage Q (fun y => u y)))
  have hξi : ∀ i : Fin d,
      MemLp (fun x => ξ x i) (∞ : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    intro i
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hξLp
  have hfluxi : ∀ i : Fin d,
      MemLp (fun x => flux x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := fun i =>
    memLp_component_of_memLp_vec hflux i
  let : ENNReal.HolderTriple (2 : ℝ≥0∞) ∞ (2 : ℝ≥0∞) := by infer_instance
  have hvprod : ∀ i : Fin d,
      MemLp (fun x => cubeFluctuation Q (fun y => u y) x * ξ x i) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) := by
    intro i
    simpa [smul_eq_mul, Pi.smul_def, Pi.mul_def, mul_comm, cubeFluctuation] using!
      (hξi i).smul (p := ∞) (q := (2 : ℝ≥0∞)) (r := (2 : ℝ≥0∞)) hv2
  have hcprod : ∀ i : Fin d,
      MemLp (fun x => c * ξ x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    intro i
    have : MemLp (fun x => c * ξ x i) (∞ : ℝ≥0∞) (normalizedCubeMeasure Q) := by
      simpa [smul_eq_mul, Pi.smul_def, Pi.mul_def, mul_comm, cubeFluctuation] using! (hξi i).const_smul c
    exact this.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ ∞)
  have huprod : ∀ i : Fin d,
      MemLp (fun x => u x * ξ x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    intro i
    simpa [smul_eq_mul, Pi.smul_def, Pi.mul_def, mul_comm, cubeFluctuation] using!
      (hξi i).smul (p := ∞) (q := (2 : ℝ≥0∞)) (r := (2 : ℝ≥0∞)) hu2
  -- componentwise split of the pairing
  have hsplit : ∀ i : Fin d,
      cubeBesovPairing Q (fun x => flux x i) (fun x => (u x • ξ x) i) =
        cubeBesovPairing Q (fun x => flux x i)
            (fun x => cubeFluctuation Q (fun y => u y) x * ξ x i) +
          cubeBesovPairing Q (fun x => flux x i) (fun x => c * ξ x i) := by
    intro i
    have h1 := integrable_mul_of_memLp_two (hfluxi i) (hvprod i)
    have h2 := integrable_mul_of_memLp_two (hfluxi i) (hcprod i)
    have hpt : ∀ x : Vec d,
        flux x i * (u x • ξ x) i =
          flux x i * (cubeFluctuation Q (fun y => u y) x * ξ x i) +
            flux x i * (c * ξ x i) := by
      intro x
      simp [cubeFluctuation, hcdef, smul_eq_mul]
      ring
    simp only [cubeBesovPairing, cubeAverage_eq_integral_normalizedCubeMeasure]
    rw [← MeasureTheory.integral_add h1 h2]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hInt : ∀ i : Fin d,
      Integrable (fun x => flux x i * (u x • ξ x) i) (normalizedCubeMeasure Q) := by
    intro i
    have := integrable_mul_of_memLp_two (hfluxi i) (huprod i)
    simpa [smul_eq_mul, Pi.smul_def, Pi.mul_def, mul_comm, cubeFluctuation] using! this
  have hsum :=
    abs_cubeAverage_vecDot_le_sum_abs_cubeBesovPairing Q flux
      (fun x => (u x) • ξ x) hInt
  have hbound : ∀ i : Fin d,
      |cubeBesovPairing Q (fun x => flux x i) (fun x => (u x • ξ x) i)| ≤
        ((3 : ℝ) ^ ((d : ℝ) + s) *
          Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => flux x i)) * (Bfl + Bmn) := by
    intro i
    have h1 := abs_cubeBesovPairing_cutoffProduct_fluctuation_le Q s flux u ξ hB
      hflux hξLp hξ hderiv hs0 hs1 i
    have h2 := abs_cubeBesovPairing_cutoffProduct_mean_le Q s c flux ξ hB
      hflux hξLp hξ hderiv hs0 hs1.le i
    calc
      |cubeBesovPairing Q (fun x => flux x i) (fun x => (u x • ξ x) i)|
          ≤ |cubeBesovPairing Q (fun x => flux x i)
                (fun x => cubeFluctuation Q (fun y => u y) x * ξ x i)| +
              |cubeBesovPairing Q (fun x => flux x i) (fun x => c * ξ x i)| := by
            rw [hsplit i]; exact abs_add_le _ _
      _ ≤ ((3 : ℝ) ^ ((d : ℝ) + s) *
              Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                (fun x => flux x i)) * Bfl +
            ((3 : ℝ) ^ ((d : ℝ) + s) *
              Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                (fun x => flux x i)) * Bmn := by
            exact add_le_add (by simpa [hBfldef] using h1) (by simpa [hBmndef] using h2)
      _ = ((3 : ℝ) ^ ((d : ℝ) + s) *
              Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                (fun x => flux x i)) * (Bfl + Bmn) := by ring
  calc
    |cubeAverage Q (fun x => vecDot (flux x) ((u x) • ξ x))|
        ≤ ∑ i : Fin d,
            |cubeBesovPairing Q (fun x => flux x i) (fun x => (u x • ξ x) i)| := hsum
    _ ≤ ∑ i : Fin d,
          ((3 : ℝ) ^ ((d : ℝ) + s) *
            Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (fun x => flux x i)) * (Bfl + Bmn) :=
          Finset.sum_le_sum fun i _ => hbound i
    _ = ((3 : ℝ) ^ ((d : ℝ) + s) *
            ∑ i : Fin d,
              Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
                (fun x => flux x i)) * (Bfl + Bmn) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]




/-- Componentwise domination of the Chapter 1 circ depth seminorm by the
Chapter 3 vector depth seminorm. -/
theorem cubeBesovCircDepthSeminorm_component_le
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) (i : Fin d) (j : ℕ) :
    cubeBesovCircDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => F x i) j ≤
      cubeBesovScaleWeight (-s) Q *
        Book.Ch03.negativeBesovVectorDepthSeminorm Q s F j := by
  classical
  have hscale : (0 : ℝ) ≤ cubeScaleFactor Q := cubeScaleFactor_nonneg Q
  have hpow : (0 : ℝ) ≤ (3 : ℝ) ^ j := by positivity
  -- the two weights differ by `ℓ^s`
  have hweight :
      cubeBesovCircDepthWeight Q s j =
        cubeBesovScaleWeight (-s) Q * ((3 : ℝ) ^ (-s * (j : ℝ))) := by
    unfold cubeBesovCircDepthWeight cubeBesovScaleWeight
    rw [Real.div_rpow hscale hpow, neg_neg, ← Real.rpow_natCast (3 : ℝ) j,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      show (-s * (j : ℝ)) = -((j : ℝ) * s) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), div_eq_mul_inv]
  -- the averages are dominated
  have haux :
      cubeBesovCircDepthAverage Q (2 : ℝ≥0∞) (fun x => F x i) j ≤
        Book.Ch03.negativeBesovVectorDepthAverage Q F j := by
    unfold cubeBesovCircDepthAverage Book.Ch03.negativeBesovVectorDepthAverage
    refine descendantsAverage_le_descendantsAverage Q j ?_
    intro R _
    have hterm : ‖cubeAverage R (fun x => F x i)‖ ^ (2 : ℝ≥0∞).toReal =
        (cubeAverageVec R F i) ^ 2 := by
      simp [Real.norm_eq_abs, cubeAverageVec, sq_abs]
    rw [hterm]
    have : (cubeAverageVec R F i) ^ 2 ≤ vecNormSq (cubeAverageVec R F) := by
      simpa [vecNormSq, vecDot, sq] using
        (Finset.single_le_sum
          (f := fun k : Fin d => cubeAverageVec R F k * cubeAverageVec R F k)
          (fun k _ => mul_self_nonneg _) (Finset.mem_univ i))
    exact this
  have hnonneg : 0 ≤ cubeBesovCircDepthAverage Q (2 : ℝ≥0∞) (fun x => F x i) j :=
    cubeBesovCircDepthAverage_nonneg Q (2 : ℝ≥0∞) _ j
  have hsqrt :
      (cubeBesovCircDepthAverage Q (2 : ℝ≥0∞) (fun x => F x i) j) ^
          (1 / (2 : ℝ≥0∞).toReal) ≤
        Real.sqrt (Book.Ch03.negativeBesovVectorDepthAverage Q F j) := by
    have h2 : (1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by norm_num
    rw [h2, ← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt haux
  unfold cubeBesovCircDepthSeminorm Book.Ch03.negativeBesovVectorDepthSeminorm
  rw [hweight, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (cubeBesovScaleWeight_nonneg (-s) Q)
  exact mul_le_mul_of_nonneg_left hsqrt
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)

/-- Componentwise domination of the Chapter 1 circ partial norm at `q = 1`. -/
theorem cubeBesovCircPartialNorm_component_le
    (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) (i : Fin d) (N : ℕ) :
    cubeBesovCircPartialNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => F x i) ≤
      cubeBesovScaleWeight (-s) Q *
        Book.Ch03.negativeBesovVectorPartialNormFinite Q s 1 N F := by
  classical
  have hone : (1 : ℝ≥0∞).toReal = 1 := by norm_num
  have hLHS :
      cubeBesovCircPartialNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞) N (fun x => F x i) =
        ∑ j ∈ Finset.range (N + 1),
          cubeBesovCircDepthSeminorm Q s (2 : ℝ≥0∞) (fun x => F x i) j := by
    unfold cubeBesovCircPartialNorm cubeBesovCircPartialSeminorm
    simp [hone, Real.rpow_one]
  have hRHS :
      Book.Ch03.negativeBesovVectorPartialNormFinite Q s 1 N F =
        ∑ j ∈ Finset.range (N + 1),
          Book.Ch03.negativeBesovVectorDepthSeminorm Q s F j := by
    unfold Book.Ch03.negativeBesovVectorPartialNormFinite
    simp [Real.rpow_one]
  rw [hLHS, hRHS, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ =>
    cubeBesovCircDepthSeminorm_component_le Q s F i j



theorem circNegativeBesovNorm_component_le_paperNegativeBesovVectorNorm
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (F : Vec d → Vec d) (i : Fin d)
    (hbdd : BddAbove (Set.range fun N : ℕ =>
      Book.Ch03.negativeBesovVectorPartialNormFinite Q s 1 N F)) :
    Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => F x i) ≤
      cubeBesovScaleWeight (-s) Q * s⁻¹ *
        SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm Q s
          (Book.Ch02.MultiscaleExponent.finite 1) F := by
  classical
  have hpaper :
      SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm Q s
          (Book.Ch02.MultiscaleExponent.finite 1) F =
        s * Book.Ch03.scaleNormalizedNegativeBesovVectorNorm Q s
          (Book.Ch02.MultiscaleExponent.finite 1) F := by
    simp [SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm,
      Real.rpow_one]
  rw [hpaper]
  have hrewrite :
      cubeBesovScaleWeight (-s) Q * s⁻¹ *
          (s * Book.Ch03.scaleNormalizedNegativeBesovVectorNorm Q s
            (Book.Ch02.MultiscaleExponent.finite 1) F) =
        cubeBesovScaleWeight (-s) Q *
          Book.Ch03.scaleNormalizedNegativeBesovVectorNorm Q s
            (Book.Ch02.MultiscaleExponent.finite 1) F := by
    field_simp
  rw [hrewrite]
  refine cubeBesovCircNorm_le_of_forall_partialNorm_le Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
    _ (by simp) ?_
  intro N
  refine (cubeBesovCircPartialNorm_component_le Q s F i N).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (cubeBesovScaleWeight_nonneg (-s) Q)
  exact le_csSup hbdd ⟨N, rfl⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
