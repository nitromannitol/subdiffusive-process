module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

@[expose] public section

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace SubdiffusiveProcess.Besov

/-- Normalized `L^p(Q)` norm, `p ∈ [1,∞]` (`p = ∞`: essential supremum). -/
def normalizedLp {d : ℕ} (Q : Set (Vec d)) (p : ℝ≥0∞) (f : Vec d → ℝ) : ℝ≥0∞ :=
  eLpNorm f p ((volume Q)⁻¹ • volume.restrict Q)

/-- `ℓ^r` average over a finite index set `S`: `(#S⁻¹ Σ_S t^r)^{1/r}`, and the maximum for `r = ∞`. -/
def averageLr {ι : Type*} (S : Set ι) (r : ℝ≥0∞) (t : ι → ℝ≥0∞) : ℝ≥0∞ :=
  if r = ∞ then ⨆ z ∈ S, t z
  else ((S.ncard : ℝ≥0∞)⁻¹ * ∑ᶠ z ∈ S, t z ^ r.toReal) ^ (1 / r.toReal)

/-- Scale aggregation `(s Σ_{n ≤ m} a_n^q)^{1/q}` (supremum for `q = ∞`). -/
def scaleAggregation (s : ℝ) (m : ℤ) (q : ℝ≥0∞) (a : ℤ → ℝ≥0∞) : ℝ≥0∞ :=
  if q = ∞ then ⨆ n ∈ {n : ℤ | n ≤ m}, a n
  else (ENNReal.ofReal s * ∑' n : ℤ, (if n ≤ m then a n ^ q.toReal else 0)) ^ (1 / q.toReal)

/-- Centres `z ∈ 3^{n-1}ℤ^d ∩ 𝒞_m` with `z + 𝒞_n ⊆ 𝒞_m`. -/
def positiveCentres (d : ℕ) (m n : ℤ) : Set (Vec d) :=
  {z | (∀ a : Fin d, ∃ k : ℤ, z a = (3 : ℝ) ^ (n - 1) * k) ∧ z ∈ cube d m ∧
    translatedCube d n z ⊆ cube d m}

/-- Centres `z ∈ 3^nℤ^d ∩ 𝒞_m`. -/
def negativeCentres (d : ℕ) (m n : ℤ) : Set (Vec d) :=
  {z | (∀ a : Fin d, ∃ k : ℤ, z a = (3 : ℝ) ^ n * k) ∧ z ∈ cube d m}

/-- The seminorm `[u]_{B^s_{p,q,r}(𝒞_m)}` of (e.Besov.Morrey.seminorm), with the endpoint conventions. -/
def besovSeminorm (d : ℕ) (m : ℤ) (s : ℝ) (p q r : ℝ≥0∞) (u : Vec d → ℝ) : ℝ≥0∞ :=
  scaleAggregation s m q (fun n =>
    ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ) * s)) *
      averageLr (positiveCentres d m n) r
        (fun z => normalizedLp (translatedCube d n z) p
          (fun x => u x - ⨍ y in translatedCube d n z, u y)))

/-- `‖g‖_{B^s_{p,q,r}(𝒞_m)} = [g] + 3^{-sm} |(g)_{𝒞_m}|`. -/
def besovNorm (d : ℕ) (m : ℤ) (s : ℝ) (p q r : ℝ≥0∞) (u : Vec d → ℝ) : ℝ≥0∞ :=
  besovSeminorm d m s p q r u +
    ENNReal.ofReal ((3 : ℝ) ^ (-(m : ℝ) * s) * |⨍ y in cube d m, u y|)

/-- The weak negative norm `‖f‖_{B^{-s}_{r,q}(𝒞_m)}` of (e.Besov.weaknorm.def). -/
def negativeBesovNorm (d : ℕ) (m : ℤ) (s : ℝ) (r q : ℝ≥0∞) (f : Vec d → ℝ) : ℝ≥0∞ :=
  scaleAggregation s m q (fun n =>
    ENNReal.ofReal ((3 : ℝ) ^ ((n : ℝ) * s)) *
      averageLr (negativeCentres d m n) r
        (fun z => ENNReal.ofReal |⨍ y in translatedCube d n z, f y|))


end SubdiffusiveProcess.Besov
