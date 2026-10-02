import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
import SubdiffusiveProcess.BesovComparison.Comparison

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace Paper

/-- Normalized `L^p(Q)` norm, `p ∈ [1,∞]` (`p = ∞`: essential supremum). -/
def aux_l_Wsp_vs_Bspp_nLp {d : ℕ} (Q : Set (Vec d)) (p : ℝ≥0∞) (f : Vec d → ℝ) : ℝ≥0∞ :=
  eLpNorm f p ((volume Q)⁻¹ • volume.restrict Q)

/-- `ℓ^r` average over a finite index set `S`: `(#S⁻¹ Σ_S t^r)^{1/r}`, and the maximum for `r = ∞`. -/
def aux_l_Wsp_vs_Bspp_avLr {ι : Type*} (S : Set ι) (r : ℝ≥0∞) (t : ι → ℝ≥0∞) : ℝ≥0∞ :=
  if r = ∞ then ⨆ z ∈ S, t z
  else ((S.ncard : ℝ≥0∞)⁻¹ * ∑ᶠ z ∈ S, t z ^ r.toReal) ^ (1 / r.toReal)

/-- Scale aggregation `(s Σ_{n ≤ m} a_n^q)^{1/q}` (supremum for `q = ∞`). -/
def aux_l_Wsp_vs_Bspp_scaleAgg (s : ℝ) (m : ℤ) (q : ℝ≥0∞) (a : ℤ → ℝ≥0∞) : ℝ≥0∞ :=
  if q = ∞ then ⨆ n ∈ {n : ℤ | n ≤ m}, a n
  else (ENNReal.ofReal s * ∑' n : ℤ, (if n ≤ m then a n ^ q.toReal else 0)) ^ (1 / q.toReal)

/-- Centres `z ∈ 3^{n-1}ℤ^d ∩ 𝒞_m` with `z + 𝒞_n ⊆ 𝒞_m`. -/
def aux_l_Wsp_vs_Bspp_posCentres (d : ℕ) (m n : ℤ) : Set (Vec d) :=
  {z | (∀ a : Fin d, ∃ k : ℤ, z a = (3 : ℝ) ^ (n - 1) * k) ∧ z ∈ cube d m ∧
    translatedCube d n z ⊆ cube d m}

/-- Centres `z ∈ 3^nℤ^d ∩ 𝒞_m`. -/
def aux_l_Wsp_vs_Bspp_negCentres (d : ℕ) (m n : ℤ) : Set (Vec d) :=
  {z | (∀ a : Fin d, ∃ k : ℤ, z a = (3 : ℝ) ^ n * k) ∧ z ∈ cube d m}

/-- The seminorm `[u]_{B^s_{p,q,r}(𝒞_m)}` of (e.Besov.Morrey.seminorm), with the endpoint conventions. -/
def aux_l_Wsp_vs_Bspp_besovSemi (d : ℕ) (m : ℤ) (s : ℝ) (p q r : ℝ≥0∞) (u : Vec d → ℝ) : ℝ≥0∞ :=
  aux_l_Wsp_vs_Bspp_scaleAgg s m q (fun n =>
    ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ) * s)) *
      aux_l_Wsp_vs_Bspp_avLr (aux_l_Wsp_vs_Bspp_posCentres d m n) r
        (fun z => aux_l_Wsp_vs_Bspp_nLp (translatedCube d n z) p
          (fun x => u x - ⨍ y in translatedCube d n z, u y)))

/-- `‖g‖_{B^s_{p,q,r}(𝒞_m)} = [g] + 3^{-sm} |(g)_{𝒞_m}|`. -/
def aux_l_Wsp_vs_Bspp_besovNorm (d : ℕ) (m : ℤ) (s : ℝ) (p q r : ℝ≥0∞) (u : Vec d → ℝ) : ℝ≥0∞ :=
  aux_l_Wsp_vs_Bspp_besovSemi d m s p q r u +
    ENNReal.ofReal ((3 : ℝ) ^ (-(m : ℝ) * s) * |⨍ y in cube d m, u y|)

/-- The weak negative norm `‖f‖_{B^{-s}_{r,q}(𝒞_m)}` of (e.Besov.weaknorm.def). -/
def aux_l_Wsp_vs_Bspp_negBesovNorm (d : ℕ) (m : ℤ) (s : ℝ) (r q : ℝ≥0∞) (f : Vec d → ℝ) : ℝ≥0∞ :=
  aux_l_Wsp_vs_Bspp_scaleAgg s m q (fun n =>
    ENNReal.ofReal ((3 : ℝ) ^ ((n : ℝ) * s)) *
      aux_l_Wsp_vs_Bspp_avLr (aux_l_Wsp_vs_Bspp_negCentres d m n) r
        (fun z => ENNReal.ofReal |⨍ y in translatedCube d n z, f y|))

/-- The fractional Sobolev seminorm `[u]_{W^{s,p}(𝒞_m)} = (s ⨍_{𝒞_m}∫_{𝒞_m} |u(x)−u(y)|^p/|x−y|^{d+sp})^{1/p}`
(e.fractional.Sobolev.seminorm; Euclidean distance), in `[0,∞]`. -/
def aux_l_Wsp_vs_Bspp_wsp (d : ℕ) (m : ℤ) (s p : ℝ) (u : Vec d → ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal s * (volume (cube d m))⁻¹ *
    ∫⁻ x in cube d m, ∫⁻ y in cube d m,
      ENNReal.ofReal (|u x - u y| ^ p) /
        ENNReal.ofReal (Homogenization.euclideanNorm (x - y) ^ ((d : ℝ) + s * p))) ^ (1 / p)



theorem l_Wsp_vs_Bspp (d : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (s p : ℝ) (m : ℤ) (u : Vec d → ℝ),
        0 < s → s < 1 → 1 ≤ p → MemLp u (ENNReal.ofReal p) (volume.restrict (cube d m)) →
        ENNReal.ofReal C⁻¹ * aux_l_Wsp_vs_Bspp_wsp d m s p u ≤
            aux_l_Wsp_vs_Bspp_besovSemi d m s (ENNReal.ofReal p) (ENNReal.ofReal p)
              (ENNReal.ofReal p) u ∧
          aux_l_Wsp_vs_Bspp_besovSemi d m s (ENNReal.ofReal p) (ENNReal.ofReal p)
              (ENNReal.ofReal p) u ≤
            ENNReal.ofReal C * aux_l_Wsp_vs_Bspp_wsp d m s p u := by
  exact SubdiffusiveProcess.BesovComparison.source_comparison d

end Paper
