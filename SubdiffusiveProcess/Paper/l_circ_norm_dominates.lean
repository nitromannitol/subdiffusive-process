import SubdiffusiveProcess.Besov.ThreeIndexDuality
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace Paper

/-- Normalized `L^p(Q)` norm, `p ∈ [1,∞]` (`p = ∞`: essential supremum). -/
def aux_l_circ_norm_dominates_nLp {d : ℕ} (Q : Set (Vec d)) (p : ℝ≥0∞) (f : Vec d → ℝ) : ℝ≥0∞ :=
  eLpNorm f p ((volume Q)⁻¹ • volume.restrict Q)

/-- `ℓ^r` average over a finite index set `S`: `(#S⁻¹ Σ_S t^r)^{1/r}`, and the maximum for `r = ∞`. -/
def aux_l_circ_norm_dominates_avLr {ι : Type*} (S : Set ι) (r : ℝ≥0∞) (t : ι → ℝ≥0∞) : ℝ≥0∞ :=
  if r = ∞ then ⨆ z ∈ S, t z
  else ((S.ncard : ℝ≥0∞)⁻¹ * ∑ᶠ z ∈ S, t z ^ r.toReal) ^ (1 / r.toReal)

/-- Scale aggregation `(s Σ_{n ≤ m} a_n^q)^{1/q}` (supremum for `q = ∞`). -/
def aux_l_circ_norm_dominates_scaleAgg (s : ℝ) (m : ℤ) (q : ℝ≥0∞) (a : ℤ → ℝ≥0∞) : ℝ≥0∞ :=
  if q = ∞ then ⨆ n ∈ {n : ℤ | n ≤ m}, a n
  else (ENNReal.ofReal s * ∑' n : ℤ, (if n ≤ m then a n ^ q.toReal else 0)) ^ (1 / q.toReal)

/-- Centres `z ∈ 3^{n-1}ℤ^d ∩ 𝒞_m` with `z + 𝒞_n ⊆ 𝒞_m`. -/
def aux_l_circ_norm_dominates_posCentres (d : ℕ) (m n : ℤ) : Set (Vec d) :=
  {z | (∀ a : Fin d, ∃ k : ℤ, z a = (3 : ℝ) ^ (n - 1) * k) ∧ z ∈ cube d m ∧
    translatedCube d n z ⊆ cube d m}

/-- Centres `z ∈ 3^nℤ^d ∩ 𝒞_m`. -/
def aux_l_circ_norm_dominates_negCentres (d : ℕ) (m n : ℤ) : Set (Vec d) :=
  {z | (∀ a : Fin d, ∃ k : ℤ, z a = (3 : ℝ) ^ n * k) ∧ z ∈ cube d m}

/-- The seminorm `[u]_{B^s_{p,q,r}(𝒞_m)}` of (e.Besov.Morrey.seminorm), with the endpoint conventions. -/
def aux_l_circ_norm_dominates_besovSemi (d : ℕ) (m : ℤ) (s : ℝ) (p q r : ℝ≥0∞) (u : Vec d → ℝ) : ℝ≥0∞ :=
  aux_l_circ_norm_dominates_scaleAgg s m q (fun n =>
    ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ) * s)) *
      aux_l_circ_norm_dominates_avLr (aux_l_circ_norm_dominates_posCentres d m n) r
        (fun z => aux_l_circ_norm_dominates_nLp (translatedCube d n z) p
          (fun x => u x - ⨍ y in translatedCube d n z, u y)))

/-- `‖g‖_{B^s_{p,q,r}(𝒞_m)} = [g] + 3^{-sm} |(g)_{𝒞_m}|`. -/
def aux_l_circ_norm_dominates_besovNorm (d : ℕ) (m : ℤ) (s : ℝ) (p q r : ℝ≥0∞) (u : Vec d → ℝ) : ℝ≥0∞ :=
  aux_l_circ_norm_dominates_besovSemi d m s p q r u +
    ENNReal.ofReal ((3 : ℝ) ^ (-(m : ℝ) * s) * |⨍ y in cube d m, u y|)

/-- The weak negative norm `‖f‖_{B^{-s}_{r,q}(𝒞_m)}` of (e.Besov.weaknorm.def). -/
def aux_l_circ_norm_dominates_negBesovNorm (d : ℕ) (m : ℤ) (s : ℝ) (r q : ℝ≥0∞) (f : Vec d → ℝ) : ℝ≥0∞ :=
  aux_l_circ_norm_dominates_scaleAgg s m q (fun n =>
    ENNReal.ofReal ((3 : ℝ) ^ ((n : ℝ) * s)) *
      aux_l_circ_norm_dominates_avLr (aux_l_circ_norm_dominates_negCentres d m n) r
        (fun z => ENNReal.ofReal |⨍ y in translatedCube d n z, f y|))



theorem l_circ_norm_dominates (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℤ) (s : ℝ) (q r : ℝ≥0∞) (f g : Vec d → ℝ),
        0 < s → s ≤ 1 → 1 ≤ q → 1 ≤ r → (s < 1 ∨ (s = 1 ∧ q = 1)) →
        IntegrableOn f (cube d m) → IntegrableOn g (cube d m) →
        IntegrableOn (fun x => f x * g x) (cube d m) →
        aux_l_circ_norm_dominates_besovNorm d m s 1 (ENNReal.conjExponent q) (ENNReal.conjExponent r) g *
          aux_l_circ_norm_dominates_negBesovNorm d m s r q f < ⊤ →
        ENNReal.ofReal |⨍ x in cube d m, f x * g x| ≤
          ENNReal.ofReal (C * s⁻¹) *
            (aux_l_circ_norm_dominates_besovNorm d m s 1 (ENNReal.conjExponent q)
                (ENNReal.conjExponent r) g *
              aux_l_circ_norm_dominates_negBesovNorm d m s r q f) := by
  refine ⟨2 * SubdiffusiveProcess.Besov.pairingConstant d,
    mul_pos (by norm_num) (SubdiffusiveProcess.Besov.pairingConstant_pos d), ?_⟩
  intro m s q r f g hs hsOne hq hr _hadmissible hf hg hfg _hfinite
  have hf' := Homogenization.integrableOn_cubeSet_originCube_iff_integrableOn_openCubeSet_originCube.mpr hf
  have hg' := Homogenization.integrableOn_cubeSet_originCube_iff_integrableOn_openCubeSet_originCube.mpr hg
  have hfg' := Homogenization.integrableOn_cubeSet_originCube_iff_integrableOn_openCubeSet_originCube.mpr hfg
  rw [cube, SubdiffusiveProcess.Besov.openCube_average_eq]
  change ENNReal.ofReal |Homogenization.cubeBesovPairing (Homogenization.originCube d m) f g| ≤
    ENNReal.ofReal ((2 * SubdiffusiveProcess.Besov.pairingConstant d) * s⁻¹) *
      (SubdiffusiveProcess.Besov.besovNorm d m s 1 (ENNReal.conjExponent q) (ENNReal.conjExponent r) g *
        SubdiffusiveProcess.Besov.negativeBesovNorm d m s r q f)
  exact SubdiffusiveProcess.Besov.threeIndex_pairing_le m s hs hsOne q r hq hr f g hf' hg' hfg' 

end Paper
