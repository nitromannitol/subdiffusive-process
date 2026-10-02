import SubdiffusiveProcess.Static.HarmonicPairDyadicGeometry
import SubdiffusiveProcess.Static.HarmonicPairMajorant

/-! # The literal dyadic clause from a uniform arbitrary-pair supplier -/
open MeasureTheory Homogenization Metric
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- The four literal witness clauses for one nested pair. -/
def PairEnergyCutoff {d : ℕ} (A : Vec d → ℝ) (c : Vec d) (R1 R2 G : ℝ) : Prop :=
  ∃ chi : H10Function (ball c R2),
    (∀ x, 0 ≤ chi.toFun x ∧ chi.toFun x ≤ 1) ∧
    (∀ x ∈ ball c R1, chi.toFun x = 1) ∧ tsupport chi.toFun ⊆ ball c R2 ∧
    ∀ (x : Vec d) (r : ℝ), 0 < r → r ≤ 1 →
      ∫⁻ w in ball x r ∩ ball c R2,
        ENNReal.ofReal (A w * vecDot (chi.grad w) (chi.grad w)) ≤
          ENNReal.ofReal (G * r ^ ((d : ℝ) - 1 / 2))

/-- The radius appearing literally in the local cutoff predicate. -/
def pairDyadicRadius (s0 s1 : ℝ) (n k : ℕ) : ℝ :=
  ((1 - (k : ℝ) / 2 ^ n) * s0 + ((k : ℝ) / 2 ^ n) * s1) / 2

/-- Uniform pair moments give the full countable dyadic cutoff clause, with a
moment price independent of the particular pair family. -/
theorem exists_dyadic_harmonic_cutoffs_of_uniform_pairs
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    {d p : ℕ} (A : Omega → Vec d → ℝ) (c : Fin p → Vec d) (s0 s1 : Fin p → ℝ)
    (hs : ∀ i, 0 < s0 i ∧ s0 i < s1 i) {q B rho : ℝ}
    (hq : 1 ≤ q) (hB : 0 ≤ B) (houter : ∀ i, s1 i / 2 ≤ rho)
    (hpairs : ∀ (i : Fin p) (R1 R2 : ℝ), 0 < R1 → R1 < R2 → R2 ≤ rho →
      ∃ Z : Omega → ℝ, Measurable Z ∧ eLpNorm Z (ENNReal.ofReal q) mu ≤ ENNReal.ofReal B ∧
        ∀ᵐ omega ∂mu, PairEnergyCutoff (A omega) (c i) R1 R2
          (Z omega * (R2 - R1) ^ (-3 : ℝ))) :
    ∃ K : Omega → ℝ, Measurable K ∧ (∀ omega, 1 ≤ K omega) ∧
      (∫⁻ omega, ENNReal.ofReal (K omega ^ q) ∂mu) ≤
        ENNReal.ofReal ((1 + ∑ i : Fin p, ((s1 i - s0 i) / 2) ^ 2) ^ q *
          (1 + 4 * (p : ℝ) * B) ^ q) ∧
      ∀ᵐ omega ∂mu, localHarmonicCutoffEstimates (A omega) c s0 s1 (K omega) 5 := by
  classical
  have hex : ∀ (n : ℕ) (i : Fin p) (k : Fin (2 ^ n + 1)),
      ∃ Z : Omega → ℝ, Measurable Z ∧ eLpNorm Z (ENNReal.ofReal q) mu ≤ ENNReal.ofReal B ∧
        ∀ᵐ omega ∂mu, (k : ℕ) < 2 ^ n →
          PairEnergyCutoff (A omega) (c i)
            (pairDyadicRadius (s0 i) (s1 i) n k)
            (pairDyadicRadius (s0 i) (s1 i) n (k + 1))
            (Z omega * ((s1 i - s0 i) / 2 ^ n / 2) ^ (-3 : ℝ)) := by
    intro n i k
    by_cases hk : (k : ℕ) < 2 ^ n
    · obtain ⟨hR1, hR12, hR2, hgap⟩ := pair_dyadic_sides (hs i).1 (hs i).2 n k hk
      obtain ⟨Z, hZmeas, hZnorm, hZpair⟩ := hpairs i
        (pairDyadicRadius (s0 i) (s1 i) n k)
        (pairDyadicRadius (s0 i) (s1 i) n (k + 1)) hR1 hR12
        (hR2.trans (houter i))
      refine ⟨Z, hZmeas, hZnorm, ?_⟩
      filter_upwards [hZpair] with omega homega
      intro _
      simpa only [pairDyadicRadius, hgap] using homega
    · refine ⟨fun _ => 0, measurable_const, ?_, ?_⟩
      · simpa using (zero_le (ENNReal.ofReal B))
      · exact Filter.Eventually.of_forall fun _ hk' => (hk hk').elim
  choose Z hZmeas hZnorm hZpair using hex
  apply exists_local_harmonic_majorant_with_moment_price mu A c s0 s1 hs hq hB
    Z (fun n i k => (hZmeas n i k).aestronglyMeasurable) hZnorm
  intro n i k
  simpa only [PairEnergyCutoff, pairDyadicRadius] using hZpair n i k

end SubdiffusiveProcess.Static
