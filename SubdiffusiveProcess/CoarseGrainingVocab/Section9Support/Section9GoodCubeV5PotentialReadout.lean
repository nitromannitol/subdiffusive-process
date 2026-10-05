module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeConstantTorsionReferenceReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.Algebra

@[expose] public section

/-!
# Reusing the deterministic lower readout at the anchored coefficient

A potential can represent exactly the same coefficient at any cutoff index.
This is an algebraic use of a deterministic theorem quantified over every
sample.  No probability statement is applied to the representing sample, and
no process law is constructed or changed.
-/

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Add a constant to the potential without changing its stored derivative. -/
def goodCubeV5ShiftPotential {d : ℕ} (g : PotentialField d) (c : ℝ) : PotentialField d :=
  ⟨(⟨fun x => g x + c, g.1.1.continuous.add continuous_const⟩, _root_.SubdiffusiveProcess.Model.PotentialField.deriv g),
    (fun x => (g.hasFDerivAt x).add_const c), g.2.2⟩

/-- A deterministic representation of `exp g`, used only in coefficient readouts. -/
def goodCubeV5ReadoutSample {d : ℕ} (M : GMCModel d) (g : PotentialField d) :
    PotentialSample d := fun k =>
  goodCubeV5ShiftPotential (_root_.SubdiffusiveProcess.Model.PotentialField.scale (if k = 0 then 1 else 0) g) (tauSq M.P)

/-- The representation is exact at every index; the original anchored law is retained. -/
theorem goodCubeV5_readout_aCutoff_eq_exp {d : ℕ} (M : GMCModel d)
    (g : PotentialField d) (n : ℕ) :
    aCutoff M n (goodCubeV5ReadoutSample M g) = fun x => Real.exp (g x) := by
  funext x
  unfold aCutoff
  congr 1
  have hterm (k : ℕ) : goodCubeV5ReadoutSample M g k x - tauSq M.P =
      if k = 0 then g x else 0 := by
    change (if k = 0 then 1 else 0) * g x + tauSq M.P - tauSq M.P = _
    split_ifs <;> ring
  simp_rw [hterm]
  simp

/-- The old readout with an arbitrary `C¹ˑ¹` logarithmic coefficient.
All cover, clock, torsion-comparison, and diffusion-data premises are retained. -/
def GoodCubeV5PotentialTorsionLowerReadout (d : ℕ)
    (p A K theta k0 etaCap epsH v0 epsL2 : ℝ) : Prop :=
  ∀ (r j k : ℕ) (B E : Cube d) (centers : Finset (Vec d))
    (G : Finset (ℕ × Vec d)) (Pairs : Set (Cube d × Cube d)),
    B.2 = (3 : ℝ)^(-(r : ℤ)) →
    (r, B.1) ∈ G →
    (∀ x ∈ centers, (k, x) ∈ G) →
    (∀ x ∈ centers,
      ((x, (3 : ℝ)^(-((j + k : ℕ) : ℤ))), (x, (3 : ℝ)^(-(k : ℤ)))) ∈ Pairs) →
    cubeSet E ⊆ ⋃ x ∈ centers, cubeSet (x, (3 : ℝ)^(-((j + k : ℕ) : ℤ))) →
    (∀ x ∈ centers, cubeSet (x, (3 : ℝ)^(-((j + k : ℕ) : ℤ))) ⊆
      cubeSet (x, (3 : ℝ)^(-(k : ℤ)))) →
    (∀ x ∈ centers, cubeSet (x, (3 : ℝ)^(-(k : ℤ))) ⊆ cubeSet B) →
    (∀ x ∈ centers, cubeSet (x, (3 : ℝ)^(-(k : ℤ))) ⊆
      centeredAxisCube B.1 (theta * B.2)) →
    ((3 : ℝ)^(-(k : ℤ)))^2 ≤ etaCap / K * B.2^2 →
    (∀ x ∈ centers, ∀ (y : Vec d) (s : ℝ), 0 < s →
      ENNReal.ofReal v0 * volume (cubeSet (affineCubeTransport y s B)) ≤
        volume (cubeSet (affineCubeTransport y s
          (x, (3 : ℝ)^(-((j + k : ℕ) : ℤ)))))) →
    ∀ (M : GMCModel d) (J n : ℕ) (g : PotentialField d) (y : Vec d)
      (law : Kernel (Vec d) (Path d)) (massFraction : ℝ),
      2 * M.delta^2 * ((J : ℝ) + 1) ≤ Real.log 2 →
      LocalDiffusionData (fun x => Real.exp (g x)) (fun x => Real.exp (g x)) law →
      GoodCubeFiniteLocalTests (fun x => Real.exp (g x)) p A
        (if J ≤ n then ahom M n else 1) epsL2 epsH massFraction
        (Section7Process.timeScale (ahom M))
        (G.image (fun q => ((n : ℤ) - q.1, y + (3 : ℝ)^n • q.2)))
        (affinePairTransport y ((3 : ℝ)^n) '' Pairs) →
      ∀ x ∈ cubeSet (affineCubeTransport y ((3 : ℝ)^n) E),
        ENNReal.ofReal ((k0 / 2) * Section7Process.timeScale (ahom M)
          (affineCubeTransport y ((3 : ℝ)^n) B).2) ≤
          meanExit law (cubeSet (affineCubeTransport y ((3 : ℝ)^n) B)) x

/-- Exact coefficient representation lifts the deterministic reference readout. -/
theorem goodCubeV5_potential_torsion_lower_readout {d : ℕ}
    {p A K theta k0 etaCap epsH v0 epsL2 : ℝ}
    (h : GoodCubeReferenceTorsionLowerReadout d p A K theta k0 etaCap epsH v0 epsL2) :
    GoodCubeV5PotentialTorsionLowerReadout d p A K theta k0 etaCap epsH v0 epsL2 := by
  intro r j k B E centers G Pairs hB hG hAux hPairs hCover hNested hOuter hCentered
    hCap hVolume M J n g y law massFraction hBudget hDiff hTests
  have hcoef := goodCubeV5_readout_aCutoff_eq_exp M g n
  exact h r j k B E centers G Pairs hB hG hAux hPairs hCover hNested hOuter hCentered
    hCap hVolume M J n (goodCubeV5ReadoutSample M g) y law massFraction hBudget
    (by simpa only [hcoef] using hDiff) (by simpa only [hcoef] using hTests)

/-- The lower readout exists for arbitrary logarithmic coefficients with exactly
the same quantifier order and constants as the established cutoff readout. -/
theorem exists_goodCubeV5_potential_torsion_lower_readout_parameters
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (p A : ℝ) (hp : 2 < p) (hA : 1 ≤ A) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ theta : ℝ, 0 < theta → theta < 1 →
      ∃ k0 etaCap epsH : ℝ, 0 < k0 ∧ 0 < etaCap ∧ 0 < epsH ∧
      ∀ v0 : ℝ, 0 < v0 → ∃ epsL2 : ℝ, 0 < epsL2 ∧
        GoodCubeV5PotentialTorsionLowerReadout d p A K theta k0 etaCap epsH v0 epsL2 := by
  obtain ⟨K, hK, hOuter⟩ :=
    exists_goodCube_reference_torsion_lower_readout_parameters d hd p A hp hA
  refine ⟨K, hK, ?_⟩
  intro theta ht0 ht1
  obtain ⟨k0, etaCap, epsH, hk0, heta, hepsH, hInner⟩ := hOuter theta ht0 ht1
  refine ⟨k0, etaCap, epsH, hk0, heta, hepsH, ?_⟩
  intro v0 hv0
  obtain ⟨epsL2, hepsL2, hRead⟩ := hInner v0 hv0
  exact ⟨epsL2, hepsL2, goodCubeV5_potential_torsion_lower_readout hRead⟩

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
