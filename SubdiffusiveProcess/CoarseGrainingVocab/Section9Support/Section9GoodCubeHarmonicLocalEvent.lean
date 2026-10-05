module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeHarmonicBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.SevenACoefficientHull
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeCoefficientLocality
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeFiniteTail

@[expose] public section

/-!
# A coefficient-local strict harmonic contraction event

The proved full-shell estimate already bounds the failure probability for a
finite cube-pair family. Harmonic contraction is constant on fibres of the
restricted coefficient observation. Its raw failure set therefore has a
restricted-measurable hull with the same outer measure. This gives the same
tail and a pointwise conclusion outside a coefficient-local event.

Source: `mfd:in-deterministic` and `s.tightness`,
with the depth selected. This event covers the harmonic clause;
the mass and torsion tests require further estimates on a common event.
-/

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open Set MeasureTheory ProbabilityTheory MarkovProcess
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open scoped ENNReal NNReal
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder (restrictedCoefficientObservation)
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The full-shell harmonic estimate admits a coefficient-local bad event
without increasing its finite-family tail bound. -/
theorem exists_goodCube_localHarmonicOscillation_restricted_bad (d : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ eps0 : ℝ, 0 < eps0 → ∃ j2 : ℕ, 2 ≤ j2 ∧
        ∀ M : GMCModel d, M.delta ≤ c → ∀ (L : ℕ) (m : ℤ)
          (Pfam : Finset (Cube d × Cube d)),
          (∀ p ∈ Pfam, 0 < p.1.2 ∧ p.2.2 = (3 : ℝ) ^ m ∧
            p.1.2 = (3 : ℝ) ^ (-(j2 : ℤ)) * p.2.2 ∧
            cubeSet p.1 ⊆ centeredAxisCube p.2.1 (p.2.2 / 2)) →
          ∀ S : Set (Vec d), S.Nonempty →
          (∀ p ∈ Pfam, cubeSet p.2 ⊆ S) →
          ∃ bad : Set (PotentialSample d),
            MeasurableSet[restrictedCoefficientSigma (aCutoff M L) S] bad ∧
            M.P.toMeasure bad ≤ ENNReal.ofReal ((Pfam.card : ℝ) *
              (C * Real.exp (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2)))) ∧
            ∀ omega ∉ bad,
              LocalHarmonicOscillation (aCutoff M L omega) eps0
                (Pfam : Set (Cube d × Cube d)) := by
  obtain ⟨c, C, hc, hC, hmain⟩ := exists_localHarmonicOscillation d
  refine ⟨c, C, hc, hC, fun eps0 heps0 => ?_⟩
  obtain ⟨j2, hj2, hM⟩ := hmain eps0 heps0
  refine ⟨j2, hj2, fun M hMdelta L m Pfam hPfam S hSne hsub => ?_⟩
  obtain ⟨bad0, hbad0, hgood0⟩ := hM M hMdelta L m Pfam hPfam
  set P : PotentialSample d → Prop := fun omega =>
    LocalHarmonicOscillation (aCutoff M L omega) eps0 (Pfam : Set (Cube d × Cube d)) with hPdef
  have hlocal : ∀ ω ω' : PotentialSample d,
      restrictedCoefficientObservation (aCutoff M L) S ω =
        restrictedCoefficientObservation (aCutoff M L) S ω' → (P ω ↔ P ω') := by
    intro ω ω' hobs
    refine goodCube_localHarmonicOscillation_congr_coeff (S := S) ?_ ?_
    · intro x hx
      exact congrFun hobs ⟨x, hx⟩
    · intro p hp
      exact hsub p (Finset.mem_coe.mp hp)
  obtain ⟨raw, hraw⟩ := goodCube_exists_restricted_failure
    (restrictedCoefficientObservation (aCutoff M L) S) P hlocal
  have hsubraw : restrictedCoefficientObservation (aCutoff M L) S ⁻¹' raw ⊆ bad0 := by
    intro ω hω
    have hnP : ¬ P ω := by simpa only [hraw, mem_ofPred_eq] using! hω
    by_contra hcontra
    exact hnP (hgood0 ω hcontra)
  let : Nonempty S := hSne.to_subtype
  obtain ⟨E, hmeasE, hsubE, hmeasEq⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.exists_cutoff_local_measurable_hull M L S raw
  have hbound : M.P.toMeasure E ≤ ENNReal.ofReal ((Pfam.card : ℝ) *
      (C * Real.exp (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2)))) := by
    calc M.P.toMeasure E
        = M.P.toMeasure (restrictedCoefficientObservation (aCutoff M L) S ⁻¹' raw) := hmeasEq
      _ ≤ M.P.toMeasure bad0 := measure_mono hsubraw
      _ ≤ ENNReal.ofReal ((Pfam.card : ℝ) *
            (C * Real.exp (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2)))) := hbad0
  refine ⟨E, hmeasE, hbound, fun omega homegaE => ?_⟩
  by_contra hnP
  have hmem : omega ∈ restrictedCoefficientObservation (aCutoff M L) S ⁻¹' raw := by
    simpa only [hraw, mem_ofPred_eq, hPdef] using! hnP
  exact homegaE (hsubE hmem)

/-- For a fixed bound on the family cardinality, the prefactor is absorbed
by a disorder threshold chosen before the model, scale, family and window. -/
theorem exists_goodCube_localHarmonicOscillation_bounded_card (d : ℕ)
    (eps0 : ℝ) (heps0 : 0 < eps0) :
    ∃ j2 : ℕ, 2 ≤ j2 ∧ ∀ (N : ℕ) (b : ℝ), 0 < b →
      ∃ c : ℝ, 0 < c ∧ c ≤ b ∧ c ≤ 1 / 2 ∧
        ∀ M : GMCModel d, M.delta ≤ c → ∀ (L : ℕ) (m : ℤ)
          (Pfam : Finset (Cube d × Cube d)), Pfam.card ≤ N →
          (∀ p ∈ Pfam, 0 < p.1.2 ∧ p.2.2 = (3 : ℝ) ^ m ∧
            p.1.2 = (3 : ℝ) ^ (-(j2 : ℤ)) * p.2.2 ∧
            cubeSet p.1 ⊆ centeredAxisCube p.2.1 (p.2.2 / 2)) →
          ∀ S : Set (Vec d), S.Nonempty →
          (∀ p ∈ Pfam, cubeSet p.2 ⊆ S) →
          ∃ bad : Set (PotentialSample d),
            MeasurableSet[restrictedCoefficientSigma (aCutoff M L) S] bad ∧
            M.P.toMeasure bad ≤ ENNReal.ofReal
              (Real.exp (-(c ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2)))) ∧
            ∀ omega ∉ bad,
              LocalHarmonicOscillation (aCutoff M L omega) eps0
                (Pfam : Set (Cube d × Cube d)) := by
  obtain ⟨c0, C0, hc0, hC0, hEps⟩ :=
    exists_goodCube_localHarmonicOscillation_restricted_bad d
  obtain ⟨j2, hj2, hMain⟩ := hEps eps0 heps0
  refine ⟨j2, hj2, ?_⟩
  intro N b hb
  obtain ⟨c, hcpos, hcmin, hc12, hTail⟩ :=
    goodCube_exists_finite_tail_absorption (((N : ℝ) + 1) * C0) c0 (min b c0)
      (by positivity) hc0 (lt_min hb hc0)
  have hcb : c ≤ b := hcmin.trans (min_le_left b c0)
  have hcc0 : c ≤ c0 := hcmin.trans (min_le_right b c0)
  refine ⟨c, hcpos, hcb, hc12, ?_⟩
  intro M hM L m Pfam hcard hFam S hS hsub
  obtain ⟨bad, hmeas, hmeas2, hbad⟩ :=
    hMain M (le_trans hM hcc0) L m Pfam hFam S hS hsub
  refine ⟨bad, hmeas, ?_, hbad⟩
  rw [sq_abs] at hmeas2
  set e := Real.exp (-c0 / (M.delta ^ 2 * Real.log M.delta ^ 2)) with he_def
  have hexp : 0 < e := Real.exp_pos _
  have hC0e : 0 ≤ C0 * e := mul_nonneg (le_of_lt hC0) (le_of_lt hexp)
  have hcardle : (Pfam.card : ℕ) ≤ N + 1 := le_trans hcard (Nat.le_succ N)
  have hcard' : ((Pfam.card : ℝ)) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast hcardle
  have hstep : ((Pfam.card : ℝ)) * (C0 * e) ≤
      (((N + 1 : ℕ) : ℝ)) * C0 * e := by
    calc ((Pfam.card : ℝ)) * (C0 * e) ≤
        ((N + 1 : ℕ) : ℝ) * (C0 * e) :=
          mul_le_mul_of_nonneg_right hcard' hC0e
      _ = ((N + 1 : ℕ) : ℝ) * C0 * e := by ring
  have htail' := hTail M.delta M.shellPrefix.delta_pos hM
  have htail'' : (((N + 1 : ℕ) : ℝ)) * C0 * e ≤
      Real.exp (-(c ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2))) := by
    simpa only [Nat.cast_add, Nat.cast_one, e] using htail'
  exact hmeas2.trans (ENNReal.ofReal_le_ofReal (hstep.trans htail''))

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
