import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeHarmonicLocalEvent
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeLocalTestEvent
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeFiniteTestTranslation
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeReferenceTemplate




set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open MeasureTheory Set Filter
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
attribute [local instance] Classical.propDecidable

/-- Strict oscillation contraction transports from the native origin family to
every lattice site, exactly as the full finite test package does. -/
theorem goodCube_localHarmonicOscillation_native_translate
    {d : ℕ} (y : Vec d) (n : ℕ) (a : Vec d → ℝ) (eps : ℝ)
    (Pairs : Set (Cube d × Cube d))
    (h : LocalHarmonicOscillation (fun x => a (x + y)) eps
      (affinePairTransport (0 : Vec d) ((3 : ℝ) ^ n) '' Pairs)) :
    LocalHarmonicOscillation a eps
      (affinePairTransport y ((3 : ℝ) ^ n) '' Pairs) := by
  have ht : LocalHarmonicOscillation a eps
      ((fun q : Cube d × Cube d => ((q.1.1 + y, q.1.2), (q.2.1 + y, q.2.2))) ''
        (affinePairTransport (0 : Vec d) ((3 : ℝ) ^ n) '' Pairs)) := by
    refine ⟨?_⟩
    intro pair hpair f hf
    obtain ⟨q, hq, rfl⟩ := hpair
    rw [goodCube_cubeSet_add_eq_translateSet q.2 y] at hf
    have h1 := goodCube_harmonicContraction_translate y (cubeSet q.1) (cubeSet q.2) a eps
      (h.contraction q hq) f hf
    rw [goodCube_cubeSet_add_eq_translateSet q.1 y, goodCube_cubeSet_add_eq_translateSet q.2 y]
    exact h1
  simpa only [Set.image_image, affinePairTransport, affineCubeTransport,
    zero_add, add_zero, Function.comp_def, add_comm] using ht

/-- **The exported reference pairs carry the strict contraction off one
coefficient-local event with the frozen layer-zero tail.**

The inner depth `j2` depends only on the requested tolerance `eps0` and on the
dimension; the cardinality bound `N` and the disorder threshold `cH` are chosen
after it and still before the model, the scale and the site.  No geometry other
than the exported template is quantified over. -/
theorem exists_goodCube_reference_oscillation_local_event
    (d : ℕ) (eps0 : ℝ) (heps0 : 0 < eps0) :
    ∃ j2 : ℕ, 2 ≤ j2 ∧
      ∀ (N : ℕ) (b : ℝ), 0 < b →
        ∃ cH : ℝ, 0 < cH ∧ cH ≤ b ∧ cH ≤ 1 / 2 ∧
          ∀ (j1 : ℕ) (grid0 : Finset (Vec d)) (PF : Finset (Cube d × Cube d))
            (Qfam0 Afam0 : Set (Cube d)), PF.card ≤ N →
            (∀ (n : ℕ) (z : Lattice d),
              IsLocalCubeGeometry grid0 j1 j2 (goodCubeCentre n z, (3 : ℝ) ^ n)
                (goodCubeReferencePairs (PF : Set (Cube d × Cube d)) n z)
                (goodCubeReferenceFamily Qfam0 n z)
                (goodCubeReferenceFamily Afam0 n z)) →
            ∃ badH : (M : GMCModel d) → (n : ℕ) →
                Set (nativeBox n 1 (0 : Lattice d) → ℝ),
              ∀ M : GMCModel d, M.delta ≤ cH → ∀ n : ℕ,
                (∀ z : Lattice d,
                  M.P.toMeasure (coefficientLocalBadEvent M n 1 (badH M n) z) ≤
                    ENNReal.ofReal (Real.exp
                      (-(cH ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2))))) ∧
                ∀ (z : Lattice d) (omega : PotentialSample d),
                  omega ∉ coefficientLocalBadEvent M n 1 (badH M n) z →
                  LocalHarmonicOscillation (aCutoff M n omega) eps0
                    (goodCubeReferencePairs (PF : Set (Cube d × Cube d)) n z) := by
  classical
  obtain ⟨j2, hj2, hmain⟩ :=
    exists_goodCube_localHarmonicOscillation_bounded_card d eps0 heps0
  refine ⟨j2, hj2, ?_⟩
  intro N b hb
  obtain ⟨cH, hcH, hcb, hc12, hH⟩ := hmain N b hb
  refine ⟨cH, hcH, hcb, hc12, ?_⟩
  intro j1 grid0 PF Qfam0 Afam0 hPcard hgeom
  have key : ∀ (M : GMCModel d) (n : ℕ),
      ∃ badH : Set (nativeBox n 1 (0 : Lattice d) → ℝ),
        M.delta ≤ cH →
          (∀ z : Lattice d,
            M.P.toMeasure (coefficientLocalBadEvent M n 1 badH z) ≤
              ENNReal.ofReal (Real.exp
                (-(cH ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2))))) ∧
          ∀ (z : Lattice d) (omega : PotentialSample d),
            omega ∉ coefficientLocalBadEvent M n 1 badH z →
            LocalHarmonicOscillation (aCutoff M n omega) eps0
              (goodCubeReferencePairs (PF : Set (Cube d × Cube d)) n z) := by
    intro M n
    by_cases hM : M.delta ≤ cH
    · set PFn : Finset (Cube d × Cube d) :=
        PF.image (affinePairTransport (0 : Vec d) ((3 : ℝ) ^ n)) with hPFn
      have hcoe : (PFn : Set (Cube d × Cube d))
          = goodCubeReferencePairs (PF : Set (Cube d × Cube d)) n (0 : Lattice d) := by
        rw [hPFn, Finset.coe_image]
        simp only [affinePairTransport, affineCubeTransport,
          goodCubeReferencePairs, goodCubeReferenceTransport,
          goodCubeCentre_zero_lattice]
      have hgeo0 := hgeom n (0 : Lattice d)
      rw [← hcoe] at hgeo0
      have hcard : PFn.card ≤ N := (Finset.card_image_le).trans hPcard
      have hshape : ∀ p ∈ PFn, 0 < p.1.2 ∧ p.2.2 = (3 : ℝ) ^ ((n : ℤ) - (j1 : ℤ)) ∧
          p.1.2 = (3 : ℝ) ^ (-(j2 : ℤ)) * p.2.2 ∧
          cubeSet p.1 ⊆ SubdiffusiveProcess.Section9.centeredAxisCube p.2.1 (p.2.2 / 2) := by
        intro p hp
        have hpP : p ∈ (PFn : Set (Cube d × Cube d)) := hp
        refine ⟨hgeo0.side_pos p.1 (hgeo0.pair_mem p hpP).1, ?_,
          hgeo0.pair_inner_side p hpP, hgeo0.pair_middle_half p hpP⟩
        have hout := hgeo0.pair_outer_side p hpP
        rw [hout]
        rw [← zpow_natCast (3 : ℝ) n, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
        congr 1
        ring
      have hinS : ∀ p ∈ PFn, cubeSet p.2 ⊆ nativeBox n 1 (0 : Lattice d) := by
        intro p hp
        have hpP : p ∈ (PFn : Set (Cube d × Cube d)) := hp
        refine (hgeo0.pair_in_half p hpP).trans ?_
        have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
        simp only [nativeBox, one_mul]
        exact centeredAxisCube_mono (by linarith)
      obtain ⟨Bad, _hmeasBad, hboundBad, hgoodBad⟩ :=
        hH M hM n ((n : ℤ) - (j1 : ℤ)) PFn hcard hshape
          (nativeBox n 1 (0 : Lattice d))
          (nativeBox_nonempty n (by norm_num : (0 : ℝ) < 1) (0 : Lattice d)) hinS
      have hlocal : ∀ a c : Vec d → ℝ,
          Set.EqOn a c (nativeBox n 1 (0 : Lattice d)) →
          (LocalHarmonicOscillation a eps0 (PFn : Set (Cube d × Cube d)) ↔
            LocalHarmonicOscillation c eps0 (PFn : Set (Cube d × Cube d))) := by
        intro a c hac
        exact goodCube_localHarmonicOscillation_congr_coeff hac
          (fun p hp => hinS p (Finset.mem_coe.mp hp))
      obtain ⟨badH, hbadmu, hbadgood⟩ :=
        goodCube_exists_raw_local_test_event M n
          (fun a => LocalHarmonicOscillation a eps0 (PFn : Set (Cube d × Cube d)))
          hlocal Bad hboundBad (ae_of_all _ hgoodBad)
      refine ⟨badH, fun _ => ⟨hbadmu, ?_⟩⟩
      intro z omega homega
      have hres := hbadgood z omega homega
      rw [hPFn, Finset.coe_image] at hres
      exact goodCube_localHarmonicOscillation_native_translate (goodCubeCentre n z) n
        (aCutoff M n omega) eps0 (PF : Set (Cube d × Cube d)) hres
    · exact ⟨∅, fun hM' => absurd hM' hM⟩
  choose badH hbadH using key
  exact ⟨badH, fun M hM n => hbadH M n hM⟩

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
