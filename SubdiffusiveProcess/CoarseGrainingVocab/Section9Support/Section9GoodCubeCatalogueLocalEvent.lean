module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeCatalogueTests
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeHarmonicLocalEvent
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeFiniteLocalTests

@[expose] public section

/-!
# One coefficient-local event for the finite good-cube tests

The ambient catalogue event supplies Sobolev, torsion comparison, and all-pair
mass tests. The bounded-cardinality harmonic event supplies strict oscillation
contraction for the supplied common-scale pair catalogue. Absorbing their two
tails and using locality on the native parent produces one raw restricted
coefficient failure set, with the same probability bound at every lattice site.
The harmonic separation is chosen before the finite catalogue bounds.
-/

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open Set MeasureTheory Filter SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
attribute [local instance] Classical.propDecidable

/-- A common finite analytic and strict harmonic event is local to the actual
cutoff coefficient on the native parent, with the same tail at every lattice site. -/
theorem exists_goodCube_finite_catalogue_local_event
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ p A : ℝ, 2 < p ∧ 1 ≤ A ∧
      ∀ epsH : ℝ, 0 < epsH →
        ∃ j : ℕ, 2 ≤ j ∧
          ∀ (J N : ℕ) (eps : ℝ), 0 < eps →
            ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧
              ∀ M : GMCModel d, M.delta ≤ c →
              ∀ (n : ℕ) (G : Finset (ℕ × Vec d)), G.card ≤ N →
                (∀ q ∈ G, q.1 ≤ J) →
                (∀ q ∈ G, cubeSet (q.2, (3 : ℝ) ^ (-(q.1 : ℤ))) ⊆
                  cubeSet ((0 : Vec d), (1 : ℝ))) →
              ∀ (m : ℤ) (Pfam : Finset (Cube d × Cube d)), Pfam.card ≤ N →
                (∀ q ∈ Pfam,
                  0 < q.1.2 ∧ q.2.2 = (3 : ℝ) ^ m ∧
                  q.1.2 = (3 : ℝ) ^ (-(j : ℤ)) * q.2.2 ∧
                  cubeSet q.1 ⊆ SubdiffusiveProcess.Section9.centeredAxisCube q.2.1 (q.2.2 / 2)) →
                (∀ q ∈ Pfam, cubeSet q.2 ⊆ nativeBox n 1 (0 : Lattice d)) →
                ∃ bad : Set (nativeBox n 1 (0 : Lattice d) → ℝ),
                  (∀ z : Lattice d,
                    M.P.toMeasure (coefficientLocalBadEvent M n 1 bad z) ≤
                      ENNReal.ofReal (Real.exp
                        (-(c ^ 2 / (M.delta ^ 2 * (Real.log M.delta) ^ 2))))) ∧
                  ∀ (z : Lattice d) (omega : PotentialSample d),
                    omega ∉ coefficientLocalBadEvent M n 1 bad z →
                    GoodCubeFiniteLocalTests
                      (fun x => aCutoff M n omega (x + goodCubeCentre n z))
                      p A (if J ≤ n then ahom M n else 1) eps epsH
                      ((((3 : ℝ) ^ (-(J : ℤ))) ^ d) / 3)
                      (Section7Process.timeScale (ahom M))
                      (G.image (fun q => ((n : ℤ) - q.1, (3 : ℝ) ^ n • q.2)))
                      (Pfam : Set (Cube d × Cube d)) := by
  classical
  obtain ⟨p, A, hp, hA, hcatalogue⟩ := exists_goodCube_finite_catalogue_ambient_tests d hd
  refine ⟨p, A, hp, hA, ?_⟩
  intro epsH hepsH
  obtain ⟨j, hj, hharmonic⟩ := exists_goodCube_localHarmonicOscillation_bounded_card d epsH hepsH
  refine ⟨j, hj, ?_⟩
  intro J N eps heps
  obtain ⟨cC, hcC, _, hC⟩ := hcatalogue J N eps heps
  obtain ⟨cH, hcH, hcHC, _, hH⟩ := hharmonic N cC hcC
  obtain ⟨c, hc, hccH, hchalf, habsorb⟩ := goodCube_exists_finite_tail_absorption
    2 (cH ^ 2) cH (by norm_num) (sq_pos_of_pos hcH) hcH
  refine ⟨c, hc, hchalf, ?_⟩
  intro M hM n G hcard hdepth hinside m Pfam hPcard hPgeom hPinside
  obtain ⟨BadC, _, hBadC, hgoodC⟩ :=
    hC M (hM.trans (hccH.trans hcHC)) n G hcard hdepth hinside
  obtain ⟨BadH, _, hBadH, hgoodH⟩ :=
    hH M (hM.trans hccH) n m Pfam hPcard hPgeom
      (nativeBox n 1 (0 : Lattice d))
      (nativeBox_nonempty n (by norm_num : 0 < (1 : ℝ)) (0 : Lattice d)) hPinside
  let D : ℝ := M.delta ^ 2 * (Real.log M.delta) ^ 2
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hD : 0 < D := by
    have hlog : Real.log M.delta < 0 :=
      Real.log_neg hdelta ((hM.trans hchalf).trans_lt (by norm_num))
    exact mul_pos (sq_pos_of_pos hdelta) (sq_pos_of_ne_zero (ne_of_lt hlog))
  have hsq : cH ^ 2 ≤ cC ^ 2 := by nlinarith
  have hCdecay : ENNReal.ofReal (Real.exp (-(cC ^ 2 / D))) ≤
      ENNReal.ofReal (Real.exp (-(cH ^ 2 / D))) := by
    apply ENNReal.ofReal_le_ofReal
    exact Real.exp_le_exp.mpr (neg_le_neg (div_le_div_of_nonneg_right hsq hD.le))
  have hbound : M.P.toMeasure (BadC ∪ BadH) ≤
      ENNReal.ofReal (Real.exp (-(c ^ 2 / D))) := by
    calc M.P.toMeasure (BadC ∪ BadH)
        ≤ M.P.toMeasure BadC + M.P.toMeasure BadH := measure_union_le _ _
      _ ≤ ENNReal.ofReal (Real.exp (-(cH ^ 2 / D))) +
          ENNReal.ofReal (Real.exp (-(cH ^ 2 / D))) :=
        add_le_add (hBadC.trans hCdecay) hBadH
      _ = ENNReal.ofReal (2 * Real.exp (-(cH ^ 2 / D))) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        congr 1
        ring
      _ ≤ ENNReal.ofReal (Real.exp (-(c ^ 2 / D))) := by
        apply ENNReal.ofReal_le_ofReal
        simpa only [neg_div] using habsorb M.delta hdelta hM
  let Gn : Finset (ℤ × Vec d) :=
    G.image (fun q => ((n : ℤ) - q.1, (3 : ℝ) ^ n • q.2))
  let Tests : (Vec d → ℝ) → Prop := fun a =>
    GoodCubeFiniteLocalTests a p A (if J ≤ n then ahom M n else 1) eps epsH
      ((((3 : ℝ) ^ (-(J : ℤ))) ^ d) / 3)
      (Section7Process.timeScale (ahom M)) Gn (Pfam : Set (Cube d × Cube d))
  have hnative : nativeBox n 1 (0 : Lattice d) =
      cubeSet ((0 : Vec d), (3 : ℝ) ^ n) := by
    simp only [nativeBox, one_mul, goodCubeCentre_zero_lattice, cubeSet]
  have hGninside : ∀ q ∈ Gn,
      cubeSet (q.2, (3 : ℝ) ^ q.1) ⊆ nativeBox n 1 (0 : Lattice d) := by
    intro q hq
    obtain ⟨q0, hq0, rfl⟩ := Finset.mem_image.mp hq
    rw [hnative]
    exact goodCube_catalogue_cube_subset_parent n q0.1 q0.2 (hinside q0 hq0)
  have hlocal : ∀ a b : Vec d → ℝ,
      Set.EqOn a b (nativeBox n 1 (0 : Lattice d)) → (Tests a ↔ Tests b) := by
    intro a b hab
    exact goodCube_finiteLocalTests_congr_coeff hab p A
      (if J ≤ n then ahom M n else 1) eps epsH
      ((((3 : ℝ) ^ (-(J : ℤ))) ^ d) / 3)
      (Section7Process.timeScale (ahom M)) Gn (Pfam : Set (Cube d × Cube d))
      hGninside (fun q hq => hPinside q (Finset.mem_coe.mp hq))
  have hgood : ∀ omega, omega ∉ BadC ∪ BadH → Tests (aCutoff M n omega) := by
    intro omega homega
    have hnotC : omega ∉ BadC := fun h => homega (Or.inl h)
    have hnotH : omega ∉ BadH := fun h => homega (Or.inr h)
    obtain ⟨htests, hmass⟩ := hgoodC omega hnotC
    refine ⟨?_, ?_, ?_, hgoodH omega hnotH⟩
    · intro q hq
      obtain ⟨q0, hq0, rfl⟩ := Finset.mem_image.mp hq
      exact (htests q0 hq0).1
    · intro q hq
      obtain ⟨q0, hq0, rfl⟩ := Finset.mem_image.mp hq
      exact (htests q0 hq0).2
    · intro q hq r hr
      obtain ⟨q0, hq0, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨r0, hr0, rfl⟩ := Finset.mem_image.mp hr
      exact hmass q0 hq0 r0 hr0
  exact goodCube_exists_raw_local_test_event M n Tests hlocal (BadC ∪ BadH)
    hbound (ae_of_all _ hgood)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
