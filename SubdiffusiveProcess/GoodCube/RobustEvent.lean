import SubdiffusiveProcess.GoodCube.RobustTests




open Homogenization hiding Vec cubeSet
open MeasureTheory Set Filter
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation (Lattice)
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Opus55

variable {d : ℕ}

theorem nativeBox_zero_eq_cubeSet (n : ℕ) :
    nativeBox n 1 (0 : Lattice d) = cubeSet ((0 : Vec d), (3 : ℝ) ^ n) := by
  simp only [nativeBox, one_mul, goodCubeCentre_zero_lattice, cubeSet]

/-- **The robust catalogue local event.** -/
theorem exists_goodCube_finite_catalogue_local_event_robust
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ p A : ℝ, 2 < p ∧ 1 ≤ A ∧
      ∀ epsH : ℝ, 0 < epsH →
        ∃ j : ℕ, 2 ≤ j ∧
          ∀ (J N : ℕ) (eps : ℝ), 0 < eps →
            ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 / 4 ∧
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
                    GoodCubeV5RobustFiniteLocalTests
                      (fun x => aCutoff M n omega (x + goodCubeCentre n z))
                      (nativeBox n 1 (0 : Lattice d)) epsilon
                      p A (if J ≤ n then ahom M n else 1) eps epsH
                      ((((3 : ℝ) ^ (-(J : ℤ))) ^ d) / 9)
                      (Section7Process.timeScale (ahom M))
                      (G.image (fun q => ((n : ℤ) - q.1, (3 : ℝ) ^ n • q.2)))
                      (Pfam : Set (Cube d × Cube d)) := by
  classical
  obtain ⟨p, A, hp, hA, hcatalogue⟩ := exists_goodCube_finite_catalogue_ambient_tests_robust d hd
  refine ⟨p, A, hp, hA, ?_⟩
  intro epsH hepsH
  obtain ⟨epsStar, hepsStar, j, hj, hharmonic⟩ :=
    exists_goodCube_robustHarmonicOscillation_bounded_card d epsH hepsH
  refine ⟨j, hj, ?_⟩
  intro J N eps heps
  obtain ⟨epsC, hepsC, hepsC4, cC, hcC, _, hC⟩ := hcatalogue J N eps heps
  refine ⟨min epsC epsStar, lt_min hepsC hepsStar, (min_le_left _ _).trans hepsC4, ?_⟩
  obtain ⟨cH, hcH, hcHC, _, hH⟩ := hharmonic N cC hcC
  obtain ⟨c, hc, hccH, hchalf, habsorb⟩ := goodCube_exists_finite_tail_absorption
    2 (cH ^ 2) cH (by norm_num) (sq_pos_of_pos hcH) hcH
  refine ⟨c, hc, hchalf, ?_⟩
  intro M hM n G hcard hdepth hinside m Pfam hPcard hPgeom hPinside
  obtain ⟨BadC, _, hBadC, hgoodC⟩ :=
    hC M (hM.trans (hccH.trans hcHC)) n G hcard hdepth hinside
  obtain ⟨BadH, hBadH, hgoodH⟩ := hH M (hM.trans hccH) n m Pfam hPcard hPgeom
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
  let S0 : Set (Vec d) := nativeBox n 1 (0 : Lattice d)
  let Tests : (Vec d → ℝ) → Prop := fun a =>
    GoodCubeV5RobustFiniteLocalTests a S0 (min epsC epsStar)
      p A (if J ≤ n then ahom M n else 1) eps epsH
      ((((3 : ℝ) ^ (-(J : ℤ))) ^ d) / 9)
      (Section7Process.timeScale (ahom M)) Gn (Pfam : Set (Cube d × Cube d))
  have hnative : S0 = cubeSet ((0 : Vec d), (3 : ℝ) ^ n) := nativeBox_zero_eq_cubeSet n
  have hGninside : ∀ q ∈ Gn, cubeSet (q.2, (3 : ℝ) ^ q.1) ⊆ S0 := by
    intro q hq
    obtain ⟨q0, hq0, rfl⟩ := Finset.mem_image.mp hq
    rw [hnative]
    exact goodCube_catalogue_cube_subset_parent n q0.1 q0.2 (hinside q0 hq0)
  have hlocal : ∀ a b : Vec d → ℝ, Set.EqOn a b S0 → (Tests a ↔ Tests b) := by
    intro a b hab
    exact goodCubeV5RobustFiniteLocalTests_congr_coeff hab (min epsC epsStar) p A
      (if J ≤ n then ahom M n else 1) eps epsH
      ((((3 : ℝ) ^ (-(J : ℤ))) ^ d) / 9)
      (Section7Process.timeScale (ahom M)) Gn (Pfam : Set (Cube d × Cube d))
      hGninside (fun q hq => hPinside q (Finset.mem_coe.mp hq))
  have hgood : ∀ omega, omega ∉ BadC ∪ BadH → Tests (aCutoff M n omega) := by
    intro omega homega th hadm
    have hnotC : omega ∉ BadC := fun h => homega (Or.inl h)
    have hnotH : omega ∉ BadH := fun h => homega (Or.inr h)
    have hadmC : GoodCubeV5AdmissibleMultiplier (cubeSet ((0 : Vec d), (3 : ℝ) ^ n)) epsC th := by
      rw [← hnative]
      exact admissibleMultiplier_mono_eps (min_le_left _ _) hadm
    obtain ⟨htests, hmass⟩ := hgoodC omega hnotC th hadmC
    refine ⟨?_, ?_, ?_, ?_⟩
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
    · exact hgoodH omega hnotH S0 (min epsC epsStar) (min_le_right _ _) hPinside th hadm
  exact goodCube_exists_raw_local_test_event M n Tests hlocal (BadC ∪ BadH)
    hbound (ae_of_all _ hgood)

/-! ## Transport of the robust tests to the site -/

/-- The robust tests of the recentred coefficient on the origin box give the robust tests of
the coefficient itself on the site box, for the site family. -/
theorem robustFiniteLocalTests_native_translate (n : ℕ) (z : Lattice d)
    (a : Vec d → ℝ) (ha : Continuous a) {epsilon p A sigma eps epsH mf : ℝ} (hp : 0 < p)
    (clock : ℝ → ℝ) (G : Finset (ℕ × Vec d)) (Pairs : Set (Cube d × Cube d))
    (hGin : ∀ q ∈ G.image (fun q => ((n : ℤ) - q.1, goodCubeCentre n z + (3 : ℝ) ^ n • q.2)),
      cubeSet (q.2, (3 : ℝ) ^ q.1) ⊆ nativeBox n 1 z)
    (hPin : ∀ q ∈ affinePairTransport (goodCubeCentre n z) ((3 : ℝ) ^ n) '' Pairs,
      cubeSet q.2 ⊆ nativeBox n 1 z)
    (h : GoodCubeV5RobustFiniteLocalTests (fun x => a (x + goodCubeCentre n z))
      (nativeBox n 1 (0 : Lattice d)) epsilon p A sigma eps epsH mf clock
      (G.image (fun q => ((n : ℤ) - q.1, (3 : ℝ) ^ n • q.2)))
      (affinePairTransport (0 : Vec d) ((3 : ℝ) ^ n) '' Pairs)) :
    GoodCubeV5RobustFiniteLocalTests a (nativeBox n 1 z) epsilon p A sigma eps epsH mf clock
      (G.image (fun q => ((n : ℤ) - q.1, goodCubeCentre n z + (3 : ℝ) ^ n • q.2)))
      (affinePairTransport (goodCubeCentre n z) ((3 : ℝ) ^ n) '' Pairs) := by
  classical
  intro th hadm
  set S := nativeBox n 1 z with hS
  have hSopen : IsOpen S := isOpen_centeredAxisCube _ _
  let th' : Vec d → ℝ := S.piecewise th (fun _ => 1)
  have hEq : Set.EqOn th th' S := fun x hx => by simp [th', Set.piecewise_eq_of_mem _ _ _ hx]
  have hth'meas : Measurable th' :=
    hadm.1.measurable_piecewise continuous_const.continuousOn hSopen.measurableSet
  have hadm' : GoodCubeV5AdmissibleMultiplier S epsilon th' := by
    obtain ⟨hc, hpos, k, hk, hkb⟩ := hadm
    refine ⟨hc.congr (fun x hx => (hEq hx).symm), fun x hx => ?_, k, hk, fun x hx => ?_⟩
    · rw [← hEq hx]; exact hpos x hx
    · rw [← hEq hx]; exact hkb x hx
  have hadm0 := admissibleMultiplier_translate hadm'
  have h0 := h _ hadm0
  have hprod : Measurable (fun x => a x * th' x) := ha.measurable.mul hth'meas
  have hT := goodCube_finiteLocalTests_native_translate (goodCubeCentre n z) n
    (fun x => a x * th' x) hprod p A sigma eps epsH mf hp clock G Pairs h0
  refine (goodCube_finiteLocalTests_congr_coeff (S := S) ?_ p A sigma eps epsH mf clock _ _
    hGin hPin).mp hT
  intro x hx
  simp only [← hEq hx]

/-- **The robust reference catalogue event family.** -/
theorem exists_goodCube_reference_catalogue_event_family_robust
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ p A : ℝ, 2 < p ∧ 1 ≤ A ∧
      ∀ epsH : ℝ, 0 < epsH →
        ∃ j : ℕ, 2 ≤ j ∧
          ∀ (J N : ℕ) (eps : ℝ), 0 < eps →
            ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 / 4 ∧
            ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧
              ∀ G : Finset (ℕ × Vec d), G.card ≤ N →
                (∀ q ∈ G, q.1 ≤ J) →
                (∀ q ∈ G, cubeSet (q.2, (3 : ℝ) ^ (-(q.1 : ℤ))) ⊆
                  cubeSet ((0 : Vec d), (1 : ℝ))) →
              ∀ (k : ℕ) (X : Finset (Vec d)),
                (∀ x ∈ X, cubeSet (x, (3 : ℝ) ^ (-(k : ℤ))) ⊆
                  cubeSet ((0 : Vec d), (1 : ℝ))) →
                (goodCubeAuxiliaryPairs X j (-(k : ℤ))).card ≤ N →
                ∃ bad : (M : GMCModel d) → (n : ℕ) →
                  Set (nativeBox n 1 (0 : Lattice d) → ℝ),
                  ∀ M : GMCModel d, M.delta ≤ c → ∀ n : ℕ,
                    (∀ z : Lattice d,
                      M.P.toMeasure (coefficientLocalBadEvent M n 1 (bad M n) z) ≤
                        ENNReal.ofReal (Real.exp
                          (-(c ^ 2 / (M.delta ^ 2 * (Real.log M.delta) ^ 2))))) ∧
                    ∀ (z : Lattice d) (omega : PotentialSample d),
                      omega ∉ coefficientLocalBadEvent M n 1 (bad M n) z →
                      GoodCubeV5RobustFiniteLocalTests (aCutoff M n omega) (nativeBox n 1 z)
                        epsilon p A (if J ≤ n then ahom M n else 1) eps epsH
                        ((((3 : ℝ) ^ (-(J : ℤ))) ^ d) / 9)
                        (Section7Process.timeScale (ahom M))
                        (G.image (fun q => ((n : ℤ) - q.1,
                          goodCubeCentre n z + (3 : ℝ) ^ n • q.2)))
                        (affinePairTransport (goodCubeCentre n z) ((3 : ℝ)^n) ''
                          (goodCubeAuxiliaryPairs X j (-(k : ℤ)) : Set (Cube d × Cube d))) := by
  classical
  obtain ⟨p, A, hp2, hA, hloc⟩ := exists_goodCube_finite_catalogue_local_event_robust d hd
  refine ⟨p, A, hp2, hA, ?_⟩
  intro epsH hepsH
  obtain ⟨j, hj, hloc⟩ := hloc epsH hepsH
  refine ⟨j, hj, ?_⟩
  intro J N eps heps
  obtain ⟨epsilon, hepsilon, hepsilon4, c, hc, hcHalf, huse⟩ := hloc J N eps heps
  refine ⟨epsilon, hepsilon, hepsilon4, c, hc, hcHalf, ?_⟩
  intro G hGcard hGdepth hGinside k X hX hPcard
  have hp : 0 < p := lt_trans (by norm_num : (0 : ℝ) < 2) hp2
  have hj1 : 1 ≤ j := le_trans (by norm_num : (1 : ℕ) ≤ 2) hj
  have key : ∀ (M : GMCModel d) (n : ℕ),
      ∃ bad : Set (nativeBox n 1 (0 : Lattice d) → ℝ),
      M.delta ≤ c →
        (∀ z : Lattice d,
          M.P.toMeasure (coefficientLocalBadEvent M n 1 bad z) ≤
            ENNReal.ofReal (Real.exp
              (-(c ^ 2 / (M.delta ^ 2 * (Real.log M.delta) ^ 2))))) ∧
        ∀ (z : Lattice d) (omega : PotentialSample d),
          omega ∉ coefficientLocalBadEvent M n 1 bad z →
          GoodCubeV5RobustFiniteLocalTests (aCutoff M n omega) (nativeBox n 1 z)
            epsilon p A (if J ≤ n then ahom M n else 1) eps epsH
            ((((3 : ℝ) ^ (-(J : ℤ))) ^ d) / 9)
            (Section7Process.timeScale (ahom M))
            (G.image (fun q => ((n : ℤ) - q.1,
              goodCubeCentre n z + (3 : ℝ) ^ n • q.2)))
            (affinePairTransport (goodCubeCentre n z) ((3 : ℝ) ^ n) ''
              (goodCubeAuxiliaryPairs X j (-(k : ℤ)) : Set (Cube d × Cube d))) := by
    intro M n
    obtain ⟨hcard, hprop⟩ :=
      goodCube_auxiliary_pair_catalog_native X j k hj1 hX n (0 : Vec d)
    have hPcardN : ((goodCubeAuxiliaryPairs X j (-(k : ℤ))).image
        (affinePairTransport (0 : Vec d) ((3 : ℝ) ^ n))).card ≤ N := hcard.le.trans hPcard
    have hgeom : ∀ q ∈ (goodCubeAuxiliaryPairs X j (-(k : ℤ))).image
        (affinePairTransport (0 : Vec d) ((3 : ℝ) ^ n)),
        0 < q.1.2 ∧ q.2.2 = (3 : ℝ) ^ (((n : ℤ) - k)) ∧
        q.1.2 = (3 : ℝ) ^ (-(j : ℤ)) * q.2.2 ∧
        cubeSet q.1 ⊆ SubdiffusiveProcess.Section9.centeredAxisCube q.2.1 (q.2.2 / 2) := by
      intro q hq
      obtain ⟨h0, h1, h2, h3, -, -⟩ := hprop q hq
      exact ⟨h0, h1, h2, subset_closure.trans h3⟩
    have hparent : ∀ q ∈ (goodCubeAuxiliaryPairs X j (-(k : ℤ))).image
        (affinePairTransport (0 : Vec d) ((3 : ℝ) ^ n)),
        cubeSet q.2 ⊆ nativeBox n 1 (0 : Lattice d) := by
      intro q hq
      obtain ⟨-, -, -, -, h4, -⟩ := hprop q hq
      rw [nativeBox_zero_eq_cubeSet]
      exact h4
    by_cases hM : M.delta ≤ c
    · obtain ⟨bad, hbad, htests⟩ :=
        huse M hM n G hGcard hGdepth hGinside ((n : ℤ) - k)
          ((goodCubeAuxiliaryPairs X j (-(k : ℤ))).image
            (affinePairTransport (0 : Vec d) ((3 : ℝ) ^ n)))
          hPcardN hgeom hparent
      refine ⟨bad, fun _ => ⟨hbad, ?_⟩⟩
      intro z omega homega
      have hT := htests z omega homega
      rw [Finset.coe_image] at hT
      refine robustFiniteLocalTests_native_translate n z (aCutoff M n omega)
        (continuous_aCutoff M n omega) hp (Section7Process.timeScale (ahom M)) G
        (goodCubeAuxiliaryPairs X j (-(k : ℤ)) : Set (Cube d × Cube d)) ?_ ?_ hT
      · intro q hq
        obtain ⟨q0, hq0, rfl⟩ := Finset.mem_image.mp hq
        have h := goodCube_catalogue_cube_subset_parent n q0.1 q0.2 (hGinside q0 hq0)
        have hmaps := (goodCube_cubeSet_add_eq_translateSet
          ((3 : ℝ) ^ n • q0.2, (3 : ℝ) ^ ((n : ℤ) - q0.1)) (goodCubeCentre n z))
        intro x hx
        have hx' : x ∈ cubeSet ((3 : ℝ) ^ n • q0.2 + goodCubeCentre n z,
            (3 : ℝ) ^ ((n : ℤ) - q0.1)) := by
          simpa only [add_comm] using hx
        rw [hmaps] at hx'
        obtain ⟨y, hy, rfl⟩ := (Homogenization.image_addRight_eq_translateSet _ _).symm ▸ hx'
        exact (mem_nativeBox_add_iff n z y).mpr (by
          rw [nativeBox_zero_eq_cubeSet]; exact h hy)
      · intro q hq
        obtain ⟨q0, hq0, rfl⟩ := hq
        obtain ⟨-, -, -, -, h4, -⟩ := goodCube_auxiliary_pair_catalog_native X j k hj1 hX n
          (goodCubeCentre n z) |>.2 _ (Finset.mem_image_of_mem _ hq0)
        refine h4.trans ?_
        simp only [nativeBox, one_mul, cubeSet]
        exact subset_rfl
    · exact ⟨∅, fun hM' => absurd hM' hM⟩
  choose bad hbad using key
  exact ⟨bad, fun M hM n => hbad M n hM⟩

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Opus55


