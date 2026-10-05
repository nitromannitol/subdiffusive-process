module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeV5Oscillation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeV5RobustTests

@[expose] public section




set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open Set MeasureTheory ProbabilityTheory MarkovProcess
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

variable {d : ℕ}

/-- Admissibility restricts to a smaller observation set with the same constant. -/
theorem admissibleMultiplier_mono {S T : Set (Vec d)} (hTS : T ⊆ S) {epsilon : ℝ}
    {theta : Vec d → ℝ} (h : GoodCubeV5AdmissibleMultiplier S epsilon theta) :
    GoodCubeV5AdmissibleMultiplier T epsilon theta := by
  obtain ⟨hc, hpos, k, hk, hk'⟩ := h
  exact ⟨hc.mono hTS, fun x hx => hpos x (hTS hx), k, hk, fun x hx => hk' x (hTS hx)⟩

/-- Admissibility with a smaller tolerance is admissibility with a larger one. -/
theorem admissibleMultiplier_mono_eps {S : Set (Vec d)} {epsilon epsilon' : ℝ}
    (hle : epsilon ≤ epsilon') {theta : Vec d → ℝ}
    (h : GoodCubeV5AdmissibleMultiplier S epsilon theta) :
    GoodCubeV5AdmissibleMultiplier S epsilon' theta := by
  obtain ⟨hc, hpos, k, hk, hk'⟩ := h
  exact ⟨hc, hpos, k, hk, fun x hx => (hk' x hx).trans hle⟩

/-- **Step H, one pair.** -/
theorem exists_pair_robustHarmonicOscillation (d : ℕ) :
    ∃ epsilonStar c C : ℝ, 0 < epsilonStar ∧ 0 < c ∧ 0 < C ∧
      ∀ eps0 : ℝ, 0 < eps0 → ∃ j2 : ℕ, 2 ≤ j2 ∧
        ∀ M : GMCModel d, M.delta ≤ c → ∀ (L : ℕ) (m : ℤ) (p : Cube d × Cube d),
          0 < p.1.2 → p.2.2 = (3 : ℝ) ^ m →
          p.1.2 = (3 : ℝ) ^ (-(j2 : ℤ)) * p.2.2 →
          cubeSet p.1 ⊆ centeredAxisCube p.2.1 (p.2.2 / 2) →
          ∃ bad : Set (PotentialSample d),
            M.P.toMeasure bad ≤ ENNReal.ofReal
              (C * Real.exp (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
            ∀ omega ∉ bad, ∀ (S : Set (Vec d)) (epsilon : ℝ),
              epsilon ≤ epsilonStar → cubeSet p.2 ⊆ S →
              ∀ theta : Vec d → ℝ, GoodCubeV5AdmissibleMultiplier S epsilon theta →
              ∀ h : Vec d → ℝ,
                WeakHarmonic (fun x => aCutoff M L omega x * theta x) (cubeSet p.2) h →
                  oscillation (cubeSet p.1) h ≤
                    ENNReal.ofReal eps0 * oscillation (cubeSet p.2) h := by
  obtain ⟨epsStar, c, C, hepsStar, hc, hC, hmain⟩ :=
    _root_.SubdiffusiveProcess.Section6.cutoff_holder_bounded_multiplier d
  refine ⟨epsStar, c, C, hepsStar, hc, hC, ?_⟩
  intro eps0 heps0
  obtain ⟨j, hj2, hjle⟩ := exists_depth_of_contraction C c eps0 hc heps0
  refine ⟨j + 1, by omega, ?_⟩
  intro M hdelta L m p hip houter hinner hhalf
  have hmid : IsMiddleHalfSubcube (m - 1) p.1.1 (j + 1 - 1) (cubeSet p.1) :=
    isMiddleHalfSubcube_window (by omega) hip houter hinner
  obtain ⟨bad, _, hbadmu, hbadmain⟩ :=
    hmain M hdelta L (m - 1) p.1.1 (j + 1 - 1) (by omega) (cubeSet p.1) hmid
  refine ⟨bad, hbadmu, ?_⟩
  intro omega hom S epsilon hepsle hpS theta hadm h hharm
  have hWS : translatedCube d (m - 1) p.1.1 ⊆ S :=
    (subset_closure.trans (closure_window_subset hip houter hhalf)).trans hpS
  obtain ⟨hthetaC, hthetaP, k, hk, hkb⟩ :=
    admissibleMultiplier_mono_eps hepsle (admissibleMultiplier_mono hWS hadm)
  refine oscillation_le_of_windowContraction (j2 := j + 1)
    (K := C * (3 : ℝ) ^ (-c * ((j + 1 - 1 : ℕ) : ℝ))) (by omega) hip houter hinner hhalf
    (by positivity) (by simpa using hjle) heps0 ?_ hharm
  intro u hu
  obtain ⟨hRep, hRepC, hRepAe, hRepOsc, -⟩ :=
    hbadmain omega hom theta hthetaC hthetaP ⟨k, hk, hkb⟩ u hu
  exact ⟨hRep, hRepC, hRepAe, hRepOsc⟩

/-- **Step H, a finite family of pairs.**  One bad event, chosen before the observation set,
the tolerance and the multiplier. -/
theorem exists_robustLocalHarmonicOscillation (d : ℕ) :
    ∃ epsilonStar c C : ℝ, 0 < epsilonStar ∧ 0 < c ∧ 0 < C ∧
      ∀ eps0 : ℝ, 0 < eps0 → ∃ j2 : ℕ, 2 ≤ j2 ∧
        ∀ M : GMCModel d, M.delta ≤ c → ∀ (L : ℕ) (m : ℤ)
          (Pfam : Finset (Cube d × Cube d)),
          (∀ p ∈ Pfam, 0 < p.1.2 ∧ p.2.2 = (3 : ℝ) ^ m ∧
            p.1.2 = (3 : ℝ) ^ (-(j2 : ℤ)) * p.2.2 ∧
            cubeSet p.1 ⊆ centeredAxisCube p.2.1 (p.2.2 / 2)) →
          ∃ bad : Set (PotentialSample d),
            M.P.toMeasure bad ≤ ENNReal.ofReal ((Pfam.card : ℝ) *
              (C * Real.exp (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2)))) ∧
            ∀ omega ∉ bad, ∀ (S : Set (Vec d)) (epsilon : ℝ), epsilon ≤ epsilonStar →
              (∀ p ∈ Pfam, cubeSet p.2 ⊆ S) →
              GoodCubeV5RobustHarmonicOscillation (aCutoff M L omega) S epsilon eps0
                (Pfam : Set (Cube d × Cube d)) := by
  classical
  obtain ⟨epsStar, c, C, hepsStar, hc, hC, hmain⟩ :=
    exists_pair_robustHarmonicOscillation d
  refine ⟨epsStar, c, C, hepsStar, hc, hC, ?_⟩
  intro eps0 heps0
  obtain ⟨j2, hj2, hpair⟩ := hmain eps0 heps0
  refine ⟨j2, hj2, ?_⟩
  intro M hdelta L m Pfam hPfam
  set X : ℝ := C * Real.exp (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2)) with hX
  have hchoice : ∀ p ∈ Pfam, ∃ bad : Set (PotentialSample d),
      M.P.toMeasure bad ≤ ENNReal.ofReal X ∧
      ∀ omega ∉ bad, ∀ (S : Set (Vec d)) (epsilon : ℝ),
        epsilon ≤ epsStar → cubeSet p.2 ⊆ S →
        ∀ theta : Vec d → ℝ, GoodCubeV5AdmissibleMultiplier S epsilon theta →
        ∀ h : Vec d → ℝ,
          WeakHarmonic (fun x => aCutoff M L omega x * theta x) (cubeSet p.2) h →
            oscillation (cubeSet p.1) h ≤
              ENNReal.ofReal eps0 * oscillation (cubeSet p.2) h := by
    intro p hp
    obtain ⟨hip, houter, hinner, hhalf⟩ := hPfam p hp
    exact hpair M hdelta L m p hip houter hinner hhalf
  choose! badOf hbadmu hbadmain using hchoice
  refine ⟨⋃ p ∈ Pfam, badOf p, ?_, ?_⟩
  · refine le_trans (measure_biUnion_finset_le _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun p hp => hbadmu p hp)) ?_
    have hcard : (0 : ℝ) ≤ (Pfam.card : ℝ) := by positivity
    rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul hcard,
      ENNReal.ofReal_natCast]
  · intro omega hom S epsilon hepsle hsub theta hadm
    refine ⟨fun p hp h hharm => ?_⟩
    have hp' : p ∈ Pfam := hp
    refine hbadmain p hp' omega (fun hmem => hom ?_) S epsilon hepsle (hsub p hp') theta hadm
      h hharm
    exact Set.mem_biUnion hp' hmem

/-- **Step H, with the family cardinality absorbed into the disorder threshold.** -/
theorem exists_goodCube_robustHarmonicOscillation_bounded_card (d : ℕ)
    (eps0 : ℝ) (heps0 : 0 < eps0) :
    ∃ epsilonStar : ℝ, 0 < epsilonStar ∧ ∃ j2 : ℕ, 2 ≤ j2 ∧ ∀ (N : ℕ) (b : ℝ), 0 < b →
      ∃ c : ℝ, 0 < c ∧ c ≤ b ∧ c ≤ 1 / 2 ∧
        ∀ M : GMCModel d, M.delta ≤ c → ∀ (L : ℕ) (m : ℤ)
          (Pfam : Finset (Cube d × Cube d)), Pfam.card ≤ N →
          (∀ p ∈ Pfam, 0 < p.1.2 ∧ p.2.2 = (3 : ℝ) ^ m ∧
            p.1.2 = (3 : ℝ) ^ (-(j2 : ℤ)) * p.2.2 ∧
            cubeSet p.1 ⊆ centeredAxisCube p.2.1 (p.2.2 / 2)) →
          ∃ bad : Set (PotentialSample d),
            M.P.toMeasure bad ≤ ENNReal.ofReal
              (Real.exp (-(c ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2)))) ∧
            ∀ omega ∉ bad, ∀ (S : Set (Vec d)) (epsilon : ℝ), epsilon ≤ epsilonStar →
              (∀ p ∈ Pfam, cubeSet p.2 ⊆ S) →
              GoodCubeV5RobustHarmonicOscillation (aCutoff M L omega) S epsilon eps0
                (Pfam : Set (Cube d × Cube d)) := by
  obtain ⟨epsStar, c0, C0, hepsStar, hc0, hC0, hEps⟩ :=
    exists_robustLocalHarmonicOscillation d
  refine ⟨epsStar, hepsStar, ?_⟩
  obtain ⟨j2, hj2, hMain⟩ := hEps eps0 heps0
  refine ⟨j2, hj2, ?_⟩
  intro N b hb
  obtain ⟨c, hcpos, hcmin, hc12, hTail⟩ :=
    goodCube_exists_finite_tail_absorption (((N : ℝ) + 1) * C0) c0 (min b c0)
      (by positivity) hc0 (lt_min hb hc0)
  have hcb : c ≤ b := hcmin.trans (min_le_left b c0)
  have hcc0 : c ≤ c0 := hcmin.trans (min_le_right b c0)
  refine ⟨c, hcpos, hcb, hc12, ?_⟩
  intro M hM L m Pfam hcard hFam
  obtain ⟨bad, hmeas2, hbad⟩ := hMain M (le_trans hM hcc0) L m Pfam hFam
  refine ⟨bad, ?_, hbad⟩
  rw [sq_abs] at hmeas2
  set e := Real.exp (-c0 / (M.delta ^ 2 * Real.log M.delta ^ 2)) with he_def
  have hexp : 0 < e := Real.exp_pos _
  have hC0e : 0 ≤ C0 * e := mul_nonneg (le_of_lt hC0) (le_of_lt hexp)
  have hcardle : (Pfam.card : ℕ) ≤ N + 1 := le_trans hcard (Nat.le_succ N)
  have hcard' : ((Pfam.card : ℝ)) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast hcardle
  have hstep : ((Pfam.card : ℝ)) * (C0 * e) ≤ (((N + 1 : ℕ) : ℝ)) * C0 * e := by
    calc ((Pfam.card : ℝ)) * (C0 * e) ≤ ((N + 1 : ℕ) : ℝ) * (C0 * e) :=
          mul_le_mul_of_nonneg_right hcard' hC0e
      _ = ((N + 1 : ℕ) : ℝ) * C0 * e := by ring
  have htail' := hTail M.delta M.shellPrefix.delta_pos hM
  have htail'' : (((N + 1 : ℕ) : ℝ)) * C0 * e ≤
      Real.exp (-(c ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2))) := by
    simpa only [Nat.cast_add, Nat.cast_one, e] using htail'
  exact hmeas2.trans (ENNReal.ofReal_le_ofReal (hstep.trans htail''))

/-- Translating the native box to the origin. -/
theorem mem_nativeBox_add_iff (n : ℕ) (z : Lattice d) (x : Vec d) :
    x + goodCubeCentre n z ∈ nativeBox n 1 z ↔ x ∈ nativeBox n 1 (0 : Lattice d) := by
  simp [nativeBox, mem_centeredAxisCube, goodCubeCentre_zero_lattice]

/-- Admissibility transports to the origin box along the site translation. -/
theorem admissibleMultiplier_translate {n : ℕ} {z : Lattice d} {epsilon : ℝ}
    {theta : Vec d → ℝ}
    (h : GoodCubeV5AdmissibleMultiplier (nativeBox n 1 z) epsilon theta) :
    GoodCubeV5AdmissibleMultiplier (nativeBox n 1 (0 : Lattice d)) epsilon
      (fun x => theta (x + goodCubeCentre n z)) := by
  obtain ⟨hc, hpos, k, hk, hkb⟩ := h
  have hmaps : Set.MapsTo (fun x : Vec d => x + goodCubeCentre n z)
      (nativeBox n 1 (0 : Lattice d)) (nativeBox n 1 z) :=
    fun x hx => (mem_nativeBox_add_iff n z x).mpr hx
  refine ⟨?_, fun x hx => hpos _ ((mem_nativeBox_add_iff n z x).mpr hx), k, hk,
    fun x hx => hkb _ ((mem_nativeBox_add_iff n z x).mpr hx)⟩
  exact hc.comp (Continuous.continuousOn (by fun_prop)) hmaps

/-- **Step H, exported.**  The reference pairs carry the *robust* strict contraction — the
contraction for every admissible multiplier at once — off one coefficient-local event with the
layer-zero tail.  The multiplier tolerance `epsilonStar` is the anchor's own, and
is fixed before the tolerance `eps0`, the template and the model. -/
theorem exists_goodCube_reference_robustOscillation_local_event
    (d : ℕ) (eps0 : ℝ) (heps0 : 0 < eps0) :
    ∃ epsilonStar : ℝ, 0 < epsilonStar ∧ ∃ j2 : ℕ, 2 ≤ j2 ∧
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
                  ∀ epsilon : ℝ, epsilon ≤ epsilonStar →
                    GoodCubeV5RobustHarmonicOscillation (aCutoff M n omega)
                      (nativeBox n 1 z) epsilon eps0
                      (goodCubeReferencePairs (PF : Set (Cube d × Cube d)) n z) := by
  classical
  obtain ⟨epsStar, hepsStar, j2, hj2, hmain⟩ :=
    exists_goodCube_robustHarmonicOscillation_bounded_card d eps0 heps0
  refine ⟨epsStar, hepsStar, j2, hj2, ?_⟩
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
            ∀ epsilon : ℝ, epsilon ≤ epsStar →
              GoodCubeV5RobustHarmonicOscillation (aCutoff M n omega)
                (nativeBox n 1 z) epsilon eps0
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
        rfl
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
      obtain ⟨Bad, hboundBad, hgoodBad⟩ :=
        hH M hM n ((n : ℤ) - (j1 : ℤ)) PFn hcard hshape
      set P : (Vec d → ℝ) → Prop := fun a =>
        ∀ theta : Vec d → ℝ,
          GoodCubeV5AdmissibleMultiplier (nativeBox n 1 (0 : Lattice d)) epsStar theta →
          LocalHarmonicOscillation (fun x => a x * theta x) eps0
            (PFn : Set (Cube d × Cube d)) with hPdef
      have hlocal : ∀ a c : Vec d → ℝ,
          Set.EqOn a c (nativeBox n 1 (0 : Lattice d)) → (P a ↔ P c) := by
        intro a c hac
        constructor
        · intro h theta hth
          exact (goodCube_localHarmonicOscillation_congr_coeff
            (a := fun x => a x * theta x) (b := fun x => c x * theta x)
            (fun x hx => by show a x * theta x = c x * theta x; rw [hac hx])
            (fun p hp => hinS p (Finset.mem_coe.mp hp))).mp (h theta hth)
        · intro h theta hth
          exact (goodCube_localHarmonicOscillation_congr_coeff
            (a := fun x => a x * theta x) (b := fun x => c x * theta x)
            (fun x hx => by show a x * theta x = c x * theta x; rw [hac hx])
            (fun p hp => hinS p (Finset.mem_coe.mp hp))).mpr (h theta hth)
      have hgoodBad' : ∀ omega ∉ Bad, P (aCutoff M n omega) := by
        intro omega hom theta hth
        exact hgoodBad omega hom (nativeBox n 1 (0 : Lattice d)) epsStar le_rfl hinS theta hth
      obtain ⟨badH, hbadmu, hbadgood⟩ :=
        goodCube_exists_raw_local_test_event M n P hlocal Bad hboundBad
          (ae_of_all _ hgoodBad')
      refine ⟨badH, fun _ => ⟨hbadmu, ?_⟩⟩
      intro z omega homega epsilon hepsle theta hadm
      have hth0 : GoodCubeV5AdmissibleMultiplier (nativeBox n 1 (0 : Lattice d)) epsStar
          (fun x => theta (x + goodCubeCentre n z)) :=
        admissibleMultiplier_mono_eps hepsle (admissibleMultiplier_translate hadm)
      have hres := hbadgood z omega homega _ hth0
      rw [hPFn, Finset.coe_image] at hres
      exact goodCube_localHarmonicOscillation_native_translate (goodCubeCentre n z) n
        (fun x => aCutoff M n omega x * theta x) eps0 (PF : Set (Cube d × Cube d)) hres
    · exact ⟨∅, fun hM' => absurd hM' hM⟩
  choose badH hbadH using key
  exact ⟨badH, fun M hM n => hbadH M n hM⟩

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
