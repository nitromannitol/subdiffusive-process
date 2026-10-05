module

public import SubdiffusiveProcess.GoodCube.RobustReadout

@[expose] public section

/-!
# The selected-constants robust package and the exact frozen version-5 conclusion

`GoodCubeSelectedRobustPackageV5` replaces the universal
same-constant carrier `GoodCubeAnchoredTransferAll`.  Its constants are **selected** in the
printed order : the catalogue and its analytic
tolerances first, then the multiplier tolerance `ε`, then the shell tolerance `ε₁` with
`R(ε₁) = ε₁·3^{-1/4}/(1-3^{-1/4}) ≤ log(1+ε)`, and only then the disorder threshold `c`,
which also absorbs `ε₁` in the layer tails.  The robust local event carries the post-perturbation
finite tests for every admissible multiplier; both the cutoff (`θ = 1`) and the anchored
(`θ = aAnchored/aCutoff`) coefficients are read out of the **same** tests at the **same**
constants.
-/

open Homogenization hiding Vec cubeSet
open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.CoarseGrainingVocab (restrictedCoefficientSigma)
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.RobustGoodCube

variable {d : ℕ}

/-! ## Small robust helpers -/

theorem robustFiniteLocalTests_mono_eps {a : Vec d → ℝ} {S : Set (Vec d)}
    {e1 e2 p A sigma eps epsH mf : ℝ} {clock : ℝ → ℝ} {G : Finset (ℤ × Vec d)}
    {Pairs : Set (Cube d × Cube d)} (h12 : e1 ≤ e2)
    (h : GoodCubeV5RobustFiniteLocalTests a S e2 p A sigma eps epsH mf clock G Pairs) :
    GoodCubeV5RobustFiniteLocalTests a S e1 p A sigma eps epsH mf clock G Pairs :=
  fun th hth => h th (admissibleMultiplier_mono_eps h12 hth)

/-- The robust contraction read at the multiplier `1`. -/
theorem robustHarmonicOscillation_cutoff {a : Vec d → ℝ} {S : Set (Vec d)} {eps eps0 : ℝ}
    {Pfam : Set (Cube d × Cube d)} (heps : 0 ≤ eps)
    (h : GoodCubeV5RobustHarmonicOscillation a S eps eps0 Pfam) :
    LocalHarmonicOscillation a eps0 Pfam := by
  have h1 := h (fun _ => 1)
    ⟨continuousOn_const, fun _ _ => one_pos, 1, one_pos, fun _ _ => by simpa using heps⟩
  simpa only [mul_one] using h1

/-- The site catalogue lies in the native box. -/
theorem catalogue_site_cubes_subset_nativeBox (n : ℕ) (z : Lattice d)
    (G : Finset (ℕ × Vec d))
    (hGinside : ∀ q ∈ G, cubeSet (q.2, (3 : ℝ) ^ (-(q.1 : ℤ))) ⊆
      cubeSet ((0 : Vec d), (1 : ℝ))) :
    ∀ q ∈ G.image (fun q => ((n : ℤ) - q.1, goodCubeCentre n z + (3 : ℝ) ^ n • q.2)),
      cubeSet (q.2, (3 : ℝ) ^ q.1) ⊆ nativeBox n 1 z := by
  intro q hq
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

/-- The site auxiliary pairs lie in the native box. -/
theorem auxPairs_site_subset_nativeBox (X : Finset (Vec d)) (j k : ℕ) (hj1 : 1 ≤ j)
    (hX : ∀ x ∈ X, cubeSet (x, (3 : ℝ) ^ (-(k : ℤ))) ⊆ cubeSet ((0 : Vec d), (1 : ℝ)))
    (n : ℕ) (z : Lattice d) :
    ∀ q ∈ affinePairTransport (goodCubeCentre n z) ((3 : ℝ) ^ n) ''
        (goodCubeAuxiliaryPairs X j (-(k : ℤ)) : Set (Cube d × Cube d)),
      cubeSet q.2 ⊆ nativeBox n 1 z := by
  intro q hq
  obtain ⟨q0, hq0, rfl⟩ := hq
  obtain ⟨-, -, -, -, h4, -⟩ := goodCube_auxiliary_pair_catalog_native X j k hj1 hX n
    (goodCubeCentre n z) |>.2 _ (Finset.mem_image_of_mem _ hq0)
  refine h4.trans ?_
  simp only [nativeBox, one_mul, cubeSet]
  exact subset_rfl

/-- The reference pairs lie in the native box. -/
theorem referencePairs_subset_nativeBox {grid0 : Finset (Vec d)} {j1 j2 : ℕ}
    {Pfam0 : Set (Cube d × Cube d)} {Qfam0 Afam0 : Set (Cube d)} (n : ℕ) (z : Lattice d)
    (hgeom : IsLocalCubeGeometry grid0 j1 j2 (goodCubeCentre n z, (3 : ℝ) ^ n)
      (goodCubeReferencePairs Pfam0 n z) (goodCubeReferenceFamily Qfam0 n z)
      (goodCubeReferenceFamily Afam0 n z)) :
    ∀ q ∈ goodCubeReferencePairs Pfam0 n z, cubeSet q.2 ⊆ nativeBox n 1 z := by
  intro q hq
  refine (hgeom.pair_in_half q hq).trans ?_
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  simp only [nativeBox, one_mul]
  exact centeredAxisCube_mono (by linarith)

/-- The anchored coefficient is the cutoff coefficient of a deterministic readout sample. -/
theorem aCutoff_readoutSample_anchoredLog (M : GMCModel d) (n : ℕ)
    (omega : AnchoredC11Sample d) :
    aCutoff M n (goodCubeV5ReadoutSample M (anchoredLog omega)) = aAnchored M omega := by
  rw [goodCubeV5_readout_aCutoff_eq_exp]
  rfl

/-- **Step 5's factorization**.  On the full good
event, `aAnchored = c_U · aCutoff · θ` on the native box, with `c_U > 0` constant,
`θ(z_U) = 1`, `|log θ| ≤ R(ε₁)` from the `j ≥ 1` layers, and hence `|θ - 1| ≤ ε` as soon as
`R(ε₁) ≤ log(1 + ε)`.  No derivative of `θ` is needed downstream. -/
theorem anchored_factorization (M : GMCModel d) (omega : AnchoredC11Sample d) (n : ℕ)
    (z : Lattice d) {eps1 epsilon : ℝ} (heps1 : 0 ≤ eps1) (hepsilon : 0 < epsilon)
    (hbudget : goodCubeV5TailBudget eps1 ≤ Real.log (1 + epsilon))
    (E0 : Lattice d → Set (PotentialSample d))
    (hgood : omega.1 ∈ goodCubeEvent (goodCubeEventField n 1 eps1 E0) z) :
    0 < aAnchored M omega (goodCubeCentre n z) / aCutoff M n omega.1 (goodCubeCentre n z) ∧
    ∀ x ∈ nativeBox n 1 z,
      aAnchored M omega x =
        (aAnchored M omega (goodCubeCentre n z) / aCutoff M n omega.1 (goodCubeCentre n z)) *
          aCutoff M n omega.1 x *
          ((aAnchored M omega x / aCutoff M n omega.1 x) /
            (aAnchored M omega (goodCubeCentre n z) /
              aCutoff M n omega.1 (goodCubeCentre n z))) ∧
      |Real.log ((aAnchored M omega x / aCutoff M n omega.1 x) /
          (aAnchored M omega (goodCubeCentre n z) /
            aCutoff M n omega.1 (goodCubeCentre n z)))| ≤ goodCubeV5TailBudget eps1 ∧
      |(aAnchored M omega x / aCutoff M n omega.1 x) /
          (aAnchored M omega (goodCubeCentre n z) /
            aCutoff M n omega.1 (goodCubeCentre n z)) - 1| ≤ epsilon := by
  set r : Vec d → ℝ := fun x => aAnchored M omega x / aCutoff M n omega.1 x with hr
  have hrpos (x : Vec d) : 0 < r x := div_pos (aAnchored_pos M omega x) (aCutoff_pos M n omega.1 x)
  have hc : goodCubeCentre n z ∈ nativeBox n 1 z := by
    refine mem_centeredAxisCube.mpr fun i => ?_
    simp only [sub_self, abs_zero]
    positivity
  refine ⟨hrpos _, fun x hx => ⟨?_, ?_, ?_⟩⟩
  · have ha := (aCutoff_pos M n omega.1 x).ne'
    have hAc := (aAnchored_pos M omega (goodCubeCentre n z)).ne'
    have hac := (aCutoff_pos M n omega.1 (goodCubeCentre n z)).ne'
    change aAnchored M omega x = r (goodCubeCentre n z) * aCutoff M n omega.1 x *
      (r x / r (goodCubeCentre n z))
    rw [hr]
    field_simp
  · have hlog := goodCubeV5_log_ratio_sub_le M omega n z heps1 E0 hgood hx hc
    change |Real.log (r x / r (goodCubeCentre n z))| ≤ _
    rw [Real.log_div (hrpos x).ne' (hrpos _).ne']
    exact hlog
  · have hlog := goodCubeV5_log_ratio_sub_le M omega n z heps1 E0 hgood hx hc
    change |r x / r (goodCubeCentre n z) - 1| ≤ epsilon
    set t := Real.log (r x) - Real.log (r (goodCubeCentre n z)) with ht
    have htb : |t| ≤ Real.log (1 + epsilon) := hlog.trans hbudget
    have heq : r x / r (goodCubeCentre n z) = Real.exp t := by
      rw [ht, Real.exp_sub, Real.exp_log (hrpos x), Real.exp_log (hrpos _)]
    rw [heq]
    have hupper : Real.exp t ≤ 1 + epsilon := by
      simpa only [Real.exp_log (by linarith : 0 < 1 + epsilon)] using
        Real.exp_le_exp.mpr (abs_le.mp htb).2
    have hlogle : Real.log (1 + epsilon) ≤ epsilon := by
      simpa using Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + epsilon)
    have hlow := Real.add_one_le_exp t
    exact abs_le.mpr ⟨by linarith [(abs_le.mp htb).1], by linarith⟩

/-! ## The selected-constants interface -/

/-- **The selected-constants robust package.**  One reference template, one catalogue, one
raw local event, and constants chosen in the printed order.  In contrast with
`GoodCubeAnchoredTransferAll`, nothing is quantified over arbitrary constants: the robust tests
already carry the multiplier losses (`3A`, `θ_J/9`, the additive torsion margin), and the
shell tolerance `eps1` is calibrated against the multiplier tolerance `epsilon`. -/
def GoodCubeSelectedRobustPackageV5 (d : ℕ) (eta p0 eps0 : ℝ) : Prop :=
  ∃ (c C eps1 epsilon A epsL2 epsH massFraction : ℝ) (Cdep j1 j2 J : ℕ) (r : ℤ)
    (G : Finset (ℕ × Vec d)) (Pairs : Set (Cube d × Cube d)),
    0 < c ∧ 1 ≤ C ∧ 0 < eps1 ∧ 0 < epsilon ∧ epsilon < 1 / 2 ∧
    goodCubeV5TailBudget eps1 ≤ Real.log (1 + epsilon) ∧
    1 < (3 : ℝ) ^ r ∧ ((shellCoverShifts d r).card : ℝ) ≤ C ∧
    1 + Real.sqrt (d : ℝ) ≤ (Cdep : ℝ) ∧
    c ≤ 1 / 3 ∧ c ≤ Real.sqrt layerTailConstant * eps1 ∧
    2 * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * c) ≤ eps1 ∧
    C * (3 : ℝ) ^ (-(3 * (j1 : ℝ) / 2)) ≤ eta / 2 ∧
    ∃ (grid0 : Finset (Vec d)) (Pfam0 : Set (Cube d × Cube d)) (Qfam0 Afam0 : Set (Cube d))
      (bad : (M : GMCModel d) → (n : ℕ) → Set (nativeBox n 1 (0 : Lattice d) → ℝ)),
      (∀ (n : ℕ) (z : Lattice d),
        IsLocalCubeGeometry grid0 j1 j2 (goodCubeCentre n z, (3 : ℝ) ^ n)
          (goodCubeReferencePairs Pfam0 n z) (goodCubeReferenceFamily Qfam0 n z)
          (goodCubeReferenceFamily Afam0 n z)) ∧
      (∀ (n : ℕ) (z : Lattice d), ∀ q ∈ G.image
          (fun q => ((n : ℤ) - q.1, goodCubeCentre n z + (3 : ℝ) ^ n • q.2)),
        cubeSet (q.2, (3 : ℝ) ^ q.1) ⊆ nativeBox n 1 z) ∧
      (∀ (n : ℕ) (z : Lattice d),
        ∀ q ∈ affinePairTransport (goodCubeCentre n z) ((3 : ℝ) ^ n) '' Pairs,
        cubeSet q.2 ⊆ nativeBox n 1 z) ∧
      GoodCubeV5RobustLocalEvent d c C epsilon p0 A epsL2 epsH massFraction eps0 J G Pairs
        Pfam0 bad ∧
      (∀ M : GMCModel d, M.delta ≤ c → ∀ (n : ℕ) (z : Lattice d) (omega : PotentialSample d)
        (law : Kernel (Vec d) (Path d)),
        LocalDiffusionData (aCutoff M n omega) (aCutoff M n omega) law →
        GoodCubeFiniteLocalTests (aCutoff M n omega) p0 A (if J ≤ n then ahom M n else 1)
          epsL2 epsH massFraction (Section7Process.timeScale (ahom M))
          (G.image (fun q => ((n : ℤ) - q.1, goodCubeCentre n z + (3 : ℝ) ^ n • q.2)))
          (affinePairTransport (goodCubeCentre n z) ((3 : ℝ) ^ n) '' Pairs) →
        LocalTorsionEstimates (aCutoff M n omega) law (Section7Process.timeScale (ahom M))
          p0 c C (goodCubeCentre n z, (3 : ℝ) ^ n) (goodCubeReferenceFamily Qfam0 n z)
          (goodCubeReferenceFamily Afam0 n z))

/-! ## The assembly -/

/-- **The exact frozen version-5 conclusion from the selected robust package.** -/
theorem weighted_good_cube_events_v5_of_robustPackage
    (d : ℕ) [NeZero d] (eta : ℝ) (heta0 : 0 < eta) (p0 : ℝ) (hp0 : 2 < p0)
    (hpkg : GoodCubeSelectedRobustPackageV5 d eta p0 (eta / 2)) :
    ∃ (c C eps0 p0 : ℝ) (Cdep j1 j2 : ℕ),
      0 < c ∧ 0 < C ∧ 0 < eps0 ∧ eps0 ≤ eta / 2 ∧ 2 < p0 ∧
      C * (3 : ℝ) ^ (-(3 * (j1 : ℝ) / 2)) ≤ eta / 2 ∧
      ∃ (grid0 : Finset (Vec d)) (Pfam0 : Set (Cube d × Cube d))
        (Qfam0 Afam0 : Set (Cube d)),
        let transportCube : ℕ → Lattice d → Cube d → Cube d := fun n z Q =>
          (goodCubeCentre n z + (3 : ℝ) ^ n • Q.1, (3 : ℝ) ^ n * Q.2)
        let Pfam : ℕ → Lattice d → Set (Cube d × Cube d) := fun n z =>
          (fun p => (transportCube n z p.1, transportCube n z p.2)) '' Pfam0
        let Qfam : ℕ → Lattice d → Set (Cube d) := fun n z =>
          transportCube n z '' Qfam0
        let Afam : ℕ → Lattice d → Set (Cube d) := fun n z =>
          transportCube n z '' Afam0
        (∀ (n : ℕ) (z : Lattice d),
          IsLocalCubeGeometry grid0 j1 j2 (goodCubeCentre n z, (3 : ℝ) ^ n)
            (Pfam n z) (Qfam n z) (Afam n z)) ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ c →
        ∀ n : ℕ,
        ∃ E : ℕ → Lattice d → Set (_root_.SubdiffusiveProcess.Model.PotentialSample d),
          (∀ z : Lattice d,
            MeasurableSet[restrictedCoefficientSigma
              (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
                _root_.SubdiffusiveProcess.Model.aCutoff M n omega)
              (centeredAxisCube (goodCubeCentre n z) (C * (3 : ℝ) ^ n))] (E 0 z)) ∧
          (∀ j : ℕ, 1 ≤ j → ∀ z : Lattice d,
            MeasurableSet[shellLocalSigma (n + j)
              (centeredAxisCube (goodCubeCentre n z) (C * (3 : ℝ) ^ (n + j)))] (E j z)) ∧
          (∀ (j : ℕ) (z : Lattice d),
            M.P.toMeasure (E j z) ≤
              ENNReal.ofReal (C * Real.exp (-(c * (c / (M.delta ^ 2 * Real.log M.delta ^ 2)) *
                (3 : ℝ) ^ (3 * (j : ℝ) / 2))))) ∧
          IndependentEventScales M.P.toMeasure E ∧
          MultiscaleFiniteRangeIndependentEvents M.P.toMeasure (fun j => Cdep * 3 ^ j) E ∧
          TranslationInvariantEventLaw M.P.toMeasure E ∧
          (∀ z : Lattice d,
            ∀ omega ∈ goodCubeEvent E z,
              ∀ law : Kernel (Vec d) (Path d),
                LocalDiffusionData (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)
                  (_root_.SubdiffusiveProcess.Model.aCutoff M n omega) law →
                LocalTorsionEstimates (_root_.SubdiffusiveProcess.Model.aCutoff M n omega) law
                    (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
                      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M))
                    p0 c C (goodCubeCentre n z, (3 : ℝ) ^ n) (Qfam n z) (Afam n z) ∧
                  LocalHarmonicOscillation (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)
                    eps0 (Pfam n z)) ∧
          (∀ z : Lattice d,
            ∀ omega : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d,
              (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) ∈ goodCubeEvent E z →
              ∀ law : Kernel (Vec d) (Path d),
                LocalDiffusionData (_root_.SubdiffusiveProcess.Model.aAnchored M omega)
                  (_root_.SubdiffusiveProcess.Model.aAnchored M omega) law →
                LocalTorsionEstimates (_root_.SubdiffusiveProcess.Model.aAnchored M omega) law
                    (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
                      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M))
                    p0 c C (goodCubeCentre n z, (3 : ℝ) ^ n) (Qfam n z) (Afam n z) ∧
                  LocalHarmonicOscillation (_root_.SubdiffusiveProcess.Model.aAnchored M omega)
                    eps0 (Pfam n z)) := by
  have hpkg' := hpkg
  rcases hpkg' with ⟨c, C, eps1, epsilon, A, epsL2, epsH, mf, Cdep, j1, j2, J, r, G, Pairs,
    hc, hC1, heps1, hepsilon, hhalf, hbudget, hBr, hNC, hCdep, hc3, hcK, hcdelta, hsmall,
    grid0, Pfam0, Qfam0, Afam0, bad, hgeom, hGin, hPin, hlocal, hread⟩
  have hC : 0 < C := lt_of_lt_of_le one_pos hC1
  have heps0 : 0 < eta / 2 := by linarith
  have hB : (0 : ℝ) < 1 := one_pos
  obtain ⟨E0, hE0meas, hE0sub, hE0prob, hE0cov⟩ := exists_layerZero_hull_family hB bad
  refine ⟨c, C, eta / 2, p0, Cdep, j1, j2, hc, hC, heps0, le_rfl, hp0, hsmall,
    grid0, Pfam0, Qfam0, Afam0, ?_⟩
  refine ⟨hgeom, ?_⟩
  intro M hdelta n
  refine ⟨goodCubeEventField n 1 eps1 (E0 M n), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- clause 7a, on the enlarged box
  · intro z
    have hbox : nativeBox n 1 z ⊆ centeredAxisCube (goodCubeCentre n z) (C * (3 : ℝ) ^ n) :=
      centeredAxisCube_mono (mul_le_mul_of_nonneg_right hC1 (by positivity))
    exact SubdiffusiveProcess.CoarseGrainingVocab.restrictedCoefficientSigma_mono _ hbox _ (hE0meas M n z)
  -- clause 7b, on the enlarged box
  · intro j hj z
    have hbox : layerBox n j 1 z ⊆
        centeredAxisCube (goodCubeCentre n z) (C * (3 : ℝ) ^ (n + j)) :=
      centeredAxisCube_mono (mul_le_mul_of_nonneg_right hC1 (by positivity))
    refine shellLocalSigma_mono (n + j) hbox _ ?_
    match j with
    | 0 => exact absurd hj (by omega)
    | (i + 1) => exact measurableSet_layerEvent hB.le n (i + 1) eps1 z
  -- clause 7c
  · intro j z
    have hdpos : 0 < M.delta := M.shellPrefix.delta_pos
    match j with
    | 0 =>
        have h := (hE0prob M n z).le.trans (hlocal M hdelta n z).1
        have hrw : (3 : ℝ) ^ (3 * ((0 : ℕ) : ℝ) / 2) = 1 := by
          norm_num
        simpa only [goodCubeEventField, hrw, mul_one] using h
    | (i + 1) =>
        have hdlt : 2 * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) ≤ eps1 := by
          refine le_trans ?_ hcdelta
          have hpos : (0 : ℝ) < (1 + Real.log 2) ^ (2 : ℝ)⁻¹ :=
            Real.rpow_pos_of_pos (by positivity) _
          nlinarith
        have hlayer := measure_layerEvent_le_cover M n (i + 1) hB.le hBr hdlt z
        refine hlayer.trans (ENNReal.ofReal_le_ofReal ?_)
        have hexp : c * (c / (M.delta ^ 2 * Real.log M.delta ^ 2)) *
            (3 : ℝ) ^ (3 * ((i + 1 : ℕ) : ℝ) / 2) ≤
            layerTailConstant * (eps1 ^ 2 / M.delta ^ 2) *
              (3 : ℝ) ^ (3 * ((i + 1 : ℕ) : ℝ) / 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by norm_num) _)
          exact tail_exponent_transfer layerTailConstant_pos hdpos hdelta hc3 hcK
        have hmono : Real.exp (-(layerTailConstant * (eps1 ^ 2 / M.delta ^ 2) *
              (3 : ℝ) ^ (3 * ((i + 1 : ℕ) : ℝ) / 2))) ≤
            Real.exp (-(c * (c / (M.delta ^ 2 * Real.log M.delta ^ 2)) *
              (3 : ℝ) ^ (3 * ((i + 1 : ℕ) : ℝ) / 2))) :=
          Real.exp_le_exp.mpr (by linarith)
        exact mul_le_mul hNC hmono (Real.exp_pos _).le hC.le
  -- clause 7d
  · exact (goodCubeEventField_clauses M n hB.le hCdep (E0 M n) (hE0meas M n)).2.1
  -- clause 7e
  · exact (goodCubeEventField_clauses M n hB.le hCdep (E0 M n) (hE0meas M n)).2.2
  -- clause 7f
  · exact translationInvariantEventLaw_goodCubeEventField M n hB.le (E0 M n)
      (fun z => measurableSet_of_restrictedCoefficientSigma (hE0meas M n z))
      (fun z a => hE0cov M n z a)
  -- clause 7g: the cutoff package, read from the robust tests at the multiplier `1`
  · intro z omega hom law hdiff
    have homraw := goodCubeEvent_mono_layerZero n 1 eps1
      (coefficientLocalBadEvent M n 1 (bad M n)) (E0 M n) (hE0sub M n) z hom
    have hnot := not_mem_layerZero_of_goodCubeEvent homraw
    obtain ⟨htestsR, hoscR⟩ := (hlocal M hdelta n z).2 omega hnot
    exact ⟨hread M hdelta n z omega law hdiff
        (goodCubeV5RobustFiniteLocalTests_cutoff hepsilon.le htestsR),
      robustHarmonicOscillation_cutoff hepsilon.le hoscR⟩
  -- the anchored package, read from the same tests at the anchored ratio
  · intro z omega hom law hdiff
    have homraw := goodCubeEvent_mono_layerZero n 1 eps1
      (coefficientLocalBadEvent M n 1 (bad M n)) (E0 M n) (hE0sub M n) z hom
    obtain ⟨htestsA, hoscA⟩ := goodCubeV5_anchored_tests_of_local_event hlocal heps1
      hepsilon hhalf hbudget M hdelta n z omega homraw (hGin n z) (hPin n z)
      (referencePairs_subset_nativeBox n z (hgeom n z))
    have hcoef := aCutoff_readoutSample_anchoredLog M n omega
    have hdiff' : LocalDiffusionData
        (aCutoff M n (goodCubeV5ReadoutSample M (anchoredLog omega)))
        (aCutoff M n (goodCubeV5ReadoutSample M (anchoredLog omega))) law := by
      rw [hcoef]; exact hdiff
    have htests' : GoodCubeFiniteLocalTests
        (aCutoff M n (goodCubeV5ReadoutSample M (anchoredLog omega))) p0 A
        (if J ≤ n then ahom M n else 1) epsL2 epsH mf (Section7Process.timeScale (ahom M))
        (G.image (fun q => ((n : ℤ) - q.1, goodCubeCentre n z + (3 : ℝ) ^ n • q.2)))
        (affinePairTransport (goodCubeCentre n z) ((3 : ℝ) ^ n) '' Pairs) := by
      rw [hcoef]; exact htestsA
    have hT := hread M hdelta n z _ law hdiff' htests'
    rw [hcoef] at hT
    exact ⟨hT, hoscA⟩

/-! ## The producer -/

/-- The disorder threshold forced by the shell tolerance: `c ≤ √K ε₁` and
`2 (1 + log 2)^{1/2} c ≤ ε₁`. -/
def shellThreshold (eps1 : ℝ) : ℝ :=
  min (Real.sqrt layerTailConstant * eps1) (eps1 / (2 * (1 + Real.log 2) ^ (2 : ℝ)⁻¹))

theorem shellThreshold_spec {eps1 c : ℝ} (heps1 : 0 < eps1)
    (hc : c ≤ shellThreshold eps1) :
    0 < shellThreshold eps1 ∧ c ≤ Real.sqrt layerTailConstant * eps1 ∧
      2 * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * c) ≤ eps1 := by
  have hq : (0 : ℝ) < (1 + Real.log 2) ^ (2 : ℝ)⁻¹ :=
    Real.rpow_pos_of_pos (by positivity) _
  have hK : 0 < Real.sqrt layerTailConstant := Real.sqrt_pos.mpr layerTailConstant_pos
  refine ⟨lt_min (mul_pos hK heps1) (div_pos heps1 (by positivity)),
    hc.trans (min_le_left _ _), ?_⟩
  have h2 : c ≤ eps1 / (2 * (1 + Real.log 2) ^ (2 : ℝ)⁻¹) := hc.trans (min_le_right _ _)
  rw [le_div_iff₀ (by positivity)] at h2
  linarith

theorem shellThreshold_pos {eps1 : ℝ} (heps1 : 0 < eps1) : 0 < shellThreshold eps1 := by
  have hq : (0 : ℝ) < (1 + Real.log 2) ^ (2 : ℝ)⁻¹ :=
    Real.rpow_pos_of_pos (by positivity) _
  have hK : 0 < Real.sqrt layerTailConstant := Real.sqrt_pos.mpr layerTailConstant_pos
  exact lt_min (mul_pos hK heps1) (div_pos heps1 (by positivity))

/-- Two coefficient-local layer-zero tails at rates `cEvt, cH` are absorbed into the frozen
tail shape at any `c ≤ cAbs`. -/
theorem goodCube_combined_layerZero_tail (M : GMCModel d) (n : ℕ) (z : Lattice d)
    (s t : Set (nativeBox n 1 (0 : Lattice d) → ℝ)) {c cEvt cH cAbs C : ℝ}
    (hc : 0 ≤ c) (hccAbs : c ≤ cAbs) (h1C : 1 ≤ C) (hminpos : 0 < min cEvt cH)
    (hdelta : M.delta ≤ cAbs)
    (habsorb : ∀ delta : ℝ, 0 < delta → delta ≤ cAbs →
      2 * Real.exp (-(min cEvt cH) ^ 2 / (delta ^ 2 * Real.log delta ^ 2)) ≤
        Real.exp (-(cAbs ^ 2 / (delta ^ 2 * Real.log delta ^ 2))))
    (h1 : M.P.toMeasure (coefficientLocalBadEvent M n 1 s z) ≤
      ENNReal.ofReal (Real.exp (-(cEvt ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2)))))
    (h2 : M.P.toMeasure (coefficientLocalBadEvent M n 1 t z) ≤
      ENNReal.ofReal (Real.exp (-(cH ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2))))) :
    M.P.toMeasure (coefficientLocalBadEvent M n 1 (s ∪ t) z) ≤ ENNReal.ofReal
      (C * Real.exp (-(c * (c / (M.delta ^ 2 * Real.log M.delta ^ 2))))) := by
  have hdpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hDnn : (0 : ℝ) ≤ M.delta ^ 2 * Real.log M.delta ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hmono : ∀ e : ℝ, min cEvt cH ≤ e →
      ENNReal.ofReal (Real.exp (-(e ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2)))) ≤
        ENNReal.ofReal (Real.exp
          (-((min cEvt cH) ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2)))) := by
    intro e he
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg ?_))
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hminpos.le he 2) hDnn
  have hsum : M.P.toMeasure (coefficientLocalBadEvent M n 1 (s ∪ t) z) ≤
      ENNReal.ofReal (Real.exp
        (-((min cEvt cH) ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2)))) +
      ENNReal.ofReal (Real.exp
        (-((min cEvt cH) ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2)))) := by
    rw [coefficientLocalBadEvent_union]
    exact (measure_union_le _ _).trans
      (add_le_add (h1.trans (hmono cEvt (min_le_left _ _)))
        (h2.trans (hmono cH (min_le_right _ _))))
  refine hsum.trans ?_
  have hdouble : ENNReal.ofReal (Real.exp
        (-((min cEvt cH) ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2)))) +
      ENNReal.ofReal (Real.exp
        (-((min cEvt cH) ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2)))) =
      ENNReal.ofReal (2 * Real.exp
        (-((min cEvt cH) ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2)))) := by
    rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
    congr 1
    ring
  rw [hdouble]
  have habs := habsorb M.delta hdpos hdelta
  have habs' : 2 * Real.exp
        (-((min cEvt cH) ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2))) ≤
      Real.exp (-(cAbs ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2))) := by
    simpa only [neg_div] using habs
  exact (ENNReal.ofReal_le_ofReal habs').trans
    (goodCube_catalogue_tail_mono M c cAbs C hc hccAbs h1C)

/-- **The robust local event (the obligation) from its two coefficient-local parts.** -/
theorem goodCubeV5RobustLocalEvent_of_parts {c C epsilon epsCat epsStar p A epsL2 epsH
    massFraction eps0 cEvt cH cAbs : ℝ} {J : ℕ}
    {G : Finset (ℕ × Vec d)} {Pairs Pfam0 : Set (Cube d × Cube d)}
    (bad badH : (M : GMCModel d) → (n : ℕ) → Set (nativeBox n 1 (0 : Lattice d) → ℝ))
    (hc : 0 ≤ c) (hccAbs : c ≤ cAbs) (hccEvt : c ≤ cEvt) (hccH : c ≤ cH) (h1C : 1 ≤ C)
    (hminpos : 0 < min cEvt cH) (hepsCat : epsilon ≤ epsCat) (hepsStar : epsilon ≤ epsStar)
    (habsorb : ∀ delta : ℝ, 0 < delta → delta ≤ cAbs →
      2 * Real.exp (-(min cEvt cH) ^ 2 / (delta ^ 2 * Real.log delta ^ 2)) ≤
        Real.exp (-(cAbs ^ 2 / (delta ^ 2 * Real.log delta ^ 2))))
    (hbad : ∀ M : GMCModel d, M.delta ≤ cEvt → ∀ n : ℕ,
      (∀ z : Lattice d,
        M.P.toMeasure (coefficientLocalBadEvent M n 1 (bad M n) z) ≤
          ENNReal.ofReal (Real.exp (-(cEvt ^ 2 / (M.delta ^ 2 * (Real.log M.delta) ^ 2))))) ∧
      ∀ (z : Lattice d) (omega : PotentialSample d),
        omega ∉ coefficientLocalBadEvent M n 1 (bad M n) z →
        GoodCubeV5RobustFiniteLocalTests (aCutoff M n omega) (nativeBox n 1 z)
          epsCat p A (if J ≤ n then ahom M n else 1) epsL2 epsH massFraction
          (Section7Process.timeScale (ahom M))
          (G.image (fun q => ((n : ℤ) - q.1, goodCubeCentre n z + (3 : ℝ) ^ n • q.2)))
          (affinePairTransport (goodCubeCentre n z) ((3 : ℝ)^n) '' Pairs))
    (hbadH : ∀ M : GMCModel d, M.delta ≤ cH → ∀ n : ℕ,
      (∀ z : Lattice d,
        M.P.toMeasure (coefficientLocalBadEvent M n 1 (badH M n) z) ≤
          ENNReal.ofReal (Real.exp (-(cH ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2))))) ∧
      ∀ (z : Lattice d) (omega : PotentialSample d),
        omega ∉ coefficientLocalBadEvent M n 1 (badH M n) z →
        ∀ epsilon : ℝ, epsilon ≤ epsStar →
          GoodCubeV5RobustHarmonicOscillation (aCutoff M n omega)
            (nativeBox n 1 z) epsilon eps0 (goodCubeReferencePairs Pfam0 n z)) :
    GoodCubeV5RobustLocalEvent d c C epsilon p A epsL2 epsH massFraction eps0 J G Pairs
      Pfam0 (fun M n => bad M n ∪ badH M n) := by
  intro M hdelta n z
  refine ⟨goodCube_combined_layerZero_tail M n z (bad M n) (badH M n) hc hccAbs h1C hminpos
    (hdelta.trans hccAbs) habsorb ((hbad M (hdelta.trans hccEvt) n).1 z)
    ((hbadH M (hdelta.trans hccH) n).1 z), ?_⟩
  intro omega hom
  have hnot1 : omega ∉ coefficientLocalBadEvent M n 1 (bad M n) z := fun hmem =>
    hom (by rw [coefficientLocalBadEvent_union]; exact Or.inl hmem)
  have hnot2 : omega ∉ coefficientLocalBadEvent M n 1 (badH M n) z := fun hmem =>
    hom (by rw [coefficientLocalBadEvent_union]; exact Or.inr hmem)
  exact ⟨robustFiniteLocalTests_mono_eps hepsCat
      ((hbad M (hdelta.trans hccEvt) n).2 z omega hnot1),
    (hbadH M (hdelta.trans hccH) n).2 z omega hnot2 epsilon hepsStar⟩

/-- **The selected robust package exists**, with the exponent fixed before `eta`. -/
theorem exists_goodCube_selected_robust_package_v5 (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ p : ℝ, 2 < p ∧ ∀ eta : ℝ, 0 < eta →
      GoodCubeSelectedRobustPackageV5 d eta p (eta / 2) := by
  classical
  obtain ⟨p, A, hp, hA, hevent⟩ := exists_goodCube_reference_catalogue_event_family_robust d hd
  obtain ⟨CE, _hCE, hexit⟩ := exists_goodCube_exit_upper_constant hp
  refine ⟨p, hp, ?_⟩
  intro eta heta
  have heps0 : 0 < eta / 2 := by linarith
  obtain ⟨epsStar0, hepsStar0, jH, hjH, hoscN⟩ :=
    exists_goodCube_reference_robustOscillation_local_event d (eta / 2) heps0
  obtain ⟨C, cShell, Cdep, j1, r, hC, hcShell, hAC, hCEC, hBr, hNC, h1C,
    hCdep, hcShell3, _hcShellK, _hcShellDelta, hj1, hsmall⟩ :=
    exists_goodCube_selected_scalar_parameters d eta heta A CE hA
  obtain ⟨grid0, Pfam0, Qfam0, Afam0, hgeom0, hinside, hgeom⟩ :=
    exists_goodCubeReferenceTemplate d hj1 (le_trans (by norm_num) hjH)
  have hunit : ((0 : Vec d), (1 : ℝ)) ∈ Qfam0 := by
    simpa only [pow_zero] using hgeom0.self_mem
  have hinside1 : ∀ Q ∈ Qfam0, cubeSet Q ⊆ cubeSet ((0 : Vec d), (1 : ℝ)) := by
    simpa only [pow_zero] using hinside
  -- the exported pair template and its robust harmonic event
  set PF : Finset (Cube d × Cube d) := hgeom0.finite_P.toFinset with hPFdef
  have hPFcoe : (PF : Set (Cube d × Cube d)) = Pfam0 := by
    rw [hPFdef, Set.Finite.coe_toFinset]
  obtain ⟨cH, hcH, _hcHb, _hcH12, hoscFam⟩ := hoscN PF.card 1 one_pos
  obtain ⟨badH, hbadH⟩ := hoscFam j1 grid0 PF Qfam0 Afam0 (le_refl _)
    (by rw [hPFcoe]; exact hgeom)
  -- the lower readout, the auxiliary geometry and the catalogue
  obtain ⟨K, hK, hlowerTheta⟩ :=
    exists_goodCube_reference_torsion_lower_readout_parameters d hd p A hp hA
  obtain ⟨theta, W, htheta0, htheta1, _hW, hcoverChoices⟩ :=
    exists_goodCube_complete_auxiliary_geometry Qfam0 hgeom0.finite_Q hgeom0.side_pos
      hunit hinside1
  obtain ⟨k0, etaCap, epsH, hk0, hetaCap, hepsH, hlowerV⟩ :=
    hlowerTheta theta htheta0 htheta1
  obtain ⟨j, hj, heventJ⟩ := hevent epsH hepsH
  obtain ⟨k, _N0, v0, centers, hv0, _hv0eq, hauxAll⟩ :=
    hcoverChoices etaCap K hetaCap hK j hj
  obtain ⟨_J0, depth, hdepthAll, _hnative, _hvolume⟩ :=
    exists_goodCube_reference_scale_catalog grid0 Qfam0 hgeom0.finite_Q hgeom0.side_pos
      hgeom0.gridded hinside1
  have hdepth : ∀ Q : Qfam0, Q.val.2 = (3 : ℝ)^(-(depth Q : ℤ)) :=
    fun Q => (hdepthAll Q).2.1
  have htarget := goodCube_auxiliary_target_geometry Qfam0 hgeom0.finite_Q
    hgeom0.side_pos hunit hinside1
  let : Finite (Option (GoodCubeCompactPair Qfam0)) := htarget.1
  have hauxInside : ∀ i, ∀ x ∈ centers i,
      cubeSet (x, (3 : ℝ)^(-(k : ℤ))) ⊆ cubeSet ((0 : Vec d), (1 : ℝ)) := by
    intro i x hx
    have hout := ((hauxAll i).2.2.2.2 x hx).2.1
    exact (subset_closure.trans hout).trans
      (hinside1 _ (htarget.2 i).2.2.1)
  obtain ⟨G, P, J, N, hGcard, hPcard, _hkJ, hG, hGorig, hGquarter, hGaux, hP, _hPgeom⟩ :=
    exists_goodCube_unified_test_catalog Qfam0 hgeom0.finite_Q depth hdepth hinside1
      centers j k (by omega) hauxInside
  obtain ⟨epsL2, hepsL2, hlower⟩ := hlowerV v0 hv0
  obtain ⟨epsCat, hepsCat, hepsCat4, cEvt, hcEvt, _hcEvtHalf, heventG⟩ :=
    heventJ J N epsL2 hepsL2
  let X := goodCubeAuxiliaryCenterUnion centers
  have hX : ∀ x ∈ X, cubeSet (x, (3 : ℝ)^(-(k : ℤ))) ⊆
      cubeSet ((0 : Vec d), (1 : ℝ)) := by
    intro x hx
    obtain ⟨i, hi⟩ := (mem_goodCube_auxiliary_center_union centers x).mp hx
    exact hauxInside i x hi
  have hPcard' : (goodCubeAuxiliaryPairs X j (-(k : ℤ))).card ≤ N := by
    simpa only [hP] using hPcard
  obtain ⟨bad, hbad⟩ := heventG G hGcard (fun q hq => (hG q hq).1)
    (fun q hq => (hG q hq).2) k X hX hPcard'
  obtain ⟨cClock, hcClock, _hcClockHalf, hclock⟩ := exists_goodCube_depth_clock_threshold J
  -- the multiplier tolerance, then the shell tolerance
  set epsilon : ℝ := min epsCat epsStar0 with hepsilondef
  have hepsilon : 0 < epsilon := lt_min hepsCat hepsStar0
  have hepsilonCat : epsilon ≤ epsCat := min_le_left _ _
  have hepsilonStar : epsilon ≤ epsStar0 := min_le_right _ _
  have hhalf : epsilon < 1 / 2 := lt_of_le_of_lt (hepsilonCat.trans hepsCat4) (by norm_num)
  obtain ⟨eps1, heps1, hbudget1⟩ := exists_goodCubeV5_shell_tolerance hepsilon
  have hshell0 := shellThreshold_pos heps1
  -- the two layer-zero tails are absorbed into one
  have hminpos : 0 < min cEvt cH := lt_min hcEvt hcH
  obtain ⟨cAbs, hcAbs, hcAbsMin, _hcAbsHalf, habsorb⟩ :=
    goodCube_exists_finite_tail_absorption 2 ((min cEvt cH) ^ 2) (min cEvt cH)
      (by norm_num) (by positivity) hminpos
  let massFraction : ℝ := (((3 : ℝ)^(-(J : ℤ)))^d) / 9
  have hmass : 0 < massFraction := by dsimp [massFraction]; positivity
  let c : ℝ := min cAbs (min cShell (min cClock (min (k0 / 2)
    (min massFraction (shellThreshold eps1)))))
  have hc : 0 < c := lt_min hcAbs (lt_min hcShell (lt_min hcClock
    (lt_min (div_pos hk0 (by norm_num)) (lt_min hmass hshell0))))
  have hccAbs : c ≤ cAbs := min_le_left _ _
  have hcR1 : c ≤ min cShell (min cClock (min (k0 / 2)
      (min massFraction (shellThreshold eps1)))) := min_le_right _ _
  have hccShell : c ≤ cShell := hcR1.trans (min_le_left _ _)
  have hcR2 := hcR1.trans (min_le_right _ _)
  have hccClock : c ≤ cClock := hcR2.trans (min_le_left _ _)
  have hcR3 := hcR2.trans (min_le_right _ _)
  have hccLower : c ≤ k0 / 2 := hcR3.trans (min_le_left _ _)
  have hcR4 := hcR3.trans (min_le_right _ _)
  have hccMass : c ≤ massFraction := hcR4.trans (min_le_left _ _)
  have hccShellT : c ≤ shellThreshold eps1 := hcR4.trans (min_le_right _ _)
  have hccEvt : c ≤ cEvt := (hccAbs.trans hcAbsMin).trans (min_le_left _ _)
  have hccH : c ≤ cH := (hccAbs.trans hcAbsMin).trans (min_le_right _ _)
  obtain ⟨_, hcK, hcdelta⟩ := shellThreshold_spec heps1 hccShellT
  have hbudget : ∀ M : GMCModel d, M.delta ≤ c →
      2 * M.delta^2 * ((J : ℝ) + 1) ≤ Real.log 2 :=
    fun M hdelta => hclock M.delta M.shellPrefix.delta_pos (hdelta.trans hccClock)
  -- the robust local event (the obligation), proved
  have hbadH' : ∀ M : GMCModel d, M.delta ≤ cH → ∀ n : ℕ,
      (∀ z : Lattice d,
        M.P.toMeasure (coefficientLocalBadEvent M n 1 (badH M n) z) ≤
          ENNReal.ofReal (Real.exp (-(cH ^ 2 / (M.delta ^ 2 * Real.log M.delta ^ 2))))) ∧
      ∀ (z : Lattice d) (omega : PotentialSample d),
        omega ∉ coefficientLocalBadEvent M n 1 (badH M n) z →
        ∀ epsilon : ℝ, epsilon ≤ epsStar0 →
          GoodCubeV5RobustHarmonicOscillation (aCutoff M n omega)
            (nativeBox n 1 z) epsilon (eta / 2) (goodCubeReferencePairs Pfam0 n z) := by
    intro M hM n
    refine ⟨(hbadH M hM n).1, fun z omega hom e he => ?_⟩
    have h := (hbadH M hM n).2 z omega hom e he
    rwa [hPFcoe] at h
  have hlocal := goodCubeV5RobustLocalEvent_of_parts (c := c) (C := C) (epsilon := epsilon)
    (J := J) (G := G)
    (Pairs := (goodCubeAuxiliaryPairs X j (-(k : ℤ)) : Set (Cube d × Cube d)))
    bad badH hc.le hccAbs hccEvt hccH h1C hminpos hepsilonCat hepsilonStar habsorb hbad hbadH'
  -- the per-sample readout at the selected constants
  have hread : ∀ M : GMCModel d, M.delta ≤ c → ∀ (n : ℕ) (z : Lattice d)
      (omega : PotentialSample d) (law : Kernel (Vec d) (Path d)),
      LocalDiffusionData (aCutoff M n omega) (aCutoff M n omega) law →
      GoodCubeFiniteLocalTests (aCutoff M n omega) p A (if J ≤ n then ahom M n else 1)
        epsL2 epsH massFraction (Section7Process.timeScale (ahom M))
        (G.image (fun q => ((n : ℤ) - q.1, goodCubeCentre n z + (3 : ℝ) ^ n • q.2)))
        (affinePairTransport (goodCubeCentre n z) ((3 : ℝ) ^ n) ''
          (goodCubeAuxiliaryPairs X j (-(k : ℤ)) : Set (Cube d × Cube d))) →
      LocalTorsionEstimates (aCutoff M n omega) law (Section7Process.timeScale (ahom M))
        p c C (goodCubeCentre n z, (3 : ℝ) ^ n) (goodCubeReferenceFamily Qfam0 n z)
        (goodCubeReferenceFamily Afam0 n z) := by
    intro M hdelta n z omega law hD htests
    refine goodCube_localTorsionEstimates_of_tests_sample hd p A C CE c K theta k0 etaCap
      epsH v0 epsL2 massFraction hA hCEC hAC hexit grid0 j1 jH Pfam0 Qfam0 Afam0 hgeom
      hgeom0.finite_Q hgeom0.side_pos hunit hinside1 depth hdepth j k J G
      (goodCubeAuxiliaryPairs X j (-(k : ℤ)) : Set (Cube d × Cube d)) centers
      hGorig hGquarter hGaux ?_ ?_ ?_ ?_ hlower hccLower hccMass M (hbudget M hdelta)
      n z omega law hD htests
    · intro i x hx
      exact goodCube_auxiliary_pair_catalog_mem centers j k i x hx
    · intro i
      exact (hauxAll i).2.2.1
    · intro i
      exact (hauxAll i).2.2.2.1
    · intro i x hx
      obtain ⟨_hW, hparent, htheta, hhalf', hvol⟩ := (hauxAll i).2.2.2.2 x hx
      exact ⟨hparent, htheta, hhalf', fun y s hs => (hvol y s hs).2⟩
  have hj1' : 1 ≤ j := le_trans (by norm_num) hj
  refine ⟨c, C, eps1, epsilon, A, epsL2, epsH, massFraction, Cdep, j1, jH, J, r, G,
    (goodCubeAuxiliaryPairs X j (-(k : ℤ)) : Set (Cube d × Cube d)),
    hc, h1C, heps1, hepsilon, hhalf, hbudget1, hBr, hNC, hCdep, hccShell.trans hcShell3,
    hcK, hcdelta, hsmall, grid0, Pfam0, Qfam0, Afam0, (fun M n => bad M n ∪ badH M n), hgeom,
    fun n z => catalogue_site_cubes_subset_nativeBox n z G (fun q hq => (hG q hq).2),
    fun n z => auxPairs_site_subset_nativeBox X j k hj1' hX n z, hlocal, hread⟩

/-! ## The exact frozen version-5 conclusion, with no residual hypothesis -/

/-- **The weighted good-cube events lemma, version 5.**  The statement is character for
character the frozen `SubdiffusiveProcess.Frozen.Section9.weighted_good_cube_events` (checked by `example`
below against the frozen declaration's type). -/
theorem weighted_good_cube_events_v5_robust
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) (eta : ℝ) (heta0 : 0 < eta) (_heta1 : eta < 1) :
    ∃ (c C eps0 p0 : ℝ) (Cdep j1 j2 : ℕ),
      0 < c ∧ 0 < C ∧ 0 < eps0 ∧ eps0 ≤ eta / 2 ∧ 2 < p0 ∧
      C * (3 : ℝ) ^ (-(3 * (j1 : ℝ) / 2)) ≤ eta / 2 ∧
      ∃ (grid0 : Finset (Vec d)) (Pfam0 : Set (Cube d × Cube d))
        (Qfam0 Afam0 : Set (Cube d)),
        let transportCube : ℕ → Lattice d → Cube d → Cube d := fun n z Q =>
          (goodCubeCentre n z + (3 : ℝ) ^ n • Q.1, (3 : ℝ) ^ n * Q.2)
        let Pfam : ℕ → Lattice d → Set (Cube d × Cube d) := fun n z =>
          (fun p => (transportCube n z p.1, transportCube n z p.2)) '' Pfam0
        let Qfam : ℕ → Lattice d → Set (Cube d) := fun n z =>
          transportCube n z '' Qfam0
        let Afam : ℕ → Lattice d → Set (Cube d) := fun n z =>
          transportCube n z '' Afam0
        (∀ (n : ℕ) (z : Lattice d),
          IsLocalCubeGeometry grid0 j1 j2 (goodCubeCentre n z, (3 : ℝ) ^ n)
            (Pfam n z) (Qfam n z) (Afam n z)) ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ c →
        ∀ n : ℕ,
        ∃ E : ℕ → Lattice d → Set (_root_.SubdiffusiveProcess.Model.PotentialSample d),
          (∀ z : Lattice d,
            MeasurableSet[restrictedCoefficientSigma
              (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
                _root_.SubdiffusiveProcess.Model.aCutoff M n omega)
              (centeredAxisCube (goodCubeCentre n z) (C * (3 : ℝ) ^ n))] (E 0 z)) ∧
          (∀ j : ℕ, 1 ≤ j → ∀ z : Lattice d,
            MeasurableSet[shellLocalSigma (n + j)
              (centeredAxisCube (goodCubeCentre n z) (C * (3 : ℝ) ^ (n + j)))] (E j z)) ∧
          (∀ (j : ℕ) (z : Lattice d),
            M.P.toMeasure (E j z) ≤
              ENNReal.ofReal (C * Real.exp (-(c * (c / (M.delta ^ 2 * Real.log M.delta ^ 2)) *
                (3 : ℝ) ^ (3 * (j : ℝ) / 2))))) ∧
          IndependentEventScales M.P.toMeasure E ∧
          MultiscaleFiniteRangeIndependentEvents M.P.toMeasure (fun j => Cdep * 3 ^ j) E ∧
          TranslationInvariantEventLaw M.P.toMeasure E ∧
          (∀ z : Lattice d,
            ∀ omega ∈ goodCubeEvent E z,
              ∀ law : Kernel (Vec d) (Path d),
                LocalDiffusionData (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)
                  (_root_.SubdiffusiveProcess.Model.aCutoff M n omega) law →
                LocalTorsionEstimates (_root_.SubdiffusiveProcess.Model.aCutoff M n omega) law
                    (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
                      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M))
                    p0 c C (goodCubeCentre n z, (3 : ℝ) ^ n) (Qfam n z) (Afam n z) ∧
                  LocalHarmonicOscillation (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)
                    eps0 (Pfam n z)) ∧
          (∀ z : Lattice d,
            ∀ omega : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d,
              (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) ∈ goodCubeEvent E z →
              ∀ law : Kernel (Vec d) (Path d),
                LocalDiffusionData (_root_.SubdiffusiveProcess.Model.aAnchored M omega)
                  (_root_.SubdiffusiveProcess.Model.aAnchored M omega) law →
                LocalTorsionEstimates (_root_.SubdiffusiveProcess.Model.aAnchored M omega) law
                    (SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.timeScale
                      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M))
                    p0 c C (goodCubeCentre n z, (3 : ℝ) ^ n) (Qfam n z) (Afam n z) ∧
                  LocalHarmonicOscillation (_root_.SubdiffusiveProcess.Model.aAnchored M omega)
                    eps0 (Pfam n z)) := by
  obtain ⟨p, hp, hpkg⟩ := exists_goodCube_selected_robust_package_v5 d hd
  exact weighted_good_cube_events_v5_of_robustPackage d eta heta0 p hp (hpkg eta heta0)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.RobustGoodCube




