module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryMeanControlCube
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6OddClass.SeamCore

@[expose] public section

/-!
# The doubled flush cube inside the reflected boundary window

The projected cell is centered at the coordinatewise clamped `wellPlacedCentre`, so no secondary boundary-window construction is needed.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization MeasureTheory InnerProductSpace
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open MeanControlGeometry MeanControlSchauder

noncomputable section

variable {d : ℕ}

private theorem windowLo_wellPlacedCentre {m k : ℤ} (_hkm : k ≤ m)
    (q : Vec d) (j : Fin d) :
    windowLo (wellPlacedCentre q m k) m k j =
      wellPlacedCentre q m k j - (1 / 2 : ℝ) * (3 : ℝ) ^ k := by
  rw [windowLo, max_eq_left]
  have h := neg_wellPlacedHalfGap_le_wellPlacedCentre q m k j
  rw [wellPlacedHalfGap] at h
  linarith

private theorem windowHi_wellPlacedCentre {m k : ℤ} (hkm : k ≤ m)
    (q : Vec d) (j : Fin d) :
    windowHi (wellPlacedCentre q m k) m k j =
      wellPlacedCentre q m k j + (1 / 2 : ℝ) * (3 : ℝ) ^ k := by
  rw [windowHi, min_eq_left]
  have h := wellPlacedCentre_le_wellPlacedHalfGap hkm q j
  rw [wellPlacedHalfGap] at h
  linarith

private theorem reflectedLo_le_wellPlacedCentre_sub {m k : ℤ} (hkm : k < m)
    (q : Vec d) (j : Fin d) :
    reflectedLo (wellPlacedCentre q m k) m k j ≤
      wellPlacedCentre q m k j - (1 / 2 : ℝ) * (3 : ℝ) ^ k := by
  by_cases hlow : MeetsLowerFace (wellPlacedCentre q m k) m k j
  · rw [reflectedLo_of_meetsLowerFace hlow,
      windowHi_wellPlacedCentre hkm.le]
    have hc := neg_wellPlacedHalfGap_le_wellPlacedCentre q m k j
    have hmeet : wellPlacedCentre q m k j -
        (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤
        -(1 / 2 : ℝ) * (3 : ℝ) ^ m := hlow
    have hkpos : 0 < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
    rw [wellPlacedHalfGap] at hc
    linarith only [hc, hkpos]
  · rw [reflectedLo_of_not_meetsLowerFace hlow,
      windowLo_wellPlacedCentre hkm.le]

private theorem wellPlacedCentre_add_le_reflectedHi {m k : ℤ} (hkm : k < m)
    (q : Vec d) (j : Fin d) :
    wellPlacedCentre q m k j + (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤
      reflectedHi (wellPlacedCentre q m k) m k j := by
  by_cases hup : MeetsUpperFace (wellPlacedCentre q m k) m k j
  · rw [reflectedHi_of_meetsUpperFace hup,
      windowLo_wellPlacedCentre hkm.le]
    have hc := wellPlacedCentre_le_wellPlacedHalfGap hkm.le q j
    have hmeet : (1 / 2 : ℝ) * (3 : ℝ) ^ m ≤
        wellPlacedCentre q m k j +
          (1 / 2 : ℝ) * (3 : ℝ) ^ k := hup
    have hkpos : 0 < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
    rw [wellPlacedHalfGap] at hc
    linarith only [hc, hkpos]
  · rw [reflectedHi_of_not_meetsUpperFace hup,
      windowHi_wellPlacedCentre hkm.le]

/-- The cube obtained by doubling a clamped cell through any saturated face is
contained in the reflected window used by the proved odd-extension producer. -/
theorem sealDouble_wellPlacedCentre_subset_reflectedWindow
    {m k : ℤ} (hkm : k < m) {q : Vec d} {i : Fin d} {sg : ℝ}
    (hsg : sg = 1 ∨ sg = -1)
    (hover : wellPlacedHalfGap m k < sg * q i) :
    sealDouble (wellPlacedCentre q m k) ((3 : ℝ) ^ k) i sg ⊆
      reflectedWindow (wellPlacedCentre q m k) m k := by
  intro y hy
  rw [sealDouble, mem_coordBox_iff] at hy
  rw [mem_reflectedWindow_iff]
  intro j
  have hj := hy j
  by_cases hji : j = i
  · subst j
    have hface := wellPlacedCentre_faceLevel hkm.le hsg hover
    rcases hsg with rfl | rfl
    · norm_num at hj
      have hup : MeetsUpperFace (wellPlacedCentre q m k) m k i := by
        rw [MeetsUpperFace]
        linarith only [hface]
      have hlow : ¬ MeetsLowerFace (wellPlacedCentre q m k) m k i :=
        not_meetsLowerFace_of_meetsUpperFace hkm hup
      rw [reflectedLo_of_not_meetsLowerFace hlow,
        reflectedHi_of_meetsUpperFace hup,
        windowLo_wellPlacedCentre hkm.le]
      constructor <;> linarith only [hj.1, hj.2, hface]
    · norm_num at hj
      have hlow : MeetsLowerFace (wellPlacedCentre q m k) m k i := by
        rw [MeetsLowerFace]
        linarith only [hface]
      have hup : ¬ MeetsUpperFace (wellPlacedCentre q m k) m k i := by
        intro hu
        exact (not_meetsLowerFace_of_meetsUpperFace hkm hu) hlow
      rw [reflectedLo_of_meetsLowerFace hlow,
        reflectedHi_of_not_meetsUpperFace hup,
        windowHi_wellPlacedCentre hkm.le]
      constructor <;> linarith only [hj.1, hj.2, hface]
  · rw [ite_eq_right hji, ite_eq_right hji] at hj
    have hlo := reflectedLo_le_wellPlacedCentre_sub hkm q j
    have hhi := wellPlacedCentre_add_le_reflectedHi hkm q j
    constructor <;> linarith only [hj.1, hj.2, hlo, hhi]

/-- A classically harmonic representative which is pointwise odd on the
reflected window has a dimension-only mean bound on the physical clamped
cell.  The symmetrization is global, so the abstract face-odd theorem is used
without strengthening the representative's off-window behavior. -/
theorem exists_abs_volumeAverage_le_normalizedL2On_wellPlacedFaceOdd
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (m k : ℤ) (q : Vec d) (i : Fin d) (sg : ℝ) (V : Vec d → ℝ),
        k < m → (sg = 1 ∨ sg = -1) →
        wellPlacedHalfGap m k < sg * q i →
        (∀ y ∈ reflectedWindow (wellPlacedCentre q m k) m k,
          V (coordFaceReflection
            (sg * ((1 / 2 : ℝ) * (3 : ℝ) ^ m)) i y) = -V y) →
        MemLp V 2 (volume : Measure (Vec d)) →
        HarmonicOnNhd (V ∘
            (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
          ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) ''
            reflectedWindow (wellPlacedCentre q m k) m k) →
        |volumeAverage
            (translatedCube d k (wellPlacedCentre q m k)) V| ≤
          C * normalizedL2On
            (translatedCube d k (wellPlacedCentre q m k))
            (fun y => V y -
              volumeAverage
                (translatedCube d k (wellPlacedCentre q m k)) V) := by
  classical
  obtain ⟨C, hC0, hC⟩ := MeanControlSchauder.exists_abs_le_normalizedL2On_sealCube d
  refine ⟨C, hC0, ?_⟩
  intro m k q i sg V hkm hsg hover hodd hVmem hharm
  let c : Vec d := wellPlacedCentre q m k
  let L : ℝ := (3 : ℝ) ^ k
  let a : ℝ := sg * ((1 / 2 : ℝ) * (3 : ℝ) ^ m)
  let r : Vec d → Vec d := coordFaceReflection a i
  let W : Vec d → ℝ := fun y => (V y - V (r y)) / 2
  let K : Set (Vec d) := sealCube c L
  let D : Set (Vec d) := sealDouble c L i sg
  have hDsub : D ⊆ reflectedWindow c m k := by
    simpa only [D, c, L] using
      sealDouble_wellPlacedCentre_subset_reflectedWindow hkm hsg hover
  have hWV : Set.EqOn W V D := by
    intro y hy
    have hyR := hDsub hy
    have hoddY := hodd y hyR
    dsimp only [W, r, a]
    rw [hoddY]
    ring
  have hWodd : ∀ y, W (coordFaceReflection a i y) = -W y := by
    intro y
    dsimp only [W, r]
    rw [coordFaceReflection_involutive]
    ring
  have hDm : MeasurableSet D := by
    dsimp only [D, sealDouble]
    exact (isOpen_coordBox _ _).measurableSet
  have hWVae : W =ᵐ[volume.restrict D] V := by
    filter_upwards [self_mem_ae_restrict hDm] with y hy
    exact hWV hy
  have hWmem : MemLp W 2 (volume.restrict D) :=
    MemLp.ae_eq hWVae.symm (hVmem.restrict D)
  have hharmD :
      HarmonicOnNhd (V ∘
          (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' D) := by
    intro y hy
    exact hharm y (Set.image_mono hDsub hy)
  have hharmW :
      HarmonicOnNhd (W ∘
          (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' D) :=
    Section6OddClass.harmonicOnNhd_congr_eqOn
      (isOpen_coordBox _ _) hWV hharmD
  let beta : ℝ := volumeAverage K V
  have hharmSub :
      HarmonicOnNhd ((fun y => W y - beta) ∘
          (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' D) :=
    Section6Schauder.harmonicOnNhd_sub_const hharmW beta
  have hface : c i + sg * (L / 2) = a := by
    dsimp only [c, L, a]
    exact MeanControlSchauder.wellPlacedCentre_faceLevel_signed hkm.le hsg hover
  have hmain := hC i sg L c W beta hsg (zpow_pos (by norm_num) k)
    (by simpa only [hface] using hWodd) hWmem hharmSub
  have hKeq : translatedCube d k c = K := by
    rw [translatedCube, cube, MeanControlSchauder.image_add_eq_sealCube]
  have hKD : K ⊆ D := by
    intro y hy
    dsimp only [K, D, sealCube, sealDouble] at hy ⊢
    rw [mem_coordBox_iff] at hy ⊢
    intro j
    have hj := hy j
    by_cases hji : j = i
    · subst j
      have hLpos : 0 < L := by dsimp only [L]; positivity
      rcases hsg with rfl | rfl
      · norm_num
        exact ⟨hj.1, by linarith only [hj.2, hLpos]⟩
      · norm_num
        exact ⟨by linarith only [hj.1, hLpos], hj.2⟩
    · rw [ite_eq_right hji, ite_eq_right hji]
      exact hj
  have hWV_K : Set.EqOn W V K := fun _ hy => hWV (hKD hy)
  have hnorm : normalizedL2On K (fun y => W y - beta) =
      normalizedL2On K (fun y => V y - volumeAverage K V) := by
    apply Section6OddClass.normalizedL2On_congr_ae
    filter_upwards [self_mem_ae_restrict
      (by dsimp only [K, sealCube]; exact (isOpen_coordBox _ _).measurableSet)] with y hy
    rw [hWV_K hy]
  rw [hnorm] at hmain
  simpa only [beta, c, K, hKeq] using hmain

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
