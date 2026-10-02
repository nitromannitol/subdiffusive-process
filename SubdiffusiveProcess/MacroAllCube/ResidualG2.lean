import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeLargeBox
import SubdiffusiveProcess.CoarseGrainingVocab.OGammaSplit
import Homogenization.Geometry.ConvexDomain

/-!
# (g2) for a boundedly dilated seed law

For `0 < s ≤ 3`, the unit cube dilated by `s` lies in the triadic cube of side
`3`, which is covered by the dimension-only family `shellCoverShifts d 1` of
translated unit cubes.  The `(g2)` observable of `x ↦ g (s x)` is therefore at
most `13` times the sum of the translated unit-cube `(g2)` observables of `g`:
value `≤ G`, gradient `≤ s G ≤ 3 G`, gradient Lipschitz seminorm
`≤ s² G ≤ 9 G` (segment chaining across the cover,
`Section9Support.norm_deriv_sub_le_of_forall_g2_le`).  Stationarity and the
loss-free Orlicz sum then give `(g2)` for the dilated law at the scale
`13 · card · δ`.  No independence between the covering cubes is used, and the
seed law is not assumed scale invariant.
-/

set_option autoImplicit false

open MeasureTheory Homogenization
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab (shellCoverShifts shellCoverCenter)

noncomputable section

namespace ResidualModel

variable {d : ℕ}

/-! ## The dimension-only cover -/

/-- The translated unit cubes covering the origin cube of side `3`. -/
abbrev coverShifts (d : ℕ) : Finset (Fin d → ℤ) := shellCoverShifts d 1

/-- The sum of the `(g2)` observables over the covering unit cubes. -/
def coverG2 (g : PotentialField d) : ℝ :=
  ∑ p ∈ coverShifts d,
    PotentialField.g2Observable (PotentialField.translate (shellCoverCenter p) g)

theorem coverG2_nonneg (g : PotentialField d) : 0 ≤ coverG2 g :=
  Finset.sum_nonneg fun _ _ => PotentialField.g2Observable_nonneg _

theorem g2_translate_le_coverG2 (g : PotentialField d) {p : Fin d → ℤ}
    (hp : p ∈ coverShifts d) :
    PotentialField.g2Observable (PotentialField.translate (shellCoverCenter p) g) ≤
      coverG2 g :=
  Finset.single_le_sum
    (f := fun q => PotentialField.g2Observable
      (PotentialField.translate (shellCoverCenter q) g))
    (fun _ _ => PotentialField.g2Observable_nonneg _) hp

/-- The hypothesis form consumed by the translated cover readouts, at centre `0`. -/
theorem forall_g2_le_coverG2 (g : PotentialField d) :
    ∀ p ∈ shellCoverShifts d 1,
      PotentialField.g2Observable
          (PotentialField.translate (0 + shellCoverCenter p) g) ≤ coverG2 g := by
  intro p hp
  rw [zero_add]
  exact g2_translate_le_coverG2 g hp

theorem smul_mem_openCubeSet_one {s : ℝ} (hs0 : 0 < s) (hs3 : s ≤ 3) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d 0)) :
    s • x ∈ openCubeSet (originCube d 1) := by
  rw [mem_openCubeSet_originCube_iff] at hx ⊢
  intro i
  have hxi := hx i
  simp only [zpow_zero, mul_one, zpow_one] at hxi ⊢
  have hsm : (s • x) i = s * x i := rfl
  rw [hsm]
  have h1 : 0 < s * (1 / 2 - x i) := mul_pos hs0 (by linarith [hxi.2])
  have h2 : 0 < s * (x i + 1 / 2) := mul_pos hs0 (by linarith [hxi.1])
  constructor <;> nlinarith

/-- Membership in the cover's cube, in the recentred form of the readouts. -/
theorem smul_sub_zero_mem {s : ℝ} (hs0 : 0 < s) (hs3 : s ≤ 3) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d 0)) :
    s • x - 0 ∈ openCubeSet (originCube d 1) := by
  rw [sub_zero]
  exact smul_mem_openCubeSet_one hs0 hs3 hx

/-! ## The three pieces of the `(g2)` observable -/

theorem abs_apply_le_coverG2 (g : PotentialField d) {w : Vec d}
    (hw : w ∈ openCubeSet (originCube d 1)) :
    |g w| ≤ coverG2 g := by
  obtain ⟨p, hp, hwp⟩ := SubdiffusiveProcess.CoarseGrainingVocab.exists_shellCoverShift_mem hw
  rw [mem_translateSet_iff_sub_mem] at hwp
  have h := PotentialField.abs_apply_le_g2Observable
    (PotentialField.translate (shellCoverCenter p) g) hwp
  rw [PotentialField.translate_apply, sub_add_cancel] at h
  exact h.trans (g2_translate_le_coverG2 g hp)

theorem unitCubeValueNorm_spatialScale_le {s : ℝ} (hs0 : 0 < s) (hs3 : s ≤ 3)
    (g : PotentialField d) :
    PotentialField.unitCubeValueNorm (PotentialField.spatialScale s g) ≤ coverG2 g := by
  apply csSup_le (Set.range_nonempty _)
  rintro b ⟨o, rfl⟩
  cases o with
  | none => exact coverG2_nonneg g
  | some x =>
      show |PotentialField.spatialScale s g x.1| ≤ _
      rw [PotentialField.spatialScale_apply]
      exact abs_apply_le_coverG2 g (smul_mem_openCubeSet_one hs0 hs3 x.2)

theorem unitCubeDerivNorm_spatialScale_le_cover {s : ℝ} (hs0 : 0 < s) (hs3 : s ≤ 3)
    (g : PotentialField d) :
    PotentialField.unitCubeDerivNorm (PotentialField.spatialScale s g) ≤
      3 * coverG2 g := by
  apply csSup_le (Set.range_nonempty _)
  rintro b ⟨o, rfl⟩
  cases o with
  | none => exact mul_nonneg (by norm_num) (coverG2_nonneg g)
  | some x =>
      show ‖PotentialField.deriv (PotentialField.spatialScale s g) x.1‖ ≤ _
      rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.deriv_spatialScale, norm_smul,
        Real.norm_eq_abs, abs_of_pos hs0]
      have h := SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.norm_deriv_le_of_forall_g2_le
        g 0 (forall_g2_le_coverG2 g) (smul_sub_zero_mem hs0 hs3 x.2)
      exact mul_le_mul hs3 h (norm_nonneg _) (by norm_num)

theorem unitCubeDerivLipschitzSeminorm_spatialScale_le_cover {s : ℝ} (hs0 : 0 < s)
    (hs3 : s ≤ 3) (g : PotentialField d) :
    PotentialField.unitCubeDerivLipschitzSeminorm (PotentialField.spatialScale s g) ≤
      9 * coverG2 g := by
  have hG := coverG2_nonneg g
  have hconv : Convex ℝ (openCubeSet (originCube d 1)) := convex_openCubeSet _
  have hsub : ∀ u ∈ openCubeSet (originCube d 1), u - 0 ∈ openCubeSet (originCube d 1) := by
    intro u hu
    rwa [sub_zero]
  apply csSup_le (Set.range_nonempty _)
  rintro b ⟨o, rfl⟩
  cases o with
  | none => exact mul_nonneg (by norm_num) hG
  | some p =>
      have hne : p.val.fst.val ≠ p.val.snd.val := fun hEq => p.property (Subtype.ext hEq)
      have hdist : 0 < dist p.val.fst.val p.val.snd.val := dist_pos.mpr hne
      have hchain := SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.norm_deriv_sub_le_of_forall_g2_le
        g 0 (forall_g2_le_coverG2 g) hconv hsub
        (smul_mem_openCubeSet_one hs0 hs3 p.val.fst.2)
        (smul_mem_openCubeSet_one hs0 hs3 p.val.snd.2)
      have hsV : ‖s • p.val.fst.val - s • p.val.snd.val‖ =
          s * ‖p.val.fst.val - p.val.snd.val‖ := by
        rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
      rw [hsV] at hchain
      show dist (PotentialField.deriv (PotentialField.spatialScale s g) p.val.fst.val)
          (PotentialField.deriv (PotentialField.spatialScale s g) p.val.snd.val) /
          dist p.val.fst.val p.val.snd.val ≤ _
      rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.deriv_spatialScale,
        SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.deriv_spatialScale,
        div_le_iff₀ hdist, dist_eq_norm, dist_eq_norm,
        show s • PotentialField.deriv g (s • p.val.fst.val) -
            s • PotentialField.deriv g (s • p.val.snd.val) =
            s • (PotentialField.deriv g (s • p.val.fst.val) -
              PotentialField.deriv g (s • p.val.snd.val)) by rw [smul_sub],
        norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
      have hn : 0 ≤ ‖p.val.fst.val - p.val.snd.val‖ := norm_nonneg _
      have hss : s * s ≤ 9 := by nlinarith
      calc s * ‖PotentialField.deriv g (s • p.val.fst.val) -
              PotentialField.deriv g (s • p.val.snd.val)‖
          ≤ s * (coverG2 g * (s * ‖p.val.fst.val - p.val.snd.val‖)) :=
            mul_le_mul_of_nonneg_left hchain hs0.le
        _ = (s * s) * (coverG2 g * ‖p.val.fst.val - p.val.snd.val‖) := by ring
        _ ≤ 9 * (coverG2 g * ‖p.val.fst.val - p.val.snd.val‖) :=
            mul_le_mul_of_nonneg_right hss (mul_nonneg hG hn)
        _ = 9 * coverG2 g * ‖p.val.fst.val - p.val.snd.val‖ := by ring

/-- **The deterministic finite-cover estimate.**  For `0 < s ≤ 3` the `(g2)`
observable of `x ↦ g (s x)` is at most `13` times the sum of the translated
unit-cube `(g2)` observables of `g` over the dimension-only cover. -/
theorem g2Observable_spatialScale_le {s : ℝ} (hs0 : 0 < s) (hs3 : s ≤ 3)
    (g : PotentialField d) :
    PotentialField.g2Observable (PotentialField.spatialScale s g) ≤ 13 * coverG2 g := by
  have h1 := unitCubeValueNorm_spatialScale_le hs0 hs3 g
  have h2 := unitCubeDerivNorm_spatialScale_le_cover hs0 hs3 g
  have h3 := unitCubeDerivLipschitzSeminorm_spatialScale_le_cover hs0 hs3 g
  unfold PotentialField.g2Observable
  linarith

/-! ## Orlicz algebra -/

/-- Change of variables for `OGammaLE` along a pushforward. -/
theorem ogammaLE_map_iff {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {T : Ω → Ω'} (hT : AEMeasurable T μ) {σ A : ℝ} {X : Ω' → ℝ}
    (hX : AEMeasurable X (Measure.map T μ)) :
    SubdiffusiveProcess.OGammaLE (Measure.map T μ) σ A X ↔ SubdiffusiveProcess.OGammaLE μ σ A (fun ω => X (T ω)) := by
  have hmeas : AEStronglyMeasurable
      (fun z => Real.exp ((A⁻¹ * max (X z) 0) ^ σ)) (Measure.map T μ) :=
    (SubdiffusiveProcess.CoarseGrainingVocab.OGamma.aemeasurable_integrand σ A hX).aestronglyMeasurable
  constructor
  · rintro ⟨hi, hb⟩
    exact ⟨(integrable_map_measure hmeas hT).mp hi, by rwa [← integral_map hT hmeas]⟩
  · rintro ⟨hi, hb⟩
    exact ⟨(integrable_map_measure hmeas hT).mpr hi, by rwa [integral_map hT hmeas]⟩

/-- **Loss-free finite sums.**  A sum of `n` variables each `O_Γσ(A)` is
`O_Γσ(n A)`, for `σ ≥ 1`; no independence is used. -/
theorem ogammaLE_finset_sum {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {σ A : ℝ} (hA : 0 < A) (hσ : 1 ≤ σ) {s : Finset ι} (hs : s.Nonempty)
    {X : ι → Ω → ℝ} (hX : ∀ i ∈ s, AEMeasurable (X i) μ)
    (h : ∀ i ∈ s, SubdiffusiveProcess.OGammaLE μ σ A (X i)) :
    SubdiffusiveProcess.OGammaLE μ σ ((s.card : ℝ) * A) (fun ω => ∑ i ∈ s, X i ω) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
      simpa only [Finset.card_singleton, Nat.cast_one, one_mul, Finset.sum_singleton]
        using h a (Finset.mem_singleton_self a)
  | cons a s ha hs ih =>
      have hXa := hX a (Finset.mem_cons_self a s)
      have hOa := h a (Finset.mem_cons_self a s)
      have hXs : ∀ i ∈ s, AEMeasurable (X i) μ :=
        fun i hi => hX i (Finset.mem_cons_of_mem hi)
      have hOs : ∀ i ∈ s, SubdiffusiveProcess.OGammaLE μ σ A (X i) :=
        fun i hi => h i (Finset.mem_cons_of_mem hi)
      have ih' := ih hXs hOs
      have hsA : 0 < (s.card : ℝ) * A :=
        mul_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr hs)) hA
      have hsum : AEMeasurable (fun ω => ∑ i ∈ s, X i ω) μ :=
        Finset.aemeasurable_fun_sum s hXs
      have hadd := SubdiffusiveProcess.CoarseGrainingVocab.OGamma.ogammaLE_add hA hsA hσ hXa hsum hOa ih'
      have hcard : ((Finset.cons a s ha).card : ℝ) * A = A + (s.card : ℝ) * A := by
        rw [Finset.card_cons]
        push_cast
        ring
      rw [hcard]
      simpa only [Finset.sum_cons] using hadd

/-! ## `(g2)` for the dilated law -/

/-- The dimension-only disorder factor: `13` times the number of covering cubes. -/
def residualDisorderFactor (d : ℕ) : ℝ := 13 * ((coverShifts d).card : ℝ)

theorem coverShifts_card (d : ℕ) : (coverShifts d).card = 19 ^ d := by
  rw [coverShifts, SubdiffusiveProcess.CoarseGrainingVocab.card_shellCoverShifts]
  rfl

theorem residualDisorderFactor_eq (d : ℕ) :
    residualDisorderFactor d = 13 * (19 : ℝ) ^ d := by
  rw [residualDisorderFactor, coverShifts_card]
  push_cast
  rfl

theorem residualDisorderFactor_pos (d : ℕ) : 0 < residualDisorderFactor d := by
  rw [residualDisorderFactor_eq]
  positivity

theorem one_le_residualDisorderFactor (d : ℕ) : 1 ≤ residualDisorderFactor d := by
  rw [residualDisorderFactor_eq]
  have h : (1 : ℝ) ≤ (19 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  linarith

/-- **(g2) on the enlarged cube.**  If a seed law `μ` is stationary and
satisfies `(g2)` at scale `δ`, then its image under `x ↦ g (s x)`, `0 < s ≤ 3`,
satisfies `(g2)` at scale `residualDisorderFactor d * δ`.  The factor depends
only on the dimension. -/
theorem ogammaLE_g2Observable_map_spatialScale (μ : Measure (PotentialField d))
    {δ s : ℝ} (hδ : 0 < δ) (hs0 : 0 < s) (hs3 : s ≤ 3)
    (hstat : ∀ z : Vec d, Measure.map (PotentialField.translate z) μ = μ)
    (hG2 : SubdiffusiveProcess.OGammaLE μ 2 δ PotentialField.g2Observable) :
    SubdiffusiveProcess.OGammaLE (Measure.map (PotentialField.spatialScale s) μ) 2
      (residualDisorderFactor d * δ) PotentialField.g2Observable := by
  have hS : Measurable (PotentialField.spatialScale (d := d) s) :=
    (PotentialField.continuous_spatialScale s).measurable
  have hcard : 0 < ((coverShifts d).card : ℝ) :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d 1))
  rw [ogammaLE_map_iff hS.aemeasurable
    PotentialField.g2Observable_measurable.aemeasurable]
  -- every covering unit cube carries `(g2)` at scale `δ`, by stationarity
  have hone : ∀ p ∈ coverShifts d, SubdiffusiveProcess.OGammaLE μ 2 δ
      (fun g => PotentialField.g2Observable
        (PotentialField.translate (shellCoverCenter p) g)) := by
    intro p _
    exact SubdiffusiveProcess.CoarseGrainingVocab.OGamma.ogammaLE_comp_measurePreserving
      ⟨PotentialField.measurable_translate _, hstat _⟩
      PotentialField.g2Observable_measurable.aemeasurable hG2
  have hmeas : ∀ p ∈ coverShifts d, AEMeasurable
      (fun g : PotentialField d => PotentialField.g2Observable
        (PotentialField.translate (shellCoverCenter p) g)) μ := by
    intro p _
    exact (PotentialField.g2Observable_measurable.comp
      (PotentialField.measurable_translate _)).aemeasurable
  have hsum := ogammaLE_finset_sum hδ (by norm_num : (1 : ℝ) ≤ 2)
    (SubdiffusiveProcess.CoarseGrainingVocab.shellCoverShifts_nonempty d 1) hmeas hone
  have hcover : SubdiffusiveProcess.OGammaLE μ 2 (((coverShifts d).card : ℝ) * δ) coverG2 := hsum
  have hthirteen := SubdiffusiveProcess.CoarseGrainingVocab.OGamma.ogammaLE_const_mul
    (mul_pos hcard hδ) (by norm_num : (0 : ℝ) < 13) hcover
  have hscale : residualDisorderFactor d * δ = 13 * (((coverShifts d).card : ℝ) * δ) := by
    rw [residualDisorderFactor]
    ring
  rw [hscale]
  exact SubdiffusiveProcess.CoarseGrainingVocab.OGamma.ogammaLE_of_ae_le
    (mul_pos (by norm_num) (mul_pos hcard hδ)) (by norm_num)
    (PotentialField.g2Observable_measurable.comp hS).aemeasurable
    (Filter.Eventually.of_forall fun g => g2Observable_spatialScale_le hs0 hs3 g)
    hthirteen

end ResidualModel



