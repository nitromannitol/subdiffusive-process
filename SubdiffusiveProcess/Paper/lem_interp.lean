module

public import SubdiffusiveProcess.Paper.lem_interp_averaging
public import SubdiffusiveProcess.Paper.lem_interp_scale_bound
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Set
open SubdiffusiveProcess
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



lemma aux_lem_interp_core {d : ℕ} (hd : 1 ≤ d) {alpha beta : ℝ}
    (hb : 0 < beta) (hba : beta < alpha) (ha : alpha ≤ 1)
    {Cs N A B r : ℝ} (hCs : 0 < Cs) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hrA : r ≤ A) (hBA : B ≤ A)
    (hbound : ∀ h : ℝ, 0 < h → h ≤ 1 →
      N ≤ Cs * (r * h ^ (alpha - beta) + h ^ (-(d : ℝ) / 2 - beta) * B)) :
    N ≤ 2 * Cs * A ^ (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)) *
          B ^ ((alpha - beta) / (alpha + (d : ℝ) / 2)) := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hEpos : 0 < alpha + (d : ℝ) / 2 := by linarith
  have hγpos : 0 < alpha - beta := sub_pos.mpr hba
  have hEθ : (alpha + (d : ℝ) / 2) * ((alpha - beta) / (alpha + (d : ℝ) / 2)) =
      alpha - beta := mul_div_cancel₀ _ (ne_of_gt hEpos)
  have hθpos : 0 < (alpha - beta) / (alpha + (d : ℝ) / 2) := div_pos hγpos hEpos
  have h1θ : 0 ≤ 1 - (alpha - beta) / (alpha + (d : ℝ) / 2) := by
    rw [sub_nonneg]
    exact (div_le_one hEpos).mpr (by linarith)
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · have hBz : B = 0 := hB0.symm
    rw [show 2 * Cs * A ^ (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)) *
        B ^ ((alpha - beta) / (alpha + (d : ℝ) / 2)) = 0 by
        rw [hBz, Real.zero_rpow (ne_of_gt hθpos), mul_zero]]
    have hb0 : ∀ h : ℝ, 0 < h → h ≤ 1 → N ≤ Cs * (r * h ^ (alpha - beta)) := by
      intro h hh hh1
      have hthis := hbound h hh hh1
      rw [hBz, mul_zero, add_zero] at hthis
      exact hthis
    rcases le_or_gt (Cs * r) 0 with hcr | hcr
    · have h1 := hb0 1 one_pos le_rfl
      rw [Real.one_rpow, mul_one] at h1
      linarith
    · refine le_of_forall_pos_le_add (fun ε hε => ?_)
      have hcrpos : 0 < Cs * r := hcr
      have hεcr : 0 < ε / (Cs * r) := div_pos hε hcrpos
      set t : ℝ := min 1 ((ε / (Cs * r)) ^ (1 / (alpha - beta))) with htdef
      have htpos : 0 < t := lt_min one_pos (Real.rpow_pos_of_pos hεcr _)
      have htle1 : t ≤ 1 := min_le_left _ _
      have htle : t ≤ (ε / (Cs * r)) ^ (1 / (alpha - beta)) := min_le_right _ _
      have htpow : t ^ (alpha - beta) ≤ ε / (Cs * r) := by
        have h := Real.rpow_le_rpow (le_of_lt htpos) htle (le_of_lt hγpos)
        rwa [← Real.rpow_mul (le_of_lt hεcr) (1 / (alpha - beta)) (alpha - beta),
          one_div, inv_mul_cancel₀ (ne_of_gt hγpos), Real.rpow_one] at h
      have hN1 := hb0 t htpos htle1
      have h2 : Cs * (r * t ^ (alpha - beta)) ≤ ε := by
        rw [show Cs * (r * t ^ (alpha - beta)) = (Cs * r) * t ^ (alpha - beta) by ring]
        calc (Cs * r) * t ^ (alpha - beta) ≤ (Cs * r) * (ε / (Cs * r)) :=
              mul_le_mul_of_nonneg_left htpow (le_of_lt hcrpos)
          _ = ε := by rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hcrpos)]
      linarith
  · have hApos : 0 < A := lt_of_lt_of_le hBpos hBA
    rcases le_or_gt B r with hBr | hrB
    · have hrpos : 0 < r := lt_of_lt_of_le hBpos hBr
      set h : ℝ := (B / r) ^ (1 / (alpha + (d : ℝ) / 2)) with hhdef
      have hBrdn : 0 ≤ B / r := (div_pos hBpos hrpos).le
      have hBrdpos : 0 < B / r := div_pos hBpos hrpos
      have hBrdle1 : B / r ≤ 1 := (div_le_one hrpos).mpr hBr
      have hhpos : 0 < h := Real.rpow_pos_of_pos hBrdpos _
      have hhle1 : h ≤ 1 := by
        have hthis := Real.rpow_le_rpow hBrdn hBrdle1
          (by positivity : (0 : ℝ) ≤ 1 / (alpha + (d : ℝ) / 2))
        rwa [Real.one_rpow] at hthis
      have hhE : h ^ (alpha + (d : ℝ) / 2) = B / r := by
        rw [hhdef, ← Real.rpow_mul hBrdn (1 / (alpha + (d : ℝ) / 2)) (alpha + (d : ℝ) / 2),
          one_div, inv_mul_cancel₀ (ne_of_gt hEpos), Real.rpow_one]
      have hh1 : h ^ (alpha - beta) = (B / r) ^ ((alpha - beta) / (alpha + (d : ℝ) / 2)) := by
        calc h ^ (alpha - beta) =
              h ^ ((alpha + (d : ℝ) / 2) * ((alpha - beta) / (alpha + (d : ℝ) / 2))) := by rw [hEθ]
          _ = (h ^ (alpha + (d : ℝ) / 2)) ^ ((alpha - beta) / (alpha + (d : ℝ) / 2)) :=
              Real.rpow_mul hhpos.le _ _
          _ = (B / r) ^ ((alpha - beta) / (alpha + (d : ℝ) / 2)) := by rw [hhE]
      have hdiv : (B / r) ^ ((alpha - beta) / (alpha + (d : ℝ) / 2)) * r =
          B ^ ((alpha - beta) / (alpha + (d : ℝ) / 2)) *
            r ^ (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)) := by
        rw [Real.div_rpow hBpos.le hrpos.le, div_eq_mul_inv,
          Real.rpow_sub hrpos 1 ((alpha - beta) / (alpha + (d : ℝ) / 2)), Real.rpow_one,
          div_eq_mul_inv]
        ring
      have key1 : r * h ^ (alpha - beta) =
          B ^ ((alpha - beta) / (alpha + (d : ℝ) / 2)) *
            r ^ (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)) := by
        rw [hh1]
        calc r * (B / r) ^ ((alpha - beta) / (alpha + (d : ℝ) / 2))
            = (B / r) ^ ((alpha - beta) / (alpha + (d : ℝ) / 2)) * r := by ring
          _ = _ := hdiv
      have hδ_eq : h ^ (-(d : ℝ) / 2 - beta) * B = r * h ^ (alpha - beta) := by
        have hB_eq : B = h ^ (alpha + (d : ℝ) / 2) * r := by
          rw [hhE, div_mul_cancel₀ B (ne_of_gt hrpos)]
        rw [hB_eq, ← mul_assoc,
          ← Real.rpow_add hhpos (-(d : ℝ) / 2 - beta) (alpha + (d : ℝ) / 2)]
        rw [show -(d : ℝ) / 2 - beta + (alpha + (d : ℝ) / 2) = alpha - beta by ring]
        ring
      have hcomb : r * h ^ (alpha - beta) + h ^ (-(d : ℝ) / 2 - beta) * B =
          2 * (B ^ ((alpha - beta) / (alpha + (d : ℝ) / 2)) *
            r ^ (1 - (alpha - beta) / (alpha + (d : ℝ) / 2))) := by
        rw [key1, hδ_eq, key1]
        ring
      have hN := hbound h hhpos hhle1
      rw [hcomb] at hN
      have h2 : B ^ ((alpha - beta) / (alpha + (d : ℝ) / 2)) *
            r ^ (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)) ≤
          A ^ (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)) *
            B ^ ((alpha - beta) / (alpha + (d : ℝ) / 2)) := by
        calc B ^ ((alpha - beta) / (alpha + (d : ℝ) / 2)) *
              r ^ (1 - (alpha - beta) / (alpha + (d : ℝ) / 2))
            ≤ B ^ ((alpha - beta) / (alpha + (d : ℝ) / 2)) *
              A ^ (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)) :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr hrA h1θ)
                (Real.rpow_nonneg hBpos.le _)
          _ = A ^ (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)) *
              B ^ ((alpha - beta) / (alpha + (d : ℝ) / 2)) := by ring
      have hfin : Cs * (2 * (B ^ ((alpha - beta) / (alpha + (d : ℝ) / 2)) *
            r ^ (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)))) ≤
          2 * Cs * A ^ (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)) *
            B ^ ((alpha - beta) / (alpha + (d : ℝ) / 2)) := by
        calc Cs * (2 * (B ^ ((alpha - beta) / (alpha + (d : ℝ) / 2)) *
              r ^ (1 - (alpha - beta) / (alpha + (d : ℝ) / 2))))
            = 2 * Cs * (B ^ ((alpha - beta) / (alpha + (d : ℝ) / 2)) *
              r ^ (1 - (alpha - beta) / (alpha + (d : ℝ) / 2))) := by ring
          _ ≤ 2 * Cs * (A ^ (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)) *
              B ^ ((alpha - beta) / (alpha + (d : ℝ) / 2))) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = 2 * Cs * A ^ (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)) *
              B ^ ((alpha - beta) / (alpha + (d : ℝ) / 2)) := by ring
      linarith [hN, hfin]
    · have hN := hbound 1 one_pos le_rfl
      simp only [Real.one_rpow, mul_one, one_mul] at hN
      have hBle : B ≤ A ^ (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)) *
          B ^ ((alpha - beta) / (alpha + (d : ℝ) / 2)) := by
        have hsum : (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)) +
            ((alpha - beta) / (alpha + (d : ℝ) / 2)) = 1 := by ring
        calc B = B ^ (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)) *
              B ^ ((alpha - beta) / (alpha + (d : ℝ) / 2)) := by
              rw [← Real.rpow_add hBpos (1 - (alpha - beta) / (alpha + (d : ℝ) / 2))
                ((alpha - beta) / (alpha + (d : ℝ) / 2)), hsum, Real.rpow_one]
          _ ≤ A ^ (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)) *
              B ^ ((alpha - beta) / (alpha + (d : ℝ) / 2)) :=
              mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hBpos.le hBA h1θ)
                (Real.rpow_nonneg hBpos.le _)
      have hfin : Cs * (r + B) ≤ 2 * Cs * A ^ (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)) *
            B ^ ((alpha - beta) / (alpha + (d : ℝ) / 2)) := by
        calc Cs * (r + B) ≤ Cs * (2 * B) := by
              apply mul_le_mul_of_nonneg_left _ hCs.le
              linarith [hrB.le]
          _ = 2 * Cs * B := by ring
          _ ≤ 2 * Cs * (A ^ (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)) *
              B ^ ((alpha - beta) / (alpha + (d : ℝ) / 2))) :=
              mul_le_mul_of_nonneg_left hBle (by positivity)
          _ = 2 * Cs * A ^ (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)) *
              B ^ ((alpha - beta) / (alpha + (d : ℝ) / 2)) := by ring
      linarith [hN, hfin]

theorem lem_interp (d : ℕ) (hd : 1 ≤ d) (alpha beta : ℝ) (hb : 0 < beta)
    (hba : beta < alpha) (ha : alpha ≤ 1) :
    let Q0 := centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num)
    let S := closure (Q0 : Set (SpatialCoordinates d))
    let theta := (alpha - beta) / (alpha + (d : ℝ) / 2)
    ∃ C : ℝ, 0 < C ∧
      ∀ v : SpatialCoordinates d → ℝ, _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha S v →
        _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S v ∧
          _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta S v ≤
            C * ((eLpNorm v 2 (volume.restrict (Q0 : Set (SpatialCoordinates d)))).toReal) ^ theta *
              (_root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha S v) ^ (1 - theta) := by
  dsimp only
  have ha0 : 0 < alpha := lt_trans hb hba
  obtain ⟨Ca, hCapos, hvaver⟩ := lem_interp_averaging d hd alpha ha0 ha
  obtain ⟨Cs, hCspos, hvscale⟩ := lem_interp_scale_bound d hd alpha beta hb hba ha
  refine ⟨2 * Cs, by positivity, ?_⟩
  intro v hv
  have hvs := hvscale v hv
  refine ⟨hvs.1, ?_⟩
  have hr : 0 ≤ _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm alpha
      (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d))) v := by
    rw [_root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm, _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet]
    apply Real.sSup_nonneg
    rintro w ⟨x, hx, y, hy, hxy, rfl⟩
    exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) alpha)
  have hsupv : 0 ≤ sSup {w : ℝ | ∃ x ∈ closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d)), w = |v x|} :=
    Real.sSup_nonneg (by rintro w ⟨x, hx, rfl⟩; exact abs_nonneg _)
  have hA : 0 ≤ _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
      (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d))) v := by
    simp only [_root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm]
    linarith
  have hrA : _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm alpha
      (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d))) v ≤
      _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
        (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d))) v := by
    simp only [_root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm]
    linarith
  have hB : 0 ≤ (eLpNorm v 2
      (volume.restrict (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d)))).toReal :=
    ENNReal.toReal_nonneg
  have hmeas : MeasurableSet
      (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d)) := by
    rw [centeredCube_eq_pi (0 : SpatialCoordinates d) (r := 1) (by norm_num)]
    exact MeasurableSet.pi Set.countable_univ (fun i _ => isOpen_Ioo.measurableSet)
  have hbdd : BddAbove {w : ℝ | ∃ x ∈ closure
      (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d)), w = |v x|} := by
    refine ⟨Ca * (eLpNorm v 2
        (volume.restrict (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d)))).toReal +
        _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm alpha
          (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d))) v, ?_⟩
    rintro w ⟨x, hx, rfl⟩
    have hh := (hvaver v hv).2 1 one_pos le_rfl x hx
    simpa only [Real.one_rpow, mul_one] using hh
  have hL2 : (eLpNorm v 2
      (volume.restrict (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d)))).toReal ≤
      _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
        (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d))) v := by
    have hpwise : ∀ᵐ x ∂(volume.restrict
        (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d))),
        ‖v x‖ ≤ sSup {w : ℝ | ∃ x ∈ closure
          (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d)), w = |v x|} :=
      ae_restrict_of_forall_mem hmeas (fun x hx => by
        have hxS : x ∈ closure
            (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d)) :=
          subset_closure hx
        have hthis := le_csSup hbdd ⟨x, hxS, rfl⟩
        simpa only [Real.norm_eq_abs] using hthis)
    have hcont := aux_lem_interp_averaging_continuousOn ha0 hr
      (aux_lem_interp_averaging_holder_bound ha0 hv)
    have hmeasV : AEStronglyMeasurable v
        (volume.restrict (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d))) :=
      (hcont.mono subset_closure).aestronglyMeasurable hmeas
    have hle := eLpNorm_le_of_ae_bound
      (μ := volume.restrict
        (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d)))
      (p := 2) (f := v)
      (C := sSup {w : ℝ | ∃ x ∈ closure
        (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d)), w = |v x|}) hmeasV hpwise
    have hvol : volume (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d)) = 1 := by
      rw [show volume (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d)) =
          ENNReal.ofReal ((1 : ℝ) ^ d) from
            centeredCube_volume (0 : SpatialCoordinates d) (r := 1) (by norm_num)]
      simp
    rw [Measure.restrict_apply_univ, hvol] at hle
    simp only [ENNReal.one_rpow, one_mul] at hle
    have h1 := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hle
    rw [ENNReal.toReal_ofReal hsupv] at h1
    exact le_trans h1 (le_add_of_nonneg_right hr)
  have hbound : ∀ h : ℝ, 0 < h → h ≤ 1 →
      _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
          (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d))) v ≤
        Cs * (_root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm alpha
            (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d))) v *
              h ^ (alpha - beta) +
          h ^ (-(d : ℝ) / 2 - beta) * (eLpNorm v 2
            (volume.restrict (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d)))).toReal) := by
    intro h hh hh1
    exact (hvs.2 h hh hh1).2
  have hcore := aux_lem_interp_core hd hb hba ha hCspos hB hr hrA hL2 hbound
  calc _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
        (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d))) v
      ≤ 2 * Cs * (_root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
          (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d))) v) ^
            (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)) *
          ((eLpNorm v 2
            (volume.restrict (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d)))).toReal) ^
            ((alpha - beta) / (alpha + (d : ℝ) / 2)) := hcore
    _ = 2 * Cs * ((eLpNorm v 2
          (volume.restrict (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d)))).toReal) ^
            ((alpha - beta) / (alpha + (d : ℝ) / 2)) *
          (_root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
            (closure (centeredCube (0 : SpatialCoordinates d) (1 : ℝ) (by norm_num) : Set (SpatialCoordinates d))) v) ^
            (1 - (alpha - beta) / (alpha + (d : ℝ) / 2)) := by ring

end SubdiffusiveProcess.Paper
