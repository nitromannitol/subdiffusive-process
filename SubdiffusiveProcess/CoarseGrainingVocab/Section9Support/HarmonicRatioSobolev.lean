module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserLocalBoundednessStep
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.HarmonicRatioEnergy

@[expose] public section

/-!
# The localized ratio-sixteen power rung

The constant is chosen before the coefficient, cube, function, and power.
A qualitative local bound justifies the tests and does not occur in the result.
-/
set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Filter Set
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal BigOperators Topology
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Caccioppoli followed by Sobolev, starting from a bundled weak solution. -/
theorem exists_harmonic_ratio_h1_power_sobolev_step {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Vec d → ℝ) (z : Vec d) (r R : ℝ),
        0 < r → r < R → R ≤ 1 →
        AEStronglyMeasurable a (volume.restrict (centeredAxisCube z R)) →
        (∀ᵐ x ∂volume.restrict (centeredAxisCube z R), 1 / 4 ≤ a x ∧ a x ≤ 4) →
        ∀ u : H1Function (centeredAxisCube z R),
          IsWeaklyHarmonicOn a (centeredAxisCube z R) u →
          ∀ M : ℝ, 0 ≤ M →
          (∀ᵐ x ∂volume.restrict (centeredAxisCube z R), |u.toFun x| ≤ M) →
          ∀ s : ℝ, 1 ≤ s →
          eLpNorm (fun x => (max (u.toFun x) 0) ^ s) (moserSobolevExponent d) (volume.restrict (centeredAxisCube z r)) ≤
            ENNReal.ofReal (C * s / (R - r)) * eLpNorm (fun x => (max (u.toFun x) 0) ^ s) 2
              (volume.restrict (centeredAxisCube z R)) := by
  obtain ⟨S, hS, hSob⟩ := exists_moser_cube_sobolev hd
  let C : ℝ := (S : ℝ) * ((d : ℝ) * (768 * ((d : ℝ) + 1)) + 1)
  have hC : 0 < C := mul_pos (by exact_mod_cast hS) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro a z r R hr hrR hR1 ha hab v hu M hM hvM s hs
  have hs0 : 0 ≤ s := by linarith
  have hgap : 0 < R - r := sub_pos.mpr hrR
  have hR : 0 < R := hr.trans hrR
  have hU := isOpenBoundedConvexDomain_axisCube (fun i => z i - R / 2) R
  obtain ⟨u, f, huval, _, hpair⟩ := exists_moser_power_pair hU v hM hvM hs
  rw [← huval]
  obtain ⟨eta, heta, hetac, hetasub, hetaRange, hetaOne, hetaGrad⟩ :=
    exists_moser_cube_cutoff z hrR
  let K : ℝ := 64 * ((d : ℝ) + 1) / (R - r)
  have hK : 0 ≤ K := by positivity
  have hgrad : ∀ x, vecNormSq (euclideanGradient eta x) ≤ K ^ 2 := by
    intro x
    have hdnum : (d : ℝ) ≤ ((d : ℝ) + 1) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) d, sq_nonneg (d : ℝ)]
    refine (hetaGrad x).trans ((mul_le_mul_of_nonneg_right hdnum (sq_nonneg _)).trans_eq ?_)
    dsimp only [K]
    ring
  let w := u.mulContDiffHasCompactSupport heta hetac
  have hcoord (i : Fin d) :
      eLpNorm (fun x => w.grad x i) 2 (volume.restrict (centeredAxisCube z R)) ≤
        ENNReal.ofReal (12 * s * K) * eLpNorm u.toFun 2 (volume.restrict (centeredAxisCube z R)) :=
    harmonic_ratio_power_cutoff_gradient_l2 hU ha hab v u f hu hs hpair heta hetac hetasub hetaRange hK hgrad i
  have hvalue := moser_cutoff_value_l2 u heta hetac hetaRange
  have hinner : eLpNorm u.toFun (moserSobolevExponent d)
      (volume.restrict (centeredAxisCube z r)) ≤
        eLpNorm w.toFun (moserSobolevExponent d) (volume.restrict (centeredAxisCube z R)) := by
    have heq : u.toFun =ᵐ[volume.restrict (centeredAxisCube z r)] w.toFun := by
      filter_upwards [ae_restrict_mem (isOpen_axisCube _ _).measurableSet] with x hx
      rw [H1Function.mulContDiffHasCompactSupport_toFun]
      dsimp only
      rw [hetaOne x hx, one_mul]
    rw [eLpNorm_congr_ae heq]
    exact eLpNorm_mono_measure _ (Measure.restrict_mono (centeredAxisCube_mono hrR.le) le_rfl)
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hcoord i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hcoef : (S : ℝ) * ((d : ℝ) * (12 * s * K) + R⁻¹) ≤ C * s / (R - r) := by
    have hi : R⁻¹ ≤ s * (R - r)⁻¹ := by
      have hi0 : R⁻¹ ≤ (R - r)⁻¹ := by
        simpa only [one_div] using
          (one_div_le_one_div_of_le hgap (show R - r ≤ R by linarith))
      exact hi0.trans (le_mul_of_one_le_left (inv_nonneg.mpr hgap.le) hs)
    calc
      (S : ℝ) * ((d : ℝ) * (12 * s * K) + R⁻¹) ≤
          (S : ℝ) * ((d : ℝ) * (12 * s * K) + s * (R - r)⁻¹) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hi) S.coe_nonneg
      _ = C * s / (R - r) := by dsimp only [C, K]; ring
  calc
    eLpNorm u.toFun (moserSobolevExponent d) (volume.restrict (centeredAxisCube z r)) ≤
        eLpNorm w.toFun (moserSobolevExponent d) (volume.restrict (centeredAxisCube z R)) := hinner
    _ ≤ (S : ℝ≥0∞) *
        ((∑ i : Fin d, eLpNorm (fun x => w.grad x i) 2 (volume.restrict (centeredAxisCube z R))) +
          ENNReal.ofReal R⁻¹ * eLpNorm w.toFun 2 (volume.restrict (centeredAxisCube z R))) :=
      hSob _ R hR hR1 w
    _ ≤ (S : ℝ≥0∞) *
        ((d : ℝ≥0∞) * (ENNReal.ofReal (12 * s * K) *
          eLpNorm u.toFun 2 (volume.restrict (centeredAxisCube z R))) +
          ENNReal.ofReal R⁻¹ * eLpNorm u.toFun 2 (volume.restrict (centeredAxisCube z R))) :=
      mul_le_mul' le_rfl (add_le_add hsum (mul_le_mul' le_rfl hvalue))
    _ = ENNReal.ofReal ((S : ℝ) * ((d : ℝ) * (12 * s * K) + R⁻¹)) *
        eLpNorm u.toFun 2 (volume.restrict (centeredAxisCube z R)) := by
      rw [ENNReal.ofReal_mul S.coe_nonneg,
        ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg d) (by positivity)) (inv_nonneg.mpr hR.le),
        ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_natCast,
        ENNReal.ofReal_coe_nnreal]
      ring
    _ ≤ ENNReal.ofReal (C * s / (R - r)) *
        eLpNorm u.toFun 2 (volume.restrict (centeredAxisCube z R)) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef) le_rfl

/-- The arbitrary-power rung for the source's local weak-harmonicity predicate. -/
theorem exists_weakHarmonic_ratio_power_sobolev_step {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Vec d → ℝ) (z : Vec d) (r R : ℝ),
        0 < r → r < R → R ≤ 1 →
        AEStronglyMeasurable a (volume.restrict (centeredAxisCube z R)) →
        (∀ x, 1 / 4 ≤ a x ∧ a x ≤ 4) →
        ∀ h : Vec d → ℝ, WeakHarmonic a (centeredAxisCube z R) h →
        ∀ s : ℝ, 1 ≤ s →
          eLpNorm (fun x => (max (h x) 0) ^ s) (moserSobolevExponent d)
              (volume.restrict (centeredAxisCube z r)) ≤
            ENNReal.ofReal (C * s / (R - r)) *
              eLpNorm (fun x => (max (h x) 0) ^ s) 2
                (volume.restrict (centeredAxisCube z R)) := by
  obtain ⟨C, hC, hstep⟩ := exists_harmonic_ratio_h1_power_sobolev_step hd
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  intro a z r R hr hrR hR1 ha hab h hh s hs
  let T : ℝ := (r + R) / 2
  have hrT : r < T := by dsimp only [T]; linarith
  have hTR : T < R := by dsimp only [T]; linarith
  have hsub : centeredAxisCube z T ⊆ centeredAxisCube z R := centeredAxisCube_mono hTR.le
  have hbounded : Bornology.IsBounded (centeredAxisCube z T) :=
    Bornology.IsBounded.pi fun _ => Metric.isBounded_Ioo _ _
  have hcl := closure_centeredAxisCube_subset (x := z) hTR
  obtain ⟨u, hueq, hu⟩ := hh.2 (centeredAxisCube z T) (isOpen_axisCube _ _)
    hbounded.isCompact_closure hcl
  obtain ⟨M, hM⟩ := hbounded.isCompact_closure.exists_bound_of_continuousOn (hh.1.mono hcl)
  have huM : ∀ᵐ x ∂volume.restrict (centeredAxisCube z T), |u.toFun x| ≤ max M 0 := by
    filter_upwards [hueq, ae_restrict_mem (isOpen_axisCube _ _).measurableSet] with x hx hxT
    rw [hx]
    exact (hM x (subset_closure hxT)).trans (le_max_left _ _)
  have hu' : IsWeaklyHarmonicOn a (centeredAxisCube z T) u := by
    intro phi
    simpa only [vecDot_smul_left] using hu phi
  have haT := ha.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hresult := hstep a z r T hr hrT (hTR.le.trans hR1) haT
    (Eventually.of_forall hab) u hu' (max M 0) (le_max_right _ _) huM s hs
  have hueqSmall : u.toFun =ᵐ[volume.restrict (centeredAxisCube z r)] h :=
    hueq.filter_mono (ae_mono (Measure.restrict_mono (centeredAxisCube_mono hrT.le) le_rfl))
  have hpowequal : (fun x => (max (u.toFun x) 0) ^ s) =ᵐ[volume.restrict (centeredAxisCube z T)]
      fun x => (max (h x) 0) ^ s := hueq.mono fun x hx => by dsimp only at hx ⊢; rw [hx]
  have hpowequalSmall : (fun x => (max (u.toFun x) 0) ^ s) =ᵐ[volume.restrict (centeredAxisCube z r)]
      fun x => (max (h x) 0) ^ s := hueqSmall.mono fun x hx => by dsimp only at hx ⊢; rw [hx]
  rw [eLpNorm_congr_ae hpowequalSmall, eLpNorm_congr_ae hpowequal] at hresult
  have hcoef : C * s / (T - r) = (2 * C) * s / (R - r) := by
    rw [show T - r = (R - r) / 2 by dsimp only [T]; ring]
    field_simp [(sub_pos.mpr hrR).ne']
  rw [hcoef] at hresult
  exact hresult.trans (mul_le_mul' le_rfl
    (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)))

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
