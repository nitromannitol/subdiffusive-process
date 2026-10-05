module

public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCaccioppoli
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.BoundaryCellRow

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book Homogenization.Book.Ch03
open scoped BigOperators ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess.Paper

theorem aux_inputs_det_scalar_translation_containment
    (d : ℕ) (Q : Homogenization.TriadicCube d) (z : Vec d) :
    ∃ m : ℤ, translateSet z (openCubeSet Q) ⊆ openCubeSet (originCube d m) := by
  let A : ℝ := ‖cubeCenter Q‖ + cubeRadius Q + ‖z‖
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * A)
  have hpow1 : ∀ n : ℕ, (1 : ℝ) ≤ (3 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        rw [pow_succ]
        nlinarith
  have hpow : ∀ n : ℕ, (n : ℝ) ≤ (3 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        calc
          ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
          _ ≤ (3 : ℝ) ^ n + 1 := by simpa [add_comm] using add_le_add_right ih 1
          _ ≤ (3 : ℝ) ^ n + 2 * (3 : ℝ) ^ n := by
            nlinarith [hpow1 n]
          _ = (3 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring
  have hlarge : A < (1 / 2 : ℝ) * (3 : ℝ) ^ (N : ℤ) := by
    rw [zpow_natCast]
    nlinarith [hpow N]
  refine ⟨N, ?_⟩
  intro y hy
  rw [mem_translateSet_iff_sub_mem] at hy
  have hy_eq : y = (y - z) + z := by simp
  have hy_ball : dist (y - z) (cubeCenter Q) ≤ cubeRadius Q := by
    have hmem := cubeSet_subset_closedBall Q (openCubeSet_subset_cubeSet Q hy)
    exact Metric.mem_closedBall.mp hmem
  have hy_sub_norm : ‖y - z‖ ≤ ‖cubeCenter Q‖ + cubeRadius Q := by
    calc
      ‖y - z‖ = dist (y - z) 0 := by simp
      _ ≤ dist (y - z) (cubeCenter Q) + dist (cubeCenter Q) 0 := dist_triangle _ _ _
      _ ≤ cubeRadius Q + ‖cubeCenter Q‖ := by simpa using add_le_add_right hy_ball ‖cubeCenter Q‖
      _ = ‖cubeCenter Q‖ + cubeRadius Q := by ring
  have hy_norm : ‖y‖ ≤ ‖y - z‖ + ‖z‖ := by
    calc
      ‖y‖ = ‖(y - z) + z‖ := congrArg norm hy_eq
      _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
  have hy_bound : ‖y‖ < (1 / 2 : ℝ) * (3 : ℝ) ^ (N : ℤ) := by
    dsimp [A] at hlarge
    linarith
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hi : ‖y i‖ ≤ ‖y‖ := norm_le_pi_norm y i
  constructor
  · have hneg : -‖y i‖ ≤ y i := by simpa only [Real.norm_eq_abs] using neg_abs_le (y i)
    linarith
  · have hpos : y i ≤ ‖y i‖ := by simpa only [Real.norm_eq_abs] using le_abs_self (y i)
    linarith

noncomputable def aux_inputs_det_scalar_translation_onCube
    (d : ℕ) (Q K : Homogenization.TriadicCube d) (z : Vec d)
    (a : Vec d → ℝ) (hK : ScalarCoeffOnData (Ch02.cubeDomain K) a)
    (hsub : translateSet z (openCubeSet Q) ⊆ openCubeSet K) :
    ScalarCoeffOnData (Ch02.cubeDomain Q) (fun x => a (x + z)) := by
  let U : Set (Vec d) := openCubeSet Q
  let V : Set (Vec d) := translateSet z U
  have hVmeas : MeasurableSet V := by
    change MeasurableSet (translateSet z (openCubeSet Q))
    rw [← preimage_subRight_eq_translateSet]
    exact (measurableSet_openCubeSet Q).preimage
      (continuous_id.sub continuous_const).measurable
  have hKell : IsAEEllipticFieldOn hK.lam hK.Lam (openCubeSet K)
      (scalarCoeffField a) := by
    refine ⟨measurableSet_openCubeSet K, ?_, ?_⟩
    · intro i j
      simpa [volumeMeasureOn, Ch02.cubeDomain_coe] using hK.aeStronglyMeasurable i j
    · simpa [volumeMeasureOn, Ch02.cubeDomain_coe] using! hK.toCoeffOn.aeElliptic
  have hVell : IsAEEllipticFieldOn hK.lam hK.Lam V (scalarCoeffField a) := by
    exact hKell.mono hVmeas (by simpa [V, U] using hsub)
  have hpre : IsAEEllipticFieldOn hK.lam hK.Lam V
      (Homogenization.translateCoeffField (-z)
        (Homogenization.translateCoeffField z (scalarCoeffField a))) := by
    simpa [Homogenization.translateCoeffField] using hVell
  have htarget' :=
    Homogenization.IsAEEllipticFieldOn.translateSet_of_translateCoeffField
      (d := d) (U := V)
      (a := Homogenization.translateCoeffField z (scalarCoeffField a)) (-z) hpre
  have htarget : IsAEEllipticFieldOn hK.lam hK.Lam U
      (scalarCoeffField (fun x => a (x + z))) := by
    simpa [U, V, Homogenization.translateSet_translateSet,
      Homogenization.translateCoeffField, scalarCoeffField] using! htarget'
  have hboundsV : ∀ᵐ x ∂ volumeMeasureOn V,
      hK.lam ≤ a x ∧ a x ≤ hK.Lam := by
    have hmono : volume.restrict V ≤ volume.restrict (openCubeSet K) :=
      MeasureTheory.Measure.restrict_mono hsub le_rfl
    have hsource : ∀ᵐ x ∂ volumeMeasureOn (openCubeSet K),
        hK.lam ≤ a x ∧ a x ≤ hK.Lam := by
      simpa [volumeMeasureOn, Ch02.cubeDomain_coe] using hK.aeBounds
    exact Filter.Eventually.filter_mono (MeasureTheory.ae_mono hmono) hsource
  have hboundsU :=
    (measurePreserving_addRight_restrict_translateSet (d := d) z U).quasiMeasurePreserving.ae
      hboundsV
  refine ⟨hK.lam, hK.Lam, hK.lam_pos, hK.lam_le_Lam, ?_, ?_⟩
  · intro i j
    simpa [U, volumeMeasureOn, Ch02.cubeDomain_coe] using
      htarget.aestronglyMeasurable_restrictCoeffField_apply i j
  · simpa [U, volumeMeasureOn, Ch02.cubeDomain_coe] using hboundsU

theorem inputs_det_scalar_translation (d : ℕ) (a : Vec d → ℝ)
    (data : ScalarTriadicCoeffData a) (z : Vec d) :
    (Nonempty (ScalarTriadicCoeffData (fun x => a (x + z)))) := by
  refine ⟨{ onCube := ?_ }⟩
  intro Q
  let m := Classical.choose (aux_inputs_det_scalar_translation_containment d Q z)
  have hsub := Classical.choose_spec (aux_inputs_det_scalar_translation_containment d Q z)
  exact aux_inputs_det_scalar_translation_onCube d Q (originCube d m) z a
    (data.onCube (originCube d m)) (by simpa using hsub)

end SubdiffusiveProcess.Paper

