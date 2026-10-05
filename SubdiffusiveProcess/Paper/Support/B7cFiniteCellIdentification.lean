module

public import SubdiffusiveProcess.Paper.prop_gluing
public import SubdiffusiveProcess.Sobolev.NativeHarmonicMinimum
public import SubdiffusiveProcess.Sobolev.GoodextHolderLimit
public import SubdiffusiveProcess.FiniteStopping.CutoffRestrictions
public import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.H1Transport

@[expose] public section





set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The catalogue and an arbitrary finite interpolant with the same datum
give the same continuous function and weak gradient. Their datum gradient
representatives may differ; the maximum principle uses their equal values. -/
theorem aux_mfd_prop_boundary_finite_identification
    {d : ℕ} [NeZero d] (Q : Opens (SpatialCoordinates d))
    (hQ : IsOpenBoundedConvexDomain (Q : Set (SpatialCoordinates d)))
    (a : SpatialCoordinates d → ℝ) (ha : Continuous a)
    (lo hi : ℝ) (hlo : 0 < lo)
    (hab : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)), lo ≤ a x ∧ a x ≤ hi)
    (u v phi psi : H1Function (Q : Set (SpatialCoordinates d)))
    (hu : IsWeaklyHarmonicOn a (Q : Set (SpatialCoordinates d)) u)
    (hv : IsWeaklyHarmonicOn a (Q : Set (SpatialCoordinates d)) v)
    (hut : HasZeroTraceDifferenceOn (Q : Set (SpatialCoordinates d)) u phi)
    (hvt : HasZeroTraceDifferenceOn (Q : Set (SpatialCoordinates d)) v psi)
    (huc : ContinuousOn u.toFun (closure (Q : Set (SpatialCoordinates d))))
    (hvc : ContinuousOn v.toFun (closure (Q : Set (SpatialCoordinates d))))
    (hdatum : phi.toFun = psi.toFun) :
    Set.EqOn u.toFun v.toFun (closure (Q : Set (SpatialCoordinates d))) ∧
      u.grad =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] v.grad := by
  have hbound : ∀ x ∈ (Q : Set (SpatialCoordinates d)), lo ≤ a x ∧ a x ≤ hi :=
    fun x hx => hab x (subset_closure hx)
  have hle := aux_prop_gluing_harmonic_diff_le (Q : Set (SpatialCoordinates d)) hQ a
    lo hi hlo ha hbound u v phi psi hu hv hut hvt huc hvc 0
    (fun x => by rw [hdatum]; simp only [sub_self, le_refl])
  have hge := aux_prop_gluing_harmonic_diff_le (Q : Set (SpatialCoordinates d)) hQ a
    lo hi hlo ha hbound v u psi phi hv hu hvt hut hvc huc 0
    (fun x => by rw [hdatum]; simp only [sub_self, le_refl])
  have heq : Set.EqOn u.toFun v.toFun (closure (Q : Set (SpatialCoordinates d))) := by
    intro x hx
    exact le_antisymm (sub_nonpos.mp (hle x hx)) (sub_nonpos.mp (hge x hx))
  exact ⟨heq, Homogenization.Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq Q.isOpen
    ((ae_restrict_mem Q.isOpen.measurableSet).mono fun x hx => heq (subset_closure hx))⟩

/-- Coefficient continuity and positivity are inherent in the literal
normalized cutoff field, and are independent of the infrared law. -/
theorem aux_mfd_prop_boundary_cutoff_continuous
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) : Continuous (cutoffCoefficient M H omega N) := by
  refine continuous_const.mul (Real.continuous_exp.comp ?_)
  exact Continuous.sub
    (Continuous.add (H omega).continuous
      (continuous_finsetSum _ fun j _ => (omega (-(Int.ofNat j))).continuous))
    continuous_const

/-- The actual cutoff coefficient has finite-cutoff ellipticity bounds on
any fixed closed cube, derived internally from positivity and compactness. -/
theorem aux_mfd_prop_boundary_cutoff_elliptic_closure
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ lo hi : ℝ, 0 < lo ∧
      ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
        lo ≤ cutoffCoefficient M H omega N x ∧ cutoffCoefficient M H omega N x ≤ hi := by
  have hK := lane2_isCompact_closure_centeredCube z hr
  have hne : (closure (centeredCube z r hr : Set (SpatialCoordinates d))).Nonempty :=
    ⟨z, subset_closure (Metric.mem_ball_self (by positivity : 0 < r / 2))⟩
  have hc := aux_mfd_prop_boundary_cutoff_continuous M H omega N
  obtain ⟨x0, -, hmin⟩ := hK.exists_isMinOn hne hc.continuousOn
  obtain ⟨x1, -, hmax⟩ := hK.exists_isMaxOn hne hc.continuousOn
  refine ⟨cutoffCoefficient M H omega N x0, cutoffCoefficient M H omega N x1, ?_,
    fun x hx => ⟨hmin hx, hmax hx⟩⟩
  exact mul_pos (inv_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)

/-- Fixed-catalogue estimates transfer to every native harmonic solution
of the same smooth trace. All constants precede the cutoff index. -/
theorem aux_mfd_prop_boundary_catalogue_cell_bounds
    {d : ℕ} [NeZero d]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : ℕ → SpatialCoordinates d → ℝ) (hac : ∀ n, Continuous (a n))
    (hell : ∀ n, ∃ lo hi : ℝ, 0 < lo ∧
      ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
        lo ≤ a n x ∧ a n x ≤ hi)
    (phi psi : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hdatum : phi.toFun = psi.toFun)
    (v : ℕ → H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hv : ∀ n, IsWeaklyHarmonicOn (a n) (centeredCube z r hr : Set (SpatialCoordinates d)) (v n))
    (hvt : ∀ n, HasZeroTraceDifferenceOn (centeredCube z r hr : Set (SpatialCoordinates d)) (v n) psi)
    (hvc : ∀ n, ContinuousOn (v n).toFun (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (alpha t : ℝ) (halpha : 0 < alpha)
    (Cenergy Cgrowth Cholder : ℝ)
    (hEnergy : ∀ n, energy (a n) (centeredCube z r hr : Set (SpatialCoordinates d)) (v n) ≤ Cenergy)
    (hGrowth : ∀ n, ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal (a n y * ∑ i : Fin d, ((v n).grad y i) ^ 2)))
          (Metric.ball x rr) ≤ ENNReal.ofReal (Cgrowth * rr ^ t))
    (hHolder : ∀ n, _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
      (closure (centeredCube z r hr : Set (SpatialCoordinates d))) (v n).toFun)
    (hNorm : ∀ n, _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
      (closure (centeredCube z r hr : Set (SpatialCoordinates d))) (v n).toFun ≤ Cholder) :
    ∃ B H : ℝ, 0 ≤ B ∧ 0 ≤ H ∧
      ∀ (n : ℕ) (u : H1Function (centeredCube z r hr : Set (SpatialCoordinates d))),
        IsWeaklyHarmonicOn (a n) (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        HasZeroTraceDifferenceOn (centeredCube z r hr : Set (SpatialCoordinates d)) u phi →
        ContinuousOn u.toFun (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
        energy (a n) (centeredCube z r hr : Set (SpatialCoordinates d)) u ≤ B ∧
        (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal (a n y * ∑ i : Fin d, (u.grad y i) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)) ∧
        (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∀ y ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
            |u.toFun x - u.toFun y| ≤ H * dist x y ^ alpha) ∧
        (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), |u.toFun x| ≤ H) := by
  let Q := centeredCube z r hr
  have hpoints : ∀ n, 0 ≤ Cholder ∧
      (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), |(v n).toFun x| ≤ Cholder) ∧
      ∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
      ∀ y ∈ closure (Q : Set (SpatialCoordinates d)),
        |(v n).toFun x - (v n).toFun y| ≤
          Cholder * (Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)) ^ alpha :=
    fun n => aux_lem_goodext_pointwise_of_cAlpha alpha Cholder halpha _
      (lane2_isCompact_closure_centeredCube z hr) (v n).toFun (hvc n) (hHolder n) (hNorm n)
  let B := max 0 (max Cenergy Cgrowth)
  let H := Cholder * max 1 ((Real.sqrt d) ^ alpha)
  have hB : 0 ≤ B := le_max_left _ _
  have hH : 0 ≤ H := mul_nonneg (hpoints 0).1 (zero_le_one.trans (le_max_left _ _))
  refine ⟨B, H, hB, hH, ?_⟩
  intro n u hu hut huc
  obtain ⟨lo, hi, hlo, hab⟩ := hell n
  obtain ⟨heq, hgrad⟩ := aux_mfd_prop_boundary_finite_identification Q
    (lane2_isOpenBoundedConvexDomain_centeredCube z hr) (a n) (hac n) lo hi hlo hab
    u (v n) phi psi hu (hv n) hut (hvt n) huc (hvc n) hdatum
  have hEeq : energy (a n) (Q : Set (SpatialCoordinates d)) u =
      energy (a n) (Q : Set (SpatialCoordinates d)) (v n) := by
    apply integral_congr_ae
    filter_upwards [hgrad] with x hx
    simp only [hx]
  have hMeq : ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
      (fun y => ENNReal.ofReal (a n y * ∑ i : Fin d, (u.grad y i) ^ 2))) =
      ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
      (fun y => ENNReal.ofReal (a n y * ∑ i : Fin d, ((v n).grad y i) ^ 2))) := by
    apply withDensity_congr_ae
    filter_upwards [hgrad] with x hx
    rw [hx]
  refine ⟨hEeq.trans_le ((hEnergy n).trans ((le_max_left _ _).trans (le_max_right _ _))), ?_, ?_, ?_⟩
  · intro x hx rr hrr hrr1
    rw [hMeq]
    exact (hGrowth n x hx rr hrr hrr1).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _))
        (Real.rpow_nonneg hrr.le t)))
  · intro x hx y hy
    rw [heq hx, heq hy]
    calc
      |(v n).toFun x - (v n).toFun y| ≤
          Cholder * (Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)) ^ alpha :=
        (hpoints n).2.2 x hx y hy
      _ ≤ Cholder * (Real.sqrt d * dist x y) ^ alpha :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Real.sqrt_nonneg _)
          (aux_lem_goodext_euclid_le x y) halpha.le) (hpoints n).1
      _ = (Cholder * (Real.sqrt d) ^ alpha) * dist x y ^ alpha := by
        rw [Real.mul_rpow (Real.sqrt_nonneg _) dist_nonneg]
        ring
      _ ≤ H * dist x y ^ alpha := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_max_right _ _) (hpoints n).1)
        (Real.rpow_nonneg dist_nonneg _)
  · intro x hx
    rw [heq hx]
    exact ((hpoints n).2.1 x hx).trans (by
      change Cholder ≤ Cholder * max 1 ((Real.sqrt d) ^ alpha)
      exact le_mul_of_one_le_right (hpoints n).1 (le_max_left _ _))

end SubdiffusiveProcess.Paper
