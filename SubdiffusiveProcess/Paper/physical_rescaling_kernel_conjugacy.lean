module

public import SubdiffusiveProcess.Paper.physical_generator_reindexing
public import SubdiffusiveProcess.Paper.in_crossing
public import MarkovProcess.FiniteTime.KernelEquivariance
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeWeakGenerator
public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import SubdiffusiveProcess.MultiplicativeChaos.TimeMarginal
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeMarginalIdentification

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess
open SubdiffusiveProcess
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock
open scoped ENNReal NNReal
open scoped Pointwise
open scoped BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_physical_rescaling_kernel_conjugacy_path_integral
    {d : ℕ} (P : SubMarkovKernelSemigroup (SpatialCoordinates d))
    (ν : Measure (DiffusionPath d)) (x : SpatialCoordinates d)
    [IsProbabilityMeasure ν]
    (hfd : ∀ s : NNReal,
      ν.map (ContinuousPath.finsetEvaluation ({s} : Finset NNReal)) =
        SubMarkovKernelSemigroup.finiteSetKernel P ({s} : Finset NNReal) x)
    (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ) :
    (∀ t : ℝ, kernelIntegral (P (Real.toNNReal t)) f x =
      ∫ path, f (path (Real.toNNReal t)) ∂ν) ∧
    Continuous (fun t : ℝ ↦ kernelIntegral (P (Real.toNNReal t)) f x) := by
  have heq : ∀ s : NNReal,
      kernelIntegral (P s) f x = ∫ path, f (path s) ∂ν := by
    intro s
    have hmap : ν.map (fun path : DiffusionPath d => path s) = P.kernel s x :=
      SubdiffusiveProcess.map_eval_eq_of_finsetEvaluation P ν x s (hfd s)
    have hmeas : Measurable (fun path : DiffusionPath d => path s) :=
      ContinuousPath.measurable_coordinateProcess s
    rw [kernelIntegral, ← hmap]
    exact integral_map hmeas.aemeasurable f.continuous.aestronglyMeasurable
  refine ⟨fun t ↦ heq (Real.toNNReal t), ?_⟩
  rw [show (fun t : ℝ ↦ kernelIntegral (P (Real.toNNReal t)) f x) =
      (fun t : ℝ ↦ ∫ path, f (path (Real.toNNReal t)) ∂ν) by
        funext t
        exact heq (Real.toNNReal t)]
  exact continuous_integral_coordinate f ν

theorem aux_physical_rescaling_kernel_conjugacy_cast_h10_toFun
    {d : ℕ} {U V : Set (SpatialCoordinates d)}
    (hUV : U = V) (φ : H10Function U) (x : SpatialCoordinates d) :
    (hUV ▸ φ).toH1Function.toFun x = φ.toH1Function.toFun x := by
  subst V
  rfl

theorem aux_physical_rescaling_kernel_conjugacy_cast_h10_grad
    {d : ℕ} {U V : Set (SpatialCoordinates d)}
    (hUV : U = V) (φ : H10Function U) (x : SpatialCoordinates d) :
    (hUV ▸ φ).toH1Function.grad x = φ.toH1Function.grad x := by
  subst V
  rfl

theorem aux_physical_rescaling_kernel_conjugacy_coefficient_scale
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (sigma : ℕ → BilateralField d → BilateralField d)
    (N : ℕ) (omega : BilateralField d)
    (hV : ∀ x : SpatialCoordinates d,
      cutoffPotential H omega 0 (((3 : ℝ) ^ N) • x) - omega 0 0 =
        cutoffPotential H (sigma N omega) N x -
          ∑ i ∈ Finset.range (N + 1), (sigma N omega) (-(i : Int)) 0) :
    ∃ a α r : ℝ, 0 < a ∧ 0 < α ∧ r ≠ 0 ∧
      (physicalTimeFactor M N : ℝ) = r * a ^ 2 ∧
      (∀ x, cutoffCoefficient M H (sigma N omega) N x =
        α * r * cutoffCoefficient M H omega 0 (a • x)) ∧
      (∀ x, cutoffSpeedDensity M H (sigma N omega) N x =
        α * cutoffSpeedDensity M H omega 0 (a • x)) ∧
      a = (3 : ℝ) ^ N := by
  let a : ℝ := (3 : ℝ) ^ N
  let r : ℝ := SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 /
    SubdiffusiveProcess.CoarseGrainingVocab.ahom M N
  let α : ℝ := Real.exp
    (∑ i ∈ Finset.range (N + 1), (sigma N omega) (-(i : Int)) 0 -
      omega 0 0 - (N : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hα : 0 < α := by
    dsimp [α]
    exact Real.exp_pos _
  have hr : r ≠ 0 := by
    dsimp [r]
    exact div_ne_zero (ne_of_gt (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M 0))
      (ne_of_gt (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N))
  have hfactor : (physicalTimeFactor M N : ℝ) = r * a ^ 2 := by
    dsimp [physicalTimeFactor, r, a]
    change SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 * (3 : ℝ) ^ (2 * N) /
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N = _
    simp only [div_eq_mul_inv, mul_comm 2 N, pow_mul]
    ring
  refine ⟨a, α, r, ha, hα, hr, hfactor, ?_, ?_, rfl⟩
  · intro x
    have hprod :
        Real.exp (∑ i ∈ Finset.range (N + 1),
            (sigma N omega) (-(i : Int)) 0 - omega 0 0 -
              (N : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
          Real.exp (cutoffPotential H omega 0 (((3 : ℝ) ^ N) • x) -
            _root_.SubdiffusiveProcess.Model.tauSq M.P) =
        Real.exp (cutoffPotential H (sigma N omega) N x -
          (N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
      rw [← Real.exp_add]
      congr 1
      linarith [hV x]
    dsimp [a, α, r]
    unfold cutoffCoefficient
    calc
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
          Real.exp (cutoffPotential H (sigma N omega) N x -
            (N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) =
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
            (Real.exp (∑ i ∈ Finset.range (N + 1),
                (sigma N omega) (-(i : Int)) 0 - omega 0 0 -
                  (N : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
              Real.exp (cutoffPotential H omega 0 (((3 : ℝ) ^ N) • x) -
                _root_.SubdiffusiveProcess.Model.tauSq M.P)) := by rw [hprod]
      _ = Real.exp (∑ i ∈ Finset.range (N + 1),
            (sigma N omega) (-(i : Int)) 0 - omega 0 0 -
              (N : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 /
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) *
          ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0)⁻¹ *
              Real.exp (cutoffPotential H omega 0 (((3 : ℝ) ^ N) • x) -
                (((0 : ℕ) : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) := by
        field_simp [SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M 0,
          SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N]
        ring_nf
        simp [mul_assoc, ne_of_gt (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M 0)]
  · intro x
    have hprod :
        Real.exp (∑ i ∈ Finset.range (N + 1),
            (sigma N omega) (-(i : Int)) 0 - omega 0 0 -
              (N : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
          Real.exp (cutoffPotential H omega 0 (((3 : ℝ) ^ N) • x) -
            _root_.SubdiffusiveProcess.Model.tauSq M.P) =
        Real.exp (cutoffPotential H (sigma N omega) N x -
          (N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
      rw [← Real.exp_add]
      congr 1
      linarith [hV x]
    dsimp [a, α]
    unfold cutoffSpeedDensity
    norm_num
    exact hprod.symm

theorem aux_physical_rescaling_kernel_conjugacy_massive_bounds
    {d : ℕ} {c rho : SpatialCoordinates d → ℝ}
    (hc : Continuous c) (hrho : Continuous rho)
    (hpc : ∀ x, 0 < c x) (hpr : ∀ x, 0 < rho x) :
    Nonempty (SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.MassiveCubeBounds c rho) := by
  let bc : ∀ n : ℕ, ℝ × ℝ := fun n ↦
    Classical.choose (exists_cube_bounds hc hpc n)
  let br : ∀ n : ℕ, ℝ × ℝ := fun n ↦
    Classical.choose (exists_cube_bounds hrho hpr n)
  have hbc : ∀ n : ℕ, 0 < (bc n).1 ∧
      ∀ x ∈ cube d (n : ℤ), (bc n).1 ≤ c x ∧ c x ≤ (bc n).2 := by
    intro n
    exact Classical.choose_spec (exists_cube_bounds hc hpc n)
  have hbr : ∀ n : ℕ, 0 < (br n).1 ∧
      ∀ x ∈ cube d (n : ℤ), (br n).1 ≤ rho x ∧ rho x ≤ (br n).2 := by
    intro n
    exact Classical.choose_spec (exists_cube_bounds hrho hpr n)
  refine ⟨{
    lam := fun n ↦ (bc n).1
    Lam := fun n ↦ (bc n).2
    rhoMin := fun n ↦ (br n).1
    rhoMax := fun n ↦ (br n).2
    lam_pos := fun n ↦ (hbc n).1
    rhoMin_pos := fun n ↦ (hbr n).1
    ell := fun n ↦
      SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.isEllipticFieldOn_scalarCoeffField_of_continuousOn
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)).isOpen.measurableSet
        hc.continuousOn (hbc n).1 (hbc n).2
    coeff_lower := fun n x hx ↦ (hbc n).2 x hx |>.1
    rho_measurable := fun n ↦ hrho.aestronglyMeasurable.restrict
    rho_lower := fun n x hx ↦ (hbr n).2 x hx |>.1
    rho_bounded := fun n ↦ by
      filter_upwards [ae_restrict_mem
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)).isOpen.measurableSet]
        with x hx
      rw [abs_of_pos (hpr x)]
      exact (hbr n).2 x hx |>.2 }⟩

theorem aux_physical_rescaling_kernel_conjugacy_massive_unscale
    {d : ℕ} {U : Set (SpatialCoordinates d)}
    {a α r μ lam : ℝ} {c rho C R : SpatialCoordinates d → ℝ}
    {u : H1Function (a • U)} {f0 f : SpatialCoordinates d → ℝ}
    (ha : 0 < a) (hα : α ≠ 0) (hr : r ≠ 0)
    (hμ : μ = r * a ^ 2 * lam)
    (hC : ∀ x, C x = α * r * c (a • x))
    (hR : ∀ x, R x = α * rho (a • x))
    (hf : ∀ x, f0 (a • x) = f x)
  (hu : IsMassiveWeakSolutionOn c rho lam (a • U) u f0) :
    IsMassiveWeakSolutionOn C R μ U
      ((r * a ^ 2)⁻¹ • u.unscale ha) f := by
  intro φ
  have hset : a⁻¹ • a • U = U := by
    ext x
    simp [ha.ne']
  let φ' : H10Function (a⁻¹ • a • U) := by
    exact hset.symm ▸ φ
  let ψ : H10Function (a • U) := by
    simpa [smul_smul, ha.ne'] using
      (H10Function.unscale (U := a • U) (a := a⁻¹) (inv_pos.mpr ha) φ')
  have hψval : ψ.toH1Function.toFun =
      (fun y => φ.toH1Function.toFun (a⁻¹ • y)) := by
    funext y
    change (H10Function.unscale (U := a • U) (a := a⁻¹)
      (inv_pos.mpr ha) φ').toH1Function.toFun y = _
    rw [H10Function.unscale_toH1Function, H1Function.unscale_toFun]
    change φ'.toH1Function.toFun (a⁻¹ • y) = _
    exact aux_physical_rescaling_kernel_conjugacy_cast_h10_toFun
      hset.symm φ (a⁻¹ • y)
  have hψgrad : ψ.toH1Function.grad =
      (fun y => a⁻¹ • φ.toH1Function.grad (a⁻¹ • y)) := by
    funext y
    change (H10Function.unscale (U := a • U) (a := a⁻¹)
      (inv_pos.mpr ha) φ').toH1Function.grad y = _
    rw [H10Function.unscale_toH1Function, H1Function.unscale_grad]
    change a⁻¹ • φ'.toH1Function.grad (a⁻¹ • y) = _
    rw [aux_physical_rescaling_kernel_conjugacy_cast_h10_grad hset.symm φ]
  have hψ := hu ψ
  have hmass :
      ∫ y in a • U, rho y * u.toFun y * ψ.toH1Function.toFun y ∂volume =
        a ^ d * ∫ x in U, rho (a • x) * u.toFun (a • x) * φ.toH1Function.toFun x ∂volume := by
    rw [hψval]
    have h := Homogenization.Book.Ch01.setIntegral_comp_smul_of_pos
      ha U (fun y : SpatialCoordinates d =>
        rho y * u.toFun y * φ.toH1Function.toFun (a⁻¹ • y))
    have h' :
        ∫ x in U, rho (a • x) * u.toFun (a • x) * φ.toH1Function.toFun x ∂volume =
          (a ^ d)⁻¹ * ∫ y in a • U,
            rho y * u.toFun y * φ.toH1Function.toFun (a⁻¹ • y) ∂volume := by
      simpa only [smul_eq_mul, smul_smul, inv_mul_cancel₀ ha.ne', one_smul] using h
    have hpow : a ^ d ≠ 0 := (pow_pos ha d).ne'
    calc
      ∫ y in a • U, rho y * u.toFun y * φ.toH1Function.toFun (a⁻¹ • y) ∂volume =
          a ^ d * ((a ^ d)⁻¹ * ∫ y in a • U,
            rho y * u.toFun y * φ.toH1Function.toFun (a⁻¹ • y) ∂volume) := by
              field_simp [hpow]
      _ = a ^ d * ∫ x in U,
            rho (a • x) * u.toFun (a • x) * φ.toH1Function.toFun x ∂volume := by
              rw [← h']
  have henergy :
      ∫ y in a • U, vecDot (c y • u.grad y) (ψ.toH1Function.grad y) ∂volume =
        a ^ d * a⁻¹ * ∫ x in U,
          vecDot (c (a • x) • u.grad (a • x)) (φ.toH1Function.grad x) ∂volume := by
    rw [hψgrad]
    have h := Homogenization.Book.Ch01.setIntegral_comp_smul_of_pos
      ha U (fun y : SpatialCoordinates d =>
        vecDot (c y • u.grad y) (φ.toH1Function.grad (a⁻¹ • y)))
    have h' :
        ∫ x in U, vecDot (c (a • x) • u.grad (a • x))
            (φ.toH1Function.grad x) ∂volume =
          (a ^ d)⁻¹ * ∫ y in a • U,
            vecDot (c y • u.grad y) (φ.toH1Function.grad (a⁻¹ • y)) ∂volume := by
      simpa only [smul_eq_mul, smul_smul, inv_mul_cancel₀ ha.ne', one_smul] using h
    have hpow : a ^ d ≠ 0 := (pow_pos ha d).ne'
    have hbase :
        ∫ y in a • U, vecDot (c y • u.grad y)
            (φ.toH1Function.grad (a⁻¹ • y)) ∂volume =
          a ^ d * ∫ x in U, vecDot (c (a • x) • u.grad (a • x))
            (φ.toH1Function.grad x) ∂volume := by
      calc
        ∫ y in a • U, vecDot (c y • u.grad y)
            (φ.toH1Function.grad (a⁻¹ • y)) ∂volume =
            a ^ d * ((a ^ d)⁻¹ * ∫ y in a • U,
              vecDot (c y • u.grad y)
                (φ.toH1Function.grad (a⁻¹ • y)) ∂volume) := by
                  field_simp [hpow]
        _ = a ^ d * ∫ x in U, vecDot (c (a • x) • u.grad (a • x))
              (φ.toH1Function.grad x) ∂volume := by
                rw [← h']
    calc
      ∫ y in a • U, vecDot (c y • u.grad y)
          (a⁻¹ • φ.toH1Function.grad (a⁻¹ • y)) ∂volume =
          a⁻¹ * ∫ y in a • U,
            vecDot (c y • u.grad y) (φ.toH1Function.grad (a⁻¹ • y)) ∂volume := by
              rw [show (fun y : SpatialCoordinates d =>
                vecDot (c y • u.grad y) (a⁻¹ • φ.toH1Function.grad (a⁻¹ • y))) =
                fun y => a⁻¹ * vecDot (c y • u.grad y)
                  (φ.toH1Function.grad (a⁻¹ • y)) by
                  funext y
                  simp [vecDot_smul_right]]
              rw [integral_const_mul]
      _ = a ^ d * a⁻¹ * ∫ x in U,
            vecDot (c (a • x) • u.grad (a • x))
              (φ.toH1Function.grad x) ∂volume := by
              rw [hbase]
              ring
  have hsource :
      ∫ y in a • U, rho y * f0 y * ψ.toH1Function.toFun y ∂volume =
        a ^ d * ∫ x in U, rho (a • x) * f x * φ.toH1Function.toFun x ∂volume := by
    rw [hψval]
    have h := Homogenization.Book.Ch01.setIntegral_comp_smul_of_pos
      ha U (fun y : SpatialCoordinates d =>
        rho y * f0 y * φ.toH1Function.toFun (a⁻¹ • y))
    have h' :
        ∫ x in U, rho (a • x) * f x * φ.toH1Function.toFun x ∂volume =
          (a ^ d)⁻¹ * ∫ y in a • U,
            rho y * f0 y * φ.toH1Function.toFun (a⁻¹ • y) ∂volume := by
      simpa only [smul_eq_mul, smul_smul, inv_mul_cancel₀ ha.ne', one_smul, hf] using h
    have hpow : a ^ d ≠ 0 := (pow_pos ha d).ne'
    calc
      ∫ y in a • U, rho y * f0 y * φ.toH1Function.toFun (a⁻¹ • y) ∂volume =
          a ^ d * ((a ^ d)⁻¹ * ∫ y in a • U,
            rho y * f0 y * φ.toH1Function.toFun (a⁻¹ • y) ∂volume) := by
              field_simp [hpow]
      _ = a ^ d * ∫ x in U,
            rho (a • x) * f x * φ.toH1Function.toFun x ∂volume := by
              rw [← h']
  rw [hmass, henergy, hsource] at hψ
  simp only [hC, hR, H1Function.smul_toFun, H1Function.smul_grad,
    H1Function.unscale_toFun, H1Function.unscale_grad]
  have hmass' :
      (∫ x in U, α * rho (a • x) * ((r * a ^ 2)⁻¹ * u.toFun (a • x)) *
        φ.toH1Function.toFun x ∂volume) =
        α * (r * a ^ 2)⁻¹ *
          ∫ x in U, rho (a • x) * u.toFun (a • x) * φ.toH1Function.toFun x ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    field_simp [hα, hr, ha.ne']
  have henergy' :
      (∫ x in U, vecDot ((α * r * c (a • x)) • (r * a ^ 2)⁻¹ •
        a • u.grad (a • x)) (φ.toH1Function.grad x) ∂volume) =
        α / a * ∫ x in U,
          vecDot (c (a • x) • u.grad (a • x))
            (φ.toH1Function.grad x) ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [vecDot_smul_left]
    field_simp [hα, hr, ha.ne']
  have hsource' :
      (∫ x in U, α * rho (a • x) * f x * φ.toH1Function.toFun x ∂volume) =
        α * ∫ x in U, rho (a • x) * f x * φ.toH1Function.toFun x ∂volume := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [hmass', henergy']
  rw [hμ, hsource']
  have hpow : a ^ d ≠ 0 := (pow_pos ha d).ne'
  field_simp [hpow] at hψ
  field_simp [hα, hr, ha.ne']
  nlinarith [hψ]

theorem aux_physical_rescaling_kernel_conjugacy_resolvent_solution
    {d : ℕ} {a α r μ lam : ℝ}
    {c rho C R : SpatialCoordinates d → ℝ}
    (ha : 0 < a) (hα : α ≠ 0) (hr : r ≠ 0)
    (hμ : μ = r * a ^ 2 * lam)
    (hC : ∀ x, C x = α * r * c (a • x))
    (hR : ∀ x, R x = α * rho (a • x))
    (hμpos : 0 < μ) (hlampos : 0 < lam)
    (B : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.MassiveCubeBounds C R)
    (D0 DN : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum
      (SpatialCoordinates d))
    (hD0 : IsWeakEllipticResolvent c rho D0)
    (hDN : IsWeakEllipticResolvent C R DN)
    (f0 : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ)
    (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ)
    (hf : ∀ x, f0 (a • x) = f x) :
    ∀ x, DN.solution ⟨μ, hμpos⟩ f x =
      (r * a ^ 2)⁻¹ * D0.solution ⟨lam, hlampos⟩ f0 (a • x) := by
  let e : SpatialCoordinates d ≃ₜ SpatialCoordinates d :=
    Homeomorph.smulOfNeZero a ha.ne'
  let v0 : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ := {
    toFun := fun x => D0.solution ⟨lam, hlampos⟩ f0 (a • x)
    continuous_toFun := (D0.solution ⟨lam, hlampos⟩ f0).continuous.comp
      (by simpa only using!
        ((continuous_const : Continuous (fun _ : SpatialCoordinates d ↦ a)).smul
          (continuous_id : Continuous (id : SpatialCoordinates d → SpatialCoordinates d))))
    zero_at_infty' := (zero_at_infty (D0.solution ⟨lam, hlampos⟩ f0)).comp
      e.toCocompactMap.cocompact_tendsto' }
  let v : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ :=
    (r * a ^ 2)⁻¹ • v0
  have hv_apply : ∀ x, v x =
      (r * a ^ 2)⁻¹ * D0.solution ⟨lam, hlampos⟩ f0 (a • x) := by
    intro x
    rfl
  have hff : ∀ k : ℕ, MemL2On (cube d (k : ℤ)) (fun x => f x) := by
    intro k
    let W : Set (SpatialCoordinates d) := cube d (k : ℤ)
    let hW : IsOpenBoundedConvexDomain W := by
      dsimp [W]
      exact SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.isOpenBoundedConvexDomain_cube
        d (k : ℤ)
    let := hW.isFiniteMeasure_restrict_volume
    apply MemLp.of_bound f.continuous.aestronglyMeasurable.restrict ‖f.toBCF‖
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs] using! f.toBCF.norm_coe_le_norm x
  have hzero : ∀ x, (DN.solution ⟨μ, hμpos⟩ f - v) x = 0 := by
    intro x
    apply eq_zero_of_localMassiveWeakSolution_of_tendsto_cocompact B hμpos
    · exact (DN.solution ⟨μ, hμpos⟩ f).continuous.sub v.continuous
    · simpa only [ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply, sub_zero] using!
        (zero_at_infty (DN.solution ⟨μ, hμpos⟩ f)).sub (zero_at_infty v)
    · intro k
      let W : Set (SpatialCoordinates d) := cube d (k : ℤ)
      have hW : IsOpenBoundedConvexDomain W := by
        dsimp [W]
        exact SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.isOpenBoundedConvexDomain_cube
          d (k : ℤ)
      obtain ⟨uN, huN, hsolN⟩ := hDN ⟨μ, hμpos⟩ f W hW
      let W' : Set (SpatialCoordinates d) := a • W
      have hW' : IsOpenBoundedConvexDomain W' := by
        have hbd : IsBoundedDomain W' := by
          rcases hW.isBoundedDomain with ⟨K, hKpos, hK⟩
          refine ⟨a * K, mul_pos ha hKpos, ?_⟩
          rintro x ⟨y, hy, rfl⟩ i
          change |a * y i| ≤ a * K
          rw [abs_mul, abs_of_pos ha]
          exact mul_le_mul_of_nonneg_left (hK y hy i) ha.le
        refine ⟨?_, ?_, ?_⟩
        · change IsOpen (e '' W)
          exact (e.isOpen_image).2 hW.isOpen
        · exact hbd
        · change Convex ℝ (a • W)
          exact hW.convex.smul a
      obtain ⟨u0, hu0, hsol0⟩ := hD0 ⟨lam, hlampos⟩ f0 W' hW'
      have huScale := aux_physical_rescaling_kernel_conjugacy_massive_unscale
        (U := W) (a := a) (α := α) (r := r) (μ := μ) (lam := lam)
        (c := c) (rho := rho) (C := C) (R := R) (u := u0)
        (f0 := fun y => f0 y) (f := fun y => f y)
        ha hα hr hμ hC hR hf hsol0
      have hzeroLocal :
          IsMassiveWeakSolutionOn C R μ W (uN -
            ((r * a ^ 2)⁻¹ • u0.unscale ha)) (fun _ ↦ (0 : ℝ)) := by
        have hs := IsMassiveWeakSolutionOn.sub
          (B.ell k) (B.rho_measurable k) (B.rho_bounded k)
          (hff k) (hff k) hsolN huScale
        simpa using! hs
      refine ⟨uN - ((r * a ^ 2)⁻¹ • u0.unscale ha), ?_, hzeroLocal⟩
      filter_upwards [ae_restrict_mem hW.isOpen.measurableSet] with y hy
      simp only [H1Function.sub_toFun, H1Function.smul_toFun,
        H1Function.unscale_toFun]
      simp only [ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply]
      rw [huN y hy]
      rw [hv_apply y]
      rw [hu0 (a • y) ⟨y, hy, rfl⟩]
  intro x
  have hx := hzero x
  simpa only [ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply, hv_apply] using! sub_eq_zero.mp hx



theorem physical_rescaling_kernel_conjugacy
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (_hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (sigma : ℕ → BilateralField d → BilateralField d)
    (hsigmadef : ∀ N omega (j : ℤ) (x : SpatialCoordinates d),
      sigma N omega j x = omega (j + (N : ℤ)) (((3 : ℝ) ^ N) • x)) :
    ∀ N : ℕ, ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (t : NNReal) (x : SpatialCoordinates d),
        PN N (sigma N omega) t x =
          Measure.map (fun y : SpatialCoordinates d => ((3 : ℝ)⁻¹ ^ N) • y)
            (PN 0 omega (physicalTimeFactor M N * t) (((3 : ℝ) ^ N) • x)) := by
  let g : ℕ → BilateralField d → ℕ → SpatialCoordinates d → ℝ :=
    fun N omega i y =>
      omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y)
  let af : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
    fun N omega y => Real.exp (∑ i ∈ Finset.range (N + 1),
      (g N omega i y - _root_.SubdiffusiveProcess.Model.tauSq M.P))
  have hg : ∀ N omega i y, g N omega i y =
      omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y) := by
    intro N omega i y
    rfl
  have haf : ∀ N omega y, af N omega y = Real.exp (∑ i ∈ Finset.range (N + 1),
      (g N omega i y - _root_.SubdiffusiveProcess.Model.tauSq M.P) : ℝ) := by
    intro N omega y
    rfl
  obtain ⟨_, hseriesCoeff⟩ := coefficient_physical_identity M H hH g hg af haf
  have hseries : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ x : SpatialCoordinates d, HasSum
        (fun n : ℕ => omega (Int.ofNat (n + 1)) x -
          omega (Int.ofNat (n + 1)) 0) (H omega x) := by
    filter_upwards [hseriesCoeff] with omega hω
    intro x
    convert hω 0 x using 1
    funext n
    dsimp [g]
    norm_num
    congr 1 <;> ring
  have hmp : ∀ N, MeasurePreserving (sigma N)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure := by
    intro N
    exact aux_physical_generator_reindexing_sigma_measurePreserving
      M sigma hsigmadef N
  have hV := aux_physical_generator_reindexing_potential_identity
    H sigma hsigmadef (chaosSampleLaw M).toMeasure hseries hmp
  intro N
  have hresSigma := (hmp N).quasiMeasurePreserving.ae hin.1
  have hpathSigma := (hmp N).quasiMeasurePreserving.ae hin.2.2
  have hpot := hV N
  filter_upwards [hin.1, hresSigma, hpot, hin.2.2, hpathSigma]
    with omega hres0 hresN hpot hpath0 hpathN
  intro t x
  let : IsMarkovKernel (PN N (sigma N omega) t) :=
    (hin.2.1 N (sigma N omega)).isMarkovKernel t
  let : IsMarkovKernel
      (PN 0 omega (physicalTimeFactor M N * t)) :=
    (hin.2.1 0 omega).isMarkovKernel _
  refine Measure.ext_of_integral_eq_on_compactlySupported fun f ↦ ?_
  let f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ := {
    toFun := fun y => f y
    continuous_toFun := f.continuous
    zero_at_infty' := zero_at_infty f }
  obtain ⟨a, α, r, ha, hα, hr, hfactor, hC, hR, haeq⟩ :=
    aux_physical_rescaling_kernel_conjugacy_coefficient_scale
      M H sigma N omega hpot
  obtain ⟨D0, hD0dense, hD0, hD0eq⟩ := hres0 0
  obtain ⟨DN, hDNdense, hDN, hDNeq⟩ := hresN N
  have hCcont : Continuous (cutoffCoefficient M H (sigma N omega) N) :=
    _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous M H (sigma N omega) N
  have hRcont : Continuous (cutoffSpeedDensity M H (sigma N omega) N) := by
    unfold cutoffSpeedDensity cutoffPotential
    fun_prop
  have hCpos : ∀ x, 0 < cutoffCoefficient M H (sigma N omega) N x := by
    intro x
    exact _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos M H (sigma N omega) N x
  have hRpos : ∀ x, 0 < cutoffSpeedDensity M H (sigma N omega) N x := by
    intro x
    exact Real.exp_pos _
  let B := Classical.choice
    (aux_physical_rescaling_kernel_conjugacy_massive_bounds hCcont hRcont hCpos hRpos)
  have hclock : 0 < (physicalTimeFactor M N : ℝ) := by
    exact (NNReal.coe_pos.mpr (by
      change 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M 0 * (3 : ℝ) ^ (2 * N) /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N
      exact div_pos
        (mul_pos (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M 0) (pow_pos (by norm_num) _))
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)))
  have hq : 0 < r * a ^ 2 := by
    rw [← hfactor]
    exact hclock
  let f0 : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ := {
    toFun := fun y => f (a⁻¹ • y)
    continuous_toFun := f.continuous.comp (by simpa only using!
      ((continuous_const : Continuous (fun _ : SpatialCoordinates d ↦ a⁻¹)).smul
        (continuous_id : Continuous (id : SpatialCoordinates d → SpatialCoordinates d))))
    zero_at_infty' := (zero_at_infty f).comp
      (Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha.ne')).toCocompactMap.cocompact_tendsto' }
  have hf0 : ∀ y : SpatialCoordinates d, f0 (a • y) = f y := by
    intro y
    dsimp [f0]
    simp [ha.ne']
  have hsol : ∀ (lam : ℝ), ∀ hlam : 0 < lam, ∀ x,
      DN.solution ⟨r * a ^ 2 * lam, mul_pos hq hlam⟩ f x =
        (r * a ^ 2)⁻¹ * D0.solution ⟨lam, hlam⟩ f0 (a • x) := by
    intro lam hlam x
    exact aux_physical_rescaling_kernel_conjugacy_resolvent_solution
      (a := a) (α := α) (r := r) (μ := r * a ^ 2 * lam) (lam := lam)
      (c := cutoffCoefficient M H omega 0)
      (rho := cutoffSpeedDensity M H omega 0)
      (C := cutoffCoefficient M H (sigma N omega) N)
      (R := cutoffSpeedDensity M H (sigma N omega) N)
      ha (ne_of_gt hα) hr (by rfl) hC hR (mul_pos hq hlam) hlam B D0 DN
      hD0 hDN f0 f hf0 x
  have hLap : ∀ (lam : ℝ), 0 < lam → ∀ x,
      (∫ t in Set.Ioi (0 : ℝ), Real.exp (-((r * a ^ 2) * lam) * t) *
          kernelIntegral (PN N (sigma N omega) (Real.toNNReal t)) f x) =
        (r * a ^ 2)⁻¹ *
          ∫ t in Set.Ioi (0 : ℝ), Real.exp (-lam * t) *
            kernelIntegral (PN 0 omega (Real.toNNReal t)) f0 (a • x) := by
    intro lam hlam x
    have hs := hsol lam hlam x
    rw [hDNeq ⟨r * a ^ 2 * lam, mul_pos hq hlam⟩ f x,
      hD0eq ⟨lam, hlam⟩ f0 (a • x)] at hs
    exact hs
  let : IsMarkovKernel (KN N) := hKN N
  let : IsMarkovKernel (KN 0) := hKN 0
  have hFN := aux_physical_rescaling_kernel_conjugacy_path_integral
    (PN N (sigma N omega)) (KN N (sigma N omega, x)) x
    (fun s ↦ by
      rw [← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation _)]
      exact hpathN N ({s} : Finset NNReal) x) f
  have hF0 := aux_physical_rescaling_kernel_conjugacy_path_integral
    (PN 0 omega) (KN 0 (omega, a • x)) (a • x)
    (fun s ↦ by
      rw [← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation _)]
      exact hpath0 0 ({s} : Finset NNReal) (a • x)) f0
  let F : ℝ → ℝ := fun s ↦
    kernelIntegral (PN N (sigma N omega) (Real.toNNReal s)) f x
  let G : ℝ → ℝ := fun s ↦
    kernelIntegral (PN 0 omega (Real.toNNReal s)) f0 (a • x)
  have hFcont : Continuous F := by
    simpa [F] using hFN.2
  have hGcont : Continuous G := by
    simpa [G] using hF0.2
  have hqchange : ∀ (lam : ℝ), 0 < lam →
      (∫ s in Set.Ioi (0 : ℝ), Real.exp (-((r * a ^ 2) * lam) * s) *
          G ((r * a ^ 2) * s)) =
        (r * a ^ 2)⁻¹ *
          ∫ s in Set.Ioi (0 : ℝ), Real.exp (-lam * s) * G s := by
    intro lam hlam
    have hc := MeasureTheory.integral_comp_mul_left_Ioi
      (fun s : ℝ => Real.exp (-lam * s) * G s) 0 hq
    convert! hc using 1 <;>
      (try simp only [mul_zero, smul_eq_mul]) ; ring
  have hLap' : ∀ (lam : ℝ), 0 < lam →
      ∫ s in Set.Ioi (0 : ℝ), Real.exp (-((r * a ^ 2) * lam) * s) * F s =
        ∫ s in Set.Ioi (0 : ℝ), Real.exp (-((r * a ^ 2) * lam) * s) *
          G ((r * a ^ 2) * s) := by
    intro lam hlam
    calc
      ∫ s in Set.Ioi (0 : ℝ), Real.exp (-((r * a ^ 2) * lam) * s) * F s =
          (r * a ^ 2)⁻¹ * ∫ s in Set.Ioi (0 : ℝ), Real.exp (-lam * s) * G s := by
            simpa [F, G] using hLap lam hlam x
      _ = ∫ s in Set.Ioi (0 : ℝ), Real.exp (-((r * a ^ 2) * lam) * s) *
          G ((r * a ^ 2) * s) := (hqchange lam hlam).symm
  have hLap'' : ∀ (mu : ℝ), 0 < mu →
      ∫ s in Set.Ioi (0 : ℝ), Real.exp (-(mu * s)) * F s =
        ∫ s in Set.Ioi (0 : ℝ), Real.exp (-(mu * s)) *
          (G ∘ fun z : ℝ => (r * a ^ 2) * id z) s := by
    intro mu hmu
    have hlam : 0 < mu / (r * a ^ 2) := div_pos hmu hq
    have h := hLap' (mu / (r * a ^ 2)) hlam
    have hmul : (r * a ^ 2) * (mu / (r * a ^ 2)) = mu := by
      field_simp [ne_of_gt hq]
    simpa [Function.comp_apply, hmul] using h
  have hboundF : ∀ s : ℝ, |F s| ≤ max ‖f.toBCF‖ ‖f0.toBCF‖ := by
    intro s
    rw [show F s = ∫ path, f (path (Real.toNNReal s))
        ∂(KN N (sigma N omega, x)) by
          exact hFN.1 s]
    exact (abs_integral_coordinate_le f _ _).trans (le_max_left _ _)
  have hboundG : ∀ s : ℝ, |G ((r * a ^ 2) * s)| ≤
      max ‖f.toBCF‖ ‖f0.toBCF‖ := by
    intro s
    rw [show G ((r * a ^ 2) * s) =
        ∫ path, f0 (path (Real.toNNReal ((r * a ^ 2) * s)))
          ∂(KN 0 (omega, a • x)) by exact hF0.1 _]
    exact (abs_integral_coordinate_le f0 _ _).trans (le_max_right _ _)
  have htime : ∀ s : ℝ, 0 ≤ s → F s = G ((r * a ^ 2) * s) := by
    intro s hs
    exact eq_of_forall_integral_exp_neg_mul_eq hFcont
      (hGcont.comp (continuous_const.mul continuous_id))
      hboundF hboundG hLap'' s hs
  have hqtime : (r * a ^ 2) * (t : ℝ) =
      ((physicalTimeFactor M N * t : NNReal) : ℝ) := by
    rw [← hfactor]
    norm_num
  have hkernelIntegral :
      kernelIntegral (PN N (sigma N omega) t) f x =
        kernelIntegral (PN 0 omega (physicalTimeFactor M N * t)) f0 (a • x) := by
    have hs := htime (t : ℝ) t.coe_nonneg
    simp only [F, G] at hs
    rw [hqtime] at hs
    simp only [NNReal.coe_mul] at hs
    have hnn : Real.toNNReal (((physicalTimeFactor M N : ℝ) * (t : ℝ))) =
        physicalTimeFactor M N * t := by
      apply NNReal.eq
      rw [Real.coe_toNNReal]
      · simp [NNReal.coe_mul]
      · positivity
    rw [hnn] at hs
    simpa only [Real.toNNReal_coe] using hs
  have hdilation : ∀ y : SpatialCoordinates d,
      ((3 : ℝ)⁻¹ ^ N) • y = a⁻¹ • y := by
    intro y
    rw [haeq]
    congr 1
    simp only [inv_pow]
  have hmapIntegral :
      (∫ y, f y ∂Measure.map (fun y : SpatialCoordinates d =>
        ((3 : ℝ)⁻¹ ^ N) • y)
          (PN 0 omega (physicalTimeFactor M N * t) (a • x))) =
        kernelIntegral (PN 0 omega (physicalTimeFactor M N * t)) f0 (a • x) := by
    rw [kernelIntegral]
    rw [MeasureTheory.integral_map]
    · apply integral_congr_ae
      filter_upwards [] with y
      dsimp [f0]
      rw [hdilation]
    · have hscale : Continuous (fun y : SpatialCoordinates d ↦ ((3 : ℝ)⁻¹ ^ N) • y) := by
        simpa only using!
          ((continuous_const : Continuous (fun _ : SpatialCoordinates d ↦ (3 : ℝ)⁻¹ ^ N)).smul
            (continuous_id : Continuous (id : SpatialCoordinates d → SpatialCoordinates d)))
      exact hscale.measurable.aemeasurable
    · exact f.continuous.aestronglyMeasurable
  rw [kernelIntegral] at hkernelIntegral
  change (∫ y, f y ∂(PN N (sigma N omega) t) x) =
    ∫ y, f y ∂Measure.map (fun y : SpatialCoordinates d =>
      ((3 : ℝ)⁻¹ ^ N) • y)
        (PN 0 omega (physicalTimeFactor M N * t) (((3 : ℝ) ^ N) • x))
  calc
    (∫ y, f y ∂(PN N (sigma N omega) t) x) =
        kernelIntegral (PN N (sigma N omega) t) f x := rfl
    _ = kernelIntegral (PN 0 omega (physicalTimeFactor M N * t)) f0 (a • x) :=
      hkernelIntegral
    _ = ∫ y, f y ∂Measure.map (fun y : SpatialCoordinates d =>
        ((3 : ℝ)⁻¹ ^ N) • y)
          (PN 0 omega (physicalTimeFactor M N * t) (a • x)) := hmapIntegral.symm
    _ = ∫ y, f y ∂Measure.map (fun y : SpatialCoordinates d =>
        ((3 : ℝ)⁻¹ ^ N) • y)
          (PN 0 omega (physicalTimeFactor M N * t) (((3 : ℝ) ^ N) • x)) := by
      rw [haeq]

end SubdiffusiveProcess.Paper
