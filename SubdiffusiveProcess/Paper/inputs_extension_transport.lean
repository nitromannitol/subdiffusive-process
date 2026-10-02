import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Sobolev.NativeH1
import SubdiffusiveProcess.Sobolev.NativeH10
import SubdiffusiveProcess.Lane2.VecDotForm
import SubdiffusiveProcess.Lane2.CellAssembly
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FractionalTransport
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FractionalDatum
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.EquationTranslation
import Homogenization.Sobolev.Fractional.EuclideanWspLpMembership

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem aux_inputs_extension_transport_inner {d : ℕ}
    {Ω : Opens (SpatialCoordinates d)} (F G : HilbertGradient Ω) :
    inner ℝ F G = ∫ x in (Ω : Set (SpatialCoordinates d)),
      Homogenization.vecDot (fun i => (F i : SpatialCoordinates d → ℝ) x)
        (fun i => (G i : SpatialCoordinates d → ℝ) x) ∂volume := by
  have hint (i : Fin d) : IntegrableOn
      (fun x => (F i : SpatialCoordinates d → ℝ) x *
        (G i : SpatialCoordinates d → ℝ) x)
      (Ω : Set (SpatialCoordinates d)) volume := by
    have h := L2.integrable_inner (𝕜 := ℝ) (E := ℝ) (F i) (G i)
    apply h.congr
    filter_upwards [] with x
    simp [RCLike.inner_apply] <;> ring
  calc
    inner ℝ F G = ∑ i : Fin d, inner ℝ (F i) (G i) := PiLp.inner_apply F G
    _ = ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
        (F i : SpatialCoordinates d → ℝ) x * (G i : SpatialCoordinates d → ℝ) x
          ∂volume := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [L2.inner_def (𝕜 := ℝ) (E := ℝ)]
      apply integral_congr_ae
      filter_upwards [] with x
      simp [RCLike.inner_apply] <;> ring
    _ = ∫ x in (Ω : Set (SpatialCoordinates d)),
        ∑ i : Fin d, (F i : SpatialCoordinates d → ℝ) x *
          (G i : SpatialCoordinates d → ℝ) x ∂volume := by
      rw [← integral_finset_sum _ (fun i _ => hint i)]
    _ = ∫ x in (Ω : Set (SpatialCoordinates d)),
        Homogenization.vecDot (fun i => (F i : SpatialCoordinates d → ℝ) x)
          (fun i => (G i : SpatialCoordinates d → ℝ) x) ∂volume := by
      simp [Homogenization.vecDot]

theorem aux_inputs_extension_transport_h10_cast_grad {d : ℕ}
    {U V : Set (Homogenization.Vec d)} (h : U = V)
    (φ : Homogenization.H10Function V) :
    (h.symm ▸ φ).toH1Function.grad = φ.toH1Function.grad := by
  cases h
  rfl

theorem aux_inputs_extension_transport_h1_cast_grad {d : ℕ}
    {U V : Set (Homogenization.Vec d)} (h : U = V)
    (u : Homogenization.H1Function U) :
    (h ▸ u).grad = u.grad := by
  cases h
  rfl

theorem aux_inputs_extension_transport_h1_cast_value {d : ℕ}
    {U V : Set (Homogenization.Vec d)} (h : U = V)
    (u : Homogenization.H1Function U) :
    (h ▸ u).toFun = u.toFun := by
  cases h
  rfl

theorem aux_inputs_extension_transport_h10_cast_value {d : ℕ}
    {U V : Set (Homogenization.Vec d)} (h : U = V)
    (u : Homogenization.H10Function U) :
    (h ▸ u).toH1Function.toFun = u.toH1Function.toFun := by
  cases h
  rfl

theorem aux_inputs_extension_transport_domain {d : ℕ} (z : SpatialCoordinates d)
    (m : ℕ) (hr : (0 : ℝ) < 3 ^ m) :
    (centeredCube z ((3 : ℝ) ^ m) hr : Set (SpatialCoordinates d)) =
      Homogenization.translateSet z
        (Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ))) := by
  ext x
  rw [Homogenization.mem_translateSet_iff_sub_mem]
  rw [centeredCube_eq_pi]
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo,
    Homogenization.openCubeSet, Homogenization.originCube,
    Homogenization.cubeScaleFactor, Pi.zero_apply,
    zpow_natCast]
  simp only [Set.mem_setOf_eq]
  norm_num
  constructor
  · intro hx
    intro i
    rcases hx i with ⟨hlo, hhi⟩
    constructor <;> linarith
  · intro hx
    intro i
    rcases hx i with ⟨hlo, hhi⟩
    constructor <;> linarith

theorem aux_inputs_extension_transport_chart {d : ℕ} (m : ℕ)
    (z : SpatialCoordinates d) (hr : (0 : ℝ) < 3 ^ m)
    (a : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ m) hr))
    (Jc : Paper.in_J d) :
    let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
    let A : Homogenization.Book.Ch02.TriadicCoeffFamily d :=
      Homogenization.Book.Ch02.TriadicCoeffFamily.dilate (m : ℤ)
        (Jc.chart z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m))
    (A.coeffOn Q).toCoeffField =ᵐ[volume.restrict (Homogenization.openCubeSet Q)]
      fun y => Homogenization.scalarMatrix (a.val (fun i => y i + z i)) := by
  dsimp
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let Q₀ : Homogenization.TriadicCube d := Homogenization.originCube d 0
  let c : Homogenization.Book.Ch02.TriadicCoeffFamily d :=
    Jc.chart z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m)
  let A : Homogenization.Book.Ch02.TriadicCoeffFamily d :=
    Homogenization.Book.Ch02.TriadicCoeffFamily.dilate (m : ℤ) c
  have hDil := Homogenization.Book.Ch02.TriadicCoeffFamily.isDilation_dilate
    (m : ℤ) c Q₀
  rcases hDil with ⟨_, _, hCubeDil⟩
  have hDilCoeff :
      (A.coeffOn Q).toCoeffField =ᵐ[volume.restrict (Homogenization.openCubeSet Q)]
        fun y => Homogenization.Book.Ch02.dilateCoeffField (m : ℤ)
          (c.coeffOn Q₀).toCoeffField y := by
    have hQ : Homogenization.Book.Ch02.dilateCube (m : ℤ) Q₀ = Q := by
      simp [Q, Q₀, Homogenization.Book.Ch02.dilateCube,
        Homogenization.originCube]
    rw [← hQ]
    simpa only [A] using hCubeDil
  have hchart := Jc.chart_eq z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) hr
    (Set.Subset.rfl) Q₀ (by simp [Q₀])
  have hchartDil :=
    Homogenization.Book.Ch02.eventuallyEq_comp_undilate_of_ae_eq
      (m : ℤ) hchart
  have hscale : Homogenization.Book.Ch02.triadicDilationFactor (m : ℤ) =
      (3 : ℝ) ^ m := by
    simp [Homogenization.Book.Ch02.triadicDilationFactor, zpow_natCast]
  have hcoord (y : Homogenization.Vec d) :
      (fun i => z i + (3 : ℝ) ^ m *
          Homogenization.Book.Ch02.undilateVec (m : ℤ) y i) =
        fun i => y i + z i := by
    funext i
    simp only [Homogenization.Book.Ch02.undilateVec, Pi.smul_apply, smul_eq_mul]
    rw [← hscale]
    calc
      z i + Homogenization.Book.Ch02.triadicDilationFactor (m : ℤ) *
          ((Homogenization.Book.Ch02.triadicDilationFactor (m : ℤ))⁻¹ * y i) =
          z i + (Homogenization.Book.Ch02.triadicDilationFactor (m : ℤ) *
            (Homogenization.Book.Ch02.triadicDilationFactor (m : ℤ))⁻¹) * y i := by ring
      _ = y i + z i := by
        rw [mul_inv_cancel₀
          (ne_of_gt (Homogenization.Book.Ch02.triadicDilationFactor_pos _))]
        ring
  have hchartDil' :
      (fun y => Homogenization.Book.Ch02.dilateCoeffField (m : ℤ)
        (c.coeffOn Q₀).toCoeffField y) =ᵐ[volume.restrict (Homogenization.openCubeSet Q)]
        fun y => Homogenization.scalarMatrix (a.val (fun i => y i + z i)) := by
    have hchartDil'' :
        (fun y => (c.coeffOn Q₀).toCoeffField
          (Homogenization.Book.Ch02.undilateVec (m : ℤ) y)) =ᵐ[
            volume.restrict (Homogenization.openCubeSet Q)]
          fun y => Homogenization.scalarMatrix
            (a.val (fun i => y i + z i)) := by
      have hQ : Homogenization.Book.Ch02.dilateCube (m : ℤ) Q₀ = Q := by
        simp [Q, Q₀, Homogenization.Book.Ch02.dilateCube,
          Homogenization.originCube]
      simpa [Q, Q₀, hQ, Homogenization.volumeMeasureOn, hcoord] using hchartDil
    filter_upwards [hchartDil''] with y hy
    simpa [Homogenization.Book.Ch02.dilateCoeffField] using hy
  exact hDilCoeff.trans hchartDil'

theorem aux_inputs_extension_transport_fractionalKernelSq {d : ℕ}
    (s : Homogenization.FractionalOrder) (f : Homogenization.Vec d → Homogenization.Vec d)
    (xy : Homogenization.Vec d × Homogenization.Vec d) :
    ‖SubdiffusiveProcess.CoarseGrainingVocab.fractionalKernel s.1 f xy‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal (∑ i : Fin d, (f xy.1 i - f xy.2 i) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (xy.1 j - xy.2 j) ^ 2))) ^
          ((d : ℝ) + 2 * s.1) := by
  rw [← ofReal_norm_eq_enorm]
  rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two]
  have hnorm : SubdiffusiveProcess.CoarseGrainingVocab.fractionalKernel s.1 f xy =
      ‖Homogenization.cubeEuclideanWspKernel s Homogenization.FiniteLpExponent.two f xy‖ := by
    rw [SubdiffusiveProcess.CoarseGrainingVocab.fractionalKernel,
      Homogenization.norm_cubeEuclideanWspKernel,
      Homogenization.euclideanDist]
    rw [Real.rpow_neg (Homogenization.euclideanNorm_nonneg _)]
    rw [Homogenization.FiniteLpExponent.two_exponent]
    norm_num
    ring
  have hkernelSq :
      ‖Homogenization.cubeEuclideanWspKernel s Homogenization.FiniteLpExponent.two f xy‖ₑ ^
          (2 : ℝ) =
        ENNReal.ofReal (∑ i : Fin d, (f xy.1 i - f xy.2 i) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (xy.1 j - xy.2 j) ^ 2))) ^
            ((d : ℝ) + 2 * s.1) := by
    rw [← ofReal_norm_eq_enorm]
    rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two]
    rw [Homogenization.norm_cubeEuclideanWspKernel]
    norm_num
    let a : ℝ := (d : ℝ) + 2 * s.1
    rw [show -((d : ℝ) / 2) + -s.1 = -a / 2 by dsimp [a]; ring]
    rw [show (d : ℝ) + 2 * s.1 = a by simp [a, add_comm, mul_comm]]
    by_cases hxy : xy.1 = xy.2
    · rw [hxy]
      simp
    · have hpos : 0 < Homogenization.euclideanDist xy.1 xy.2 := by
        apply lt_of_le_of_ne (Homogenization.euclideanDist_nonneg _ _)
        intro hzero
        exact hxy (Homogenization.euclideanDist_eq_zero_iff.mp hzero.symm)
      rw [mul_pow]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
      norm_num only [Nat.cast_ofNat]
      rw [show (-a / 2) * (2 : ℝ) = -a by ring]
      rw [Real.rpow_neg hpos.le]
      rw [mul_comm, ← div_eq_mul_inv]
      rw [ENNReal.ofReal_div_of_pos]
      rw [← ENNReal.ofReal_rpow_of_pos hpos]
      unfold Homogenization.euclideanDist Homogenization.euclideanNorm
      simp only [Homogenization.vecNormSq, Homogenization.vecDot, Pi.sub_apply,
        pow_two]
      rw [show Real.sqrt (∑ i : Fin d, (f xy.1 i - f xy.2 i) *
          (f xy.1 i - f xy.2 i)) * Real.sqrt (∑ i : Fin d,
            (f xy.1 i - f xy.2 i) * (f xy.1 i - f xy.2 i)) =
          ∑ i : Fin d, (f xy.1 i - f xy.2 i) * (f xy.1 i - f xy.2 i) by
        rw [← pow_two, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => mul_self_nonneg _))]]
      all_goals exact Real.rpow_pos_of_pos hpos _
  calc
    ENNReal.ofReal (‖SubdiffusiveProcess.CoarseGrainingVocab.fractionalKernel s.1 f xy‖ ^ (2 : ℝ)) =
        ENNReal.ofReal (‖Homogenization.cubeEuclideanWspKernel s
          Homogenization.FiniteLpExponent.two f xy‖ ^ (2 : ℝ)) := by
            rw [hnorm, norm_norm]
    _ = ‖Homogenization.cubeEuclideanWspKernel s
          Homogenization.FiniteLpExponent.two f xy‖ₑ ^ (2 : ℝ) := by
        rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two,
          ofReal_norm_eq_enorm]
    _ = _ := hkernelSq

theorem aux_inputs_extension_transport_raw_eq_fractionalOn {d : ℕ}
    (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : Set.Ioo (0 : ℝ) 1)
    (f : Fin d → DomainL2 (centeredCube z r hr)) :
    cubeFractionalL2Seminorm hd z r hr s f =
      SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn
        (centeredCube z r hr : Set (SpatialCoordinates d)) s.1
        (fun x i => f i x) := by
  let Ω : Set (SpatialCoordinates d) := centeredCube z r hr
  let μ : Measure (SpatialCoordinates d) := volume.restrict Ω
  let F : SpatialCoordinates d → SpatialCoordinates d := fun x i => f i x
  let raw : SpatialCoordinates d × SpatialCoordinates d → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (∑ i : Fin d, (f i q.1 - f i q.2) ^ 2) /
      (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ 2))) ^
        ((d : ℝ) + 2 * s.1)
  have hcoord (i : Fin d) : AEMeasurable
      (fun q : SpatialCoordinates d × SpatialCoordinates d =>
        (f i q.1 : ℝ) - f i q.2) (μ.prod μ) := by
    have hf : AEStronglyMeasurable (fun x : SpatialCoordinates d => (f i x : ℝ)) μ := by
      simpa only [μ, Ω] using Lp.aestronglyMeasurable (f i)
    exact (hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).aemeasurable.sub
      (hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).aemeasurable
  have hnum : AEMeasurable (fun q : SpatialCoordinates d × SpatialCoordinates d =>
      ∑ i : Fin d, ((f i q.1 : ℝ) - f i q.2) ^ 2) (μ.prod μ) :=
    Finset.aemeasurable_fun_sum Finset.univ fun i _ => (hcoord i).pow_const 2
  have hden : Measurable (fun q : SpatialCoordinates d × SpatialCoordinates d =>
      (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (q.1 j - q.2 j) ^ 2))) ^
        ((d : ℝ) + 2 * s.1)) := by
    apply Measurable.pow
    · apply Measurable.ennreal_ofReal
      apply Measurable.sqrt
      exact Finset.measurable_sum Finset.univ fun j _ =>
        (((measurable_pi_apply j).comp measurable_fst).sub
          ((measurable_pi_apply j).comp measurable_snd)).pow_const 2
    · exact measurable_const
  have hraw : AEMeasurable raw (μ.prod μ) := by
    exact hnum.ennreal_ofReal.div hden.aemeasurable
  have hkernel : AEMeasurable (fun q : SpatialCoordinates d × SpatialCoordinates d =>
      ‖SubdiffusiveProcess.CoarseGrainingVocab.fractionalKernel s.1 F q‖ₑ ^ (2 : ℝ)) (μ.prod μ) := by
    refine hraw.congr ?_
    filter_upwards [] with q
    dsimp [raw, F]
    exact (aux_inputs_extension_transport_fractionalKernelSq s
      (fun x i => f i x) q).symm
  have hintegral :
      (∫⁻ x in Ω, ∫⁻ y in Ω, raw (x, y) ∂volume ∂volume) =
        ∫⁻ q, ‖SubdiffusiveProcess.CoarseGrainingVocab.fractionalKernel s.1 F q‖ₑ ^ (2 : ℝ)
          ∂(μ.prod μ) := by
    change (∫⁻ x, ∫⁻ y, raw (x, y) ∂μ ∂μ) = _
    rw [← lintegral_prod raw hraw]
    apply lintegral_congr_ae
    filter_upwards [] with q
    dsimp [raw, F]
    exact (aux_inputs_extension_transport_fractionalKernelSq s
      (fun x i => f i x) q).symm
  unfold cubeFractionalL2Seminorm SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn
  dsimp [Ω, raw, F] at hintegral ⊢
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat]
  rw [← hintegral]
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]

theorem inputs_extension_transport (d : ℕ) (hd : 2 ≤ d) (Jc : Paper.in_J d) :
    (∀ (z : SpatialCoordinates d) (m : ℕ) (hr : (0 : ℝ) < 3 ^ m)
      (a : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ m) hr))
      (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1)
      
      (g : HilbertGradient (centeredCube z ((3 : ℝ) ^ m) hr)),
      cubeFractionalL2Seminorm hd z ((3 : ℝ) ^ m) hr ⟨s, hs.1, hs.2⟩
          (fun i => g i) ≠ ⊤ →
      
      ∀ (hDatum v : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hr))
        (hhfin : cubeFractionalL2Seminorm hd z ((3 : ℝ) ^ m) hr ⟨s, hs.1, hs.2⟩
          (fun i => sobolevGradient (hDatum : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr)) i) ≠ ⊤),
      
      (∀ φ : killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hr),
        sobolevCoefficientForm a (v : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr)) (φ : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr)) =
          -inner ℝ g
            (subspaceGradient
              (killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hr)) φ)) →
      
      ((v : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr)) -
          (hDatum : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr))) ∈
        killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hr) →
      let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ);
      let A : Homogenization.Book.Ch02.TriadicCoeffFamily d :=
        Homogenization.Book.Ch02.TriadicCoeffFamily.dilate (m : ℤ)
          (Jc.chart z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m));
      let gs : Homogenization.Vec d → Homogenization.Vec d :=
        fun y i => -((g i : SpatialCoordinates d → ℝ) (y + z));
      Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp Q
        ⟨s, hs.1, hs.2⟩ Homogenization.FiniteLpExponent.two gs ∧
      ∃ u : Homogenization.Book.Ch03.DirichletForcedCubeSolution Q A gs,
        Homogenization.Book.Ch03.dirichletBoundaryGradientField u =
          (fun y i => (sobolevGradient (hDatum : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr)) i : SpatialCoordinates d → ℝ) (y + z)) ∧
        u.toH1.grad =
          (fun y i => (sobolevGradient (v : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr)) i : SpatialCoordinates d → ℝ) (y + z)) ∧
        normalizedEnergyNorm a (centeredCube z ((3 : ℝ) ^ m) hr).isOpen.measurableSet
          (sobolevGradient (v : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr))) ≤
          Homogenization.Book.Ch03.dirichletForcedSolutionEnergyNorm Q A u) := by
  intro z m hr a s hs g hg
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let A : Homogenization.Book.Ch02.TriadicCoeffFamily d :=
    Homogenization.Book.Ch02.TriadicCoeffFamily.dilate (m : ℤ)
      (Jc.chart z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m))
  let gs : Homogenization.Vec d → Homogenization.Vec d :=
    fun y i => -((g i : SpatialCoordinates d → ℝ) (y + z))
  intro hDatum v hhfin hweak hbd
  letI : NeZero d := ⟨by omega⟩
  let Ω : Opens (SpatialCoordinates d) := centeredCube z ((3 : ℝ) ^ m) hr
  let U : Set (Homogenization.Vec d) := Homogenization.openCubeSet Q
  have hdom : (Ω : Set (SpatialCoordinates d)) =
      Homogenization.translateSet z U := by
    exact aux_inputs_extension_transport_domain z m hr
  obtain ⟨hNative, hNativeVal, hNativeGrad⟩ :=
    SubdiffusiveProcess.exists_nativeH1Function_of_weakSobolevGraph hDatum
  obtain ⟨vNative, vNativeVal, vNativeGrad⟩ :=
    SubdiffusiveProcess.exists_nativeH1Function_of_weakSobolevGraph v
  let diff : killedSobolevGraph Ω := ⟨
    (v : SobolevData Ω) - (hDatum : SobolevData Ω), hbd⟩
  obtain ⟨rho, rhoVal, rhoGrad⟩ :=
    SubdiffusiveProcess.exists_nativeH10Function_of_killedSobolevGraph diff
  let hT : Homogenization.H1Function (Homogenization.translateSet z U) :=
    hdom ▸ hNative
  let vT : Homogenization.H1Function (Homogenization.translateSet z U) :=
    hdom ▸ vNative
  let rhoT : Homogenization.H10Function (Homogenization.translateSet z U) :=
    hdom ▸ rho
  let hQ : Homogenization.H1Function U := Homogenization.H1Function.untranslate z hT
  let vQ : Homogenization.H1Function U := Homogenization.H1Function.untranslate z vT
  let rhoQ : Homogenization.H10Function U := Homogenization.H10Function.untranslate z rhoT
  have vData_eq : (v : SobolevData Ω) =
      SubdiffusiveProcess.sobolevDataOfH1 vNative := by
    apply Prod.ext
    · apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp vNative.memL2] with x hx
      change ((v : SobolevData Ω).1 : SpatialCoordinates d → ℝ) x =
        (MemLp.toLp vNative.toFun vNative.memL2 : DomainL2 Ω) x
      exact (congrFun vNativeVal x).symm.trans hx.symm
    · funext i
      apply Lp.ext
      filter_upwards [SubdiffusiveProcess.sobolevDataOfH1_snd_coeFn vNative i]
        with x hx
      change ((v : SobolevData Ω).2 i : SpatialCoordinates d → ℝ) x = _
      have hgrad : vNative.grad x i = ((v : SobolevData Ω).2 i : SpatialCoordinates d → ℝ) x :=
        congrFun (congrFun vNativeGrad x) i
      rw [← hgrad]
      exact hx.symm
  obtain ⟨Cbound, hbound⟩ := SubdiffusiveProcess.lane2_coeff_ae_bound a
  have hHint (w : Homogenization.H1Function (Ω : Set (SpatialCoordinates d)))
      (i : Fin d) : IntegrableOn
        (fun x => a.val x * (vNative.grad x i * w.grad x i))
        (Ω : Set (SpatialCoordinates d)) volume :=
    SubdiffusiveProcess.lane2_integrableOn_coeff_mul (Lp.aestronglyMeasurable a.val)
      hbound (vNative.gradMemL2 i) (w.gradMemL2 i)
  let gFun : SpatialCoordinates d → SpatialCoordinates d :=
    fun x i => (g i : SpatialCoordinates d → ℝ) x
  have hweakNative (φ : Homogenization.H10Function (Ω : Set (SpatialCoordinates d))) :
      sobolevCoefficientForm a (SubdiffusiveProcess.sobolevDataOfH1 vNative)
          (SubdiffusiveProcess.sobolevDataOfH1 φ.toH1Function) =
        -∫ x in (Ω : Set (SpatialCoordinates d)),
          Homogenization.vecDot (gFun x) (φ.toH1Function.grad x) ∂volume := by
    let φk : killedSobolevGraph Ω := ⟨
      SubdiffusiveProcess.sobolevDataOfH1 φ.toH1Function,
      SubdiffusiveProcess.sobolevDataOfH1_mem_killed φ⟩
    have heq : sobolevCoefficientForm a (v : SobolevData Ω)
        (SubdiffusiveProcess.sobolevDataOfH1 φ.toH1Function) =
          -inner ℝ g (subspaceGradient (killedSobolevGraph Ω) φk) := by
      simpa only [φk] using hweak φk
    rw [vData_eq] at heq
    have hL := SubdiffusiveProcess.sobolevCoefficientForm_eq_integral_vecDot
      a vNative φ.toH1Function (fun i => hHint φ.toH1Function i)
    rw [hL] at heq ⊢
    rw [aux_inputs_extension_transport_inner] at heq
    have hcoord (i : Fin d) :
        ((subspaceGradient (killedSobolevGraph Ω) φk i : DomainL2 Ω) :
          SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
          fun x => φ.toH1Function.grad x i := by
      change ((sobolevGradient
        (SubdiffusiveProcess.sobolevDataOfH1 φ.toH1Function) i : DomainL2 Ω) :
          SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
          fun x => φ.toH1Function.grad x i
      exact SubdiffusiveProcess.sobolevDataOfH1_snd_coeFn φ.toH1Function i
    have hInt :
        (∫ x in (Ω : Set (SpatialCoordinates d)),
          Homogenization.vecDot (fun i => (g i : SpatialCoordinates d → ℝ) x)
            (fun i => ((subspaceGradient (killedSobolevGraph Ω) φk i : DomainL2 Ω) x))
            ∂volume) =
        ∫ x in (Ω : Set (SpatialCoordinates d)),
          Homogenization.vecDot (gFun x) (φ.toH1Function.grad x) ∂volume := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.2 hcoord] with x hx
      simp only [Homogenization.vecDot]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [gFun]
      rw [hx i]
    rw [hInt] at heq
    exact heq
  have hdiv : SubdiffusiveProcess.CoarseGrainingVocab.IsDivFormWeakSolutionOn a.val
      (Ω : Set (SpatialCoordinates d)) vNative gFun := by
    exact SubdiffusiveProcess.isDivFormWeakSolutionOn_of_weak_equation
      a vNative gFun (fun w i => hHint w i) hweakNative
  have hdivT : SubdiffusiveProcess.CoarseGrainingVocab.IsDivFormWeakSolutionOn a.val
      (Homogenization.translateSet z U) vT gFun := by
    intro φ
    let φΩ : Homogenization.H10Function (Ω : Set (SpatialCoordinates d)) := hdom.symm ▸ φ
    have h := hdiv φΩ
    have hgrad := aux_inputs_extension_transport_h10_cast_grad hdom φ
    rw [hgrad] at h
    simpa [φΩ, hdom, vT, gFun] using h
  have hdivQ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.isDivFormWeakSolutionOn_untranslate
      z hdivT
  have hforce : Homogenization.Book.Ch03.IsForcedEquation Q A vQ gs := by
    intro φ
    have hdiv := hdivQ φ
    have hchart := aux_inputs_extension_transport_chart m z hr a Jc
    have hcoeff : (fun x : Homogenization.Vec d =>
        Homogenization.vecDot
          (Homogenization.matVecMul ((A.coeffOn Q).toCoeffField x) (vQ.grad x))
          (φ.toH1Function.grad x)) =ᵐ[volume.restrict U] fun x =>
        Homogenization.vecDot
          ((a.val (fun i => x i + z i)) • vQ.grad x) (φ.toH1Function.grad x) := by
      filter_upwards [hchart] with x hx
      rw [hx, Homogenization.matVecMul_scalarMatrix]
    calc
      (∫ x in U, Homogenization.vecDot
          (Homogenization.matVecMul ((A.coeffOn Q).toCoeffField x) (vQ.grad x))
          (φ.toH1Function.grad x) ∂volume) =
        ∫ x in U, Homogenization.vecDot
          ((a.val (fun i => x i + z i)) • vQ.grad x)
          (φ.toH1Function.grad x) ∂volume := by
            exact integral_congr_ae hcoeff
      _ = -∫ x in U, Homogenization.vecDot (gFun (x + z))
          (φ.toH1Function.grad x) ∂volume := hdiv
      _ = ∫ x in U, Homogenization.vecDot (gs x)
          (φ.toH1Function.grad x) ∂volume := by
            rw [← integral_neg]
            apply integral_congr_ae
            filter_upwards [] with x
            simp [gs, gFun, Homogenization.vecDot, Finset.sum_neg_distrib]
  have hzeroQ : rhoQ.toH1Function.toFun =ᵐ[
      Homogenization.volumeMeasureOn U]
        fun x => vQ.toFun x - hQ.toFun x := by
    have hzeroLocal : rho.toH1Function.toFun =ᵐ[
        volume.restrict (Ω : Set (SpatialCoordinates d))]
        fun x => vNative.toFun x - hNative.toFun x := by
      filter_upwards [Lp.coeFn_sub (v : SobolevData Ω).1
        (hDatum : SobolevData Ω).1] with x hx
      rw [rhoVal, vNativeVal, hNativeVal]
      exact hx
    have hrhoT := aux_inputs_extension_transport_h10_cast_value hdom rho
    have hvT := aux_inputs_extension_transport_h1_cast_value hdom vNative
    have hhT := aux_inputs_extension_transport_h1_cast_value hdom hNative
    have hzeroTrans : rhoT.toH1Function.toFun =ᵐ[
        volume.restrict (Homogenization.translateSet z U)]
        fun x => vT.toFun x - hT.toFun x := by
      rw [hrhoT, hvT, hhT]
      simpa only [← hdom] using hzeroLocal
    have hzeroPull :=
      (Homogenization.measurePreserving_addRight_restrict_translateSet z U).quasiMeasurePreserving.ae_eq
        hzeroTrans
    simpa [Homogenization.volumeMeasureOn, rhoQ, vQ, hQ,
      Homogenization.H10Function.untranslate_toH1Function,
      Homogenization.H1Function.untranslate_toFun] using hzeroPull
  have hFull : Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp Q
      ⟨s, hs.1, hs.2⟩ Homogenization.FiniteLpExponent.two gs := by
    let sOrder : Homogenization.FractionalOrder := ⟨s, hs.1, hs.2⟩
    let gQ : Homogenization.Vec d → Homogenization.Vec d :=
      fun y i => (g i : SpatialCoordinates d → ℝ) (y + z)
    have hfracLocal : SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn
        (Ω : Set (SpatialCoordinates d)) s gFun ≠ ⊤ := by
      rw [← aux_inputs_extension_transport_raw_eq_fractionalOn hd z ((3 : ℝ) ^ m) hr
        ⟨s, hs.1, hs.2⟩ (fun i => g i)]
      exact hg
    have hfracTrans : SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn
        (Homogenization.translateSet z U) s gFun ≠ ⊤ := by
      simpa only [hdom] using hfracLocal
    have hfracQ : SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn U s gQ ≠ ⊤ := by
      rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.fractionalSeminormOn_translateSet
        z U s gFun] at hfracTrans
      simpa only [gFun, gQ] using hfracTrans
    have hgCoord (i : Fin d) : MemLp
        (fun y : Homogenization.Vec d => (g i : SpatialCoordinates d → ℝ) (y + z))
        2 (volume.restrict U) := by
      have hgi : MemLp (fun x : SpatialCoordinates d => (g i : SpatialCoordinates d → ℝ) x)
          2 (volume.restrict (Homogenization.translateSet z U)) := by
        simpa only [← hdom] using (Lp.memLp (g i))
      simpa only using hgi.comp_measurePreserving
        (Homogenization.measurePreserving_addRight_restrict_translateSet z U)
    have hgHilbert : MemLp (fun y => Homogenization.HilbertVec.ofVec (gQ y)) 2
        (volume.restrict U) := by
      rw [MeasureTheory.memLp_piLp_iff]
      intro i
      simpa only [gQ, Homogenization.HilbertVec.ofVec, PiLp.toLp_apply] using hgCoord i
    have hgsHilbert : MemLp
        (fun y => Homogenization.HilbertVec.ofVec (gs y)) 2 (volume.restrict U) := by
      simpa [gs, gQ, Homogenization.hilbertifyVecField] using hgHilbert.neg
    have hLp : MemLp (fun y => Homogenization.HilbertVec.ofVec (gs y)) 2
        (Homogenization.normalizedCubeMeasure Q) := by
      simpa only [Homogenization.normalizedCubeMeasure, Homogenization.cubeMeasure,
        Homogenization.volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using
          hgsHilbert.smul_measure ENNReal.ofReal_ne_top
    have hfracNeg : SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn U s gs ≠ ⊤ := by
      have hEqNeg : SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn U s gs =
          SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn U s gQ := by
        unfold SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn
        congr 1
        congr 1
        funext q
        unfold SubdiffusiveProcess.CoarseGrainingVocab.fractionalKernel
        have hvec : (fun i => -gQ q.1 i) - (fun i => -gQ q.2 i) =
            -(gQ q.1 - gQ q.2) := by
          funext i
          change -gQ q.1 i - -gQ q.2 i = -(gQ q.1 i - gQ q.2 i)
          ring
        rw [hvec, Homogenization.euclideanNorm_neg]
      rw [hEqNeg]
      exact hfracQ
    have hsemi : Homogenization.cubeEuclideanWspESeminorm Q sOrder
        Homogenization.FiniteLpExponent.two gs < ⊤ := by
      have hEq :=
        SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.fractionalSeminormOn_openCubeSet_eq_sqrt_mul_cubeEuclideanWspESeminorm
          Q sOrder gs
      have hcoef : (ENNReal.ofReal sOrder.1) ^ (1 / 2 : ℝ) ≠ 0 := by
        exact ne_of_gt (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hs.1)
          ENNReal.ofReal_ne_top)
      have hne : Homogenization.cubeEuclideanWspESeminorm Q sOrder
          Homogenization.FiniteLpExponent.two gs ≠ ⊤ := by
        intro htop
        apply hfracNeg
        rw [hEq, htop]
        exact ENNReal.mul_top hcoef
      exact lt_top_iff_ne_top.mpr hne
    exact ⟨hLp,
      Homogenization.memCubeEuclideanWsp_of_memLp_of_eSeminorm_lt_top hLp hsemi⟩
  let sol : Homogenization.Book.Ch03.DirichletForcedCubeSolution Q A gs :=
    { toH1 := vQ
      boundaryData := hQ
      weakSolution := hforce
      zeroTraceDifference := ⟨rhoQ, hzeroQ⟩ }
  refine ⟨hFull, ⟨sol, ?_, ?_, ?_⟩⟩
  · funext y i
    change (Homogenization.H1Function.untranslate z hT).grad y i =
      ((sobolevGradient (hDatum : SobolevData Ω) i : DomainL2 Ω) :
        SpatialCoordinates d → ℝ) (y + z)
    rw [Homogenization.H1Function.untranslate_grad]
    rw [aux_inputs_extension_transport_h1_cast_grad hdom hNative]
    have hpoint : hNative.grad (y + z) i =
        ((hDatum : SobolevData Ω).2 i : SpatialCoordinates d → ℝ) (y + z) :=
      congrFun (congrFun hNativeGrad (y + z)) i
    simpa [SubdiffusiveProcess.sobolevGradient] using hpoint
  · funext y i
    change (Homogenization.H1Function.untranslate z vT).grad y i =
      ((sobolevGradient (v : SobolevData Ω) i : DomainL2 Ω) :
        SpatialCoordinates d → ℝ) (y + z)
    rw [Homogenization.H1Function.untranslate_grad]
    rw [aux_inputs_extension_transport_h1_cast_grad hdom vNative]
    have hpoint : vNative.grad (y + z) i =
        ((v : SobolevData Ω).2 i : SpatialCoordinates d → ℝ) (y + z) :=
      congrFun (congrFun vNativeGrad (y + z)) i
    simpa [SubdiffusiveProcess.sobolevGradient] using hpoint
  · have hEnergy :
        normalizedEnergyNorm a Ω.isOpen.measurableSet
          (sobolevGradient (v : SobolevData Ω)) ≤
          Homogenization.Book.Ch03.dirichletForcedSolutionEnergyNorm Q A sol := by
      rw [normalizedEnergyNorm,
        Homogenization.Book.Ch03.dirichletForcedSolutionEnergyNorm,
        Homogenization.Book.Ch03.h1EnergyNormOnCube]
      apply Real.sqrt_le_sqrt
      have henergyValue :
          SubdiffusiveProcess.localGradientEnergy a Ω.isOpen.measurableSet
              (sobolevGradient (v : SobolevData Ω)) / volume.real (Ω : Set (SpatialCoordinates d)) =
            Homogenization.Book.Ch03.localizedCoeffEnergyValue U (A.coeffOn Q) vQ := by
        have hgrad (y : Homogenization.Vec d) (i : Fin d) :
            vQ.grad y i =
              ((sobolevGradient (v : SobolevData Ω) i : DomainL2 Ω) :
                SpatialCoordinates d → ℝ) (y + z) := by
          change (Homogenization.H1Function.untranslate z vT).grad y i = _
          rw [Homogenization.H1Function.untranslate_grad]
          rw [aux_inputs_extension_transport_h1_cast_grad hdom vNative]
          have hpoint : vNative.grad (y + z) i =
              ((v : SobolevData Ω).2 i : DomainL2 Ω) (y + z) :=
            congrFun (congrFun vNativeGrad (y + z)) i
          simpa [SubdiffusiveProcess.sobolevGradient] using hpoint
        have hvNativeGrad (x : SpatialCoordinates d) (i : Fin d) :
            vNative.grad x i =
              ((sobolevGradient (v : SobolevData Ω) i : DomainL2 Ω) :
                SpatialCoordinates d → ℝ) x := by
          have hpoint : vNative.grad x i =
              ((v : SobolevData Ω).2 i : DomainL2 Ω) x :=
            congrFun (congrFun vNativeGrad x) i
          simpa [SubdiffusiveProcess.sobolevGradient] using hpoint
        have hMeasure : volume.restrict (Ω : Set (SpatialCoordinates d)) =
            volume.restrict (Homogenization.translateSet z U) :=
          congrArg (fun S : Set (SpatialCoordinates d) => volume.restrict S) hdom
        have hvolume : volume (Ω : Set (SpatialCoordinates d)) = volume U := by
          calc
            volume (Ω : Set (SpatialCoordinates d)) =
                volume (Homogenization.translateSet z U) := congrArg volume hdom
            _ = volume U := Homogenization.volume_translateSet_eq z U
        have hvolumeReal : volume.real (Ω : Set (SpatialCoordinates d)) =
            (volume U).toReal := congrArg ENNReal.toReal hvolume
        have hIntU (i : Fin d) : IntegrableOn
            (fun y : Homogenization.Vec d =>
              a.val (y + z) * (vQ.grad y i) ^ 2) U volume := by
          have hIntOmega : Integrable
              (fun x : SpatialCoordinates d =>
                a.val x * (vNative.grad x i * vNative.grad x i))
              (volume.restrict (Ω : Set (SpatialCoordinates d))) :=
            hHint vNative i
          have hIntTranslated : Integrable
              (fun x : SpatialCoordinates d =>
                a.val x * (vNative.grad x i * vNative.grad x i))
              (volume.restrict (Homogenization.translateSet z U)) := by
            rw [← hMeasure]
            exact hIntOmega
          have hIntComp : Integrable
              (fun y : Homogenization.Vec d => a.val (y + z) *
                (vNative.grad (y + z) i * vNative.grad (y + z) i))
              (volume.restrict U) := by
            simpa only [Function.comp_def] using
              MeasurePreserving.integrable_comp_of_integrable
                (Homogenization.measurePreserving_addRight_restrict_translateSet z U)
                hIntTranslated
          change Integrable _ (volume.restrict U)
          refine hIntComp.congr ?_
          filter_upwards [] with y
          rw [hvNativeGrad (y + z) i, hgrad y i]
          simp [pow_two]
        have htrans (i : Fin d) :
            (∫ x in (Ω : Set (SpatialCoordinates d)),
              a.val x * (((sobolevGradient (v : SobolevData Ω) i : DomainL2 Ω) :
                SpatialCoordinates d → ℝ) x) ^ 2 ∂volume) =
            ∫ y in U, a.val (y + z) * (vQ.grad y i) ^ 2 ∂volume := by
          let f : SpatialCoordinates d → ℝ := fun x =>
            a.val x * (((sobolevGradient (v : SobolevData Ω) i : DomainL2 Ω) :
              SpatialCoordinates d → ℝ) x) ^ 2
          calc
            ∫ x in (Ω : Set (SpatialCoordinates d)), f x ∂volume =
                ∫ x in Homogenization.translateSet z U, f x ∂volume :=
              congrArg (fun S : Set (SpatialCoordinates d) => ∫ x in S, f x ∂volume) hdom
            _ = ∫ y in U, a.val (y + z) *
                (((sobolevGradient (v : SobolevData Ω) i : DomainL2 Ω) :
                  SpatialCoordinates d → ℝ) (y + z)) ^ 2 ∂volume := by
              symm
              exact Homogenization.setIntegral_comp_addRight_translateSet z U f
            _ = ∫ y in U, a.val (y + z) * (vQ.grad y i) ^ 2 ∂volume := by
              apply integral_congr_ae
              filter_upwards [] with y
              rw [hgrad y i]
        have hlocal :
            SubdiffusiveProcess.localGradientEnergy a Ω.isOpen.measurableSet
                (sobolevGradient (v : SobolevData Ω)) =
              ∑ i : Fin d, ∫ y in U,
                a.val (y + z) * (vQ.grad y i) ^ 2 ∂volume := by
          rw [SubdiffusiveProcess.localGradientEnergy_eq_integral]
          simp only [Measure.restrict_restrict Ω.isOpen.measurableSet]
          simp only [Ω, Set.inter_self]
          apply Finset.sum_congr rfl
          intro i hi
          exact htrans i
        have hchart := aux_inputs_extension_transport_chart m z hr a Jc
        have henergyDensity :
            Homogenization.coefficientEnergyDensity (A.coeffOn Q).toCoeffField vQ.grad =ᵐ[
              volume.restrict U] fun y =>
                ∑ i : Fin d, a.val (y + z) * (vQ.grad y i) ^ 2 := by
          filter_upwards [hchart] with y hy
          have hArg : (fun j => y j + z j) = y + z := by
            funext j
            rfl
          rw [hArg] at hy
          change Homogenization.vecDot (vQ.grad y)
              (Homogenization.matVecMul
                (Homogenization.symmPart ((A.coeffOn Q).toCoeffField y))
                (vQ.grad y)) = _
          rw [hy, Homogenization.Book.Ch02.symmPart_scalarMatrix,
            Homogenization.matVecMul_scalarMatrix,
            Homogenization.vecDot_smul_right]
          simp [Homogenization.vecDot, pow_two, Finset.mul_sum,
            mul_comm, mul_left_comm, mul_assoc]
        have hsumDensity :
            (∑ i : Fin d, ∫ y in U,
              a.val (y + z) * (vQ.grad y i) ^ 2 ∂volume) =
              ∫ y in U,
                Homogenization.coefficientEnergyDensity
                  (A.coeffOn Q).toCoeffField vQ.grad y ∂volume := by
          rw [← integral_finset_sum Finset.univ (fun i _ => hIntU i)]
          apply integral_congr_ae
          exact henergyDensity.symm
        calc
          _ = (volume U).toReal⁻¹ *
              ∫ y in U, Homogenization.coefficientEnergyDensity
                (A.coeffOn Q).toCoeffField vQ.grad y ∂volume := by
            rw [hlocal, hvolumeReal]
            rw [hsumDensity]
            ring
          _ = Homogenization.Book.Ch03.localizedCoeffEnergyValue
              U (A.coeffOn Q) vQ := by
            rw [Homogenization.Book.Ch03.localizedCoeffEnergyValue_eq_volumeAverage_coefficientEnergyDensity]
            unfold Homogenization.volumeAverage
            rfl
      rw [henergyValue]
    exact hEnergy

end Paper

