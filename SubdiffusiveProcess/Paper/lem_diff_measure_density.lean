import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Geometry.Cube
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology

namespace Paper
noncomputable section

theorem aux_lem_diff_measure_density_quadratic_cross_bound
    {a b r : ℝ} (h : ∀ t : ℝ, 0 ≤ b * (t * t) + 2 * r * t + a) :
    0 ≤ a ∧ 0 ≤ b ∧ |r| ≤ Real.sqrt (a * b) := by
  have ha : 0 ≤ a := by simpa using h 0
  have hd : r ^ 2 ≤ a * b := by
    have hd' := discrim_le_zero (a := b) (b := 2 * r) (c := a) (by
      intro t
      simpa [mul_assoc, mul_left_comm, mul_comm] using h t)
    simp only [discrim, sq] at hd'
    nlinarith
  have hb : 0 ≤ b := by
    by_contra hb
    have hb' : b < 0 := lt_of_not_ge hb
    by_cases ha0 : a = 0
    · have := h 1
      rw [ha0] at this
      nlinarith
    · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      nlinarith [sq_nonneg r]
  have hs : (Real.sqrt (a * b)) ^ 2 = a * b :=
    Real.sq_sqrt (mul_nonneg ha hb)
  have hrs : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg _
  refine ⟨ha, hb, ?_⟩
  nlinarith [sq_abs r]

theorem aux_lem_diff_measure_density_quadratic_cross_bound_rat
    {a b r : ℝ} (h : ∀ t : ℚ, 0 ≤ b * ((t : ℝ) * (t : ℝ)) +
      2 * r * (t : ℝ) + a) :
    0 ≤ a ∧ 0 ≤ b ∧ |r| ≤ Real.sqrt (a * b) := by
  apply aux_lem_diff_measure_density_quadratic_cross_bound
  intro t
  by_contra ht
  have ht' : b * (t * t) + 2 * r * t + a < 0 := lt_of_not_ge ht
  let U : Set ℝ := {s | b * (s * s) + 2 * r * s + a < 0}
  have hUopen : IsOpen U := by
    dsimp [U]
    exact isOpen_lt (by fun_prop) continuous_const
  have htU : t ∈ U := ht'
  obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open hUopen ⟨t, htU⟩
  exact (not_lt_of_ge (h q)) hq

theorem aux_lem_diff_measure_density_energy_measure_quad
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} {E : DirichletForm.ClosedForm m}
    (Gamma : DirichletForm.EnergyMeasure E)
    {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (t : ℝ) {A : Set X} (hA : MeasurableSet A) :
    (Gamma.measure (u + t • v) A).toReal =
      (Gamma.measure u A).toReal + 2 * t * Gamma.cross u v A +
        t ^ 2 * (Gamma.measure v A).toReal := by
  have htv : t • v ∈ E.domain := E.domain.smul_mem t hv
  have huv : u + t • v ∈ E.domain := E.domain.add_mem hu htv
  rw [← Gamma.cross_self (u + t • v) huv A hA,
    Gamma.cross_add_self_apply hu htv A,
    Gamma.cross_self u hu A hA,
    Gamma.cross_smul_right t u hu v hv,
    VectorMeasure.smul_apply,
    Gamma.cross_smul_left t hv htv,
    Gamma.cross_smul_right t v hv v hv,
    VectorMeasure.smul_apply, VectorMeasure.smul_apply,
    Gamma.cross_self v hv A hA]
  simp only [smul_eq_mul]
  ring

theorem aux_lem_diff_measure_density_convex_coeff_sum {m M c : ℝ} (h : M - m ≠ 0) :
    (M - c) / (M - m) + (c - m) / (M - m) = 1 := by
  rw [← add_div]
  rw [show M - c + (c - m) = M - m by ring, div_self h]

theorem aux_lem_diff_measure_density_cross_interpolation
    {m M c q p : ℝ} (h : M - m ≠ 0) :
    q - c * p = (M - c) / (M - m) * (q - m * p) -
      (c - m) / (M - m) * (M * p - q) := by
  field_simp [h]
  ring



theorem lem_diff_measure_density
    (d : ℕ) (hd : 2 ≤ d)
    (zQ : SpatialCoordinates d) (rQ : ℝ) (hrQ : 0 < rQ) :
    let Q : Opens (SpatialCoordinates d) := centeredCube zQ rQ hrQ
    ∀ (E F : DirichletForm.ClosedForm
        (volume.restrict (Q : Set (SpatialCoordinates d))))
      (GammaE : DirichletForm.EnergyMeasure E)
      (GammaF : DirichletForm.EnergyMeasure F)
      (hdom : E.domain = F.domain)
      (m M c : ℝ) (hm : 0 < m) (hmc : m ≤ c) (hcM : c ≤ M)
      (horder : ∀ h ∈ E.domain, ∀ A : Set (SpatialCoordinates d),
        MeasurableSet A →
          m * (GammaE.measure h A).toReal ≤ (GammaF.measure h A).toReal ∧
            (GammaF.measure h A).toReal ≤ M * (GammaE.measure h A).toReal)
      (u v : DomainL2 Q) (hu : u ∈ E.domain) (hv : v ∈ E.domain),
    let sigma := GammaE.measure u + GammaE.measure v
    ∃ (eU eV dUV : SpatialCoordinates d → ℝ),
      Integrable eU sigma ∧ Integrable eV sigma ∧ Integrable dUV sigma ∧
      (∀ᵐ x ∂sigma, 0 ≤ eU x ∧ 0 ≤ eV x) ∧
      GammaE.measure u = sigma.withDensity (fun x => ENNReal.ofReal (eU x)) ∧
      GammaE.measure v = sigma.withDensity (fun x => ENNReal.ofReal (eV x)) ∧
      GammaF.cross u v - c • GammaE.cross u v = sigma.withDensityᵥ dUV ∧
      (∀ᵐ x ∂sigma, |dUV x| ≤ (M - m) * Real.sqrt (eU x * eV x)) := by
  dsimp
  intro E F GammaE GammaF hdom m M c hm hmc hcM horder u v hu hv
  classical
  let μ : Measure (SpatialCoordinates d) := GammaE.measure u
  let ν : Measure (SpatialCoordinates d) := GammaE.measure v
  let sigma : Measure (SpatialCoordinates d) := μ + ν
  change ∃ (eU eV dUV : SpatialCoordinates d → ℝ),
    Integrable eU sigma ∧ Integrable eV sigma ∧ Integrable dUV sigma ∧
      (∀ᵐ x ∂sigma, 0 ≤ eU x ∧ 0 ≤ eV x) ∧
      μ = sigma.withDensity (fun x => ENNReal.ofReal (eU x)) ∧
      ν = sigma.withDensity (fun x => ENNReal.ofReal (eV x)) ∧
      GammaF.cross u v - c • GammaE.cross u v = sigma.withDensityᵥ dUV ∧
      (∀ᵐ x ∂sigma, |dUV x| ≤ (M - m) * Real.sqrt (eU x * eV x))
  letI : IsFiniteMeasure μ := ⟨by
    simpa [μ] using GammaE.measure_univ_lt_top u hu⟩
  letI : IsFiniteMeasure ν := ⟨by
    simpa [ν] using GammaE.measure_univ_lt_top v hv⟩
  letI : IsFiniteMeasure sigma := by
    dsimp [sigma]
    infer_instance
  have hμsigma : μ ≪ sigma := by
    exact Measure.AbsolutelyContinuous.rfl.add_right ν
  have hνsigma : ν ≪ sigma := by
    simpa [sigma, add_comm] using
      (Measure.AbsolutelyContinuous.rfl.add_right μ : ν ≪ ν + μ)
  have huF : u ∈ F.domain := hdom ▸ hu
  have hvF : v ∈ F.domain := hdom ▸ hv
  have hFzero : ∀ {w : DomainL2 (centeredCube zQ rQ hrQ)}, w ∈ E.domain →
      ∀ {A : Set (SpatialCoordinates d)}, MeasurableSet A →
        GammaE.measure w A = 0 → GammaF.measure w A = 0 := by
    intro w hw A hA hzero
    have hupper := (horder w hw A hA).2
    have hto : (GammaF.measure w A).toReal = 0 := by
      have hle : (GammaF.measure w A).toReal ≤ 0 := by
        simpa [hzero] using hupper
      exact le_antisymm hle (ENNReal.toReal_nonneg)
    rcases (ENNReal.toReal_eq_zero_iff _).mp hto with hzero' | htop
    · exact hzero'
    · exact False.elim ((GammaF.measure_ne_top (hdom ▸ hw) A) htop)
  have hcrossEac : GammaE.cross u v ≪ᵥ sigma.toENNRealVectorMeasure := by
    refine VectorMeasure.AbsolutelyContinuous.mk ?_
    intro A hA hsig
    have hsig' : sigma A = 0 := by
      simpa only [Measure.toENNRealVectorMeasure_apply_measurable hA] using hsig
    have hsum : μ A + ν A = 0 := by
      simpa [sigma, Measure.add_apply] using hsig'
    have hμA : μ A = 0 := (add_eq_zero.mp hsum).1
    have hνA : ν A = 0 := (add_eq_zero.mp hsum).2
    have hcs := GammaE.abs_cross_le u hu v hv A hA
    have hz : |GammaE.cross u v A| ≤ 0 := by
      simpa [μ, ν, hμA, hνA] using hcs
    exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))
  have hcrossFac : GammaF.cross u v ≪ᵥ sigma.toENNRealVectorMeasure := by
    refine VectorMeasure.AbsolutelyContinuous.mk ?_
    intro A hA hsig
    have hsig' : sigma A = 0 := by
      simpa only [Measure.toENNRealVectorMeasure_apply_measurable hA] using hsig
    have hsum : μ A + ν A = 0 := by
      simpa [sigma, Measure.add_apply] using hsig'
    have hμA : μ A = 0 := (add_eq_zero.mp hsum).1
    have hνA : ν A = 0 := (add_eq_zero.mp hsum).2
    have hμFA : GammaF.measure u A = 0 := hFzero hu hA (by simpa [μ] using hμA)
    have hνFA : GammaF.measure v A = 0 := hFzero hv hA (by simpa [ν] using hνA)
    have hcs := GammaF.abs_cross_le u huF v hvF A hA
    have hz : |GammaF.cross u v A| ≤ 0 := by
      simpa [hμFA, hνFA] using hcs
    exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))
  let eU : SpatialCoordinates d → ℝ := fun x => (μ.rnDeriv sigma x).toReal
  let eV : SpatialCoordinates d → ℝ := fun x => (ν.rnDeriv sigma x).toReal
  have heUInt : Integrable eU sigma := by
    dsimp [eU]
    exact integrable_toReal_of_lintegral_ne_top
      (Measure.measurable_rnDeriv μ sigma).aemeasurable
      (Measure.lintegral_rnDeriv_lt_top μ sigma).ne
  have heVInt : Integrable eV sigma := by
    dsimp [eV]
    exact integrable_toReal_of_lintegral_ne_top
      (Measure.measurable_rnDeriv ν sigma).aemeasurable
      (Measure.lintegral_rnDeriv_lt_top ν sigma).ne
  have heUeq : μ = sigma.withDensity (fun x => ENNReal.ofReal (eU x)) := by
    calc
      μ = sigma.withDensity (μ.rnDeriv sigma) :=
        (Measure.withDensity_rnDeriv_eq μ sigma hμsigma).symm
      _ = sigma.withDensity (fun x => ENNReal.ofReal (eU x)) := by
        apply withDensity_congr_ae
        filter_upwards [Measure.rnDeriv_ne_top μ sigma] with x hx
        exact (ENNReal.ofReal_toReal hx).symm
  have heVeq : ν = sigma.withDensity (fun x => ENNReal.ofReal (eV x)) := by
    calc
      ν = sigma.withDensity (ν.rnDeriv sigma) :=
        (Measure.withDensity_rnDeriv_eq ν sigma hνsigma).symm
      _ = sigma.withDensity (fun x => ENNReal.ofReal (eV x)) := by
        apply withDensity_congr_ae
        filter_upwards [Measure.rnDeriv_ne_top ν sigma] with x hx
        exact (ENNReal.ofReal_toReal hx).symm
  let p : SpatialCoordinates d → ℝ := (GammaE.cross u v).rnDeriv sigma
  let q : SpatialCoordinates d → ℝ := (GammaF.cross u v).rnDeriv sigma
  have hpInt : Integrable p sigma := by
    exact SignedMeasure.integrable_rnDeriv _ _
  have hqInt : Integrable q sigma := by
    exact SignedMeasure.integrable_rnDeriv _ _
  have hpeq : sigma.withDensityᵥ p = GammaE.cross u v := by
    exact SignedMeasure.withDensityᵥ_rnDeriv_eq _ sigma hcrossEac
  have hqeq : sigma.withDensityᵥ q = GammaF.cross u v := by
    exact SignedMeasure.withDensityᵥ_rnDeriv_eq _ sigma hcrossFac
  let D : SignedMeasure (SpatialCoordinates d) :=
    GammaF.cross u v - c • GammaE.cross u v
  have hDac : D ≪ᵥ sigma.toENNRealVectorMeasure := by
    refine VectorMeasure.AbsolutelyContinuous.mk ?_
    intro A hA hsig
    have hsig' : sigma A = 0 := by
      simpa only [Measure.toENNRealVectorMeasure_apply_measurable hA] using hsig
    have hsum : μ A + ν A = 0 := by
      simpa [sigma, Measure.add_apply] using hsig'
    have hμA : μ A = 0 := (add_eq_zero.mp hsum).1
    have hνA : ν A = 0 := (add_eq_zero.mp hsum).2
    have hEA : GammaE.cross u v A = 0 := by
      have hcs := GammaE.abs_cross_le u hu v hv A hA
      have hz : |GammaE.cross u v A| ≤ 0 := by
        simpa [μ, ν, hμA, hνA] using hcs
      exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))
    have hFA : GammaF.cross u v A = 0 := by
      have hμFA : GammaF.measure u A = 0 := hFzero hu hA (by simpa [μ] using hμA)
      have hνFA : GammaF.measure v A = 0 := hFzero hv hA (by simpa [ν] using hνA)
      have hcs := GammaF.abs_cross_le u huF v hvF A hA
      have hz : |GammaF.cross u v A| ≤ 0 := by
        simpa [hμFA, hνFA] using hcs
      exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))
    simp [D, VectorMeasure.sub_apply, VectorMeasure.smul_apply, hEA, hFA]
  let dUV : SpatialCoordinates d → ℝ := D.rnDeriv sigma
  have hdUVInt : Integrable dUV sigma := by
    exact SignedMeasure.integrable_rnDeriv _ _
  have hDeq : D = sigma.withDensityᵥ dUV := by
    symm
    exact SignedMeasure.withDensityᵥ_rnDeriv_eq _ sigma hDac
  have hαsigma : GammaF.measure u ≪ sigma := by
    refine Measure.AbsolutelyContinuous.mk ?_
    intro A hA hsig
    have hsig' : sigma A = 0 := by
      simpa only [Measure.toENNRealVectorMeasure_apply_measurable hA] using hsig
    have hsum : μ A + ν A = 0 := by
      simpa [sigma, Measure.add_apply] using hsig'
    have hμA : μ A = 0 := (add_eq_zero.mp hsum).1
    exact hFzero hu hA (by simpa [μ] using hμA)
  have hβsigma : GammaF.measure v ≪ sigma := by
    refine Measure.AbsolutelyContinuous.mk ?_
    intro A hA hsig
    have hsig' : sigma A = 0 := by
      simpa only [Measure.toENNRealVectorMeasure_apply_measurable hA] using hsig
    have hsum : μ A + ν A = 0 := by
      simpa [sigma, Measure.add_apply] using hsig'
    have hνA : ν A = 0 := (add_eq_zero.mp hsum).2
    exact hFzero hv hA (by simpa [ν] using hνA)
  letI : IsFiniteMeasure (GammaF.measure u) := ⟨GammaF.measure_univ_lt_top u huF⟩
  letI : IsFiniteMeasure (GammaF.measure v) := ⟨GammaF.measure_univ_lt_top v hvF⟩
  let α : Measure (SpatialCoordinates d) := GammaF.measure u
  let β : Measure (SpatialCoordinates d) := GammaF.measure v
  letI : IsFiniteMeasure α := by
    dsimp [α]
    infer_instance
  letI : IsFiniteMeasure β := by
    dsimp [β]
    infer_instance
  let a : SpatialCoordinates d → ℝ := fun x => (α.rnDeriv sigma x).toReal
  let b : SpatialCoordinates d → ℝ := fun x => (β.rnDeriv sigma x).toReal
  have haInt : Integrable a sigma := by
    dsimp [a]
    exact integrable_toReal_of_lintegral_ne_top
      (Measure.measurable_rnDeriv α sigma).aemeasurable
      (Measure.lintegral_rnDeriv_lt_top α sigma).ne
  have hbInt : Integrable b sigma := by
    dsimp [b]
    exact integrable_toReal_of_lintegral_ne_top
      (Measure.measurable_rnDeriv β sigma).aemeasurable
      (Measure.lintegral_rnDeriv_lt_top β sigma).ne
  have heU_set : ∀ (A : Set (SpatialCoordinates d)), MeasurableSet A →
      (∫ x in A, eU x ∂sigma) = (μ A).toReal := by
    intro A hA
    simpa [eU, Measure.real] using Measure.setIntegral_toReal_rnDeriv hμsigma A
  have heV_set : ∀ (A : Set (SpatialCoordinates d)), MeasurableSet A →
      (∫ x in A, eV x ∂sigma) = (ν A).toReal := by
    intro A hA
    simpa [eV, Measure.real] using Measure.setIntegral_toReal_rnDeriv hνsigma A
  have ha_set : ∀ (A : Set (SpatialCoordinates d)), MeasurableSet A →
      (∫ x in A, a x ∂sigma) = (GammaF.measure u A).toReal := by
    intro A hA
    simpa [a, α, Measure.real] using Measure.setIntegral_toReal_rnDeriv
      hαsigma A
  have hb_set : ∀ (A : Set (SpatialCoordinates d)), MeasurableSet A →
      (∫ x in A, b x ∂sigma) = (GammaF.measure v A).toReal := by
    intro A hA
    simpa [b, β, Measure.real] using Measure.setIntegral_toReal_rnDeriv
      hβsigma A
  have hp_set : ∀ (A : Set (SpatialCoordinates d)), MeasurableSet A →
      (∫ x in A, p x ∂sigma) = GammaE.cross u v A := by
    intro A hA
    rw [← hpeq, withDensityᵥ_apply hpInt hA]
  have hq_set : ∀ (A : Set (SpatialCoordinates d)), MeasurableSet A →
      (∫ x in A, q x ∂sigma) = GammaF.cross u v A := by
    intro A hA
    rw [← hqeq, withDensityᵥ_apply hqInt hA]
  have hEpolyInt : ∀ t : ℝ,
      Integrable (fun x => eU x + 2 * t * p x + t ^ 2 * eV x) sigma := by
    intro t
    exact (heUInt.add (hpInt.const_mul (2 * t))).add (heVInt.const_mul (t ^ 2))
  have hFpolyInt : ∀ t : ℝ,
      Integrable (fun x => a x + 2 * t * q x + t ^ 2 * b x) sigma := by
    intro t
    exact (haInt.add (hqInt.const_mul (2 * t))).add (hbInt.const_mul (t ^ 2))
  have hEpoly_set : ∀ (t : ℝ) (A : Set (SpatialCoordinates d)), MeasurableSet A →
      (∫ x in A, eU x + 2 * t * p x + t ^ 2 * eV x ∂sigma) =
        (GammaE.measure (u + t • v) A).toReal := by
    intro t A hA
    calc
      (∫ x in A, eU x + 2 * t * p x + t ^ 2 * eV x ∂sigma) =
          (∫ x in A, eU x ∂sigma) +
              (∫ x in A, 2 * t * p x ∂sigma) +
              (∫ x in A, t ^ 2 * eV x ∂sigma) := by
        calc
          _ = (∫ x in A,
              ((eU + fun x => 2 * t * p x) + fun x => t ^ 2 * eV x) x ∂sigma) := by
            simp only [Pi.add_apply]
          _ = (∫ x in A, (eU + fun x => 2 * t * p x) x ∂sigma) +
              (∫ x in A, (fun x => t ^ 2 * eV x) x ∂sigma) := by
            exact integral_add' (μ := sigma.restrict A)
              ((heUInt.add (hpInt.const_mul (2 * t))).integrableOn)
              (heVInt.const_mul (t ^ 2)).integrableOn
          _ = _ := by
            rw [integral_add' (μ := sigma.restrict A) heUInt.integrableOn
              (hpInt.const_mul (2 * t)).integrableOn]
      _ = (μ A).toReal + 2 * t * GammaE.cross u v A +
            t ^ 2 * (ν A).toReal := by
        rw [integral_const_mul, integral_const_mul, heU_set A hA, hp_set A hA,
          heV_set A hA]
      _ = (GammaE.measure (u + t • v) A).toReal := by
        rw [aux_lem_diff_measure_density_energy_measure_quad GammaE hu hv t hA]
  have hFpoly_set : ∀ (t : ℝ) (A : Set (SpatialCoordinates d)), MeasurableSet A →
      (∫ x in A, a x + 2 * t * q x + t ^ 2 * b x ∂sigma) =
        (GammaF.measure (u + t • v) A).toReal := by
    intro t A hA
    have htvF : t • v ∈ F.domain := F.domain.smul_mem t hvF
    calc
      (∫ x in A, a x + 2 * t * q x + t ^ 2 * b x ∂sigma) =
          (∫ x in A, a x ∂sigma) +
              (∫ x in A, 2 * t * q x ∂sigma) +
              (∫ x in A, t ^ 2 * b x ∂sigma) := by
        calc
          _ = (∫ x in A,
              ((a + fun x => 2 * t * q x) + fun x => t ^ 2 * b x) x ∂sigma) := by
            simp only [Pi.add_apply]
          _ = (∫ x in A, (a + fun x => 2 * t * q x) x ∂sigma) +
              (∫ x in A, (fun x => t ^ 2 * b x) x ∂sigma) := by
            exact integral_add' (μ := sigma.restrict A)
              ((haInt.add (hqInt.const_mul (2 * t))).integrableOn)
              (hbInt.const_mul (t ^ 2)).integrableOn
          _ = _ := by
            rw [integral_add' (μ := sigma.restrict A) haInt.integrableOn
              (hqInt.const_mul (2 * t)).integrableOn]
      _ = (GammaF.measure u A).toReal + 2 * t * GammaF.cross u v A +
            t ^ 2 * (GammaF.measure v A).toReal := by
        rw [integral_const_mul, integral_const_mul, ha_set A hA, hq_set A hA,
          hb_set A hA]
      _ = (GammaF.measure (u + t • v) A).toReal := by
        rw [aux_lem_diff_measure_density_energy_measure_quad GammaF huF hvF t hA]
  have hLower : ∀ t : ℝ, ∀ᵐ x ∂sigma,
      0 ≤ (a x + 2 * t * q x + t ^ 2 * b x) -
        m * (eU x + 2 * t * p x + t ^ 2 * eV x) := by
    intro t
    apply ae_nonneg_of_forall_setIntegral_nonneg
      ((hFpolyInt t).sub ((hEpolyInt t).const_mul m))
    intro A hA hAtop
    rw [integral_sub' (hFpolyInt t).integrableOn ((hEpolyInt t).const_mul m).integrableOn,
      integral_const_mul, hFpoly_set t A hA, hEpoly_set t A hA]
    exact sub_nonneg.mpr (horder (u + t • v)
      (E.domain.add_mem hu (E.domain.smul_mem t hv)) A hA).1
  have hUpper : ∀ t : ℝ, ∀ᵐ x ∂sigma,
      0 ≤ M * (eU x + 2 * t * p x + t ^ 2 * eV x) -
        (a x + 2 * t * q x + t ^ 2 * b x) := by
    intro t
    apply ae_nonneg_of_forall_setIntegral_nonneg
      (((hEpolyInt t).const_mul M).sub (hFpolyInt t))
    intro A hA hAtop
    rw [integral_sub' ((hEpolyInt t).const_mul M).integrableOn (hFpolyInt t).integrableOn,
      integral_const_mul, hEpoly_set t A hA, hFpoly_set t A hA]
    exact sub_nonneg.mpr (horder (u + t • v)
      (E.domain.add_mem hu (E.domain.smul_mem t hv)) A hA).2
  have hLowerRat : ∀ᵐ x ∂sigma, ∀ t : ℚ,
      0 ≤ (a x + 2 * (t : ℝ) * q x + (t : ℝ) ^ 2 * b x) -
        m * (eU x + 2 * (t : ℝ) * p x + (t : ℝ) ^ 2 * eV x) := by
    rw [ae_all_iff]
    intro t
    exact hLower (t : ℝ)
  have hUpperRat : ∀ᵐ x ∂sigma, ∀ t : ℚ,
      0 ≤ M * (eU x + 2 * (t : ℝ) * p x + (t : ℝ) ^ 2 * eV x) -
        (a x + 2 * (t : ℝ) * q x + (t : ℝ) ^ 2 * b x) := by
    rw [ae_all_iff]
    intro t
    exact hUpper (t : ℝ)
  have heU_nonneg : ∀ᵐ x ∂sigma, 0 ≤ eU x := by
    filter_upwards [] with x
    exact ENNReal.toReal_nonneg
  have heV_nonneg : ∀ᵐ x ∂sigma, 0 ≤ eV x := by
    filter_upwards [] with x
    exact ENNReal.toReal_nonneg
  have hquadLower : ∀ᵐ x ∂sigma, ∀ t : ℚ,
      0 ≤ (b x - m * eV x) * ((t : ℝ) * (t : ℝ)) +
        2 * (q x - m * p x) * (t : ℝ) + (a x - m * eU x) := by
    filter_upwards [hLowerRat] with x hx
    intro t
    nlinarith [hx t]
  have hquadUpper : ∀ᵐ x ∂sigma, ∀ t : ℚ,
      0 ≤ (M * eV x - b x) * ((t : ℝ) * (t : ℝ)) +
        2 * (M * p x - q x) * (t : ℝ) + (M * eU x - a x) := by
    filter_upwards [hUpperRat] with x hx
    intro t
    nlinarith [hx t]
  have hmatrix : ∀ᵐ x ∂sigma,
      0 ≤ a x - m * eU x ∧ 0 ≤ b x - m * eV x ∧
        |q x - m * p x| ≤ Real.sqrt ((a x - m * eU x) * (b x - m * eV x)) ∧
        0 ≤ M * eU x - a x ∧ 0 ≤ M * eV x - b x ∧
        |M * p x - q x| ≤ Real.sqrt ((M * eU x - a x) * (M * eV x - b x)) := by
    filter_upwards [hquadLower, hquadUpper] with x hxL hxU
    have hL := aux_lem_diff_measure_density_quadratic_cross_bound_rat
      (a := a x - m * eU x) (b := b x - m * eV x) (r := q x - m * p x) (by
        intro t
        exact hxL t)
    have hU := aux_lem_diff_measure_density_quadratic_cross_bound_rat
      (a := M * eU x - a x) (b := M * eV x - b x) (r := M * p x - q x) (by
        intro t
        exact hxU t)
    exact ⟨hL.1, hL.2.1, hL.2.2, hU.1, hU.2.1, hU.2.2⟩
  have hDdensity : sigma.withDensityᵥ (q - c • p) = D := by
    have hcpInt : Integrable (c • p) sigma := hpInt.smul c
    rw [withDensityᵥ_sub hqInt hcpInt, withDensityᵥ_smul p c,
      hqeq, hpeq]
  have hdUV_eq : dUV =ᵐ[sigma] q - c • p := by
    apply hdUVInt.ae_eq_of_withDensityᵥ_eq
      (hqInt.sub (hpInt.const_mul c))
    calc
      sigma.withDensityᵥ dUV = D := hDeq.symm
      _ = sigma.withDensityᵥ (q - c • p) := hDdensity.symm
  have hbound : ∀ᵐ x ∂sigma, |q x - c * p x| ≤
      (M - m) * Real.sqrt (eU x * eV x) := by
    filter_upwards [hmatrix, heU_nonneg, heV_nonneg] with x hx hxeU hxeV
    rcases hx with ⟨hL0, hN0, hRL, hU0, hV0, hRU⟩
    by_cases hpos : 0 < M - m
    · have hLle : a x - m * eU x ≤ (M - m) * eU x := by
        linarith only [hU0]
      have hNle : b x - m * eV x ≤ (M - m) * eV x := by
        linarith only [hV0]
      have hUle : M * eU x - a x ≤ (M - m) * eU x := by
        linarith only [hL0]
      have hVle : M * eV x - b x ≤ (M - m) * eV x := by
        linarith only [hN0]
      have hprodL : (a x - m * eU x) * (b x - m * eV x) ≤
          ((M - m) * eU x) * ((M - m) * eV x) :=
        mul_le_mul hLle hNle hN0 (mul_nonneg (le_of_lt hpos) hxeU)
      have hprodU : (M * eU x - a x) * (M * eV x - b x) ≤
          ((M - m) * eU x) * ((M - m) * eV x) :=
        mul_le_mul hUle hVle hV0 (mul_nonneg (le_of_lt hpos) hxeU)
      have hsqrtL : Real.sqrt ((a x - m * eU x) * (b x - m * eV x)) ≤
          (M - m) * Real.sqrt (eU x * eV x) := by
        calc
          Real.sqrt ((a x - m * eU x) * (b x - m * eV x)) ≤
              Real.sqrt (((M - m) * eU x) * ((M - m) * eV x)) :=
            Real.sqrt_le_sqrt hprodL
          _ = (M - m) * Real.sqrt (eU x * eV x) := by
            rw [show ((M - m) * eU x) * ((M - m) * eV x) =
                (M - m) ^ 2 * (eU x * eV x) by ring,
              Real.sqrt_mul (sq_nonneg (M - m)), Real.sqrt_sq_eq_abs,
              abs_of_pos hpos]
      have hsqrtU : Real.sqrt ((M * eU x - a x) * (M * eV x - b x)) ≤
          (M - m) * Real.sqrt (eU x * eV x) := by
        calc
          Real.sqrt ((M * eU x - a x) * (M * eV x - b x)) ≤
              Real.sqrt (((M - m) * eU x) * ((M - m) * eV x)) :=
            Real.sqrt_le_sqrt hprodU
          _ = (M - m) * Real.sqrt (eU x * eV x) := by
            rw [show ((M - m) * eU x) * ((M - m) * eV x) =
                (M - m) ^ 2 * (eU x * eV x) by ring,
              Real.sqrt_mul (sq_nonneg (M - m)), Real.sqrt_sq_eq_abs,
              abs_of_pos hpos]
      have hRL' : |q x - m * p x| ≤
          (M - m) * Real.sqrt (eU x * eV x) := hRL.trans hsqrtL
      have hRU' : |M * p x - q x| ≤
          (M - m) * Real.sqrt (eU x * eV x) := hRU.trans hsqrtU
      have hθL : 0 ≤ (M - c) / (M - m) :=
        div_nonneg (sub_nonneg.mpr hcM) (le_of_lt hpos)
      have hθU : 0 ≤ (c - m) / (M - m) :=
        div_nonneg (sub_nonneg.mpr hmc) (le_of_lt hpos)
      have hθsum : (M - c) / (M - m) + (c - m) / (M - m) = 1 := by
        exact aux_lem_diff_measure_density_convex_coeff_sum (ne_of_gt hpos)
      have hid : q x - c * p x =
          (M - c) / (M - m) * (q x - m * p x) -
            (c - m) / (M - m) * (M * p x - q x) := by
        exact aux_lem_diff_measure_density_cross_interpolation (ne_of_gt hpos)
      calc
        |q x - c * p x| =
            |(M - c) / (M - m) * (q x - m * p x) -
              (c - m) / (M - m) * (M * p x - q x)| := by rw [← hid]
        _ ≤ |(M - c) / (M - m) * (q x - m * p x)| +
              |(c - m) / (M - m) * (M * p x - q x)| := abs_sub _ _
        _ = (M - c) / (M - m) * |q x - m * p x| +
              (c - m) / (M - m) * |M * p x - q x| := by
          rw [abs_mul, abs_of_nonneg hθL, abs_mul, abs_of_nonneg hθU]
        _ ≤ (M - c) / (M - m) * ((M - m) * Real.sqrt (eU x * eV x)) +
              (c - m) / (M - m) * ((M - m) * Real.sqrt (eU x * eV x)) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hRL' hθL)
            (mul_le_mul_of_nonneg_left hRU' hθU)
        _ = (M - m) * Real.sqrt (eU x * eV x) := by
          rw [← add_mul, hθsum, one_mul]
    · have hzero : M - m = 0 := by
        exact le_antisymm (le_of_not_gt hpos) (sub_nonneg.mpr (le_trans hmc hcM))
      have hMm : M = m := sub_eq_zero.mp hzero
      have hcm : c = m := by
        linarith only [hmc, hcM, hMm]
      have hU0' := hU0
      have hV0' := hV0
      rw [hMm] at hU0' hV0'
      have hLzero : a x - m * eU x = 0 := by
        linarith only [hL0, hU0']
      have hNzero : b x - m * eV x = 0 := by
        linarith only [hN0, hV0']
      have hsqrt : Real.sqrt ((a x - m * eU x) * (b x - m * eV x)) = 0 := by
        rw [hLzero, zero_mul, Real.sqrt_zero]
      have hRle : |q x - m * p x| ≤ 0 := by
        simpa [hsqrt] using hRL
      have hRzero : q x - m * p x = 0 :=
        abs_eq_zero.mp (le_antisymm hRle (abs_nonneg _))
      have hqzero : q x - c * p x = 0 := by
        rw [hcm]
        exact hRzero
      rw [hqzero, hzero]
      simp
  have hnonneg : ∀ᵐ x ∂sigma, 0 ≤ eU x ∧ 0 ≤ eV x :=
    heU_nonneg.and heV_nonneg
  have hDfinal : GammaF.cross u v - c • GammaE.cross u v =
      sigma.withDensityᵥ dUV := by
    simpa [D] using hDeq
  have hbound' : ∀ᵐ x ∂sigma, |dUV x| ≤
      (M - m) * Real.sqrt (eU x * eV x) := by
    filter_upwards [hdUV_eq, hbound] with x hdx hx
    rw [hdx]
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using hx
  exact ⟨eU, eV, dUV, heUInt, heVInt, hdUVInt, hnonneg, heUeq, heVeq,
    hDfinal, hbound'⟩

end
end Paper
