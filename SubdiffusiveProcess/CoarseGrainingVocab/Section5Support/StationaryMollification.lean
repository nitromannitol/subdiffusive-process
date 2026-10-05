module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationaryGradientDuality
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-!
# Hilbert-space mollification of stationary fields

This is the minimal stationary smoothing operator needed by the Section 5
Hodge calculation.  Unlike a samplewise convolution, it is defined directly
as a Bochner integral in stationary `L²`:

`A_kappa X = integral y, kappa y * U_(-y) X`.

This shorter Hilbert-space formulation avoids
the realization and local-integrability API that is not needed for the
one-step trace identity.
-/

open Filter MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Stationary

noncomputable section

/-- A smooth, compactly supported, nonnegative unit-mass kernel on `Vec d`. -/
structure L2Mollifier (d : ℕ) where
  toFun : Vec d → ℝ
  radius : ℝ
  nonneg : ∀ y, 0 ≤ toFun y
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  compactSupport : HasCompactSupport toFun
  integral_eq_one : ∫ y, toFun y = 1
  support_subset : Function.support toFun ⊆ Metric.ball 0 radius

namespace L2Mollifier

variable {d : ℕ}

theorem continuous (rho : L2Mollifier d) : Continuous rho.toFun :=
  rho.smooth.continuous

theorem integrable (rho : L2Mollifier d) : Integrable rho.toFun volume :=
  rho.continuous.integrable_of_hasCompactSupport rho.compactSupport

/-- The standard normalized bump mollifier at a positive radius. -/
def ofRadius (d : ℕ) {r : ℝ} (hr : 0 < r) : L2Mollifier d where
  toFun := (ContDiffBump.mk (c := (0 : Vec d)) (r / 2) r
    (by linarith) (by linarith)).normed volume
  radius := r
  nonneg := fun y => ContDiffBump.nonneg_normed _ y
  smooth := ContDiffBump.contDiff_normed _
  compactSupport := ContDiffBump.hasCompactSupport_normed _
  integral_eq_one := ContDiffBump.integral_normed _
  support_subset := le_of_eq (ContDiffBump.support_normed_eq _)

end L2Mollifier

variable {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
variable {mu : Measure Omega}
variable [AddAction (Vec d) Omega]
variable [MeasurableConstVAdd (Vec d) Omega]
variable [VAddInvariantMeasure (Vec d) Omega mu]
variable [TopologicalSpace Omega] [R1Space Omega] [BorelSpace Omega]
variable [ContinuousVAdd (Vec d) Omega]
variable [IsLocallyFiniteMeasure mu] [mu.InnerRegularCompactLTTop]

/-- Mollification directly in the stationary Hilbert space. -/
def mollifyL2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (kappa : Vec d → ℝ) (X : Lp E 2 mu) : Lp E 2 mu :=
  ∫ y : Vec d, kappa y • koopman (mu := mu) (-y) X

/-- The Hilbert-valued integrand defining stationary mollification is
continuous for a continuous kernel. -/
theorem continuous_mollifyL2_integrand
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa) (X : Lp E 2 mu) :
    Continuous (fun y : Vec d => kappa y • koopman (mu := mu) (-y) X) := by
  exact hkappa.smul
    ((continuous_koopman_orbit (mu := mu) X).comp continuous_neg)

omit [TopologicalSpace Omega] [R1Space Omega] [BorelSpace Omega]
  [ContinuousVAdd (Vec d) Omega] [IsLocallyFiniteMeasure mu]
  [mu.InnerRegularCompactLTTop] in
/-- The mollifier integrand is continuous whenever the particular Koopman
orbit is continuous; no topology on the sample carrier is needed. -/
theorem continuous_mollifyL2_integrand_of_continuous_koopmanOrbit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa) (X : Lp E 2 mu)
    (hX : Continuous (fun z : Vec d => koopman (mu := mu) z X)) :
    Continuous (fun y : Vec d => kappa y • koopman (mu := mu) (-y) X) := by
  exact hkappa.smul (hX.comp continuous_neg)

/-- A continuous compactly supported kernel gives an integrable
Hilbert-valued stationary mollification integrand. -/
theorem integrable_mollifyL2_integrand
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa) (X : Lp E 2 mu) :
    Integrable (fun y : Vec d => kappa y • koopman (mu := mu) (-y) X) volume := by
  exact (continuous_mollifyL2_integrand (mu := mu) hkappa X)
    |>.integrable_of_hasCompactSupport hcompact.smul_right

omit [TopologicalSpace Omega] [R1Space Omega] [BorelSpace Omega]
  [ContinuousVAdd (Vec d) Omega] [IsLocallyFiniteMeasure mu]
  [mu.InnerRegularCompactLTTop] in
/-- Integrability of the mollifier integrand from continuity of the
particular Koopman orbit. -/
theorem integrable_mollifyL2_integrand_of_continuous_koopmanOrbit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa) (X : Lp E 2 mu)
    (hX : Continuous (fun z : Vec d => koopman (mu := mu) z X)) :
    Integrable (fun y : Vec d => kappa y • koopman (mu := mu) (-y) X) volume := by
  exact (continuous_mollifyL2_integrand_of_continuous_koopmanOrbit
    (mu := mu) hkappa X hX).integrable_of_hasCompactSupport hcompact.smul_right

/-- Stationary mollification is additive in the field. -/
theorem mollifyL2_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa) (X Y : Lp E 2 mu) :
    mollifyL2 (mu := mu) kappa (X + Y) =
      mollifyL2 (mu := mu) kappa X + mollifyL2 (mu := mu) kappa Y := by
  rw [mollifyL2, mollifyL2, mollifyL2]
  simp_rw [map_add, smul_add]
  exact integral_add
    (integrable_mollifyL2_integrand (mu := mu) hkappa hcompact X)
    (integrable_mollifyL2_integrand (mu := mu) hkappa hcompact Y)

omit [TopologicalSpace Omega] [R1Space Omega] [BorelSpace Omega]
  [ContinuousVAdd (Vec d) Omega] [IsLocallyFiniteMeasure mu]
  [mu.InnerRegularCompactLTTop] in
/-- Mollification preserves addition for two strongly continuous particular
Koopman orbits. -/
theorem mollifyL2_add_of_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa) (X Y : Lp E 2 mu)
    (hX : Continuous (fun z : Vec d => koopman (mu := mu) z X))
    (hY : Continuous (fun z : Vec d => koopman (mu := mu) z Y)) :
    mollifyL2 (mu := mu) kappa (X + Y) =
      mollifyL2 (mu := mu) kappa X + mollifyL2 (mu := mu) kappa Y := by
  rw [mollifyL2, mollifyL2, mollifyL2]
  simp_rw [map_add, smul_add]
  exact integral_add
    (integrable_mollifyL2_integrand_of_continuous_koopmanOrbit
      (mu := mu) hkappa hcompact X hX)
    (integrable_mollifyL2_integrand_of_continuous_koopmanOrbit
      (mu := mu) hkappa hcompact Y hY)

omit [TopologicalSpace Omega] [R1Space Omega] [BorelSpace Omega]
  [ContinuousVAdd (Vec d) Omega] [IsLocallyFiniteMeasure mu]
  [mu.InnerRegularCompactLTTop] in
/-- Mollification commutes with a finite sum of strongly continuous
particular Koopman orbits. -/
theorem mollifyL2_finset_sum_of_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type*} (s : Finset I) (X : I → Lp E 2 mu)
    (hX : ∀ i ∈ s, Continuous (fun z : Vec d => koopman (mu := mu) z (X i)))
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa) :
    mollifyL2 (mu := mu) kappa (∑ i ∈ s, X i) =
      ∑ i ∈ s, mollifyL2 (mu := mu) kappa (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mollifyL2]
  | @insert i s his ih =>
      simp only [Finset.sum_insert his]
      rw [mollifyL2_add_of_continuous hkappa hcompact]
      · rw [ih (fun j hj => hX j (Finset.mem_insert_of_mem hj))]
      · exact hX i (Finset.mem_insert_self i s)
      · have hc := continuous_finsetSum s fun j hj =>
          hX j (Finset.mem_insert_of_mem hj)
        convert hc using 1
        funext z
        simp only [map_sum]

omit [TopologicalSpace Omega] [R1Space Omega] [BorelSpace Omega]
  [ContinuousVAdd (Vec d) Omega] [IsLocallyFiniteMeasure mu]
  [mu.InnerRegularCompactLTTop] in
/-- Mollification preserves subtraction for two strongly continuous
particular Koopman orbits. -/
theorem mollifyL2_sub_of_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa) (X Y : Lp E 2 mu)
    (hX : Continuous (fun z : Vec d => koopman (mu := mu) z X))
    (hY : Continuous (fun z : Vec d => koopman (mu := mu) z Y)) :
    mollifyL2 (mu := mu) kappa (X - Y) =
      mollifyL2 (mu := mu) kappa X - mollifyL2 (mu := mu) kappa Y := by
  rw [mollifyL2, mollifyL2, mollifyL2]
  simp_rw [map_sub, smul_sub]
  exact integral_sub
    (integrable_mollifyL2_integrand_of_continuous_koopmanOrbit
      (mu := mu) hkappa hcompact X hX)
    (integrable_mollifyL2_integrand_of_continuous_koopmanOrbit
      (mu := mu) hkappa hcompact Y hY)

omit [TopologicalSpace Omega] [R1Space Omega] [BorelSpace Omega]
  [ContinuousVAdd (Vec d) Omega] [IsLocallyFiniteMeasure mu]
  [mu.InnerRegularCompactLTTop] in
/-- Stationary mollification is real-linear in the field. -/
theorem mollifyL2_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {kappa : Vec d → ℝ} (c : ℝ) (X : Lp E 2 mu) :
    mollifyL2 (mu := mu) kappa (c • X) =
      c • mollifyL2 (mu := mu) kappa X := by
  rw [mollifyL2, mollifyL2]
  simp_rw [map_smul, smul_comm (kappa _) c]
  exact integral_smul c _

omit [TopologicalSpace Omega] [R1Space Omega] [BorelSpace Omega]
  [ContinuousVAdd (Vec d) Omega] [IsLocallyFiniteMeasure mu]
  [mu.InnerRegularCompactLTTop] in
/-- The stationary mollifier has operator norm at most the `L¹` norm of its
kernel. -/
theorem norm_mollifyL2_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa) (X : Lp E 2 mu) :
    ‖mollifyL2 (mu := mu) kappa X‖ ≤ (∫ y : Vec d, |kappa y|) * ‖X‖ := by
  have hkappaInt : Integrable kappa volume :=
    hkappa.integrable_of_hasCompactSupport hcompact
  rw [mollifyL2]
  calc
    ‖∫ y : Vec d, kappa y • koopman (mu := mu) (-y) X‖ ≤
        ∫ y : Vec d, |kappa y| * ‖X‖ := by
      apply norm_integral_le_of_norm_le (hkappaInt.abs.mul_const ‖X‖)
      filter_upwards [] with y
      rw [norm_smul, LinearIsometry.norm_map]
      simp only [Real.norm_eq_abs]
      rfl
    _ = (∫ y : Vec d, |kappa y|) * ‖X‖ := integral_mul_const ‖X‖ _

/-- Stationary mollification as a bounded linear operator on `L²`. -/
def mollifyL2CLM
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (kappa : Vec d → ℝ) (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa) : Lp E 2 mu →L[ℝ] Lp E 2 mu :=
  LinearMap.mkContinuous
    { toFun := mollifyL2 (mu := mu) kappa
      map_add' := mollifyL2_add (mu := mu) hkappa hcompact
      map_smul' := mollifyL2_smul (mu := mu) }
    (∫ y : Vec d, |kappa y|) (norm_mollifyL2_le (mu := mu) hkappa hcompact)

@[simp] theorem mollifyL2CLM_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (kappa : Vec d → ℝ) (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa) (X : Lp E 2 mu) :
    mollifyL2CLM (mu := mu) kappa hkappa hcompact X =
      mollifyL2 (mu := mu) kappa X := rfl

/-- A continuous linear map on the value space commutes with stationary
mollification. -/
theorem map_mollifyL2
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (T : Lp E 2 mu →L[ℝ] Lp F 2 mu)
    (hT : ∀ z : Vec d, ∀ X : Lp E 2 mu,
      T (koopman (mu := mu) z X) = koopman (mu := mu) z (T X))
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa) (X : Lp E 2 mu) :
    T (mollifyL2 (mu := mu) kappa X) =
      mollifyL2 (mu := mu) kappa (T X) := by
  rw [mollifyL2, mollifyL2, ← T.integral_comp_comm
    (integrable_mollifyL2_integrand (mu := mu) hkappa hcompact X)]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [map_smul, hT]

/-- Coordinate extraction commutes with stationary mollification. -/
theorem vectorL2Coord_mollifyL2
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa) (F : VectorL2 d mu) (i : Fin d) :
    vectorL2Coord (mu := mu) i (mollifyL2 (mu := mu) kappa F) =
      mollifyL2 (mu := mu) kappa (vectorL2Coord (mu := mu) i F) := by
  exact map_mollifyL2 (mu := mu) (vectorL2Coord (mu := mu) i)
    (fun z X => (koopman_vectorL2Coord z i X).symm) hkappa hcompact F

omit [TopologicalSpace Omega] [R1Space Omega] [BorelSpace Omega]
  [ContinuousVAdd (Vec d) Omega] [IsLocallyFiniteMeasure mu]
  [mu.InnerRegularCompactLTTop] in
/-- Coordinate extraction commutes with mollification when the particular
vector orbit is strongly continuous. -/
theorem vectorL2Coord_mollifyL2_of_continuous
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa) (F : VectorL2 d mu)
    (hF : Continuous (fun z : Vec d => koopman (mu := mu) z F))
    (i : Fin d) :
    vectorL2Coord (mu := mu) i (mollifyL2 (mu := mu) kappa F) =
      mollifyL2 (mu := mu) kappa (vectorL2Coord (mu := mu) i F) := by
  rw [mollifyL2, mollifyL2]
  have hint := integrable_mollifyL2_integrand_of_continuous_koopmanOrbit
    (mu := mu) hkappa hcompact F hF
  rw [← (vectorL2Coord (mu := mu) i).integral_comp_comm hint]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [map_smul, koopman_vectorL2Coord]

/-- Stationary mollification commutes with every Koopman translation. -/
theorem koopman_mollifyL2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (z : Vec d) {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa) (X : Lp E 2 mu) :
    koopman (mu := mu) z (mollifyL2 (mu := mu) kappa X) =
      mollifyL2 (mu := mu) kappa (koopman (mu := mu) z X) := by
  apply map_mollifyL2 (mu := mu) (koopman (mu := mu) z).toContinuousLinearMap
    (fun w Y => ?_) hkappa hcompact X
  change koopman (mu := mu) z (koopman (mu := mu) w Y) =
    koopman (mu := mu) w (koopman (mu := mu) z Y)
  rw [koopman_koopman, koopman_koopman]
  congr 2
  abel

/-- Mollifying a genuine strong horizontal gradient mollifies its primitive
and its vector field simultaneously. -/
theorem HasHorizontalGradient.mollifyL2
    {phi : ScalarL2 mu} {F : VectorL2 d mu}
    (hphi : HasHorizontalGradient (mu := mu) phi F)
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa) :
    HasHorizontalGradient (mu := mu)
      (mollifyL2 (mu := mu) kappa phi)
      (mollifyL2 (mu := mu) kappa F) := by
  intro i
  have hderiv := (mollifyL2CLM (mu := mu) kappa hkappa hcompact).hasFDerivAt
    |>.comp_hasDerivAt 0 (hphi i)
  rw [vectorL2Coord_mollifyL2 (mu := mu) hkappa hcompact]
  convert hderiv using 1
  · funext t
    exact koopman_mollifyL2 (mu := mu)
      (t • (Pi.single i 1 : Vec d)) hkappa hcompact phi
  · simp only [mollifyL2CLM_apply]

/-- Stationary mollification preserves the linear range of strong horizontal
gradients. -/
theorem mollifyL2_mem_horizontalGradientRange
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa) {F : VectorL2 d mu}
    (hF : F ∈ horizontalGradientRange (mu := mu) (d := d)) :
    mollifyL2 (mu := mu) kappa F ∈
      horizontalGradientRange (mu := mu) (d := d) := by
  obtain ⟨phi, hphi⟩ := hF
  exact ⟨mollifyL2 (mu := mu) kappa phi,
    hphi.mollifyL2 hkappa hcompact⟩

/-- Stationary mollification preserves the closed stationary potential
subspace. -/
theorem mollifyL2_mem_stationaryPotentialSubspace
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa) {F : VectorL2 d mu}
    (hF : F ∈ stationaryPotentialSubspace (mu := mu) (d := d)) :
    mollifyL2 (mu := mu) kappa F ∈
      stationaryPotentialSubspace (mu := mu) (d := d) := by
  let T := mollifyL2CLM (mu := mu) (E := HilbertVec d) kappa hkappa hcompact
  let S := horizontalGradientRange (mu := mu) (d := d)
  have hmap : S.map (T : VectorL2 d mu →ₗ[ℝ] VectorL2 d mu) ≤ S := by
    rintro _ ⟨F, hFS, rfl⟩
    exact mollifyL2_mem_horizontalGradientRange hkappa hcompact hFS
  have hmemMap : T F ∈ S.topologicalClosure.map
      (T : VectorL2 d mu →ₗ[ℝ] VectorL2 d mu) := ⟨F, hF, rfl⟩
  have hclosure : T F ∈
      (S.map (T : VectorL2 d mu →ₗ[ℝ] VectorL2 d mu)).topologicalClosure :=
    Submodule.topologicalClosure_map T S hmemMap
  exact (Submodule.topologicalClosure_mono hmap) hclosure

omit [TopologicalSpace Omega] [R1Space Omega] [BorelSpace Omega]
  [ContinuousVAdd (Vec d) Omega] [IsLocallyFiniteMeasure mu]
  [mu.InnerRegularCompactLTTop] in
/-- Mollification preserves the closed potential space using! only strong
continuity of the particular potential field's orbit. -/
theorem mollifyL2_mem_stationaryPotentialSubspace_of_continuous
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa) {F : VectorL2 d mu}
    (hF : F ∈ stationaryPotentialSubspace (mu := mu) (d := d))
    (hForbit : Continuous (fun z : Vec d => koopman (mu := mu) z F)) :
    mollifyL2 (mu := mu) kappa F ∈
      stationaryPotentialSubspace (mu := mu) (d := d) := by
  let S := stationaryPotentialSubspace (mu := mu) (d := d)
  change mollifyL2 (mu := mu) kappa F ∈ S
  rw [← S.orthogonal_orthogonal]
  refine (Submodule.mem_orthogonal _ _).2 fun R hR => ?_
  rw [mollifyL2]
  have hint := integrable_mollifyL2_integrand_of_continuous_koopmanOrbit
    (mu := mu) hkappa hcompact F hForbit
  rw [← integral_inner hint R]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [] with y
  change inner ℝ R (kappa y • koopman (mu := mu) (-y) F) = (0 : ℝ)
  rw [inner_smul_right, inner_koopman_right]
  have hRy : koopman (mu := mu) y R ∈
      stationarySolenoidalSubspace (mu := mu) (d := d) :=
    koopman_mem_stationarySolenoidalSubspace y hR
  have hzero : inner ℝ F (koopman (mu := mu) y R) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hF hRy
  simp only [neg_neg, real_inner_comm, hzero, mul_zero]

/-- Stationary mollification preserves the stationary-solenoidal subspace. -/
theorem mollifyL2_mem_stationarySolenoidalSubspace
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa) {F : VectorL2 d mu}
    (hF : F ∈ stationarySolenoidalSubspace (mu := mu) (d := d)) :
    mollifyL2 (mu := mu) kappa F ∈
      stationarySolenoidalSubspace (mu := mu) (d := d) := by
  refine (Submodule.mem_orthogonal _ _).2 fun U hU => ?_
  rw [mollifyL2]
  have hint := integrable_mollifyL2_integrand
    (mu := mu) hkappa hcompact F
  rw [← integral_inner hint U]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [] with y
  change inner ℝ U (kappa y • koopman (mu := mu) (-y) F) = (0 : ℝ)
  rw [inner_smul_right, inner_koopman_right]
  have hUy : koopman (mu := mu) y U ∈
      stationaryPotentialSubspace (mu := mu) (d := d) :=
    koopman_mem_stationaryPotentialSubspace y hU
  have hzero : inner ℝ (koopman (mu := mu) y U) F = 0 :=
    (Submodule.mem_orthogonal _ _).1 hF _ hUy
  simp only [neg_neg, hzero, mul_zero]

omit [TopologicalSpace Omega] [R1Space Omega] [BorelSpace Omega]
  [ContinuousVAdd (Vec d) Omega] [IsLocallyFiniteMeasure mu]
  [mu.InnerRegularCompactLTTop] in
/-- The solenoidal-preservation argument only needs continuity of the orbit
being mollified. -/
theorem mollifyL2_mem_stationarySolenoidalSubspace_of_continuous
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa) {F : VectorL2 d mu}
    (hF : F ∈ stationarySolenoidalSubspace (mu := mu) (d := d))
    (hForbit : Continuous (fun z : Vec d => koopman (mu := mu) z F)) :
    mollifyL2 (mu := mu) kappa F ∈
      stationarySolenoidalSubspace (mu := mu) (d := d) := by
  refine (Submodule.mem_orthogonal _ _).2 fun U hU => ?_
  rw [mollifyL2]
  have hint := integrable_mollifyL2_integrand_of_continuous_koopmanOrbit
    (mu := mu) hkappa hcompact F hForbit
  rw [← integral_inner hint U]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [] with y
  change inner ℝ U (kappa y • koopman (mu := mu) (-y) F) = (0 : ℝ)
  rw [inner_smul_right, inner_koopman_right]
  have hUy : koopman (mu := mu) y U ∈
      stationaryPotentialSubspace (mu := mu) (d := d) :=
    koopman_mem_stationaryPotentialSubspace y hU
  have hzero : inner ℝ (koopman (mu := mu) y U) F = 0 :=
    (Submodule.mem_orthogonal _ _).1 hF _ hUy
  simp only [neg_neg, hzero, mul_zero]

/-- Jensen's elementary `L²`-Hilbert estimate for a unit-mass stationary
mollifier. -/
theorem norm_mollifyL2_sub_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (rho : L2Mollifier d) (X : Lp E 2 mu) {epsilon : ℝ}
    (horbit : ∀ y ∈ Metric.ball (0 : Vec d) rho.radius,
      ‖koopman (mu := mu) (-y) X - X‖ ≤ epsilon) :
    ‖mollifyL2 (mu := mu) rho.toFun X - X‖ ≤ epsilon := by
  have hconstInt : Integrable (fun y : Vec d => rho.toFun y • X) volume := by
    exact (rho.continuous.smul continuous_const).integrable_of_hasCompactSupport
      rho.compactSupport.smul_right
  have hrepr : mollifyL2 (mu := mu) rho.toFun X - X =
      ∫ y : Vec d, rho.toFun y • (koopman (mu := mu) (-y) X - X) := by
    rw [mollifyL2]
    have hmain := integrable_mollifyL2_integrand
      (mu := mu) rho.continuous rho.compactSupport X
    have hrhoX : (∫ y : Vec d, rho.toFun y • X) = X := by
      rw [integral_smul_const, rho.integral_eq_one, one_smul]
    calc
      (∫ y : Vec d, rho.toFun y • koopman (mu := mu) (-y) X) - X =
          (∫ y : Vec d, rho.toFun y • koopman (mu := mu) (-y) X) -
            ∫ y : Vec d, rho.toFun y • X := by
        rw [hrhoX]
      _ = ∫ y : Vec d, (rho.toFun y • koopman (mu := mu) (-y) X) -
          rho.toFun y • X := (integral_sub hmain hconstInt).symm
      _ = ∫ y : Vec d, rho.toFun y •
          (koopman (mu := mu) (-y) X - X) := by
        congr 1
        funext y
        rw [smul_sub]
  rw [hrepr]
  have hweight : Integrable (fun y : Vec d => rho.toFun y * epsilon) volume :=
    rho.integrable.mul_const epsilon
  calc
    ‖∫ y : Vec d, rho.toFun y •
        (koopman (mu := mu) (-y) X - X)‖ ≤
        ∫ y : Vec d, rho.toFun y * epsilon := by
      apply norm_integral_le_of_norm_le hweight
      filter_upwards [] with y
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (rho.nonneg y)]
      by_cases hy : rho.toFun y = 0
      · simp [hy]
      · exact mul_le_mul_of_nonneg_left
          (horbit y (rho.support_subset hy)) (rho.nonneg y)
    _ = epsilon := by
      rw [integral_mul_const, rho.integral_eq_one, one_mul]

omit [TopologicalSpace Omega] [R1Space Omega] [BorelSpace Omega]
  [ContinuousVAdd (Vec d) Omega] [IsLocallyFiniteMeasure mu]
  [mu.InnerRegularCompactLTTop] in
/-- Jensen's `L²` estimate when continuity is supplied only for the
particular Koopman orbit being mollified. -/
theorem norm_mollifyL2_sub_le_of_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (rho : L2Mollifier d) (X : Lp E 2 mu)
    (hX : Continuous (fun z : Vec d => koopman (mu := mu) z X))
    {epsilon : ℝ}
    (horbit : ∀ y ∈ Metric.ball (0 : Vec d) rho.radius,
      ‖koopman (mu := mu) (-y) X - X‖ ≤ epsilon) :
    ‖mollifyL2 (mu := mu) rho.toFun X - X‖ ≤ epsilon := by
  have hconstInt : Integrable (fun y : Vec d => rho.toFun y • X) volume := by
    exact (rho.continuous.smul continuous_const).integrable_of_hasCompactSupport
      rho.compactSupport.smul_right
  have hrepr : mollifyL2 (mu := mu) rho.toFun X - X =
      ∫ y : Vec d, rho.toFun y • (koopman (mu := mu) (-y) X - X) := by
    rw [mollifyL2]
    have hmain := integrable_mollifyL2_integrand_of_continuous_koopmanOrbit
      (mu := mu) rho.continuous rho.compactSupport X hX
    have hrhoX : (∫ y : Vec d, rho.toFun y • X) = X := by
      rw [integral_smul_const, rho.integral_eq_one, one_smul]
    calc
      (∫ y : Vec d, rho.toFun y • koopman (mu := mu) (-y) X) - X =
          (∫ y : Vec d, rho.toFun y • koopman (mu := mu) (-y) X) -
            ∫ y : Vec d, rho.toFun y • X := by
        rw [hrhoX]
      _ = ∫ y : Vec d, (rho.toFun y • koopman (mu := mu) (-y) X) -
          rho.toFun y • X := (integral_sub hmain hconstInt).symm
      _ = ∫ y : Vec d, rho.toFun y •
          (koopman (mu := mu) (-y) X - X) := by
        congr 1
        funext y
        rw [smul_sub]
  rw [hrepr]
  have hweight : Integrable (fun y : Vec d => rho.toFun y * epsilon) volume :=
    rho.integrable.mul_const epsilon
  calc
    ‖∫ y : Vec d, rho.toFun y •
        (koopman (mu := mu) (-y) X - X)‖ ≤
        ∫ y : Vec d, rho.toFun y * epsilon := by
      apply norm_integral_le_of_norm_le hweight
      filter_upwards [] with y
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (rho.nonneg y)]
      by_cases hy : rho.toFun y = 0
      · simp [hy]
      · exact mul_le_mul_of_nonneg_left
          (horbit y (rho.support_subset hy)) (rho.nonneg y)
    _ = epsilon := by
      rw [integral_mul_const, rho.integral_eq_one, one_mul]

/-- Smooth stationary mollifications approximate every stationary `L²`
field arbitrarily well. -/
theorem exists_mollifier_norm_mollifyL2_sub_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (X : Lp E 2 mu) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ rho : L2Mollifier d,
      ‖mollifyL2 (mu := mu) rho.toFun X - X‖ < epsilon := by
  let eta : ℝ := epsilon / 2
  have heta : 0 < eta := div_pos hepsilon (by norm_num)
  have heta_lt : eta < epsilon := by
    dsimp only [eta]
    linarith
  have hcont : ContinuousAt
      (fun z : Vec d => koopman (mu := mu) z X) 0 :=
    (continuous_koopman_orbit (mu := mu) (d := d) X).continuousAt
  have hnhds : ∀ᶠ z : Vec d in nhds 0,
      ‖koopman (mu := mu) z X - X‖ < eta := by
    have hnorm : ContinuousAt
        (fun z : Vec d => ‖koopman (mu := mu) z X - X‖) 0 :=
      (hcont.sub (continuousAt_const : ContinuousAt
        (fun _ : Vec d => X) 0)).norm
    exact hnorm.eventually_lt continuousAt_const (by
      simpa only [koopman_zero, sub_self, norm_zero] using! heta)
  obtain ⟨r, hr, hrball⟩ := Metric.eventually_nhds_iff.1 hnhds
  let rho := L2Mollifier.ofRadius d hr
  have hglobal := continuous_koopmanOrbit_of_continuousAt_zero X hcont
  refine ⟨rho, lt_of_le_of_lt
    (norm_mollifyL2_sub_le_of_continuous
      (mu := mu) (epsilon := eta) rho X hglobal ?_) heta_lt⟩
  intro y hy
  apply le_of_lt (hrball (y := -y) ?_)
  rw [dist_zero_right, norm_neg]
  change y ∈ Metric.ball (0 : Vec d) r at hy
  simpa only [Metric.mem_ball, dist_zero_right] using! hy

omit [TopologicalSpace Omega] [R1Space Omega] [BorelSpace Omega]
  [ContinuousVAdd (Vec d) Omega] [IsLocallyFiniteMeasure mu]
  [mu.InnerRegularCompactLTTop] in
/-- Approximate identity for one stationary field from strong continuity of
its particular Koopman orbit at the identity. -/
theorem exists_mollifier_norm_mollifyL2_sub_lt_of_continuousAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (X : Lp E 2 mu)
    (hcont : ContinuousAt (fun z : Vec d => koopman (mu := mu) z X) 0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ rho : L2Mollifier d,
      ‖mollifyL2 (mu := mu) rho.toFun X - X‖ < epsilon := by
  let eta : ℝ := epsilon / 2
  have heta : 0 < eta := div_pos hepsilon (by norm_num)
  have heta_lt : eta < epsilon := by
    dsimp only [eta]
    linarith
  have hnhds : ∀ᶠ z : Vec d in nhds 0,
      ‖koopman (mu := mu) z X - X‖ < eta := by
    have hnorm : ContinuousAt
        (fun z : Vec d => ‖koopman (mu := mu) z X - X‖) 0 :=
      (hcont.sub (continuousAt_const : ContinuousAt
        (fun _ : Vec d => X) 0)).norm
    exact hnorm.eventually_lt continuousAt_const (by
      simpa only [koopman_zero, sub_self, norm_zero] using! heta)
  obtain ⟨r, hr, hrball⟩ := Metric.eventually_nhds_iff.1 hnhds
  let rho := L2Mollifier.ofRadius d hr
  have hglobal := continuous_koopmanOrbit_of_continuousAt_zero X hcont
  refine ⟨rho, lt_of_le_of_lt
    (norm_mollifyL2_sub_le_of_continuous
      (mu := mu) (epsilon := eta) rho X hglobal ?_) heta_lt⟩
  intro y hy
  apply le_of_lt (hrball (y := -y) ?_)
  rw [dist_zero_right, norm_neg]
  change y ∈ Metric.ball (0 : Vec d) r at hy
  simpa only [Metric.mem_ball, dist_zero_right] using! hy

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Stationary
