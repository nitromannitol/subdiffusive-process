module

public import SubdiffusiveProcess.VariationalResponses.VecDotForm
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.VariationalResponses.LocalRepresentative
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.Interior.TranslatedFinitePResidualLift
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.Interior.InhomogeneousGlobalRepresentative
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.Restriction

@[expose] public section

/-!
# Continuous representatives of sourced native weak solutions, `alpha ≥ 1/2`
For the actual cutoff coefficient on the cube `Q` and a scalar source in
`L^{d/(1-alpha)}`, `1/2 ≤ alpha < 1`, every native weak solution has a
continuous representative on `Q`.  Route: native data to GMC's `H1Function` and massive equation
(`ρ = 1`, `μ = 0`), restriction to small translated triadic cubes, GMC's Calderón–Zygmund
residual lift (`g ∈ L^{d/(1-alpha)} ⊆ L^{2d}`), GMC's small-contrast Schauder representative, and
countable-cover gluing of the canonical ball-average representative.
-/

open MeasureTheory Set Metric Filter Topology TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open Homogenization hiding Vec

noncomputable section
namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- A native weak solution with a scalar volume load is GMC's massive weak solution with
`ρ = 1`, `μ = 0` and the coefficient's `L^∞` representative. -/
theorem aux_in_deterministic_regularity_massive_of_native {d : ℕ}
    {Ω : Opens (SpatialCoordinates d)} (a : PositiveCoefficient Ω)
    (f : SpatialCoordinates d → ℝ) (fL2 : DomainL2 Ω)
    (hfL2 : ((fL2 : SpatialCoordinates d → ℝ)) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] f)
    (u : weakSobolevGraph Ω)
    (hu : ∀ psi : killedSobolevGraph Ω,
      sobolevCoefficientForm a (u : SobolevData Ω) (psi : SobolevData Ω) =
        sobolevVolumeLoad fL2 (psi : SobolevData Ω))
    (v : H1Function (Ω : Set (SpatialCoordinates d)))
    (hv : (v : SpatialCoordinates d → ℝ) = fun x => u.val.1 x)
    (hvg : v.grad = fun x i => u.val.2 i x) :
    IsMassiveWeakSolutionOn (fun x => a.val x) (fun _ => 1) 0
      (Ω : Set (SpatialCoordinates d)) v f := by
  intro φ
  have hU : (u : SobolevData Ω) = sobolevDataOfH1 v := by
    refine Prod.ext ?_ ?_
    · refine Lp.ext ((sobolevDataOfH1_fst_coeFn v).trans ?_).symm
      exact Eventually.of_forall fun x => congrFun hv x
    · funext i
      refine Lp.ext ((sobolevDataOfH1_snd_coeFn v i).trans ?_).symm
      exact Eventually.of_forall fun x => by rw [hvg]
  have hint : ∀ i : Fin d, IntegrableOn
      (fun x => a.val x * (v.grad x i * φ.toH1Function.grad x i))
      (Ω : Set (SpatialCoordinates d)) volume := by
    intro i
    have h2 : Integrable (fun x => v.grad x i * φ.toH1Function.grad x i)
        (volume.restrict (Ω : Set (SpatialCoordinates d))) :=
      (v.gradMemL2 i).integrable_mul (φ.toH1Function.gradMemL2 i)
    exact (Lp.memLp a.val).integrable_mul (memLp_one_iff_integrable.2 h2)
  have hψ := hu ⟨sobolevDataOfH1 φ.toH1Function, sobolevDataOfH1_mem_killed φ⟩
  rw [hU, sobolevCoefficientForm_eq_integral_vecDot a v φ.toH1Function hint,
    sobolevVolumeLoad_apply] at hψ
  rw [zero_mul, zero_add, hψ]
  refine integral_congr_ae ?_
  filter_upwards [hfL2, sobolevDataOfH1_fst_coeFn φ.toH1Function] with x h1 h2
  rw [h1, h2]
  ring

/-- Restriction of the scalar (massive, `ρ = 1`, `μ = 0`) equation to an open subset. -/
theorem aux_in_deterministic_regularity_massive_restrict {d : ℕ} {c : Vec d → ℝ}
    {W V : Set (Vec d)} (hW : IsOpen W) (hV : IsOpen V) (hVW : V ⊆ W) {u : H1Function W}
    {f : Vec d → ℝ} (h : IsMassiveWeakSolutionOn c (fun _ => 1) 0 W u f) :
    IsMassiveWeakSolutionOn c (fun _ => 1) 0 V (u.restrict hV hVW) f := by
  intro φ
  have hφ := h (φ.extendByZeroToOpenSuperset hV.measurableSet hW hVW)
  have hflux := Section6BoundaryL2.setIntegral_vecDot_extendByZero hW hV hVW
    (fun p => c p • u.grad p) φ
  have hsrc : ∫ x in W, (fun _ => (1 : ℝ)) x * f x *
      (φ.extendByZeroToOpenSuperset hV.measurableSet hW hVW).toH1Function.toFun x ∂volume =
      ∫ x in V, (fun _ => (1 : ℝ)) x * f x * φ.toH1Function.toFun x ∂volume := by
    rw [H10Function.extendByZeroToOpenSuperset_toFun, H10Function.zeroExtension]
    have hind : (fun x => (fun _ => (1 : ℝ)) x * f x * V.indicator φ.toH1Function.toFun x) =
        V.indicator (fun x => (fun _ => (1 : ℝ)) x * f x * φ.toH1Function.toFun x) := by
      funext x
      by_cases hx : x ∈ V
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    rw [hind, setIntegral_indicator hV.measurableSet, Set.inter_eq_right.2 hVW]
  rw [zero_mul, zero_add] at hφ ⊢
  calc ∫ x in V, vecDot (c x • (u.restrict hV hVW).grad x) (φ.toH1Function.grad x) ∂volume
      = ∫ p in W, vecDot (c p • u.grad p)
          ((φ.extendByZeroToOpenSuperset hV.measurableSet hW hVW).toH1Function.grad p)
          ∂volume := hflux.symm
    _ = _ := hφ
    _ = _ := hsrc

/-- A translated triadic cube is a sup-ball. -/
theorem aux_in_deterministic_regularity_translateSet_eq_ball {d : ℕ} (z : Vec d) (m : ℤ) :
    translateSet z (openCubeSet (originCube d m)) = Metric.ball z ((3 : ℝ) ^ m / 2) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  ext x
  rw [mem_translateSet_iff_sub_mem, Metric.mem_ball, dist_pi_lt_iff (by positivity)]
  simp only [openCubeSet, originCube, cubeScaleFactor, mem_ofPred_eq, Pi.zero_apply,
    Int.cast_zero, zero_sub, zero_add, Pi.sub_apply, Real.dist_eq, abs_lt]
  constructor
  · intro h i; constructor <;> linarith [(h i).1, (h i).2]
  · intro h i; constructor <;> linarith [(h i).1, (h i).2]

/-- **Local continuity.**  Around every point of an open set on which the scalar equation holds
with a continuous positive coefficient (up to an a.e. change) and a source in
`L^{d/(1-alpha)}`, `alpha ≥ 1/2`, the canonical ball-average representative is continuous and
equal to the solution a.e. on a neighbourhood. -/
theorem aux_in_deterministic_regularity_local_cont {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {W : Set (Vec d)} (hW : IsOpen W) {c s : Vec d → ℝ} (hcs : c =ᵐ[volume.restrict W] s)
    (hs : ContinuousOn s W) (hspos : ∀ x ∈ W, 0 < s x)
    {u : H1Function W} {f : Vec d → ℝ} (alpha : ℝ) (halpha : 1 / 2 ≤ alpha)
    (halpha1 : alpha < 1)
    (hf : MemLp f (ENNReal.ofReal ((d : ℝ) / (1 - alpha))) (volume.restrict W))
    (hu : IsMassiveWeakSolutionOn c (fun _ => 1) 0 W u f)
    (x0 : Vec d) (hx0 : x0 ∈ W) :
    ∃ T : Set (Vec d), IsOpen T ∧ x0 ∈ T ∧ T ⊆ W ∧
      ContinuousOn (euclideanBallAverageRepresentative u.toFun) T ∧
      euclideanBallAverageRepresentative u.toFun =ᵐ[volume.restrict T] u.toFun := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hW x0 hx0
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (show (1 / 3 : ℝ) < 1 by norm_num)
  set m : ℤ := -(n : ℤ) with hm
  set T : Set (Vec d) := translateSet x0 (openCubeSet (originCube d m)) with hTdef
  have hTball : T = Metric.ball x0 ((3 : ℝ) ^ m / 2) :=
    aux_in_deterministic_regularity_translateSet_eq_ball x0 m
  have h3m : (3 : ℝ) ^ m = (1 / 3 : ℝ) ^ n := by
    rw [hm, zpow_neg, zpow_natCast, one_div, inv_pow]
  have hTopen : IsOpen T := by rw [hTball]; exact Metric.isOpen_ball
  have hxT : x0 ∈ T := by rw [hTball]; exact Metric.mem_ball_self (by positivity)
  have hTW : T ⊆ W := by
    rw [hTball]
    refine (Metric.ball_subset_ball ?_).trans hball
    rw [h3m]; linarith [pow_pos (show (0 : ℝ) < 1 / 3 by norm_num) n]
  -- the equation on `T`
  set uT := u.restrict hTopen hTW with huT
  have huT' : IsMassiveWeakSolutionOn c (fun _ => 1) 0 T uT f :=
    aux_in_deterministic_regularity_massive_restrict hW hTopen hTW hu
  -- the source exponent
  have h1a : 0 < 1 - alpha := by linarith
  have hqge : 2 * (d : ℝ) ≤ (d : ℝ) / (1 - alpha) := by
    rw [le_div_iff₀ h1a]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hq2 : (2 : ℝ) < (d : ℝ) / (1 - alpha) := by nlinarith
  let q : FiniteLpExponent :=
    { exponent := ENNReal.ofReal ((d : ℝ) / (1 - alpha))
      one_lt := by
        rw [ENNReal.one_lt_ofReal]; linarith
      lt_top := ENNReal.ofReal_lt_top }
  have hqReal : q.exponent.toReal = (d : ℝ) / (1 - alpha) := by
    change (ENNReal.ofReal ((d : ℝ) / (1 - alpha))).toReal = _
    rw [ENNReal.toReal_ofReal (by positivity)]
  have : IsFiniteMeasure (volume.restrict T) := by
    rw [hTball]; exact isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hfT : MemLp f (ENNReal.ofReal ((d : ℝ) / (1 - alpha))) (volume.restrict T) :=
    hf.mono_measure (Measure.restrict_mono hTW le_rfl)
  have hf2 : MemL2On T f := by
    refine hfT.mono_exponent ?_
    rw [show (2 : ENNReal) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal hq2.le
  have hres : MemLp (massiveResidual (fun _ => (1 : ℝ)) 0 uT f) q.exponent
      (volume.restrict T) := by
    have : massiveResidual (fun _ => (1 : ℝ)) 0 uT f = f := by
      funext x; simp [massiveResidual]
    rw [this]; exact hfT
  obtain ⟨g, -, hdiv, hgLp⟩ :=
    exists_finiteLp_divergence_lift_of_isMassiveWeakSolutionOn_translateSet d q
      (by rw [hqReal]; exact hq2) x0 (rhoMax := 1)
      (aestronglyMeasurable_const) (Eventually.of_forall fun _ => by simp) hf2 hres huT'
  have hdiv' : IsDivFormWeakSolutionOn s T uT g :=
    isDivFormWeakSolutionOn_congr_coefficient
      (ae_restrict_of_ae_restrict_of_subset hTW hcs) hdiv
  have hg : MemVectorLpOn T (schauderSourceExponent d (1 / 2)) g := by
    refine hgLp.mono_exponent ?_
    change ENNReal.ofReal ((d : ℝ) / (1 - 1 / 2)) ≤ ENNReal.ofReal ((d : ℝ) / (1 - alpha))
    refine ENNReal.ofReal_le_ofReal ?_
    have : (d : ℝ) / (1 - 1 / 2) = 2 * d := by ring
    rw [this]; exact hqge
  obtain ⟨hcont, hae⟩ := continuousOn_and_ae_eq_euclideanBallAverageRepresentative_inhomogeneous
    hd hTopen (hs.mono hTW) (fun x hx => hspos x (hTW hx)) hdiv' hg
  exact ⟨T, hTopen, hxT, hTW, hcont, hae⟩

/-- **Gluing** local continuity and local a.e. equality over an open set. -/
theorem aux_in_deterministic_regularity_glue_local {d : ℕ} {W : Set (Vec d)}
    (F g0 : Vec d → ℝ)
    (hloc : ∀ x0 ∈ W, ∃ T : Set (Vec d), IsOpen T ∧ x0 ∈ T ∧ T ⊆ W ∧
      ContinuousOn F T ∧ F =ᵐ[volume.restrict T] g0) :
    ContinuousOn F W ∧ F =ᵐ[volume.restrict W] g0 := by
  choose T hTo hxT hTW hTc hTae using hloc
  refine ⟨fun x hx => ((hTc x hx).continuousAt ((hTo x hx).mem_nhds (hxT x hx))).continuousWithinAt,
    ?_⟩
  let V : W → Set (Vec d) := fun p => T p p.2
  have hVopen : ∀ p, IsOpen (V p) := fun p => hTo p p.2
  obtain ⟨S, hScount, hSunion⟩ := TopologicalSpace.isOpen_iUnion_countable V hVopen
  have hcover : W ⊆ ⋃ p ∈ S, V p := by
    intro x hx
    have : x ∈ ⋃ p, V p := Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxT x hx⟩
    rw [← hSunion] at this
    exact this
  have : Countable S := hScount.to_subtype
  have hcover' : W ⊆ ⋃ p : S, V p := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.1 (hcover hx)
    exact Set.mem_iUnion.2 ⟨⟨p, hp⟩, hxp⟩
  refine ae_restrict_of_ae_restrict_of_subset hcover' ?_
  rw [ae_restrict_iUnion_iff]
  intro p
  exact hTae p.1 p.1.2

/-- **`cont` for `1/2 ≤ alpha < 1`**: every native weak solution on `Q` of the actual cutoff
equation with a scalar source in `L^{d/(1-alpha)}(Q)` has a continuous representative on `Q`. -/
theorem aux_in_deterministic_regularity_cont_half {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (alpha : ℝ) (halpha : 1 / 2 ≤ alpha) (halpha1 : alpha < 1)
    (f : SpatialCoordinates d → ℝ)
    (hf : MemLp f (ENNReal.ofReal ((d : ℝ) / (1 - alpha)))
      (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
    (fL2 : DomainL2 (centeredCube Qcentre Qside hQside))
    (hfL2 : ((fL2 : SpatialCoordinates d → ℝ)) =ᵐ[volume.restrict
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] f)
    (u : weakSobolevGraph (centeredCube Qcentre Qside hQside))
    (hu : ∀ psi : killedSobolevGraph (centeredCube Qcentre Qside hQside),
      sobolevCoefficientForm (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside)
        (u : SobolevData (centeredCube Qcentre Qside hQside))
        (psi : SobolevData (centeredCube Qcentre Qside hQside)) =
      sobolevVolumeLoad fL2 (psi : SobolevData (centeredCube Qcentre Qside hQside))) :
    ∃ U : SpatialCoordinates d → ℝ,
      ContinuousOn U (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) ∧
      (((u : SobolevData (centeredCube Qcentre Qside hQside)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U) := by
  obtain ⟨v, hv, hvg⟩ := exists_nativeH1Function_of_weakSobolevGraph u
  have hmass := aux_in_deterministic_regularity_massive_of_native
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside) f fL2 hfL2 u hu v hv hvg
  have : Fact (((centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ⊆
      (closedCube Qcentre Qside hQside : Set (SpatialCoordinates d))) :=
    ⟨centeredCube_subset_closedCube Qcentre hQside⟩
  have hval : ∀ᵐ x ∂volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)),
      ∀ hx : x ∈ (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)),
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside).val x =
          _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM M H omega N Qcentre hQside
            ⟨x, centeredCube_subset_closedCube Qcentre hQside hx⟩ / 1 :=
    normalizedContinuousPositiveCoefficient_coeFn (Ω := centeredCube Qcentre Qside hQside)
      (closedCube Qcentre Qside hQside) (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM M H omega N Qcentre hQside)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficientCM_pos M H omega N Qcentre hQside) 1 one_pos
  have hcoef : (fun x => (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H omega N Qcentre hQside).val x)
      =ᵐ[volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))]
        cutoffCoefficient M H omega N := by
    filter_upwards [hval, ae_restrict_mem (centeredCube Qcentre Qside hQside).isOpen.measurableSet]
      with x hx hxΩ
    rw [hx hxΩ, div_one]
    rfl
  have hloc := fun x0 hx0 => aux_in_deterministic_regularity_local_cont hd
    (centeredCube Qcentre Qside hQside).isOpen hcoef
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous M H omega N).continuousOn
    (fun x _ => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos M H omega N x) alpha halpha halpha1 hf hmass x0 hx0
  obtain ⟨hC, hA⟩ := aux_in_deterministic_regularity_glue_local
    (euclideanBallAverageRepresentative v.toFun) v.toFun hloc
  refine ⟨euclideanBallAverageRepresentative v.toFun, hC, ?_⟩
  have hvf : v.toFun = fun x => (u : SobolevData (centeredCube Qcentre Qside hQside)).1 x := hv
  rw [hvf] at hA ⊢
  exact hA.symm

end SubdiffusiveProcess.Paper
