import Mathlib
import SubdiffusiveProcess.Paper.prop_growth
import SubdiffusiveProcess.Paper.prop_growth_large_root
import SubdiffusiveProcess.Paper.killed_continuous_boundary_zero
import SubdiffusiveProcess.Sobolev.GradientGrowthOnCubes

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped Topology ENNReal NNReal InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The actual killed source solution solves the Dirichlet problem with zero datum and the
source function `F` (any function a.e. equal to the `L²` source `g`). -/
theorem aux_conv_represented_source_clause_solves
    {d : ℕ} {Q : Opens (SpatialCoordinates d)} (S : ResponseSpace Q)
    (hS : S.space = killedSobolevGraph Q) (a : PositiveCoefficient Q)
    (g : DomainL2 Q) (F : SpatialCoordinates d → ℝ)
    (hgF : (g : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] F) :
    SolvesDirichlet a F ⟨0, zero_mem _⟩
      ⟨((responseSolution S a ((sobolevVolumeLoad g).comp S.space.subtypeL)).val : SobolevData Q),
        S.le_weak (responseSolution S a ((sobolevVolumeLoad g).comp S.space.subtypeL)).2⟩ := by
  refine ⟨?_, ?_⟩
  · change ((responseSolution S a ((sobolevVolumeLoad g).comp S.space.subtypeL)).val : SobolevData Q) - 0 ∈ _
    rw [sub_zero, ← hS]
    exact (responseSolution S a ((sobolevVolumeLoad g).comp S.space.subtypeL)).2
  · intro ψ
    have hψ : (ψ : SobolevData Q) ∈ S.space := by rw [hS]; exact ψ.2
    have hspec := responseSolution_spec S a ((sobolevVolumeLoad g).comp S.space.subtypeL)
      ⟨(ψ : SobolevData Q), hψ⟩
    rw [responseForm_apply] at hspec
    rw [sobolevCoefficientForm_apply]
    refine hspec.trans ?_
    simp only [ContinuousLinearMap.comp_apply, sobolevVolumeLoad_apply]
    refine integral_congr_ae ?_
    filter_upwards [hgF] with x hx
    rw [hx]
    rfl


/-- `c2Norm` of the zero function is at most zero. -/
theorem aux_conv_represented_source_clause_c2Norm_zero {d : ℕ} (S : Set (SpatialCoordinates d)) :
    c2Norm S (fun _ => (0 : ℝ)) ≤ 0 := by
  unfold c2Norm
  have h1 : sSup {v : ℝ | ∃ x ∈ S, v = |(fun _ : SpatialCoordinates d => (0 : ℝ)) x|} ≤ 0 := by
    apply Real.sSup_nonpos
    rintro v ⟨x, -, rfl⟩
    simp
  have h2 : sSup {v : ℝ | ∃ x ∈ S,
      v = ‖fderiv ℝ (fun _ : SpatialCoordinates d => (0 : ℝ)) x‖} ≤ 0 := by
    apply Real.sSup_nonpos
    rintro v ⟨x, -, rfl⟩
    simp
  have h3 : sSup {v : ℝ | ∃ x ∈ S, v = ‖fderiv ℝ (fderiv ℝ
      (fun _ : SpatialCoordinates d => (0 : ℝ))) x‖} ≤ 0 := by
    apply Real.sSup_nonpos
    rintro v ⟨x, -, rfl⟩
    have : fderiv ℝ (fderiv ℝ (fun _ : SpatialCoordinates d => (0 : ℝ))) x = 0 := by simp
    rw [this]
    exact (norm_zero (E := SpatialCoordinates d →L[ℝ] (SpatialCoordinates d →L[ℝ] ℝ))).le
  linarith


/-- A property holding almost everywhere holds on a measurable set of full measure. -/
theorem aux_conv_represented_source_clause_event {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {P : α → Prop} (h : ∀ᵐ x ∂μ, P x) :
    ∃ G : Set α, MeasurableSet G ∧ μ Gᶜ = 0 ∧ ∀ x ∈ G, P x := by
  classical
  refine ⟨(toMeasurable μ {x | ¬ P x})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
  · simp only [compl_compl]
    rw [measure_toMeasurable]
    exact ae_iff.1 h
  · intro x hx
    by_contra hbad
    exact hx (subset_toMeasurable μ {x | ¬ P x} hbad)

/-- Measurable nonnegative majorant with the first-moment bank. -/
theorem aux_conv_represented_source_clause_pos_majorant {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (K : ℕ → α → ℝ) (hmem : ∀ N, MemLp (K N) (ENNReal.ofReal 1) μ)
    (Cb : ℝ) (hb : ∀ N, eLpNorm (K N) (ENNReal.ofReal 1) μ ≤ ENNReal.ofReal Cb) :
    ∃ Kh : ℕ → α → ℝ, (∀ N, Measurable (Kh N)) ∧ (∀ N β, 0 ≤ Kh N β) ∧
      (∀ N, ∀ᵐ β ∂μ, K N β ≤ Kh N β) ∧
      (∀ N, MemLp (Kh N) (ENNReal.ofReal 1) μ ∧
        eLpNorm (Kh N) (ENNReal.ofReal 1) μ ≤ ENNReal.ofReal (max Cb 0)) := by
  classical
  let Km : ℕ → α → ℝ := fun N => (hmem N).aestronglyMeasurable.mk (K N)
  have hKm : ∀ N, StronglyMeasurable (Km N) := fun N =>
    (hmem N).aestronglyMeasurable.stronglyMeasurable_mk
  have hKae : ∀ N, K N =ᵐ[μ] Km N := fun N => (hmem N).aestronglyMeasurable.ae_eq_mk
  refine ⟨fun N β => max (Km N β) 0, fun N => (hKm N).measurable.max measurable_const,
    fun N β => le_max_right _ _, fun N => ?_, fun N => ?_⟩
  · filter_upwards [hKae N] with β hβ
    rw [hβ]
    exact le_max_left _ _
  · have hmeas : AEStronglyMeasurable (fun β => max (Km N β) 0) μ :=
      ((hKm N).measurable.max measurable_const).aestronglyMeasurable
    have hle : eLpNorm (fun β => max (Km N β) 0) (ENNReal.ofReal 1) μ ≤
        eLpNorm (K N) (ENNReal.ofReal 1) μ := by
      refine eLpNorm_mono_ae ?_
      filter_upwards [hKae N] with β hβ
      rw [hβ, Real.norm_eq_abs, Real.norm_eq_abs]
      rcases le_total (Km N β) 0 with h | h
      · rw [max_eq_right h, abs_zero]; exact abs_nonneg _
      · rw [max_eq_left h]
    refine ⟨⟨hmeas, ?_⟩, hle.trans ((hb N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))⟩
    exact lt_of_le_of_lt hle (hmem N).2


/-- `closure` of the open cube is the closed cube. -/
theorem aux_conv_represented_source_clause_closure {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) :
    closure ((centeredCube z r hr : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) =
      (closedCube z r hr : Set (SpatialCoordinates d)) := by
  change closure (Metric.ball z (r / 2)) = Metric.closedBall z (r / 2)
  exact closure_ball z (half_pos hr).ne'

/-- A continuous representative of a killed function vanishes on the frontier of the cube. -/
theorem aux_conv_represented_source_clause_frontier {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (w : SobolevData (centeredCube z r hr))
    (hw : w ∈ killedSobolevGraph (centeredCube z r hr)) (U : SpatialCoordinates d → ℝ)
    (hUc : Continuous U)
    (hUae : ((w.1 : DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U) :
    ∀ x ∈ frontier ((centeredCube z r hr : Opens (SpatialCoordinates d)) :
      Set (SpatialCoordinates d)), U x = 0 := by
  intro x hx
  have hxf : x ∈ closure ((centeredCube z r hr : Opens (SpatialCoordinates d)) :
      Set (SpatialCoordinates d)) ∧ x ∉ interior ((centeredCube z r hr :
      Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) := hx
  rw [(centeredCube z r hr).isOpen.interior_eq] at hxf
  exact killed_continuous_boundary_zero d z r hr w hw U hUc hUae x
    ((aux_conv_represented_source_clause_closure z r hr) ▸ hxf.1) hxf.2

/-- Interior local gradient bounds give energy-measure growth at every centre, with a factor
`A` depending only on the cube. -/
theorem aux_conv_represented_source_clause_growth {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (u : SobolevData (centeredCube z r hr))
        (t K Kh Kf : ℝ), 0 ≤ t → 0 ≤ Kf → K ≤ Kh → 0 ≤ Kh →
        (∀ x ∈ ((centeredCube z r hr : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
          ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
            localGradientEnergy a
              (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
              (Metric.isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
              (sobolevGradient u) ≤ K * (Kf + 0) ^ 2 * rad ^ t) →
        ∀ (x : SpatialCoordinates d) (rr : ℝ), 0 < rr → rr ≤ 1 →
          ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
            (fun y => ENNReal.ofReal (a.val y * ∑ i : Fin d, ((u.2 i) y) ^ 2)))
            (Metric.ball x rr) ≤ ENNReal.ofReal ((2 ^ t * A * (Kh * Kf ^ 2)) * rr ^ t) := by
  obtain ⟨A, hA1, hAgeom⟩ := gradient_energy_measure_growth_all_centres z r hr
  refine ⟨A, hA1, ?_⟩
  intro a u t K Kh Kf ht0 hKf hKK hKh hgrowth x rr hrr hrr1
  have hprodnn : 0 ≤ Kh * Kf ^ 2 := mul_nonneg hKh (sq_nonneg _)
  have hg' : ∀ x ∈ ((centeredCube z r hr : Opens (SpatialCoordinates d)) :
      Set (SpatialCoordinates d)), ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
      localGradientEnergy a (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
        (sobolevGradient u) ≤ (Kh * Kf ^ 2) * rho ^ t := by
    intro x hx rho hrho hrho1
    have h1 := hgrowth x hx rho hrho hrho1
    have hloc : localGradientEnergy a (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
        (sobolevGradient u) =
        localGradientEnergy a
          (s := Metric.ball x rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (Metric.isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
          (sobolevGradient u) := by
      rw [localGradientEnergy_eq_integral, localGradientEnergy_eq_integral]
      simp only [Measure.restrict_restrict Metric.isOpen_ball.measurableSet,
        Measure.restrict_restrict (Metric.isOpen_ball.measurableSet.inter
          (centeredCube z r hr).isOpen.measurableSet), Set.inter_assoc, Set.inter_self]
    rw [hloc]
    refine h1.trans ?_
    have hpow : 0 ≤ rho ^ t := Real.rpow_nonneg hrho.le t
    calc K * (Kf + 0) ^ 2 * rho ^ t = (K * Kf ^ 2) * rho ^ t := by ring
      _ ≤ (Kh * Kf ^ 2) * rho ^ t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKK (sq_nonneg _)) hpow
  exact hAgeom a (sobolevGradient u) (Kh * Kf ^ 2) t hprodnn ht0 hg' x rr hrr hrr1

/-- **Catalogue clause K (killed source solutions) from the actual growth theorem.**
For the killed source solution of any `L²` source `g` with a bounded representative `F`, on one
measurable full-measure event: the coefficient-weighted energy measure of every ball of radius at most
one (centres anywhere) is at most `Kg N β · Kf² · rr^t`, and the solution has a continuous
`C^α` representative vanishing on the frontier with `C^α`-norm at most `Kh N β · Kf`. The constants
`Kg`, `Kh` are measurable, nonnegative and have the first-moment bank. -/
theorem conv_represented_catalogue_source_clause
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (t alpha : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr))
        (_hS : S.space = killedSobolevGraph (centeredCube z r hr)),
      ∃ (Kg Kh : ℕ → BilateralField d → ℝ) (Cbg Cbh : ℝ) (G : Set (BilateralField d)),
        MeasurableSet G ∧ (chaosSampleLaw M).toMeasure Gᶜ = 0 ∧ 0 ≤ Cbg ∧ 0 ≤ Cbh ∧
        (∀ N, Measurable (Kg N)) ∧ (∀ N β, 0 ≤ Kg N β) ∧
        (∀ N, MemLp (Kg N) (ENNReal.ofReal 1) (chaosSampleLaw M).toMeasure ∧
          eLpNorm (Kg N) (ENNReal.ofReal 1) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal Cbg) ∧
        (∀ N, Measurable (Kh N)) ∧ (∀ N β, 0 ≤ Kh N β) ∧
        (∀ N, MemLp (Kh N) (ENNReal.ofReal 1) (chaosSampleLaw M).toMeasure ∧
          eLpNorm (Kh N) (ENNReal.ofReal 1) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal Cbh) ∧
        ∀ (N : ℕ), ∀ β ∈ G, ∀ (g : DomainL2 (centeredCube z r hr))
          (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
          AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
          ((g : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] F) →
          (∀ (x : SpatialCoordinates d) (rr : ℝ), 0 < rr → rr ≤ 1 →
            ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal
                ((Lane4.cutoffPositiveCoefficient M H β N z hr).val y *
                  ∑ i : Fin d, (((responseSolution S
                    (Lane4.cutoffPositiveCoefficient M H β N z hr)
                    ((sobolevVolumeLoad g).comp S.space.subtypeL)).val.2 i) y) ^ 2)))
              (Metric.ball x rr) ≤
            ENNReal.ofReal (Kg N β * Kf ^ 2 * rr ^ t)) ∧
          ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            (((responseSolution S (Lane4.cutoffPositiveCoefficient M H β N z hr)
                ((sobolevVolumeLoad g).comp S.space.subtypeL)).val.1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U) ∧
            (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0) ∧
            IsHolderOn alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d))) U ∧
            cAlphaNorm alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d))) U ≤
              Kh N β * Kf := by
  classical
  obtain ⟨δE, hδE, hE⟩ := prop_growth d hd I Pin X W Cp Sob t alpha 1 (fun _ => (1 : ℝ))
    ht htd ha ha1 (fun _ => le_rfl)
  obtain ⟨δL, hδL, hL⟩ := prop_growth_large_root d hd I Pin X W Cp Sob t alpha 1 (fun _ => (1 : ℝ))
    ht htd ha ha1 (fun _ => le_rfl)
  refine ⟨min δE δL, lt_min hδE hδL, ?_⟩
  intro M Rm Sreg It H hIR hδ z r hr S hS
  set P0 : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure with hP0
  obtain ⟨K, Cbound, hmem, hnorm, hge, hprop⟩ := (dite (r ≤ 1)
    (fun hr1 => hE M Rm Sreg It H hIR (hδ.trans (min_le_left _ _)) z r hr hr1)
    (fun hr1 => hL M Rm Sreg It H hIR (hδ.trans (min_le_right _ _)) z r hr
      (lt_of_not_ge hr1)))
  have ht0 : 0 ≤ t := by
    have : (1 : ℝ) < t := by
      have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    linarith
  obtain ⟨Kh, hKhm, hKhnn, hKle, hKhbank⟩ :=
    aux_conv_represented_source_clause_pos_majorant (μ := P0) K (fun N => hmem 0 N)
      (Cbound 0) (fun N => hnorm 0 N)
  obtain ⟨A, hA1, hGrowth⟩ := aux_conv_represented_source_clause_growth z r hr
  have hAnn : 0 ≤ 2 ^ t * A := mul_nonneg (Real.rpow_nonneg (by norm_num) t) (by linarith)
  have hev := (ae_all_iff.2 hKle).and (hge.and hprop)
  obtain ⟨G, hGm, hGnull, hGP⟩ := aux_conv_represented_source_clause_event hev
  refine ⟨fun N β => (2 ^ t * A) * Kh N β, Kh, (2 ^ t * A) * max (Cbound 0) 0, max (Cbound 0) 0, G,
    hGm, hGnull, mul_nonneg hAnn (le_max_right _ _), le_max_right _ _,
    fun N => (hKhm N).const_mul _, fun N β => mul_nonneg hAnn (hKhnn N β), fun N => ?_,
    hKhm, hKhnn, hKhbank, ?_⟩
  · refine ⟨(hKhbank N).1.const_mul _, ?_⟩
    calc eLpNorm (fun β => (2 ^ t * A) * Kh N β) (ENNReal.ofReal 1) P0
        ≤ ‖(2 ^ t * A : ℝ)‖ₑ * eLpNorm (Kh N) (ENNReal.ofReal 1) P0 := by
          simpa [Pi.smul_apply, smul_eq_mul] using
            (eLpNorm_const_smul_le (c := (2 ^ t * A : ℝ)) (f := Kh N) (p := ENNReal.ofReal 1)
              (μ := P0))
      _ ≤ ‖(2 ^ t * A : ℝ)‖ₑ * ENNReal.ofReal (max (Cbound 0) 0) :=
          mul_le_mul_right (hKhbank N).2 _
      _ = ENNReal.ofReal ((2 ^ t * A) * max (Cbound 0) 0) := by
          rw [Real.enorm_eq_ofReal hAnn]
          exact (ENNReal.ofReal_mul hAnn).symm
  · intro N β hβ g F Kf hKf hFm hFb hgF
    obtain ⟨hKleβ, hgeβ, hmainβ⟩ := hGP β hβ
    have hsolve := aux_conv_represented_source_clause_solves S hS
      (Lane4.cutoffPositiveCoefficient M H β N z hr) g F hgF
    have hb0 : ((((⟨0, zero_mem _⟩ : weakSobolevGraph (centeredCube z r hr)) :
        SobolevData (centeredCube z r hr)).1 : DomainL2 (centeredCube z r hr)) :
          SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))] (fun _ => (0 : ℝ)) := by
      simpa using (Lp.coeFn_zero ℝ 2
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    obtain ⟨hgrowth, U, hUc, hUae, hUh, hUn⟩ := hmainβ N F Kf hKf hFm hFb (fun _ => (0 : ℝ)) 0
      contDiff_const (aux_conv_represented_source_clause_c2Norm_zero _) _ _ hb0 hsolve
    have hkilled : ((responseSolution S (Lane4.cutoffPositiveCoefficient M H β N z hr)
        ((sobolevVolumeLoad g).comp S.space.subtypeL) : S.space) :
          SobolevData (centeredCube z r hr)) ∈ killedSobolevGraph (centeredCube z r hr) := by
      rw [← hS]; exact (responseSolution S (Lane4.cutoffPositiveCoefficient M H β N z hr)
        ((sobolevVolumeLoad g).comp S.space.subtypeL)).2
    have hKK : K N β ≤ Kh N β := hKleβ N
    refine ⟨?_, U, hUc, hUae, ?_, ?_, ?_⟩
    · intro x rr hrr hrr1
      have hm := hGrowth (Lane4.cutoffPositiveCoefficient M H β N z hr)
        ((responseSolution S (Lane4.cutoffPositiveCoefficient M H β N z hr)
          ((sobolevVolumeLoad g).comp S.space.subtypeL) : S.space) :
            SobolevData (centeredCube z r hr))
        t (K N β) (Kh N β) Kf ht0 hKf hKK (hKhnn N β)
        (fun x hx rad hrad hrad1 => hgrowth x rad hx hrad hrad1) x rr hrr hrr1
      refine hm.trans (le_of_eq ?_)
      congr 1
      ring
    · exact aux_conv_represented_source_clause_frontier z r hr _ hkilled U hUc hUae
    · rw [aux_conv_represented_source_clause_closure z r hr]; exact hUh
    · rw [aux_conv_represented_source_clause_closure z r hr]
      refine hUn.trans ?_
      calc K N β * (Kf + 0) = K N β * Kf := by ring
        _ ≤ Kh N β * Kf := mul_le_mul_of_nonneg_right hKK hKf

end Paper
