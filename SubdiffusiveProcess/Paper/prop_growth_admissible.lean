module

public import SubdiffusiveProcess.Paper.prop_growth_trunc_holder_assembly
public import SubdiffusiveProcess.Paper.prop_growth_trunc_energy_assembly
public import SubdiffusiveProcess.Paper.prop_growth_energy_assembly
public import SubdiffusiveProcess.Paper.prop_growth_holder_assembly
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

@[expose] public section

/-!
# Energy growth at all radii for every admissible infrared field

`mfd:prop-growth` for the characterized field and for every finite truncation `H_{L'}`,
`L' ≥ 0` (`H = 0` included), with one threshold fixed before the model.  `prop_growth` is the
characterized case.  Not claimed here: moment constants uniform in the model and the cube.
-/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Combine the energy and Hölder majorants into one random constant with
all prescribed moments and a common almost-sure domination event. -/
theorem aux_prop_growth_pair_majorant
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (k : ℕ) (ps : Fin k → ℝ) (hps : ∀ i, 1 ≤ ps i)
    (K₁ K₂ : ℕ → Ω → ℝ) (C₁ C₂ : Fin k → ℝ)
    (hmem₁ : ∀ i N, MemLp (K₁ N) (ENNReal.ofReal (ps i)) P)
    (hmem₂ : ∀ i N, MemLp (K₂ N) (ENNReal.ofReal (ps i)) P)
    (hnorm₁ : ∀ i N, eLpNorm (K₁ N) (ENNReal.ofReal (ps i)) P ≤
      ENNReal.ofReal (C₁ i))
    (hnorm₂ : ∀ i N, eLpNorm (K₂ N) (ENNReal.ofReal (ps i)) P ≤
      ENNReal.ofReal (C₂ i))
    (hge₁ : ∀ᵐ om ∂P, ∀ N, 1 ≤ K₁ N om)
    (hge₂ : ∀ᵐ om ∂P, ∀ N, 1 ≤ K₂ N om) :
    ∃ (K : ℕ → Ω → ℝ) (C : Fin k → ℝ),
      (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) P) ∧
      (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) P ≤
        ENNReal.ofReal (C i)) ∧
      (∀ᵐ om ∂P, ∀ N, 1 ≤ K N om ∧ K₁ N om ≤ K N om ∧ K₂ N om ≤ K N om) := by
  set K : ℕ → Ω → ℝ := fun N om => K₁ N om + K₂ N om with hK
  set C : Fin k → ℝ := fun i => max 0 (C₁ i) + max 0 (C₂ i) with hC
  have hp (i : Fin k) : 1 ≤ ENNReal.ofReal (ps i) :=
    ENNReal.one_le_ofReal.mpr (hps i)
  have h_ofReal_max (x : ℝ) : ENNReal.ofReal x = ENNReal.ofReal (max 0 x) := by
    simp [ENNReal.ofReal, Real.toNNReal, max_comm]
  refine ⟨K, C, ?_, ?_, ?_⟩
  · intro i N
    exact (hmem₁ i N).add (hmem₂ i N)
  · intro i N
    calc
      eLpNorm (K N) (ENNReal.ofReal (ps i)) P =
          eLpNorm (K₁ N + K₂ N) (ENNReal.ofReal (ps i)) P := rfl
      _ ≤ eLpNorm (K₁ N) (ENNReal.ofReal (ps i)) P +
            eLpNorm (K₂ N) (ENNReal.ofReal (ps i)) P :=
        eLpNorm_add_le (hp i)
      _ ≤ ENNReal.ofReal (C₁ i) + ENNReal.ofReal (C₂ i) :=
        add_le_add (hnorm₁ i N) (hnorm₂ i N)
      _ = ENNReal.ofReal (max 0 (C₁ i)) + ENNReal.ofReal (max 0 (C₂ i)) := by
        simp [h_ofReal_max]
      _ = ENNReal.ofReal (max 0 (C₁ i) + max 0 (C₂ i)) := by
        rw [ENNReal.ofReal_add (by simp) (by simp)]
      _ = ENNReal.ofReal (C i) := rfl
  · filter_upwards [hge₁, hge₂] with om hom₁ hom₂
    intro N
    have h1 : 1 ≤ K₁ N om := hom₁ N
    have h2 : 1 ≤ K₂ N om := hom₂ N
    dsimp [K]
    constructor
    · linarith
    constructor <;> linarith

/-- The concrete `C²` norm is nonnegative, including when its constituent
suprema are represented by real `sSup`. -/
theorem aux_prop_growth_c2Norm_nonneg
    {d : ℕ} (S : Set (SpatialCoordinates d))
    (phi : SpatialCoordinates d → ℝ) :
    0 ≤ c2Norm S phi := by
  unfold c2Norm
  have hA : 0 ≤ sSup {v : ℝ | ∃ x ∈ S, v = |phi x|} :=
    Real.sSup_nonneg (by rintro v ⟨x, _, rfl⟩; exact abs_nonneg _)
  have hB : 0 ≤ sSup {v : ℝ | ∃ x ∈ S, v = ‖fderiv ℝ phi x‖} :=
    Real.sSup_nonneg (by rintro v ⟨x, _, rfl⟩; exact norm_nonneg (fderiv ℝ phi x))
  have hC : 0 ≤ sSup {v : ℝ | ∃ x ∈ S, v = ‖fderiv ℝ (fderiv ℝ phi) x‖} := by
    apply Real.sSup_nonneg
    rintro v ⟨x, _, rfl⟩
    exact norm_nonneg (fderiv ℝ (fderiv ℝ phi) x)
  linarith

/-- The truncated half of `prop_growth_admissible`: the energy and Hölder assemblies at a
finite infrared truncation combined into one majorant. -/
theorem aux_prop_growth_admissible_trunc :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (_Cp : CampanatoInput d)
    (_S : SobolevFoundationalInput d hd) (t alpha : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < d → 0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (L0 : ℕ),
      H = (fun om' => infraredPartialSum om' L0) → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N, 1 ≤ K N om) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube z r hr →
            0 < rad → rad ≤ 1 →
            localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
                (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter
                  (centeredCube z r hr).isOpen.measurableSet)
                (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
              K N om * (Kf + Cphi) ^ 2 * rad ^ t) ∧
          (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
            IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
            cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
              K N om * (Kf + Cphi)) := by
  intro d hd _ _ E P X W Cp S t alpha k ps htlow hthi ha0 ha1 hps
  obtain ⟨δE, hδE, hE⟩ :=
    prop_growth_trunc_energy_assembly d hd E P X W Cp S t alpha k ps
      htlow hthi ha0 ha1 hps
  obtain ⟨δH, hδH, hH⟩ :=
    prop_growth_trunc_holder_assembly d hd E P X W Cp S t alpha k ps
      htlow hthi ha0 ha1 hps
  refine ⟨min δE δH, lt_min hδE hδH, ?_⟩
  intro M Rm H L0 hIR hδ z r hr hrle
  obtain ⟨KE, CE, hmemE, hnormE, hgeE, henergy⟩ :=
    hE M Rm H L0 hIR (hδ.trans (min_le_left _ _)) z r hr hrle
  obtain ⟨KH, CH, hmemH, hnormH, hgeH, hholder⟩ :=
    hH M Rm H L0 hIR (hδ.trans (min_le_right _ _)) z r hr hrle
  obtain ⟨K, C, hmem, hnorm, hdom⟩ :=
    aux_prop_growth_pair_majorant (chaosSampleLaw M).toMeasure k ps hps
      KE KH CE CH hmemE hmemH hnormE hnormH hgeE hgeH
  refine ⟨K, C, hmem, hnorm, ?_, ?_⟩
  · filter_upwards [hdom] with om hom
    intro N
    exact (hom N).1
  · filter_upwards [henergy, hholder, hdom] with om he hh hdK
    intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
    have hCphi0 : 0 ≤ Cphi :=
      (aux_prop_growth_c2Norm_nonneg (closedCube z r hr :
        Set (SpatialCoordinates d)) phi).trans hCphi
    have hdata0 : 0 ≤ Kf + Cphi := add_nonneg hKf hCphi0
    constructor
    · intro x rad hx hrad hrad1
      have hbase := he N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
        x rad hx hrad hrad1
      have hfactor : 0 ≤ (Kf + Cphi) ^ 2 * rad ^ t :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hrad.le _)
      calc
        _ ≤ KE N om * (Kf + Cphi) ^ 2 * rad ^ t := hbase
        _ = KE N om * ((Kf + Cphi) ^ 2 * rad ^ t) := by ring
        _ ≤ K N om * ((Kf + Cphi) ^ 2 * rad ^ t) :=
          mul_le_mul_of_nonneg_right (hdK N).2.1 hfactor
        _ = K N om * (Kf + Cphi) ^ 2 * rad ^ t := by ring
    · obtain ⟨U, hUcont, hUae, hUholder, hUnorm⟩ :=
        hh N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
      refine ⟨U, hUcont, hUae, hUholder, hUnorm.trans ?_⟩
      exact mul_le_mul_of_nonneg_right (hdK N).2.2 hdata0



/-- The genuine-field half of `prop_growth_admissible`: the energy and Hölder
assemblies combined into one majorant (the former proof of `prop_growth`). -/
theorem aux_prop_growth_admissible_genuine :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (_Cp : CampanatoInput d)
    (_S : SobolevFoundationalInput d hd) (t alpha : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < d → 0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N, 1 ≤ K N om) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube z r hr →
            0 < rad → rad ≤ 1 →
            localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
                (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter
                  (centeredCube z r hr).isOpen.measurableSet)
                (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
              K N om * (Kf + Cphi) ^ 2 * rad ^ t) ∧
          (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
            IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
            cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
              K N om * (Kf + Cphi)) := by
  intro d hd _ _ E P X W Cp S t alpha k ps htlow hthi ha0 ha1 hps
  obtain ⟨δE, hδE, hE⟩ :=
    prop_growth_energy_assembly d hd E P X W Cp S t alpha k ps
      htlow hthi ha0 ha1 hps
  obtain ⟨δH, hδH, hH⟩ :=
    prop_growth_holder_assembly d hd E P X W Cp S t alpha k ps
      htlow hthi ha0 ha1 hps
  refine ⟨min δE δH, lt_min hδE hδH, ?_⟩
  intro M Rm Sreg It H hIR hδ z r hr hrle
  obtain ⟨KE, CE, hmemE, hnormE, hgeE, henergy⟩ :=
    hE M Rm Sreg It H hIR (hδ.trans (min_le_left _ _)) z r hr hrle
  obtain ⟨KH, CH, hmemH, hnormH, hgeH, hholder⟩ :=
    hH M Rm Sreg It H hIR (hδ.trans (min_le_right _ _)) z r hr hrle
  obtain ⟨K, C, hmem, hnorm, hdom⟩ :=
    aux_prop_growth_pair_majorant (chaosSampleLaw M).toMeasure k ps hps
      KE KH CE CH hmemE hmemH hnormE hnormH hgeE hgeH
  refine ⟨K, C, hmem, hnorm, ?_, ?_⟩
  · filter_upwards [hdom] with om hom
    intro N
    exact (hom N).1
  · filter_upwards [henergy, hholder, hdom] with om he hh hdK
    intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
    have hCphi0 : 0 ≤ Cphi :=
      (aux_prop_growth_c2Norm_nonneg (closedCube z r hr :
        Set (SpatialCoordinates d)) phi).trans hCphi
    have hdata0 : 0 ≤ Kf + Cphi := add_nonneg hKf hCphi0
    constructor
    · intro x rad hx hrad hrad1
      have hbase := he N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
        x rad hx hrad hrad1
      have hfactor : 0 ≤ (Kf + Cphi) ^ 2 * rad ^ t :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hrad.le _)
      calc
        _ ≤ KE N om * (Kf + Cphi) ^ 2 * rad ^ t := hbase
        _ = KE N om * ((Kf + Cphi) ^ 2 * rad ^ t) := by ring
        _ ≤ K N om * ((Kf + Cphi) ^ 2 * rad ^ t) :=
          mul_le_mul_of_nonneg_right (hdK N).2.1 hfactor
        _ = K N om * (Kf + Cphi) ^ 2 * rad ^ t := by ring
    · obtain ⟨U, hUcont, hUae, hUholder, hUnorm⟩ :=
        hh N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
      refine ⟨U, hUcont, hUae, hUholder, hUnorm.trans ?_⟩
      exact mul_le_mul_of_nonneg_right (hdK N).2.2 hdata0


/-- `H = 0` is the zeroth infrared truncation. -/
theorem aux_prop_growth_admissible_zero {d : ℕ} :
    (fun _ : BilateralField d => (0 : C(SpatialCoordinates d, ℝ))) =
      fun om => infraredPartialSum om 0 := by
  funext om
  simp [infraredPartialSum]



theorem prop_growth_admissible :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (_Cp : CampanatoInput d)
    (_S : SobolevFoundationalInput d hd) (t alpha : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < d → 0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      (InfraredCharacterization M H ∨ ∃ L : ℕ, H = fun om => infraredPartialSum om L) →
      M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N, 1 ≤ K N om) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube z r hr →
            0 < rad → rad ≤ 1 →
            localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
                (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter
                  (centeredCube z r hr).isOpen.measurableSet)
                (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
              K N om * (Kf + Cphi) ^ 2 * rad ^ t) ∧
          (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
            IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
            cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
              K N om * (Kf + Cphi)) := by
  intro d hd _ _ E P X W Cp S t alpha k ps htlow hthi ha0 ha1 hps
  obtain ⟨δG, hδG, hG⟩ :=
    aux_prop_growth_admissible_genuine d hd E P X W Cp S t alpha k ps htlow hthi ha0 ha1 hps
  obtain ⟨δT, hδT, hT⟩ :=
    aux_prop_growth_admissible_trunc d hd E P X W Cp S t alpha k ps htlow hthi ha0 ha1 hps
  refine ⟨min δG δT, lt_min hδG hδT, ?_⟩
  intro M Rm Sreg It H hadm hδ z r hr hrle
  rcases hadm with hIR | ⟨L, hL⟩
  · exact hG M Rm Sreg It H hIR (hδ.trans (min_le_left _ _)) z r hr hrle
  · exact hT M Rm H L hL (hδ.trans (min_le_right _ _)) z r hr hrle

end Paper
