module

public import SubdiffusiveProcess.Paper.in_joint_extraction_killed_model
public import SubdiffusiveProcess.Paper.model_triadic_cube_coercivity
public import SubdiffusiveProcess.Probability.SubseqUniquenessInProbability
public import SubdiffusiveProcess.Lnorm.CutoffVolumeResponseMeasurability
public import SubdiffusiveProcess.Sobolev.CountableSmoothSources

@[expose] public section

/-!
# `in_killed_inverse_inprob`: full-sequence convergence in probability of the killed inverses

Step 4 of `mfd:prop-uniform-resolvent`  at the level of the operators
`G_N^Q` of the actual model, for the countable family of rational triadic cubes.  Every subsequence has a
further subsequence along which the killed inverses converge in operator norm almost surely, jointly for
all cubes (`in_joint_extraction_killed_model`); *if* any two such almost-sure limits agree almost surely
(the uniqueness of the subsequential limit, an explicit hypothesis `hUniq` whose exact form is the
conclusion of `conv_represented_thm_c1_uniqueness_actual` with its environment-form hypothesis
discharged), then the subsequence criterion
(`tendstoInMeasure_of_forall_strictMono_subseq_exists_subseq_ae`) gives convergence in probability of the whole
sequence to a measurable limit `G i`.

Nothing here proves uniqueness; that is a separate supplied input.
-/

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology ENNReal NNReal ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- **Full-sequence convergence in probability of the killed inverses, from uniqueness of the
subsequential limits.**  For the actual model, for a countable family of rational triadic cubes containing
every such cube, and assuming `hUniq` (equality almost surely of the almost-sure operator-norm limits of any
two cutoff subsequences), the killed inverses `G_N^i(ω)` converge in probability as `N → ∞` (full sequence, in
operator norm) to a measurable random operator `G i`. -/
theorem in_killed_inverse_inprob
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hInterp : CubeFractionalInterpolationInput d hd)
    (E : in_J d) (Pin : in_poincare d hd E) (X : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd)
    (hUniq : ∃ δU : ℝ, 0 < δU ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H),
        M.delta ≤ δU →
      ∀ (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ) (hR : ∀ i, 0 < R i)
        (Sspace : ∀ i, ResponseSpace (centeredCube (Z i) (R i) (hR i)))
        (_hS : ∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (Z i) (R i) (hR i)))
        (_hrat : ∀ i, (∀ c : Fin d, ∃ q : ℚ, Z i c = (q : ℝ)) ∧ ∃ m : ℤ, R i = (3 : ℝ) ^ m)
        (_hcomp : ∀ (z' : SpatialCoordinates d) (r' : ℝ), (∀ c : Fin d, ∃ q : ℚ, z' c = (q : ℝ)) →
          (∃ m : ℤ, r' = (3 : ℝ) ^ m) → ∃ i, Z i = z' ∧ R i = r')
        (NE NF : ℕ → ℕ), StrictMono NE → StrictMono NF →
      ∀ (GE0 GF0 : (i : ℕ) → BilateralField d →
          DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ]
            DomainL2 (centeredCube (Z i) (R i) (hR i))),
        (∀ᵐ β ∂(chaosSampleLaw M).toMeasure, ∀ i,
          Tendsto (fun n => volumeResponseOperator (Sspace i)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β (NE n) (Z i) (hR i))) atTop
            (𝓝 (GE0 i β))) →
        (∀ᵐ β ∂(chaosSampleLaw M).toMeasure, ∀ i,
          Tendsto (fun n => volumeResponseOperator (Sspace i)
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β (NF n) (Z i) (hR i))) atTop
            (𝓝 (GF0 i β))) →
        ∀ᵐ β ∂(chaosSampleLaw M).toMeasure, ∀ i, GE0 i β = GF0 i β) :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H),
        M.delta ≤ δ0 →
      ∀ (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ) (hR : ∀ i, 0 < R i)
        (Sspace : ∀ i, ResponseSpace (centeredCube (Z i) (R i) (hR i)))
        (_hS : ∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (Z i) (R i) (hR i)))
        (_hrat : ∀ i, (∀ c : Fin d, ∃ q : ℚ, Z i c = (q : ℝ)) ∧ ∃ m : ℤ, R i = (3 : ℝ) ^ m)
        (_hcomp : ∀ (z' : SpatialCoordinates d) (r' : ℝ), (∀ c : Fin d, ∃ q : ℚ, z' c = (q : ℝ)) →
          (∃ m : ℤ, r' = (3 : ℝ) ^ m) → ∃ i, Z i = z' ∧ R i = r'),
      ∃ G : (i : ℕ) → BilateralField d →
          DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ]
            DomainL2 (centeredCube (Z i) (R i) (hR i)),
        (∀ i, Measurable (G i)) ∧
        ∀ i, ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
          (chaosSampleLaw M).toMeasure {β | eps ≤
            ‖volumeResponseOperator (Sspace i)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β N (Z i) (hR i)) - G i β‖} ≤
            ENNReal.ofReal rho := by
  classical
  obtain ⟨δU, hδU, hU⟩ := hUniq
  obtain ⟨δ1, hδ1, hcoerc⟩ := model_triadic_cube_coercivity d hd E Pin Sob
  obtain ⟨δ2, hδ2, hext⟩ := in_joint_extraction_killed_model d hd E Pin X W Cp Sob hInterp
  refine ⟨min δU (min δ1 δ2), lt_min hδU (lt_min hδ1 hδ2), ?_⟩
  intro M Rm Sreg It H hH hδ Z R hR Sspace hS hrat hcomp
  have hδU' : M.delta ≤ δU := hδ.trans (min_le_left _ _)
  have hδ1' : M.delta ≤ δ1 := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ2' : M.delta ≤ δ2 := hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  have hrad : ∀ i, R i ≤ 1 ∨ ∃ k : ℕ, 0 < k ∧ R i = (3 : ℝ) ^ k := by
    intro i
    obtain ⟨m, hm⟩ := (hrat i).2
    by_cases hm0 : m ≤ 0
    · left
      rw [hm]
      exact zpow_le_one_of_nonpos₀ (by norm_num) hm0
    · right
      refine ⟨m.toNat, by omega, ?_⟩
      rw [hm, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]
  obtain ⟨Kc, Cb, hCb, hKcmeas, hKcnn, hcoer, hL1, htight⟩ :=
    hcoerc M Rm H hH hδ1' Z R hR hrad
  choose Dsub hDc hDd hDs using fun i =>
    SubdiffusiveProcess.SmoothSources.exists_countable_dense_smooth_submodule (Z i) (R i) (hR i)
  let D : (i : ℕ) → Set (DomainL2 (centeredCube (Z i) (R i) (hR i))) :=
    fun i => (Dsub i : Set _)
  have hDcount : ∀ i, Countable (D i) := fun i => (hDc i).to_subtype
  have hDadd : ∀ i, ∀ x ∈ D i, ∀ y ∈ D i, x + y ∈ D i :=
    fun i x hx y hy => (Dsub i).add_mem hx hy
  have hDsmooth : ∀ i, ∀ x ∈ D i, ∃ F : SpatialCoordinates d → ℝ,
      ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      tsupport F ⊆ (centeredCube (Z i) (R i) (hR i) : Set (SpatialCoordinates d)) ∧
      (x : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube (Z i) (R i) (hR i) : Set (SpatialCoordinates d))] F :=
    fun i x hx => hDs i ⟨x, hx⟩
  let GN : (i : ℕ) → ℕ → BilateralField d →
      DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ]
        DomainL2 (centeredCube (Z i) (R i) (hR i)) :=
    fun i N β => volumeResponseOperator (Sspace i)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β N (Z i) (hR i))
  have hGN : ∀ i N (om : BilateralField d) f, GN i N om f =
      (responseSolution (Sspace i)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (id om) N (Z i) (hR i))
        ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)).val.1 :=
    fun i N om f => volumeResponseOperator_apply _ _ _
  have hextract : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ (NE : ℕ → ℕ) (δE : ℕ → ℕ)
      (GE : (i : ℕ) → BilateralField d →
        DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ]
          DomainL2 (centeredCube (Z i) (R i) (hR i))),
      StrictMono NE ∧ StrictMono δE ∧ NE = ψ ∘ δE ∧
        ∀ᵐ β ∂P, ∀ i, Tendsto (fun n => GN i (NE n) β) atTop (𝓝 (GE i β)) := by
    intro ψ hψ
    obtain ⟨NE, NF, GE, GF, hNE, hNF, hcand, δE, δF, hδE, hδF, hNEeq, hNFeq⟩ :=
      hext M Rm Sreg It H hH hδ2' (BilateralField d) P id Z R hR Sspace GN D (fun i => hDd i) hDadd hDsmooth
        hGN Kc hcoer htight inferInstance measurable_id (Measure.map_id) hS ψ ψ hψ hψ
    obtain ⟨-, -, -, -, -, -, -, hae⟩ := hcand
    exact ⟨NE, δE, GE, hNE, hδE, hNEeq, hae.mono fun β h i => (h i).1⟩
  obtain ⟨NE1, δ1', GE1, hNE1, -, -, hae1⟩ := hextract id strictMono_id
  have hi : ∀ i, ∃ G0 : BilateralField d →
      DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ]
        DomainL2 (centeredCube (Z i) (R i) (hR i)),
      Measurable G0 ∧ ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
        P {β | eps ≤ ‖GN i N β - G0 β‖} ≤ ENNReal.ofReal rho := by
    intro i
    have hstr : ∀ n, StronglyMeasurable (GN i n) := fun n =>
      stronglyMeasurable_cutoffVolumeResponseOperator M H hH.1 n (Z i) (R i) (hR i) (Sspace i)
    have hR0 : AEStronglyMeasurable (GE1 i) P :=
      aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hstr (NE1 n)).aestronglyMeasurable)
        (hae1.mono fun β h => h i)
    have hdmeas : ∀ (m : ℕ) (eps : ℝ), 0 < eps →
        NullMeasurableSet {β | eps ≤ dist (GN i m β) (GE1 i β)} P := by
      intro m eps _
      have hf : AEMeasurable (fun β => ‖GN i m β - GE1 i β‖) P :=
        ((hstr m).aestronglyMeasurable.sub hR0).norm.aemeasurable
      have hset : {β | eps ≤ dist (GN i m β) (GE1 i β)} =
          (fun β => ‖GN i m β - GE1 i β‖) ⁻¹' Set.Ici eps := by
        ext β
        simp only [mem_ofPred_eq, Set.mem_preimage, Set.mem_Ici, dist_eq_norm]
      rw [hset]
      exact hf.nullMeasurableSet_preimage measurableSet_Ici
    have hsub : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧
        ∀ᵐ β ∂P, Tendsto (fun n => GN i (ψ (ψ' n)) β) atTop (𝓝 (GE1 i β)) := by
      intro ψ hψ
      obtain ⟨NE2, δE2, GE2, hNE2, hδE2, hNE2eq, hae2⟩ := hextract ψ hψ
      have huniq := hU M Rm Sreg It H hH hδU' Z R hR Sspace hS hrat hcomp NE1 NE2 hNE1 hNE2
        GE1 GE2 hae1 hae2
      subst hNE2eq
      refine ⟨δE2, hδE2, ?_⟩
      filter_upwards [hae2, huniq] with β hβ hu
      have h := hβ i
      rw [← hu i] at h
      exact h
    have hprob := SubdiffusiveProcess.Probability.tendstoInMeasure_of_forall_strictMono_subseq_exists_subseq_ae P
      (fun n β => GN i n β) (GE1 i) hdmeas hsub
    refine ⟨hR0.mk (GE1 i), hR0.stronglyMeasurable_mk.measurable, ?_⟩
    intro eps heps rho hrho
    obtain ⟨N0, hN0⟩ := hprob eps heps rho hrho
    refine ⟨N0, fun N hN => ?_⟩
    have hset : {β | eps ≤ ‖GN i N β - hR0.mk (GE1 i) β‖} =ᵐ[P]
        {β | eps ≤ dist (GN i N β) (GE1 i β)} := by
      filter_upwards [hR0.ae_eq_mk] with β hβ
      show (eps ≤ ‖GN i N β - hR0.mk (GE1 i) β‖) = (eps ≤ dist (GN i N β) (GE1 i β))
      rw [dist_eq_norm, hβ]
    rw [measure_congr hset]
    exact hN0 N hN
  choose G hGmeas hGprob using hi
  exact ⟨G, hGmeas, hGprob⟩

end SubdiffusiveProcess.Paper
