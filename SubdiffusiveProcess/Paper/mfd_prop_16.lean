module

public import SubdiffusiveProcess.Section9LiveRate.Exponents
public import SubdiffusiveProcess.Paper.prop_16
public import SubdiffusiveProcess.Paper.mfd_lem_15
public import SubdiffusiveProcess.Paper.inputs_J_witness

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity _root_.SubdiffusiveProcess.ResponseMoments

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_mfd_prop_16_dirichlet :
  ∀ (d : ℕ) (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (phi : SpatialCoordinates d → ℝ) (_hphi : ContDiff ℝ ∞ phi)
    (_hnonconst : ∃ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∃ y ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), phi x ≠ phi y)
    (b : weakSobolevGraph (centeredCube z r hr))
    (_hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (f : SpatialCoordinates d → ℝ) (_hf : ContDiff ℝ ∞ f)
    (_hfc : HasCompactSupport f)
    (_hfsupp : tsupport f ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (_hf0 : ∃ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), f x ≠ 0)
    (fL2 : DomainL2 (centeredCube z r hr))
    (_hfL2 : (fL2 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f)
    (t p B : ℝ) (_ht_lower : (d : ℝ) - 1 < t) (_ht_upper : t < (d : ℝ))
    (_hp : 2 ≤ p) (_hB : 0 ≤ B) (dirichlet : Bool),
    let S := killedResponseSpace hP
    let L := (sobolevVolumeLoad fL2).comp S.space.subtypeL
    ∃ C : ℝ, 0 < C ∧
      ∀ (delta : ℝ), 0 < delta → delta ≤ 1 →
        ∀ (Praw : ProbabilityMeasure (_root_.SubdiffusiveProcess.Model.PotentialSample d))
          (_G1 : _root_.SubdiffusiveProcess.Model.ShellLawG1 d Praw)
          (_G2 : _root_.SubdiffusiveProcess.Model.ShellLawG2 d delta Praw),
          let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d,
              C(SpatialCoordinates d, ℝ)) :=
            ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
          let nu := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw Praw).map
            forget
          let P := (commonScaleLaw d nu).toMeasure
          ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
            Measurable H →
            (∀ᵐ omega ∂P,
              Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega))) →
            ∀ (kappa : ℕ → ℝ), (∀ N, 0 < kappa N) →
            ∀ (aN : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr)),
              (∀ N omega,
                (aN N omega).val =ᵐ[volume.restrict
                  (centeredCube z r hr : Set (SpatialCoordinates d))]
                  (fun x => Real.exp (cutoffPotential H omega N x - Real.log (kappa N)))) →
            let RN : ℕ → BilateralField d → ℝ :=
            fun N omega =>
              if dirichlet then
                dirichletResponse S (aN N omega) b
              else
                inverseResponse S (aN N omega) L
          let gN : ℕ → BilateralField d → HilbertGradient (centeredCube z r hr) :=
            fun N omega =>
              if dirichlet then
                sobolevGradient (dirichletMinimizer S (aN N omega) b).val
              else
                subspaceGradient S.space (responseSolution S (aN N omega) L)
          ∀ (K : ℕ → BilateralField d → ℝ),
            ((∀ N, AEStronglyMeasurable (K N) P) ∧
            (∀ᵐ omega ∂P, ∀ N, 0 ≤ K N omega)) →
            (∀ᵐ omega ∂P, ∀ N, ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
              ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
                localGradientEnergy (aN N omega)
                  (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
                  (gN N omega) ≤ K N omega * rho ^ t) →
            (∀ N,
              MemLp (K N) (ENNReal.ofReal (3 * p)) P ∧
              MemLp (RN N) (ENNReal.ofReal (3 * p)) P ∧
              eLpNorm (K N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B ∧
              eLpNorm (RN N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
            (∀ h N : ℕ,
              let sigma_h := bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h
              eLpNorm
                (fun om => RN N om - (P[RN N | sigma_h]) om)
                (ENNReal.ofReal p) P ≤
              ENNReal.ofReal
                (C * delta *
                  (3 : ℝ) ^
                    (-(t * (t - (d : ℝ) + 1) / (t + 1) /
                        8) * (h : ℝ)))) ∧
            (∀ h N : ℕ, N < h →
              let sigma_h := bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h
              eLpNorm
                (fun om => RN N om - (P[RN N | sigma_h]) om)
                (ENNReal.ofReal p) P ≤
              ENNReal.ofReal
                (C * delta * (3 : ℝ) ^ (-(h : ℝ))))
    := by
  intro d hd instM instB z r hr hP phi hphi hnonconst b hb f hf hfc hfsupp hf0 fL2 hfL2
    t p B ht_lower ht_upper hp hB dirichlet S L
  have hES : EfronSteinMomentInequality := by
    constructor
    intro q hq
    obtain ⟨Cq, hCq, hqall⟩ := in_efron_stein aux_lem_15_bblm q hq
    refine ⟨Cq, hCq, ?_⟩
    intro m Xi instXi mu instMu X hX
    let := instXi
    let := instMu
    exact (hqall m Xi mu).1 X hX.aestronglyMeasurable hX
  obtain ⟨C15, hC15, h15⟩ := mfd_lem_15 hES d hd z r hr hP phi hphi hnonconst b hb
    f hf hfc hfsupp hf0 fL2 hfL2 t p B ht_lower ht_upper hp hB dirichlet
  obtain ⟨Ctail, hCtail, htail⟩ := aux_prop_16_coarse_tail d z r hr
  obtain ⟨Ccb, hCcb, hcb⟩ := prop_16_coarse_block_dirichlet d hd z r hr hP b fL2 t p B
    ht_lower ht_upper hp hB dirichlet Ctail hCtail
  obtain ⟨ha0, ha1⟩ := SubdiffusiveProcess.Section9LiveRate.influence_exponent_pos_le_one d hd t ht_lower ht_upper
  set a := t * (t - (d : ℝ) + 1) / (t + 1) / 8 with ha_def
  have hr1 : (3 : ℝ) ^ (-a) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h1r : 0 < 1 - (3 : ℝ) ^ (-a) := by linarith
  refine ⟨C15 / (1 - (3 : ℝ) ^ (-a)) + Ccb, by positivity, ?_⟩
  intro delta hdelta hdelta1 Praw G1 G2 forget nu P H hH hHconv kappa hkappa aN haN RN gN
    K hK hgrowth hmom
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ p)
  have hkey : ∀ h N : ℕ,
      eLpNorm (fun om => RN N om -
          (P[RN N | bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) om)
        (ENNReal.ofReal p) P ≤
      (∑ k ∈ Finset.Ioc h N,
          ENNReal.ofReal (C15 * delta * (3 : ℝ) ^ (-a * (k : ℝ)))) +
        ENNReal.ofReal (Ccb * delta * (3 : ℝ) ^ (-(h : ℝ))) := by
    intro h N
    have hRmem : MemLp (RN N) (ENNReal.ofReal (3 * p)) P := (hmom N).2.1
    have hRint : Integrable (RN N) P :=
      hRmem.integrable (by simpa using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ 3 * p))
    have hsplit := aux_prop_16_band_split
      (fun j : ℤ => (scaledLayerLaw d nu j : Measure C(SpatialCoordinates d, ℝ))) h hp1
      ENNReal.ofReal_ne_top hRint
    refine hsplit.trans ?_
    rw [add_comm]
    refine add_le_add ?_ ?_
    · have hdet : ∀ ω₁ ∈ {om : BilateralField d | Tendsto (infraredPartialSum om) atTop (𝓝 (H om))},
          ∀ ω₂ ∈ {om : BilateralField d | Tendsto (infraredPartialSum om) atTop (𝓝 (H om))},
          (∀ j : ℤ, -(N : ℤ) ≤ j → ω₁ j = ω₂ j) → RN N ω₁ = RN N ω₂ := by
        intro ω₁ h1 ω₂ h2 hagree
        have hH12 := aux_prop_16_infrared_eq H ω₁ ω₂ h1 h2 (fun j hj => hagree j (by omega))
        have hcut := aux_prop_16_cutoff_eq H ω₁ ω₂ N hH12 hagree
        have haeq : aN N ω₁ = aN N ω₂ := by
          apply Subtype.ext
          apply Lp.ext
          filter_upwards [haN N ω₁, haN N ω₂] with x hx1 hx2
          rw [hx1, hx2, hcut]
        simp only [RN, haeq]
      exact aux_prop_16_fine_telescope _ hp1 (RN N) hRmem.aestronglyMeasurable _ hHconv h N hdet
        (fun k => ENNReal.ofReal (C15 * delta * (3 : ℝ) ^ (-a * (k : ℝ))))
        (fun k _ hkN => h15 delta hdelta hdelta1 Praw G1 G2 H hH hHconv kappa hkappa aN haN
          K hK hgrowth hmom N k hkN)
    · have hcb' := hcb delta hdelta hdelta1 Praw G1 G2 H hH hHconv kappa hkappa aN haN
        (htail delta hdelta hdelta1 Praw G1 G2 H hH hHconv)
        (fun N => ⟨(hmom N).2.1, (hmom N).2.2.2⟩) h N
      have hTmp := measurePreserving_copy_infinitePi_block
        (fun j : ℤ => (scaledLayerLaw d nu j : Measure C(SpatialCoordinates d, ℝ)))
        {j : ℤ | (h : ℤ) < j}
      have hmeas : AEStronglyMeasurable (fun q : BilateralField d × BilateralField d =>
          RN N q.1 - RN N (fun j => if (h : ℤ) < j then q.2 j else q.1 j)) (P.prod P) :=
        (hRmem.aestronglyMeasurable.comp_measurePreserving measurePreserving_fst).sub
          (hRmem.aestronglyMeasurable.comp_measurePreserving hTmp)
      exact (eLpNorm_le_eLpNorm_of_exponent_le
        (ENNReal.ofReal_le_ofReal (by linarith))).trans hcb'
  refine ⟨fun h N => ?_, fun h N hNh => ?_⟩
  · refine (hkey h N).trans ?_
    have hg := aux_prop_16_geom a ha0 (C15 * delta) (by positivity) h N
    refine (add_le_add hg le_rfl).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h3 : (3 : ℝ) ^ (-(h : ℝ)) ≤ (3 : ℝ) ^ (-a * (h : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have : (0 : ℝ) ≤ h := Nat.cast_nonneg h
      nlinarith
    have h4 : 0 ≤ (3 : ℝ) ^ (-a * (h : ℝ)) := by positivity
    calc C15 * delta * (3 : ℝ) ^ (-a * (h : ℝ)) / (1 - (3 : ℝ) ^ (-a)) +
          Ccb * delta * (3 : ℝ) ^ (-(h : ℝ))
        ≤ C15 * delta * (3 : ℝ) ^ (-a * (h : ℝ)) / (1 - (3 : ℝ) ^ (-a)) +
          Ccb * delta * (3 : ℝ) ^ (-a * (h : ℝ)) := by gcongr
      _ = (C15 / (1 - (3 : ℝ) ^ (-a)) + Ccb) * delta * (3 : ℝ) ^ (-a * (h : ℝ)) := by
          field_simp
  · refine (hkey h N).trans ?_
    rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, zero_add]
    apply ENNReal.ofReal_le_ofReal
    have : 0 ≤ C15 / (1 - (3 : ℝ) ^ (-a)) := by positivity
    have h4 : 0 ≤ delta * (3 : ℝ) ^ (-(h : ℝ)) := by positivity
    nlinarith

theorem aux_mfd_prop_16_neumann_influence :
  ∀ (d : ℕ) (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (rho : ℝ → ℝ),
    ContDiff ℝ ∞ rho →
    (∀ tau, 0 ≤ rho tau) →
    (∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) →
    (∫ tau, rho tau) = 1 →
    ∀ (pvec : Fin d → ℝ),
      (∑ i : Fin d, (pvec i) ^ 2) = 1 →
    ∀ (hP : ∃ Kp : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
        ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
          Kp * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖),
      let Q := unitNeumannCube d
      let S := meanZeroResponseSpace hP
      let L0 : S.space →L[ℝ] ℝ :=
        (affineNeumannLoad pvec).comp (subspaceGradient (meanZeroSobolevGraph Q))
      ∀ (fL2 : ℝ → DomainL2 Q),
        (∀ eps : ℝ, (0 < eps ∧ eps < 1 / 8) →
          ((fL2 eps : SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (Q : Set (SpatialCoordinates d))]
            faceBump rho pvec eps)) →
        let Leps : ℝ → S.space →L[ℝ] ℝ := fun eps =>
          (sobolevVolumeLoad (fL2 eps)).comp S.space.subtypeL
        ∀ (t p B : ℝ),
          ((d : ℝ) - 1 < t ∧ t < (d : ℝ) ∧ 2 ≤ p ∧ 0 ≤ B) →
          ∃ C : ℝ, 0 < C ∧
            ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d),
              (0 < M.delta ∧ M.delta ≤ 1) →
              ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
                InfraredCharacterization M H →
                let P : Measure (BilateralField d) :=
                  (chaosSampleLaw M).toMeasure
                let aN : ℕ → BilateralField d → PositiveCoefficient Q := fun N om =>
                  cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos
                let yN : ℕ → BilateralField d → ℝ := fun N om =>
                  inverseResponse S (aN N om) L0
                let yeps : ℝ → ℕ → BilateralField d → ℝ := fun eps N om =>
                  inverseResponse S (aN N om) (Leps eps)
                let ueps : ℝ → ℕ → BilateralField d → S.space := fun eps N om =>
                  responseSolution S (aN N om) (Leps eps)
                ∀ (K : ℕ → BilateralField d → ℝ),
                  (∀ N, AEStronglyMeasurable (K N) P) →
                  (∀ᵐ om ∂P, ∀ N, 0 ≤ K N om) →
                  (∀ᵐ om ∂P,
                    ∀ (N : ℕ) (eps : ℝ),
                      (0 < eps ∧ eps < 1 / 8) →
                      ∀ (x : SpatialCoordinates d) (rad : ℝ),
                        x ∈ Q → (0 < rad ∧ rad ≤ 1) →
                        localGradientEnergy (aN N om)
                            (s := Metric.ball x rad ∩ (Q : Set (SpatialCoordinates d)))
                            (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
                            (subspaceGradient S.space (ueps eps N om)) ≤
                          K N om * eps ^ (-2 : ℝ) * rad ^ t) →
                  (∀ N,
                    MemLp (K N) (ENNReal.ofReal (3 * p)) P ∧
                      eLpNorm (K N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
                  (∀ N eps, (0 < eps ∧ eps < 1 / 8) →
                    MemLp (yeps eps N) (ENNReal.ofReal (3 * p)) P ∧
                      eLpNorm (yeps eps N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
                  (∀ N,
                    MemLp (yN N) (ENNReal.ofReal (4 * p)) P ∧
                      eLpNorm (yN N) (ENNReal.ofReal (4 * p)) P ≤ ENNReal.ofReal B) →
                  (∀ N eps, (0 < eps ∧ eps < 1 / 8) →
                    eLpNorm (fun om => yN N om - yeps eps N om)
                      (ENNReal.ofReal p) P ≤
                      ENNReal.ofReal (B * eps ^ (1 / 4 : ℝ))) →
                  ∀ (eps : ℝ), (0 < eps ∧ eps < 1 / 8) →
                    ∀ (N j : ℕ), j ≤ N →
                      eLpNorm
                        (fun pair : BilateralField d × BilateralField d =>
                          yeps eps N pair.1 -
                            yeps eps N
                              (Function.update pair.1 (-(j : ℤ))
                                (pair.2 (-(j : ℤ)))))
                        (ENNReal.ofReal p) (P.prod P) ≤
                        ENNReal.ofReal
                          (C * M.delta * eps ^ (-2 : ℝ) *
                            (3 : ℝ) ^
                              (-((t * (t - (d : ℝ) + 1) / (t + 1) /
                                8) * (j : ℝ)))) := by
  intro d hd _ _ rho _ _ _ _ pvec _ hP Q S L0 fL2 _ Leps t p B htpB
  obtain ⟨ht_lower, _, hp, hB⟩ := htpB
  obtain ⟨A, hA, hmain⟩ := aux_mfd_lem_15_uniform d hd (fun _ => (1 / 2 : ℝ)) 1 one_pos
    t p ht_lower hp
  refine ⟨A * B + 1, by positivity, ?_⟩
  intro M hMdelta H hH P aN yN yeps ueps K hKm hKnn hgrowth hKmom hyeps _ _ eps heps N j hjN
  have hc1 : 1 ≤ eps ^ (-2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos heps.1 (by linarith [heps.2]) (by norm_num)
  have hc0 : 0 ≤ eps ^ (-2 : ℝ) := zero_le_one.trans hc1
  have hK'm : ∀ N, AEStronglyMeasurable (fun om => K N om * eps ^ (-2 : ℝ)) P :=
    fun N => (hKm N).mul_const _
  have hK'nn : ∀ᵐ om ∂P, ∀ N, 0 ≤ K N om * eps ^ (-2 : ℝ) := by
    filter_upwards [hKnn] with om hom N
    exact mul_nonneg (hom N) hc0
  have hgrowth' : ∀ᵐ om ∂P, ∀ N, ∀ x ∈ (Q : Set (SpatialCoordinates d)),
      ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
        localGradientEnergy (aN N om)
          (s := Metric.ball x rad) Metric.isOpen_ball.measurableSet
          (aux_lem_15_u_grad S false 0 (Leps eps) (aN N om)) ≤
          K N om * eps ^ (-2 : ℝ) * rad ^ t := by
    filter_upwards [hgrowth] with om hom N x hx rad hrad0 hrad1
    have h := hom N eps heps x rad hx ⟨hrad0, hrad1⟩
    rw [aux_lem_neumann_15_localEnergy_inter (aN N om) Metric.isOpen_ball.measurableSet] at h
    exact h
  have hmomK : eLpNorm (fun om => K N om * eps ^ (-2 : ℝ)) (ENNReal.ofReal (3 * p)) P ≤
      ENNReal.ofReal (eps ^ (-2 : ℝ) * B) := by
    have hfun : (fun om => K N om * eps ^ (-2 : ℝ)) = eps ^ (-2 : ℝ) • K N := by
      funext om; simp [mul_comm]
    rw [hfun, eLpNorm_const_smul, Real.enorm_eq_ofReal hc0, ENNReal.ofReal_mul hc0]
    gcongr
    exact (hKmom N).2
  have hmomR : eLpNorm (fun om => aux_lem_15_u_resp S false 0 (Leps eps) (aN N om))
      (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal (eps ^ (-2 : ℝ) * B) := by
    refine ((hyeps N eps heps).2).trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith
  have hbound := hmain (eps ^ (-2 : ℝ) * B) (by positivity) S false 0 (Leps eps)
    M.delta hMdelta.1 hMdelta.2 M.P M.G1 M.G2 H hH.1 hH.2 (aux_lem_neumann_15_kappa M) aN
    (fun N om => aux_lem_neumann_15_coeff_ae M H om N _ one_pos)
    (fun N om => K N om * eps ^ (-2 : ℝ)) hK'm hK'nn hgrowth' N j hjN hmomK hmomR
  refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
  have hY : 0 ≤ (3 : ℝ) ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / 8) * (j : ℝ)) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  rw [show -((t * (t - (d : ℝ) + 1) / (t + 1) / 8) * (j : ℝ)) =
      -(t * (t - (d : ℝ) + 1) / (t + 1) / 8) * (j : ℝ) by ring]
  have hdel : 0 ≤ M.delta := hMdelta.1.le
  have hkey : A * (eps ^ (-2 : ℝ) * B) ≤ (A * B + 1) * eps ^ (-2 : ℝ) := by
    nlinarith
  calc A * (eps ^ (-2 : ℝ) * B) * M.delta *
        (3 : ℝ) ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / 8) * (j : ℝ))
      ≤ (A * B + 1) * eps ^ (-2 : ℝ) * M.delta *
        (3 : ℝ) ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / 8) * (j : ℝ)) := by
        gcongr
    _ = (A * B + 1) * M.delta * eps ^ (-2 : ℝ) *
        (3 : ℝ) ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / 8) * (j : ℝ)) := by
        ring

theorem aux_mfd_prop_16_neumann :
  ∀ (d : ℕ) (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (_I : _root_.SubdiffusiveProcess.Paper.in_J d) (Cresp : ℝ) (_hCresp : 0 < Cresp)
    (rho : ℝ → ℝ),
    ContDiff ℝ ∞ rho →
    (∀ tau, 0 ≤ rho tau) →
    (∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) →
    (∫ tau, rho tau) = 1 →
    ∀ (pvec : Fin d → ℝ),
      (∑ i : Fin d, (pvec i) ^ 2) = 1 →
    ∀ (hP : ∃ Kp : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
        ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
          Kp * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖),
      let Q := unitNeumannCube d
      let S := meanZeroResponseSpace hP
      let L0 : S.space →L[ℝ] ℝ :=
        (affineNeumannLoad pvec).comp (subspaceGradient (meanZeroSobolevGraph Q))
      ∀ (fL2 : ℝ → DomainL2 Q),
        (∀ eps : ℝ, (0 < eps ∧ eps < 1 / 8) →
          ((fL2 eps : SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (Q : Set (SpatialCoordinates d))]
            faceBump rho pvec eps)) →
        let Leps : ℝ → S.space →L[ℝ] ℝ := fun eps =>
          (sobolevVolumeLoad (fL2 eps)).comp S.space.subtypeL
        ∀ (t p B : ℝ),
          ((d : ℝ) - 1 < t ∧ t < (d : ℝ) ∧ 2 ≤ p ∧ 0 ≤ B) →
          ∃ delta0 C : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧ 0 < C ∧
            ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d),
              (0 < M.delta ∧ M.delta ≤ delta0) →
              ∀ (Rinput : _root_.SubdiffusiveProcess.Paper.in_responses d M),
                Rinput.C ≤ Cresp →
                4 * p ≤ Cresp⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
                ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
                InfraredCharacterization M H →
                let P : Measure (BilateralField d) :=
                  (chaosSampleLaw M).toMeasure
                let aN : ℕ → BilateralField d → PositiveCoefficient Q := fun N om =>
                  cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos
                let yN : ℕ → BilateralField d → ℝ := fun N om =>
                  inverseResponse S (aN N om) L0
                let yeps : ℝ → ℕ → BilateralField d → ℝ := fun eps N om =>
                  inverseResponse S (aN N om) (Leps eps)
                let ueps : ℝ → ℕ → BilateralField d → S.space := fun eps N om =>
                  responseSolution S (aN N om) (Leps eps)
                ∀ (K : ℕ → BilateralField d → ℝ),
                  (∀ N, AEStronglyMeasurable (K N) P) →
                  (∀ᵐ om ∂P, ∀ N, 0 ≤ K N om) →
                  (∀ᵐ om ∂P,
                    ∀ (N : ℕ) (eps : ℝ),
                      (0 < eps ∧ eps < 1 / 8) →
                      ∀ (x : SpatialCoordinates d) (rad : ℝ),
                        x ∈ Q → (0 < rad ∧ rad ≤ 1) →
                        localGradientEnergy (aN N om)
                            (s := Metric.ball x rad ∩ (Q : Set (SpatialCoordinates d)))
                            (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
                            (subspaceGradient S.space (ueps eps N om)) ≤
                          K N om * eps ^ (-2 : ℝ) * rad ^ t) →
                  (∀ N,
                    MemLp (K N) (ENNReal.ofReal (3 * p)) P ∧
                      eLpNorm (K N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
                  (∀ N eps, (0 < eps ∧ eps < 1 / 8) →
                    MemLp (yeps eps N) (ENNReal.ofReal (3 * p)) P ∧
                      eLpNorm (yeps eps N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
                  (∀ N,
                    MemLp (yN N) (ENNReal.ofReal (4 * p)) P ∧
                      eLpNorm (yN N) (ENNReal.ofReal (4 * p)) P ≤ ENNReal.ofReal B) →
                  (∀ N eps, (0 < eps ∧ eps < 1 / 8) →
                    eLpNorm (fun om => yN N om - yeps eps N om)
                      (ENNReal.ofReal p) P ≤
                      ENNReal.ofReal (B * eps ^ (1 / 4 : ℝ))) →
                  (∀ h N : ℕ,
                    let sigma_h := bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h
                    eLpNorm
                      (fun om => yN N om - (P[yN N | sigma_h]) om)
                      (ENNReal.ofReal p) P ≤
                    ENNReal.ofReal
                      (C * Real.sqrt M.delta *
                        (3 : ℝ) ^
                          (-((t * (t - (d : ℝ) + 1) / (t + 1) /
                              8 / 32) * (h : ℝ))))) ∧
                  (∀ h N : ℕ, N < h →
                    let sigma_h := bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h
                    eLpNorm
                      (fun om => yN N om - (P[yN N | sigma_h]) om)
                      (ENNReal.ofReal p) P ≤
                    ENNReal.ofReal
                      (C * M.delta * (3 : ℝ) ^ (-(h : ℝ))))
    := by
  intro d hd instM instB I Cresp hCresp rho hrho1 hrho2 hrho3 hrho4 pvec hpvec hP Q S L0
    fL2 hfL2 Leps t p B htpB
  obtain ⟨ht_lower, ht_upper, hp, hB⟩ := htpB
  obtain ⟨Cn, hCn, hn15⟩ := aux_mfd_prop_16_neumann_influence d hd rho hrho1 hrho2 hrho3 hrho4 pvec hpvec hP
    fL2 hfL2 t p B ⟨ht_lower, ht_upper, hp, hB⟩
  obtain ⟨Ccn, hCcn, hcbn⟩ := prop_16_coarse_block_neumann d hd Cresp hCresp pvec hpvec hP
    p B hp hB
  obtain ⟨delta0, Cc, hdelta0, hdelta01, hCc, hcent⟩ :=
    neumann_centered_response d hd I Cresp hCresp p hp pvec hpvec hP
  obtain ⟨ha0, ha1⟩ := SubdiffusiveProcess.Section9LiveRate.influence_exponent_pos_le_one d hd t ht_lower ht_upper
  set a := t * (t - (d : ℝ) + 1) / (t + 1) / 8 with ha_def
  have hr1 : (3 : ℝ) ^ (-a) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h1r : 0 < 1 - (3 : ℝ) ^ (-a) := by linarith
  refine ⟨delta0, Real.sqrt (4 * (Ccn + 2 * B + Cn / (1 - (3 : ℝ) ^ (-a))) * Cc) + 8 * Cc +
    Ccn + 1, hdelta0, hdelta01, by positivity, ?_⟩
  intro M hM Rinput hRC hscale H hH P aN yN yeps ueps K hKm hK0 hgrowth hKmom hyeps hyN
    hsmooth
  obtain ⟨hδ0, hδ⟩ := hM
  have hδ1 : M.delta ≤ 1 := hδ.trans hdelta01
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ p)
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) := fun j =>
    (scaledLayerLaw d (chaosRootFieldLaw M) j : Measure C(SpatialCoordinates d, ℝ))
  have hc := hcent M ⟨hδ0, hδ⟩ Rinput hRC hscale H hH (fun N => aux_prop_16_relab N)
    (fun N => aux_prop_16_relab_mp M N)
    (ae_of_all _ fun om N i x => aux_prop_16_relab_apply N om i x)
  let G : Set (BilateralField d) :=
    {om | Tendsto (infraredPartialSum om) atTop (𝓝 (H om))}
  have hG : ∀ᵐ om ∂(Measure.infinitePi laws), om ∈ G := hH.2
  have hdetA : ∀ N : ℕ, ∀ ω₁ ∈ G, ∀ ω₂ ∈ G, (∀ j : ℤ, -(N : ℤ) ≤ j → ω₁ j = ω₂ j) →
      aN N ω₁ = aN N ω₂ := by
    intro N ω₁ h1 ω₂ h2 hagree
    have hH12 := aux_prop_16_infrared_eq H ω₁ ω₂ h1 h2 (fun j hj => hagree j (by omega))
    exact aux_prop_16_cpc_eq M H ω₁ ω₂ N _ one_pos
      (aux_prop_16_cutoff_eq H ω₁ ω₂ N hH12 hagree)
  have hdetN : ∀ N : ℕ, ∀ ω₁ ∈ G, ∀ ω₂ ∈ G, (∀ j : ℤ, -(N : ℤ) ≤ j → ω₁ j = ω₂ j) →
      yN N ω₁ = yN N ω₂ := by
    intro N ω₁ h1 ω₂ h2 hagree
    show inverseResponse S (aN N ω₁) L0 = inverseResponse S (aN N ω₂) L0
    rw [hdetA N ω₁ h1 ω₂ h2 hagree]
  have hyNm : ∀ N, AEStronglyMeasurable (yN N) (Measure.infinitePi laws) := fun N =>
    (hyN N).1.aestronglyMeasurable
  have hyNint : ∀ N, Integrable (yN N) (Measure.infinitePi laws) := fun N =>
    (hyN N).1.integrable (by
      simpa using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ 4 * p))
  have hFCmp : ∀ h : ℕ, MeasurePreserving
      (fun q : BilateralField d × BilateralField d => fun j =>
        if j < -(h : ℤ) then q.2 j else q.1 j)
      ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) (Measure.infinitePi laws) :=
    fun h => measurePreserving_copy_infinitePi_block laws {j : ℤ | j < -(h : ℤ)}
  have hCCmp : ∀ h : ℕ, MeasurePreserving
      (fun q : BilateralField d × BilateralField d => fun j =>
        if (h : ℤ) < j then q.2 j else q.1 j)
      ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) (Measure.infinitePi laws) :=
    fun h => measurePreserving_copy_infinitePi_block laws {j : ℤ | (h : ℤ) < j}
  have hcoarse : ∀ h N : ℕ,
      eLpNorm (fun q : BilateralField d × BilateralField d =>
          yN N q.1 - yN N (fun j => if (h : ℤ) < j then q.2 j else q.1 j))
        (ENNReal.ofReal p) ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) ≤
      ENNReal.ofReal (Ccn * M.delta * (3 : ℝ) ^ (-(h : ℝ))) := by
    intro h N
    have hmeas : AEStronglyMeasurable (fun q : BilateralField d × BilateralField d =>
        yN N q.1 - yN N (fun j => if (h : ℤ) < j then q.2 j else q.1 j))
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) :=
      ((hyNm N).comp_measurePreserving measurePreserving_fst).sub
        ((hyNm N).comp_measurePreserving (hCCmp h))
    exact (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (by linarith))).trans (hcbn M ⟨hδ0, hδ1⟩ Rinput hRC hscale H hH hyN h N)
  have hfine0 : ∀ h N : ℕ, N ≤ h →
      eLpNorm (fun q : BilateralField d × BilateralField d =>
          yN N q.1 - yN N (fun j => if j < -(h : ℤ) then q.2 j else q.1 j))
        (ENNReal.ofReal p) ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) ≤ 0 := by
    intro h N hNh
    have htel := aux_prop_16_fine_telescope laws hp1 (yN N) (hyNm N) G hG h N (hdetN N)
      (fun _ => 0) (fun k hk hkN => absurd (lt_of_lt_of_le hk hkN) (by omega))
    simpa using htel
  have hfine : ∀ h N : ℕ, ∀ ε : ℝ, 0 < ε ∧ ε < 1 / 8 →
      eLpNorm (fun q : BilateralField d × BilateralField d =>
          yN N q.1 - yN N (fun j => if j < -(h : ℤ) then q.2 j else q.1 j))
        (ENNReal.ofReal p) ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) ≤
      ENNReal.ofReal (2 * B * ε ^ (1 / 4 : ℝ) + Cn * M.delta * ε ^ (-2 : ℝ) *
        (3 : ℝ) ^ (-a * (h : ℝ)) / (1 - (3 : ℝ) ^ (-a))) := by
    intro h N ε hε
    have hyem : AEStronglyMeasurable (yeps ε N) (Measure.infinitePi laws) :=
      (hyeps N ε hε).1.aestronglyMeasurable
    have hdiff : eLpNorm (fun om => yN N om - yeps ε N om) (ENNReal.ofReal p)
        (Measure.infinitePi laws) ≤ ENNReal.ofReal (B * ε ^ (1 / 4 : ℝ)) := hsmooth N ε hε
    have hdetE : ∀ ω₁ ∈ G, ∀ ω₂ ∈ G, (∀ j : ℤ, -(N : ℤ) ≤ j → ω₁ j = ω₂ j) →
        yeps ε N ω₁ = yeps ε N ω₂ := by
      intro ω₁ h1 ω₂ h2 hagree
      show inverseResponse S (aN N ω₁) (Leps ε) = inverseResponse S (aN N ω₂) (Leps ε)
      rw [hdetA N ω₁ h1 ω₂ h2 hagree]
    have htel := aux_prop_16_fine_telescope laws hp1 (yeps ε N) hyem G hG h N hdetE
      (fun k => ENNReal.ofReal (Cn * M.delta * ε ^ (-2 : ℝ) * (3 : ℝ) ^ (-(a * (k : ℝ)))))
      (fun k _ hkN => hn15 M ⟨hδ0, hδ1⟩ H hH K hKm hK0 hgrowth hKmom hyeps hyN hsmooth
        ε hε N k hkN)
    have hgeo := aux_prop_16_geom_neg a ha0 (Cn * M.delta * ε ^ (-2 : ℝ))
      (by have : 0 ≤ ε ^ (-2 : ℝ) := Real.rpow_nonneg hε.1.le _; positivity) h N
    let FC : BilateralField d × BilateralField d → BilateralField d := fun q j =>
      if j < -(h : ℤ) then q.2 j else q.1 j
    have m1 : AEStronglyMeasurable (fun q : BilateralField d × BilateralField d =>
        yN N q.1 - yeps ε N q.1)
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) :=
      ((hyNm N).sub hyem).comp_measurePreserving measurePreserving_fst
    have m2 : AEStronglyMeasurable (fun q : BilateralField d × BilateralField d =>
        yeps ε N q.1 - yeps ε N (FC q))
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) :=
      (hyem.comp_measurePreserving measurePreserving_fst).sub
        (hyem.comp_measurePreserving (hFCmp h))
    have m3 : AEStronglyMeasurable (fun q : BilateralField d × BilateralField d =>
        yN N (FC q) - yeps ε N (FC q))
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) :=
      ((hyNm N).sub hyem).comp_measurePreserving (hFCmp h)
    have hsplit : (fun q : BilateralField d × BilateralField d => yN N q.1 - yN N (FC q)) =
        ((fun q => yN N q.1 - yeps ε N q.1) + (fun q => yeps ε N q.1 - yeps ε N (FC q))) -
          (fun q => yN N (FC q) - yeps ε N (FC q)) := by
      funext q
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    change eLpNorm (fun q : BilateralField d × BilateralField d => yN N q.1 - yN N (FC q))
      (ENNReal.ofReal p) ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) ≤ _
    rw [hsplit]
    refine (eLpNorm_sub_le hp1).trans ?_
    refine (add_le_add (eLpNorm_add_le hp1) le_rfl).trans ?_
    let gd : BilateralField d → ℝ := fun om => yN N om - yeps ε N om
    have hgd : AEStronglyMeasurable gd (Measure.infinitePi laws) := (hyNm N).sub hyem
    have e1 := aux_prop_16_eLpNorm_mp (ENNReal.ofReal p) Prod.fst
      (measurePreserving_fst : MeasurePreserving Prod.fst
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) (Measure.infinitePi laws))
      gd hgd
    have e3 := aux_prop_16_eLpNorm_mp (ENNReal.ofReal p) FC (hFCmp h) gd hgd
    change eLpNorm (fun q : BilateralField d × BilateralField d => gd q.1)
        (ENNReal.ofReal p) ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) +
      eLpNorm (fun q : BilateralField d × BilateralField d =>
        yeps ε N q.1 - yeps ε N (FC q)) (ENNReal.ofReal p)
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) +
      eLpNorm (fun q : BilateralField d × BilateralField d => gd (FC q))
        (ENNReal.ofReal p) ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) ≤ _
    rw [e1, e3]
    have hB0 : 0 ≤ B * ε ^ (1 / 4 : ℝ) := by
      have : 0 ≤ ε ^ (1 / 4 : ℝ) := Real.rpow_nonneg hε.1.le _
      positivity
    have hF0 : 0 ≤ Cn * M.delta * ε ^ (-2 : ℝ) * (3 : ℝ) ^ (-a * (h : ℝ)) /
        (1 - (3 : ℝ) ^ (-a)) := by
      have : 0 ≤ ε ^ (-2 : ℝ) := Real.rpow_nonneg hε.1.le _
      positivity
    calc eLpNorm (fun om => yN N om - yeps ε N om) (ENNReal.ofReal p) (Measure.infinitePi laws) +
          eLpNorm (fun q : BilateralField d × BilateralField d =>
            yeps ε N q.1 - yeps ε N (FC q)) (ENNReal.ofReal p)
            ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) +
          eLpNorm (fun om => yN N om - yeps ε N om) (ENNReal.ofReal p) (Measure.infinitePi laws)
        ≤ ENNReal.ofReal (B * ε ^ (1 / 4 : ℝ)) +
            ENNReal.ofReal (Cn * M.delta * ε ^ (-2 : ℝ) * (3 : ℝ) ^ (-a * (h : ℝ)) /
              (1 - (3 : ℝ) ^ (-a))) +
            ENNReal.ofReal (B * ε ^ (1 / 4 : ℝ)) :=
          add_le_add (add_le_add hdiff (htel.trans hgeo)) hdiff
      _ = ENNReal.ofReal (2 * B * ε ^ (1 / 4 : ℝ) + Cn * M.delta * ε ^ (-2 : ℝ) *
            (3 : ℝ) ^ (-a * (h : ℝ)) / (1 - (3 : ℝ) ^ (-a))) := by
          rw [← ENNReal.ofReal_add hB0 hF0, ← ENNReal.ofReal_add (by positivity) hB0]
          congr 1
          ring
  have hcentE : ∀ h N : ℕ,
      eLpNorm (fun om => yN N om -
          ((Measure.infinitePi laws)[yN N | bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ))
            h]) om) (ENNReal.ofReal p) (Measure.infinitePi laws) ≤
        ENNReal.ofReal (4 * Cc * M.delta) := by
    intro h N
    have hcN := (hc N).2.2.2.2
    refine (aux_prop_16_band_split laws h hp1 ENNReal.ofReal_ne_top (hyNint N)).trans ?_
    have c1 := aux_prop_16_copy_centered laws hp1 (yN N) (hyNm N) _ (hCCmp h)
      (∫ om, yN N om ∂(Measure.infinitePi laws))
    have c2 := aux_prop_16_copy_centered laws hp1 (yN N) (hyNm N) _ (hFCmp h)
      (∫ om, yN N om ∂(Measure.infinitePi laws))
    have hx : 0 ≤ Cc * M.delta := by positivity
    calc _ ≤ 2 * eLpNorm (fun om => yN N om - ∫ om, yN N om ∂(Measure.infinitePi laws))
            (ENNReal.ofReal p) (Measure.infinitePi laws) +
          2 * eLpNorm (fun om => yN N om - ∫ om, yN N om ∂(Measure.infinitePi laws))
            (ENNReal.ofReal p) (Measure.infinitePi laws) := add_le_add c1 c2
      _ ≤ 2 * ENNReal.ofReal (Cc * M.delta) + 2 * ENNReal.ofReal (Cc * M.delta) := by
          gcongr <;> exact hcN
      _ = ENNReal.ofReal (4 * Cc * M.delta) := by
          rw [two_mul, ← ENNReal.ofReal_add hx hx, ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
          congr 1
          ring
  refine ⟨fun h N => ?_, fun h N hNh => ?_⟩
  · have hE1 : ∀ ε : ℝ, 0 < ε ∧ ε < 1 / 8 →
        eLpNorm (fun om => yN N om -
          ((Measure.infinitePi laws)[yN N | bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ))
            h]) om) (ENNReal.ofReal p) (Measure.infinitePi laws) ≤
        ENNReal.ofReal (Ccn * M.delta * (3 : ℝ) ^ (-(h : ℝ)) + 2 * B * ε ^ (1 / 4 : ℝ) +
          Cn * M.delta * ε ^ (-2 : ℝ) * (3 : ℝ) ^ (-a * (h : ℝ)) / (1 - (3 : ℝ) ^ (-a))) := by
      intro ε hε
      refine (aux_prop_16_band_split laws h hp1 ENNReal.ofReal_ne_top (hyNint N)).trans ?_
      refine (add_le_add (hcoarse h N) (hfine h N ε hε)).trans ?_
      have hF0 : 0 ≤ 2 * B * ε ^ (1 / 4 : ℝ) + Cn * M.delta * ε ^ (-2 : ℝ) *
          (3 : ℝ) ^ (-a * (h : ℝ)) / (1 - (3 : ℝ) ^ (-a)) := by
        have : 0 ≤ ε ^ (-2 : ℝ) := Real.rpow_nonneg hε.1.le _
        have : 0 ≤ ε ^ (1 / 4 : ℝ) := Real.rpow_nonneg hε.1.le _
        positivity
      rw [← ENNReal.ofReal_add (by positivity) hF0]
      apply ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
    have hnum := aux_prop_16_neumann_numeric a ha0 ha1 h M.delta hδ0 hδ1 Ccn B Cn Cc hCcn.le hB
      hCn.le hCc.le _ hE1 (hcentE h N)
    refine hnum.trans (ENNReal.ofReal_le_ofReal ?_)
    have hsd : 0 ≤ Real.sqrt M.delta := Real.sqrt_nonneg _
    have he : 0 ≤ (3 : ℝ) ^ (-((a / 32) * (h : ℝ))) := by positivity
    apply mul_le_mul_of_nonneg_right _ he
    apply mul_le_mul_of_nonneg_right _ hsd
    linarith
  · refine (aux_prop_16_band_split laws h hp1 ENNReal.ofReal_ne_top (hyNint N)).trans ?_
    refine (add_le_add (hcoarse h N) (hfine0 h N hNh.le)).trans ?_
    rw [add_zero]
    apply ENNReal.ofReal_le_ofReal
    have h2 : 0 ≤ Real.sqrt (4 * (Ccn + 2 * B + Cn / (1 - (3 : ℝ) ^ (-a))) * Cc) + 8 * Cc := by
      positivity
    have he : 0 ≤ (3 : ℝ) ^ (-(h : ℝ)) := by positivity
    apply mul_le_mul_of_nonneg_right _ he
    apply mul_le_mul_of_nonneg_right _ hδ0.le
    linarith

theorem mfd_prop_16 :
  (∀ (d : ℕ) (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (phi : SpatialCoordinates d → ℝ) (_hphi : ContDiff ℝ ∞ phi)
    (_hnonconst : ∃ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∃ y ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), phi x ≠ phi y)
    (b : weakSobolevGraph (centeredCube z r hr))
    (_hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (f : SpatialCoordinates d → ℝ) (_hf : ContDiff ℝ ∞ f)
    (_hfc : HasCompactSupport f)
    (_hfsupp : tsupport f ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (_hf0 : ∃ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), f x ≠ 0)
    (fL2 : DomainL2 (centeredCube z r hr))
    (_hfL2 : (fL2 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f)
    (t p B : ℝ) (_ht_lower : (d : ℝ) - 1 < t) (_ht_upper : t < (d : ℝ))
    (_hp : 2 ≤ p) (_hB : 0 ≤ B) (dirichlet : Bool),
    let S := killedResponseSpace hP
    let L := (sobolevVolumeLoad fL2).comp S.space.subtypeL
    ∃ C : ℝ, 0 < C ∧
      ∀ (delta : ℝ), 0 < delta → delta ≤ 1 →
        ∀ (Praw : ProbabilityMeasure (_root_.SubdiffusiveProcess.Model.PotentialSample d))
          (_G1 : _root_.SubdiffusiveProcess.Model.ShellLawG1 d Praw)
          (_G2 : _root_.SubdiffusiveProcess.Model.ShellLawG2 d delta Praw),
          let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d,
              C(SpatialCoordinates d, ℝ)) :=
            ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
          let nu := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw Praw).map
            forget
          let P := (commonScaleLaw d nu).toMeasure
          ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
            Measurable H →
            (∀ᵐ omega ∂P,
              Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega))) →
            ∀ (kappa : ℕ → ℝ), (∀ N, 0 < kappa N) →
            ∀ (aN : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr)),
              (∀ N omega,
                (aN N omega).val =ᵐ[volume.restrict
                  (centeredCube z r hr : Set (SpatialCoordinates d))]
                  (fun x => Real.exp (cutoffPotential H omega N x - Real.log (kappa N)))) →
            let RN : ℕ → BilateralField d → ℝ :=
            fun N omega =>
              if dirichlet then
                dirichletResponse S (aN N omega) b
              else
                inverseResponse S (aN N omega) L
          let gN : ℕ → BilateralField d → HilbertGradient (centeredCube z r hr) :=
            fun N omega =>
              if dirichlet then
                sobolevGradient (dirichletMinimizer S (aN N omega) b).val
              else
                subspaceGradient S.space (responseSolution S (aN N omega) L)
          ∀ (K : ℕ → BilateralField d → ℝ),
            ((∀ N, AEStronglyMeasurable (K N) P) ∧
            (∀ᵐ omega ∂P, ∀ N, 0 ≤ K N omega)) →
            (∀ᵐ omega ∂P, ∀ N, ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
              ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
                localGradientEnergy (aN N omega)
                  (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
                  (gN N omega) ≤ K N omega * rho ^ t) →
            (∀ N,
              MemLp (K N) (ENNReal.ofReal (3 * p)) P ∧
              MemLp (RN N) (ENNReal.ofReal (3 * p)) P ∧
              eLpNorm (K N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B ∧
              eLpNorm (RN N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
            (∀ h N : ℕ,
              let sigma_h := bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h
              eLpNorm
                (fun om => RN N om - (P[RN N | sigma_h]) om)
                (ENNReal.ofReal p) P ≤
              ENNReal.ofReal
                (C * delta *
                  (3 : ℝ) ^
                    (-(t * (t - (d : ℝ) + 1) / (t + 1) /
                        8) * (h : ℝ)))) ∧
            (∀ h N : ℕ, N < h →
              let sigma_h := bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h
              eLpNorm
                (fun om => RN N om - (P[RN N | sigma_h]) om)
                (ENNReal.ofReal p) P ≤
              ENNReal.ofReal
                (C * delta * (3 : ℝ) ^ (-(h : ℝ)))) ) ∧
  (∀ (d : ℕ) (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cresp : ℝ) (_hCresp : 0 < Cresp)
    (rho : ℝ → ℝ),
    ContDiff ℝ ∞ rho →
    (∀ tau, 0 ≤ rho tau) →
    (∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) →
    (∫ tau, rho tau) = 1 →
    ∀ (pvec : Fin d → ℝ),
      (∑ i : Fin d, (pvec i) ^ 2) = 1 →
    ∀ (hP : ∃ Kp : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
        ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
          Kp * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖),
      let Q := unitNeumannCube d
      let S := meanZeroResponseSpace hP
      let L0 : S.space →L[ℝ] ℝ :=
        (affineNeumannLoad pvec).comp (subspaceGradient (meanZeroSobolevGraph Q))
      ∀ (fL2 : ℝ → DomainL2 Q),
        (∀ eps : ℝ, (0 < eps ∧ eps < 1 / 8) →
          ((fL2 eps : SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (Q : Set (SpatialCoordinates d))]
            faceBump rho pvec eps)) →
        let Leps : ℝ → S.space →L[ℝ] ℝ := fun eps =>
          (sobolevVolumeLoad (fL2 eps)).comp S.space.subtypeL
        ∀ (t p B : ℝ),
          ((d : ℝ) - 1 < t ∧ t < (d : ℝ) ∧ 2 ≤ p ∧ 0 ≤ B) →
          ∃ delta0 C : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧ 0 < C ∧
            ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d),
              (0 < M.delta ∧ M.delta ≤ delta0) →
              ∀ (Rinput : _root_.SubdiffusiveProcess.Paper.in_responses d M),
                Rinput.C ≤ Cresp →
                4 * p ≤ Cresp⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
                ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
                InfraredCharacterization M H →
                let P : Measure (BilateralField d) :=
                  (chaosSampleLaw M).toMeasure
                let aN : ℕ → BilateralField d → PositiveCoefficient Q := fun N om =>
                  cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos
                let yN : ℕ → BilateralField d → ℝ := fun N om =>
                  inverseResponse S (aN N om) L0
                let yeps : ℝ → ℕ → BilateralField d → ℝ := fun eps N om =>
                  inverseResponse S (aN N om) (Leps eps)
                let ueps : ℝ → ℕ → BilateralField d → S.space := fun eps N om =>
                  responseSolution S (aN N om) (Leps eps)
                ∀ (K : ℕ → BilateralField d → ℝ),
                  (∀ N, AEStronglyMeasurable (K N) P) →
                  (∀ᵐ om ∂P, ∀ N, 0 ≤ K N om) →
                  (∀ᵐ om ∂P,
                    ∀ (N : ℕ) (eps : ℝ),
                      (0 < eps ∧ eps < 1 / 8) →
                      ∀ (x : SpatialCoordinates d) (rad : ℝ),
                        x ∈ Q → (0 < rad ∧ rad ≤ 1) →
                        localGradientEnergy (aN N om)
                            (s := Metric.ball x rad ∩ (Q : Set (SpatialCoordinates d)))
                            (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
                            (subspaceGradient S.space (ueps eps N om)) ≤
                          K N om * eps ^ (-2 : ℝ) * rad ^ t) →
                  (∀ N,
                    MemLp (K N) (ENNReal.ofReal (3 * p)) P ∧
                      eLpNorm (K N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
                  (∀ N eps, (0 < eps ∧ eps < 1 / 8) →
                    MemLp (yeps eps N) (ENNReal.ofReal (3 * p)) P ∧
                      eLpNorm (yeps eps N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
                  (∀ N,
                    MemLp (yN N) (ENNReal.ofReal (4 * p)) P ∧
                      eLpNorm (yN N) (ENNReal.ofReal (4 * p)) P ≤ ENNReal.ofReal B) →
                  (∀ N eps, (0 < eps ∧ eps < 1 / 8) →
                    eLpNorm (fun om => yN N om - yeps eps N om)
                      (ENNReal.ofReal p) P ≤
                      ENNReal.ofReal (B * eps ^ (1 / 4 : ℝ))) →
                  (∀ h N : ℕ,
                    let sigma_h := bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h
                    eLpNorm
                      (fun om => yN N om - (P[yN N | sigma_h]) om)
                      (ENNReal.ofReal p) P ≤
                    ENNReal.ofReal
                      (C * Real.sqrt M.delta *
                        (3 : ℝ) ^
                          (-((t * (t - (d : ℝ) + 1) / (t + 1) /
                              8 / 32) * (h : ℝ))))) ∧
                  (∀ h N : ℕ, N < h →
                    let sigma_h := bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h
                    eLpNorm
                      (fun om => yN N om - (P[yN N | sigma_h]) om)
                      (ENNReal.ofReal p) P ≤
                    ENNReal.ofReal
                      (C * M.delta * (3 : ℝ) ^ (-(h : ℝ)))) ) := by
  refine ⟨aux_mfd_prop_16_dirichlet, ?_⟩
  intro d hd instM instB
  exact aux_mfd_prop_16_neumann d hd (Classical.choice (inputs_J_witness d hd))

end SubdiffusiveProcess.Paper
