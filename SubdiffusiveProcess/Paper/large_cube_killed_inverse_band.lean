import SubdiffusiveProcess.Paper.prop_16
import SubdiffusiveProcess.Paper.rem_bank_response_moments
import SubdiffusiveProcess.Paper.aux_test_prop16_rd_band
import SubdiffusiveProcess.Paper.response_l1_compact_of_band
import SubdiffusiveProcess.Lane3.ResponseInstances
import SubdiffusiveProcess.Lnorm.KilledResponsePotential
import SubdiffusiveProcess.Geometry.AffineFrontierNonconst
import SubdiffusiveProcess.Sobolev.ContinuousBoundaryInfimum
import SubdiffusiveProcess.Sobolev.LocalEnergy

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane4 SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators ContDiff

local instance aux_large_cube_killed_inverse_band_fact : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 1) :=
  ⟨by norm_num⟩

noncomputable section
namespace Paper

/-- The arbitrary-radius killed-inverse branch of `prop_16`, with response moments supplied by
`rem_bank_response_moments`. The only additional stochastic input is the local-energy profile
required by `prop_16`; unlike the boundary-response wrapper, this statement allows every `r>0`. -/
theorem large_cube_killed_inverse_band
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d) :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        (hH : InfraredCharacterization M H) → (hδ : M.delta ≤ min 1 δ0) →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
          ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
            K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
        (f : SpatialCoordinates d → ℝ) (hf : ContDiff ℝ ∞ f)
        (hfc : HasCompactSupport f)
        (hfsupp : tsupport f ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
        (hf0 : ∃ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), f x ≠ 0)
        (fL2 : DomainL2 (centeredCube z r hr))
        (hfL2 : (fL2 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f),
      let Pm : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
      let S := killedResponseSpace hP
      let a : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr) :=
        fun N omega => cutoffPositiveCoefficient M H omega N z hr
      let L : S.space →L[ℝ] ℝ := (sobolevVolumeLoad fL2).comp S.space.subtypeL
      let RN : ℕ → BilateralField d → ℝ := fun N omega => inverseResponse S (a N omega) L
      let gN : ℕ → BilateralField d → HilbertGradient (centeredCube z r hr) :=
        fun N omega => subspaceGradient S.space (responseSolution S (a N omega) L)
      ∀ (K : ℕ → BilateralField d → ℝ) (BK : ℝ),
        0 ≤ BK →
        (∀ N, AEStronglyMeasurable (K N) Pm) →
        (∀ᵐ omega ∂Pm, ∀ N, 0 ≤ K N omega) →
        (∀ᵐ omega ∂Pm, ∀ N (x : SpatialCoordinates d), x ∈ (centeredCube z r hr : Set _)
          → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
            localGradientEnergy (a N omega) (s := Metric.ball x ρ) Metric.isOpen_ball.measurableSet
              (gN N omega) ≤ K N omega * ρ ^ ((d : ℝ) - 1 / 2)) →
        (∀ N, MemLp (K N) (ENNReal.ofReal (3 * 2)) Pm ∧
          eLpNorm (K N) (ENNReal.ofReal (3 * 2)) Pm ≤ ENNReal.ofReal BK) →
        ∃ Cmom Cband : ℝ, 0 ≤ Cmom ∧ 0 < Cband ∧
          (∀ N, MemLp (RN N) (ENNReal.ofReal 6) Pm ∧
            eLpNorm (RN N) (ENNReal.ofReal 6) Pm ≤ ENNReal.ofReal Cmom) ∧
          (∀ h N : ℕ,
            eLpNorm (fun omega => RN N omega - (Pm[RN N | bandSigma
              (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) omega)
              (ENNReal.ofReal 2) Pm ≤
            ENNReal.ofReal (Cband * M.delta * (3 : ℝ) ^
              (-(aux_prop16_aD d) * (h : ℝ)))) := by
  haveI : NeZero d := ⟨by omega⟩
  let t : ℝ := (d : ℝ) - 1 / 2
  have ht0 : (d : ℝ) - 1 < t := by dsimp [t]; linarith
  have ht1 : t < (d : ℝ) := by dsimp [t]; linarith
  obtain ⟨δresp, hδresp, hmoments⟩ :=
    rem_bank_response_moments d hd E Pc Xc W t ht0 ht1 2 6 (by norm_num) (by norm_num)
  refine ⟨δresp, hδresp, ?_⟩
  intro M Rm Sreg It H hH hδ z r hr hP f hf hfc hfsupp hf0 fL2 hfL2
  intro Pm S a L RN gN K BK hBK hKmeas hKnonneg hKlocal hKmem
  let slope : Fin d → ℝ := Pi.single 0 (1 : ℝ)
  have hslope : slope ≠ 0 := by
    intro hs
    have h0 := congrFun hs (0 : Fin d)
    simpa [slope] using h0
  let phi : SpatialCoordinates d → ℝ := fun x => ∑ i : Fin d, slope i * x i
  have hphi : ContDiff ℝ ∞ phi := by
    dsimp [phi]
    fun_prop
  obtain ⟨x₁, hx₁, x₂, hx₂, hnonconst⟩ :=
    SubdiffusiveProcess.affine_frontier_nonconst z r hr slope hslope
  obtain ⟨b, hb⟩ :=
    SubdiffusiveProcess.smooth_cube_weakSobolev_representative z r hr phi hphi
  obtain ⟨Bresp, hBresp, hresponse⟩ :=
    (hmoments M Rm Sreg It H hH hδ) z r hr hP phi hphi b hb f hf hfc hfsupp fL2 hfL2
  have hRNbound : ∀ N, eLpNorm (RN N) (ENNReal.ofReal (3 * 2)) Pm ≤ ENNReal.ofReal Bresp := by
    intro N
    have hsix :
        eLpNorm (fun omega => dirichletResponse S (a N omega) b)
            (ENNReal.ofReal (3 * 2)) Pm +
          eLpNorm (RN N) (ENNReal.ofReal (3 * 2)) Pm +
          eLpNorm (fun omega => dirichletResponse S (a N omega) b)
            (ENNReal.ofReal 6) Pm +
          eLpNorm (RN N) (ENNReal.ofReal 6) Pm + 0 + 0 ≤ ENNReal.ofReal Bresp := by
      simpa [Pm, S, a, L, RN] using (hresponse N).2.2.2.2
    obtain ⟨_, h₂, _, _, _, _⟩ := aux_prop16_le_of_add_six hsix
    exact h₂
  have hRNbound6 : ∀ N, eLpNorm (RN N) (ENNReal.ofReal 6) Pm ≤ ENNReal.ofReal Bresp := by
    intro N
    have hsix :
        eLpNorm (fun omega => dirichletResponse S (a N omega) b)
            (ENNReal.ofReal (3 * 2)) Pm +
          eLpNorm (RN N) (ENNReal.ofReal (3 * 2)) Pm +
          eLpNorm (fun omega => dirichletResponse S (a N omega) b)
            (ENNReal.ofReal 6) Pm +
          eLpNorm (RN N) (ENNReal.ofReal 6) Pm + 0 + 0 ≤ ENNReal.ofReal Bresp := by
      simpa [Pm, S, a, L, RN] using (hresponse N).2.2.2.2
    obtain ⟨_, _, _, h₄, _, _⟩ := aux_prop16_le_of_add_six hsix
    exact h₄
  have hB : 0 ≤ max BK Bresp := le_max_of_le_right hBresp
  have hMom : ∀ N,
      MemLp (K N) (ENNReal.ofReal (3 * 2)) Pm ∧
      MemLp (RN N) (ENNReal.ofReal (3 * 2)) Pm ∧
      eLpNorm (K N) (ENNReal.ofReal (3 * 2)) Pm ≤ ENNReal.ofReal (max BK Bresp) ∧
      eLpNorm (RN N) (ENNReal.ofReal (3 * 2)) Pm ≤ ENNReal.ofReal (max BK Bresp) := by
    intro N
    refine ⟨(hKmem N).1, ?_, ?_, ?_⟩
    · simpa [Pm, S, a, L, RN] using (hresponse N).2.1
    · exact (hKmem N).2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    · exact (hRNbound N).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
  obtain ⟨C, hC, hbandMain⟩ := Paper.prop_16.1 d hd z r hr hP phi hphi
    ⟨x₁, hx₁, x₂, hx₂, hnonconst⟩ b hb f hf hfc hfsupp hf0 fL2 hfL2
    t 2 (max BK Bresp) ht0 ht1 (by norm_num) hB false
  refine ⟨Bresp, C, hBresp, hC, ?_, ?_⟩
  · intro N
    exact ⟨by simpa [Pm, S, a, L, RN] using (hresponse N).2.2.2.1, hRNbound6 N⟩
  intro h N
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hmain := hbandMain M.delta hδpos (hδ.trans (min_le_left _ _))
    M.P M.G1 M.G2 H hH.1 hH.2
    (fun n => aux_prop16_kap M n) (fun n => aux_prop16_kap_pos M n)
    (fun n omega => cutoffPositiveCoefficient M H omega n z hr)
    (fun n omega => aux_prop16_cutoff_ae_exp M H n omega z r hr)
    K ⟨hKmeas, hKnonneg⟩ hKlocal hMom
  have hband := hmain.1 h N
  have hexp :
      t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) = aux_prop16_aD d := by
    dsimp [t, aux_prop16_aD]
  simpa [RN, Pm, hexp] using hband

/-- Countable-family killed-inverse `L⁶` moment and band inputs. The explicit `K i N omega`
profile is the local-energy input required by the inverse branch of `prop_16`. -/
theorem aux_large_cube_killed_inverse_response_family_inputs
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (Xc : in_extension d hd E)
    (W : SmallPerturbationInput d) (Idx : Type) [Countable Idx]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ Kp : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
      ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
        Kp * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (F : Idx → SpatialCoordinates d → ℝ)
    (hF : ∀ i, ContDiff ℝ ∞ (F i))
    (hFc : ∀ i, HasCompactSupport (F i))
    (hFsupp : ∀ i, tsupport (F i) ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hF0 : ∀ i, ∃ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), F i x ≠ 0)
    (fL2 : Idx → DomainL2 (centeredCube z r hr))
    (hfL2 : ∀ i, (fL2 i : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] F i) :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        (hH : InfraredCharacterization M H) → (hδ : M.delta ≤ min 1 δ0) →
      let Pm : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
      let S := killedResponseSpace hP
      let a : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr) :=
        fun N omega => cutoffPositiveCoefficient M H omega N z hr
      let L : Idx → S.space →L[ℝ] ℝ :=
        fun i => (sobolevVolumeLoad (fL2 i)).comp S.space.subtypeL
      let gN : Idx → ℕ → BilateralField d → HilbertGradient (centeredCube z r hr) :=
        fun i N omega => subspaceGradient S.space (responseSolution S (a N omega) (L i))
      let R : Idx → Response (centeredCube z r hr) :=
        fun i => inverseResponseData S (L i)
      ∀ (K : Idx → ℕ → BilateralField d → ℝ) (BK : Idx → ℝ),
        (∀ i, 0 ≤ BK i) →
        (∀ i N, AEStronglyMeasurable (K i N) Pm) →
        (∀ᵐ omega ∂Pm, ∀ i N, 0 ≤ K i N omega) →
        (∀ᵐ omega ∂Pm, ∀ i N (x : SpatialCoordinates d),
          x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
            localGradientEnergy (a N omega) (s := Metric.ball x ρ)
              Metric.isOpen_ball.measurableSet (gN i N omega) ≤
                K i N omega * ρ ^ ((d : ℝ) - 1 / 2)) →
        (∀ i N, MemLp (K i N) (ENNReal.ofReal (3 * 2)) Pm ∧
          eLpNorm (K i N) (ENNReal.ofReal (3 * 2)) Pm ≤ ENNReal.ofReal (BK i)) →
        ∃ Cmom Cband : Idx → ℝ,
          (∀ i, 0 ≤ Cmom i ∧ 0 ≤ Cband i) ∧
          0 < aux_prop16_aD d ∧
          (∀ i N,
              MemLp (SubdiffusiveProcess.Lnorm.potentialResponseOriginal
                z r hr (R i) M H N) (ENNReal.ofReal 6) Pm) ∧
          (∀ i N,
              eLpNorm (SubdiffusiveProcess.Lnorm.potentialResponseOriginal
                z r hr (R i) M H N) (ENNReal.ofReal 6) Pm ≤ ENNReal.ofReal (Cmom i)) ∧
          (∀ (i : Idx) (h N : ℕ),
              eLpNorm
                (fun omega =>
                  SubdiffusiveProcess.Lnorm.potentialResponseOriginal
                      z r hr (R i) M H N omega -
                    (Pm[SubdiffusiveProcess.Lnorm.potentialResponseOriginal
                      z r hr (R i) M H N |
                      bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) omega)
                (ENNReal.ofReal 2) Pm ≤
                ENNReal.ofReal (Cband i * M.delta * (3 : ℝ) ^
                  (-aux_prop16_aD d * (h : ℝ)))) := by
  obtain ⟨δ0, hδ0, hmodels⟩ := large_cube_killed_inverse_band d hd E Pc Xc W
  refine ⟨δ0, hδ0, ?_⟩
  intro M Rm Sreg It H hH hδ Pm S a L gN R K BK hBK hKmeas hKnonneg hKlocal hKmem
  classical
  let RN : Idx → ℕ → BilateralField d → ℝ :=
    fun i N omega => inverseResponse S (a N omega) (L i)
  let singleBand := hmodels M Rm Sreg It H hH hδ
  have hper : ∀ i, ∃ cm cb : ℝ, 0 ≤ cm ∧ 0 < cb ∧
      (∀ N, MemLp (RN i N) (ENNReal.ofReal 6) Pm ∧
        eLpNorm (RN i N) (ENNReal.ofReal 6) Pm ≤ ENNReal.ofReal cm) ∧
      (∀ h N,
        eLpNorm (fun omega => RN i N omega -
          (Pm[RN i N | bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) omega)
          (ENNReal.ofReal 2) Pm ≤
        ENNReal.ofReal (cb * M.delta * (3 : ℝ) ^
          (-aux_prop16_aD d * (h : ℝ)))) := by
    intro i
    simpa [Pm, S, a, L, RN, gN] using
      (singleBand z r hr hP (F i) (hF i) (hFc i) (hFsupp i) (hF0 i)
        (fL2 i) (hfL2 i) (K i) (BK i) (hBK i) (fun N => hKmeas i N)
        (hKnonneg.mono fun omega ho => ho i) (hKlocal.mono fun omega ho => ho i)
        (fun N => by
          simpa only [show (3 : ℝ) * 2 = 6 by norm_num] using hKmem i N))
  let Cmom : Idx → ℝ := fun i => Classical.choose (hper i)
  have hper' (i : Idx) : ∃ cb : ℝ, 0 ≤ Cmom i ∧ 0 < cb ∧
      (∀ N, MemLp (RN i N) (ENNReal.ofReal 6) Pm ∧
        eLpNorm (RN i N) (ENNReal.ofReal 6) Pm ≤ ENNReal.ofReal (Cmom i)) ∧
      (∀ h N,
        eLpNorm (fun omega => RN i N omega -
          (Pm[RN i N | bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) omega)
          (ENNReal.ofReal 2) Pm ≤
        ENNReal.ofReal (cb * M.delta * (3 : ℝ) ^
          (-aux_prop16_aD d * (h : ℝ)))) := Classical.choose_spec (hper i)
  let Cband : Idx → ℝ := fun i => Classical.choose (hper' i)
  have hselected (i : Idx) : 0 ≤ Cmom i ∧ 0 < Cband i ∧
      (∀ N, MemLp (RN i N) (ENNReal.ofReal 6) Pm ∧
        eLpNorm (RN i N) (ENNReal.ofReal 6) Pm ≤ ENNReal.ofReal (Cmom i)) ∧
      (∀ h N,
        eLpNorm (fun omega => RN i N omega -
          (Pm[RN i N | bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) omega)
          (ENNReal.ofReal 2) Pm ≤
        ENNReal.ofReal (Cband i * M.delta * (3 : ℝ) ^
          (-aux_prop16_aD d * (h : ℝ)))) := Classical.choose_spec (hper' i)
  have hEq (i : Idx) (N : ℕ) :
      (fun omega =>
        SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr (R i) M H N omega) =ᵐ[Pm]
      (fun omega => RN i N omega) := by
    filter_upwards [] with omega
    simp [RN, R, L, a, SubdiffusiveProcess.Lnorm.potentialResponseOriginal_inverse]
  have hmem6 : ∀ i N,
      MemLp (SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr (R i) M H N)
        (ENNReal.ofReal 6) Pm := by
    intro i N
    exact (memLp_congr_ae (hEq i N)).2 ((hselected i).2.2.1 N).1
  have hmom6 : ∀ i N,
      eLpNorm (SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr (R i) M H N)
        (ENNReal.ofReal 6) Pm ≤ ENNReal.ofReal (Cmom i) := by
    intro i N
    rw [eLpNorm_congr_ae (hEq i N)]
    exact ((hselected i).2.2.1 N).2
  have hband2 : ∀ (i : Idx) (h N : ℕ),
      eLpNorm
        (fun omega =>
          SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr (R i) M H N omega -
            (Pm[SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr (R i) M H N |
              bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) omega)
        (ENNReal.ofReal 2) Pm ≤
        ENNReal.ofReal (Cband i * M.delta * (3 : ℝ) ^
            (-aux_prop16_aD d * (h : ℝ))) := by
    intro i h N
    have hCE :
        Pm[SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr (R i) M H N |
          bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h] =ᵐ[Pm]
        Pm[RN i N | bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h] :=
      condExp_congr_ae (m := bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h) (hEq i N)
    have hdiff :
        (fun omega =>
          SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr (R i) M H N omega -
            (Pm[SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr (R i) M H N |
              bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) omega) =ᵐ[Pm]
        (fun omega => RN i N omega -
          (Pm[RN i N | bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) omega) := by
      filter_upwards [hEq i N, hCE] with omega hresp hce
      rw [hresp, hce]
    rw [eLpNorm_congr_ae hdiff]
    exact (hselected i).2.2.2 h N
  have hCmom : ∀ i, 0 ≤ Cmom i := fun i => (hselected i).1
  have hCband : ∀ i, 0 ≤ Cband i := fun i => (le_of_lt (hselected i).2.1)
  have haD : 0 < aux_prop16_aD d := by
    have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hnum : 0 < (d : ℝ) - 1 / 2 := by linarith
    have hcross : ((d : ℝ) - 1 / 2) - (d : ℝ) + 1 = (1 : ℝ) / 2 := by ring
    have hcrosspos : 0 < ((d : ℝ) - 1 / 2) - (d : ℝ) + 1 := by
      rw [hcross]
      norm_num
    have hden : 0 < ((d : ℝ) - 1 / 2) + 1 := by linarith
    have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
    dsimp [aux_prop16_aD]
    positivity
  refine ⟨Cmom, Cband, ?_⟩
  refine ⟨?_, haD, hmem6, hmom6, hband2⟩
  intro i
  exact ⟨hCmom i, hCband i⟩

/-- Exact quadratic-response consumer adapter: the supplied `L⁶` and band bounds for the
original potentials of `inverseResponseData S (L i)` feed the generic arbitrary-cube compactness
theorem and return its `L¹` membership and compact-closure conclusions. -/
theorem aux_large_cube_killed_inverse_response_l1_compact
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (Idx : Type) [Countable Idx]
    (S : ResponseSpace (centeredCube z r hr))
    (L : Idx → S.space →L[ℝ] ℝ)
    (Cmom Cband : Idx → ℝ) (aD : ℝ)
    (hCmom : ∀ i, 0 ≤ Cmom i) (hCband : ∀ i, 0 ≤ Cband i) (haD : 0 < aD)
    (hmem6 : ∀ i N,
      MemLp (SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr
        (inverseResponseData S (L i)) M H N)
        (ENNReal.ofReal 6) (chaosSampleLaw M).toMeasure)
    (hmom6 : ∀ i N,
      eLpNorm (SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr
        (inverseResponseData S (L i)) M H N)
        (ENNReal.ofReal 6) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cmom i))
    (hband2 : ∀ (i : Idx) (h N : ℕ),
      eLpNorm
        (fun omega =>
          SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr
              (inverseResponseData S (L i)) M H N omega -
            (((chaosSampleLaw M).toMeasure)[
              SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr
                (inverseResponseData S (L i)) M H N |
              bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) omega)
        (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cband i * M.delta * (3 : ℝ) ^ (-aD * (h : ℝ)))) :
    (∀ i N,
      MemLp (SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr
        (inverseResponseData S (L i)) M H N) 1 (chaosSampleLaw M).toMeasure) ∧
    (∀ i, IsCompact (closure (Set.range (fun N =>
      ((hmem6 i N).mono_exponent (by norm_num : ENNReal.ofReal 1 ≤ ENNReal.ofReal 6)).toLp
        (SubdiffusiveProcess.Lnorm.potentialResponseOriginal z r hr
          (inverseResponseData S (L i)) M H N))))) := by
  exact Paper.response_l1_compact_of_band d z r hr M H hH Idx
    (fun i => inverseResponseData S (L i)) Cmom Cband aD hCmom hCband haD hmem6 hmom6 hband2

end Paper
