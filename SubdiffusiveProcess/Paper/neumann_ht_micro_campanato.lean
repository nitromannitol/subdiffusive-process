module

public import SubdiffusiveProcess.Paper.neumann_ht_energy
public import SubdiffusiveProcess.Paper.calib3_envelope
public import SubdiffusiveProcess.Paper.prop_growth_holder_micro_campanato

@[expose] public section

/-! Campanato decay below the wavelength `3^{-(N+j)}` for the bounded-source Neumann problem with the
top-block-removed coefficient (transplant of `aux_cor_neumann_source_micro_campanato`): the energy input
is `neumann_ht_energy`, the coefficient envelope `calib3_envelope` (rate constants independent of `j`,
prefactor `CE(j)`), and the smallness threshold is chosen before `j`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace Metric Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

noncomputable section
namespace Paper

/-- The exponent `t` used for the energy input of the Campanato estimates. -/
theorem aux_neumann_ht_micro_campanato_exponents (d : ℕ) (alpha : ℝ) (ha1 : alpha < 1) :
    ∃ t e : ℝ, (d : ℝ) - 1 < t ∧ t < d ∧ 0 < e ∧ 2 + t = 2 * alpha + d + e := by
  obtain ⟨ht1, htd, he0⟩ := aux_cor_neumann_source_t1_exponent d alpha ha1
  refine ⟨(max ((d : ℝ) - 1) ((d : ℝ) - 2 + 2 * alpha) + d) / 2,
    2 + (max ((d : ℝ) - 1) ((d : ℝ) - 2 + 2 * alpha) + d) / 2 - 2 * alpha - d, ht1, htd, he0, ?_⟩
  ring

theorem neumann_ht_micro_campanato (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) (alpha : ℝ)
    (k : ℕ) (ps : Fin k → ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) (hps : ∀ i, 1 ≤ ps i) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg),
        M.delta ≤ delta0 → ∀ j : ℕ, 0 < j →
        ∃ (Kosc : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
          (∀ N om, 0 ≤ Kosc N om) ∧
          (∀ i N, MemLp (Kosc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
          (∀ i N, eLpNorm (Kosc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (Cbound i)) ∧
          ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
            ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
              AEMeasurable F (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
              (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
                |F x| ≤ Kf) →
              (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
            ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
              SolvesNeumann (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j)
                (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) F v →
              ∀ x ∈ unitNeumannCube d, ∀ rad : ℝ, 0 < rad →
                rad ≤ (3 : ℝ) ^ (-((N + j : ℕ) : ℤ)) → rad ≤ 1 →
                ∫ y in Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
                    ((v : SobolevData (unitNeumannCube d)).1 y - setAverage
                      (Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
                      (v : SobolevData (unitNeumannCube d)).1) ^ 2
                    ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)) ≤
                  (Kosc N om * Kf) ^ 2 * rad ^ (2 * alpha) *
                    volume.real (Metric.ball x rad ∩
                      (unitNeumannCube d : Set (SpatialCoordinates d))) := by
  obtain ⟨t, e, ht1, htd, he, hexp⟩ := aux_neumann_ht_micro_campanato_exponents d alpha ha1
  have hsum0 : 0 ≤ ∑ i, ps i := Finset.sum_nonneg fun i _ => le_trans zero_le_one (hps i)
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = 1 + ∑ i, ps i := ⟨_, rfl⟩
  have hq : 1 ≤ q := by rw [hqdef]; linarith
  have hpq : ∀ i, ps i ≤ q := by
    intro i
    have := Finset.single_le_sum (fun j _ => le_trans zero_le_one (hps j)) (Finset.mem_univ i)
    rw [hqdef]; linarith
  have hq0 : 0 < 2 * q := by linarith
  obtain ⟨deltaE, hdeltaE, hEA⟩ := neumann_ht_energy d hd E _P _X _W D t k ps ht1 htd hps
  obtain ⟨Cpe, Cd, cd, hCpe, hCd, hcd, hroot⟩ := calib3_envelope d hd q hq
  obtain ⟨CP, hCP0, hPoinc⟩ :=
    aux_prop_growth_holder_micro_campanato_scaled_poincare d (by omega)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  obtain ⟨dabs, hdabs⟩ : ∃ s : ℝ, s = min 1 ((e / 2) * Real.log 3 / (Cd + Cpe)) := ⟨_, rfl⟩
  have hdabs0 : 0 < dabs := by
    rw [hdabs]
    exact lt_min one_pos (div_pos (mul_pos (half_pos he) hlog3) (add_pos hCd hCpe))
  refine ⟨min deltaE (min (cd / (2 * q)) dabs),
    lt_min hdeltaE (lt_min (div_pos hcd hq0) hdabs0), ?_⟩
  intro M Rm Sreg It hdelta j hj
  have hdE : M.delta ≤ deltaE := hdelta.trans (min_le_left _ _)
  have hdc : M.delta ≤ cd / (2 * q) :=
    hdelta.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hda : M.delta ≤ dabs := hdelta.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hrate : Cd * M.delta + Cpe * M.delta ^ 2 ≤ (e / 2) * Real.log 3 :=
    aux_prop_growth_holder_micro_campanato_rate Cd Cpe e M.delta hCd hCpe hdpos
      (hda.trans_eq hdabs)
  obtain ⟨K, CbK, hK0, hKL, hKB, hen⟩ := hEA M Rm Sreg It hdE j hj
  obtain ⟨Dx, Mx, CD, CE, hCD, hCE, hDMx0, hext, hmem, -, hMxmom⟩ :=
    hroot M hdc j hj (fun _ => (1 / 2 : ℝ))
  have hfac := aux_prop_growth_holder_micro_campanato_fac e _ he hrate
  have hCP1 : 0 ≤ 1 + CP := add_nonneg zero_le_one hCP0
  refine ⟨fun N om => (1 + CP) * (Mx (N + j) om + |K N om|) * ((3 : ℝ) ^ (-((N + j : ℕ) : ℤ))) ^ (e / 2),
    fun i => (1 + CP) * (CE + max (CbK i) 0), ?_, ?_, ?_, ?_⟩
  · intro N om
    have := (hDMx0 (N + j) om).2
    have := (hfac (N + j)).1
    positivity
  · intro i N
    exact (aux_prop_growth_holder_micro_campanato_moment (chaosSampleLaw M).toMeasure (ps i) q
      (hps i) (hpq i) (Mx (N + j)) (K N) (1 + CP) _
      ((Cd * M.delta + Cpe * M.delta ^ 2) * ((N + j : ℕ) : ℝ)) CE
      (CbK i) hCP1 (hfac (N + j)).1 (hfac (N + j)).2.1 (hfac (N + j)).2.2 hCE (hmem (N + j)).2
      (hMxmom (N + j)) (hKL i N) (hKB i N)).1
  · intro i N
    exact (aux_prop_growth_holder_micro_campanato_moment (chaosSampleLaw M).toMeasure (ps i) q
      (hps i) (hpq i) (Mx (N + j)) (K N) (1 + CP) _
      ((Cd * M.delta + Cpe * M.delta ^ 2) * ((N + j : ℕ) : ℝ)) CE
      (CbK i) hCP1 (hfac (N + j)).1 (hfac (N + j)).2.1 (hfac (N + j)).2.2 hCE (hmem (N + j)).2
      (hMxmom (N + j)) (hKL i N) (hKB i N)).2
  · filter_upwards [hen, hext] with om hom hext'
    intro N F Kf hKf hFm hFb hmean v hsol x hx rad hrad hradN hrad1
    obtain ⟨hMxpos, hbounds, -⟩ := hext' (N + j)
    have hlow := aux_cor_neumann_source_micro_floor M (calib3_HT d j) om (N + j) (Mx (N + j) om)
      hMxpos (fun y hy => (hbounds y hy).1)
    exact aux_cor_neumann_source_micro_pathwise CP hCP0 hPoinc
      (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j) (fun _ => (1 / 2 : ℝ)) one_pos)
      (Mx (N + j) om) hMxpos.le hlow v (K N om) Kf t alpha e ((3 : ℝ) ^ (-((N + j : ℕ) : ℤ))) rad
      hrad hradN hrad1 he.le hexp
      (fun c hc => hom N F Kf hKf hFm hFb hmean v hsol c rad hc hrad hrad1) x hx

end Paper
