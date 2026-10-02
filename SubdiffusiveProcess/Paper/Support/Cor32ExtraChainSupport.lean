import SubdiffusiveProcess.Paper.Support.Cor32ProbabilitySupport





open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Paper
noncomputable section
theorem aux_cor_32_extra_chain
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (field : Ω → BilateralField d) (hfield_meas : Measurable field)
    (hfield_map : Measure.map field P = (chaosSampleLaw model).toMeasure)
    (H1 : ℕ) (hH1 : 1 ≤ H1)
    (thetap : ℝ) (hthetap0 : 0 < thetap) (hthetap1 : thetap < 1)
    (p Cbound q r K A lam0 : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r) (hr1 : r < 1)
    (hCbound : 0 ≤ Cbound) (hKdef : K = lam0 * (1 - r) / 2) (hlam0 : 0 < lam0) (hApos : 0 < A)
    (hbudget : ∀ k : ℕ,
      2 * ((2 * (Cbound / q * q ^ k) / (K * r ^ k)) ^ p) ≤ Real.exp (-(A * ((k : ℝ) + 1))))
    (hAbeats : 1 + ((H1 * d : ℕ) : ℝ) * Real.log 3 ≤
      A * thetap / 24 + Real.log (1 - Real.exp (-A / 2)))
    (Band : ℕ → ℕ → MeasurableSpace Ω)
    (hBand_def : ∀ (n H : ℕ), Band n H =
      ⨆ (j : ℤ) (_h : |j + ((H1 * n : ℕ) : ℤ)| ≤ (H : ℤ)),
        (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap
          (fun omega : Ω => field omega j))
    (Test : (n : ℕ) → (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Ω → ℝ)
    (TestB : (n : ℕ) → (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → ℕ → Ω → ℝ)
    (hTest_meas : ∀ n w, Measurable (Test n w))
    (hTest_ae : ∀ n w, AEStronglyMeasurable (Test n w) P)
    (hTestB_meas : ∀ n w H, StronglyMeasurable[Band n H] (TestB n w H))
    (hTestB_ae : ∀ n w H, AEStronglyMeasurable (TestB n w H) P)
    (hTest_moment : ∀ n w, eLpNorm (Test n w) (ENNReal.ofReal p) P ≤ ENNReal.ofReal Cbound)
    (hTest_err : ∀ n w (H : ℕ), eLpNorm (fun om => Test n w om - TestB n w H om)
      (ENNReal.ofReal p) P ≤ ENNReal.ofReal (Cbound * q ^ H)) :
    ∃ Bextra : Ω → ℝ, Measurable Bextra ∧ (∀ omega, 0 ≤ Bextra omega) ∧
      ∀ᵐ omega ∂P, ∀ J : ℕ, 1 ≤ J →
        ∀ pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1),
          (Nat.card {j : Fin J // ¬ (Test (j.val + 1)
              (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩) omega ≤ lam0)} : ℝ) ≤
            thetap * (J : ℝ) + Bextra omega := by
  have hindep := aux_cor_32_field_layers_iIndepFun P model field hfield_meas hfield_map
  -- countable joint a.e.-limit carrier
  let Y : (Σ n : ℕ, Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Ω → ℝ :=
    fun qi => Test qi.1 qi.2
  let Yb : (Σ n : ℕ, Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → ℕ → Ω → ℝ :=
    fun qi k => TestB qi.1 qi.2 k
  have hYae : ∀ qi, AEStronglyMeasurable (Y qi) P := fun qi => hTest_ae qi.1 qi.2
  have hYbae : ∀ qi k, AEStronglyMeasurable (Yb qi k) P := fun qi k => hTestB_ae qi.1 qi.2 k
  have herrq : ∀ qi (k : ℕ), eLpNorm (fun om => Y qi om - Yb qi k om) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (Cbound * q ^ k) := fun qi k => hTest_err qi.1 qi.2 k
  have hae0 : ∀ qi, ∀ᵐ ω ∂P, Tendsto (fun k => Y qi ω - Yb qi k ω) atTop (𝓝 (0 : ℝ)) := by
    intro qi
    exact aux_ae_tendsto_zero_of_geometric_base P p q Cbound hp hq.le hq1 hCbound
      (fun k om => Y qi om - Yb qi k om) (fun k => (hYae qi).sub (hYbae qi k)) (herrq qi)
  have haeAll : ∀ᵐ ω ∂P, ∀ qi, Tendsto (fun k => Yb qi k ω) atTop (𝓝 (Y qi ω)) := by
    have hzero : ∀ᵐ ω ∂P, ∀ qi, Tendsto (fun k => Y qi ω - Yb qi k ω) atTop (𝓝 (0 : ℝ)) :=
      ae_all_iff.mpr hae0
    filter_upwards [hzero] with ω hω qi
    have ht := (tendsto_const_nhds (x := Y qi ω)).sub (hω qi)
    simpa using ht
  obtain ⟨Sigma, hSigmaMeas, hSigmaP, hSigmaProp⟩ :=
    aux_exists_measurable_full_measure_of_ae P
      (fun ω => ∀ qi, Tendsto (fun k => Yb qi k ω) atTop (𝓝 (Y qi ω))) haeAll
  
  have hBandmono : ∀ n : ℕ, Monotone (Band n) := by
    intro n Ha Hb hHab
    rw [hBand_def n Ha, hBand_def n Hb]
    apply iSup_le; intro j; apply iSup_le; intro hj
    have hj' : |j + ((H1 * n : ℕ) : ℤ)| ≤ (Hb : ℤ) :=
      le_trans hj (by exact_mod_cast hHab)
    exact le_iSup₂ (f := fun j (_ : |j + ((H1 * n : ℕ) : ℤ)| ≤ (Hb : ℤ)) =>
      (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap
        (fun omega : Ω => field omega j)) j hj'
  have hnode_cover : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
      ∃ W : ℕ+ → Set Ω,
        (∀ h : ℕ+, MeasurableSet[Band n h] (W h)) ∧
        (∀ h : ℕ+, P (W h) ≤ ENNReal.ofReal (Real.exp (-(A * (h : ℝ))))) ∧
        Sigma ∩ {ω | lam0 ≤ Test n w ω} ⊆ ⋃ h : ℕ+, W h := by
    intro n w
    exact aux_cor_32_node_cover P p A q r K Cbound lam0 hp hq hq1.le hr hr1 hCbound hlam0 hKdef
      hbudget (Band n) (hBandmono n) (Test n w) (TestB n w) (hTestB_meas n w) (hTestB_ae n w)
      (hTest_ae n w) (hTest_moment n w) (hTest_err n w) Sigma
      (fun ω hω => hSigmaProp ω hω ⟨n, w⟩)
  choose W hWmeas hWprob hWcover using hnode_cover
  let g : ℤ → Ω → C(SpatialCoordinates d, ℝ) := fun j omega => field omega j
  have hg_meas : ∀ j : ℤ, Measurable (g j) := fun j => (measurable_pi_apply j).comp hfield_meas
  have hdevAll : ∀ J : ℕ, 1 ≤ J →
      P {ω | ∃ π : Fin J → OddGridIndex d (subdivisionHalfWidth H1),
          thetap * (J : ℝ) ≤
            (Nat.card {i : Fin J //
                ¬ (Test (i.val + 1)
                    (fun t : Fin (i.val + 1) => π ⟨t.val, by omega⟩) ω ≤ lam0)} : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(1 * (J : ℝ)))) := by
    intro J hJ
    let β : Type := Fin J → OddGridIndex d (subdivisionHalfWidth H1)
    let ns : β → Fin J → ℤ := fun _ i => ((H1 * (i.val + 1) : ℕ) : ℤ)
    have hns : ∀ b : β, Function.Injective (ns b) := by
      intro b i k hik
      have heqn : H1 * (i.val + 1) = H1 * (k.val + 1) := by
        have := hik
        dsimp only [ns] at this
        exact_mod_cast this
      have heqi : i.val + 1 = k.val + 1 := Nat.eq_of_mul_eq_mul_left hH1 heqn
      exact Fin.ext (by omega)
    let failure : β → Fin J → Set Ω := fun b i =>
      Sigma ∩ {ω | ¬ (Test (i.val + 1)
        (fun t : Fin (i.val + 1) => b ⟨t.val, by omega⟩) ω ≤ lam0)}
    let Wbr : β → Fin J → ℕ+ → Set Ω := fun b i h =>
      W (i.val + 1) (fun t : Fin (i.val + 1) => b ⟨t.val, by omega⟩) h
    have hWbr_meas : ∀ (b : β) (i : Fin J) (h : ℕ+),
        MeasurableSet[
          ⨆ j : ℤ, ⨆ (_ : j ∈ Finset.Icc (ns b i - (h : ℤ)) (ns b i + 2 * (h : ℤ))),
            MeasurableSpace.comap (g (-j))
              (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ))]
          (Wbr b i h) := by
      intro b i h
      have hle : Band (i.val + 1) (h : ℕ) ≤
          ⨆ j : ℤ, ⨆ (_ : j ∈ Finset.Icc (ns b i - (h : ℤ)) (ns b i + 2 * (h : ℤ))),
            MeasurableSpace.comap (g (-j))
              (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)) := by
        rw [hBand_def (i.val + 1) (h : ℕ)]
        have hcast : ((H1 * (i.val + 1) : ℕ) : ℤ) = ns b i := rfl
        rw [hcast]
        exact aux_cor_32_band_le_branch_window g (ns b i) (h : ℤ) (h : ℤ) le_rfl
      exact hle _ (hWmeas (i.val + 1) (fun t : Fin (i.val + 1) => b ⟨t.val, by omega⟩) h)
    have hWbr_prob : ∀ (b : β) (i : Fin J) (h : ℕ+),
        P (Wbr b i h) ≤ ENNReal.ofReal (Real.exp (-A * (h : ℝ))) := by
      intro b i h
      have := hWprob (i.val + 1) (fun t : Fin (i.val + 1) => b ⟨t.val, by omega⟩) h
      simpa [neg_mul] using this
    have hfailure_cov : ∀ (b : β) (i : Fin J), failure b i ⊆ ⋃ h : ℕ+, Wbr b i h := by
      intro b i om hom
      apply hWcover (i.val + 1) (fun t : Fin (i.val + 1) => b ⟨t.val, by omega⟩)
      refine ⟨hom.1, ?_⟩
      have hlt : lam0 < Test (i.val + 1)
          (fun t : Fin (i.val + 1) => b ⟨t.val, by omega⟩) om := lt_of_not_ge hom.2
      exact hlt.le
    have hbranch :=
      SubdiffusiveProcess.union_bound_finitely_many_bad_branches (β := β) J A thetap
        hApos hthetap0 hthetap1 Ω C(SpatialCoordinates d, ℝ) P g hg_meas hindep ns hns
        failure Wbr hWbr_meas hWbr_prob hfailure_cov
    have hN : Fintype.card β = (Fintype.card (OddGridIndex d (subdivisionHalfWidth H1))) ^ J := by
      simp [β]
    have hcardpos : 0 < Fintype.card (OddGridIndex d (subdivisionHalfWidth H1)) :=
      Fintype.card_pos
    have h3odd : Odd ((3 : ℕ) ^ H1) := Odd.pow ⟨1, rfl⟩
    obtain ⟨kk, hkk⟩ := h3odd
    have hsw : subdivisionHalfWidth H1 = kk := by
      unfold subdivisionHalfWidth
      omega
    have hpow3 : 2 * subdivisionHalfWidth H1 + 1 = 3 ^ H1 := by rw [hsw]; omega
    have hcardeq2 : Fintype.card (OddGridIndex d (subdivisionHalfWidth H1)) = 3 ^ (H1 * d) := by
      show Fintype.card (Fin d → Fin (2 * subdivisionHalfWidth H1 + 1)) = 3 ^ (H1 * d)
      rw [hpow3]
      simp [pow_mul]
    have hlogN : Real.log (Fintype.card (OddGridIndex d (subdivisionHalfWidth H1)) : ℝ) =
        ((H1 * d : ℕ) : ℝ) * Real.log 3 := by
      rw [hcardeq2]
      push_cast
      rw [Real.log_pow]
      push_cast
      ring
    have hfinal : (Fintype.card β : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp
          (-((A * thetap / 24) + Real.log (1 - Real.exp (-A / 2))) * (J : ℝ))) ≤
        ENNReal.ofReal (Real.exp (-(1 * (J : ℝ)))) := by
      have hcardR : ((Fintype.card β : ℕ) : ℝ) =
          Real.exp (Real.log (Fintype.card (OddGridIndex d (subdivisionHalfWidth H1)) : ℝ) *
            (J : ℝ)) := by
        rw [hN]
        rw [show ((Fintype.card (OddGridIndex d (subdivisionHalfWidth H1)) ^ J : ℕ) : ℝ) =
            ((Fintype.card (OddGridIndex d (subdivisionHalfWidth H1)) : ℝ)) ^ J by push_cast; ring]
        rw [mul_comm (Real.log _) (J:ℝ), Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hcardpos)]
      have hprod : ((Fintype.card β : ℕ) : ℝ) *
          Real.exp (-((A * thetap / 24) + Real.log (1 - Real.exp (-A / 2))) * (J : ℝ)) ≤
          Real.exp (-(1 * (J : ℝ))) := by
        rw [hcardR, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hJ0 : (0:ℝ) ≤ (J:ℝ) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hAbeats hJ0, hlogN]
      rw [show ((Fintype.card β : ℕ) : ℝ≥0∞) =
          ENNReal.ofReal ((Fintype.card β : ℕ) : ℝ) by
            exact (ENNReal.ofReal_natCast (Fintype.card β)).symm]
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal hprod
    have hsigma_transfer :
        {ω | ∃ π : Fin J → OddGridIndex d (subdivisionHalfWidth H1),
            thetap * (J : ℝ) ≤
              (Nat.card {i : Fin J //
                  ¬ (Test (i.val + 1)
                      (fun t : Fin (i.val + 1) => π ⟨t.val, by omega⟩) ω ≤ lam0)} : ℝ)} ⊆
          Sigmaᶜ ∪ {ω | ∃ b : β, thetap * (J : ℝ) ≤
              (Set.ncard {i : Fin J | ω ∈ failure b i} : ℝ)} := by
      rintro ω ⟨π, hπ⟩
      by_cases homS : ω ∈ Sigma
      · right
        refine ⟨π, ?_⟩
        have hseteq : {i : Fin J | ω ∈ failure π i} =
            {i : Fin J | ¬ (Test (i.val + 1)
              (fun t : Fin (i.val + 1) => π ⟨t.val, by omega⟩) ω ≤ lam0)} := by
          ext i
          simp only [failure, Set.mem_setOf_eq, Set.mem_inter_iff]
          exact ⟨fun h => h.2, fun h => ⟨homS, h⟩⟩
        have hcardeq : (Set.ncard {i : Fin J | ω ∈ failure π i} : ℝ) =
            (Nat.card {i : Fin J //
                ¬ (Test (i.val + 1)
                    (fun t : Fin (i.val + 1) => π ⟨t.val, by omega⟩) ω ≤ lam0)} : ℝ) := by
          rw [← Nat.card_coe_set_eq, hseteq]
          rfl
        rw [hcardeq]; exact hπ
      · left; exact homS
    calc P {ω | ∃ π : Fin J → OddGridIndex d (subdivisionHalfWidth H1),
          thetap * (J : ℝ) ≤
            (Nat.card {i : Fin J //
                ¬ (Test (i.val + 1)
                    (fun t : Fin (i.val + 1) => π ⟨t.val, by omega⟩) ω ≤ lam0)} : ℝ)}
        ≤ P (Sigmaᶜ ∪ {ω | ∃ b : β, thetap * (J : ℝ) ≤
              (Set.ncard {i : Fin J | ω ∈ failure b i} : ℝ)}) :=
          measure_mono hsigma_transfer
      _ ≤ P Sigmaᶜ + P {ω | ∃ b : β, thetap * (J : ℝ) ≤
              (Set.ncard {i : Fin J | ω ∈ failure b i} : ℝ)} := measure_union_le _ _
      _ = P {ω | ∃ b : β, thetap * (J : ℝ) ≤
              (Set.ncard {i : Fin J | ω ∈ failure b i} : ℝ)} := by
          have hcompl : P Sigmaᶜ = 0 := by
            rw [prob_compl_eq_one_sub hSigmaMeas, hSigmaP, tsub_self]
          rw [hcompl, zero_add]
      _ ≤ (Fintype.card β : ℝ≥0∞) * ENNReal.ofReal (Real.exp
            (-((A * thetap / 24) + Real.log (1 - Real.exp (-A / 2))) * (J : ℝ))) := hbranch
      _ ≤ ENNReal.ofReal (Real.exp (-(1 * (J : ℝ)))) := hfinal
  let N : ℕ := Fintype.card (OddGridIndex d (subdivisionHalfWidth H1))
  have hNpos : 0 < N := Fintype.card_pos
  let e : OddGridIndex d (subdivisionHalfWidth H1) ≃ Fin N := Fintype.equivFin _
  let badCount : (J : ℕ) → (Fin J → OddGridIndex d (subdivisionHalfWidth H1)) → Ω → ℕ :=
    fun J pi omega => Nat.card {i : Fin J //
      ¬ (Test (i.val + 1) (fun t : Fin (i.val + 1) => pi ⟨t.val, by omega⟩) omega ≤ lam0)}
  let badCountN : (J : ℕ) → (Fin J → Fin N) → Ω → ℕ :=
    fun J pi omega => badCount J (fun i => e.symm (pi i)) omega
  have hleN : ∀ (K : ℕ) (pi : Fin K → Fin N) (omega : Ω), badCountN K pi omega ≤ K := by
    intro K pi omega
    dsimp only [badCountN, badCount]
    calc Nat.card {i : Fin K // ¬ (Test (i.val + 1)
          (fun t : Fin (i.val + 1) => e.symm (pi ⟨t.val, by omega⟩)) omega ≤ lam0)} ≤
        Nat.card (Fin K) := by
          apply Nat.card_le_card_of_injective (fun x => x.1)
          intro a b hab
          exact Subtype.ext hab
      _ = K := by simp
  have hmeasN : ∀ (K : ℕ) (pi : Fin K → Fin N), Measurable (badCountN K pi) := by
    intro K pi
    apply measurable_ncard.comp
    apply measurable_set_iff.mpr
    intro i
    change Measurable (fun omega =>
      ¬ (Test (i.val + 1) (fun t : Fin (i.val + 1) => e.symm (pi ⟨t.val, by omega⟩)) omega ≤ lam0))
    exact measurableSet_setOf.mp ((measurableSet_le (hTest_meas (i.val + 1)
      (fun t : Fin (i.val + 1) => e.symm (pi ⟨t.val, by omega⟩))) measurable_const).compl)
  have hdevNAll : ∀ K : ℕ, 1 ≤ K →
      P {ω | ∃ pi : Fin K → Fin N, thetap * (K : ℝ) ≤ (badCountN K pi ω : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(1 * (K : ℝ)))) := by
    intro K hK
    have heq : {ω | ∃ b : Fin K → OddGridIndex d (subdivisionHalfWidth H1),
          thetap * (K : ℝ) ≤ (badCount K b ω : ℝ)} =
        {ω | ∃ pi : Fin K → Fin N, thetap * (K : ℝ) ≤ (badCountN K pi ω : ℝ)} := by
      ext ω
      constructor
      · rintro ⟨b, hb⟩
        exact ⟨fun i => e (b i), by simpa [badCountN] using hb⟩
      · rintro ⟨pi, hpi⟩
        exact ⟨fun i => e.symm (pi i), by simpa [badCountN] using hpi⟩
    rw [← heq]
    exact hdevAll K hK
  obtain ⟨B, hBmeas, hBnonneg, hBae, hBtail⟩ :=
    SubdiffusiveProcess.Lane3.all_chain_estimate Ω P N hNpos thetap 1 hthetap0 hthetap1
      one_pos badCountN hleN hmeasN hdevNAll
  refine ⟨B, hBmeas, hBnonneg, ?_⟩
  filter_upwards [hBae] with omega hω J hJ pi
  have hthis := hω J (fun i => e (pi i)) hJ
  simpa [badCountN, badCount] using hthis


end
end Paper
