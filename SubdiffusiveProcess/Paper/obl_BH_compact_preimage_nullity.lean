module

public import SubdiffusiveProcess.Paper.obl_BH_smooth_null_cutoffs
public import SubdiffusiveProcess.Paper.obl_BH_cutoff_weak_form
public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.DirichletForm.All

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal Topology ContDiff

namespace Paper

lemma aux_obl_BH_compact_preimage_nullity_cutoffs
    (K : Set ℝ) (hK : IsCompact K) (hKnull : volume K = 0) :
    ∃ (U : ℕ → Set ℝ) (phi : ℕ → ℝ → ℝ),
      (∀ n : ℕ,
        IsOpen (U n) ∧ K ⊆ U n ∧
          volume.real (U n) ≤ 1 / ((n : ℝ) + 1) ∧
          volume (U n) ≠ ⊤) ∧
      (∀ n : ℕ,
        ContDiff ℝ ∞ (phi n) ∧
          (∀ x : ℝ, 0 ≤ phi n x ∧ phi n x ≤ 1) ∧
          (∀ x ∈ K, phi n x = 1) ∧
          tsupport (phi n) ⊆ U n) := by
  have hU : ∀ n : ℕ, ∃ U : Set ℝ,
      K ⊆ U ∧ IsOpen U ∧ volume U < ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    intro n
    have hn : 0 < (1 / ((n : ℝ) + 1) : ℝ) := by positivity
    apply Set.exists_isOpen_lt_of_lt K (ENNReal.ofReal (1 / ((n : ℝ) + 1)))
    rw [hKnull]
    exact ENNReal.ofReal_pos.mpr hn
  choose U hKU hUopen hUmeasure using hU
  have hUreal : ∀ n : ℕ, volume.real (U n) ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    have hn : 0 ≤ (1 / ((n : ℝ) + 1) : ℝ) := by positivity
    have hlt : (volume (U n)).toReal <
        (ENNReal.ofReal (1 / ((n : ℝ) + 1))).toReal :=
      (ENNReal.toReal_lt_toReal (ne_of_lt ((hUmeasure n).trans_le le_top))
        ENNReal.ofReal_ne_top).mpr (hUmeasure n)
    rw [ENNReal.toReal_ofReal hn] at hlt
    exact hlt.le
  have hphi : ∀ n : ℕ, ∃ phi : ℝ → ℝ,
      ContDiff ℝ ∞ phi ∧
        (∀ x : ℝ, 0 ≤ phi x ∧ phi x ≤ 1) ∧
        (∀ x ∈ K, phi x = 1) ∧
        tsupport phi ⊆ U n := by
    intro n
    exact aux_obl_BH_smooth_null_cutoffs_smooth K (U n) hK (hUopen n) (hKU n)
  choose phi hphi_smooth hphi_range hphi_one hphi_support using hphi
  refine ⟨U, phi, ?_, ?_⟩
  · intro n
    exact ⟨hUopen n, hKU n, hUreal n,
      ne_of_lt ((hUmeasure n).trans_le le_top)⟩
  · intro n
    exact ⟨hphi_smooth n, hphi_range n, hphi_one n, hphi_support n⟩

lemma aux_obl_BH_compact_preimage_nullity_pairing
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : _root_.DirichletForm
      (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (u : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hu : u ∈ E.toClosedForm.domain)
    (uc : SpatialCoordinates d → ℝ) (huc : Continuous uc)
    (hurep : (⇑u =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] uc))
    (T phi : ℝ → ℝ) (hT0 : T 0 = 0)
    (hTderiv : ∀ s : ℝ, HasDerivAt T (phi s) s)
    (hTcd : ContDiff ℝ 1 T)
    (w : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hw : w ∈ E.toClosedForm.domain)
    (hwrep : (⇑w =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
      (fun x => T (uc x))))
    (hphic : Continuous phi) (hphib : ∀ s : ℝ, |phi s| ≤ 1) :
    (∫ x, phi (uc x) ∂(Gamma.measure u)) = E.toClosedForm.form u w := by
  let p : SpatialCoordinates d → ℝ := fun x => phi (uc x)
  let μ : Measure (SpatialCoordinates d) := Gamma.measure u
  have hp_cont : Continuous p := hphic.comp huc
  have hp_bound : ∀ x, |p x| ≤ 1 := fun x => hphib (uc x)
  letI : IsFiniteMeasure μ := ⟨Gamma.measure_univ_lt_top u hu⟩
  have hp_int : Integrable p μ := by
    exact DirichletForm.integrable_of_continuous_of_bound hp_cont hp_bound
  have hp_sq_int : Integrable (fun x => p x ^ 2) μ := by
    apply DirichletForm.integrable_of_continuous_of_bound (C := 1) (hp_cont.pow 2)
    intro x
    rw [Pi.pow_apply, abs_pow]
    have hsq : |p x| ^ 2 ≤ (1 : ℝ) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg (p x)) (by norm_num : (0 : ℝ) ≤ 1)).2 (hp_bound x)
    norm_num at hsq ⊢
    exact hsq
  have h1_int : Integrable (fun _ : SpatialCoordinates d => (1 : ℝ)) μ :=
    integrable_const 1
  have h2p_int : Integrable (fun x => 2 * p x) μ := by
    simpa [smul_eq_mul] using! hp_int.smul (2 : ℝ)
  have hTderiv_fun : deriv T = phi := by
    funext s
    exact (hTderiv s).deriv
  let S : ℝ → ℝ := fun s => s + T s
  have hS0 : S 0 = 0 := by simp [S, hT0]
  have hSderiv : deriv S = fun s => 1 + phi s := by
    funext s
    have hs := (hasDerivAt_id s).add (hTderiv s)
    simpa [S] using! hs.deriv
  have hS_contdiff : ContDiff ℝ 1 S := by
    simpa [S] using (contDiff_id.add hTcd)
  have hSrep :
      (⇑(u + w) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
        (fun x => S (uc x))) := by
    filter_upwards [Lp.coeFn_add u w, hurep, hwrep] with x hadd hx hy
    calc
      (⇑(u + w)) x = (⇑u) x + (⇑w) x := hadd
      _ = uc x + T (uc x) := by rw [hx, hy]
      _ = S (uc x) := rfl
  have hTchain := Gamma.chain_rule u hu uc huc hurep T hTcd hT0 w hw hwrep
    Set.univ MeasurableSet.univ
  have hTmass : (Gamma.measure w Set.univ).toReal =
      ∫ x, p x ^ 2 ∂μ := by
    simpa [p, μ, hTderiv_fun] using hTchain
  have hSchain := Gamma.chain_rule u hu uc huc hurep S hS_contdiff hS0
      (u + w) (E.toClosedForm.domain.add_mem hu hw) hSrep
      Set.univ MeasurableSet.univ
  have hSmass : (Gamma.measure (u + w) Set.univ).toReal =
      ∫ x, (1 + p x) ^ 2 ∂μ := by
    simpa [p, μ, hSderiv] using hSchain
  have hUmass : E.toClosedForm.form u u = ∫ x, (1 : ℝ) ∂μ := by
    calc
      E.toClosedForm.form u u = (Gamma.measure u Set.univ).toReal :=
        (Gamma.measure_univ u hu).symm
      _ = ∫ x, (1 : ℝ) ∂μ := by simp [μ, integral_const, measureReal_def]
  have hWmass : E.toClosedForm.form w w = ∫ x, p x ^ 2 ∂μ := by
    calc
      E.toClosedForm.form w w = (Gamma.measure w Set.univ).toReal :=
        (Gamma.measure_univ w hw).symm
      _ = ∫ x, p x ^ 2 ∂μ := hTmass
  have hIntExpand :
      (∫ x, (1 + p x) ^ 2 ∂μ) =
        (∫ x, (1 : ℝ) ∂μ) + 2 * (∫ x, p x ∂μ) +
          ∫ x, p x ^ 2 ∂μ := by
    calc
      (∫ x, (1 + p x) ^ 2 ∂μ) =
          ∫ x, ((1 : ℝ) + 2 * p x) + p x ^ 2 ∂μ := by
            apply integral_congr_ae
            filter_upwards [] with x
            ring
      _ = (∫ x, (1 : ℝ) + 2 * p x ∂μ) +
          ∫ x, p x ^ 2 ∂μ := integral_add (h1_int.add h2p_int) hp_sq_int
      _ = ((∫ x, (1 : ℝ) ∂μ) + ∫ x, 2 * p x ∂μ) +
          ∫ x, p x ^ 2 ∂μ := by rw [integral_add h1_int h2p_int]
      _ = (∫ x, (1 : ℝ) ∂μ) + 2 * (∫ x, p x ∂μ) +
          ∫ x, p x ^ 2 ∂μ := by
            rw [integral_const_mul]
  have hmain :
      E.toClosedForm.form u u + 2 * E.toClosedForm.form u w +
          E.toClosedForm.form w w =
        (∫ x, (1 : ℝ) ∂μ) + 2 * (∫ x, p x ∂μ) +
          ∫ x, p x ^ 2 ∂μ := by
    calc
      E.toClosedForm.form u u + 2 * E.toClosedForm.form u w +
          E.toClosedForm.form w w =
          E.toClosedForm.form (u + w) (u + w) :=
        (E.toClosedForm.form_add_self hu hw).symm
      _ = (Gamma.measure (u + w) Set.univ).toReal :=
        (Gamma.measure_univ (u + w) (E.toClosedForm.domain.add_mem hu hw)).symm
      _ = ∫ x, (1 + p x) ^ 2 ∂μ := hSmass
      _ = (∫ x, (1 : ℝ) ∂μ) + 2 * (∫ x, p x ∂μ) +
          ∫ x, p x ^ 2 ∂μ := hIntExpand
  rw [hUmass, hWmass] at hmain
  linarith



theorem obl_BH_compact_preimage_nullity
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : _root_.DirichletForm
      (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    (halg : DirichletForm.IsCoreAlgebra E.toClosedForm)
    (hnc : DirichletForm.HasNormalContractions E)
    (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hv : v ∈ E.toClosedForm.domain)
    (vc : SpatialCoordinates d → ℝ) (hvc : Continuous vc)
    (hrep : (⇑v =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] vc)) :
    ∀ N : Set ℝ, MeasurableSet N → volume N = 0 →
      Gamma.measure v (vc ⁻¹' N) = 0 := by
  have hcompact : ∀ K : Set ℝ, IsCompact K → volume K = 0 →
      Gamma.measure v (vc ⁻¹' K) = 0 := by
    intro K hK hKnull
    obtain ⟨U, phi, hU, hphi⟩ :=
      aux_obl_BH_compact_preimage_nullity_cutoffs K hK hKnull
    have hU' : ∀ n : ℕ,
        IsOpen (U n) ∧ K ⊆ U n ∧
          volume.real (U n) ≤ 1 / ((n : ℝ) + 1) := by
      intro n
      exact ⟨(hU n).1, (hU n).2.1, (hU n).2.2.1⟩
    have hUfinite : ∀ n : ℕ, volume (U n) ≠ ⊤ := by
      intro n
      exact (hU n).2.2.2
    obtain ⟨T, w, hT, hTb, hw, henergy, hnorm, hweak⟩ :=
      obl_BH_cutoff_weak_form E hnc K U phi hU' hUfinite hphi v hv vc hvc hrep
    have hBmeas : MeasurableSet (vc ⁻¹' K) :=
      hvc.measurable hK.isClosed.measurableSet
    have hBfinite : Gamma.measure v (vc ⁻¹' K) ≠ ⊤ :=
      Gamma.measure_ne_top hv _
    have hBreal_nonneg : 0 ≤ (Gamma.measure v (vc ⁻¹' K)).toReal :=
      ENNReal.toReal_nonneg
    have hBreal_le_zero : (Gamma.measure v (vc ⁻¹' K)).toReal ≤ 0 := by
      refine ge_of_tendsto (hweak v hv) ?_
      filter_upwards [] with n
      let f : SpatialCoordinates d → ℝ := fun x => phi n (vc x)
      have hfcont : Continuous f := (hphi n).1.continuous.comp hvc
      have hfbnd : ∀ x, |f x| ≤ 1 := by
        intro x
        dsimp [f]
        rcases (hphi n).2.1 (vc x) with ⟨hx0, hx1⟩
        exact abs_le.mpr ⟨by linarith, hx1⟩
      have hfint : Integrable f (Gamma.measure v) := by
        exact DirichletForm.integrable_of_energyMeasure Gamma hfcont hfbnd hv
      have hfnonneg : 0 ≤ᵐ[Gamma.measure v] f :=
        Filter.Eventually.of_forall (fun x => by
          dsimp [f]
          exact (hphi n).2.1 (vc x) |>.1)
      have hmeasure : Gamma.measure v (vc ⁻¹' K) ≤
          ENNReal.ofReal (∫ x, f x ∂(Gamma.measure v)) :=
        hfint.measure_le_integral hfnonneg (s := vc ⁻¹' K) (by
        intro x hx
        dsimp [f]
        rw [(hphi n).2.2.1 (vc x) hx])
      have hint_nonneg : 0 ≤ ∫ x, f x ∂(Gamma.measure v) :=
        integral_nonneg_of_ae hfnonneg
      have hle_real :
          (Gamma.measure v (vc ⁻¹' K)).toReal ≤
            E.toClosedForm.form v (w n) := by
        calc
          (Gamma.measure v (vc ⁻¹' K)).toReal ≤
              (ENNReal.ofReal (∫ x, f x ∂(Gamma.measure v))).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
          _ = ∫ x, f x ∂(Gamma.measure v) :=
            ENNReal.toReal_ofReal hint_nonneg
          _ = E.toClosedForm.form v (w n) := by
            simpa [f] using (aux_obl_BH_compact_preimage_nullity_pairing E Gamma v hv vc hvc hrep
              (T n) (phi n) (hTb n).1 (by
                intro s
                have heq : T n = fun t => ∫ z in (0 : ℝ)..t, phi n z :=
                  funext (hT n)
                rw [heq]
                exact ((hphi n).1.continuous.integral_hasStrictDerivAt 0 s).hasDerivAt)
              (by
                apply contDiff_one_iff_deriv.mpr
                refine ⟨(fun s => ?_), ?_⟩
                · have heq : T n = fun t => ∫ z in (0 : ℝ)..t, phi n z :=
                    funext (hT n)
                  rw [heq]
                  exact ((hphi n).1.continuous.integral_hasStrictDerivAt 0 s).hasDerivAt.differentiableAt
                · have hderiv : deriv (T n) = phi n := by
                    funext s
                    have heq : T n = fun t => ∫ z in (0 : ℝ)..t, phi n z :=
                      funext (hT n)
                    rw [heq]
                    exact Continuous.deriv_integral (phi n) (hphi n).1.continuous
                      (0 : ℝ) s
                  rw [hderiv]
                  exact (hphi n).1.continuous)
              (w n) (hw n).1 (hw n).2
              (hphi n).1.continuous (fun s => by
                rcases (hphi n).2.1 s with ⟨hs0, hs1⟩
                exact abs_le.mpr ⟨by linarith, hs1⟩))
      exact hle_real
    have hBreal_zero : (Gamma.measure v (vc ⁻¹' K)).toReal = 0 :=
      le_antisymm hBreal_le_zero hBreal_nonneg
    exact (measureReal_eq_zero_iff hBfinite).mp hBreal_zero
  intro N hN hNnull
  have hNpremeas : MeasurableSet (vc ⁻¹' N) := hvc.measurable hN
  let μ : Measure (SpatialCoordinates d) := Gamma.measure v
  letI : (Gamma.measure v).Regular := Gamma.regular v hv
  rw [hNpremeas.measure_eq_iSup_isCompact_of_ne_top (Gamma.measure_ne_top hv _)]
  simp only [ENNReal.iSup_eq_zero]
  intro K hKsub hKcompact
  have hKimage_compact : IsCompact (vc '' K) := hKcompact.image hvc
  have hKimage_null : volume (vc '' K) = 0 := by
    apply measure_mono_null
    · rintro y ⟨x, hx, rfl⟩
      exact hKsub hx
    · exact hNnull
  have hpreimage_image := hcompact (vc '' K) hKimage_compact hKimage_null
  apply measure_mono_null (s := K) (t := vc ⁻¹' (vc '' K))
    (fun x hx => ⟨x, hx, rfl⟩) hpreimage_image

end Paper
