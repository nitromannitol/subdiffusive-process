module

public import SubdiffusiveProcess.Paper.Foundations.AuditExports.InfraredFamilyTransport
public import SubdiffusiveProcess.Paper.Foundations.AuditExports.InfraredFamilyMicroscopic
public import Mathlib.MeasureTheory.Function.LpOrder
public import SubdiffusiveProcess.Paper.inputs_simultaneous

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric Filter
open SubdiffusiveProcess SubdiffusiveProcess.Paper SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff Topology

noncomputable section
namespace SubdiffusiveProcess.AuditExports

/-- The common Neumann regularity bank on every fixed cube, for the limit,
zero infrared and every positive-layer truncation. The threshold precedes
the cube; the bank and all numerical moment bounds precede the family index. -/
theorem infrared_family_neumann_cubes
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (X : in_extension d hd E)
    (W : SmallPerturbationInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Cp : CampanatoInput d) (t alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ)
    (ht1 : (d : ℝ) - 1 < t) (htd : t < d)
    (ha0 : 0 < alpha) (ha1 : alpha < 1) (hps : ∀ i, 1 ≤ ps i) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      ∃ (K : ℕ → BilateralField d → ℝ) (Cb : Fin k → ℝ),
        (∀ N om, 0 ≤ K N om) ∧
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cb i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ idx : Option ℕ, ∀ N : ℕ,
          aux_lem_as_regularity_nc_estimate z r hr
            (cutoffPositiveCoefficient M (infraredFamily H idx) om N z hr) t alpha (K N om) := by
  classical
  obtain ⟨dh, hdh, hhigh⟩ := infrared_family_affine_high d hd E P X W D Cp t alpha k ps
    ht1 htd ha0 ha1 hps
  obtain ⟨ds, hds, hsmall⟩ := infrared_family_microscopic_prefix d hd E P W Cp t alpha
    ht1 htd ha0 ha1 k ps hps
  refine ⟨min dh ds, lt_min hdh hds, ?_⟩
  intro M Rm Sreg It H hH hdelta z r hr
  obtain ⟨m, rho, hrho, hreq⟩ := aux_lem_as_regularity_nc_octave_decompose r hr
  obtain ⟨KH, CH, hKH, hKHL, hKHB, hHAE⟩ := hhigh M Rm Sreg It H hH
    (hdelta.trans (min_le_left _ _)) z r hr m rho
    (by linarith [hrho.1]) (by linarith [hrho.2]) hreq
  by_cases hm : m + 1 ≤ 0
  · refine ⟨KH, CH, hKH, hKHL, hKHB, ?_⟩
    filter_upwards [hHAE] with om hom idx N
    exact hom idx N (by omega)
  · let mp : ℕ := (m + 1).toNat
    let mn : ℕ := m.toNat
    have hmn : (mn : ℤ) = m := by dsimp [mn]; omega
    have hrmn : (3 : ℝ) ^ mn * r = rho := by
      rw [hreq, ← zpow_natCast, hmn, ← mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      simp only [add_neg_cancel, zpow_zero, one_mul]
    have hr1 : r ≤ 1 := by
      have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ mn := one_le_pow₀ (by norm_num)
      nlinarith [hrho.2]
    have hrprefix : ∀ N : ℕ, N < mp → (3 : ℝ) ^ N * r ≤ 1 := by
      intro N hN
      have hNmn : N ≤ mn := by dsimp [mp, mn] at *; omega
      calc _ ≤ (3 : ℝ) ^ mn * r :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hNmn) hr.le
        _ ≤ 1 := hrmn.le.trans hrho.2
    obtain ⟨KS, CS, hKS, hKSL, hKSB, hSAE⟩ := hsmall M Rm H hH
      (hdelta.trans (min_le_right _ _)) z r hr hr1 mp hrprefix
    refine ⟨fun N om => KH N om + KS N om, fun i => max (CH i) 0 + max (CS i) 0,
      fun N om => add_nonneg (hKH N om) (hKS N om),
      fun i N => (hKHL i N).add (hKSL i N), ?_, ?_⟩
    · intro i N
      have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (ps i) := by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hps i)
      calc _ ≤ eLpNorm (KH N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure +
          eLpNorm (KS N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure := eLpNorm_add_le hp
        _ ≤ ENNReal.ofReal (max (CH i) 0) + ENNReal.ofReal (max (CS i) 0) :=
          add_le_add ((hKHB i N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
            ((hKSB i N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
        _ = _ := (ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)).symm
    · filter_upwards [hHAE, hSAE] with om hh hs idx N
      by_cases hN : m + 1 ≤ (N : ℤ)
      · exact aux_lem_as_regularity_nc_estimate_mono
          (le_add_of_nonneg_right (hKS N om)) (hh idx N hN)
      · have hNp : N < mp := by dsimp [mp]; omega
        exact aux_lem_as_regularity_nc_estimate_mono
          (le_add_of_nonneg_left (hKH N om)) (hs idx N hNp)

/-- Zero infrared is stationary under the exact spatial field translation. -/
theorem cutoffCoefficient_zero_translate {d : ℕ}
    (M : SubdiffusiveProcess.Model.GMCModel d) (w x : SpatialCoordinates d)
    (om : BilateralField d) (N : ℕ) :
    cutoffCoefficient M 0 (aux_transport_S 0 w om) N x = cutoffCoefficient M 0 om N (w + x) := by
  unfold cutoffCoefficient cutoffPotential
  simp only [Pi.zero_apply, ContinuousMap.zero_apply, zero_add]
  congr 2
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [aux_transport_S_apply]
  simp only [sub_zero, neg_zero, zpow_zero, one_smul]

/-- Pure translation preserves the exact bounded-source Neumann estimates.
The two affine transports use the same unit datum, so every dilation factor
cancels, including in the localized energy. -/
theorem neumann_estimate_zero_translate {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Model.GMCModel d) (om : BilateralField d) (N : ℕ)
    (z w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (t alpha K : ℝ) (ha : 0 ≤ alpha)
    (hest : aux_lem_as_regularity_nc_estimate z r hr
      (cutoffPositiveCoefficient M 0 (aux_transport_S 0 w om) N z hr) t alpha K) :
    aux_lem_as_regularity_nc_estimate (z + w) r hr
      (cutoffPositiveCoefficient M 0 om N (z + w) hr) t alpha K := by
  let z0 : SpatialCoordinates d := fun _ => (1 / 2 : ℝ)
  let zn : SpatialCoordinates d := z + w
  let Tn : SpatialCoordinates d → SpatialCoordinates d := cubeDilation zn z0 r
  let Tb : SpatialCoordinates d → SpatialCoordinates d := cubeDilation z z0 r
  let Inv : SpatialCoordinates d → SpatialCoordinates d := cubeDilation z0 zn r⁻¹
  let tr : SpatialCoordinates d → SpatialCoordinates d := cubeDilation z zn 1
  let a := cutoffPositiveCoefficient M 0 (aux_transport_S 0 w om) N z hr
  have hmaps : ∀ y, Tb (Inv y) = tr y := by
    intro y
    funext i
    simp only [Tb, Inv, tr, cubeDilation_apply]
    dsimp [zn]
    field_simp
    ring
  have hpoints : ∀ x, Tn x = w + Tb x := by
    intro x
    funext i
    simp only [Tn, Tb, cubeDilation_apply, Pi.add_apply]
    dsimp [zn]
    ring
  obtain ⟨a1, ha1, -, hNeu⟩ := lem_as_regularity_affine_transport d M 0 om N zn r hr
  have hqb := dilation_quasi_measure_preserving d z z0 r hr one_pos
  have hqn := dilation_quasi_measure_preserving d zn z0 r hr one_pos
  have hqi := aux_prop_growth_large_root_qmp_inv zn z0 hr
  have hcoef : ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      a1.val x = a.val (Tb x) := by
    filter_upwards [ha1, hqn.ae (aux_fscc_holNeuH_cutoffPos_val M 0 om N zn hr),
      hqb.ae (aux_fscc_holNeuH_cutoffPos_val M 0 (aux_transport_S 0 w om) N z hr)]
      with x hx1 hx2 hx3
    rw [hx1, hx2, hx3, cutoffCoefficient_zero_translate, ← hpoints]
  intro F Kf hKf hFm hFb hFz v hsol
  obtain ⟨F1, v1, -, hF1m, hF1b, hF1z, hsol1, hv1, -, henergy⟩ :=
    hNeu F Kf hKf hFm hFb hFz v hsol
  obtain ⟨vb, hvb, hgradb⟩ := aux_lem_as_regularity_nc_meanzero_pushforward z z0 r hr v1
  let Fb : SpatialCoordinates d → ℝ := fun y => (r ^ 2)⁻¹ * F1 (cubeDilation z0 z r⁻¹ y)
  have hqbi := aux_prop_growth_large_root_qmp_inv z z0 hr
  have hFbm : AEMeasurable Fb (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    (hF1m.comp_quasiMeasurePreserving hqbi).const_mul _
  have hFbb : ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), |Fb y| ≤ Kf := by
    filter_upwards [hqbi.ae hF1b] with y hy
    dsimp only [Fb]
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
    have hh := mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr (sq_nonneg r))
    simpa only [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hr.ne'), one_mul] using hh
  have hFbz : (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), Fb y) = 0 := by
    have hs := aux_lem_as_regularity_affine_transport_integral_scaling d z z0 r hr one_pos Fb hFbm
    have hz : (∫ x in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)), Fb (Tb x)) = 0 := by
      simp only [Fb, Tb, aux_prop_growth_large_root_cubeDilation_inv_right z z0 hr,
        integral_const_mul]
      change (r ^ 2)⁻¹ * (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F1 x) = 0
      rw [hF1z, mul_zero]
    rw [hs] at hz
    exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero (pow_ne_zero _ hr.ne'))
  have hsolb := aux_lem_as_regularity_nc_neumann_pushforward z z0 r hr a a1 hcoef
    F1 hF1m vb v1 hvb hsol1
  obtain ⟨⟨U, hUc, hUH, hUae, hUn⟩, hEn⟩ := hest Fb Kf hKf hFbm hFbb hFbz vb hsolb
  have htrans := aux_prop_growth_large_root_holder_transport_gen zn z hr hr
    (lam := 1) le_rfl (by ring) ha U hUc hUH
  simp only [inv_one] at htrans
  refine ⟨⟨fun y => U (tr y), htrans.1, htrans.2.1, ?_, htrans.2.2.trans hUn⟩, ?_⟩
  · filter_upwards [hqi.ae hv1, hqi.ae hvb, hqi.ae (hqb.ae hUae)] with y hyn hyb hyU
    change ((v1 : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) (Inv y) =
      ((v : SobolevData (centeredCube zn r hr)).1 : SpatialCoordinates d → ℝ) (Tn (Inv y)) at hyn
    have hTny : Tn (Inv y) = y := aux_prop_growth_large_root_cubeDilation_inv_left zn z0 hr y
    rw [hTny] at hyn
    have hh := hyn.symm.trans (hyb.trans hyU)
    change ((v : SobolevData (centeredCube zn r hr)).1 : SpatialCoordinates d → ℝ) y =
      U (Tb (Inv y)) at hh
    simpa only [hmaps] using hh
  · intro x rad hx hrad hrad1
    let x1 := Inv x
    have hx1 : x1 ∈ centeredCube z0 1 one_pos :=
      aux_prop_growth_large_root_cubeDilation_inv_mem_centeredCube zn z0 hr hx
    have hxb : Tb x1 ∈ centeredCube z r hr := by
      change x1 ∈ (cubeDilation z z0 r) ⁻¹' (centeredCube z r hr : Set (SpatialCoordinates d))
      rwa [cubeDilation_preimage_centeredCube z z0 hr one_pos]
    have hEb := aux_lem_as_regularity_affine_transport_local_energy_scaling d z z0 r hr one_pos
      a a1 (sobolevGradient (vb : SobolevData (centeredCube z r hr)))
      (sobolevGradient (v1 : SobolevData (unitNeumannCube d)))
      hcoef hgradb x1 (rad / r) (div_pos hrad hr)
    have hEnw := henergy x1 (rad / r) (div_pos hrad hr)
    have hTx : cubeDilation zn z0 r x1 = x :=
      aux_prop_growth_large_root_cubeDilation_inv_left zn z0 hr x
    have hrr : r * (rad / r) = rad := mul_div_cancel₀ rad hr.ne'
    rw [hTx, hrr] at hEnw
    rw [hrr] at hEb
    have heq := (mul_left_cancel₀ (Real.rpow_pos_of_pos hr ((2 : ℝ) - d)).ne')
      (hEnw.symm.trans hEb)
    exact heq.trans_le (hEn (Tb x1) rad hxb hrad hrad1)

/-- Maximum of finitely many nonnegative translated constants, with zero
adjoined so the empty collection is also covered. -/
def translatedBankMaximum {d : ℕ} {I : Type*} [Fintype I]
    (K : ℕ → BilateralField d → ℝ) (shift : I → SpatialCoordinates d)
    (N : ℕ) : BilateralField d → ℝ :=
  (Finset.univ : Finset (Option I)).sup' ⟨none, Finset.mem_univ _⟩
    (fun j => j.elim 0 (fun i om => K N (aux_transport_S 0 (shift i) om)))

/-- A finite maximum of scalar finite-moment functions has the same moment
order. This is a lattice closure lemma, not a model-specific bank premise. -/
theorem memLp_finset_sup_functions
    {Ω I : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p : ℝ≥0∞)
    (s : Finset I) (f : I → Ω → ℝ) (hs : s.Nonempty)
    (hf : ∀ i ∈ s, MemLp (f i) p μ) : MemLp (s.sup' hs f) p μ := by
  classical
  revert hs hf
  induction s using Finset.induction_on with
  | empty => intro hs; simp at hs
  | @insert i s hi ih =>
    intro hs hf
    by_cases hse : s.Nonempty
    · rw [Finset.sup'_insert hse]
      exact (hf i (Finset.mem_insert_self _ _)).sup
        (ih hse (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    · have hsz : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hse
      subst s
      simpa using hf i (Finset.mem_insert_self _ _)

/-- The translated constants retain the exact original moment bounds,
and their finite maximum has the usual finite-sum bound. -/
theorem translated_neumann_bank
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Model.GMCModel d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (t alpha : ℝ) (ha : 0 ≤ alpha) (k : ℕ) (ps : Fin k → ℝ) (hps : ∀ i, 1 ≤ ps i)
    (K : ℕ → BilateralField d → ℝ) (Cb : Fin k → ℝ)
    (hK : ∀ N om, 0 ≤ K N om)
    (hKL : ∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure)
    (hKB : ∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Cb i))
    (hAE : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N,
      aux_lem_as_regularity_nc_estimate z r hr (cutoffPositiveCoefficient M 0 om N z hr)
        t alpha (K N om)) :
    (∀ w : SpatialCoordinates d,
      (∀ i N, MemLp (fun om => K N (aux_transport_S 0 w om)) (ENNReal.ofReal (ps i))
        (chaosSampleLaw M).toMeasure) ∧
      (∀ i N, eLpNorm (fun om => K N (aux_transport_S 0 w om)) (ENNReal.ofReal (ps i))
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cb i)) ∧
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N,
        aux_lem_as_regularity_nc_estimate (z + w) r hr
          (cutoffPositiveCoefficient M 0 om N (z + w) hr) t alpha
          (K N (aux_transport_S 0 w om))) ∧
    ∀ (I : Type) [Fintype I] (shift : I → SpatialCoordinates d),
      (∀ i N, MemLp (translatedBankMaximum K shift N) (ENNReal.ofReal (ps i))
        (chaosSampleLaw M).toMeasure) ∧
      (∀ i N, eLpNorm (translatedBankMaximum K shift N) (ENNReal.ofReal (ps i))
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal ((Fintype.card I : ℝ) * max (Cb i) 0)) ∧
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ j : I, ∀ N,
        aux_lem_as_regularity_nc_estimate (z + shift j) r hr
          (cutoffPositiveCoefficient M 0 om N (z + shift j) hr) t alpha
          (translatedBankMaximum K shift N om) := by
  classical
  have hsingle : ∀ w : SpatialCoordinates d,
      (∀ i N, MemLp (fun om => K N (aux_transport_S 0 w om)) (ENNReal.ofReal (ps i))
        (chaosSampleLaw M).toMeasure) ∧
      (∀ i N, eLpNorm (fun om => K N (aux_transport_S 0 w om)) (ENNReal.ofReal (ps i))
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cb i)) ∧
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N,
        aux_lem_as_regularity_nc_estimate (z + w) r hr
          (cutoffPositiveCoefficient M 0 om N (z + w) hr) t alpha
          (K N (aux_transport_S 0 w om)) := by
    intro w
    have hS := aux_transport_S_measurePreserving M 0 w
    refine ⟨fun i N => (hKL i N).comp_measurePreserving hS, ?_, ?_⟩
    · intro i N
      have heq := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal (ps i))
        (hKL i N).aestronglyMeasurable hS
      exact heq.trans_le (hKB i N)
    · filter_upwards [hS.quasiMeasurePreserving.ae hAE] with om hom N
      exact neumann_estimate_zero_translate M om N z w r hr t alpha (K N (aux_transport_S 0 w om))
        ha (hom N)
  refine ⟨hsingle, ?_⟩
  intro I _ shift
  let Sum : ℕ → BilateralField d → ℝ := fun N om => ∑ j : I, K N (aux_transport_S 0 (shift j) om)
  have hsum0 : ∀ N om, 0 ≤ Sum N om := fun N om => Finset.sum_nonneg (fun j _ => hK N _)
  have hmax0 : ∀ N om, 0 ≤ translatedBankMaximum K shift N om := by
    intro N om
    have hh := Finset.le_sup' (f := fun j : Option I => j.elim (0 : BilateralField d → ℝ)
      (fun j om => K N (aux_transport_S 0 (shift j) om))) (Finset.mem_univ none)
    exact hh om
  have hmaxSum : ∀ N om, translatedBankMaximum K shift N om ≤ Sum N om := by
    intro N om
    have hh : (Finset.univ : Finset (Option I)).sup' ⟨none, Finset.mem_univ _⟩
        (fun j => j.elim (0 : BilateralField d → ℝ)
          (fun i om => K N (aux_transport_S 0 (shift i) om))) ≤ Sum N := by
      apply Finset.sup'_le
      intro j _ om
      cases j with
      | none => exact hsum0 N om
      | some j =>
        exact Finset.single_le_sum
          (f := fun i : I => K N (aux_transport_S 0 (shift i) om))
          (fun i _ => hK N _) (Finset.mem_univ j)
    exact hh om
  have hmaxL : ∀ i N, MemLp (translatedBankMaximum K shift N) (ENNReal.ofReal (ps i))
      (chaosSampleLaw M).toMeasure := by
    intro i N
    apply memLp_finset_sup_functions
    intro j _
    cases j with
    | none => exact memLp_const 0
    | some j => exact (hsingle (shift j)).1 i N
  have hsumB : ∀ i N, eLpNorm (Sum N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((Fintype.card I : ℝ) * max (Cb i) 0) := by
    intro i N
    have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (ps i) := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hps i)
    calc _ ≤ ∑ j : I, eLpNorm (fun om => K N (aux_transport_S 0 (shift j) om))
          (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure :=
        by simpa only [Finset.sum_fn, Sum] using
          eLpNorm_sum_le (μ := (chaosSampleLaw M).toMeasure)
            (s := Finset.univ) (f := fun j : I => fun om => K N (aux_transport_S 0 (shift j) om)) hp
      _ ≤ ∑ _j : I, ENNReal.ofReal (max (Cb i) 0) := Finset.sum_le_sum (fun j _ =>
        ((hsingle (shift j)).2.1 i N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
      _ = ENNReal.ofReal ((Fintype.card I : ℝ) * max (Cb i) 0) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => le_max_right (Cb i) 0)]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine ⟨hmaxL, ?_, ?_⟩
  · intro i N
    have hnorm := eLpNorm_mono_ae (f := translatedBankMaximum K shift N) (g := Sum N)
      (p := ENNReal.ofReal (ps i)) (hmaxL i N).aestronglyMeasurable
      (Filter.Eventually.of_forall fun om => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hmax0 N om), abs_of_nonneg (hsum0 N om)]
        exact hmaxSum N om)
    exact hnorm.trans (hsumB i N)
  · have hAll := ae_all_iff.mpr (fun j : I => (hsingle (shift j)).2.2)
    filter_upwards [hAll] with om hom j N
    have hle : K N (aux_transport_S 0 (shift j) om) ≤ translatedBankMaximum K shift N om := by
      have hh := Finset.le_sup' (f := fun j : Option I => j.elim (0 : BilateralField d → ℝ)
        (fun j om => K N (aux_transport_S 0 (shift j) om))) (Finset.mem_univ (some j))
      exact hh om
    exact aux_lem_as_regularity_nc_estimate_mono hle (hom j N)

/-- The stationary translation clauses: each translated bank has the
original moment bounds, and a finite collection uses its actual maximum. -/
def translatedNeumannClauses
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Model.GMCModel d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (t alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ)
    (K : ℕ → BilateralField d → ℝ) (Cb : Fin k → ℝ) : Prop :=
    (∀ w : SpatialCoordinates d,
      (∀ i N, MemLp (fun om => K N (aux_transport_S 0 w om)) (ENNReal.ofReal (ps i))
        (chaosSampleLaw M).toMeasure) ∧
      (∀ i N, eLpNorm (fun om => K N (aux_transport_S 0 w om)) (ENNReal.ofReal (ps i))
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cb i)) ∧
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N,
        aux_lem_as_regularity_nc_estimate (z + w) r hr
          (cutoffPositiveCoefficient M 0 om N (z + w) hr) t alpha
          (K N (aux_transport_S 0 w om))) ∧
    ∀ (I : Type) [Fintype I] (shift : I → SpatialCoordinates d),
      (∀ i N, MemLp (translatedBankMaximum K shift N) (ENNReal.ofReal (ps i))
        (chaosSampleLaw M).toMeasure) ∧
      (∀ i N, eLpNorm (translatedBankMaximum K shift N) (ENNReal.ofReal (ps i))
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal ((Fintype.card I : ℝ) * max (Cb i) 0)) ∧
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ j : I, ∀ N,
        aux_lem_as_regularity_nc_estimate (z + shift j) r hr
          (cutoffPositiveCoefficient M 0 om N (z + shift j) hr) t alpha
          (translatedBankMaximum K shift N om)

/-- Paper `mfd:cor-neumann-source`, including the author-accepted stronger
infrared-family and stationary-translation paragraph. No family regularity,
common random constant or numerical family moment bound is an input. -/
theorem neumann_source_infrared_family_of_inputs
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (X : in_extension d hd E)
    (W : SmallPerturbationInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Cp : CampanatoInput d) (t alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ)
    (ht1 : (d : ℝ) - 1 < t) (htd : t < d)
    (ha0 : 0 < alpha) (ha1 : alpha < 1) (hps : ∀ i, 1 ≤ ps i) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      ∃ (K : ℕ → BilateralField d → ℝ) (Cb : Fin k → ℝ),
        (∀ N om, 0 ≤ K N om) ∧
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cb i)) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ idx : Option ℕ, ∀ N : ℕ,
          aux_lem_as_regularity_nc_estimate z r hr
            (cutoffPositiveCoefficient M (infraredFamily H idx) om N z hr) t alpha (K N om)) ∧
        translatedNeumannClauses M z r hr t alpha k ps K Cb := by
  obtain ⟨delta0, hdelta0, hbank⟩ := infrared_family_neumann_cubes d hd E P X W D Cp t alpha
    k ps ht1 htd ha0 ha1 hps
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hH hdelta z r hr
  obtain ⟨K, Cb, hK, hKL, hKB, hAE⟩ := hbank M Rm Sreg It H hH hdelta z r hr
  have hzero : infraredFamily H (some 0) = 0 := by
    funext om
    ext x
    simp [infraredFamily, infraredPartialSum]
  have hzeroAE : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N,
      aux_lem_as_regularity_nc_estimate z r hr (cutoffPositiveCoefficient M 0 om N z hr)
        t alpha (K N om) := by
    filter_upwards [hAE] with om hom N
    simpa only [hzero] using hom (some 0) N
  exact ⟨K, Cb, hK, hKL, hKB, hAE,
    translated_neumann_bank M z r hr t alpha ha0.le k ps hps K Cb hK hKL hKB hzeroAE⟩

/-- Source-facing bounded Neumann estimates. All analytic infrastructure is
constructed internally, before the model and infrared-family choice. -/
theorem neumann_source_infrared_family
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (t alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ)
    (ht1 : (d : ℝ) - 1 < t) (htd : t < d)
    (ha0 : 0 < alpha) (ha1 : alpha < 1) (hps : ∀ i, 1 ≤ ps i) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      ∃ (K : ℕ → BilateralField d → ℝ) (Cb : Fin k → ℝ),
        (∀ N om, 0 ≤ K N om) ∧
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cb i)) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ idx : Option ℕ, ∀ N : ℕ,
          aux_lem_as_regularity_nc_estimate z r hr
            (cutoffPositiveCoefficient M (infraredFamily H idx) om N z hr) t alpha (K N om)) ∧
        translatedNeumannClauses M z r hr t alpha k ps K Cb := by
  classical
  have : NeZero d := ⟨by omega⟩
  let E : in_J d := Classical.choice (inputs_J_witness d hd)
  let P : in_poincare d hd E := Classical.choice (inputs_poincare_witness d hd E)
  let X : in_extension d hd E := Classical.choice (inputs_extension_witness d hd E)
  let W : SmallPerturbationInput d := Classical.choice (inputs_W_witness d)
  let Cp : CampanatoInput d := Classical.choice (inputs_Cp_witness d)
  obtain ⟨db, hdb, hbank⟩ := neumann_source_infrared_family_of_inputs d hd E P X W
    (inputs_deterministic_witness d hd) Cp t alpha k ps ht1 htd ha0 ha1 hps
  obtain ⟨_, dr, _, hdr, hresp⟩ := inputs_responses_witness d hd 1 le_rfl
  refine ⟨min db dr, lt_min hdb hdr, ?_⟩
  intro M H hH hdelta z r hr
  obtain ⟨Rm, _, _⟩ := hresp M (hdelta.trans (min_le_right _ _))
  exact hbank M Rm (inputs_regularity_witness d M) (inputs_iteration_witness d hd M E)
    H hH (hdelta.trans (min_le_left _ _)) z r hr

end SubdiffusiveProcess.AuditExports
