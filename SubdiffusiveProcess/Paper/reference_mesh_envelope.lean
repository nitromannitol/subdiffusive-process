module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.lem_infrared
public import SubdiffusiveProcess.Paper.in_common_scale_coupling
public import SubdiffusiveProcess.Paper.reference_point_moments
public import SubdiffusiveProcess.Paper.reference_oscillation_moments
public import SubdiffusiveProcess.Probability.MeshEnvelope
public import SubdiffusiveProcess.Probability.GrowingMeshEnvelope
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import SubdiffusiveProcess.Main.InfraredAdmissible

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter Metric
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators

namespace SubdiffusiveProcess.Paper

lemma aux_reference_mesh_envelope_discount
    (A beta delta : ℝ) (k : ℕ)
    (_hA : 0 ≤ A) (_hbeta : 0 ≤ beta) (_hdelta : 0 ≤ delta)
    (hbound : A * delta ^ 2 ≤ beta * Real.log 3) :
    (3 : ℝ) ^ (-beta * (k : ℝ)) * Real.exp (A * delta ^ 2 * (k : ℝ)) ≤ 1 := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  rw [← Real.exp_add]
  apply (Real.exp_le_one_iff).2
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hnonpos : A * delta ^ 2 - beta * Real.log 3 ≤ 0 := by linarith
  have hprod : (A * delta ^ 2 - beta * Real.log 3) * (k : ℝ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hnonpos hk
  convert hprod using 1 ; ring

lemma aux_reference_mesh_envelope_finset_lub
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) :
    IsLUB {v : ℝ | ∃ i ∈ s, v = f i} (s.sup' hs f) := by
  refine ⟨?_, ?_⟩
  · rintro v ⟨i, hi, rfl⟩
    exact Finset.le_sup' f hi
  · intro b hb
    exact Finset.sup'_le hs f (fun i hi => hb ⟨i, hi, rfl⟩)

lemma aux_reference_mesh_envelope_point_norm
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (a B : ℝ) (ha : 0 < a) (_hB : 0 ≤ B)
    (s : Ω → ℝ) (hspos : ∀ ω, 0 < s ω)
    (hs : MemLp s (ENNReal.ofReal a) μ)
    (hsi : MemLp (fun ω => (s ω)⁻¹) (ENNReal.ofReal a) μ)
    (hint : Integrable (fun ω => (s ω)^a + (s ω)^(-a)) μ)
    (hmoment : (∫ ω, (s ω)^a + (s ω)^(-a) ∂μ) ^ (1 / a) ≤ B) :
    eLpNorm s (ENNReal.ofReal a) μ ≤ ENNReal.ofReal B ∧
      eLpNorm (fun ω => (s ω)⁻¹) (ENNReal.ofReal a) μ ≤ ENNReal.ofReal B := by
  have hpa : ENNReal.ofReal a ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr ha)
  have hpt : ENNReal.ofReal a ≠ ∞ := ENNReal.ofReal_ne_top
  have hnorms : ∀ ω, ‖s ω‖ = s ω ∧ ‖(s ω)⁻¹‖ = (s ω)⁻¹ := by
    intro ω
    exact ⟨abs_of_pos (hspos ω), abs_of_pos (inv_pos.mpr (hspos ω))⟩
  have hspow : Integrable (fun ω => ‖s ω‖ ^ (ENNReal.ofReal a).toReal) μ :=
    hs.integrable_norm_rpow hpa hpt
  have hsipow : Integrable
      (fun ω => ‖(s ω)⁻¹‖ ^ (ENNReal.ofReal a).toReal) μ :=
    hsi.integrable_norm_rpow hpa hpt
  have ha_toReal : (ENNReal.ofReal a).toReal = a := ENNReal.toReal_ofReal ha.le
  have hspow' : Integrable (fun ω => (s ω)^a) μ := by
    simpa [hnorms, ha_toReal] using hspow
  have hsipow' : Integrable (fun ω => (s ω)⁻¹ ^ a) μ := by
    simpa [hnorms, ha_toReal] using hsipow
  have hnonneg_sum : 0 ≤ᶠ[ae μ] (fun ω => (s ω)^a + (s ω)^(-a)) :=
    Filter.Eventually.of_forall (fun ω =>
      add_nonneg (Real.rpow_nonneg (le_of_lt (hspos ω)) a)
        (Real.rpow_nonneg (le_of_lt (hspos ω)) (-a)))
  have hsplit :
      ∫ ω, (s ω)^a ∂μ ≤ ∫ ω, (s ω)^a + (s ω)^(-a) ∂μ := by
    apply integral_mono_ae hspow' hint
    filter_upwards [] with ω
    exact le_add_of_nonneg_right
      (Real.rpow_nonneg (le_of_lt (hspos ω)) (-a))
  have hsplit_inv :
      ∫ ω, (s ω)⁻¹ ^ a ∂μ ≤ ∫ ω, (s ω)^a + (s ω)^(-a) ∂μ := by
    apply integral_mono_ae hsipow' hint
    filter_upwards [] with ω
    rw [Real.rpow_neg_eq_inv_rpow]
    exact le_add_of_nonneg_left
      (Real.rpow_nonneg (le_of_lt (hspos ω)) a)
  have hroot : 0 ≤ (∫ ω, (s ω)^a + (s ω)^(-a) ∂μ) := by
    exact integral_nonneg_of_ae hnonneg_sum
  have hsroot :
      (∫ ω, (s ω)^a ∂μ) ^ (1 / a) ≤
        (∫ ω, (s ω)^a + (s ω)^(-a) ∂μ) ^ (1 / a) := by
    exact Real.rpow_le_rpow
      (integral_nonneg (fun ω => Real.rpow_nonneg (le_of_lt (hspos ω)) a)) hsplit
      (by positivity)
  have hsiroot :
      (∫ ω, (s ω)⁻¹ ^ a ∂μ) ^ (1 / a) ≤
        (∫ ω, (s ω)^a + (s ω)^(-a) ∂μ) ^ (1 / a) := by
    exact Real.rpow_le_rpow
      (integral_nonneg (fun ω =>
        Real.rpow_nonneg (le_of_lt (inv_pos.mpr (hspos ω))) a)) hsplit_inv
      (by positivity)
  have hs_bound : eLpNorm s (ENNReal.ofReal a) μ ≤ ENNReal.ofReal B := by
    rw [hs.eLpNorm_eq_integral_rpow_norm hpa hpt]
    rw [ha_toReal]
    rw [show (fun ω => ‖s ω‖ ^ a) = (fun ω => (s ω)^a) by
      funext ω; rw [(hnorms ω).1]]
    exact (ENNReal.ofReal_le_ofReal (by simpa only [one_div] using hsroot.trans hmoment))
  have hsi_bound :
      eLpNorm (fun ω => (s ω)⁻¹) (ENNReal.ofReal a) μ ≤ ENNReal.ofReal B := by
    rw [hsi.eLpNorm_eq_integral_rpow_norm hpa hpt]
    rw [ha_toReal]
    rw [show (fun ω => ‖(s ω)⁻¹‖ ^ a) = (fun ω => (s ω)⁻¹ ^ a) by
      funext ω; rw [(hnorms ω).2]]
    exact (ENNReal.ofReal_le_ofReal (by simpa only [one_div] using hsiroot.trans hmoment))
  exact ⟨hs_bound, hsi_bound⟩

lemma aux_reference_mesh_envelope_product
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (q : ℝ) (hq : 0 < q) {X Y : Ω → ℝ}
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) :
    eLpNorm (fun ω => X ω * Y ω) (ENNReal.ofReal q) μ ≤
      eLpNorm X (ENNReal.ofReal (2 * q)) μ *
        eLpNorm Y (ENNReal.ofReal (2 * q)) μ := by
  have hholderReal : Real.HolderTriple (2 * q) (2 * q) q := by
    constructor
    · field_simp
      ring
    · positivity
    · positivity
  let : ENNReal.HolderTriple (2 * ENNReal.ofReal q)
      (2 * ENNReal.ofReal q) (ENNReal.ofReal q) := by
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_ofNat] using hholderReal.ennrealOfReal
  simpa using
    (eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      (fun x y : ℝ => x * y) 1 (continuous_fst.mul continuous_snd) hX hY
      (Filter.Eventually.of_forall fun _ => by simp))

lemma aux_reference_mesh_envelope_point_norm_fixed
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : Measure (BilateralField d)) (a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (s : BilateralField d → ℝ) (hspos : ∀ ω, 0 < s ω)
    (hs : MemLp s (ENNReal.ofReal a) P)
    (hsi : MemLp (fun ω => (s ω)⁻¹) (ENNReal.ofReal a) P)
    (hint : Integrable (fun ω => (s ω)^a + (s ω)^(-a)) P)
    (hmoment : (∫ ω, (s ω)^a + (s ω)^(-a) ∂P) ^ (1 / a) ≤ B) :
    eLpNorm s (ENNReal.ofReal a) P ≤ ENNReal.ofReal B ∧
      eLpNorm (fun ω => (s ω)⁻¹) (ENNReal.ofReal a) P ≤ ENNReal.ofReal B := by
  exact aux_reference_mesh_envelope_point_norm P a B ha hB s hspos hs hsi hint hmoment

lemma aux_reference_mesh_envelope_target_factor
    (eta : ℝ) (heta : 0 ≤ eta) (k : ℕ) :
    ((3 : ℝ)^(-(k : ℤ)) / 2)^eta * (3 : ℝ)^(eta * (k : ℝ)) ≤ 1 := by
  rw [Real.div_rpow (zpow_nonneg (by norm_num) _) (by norm_num) eta]
  have hpow : ((3 : ℝ)^(-(k : ℤ)))^eta = (3 : ℝ)^(-(k : ℝ) * eta) := by
    rw [← Real.rpow_intCast]
    rw [← Real.rpow_mul (by norm_num)]
    congr 1
    norm_num
  rw [hpow]
  have h2 : 1 ≤ (2 : ℝ)^eta := by
    exact Real.one_le_rpow (by norm_num) heta
  have hprod : (3 : ℝ)^(-(k : ℝ) * eta) *
      (3 : ℝ)^(eta * (k : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    ring
    rw [Real.rpow_zero]
  calc
    (3 : ℝ)^(-(k : ℝ) * eta) / 2 ^ eta *
        3 ^ (eta * (k : ℝ)) =
        ((3 : ℝ)^(-(k : ℝ) * eta) *
          3 ^ (eta * (k : ℝ))) / 2 ^ eta := by ring
    _ = 1 / 2 ^ eta := by rw [hprod]
    _ ≤ 1 := by
      have hden : 0 < (2 : ℝ)^eta := Real.rpow_pos_of_pos (by norm_num) _
      exact (div_le_iff₀ hden).2 (by simpa using h2)

lemma aux_reference_mesh_envelope_gap_identity
    (d q eta : ℝ) (hq : q ≠ 0) :
    d * Real.log 3 + q * (eta - d / q) * Real.log 3 =
      q * eta * Real.log 3 := by
  field_simp [hq]
  ring

lemma aux_reference_mesh_envelope_assembly
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q eta : ℝ) (_hqpos : 0 < q)
    {Grid : ℕ → Type*} [(k : ℕ) → Fintype (Grid k)] [Nonempty (Grid 0)]
    (kcard : ℕ → ℕ)
    (Rfun : ℕ → ℝ)
    (Zfun : ∀ _N k : ℕ, Ω → Grid k → ℝ)
    (egrid : ∀ n : ℕ, Fin (kcard n) → Grid n)
    (hegrid_surj : ∀ (n : ℕ) (a : Grid n), ∃ i, egrid n i = a)
    (Zbank : ∀ _N n : ℕ, Fin (kcard n) → Ω → ℝ)
    (hZbank_eq : ∀ (N n : ℕ) (i : Fin (kcard n)), n ≤ N →
      Zbank N n i = (fun omega => Zfun N n omega (egrid n i)))
    (hZmem : ∀ (N k : ℕ) (a : Grid k), k ≤ N →
      MemLp (Zfun N k · a) (ENNReal.ofReal q) μ)
    (KV : ℝ≥0∞) (CV : ℝ) (hKV : KV ≤ ENNReal.ofReal CV)
    (hgrowth_norm : ∀ N : ℕ, ∃ W : Ω → ℝ,
      MemLp W (ENNReal.ofReal p) μ ∧
      (∀ᵐ omega ∂μ, 0 ≤ W omega ∧
        ∀ n : ℕ, ∀ i : Fin (kcard n),
          |Zbank N n i omega| ≤ W omega * (3 : ℝ) ^ (eta * n)) ∧
      eLpNorm W (ENNReal.ofReal p) μ ≤ KV)
    (hRnonneg : ∀ k : ℕ, 0 ≤ Rfun k ^ eta)
    (hfactor : ∀ k : ℕ,
      Rfun k ^ eta * (3 : ℝ) ^ (eta * (k : ℝ)) ≤ 1)
    (hTarg_nonneg : ∀ (N : ℕ) (i : Σ k : Fin (N + 1), Grid k.1)
        (omega : Ω),
      0 ≤ Rfun i.1.1 ^ eta * Zfun N i.1.1 omega i.2) :
    ∃ V : ℕ → Ω → ℝ,
      (∀ N, Measurable (V N)) ∧
      (∀ N omega, 0 ≤ V N omega) ∧
      (∀ N, MemLp (V N) (ENNReal.ofReal p) μ) ∧
      (∀ N, eLpNorm (V N) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal CV) ∧
      ∀ᵐ omega ∂μ, ∀ N : ℕ,
        IsLUB {v : ℝ | ∃ k : ℕ, k ≤ N ∧ ∃ a : Grid k,
          v = Rfun k ^ eta * Zfun N k omega a} (V N omega) := by
  classical
  let I := fun N : ℕ => Σ k : Fin (N + 1), Grid k.1
  let : ∀ N : ℕ, Fintype (I N) := fun N => by
    dsimp [I]
    infer_instance
  let iZero : ∀ N : ℕ, I N := fun N =>
    let a0 : Grid 0 := Classical.choice (inferInstance : Nonempty (Grid 0))
    ⟨⟨0, Nat.zero_lt_succ N⟩, a0⟩
  have hI_nonempty : ∀ N : ℕ, (Finset.univ : Finset (I N)).Nonempty := by
    intro N
    exact ⟨iZero N, Finset.mem_univ _⟩
  let Targ : ∀ N : ℕ, I N → Ω → ℝ :=
    fun N i omega => Rfun i.1.1 ^ eta * Zfun N i.1.1 omega i.2
  have hTargA : ∀ (N : ℕ) (i : I N),
      AEStronglyMeasurable (Targ N i) μ := by
    intro N i
    have hk : i.1.1 ≤ N := Nat.lt_succ_iff.mp i.1.isLt
    have hz := (hZmem N i.1.1 i.2 hk).aestronglyMeasurable
    simpa [Targ] using hz.const_mul (Rfun i.1.1 ^ eta)
  let TargM : ∀ N : ℕ, I N → Ω → ℝ :=
    fun N i => AEMeasurable.mk (Targ N i) (hTargA N i).aemeasurable
  have hTargM : ∀ (N : ℕ) (i : I N), Measurable (TargM N i) := by
    intro N i
    exact (hTargA N i).aemeasurable.measurable_mk
  let V : ℕ → Ω → ℝ := fun N omega =>
    max 0 ((Finset.univ : Finset (I N)).sup'
      (hI_nonempty N) (TargM N) omega)
  have hVmeas : ∀ N, Measurable (V N) := by
    intro N
    apply Measurable.max measurable_const
    apply Finset.measurable_sup' (hI_nonempty N)
    intro i hi
    exact hTargM N i
  have haeT : ∀ᵐ omega ∂μ, ∀ N : ℕ, ∀ i : I N,
      Targ N i omega = TargM N i omega := by
    apply (ae_all_iff.2 ?_)
    intro N
    apply (ae_all_iff.2 ?_)
    intro i
    exact (hTargA N i).aemeasurable.ae_eq_mk
  have hVdom : ∀ᵐ omega ∂μ, ∀ N : ℕ, 0 ≤ V N omega ∧
      ‖V N omega‖ ≤ (Classical.choose (hgrowth_norm N)) omega := by
    let hWchoice : ∀ N : ℕ, Ω → ℝ :=
      fun N => Classical.choose (hgrowth_norm N)
    have hWspec : ∀ N, MemLp (hWchoice N) (ENNReal.ofReal p) μ ∧
        (∀ᵐ omega ∂μ, 0 ≤ hWchoice N omega ∧
          ∀ n : ℕ, ∀ i : Fin (kcard n),
            |Zbank N n i omega| ≤ hWchoice N omega * (3 : ℝ)^(eta * n)) := by
      intro N
      dsimp [hWchoice]
      exact ⟨(Classical.choose_spec (hgrowth_norm N)).1,
        (Classical.choose_spec (hgrowth_norm N)).2.1⟩
    have hWae : ∀ᵐ omega ∂μ, ∀ N : ℕ,
        0 ≤ hWchoice N omega ∧
          ∀ n : ℕ, ∀ i : Fin (kcard n),
            |Zbank N n i omega| ≤ hWchoice N omega * (3 : ℝ)^(eta * n) := by
      exact ae_all_iff.2 (fun N => (hWspec N).2)
    filter_upwards [haeT, hWae] with omega hT hW
    intro N
    have hW' := hW N
    constructor
    · exact le_max_left _ _
    · have hsup :
          (Finset.univ : Finset (I N)).sup' (hI_nonempty N) (TargM N) omega ≤
            hWchoice N omega := by
        have hsup' :
            (Finset.univ : Finset (I N)).sup' (hI_nonempty N)
                (fun i => TargM N i omega) ≤ hWchoice N omega := by
          refine Finset.sup'_le (hI_nonempty N)
            (fun i => TargM N i omega) ?_
          intro i hi
          change TargM N i omega ≤ hWchoice N omega
          rw [← hT N i]
          obtain ⟨j, hj⟩ := hegrid_surj i.1.1 i.2
          have hZdom := hW'.2 i.1.1 j
          have hin : i.1.1 ≤ N := Nat.lt_succ_iff.mp i.1.isLt
          have hZdom' : |Zfun N i.1.1 omega i.2| ≤
              hWchoice N omega * (3 : ℝ)^(eta * i.1.1) := by
            have heq := hZbank_eq N i.1.1 j hin
            rw [heq] at hZdom
            simpa [hj] using hZdom
          have hZle : Zfun N i.1.1 omega i.2 ≤
              hWchoice N omega * (3 : ℝ)^(eta * i.1.1) :=
            (le_abs_self _).trans hZdom'
          have hmul := mul_le_mul_of_nonneg_left hZle (hRnonneg i.1.1)
          calc
            Targ N i omega ≤ Rfun i.1.1 ^ eta *
                (hWchoice N omega * (3 : ℝ)^(eta * i.1.1)) := by
                  simpa [Targ] using hmul
            _ = hWchoice N omega *
                (Rfun i.1.1 ^ eta * (3 : ℝ)^(eta * i.1.1)) := by ring
            _ ≤ hWchoice N omega := by
              have hfac' : Rfun i.1.1 ^ eta *
                  (3 : ℝ)^(eta * i.1.1) ≤ 1 := hfactor i.1.1
              simpa using mul_le_mul_of_nonneg_left hfac' hW'.1
        simpa only [Finset.sup'_apply] using hsup'
      have hVle : V N omega ≤ hWchoice N omega := by
        dsimp [V]
        exact max_le hW'.1 hsup
      calc
        ‖V N omega‖ = V N omega := by
          rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
        _ ≤ hWchoice N omega := hVle
  have hVmem : ∀ N, MemLp (V N) (ENNReal.ofReal p) μ := by
    intro N
    have hW := (Classical.choose_spec (hgrowth_norm N)).1
    have hWdom := (Classical.choose_spec (hgrowth_norm N)).2.1
    apply hW.mono (hVmeas N).aestronglyMeasurable
    filter_upwards [hVdom, hWdom] with omega hω hWω
    have hωN := hω N
    simpa [Real.norm_eq_abs, abs_of_nonneg hωN.1,
      abs_of_nonneg hWω.1] using hωN.2
  have hVnorm : ∀ N, eLpNorm (V N) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal CV := by
    intro N
    have hWdom := (Classical.choose_spec (hgrowth_norm N)).2.1
    have hWnorm := (Classical.choose_spec (hgrowth_norm N)).2.2
    calc
      eLpNorm (V N) (ENNReal.ofReal p) μ ≤
          eLpNorm (Classical.choose (hgrowth_norm N))
            (ENNReal.ofReal p) μ := by
            apply eLpNorm_mono_ae (hVmeas N).aestronglyMeasurable
            filter_upwards [hVdom, hWdom] with omega hω hWω
            have hωN := hω N
            simpa [Real.norm_eq_abs, abs_of_nonneg hωN.1,
              abs_of_nonneg hWω.1] using hωN.2
      _ ≤ KV := hWnorm
      _ ≤ ENNReal.ofReal CV := hKV
  refine ⟨V, hVmeas, ?_, hVmem, hVnorm, ?_⟩
  · intro N omega
    exact le_max_left _ _
  · filter_upwards [haeT] with omega hT
    intro N
    refine ⟨?_, ?_⟩
    · rintro v ⟨k, hk, a, rfl⟩
      let i : I N := ⟨⟨k, Nat.lt_succ_of_le hk⟩, a⟩
      have hi : i ∈ (Finset.univ : Finset (I N)) := Finset.mem_univ _
      have hle := Finset.le_sup' (fun i => TargM N i omega) hi
      calc
        Rfun k ^ eta * Zfun N k omega a = Targ N i omega := by rfl
        _ = TargM N i omega := hT N i
        _ ≤ (Finset.univ : Finset (I N)).sup'
            (hI_nonempty N) (TargM N) omega := by
              simpa only [Finset.sup'_apply] using hle
        _ ≤ V N omega := le_max_right _ _
    · intro b hb
      have hb0 : 0 ≤ b := by
        have hzero : Targ N (iZero N) omega ∈
            {v : ℝ | ∃ k : ℕ, k ≤ N ∧ ∃ a : Grid k,
              v = Rfun k ^ eta * Zfun N k omega a} := by
          refine ⟨0, Nat.zero_le N, (iZero N).2, ?_⟩
          rfl
        exact (hTarg_nonneg N (iZero N) omega).trans (hb hzero)
      have hsup :
          (Finset.univ : Finset (I N)).sup' (hI_nonempty N) (TargM N) omega ≤ b := by
        have hsup' :
            (Finset.univ : Finset (I N)).sup' (hI_nonempty N)
                (fun i => TargM N i omega) ≤ b := by
          refine Finset.sup'_le (hI_nonempty N)
            (fun i => TargM N i omega) ?_
          intro i hi
          change TargM N i omega ≤ b
          rw [← hT N i]
          apply hb
          refine ⟨i.1.1, Nat.lt_succ_iff.mp i.1.isLt, i.2, rfl⟩
        simpa only [Finset.sup'_apply] using hsup'
      exact max_le hb0 hsup

lemma aux_reference_mesh_envelope_growth_tail
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : ℕ) (p q eta alpha beta gap gamma Ccard K0 S CV : ℝ)
    (hq : 1 ≤ q) (hp : 1 ≤ p) (hpq : p ≤ q)
    (hlog3 : 0 < Real.log 3) (hgamma : 0 ≤ gamma)
    (hgap : 0 < gap) (hbeta_gap : beta < gap)
    (hbeta_eq : beta = gap / 4)
    (halpha_eq : alpha = eta - gap / 2)
    (hgamma_bound : gamma ≤ beta * Real.log 3)
    (hgap_identity : (d : ℝ) * Real.log 3 + q * gap * Real.log 3 =
      q * eta * Real.log 3)
    (hCVbound : S * K0 ≤ CV)
    (hCcard : 0 ≤ Ccard) (hK0 : 0 < K0)
    (hS_nonneg : 0 ≤ S)
    {Grid : ℕ → Type*} [(k : ℕ) → Fintype (Grid k)] [Nonempty (Grid 0)]
    (kcard : ℕ → ℕ)
    (hS_eq :
      (∑' k : ℕ, ENNReal.ofReal ((3 : ℝ)^(-alpha * (k : ℝ))) *
        (kcard k : ℝ≥0∞)^(1 / q)) = ENNReal.ofReal S)
    (hcard : ∀ k : ℕ, (kcard k : ℝ) ≤
      Ccard * ((k : ℝ) + 1)^0 * (3 : ℝ)^((d : ℝ) * k))
    (Rfun : ℕ → ℝ) (Zfun : ∀ _N k : ℕ, Ω → Grid k → ℝ)
    (egrid : ∀ n : ℕ, Fin (kcard n) → Grid n)
    (hegrid_surj : ∀ (n : ℕ) (a : Grid n), ∃ i, egrid n i = a)
    (hZmem : ∀ (N k : ℕ) (a : Grid k), k ≤ N →
      MemLp (Zfun N k · a) (ENNReal.ofReal q) μ)
    (hZnorm : ∀ (N k : ℕ) (a : Grid k), k ≤ N →
      eLpNorm (Zfun N k · a) (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal (K0 * Real.exp (gamma * (k : ℝ))))
    (hfactor : ∀ k : ℕ,
      Rfun k ^ eta * (3 : ℝ) ^ (eta * (k : ℝ)) ≤ 1)
    (hRnonneg : ∀ k : ℕ, 0 ≤ Rfun k ^ eta)
    (hTarg_nonneg : ∀ (N : ℕ)
      (i : Σ k : Fin (N + 1), Grid k.1) (omega : Ω),
      0 ≤ Rfun i.1.1 ^ eta * Zfun N i.1.1 omega i.2) :
    ∃ V : ℕ → Ω → ℝ,
      (∀ N, Measurable (V N)) ∧
      (∀ N omega, 0 ≤ V N omega) ∧
      (∀ N, MemLp (V N) (ENNReal.ofReal p) μ) ∧
      (∀ N, eLpNorm (V N) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal CV) ∧
      ∀ᵐ omega ∂μ, ∀ N : ℕ,
        IsLUB {v : ℝ | ∃ k : ℕ, k ≤ N ∧ ∃ a : Grid k,
          v = Rfun k ^ eta * Zfun N k omega a} (V N omega) := by
  classical
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hgap_growth : (d : ℝ) * Real.log 3 + q * gamma <
      q * eta * Real.log 3 := by
    have hqbound : q * gamma ≤ q * beta * Real.log 3 := by
      calc
        q * gamma ≤ q * (beta * Real.log 3) :=
          mul_le_mul_of_nonneg_left hgamma_bound hqpos.le
        _ = q * beta * Real.log 3 := by ring
    have hqbeta : q * beta * Real.log 3 < q * gap * Real.log 3 := by
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hbeta_gap hqpos) hlog3
    have hqne : q ≠ 0 := ne_of_gt hqpos
    calc
      (d : ℝ) * Real.log 3 + q * gamma ≤
          (d : ℝ) * Real.log 3 + q * beta * Real.log 3 :=
        add_le_add (le_refl _) hqbound
      _ < (d : ℝ) * Real.log 3 + q * gap * Real.log 3 :=
        add_lt_add_right hqbeta _
      _ = q * eta * Real.log 3 := hgap_identity
  have hbeta_alpha : beta ≤ eta - alpha := by
    rw [hbeta_eq, halpha_eq]
    linarith only [hgap]
  let Zbank : ∀ N n : ℕ, Fin (kcard n) → Ω → ℝ :=
    fun N n i omega => if hn : n ≤ N then Zfun N n omega (egrid n i) else 0
  have hZbank : ∀ (N n : ℕ) (i : Fin (kcard n)),
      AEStronglyMeasurable (Zbank N n i) μ := by
    intro N n i
    by_cases hn : n ≤ N
    · simpa [Zbank, hn] using
        (hZmem N n (egrid n i) hn).aestronglyMeasurable
    · have hz : Zbank N n i = (fun _ : Ω => (0 : ℝ)) := by
        funext omega
        simp only [Zbank, hn, ↓reduceDIte]
      rw [hz]
      exact (measurable_const : Measurable (fun _ : Ω => (0 : ℝ))).aestronglyMeasurable
  have hKbank : ∀ (N n : ℕ) (i : Fin (kcard n)),
      eLpNorm (Zbank N n i) (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal K0 * ENNReal.ofReal (Real.exp (gamma * (n : ℝ))) := by
    intro N n i
    by_cases hn : n ≤ N
    · rw [show Zbank N n i = (fun omega => Zfun N n omega (egrid n i)) by
        funext omega
        simp only [Zbank, hn, ↓reduceDIte]]
      rw [← ENNReal.ofReal_mul hK0.le]
      exact hZnorm N n (egrid n i) hn
    · have hz : Zbank N n i = (fun _ : Ω => (0 : ℝ)) := by
        funext omega
        simp only [Zbank, hn, ↓reduceDIte]
      rw [hz]
      rw [eLpNorm_fun_zero]
      positivity
  have hqE : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal hqpos.le
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  have hpqE : ENNReal.ofReal p ≤ ENNReal.ofReal q := ENNReal.ofReal_le_ofReal hpq
  have hqtE : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  have hgapE : (d : ℝ) * Real.log 3 +
      (ENNReal.ofReal q).toReal * gamma <
      (ENNReal.ofReal q).toReal * eta * Real.log 3 := by
    simpa [hqE] using hgap_growth
  have hgrowth : ∀ N : ℕ, ∃ W : Ω → ℝ,
      MemLp W (ENNReal.ofReal p) μ ∧
      (∀ᵐ omega ∂μ, 0 ≤ W omega ∧
        ∀ n : ℕ, ∀ i : Fin (kcard n),
          |Zbank N n i omega| ≤ W omega * (3 : ℝ) ^ (eta * n)) ∧
      eLpNorm W (ENNReal.ofReal p) μ ≤
        (∑' n : ℕ, ENNReal.ofReal
          (Real.exp (gamma * (n : ℝ)) * (3 : ℝ)^(-eta * (n : ℝ))) *
            (kcard n : ℝ≥0∞)^(1 / q)) * ENNReal.ofReal K0 := by
    intro N
    have h := exists_triadic_mesh_envelope_of_exponential_growth
      μ kcard d 0 Ccard eta gamma hCcard hgamma
      hpE hpqE hqtE hgapE hcard (Zbank N) (hZbank N)
      (ENNReal.ofReal K0) ENNReal.ofReal_ne_top (hKbank N)
    simpa [hqE] using h
  have hdiscount : ∀ n : ℕ,
      Real.exp (gamma * (n : ℝ)) * (3 : ℝ)^(-eta * (n : ℝ)) ≤
        (3 : ℝ)^(-alpha * (n : ℝ)) := by
    intro n
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hba : beta ≤ eta - alpha := hbeta_alpha
    have hmul : beta * Real.log 3 ≤ (eta - alpha) * Real.log 3 :=
      mul_le_mul_of_nonneg_right hba hlog3.le
    have hlin : gamma - eta * Real.log 3 ≤ -alpha * Real.log 3 := by
      calc
        gamma - eta * Real.log 3 ≤ beta * Real.log 3 - eta * Real.log 3 :=
          sub_le_sub_right hgamma_bound _
        _ ≤ (eta - alpha) * Real.log 3 - eta * Real.log 3 :=
          sub_le_sub_right hmul _
        _ = -alpha * Real.log 3 := by ring
    calc
      gamma * (n : ℝ) + Real.log 3 * (-eta * (n : ℝ)) =
          (gamma - eta * Real.log 3) * (n : ℝ) := by ring
      _ ≤ (-alpha * Real.log 3) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hlin hn
      _ = Real.log 3 * (-alpha * (n : ℝ)) := by ring
  have hgrowth_norm : ∀ N : ℕ, ∃ W : Ω → ℝ,
      MemLp W (ENNReal.ofReal p) μ ∧
      (∀ᵐ omega ∂μ, 0 ≤ W omega ∧
        ∀ n : ℕ, ∀ i : Fin (kcard n),
          |Zbank N n i omega| ≤ W omega * (3 : ℝ) ^ (eta * n)) ∧
      eLpNorm W (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (S * K0) := by
    intro N
    obtain ⟨W, hW, hWdom, hWnorm⟩ := hgrowth N
    refine ⟨W, hW, hWdom, ?_⟩
    calc
      eLpNorm W (ENNReal.ofReal p) μ ≤
          (∑' n : ℕ, ENNReal.ofReal
            (Real.exp (gamma * (n : ℝ)) * (3 : ℝ)^(-eta * (n : ℝ))) *
              (kcard n : ℝ≥0∞)^(1 / q)) * ENNReal.ofReal K0 := hWnorm
      _ ≤ (∑' n : ℕ, ENNReal.ofReal ((3 : ℝ)^(-alpha * (n : ℝ))) *
          (kcard n : ℝ≥0∞)^(1 / q)) * ENNReal.ofReal K0 := by
        gcongr with n
        exact hdiscount n
      _ = ENNReal.ofReal (S * K0) := by
        rw [hS_eq, ← ENNReal.ofReal_mul hS_nonneg]
  have hZbank_eq : ∀ (N n : ℕ) (i : Fin (kcard n)), n ≤ N →
      Zbank N n i = (fun omega => Zfun N n omega (egrid n i)) := by
    intro N n i hn
    funext omega
    simp [Zbank, hn]
  have hKV : ENNReal.ofReal (S * K0) ≤ ENNReal.ofReal CV := by
    apply ENNReal.ofReal_le_ofReal
    exact hCVbound
  exact aux_reference_mesh_envelope_assembly
    μ p q eta hqpos (Grid := Grid) kcard Rfun Zfun egrid
    hegrid_surj
    Zbank hZbank_eq hZmem (ENNReal.ofReal (S * K0)) CV hKV hgrowth_norm
    hRnonneg hfactor hTarg_nonneg

lemma aux_reference_mesh_envelope_banks
    {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : Measure (BilateralField d))
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (q A Cmom Cosc K0 : ℝ)
    (hq : 1 ≤ q) (hqpos : 0 < q) (hA : 0 ≤ A)
    (hCmom : 0 < Cmom) (hCosc : 0 < Cosc)
    {Grid : ℕ → Type*}
    (ygrid : ∀ k : ℕ, Grid k → SpatialCoordinates d)
    (sfun : ℕ → ℕ → BilateralField d → SpatialCoordinates d → ℝ)
    (oscfun : ℕ → BilateralField d → SpatialCoordinates d → ℝ)
    (Zfun : ∀ _N k : ℕ, BilateralField d → Grid k → ℝ)
    (hZfun_eq : ∀ (N k : ℕ) (omega : BilateralField d) (a : Grid k),
      Zfun N k omega a = Real.exp (oscfun k omega (ygrid k a)) *
        (sfun N k omega (ygrid k a) +
          (sfun N k omega (ygrid k a))⁻¹))
    (hspos : ∀ (N k : ℕ) (omega : BilateralField d)
      (x : SpatialCoordinates d), 0 < sfun N k omega x)
    (hpoint_at : ∀ (N k : ℕ) (a : Grid k), k ≤ N →
      Integrable (fun omega => (sfun N k omega (ygrid k a)) ^ (2 * q) +
        (sfun N k omega (ygrid k a)) ^ (-(2 * q))) P ∧
      (∫ omega, (sfun N k omega (ygrid k a)) ^ (2 * q) +
        (sfun N k omega (ygrid k a)) ^ (-(2 * q)) ∂P) ≤
          Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ)) ∧
      MemLp (fun omega => sfun N k omega (ygrid k a))
        (ENNReal.ofReal (2 * q)) P ∧
      MemLp (fun omega => (sfun N k omega (ygrid k a))⁻¹)
        (ENNReal.ofReal (2 * q)) P)
    (hosc_at : ∀ (k : ℕ) (a : Grid k),
      MemLp (fun omega => Real.exp (oscfun k omega (ygrid k a)))
          (ENNReal.ofReal (2 * q)) P ∧
      eLpNorm (fun omega => Real.exp (oscfun k omega (ygrid k a)))
          (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal Cosc)
    (hK0 : K0 = 2 * (Cmom + 1) * Cosc) :
    (∀ (N k : ℕ) (a : Grid k), k ≤ N →
      MemLp (Zfun N k · a) (ENNReal.ofReal q) P) ∧
    (∀ (N k : ℕ) (a : Grid k), k ≤ N →
      eLpNorm (Zfun N k · a) (ENNReal.ofReal q) P ≤
        ENNReal.ofReal (K0 * Real.exp (A * M.delta ^ 2 * (k : ℝ)))) := by
  have hTmem : ∀ (N k : ℕ) (a : Grid k), k ≤ N →
      MemLp (fun omega => sfun N k omega (ygrid k a) +
        (sfun N k omega (ygrid k a))⁻¹) (ENNReal.ofReal (2 * q)) P := by
    intro N k a hk
    have h := hpoint_at N k a hk
    exact h.2.2.1.add h.2.2.2
  have hZmem : ∀ (N k : ℕ) (a : Grid k), k ≤ N →
      MemLp (Zfun N k · a) (ENNReal.ofReal q) P := by
    intro N k a hk
    let : ENNReal.HolderTriple (ENNReal.ofReal (2 * q))
        (ENNReal.ofReal (2 * q)) (ENNReal.ofReal q) := by
      have hholder : Real.HolderTriple (2 * q) (2 * q) q := by
        constructor
        · field_simp
          ring
        · positivity
        · positivity
      simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_ofNat] using hholder.ennrealOfReal
    have h : MemLp
        (fun omega => (sfun N k omega (ygrid k a) +
          (sfun N k omega (ygrid k a))⁻¹) *
          Real.exp (oscfun k omega (ygrid k a)))
        (ENNReal.ofReal q) P :=
      by simpa only [Pi.mul_apply] using! (hTmem N k a hk).mul (hosc_at k a).1
    rw [show (fun omega => Zfun N k omega a) =
        (fun omega => Real.exp (oscfun k omega (ygrid k a)) *
          (sfun N k omega (ygrid k a) +
            (sfun N k omega (ygrid k a))⁻¹)) by
      funext omega
      exact hZfun_eq N k omega a]
    change MemLp (fun omega => Real.exp (oscfun k omega (ygrid k a)) *
      (sfun N k omega (ygrid k a) +
        (sfun N k omega (ygrid k a))⁻¹)) (ENNReal.ofReal q) P
    convert h using 1
    funext omega
    ring
  have hZnorm : ∀ (N k : ℕ) (a : Grid k), k ≤ N →
      eLpNorm (Zfun N k · a) (ENNReal.ofReal q) P ≤
        ENNReal.ofReal (K0 * Real.exp (A * M.delta ^ 2 * (k : ℝ))) := by
    intro N k a hk
    rw [show (fun omega => Zfun N k omega a) =
        (fun omega => Real.exp (oscfun k omega (ygrid k a)) *
          (sfun N k omega (ygrid k a) +
            (sfun N k omega (ygrid k a))⁻¹)) by
      funext omega
      exact hZfun_eq N k omega a]
    have hoscmeas := (hosc_at k a).1.aestronglyMeasurable
    have hTmeas := (hTmem N k a hk).aestronglyMeasurable
    have hprod := aux_reference_mesh_envelope_product q hqpos
      hoscmeas hTmeas
    have hadd := eLpNorm_add_le
      (f := fun omega => sfun N k omega (ygrid k a))
      (g := fun omega => (sfun N k omega (ygrid k a))⁻¹) (μ := P)
      (by exact ENNReal.one_le_ofReal.mpr (by nlinarith : 1 ≤ 2 * q))
    have hsnorm :
        eLpNorm (fun omega => sfun N k omega (ygrid k a))
            (ENNReal.ofReal (2 * q)) P ≤
          ENNReal.ofReal
            (1 + Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ))) ∧
      eLpNorm (fun omega => (sfun N k omega (ygrid k a))⁻¹)
          (ENNReal.ofReal (2 * q)) P ≤
        ENNReal.ofReal
          (1 + Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ))) := by
      rcases hpoint_at N k a hk with ⟨hint, hmoment, hsmem, hsimem⟩
      let y : SpatialCoordinates d := ygrid k a
      let u : BilateralField d → ℝ := fun omega => sfun N k omega y
      have hsmem' : MemLp u (ENNReal.ofReal (2 * q)) P := by
        simpa only [u, y] using hsmem
      have hsimem' : MemLp (fun omega => (u omega)⁻¹)
          (ENNReal.ofReal (2 * q)) P := by
        simpa only [u, y] using hsimem
      have hint' : Integrable (fun omega => (u omega) ^ (2 * q) +
          (u omega) ^ (-(2 * q))) P := by
        simpa only [u, y] using hint
      have ha : 0 < 2 * q := mul_pos (by norm_num) hqpos
      have hDpos : 0 < Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ)) :=
        mul_pos hCmom (Real.exp_pos _)
      let D : ℝ := Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ))
      have hroot :
          (∫ omega, (u omega) ^ (2 * q) +
            (u omega) ^ (-(2 * q)) ∂P) ^ (1 / (2 * q)) ≤ 1 + D := by
        have hnonneg : 0 ≤ ∫ omega,
            (u omega) ^ (2 * q) + (u omega) ^ (-(2 * q)) ∂P :=
          integral_nonneg (fun omega => add_nonneg
            (Real.rpow_nonneg (le_of_lt (hspos N k omega (ygrid k a))) _)
            (Real.rpow_nonneg (le_of_lt (hspos N k omega (ygrid k a))) _))
        have hpow :
            (∫ omega, (u omega) ^ (2 * q) +
              (u omega) ^ (-(2 * q)) ∂P) ^ (1 / (2 * q)) ≤
              D ^ (1 / (2 * q)) := by
          exact Real.rpow_le_rpow hnonneg (by simpa [D, u, y] using hmoment)
            (by positivity)
        have he : 0 ≤ 1 / (2 * q) := by positivity
        by_cases hD : D ≤ 1
        · calc
            _ ≤ D ^ (1 / (2 * q)) := hpow
            _ ≤ 1 := Real.rpow_le_one (le_of_lt hDpos) hD he
            _ ≤ 1 + D := by linarith
        · have hD1 : 1 ≤ D := le_of_not_ge hD
          calc
            _ ≤ D ^ (1 / (2 * q)) := hpow
            _ ≤ D ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1 (by
              have htwo : 1 ≤ 2 * q := by
                calc
                  (1 : ℝ) ≤ 2 := by norm_num
                  _ ≤ 2 * q := by
                    simpa using
                      (mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 2))
              exact (div_le_iff₀ (mul_pos (by norm_num) hqpos)).2
                (by simpa using htwo))
            _ = D := Real.rpow_one D
            _ ≤ 1 + D := le_add_of_nonneg_left (by norm_num)
      have haux :
          eLpNorm u (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal (1 + D) ∧
        eLpNorm (fun omega => (u omega)⁻¹)
            (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal (1 + D) := by
        apply aux_reference_mesh_envelope_point_norm_fixed
          (d := d) P (2 * q) (1 + D) ha (by positivity)
        · exact fun omega => hspos N k omega (ygrid k a)
        · exact hsmem'
        · exact hsimem'
        · exact hint'
        · exact hroot
      unfold u y D at haux
      exact haux
    calc
      eLpNorm (fun omega => Real.exp (oscfun k omega (ygrid k a)) *
          (sfun N k omega (ygrid k a) +
            (sfun N k omega (ygrid k a))⁻¹)) (ENNReal.ofReal q) P ≤
          eLpNorm (fun omega => Real.exp (oscfun k omega (ygrid k a)))
              (ENNReal.ofReal (2 * q)) P *
            eLpNorm (fun omega => sfun N k omega (ygrid k a) +
              (sfun N k omega (ygrid k a))⁻¹)
              (ENNReal.ofReal (2 * q)) P := by
        exact hprod
      _ ≤ ENNReal.ofReal Cosc *
          (ENNReal.ofReal
            (1 + Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ))) +
           ENNReal.ofReal
            (1 + Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ)))) := by
        exact mul_le_mul (hosc_at k a).2
          (hadd.trans (add_le_add hsnorm.1 hsnorm.2)) (by positivity) (by positivity)
      _ ≤ ENNReal.ofReal (K0 * Real.exp (A * M.delta ^ 2 * (k : ℝ))) := by
        rw [hK0]
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        have he : 1 ≤ Real.exp (A * M.delta ^ 2 * (k : ℝ)) := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (by positivity)
        have hle : 1 + Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ)) ≤
            (Cmom + 1) * Real.exp (A * M.delta ^ 2 * (k : ℝ)) := by
          calc
            1 + Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ)) ≤
                Real.exp (A * M.delta ^ 2 * (k : ℝ)) +
                  Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ)) := by
              calc
                1 + Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ)) =
                    Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ)) + 1 := by ring
                _ ≤ Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ)) +
                    Real.exp (A * M.delta ^ 2 * (k : ℝ)) :=
                  add_le_add_right he (Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ)))
                _ = Real.exp (A * M.delta ^ 2 * (k : ℝ)) +
                    Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ)) := by ring
            _ = (Cmom + 1) * Real.exp (A * M.delta ^ 2 * (k : ℝ)) := by ring
        apply ENNReal.ofReal_le_ofReal
        calc
          Cosc * (1 + Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ)) +
              (1 + Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ)))) ≤
              Cosc * (2 * ((Cmom + 1) *
                Real.exp (A * M.delta ^ 2 * (k : ℝ)))) := by
                apply mul_le_mul_of_nonneg_left _ hCosc.le
                calc
                  1 + Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ)) +
                      (1 + Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ))) =
                      2 * (1 + Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ))) := by ring
                  _ ≤ 2 * ((Cmom + 1) *
                      Real.exp (A * M.delta ^ 2 * (k : ℝ))) := by
                    exact mul_le_mul_of_nonneg_left hle (by norm_num)
          _ = 2 * (Cmom + 1) * Cosc *
              Real.exp (A * M.delta ^ 2 * (k : ℝ)) := by ring
  exact ⟨hZmem, hZnorm⟩



lemma aux_reference_mesh_envelope_construction
    (d J : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (_hJ : 1 ≤ J)
    (p q eta : ℝ) (hp : 1 ≤ p) (hpq : p ≤ q)
    (heta : 0 < eta) (hdq : (d : ℝ) < q * eta) :
    ∃ delta0 CV : ℝ,
      0 < delta0 ∧ 0 < CV ∧ delta0 ≤ 1 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredAdmissible M H → M.delta ≤ delta0 →
        let P := (chaosSampleLaw M).toMeasure
        let _K : Set (SpatialCoordinates d) := {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}
        let R : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
        let G : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega x => H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x
        let s : ℕ → ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun N k omega x =>
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
                SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
              Real.exp (G k omega x - (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
        let oscSet : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
          fun k omega y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R k),
            ∃ x' ∈ Metric.closedBall y (3 * R k),
              v = |G k omega x - G k omega x'|}
        let osc : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega y => sSup (oscSet k omega y)
        let Grid : ℕ → Type := fun k => Fin d → Fin (3^(k + J) + 1)
        let ygrid : (k : ℕ) → Grid k → SpatialCoordinates d :=
          fun k a i => (a i : ℝ) * (3 : ℝ)^(-((k + J : ℕ) : ℤ))
        let Z : (N k : ℕ) → BilateralField d → Grid k → ℝ :=
          fun N k omega a => Real.exp (osc k omega (ygrid k a)) *
            (s N k omega (ygrid k a) +
              (s N k omega (ygrid k a))⁻¹)
        ∃ V : ℕ → BilateralField d → ℝ,
          (∀ N, Measurable (V N)) ∧
          (∀ N omega, 0 ≤ V N omega) ∧
          (∀ N, MemLp (V N) (ENNReal.ofReal p) P) ∧
          (∀ N, eLpNorm (V N) (ENNReal.ofReal p) P ≤ ENNReal.ofReal CV) ∧
          ∀ᵐ omega ∂P, ∀ N : ℕ,
            IsLUB {v : ℝ | ∃ k : ℕ, k ≤ N ∧ ∃ a : Grid k,
      v = (R k)^eta * Z N k omega a} (V N omega) := by
  classical
  have hq : 1 ≤ q := hp.trans hpq
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  obtain ⟨Cmom, Crate, hCmom, hCrate, hpoint⟩ :=
    reference_point_moments d hd q hq
  obtain ⟨Cosc, hCosc, hosc⟩ := reference_oscillation_moments d hd q hq
  let gap : ℝ := eta - (d : ℝ) / q
  have hgap : 0 < gap := by
    dsimp [gap]
    apply sub_pos.mpr
    exact (div_lt_iff₀ hqpos).2 (by simpa [mul_comm] using hdq)
  let beta : ℝ := gap / 4
  let alpha : ℝ := eta - gap / 2
  let A : ℝ := Crate * ((2 * q) + (2 * q)^2)
  have hbeta : 0 < beta := by dsimp [beta]; positivity
  have halpha : 0 < alpha := by
    dsimp [alpha]
    have hdpos : 0 < (d : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hd)
    have hdivpos : 0 < (d : ℝ) / q := div_pos hdpos hqpos
    nlinarith [hgap]
  have hqalpha : (d : ℝ) < q * alpha := by
    dsimp [alpha, gap]
    have hqne : q ≠ 0 := ne_of_gt hqpos
    field_simp
    nlinarith [hdq, hqpos]
  have hA : 0 < A := by
    dsimp [A]
    positivity
  let delta0 : ℝ := min 1 (beta * Real.log 3 / (A + 1))
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hdelta0 : 0 < delta0 := by
    dsimp [delta0]
    positivity
  have hdelta0_le : delta0 ≤ 1 := by
    exact min_le_left _ _
  have hdelta_bound : ∀ {delta : ℝ}, 0 < delta → delta ≤ delta0 →
      A * delta ^ 2 ≤ beta * Real.log 3 := by
    intro delta hdelta hdelta_le
    have hdelta0_nonneg : 0 ≤ delta0 := hdelta0.le
    have hsquare : delta ^ 2 ≤ delta0 ^ 2 := by
      nlinarith [sq_nonneg (delta0 - delta), sq_nonneg delta, sq_nonneg delta0]
    have hlin : A * delta0 ≤ beta * Real.log 3 := by
      change A * min 1 (beta * Real.log 3 / (A + 1)) ≤ beta * Real.log 3
      by_cases hmin : (1 : ℝ) ≤ beta * Real.log 3 / (A + 1)
      · rw [min_eq_left hmin]
        have hden : 0 < A + 1 := by linarith
        have hle : A + 1 ≤ beta * Real.log 3 :=
          by simpa using (le_div_iff₀ hden).mp hmin
        linarith
      · rw [min_eq_right (le_of_not_ge hmin)]
        have hfrac : beta * Real.log 3 / (A + 1) < 1 :=
          (lt_of_not_ge hmin)
        have hden : 0 < A + 1 := by linarith
        have hmul : A * (beta * Real.log 3 / (A + 1)) ≤ beta * Real.log 3 := by
          calc
            A * (beta * Real.log 3 / (A + 1)) =
                (A * (beta * Real.log 3)) / (A + 1) := by ring
            _ ≤ beta * Real.log 3 := by
              apply (div_le_iff₀ hden).2
              nlinarith [hA.le, hbeta, hlog3]
        exact hmul
    calc
      A * delta ^ 2 ≤ A * delta0 ^ 2 := by gcongr
      _ ≤ A * delta0 := by
        gcongr
        have hmul : 0 ≤ delta0 * (1 - delta0) :=
          mul_nonneg hdelta0_nonneg (sub_nonneg.mpr hdelta0_le)
        nlinarith
      _ ≤ beta * Real.log 3 := hlin
  let Grid : ℕ → Type := fun k => Fin d → Fin (3^(k + J) + 1)
  let kcard : ℕ → ℕ := fun k => Fintype.card (Grid k)
  have hcard_eq : ∀ k : ℕ, kcard k = (3^(k + J) + 1)^d := by
    intro k
    simp [kcard, Grid, Fintype.card_pi]
  let Ccard : ℝ := ((3 : ℝ)^J + 1)^d
  have hcard : ∀ k : ℕ, (kcard k : ℝ) ≤
      Ccard * ((k : ℝ) + 1)^0 * (3 : ℝ)^((d : ℝ) * k) := by
    intro k
    have hbase : (3 : ℝ)^(k + J) + 1 ≤
        ((3 : ℝ)^J + 1) * (3 : ℝ)^k := by
      calc
        (3 : ℝ)^(k + J) + 1 = (3 : ℝ)^k * (3 : ℝ)^J + 1 := by
          rw [pow_add]
        _ ≤ (3 : ℝ)^k * (3 : ℝ)^J + (3 : ℝ)^k := by
          gcongr
          exact one_le_pow₀ (by norm_num)
        _ = ((3 : ℝ)^J + 1) * (3 : ℝ)^k := by ring
    have hcast : (kcard k : ℝ) = ((3 : ℝ)^(k + J) + 1)^d := by
      rw [hcard_eq k, Nat.cast_pow]
      norm_num
    rw [hcast]
    calc
      ((3 : ℝ)^(k + J) + 1)^d ≤
          (((3 : ℝ)^J + 1) * (3 : ℝ)^k)^d :=
        pow_le_pow_left₀ (by positivity) hbase d
      _ = Ccard * ((k : ℝ) + 1)^0 * (3 : ℝ)^((d : ℝ) * k) := by
        dsimp [Ccard]
        norm_num [Real.rpow_natCast]
        have hpow : ((3 : ℝ)^k)^d = (3 : ℝ)^((d : ℝ) * k) := by
          calc
            ((3 : ℝ)^k)^d = ((3 : ℝ)^k) ^ (d : ℝ) :=
              (Real.rpow_natCast _ _).symm
            _ = ((3 : ℝ)^(k : ℝ)) ^ (d : ℝ) := by
              congr 1
              exact (Real.rpow_natCast _ _).symm
            _ = (3 : ℝ)^((k : ℝ) * (d : ℝ)) := by
              exact (Real.rpow_mul (by norm_num) _ _).symm
            _ = (3 : ℝ)^((d : ℝ) * k) := by
              congr 1
              ring
        rw [mul_pow, hpow]
  have hsum : Summable (fun k : ℕ =>
      (3 : ℝ)^(-alpha * (k : ℝ)) * (kcard k : ℝ)^(1 / q)) := by
    apply summable_triadic_mesh_cardinality kcard d 0 Ccard
    · positivity
    · exact hq
    · exact hqalpha
    · exact hcard
  let S : ℝ := ∑' k : ℕ,
      (3 : ℝ)^(-alpha * (k : ℝ)) * (kcard k : ℝ)^(1 / q)
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact tsum_nonneg (fun k => mul_nonneg
      (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hS_eq :
      (∑' k : ℕ, ENNReal.ofReal ((3 : ℝ)^(-alpha * (k : ℝ))) *
        (kcard k : ℝ≥0∞)^(1 / q)) = ENNReal.ofReal S := by
    calc
      (∑' k : ℕ, ENNReal.ofReal ((3 : ℝ)^(-alpha * (k : ℝ))) *
          (kcard k : ℝ≥0∞)^(1 / q)) =
          ∑' k : ℕ, ENNReal.ofReal
            ((3 : ℝ)^(-alpha * (k : ℝ)) * (kcard k : ℝ)^(1 / q)) := by
              congr 1
              funext k
              rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
              rw [show (kcard k : ℝ≥0∞) = ENNReal.ofReal (kcard k : ℝ) by norm_num]
              rw [← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _)
                (by positivity)]
      _ = ENNReal.ofReal S := by
        simpa [S] using
          (ENNReal.ofReal_tsum_of_nonneg
            (fun k => mul_nonneg
              (Real.rpow_nonneg (by norm_num) _)
              (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hsum).symm
  let K0 : ℝ := 2 * (Cmom + 1) * Cosc
  let CV : ℝ := S * K0 + 1
  have hK0 : 0 < K0 := by dsimp [K0]; positivity
  have hCV : 0 < CV := by dsimp [CV]; nlinarith [hS_nonneg, hK0]
  refine ⟨delta0, CV, hdelta0, hCV, hdelta0_le, ?_⟩
  intro M Rm H hH hMdelta
  let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  let Kset : Set (SpatialCoordinates d) := {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}
  let Rfun : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
  let Gfun : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
    fun k omega x => H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x
  let sfun : ℕ → ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
    fun N k omega x =>
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
        Real.exp (Gfun k omega x - (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
  let oscSetfun : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
    fun k omega y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * Rfun k),
      ∃ x' ∈ Metric.closedBall y (3 * Rfun k),
        v = |Gfun k omega x - Gfun k omega x'|}
  let oscfun : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
    fun k omega y => sSup (oscSetfun k omega y)
  let ygrid : (k : ℕ) → Grid k → SpatialCoordinates d :=
    fun k a i => (a i : ℝ) * (3 : ℝ)^(-((k + J : ℕ) : ℤ))
  let Zfun : (N k : ℕ) → BilateralField d → Grid k → ℝ :=
    fun N k omega a => Real.exp (oscfun k omega (ygrid k a)) *
      (sfun N k omega (ygrid k a) +
        (sfun N k omega (ygrid k a))⁻¹)
  have hygrid : ∀ (k : ℕ) (a : Grid k), ygrid k a ∈ Kset := by
    intro k a i
    constructor
    · dsimp [ygrid]
      positivity
    · have ha : (a i : ℝ) ≤ (3 : ℝ)^(k + J) := by
        exact_mod_cast (Fin.le_last (a i))
      have hs : 0 < (3 : ℝ)^(-((k + J : ℕ) : ℤ)) :=
        zpow_pos (by norm_num) _
      have hscale : (3 : ℝ)^(k + J) *
          (3 : ℝ)^(-((k + J : ℕ) : ℤ)) = 1 := by
        rw [← zpow_natCast]
        rw [← zpow_add₀ (by norm_num)]
        have hz : (↑(k + J) + (-↑(k + J)) : ℤ) = 0 := by ring
        rw [hz, zpow_zero]
      dsimp [ygrid]
      calc
        (a i : ℝ) * (3 : ℝ)^(-((k + J : ℕ) : ℤ)) ≤
            (3 : ℝ)^(k + J) * (3 : ℝ)^(-((k + J : ℕ) : ℤ)) :=
          mul_le_mul_of_nonneg_right ha hs.le
        _ = 1 := hscale
  have hpointbank := hpoint delta0 hdelta0 hdelta0_le M Rm H hH hMdelta
  have hoscbank := hosc delta0 hdelta0 hdelta0_le M H hH hMdelta
  dsimp at hpointbank hoscbank
  clear hpoint hosc
  have hspos : ∀ (N k : ℕ) (omega : BilateralField d)
      (x : SpatialCoordinates d), 0 < sfun N k omega x := by
    intro N k omega x
    dsimp [sfun]
    exact mul_pos
      (div_pos (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N - k))
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N))
      (Real.exp_pos _)
  have hpoint_at : ∀ (N k : ℕ) (a : Grid k), k ≤ N →
      Integrable (fun omega => (sfun N k omega (ygrid k a)) ^ (2 * q) +
        (sfun N k omega (ygrid k a)) ^ (-(2 * q))) P ∧
      (∫ omega, (sfun N k omega (ygrid k a)) ^ (2 * q) +
        (sfun N k omega (ygrid k a)) ^ (-(2 * q)) ∂P) ≤
          Cmom * Real.exp (Crate * ((2 * q) + (2 * q)^2) * M.delta^2 * (k : ℝ)) ∧
      MemLp (fun omega => sfun N k omega (ygrid k a))
        (ENNReal.ofReal (2 * q)) P ∧
      MemLp (fun omega => (sfun N k omega (ygrid k a))⁻¹)
        (ENNReal.ofReal (2 * q)) P := by
    intro N k a hk
    have haexp : (2 * q : ℝ) ∈ Set.Icc 1 (2 * q) := by
      constructor <;> nlinarith
    have h := hpointbank (2 * q) haexp N k hk (ygrid k a)
      (by simpa [Kset] using hygrid k a)
    change Integrable (fun omega => (sfun N k omega (ygrid k a)) ^ (2 * q) +
      (sfun N k omega (ygrid k a)) ^ (-(2 * q))) P ∧
      (∫ omega, (sfun N k omega (ygrid k a)) ^ (2 * q) +
        (sfun N k omega (ygrid k a)) ^ (-(2 * q)) ∂P) ≤
          Cmom * Real.exp (Crate * ((2 * q) + (2 * q)^2) * M.delta^2 * (k : ℝ)) ∧
      MemLp (fun omega => sfun N k omega (ygrid k a))
        (ENNReal.ofReal (2 * q)) P ∧
      MemLp (fun omega => (sfun N k omega (ygrid k a))⁻¹)
        (ENNReal.ofReal (2 * q)) P at h
    exact h
  clear hpointbank
  have hosc_at : ∀ (k : ℕ) (a : Grid k),
      MemLp (fun omega => Real.exp (oscfun k omega (ygrid k a)))
          (ENNReal.ofReal (2 * q)) P ∧
      eLpNorm (fun omega => Real.exp (oscfun k omega (ygrid k a)))
          (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal Cosc := by
    intro k a
    have h := hoscbank k (ygrid k a)
      (by simpa [Kset] using hygrid k a)
    change MemLp (fun omega => Real.exp (oscfun k omega (ygrid k a)))
        (ENNReal.ofReal (2 * q)) P ∧
      eLpNorm (fun omega => Real.exp (oscfun k omega (ygrid k a)))
        (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal Cosc at h
    exact h
  clear hoscbank
  /-
  have hsnorm : ∀ (N k : ℕ) (a : Grid k), k ≤ N →
      eLpNorm (sfun N k · (ygrid k a)) (ENNReal.ofReal (2 * q)) P ≤
        ENNReal.ofReal
          (1 + Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ))) ∧
      eLpNorm (fun omega => (sfun N k omega (ygrid k a))⁻¹)
          (ENNReal.ofReal (2 * q)) P ≤
        ENNReal.ofReal
          (1 + Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ))) := by
    intro N k a hk
    have h := hpoint_at N k a hk
    rcases h with ⟨hint, hmoment, hsmem, hsimem⟩
    let y : SpatialCoordinates d := ygrid k a
    let u : BilateralField d → ℝ := fun omega => sfun N k omega y
    have hsmem' : MemLp u (ENNReal.ofReal (2 * q)) P := by
      simpa only [u, y] using hsmem
    have hsimem' : MemLp (fun omega => (u omega)⁻¹)
        (ENNReal.ofReal (2 * q)) P := by
      simpa only [u, y] using hsimem
    have hint' : Integrable (fun omega => (u omega) ^ (2 * q) +
        (u omega) ^ (-(2 * q))) P := by
      simpa only [u, y] using hint
    have ha : 0 < 2 * q := mul_pos (by norm_num) hqpos
    have hDpos : 0 < Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ)) :=
      mul_pos hCmom (Real.exp_pos _)
    let D : ℝ := Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ))
    have hroot :
        (∫ omega, (u omega) ^ (2 * q) +
          (u omega) ^ (-(2 * q)) ∂P) ^ (1 / (2 * q)) ≤
          1 + D := by
      have hnonneg : 0 ≤ ∫ omega,
          (u omega) ^ (2 * q) + (u omega) ^ (-(2 * q)) ∂P :=
        integral_nonneg (fun omega => add_nonneg
          (Real.rpow_nonneg (le_of_lt (hspos N k omega (ygrid k a))) _)
          (Real.rpow_nonneg (le_of_lt (hspos N k omega (ygrid k a))) _))
      have hpow :
          (∫ omega, (u omega) ^ (2 * q) +
            (u omega) ^ (-(2 * q)) ∂P) ^ (1 / (2 * q)) ≤
            D ^ (1 / (2 * q)) := by
        exact Real.rpow_le_rpow hnonneg (by simpa [D, u, y] using hmoment) (by positivity)
      have he : 0 ≤ 1 / (2 * q) := by positivity
      by_cases hD : D ≤ 1
      · calc
          _ ≤ D ^ (1 / (2 * q)) := hpow
          _ ≤ 1 := Real.rpow_le_one (le_of_lt hDpos) hD he
          _ ≤ 1 + D := by linarith
      · have hD1 : 1 ≤ D := le_of_not_ge hD
        calc
          _ ≤ D ^ (1 / (2 * q)) := hpow
          _ ≤ D ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1 (by
            have htwo : 1 ≤ 2 * q := by
              calc
                (1 : ℝ) ≤ 2 := by norm_num
                _ ≤ 2 * q := by
                  simpa using
                    (mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 2))
            exact (div_le_iff₀ (mul_pos (by norm_num) hqpos)).2
              (by simpa using htwo))
          _ = D := Real.rpow_one D
          _ ≤ 1 + D := le_add_of_nonneg_left (by norm_num)
    have haux :
        eLpNorm u
            (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal (1 + D) ∧
          eLpNorm (fun omega => (u omega)⁻¹)
            (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal (1 + D) := by
      apply aux_reference_mesh_envelope_point_norm_fixed
        (d := d) P (2 * q) (1 + D) ha (by positivity)
      · exact fun omega => hspos N k omega (ygrid k a)
      · exact hsmem'
      · exact hsimem'
      · exact hint'
      · exact hroot
    unfold u y D at haux
    exact haux
  have hTmem : ∀ (N k : ℕ) (a : Grid k), k ≤ N →
      MemLp (fun omega => sfun N k omega (ygrid k a) +
        (sfun N k omega (ygrid k a))⁻¹) (ENNReal.ofReal (2 * q)) P := by
    intro N k a hk
    have h := hpoint_at N k a hk
    exact h.2.2.1.add h.2.2.2
  have hZmem : ∀ (N k : ℕ) (a : Grid k), k ≤ N →
      MemLp (Zfun N k · a) (ENNReal.ofReal q) P := by
    intro N k a hk
    letI : ENNReal.HolderTriple (ENNReal.ofReal (2 * q))
        (ENNReal.ofReal (2 * q)) (ENNReal.ofReal q) := by
      have hholder : Real.HolderTriple (2 * q) (2 * q) q := by
        constructor
        · field_simp
          ring
        · positivity
        · positivity
      simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_ofNat] using hholder.ennrealOfReal
    have h : MemLp
        (fun omega => (sfun N k omega (ygrid k a) +
          (sfun N k omega (ygrid k a))⁻¹) *
          Real.exp (oscfun k omega (ygrid k a)))
        (ENNReal.ofReal q) P :=
      by simpa only [Pi.mul_apply] using! (hTmem N k a hk).mul (hosc_at k a).1
    change MemLp (fun omega => Real.exp (oscfun k omega (ygrid k a)) *
      (sfun N k omega (ygrid k a) +
        (sfun N k omega (ygrid k a))⁻¹)) (ENNReal.ofReal q) P
    convert h using 1
    funext omega
    ring
  let gamma : ℝ := A * M.delta ^ 2
  have hZnorm : ∀ (N k : ℕ) (a : Grid k), k ≤ N →
      eLpNorm (Zfun N k · a) (ENNReal.ofReal q) P ≤
        ENNReal.ofReal (K0 * Real.exp (gamma * (k : ℝ))) := by
    intro N k a hk
    have hoscmeas := (hosc_at k a).1.aestronglyMeasurable
    have hTmeas := (hTmem N k a hk).aestronglyMeasurable
    have hprod := aux_reference_mesh_envelope_product q hqpos
      hoscmeas hTmeas
    have hadd := eLpNorm_add_le
      (f := fun omega => sfun N k omega (ygrid k a))
      (g := fun omega => (sfun N k omega (ygrid k a))⁻¹) (μ := P)
      (by exact ENNReal.one_le_ofReal.mpr (by nlinarith : 1 ≤ 2 * q))
    have hsn := hsnorm N k a hk
    calc
      eLpNorm (Zfun N k · a) (ENNReal.ofReal q) P ≤
          eLpNorm (fun omega => Real.exp (oscfun k omega (ygrid k a)))
              (ENNReal.ofReal (2 * q)) P *
            eLpNorm (fun omega => sfun N k omega (ygrid k a) +
              (sfun N k omega (ygrid k a))⁻¹)
              (ENNReal.ofReal (2 * q)) P := by
        change eLpNorm (fun omega => Real.exp (oscfun k omega (ygrid k a)) *
          (sfun N k omega (ygrid k a) +
            (sfun N k omega (ygrid k a))⁻¹)) (ENNReal.ofReal q) P ≤ _
        exact hprod
      _ ≤ ENNReal.ofReal Cosc *
          (ENNReal.ofReal
            (1 + Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ))) +
           ENNReal.ofReal
            (1 + Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ)))) := by
        exact mul_le_mul (hosc_at k a).2
          (hadd.trans (add_le_add hsn.1 hsn.2)) (by positivity) (by positivity)
      _ ≤ ENNReal.ofReal (K0 * Real.exp (gamma * (k : ℝ))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        have he : 1 ≤ Real.exp (A * M.delta ^ 2 * (k : ℝ)) := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (by positivity)
        have hle : 1 + Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ)) ≤
            (Cmom + 1) * Real.exp (A * M.delta ^ 2 * (k : ℝ)) := by
          calc
            1 + Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ)) ≤
                Real.exp (A * M.delta ^ 2 * (k : ℝ)) +
                  Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ)) :=
              calc
                1 + Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ)) =
                    Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ)) + 1 := by ring
                _ ≤ Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ)) +
                    Real.exp (A * M.delta ^ 2 * (k : ℝ)) :=
                  add_le_add_right he (Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ)))
                _ = Real.exp (A * M.delta ^ 2 * (k : ℝ)) +
                    Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ)) := by ring
            _ = (Cmom + 1) * Real.exp (A * M.delta ^ 2 * (k : ℝ)) := by ring
        apply ENNReal.ofReal_le_ofReal
        dsimp [K0, gamma]
        calc
          Cosc * (1 + Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ)) +
              (1 + Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ)))) ≤
              Cosc * (2 * ((Cmom + 1) *
                Real.exp (A * M.delta ^ 2 * (k : ℝ)))) := by
                apply mul_le_mul_of_nonneg_left _ hCosc.le
                calc
                  1 + Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ)) +
                      (1 + Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ))) =
                      2 * (1 + Cmom * Real.exp (A * M.delta ^ 2 * (k : ℝ))) := by ring
                  _ ≤ 2 * ((Cmom + 1) *
                      Real.exp (A * M.delta ^ 2 * (k : ℝ))) := by
                    exact mul_le_mul_of_nonneg_left hle (by norm_num)
          _ = 2 * (Cmom + 1) * Cosc *
              Real.exp (A * M.delta ^ 2 * (k : ℝ)) := by ring
          _ = 2 * (Cmom + 1) * Cosc *
              Real.exp (A * M.delta ^ 2 * (k : ℝ)) := by ring
  -/
  have hbanks := aux_reference_mesh_envelope_banks
    P M q A Cmom Cosc K0 hq hqpos hA.le hCmom hCosc
    (ygrid := ygrid) (sfun := sfun) (oscfun := oscfun) (Zfun := Zfun)
    (by
      intro N k omega a
      rfl) hspos hpoint_at hosc_at rfl
  have hZmem := hbanks.1
  have hZnorm := hbanks.2
  clear hpoint_at hosc_at
  let gamma : ℝ := A * M.delta ^ 2
  let egrid : ∀ n : ℕ, Fin (kcard n) → Grid n :=
    fun n => (Fintype.equivFin (Grid n)).symm
  have hgamma : 0 ≤ gamma := by dsimp [gamma]; positivity
  have hgamma_bound : gamma ≤ beta * Real.log 3 := by
    dsimp [gamma]
    exact hdelta_bound M.shellPrefix.delta_pos hMdelta
  have hfactor_tail : ∀ k : ℕ,
      Rfun k ^ eta * (3 : ℝ) ^ (eta * (k : ℝ)) ≤ 1 := by
    intro k
    simpa [Rfun] using
      (aux_reference_mesh_envelope_target_factor eta heta.le k)
  have hRnonneg_tail : ∀ k : ℕ, 0 ≤ Rfun k ^ eta := by
    intro k
    exact Real.rpow_nonneg (by positivity) _
  have hTarg_nonneg_tail : ∀ (N : ℕ)
      (i : Σ k : Fin (N + 1), Grid k.1) (omega : BilateralField d),
      0 ≤ Rfun i.1.1 ^ eta * Zfun N i.1.1 omega i.2 := by
    intro N i omega
    have hz : 0 < Zfun N i.1.1 omega i.2 := by
      dsimp [Zfun]
      exact mul_pos (Real.exp_pos _)
        (add_pos (hspos N i.1.1 omega (ygrid i.1.1 i.2))
          (inv_pos.mpr (hspos N i.1.1 omega (ygrid i.1.1 i.2))))
    exact mul_nonneg (hRnonneg_tail i.1.1) hz.le
  have hbeta_gap : beta < gap := by
    dsimp [beta]
    linarith [hgap]
  have hgap_identity : (d : ℝ) * Real.log 3 + q * gap * Real.log 3 =
      q * eta * Real.log 3 := by
    exact aux_reference_mesh_envelope_gap_identity
      (d : ℝ) q eta (ne_of_gt hqpos)
  have hCVbound : S * K0 ≤ CV := by
    dsimp [CV]
    exact le_add_of_nonneg_right zero_le_one
  have hegrid_surj_tail : ∀ (n : ℕ) (a : Grid n), ∃ i, egrid n i = a := by
    intro n a
    let i : Fin (kcard n) := (Fintype.equivFin (Grid n)) a
    refine ⟨i, ?_⟩
    simp [egrid, i]
  /-
  have hgap_growth : (d : ℝ) * Real.log 3 + q * gamma <
      q * eta * Real.log 3 := by
    have hbound := hdelta_bound (M.shellPrefix.delta_pos) hMdelta
    have hqbeta : q * beta * Real.log 3 < q * gap * Real.log 3 := by
      have : beta < gap := by
        dsimp [beta]
        linarith [hgap]
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left this hqpos) hlog3
    have hqbound : q * gamma ≤ q * beta * Real.log 3 := by
      dsimp [gamma]
      calc
        q * (A * M.delta ^ 2) ≤ q * (beta * Real.log 3) :=
          mul_le_mul_of_nonneg_left hbound hqpos.le
        _ = q * beta * Real.log 3 := by ring
    have hqne : q ≠ 0 := ne_of_gt hqpos
    calc
      (d : ℝ) * Real.log 3 + q * gamma ≤
          (d : ℝ) * Real.log 3 + q * beta * Real.log 3 :=
        add_le_add_right hqbound ((d : ℝ) * Real.log 3)
      _ < (d : ℝ) * Real.log 3 + q * gap * Real.log 3 :=
        add_lt_add_right hqbeta ((d : ℝ) * Real.log 3)
      _ = q * eta * Real.log 3 := by
        exact aux_reference_mesh_envelope_gap_identity
          (d : ℝ) q eta hqne
  let egrid : ∀ n : ℕ, Fin (kcard n) → Grid n :=
    fun n => (Fintype.equivFin (Grid n)).symm
  let Zbank : ∀ N n : ℕ, Fin (kcard n) → BilateralField d → ℝ :=
    fun N n i omega => if hn : n ≤ N then Zfun N n omega (egrid n i) else 0
  have hZbank : ∀ (N n : ℕ) (i : Fin (kcard n)),
      AEStronglyMeasurable (Zbank N n i) P := by
    intro N n i
    by_cases hn : n ≤ N
    · simpa [Zbank, hn] using
        (hZmem N n (egrid n i) hn).aestronglyMeasurable
    · have hz : Zbank N n i = (fun _ : BilateralField d => (0 : ℝ)) := by
        funext omega
        simp only [Zbank, hn, ↓reduceDIte]
      rw [hz]
      exact (measurable_const :
        Measurable (fun _ : BilateralField d => (0 : ℝ))).aestronglyMeasurable
  have hKbank : ∀ (N n : ℕ) (i : Fin (kcard n)),
      eLpNorm (Zbank N n i) (ENNReal.ofReal q) P ≤
        ENNReal.ofReal K0 * ENNReal.ofReal (Real.exp (gamma * (n : ℝ))) := by
    intro N n i
    by_cases hn : n ≤ N
    · rw [show Zbank N n i = (fun omega => Zfun N n omega (egrid n i)) by
        funext omega
        simp only [Zbank, hn, ↓reduceDIte]]
      rw [← ENNReal.ofReal_mul hK0.le]
      exact hZnorm N n (egrid n i) hn
    · have hz : Zbank N n i = (fun _ : BilateralField d => (0 : ℝ)) := by
        funext omega
        simp only [Zbank, hn, ↓reduceDIte]
      rw [hz]
      rw [eLpNorm_zero']
      positivity
  have hqE : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal hqpos.le
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p :=
    ENNReal.one_le_ofReal.mpr hp
  have hpqE : ENNReal.ofReal p ≤ ENNReal.ofReal q :=
    ENNReal.ofReal_le_ofReal hpq
  have hqtE : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  have hgapE : (d : ℝ) * Real.log 3 +
      (ENNReal.ofReal q).toReal * gamma <
      (ENNReal.ofReal q).toReal * eta * Real.log 3 := by
    simpa [hqE] using hgap_growth
  have hgrowth : ∀ N : ℕ, ∃ W : BilateralField d → ℝ,
      MemLp W (ENNReal.ofReal p) P ∧
      (∀ᵐ omega ∂P, 0 ≤ W omega ∧
        ∀ n : ℕ, ∀ i : Fin (kcard n),
          |Zbank N n i omega| ≤ W omega * (3 : ℝ) ^ (eta * n)) ∧
      eLpNorm W (ENNReal.ofReal p) P ≤
        (∑' n : ℕ, ENNReal.ofReal
          (Real.exp (gamma * (n : ℝ)) * (3 : ℝ)^(-eta * (n : ℝ))) *
            (kcard n : ℝ≥0∞)^(1 / q)) * ENNReal.ofReal K0 := by
    intro N
    have h := exists_triadic_mesh_envelope_of_exponential_growth
      P kcard d 0 Ccard eta gamma (by positivity) hgamma
      hpE hpqE hqtE hgapE hcard (Zbank N) (hZbank N)
      (ENNReal.ofReal K0) ENNReal.ofReal_ne_top (hKbank N)
    simpa [hqE] using h
  have hdiscount : ∀ n : ℕ,
      Real.exp (gamma * (n : ℝ)) * (3 : ℝ)^(-eta * (n : ℝ)) ≤
        (3 : ℝ)^(-alpha * (n : ℝ)) := by
    intro n
    have hbound : gamma ≤ beta * Real.log 3 := by
      dsimp [gamma]
      exact hdelta_bound M.shellPrefix.delta_pos hMdelta
    have hba : beta ≤ eta - alpha := by
      dsimp [alpha, beta]
      nlinarith [hgap]
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hmul : beta * Real.log 3 ≤ (eta - alpha) * Real.log 3 :=
      mul_le_mul_of_nonneg_right hba hlog3.le
    have hlin : gamma - eta * Real.log 3 ≤ -alpha * Real.log 3 := by
      calc
        gamma - eta * Real.log 3 ≤ beta * Real.log 3 - eta * Real.log 3 :=
          sub_le_sub_right hbound _
        _ ≤ (eta - alpha) * Real.log 3 - eta * Real.log 3 :=
          sub_le_sub_right hmul _
        _ = -alpha * Real.log 3 := by ring
    calc
      gamma * (n : ℝ) + Real.log 3 * (-eta * (n : ℝ)) =
          (gamma - eta * Real.log 3) * (n : ℝ) := by ring
      _ ≤ (-alpha * Real.log 3) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hlin hn
      _ = Real.log 3 * (-alpha * (n : ℝ)) := by ring
  have hgrowth_norm : ∀ N : ℕ, ∃ W : BilateralField d → ℝ,
      MemLp W (ENNReal.ofReal p) P ∧
      (∀ᵐ omega ∂P, 0 ≤ W omega ∧
        ∀ n : ℕ, ∀ i : Fin (kcard n),
          |Zbank N n i omega| ≤ W omega * (3 : ℝ) ^ (eta * n)) ∧
      eLpNorm W (ENNReal.ofReal p) P ≤ ENNReal.ofReal (S * K0) := by
    intro N
    obtain ⟨W, hW, hWdom, hWnorm⟩ := hgrowth N
    refine ⟨W, hW, hWdom, ?_⟩
    calc
      eLpNorm W (ENNReal.ofReal p) P ≤
          (∑' n : ℕ, ENNReal.ofReal
            (Real.exp (gamma * (n : ℝ)) * (3 : ℝ)^(-eta * (n : ℝ))) *
              (kcard n : ℝ≥0∞)^(1 / q)) * ENNReal.ofReal K0 := hWnorm
      _ ≤ (∑' n : ℕ, ENNReal.ofReal ((3 : ℝ)^(-alpha * (n : ℝ))) *
          (kcard n : ℝ≥0∞)^(1 / q)) * ENNReal.ofReal K0 := by
        gcongr with n
        exact hdiscount n
      _ = ENNReal.ofReal (S * K0) := by
        rw [hS_eq, ← ENNReal.ofReal_mul hS_nonneg]
  have hegrid_surj : ∀ (n : ℕ) (a : Grid n), ∃ i, egrid n i = a := by
    intro n a
    let i : Fin (kcard n) := (Fintype.equivFin (Grid n)) a
    refine ⟨i, ?_⟩
    simp [egrid, i]
  have hZbank_eq' : ∀ (N n : ℕ) (i : Fin (kcard n)), n ≤ N →
      Zbank N n i = (fun omega => Zfun N n omega (egrid n i)) := by
    intro N n i hn
    funext omega
    simp [Zbank, hn]
  have hfactor : ∀ k : ℕ,
      Rfun k ^ eta * (3 : ℝ) ^ (eta * (k : ℝ)) ≤ 1 := by
    intro k
    simpa [Rfun] using
      (aux_reference_mesh_envelope_target_factor eta heta.le k)
  have hRnonneg : ∀ k : ℕ, 0 ≤ Rfun k ^ eta := by
    intro k
    exact Real.rpow_nonneg (by positivity) _
  have hTarg_nonneg : ∀ (N : ℕ)
      (i : Σ k : Fin (N + 1), Grid k.1) (omega : BilateralField d),
      0 ≤ Rfun i.1.1 ^ eta * Zfun N i.1.1 omega i.2 := by
    intro N i omega
    dsimp [Zfun]
    have hz : 0 < Zfun N i.1.1 omega i.2 := by
      dsimp [Zfun]
      exact mul_pos (Real.exp_pos _)
        (add_pos (hspos N i.1.1 omega (ygrid i.1.1 i.2))
          (inv_pos.mpr (hspos N i.1.1 omega (ygrid i.1.1 i.2))))
    exact mul_nonneg (hRnonneg i.1.1) hz.le
  have hKV : ENNReal.ofReal (S * K0) ≤ ENNReal.ofReal CV := by
    apply ENNReal.ofReal_le_ofReal
    dsimp [CV]
    nlinarith [hS_nonneg, hK0.le]
  -/
  exact aux_reference_mesh_envelope_growth_tail
    P d p q eta alpha beta gap gamma Ccard K0 S CV
    hq hp hpq hlog3 hgamma hgap hbeta_gap rfl rfl hgamma_bound
    hgap_identity hCVbound (by dsimp [Ccard]; positivity) hK0 hS_nonneg
    (Grid := Grid) kcard hS_eq hcard Rfun Zfun egrid hegrid_surj_tail
    hZmem hZnorm
    hfactor_tail hRnonneg_tail hTarg_nonneg_tail
  /-
  let I : ℕ → Type := fun N => Σ k : Fin (N + 1), Grid k.1
  let iZero : ∀ N : ℕ, I N := fun N =>
    let a0 : Grid 0 := fun i => ⟨0, by positivity⟩
    ⟨⟨0, Nat.zero_lt_succ N⟩, a0⟩
  have hI_nonempty : ∀ N : ℕ, (Finset.univ : Finset (I N)).Nonempty := by
    intro N
    exact ⟨iZero N, Finset.mem_univ _⟩
  let Targ : ∀ N : ℕ, I N → BilateralField d → ℝ :=
    fun N i omega => Rfun i.1.1 ^ eta * Zfun N i.1.1 omega i.2
  have hTargA : ∀ (N : ℕ) (i : I N),
      AEStronglyMeasurable (Targ N i) P := by
    intro N i
    have hz := (hZmem N i.1.1 i.2 (Nat.lt_succ_iff.mp i.1.isLt)).aestronglyMeasurable
    simpa [Targ] using hz.const_mul (Rfun i.1.1 ^ eta)
  let TargM : ∀ N : ℕ, I N → BilateralField d → ℝ :=
    fun N i => AEMeasurable.mk (Targ N i) (hTargA N i).aemeasurable
  have hTargM : ∀ (N : ℕ) (i : I N), Measurable (TargM N i) := by
    intro N i
    exact (hTargA N i).aemeasurable.measurable_mk
  let V : ℕ → BilateralField d → ℝ := fun N omega =>
    max 0 ((Finset.univ : Finset (I N)).sup'
      (hI_nonempty N) (TargM N) omega)
  have hVmeas : ∀ N, Measurable (V N) := by
    intro N
    apply Measurable.max measurable_const
    apply Finset.measurable_sup' (hI_nonempty N)
    intro i hi
    exact hTargM N i
  have haeT : ∀ᵐ omega ∂P, ∀ N : ℕ, ∀ i : I N,
      Targ N i omega = TargM N i omega := by
    apply (ae_all_iff.2 ?_)
    intro N
    apply (ae_all_iff.2 ?_)
    intro i
    exact (hTargA N i).aemeasurable.ae_eq_mk
  have hTarg_nonneg : ∀ (N : ℕ) (i : I N) (omega : BilateralField d),
      0 ≤ Targ N i omega := by
    intro N i omega
    dsimp [Targ]
    have hz : 0 < Zfun N i.1.1 omega i.2 := by
      dsimp [Zfun]
      exact mul_pos (Real.exp_pos _)
        (add_pos (hspos N i.1.1 omega (ygrid i.1.1 i.2))
          (inv_pos.mpr (hspos N i.1.1 omega (ygrid i.1.1 i.2))))
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) hz.le
  have hVdom : ∀ᵐ omega ∂P, ∀ N : ℕ, 0 ≤ V N omega ∧
      ‖V N omega‖ ≤ (Classical.choose (hgrowth_norm N)) omega := by
    let hWchoice : ∀ N : ℕ, BilateralField d → ℝ :=
      fun N => Classical.choose (hgrowth_norm N)
    have hWspec : ∀ N, MemLp (hWchoice N) (ENNReal.ofReal p) P ∧
        (∀ᵐ omega ∂P, 0 ≤ hWchoice N omega ∧
          ∀ n : ℕ, ∀ i : Fin (kcard n),
            |Zbank N n i omega| ≤ hWchoice N omega * (3 : ℝ)^(eta * n)) := by
      intro N
      dsimp [hWchoice]
      exact ⟨(Classical.choose_spec (hgrowth_norm N)).1,
        (Classical.choose_spec (hgrowth_norm N)).2.1⟩
    have hWae : ∀ᵐ omega ∂P, ∀ N : ℕ,
        0 ≤ hWchoice N omega ∧
          ∀ n : ℕ, ∀ i : Fin (kcard n),
            |Zbank N n i omega| ≤ hWchoice N omega * (3 : ℝ)^(eta * n) := by
      exact ae_all_iff.2 (fun N => (hWspec N).2)
    filter_upwards [haeT, hWae] with omega hT hW
    intro N
    have hW' := hW N
    constructor
    · exact le_max_left _ _
    · have hsup :
          (Finset.univ : Finset (I N)).sup' (hI_nonempty N) (TargM N) omega ≤
            hWchoice N omega := by
        have hsup' :
            (Finset.univ : Finset (I N)).sup' (hI_nonempty N)
                (fun i => TargM N i omega) ≤ hWchoice N omega := by
          refine Finset.sup'_le (hI_nonempty N)
            (fun i => TargM N i omega) ?_
          intro i hi
          change TargM N i omega ≤ hWchoice N omega
          rw [← hT N i]
          let j : Fin (kcard i.1.1) :=
            (Fintype.equivFin (Grid i.1.1)) i.2
          have hZdom := hW'.2 i.1.1 j
          have hin : i.1.1 ≤ N := Nat.lt_succ_iff.mp i.1.isLt
          have hZle : Zfun N i.1.1 omega i.2 ≤
              hWchoice N omega * (3 : ℝ)^(eta * i.1.1) :=
            (le_abs_self _).trans (by
              simpa [Zbank, hin, j, egrid] using hZdom)
          have hfac := aux_reference_mesh_envelope_target_factor eta
            heta.le i.1.1
          have hRnonneg : 0 ≤ Rfun i.1.1 ^ eta :=
            Real.rpow_nonneg (by positivity) _
          have hmul := mul_le_mul_of_nonneg_left hZle hRnonneg
          calc
            Targ N i omega ≤ Rfun i.1.1 ^ eta *
                (hWchoice N omega * (3 : ℝ)^(eta * i.1.1)) := by
                  simpa [Targ] using hmul
            _ = hWchoice N omega *
                (Rfun i.1.1 ^ eta * (3 : ℝ)^(eta * i.1.1)) := by ring
            _ ≤ hWchoice N omega := by
              have hfac' : Rfun i.1.1 ^ eta *
                  (3 : ℝ)^(eta * i.1.1) ≤ 1 := by
                simpa [Rfun] using hfac
              simpa using mul_le_mul_of_nonneg_left hfac' hW'.1
        simpa only [Finset.sup'_apply] using hsup'
      have hVle : V N omega ≤ hWchoice N omega := by
        dsimp [V]
        exact max_le hW'.1 hsup
      calc
        ‖V N omega‖ = V N omega := by
          rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
        _ ≤ hWchoice N omega := hVle
  have hVmem : ∀ N, MemLp (V N) (ENNReal.ofReal p) P := by
    intro N
    have hW := (Classical.choose_spec (hgrowth_norm N)).1
    have hWdom := (Classical.choose_spec (hgrowth_norm N)).2.1
    apply hW.mono (hVmeas N).aestronglyMeasurable
    filter_upwards [hVdom, hWdom] with omega hω hWω
    have hωN := hω N
    simpa [Real.norm_eq_abs, abs_of_nonneg hωN.1,
      abs_of_nonneg hWω.1] using hωN.2
  have hVnorm : ∀ N, eLpNorm (V N) (ENNReal.ofReal p) P ≤ ENNReal.ofReal CV := by
    intro N
    have hWdom := (Classical.choose_spec (hgrowth_norm N)).2.1
    have hWnorm := (Classical.choose_spec (hgrowth_norm N)).2.2
    calc
      eLpNorm (V N) (ENNReal.ofReal p) P ≤
          eLpNorm (Classical.choose (hgrowth_norm N))
            (ENNReal.ofReal p) P := by
            apply eLpNorm_mono_ae (hVmeas N).aestronglyMeasurable
            filter_upwards [hVdom, hWdom] with omega hω hWω
            have hωN := hω N
            simpa [Real.norm_eq_abs, abs_of_nonneg hωN.1,
              abs_of_nonneg hWω.1] using hωN.2
      _ ≤ ENNReal.ofReal (S * K0) := hWnorm
      _ ≤ ENNReal.ofReal CV := ENNReal.ofReal_le_ofReal (by
        dsimp [CV]
        nlinarith [hS_nonneg, hK0.le])
  dsimp
  refine ⟨V, hVmeas, ?_, hVmem, hVnorm, ?_⟩
  · intro N omega
    exact le_max_left _ _
  · filter_upwards [haeT] with omega hT
    intro N
    refine ⟨?_, ?_⟩
    · rintro v ⟨k, hk, a, rfl⟩
      let i : I N := ⟨⟨k, Nat.lt_succ_of_le hk⟩, a⟩
      have hi : i ∈ (Finset.univ : Finset (I N)) := Finset.mem_univ _
      have hle := Finset.le_sup' (fun i => TargM N i omega) hi
      calc
        (Rfun k)^eta * Zfun N k omega a = Targ N i omega := by rfl
        _ = TargM N i omega := hT N i
        _ ≤ (Finset.univ : Finset (I N)).sup'
            (hI_nonempty N) (TargM N) omega := by
              simpa only [Finset.sup'_apply] using hle
        _ ≤ V N omega := le_max_right _ _
    · intro b hb
      have hb0 : 0 ≤ b := by
        have hzero : Targ N (iZero N) omega ∈
            {v : ℝ | ∃ k : ℕ, k ≤ N ∧ ∃ a : Grid k,
              v = (Rfun k)^eta * Zfun N k omega a} := by
          refine ⟨0, Nat.zero_le N, (iZero N).2, ?_⟩
          rfl
        exact (hTarg_nonneg N (iZero N) omega).trans (hb hzero)
      have hsup :
          (Finset.univ : Finset (I N)).sup' (hI_nonempty N) (TargM N) omega ≤ b := by
        have hsup' :
            (Finset.univ : Finset (I N)).sup' (hI_nonempty N)
                (fun i => TargM N i omega) ≤ b := by
          refine Finset.sup'_le (hI_nonempty N)
            (fun i => TargM N i omega) ?_
          intro i hi
          change TargM N i omega ≤ b
          rw [← hT N i]
          apply hb
          refine ⟨i.1.1, Nat.lt_succ_iff.mp i.1.isLt, i.2, rfl⟩
        simpa only [Finset.sup'_apply] using hsup'
      exact max_le hb0 hsup
  -/
  /-
  exact aux_reference_mesh_envelope_assembly
    P p q eta hqpos heta (Grid := Grid) kcard Rfun Zfun egrid
    hegrid_surj Zbank hZbank_eq' hZmem
    (ENNReal.ofReal (S * K0)) CV hKV hgrowth_norm
    hRnonneg hfactor hTarg_nonneg
  -/

theorem reference_mesh_envelope
    (d J : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hJ : 1 ≤ J)
    (p q eta : ℝ) (hp : 1 ≤ p) (hpq : p ≤ q)
    (heta : 0 < eta) (hdq : (d : ℝ) < q * eta) :
    ∃ delta0 CV : ℝ,
      0 < delta0 ∧ 0 < CV ∧ delta0 ≤ 1 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredAdmissible M H → M.delta ≤ delta0 →
        let P := (chaosSampleLaw M).toMeasure
        let _K : Set (SpatialCoordinates d) := {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}
        let R : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
        let G : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega x => H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x
        let s : ℕ → ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun N k omega x =>
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
                SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
              Real.exp (G k omega x - (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
        let oscSet : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
          fun k omega y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R k),
            ∃ x' ∈ Metric.closedBall y (3 * R k),
              v = |G k omega x - G k omega x'|}
        let osc : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega y => sSup (oscSet k omega y)
        let Grid : ℕ → Type := fun k => Fin d → Fin (3^(k + J) + 1)
        let ygrid : (k : ℕ) → Grid k → SpatialCoordinates d :=
          fun k a i => (a i : ℝ) * (3 : ℝ)^(-((k + J : ℕ) : ℤ))
        let Z : (N k : ℕ) → BilateralField d → Grid k → ℝ :=
          fun N k omega a => Real.exp (osc k omega (ygrid k a)) *
            (s N k omega (ygrid k a) +
              (s N k omega (ygrid k a))⁻¹)
        ∃ V : ℕ → BilateralField d → ℝ,
          (∀ N, Measurable (V N)) ∧
          (∀ N omega, 0 ≤ V N omega) ∧
          (∀ N, MemLp (V N) (ENNReal.ofReal p) P) ∧
          (∀ N, eLpNorm (V N) (ENNReal.ofReal p) P ≤ ENNReal.ofReal CV) ∧
          ∀ᵐ omega ∂P, ∀ N : ℕ,
            IsLUB {v : ℝ | ∃ k : ℕ, k ≤ N ∧ ∃ a : Grid k,
              v = (R k)^eta * Z N k omega a} (V N omega) := by
  exact aux_reference_mesh_envelope_construction
    d J hd hJ p q eta hp hpq heta hdq

end SubdiffusiveProcess.Paper
