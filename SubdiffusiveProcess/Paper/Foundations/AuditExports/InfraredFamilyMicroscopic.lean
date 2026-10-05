module

public import SubdiffusiveProcess.Paper.Foundations.AuditExports.InfraredFamilyRegularity
public import SubdiffusiveProcess.Paper.lem_as_regularity

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric Filter
open SubdiffusiveProcess SubdiffusiveProcess.Paper SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff Topology

noncomputable section
namespace SubdiffusiveProcess.AuditExports

/-- The deterministic microscopic argument with its global coercivity
constant exposed. The family producer below constructs this constant from
the zero-infrared coefficient and the common native envelope. -/
theorem family_small_energy_from_coercivity {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E)
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (J : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hrJ : (3 : ℝ) ^ J * r ≤ 1)
    (Mxv Dv : ℝ) (hMx : 0 < Mxv) (hDv : 0 ≤ Dv)
    (henv : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      Mxv⁻¹ ≤ cutoffCoefficient model H om J x ∧ cutoffCoefficient model H om J x ≤ Mxv)
    (hlip : ∀ x y, x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
      y ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
      |Real.log (cutoffCoefficient model H om J x) - Real.log (cutoffCoefficient model H om J y)| ≤
        Dv * (3 : ℝ) ^ J * dist x y)
    (Lam : ℝ) (hLam : 0 < Lam)
    (hcoerce : ∀ a1 : PositiveCoefficient (unitNeumannCube d),
      (∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
        a1.val x = (cutoffPositiveCoefficient model H om J z hr).val
          (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x)) →
      ∀ (F1 : SpatialCoordinates d → ℝ) (Kf1 : ℝ), 0 ≤ Kf1 →
        AEMeasurable F1 (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |F1 x| ≤ Kf1) →
      ∀ v1 : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann a1 F1 v1 →
        sobolevCoefficientForm a1 (v1 : SobolevData (unitNeumannCube d))
          (v1 : SobolevData (unitNeumannCube d)) ≤ Kf1 ^ 2 * P.C ^ 2 * Lam)
    (C c p1 t1 : ℝ) (hC : 0 < C) (t : ℝ) (ht0 : 0 ≤ t)
    (hbig : let q1 : ℝ := (d : ℝ) - 2 * (d : ℝ) / p1
      ∀ eps : ℝ, 0 < eps → eps ≤ 1 →
      ∀ (a : PositiveCoefficient (unitNeumannCube d)) (A : C(SpatialCoordinates d, ℝ)),
      a.val =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A →
      ∀ DN mN MN : ℝ, 0 ≤ DN → 0 < mN →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), mN ≤ A y ∧ A y ≤ MN) →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
        ∀ z ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
          |Real.log (A y) - Real.log (A z)| ≤ DN / eps * dist y z) →
      ∀ f : SpatialCoordinates d → ℝ, Measurable f →
      ∀ Kf : ℝ, 0 ≤ Kf → (∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
      let ell : ℝ := c * eps / (1 + DN)
      let gamma := fun (v : SobolevData (unitNeumannCube d)) (x : SpatialCoordinates d) (rr : ℝ) =>
        ∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < rr / 2} ∩
          (unitNeumannCube d : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (v.2 i y) ^ 2
      ∀ u : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann a f u →
        (∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ ell →
          gamma u x rr ≤ C * (rr / ell) ^ q1 * gamma u x (C * eps) +
            C * mN⁻¹ * Kf ^ 2 * ell ^ (2 + 2 * (d : ℝ) / p1) * rr ^ q1) ∧
        (∀ Kmac : ℝ, 0 ≤ Kmac → ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
          gamma u x (C * eps) ≤ Kmac * eps ^ t1 →
          ∀ rr : ℝ, 0 < rr → rr ≤ eps →
          gamma u x rr ≤ C * ((1 + DN) ^ t * eps ^ (t1 - t) * Kmac +
            mN⁻¹ * Kf ^ 2 * eps ^ ((d : ℝ) + 2 - t)) * rr ^ t)) :
    0 ≤ r ^ ((d : ℝ) + 2) * C * ((2 : ℝ) / r) ^ t *
          ((1 + Dv) ^ t * P.C ^ 2 *
            Lam + Mxv) +
        r ^ ((d : ℝ) + 2) * P.C ^ 2 *
          Lam *
          ((2 : ℝ) / r) ^ t ∧
      ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
        AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), F x) = 0 →
        ∀ v : meanZeroSobolevGraph (centeredCube z r hr),
          SolvesNeumann (cutoffPositiveCoefficient model H om J z hr) F v →
        ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), ∀ rad : ℝ, 0 < rad → rad ≤ r →
          localGradientEnergy (cutoffPositiveCoefficient model H om J z hr)
              (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
              (sobolevGradient (v : SobolevData (centeredCube z r hr))) ≤
            (r ^ ((d : ℝ) + 2) * C * ((2 : ℝ) / r) ^ t *
                ((1 + Dv) ^ t * P.C ^ 2 *
                  Lam + Mxv) +
              r ^ ((d : ℝ) + 2) * P.C ^ 2 *
                Lam *
                ((2 : ℝ) / r) ^ t) * Kf ^ 2 * rad ^ t := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  obtain ⟨a1, ha1, -, hNeuTransport⟩ := lem_as_regularity_affine_transport d model H om J z r hr
  obtain ⟨A1, hA1ae, hAK, hlog1⟩ := aux_prop_growth_energy_assembly_unit_coeff model H om J z r hr
    Dv Mxv 1 hDv (by simpa using hrJ) henv hlip
  have haA1 : (a1 : PositiveCoefficient (unitNeumannCube d)).val
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A1 := hA1ae a1 ha1
  let lam1 : ℝ := Lam⁻¹
  have hlam1Inv : lam1⁻¹ = Lam := inv_inv Lam
  clear hA1ae
  have hMxv0 : 0 ≤ Mxv := hMx.le
  have hMxvi0 : 0 < Mxv⁻¹ := inv_pos.mpr hMx
  have hlam1pos : 0 < lam1 := inv_pos.mpr hLam
  have hlam1i0 : 0 ≤ lam1⁻¹ := (inv_pos.mpr hlam1pos).le
  have h2rt0 : 0 ≤ ((2 : ℝ) / r) ^ t := Real.rpow_nonneg (by positivity) _
  have hDvt0 : 0 ≤ (1 + Dv) ^ t := Real.rpow_nonneg (by linarith) _
  obtain ⟨K1, hK1def⟩ : ∃ K : ℝ, K = r ^ ((d : ℝ) + 2) * C * ((2 : ℝ) / r) ^ t *
      ((1 + Dv) ^ t * P.C ^ 2 * lam1⁻¹ + Mxv) := ⟨_, rfl⟩
  obtain ⟨K2, hK2def⟩ : ∃ K : ℝ, K = r ^ ((d : ℝ) + 2) * P.C ^ 2 * lam1⁻¹ * ((2 : ℝ) / r) ^ t :=
    ⟨_, rfl⟩
  have hrdpos : 0 ≤ r ^ ((d : ℝ) + 2) := Real.rpow_nonneg hr.le _
  have hPC2 : 0 ≤ P.C ^ 2 := sq_nonneg _
  have hK10 : 0 ≤ K1 := by
    rw [hK1def]
    have hinner : 0 ≤ (1 + Dv) ^ t * P.C ^ 2 * lam1⁻¹ + Mxv :=
      add_nonneg (mul_nonneg (mul_nonneg hDvt0 hPC2) hlam1i0) hMxv0
    exact mul_nonneg (mul_nonneg (mul_nonneg hrdpos hC.le) h2rt0) hinner
  have hK20 : 0 ≤ K2 := by
    rw [hK2def]
    exact mul_nonneg (mul_nonneg (mul_nonneg hrdpos hPC2) hlam1i0) h2rt0
  rw [← hlam1Inv, ← hK1def, ← hK2def]
  refine ⟨add_nonneg hK10 hK20, ?_⟩
  intro F Kf hKf hFm hFb hmean v hsol x hx rad hrad hradr
  obtain ⟨F1, v1, hF1eq, hF1m, hF1b, hF1mean, hsolve1, hv1val, hv1grad, henergyid⟩ :=
    hNeuTransport F Kf hKf hFm hFb hmean v hsol
  clear hNeuTransport hv1val
  obtain ⟨Kmac1, hKmac1def⟩ : ∃ K : ℝ, K = sobolevCoefficientForm a1
      (v1 : SobolevData (unitNeumannCube d)) (v1 : SobolevData (unitNeumannCube d)) :=
    ⟨_, rfl⟩
  have hKmac1nonneg : 0 ≤ Kmac1 := by
    rw [hKmac1def]; exact sobolevCoefficientForm_nonneg a1 _
  have hKmac1bound : Kmac1 ≤ (r ^ 2 * Kf) ^ 2 * P.C ^ 2 * lam1⁻¹ := by
    rw [hKmac1def, hlam1Inv]
    exact hcoerce a1 ha1 F1 (r ^ 2 * Kf) (by positivity) hF1m hF1b v1 hsolve1
  clear ha1 hcoerce
  -- x1 : the preimage of x on the unit cube
  obtain ⟨x1, hx1def⟩ : ∃ y : SpatialCoordinates d, y = cubeDilation (fun _ : Fin d => (1/2:ℝ)) z r⁻¹ x := ⟨_, rfl⟩
  have hTx1 : cubeDilation z (fun _ : Fin d => (1/2:ℝ)) r x1 = x := by
    rw [hx1def]; exact aux_prop_growth_energy_assembly_dilation_inv z (fun _ : Fin d => (1/2:ℝ)) hr x
  have hx1 : x1 ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) := by
    have hpre := cubeDilation_preimage_centeredCube z (fun _ : Fin d => (1/2:ℝ)) hr one_pos
    change x1 ∈ (centeredCube (fun _ : Fin d => (1/2:ℝ)) 1 one_pos : Set (SpatialCoordinates d))
    rw [← hpre, Set.mem_preimage, hTx1]
    exact hx
  -- global-scale instance of the transport energy identity
  have hglobal := aux_fscc_holNeuH_hSmall_global model H om J z r hr a1 v1 v x x1 hx hx1 hTx1
    Kmac1 hKmac1def henergyid
  by_cases hcase : rad ≤ r / 2
  · -- micro case: transport, clamp, apply rem_resolved_microscopic's Neumann conjunct
    obtain ⟨f1, hf1m, hf1b, hf1eq⟩ := aux_prop_growth_energy_assembly_clamp
      (unitNeumannCube d : Set (SpatialCoordinates d)) F1 hF1m (r ^ 2 * Kf) (by positivity) hF1b
    have hsolve1' : SolvesNeumann a1 f1 v1 :=
      aux_fscc_holNeuH_solvesNeumann_congr hf1eq hsolve1
    have hDNnn : (0 : ℝ) ≤ Dv := hDv
    have h1DN : (0 : ℝ) < Mxv⁻¹ := hMxvi0
    have hf1b' : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |f1 y| ≤ r ^ 2 * Kf :=
      fun y _ => hf1b y
    have hcl := hbig 1 one_pos le_rfl a1 A1 haA1 Dv Mxv⁻¹ Mxv hDNnn h1DN hAK
      (by simpa using hlog1) f1 hf1m (r ^ 2 * Kf) (by positivity) hf1b'
    have hclN := (hcl v1 hsolve1').2
    clear hbig hcl
    have hprecond : ∀ x1' ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
        (∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x1' i| < C * 1 / 2} ∩
            (unitNeumannCube d : Set (SpatialCoordinates d)),
          A1 y * ∑ i : Fin d, ((v1 : SobolevData (unitNeumannCube d)).2 i y) ^ 2) ≤
          Kmac1 * (1 : ℝ) ^ t1 := by
      intro x1' hx1'
      simp only [mul_one, Real.one_rpow]
      rw [aux_prop_growth_energy_assembly_gamma_eq a1 A1 haA1 (v1 : SobolevData (unitNeumannCube d))
        x1' (by positivity : (0:ℝ) < C)]
      calc localGradientEnergy a1
            (s := Metric.ball x1' (C / 2) ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
            (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
            (sobolevGradient (v1 : SobolevData (unitNeumannCube d)))
          ≤ (weightedGradientForm (a1 : PositiveCoefficient (unitNeumannCube d)).val)
              (sobolevGradient (v1 : SobolevData (unitNeumannCube d)))
              (sobolevGradient (v1 : SobolevData (unitNeumannCube d))) :=
            localGradientEnergy_le a1 _ _
        _ = Kmac1 := hKmac1def ▸ rfl
    have hr' : (0 : ℝ) < 2 * rad / r := by positivity
    have hr'1 : 2 * rad / r ≤ 1 := by
      rw [div_le_one hr]; linarith
    have hfin := hclN Kmac1 hKmac1nonneg x1 hx1 (hprecond x1 hx1) (2 * rad / r) hr' hr'1
    clear hclN hprecond hr'1 hf1b' hsolve1' hf1eq hf1b hf1m f1 hDNnn h1DN
    beta_reduce at hfin
    rw [aux_prop_growth_energy_assembly_gamma_eq a1 A1 haA1 (v1 : SobolevData (unitNeumannCube d))
      x1 (show (0:ℝ) < 2 * rad / r from hr')] at hfin
    clear hr'
    simp only [Real.one_rpow, mul_one] at hfin
    have hballeq : Metric.ball x1 (2 * rad / r / 2) ∩
        (unitNeumannCube d : Set (SpatialCoordinates d)) =
        Metric.ball x1 (rad / r) ∩ (unitNeumannCube d : Set (SpatialCoordinates d)) := by
      have : (2 * rad / r / 2 : ℝ) = rad / r := by ring
      rw [this]
    have heq3 := aux_prop_growth_energy_assembly_lge_congr a1
      (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
      (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
      hballeq (sobolevGradient (v1 : SobolevData (unitNeumannCube d)))
    rw [heq3] at hfin
    clear heq3 hballeq A1 haA1 hAK hlog1 hx1 hglobal
    clear c p1 t1 ht0 hd2 hd0 henv hlip hMx hrJ
    clear hMxv0 hMxvi0 hlam1pos hlam1i0 h2rt0 hK10 hrdpos hPC2 hK2def
    clear hF1eq hF1m hF1b hF1mean hsolve1 hv1grad
    clear hKf hFm hFb hmean hsol hx hradr F
    clear hKmac1def hKmac1nonneg hx1def hcase
    have hK2nn : 0 ≤ K2 * Kf ^ 2 * rad ^ t :=
      mul_nonneg (mul_nonneg hK20 (sq_nonneg Kf)) (Real.rpow_nonneg hrad.le t)
    refine (aux_fscc_holNeuH_hSmall_micro_finish hd E P model H om J z r hr Dv Mxv C t lam1
      hC hDvt0 a1 v1 v Kmac1 Kf rad hrad hKmac1bound x x1 hTx1 K1 hK1def hfin henergyid).trans ?_
    have heq : (K1 + K2) * Kf ^ 2 * rad ^ t = K1 * Kf ^ 2 * rad ^ t + K2 * Kf ^ 2 * rad ^ t := by
      ring
    rw [heq]
    exact le_add_of_nonneg_right hK2nn
  · -- large-radius case: trivial monotonicity against the global energy
    have hradr2 : r / 2 < rad := lt_of_not_ge hcase
    exact aux_fscc_holNeuH_hSmall_large_finish model H om J z r hr v t ht0 P.C lam1 hlam1pos
      K1 K2 Kmac1 Kf rad hK10 hK2def hKmac1bound hglobal x hrad hradr2


/-- Every member of the infrared family uses the same zero-infrared
coercivity price after affine pullback. -/
theorem family_pullback_global_energy {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (M : SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ℝ) (hH : ‖restrictC (closedCube z r hr) (H om)‖ ≤ S)
    (a1 : PositiveCoefficient (unitNeumannCube d))
    (ha1 : ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      a1.val x = (cutoffPositiveCoefficient M H om N z hr).val
        (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x))
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFm : AEMeasurable F (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |F x| ≤ Kf)
    (v : meanZeroSobolevGraph (unitNeumannCube d)) (hsol : SolvesNeumann a1 F v) :
    sobolevCoefficientForm a1 (v : SobolevData (unitNeumannCube d))
        (v : SobolevData (unitNeumannCube d)) ≤
      Kf ^ 2 * P.C ^ 2 * (Real.exp S *
        (E.lam z r hr (cutoffPositiveCoefficient M 0 om N z hr) z r (1 / 8) 1)⁻¹) := by
  obtain ⟨a0, ha0⟩ := dilation_coefficient_transport d z
    (fun _ : Fin d => (1 / 2 : ℝ)) r hr one_pos (cutoffPositiveCoefficient M 0 om N z hr)
  have hq := dilation_quasi_measure_preserving d z
    (fun _ : Fin d => (1 / 2 : ℝ)) r hr one_pos
  have hcmp : ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      a0.val x ≤ Real.exp S * a1.val x := by
    filter_upwards [ha0, ha1, hq.ae (cutoff_zero_le_family M H om N z r hr S hH)]
      with x hx0 hx1 hxc
    rw [hx0, hx1]
    exact hxc
  have hEn := neumann_global_energy_compare hd E P a1 a0 (Real.exp S)
    (Real.exp_pos S).le hcmp F hFm Kf hKf hFb v hsol
  have hlam := E.lam_dilation z r hr (cutoffPositiveCoefficient M 0 om N z hr)
    (fun _ : Fin d => (1 / 2 : ℝ)) one_pos a0 ha0 1 1
  rw [← hlam] at hEn
  have hLi : (E.lam z r hr (cutoffPositiveCoefficient M 0 om N z hr) z r 1 1)⁻¹ ≤
      (E.lam z r hr (cutoffPositiveCoefficient M 0 om N z hr) z r (1 / 8) 1)⁻¹ :=
    inv_anti₀ (E.lam_pos _ _ _ _ _ _ _ _)
      (E.lam_mono z r hr (cutoffPositiveCoefficient M 0 om N z hr) z r 1
        (1 / 8) 1 (by norm_num))
  calc _ ≤ Kf ^ 2 * P.C ^ 2 * Real.exp S *
        (E.lam z r hr (cutoffPositiveCoefficient M 0 om N z hr) z r 1 1)⁻¹ := hEn
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hLi (Real.exp_pos S).le)
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The deterministic microscopic constants can be fixed before the
coefficient and before the common family coercivity bound. -/
theorem family_small_energy_supplied
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E)
    (W : SmallPerturbationInput d) (t : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Model.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (om : BilateralField d) (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      (3 : ℝ) ^ N * r ≤ 1 → ∀ Mx Dv : ℝ, 0 < Mx → 0 ≤ Dv →
      (∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
        Mx⁻¹ ≤ cutoffCoefficient M H om N x ∧ cutoffCoefficient M H om N x ≤ Mx) →
      (∀ x y, x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
        y ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
        |Real.log (cutoffCoefficient M H om N x) - Real.log (cutoffCoefficient M H om N y)| ≤
          Dv * (3 : ℝ) ^ N * dist x y) →
      ∀ (S : ℝ), ‖restrictC (closedCube z r hr) (H om)‖ ≤ S →
      ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
        AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), |F x| ≤ Kf) →
        (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), F x) = 0 →
      ∀ v : meanZeroSobolevGraph (centeredCube z r hr),
        SolvesNeumann (cutoffPositiveCoefficient M H om N z hr) F v →
      ∀ x ∈ centeredCube z r hr, ∀ rad : ℝ, 0 < rad → rad ≤ r →
        localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
          (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
          (sobolevGradient (v : SobolevData (centeredCube z r hr))) ≤
        aux_lem_as_regularity_nc_small_K d r C P.C t Dv Mx
          (Real.exp S * (E.lam z r hr (cutoffPositiveCoefficient M 0 om N z hr)
            z r (1 / 8) 1)⁻¹) * Kf ^ 2 * rad ^ t := by
  obtain ⟨C, c, p1, t1, hC, hbig⟩ := aux_lem_as_regularity_nc_small_constants d hd W t ht htd
  have ht0 : 0 ≤ t := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine ⟨C, hC, ?_⟩
  intro M H om N z r hr hrN Mx Dv hMx hDv henv hlip S hS
  let Lam : ℝ := Real.exp S * (E.lam z r hr (cutoffPositiveCoefficient M 0 om N z hr)
    z r (1 / 8) 1)⁻¹
  have hLam : 0 < Lam := mul_pos (Real.exp_pos S)
    (inv_pos.mpr (E.lam_pos _ _ _ _ _ _ _ _))
  exact (family_small_energy_from_coercivity hd E P M H om N z r hr hrN Mx Dv hMx hDv
    henv hlip Lam hLam
    (family_pullback_global_energy hd E P M H om N z r hr S hS)
    C c p1 t1 hC t ht0 hbig).2

/-- A common bank for every infrared convention in the finite microscopic
cutoff prefix. The threshold precedes the cube and the prefix length. -/
theorem infrared_family_microscopic_prefix
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (t alpha : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d)
    (ha : 0 < alpha) (ha1 : alpha < 1) (k : ℕ) (ps : Fin k → ℝ) (hps : ∀ i, 1 ≤ ps i) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ m : ℕ, (∀ N : ℕ, N < m → (3 : ℝ) ^ N * r ≤ 1) →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cb : Fin k → ℝ),
        (∀ N om, 0 ≤ K N om) ∧
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cb i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ idx : Option ℕ, ∀ N : ℕ, N < m →
          aux_lem_as_regularity_nc_estimate z r hr
            (cutoffPositiveCoefficient M (infraredFamily H idx) om N z hr) t alpha (K N om) := by
  classical
  let t0 : ℝ := (max t ((d : ℝ) - 2 + 2 * alpha) + d) / 2
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hmaxd : max t ((d : ℝ) - 2 + 2 * alpha) < d := max_lt htd (by linarith)
  have htt0 : t < t0 := by dsimp [t0]; linarith [le_max_left t ((d : ℝ) - 2 + 2 * alpha)]
  have ht0d : t0 < d := by dsimp [t0]; linarith
  have ht0 : (d : ℝ) - 1 < t0 := ht.trans htt0
  have ht01 : 1 ≤ t0 := by linarith
  have he : 0 ≤ 2 + t0 - 2 * alpha - d := by
    dsimp [t0]
    linarith [le_max_right t ((d : ℝ) - 2 + 2 * alpha)]
  obtain ⟨C, hC, henergy⟩ := family_small_energy_supplied d hd E P W t0 ht0 ht0d
  obtain ⟨Cpo, hCpo, hPoinc⟩ := aux_prop_growth_holder_micro_campanato_scaled_poincare d (by omega)
  let pp : ℝ := 1 + ∑ i : Fin k, ps i
  have hsum0 : 0 ≤ ∑ i : Fin k, ps i := Finset.sum_nonneg fun i _ => (hps i).trans' zero_le_one
  have hpp : 1 ≤ pp := by dsimp [pp]; linarith
  have hpspp : ∀ i, ps i ≤ pp := by
    intro i
    have hh := Finset.single_le_sum (f := ps) (fun j _ => (hps j).trans' zero_le_one)
      (Finset.mem_univ i)
    dsimp [pp]
    linarith
  let q : ℝ := 2 * pp * t0
  have hq : 1 ≤ q := by dsimp [q]; nlinarith
  obtain ⟨Cd, cd, hCd, hcd, hExt⟩ := infrared_family_extremes d hd
  obtain ⟨δL, hδL, hLam⟩ := aux_lambda_inv_moments_adm d hd E (1 / 8) ⟨by norm_num, by norm_num⟩
  refine ⟨min (cd / (2 * q)) (δL (4 * pp)),
    lt_min (div_pos hcd (by positivity)) (hδL _ (by linarith)), ?_⟩
  intro M Rm H hH hdelta z r hr hr1 m hrm
  obtain ⟨Cr, hCr, hEx⟩ := hExt z r hr q hq
  obtain ⟨Dv, ml, mu, Cx, hCx, hDv, hAE, hDm, hMm, -, -⟩ :=
    hEx M H hH (hdelta.trans (min_le_left _ _))
  obtain ⟨A, hA, hEnv⟩ := infrared_family_envelope hd z r hr
  obtain ⟨S, hSm, hS0, hSae, -, hSE⟩ := hEnv M H hH
  obtain ⟨CL, hLm, -⟩ := hLam M Rm 0 (InfraredAdmissible.zero M) z r hr hr1 (4 * pp)
    (by linarith) (hdelta.trans (min_le_right _ _))
  let L0 : ℕ → BilateralField d → ℝ := fun N om =>
    (E.lam z r hr (cutoffPositiveCoefficient M 0 om N z hr) z r (1 / 8) 1)⁻¹
  let Lam : ℕ → BilateralField d → ℝ := fun N om => Real.exp (S om) * L0 N om
  have hLam : ∀ N om, 0 < Lam N om := fun N om =>
    mul_pos (Real.exp_pos _) (inv_pos.mpr (E.lam_pos _ _ _ _ _ _ _ _))
  have hEL : MemLp (fun om => Real.exp (S om)) (ENNReal.ofReal (4 * pp))
      (chaosSampleLaw M).toMeasure := exponential_memLp _ S hSm _ (by linarith)
        (hSE (4 * pp) (by linarith)).1
  have hLL : ∀ N, MemLp (Lam N) (ENNReal.ofReal (2 * pp)) (chaosSampleLaw M).toMeasure := by
    intro N
    have : ENNReal.HolderTriple (ENNReal.ofReal (4 * pp))
        (ENNReal.ofReal (4 * pp)) (ENNReal.ofReal (2 * pp)) := by
      simpa only [show 2 * (2 * pp) = 4 * pp by ring] using
        aux_aux_macro_moment_bank_holderTriple (2 * pp)
    exact MemLp.fun_mul (p := ENNReal.ofReal (4 * pp)) (q := ENNReal.ofReal (4 * pp))
      (r := ENNReal.ofReal (2 * pp)) hEL (hLm N)
  let Mx : ℕ → BilateralField d → ℝ := fun N om => 1 + |mu N om + (ml N om)⁻¹|
  have hMx : ∀ N om, 0 < Mx N om := fun N om => by dsimp [Mx]; positivity
  have hML : ∀ N, MemLp (Mx N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure := fun N =>
    (memLp_const (1 : ℝ)).add (hMm N).abs
  let KE : ℕ → BilateralField d → ℝ := fun N om =>
    aux_lem_as_regularity_nc_small_K d r C P.C t0 (Dv N om) (Mx N om) (Lam N om)
  have hKE : ∀ N om, 0 ≤ KE N om := fun N om =>
    aux_lem_as_regularity_nc_small_K_nonneg d r C P.C t0 (Dv N om) (Mx N om) (Lam N om)
      hr hC.le (hDv N om) (hMx N om).le (hLam N om).le
  let c : ℝ := (2 + Real.sqrt d) * Cp.C alpha * (1 + Cpo) *
    r ^ ((2 + t0 - 2 * alpha - d) / 2)
  have hc : 0 ≤ c := by
    have hCp := (Cp.C_pos alpha ha ha1).le
    dsimp [c]
    positivity
  let Kraw : ℕ → BilateralField d → ℝ := fun N om => KE N om + c * (Mx N om + KE N om)
  have hKraw : ∀ N om, 0 ≤ Kraw N om := fun N om =>
    add_nonneg (hKE N om) (mul_nonneg hc (add_nonneg (hMx N om).le (hKE N om)))
  have hKrawm : ∀ i N, MemLp (Kraw N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure := by
    intro i N
    have hh := aux_lem_as_regularity_nc_small_K_memLp (chaosSampleLaw M).toMeasure
      d r C P.C t0 c pp ht01 (by linarith) (Dv N) (Mx N) (Lam N)
      (hDv N) (hDm N) (hML N) (hLL N)
    exact hh.mono_exponent (ENNReal.ofReal_le_ofReal (hpspp i))
  obtain ⟨K, Cb, hK, hKL, hKB, hKeq⟩ := aux_lem_as_regularity_nc_finite_prefix
    (chaosSampleLaw M).toMeasure Kraw hKraw m k ps hKrawm
  refine ⟨K, Cb, hK, hKL, hKB, ?_⟩
  filter_upwards [hAE, hSae] with om hom hSom
  intro idx N hNm
  rw [hKeq N hNm]
  obtain ⟨hlip, hml, henv⟩ := hom idx N
  have hz : z ∈ (closedCube z r hr : Set (SpatialCoordinates d)) := by
    change dist z z ≤ r / 2
    rw [dist_self]
    positivity
  have hmu : 0 ≤ mu N om := (hml.trans_le ((henv z hz).1.trans (henv z hz).2)).le
  have hsum : mu N om + (ml N om)⁻¹ ≤ Mx N om := by
    dsimp [Mx]
    linarith [le_abs_self (mu N om + (ml N om)⁻¹)]
  have hmuMx : mu N om ≤ Mx N om := by
    linarith [(inv_pos.mpr hml).le]
  have hmlMx : (Mx N om)⁻¹ ≤ ml N om := by
    have hle : (ml N om)⁻¹ ≤ Mx N om := by linarith
    have hh := inv_anti₀ (inv_pos.mpr hml) hle
    simpa only [inv_inv] using hh
  have henvMx : ∀ y ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      (Mx N om)⁻¹ ≤ cutoffCoefficient M (infraredFamily H idx) om N y ∧
        cutoffCoefficient M (infraredFamily H idx) om N y ≤ Mx N om :=
    fun y hy => ⟨hmlMx.trans (henv y hy).1, (henv y hy).2.trans hmuMx⟩
  have hFnorm : ‖restrictC (closedCube z r hr) (infraredFamily H idx om)‖ ≤ S om := by
    cases idx with
    | none => exact hSom.1.1
    | some L => exact (hSom.2 L).1
  have hlow : ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      1 ≤ Mx N om * (cutoffPositiveCoefficient M (infraredFamily H idx) om N z hr).val y := by
    filter_upwards [aux_prop_growth_holder_micro_campanato_coeff_ae M (infraredFamily H idx) om N z hr,
      ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with y hy hymem
    rw [hy]
    have hh := mul_le_mul_of_nonneg_left (henvMx y (centeredCube_subset_closedCube z hr hymem)).1
      (hMx N om).le
    rwa [mul_inv_cancel₀ (hMx N om).ne'] at hh
  apply aux_lem_as_regularity_nc_small_estimate Cp z r hr hr1
    (cutoffPositiveCoefficient M (infraredFamily H idx) om N z hr)
    t t0 alpha (by linarith) htt0.le ha ha1 he Cpo hCpo hPoinc
    (Mx N om) (KE N om) (hMx N om).le (hKE N om) hlow
  exact henergy M (infraredFamily H idx) om N z r hr (hrm N hNm)
    (Mx N om) (Dv N om) (hMx N om) (hDv N om) henvMx hlip (S om) hFnorm

end SubdiffusiveProcess.AuditExports
