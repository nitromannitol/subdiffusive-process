import SubdiffusiveProcess.Paper.lem_20_collar_family
import SubdiffusiveProcess.Paper.lem_20_product
import SubdiffusiveProcess.Paper.lem_20_collar_energy
import SubdiffusiveProcess.Paper.lem_20_collar_mass
import SubdiffusiveProcess.Paper.lem_20_collar_amplitude
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Lane2.BoundaryPackaging
import SubdiffusiveProcess.Lane2.NativeBridge
import SubdiffusiveProcess.Lane2.ResponseMarkov
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Lane2.MeshError
import SubdiffusiveProcess.Lane2.ExternalInputs
import SubdiffusiveProcess.Main.MeasureTrace
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

lemma aux_lem20_rpow (a e r : ℝ) (hr : 0 < r) :
    ((3 * r) ^ a) ^ 2 * r ^ (-1 - e) = 3 ^ (2 * a) * r ^ (2 * a - 1 - e) := by
  have h3r : (0 : ℝ) < 3 * r := by linarith
  have hsq : ((3 * r) ^ a) ^ 2 = (3 * r) ^ (2 * a) := by
    rw [pow_two, ← Real.rpow_add h3r]
    congr 1
    ring
  rw [hsq, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (le_of_lt hr), mul_assoc,
    ← Real.rpow_add hr]
  congr 1
  ring

lemma aux_lem20_num (cm cc a b e k f r : ℝ) (hcm : 0 ≤ cm) (hcc : 0 ≤ cc)
    (hk : 1 ≤ k) (hf : 0 ≤ f) (hr : 0 < r) :
    2 * (cm * k * r ^ b) + 2 * (k * f * (3 * r) ^ a) ^ 2 * (cc * k * r ^ (-1 - e)) ≤
      max (2 * cm) (2 * cc * 3 ^ (2 * a)) * k * (1 + k ^ 2 * f ^ 2) *
        (r ^ b + r ^ (2 * a - 1 - e)) := by
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have hf2 : (0 : ℝ) ≤ f ^ 2 := sq_nonneg f
  have hb : (0 : ℝ) ≤ r ^ b := Real.rpow_nonneg (le_of_lt hr) b
  have he : (0 : ℝ) ≤ r ^ (2 * a - 1 - e) := Real.rpow_nonneg (le_of_lt hr) _
  have hG1 : (1 : ℝ) ≤ 1 + k ^ 2 * f ^ 2 :=
    le_add_of_nonneg_right (mul_nonneg (sq_nonneg k) hf2)
  have hM : (0 : ℝ) ≤ max (2 * cm) (2 * cc * 3 ^ (2 * a)) :=
    le_trans (mul_nonneg (by norm_num) hcm) (le_max_left _ _)
  have hkey : 2 * (k * f * (3 * r) ^ a) ^ 2 * (cc * k * r ^ (-1 - e)) =
      2 * cc * 3 ^ (2 * a) * k ^ 3 * f ^ 2 * r ^ (2 * a - 1 - e) := by
    have h1 : (k * f * (3 * r) ^ a) ^ 2 = k ^ 2 * f ^ 2 * ((3 * r) ^ a) ^ 2 := by ring
    calc 2 * (k * f * (3 * r) ^ a) ^ 2 * (cc * k * r ^ (-1 - e))
        = 2 * (k ^ 2 * f ^ 2) * (((3 * r) ^ a) ^ 2 * r ^ (-1 - e)) * (cc * k) := by
          rw [h1]; ring
      _ = 2 * (k ^ 2 * f ^ 2) * (3 ^ (2 * a) * r ^ (2 * a - 1 - e)) * (cc * k) := by
          rw [aux_lem20_rpow a e r hr]
      _ = 2 * cc * 3 ^ (2 * a) * k ^ 3 * f ^ 2 * r ^ (2 * a - 1 - e) := by ring
  have hkn3 : k ^ 3 * f ^ 2 ≤ k * (1 + k ^ 2 * f ^ 2) := by
    have h : k ^ 3 * f ^ 2 = k * (k ^ 2 * f ^ 2) := by ring
    rw [h]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hk0
  have t1 : 2 * (cm * k * r ^ b) ≤
      max (2 * cm) (2 * cc * 3 ^ (2 * a)) * k * (1 + k ^ 2 * f ^ 2) * r ^ b := by
    have hbase : (0 : ℝ) ≤ k * r ^ b := mul_nonneg hk0 hb
    have s1 : 2 * cm ≤ max (2 * cm) (2 * cc * 3 ^ (2 * a)) := le_max_left _ _
    have s2 : max (2 * cm) (2 * cc * 3 ^ (2 * a)) * (k * r ^ b) * 1 ≤
        max (2 * cm) (2 * cc * 3 ^ (2 * a)) * (k * r ^ b) * (1 + k ^ 2 * f ^ 2) :=
      mul_le_mul_of_nonneg_left hG1 (mul_nonneg hM hbase)
    calc 2 * (cm * k * r ^ b) = (2 * cm) * (k * r ^ b) := by ring
      _ ≤ max (2 * cm) (2 * cc * 3 ^ (2 * a)) * (k * r ^ b) :=
          mul_le_mul_of_nonneg_right s1 hbase
      _ = max (2 * cm) (2 * cc * 3 ^ (2 * a)) * (k * r ^ b) * 1 := by ring
      _ ≤ max (2 * cm) (2 * cc * 3 ^ (2 * a)) * (k * r ^ b) *
            (1 + k ^ 2 * f ^ 2) := s2
      _ = max (2 * cm) (2 * cc * 3 ^ (2 * a)) * k * (1 + k ^ 2 * f ^ 2) * r ^ b := by ring
  have t2 : 2 * cc * 3 ^ (2 * a) * k ^ 3 * f ^ 2 * r ^ (2 * a - 1 - e) ≤
      max (2 * cm) (2 * cc * 3 ^ (2 * a)) * k * (1 + k ^ 2 * f ^ 2) *
        r ^ (2 * a - 1 - e) := by
    have hc1 : (0 : ℝ) ≤ k ^ 3 * f ^ 2 * r ^ (2 * a - 1 - e) :=
      mul_nonneg (mul_nonneg (pow_nonneg hk0 3) hf2) he
    have s1 : (2 * cc * 3 ^ (2 * a)) * (k ^ 3 * f ^ 2 * r ^ (2 * a - 1 - e)) ≤
        max (2 * cm) (2 * cc * 3 ^ (2 * a)) * (k ^ 3 * f ^ 2 * r ^ (2 * a - 1 - e)) :=
      mul_le_mul_of_nonneg_right (le_max_right (2 * cm) (2 * cc * 3 ^ (2 * a))) hc1
    have s2 : k ^ 3 * f ^ 2 * r ^ (2 * a - 1 - e) ≤
        (k * (1 + k ^ 2 * f ^ 2)) * r ^ (2 * a - 1 - e) :=
      mul_le_mul_of_nonneg_right hkn3 he
    have s3 : max (2 * cm) (2 * cc * 3 ^ (2 * a)) * (k ^ 3 * f ^ 2 * r ^ (2 * a - 1 - e)) ≤
        max (2 * cm) (2 * cc * 3 ^ (2 * a)) *
          ((k * (1 + k ^ 2 * f ^ 2)) * r ^ (2 * a - 1 - e)) :=
      mul_le_mul_of_nonneg_left s2 hM
    calc 2 * cc * 3 ^ (2 * a) * k ^ 3 * f ^ 2 * r ^ (2 * a - 1 - e)
        = (2 * cc * 3 ^ (2 * a)) * (k ^ 3 * f ^ 2 * r ^ (2 * a - 1 - e)) := by ring
      _ ≤ max (2 * cm) (2 * cc * 3 ^ (2 * a)) *
            (k ^ 3 * f ^ 2 * r ^ (2 * a - 1 - e)) := s1
      _ ≤ max (2 * cm) (2 * cc * 3 ^ (2 * a)) *
            ((k * (1 + k ^ 2 * f ^ 2)) * r ^ (2 * a - 1 - e)) := s3
      _ = max (2 * cm) (2 * cc * 3 ^ (2 * a)) * k * (1 + k ^ 2 * f ^ 2) *
            r ^ (2 * a - 1 - e) := by ring
  have hsum : max (2 * cm) (2 * cc * 3 ^ (2 * a)) * k * (1 + k ^ 2 * f ^ 2) *
        (r ^ b + r ^ (2 * a - 1 - e)) =
      max (2 * cm) (2 * cc * 3 ^ (2 * a)) * k * (1 + k ^ 2 * f ^ 2) * r ^ b +
      max (2 * cm) (2 * cc * 3 ^ (2 * a)) * k * (1 + k ^ 2 * f ^ 2) *
        r ^ (2 * a - 1 - e) := by ring
  rw [hkey, hsum]
  linarith [t1, t2]

lemma aux_lem20_bound (M k f K : ℝ) (hM : 0 ≤ M) (hk : 1 ≤ k) (hkK : k ≤ K)
    (hf : 0 ≤ f) (hK : 0 ≤ K) :
    M * k * (1 + k ^ 2 * f ^ 2) ≤ M * K * (1 + K ^ 2 * f ^ 2) := by
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have hsq : k ^ 2 ≤ K ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self hk0 hkK
  have h1 : k ^ 2 * f ^ 2 ≤ K ^ 2 * f ^ 2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg f)
  have h2 : 1 + k ^ 2 * f ^ 2 ≤ 1 + K ^ 2 * f ^ 2 := by linarith
  have h3 : (0 : ℝ) ≤ 1 + k ^ 2 * f ^ 2 := by
    have hk2 : (0 : ℝ) ≤ k ^ 2 * f ^ 2 := mul_nonneg (sq_nonneg k) (sq_nonneg f)
    linarith
  have h4 : (0 : ℝ) ≤ 1 + K ^ 2 * f ^ 2 := by
    have hK2 : (0 : ℝ) ≤ K ^ 2 * f ^ 2 := mul_nonneg (sq_nonneg K) (sq_nonneg f)
    linarith
  have h5 : k * (1 + k ^ 2 * f ^ 2) ≤ K * (1 + K ^ 2 * f ^ 2) :=
    mul_le_mul hkK h2 h3 hK
  calc M * k * (1 + k ^ 2 * f ^ 2) = M * (k * (1 + k ^ 2 * f ^ 2)) := by ring
    _ ≤ M * (K * (1 + K ^ 2 * f ^ 2)) := mul_le_mul_of_nonneg_left h5 hM
    _ = M * K * (1 + K ^ 2 * f ^ 2) := by ring



theorem lem_20
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (t alpha eta : ℝ)
    (ht_lower : (d : ℝ) - 1 < t) (ht_upper : t < (d : ℝ))
    (halpha_lower : 1 / 2 < alpha) (halpha_upper : alpha < 1)
    (heta : 0 < eta) (heta_alpha : 1 + eta < 2 * alpha)
    (Ccut : ℝ) (hCcut : 0 < Ccut) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : ResponseSpace (centeredCube z R hR)),
      S.space = killedSobolevGraph (centeredCube z R hR) →
      ∀ (a : ℕ → PositiveCoefficient (centeredCube z R hR)),
      ∀ (D : Submodule ℚ (DomainL2 (centeredCube z R hR))),
      ∀ [Countable D],
      ∀ (f : D) (fc : SpatialCoordinates d → ℝ),
      ContDiff ℝ ∞ fc →
      HasCompactSupport fc →
      tsupport fc ⊆
        (centeredCube z R hR : Set (SpatialCoordinates d)) →
      (f.val : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] fc →
      ∀ (fNorm : ℝ),
      fNorm = sSup {v : ℝ | ∃ x ∈ closure
        (centeredCube z R hR : Set (SpatialCoordinates d)), v = |fc x|} →
      0 ≤ fNorm →
      BddAbove {v : ℝ | ∃ x ∈ closure
        (centeredCube z R hR : Set (SpatialCoordinates d)), v = |fc x|} →
      ∀ (KN : ℕ → ℝ) (Kstar : ℝ),
      0 ≤ Kstar →
      (∀ n : ℕ, 1 ≤ KN n ∧ KN n ≤ Kstar) →
      ∀ (u : ℕ → S.space) (uc : ℕ → SpatialCoordinates d → ℝ),
      (∀ n : ℕ,
        u n = responseSolution S (a n)
          ((sobolevVolumeLoad f.val).comp S.space.subtypeL)) →
      (∀ n : ℕ,
        ((u n).val.1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict
            (centeredCube z R hR : Set (SpatialCoordinates d))] uc n) →
      (∀ n : ℕ,
        ContinuousOn (uc n)
          (closure (centeredCube z R hR : Set (SpatialCoordinates d)))) →
      (∀ (n : ℕ) (x : SpatialCoordinates d),
        x ∈ frontier (centeredCube z R hR : Set (SpatialCoordinates d)) →
        uc n x = 0) →
      (∀ (n : ℕ) (x y : SpatialCoordinates d),
        x ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)) →
        y ∈ closure (centeredCube z R hR : Set (SpatialCoordinates d)) →
        |uc n x - uc n y| ≤ KN n * fNorm * dist x y ^ alpha) →
      (∀ (n : ℕ) (x : SpatialCoordinates d) (s : ℝ),
        0 < s → s ≤ 1 →
        (((volume.restrict
          (centeredCube z R hR : Set (SpatialCoordinates d))).withDensity
            (fun y => ENNReal.ofReal ((a n).val y *
              ∑ i : Fin d, ((u n).val.2 i y) ^ 2)))
          (Metric.ball x s)).toReal ≤ KN n * s ^ t) →
      ∀ (chi : ℝ → ℕ → S.space),
      (∀ (r : ℝ), 0 < r → r ≤ 1 → ∀ n : ℕ,
        (∀ᵐ x ∂(volume.restrict
          (centeredCube z R hR : Set (SpatialCoordinates d))),
          0 ≤ ((chi r n).val.1 : SpatialCoordinates d → ℝ) x ∧
            ((chi r n).val.1 : SpatialCoordinates d → ℝ) x ≤ 1) ∧
        (∀ᵐ x ∂(volume.restrict
          (centeredCube z R hR : Set (SpatialCoordinates d))),
          Metric.infDist x
              (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ r →
            ((chi r n).val.1 : SpatialCoordinates d → ℝ) x = 0) ∧
        (∀ᵐ x ∂(volume.restrict
          (centeredCube z R hR : Set (SpatialCoordinates d))),
          3 * r ≤ Metric.infDist x
              (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
            ((chi r n).val.1 : SpatialCoordinates d → ℝ) x = 1) ∧
        (∀ i : Fin d, ∀ᵐ x ∂(volume.restrict
          (centeredCube z R hR : Set (SpatialCoordinates d))),
          3 * r < Metric.infDist x
              (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
            ((chi r n).val.2 i : SpatialCoordinates d → ℝ) x = 0) ∧
        responseForm S (a n) (chi r n) (chi r n) ≤
          Ccut * KN n * r ^ (-1 - eta)) →
      ∃ (prod : ℝ → ℕ → S.space),
        (∀ (r : ℝ), 0 < r → r ≤ 1 → ∀ n : ℕ,
          ((prod r n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict
              (centeredCube z R hR : Set (SpatialCoordinates d))]
              (fun x => uc n x *
                (1 - ((chi r n).val.1 : SpatialCoordinates d → ℝ) x))) ∧
        (∀ (r : ℝ), 0 < r → r ≤ 1 → ∀ n : ℕ,
          responseForm S (a n) (prod r n) (prod r n) ≤
            C * KN n * (1 + (KN n) ^ 2 * fNorm ^ 2) *
              (r ^ (t - (d : ℝ) + 1) +
                r ^ (2 * alpha - 1 - eta))) ∧
        (∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
          C * KN n * (1 + (KN n) ^ 2 * fNorm ^ 2) ≤ B) := by
  classical
  obtain ⟨C_mass, hC_mass_pos, hC_mass⟩ :=
    lem_20_collar_mass d hd z R hR t ht_lower ht_upper
  have hCvpos : (0 : ℝ) < max (2 * C_mass) (2 * Ccut * 3 ^ (2 * alpha)) :=
    lt_of_lt_of_le (by linarith : (0 : ℝ) < 2 * C_mass) (le_max_left _ _)
  refine ⟨max (2 * C_mass) (2 * Ccut * 3 ^ (2 * alpha)), hCvpos, ?_⟩
  intro S hS a D hDc f fc hfc_smooth hfc_cs hfc_supp hf_eq fNorm hfNorm
    hfn_nonneg hfn_bdd KN Kstar hKstar_nonneg hKN u uc hu huc hcont hboundary
    hholder hgrowth chi hchi
  have hprod : ∀ (r : ℝ) (n : ℕ), 0 < r → r ≤ 1 → ∃ p : S.space,
      ((p.val.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
        fun x => uc n x * (1 - ((chi r n).val.1 : SpatialCoordinates d → ℝ) x)) ∧
      (∀ i : Fin d,
        ((p.val.2 i : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
          fun x => (1 - ((chi r n).val.1 : SpatialCoordinates d → ℝ) x) *
              ((u n).val.2 i : SpatialCoordinates d → ℝ) x -
            uc n x * ((chi r n).val.2 i : SpatialCoordinates d → ℝ) x)) := by
    intro r n hr hr1
    exact lem_20_product d hd z R hR S hS (u n) (chi r n) (uc n) (huc n)
      (hcont n) (hchi r hr hr1 n).1
  let prod : ℝ → ℕ → S.space := fun r n =>
    if h : 0 < r ∧ r ≤ 1 then Classical.choose (hprod r n h.1 h.2) else u 0
  have prod_eq : ∀ (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (n : ℕ),
      prod r n = Classical.choose (hprod r n hr hr1) := by
    intro r hr hr1 n
    dsimp only [prod]
    rw [dif_pos (show 0 < r ∧ r ≤ 1 from ⟨hr, hr1⟩)]
  have hprod_val : ∀ (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (n : ℕ),
      ((prod r n).val.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
        fun x => uc n x *
          (1 - ((chi r n).val.1 : SpatialCoordinates d → ℝ) x) := by
    intro r hr hr1 n
    rw [prod_eq r hr hr1 n]
    exact (Classical.choose_spec (hprod r n hr hr1)).1
  have hprod_grad : ∀ (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (n : ℕ) (i : Fin d),
      ((prod r n).val.2 i : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))]
        fun x => (1 - ((chi r n).val.1 : SpatialCoordinates d → ℝ) x) *
            ((u n).val.2 i : SpatialCoordinates d → ℝ) x -
          uc n x * ((chi r n).val.2 i : SpatialCoordinates d → ℝ) x := by
    intro r hr hr1 n i
    rw [prod_eq r hr hr1 n]
    exact (Classical.choose_spec (hprod r n hr hr1)).2 i
  refine ⟨prod, ?_, ?_, ?_⟩
  · intro r hr hr1 n
    exact hprod_val r hr hr1 n
  · intro r hr hr1 n
    obtain ⟨hchi01, _hz, hchi_one, hgrad_zero, hchi_energy⟩ := hchi r hr hr1 n
    have hKNn : 1 ≤ KN n := (hKN n).1
    have hKN0 : (0 : ℝ) ≤ KN n := by linarith
    have h3r : (0 : ℝ) < 3 * r := by linarith
    have hM0 : (0 : ℝ) ≤ KN n * fNorm * (3 * r) ^ alpha :=
      mul_nonneg (mul_nonneg hKN0 hfn_nonneg)
        (Real.rpow_nonneg (le_of_lt h3r) alpha)
    have hM20 : (0 : ℝ) ≤ 2 * (KN n * fNorm * (3 * r) ^ alpha) ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg _)
    have hampl := lem_20_collar_amplitude d hd z R hR alpha halpha_lower
      halpha_upper (KN n) fNorm hKNn hfn_nonneg (uc n) (hcont n)
      (hboundary n) (hholder n) r hr hr1
    have henergy := lem_20_collar_energy d hd z R hR S hS (a n) (u n)
      (chi r n) (prod r n) (uc n) (huc n) (hprod_val r hr hr1 n)
      (hprod_grad r hr hr1 n) r hr hr1 hchi01 hchi_one hgrad_zero
      (KN n * fNorm * (3 * r) ^ alpha) hM0 hampl
    have hmass := hC_mass S hS (a n) (u n) (KN n) hKNn (hgrowth n) r hr hr1
    have hstep : responseForm S (a n) (prod r n) (prod r n) ≤
        2 * (C_mass * KN n * r ^ (t - (d : ℝ) + 1)) +
        2 * (KN n * fNorm * (3 * r) ^ alpha) ^ 2 *
          (Ccut * KN n * r ^ (-1 - eta)) := by
      refine le_trans henergy (add_le_add ?_ ?_)
      · exact mul_le_mul_of_nonneg_left hmass (by norm_num)
      · exact mul_le_mul_of_nonneg_left hchi_energy hM20
    have hnum := aux_lem20_num C_mass Ccut alpha (t - (d : ℝ) + 1) eta
      (KN n) fNorm r (le_of_lt hC_mass_pos) (le_of_lt hCcut) hKNn hfn_nonneg hr
    exact le_trans hstep hnum
  · refine ⟨max (2 * C_mass) (2 * Ccut * 3 ^ (2 * alpha)) * Kstar *
        (1 + Kstar ^ 2 * fNorm ^ 2), ?_, ?_⟩
    · refine mul_nonneg (mul_nonneg (le_of_lt hCvpos) hKstar_nonneg) ?_
      have hk2 : (0 : ℝ) ≤ Kstar ^ 2 * fNorm ^ 2 :=
        mul_nonneg (sq_nonneg Kstar) (sq_nonneg fNorm)
      linarith
    · intro n
      exact aux_lem20_bound (max (2 * C_mass) (2 * Ccut * 3 ^ (2 * alpha)))
        (KN n) fNorm Kstar (le_of_lt hCvpos) (hKN n).1 (hKN n).2 hfn_nonneg
        hKstar_nonneg


end Paper
