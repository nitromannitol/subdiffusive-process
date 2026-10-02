import Mathlib
import SubdiffusiveProcess.Paper.calib3_HT
import SubdiffusiveProcess.Paper.calib3_envelope
import SubdiffusiveProcess.Paper.calib3_macro_energy
import SubdiffusiveProcess.Paper.prop_growth_trunc_energy_assembly
import SubdiffusiveProcess.Paper.prop_growth_energy_assembly
import SubdiffusiveProcess.Paper.aux_macro_moment_bank

/-! Stage 3 (calibration): the all-radii energy growth `rad^t` (macro above the wavelength `3^{-(N+j)}`, micro below it) on the unit
cube for the top-block-removed model `HT_j`, coefficient level `N + j`.  Analogue of `prop_growth_trunc_energy_assembly` at unit
cubes; suppliers `calib3_macro_energy` (macro) and `calib3_envelope` (coefficient envelope and log-Lipschitz majorant). -/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- **All-radii energy growth on the unit cube for the top-block-removed model** (paper Steps 1-4 of `mfd:prop-growth`, unit cube,
`H = HT_j`, coefficient level `N + j`). -/
theorem calib3_energy_assembly :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (_Cp : CampanatoInput d) (_S : SobolevFoundationalInput d hd)
    (t alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < d → 0 < alpha → alpha < 1 →
    (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M), M.delta ≤ delta0 →
      ∀ (j : ℕ), 0 < j → ∀ (z : SpatialCoordinates d),
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i))
            (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound i)) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N, 1 ≤ K N om) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict
            (centeredCube z 1 one_pos : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z 1 one_pos : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z 1 one_pos)),
          ((b : SobolevData (centeredCube z 1 one_pos)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j) z one_pos) F b u →
          ∀ (x : SpatialCoordinates d) (rad : ℝ),
            x ∈ centeredCube z 1 one_pos → 0 < rad → rad ≤ 1 →
            localGradientEnergy (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j) z one_pos)
                (s := Metric.ball x rad ∩
                  (centeredCube z 1 one_pos : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter
                  (centeredCube z 1 one_pos).isOpen.measurableSet)
                (sobolevGradient (u : SobolevData (centeredCube z 1 one_pos))) ≤
              K N om * (Kf + Cphi) ^ 2 * rad ^ t := by
  intro d hd _ _ E P X W Cp S t alpha k ps ht htd halp halt hps
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht0 : 0 ≤ t := by linarith
  obtain ⟨p1, hp1, hp1t⟩ := aux_prop_growth_energy_assembly_p1_choice d hd t htd
  obtain ⟨t1, ht1def⟩ : ∃ s : ℝ, s = (t + d) / 2 := ⟨_, rfl⟩
  have htt1 : t < t1 := by rw [ht1def]; linarith
  have ht1d : t1 < d := by rw [ht1def]; linarith
  obtain ⟨C, hC, hmic, hmom⟩ :=
    aux_prop_growth_energy_assembly_micro_local d hd W p1 t t1 hp1 ht htt1 ht1d hp1t
  obtain ⟨Q0, hQ0def⟩ : ∃ q : ℝ, q = 2 * (1 + ∑ i, ps i) * max 1 t := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ i, ps i := Finset.sum_nonneg (fun i _ => le_trans zero_le_one (hps i))
  have hmax1 : 1 ≤ max 1 t := le_max_left _ _
  have hQ0 : 1 ≤ Q0 := by
    rw [hQ0def]
    have h1 : 1 ≤ 2 * (1 + ∑ i, ps i) := by linarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ 2 * (1 + ∑ i, ps i) * max 1 t := mul_le_mul h1 hmax1 zero_le_one (by linarith)
  have hqi : ∀ i, 2 * ps i * max 1 t ≤ Q0 := by
    intro i
    rw [hQ0def]
    have h1 : ps i ≤ 1 + ∑ j, ps j := by
      have := Finset.single_le_sum (fun j _ => le_trans zero_le_one (hps j))
        (Finset.mem_univ i)
      linarith
    have h2 : 2 * ps i ≤ 2 * (1 + ∑ j, ps j) := by linarith
    exact mul_le_mul_of_nonneg_right h2 (by linarith)
  obtain ⟨Cpe, Cd, cd, hCpe, hCd, hcd, hroot⟩ :=
    calib3_envelope d hd Q0 hQ0
  obtain ⟨dM, hdM, hmacro⟩ := calib3_macro_energy d hd E P X S t1 1 (fun _ => Q0)
    (by linarith) ht1d (fun _ => hQ0)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hrmax : 0 < min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3 := by
    refine mul_pos (lt_min (by linarith) (lt_min (by linarith) (by linarith))) hlog3
  obtain ⟨delta0, aRate, hδ0, hδM, hδc, haR0, haR, hmono⟩ :=
    aux_prop_growth_energy_assembly_threshold Cd Cpe _ dM (cd / (2 * Q0)) hCd hCpe hrmax hdM
      (by positivity)
  refine ⟨delta0, hδ0, ?_⟩
  intro M Rm hδ j hj z
  obtain ⟨Kmac0, CbM, hKmac00, hKmem, hKnorm, hKae⟩ :=
    hmacro M Rm (hδ.trans hδM) j hj z
  obtain ⟨Kmac, hKmacdef⟩ : ∃ Kmac : ℕ → BilateralField d → ℝ, Kmac = fun n om => Kmac0 (n - j) om :=
    ⟨_, rfl⟩
  have hKmacF : ∀ N, Kmac N = Kmac0 (N - j) := fun N => by rw [hKmacdef]
  have hKmac0 : ∀ N om, 0 ≤ Kmac N om := fun N om => by rw [hKmacF N]; exact hKmac00 _ _
  have hKmemN : ∀ N, MemLp (Kmac N) (ENNReal.ofReal Q0) (chaosSampleLaw M).toMeasure := fun N => by
    rw [hKmacF N]; exact hKmem 0 (N - j)
  have hKnormN : ∀ N, eLpNorm (Kmac N) (ENNReal.ofReal Q0) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (CbM 0) := fun N => by
    rw [hKmacF N]; exact hKnorm 0 (N - j)
  obtain ⟨D, Mx, CD, CE, hCD, hCE, hDMx0, hae, hmem, hDmom, hMxmom⟩ :=
    hroot M (hδ.trans hδc) j hj z
  have hrate : Cd * M.delta + Cpe * M.delta ^ 2 ≤ aRate :=
    hmono _ M.shellPrefix.delta_pos.le hδ
  have hB : ∀ i, ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      eLpNorm (fun o => (1 + D N o) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * Kmac N o)
        (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B ∧
      eLpNorm (fun o => Mx N o * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t))
        (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B ∧
      eLpNorm (fun o => Mx N o * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) - t) * (1 + D N o) ^ t)
        (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B := by
    intro i
    have hle : ENNReal.ofReal (2 * ps i * max 1 t) ≤ ENNReal.ofReal Q0 :=
      ENNReal.ofReal_le_ofReal (hqi i)
    have hqi1 : 1 ≤ 2 * ps i * max 1 t := by
      have := hps i
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ 2 * ps i * max 1 t := mul_le_mul (by linarith) hmax1 zero_le_one (by linarith)
    have hMxN : ∀ N : ℕ, eLpNorm (fun o => Mx N o + Mx N o)
        (ENNReal.ofReal (2 * ps i * max 1 t)) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (2 * CE * Real.exp (aRate * (N : ℝ))) := by
      intro N
      have h1 := aux_prop_growth_energy_assembly_double (chaosSampleLaw M).toMeasure (Mx N)
        (2 * ps i * max 1 t) Q0 (CE * Real.exp ((Cd * M.delta + Cpe * M.delta ^ 2) * N))
        hqi1 (hqi i) (hmem N).2.1 (by positivity) (hMxmom N)
      refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have he : Real.exp ((Cd * M.delta + Cpe * M.delta ^ 2) * N) ≤
          Real.exp (aRate * (N : ℝ)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hrate hN)
      have := mul_le_mul_of_nonneg_left he hCE
      linarith
    exact hmom (BilateralField d) (chaosSampleLaw M).toMeasure (ps i) (hps i) D Mx Mx Kmac
      CD (2 * CE) (max (CbM 0) 0) aRate hCD (by positivity) (le_max_right _ _) haR0 haR
      (fun N o => ⟨(hDMx0 N o).1, (hDMx0 N o).2, (hDMx0 N o).2, hKmac0 N o⟩)
      (fun N => ⟨(hmem N).1.mono_exponent hle, (hmem N).2.mono_exponent hle,
        (hmem N).2.mono_exponent hle, (hKmemN N).mono_exponent hle⟩)
      (fun N => (eLpNorm_le_eLpNorm_of_exponent_le hle (hmem N).1.1).trans (hDmom N))
      hMxN
      (fun N => (eLpNorm_le_eLpNorm_of_exponent_le hle (hKmemN N).1).trans
        ((hKnormN N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))))
  have hKps : ∀ i N, eLpNorm (Kmac N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (max (CbM 0) 0) := by
    intro i N
    have hle : ENNReal.ofReal (ps i) ≤ ENNReal.ofReal Q0 := by
      refine ENNReal.ofReal_le_ofReal ?_
      have := hqi i
      have h2 : ps i ≤ 2 * ps i * max 1 t := by
        have hp := hps i
        calc ps i = ps i * 1 * 1 := by ring
          _ ≤ ps i * 2 * max 1 t := by
            apply mul_le_mul _ hmax1 zero_le_one (by linarith)
            exact mul_le_mul_of_nonneg_left (by norm_num) (by linarith)
          _ = 2 * ps i * max 1 t := by ring
      linarith
    exact (eLpNorm_le_eLpNorm_of_exponent_le hle (hKmemN N).1).trans
      ((hKnormN N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have h2r : 0 ≤ (2 / (1 : ℝ)) ^ t := Real.rpow_nonneg (by positivity) _
  obtain ⟨K, Cbound, hKmem', hKnorm', hK1, hKdom⟩ :=
    aux_prop_growth_energy_assembly_final (chaosSampleLaw M).toMeasure k ps hps t t1 (d : ℝ)
      ((2 / (1 : ℝ)) ^ t) (aux_prop_growth_energy_assembly_Cr d 1 t t1 C) (max (CbM 0) 0) h2r
      (aux_prop_growth_energy_assembly_Cr_nonneg d 1 t t1 C one_pos hC.le) (le_max_right _ _)
      Kmac D Mx (fun N => (hKmemN N).1) (fun N => (hmem N).1.1) (fun N => (hmem N).2.1)
      hKps hB
  refine ⟨fun N om => K (N + j) om, Cbound, fun i N => hKmem' i (N + j), fun i N => hKnorm' i (N + j),
    Filter.Eventually.of_forall (fun om N => hK1 (N + j) om), ?_⟩
  filter_upwards [hKae, hae] with om hmac hen
  intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol x rad hx hrad0 hrad1
  obtain ⟨hMxpos, henvN, hlipN⟩ := hen (N + j)
  have hphys := aux_prop_growth_energy_assembly_physical t t1 C ht0 htt1 ht1d hC hmic M
    (calib3_HT d j) om (N + j) z 1 one_pos le_rfl (Kmac0 N om) (D (N + j) om) (Mx (N + j) om) (hKmac00 N om)
    (hDMx0 (N + j) om).1 hMxpos henvN hlipN
    (hmac N) F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol x rad hx hrad0 hrad1
  refine hphys.trans ?_
  have hE : 0 ≤ (Kf + Cphi) ^ 2 := sq_nonneg _
  have hradt : 0 ≤ rad ^ t := Real.rpow_nonneg hrad0.le _
  have hK' := hKdom (N + j) om
  rw [hKmacF (N + j), Nat.add_sub_cancel] at hK'
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK' hE) hradt

end Paper
