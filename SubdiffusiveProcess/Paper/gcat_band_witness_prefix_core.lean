import SubdiffusiveProcess.Paper.gcat_band_condexp
import SubdiffusiveProcess.Paper.lem_witness

open MeasureTheory Filter Set SubdiffusiveProcess
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper


/-- Single-range budget for the prefix cover: the in-prefix rate `A` is large enough that the tail term
is absorbed already at `H = k0`, so no small-range Markov bound (no smallness of the scores) is needed. -/
theorem aux_gcat_band_witness_core_budget
    (Cband : ℕ) (hCband : 0 < Cband) (c0 k0 : ℕ)
    (beta lam v Cgeom : ℝ) (hbeta : 0 < beta) (hlam : 0 < lam)
    (hv : 0 ≤ v) (hCgeom : 1 ≤ Cgeom)
    (p A Ctail Cp : ℝ) (hp : 2 ≤ p) (hCtail : 0 < Ctail) (hCp : 0 < Cp)
    (hA : 64 * ((Cband : ℝ) + 1) * (beta + v + 1) ≤ A)
    (hAk0 : Real.log (9 * Cgeom * Ctail) + beta * ((Cband : ℝ) + (c0 : ℝ)) ≤
      (A - v - beta * ((Cband : ℝ) + 1)) * (k0 : ℝ))
    (q r : ℝ) (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r) (hr1 : r < 1)
    (hrate : (q / r) ^ p = Real.exp (-(beta * ((Cband : ℝ) + 1) + v + 1))) :
    ∃ eta0 : ℝ, 0 < eta0 ∧
      ∀ eta : ℝ, 0 < eta → eta ≤ eta0 →
        ∀ H : ℕ, k0 ≤ H →
          Cgeom * Ctail * Real.exp (-((A - v) * (H : ℝ))) +
            ((H : ℝ) + 1) * Cgeom * Real.exp (v * (H : ℝ)) *
              Paper.aux_prefix_error p (Cp * eta) q r (lam * (1 - r) / 4) H ≤
          (1 / 3) * ((2 / 3) * Real.exp (-(beta * (((Cband * (H + 1) + c0 + H : ℕ) : ℝ))))) := by
  have hCb1 : (1:ℝ) ≤ (Cband:ℝ) := by exact_mod_cast hCband
  have hCpos : (0:ℝ) < Cgeom := by linarith
  have hCGC_pos : (0:ℝ) < Cgeom * Ctail := mul_pos hCpos hCtail
  have hDpos : 0 < A - v - beta * ((Cband:ℝ)+1) := by
    nlinarith [hA, hbeta, hv, hCb1]
  have hw : ∀ H : ℕ, ((Cband*(H+1)+c0+H : ℕ) : ℝ) = ((Cband:ℝ)+1)*(H:ℝ) + ((Cband:ℝ)+(c0:ℝ)) := by
    intro H; push_cast; ring
  have hlarge_fun : ∀ H : ℕ, k0 ≤ H → Cgeom*Ctail*Real.exp (-((A-v)*(H:ℝ))) ≤
      (1/9)*Real.exp (-(beta*(((Cband:ℝ)+1)*(H:ℝ) + ((Cband:ℝ)+(c0:ℝ))))) := by
    intro H hkH
    have hNH' : (k0:ℝ) ≤ (H:ℝ) := by exact_mod_cast hkH
    have hDH : Real.log (9*Cgeom*Ctail) + beta*((Cband:ℝ)+(c0:ℝ)) ≤
        (A - v - beta*((Cband:ℝ)+1))*(H:ℝ) := by
      have h1 : (A - v - beta*((Cband:ℝ)+1))*(k0:ℝ) ≤ (A - v - beta*((Cband:ℝ)+1))*(H:ℝ) :=
        mul_le_mul_of_nonneg_left hNH' (le_of_lt hDpos)
      exact hAk0.trans h1
    have hlog9 : Real.log (9*Cgeom*Ctail) = Real.log 9 + Real.log Cgeom + Real.log Ctail := by
      have h1 : Real.log (9*Cgeom*Ctail) = Real.log (9*Cgeom) + Real.log Ctail :=
        Real.log_mul (ne_of_gt (mul_pos (by norm_num : (0:ℝ) < 9) hCpos)) (ne_of_gt hCtail)
      have h2 : Real.log (9*Cgeom) = Real.log 9 + Real.log Cgeom :=
        Real.log_mul (by norm_num : (9:ℝ) ≠ 0) (ne_of_gt hCpos)
      rw [h1, h2]
    have hP9pos : (0:ℝ) < 9 * (Cgeom * Ctail * Real.exp (-((A-v)*(H:ℝ)))) := by
      have h3 : (0:ℝ) < Cgeom*Ctail*Real.exp (-((A-v)*(H:ℝ))) := mul_pos hCGC_pos (Real.exp_pos _)
      linarith
    have hgoal9 : (9:ℝ) * (Cgeom * Ctail * Real.exp (-((A-v)*(H:ℝ)))) ≤
        Real.exp (-(beta*(((Cband:ℝ)+1)*(H:ℝ) + ((Cband:ℝ)+(c0:ℝ))))) := by
      rw [← Real.log_le_log_iff hP9pos (Real.exp_pos _)]
      have hL : Real.log (9 * (Cgeom * Ctail * Real.exp (-((A-v)*(H:ℝ))))) =
          Real.log 9 + Real.log Cgeom + Real.log Ctail + (-((A-v)*(H:ℝ))) := by
        rw [Real.log_mul (ne_of_gt (by norm_num : (0:ℝ) < 9)) (ne_of_gt (mul_pos hCGC_pos (Real.exp_pos _))),
            Real.log_mul (ne_of_gt hCGC_pos) (Real.exp_ne_zero _),
            Real.log_mul (ne_of_gt hCpos) (ne_of_gt hCtail),
            Real.log_exp]
        ring
      have hR : Real.log (Real.exp (-(beta*(((Cband:ℝ)+1)*(H:ℝ) + ((Cband:ℝ)+(c0:ℝ)))))) =
          -(beta*(((Cband:ℝ)+1)*(H:ℝ) + ((Cband:ℝ)+(c0:ℝ)))) := Real.log_exp _
      rw [hL, hR]
      nlinarith [hDH, hlog9]
    calc Cgeom*Ctail*Real.exp (-((A-v)*(H:ℝ)))
        = (1/9) * ((9:ℝ) * (Cgeom * Ctail * Real.exp (-((A-v)*(H:ℝ))))) := by ring
      _ ≤ (1/9) * Real.exp (-(beta*(((Cband:ℝ)+1)*(H:ℝ) + ((Cband:ℝ)+(c0:ℝ))))) :=
          mul_le_mul_of_nonneg_left hgoal9 (by norm_num)
  have hKp : (0:ℝ) < lam*(1-r)/4 := by
    have h1r : (0:ℝ) < 1-r := by linarith
    exact div_pos (mul_pos hlam h1r) (by norm_num)
  obtain ⟨eta0, heta0pos, heta0⟩ := aux_prefix_weighted_budget p Cp q r (lam*(1-r)/4)
    (beta*((Cband:ℝ)+1)+v+1) beta v ((Cband:ℝ)+1) ((Cband:ℝ)+(c0:ℝ)) Cgeom (1/9)
    (by linarith : (0:ℝ) < p) hCp hq hr hKp hCpos (by norm_num) rfl hrate
  refine ⟨eta0, heta0pos, ?_⟩
  intro eta heta_pos heta_le H hkH
  have h1 := hlarge_fun H hkH
  have h2 := heta0 eta heta_pos heta_le H
  calc Cgeom*Ctail*Real.exp (-((A-v)*(H:ℝ))) + ((H:ℝ)+1)*Cgeom*Real.exp (v*(H:ℝ))*
        aux_prefix_error p (Cp*eta) q r (lam*(1-r)/4) H
      ≤ (1/9)*Real.exp (-(beta*(((Cband:ℝ)+1)*(H:ℝ) + ((Cband:ℝ)+(c0:ℝ))))) +
        (1/9)*Real.exp (-(beta*(((Cband:ℝ)+1)*(H:ℝ) + ((Cband:ℝ)+(c0:ℝ))))) := add_le_add h1 h2
    _ = (1/3)*((2/3)*Real.exp (-(beta*((Cband*(H+1)+c0+H : ℕ):ℝ)))) := by rw [hw H]; ring


/-- Almost-sure band limits for the countable family of prefix terms and finite tests. -/
theorem aux_gcat_band_witness_core_sigma
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : Measure (BilateralField d)) [IsProbabilityMeasure P]
    (n : ℤ) (Cband J : ℕ) (a Cp eta p : ℝ) (hp : 2 ≤ p) (ha : 0 < a) (hCp : 0 < Cp) (heta : 0 < eta)
    (I : ℕ → Type) [∀ D, Fintype (I D)]
    (s : (D : ℕ) → I D → ℕ → ℤ)
    (Y : (D : ℕ) → I D → ℕ → BilateralField d → ℝ)
    (Yb : (D : ℕ) → I D → ℕ → ℕ → BilateralField d → ℝ)
    (Tt : Fin J → BilateralField d → ℝ) (Ttb : Fin J → ℕ → BilateralField d → ℝ)
    (hYmem : ∀ D i j, MemLp (Y D i j) (ENNReal.ofReal p) P)
    (hTtmem : ∀ i, MemLp (Tt i) (ENNReal.ofReal p) P)
    (hYbmeas : ∀ D i j H, 1 ≤ H →
      StronglyMeasurable[aux_gcat_band_condexp_Bsig d (s D i j - ((Cband * (H + 1) : ℕ) : ℤ))
        (s D i j + ((Cband * (H + 1) : ℕ) : ℤ))] (Yb D i j H))
    (hTtbmeas : ∀ i H, 1 ≤ H →
      StronglyMeasurable[aux_gcat_band_condexp_Bsig d (n - ((Cband * (H + 1) : ℕ) : ℤ))
        (n + ((Cband * (H + 1) : ℕ) : ℤ))] (Ttb i H))
    (hYerr : ∀ D i j H, 1 ≤ H → eLpNorm (fun om => Y D i j om - Yb D i j H om) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (Cp * eta * (3 : ℝ) ^ (-(a * (H : ℝ)))))
    (hTterr : ∀ i H, 1 ≤ H → eLpNorm (fun om => Tt i om - Ttb i H om) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (Cp * eta * (3 : ℝ) ^ (-(a * (H : ℝ))))) :
    ∃ Sigma : Set (BilateralField d), MeasurableSet Sigma ∧ P Sigma = 1 ∧
      (∀ om ∈ Sigma, ∀ D i j, j < D → Tendsto (fun H => Yb D i j (H + 1) om) atTop (𝓝 (Y D i j om))) ∧
      (∀ om ∈ Sigma, ∀ i, Tendsto (fun H => Ttb i (H + 1) om) atTop (𝓝 (Tt i om))) := by
  classical
  have hle := aux_gcat_band_condexp_Bsig_le d
  let Q : Type := (Σ D : ℕ, I D × Fin D) ⊕ Fin J
  haveI : Countable Q := inferInstance
  let Yq : Q → BilateralField d → ℝ := fun q' om =>
    match q' with
    | Sum.inl ⟨D, i, j⟩ => Y D i (j : ℕ) om
    | Sum.inr i => Tt i om
  let Ybq : Q → ℕ → BilateralField d → ℝ := fun q' H om =>
    match q' with
    | Sum.inl ⟨D, i, j⟩ => Yb D i (j : ℕ) (H + 1) om
    | Sum.inr i => Ttb i (H + 1) om
  have hYq : ∀ q', MemLp (Yq q') (ENNReal.ofReal p) P := by
    rintro (⟨D, i, j⟩ | i)
    · exact hYmem D i j
    · exact hTtmem i
  have hYbq : ∀ q' H, AEStronglyMeasurable (Ybq q' H) P := by
    rintro (⟨D, i, j⟩ | i) H
    · exact ((hYbmeas D i (j : ℕ) (H + 1) (by omega)).mono (hle _ _)).aestronglyMeasurable
    · exact ((hTtbmeas i (H + 1) (by omega)).mono (hle _ _)).aestronglyMeasurable
  have hrate3 : ∀ H : ℕ, (3 : ℝ) ^ (-(a * (((H + 1 : ℕ) : ℝ)))) ≤ (3 : ℝ) ^ (-(a * (H : ℝ))) := by
    intro H
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    nlinarith
  have hCpeta : 0 ≤ Cp * eta := (mul_pos hCp heta).le
  have herrq : ∀ q' H, eLpNorm (fun om => Yq q' om - Ybq q' H om) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (Cp * eta * (3 : ℝ) ^ (-(a * (H : ℝ)))) := by
    rintro (⟨D, i, j⟩ | i) H
    · refine (hYerr D i (j : ℕ) (H + 1) (by omega)).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_left (hrate3 H) hCpeta
    · refine (hTterr i (H + 1) (by omega)).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_left (hrate3 H) hCpeta
  obtain ⟨Sigma, hSigmeas, hSigP, hSiglim⟩ :=
    lem_witness_common_ae_limit (BilateralField d) P Q p a Cp eta hp ha hCp heta Yq Ybq hYq hYbq herrq
  refine ⟨Sigma, hSigmeas, hSigP, ?_, ?_⟩
  · intro om hom D i j hj
    simpa [Ybq, Yq] using hSiglim (Sum.inl ⟨D, i, ⟨j, hj⟩⟩) om hom
  · intro om hom i
    simpa [Ybq, Yq] using hSiglim (Sum.inr i) om hom

/-- Prefix part of the abstract cover: the single-range dyadic band cover for the window sums. -/
theorem aux_gcat_band_witness_core_prefix
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : Measure (BilateralField d)) [IsProbabilityMeasure P]
    (n : ℤ) (Cband c0 k0 : ℕ) (hCband : 0 < Cband) (hk0 : 1 ≤ k0)
    (beta a lam v Cgeom : ℝ) (hlam : 0 < lam) (hv : 0 ≤ v) (hCgeom : 1 ≤ Cgeom)
    (p A Ctail Cp eta : ℝ) (hp : 2 ≤ p) (hCtail : 0 < Ctail) (hCp : 0 < Cp) (heta : 0 < eta)
    (q r : ℝ) (hqeq : q = (3 : ℝ) ^ (-a)) (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r) (hr1 : r < 1)
    (hbud : ∀ H : ℕ, k0 ≤ H →
      Cgeom * Ctail * Real.exp (-((A - v) * (H : ℝ))) +
        ((H : ℝ) + 1) * Cgeom * Real.exp (v * (H : ℝ)) *
          aux_prefix_error p (Cp * eta) q r (lam * (1 - r) / 4) H ≤
      (1 / 3) * ((2 / 3) * Real.exp (-(beta * (((Cband * (H + 1) + c0 + H : ℕ) : ℝ))))))
    (I : ℕ → Type) [∀ D, Fintype (I D)]
    (hcard : ∀ D, (Fintype.card (I D) : ℝ) ≤ Cgeom * Real.exp (v * (D : ℝ)))
    (s : (D : ℕ) → I D → ℕ → ℤ)
    (hs : ∀ D i j, j < D → n - (c0 : ℤ) ≤ s D i j ∧ s D i j ≤ n + (c0 : ℤ) + (D : ℤ))
    (Y : (D : ℕ) → I D → ℕ → BilateralField d → ℝ)
    (Yb : (D : ℕ) → I D → ℕ → ℕ → BilateralField d → ℝ)
    (hYmem : ∀ D i j, MemLp (Y D i j) (ENNReal.ofReal p) P)
    (hYbmeas : ∀ D i j H, 1 ≤ H →
      StronglyMeasurable[aux_gcat_band_condexp_Bsig d (s D i j - ((Cband * (H + 1) : ℕ) : ℤ))
        (s D i j + ((Cband * (H + 1) : ℕ) : ℤ))] (Yb D i j H))
    (hYerr : ∀ D i j H, 1 ≤ H → eLpNorm (fun om => Y D i j om - Yb D i j H om) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (Cp * eta * (3 : ℝ) ^ (-(a * (H : ℝ)))))
    (htailP : ∀ D, k0 ≤ D → ∀ i : I D,
      P {om | lam * (D : ℝ) / 4 < ∑ j ∈ Finset.range D, Y D i j om} ≤
        ENNReal.ofReal (Ctail * Real.exp (-(A * (D : ℝ)))))
    (Sigma : Set (BilateralField d))
    (hSiglim : ∀ om ∈ Sigma, ∀ D i j, j < D →
      Tendsto (fun H => Yb D i j (H + 1) om) atTop (𝓝 (Y D i j om))) :
    ∃ Wp : ℕ+ → Set (BilateralField d),
      (∀ h : ℕ+, MeasurableSet[aux_gcat_band_condexp_Bsig d (n - (h : ℤ)) (n + 2 * (h : ℤ))]
        (Wp h)) ∧
      (∀ h : ℕ+, P (Wp h) ≤ ENNReal.ofReal ((3 / 4) * Real.exp (-(beta * ((h : ℕ) : ℝ))))) ∧
      Sigma ∩ {om | ∃ D, k0 ≤ D ∧ ∃ i : I D,
        lam * (D : ℝ) ≤ ∑ j ∈ Finset.range D, Y D i j om} ⊆ ⋃ h : ℕ+, Wp h := by
  classical
  have hp0 : (0 : ℝ) < p := by linarith only [hp]
  have hle := aux_gcat_band_condexp_Bsig_le d
  have hCpeta : 0 ≤ Cp * eta := (mul_pos hCp heta).le
  have hgeom : ∀ H : ℕ, (3 : ℝ) ^ (-(a * (H : ℝ))) = q ^ H := by
    intro H
    calc (3 : ℝ) ^ (-(a * (H : ℝ))) = (3 : ℝ) ^ ((-a) * (H : ℝ)) := by congr 1; ring
      _ = ((3 : ℝ) ^ (-a)) ^ H := Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3) (-a) H
      _ = q ^ H := by rw [hqeq]
  let Ybz : (D : ℕ) → I D → ℕ → ℕ → BilateralField d → ℝ := fun D i j H om =>
    if H = 0 then 0 else Yb D i j H om
  let Tpre : (D : ℕ) → I D → BilateralField d → ℝ := fun D i om =>
    ∑ j ∈ Finset.range D, Y D i j om
  let Upre : (D : ℕ) → I D → ℕ → BilateralField d → ℝ := fun D i H om =>
    ∑ j ∈ Finset.range D, Ybz D i j H om
  have hYbzae : ∀ D i j H, AEStronglyMeasurable (Ybz D i j H) P := by
    intro D i j H
    by_cases hH : H = 0
    · simp only [Ybz, hH, if_true]; exact aestronglyMeasurable_const
    · simp only [Ybz, hH, if_false]
      exact ((hYbmeas D i j H (by omega)).mono (hle _ _)).aestronglyMeasurable
  have hTae : ∀ D i, AEStronglyMeasurable (Tpre D i) P := fun D i =>
    aux_prefix_ae_sum P (fun j => Y D i j) (fun j => (hYmem D i j).1) D
  have hUae : ∀ D i H, AEStronglyMeasurable (Upre D i H) P := fun D i H =>
    aux_prefix_ae_sum P (fun j => Ybz D i j H) (fun j => hYbzae D i j H) D
  have herror : ∀ D H, k0 ≤ D → D ≤ H → ∀ i : I D,
      eLpNorm (fun om => Tpre D i om - Upre D i H om) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal ((D : ℝ) * (Cp * eta) * q ^ H) := by
    intro D H hD hDH i
    have hH1 : 1 ≤ H := hk0.trans (hD.trans hDH)
    have hb := aux_prefix_norm_sum P (fun j => Y D i j) (fun j => Ybz D i j H) D p (Cp * eta * q ^ H)
      (le_trans (by norm_num : (1 : ℝ) ≤ 2) hp) (by positivity)
      (fun j => (hYmem D i j).1) (fun j => hYbzae D i j H)
      (fun j => by
        have hne : H ≠ 0 := by omega
        simpa only [Ybz, hne, if_false, hgeom H] using hYerr D i j H hH1)
    simpa only [Tpre, Upre, mul_assoc] using hb
  let w : ℕ → ℕ+ := fun H => ⟨Cband * (H + 1) + c0 + H, by
    have h1 : 0 < Cband * (H + 1) := Nat.mul_pos hCband (Nat.lt_succ_iff.mpr (Nat.zero_le H))
    omega⟩
  let bound : ℕ+ → ℝ := fun h => (3 / 4) * Real.exp (-(beta * ((h : ℕ) : ℝ)))
  have hw : Function.Injective w := by
    have hstrict : StrictMono w := by
      intro j k hjk
      change Cband * (j + 1) + c0 + j < Cband * (k + 1) + c0 + k
      have hmul := Nat.mul_le_mul_left Cband (Nat.add_le_add_right (Nat.le_of_lt hjk) 1)
      omega
    exact hstrict.injective
  have hwindow : ∀ D H j, k0 ≤ D → D ≤ j → j ≤ H → ∀ i : I D,
      StronglyMeasurable[aux_gcat_band_condexp_Bsig d (n - ((w H : ℕ) : ℤ)) (n + 2 * ((w H : ℕ) : ℤ))]
        (Upre D i j) := by
    intro D H j hD hDj hjH i
    have hj1 : j ≠ 0 := by omega
    refine Finset.stronglyMeasurable_fun_sum
      (m := aux_gcat_band_condexp_Bsig d (n - ((w H : ℕ) : ℤ)) (n + 2 * ((w H : ℕ) : ℤ)))
      (Finset.range D) ?_
    intro t ht
    have htD : t < D := Finset.mem_range.mp ht
    obtain ⟨hs1, hs2⟩ := hs D i t htD
    have hsub : Set.Icc (s D i t - ((Cband * (j + 1) : ℕ) : ℤ)) (s D i t + ((Cband * (j + 1) : ℕ) : ℤ)) ⊆
        Set.Icc (n - ((w H : ℕ) : ℤ)) (n + 2 * ((w H : ℕ) : ℤ)) := by
      intro k hk
      have hwH : ((w H : ℕ) : ℤ) = ((Cband * (H + 1) + c0 + H : ℕ) : ℤ) := rfl
      have hmulle : ((Cband * (j + 1) : ℕ) : ℤ) ≤ ((Cband * (H + 1) : ℕ) : ℤ) := by
        exact_mod_cast Nat.mul_le_mul_left Cband (Nat.add_le_add_right hjH 1)
      have hDH : (D : ℤ) ≤ (H : ℤ) := by exact_mod_cast hDj.trans hjH
      have hcast : ((Cband * (H + 1) + c0 + H : ℕ) : ℤ) =
          ((Cband * (H + 1) : ℕ) : ℤ) + (c0 : ℤ) + (H : ℤ) := by push_cast; ring
      have hnn : (0 : ℤ) ≤ ((Cband * (H + 1) : ℕ) : ℤ) := Int.natCast_nonneg _
      have hH0 : (0 : ℤ) ≤ (H : ℤ) := Int.natCast_nonneg _
      have hc00 : (0 : ℤ) ≤ (c0 : ℤ) := Int.natCast_nonneg _
      simp only [Set.mem_Icc] at hk ⊢
      rw [hwH, hcast]
      constructor <;> omega
    have hmono : aux_gcat_band_condexp_Bsig d (s D i t - ((Cband * (j + 1) : ℕ) : ℤ))
        (s D i t + ((Cband * (j + 1) : ℕ) : ℤ)) ≤
        aux_gcat_band_condexp_Bsig d (n - ((w H : ℕ) : ℤ)) (n + 2 * ((w H : ℕ) : ℤ)) :=
      aux_neg_restrict_mono (E := C(SpatialCoordinates d, ℝ)) hsub
    have hYb' : StronglyMeasurable[aux_gcat_band_condexp_Bsig d (s D i t - ((Cband * (j + 1) : ℕ) : ℤ))
        (s D i t + ((Cband * (j + 1) : ℕ) : ℤ))] (Ybz D i t j) := by
      simp only [Ybz, hj1, if_false]
      exact hYbmeas D i t j (by omega)
    exact hYb'.mono hmono
  have hbudgetW : ∀ H, k0 ≤ H →
      Cgeom * Ctail * Real.exp (-((A - v) * (H : ℝ))) +
        ((H : ℝ) + 1) * Cgeom * Real.exp (v * (H : ℝ)) *
          aux_prefix_error p (Cp * eta) q r (lam * (1 - r) / 4) H ≤ bound (w H) := by
    intro H hH
    have h := hbud H hH
    have hbw : (1 / 3) * ((2 / 3) * Real.exp (-(beta * (((Cband * (H + 1) + c0 + H : ℕ) : ℝ))))) ≤
        bound (w H) := by
      dsimp only [bound]
      have hE : ((w H : ℕ) : ℝ) = ((Cband * (H + 1) + c0 + H : ℕ) : ℝ) := rfl
      rw [hE]
      have hpos := Real.exp_pos (-(beta * (((Cband * (H + 1) + c0 + H : ℕ) : ℝ))))
      linarith only [hpos]
    exact h.trans hbw
  have hlimit : ∀ om, om ∈ Sigma → ∀ D i,
      Tendsto (fun H => Upre D i H om) atTop (𝓝 (Tpre D i om)) := by
    intro om hom D i
    refine tendsto_finset_sum _ (fun j hj => ?_)
    have hjD : j < D := Finset.mem_range.mp hj
    have h1 := hSiglim om hom D i j hjD
    have h2 : Tendsto (fun H => Yb D i j H om) atTop (𝓝 (Y D i j om)) :=
      (tendsto_add_atTop_iff_nat 1).mp h1
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with H hH
    have hne : H ≠ 0 := by omega
    simp [Ybz, hne]
  exact aux_prefix_cover_from_budget (Ω := BilateralField d) P
      (fun h => aux_gcat_band_condexp_Bsig d (n - ((h : ℕ) : ℤ)) (n + 2 * ((h : ℕ) : ℤ)))
      bound w hw k0 hk0 I lam p (Cp * eta) q r (lam * (1 - r) / 4) Cgeom v A Ctail hlam hp0 hCpeta
      hq hq1.le hr hr1 rfl (le_trans zero_le_one hCgeom) hv hCtail.le hcard Tpre Upre hTae hUae
      herror (fun D hD i => htailP D hD i) hwindow hbudgetW Sigma hlimit


/-- Abstract interval-witness cover for the prefix conditions of one cell (level `n`): window sums
`Σ_{j<D} Y D i j` of `L^p` terms over a finite index family with geometric growth, each term having layer-band
approximants, and an exponential exceedance tail of the sums, are covered by band-measurable events of the
prescribed exponential rate.  The threshold `eta0` is produced before the law, the level and the index data;
the scores themselves need no smallness. -/
theorem gcat_band_witness_prefix_core
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cband c0 k0 : ℕ) (hCband : 0 < Cband) (hk0 : 1 ≤ k0)
    (beta a lam v Cgeom : ℝ) (hbeta : 0 < beta) (ha : 0 < a) (hlam : 0 < lam)
    (hv : 0 ≤ v) (hCgeom : 1 ≤ Cgeom)
    (p A Ctail Cp : ℝ) (hp : 2 ≤ p) (hCtail : 0 < Ctail) (hCp : 0 < Cp)
    (hA : 64 * ((Cband : ℝ) + 1) * (beta + v + 1) ≤ A)
    (hpRate : 64 * ((Cband : ℝ) + 1) * (beta + v + 1) ≤ p * a * Real.log 3)
    (hAk0 : Real.log (9 * Cgeom * Ctail) + beta * ((Cband : ℝ) + (c0 : ℝ)) ≤
      (A - v - beta * ((Cband : ℝ) + 1)) * (k0 : ℝ)) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ eta : ℝ, 0 < eta → eta ≤ eta0 →
      ∀ (P : Measure (BilateralField d)) [IsProbabilityMeasure P] (n : ℤ)
        (I : ℕ → Type) [∀ D, Fintype (I D)],
      (∀ D, (Fintype.card (I D) : ℝ) ≤ Cgeom * Real.exp (v * (D : ℝ))) →
      ∀ (s : (D : ℕ) → I D → ℕ → ℤ),
      (∀ D i j, j < D → n - (c0 : ℤ) ≤ s D i j ∧ s D i j ≤ n + (c0 : ℤ) + (D : ℤ)) →
      ∀ (Y : (D : ℕ) → I D → ℕ → BilateralField d → ℝ)
        (Yb : (D : ℕ) → I D → ℕ → ℕ → BilateralField d → ℝ),
      (∀ D i j, MemLp (Y D i j) (ENNReal.ofReal p) P) →
      (∀ D i j H, 1 ≤ H →
        StronglyMeasurable[aux_gcat_band_condexp_Bsig d (s D i j - ((Cband * (H + 1) : ℕ) : ℤ))
          (s D i j + ((Cband * (H + 1) : ℕ) : ℤ))] (Yb D i j H)) →
      (∀ D i j H, 1 ≤ H → eLpNorm (fun om => Y D i j om - Yb D i j H om) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (Cp * eta * (3 : ℝ) ^ (-(a * (H : ℝ))))) →
      (∀ D, k0 ≤ D → ∀ i : I D,
        P {om | lam * (D : ℝ) / 4 < ∑ j ∈ Finset.range D, Y D i j om} ≤
          ENNReal.ofReal (Ctail * Real.exp (-(A * (D : ℝ))))) →
      ∃ Sigma : Set (BilateralField d), MeasurableSet Sigma ∧ P Sigma = 1 ∧
        ∃ W : ℕ+ → Set (BilateralField d),
          (∀ h : ℕ+, MeasurableSet[aux_gcat_band_condexp_Bsig d (n - (h : ℤ)) (n + 2 * (h : ℤ))]
            (W h)) ∧
          (∀ h : ℕ+, P (W h) ≤ ENNReal.ofReal (Real.exp (-(beta * ((h : ℕ) : ℝ))))) ∧
          Sigma ∩ {om | ∃ D, k0 ≤ D ∧ ∃ i : I D,
            lam * (D : ℝ) ≤ ∑ j ∈ Finset.range D, Y D i j om} ⊆ ⋃ h : ℕ+, W h := by
  classical
  have hp0 : (0 : ℝ) < p := by linarith only [hp]
  have hCb1' : (1 : ℝ) ≤ (Cband : ℝ) := by exact_mod_cast hCband
  have hCb1 : (0 : ℝ) < (Cband : ℝ) + 1 := by positivity
  have hX0 : (0 : ℝ) < ((Cband : ℝ) + 1) * (beta + v + 1) := by positivity
  have hpRate' : 64 * ((Cband : ℝ) + 1) * (beta + v + 1) ≤ a * p * Real.log 3 := by
    have h := hpRate; rw [mul_comm p a] at h; exact h
  have hgap : beta * ((Cband : ℝ) + 1) + v + 1 < a * p * Real.log 3 := by
    have h1 : beta * ((Cband : ℝ) + 1) ≤ (beta + v + 1) * ((Cband : ℝ) + 1) := by
      apply mul_le_mul_of_nonneg_right _ hCb1.le
      linarith only [hv]
    have h3 : v + 1 ≤ ((Cband : ℝ) + 1) * (beta + v + 1) := by
      nlinarith only [hbeta, hv, hCb1']
    nlinarith only [h1, h3, hX0, hpRate']
  obtain ⟨q, r, hqeq, hq, hq1, hr, hr1, hrate⟩ :=
    aux_prefix_geometric_rate a (beta * ((Cband : ℝ) + 1) + v + 1) p ha hp0 hgap
  obtain ⟨eta0, heta0, hbudget⟩ :=
    aux_gcat_band_witness_core_budget Cband hCband c0 k0 beta lam v Cgeom hbeta hlam hv hCgeom
      p A Ctail Cp hp hCtail hCp hA hAk0 q r hq hq1 hr hr1 hrate
  refine ⟨eta0, heta0, ?_⟩
  intro eta heta hetale P _ n I instI hcard s hs Y Yb hYmem hYbmeas hYerr htailP
  have hbud := hbudget eta heta hetale
  obtain ⟨Sigma, hSigmeas, hSigP, hSigY, -⟩ :=
    aux_gcat_band_witness_core_sigma d P n Cband 0 a Cp eta p hp ha hCp heta I s Y Yb
      (fun i => i.elim0) (fun i => i.elim0) hYmem (fun i => i.elim0) hYbmeas
      (fun i H _ => i.elim0) hYerr (fun i H _ => i.elim0)
  obtain ⟨Wp, hWpmeas, hWpprob, hWpcover⟩ :=
    aux_gcat_band_witness_core_prefix d P n Cband c0 k0 hCband hk0 beta a lam v Cgeom hlam hv hCgeom
      p A Ctail Cp eta hp hCtail hCp heta q r hqeq hq hq1 hr hr1 hbud I hcard s hs Y Yb hYmem hYbmeas
      hYerr htailP Sigma hSigY
  refine ⟨Sigma, hSigmeas, hSigP, Wp, hWpmeas, fun h => ?_, hWpcover⟩
  refine (hWpprob h).trans (ENNReal.ofReal_le_ofReal ?_)
  have hpos := Real.exp_pos (-(beta * ((h : ℕ) : ℝ)))
  linarith only [hpos]

end Paper
