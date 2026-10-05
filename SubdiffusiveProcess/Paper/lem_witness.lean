module

public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.MultiplicativeChaos.LayerFiltration
public import Mathlib.Data.Fin.Fin2
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.good_event
public import SubdiffusiveProcess.Paper.in_prefix
public import SubdiffusiveProcess.Paper.lem_band
public import SubdiffusiveProcess.Paper.score_family_interface
public import SubdiffusiveProcess.Paper.candidate_good_event
public import SubdiffusiveProcess.Paper.lem_witness_common_ae_limit
public import SubdiffusiveProcess.Paper.lem_witness_prefix_band_measurability
public import SubdiffusiveProcess.Paper.lem_witness_prefix_dyadic_cover
public import SubdiffusiveProcess.Paper.lem_witness_test_dyadic_cover

@[expose] public section

open MeasureTheory Filter Set SubdiffusiveProcess
open _root_.SubdiffusiveProcess.ResponseMoments SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.Paper

theorem aux_lem_witness_bsig_mono {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (Bsig : ℤ → ℤ → MeasurableSpace (BilateralField d))
    (hBsig : ∀ lo hi : ℤ,
      Bsig lo hi = MeasurableSpace.comap
        (fun omega : BilateralField d =>
          fun j : Set.Icc lo hi => omega (-(j : Int)))
        (inferInstance : MeasurableSpace
          ((i : Set.Icc lo hi) → C(SpatialCoordinates d, ℝ))))
    (l₁ r₁ l₂ r₂ : ℤ) (hl : l₂ ≤ l₁) (hr : r₁ ≤ r₂) :
    Bsig l₁ r₁ ≤ Bsig l₂ r₂ := by
  rw [hBsig l₁ r₁, hBsig l₂ r₂]
  refine aux_neg_restrict_mono (E := C(SpatialCoordinates d, ℝ)) ?_
  intro k hk
  exact ⟨hl.trans hk.1, hk.2.trans hr⟩

open scoped Topology

theorem aux_lem_witness_prefix_cover_two_range
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : ℕ+ → MeasurableSpace Ω)
    (bound : ℕ+ → ℝ) (hbound : ∀ h, 0 ≤ bound h)
    (w : ℕ → ℕ+) (hw : Function.Injective w)
    (k0 K : ℕ) (hk0 : 1 ≤ k0) (hKk0 : k0 ≤ K)
    (I : ℕ → Type) [∀ D, Fintype (I D)]
    (lam p M M' q r K' Cgeom v A Ctail : ℝ)
    (hlam : 0 < lam) (hp : 0 < p) (hM : 0 ≤ M) (hM' : 0 ≤ M') (hA0 : 0 ≤ A)
    (hq : 0 < q) (hq1 : q ≤ 1) (hr : 0 < r) (hr1 : r < 1)
    (hKdef : K' = lam * (1 - r) / 4)
    (hCgeom : 0 ≤ Cgeom) (hv : 0 ≤ v) (hCtail : 0 ≤ Ctail)
    (hcard : ∀ D, (Fintype.card (I D) : ℝ) ≤ Cgeom * Real.exp (v * (D : ℝ)))
    (T : (D : ℕ) → I D → Ω → ℝ)
    (U : (D : ℕ) → I D → ℕ → Ω → ℝ)
    (hT : ∀ D i, AEStronglyMeasurable (T D i) P)
    (hU : ∀ D i H, AEStronglyMeasurable (U D i H) P)
    (herror : ∀ D H, k0 ≤ D → D ≤ H → ∀ i : I D,
      eLpNorm (fun om => T D i om - U D i H om) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal ((D : ℝ) * M * q ^ H))
    (htail : ∀ D, k0 ≤ D → ∀ i : I D,
      P {om | lam * (D : ℝ) / 4 < T D i om} ≤
        ENNReal.ofReal (Ctail * Real.exp (-(A * (D : ℝ)))))
    (hbaseMarkov : ∀ D, k0 ≤ D → ∀ i : I D,
      P {om | lam * (D : ℝ) / 4 < T D i om} ≤ ENNReal.ofReal M')
    (hwindow : ∀ D H j, k0 ≤ D → D ≤ j → j ≤ H → ∀ i : I D,
      StronglyMeasurable[B (w H)] (U D i j))
    (hbudgetSmall : ∀ H, k0 ≤ H →
      Cgeom * (M' * Real.exp (A * ((K : ℝ) - 1))) * Real.exp (-((A - v) * (H : ℝ))) +
          ((H : ℝ) + 1) * Cgeom * Real.exp (v * (H : ℝ)) *
            _root_.SubdiffusiveProcess.Paper.aux_prefix_error p M q r K' H ≤ (1 / 3) * bound (w H))
    (hbudgetLarge : ∀ H, K ≤ H →
      Cgeom * Ctail * Real.exp (-((A - v) * (H : ℝ))) +
          ((H : ℝ) + 1) * Cgeom * Real.exp (v * (H : ℝ)) *
            _root_.SubdiffusiveProcess.Paper.aux_prefix_error p M q r K' H ≤ (1 / 3) * bound (w H))
    (Sigma : Set Ω)
    (hlimit : ∀ om, om ∈ Sigma → ∀ D i,
      Tendsto (fun H => U D i H om) atTop (𝓝 (T D i om))) :
    ∃ W : ℕ+ → Set Ω,
      (∀ h, MeasurableSet[B h] (W h)) ∧
      (∀ h, P (W h) ≤ ENNReal.ofReal (bound h)) ∧
      Sigma ∩ {om | ∃ D, k0 ≤ D ∧ ∃ i : I D, lam * (D : ℝ) ≤ T D i om} ⊆
        ⋃ h : ℕ+, W h := by
  have hK1 : 1 ≤ K := hk0.trans hKk0
  have hCtail₁ : 0 ≤ M' * Real.exp (A * ((K : ℝ) - 1)) :=
    mul_nonneg hM' (Real.exp_nonneg _)
  let I₁ : ℕ → Type := fun D => {i : I D // D < K}
  let T₁ : (D : ℕ) → I₁ D → Ω → ℝ := fun D i om => T D i.1 om
  let U₁ : (D : ℕ) → I₁ D → ℕ → Ω → ℝ := fun D i H om => U D i.1 H om
  have hcard₁ : ∀ D, (Fintype.card (I₁ D) : ℝ) ≤ Cgeom * Real.exp (v * (D : ℝ)) := by
    intro D
    have hle : Fintype.card (I₁ D) ≤ Fintype.card (I D) :=
      Fintype.card_subtype_le (fun _ : I D => D < K)
    calc (Fintype.card (I₁ D) : ℝ) ≤ (Fintype.card (I D) : ℝ) := by exact_mod_cast hle
      _ ≤ Cgeom * Real.exp (v * (D : ℝ)) := hcard D
  have htail₁ : ∀ (D : ℕ), k0 ≤ D → ∀ i : I₁ D,
      P {om | lam * (D : ℝ) / 4 < T₁ D i om} ≤
        ENNReal.ofReal ((M' * Real.exp (A * ((K : ℝ) - 1))) * Real.exp (-(A * (D : ℝ)))) := by
    intro D hD i
    refine le_trans (hbaseMarkov D hD i.1) ?_
    apply ENNReal.ofReal_le_ofReal
    have hDle : (D : ℝ) + 1 ≤ (K : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt i.2)
    have harg : 0 ≤ A * ((K : ℝ) - 1 - (D : ℝ)) := by
      have : (0 : ℝ) ≤ (K : ℝ) - 1 - (D : ℝ) := by linarith
      exact mul_nonneg hA0 this
    have hexp1 : (1 : ℝ) ≤ Real.exp (A * ((K : ℝ) - 1 - (D : ℝ))) := by
      simpa using (Real.exp_le_exp.mpr harg)
    have hprod : Real.exp (A * ((K : ℝ) - 1)) * Real.exp (-(A * (D : ℝ)))
        = Real.exp (A * ((K : ℝ) - 1 - (D : ℝ))) := by
      rw [← Real.exp_add]; congr 1; ring
    calc M' = M' * 1 := (mul_one M').symm
      _ ≤ M' * (Real.exp (A * ((K : ℝ) - 1)) * Real.exp (-(A * (D : ℝ)))) :=
            mul_le_mul_of_nonneg_left (by rw [hprod]; exact hexp1) hM'
      _ = M' * Real.exp (A * ((K : ℝ) - 1)) * Real.exp (-(A * (D : ℝ))) := by rw [mul_assoc]
  obtain ⟨W₁, hW₁meas, hW₁prob, hW₁cover⟩ :=
    aux_prefix_cover_from_budget P B (fun h => (1 / 3) * bound h) w hw k0 hk0 I₁
      lam p M q r K' Cgeom v A (M' * Real.exp (A * ((K : ℝ) - 1)))
      hlam hp hM hq hq1 hr hr1 hKdef hCgeom hv hCtail₁ hcard₁ T₁ U₁
      (fun D i => hT D i.1) (fun D i H => hU D i.1 H)
      (fun D H hD hDH i => herror D H hD hDH i.1)
      htail₁
      (fun D H j hD hDj hjH i => hwindow D H j hD hDj hjH i.1)
      hbudgetSmall Sigma
      (fun om homS D i => hlimit om homS D i.1)
  obtain ⟨W₂, hW₂meas, hW₂prob, hW₂cover⟩ :=
    aux_prefix_cover_from_budget P B (fun h => (1 / 3) * bound h) w hw K hK1 I
      lam p M q r K' Cgeom v A Ctail
      hlam hp hM hq hq1 hr hr1 hKdef hCgeom hv hCtail hcard T U
      hT hU
      (fun D H hKD hDH i => herror D H (hKk0.trans hKD) hDH i)
      (fun D hKD i => htail D (hKk0.trans hKD) i)
      (fun D H j hKD hDj hjH i => hwindow D H j (hKk0.trans hKD) hDj hjH i)
      hbudgetLarge Sigma hlimit
  refine ⟨fun h => W₁ h ∪ W₂ h, ?_, ?_, ?_⟩
  · intro h
    exact MeasurableSet.union (hW₁meas h) (hW₂meas h)
  · intro h
    have hb : (0 : ℝ) ≤ bound h := hbound h
    have h13 : (0 : ℝ) ≤ (1 / 3) * bound h := by linarith
    calc P (W₁ h ∪ W₂ h) ≤ P (W₁ h) + P (W₂ h) := measure_union_le (W₁ h) (W₂ h)
      _ ≤ ENNReal.ofReal ((1 / 3) * bound h) + ENNReal.ofReal ((1 / 3) * bound h) :=
            add_le_add (hW₁prob h) (hW₂prob h)
      _ = ENNReal.ofReal ((1 / 3) * bound h + (1 / 3) * bound h) :=
            (ENNReal.ofReal_add h13 h13).symm
      _ ≤ ENNReal.ofReal (bound h) := ENNReal.ofReal_le_ofReal (by linarith)
  · rintro om ⟨homS, D, hD, i, hDi⟩
    by_cases h : D < K
    · have hmem : om ∈ Sigma ∩
          {om | ∃ D, k0 ≤ D ∧ ∃ i : I₁ D, lam * (D : ℝ) ≤ T₁ D i om} :=
        ⟨homS, D, hD, ⟨i, h⟩, hDi⟩
      obtain ⟨h', hh'⟩ := Set.mem_iUnion.mp (hW₁cover hmem)
      exact Set.mem_iUnion.mpr ⟨h', Or.inl hh'⟩
    · have hKD : K ≤ D := le_of_not_gt h
      have hmem : om ∈ Sigma ∩
          {om | ∃ D, K ≤ D ∧ ∃ i : I D, lam * (D : ℝ) ≤ T D i om} :=
        ⟨homS, D, hKD, i, hDi⟩
      obtain ⟨h', hh'⟩ := Set.mem_iUnion.mp (hW₂cover hmem)
      exact Set.mem_iUnion.mpr ⟨h', Or.inr hh'⟩

theorem aux_lem_witness_budgets
    (Cband : ℕ) (hCband : 0 < Cband) (c0 k0 : ℕ) (_hk0 : 1 ≤ k0) (_hc0 : c0 ≤ k0)
    (beta a lam v Cgeom : ℝ) (hbeta : 0 < beta) (_ha : 0 < a) (hlam : 0 < lam)
    (hv : 0 ≤ v) (hCgeom : 1 ≤ Cgeom)
    (p A Ctail Cp : ℝ) (hp : 2 ≤ p) (hCtail : 0 < Ctail) (hCp : 0 < Cp)
    (hA : 64 * ((Cband : ℝ) + 1) * (beta + v + 1) ≤ A)
    (_hpRate : 64 * ((Cband : ℝ) + 1) * (beta + v + 1) ≤ p * a * Real.log 3)
    (q r : ℝ) (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r) (hr1 : r < 1)
    (hrate : (q / r) ^ p = Real.exp (-(beta * ((Cband : ℝ) + 1) + v + 1))) :
    ∃ K : ℕ, k0 ≤ K ∧ ∃ eta0 : ℝ, 0 < eta0 ∧
      ∀ eta : ℝ, 0 < eta → eta ≤ eta0 →
        (∀ H : ℕ, k0 ≤ H →
          Cgeom * ((4 * Cp * eta / lam) ^ p * Real.exp (A * ((K : ℝ) - 1))) *
              Real.exp (-((A - v) * (H : ℝ))) +
            ((H : ℝ) + 1) * Cgeom * Real.exp (v * (H : ℝ)) *
              _root_.SubdiffusiveProcess.Paper.aux_prefix_error p (Cp * eta) q r (lam * (1 - r) / 4) H ≤
          (1 / 3) * ((2 / 3) * Real.exp (-(beta * (((Cband * (H + 1) + c0 + H : ℕ) : ℝ)))))) ∧
        (∀ H : ℕ, K ≤ H →
          Cgeom * Ctail * Real.exp (-((A - v) * (H : ℝ))) +
            ((H : ℝ) + 1) * Cgeom * Real.exp (v * (H : ℝ)) *
              _root_.SubdiffusiveProcess.Paper.aux_prefix_error p (Cp * eta) q r (lam * (1 - r) / 4) H ≤
          (1 / 3) * ((2 / 3) * Real.exp (-(beta * (((Cband * (H + 1) + c0 + H : ℕ) : ℝ)))))) := by
  have hCb1 : (1:ℝ) ≤ (Cband:ℝ) := by exact_mod_cast hCband
  have hCpos : (0:ℝ) < Cgeom := by linarith
  have hCGC_pos : (0:ℝ) < Cgeom * Ctail := mul_pos hCpos hCtail
  have hDpos : 0 < A - v - beta * ((Cband:ℝ)+1) := by
    nlinarith [hA, hbeta, hv, hCb1]
  have hw : ∀ H : ℕ, ((Cband*(H+1)+c0+H : ℕ) : ℝ) = ((Cband:ℝ)+1)*(H:ℝ) + ((Cband:ℝ)+(c0:ℝ)) := by
    intro H; push_cast; ring
  obtain ⟨N, hN⟩ := exists_nat_gt ((Real.log (9*Cgeom*Ctail) + beta*((Cband:ℝ)+(c0:ℝ))) / (A - v - beta*((Cband:ℝ)+1)))
  set K : ℕ := max k0 N with hKdef
  have hkK : k0 ≤ K := by rw [hKdef]; exact le_max_left _ _
  have hNK : N ≤ K := by rw [hKdef]; exact le_max_right _ _
  have hlarge_fun : ∀ H : ℕ, K ≤ H → Cgeom*Ctail*Real.exp (-((A-v)*(H:ℝ))) ≤ (1/9)*Real.exp (-(beta*(((Cband:ℝ)+1)*(H:ℝ) + ((Cband:ℝ)+(c0:ℝ))))) := by
    intro H hKH
    have hNH : N ≤ H := le_trans hNK hKH
    have hNH' : (N:ℝ) ≤ (H:ℝ) := by exact_mod_cast hNH
    have hsN : Real.log (9*Cgeom*Ctail) + beta*((Cband:ℝ)+(c0:ℝ)) < (N:ℝ)*(A - v - beta*((Cband:ℝ)+1)) := by
      have h := hN
      rwa [div_lt_iff₀ hDpos] at h
    have hDH : Real.log (9*Cgeom*Ctail) + beta*((Cband:ℝ)+(c0:ℝ)) ≤ (A - v - beta*((Cband:ℝ)+1))*(H:ℝ) := by
      have h1 : (N:ℝ)*(A - v - beta*((Cband:ℝ)+1)) ≤ (H:ℝ)*(A - v - beta*((Cband:ℝ)+1)) := mul_le_mul_of_nonneg_right hNH' (le_of_lt hDpos)
      calc Real.log (9*Cgeom*Ctail) + beta*((Cband:ℝ)+(c0:ℝ)) ≤ (N:ℝ)*(A - v - beta*((Cband:ℝ)+1)) := le_of_lt hsN
        _ ≤ (H:ℝ)*(A - v - beta*((Cband:ℝ)+1)) := h1
        _ = (A - v - beta*((Cband:ℝ)+1))*(H:ℝ) := by ring
    have hlog9 : Real.log (9*Cgeom*Ctail) = Real.log 9 + Real.log Cgeom + Real.log Ctail := by
      have h1 : Real.log (9*Cgeom*Ctail) = Real.log (9*Cgeom) + Real.log Ctail := Real.log_mul (ne_of_gt (mul_pos (by norm_num : (0:ℝ) < 9) hCpos)) (ne_of_gt hCtail)
      have h2 : Real.log (9*Cgeom) = Real.log 9 + Real.log Cgeom := Real.log_mul (by norm_num : (9:ℝ) ≠ 0) (ne_of_gt hCpos)
      rw [h1, h2]
    have hP9pos : (0:ℝ) < 9 * (Cgeom * Ctail * Real.exp (-((A-v)*(H:ℝ)))) := by
      have h3 : (0:ℝ) < Cgeom*Ctail*Real.exp (-((A-v)*(H:ℝ))) := mul_pos hCGC_pos (Real.exp_pos _)
      linarith
    have hgoal9 : (9:ℝ) * (Cgeom * Ctail * Real.exp (-((A-v)*(H:ℝ)))) ≤ Real.exp (-(beta*(((Cband:ℝ)+1)*(H:ℝ) + ((Cband:ℝ)+(c0:ℝ))))) := by
      rw [← Real.log_le_log_iff hP9pos (Real.exp_pos _)]
      have hL : Real.log (9 * (Cgeom * Ctail * Real.exp (-((A-v)*(H:ℝ))))) = Real.log 9 + Real.log Cgeom + Real.log Ctail + (-((A-v)*(H:ℝ))) := by
        rw [Real.log_mul (ne_of_gt (by norm_num : (0:ℝ) < 9)) (ne_of_gt (mul_pos hCGC_pos (Real.exp_pos _))),
            Real.log_mul (ne_of_gt hCGC_pos) (Real.exp_ne_zero _),
            Real.log_mul (ne_of_gt hCpos) (ne_of_gt hCtail),
            Real.log_exp]
        ring
      have hR : Real.log (Real.exp (-(beta*(((Cband:ℝ)+1)*(H:ℝ) + ((Cband:ℝ)+(c0:ℝ)))))) = -(beta*(((Cband:ℝ)+1)*(H:ℝ) + ((Cband:ℝ)+(c0:ℝ)))) := Real.log_exp _
      rw [hL, hR]
      nlinarith [hDH, hlog9]
    calc Cgeom*Ctail*Real.exp (-((A-v)*(H:ℝ)))
        = (1/9) * ((9:ℝ) * (Cgeom * Ctail * Real.exp (-((A-v)*(H:ℝ))))) := by ring
      _ ≤ (1/9) * Real.exp (-(beta*(((Cband:ℝ)+1)*(H:ℝ) + ((Cband:ℝ)+(c0:ℝ))))) := mul_le_mul_of_nonneg_left hgoal9 (by norm_num)
  set E0 : ℝ := Real.exp (-(beta*(((Cband:ℝ)+1)*(k0:ℝ) + ((Cband:ℝ)+(c0:ℝ))))) with hE0def
  have hE0pos : 0 < E0 := by rw [hE0def]; exact Real.exp_pos _
  set B : ℝ := (1/9)*E0/(Cgeom*Real.exp (A*((K:ℝ)-1))*Real.exp (-((A-v)*(k0:ℝ)))) with hBdef
  have hBpos : 0 < B := by
    rw [hBdef]
    exact div_pos (mul_pos (by norm_num) hE0pos) (mul_pos (mul_pos hCpos (Real.exp_pos _)) (Real.exp_pos _))
  obtain ⟨eta0₁, heta0₁pos, heta0₁⟩ := aux_prefix_small_coefficient p Cp (lam/2) 1 B (by linarith : (0:ℝ) < p) hCp (by linarith) (by norm_num) hBpos
  have hKp : (0:ℝ) < lam*(1-r)/4 := by
    have h1r : (0:ℝ) < 1-r := by linarith
    exact div_pos (mul_pos hlam h1r) (by norm_num)
  obtain ⟨eta0₂, heta0₂pos, heta0₂⟩ := aux_prefix_weighted_budget p Cp q r (lam*(1-r)/4) (beta*((Cband:ℝ)+1)+v+1) beta v ((Cband:ℝ)+1) ((Cband:ℝ)+(c0:ℝ)) Cgeom (1/9) (by linarith : (0:ℝ) < p) hCp hq hr hKp hCpos (by norm_num) rfl hrate
  refine ⟨K, hkK, min eta0₁ eta0₂, lt_min heta0₁pos heta0₂pos, ?_⟩
  intro eta heta_pos heta_le
  have heta1 : eta ≤ eta0₁ := le_trans heta_le (min_le_left _ _)
  have heta2 : eta ≤ eta0₂ := le_trans heta_le (min_le_right _ _)
  have h2f : ∀ H : ℕ, ((H:ℝ)+1)*Cgeom*Real.exp (v*(H:ℝ))*aux_prefix_error p (Cp*eta) q r (lam*(1-r)/4) H ≤ (1/9)*Real.exp (-(beta*(((Cband:ℝ)+1)*(H:ℝ) + ((Cband:ℝ)+(c0:ℝ))))) := fun H => heta0₂ eta heta_pos heta2 H
  constructor
  · intro H hkH
    have hkH' : (k0:ℝ) ≤ (H:ℝ) := by exact_mod_cast hkH
    have hmain_exp : Real.exp (-(beta*(((Cband:ℝ)+1)*(k0:ℝ)+((Cband:ℝ)+(c0:ℝ)))) + (A-v)*((k0:ℝ)-(H:ℝ))) ≤ Real.exp (-(beta*(((Cband:ℝ)+1)*(H:ℝ)+((Cband:ℝ)+(c0:ℝ))))) := by
      rw [Real.exp_le_exp]
      have hDk : (0:ℝ) ≤ (A - v - beta*((Cband:ℝ)+1))*((H:ℝ)-(k0:ℝ)) := mul_nonneg (le_of_lt hDpos) (by linarith)
      nlinarith [hDk]
    have hconvert : 2*(Cp*eta)/(lam/2*1) = 4*Cp*eta/lam := by
      have hne : lam ≠ 0 := ne_of_gt hlam
      field_simp
      ring
    have hsmall_coeff : (4*Cp*eta/lam)^p ≤ B := by
      have hh := heta0₁ eta heta_pos heta1
      rw [hconvert] at hh
      exact hh
    have hBF0 : Cgeom*(B*Real.exp (A*((K:ℝ)-1)))*Real.exp (-((A-v)*(k0:ℝ))) = (1/9)*E0 := by
      rw [hBdef]
      field_simp
    have hcancel : Real.exp (-((A-v)*(k0:ℝ)))*Real.exp ((A-v)*(k0:ℝ)) = 1 := by
      rw [← Real.exp_add, show -((A-v)*(k0:ℝ)) + (A-v)*(k0:ℝ) = 0 by ring, Real.exp_zero]
    have h2eq : Cgeom*(B*Real.exp (A*((K:ℝ)-1))) = (1/9)*E0*Real.exp ((A-v)*(k0:ℝ)) := by
      have hstep : Cgeom*(B*Real.exp (A*((K:ℝ)-1)))*Real.exp (-((A-v)*(k0:ℝ)))*Real.exp ((A-v)*(k0:ℝ)) = (1/9)*E0*Real.exp ((A-v)*(k0:ℝ)) := by
        rw [hBF0]
      rw [mul_assoc (Cgeom*(B*Real.exp (A*((K:ℝ)-1)))) (Real.exp (-((A-v)*(k0:ℝ)))) (Real.exp ((A-v)*(k0:ℝ))), hcancel, mul_one] at hstep
      exact hstep
    have hi : Cgeom*(B*Real.exp (A*((K:ℝ)-1)))*Real.exp (-((A-v)*(H:ℝ))) = (1/9)*(E0*Real.exp ((A-v)*(k0:ℝ))*Real.exp (-((A-v)*(H:ℝ)))) := by
      rw [h2eq]; ring
    have hii : E0*Real.exp ((A-v)*(k0:ℝ))*Real.exp (-((A-v)*(H:ℝ))) ≤ Real.exp (-(beta*(((Cband:ℝ)+1)*(H:ℝ)+((Cband:ℝ)+(c0:ℝ))))) := by
      have heq : E0*Real.exp ((A-v)*(k0:ℝ))*Real.exp (-((A-v)*(H:ℝ))) = Real.exp (-(beta*(((Cband:ℝ)+1)*(k0:ℝ)+((Cband:ℝ)+(c0:ℝ)))) + (A-v)*((k0:ℝ)-(H:ℝ))) := by
        rw [hE0def, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [heq]; exact hmain_exp
    have hle2 : Cgeom*(B*Real.exp (A*((K:ℝ)-1)))*Real.exp (-((A-v)*(H:ℝ))) ≤ (1/9)*Real.exp (-(beta*(((Cband:ℝ)+1)*(H:ℝ)+((Cband:ℝ)+(c0:ℝ))))) := by
      rw [hi]; exact mul_le_mul_of_nonneg_left hii (by norm_num)
    have hle1 : Cgeom*((4*Cp*eta/lam)^p*Real.exp (A*((K:ℝ)-1)))*Real.exp (-((A-v)*(H:ℝ))) ≤ Cgeom*(B*Real.exp (A*((K:ℝ)-1)))*Real.exp (-((A-v)*(H:ℝ))) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hCpos)
      exact mul_le_mul_of_nonneg_right hsmall_coeff (Real.exp_nonneg _)
    have hmain1 := le_trans hle1 hle2
    have hmain2 := h2f H
    calc Cgeom*((4*Cp*eta/lam)^p*Real.exp (A*((K:ℝ)-1)))*Real.exp (-((A-v)*(H:ℝ))) + ((H:ℝ)+1)*Cgeom*Real.exp (v*(H:ℝ))*aux_prefix_error p (Cp*eta) q r (lam*(1-r)/4) H
        ≤ (1/9)*Real.exp (-(beta*(((Cband:ℝ)+1)*(H:ℝ)+((Cband:ℝ)+(c0:ℝ))))) + (1/9)*Real.exp (-(beta*(((Cband:ℝ)+1)*(H:ℝ)+((Cband:ℝ)+(c0:ℝ))))) := add_le_add hmain1 hmain2
      _ = (1/3)*((2/3)*Real.exp (-(beta*((Cband*(H+1)+c0+H : ℕ):ℝ)))) := by rw [hw H]; ring
  · intro H hKH
    have h1 := hlarge_fun H hKH
    have h2 := h2f H
    calc Cgeom*Ctail*Real.exp (-((A-v)*(H:ℝ))) + ((H:ℝ)+1)*Cgeom*Real.exp (v*(H:ℝ))*aux_prefix_error p (Cp*eta) q r (lam*(1-r)/4) H
        ≤ (1/9)*Real.exp (-(beta*(((Cband:ℝ)+1)*(H:ℝ) + ((Cband:ℝ)+(c0:ℝ))))) + (1/9)*Real.exp (-(beta*(((Cband:ℝ)+1)*(H:ℝ) + ((Cband:ℝ)+(c0:ℝ))))) := add_le_add h1 h2
      _ = (1/3)*((2/3)*Real.exp (-(beta*((Cband*(H+1)+c0+H : ℕ):ℝ)))) := by rw [hw H]; ring

open scoped Topology

theorem aux_lem_witness_sigma_exists
    (d : ℕ) (_hd : 1 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : Measure (BilateralField d)) [IsProbabilityMeasure P]
    (p a Cp : ℝ) (hp : 2 ≤ p) (ha : 0 < a) (hCp : 0 < Cp) (eta : ℝ) (heta : 0 < eta)
    (I : ℕ → Type) [∀ D, Fintype (I D)]
    (start : (n : ℤ) → (D : ℕ) → I D → ℤ)
    (centre : (D : ℕ) → I D → SpatialCoordinates d)
    (_tag : (D : ℕ) → I D → Fin2 2) (J : ℕ)
    (X : Fin2 2 → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
    (Xb : Fin2 2 → ℤ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
    (T : ℤ → Fin J → BilateralField d → ℝ)
    (Tb : ℤ → Fin J → ℕ → BilateralField d → ℝ)
    (hXmem : ∀ q n z, MemLp (X q n z) (ENNReal.ofReal p) P)
    (hTmem : ∀ n i, MemLp (T n i) (ENNReal.ofReal p) P)
    (hXbae : ∀ q n H z, AEStronglyMeasurable (Xb q n H z) P)
    (hTbae : ∀ n i H, AEStronglyMeasurable (Tb n i H) P)
    (hXerr : ∀ q n H z, eLpNorm (fun om => X q n z om - Xb q n H z om) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (Cp * eta * (3 : ℝ) ^ (-(a * (H : ℝ)))))
    (hTerr : ∀ n i H, eLpNorm (fun om => T n i om - Tb n i H om) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (Cp * eta * (3 : ℝ) ^ (-(a * (H : ℝ))))) :
    ∃ Sigma : Set (BilateralField d), MeasurableSet Sigma ∧ P Sigma = 1 ∧
      ∀ om, om ∈ Sigma →
        (∀ q n D i j, Tendsto (fun H => Xb q (start n D i + (j : ℤ)) H (centre D i) om)
          atTop (𝓝 (X q (start n D i + (j : ℤ)) (centre D i) om))) ∧
        (∀ n i, Tendsto (fun H => Tb n i H om) atTop (𝓝 (T n i om))) := by
  classical
    let Q := (Fin2 2 × ℤ × (Sigma (fun D : ℕ => I D)) × ℤ) ⊕ (ℤ × Fin J)
    let Y : Q → BilateralField d → ℝ := fun q om =>
      match q with
      | Sum.inl ⟨q, n, ⟨D, i⟩, j⟩ => X q (start n D i + (j : ℤ)) (centre D i) om
      | Sum.inr ⟨n, i⟩ => T n i om
    let Yb : Q → ℕ → BilateralField d → ℝ := fun q H om =>
      match q with
      | Sum.inl ⟨q, n, ⟨D, i⟩, j⟩ => Xb q (start n D i + (j : ℤ)) H (centre D i) om
      | Sum.inr ⟨n, i⟩ => Tb n i H om
    have hY : ∀ q, MemLp (Y q) (ENNReal.ofReal p) P := by
      rintro (⟨q, n, ⟨D, i⟩, j⟩ | ⟨n, i⟩)
      · exact hXmem q (start n D i + (j : ℤ)) (centre D i)
      · exact hTmem n i
    have hYb : ∀ q H, AEStronglyMeasurable (Yb q H) P := by
      rintro (⟨q, n, ⟨D, i⟩, j⟩ | ⟨n, i⟩) H
      · exact hXbae q (start n D i + (j : ℤ)) H (centre D i)
      · exact hTbae n i H
    have herr : ∀ q H, eLpNorm (fun om => Y q om - Yb q H om) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (Cp * eta * (3 : ℝ) ^ (-(a * (H : ℝ)))) := by
      rintro (⟨q, n, ⟨D, i⟩, j⟩ | ⟨n, i⟩) H
      · exact hXerr q (start n D i + (j : ℤ)) H (centre D i)
      · exact hTerr n i H
    obtain ⟨Sigma, hmeas, hP, hlim⟩ :=
      _root_.SubdiffusiveProcess.Paper.lem_witness_common_ae_limit (BilateralField d) P Q p a Cp eta hp ha hCp heta
        Y Yb hY hYb herr
    refine ⟨Sigma, hmeas, hP, ?_⟩
    intro om hom
    refine ⟨?_, ?_⟩
    · intro q n D i j
      exact hlim (Sum.inl ⟨q, n, ⟨D, i⟩, j⟩) om hom
    · intro n i
      exact hlim (Sum.inr ⟨n, i⟩) om hom

/--
`mfd:lem-witness`, full prefix-and-finite-test
probability form.

Scope and inputs:

* exact band: every witness `W h` is measurable in
  `Bsig (n - h) (n + 2*h)`, with `Bsig` pinned by the exact original-layer
  observation equality `hBsig` on the concrete `BilateralField d` layer
  space;
* uniform threshold: one `eta0` is chosen before the random data and test
  functions, and the assertion is uniform for every `0 < eta <= eta0`;
* complete prefix sum and entropy: the conclusion covers all depths `D` with
  `k0 <= D`, all catalogue codes `i : I D`, and uses the explicit finite
  cardinality bound `Fintype.card (I D) <= Cgeom * exp (v*D)`;
* both score tags: `Fin2 2` indexes both admissible score species throughout
  `X` and `Xb`;
* initial/additional baseline bounds: both every score `X q n z` and every
  finite test `T n i` have the stated `L^p` baseline bound, and both have the
  corresponding band approximants and band errors;
* all `D`: the prefix large-deviation supplier is stated for every `n`, every
  `D` with `k0 <= D`, and every catalogue code, with one common observation
  anchor `n` and coherent interval `start n D i + range D`;
* failure at non-strict boundary: `G` is defined using strict good inequalities
  `< lam`, so `(G n)ᶜ` includes the failure boundary `>= lam` and is covered;
* arbitrary positive `a`: only `0 < a` is assumed, while the safe rate margins
  are expressed by `hA` and `hpRate` without imposing `a > log 2` or
  `a > log 3`;
* beta chosen before p before amplitude: `beta`, then `p` and its rate margin,
  are fixed before the small-disorder threshold `eta0` is produced;
* no field smuggling witness conclusion: no witness events or witness
  probability bounds are hypotheses; the theorem concludes the measurable
  events, their probability bounds, and the cover itself.

The quantitative catalogue must identify its event with the fully parameterized
`candidate_good_event` instance via `G n ⊆ GE`; the measure is identified with
the same model law. The cover below is literally for that candidate event.
No witness or probability conclusion is supplied by the identification.

The full-measure `Sigma` version below is an explicit recorded representation
choice: the `L^p` data are fixed only almost everywhere, so this is not an
exact pointwise cover on all `omega`.  All finite initial tests are included
in the single family `T`; an additional scalar or matrix-norm test can extend
`J`, and `J` may be zero, so no separate theorem is needed.  No source-approval
claim is made.


Carried-input scope and inputs:
- candidate_good_event  supplies the complete concrete event parameters.
- The law equality and G n ⊆ GE identify the quantitative tests with that instance.
- Sigma remains before every observation index and every candidate instance; witnesses remain conclusions.
-/
/- The score/band/prefix premises below are the abstract interface of the witness
construction. The actual-model supplier is SubdiffusiveProcess.Paper.gcat_band_witness: it derives
its score banks from lem_band and prefix_physical_tail, and uses gcat_prefix_limits
and gcat_finite_scores to identify the extracted good event. In that concrete
instance, X/Xb are the two limit prefix-score arrays and their band approximants;
T/Tb are the ramped finite-test arrays and their band approximants. The inclusion
G n ⊆ GE is the corresponding prefix-and-test conjunction. The paper-facing
actual-model witness supplier is gcat_band_witness, which is applied inside the
full all-chain construction; this declaration retains the additional-test
interface of mfd:lem-witness. No probability or witness-event output is assumed. -/
theorem lem_witness
    (d : ℕ) (hd : 1 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : Measure (BilateralField d)) [IsProbabilityMeasure P]
    (Bsig : ℤ → ℤ → MeasurableSpace (BilateralField d))
    (hBsig : ∀ lo hi : ℤ,
      Bsig lo hi = MeasurableSpace.comap
        (fun omega : BilateralField d =>
          fun j : Set.Icc lo hi => omega (-(j : Int)))
        (inferInstance : MeasurableSpace
          ((i : Set.Icc lo hi) → C(SpatialCoordinates d, ℝ))))
    (Cband : ℕ) (hCband : 0 < Cband)
    (c0 k0 J : ℕ) (hk0 : 1 ≤ k0) (hc0 : c0 ≤ k0)
    (beta a lam v Cgeom : ℝ)
    (hbeta : 0 < beta) (ha : 0 < a) (hlam : 0 < lam)
    (hv : 0 ≤ v) (hCgeom : 1 ≤ Cgeom)
    (p A Ctail Cp : ℝ)
    (hp : 2 ≤ p) (hCtail : 0 < Ctail) (hCp : 0 < Cp)
    (hA : 64 * ((Cband : ℝ) + 1) * (beta + v + 1) ≤ A)
    (hpRate : 64 * ((Cband : ℝ) + 1) * (beta + v + 1) ≤
      p * a * Real.log 3)
    : ∃ eta0 : ℝ, 0 < eta0 ∧
        ∀ eta : ℝ, 0 < eta → eta ≤ eta0 →
          ∀ (I : ℕ → Type) [∀ D, Fintype (I D)],
          ∀ (start : (n : ℤ) → (D : ℕ) → I D → ℤ),
          ∀ (centre : (D : ℕ) → I D → SpatialCoordinates d),
          ∀ (tag : (D : ℕ) → I D → Fin2 2),
          (∀ D, (Fintype.card (I D) : ℝ) ≤
            Cgeom * Real.exp (v * (D : ℝ))) →
          (∀ n D i,
            n - (c0 : ℤ) ≤ start n D i ∧
              start n D i ≤ n + (c0 : ℤ)) →
          ∀ (X : Fin2 2 → ℤ → SpatialCoordinates d →
            BilateralField d → ℝ),
          ∀ (Xb : Fin2 2 → ℤ → ℕ → SpatialCoordinates d →
            BilateralField d → ℝ),
          ∀ (T : ℤ → Fin J → BilateralField d → ℝ),
          ∀ (Tb : ℤ → Fin J → ℕ → BilateralField d → ℝ),
          (∀ q n z, MemLp (X q n z) (ENNReal.ofReal p) P) →
          (∀ n i, MemLp (T n i) (ENNReal.ofReal p) P) →
          (∀ q n z, eLpNorm (X q n z) (ENNReal.ofReal p) P ≤
            ENNReal.ofReal (Cp * eta)) →
          (∀ n i, eLpNorm (T n i) (ENNReal.ofReal p) P ≤
            ENNReal.ofReal (Cp * eta)) →
          (∀ q n H z,
            StronglyMeasurable[
              Bsig (n - ((Cband * (H + 1) : ℕ) : ℤ))
                (n + ((Cband * (H + 1) : ℕ) : ℤ))]
              (Xb q n H z)) →
          (∀ n i H,
            StronglyMeasurable[
              Bsig (n - ((Cband * (H + 1) : ℕ) : ℤ))
                (n + ((Cband * (H + 1) : ℕ) : ℤ))]
              (Tb n i H)) →
          (∀ q n H z,
            eLpNorm (fun om => X q n z om - Xb q n H z om)
                (ENNReal.ofReal p) P ≤
              ENNReal.ofReal
                (Cp * eta * (3 : ℝ) ^ (-(a * (H : ℝ))))) →
          (∀ n i H,
            eLpNorm (fun om => T n i om - Tb n i H om)
                (ENNReal.ofReal p) P ≤
              ENNReal.ofReal
                (Cp * eta * (3 : ℝ) ^ (-(a * (H : ℝ))))) →
          (∀ n D, k0 ≤ D → ∀ i : I D,
            P {om |
                lam * (D : ℝ) / 4 <
                  ∑ j ∈ Finset.range D,
                    X (tag D i) (start n D i + (j : ℤ)) (centre D i) om} ≤
              ENNReal.ofReal (Ctail * Real.exp (-(A * (D : ℝ))))) →
          let G : ℤ → Set (BilateralField d) := fun n => {om |
            (∀ D : ℕ, k0 ≤ D → ∀ i : I D,
              (∑ j ∈ Finset.range D,
                X (tag D i) (start n D i + (j : ℤ)) (centre D i) om) <
                lam * (D : ℝ)) ∧
            (∀ i : Fin J, T n i om < lam)}
          ∃ Sigma : Set (BilateralField d), MeasurableSet Sigma ∧
            P Sigma = 1 ∧
            ∀ n : ℤ, ∀ (cand_hd : 2 ≤ d)
    (cand_I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (cand_M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (cand_H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (cand_hMH : InfraredCharacterization cand_M cand_H)
    (cand_k : ℕ) (cand_z : SpatialCoordinates d)
    (cand_qside : ℝ)
    (cand_hqside : cand_qside = (3 : ℝ) ^ (-(cand_k : ℤ)))
    (cand_qcenter : SpatialCoordinates d)
    (cand_hqcenter : cand_qcenter = cand_z)
    (cand_Enl cand_Shift cand_Cmp : Type)
    [Fintype cand_Enl] [Fintype cand_Shift] [Fintype cand_Cmp]
    (cand_selfE : cand_Enl) (cand_selfShift : cand_Shift)
    (cand_qRoot : cand_Enl × cand_Shift)
    (cand_hqRoot : cand_qRoot = (cand_selfE, cand_selfShift))
    (cand_factor : cand_Enl → ℕ)
    (cand_hfactor : cand_factor cand_selfE = 0)
    (cand_padE : cand_Enl) (cand_hpad : cand_factor cand_padE = 1)
    (cand_shift : cand_Shift → SpatialCoordinates d)
    (cand_hshift : cand_shift cand_selfShift = 0)
    (cand_rootLevel : cand_Enl × cand_Shift → ℤ)
    (cand_hrootLevel : ∀ (e : cand_Enl) (t : cand_Shift),
      cand_rootLevel (e, t) = (cand_k : ℤ) - (cand_factor e : ℤ))
    (cand_rootSide : cand_Enl × cand_Shift → ℝ)
    (cand_hrootSide : ∀ (U : cand_Enl × cand_Shift),
      cand_rootSide U = (3 : ℝ) ^ (-cand_rootLevel U))
    (cand_rootCentre : cand_Enl × cand_Shift → SpatialCoordinates d)
    (cand_hrootCentre : ∀ (e : cand_Enl) (t : cand_Shift),
      cand_rootCentre (e, t) = cand_qcenter + cand_rootSide (e, t) • cand_shift t)
    (cand_rootPos : ∀ (U : cand_Enl × cand_Shift), 0 < cand_rootSide U)
    (cand_hGridCover : ∀ (x : SpatialCoordinates d), x ∈ Metric.closedBall cand_z (cand_qside / 2) →
      ∀ rho : ℝ, 0 < rho → rho ≤ cand_qside →
        ∃ (U : cand_Enl × cand_Shift) (D : ℕ) (w : Fin D → OddGridIndex d 1),
          Metric.ball x (rho / 2) ⊆
            Metric.ball (descendantCenter 1 (cand_rootCentre U) (cand_rootSide U) D w)
              (descendantSide 1 D (cand_rootSide U) / 2) ∧
          descendantSide 1 D (cand_rootSide U) ≤ 9 * rho)
    (cand_parent : cand_Cmp → cand_Enl × cand_Shift)
    (cand_depth : cand_Cmp → ℕ)
    (cand_word : (c : cand_Cmp) → Fin (cand_depth c) → OddGridIndex d 1)
    (cand_cmpCentre : cand_Cmp → SpatialCoordinates d)
    (cand_hcmpCentre : ∀ (c : cand_Cmp),
      cand_cmpCentre c =
        descendantCenter 1 (cand_rootCentre (cand_parent c)) (cand_rootSide (cand_parent c))
          (cand_depth c) (cand_word c))
    (cand_cmpLevel : cand_Cmp → ℤ)
    (cand_hcmpLevel : ∀ (c : cand_Cmp),
      cand_cmpLevel c = cand_rootLevel (cand_parent c) + (cand_depth c : ℤ))
    (cand_cmpSide : cand_Cmp → ℝ)
    (cand_hcmpSide : ∀ (c : cand_Cmp), cand_cmpSide c = (3 : ℝ) ^ (-cand_cmpLevel c))
    (cand_cmpPos : ∀ (c : cand_Cmp), 0 < cand_cmpSide c)
    (cand_chosen : cand_Cmp)
    (cand_observationCentre :
      ∀ (_U : cand_Enl × cand_Shift) (D : ℕ),
        ((Fin D → OddGridIndex d 1) ⊕ (cand_Enl × cand_Shift)) →
          SpatialCoordinates d)
    (cand_hObservationCentre : ∀ (U : cand_Enl × cand_Shift) (D : ℕ)
      (code : (Fin D → OddGridIndex d 1) ⊕ (cand_Enl × cand_Shift)),
      cand_observationCentre U D code =
        Sum.elim
          (fun w => descendantCenter 1 (cand_rootCentre U) (cand_rootSide U) D w)
          (fun V => cand_rootCentre V) code)
    (cand_eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (cand_hEta : ∀ᵐ omega ∂(chaosSampleLaw cand_M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d),
        cand_eta N omega i y =
          omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (cand_F cand_Praw cand_Rraw cand_Draw : ℕ → ℕ → Vec d → BilateralField d → ENNReal)
    (cand_Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
    (cand_rawGood : ℕ → ℕ → Vec d → BilateralField d → Prop)
    (cand_s cand_eps : ℝ)
    (cand_hs : cand_s ∈ Set.Ioc (0 : ℝ) 1)
    (cand_heps : cand_eps ∈ Set.Ioo (0 : ℝ) 1)
    (cand_hPrimitive : ∀ᵐ omega ∂(chaosSampleLaw cand_M).toMeasure,
      ∀ N : ℕ,
        primitive_scores d cand_M cand_s cand_eps (cand_eta N omega)
          (fun m y => cand_F N m y omega)
          (fun m y => cand_Praw N m y omega)
          (fun m y => cand_Rraw N m y omega)
          (fun m y => cand_Draw N m y omega)
          (fun m y => cand_Z N m y omega)
          (fun m y => cand_rawGood N m y omega))
    (cand_cbuf cand_k0 : ℕ)
    (cand_lambdaCut cand_lambdaLim cand_lambdaDet cand_sigma cand_cell cand_epshom cand_cdet : ℝ)
    (cand_hThresholds :
      0 < cand_lambdaCut ∧ cand_lambdaCut < cand_lambdaLim ∧
      cand_lambdaLim < cand_lambdaDet ∧ cand_lambdaDet < 1)
    (cand_hsigma : cand_sigma ∈ Set.Ioc (0 : ℝ) 1)
    (cand_hcell : cand_cell ∈ Set.Ioo (0 : ℝ) 1)
    (cand_hepshom : 0 < cand_epshom)
    (cand_hcdet : 0 < cand_cdet)
    (cand_prefixZ : ∀ (_N : ℕ) (_U : cand_Enl × cand_Shift) (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (cand_Enl × cand_Shift)) →
        BilateralField d → ℝ)
    (cand_prefixD : ∀ (_N : ℕ) (_U : cand_Enl × cand_Shift) (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (cand_Enl × cand_Shift)) →
        BilateralField d → ℝ)
    (cand_hPrefixZ : ∀ (N : ℕ) (U : cand_Enl × cand_Shift) (D : ℕ)
      (code : (Fin D → OddGridIndex d 1) ⊕ (cand_Enl × cand_Shift)) (omega : BilateralField d),
      cand_prefixZ N U D code omega =
        if cand_rootLevel U + (D : ℤ) ≤ (N : ℤ) then
          ∑ j ∈ Finset.Icc (cand_rootLevel U - (cand_cbuf : ℤ))
            (cand_rootLevel U + (D : ℤ)),
            if 0 ≤ (N : ℤ) - j then
              cand_Z N ((N : ℤ) - j).toNat
                (((3 : ℝ) ^ N) • cand_observationCentre U D code) omega
            else 0
        else 0)
    (cand_hPrefixD : ∀ (N : ℕ) (U : cand_Enl × cand_Shift) (D : ℕ)
      (code : (Fin D → OddGridIndex d 1) ⊕ (cand_Enl × cand_Shift)) (omega : BilateralField d),
      cand_prefixD N U D code omega =
        if cand_rootLevel U + (D : ℤ) ≤ (N : ℤ) then
          ∑ j ∈ Finset.Icc (cand_rootLevel U - (cand_cbuf : ℤ))
            (cand_rootLevel U + (D : ℤ)),
            if 0 ≤ (N : ℤ) - j then
              (cand_Draw N ((N : ℤ) - j).toNat
                (((3 : ℝ) ^ N) • cand_observationCentre U D code) omega).toReal
            else 0
        else 0)
    (cand_hFiniteScoreGuard : ∀ᵐ omega ∂(chaosSampleLaw cand_M).toMeasure,
      ∀ (N : ℕ) (U : cand_Enl × cand_Shift) (D : ℕ)
        (code : (Fin D → OddGridIndex d 1) ⊕ (cand_Enl × cand_Shift)),
        cand_rootLevel U + (D : ℤ) ≤ (N : ℤ) →
        ∀ j ∈ Finset.Icc (cand_rootLevel U - (cand_cbuf : ℤ))
          (cand_rootLevel U + (D : ℤ)),
          cand_Draw N ((N : ℤ) - j).toNat
            (((3 : ℝ) ^ N) • cand_observationCentre U D code) omega ≠ ⊤)
    (cand_sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ)
    (cand_hsN : ∀ (N : ℕ) (l : ℤ) (w : SpatialCoordinates d)
      (omega : BilateralField d),
      cand_sN N l w omega =
        if l ≤ (N : ℤ) then
          (let kappa : ℕ → ℝ := fun J =>
            Real.exp (((J : ℝ) + 1) *
              _root_.SubdiffusiveProcess.Model.tauSq cand_M.P) *
              SubdiffusiveProcess.CoarseGrainingVocab.ahom cand_M J
           let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
             fun ell v beta =>
               if 0 ≤ ell then
                 ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
               else
                 -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
           kappa ((N : ℤ) - l).toNat / kappa N *
             Real.exp (cand_H omega w + retained l w omega))
        else 1)
    (cand_ellLoN cand_ellHiN : ℕ → cand_Enl × cand_Shift → BilateralField d → ℝ)
    (cand_hEllLoN : ∀ (N : ℕ) (U : cand_Enl × cand_Shift) (omega : BilateralField d),
      cand_ellLoN N U omega =
        cand_I.lam (cand_rootCentre U) (cand_rootSide U) (cand_rootPos U)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient cand_M cand_H omega N
            (cand_rootCentre U) (cand_rootPos U))
          (cand_rootCentre U) (cand_rootSide U) cand_sigma 2 /
          cand_sN N (cand_rootLevel U) (cand_rootCentre U) omega)
    (cand_hEllHiN : ∀ (N : ℕ) (U : cand_Enl × cand_Shift) (omega : BilateralField d),
      cand_ellHiN N U omega =
        cand_I.Lam (cand_rootCentre U) (cand_rootSide U) (cand_rootPos U)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient cand_M cand_H omega N
            (cand_rootCentre U) (cand_rootPos U))
          (cand_rootCentre U) (cand_rootSide U) cand_sigma 2 /
          cand_sN N (cand_rootLevel U) (cand_rootCentre U) omega)
    (cand_AEN : ℕ → cand_Enl × cand_Shift → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
    (cand_hAEN : ∀ (N : ℕ) (U : cand_Enl × cand_Shift) (omega : BilateralField d),
      cand_AEN N U omega =
        (cand_sN N (cand_rootLevel U) (cand_rootCentre U) omega)⁻¹ •
          Homogenization.Book.Ch02.sigmaCoarse
            (Homogenization.Book.Ch02.cubeDomain
              (Homogenization.originCube d 0))
            ((cand_I.chart (cand_rootCentre U) (cand_rootSide U) (cand_rootPos U)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient cand_M cand_H omega N
                (cand_rootCentre U) (cand_rootPos U))
              (cand_rootCentre U) (cand_rootSide U)).coeffOn
              (Homogenization.originCube d 0)))
    (cand_errN cand_ratioN : ℕ → cand_Cmp → BilateralField d → ℝ)
    (cand_hErrN : ∀ (N : ℕ) (c : cand_Cmp) (omega : BilateralField d),
      cand_errN N c omega =
        cand_I.err (cand_cmpCentre c) (cand_cmpSide c) (cand_cmpPos c)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient cand_M cand_H omega N
            (cand_cmpCentre c) (cand_cmpPos c))
          (cand_cmpCentre c) (cand_cmpSide c)
          (cand_sN N (cand_cmpLevel c) (cand_cmpCentre c) omega) cand_s 2)
    (cand_hRatioN : ∀ (N : ℕ) (c : cand_Cmp) (omega : BilateralField d),
      cand_ratioN N c omega =
        cand_sN N (cand_k : ℤ) cand_qcenter omega /
          cand_sN N (cand_cmpLevel c) (cand_cmpCentre c) omega)
    (cand_phi : ℕ → ℕ)
    (cand_hphi : StrictMono cand_phi)
    (cand_prefixZLim : ∀ (_U : cand_Enl × cand_Shift) (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (cand_Enl × cand_Shift)) →
        BilateralField d → ℝ)
    (cand_prefixDLim : ∀ (_U : cand_Enl × cand_Shift) (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (cand_Enl × cand_Shift)) →
        BilateralField d → ℝ)
    (cand_ellLoLim cand_ellHiLim : (cand_Enl × cand_Shift) → BilateralField d → ℝ)
    (cand_AE_Lim : (cand_Enl × cand_Shift) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
    (cand_errLim cand_ratioLim : cand_Cmp → BilateralField d → ℝ)
    (cand_hPrefixZLim : ∀ (U : cand_Enl × cand_Shift) (D : ℕ)
      (code : (Fin D → OddGridIndex d 1) ⊕ (cand_Enl × cand_Shift)),
      TendstoInMeasure (chaosSampleLaw cand_M).toMeasure
        (fun n omega => cand_prefixZ (cand_phi n) U D code omega) atTop
        (cand_prefixZLim U D code))
    (cand_hPrefixDLim : ∀ (U : cand_Enl × cand_Shift) (D : ℕ)
      (code : (Fin D → OddGridIndex d 1) ⊕ (cand_Enl × cand_Shift)),
      TendstoInMeasure (chaosSampleLaw cand_M).toMeasure
        (fun n omega => cand_prefixD (cand_phi n) U D code omega) atTop
        (cand_prefixDLim U D code))
    (cand_hEllLoLim : ∀ (U : cand_Enl × cand_Shift),
      TendstoInMeasure (chaosSampleLaw cand_M).toMeasure
        (fun n omega => cand_ellLoN (cand_phi n) U omega) atTop (cand_ellLoLim U))
    (cand_hEllHiLim : ∀ (U : cand_Enl × cand_Shift),
      TendstoInMeasure (chaosSampleLaw cand_M).toMeasure
        (fun n omega => cand_ellHiN (cand_phi n) U omega) atTop (cand_ellHiLim U))
    (cand_hAELim : ∀ (U : cand_Enl × cand_Shift) (i j : Fin d),
      TendstoInMeasure (chaosSampleLaw cand_M).toMeasure
        (fun n omega => cand_AEN (cand_phi n) U omega i j) atTop
        (fun omega => cand_AE_Lim U omega i j))
    (cand_hErrLim : ∀ (c : cand_Cmp),
      TendstoInMeasure (chaosSampleLaw cand_M).toMeasure
        (fun n omega => cand_errN (cand_phi n) c omega) atTop (cand_errLim c))
    (cand_hRatioLim : ∀ (c : cand_Cmp),
      TendstoInMeasure (chaosSampleLaw cand_M).toMeasure
        (fun n omega => cand_ratioN (cand_phi n) c omega) atTop (cand_ratioLim c)),
            let GE := candidate_good_event d cand_hd
              cand_I cand_M cand_H cand_hMH cand_k cand_z cand_qside
              cand_hqside cand_qcenter cand_hqcenter cand_Enl cand_Shift cand_Cmp cand_selfE
              cand_selfShift cand_qRoot cand_hqRoot cand_factor cand_hfactor cand_padE cand_hpad
              cand_shift cand_hshift cand_rootLevel cand_hrootLevel cand_rootSide cand_hrootSide cand_rootCentre
              cand_hrootCentre cand_rootPos cand_hGridCover cand_parent cand_depth cand_word cand_cmpCentre
              cand_hcmpCentre cand_cmpLevel cand_hcmpLevel cand_cmpSide cand_hcmpSide cand_cmpPos cand_chosen
              cand_observationCentre cand_hObservationCentre cand_eta cand_hEta cand_F cand_Praw cand_Rraw
              cand_Draw cand_Z cand_rawGood cand_s cand_eps cand_hs cand_heps
              cand_hPrimitive cand_cbuf cand_k0 cand_lambdaCut cand_lambdaLim cand_lambdaDet cand_sigma
              cand_cell cand_epshom cand_cdet cand_hThresholds cand_hsigma cand_hcell cand_hepshom
              cand_hcdet cand_prefixZ cand_prefixD cand_hPrefixZ cand_hPrefixD cand_hFiniteScoreGuard cand_sN
              cand_hsN cand_ellLoN cand_ellHiN cand_hEllLoN cand_hEllHiN cand_AEN cand_hAEN
              cand_errN cand_ratioN cand_hErrN cand_hRatioN cand_phi cand_hphi cand_prefixZLim
              cand_prefixDLim cand_ellLoLim cand_ellHiLim cand_AE_Lim cand_errLim cand_ratioLim cand_hPrefixZLim
              cand_hPrefixDLim cand_hEllLoLim cand_hEllHiLim cand_hAELim cand_hErrLim cand_hRatioLim
            (hModelLaw : P = (chaosSampleLaw cand_M).toMeasure) →
            (hG : G n ⊆ GE) →
            ∃ W : ℕ+ → Set (BilateralField d),
              (∀ h : ℕ+,
                MeasurableSet[
                  Bsig (n - (h : ℤ)) (n + 2 * (h : ℤ))] (W h)) ∧
              (∀ h : ℕ+,
                P (W h) ≤
                  ENNReal.ofReal (Real.exp (-(beta * (h : ℝ))))) ∧
              Sigma ∩ GEᶜ ⊆ ⋃ h : ℕ+, W h := by
  classical
  have hp0 : (0 : ℝ) < p := by linarith
  have hCb1 : (0 : ℝ) < (Cband : ℝ) + 1 := by positivity
  have h64 : (beta + 1) < 64 * (beta + v + 1) := by linarith
  have hbase1 : (beta + 1) * (Cband : ℝ) < 64 * ((Cband : ℝ) + 1) * (beta + v + 1) := by
    have h1 : (beta + 1) * (Cband : ℝ) ≤ (beta + 1) * ((Cband : ℝ) + 1) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith : (0 : ℝ) ≤ beta + 1)
      linarith
    have h2 : (beta + 1) * ((Cband : ℝ) + 1) < (64 * (beta + v + 1)) * ((Cband : ℝ) + 1) :=
      mul_lt_mul_of_pos_right h64 hCb1
    calc (beta + 1) * (Cband : ℝ) ≤ (beta + 1) * ((Cband : ℝ) + 1) := h1
      _ < (64 * (beta + v + 1)) * ((Cband : ℝ) + 1) := h2
      _ = 64 * ((Cband : ℝ) + 1) * (beta + v + 1) := by ring
  have hpRate' : 64 * ((Cband : ℝ) + 1) * (beta + v + 1) ≤ a * p * Real.log 3 := by
    have h := hpRate; rw [mul_comm p a] at h; exact h
  have hgap : beta * ((Cband : ℝ) + 1) + v + 1 < a * p * Real.log 3 := by
    have h1 : beta * ((Cband : ℝ) + 1) ≤ (beta + v + 1) * ((Cband : ℝ) + 1) := by
      apply mul_le_mul_of_nonneg_right _ hCb1.le
      linarith
    have h3 : v + 1 ≤ ((Cband : ℝ) + 1) * (beta + v + 1) := by
      have h4 : (1 : ℝ) ≤ (Cband : ℝ) + 1 := by linarith
      nlinarith [h4, hbeta, hv]
    have h2 : beta * ((Cband : ℝ) + 1) + v + 1 ≤ 64 * ((Cband : ℝ) + 1) * (beta + v + 1) := by
      nlinarith [h1, h3, hCb1]
    linarith [h2, hpRate']
  have hdecay2 : (beta + 2) * (Cband : ℝ) < a * p * Real.log 3 := by
    have h64' : (beta + 2) < 64 * (beta + v + 1) := by linarith
    have h1 : (beta + 2) * (Cband : ℝ) ≤ (beta + 2) * ((Cband : ℝ) + 1) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith : (0 : ℝ) ≤ beta + 2)
      linarith
    have h2 : (beta + 2) * ((Cband : ℝ) + 1) < (64 * (beta + v + 1)) * ((Cband : ℝ) + 1) :=
      mul_lt_mul_of_pos_right h64' hCb1
    have h3 : (beta + 2) * (Cband : ℝ) < 64 * ((Cband : ℝ) + 1) * (beta + v + 1) := by
      calc (beta + 2) * (Cband : ℝ) ≤ (beta + 2) * ((Cband : ℝ) + 1) := h1
        _ < (64 * (beta + v + 1)) * ((Cband : ℝ) + 1) := h2
        _ = 64 * ((Cband : ℝ) + 1) * (beta + v + 1) := by ring
    linarith [h3, hpRate']
  obtain ⟨q, r, hqeq, hq, hq1, hr, hr1, hrate⟩ :=
    aux_prefix_geometric_rate a (beta * ((Cband : ℝ) + 1) + v + 1) p ha hp0 hgap
  obtain ⟨K, hkK, eta0A, heta0A, hbudgets⟩ :=
    aux_lem_witness_budgets Cband hCband c0 k0 hk0 hc0 beta a lam v Cgeom hbeta ha hlam hv hCgeom
      p A Ctail Cp hp hCtail hCp hA hpRate q r hq hq1 hr hr1 hrate
  obtain ⟨eta0T, heta0T, htest⟩ :=
    lem_witness_test_dyadic_cover d hd P Bsig Cband k0 hCband hk0 J (beta + 2) a lam Cp
      (by linarith) ha hlam hCp p hp
      (fun l₁ r₁ l₂ r₂ hl hr => aux_lem_witness_bsig_mono Bsig hBsig l₁ r₁ l₂ r₂ hl hr) hdecay2
  refine ⟨min eta0A eta0T, lt_min heta0A heta0T, ?_⟩
  intro eta heta hetale
  have hetaA : eta ≤ eta0A := le_trans hetale (min_le_left _ _)
  have hetaT : eta ≤ eta0T := le_trans hetale (min_le_right _ _)
  have hbud := hbudgets eta heta hetaA
  have htest' := htest eta heta hetaT
  intro I instI start centre tag hcard hstart X Xb T Tb
    hXmem hTmem hXnorm hTnorm hXbmeas hTbmeas hXerr hTerr htailP
  obtain ⟨hXbae, hTbae, hband⟩ :=
    lem_witness_prefix_band_measurability d hd P Bsig hBsig Cband c0 J Xb Tb hXbmeas hTbmeas
  obtain ⟨Sig0, hSigmeas, hSigP, hSiglim⟩ :=
    aux_lem_witness_sigma_exists d hd P p a Cp hp ha hCp eta heta I start centre tag J X Xb T Tb
      hXmem hTmem hXbae hTbae hXerr hTerr
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
  have hbound : ∀ h, 0 ≤ bound h := fun h => by dsimp only [bound]; positivity
  have hA0 : (0 : ℝ) ≤ A := le_trans (by positivity) hA
  intro G
  refine ⟨Sig0, hSigmeas, hSigP, ?_⟩
  intro n cand_hd cand_I cand_M cand_H cand_hMH cand_k cand_z cand_qside cand_hqside cand_qcenter cand_hqcenter cand_Enl cand_Shift cand_Cmp cand_selfE cand_selfShift cand_qRoot cand_hqRoot cand_factor cand_hfactor cand_padE cand_hpad cand_shift cand_hshift cand_rootLevel cand_hrootLevel cand_rootSide cand_hrootSide cand_rootCentre cand_hrootCentre cand_rootPos cand_hGridCover cand_parent cand_depth cand_word cand_cmpCentre cand_hcmpCentre cand_cmpLevel cand_hcmpLevel cand_cmpSide cand_hcmpSide cand_cmpPos cand_chosen cand_observationCentre cand_hObservationCentre cand_eta cand_hEta cand_F cand_Praw cand_Rraw cand_Draw cand_Z cand_rawGood cand_s cand_eps cand_hs cand_heps cand_hPrimitive cand_cbuf cand_k0 cand_lambdaCut cand_lambdaLim cand_lambdaDet cand_sigma cand_cell cand_epshom cand_cdet cand_hThresholds cand_hsigma cand_hcell cand_hepshom cand_hcdet cand_prefixZ cand_prefixD cand_hPrefixZ cand_hPrefixD cand_hFiniteScoreGuard cand_sN cand_hsN cand_ellLoN cand_ellHiN cand_hEllLoN cand_hEllHiN cand_AEN cand_hAEN cand_errN cand_ratioN cand_hErrN cand_hRatioN cand_phi cand_hphi cand_prefixZLim cand_prefixDLim cand_ellLoLim cand_ellHiLim cand_AE_Lim cand_errLim cand_ratioLim cand_hPrefixZLim cand_hPrefixDLim cand_hEllLoLim cand_hEllHiLim cand_hAELim cand_hErrLim cand_hRatioLim _ _ hMl1 hGset _ hGeq
  let Tpre : (D : ℕ) → I D → BilateralField d → ℝ := fun D i om =>
    ∑ j ∈ Finset.range D, X (tag D i) (start n D i + (j : ℤ)) (centre D i) om
  let Upre : (D : ℕ) → I D → ℕ → BilateralField d → ℝ := fun D i H om =>
    ∑ j ∈ Finset.range D, Xb (tag D i) (start n D i + (j : ℤ)) H (centre D i) om
  have hgeom : ∀ H : ℕ, (3 : ℝ) ^ (-(a * (H : ℝ))) = q ^ H := by
    intro H
    calc (3 : ℝ) ^ (-(a * (H : ℝ))) = (3 : ℝ) ^ ((-a) * (H : ℝ)) := by congr 1; ring
      _ = ((3 : ℝ) ^ (-a)) ^ H := Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3) (-a) H
      _ = q ^ H := by rw [hqeq]
  have hSigAE : ∀ᵐ om ∂P, om ∈ Sig0 := by
    apply ae_iff.mpr
    change P Sig0ᶜ = 0
    rw [measure_compl hSigmeas (by simp), hSigP]
    simp
  have hXae : ∀ D (i : I D) (j : ℕ),
      AEStronglyMeasurable (X (tag D i) (start n D i + (j : ℤ)) (centre D i)) P := by
    intro D i j
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (fun H => hXbae (tag D i) (start n D i + (j : ℤ)) H (centre D i))
    filter_upwards [hSigAE] with om hom
    exact (hSiglim om hom).1 (tag D i) n D i (j : ℤ)
  have hTae : ∀ D i, AEStronglyMeasurable (Tpre D i) P := by
    intro D i
    exact aux_prefix_ae_sum P (fun j => X (tag D i) (start n D i + (j : ℤ)) (centre D i))
      (fun j => hXae D i j) D
  have hUae : ∀ D i H, AEStronglyMeasurable (Upre D i H) P := by
    intro D i H
    exact aux_prefix_ae_sum P (fun j => Xb (tag D i) (start n D i + (j : ℤ)) H (centre D i))
      (fun j => hXbae (tag D i) (start n D i + (j : ℤ)) H (centre D i)) D
  have herror : ∀ D H, k0 ≤ D → D ≤ H → ∀ i : I D,
      eLpNorm (fun om => Tpre D i om - Upre D i H om) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal ((D : ℝ) * (Cp * eta) * q ^ H) := by
    intro D H hD hDH i
    have hb := aux_prefix_norm_sum P (fun j => X (tag D i) (start n D i + (j : ℤ)) (centre D i))
      (fun j => Xb (tag D i) (start n D i + (j : ℤ)) H (centre D i)) D p (Cp * eta * q ^ H)
      (le_trans (by norm_num : (1 : ℝ) ≤ 2) hp) (by positivity)
      (fun j => hXae D i j)
      (fun j => hXbae (tag D i) (start n D i + (j : ℤ)) H (centre D i))
      (fun j => by simpa only [hgeom H] using hXerr (tag D i) (start n D i + (j : ℤ)) H (centre D i))
    simpa only [Tpre, Upre, mul_assoc] using hb
  have htail' : ∀ D, k0 ≤ D → ∀ i : I D,
      P {om | lam * (D : ℝ) / 4 < Tpre D i om} ≤
        ENNReal.ofReal (Ctail * Real.exp (-(A * (D : ℝ)))) := by
    intro D hD i
    exact htailP n D hD i
  have hbaseMarkov : ∀ D, k0 ≤ D → ∀ i : I D,
      P {om | lam * (D : ℝ) / 4 < Tpre D i om} ≤ ENNReal.ofReal ((4 * Cp * eta / lam) ^ p) := by
    intro D hD i
    have hDpos : (0 : ℝ) < (D : ℝ) := by
      have hD0 : 0 < D := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) (le_trans hk0 hD)
      exact_mod_cast hD0
    have hnorm : eLpNorm (Tpre D i) (ENNReal.ofReal p) P ≤ ENNReal.ofReal ((D : ℝ) * (Cp * eta)) := by
      have hb := aux_prefix_norm_sum P (fun j => X (tag D i) (start n D i + (j : ℤ)) (centre D i))
        (fun _ : ℕ => fun _ => (0 : ℝ)) D p (Cp * eta)
        (le_trans (by norm_num : (1 : ℝ) ≤ 2) hp) (mul_pos hCp heta).le
        (fun j => hXae D i j)
        (fun _ => aestronglyMeasurable_const)
        (fun j => by simpa using hXnorm (tag D i) (start n D i + (j : ℤ)) (centre D i))
      simpa only [Tpre, Finset.sum_const_zero, sub_zero] using hb
    have ht : (0 : ℝ) < lam * (D : ℝ) / 4 := by
      have := mul_pos hlam hDpos; linarith
    have hsub : {om | lam * (D : ℝ) / 4 < Tpre D i om} ⊆
        {om | lam * (D : ℝ) / 4 ≤ |Tpre D i om|} := by
      intro om hom
      have hom' : lam * (D : ℝ) / 4 < Tpre D i om := hom
      exact le_trans hom'.le (le_abs_self _)
    have hratioD : (D : ℝ) * (Cp * eta) / (lam * (D : ℝ) / 4) = 4 * Cp * eta / lam := by
      field_simp
    have hmarkov := aux_prefix_lp_tail P (Tpre D i) p (lam * (D : ℝ) / 4) ((D : ℝ) * (Cp * eta))
      hp0 ht (by positivity) (hTae D i) hnorm
    rw [hratioD] at hmarkov
    exact le_trans (measure_mono hsub) hmarkov
  have hwindow : ∀ D H j, k0 ≤ D → D ≤ j → j ≤ H → ∀ i : I D,
      StronglyMeasurable[Bsig (n - ((w H : ℕ) : ℤ)) (n + 2 * ((w H : ℕ) : ℤ))] (Upre D i j) := by
    intro D H j hD hDj hjH i
    have hRj : Cband * (j + 1) + c0 + D ≤ Cband * (H + 1) + c0 + H := by
      have hmul := Nat.mul_le_mul_left Cband (Nat.add_le_add_right hjH 1)
      omega
    have hwdef : ((w H : ℕ) : ℤ) = ((Cband * (H + 1) + c0 + H : ℕ) : ℤ) := rfl
    have hsm := hband n D j (start n D i) (tag D i) (centre D i) hDj (hstart n D i).1
      (hstart n D i).2
    have hmono : Bsig (n - ((Cband * (j + 1) + c0 + D : ℕ) : ℤ))
          (n + 2 * ((Cband * (j + 1) + c0 + D : ℕ) : ℤ)) ≤
        Bsig (n - ((w H : ℕ) : ℤ)) (n + 2 * ((w H : ℕ) : ℤ)) := by
      apply aux_lem_witness_bsig_mono Bsig hBsig
      · rw [hwdef]; omega
      · rw [hwdef]; omega
    simpa only [Upre] using hsm.mono hmono
  have hbudgetSmall : ∀ H, k0 ≤ H →
      Cgeom * (((4 * Cp * eta / lam) ^ p) * Real.exp (A * ((K : ℝ) - 1))) *
          Real.exp (-((A - v) * (H : ℝ))) +
        ((H : ℝ) + 1) * Cgeom * Real.exp (v * (H : ℝ)) *
          aux_prefix_error p (Cp * eta) q r (lam * (1 - r) / 4) H ≤ (1 / 3) * bound (w H) := by
    intro H hH
    have h := hbud.1 H hH
    have hbw : (2 / 3) * Real.exp (-(beta * (((Cband * (H + 1) + c0 + H : ℕ) : ℝ)))) ≤ bound (w H) := by
      dsimp only [bound]
      have hE : ((w H : ℕ) : ℝ) = ((Cband * (H + 1) + c0 + H : ℕ) : ℝ) := rfl
      rw [hE]
      apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos _))
      norm_num
    exact le_trans h (mul_le_mul_of_nonneg_left hbw (by norm_num))
  have hbudgetLarge : ∀ H, K ≤ H →
      Cgeom * Ctail * Real.exp (-((A - v) * (H : ℝ))) +
        ((H : ℝ) + 1) * Cgeom * Real.exp (v * (H : ℝ)) *
          aux_prefix_error p (Cp * eta) q r (lam * (1 - r) / 4) H ≤ (1 / 3) * bound (w H) := by
    intro H hH
    have h := hbud.2 H hH
    have hbw : (2 / 3) * Real.exp (-(beta * (((Cband * (H + 1) + c0 + H : ℕ) : ℝ)))) ≤ bound (w H) := by
      dsimp only [bound]
      have hE : ((w H : ℕ) : ℝ) = ((Cband * (H + 1) + c0 + H : ℕ) : ℝ) := rfl
      rw [hE]
      apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos _))
      norm_num
    exact le_trans h (mul_le_mul_of_nonneg_left hbw (by norm_num))
  have hlimitP : ∀ om, om ∈ Sig0 → ∀ D i,
      Tendsto (fun H => Upre D i H om) atTop (𝓝 (Tpre D i om)) := by
    intro om hom D i
    exact aux_prefix_limit_sum (fun j H => Xb (tag D i) (start n D i + (j : ℤ)) H (centre D i) om)
      (fun j => X (tag D i) (start n D i + (j : ℤ)) (centre D i) om)
      (fun j => (hSiglim om hom).1 (tag D i) n D i (j : ℤ)) D
  obtain ⟨Wp, hWpmeas, hWpprob, hWpcover⟩ :=
    aux_lem_witness_prefix_cover_two_range (Ω := BilateralField d) P
      (fun h => Bsig (n - ((h : ℕ) : ℤ)) (n + 2 * ((h : ℕ) : ℤ)))
      bound hbound w hw k0 K hk0 hkK I lam p (Cp * eta) ((4 * Cp * eta / lam) ^ p) q r
      (lam * (1 - r) / 4) Cgeom v A Ctail hlam hp0 (mul_pos hCp heta).le (by positivity) hA0
      hq hq1.le hr hr1 rfl (le_trans zero_le_one hCgeom) hv hCtail.le hcard Tpre Upre hTae hUae
      herror htail' hbaseMarkov hwindow hbudgetSmall hbudgetLarge Sig0 hlimitP
  obtain ⟨Wt, hWtmeas, hWtprob, hWtcover⟩ :=
    htest' T Tb hTmem hTnorm hTbmeas hTbae hTerr Sig0 hSigmeas hSigP
      (fun om hom => (hSiglim om hom).2) n
  refine ⟨fun h => Wp h ∪ Wt h, ?_, ?_, ?_⟩
  · intro h
    exact MeasurableSet.union (hWpmeas h) (hWtmeas h)
  · intro h
    have hb1 : (0 : ℝ) ≤ bound h := hbound h
    have hb2 : (0 : ℝ) ≤ (1 / 4) * Real.exp (-(beta * ((h : ℕ) : ℝ))) := by positivity
    have hWt' : P (Wt h) ≤ ENNReal.ofReal ((1 / 4) * Real.exp (-(beta * ((h : ℕ) : ℝ)))) := by
      refine le_trans (hWtprob h) (ENNReal.ofReal_le_ofReal ?_)
      have hE0 : Real.exp (-((beta + 2) * ((h : ℕ) : ℝ)))
          = Real.exp (-(beta * ((h : ℕ) : ℝ))) * Real.exp (-(2 * ((h : ℕ) : ℝ))) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hE0]
      have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by
        have h := Real.add_one_le_exp 1
        linarith
      have hexp2 : (4 : ℝ) ≤ Real.exp 2 := by
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        rw [h2]
        have hmul := mul_le_mul hexp1 hexp1 (by norm_num : (0 : ℝ) ≤ 2) (by linarith : (0 : ℝ) ≤ Real.exp 1)
        linarith
      have hexphalf : Real.exp (-(2 * ((h : ℕ) : ℝ))) ≤ 1 / 4 := by
        have h1 : (1 : ℝ) ≤ ((h : ℕ) : ℝ) := by
          have h1' : 1 ≤ (h : ℕ) := Nat.succ_le_of_lt h.pos
          exact_mod_cast h1'
        have hle : Real.exp (-(2 * ((h : ℕ) : ℝ))) ≤ Real.exp (-2) :=
          Real.exp_le_exp.mpr (by linarith)
        have hval : Real.exp (-2) = 1 / Real.exp 2 := by rw [Real.exp_neg, one_div]
        have hfin : 1 / Real.exp 2 ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hexp2
        rw [hval] at hle
        linarith
      calc Real.exp (-(beta * ((h : ℕ) : ℝ))) * Real.exp (-(2 * ((h : ℕ) : ℝ)))
          ≤ Real.exp (-(beta * ((h : ℕ) : ℝ))) * (1 / 4) :=
            mul_le_mul_of_nonneg_left hexphalf (Real.exp_pos _).le
        _ = (1 / 4) * Real.exp (-(beta * ((h : ℕ) : ℝ))) := by ring
    calc P (Wp h ∪ Wt h) ≤ P (Wp h) + P (Wt h) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (bound h) + ENNReal.ofReal ((1 / 4) * Real.exp (-(beta * ((h : ℕ) : ℝ)))) :=
            add_le_add (hWpprob h) hWt'
      _ = ENNReal.ofReal (bound h + (1 / 4) * Real.exp (-(beta * ((h : ℕ) : ℝ)))) :=
            (ENNReal.ofReal_add hb1 hb2).symm
      _ ≤ ENNReal.ofReal (Real.exp (-(beta * ((h : ℕ) : ℝ)))) := by
          apply ENNReal.ofReal_le_ofReal
          have hEq : (3 / 4) * Real.exp (-(beta * ((h : ℕ) : ℝ))) +
              (1 / 4) * Real.exp (-(beta * ((h : ℕ) : ℝ))) =
              Real.exp (-(beta * ((h : ℕ) : ℝ))) := by ring
          dsimp only [bound]
          rw [hEq]
  · intro om hom
    obtain ⟨homSig, homGE⟩ := hom
    have hGn : ¬ (om ∈ G n) := by
      intro hcon
      exact homGE (hGeq hcon)
    have hGn' : ¬ ((∀ D, k0 ≤ D → ∀ i : I D,
        (∑ j ∈ Finset.range D, X (tag D i) (start n D i + (j : ℤ)) (centre D i) om) < lam * (D : ℝ)) ∧
        (∀ i : Fin J, T n i om < lam)) := by
      simpa only [G, mem_ofPred_eq] using hGn
    rw [not_and_or] at hGn'
    rcases hGn' with hA | hB
    · push Not at hA
      obtain ⟨D, hD, i, hle⟩ := hA
      obtain ⟨h, hh⟩ := Set.mem_iUnion.mp (hWpcover ⟨homSig, D, hD, i, hle⟩)
      exact Set.mem_iUnion.mpr ⟨h, Or.inl hh⟩
    · push Not at hB
      obtain ⟨i, hle⟩ := hB
      obtain ⟨h, hh⟩ := Set.mem_iUnion.mp (hWtcover ⟨homSig, i, hle⟩)
      exact Set.mem_iUnion.mpr ⟨h, Or.inr hh⟩

end SubdiffusiveProcess.Paper

