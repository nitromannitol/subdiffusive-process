module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.VariationalLevelEnergy
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.VariationalLevelBound
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WeightedMassiveSolution
public import SubdiffusiveProcess.CoarseGrainingVocab.Section11.CubeH10Embedding
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.HarmonicScaledBoundedness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.EssentialHarmonicRepresentative
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.GlobalRepresentative
public import SubdiffusiveProcess.Assumptions.CoefficientRegularity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.VariationalGreenContinuity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLowerOccupationEllipticity
public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import SubdiffusiveProcess.Main.CutoffSpeedDensity

-- Proof component: SharpStampacchia
@[expose] public section

section
open MeasureTheory Homogenization Filter Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Holder on the support retains the full source-exponent gain. -/
lemma aux_car_moser_source_local_bound_support_holder
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f v : X → ℝ} {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hpq : 1 / q + 1 / p < 1)
    (hf : AEStronglyMeasurable f μ) (hv : AEStronglyMeasurable v μ)
    (S : Set X) (hS : ∀ x ∉ S, v x = 0) :
    (∫⁻ x, ENNReal.ofReal (|f x| * |v x|) ∂μ) ≤
      eLpNorm f (ENNReal.ofReal q) μ * eLpNorm v (ENNReal.ofReal p) μ *
        (μ S) ^ (1 - 1 / q - 1 / p) := by
  let t : ℝ := (1 / q + 1 / p)⁻¹
  have hs0 : 0 < 1 / q + 1 / p := add_pos (one_div_pos.mpr hq) (one_div_pos.mpr hp)
  have ht : 0 < t := inv_pos.mpr hs0
  have ht1 : 1 ≤ t := (one_le_inv₀ hs0).mpr hpq.le
  have htriple : Real.HolderTriple q p t :=
    ⟨by dsimp only [t]; simp only [one_div, inv_inv], hq, hp⟩
  let : ENNReal.HolderTriple (ENNReal.ofReal q) (ENNReal.ofReal p) (ENNReal.ofReal t) :=
    htriple.ennrealOfReal
  have hsupp : Function.support (fun x => ENNReal.ofReal (|f x| * |v x|)) ⊆ S := by
    intro x hx
    by_contra hxs
    exact hx (by simp only [hS x hxs, abs_zero, mul_zero, ENNReal.ofReal_zero])
  rw [← setLIntegral_eq_of_support_subset hsupp]
  have heq : (∫⁻ x in S, ENNReal.ofReal (|f x| * |v x|) ∂μ) =
      eLpNorm (fun x => f x * v x) 1 (μ.restrict S) := by
    have hfv : AEStronglyMeasurable (fun x => f x * v x) (μ.restrict S) := hf.restrict.mul hv.restrict
    rw [eLpNorm_one_eq_lintegral_enorm hfv]
    simp only [ ← ofReal_norm, Real.norm_eq_abs, abs_mul]
  rw [heq]
  have hcompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := μ.restrict S) (p := 1) (q := ENNReal.ofReal t)
    (by simpa only [ENNReal.ofReal_one] using! ENNReal.ofReal_le_ofReal ht1)
    (hf.restrict.mul hv.restrict)
  have hexp : 1 - 1 / t = 1 - 1 / q - 1 / p := by
    dsimp only [t]
    rw [one_div, inv_inv]
    ring
  simp only [ENNReal.toReal_one, ENNReal.toReal_ofReal ht.le,
    Measure.restrict_apply_univ, div_one, hexp] at hcompare
  have hholder := eLpNorm_smul_le_mul_eLpNorm
    (μ := μ.restrict S) (p := ENNReal.ofReal q) (q := ENNReal.ofReal p)
    (r := ENNReal.ofReal t) hf.restrict hv.restrict
  have hprod : eLpNorm (fun x => f x * v x) (ENNReal.ofReal t) (μ.restrict S) ≤
      eLpNorm f (ENNReal.ofReal q) μ * eLpNorm v (ENNReal.ofReal p) μ :=
    by simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using!
      hholder.trans (mul_le_mul' (eLpNorm_restrict_le f _ μ S) (eLpNorm_restrict_le v _ μ S))
  exact hcompare.trans (mul_le_mul_left hprod _)

/-- The energy level estimate gives the sharp, unsquared volume recursion. -/
lemma aux_car_moser_source_local_bound_level_recursion
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {u f : X → ℝ} {p q B k l : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hpq : 1 / q + 1 / p < 1) (hB : 0 ≤ B)
    (hu : MemLp u (ENNReal.ofReal p) μ) (hf : MemLp f (ENNReal.ofReal q) μ)
    (hk : 0 ≤ k) (hkl : k < l)
    (hLevel : (eLpNorm (fun x => max (u x - k) 0) (ENNReal.ofReal p) μ) ^ 2 ≤
      ENNReal.ofReal B * ∫⁻ x, ENNReal.ofReal (|f x| * max (u x - k) 0) ∂μ) :
    (l - k) * (μ {x | l < u x}).toReal ^ (1 / p) ≤
      B * (eLpNorm f (ENNReal.ofReal q) μ).toReal *
        (μ {x | k < u x}).toReal ^ (1 - 1 / q - 1 / p) := by
  let v : X → ℝ := fun x => max (u x - k) 0
  have hv : MemLp v (ENNReal.ofReal p) μ := memLp_positiveTruncation hu hk
  have hv0 (x : X) : 0 ≤ v x := le_max_right _ _
  have hsupport (x : X) (hx : x ∉ {x | k < u x}) : v x = 0 :=
    max_eq_right (sub_nonpos.mpr (not_lt.mp hx))
  let L := ∫⁻ x, ENNReal.ofReal (|f x| * v x) ∂μ
  let V := (eLpNorm v (ENNReal.ofReal p) μ).toReal
  let N := (eLpNorm f (ENNReal.ofReal q) μ).toReal
  let a := (μ {x | k < u x}).toReal
  have hholder : L ≤ eLpNorm f (ENNReal.ofReal q) μ * eLpNorm v (ENNReal.ofReal p) μ *
      (μ {x | k < u x}) ^ (1 - 1 / q - 1 / p) := by
    simpa only [L, abs_of_nonneg (hv0 _)] using!
      aux_car_moser_source_local_bound_support_holder hp hq hpq
        hf.aestronglyMeasurable hv.aestronglyMeasurable {x | k < u x} hsupport
  have hdelta : 0 ≤ 1 - 1 / q - 1 / p := by linarith
  have htop : eLpNorm f (ENNReal.ofReal q) μ * eLpNorm v (ENNReal.ofReal p) μ *
      (μ {x | k < u x}) ^ (1 - 1 / q - 1 / p) ≠ ∞ := by
    have hfn := hf.eLpNorm_lt_top
    have hvn := hv.eLpNorm_lt_top
    have hsn := measure_lt_top μ {x | k < u x}
    finiteness
  have hLN : L ≠ ∞ := ne_top_of_le_ne_top htop hholder
  have hrealLevel : V ^ 2 ≤ B * L.toReal := by
    simpa only [V, L, v, ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofReal hB] using!
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLN) hLevel
  have hrealHolder : L.toReal ≤ N * V * a ^ (1 - 1 / q - 1 / p) := by
    simpa only [N, V, a, ENNReal.toReal_mul, ENNReal.toReal_rpow] using!
      ENNReal.toReal_mono htop hholder
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hC0 : 0 ≤ B * N * a ^ (1 - 1 / q - 1 / p) :=
    mul_nonneg (mul_nonneg hB ENNReal.toReal_nonneg) (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  have hVN : V ≤ B * N * a ^ (1 - 1 / q - 1 / p) := by
    have hbound : V ^ 2 ≤ V * (B * N * a ^ (1 - 1 / q - 1 / p)) := by
      calc
        _ ≤ B * L.toReal := hrealLevel
        _ ≤ B * (N * V * a ^ (1 - 1 / q - 1 / p)) := mul_le_mul_of_nonneg_left hrealHolder hB
        _ = _ := by ring
    nlinarith
  have hlow := positiveTruncation_level_norm_lower μ hu.aestronglyMeasurable hp hkl
  have hlowReal : (l - k) * (μ {x | l < u x}).toReal ^ (1 / p) ≤ V := by
    simpa only [V, v, ENNReal.toReal_mul, ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hkl.le)] using!
        ENNReal.toReal_mono hv.eLpNorm_ne_top hlow
  exact hlowReal.trans hVN

/-- Sharp Stampacchia extinction. The forcing condition is
`1 / q + 2 / p < 1`, where `p` is the Sobolev exponent. -/
theorem aux_car_moser_source_local_bound_sharp_level_bound
    {X : Type*} [MeasurableSpace X] {p q : ℝ}
    (hp : 2 < p) (hq : 0 < q) (hcrit : 1 / q + 2 / p < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure X) [IsFiniteMeasure μ]
      (B : ℝ), 0 < B → 0 < (μ univ).toReal →
      ∀ (u f : X → ℝ), MemLp u (ENNReal.ofReal p) μ → MemLp f (ENNReal.ofReal q) μ →
      (∀ k : ℝ, 0 ≤ k →
        (eLpNorm (fun x => max (u x - k) 0) (ENNReal.ofReal p) μ) ^ 2 ≤
          ENNReal.ofReal B * ∫⁻ x, ENNReal.ofReal (|f x| * max (u x - k) 0) ∂μ) →
      ∀ᵐ x ∂μ, u x ≤ C * B * (μ univ).toReal ^ (1 - 1 / q - 2 / p) *
        (eLpNorm f (ENNReal.ofReal q) μ).toReal := by
  let delta : ℝ := 1 - 1 / q - 1 / p
  let alpha : ℝ := p * delta
  let beta : ℝ := alpha - 1
  let D : ℝ := 2 * alpha / beta
  let C : ℝ := ((4 : ℝ) ^ alpha) ^ (1 / (2 * beta))
  have hp0 : 0 < p := by linarith
  have hip : 0 < 1 / p := one_div_pos.mpr hp0
  have hcrit' : 1 / q + 2 * (1 / p) < 1 := by
    simpa only [div_eq_mul_inv, one_mul] using! hcrit
  have hdelta : 0 < delta := by dsimp only [delta]; linarith
  have halpha : 1 < alpha := by
    have hmul := (div_lt_iff₀ hp0).mp (show 1 / p < delta by dsimp only [delta]; linarith)
    dsimp only [alpha]
    nlinarith
  have halpha0 : 0 < alpha := lt_trans zero_lt_one halpha
  have hbeta : 0 < beta := by dsimp only [beta]; linarith
  have hD : 0 < D := div_pos (mul_pos (by norm_num) halpha0) hbeta
  have hcritical : D * beta = 2 * alpha := by
    dsimp only [D]
    exact div_mul_cancel₀ _ hbeta.ne'
  have hC : 0 < C := by dsimp only [C]; positivity
  have hpq : 1 / q + 1 / p < 1 := by linarith
  refine ⟨C, hC, ?_⟩
  intro μ _ B hB hM u f hu hf hLevel
  let N : ℝ := (eLpNorm f (ENNReal.ofReal q) μ).toReal
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  by_cases hNz : N = 0
  · have hfn : eLpNorm f (ENNReal.ofReal q) μ = 0 :=
      ((ENNReal.toReal_eq_zero_iff _).mp hNz).resolve_right hf.eLpNorm_ne_top
    have hfzero := (eLpNorm_eq_zero_iff
      (ne_of_gt (ENNReal.ofReal_pos.mpr hq))).mp hfn
    have hzero : (∫⁻ x, ENNReal.ofReal (|f x| * max (u x - 0) 0) ∂μ) = 0 := by
      calc
        _ = ∫⁻ _x, (0 : ℝ≥0∞) ∂μ := by
          apply lintegral_congr_ae
          filter_upwards [hfzero] with x hx
          simp only [Pi.zero_apply] at hx
          simp only [hx, abs_zero, zero_mul, ENNReal.ofReal_zero]
        _ = 0 := lintegral_zero
    have hnormsq := hLevel 0 le_rfl
    rw [hzero, mul_zero] at hnormsq
    have hnorm : eLpNorm (fun x => max (u x - 0) 0) (ENNReal.ofReal p) μ = 0 :=
      eq_zero_of_pow_eq_zero (le_antisymm hnormsq bot_le)
    have hueq := (eLpNorm_eq_zero_iff
      (ne_of_gt (ENNReal.ofReal_pos.mpr hp0))).mp hnorm
    filter_upwards [hueq] with x hx
    have hux : u x ≤ 0 := by
      have hle := le_max_left (u x) 0
      simpa only [sub_zero, Pi.zero_apply] using!
        hle.trans (by simpa only [sub_zero, Pi.zero_apply] using! hx.le)
    change u x ≤ C * B * (μ univ).toReal ^ (1 - 1 / q - 2 / p) * N
    simpa only [hNz, mul_zero] using! hux
  have hN : 0 < N := lt_of_le_of_ne hN0 (Ne.symm hNz)
  let L : ℝ := (μ univ).toReal ^ (beta / p)
  let E0 : ℝ := B * N
  let K : ℝ := C * L * E0
  let a : ℝ → ℝ := fun k => (μ {x | k < u x}).toReal ^ (2 * delta)
  have hL : 0 < L := Real.rpow_pos_of_pos hM _
  have hE0 : 0 < E0 := mul_pos hB hN
  have hK : 0 < K := mul_pos (mul_pos hC hL) hE0
  have hLd : 0 < L ^ D := Real.rpow_pos_of_pos hL _
  have hLpow : L ^ D = (μ univ).toReal ^ (2 * delta) := by
    rw [show L = (μ univ).toReal ^ (beta / p) from rfl, ← Real.rpow_mul hM.le]
    congr 1
    dsimp only [D, alpha]
    field_simp
  have hinit : a (deGiorgiLevel K 0) ≤ L ^ D := by
    rw [hLpow, deGiorgiLevel_zero]
    exact Real.rpow_le_rpow ENNReal.toReal_nonneg
      (ENNReal.toReal_mono (measure_ne_top μ univ) (measure_mono (subset_univ _)))
      (mul_nonneg (by norm_num) hdelta.le)
  have hrec : ∀ k l : ℝ, 0 ≤ k → k < l →
      (l - k) ^ 2 * (a l) ^ (1 / alpha) ≤ (B ^ 2 * N ^ 2) * a k := by
    intro k l hk hkl
    have hraw := aux_car_moser_source_local_bound_level_recursion μ hp0 hq hpq
      hB.le hu hf hk hkl (hLevel k hk)
    have hlow0 : 0 ≤ (l - k) * (μ {x | l < u x}).toReal ^ (1 / p) :=
      mul_nonneg (sub_nonneg.mpr hkl.le) (Real.rpow_nonneg ENNReal.toReal_nonneg _)
    have hsq := pow_le_pow_left₀ hlow0 hraw 2
    have hpow (x : ℝ) (hx : 0 ≤ x) (e : ℝ) : (x ^ e) ^ 2 = x ^ (2 * e) := by
      rw [← Real.rpow_natCast (x ^ e) 2, ← Real.rpow_mul hx]
      congr 1
      ring
    have hexp : 2 * delta * (1 / alpha) = 2 * (1 / p) := by
      dsimp only [alpha]
      field_simp
    simpa only [a, N, mul_pow, hpow _ ENNReal.toReal_nonneg,
      ← Real.rpow_mul ENNReal.toReal_nonneg, hexp, delta, mul_assoc] using! hsq
  have hadm := deGiorgi_admissible_real_exponent
    (d := D) (C_F := 1) (E₀ := E0) (L := L) (Cd := C)
    (α := alpha) (β := beta) halpha0 hbeta rfl hcritical
    (by norm_num) hE0 hL hC (by simp only [one_mul]; exact le_rfl)
  have hKcond : ((B ^ 2 * N ^ 2) / K ^ 2) ^ alpha * (4 : ℝ) ^ alpha * (L ^ D) ^ beta ≤
      ((4 : ℝ) ^ alpha) ^ (-(1 / beta)) := by
    simpa only [E0, K, one_pow, one_mul, mul_pow] using! hadm
  have hdecay := deGiorgi_levelVolume_tendsto_zero (a := a) (Ld := L ^ D)
    (Crec := B ^ 2 * N ^ 2) (K := K) (α := alpha) (β := beta)
    (γ := 1 / alpha) (B := (4 : ℝ) ^ alpha)
    (fun _ => Real.rpow_nonneg ENNReal.toReal_nonneg _) hLd (by positivity) hK
    halpha rfl (one_div_mul_cancel halpha0.ne') rfl hinit hrec hKcond
  have hnull : μ {x | K < u x} = 0 := by
    have hle : (μ {x | K < u x}).toReal ^ (2 * delta) ≤ 0 := by
      apply ge_of_tendsto hdecay
      apply Filter.Eventually.of_forall
      intro n
      apply Real.rpow_le_rpow ENNReal.toReal_nonneg
        (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono ?_))
        (mul_nonneg (by norm_num) hdelta.le)
      intro x hx
      exact (deGiorgiLevel_lt hK n).trans hx
    by_contra hn
    have hmpos : 0 < (μ {x | K < u x}).toReal :=
      ENNReal.toReal_pos hn (measure_ne_top μ _)
    exact (not_lt_of_ge hle) (Real.rpow_pos_of_pos hmpos _)
  have hae : ∀ᵐ x ∂μ, u x ≤ K := by simpa only [ae_iff, not_le] using! hnull
  have hpower : beta / p = 1 - 1 / q - 2 / p := by
    dsimp only [beta, alpha, delta]
    field_simp
    ring
  have hKvalue : K = C * B * (μ univ).toReal ^ (1 - 1 / q - 2 / p) * N := by
    dsimp only [K, E0, L]
    rw [hpower]
    ring
  simpa only [hKvalue, N] using! hae

end SubdiffusiveProcess.Paper
end
end

-- Proof component: SharpGreen
section
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The actual form inequalities give Sobolev integrability of every killed
function, independently of its forcing. -/
lemma aux_car_moser_source_local_bound_killed_memLp
    {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U)
    {c rho : Vec d → ℝ} (hc : CoefficientOn U c) (hr : CoefficientOn U rho)
    {p A F : ℝ} (hA : 0 ≤ A) (hF : 0 ≤ F)
    (hSob : SobolevAssumption c rho U p A F)
    (hPoi : PoincareAssumption c rho U A F) (v : H10Function U) :
    MemLp v.toH1Function.toFun (ENNReal.ofReal p) ((weightedMeasure rho).restrict U) := by
  have hv2 := memLp_weighted_of_volume_restrict hU hr v.toH1Function.memL2
  obtain ⟨lo, hi, hlo, hb⟩ := hc.2
  have hc0 : ∀ᵐ x ∂volume.restrict U, 0 ≤ c x := hb.mono fun _ hx => hlo.le.trans hx.1
  have hs := sobolev_energy_bound_of_sobolevAssumption_poincareAssumption
    hA hF hc0 hSob hPoi v
  have hfin := hs.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  change SubdiffusiveProcess.RawLp.eLpNorm v.toFun (ENNReal.ofReal p) ((weightedMeasure rho).restrict U) ^ 2 < ⊤ at hfin
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hv2.aestronglyMeasurable] at hfin
  change eLpNorm v.toH1Function.toFun (ENNReal.ofReal p) ((weightedMeasure rho).restrict U) < ⊤
  by_contra hn
  have ht : eLpNorm v.toH1Function.toFun (ENNReal.ofReal p) ((weightedMeasure rho).restrict U) = ∞ :=
    top_le_iff.mp (not_lt.mp hn)
  change (eLpNorm v.toH1Function.toFun (ENNReal.ofReal p) ((weightedMeasure rho).restrict U)) ^ 2 < ⊤ at hfin
  simp only [ht, ENNReal.top_pow (by norm_num : (2 : ℕ) ≠ 0), lt_self_iff_false] at hfin



theorem aux_car_moser_source_local_bound_sharp_green
    {d : ℕ} {p q : ℝ} (hp : 2 < p) (hq : 0 < q) (hcrit : 1 / q + 2 / p < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {U : Set (Vec d)},
      IsOpenBoundedConvexDomain U → U.Nonempty →
      ∀ {c rho : Vec d → ℝ}, CoefficientOn U c → CoefficientOn U rho →
      ∀ {A F : ℝ}, 0 < A → 0 < F →
      SobolevAssumption c rho U p A F → PoincareAssumption c rho U A F →
      ∀ {f : Vec d → ℝ}, MemLp f (ENNReal.ofReal q) ((weightedMeasure rho).restrict U) →
      ∀ (u : H10Function U), IsMassiveWeakSolutionOn c rho 0 U u.toH1Function f →
        eLpNorm u.toH1Function.toFun ⊤ ((weightedMeasure rho).restrict U) ≤
          ENNReal.ofReal (C * A * (A + 1) * F) * weightedMeasure rho U ^ (-1 / q) *
            eLpNorm f (ENNReal.ofReal q) ((weightedMeasure rho).restrict U) := by
  obtain ⟨C, hC, hbound⟩ := aux_car_moser_source_local_bound_sharp_level_bound
    (X := Vec d) hp hq hcrit
  refine ⟨C, hC, ?_⟩
  intro U hU hne c rho hc hr A F hA hF hSob hPoi f hf u hu
  let mu := (weightedMeasure rho).restrict U
  let : IsFiniteMeasure (volume.restrict U) := hU.isFiniteMeasure_restrict_volume
  obtain ⟨lo, hi, hlo, hrb⟩ := hr.2
  have hmeasure := weightedMeasure_restrict_le_smul_volume_restrict hU.isOpen.measurableSet hi
    (hrb.mono fun _ hx => hx.2)
  let : IsFiniteMeasure mu := ⟨by
    apply (Measure.le_iff.mp hmeasure univ MeasurableSet.univ).trans_lt
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top (volume.restrict U) univ)⟩
  have hmass : mu univ = weightedMeasure rho U := by simp only [mu, Measure.restrict_apply_univ]
  have hmu0 : 0 < mu univ := weightedMeasure_restrict_open_pos hU.isOpen hr univ isOpen_univ
    (by simpa only [univ_inter] using! hne)
  have hM : 0 < (weightedMeasure rho U).toReal := by
    rw [← hmass]
    exact ENNReal.toReal_pos hmu0.ne' (measure_ne_top mu univ)
  have hMtop : weightedMeasure rho U ≠ ⊤ := by rw [← hmass]; exact measure_ne_top mu univ
  let B : ℝ := A * (A + 1) * F * (weightedMeasure rho U).toReal ^ (-(1 - 2 / p))
  have hB : 0 < B := by dsimp only [B]; positivity
  have hup : MemLp u.toH1Function.toFun (ENNReal.ofReal p) mu :=
    aux_car_moser_source_local_bound_killed_memLp hU.isOpen.measurableSet hc hr hA.le hF.le hSob hPoi u
  have hupper := hbound mu B hB (by rwa [hmass]) u.toH1Function.toFun f hup hf
    (variational_green_positive_level_bound hU hc hr hA.le hF.le hSob hPoi u hu)
  have huneg : IsMassiveWeakSolutionOn c rho 0 U (-u).toH1Function (fun x => -f x) :=
    isMassiveWeakSolutionOn_neg hu
  have hunegp : MemLp (-u).toH1Function.toFun (ENNReal.ofReal p) mu :=
    aux_car_moser_source_local_bound_killed_memLp hU.isOpen.measurableSet hc hr hA.le hF.le hSob hPoi (-u)
  have hnegative := hbound mu B hB (by rwa [hmass]) (-u).toH1Function.toFun (fun x => -f x) hunegp hf.neg
    (variational_green_positive_level_bound hU hc hr hA.le hF.le hSob hPoi (-u) huneg)
  have hnegNorm : eLpNorm (fun x => -f x) (ENNReal.ofReal q) mu =
      eLpNorm f (ENNReal.ofReal q) mu := eLpNorm_neg f _ _
  have hpair : ∀ᵐ x ∂mu, |u.toH1Function.toFun x| ≤ C * B *
      (mu univ).toReal ^ (1 - 1 / q - 2 / p) * (eLpNorm f (ENNReal.ofReal q) mu).toReal := by
    filter_upwards [hupper, hnegative] with x hx hxneg
    rw [hnegNorm] at hxneg
    change (-1 : ℝ) * u.toH1Function.toFun x ≤ _ at hxneg
    rw [neg_one_mul] at hxneg
    exact abs_le.mpr ⟨by linarith, hx⟩
  have hconstant : C * B * (mu univ).toReal ^ (1 - 1 / q - 2 / p) =
      (C * A * (A + 1) * F) * (weightedMeasure rho U).toReal ^ (-1 / q) := by
    rw [hmass]
    dsimp only [B]
    calc
      _ = (C * A * (A + 1) * F) *
          ((weightedMeasure rho U).toReal ^ (-(1 - 2 / p)) *
            (weightedMeasure rho U).toReal ^ (1 - 1 / q - 2 / p)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hM]
        congr 2
        ring
  simp only [hconstant] at hpair
  have hnorm : eLpNorm u.toH1Function.toFun ⊤ mu ≤ ENNReal.ofReal
      ((C * A * (A + 1) * F) * (weightedMeasure rho U).toReal ^ (-1 / q) *
        (eLpNorm f (ENNReal.ofReal q) mu).toReal) := by
    rw [eLpNorm_exponent_top hup.aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_bound (hpair.mono fun _ hx => by simpa only [Real.norm_eq_abs] using! hx)
  have hcoef : 0 ≤ C * A * (A + 1) * F := by positivity
  rw [ENNReal.ofReal_mul (mul_nonneg hcoef (Real.rpow_nonneg hM.le _)),
    ENNReal.ofReal_toReal hf.eLpNorm_ne_top, ENNReal.ofReal_mul hcoef,
    ← ENNReal.ofReal_rpow_of_pos hM, ENNReal.ofReal_toReal hMtop] at hnorm
  exact hnorm

end SubdiffusiveProcess.Paper
end
end

-- Proof component: SourceProjection
section
open Homogenization MeasureTheory
open SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Harmonic replacement constructs the source correction from the given
weak solution. No additional `L²` assumption on the forcing is needed. -/
theorem aux_car_moser_source_local_bound_harmonic_decomposition
    {d : ℕ} [NeZero d] {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (hne : U.Nonempty) {a b f : Vec d → ℝ} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U (scalarCoeffField a))
    (u : H1Function U) (hu : IsMassiveWeakSolutionOn a b 0 U u f) :
    ∃ (v : H10Function U) (h : H1Function U),
      (∀ x, u.toFun x = v.toH1Function.toFun x + h.toFun x) ∧
      IsMassiveWeakSolutionOn a b 0 U v.toH1Function f ∧ IsWeaklyHarmonicOn a U h := by
  obtain ⟨h, ⟨w, hwf, hwg⟩, hh⟩ := lane2_exists_weaklyHarmonic_of_zeroTrace hU hne hEll u
  refine ⟨-w, h, ?_, ?_, hh⟩
  · intro x
    change u.toFun x = (-1 : ℝ) * w.toH1Function.toFun x + h.toFun x
    rw [hwf x]
    ring
  · intro phi
    have huInt := integrableOn_energy_term hEll u.grad_memVectorL2 phi.toH1Function.grad_memVectorL2
    have hwInt := integrableOn_energy_term hEll w.toH1Function.grad_memVectorL2
      phi.toH1Function.grad_memVectorL2
    have hsplit :
        (∫ x in U, vecDot (a x • h.grad x) (phi.toH1Function.grad x)) =
          (∫ x in U, vecDot (a x • u.grad x) (phi.toH1Function.grad x)) +
            ∫ x in U, vecDot (a x • w.toH1Function.grad x) (phi.toH1Function.grad x) := by
      have heq : (fun x => vecDot (a x • h.grad x) (phi.toH1Function.grad x)) =
          fun x => vecDot (a x • u.grad x) (phi.toH1Function.grad x) +
            vecDot (a x • w.toH1Function.grad x) (phi.toH1Function.grad x) := by
        funext x
        rw [hwg x, smul_add, vecDot_add_left]
      rw [heq, integral_add huInt hwInt]
    have hhphi := hh phi
    have huphi := hu phi
    simp only [zero_mul, zero_add] at huphi ⊢
    have hneg : (fun x => vecDot (a x • (-w).toH1Function.grad x) (phi.toH1Function.grad x)) =
        fun x => -vecDot (a x • w.toH1Function.grad x) (phi.toH1Function.grad x) := by
      funext x
      change vecDot (a x • ((-1 : ℝ) • w.toH1Function.grad x)) (phi.toH1Function.grad x) = _
      simp only [neg_one_smul, smul_neg, vecDot_neg_left]
    rw [hneg, integral_neg]
    rw [hsplit] at hhphi
    linarith

end SubdiffusiveProcess.Paper
end
end

-- Proof component: CubeSourceSobolev
section
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section11
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- A subcritical Sobolev pair exists for every forcing exponent above `d/2`,
including the range between one and two in dimensions two and three. -/
theorem aux_car_moser_source_local_bound_sobolev_exponents
    {d : ℕ} (hd : 2 ≤ d) {q : ℝ} (hq : (d : ℝ) / 2 < q) :
    ∃ s p : FiniteLpExponent,
      s.exponent ≤ 2 ∧ s.exponent.toReal < d ∧ 2 < p.exponent.toReal ∧
      (p.exponent.toReal)⁻¹ = (s.exponent.toReal)⁻¹ - (d : ℝ)⁻¹ ∧
      1 / q + 2 / p.exponent.toReal < 1 := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hq0 : 0 < q := by linarith
  have hiq : 0 < 1 / (2 * q) := by positivity
  have hid : 0 < 1 / (d : ℝ) := one_div_pos.mpr hd0
  have hqd : 1 / (2 * q) < 1 / (d : ℝ) :=
    one_div_lt_one_div_of_lt hd0 (by linarith)
  have hdhalf : 1 / (d : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hd2
  let a : ℝ := 1 + 1 / (d : ℝ) - 1 / (2 * q)
  let b : ℝ := 1 - 1 / (d : ℝ) - 1 / (2 * q)
  have ha1 : 1 < a := by dsimp only [a]; linarith
  have ha2 : a < 2 := by dsimp only [a]; linarith
  have ha0 : 0 < a := lt_trans zero_lt_one ha1
  have hb0 : 0 < b := by dsimp only [b]; linarith
  have hb1 : b < 1 := by dsimp only [b]; linarith
  have hs1 : 1 < 2 / a := (lt_div_iff₀ ha0).mpr (by linarith)
  have hs2 : 2 / a ≤ 2 := (div_le_iff₀ ha0).mpr (by linarith)
  have hsd : 2 / a < d := by
    apply (div_lt_iff₀ ha0).mpr
    have hsmall : 2 / (d : ℝ) < a := by
      have heq : 2 / (d : ℝ) = 2 * (1 / (d : ℝ)) := by ring
      rw [heq]
      dsimp only [a]
      linarith
    exact (div_lt_iff₀ hd0).mp hsmall |>.trans_eq (mul_comm a (d : ℝ))
  have hp2 : 2 < 2 / b := (lt_div_iff₀ hb0).mpr (by linarith)
  let s : FiniteLpExponent := ⟨ENNReal.ofReal (2 / a), by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr hs1,
    ENNReal.ofReal_lt_top⟩
  let p : FiniteLpExponent := ⟨ENNReal.ofReal (2 / b), by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr (by linarith),
    ENNReal.ofReal_lt_top⟩
  have hsreal : s.exponent.toReal = 2 / a := ENNReal.toReal_ofReal (by positivity)
  have hpreal : p.exponent.toReal = 2 / b := ENNReal.toReal_ofReal (by positivity)
  refine ⟨s, p, ?_, ?_, ?_, ?_, ?_⟩
  · show ENNReal.ofReal (2 / a) ≤ 2
    exact_mod_cast ENNReal.ofReal_le_ofReal hs2
  · rwa [hsreal]
  · rwa [hpreal]
  · rw [hpreal, hsreal, inv_div, inv_div]
    dsimp only [a, b]
    ring
  · have hreduce : 2 / (2 / b) = b := by field_simp
    rw [hpreal, hreduce]
    have heq : 1 / q = 2 * (1 / (2 * q)) := by ring
    rw [heq]
    dsimp only [b]
    linarith

/-- A pointwise lower ellipticity bound controls the unweighted energy. -/
lemma aux_car_moser_source_local_bound_energy_comparison
    {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U) {a : Vec d → ℝ}
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U (scalarCoeffField a))
    (hlo : ∀ x ∈ U, lam ≤ a x) (v : H1Function U) :
    energy (fun _ => 1) U v ≤ lam⁻¹ * energy a U v := by
  have hi0 := integrableOn_vecDot_of_memVectorL2 v.grad_memVectorL2 v.grad_memVectorL2
  have hiA := integrableOn_energy_term hEll v.grad_memVectorL2 v.grad_memVectorL2
  have hraw : lam * energy (fun _ => 1) U v ≤ energy a U v := by
    simp only [energy, one_mul, ← integral_const_mul]
    apply integral_mono_ae (hi0.const_mul lam)
      (by simpa only [Homogenization.vecDot_smul_left] using! hiA)
    filter_upwards [ae_restrict_mem hU] with x hx
    exact mul_le_mul_of_nonneg_right (hlo x hx) (vecNormSq_nonneg (v.grad x))
  have hh := mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hlam.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hlam.ne', one_mul] using! hh

/-- Uniform ellipticity on a fixed cube produces the full weighted Sobolev
energy inequality. Its constant is chosen before the killed function. -/
theorem aux_car_moser_source_local_bound_cube_sobolev
    {d : ℕ} [NeZero d] (s p : FiniteLpExponent)
    (hs : s.exponent ≤ 2) (hsd : s.exponent.toReal < d)
    (hsp : (p.exponent.toReal)⁻¹ = (s.exponent.toReal)⁻¹ - (d : ℝ)⁻¹)
    (z : Vec d) {L : ℝ} (hL : 0 < L)
    {a rho : Vec d → ℝ} {lam Lam : ℝ} (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam (axisCube z L) (scalarCoeffField a))
    (hlo : ∀ x ∈ axisCube z L, lam ≤ a x) (hr : CoefficientOn (axisCube z L) rho) :
    ∃ B : ℝ, 0 < B ∧ ∀ v : H10Function (axisCube z L),
      (eLpNorm v.toH1Function.toFun p.exponent ((weightedMeasure rho).restrict (axisCube z L))) ^ 2 ≤
        ENNReal.ofReal B * ENNReal.ofReal (energy a (axisCube z L) v.toH1Function) := by
  obtain ⟨C, hC, hemb⟩ := h10_cube_embedding_sq s hs hsd
  obtain ⟨rlo, rhi, hrlo, hrb⟩ := hr.2
  let R : ℝ := |rhi| + 1
  have hR : 0 < R := by dsimp only [R]; positivity
  have hrb' : ∀ᵐ x ∂volume.restrict (axisCube z L), rho x ≤ R :=
    hrb.mono fun _ hx => hx.2.trans ((le_abs_self _).trans (by dsimp only [R]; linarith))
  have hm := weightedMeasure_restrict_le_smul_volume_restrict (isOpen_axisCube z L).measurableSet R hrb'
  let M : ℝ := (volume (axisCube z L)).toReal
  let K : ℝ := C * M ^ (2 * (1 / s.exponent.toReal - 1 / 2))
  let T : ℝ := R ^ (1 / p.exponent.toReal)
  have hM : 0 < M := volume_axisCube_toReal_pos z hL
  have hK : 0 < K := mul_pos hC (Real.rpow_pos_of_pos hM _)
  have hT : 0 < T := Real.rpow_pos_of_pos hR _
  refine ⟨T ^ 2 * K * lam⁻¹, by positivity, ?_⟩
  intro v
  have hnorm : eLpNorm v.toH1Function.toFun p.exponent ((weightedMeasure rho).restrict (axisCube z L)) ≤
      ENNReal.ofReal T * eLpNorm v.toH1Function.toFun p.exponent (volume.restrict (axisCube z L)) := by
    have hh := eLpNorm_mono_measure v.toH1Function.toFun hm (p := p.exponent)
    rw [eLpNorm_smul_measure_of_ne_top p.lt_top.ne v.toH1Function.toFun
      (ENNReal.ofReal R) v.toH1Function.memL2.aestronglyMeasurable,
      smul_eq_mul, ENNReal.toReal_div, ENNReal.toReal_one,
      ENNReal.ofReal_rpow_of_pos hR] at hh
    exact hh
  have hsquare := pow_le_pow_left₀ bot_le hnorm 2
  rw [mul_pow, ← ENNReal.ofReal_pow hT.le] at hsquare
  have hv := hemb p hsp z L hL v
  have henergy := aux_car_moser_source_local_bound_energy_comparison
    (isOpen_axisCube z L).measurableSet hlam hEll hlo v.toH1Function
  calc
    _ ≤ ENNReal.ofReal (T ^ 2) *
        (eLpNorm v.toH1Function.toFun p.exponent (volume.restrict (axisCube z L))) ^ 2 := hsquare
    _ ≤ ENNReal.ofReal (T ^ 2) *
        (ENNReal.ofReal K * ENNReal.ofReal (energy (fun _ => 1) (axisCube z L) v.toH1Function)) :=
      mul_le_mul' le_rfl hv
    _ ≤ ENNReal.ofReal (T ^ 2) *
        (ENNReal.ofReal K * ENNReal.ofReal (lam⁻¹ * energy a (axisCube z L) v.toH1Function)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal henergy))
    _ = _ := by
      rw [ENNReal.ofReal_mul (inv_nonneg.mpr hlam.le),
        ENNReal.ofReal_mul (mul_nonneg (sq_nonneg T) hK.le),
        ENNReal.ofReal_mul (sq_nonneg T)]
      ring

end SubdiffusiveProcess.Paper
end
end

-- Proof component: ConstructedForms
section
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Normalize an already proved pure Sobolev energy bound into the library's
Sobolev and Poincare interfaces. The form estimates are conclusions. -/
theorem aux_car_moser_source_local_bound_forms_of_sobolev
    {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U) {a rho : Vec d → ℝ}
    (hr : CoefficientOn U rho) {p B : ℝ} (hp : 2 < p) (hB : 0 < B)
    (hM : 0 < (weightedMeasure rho U).toReal)
    (hSob : ∀ v : H10Function U,
      (eLpNorm v.toH1Function.toFun (ENNReal.ofReal p) ((weightedMeasure rho).restrict U)) ^ 2 ≤
        ENNReal.ofReal B * ENNReal.ofReal (energy a U v.toH1Function)) :
    ∃ A : ℝ, 0 < A ∧ SobolevAssumption a rho U p A 1 ∧ PoincareAssumption a rho U A 1 := by
  let M : ℝ := (weightedMeasure rho U).toReal
  let w : ℝ := M ^ (1 - 2 / p)
  let A : ℝ := 1 + B * w
  have hw : 0 < w := Real.rpow_pos_of_pos hM _
  have hA : 0 < A := by dsimp only [A]; positivity
  have hBA : B * w ≤ A := by dsimp only [A]; linarith
  have hcoef : B ≤ A * M ^ (-(1 - 2 / p)) := by
    rw [Real.rpow_neg hM.le, ← div_eq_mul_inv]
    exact (le_div_iff₀ hw).mpr hBA
  refine ⟨A, hA, ?_, ?_⟩
  · intro v
    change SubdiffusiveProcess.RawLp.eLpNorm v.toFun (ENNReal.ofReal p) ((weightedMeasure rho).restrict U) ^ 2 ≤ _
    rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded
      (memLp_weighted_of_volume_restrict hU hr v.toH1Function.memL2).aestronglyMeasurable]
    have hSobGuarded := hSob v
    refine hSobGuarded.trans ?_
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef)
      (le_add_left (by simp only [one_mul]; exact le_rfl))
  · intro v
    have hv2 := memLp_weighted_of_volume_restrict hU hr v.toH1Function.memL2
    have hp2 : (2 : ENNReal) ≤ ENNReal.ofReal p := by
      simpa only [ENNReal.ofReal_ofNat] using! ENNReal.ofReal_le_ofReal hp.le
    have hn := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp2 hv2.aestronglyMeasurable
    rw [Measure.restrict_apply_univ, ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ p)] at hn
    have hsq := pow_le_pow_left₀ bot_le hn 2
    rw [mul_pow] at hsq
    have hmtop : weightedMeasure rho U ≠ ⊤ := (ENNReal.toReal_pos_iff.mp hM).2.ne
    have hpow : (weightedMeasure rho U ^ (1 / 2 - 1 / p)) ^ 2 = ENNReal.ofReal w := by
      rw [← ENNReal.ofReal_toReal hmtop, ENNReal.ofReal_rpow_of_pos hM,
        ← ENNReal.ofReal_pow (Real.rpow_nonneg hM.le _)]
      congr 1
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hM.le]
      congr 1
      ring
    rw [hpow] at hsq
    simp only [lpSq, ENNReal.ofReal_ofNat]
    change SubdiffusiveProcess.RawLp.eLpNorm v.toFun 2 ((weightedMeasure rho).restrict U) ^ 2 ≤ _
    rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hv2.aestronglyMeasurable]
    have hSobGuarded := hSob v
    calc
      _ ≤ (eLpNorm v.toH1Function.toFun (ENNReal.ofReal p) ((weightedMeasure rho).restrict U)) ^ 2 *
          ENNReal.ofReal w := hsq
      _ ≤ (ENNReal.ofReal B * ENNReal.ofReal (energy a U v.toH1Function)) * ENNReal.ofReal w :=
        mul_le_mul' hSobGuarded le_rfl
      _ = ENNReal.ofReal (B * w) * ENNReal.ofReal (energy a U v.toH1Function) := by
        rw [ENNReal.ofReal_mul hB.le]
        ring
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal (energy a U v.toH1Function) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hBA) le_rfl
      _ = _ := by rw [mul_one, ENNReal.ofReal_mul hA.le]

end SubdiffusiveProcess.Paper
end
end

-- Proof component: HarmonicLocalBound
section
open Homogenization MeasureTheory Filter Set
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Apply the existing scaled Moser estimate to both signs. -/
theorem aux_car_moser_source_local_bound_harmonic_scaled_abs
    {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Vec d → ℝ) (z : Vec d) (R : ℝ), 0 < R →
      (∀ x ∈ centeredAxisCube z R, 1 / 4 ≤ a x ∧ a x ≤ 4) →
      AEStronglyMeasurable a (volume.restrict (centeredAxisCube z R)) →
      ∀ h : Vec d → ℝ, WeakHarmonic a (centeredAxisCube z R) h →
      ∀ x ∈ centeredAxisCube z (R / 4),
        ENNReal.ofReal |h x| ≤ ENNReal.ofReal C * volume (centeredAxisCube z R) ^ (-(1 / 2) : ℝ) *
          eLpNorm h 2 (volume.restrict (centeredAxisCube z R)) := by
  obtain ⟨C, hC, hbound⟩ := exists_harmonic_scaled_positive_bound hd
  refine ⟨C, hC, ?_⟩
  intro a z R hR hab ha h hh x hx
  have hnorm (g : Vec d → ℝ) :
      eLpNorm (fun y => max (g y) 0) 2 (volume.restrict (centeredAxisCube z R)) ≤
        eLpNorm g 2 (volume.restrict (centeredAxisCube z R)) := by
    by_cases hg : AEStronglyMeasurable g (volume.restrict (centeredAxisCube z R))
    · apply eLpNorm_mono (hg.sup aestronglyMeasurable_const)
      intro y
      change ‖max (g y) 0‖ ≤ ‖g y‖
      rw [Real.norm_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _) (abs_nonneg _)
    · simp [eLpNorm, hg]
  by_cases hpos : 0 ≤ h x
  · have hhx := (hbound a z R hR hab ha h hh x hx).trans (mul_le_mul' le_rfl (hnorm h))
    simpa only [max_eq_left hpos, abs_of_nonneg hpos] using! hhx
  · have hhx := (hbound a z R hR hab ha (fun y => -h y) (moser_weakHarmonic_neg hh) x hx).trans
      (mul_le_mul' le_rfl (hnorm (fun y => -h y)))
    have hnegNorm : eLpNorm (fun y => -h y) 2 (volume.restrict (centeredAxisCube z R)) =
        eLpNorm h 2 (volume.restrict (centeredAxisCube z R)) := eLpNorm_neg h _ _
    rw [hnegNorm] at hhx
    simpa only [max_eq_left (neg_nonneg.mpr (le_of_not_ge hpos)),
      abs_of_nonpos (le_of_not_ge hpos)] using! hhx

/-- Continuity and positivity select local coefficient bands independently
of the weak solution. -/
lemma aux_car_moser_source_local_bound_local_band
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U) {a : Vec d → ℝ}
    (ha : ContinuousOn a U) (hapos : ∀ x ∈ U, 0 < a x)
    {x : Vec d} (hx : x ∈ U) :
    ∃ R : ℝ, 0 < R ∧ centeredAxisCube x R ⊆ U ∧
      ∀ y ∈ centeredAxisCube x R, 1 / 4 ≤ (a x)⁻¹ * a y ∧ (a x)⁻¹ * a y ≤ 4 := by
  have hax := hapos x hx
  have ht : ContinuousAt (fun y => (a x)⁻¹ * a y) x :=
    continuousAt_const.mul (ha.continuousAt (hU.mem_nhds hx))
  obtain ⟨r, hr, hclose⟩ := (Metric.continuousAt_iff.mp ht) (1 / 2) (by norm_num)
  obtain ⟨s, hs, hball⟩ := Metric.isOpen_iff.mp hU x hx
  let R : ℝ := min r s
  have hR : 0 < R := lt_min hr hs
  have hdist {y : Vec d} (hy : y ∈ centeredAxisCube x R) : dist y x < R := by
    rw [dist_pi_lt_iff hR]
    intro i
    rw [Real.dist_eq]
    exact (mem_centeredAxisCube.mp hy i).trans (half_lt_self hR)
  refine ⟨R, hR, ?_, ?_⟩
  · intro y hy
    exact hball ((hdist hy).trans_le (min_le_right r s))
  · intro y hy
    have h := hclose ((hdist hy).trans_le (min_le_left r s))
    rw [inv_mul_cancel₀ hax.ne', Real.dist_eq, abs_lt] at h
    constructor <;> linarith [h.1, h.2]

/-- A finite cover turns the local Moser bound into an estimate on every
compact subset. The constant is chosen before the harmonic function. -/
theorem aux_car_moser_source_local_bound_harmonic_compact
    {d : ℕ} (hd : 2 ≤ d) {U K : Set (Vec d)} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) {a : Vec d → ℝ}
    (ha : ContinuousOn a U) (hapos : ∀ x ∈ U, 0 < a x) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : Vec d → ℝ, WeakHarmonic a U h →
      ∀ x ∈ K, ENNReal.ofReal |h x| ≤ ENNReal.ofReal C * eLpNorm h 2 (volume.restrict U) := by
  classical
  obtain ⟨C0, hC0, hbound⟩ := aux_car_moser_source_local_bound_harmonic_scaled_abs hd
  have hlocal (x : K) := aux_car_moser_source_local_bound_local_band hU ha hapos (hKU x.2)
  choose R hR hsub hband using hlocal
  obtain ⟨S, hcover⟩ := hK.elim_finite_subcover
    (fun x : K => centeredAxisCube x (R x / 4)) (fun _ => isOpen_axisCube _ _)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩,
      self_mem_centeredAxisCube (div_pos (hR ⟨x, hx⟩) (by norm_num))⟩)
  let price : K → ℝ := fun x => C0 * ((R x) ^ d) ^ (-(1 / 2) : ℝ)
  have hprice (x : K) : 0 < price x := mul_pos hC0 (Real.rpow_pos_of_pos (pow_pos (hR x) d) _)
  let C : ℝ := 1 + ∑ x ∈ S, price x
  have hC : 0 < C := by
    have hsum : 0 ≤ ∑ x ∈ S, price x := Finset.sum_nonneg fun x _ => (hprice x).le
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro h hh x hx
  obtain ⟨y, hyS, hxy⟩ := mem_iUnion₂.mp (hcover hx)
  have hnorm : eLpNorm h 2 (volume.restrict (centeredAxisCube y.1 (R y))) ≤
      eLpNorm h 2 (volume.restrict U) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono (hsub y) le_rfl)
  have hweak : WeakHarmonic (fun z => (a y)⁻¹ * a z) (centeredAxisCube y.1 (R y)) h :=
    harmonic_weakHarmonic_const_mul_coefficient (moser_weakHarmonic_mono hh (hsub y)) _
  have ham : AEStronglyMeasurable (fun z => (a y)⁻¹ * a z)
      (volume.restrict (centeredAxisCube y.1 (R y))) :=
    (continuousOn_const.mul (ha.mono (hsub y))).aestronglyMeasurable
      (isOpen_axisCube _ _).measurableSet
  have hb := hbound (fun z => (a y)⁻¹ * a z) y.1 (R y) (hR y) (hband y) ham h hweak x hxy
  have hfactor : ENNReal.ofReal C0 * volume (centeredAxisCube y.1 (R y)) ^ (-(1 / 2) : ℝ) =
      ENNReal.ofReal (price y) := by
    rw [volume_centeredAxisCube_eq y.1 (hR y).le,
      ENNReal.ofReal_rpow_of_pos (pow_pos (hR y) d), ← ENNReal.ofReal_mul hC0.le]
  rw [hfactor] at hb
  have hle : price y ≤ C := by
    have hsum := Finset.single_le_sum (fun z _ => (hprice z).le) hyS
    dsimp only [C]
    linarith
  exact hb.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hle) hnorm)

/-- No prior boundedness or pointwise regularity of the H1 representative is
needed for the local harmonic infinity estimate. -/
theorem aux_car_moser_source_local_bound_h1_harmonic_compact
    {d : ℕ} (hd : 2 ≤ d) {U K : Set (Vec d)} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) {a : Vec d → ℝ}
    (ha : ContinuousOn a U) (hapos : ∀ x ∈ U, 0 < a x) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : H1Function U, IsWeaklyHarmonicOn a U u →
      eLpNorm u.toFun ⊤ (volume.restrict K) ≤ ENNReal.ofReal C * eLpNorm u.toFun 2 (volume.restrict U) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hbound⟩ := aux_car_moser_source_local_bound_harmonic_compact hd hU hK hKU ha hapos
  refine ⟨C, hC, ?_⟩
  intro u hu
  obtain ⟨hgcont, hgae⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.continuousOn_and_ae_eq_euclideanBallAverageRepresentative
      hd hU ha hapos hu
  let g := SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.euclideanBallAverageRepresentative u.toFun
  have hg : WeakHarmonic a U g := essential_representative_weakHarmonic hU u hu hgcont hgae
  have hpoint := hbound g hg
  have hnorm : eLpNorm g 2 (volume.restrict U) = eLpNorm u.toFun 2 (volume.restrict U) := eLpNorm_congr_ae hgae
  have hgaek := ae_restrict_of_ae_restrict_of_subset hKU hgae
  have hae : ∀ᵐ x ∂volume.restrict K, ‖u.toFun x‖ₑ ≤ ENNReal.ofReal C * eLpNorm u.toFun 2 (volume.restrict U) := by
    filter_upwards [hgaek, ae_restrict_mem hK.measurableSet] with x hxeq hx
    rw [← hxeq, ← ofReal_norm, Real.norm_eq_abs]
    rw [← hnorm]
    exact hpoint x hx
  rw [eLpNorm_exponent_top
    (u.memL2.aestronglyMeasurable.mono_measure (Measure.restrict_mono hKU le_rfl))]
  exact eLpNormEssSup_le_of_ae_enorm_bound hae

end SubdiffusiveProcess.Paper
end
end

-- Proof component: WeightedHarmonic
section
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The density lower bound controls the unweighted L2 norm. -/
theorem aux_car_moser_source_local_bound_l2_density_comparison
    {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U) {rho : Vec d → ℝ}
    (hr : CoefficientOn U rho) :
    ∃ L : ℝ, 0 < L ∧ ∀ f : Vec d → ℝ,
      eLpNorm f 2 (volume.restrict U) ≤
        ENNReal.ofReal L * eLpNorm f 2 ((weightedMeasure rho).restrict U) := by
  obtain ⟨lo, hi, hlo, hb⟩ := hr.2
  let L : ℝ := lo ^ (-(1 / 2) : ℝ)
  have hL : 0 < L := Real.rpow_pos_of_pos hlo _
  refine ⟨L, hL, ?_⟩
  intro f
  have hm := smul_volume_restrict_le_weightedMeasure_restrict hU lo (hb.mono fun _ hx => hx.1)
  by_cases hf : AEStronglyMeasurable f (volume.restrict U)
  ·
    have hn := eLpNorm_mono_measure f hm (p := (2 : ℝ≥0∞))
    rw [eLpNorm_smul_measure_of_ne_top (by norm_num) f (ENNReal.ofReal lo) hf, smul_eq_mul,
      ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat,
      ENNReal.ofReal_rpow_of_pos hlo] at hn
    have hprod : ENNReal.ofReal L * ENNReal.ofReal (lo ^ (1 / 2 : ℝ)) = 1 := by
      rw [← ENNReal.ofReal_mul hL.le, ← Real.rpow_add hlo]
      norm_num
    have hh := mul_le_mul' (le_refl (ENNReal.ofReal L)) hn
    simpa only [← mul_assoc, hprod, one_mul] using! hh
  · have hfW : ¬ AEStronglyMeasurable f ((weightedMeasure rho).restrict U) := by
      intro h
      exact hf (h.mono_ac (volume_restrict_absolutelyContinuous_weightedMeasure_restrict hU hr))
    simp [MeasureTheory.eLpNorm, hf, hfW, (ENNReal.ofReal_pos.mpr hL).ne']

/-- The harmonic local estimate in the same weighted L2 measure as the
source equation. -/
theorem aux_car_moser_source_local_bound_weighted_harmonic
    {d : ℕ} (hd : 2 ≤ d) {U K : Set (Vec d)} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) {a rho : Vec d → ℝ}
    (ha : ContinuousOn a U) (hapos : ∀ x ∈ U, 0 < a x)
    (hr : CoefficientOn U rho) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : H1Function U, IsWeaklyHarmonicOn a U u →
      eLpNorm u.toFun ⊤ ((weightedMeasure rho).restrict K) ≤
        ENNReal.ofReal C * eLpNorm u.toFun 2 ((weightedMeasure rho).restrict U) := by
  obtain ⟨C, hC, hbound⟩ := aux_car_moser_source_local_bound_h1_harmonic_compact hd hU hK hKU ha hapos
  obtain ⟨L, hL, hcompare⟩ := aux_car_moser_source_local_bound_l2_density_comparison hU.measurableSet hr
  refine ⟨C * L, mul_pos hC hL, ?_⟩
  intro u hu
  have htop : eLpNorm u.toFun ⊤ ((weightedMeasure rho).restrict K) ≤
      eLpNorm u.toFun ⊤ (volume.restrict K) := by
    have hv := u.memL2.aestronglyMeasurable.mono_measure (Measure.restrict_mono hKU le_rfl)
    have hw := hv.mono_ac (weightedMeasure_restrict_absolutelyContinuous_volume_restrict (rho := rho) hK.measurableSet)
    rw [eLpNorm_exponent_top hw, eLpNorm_exponent_top hv]
    exact eLpNormEssSup_mono_measure u.toFun
      (weightedMeasure_restrict_absolutelyContinuous_volume_restrict hK.measurableSet)
  have hh := htop.trans ((hbound u hu).trans (mul_le_mul' le_rfl (hcompare u.toFun)))
  simpa only [ENNReal.ofReal_mul hC.le, mul_assoc] using! hh

end SubdiffusiveProcess.Paper
end
end

-- Proof component: LocalSourceAssembly
section
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The deterministic local source estimate for continuous positive scalar
coefficients. All form constants are derived inside the proof. -/
theorem aux_car_moser_source_local_bound_deterministic
    {d : ℕ} (hd : 2 ≤ d) (z : Vec d) {L : ℝ} (hL : 0 < L)
    (K : Set (Vec d)) (hK : IsCompact K) (hKU : K ⊆ axisCube z L)
    (a rho : Vec d → ℝ) (ha : Continuous a) (hrho : Continuous rho)
    (hapos : ∀ x, 0 < a x) (hrhopos : ∀ x, 0 < rho x)
    (q : ℝ) (hq : (d : ℝ) / 2 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : H1Function (axisCube z L)) (f : Vec d → ℝ),
      MemLp f (ENNReal.ofReal q) ((weightedMeasure rho).restrict (axisCube z L)) →
      IsMassiveWeakSolutionOn a rho 0 (axisCube z L) u f →
      eLpNorm u.toFun ⊤ ((weightedMeasure rho).restrict K) ≤
        ENNReal.ofReal C * (eLpNorm u.toFun 2 ((weightedMeasure rho).restrict (axisCube z L)) +
          eLpNorm f (ENNReal.ofReal q) ((weightedMeasure rho).restrict (axisCube z L))) := by
  let : NeZero d := ⟨by omega⟩
  let U : Set (Vec d) := axisCube z L
  have hU : IsOpenBoundedConvexDomain U := isOpenBoundedConvexDomain_axisCube z L
  have hne : U.Nonempty := by
    refine ⟨fun i => z i + L / 2, ?_⟩
    intro i _
    constructor <;> linarith
  have hc : CoefficientOn U a :=
    SubdiffusiveProcess.Assumptions.CoefficientRegularity.coefficientOn_of_continuous_pos ha hapos hU.isBoundedDomain.isBounded
  have hr : CoefficientOn U rho :=
    SubdiffusiveProcess.Assumptions.CoefficientRegularity.coefficientOn_of_continuous_pos hrho hrhopos hU.isBoundedDomain.isBounded
  obtain ⟨lam, Lam, hlam, hb⟩ := hc.2
  have hbounds : ∀ x ∈ U, lam ≤ a x ∧ a x ≤ Lam :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower.forall_mem_of_ae_of_continuousOn
      hU.isOpen ha.continuousOn hb
  have hEll : IsEllipticFieldOn lam Lam U (scalarCoeffField a) :=
    SubdiffusiveProcess.lane2_isEllipticFieldOn_scalar hU.isOpen.measurableSet ha.measurable hlam hbounds
  obtain ⟨s, p, hs, hsd, hp, hsp, hcrit⟩ :=
    aux_car_moser_source_local_bound_sobolev_exponents hd hq
  obtain ⟨B, hB, hSob⟩ := aux_car_moser_source_local_bound_cube_sobolev
    s p hs hsd hsp z hL hlam hEll (fun x hx => (hbounds x hx).1) hr
  let mu : Measure (Vec d) := (weightedMeasure rho).restrict U
  let : IsFiniteMeasure (volume.restrict U) := hU.isFiniteMeasure_restrict_volume
  let : IsFiniteMeasure mu := variational_weighted_isFiniteMeasure hU.isOpen.measurableSet hr
  have hM : 0 < (weightedMeasure rho U).toReal := by
    have hm := weightedMeasure_restrict_open_pos hU.isOpen hr univ isOpen_univ
      (by simpa only [univ_inter] using! hne)
    exact ENNReal.toReal_pos (by simpa only [Measure.restrict_apply_univ] using! hm.ne')
      (by simpa only [mu, Measure.restrict_apply_univ] using! measure_ne_top mu univ)
  have hpn : ENNReal.ofReal p.exponent.toReal = p.exponent := ENNReal.ofReal_toReal p.lt_top.ne
  obtain ⟨A, hA, hSobA, hPoiA⟩ := aux_car_moser_source_local_bound_forms_of_sobolev
    hU.isOpen.measurableSet hr hp hB hM (by simpa only [hpn] using! hSob)
  have hq0 : 0 < q := by
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨Cs, hCs, hgreen⟩ := aux_car_moser_source_local_bound_sharp_green hp hq0 hcrit
  let G : ℝ := (Cs * A * (A + 1) * 1) * (weightedMeasure rho U).toReal ^ (-1 / q)
  have hG : 0 < G := by dsimp only [G]; positivity
  have hGbound : ∀ (f : Vec d → ℝ), MemLp f (ENNReal.ofReal q) mu →
      ∀ v : H10Function U, IsMassiveWeakSolutionOn a rho 0 U v.toH1Function f →
        eLpNorm v.toH1Function.toFun ⊤ mu ≤ ENNReal.ofReal G * eLpNorm f (ENNReal.ofReal q) mu := by
    intro f hf v hv
    have hh := hgreen hU hne hc hr hA (by norm_num) hSobA hPoiA hf v hv
    have hmtop : weightedMeasure rho U ≠ ⊤ := (ENNReal.toReal_pos_iff.mp hM).2.ne
    have hfactor : ENNReal.ofReal G =
        ENNReal.ofReal (Cs * A * (A + 1) * 1) * weightedMeasure rho U ^ (-1 / q) := by
      dsimp only [G]
      rw [ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_rpow_of_pos hM,
        ENNReal.ofReal_toReal hmtop]
    rw [hfactor]
    exact hh
  obtain ⟨Ch, hCh, hharmonic⟩ := aux_car_moser_source_local_bound_weighted_harmonic
    hd hU.isOpen hK hKU ha.continuousOn (fun x _ => hapos x) hr
  let V : ℝ := (mu univ).toReal ^ (1 / 2 : ℝ)
  have hV : 0 ≤ V := Real.rpow_nonneg ENNReal.toReal_nonneg _
  let E : ℝ := G + Ch * G * V
  have hE : 0 ≤ E := add_nonneg hG.le (mul_nonneg (mul_nonneg hCh.le hG.le) hV)
  let C : ℝ := 1 + Ch + E
  have hC : 0 < C := by dsimp only [C]; linarith
  have hChC : Ch ≤ C := by dsimp only [C]; linarith
  have hEC : E ≤ C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro u f hf hu
  obtain ⟨v, h, hsplit, hv, hh⟩ := aux_car_moser_source_local_bound_harmonic_decomposition hU hne hEll u hu
  have hvm : MemLp v.toH1Function.toFun 2 mu :=
    memLp_weighted_of_volume_restrict hU.isOpen.measurableSet hr v.toH1Function.memL2
  have hhm : MemLp h.toFun 2 mu := memLp_weighted_of_volume_restrict hU.isOpen.measurableSet hr h.memL2
  have hum : MemLp u.toFun 2 mu := memLp_weighted_of_volume_restrict hU.isOpen.measurableSet hr u.memL2
  have hgreenTop := hGbound f hf v hv
  have hvL2 : eLpNorm v.toH1Function.toFun 2 mu ≤
      ENNReal.ofReal G * eLpNorm f (ENNReal.ofReal q) mu * ENNReal.ofReal V := by
    have hn := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := mu) (p := 2) (q := ⊤) le_top hvm.aestronglyMeasurable
    simp only [ENNReal.toReal_ofNat, ENNReal.toReal_top, div_zero, sub_zero] at hn
    have hpow : (mu univ) ^ (1 / 2 : ℝ) = ENNReal.ofReal V := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top mu univ),
        ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num)]
    exact hn.trans (mul_le_mul' hgreenTop (le_of_eq hpow))
  have hhfun : h.toFun = fun x => u.toFun x - v.toH1Function.toFun x := by
    funext x
    have hx := hsplit x
    linarith
  have hhL2 : eLpNorm h.toFun 2 mu ≤ eLpNorm u.toFun 2 mu + eLpNorm v.toH1Function.toFun 2 mu := by
    rw [hhfun]
    exact eLpNorm_sub_le (by norm_num)
  have hfun : u.toFun = fun x => v.toH1Function.toFun x + h.toFun x := funext hsplit
  have hmuK : (weightedMeasure rho).restrict K ≤ mu := Measure.restrict_mono hKU le_rfl
  have huTop : eLpNorm u.toFun ⊤ ((weightedMeasure rho).restrict K) ≤
      eLpNorm v.toH1Function.toFun ⊤ ((weightedMeasure rho).restrict K) +
        eLpNorm h.toFun ⊤ ((weightedMeasure rho).restrict K) := by
    rw [hfun]
    exact eLpNorm_add_le (by simp only [le_top])
  have hmain := huTop.trans (add_le_add
    ((eLpNorm_mono_measure _ hmuK).trans hgreenTop)
    ((hharmonic h hh).trans (mul_le_mul' le_rfl (hhL2.trans (add_le_add le_rfl hvL2)))))
  have heq :
      ENNReal.ofReal G * eLpNorm f (ENNReal.ofReal q) mu + ENNReal.ofReal Ch *
        (eLpNorm u.toFun 2 mu + ENNReal.ofReal G * eLpNorm f (ENNReal.ofReal q) mu * ENNReal.ofReal V) =
      ENNReal.ofReal Ch * eLpNorm u.toFun 2 mu + ENNReal.ofReal E * eLpNorm f (ENNReal.ofReal q) mu := by
    dsimp only [E]
    rw [ENNReal.ofReal_add hG.le (mul_nonneg (mul_nonneg hCh.le hG.le) hV),
      ENNReal.ofReal_mul (mul_nonneg hCh.le hG.le), ENNReal.ofReal_mul hCh.le]
    ring
  rw [heq] at hmain
  exact hmain.trans (by
    rw [mul_add]
    exact add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal hChC) le_rfl)
      (mul_le_mul' (ENNReal.ofReal_le_ofReal hEC) le_rfl))

end SubdiffusiveProcess.Paper
end
end

-- Proof component: CutoffLocalSource
section
open Homogenization MeasureTheory Set SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The centered cube is a translated coordinate cube of the same side. -/
lemma aux_car_moser_source_local_bound_centered_cube
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    (centeredCube z r hr : Set (SpatialCoordinates d)) =
      axisCube (fun i => z i - r / 2) r := by
  rw [centeredCube_eq_pi z hr]
  unfold axisCube
  congr 1
  funext i
  congr 1
  ring

/-- At each fixed cutoff the speed density is continuous and positive. -/
lemma aux_car_moser_source_local_bound_speed_density
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (ω : BilateralField d) (N : ℕ) :
    Continuous (cutoffSpeedDensity M H ω N) ∧ ∀ x, 0 < cutoffSpeedDensity M H ω N x := by
  constructor
  · apply Real.continuous_exp.comp
    exact Continuous.sub
      (Continuous.add (H ω).continuous
        (continuous_finsetSum _ fun j _ => (ω (-(Int.ofNat j))).continuous))
      continuous_const
  · intro x
    exact Real.exp_pos _

/-- Fixed-cutoff local infinity bound for a weak solution with an L^p source,
for the complete range p > d/2. The constant is chosen before both u and f;
no boundedness, sign, source L^2, or form-estimate hypothesis is imposed. -/
theorem car_moser_source_local_bound
    {d : ℕ} (hd : 2 ≤ d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (ω : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (K : Set (SpatialCoordinates d)) (hK : IsCompact K)
    (hKU : K ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (p : ℝ) (hp : (d : ℝ) / 2 < p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
        (f : SpatialCoordinates d → ℝ),
        MemLp f (ENNReal.ofReal p)
          ((weightedMeasure (cutoffSpeedDensity M H ω N)).restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))) →
        IsMassiveWeakSolutionOn (cutoffCoefficient M H ω N)
          (cutoffSpeedDensity M H ω N) 0
          (centeredCube z r hr : Set (SpatialCoordinates d)) u f →
        eLpNorm u.toFun ⊤ ((weightedMeasure (cutoffSpeedDensity M H ω N)).restrict K) ≤
          ENNReal.ofReal C *
            (eLpNorm u.toFun 2 ((weightedMeasure (cutoffSpeedDensity M H ω N)).restrict
              (centeredCube z r hr : Set (SpatialCoordinates d))) +
             eLpNorm f (ENNReal.ofReal p)
               ((weightedMeasure (cutoffSpeedDensity M H ω N)).restrict
                 (centeredCube z r hr : Set (SpatialCoordinates d)))) := by
  have hcube := aux_car_moser_source_local_bound_centered_cube z hr
  rw [hcube] at hKU ⊢
  obtain ⟨hbcont, hbpos⟩ := aux_car_moser_source_local_bound_speed_density M H ω N
  exact aux_car_moser_source_local_bound_deterministic hd (fun i => z i - r / 2) hr K hK hKU
    (cutoffCoefficient M H ω N) (cutoffSpeedDensity M H ω N)
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_continuous M H ω N) hbcont
    (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos M H ω N) hbpos p hp

end SubdiffusiveProcess.Paper
end
end

-- Proof component: ResolventSourceBridge
section
open Homogenization MeasureTheory Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Retain the resolvent mass exactly by moving it to the source. -/
theorem aux_car_moser_source_local_bound_mass_to_source
    {d : ℕ} {U : Set (Vec d)} {a rho f : Vec d → ℝ} {m : ℝ}
    (hr : CoefficientOn U rho) (hf : MemL2On U f) {u : H1Function U}
    (hu : IsMassiveWeakSolutionOn a rho m U u f) :
    IsMassiveWeakSolutionOn a rho 0 U u (fun x => f x - m * u.toFun x) := by
  obtain ⟨lo, hi, hlo, hb⟩ := hr.2
  have hrb : ∀ᵐ x ∂volume.restrict U, |rho x| ≤ hi := hb.mono fun x hx => by
    rw [abs_of_pos (hlo.trans_le hx.1)]
    exact hx.2
  intro v
  have hfu := integrableOn_mass_term hr.1 hrb hf v.toH1Function.memL2
  have huu := integrableOn_mass_term hr.1 hrb u.memL2 v.toH1Function.memL2
  have heq : (fun x => rho x * (f x - m * u.toFun x) * v.toH1Function.toFun x) =
      fun x => rho x * f x * v.toH1Function.toFun x -
        m * (rho x * u.toFun x * v.toH1Function.toFun x) := by
    funext x
    ring
  rw [heq, integral_sub hfu (huu.const_mul m), integral_const_mul]
  have huv := hu v
  linarith

/-- A uniform essential bound and a small L^2 norm give a small finite L^q
norm. This is the interpolation needed for the effective resolvent source. -/
theorem aux_car_moser_source_local_bound_bounded_interpolation
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (u : X → ℝ)
    {q : ℝ} (hq : 2 ≤ q) {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hb : ∀ᵐ x ∂μ, ‖u x‖ₑ ≤ B) :
    SubdiffusiveProcess.RawLp.eLpNorm u (ENNReal.ofReal q) μ ≤
      B ^ (1 - 2 / q) * (SubdiffusiveProcess.RawLp.eLpNorm u 2 μ) ^ (2 / q) := by
  have hq0 : 0 < q := by linarith
  have hexp : 0 ≤ q - 2 := sub_nonneg.mpr hq
  have hpoint : ∀ᵐ x ∂μ, ‖u x‖ₑ ^ q ≤ B ^ (q - 2) * ‖u x‖ₑ ^ (2 : ℝ) := by
    filter_upwards [hb] with x hx
    calc
      _ = ‖u x‖ₑ ^ ((q - 2) + 2) := by congr 1; ring
      _ = ‖u x‖ₑ ^ (q - 2) * ‖u x‖ₑ ^ (2 : ℝ) :=
        ENNReal.rpow_add_of_nonneg _ _ hexp (by norm_num)
      _ ≤ _ := mul_le_mul' (ENNReal.rpow_le_rpow hx hexp) le_rfl
  have hint : (∫⁻ x, ‖u x‖ₑ ^ q ∂μ) ≤
      B ^ (q - 2) * ∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) ∂μ := by
    calc
      _ ≤ ∫⁻ x, B ^ (q - 2) * ‖u x‖ₑ ^ (2 : ℝ) ∂μ := lintegral_mono_ae hpoint
      _ = _ := lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hexp hB)
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral (ENNReal.ofReal_pos.mpr hq0).ne' ENNReal.ofReal_ne_top u μ,
    ENNReal.toReal_ofReal hq0.le]
  have he1 : (q - 2) * (1 / q) = 1 - 2 / q := by field_simp
  have he2 : (1 / 2 : ℝ) * (2 / q) = 1 / q := by ring
  calc
    _ ≤ (B ^ (q - 2) * ∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / q) :=
      ENNReal.rpow_le_rpow hint (one_div_nonneg.mpr hq0.le)
    _ = B ^ (1 - 2 / q) * (SubdiffusiveProcess.RawLp.eLpNorm u 2 μ) ^ (2 / q) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hq0.le),
        ← ENNReal.rpow_mul, he1,
        SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) u μ,
        ENNReal.toReal_ofNat, ← ENNReal.rpow_mul, he2]

end SubdiffusiveProcess.Paper
end
end

-- Proof component: C0SourceConsumer
section
open Homogenization MeasureTheory Set SubdiffusiveProcess MarkovProcess.Semigroup
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open scoped ENNReal ZeroAtInfty

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- A C0 function lies in every local Lp space of finite measure. -/
lemma aux_car_moser_source_local_bound_c0_memLp
    {d : ℕ} (μ : Measure (SpatialCoordinates d)) [IsFiniteMeasure μ]
    (f : C₀(SpatialCoordinates d, ℝ)) (p : ℝ≥0∞) : MemLp f p μ := by
  apply MemLp.of_bound f.continuous.aestronglyMeasurable ‖f.toBCF‖
  exact Filter.Eventually.of_forall fun x => f.toBCF.norm_coe_le_norm x



theorem aux_car_moser_source_local_bound_c0_resolvent
    {d : ℕ} (hd : 2 ≤ d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (ω : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (K : Set (SpatialCoordinates d)) (hK : IsCompact K)
    (hKU : K ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (p : ℝ) (hp : (d : ℝ) / 2 < p)
    (D : C0ResolventDatum (SpatialCoordinates d))
    (hD : IsWeakEllipticResolvent (cutoffCoefficient M H ω N) (cutoffSpeedDensity M H ω N) D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : PositiveShift) (f : C₀(SpatialCoordinates d, ℝ)),
      eLpNorm (D.solution m f) ⊤ ((weightedMeasure (cutoffSpeedDensity M H ω N)).restrict K) ≤
        ENNReal.ofReal C *
          (eLpNorm (D.solution m f) 2 ((weightedMeasure (cutoffSpeedDensity M H ω N)).restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))) +
           eLpNorm f (ENNReal.ofReal p) ((weightedMeasure (cutoffSpeedDensity M H ω N)).restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))) +
           ENNReal.ofReal (m : ℝ) * eLpNorm (D.solution m f) (ENNReal.ofReal p)
            ((weightedMeasure (cutoffSpeedDensity M H ω N)).restrict
              (centeredCube z r hr : Set (SpatialCoordinates d)))) := by
  let U : Set (SpatialCoordinates d) := centeredCube z r hr
  let b := cutoffSpeedDensity M H ω N
  let μ := (weightedMeasure b).restrict U
  have hU : IsOpenBoundedConvexDomain U := by
    dsimp only [U]
    rw [aux_car_moser_source_local_bound_centered_cube z hr]
    exact isOpenBoundedConvexDomain_axisCube _ _
  have hb := aux_car_moser_source_local_bound_speed_density M H ω N
  have hbc : CoefficientOn U b :=
    SubdiffusiveProcess.Assumptions.CoefficientRegularity.coefficientOn_of_continuous_pos hb.1 hb.2
      (centeredCube_isBounded z hr)
  let : IsFiniteMeasure (volume.restrict U) := hU.isFiniteMeasure_restrict_volume
  let : IsFiniteMeasure μ := variational_weighted_isFiniteMeasure hU.isOpen.measurableSet hbc
  obtain ⟨C, hC, hbound⟩ := car_moser_source_local_bound hd M H ω N z hr K hK hKU p hp
  refine ⟨C, hC, ?_⟩
  intro m f
  obtain ⟨u, hueq, hu⟩ := hD m f U hU
  have huae : u.toFun =ᵐ[μ] D.solution m f := by
    filter_upwards [ae_restrict_mem hU.isOpen.measurableSet] with x hx
    exact hueq x hx
  have huk : u.toFun =ᵐ[(weightedMeasure b).restrict K] D.solution m f :=
    ae_restrict_of_ae_restrict_of_subset hKU huae
  have hf2 := aux_car_moser_source_local_bound_c0_memLp (volume.restrict U) f 2
  have hfp := aux_car_moser_source_local_bound_c0_memLp μ f (ENNReal.ofReal p)
  have hup : MemLp u.toFun (ENNReal.ofReal p) μ :=
    (memLp_congr_ae huae).mpr
      (aux_car_moser_source_local_bound_c0_memLp μ (D.solution m f) (ENNReal.ofReal p))
  have hsource := aux_car_moser_source_local_bound_mass_to_source hbc hf2 hu
  have hh := hbound u (fun x => f x - (m : ℝ) * u.toFun x) (hfp.sub (hup.const_mul (m : ℝ))) hsource
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hp1 : 1 ≤ p := by linarith
    simpa only [ENNReal.ofReal_one] using! ENNReal.ofReal_le_ofReal hp1
  have hs := eLpNorm_sub_le (μ := μ) (f := (⇑f)) (g := fun x => (m : ℝ) * u.toFun x) hp1
  have hsmul : eLpNorm (fun x => (m : ℝ) * u.toFun x) (ENNReal.ofReal p) μ =
      ENNReal.ofReal (m : ℝ) * eLpNorm u.toFun (ENNReal.ofReal p) μ := by
    simpa only [smul_eq_mul, ← ofReal_norm, Real.norm_of_nonneg m.property.le]
      using! eLpNorm_const_smul (m : ℝ) u.toFun (ENNReal.ofReal p) μ
  rw [hsmul] at hs
  have hout := hh.trans (mul_le_mul' le_rfl (add_le_add le_rfl hs))
  rw [eLpNorm_congr_ae huk, eLpNorm_congr_ae huae, eLpNorm_congr_ae huae] at hout
  simpa only [add_assoc] using! hout

end SubdiffusiveProcess.Paper
end
end
























