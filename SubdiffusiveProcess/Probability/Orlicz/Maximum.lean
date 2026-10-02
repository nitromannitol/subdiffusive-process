import SubdiffusiveProcess.Probability.Orlicz.WeakBridge
import Homogenization.Probability.IndependentSums.GammaSigma.Operations

/-! Maximum scaling, adapting the author's Superdiffusion maximum calculus
and bridging its weak-tail convention to the expectation convention. -/
open MeasureTheory Homogenization.IndependentSums
noncomputable section
namespace SubdiffusiveProcess.Probability.Orlicz
variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem isBigOWith_gammaSigma_finset_sup'_of_nonempty [IsFiniteMeasure μ]
    (s : Finset ι) (hs : s.Nonempty) {X : ι → Ω → ℝ} {A σ : ℝ}
    (hσ : 0 < σ) (hA : 0 ≤ A)
    (hX : ∀ i ∈ s, IsBigOWith μ (gammaSigma σ) (X i) A) :
    IsBigOWith μ (gammaSigma σ) (fun ω => s.sup' hs fun i => X i ω)
      ((3 * max 1 (Real.log (s.card : ℝ))) ^ σ⁻¹ * A) := by
  have hinv : (0 : ℝ) ≤ σ⁻¹ := inv_nonneg.2 hσ.le
  by_cases hcard : 2 ≤ s.card
  · have hcard_real : (2 : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast hcard
    have hlog_pos : 0 < Real.log (s.card : ℝ) := Real.log_pos (by linarith)
    have hbase_nonneg : (0 : ℝ) ≤ 3 * Real.log (s.card : ℝ) := by linarith
    have hbase_le : 3 * Real.log (s.card : ℝ)
        ≤ 3 * max 1 (Real.log (s.card : ℝ)) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)
    refine (isBigOWith_gammaSigma_finset_sup' (μ := μ) s hs (X := X) (A := A)
      (σ := σ) hσ hcard hX).mono_scale ?_
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hbase_nonneg hbase_le hinv) hA
  · have hcard_eq : s.card = 1 := by
      have hpos := hs.card_pos
      omega
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard_eq
    have hfun : (fun ω => ({i} : Finset ι).sup' hs fun j => X j ω) = X i := by
      funext ω
      simp
    have hcard_one : ((({i} : Finset ι).card : ℝ)) = 1 := by simp
    have hmax : max (1 : ℝ) 0 = 1 := max_eq_left (by norm_num)
    rw [hfun, hcard_one, Real.log_one, hmax, mul_one]
    refine (hX i (Finset.mem_singleton_self i)).mono_scale ?_
    exact le_mul_of_one_le_left hA (Real.one_le_rpow (by norm_num) hinv)


theorem exists_ogammaLE_maximum (s : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
        ∀ σ : ℝ, 0 < σ → ∀ (ι : Type) (I : Finset ι) (hI : I.Nonempty) (X : ι → Ω → ℝ),
          (∀ i ∈ I, Measurable (X i)) → (∀ i ∈ I, SubdiffusiveProcess.OGammaLE μ s σ (X i)) →
          SubdiffusiveProcess.OGammaLE μ s (C * (Real.log (2 * (I.card : ℝ))) ^ (1 / s) * σ)
            (fun ω => I.sup' hI (fun i => X i ω)) := by
  let D : ℝ := (1 + Real.log 2) ^ s⁻¹
  let H : ℝ := 1 + 1 / Real.log 2
  let C : ℝ := (4 : ℝ) ^ s⁻¹ * (3 * H) ^ s⁻¹ * D
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < D := Real.rpow_pos_of_pos (by linarith) _
  have hH : 0 < H := by dsimp [H]; positivity
  have h4 : 0 < (4 : ℝ) ^ s⁻¹ := Real.rpow_pos_of_pos (by norm_num) _
  have hQ : 0 < (3 * H) ^ s⁻¹ := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨C, mul_pos (mul_pos h4 hQ) hD, ?_⟩
  intro Ω _ μ _ σ hσ ι I hI X hm hX
  have hw : ∀ i ∈ I, IsBigOWith μ (gammaSigma s) (X i) (D * σ) :=
    fun i hi => isBigOWith_gammaSigma_of_ogammaLE hs hσ (hX i hi)
  have hA : 0 < D * σ := mul_pos hD hσ
  have hmax := isBigOWith_gammaSigma_finset_sup'_of_nonempty I hI hs hA.le hw
  have hMm : Measurable (fun ω => I.sup' hI (fun i => X i ω)) := by
    convert Finset.measurable_sup' hI hm using 1
    ext ω
    exact (Finset.sup'_apply hI X ω).symm
  have hbase : 0 < 3 * max 1 (Real.log (I.card : ℝ)) :=
    mul_pos (by norm_num) (zero_lt_one.trans_le (le_max_left _ _))
  have hB : 0 < (3 * max 1 (Real.log (I.card : ℝ))) ^ s⁻¹ * (D * σ) :=
    mul_pos (Real.rpow_pos_of_pos hbase _) hA
  have ho := ogammaLE_of_isBigOWith_gammaSigma hs hB hMm hmax
  let L : ℝ := Real.log (2 * (I.card : ℝ))
  have hn : (1 : ℝ) ≤ I.card := by exact_mod_cast hI.card_pos
  have hnp : (0 : ℝ) < I.card := zero_lt_one.trans_le hn
  have hln : 0 ≤ Real.log (I.card : ℝ) := Real.log_nonneg hn
  have hL : L = Real.log 2 + Real.log (I.card : ℝ) := Real.log_mul (by norm_num) hnp.ne'
  have hLp : 0 < L := by rw [hL]; linarith
  have hmaxL : max 1 (Real.log (I.card : ℝ)) ≤ H * L := by
    have hd : 1 ≤ L / Real.log 2 := (le_div_iff₀ hlog).mpr (by rw [hL]; linarith)
    have hlnL : Real.log (I.card : ℝ) ≤ L := by rw [hL]; linarith
    have hm : max 1 (Real.log (I.card : ℝ)) ≤ 1 + Real.log (I.card : ℝ) :=
      max_le (by linarith) (by linarith)
    refine hm.trans ?_
    dsimp [H]
    rw [add_mul, one_mul, one_div_mul_eq_div]
    linarith
  have hpow : (3 * max 1 (Real.log (I.card : ℝ))) ^ s⁻¹ ≤
      (3 * H) ^ s⁻¹ * L ^ s⁻¹ := by
    rw [← Real.mul_rpow (by positivity : 0 ≤ 3 * H) hLp.le]
    exact Real.rpow_le_rpow hbase.le (by nlinarith [hmaxL]) (inv_nonneg.mpr hs.le)
  have hscale : (4 : ℝ) ^ s⁻¹ * ((3 * max 1 (Real.log (I.card : ℝ))) ^ s⁻¹ * (D * σ)) ≤
      C * L ^ s⁻¹ * σ := by
    calc
      _ ≤ (4 : ℝ) ^ s⁻¹ * (((3 * H) ^ s⁻¹ * L ^ s⁻¹) * (D * σ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hA.le) h4.le
      _ = _ := by dsimp [C]; ring
  have h := SubdiffusiveProcess.CoarseGrainingVocab.OGamma.ogammaLE_mono_scale
    (mul_pos h4 hB) hscale hs.le hMm.aemeasurable ho
  simpa only [one_div] using h

end SubdiffusiveProcess.Probability.Orlicz
