import SubdiffusiveProcess.Probability.ProductLpContraction
import SubdiffusiveProcess.Probability.LayerProductBlocks
import SubdiffusiveProcess.Probability.ProductConditionalExpectation
import SubdiffusiveProcess.Main.ChaosSampleLaw

open MeasureTheory Filter Set SubdiffusiveProcess
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper


/-- L^p contraction of the conditional expectation onto the coordinates in an arbitrary index set `S`
of an infinite product of probability spaces (finite `p`, `1 ≤ p`). -/
theorem aux_gcat_band_condexp_restrict_eLpNorm_le
    (Y : ℤ → Type) [instY : ∀ j, MeasurableSpace (Y j)]
    (laws : (j : ℤ) → Measure (Y j)) [∀ j, IsProbabilityMeasure (laws j)]
    (S : Set ℤ) {f : ((j : ℤ) → Y j) → ℝ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ∞) (hf : Integrable f (Measure.infinitePi laws)) :
    eLpNorm ((Measure.infinitePi laws)[f |
        (inferInstance : MeasurableSpace ((j : S) → Y j)).comap S.restrict]) p
        (Measure.infinitePi laws) ≤ eLpNorm f p (Measure.infinitePi laws) := by
  classical
  let e : ((j : ℤ) → Y j) ≃ᵐ
      ((j : S) → Y j) × ((j : {j : ℤ // j ∉ S}) → Y j) :=
    MeasurableEquiv.piEquivPiSubtypeProd Y (fun j => j ∈ S)
  let μ : Measure (((j : ℤ) → Y j)) := Measure.infinitePi laws
  let ν : Measure (((j : S) → Y j) × ((j : {j : ℤ // j ∉ S}) → Y j)) :=
    (Measure.infinitePi (fun j : S => laws j.1)).prod
      (Measure.infinitePi (fun j : {j : ℤ // j ∉ S} => laws j.1))
  have he : MeasurePreserving e μ ν :=
    SubdiffusiveProcess.measurePreserving_infinitePi_split laws (fun j => j ∈ S)
  have hband_eq : (inferInstance : MeasurableSpace ((j : S) → Y j)).comap S.restrict =
      (inferInstance : MeasurableSpace ((j : S) → Y j)).comap (fun ω => (e ω).1) := rfl
  have hce : μ[f | (inferInstance : MeasurableSpace ((j : S) → Y j)).comap S.restrict] =ᵐ[μ]
      (ν[f ∘ e.symm | (inferInstance : MeasurableSpace ((j : S) → Y j)).comap Prod.fst]) ∘ e := by
    rw [hband_eq]
    simpa only [MeasurableSpace.comap_comp, Function.comp_def, e.symm_apply_apply] using
      (SubdiffusiveProcess.condExp_comp_measurableEquiv e he measurable_fst.comap_le
        (f := f ∘ e.symm) ((he.symm e).integrable_comp_of_integrable hf))
  rw [eLpNorm_congr_ae hce]
  calc
    eLpNorm ((ν[f ∘ e.symm |
        (inferInstance : MeasurableSpace ((j : S) → Y j)).comap Prod.fst]) ∘ e) p μ =
        eLpNorm (ν[f ∘ e.symm |
          (inferInstance : MeasurableSpace ((j : S) → Y j)).comap Prod.fst]) p ν := by
      exact eLpNorm_comp_measurePreserving
        (stronglyMeasurable_condExp.mono measurable_fst.comap_le).aestronglyMeasurable he
    _ ≤ eLpNorm (f ∘ e.symm) p ν :=
      SubdiffusiveProcess.condExp_prod_fst_eLpNorm_le hp hpt
        ((he.symm e).integrable_comp_of_integrable hf)
    _ = eLpNorm f p μ := by
      exact eLpNorm_comp_measurePreserving hf.aestronglyMeasurable (he.symm e)



/-- Abstract limit passage for band approximants: an `L^p`-limit `X` of `Xn`, each within `ε` (in `L^p`)
of an `m`-measurable `Yn`, is within `2ε` of its own conditional expectation on `m`, provided
conditional expectation is an `L^p`-contraction. -/
theorem aux_gcat_band_condexp_limit_abstract
    {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : m ≤ m0) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hcontr : ∀ z : Ω → ℝ, Integrable z μ → eLpNorm (μ[z|m]) p μ ≤ eLpNorm z p μ)
    {X : Ω → ℝ} (hX : MemLp X p μ) {Xn Yn : ℕ → Ω → ℝ} (hXn : ∀ n, MemLp (Xn n) p μ)
    (hconv : Tendsto (fun n => eLpNorm (Xn n - X) p μ) atTop (𝓝 0))
    {ε : ℝ≥0∞}
    (hYm : ∀ᶠ n in atTop, AEStronglyMeasurable[m] (Yn n) μ)
    (hYe : ∀ᶠ n in atTop, eLpNorm (Xn n - Yn n) p μ ≤ ε) :
    eLpNorm (X - μ[X|m]) p μ ≤ 2 * ε := by
  by_cases hε : ε = ⊤
  · simp [hε]
  have hXi : Integrable X μ := hX.integrable hp
  have hkey : ∀ n, AEStronglyMeasurable[m] (Yn n) μ → eLpNorm (Xn n - Yn n) p μ ≤ ε →
      eLpNorm (X - μ[X|m]) p μ ≤ 2 * eLpNorm (Xn n - X) p μ + 2 * ε := by
    intro n hYn hYen
    have hXni : Integrable (Xn n) μ := (hXn n).integrable hp
    have hd : MemLp (Xn n - Yn n) p μ :=
      ⟨(hXn n).aestronglyMeasurable.sub (hYn.mono hm), hYen.trans_lt (lt_top_iff_ne_top.mpr hε)⟩
    have hYi : Integrable (Yn n) μ := by
      have h1 : MemLp (Yn n) p μ := by
        have := (hXn n).sub hd
        simpa using this
      exact h1.integrable hp
    -- condExp of `Yn n` is itself
    obtain ⟨Y', hY'm, hY'eq⟩ := hYn
    have hY'i : Integrable Y' μ := hYi.congr hY'eq
    have hcondY : μ[Yn n|m] =ᵐ[μ] Yn n := by
      have h1 : μ[Yn n|m] =ᵐ[μ] μ[Y'|m] := condExp_congr_ae hY'eq
      have h2 : μ[Y'|m] = Y' := condExp_of_stronglyMeasurable hm hY'm hY'i
      filter_upwards [h1, hY'eq] with ω h1 h2'
      rw [h1, h2, h2']
    have hce1 : μ[Yn n - Xn n|m] =ᵐ[μ] μ[Yn n|m] - μ[Xn n|m] := condExp_sub hYi hXni m
    have hce2 : μ[Xn n - X|m] =ᵐ[μ] μ[Xn n|m] - μ[X|m] := condExp_sub hXni hXi m
    have heq : X - μ[X|m] =ᵐ[μ]
        (X - Xn n) + (Xn n - Yn n) + μ[Yn n - Xn n|m] + μ[Xn n - X|m] := by
      filter_upwards [hce1, hce2, hcondY] with ω h1 h2 h3
      simp only [Pi.sub_apply, Pi.add_apply] at h1 h2 h3 ⊢
      rw [h1, h2, h3]
      ring
    rw [eLpNorm_congr_ae heq]
    have hb1 : eLpNorm (X - Xn n) p μ = eLpNorm (Xn n - X) p μ := by
      rw [← eLpNorm_neg]; congr 1; funext ω; simp
    have hb2 : eLpNorm (μ[Yn n - Xn n|m]) p μ ≤ ε := by
      refine (hcontr _ (hYi.sub hXni)).trans ?_
      rw [← eLpNorm_neg]
      refine le_trans (le_of_eq ?_) hYen
      congr 1; funext ω; simp
    have hb3 : eLpNorm (μ[Xn n - X|m]) p μ ≤ eLpNorm (Xn n - X) p μ :=
      hcontr _ (hXni.sub hXi)
    have hm1 : AEStronglyMeasurable (X - Xn n) μ := hX.aestronglyMeasurable.sub (hXn n).aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (Xn n - Yn n) μ := hd.aestronglyMeasurable
    have hm3 : AEStronglyMeasurable (μ[Yn n - Xn n|m]) μ :=
      (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable
    have hm4 : AEStronglyMeasurable (μ[Xn n - X|m]) μ :=
      (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable
    calc eLpNorm ((X - Xn n) + (Xn n - Yn n) + μ[Yn n - Xn n|m] + μ[Xn n - X|m]) p μ
        ≤ eLpNorm ((X - Xn n) + (Xn n - Yn n) + μ[Yn n - Xn n|m]) p μ +
            eLpNorm (μ[Xn n - X|m]) p μ := eLpNorm_add_le ((hm1.add hm2).add hm3) hm4 hp
      _ ≤ (eLpNorm ((X - Xn n) + (Xn n - Yn n)) p μ + eLpNorm (μ[Yn n - Xn n|m]) p μ) +
            eLpNorm (μ[Xn n - X|m]) p μ := by
          gcongr
          exact eLpNorm_add_le (hm1.add hm2) hm3 hp
      _ ≤ ((eLpNorm (X - Xn n) p μ + eLpNorm (Xn n - Yn n) p μ) + eLpNorm (μ[Yn n - Xn n|m]) p μ) +
            eLpNorm (μ[Xn n - X|m]) p μ := by
          gcongr
          exact eLpNorm_add_le hm1 hm2 hp
      _ ≤ 2 * eLpNorm (Xn n - X) p μ + 2 * ε := by
          rw [hb1]
          have : eLpNorm (Xn n - Yn n) p μ ≤ ε := hYen
          calc (eLpNorm (Xn n - X) p μ + eLpNorm (Xn n - Yn n) p μ) + eLpNorm (μ[Yn n - Xn n|m]) p μ +
                eLpNorm (μ[Xn n - X|m]) p μ
              ≤ (eLpNorm (Xn n - X) p μ + ε) + ε + eLpNorm (Xn n - X) p μ := by gcongr
            _ = 2 * eLpNorm (Xn n - X) p μ + 2 * ε := by ring
  have hev : ∀ᶠ n in atTop, eLpNorm (X - μ[X|m]) p μ ≤ 2 * eLpNorm (Xn n - X) p μ + 2 * ε := by
    filter_upwards [hYm, hYe] with n h1 h2
    exact hkey n h1 h2
  have hlim : Tendsto (fun n => 2 * eLpNorm (Xn n - X) p μ + 2 * ε) atTop (𝓝 (2 * 0 + 2 * ε)) :=
    ((ENNReal.Tendsto.const_mul hconv (Or.inr (by norm_num))).add_const _)
  have := ge_of_tendsto hlim hev
  simpa using this


/-- The layer `σ`-field `σ(ω_{-j} : lo ≤ j ≤ hi)` of the interval events of `lem_witness`. -/
def aux_gcat_band_condexp_Bsig (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (lo hi : ℤ) : MeasurableSpace (BilateralField d) :=
  MeasurableSpace.comap
    (fun omega : BilateralField d => fun j : Set.Icc lo hi => omega (-(j : ℤ)))
    (inferInstance : MeasurableSpace ((j : Set.Icc lo hi) → C(SpatialCoordinates d, ℝ)))

/-- `σ(ω_{-j} : j ∈ [lo,hi])` is the comap of the coordinate restriction to `[-hi,-lo]`. -/
theorem aux_gcat_band_condexp_Bsig_eq (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (lo hi : ℤ) :
    aux_gcat_band_condexp_Bsig d lo hi =
      (inferInstance : MeasurableSpace ((j : Set.Icc (-hi) (-lo)) → C(SpatialCoordinates d, ℝ))).comap
        (Set.Icc (-hi) (-lo)).restrict := by
  unfold aux_gcat_band_condexp_Bsig
  apply le_antisymm
  · let r : ((j : Set.Icc (-hi) (-lo)) → C(SpatialCoordinates d, ℝ)) →
        ((j : Set.Icc lo hi) → C(SpatialCoordinates d, ℝ)) :=
      fun x j => x ⟨-(j : ℤ), by
        have h := j.2
        simp only [Set.mem_Icc] at h ⊢
        omega⟩
    have hr : Measurable r := measurable_pi_iff.mpr (fun j => measurable_pi_apply _)
    have hfac : (fun omega : BilateralField d => fun j : Set.Icc lo hi => omega (-(j : ℤ))) =
        r ∘ (Set.Icc (-hi) (-lo)).restrict := rfl
    rw [hfac, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hr.comap_le
  · let r : ((j : Set.Icc lo hi) → C(SpatialCoordinates d, ℝ)) →
        ((j : Set.Icc (-hi) (-lo)) → C(SpatialCoordinates d, ℝ)) :=
      fun x j => x ⟨-(j : ℤ), by
        have h := j.2
        simp only [Set.mem_Icc] at h ⊢
        omega⟩
    have hr : Measurable r := measurable_pi_iff.mpr (fun j => measurable_pi_apply _)
    have hfac : (Set.Icc (-hi) (-lo)).restrict =
        r ∘ (fun omega : BilateralField d => fun j : Set.Icc lo hi => omega (-(j : ℤ))) := by
      funext omega j
      simp [r, Set.restrict]
    rw [hfac, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hr.comap_le

theorem aux_gcat_band_condexp_Bsig_le (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (lo hi : ℤ) : aux_gcat_band_condexp_Bsig d lo hi ≤ (inferInstance : MeasurableSpace (BilateralField d)) := by
  unfold aux_gcat_band_condexp_Bsig
  have h : Measurable (fun omega : BilateralField d => fun j : Set.Icc lo hi => omega (-(j : ℤ))) :=
    measurable_pi_iff.mpr (fun j => measurable_pi_apply (-(j : ℤ)))
  exact h.comap_le

/-- Conditional expectation onto a layer band is an `L^p`-contraction under the model law. -/
theorem aux_gcat_band_condexp_contraction (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (lo hi : ℤ) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (z : BilateralField d → ℝ) (hz : Integrable z (chaosSampleLaw M).toMeasure) :
    eLpNorm ((chaosSampleLaw M).toMeasure[z | aux_gcat_band_condexp_Bsig d lo hi]) p
        (chaosSampleLaw M).toMeasure ≤ eLpNorm z p (chaosSampleLaw M).toMeasure := by
  rw [aux_gcat_band_condexp_Bsig_eq]
  exact aux_gcat_band_condexp_restrict_eLpNorm_le (Y := fun _ => C(SpatialCoordinates d, ℝ))
    (fun j => (SubdiffusiveProcess.scaledLayerLaw d (SubdiffusiveProcess.chaosRootFieldLaw M) j :
      Measure C(SpatialCoordinates d, ℝ))) (Set.Icc (-hi) (-lo)) hp hpt hz

/-- Band approximation of an `L^p`-limit: if `X_n → X` in `L^p` of the model law and `X_n` is within `ε`
(in `L^p`) of a `σ(ω_{-j} : lo ≤ j ≤ hi)`-measurable function for all large `n`, then `X` is within `2ε`
of its conditional expectation on that band. -/
theorem gcat_band_condexp (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (lo hi : ℤ) {p : ℝ} (hp : 1 ≤ p)
    {X : BilateralField d → ℝ} (hX : MemLp X (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure)
    {Xn Yn : ℕ → BilateralField d → ℝ}
    (hXn : ∀ n, MemLp (Xn n) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure)
    (hconv : Tendsto (fun n => eLpNorm (Xn n - X) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure)
      atTop (𝓝 0))
    {ε : ℝ}
    (hYm : ∀ᶠ n in atTop, AEStronglyMeasurable[MeasurableSpace.comap
        (fun omega : BilateralField d => fun j : Set.Icc lo hi => omega (-(j : ℤ)))
        (inferInstance : MeasurableSpace ((j : Set.Icc lo hi) → C(SpatialCoordinates d, ℝ)))]
      (Yn n) (chaosSampleLaw M).toMeasure)
    (hYe : ∀ᶠ n in atTop, eLpNorm (Xn n - Yn n) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ε) :
    StronglyMeasurable[aux_gcat_band_condexp_Bsig d lo hi]
        ((chaosSampleLaw M).toMeasure[X | aux_gcat_band_condexp_Bsig d lo hi]) ∧
      eLpNorm (X - (chaosSampleLaw M).toMeasure[X | aux_gcat_band_condexp_Bsig d lo hi])
        (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (2 * ε) := by
  have hp' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  refine ⟨stronglyMeasurable_condExp, ?_⟩
  have hlim := aux_gcat_band_condexp_limit_abstract (m := aux_gcat_band_condexp_Bsig d lo hi)
    (aux_gcat_band_condexp_Bsig_le d lo hi) hp'
    (fun z hz => aux_gcat_band_condexp_contraction d M lo hi hp' ENNReal.ofReal_ne_top z hz)
    hX hXn hconv hYm hYe
  have hε : ε ≤ 0 ∨ 0 < ε := le_or_gt ε 0
  rcases hε with hε | hε
  · -- a nonpositive bound forces the trivial case: 2 * ofReal ε = 0 = ofReal (2ε)
    have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal ε = ENNReal.ofReal (2 * ε) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]; simp
    rw [← h2]; exact hlim
  · have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal ε = ENNReal.ofReal (2 * ε) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]; simp
    rw [← h2]; exact hlim

end Paper
