module

public import SubdiffusiveProcess.Sobolev.GMCRootOrlicz
public import SubdiffusiveProcess.Sobolev.AnchoredContraction
public import SubdiffusiveProcess.Probability.GMCFieldLaws

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess

/-- The actual GMC root law has a uniform exponential-square bound for anchored contractions on each compact set. -/
theorem exists_gmc_anchored_contraction_exp_square
    {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (R : ℝ) (hR : 0 < R) :
    ∃ m : ℕ, 0 < m ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (K : Compacts (SpatialCoordinates d))
        (hK : ∀ x ∈ (K : Set (SpatialCoordinates d)), ‖x‖ ≤ R)
        (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1),
        let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ)) :=
          ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
        let ν := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).map forget
        (∫⁻ f, ENNReal.ofReal (Real.exp
          ((‖(f.comp (⟨fun x : SpatialCoordinates d => c • x,
              by fun_prop⟩ :
                C(SpatialCoordinates d, SpatialCoordinates d))).restrict
                  (K : Set (SpatialCoordinates d)) - ContinuousMap.const K (f 0)‖ /
            (c * R * ((m : ℝ) * M.delta))) ^ 2)) ∂ν.toMeasure) ≤ 2 := by
  classical
  obtain ⟨S, hSne, hLip, hExp⟩ :=
    exists_gmc_root_lipschitz_cover_exp_square (d := d) R
  refine ⟨S.card, Finset.card_pos.mpr hSne, ?_⟩
  intro M K hK c hc0 hc1
  dsimp only
  let μ : Measure (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :=
    (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure
  let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let Φ : C(SpatialCoordinates d, ℝ) → ℝ≥0∞ := fun f =>
    ENNReal.ofReal (Real.exp
      ((‖(f.comp (⟨fun x : SpatialCoordinates d => c • x,
          by fun_prop⟩ :
            C(SpatialCoordinates d, SpatialCoordinates d))).restrict
              (K : Set (SpatialCoordinates d)) - ContinuousMap.const K (f 0)‖ /
        (c * R * ((S.card : ℝ) * M.delta))) ^ 2))
  have hΦ : Measurable Φ := by
    let dilation : C(SpatialCoordinates d, SpatialCoordinates d) :=
      ⟨fun x => c • x, by fun_prop⟩
    have hcomp : Continuous
        (fun f : C(SpatialCoordinates d, ℝ) => f.comp dilation) :=
      ContinuousMap.continuous_precomp dilation
    have hrestrict : Continuous
        (fun f : C(SpatialCoordinates d, ℝ) =>
          (f.comp dilation).restrict (K : Set (SpatialCoordinates d))) :=
      (ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d))).comp hcomp
    have hanchor : Continuous
        (fun f : C(SpatialCoordinates d, ℝ) => ContinuousMap.const K (f 0)) :=
      ContinuousMap.continuous_const'.comp (continuous_eval_const (0 : SpatialCoordinates d))
    have hnorm : Continuous
        (fun f : C(SpatialCoordinates d, ℝ) =>
          ‖(f.comp dilation).restrict (K : Set (SpatialCoordinates d)) -
            ContinuousMap.const K (f 0)‖) :=
      continuous_norm.comp (hrestrict.sub hanchor)
    dsimp [Φ, dilation]
    exact (ENNReal.continuous_ofReal.comp
      (Real.continuous_exp.comp ((hnorm.div_const _).pow 2))).measurable
  change (∫⁻ f, Φ f ∂Measure.map forget μ) ≤ 2
  rw [lintegral_map hΦ forget.continuous.measurable]
  let W : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d → ℝ := fun g =>
    ∑ z ∈ S, SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate z g)
  have hδ : 0 < M.delta := M.shellPrefix.delta_pos
  have hcard : 0 < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hSne
  have hden : (∑ z ∈ S, M.delta) = (S.card : ℝ) * M.delta := by
    simp
  have hdenpos : 0 < c * R * ((S.card : ℝ) * M.delta) := by
    positivity
  have hW0 : ∀ g, 0 ≤ W g := by
    intro g
    dsimp [W]
    exact Finset.sum_nonneg (fun z hz =>
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.g2Observable_nonneg _)
  have hpoint : ∀ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      Φ (forget g) ≤ ENNReal.ofReal (Real.exp
        (((W g) / (∑ z ∈ S, M.delta)) ^ 2)) := by
    intro g
    have hn := norm_anchored_contraction_on_compact_le K (forget g)
      hc0.le hc1 hR.le hK (hLip g)
    have hn' :
        ‖((forget g).comp (⟨fun x : SpatialCoordinates d => c • x,
            by fun_prop⟩ :
          C(SpatialCoordinates d, SpatialCoordinates d))).restrict
              (K : Set (SpatialCoordinates d)) - ContinuousMap.const K ((forget g) 0)‖
          ≤ c * R * W g := by
      erw [NNReal.coe_sum] at hn
      simpa [W, forget] using! hn
    have hq :
        ‖((forget g).comp (⟨fun x : SpatialCoordinates d => c • x,
            by fun_prop⟩ :
          C(SpatialCoordinates d, SpatialCoordinates d))).restrict
              (K : Set (SpatialCoordinates d)) - ContinuousMap.const K ((forget g) 0)‖ /
            (c * R * ((S.card : ℝ) * M.delta)) ≤
          W g / (∑ z ∈ S, M.delta) := by
      calc
        _ ≤ (c * R * W g) / (c * R * ((S.card : ℝ) * M.delta)) :=
          div_le_div_of_nonneg_right hn' hdenpos.le
        _ = W g / (∑ z ∈ S, M.delta) := by
          rw [hden]
          field_simp
    have hq0 : 0 ≤
        ‖((forget g).comp (⟨fun x : SpatialCoordinates d => c • x,
            by fun_prop⟩ :
          C(SpatialCoordinates d, SpatialCoordinates d))).restrict
              (K : Set (SpatialCoordinates d)) - ContinuousMap.const K ((forget g) 0)‖ /
            (c * R * ((S.card : ℝ) * M.delta)) :=
      div_nonneg (norm_nonneg _) hdenpos.le
    have hr0 : 0 ≤ W g / (∑ z ∈ S, M.delta) :=
      div_nonneg (hW0 g) (by rw [hden]; positivity)
    have hsq := (sq_le_sq₀ hq0 hr0).2 hq
    have hexp : Real.exp
        ((‖((forget g).comp (⟨fun x : SpatialCoordinates d => c • x,
            by fun_prop⟩ :
          C(SpatialCoordinates d, SpatialCoordinates d))).restrict
              (K : Set (SpatialCoordinates d)) - ContinuousMap.const K ((forget g) 0)‖ /
            (c * R * ((S.card : ℝ) * M.delta))) ^ 2) ≤
        Real.exp ((W g / (∑ z ∈ S, M.delta)) ^ 2) :=
      Real.exp_le_exp.mpr hsq
    exact ENNReal.ofReal_mono hexp
  exact (lintegral_mono hpoint).trans (by
    simpa [W] using hExp M)

end SubdiffusiveProcess
