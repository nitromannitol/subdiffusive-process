module

public import SubdiffusiveProcess.Paper.prop_conc_fine_layer_crude

@[expose] public section

/-! Assembly of the fine-layer step: the fine case (relative wavelength `3^{-n} ≤ r0`) and the crude case
(`3^{-n} > r0`, finitely many scales) combine to `‖f(ω) - f(ω^{(j)})‖_p ≤ C δ (M - m) 3^{-aexp n}` for every layer
`j` with `j + k ≤ 0`, with `n = |j + k|`, `aexp = 3b/8`, `b = t (t - d + 1)/(t + 1)`, `t = d - 1/2`. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology
namespace Paper
noncomputable section

theorem prop_conc_fine_layer_assembly (d : ℕ) (hd : 2 ≤ d)
    (hES : SubdiffusiveProcess.Lane3.EfronSteinMomentInequality)
    (C0 : ℝ) (hC0 : 1 ≤ C0) (p : ℝ) (hp : 2 ≤ p) (B : ℝ) (hB0 : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧
    ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
      (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      (field : Ω → BilateralField d) (m M : ℝ) (Q : Opens (SpatialCoordinates d))
      (zcell : SpatialCoordinates d) (k : ℕ) (r : ℝ) (hr : 0 < r) (_hrk : r = (3 : ℝ) ^ (-(k : ℝ)))
      (c : ℝ), c ∈ Set.Icc m M →
      ∀ (pvec : Fin d → ℝ), pvec ∈ aux_prop_conc_pair_data_slopes d →
      ∀ (f K : BilateralField d → ℝ) (j : ℤ), j + (k : ℤ) ≤ 0 →
        prop_conc_fine_layer_data d model C0 m M Q zcell r hr c pvec (aux_prop_conc_fine_layer_fine_t d)
          p B P field f K j →
        eLpNorm (fun q : BilateralField d × BilateralField d => f q.1 - f (Function.update q.1 j (q.2 j)))
            (ENNReal.ofReal p)
            ((chaosSampleLaw model).toMeasure.prod (chaosSampleLaw model).toMeasure) ≤
          ENNReal.ofReal (C * model.delta * (M - m) *
            (3 : ℝ) ^ (-(3 * aux_prop_conc_fine_layer_fine_b d / 8) * ((j + (k : ℤ)).natAbs : ℝ))) := by
  obtain ⟨r0, hr0, Kf, hKf, hfine⟩ := prop_conc_fine_layer_fine d hd hES C0 hC0 p hp B hB0
  obtain ⟨Kc, hKc, hcrude⟩ := prop_conc_fine_layer_crude d hd C0 hC0 p hp B
  have hb : 0 < aux_prop_conc_fine_layer_fine_b d := by
    have h1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    unfold aux_prop_conc_fine_layer_fine_b aux_prop_conc_fine_layer_fine_t
    have h2 : (0 : ℝ) < (d : ℝ) - 1 / 2 := by linarith
    have h3 : (0 : ℝ) < (d : ℝ) - 1 / 2 - d + 1 := by linarith
    positivity
  set b : ℝ := aux_prop_conc_fine_layer_fine_b d with hbdef
  refine ⟨Kf + Kc * ((r0 ^ (-(b / 12))) ^ 2) * r0 ^ (-(3 * b / 8)), by positivity, ?_⟩
  intro _ _ model Ω _ P field m M Q zcell k r hr hrk c hc pvec hpvec f K j hjk hD
  have hδ0 : 0 < model.delta := model.shellPrefix.delta_pos
  have hgap : 0 ≤ M - m := sub_nonneg.mpr (hc.1.trans hc.2)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (j + (k : ℤ)).natAbs = n := ⟨_, rfl⟩
  have hjn : j = -((n + k : ℕ) : ℤ) := by push_cast; omega
  rw [hn]
  obtain ⟨rs, hrsdef⟩ : ∃ rs : ℝ, rs = (3 : ℝ) ^ (-(n : ℝ)) := ⟨_, rfl⟩
  have hrs0 : 0 < rs := by rw [hrsdef]; positivity
  have hrs1 : rs ≤ 1 := by
    rw [hrsdef]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simp)
  have hpow : (3 : ℝ) ^ (-(3 * b / 8) * (n : ℝ)) = rs ^ (3 * b / 8) := by
    rw [hrsdef, ← Real.rpow_mul (by norm_num)]; congr 1; ring
  rw [hpow]
  by_cases hrs : rs ≤ r0
  · have := hfine model P field m M Q zcell k r hr hrk c hc pvec hpvec f K j n hjn hD (by rw [← hrsdef]; exact hrs)
    rw [← hrsdef] at this
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    have hrb : 0 < rs ^ (3 * b / 8) := Real.rpow_pos_of_pos hrs0 _
    have : 0 ≤ Kc * ((r0 ^ (-(b / 12))) ^ 2) * r0 ^ (-(3 * b / 8)) := by positivity
    nlinarith [mul_pos (mul_pos hδ0 hrb) (show (0:ℝ) < 1 by norm_num), mul_nonneg (mul_nonneg hδ0.le hgap) hrb.le,
      mul_nonneg (mul_nonneg (mul_nonneg hδ0.le hgap) hrb.le) this]
  · push_neg at hrs
    have := hcrude model P field m M Q zcell k r hr hrk c hc pvec hpvec f K j n hjn hD
    rw [← hrsdef] at this
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : rs ^ (-(b / 12)) ≤ r0 ^ (-(b / 12)) :=
      Real.rpow_le_rpow_of_nonpos hr0 hrs.le (by have : 0 < b / 12 := by positivity
                                                 linarith)
    have h2 : r0 ^ (3 * b / 8) ≤ rs ^ (3 * b / 8) := Real.rpow_le_rpow hr0.le hrs.le (by positivity)
    have h3 : r0 ^ (-(3 * b / 8)) * rs ^ (3 * b / 8) ≥ 1 := by
      calc r0 ^ (-(3 * b / 8)) * rs ^ (3 * b / 8) ≥ r0 ^ (-(3 * b / 8)) * r0 ^ (3 * b / 8) :=
            mul_le_mul_of_nonneg_left h2 (Real.rpow_pos_of_pos hr0 _).le
        _ = 1 := by rw [← Real.rpow_add hr0]; simp
    have h4 : (rs ^ (-(b / 12))) ^ 2 ≤ (r0 ^ (-(b / 12))) ^ 2 := by
      have := Real.rpow_pos_of_pos hrs0 (-(b / 12))
      exact pow_le_pow_left₀ this.le h1 2
    have h5 : (rs ^ (-(b / 12))) ^ 2 ≤ (r0 ^ (-(b / 12))) ^ 2 * r0 ^ (-(3 * b / 8)) * rs ^ (3 * b / 8) := by
      calc (rs ^ (-(b / 12))) ^ 2 ≤ (r0 ^ (-(b / 12))) ^ 2 * 1 := by simpa using h4
        _ ≤ (r0 ^ (-(b / 12))) ^ 2 * (r0 ^ (-(3 * b / 8)) * rs ^ (3 * b / 8)) :=
            mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
        _ = _ := by ring
    have hrb : 0 < rs ^ (3 * b / 8) := Real.rpow_pos_of_pos hrs0 _
    have hpos : 0 ≤ model.delta * (M - m) := mul_nonneg hδ0.le hgap
    calc Kc * model.delta * (M - m) * (rs ^ (-(b / 12))) ^ 2
        ≤ Kc * model.delta * (M - m) * ((r0 ^ (-(b / 12))) ^ 2 * r0 ^ (-(3 * b / 8)) * rs ^ (3 * b / 8)) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ ≤ _ := by
          have : 0 ≤ Kf * model.delta * (M - m) * rs ^ (3 * b / 8) := by positivity
          nlinarith [this]

end
end Paper
