module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceProviderGMC
public import SubdiffusiveProcess.Frozen.Section8.MassiveNegativeSobolevNormSq
public import SubdiffusiveProcess.Frozen.Vocab.Ahom
public import SubdiffusiveProcess.Frozen.Assumptions.OGammaLE

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Set Topology
open Homogenization
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.Frozen.Section8
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- A nonpositive random variable satisfies every `O_{Γ_1}` bound. -/
theorem ogammaLE_one_of_nonpos {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu] {A : ℝ} {X : Omega → ℝ}
    (hX : ∀ omega, X omega ≤ 0) : SubdiffusiveProcess.OGammaLE mu 1 A X := by
  have hpt : ∀ omega, Real.exp ((A⁻¹ * max (X omega) 0) ^ (1 : ℝ)) = 1 := by
    intro omega
    rw [max_eq_right (hX omega)]
    simp
  constructor
  · exact (integrable_const (1 : ℝ)).congr
      (Filter.Eventually.of_forall fun omega ↦ (hpt omega).symm)
  · rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    simp

/-- The deterministic clause and the two `O_{Γ_1}` tails of the frozen block
are satisfied by the trivial witnesses `R* := R` and `Z := 1`.

This isolates the content of the anchor: the tails are free, and everything
substantive sits in the two analytic rows below. -/
theorem trivial_radius_factor_tails (M : GMCModel d) {R C CSigma A B : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (hCSigma : 0 ≤ CSigma) :
    (∀ _omega : PotentialSample d, R ≤ R ∧ (1 : ℝ) ≤ 1) ∧
    SubdiffusiveProcess.OGammaLE M.P.toMeasure 1 A
      (fun _omega : PotentialSample d ↦ Real.log (R / R) - C) ∧
    SubdiffusiveProcess.OGammaLE M.P.toMeasure 1 B
      (fun _omega : PotentialSample d ↦ Real.log (1 : ℝ) - CSigma) := by
  refine ⟨fun _ ↦ ⟨le_rfl, le_rfl⟩, ogammaLE_one_of_nonpos ?_,
    ogammaLE_one_of_nonpos ?_⟩
  · intro _omega
    rw [div_self hR.ne', Real.log_one]
    linarith
  · intro _omega
    rw [Real.log_one]
    linarith



def WholeSpaceRows (d : ℕ) (c C : ℝ) : Prop :=
  ∀ sigma : ℝ, sigma ∈ Set.Ioo (0 : ℝ) 1 →
    ∃ deltaSigma CSigma : ℝ,
      0 < deltaSigma ∧ 0 < CSigma ∧
      ∀ M : GMCModel d, M.delta ≤ deltaSigma →
      ∀ L : ℕ, ∀ t : ℝ, 0 < t → ∀ x0 : Vec d,
        let R := Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom M L * t)
        (3 : ℝ) ^ L ≤ R →
        ∃ Rstar Z : PotentialSample d → ℝ,
          (∀ omega, R ≤ Rstar omega ∧ 1 ≤ Z omega) ∧
          SubdiffusiveProcess.OGammaLE M.P.toMeasure 1
            (C * M.delta ^ 2 * |Real.log M.delta|)
            (fun omega ↦ Real.log (Rstar omega / R) - C) ∧
          SubdiffusiveProcess.OGammaLE M.P.toMeasure 1
            (CSigma * M.delta ^ 2 * |Real.log M.delta|)
            (fun omega ↦ Real.log (Z omega) - CSigma) ∧
          ∀ᵐ omega ∂M.P.toMeasure, ∀ f : Vec d → ℝ, MemLp f 2 volume →
            Function.support f ⊆ Metric.ball x0 R →
            ∀ u : WholeSpaceDivergenceResolventSolution
                (aCutoff M L omega) t f,
              (∀ r, Rstar omega ≤ r →
                ∫ x in (Metric.ball x0 r)ᶜ, u.toFun x ^ 2 ∂volume ≤
                  C * Real.exp (-c * r / R) * ∫ x, f x ^ 2 ∂volume) ∧
              (∃ fluxHat : Vec d → Fin d → ℂ,
                IsFourierRepresentative
                  (fun x ↦ (aCutoff M L omega x -
                    SubdiffusiveProcess.CoarseGrainingVocab.ahom M L) • u.grad x) fluxHat ∧
                massiveNegativeSobolevNormSq R sigma fluxHat ≤
                  CSigma * Z omega * SubdiffusiveProcess.CoarseGrainingVocab.ahom M L * t⁻¹ *
                    R ^ (2 * sigma) * ∫ x, f x ^ 2 ∂volume)



theorem whole_space_resolvent_estimates_of_rows {c C : ℝ}
    (hc : 0 < c) (hcC : c ≤ C) (hrows : WholeSpaceRows d c C) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
    ∀ sigma : ℝ, sigma ∈ Set.Ioo (0 : ℝ) 1 →
      ∃ deltaSigma CSigma : ℝ,
        0 < deltaSigma ∧ 0 < CSigma ∧
        ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ deltaSigma →
        ∀ L : ℕ, ∀ t : ℝ, 0 < t → ∀ x0 : Vec d,
          let R := Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom M L * t)
          (3 : ℝ) ^ L ≤ R →
          ∃ Rstar Z : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ,
            (∀ omega, R ≤ Rstar omega ∧ 1 ≤ Z omega) ∧
            SubdiffusiveProcess.OGammaLE M.P.toMeasure 1
              (C * M.delta ^ 2 * |Real.log M.delta|)
              (fun omega ↦ Real.log (Rstar omega / R) - C) ∧
            SubdiffusiveProcess.OGammaLE M.P.toMeasure 1
              (CSigma * M.delta ^ 2 * |Real.log M.delta|)
              (fun omega ↦ Real.log (Z omega) - CSigma) ∧
            ∀ᵐ omega ∂M.P.toMeasure, ∀ f, MemLp f 2 volume →
              Function.support f ⊆ Metric.ball x0 R →
              ∃ u : WholeSpaceDivergenceResolventSolution
                  (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) t f,
                (∀ v : WholeSpaceDivergenceResolventSolution
                    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) t f,
                  u.toFun =ᵐ[volume] v.toFun ∧ u.grad =ᵐ[volume] v.grad) ∧
                (∀ r, Rstar omega ≤ r →
                  ∫ x in (Metric.ball x0 r)ᶜ, u.toFun x ^ 2 ∂volume ≤
                    C * Real.exp (-c * r / R) * ∫ x, f x ^ 2 ∂volume) ∧
                let flux := fun x ↦
                  (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x -
                    SubdiffusiveProcess.CoarseGrainingVocab.ahom M L) • u.grad x
                ∃ fluxHat : Vec d → Fin d → ℂ,
                  IsFourierRepresentative flux fluxHat ∧
                  massiveNegativeSobolevNormSq R sigma fluxHat ≤
                    CSigma * Z omega * SubdiffusiveProcess.CoarseGrainingVocab.ahom M L * t⁻¹ *
                      R ^ (2 * sigma) * ∫ x, f x ^ 2 ∂volume := by
  refine ⟨c, C, hc, hcC, ?_⟩
  intro sigma hsigma
  obtain ⟨deltaSigma, CSigma, hdelta, hCSigma, hmain⟩ := hrows sigma hsigma
  refine ⟨deltaSigma, CSigma, hdelta, hCSigma, ?_⟩
  intro M hM L t ht x0 R hR
  haveI : NeZero d := ⟨by have := M.shellPrefix.dimension; omega⟩
  obtain ⟨Rstar, Z, hbase, htail1, htail2, hae⟩ := hmain M hM L t ht x0 hR
  refine ⟨Rstar, Z, hbase, htail1, htail2, ?_⟩
  filter_upwards [hae,
    ae_forall_exists_finiteCutoffWholeSpaceSolution M L ht x0] with
    omega hrow hsolve
  intro f hf hsupp
  obtain ⟨u, huniq, _, _⟩ := hsolve f hf
  obtain ⟨hext, hflux⟩ := hrow f hf hsupp u
  exact ⟨u, huniq, hext, hflux⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
