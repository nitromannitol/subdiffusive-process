module

public import SubdiffusiveProcess.CoarseGrainingVocab.Concentration.Statement

@[expose] public section




namespace SubdiffusiveProcess.Concentration

open MeasureTheory ProbabilityTheory Finset Real
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Simultaneous translation of both integer indices of a scale array. -/
def translateArray (X : ℤ → ℤ → Ω → ℝ) (m₀ : ℤ) : ℤ → ℤ → Ω → ℝ :=
  fun k j ω => X (k + m₀) (j + m₀) ω

omit [MeasurableSpace Ω] in
/-- Simultaneous translation preserves the geometrically weighted row sum. -/
lemma Yk_translateArray (X : ℤ → ℤ → Ω → ℝ) (m₀ k : ℤ) (s : ℝ) (ω : Ω) :
    Yk (translateArray X m₀) s k ω = Yk X s (k + m₀) ω := by
  unfold Yk translateArray
  rw [← (Equiv.addRight m₀).tsum_eq
    (fun j : ℤ => wt s (k + m₀) j * X (k + m₀) j ω)]
  apply tsum_congr
  intro j
  congr 1
  unfold wt idist
  congr 2
  have hadd : (Equiv.addRight m₀) j = j + m₀ := rfl
  rw [hadd]
  push_cast
  congr 1
  ring_nf

/-- Translation of a finite integer window, in the form used by the event. -/
lemma sum_Icc_translateArray (f : ℤ → ℝ) (m₀ : ℤ) (m : ℕ) :
    ∑ k ∈ Finset.Icc (0 : ℤ) (m : ℤ), f (k + m₀) =
      ∑ k ∈ Finset.Icc m₀ (m₀ + (m : ℤ)), f k := by
  classical
  calc
    ∑ k ∈ Finset.Icc (0 : ℤ) (m : ℤ), f (k + m₀) =
        ∑ k ∈ (Finset.Icc (0 : ℤ) (m : ℤ)).image (fun k => k + m₀), f k := by
          rw [Finset.sum_image]
          intro a _ b _ hab
          exact add_right_cancel hab
    _ = ∑ k ∈ Finset.Icc m₀ (m₀ + (m : ℤ)), f k := by
      rw [Finset.image_add_right_Icc]
      congr 2 <;> ring

/-- Residue-class column independence is invariant under simultaneous integer
translation of the row and column indices. -/
lemma columnsIndep_translateArray {P : Measure Ω} {X : ℤ → ℤ → Ω → ℝ} {r : ℕ}
    (hindep : ColumnsIndep P X r) (m₀ : ℤ) :
    ColumnsIndep P (translateArray X m₀) r := by
  intro b
  let shiftRows : (ℤ → ℝ) → (ℤ → ℝ) := fun f k => f (k + m₀)
  have hshift : Measurable shiftRows := by
    rw [measurable_pi_iff]
    intro k
    exact measurable_pi_apply (k + m₀)
  have h := (hindep (b + m₀)).comp (fun _ => shiftRows) (fun _ => hshift)
  apply h.congr
  intro j
  filter_upwards [] with ω
  funext k
  simp only [Function.comp_apply, shiftRows, translateArray]
  rw [show j * (r : ℤ) + b + m₀ = j * (r : ℤ) + (b + m₀) by ring]

/-- **Appendix B, Proposition `p.concentration.for.scales`**, with the fixed
universal constant exposed.  This is the source-exact translated-window form:
literal constants `6` and `16`, arbitrary `m₀ : ℤ`, and arbitrary `m : ℕ`.

`ColumnsIndep` records the exact residue-class mutual independence consequence
of the printed two-set `r`-dependence assumption that the proof consumes. -/
theorem concentration_for_scales_Cstar
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℤ → ℤ → Ω → ℝ)
    {p s : ℝ} {r : ℕ} (hp : 1 ≤ p) (hs : 0 < s) (hs1 : s ≤ 1)
    (hsp : 1 ≤ s * p) (hr : 1 ≤ r)
    (hXmeas : ∀ k j, Measurable (X k j))
    (hXnn : ∀ k j ω, 0 ≤ X k j ω)
    (hmomL : ∀ k j, ∫⁻ ω, ENNReal.ofReal ((X k j ω) ^ p) ∂P ≤ 1)
    (hindep : ColumnsIndep P X r) :
    ∀ (m₀ : ℤ) (m : ℕ) (θ : ℝ), 0 < θ → θ ≤ 1 →
      P {ω | θ < (1 / ((m : ℝ) + 1)) *
          ∑ k ∈ Finset.Icc m₀ (m₀ + (m : ℤ)),
            (if 6 * s⁻¹ * Cstar ^ (1 / p) * θ ^ (-1 / p) < Yk X s k ω
              then (1 : ℝ) else 0)}
        ≤ ENNReal.ofReal
          (Real.exp (-(s * p * θ) / (16 * (r : ℝ)) * ((m : ℝ) + 1))) := by
  classical
  intro m₀ m θ hθ0 hθ1
  have hbase := p_concentration_for_scales_Cstar P (translateArray X m₀)
    hp hs hs1 hsp hr
    (fun k j => hXmeas (k + m₀) (j + m₀))
    (fun k j ω => hXnn (k + m₀) (j + m₀) ω)
    (fun k j => hmomL (k + m₀) (j + m₀))
    (columnsIndep_translateArray hindep m₀) m θ hθ0 hθ1
  have hevent :
      {ω | θ < (1 / ((m : ℝ) + 1)) *
          ∑ k ∈ Finset.Icc m₀ (m₀ + (m : ℤ)),
            (if 6 * s⁻¹ * Cstar ^ (1 / p) * θ ^ (-1 / p) < Yk X s k ω
              then (1 : ℝ) else 0)} =
      {ω | θ < (1 / ((m : ℝ) + 1)) *
          ∑ k ∈ Finset.Icc (0 : ℤ) (m : ℤ),
            (if 6 * s⁻¹ * Cstar ^ (1 / p) * θ ^ (-1 / p) <
                Yk (translateArray X m₀) s k ω then (1 : ℝ) else 0)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [← sum_Icc_translateArray
      (fun k => if 6 * s⁻¹ * Cstar ^ (1 / p) * θ ^ (-1 / p) < Yk X s k ω
        then (1 : ℝ) else 0) m₀ m]
    simp only [Yk_translateArray]
  rw [hevent]
  exact hbase

/-- Existential-universal-constant form of the source proposition. -/
theorem concentration_for_scales
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℤ → ℤ → Ω → ℝ)
    {p s : ℝ} {r : ℕ} (hp : 1 ≤ p) (hs : 0 < s) (hs1 : s ≤ 1)
    (hsLower : 1 / p ≤ s) (hr : 1 ≤ r)
    (hXmeas : ∀ k j, Measurable (X k j))
    (hXnn : ∀ k j ω, 0 ≤ X k j ω)
    (hmomL : ∀ k j, ∫⁻ ω, ENNReal.ofReal ((X k j ω) ^ p) ∂P ≤ 1)
    (hindep : ColumnsIndep P X r) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m₀ : ℤ) (m : ℕ) (θ : ℝ), 0 < θ → θ ≤ 1 →
        P {ω | θ < (1 / ((m : ℝ) + 1)) *
            ∑ k ∈ Finset.Icc m₀ (m₀ + (m : ℤ)),
              (if 6 * s⁻¹ * C ^ (1 / p) * θ ^ (-1 / p) < Yk X s k ω
                then (1 : ℝ) else 0)}
          ≤ ENNReal.ofReal
            (Real.exp (-(s * p * θ) / (16 * (r : ℝ)) * ((m : ℝ) + 1))) := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hsp : 1 ≤ s * p := (div_le_iff₀ hp0).1 hsLower
  exact ⟨Cstar, Cstar_pos,
    concentration_for_scales_Cstar P X hp hs hs1 hsp hr hXmeas hXnn hmomL hindep⟩

end SubdiffusiveProcess.Concentration
