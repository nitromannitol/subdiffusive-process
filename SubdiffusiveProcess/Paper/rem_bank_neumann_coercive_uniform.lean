module

public import SubdiffusiveProcess.Paper.lem_coercivity_uniform
public import SubdiffusiveProcess.Paper.rem_bank

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



def aux_rem_bank_neumann_coercive_uniform_D12 (delta0 : ℝ → ℝ) (p : ℝ) : ℝ :=
  delta0 (12 * max p (1 / 12 : ℝ))
def aux_rem_bank_neumann_coercive_uniform_B12 (Cbound : ℝ → ℝ) (p : ℝ) : ℝ :=
  Cbound (12 * max p (1 / 12 : ℝ))
def aux_rem_bank_neumann_coercive_uniform_D4 (delta0 : ℝ → ℝ) (q : ℝ) : ℝ :=
  delta0 (4 * max q (1 / 4 : ℝ))
def aux_rem_bank_neumann_coercive_uniform_B4 (Cbound : ℝ → ℝ) (q : ℝ) : ℝ :=
  Cbound (4 * max q (1 / 4 : ℝ))
def aux_rem_bank_neumann_coercive_uniform_D3 (delta0 : ℝ → ℝ) (p : ℝ) : ℝ :=
  delta0 (3 * max p (1 / 3 : ℝ))
def aux_rem_bank_neumann_coercive_uniform_B3 (Cbound : ℝ → ℝ) (p : ℝ) : ℝ :=
  Cbound (3 * max p (1 / 3 : ℝ))
def aux_rem_bank_neumann_coercive_uniform_Dq (delta0 : ℝ → ℝ) (q : ℝ) : ℝ :=
  delta0 (max q 1)
def aux_rem_bank_neumann_coercive_uniform_Bq (Cbound : ℝ → ℝ) (q : ℝ) : ℝ :=
  Cbound (max q 1)

theorem aux_rem_bank_neumann_coercive_uniform_D12_pos (delta0 : ℝ → ℝ)
    (hdelta0 : ∀ p, 1 ≤ p → 0 < delta0 p) (p : ℝ) :
    0 < aux_rem_bank_neumann_coercive_uniform_D12 delta0 p :=
  hdelta0 _ (by have := le_max_right p (1 / 12 : ℝ); nlinarith)
theorem aux_rem_bank_neumann_coercive_uniform_D4_pos (delta0 : ℝ → ℝ)
    (hdelta0 : ∀ p, 1 ≤ p → 0 < delta0 p) (q : ℝ) :
    0 < aux_rem_bank_neumann_coercive_uniform_D4 delta0 q :=
  hdelta0 _ (by have := le_max_right q (1 / 4 : ℝ); nlinarith)
theorem aux_rem_bank_neumann_coercive_uniform_D3_pos (delta0 : ℝ → ℝ)
    (hdelta0 : ∀ p, 1 ≤ p → 0 < delta0 p) (p : ℝ) :
    0 < aux_rem_bank_neumann_coercive_uniform_D3 delta0 p :=
  hdelta0 _ (by have := le_max_right p (1 / 3 : ℝ); nlinarith)
theorem aux_rem_bank_neumann_coercive_uniform_Dq_pos (delta0 : ℝ → ℝ)
    (hdelta0 : ∀ p, 1 ≤ p → 0 < delta0 p) (q : ℝ) :
    0 < aux_rem_bank_neumann_coercive_uniform_Dq delta0 q :=
  hdelta0 _ (le_max_right q 1)

/-- Small, isolated-context companions to the `B12/B4/B3/Bq` defs above: unfold the def and
simplify the inner `max` once `max _ _ = _` is already known, so that the caller (inside the huge
`aux_rem_bank_neumann_coercive_uniform_mloop` context below) never needs an `unfold`/`rw` tactic of
its own — only a cheap `.trans` application, avoiding pushing that declaration's elaboration over
the heartbeat budget. -/
theorem aux_rem_bank_neumann_coercive_uniform_B12_eq (Cbound : ℝ → ℝ) (p : ℝ)
    (h : max p (1 / 12 : ℝ) = p) :
    aux_rem_bank_neumann_coercive_uniform_B12 Cbound p = Cbound (12 * p) := by
  simp only [aux_rem_bank_neumann_coercive_uniform_B12, h]
theorem aux_rem_bank_neumann_coercive_uniform_B4_eq (Cbound : ℝ → ℝ) (q : ℝ)
    (h : max q (1 / 4 : ℝ) = q) :
    aux_rem_bank_neumann_coercive_uniform_B4 Cbound q = Cbound (4 * q) := by
  simp only [aux_rem_bank_neumann_coercive_uniform_B4, h]
theorem aux_rem_bank_neumann_coercive_uniform_B3_eq (Cbound : ℝ → ℝ) (p : ℝ)
    (h : max p (1 / 3 : ℝ) = p) :
    aux_rem_bank_neumann_coercive_uniform_B3 Cbound p = Cbound (3 * p) := by
  simp only [aux_rem_bank_neumann_coercive_uniform_B3, h]
theorem aux_rem_bank_neumann_coercive_uniform_Bq_eq (Cbound : ℝ → ℝ) (q : ℝ)
    (h : max q (1 : ℝ) = q) :
    aux_rem_bank_neumann_coercive_uniform_Bq Cbound q = Cbound q := by
  simp only [aux_rem_bank_neumann_coercive_uniform_Bq, h]



theorem aux_rem_bank_neumann_coercive_uniform_mloop (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (p q : ℝ) (hp2 : 2 ≤ p) (hpq : p < q)
    (rho : ℝ → ℝ) (pvec : Fin d → ℝ)
    (hPn : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph (unitNeumannCube d),
        ‖(w : SobolevData (unitNeumannCube d)).1‖ ≤
          K * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) w‖)
    (delta0 Cbound : ℝ → ℝ) (hdelta0 : ∀ p, 1 ≤ p → 0 < delta0 p)
    (h_coerc_inner : ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
      ∃ K : ℕ → BilateralField d → ℝ,
        (∀ (N : ℕ) (om : BilateralField d),
          (∀ v : killedSobolevGraph (unitNeumannCube d),
            cubeFractionalL2Seminorm hd (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
                (fun _ : Fin 1 => (v : SobolevData (unitNeumannCube d)).1) < ⊤ ∧
            cubeFractionalSqNorm hd (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
                (v : SobolevData (unitNeumannCube d)).1 ≤
              K N om * sobolevCoefficientForm (cutoffPositiveCoefficient (M) H om N
                  (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
                (v : SobolevData (unitNeumannCube d))
                (v : SobolevData (unitNeumannCube d))) ∧
          (∀ v : meanZeroSobolevGraph (unitNeumannCube d),
            cubeFractionalL2Seminorm hd (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
                (fun _ : Fin 1 => (v : SobolevData (unitNeumannCube d)).1) < ⊤ ∧
            cubeFractionalSqNorm hd (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
                (v : SobolevData (unitNeumannCube d)).1 ≤
              K N om * sobolevCoefficientForm (cutoffPositiveCoefficient (M) H om N
                  (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
                (v : SobolevData (unitNeumannCube d))
                (v : SobolevData (unitNeumannCube d)))) ∧
        (∀ p, 1 ≤ p → (M).delta ≤ delta0 p →
          ∀ N, MemLp (K N) (ENNReal.ofReal p) (chaosSampleLaw (M)).toMeasure ∧
            eLpNorm (K N) (ENNReal.ofReal p) (chaosSampleLaw (M)).toMeasure ≤
              ENNReal.ofReal (Cbound p)))
    (Cy : ℝ) (hCy0 : 0 ≤ Cy)
    (hCyb : ∀ (hP : ∃ Kp : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
        ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
          Kp * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖)
      (a : PositiveCoefficient (unitNeumannCube d)) (K : ℝ), 0 ≤ K →
      (∀ v : meanZeroSobolevGraph (unitNeumannCube d),
        cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
            (v : SobolevData (unitNeumannCube d)).1 ≤
          K * sobolevCoefficientForm a (v : SobolevData (unitNeumannCube d))
            (v : SobolevData (unitNeumannCube d))) →
      inverseResponse (meanZeroResponseSpace hP) a
          ((affineNeumannLoad pvec).comp
            (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))) ≤ Cy * K ∧
      ∀ eps : ℝ, 0 < eps → eps < 1 / 8 → ∀ fL2 : DomainL2 (unitNeumannCube d),
        ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
            faceBump rho pvec eps) →
        inverseResponse (meanZeroResponseSpace hP) a
            ((sobolevVolumeLoad fL2).comp (meanZeroResponseSpace hP).space.subtypeL) ≤ Cy * K)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hIC : InfraredCharacterization M H)
    (hδ_le : M.delta ≤ min 1 (min (min (aux_rem_bank_neumann_coercive_uniform_D12 delta0 p)
        (aux_rem_bank_neumann_coercive_uniform_D4 delta0 q))
      (min (aux_rem_bank_neumann_coercive_uniform_D3 delta0 p)
        (aux_rem_bank_neumann_coercive_uniform_Dq delta0 q)))) :
    let Pm0 : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
    let Sn : ResponseSpace (unitNeumannCube d) := meanZeroResponseSpace hPn
    let an : ℕ → BilateralField d → PositiveCoefficient (unitNeumannCube d) := fun N omega =>
        cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos
    let Lp : Sn.space →L[ℝ] ℝ :=
        (affineNeumannLoad pvec).comp (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))
    let yn : ℕ → BilateralField d → ℝ := fun N omega => inverseResponse Sn (an N omega) Lp
    ∃ Kcoerc : ℕ → BilateralField d → ℝ,
      (∀ N, ∀ omega, 0 ≤ Kcoerc N omega ∧
        (∀ v : meanZeroSobolevGraph (unitNeumannCube d),
            cubeFractionalSqNorm hd (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
                v.val.1 ≤
              Kcoerc N omega * sobolevCoefficientForm (an N omega) v.val v.val)) ∧
      (∀ N, MemLp (Kcoerc N) (ENNReal.ofReal (12 * p)) Pm0 ∧
            MemLp (yn N) (ENNReal.ofReal (12 * p)) Pm0 ∧
            MemLp (Kcoerc N) (ENNReal.ofReal (4 * q)) Pm0 ∧
            MemLp (yn N) (ENNReal.ofReal (4 * q)) Pm0) ∧
      (∀ N, eLpNorm (Kcoerc N) (ENNReal.ofReal (12 * p)) Pm0 +
            eLpNorm (yn N) (ENNReal.ofReal (12 * p)) Pm0 +
            eLpNorm (Kcoerc N) (ENNReal.ofReal (4 * q)) Pm0 +
            eLpNorm (yn N) (ENNReal.ofReal (4 * q)) Pm0 ≤
              ENNReal.ofReal ((max (aux_rem_bank_neumann_coercive_uniform_B12 Cbound p) 0 +
                  Cy * max (aux_rem_bank_neumann_coercive_uniform_B12 Cbound p) 0) +
                (max (aux_rem_bank_neumann_coercive_uniform_B4 Cbound q) 0 +
                  Cy * max (aux_rem_bank_neumann_coercive_uniform_B4 Cbound q) 0))) ∧
      (∀ eps : ℝ, 0 < eps → eps < 1 / 8 → ∀ fL2 : DomainL2 (unitNeumannCube d),
          ((fL2 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
            faceBump rho pvec eps) →
          let ys : ℕ → BilateralField d → ℝ :=
            fun N omega => inverseResponse Sn (an N omega)
              ((sobolevVolumeLoad fL2).comp Sn.space.subtypeL)
          ∀ N, MemLp (ys N) (ENNReal.ofReal (3 * p)) Pm0 ∧
               MemLp (ys N) (ENNReal.ofReal q) Pm0 ∧
               eLpNorm (ys N) (ENNReal.ofReal (3 * p)) Pm0 +
                 eLpNorm (ys N) (ENNReal.ofReal q) Pm0 ≤
                   ENNReal.ofReal (Cy * max (aux_rem_bank_neumann_coercive_uniform_B3 Cbound p) 0 +
                     Cy * max (aux_rem_bank_neumann_coercive_uniform_Bq Cbound q) 0)) := by
  intro Pm0 Sn an Lp yn
  obtain ⟨B12, hB12def⟩ : ∃ x : ℝ, x = aux_rem_bank_neumann_coercive_uniform_B12 Cbound p := ⟨_, rfl⟩
  obtain ⟨B4, hB4def⟩ : ∃ x : ℝ, x = aux_rem_bank_neumann_coercive_uniform_B4 Cbound q := ⟨_, rfl⟩
  obtain ⟨B3, hB3def⟩ : ∃ x : ℝ, x = aux_rem_bank_neumann_coercive_uniform_B3 Cbound p := ⟨_, rfl⟩
  obtain ⟨Bq, hBqdef⟩ : ∃ x : ℝ, x = aux_rem_bank_neumann_coercive_uniform_Bq Cbound q := ⟨_, rfl⟩
  have hA_1 : (1 : ℝ) ≤ 12 * max p (1 / 12 : ℝ) := by have := le_max_right p (1 / 12 : ℝ); nlinarith
  have hA_2 : (1 : ℝ) ≤ 4 * max q (1 / 4 : ℝ) := by have := le_max_right q (1 / 4 : ℝ); nlinarith
  have hA_3 : (1 : ℝ) ≤ 3 * max p (1 / 3 : ℝ) := by have := le_max_right p (1 / 3 : ℝ); nlinarith
  have hA_4 : (1 : ℝ) ≤ max q 1 := le_max_right q 1
  have h1 : M.delta ≤ 1 := hδ_le.trans (min_le_left (1:ℝ) _)
  have h2 := hδ_le.trans (min_le_right (1:ℝ) _)
  have hM12 : M.delta ≤ aux_rem_bank_neumann_coercive_uniform_D12 delta0 p :=
    h2.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hM4 : M.delta ≤ aux_rem_bank_neumann_coercive_uniform_D4 delta0 q :=
    h2.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hM3 : M.delta ≤ aux_rem_bank_neumann_coercive_uniform_D3 delta0 p :=
    h2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hMq : M.delta ≤ aux_rem_bank_neumann_coercive_uniform_Dq delta0 q :=
    h2.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨K, hK_coerc, hK_mom⟩ := h_coerc_inner M Rm H hIC
  have hcoerc : ∀ N omega, ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
      cubeFractionalSqNorm hd (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
          v.val.1 ≤
        |K N omega| * sobolevCoefficientForm (an N omega) v.val v.val := by
    intro N omega v
    exact (((hK_coerc N omega).2 v).2).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (sobolevCoefficientForm_nonneg _ _))
  have hK12 := hK_mom (12 * max p (1 / 12 : ℝ)) hA_1 hM12
  have hK4 := hK_mom (4 * max q (1 / 4 : ℝ)) hA_2 hM4
  have hK3 := hK_mom (3 * max p (1 / 3 : ℝ)) hA_3 hM3
  have hKq := hK_mom (max q 1) hA_4 hMq
  have hmax_p : max p (1 / 12 : ℝ) = p := max_eq_left (by nlinarith)
  have hmax_q : max q (1 / 4 : ℝ) = q := max_eq_left (by nlinarith)
  have hmax_p3 : max p (1 / 3 : ℝ) = p := max_eq_left (by nlinarith)
  have hmax_q1 : max q 1 = q := max_eq_left (by linarith)
  rw [hmax_p] at hK12; rw [hmax_q] at hK4; rw [hmax_p3] at hK3; rw [hmax_q1] at hKq
  have hB12eq : B12 = Cbound (12 * p) :=
    hB12def.trans (aux_rem_bank_neumann_coercive_uniform_B12_eq Cbound p hmax_p)
  have hB4eq : B4 = Cbound (4 * q) :=
    hB4def.trans (aux_rem_bank_neumann_coercive_uniform_B4_eq Cbound q hmax_q)
  have hB3eq : B3 = Cbound (3 * p) :=
    hB3def.trans (aux_rem_bank_neumann_coercive_uniform_B3_eq Cbound p hmax_p3)
  have hBqeq : Bq = Cbound q :=
    hBqdef.trans (aux_rem_bank_neumann_coercive_uniform_Bq_eq Cbound q hmax_q1)
  rw [← hB12eq] at hK12; rw [← hB4eq] at hK4; rw [← hB3eq] at hK3; rw [← hBqeq] at hKq
  let Kcoerc : ℕ → BilateralField d → ℝ := fun N omega => |K N omega|
  have hKcoerc0 : ∀ N omega, 0 ≤ Kcoerc N omega := fun N omega => abs_nonneg _
  have hynb : ∀ N omega, yn N omega ≤ Kcoerc N omega * Cy := by
    intro N omega
    exact (hCyb hPn (an N omega) |K N omega| (abs_nonneg _) (hcoerc N omega)).1.trans
      (le_of_eq (mul_comm Cy (|K N omega|)))
  have hKabs12 : ∀ N, MemLp (Kcoerc N) (ENNReal.ofReal (12 * p)) Pm0 ∧
      eLpNorm (Kcoerc N) (ENNReal.ofReal (12 * p)) Pm0 ≤ ENNReal.ofReal (max B12 0) := fun N =>
    ⟨(aux_rem_bank_abs_moment Pm0 (K N) (ENNReal.ofReal (12 * p)) B12 (hK12 N).1 (hK12 N).2).1,
      ((aux_rem_bank_abs_moment Pm0 (K N) (ENNReal.ofReal (12 * p)) B12 (hK12 N).1 (hK12 N).2).2).trans
        (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
  have hKabs4 : ∀ N, MemLp (Kcoerc N) (ENNReal.ofReal (4 * q)) Pm0 ∧
      eLpNorm (Kcoerc N) (ENNReal.ofReal (4 * q)) Pm0 ≤ ENNReal.ofReal (max B4 0) := fun N =>
    ⟨(aux_rem_bank_abs_moment Pm0 (K N) (ENNReal.ofReal (4 * q)) B4 (hK4 N).1 (hK4 N).2).1,
      ((aux_rem_bank_abs_moment Pm0 (K N) (ENNReal.ofReal (4 * q)) B4 (hK4 N).1 (hK4 N).2).2).trans
        (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
  have hKabs3 : ∀ N, MemLp (Kcoerc N) (ENNReal.ofReal (3 * p)) Pm0 ∧
      eLpNorm (Kcoerc N) (ENNReal.ofReal (3 * p)) Pm0 ≤ ENNReal.ofReal (max B3 0) := fun N =>
    ⟨(aux_rem_bank_abs_moment Pm0 (K N) (ENNReal.ofReal (3 * p)) B3 (hK3 N).1 (hK3 N).2).1,
      ((aux_rem_bank_abs_moment Pm0 (K N) (ENNReal.ofReal (3 * p)) B3 (hK3 N).1 (hK3 N).2).2).trans
        (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
  have hKabsq : ∀ N, MemLp (Kcoerc N) (ENNReal.ofReal q) Pm0 ∧
      eLpNorm (Kcoerc N) (ENNReal.ofReal q) Pm0 ≤ ENNReal.ofReal (max Bq 0) := fun N =>
    ⟨(aux_rem_bank_abs_moment Pm0 (K N) (ENNReal.ofReal q) Bq (hKq N).1 (hKq N).2).1,
      ((aux_rem_bank_abs_moment Pm0 (K N) (ENNReal.ofReal q) Bq (hKq N).1 (hKq N).2).2).trans
        (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
  have hyn_as : ∀ N, AEStronglyMeasurable (yn N) Pm0 := fun N =>
    (aux_rem_bank_response_moments_measurable_inverseResponse M H hIC.1 N
      (fun _ : Fin d => (1 / 2 : ℝ)) one_pos Sn Lp).aestronglyMeasurable
  have hyn12 : ∀ N, MemLp (yn N) (ENNReal.ofReal (12 * p)) Pm0 ∧
      eLpNorm (yn N) (ENNReal.ofReal (12 * p)) Pm0 ≤ ENNReal.ofReal (Cy * max B12 0) := fun N =>
    aux_rem_bank_response_moments_memLp_of_envelope Pm0 (yn N) (Kcoerc N) Cy (max B12 0)
      hCy0 (ENNReal.ofReal (12 * p)) (hyn_as N) (hKabs12 N).1 (hKabs12 N).2
      (Filter.Eventually.of_forall fun omega =>
        ⟨inverseResponse_nonneg Sn (an N omega) Lp, hKcoerc0 N omega, hynb N omega⟩)
  have hyn4 : ∀ N, MemLp (yn N) (ENNReal.ofReal (4 * q)) Pm0 ∧
      eLpNorm (yn N) (ENNReal.ofReal (4 * q)) Pm0 ≤ ENNReal.ofReal (Cy * max B4 0) := fun N =>
    aux_rem_bank_response_moments_memLp_of_envelope Pm0 (yn N) (Kcoerc N) Cy (max B4 0)
      hCy0 (ENNReal.ofReal (4 * q)) (hyn_as N) (hKabs4 N).1 (hKabs4 N).2
      (Filter.Eventually.of_forall fun omega =>
        ⟨inverseResponse_nonneg Sn (an N omega) Lp, hKcoerc0 N omega, hynb N omega⟩)
  refine ⟨Kcoerc, fun N omega => ⟨abs_nonneg _, fun v => hcoerc N omega v⟩,
    fun N => ⟨(hKabs12 N).1, (hyn12 N).1, (hKabs4 N).1, (hyn4 N).1⟩, ?_, ?_⟩
  · rw [← hB12def, ← hB4def]
    intro N
    have hA12 : (0:ℝ) ≤ max B12 0 := le_max_right _ _
    have hA4 : (0:ℝ) ≤ max B4 0 := le_max_right _ _
    have h12' : eLpNorm (Kcoerc N) (ENNReal.ofReal (12 * p)) Pm0 + eLpNorm (yn N) (ENNReal.ofReal (12 * p)) Pm0
        ≤ ENNReal.ofReal (max B12 0 + Cy * max B12 0) :=
      (add_le_add (hKabs12 N).2 (hyn12 N).2).trans (le_of_eq (ENNReal.ofReal_add hA12 (mul_nonneg hCy0 hA12)).symm)
    have h34' : eLpNorm (Kcoerc N) (ENNReal.ofReal (4 * q)) Pm0 + eLpNorm (yn N) (ENNReal.ofReal (4 * q)) Pm0
        ≤ ENNReal.ofReal (max B4 0 + Cy * max B4 0) :=
      (add_le_add (hKabs4 N).2 (hyn4 N).2).trans (le_of_eq (ENNReal.ofReal_add hA4 (mul_nonneg hCy0 hA4)).symm)
    calc eLpNorm (Kcoerc N) (ENNReal.ofReal (12 * p)) Pm0 + eLpNorm (yn N) (ENNReal.ofReal (12 * p)) Pm0
          + eLpNorm (Kcoerc N) (ENNReal.ofReal (4 * q)) Pm0 + eLpNorm (yn N) (ENNReal.ofReal (4 * q)) Pm0
        = (eLpNorm (Kcoerc N) (ENNReal.ofReal (12 * p)) Pm0 + eLpNorm (yn N) (ENNReal.ofReal (12 * p)) Pm0)
          + (eLpNorm (Kcoerc N) (ENNReal.ofReal (4 * q)) Pm0 + eLpNorm (yn N) (ENNReal.ofReal (4 * q)) Pm0) := by
            rw [add_assoc]
      _ ≤ ENNReal.ofReal (max B12 0 + Cy * max B12 0) + ENNReal.ofReal (max B4 0 + Cy * max B4 0) :=
            add_le_add h12' h34'
      _ = ENNReal.ofReal ((max B12 0 + Cy * max B12 0) + (max B4 0 + Cy * max B4 0)) :=
            (ENNReal.ofReal_add (add_nonneg hA12 (mul_nonneg hCy0 hA12)) (add_nonneg hA4 (mul_nonneg hCy0 hA4))).symm
  · rw [← hB3def, ← hBqdef]
    intro eps heps heps8 fL2 hfL2 ys N
    have hA3 : (0:ℝ) ≤ max B3 0 := le_max_right _ _
    have hAq : (0:ℝ) ≤ max Bq 0 := le_max_right _ _
    have hysb : ∀ omega, ys N omega ≤ Kcoerc N omega * Cy := by
      intro omega
      exact ((hCyb hPn (an N omega) |K N omega| (abs_nonneg _) (hcoerc N omega)).2 eps heps heps8 fL2 hfL2).trans
        (le_of_eq (mul_comm Cy (|K N omega|)))
    have hys_as : AEStronglyMeasurable (ys N) Pm0 :=
      (aux_rem_bank_response_moments_measurable_inverseResponse M H hIC.1 N
        (fun _ : Fin d => (1 / 2 : ℝ)) one_pos Sn
        ((sobolevVolumeLoad fL2).comp Sn.space.subtypeL)).aestronglyMeasurable
    have hys3 := aux_rem_bank_response_moments_memLp_of_envelope Pm0 (ys N) (Kcoerc N) Cy (max B3 0)
      hCy0 (ENNReal.ofReal (3 * p)) hys_as (hKabs3 N).1 (hKabs3 N).2
      (Filter.Eventually.of_forall fun omega =>
        ⟨inverseResponse_nonneg Sn (an N omega) ((sobolevVolumeLoad fL2).comp Sn.space.subtypeL),
          hKcoerc0 N omega, hysb omega⟩)
    have hysq := aux_rem_bank_response_moments_memLp_of_envelope Pm0 (ys N) (Kcoerc N) Cy (max Bq 0)
      hCy0 (ENNReal.ofReal q) hys_as (hKabsq N).1 (hKabsq N).2
      (Filter.Eventually.of_forall fun omega =>
        ⟨inverseResponse_nonneg Sn (an N omega) ((sobolevVolumeLoad fL2).comp Sn.space.subtypeL),
          hKcoerc0 N omega, hysb omega⟩)
    exact ⟨hys3.1, hysq.1,
      (add_le_add hys3.2 hysq.2).trans
        (le_of_eq (ENNReal.ofReal_add (mul_nonneg hCy0 hA3) (mul_nonneg hCy0 hAq)).symm)⟩



theorem rem_bank_neumann_coercive_uniform (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : Paper.in_J d) (P : Paper.in_poincare d hd E)
    (Sfi : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd) (p q : ℝ)
    (hp2 : 2 ≤ p) (hpq : p < q)
    (rho : ℝ → ℝ) (hrho : ContDiff ℝ ∞ rho) (hrho0 : ∀ v : ℝ, 0 ≤ rho v)
    (hrhos : ∀ v : ℝ, v ∉ Set.Ioo (1 : ℝ) 2 → rho v = 0) (hrhoi : (∫ v, rho v) = 1)
    (pvec : Fin d → ℝ) (hpvec : (∑ i : Fin d, (pvec i) ^ 2) = 1)
    (hPn : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph (unitNeumannCube d),
        ‖(w : SobolevData (unitNeumannCube d)).1‖ ≤
          K * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) w‖) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∃ B9 Bsm : ℝ, 0 ≤ B9 ∧ 0 ≤ Bsm ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ min 1 delta0 →
        let Pm0 : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
        let Sn : ResponseSpace (unitNeumannCube d) := meanZeroResponseSpace hPn
        let an : ℕ → BilateralField d → PositiveCoefficient (unitNeumannCube d) := fun N omega =>
            cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos
        let Lp : Sn.space →L[ℝ] ℝ :=
            (affineNeumannLoad pvec).comp (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))
        let yn : ℕ → BilateralField d → ℝ := fun N omega => inverseResponse Sn (an N omega) Lp
        ∃ Kcoerc : ℕ → BilateralField d → ℝ,
          (∀ N, ∀ omega, 0 ≤ Kcoerc N omega ∧
            (∀ v : meanZeroSobolevGraph (unitNeumannCube d),
                cubeFractionalSqNorm hd (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
                    v.val.1 ≤
                  Kcoerc N omega * sobolevCoefficientForm (an N omega) v.val v.val)) ∧
          (∀ N, MemLp (Kcoerc N) (ENNReal.ofReal (12 * p)) Pm0 ∧
                MemLp (yn N) (ENNReal.ofReal (12 * p)) Pm0 ∧
                MemLp (Kcoerc N) (ENNReal.ofReal (4 * q)) Pm0 ∧
                MemLp (yn N) (ENNReal.ofReal (4 * q)) Pm0) ∧
          (∀ N, eLpNorm (Kcoerc N) (ENNReal.ofReal (12 * p)) Pm0 +
                eLpNorm (yn N) (ENNReal.ofReal (12 * p)) Pm0 +
                eLpNorm (Kcoerc N) (ENNReal.ofReal (4 * q)) Pm0 +
                eLpNorm (yn N) (ENNReal.ofReal (4 * q)) Pm0 ≤
                  ENNReal.ofReal B9) ∧
          (∀ eps : ℝ, 0 < eps → eps < 1 / 8 → ∀ fL2 : DomainL2 (unitNeumannCube d),
              ((fL2 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
                faceBump rho pvec eps) →
              let ys : ℕ → BilateralField d → ℝ :=
                fun N omega => inverseResponse Sn (an N omega)
                  ((sobolevVolumeLoad fL2).comp Sn.space.subtypeL)
              ∀ N, MemLp (ys N) (ENNReal.ofReal (3 * p)) Pm0 ∧
                   MemLp (ys N) (ENNReal.ofReal q) Pm0 ∧
                   eLpNorm (ys N) (ENNReal.ofReal (3 * p)) Pm0 +
                     eLpNorm (ys N) (ENNReal.ofReal q) Pm0 ≤
                       ENNReal.ofReal Bsm) := by
  obtain ⟨delta0, hdelta0, Cbound, hCbound, h_coerc_inner⟩ :=
    lem_coercivity_uniform d hd E P Sfi (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos le_rfl
  obtain ⟨Cy, hCy0, hCyb⟩ :=
    aux_rem_bank_unit_neumann_response_le_coerc d hd Sfi rho hrho hrho0 hrhos hrhoi pvec hpvec
  have hA_1 : (1 : ℝ) ≤ 12 * max p (1 / 12 : ℝ) := by have := le_max_right p (1 / 12 : ℝ); nlinarith
  have hA_2 : (1 : ℝ) ≤ 4 * max q (1 / 4 : ℝ) := by have := le_max_right q (1 / 4 : ℝ); nlinarith
  have hA_3 : (1 : ℝ) ≤ 3 * max p (1 / 3 : ℝ) := by have := le_max_right p (1 / 3 : ℝ); nlinarith
  have hA_4 : (1 : ℝ) ≤ max q 1 := le_max_right q 1
  refine ⟨min (min (aux_rem_bank_neumann_coercive_uniform_D12 delta0 p)
        (aux_rem_bank_neumann_coercive_uniform_D4 delta0 q))
      (min (aux_rem_bank_neumann_coercive_uniform_D3 delta0 p)
        (aux_rem_bank_neumann_coercive_uniform_Dq delta0 q)),
    lt_min (lt_min (aux_rem_bank_neumann_coercive_uniform_D12_pos delta0 hdelta0 p)
        (aux_rem_bank_neumann_coercive_uniform_D4_pos delta0 hdelta0 q))
      (lt_min (aux_rem_bank_neumann_coercive_uniform_D3_pos delta0 hdelta0 p)
        (aux_rem_bank_neumann_coercive_uniform_Dq_pos delta0 hdelta0 q)),
    (max (aux_rem_bank_neumann_coercive_uniform_B12 Cbound p) 0 +
        Cy * max (aux_rem_bank_neumann_coercive_uniform_B12 Cbound p) 0) +
      (max (aux_rem_bank_neumann_coercive_uniform_B4 Cbound q) 0 +
        Cy * max (aux_rem_bank_neumann_coercive_uniform_B4 Cbound q) 0),
    Cy * max (aux_rem_bank_neumann_coercive_uniform_B3 Cbound p) 0 +
      Cy * max (aux_rem_bank_neumann_coercive_uniform_Bq Cbound q) 0, ?_, ?_, ?_⟩
  · have hA12 : (0:ℝ) ≤ max (aux_rem_bank_neumann_coercive_uniform_B12 Cbound p) 0 := le_max_right _ _
    have hA4 : (0:ℝ) ≤ max (aux_rem_bank_neumann_coercive_uniform_B4 Cbound q) 0 := le_max_right _ _
    exact add_nonneg (add_nonneg hA12 (mul_nonneg hCy0 hA12)) (add_nonneg hA4 (mul_nonneg hCy0 hA4))
  · have hA3 : (0:ℝ) ≤ max (aux_rem_bank_neumann_coercive_uniform_B3 Cbound p) 0 := le_max_right _ _
    have hAq : (0:ℝ) ≤ max (aux_rem_bank_neumann_coercive_uniform_Bq Cbound q) 0 := le_max_right _ _
    exact add_nonneg (mul_nonneg hCy0 hA3) (mul_nonneg hCy0 hAq)
  intro M Rm H hIC hδ_le
  exact aux_rem_bank_neumann_coercive_uniform_mloop d hd p q hp2 hpq rho pvec hPn delta0 Cbound
    hdelta0 h_coerc_inner Cy hCy0 hCyb M Rm H hIC hδ_le

end Paper
