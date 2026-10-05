module

public import SubdiffusiveProcess.Paper.neumann_ht_campanato
public import SubdiffusiveProcess.Paper.neumann_ht_rem_resolved
public import SubdiffusiveProcess.Paper.cor_neumann_source
public import SubdiffusiveProcess.Paper.rem_resolved_microscopic

@[expose] public section

/-! Unit-cube Hölder bound for the top-block-removed coefficient `A^{HT_j}_{N+j}`, `HT_j = -∑_{i<j} ω(-i)`.

The analogue of `cor_neumann_source` (Hölder half) for the coefficient with the `j` coarsest layers of
the cutoff removed: mean-zero Neumann solutions with a bounded source have a `C^α` representative on the
closed unit cube with norm at most `K_N ‖f‖_∞`, `K_N` of finite first moment uniformly in `N`.  The
smallness threshold `delta0` does not depend on `j` (nor on the model, the cutoff, the source); the random
constant and its moment bound depend on `j` only through prefactors.  Paper: `mfd:cor-neumann-source`
(`mfd:cor-neumann-source` and `mfd:lem-finite-source-comparison`), for the coefficient `A^{HT_j}` of the rescaled cube of side `3^j`
(`mfd:lem-finite-source-comparison`, last paragraph of its proof). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace Metric Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- **Unit-cube Hölder bound for the top-block-removed coefficient** (`H = HT_j`, cutoff `N + j`):
one threshold `delta0` before the model and `j`; the random constant of finite first moment, uniformly in
`N`, and its moment bound may depend on `j`. -/
theorem neumann_ht_unit_holder
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E)
    (X : in_extension d hd E) (W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Cp : CampanatoInput d) (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d model)
        (Sreg : in_6_16 d model) (_It : in_iteration d model E Sreg),
        model.delta ≤ delta0 → ∀ j : ℕ, 0 < j →
        ∃ (Kcor : ℕ → BilateralField d → ℝ) (Cbcor : ℝ),
          (∀ N, MemLp (Kcor N) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure) ∧
          (∀ N, eLpNorm (Kcor N) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤
            ENNReal.ofReal Cbcor) ∧
          ∀ᵐ om ∂(chaosSampleLaw model).toMeasure,
            ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
              AEMeasurable F
                (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
              (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
                |F x| ≤ Kf) →
              (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
              ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
                SolvesNeumann (cutoffPositiveCoefficient model (calib3_HT d j) om (N + j)
                  (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) F v →
                ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
                  IsHolderOn alpha
                    (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                      Set (SpatialCoordinates d)) U ∧
                  ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
                    =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U ∧
                  cAlphaNorm alpha
                    (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                      Set (SpatialCoordinates d)) U ≤ Kcor N om * Kf := by
  obtain ⟨delta0, hdelta0, hCa⟩ :=
    neumann_ht_campanato d hd E P X W D alpha 1 (fun _ => (1 : ℝ)) ha0 ha1
      (fun _ => le_rfl)
  refine ⟨delta0, hdelta0, ?_⟩
  intro model Rm Sreg It hδ j hj
  obtain ⟨Kc, Cc, hKc0, hKcL, hKcB, hCae⟩ := hCa model Rm Sreg It hδ j hj
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = max 1 ((2 + Real.sqrt d) * Cp.C alpha) := ⟨_, rfl⟩
  have hc1 : 1 ≤ c := hcdef ▸ le_max_left _ _
  have hc0 : 0 ≤ c := by linarith
  have hcC : (2 + Real.sqrt d) * Cp.C alpha ≤ c := hcdef ▸ le_max_right _ _
  refine ⟨fun N om => c * Kc N om, c * Cc 0, fun N => (hKcL 0 N).const_mul c, fun N => ?_, ?_⟩
  · have h := hKcB 0 N
    show eLpNorm (fun om => c * Kc N om) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤ _
    rw [aux_rem_resolved_microscopic_nonneg_scalar_eLpNorm _ _ c hc0]
    calc ENNReal.ofReal c * eLpNorm (Kc N) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure
        ≤ ENNReal.ofReal c * ENNReal.ofReal (Cc 0) := by gcongr
      _ = ENNReal.ofReal (c * Cc 0) := (ENNReal.ofReal_mul hc0).symm
  · filter_upwards [hCae] with om hC
    intro N F Kf hKf hFm hFb hmean v hsol
    obtain ⟨U, hUc, hUH, hUae, hUn⟩ := aux_cor_neumann_source_holder_of_campanato Cp ha0 ha1 v
      (hKc0 N om) hKf (hC N F Kf hKf hFm hFb hmean v hsol)
    refine ⟨U, hUc, hUH, hUae, hUn.trans ?_⟩
    have h1 : (2 + Real.sqrt d) * Cp.C alpha * Kc N om ≤ c * Kc N om :=
      mul_le_mul_of_nonneg_right hcC (hKc0 N om)
    exact mul_le_mul_of_nonneg_right h1 hKf

end SubdiffusiveProcess.Paper
