module

public import SubdiffusiveProcess.Paper.rem_bank_neumann_coercive_response_bound_uniform
public import SubdiffusiveProcess.Paper.lem_neumann_error

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Model-uniform instantiation of `lem_neumann_error` at a fixed `(rho, pvec)`, with
`Bcoerc = Bresponse` both taken from `rem_bank_neumann_coercive_response_bound_uniform`'s own
model-uniform `B` (order `4p`). Item (b1) of the `lem_neumann_15` assembly plan: `lem_neumann_error`'s `Bcoerc`/`Bresponse` are fixed before its own internal
`∀ M ∀ rho ∀ pvec`, which is consistent with using a `(rho,pvec)`-specific value here because the
resulting statement is only ever APPLIED at this SAME `(rho, pvec)` downstream (never required to
hold universally). -/
theorem g9_neumann_error_instantiation_uniform (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : _root_.SubdiffusiveProcess.Paper.in_J d) (P : _root_.SubdiffusiveProcess.Paper.in_poincare d hd E)
    (Sfi : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd) (p : ℝ) (hp : 1 ≤ p)
    (rho : ℝ → ℝ) (hrho : ContDiff ℝ ∞ rho) (hrho0 : ∀ v : ℝ, 0 ≤ rho v)
    (hrhos : ∀ v : ℝ, v ∉ Set.Ioo (1 : ℝ) 2 → rho v = 0) (hrhoi : (∫ v, rho v) = 1)
    (pvec : Fin d → ℝ) (hpvec : (∑ i : Fin d, (pvec i) ^ 2) = 1)
    (hPn : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph (unitNeumannCube d),
        ‖(w : SobolevData (unitNeumannCube d)).1‖ ≤
          K * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) w‖) :
    ∃ delta0 K Cerr Cunif : ℝ, 0 < delta0 ∧ 0 < K ∧ 0 < Cerr ∧ 0 < Cunif ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        let Pm0 : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
        let Sn : ResponseSpace (unitNeumannCube d) := meanZeroResponseSpace hPn
        let an : ℕ → BilateralField d → PositiveCoefficient (unitNeumannCube d) := fun N omega =>
            cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos
        let Lp : Sn.space →L[ℝ] ℝ :=
            (affineNeumannLoad pvec).comp (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))
        let yn : ℕ → BilateralField d → ℝ := fun N omega => inverseResponse Sn (an N omega) Lp
        ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
        ∀ fL2 : ℕ → BilateralField d → DomainL2 (unitNeumannCube d),
          (∀ N om, ((fL2 N om : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
              faceBump rho pvec eps)) →
        ∀ (N : ℕ) (_om : BilateralField d), eLpNorm (fun om' => yn N om' -
            inverseResponse Sn (an N om')
              ((sobolevVolumeLoad (fL2 N om')).comp Sn.space.subtypeL))
            (ENNReal.ofReal p) Pm0 ≤ ENNReal.ofReal (Cerr * eps ^ (1 / 4 : ℝ)) := by
  obtain ⟨delta0c, hdelta0c, B, hB0, hcoerc⟩ :=
    rem_bank_neumann_coercive_response_bound_uniform d hd E P Sfi p hp rho hrho hrho0 hrhos hrhoi
      pvec hpvec hPn
  obtain ⟨delta0e, Ke, Cerr, Cunif, hd0e, hKe, hCerre, hCunife, hmain⟩ :=
    lem_neumann_error d hd E P Sfi p hp B B hB0 hB0
  refine ⟨min 1 (min delta0c delta0e), Ke, Cerr, Cunif, ?_, hKe, hCerre, hCunife, ?_⟩
  · exact lt_min one_pos (lt_min hdelta0c hd0e)
  · intro M Rm H hIC hδ
    have hδc : M.delta ≤ min 1 delta0c :=
      le_min (hδ.trans (min_le_left _ _)) (hδ.trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hδe : M.delta ≤ delta0e := hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
    obtain ⟨Kcoerc, hKcoerc, hKmem, hKnorm⟩ := hcoerc M Rm H hIC hδc
    intro Pm0 Sn an Lp yn eps heps heps8 fL2 hfeq N om
    exact (hmain M Rm H hIC hδe rho hrho hrho0 hrhos hrhoi pvec hpvec hPn Kcoerc
      (fun N om => (hKcoerc N om).2) (fun N => (hKmem N).1) (fun N => (hKnorm N).1)
      (fun N => (hKmem N).2) (fun N => (hKnorm N).2) eps heps heps8 fL2 hfeq N om).2.1

end SubdiffusiveProcess.Paper
