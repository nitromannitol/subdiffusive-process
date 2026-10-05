module

public import SubdiffusiveProcess.Paper.lem_as_regularity_finite_atom_bank

@[expose] public section

/-! The physical retained response catalogue is an explicit finite bank.
Its cardinality is at most a polynomial factor times a geometric factor in
the retained depth. No growing-mesh summability is claimed here.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators Topology
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The retained response catalogue has the required polynomial-geometric cardinality bound. -/
theorem aux_lem_as_regularity_retained_atom_tail_card (d H : ℕ) :
    (aux_prefix_rraw_G d H).card ≤ (H + 1) * (3 ^ (H + 1)) ^ d := by
  classical
  have hsub : (aux_prefix_rraw_G d H).card ≤
      (Finset.Icc 2 H).card * (aux_psf_Rindex d H).card := by
    unfold aux_prefix_rraw_G
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_product _ _)
  apply hsub.trans
  apply Nat.mul_le_mul
  · rw [Nat.card_Icc]
    omega
  · exact aux_prefix_rraw_Rindex_card_le d H

/-- Retained atoms at one physical score coordinate have one future cutoff and one finite-bank tail. -/
theorem lem_as_regularity_retained_atom_tail
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : in_responses d M) (Sreg : in_6_16 d M) (_It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ eps : ℝ, 0 < eps → ∃ C c : ℝ, ∃ N0 : ℕ, 0 < C ∧ 0 < c ∧
        ∀ (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d),
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            ∀ (N i : ℕ) (y : SpatialCoordinates d), eta N omega i y =
              omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
        ∀ (n : ℤ) (z : SpatialCoordinates d) (N K Hdepth : ℕ),
          N0 ≤ K → n + (Hdepth : ℤ) + (K : ℤ) ≤ (N : ℤ) →
          ∃ M0 : ℕ, N ≤ M0 ∧ ∀ N' : ℕ, M0 ≤ N' →
            (chaosSampleLaw M).toMeasure {omega | ∃ rk ∈ aux_prefix_rraw_G d Hdepth,
              eps * (1 + aux_prefix_rraw_atom M eta N (-n - rk.1)
                  (z + (3 : ℝ) ^ (-n - rk.1) • aux_prefix_rraw_kvec rk.2) omega) <
                |aux_prefix_rraw_atom M eta N (-n - rk.1)
                    (z + (3 : ℝ) ^ (-n - rk.1) • aux_prefix_rraw_kvec rk.2) omega -
                  aux_prefix_rraw_atom M eta N' (-n - rk.1)
                    (z + (3 : ℝ) ^ (-n - rk.1) • aux_prefix_rraw_kvec rk.2) omega|} ≤
              ENNReal.ofReal (((aux_prefix_rraw_G d Hdepth).card : ℝ) *
                (C * (3 : ℝ) ^ (-c * (K : ℝ)))) := by
  classical
  obtain ⟨delta0, hdelta0, hbank⟩ := lem_as_regularity_finite_atom_bank
    d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hH hdelta eps heps
  obtain ⟨C, c, N0, hC, hc, htail⟩ := hbank M Rm Sreg It H hH hdelta eps heps
  refine ⟨C, c, N0, hC, hc, ?_⟩
  intro eta hEta n z N K Hdepth hK0 hK
  let G := aux_prefix_rraw_G d Hdepth
  let idx : {rk // rk ∈ G} ≃ Fin G.card := G.equivFin
  let l : Fin G.card → ℤ := fun i => -n - (idx.symm i).val.1
  let y : Fin G.card → SpatialCoordinates d := fun i =>
    z + (3 : ℝ) ^ (l i) • aux_prefix_rraw_kvec (idx.symm i).val.2
  have hr (i : Fin G.card) : (idx.symm i).val.1 ≤ Hdepth :=
    (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp
      (idx.symm i).property).1).1).2
  obtain ⟨M0, hNM0, hM0⟩ := htail eta hEta G.card l y N K hK0
    (fun i => by dsimp only [l]; have := hr i; omega)
    (fun i => by dsimp only [l]; have := hr i; omega)
  refine ⟨M0, hNM0, fun N' hN' => (measure_mono ?_).trans (hM0 N' hN')⟩
  rintro omega ⟨rk, hrk, hbad⟩
  refine ⟨idx ⟨rk, hrk⟩, ?_⟩
  simpa only [l, y, Equiv.symm_apply_apply] using hbad

end SubdiffusiveProcess.Paper
