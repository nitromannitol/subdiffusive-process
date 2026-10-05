module

public import SubdiffusiveProcess.Paper.prop_conc_countable_native_growth
public import SubdiffusiveProcess.Paper.mesh_interpolator
public import SubdiffusiveProcess.Sobolev.NativeCellGrowth

@[expose] public section

/-! Actual harmonic meshes with bounded energy and cell Holder norms.
One further cutoff subsequence works for every triadic mesh and smooth datum.
This module does not pass the meshes into a limiting form. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff BigOperators
namespace SubdiffusiveProcess.Paper
noncomputable section

/-- The actual harmonic meshes have a common-subsequence energy bound and bounded Holder norms on their cells. -/
theorem prop_conc_mesh_bounded_holder
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) :
    ∃ delta0 Cmesh : ℝ, 0 < delta0 ∧ 0 ≤ Cmesh ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (N : ℕ → ℕ),
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∃ seq : ℕ → ℕ, StrictMono seq ∧
      ∀ J : ℕ, r / (3 : ℝ) ^ J ≤ 1 →
      ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ phi →
        HasCompactSupport phi → tsupport phi ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∃ w : ℕ → H10Function (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∃ Ebound Hbound : ℝ, 0 ≤ Ebound ∧ 0 ≤ Hbound ∧ ∀ n,
        energy (cutoffCoefficient M H om (N (seq n)))
          (centeredCube z r hr : Set (SpatialCoordinates d)) (w n).toH1Function ≤ Ebound ∧
        ContinuousOn (w n).toH1Function.toFun
          (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        (∀ k : OddGridIndex d (triadicHalf J),
          IsHolderOn (3 / 4) (closure (oddGridCell z r hr (triadicHalf J) k :
            Set (SpatialCoordinates d))) (w n).toH1Function.toFun ∧
          cAlphaNorm (3 / 4) (closure (oddGridCell z r hr (triadicHalf J) k :
            Set (SpatialCoordinates d))) (w n).toH1Function.toFun ≤ Hbound) ∧
        ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
          |(w n).toH1Function.toFun x - phi x| ≤ Cmesh * (r / (3 : ℝ) ^ J) *
            sSup ((fun y => ‖fderiv ℝ phi y‖) ''
              closure (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  classical
  have dimensionNonzero : NeZero d := ⟨by omega⟩
  obtain ⟨delta0, hdelta0, hs⟩ := prop_conc_countable_native_growth d hd I Pin X W Cp Sob
    ((d : ℝ) - 1 / 2) (3 / 4) (by linarith only []) (by linarith only [])
    (by norm_num) (by norm_num)
  obtain ⟨Cmesh, hCmesh, hmesh⟩ := mesh_interpolator (d := d) hd
  refine ⟨delta0, Cmesh, hdelta0, hCmesh, ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr N
  let Idx := (J : ℕ) × OddGridIndex d (triadicHalf J)
  let cz : Idx → SpatialCoordinates d := fun i => oddGridCenter z r (triadicHalf i.1) i.2
  let cr : Idx → ℝ := fun i => r / (2 * (triadicHalf i.1 : ℝ) + 1)
  have chr : ∀ i, 0 < cr i := fun _ => div_pos hr (by positivity)
  filter_upwards [hs M Rm Sreg It H hIR hdelta Idx cz cr chr N] with om hom
  obtain ⟨seq, hseq, hcells⟩ := hom
  refine ⟨seq, hseq, ?_⟩
  intro J hside phi hphi hcompact hsupp
  choose K hK hbound using fun k : OddGridIndex d (triadicHalf J) => hcells ⟨J, k⟩
  let beta : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    H1Function.ofContDiff (centeredCube z r hr).isOpen (hphi.of_le (by norm_num)) hcompact
  choose lam Lam hlam hb using fun n => cutoffCoefficient_closedCube_bounds M H om (N (seq n)) z hr
  have hex (n : ℕ) :=
    hmesh z r hr J (cutoffCoefficient M H om (N (seq n))) (lam n) (Lam n) (hlam n)
      (cutoffCoefficient_continuous M H om (N (seq n)))
      (fun x hx => hb n x (centeredCube_subset_closedCube z hr hx)) beta hphi hcompact hsupp
  choose w hwcont hwcell hwsum hwerr using hex
  let Cphi : OddGridIndex d (triadicHalf J) → ℝ := fun k =>
    c2Norm (closedCube (cz ⟨J, k⟩) (cr ⟨J, k⟩) (chr ⟨J, k⟩) : Set (SpatialCoordinates d)) phi
  have hCphi : ∀ k, 0 ≤ Cphi k := fun k => aux_prop_growth_c2Norm_nonneg _ phi
  have hdata (k : OddGridIndex d (triadicHalf J)) (n : ℕ) :=
    hbound k n phi (hphi.of_le (WithTop.coe_le_coe.mpr le_top))
      (beta.restrict (oddGridCell z r hr (triadicHalf J) k).isOpen
        (oddGridCell_subset z hr (triadicHalf J) k))
      ((w n).toH1Function.restrict (oddGridCell z r hr (triadicHalf J) k).isOpen
        (oddGridCell_subset z hr (triadicHalf J) k))
      (Filter.Eventually.of_forall fun _ => rfl) (hwcell n k).2.1 (hwcell n k).2.2.le
      ((hwcont n).mono (closure_oddGridCell_subset z hr (triadicHalf J) k))
  refine ⟨w, ∑ k, K k * (Cphi k) ^ 2, ∑ k, K k * Cphi k,
    Finset.sum_nonneg (fun k _ => mul_nonneg (hK k) (sq_nonneg _)),
    Finset.sum_nonneg (fun k _ => mul_nonneg (hK k) (hCphi k)), ?_⟩
  intro n
  refine ⟨?_, hwcont n, ?_, hwerr n⟩
  · rw [hwsum n]
    apply Finset.sum_le_sum
    intro k _
    rw [← (hwcell n k).2.2]
    have hc := (cutoffPositiveCoefficient_representative M H om (N (seq n))
      (cz ⟨J, k⟩) (chr ⟨J, k⟩)).2.2.2
    apply native_energy_le_of_unit_growth (cz ⟨J, k⟩) (chr ⟨J, k⟩)
      ((cell_side_eq r J).le.trans hside) _ _ hc
    simpa only [Real.one_rpow, mul_one] using! (hdata k n).2.2 (cz ⟨J, k⟩) 1
      (Metric.mem_ball_self (half_pos (chr ⟨J, k⟩))) zero_lt_one le_rfl
  · intro k
    have hclosure : closure (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d)) =
        (closedCube (cz ⟨J, k⟩) (cr ⟨J, k⟩) (chr ⟨J, k⟩) : Set (SpatialCoordinates d)) :=
      aux_prop_conc_form_cutoff_continuity_closure_cube _ _ _
    rw [hclosure]
    exact ⟨(hdata k n).1, (hdata k n).2.1.trans
      (Finset.single_le_sum (fun i _ => mul_nonneg (hK i) (hCphi i)) (Finset.mem_univ k))⟩

end
end SubdiffusiveProcess.Paper
