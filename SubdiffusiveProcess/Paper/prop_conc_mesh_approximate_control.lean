module

public import SubdiffusiveProcess.Paper.prop_conc_mesh_cutoff_family
public import SubdiffusiveProcess.Paper.mesh_interpolator
public import SubdiffusiveProcess.Geometry.TriadicApproximation
public import SubdiffusiveProcess.Sobolev.CubeUniformError
public import SubdiffusiveProcess.Sobolev.NativeBoundaryResponse

@[expose] public section

/-! Uniform energy bounds for harmonic mesh approximations on a fixed sequence.
The harmonic-cell estimates are explicit inputs; no random extraction is asserted. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff BigOperators
namespace SubdiffusiveProcess.Paper
noncomputable section

/-- Bounds for every harmonic cell provide bounded-energy approximation of each smooth source. -/
theorem prop_conc_mesh_approximate_control
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (a : ℕ → SpatialCoordinates d → ℝ) (ha : ∀ n, Continuous (a n))
    (hpos : ∀ n x, 0 < a n x)
    (aC : ℕ → PositiveCoefficient (centeredCube z r hr))
    (hAC : ∀ n, (aC n).val =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))] a n)
    (t alpha : ℝ)
    (hcell : aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr a t alpha) :
    ∀ phi : DomainL2 (centeredCube z r hr),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        (phi : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) →
      ∀ eps : ℝ, 0 < eps → ∃ w : ℕ → S.space, ∃ C : ℝ,
        (∀ n, responseForm S (aC n) (w n) (w n) ≤ C) ∧
        (∀ n, ‖(w n).val.1 - phi‖ ≤ eps) := by
  classical
  have dimensionNonzero : NeZero d := ⟨by omega⟩
  intro phi hphi eps heps
  obtain ⟨fc, hfc, hcompact, hsupp, hrep⟩ := hphi
  let V : ℝ := Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))
  have hV : 0 ≤ V := Real.sqrt_nonneg _
  have hden : 0 < V + 1 := by linarith only [hV]
  let eta : ℝ := eps / (V + 1)
  have heta : 0 < eta := div_pos heps hden
  obtain ⟨Cmesh, _hCmesh, hmesh⟩ := mesh_interpolator (d := d) hd
  let G : ℝ := sSup ((fun y => ‖fderiv ℝ fc y‖) ''
    closure (centeredCube z r hr : Set (SpatialCoordinates d)))
  obtain ⟨J, hside, herror⟩ := exists_triadic_side_error_lt r (Cmesh * G) eta heta
  let thetaH : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    H1Function.ofContDiff (centeredCube z r hr).isOpen (hfc.of_le (by norm_num)) hcompact
  choose E Gr Ho hE hGr hHo hbounds using hcell J hside fc hfc thetaH rfl
  have hex (n : ℕ) : ∃ w : H10Function (centeredCube z r hr : Set (SpatialCoordinates d)),
      energy (a n) (centeredCube z r hr : Set (SpatialCoordinates d)) w.toH1Function ≤
        ∑ k : OddGridIndex d (triadicHalf J), E k ∧
      (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
        |w.toH1Function.toFun x - fc x| < eta) := by
    obtain ⟨lam, Lam, hlam, hboundsQ⟩ := aux_lem_cutoffs_pos_bounds (a n) (ha n) (hpos n)
      (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
      (lane2_isCompact_closure_centeredCube z hr)
    obtain ⟨w, hwcont, hwcell, hwsum, hwerr⟩ := hmesh z r hr J (a n) lam Lam hlam (ha n)
      (fun x hx => hboundsQ x (subset_closure hx)) thetaH hfc hcompact hsupp
    refine ⟨w, ?_, ?_⟩
    · rw [hwsum]
      apply Finset.sum_le_sum
      intro k _hk
      rw [← (hwcell k).2.2]
      exact (hbounds k n _ (hwcell k).1 (hwcell k).2.1
        (hwcont.mono (closure_mono (oddGridCell_subset z hr (triadicHalf J) k)))).1
    · intro x hx
      refine (hwerr x hx).trans_lt ?_
      change Cmesh * (r / (3 : ℝ) ^ J) * G < eta
      nlinarith only [herror]
  choose w hwE hwerr using hex
  let v : ℕ → S.space := fun n =>
    ⟨sobolevDataOfH1 (w n).toH1Function, hS.symm ▸ sobolevDataOfH1_mem_killed (w n)⟩
  refine ⟨v, ∑ k : OddGridIndex d (triadicHalf J), E k, ?_, ?_⟩
  · intro n
    change sobolevCoefficientForm (aC n) (sobolevDataOfH1 (w n).toH1Function)
      (sobolevDataOfH1 (w n).toH1Function) ≤ _
    rw [← energy_eq_sobolevCoefficientForm (aC n) _ (hAC n) (w n).toH1Function]
    exact hwE n
  · intro n
    have hb := cube_norm_sub_le_of_uniform_error z hr (w n).toH1Function.toFun fc eta heta.le
      (fun x hx => (hwerr n x hx).le) (v n).val.1 phi
      (sobolevDataOfH1_fst_coeFn (w n).toH1Function) hrep
    refine hb.trans ?_
    change V * (eps / (V + 1)) ≤ eps
    rw [← mul_div_assoc, div_le_iff₀ hden]
    nlinarith only [heps]

end
end SubdiffusiveProcess.Paper
