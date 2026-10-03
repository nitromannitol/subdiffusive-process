module

public import SubdiffusiveProcess.Lane2.CellAssembly
public import SubdiffusiveProcess.Lane4.Carriers

@[expose] public section

/-! Transfer continuous native representatives and their Holder norms on closed cells.
These facts identify representatives only; they assert no coefficient estimates. -/

open MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess.Lane4

namespace SubdiffusiveProcess

/-- Continuous representatives equal almost everywhere on an open set agree on its closure. -/
theorem eqOn_closure_of_ae_eq_restrict
    {d : ℕ} {Q : Set (SpatialCoordinates d)} (hQ : IsOpen Q)
    {f g : SpatialCoordinates d → ℝ}
    (hf : ContinuousOn f (closure Q)) (hg : ContinuousOn g (closure Q))
    (hae : f =ᵐ[volume.restrict Q] g) : EqOn f g (closure Q) :=
  Set.EqOn.of_subset_closure
    (lane2_eqOn_of_ae_eq_of_continuousOn hQ (hf.mono subset_closure)
      (hg.mono subset_closure) hae) hf hg subset_closure Subset.rfl

/-- Holder difference-quotient sets depend only on the values on their domain. -/
theorem holderRatioSet_congr {d : ℕ} {alpha : ℝ} {Q : Set (SpatialCoordinates d)}
    {f g : SpatialCoordinates d → ℝ} (hfg : EqOn f g Q) :
    holderRatioSet alpha Q f = holderRatioSet alpha Q g := by
  ext v
  constructor
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    exact ⟨x, hx, y, hy, hxy, by rw [hfg hx, hfg hy]⟩
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    exact ⟨x, hx, y, hy, hxy, by rw [hfg hx, hfg hy]⟩

/-- Holder regularity transfers between representatives equal on the domain. -/
theorem isHolderOn_congr {d : ℕ} {alpha : ℝ} {Q : Set (SpatialCoordinates d)}
    {f g : SpatialCoordinates d → ℝ} (hfg : EqOn f g Q) :
    IsHolderOn alpha Q f ↔ IsHolderOn alpha Q g := by
  unfold IsHolderOn
  rw [holderRatioSet_congr hfg]

/-- The complete Holder norm transfers between representatives equal on the domain. -/
theorem cAlphaNorm_congr {d : ℕ} {alpha : ℝ} {Q : Set (SpatialCoordinates d)}
    {f g : SpatialCoordinates d → ℝ} (hfg : EqOn f g Q) :
    cAlphaNorm alpha Q f = cAlphaNorm alpha Q g := by
  have hsup : {v : ℝ | ∃ x ∈ Q, v = |f x|} = {v : ℝ | ∃ x ∈ Q, v = |g x|} := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, congrArg abs (hfg hx)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, congrArg abs (hfg hx).symm⟩
  unfold cAlphaNorm holderSeminorm
  rw [hsup, holderRatioSet_congr hfg]

end SubdiffusiveProcess
