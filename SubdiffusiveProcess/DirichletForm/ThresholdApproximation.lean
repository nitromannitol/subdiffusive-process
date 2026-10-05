module

public import SubdiffusiveProcess.DirichletForm.ThresholdCore

@[expose] public section

/-! Compactly supported form-domain approximations by soft thresholding.
A continuous representative close to a compactly supported test function
produces a core representative; existence of that domain element is not assumed here. -/

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.LimitFormCore
noncomputable section

/-- Soft thresholding a continuous domain representative close to a compact test gives a compact core approximation. -/
theorem compact_approximation_of_continuous_domain
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (F : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hNC : _root_.SubdiffusiveProcess.DirichletForm.HasNormalContractions F)
    (u : DomainL2 (centeredCube z r hr)) (hu : u ∈ F.toClosedForm.domain)
    (uc : SpatialCoordinates d → ℝ)
    (huc : ContinuousOn uc (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hurep : (u : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc)
    (phi : SpatialCoordinates d → ℝ) (hcompact : HasCompactSupport phi)
    (hsupp : tsupport phi ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (s : ℝ) (hs : 0 < s)
    (happrox : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
      |uc x - phi x| ≤ s / 2) :
    ∃ w ∈ F.toClosedForm.domain, ∃ g : SpatialCoordinates d → ℝ,
      Continuous g ∧ HasCompactSupport g ∧
      tsupport g ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      ((w : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] g) ∧
      ∀ x, |g x - phi x| ≤ 3 * s / 2 := by
  classical
  let Q := (centeredCube z r hr : Set (SpatialCoordinates d))
  let T : SpatialCoordinates d → ℝ := fun x => softThreshold s (uc x)
  have hT : ContinuousOn T (closure Q) := (continuous_softThreshold s).comp_continuousOn huc
  have hz : ∀ x ∈ closure Q, x ∉ tsupport phi → T x = 0 := by
    intro x hx hxphi
    have hphi : phi x = 0 := image_eq_zero_of_notMem_tsupport hxphi
    have hsmall := happrox x hx
    rw [hphi, sub_zero] at hsmall
    by_contra hne
    have hbig := softThreshold_ne_zero hne
    linarith only [hsmall, hbig, hs]
  let g : SpatialCoordinates d → ℝ := (closure Q).piecewise T 0
  have hg : Continuous g := by
    apply continuous_piecewise ?_ ?_ continuousOn_const
    · intro x hx
      have hxc : x ∈ closure Q := isClosed_closure.frontier_subset hx
      apply hz x hxc
      intro hxphi
      have hxi : x ∈ interior (closure Q) :=
        interior_maximal subset_closure (centeredCube z r hr).isOpen (hsupp hxphi)
      exact hx.2 hxi
    · simpa only [closure_closure] using hT
  have hsupport : Function.support g ⊆ tsupport phi := by
    intro x hx
    by_contra hxphi
    by_cases hxQ : x ∈ closure Q
    · exact hx (by dsimp only [g]; rw [Set.piecewise_eq_of_mem _ _ _ hxQ]; exact hz x hxQ hxphi)
    · exact hx (by dsimp only [g]; rw [Set.piecewise_eq_of_notMem _ _ _ hxQ]; rfl)
  have hgcompact : HasCompactSupport g :=
    HasCompactSupport.of_support_subset_isCompact hcompact hsupport
  have hgQ : tsupport g ⊆ Q := (closure_minimal hsupport (isClosed_tsupport phi)).trans hsupp
  have hmem : MemLp g 2 (volume.restrict Q) := hg.memLp_of_hasCompactSupport hgcompact
  let w : DomainL2 (centeredCube z r hr) := hmem.toLp g
  have hwrep : (w : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict Q] g := hmem.coeFn_toLp
  have hwT : (w : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict Q]
      fun x => softThreshold s (u x) := by
    filter_upwards [hwrep, hurep, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet]
      with x hw hu hx
    rw [hw, hu]
    dsimp only [g]
    rw [Set.piecewise_eq_of_mem _ _ _ (subset_closure hx)]
  obtain ⟨hwdom, _⟩ := hNC.operatesOn _ (softThreshold_isNormalContraction hs.le) u hu w hwT
  refine ⟨w, hwdom, g, hg, hgcompact, hgQ, hwrep, ?_⟩
  intro x
  by_cases hx : x ∈ closure Q
  · dsimp only [g]
    rw [Set.piecewise_eq_of_mem _ _ _ hx]
    have ht := softThreshold_sub_le hs.le (uc x)
    have ha := happrox x hx
    have htri := abs_sub_le (T x) (uc x) (phi x)
    linarith only [ht, ha, htri]
  · have hphi : phi x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (subset_closure (hsupp h)))
    dsimp only [g]
    rw [Set.piecewise_eq_of_notMem _ _ _ hx, hphi]
    simpa only [Pi.zero_apply, sub_self, abs_zero] using (by positivity : 0 ≤ 3 * s / 2)

end
end SubdiffusiveProcess.LimitFormCore
