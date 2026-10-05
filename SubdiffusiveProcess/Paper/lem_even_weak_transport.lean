module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.BoundaryEnergy
public import SubdiffusiveProcess.Sobolev.ReflectionObjectives
public import SubdiffusiveProcess.VariationalResponses.DivLoad
public import SubdiffusiveProcess.Paper.lem_even_fold_construction
@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity

noncomputable section
namespace SubdiffusiveProcess.Paper

lemma aux_lem_even_weak_transport_foldedCube_bounded
    (d : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (I P : Finset (Fin d)) :
    Bornology.IsBounded (foldedCube w r hr I P : Set (SpatialCoordinates d)) := by
  rw [foldedCube]
  apply Bornology.IsBounded.pi
  intro j
  by_cases hj : j ∈ I
  · by_cases hjP : j ∈ P
    · simpa [hj, hjP] using!
        (Metric.isBounded_Ioo (w j - r / 2) (w j + 3 * r / 2))
    · simpa [hj, hjP] using!
        (Metric.isBounded_Ioo (w j - 3 * r / 2) (w j + r / 2))
  · simpa [hj] using! (Metric.isBounded_Ioo (w j - r / 2) (w j + r / 2))

lemma aux_lem_even_weak_transport_form_congr
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a₁ a₂ : PositiveCoefficient Ω)
    (ha : ((a₁.val : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (Ω : Set (SpatialCoordinates d))]
      (a₂.val : SpatialCoordinates d → ℝ)))
    (u₁ u₂ : SobolevData Ω)
    (hu : ∀ j : Fin d, ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      (u₁.2 j : SpatialCoordinates d → ℝ) x = (u₂.2 j : SpatialCoordinates d → ℝ) x)
    (ψ : SobolevData Ω) :
    sobolevCoefficientForm a₁ u₁ ψ = sobolevCoefficientForm a₂ u₂ ψ := by
  rw [sobolevCoefficientForm_apply, sobolevCoefficientForm_apply]
  apply Finset.sum_congr rfl
  intro j hj
  apply integral_congr_ae
  filter_upwards [ha, hu j] with x hax hux
  rw [hax, hux]

lemma aux_lem_even_weak_transport_source
    {d : ℕ} (D : SubdiffusiveProcess.EvenReflectionDomain d)
    (G H : SpatialCoordinates d → ℝ)
    (hΩ : ∀ᵐ x ∂volume.restrict (D.Ω : Set (SpatialCoordinates d)),
      H x = G x)
    (hR : ∀ᵐ x ∂volume.restrict (D.reflected : Set (SpatialCoordinates d)),
      H x = G (coordinateReflection D.z {D.i} x))
    (ψ : SobolevData D.U)
    (hIntΩ : IntegrableOn (fun x => H x * ψ.1 x) (D.Ω : Set (SpatialCoordinates d)))
    (hIntR : IntegrableOn (fun x => H x * ψ.1 x)
      (D.reflected : Set (SpatialCoordinates d))) :
    (∫ x in (D.Ω : Set (SpatialCoordinates d)),
        G x * (sobolevDataRestrict D.Ω_le ψ).1 x) +
      (∫ x in (D.Ω : Set (SpatialCoordinates d)),
        G x * (D.reflectedRestrict ψ).1 x) =
      ∫ x in (D.U : Set (SpatialCoordinates d)), H x * ψ.1 x := by
  have hrestrict : ∀ᵐ x ∂volume.restrict (D.Ω : Set (SpatialCoordinates d)),
      (sobolevDataRestrict D.Ω_le ψ).1 x = ψ.1 x :=
    domainLpRestrict_coeFn D.Ω_le ψ.1
  have eΩ : (∫ x in (D.Ω : Set (SpatialCoordinates d)),
        G x * (sobolevDataRestrict D.Ω_le ψ).1 x) =
      ∫ x in (D.Ω : Set (SpatialCoordinates d)), H x * ψ.1 x := by
    apply integral_congr_ae
    filter_upwards [hΩ, hrestrict] with x hx hψ
    rw [hx, hψ]
  have eR : (∫ x in (D.Ω : Set (SpatialCoordinates d)),
        G x * (D.reflectedRestrict ψ).1 x) =
      ∫ x in (D.reflected : Set (SpatialCoordinates d)), H x * ψ.1 x := by
    change (∫ x in (D.Ω : Set (SpatialCoordinates d)),
      G x * reflectionLp D.z {D.i} D.preimage_reflected
        (domainLpRestrict D.reflected_le ψ.1) x) = _
    rw [integral_mul_reflectionLp D.z {D.i} D.preimage_reflected G
      (domainLpRestrict D.reflected_le ψ.1)]
    apply integral_congr_ae
    filter_upwards [hR, domainLpRestrict_coeFn D.reflected_le ψ.1] with x hx hψ
    rw [hx, hψ]
  rw [eΩ, eR]
  rw [← setIntegral_union D.disjoint_Ω_reflected D.reflected.isOpen.measurableSet
    hIntΩ hIntR]
  exact setIntegral_congr_set D.union_ae_eq

lemma aux_lem_even_weak_transport_piecewise_regular
    {d : ℕ} (D : SubdiffusiveProcess.EvenReflectionDomain d)
    (G H : SpatialCoordinates d → ℝ) (M : ℝ)
    (hG : AEMeasurable G
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))))
    (hGbd : ∀ᵐ x ∂volume.restrict (D.Ω : Set (SpatialCoordinates d)),
      |G x| ≤ M)
    (_hΩ : ∀ᵐ x ∂volume.restrict (D.Ω : Set (SpatialCoordinates d)),
      H x = G x)
    (_hR : ∀ᵐ x ∂volume.restrict (D.reflected : Set (SpatialCoordinates d)),
      H x = G (coordinateReflection D.z {D.i} x))
    (hH : ∀ᵐ x ∂volume.restrict (D.U : Set (SpatialCoordinates d)),
      H x = (D.Ω : Set (SpatialCoordinates d)).indicator G x +
        (D.reflected : Set (SpatialCoordinates d)).indicator
          (G ∘ coordinateReflection D.z {D.i}) x) :
    AEMeasurable H (volume.restrict (D.U : Set (SpatialCoordinates d))) ∧
      (∀ᵐ x ∂volume.restrict (D.U : Set (SpatialCoordinates d)), |H x| ≤ M) := by
  have hRmap : MeasurePreserving (coordinateReflection D.z {D.i})
      (volume.restrict (D.reflected : Set (SpatialCoordinates d)))
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
    coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_Ω
  have hpieceΩ : AEMeasurable ((D.Ω : Set (SpatialCoordinates d)).indicator G)
      (volume.restrict (D.U : Set (SpatialCoordinates d))) := by
    apply (aemeasurable_indicator_iff D.Ω.isOpen.measurableSet).2
    rw [Measure.restrict_restrict D.Ω.isOpen.measurableSet,
      Set.inter_eq_left.mpr D.Ω_le]
    exact hG
  have hGR : AEMeasurable (G ∘ coordinateReflection D.z {D.i})
      (volume.restrict (D.reflected : Set (SpatialCoordinates d))) :=
    hG.comp_quasiMeasurePreserving hRmap.quasiMeasurePreserving
  have hpieceR : AEMeasurable
      ((D.reflected : Set (SpatialCoordinates d)).indicator
        (G ∘ coordinateReflection D.z {D.i})
      )
      (volume.restrict (D.U : Set (SpatialCoordinates d))) := by
    apply (aemeasurable_indicator_iff D.reflected.isOpen.measurableSet).2
    rw [Measure.restrict_restrict D.reflected.isOpen.measurableSet,
      Set.inter_eq_left.mpr D.reflected_le]
    exact hGR
  have hpiece : AEMeasurable
      ((D.Ω : Set (SpatialCoordinates d)).indicator G +
        (D.reflected : Set (SpatialCoordinates d)).indicator
          (G ∘ coordinateReflection D.z {D.i}))
      (volume.restrict (D.U : Set (SpatialCoordinates d))) := by
    exact hpieceΩ.add hpieceR
  have hH' :
      ((D.Ω : Set (SpatialCoordinates d)).indicator G +
        (D.reflected : Set (SpatialCoordinates d)).indicator
          (G ∘ coordinateReflection D.z {D.i})) =ᵐ[
        volume.restrict (D.U : Set (SpatialCoordinates d))] H := by
    filter_upwards [hH] with x hx
    exact hx.symm
  have hHmeas := hpiece.congr hH'
  have hRbd : ∀ᵐ x ∂volume.restrict (D.reflected : Set (SpatialCoordinates d)),
      |G (coordinateReflection D.z {D.i} x)| ≤ M :=
    hRmap.quasiMeasurePreserving.ae hGbd
  have hGbdU : ∀ᵐ x ∂volume.restrict (D.U : Set (SpatialCoordinates d)),
      x ∈ (D.Ω : Set (SpatialCoordinates d)) → |G x| ≤ M :=
    ae_restrict_of_ae ((ae_restrict_iff' D.Ω.isOpen.measurableSet).mp hGbd)
  have hRbdU : ∀ᵐ x ∂volume.restrict (D.U : Set (SpatialCoordinates d)),
      x ∈ (D.reflected : Set (SpatialCoordinates d)) →
        |G (coordinateReflection D.z {D.i} x)| ≤ M :=
    ae_restrict_of_ae ((ae_restrict_iff' D.reflected.isOpen.measurableSet).mp hRbd)
  have hpiecebd : ∀ᵐ x ∂volume.restrict (D.U : Set (SpatialCoordinates d)),
      |((D.Ω : Set (SpatialCoordinates d)).indicator G x +
        (D.reflected : Set (SpatialCoordinates d)).indicator
          (G ∘ coordinateReflection D.z {D.i}) x)| ≤ M := by
    filter_upwards [hGbdU, hRbdU, D.ae_mem_or_mem] with x hxΩ hxR hxmem
    rcases hxmem with hx | hx
    · rw [Set.indicator_of_mem hx, Set.indicator_of_notMem
        (D.notMem_reflected_of_mem_Ω hx), add_zero]
      exact hxΩ hx
    · rw [Set.indicator_of_notMem (D.notMem_Ω_of_mem_reflected hx),
        Set.indicator_of_mem hx, zero_add, Function.comp_apply]
      exact hxR hx
  refine ⟨hHmeas, ?_⟩
  filter_upwards [hpiecebd, hH] with x hx hxy
  rw [hxy]
  exact hx

lemma aux_lem_even_weak_transport_one_face
    {d : ℕ} (D : SubdiffusiveProcess.EvenReflectionDomain d)
    (a : PositiveCoefficient D.Ω) (u : SobolevData D.Ω)
    (G H : SpatialCoordinates d → ℝ)
    (hEq : ∀ φ : weakSobolevGraph D.Ω,
      sobolevCoefficientForm a u (φ : SobolevData D.Ω) =
        ∫ x in (D.Ω : Set (SpatialCoordinates d)), G x *
          (φ : SobolevData D.Ω).1 x)
    (hΩ : ∀ᵐ x ∂volume.restrict (D.Ω : Set (SpatialCoordinates d)),
      H x = G x)
    (hR : ∀ᵐ x ∂volume.restrict (D.reflected : Set (SpatialCoordinates d)),
      H x = G (coordinateReflection D.z {D.i} x))
    (ψ : weakSobolevGraph D.U)
    (hIntΩ : IntegrableOn (fun x => H x * (ψ : SobolevData D.U).1 x)
      (D.Ω : Set (SpatialCoordinates d)))
    (hIntR : IntegrableOn (fun x => H x * (ψ : SobolevData D.U).1 x)
      (D.reflected : Set (SpatialCoordinates d))) :
    sobolevCoefficientForm (D.evenExtensionCoefficient a)
        (D.evenExtension u) (ψ : SobolevData D.U) =
      ∫ x in (D.U : Set (SpatialCoordinates d)), H x *
        (ψ : SobolevData D.U).1 x := by
  have htransport := D.evenExtension_weak_equation a
    (sobolevCoefficientForm a u) (by
      intro φ hφ
      rfl) ψ.property
  have h1 := hEq
    (⟨sobolevDataRestrict D.Ω_le (ψ : SobolevData D.U),
      sobolevDataRestrict_mem_weak D.Ω_le ψ.property⟩ : weakSobolevGraph D.Ω)
  have h2 := hEq
    (⟨D.reflectedRestrict (ψ : SobolevData D.U),
      D.reflectedRestrict_mem_weak ψ.property⟩ : weakSobolevGraph D.Ω)
  rw [htransport]
  rw [h1, h2]
  exact aux_lem_even_weak_transport_source D G H hΩ hR
    (ψ : SobolevData D.U) hIntΩ hIntR

lemma aux_lem_even_weak_transport_reflected
    {d : ℕ} (D : SubdiffusiveProcess.EvenReflectionDomain d)
    (b : PositiveCoefficient D.reflected) (u : SobolevData D.reflected)
    (G : SpatialCoordinates d → ℝ)
    (hEq : ∀ φ : weakSobolevGraph D.reflected,
      sobolevCoefficientForm b u (φ : SobolevData D.reflected) =
        ∫ x in (D.reflected : Set (SpatialCoordinates d)), G x *
          (φ : SobolevData D.reflected).1 x)
    (ψ : weakSobolevGraph D.Ω) :
    sobolevCoefficientForm
        (reflectionCoefficient D.z {D.i} D.preimage_reflected b)
        (reflectionSobolevData D.z {D.i} D.preimage_reflected u)
        (ψ : SobolevData D.Ω) =
      ∫ x in (D.Ω : Set (SpatialCoordinates d)),
        G (coordinateReflection D.z {D.i} x) *
          (ψ : SobolevData D.Ω).1 x := by
  let ψR : weakSobolevGraph D.reflected :=
    ⟨reflectionSobolevData D.z {D.i} D.preimage_Ω
        (ψ : SobolevData D.Ω),
      reflectionSobolevData_mem_weak D.z {D.i} D.preimage_Ω ψ.property⟩
  have hform := sobolevCoefficientForm_reflection D.z {D.i}
    D.preimage_reflected b u (ψR : SobolevData D.reflected)
  have hinv : reflectionSobolevData D.z {D.i} D.preimage_reflected
      (ψR : SobolevData D.reflected) = (ψ : SobolevData D.Ω) := by
    dsimp [ψR]
    exact reflectionSobolevData_inverse D.z {D.i} D.preimage_Ω
      (ψ : SobolevData D.Ω)
  have hform' : sobolevCoefficientForm
        (reflectionCoefficient D.z {D.i} D.preimage_reflected b)
        (reflectionSobolevData D.z {D.i} D.preimage_reflected u)
        (ψ : SobolevData D.Ω) =
      sobolevCoefficientForm b u (ψR : SobolevData D.reflected) := by
    rw [← hform, hinv]
  rw [hform', hEq ψR]
  change (∫ x in (D.reflected : Set (SpatialCoordinates d)),
      G x * reflectionLp D.z {D.i} D.preimage_Ω
        (ψ : SobolevData D.Ω).1 x) = _
  rw [integral_mul_reflectionLp D.z {D.i} D.preimage_Ω G
    (ψ : SobolevData D.Ω).1]

lemma aux_lem_even_weak_transport_geometry_up
    (d : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (I P : Finset (Fin d)) (i : Fin d) (hi : i ∉ I) (hiP : i ∈ P) :
    ∃ D : SubdiffusiveProcess.EvenReflectionDomain d,
      D.Ω = foldedCube w r hr I P ∧
      D.U = foldedCube w r hr (insert i I) P ∧
      D.z = foldedCubeCenter w r (insert i I) P ∧
      D.i = i ∧
      (∀ x : SpatialCoordinates d, x ∈ D.Ω →
        coordinateFold (foldedCubeCenter w r (insert i I) P) (insert i I) P x =
          coordinateFold (foldedCubeCenter w r I P) I P x) ∧
      (∀ x : SpatialCoordinates d, x ∈ D.reflected →
        coordinateFold (foldedCubeCenter w r (insert i I) P) (insert i I) P x =
          coordinateFold (foldedCubeCenter w r I P) I P
            (coordinateReflection D.z {i} x)) ∧
      (∀ j x, x ∈ D.Ω →
        (if j ∈ insert i I then
            coordinateReflectionSign P j *
              (if x j < foldedCubeCenter w r (insert i I) P j then -1 else 1)
         else 1) =
          (if j ∈ I then
            coordinateReflectionSign P j *
              (if x j < foldedCubeCenter w r I P j then -1 else 1)
           else 1)) ∧
      (∀ j x, x ∈ D.reflected →
        (if j ∈ insert i I then
            coordinateReflectionSign P j *
              (if x j < foldedCubeCenter w r (insert i I) P j then -1 else 1)
         else 1) =
          coordinateReflectionSign {i} j *
            (if j ∈ I then
              coordinateReflectionSign P j *
                (if (coordinateReflection D.z {i} x) j <
                    foldedCubeCenter w r I P j then -1 else 1)
             else 1)) := by
  classical
  let z : SpatialCoordinates d := foldedCubeCenter w r (insert i I) P
  let D : SubdiffusiveProcess.EvenReflectionDomain d :=
    { z := z
      i := i
      Ω := foldedCube w r hr I P
      U := foldedCube w r hr (insert i I) P
      mem_iff := by
        intro x
        change x ∈ (foldedCube w r hr I P : Set _) ↔
          x ∈ (foldedCube w r hr (insert i I) P : Set _) ∧ x i < z i
        simp only [foldedCube, z]
        constructor
        · intro hx
          refine ⟨?_, ?_⟩
          · intro j hjj
            have hxj := hx j hjj
            by_cases hji : j = i
            · subst j
              have hxj' : x i ∈ Set.Ioo (w i - r / 2) (w i + r / 2) := by
                simpa [hi] using! hxj
              have hnew : x i ∈ Set.Ioo (w i - r / 2) (w i + 3 * r / 2) :=
                ⟨hxj'.1, by linarith [hxj'.2, hr]⟩
              simpa [Finset.mem_insert, hiP] using! hnew
            · simpa [Finset.mem_insert, hji] using! hxj
          · have hxi := hx i (by simp)
            have hxi' : x i ∈ Set.Ioo (w i - r / 2) (w i + r / 2) := by
              simpa [hi] using! hxi
            simpa [foldedCubeCenter, z, Finset.mem_insert, hiP] using! hxi'.2
        · rintro ⟨hx, hxi⟩ j hjj
          have hxj := hx j hjj
          by_cases hji : j = i
          · subst j
            have hxj' : x i ∈ Set.Ioo (w i - r / 2) (w i + 3 * r / 2) := by
              simpa [Finset.mem_insert, hiP] using! hxj
            have hz : z i = w i + r / 2 := by
              simp [z, foldedCubeCenter, hiP]
            have hold : x i ∈ Set.Ioo (w i - r / 2) (w i + r / 2) :=
              ⟨hxj'.1, by simpa [foldedCubeCenter, hiP, z] using! hxi⟩
            simpa [hi] using! hold
          · simpa [Finset.mem_insert, hji] using! hxj
      symm := by
        ext x
        change coordinateReflection z {i} x ∈
            (foldedCube w r hr (insert i I) P : Set _) ↔
          x ∈ (foldedCube w r hr (insert i I) P : Set _)
        simp only [foldedCube]
        constructor <;> intro hx j hjj
        · have hxj := hx j hjj
          by_cases hji : j = i
          · subst j
            have hxj' : coordinateReflection z {i} x i ∈
                Set.Ioo (w i - r / 2) (w i + 3 * r / 2) := by
              simpa [Finset.mem_insert, hiP] using! hxj
            simp only [coordinateReflection_single_apply_self] at hxj'
            rcases hxj' with ⟨hx1, hx2⟩
            have hz : z i = w i + r / 2 := by
              simp [z, foldedCubeCenter, hiP]
            have htarget : x i ∈
                Set.Ioo (w i - r / 2) (w i + 3 * r / 2) := by
              constructor <;> linarith [hx1, hx2, hr, hz]
            simpa [Finset.mem_insert, hiP] using! htarget
          · simpa [coordinateReflection, Finset.mem_singleton, hji,
              Finset.mem_insert, hji] using! hxj
        · have hxj := hx j hjj
          by_cases hji : j = i
          · subst j
            have hxj' : x i ∈
                Set.Ioo (w i - r / 2) (w i + 3 * r / 2) := by
              simpa [Finset.mem_insert, hiP] using! hxj
            have htarget : coordinateReflection z {i} x i ∈
                Set.Ioo (w i - r / 2) (w i + 3 * r / 2) := by
              simp only [coordinateReflection_single_apply_self]
              have hz : z i = w i + r / 2 := by
                simp [z, foldedCubeCenter, hiP]
              rcases hxj' with ⟨hx1, hx2⟩
              constructor <;> linarith [hx1, hx2, hr, hz]
            simpa [Finset.mem_insert, hiP] using! htarget
          · simpa [coordinateReflection, Finset.mem_singleton, hji,
              Finset.mem_insert, hji] using! hxj }
  let z₀ : SpatialCoordinates d := foldedCubeCenter w r I P
  have hcenter : coordinateFold z₀ I P = coordinateFold z I P := by
    funext x j
    by_cases hj : j ∈ I
    · simp only [coordinateFold, hj, ite_true]
      by_cases hji : j = i
      · subst j
        exact (hi hj).elim
      · simp [z, z₀, foldedCubeCenter, hji]
    · simp only [coordinateFold, hj, ite_false]
  have hΩ (x : SpatialCoordinates d) (hx : x ∈ D.Ω) :
      coordinateFold z (insert i I) P x = coordinateFold z₀ I P x := by
    have hxi : x i ≤ z i :=
      le_of_lt ((D.mem_iff x).mp hx |>.2)
    calc
      coordinateFold z (insert i I) P x = coordinateFold z I (insert i P) x := by
        simpa [Finset.insert_eq_of_mem hiP] using!
          (lane2_fold_insert_both_of_le (z := z) (I := I) (P := P)
            (i := i) hi hxi)
      _ = coordinateFold z I P x := by simp [Finset.insert_eq_of_mem hiP]
      _ = coordinateFold z₀ I P x := by rw [hcenter]
  have hR (x : SpatialCoordinates d) (hx : x ∈ D.reflected) :
      coordinateFold z (insert i I) P x =
        coordinateFold z₀ I P (coordinateReflection z {i} x) := by
    have hxi : z i ≤ x i :=
      le_of_lt ((D.mem_reflected_iff x).mp hx |>.2)
    calc
      coordinateFold z (insert i I) P x =
          coordinateFold z I (insert i P) (coordinateReflection z {i} x) := by
        simpa [Finset.insert_eq_of_mem hiP] using!
          (lane2_fold_insert_both_of_ge (z := z) (I := I) (P := P)
            (i := i) hi hxi)
      _ = coordinateFold z I P (coordinateReflection z {i} x) := by
        simp [Finset.insert_eq_of_mem hiP]
      _ = coordinateFold z₀ I P (coordinateReflection z {i} x) := by rw [hcenter]
  have hfacΩ (j : Fin d) (x : SpatialCoordinates d) (hx : x ∈ D.Ω) :
      (if j ∈ insert i I then
          coordinateReflectionSign P j *
            (if x j < foldedCubeCenter w r (insert i I) P j then -1 else 1)
       else 1) =
        (if j ∈ I then
          coordinateReflectionSign P j *
            (if x j < foldedCubeCenter w r I P j then -1 else 1)
         else 1) := by
    by_cases hji : j = i
    · subst j
      have hxi : x i < z i := (D.mem_iff x).mp hx |>.2
      have hxi' : x i < w i + r / 2 := by
        simpa [z, foldedCubeCenter, hiP] using! hxi
      simp [hi, hiP, foldedCubeCenter, coordinateReflectionSign, hxi']
    · by_cases hj : j ∈ I
      · simp [Finset.mem_insert, hji, hj, foldedCubeCenter]
      · simp [Finset.mem_insert, hji, hj]
  have hfacR (j : Fin d) (x : SpatialCoordinates d) (hx : x ∈ D.reflected) :
      (if j ∈ insert i I then
          coordinateReflectionSign P j *
            (if x j < foldedCubeCenter w r (insert i I) P j then -1 else 1)
       else 1) =
        coordinateReflectionSign {i} j *
          (if j ∈ I then
            coordinateReflectionSign P j *
              (if (coordinateReflection D.z {i} x) j <
                  foldedCubeCenter w r I P j then -1 else 1)
           else 1) := by
    by_cases hji : j = i
    · subst j
      have hxi : z i < x i := (D.mem_reflected_iff x).mp hx |>.2
      have hxi' : ¬ x i < w i + r / 2 := by
        intro hlt
        have : x i < z i := by simpa [z, foldedCubeCenter, hiP] using! hlt
        linarith
      simp [hi, hiP, foldedCubeCenter, coordinateReflectionSign, hxi']
    · have hRj : (coordinateReflection z {i} x) j = x j :=
        coordinateReflection_single_apply_of_ne z hji x
      have hRj' : (coordinateReflection D.z {i} x) j = x j := by
        simpa [D] using! coordinateReflection_single_apply_of_ne z hji x
      simp [Finset.mem_insert, hji, foldedCubeCenter,
        coordinateReflectionSign, hRj']
  refine ⟨D, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hΩ x hx
  · intro x hx
    exact hR x hx
  · exact hfacΩ
  · exact hfacR

lemma aux_lem_even_weak_transport_geometry_down
    (d : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (I P : Finset (Fin d)) (i : Fin d) (hi : i ∉ I) (hiP : i ∉ P) :
    ∃ D : SubdiffusiveProcess.EvenReflectionDomain d,
      D.reflected = foldedCube w r hr I P ∧
      D.U = foldedCube w r hr (insert i I) P ∧
      D.z = foldedCubeCenter w r (insert i I) P ∧
      D.i = i ∧
      (∀ x : SpatialCoordinates d, x ∈ D.Ω →
        coordinateFold (foldedCubeCenter w r (insert i I) P) (insert i I) P x =
          coordinateFold (foldedCubeCenter w r I P) I P
            (coordinateReflection D.z {i} x)) ∧
      (∀ x : SpatialCoordinates d, x ∈ D.reflected →
        coordinateFold (foldedCubeCenter w r (insert i I) P) (insert i I) P x =
          coordinateFold (foldedCubeCenter w r I P) I P x) ∧
      (∀ j x, x ∈ D.Ω →
        (if j ∈ insert i I then
            coordinateReflectionSign P j *
              (if x j < foldedCubeCenter w r (insert i I) P j then -1 else 1)
         else 1) =
          coordinateReflectionSign {i} j *
            (if j ∈ I then
              coordinateReflectionSign P j *
                (if (coordinateReflection D.z {i} x) j <
                    foldedCubeCenter w r I P j then -1 else 1)
             else 1)) ∧
      (∀ j x, x ∈ D.reflected →
        (if j ∈ insert i I then
            coordinateReflectionSign P j *
              (if x j < foldedCubeCenter w r (insert i I) P j then -1 else 1)
         else 1) =
          (if j ∈ I then
            coordinateReflectionSign P j *
              (if x j < foldedCubeCenter w r I P j then -1 else 1)
           else 1)) := by
  classical
  let z : SpatialCoordinates d := foldedCubeCenter w r (insert i I) P
  let Ω : Opens (SpatialCoordinates d) :=
    { carrier := coordinateReflection z {i} ⁻¹'
        (foldedCube w r hr I P : Set (SpatialCoordinates d))
      is_open' := (foldedCube w r hr I P).isOpen.preimage
        (coordinateReflection_isometry z {i}).continuous }
  let D : SubdiffusiveProcess.EvenReflectionDomain d :=
    { z := z
      i := i
      Ω := Ω
      U := foldedCube w r hr (insert i I) P
      mem_iff := by
        intro x
        change coordinateReflection z {i} x ∈
            (foldedCube w r hr I P : Set _) ↔
          x ∈ (foldedCube w r hr (insert i I) P : Set _) ∧ x i < z i
        simp only [foldedCube]
        constructor
        · intro hx
          refine ⟨?_, ?_⟩
          · intro j hjj
            have hxj := hx j hjj
            by_cases hji : j = i
            · subst j
              have hxj' : coordinateReflection z {i} x i ∈
                  Set.Ioo (w i - r / 2) (w i + r / 2) := by
                simpa [hi] using! hxj
              have hxi : x i ∈ Set.Ioo (w i - 3 * r / 2) (w i + r / 2) := by
                have hz : z i = w i - r / 2 := by
                  simp [z, foldedCubeCenter, hiP]
                rw [coordinateReflection_single_apply_self] at hxj'
                rcases hxj' with ⟨hx1, hx2⟩
                constructor <;> linarith [hx1, hx2, hr, hz]
              simpa [Finset.mem_insert, hiP] using! hxi
            · simpa [coordinateReflection_single_apply_of_ne z hji x,
                Finset.mem_insert, hji] using! hxj
          · have hxj := hx i (by simp)
            have hxj' : coordinateReflection z {i} x i ∈
                Set.Ioo (w i - r / 2) (w i + r / 2) := by
              simpa [hi] using! hxj
            have hz : z i = w i - r / 2 := by
              simp [z, foldedCubeCenter, hiP]
            simp only [coordinateReflection_single_apply_self] at hxj'
            rcases hxj' with ⟨hx1, hx2⟩
            linarith [hx1, hx2, hr, hz]
        · rintro ⟨hx, hxi⟩ j hjj
          have hxj := hx j hjj
          by_cases hji : j = i
          · subst j
            have hxj' : x i ∈ Set.Ioo (w i - 3 * r / 2) (w i + r / 2) := by
              simpa [Finset.mem_insert, hiP] using! hxj
            have hz : z i = w i - r / 2 := by
              simp [z, foldedCubeCenter, hiP]
            have href : coordinateReflection z {i} x i ∈
                Set.Ioo (w i - r / 2) (w i + r / 2) := by
              simp only [coordinateReflection_single_apply_self]
              rcases hxj' with ⟨hx1, hx2⟩
              constructor <;> linarith [hx1, hx2, hr, hz]
            simpa [hi] using! href
          · simpa [coordinateReflection_single_apply_of_ne z hji x,
              Finset.mem_insert, hji] using! hxj
      symm := by
        ext x
        change coordinateReflection z {i} x ∈
            (foldedCube w r hr (insert i I) P : Set _) ↔
          x ∈ (foldedCube w r hr (insert i I) P : Set _)
        simp only [foldedCube]
        constructor <;> intro hx j hjj
        · have hxj := hx j hjj
          by_cases hji : j = i
          · subst j
            have hxj' : coordinateReflection z {i} x i ∈
                Set.Ioo (w i - 3 * r / 2) (w i + r / 2) := by
              simpa [Finset.mem_insert, hiP] using! hxj
            simp only [coordinateReflection_single_apply_self] at hxj'
            have hz : z i = w i - r / 2 := by
              simp [z, foldedCubeCenter, hiP]
            rcases hxj' with ⟨hx1, hx2⟩
            have htarget : x i ∈
                Set.Ioo (w i - 3 * r / 2) (w i + r / 2) := by
              constructor <;> linarith [hx1, hx2, hr, hz]
            simpa [Finset.mem_insert, hiP] using! htarget
          · simpa [coordinateReflection, Finset.mem_singleton, hji,
              Finset.mem_insert, hji] using! hxj
        · have hxj := hx j hjj
          by_cases hji : j = i
          · subst j
            have hxj' : x i ∈
                Set.Ioo (w i - 3 * r / 2) (w i + r / 2) := by
              simpa [Finset.mem_insert, hiP] using! hxj
            have hz : z i = w i - r / 2 := by
              simp [z, foldedCubeCenter, hiP]
            have htarget : coordinateReflection z {i} x i ∈
                Set.Ioo (w i - 3 * r / 2) (w i + r / 2) := by
              simp only [coordinateReflection_single_apply_self]
              rcases hxj' with ⟨hx1, hx2⟩
              constructor <;> linarith [hx1, hx2, hr, hz]
            simpa [Finset.mem_insert, hiP] using! htarget
          · simpa [coordinateReflection, Finset.mem_singleton, hji,
              Finset.mem_insert, hji] using! hxj }
  have hDref : D.reflected = foldedCube w r hr I P := by
    ext x
    change coordinateReflection z {i} x ∈
        coordinateReflection z {i} ⁻¹'
          (foldedCube w r hr I P : Set _) ↔
      x ∈ (foldedCube w r hr I P : Set _)
    simp only [Set.mem_preimage]
    rw [coordinateReflection_involutive]
  let z₀ : SpatialCoordinates d := foldedCubeCenter w r I P
  have hcenter : coordinateFold z₀ I P = coordinateFold z I P := by
    funext x j
    by_cases hj : j ∈ I
    · simp only [coordinateFold, hj, ite_true]
      by_cases hji : j = i
      · subst j
        exact (hi hj).elim
      · simp [z, z₀, foldedCubeCenter, hji]
    · simp only [coordinateFold, hj, ite_false]
  have hΩ (x : SpatialCoordinates d) (hx : x ∈ D.Ω) :
      coordinateFold z (insert i I) P x =
        coordinateFold z₀ I P (coordinateReflection z {i} x) := by
    have hxi : x i ≤ z i :=
      le_of_lt ((D.mem_iff x).mp hx |>.2)
    calc
      coordinateFold z (insert i I) P x =
          coordinateFold z I P (coordinateReflection z {i} x) := by
        simpa using!
          (lane2_fold_insert_I_of_le (z := z) (I := I) (P := P)
            (i := i) hi hiP hxi)
      _ = coordinateFold z₀ I P (coordinateReflection z {i} x) := by
        rw [hcenter]
  have hR (x : SpatialCoordinates d) (hx : x ∈ D.reflected) :
      coordinateFold z (insert i I) P x = coordinateFold z₀ I P x := by
    have hxi : z i ≤ x i :=
      le_of_lt ((D.mem_reflected_iff x).mp hx |>.2)
    calc
      coordinateFold z (insert i I) P x = coordinateFold z I P x := by
        simpa using!
          (lane2_fold_insert_I_of_ge (z := z) (I := I) (P := P)
            (i := i) hi hiP hxi)
      _ = coordinateFold z₀ I P x := by rw [hcenter]
  have hfacΩ (j : Fin d) (x : SpatialCoordinates d) (hx : x ∈ D.Ω) :
      (if j ∈ insert i I then
          coordinateReflectionSign P j *
            (if x j < foldedCubeCenter w r (insert i I) P j then -1 else 1)
       else 1) =
        coordinateReflectionSign {i} j *
          (if j ∈ I then
            coordinateReflectionSign P j *
              (if (coordinateReflection D.z {i} x) j <
                  foldedCubeCenter w r I P j then -1 else 1)
           else 1) := by
    by_cases hji : j = i
    · subst j
      have hxi : x i < z i := (D.mem_iff x).mp hx |>.2
      have hxi' : x i < w i - r / 2 := by
        simpa [z, foldedCubeCenter, hiP] using! hxi
      simp [hi, hiP, foldedCubeCenter, coordinateReflectionSign, hxi']
    · have hRj : (coordinateReflection D.z {i} x) j = x j := by
        simpa [D] using! coordinateReflection_single_apply_of_ne z hji x
      simp [Finset.mem_insert, hji, foldedCubeCenter,
        coordinateReflectionSign, hRj]
  have hfacR (j : Fin d) (x : SpatialCoordinates d) (hx : x ∈ D.reflected) :
      (if j ∈ insert i I then
          coordinateReflectionSign P j *
            (if x j < foldedCubeCenter w r (insert i I) P j then -1 else 1)
       else 1) =
        (if j ∈ I then
          coordinateReflectionSign P j *
            (if x j < foldedCubeCenter w r I P j then -1 else 1)
         else 1) := by
    by_cases hji : j = i
    · subst j
      have hxi : z i < x i := (D.mem_reflected_iff x).mp hx |>.2
      have hxi' : ¬ x i < w i - r / 2 := by
        intro hlt
        have : x i < z i := by simpa [z, foldedCubeCenter, hiP] using! hlt
        linarith
      simp [hi, hiP, foldedCubeCenter, coordinateReflectionSign, hxi']
    · by_cases hjI : j ∈ I <;> by_cases hjP : j ∈ P <;>
        simp [Finset.mem_insert, hji, foldedCubeCenter,
          coordinateReflectionSign, hjI, hjP]
  refine ⟨D, hDref, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hΩ x hx
  · intro x hx
    exact hR x hx
  · exact hfacΩ
  · exact hfacR

lemma aux_lem_even_weak_transport_base
    (d : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (P : Finset (Fin d))
    (a : PositiveCoefficient (centeredCube w r hr))
    (v : weakSobolevGraph (centeredCube w r hr))
    (F : SpatialCoordinates d → ℝ) (MF : ℝ) (_hMF : 0 ≤ MF)
    (hF : AEMeasurable F
      (volume.restrict (centeredCube w r hr : Set (SpatialCoordinates d))))
    (hbound : ∀ᵐ x ∂volume.restrict (centeredCube w r hr : Set (SpatialCoordinates d)),
      |F x| ≤ MF)
    (heq : ∀ ψ : weakSobolevGraph (centeredCube w r hr),
      sobolevCoefficientForm a (v : SobolevData (centeredCube w r hr))
          (ψ : SobolevData (centeredCube w r hr)) =
        ∫ x in (centeredCube w r hr : Set (SpatialCoordinates d)),
          F x * (ψ : SobolevData (centeredCube w r hr)).1 x)
    (af : PositiveCoefficient (foldedCube w r hr ∅ P))
    (vf : weakSobolevGraph (foldedCube w r hr ∅ P))
    (ha : ((af.val : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (foldedCube w r hr ∅ P : Set (SpatialCoordinates d))]
      fun x => a.val (coordinateFold (foldedCubeCenter w r ∅ P) ∅ P x)))
    (hg : ∀ j : Fin d,
      ∀ᵐ x ∂volume.restrict (foldedCube w r hr ∅ P : Set (SpatialCoordinates d)),
        sobolevGradient (vf : SobolevData (foldedCube w r hr ∅ P)) j x =
          (if j ∈ (∅ : Finset (Fin d)) then
            coordinateReflectionSign P j *
              (if x j < foldedCubeCenter w r ∅ P j then -1 else 1)
           else 1) *
            sobolevGradient (v : SobolevData (centeredCube w r hr)) j
              (coordinateFold (foldedCubeCenter w r ∅ P) ∅ P x)) :
    (∀ ψ : weakSobolevGraph (foldedCube w r hr ∅ P),
      sobolevCoefficientForm af (vf : SobolevData (foldedCube w r hr ∅ P))
          (ψ : SobolevData (foldedCube w r hr ∅ P)) =
        ∫ x in (foldedCube w r hr ∅ P : Set (SpatialCoordinates d)),
          F (coordinateFold (foldedCubeCenter w r ∅ P) ∅ P x) *
            (ψ : SobolevData (foldedCube w r hr ∅ P)).1 x) ∧
      AEMeasurable
          (fun x => F (coordinateFold (foldedCubeCenter w r ∅ P) ∅ P x))
          (volume.restrict (foldedCube w r hr ∅ P : Set (SpatialCoordinates d))) ∧
      (∀ᵐ x ∂volume.restrict (foldedCube w r hr ∅ P : Set (SpatialCoordinates d)),
        |F (coordinateFold (foldedCubeCenter w r ∅ P) ∅ P x)| ≤ MF) := by
  have hΩ : foldedCube w r hr ∅ P = centeredCube w r hr := by
    ext x
    rw [centeredCube_eq_pi]
    simp [foldedCube]
  have hfold (x : SpatialCoordinates d) :
      coordinateFold (foldedCubeCenter w r ∅ P) ∅ P x = x := by
    funext j
    simp [coordinateFold]
  generalize hq : foldedCube w r hr ∅ P = Q at af vf ha hg ⊢
  have hQ : Q = centeredCube w r hr := hq.symm.trans hΩ
  cases hQ
  have ha' : ((af.val : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube w r hr : Set (SpatialCoordinates d))] a.val) := by
    filter_upwards [ha] with x hx
    rw [hfold] at hx
    exact hx
  have hg' : ∀ j : Fin d,
      ∀ᵐ x ∂volume.restrict (centeredCube w r hr : Set (SpatialCoordinates d)),
        ((vf : SobolevData (centeredCube w r hr)).2 j : SpatialCoordinates d → ℝ) x =
          ((v : SobolevData (centeredCube w r hr)).2 j : SpatialCoordinates d → ℝ) x := by
    intro j
    have hj := hg j
    change ∀ᵐ x ∂volume.restrict (centeredCube w r hr : Set (SpatialCoordinates d)),
      ((vf : SobolevData (centeredCube w r hr)).2 j : SpatialCoordinates d → ℝ) x = _ at hj
    filter_upwards [hj] with x hx
    simpa [hfold] using! hx
  have hregular :
      AEMeasurable (fun x => F (coordinateFold (foldedCubeCenter w r ∅ P) ∅ P x))
          (volume.restrict (centeredCube w r hr : Set (SpatialCoordinates d))) ∧
      (∀ᵐ x ∂volume.restrict (centeredCube w r hr : Set (SpatialCoordinates d)),
        |F (coordinateFold (foldedCubeCenter w r ∅ P) ∅ P x)| ≤ MF) := by
    constructor
    · simpa [hfold] using! hF
    · filter_upwards [hbound] with x hx
      simpa [hfold] using! hx
  refine ⟨?_, hregular.1, hregular.2⟩
  intro ψ
  have hform := aux_lem_even_weak_transport_form_congr af a
    ha' (vf : SobolevData (centeredCube w r hr)) (v : SobolevData (centeredCube w r hr))
    hg' (ψ : SobolevData (centeredCube w r hr))
  rw [hform, heq ψ]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [Function.comp_apply] using!
      congrArg (fun y => F y * (ψ : SobolevData (centeredCube w r hr)).1 x)
      (hfold x).symm)

lemma aux_lem_even_weak_transport_cast_equation
    {d : ℕ} {Ω₁ Ω₂ : Opens (SpatialCoordinates d)}
    (hΩ : Ω₁ = Ω₂) (a : PositiveCoefficient Ω₂)
    (u : weakSobolevGraph Ω₂) (G : SpatialCoordinates d → ℝ)
    (hEq : ∀ φ : weakSobolevGraph Ω₂,
      sobolevCoefficientForm a (u : SobolevData Ω₂)
          (φ : SobolevData Ω₂) =
        ∫ x in (Ω₂ : Set (SpatialCoordinates d)), G x *
          (φ : SobolevData Ω₂).1 x) :
    ∀ φ : weakSobolevGraph Ω₁,
      sobolevCoefficientForm (hΩ.symm ▸ a) (hΩ.symm ▸ (u : SobolevData Ω₂))
          (φ : SobolevData Ω₁) =
        ∫ x in (Ω₁ : Set (SpatialCoordinates d)), G x *
          (φ : SobolevData Ω₁).1 x := by
  subst hΩ
  exact hEq

lemma aux_lem_even_weak_transport_even_gradient
    {d : ℕ} (D : SubdiffusiveProcess.EvenReflectionDomain d)
    (u : SobolevData D.Ω)
    (newFold oldFold : SpatialCoordinates d → SpatialCoordinates d)
    (newFac oldFac : Fin d → SpatialCoordinates d → ℝ)
    (gv : Fin d → SpatialCoordinates d → ℝ)
    (hbaseΩ : ∀ j : Fin d,
      ∀ᵐ x ∂volume.restrict (D.Ω : Set (SpatialCoordinates d)),
        (u.2 j : SpatialCoordinates d → ℝ) x =
          oldFac j x * gv j (oldFold x))
    (hbaseR : ∀ j : Fin d,
      ∀ᵐ x ∂volume.restrict (D.reflected : Set (SpatialCoordinates d)),
        (u.2 j : SpatialCoordinates d → ℝ)
            (coordinateReflection D.z {D.i} x) =
          oldFac j (coordinateReflection D.z {D.i} x) *
            gv j (oldFold (coordinateReflection D.z {D.i} x)))
    (hfoldΩ : ∀ x : SpatialCoordinates d, x ∈ D.Ω →
      newFold x = oldFold x)
    (hfoldR : ∀ x : SpatialCoordinates d, x ∈ D.reflected →
      newFold x = oldFold (coordinateReflection D.z {D.i} x))
    (hfacΩ : ∀ j x, x ∈ D.Ω → newFac j x = oldFac j x)
    (hfacR : ∀ j x, x ∈ D.reflected →
      newFac j x = coordinateReflectionSign {D.i} j *
        oldFac j (coordinateReflection D.z {D.i} x)) :
    ∀ j : Fin d, ∀ᵐ x ∂volume.restrict (D.U : Set (SpatialCoordinates d)),
      sobolevGradient (D.evenExtension u) j x = newFac j x * gv j (newFold x) := by
  intro j
  change ∀ᵐ x ∂volume.restrict (D.U : Set (SpatialCoordinates d)),
    ((D.evenExtension u).2 j : SpatialCoordinates d → ℝ) x =
      newFac j x * gv j (newFold x)
  have hge := D.evenExtension_snd_coeFn u j
  have hΩ := ae_restrict_of_ae (s := (D.U : Set (SpatialCoordinates d)))
    ((ae_restrict_iff' D.Ω.isOpen.measurableSet).mp (hbaseΩ j))
  have hR := ae_restrict_of_ae (s := (D.U : Set (SpatialCoordinates d)))
    ((ae_restrict_iff' D.reflected.isOpen.measurableSet).mp (hbaseR j))
  filter_upwards [hge, hΩ, hR, D.ae_mem_or_mem] with x hxe hxΩ hxR hxmem
  rcases hxmem with hx | hx
  · rw [hxe, Set.indicator_of_mem hx,
      Set.indicator_of_notMem (D.notMem_reflected_of_mem_Ω hx), add_zero]
    rw [hxΩ hx, hfacΩ j x hx, hfoldΩ x hx]
  · rw [hxe, Set.indicator_of_notMem (D.notMem_Ω_of_mem_reflected hx),
      Set.indicator_of_mem hx, zero_add]
    rw [hxR hx, hfacR j x hx, hfoldR x hx]
    ring

lemma aux_lem_even_weak_transport_cast_gradient
    {d : ℕ} {Ω₁ Ω₂ : Opens (SpatialCoordinates d)}
    (hΩ : Ω₁ = Ω₂) (u : SobolevData Ω₂)
    (g : Fin d → SpatialCoordinates d → ℝ)
    (hu : ∀ j : Fin d, ∀ᵐ x ∂volume.restrict (Ω₂ : Set (SpatialCoordinates d)),
      sobolevGradient u j x = g j x) :
    ∀ j : Fin d, ∀ᵐ x ∂volume.restrict (Ω₁ : Set (SpatialCoordinates d)),
      sobolevGradient (hΩ.symm ▸ u) j x = g j x := by
  subst hΩ
  exact hu

lemma aux_lem_even_weak_transport_cast_weak_coe
    {d : ℕ} {Ω₁ Ω₂ : Opens (SpatialCoordinates d)}
    (hΩ : Ω₁ = Ω₂) (u : weakSobolevGraph Ω₂) :
    (hΩ.symm ▸ u : weakSobolevGraph Ω₁).1 =
      hΩ.symm ▸ (u : SobolevData Ω₂) := by
  subst hΩ
  rfl

lemma aux_lem_even_weak_transport_step_up
    (d : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (I P : Finset (Fin d)) (i : Fin d) (hi : i ∉ I) (hiP : i ∈ P)
    (a : PositiveCoefficient (centeredCube w r hr))
    (v : weakSobolevGraph (centeredCube w r hr))
    (F : SpatialCoordinates d → ℝ) (MF : ℝ)
    (af0 : PositiveCoefficient (foldedCube w r hr I P))
    (vf0 : weakSobolevGraph (foldedCube w r hr I P))
    (ha0 : ((af0.val : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d))]
      fun x => a.val (coordinateFold (foldedCubeCenter w r I P) I P x)))
    (hg0 : ∀ j : Fin d,
      ∀ᵐ x ∂volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d)),
        sobolevGradient (vf0 : SobolevData (foldedCube w r hr I P)) j x =
          (if j ∈ I then
            coordinateReflectionSign P j *
              (if x j < foldedCubeCenter w r I P j then -1 else 1)
           else 1) *
            sobolevGradient (v : SobolevData (centeredCube w r hr)) j
              (coordinateFold (foldedCubeCenter w r I P) I P x))
    (hprev : ∀ ψ : weakSobolevGraph (foldedCube w r hr I P),
      sobolevCoefficientForm af0 (vf0 : SobolevData (foldedCube w r hr I P))
          (ψ : SobolevData (foldedCube w r hr I P)) =
        ∫ x in (foldedCube w r hr I P : Set (SpatialCoordinates d)),
          F (coordinateFold (foldedCubeCenter w r I P) I P x) *
            (ψ : SobolevData (foldedCube w r hr I P)).1 x)
    (hGm : AEMeasurable
      (fun x => F (coordinateFold (foldedCubeCenter w r I P) I P x))
      (volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d))))
    (hGb : ∀ᵐ x ∂volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d)),
      |F (coordinateFold (foldedCubeCenter w r I P) I P x)| ≤ MF)
    (af : PositiveCoefficient (foldedCube w r hr (insert i I) P))
    (vf : weakSobolevGraph (foldedCube w r hr (insert i I) P))
    (ha : ((af.val : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d))]
      fun x => a.val
        (coordinateFold (foldedCubeCenter w r (insert i I) P) (insert i I) P x)))
    (hg : ∀ j : Fin d,
      ∀ᵐ x ∂volume.restrict
          (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d)),
        sobolevGradient (vf : SobolevData (foldedCube w r hr (insert i I) P)) j x =
          (if j ∈ insert i I then
            coordinateReflectionSign P j *
              (if x j < foldedCubeCenter w r (insert i I) P j then -1 else 1)
           else 1) *
            sobolevGradient (v : SobolevData (centeredCube w r hr)) j
              (coordinateFold (foldedCubeCenter w r (insert i I) P)
                (insert i I) P x)) :
    (∀ ψ : weakSobolevGraph (foldedCube w r hr (insert i I) P),
      sobolevCoefficientForm af (vf : SobolevData (foldedCube w r hr (insert i I) P))
          (ψ : SobolevData (foldedCube w r hr (insert i I) P)) =
        ∫ x in (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d)),
          F (coordinateFold (foldedCubeCenter w r (insert i I) P) (insert i I) P x) *
            (ψ : SobolevData (foldedCube w r hr (insert i I) P)).1 x) ∧
      AEMeasurable
        (fun x => F (coordinateFold (foldedCubeCenter w r (insert i I) P)
          (insert i I) P x))
        (volume.restrict
          (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d))) ∧
      (∀ᵐ x ∂volume.restrict
          (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d)),
        |F (coordinateFold (foldedCubeCenter w r (insert i I) P)
          (insert i I) P x)| ≤ MF) := by
  obtain ⟨D, hDΩ, hDU, hDz, hDi, hfoldΩ, hfoldR, hfacΩ, hfacR⟩ :=
    aux_lem_even_weak_transport_geometry_up d w r hr I P i hi hiP
  let aD : PositiveCoefficient D.Ω := hDΩ.symm ▸ af0
  let vD : weakSobolevGraph D.Ω :=
    ⟨hDΩ.symm ▸ (vf0 : SobolevData (foldedCube w r hr I P)),
      aux_lem_even_fold_construction_cast_weak D.Ω
        (foldedCube w r hr I P) hDΩ (vf0 : SobolevData (foldedCube w r hr I P))
        vf0.property⟩
  let oldFold : SpatialCoordinates d → SpatialCoordinates d :=
    coordinateFold (foldedCubeCenter w r I P) I P
  let newFold : SpatialCoordinates d → SpatialCoordinates d :=
    coordinateFold (foldedCubeCenter w r (insert i I) P) (insert i I) P
  let oldFac : Fin d → SpatialCoordinates d → ℝ := fun j x =>
    if j ∈ I then coordinateReflectionSign P j *
      (if x j < foldedCubeCenter w r I P j then -1 else 1) else 1
  let newFac : Fin d → SpatialCoordinates d → ℝ := fun j x =>
    if j ∈ insert i I then coordinateReflectionSign P j *
      (if x j < foldedCubeCenter w r (insert i I) P j then -1 else 1) else 1
  let gv : Fin d → SpatialCoordinates d → ℝ := fun j x =>
    sobolevGradient (v : SobolevData (centeredCube w r hr)) j x
  let G0 : SpatialCoordinates d → ℝ := fun x => F (oldFold x)
  let Hnew : SpatialCoordinates d → ℝ := fun x => F (newFold x)
  have hcenter : coordinateFold (foldedCubeCenter w r I P) I P =
      coordinateFold D.z I P := by
    rw [hDz]
    funext x j
    by_cases hj : j ∈ I
    · simp only [coordinateFold, hj, ite_true]
      by_cases hji : j = i
      · exact (hi (hji ▸ hj)).elim
      · simp [foldedCubeCenter, hji]
    · simp [coordinateFold, hj]
  have hEqD : ∀ φ : weakSobolevGraph D.Ω,
      sobolevCoefficientForm aD (vD : SobolevData D.Ω)
          (φ : SobolevData D.Ω) =
        ∫ x in (D.Ω : Set (SpatialCoordinates d)), G0 x *
          (φ : SobolevData D.Ω).1 x := by
    intro φ
    have h := aux_lem_even_weak_transport_cast_equation hDΩ af0 vf0 G0 hprev φ
    simpa [aD, vD, G0, oldFold] using! h
  have haD : ((aD.val : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (D.Ω : Set (SpatialCoordinates d))]
      foldedCoefficientP (a.val : SpatialCoordinates d → ℝ) D.z I P) := by
    have haval := aux_lem_even_fold_construction_cast_positive_val D.Ω
      (foldedCube w r hr I P) hDΩ af0
    rw [haval]
    exact aux_lem_even_fold_construction_cast_lp_ae D.Ω
      (foldedCube w r hr I P) hDΩ af0.val (by
        simpa [foldedCoefficientP, hcenter] using! ha0)
  have hiD : D.i ∉ I := by simpa [hDi] using! hi
  have hcoefD := lane2_evenExtensionCoefficient_fold_up D aD hiD (by rfl) haD
  have hcoef : ((D.evenExtensionCoefficient aD).val : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (D.U : Set (SpatialCoordinates d))]
      fun x => a.val (newFold x) := by
    filter_upwards [hcoefD] with x hx
    simpa [foldedCoefficientP, newFold, hDz, hDi,
      Finset.insert_eq_of_mem hiP] using! hx
  have hbaseΩ : ∀ j : Fin d,
      ∀ᵐ x ∂volume.restrict (D.Ω : Set (SpatialCoordinates d)),
        ((vD : SobolevData D.Ω).2 j : SpatialCoordinates d → ℝ) x =
          oldFac j x * gv j (oldFold x) := by
    intro j
    have hgj := hg0 j
    change ∀ᵐ x ∂volume.restrict
        (foldedCube w r hr I P : Set (SpatialCoordinates d)),
      ((vf0 : SobolevData (foldedCube w r hr I P)).2 j :
        SpatialCoordinates d → ℝ) x = _ at hgj
    have hgj' : ∀ᵐ x ∂volume.restrict
        (foldedCube w r hr I P : Set (SpatialCoordinates d)),
      ((vf0 : SobolevData (foldedCube w r hr I P)).2 j :
        SpatialCoordinates d → ℝ) x = oldFac j x * gv j (oldFold x) := by
      simpa [oldFac, gv, oldFold] using! hgj
    have hc := aux_lem_even_fold_construction_cast_ae D.Ω
      (foldedCube w r hr I P) hDΩ
      ((vf0 : SobolevData (foldedCube w r hr I P)).2 j) hgj'
    have hcomp : (vD : SobolevData D.Ω).2 j = hDΩ.symm ▸
        (vf0 : SobolevData (foldedCube w r hr I P)).2 j := by
      have hc' := congrArg (fun q : SobolevData D.Ω => q.2 j)
        (aux_lem_even_fold_construction_cast_sobolev_components D.Ω
          (foldedCube w r hr I P) hDΩ
          (vf0 : SobolevData (foldedCube w r hr I P)))
      simpa [vD] using! hc'
    rw [hcomp]
    exact hc
  have hbaseR : ∀ j : Fin d,
      ∀ᵐ x ∂volume.restrict (D.reflected : Set (SpatialCoordinates d)),
        ((vD : SobolevData D.Ω).2 j : SpatialCoordinates d → ℝ)
            (coordinateReflection D.z {D.i} x) =
          oldFac j (coordinateReflection D.z {D.i} x) *
            gv j (oldFold (coordinateReflection D.z {D.i} x)) := by
    intro j
    have hm : MeasurePreserving (coordinateReflection D.z {D.i})
        (volume.restrict (D.reflected : Set (SpatialCoordinates d)))
        (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
      coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_Ω
    have h := hm.quasiMeasurePreserving.ae (hbaseΩ j)
    simpa only [Function.comp_apply] using! h
  have hgradD := aux_lem_even_weak_transport_even_gradient D
    (vD : SobolevData D.Ω) newFold oldFold newFac oldFac gv hbaseΩ hbaseR
    (by simpa [newFold, oldFold, hDi] using! hfoldΩ)
    (by simpa [newFold, oldFold, hDi] using! hfoldR)
    (by simpa [newFac, oldFac, hDi] using! hfacΩ)
    (by simpa [newFac, oldFac, hDi] using! hfacR)
  have hreg : AEMeasurable Hnew
      (volume.restrict (D.U : Set (SpatialCoordinates d))) ∧
      (∀ᵐ x ∂volume.restrict (D.U : Set (SpatialCoordinates d)), |Hnew x| ≤ MF) := by
    apply aux_lem_even_weak_transport_piecewise_regular D G0 Hnew MF
    · rw [hDΩ]
      simpa [G0, oldFold] using! hGm
    · rw [hDΩ]
      simpa [G0, oldFold] using! hGb
    · filter_upwards [ae_restrict_mem D.Ω.isOpen.measurableSet] with x hx
      simpa [Hnew, G0, newFold, oldFold] using! congrArg F (hfoldΩ x hx)
    · filter_upwards [ae_restrict_mem D.reflected.isOpen.measurableSet] with x hx
      simpa [Hnew, G0, newFold, oldFold, hDi, Function.comp_apply] using!
        congrArg F (hfoldR x hx)
    · filter_upwards [D.ae_mem_or_mem] with x hx
      rcases hx with hx | hx
      · rw [Set.indicator_of_mem hx,
          Set.indicator_of_notMem (D.notMem_reflected_of_mem_Ω hx), add_zero]
        simpa [Hnew, G0, newFold, oldFold] using! congrArg F (hfoldΩ x hx)
      · rw [Set.indicator_of_notMem (D.notMem_Ω_of_mem_reflected hx),
          Set.indicator_of_mem hx, zero_add]
        simpa [Hnew, G0, newFold, oldFold, hDi, Function.comp_apply] using!
          congrArg F (hfoldR x hx)
  let aE : PositiveCoefficient D.U := D.evenExtensionCoefficient aD
  let uE : weakSobolevGraph D.U :=
    ⟨D.evenExtension (vD : SobolevData D.Ω),
      D.evenExtension_mem_weak vD.property⟩
  have hEqE : ∀ ψD : weakSobolevGraph D.U,
      sobolevCoefficientForm aE (uE : SobolevData D.U)
          (ψD : SobolevData D.U) =
        ∫ x in (D.U : Set (SpatialCoordinates d)), Hnew x *
          (ψD : SobolevData D.U).1 x := by
    intro ψD
    have hregN : AEMeasurable Hnew
        (volume.restrict (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d))) ∧
        (∀ᵐ x ∂volume.restrict
          (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d)), |Hnew x| ≤ MF) := by
      simpa [hDU] using! hreg
    have hboundedU : Bornology.IsBounded (D.U : Set (SpatialCoordinates d)) := by
      rw [hDU]
      exact aux_lem_even_weak_transport_foldedCube_bounded d w r hr (insert i I) P
    have hmem := lane2_memLp_of_bounded_measurable
      hboundedU hreg.1.aestronglyMeasurable (by
        filter_upwards [hreg.2] with x hx
        simpa [Real.norm_eq_abs] using! hx)
    have hIntU : Integrable (fun x => Hnew x *
        (ψD : SobolevData D.U).1 x) (volume.restrict (D.U : Set _)) :=
      hmem.integrable_mul (Lp.memLp (ψD : SobolevData D.U).1)
    have hIntΩ : IntegrableOn (fun x => Hnew x *
        (ψD : SobolevData D.U).1 x) (D.Ω : Set (SpatialCoordinates d)) :=
      hIntU.mono_measure (Measure.restrict_mono D.Ω_le le_rfl)
    have hIntR : IntegrableOn (fun x => Hnew x *
        (ψD : SobolevData D.U).1 x) (D.reflected : Set (SpatialCoordinates d)) :=
      hIntU.mono_measure (Measure.restrict_mono D.reflected_le le_rfl)
    simpa [aE, uE] using! aux_lem_even_weak_transport_one_face D aD
      (vD : SobolevData D.Ω) G0 Hnew hEqD
      (by
        filter_upwards [ae_restrict_mem D.Ω.isOpen.measurableSet] with x hx
        simpa [Hnew, G0, newFold, oldFold] using! congrArg F (hfoldΩ x hx))
      (by
        filter_upwards [ae_restrict_mem D.reflected.isOpen.measurableSet] with x hx
        simpa [Hnew, G0, newFold, oldFold, hDi, Function.comp_apply] using!
          congrArg F (hfoldR x hx)) ψD hIntΩ hIntR
  let hDU' : foldedCube w r hr (insert i I) P = D.U := hDU.symm
  let aN : PositiveCoefficient (foldedCube w r hr (insert i I) P) := hDU'.symm ▸ aE
  let vN : weakSobolevGraph (foldedCube w r hr (insert i I) P) := hDU'.symm ▸ uE
  have hvNdata : vN.1 = hDU'.symm ▸ (uE : SobolevData D.U) := by
    simpa [vN] using!
      (aux_lem_even_weak_transport_cast_weak_coe hDU' uE)
  have hEqN : ∀ ψD : weakSobolevGraph (foldedCube w r hr (insert i I) P),
      sobolevCoefficientForm aN vN.1
          (ψD : SobolevData (foldedCube w r hr (insert i I) P)) =
        ∫ x in (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d)),
          Hnew x * (ψD : SobolevData (foldedCube w r hr (insert i I) P)).1 x := by
    intro ψD
    have h := aux_lem_even_weak_transport_cast_equation hDU' aE uE Hnew hEqE ψD
    simpa [aN, hvNdata] using! h
  have hcoefN : ((aN.val : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d))]
      fun x => a.val (newFold x)) := by
    have hv := aux_lem_even_fold_construction_cast_positive_val
      (foldedCube w r hr (insert i I) P) D.U hDU' aE
    rw [hv]
    exact aux_lem_even_fold_construction_cast_lp_ae
      (foldedCube w r hr (insert i I) P) D.U hDU' aE.val hcoef
  have hgradN : ∀ j : Fin d, ∀ᵐ x ∂volume.restrict
      (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d)),
      sobolevGradient vN.1 j x =
        newFac j x * gv j (newFold x) := by
    have h := aux_lem_even_weak_transport_cast_gradient hDU'
      (uE : SobolevData D.U) (fun j x => newFac j x * gv j (newFold x))
      (by simpa [uE] using! hgradD)
    rw [hvNdata]
    exact h
  have heq : ∀ ψ : weakSobolevGraph (foldedCube w r hr (insert i I) P),
      sobolevCoefficientForm af (vf : SobolevData (foldedCube w r hr (insert i I) P))
          (ψ : SobolevData (foldedCube w r hr (insert i I) P)) =
        ∫ x in (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d)),
          F (newFold x) * (ψ : SobolevData (foldedCube w r hr (insert i I) P)).1 x := by
    intro ψ
    have hfg : ∀ j : Fin d, ∀ᵐ x ∂volume.restrict
        (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d)),
        sobolevGradient (vf : SobolevData (foldedCube w r hr (insert i I) P)) j x =
          sobolevGradient vN.1 j x := by
      intro j
      filter_upwards [hg j, hgradN j] with x hx hy
      exact hx.trans hy.symm
    have hc := aux_lem_even_weak_transport_form_congr af aN
      (ha.trans hcoefN.symm) (vf : SobolevData (foldedCube w r hr (insert i I) P))
      vN.1 hfg
      (ψ : SobolevData (foldedCube w r hr (insert i I) P))
    rw [hc]
    simpa [Hnew, newFold] using! hEqN ψ
  refine ⟨heq, ?_, ?_⟩
  · simpa [Hnew, newFold, hDU] using! hreg.1
  · simpa [Hnew, newFold, hDU] using! hreg.2

lemma aux_lem_even_weak_transport_step_down
    (d : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (I P : Finset (Fin d)) (i : Fin d) (hi : i ∉ I) (hiP : i ∉ P)
    (a : PositiveCoefficient (centeredCube w r hr))
    (v : weakSobolevGraph (centeredCube w r hr))
    (F : SpatialCoordinates d → ℝ) (MF : ℝ)
    (af0 : PositiveCoefficient (foldedCube w r hr I P))
    (vf0 : weakSobolevGraph (foldedCube w r hr I P))
    (ha0 : ((af0.val : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d))]
      fun x => a.val (coordinateFold (foldedCubeCenter w r I P) I P x)))
    (hg0 : ∀ j : Fin d,
      ∀ᵐ x ∂volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d)),
        sobolevGradient (vf0 : SobolevData (foldedCube w r hr I P)) j x =
          (if j ∈ I then
            coordinateReflectionSign P j *
              (if x j < foldedCubeCenter w r I P j then -1 else 1)
           else 1) *
            sobolevGradient (v : SobolevData (centeredCube w r hr)) j
              (coordinateFold (foldedCubeCenter w r I P) I P x))
    (hprev : ∀ ψ : weakSobolevGraph (foldedCube w r hr I P),
      sobolevCoefficientForm af0 (vf0 : SobolevData (foldedCube w r hr I P))
          (ψ : SobolevData (foldedCube w r hr I P)) =
        ∫ x in (foldedCube w r hr I P : Set (SpatialCoordinates d)),
          F (coordinateFold (foldedCubeCenter w r I P) I P x) *
            (ψ : SobolevData (foldedCube w r hr I P)).1 x)
    (hGm : AEMeasurable
      (fun x => F (coordinateFold (foldedCubeCenter w r I P) I P x))
      (volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d))))
    (hGb : ∀ᵐ x ∂volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d)),
      |F (coordinateFold (foldedCubeCenter w r I P) I P x)| ≤ MF)
    (af : PositiveCoefficient (foldedCube w r hr (insert i I) P))
    (vf : weakSobolevGraph (foldedCube w r hr (insert i I) P))
    (ha : ((af.val : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d))]
      fun x => a.val
        (coordinateFold (foldedCubeCenter w r (insert i I) P) (insert i I) P x)))
    (hg : ∀ j : Fin d,
      ∀ᵐ x ∂volume.restrict
          (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d)),
        sobolevGradient (vf : SobolevData (foldedCube w r hr (insert i I) P)) j x =
          (if j ∈ insert i I then
            coordinateReflectionSign P j *
              (if x j < foldedCubeCenter w r (insert i I) P j then -1 else 1)
           else 1) *
            sobolevGradient (v : SobolevData (centeredCube w r hr)) j
              (coordinateFold (foldedCubeCenter w r (insert i I) P)
                (insert i I) P x)) :
    (∀ ψ : weakSobolevGraph (foldedCube w r hr (insert i I) P),
      sobolevCoefficientForm af (vf : SobolevData (foldedCube w r hr (insert i I) P))
          (ψ : SobolevData (foldedCube w r hr (insert i I) P)) =
        ∫ x in (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d)),
          F (coordinateFold (foldedCubeCenter w r (insert i I) P) (insert i I) P x) *
            (ψ : SobolevData (foldedCube w r hr (insert i I) P)).1 x) ∧
      AEMeasurable
        (fun x => F (coordinateFold (foldedCubeCenter w r (insert i I) P)
          (insert i I) P x))
        (volume.restrict
          (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d))) ∧
      (∀ᵐ x ∂volume.restrict
          (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d)),
        |F (coordinateFold (foldedCubeCenter w r (insert i I) P)
          (insert i I) P x)| ≤ MF) := by
  obtain ⟨D, hDref, hDU, hDz, hDi, hfoldΩ, hfoldR, hfacΩ, hfacR⟩ :=
    aux_lem_even_weak_transport_geometry_down d w r hr I P i hi hiP
  let bD : PositiveCoefficient D.reflected := hDref.symm ▸ af0
  let uB : weakSobolevGraph D.reflected :=
    ⟨hDref.symm ▸ (vf0 : SobolevData (foldedCube w r hr I P)),
      aux_lem_even_fold_construction_cast_weak D.reflected
        (foldedCube w r hr I P) hDref (vf0 : SobolevData (foldedCube w r hr I P))
        vf0.property⟩
  let oldFold0 : SpatialCoordinates d → SpatialCoordinates d :=
    coordinateFold (foldedCubeCenter w r I P) I P
  let newFold : SpatialCoordinates d → SpatialCoordinates d :=
    coordinateFold (foldedCubeCenter w r (insert i I) P) (insert i I) P
  let oldFac0 : Fin d → SpatialCoordinates d → ℝ := fun j x =>
    if j ∈ I then coordinateReflectionSign P j *
      (if x j < foldedCubeCenter w r I P j then -1 else 1) else 1
  let oldFold : SpatialCoordinates d → SpatialCoordinates d := fun x =>
    oldFold0 (coordinateReflection D.z {D.i} x)
  let oldFac : Fin d → SpatialCoordinates d → ℝ := fun j x =>
    coordinateReflectionSign {D.i} j *
      oldFac0 j (coordinateReflection D.z {D.i} x)
  let newFac : Fin d → SpatialCoordinates d → ℝ := fun j x =>
    if j ∈ insert i I then coordinateReflectionSign P j *
      (if x j < foldedCubeCenter w r (insert i I) P j then -1 else 1) else 1
  let gv : Fin d → SpatialCoordinates d → ℝ := fun j x =>
    sobolevGradient (v : SobolevData (centeredCube w r hr)) j x
  let G0 : SpatialCoordinates d → ℝ := fun x => F (oldFold0 x)
  let Gd : SpatialCoordinates d → ℝ := fun x => G0 (coordinateReflection D.z {D.i} x)
  let Hnew : SpatialCoordinates d → ℝ := fun x => F (newFold x)
  have hcenter : coordinateFold (foldedCubeCenter w r I P) I P =
      coordinateFold D.z I P := by
    rw [hDz]
    funext x j
    by_cases hj : j ∈ I
    · simp only [coordinateFold, hj, ite_true]
      by_cases hji : j = i
      · exact (hi (hji ▸ hj)).elim
      · simp [foldedCubeCenter, hji]
    · simp [coordinateFold, hj]
  have hEqB : ∀ φ : weakSobolevGraph D.reflected,
      sobolevCoefficientForm bD (uB : SobolevData D.reflected)
          (φ : SobolevData D.reflected) =
        ∫ x in (D.reflected : Set (SpatialCoordinates d)), G0 x *
          (φ : SobolevData D.reflected).1 x := by
    intro φ
    have h := aux_lem_even_weak_transport_cast_equation hDref af0 vf0 G0 hprev φ
    simpa [bD, uB, G0, oldFold0] using! h
  let aD : PositiveCoefficient D.Ω :=
    reflectionCoefficient D.z {D.i} D.preimage_reflected bD
  let uD : SobolevData D.Ω :=
    reflectionSobolevData D.z {D.i} D.preimage_reflected (uB : SobolevData D.reflected)
  have hEqD : ∀ φ : weakSobolevGraph D.Ω,
      sobolevCoefficientForm aD uD (φ : SobolevData D.Ω) =
        ∫ x in (D.Ω : Set (SpatialCoordinates d)), Gd x *
          (φ : SobolevData D.Ω).1 x := by
    intro φ
    simpa [aD, uD, Gd] using!
      aux_lem_even_weak_transport_reflected D bD
        (uB : SobolevData D.reflected) G0 hEqB φ
  have haD : ((bD.val : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (D.reflected : Set (SpatialCoordinates d))]
      foldedCoefficientP (a.val : SpatialCoordinates d → ℝ) D.z I P) := by
    have haval := aux_lem_even_fold_construction_cast_positive_val D.reflected
      (foldedCube w r hr I P) hDref af0
    rw [haval]
    exact aux_lem_even_fold_construction_cast_lp_ae D.reflected
      (foldedCube w r hr I P) hDref af0.val (by
        simpa [foldedCoefficientP, hcenter] using! ha0)
  have hiD : D.i ∉ I := by simpa [hDi] using! hi
  have hcoefD := lane2_evenExtensionCoefficient_fold_down D bD hiD
    (by simpa [hDi] using! hiP) (by rfl) haD
  have hcoef : ((D.evenExtensionCoefficient aD).val : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (D.U : Set (SpatialCoordinates d))]
      fun x => a.val (newFold x) := by
    filter_upwards [hcoefD] with x hx
    simpa [aD, foldedCoefficientP, newFold, hDz, hDi] using! hx
  have hbaseB : ∀ j : Fin d,
      ∀ᵐ x ∂volume.restrict (D.reflected : Set (SpatialCoordinates d)),
        ((uB : SobolevData D.reflected).2 j : SpatialCoordinates d → ℝ) x =
          oldFac0 j x * gv j (oldFold0 x) := by
    intro j
    have hgj := hg0 j
    change ∀ᵐ x ∂volume.restrict
        (foldedCube w r hr I P : Set (SpatialCoordinates d)),
      ((vf0 : SobolevData (foldedCube w r hr I P)).2 j :
        SpatialCoordinates d → ℝ) x = _ at hgj
    have hgj' : ∀ᵐ x ∂volume.restrict
        (foldedCube w r hr I P : Set (SpatialCoordinates d)),
      ((vf0 : SobolevData (foldedCube w r hr I P)).2 j :
        SpatialCoordinates d → ℝ) x = oldFac0 j x * gv j (oldFold0 x) := by
      simpa [oldFac0, gv, oldFold0] using! hgj
    have hc := aux_lem_even_fold_construction_cast_ae D.reflected
      (foldedCube w r hr I P) hDref
      ((vf0 : SobolevData (foldedCube w r hr I P)).2 j) hgj'
    have hcomp : (uB : SobolevData D.reflected).2 j = hDref.symm ▸
        (vf0 : SobolevData (foldedCube w r hr I P)).2 j := by
      have hc' := congrArg (fun q : SobolevData D.reflected => q.2 j)
        (aux_lem_even_fold_construction_cast_sobolev_components D.reflected
          (foldedCube w r hr I P) hDref
          (vf0 : SobolevData (foldedCube w r hr I P)))
      simpa [uB] using! hc'
    rw [hcomp]
    exact hc
  have hmΩ : MeasurePreserving (coordinateReflection D.z {D.i})
      (volume.restrict (D.Ω : Set (SpatialCoordinates d)))
      (volume.restrict (D.reflected : Set (SpatialCoordinates d))) :=
    coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_reflected
  have hbaseΩ : ∀ j : Fin d,
      ∀ᵐ x ∂volume.restrict (D.Ω : Set (SpatialCoordinates d)),
        (uD.2 j : SpatialCoordinates d → ℝ) x =
          oldFac j x * gv j (oldFold x) := by
    intro j
    have href := reflectionSobolevData_gradient_coeFn D.z {D.i}
      D.preimage_reflected (uB : SobolevData D.reflected) j
    have hp := hmΩ.quasiMeasurePreserving.ae (hbaseB j)
    filter_upwards [href, hp] with x hx hrx
    rw [hx, hrx]
    simp only [oldFac, oldFold]
    ring
  have hbaseR : ∀ j : Fin d,
      ∀ᵐ x ∂volume.restrict (D.reflected : Set (SpatialCoordinates d)),
        (uD.2 j : SpatialCoordinates d → ℝ)
            (coordinateReflection D.z {D.i} x) =
          oldFac j (coordinateReflection D.z {D.i} x) *
            gv j (oldFold (coordinateReflection D.z {D.i} x)) := by
    intro j
    have hm : MeasurePreserving (coordinateReflection D.z {D.i})
        (volume.restrict (D.reflected : Set (SpatialCoordinates d)))
        (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
      coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_Ω
    have h := hm.quasiMeasurePreserving.ae (hbaseΩ j)
    simpa only [Function.comp_apply] using! h
  have hfoldΩ' : ∀ x : SpatialCoordinates d, x ∈ D.Ω →
      newFold x = oldFold x := by
    intro x hx
    dsimp [newFold, oldFold]
    simpa [hDi] using! hfoldΩ x hx
  have hfoldR' : ∀ x : SpatialCoordinates d, x ∈ D.reflected →
      newFold x = oldFold (coordinateReflection D.z {D.i} x) := by
    intro x hx
    dsimp [newFold, oldFold]
    rw [coordinateReflection_involutive]
    simpa [hDi] using! hfoldR x hx
  have hfacΩ' : ∀ j x, x ∈ D.Ω → newFac j x = oldFac j x := by
    intro j x hx
    dsimp [newFac, oldFac]
    simpa [oldFac0, hDi] using! hfacΩ j x hx
  have hsourceR : ∀ x : SpatialCoordinates d, x ∈ D.reflected →
      Hnew x = Gd (coordinateReflection D.z {D.i} x) := by
    intro x hx
    dsimp [Hnew, Gd, G0, oldFold, newFold]
    rw [coordinateReflection_involutive]
    simpa [hDi] using! congrArg F (hfoldR x hx)
  have hgradD := aux_lem_even_weak_transport_even_gradient D uD newFold oldFold
    newFac oldFac gv hbaseΩ hbaseR
    hfoldΩ' hfoldR' hfacΩ'
    (by
      intro j x hx
      calc
        newFac j x = oldFac0 j x := hfacR j x hx
        _ = coordinateReflectionSign {D.i} j *
            oldFac j (coordinateReflection D.z {D.i} x) := by
          simp only [oldFac]
          rw [coordinateReflection_involutive]
          have hs : coordinateReflectionSign {D.i} j *
              coordinateReflectionSign {D.i} j = 1 := by
            simpa [pow_two] using! coordinateReflectionSign_sq {D.i} j
          calc
            oldFac0 j x = 1 * oldFac0 j x := by rw [one_mul]
            _ = (coordinateReflectionSign {D.i} j *
                coordinateReflectionSign {D.i} j) * oldFac0 j x := by rw [hs]
            _ = coordinateReflectionSign {D.i} j *
                (coordinateReflectionSign {D.i} j * oldFac0 j x) := by ring)
  have hGmB : AEMeasurable G0
      (volume.restrict (D.reflected : Set (SpatialCoordinates d))) := by
    rw [hDref]
    simpa [G0, oldFold0] using! hGm
  have hGbB : ∀ᵐ x ∂volume.restrict (D.reflected : Set (SpatialCoordinates d)),
      |G0 x| ≤ MF := by
    rw [hDref]
    simpa [G0, oldFold0] using! hGb
  have hGmD : AEMeasurable Gd
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) := by
    simpa [Gd] using! hGmB.comp_quasiMeasurePreserving hmΩ.quasiMeasurePreserving
  have hGbD : ∀ᵐ x ∂volume.restrict (D.Ω : Set (SpatialCoordinates d)),
      |Gd x| ≤ MF := by
    have h := hmΩ.quasiMeasurePreserving.ae hGbB
    simpa [Gd, Function.comp_apply] using! h
  have hreg : AEMeasurable Hnew
      (volume.restrict (D.U : Set (SpatialCoordinates d))) ∧
      (∀ᵐ x ∂volume.restrict (D.U : Set (SpatialCoordinates d)), |Hnew x| ≤ MF) := by
    apply aux_lem_even_weak_transport_piecewise_regular D Gd Hnew MF hGmD hGbD
    · filter_upwards [ae_restrict_mem D.Ω.isOpen.measurableSet] with x hx
      simpa [Hnew, Gd, G0, newFold, oldFold, oldFold0, hDi, Function.comp_apply] using!
        congrArg F (hfoldΩ x hx)
    · filter_upwards [ae_restrict_mem D.reflected.isOpen.measurableSet] with x hx
      exact hsourceR x hx
    · filter_upwards [D.ae_mem_or_mem] with x hx
      rcases hx with hx | hx
      · rw [Set.indicator_of_mem hx,
          Set.indicator_of_notMem (D.notMem_reflected_of_mem_Ω hx), add_zero]
        simpa [Hnew, Gd, G0, newFold, oldFold, oldFold0, hDi, Function.comp_apply] using!
          congrArg F (hfoldΩ x hx)
      · rw [Set.indicator_of_notMem (D.notMem_Ω_of_mem_reflected hx),
          Set.indicator_of_mem hx, zero_add]
        exact hsourceR x hx
  let aE : PositiveCoefficient D.U := D.evenExtensionCoefficient aD
  let uE : weakSobolevGraph D.U :=
    ⟨D.evenExtension uD, D.evenExtension_mem_weak (by
      exact reflectionSobolevData_mem_weak D.z {D.i} D.preimage_reflected uB.property)⟩
  have hEqE : ∀ ψD : weakSobolevGraph D.U,
      sobolevCoefficientForm aE (uE : SobolevData D.U)
          (ψD : SobolevData D.U) =
        ∫ x in (D.U : Set (SpatialCoordinates d)), Hnew x *
          (ψD : SobolevData D.U).1 x := by
    intro ψD
    have hboundedU : Bornology.IsBounded (D.U : Set (SpatialCoordinates d)) := by
      rw [hDU]
      exact aux_lem_even_weak_transport_foldedCube_bounded d w r hr (insert i I) P
    have hmem := lane2_memLp_of_bounded_measurable hboundedU
      hreg.1.aestronglyMeasurable (by
        filter_upwards [hreg.2] with x hx
        simpa [Real.norm_eq_abs] using! hx)
    have hIntU : Integrable (fun x => Hnew x *
        (ψD : SobolevData D.U).1 x) (volume.restrict (D.U : Set _)) :=
      hmem.integrable_mul (Lp.memLp (ψD : SobolevData D.U).1)
    have hIntΩ : IntegrableOn (fun x => Hnew x *
        (ψD : SobolevData D.U).1 x) (D.Ω : Set (SpatialCoordinates d)) :=
      hIntU.mono_measure (Measure.restrict_mono D.Ω_le le_rfl)
    have hIntR : IntegrableOn (fun x => Hnew x *
        (ψD : SobolevData D.U).1 x) (D.reflected : Set (SpatialCoordinates d)) :=
      hIntU.mono_measure (Measure.restrict_mono D.reflected_le le_rfl)
    simpa [aE, uE] using! aux_lem_even_weak_transport_one_face D aD uD Gd Hnew hEqD
      (by
        filter_upwards [ae_restrict_mem D.Ω.isOpen.measurableSet] with x hx
        simpa [Hnew, Gd, G0, newFold, oldFold, oldFold0, hDi, Function.comp_apply] using!
          congrArg F (hfoldΩ x hx))
      (by
        filter_upwards [ae_restrict_mem D.reflected.isOpen.measurableSet] with x hx
        exact hsourceR x hx) ψD hIntΩ hIntR
  let hDU' : foldedCube w r hr (insert i I) P = D.U := hDU.symm
  let aN : PositiveCoefficient (foldedCube w r hr (insert i I) P) := hDU'.symm ▸ aE
  let vN : weakSobolevGraph (foldedCube w r hr (insert i I) P) := hDU'.symm ▸ uE
  have hvNdata : vN.1 = hDU'.symm ▸ (uE : SobolevData D.U) := by
    simpa [vN] using!
      (aux_lem_even_weak_transport_cast_weak_coe hDU' uE)
  have hEqN : ∀ ψD : weakSobolevGraph (foldedCube w r hr (insert i I) P),
      sobolevCoefficientForm aN vN.1
          (ψD : SobolevData (foldedCube w r hr (insert i I) P)) =
        ∫ x in (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d)),
          Hnew x * (ψD : SobolevData (foldedCube w r hr (insert i I) P)).1 x := by
    intro ψD
    have h := aux_lem_even_weak_transport_cast_equation hDU' aE uE Hnew hEqE ψD
    simpa [aN, hvNdata] using! h
  have hcoefN : ((aN.val : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d))]
      fun x => a.val (newFold x)) := by
    have hv := aux_lem_even_fold_construction_cast_positive_val
      (foldedCube w r hr (insert i I) P) D.U hDU' aE
    rw [hv]
    exact aux_lem_even_fold_construction_cast_lp_ae
      (foldedCube w r hr (insert i I) P) D.U hDU' aE.val hcoef
  have hgradN : ∀ j : Fin d, ∀ᵐ x ∂volume.restrict
      (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d)),
      sobolevGradient vN.1 j x = newFac j x * gv j (newFold x) := by
    have h := aux_lem_even_weak_transport_cast_gradient hDU'
      (uE : SobolevData D.U) (fun j x => newFac j x * gv j (newFold x))
      (by simpa [uE] using! hgradD)
    rw [hvNdata]
    exact h
  have heq : ∀ ψ : weakSobolevGraph (foldedCube w r hr (insert i I) P),
      sobolevCoefficientForm af (vf : SobolevData (foldedCube w r hr (insert i I) P))
          (ψ : SobolevData (foldedCube w r hr (insert i I) P)) =
        ∫ x in (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d)),
          F (newFold x) * (ψ : SobolevData (foldedCube w r hr (insert i I) P)).1 x := by
    intro ψ
    have hfg : ∀ j : Fin d, ∀ᵐ x ∂volume.restrict
        (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d)),
        sobolevGradient (vf : SobolevData (foldedCube w r hr (insert i I) P)) j x =
          sobolevGradient vN.1 j x := by
      intro j
      filter_upwards [hg j, hgradN j] with x hx hy
      exact hx.trans hy.symm
    have hc := aux_lem_even_weak_transport_form_congr af aN
      (ha.trans hcoefN.symm) (vf : SobolevData (foldedCube w r hr (insert i I) P))
      vN.1 hfg (ψ : SobolevData (foldedCube w r hr (insert i I) P))
    rw [hc]
    simpa [Hnew, newFold] using! hEqN ψ
  refine ⟨heq, ?_, ?_⟩
  · simpa [Hnew, newFold, hDU] using! hreg.1
  · simpa [Hnew, newFold, hDU] using! hreg.2

lemma aux_lem_even_weak_transport_induction
    (d : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube w r hr))
    (v : weakSobolevGraph (centeredCube w r hr))
    (F : SpatialCoordinates d → ℝ) (MF : ℝ) (hMF : 0 ≤ MF)
    (hF : AEMeasurable F
      (volume.restrict (centeredCube w r hr : Set (SpatialCoordinates d))))
    (hbound : ∀ᵐ x ∂volume.restrict (centeredCube w r hr : Set (SpatialCoordinates d)),
      |F x| ≤ MF)
    (_hmean : (∫ x in (centeredCube w r hr : Set (SpatialCoordinates d)), F x) = 0)
    (heq : ∀ ψ : weakSobolevGraph (centeredCube w r hr),
      sobolevCoefficientForm a (v : SobolevData (centeredCube w r hr))
          (ψ : SobolevData (centeredCube w r hr)) =
        ∫ x in (centeredCube w r hr : Set (SpatialCoordinates d)),
          F x * (ψ : SobolevData (centeredCube w r hr)).1 x) :
    ∀ (I P : Finset (Fin d))
      (af : PositiveCoefficient (foldedCube w r hr I P))
      (vf : weakSobolevGraph (foldedCube w r hr I P)),
      ((af.val : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d))]
        fun x => a.val (coordinateFold (foldedCubeCenter w r I P) I P x)) →
      (∀ j : Fin d,
        ∀ᵐ x ∂volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d)),
          sobolevGradient (vf : SobolevData (foldedCube w r hr I P)) j x =
            (if j ∈ I then
              coordinateReflectionSign P j *
                (if x j < foldedCubeCenter w r I P j then -1 else 1)
             else 1) *
              sobolevGradient (v : SobolevData (centeredCube w r hr)) j
                (coordinateFold (foldedCubeCenter w r I P) I P x)) →
      (∀ ψ : weakSobolevGraph (foldedCube w r hr I P),
        sobolevCoefficientForm af (vf : SobolevData (foldedCube w r hr I P))
            (ψ : SobolevData (foldedCube w r hr I P)) =
          ∫ x in (foldedCube w r hr I P : Set (SpatialCoordinates d)),
            F (coordinateFold (foldedCubeCenter w r I P) I P x) *
              (ψ : SobolevData (foldedCube w r hr I P)).1 x) ∧
      AEMeasurable
        (fun x => F (coordinateFold (foldedCubeCenter w r I P) I P x))
        (volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d))) ∧
      (∀ᵐ x ∂volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d)),
        |F (coordinateFold (foldedCubeCenter w r I P) I P x)| ≤ MF) := by
  intro I
  induction I using Finset.induction_on with
  | empty =>
      intro P af vf ha hg
      exact aux_lem_even_weak_transport_base d w r hr P a v F MF hMF hF hbound
        heq af vf ha hg
  | @insert i I hi ih =>
      intro P af vf ha hg
      obtain ⟨af0, vf0, ha0, hv0, hg0⟩ :=
        aux_lem_even_fold_construction_induction d w r hr I P a v
      obtain ⟨hprev, hGm, hGb⟩ := ih P af0 vf0 ha0 hg0
      by_cases hiP : i ∈ P
      · exact aux_lem_even_weak_transport_step_up d w r hr I P i hi hiP a v F MF
          af0 vf0 ha0 hg0 hprev hGm hGb af vf ha hg
      · exact aux_lem_even_weak_transport_step_down d w r hr I P i hi hiP a v F MF
          af0 vf0 ha0 hg0 hprev hGm hGb af vf ha hg



theorem lem_even_weak_transport
  (d : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
  (I P : Finset (Fin d))
  (a : PositiveCoefficient (centeredCube w r hr))
  (v : weakSobolevGraph (centeredCube w r hr))
  (af : PositiveCoefficient (foldedCube w r hr I P))
  (vf : weakSobolevGraph (foldedCube w r hr I P))
  (ha : ((af.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d))]
    fun x => a.val (coordinateFold (foldedCubeCenter w r I P) I P x)))
  (hg : (∀ j : Fin d,
    ∀ᵐ x ∂volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d)),
      sobolevGradient (vf : SobolevData (foldedCube w r hr I P)) j x =
        (if j ∈ I then
          coordinateReflectionSign P j *
            (if x j < foldedCubeCenter w r I P j then -1 else 1)
         else 1) *
          sobolevGradient (v : SobolevData (centeredCube w r hr)) j
            (coordinateFold (foldedCubeCenter w r I P) I P x)))
  (F : SpatialCoordinates d → ℝ) (MF : ℝ) (hMF : 0 ≤ MF)
  (hF : AEMeasurable F
    (volume.restrict (centeredCube w r hr : Set (SpatialCoordinates d))))
  (hbound : ∀ᵐ x ∂volume.restrict (centeredCube w r hr : Set (SpatialCoordinates d)),
    |F x| ≤ MF)
  (hmean : (∫ x in (centeredCube w r hr : Set (SpatialCoordinates d)), F x) = 0)
  (heq : ∀ ψ : weakSobolevGraph (centeredCube w r hr),
    sobolevCoefficientForm a (v : SobolevData (centeredCube w r hr))
        (ψ : SobolevData (centeredCube w r hr)) =
      ∫ x in (centeredCube w r hr : Set (SpatialCoordinates d)),
        F x * (ψ : SobolevData (centeredCube w r hr)).1 x) :
  ∀ ψ : weakSobolevGraph (foldedCube w r hr I P),
    sobolevCoefficientForm af (vf : SobolevData (foldedCube w r hr I P))
        (ψ : SobolevData (foldedCube w r hr I P)) =
      ∫ x in (foldedCube w r hr I P : Set (SpatialCoordinates d)),
        F (coordinateFold (foldedCubeCenter w r I P) I P x) *
          (ψ : SobolevData (foldedCube w r hr I P)).1 x := by
  intro ψ
  exact (aux_lem_even_weak_transport_induction d w r hr a v F MF hMF hF hbound
    hmean heq I P af vf ha hg).1 ψ

end SubdiffusiveProcess.Paper
