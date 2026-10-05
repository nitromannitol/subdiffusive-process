module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.BoundaryEnergy
public import SubdiffusiveProcess.VariationalResponses.FoldedIteration
public import SubdiffusiveProcess.Paper.lem_even_fold_partition
public import SubdiffusiveProcess.Paper.lem_even_fold_face_gluing

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity

noncomputable section
namespace SubdiffusiveProcess.Paper

lemma aux_lem_even_fold_construction_cast_ae
    {d : ℕ} (Ω₁ Ω₂ : Opens (SpatialCoordinates d)) (hΩ : Ω₁ = Ω₂)
    (f : DomainL2 Ω₂) {g : SpatialCoordinates d → ℝ}
    (hf : (f : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (Ω₂ : Set (SpatialCoordinates d))] g) :
    ((hΩ.symm ▸ f : DomainL2 Ω₁) : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (Ω₁ : Set (SpatialCoordinates d))] g := by
  subst hΩ
  exact hf

lemma aux_lem_even_fold_construction_cast_weak
    {d : ℕ} (Ω₁ Ω₂ : Opens (SpatialCoordinates d)) (hΩ : Ω₁ = Ω₂)
    (u : SobolevData Ω₂) (hu : u ∈ weakSobolevGraph Ω₂) :
    hΩ.symm ▸ u ∈ weakSobolevGraph Ω₁ := by
  subst hΩ
  exact hu

lemma aux_lem_even_fold_construction_cast_lp_ae
    {d : ℕ} {p : ℝ≥0∞} (Ω₁ Ω₂ : Opens (SpatialCoordinates d))
    (hΩ : Ω₁ = Ω₂) (f : Lp ℝ p (volume.restrict (Ω₂ : Set (SpatialCoordinates d))))
    {g : SpatialCoordinates d → ℝ}
    (hf : (f : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (Ω₂ : Set (SpatialCoordinates d))] g) :
    ((hΩ.symm ▸ f : Lp ℝ p (volume.restrict (Ω₁ : Set (SpatialCoordinates d)))) :
      SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (Ω₁ : Set (SpatialCoordinates d))] g := by
  subst hΩ
  exact hf

lemma aux_lem_even_fold_construction_cast_positive_val
    {d : ℕ} (Ω₁ Ω₂ : Opens (SpatialCoordinates d)) (hΩ : Ω₁ = Ω₂)
    (a : PositiveCoefficient Ω₂) :
    (hΩ.symm ▸ a : PositiveCoefficient Ω₁).val = hΩ.symm ▸ a.val := by
  subst hΩ
  rfl

lemma aux_lem_even_fold_construction_cast_sobolev_components
    {d : ℕ} (Ω₁ Ω₂ : Opens (SpatialCoordinates d)) (hΩ : Ω₁ = Ω₂)
    (u : SobolevData Ω₂) :
    hΩ.symm ▸ u =
      (hΩ.symm ▸ u.1, fun j : Fin d => hΩ.symm ▸ u.2 j) := by
  subst hΩ
  rfl

lemma aux_lem_even_fold_construction_cast_weak_components
    {d : ℕ} (Ω₁ Ω₂ : Opens (SpatialCoordinates d)) (hΩ : Ω₁ = Ω₂)
    (u : SobolevData Ω₂) (hu : u ∈ weakSobolevGraph Ω₂) :
    (hΩ.symm ▸ u.1, fun j : Fin d => hΩ.symm ▸ u.2 j) ∈
      weakSobolevGraph Ω₁ := by
  subst hΩ
  exact hu

lemma aux_lem_even_fold_construction_up
  (d : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
  (I P : Finset (Fin d)) (i : Fin d) (hi : i ∉ I)
  (a : PositiveCoefficient (centeredCube w r hr))
  (v : weakSobolevGraph (centeredCube w r hr))
  (af : PositiveCoefficient (foldedCube w r hr I P))
  (vf : weakSobolevGraph (foldedCube w r hr I P))
  (ha : ((af.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d))]
    fun x => a.val (coordinateFold (foldedCubeCenter w r I P) I P x)))
  (hv : (((vf : SobolevData (foldedCube w r hr I P)).1 :
      SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d))]
    fun x => (v : SobolevData (centeredCube w r hr)).1
      (coordinateFold (foldedCubeCenter w r I P) I P x)))
  (hg : ∀ j : Fin d,
    ∀ᵐ x ∂volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d)),
      sobolevGradient (vf : SobolevData (foldedCube w r hr I P)) j x =
        (if j ∈ I then
          coordinateReflectionSign P j *
            (if x j < foldedCubeCenter w r I P j then -1 else 1)
         else 1) *
          sobolevGradient (v : SobolevData (centeredCube w r hr)) j
            (coordinateFold (foldedCubeCenter w r I P) I P x))
  (hiP : i ∈ P) :
  ∃ (af' : PositiveCoefficient (foldedCube w r hr (insert i I) P))
    (vf' : weakSobolevGraph (foldedCube w r hr (insert i I) P)),
    ((af'.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict
          (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d))]
    fun x => a.val
      (coordinateFold (foldedCubeCenter w r (insert i I) P) (insert i I) P x)) ∧
    (((vf' : SobolevData (foldedCube w r hr (insert i I) P)).1 :
        SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict
          (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d))]
    fun x => (v : SobolevData (centeredCube w r hr)).1
      (coordinateFold (foldedCubeCenter w r (insert i I) P) (insert i I) P x)) ∧
    (∀ j : Fin d,
      ∀ᵐ x ∂volume.restrict
          (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d)),
        sobolevGradient (vf' :
            SobolevData (foldedCube w r hr (insert i I) P)) j x =
          (if j ∈ insert i I then
            coordinateReflectionSign P j *
              (if x j < foldedCubeCenter w r (insert i I) P j then -1 else 1)
           else 1) *
            sobolevGradient (v : SobolevData (centeredCube w r hr)) j
              (coordinateFold (foldedCubeCenter w r (insert i I) P)
                (insert i I) P x)) := by
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
              have hnew : x i ∈ Set.Ioo (w i - r / 2) (w i + 3 * r / 2) := by
                exact ⟨hxj'.1, by linarith [hxj'.2, hr]⟩
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
            simp only [coordinateReflection_single_apply_self]
              at hxj'
            rcases hxj' with ⟨hx1, hx2⟩
            have htarget : x i ∈
                Set.Ioo (w i - r / 2) (w i + 3 * r / 2) := by
              have hz : z i = w i + r / 2 := by
                simp [z, foldedCubeCenter, hiP]
              constructor <;> linarith [hx1, hx2, hr, hz]
            simpa [Finset.mem_insert, hiP] using! htarget
          · simpa [coordinateReflection, Finset.mem_singleton, hji,
              Finset.mem_insert, hji] using! hxj
        · have hxj := hx j hjj
          by_cases hji : j = i
          · subst j
            have hxj' : x i ∈ Set.Ioo (w i - r / 2) (w i + 3 * r / 2) := by
              simpa [Finset.mem_insert, hiP] using! hxj
            rcases hxj' with ⟨hx1, hx2⟩
            have htarget : coordinateReflection z {i} x i ∈
                Set.Ioo (w i - r / 2) (w i + 3 * r / 2) := by
              simp only [coordinateReflection_single_apply_self]
              have hz : z i = w i + r / 2 := by
                simp [z, foldedCubeCenter, hiP]
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
  have hfold_le (x : SpatialCoordinates d) (hx : x ∈ (D.Ω : Set _)) :
      coordinateFold z (insert i I) P x = coordinateFold z₀ I P x := by
    have hxi : x i ≤ z i :=
      le_of_lt ((D.mem_iff x).mp hx |>.2)
    calc
      coordinateFold z (insert i I) P x =
          coordinateFold z I (insert i P) x := by
            simpa [Finset.insert_eq_of_mem hiP] using
              (lane2_fold_insert_both_of_le (z := z) (I := I) (P := P)
                (i := i) hi hxi)
      _ = coordinateFold z I P x := by simp [Finset.insert_eq_of_mem hiP]
      _ = coordinateFold z₀ I P x := by rw [hcenter]
  have hfold_ge (x : SpatialCoordinates d) (hx : x ∈ (D.reflected : Set _)) :
      coordinateFold z (insert i I) P x =
        coordinateFold z₀ I P (coordinateReflection z {i} x) := by
    have hxi : z i ≤ x i :=
      le_of_lt ((D.mem_reflected_iff x).mp hx |>.2)
    calc
      coordinateFold z (insert i I) P x =
          coordinateFold z I (insert i P) (coordinateReflection z {i} x) := by
            simpa [Finset.insert_eq_of_mem hiP] using
              (lane2_fold_insert_both_of_ge (z := z) (I := I) (P := P)
                (i := i) hi hxi)
      _ = coordinateFold z I P (coordinateReflection z {i} x) := by
            simp [Finset.insert_eq_of_mem hiP]
      _ = coordinateFold z₀ I P (coordinateReflection z {i} x) := by
            rw [hcenter]
  have haD : ((af.val : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (D.Ω : Set (SpatialCoordinates d))]
      foldedCoefficientP (a.val : SpatialCoordinates d → ℝ) z I P) := by
    filter_upwards [ha] with x hx
    rw [hx]
    simp only [foldedCoefficientP]
    rw [hcenter]
  have hcoef := lane2_evenExtensionCoefficient_fold_up D af hi
    (z := z) (a := (a.val : SpatialCoordinates d → ℝ))
    (I := I) (P := P)
    (by simp [D, z, foldedCubeCenter, hiP, hi]) haD
  let af' : PositiveCoefficient (foldedCube w r hr (insert i I) P) :=
    D.evenExtensionCoefficient af
  let vf' : weakSobolevGraph (foldedCube w r hr (insert i I) P) :=
    ⟨D.evenExtension vf, D.evenExtension_mem_weak vf.property⟩
  refine ⟨af', vf', ?_, ?_, ?_⟩
  · simpa [af', D, foldedCoefficientP, Finset.insert_eq_of_mem hiP] using! hcoef
  · have hfe := D.evenExtension_fst_coeFn vf
    have hvU := ae_restrict_of_ae (s := (D.U : Set _))
      ((ae_restrict_iff' D.Ω.isOpen.measurableSet).mp hv)
    have hm : MeasurePreserving (coordinateReflection D.z {D.i})
        (volume.restrict (D.reflected : Set _))
        (volume.restrict (D.Ω : Set _)) :=
      coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_Ω
    have hvR := hm.quasiMeasurePreserving.ae hv
    have hvRU := ae_restrict_of_ae (s := (D.U : Set _))
      ((ae_restrict_iff' D.reflected.isOpen.measurableSet).mp hvR)
    have hmem := D.ae_mem_or_mem
    have hfe' := hfe
    filter_upwards [hfe', hvU, hvRU, hmem] with x hxe hxvΩ hxvR hxmem
    rcases hxmem with hxΩ | hxR
    · have hxR' : x ∉ (D.reflected : Set _) := D.notMem_reflected_of_mem_Ω hxΩ
      rw [hxe, Set.indicator_of_mem hxΩ, Set.indicator_of_notMem hxR', add_zero,
        hxvΩ hxΩ]
      rw [hfold_le x hxΩ]
    · have hxΩ' : x ∉ (D.Ω : Set _) := D.notMem_Ω_of_mem_reflected hxR
      rw [hxe, Set.indicator_of_notMem hxΩ', Set.indicator_of_mem hxR, zero_add]
      change (vf : SobolevData (foldedCube w r hr I P)).1
          (coordinateReflection D.z {D.i} x) = _
      rw [hxvR hxR, hfold_ge x hxR]
  · intro j
    change ∀ᵐ x ∂volume.restrict
        (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d)),
      ((D.evenExtension vf).2 j : SpatialCoordinates d → ℝ) x = _
    have hge := D.evenExtension_snd_coeFn vf j
    have hgj := hg j
    change ∀ᵐ x ∂volume.restrict
        (foldedCube w r hr I P : Set (SpatialCoordinates d)),
        ((vf : SobolevData (foldedCube w r hr I P)).2 j :
          SpatialCoordinates d → ℝ) x = _ at hgj
    have hgjU := ae_restrict_of_ae (s := (D.U : Set _))
      ((ae_restrict_iff' D.Ω.isOpen.measurableSet).mp hgj)
    have hm : MeasurePreserving (coordinateReflection D.z {D.i})
        (volume.restrict (D.reflected : Set _))
        (volume.restrict (D.Ω : Set _)) :=
      coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_Ω
    have hgjR := hm.quasiMeasurePreserving.ae hgj
    have hgjRU := ae_restrict_of_ae (s := (D.U : Set _))
      ((ae_restrict_iff' D.reflected.isOpen.measurableSet).mp hgjR)
    have hmem := D.ae_mem_or_mem
    filter_upwards [hge, hgjU, hgjRU, hmem] with x hxe hxgΩ hxgR hxmem
    rcases hxmem with hxΩ | hxR
    · have hxR' : x ∉ (D.reflected : Set _) := D.notMem_reflected_of_mem_Ω hxΩ
      have hfac_le :
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
          have hxi : x i < z i := (D.mem_iff x).mp hxΩ |>.2
          have hxi' : x i < w i + r / 2 := by
            simpa [z, foldedCubeCenter, hiP] using! hxi
          simp [hi, hiP, foldedCubeCenter, coordinateReflectionSign, hxi']
        · by_cases hj : j ∈ I
          · have hnew : foldedCubeCenter w r (insert i I) P j =
                foldedCubeCenter w r I P j := by
              simp [foldedCubeCenter, hji, hj]
            simp [Finset.mem_insert, hji, hj, hnew]
          · simp [Finset.mem_insert, hji, hj]
      rw [hxe, Set.indicator_of_mem hxΩ, Set.indicator_of_notMem hxR', add_zero]
      rw [hxgΩ hxΩ, hfac_le]
      have hfold_le' : coordinateFold (foldedCubeCenter w r (insert i I) P)
          (insert i I) P x = coordinateFold (foldedCubeCenter w r I P) I P x := by
        simpa [z] using! hfold_le x hxΩ
      rw [hfold_le']
    · have hxΩ' : x ∉ (D.Ω : Set _) := D.notMem_Ω_of_mem_reflected hxR
      have hfac_ge :
          (if j ∈ insert i I then
              coordinateReflectionSign P j *
                (if x j < foldedCubeCenter w r (insert i I) P j then -1 else 1)
           else 1) =
            coordinateReflectionSign {i} j *
              (if j ∈ I then
                coordinateReflectionSign P j *
                  (if (coordinateReflection z {i} x) j <
                      foldedCubeCenter w r I P j then -1 else 1)
               else 1) := by
        by_cases hji : j = i
        · subst j
          have hxi : z i < x i := (D.mem_reflected_iff x).mp hxR |>.2
          have hxi' : w i + r / 2 < x i := by
            simpa [z, foldedCubeCenter, hiP] using! hxi
          have hnlt : ¬ x i < w i + r / 2 := by linarith
          simp [hi, hiP, foldedCubeCenter, coordinateReflectionSign, hnlt]
        · have hRj : (coordinateReflection z {i} x) j = x j :=
            coordinateReflection_single_apply_of_ne z hji x
          have hnew : foldedCubeCenter w r (insert i I) P j =
                foldedCubeCenter w r I P j := by
            simp [foldedCubeCenter, hji]
          simp [Finset.mem_insert, hji, hnew, hRj,
            coordinateReflectionSign]
      have hfac_ge' :
          (if j ∈ insert i I then
              coordinateReflectionSign P j *
                (if x j < foldedCubeCenter w r (insert i I) P j then -1 else 1)
           else 1) =
            coordinateReflectionSign {D.i} j *
              (if j ∈ I then
                coordinateReflectionSign P j *
                  (if (coordinateReflection D.z {D.i} x) j <
                      foldedCubeCenter w r I P j then -1 else 1)
               else 1) := by
        simpa [D, z] using! hfac_ge
      rw [hxe, Set.indicator_of_notMem hxΩ', Set.indicator_of_mem hxR, zero_add]
      change coordinateReflectionSign {D.i} j *
          ((vf : SobolevData (foldedCube w r hr I P)).2 j :
            SpatialCoordinates d → ℝ) (coordinateReflection D.z {D.i} x) = _
      rw [hxgR hxR]
      rw [← mul_assoc, ← hfac_ge']
      have hfold_ge' : coordinateFold (foldedCubeCenter w r (insert i I) P)
          (insert i I) P x = coordinateFold z₀ I P (coordinateReflection z {i} x) := by
        simpa [D, z] using! hfold_ge x hxR
      rw [hfold_ge']


lemma aux_lem_even_fold_construction_down
  (d : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
  (I P : Finset (Fin d)) (i : Fin d) (hi : i ∉ I)
  (a : PositiveCoefficient (centeredCube w r hr))
  (v : weakSobolevGraph (centeredCube w r hr))
  (af : PositiveCoefficient (foldedCube w r hr I P))
  (vf : weakSobolevGraph (foldedCube w r hr I P))
  (ha : ((af.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d))]
    fun x => a.val (coordinateFold (foldedCubeCenter w r I P) I P x)))
  (hv : (((vf : SobolevData (foldedCube w r hr I P)).1 :
      SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d))]
    fun x => (v : SobolevData (centeredCube w r hr)).1
      (coordinateFold (foldedCubeCenter w r I P) I P x)))
  (hg : ∀ j : Fin d,
    ∀ᵐ x ∂volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d)),
      sobolevGradient (vf : SobolevData (foldedCube w r hr I P)) j x =
        (if j ∈ I then
          coordinateReflectionSign P j *
            (if x j < foldedCubeCenter w r I P j then -1 else 1)
         else 1) *
          sobolevGradient (v : SobolevData (centeredCube w r hr)) j
            (coordinateFold (foldedCubeCenter w r I P) I P x))
  (hiP : i ∉ P) :
  ∃ (af' : PositiveCoefficient (foldedCube w r hr (insert i I) P))
    (vf' : weakSobolevGraph (foldedCube w r hr (insert i I) P)),
    ((af'.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict
          (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d))]
    fun x => a.val
      (coordinateFold (foldedCubeCenter w r (insert i I) P) (insert i I) P x)) ∧
    (((vf' : SobolevData (foldedCube w r hr (insert i I) P)).1 :
        SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict
          (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d))]
    fun x => (v : SobolevData (centeredCube w r hr)).1
      (coordinateFold (foldedCubeCenter w r (insert i I) P) (insert i I) P x)) ∧
    (∀ j : Fin d,
      ∀ᵐ x ∂volume.restrict
          (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d)),
        sobolevGradient (vf' :
            SobolevData (foldedCube w r hr (insert i I) P)) j x =
          (if j ∈ insert i I then
            coordinateReflectionSign P j *
              (if x j < foldedCubeCenter w r (insert i I) P j then -1 else 1)
           else 1) *
            sobolevGradient (v : SobolevData (centeredCube w r hr)) j
              (coordinateFold (foldedCubeCenter w r (insert i I) P)
                (insert i I) P x)) := by
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
              have hxi : x i ∈
                  Set.Ioo (w i - 3 * r / 2) (w i + r / 2) := by
                have hz : z i = w i - r / 2 := by
                  simp [z, foldedCubeCenter, hiP]
                have hxj'' := hxj'
                rw [coordinateReflection_single_apply_self] at hxj''
                rcases hxj'' with ⟨hx1, hx2⟩
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
            have hxj' : x i ∈
                Set.Ioo (w i - 3 * r / 2) (w i + r / 2) := by
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
  have hfold_lower (x : SpatialCoordinates d) (hx : x ∈ (D.Ω : Set _)) :
      coordinateFold z (insert i I) P x =
        coordinateFold z₀ I P (coordinateReflection z {i} x) := by
    have hxi : x i ≤ z i :=
      le_of_lt ((D.mem_iff x).mp hx |>.2)
    calc
      coordinateFold z (insert i I) P x =
          coordinateFold z I P (coordinateReflection z {i} x) := by
            simpa using
              (lane2_fold_insert_I_of_le (z := z) (I := I) (P := P)
                (i := i) hi hiP hxi)
      _ = coordinateFold z₀ I P (coordinateReflection z {i} x) := by
            rw [hcenter]
  have hfold_upper (x : SpatialCoordinates d) (hx : x ∈ (D.reflected : Set _)) :
      coordinateFold z (insert i I) P x = coordinateFold z₀ I P x := by
    have hxi : z i ≤ x i :=
      le_of_lt ((D.mem_reflected_iff x).mp hx |>.2)
    calc
      coordinateFold z (insert i I) P x = coordinateFold z I P x := by
            simpa using
              (lane2_fold_insert_I_of_ge (z := z) (I := I) (P := P)
                (i := i) hi hiP hxi)
      _ = coordinateFold z₀ I P x := by rw [hcenter]
  let afD : PositiveCoefficient D.reflected :=
    hDref.symm ▸ af
  let vfD : SobolevData D.reflected :=
    hDref.symm ▸ (vf : SobolevData (foldedCube w r hr I P))
  have hcast : vfD =
      (hDref.symm ▸ (vf : SobolevData (foldedCube w r hr I P)).1,
        fun j : Fin d => hDref.symm ▸
          (vf : SobolevData (foldedCube w r hr I P)).2 j) := by
    simpa [vfD] using
      (aux_lem_even_fold_construction_cast_sobolev_components D.reflected
        (foldedCube w r hr I P) hDref
        (vf : SobolevData (foldedCube w r hr I P)))
  have haD : ((afD.val : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (D.reflected : Set (SpatialCoordinates d))]
      foldedCoefficientP (a.val : SpatialCoordinates d → ℝ) z I P) := by
    have haval := aux_lem_even_fold_construction_cast_positive_val D.reflected
      (foldedCube w r hr I P) hDref af
    rw [haval]
    have haD0 := aux_lem_even_fold_construction_cast_lp_ae D.reflected
      (foldedCube w r hr I P) hDref af.val (by
        simpa [foldedCoefficientP, hcenter] using! ha)
    filter_upwards [haD0] with x hx
    change (hDref.symm ▸ af.val : Lp ℝ ∞
        (volume.restrict (D.reflected : Set _))) x =
      a.val (coordinateFold z I P x)
    rw [hcenter] at hx
    exact hx
  have hcoef := lane2_evenExtensionCoefficient_fold_down D afD hi hiP
    (by simp [D, z, foldedCubeCenter, hiP, hi]) haD
  let af' : PositiveCoefficient (foldedCube w r hr (insert i I) P) :=
    D.evenExtensionCoefficient
      (reflectionCoefficient D.z {D.i} D.preimage_reflected afD)
  let u₀ : SobolevData D.Ω :=
    reflectionSobolevData D.z {D.i} D.preimage_reflected vfD
  have hvfD : vfD ∈ weakSobolevGraph D.reflected := by
    have hc := aux_lem_even_fold_construction_cast_weak_components D.reflected
      (foldedCube w r hr I P) hDref (vf : SobolevData (foldedCube w r hr I P))
      vf.property
    simpa [hcast] using! hc
  have hu₀ : u₀ ∈ weakSobolevGraph D.Ω := by
    exact reflectionSobolevData_mem_weak D.z {D.i} D.preimage_reflected hvfD
  let vf' : weakSobolevGraph (foldedCube w r hr (insert i I) P) :=
    ⟨D.evenExtension u₀, D.evenExtension_mem_weak hu₀⟩
  refine ⟨af', vf', ?_, ?_, ?_⟩
  · simpa [af', D, foldedCoefficientP] using! hcoef
  · change ((D.evenExtension u₀).1 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (D.U : Set (SpatialCoordinates d))] _
    have hu₀L := reflectionLp_coeFn D.z {D.i} D.preimage_reflected vfD.1
    have hu₀L0 : ((u₀.1 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (D.Ω : Set _)]
        fun x => (vfD.1 : SpatialCoordinates d → ℝ)
          (coordinateReflection D.z {D.i} x)) := by
      change ((reflectionLp D.z {D.i} D.preimage_reflected vfD.1 :
        SpatialCoordinates d → ℝ) =ᵐ[_] _)
      simpa only [Function.comp_apply] using! hu₀L
    have hmR : MeasurePreserving (coordinateReflection D.z {D.i})
        (volume.restrict (D.reflected : Set _))
        (volume.restrict (D.Ω : Set _)) :=
      coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_Ω
    have hmL : MeasurePreserving (coordinateReflection D.z {D.i})
        (volume.restrict (D.Ω : Set _))
        (volume.restrict (D.reflected : Set _)) :=
      coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_reflected
    have hu₀Rraw := hmR.quasiMeasurePreserving.ae hu₀L0
    have hu₀R : ((u₀.1 : SpatialCoordinates d → ℝ) ∘
        coordinateReflection D.z {D.i}) =ᵐ[
          volume.restrict (D.reflected : Set _)]
        (vfD.1 : SpatialCoordinates d → ℝ) := by
      filter_upwards [hu₀Rraw] with x hx
      change (u₀.1 : SpatialCoordinates d → ℝ)
          (coordinateReflection D.z {D.i} x) =
        (vfD.1 : SpatialCoordinates d → ℝ)
          (coordinateReflection D.z {D.i}
            (coordinateReflection D.z {D.i} x)) at hx
      rw [coordinateReflection_involutive] at hx
      exact hx
    have hu₀R' := ae_restrict_of_ae (s := (D.U : Set _))
      ((ae_restrict_iff' D.reflected.isOpen.measurableSet).mp hu₀R)
    have hu₀L' := ae_restrict_of_ae (s := (D.U : Set _))
      ((ae_restrict_iff' D.Ω.isOpen.measurableSet).mp hu₀L0)
    have hvD : ((vfD.1 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (D.reflected : Set _)]
        fun x => (v : SobolevData (centeredCube w r hr)).1
          (coordinateFold z₀ I P x)) := by
      have hvD0 := aux_lem_even_fold_construction_cast_ae D.reflected
        (foldedCube w r hr I P) hDref
        (vf : SobolevData (foldedCube w r hr I P)).1 hv
      have hfst := congrArg Prod.fst hcast
      rw [hfst]
      simpa [z₀] using! hvD0
    have hvU := ae_restrict_of_ae (s := (D.U : Set _))
      ((ae_restrict_iff' D.reflected.isOpen.measurableSet).mp hvD)
    have hvL := hmL.quasiMeasurePreserving.ae hvD
    have hvLU := ae_restrict_of_ae (s := (D.U : Set _))
      ((ae_restrict_iff' D.Ω.isOpen.measurableSet).mp hvL)
    have hfe := D.evenExtension_fst_coeFn u₀
    have hmem := D.ae_mem_or_mem
    filter_upwards [hfe, hu₀L', hu₀R', hvLU, hvU, hmem]
      with x hxe hxul hxur hxvl hxvu hxmem
    rcases hxmem with hxΩ | hxR
    · have hxR' : x ∉ (D.reflected : Set _) := D.notMem_reflected_of_mem_Ω hxΩ
      have hfold : coordinateFold (foldedCubeCenter w r (insert i I) P)
          (insert i I) P x = coordinateFold z₀ I P
            (coordinateReflection z {i} x) := by
        simpa [z] using! hfold_lower x hxΩ
      calc
        ((D.evenExtension u₀).1 : SpatialCoordinates d → ℝ) x =
            (D.Ω : Set (SpatialCoordinates d)).indicator
                (u₀.1 : SpatialCoordinates d → ℝ) x +
              (D.reflected : Set (SpatialCoordinates d)).indicator
                ((u₀.1 : SpatialCoordinates d → ℝ) ∘
                  coordinateReflection D.z {D.i}) x := hxe
        _ = (u₀.1 : SpatialCoordinates d → ℝ) x := by
          rw [Set.indicator_of_mem hxΩ, Set.indicator_of_notMem hxR', add_zero]
        _ =
            (vfD.1 : SpatialCoordinates d → ℝ)
              (coordinateReflection z {i} x) := hxul hxΩ
        _ = (v : SobolevData (centeredCube w r hr)).1
              (coordinateFold z₀ I P (coordinateReflection z {i} x)) :=
            hxvl hxΩ
        _ = (v : SobolevData (centeredCube w r hr)).1
              (coordinateFold (foldedCubeCenter w r (insert i I) P)
                (insert i I) P x) := by rw [hfold]
    · have hxΩ' : x ∉ (D.Ω : Set _) := D.notMem_Ω_of_mem_reflected hxR
      have hfold : coordinateFold (foldedCubeCenter w r (insert i I) P)
          (insert i I) P x = coordinateFold z₀ I P x := by
        simpa [z] using! hfold_upper x hxR
      calc
        ((D.evenExtension u₀).1 : SpatialCoordinates d → ℝ) x =
            (D.Ω : Set (SpatialCoordinates d)).indicator
                (u₀.1 : SpatialCoordinates d → ℝ) x +
              (D.reflected : Set (SpatialCoordinates d)).indicator
                ((u₀.1 : SpatialCoordinates d → ℝ) ∘
                  coordinateReflection D.z {D.i}) x := hxe
        _ = (u₀.1 : SpatialCoordinates d → ℝ)
              (coordinateReflection z {i} x) := by
          rw [Set.indicator_of_notMem hxΩ', Set.indicator_of_mem hxR, zero_add]
          change (u₀.1 : SpatialCoordinates d → ℝ)
            (coordinateReflection z {i} x) =
            (u₀.1 : SpatialCoordinates d → ℝ)
              (coordinateReflection z {i} x)
          rfl
        _ = (vfD.1 : SpatialCoordinates d → ℝ) x := hxur hxR
        _ = (v : SobolevData (centeredCube w r hr)).1
              (coordinateFold z₀ I P x) := hxvu hxR
        _ = (v : SobolevData (centeredCube w r hr)).1
              (coordinateFold (foldedCubeCenter w r (insert i I) P)
                (insert i I) P x) := by rw [hfold]
  · intro j
    change ∀ᵐ x ∂volume.restrict
        (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d)),
      ((D.evenExtension u₀).2 j : SpatialCoordinates d → ℝ) x = _
    have hu₀gL := reflectionSobolevData_gradient_coeFn D.z {D.i}
      D.preimage_reflected vfD j
    have hu₀gL0 : ((u₀.2 j : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (D.Ω : Set _)]
        fun x => coordinateReflectionSign {D.i} j *
          (vfD.2 j : SpatialCoordinates d → ℝ)
            (coordinateReflection D.z {D.i} x)) := by
      simpa only [u₀] using! hu₀gL
    have hmR : MeasurePreserving (coordinateReflection D.z {D.i})
        (volume.restrict (D.reflected : Set _))
        (volume.restrict (D.Ω : Set _)) :=
      coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_Ω
    have hmL : MeasurePreserving (coordinateReflection D.z {D.i})
        (volume.restrict (D.Ω : Set _))
        (volume.restrict (D.reflected : Set _)) :=
      coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_reflected
    have hu₀gRraw := hmR.quasiMeasurePreserving.ae hu₀gL0
    have hu₀gR : ((u₀.2 j : SpatialCoordinates d → ℝ) ∘
        coordinateReflection D.z {D.i}) =ᵐ[
          volume.restrict (D.reflected : Set _)]
        fun x => coordinateReflectionSign {D.i} j *
          (vfD.2 j : SpatialCoordinates d → ℝ) x := by
      filter_upwards [hu₀gRraw] with x hx
      change (u₀.2 j : SpatialCoordinates d → ℝ)
          (coordinateReflection D.z {D.i} x) =
        coordinateReflectionSign {D.i} j *
          (vfD.2 j : SpatialCoordinates d → ℝ)
            (coordinateReflection D.z {D.i}
              (coordinateReflection D.z {D.i} x)) at hx
      rw [coordinateReflection_involutive] at hx
      exact hx
    have hu₀gR' := ae_restrict_of_ae (s := (D.U : Set _))
      ((ae_restrict_iff' D.reflected.isOpen.measurableSet).mp hu₀gR)
    have hu₀gL' := ae_restrict_of_ae (s := (D.U : Set _))
      ((ae_restrict_iff' D.Ω.isOpen.measurableSet).mp hu₀gL0)
    have hgjD : ∀ᵐ x ∂volume.restrict (D.reflected : Set _),
        ((vfD : SobolevData D.reflected).2 j : SpatialCoordinates d → ℝ) x =
          (if j ∈ I then
              coordinateReflectionSign P j *
                (if x j < foldedCubeCenter w r I P j then -1 else 1)
           else 1) *
            (sobolevGradient (v : SobolevData (centeredCube w r hr)) j)
          (coordinateFold z₀ I P x) := by
      have hbase := aux_lem_even_fold_construction_cast_ae D.reflected
        (foldedCube w r hr I P) hDref
        ((vf : SobolevData (foldedCube w r hr I P)).2 j) (hg j)
      have hcompj : vfD.2 j = hDref.symm ▸
          (vf : SobolevData (foldedCube w r hr I P)).2 j := by
        have hc := congrArg (fun q : SobolevData D.reflected => q.2 j) hcast
        simpa only using! hc
      rw [← hcompj] at hbase
      simpa [z₀] using! hbase
    have hgjL := hmL.quasiMeasurePreserving.ae hgjD
    have hgjLU := ae_restrict_of_ae (s := (D.U : Set _))
      ((ae_restrict_iff' D.Ω.isOpen.measurableSet).mp hgjL)
    have hgjU := ae_restrict_of_ae (s := (D.U : Set _))
      ((ae_restrict_iff' D.reflected.isOpen.measurableSet).mp hgjD)
    have hge := D.evenExtension_snd_coeFn u₀ j
    have hmem := D.ae_mem_or_mem
    filter_upwards [hge, hu₀gL', hu₀gR', hgjLU, hgjU, hmem]
      with x hxe hxgL hxgR hxjL hxjU hxmem
    rcases hxmem with hxΩ | hxR
    · have hxR' : x ∉ (D.reflected : Set _) := D.notMem_reflected_of_mem_Ω hxΩ
      rw [hxe, Set.indicator_of_mem hxΩ, Set.indicator_of_notMem hxR', add_zero]
      rw [hxgL hxΩ, hxjL hxΩ]
      have hfac :
          (if j ∈ insert i I then
              coordinateReflectionSign P j *
                (if x j < foldedCubeCenter w r (insert i I) P j then -1 else 1)
           else 1) =
            coordinateReflectionSign {i} j *
              (if j ∈ I then
                coordinateReflectionSign P j *
                  (if (coordinateReflection z {i} x) j <
                      foldedCubeCenter w r I P j then -1 else 1)
               else 1) := by
        by_cases hji : j = i
        · subst j
          have hxi : x i < z i := (D.mem_iff x).mp hxΩ |>.2
          have hxi' : x i < w i - r / 2 := by
            simpa [z, foldedCubeCenter, hiP] using! hxi
          simp [hi, hiP, foldedCubeCenter, coordinateReflectionSign, hxi']
        · have hRj : (coordinateReflection z {i} x) j = x j :=
            coordinateReflection_single_apply_of_ne z hji x
          have hnew : foldedCubeCenter w r (insert i I) P j =
                foldedCubeCenter w r I P j := by
            simp [foldedCubeCenter, hji]
          simp [Finset.mem_insert, hji, hnew, hRj,
            coordinateReflectionSign]
      have hfold : coordinateFold (foldedCubeCenter w r (insert i I) P)
          (insert i I) P x = coordinateFold z₀ I P
            (coordinateReflection z {i} x) := by
        simpa [z] using! hfold_lower x hxΩ
      rw [hfac, hfold]
      simp [D, z]
      simp only [mul_assoc]
    · have hxΩ' : x ∉ (D.Ω : Set _) := D.notMem_Ω_of_mem_reflected hxR
      rw [hxe, Set.indicator_of_notMem hxΩ', Set.indicator_of_mem hxR, zero_add]
      have hxgR' := hxgR hxR
      simp only [Function.comp_apply] at hxgR'
      rw [hxgR', hxjU hxR]
      have hfac :
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
          have hxi : z i < x i := (D.mem_reflected_iff x).mp hxR |>.2
          have hxi' : w i - r / 2 < x i := by
            simpa [z, foldedCubeCenter, hiP] using! hxi
          have hnlt : ¬ x i < w i - r / 2 := by linarith
          simp [hi, hiP, foldedCubeCenter, coordinateReflectionSign, hnlt]
        · by_cases hjI : j ∈ I <;> by_cases hjP : j ∈ P <;>
            simp [Finset.mem_insert, hji, foldedCubeCenter,
              coordinateReflectionSign, hjI, hjP]
      have hfold : coordinateFold (foldedCubeCenter w r (insert i I) P)
          (insert i I) P x = coordinateFold z₀ I P x := by
        simpa [z] using! hfold_upper x hxR
      rw [hfac, hfold]
      simp [D]
      by_cases hji : j = i
      · subst j
        simp [coordinateReflectionSign, hi]
      · simp [coordinateReflectionSign, Finset.mem_singleton, hji]

lemma aux_lem_even_fold_construction_induction
  (d : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
  (I P : Finset (Fin d))
  (a : PositiveCoefficient (centeredCube w r hr))
  (v : weakSobolevGraph (centeredCube w r hr)) :
  ∃ (af : PositiveCoefficient (foldedCube w r hr I P))
    (vf : weakSobolevGraph (foldedCube w r hr I P)),
    ((af.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d))]
    fun x => a.val (coordinateFold (foldedCubeCenter w r I P) I P x)) ∧
    (((vf : SobolevData (foldedCube w r hr I P)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d))]
    fun x => (v : SobolevData (centeredCube w r hr)).1
      (coordinateFold (foldedCubeCenter w r I P) I P x)) ∧
    (∀ j : Fin d,
    ∀ᵐ x ∂volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d)),
      sobolevGradient (vf : SobolevData (foldedCube w r hr I P)) j x =
        (if j ∈ I then
          coordinateReflectionSign P j *
            (if x j < foldedCubeCenter w r I P j then -1 else 1)
         else 1) *
          sobolevGradient (v : SobolevData (centeredCube w r hr)) j
            (coordinateFold (foldedCubeCenter w r I P) I P x)) := by
  induction I using Finset.induction_on with
  | empty =>
      have hΩ : foldedCube w r hr ∅ P = centeredCube w r hr := by
        ext x
        rw [centeredCube_eq_pi]
        simp [foldedCube]
      rw [hΩ]
      have hfold (x : SpatialCoordinates d) :
          coordinateFold (foldedCubeCenter w r ∅ P) ∅ P x = x := by
        funext k
        simp [coordinateFold]
      refine ⟨a, v, ?_, ?_, ?_⟩
      · filter_upwards [] with x
        rfl
      · filter_upwards [] with x
        rw [hfold]
      · intro j
        filter_upwards [] with x
        rw [hfold]
        simp only [Finset.notMem_empty, ite_false, one_mul]
  | @insert i I hi ih =>
      obtain ⟨af, vf, haf, hvf, hgf⟩ := ih
      by_cases hiP : i ∈ P
      · exact aux_lem_even_fold_construction_up d w r hr I P i hi a v af vf
          haf hvf hgf hiP
      · exact aux_lem_even_fold_construction_down d w r hr I P i hi a v af vf
          haf hvf hgf hiP

/-- Even extension and its weak-gradient chain rule.
* Concrete cube, positive side, active coordinate faces and arbitrary fold signs:
  the geometric data of `lem_even`.
* PositiveCoefficient is the standing bounded, uniformly positive scalar
  coefficient; v is an actual H¹ element.
* The folded coefficient and H¹ function are CONSTRUCTED, with a.e. value ties.
* The signed weak-gradient identity is CONCLUDED, from the single-face chain
  rule and iteration; no extension or gradient identity is assumed.
The sign on the reflection hyperplanes is immaterial to the a.e. identity.
The pinned one-face APIs EvenReflectionDomain.evenExtension_mem_weak and
evenExtensionCoefficient are implementation ingredients, not extra hypotheses.
The finite reflected-copy partition and one-new-face gluing obligations are
exposed as the fine suppliers lem_even_fold_partition and
lem_even_fold_face_gluing; they are not assumed in this declaration.
-/
theorem lem_even_fold_construction
  (d : ℕ) (w : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
  (I P : Finset (Fin d))
  (a : PositiveCoefficient (centeredCube w r hr))
  (v : weakSobolevGraph (centeredCube w r hr)) :
  ∃ (af : PositiveCoefficient (foldedCube w r hr I P))
    (vf : weakSobolevGraph (foldedCube w r hr I P)),
    ((af.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d))]
    fun x => a.val (coordinateFold (foldedCubeCenter w r I P) I P x)) ∧
    (((vf : SobolevData (foldedCube w r hr I P)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d))]
    fun x => (v : SobolevData (centeredCube w r hr)).1
      (coordinateFold (foldedCubeCenter w r I P) I P x)) ∧
    (∀ j : Fin d,
    ∀ᵐ x ∂volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d)),
      sobolevGradient (vf : SobolevData (foldedCube w r hr I P)) j x =
        (if j ∈ I then
          coordinateReflectionSign P j *
            (if x j < foldedCubeCenter w r I P j then -1 else 1)
         else 1) *
          sobolevGradient (v : SobolevData (centeredCube w r hr)) j
            (coordinateFold (foldedCubeCenter w r I P) I P x)) := by
  exact aux_lem_even_fold_construction_induction d w r hr I P a v

end SubdiffusiveProcess.Paper
