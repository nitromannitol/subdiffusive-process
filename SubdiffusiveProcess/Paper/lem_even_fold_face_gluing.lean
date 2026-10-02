import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
import SubdiffusiveProcess.Sobolev.BoundaryEnergy
import SubdiffusiveProcess.Lane2.BoxReflection
import SubdiffusiveProcess.Lane2.FoldedIteration
import SubdiffusiveProcess.Paper.lem_even_fold_partition

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess SubdiffusiveProcess.Lane4

noncomputable section
namespace Paper

theorem aux_lem_even_fold_face_gluing_cast_lp
    {d : ℕ} {U V : Opens (SpatialCoordinates d)} (h : U = V)
    (f : Lp ℝ ∞ (volume.restrict (V : Set (SpatialCoordinates d)))) :
    ((h.symm ▸ f : Lp ℝ ∞ (volume.restrict (U : Set (SpatialCoordinates d)))) :
        SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (U : Set (SpatialCoordinates d))]
      (f : SpatialCoordinates d → ℝ) := by
  cases h
  rfl

theorem aux_lem_even_fold_face_gluing_cast_ae
    {d : ℕ} {U V : Opens (SpatialCoordinates d)} (h : U = V)
    {f g : SpatialCoordinates d → ℝ}
    (ha : f =ᵐ[volume.restrict (V : Set (SpatialCoordinates d))] g) :
    f =ᵐ[volume.restrict (U : Set (SpatialCoordinates d))] g := by
  cases h
  exact ha

theorem aux_lem_even_fold_face_gluing_cast_positive
    {d : ℕ} {U V : Opens (SpatialCoordinates d)} (h : U = V)
    (f : PositiveCoefficient V) :
    ((h.symm ▸ f).val : SpatialCoordinates d → ℝ) =
      ((h.symm ▸ f.val : Lp ℝ ∞ (volume.restrict (U : Set (SpatialCoordinates d)))) :
        SpatialCoordinates d → ℝ) := by
  cases h
  rfl

theorem aux_lem_even_fold_face_gluing_cast_weak_fst
    {d : ℕ} {U V : Opens (SpatialCoordinates d)} (h : U = V)
    (f : weakSobolevGraph V) :
    ((((h.symm ▸ f : weakSobolevGraph U) : SobolevData U).1 :
        SpatialCoordinates d → ℝ) =
      (((f : SobolevData V).1 : SpatialCoordinates d → ℝ))) := by
  cases h
  rfl

theorem aux_lem_even_fold_face_gluing_cast_weak_snd
    {d : ℕ} {U V : Opens (SpatialCoordinates d)} (h : U = V)
    (f : weakSobolevGraph V) (j : Fin d) :
    ((((h.symm ▸ f : weakSobolevGraph U) : SobolevData U).2 j :
        SpatialCoordinates d → ℝ) =
      (((f : SobolevData V).2 j : SpatialCoordinates d → ℝ))) := by
  cases h
  rfl

theorem aux_lem_even_fold_face_gluing_reflect_ae
    {d : ℕ} (z : SpatialCoordinates d) (I : Finset (Fin d))
    {Ω U : Opens (SpatialCoordinates d)}
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    {f g : SpatialCoordinates d → ℝ}
    (h : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      f x = g (coordinateReflection z I x)) :
    ∀ᵐ x ∂volume.restrict (U : Set (SpatialCoordinates d)),
      f (coordinateReflection z I x) = g x := by
  have hm : MeasurePreserving (coordinateReflection z I)
      (volume.restrict (U : Set (SpatialCoordinates d)))
      (volume.restrict (Ω : Set (SpatialCoordinates d))) :=
    coordinateReflection_domain_measurePreserving z I hU
  have hr := hm.quasiMeasurePreserving.ae h
  filter_upwards [hr] with x hx
  change f (coordinateReflection z I x) =
    g (coordinateReflection z I (coordinateReflection z I x)) at hx
  rw [coordinateReflection_involutive] at hx
  exact hx



theorem aux_lem_even_fold_face_gluing_down
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
  let lo : SpatialCoordinates d := fun j =>
    if j ∈ I then
      if j ∈ P then w j - r / 2 else w j - 3 * r / 2
    else w j - r / 2
  let hi₀ : SpatialCoordinates d := fun j =>
    if j ∈ I then
      if j ∈ P then w j + 3 * r / 2 else w j + r / 2
    else w j + r / 2
  have hΩ : openBox lo hi₀ = foldedCube w r hr I P := by
    apply Opens.ext
    ext x
    rw [SetLike.mem_coe, mem_openBox_iff]
    change (∀ j, lo j < x j ∧ x j < hi₀ j) ↔
      x ∈ Set.pi Set.univ (fun j =>
        if j ∈ I then
          (if j ∈ P then Set.Ioo (w j - r / 2) (w j + 3 * r / 2)
           else Set.Ioo (w j - 3 * r / 2) (w j + r / 2))
        else Set.Ioo (w j - r / 2) (w j + r / 2))
    simp only [Set.mem_univ_pi]
    change (∀ j, lo j < x j ∧ x j < hi₀ j) ↔
      ∀ j, x j ∈ if j ∈ I then
        (if j ∈ P then Set.Ioo (w j - r / 2) (w j + 3 * r / 2)
         else Set.Ioo (w j - 3 * r / 2) (w j + r / 2))
      else Set.Ioo (w j - r / 2) (w j + r / 2)
    constructor
    · intro hx j
      by_cases hj : j ∈ I
      · by_cases hjP : j ∈ P
        · have h := hx j
          simp [hj, hjP, lo, hi₀] at h ⊢
          exact h
        · have h := hx j
          simp [hj, hjP, lo, hi₀] at h ⊢
          exact h
      · have h := hx j
        simp [hj, lo, hi₀] at h ⊢
        exact h
    · intro hx j
      by_cases hj : j ∈ I
      · by_cases hjP : j ∈ P
        · have h := hx j
          simp [hj, hjP, lo, hi₀] at h ⊢
          exact h
        · have h := hx j
          simp [hj, hjP, lo, hi₀] at h ⊢
          exact h
      · have h := hx j
        simp [hj, lo, hi₀] at h ⊢
        exact h
  have hU : openBox (lowerDoubledCorner lo hi₀ i) hi₀ =
      foldedCube w r hr (insert i I) P := by
    apply Opens.ext
    ext x
    rw [SetLike.mem_coe, mem_openBox_iff]
    change (∀ j, lowerDoubledCorner lo hi₀ i j < x j ∧ x j < hi₀ j) ↔
      x ∈ Set.pi Set.univ (fun j =>
        if j ∈ insert i I then
          (if j ∈ P then Set.Ioo (w j - r / 2) (w j + 3 * r / 2)
           else Set.Ioo (w j - 3 * r / 2) (w j + r / 2))
        else Set.Ioo (w j - r / 2) (w j + r / 2))
    simp only [Set.mem_univ_pi]
    change (∀ j, lowerDoubledCorner lo hi₀ i j < x j ∧ x j < hi₀ j) ↔
      ∀ j, x j ∈ if j ∈ insert i I then
        (if j ∈ P then Set.Ioo (w j - r / 2) (w j + 3 * r / 2)
         else Set.Ioo (w j - 3 * r / 2) (w j + r / 2))
      else Set.Ioo (w j - r / 2) (w j + r / 2)
    constructor
    · intro hx j
      by_cases hji : j = i
      · subst j
        have h := hx i
        simp [lowerDoubledCorner, lo, hi₀, hi, hiP, Set.mem_Ioo] at h ⊢
        constructor <;> linarith [h.1, h.2]
      · by_cases hj : j ∈ I
        · by_cases hjP : j ∈ P
          · have h := hx j
            simp [Finset.mem_insert, hj, hjP, hji, lowerDoubledCorner,
              lo, hi₀] at h ⊢
            exact h
          · have h := hx j
            simp [Finset.mem_insert, hj, hjP, hji, lowerDoubledCorner,
              lo, hi₀] at h ⊢
            exact h
        · have h := hx j
          simp [Finset.mem_insert, hj, hji, lowerDoubledCorner, lo, hi₀] at h ⊢
          exact h
    · intro hx j
      by_cases hji : j = i
      · subst j
        have h := hx i
        simp [lowerDoubledCorner, lo, hi₀, hi, hiP, Set.mem_Ioo] at h ⊢
        constructor <;> linarith [h.1, h.2]
      · by_cases hj : j ∈ I
        · by_cases hjP : j ∈ P
          · have h := hx j
            simp [Finset.mem_insert, hj, hjP, hji, lowerDoubledCorner,
              lo, hi₀] at h ⊢
            exact h
          · have h := hx j
            simp [Finset.mem_insert, hj, hjP, hji, lowerDoubledCorner,
              lo, hi₀] at h ⊢
            exact h
        · have h := hx j
          simp [Finset.mem_insert, hj, hji, lowerDoubledCorner, lo, hi₀] at h ⊢
          exact h
  let Db : EvenReflectionDomain d :=
    boxEvenReflectionDomain (lowerDoubledCorner lo hi₀ i)
      (Function.update hi₀ i (lo i)) i
  have hDbref : Db.reflected = foldedCube w r hr I P := by
    calc
      Db.reflected = openBox lo hi₀ := by
        simpa [Db] using boxEvenReflectionDomain_mirror_reflected lo hi₀ i
      _ = foldedCube w r hr I P := hΩ
  have hDbU : Db.U = foldedCube w r hr (insert i I) P := by
    calc
      Db.U = openBox (lowerDoubledCorner lo hi₀ i) hi₀ := by
        simpa [Db] using boxEvenReflectionDomain_mirror_U lo hi₀ i
      _ = foldedCube w r hr (insert i I) P := hU
  let D : EvenReflectionDomain d :=
    { z := Db.z
      i := i
      Ω := Db.Ω
      U := foldedCube w r hr (insert i I) P
      mem_iff := by
        intro x
        rw [← hDbU]
        exact Db.mem_iff x
      symm := by
        rw [← hDbU]
        exact Db.symm }
  have hDref : D.reflected = foldedCube w r hr I P := by
    change Db.reflected = foldedCube w r hr I P
    exact hDbref
  let z : SpatialCoordinates d := foldedCubeCenter w r (insert i I) P
  have hz : z i = D.z i := by
    dsimp [D, Db, boxEvenReflectionDomain]
    simp [z, foldedCubeCenter, lowerDoubledCorner, lo, hi₀, hi, hiP,
      upperFacePoint]
  have hcoord (x : SpatialCoordinates d) :
      coordinateFold (foldedCubeCenter w r I P) I P x =
        coordinateFold z I P x := by
    funext j
    by_cases hj : j ∈ I
    · have hji : j ≠ i := by
        intro hji
        exact hi (hji ▸ hj)
      simp [coordinateFold, foldedCubeCenter, z, hj, hji]
    · simp [coordinateFold, hj]
  have hRcong : coordinateReflection z {i} =
      coordinateReflection D.z {i} :=
    coordinateReflection_single_congr z D.z i hz
  have hfold_le (x : SpatialCoordinates d) (hx : x i ≤ D.z i) :
      coordinateFold z (insert i I) P x =
        coordinateFold (foldedCubeCenter w r I P) I P
          (coordinateReflection D.z {i} x) := by
    calc
      coordinateFold z (insert i I) P x =
          coordinateFold z I P (coordinateReflection z {i} x) := by
        exact lane2_fold_insert_I_of_le hi hiP (by rw [hz]; exact hx)
      _ = coordinateFold (foldedCubeCenter w r I P) I P
          (coordinateReflection D.z {i} x) := by
        rw [hcoord, hRcong]
  have hfold_ge (x : SpatialCoordinates d) (hx : D.z i ≤ x i) :
      coordinateFold z (insert i I) P x =
        coordinateFold (foldedCubeCenter w r I P) I P x := by
    calc
      coordinateFold z (insert i I) P x = coordinateFold z I P x := by
        exact lane2_fold_insert_I_of_ge hi hiP (by rw [hz]; exact hx)
      _ = coordinateFold (foldedCubeCenter w r I P) I P x := (hcoord x).symm
  have hfac_le (j : Fin d) (x : SpatialCoordinates d) (hx : x i < D.z i) :
      (if j ∈ insert i I then
          coordinateReflectionSign P j *
            (if x j < z j then -1 else 1)
        else 1) =
        coordinateReflectionSign {i} j *
          (if j ∈ I then
            coordinateReflectionSign P j *
              (if (coordinateReflection D.z {i} x) j <
                  foldedCubeCenter w r I P j then -1 else 1)
          else 1) := by
    by_cases hji : j = i
    · subst j
      have hxi : x i < z i := by rw [hz]; exact hx
      have hxi' : x i < w i - r / 2 := by
        simpa [z, foldedCubeCenter, hiP] using hxi
      have hnotz : ¬ z i ≤ x i := not_le_of_gt hxi
      simp [hi, hiP, foldedCubeCenter, coordinateReflectionSign, hxi', hnotz]
    · have hRj : (coordinateReflection D.z {i} x) j = x j :=
        coordinateReflection_single_apply_of_ne D.z hji x
      have hnew : foldedCubeCenter w r (insert i I) P j =
          foldedCubeCenter w r I P j := by
        simp [foldedCubeCenter, hji]
      simp [Finset.mem_insert, hji, z, foldedCubeCenter, hnew, hRj,
        coordinateReflectionSign]
  have hfac_ge (j : Fin d) (x : SpatialCoordinates d) (hx : D.z i < x i) :
      (if j ∈ insert i I then
          coordinateReflectionSign P j *
            (if x j < z j then -1 else 1)
        else 1) =
        (if j ∈ I then
          coordinateReflectionSign P j *
            (if x j < foldedCubeCenter w r I P j then -1 else 1)
         else 1) := by
    by_cases hji : j = i
    · subst j
      have hzx : z i < x i := by rw [hz]; exact hx
      have hnot : ¬ x i < w i - r / 2 := by
        intro hxi
        have : x i < z i := by simpa [z, foldedCubeCenter, hiP] using hxi
        linarith
      have hnotz : ¬ x i < z i := not_lt_of_ge (le_of_lt hzx)
      simp [hi, hiP, foldedCubeCenter, coordinateReflectionSign, hnot, hnotz]
    · simp [Finset.mem_insert, hji, z, foldedCubeCenter,
        coordinateReflectionSign]
  let afR : PositiveCoefficient D.reflected := hDref.symm ▸ af
  have hafcast := aux_lem_even_fold_face_gluing_cast_lp hDref af.val
  have haD := aux_lem_even_fold_face_gluing_cast_ae hDref ha
  have hfoldR : ((afR.val : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (D.reflected : Set (SpatialCoordinates d))]
      foldedCoefficientP (a.val : SpatialCoordinates d → ℝ) z I P) := by
    filter_upwards [hafcast, haD] with x hxcast hx
    have hcoeval := congrFun
      (aux_lem_even_fold_face_gluing_cast_positive hDref af) x
    rw [hcoeval, hxcast, hx]
    rw [hcoord]
    simp only [foldedCoefficientP]
  have hz' : z i = D.z i := hz
  have hac := lane2_evenExtensionCoefficient_fold_down D afR
    (a := (a.val : SpatialCoordinates d → ℝ)) (z := z) (I := I) (P := P)
    hi hiP hz' hfoldR
  let vfR : weakSobolevGraph D.reflected := hDref.symm ▸ vf
  let u : SobolevData D.Ω :=
    reflectionSobolevData D.z {i} D.preimage_reflected
      vfR.1
  have hu : u ∈ weakSobolevGraph D.Ω := by
    exact reflectionSobolevData_mem_weak D.z {i} D.preimage_reflected
      vfR.property
  have hmp := coordinateReflection_domain_measurePreserving D.z {i}
      D.preimage_reflected
  have hmp' := coordinateReflection_domain_measurePreserving D.z {i}
      (coordinateReflection_preimage_reverse D.z {i} D.preimage_reflected)
  have hvfcast := aux_lem_even_fold_face_gluing_cast_weak_fst hDref vf
  have hvfcastR : ∀ᵐ x ∂volume.restrict (D.Ω : Set (SpatialCoordinates d)),
      ((((vfR.1).1 : DomainL2 D.reflected) : SpatialCoordinates d → ℝ)
        (coordinateReflection D.z {i} x)) =
      (((vf : SobolevData (foldedCube w r hr I P)).1 :
        SpatialCoordinates d → ℝ) (coordinateReflection D.z {i} x)) :=
    Filter.Eventually.of_forall (fun x =>
      congrFun hvfcast (coordinateReflection D.z {i} x))
  have hval0 := reflectionLp_coeFn D.z {i} D.preimage_reflected
    ((vfR.1 : SobolevData D.reflected).1 : DomainL2 D.reflected)
  have hval : (((u.1 : DomainL2 D.Ω) : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (D.Ω : Set (SpatialCoordinates d))]
      fun x => ((vf : SobolevData (foldedCube w r hr I P)).1 :
        SpatialCoordinates d → ℝ) (coordinateReflection D.z {i} x)) := by
    filter_upwards [hval0, hvfcastR] with x hx hy
    rw [show ((u.1 : DomainL2 D.Ω) : SpatialCoordinates d → ℝ) x =
        ((reflectionLp D.z {i} D.preimage_reflected
          ((vfR.1 : SobolevData D.reflected).1 : DomainL2 D.reflected)) :
            SpatialCoordinates d → ℝ) x by rfl,
      hx]
    simpa only [Function.comp_apply] using hy
  have hgrad0 (j : Fin d) :
      (((u.2 j : DomainL2 D.Ω) : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (D.Ω : Set (SpatialCoordinates d))]
        fun x => coordinateReflectionSign {i} j *
          (((vfR.1 : SobolevData D.reflected).2 j : DomainL2 D.reflected) :
            SpatialCoordinates d → ℝ)
            (coordinateReflection D.z {i} x)) := by
    have hs := Lp.coeFn_smul (coordinateReflectionSign {i} j)
      (reflectionLp D.z {i} D.preimage_reflected
        ((vfR.1 : SobolevData D.reflected).2 j))
    filter_upwards [hs, reflectionLp_coeFn D.z {i} D.preimage_reflected
      ((vfR.1 : SobolevData D.reflected).2 j)] with x hs hx
    change (coordinateReflectionSign {i} j •
      reflectionLp D.z {i} D.preimage_reflected
        ((vfR.1 : SobolevData D.reflected).2 j)) x = _
    rw [hs, Pi.smul_apply, smul_eq_mul, hx]
    rfl
  have hgrad (j : Fin d) :
      (((u.2 j : DomainL2 D.Ω) : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (D.Ω : Set (SpatialCoordinates d))]
        fun x => coordinateReflectionSign {i} j *
          ((vf : SobolevData (foldedCube w r hr I P)).2 j :
            SpatialCoordinates d → ℝ) (coordinateReflection D.z {i} x)) := by
    have hvfcastj := aux_lem_even_fold_face_gluing_cast_weak_snd hDref vf j
    have hvfcastjR : ∀ᵐ x ∂volume.restrict (D.Ω : Set (SpatialCoordinates d)),
        ((((vfR.1).2 j : DomainL2 D.reflected) : SpatialCoordinates d → ℝ)
          (coordinateReflection D.z {i} x)) =
        (((vf : SobolevData (foldedCube w r hr I P)).2 j :
          SpatialCoordinates d → ℝ) (coordinateReflection D.z {i} x)) :=
      Filter.Eventually.of_forall (fun x =>
        congrFun hvfcastj (coordinateReflection D.z {i} x))
    filter_upwards [hgrad0 j, hvfcastjR] with x hx hy
    rw [hx, hy]
  have hvD : (((vf : SobolevData (foldedCube w r hr I P)).1 :
      SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (D.reflected : Set (SpatialCoordinates d))]
      fun x => (v : SobolevData (centeredCube w r hr)).1
        (coordinateFold (foldedCubeCenter w r I P) I P x)) := by
    exact aux_lem_even_fold_face_gluing_cast_ae hDref hv
  have hvLowerRaw := hmp.quasiMeasurePreserving.ae hvD
  have hvLower : ∀ᵐ x ∂volume.restrict (D.Ω : Set (SpatialCoordinates d)),
      ((vf : SobolevData (foldedCube w r hr I P)).1 :
        SpatialCoordinates d → ℝ) (coordinateReflection D.z {i} x) =
        (v : SobolevData (centeredCube w r hr)).1
          (coordinateFold (foldedCubeCenter w r I P) I P
            (coordinateReflection D.z {i} x)) := by
    simpa only [Function.comp_apply] using hvLowerRaw
  have hvalLower : (((u.1 : DomainL2 D.Ω) : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (D.Ω : Set (SpatialCoordinates d))]
      fun x => (v : SobolevData (centeredCube w r hr)).1
        (coordinateFold (foldedCubeCenter w r I P) I P
          (coordinateReflection D.z {i} x))) := by
    filter_upwards [hval, hvLower] with x hx hy
    rw [hx, hy]
  have hvalRRaw := hmp'.quasiMeasurePreserving.ae hval
  have hvalR : (((u.1 : DomainL2 D.Ω) : SpatialCoordinates d → ℝ) ∘
      coordinateReflection D.z {i}) =ᵐ[
      volume.restrict (D.reflected : Set (SpatialCoordinates d))]
      ((vf : SobolevData (foldedCube w r hr I P)).1 :
        SpatialCoordinates d → ℝ) := by
    filter_upwards [hvalRRaw] with x hx
    change ((u.1 : DomainL2 D.Ω) : SpatialCoordinates d → ℝ)
        (coordinateReflection D.z {i} x) =
      ((vf : SobolevData (foldedCube w r hr I P)).1 :
        SpatialCoordinates d → ℝ)
        (coordinateReflection D.z {i} (coordinateReflection D.z {i} x)) at hx
    rw [coordinateReflection_involutive] at hx
    exact hx
  have hvalUpper : (((u.1 : DomainL2 D.Ω) : SpatialCoordinates d → ℝ) ∘
      coordinateReflection D.z {i}) =ᵐ[
      volume.restrict (D.reflected : Set (SpatialCoordinates d))]
      fun x => (v : SobolevData (centeredCube w r hr)).1
        (coordinateFold (foldedCubeCenter w r I P) I P x) := by
    filter_upwards [hvalR, hvD] with x hx hy
    rw [hx, hy]
  have hvalLowerU := ae_restrict_of_ae (μ := (volume : Measure (SpatialCoordinates d)))
    (s := (D.U : Set (SpatialCoordinates d)))
    ((ae_restrict_iff' (μ := (volume : Measure (SpatialCoordinates d)))
      D.Ω.isOpen.measurableSet).mp hvalLower)
  have hvalUpperU := ae_restrict_of_ae (μ := (volume : Measure (SpatialCoordinates d)))
    (s := (D.U : Set (SpatialCoordinates d)))
    ((ae_restrict_iff' (μ := (volume : Measure (SpatialCoordinates d)))
      D.reflected.isOpen.measurableSet).mp hvalUpper)
  have hweak := D.evenExtension_mem_weak hu
  refine ⟨D.evenExtensionCoefficient
      (reflectionCoefficient D.z {D.i} D.preimage_reflected afR),
    ⟨D.evenExtension u, hweak⟩, ?_, ?_, ?_⟩
  · change ((D.evenExtensionCoefficient
        (reflectionCoefficient D.z {D.i} D.preimage_reflected afR)).val :
          SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (foldedCube w r hr (insert i I) P :
          Set (SpatialCoordinates d))]
      foldedCoefficientP (a.val : SpatialCoordinates d → ℝ) z (insert D.i I) P
      at hac
    simpa only [foldedCoefficientP] using hac
  · filter_upwards [D.evenExtension_fst_coeFn u, hvalLowerU, hvalUpperU,
      D.ae_mem_or_mem] with x he hxl hxu hmem
    rcases hmem with hx | hx
    · rw [he, Set.indicator_of_mem hx,
        Set.indicator_of_notMem (D.notMem_reflected_of_mem_Ω hx), add_zero]
      rw [hxl hx, hfold_le x (le_of_lt ((D.mem_iff x).mp hx).2)]
    · rw [he, Set.indicator_of_notMem (D.notMem_Ω_of_mem_reflected hx),
        Set.indicator_of_mem hx, zero_add, Function.comp_apply]
      have hxu' := hxu hx
      change ((u.1 : DomainL2 D.Ω) : SpatialCoordinates d → ℝ)
        (coordinateReflection D.z {i} x) = _ at hxu'
      calc
        ((u.1 : DomainL2 D.Ω) : SpatialCoordinates d → ℝ)
            (coordinateReflection D.z {i} x) =
            (v : SobolevData (centeredCube w r hr)).1
              (coordinateFold (foldedCubeCenter w r I P) I P x) := hxu'
        _ = (v : SobolevData (centeredCube w r hr)).1
              (coordinateFold z (insert i I) P x) := by
          exact congrArg
            (fun y => (v : SobolevData (centeredCube w r hr)).1 y)
            (hfold_ge x (le_of_lt ((D.mem_reflected_iff x).mp hx).2)).symm
  · intro j
    change ∀ᵐ x ∂volume.restrict
        (D.U : Set (SpatialCoordinates d)),
      ((D.evenExtension u).2 j : SpatialCoordinates d → ℝ) x = _
    have hgjD := aux_lem_even_fold_face_gluing_cast_ae hDref (hg j)
    have hgjLRaw := hmp.quasiMeasurePreserving.ae hgjD
    have hgjU := ae_restrict_of_ae
      (μ := (volume : Measure (SpatialCoordinates d)))
      (s := (D.U : Set (SpatialCoordinates d)))
      ((ae_restrict_iff' (μ := (volume : Measure (SpatialCoordinates d)))
        D.reflected.isOpen.measurableSet).mp hgjD)
    have hgjLU := ae_restrict_of_ae
      (μ := (volume : Measure (SpatialCoordinates d)))
      (s := (D.U : Set (SpatialCoordinates d)))
      ((ae_restrict_iff' (μ := (volume : Measure (SpatialCoordinates d)))
        D.Ω.isOpen.measurableSet).mp hgjLRaw)
    have hgrR := aux_lem_even_fold_face_gluing_reflect_ae D.z {i}
      (coordinateReflection_preimage_reverse D.z {i} D.preimage_reflected)
      (f := fun x => ((u.2 j : DomainL2 D.Ω) : SpatialCoordinates d → ℝ) x)
      (g := fun x => coordinateReflectionSign {i} j *
        ((vf : SobolevData (foldedCube w r hr I P)).2 j :
          SpatialCoordinates d → ℝ) x)
      (hgrad j)
    have hgrLU := ae_restrict_of_ae
      (μ := (volume : Measure (SpatialCoordinates d)))
      (s := (D.U : Set (SpatialCoordinates d)))
      ((ae_restrict_iff' (μ := (volume : Measure (SpatialCoordinates d)))
        D.Ω.isOpen.measurableSet).mp (hgrad j))
    have hgrRU := ae_restrict_of_ae
      (μ := (volume : Measure (SpatialCoordinates d)))
      (s := (D.U : Set (SpatialCoordinates d)))
      ((ae_restrict_iff' (μ := (volume : Measure (SpatialCoordinates d)))
        D.reflected.isOpen.measurableSet).mp hgrR)
    filter_upwards [D.evenExtension_snd_coeFn u j, hgrLU, hgrRU,
      hgjLU, hgjU, D.ae_mem_or_mem] with x hxe hxgL hxgR hxjL hxjU hmem
    change ((D.evenExtension u).2 j : SpatialCoordinates d → ℝ) x = _
    rcases hmem with hx | hx
    · rw [hxe, Set.indicator_of_mem hx,
        Set.indicator_of_notMem (D.notMem_reflected_of_mem_Ω hx), add_zero]
      have hxgL' := hxgL hx
      have hxjL' := hxjL hx
      change ((u.2 j : DomainL2 D.Ω) : SpatialCoordinates d → ℝ) x = _
        at hxgL'
      change ((vf : SobolevData (foldedCube w r hr I P)).2 j :
          SpatialCoordinates d → ℝ) (coordinateReflection D.z {i} x) = _
        at hxjL'
      have hfac' :
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
        simpa [z] using hfac_le j x ((D.mem_iff x).mp hx).2
      have hfold' :
          coordinateFold (foldedCubeCenter w r (insert i I) P)
              (insert i I) P x =
            coordinateFold (foldedCubeCenter w r I P) I P
              (coordinateReflection D.z {i} x) := by
        simpa [z] using hfold_le x (le_of_lt ((D.mem_iff x).mp hx).2)
      rw [hxgL', hxjL', hfac', hfold']
      ring
    · rw [hxe, Set.indicator_of_notMem (D.notMem_Ω_of_mem_reflected hx),
        Set.indicator_of_mem hx, zero_add]
      have hxgR' := hxgR hx
      have hxjU' := hxjU hx
      change ((u.2 j : DomainL2 D.Ω) : SpatialCoordinates d → ℝ)
          (coordinateReflection D.z {i} x) = _ at hxgR'
      change ((vf : SobolevData (foldedCube w r hr I P)).2 j :
          SpatialCoordinates d → ℝ) x = _ at hxjU'
      have hfac' :
          (if j ∈ insert i I then
              coordinateReflectionSign P j *
                (if x j < foldedCubeCenter w r (insert i I) P j then -1 else 1)
           else 1) =
            (if j ∈ I then
              coordinateReflectionSign P j *
                (if x j < foldedCubeCenter w r I P j then -1 else 1)
             else 1) := by
        simpa [z] using hfac_ge j x ((D.mem_reflected_iff x).mp hx).2
      have hfold' :
          coordinateFold (foldedCubeCenter w r (insert i I) P)
              (insert i I) P x =
            coordinateFold (foldedCubeCenter w r I P) I P x := by
        simpa [z] using hfold_ge x
          (le_of_lt ((D.mem_reflected_iff x).mp hx).2)
      rw [hxgR', hxjU', hfac', hfold']
      have hDi : D.i = i := rfl
      simp only [hDi]
      by_cases hji : j = i
      · subst j
        simp [coordinateReflectionSign] <;> ring
      · simp [coordinateReflectionSign, Finset.mem_singleton, hji] <;> ring


theorem lem_even_fold_face_gluing
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
            (coordinateFold (foldedCubeCenter w r I P) I P x)) :
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
  by_cases hiP : i ∈ P
  · let lo : SpatialCoordinates d := fun j =>
      if j ∈ I then
        if j ∈ P then w j - r / 2 else w j - 3 * r / 2
      else w j - r / 2
    let hi₀ : SpatialCoordinates d := fun j =>
      if j ∈ I then
        if j ∈ P then w j + 3 * r / 2 else w j + r / 2
      else w j + r / 2
    have hΩ : openBox lo hi₀ = foldedCube w r hr I P := by
      apply Opens.ext
      ext x
      rw [SetLike.mem_coe, mem_openBox_iff]
      change (∀ j, lo j < x j ∧ x j < hi₀ j) ↔
        x ∈ Set.pi Set.univ (fun j =>
          if j ∈ I then
            (if j ∈ P then Set.Ioo (w j - r / 2) (w j + 3 * r / 2)
             else Set.Ioo (w j - 3 * r / 2) (w j + r / 2))
          else Set.Ioo (w j - r / 2) (w j + r / 2))
      simp only [Set.mem_univ_pi]
      change (∀ j, lo j < x j ∧ x j < hi₀ j) ↔
        ∀ j, x j ∈ if j ∈ I then
          (if j ∈ P then Set.Ioo (w j - r / 2) (w j + 3 * r / 2)
           else Set.Ioo (w j - 3 * r / 2) (w j + r / 2))
        else Set.Ioo (w j - r / 2) (w j + r / 2)
      constructor
      · intro hx j
        by_cases hj : j ∈ I
        · by_cases hjP : j ∈ P
          · have h := hx j
            simp [hj, hjP, lo, hi₀] at h ⊢
            exact h
          · have h := hx j
            simp [hj, hjP, lo, hi₀] at h ⊢
            exact h
        · have h := hx j
          simp [hj, lo, hi₀, Set.mem_Ioo] at h ⊢
          exact h
      · intro hx j
        by_cases hj : j ∈ I
        · by_cases hjP : j ∈ P
          · have h := hx j
            simp [hj, hjP, lo, hi₀] at h ⊢
            exact h
          · have h := hx j
            simp [hj, hjP, lo, hi₀] at h ⊢
            exact h
        · have h := hx j
          simp [hj, lo, hi₀, Set.mem_Ioo] at h ⊢
          exact h
    have hU : openBox lo (doubledCorner lo hi₀ i) =
        foldedCube w r hr (insert i I) P := by
      apply Opens.ext
      ext x
      rw [SetLike.mem_coe, mem_openBox_iff]
      change (∀ j, lo j < x j ∧ x j < doubledCorner lo hi₀ i j) ↔
        x ∈ Set.pi Set.univ (fun j =>
          if j ∈ insert i I then
            (if j ∈ P then Set.Ioo (w j - r / 2) (w j + 3 * r / 2)
             else Set.Ioo (w j - 3 * r / 2) (w j + r / 2))
          else Set.Ioo (w j - r / 2) (w j + r / 2))
      simp only [Set.mem_univ_pi]
      change (∀ j, lo j < x j ∧ x j < doubledCorner lo hi₀ i j) ↔
        ∀ j, x j ∈ if j ∈ insert i I then
          (if j ∈ P then Set.Ioo (w j - r / 2) (w j + 3 * r / 2)
           else Set.Ioo (w j - 3 * r / 2) (w j + r / 2))
        else Set.Ioo (w j - r / 2) (w j + r / 2)
      constructor
      · intro hx j
        by_cases hji : j = i
        · subst j
          have h := hx i
          simp [lo, hi₀, doubledCorner, hi, hiP, Set.mem_Ioo] at h ⊢
          constructor <;> linarith [h.1, h.2]
        · have hji' : j ∉ insert i I ↔ j ∉ I := by simp [hji]
          by_cases hj : j ∈ I
          · by_cases hjP : j ∈ P
            · have h := hx j
              simp [Finset.mem_insert, hj, hjP, hji, lo, hi₀, doubledCorner] at h ⊢
              exact h
            · have h := hx j
              simp [Finset.mem_insert, hj, hjP, hji, lo, hi₀, doubledCorner] at h ⊢
              exact h
          · have h := hx j
            simp [Finset.mem_insert, hj, hji, lo, hi₀, doubledCorner,
              Set.mem_Ioo] at h ⊢
            exact h
      · intro hx j
        by_cases hji : j = i
        · subst j
          have h := hx i
          simp [lo, hi₀, doubledCorner, hi, hiP, Set.mem_Ioo] at h ⊢
          constructor <;> linarith [h.1, h.2]
        · by_cases hj : j ∈ I
          · by_cases hjP : j ∈ P
            · have h := hx j
              simp [Finset.mem_insert, hj, hjP, hji, lo, hi₀, doubledCorner] at h ⊢
              exact h
            · have h := hx j
              simp [Finset.mem_insert, hj, hjP, hji, lo, hi₀, doubledCorner] at h ⊢
              exact h
          · have h := hx j
            simp [Finset.mem_insert, hj, hji, lo, hi₀, doubledCorner,
              Set.mem_Ioo] at h ⊢
            exact h
    let Db : EvenReflectionDomain d := boxEvenReflectionDomain lo hi₀ i
    have hDbΩ : Db.Ω = foldedCube w r hr I P := by
      simpa [Db] using hΩ
    have hDbU : Db.U = foldedCube w r hr (insert i I) P := by
      simpa [Db] using hU
    let D : EvenReflectionDomain d :=
      { z := Db.z
        i := i
        Ω := foldedCube w r hr I P
        U := foldedCube w r hr (insert i I) P
        mem_iff := by
          intro x
          rw [← hDbΩ, ← hDbU]
          exact Db.mem_iff x
        symm := by
          rw [← hDbU]
          exact Db.symm }
    let z : SpatialCoordinates d := foldedCubeCenter w r (insert i I) P
    have hz : z i = D.z i := by
      dsimp [D, Db, boxEvenReflectionDomain]
      simp [z, foldedCubeCenter, lo, hi₀, upperFacePoint, hi, hiP]
    have hcoord (x : SpatialCoordinates d) :
        coordinateFold (foldedCubeCenter w r I P) I P x =
          coordinateFold z I P x := by
      funext j
      by_cases hj : j ∈ I
      · have hji : j ≠ i := by
          intro hji
          exact hi (hji ▸ hj)
        simp [coordinateFold, foldedCubeCenter, z, hj, hji]
      · simp [coordinateFold, hj]
    have hfold : ((af.val : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (D.Ω : Set (SpatialCoordinates d))]
        foldedCoefficientP (a.val : SpatialCoordinates d → ℝ) z I P) := by
      filter_upwards [ha] with x hx
      rw [hx]
      rw [hcoord]
      rfl
    have hac := lane2_evenExtensionCoefficient_fold_up D af
      (a := (a.val : SpatialCoordinates d → ℝ)) (z := z) (I := I) (P := P)
      hi hz hfold
    have hweak := D.evenExtension_mem_weak vf.property
    have hRcong : coordinateReflection z {i} =
        coordinateReflection D.z {i} :=
      coordinateReflection_single_congr z D.z i hz
    have hfold_le (x : SpatialCoordinates d) (hx : x i ≤ D.z i) :
        coordinateFold z (insert i I) P x =
          coordinateFold (foldedCubeCenter w r I P) I P x := by
      calc
        coordinateFold z (insert i I) P x = coordinateFold z I P x := by
          simpa only [Finset.insert_eq_of_mem hiP] using
            (lane2_fold_insert_both_of_le (z := z) (I := I) (P := P)
              hi (by rw [hz]; exact hx))
        _ = coordinateFold (foldedCubeCenter w r I P) I P x := (hcoord x).symm
    have hfold_ge (x : SpatialCoordinates d) (hx : D.z i ≤ x i) :
        coordinateFold z (insert i I) P x =
          coordinateFold (foldedCubeCenter w r I P) I P
            (coordinateReflection D.z {i} x) := by
      calc
        coordinateFold z (insert i I) P x =
            coordinateFold z I P (coordinateReflection z {i} x) := by
          simpa only [Finset.insert_eq_of_mem hiP] using
            (lane2_fold_insert_both_of_ge (z := z) (I := I) (P := P)
              hi (by rw [hz]; exact hx))
        _ = coordinateFold (foldedCubeCenter w r I P) I P
            (coordinateReflection D.z {i} x) := by
          rw [hcoord, hRcong]
    have hfac_le (j : Fin d) (x : SpatialCoordinates d) (hx : x i < D.z i) :
        (if j ∈ insert i I then
            coordinateReflectionSign P j *
              (if x j < z j then -1 else 1)
          else 1) =
          (if j ∈ I then
            coordinateReflectionSign P j *
              (if x j < foldedCubeCenter w r I P j then -1 else 1)
          else 1) := by
      by_cases hji : j = i
      · subst j
        have hxz : x i < z i := by rw [hz]; exact hx
        have hxi : x i < w i + r / 2 := by
          simpa [z, foldedCubeCenter, hiP] using hxz
        have hnot : ¬ z i ≤ x i := not_le_of_gt hxz
        simp [hi, hiP, coordinateReflectionSign, hxi, hnot]
      · simp [Finset.mem_insert, hji, z, foldedCubeCenter]
    have hfac_ge (j : Fin d) (x : SpatialCoordinates d) (hx : D.z i < x i) :
        (if j ∈ insert i I then
            coordinateReflectionSign P j *
              (if x j < z j then -1 else 1)
          else 1) =
          coordinateReflectionSign {i} j *
            (if j ∈ I then
              coordinateReflectionSign P j *
                (if (coordinateReflection D.z {i} x) j <
                    foldedCubeCenter w r I P j then -1 else 1)
            else 1) := by
      by_cases hji : j = i
      · subst j
        have hzx : z i < x i := by rw [hz]; exact hx
        have hxi : ¬ x i < w i + r / 2 := by
          intro hxi
          have : x i < z i := by simpa [z, foldedCubeCenter, hiP] using hxi
          linarith
        have hnot : ¬ x i < z i := not_lt_of_ge (le_of_lt hzx)
        simp [hi, hiP, coordinateReflectionSign, hxi, hnot]
      · simp [Finset.mem_insert, hji, z, foldedCubeCenter,
          coordinateReflectionSign,
          coordinateReflection_single_apply_of_ne D.z hji]
    refine ⟨D.evenExtensionCoefficient af, ⟨D.evenExtension vf, hweak⟩,
      ?_, ?_, ?_⟩
    · change ((D.evenExtensionCoefficient af).val : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (foldedCube w r hr (insert i I) P : Set (SpatialCoordinates d))]
        foldedCoefficientP (a.val : SpatialCoordinates d → ℝ) z (insert i I) (insert i P) at hac
      rw [Finset.insert_eq_of_mem hiP] at hac
      simpa only [foldedCoefficientP] using hac
    · have hmp := coordinateReflection_domain_measurePreserving D.z {i}
          D.preimage_Ω
      have hvR := hmp.quasiMeasurePreserving.ae hv
      have hR' := ae_restrict_of_ae (μ := (volume : Measure (SpatialCoordinates d)))
        (s := (D.U : Set (SpatialCoordinates d)))
        ((ae_restrict_iff' (μ := (volume : Measure (SpatialCoordinates d)))
          D.reflected.isOpen.measurableSet).mp hvR)
      have hvU := ae_restrict_of_ae (μ := (volume : Measure (SpatialCoordinates d)))
        (s := (D.U : Set (SpatialCoordinates d)))
        ((ae_restrict_iff' (μ := (volume : Measure (SpatialCoordinates d)))
          D.Ω.isOpen.measurableSet).mp hv)
      filter_upwards [D.evenExtension_fst_coeFn vf, hR', hvU,
        D.ae_mem_or_mem] with x he hvr hvx hmem
      rcases hmem with hx | hx
      · rw [he, Set.indicator_of_mem hx,
          Set.indicator_of_notMem (D.notMem_reflected_of_mem_Ω hx), add_zero]
        rw [hvx hx, hfold_le x (le_of_lt ((D.mem_iff x).mp hx).2)]
      · rw [he, Set.indicator_of_notMem (D.notMem_Ω_of_mem_reflected hx),
          Set.indicator_of_mem hx, zero_add, Function.comp_apply]
        rw [hvr hx, hfold_ge x (le_of_lt ((D.mem_reflected_iff x).mp hx).2)]
    · intro j
      have hmp := coordinateReflection_domain_measurePreserving D.z {i}
          D.preimage_Ω
      have hgR := hmp.quasiMeasurePreserving.ae (hg j)
      have hR' := ae_restrict_of_ae (μ := (volume : Measure (SpatialCoordinates d)))
        (s := (D.U : Set (SpatialCoordinates d)))
        ((ae_restrict_iff' (μ := (volume : Measure (SpatialCoordinates d)))
          D.reflected.isOpen.measurableSet).mp hgR)
      have hgU := ae_restrict_of_ae (μ := (volume : Measure (SpatialCoordinates d)))
        (s := (D.U : Set (SpatialCoordinates d)))
        ((ae_restrict_iff' (μ := (volume : Measure (SpatialCoordinates d)))
          D.Ω.isOpen.measurableSet).mp (hg j))
      filter_upwards [D.evenExtension_snd_coeFn vf j, hR', hgU,
        D.ae_mem_or_mem] with x he hgr hgu hmem
      change ((D.evenExtension vf).2 j : SpatialCoordinates d → ℝ) x = _
      rcases hmem with hx | hx
      · rw [he, Set.indicator_of_mem hx,
          Set.indicator_of_notMem (D.notMem_reflected_of_mem_Ω hx), add_zero,
          hfac_le j x ((D.mem_iff x).mp hx).2]
        have hgu' := hgu hx
        change ((vf : SobolevData D.Ω).2 j : SpatialCoordinates d → ℝ) x = _ at hgu'
        rw [hgu', hfold_le x (le_of_lt ((D.mem_iff x).mp hx).2)]
      · rw [he, Set.indicator_of_notMem (D.notMem_Ω_of_mem_reflected hx),
          Set.indicator_of_mem hx, zero_add]
        have hgr' := hgr hx
        change ((vf : SobolevData D.Ω).2 j : SpatialCoordinates d → ℝ)
          (coordinateReflection D.z {i} x) = _ at hgr'
        rw [hgr', hfold_ge x (le_of_lt ((D.mem_reflected_iff x).mp hx).2),
          hfac_ge j x ((D.mem_reflected_iff x).mp hx).2]
        ring
  · exact aux_lem_even_fold_face_gluing_down d w r hr I P i hi a v af vf ha hv hg hiP

end Paper

