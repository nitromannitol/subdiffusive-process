module

public import SubdiffusiveProcess.VariationalResponses.KilledTest
public import SubdiffusiveProcess.VariationalResponses.OddVanishing
public import SubdiffusiveProcess.VariationalResponses.FoldedIteration

@[expose] public section

/-!
# The reflection transport on the killed test class

The odd-extension transport of `SubdiffusiveProcess.VariationalResponses.OddIteration` is run
here against KILLED tests, which is the class a Dirichlet cell problem supplies:
a cell-harmonic `u` with `u - φ ∈ H¹₀` satisfies the forced equation only
against `H¹₀` tests, never against the whole weak graph.  The step that makes
this work is `restrictSub_mem_killed`: for a killed test `ψ` on the
doubled domain, `ψ|_Ω - R*(ψ|_{ρΩ})` is a killed test on the lower half, so the
bilinearity of the coefficient form turns the two half-integrals into a single
evaluation of the load on an admissible test.
-/

open MeasureTheory Set TopologicalSpace

noncomputable section

namespace SubdiffusiveProcess

variable {d : ℕ}

/-! ## Transport of the forced equation -/

/-- `w` solves the forced weak equation on `U` with coefficient `A` and load `L`. -/
def SolvesOn {U : Opens (SpatialCoordinates d)} (A : PositiveCoefficient U)
    (w : SobolevData U) (L : SobolevData U → ℝ) : Prop :=
  ∀ v ∈ killedSobolevGraph U, sobolevCoefficientForm A w v = L v

namespace EvenReflectionDomain

variable (D : EvenReflectionDomain d)

/-- The forced-equation transport of `oddExtension_weak_equation`, with the
load carried as a plain function rather than a continuous linear map: the
transport uses only its values, and the iteration then needs no continuous
linear structure on the reflected loads. -/
theorem oddExtension_killed_equation (a : PositiveCoefficient D.Ω)
    {u : SobolevData D.Ω} (L : SobolevData D.Ω → ℝ)
    (hL : ∀ v ∈ killedSobolevGraph D.Ω, sobolevCoefficientForm a u v = L v)
    {ψ : SobolevData D.U} (hψ : ψ ∈ killedSobolevGraph D.U) :
    sobolevCoefficientForm (D.evenExtensionCoefficient a) (D.oddExtension u) ψ =
      L (sobolevDataRestrict D.Ω_le ψ - D.reflectedRestrict ψ) := by
  rw [sobolevCoefficientForm_oddExtension,
    ← hL _ (D.restrictSub_mem_killed hψ), map_sub]

end EvenReflectionDomain

/-- **The upward doubling step, carrying the forced equation.** -/
theorem solves_step_up (D : EvenReflectionDomain d)
    {B C : Opens (SpatialCoordinates d)} (hB : D.Ω = B) (hC : D.U = C)
    (a : PositiveCoefficient B) {w : SobolevData B} (hw : w ∈ killedSobolevGraph B)
    (L : SobolevData B → ℝ) (hL : SolvesOn a w L) :
    ∃ (A : PositiveCoefficient C) (v : SobolevData C) (L' : SobolevData C → ℝ),
      v ∈ killedSobolevGraph C ∧ SolvesOn A v L' ∧
      ((v.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (B : Set (SpatialCoordinates d))]
          (w.1 : SpatialCoordinates d → ℝ)) ∧
      ((A.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (B : Set (SpatialCoordinates d))]
          (a.val : SpatialCoordinates d → ℝ)) ∧
      (∀ᵐ x ∂(volume.restrict (C : Set (SpatialCoordinates d))),
        (v.1 : SpatialCoordinates d → ℝ) (coordinateReflection D.z {D.i} x)
          = -((v.1 : SpatialCoordinates d → ℝ) x)) := by
  subst hB
  subst hC
  exact ⟨D.evenExtensionCoefficient a, D.oddExtension w,
    fun ψ => L (sobolevDataRestrict D.Ω_le ψ - D.reflectedRestrict ψ),
    _root_.SubdiffusiveProcess.EvenReflectionDomain.oddExtension_mem_killed D hw,
    fun ψ hψ => D.oddExtension_killed_equation a L hL hψ,
    D.oddExtension_ae_eq_on_Omega w,
    D.evenExtensionCoefficient_ae_Ω a,
    D.oddExtension_ae_odd w⟩

/-- **The downward doubling step, carrying the forced equation.** -/
theorem solves_step_down (D : EvenReflectionDomain d)
    {B C : Opens (SpatialCoordinates d)} (hB : D.reflected = B) (hC : D.U = C)
    (b : PositiveCoefficient B) {w : SobolevData B} (hw : w ∈ killedSobolevGraph B)
    (L : SobolevData B → ℝ) (hL : SolvesOn b w L) :
    ∃ (A : PositiveCoefficient C) (v : SobolevData C) (L' : SobolevData C → ℝ),
      v ∈ killedSobolevGraph C ∧ SolvesOn A v L' ∧
      ((v.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (B : Set (SpatialCoordinates d))]
          (w.1 : SpatialCoordinates d → ℝ)) ∧
      ((A.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (B : Set (SpatialCoordinates d))]
          (b.val : SpatialCoordinates d → ℝ)) ∧
      (∀ᵐ x ∂(volume.restrict (C : Set (SpatialCoordinates d))),
        (v.1 : SpatialCoordinates d → ℝ) (coordinateReflection D.z {D.i} x)
          = -((v.1 : SpatialCoordinates d → ℝ) x)) := by
  subst hB
  subst hC
  -- pull the datum, the coefficient and the load down to the lower half
  set a : PositiveCoefficient D.Ω :=
    reflectionCoefficient D.z {D.i} D.preimage_reflected b with ha
  set v₀ : SobolevData D.Ω :=
    reflectionSobolevData D.z {D.i} D.preimage_reflected w with hv₀
  have hsolve : SolvesOn a v₀
      (fun v => L (reflectionSobolevData D.z {D.i} D.preimage_Ω v)) := by
    intro v hv
    have hinv := reflectionSobolevData_inverse D.z {D.i} D.preimage_Ω v
    have hrefl := sobolevCoefficientForm_reflection D.z {D.i} D.preimage_reflected b w
      (reflectionSobolevData D.z {D.i} D.preimage_Ω v)
    rw [hinv] at hrefl
    rw [ha, hv₀, hrefl]
    exact hL _ (reflectionSobolevData_mem_killed D.z {D.i} D.preimage_Ω hv)
  set X := D.oddExtension v₀ with hX
  refine ⟨D.evenExtensionCoefficient a, -X,
    fun ψ => -((fun v => L (reflectionSobolevData D.z {D.i} D.preimage_Ω v))
      (sobolevDataRestrict D.Ω_le ψ - D.reflectedRestrict ψ)),
    neg_mem (oddExtension_reflected_mem_killed D hw), ?_, ?_, ?_, ?_⟩
  · intro ψ hψ
    have h := D.oddExtension_killed_equation a
      (fun v => L (reflectionSobolevData D.z {D.i} D.preimage_Ω v)) hsolve hψ
    rw [show sobolevCoefficientForm (D.evenExtensionCoefficient a) (-X) ψ =
      -(sobolevCoefficientForm (D.evenExtensionCoefficient a) X ψ) by
        rw [map_neg]; rfl]
    rw [hX, h]
  · have hneg : (((-X).1 : DomainL2 D.U) : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (D.U : Set (SpatialCoordinates d))]
          fun x => -((X.1 : SpatialCoordinates d → ℝ) x) := Lp.coeFn_neg (X.1)
    have hneg' := ae_restrict_of_ae_restrict_of_subset
      (μ := (volume : Measure (SpatialCoordinates d)))
      (s := (D.reflected : Set (SpatialCoordinates d)))
      (t := (D.U : Set (SpatialCoordinates d))) D.reflected_le hneg
    filter_upwards [hneg', D.oddExtension_reflected_ae_eq_neg w] with x h1 h2
    rw [h1, h2, neg_neg]
  · exact (D.evenExtensionCoefficient_ae_reflected a).trans
      (D.reflectedCoefficient_reflection_ae b)
  · refine ae_odd_of_ae_eq D.z {D.i} D.symm
      (f := (((-X).1 : DomainL2 D.U) : SpatialCoordinates d → ℝ))
      (g := fun x => -((X.1 : SpatialCoordinates d → ℝ) x)) (Lp.coeFn_neg (X.1)) ?_
    filter_upwards [D.oddExtension_ae_odd v₀] with x hx
    simp only [hX] at hx ⊢
    rw [hx]

/-- **Doubling a box across every face in `I`, carrying the forced equation.**
The invariant of `exists_doubled_box` is enlarged by a coefficient and a
load: each doubling step replaces the coefficient by its even extension and the
load by its odd reflection, and both agree almost everywhere with the original
data on the original box. -/
theorem exists_doubled_box_equation (lo hi : SpatialCoordinates d)
    (hlohi : ∀ j, lo j < hi j) (I : Finset (Fin d))
    (a : PositiveCoefficient (openBox lo hi))
    {u : SobolevData (openBox lo hi)} (hu : u ∈ killedSobolevGraph (openBox lo hi))
    (L : SobolevData (openBox lo hi) → ℝ) (hL : SolvesOn a u L) :
    ∃ (lo' hi' : SpatialCoordinates d) (A : PositiveCoefficient (openBox lo' hi'))
      (w : SobolevData (openBox lo' hi')) (L' : SobolevData (openBox lo' hi') → ℝ),
      w ∈ killedSobolevGraph (openBox lo' hi') ∧
      SolvesOn A w L' ∧
      (∀ j ∈ I, lo' j < lo j ∧ hi j < hi' j) ∧
      (∀ j, j ∉ I → lo' j = lo j ∧ hi' j = hi j) ∧
      ((w.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (openBox lo hi : Set (SpatialCoordinates d))]
          (u.1 : SpatialCoordinates d → ℝ)) ∧
      ((A.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (openBox lo hi : Set (SpatialCoordinates d))]
          (a.val : SpatialCoordinates d → ℝ)) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    exact ⟨lo, hi, a, u, L, hu, hL, by simp, fun j _ => ⟨rfl, rfl⟩,
      Filter.EventuallyEq.refl _ _, Filter.EventuallyEq.refl _ _⟩
  | @insert i I hiI ih =>
    obtain ⟨lo₀, hi₀, A₀, w, L₀, hw, hsolve, hstrict, heq, hae, hcoef⟩ := ih
    have hmono : ∀ j, lo₀ j ≤ lo j ∧ hi j ≤ hi₀ j := by
      intro j
      by_cases hj : j ∈ I
      · exact ⟨(hstrict j hj).1.le, (hstrict j hj).2.le⟩
      · exact ⟨(heq j hj).1.le, (heq j hj).2.ge⟩
    have hlo₀hi₀ : ∀ j, lo₀ j < hi₀ j := fun j =>
      lt_of_le_of_lt (hmono j).1 (lt_of_lt_of_le (hlohi j) (hmono j).2)
    obtain ⟨hloi, hhii⟩ : lo₀ i = lo i ∧ hi₀ i = hi i := heq i hiI
    obtain ⟨A₁, w₁, L₁, hw₁, hsolve₁, hae₁, hcoef₁, -⟩ :=
      solves_step_up (boxEvenReflectionDomain lo₀ hi₀ i) rfl rfl A₀ hw L₀ hsolve
    obtain ⟨A₂, w₂, L₂, hw₂, hsolve₂, hae₂, hcoef₂, -⟩ :=
      solves_step_down
        (boxEvenReflectionDomain (lowerDoubledCorner lo₀ (doubledCorner lo₀ hi₀ i) i)
          (Function.update (doubledCorner lo₀ hi₀ i) i (lo₀ i)) i)
        (boxEvenReflectionDomain_mirror_reflected lo₀ (doubledCorner lo₀ hi₀ i) i)
        (boxEvenReflectionDomain_mirror_U lo₀ (doubledCorner lo₀ hi₀ i) i) A₁ hw₁ L₁ hsolve₁
    have hsub1 : (openBox lo hi : Set (SpatialCoordinates d)) ⊆
        (openBox lo₀ hi₀ : Set (SpatialCoordinates d)) :=
      openBox_subset_openBox (fun j => (hmono j).1) (fun j => (hmono j).2)
    have hstep : ∀ j, hi₀ j ≤ doubledCorner lo₀ hi₀ i j := by
      intro j
      by_cases hj : j = i
      · subst hj
        rw [doubledCorner_apply_self]
        linarith [hlo₀hi₀ j]
      · rw [doubledCorner_apply_of_ne _ _ hj]
    have hsub2 : (openBox lo hi : Set (SpatialCoordinates d)) ⊆
        (openBox lo₀ (doubledCorner lo₀ hi₀ i) : Set (SpatialCoordinates d)) :=
      openBox_subset_openBox (fun j => (hmono j).1)
        (fun j => le_trans (hmono j).2 (hstep j))
    refine ⟨lowerDoubledCorner lo₀ (doubledCorner lo₀ hi₀ i) i, doubledCorner lo₀ hi₀ i,
      A₂, w₂, L₂, hw₂, hsolve₂, ?_, ?_, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with hjeq | hjI
      · subst hjeq
        rw [lowerDoubledCorner, Function.update_self, doubledCorner_apply_self]
        constructor <;> linarith [hlohi j]
      · have hne : j ≠ i := by rintro rfl; exact hiI hjI
        rw [lowerDoubledCorner, Function.update_of_ne hne,
          doubledCorner_apply_of_ne _ _ hne]
        exact hstrict j hjI
    · intro j hj
      have hji : j ≠ i := fun h => hj (Finset.mem_insert.mpr (Or.inl h))
      have hjI : j ∉ I := fun h => hj (Finset.mem_insert.mpr (Or.inr h))
      rw [lowerDoubledCorner, Function.update_of_ne hji,
        doubledCorner_apply_of_ne _ _ hji]
      exact heq j hjI
    · exact Filter.EventuallyEq.trans
        (ae_restrict_of_ae_restrict_of_subset
          (μ := (volume : Measure (SpatialCoordinates d))) hsub2 hae₂)
        (Filter.EventuallyEq.trans
          (ae_restrict_of_ae_restrict_of_subset
            (μ := (volume : Measure (SpatialCoordinates d))) hsub1 hae₁) hae)
    · exact Filter.EventuallyEq.trans
        (ae_restrict_of_ae_restrict_of_subset
          (μ := (volume : Measure (SpatialCoordinates d))) hsub2 hcoef₂)
        (Filter.EventuallyEq.trans
          (ae_restrict_of_ae_restrict_of_subset
            (μ := (volume : Measure (SpatialCoordinates d))) hsub1 hcoef₁) hcoef)

/-- **The odd extension over the active set, carrying the forced equation.**
This is `exists_odd_doubled_box` with the coefficient and the load
transported alongside the datum: the resulting `w` solves the forced equation on
the doubled box for the iterated even extension `A` of the coefficient and the
iterated odd reflection `L'` of the load, and both `w` and `A` agree almost
everywhere with the original data on the original box. -/
theorem exists_odd_doubled_box_equation (lo hi x₀ : SpatialCoordinates d)
    (hlohi : ∀ j, lo j < hi j) (hx₀ : ∀ j, x₀ j ∈ Set.Icc (lo j) (hi j))
    (i₀ : Fin d) (hface : x₀ i₀ = lo i₀ ∨ x₀ i₀ = hi i₀)
    (I : Finset (Fin d)) (hi₀I : i₀ ∉ I)
    (hinterior : ∀ j, j ∉ I → j ≠ i₀ → lo j < x₀ j ∧ x₀ j < hi j)
    (a : PositiveCoefficient (openBox lo hi))
    {u : SobolevData (openBox lo hi)} (hu : u ∈ killedSobolevGraph (openBox lo hi))
    (L : SobolevData (openBox lo hi) → ℝ) (hL : SolvesOn a u L) :
    ∃ (B : Opens (SpatialCoordinates d)) (A : PositiveCoefficient B)
      (w : SobolevData B) (L' : SobolevData B → ℝ),
      w ∈ killedSobolevGraph B ∧
      SolvesOn A w L' ∧
      x₀ ∈ (B : Set (SpatialCoordinates d)) ∧
      (openBox lo hi : Set (SpatialCoordinates d)) ⊆ (B : Set (SpatialCoordinates d)) ∧
      Set.MapsTo (coordinateReflection x₀ {i₀}) (B : Set (SpatialCoordinates d))
        (B : Set (SpatialCoordinates d)) ∧
      ((w.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (openBox lo hi : Set (SpatialCoordinates d))]
          (u.1 : SpatialCoordinates d → ℝ)) ∧
      ((A.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (openBox lo hi : Set (SpatialCoordinates d))]
          (a.val : SpatialCoordinates d → ℝ)) ∧
      (∀ᵐ x ∂(volume.restrict (B : Set (SpatialCoordinates d))),
        (w.1 : SpatialCoordinates d → ℝ) (coordinateReflection x₀ {i₀} x)
          = -((w.1 : SpatialCoordinates d → ℝ) x)) := by
  classical
  obtain ⟨lo₀, hi₀, A₀, w₀, L₀, hw₀, hsolve₀, hstrict, heq, hae₀, hcoef₀⟩ :=
    exists_doubled_box_equation lo hi hlohi I a hu L hL
  have hmono : ∀ j, lo₀ j ≤ lo j ∧ hi j ≤ hi₀ j := by
    intro j
    by_cases hj : j ∈ I
    · exact ⟨(hstrict j hj).1.le, (hstrict j hj).2.le⟩
    · exact ⟨(heq j hj).1.le, (heq j hj).2.ge⟩
  have hlo₀hi₀ : ∀ j, lo₀ j < hi₀ j := fun j =>
    lt_of_le_of_lt (hmono j).1 (lt_of_lt_of_le (hlohi j) (hmono j).2)
  obtain ⟨hloi, hhii⟩ : lo₀ i₀ = lo i₀ ∧ hi₀ i₀ = hi i₀ := heq i₀ hi₀I
  have hbase : (openBox lo hi : Set (SpatialCoordinates d)) ⊆
      (openBox lo₀ hi₀ : Set (SpatialCoordinates d)) :=
    openBox_subset_openBox (fun j => (hmono j).1) (fun j => (hmono j).2)
  have hside : ∀ j, j ≠ i₀ → lo₀ j < x₀ j ∧ x₀ j < hi₀ j := by
    intro j hj
    by_cases hjI : j ∈ I
    · exact ⟨lt_of_lt_of_le (hstrict j hjI).1 (hx₀ j).1,
        lt_of_le_of_lt (hx₀ j).2 (hstrict j hjI).2⟩
    · obtain ⟨h1, h2⟩ := heq j hjI
      obtain ⟨h3, h4⟩ := hinterior j hjI hj
      exact ⟨h1 ▸ h3, h2 ▸ h4⟩
  rcases hface with hlow | hhigh
  · refine ⟨openBox (lowerDoubledCorner lo₀ hi₀ i₀) hi₀, ?_⟩
    obtain ⟨A, w, L', hw, hsolve, hae, hcoef, hodd⟩ :=
      solves_step_down
        (boxEvenReflectionDomain (lowerDoubledCorner lo₀ hi₀ i₀)
          (Function.update hi₀ i₀ (lo₀ i₀)) i₀)
        (boxEvenReflectionDomain_mirror_reflected lo₀ hi₀ i₀)
        (boxEvenReflectionDomain_mirror_U lo₀ hi₀ i₀) A₀ hw₀ L₀ hsolve₀
    have hz : (boxEvenReflectionDomain (lowerDoubledCorner lo₀ hi₀ i₀)
        (Function.update hi₀ i₀ (lo₀ i₀)) i₀).z i₀ = x₀ i₀ := by
      show upperFacePoint (lowerDoubledCorner lo₀ hi₀ i₀)
        (Function.update hi₀ i₀ (lo₀ i₀)) i₀ i₀ = x₀ i₀
      rw [upperFacePoint_apply_self, Function.update_self, hloi, hlow]
    have hcong : coordinateReflection
        (boxEvenReflectionDomain (lowerDoubledCorner lo₀ hi₀ i₀)
          (Function.update hi₀ i₀ (lo₀ i₀)) i₀).z {i₀} =
        coordinateReflection x₀ {i₀} :=
      coordinateReflection_single_congr _ _ i₀ hz
    have hlower : ∀ j, lowerDoubledCorner lo₀ hi₀ i₀ j ≤ lo₀ j := by
      intro j
      by_cases hj : j = i₀
      · subst hj
        rw [lowerDoubledCorner, Function.update_self]
        linarith [hlo₀hi₀ j]
      · rw [lowerDoubledCorner, Function.update_of_ne hj]
    refine ⟨A, w, L', hw, hsolve, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_openBox_iff]
      intro j
      by_cases hj : j = i₀
      · subst hj
        rw [lowerDoubledCorner, Function.update_self, hlow, ← hloi]
        refine ⟨by linarith [hlo₀hi₀ j], ?_⟩
        have h2 := hlo₀hi₀ j
        rw [hloi, ← hlow] at h2 ⊢
        linarith
      · exact ⟨lt_of_le_of_lt (hlower j) (hside j hj).1, (hside j hj).2⟩
    · exact openBox_subset_openBox
        (fun j => le_trans (hlower j) (hmono j).1) (fun j => (hmono j).2)
    · intro x hx
      have hU := boxEvenReflectionDomain_mirror_U lo₀ hi₀ i₀
      have hxU : x ∈ (boxEvenReflectionDomain (lowerDoubledCorner lo₀ hi₀ i₀)
          (Function.update hi₀ i₀ (lo₀ i₀)) i₀).U := by rw [hU]; exact hx
      have hres := (EvenReflectionDomain.reflection_mem_U_iff
        (boxEvenReflectionDomain (lowerDoubledCorner lo₀ hi₀ i₀)
          (Function.update hi₀ i₀ (lo₀ i₀)) i₀) x).mpr hxU
      rw [hU] at hres
      rw [← hcong]
      exact hres
    · exact Filter.EventuallyEq.trans
        (ae_restrict_of_ae_restrict_of_subset
          (μ := (volume : Measure (SpatialCoordinates d))) hbase hae) hae₀
    · exact Filter.EventuallyEq.trans
        (ae_restrict_of_ae_restrict_of_subset
          (μ := (volume : Measure (SpatialCoordinates d))) hbase hcoef) hcoef₀
    · rw [← hcong]; exact hodd
  · refine ⟨openBox lo₀ (doubledCorner lo₀ hi₀ i₀), ?_⟩
    obtain ⟨A, w, L', hw, hsolve, hae, hcoef, hodd⟩ :=
      solves_step_up (boxEvenReflectionDomain lo₀ hi₀ i₀) rfl rfl A₀ hw₀ L₀ hsolve₀
    have hz : (boxEvenReflectionDomain lo₀ hi₀ i₀).z i₀ = x₀ i₀ := by
      show upperFacePoint lo₀ hi₀ i₀ i₀ = x₀ i₀
      rw [upperFacePoint_apply_self, hhii, hhigh]
    have hcong : coordinateReflection (boxEvenReflectionDomain lo₀ hi₀ i₀).z {i₀} =
        coordinateReflection x₀ {i₀} :=
      coordinateReflection_single_congr _ _ i₀ hz
    have hupper : ∀ j, hi₀ j ≤ doubledCorner lo₀ hi₀ i₀ j := by
      intro j
      by_cases hj : j = i₀
      · subst hj
        rw [doubledCorner_apply_self]
        linarith [hlo₀hi₀ j]
      · rw [doubledCorner_apply_of_ne _ _ hj]
    refine ⟨A, w, L', hw, hsolve, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_openBox_iff]
      intro j
      by_cases hj : j = i₀
      · subst hj
        rw [doubledCorner_apply_self, hhigh, ← hhii]
        exact ⟨by linarith [hlo₀hi₀ j, (hmono j).1, (hx₀ j).1],
          by linarith [hlo₀hi₀ j]⟩
      · exact ⟨(hside j hj).1, lt_of_lt_of_le (hside j hj).2 (hupper j)⟩
    · exact openBox_subset_openBox (fun j => (hmono j).1)
        (fun j => le_trans (hmono j).2 (hupper j))
    · intro x hx
      rw [← hcong]
      exact (EvenReflectionDomain.reflection_mem_U_iff
        (boxEvenReflectionDomain lo₀ hi₀ i₀) x).mpr hx
    · exact Filter.EventuallyEq.trans
        (ae_restrict_of_ae_restrict_of_subset
          (μ := (volume : Measure (SpatialCoordinates d))) hbase hae) hae₀
    · exact Filter.EventuallyEq.trans
        (ae_restrict_of_ae_restrict_of_subset
          (μ := (volume : Measure (SpatialCoordinates d))) hbase hcoef) hcoef₀
    · rw [← hcong]; exact hodd

/-! ## The single-reflection doubling step, with the fold identity -/

/-- **The upward step.**  Reflecting across the upper `D.i`-face of the box,
which is the plane through `z` in that coordinate: the datum is odd-extended,
the coefficient becomes the fold over `(insert D.i I, insert D.i P)`, and the
load is reflected. -/
theorem fold_step_up (D : EvenReflectionDomain d)
    {B C : Opens (SpatialCoordinates d)} (hB : D.Ω = B) (hC : D.U = C)
    (hCb : Bornology.IsBounded (C : Set (SpatialCoordinates d)))
    {a0 : SpatialCoordinates d → ℝ} {z : SpatialCoordinates d} {I P : Finset (Fin d)}
    (hiI : D.i ∉ I) (hz : z D.i = D.z D.i)
    (A0 : PositiveCoefficient B)
    (hfold : (A0.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (B : Set (SpatialCoordinates d))] foldedCoefficientP a0 z I P)
    {w : SobolevData B} (hw : w ∈ killedSobolevGraph B)
    (L : SobolevData B → ℝ) (hL : SolvesOn A0 w L) :
    ∃ (A : PositiveCoefficient C) (v : SobolevData C) (L' : SobolevData C → ℝ),
      v ∈ killedSobolevGraph C ∧ SolvesOn A v L' ∧
      ((v.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (B : Set (SpatialCoordinates d))]
          (w.1 : SpatialCoordinates d → ℝ)) ∧
      ((A.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (C : Set (SpatialCoordinates d))]
          foldedCoefficientP a0 z (insert D.i I) (insert D.i P)) ∧
      (∀ᵐ x ∂(volume.restrict (C : Set (SpatialCoordinates d))),
        (v.1 : SpatialCoordinates d → ℝ) (coordinateReflection D.z {D.i} x)
          = -((v.1 : SpatialCoordinates d → ℝ) x)) ∧
      (∀ (z' : SpatialCoordinates d) (j : Fin d),
        coordinateReflection z' {j} ⁻¹' (B : Set (SpatialCoordinates d))
          = (B : Set (SpatialCoordinates d)) →
        coordinateReflection z' {j} ⁻¹' (C : Set (SpatialCoordinates d))
          = (C : Set (SpatialCoordinates d)) →
        (∀ x : SpatialCoordinates d,
          coordinateReflection D.z {D.i} (coordinateReflection z' {j} x)
            = coordinateReflection z' {j} (coordinateReflection D.z {D.i} x)) →
        (∀ᵐ x ∂(volume.restrict (B : Set (SpatialCoordinates d))),
          (w.1 : SpatialCoordinates d → ℝ) (coordinateReflection z' {j} x)
            = -((w.1 : SpatialCoordinates d → ℝ) x)) →
        ∀ᵐ x ∂(volume.restrict (C : Set (SpatialCoordinates d))),
          (v.1 : SpatialCoordinates d → ℝ) (coordinateReflection z' {j} x)
            = -((v.1 : SpatialCoordinates d → ℝ) x)) ∧
      (∀ g : SpatialCoordinates d → SpatialCoordinates d,
        BoundedField g → IsDivLoad (U := B) L g →
        ∃ g' : SpatialCoordinates d → SpatialCoordinates d,
          BoundedField g' ∧ IsDivLoad (U := C) L' g') := by
  subst hB
  subst hC
  exact ⟨D.evenExtensionCoefficient A0, D.oddExtension w,
    fun ψ => L (sobolevDataRestrict D.Ω_le ψ - D.reflectedRestrict ψ),
    _root_.SubdiffusiveProcess.EvenReflectionDomain.oddExtension_mem_killed D hw,
    fun ψ hψ => D.oddExtension_killed_equation A0 L hL hψ,
    D.oddExtension_ae_eq_on_Omega w,
    evenExtensionCoefficient_fold_up D A0 hiI hz hfold,
    D.oddExtension_ae_odd w,
    fun z' j hB' hC' hcomm hodd =>
      D.oddExtension_ae_odd_other z' j hB' hC' hcomm hodd,
    fun g hg hLg => ⟨D.oddReflectedField g,
      boundedField_oddReflectedField D hg,
      divLoad_up D hg hCb hLg⟩⟩

/-- **The downward step.**  Reflecting across the lower `D.i`-face: the new
coordinate is folded upward, so it enters `I` but not `P`. -/
theorem fold_step_down (D : EvenReflectionDomain d)
    {B C : Opens (SpatialCoordinates d)} (hB : D.reflected = B) (hC : D.U = C)
    (hCb : Bornology.IsBounded (C : Set (SpatialCoordinates d)))
    {a0 : SpatialCoordinates d → ℝ} {z : SpatialCoordinates d} {I P : Finset (Fin d)}
    (hiI : D.i ∉ I) (hiP : D.i ∉ P) (hz : z D.i = D.z D.i)
    (A0 : PositiveCoefficient B)
    (hfold : (A0.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (B : Set (SpatialCoordinates d))] foldedCoefficientP a0 z I P)
    {w : SobolevData B} (hw : w ∈ killedSobolevGraph B)
    (L : SobolevData B → ℝ) (hL : SolvesOn A0 w L) :
    ∃ (A : PositiveCoefficient C) (v : SobolevData C) (L' : SobolevData C → ℝ),
      v ∈ killedSobolevGraph C ∧ SolvesOn A v L' ∧
      ((v.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (B : Set (SpatialCoordinates d))]
          (w.1 : SpatialCoordinates d → ℝ)) ∧
      ((A.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (C : Set (SpatialCoordinates d))]
          foldedCoefficientP a0 z (insert D.i I) P) ∧
      (∀ᵐ x ∂(volume.restrict (C : Set (SpatialCoordinates d))),
        (v.1 : SpatialCoordinates d → ℝ) (coordinateReflection D.z {D.i} x)
          = -((v.1 : SpatialCoordinates d → ℝ) x)) ∧
      (∀ (z' : SpatialCoordinates d) (j : Fin d),
        coordinateReflection z' {j} ⁻¹' (B : Set (SpatialCoordinates d))
          = (B : Set (SpatialCoordinates d)) →
        coordinateReflection z' {j} ⁻¹' (C : Set (SpatialCoordinates d))
          = (C : Set (SpatialCoordinates d)) →
        (∀ x : SpatialCoordinates d,
          coordinateReflection D.z {D.i} (coordinateReflection z' {j} x)
            = coordinateReflection z' {j} (coordinateReflection D.z {D.i} x)) →
        (∀ᵐ x ∂(volume.restrict (B : Set (SpatialCoordinates d))),
          (w.1 : SpatialCoordinates d → ℝ) (coordinateReflection z' {j} x)
            = -((w.1 : SpatialCoordinates d → ℝ) x)) →
        ∀ᵐ x ∂(volume.restrict (C : Set (SpatialCoordinates d))),
          (v.1 : SpatialCoordinates d → ℝ) (coordinateReflection z' {j} x)
            = -((v.1 : SpatialCoordinates d → ℝ) x)) ∧
      (∀ g : SpatialCoordinates d → SpatialCoordinates d,
        BoundedField g → IsDivLoad (U := B) L g →
        ∃ g' : SpatialCoordinates d → SpatialCoordinates d,
          BoundedField g' ∧ IsDivLoad (U := C) L' g') := by
  subst hB
  subst hC
  set b : PositiveCoefficient D.Ω :=
    reflectionCoefficient D.z {D.i} D.preimage_reflected A0 with hb
  set v₀ : SobolevData D.Ω :=
    reflectionSobolevData D.z {D.i} D.preimage_reflected w with hv₀
  have hsolve : SolvesOn b v₀
      (fun v => L (reflectionSobolevData D.z {D.i} D.preimage_Ω v)) := by
    intro v hv
    have hinv := reflectionSobolevData_inverse D.z {D.i} D.preimage_Ω v
    have hrefl := sobolevCoefficientForm_reflection D.z {D.i} D.preimage_reflected A0 w
      (reflectionSobolevData D.z {D.i} D.preimage_Ω v)
    rw [hinv] at hrefl
    rw [hb, hv₀, hrefl]
    exact hL _ (reflectionSobolevData_mem_killed D.z {D.i} D.preimage_Ω hv)
  set X := D.oddExtension v₀ with hX
  refine ⟨D.evenExtensionCoefficient b, -X,
    fun ψ => -((fun v => L (reflectionSobolevData D.z {D.i} D.preimage_Ω v))
      (sobolevDataRestrict D.Ω_le ψ - D.reflectedRestrict ψ)),
    neg_mem (oddExtension_reflected_mem_killed D hw), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ψ hψ
    have h := D.oddExtension_killed_equation b
      (fun v => L (reflectionSobolevData D.z {D.i} D.preimage_Ω v)) hsolve hψ
    rw [show sobolevCoefficientForm (D.evenExtensionCoefficient b) (-X) ψ =
      -(sobolevCoefficientForm (D.evenExtensionCoefficient b) X ψ) by
        rw [map_neg]; rfl]
    rw [hX, h]
  · have hneg : (((-X).1 : DomainL2 D.U) : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (D.U : Set (SpatialCoordinates d))]
          fun x => -((X.1 : SpatialCoordinates d → ℝ) x) := Lp.coeFn_neg (X.1)
    have hneg' := ae_restrict_of_ae_restrict_of_subset
      (μ := (volume : Measure (SpatialCoordinates d)))
      (s := (D.reflected : Set (SpatialCoordinates d)))
      (t := (D.U : Set (SpatialCoordinates d))) D.reflected_le hneg
    filter_upwards [hneg', D.oddExtension_reflected_ae_eq_neg w] with x h1 h2
    rw [h1, h2, neg_neg]
  · exact evenExtensionCoefficient_fold_down D A0 hiI hiP hz hfold
  · refine ae_odd_of_ae_eq D.z {D.i} D.symm
      (f := (((-X).1 : DomainL2 D.U) : SpatialCoordinates d → ℝ))
      (g := fun x => -((X.1 : SpatialCoordinates d → ℝ) x)) (Lp.coeFn_neg (X.1)) ?_
    filter_upwards [D.oddExtension_ae_odd v₀] with x hx
    simp only [hX] at hx ⊢
    rw [hx]
  · intro z' j hB' hC' hcomm hodd
    have hOm' : coordinateReflection z' {j} ⁻¹'
        (D.Ω : Set (SpatialCoordinates d))
        = (D.Ω : Set (SpatialCoordinates d)) := by
      have hΩiff : ∀ y : SpatialCoordinates d,
          y ∈ (D.Ω : Set (SpatialCoordinates d)) ↔
            coordinateReflection D.z {D.i} y ∈
              (D.reflected : Set (SpatialCoordinates d)) := by
        intro y
        rw [← D.preimage_reflected]
        rfl
      ext x
      rw [Set.mem_preimage, hΩiff, hΩiff, hcomm]
      constructor
      · intro h
        have hy : coordinateReflection D.z {D.i} x ∈
            coordinateReflection z' {j} ⁻¹'
              (D.reflected : Set (SpatialCoordinates d)) := h
        rwa [hB'] at hy
      · intro h
        have hy : coordinateReflection D.z {D.i} x ∈
            coordinateReflection z' {j} ⁻¹'
              (D.reflected : Set (SpatialCoordinates d)) := by rwa [hB']
        exact hy
    have hmpR : MeasurePreserving (coordinateReflection D.z {D.i})
        (volume.restrict (D.Ω : Set (SpatialCoordinates d)))
        (volume.restrict (D.reflected : Set (SpatialCoordinates d))) :=
      coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_reflected
    have hv₀odd : ∀ᵐ x ∂(volume.restrict (D.Ω : Set (SpatialCoordinates d))),
        ((v₀.1 : DomainL2 D.Ω) : SpatialCoordinates d → ℝ)
            (coordinateReflection z' {j} x)
          = -(((v₀.1 : DomainL2 D.Ω) : SpatialCoordinates d → ℝ) x) := by
      have hmpU : MeasurePreserving (coordinateReflection z' {j})
          (volume.restrict (D.Ω : Set (SpatialCoordinates d)))
          (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
        coordinateReflection_domain_measurePreserving z' {j} hOm'
      have hc := reflectionLp_coeFn D.z {D.i} D.preimage_reflected w.1
      have hcr := hmpU.quasiMeasurePreserving.ae hc
      have hoddi := hmpR.quasiMeasurePreserving.ae hodd
      filter_upwards [hc, hcr, hoddi] with x e1 e2 e3
      simp only [Function.comp_apply] at e1 e2 e3
      have e1' : ((v₀.1 : DomainL2 D.Ω) : SpatialCoordinates d → ℝ) x
          = ((w.1 : DomainL2 D.reflected) : SpatialCoordinates d → ℝ)
            (coordinateReflection D.z {D.i} x) := e1
      have e2' : ((v₀.1 : DomainL2 D.Ω) : SpatialCoordinates d → ℝ)
            (coordinateReflection z' {j} x)
          = ((w.1 : DomainL2 D.reflected) : SpatialCoordinates d → ℝ)
            (coordinateReflection D.z {D.i} (coordinateReflection z' {j} x)) := e2
      rw [e2', hcomm, e3, e1']
    have hXodd := D.oddExtension_ae_odd_other z' j hOm' hC' hcomm hv₀odd
    refine ae_odd_of_ae_eq z' {j} hC'
      (f := (((-X).1 : DomainL2 D.U) : SpatialCoordinates d → ℝ))
      (g := fun x => -((X.1 : SpatialCoordinates d → ℝ) x)) (Lp.coeFn_neg (X.1)) ?_
    filter_upwards [hXodd] with x hx
    simp only [hX] at hx ⊢
    rw [hx]
  · exact fun g hg hLg => ⟨fun x i => -(D.oddReflectedField
      (fun y j => coordinateReflectionSign {D.i} j *
        g (coordinateReflection D.z {D.i} y) j) x i),
      boundedField_neg
        (boundedField_oddReflectedField D (boundedField_pullback D hg)),
      divLoad_down D hg hCb hLg⟩

theorem fold_empty (z : SpatialCoordinates d) (P : Finset (Fin d))
    (y : SpatialCoordinates d) : coordinateFold z ∅ P y = y :=
  funext fun j => fold_apply_of_notMem_I (Finset.notMem_empty j) y

theorem foldedCoefficientP_empty (a : SpatialCoordinates d → ℝ)
    (z : SpatialCoordinates d) (P : Finset (Fin d)) :
    foldedCoefficientP a z ∅ P = a := by
  funext y
  rw [foldedCoefficientP, fold_empty]

/-! ## The single-reflection iteration over the active set -/

/-- Reflections in different coordinates commute. -/
theorem coordinateReflection_comm {i j : Fin d} (hij : i ≠ j)
    (z z' : SpatialCoordinates d) (x : SpatialCoordinates d) :
    coordinateReflection z {i} (coordinateReflection z' {j} x)
      = coordinateReflection z' {j} (coordinateReflection z {i} x) := by
  funext k
  by_cases hki : k = i
  · subst hki
    rw [coordinateReflection_single_apply_self,
      coordinateReflection_single_apply_of_ne _ hij,
      coordinateReflection_single_apply_of_ne _ hij,
      coordinateReflection_single_apply_self]
  · by_cases hkj : k = j
    · subst hkj
      rw [coordinateReflection_single_apply_of_ne _ hki,
        coordinateReflection_single_apply_self,
        coordinateReflection_single_apply_self,
        coordinateReflection_single_apply_of_ne _ hki]
    · rw [coordinateReflection_single_apply_of_ne _ hki,
        coordinateReflection_single_apply_of_ne _ hkj,
        coordinateReflection_single_apply_of_ne _ hkj,
        coordinateReflection_single_apply_of_ne _ hki]

/-- A box whose `i`-interval is symmetric about `x₀ i` is invariant under the
reflection about `x₀` in that coordinate. -/
theorem openBox_reflection_invariant {lo hi x₀ : SpatialCoordinates d}
    {i : Fin d} (hsym : lo i + hi i = 2 * x₀ i) :
    coordinateReflection x₀ {i} ⁻¹'
        (openBox lo hi : Set (SpatialCoordinates d))
      = (openBox lo hi : Set (SpatialCoordinates d)) := by
  ext y
  simp only [Set.mem_preimage, SetLike.mem_coe, mem_openBox_iff]
  constructor
  · intro h k
    by_cases hk : k = i
    · subst hk
      have hki := h k
      rw [coordinateReflection_single_apply_self] at hki
      constructor <;> linarith [hki.1, hki.2]
    · have hkk := h k
      rwa [coordinateReflection_single_apply_of_ne _ hk] at hkk
  · intro h k
    by_cases hk : k = i
    · subst hk
      have hki := h k
      rw [coordinateReflection_single_apply_self]
      constructor <;> linarith [hki.1, hki.2]
    · rw [coordinateReflection_single_apply_of_ne _ hk]
      exact h k

/-- **Doubling the box once per active coordinate, across the face that carries
`x₀`.**  Every reflection plane passes through `x₀`, so the composite even
extension of the coefficient is exactly the fold `a₀ ∘ coordinateFold x₀ J P`,
with `P` the active coordinates whose face is the box's UPPER face.  The datum
stays killed and keeps solving the forced equation, and `x₀` becomes interior in
every coordinate of `J`. -/
theorem exists_folded_box (lo hi x₀ : SpatialCoordinates d)
    (hlohi : ∀ j, lo j < hi j) (J : Finset (Fin d))
    (hJface : ∀ j ∈ J, x₀ j = lo j ∨ x₀ j = hi j)
    (a0 : SpatialCoordinates d → ℝ) (A₀ : PositiveCoefficient (openBox lo hi))
    (hA₀ : (A₀.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (openBox lo hi : Set (SpatialCoordinates d))] a0)
    {u : SobolevData (openBox lo hi)} (hu : u ∈ killedSobolevGraph (openBox lo hi))
    (L : SobolevData (openBox lo hi) → ℝ) (hL : SolvesOn A₀ u L) :
    ∃ (lo' hi' : SpatialCoordinates d) (P : Finset (Fin d))
      (A : PositiveCoefficient (openBox lo' hi')) (w : SobolevData (openBox lo' hi'))
      (L' : SobolevData (openBox lo' hi') → ℝ),
      P ⊆ J ∧
      w ∈ killedSobolevGraph (openBox lo' hi') ∧
      SolvesOn A w L' ∧
      ((A.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (openBox lo' hi' : Set (SpatialCoordinates d))]
          foldedCoefficientP a0 x₀ J P) ∧
      (∀ j, lo' j ≤ lo j ∧ hi j ≤ hi' j) ∧
      (∀ j ∈ J, lo' j < x₀ j ∧ x₀ j < hi' j) ∧
      (∀ j, j ∉ J → lo' j = lo j ∧ hi' j = hi j) ∧
      ((w.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (openBox lo hi : Set (SpatialCoordinates d))]
          (u.1 : SpatialCoordinates d → ℝ)) ∧
      (∀ i ∈ J, lo' i + hi' i = 2 * x₀ i) ∧
      (∀ i ∈ J, ∀ᵐ x ∂(volume.restrict
        (openBox lo' hi' : Set (SpatialCoordinates d))),
        (w.1 : SpatialCoordinates d → ℝ) (coordinateReflection x₀ {i} x)
          = -((w.1 : SpatialCoordinates d → ℝ) x)) ∧
      (∀ g : SpatialCoordinates d → SpatialCoordinates d,
        BoundedField g → IsDivLoad (U := openBox lo hi) L g →
        ∃ g' : SpatialCoordinates d → SpatialCoordinates d,
          BoundedField g' ∧
            IsDivLoad (U := openBox lo' hi') L' g') := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    refine ⟨lo, hi, ∅, A₀, u, L, Finset.Subset.refl _, hu, hL, ?_,
      fun j => ⟨le_rfl, le_rfl⟩, by simp, fun j _ => ⟨rfl, rfl⟩,
      Filter.EventuallyEq.refl _ _, by simp, by simp, fun g hg hLg => ⟨g, hg, hLg⟩⟩
    rw [foldedCoefficientP_empty]
    exact hA₀
  | @insert i J hiJ ih =>
    obtain ⟨lo₀, hi₀, P₀, A, w, L₀, hPJ, hw, hsolve, hfold, hmono, hint, heq, hae,
      hsymJ, hoddJ, hdivJ⟩ :=
      ih (fun j hj => hJface j (Finset.mem_insert_of_mem hj))
    have hlo₀hi₀ : ∀ j, lo₀ j < hi₀ j := fun j =>
      lt_of_le_of_lt (hmono j).1 (lt_of_lt_of_le (hlohi j) (hmono j).2)
    obtain ⟨hloi, hhii⟩ : lo₀ i = lo i ∧ hi₀ i = hi i := heq i hiJ
    have hbase : (openBox lo hi : Set (SpatialCoordinates d)) ⊆
        (openBox lo₀ hi₀ : Set (SpatialCoordinates d)) :=
      openBox_subset_openBox (fun j => (hmono j).1) (fun j => (hmono j).2)
    have hiP : i ∉ P₀ := fun h => hiJ (hPJ h)
    rcases hJface i (Finset.mem_insert_self i J) with hlow | hhigh
    · -- `x₀` lies on the lower `i`-face: reflect downward
      have hz : x₀ i = (boxEvenReflectionDomain (lowerDoubledCorner lo₀ hi₀ i)
          (Function.update hi₀ i (lo₀ i)) i).z i := by
        show x₀ i = upperFacePoint (lowerDoubledCorner lo₀ hi₀ i)
          (Function.update hi₀ i (lo₀ i)) i i
        rw [upperFacePoint_apply_self, Function.update_self, hloi, hlow]
      obtain ⟨A', w', L'', hw', hsolve', hae', hfold', hoddi, hother, hdiv'⟩ :=
        fold_step_down
          (boxEvenReflectionDomain (lowerDoubledCorner lo₀ hi₀ i)
            (Function.update hi₀ i (lo₀ i)) i)
          (boxEvenReflectionDomain_mirror_reflected lo₀ hi₀ i)
          (boxEvenReflectionDomain_mirror_U lo₀ hi₀ i)
          (isBounded_openBox _ _)
          hiJ hiP hz A hfold hw L₀ hsolve
      have hlower : ∀ j, lowerDoubledCorner lo₀ hi₀ i j ≤ lo₀ j := by
        intro j
        by_cases hj : j = i
        · subst hj
          rw [lowerDoubledCorner, Function.update_self]
          linarith [hlo₀hi₀ j]
        · rw [lowerDoubledCorner, Function.update_of_ne hj]
      refine ⟨lowerDoubledCorner lo₀ hi₀ i, hi₀, P₀, A', w', L'',
        Finset.Subset.trans hPJ (Finset.subset_insert i J), hw', hsolve', hfold',
        fun j => ⟨le_trans (hlower j) (hmono j).1, (hmono j).2⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with hjeq | hjJ
        · subst hjeq
          rw [lowerDoubledCorner, Function.update_self, hlow, ← hloi]
          constructor <;> linarith [hlo₀hi₀ j]
        · exact ⟨lt_of_le_of_lt (hlower j) (hint j hjJ).1, (hint j hjJ).2⟩
      · intro j hj
        have hji : j ≠ i := fun h => hj (Finset.mem_insert.mpr (Or.inl h))
        have hjJ : j ∉ J := fun h => hj (Finset.mem_insert.mpr (Or.inr h))
        rw [lowerDoubledCorner, Function.update_of_ne hji]
        exact heq j hjJ
      · exact Filter.EventuallyEq.trans
          (ae_restrict_of_ae_restrict_of_subset
            (μ := (volume : Measure (SpatialCoordinates d))) hbase hae') hae
      · intro j hj
        rcases Finset.mem_insert.mp hj with hjeq | hjJ
        · subst hjeq
          rw [lowerDoubledCorner, Function.update_self, hlow, ← hloi]
          ring
        · have hji : j ≠ i := by rintro rfl; exact hiJ hjJ
          rw [lowerDoubledCorner, Function.update_of_ne hji]
          exact hsymJ j hjJ
      · intro j hj
        rcases Finset.mem_insert.mp hj with hjeq | hjJ
        · subst hjeq
          rw [coordinateReflection_single_congr x₀ _ j hz]
          exact hoddi
        · have hji : j ≠ i := by rintro rfl; exact hiJ hjJ
          refine hother x₀ j (openBox_reflection_invariant (hsymJ j hjJ))
            (openBox_reflection_invariant ?_)
            (fun x => coordinateReflection_comm (Ne.symm hji) _ x₀ x)
            (hoddJ j hjJ)
          rw [lowerDoubledCorner, Function.update_of_ne hji]
          exact hsymJ j hjJ
      · intro g hg hLg
        obtain ⟨g₁, hg₁, hL₁⟩ := hdivJ g hg hLg
        exact hdiv' g₁ hg₁ hL₁
    · -- `x₀` lies on the upper `i`-face: reflect upward
      have hz : x₀ i = (boxEvenReflectionDomain lo₀ hi₀ i).z i := by
        show x₀ i = upperFacePoint lo₀ hi₀ i i
        rw [upperFacePoint_apply_self, hhii, hhigh]
      obtain ⟨A', w', L'', hw', hsolve', hae', hfold', hoddi, hother, hdiv'⟩ :=
        fold_step_up (boxEvenReflectionDomain lo₀ hi₀ i) rfl rfl
          (isBounded_openBox _ _) hiJ hz A hfold hw L₀ hsolve
      have hupper : ∀ j, hi₀ j ≤ doubledCorner lo₀ hi₀ i j := by
        intro j
        by_cases hj : j = i
        · subst hj
          rw [doubledCorner_apply_self]
          linarith [hlo₀hi₀ j]
        · rw [doubledCorner_apply_of_ne _ _ hj]
      refine ⟨lo₀, doubledCorner lo₀ hi₀ i, insert i P₀, A', w', L'',
        Finset.insert_subset_insert i hPJ, hw', hsolve', hfold',
        fun j => ⟨(hmono j).1, le_trans (hmono j).2 (hupper j)⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with hjeq | hjJ
        · subst hjeq
          rw [doubledCorner_apply_self, hhigh, ← hhii]
          constructor
          · linarith [hlo₀hi₀ j]
          · linarith [hlo₀hi₀ j]
        · exact ⟨(hint j hjJ).1, lt_of_lt_of_le (hint j hjJ).2 (hupper j)⟩
      · intro j hj
        have hji : j ≠ i := fun h => hj (Finset.mem_insert.mpr (Or.inl h))
        have hjJ : j ∉ J := fun h => hj (Finset.mem_insert.mpr (Or.inr h))
        rw [doubledCorner_apply_of_ne _ _ hji]
        exact heq j hjJ
      · exact Filter.EventuallyEq.trans
          (ae_restrict_of_ae_restrict_of_subset
            (μ := (volume : Measure (SpatialCoordinates d))) hbase hae') hae
      · intro j hj
        rcases Finset.mem_insert.mp hj with hjeq | hjJ
        · subst hjeq
          rw [doubledCorner_apply_self, hhigh, ← hhii]
          ring
        · have hji : j ≠ i := by rintro rfl; exact hiJ hjJ
          rw [doubledCorner_apply_of_ne _ _ hji]
          exact hsymJ j hjJ
      · intro j hj
        rcases Finset.mem_insert.mp hj with hjeq | hjJ
        · subst hjeq
          rw [coordinateReflection_single_congr x₀ _ j hz]
          exact hoddi
        · have hji : j ≠ i := by rintro rfl; exact hiJ hjJ
          refine hother x₀ j (openBox_reflection_invariant (hsymJ j hjJ))
            (openBox_reflection_invariant ?_)
            (fun x => coordinateReflection_comm (Ne.symm hji) _ x₀ x)
            (hoddJ j hjJ)
          rw [doubledCorner_apply_of_ne _ _ hji]
          exact hsymJ j hjJ
      · intro g hg hLg
        obtain ⟨g₁, hg₁, hL₁⟩ := hdivJ g hg hLg
        exact hdiv' g₁ hg₁ hL₁

/-- **The odd extension over the active set, with the coefficient identified as
a fold.**  All the active coordinates are doubled across the faces through `x₀`,
the last of them being `i₀`, so that the datum is odd about the plane
`{x_{i₀} = (x₀)_{i₀}}` and the coefficient on the doubled box is exactly
`a₀ ∘ coordinateFold x₀ (insert i₀ I) P`.  This is the pair of inputs GMC's
small-contrast Schauder estimate consumes: a genuine continuous coefficient
whose contrast at `x₀` is `1`, and a solution of the forced equation. -/
theorem exists_odd_folded_box (lo hi x₀ : SpatialCoordinates d)
    (hlohi : ∀ j, lo j < hi j)
    (I : Finset (Fin d)) (i₀ : Fin d) (hi₀I : i₀ ∉ I)
    (hIface : ∀ j ∈ I, x₀ j = lo j ∨ x₀ j = hi j)
    (hface₀ : x₀ i₀ = lo i₀ ∨ x₀ i₀ = hi i₀)
    (hinterior : ∀ j, j ∉ I → j ≠ i₀ → lo j < x₀ j ∧ x₀ j < hi j)
    (a0 : SpatialCoordinates d → ℝ) (A₀ : PositiveCoefficient (openBox lo hi))
    (hA₀ : (A₀.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (openBox lo hi : Set (SpatialCoordinates d))] a0)
    {u : SobolevData (openBox lo hi)} (hu : u ∈ killedSobolevGraph (openBox lo hi))
    (L : SobolevData (openBox lo hi) → ℝ) (hL : SolvesOn A₀ u L) :
    ∃ (lo' hi' : SpatialCoordinates d) (P : Finset (Fin d))
      (A : PositiveCoefficient (openBox lo' hi')) (w : SobolevData (openBox lo' hi'))
      (L' : SobolevData (openBox lo' hi') → ℝ),
      w ∈ killedSobolevGraph (openBox lo' hi') ∧
      SolvesOn A w L' ∧
      ((A.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (openBox lo' hi' : Set (SpatialCoordinates d))]
          foldedCoefficientP a0 x₀ (insert i₀ I) P) ∧
      x₀ ∈ (openBox lo' hi' : Set (SpatialCoordinates d)) ∧
      (openBox lo hi : Set (SpatialCoordinates d)) ⊆
        (openBox lo' hi' : Set (SpatialCoordinates d)) ∧
      Set.MapsTo (coordinateReflection x₀ {i₀})
        (openBox lo' hi' : Set (SpatialCoordinates d))
        (openBox lo' hi' : Set (SpatialCoordinates d)) ∧
      ((w.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (openBox lo hi : Set (SpatialCoordinates d))]
          (u.1 : SpatialCoordinates d → ℝ)) ∧
      (∀ᵐ x ∂(volume.restrict (openBox lo' hi' : Set (SpatialCoordinates d))),
        (w.1 : SpatialCoordinates d → ℝ) (coordinateReflection x₀ {i₀} x)
          = -((w.1 : SpatialCoordinates d → ℝ) x)) ∧
      (∀ i ∈ insert i₀ I, lo' i + hi' i = 2 * x₀ i) ∧
      (∀ i ∈ insert i₀ I, ∀ᵐ x ∂(volume.restrict
        (openBox lo' hi' : Set (SpatialCoordinates d))),
        (w.1 : SpatialCoordinates d → ℝ) (coordinateReflection x₀ {i} x)
          = -((w.1 : SpatialCoordinates d → ℝ) x)) ∧
      (∀ g : SpatialCoordinates d → SpatialCoordinates d,
        BoundedField g → IsDivLoad (U := openBox lo hi) L g →
        ∃ g' : SpatialCoordinates d → SpatialCoordinates d,
          BoundedField g' ∧
            IsDivLoad (U := openBox lo' hi') L' g') := by
  classical
  obtain ⟨lo₀, hi₀, P₀, A, w, L₀, hPJ, hw, hsolve, hfold, hmono, hint, heq, hae,
    hsymI, hoddI, hdivI⟩ :=
    exists_folded_box lo hi x₀ hlohi I hIface a0 A₀ hA₀ hu L hL
  have hlo₀hi₀ : ∀ j, lo₀ j < hi₀ j := fun j =>
    lt_of_le_of_lt (hmono j).1 (lt_of_lt_of_le (hlohi j) (hmono j).2)
  obtain ⟨hloi, hhii⟩ : lo₀ i₀ = lo i₀ ∧ hi₀ i₀ = hi i₀ := heq i₀ hi₀I
  have hiP : i₀ ∉ P₀ := fun h => hi₀I (hPJ h)
  have hbase : (openBox lo hi : Set (SpatialCoordinates d)) ⊆
      (openBox lo₀ hi₀ : Set (SpatialCoordinates d)) :=
    openBox_subset_openBox (fun j => (hmono j).1) (fun j => (hmono j).2)
  have hside : ∀ j, j ≠ i₀ → lo₀ j < x₀ j ∧ x₀ j < hi₀ j := by
    intro j hj
    by_cases hjI : j ∈ I
    · exact hint j hjI
    · obtain ⟨h1, h2⟩ := heq j hjI
      obtain ⟨h3, h4⟩ := hinterior j hjI hj
      exact ⟨h1 ▸ h3, h2 ▸ h4⟩
  rcases hface₀ with hlow | hhigh
  · have hz : x₀ i₀ = (boxEvenReflectionDomain (lowerDoubledCorner lo₀ hi₀ i₀)
        (Function.update hi₀ i₀ (lo₀ i₀)) i₀).z i₀ := by
      show x₀ i₀ = upperFacePoint (lowerDoubledCorner lo₀ hi₀ i₀)
        (Function.update hi₀ i₀ (lo₀ i₀)) i₀ i₀
      rw [upperFacePoint_apply_self, Function.update_self, hloi, hlow]
    obtain ⟨A', w', L'', hw', hsolve', hae', hfold', hodd', hother', hdiv'⟩ :=
      fold_step_down
        (boxEvenReflectionDomain (lowerDoubledCorner lo₀ hi₀ i₀)
          (Function.update hi₀ i₀ (lo₀ i₀)) i₀)
        (boxEvenReflectionDomain_mirror_reflected lo₀ hi₀ i₀)
        (boxEvenReflectionDomain_mirror_U lo₀ hi₀ i₀)
        (isBounded_openBox _ _)
        hi₀I hiP hz A hfold hw L₀ hsolve
    have hcong : coordinateReflection
        (boxEvenReflectionDomain (lowerDoubledCorner lo₀ hi₀ i₀)
          (Function.update hi₀ i₀ (lo₀ i₀)) i₀).z {i₀} =
        coordinateReflection x₀ {i₀} :=
      coordinateReflection_single_congr _ _ i₀ hz.symm
    have hlower : ∀ j, lowerDoubledCorner lo₀ hi₀ i₀ j ≤ lo₀ j := by
      intro j
      by_cases hj : j = i₀
      · subst hj
        rw [lowerDoubledCorner, Function.update_self]
        linarith [hlo₀hi₀ j]
      · rw [lowerDoubledCorner, Function.update_of_ne hj]
    refine ⟨lowerDoubledCorner lo₀ hi₀ i₀, hi₀, P₀, A', w', L'',
      hw', hsolve', hfold', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_openBox_iff]
      intro j
      by_cases hj : j = i₀
      · subst hj
        rw [lowerDoubledCorner, Function.update_self, hlow, ← hloi]
        constructor <;> linarith [hlo₀hi₀ j]
      · exact ⟨lt_of_le_of_lt (hlower j) (hside j hj).1, (hside j hj).2⟩
    · exact openBox_subset_openBox
        (fun j => le_trans (hlower j) (hmono j).1) (fun j => (hmono j).2)
    · intro x hx
      have hU := boxEvenReflectionDomain_mirror_U lo₀ hi₀ i₀
      have hxU : x ∈ (boxEvenReflectionDomain (lowerDoubledCorner lo₀ hi₀ i₀)
          (Function.update hi₀ i₀ (lo₀ i₀)) i₀).U := by rw [hU]; exact hx
      have hres := (EvenReflectionDomain.reflection_mem_U_iff
        (boxEvenReflectionDomain (lowerDoubledCorner lo₀ hi₀ i₀)
          (Function.update hi₀ i₀ (lo₀ i₀)) i₀) x).mpr hxU
      rw [hU] at hres
      rw [← hcong]
      exact hres
    · exact Filter.EventuallyEq.trans
        (ae_restrict_of_ae_restrict_of_subset
          (μ := (volume : Measure (SpatialCoordinates d))) hbase hae') hae
    · rw [← hcong]; exact hodd'
    · intro i hi
      rcases Finset.mem_insert.mp hi with hieq | hiI'
      · subst hieq
        rw [lowerDoubledCorner, Function.update_self, hlow, ← hloi]
        ring
      · have hne : i ≠ i₀ := by rintro rfl; exact hi₀I hiI'
        rw [lowerDoubledCorner, Function.update_of_ne hne]
        exact hsymI i hiI'
    · intro i hi
      rcases Finset.mem_insert.mp hi with hieq | hiI'
      · subst hieq
        rw [← hcong]; exact hodd'
      · have hne : i ≠ i₀ := by rintro rfl; exact hi₀I hiI'
        refine hother' x₀ i (openBox_reflection_invariant (hsymI i hiI'))
          (openBox_reflection_invariant ?_)
          (fun x => coordinateReflection_comm (Ne.symm hne) _ x₀ x)
          (hoddI i hiI')
        rw [lowerDoubledCorner, Function.update_of_ne hne]
        exact hsymI i hiI'
    · intro g hg hLg
      obtain ⟨g₁, hg₁, hL₁⟩ := hdivI g hg hLg
      exact hdiv' g₁ hg₁ hL₁
  · have hz : x₀ i₀ = (boxEvenReflectionDomain lo₀ hi₀ i₀).z i₀ := by
      show x₀ i₀ = upperFacePoint lo₀ hi₀ i₀ i₀
      rw [upperFacePoint_apply_self, hhii, hhigh]
    obtain ⟨A', w', L'', hw', hsolve', hae', hfold', hodd', hother', hdiv'⟩ :=
      fold_step_up (boxEvenReflectionDomain lo₀ hi₀ i₀) rfl rfl
        (isBounded_openBox _ _) hi₀I hz A hfold hw L₀ hsolve
    have hcong : coordinateReflection (boxEvenReflectionDomain lo₀ hi₀ i₀).z {i₀} =
        coordinateReflection x₀ {i₀} :=
      coordinateReflection_single_congr _ _ i₀ hz.symm
    have hupper : ∀ j, hi₀ j ≤ doubledCorner lo₀ hi₀ i₀ j := by
      intro j
      by_cases hj : j = i₀
      · subst hj
        rw [doubledCorner_apply_self]
        linarith [hlo₀hi₀ j]
      · rw [doubledCorner_apply_of_ne _ _ hj]
    refine ⟨lo₀, doubledCorner lo₀ hi₀ i₀, insert i₀ P₀, A', w', L'',
      hw', hsolve', hfold', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_openBox_iff]
      intro j
      by_cases hj : j = i₀
      · subst hj
        rw [doubledCorner_apply_self, hhigh, ← hhii]
        constructor <;> linarith [hlo₀hi₀ j]
      · exact ⟨(hside j hj).1, lt_of_lt_of_le (hside j hj).2 (hupper j)⟩
    · exact openBox_subset_openBox (fun j => (hmono j).1)
        (fun j => le_trans (hmono j).2 (hupper j))
    · intro x hx
      rw [← hcong]
      exact (EvenReflectionDomain.reflection_mem_U_iff
        (boxEvenReflectionDomain lo₀ hi₀ i₀) x).mpr hx
    · exact Filter.EventuallyEq.trans
        (ae_restrict_of_ae_restrict_of_subset
          (μ := (volume : Measure (SpatialCoordinates d))) hbase hae') hae
    · rw [← hcong]; exact hodd'
    · intro i hi
      rcases Finset.mem_insert.mp hi with hieq | hiI'
      · subst hieq
        rw [doubledCorner_apply_self, hhigh, ← hhii]
        ring
      · have hne : i ≠ i₀ := by rintro rfl; exact hi₀I hiI'
        rw [doubledCorner_apply_of_ne _ _ hne]
        exact hsymI i hiI'
    · intro i hi
      rcases Finset.mem_insert.mp hi with hieq | hiI'
      · subst hieq
        rw [← hcong]; exact hodd'
      · have hne : i ≠ i₀ := by rintro rfl; exact hi₀I hiI'
        refine hother' x₀ i (openBox_reflection_invariant (hsymI i hiI'))
          (openBox_reflection_invariant ?_)
          (fun x => coordinateReflection_comm (Ne.symm hne) _ x₀ x)
          (hoddI i hiI')
        rw [doubledCorner_apply_of_ne _ _ hne]
        exact hsymI i hiI'
    · intro g hg hLg
      obtain ⟨g₁, hg₁, hL₁⟩ := hdivI g hg hLg
      exact hdiv' g₁ hg₁ hL₁

/-- **Divergence-form loads survive one odd-extension step.**  If `u` solves the
forced equation on the lower half with the divergence-form load `-∫ g·∇v`, then
its odd extension solves the forced equation on the doubled domain with the
divergence-form load of the ODD REFLECTION of `g`. -/
theorem divLoad_transport (D : EvenReflectionDomain d)
    (a : PositiveCoefficient D.Ω)
    (g : SpatialCoordinates d → SpatialCoordinates d)
    (hg : ∀ i : Fin d, MemLp (fun x => g x i) 2
      (volume.restrict (D.U : Set (SpatialCoordinates d))))
    {u : SobolevData D.Ω}
    (hL : SolvesOn a u (fun v => -∫ x in (D.Ω : Set (SpatialCoordinates d)),
      ∑ i : Fin d, g x i * ((v.2 i : DomainL2 D.Ω) : SpatialCoordinates d → ℝ) x)) :
    SolvesOn (D.evenExtensionCoefficient a) (D.oddExtension u)
      (fun ψ => -∫ x in (D.U : Set (SpatialCoordinates d)),
        ∑ i : Fin d, D.oddReflectedField g x i *
          ((ψ.2 i : DomainL2 D.U) : SpatialCoordinates d → ℝ) x) := by
  intro ψ hψ
  rw [D.oddExtension_killed_equation a _ hL hψ]
  have hlin : ∀ (A B : SobolevData D.Ω),
      (∫ x in (D.Ω : Set (SpatialCoordinates d)),
        ∑ i : Fin d, g x i * (((A - B).2 i : DomainL2 D.Ω) :
          SpatialCoordinates d → ℝ) x)
      = (∫ x in (D.Ω : Set (SpatialCoordinates d)),
          ∑ i : Fin d, g x i * ((A.2 i : DomainL2 D.Ω) :
            SpatialCoordinates d → ℝ) x)
        - (∫ x in (D.Ω : Set (SpatialCoordinates d)),
          ∑ i : Fin d, g x i * ((B.2 i : DomainL2 D.Ω) :
            SpatialCoordinates d → ℝ) x) := by
    intro A B
    have hgΩ : ∀ i : Fin d, MemLp (fun x => g x i) 2
        (volume.restrict (D.Ω : Set (SpatialCoordinates d))) := fun i =>
      (hg i).mono_measure (Measure.restrict_mono D.Ω_le le_rfl)
    have hIA : ∀ i : Fin d, IntegrableOn
        (fun x => g x i * ((A.2 i : DomainL2 D.Ω) :
          SpatialCoordinates d → ℝ) x)
        (D.Ω : Set (SpatialCoordinates d)) volume := fun i =>
      (hgΩ i).integrable_mul (Lp.memLp (A.2 i))
    have hIB : ∀ i : Fin d, IntegrableOn
        (fun x => g x i * ((B.2 i : DomainL2 D.Ω) :
          SpatialCoordinates d → ℝ) x)
        (D.Ω : Set (SpatialCoordinates d)) volume := fun i =>
      (hgΩ i).integrable_mul (Lp.memLp (B.2 i))
    have hAB : (∫ x in (D.Ω : Set (SpatialCoordinates d)),
        ∑ i : Fin d, g x i * (((A - B).2 i : DomainL2 D.Ω) :
          SpatialCoordinates d → ℝ) x)
        = ∫ x in (D.Ω : Set (SpatialCoordinates d)),
          (∑ i : Fin d, g x i * ((A.2 i : DomainL2 D.Ω) :
            SpatialCoordinates d → ℝ) x
            - ∑ i : Fin d, g x i * ((B.2 i : DomainL2 D.Ω) :
              SpatialCoordinates d → ℝ) x) := by
      refine integral_congr_ae ?_
      have hall : ∀ᵐ x ∂(volume.restrict (D.Ω : Set (SpatialCoordinates d))),
          ∀ i : Fin d, (((A - B).2 i : DomainL2 D.Ω) :
            SpatialCoordinates d → ℝ) x
            = ((A.2 i : DomainL2 D.Ω) : SpatialCoordinates d → ℝ) x
              - ((B.2 i : DomainL2 D.Ω) : SpatialCoordinates d → ℝ) x :=
        ae_all_iff.2 (fun i => by
          filter_upwards [Lp.coeFn_sub (A.2 i) (B.2 i)] with x hx
          exact hx)
      filter_upwards [hall] with x hx
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by rw [hx i]; ring)
    rw [hAB]
    exact integral_sub (integrable_finsetSum _ (fun i _ => hIA i))
      (integrable_finsetSum _ (fun i _ => hIB i))
  rw [hlin]
  have hgΩ : ∀ i : Fin d, MemLp (fun x => g x i) 2
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) := fun i =>
    (hg i).mono_measure (Measure.restrict_mono D.Ω_le le_rfl)
  have hA : ∀ i : Fin d, IntegrableOn
      (fun x => g x i * ((sobolevDataRestrict D.Ω_le ψ).2 i) x)
      (D.Ω : Set (SpatialCoordinates d)) volume := fun i =>
    (hgΩ i).integrable_mul (Lp.memLp ((sobolevDataRestrict D.Ω_le ψ).2 i))
  have hB : ∀ i : Fin d, IntegrableOn
      (fun x => g x i * ((D.reflectedRestrict ψ).2 i) x)
      (D.Ω : Set (SpatialCoordinates d)) volume := fun i =>
    (hgΩ i).integrable_mul (Lp.memLp ((D.reflectedRestrict ψ).2 i))
  have hC : ∀ i : Fin d, IntegrableOn
      (fun x => D.oddReflectedField g x i * (ψ.2 i) x)
      (D.U : Set (SpatialCoordinates d)) volume := fun i =>
    oddReflectedField_integrableOn D g i (hg i) ψ
  have hsumA : (∫ x in (D.Ω : Set (SpatialCoordinates d)),
      ∑ i : Fin d, g x i * ((sobolevDataRestrict D.Ω_le ψ).2 i) x) =
      ∑ i : Fin d, ∫ x in (D.Ω : Set (SpatialCoordinates d)),
        g x i * ((sobolevDataRestrict D.Ω_le ψ).2 i) x :=
    integral_finsetSum _ (fun i _ => hA i)
  have hsumB : (∫ x in (D.Ω : Set (SpatialCoordinates d)),
      ∑ i : Fin d, g x i * ((D.reflectedRestrict ψ).2 i) x) =
      ∑ i : Fin d, ∫ x in (D.Ω : Set (SpatialCoordinates d)),
        g x i * ((D.reflectedRestrict ψ).2 i) x :=
    integral_finsetSum _ (fun i _ => hB i)
  have hsumC : (∫ x in (D.U : Set (SpatialCoordinates d)),
      ∑ i : Fin d, D.oddReflectedField g x i * (ψ.2 i) x) =
      ∑ i : Fin d, ∫ x in (D.U : Set (SpatialCoordinates d)),
        D.oddReflectedField g x i * (ψ.2 i) x :=
    integral_finsetSum _ (fun i _ => hC i)
  have key : (∑ i : Fin d, ∫ x in (D.Ω : Set (SpatialCoordinates d)),
        g x i * ((sobolevDataRestrict D.Ω_le ψ).2 i) x) -
      (∑ i : Fin d, ∫ x in (D.Ω : Set (SpatialCoordinates d)),
        g x i * ((D.reflectedRestrict ψ).2 i) x) =
      ∑ i : Fin d, ∫ x in (D.U : Set (SpatialCoordinates d)),
        D.oddReflectedField g x i * (ψ.2 i) x := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => divLoad_component D g i (hg i) ψ)
  simp only
  rw [hsumA, hsumB, hsumC]
  linarith [key]

/-! ## The coefficient-free multi-face odd extension -/

/-- The constant coefficient `1`, used to run the reflection iteration when only
the datum matters. -/
def oneCoefficient (U : Opens (SpatialCoordinates d)) :
    PositiveCoefficient U :=
  ⟨(memLp_top_const (1 : ℝ)).toLp _, 1 / 2, by norm_num, by
    filter_upwards [MemLp.coeFn_toLp (memLp_top_const (1 : ℝ))
      (μ := volume.restrict (U : Set (SpatialCoordinates d)))] with x hx
    rw [hx]
    norm_num⟩

/-- **The odd extension over the active set, odd about EVERY active face.**
Each active coordinate is doubled once, across the face that carries `x₀`, so
every reflection plane passes through `x₀`; the resulting datum is killed on an
open box containing `x₀` in its interior, agrees with the original datum on the
original box, and is almost everywhere odd under the reflection in each active
coordinate, the box being invariant under each. -/
theorem exists_multiOdd_box (lo hi x₀ : SpatialCoordinates d)
    (hlohi : ∀ j, lo j < hi j)
    (I : Finset (Fin d)) (i₀ : Fin d) (hi₀I : i₀ ∈ I)
    (hIface : ∀ i ∈ I, x₀ i = lo i ∨ x₀ i = hi i)
    (hIo : ∀ j, j ∉ I → lo j < x₀ j ∧ x₀ j < hi j)
    {u : SobolevData (openBox lo hi)} (hu : u ∈ killedSobolevGraph (openBox lo hi)) :
    ∃ (lo' hi' : SpatialCoordinates d) (w : SobolevData (openBox lo' hi')),
      (∀ j, lo' j < hi' j) ∧
      w ∈ killedSobolevGraph (openBox lo' hi') ∧
      x₀ ∈ (openBox lo' hi' : Set (SpatialCoordinates d)) ∧
      (openBox lo hi : Set (SpatialCoordinates d)) ⊆
        (openBox lo' hi' : Set (SpatialCoordinates d)) ∧
      (∀ i ∈ I, Set.MapsTo (coordinateReflection x₀ {i})
        (openBox lo' hi' : Set (SpatialCoordinates d))
        (openBox lo' hi' : Set (SpatialCoordinates d))) ∧
      ((w.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (openBox lo hi : Set (SpatialCoordinates d))]
          (u.1 : SpatialCoordinates d → ℝ)) ∧
      (∀ i ∈ I, ∀ᵐ x ∂(volume.restrict
        (openBox lo' hi' : Set (SpatialCoordinates d))),
        (w.1 : SpatialCoordinates d → ℝ) (coordinateReflection x₀ {i} x)
          = -((w.1 : SpatialCoordinates d → ℝ) x)) ∧
      (∀ v : SpatialCoordinates d → ℝ,
        ContinuousOn v (openBox lo' hi' : Set (SpatialCoordinates d)) →
        (v =ᵐ[volume.restrict (openBox lo' hi' : Set (SpatialCoordinates d))]
          (w.1 : SpatialCoordinates d → ℝ)) → v x₀ = 0) := by
  classical
  obtain ⟨lo', hi', P, A, w, L', hw, hsolve, hfold, hmem, hsub, hmaps, hae,
    hodd, hsym, hoddAll, -⟩ :=
    exists_odd_folded_box lo hi x₀ hlohi (I.erase i₀) i₀
      (Finset.notMem_erase i₀ I)
      (fun j hj => hIface j (Finset.mem_of_mem_erase hj))
      (hIface i₀ hi₀I)
      (fun j hj hji => hIo j (fun hjI => hj (Finset.mem_erase.mpr ⟨hji, hjI⟩)))
      (fun _ => (1 : ℝ)) (oneCoefficient (openBox lo hi))
      (MemLp.coeFn_toLp (memLp_top_const (1 : ℝ))
        (μ := volume.restrict (openBox lo hi : Set (SpatialCoordinates d)))) hu
      (fun v => sobolevCoefficientForm (oneCoefficient (openBox lo hi)) u v)
      (fun _ _ => rfl)
  have hIeq : insert i₀ (I.erase i₀) = I := Finset.insert_erase hi₀I
  rw [hIeq] at hsym hoddAll
  refine ⟨lo', hi', w, ?_, hw, hmem, hsub, ?_, hae, hoddAll, ?_⟩
  · intro j
    have hx : x₀ ∈ openBox lo' hi' := hmem
    rw [mem_openBox_iff] at hx
    exact lt_trans (hx j).1 (hx j).2
  · intro i hi x hx
    have hinv := openBox_reflection_invariant (hsym i hi)
    have : x ∈ coordinateReflection x₀ {i} ⁻¹'
        (openBox lo' hi' : Set (SpatialCoordinates d)) := by
      rw [hinv]; exact hx
    exact this
  · intro v hvcont hvae
    have hinv := openBox_reflection_invariant (hsym i₀ hi₀I)
    have hmaps' : Set.MapsTo (coordinateReflection x₀ {i₀})
        (openBox lo' hi' : Set (SpatialCoordinates d))
        (openBox lo' hi' : Set (SpatialCoordinates d)) := by
      intro x hx
      have hx' : x ∈ coordinateReflection x₀ {i₀} ⁻¹'
          (openBox lo' hi' : Set (SpatialCoordinates d)) := by
        rw [hinv]; exact hx
      exact hx'
    exact eq_zero_of_ae_odd_of_continuousOn (openBox lo' hi').isOpen x₀
      {i₀} hmaps' hvcont
      (ae_odd_of_ae_eq (S := openBox lo' hi') x₀ {i₀} hinv hvae
        (hoddAll i₀ hi₀I)) hmem
      (coordinateReflection_single_eq_self x₀ i₀ rfl)

end SubdiffusiveProcess
