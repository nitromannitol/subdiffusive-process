module

public import SubdiffusiveProcess.VariationalResponses.BoxReflection

@[expose] public section

/-!
# Oddness and the iterated doubling of a box

The boundary-continuity argument for a mesh cell reflects the killed datum
`u - φ` across the faces of the cell that contain the boundary point `x₀`.
`SubdiffusiveProcess.VariationalResponses.OddExtension` supplies the single-face step; this
file supplies the two facts about that step which the iteration needs:

* `lane2_oddExtension_ae_odd` -- the odd extension really is odd, almost
  everywhere on the doubled domain, so that `lane2_eq_zero_on_activeFaces`
  applies to a continuous representative of it;
* `lane2_oddExtension_ae_eq_on_Omega` -- the odd extension has not changed the
  datum on the original domain, so the final continuous representative still
  represents `u - φ` there.
-/

open MeasureTheory Set TopologicalSpace

noncomputable section

namespace SubdiffusiveProcess

variable {d : ℕ}

namespace EvenReflectionDomain

variable (D : EvenReflectionDomain d)

/-- **The odd extension is odd.**  On the doubled domain the extension of `u`
satisfies `w (ρ x) = - w x` almost everywhere, where `ρ` is the reflection in
the plane.  The proof transports the explicit indicator description of the
extension through the measure-preserving reflection and then checks the
identity pointwise on the two halves. -/
theorem lane2_oddExtension_ae_odd (u : SobolevData D.Ω) :
    ∀ᵐ x ∂(volume.restrict (D.U : Set (SpatialCoordinates d))),
      ((D.oddExtension u).1 : SpatialCoordinates d → ℝ)
          (coordinateReflection D.z {D.i} x)
        = -((D.oddExtension u).1 : SpatialCoordinates d → ℝ) x := by
  have hm : MeasurePreserving (coordinateReflection D.z {D.i})
      (volume.restrict (D.U : Set (SpatialCoordinates d)))
      (volume.restrict (D.U : Set (SpatialCoordinates d))) :=
    coordinateReflection_domain_measurePreserving D.z {D.i} D.symm
  have hfg := D.lane2_oddExtension_fst_coeFn u
  have hfgρ := hm.quasiMeasurePreserving.ae hfg
  filter_upwards [hfg, hfgρ] with x hx hxρ
  rw [hx, hxρ]
  have hinv : coordinateReflection D.z {D.i} (coordinateReflection D.z {D.i} x) = x :=
    coordinateReflection_involutive D.z {D.i} x
  have hΩ : coordinateReflection D.z {D.i} x ∈ (D.Ω : Set (SpatialCoordinates d))
      ↔ x ∈ (D.reflected : Set (SpatialCoordinates d)) := by
    rw [← D.preimage_Ω]; rfl
  have hR : coordinateReflection D.z {D.i} x ∈ (D.reflected : Set (SpatialCoordinates d))
      ↔ x ∈ (D.Ω : Set (SpatialCoordinates d)) := by
    rw [← D.preimage_reflected]; rfl
  by_cases hxΩ : x ∈ (D.Ω : Set (SpatialCoordinates d))
  · have hxR : x ∉ (D.reflected : Set (SpatialCoordinates d)) := fun h =>
      (Set.disjoint_left.mp D.disjoint_Ω_reflected hxΩ) h
    rw [Set.indicator_of_notMem (by simpa [hΩ] using hxR),
      Set.indicator_of_mem (by simpa [hR] using hxΩ),
      Set.indicator_of_mem hxΩ, Set.indicator_of_notMem hxR]
    simp [Function.comp, hinv]
  · by_cases hxR : x ∈ (D.reflected : Set (SpatialCoordinates d))
    · rw [Set.indicator_of_mem (by simpa [hΩ] using hxR),
        Set.indicator_of_notMem (by simpa [hR] using hxΩ),
        Set.indicator_of_notMem hxΩ, Set.indicator_of_mem hxR]
      simp [Function.comp]
    · rw [Set.indicator_of_notMem (by simpa [hΩ] using hxR),
        Set.indicator_of_notMem (by simpa [hR] using hxΩ),
        Set.indicator_of_notMem hxΩ, Set.indicator_of_notMem hxR]
      simp

/-- **Oddness about another plane survives the reflection.**  If the datum is
odd about a plane `P_j` transverse to the reflection plane, and both halves and
the doubled domain are `P_j`-invariant, then so is the odd extension.  This is
what makes the multi-face construction odd about EVERY active face, not just
the last one: the reflections commute, so an earlier oddness is carried through
each later doubling. -/
theorem lane2_oddExtension_ae_odd_other (z' : SpatialCoordinates d) (j : Fin d)
    (hOm : coordinateReflection z' {j} ⁻¹' (D.Ω : Set (SpatialCoordinates d))
      = (D.Ω : Set (SpatialCoordinates d)))
    (hUU : coordinateReflection z' {j} ⁻¹' (D.U : Set (SpatialCoordinates d))
      = (D.U : Set (SpatialCoordinates d)))
    (hcomm : ∀ x : SpatialCoordinates d,
      coordinateReflection D.z {D.i} (coordinateReflection z' {j} x)
        = coordinateReflection z' {j} (coordinateReflection D.z {D.i} x))
    {u : SobolevData D.Ω}
    (hodd : ∀ᵐ x ∂(volume.restrict (D.Ω : Set (SpatialCoordinates d))),
      ((u.1 : DomainL2 D.Ω) : SpatialCoordinates d → ℝ)
          (coordinateReflection z' {j} x)
        = -(((u.1 : DomainL2 D.Ω) : SpatialCoordinates d → ℝ) x)) :
    ∀ᵐ x ∂(volume.restrict (D.U : Set (SpatialCoordinates d))),
      ((D.oddExtension u).1 : SpatialCoordinates d → ℝ)
          (coordinateReflection z' {j} x)
        = -(((D.oddExtension u).1 : SpatialCoordinates d → ℝ) x) := by
  have hiff : ∀ (S : Set (SpatialCoordinates d)),
      coordinateReflection z' {j} ⁻¹' S = S →
      ∀ y : SpatialCoordinates d, coordinateReflection z' {j} y ∈ S ↔ y ∈ S := by
    intro S hS y
    constructor
    · intro h
      have hy : y ∈ coordinateReflection z' {j} ⁻¹' S := h
      rwa [hS] at hy
    · intro h
      have hy : y ∈ coordinateReflection z' {j} ⁻¹' S := by rwa [hS]
      exact hy
  have hRefl : coordinateReflection z' {j} ⁻¹'
      (D.reflected : Set (SpatialCoordinates d))
      = (D.reflected : Set (SpatialCoordinates d)) := by
    ext x
    simp only [Set.mem_preimage]
    show coordinateReflection D.z {D.i} (coordinateReflection z' {j} x) ∈
      (D.Ω : Set (SpatialCoordinates d)) ↔
      coordinateReflection D.z {D.i} x ∈ (D.Ω : Set (SpatialCoordinates d))
    rw [hcomm]
    exact hiff _ hOm _
  have hmpU : MeasurePreserving (coordinateReflection z' {j})
      (volume.restrict (D.U : Set (SpatialCoordinates d)))
      (volume.restrict (D.U : Set (SpatialCoordinates d))) :=
    coordinateReflection_domain_measurePreserving z' {j} hUU
  have hmpi : MeasurePreserving (coordinateReflection D.z {D.i})
      (volume.restrict (D.reflected : Set (SpatialCoordinates d)))
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
    coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_Ω
  have hfg := D.lane2_oddExtension_fst_coeFn u
  have hfgr := hmpU.quasiMeasurePreserving.ae hfg
  have hoddOm := ae_restrict_of_ae (s := (D.U : Set (SpatialCoordinates d)))
    ((ae_restrict_iff' D.Ω.isOpen.measurableSet).mp hodd)
  have hoddR := ae_restrict_of_ae (s := (D.U : Set (SpatialCoordinates d)))
    ((ae_restrict_iff' D.reflected.isOpen.measurableSet).mp
      (hmpi.quasiMeasurePreserving.ae hodd))
  filter_upwards [hfg, hfgr, hoddOm, hoddR] with x e1 e2 e3 e4
  rw [e1, e2]
  have hmemOm := hiff _ hOm x
  have hmemR := hiff _ hRefl x
  by_cases hxOm : x ∈ (D.Ω : Set (SpatialCoordinates d))
  · have hxR : x ∉ (D.reflected : Set (SpatialCoordinates d)) :=
      D.notMem_reflected_of_mem_Ω hxOm
    rw [Set.indicator_of_mem (hmemOm.mpr hxOm),
      Set.indicator_of_notMem (fun h => hxR (hmemR.mp h)),
      Set.indicator_of_mem hxOm, Set.indicator_of_notMem hxR]
    rw [sub_zero, sub_zero, e3 hxOm]
  · by_cases hxR : x ∈ (D.reflected : Set (SpatialCoordinates d))
    · have hxOm' : coordinateReflection z' {j} x ∉
          (D.Ω : Set (SpatialCoordinates d)) := fun h => hxOm (hmemOm.mp h)
      rw [Set.indicator_of_notMem hxOm', Set.indicator_of_mem (hmemR.mpr hxR),
        Set.indicator_of_notMem hxOm, Set.indicator_of_mem hxR]
      rw [zero_sub, zero_sub, neg_inj]
      simp only [Function.comp_apply]
      rw [hcomm, e4 hxR]
    · have hxOm' : coordinateReflection z' {j} x ∉
          (D.Ω : Set (SpatialCoordinates d)) := fun h => hxOm (hmemOm.mp h)
      have hxR' : coordinateReflection z' {j} x ∉
          (D.reflected : Set (SpatialCoordinates d)) := fun h => hxR (hmemR.mp h)
      rw [Set.indicator_of_notMem hxOm', Set.indicator_of_notMem hxR',
        Set.indicator_of_notMem hxOm, Set.indicator_of_notMem hxR]
      simp

/-- **The odd extension does not disturb the original datum.**  On the lower
half the extension agrees almost everywhere with `u`. -/
theorem lane2_oddExtension_ae_eq_on_Omega (u : SobolevData D.Ω) :
    ((D.oddExtension u).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (D.Ω : Set (SpatialCoordinates d))]
        (u.1 : SpatialCoordinates d → ℝ) := by
  have hsub := ae_restrict_of_ae_restrict_of_subset
    (μ := (volume : Measure (SpatialCoordinates d)))
    (s := (D.Ω : Set (SpatialCoordinates d)))
    (t := (D.U : Set (SpatialCoordinates d))) D.Ω_le
    (D.lane2_oddExtension_fst_coeFn u)
  have hmem : ∀ᵐ x ∂(volume.restrict (D.Ω : Set (SpatialCoordinates d))),
      x ∈ (D.Ω : Set (SpatialCoordinates d)) :=
    ae_restrict_mem D.Ω.isOpen.measurableSet
  filter_upwards [hsub, hmem] with x hx hxΩ
  have hxR : x ∉ (D.reflected : Set (SpatialCoordinates d)) := fun h =>
    (Set.disjoint_left.mp D.disjoint_Ω_reflected hxΩ) h
  rw [hx, Set.indicator_of_mem hxΩ, Set.indicator_of_notMem hxR, sub_zero]

/-- **On the upper half the odd extension of a pullback is the negated datum.**
This is the downward step seen from the original box: doubling a box downward
across its lower face reproduces `-w` there, not `w`. -/
theorem lane2_oddExtension_reflected_ae_eq_neg (v : SobolevData D.reflected) :
    ((D.oddExtension (reflectionSobolevData D.z {D.i} D.preimage_reflected v)).1 :
        SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (D.reflected : Set (SpatialCoordinates d))]
        fun x => -((v.1 : SpatialCoordinates d → ℝ) x) := by
  have h1 := ae_restrict_of_ae_restrict_of_subset
    (μ := (volume : Measure (SpatialCoordinates d)))
    (s := (D.reflected : Set (SpatialCoordinates d)))
    (t := (D.U : Set (SpatialCoordinates d))) D.reflected_le
    (D.lane2_oddExtension_fst_coeFn
      (reflectionSobolevData D.z {D.i} D.preimage_reflected v))
  have hmem : ∀ᵐ x ∂(volume.restrict (D.reflected : Set (SpatialCoordinates d))),
      x ∈ (D.reflected : Set (SpatialCoordinates d)) :=
    ae_restrict_mem D.reflected.isOpen.measurableSet
  have hmR : MeasurePreserving (coordinateReflection D.z {D.i})
      (volume.restrict (D.reflected : Set (SpatialCoordinates d)))
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
    coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_Ω
  have h2 := hmR.quasiMeasurePreserving.ae
    (reflectionLp_coeFn D.z {D.i} D.preimage_reflected v.1)
  filter_upwards [h1, hmem, h2] with x hx hxR hx2
  have hxΩ : x ∉ (D.Ω : Set (SpatialCoordinates d)) := fun h =>
    (Set.disjoint_left.mp D.disjoint_Ω_reflected h) hxR
  rw [hx, Set.indicator_of_notMem hxΩ, Set.indicator_of_mem hxR, zero_sub]
  have hinv : coordinateReflection D.z {D.i} (coordinateReflection D.z {D.i} x) = x :=
    coordinateReflection_involutive D.z {D.i} x
  simp only [Function.comp_apply] at hx2 ⊢
  have hfst : ((reflectionSobolevData D.z {D.i} D.preimage_reflected v).1 :
      DomainL2 D.Ω) = reflectionLp D.z {D.i} D.preimage_reflected v.1 := rfl
  rw [hfst, hx2, hinv]

end EvenReflectionDomain

/-- Almost-everywhere oddness transfers along an almost-everywhere equality on a
reflection-invariant open set. -/
theorem lane2_ae_odd_of_ae_eq (z : SpatialCoordinates d) (I : Finset (Fin d))
    {S : Opens (SpatialCoordinates d)}
    (hS : coordinateReflection z I ⁻¹' (S : Set (SpatialCoordinates d)) =
      (S : Set (SpatialCoordinates d)))
    {f g : SpatialCoordinates d → ℝ}
    (hfg : f =ᵐ[volume.restrict (S : Set (SpatialCoordinates d))] g)
    (hg : ∀ᵐ x ∂(volume.restrict (S : Set (SpatialCoordinates d))),
      g (coordinateReflection z I x) = -g x) :
    ∀ᵐ x ∂(volume.restrict (S : Set (SpatialCoordinates d))),
      f (coordinateReflection z I x) = -f x := by
  have hm : MeasurePreserving (coordinateReflection z I)
      (volume.restrict (S : Set (SpatialCoordinates d)))
      (volume.restrict (S : Set (SpatialCoordinates d))) :=
    coordinateReflection_domain_measurePreserving z I hS
  have hfgρ := hm.quasiMeasurePreserving.ae hfg
  filter_upwards [hfg, hfgρ, hg] with x hx hxρ hxg
  rw [hxρ, hx, hxg]

/-- **The upward doubling step.**  A killed datum on `B = D.Ω` extends to a
killed datum on `C = D.U` that agrees with it on `B` and is odd about the
reflection plane. -/
theorem lane2_reflect_step_up (D : EvenReflectionDomain d)
    {B C : Opens (SpatialCoordinates d)} (hB : D.Ω = B) (hC : D.U = C)
    {w : SobolevData B} (hw : w ∈ killedSobolevGraph B) :
    ∃ v : SobolevData C, v ∈ killedSobolevGraph C ∧
      ((v.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (B : Set (SpatialCoordinates d))]
          (w.1 : SpatialCoordinates d → ℝ)) ∧
      (∀ᵐ x ∂(volume.restrict (C : Set (SpatialCoordinates d))),
        (v.1 : SpatialCoordinates d → ℝ) (coordinateReflection D.z {D.i} x)
          = -((v.1 : SpatialCoordinates d → ℝ) x)) := by
  subst hB
  subst hC
  exact ⟨D.oddExtension w, EvenReflectionDomain.lane2_oddExtension_mem_killed D hw,
    D.lane2_oddExtension_ae_eq_on_Omega w, D.lane2_oddExtension_ae_odd w⟩

/-- **The downward doubling step.**  A killed datum on `B = D.reflected` extends
to a killed datum on `C = D.U` that agrees with it on `B` and is odd about the
reflection plane.  The sign is fixed by taking the negative of the odd extension
of the pullback, which is again killed. -/
theorem lane2_reflect_step_down (D : EvenReflectionDomain d)
    {B C : Opens (SpatialCoordinates d)} (hB : D.reflected = B) (hC : D.U = C)
    {w : SobolevData B} (hw : w ∈ killedSobolevGraph B) :
    ∃ v : SobolevData C, v ∈ killedSobolevGraph C ∧
      ((v.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (B : Set (SpatialCoordinates d))]
          (w.1 : SpatialCoordinates d → ℝ)) ∧
      (∀ᵐ x ∂(volume.restrict (C : Set (SpatialCoordinates d))),
        (v.1 : SpatialCoordinates d → ℝ) (coordinateReflection D.z {D.i} x)
          = -((v.1 : SpatialCoordinates d → ℝ) x)) := by
  subst hB
  subst hC
  set X := D.oddExtension (reflectionSobolevData D.z {D.i} D.preimage_reflected w) with hX
  refine ⟨-X, neg_mem (lane2_oddExtension_reflected_mem_killed D hw), ?_, ?_⟩
  · have hneg : (((-X).1 : DomainL2 D.U) : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (D.U : Set (SpatialCoordinates d))]
          fun x => -((X.1 : SpatialCoordinates d → ℝ) x) := by
      have := Lp.coeFn_neg (X.1)
      exact this
    have hneg' := ae_restrict_of_ae_restrict_of_subset
      (μ := (volume : Measure (SpatialCoordinates d)))
      (s := (D.reflected : Set (SpatialCoordinates d)))
      (t := (D.U : Set (SpatialCoordinates d))) D.reflected_le hneg
    filter_upwards [hneg', D.lane2_oddExtension_reflected_ae_eq_neg w] with x h1 h2
    rw [h1, h2, neg_neg]
  · refine lane2_ae_odd_of_ae_eq D.z {D.i} D.symm
      (f := (((-X).1 : DomainL2 D.U) : SpatialCoordinates d → ℝ))
      (g := fun x => -((X.1 : SpatialCoordinates d → ℝ) x)) (Lp.coeFn_neg (X.1)) ?_
    filter_upwards [D.lane2_oddExtension_ae_odd
      (reflectionSobolevData D.z {D.i} D.preimage_reflected w)] with x hx
    simp only [hX] at hx ⊢
    rw [hx]

/-- Monotonicity of boxes in their corners. -/
theorem openBox_subset_openBox {lo hi lo' hi' : SpatialCoordinates d}
    (hlo : ∀ j, lo' j ≤ lo j) (hhi : ∀ j, hi j ≤ hi' j) :
    (openBox lo hi : Set (SpatialCoordinates d)) ⊆
      (openBox lo' hi' : Set (SpatialCoordinates d)) := by
  intro x hx
  have hx' : x ∈ openBox lo hi := hx
  rw [mem_openBox_iff] at hx'
  have : x ∈ openBox lo' hi' := by
    rw [mem_openBox_iff]
    exact fun j => ⟨lt_of_le_of_lt (hlo j) (hx' j).1, lt_of_lt_of_le (hx' j).2 (hhi j)⟩
  exact this

/-- **Doubling a box across every face in a finite set of coordinates.**  Given a
killed datum on `openBox lo hi`, repeated upward and downward reflection in each
coordinate of `I` produces a killed datum on a strictly larger box which agrees
with the original datum on the original box and whose corners have moved only in
the coordinates of `I`.  Each coordinate is doubled in both directions, so a
boundary point whose active coordinates lie in `I` becomes interior in those
directions. -/
theorem lane2_exists_doubled_box (lo hi : SpatialCoordinates d)
    (hlohi : ∀ j, lo j < hi j) (I : Finset (Fin d))
    {u : SobolevData (openBox lo hi)} (hu : u ∈ killedSobolevGraph (openBox lo hi)) :
    ∃ (lo' hi' : SpatialCoordinates d) (w : SobolevData (openBox lo' hi')),
      w ∈ killedSobolevGraph (openBox lo' hi') ∧
      (∀ j ∈ I, lo' j < lo j ∧ hi j < hi' j) ∧
      (∀ j, j ∉ I → lo' j = lo j ∧ hi' j = hi j) ∧
      ((w.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (openBox lo hi : Set (SpatialCoordinates d))]
          (u.1 : SpatialCoordinates d → ℝ)) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    exact ⟨lo, hi, u, hu, by simp, fun j _ => ⟨rfl, rfl⟩, Filter.EventuallyEq.refl _ _⟩
  | @insert i I hiI ih =>
    obtain ⟨lo₀, hi₀, w, hw, hstrict, heq, hae⟩ := ih
    have hmono : ∀ j, lo₀ j ≤ lo j ∧ hi j ≤ hi₀ j := by
      intro j
      by_cases hj : j ∈ I
      · exact ⟨(hstrict j hj).1.le, (hstrict j hj).2.le⟩
      · exact ⟨(heq j hj).1.le, (heq j hj).2.ge⟩
    have hlo₀hi₀ : ∀ j, lo₀ j < hi₀ j := fun j =>
      lt_of_le_of_lt (hmono j).1 (lt_of_lt_of_le (hlohi j) (hmono j).2)
    obtain ⟨hloi, hhii⟩ : lo₀ i = lo i ∧ hi₀ i = hi i := heq i hiI
    -- the upward step: double across the upper `i`-face
    obtain ⟨w₁, hw₁, hae₁, -⟩ :=
      lane2_reflect_step_up (boxEvenReflectionDomain lo₀ hi₀ i) rfl rfl hw
    -- the downward step: double the result across its lower `i`-face
    obtain ⟨w₂, hw₂, hae₂, -⟩ :=
      lane2_reflect_step_down
        (boxEvenReflectionDomain (lowerDoubledCorner lo₀ (doubledCorner lo₀ hi₀ i) i)
          (Function.update (doubledCorner lo₀ hi₀ i) i (lo₀ i)) i)
        (boxEvenReflectionDomain_mirror_reflected lo₀ (doubledCorner lo₀ hi₀ i) i)
        (boxEvenReflectionDomain_mirror_U lo₀ (doubledCorner lo₀ hi₀ i) i) hw₁
    refine ⟨lowerDoubledCorner lo₀ (doubledCorner lo₀ hi₀ i) i, doubledCorner lo₀ hi₀ i,
      w₂, hw₂, ?_, ?_, ?_⟩
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
    · have hsub1 : (openBox lo hi : Set (SpatialCoordinates d)) ⊆
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
      have h2 := ae_restrict_of_ae_restrict_of_subset
        (μ := (volume : Measure (SpatialCoordinates d))) hsub2 hae₂
      have h1 := ae_restrict_of_ae_restrict_of_subset
        (μ := (volume : Measure (SpatialCoordinates d))) hsub1 hae₁
      exact Filter.EventuallyEq.trans h2 (Filter.EventuallyEq.trans h1 hae)

/-- A single-coordinate reflection depends only on the reflected coordinate of
the base point. -/
theorem coordinateReflection_single_congr (z z' : SpatialCoordinates d) (i : Fin d)
    (h : z i = z' i) : coordinateReflection z {i} = coordinateReflection z' {i} := by
  funext x
  funext j
  by_cases hj : j = i
  · subst hj
    rw [coordinateReflection_single_apply_self, coordinateReflection_single_apply_self, h]
  · rw [coordinateReflection_single_apply_of_ne _ hj,
      coordinateReflection_single_apply_of_ne _ hj]

/-- **The odd extension over the active set.**  Let `x₀` be a boundary point of
`openBox lo hi` lying on the `i₀`-face, let `I` collect the other coordinates in
which `x₀` sits on a face, and let `u` be a killed datum on the box.  Doubling
the box in every coordinate of `I` and then reflecting oddly across the
`i₀`-face produces a killed datum `w` on an open box `B` which

* contains `x₀` in its interior and contains the original box,
* is invariant under the reflection `ρ` in the plane `{x i₀ = x₀ i₀}`,
* agrees with `u` almost everywhere on the original box, and
* is almost everywhere odd under `ρ`.

A continuous representative of `w` on `B` therefore vanishes at `x₀` by
`lane2_eq_zero_on_activeFaces`, which is the boundary-continuity step. -/
theorem lane2_exists_odd_doubled_box (lo hi x₀ : SpatialCoordinates d)
    (hlohi : ∀ j, lo j < hi j) (hx₀ : ∀ j, x₀ j ∈ Set.Icc (lo j) (hi j))
    (i₀ : Fin d) (hface : x₀ i₀ = lo i₀ ∨ x₀ i₀ = hi i₀)
    (I : Finset (Fin d)) (hi₀I : i₀ ∉ I)
    (hinterior : ∀ j, j ∉ I → j ≠ i₀ → lo j < x₀ j ∧ x₀ j < hi j)
    {u : SobolevData (openBox lo hi)} (hu : u ∈ killedSobolevGraph (openBox lo hi)) :
    ∃ (lo' hi' : SpatialCoordinates d) (w : SobolevData (openBox lo' hi')),
      w ∈ killedSobolevGraph (openBox lo' hi') ∧
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
          = -((w.1 : SpatialCoordinates d → ℝ) x)) := by
  classical
  obtain ⟨lo₀, hi₀, w₀, hw₀, hstrict, heq, hae₀⟩ :=
    lane2_exists_doubled_box lo hi hlohi I hu
  have hmono : ∀ j, lo₀ j ≤ lo j ∧ hi j ≤ hi₀ j := by
    intro j
    by_cases hj : j ∈ I
    · exact ⟨(hstrict j hj).1.le, (hstrict j hj).2.le⟩
    · exact ⟨(heq j hj).1.le, (heq j hj).2.ge⟩
  have hlo₀hi₀ : ∀ j, lo₀ j < hi₀ j := fun j =>
    lt_of_le_of_lt (hmono j).1 (lt_of_lt_of_le (hlohi j) (hmono j).2)
  obtain ⟨hloi, hhii⟩ : lo₀ i₀ = lo i₀ ∧ hi₀ i₀ = hi i₀ := heq i₀ hi₀I
  -- in every coordinate other than `i₀` the point is already interior to the doubled box
  have hside : ∀ j, j ≠ i₀ → lo₀ j < x₀ j ∧ x₀ j < hi₀ j := by
    intro j hj
    by_cases hjI : j ∈ I
    · exact ⟨lt_of_lt_of_le (hstrict j hjI).1 (hx₀ j).1,
        lt_of_le_of_lt (hx₀ j).2 (hstrict j hjI).2⟩
    · obtain ⟨h1, h2⟩ := heq j hjI
      obtain ⟨h3, h4⟩ := hinterior j hjI hj
      exact ⟨h1 ▸ h3, h2 ▸ h4⟩
  rcases hface with hlow | hhigh
  · -- `x₀` sits on the lower `i₀`-face: reflect downward
    refine ⟨lowerDoubledCorner lo₀ hi₀ i₀, hi₀, ?_⟩
    obtain ⟨w, hw, hae, hodd⟩ :=
      lane2_reflect_step_down
        (boxEvenReflectionDomain (lowerDoubledCorner lo₀ hi₀ i₀)
          (Function.update hi₀ i₀ (lo₀ i₀)) i₀)
        (boxEvenReflectionDomain_mirror_reflected lo₀ hi₀ i₀)
        (boxEvenReflectionDomain_mirror_U lo₀ hi₀ i₀) hw₀
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
    refine ⟨w, hw, ?_, ?_, ?_, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_openBox_iff]
      intro j
      by_cases hj : j = i₀
      · subst hj
        rw [lowerDoubledCorner, Function.update_self, hlow, ← hloi]
        exact ⟨by linarith [hlo₀hi₀ j], by
          have := (hx₀ j).2
          have h2 := hlo₀hi₀ j
          have h3 := (hmono j).2
          rw [hloi, ← hlow] at h2 ⊢
          linarith⟩
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
          (μ := (volume : Measure (SpatialCoordinates d)))
          (openBox_subset_openBox (fun j => (hmono j).1) (fun j => (hmono j).2)) hae) hae₀
    · rw [← hcong]; exact hodd
  · -- `x₀` sits on the upper `i₀`-face: reflect upward
    refine ⟨lo₀, doubledCorner lo₀ hi₀ i₀, ?_⟩
    obtain ⟨w, hw, hae, hodd⟩ :=
      lane2_reflect_step_up (boxEvenReflectionDomain lo₀ hi₀ i₀) rfl rfl hw₀
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
    refine ⟨w, hw, ?_, ?_, ?_, ?_, ?_⟩
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
          (μ := (volume : Measure (SpatialCoordinates d)))
          (openBox_subset_openBox (fun j => (hmono j).1) (fun j => (hmono j).2)) hae) hae₀
    · rw [← hcong]; exact hodd

namespace EvenReflectionDomain

variable (D : EvenReflectionDomain d)

/-- Reflecting a coefficient from the upper half to the lower half and back
returns it almost everywhere. -/
theorem lane2_reflectedCoefficient_reflection_ae (b : PositiveCoefficient D.reflected) :
    ((D.reflectedCoefficient
        (reflectionCoefficient D.z {D.i} D.preimage_reflected b)).val :
        SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (D.reflected : Set (SpatialCoordinates d))]
        (b.val : SpatialCoordinates d → ℝ) := by
  have hmR : MeasurePreserving (coordinateReflection D.z {D.i})
      (volume.restrict (D.reflected : Set (SpatialCoordinates d)))
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
    coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_Ω
  have hrc : D.reflectedCoefficient (reflectionCoefficient D.z {D.i} D.preimage_reflected b)
      = reflectionCoefficient D.z {D.i} D.preimage_Ω
        (reflectionCoefficient D.z {D.i} D.preimage_reflected b) := rfl
  rw [hrc]
  have h1 := reflectionCoefficient_coeFn D.z {D.i} D.preimage_Ω
    (reflectionCoefficient D.z {D.i} D.preimage_reflected b)
  have h2 := hmR.quasiMeasurePreserving.ae
    (reflectionCoefficient_coeFn D.z {D.i} D.preimage_reflected b)
  filter_upwards [h1, h2] with x hx hx2
  simp only [Function.comp_apply] at hx hx2 ⊢
  rw [hx, hx2, coordinateReflection_involutive D.z {D.i} x]

end EvenReflectionDomain

end SubdiffusiveProcess
