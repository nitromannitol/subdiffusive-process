import SubdiffusiveProcess.Paper.prop_conc_form_continuity
import SubdiffusiveProcess.Paper.prop_locality
import SubdiffusiveProcess.DirichletForm.ResolventContinuousCore

/-! Extracted local form data for the relative concentration proof.
This module proves the stated deterministic implications; it does not construct random bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set Topology TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4 Homogenization SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff BigOperators

noncomputable section
namespace Paper
variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

/-- Locality of the dual limiting energy implies locality of its representing closed form. -/
theorem aux_prop_conc_form_data_qlocal
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGsymm : ∀ f g : DomainL2 (centeredCube z r hr),
      (inner ℝ f (G g) : ℝ) = (inner ℝ g (G f) : ℝ))
    (hLower : ∀ (wN : ℕ → S.space) (w : DomainL2 (centeredCube z r hr)),
      (∀ f : DomainL2 (centeredCube z r hr),
        Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      limitFormEnergy G w ≤
        liminf (fun n => ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal)) atTop)
    (hRecovery : ∀ w ∈ limitFormDomain G, ∃ wN : ℕ → S.space,
      Tendsto (fun n => ((wN n).val.1,
        ((responseForm S (a n) (wN n) (wN n) : ℝ) : EReal))) atTop
        (𝓝 (w, limitFormEnergy G w)))
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n)
    (Kstar : ℝ) (hKstar : ∀ n, KN n ≤ Kstar)
    (hfrac : ∀ w : S.space,
      cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
        (fun _ : Fin 1 => w.val.1) < ⊤)
    (hcoercive : ∀ n (w : S.space),
      ‖w.val.1‖ ^ 2 + volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
          (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤ KN n * responseForm S (a n) w w)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (t : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (hcutoffs : ∀ (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O →
        closure O ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → S.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
            0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm S (a n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), ∀ rr : ℝ,
            0 < rr → rr ≤ 1 →
            ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((a n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (F : DirichletForm.ClosedForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hF : ∀ u, F.energy u = limitFormEnergy G u) :
    ∀ u v : DomainL2 (centeredCube z r hr),
      F.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
      F.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
      ∀ uc vc : SpatialCoordinates d → ℝ,
        (u : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
        (v : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
        Continuous uc → Continuous vc →
        HasCompactSupport uc → HasCompactSupport vc →
        tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
        tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
        ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
          (∀ x ∈ W, uc x = c) → F.form u v = 0 := by
  intro u v hu hv uc vc huc hvc hucont hvcont husupp hvsupp husuppQ hvsuppQ c W hW hsupp hconst
  have hu' : MemFormCore G u :=
    ⟨by
        show limitFormEnergy G u < ⊤
        rw [← hF u]
        exact (F.energy_lt_top_iff u).2 hu.1,
      hu.2⟩
  have hv' : MemFormCore G v :=
    ⟨by
        show limitFormEnergy G v < ⊤
        rw [← hF v]
        exact (F.energy_lt_top_iff v).2 hv.1,
      hv.2⟩
  have hbi := prop_locality d hd z r hr S hS a G hGsymm hLower hRecovery KN hKN Kstar hKstar
    hfrac hcoercive hInterp t ht htd hcutoffs u v hu' hv' uc vc huc hvc hucont hvcont hvsupp
    husuppQ hvsuppQ husupp c W hW hsupp hconst
  exact SubdiffusiveProcess.LimitFormCore.form_eq_zero_of_bilinear F G hF u v hu.1 hv.1 hbi

/-- Strong locality from the Q-relative Beurling–Deny step `BDQ` and the header's `BD`. -/
theorem aux_prop_conc_form_data_isStronglyLocal (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (F : _root_.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (BD : DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
    (BDQ : (∃ C, DirichletForm.IsCoreOn F.toClosedForm
        (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) →
      DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (C : Set (DomainL2 (centeredCube z r hr)))
    (hC : DirichletForm.IsCoreOn F.toClosedForm
      (centeredCube z r hr : Set (SpatialCoordinates d)) C)
    (hloc : ∀ u v : DomainL2 (centeredCube z r hr),
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        F.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → F.toClosedForm.form u v = 0) :
    DirichletForm.IsStronglyLocal F.toClosedForm :=
  BD.isStronglyLocal_of_onCore (SubdiffusiveProcess.LimitFormCore.isRegular_of_isCoreOn z r hr _ C hC)
    (BDQ ⟨C, hC⟩ hloc)


/-- The local resolvent, recovery, cutoff and density data yield a regular strongly local form. -/
theorem prop_conc_form_data (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (GNi : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGNi : ∀ (n : ℕ) (f : DomainL2 (centeredCube z r hr)), GNi n f =
      (responseSolution (killedResponseSpace hP) (a n)
        ((sobolevVolumeLoad f).comp (killedResponseSpace hP).space.subtypeL)).val.1)
    (G Rroot : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGtend : Tendsto GNi atTop (𝓝 G))
    (hGsymm0 : ∀ x y : DomainL2 (centeredCube z r hr), inner ℝ (G x) y = inner ℝ x (G y))
    (hGinj : Function.Injective G)
    (hRsymm : ∀ x y : DomainL2 (centeredCube z r hr),
      inner ℝ (Rroot x) y = inner ℝ x (Rroot y))
    (hRcomp : Rroot.comp Rroot = G)
    (hRdom : limitFormDomain G = Set.range Rroot)
    (EForm : _root_.DirichletForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hEForm : ∀ u : DomainL2 (centeredCube z r hr),
      EForm.toClosedForm.energy u = limitFormEnergy G u)
    (hHNC : DirichletForm.HasNormalContractions EForm)
    (hGlow : ∀ (uN : ℕ → DomainL2 (centeredCube z r hr)) (u : DomainL2 (centeredCube z r hr)),
      (∀ f : DomainL2 (centeredCube z r hr),
        Tendsto (fun n => inner ℝ f (uN n)) atTop (𝓝 (inner ℝ f u))) →
      limitFormEnergy G u ≤
        liminf (fun n => sInf {e : EReal | ∃ w : (killedResponseSpace hP).space,
          w.val.1 = uN n ∧ e = (responseForm (killedResponseSpace hP) (a n) w w : EReal)})
          atTop)
    (hGrec : ∀ u ∈ limitFormDomain G, ∃ w : ℕ → (killedResponseSpace hP).space,
      Tendsto (fun n => ((w n).val.1,
        ((responseForm (killedResponseSpace hP) (a n) (w n) (w n) : ℝ) : EReal))) atTop
        (𝓝 (u, limitFormEnergy G u)))
    (hdense : ∀ u ∈ limitFormDomain G, ∀ ε : ℝ, 0 < ε →
      ∃ f : DomainL2 (centeredCube z r hr),
        (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ (⊤ : ℕ∞) fc ∧ HasCompactSupport fc ∧
          tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
          (f : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) ∧
        ‖u - G f‖ ≤ ε ∧ limitFormEnergy G (u - G f) ≤ ((ε : ℝ) : EReal))
    (Kcoef : ℝ) (hKcoef : 0 ≤ Kcoef)
    (hCoerv : ∀ (n : ℕ) (v : (killedResponseSpace hP).space),
      cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
          (fun _ : Fin 1 => v.val.1) < ⊤ ∧
      ‖v.val.1‖ ^ 2 + volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
          ((cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
              (fun _ : Fin 1 => v.val.1)).toReal) ^ 2 ≤
        Kcoef * responseForm (killedResponseSpace hP) (a n) v v)
    (Interp : CubeFractionalInterpolationInput d hd)
    (Kreg : ℝ) (hKreg : 0 ≤ Kreg)
    (hDreg : ∀ N : ℕ, Paper.aux_prop_conc_form_cutoff_continuity_DirProp z r hr (a N) Kreg)
    (BD : DirichletForm.HasBeurlingDenyLocality EForm.toClosedForm)
    (BDQ : (∃ C, DirichletForm.IsCoreOn EForm.toClosedForm
        (centeredCube z r hr : Set (SpatialCoordinates d)) C) →
      (∀ u v : DomainL2 (centeredCube z r hr),
        EForm.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
        EForm.toClosedForm.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
        ∀ uc vc : SpatialCoordinates d → ℝ,
          (u : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
          (v : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
          Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
          tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
            (∀ x ∈ W, uc x = c) → EForm.toClosedForm.form u v = 0) →
      DirichletForm.IsStronglyLocalOnCore EForm.toClosedForm)
    (hcutoffs : ∀ (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O →
        closure O ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → (killedResponseSpace hP).space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
            0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm (killedResponseSpace hP) (a n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), ∀ rr : ℝ,
            0 < rr → rr ≤ 1 →
            ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((a n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ ((d : ℝ) - 1 / 2))))
    (hunif : ∀ f0 : SpatialCoordinates d → ℝ, Continuous f0 → HasCompactSupport f0 →
      tsupport f0 ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∀ ε : ℝ, 0 < ε → ∃ w ∈ EForm.toClosedForm.domain, ∃ g : SpatialCoordinates d → ℝ,
        Continuous g ∧ HasCompactSupport g ∧
        tsupport g ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        (w : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] g ∧
        ∀ x, |g x - f0 x| < ε) :
    ∃ F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
      (∀ u : DomainL2 (centeredCube z r hr),
        F.toClosedForm.energy u = limitFormEnergy G u) ∧
      DirichletForm.IsRegular F.toClosedForm ∧
      DirichletForm.IsStronglyLocal F.toClosedForm := by
  have hcont : ∀ f : DomainL2 (centeredCube z r hr),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ (⊤ : ℕ∞) fc ∧ HasCompactSupport fc ∧
          tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
          (f : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) →
      ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
        ((G f : DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
        ∀ x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0 :=
    fun f hf => Paper.prop_conc_form_continuity hd z r hr hP a Kreg hKreg hDreg GNi hGNi G
      hGtend f hf
  have hCoreOn := SubdiffusiveProcess.LimitFormCore.isCoreOn z r hr EForm hHNC G Rroot hEForm hRsymm hGinj
    hRcomp hRdom hdense hcont hunif
  refine ⟨EForm, hEForm, SubdiffusiveProcess.LimitFormCore.isRegular_of_isCoreOn z r hr EForm.toClosedForm _
    hCoreOn, ?_⟩
  have hGsymmQ : ∀ f g : DomainL2 (centeredCube z r hr),
      (inner ℝ f (G g) : ℝ) = (inner ℝ g (G f) : ℝ) := by
    intro f g
    calc inner ℝ f (G g) = inner ℝ (G g) f := real_inner_comm _ _
      _ = inner ℝ g (G f) := hGsymm0 g f
  have hLowerQ : ∀ (wN : ℕ → (killedResponseSpace hP).space)
      (w : DomainL2 (centeredCube z r hr)),
      (∀ f : DomainL2 (centeredCube z r hr),
        Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
      limitFormEnergy G w ≤ liminf (fun n => (responseForm (killedResponseSpace hP) (a n)
        (wN n) (wN n) : EReal)) atTop := by
    intro wN w hweak
    refine (hGlow (fun n => (wN n).val.1) w hweak).trans ?_
    exact liminf_le_liminf (Filter.Eventually.of_forall fun n => sInf_le ⟨wN n, rfl, rfl⟩)
  have hfrac : ∀ w : (killedResponseSpace hP).space,
      cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder (fun _ : Fin 1 => w.val.1) <
        ⊤ :=
    fun w => (hCoerv 0 w).1
  have hcoercive : ∀ (n : ℕ) (w : (killedResponseSpace hP).space),
      ‖w.val.1‖ ^ 2 + volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
          ((cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
              (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤
        Kcoef * responseForm (killedResponseSpace hP) (a n) w w :=
    fun n w => (hCoerv n w).2
  have hloc := Paper.aux_prop_conc_form_data_qlocal d hd z r hr (killedResponseSpace hP) rfl a G hGsymmQ
    hLowerQ hGrec (fun _ => Kcoef) (fun _ => hKcoef) Kcoef (fun _ => le_refl Kcoef) hfrac
    hcoercive Interp ((d : ℝ) - 1 / 2) (by linarith only []) (by linarith only []) hcutoffs EForm.toClosedForm
    hEForm
  exact Paper.aux_prop_conc_form_data_isStronglyLocal z r hr EForm BD BDQ _ hCoreOn hloc

end Paper
