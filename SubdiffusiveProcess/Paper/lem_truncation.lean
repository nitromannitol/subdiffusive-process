import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Lane2.BoundaryPackaging
import SubdiffusiveProcess.Lane2.NativeBridge
import SubdiffusiveProcess.Lane2.ResponseMarkov
import SubdiffusiveProcess.Main.MeasureTrace
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Paper.lem_truncation_family
import SubdiffusiveProcess.Paper.lem_truncation_cauchy
import SubdiffusiveProcess.Paper.obl_BH
import SubdiffusiveProcess.Paper.prop_killed_consistency
import SubdiffusiveProcess.Paper.prop_killed_inverse
import SubdiffusiveProcess.Paper.prop_regularity
import SubdiffusiveProcess.Paper.obl_FOT


open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

lemma aux_lem_truncation_cauchy_no_fot
    (d : ℕ) (hd : 2 ≤ d)
    (zQ zq : SpatialCoordinates d)
    (R r : ℝ) (hR0 : 0 < R) (hr0 : 0 < r)
    (hqQ : (centeredCube zq r hr0 : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))
    (EQ : _root_.DirichletForm
      (volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure EQ.toClosedForm)
    (hnc : DirichletForm.HasNormalContractions EQ)
    (halg : DirichletForm.IsCoreAlgebra EQ.toClosedForm)
    (hreg : ∃ C : Set (DomainL2 (centeredCube zQ R hR0)),
      DirichletForm.IsCoreOn EQ.toClosedForm
        (centeredCube zQ R hR0 : Set (SpatialCoordinates d)) C)
    (Dq : Submodule ℝ (DomainL2 (centeredCube zQ R hR0)))
    (hkilled : DirichletForm.IsKilledDomain EQ.toClosedForm
      (centeredCube zq r hr0 : Set (SpatialCoordinates d)) Dq)
    (v : DomainL2 (centeredCube zQ R hR0)) (hv : v ∈ EQ.toClosedForm.domain)
    (vc : SpatialCoordinates d → ℝ)
    (hvccont : ContinuousOn vc
      (closure (centeredCube zQ R hR0 : Set (SpatialCoordinates d))))
    (hvrep : (v : SpatialCoordinates d → ℝ)
      =ᵐ[(volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))] vc)
    (hvanish : ∀ x ∈ frontier (centeredCube zq r hr0 : Set (SpatialCoordinates d)),
      vc x = 0)
    (hBH_null : ∀ N : Set ℝ, MeasurableSet N → volume N = 0 →
      Gamma.measure v (vc ⁻¹' N) = 0)
    (w : ℝ → DomainL2 (centeredCube zQ R hR0))
    (hfamily : ∀ ε : ℝ, 0 < ε →
      w ε ∈ Dq ∧
      (∀ B : Set (SpatialCoordinates d), MeasurableSet B →
        Gamma.measure (w ε) B =
          Gamma.measure v (B ∩ (centeredCube zq r hr0 : Set (SpatialCoordinates d)) ∩
            {x : SpatialCoordinates d | ε < |vc x|})) ∧
      ((w ε : SpatialCoordinates d → ℝ)
        =ᵐ[(volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))]
          fun x => DirichletForm.truncation ε
            (Set.indicator
              (closure (centeredCube zq r hr0 : Set (SpatialCoordinates d))) vc x))) :
    (∀ ε ε' : ℝ, 0 < ε' → ε' < ε →
      EQ.toClosedForm.form (w ε - w ε') (w ε - w ε') =
        (Gamma.measure v
          ((centeredCube zq r hr0 : Set (SpatialCoordinates d)) ∩
            {x : SpatialCoordinates d | ε' < |vc x| ∧ |vc x| < ε})).toReal) ∧
    Tendsto (fun ε : ℝ =>
        (Gamma.measure v
          ((centeredCube zq r hr0 : Set (SpatialCoordinates d)) ∩
            {x : SpatialCoordinates d | 0 < |vc x| ∧ |vc x| < ε})).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    (∀ δ : ℝ, 0 < δ →
      ∃ ε0 : ℝ, 0 < ε0 ∧
        ∀ ε ε' : ℝ, 0 < ε → ε < ε0 → 0 < ε' → ε' < ε0 →
          EQ.toClosedForm.form (w ε - w ε') (w ε - w ε') < δ) := by
  let q : Set (SpatialCoordinates d) :=
    (centeredCube zq r hr0 : Set (SpatialCoordinates d))
  let Q : Set (SpatialCoordinates d) :=
    (centeredCube zQ R hR0 : Set (SpatialCoordinates d))
  have hqopen : IsOpen q := by
    dsimp [q]
    exact (centeredCube zq r hr0).isOpen
  have hQopen : IsOpen Q := by
    dsimp [Q]
    exact (centeredCube zQ R hR0).isOpen
  have hqQ' : q ⊆ Q := by
    exact hqQ
  have hqclQ : q ⊆ closure Q := hqQ'.trans subset_closure
  have hqcont : ContinuousOn vc q := hvccont.mono hqclQ
  have habscont : ContinuousOn (fun x : SpatialCoordinates d => |vc x|) q :=
    hqcont.abs
  have hQmeas : MeasurableSet Q := hQopen.measurableSet
  have hqmeas : MeasurableSet q := hqopen.measurableSet
  have hlevel : ∀ c : ℝ,
      Gamma.measure v (q ∩ {x : SpatialCoordinates d | vc x = c}) = 0 := by
    intro c
    refine measure_mono_null (fun x hx => ?_)
      (hBH_null {c} (measurableSet_singleton c) (by simp))
    exact hx.2
  let s : ℝ → Set (SpatialCoordinates d) := fun ε =>
    q ∩ {x : SpatialCoordinates d | 0 < |vc x| ∧ |vc x| < ε}
  have hsopen : ∀ {ε : ℝ}, 0 < ε → IsOpen (s ε) := by
    intro ε hε
    change IsOpen (q ∩ (fun x : SpatialCoordinates d => |vc x|) ⁻¹' Set.Ioo 0 ε)
    exact habscont.isOpen_inter_preimage hqopen isOpen_Ioo
  have hsmeas : ∀ {ε : ℝ}, 0 < ε → MeasurableSet (s ε) := by
    intro ε hε
    exact (hsopen hε).measurableSet
  have hsmono : ∀ i j : ℝ, 0 < i → i ≤ j → s i ⊆ s j := by
    intro i j hi hij x hx
    change x ∈ q ∩ {x : SpatialCoordinates d | 0 < |vc x| ∧ |vc x| < i} at hx
    change x ∈ q ∩ {x : SpatialCoordinates d | 0 < |vc x| ∧ |vc x| < j}
    exact ⟨hx.1, hx.2.1, lt_of_lt_of_le hx.2.2 hij⟩
  have hs_inter : (⋂ ε > (0 : ℝ), s ε) = ∅ := by
    ext x
    constructor
    · intro hx
      have hxall : ∀ ε : ℝ, 0 < ε → x ∈ s ε := by
        simpa only [mem_iInter] using hx
      have hxone := hxall 1 (by norm_num)
      have hxpos : 0 < |vc x| := by
        exact (show x ∈ q ∩ {x : SpatialCoordinates d |
          0 < |vc x| ∧ |vc x| < 1} from hxone).2.1
      have hxlt := (show x ∈ q ∩ {x : SpatialCoordinates d |
          0 < |vc x| ∧ |vc x| < |vc x|} from hxall |vc x| hxpos).2.2
      exact (lt_irrefl _ hxlt).elim
    · intro hx
      exact (by simpa using hx)
  have hμtend : Tendsto (fun ε : ℝ => Gamma.measure v (s ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := tendsto_measure_biInter_gt (μ := Gamma.measure v) (s := s)
      (fun ε hε => (hsmeas hε).nullMeasurableSet) hsmono
      ⟨1, by norm_num, (Gamma.measure_ne_top hv (s 1))⟩
    simpa only [Function.comp_apply, hs_inter, measure_empty] using h
  have hreal : Tendsto (fun ε : ℝ => (Gamma.measure v (s ε)).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    exact (ENNReal.continuousAt_toReal (by simp)).tendsto.comp hμtend
  have hfirst : ∀ ε ε' : ℝ, 0 < ε' → ε' < ε →
      EQ.toClosedForm.form (w ε - w ε') (w ε - w ε') =
        (Gamma.measure v
          (q ∩ {x : SpatialCoordinates d | ε' < |vc x| ∧ |vc x| < ε})).toReal := by
    intro ε ε' hε' hlt
    have hε : 0 < ε := lt_trans hε' hlt
    have hwε : w ε ∈ EQ.toClosedForm.domain :=
      hkilled.le_domain (hfamily ε hε).1
    have hwε' : w ε' ∈ EQ.toClosedForm.domain :=
      hkilled.le_domain (hfamily ε' hε').1
    have hdiff : w ε - w ε' ∈ EQ.toClosedForm.domain :=
      EQ.toClosedForm.domain.sub_mem hwε hwε'
    have hzero : Gamma.measure (0 : DomainL2 (centeredCube zQ R hR0)) = 0 :=
      aux_lem_truncation_cauchy_measure_zero Gamma
    let Aplus : Set (SpatialCoordinates d) := q ∩ {x | ε < vc x}
    let Aminus : Set (SpatialCoordinates d) := q ∩ {x | vc x < -ε}
    let B : Set (SpatialCoordinates d) := q ∩ {x | |vc x| < ε}
    let Lplus : Set (SpatialCoordinates d) := q ∩ {x | vc x = ε}
    let Lminus : Set (SpatialCoordinates d) := q ∩ {x | vc x = -ε}
    have hAplusopen : IsOpen Aplus := by
      change IsOpen (q ∩ vc ⁻¹' Set.Ioi ε)
      exact hqcont.isOpen_inter_preimage hqopen isOpen_Ioi
    have hAminusopen : IsOpen Aminus := by
      change IsOpen (q ∩ vc ⁻¹' Set.Iio (-ε))
      exact hqcont.isOpen_inter_preimage hqopen isOpen_Iio
    have hBopen : IsOpen B := by
      change IsOpen (q ∩ (fun x : SpatialCoordinates d => |vc x|) ⁻¹' Set.Iio ε)
      exact habscont.isOpen_inter_preimage hqopen isOpen_Iio
    have hAplusmeas : MeasurableSet Aplus := hAplusopen.measurableSet
    have hAminusmeas : MeasurableSet Aminus := hAminusopen.measurableSet
    have hBmeas : MeasurableSet B := hBopen.measurableSet
    have hLplusmeas : MeasurableSet Lplus := by
      rcases (continuousOn_iff_isClosed.mp hqcont {ε} isClosed_singleton) with
        ⟨C, hC, hCeq⟩
      have heq : Lplus = C ∩ q := by
        ext x
        constructor
        · intro hx
          have : x ∈ vc ⁻¹' ({ε} : Set ℝ) ∩ q := by
            exact ⟨by simpa [Set.preimage, hx.2], hx.1⟩
          rw [hCeq] at this
          exact this
        · intro hx
          have : x ∈ vc ⁻¹' ({ε} : Set ℝ) ∩ q := by
            rw [hCeq]
            exact hx
          exact ⟨this.2, by simpa [Set.preimage] using this.1⟩
      rw [heq]
      exact hC.measurableSet.inter hqmeas
    have hLminusmeas : MeasurableSet Lminus := by
      rcases (continuousOn_iff_isClosed.mp hqcont {-ε} isClosed_singleton) with
        ⟨C, hC, hCeq⟩
      have heq : Lminus = C ∩ q := by
        ext x
        constructor
        · intro hx
          have : x ∈ vc ⁻¹' ({-ε} : Set ℝ) ∩ q := by
            exact ⟨by simpa [Set.preimage, hx.2], hx.1⟩
          rw [hCeq] at this
          exact this
        · intro hx
          have : x ∈ vc ⁻¹' ({-ε} : Set ℝ) ∩ q := by
            rw [hCeq]
            exact hx
          exact ⟨this.2, by simpa [Set.preimage] using this.1⟩
      rw [heq]
      exact hC.measurableSet.inter hqmeas
    have hrepdiff : (w ε - w ε' : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict Q] (fun x =>
          DirichletForm.truncation ε
              (Set.indicator (closure q) vc x) -
            DirichletForm.truncation ε'
              (Set.indicator (closure q) vc x)) := by
      filter_upwards [Lp.coeFn_sub (w ε) (w ε'),
        (hfamily ε hε).2.2, (hfamily ε' hε').2.2] with x hx hxε hxε'
      simpa [q, Pi.sub_apply, hxε, hxε'] using hx
    have hconst_plus : (w ε - w ε' : SpatialCoordinates d → ℝ) =ᵐ[
        (volume.restrict Q).restrict Aplus]
        (fun _ => (0 : ℝ) + (ε' - ε)) := by
      filter_upwards [hrepdiff.restrict, ae_restrict_mem hAplusmeas] with x hx hxa
      have hxc : Set.indicator (closure q) vc x = vc x :=
        Set.indicator_of_mem (subset_closure hxa.1) vc
      rw [hx, hxc, aux_lem_truncation_cauchy_trunc_pos ε ε' (vc x)
        hε' hlt hxa.2]
      simp
    have hconst_minus : (w ε - w ε' : SpatialCoordinates d → ℝ) =ᵐ[
        (volume.restrict Q).restrict Aminus]
        (fun _ => (0 : ℝ) + (ε - ε')) := by
      filter_upwards [hrepdiff.restrict, ae_restrict_mem hAminusmeas] with x hx hxa
      have hxc : Set.indicator (closure q) vc x = vc x :=
        Set.indicator_of_mem (subset_closure hxa.1) vc
      rw [hx, hxc, aux_lem_truncation_cauchy_trunc_neg ε ε' (vc x)
        hε' hlt hxa.2]
      simp
    have hconst_B : (w ε - w ε' : SpatialCoordinates d → ℝ) =ᵐ[
        (volume.restrict Q).restrict B]
        (fun x => ((-w ε' : DomainL2 (centeredCube zQ R hR0)) :
          SpatialCoordinates d → ℝ) x + 0) := by
      filter_upwards [hrepdiff.restrict, (Lp.coeFn_neg (w ε')).restrict,
        (hfamily ε' hε').2.2.restrict, ae_restrict_mem hBmeas] with x hx hxneg hxε' hxb
      have hxc : Set.indicator (closure q) vc x = vc x :=
        Set.indicator_of_mem (subset_closure hxb.1) vc
      have hsmall : DirichletForm.truncation ε (vc x) = 0 := by
        exact aux_lem_truncation_cauchy_trunc_small ε (vc x)
          (abs_lt.mp hxb.2).1 (abs_lt.mp hxb.2).2
      rw [hx, hxc, hsmall]
      rw [show ((-w ε' : DomainL2 (centeredCube zQ R hR0)) :
          SpatialCoordinates d → ℝ) x = -((w ε' :
            DomainL2 (centeredCube zQ R hR0)) : SpatialCoordinates d → ℝ) x by
            exact hxneg]
      have hxc' : Set.indicator
          (closure (centeredCube zq r hr0 : Set (SpatialCoordinates d))) vc x = vc x := by
        simpa [q] using hxc
      have hxε'vc : ((w ε' : DomainL2 (centeredCube zQ R hR0)) :
          SpatialCoordinates d → ℝ) x = DirichletForm.truncation ε' (vc x) := by
        rw [hxε', hxc']
      rw [hxε'vc]
      ring
    have hconst_plus' : ((w ε - w ε' : DomainL2 (centeredCube zQ R hR0)) :
        SpatialCoordinates d → ℝ) =ᵐ[
        (volume.restrict Q).restrict Aplus]
        (fun _ => (0 : ℝ) + (ε' - ε)) :=
      (Lp.coeFn_sub (w ε) (w ε')).restrict |>.trans hconst_plus
    have hconst_minus' : ((w ε - w ε' : DomainL2 (centeredCube zQ R hR0)) :
        SpatialCoordinates d → ℝ) =ᵐ[
        (volume.restrict Q).restrict Aminus]
        (fun _ => (0 : ℝ) + (ε - ε')) :=
      (Lp.coeFn_sub (w ε) (w ε')).restrict |>.trans hconst_minus
    have hconst_B' : ((w ε - w ε' : DomainL2 (centeredCube zQ R hR0)) :
        SpatialCoordinates d → ℝ) =ᵐ[
        (volume.restrict Q).restrict B]
        (fun x => ((-w ε' : DomainL2 (centeredCube zQ R hR0)) :
          SpatialCoordinates d → ℝ) x + 0) :=
      (Lp.coeFn_sub (w ε) (w ε')).restrict |>.trans hconst_B
    have hconst_plus'' : ((w ε - w ε' : DomainL2 (centeredCube zQ R hR0)) :
        SpatialCoordinates d → ℝ) =ᵐ[
          (volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))).restrict Aplus]
        (fun x => ((0 : DomainL2 (centeredCube zQ R hR0)) :
          SpatialCoordinates d → ℝ) x + (ε' - ε)) := by
      have hp := hconst_plus'
      have hz : ((0 : DomainL2 (centeredCube zQ R hR0)) :
          SpatialCoordinates d → ℝ) =ᵐ[
            (volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))).restrict Aplus]
          (fun _ => (0 : ℝ)) :=
        (Lp.coeFn_zero ℝ 2 (volume.restrict
          (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))).restrict
      have hp' : ((w ε - w ε' : DomainL2 (centeredCube zQ R hR0)) :
          SpatialCoordinates d → ℝ) =ᵐ[
            (volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))).restrict Aplus]
          (fun _ => (0 : ℝ) + (ε' - ε)) := by
        simpa only [Q] using hp
      filter_upwards [hp', hz] with x hx hz
      rw [hx, hz]
    have hconst_minus'' : ((w ε - w ε' : DomainL2 (centeredCube zQ R hR0)) :
        SpatialCoordinates d → ℝ) =ᵐ[
          (volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))).restrict Aminus]
        (fun x => ((0 : DomainL2 (centeredCube zQ R hR0)) :
          SpatialCoordinates d → ℝ) x + (ε - ε')) := by
      have hp := hconst_minus'
      have hz : ((0 : DomainL2 (centeredCube zQ R hR0)) :
          SpatialCoordinates d → ℝ) =ᵐ[
            (volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))).restrict Aminus]
          (fun _ => (0 : ℝ)) :=
        (Lp.coeFn_zero ℝ 2 (volume.restrict
          (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))).restrict
      have hp' : ((w ε - w ε' : DomainL2 (centeredCube zQ R hR0)) :
          SpatialCoordinates d → ℝ) =ᵐ[
            (volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))).restrict Aminus]
          (fun _ => (0 : ℝ) + (ε - ε')) := by
        simpa only [Q] using hp
      filter_upwards [hp', hz] with x hx hz
      rw [hx, hz]
    have hconst_B'' : ((w ε - w ε' : DomainL2 (centeredCube zQ R hR0)) :
        SpatialCoordinates d → ℝ) =ᵐ[
          (volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))).restrict B]
        (fun x => ((-w ε' : DomainL2 (centeredCube zQ R hR0)) :
          SpatialCoordinates d → ℝ) x + 0) := by
      simpa [Q] using hconst_B'
    have hplus0 : Gamma.measure (w ε - w ε') Aplus = 0 := by
      have hres := DirichletForm.aux_restrict_congr_constant Gamma halg
        (w ε - w ε') 0 hdiff EQ.toClosedForm.domain.zero_mem Aplus
        hAplusopen (ε' - ε) hconst_plus''
      have hmass := congrArg (fun μ : Measure (SpatialCoordinates d) => μ Aplus) hres
      have hmass' : Gamma.measure (w ε - w ε') Aplus = Gamma.measure 0 Aplus := by
        simpa only [Measure.restrict_apply_self] using hmass
      rw [hzero] at hmass'
      exact hmass'
    have hminus0 : Gamma.measure (w ε - w ε') Aminus = 0 := by
      have hres := DirichletForm.aux_restrict_congr_constant Gamma halg
        (w ε - w ε') 0 hdiff EQ.toClosedForm.domain.zero_mem Aminus
        hAminusopen (ε - ε') hconst_minus''
      have hmass := congrArg (fun μ : Measure (SpatialCoordinates d) => μ Aminus) hres
      have hmass' : Gamma.measure (w ε - w ε') Aminus = Gamma.measure 0 Aminus := by
        simpa only [Measure.restrict_apply_self] using hmass
      rw [hzero] at hmass'
      exact hmass'
    have hBmass : Gamma.measure (w ε - w ε') B =
        Gamma.measure v (q ∩ {x : SpatialCoordinates d |
          ε' < |vc x| ∧ |vc x| < ε}) := by
      have hres := DirichletForm.aux_restrict_congr_constant Gamma halg
        (w ε - w ε') (-w ε') hdiff (EQ.toClosedForm.domain.neg_mem hwε') B
        hBopen 0 hconst_B''
      have hmass := congrArg (fun μ : Measure (SpatialCoordinates d) => μ B) hres
      have hmass' : Gamma.measure (w ε - w ε') B = Gamma.measure (-w ε') B := by
        simpa only [Measure.restrict_apply_self] using hmass
      rw [aux_lem_truncation_cauchy_measure_neg Gamma hwε'] at hmass'
      calc
        Gamma.measure (w ε - w ε') B = Gamma.measure (w ε') B := hmass'
        _ = Gamma.measure v (B ∩ q ∩ {x : SpatialCoordinates d |
          ε' < |vc x|}) := (hfamily ε' hε').2.1 B hBmeas
        _ = Gamma.measure v (q ∩ {x : SpatialCoordinates d |
          ε' < |vc x| ∧ |vc x| < ε}) := by
          congr 1
          ext x
          constructor
          · intro hx
            change x ∈ B ∩ q ∩ {x : SpatialCoordinates d | ε' < |vc x|} at hx
            change x ∈ q ∩ {x : SpatialCoordinates d |
              ε' < |vc x| ∧ |vc x| < ε}
            rcases hx with ⟨⟨hxB, hxq⟩, hthr⟩
            change x ∈ q ∩ {x : SpatialCoordinates d | |vc x| < ε} at hxB
            exact ⟨hxB.1, hthr, hxB.2⟩
          · intro hx
            change x ∈ q ∩ {x : SpatialCoordinates d |
              ε' < |vc x| ∧ |vc x| < ε} at hx
            change x ∈ B ∩ q ∩ {x : SpatialCoordinates d | ε' < |vc x|}
            rcases hx with ⟨hxq, hthr, hltε⟩
            exact ⟨⟨⟨hxq, hltε⟩, hxq⟩, hthr⟩
    have hLplusε : Gamma.measure (w ε) Lplus = 0 := by
      rw [(hfamily ε hε).2.1 Lplus hLplusmeas]
      apply measure_mono_null
      · intro x hx
        have hxL := hx.1.1
        change x ∈ q ∩ {x : SpatialCoordinates d | vc x = ε} at hxL
        exact hxL
      · exact hlevel ε
    have hLpluse' : Gamma.measure (w ε') Lplus = 0 := by
      rw [(hfamily ε' hε').2.1 Lplus hLplusmeas]
      apply measure_mono_null
      · intro x hx
        have hxL := hx.1.1
        change x ∈ q ∩ {x : SpatialCoordinates d | vc x = ε} at hxL
        exact hxL
      · exact hlevel ε
    have hLminusε : Gamma.measure (w ε) Lminus = 0 := by
      rw [(hfamily ε hε).2.1 Lminus hLminusmeas]
      apply measure_mono_null
      · intro x hx
        have hxL := hx.1.1
        change x ∈ q ∩ {x : SpatialCoordinates d | vc x = -ε} at hxL
        exact hxL
      · exact hlevel (-ε)
    have hLminuse' : Gamma.measure (w ε') Lminus = 0 := by
      rw [(hfamily ε' hε').2.1 Lminus hLminusmeas]
      apply measure_mono_null
      · intro x hx
        have hxL := hx.1.1
        change x ∈ q ∩ {x : SpatialCoordinates d | vc x = -ε} at hxL
        exact hxL
      · exact hlevel (-ε)
    have hLplus0 : Gamma.measure (w ε - w ε') Lplus = 0 :=
      aux_lem_truncation_cauchy_sub_measure_zero Gamma hwε hwε' hLplusmeas
        hLplusε hLpluse'
    have hLminus0 : Gamma.measure (w ε - w ε') Lminus = 0 :=
      aux_lem_truncation_cauchy_sub_measure_zero Gamma hwε hwε' hLminusmeas
        hLminusε hLminuse'
    have hqcompε : Gamma.measure (w ε) qᶜ = 0 := by
      rw [(hfamily ε hε).2.1 qᶜ hqmeas.compl]
      simp [q]
    have hqcompε' : Gamma.measure (w ε') qᶜ = 0 := by
      rw [(hfamily ε' hε').2.1 qᶜ hqmeas.compl]
      simp [q]
    have hqcomp0 : Gamma.measure (w ε - w ε') qᶜ = 0 :=
      aux_lem_truncation_cauchy_sub_measure_zero Gamma hwε hwε' hqmeas.compl
        hqcompε hqcompε'
    have hpartition : q = (Aplus ∪ Aminus) ∪ (B ∪ (Lplus ∪ Lminus)) := by
      ext x
      constructor
      · intro hx
        by_cases hp : ε < vc x
        · exact Or.inl (Or.inl ⟨hx, hp⟩)
        by_cases hm : vc x < -ε
        · exact Or.inl (Or.inr ⟨hx, hm⟩)
        by_cases heq : vc x = ε
        · exact Or.inr (Or.inr (Or.inl ⟨hx, heq⟩))
        by_cases heqm : vc x = -ε
        · exact Or.inr (Or.inr (Or.inr ⟨hx, heqm⟩))
        · have hupper : vc x < ε := lt_of_le_of_ne (le_of_not_gt hp) heq
          have hlower : -ε < vc x :=
            lt_of_le_of_ne (le_of_not_gt hm) (Ne.symm heqm)
          exact Or.inr (Or.inl ⟨hx, (abs_lt).2 ⟨hlower, hupper⟩⟩)
      · intro hx
        rcases hx with (hp | hm) | (hb | (hlp | hlm))
        · exact hp.1
        · exact hm.1
        · exact hb.1
        · exact hlp.1
        · exact hlm.1
    have hdisj_A : Disjoint Aplus Aminus := by
      refine Set.disjoint_left.2 ?_
      intro x hx hy
      have hxp : ε < vc x := by exact hx.2
      have hxm : vc x < -ε := by exact hy.2
      linarith
    have hdisj_L : Disjoint Lplus Lminus := by
      refine Set.disjoint_left.2 ?_
      intro x hx hy
      have hxp : vc x = ε := by exact hx.2
      have hxm : vc x = -ε := by exact hy.2
      linarith
    have hdisj_B : Disjoint B (Lplus ∪ Lminus) := by
      refine Set.disjoint_left.2 ?_
      intro x hx hy
      have hxb : |vc x| < ε := by exact hx.2
      rcases hy with hlp | hlm
      · have hxp : vc x = ε := by exact hlp.2
        linarith [abs_lt.mp hxb]
      · have hxm : vc x = -ε := by exact hlm.2
        linarith [abs_lt.mp hxb]
    have hdisj_left : Disjoint (Aplus ∪ Aminus) (B ∪ (Lplus ∪ Lminus)) := by
      refine Set.disjoint_left.2 ?_
      intro x hx hy
      rcases hx with hp | hm
      · rcases hy with hb | (hlp | hlm)
        · have hxp : ε < vc x := by exact hp.2
          have hxb : |vc x| < ε := by exact hb.2
          linarith [abs_lt.mp hxb]
        · have hxp : ε < vc x := by exact hp.2
          have hxl : vc x = ε := by exact hlp.2
          linarith
        · have hxp : ε < vc x := by exact hp.2
          have hxl : vc x = -ε := by exact hlm.2
          linarith
      · rcases hy with hb | (hlp | hlm)
        · have hxm : vc x < -ε := by exact hm.2
          have hxb : |vc x| < ε := by exact hb.2
          linarith [abs_lt.mp hxb]
        · have hxm : vc x < -ε := by exact hm.2
          have hxl : vc x = ε := by exact hlp.2
          linarith
        · have hxm : vc x < -ε := by exact hm.2
          have hxl : vc x = -ε := by exact hlm.2
          linarith
    have hqmass : Gamma.measure (w ε - w ε') q =
        Gamma.measure (w ε - w ε') Aplus +
          Gamma.measure (w ε - w ε') Aminus +
          Gamma.measure (w ε - w ε') B +
          Gamma.measure (w ε - w ε') Lplus +
          Gamma.measure (w ε - w ε') Lminus := by
      rw [hpartition,
        measure_union hdisj_left
          (hBmeas.union (hLplusmeas.union hLminusmeas)),
        measure_union hdisj_A hAminusmeas,
        measure_union hdisj_B (hLplusmeas.union hLminusmeas),
        measure_union hdisj_L hLminusmeas]
      ring
    have hqmass' : Gamma.measure (w ε - w ε') q =
        Gamma.measure v (q ∩ {x : SpatialCoordinates d |
          ε' < |vc x| ∧ |vc x| < ε}) := by
      rw [hqmass, hplus0, hminus0, hBmass, hLplus0, hLminus0]
      simp
    have huniv : Gamma.measure (w ε - w ε') Set.univ =
        Gamma.measure (w ε - w ε') q := by
      have hdisjcomp : Disjoint q qᶜ := by
        refine Set.disjoint_left.2 ?_
        intro x hx hxcomp
        exact hxcomp hx
      rw [← Set.union_compl_self q,
        measure_union hdisjcomp hqmeas.compl,
        hqcomp0, add_zero]
    have hfirst_result :
        EQ.toClosedForm.form (w ε - w ε') (w ε - w ε') =
          (Gamma.measure v (q ∩ {x : SpatialCoordinates d |
            ε' < |vc x| ∧ |vc x| < ε})).toReal := by
      calc
        EQ.toClosedForm.form (w ε - w ε') (w ε - w ε') =
            (Gamma.measure (w ε - w ε') Set.univ).toReal :=
          (Gamma.measure_univ (w ε - w ε') hdiff).symm
        _ = (Gamma.measure (w ε - w ε') q).toReal := congrArg ENNReal.toReal huniv
        _ = (Gamma.measure v (q ∩ {x : SpatialCoordinates d |
            ε' < |vc x| ∧ |vc x| < ε})).toReal := congrArg ENNReal.toReal hqmass'
    exact hfirst_result
  have hsmall : ∀ δ : ℝ, 0 < δ →
      ∃ ε0 : ℝ, 0 < ε0 ∧
        ∀ ε ε' : ℝ, 0 < ε → ε < ε0 → 0 < ε' → ε' < ε0 →
          EQ.toClosedForm.form (w ε - w ε') (w ε - w ε') < δ := by
    intro δ hδ
    have hev : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
        (Gamma.measure v (s ε)).toReal < δ :=
      (tendsto_order.1 hreal).2 δ hδ
    rcases mem_nhdsWithin.mp hev with ⟨U, hUopen, hU0, hUsub⟩
    rcases Metric.mem_nhds_iff.mp (hUopen.mem_nhds hU0) with
      ⟨ε0, hε0, hball⟩
    refine ⟨ε0, hε0, ?_⟩
    intro ε ε' hε hεlt hε' hε'lt
    have hmeasure : ∀ t : ℝ, 0 < t → t < ε0 →
        (Gamma.measure v (s t)).toReal < δ := by
      intro t ht htlt
      have htU : t ∈ U := hball (by
        simpa [Real.dist_eq, abs_of_pos ht] using htlt)
      exact hUsub ⟨htU, ht⟩
    have hordered : ∀ a b : ℝ, 0 < b → b < a → a < ε0 →
        EQ.toClosedForm.form (w a - w b) (w a - w b) < δ := by
      intro a b hb hba ha
      have hab := hfirst a b hb hba
      rw [hab]
      apply lt_of_le_of_lt
      · apply DirichletForm.EnergyMeasure.toReal_measure_mono Gamma hv
        intro x hx
        change x ∈ q ∩ {x : SpatialCoordinates d |
          b < |vc x| ∧ |vc x| < a} at hx
        change x ∈ s a
        exact ⟨hx.1, lt_trans hb hx.2.1, hx.2.2⟩
      · exact hmeasure a (lt_trans hb hba) ha
    rcases le_total ε' ε with hle | hle
    · rcases lt_or_eq_of_le hle with hlt' | heq'
      · exact hordered ε ε' hε' hlt' hεlt
      · subst ε'
        have hz : EQ.toClosedForm.form (w ε - w ε) (w ε - w ε) = 0 := by
          rw [sub_self]
          exact EQ.toClosedForm.form_zero_left EQ.toClosedForm.domain.zero_mem
        rw [hz]
        exact hδ
    · rcases lt_or_eq_of_le hle with hlt' | heq'
      · have hrev := hordered ε' ε hε hlt' hε'lt
        have heq : w ε - w ε' = -(w ε' - w ε) := by abel
        have hdiffdom : w ε' - w ε ∈ EQ.toClosedForm.domain :=
          EQ.toClosedForm.domain.sub_mem
            (hkilled.le_domain (hfamily ε' hε').1)
            (hkilled.le_domain (hfamily ε hε).1)
        calc
          EQ.toClosedForm.form (w ε - w ε') (w ε - w ε') =
              EQ.toClosedForm.form (-(w ε' - w ε)) (-(w ε' - w ε)) := by rw [heq]
          _ = -EQ.toClosedForm.form (w ε' - w ε) (-(w ε' - w ε)) :=
            EQ.toClosedForm.form_neg_left hdiffdom
              (EQ.toClosedForm.domain.neg_mem hdiffdom)
          _ = -(-EQ.toClosedForm.form (w ε' - w ε) (w ε' - w ε)) := by
            rw [EQ.toClosedForm.form_neg_right hdiffdom hdiffdom]
          _ = EQ.toClosedForm.form (w ε' - w ε) (w ε' - w ε) := by
            ring
          _ < δ := hrev
      · subst ε'
        have hz : EQ.toClosedForm.form (w ε - w ε) (w ε - w ε) = 0 := by
          rw [sub_self]
          exact EQ.toClosedForm.form_zero_left EQ.toClosedForm.domain.zero_mem
        rw [hz]
        exact hδ
  refine ⟨?_, ?_, ?_⟩
  · intro ε ε' hε' hlt
    simpa [q] using hfirst ε ε' hε' hlt
  · simpa [s, q] using hreal
  · intro δ hδ
    simpa [q] using hsmall δ hδ



theorem lem_truncation
    (d : ℕ) (hd : 2 ≤ d)
    (zQ zq : SpatialCoordinates d)
    (R r : ℝ) (hR0 : 0 < R) (hr0 : 0 < r)
    (hqQ : (centeredCube zq r hr0 : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))
    (EQ : _root_.DirichletForm
      (volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure EQ.toClosedForm)
    (hnc : DirichletForm.HasNormalContractions EQ)
    (halg : DirichletForm.IsCoreAlgebra EQ.toClosedForm)
    (hreg : ∃ C : Set (DomainL2 (centeredCube zQ R hR0)),
      DirichletForm.IsCoreOn EQ.toClosedForm
        (centeredCube zQ R hR0 : Set (SpatialCoordinates d)) C)
    (Dq : Submodule ℝ (DomainL2 (centeredCube zQ R hR0)))
    (hkilled : DirichletForm.IsKilledDomain EQ.toClosedForm
      (centeredCube zq r hr0 : Set (SpatialCoordinates d)) Dq)
    (v : DomainL2 (centeredCube zQ R hR0)) (hv : v ∈ EQ.toClosedForm.domain)
    (vc : SpatialCoordinates d → ℝ)
    (hvccont : ContinuousOn vc
      (closure (centeredCube zQ R hR0 : Set (SpatialCoordinates d))))
    (hvrep : (v : SpatialCoordinates d → ℝ)
      =ᵐ[(volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))] vc)
    (hvanish : ∀ x ∈ frontier (centeredCube zq r hr0 : Set (SpatialCoordinates d)),
      vc x = 0)
    (hBH_null : ∀ N : Set ℝ, MeasurableSet N → volume N = 0 →
      Gamma.measure v (vc ⁻¹' N) = 0)
    (hBH_chain : ∀ T : ℝ → ℝ, (∃ K : ℝ≥0, LipschitzWith K T) → T 0 = 0 →
      ∀ Tderiv : ℝ → ℝ, Measurable Tderiv →
      (∀ᵐ s : ℝ, HasDerivAt T (Tderiv s) s) →
      ∀ w : DomainL2 (centeredCube zQ R hR0), w ∈ EQ.toClosedForm.domain →
      ((w : SpatialCoordinates d → ℝ)
        =ᵐ[(volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))]
          fun x => T (vc x)) →
      ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
        (Gamma.measure w B).toReal =
          ∫ x in B, (Tderiv (vc x)) ^ 2 ∂(Gamma.measure v))
    (vq : DomainL2 (centeredCube zQ R hR0))
    (hvq : (vq : SpatialCoordinates d → ℝ)
      =ᵐ[(volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))]
        Set.indicator (closure (centeredCube zq r hr0 : Set (SpatialCoordinates d))) vc) :
    vq ∈ Dq ∧
      EQ.toClosedForm.form vq vq =
        (Gamma.measure v (centeredCube zq r hr0 : Set (SpatialCoordinates d))).toReal ∧
      EQ.toClosedForm.energy vq =
        ((Gamma.measure v (centeredCube zq r hr0 : Set (SpatialCoordinates d))).toReal : EReal) := by
  obtain ⟨w, hfamily⟩ := lem_truncation_family d hd zQ zq R r hR0 hr0 hqQ EQ Gamma
    hnc halg hreg Dq hkilled v hv vc hvccont hvrep hvanish hBH_chain
  have hfamily' : ∀ ε : ℝ, 0 < ε →
      w ε ∈ Dq ∧
      (∀ B : Set (SpatialCoordinates d), MeasurableSet B →
        Gamma.measure (w ε) B =
          Gamma.measure v (B ∩ (centeredCube zq r hr0 : Set (SpatialCoordinates d)) ∩
            {x : SpatialCoordinates d | ε < |vc x|})) ∧
      ((w ε : SpatialCoordinates d → ℝ) =ᵐ[
        (volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))]
        fun x => DirichletForm.truncation ε
          (Set.indicator (closure (centeredCube zq r hr0 : Set (SpatialCoordinates d))) vc x)) := by
    intro ε hε
    exact ⟨(hfamily ε hε).1, (hfamily ε hε).2.1, (hfamily ε hε).2.2.1⟩
  obtain ⟨hannulus, hmass, hsmall⟩ := aux_lem_truncation_cauchy_no_fot d hd zQ zq R r hR0 hr0 hqQ EQ
    Gamma hnc halg hreg Dq hkilled v hv vc hvccont hvrep hvanish hBH_null w hfamily'
  let ε : ℕ → ℝ := fun n => 1 / (n + 1)
  let u : ℕ → DomainL2 (centeredCube zQ R hR0) := fun n => w (ε n)
  have hεpos : ∀ n : ℕ, 0 < ε n := by
    intro n
    dsimp [ε]
    positivity
  have huD : ∀ n : ℕ, u n ∈ Dq := by
    intro n
    exact (hfamily (ε n) (hεpos n)).1
  have hu : ∀ n : ℕ, u n ∈ EQ.toClosedForm.domain := by
    intro n
    exact hkilled.le_domain (huD n)
  have hQmeas : MeasurableSet (centeredCube zQ R hR0 : Set (SpatialCoordinates d)) :=
    (centeredCube zQ R hR0).isOpen.measurableSet
  have hSmeas : MeasurableSet (closure (centeredCube zq r hr0 : Set (SpatialCoordinates d))) :=
    isClosed_closure.measurableSet
  have hSfin : (volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))
      (closure (centeredCube zq r hr0 : Set (SpatialCoordinates d))) ≠ ⊤ := by
    exact measure_ne_top _ _
  have hbound : ∀ n : ℕ, ∀ᵐ x ∂(volume.restrict
      (centeredCube zQ R hR0 : Set (SpatialCoordinates d))),
      ‖((u n - vq : DomainL2 (centeredCube zQ R hR0)) :
        SpatialCoordinates d → ℝ) x‖ ≤
        (Set.indicator (closure (centeredCube zq r hr0 : Set (SpatialCoordinates d)))
          (fun _ => ε n)) x := by
    intro n
    filter_upwards [Lp.coeFn_sub (u n) vq,
      (hfamily (ε n) (hεpos n)).2.2.1,
      (hfamily (ε n) (hεpos n)).2.2.2, hvq] with x hx hrep htr hvqx
    by_cases hxs : x ∈ closure (centeredCube zq r hr0 : Set (SpatialCoordinates d))
    · rw [Set.indicator_of_mem hxs]
      rw [hx, Pi.sub_apply, hvqx, Real.norm_eq_abs]
      simpa [u] using htr
    · have hzero : ((u n : DomainL2 (centeredCube zQ R hR0)) :
          SpatialCoordinates d → ℝ) x = 0 := by
        simpa only [show u n = w (ε n) by rfl, hrep,
          Set.indicator_of_notMem hxs] using (DirichletForm.truncation_zero (ε n))
      have hvzero : (vq : SpatialCoordinates d → ℝ) x = 0 := by
        calc
          (vq : SpatialCoordinates d → ℝ) x =
              (Set.indicator (closure (centeredCube zq r hr0 : Set (SpatialCoordinates d))) vc) x := hvqx
          _ = 0 := Set.indicator_of_notMem hxs vc
      calc
        ‖((u n - vq : DomainL2 (centeredCube zQ R hR0)) :
            SpatialCoordinates d → ℝ) x‖ =
            |(u n : SpatialCoordinates d → ℝ) x - (vq : SpatialCoordinates d → ℝ) x| := by
              simpa only [hx, Pi.sub_apply, Real.norm_eq_abs]
        _ = 0 := by simp [hzero, hvzero]
        _ ≤ (Set.indicator (closure (centeredCube zq r hr0 : Set (SpatialCoordinates d)))
            (fun _ => ε n)) x := by simp [Set.indicator_of_notMem hxs]
  have hnormbound : ∀ n : ℕ,
      ‖u n - vq‖ ≤ ε n * Real.sqrt
        ((volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))
          (closure (centeredCube zq r hr0 : Set (SpatialCoordinates d)))).toReal := by
    intro n
    exact DirichletForm.ClosedForm.norm_le_of_ae_indicator_bound hSmeas hSfin
      (by positivity) (hbound n)
  have hεtend : Tendsto ε atTop (𝓝 0) := by
    simpa [ε, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hnormtend : Tendsto (fun n : ℕ => ‖u n - vq‖) atTop (𝓝 0) := by
    have hupper : Tendsto (fun n : ℕ => ε n * Real.sqrt
        ((volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))
          (closure (centeredCube zq r hr0 : Set (SpatialCoordinates d)))).toReal) atTop
        (𝓝 0) := by
      simpa [ε] using hεtend.mul_const (Real.sqrt
        ((volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))
          (closure (centeredCube zq r hr0 : Set (SpatialCoordinates d)))).toReal)
    exact squeeze_zero (fun n => norm_nonneg _) hnormbound hupper
  have hL2 : Tendsto u atTop (𝓝 vq) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [sub_eq_add_neg, add_comm] using hnormtend
  have hcauchy : ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
        EQ.toClosedForm.form (u p - u q) (u p - u q) < δ := by
    intro δ hδ
    obtain ⟨ε0, hε0, hsmall0⟩ := hsmall δ hδ
    have hev : ∀ᶠ n : ℕ in atTop, ε n < ε0 :=
      hεtend.eventually (Iio_mem_nhds hε0)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨N, ?_⟩
    intro p hp q' hq'
    exact hsmall0 (ε p) (ε q') (hεpos p) (hN p hp) (hεpos q') (hN q' hq')
  obtain ⟨hvqdom, henergyconv⟩ :=
    EQ.toClosedForm.mem_domain_of_tendsto_of_formCauchy u hu vq hL2 hcauchy
  have hvqD : vq ∈ Dq := hkilled.isClosed u vq huD hvqdom henergyconv
  have hformtend : Tendsto (fun n : ℕ => EQ.toClosedForm.form (u n) (u n)) atTop
      (𝓝 (EQ.toClosedForm.form vq vq)) :=
    EQ.toClosedForm.tendsto_form_self_of_tendsto_energyNormSq hu hvqdom henergyconv
  let q : Set (SpatialCoordinates d) :=
    (centeredCube zq r hr0 : Set (SpatialCoordinates d))
  let Q : Set (SpatialCoordinates d) :=
    (centeredCube zQ R hR0 : Set (SpatialCoordinates d))
  have hqopen : IsOpen q := by
    dsimp [q]
    exact (centeredCube zq r hr0).isOpen
  have hQopen : IsOpen Q := by
    dsimp [Q]
    exact (centeredCube zQ R hR0).isOpen
  have hqQ' : q ⊆ Q := by
    exact hqQ
  have hqclQ : q ⊆ closure Q := hqQ'.trans subset_closure
  have hqcont : ContinuousOn vc q := hvccont.mono hqclQ
  have habscont : ContinuousOn (fun x : SpatialCoordinates d => |vc x|) q :=
    hqcont.abs
  have hlevel : ∀ c : ℝ,
      Gamma.measure v (q ∩ {x : SpatialCoordinates d | vc x = c}) = 0 := by
    intro c
    refine measure_mono_null (fun x hx => ?_)
      (hBH_null {c} (measurableSet_singleton c) (by simp))
    exact hx.2
  have hlevelAbs : ∀ t : ℝ,
      Gamma.measure v (q ∩ {x : SpatialCoordinates d | |vc x| = t}) = 0 := by
    intro t
    apply measure_mono_null (t :=
      (q ∩ {x : SpatialCoordinates d | vc x = t}) ∪
        (q ∩ {x : SpatialCoordinates d | vc x = -t}))
    · intro x hx
      by_cases hnonneg : 0 ≤ vc x
      · left
        exact ⟨hx.1, by simpa [abs_of_nonneg hnonneg] using hx.2⟩
      · right
        have hnonpos : vc x ≤ 0 := le_of_not_ge hnonneg
        have hxt : -vc x = t := by simpa [abs_of_nonpos hnonpos] using hx.2
        exact ⟨hx.1, by
          have hxt' := congrArg (fun y : ℝ => -y) hxt
          simpa using hxt'⟩
    · exact measure_union_null (hlevel t) (hlevel (-t))
  let s : ℝ → Set (SpatialCoordinates d) := fun t =>
    q ∩ {x : SpatialCoordinates d | 0 < |vc x| ∧ |vc x| < t}
  let A : ℝ → Set (SpatialCoordinates d) := fun t =>
    q ∩ {x : SpatialCoordinates d | t < |vc x|}
  let N : ℝ → Set (SpatialCoordinates d) := fun t =>
    (q ∩ {x : SpatialCoordinates d | |vc x| = 0}) ∪
      (q ∩ {x : SpatialCoordinates d | |vc x| = t})
  have hseq_measure : ∀ t : ℝ, 0 < t →
      Gamma.measure v (A t) = Gamma.measure v q - Gamma.measure v (s t) := by
    intro t ht
    have hNzero : Gamma.measure v (N t) = 0 := by
      apply measure_union_null
      · exact hlevelAbs 0
      · exact hlevelAbs t
    have hsA : s t ⊆ q \ A t := by
      intro x hx
      refine ⟨hx.1, ?_⟩
      intro hxa
      exact (not_lt_of_ge (le_of_lt hx.2.2)) hxa.2
    have hAcomp : q \ A t ⊆ s t ∪ N t := by
      intro x hx
      have hxq : x ∈ q := hx.1
      have hnot : ¬ t < |vc x| := by
        intro h
        exact hx.2 ⟨hxq, h⟩
      have hle : |vc x| ≤ t := le_of_not_gt hnot
      by_cases hz : |vc x| = 0
      · exact Or.inr (Or.inl ⟨hxq, hz⟩)
      by_cases heq : |vc x| = t
      · exact Or.inr (Or.inr ⟨hxq, heq⟩)
      · left
        exact ⟨hxq, lt_of_le_of_ne (abs_nonneg _) (Ne.symm hz),
          lt_of_le_of_ne hle heq⟩
    have hdiffnull : Gamma.measure v ((s t ∪ N t) \ s t) = 0 := by
      exact measure_mono_null (by
        intro x hx
        rcases hx.1 with hs | hn
        · exact (hx.2 hs).elim
        · exact hn) hNzero
    have hbetween : Gamma.measure v (s t) =
        Gamma.measure v (q \ A t) :=
      measure_eq_measure_smaller_of_between_null_diff hsA hAcomp hdiffnull
    have hAopen : IsOpen (A t) := by
      change IsOpen (q ∩ (fun x : SpatialCoordinates d => |vc x|) ⁻¹' Set.Ioi t)
      exact habscont.isOpen_inter_preimage hqopen isOpen_Ioi
    have hAmeas : MeasurableSet (A t) := hAopen.measurableSet
    have hAq : A t ⊆ q := inter_subset_left
    have hAfinite : Gamma.measure v (A t) ≠ ⊤ := by
      exact ne_top_of_le_ne_top (Gamma.measure_ne_top hv q) (measure_mono hAq)
    have hadd : Gamma.measure v (A t) + Gamma.measure v (s t) =
        Gamma.measure v q := by
      calc
        Gamma.measure v (A t) + Gamma.measure v (s t) =
            Gamma.measure v (A t) + Gamma.measure v (q \ A t) :=
          congrArg (fun x : ℝ≥0∞ => Gamma.measure v (A t) + x) hbetween
        _ = Gamma.measure v (A t ∪ q) :=
          measure_add_diff hAmeas.nullMeasurableSet q
        _ = Gamma.measure v q := by rw [union_eq_self_of_subset_left hAq]
    have hsfinite : Gamma.measure v (s t) ≠ ⊤ := by
      exact ne_top_of_le_ne_top (Gamma.measure_ne_top hv q)
        (measure_mono (inter_subset_left))
    exact ENNReal.eq_sub_of_add_eq hsfinite hadd
  have hmassμ : Tendsto (fun t : ℝ => Gamma.measure v (s t))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    apply (ENNReal.tendsto_toReal_zero_iff
      (hf := fun t => ne_top_of_le_ne_top (Gamma.measure_ne_top hv q)
        (measure_mono (inter_subset_left)))).mp
    simpa [s] using hmass
  have hAμ : Tendsto (fun t : ℝ => Gamma.measure v (A t))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (Gamma.measure v q)) := by
    have hsub : Tendsto (fun t : ℝ => Gamma.measure v q - Gamma.measure v (s t))
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (Gamma.measure v q - 0)) :=
      ENNReal.Tendsto.sub tendsto_const_nhds hmassμ
        (Or.inl (Gamma.measure_ne_top hv q))
    have hsub' : Tendsto (fun t : ℝ => Gamma.measure v q - Gamma.measure v (s t))
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (Gamma.measure v q)) := by
      simpa using hsub
    apply hsub'.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [hseq_measure t ht]
  have hAreal : Tendsto (fun t : ℝ => (Gamma.measure v (A t)).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (Gamma.measure v q).toReal) := by
    exact (ENNReal.continuousAt_toReal (Gamma.measure_ne_top hv q)).tendsto.comp hAμ
  have hεwithin : Tendsto ε atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hεtend, Eventually.of_forall (fun n => hεpos n)⟩
  have hAseq : Tendsto (fun n : ℕ => (Gamma.measure v (A (ε n))).toReal)
      atTop (𝓝 (Gamma.measure v q).toReal) := hAreal.comp hεwithin
  have hformgamma : ∀ n : ℕ,
      EQ.toClosedForm.form (u n) (u n) =
        (Gamma.measure v (A (ε n))).toReal := by
    intro n
    calc
      EQ.toClosedForm.form (u n) (u n) =
          (Gamma.measure (u n) Set.univ).toReal :=
        (Gamma.measure_univ (u n) (hu n)).symm
      _ = (Gamma.measure v
          (Set.univ ∩ (centeredCube zq r hr0 : Set (SpatialCoordinates d)) ∩
            {x : SpatialCoordinates d | ε n < |vc x|})).toReal := by
        apply congrArg ENNReal.toReal
        simpa [u] using
          ((hfamily (ε n) (hεpos n)).2.1 Set.univ MeasurableSet.univ)
      _ = (Gamma.measure v (A (ε n))).toReal := by
        have hset : Set.univ ∩ (centeredCube zq r hr0 : Set (SpatialCoordinates d)) ∩
            {x : SpatialCoordinates d | ε n < |vc x|} = A (ε n) := by
          ext x
          simp [A, q]
        rw [hset]
  have hformgamma_tend : Tendsto
      (fun n : ℕ => EQ.toClosedForm.form (u n) (u n)) atTop
      (𝓝 (Gamma.measure v q).toReal) := by
    apply hAseq.congr'
    exact Eventually.of_forall (fun n => (hformgamma n).symm)
  have hform_eq : EQ.toClosedForm.form vq vq =
      (Gamma.measure v q).toReal :=
    tendsto_nhds_unique hformtend hformgamma_tend
  have henergy_eq : EQ.toClosedForm.energy vq =
      ((Gamma.measure v q).toReal : EReal) := by
    rw [EQ.toClosedForm.energy_of_mem hvqdom, hform_eq]
  refine ⟨hvqD, ?_, ?_⟩
  · simpa [q] using hform_eq
  · simpa [q] using henergy_eq

end Paper
