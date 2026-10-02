import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Lane2.BoundaryPackaging
import SubdiffusiveProcess.Lane2.NativeBridge
import SubdiffusiveProcess.Lane2.ResponseMarkov
import SubdiffusiveProcess.Main.MeasureTrace
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Paper.lem_truncation_cauchy_locality
import SubdiffusiveProcess.Paper.lem_truncation_family
import SubdiffusiveProcess.Paper.obl_BH
import SubdiffusiveProcess.Paper.prop_killed_consistency
import SubdiffusiveProcess.Paper.prop_regularity
import SubdiffusiveProcess.Paper.prop_killed_inverse
import SubdiffusiveProcess.Paper.obl_FOT

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

lemma aux_lem_truncation_cauchy_trunc_pos (ε ε' s : ℝ)
    (hε' : 0 < ε') (hlt : ε' < ε) (hs : ε < s) :
    DirichletForm.truncation ε s - DirichletForm.truncation ε' s = ε' - ε := by
  simp only [DirichletForm.truncation]
  rw [max_eq_left (by linarith), max_eq_right (by linarith),
    max_eq_left (by linarith), max_eq_right (by linarith)]
  ring

lemma aux_lem_truncation_cauchy_trunc_neg (ε ε' s : ℝ)
    (hε' : 0 < ε') (hlt : ε' < ε) (hs : s < -ε) :
    DirichletForm.truncation ε s - DirichletForm.truncation ε' s = ε - ε' := by
  simp only [DirichletForm.truncation]
  rw [max_eq_right (by linarith), max_eq_left (by linarith),
    max_eq_right (by linarith), max_eq_left (by linarith)]
  ring

lemma aux_lem_truncation_cauchy_trunc_small (ε s : ℝ)
    (hs₁ : -ε < s) (hs₂ : s < ε) :
    DirichletForm.truncation ε s = 0 := by
  simp only [DirichletForm.truncation]
  rw [max_eq_right (by linarith), max_eq_right (by linarith)]
  ring

lemma aux_lem_truncation_cauchy_measure_neg
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} {E : _root_.DirichletForm m}
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    {u : Lp ℝ 2 m} (hu : u ∈ E.toClosedForm.domain) :
    Gamma.measure (-u) = Gamma.measure u := by
  have hmain : Gamma.measure ((-1 : ℝ) • u) = Gamma.measure u := by
    ext B hB
    apply (ENNReal.toReal_eq_toReal_iff'
      (Gamma.measure_ne_top (E.toClosedForm.domain.smul_mem (-1) hu) B)
      (Gamma.measure_ne_top hu B)).mp
    have hcross : Gamma.cross ((-1 : ℝ) • u) ((-1 : ℝ) • u) B =
        Gamma.cross u u B := by
      rw [Gamma.cross_smul_left (-1) hu
          (E.toClosedForm.domain.smul_mem (-1) hu),
        Gamma.cross_smul_right (-1) u hu u hu,
        VectorMeasure.smul_apply, VectorMeasure.smul_apply,
        smul_eq_mul, smul_eq_mul]
      ring
    calc
      (Gamma.measure ((-1 : ℝ) • u) B).toReal =
          Gamma.cross ((-1 : ℝ) • u) ((-1 : ℝ) • u) B :=
        (Gamma.cross_self ((-1 : ℝ) • u)
          (E.toClosedForm.domain.smul_mem (-1) hu) B hB).symm
      _ = Gamma.cross u u B := hcross
      _ = (Gamma.measure u B).toReal := Gamma.cross_self u hu B hB
  simpa only [neg_one_smul] using hmain

lemma aux_lem_truncation_cauchy_measure_zero
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} {E : _root_.DirichletForm m}
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm) :
    Gamma.measure 0 = 0 := by
  ext B hB
  apply (ENNReal.toReal_eq_toReal_iff'
    (Gamma.measure_ne_top E.toClosedForm.domain.zero_mem B)
    (by simp)).mp
  have hle := Gamma.toReal_measure_mono E.toClosedForm.domain.zero_mem
    (Set.subset_univ B)
  have htotal := Gamma.measure_univ 0 E.toClosedForm.domain.zero_mem
  rw [E.toClosedForm.form_zero_left E.toClosedForm.domain.zero_mem] at htotal
  exact le_antisymm (hle.trans_eq htotal) ENNReal.toReal_nonneg

lemma aux_lem_truncation_cauchy_sub_measure_zero
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} {E : _root_.DirichletForm m}
    (Gamma : DirichletForm.EnergyMeasure E.toClosedForm)
    {u v : Lp ℝ 2 m} (hu : u ∈ E.toClosedForm.domain)
    (hv : v ∈ E.toClosedForm.domain) {B : Set X} (hB : MeasurableSet B)
    (hu0 : Gamma.measure u B = 0) (hv0 : Gamma.measure v B = 0) :
    Gamma.measure (u - v) B = 0 := by
  have hcross : Gamma.cross u v B = 0 := by
    have hle := Gamma.abs_cross_le u hu v hv B hB
    rw [hu0, hv0, ENNReal.toReal_zero, Real.sqrt_zero, mul_zero] at hle
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  have hval : (Gamma.measure (u - v) B).toReal = 0 := by
    calc
      (Gamma.measure (u - v) B).toReal = Gamma.cross (u - v) (u - v) B :=
        (Gamma.cross_self (u - v) (E.toClosedForm.domain.sub_mem hu hv) B hB).symm
      _ = Gamma.cross u u B - 2 * Gamma.cross u v B + Gamma.cross v v B :=
        Gamma.cross_sub_self_apply hu hv B
      _ = 0 := by
        rw [Gamma.cross_self u hu B hB, Gamma.cross_self v hv B hB,
          hu0, hv0, hcross]
        simp
  rcases (ENNReal.toReal_eq_zero_iff _).mp hval with h | h
  · exact h
  · exact False.elim ((Gamma.measure_ne_top (E.toClosedForm.domain.sub_mem hu hv) B) h)



theorem lem_truncation_cauchy
    (d : ℕ) (hd : 2 ≤ d)
    (zQ zq : SpatialCoordinates d)
    (R r : ℝ) (hR0 : 0 < R) (hr0 : 0 < r)
    (hqQ : (centeredCube zq r hr0 : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))
    (EQ : _root_.DirichletForm
      (volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))))
    (hFOT : obl_FOT EQ)
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
    calc
      EQ.toClosedForm.form (w ε - w ε') (w ε - w ε') =
          (Gamma.measure (w ε - w ε') Set.univ).toReal :=
        (Gamma.measure_univ (w ε - w ε') hdiff).symm
      _ = (Gamma.measure (w ε - w ε') q).toReal := congrArg ENNReal.toReal huniv
      _ = (Gamma.measure v (q ∩ {x : SpatialCoordinates d |
          ε' < |vc x| ∧ |vc x| < ε})).toReal := congrArg ENNReal.toReal hqmass'
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

end Paper
