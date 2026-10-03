module

public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.lem_endpoints_support_2
public import SubdiffusiveProcess.Paper.lem_endpoints_support_3
public import SubdiffusiveProcess.Paper.lem_endpoints_support_4
public import SubdiffusiveProcess.Paper.lem_endpoints_support_5
public import SubdiffusiveProcess.Paper.lem_endpoints_support_6
public import SubdiffusiveProcess.Paper.lem_endpoints_support_7
public import SubdiffusiveProcess.Paper.lem_endpoints_zero_one
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ContDiff
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Paper

theorem aux_lem_endpoints_support_8_endpoint_invariance (d : ℕ) (hd : 2 ≤ d) :
    [NeZero d] →
    (I : Paper.in_J d) →
    (X : Paper.in_extension d hd I) →
    (Sob : Lane4.SobolevFoundationalInput d hd) →
    (Step : Paper.cutoff_good_scale_input d) →
    (MeyersMorrey : Lane4.SmallPerturbationInput d) →
    (Pin : Paper.in_poincare d hd I) →
    (D : Paper.lane4_deterministic_good_scale_input d) →
    (Cp : SubdiffusiveProcess.Lane4.CampanatoInput d) →
    (hES : SubdiffusiveProcess.Lane3.EfronSteinMomentInequality) →
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      DirichletForm.HasBeurlingDenyLocality F.toClosedForm) →
    (BDQ : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      (∃ C, DirichletForm.IsCoreOn F.toClosedForm
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
      DirichletForm.IsStronglyLocalOnCore F.toClosedForm) →
    (EM : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      DirichletForm.HasEnergyMeasure F) →
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u) →
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → BilateralField d →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → BilateralField d →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ),
        in_joint_extracted_candidates d model H (BilateralField d)
          (chaosSampleLaw model).toMeasure (fun omega => omega) z r hr Sspace GN GE GF NE NF →
        (hBoundsC : aux_lem_endpoints_support_1_represented_bounds_weak d hd model H
          (BilateralField d) (chaosSampleLaw model).toMeasure (fun omega => omega) z r hr Sspace
          GE GF NE NF) →
        (hdomains : ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ i,
          limitFormDomain (GE i omega) = limitFormDomain (GF i omega)) →
        (∀ S : Finset ℤ,
          ∀ᵐ zz ∂(((chaosSampleLaw model).toMeasure).prod (chaosSampleLaw model).toMeasure),
            sSup (aux_lem_endpoints_lowerSet z r hr GE GF zz.1) =
              sSup (aux_lem_endpoints_lowerSet z r hr GE GF
                (fun j => if j ∈ S then zz.2 j else zz.1 j))) ∧
        (∀ S : Finset ℤ,
          ∀ᵐ zz ∂(((chaosSampleLaw model).toMeasure).prod (chaosSampleLaw model).toMeasure),
            sInf (aux_lem_endpoints_upperSet z r hr GE GF zz.1) =
              sInf (aux_lem_endpoints_upperSet z r hr GE GF
                (fun j => if j ∈ S then zz.2 j else zz.1 j)))  := by
  intro inst I X Sob Step MeyersMorrey Pin D Cp hES BD BDQ EM hcontract
  letI : NeZero d := inst
  refine ⟨1, by norm_num, ?_⟩
  intro _ _ model _hmodel H z r hr Sspace GN GE GF NE NF hJoint hBoundsC hdomains
  classical
  have hside : ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ i,
      (∃ σ : ℕ → ℕ, StrictMono σ ∧
        Nonempty (aux_lem_endpoints_support_6_limit_side d hd model H omega (z i) (r i) (hr i)
          (Sspace i) (GE i omega) (NE ∘ σ))) ∧
      (∃ σ : ℕ → ℕ, StrictMono σ ∧
        Nonempty (aux_lem_endpoints_support_6_limit_side d hd model H omega (z i) (r i) (hr i)
          (Sspace i) (GF i omega) (NF ∘ σ))) := by
    filter_upwards [hBoundsC, hJoint.2.2.2.2.2.2.2] with omega hb hc i
    have hSi := hJoint.2.2.2.2.2.1 i
    have hcontract0 := fun n => hcontract (z i) (r i) (hr i) (Sspace i) hSi
      (Lane4.cutoffPositiveCoefficient model H omega n (z i) (hr i))
    obtain ⟨σE, hσE, hbE⟩ := (hb i).1
    obtain ⟨σF, hσF, hbF⟩ := (hb i).2
    exact ⟨⟨σE, hσE, lem_endpoints_support_7 hd model H omega (z i) (r i) (hr i)
      (Sspace i) hSi hcontract0 (GE i omega) (NE ∘ σE) (fun n => GN i (NE (σE n)) omega)
      (fun n f => hJoint.2.2.2.2.2.2.1 i (NE (σE n)) omega f)
      ((hc i).1.comp hσE.tendsto_atTop) hbE BD BDQ EM⟩,
      ⟨σF, hσF, lem_endpoints_support_7 hd model H omega (z i) (r i) (hr i)
      (Sspace i) hSi hcontract0 (GF i omega) (NF ∘ σF) (fun n => GN i (NF (σF n)) omega)
      (fun n f => hJoint.2.2.2.2.2.2.1 i (NF (σF n)) omega f)
      ((hc i).2.comp hσF.tendsto_atTop) hbF BD BDQ EM⟩⟩
  exact aux_lem_endpoints_support_7_endpoint_invariance_with_sides d hd model H z r hr Sspace
    GN GE GF NE NF hJoint hside hdomains

end Paper

section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators
namespace Paper



-- (HI : InfraredCharacterization model H) after H (nitro-7b approved, aux-internal); aux_thm_prop_det passes hJoint.2.2.2.1.

theorem lem_endpoints_support_8 (d : ℕ) (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ),
        (hJoint :
          in_joint_extracted_candidates d model H Ω P field z r hr Sspace GN GE GF NE NF) →
        ∀ C0 : ℝ, 1 ≤ C0 →
        (∀ᵐ omega ∂P, aux_lem_endpoints_compare z r hr GE GF C0 omega) →
        (∀ᵐ omega ∂P, aux_lem_endpoints_nonzero z r hr GE omega) →
        ∀ (GNc : (i : ℕ) → ℕ → BilateralField d →
            DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
              DomainL2 (centeredCube (z i) (r i) (hr i))),
          (∀ i N x f, GNc i N x f =
            (responseSolution (Sspace i)
              (Lane4.cutoffPositiveCoefficient model H x N (z i) (hr i))
              ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)).val.1) →
          (∀ i N (f : DomainL2 (centeredCube (z i) (r i) (hr i))),
            StronglyMeasurable (fun x : BilateralField d => GNc i N x f)) →
          (∀ (GEc GFc : (i : ℕ) → BilateralField d →
              DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
                DomainL2 (centeredCube (z i) (r i) (hr i))),
            in_joint_extracted_candidates d model H (BilateralField d)
              (chaosSampleLaw model).toMeasure (fun omega => omega) z r hr Sspace GNc GEc GFc
              NE NF →
            (∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ i,
              limitFormDomain (GEc i omega) = limitFormDomain (GFc i omega)) →
            (∀ S : Finset ℤ,
              ∀ᵐ zz ∂(((chaosSampleLaw model).toMeasure).prod (chaosSampleLaw model).toMeasure),
                sSup (aux_lem_endpoints_lowerSet z r hr GEc GFc zz.1) =
                  sSup (aux_lem_endpoints_lowerSet z r hr GEc GFc
                    (fun j => if j ∈ S then zz.2 j else zz.1 j))) ∧
            (∀ S : Finset ℤ,
              ∀ᵐ zz ∂(((chaosSampleLaw model).toMeasure).prod (chaosSampleLaw model).toMeasure),
                sInf (aux_lem_endpoints_upperSet z r hr GEc GFc zz.1) =
                  sInf (aux_lem_endpoints_upperSet z r hr GEc GFc
                    (fun j => if j ∈ S then zz.2 j else zz.1 j)))) →
          ∃ cL cU : ℝ, ∀ᵐ omega ∂P,
            sSup (aux_lem_endpoints_lowerSet z r hr GE GF omega) = cL ∧
              sInf (aux_lem_endpoints_upperSet z r hr GE GF omega) = cU := by
  obtain ⟨delta0, hdelta0, hEnd⟩ := lem_endpoints_zero_one d hd
  refine ⟨delta0, hdelta0, ?_⟩
  intro _ _ model hmodel H Ω _ P field z r hr Sspace GN GE GF NE NF hJoint
    C0 hC0 hcomp hnz GNc hGNc hGNcm hinv
  have hcan := lem_endpoints_support_5 d model H Ω P field z r hr Sspace GN GE GF NE NF hJoint
    GNc hGNc hGNcm
  rcases hcan with ⟨GEc, GFc, hcanon, hEm, hFm, hae⟩
  have hfield : Measurable field := hJoint.2.1
  have hmap : Measure.map field P = (chaosSampleLaw model).toMeasure := hJoint.2.2.1
  have hsn := aux_lem_endpoints_support_3_candidates_symm_nonneg d model H Ω P field z r hr Sspace GN GE GF NE NF
    hJoint
  have hgoodP : ∀ᵐ omega ∂P, aux_lem_endpoints_support_4_goodSeq z r hr GEc GFc C0 (field omega) := by
    filter_upwards [hae, hcomp, hnz, hsn] with omega homega hc hn hs
    have hup := lem_endpoints_support_4 z r hr GE GF omega (fun i => (hs i).1.1)
      (fun i => (hs i).1.2) (fun i => (hs i).2.1) (fun i => (hs i).2.2) C0 hC0 hc
    have hgood : aux_lem_endpoints_support_4_goodSeq z r hr GE GF C0 omega :=
      ⟨fun i k l => ⟨(hs i).1.1 _ _, (hs i).2.1 _ _⟩, fun i k => ⟨(hs i).1.2 _, (hs i).2.2 _⟩,
        hup.1, hup.2,
        aux_lem_endpoints_support_5_nonzero_seq z r hr GE omega (fun i => (hs i).1.1) (fun i => (hs i).1.2) hn⟩
    exact ((aux_lem_endpoints_support_6_goodSeq_congr z r hr GE GF GEc GFc C0 omega (field omega) homega).1).1 hgood
  have hgoodμ : ∀ᵐ x ∂(chaosSampleLaw model).toMeasure, aux_lem_endpoints_support_4_goodSeq z r hr GEc GFc C0 x :=
    aux_lem_endpoints_support_4_ae_mem_of_map P _ field hfield hmap _
      (aux_lem_endpoints_support_5_goodSeq_measurableSet z r hr GEc GFc hEm hFm C0) hgoodP
  have hL := aux_lem_endpoints_support_5_ct_lower_regular z r hr _ GEc GFc hEm hFm C0 hC0 hgoodμ
  have hU := aux_lem_endpoints_support_5_ct_upper_regular z r hr _ GEc GFc hEm hFm C0 hC0 hgoodμ
  have hdomains : ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ i,
      limitFormDomain (GEc i omega) = limitFormDomain (GFc i omega) := by
    filter_upwards [hgoodμ] with omega hgood i
    exact (aux_lem_endpoints_support_7_goodSeq_compare z r hr GEc GFc C0 hC0 omega hgood i).1
  have hinv' := hinv GEc GFc hcanon hdomains
  
  -- `in_joint_extracted_candidates` binder (nor the `H, Sspace, GN, NE, NF` it alone needed);
  -- the call site is patched to the new, strictly weaker-hypothesis signature only.
  have hμ := hEnd model hmodel z r hr GEc GFc hL.1 hU.1 C0 hL.2 hU.2
    hinv'.1 hinv'.2
  rcases hμ with ⟨cL, cU, hμ⟩
  refine ⟨cL, cU, ?_⟩
  have hPull : ∀ᵐ omega ∂P,
      sSup (aux_lem_endpoints_lowerSet z r hr GEc GFc (field omega)) = cL ∧
        sInf (aux_lem_endpoints_upperSet z r hr GEc GFc (field omega)) = cU := by
    rw [← hmap] at hμ
    exact ae_of_ae_map hfield.aemeasurable hμ
  filter_upwards [hPull, hae] with omega h1 h2
  have hc := aux_lem_endpoints_support_6_goodSeq_congr z r hr GE GF GEc GFc C0 omega (field omega) h2
  rw [hc.2.1, hc.2.2]
  exact h1

end Paper
end
