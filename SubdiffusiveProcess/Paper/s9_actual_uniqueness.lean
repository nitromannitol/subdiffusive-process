import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Paper.cutoff_good_scale_input
import SubdiffusiveProcess.Paper.sum_errors_baseline_input
import SubdiffusiveProcess.Lane2.ExternalInputs
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.DirichletForm.Regular
import SubdiffusiveProcess.Lane3.Interfaces
import SubdiffusiveProcess.Sobolev.VolumeResponseOperator
import SubdiffusiveProcess.Paper.thm_prop_env
import SubdiffusiveProcess.Paper.thm_c1_actual_candidates
import SubdiffusiveProcess.Paper.inputs_EM_witness
import SubdiffusiveProcess.Paper.conv_represented_limit_identification
import SubdiffusiveProcess.Paper.conv_represented_model_operators
import SubdiffusiveProcess.Lnorm.CutoffVolumeResponseMeasurability
import SubdiffusiveProcess.Sobolev.CountableSmoothSources
import SubdiffusiveProcess.Sobolev.LimitFormUniqueness

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- **Identification of a represented limit** (helper of `s9_actual_uniqueness`): on a package whose
environments `env n` and limit field `field` are measure preserving for the chaos law, if the cutoff
inverse operators evaluated at `(env n ω, N n)` converge to `G ω` and the original cutoff operators
converge almost surely to `G0`, then `G ω = G0 (field ω)` almost surely. -/
theorem aux_s9_actual_uniqueness_identify
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (Dop : Set (DomainL2 (centeredCube z r hr))) (hDc : Dop.Countable) (hDd : Dense Dop)
    (hDadd : ∀ x ∈ Dop, ∀ y ∈ Dop, x + y ∈ Dop)
    (N : ℕ → ℕ)
    {Ωh : Type} [MeasurableSpace Ωh] (Ph : Measure Ωh) [IsProbabilityMeasure Ph]
    (field : Ωh → BilateralField d) (env : ℕ → Ωh → BilateralField d)
    (GN : ℕ → Ωh → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : Ωh → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G0 : BilateralField d → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hmpLim : MeasurePreserving field Ph (chaosSampleLaw M).toMeasure)
    (hmp : ∀ n, MeasurePreserving (env n) Ph (chaosSampleLaw M).toMeasure)
    (henvc : ∀ᵐ ω ∂Ph, Tendsto (fun n => env n ω) atTop (𝓝 (field ω)))
    (hGNd : ∀ᵐ ω ∂Ph, ∀ n f, GN n ω f =
      (responseSolution S (Lane4.cutoffPositiveCoefficient M H (env n ω) (N n) z hr)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hGNc : ∀ᵐ ω ∂Ph, Tendsto (fun n => GN n ω) atTop (𝓝 (G ω)))
    (hlim : ∀ᵐ β ∂(chaosSampleLaw M).toMeasure,
      Tendsto (fun n => volumeResponseOperator S
        (Lane4.cutoffPositiveCoefficient M H β (N n) z hr)) atTop (𝓝 (G0 β))) :
    ∀ᵐ ω ∂Ph, G ω = G0 (field ω) := by
  classical
  haveI : PolishSpace (BilateralField d) := aux_conv_represented_model_operators_polish d
  let P0 : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  have hΦmeas : ∀ n, StronglyMeasurable (fun β => volumeResponseOperator S
      (Lane4.cutoffPositiveCoefficient M H β (N n) z hr)) := fun n =>
    stronglyMeasurable_cutoffVolumeResponseOperator M H hH.1 (N n) z r hr S
  have hsym : ∀ n β x y, inner ℝ (volumeResponseOperator S
      (Lane4.cutoffPositiveCoefficient M H β (N n) z hr) x) y =
      inner ℝ x (volumeResponseOperator S
        (Lane4.cutoffPositiveCoefficient M H β (N n) z hr) y) := by
    intro n β x y
    rw [real_inner_comm]
    exact volumeResponseOperator_symm S _ y x
  have hmeas : ∀ n, ∀ x ∈ Dop, Measurable (fun β => inner ℝ x (volumeResponseOperator S
      (Lane4.cutoffPositiveCoefficient M H β (N n) z hr) x)) := by
    intro n x hx
    have hc : Continuous (fun A : DomainL2 (centeredCube z r hr) →L[ℝ]
        DomainL2 (centeredCube z r hr) => inner ℝ x (A x)) :=
      continuous_const.inner ((ContinuousLinearMap.apply ℝ _ x).continuous)
    exact (hc.comp_stronglyMeasurable (hΦmeas n)).measurable
  refine conv_represented_limit_identification P0 Ph
    (fun n β => volumeResponseOperator S (Lane4.cutoffPositiveCoefficient M H β (N n) z hr))
    G0 G id strictMono_id env field hsym Dop hDc hDd hDadd hmeas hmp hmpLim hlim ?_
  filter_upwards [henvc, hGNd, hGNc] with w h1 h2 h3
  refine ⟨h1, ?_⟩
  have hfun : (fun n => volumeResponseOperator S
      (Lane4.cutoffPositiveCoefficient M H (env n w) (N (id n)) z hr)) = fun n => GN n w := by
    funext n
    refine ContinuousLinearMap.ext fun f => ?_
    rw [volumeResponseOperator_apply]
    exact (h2 n f).symm
  rw [hfun]
  exact h3

/-- The limit of symmetric positive operators is symmetric and positive (helper of
`s9_actual_uniqueness`), in the form used by `eq_of_limitFormEnergy_eq`. -/
theorem aux_s9_actual_uniqueness_limit_symm_pos
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr)) (N : ℕ → ℕ)
    (β : BilateralField d)
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hlim : Tendsto (fun n => volumeResponseOperator S
        (Lane4.cutoffPositiveCoefficient M H β (N n) z hr)) atTop (𝓝 G)) :
    (∀ x y, inner ℝ x (G y) = inner ℝ y (G x)) ∧ (∀ x, 0 ≤ inner ℝ x (G x)) := by
  have happ : ∀ w, Tendsto (fun n => volumeResponseOperator S
      (Lane4.cutoffPositiveCoefficient M H β (N n) z hr) w) atTop (𝓝 (G w)) := fun w =>
    ((ContinuousLinearMap.apply ℝ _ w).continuous.tendsto G).comp hlim
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · have h1 : Tendsto (fun n => inner ℝ x (volumeResponseOperator S
        (Lane4.cutoffPositiveCoefficient M H β (N n) z hr) y)) atTop (𝓝 (inner ℝ x (G y))) :=
      tendsto_const_nhds.inner (happ y)
    have h2 : Tendsto (fun n => inner ℝ y (volumeResponseOperator S
        (Lane4.cutoffPositiveCoefficient M H β (N n) z hr) x)) atTop (𝓝 (inner ℝ y (G x))) :=
      tendsto_const_nhds.inner (happ x)
    exact tendsto_nhds_unique h1 (by simpa only [volumeResponseOperator_symm S] using h2)
  · have h1 : Tendsto (fun n => inner ℝ x (volumeResponseOperator S
        (Lane4.cutoffPositiveCoefficient M H β (N n) z hr) x)) atTop (𝓝 (inner ℝ x (G x))) :=
      tendsto_const_nhds.inner (happ x)
    refine ge_of_tendsto h1 (Eventually.of_forall fun n => ?_)
    rw [volumeResponseOperator_apply]
    exact volumeResponse_pairing_nonneg S _ x

/-- Equality of finite-energy domains and of the real parts of the energies on it, for two
positive symmetric operators, gives equality of the operators (helper of `s9_actual_uniqueness`). -/
theorem aux_s9_actual_uniqueness_eq_of_toReal
    {d : ℕ} {Q : TopologicalSpace.Opens (SpatialCoordinates d)}
    (G F : DomainL2 Q →L[ℝ] DomainL2 Q)
    (hGs : ∀ x y, inner ℝ x (G y) = inner ℝ y (G x))
    (hGp : ∀ x, 0 ≤ inner ℝ x (G x))
    (hFs : ∀ x y, inner ℝ x (F y) = inner ℝ y (F x))
    (hFp : ∀ x, 0 ≤ inner ℝ x (F x))
    (hd : limitFormDomain G = limitFormDomain F)
    (he : ∀ u ∈ limitFormDomain G,
      (limitFormEnergy F u).toReal = 1 * (limitFormEnergy G u).toReal) : G = F := by
  refine eq_of_limitFormEnergy_eq G F hGs hGp hFs hFp hd fun u hu => ?_
  have huF : u ∈ limitFormDomain F := hd ▸ hu
  have hG1 : limitFormEnergy G u < ⊤ := hu
  have hF1 : limitFormEnergy F u < ⊤ := huF
  have hG0 : limitFormEnergy G u ≠ ⊥ :=
    ne_bot_of_le_ne_bot (by simp) (limitFormEnergy_nonneg G u)
  have hF0 : limitFormEnergy F u ≠ ⊥ :=
    ne_bot_of_le_ne_bot (by simp) (limitFormEnergy_nonneg F u)
  have h := he u hu
  rw [one_mul] at h
  calc limitFormEnergy G u = ((limitFormEnergy G u).toReal : EReal) :=
        (EReal.coe_toReal hG1.ne hG0).symm
    _ = ((limitFormEnergy F u).toReal : EReal) := by rw [h]
    _ = limitFormEnergy F u := EReal.coe_toReal hF1.ne hF0

/-- **Uniqueness of the subsequential limits of the killed inverses for the actual model** (paper
`mfd:thm-c1`, "Identification of the scalar", used in Step 4 of `mfd:prop-uniform-resolvent`): there is a
threshold `δU > 0` such that for every model with `δ ≤ δU` and every countable family of rational triadic
cubes containing all of them, any two strictly increasing cutoff sequences whose killed inverses
converge almost surely in operator norm on every cube have almost surely equal limits.  This is EXACTLY the
hypothesis `hUniq` of `in_killed_inverse_inprob` (same binders, same quantifier order).  Standing inputs:
those of `thm_A` (`EM` is supplied by `inputs_EM_witness`).

Proof: `thm_prop_env` gives `F = c E` on the original space; `thm_c1_actual_candidates` gives a represented
package (along a subsequence) on which `F = c E` forces `c = 1`; the limits of the package are identified
with the original limits at the limit field (`conv_represented_limit_identification`), which moves `F = c E`
to the package; then `c = 1`, the two limit forms have the same domain and energies, and
`eq_of_limitFormEnergy_eq` gives `GE0 = GF0`. -/
theorem s9_actual_uniqueness
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (Jc : Paper.in_J d) (Pc : Paper.in_poincare d hd Jc)
    (Xc : Paper.in_extension d hd Jc)
    (Sf : Lane4.SobolevFoundationalInput d hd)
    (W : Lane4.SmallPerturbationInput d)
    (Cp : Lane4.CampanatoInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : SubdiffusiveProcess.Lane3.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (Interp : CubeFractionalInterpolationInput d hd)
    (BD : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (F : _root_.DirichletForm
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))),
      DirichletForm.HasBeurlingDenyLocality F.toClosedForm)
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
      DirichletForm.IsStronglyLocalOnCore F.toClosedForm)
    (hcontract : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr)),
      S.space = killedSobolevGraph (centeredCube z r hr) →
      ∀ (a : PositiveCoefficient (centeredCube z r hr)) (T : ℝ → ℝ),
        DirichletForm.IsNormalContraction T → ∀ u : S.space, ∃ v : S.space,
          ((v.val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
              (fun x => T (u.val.1 x))) ∧
          responseForm S a v v ≤ responseForm S a u u) :
    ∃ δU : ℝ, 0 < δU ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H),
        M.delta ≤ δU →
      ∀ (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ) (hR : ∀ i, 0 < R i)
        (Sspace : ∀ i, ResponseSpace (centeredCube (Z i) (R i) (hR i)))
        (hS : ∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (Z i) (R i) (hR i)))
        (hrat : ∀ i, (∀ c : Fin d, ∃ q : ℚ, Z i c = (q : ℝ)) ∧ ∃ m : ℤ, R i = (3 : ℝ) ^ m)
        (hcomp : ∀ (z' : SpatialCoordinates d) (r' : ℝ), (∀ c : Fin d, ∃ q : ℚ, z' c = (q : ℝ)) →
          (∃ m : ℤ, r' = (3 : ℝ) ^ m) → ∃ i, Z i = z' ∧ R i = r')
        (NE NF : ℕ → ℕ), StrictMono NE → StrictMono NF →
      ∀ (GE0 GF0 : (i : ℕ) → BilateralField d →
          DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ]
            DomainL2 (centeredCube (Z i) (R i) (hR i))),
        (∀ᵐ β ∂(chaosSampleLaw M).toMeasure, ∀ i,
          Tendsto (fun n => volumeResponseOperator (Sspace i)
            (Lane4.cutoffPositiveCoefficient M H β (NE n) (Z i) (hR i))) atTop
            (𝓝 (GE0 i β))) →
        (∀ᵐ β ∂(chaosSampleLaw M).toMeasure, ∀ i,
          Tendsto (fun n => volumeResponseOperator (Sspace i)
            (Lane4.cutoffPositiveCoefficient M H β (NF n) (Z i) (hR i))) atTop
            (𝓝 (GF0 i β))) →
        ∀ᵐ β ∂(chaosSampleLaw M).toMeasure, ∀ i, GE0 i β = GF0 i β := by
  classical
  haveI hne : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩
  obtain ⟨δp, C0, hδp, hC0, hprop⟩ := thm_prop_env d hd Jc Xc Sf Step W Pc D Cp Interp hES Dbase
    BD BDQ (fun z r hr F => inputs_EM_witness d z r hr F) hcontract
  obtain ⟨δc, hδc, hcal⟩ := thm_c1_actual_candidates d hd Interp Jc Pc Xc W Cp Sf (3 / 4) (1 / 4)
    (5 / 8) ((d : ℝ) - 1 / 2) (by linarith) (by linarith) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨min δp δc, lt_min hδp hδc, ?_⟩
  intro M Rm Sreg It H hH hδ Z R hR Sspace hS hrat hcomp NE NF hNE hNF GE0 GF0 hlimE hlimF
  obtain ⟨c, hc1, hc2, hE⟩ := hprop M Rm Sreg It H hH (hδ.trans (min_le_left _ _)) Z R hR Sspace hS
    hrat hcomp NE NF hNE hNF GE0 GF0 hlimE hlimF
  obtain ⟨seq, hseq, Ωh, mΩh, Ph, hPh, field, env, GNE, GNF, GE, GF, hjoint, -, -, hone⟩ :=
    hcal M Rm Sreg It H hH (hδ.trans (min_le_right _ _)) Z R hR Sspace hS hrat hcomp NE NF hNE hNF
  haveI : IsProbabilityMeasure Ph := hPh
  obtain ⟨-, hfm, hfmap, -, -, -, hMP, henvc, -, hGNd, hGNc⟩ := hjoint.1
  have hmpLim : MeasurePreserving field Ph (chaosSampleLaw M).toMeasure := ⟨hfm, hfmap⟩
  choose Dsub hDc hDd _ using fun i =>
    SubdiffusiveProcess.SmoothSources.exists_countable_dense_smooth_submodule (Z i) (R i) (hR i)
  have hid : ∀ᵐ ω ∂Ph, ∀ i, GE i ω = GE0 i (field ω) ∧ GF i ω = GF0 i (field ω) := by
    rw [ae_all_iff]
    intro i
    have h1 := aux_s9_actual_uniqueness_identify d M H hH (Z i) (R i) (hR i) (Sspace i)
      (Dsub i : Set _) (hDc i) (hDd i) (fun x hx y hy => (Dsub i).add_mem hx hy)
      (fun n => NE (seq n)) Ph field env (fun n ω => GNE i n ω) (fun ω => GE i ω)
      (fun β => GE0 i β) hmpLim (fun n => (hMP n).1)
      (by filter_upwards [henvc] with w h; exact h.1)
      (by filter_upwards [hGNd] with w h n f; exact (h i n f).1)
      (by filter_upwards [hGNc] with w h; exact (h i).1)
      (by filter_upwards [hlimE] with β hβ; exact (hβ i).comp hseq.tendsto_atTop)
    have h2 := aux_s9_actual_uniqueness_identify d M H hH (Z i) (R i) (hR i) (Sspace i)
      (Dsub i : Set _) (hDc i) (hDd i) (fun x hx y hy => (Dsub i).add_mem hx hy)
      (fun n => NF (seq n)) Ph field env (fun n ω => GNF i n ω) (fun ω => GF i ω)
      (fun β => GF0 i β) hmpLim (fun n => (hMP n).2)
      (by filter_upwards [henvc] with w h; exact h.2)
      (by filter_upwards [hGNd] with w h n f; exact (h i n f).2)
      (by filter_upwards [hGNc] with w h; exact (h i).2)
      (by filter_upwards [hlimF] with β hβ; exact (hβ i).comp hseq.tendsto_atTop)
    filter_upwards [h1, h2] with ω a b
    exact ⟨a, b⟩
  have hΩ : ∀ᵐ ω ∂Ph, ∀ i, limitFormDomain (GE i ω) = limitFormDomain (GF i ω) ∧
      ∀ u : DomainL2 (centeredCube (Z i) (R i) (hR i)), u ∈ limitFormDomain (GE i ω) →
        (limitFormEnergy (GF i ω) u).toReal = c * (limitFormEnergy (GE i ω) u).toReal := by
    have hE' := hmpLim.quasiMeasurePreserving.ae hE
    filter_upwards [hE', hid] with ω h1 h2 i
    rw [(h2 i).1, (h2 i).2]
    exact h1 i
  have hcpos : 0 < c := lt_of_lt_of_le (inv_pos.2 (lt_of_lt_of_le one_pos hC0)) hc1
  have hc : c = 1 := hone c hcpos hΩ
  subst hc
  filter_upwards [hE, hlimE, hlimF] with β hβ hlE hlF i
  obtain ⟨hdom, hen⟩ := hβ i
  obtain ⟨hEs, hEp⟩ := aux_s9_actual_uniqueness_limit_symm_pos d M H (Z i) (R i) (hR i) (Sspace i)
    NE β (GE0 i β) (hlE i)
  obtain ⟨hFs, hFp⟩ := aux_s9_actual_uniqueness_limit_symm_pos d M H (Z i) (R i) (hR i) (Sspace i)
    NF β (GF0 i β) (hlF i)
  exact aux_s9_actual_uniqueness_eq_of_toReal _ _ hEs hEp hFs hFp hdom (fun u hu => hen u hu)

end Paper
