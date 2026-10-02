import SubdiffusiveProcess.Lane3.BandFiltration
import SubdiffusiveProcess.Main.CutoffCoefficient
import Homogenization.Sobolev.H1.BasicLemmas
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Lane4.CubeDilation
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Lane2.ExternalInputs
import SubdiffusiveProcess.Sobolev.DirichletResponse
import Mathlib.Analysis.Seminorm
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic
import Mathlib
import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
import SubdiffusiveProcess.Sobolev.DomainPoincare
import SubdiffusiveProcess.Lane4.Bridge
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ScalarFieldPackaging
import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerReduction
import SubdiffusiveProcess.Probability.ConditionalPullback
import SubdiffusiveProcess.Sobolev.AffineData
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Lane3.Interfaces
import SubdiffusiveProcess.Lnorm.BoundaryResponseFamily
import SubdiffusiveProcess.Lnorm.CutoffPotentialProxy
import SubdiffusiveProcess.Lnorm.LayerRegroup

/-! This module establishes RegroupedBoundaryCompactness for the cutoff-response compactness construction;
it does not identify subsequential limits or assert local-normalization convergence. -/

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Metric
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff
noncomputable section

namespace SubdiffusiveProcess.Lnorm

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy hsplit for the cutoff-response compactness construction. -/
theorem proxy_hsplit
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (b : weakSobolevGraph (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : ℕ) :
    ∃ (X : Type) (_ : MetricSpace X) (_ : TopologicalSpace.SeparableSpace X)
      (_ : MeasurableSpace X) (_ : BorelSpace X) (Q : Opens (SpatialCoordinates d))
      (R : SubdiffusiveProcess.Lane3.Response Q)
      (V : ((j : bandSet H) → SubdiffusiveProcess.Lnorm.regroup_Y d j.1) → X)
      (psi : X → SubdiffusiveProcess.Lane3.Potential Q)
      (tail : ℕ → ((j : {j : ℤ // j ∉ bandSet H}) → SubdiffusiveProcess.Lnorm.regroup_Y d j.1) →
        SubdiffusiveProcess.Lane3.Potential Q),
      Measurable V ∧
      LipschitzWith 1 psi ∧
      (∀ N : ℕ, H ≤ N →
        Measurable (fun w : X × ((j : {j : ℤ // j ∉ bandSet H}) → SubdiffusiveProcess.Lnorm.regroup_Y d j.1) =>
          R.eval (psi w.1 + tail N w.2))) ∧
      (∀ N : ℕ, H ≤ N → ∀ omg : (j : ℤ) → SubdiffusiveProcess.Lnorm.regroup_Y d j,
        SubdiffusiveProcess.Lnorm.proxy_Rf z r hr hP b M N omg =
          R.eval (psi (V (fun j => omg j.1)) + tail N (fun j => omg j.1))) := by
  letI mX : MeasurableSpace C(closedCube z r hr, ℝ) := borel _
  haveI bX : BorelSpace C(closedCube z r hr, ℝ) := ⟨rfl⟩
  refine ⟨C(closedCube z r hr, ℝ), inferInstance, inferInstance, mX, bX,
    centeredCube z r hr, SubdiffusiveProcess.Lnorm.lnaff_response (killedResponseSpace hP) b,
    (fun b => SubdiffusiveProcess.Lnorm.proxy_V H b z r hr), compactPotentialLp (closedCube z r hr),
    fun N t => SubdiffusiveProcess.Lnorm.proxy_tail M H N t z r hr,
    SubdiffusiveProcess.Lnorm.proxy_V_measurable H z r hr, SubdiffusiveProcess.Lnorm.proxy_cp_lipschitz z r hr, ?_, ?_⟩
  · intro N _
    have hRfromC : Continuous (fun f : C(closedCube z r hr, ℝ) =>
        (SubdiffusiveProcess.Lnorm.lnaff_response (killedResponseSpace hP) b).eval
          (compactPotentialLp (closedCube z r hr) f)) :=
      (SubdiffusiveProcess.Lnorm.proxy_response_eval_continuous (SubdiffusiveProcess.Lnorm.lnaff_response (killedResponseSpace hP) b)).comp
        (SubdiffusiveProcess.Lnorm.proxy_cp_lipschitz z r hr).continuous
    have hinner : Measurable (fun w : C(closedCube z r hr, ℝ) ×
        ((j : {j : ℤ // j ∉ bandSet H}) → SubdiffusiveProcess.Lnorm.regroup_Y d j.1) =>
        w.1 + SubdiffusiveProcess.Lnorm.proxy_tailContFn M H N w.2 z r hr) :=
      Measurable.add measurable_fst
        ((SubdiffusiveProcess.Lnorm.proxy_tailContFn_measurable M H N z r hr).comp measurable_snd)
    have heq : (fun w : C(closedCube z r hr, ℝ) ×
        ((j : {j : ℤ // j ∉ bandSet H}) → SubdiffusiveProcess.Lnorm.regroup_Y d j.1) =>
        (SubdiffusiveProcess.Lnorm.lnaff_response (killedResponseSpace hP) b).eval
          (compactPotentialLp (closedCube z r hr) w.1 + SubdiffusiveProcess.Lnorm.proxy_tail M H N w.2 z r hr)) =
        (fun f : C(closedCube z r hr, ℝ) => (SubdiffusiveProcess.Lnorm.lnaff_response (killedResponseSpace hP) b).eval
            (compactPotentialLp (closedCube z r hr) f)) ∘
          (fun w => w.1 + SubdiffusiveProcess.Lnorm.proxy_tailContFn M H N w.2 z r hr) := by
      funext w
      show _ = (SubdiffusiveProcess.Lnorm.lnaff_response (killedResponseSpace hP) b).eval
          (compactPotentialLp (closedCube z r hr) (w.1 + SubdiffusiveProcess.Lnorm.proxy_tailContFn M H N w.2 z r hr))
      rw [SubdiffusiveProcess.Lnorm.proxy_tail_eq_compactPotentialLp, ← compactPotentialLp_add]
    rw [heq]
    exact hRfromC.measurable.comp hinner
  · intro N hN omg
    unfold SubdiffusiveProcess.Lnorm.proxy_Rf
    rw [SubdiffusiveProcess.Lnorm.proxy_pot'_split M H N hN omg z r hr]

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy pot' at regroup for the cutoff-response compactness construction. -/
theorem proxy_pot'_at_regroup (Hterm : C(SpatialCoordinates d, ℝ))
    (N : ℕ) (omega : BilateralField d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    compactPotentialLp (closedCube z r hr)
        (SubdiffusiveProcess.Lnorm.proxy_contFn' Hterm N (SubdiffusiveProcess.Lnorm.regroup omega) z r hr M) =
      SubdiffusiveProcess.Lnorm.proxy_pot Hterm M N omega z r hr := by
  unfold SubdiffusiveProcess.Lnorm.proxy_pot
  rw [SubdiffusiveProcess.Lnorm.proxy_contFn'_at_regroup]

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy RD for the cutoff-response compactness construction. -/
def proxy_RD
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (b : weakSobolevGraph (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (omega : BilateralField d) : ℝ :=
  dirichletResponse (killedResponseSpace hP) (cutoffPositiveCoefficient M H omega N z hr) b

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy Rf comp regroup ae eq RD for the cutoff-response compactness construction. -/
theorem proxy_Rf_comp_regroup_ae_eq_RD
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (b : weakSobolevGraph (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (N : ℕ) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      SubdiffusiveProcess.Lnorm.proxy_Rf z r hr hP b M N (SubdiffusiveProcess.Lnorm.regroup omega) =
        SubdiffusiveProcess.Lnorm.proxy_RD z r hr hP b M H N omega := by
  filter_upwards [SubdiffusiveProcess.Lnorm.htilde_eq_H_ae d hH] with omega heq
  unfold SubdiffusiveProcess.Lnorm.proxy_Rf SubdiffusiveProcess.Lnorm.proxy_RD
  rw [SubdiffusiveProcess.Lnorm.lnaff_response_eval]
  have hcoord : SubdiffusiveProcess.Lnorm.regroup omega 0 = (omega 0, fun n : ℕ => omega ((n : ℤ) + 1)) :=
    SubdiffusiveProcess.Lnorm.regroup_apply_zero d omega
  have hHterm : SubdiffusiveProcess.Lnorm.htilde d (SubdiffusiveProcess.Lnorm.regroup omega 0).2 = H omega := by
    rw [hcoord]; exact heq
  rw [show SubdiffusiveProcess.Lnorm.proxy_pot' N (SubdiffusiveProcess.Lnorm.regroup omega) z r hr M =
      compactPotentialLp (closedCube z r hr)
        (SubdiffusiveProcess.Lnorm.proxy_contFn' (SubdiffusiveProcess.Lnorm.htilde d (SubdiffusiveProcess.Lnorm.regroup omega 0).2) N
          (SubdiffusiveProcess.Lnorm.regroup omega) z r hr M) from rfl,
    hHterm, SubdiffusiveProcess.Lnorm.proxy_pot'_at_regroup, ← SubdiffusiveProcess.Lnorm.proxy_pot_eq_coefficient]

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- regroup laws eq map for the cutoff-response compactness construction. -/
theorem regroup_laws_eq_map (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_laws M) =
      Measure.map (SubdiffusiveProcess.Lnorm.regroup (d := d)) (chaosSampleLaw M).toMeasure :=
  (SubdiffusiveProcess.Lnorm.regroup_measurePreserving M).map_eq.symm

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy hmom for the cutoff-response compactness construction. -/
theorem proxy_hmom
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (b : weakSobolevGraph (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (q : ℝ≥0∞) (N : ℕ) (Cmom : ℝ) (hCmom : 0 ≤ Cmom)
    (hRDmem : MemLp (SubdiffusiveProcess.Lnorm.proxy_RD z r hr hP b M H N) q (chaosSampleLaw M).toMeasure)
    (hRDbound : eLpNorm (SubdiffusiveProcess.Lnorm.proxy_RD z r hr hP b M H N) q (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal Cmom) :
    MemLp (SubdiffusiveProcess.Lnorm.proxy_Rf z r hr hP b M N) q (Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_laws M)) ∧
      eLpNorm (SubdiffusiveProcess.Lnorm.proxy_Rf z r hr hP b M N) q
          (Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_laws M)) ≤ ENNReal.ofReal Cmom := by
  have hae := SubdiffusiveProcess.Lnorm.proxy_Rf_comp_regroup_ae_eq_RD z r hr hP b M H hH N
  have hcomp_ae : (SubdiffusiveProcess.Lnorm.proxy_Rf z r hr hP b M N ∘ SubdiffusiveProcess.Lnorm.regroup) =ᵐ[(chaosSampleLaw M).toMeasure]
      SubdiffusiveProcess.Lnorm.proxy_RD z r hr hP b M H N := hae
  have hmem_comp : MemLp (SubdiffusiveProcess.Lnorm.proxy_Rf z r hr hP b M N ∘ SubdiffusiveProcess.Lnorm.regroup) q
      (chaosSampleLaw M).toMeasure := hRDmem.ae_eq hcomp_ae.symm
  rw [SubdiffusiveProcess.Lnorm.regroup_laws_eq_map]
  have hmemRf : MemLp (SubdiffusiveProcess.Lnorm.proxy_Rf z r hr hP b M N) q
      (Measure.map (SubdiffusiveProcess.Lnorm.regroup (d := d)) (chaosSampleLaw M).toMeasure) :=
    (MeasurableEquiv.memLp_map_measure_iff (SubdiffusiveProcess.Lnorm.regroup (d := d))).mpr hmem_comp
  refine ⟨hmemRf, ?_⟩
  rw [eLpNorm_map_measure hmemRf.aestronglyMeasurable
      (SubdiffusiveProcess.Lnorm.regroup (d := d)).measurable.aemeasurable,
    eLpNorm_congr_ae hcomp_ae]
  exact hRDbound

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- regroup bandSigma apply measurable for the cutoff-response compactness construction. -/
theorem regroup_bandSigma_apply_measurable (H : ℕ) (k : ℤ)
    (hk : k ∈ Set.Icc (-(H : ℤ)) (H : ℤ)) :
    Measurable[bandSigma (SubdiffusiveProcess.Lnorm.regroup_Y d) H]
      (fun y : (k' : ℤ) → SubdiffusiveProcess.Lnorm.regroup_Y d k' => y k) := by
  have hle : (SubdiffusiveProcess.Lnorm.regroup_Y_measurableSpace d k).comap
      (fun y : (k' : ℤ) → SubdiffusiveProcess.Lnorm.regroup_Y d k' => y k) ≤
        bandSigma (SubdiffusiveProcess.Lnorm.regroup_Y d) H :=
    le_iSup₂ (f := fun (k' : ℤ) (_ : k' ∈ Set.Icc (-(H : ℤ)) (H : ℤ)) =>
      (SubdiffusiveProcess.Lnorm.regroup_Y_measurableSpace d k').comap
        (fun y : (k'' : ℤ) → SubdiffusiveProcess.Lnorm.regroup_Y d k'' => y k')) k hk
  exact measurable_iff_comap_le.mpr hle

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- regroup bandSigma le for the cutoff-response compactness construction. -/
theorem regroup_bandSigma_le (H : ℕ) :
    bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) H ≤
      (bandSigma (SubdiffusiveProcess.Lnorm.regroup_Y d) H).comap (SubdiffusiveProcess.Lnorm.regroup (d := d)) := by
  refine iSup₂_le (fun j hj => ?_)
  obtain ⟨hj1, hj2⟩ := Set.mem_Icc.mp hj
  have key : ∃ φ : ((k : ℤ) → SubdiffusiveProcess.Lnorm.regroup_Y d k) → C(SpatialCoordinates d, ℝ),
      Measurable[bandSigma (SubdiffusiveProcess.Lnorm.regroup_Y d) H] φ ∧
      ∀ omega : BilateralField d, φ (SubdiffusiveProcess.Lnorm.regroup omega) = omega j := by
    rcases lt_trichotomy j 0 with hneg | hzero | hpos
    ·
      have hnn : (0 : ℤ) ≤ -j - 1 := by omega
      set m : ℕ := (-j - 1).toNat with hm
      have hmcast : ((-j - 1).toNat : ℤ) = -j - 1 := Int.toNat_of_nonneg hnn
      have hjeq : j = -((m : ℤ) + 1) := by rw [hm]; omega
      have hmem : (Int.ofNat (m + 1) : ℤ) ∈ Set.Icc (-(H : ℤ)) (H : ℤ) := by
        rw [Set.mem_Icc]
        simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
        constructor <;> omega
      refine ⟨fun y => SubdiffusiveProcess.Lnorm.proxy_fineCoord y m, SubdiffusiveProcess.Lnorm.regroup_bandSigma_apply_measurable H
        (Int.ofNat (m + 1)) hmem, fun omega => ?_⟩
      show SubdiffusiveProcess.Lnorm.regroup omega ((m : ℤ) + 1) = omega j
      rw [SubdiffusiveProcess.Lnorm.regroup_apply_succ, hjeq]
      congr 1
    ·
      have h0 : (0 : ℤ) ∈ Set.Icc (-(H : ℤ)) (H : ℤ) := by rw [Set.mem_Icc]; omega
      refine ⟨fun y => (y 0).1,
        measurable_fst.comp (SubdiffusiveProcess.Lnorm.regroup_bandSigma_apply_measurable H 0 h0),
        fun omega => ?_⟩
      show (SubdiffusiveProcess.Lnorm.regroup omega 0).1 = omega j
      rw [SubdiffusiveProcess.Lnorm.regroup_apply_zero, hzero]
    ·
      have hnn : (0 : ℤ) ≤ j - 1 := by omega
      set m : ℕ := (j - 1).toNat with hm
      have hmcast : ((j - 1).toNat : ℤ) = j - 1 := Int.toNat_of_nonneg hnn
      have hjeq : j = (m : ℤ) + 1 := by rw [hm]; omega
      have h0 : (0 : ℤ) ∈ Set.Icc (-(H : ℤ)) (H : ℤ) := by rw [Set.mem_Icc]; omega
      refine ⟨fun y => (y 0).2 m,
        (measurable_pi_apply m).comp (measurable_snd.comp
          (SubdiffusiveProcess.Lnorm.regroup_bandSigma_apply_measurable H 0 h0)),
        fun omega => ?_⟩
      show (SubdiffusiveProcess.Lnorm.regroup omega 0).2 m = omega j
      rw [SubdiffusiveProcess.Lnorm.regroup_apply_zero, hjeq]
  obtain ⟨φ, hφmeas, hφeq⟩ := key
  have heq : (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap
      (fun omega : BilateralField d => omega j) =
      ((inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap φ).comap
        (SubdiffusiveProcess.Lnorm.regroup (d := d)) := by
    rw [MeasurableSpace.comap_comp]
    congr 1
    funext omega
    exact (hφeq omega).symm
  rw [heq]
  exact MeasurableSpace.comap_mono (measurable_iff_comap_le.mp hφmeas)

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- condExp contraction for the cutoff-response compactness construction. -/
theorem condExp_contraction {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {m1 m2 : MeasurableSpace Ω} (hm1 : m1 ≤ m0) (hm2 : m2 ≤ m0)
    (hm12 : m1 ≤ m2) {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    eLpNorm (fun x => f x - (μ[f|m2]) x) 2 μ ≤ eLpNorm (fun x => f x - (μ[f|m1]) x) 2 μ := by
  set F2 : Lp ℝ 2 μ := hf.toLp f with hF2def
  set a1 : Lp ℝ 2 μ := (condExpL2 ℝ ℝ hm1 F2 : Lp ℝ 2 μ) with ha1def
  set a2 : Lp ℝ 2 μ := (condExpL2 ℝ ℝ hm2 F2 : Lp ℝ 2 μ) with ha2def
  have hF2eq : (F2 : Ω → ℝ) =ᵐ[μ] f := by rw [hF2def]; exact hf.coeFn_toLp
  have ha1eq : (a1 : Ω → ℝ) =ᵐ[μ] (μ[f|m1]) := by rw [ha1def, hF2def]; exact hf.condExpL2_ae_eq_condExp hm1
  have ha2eq : (a2 : Ω → ℝ) =ᵐ[μ] (μ[f|m2]) := by rw [ha2def, hF2def]; exact hf.condExpL2_ae_eq_condExp hm2
  have ha1meas : AEStronglyMeasurable[m1] (a1 : Ω → ℝ) μ := aestronglyMeasurable_condExpL2 hm1 F2
  have ha2meas : AEStronglyMeasurable[m2] (a2 : Ω → ℝ) μ := aestronglyMeasurable_condExpL2 hm2 F2
  have hsub_meas : AEStronglyMeasurable[m2] ((a2 - a1 : Lp ℝ 2 μ) : Ω → ℝ) μ := by
    refine AEStronglyMeasurable.congr ?_ (Lp.coeFn_sub a2 a1).symm
    exact ha2meas.sub (ha1meas.mono hm12)
  have hinner : (@inner ℝ (Lp ℝ 2 μ) _ F2 (a2 - a1)) = (@inner ℝ (Lp ℝ 2 μ) _ a2 (a2 - a1)) := by
    have h := inner_condExpL2_eq_inner_fun (𝕜 := ℝ) hm2 F2 (a2 - a1) hsub_meas
    rw [← ha2def] at h
    exact h.symm
  have horth : (@inner ℝ (Lp ℝ 2 μ) _ (F2 - a2) (a2 - a1)) = (0 : ℝ) := by
    rw [inner_sub_left, hinner, sub_self]
  have hpyth : ‖(F2 - a1 : Lp ℝ 2 μ)‖ * ‖(F2 - a1 : Lp ℝ 2 μ)‖ =
      ‖(F2 - a2 : Lp ℝ 2 μ)‖ * ‖(F2 - a2 : Lp ℝ 2 μ)‖ +
        ‖(a2 - a1 : Lp ℝ 2 μ)‖ * ‖(a2 - a1 : Lp ℝ 2 μ)‖ := by
    have hsplit : (F2 - a1 : Lp ℝ 2 μ) = (F2 - a2 : Lp ℝ 2 μ) + (a2 - a1 : Lp ℝ 2 μ) := by abel
    rw [hsplit]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  have hle : ‖(F2 - a2 : Lp ℝ 2 μ)‖ ≤ ‖(F2 - a1 : Lp ℝ 2 μ)‖ := by
    nlinarith only [hm1, hm2, hm12, hF2def, ha1def, ha2def, hinner, horth, hpyth, norm_nonneg (F2 - a2 : Lp ℝ 2 μ), norm_nonneg (F2 - a1 : Lp ℝ 2 μ), norm_nonneg (a2 - a1 : Lp ℝ 2 μ), sq_nonneg (‖(a2 - a1 : Lp ℝ 2 μ)‖)]
  have hae1 : (F2 - a1 : Lp ℝ 2 μ) =ᵐ[μ] (fun x => f x - (μ[f|m1]) x) := by
    filter_upwards [Lp.coeFn_sub F2 a1, hF2eq, ha1eq] with x hx hfx hcx
    rw [hx]; simp only [Pi.sub_apply]; rw [hfx, hcx]
  have hae2 : (F2 - a2 : Lp ℝ 2 μ) =ᵐ[μ] (fun x => f x - (μ[f|m2]) x) := by
    filter_upwards [Lp.coeFn_sub F2 a2, hF2eq, ha2eq] with x hx hfx hcx
    rw [hx]; simp only [Pi.sub_apply]; rw [hfx, hcx]
  have hnorm1 : eLpNorm (fun x => f x - (μ[f|m1]) x) 2 μ = ENNReal.ofReal ‖(F2 - a1 : Lp ℝ 2 μ)‖ := by
    rw [← eLpNorm_congr_ae hae1, Lp.norm_def]
    exact (ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)).symm
  have hnorm2 : eLpNorm (fun x => f x - (μ[f|m2]) x) 2 μ = ENNReal.ofReal ‖(F2 - a2 : Lp ℝ 2 μ)‖ := by
    rw [← eLpNorm_congr_ae hae2, Lp.norm_def]
    exact (ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)).symm
  rw [hnorm1, hnorm2]
  exact ENNReal.ofReal_le_ofReal hle

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy hband for the cutoff-response compactness construction. -/
theorem proxy_hband
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (b : weakSobolevGraph (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (Cband aD : ℝ) (Cmom6 : ℝ)
    (hRDmoment6 : ∀ N, MemLp (SubdiffusiveProcess.Lnorm.proxy_RD z r hr hP b M H N) (ENNReal.ofReal 6)
      (chaosSampleLaw M).toMeasure)
    (hRDband : ∀ (h N : ℕ),
      eLpNorm (fun omega => SubdiffusiveProcess.Lnorm.proxy_RD z r hr hP b M H N omega -
          (((chaosSampleLaw M).toMeasure)[SubdiffusiveProcess.Lnorm.proxy_RD z r hr hP b M H N |
            bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) omega)
        (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Cband * M.delta * (3 : ℝ) ^ (-aD * (h : ℝ))))
    (Hd Nd : ℕ) :
    eLpNorm (fun y => SubdiffusiveProcess.Lnorm.proxy_Rf z r hr hP b M Nd y -
        ((Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_laws M))[SubdiffusiveProcess.Lnorm.proxy_Rf z r hr hP b M Nd |
          bandSigma (SubdiffusiveProcess.Lnorm.regroup_Y d) Hd]) y) (ENNReal.ofReal 2)
      (Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_laws M)) ≤
    ENNReal.ofReal (Cband * M.delta * (3 : ℝ) ^ (-aD * (Hd : ℝ))) := by
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
  set Pm := (chaosSampleLaw M).toMeasure with hPmdef
  set laws := Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_laws M) with hlawsdef
  set RD := SubdiffusiveProcess.Lnorm.proxy_RD z r hr hP b M H Nd with hRDdef
  set Rf := SubdiffusiveProcess.Lnorm.proxy_Rf z r hr hP b M Nd with hRfdef
  have hm1 : bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) Hd ≤
      (MeasurableSpace.pi : MeasurableSpace (BilateralField d)) := by
    refine iSup₂_le fun j _ s hs => ?_
    obtain ⟨t, ht, hst⟩ := hs
    exact hst ▸ measurable_pi_apply j ht
  have hm2Y : bandSigma (SubdiffusiveProcess.Lnorm.regroup_Y d) Hd ≤
      (MeasurableSpace.pi : MeasurableSpace ((j : ℤ) → SubdiffusiveProcess.Lnorm.regroup_Y d j)) := by
    refine iSup₂_le fun j _ s hs => ?_
    obtain ⟨t, ht, hst⟩ := hs
    exact hst ▸ measurable_pi_apply j ht
  have hm2 : (bandSigma (SubdiffusiveProcess.Lnorm.regroup_Y d) Hd).comap (SubdiffusiveProcess.Lnorm.regroup (d := d)) ≤
      (MeasurableSpace.pi : MeasurableSpace (BilateralField d)) :=
    le_trans (MeasurableSpace.comap_mono hm2Y)
      (measurable_iff_comap_le.mp (SubdiffusiveProcess.Lnorm.regroup (d := d)).measurable)
  have hm12 : bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) Hd ≤
      (bandSigma (SubdiffusiveProcess.Lnorm.regroup_Y d) Hd).comap (SubdiffusiveProcess.Lnorm.regroup (d := d)) :=
    SubdiffusiveProcess.Lnorm.regroup_bandSigma_le Hd
  have hRDmem2 : MemLp RD 2 Pm := by
    rw [hRDdef, hPmdef]; exact (hRDmoment6 Nd).mono_exponent (by norm_num)
  have hcontraction := SubdiffusiveProcess.Lnorm.condExp_contraction (Ω := BilateralField d) (μ := Pm)
    (m0 := MeasurableSpace.pi) hm1 hm2 hm12 hRDmem2
  have hbandbound := hRDband Hd Nd
  rw [h2] at hcontraction
  have hRHS : eLpNorm (fun x => RD x -
      (Pm[RD|bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) Hd]) x) (ENNReal.ofReal 2) Pm ≤
      ENNReal.ofReal (Cband * M.delta * (3 : ℝ) ^ (-aD * (Hd : ℝ))) := hbandbound
  have hmid := hcontraction.trans hRHS

  have hae : Rf ∘ (SubdiffusiveProcess.Lnorm.regroup (d := d)) =ᵐ[Pm] RD := by
    rw [hRfdef, hRDdef, hPmdef]
    exact SubdiffusiveProcess.Lnorm.proxy_Rf_comp_regroup_ae_eq_RD z r hr hP b M H hH Nd
  have hRDmem6 : MemLp RD (ENNReal.ofReal 6) Pm := by rw [hRDdef, hPmdef]; exact hRDmoment6 Nd
  have hRfmem_comp : MemLp (Rf ∘ (SubdiffusiveProcess.Lnorm.regroup (d := d))) (ENNReal.ofReal 6) Pm :=
    hRDmem6.ae_eq hae.symm
  have hmp : MeasurePreserving (SubdiffusiveProcess.Lnorm.regroup (d := d)) Pm laws := by
    rw [hPmdef, hlawsdef]; exact SubdiffusiveProcess.Lnorm.regroup_measurePreserving M
  have hRfmem : MemLp Rf (ENNReal.ofReal 6) laws := by
    rw [← hmp.map_eq]
    exact (MeasurableEquiv.memLp_map_measure_iff (SubdiffusiveProcess.Lnorm.regroup (d := d))).mpr hRfmem_comp
  have htransport : Integrable Rf laws := hRfmem.integrable (by norm_num)
  have hcep := SubdiffusiveProcess.condExp_comp_measurePreserving hmp
    (bandSigma_le (Y := SubdiffusiveProcess.Lnorm.regroup_Y d) Hd) htransport

  have hcongr1 : Pm[Rf ∘ (SubdiffusiveProcess.Lnorm.regroup (d := d)) |
      (bandSigma (SubdiffusiveProcess.Lnorm.regroup_Y d) Hd).comap (SubdiffusiveProcess.Lnorm.regroup (d := d))] =ᵐ[Pm]
      Pm[RD | (bandSigma (SubdiffusiveProcess.Lnorm.regroup_Y d) Hd).comap (SubdiffusiveProcess.Lnorm.regroup (d := d))] :=
    condExp_congr_ae hae
  have hkey : (laws[Rf | bandSigma (SubdiffusiveProcess.Lnorm.regroup_Y d) Hd]) ∘ (SubdiffusiveProcess.Lnorm.regroup (d := d))
      =ᵐ[Pm] Pm[RD | (bandSigma (SubdiffusiveProcess.Lnorm.regroup_Y d) Hd).comap (SubdiffusiveProcess.Lnorm.regroup (d := d))] :=
    hcep.symm.trans hcongr1
  have hgoal_ae : (fun omega => Rf (SubdiffusiveProcess.Lnorm.regroup omega) -
      (laws[Rf | bandSigma (SubdiffusiveProcess.Lnorm.regroup_Y d) Hd]) (SubdiffusiveProcess.Lnorm.regroup omega))
      =ᵐ[Pm] (fun x => RD x -
        (Pm[RD | (bandSigma (SubdiffusiveProcess.Lnorm.regroup_Y d) Hd).comap (SubdiffusiveProcess.Lnorm.regroup (d := d))]) x) := by
    filter_upwards [hae, hkey] with omega h1 h2
    simp only [Function.comp_apply] at h1 h2
    show Rf (SubdiffusiveProcess.Lnorm.regroup omega) -
      (laws[Rf | bandSigma (SubdiffusiveProcess.Lnorm.regroup_Y d) Hd]) (SubdiffusiveProcess.Lnorm.regroup omega) = _
    rw [h1, h2]
  have hcompeq : eLpNorm (fun y => Rf y -
      (laws[Rf | bandSigma (SubdiffusiveProcess.Lnorm.regroup_Y d) Hd]) y) (ENNReal.ofReal 2) laws =
      eLpNorm (fun omega => Rf (SubdiffusiveProcess.Lnorm.regroup omega) -
        (laws[Rf | bandSigma (SubdiffusiveProcess.Lnorm.regroup_Y d) Hd]) (SubdiffusiveProcess.Lnorm.regroup omega))
        (ENNReal.ofReal 2) Pm := by
    have hgmeas : AEStronglyMeasurable (fun y => Rf y -
        (laws[Rf | bandSigma (SubdiffusiveProcess.Lnorm.regroup_Y d) Hd]) y) laws :=
      hRfmem.aestronglyMeasurable.sub
        (stronglyMeasurable_condExp.aestronglyMeasurable.mono (bandSigma_le Hd))
    exact (eLpNorm_comp_measurePreserving hgmeas hmp).symm
  rw [hcompeq, eLpNorm_congr_ae hgoal_ae]
  exact hmid

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy compact transport for the cutoff-response compactness construction. -/
theorem proxy_compact_transport
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (b : weakSobolevGraph (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]
    (hRDmem : ∀ N, MemLp (SubdiffusiveProcess.Lnorm.proxy_RD z r hr hP b M H N) p (chaosSampleLaw M).toMeasure)
    (hRfmem : ∀ N, MemLp (SubdiffusiveProcess.Lnorm.proxy_Rf z r hr hP b M N) p
      (Measure.infinitePi (SubdiffusiveProcess.Lnorm.regroup_laws M)))
    (hcompact : IsCompact (closure (Set.range (fun N =>
      (hRfmem N).toLp (SubdiffusiveProcess.Lnorm.proxy_Rf z r hr hP b M N))))) :
    IsCompact (closure (Set.range (fun N =>
      (hRDmem N).toLp (SubdiffusiveProcess.Lnorm.proxy_RD z r hr hP b M H N)))) := by
  have hmp := SubdiffusiveProcess.Lnorm.regroup_measurePreserving M
  set pull := Lp.compMeasurePreserving (E := ℝ) (p := p) (SubdiffusiveProcess.Lnorm.regroup (d := d)) hmp
    with pulldef
  have hiso : Isometry pull := Lp.isometry_compMeasurePreserving hmp
  have hrep : (fun N => (hRDmem N).toLp (SubdiffusiveProcess.Lnorm.proxy_RD z r hr hP b M H N)) =
      pull ∘ (fun N => (hRfmem N).toLp (SubdiffusiveProcess.Lnorm.proxy_Rf z r hr hP b M N)) := by
    funext N
    have hae : Filter.EventuallyEq (MeasureTheory.ae (chaosSampleLaw M).toMeasure)
        (SubdiffusiveProcess.Lnorm.proxy_Rf z r hr hP b M N ∘ (SubdiffusiveProcess.Lnorm.regroup (d := d)))
        (SubdiffusiveProcess.Lnorm.proxy_RD z r hr hP b M H N) :=
      SubdiffusiveProcess.Lnorm.proxy_Rf_comp_regroup_ae_eq_RD z r hr hP b M H hH N
    have hstep : pull ((hRfmem N).toLp (SubdiffusiveProcess.Lnorm.proxy_Rf z r hr hP b M N)) =
        ((hRfmem N).comp_measurePreserving hmp).toLp
          (SubdiffusiveProcess.Lnorm.proxy_Rf z r hr hP b M N ∘ (SubdiffusiveProcess.Lnorm.regroup (d := d))) := by
      rw [pulldef]; exact Lp.toLp_compMeasurePreserving (hRfmem N) hmp
    show _ = pull ((hRfmem N).toLp (SubdiffusiveProcess.Lnorm.proxy_Rf z r hr hP b M N))
    rw [hstep]
    apply Lp.ext
    exact ((((hRfmem N).comp_measurePreserving hmp).coeFn_toLp).trans
      (hae.trans (hRDmem N).coeFn_toLp.symm)).symm
  rw [hrep, Set.range_comp pull,
    hiso.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous hiso.continuous]
  exact hcompact.image hiso.continuous

end

end SubdiffusiveProcess.Lnorm
