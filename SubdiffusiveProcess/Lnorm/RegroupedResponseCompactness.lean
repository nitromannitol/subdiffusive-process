module

public import SubdiffusiveProcess.Lnorm.RegroupedBoundaryCompactness

@[expose] public section

/-! The infrared regrouping, band estimates, and compactness transport apply to every
positive potential response. This module assumes the original response bounds and proves no uniqueness. -/

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Metric
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section
namespace SubdiffusiveProcess.Lnorm
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- A positive response evaluated at the total potential on the regrouped environment. -/
def potentialResponseProxy (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (R : Response (centeredCube z r hr)) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (y : (j : ℤ) → regroup_Y d j) : ℝ :=
  R.eval (proxy_pot' N y z r hr M)

/-- A positive response evaluated at the actual original-field cutoff potential. -/
def potentialResponseOriginal (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (R : Response (centeredCube z r hr)) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (omega : BilateralField d) : ℝ :=
  R.eval (proxy_pot (H omega) M N omega z r hr)

/-- Every positive response admits the retained-potential and tail factorization. -/
theorem responseProxy_hsplit
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (R : Response (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : ℕ) :
    ∃ (X : Type) (_ : MetricSpace X) (_ : TopologicalSpace.SeparableSpace X)
      (_ : MeasurableSpace X) (_ : BorelSpace X) (Q : Opens (SpatialCoordinates d))
      (R' : SubdiffusiveProcess.Lane3.Response Q)
      (V : ((j : bandSet H) → regroup_Y d j.1) → X)
      (psi : X → SubdiffusiveProcess.Lane3.Potential Q)
      (tail : ℕ → ((j : {j : ℤ // j ∉ bandSet H}) → regroup_Y d j.1) →
        SubdiffusiveProcess.Lane3.Potential Q),
      Measurable V ∧
      LipschitzWith 1 psi ∧
      (∀ N : ℕ, H ≤ N →
        Measurable (fun w : X × ((j : {j : ℤ // j ∉ bandSet H}) → regroup_Y d j.1) =>
          R'.eval (psi w.1 + tail N w.2))) ∧
      (∀ N : ℕ, H ≤ N → ∀ omg : (j : ℤ) → regroup_Y d j,
        potentialResponseProxy z r hr R M N omg =
          R'.eval (psi (V (fun j => omg j.1)) + tail N (fun j => omg j.1))) := by
  letI mX : MeasurableSpace C(closedCube z r hr, ℝ) := borel _
  haveI bX : BorelSpace C(closedCube z r hr, ℝ) := ⟨rfl⟩
  refine ⟨C(closedCube z r hr, ℝ), inferInstance, inferInstance, mX, bX,
    centeredCube z r hr, R,
    (fun b => proxy_V H b z r hr), compactPotentialLp (closedCube z r hr),
    fun N t => proxy_tail M H N t z r hr,
    proxy_V_measurable H z r hr, proxy_cp_lipschitz z r hr, ?_, ?_⟩
  · intro N _
    have hRfromC : Continuous (fun f : C(closedCube z r hr, ℝ) =>
        (R).eval
          (compactPotentialLp (closedCube z r hr) f)) :=
      (proxy_response_eval_continuous (R)).comp
        (proxy_cp_lipschitz z r hr).continuous
    have hinner : Measurable (fun w : C(closedCube z r hr, ℝ) ×
        ((j : {j : ℤ // j ∉ bandSet H}) → regroup_Y d j.1) =>
        w.1 + proxy_tailContFn M H N w.2 z r hr) :=
      Measurable.add measurable_fst
        ((proxy_tailContFn_measurable M H N z r hr).comp measurable_snd)
    have heq : (fun w : C(closedCube z r hr, ℝ) ×
        ((j : {j : ℤ // j ∉ bandSet H}) → regroup_Y d j.1) =>
        (R).eval
          (compactPotentialLp (closedCube z r hr) w.1 + proxy_tail M H N w.2 z r hr)) =
        (fun f : C(closedCube z r hr, ℝ) => (R).eval
            (compactPotentialLp (closedCube z r hr) f)) ∘
          (fun w => w.1 + proxy_tailContFn M H N w.2 z r hr) := by
      funext w
      show _ = (R).eval
          (compactPotentialLp (closedCube z r hr) (w.1 + proxy_tailContFn M H N w.2 z r hr))
      rw [proxy_tail_eq_compactPotentialLp, ← compactPotentialLp_add]
    rw [heq]
    exact hRfromC.measurable.comp hinner
  · intro N hN omg
    unfold potentialResponseProxy
    rw [proxy_pot'_split M H N hN omg z r hr]

/-- The regrouped positive response equals its original-field response almost everywhere. -/
theorem responseProxy_pullback
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (R : Response (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (N : ℕ) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      potentialResponseProxy z r hr R M N (regroup omega) =
        potentialResponseOriginal z r hr R M H N omega := by
  filter_upwards [htilde_eq_H_ae d hH] with omega heq
  unfold potentialResponseProxy potentialResponseOriginal
  have hcoord : regroup omega 0 = (omega 0, fun n : ℕ => omega ((n : ℤ) + 1)) :=
    regroup_apply_zero d omega
  have hHterm : htilde d (regroup omega 0).2 = H omega := by
    rw [hcoord]; exact heq
  rw [show proxy_pot' N (regroup omega) z r hr M =
      compactPotentialLp (closedCube z r hr)
        (proxy_contFn' (htilde d (regroup omega 0).2) N
          (regroup omega) z r hr M) from rfl,
    hHterm, proxy_pot'_at_regroup]

/-- Measure-preserving regrouping preserves the actual response moment bound. -/
theorem responseProxy_moments
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (R : Response (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (q : ℝ≥0∞) (N : ℕ) (Cmom : ℝ) (hCmom : 0 ≤ Cmom)
    (hRDmem : MemLp (potentialResponseOriginal z r hr R M H N) q (chaosSampleLaw M).toMeasure)
    (hRDbound : eLpNorm (potentialResponseOriginal z r hr R M H N) q (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal Cmom) :
    MemLp (potentialResponseProxy z r hr R M N) q (Measure.infinitePi (regroup_laws M)) ∧
      eLpNorm (potentialResponseProxy z r hr R M N) q
          (Measure.infinitePi (regroup_laws M)) ≤ ENNReal.ofReal Cmom := by
  have hae := responseProxy_pullback z r hr R M H hH N
  have hcomp_ae : (potentialResponseProxy z r hr R M N ∘ regroup) =ᵐ[(chaosSampleLaw M).toMeasure]
      potentialResponseOriginal z r hr R M H N := hae
  have hmem_comp : MemLp (potentialResponseProxy z r hr R M N ∘ regroup) q
      (chaosSampleLaw M).toMeasure := hRDmem.ae_eq hcomp_ae.symm
  rw [regroup_laws_eq_map]
  have hmemRf : MemLp (potentialResponseProxy z r hr R M N) q
      (Measure.map (regroup (d := d)) (chaosSampleLaw M).toMeasure) :=
    (MeasurableEquiv.memLp_map_measure_iff (regroup (d := d))).mpr hmem_comp
  refine ⟨hmemRf, ?_⟩
  rw [eLpNorm_map_measure hmemRf.aestronglyMeasurable
      (regroup (d := d)).measurable.aemeasurable,
    eLpNorm_congr_ae hcomp_ae]
  exact hRDbound

/-- Enlarging the retained band transfers its approximation bound to the regrouped response. -/
theorem responseProxy_band
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (R : Response (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (Cband aD : ℝ) (Cmom6 : ℝ)
    (hRDmoment6 : ∀ N, MemLp (potentialResponseOriginal z r hr R M H N) (ENNReal.ofReal 6)
      (chaosSampleLaw M).toMeasure)
    (hRDband : ∀ (h N : ℕ),
      eLpNorm (fun omega => potentialResponseOriginal z r hr R M H N omega -
          (((chaosSampleLaw M).toMeasure)[potentialResponseOriginal z r hr R M H N |
            bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) omega)
        (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Cband * M.delta * (3 : ℝ) ^ (-aD * (h : ℝ))))
    (Hd Nd : ℕ) :
    eLpNorm (fun y => potentialResponseProxy z r hr R M Nd y -
        ((Measure.infinitePi (regroup_laws M))[potentialResponseProxy z r hr R M Nd |
          bandSigma (regroup_Y d) Hd]) y) (ENNReal.ofReal 2)
      (Measure.infinitePi (regroup_laws M)) ≤
    ENNReal.ofReal (Cband * M.delta * (3 : ℝ) ^ (-aD * (Hd : ℝ))) := by
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
  set Pm := (chaosSampleLaw M).toMeasure with hPmdef
  set laws := Measure.infinitePi (regroup_laws M) with hlawsdef
  set RD := potentialResponseOriginal z r hr R M H Nd with hRDdef
  set Rf := potentialResponseProxy z r hr R M Nd with hRfdef
  have hm1 : bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) Hd ≤
      (MeasurableSpace.pi : MeasurableSpace (BilateralField d)) := by
    refine iSup₂_le fun j _ s hs => ?_
    obtain ⟨t, ht, hst⟩ := hs
    exact hst ▸ measurable_pi_apply j ht
  have hm2Y : bandSigma (regroup_Y d) Hd ≤
      (MeasurableSpace.pi : MeasurableSpace ((j : ℤ) → regroup_Y d j)) := by
    refine iSup₂_le fun j _ s hs => ?_
    obtain ⟨t, ht, hst⟩ := hs
    exact hst ▸ measurable_pi_apply j ht
  have hm2 : (bandSigma (regroup_Y d) Hd).comap (regroup (d := d)) ≤
      (MeasurableSpace.pi : MeasurableSpace (BilateralField d)) :=
    le_trans (MeasurableSpace.comap_mono hm2Y)
      (measurable_iff_comap_le.mp (regroup (d := d)).measurable)
  have hm12 : bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) Hd ≤
      (bandSigma (regroup_Y d) Hd).comap (regroup (d := d)) :=
    regroup_bandSigma_le Hd
  have hRDmem2 : MemLp RD 2 Pm := by
    rw [hRDdef, hPmdef]; exact (hRDmoment6 Nd).mono_exponent (by norm_num)
  have hcontraction := condExp_contraction (Ω := BilateralField d) (μ := Pm)
    (m0 := MeasurableSpace.pi) hm1 hm2 hm12 hRDmem2
  have hbandbound := hRDband Hd Nd
  rw [h2] at hcontraction
  have hRHS : eLpNorm (fun x => RD x -
      (Pm[RD|bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) Hd]) x) (ENNReal.ofReal 2) Pm ≤
      ENNReal.ofReal (Cband * M.delta * (3 : ℝ) ^ (-aD * (Hd : ℝ))) := hbandbound
  have hmid := hcontraction.trans hRHS

  have hae : Rf ∘ (regroup (d := d)) =ᵐ[Pm] RD := by
    rw [hRfdef, hRDdef, hPmdef]
    exact responseProxy_pullback z r hr R M H hH Nd
  have hRDmem6 : MemLp RD (ENNReal.ofReal 6) Pm := by rw [hRDdef, hPmdef]; exact hRDmoment6 Nd
  have hRfmem_comp : MemLp (Rf ∘ (regroup (d := d))) (ENNReal.ofReal 6) Pm :=
    hRDmem6.ae_eq hae.symm
  have hmp : MeasurePreserving (regroup (d := d)) Pm laws := by
    rw [hPmdef, hlawsdef]; exact regroup_measurePreserving M
  have hRfmem : MemLp Rf (ENNReal.ofReal 6) laws := by
    rw [← hmp.map_eq]
    exact (MeasurableEquiv.memLp_map_measure_iff (regroup (d := d))).mpr hRfmem_comp
  have htransport : Integrable Rf laws := hRfmem.integrable (by norm_num)
  have hcep := SubdiffusiveProcess.condExp_comp_measurePreserving hmp
    (bandSigma_le (Y := regroup_Y d) Hd) htransport

  have hcongr1 : Pm[Rf ∘ (regroup (d := d)) |
      (bandSigma (regroup_Y d) Hd).comap (regroup (d := d))] =ᵐ[Pm]
      Pm[RD | (bandSigma (regroup_Y d) Hd).comap (regroup (d := d))] :=
    condExp_congr_ae hae
  have hkey : (laws[Rf | bandSigma (regroup_Y d) Hd]) ∘ (regroup (d := d))
      =ᵐ[Pm] Pm[RD | (bandSigma (regroup_Y d) Hd).comap (regroup (d := d))] :=
    hcep.symm.trans hcongr1
  have hgoal_ae : (fun omega => Rf (regroup omega) -
      (laws[Rf | bandSigma (regroup_Y d) Hd]) (regroup omega))
      =ᵐ[Pm] (fun x => RD x -
        (Pm[RD | (bandSigma (regroup_Y d) Hd).comap (regroup (d := d))]) x) := by
    filter_upwards [hae, hkey] with omega h1 h2
    simp only [Function.comp_apply] at h1 h2
    show Rf (regroup omega) -
      (laws[Rf | bandSigma (regroup_Y d) Hd]) (regroup omega) = _
    rw [h1, h2]
  have hcompeq : eLpNorm (fun y => Rf y -
      (laws[Rf | bandSigma (regroup_Y d) Hd]) y) (ENNReal.ofReal 2) laws =
      eLpNorm (fun omega => Rf (regroup omega) -
        (laws[Rf | bandSigma (regroup_Y d) Hd]) (regroup omega))
        (ENNReal.ofReal 2) Pm := by
    have hgmeas : AEStronglyMeasurable (fun y => Rf y -
        (laws[Rf | bandSigma (regroup_Y d) Hd]) y) laws :=
      hRfmem.aestronglyMeasurable.sub
        (stronglyMeasurable_condExp.aestronglyMeasurable.mono (bandSigma_le Hd))
    exact (eLpNorm_comp_measurePreserving hgmeas hmp).symm
  rw [hcompeq, eLpNorm_congr_ae hgoal_ae]
  exact hmid

/-- Compact response ranges pull back to the original field by the regrouping isometry. -/
theorem responseProxy_compact_transport
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (R : Response (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]
    (hRDmem : ∀ N, MemLp (potentialResponseOriginal z r hr R M H N) p (chaosSampleLaw M).toMeasure)
    (hRfmem : ∀ N, MemLp (potentialResponseProxy z r hr R M N) p
      (Measure.infinitePi (regroup_laws M)))
    (hcompact : IsCompact (closure (Set.range (fun N =>
      (hRfmem N).toLp (potentialResponseProxy z r hr R M N))))) :
    IsCompact (closure (Set.range (fun N =>
      (hRDmem N).toLp (potentialResponseOriginal z r hr R M H N)))) := by
  have hmp := regroup_measurePreserving M
  set pull := Lp.compMeasurePreserving (E := ℝ) (p := p) (regroup (d := d)) hmp
    with pulldef
  have hiso : Isometry pull := Lp.isometry_compMeasurePreserving hmp
  have hrep : (fun N => (hRDmem N).toLp (potentialResponseOriginal z r hr R M H N)) =
      pull ∘ (fun N => (hRfmem N).toLp (potentialResponseProxy z r hr R M N)) := by
    funext N
    have hae : Filter.EventuallyEq (MeasureTheory.ae (chaosSampleLaw M).toMeasure)
        (potentialResponseProxy z r hr R M N ∘ (regroup (d := d)))
        (potentialResponseOriginal z r hr R M H N) :=
      responseProxy_pullback z r hr R M H hH N
    have hstep : pull ((hRfmem N).toLp (potentialResponseProxy z r hr R M N)) =
        ((hRfmem N).comp_measurePreserving hmp).toLp
          (potentialResponseProxy z r hr R M N ∘ (regroup (d := d))) := by
      rw [pulldef]; exact Lp.toLp_compMeasurePreserving (hRfmem N) hmp
    show _ = pull ((hRfmem N).toLp (potentialResponseProxy z r hr R M N))
    rw [hstep]
    apply Lp.ext
    exact ((((hRfmem N).comp_measurePreserving hmp).coeFn_toLp).trans
      (hae.trans (hRDmem N).coeFn_toLp.symm)).symm
  rw [hrep, Set.range_comp pull,
    hiso.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous hiso.continuous]
  exact hcompact.image hiso.continuous

end SubdiffusiveProcess.Lnorm
