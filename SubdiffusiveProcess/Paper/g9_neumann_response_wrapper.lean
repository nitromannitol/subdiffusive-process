import SubdiffusiveProcess.Paper.lem_local_normalizations_regroup
import SubdiffusiveProcess.Paper.prop_response_compact
import SubdiffusiveProcess.Paper.lem_prefix_limit_atom_extraction
import SubdiffusiveProcess.Lane4.Carriers

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal

noncomputable section
namespace Paper

/-! ## Part 1: a `Response`-generic replay of `lem_local_normalizations`'s "regroup" machinery

`lem_local_normalizations` builds `aux_lem_local_normalizations_lnorm_proxy_{Rf,RD,hsplit,hmom,hband,compact_transport}`
hardcoded to the Dirichlet response `aux_lem_local_normalizations_lnaff_response (killedResponseSpace hP) b`.
Every step of that construction past `aux_lem_local_normalizations_lnorm_proxy_pot'`/`_V`/`_tail` (which are
already response-agnostic) only uses the response through `R.eval`'s continuity
(`aux_lem_local_normalizations_lnorm_proxy_response_eval_continuous`, itself already generic in `R`), so the
whole `hsplit`/`hmom`/`hband`/`compact_transport` stack replays verbatim for an ARBITRARY
`R : Response (centeredCube z r hr)`. This section makes that genericity explicit once, so the
Neumann (`inverseResponse`) case below is a direct instantiation rather than a second copy of the
proof text. -/

section AuxG9Generic

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The native (regrouped-`y`-coordinate) response for an arbitrary `R`. -/
def aux_g9_neumann_response_wrapper_generic_Rf (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (R : SubdiffusiveProcess.Lane3.Response (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (y : (j : ℤ) → aux_lem_local_normalizations_lnorm_regroup_Y d j) : ℝ :=
  R.eval (aux_lem_local_normalizations_lnorm_proxy_pot' N y z r hr M)

/-- The true (`H`-based) response for an arbitrary `R`. -/
def aux_g9_neumann_response_wrapper_generic_RTrue (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (R : SubdiffusiveProcess.Lane3.Response (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (omega : BilateralField d) : ℝ :=
  R.eval (aux_lem_local_normalizations_lnorm_proxy_pot (H omega) M N omega z r hr)

/-- `hsplit`, for an arbitrary `R`. Direct replay of
`aux_lem_local_normalizations_lnorm_proxy_hsplit`'s proof with `R` in place of the hardcoded
Dirichlet response. -/
theorem aux_g9_neumann_response_wrapper_generic_hsplit
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (R : SubdiffusiveProcess.Lane3.Response (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : ℕ) :
    ∃ (X : Type) (_ : MetricSpace X) (_ : TopologicalSpace.SeparableSpace X)
      (_ : MeasurableSpace X) (_ : BorelSpace X) (Q : Opens (SpatialCoordinates d))
      (R' : SubdiffusiveProcess.Lane3.Response Q)
      (V : ((j : bandSet H) → aux_lem_local_normalizations_lnorm_regroup_Y d j.1) → X)
      (psi : X → SubdiffusiveProcess.Lane3.Potential Q)
      (tail : ℕ → ((j : {j : ℤ // j ∉ bandSet H}) → aux_lem_local_normalizations_lnorm_regroup_Y d j.1) →
        SubdiffusiveProcess.Lane3.Potential Q),
      Measurable V ∧
      LipschitzWith 1 psi ∧
      (∀ N : ℕ, H ≤ N →
        Measurable (fun w : X × ((j : {j : ℤ // j ∉ bandSet H}) → aux_lem_local_normalizations_lnorm_regroup_Y d j.1) =>
          R'.eval (psi w.1 + tail N w.2))) ∧
      (∀ N : ℕ, H ≤ N → ∀ omg : (j : ℤ) → aux_lem_local_normalizations_lnorm_regroup_Y d j,
        aux_g9_neumann_response_wrapper_generic_Rf z r hr R M N omg =
          R'.eval (psi (V (fun j => omg j.1)) + tail N (fun j => omg j.1))) := by
  letI mX : MeasurableSpace C(closedCube z r hr, ℝ) := borel _
  haveI bX : BorelSpace C(closedCube z r hr, ℝ) := ⟨rfl⟩
  refine ⟨C(closedCube z r hr, ℝ), inferInstance, inferInstance, mX, bX,
    centeredCube z r hr, R,
    (fun b => aux_lem_local_normalizations_lnorm_proxy_V H b z r hr), compactPotentialLp (closedCube z r hr),
    fun N t => aux_lem_local_normalizations_lnorm_proxy_tail M H N t z r hr,
    aux_lem_local_normalizations_lnorm_proxy_V_measurable H z r hr, aux_lem_local_normalizations_lnorm_proxy_cp_lipschitz z r hr, ?_, ?_⟩
  · intro N _
    have hRfromC : Continuous (fun f : C(closedCube z r hr, ℝ) =>
        R.eval (compactPotentialLp (closedCube z r hr) f)) :=
      (aux_lem_local_normalizations_lnorm_proxy_response_eval_continuous R).comp
        (aux_lem_local_normalizations_lnorm_proxy_cp_lipschitz z r hr).continuous
    have hinner : Measurable (fun w : C(closedCube z r hr, ℝ) ×
        ((j : {j : ℤ // j ∉ bandSet H}) → aux_lem_local_normalizations_lnorm_regroup_Y d j.1) =>
        w.1 + aux_lem_local_normalizations_lnorm_proxy_tailContFn M H N w.2 z r hr) :=
      Measurable.add measurable_fst
        ((aux_lem_local_normalizations_lnorm_proxy_tailContFn_measurable M H N z r hr).comp measurable_snd)
    have heq : (fun w : C(closedCube z r hr, ℝ) ×
        ((j : {j : ℤ // j ∉ bandSet H}) → aux_lem_local_normalizations_lnorm_regroup_Y d j.1) =>
        R.eval
          (compactPotentialLp (closedCube z r hr) w.1 + aux_lem_local_normalizations_lnorm_proxy_tail M H N w.2 z r hr)) =
        (fun f : C(closedCube z r hr, ℝ) => R.eval
            (compactPotentialLp (closedCube z r hr) f)) ∘
          (fun w => w.1 + aux_lem_local_normalizations_lnorm_proxy_tailContFn M H N w.2 z r hr) := by
      funext w
      show _ = R.eval
          (compactPotentialLp (closedCube z r hr) (w.1 + aux_lem_local_normalizations_lnorm_proxy_tailContFn M H N w.2 z r hr))
      rw [aux_lem_local_normalizations_lnorm_proxy_tail_eq_compactPotentialLp, ← compactPotentialLp_add]
    rw [heq]
    exact hRfromC.measurable.comp hinner
  · intro N hN omg
    unfold aux_g9_neumann_response_wrapper_generic_Rf
    rw [aux_lem_local_normalizations_lnorm_proxy_pot'_split M H N hN omg z r hr]

/-- The a.e. transport fact, for an arbitrary `R`. -/
theorem aux_g9_neumann_response_wrapper_generic_ae_eq
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (R : SubdiffusiveProcess.Lane3.Response (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (N : ℕ) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      aux_g9_neumann_response_wrapper_generic_Rf z r hr R M N (aux_lem_local_normalizations_lnorm_regroup omega) =
        aux_g9_neumann_response_wrapper_generic_RTrue z r hr R M H N omega := by
  filter_upwards [aux_lem_local_normalizations_lnorm_htilde_eq_H_ae d hH] with omega heq
  unfold aux_g9_neumann_response_wrapper_generic_Rf aux_g9_neumann_response_wrapper_generic_RTrue
  congr 1
  have hcoord := aux_lem_local_normalizations_lnorm_regroup_apply_zero d omega
  have hHterm : aux_lem_local_normalizations_lnorm_htilde d (aux_lem_local_normalizations_lnorm_regroup omega 0).2 = H omega := by
    rw [hcoord]; exact heq
  rw [show aux_lem_local_normalizations_lnorm_proxy_pot' N (aux_lem_local_normalizations_lnorm_regroup omega) z r hr M =
      compactPotentialLp (closedCube z r hr)
        (aux_lem_local_normalizations_lnorm_proxy_contFn' (aux_lem_local_normalizations_lnorm_htilde d (aux_lem_local_normalizations_lnorm_regroup omega 0).2) N
          (aux_lem_local_normalizations_lnorm_regroup omega) z r hr M) from rfl,
    hHterm]
  exact aux_lem_local_normalizations_lnorm_proxy_pot'_at_regroup (H omega) N omega z r hr M

/-- `hmom`, for an arbitrary `R`. -/
theorem aux_g9_neumann_response_wrapper_generic_hmom
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (R : SubdiffusiveProcess.Lane3.Response (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (q : ℝ≥0∞) (N : ℕ) (Cmom : ℝ) (hCmom : 0 ≤ Cmom)
    (hRDmem : MemLp (aux_g9_neumann_response_wrapper_generic_RTrue z r hr R M H N) q (chaosSampleLaw M).toMeasure)
    (hRDbound : eLpNorm (aux_g9_neumann_response_wrapper_generic_RTrue z r hr R M H N) q (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal Cmom) :
    MemLp (aux_g9_neumann_response_wrapper_generic_Rf z r hr R M N) q (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M)) ∧
      eLpNorm (aux_g9_neumann_response_wrapper_generic_Rf z r hr R M N) q
          (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M)) ≤ ENNReal.ofReal Cmom := by
  have hae := aux_g9_neumann_response_wrapper_generic_ae_eq z r hr R M H hH N
  have hcomp_ae : (aux_g9_neumann_response_wrapper_generic_Rf z r hr R M N ∘ aux_lem_local_normalizations_lnorm_regroup) =ᵐ[(chaosSampleLaw M).toMeasure]
      aux_g9_neumann_response_wrapper_generic_RTrue z r hr R M H N := hae
  have hmem_comp : MemLp (aux_g9_neumann_response_wrapper_generic_Rf z r hr R M N ∘ aux_lem_local_normalizations_lnorm_regroup) q
      (chaosSampleLaw M).toMeasure := hRDmem.ae_eq hcomp_ae.symm
  rw [aux_lem_local_normalizations_lnorm_regroup_laws_eq_map]
  have hmemRf : MemLp (aux_g9_neumann_response_wrapper_generic_Rf z r hr R M N) q
      (Measure.map (aux_lem_local_normalizations_lnorm_regroup (d := d)) (chaosSampleLaw M).toMeasure) :=
    (MeasurableEquiv.memLp_map_measure_iff (aux_lem_local_normalizations_lnorm_regroup (d := d))).mpr hmem_comp
  refine ⟨hmemRf, ?_⟩
  rw [eLpNorm_map_measure hmemRf.aestronglyMeasurable
      (aux_lem_local_normalizations_lnorm_regroup (d := d)).measurable.aemeasurable,
    eLpNorm_congr_ae hcomp_ae]
  exact hRDbound

/-- `hband`, for an arbitrary `R`. Direct replay of `aux_lem_local_normalizations_lnorm_proxy_hband`'s proof. -/
theorem aux_g9_neumann_response_wrapper_generic_hband
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (R : SubdiffusiveProcess.Lane3.Response (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (Delta Cband aD : ℝ) (Cmom6 : ℝ)
    (hRDmoment6 : ∀ N, MemLp (aux_g9_neumann_response_wrapper_generic_RTrue z r hr R M H N) (ENNReal.ofReal 6)
      (chaosSampleLaw M).toMeasure)
    (hRDband : ∀ (h N : ℕ),
      eLpNorm (fun omega => aux_g9_neumann_response_wrapper_generic_RTrue z r hr R M H N omega -
          (((chaosSampleLaw M).toMeasure)[aux_g9_neumann_response_wrapper_generic_RTrue z r hr R M H N |
            bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) omega)
        (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Cband * Delta * (3 : ℝ) ^ (-(aD * (h : ℝ)))))
    (Hd Nd : ℕ) :
    eLpNorm (fun y => aux_g9_neumann_response_wrapper_generic_Rf z r hr R M Nd y -
        ((Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M))[aux_g9_neumann_response_wrapper_generic_Rf z r hr R M Nd |
          bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd]) y) (ENNReal.ofReal 2)
      (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M)) ≤
    ENNReal.ofReal (Cband * Delta * (3 : ℝ) ^ (-(aD * (Hd : ℝ)))) := by
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
  set Pm := (chaosSampleLaw M).toMeasure with hPmdef
  set laws := Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M) with hlawsdef
  set RD := aux_g9_neumann_response_wrapper_generic_RTrue z r hr R M H Nd with hRDdef
  set Rf := aux_g9_neumann_response_wrapper_generic_Rf z r hr R M Nd with hRfdef
  have hm1 : bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) Hd ≤
      (MeasurableSpace.pi : MeasurableSpace (BilateralField d)) := by
    refine iSup₂_le fun j _ s hs => ?_
    obtain ⟨t, ht, hst⟩ := hs
    exact hst ▸ measurable_pi_apply j ht
  have hm2Y : bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd ≤
      (MeasurableSpace.pi : MeasurableSpace ((j : ℤ) → aux_lem_local_normalizations_lnorm_regroup_Y d j)) := by
    refine iSup₂_le fun j _ s hs => ?_
    obtain ⟨t, ht, hst⟩ := hs
    exact hst ▸ measurable_pi_apply j ht
  have hm2 : (bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd).comap (aux_lem_local_normalizations_lnorm_regroup (d := d)) ≤
      (MeasurableSpace.pi : MeasurableSpace (BilateralField d)) :=
    le_trans (MeasurableSpace.comap_mono hm2Y)
      (measurable_iff_comap_le.mp (aux_lem_local_normalizations_lnorm_regroup (d := d)).measurable)
  have hm12 : bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) Hd ≤
      (bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd).comap (aux_lem_local_normalizations_lnorm_regroup (d := d)) :=
    aux_lem_local_normalizations_lnorm_regroup_bandSigma_le Hd
  have hRDmem2 : MemLp RD 2 Pm := by
    rw [hRDdef, hPmdef]; exact (hRDmoment6 Nd).mono_exponent (by norm_num)
  have hcontraction := aux_lem_local_normalizations_lnorm_condExp_contraction (Ω := BilateralField d) (μ := Pm)
    (m0 := MeasurableSpace.pi) hm1 hm2 hm12 hRDmem2
  have hbandbound := hRDband Hd Nd
  rw [h2] at hcontraction
  have hRHS : eLpNorm (fun x => RD x -
      (Pm[RD|bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) Hd]) x) (ENNReal.ofReal 2) Pm ≤
      ENNReal.ofReal (Cband * Delta * (3 : ℝ) ^ (-(aD * (Hd : ℝ)))) := hbandbound
  have hmid := hcontraction.trans hRHS
  have hae : Rf ∘ (aux_lem_local_normalizations_lnorm_regroup (d := d)) =ᵐ[Pm] RD := by
    rw [hRfdef, hRDdef, hPmdef]
    exact aux_g9_neumann_response_wrapper_generic_ae_eq z r hr R M H hH Nd
  have hRDmem6 : MemLp RD (ENNReal.ofReal 6) Pm := by rw [hRDdef, hPmdef]; exact hRDmoment6 Nd
  have hRfmem_comp : MemLp (Rf ∘ (aux_lem_local_normalizations_lnorm_regroup (d := d))) (ENNReal.ofReal 6) Pm :=
    hRDmem6.ae_eq hae.symm
  have hmp : MeasurePreserving (aux_lem_local_normalizations_lnorm_regroup (d := d)) Pm laws := by
    rw [hPmdef, hlawsdef]; exact aux_lem_local_normalizations_lnorm_regroup_measurePreserving M
  have hRfmem : MemLp Rf (ENNReal.ofReal 6) laws := by
    rw [← hmp.map_eq]
    exact (MeasurableEquiv.memLp_map_measure_iff (aux_lem_local_normalizations_lnorm_regroup (d := d))).mpr hRfmem_comp
  have htransport : Integrable Rf laws := hRfmem.integrable (by norm_num)
  have hcep := SubdiffusiveProcess.condExp_comp_measurePreserving hmp
    (bandSigma_le (Y := aux_lem_local_normalizations_lnorm_regroup_Y d) Hd) htransport
  have hcongr1 : Pm[Rf ∘ (aux_lem_local_normalizations_lnorm_regroup (d := d)) |
      (bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd).comap (aux_lem_local_normalizations_lnorm_regroup (d := d))] =ᵐ[Pm]
      Pm[RD | (bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd).comap (aux_lem_local_normalizations_lnorm_regroup (d := d))] :=
    condExp_congr_ae hae
  have hkey : (laws[Rf | bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd]) ∘ (aux_lem_local_normalizations_lnorm_regroup (d := d))
      =ᵐ[Pm] Pm[RD | (bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd).comap (aux_lem_local_normalizations_lnorm_regroup (d := d))] :=
    hcep.symm.trans hcongr1
  have hgoal_ae : (fun omega => Rf (aux_lem_local_normalizations_lnorm_regroup omega) -
      (laws[Rf | bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd]) (aux_lem_local_normalizations_lnorm_regroup omega))
      =ᵐ[Pm] (fun x => RD x -
        (Pm[RD | (bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd).comap (aux_lem_local_normalizations_lnorm_regroup (d := d))]) x) := by
    filter_upwards [hae, hkey] with omega h1 h2
    simp only [Function.comp_apply] at h1 h2
    show Rf (aux_lem_local_normalizations_lnorm_regroup omega) -
      (laws[Rf | bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd]) (aux_lem_local_normalizations_lnorm_regroup omega) = _
    rw [h1, h2]
  have hcompeq : eLpNorm (fun y => Rf y -
      (laws[Rf | bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd]) y) (ENNReal.ofReal 2) laws =
      eLpNorm (fun omega => Rf (aux_lem_local_normalizations_lnorm_regroup omega) -
        (laws[Rf | bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd]) (aux_lem_local_normalizations_lnorm_regroup omega))
        (ENNReal.ofReal 2) Pm := by
    have hgmeas : AEStronglyMeasurable (fun y => Rf y -
        (laws[Rf | bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd]) y) laws :=
      hRfmem.aestronglyMeasurable.sub
        (stronglyMeasurable_condExp.aestronglyMeasurable.mono (bandSigma_le Hd))
    exact (eLpNorm_comp_measurePreserving hgmeas hmp).symm
  rw [hcompeq, eLpNorm_congr_ae hgoal_ae]
  exact hmid

/-- **L¹ conditional-expectation contraction, factor 2.** Unlike the L² case (Pythagorean
orthogonality, factor 1), a finer sigma-algebra's L¹ condexp-gap is controlled by the coarser
one's only up to a factor of 2: `E[f|m2] - E[f|m1] = E[f - E[f|m1] | m2]` (since `E[f|m1]` is
already `m2`-measurable, conditioning it on `m2` is the identity), and Jensen's contraction
(`eLpNorm_one_condExp_le_eLpNorm`) bounds this by `‖f - E[f|m1]‖₁`; the triangle inequality then
gives the factor of `2`. This is the tool that lets `hband` be supplied directly from
`generic_band_two_sided`'s L¹ output (built for the ORIGINAL, non-regrouped index) instead of via
the more expensive prop_16-style probabilistic argument -- no positive-block resampling/
independence needed, matching the same regroup-transport idea `lem_local_normalizations` uses at
L², just one order lower and with a worse (but harmless) constant. -/
theorem aux_g9_neumann_response_wrapper_condExp_L1_contraction {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {m1 m2 : MeasurableSpace Ω} (hm2 : m2 ≤ m0)
    (hm12 : m1 ≤ m2) {f : Ω → ℝ} (hf : Integrable f μ) :
    eLpNorm (fun x => f x - (μ[f|m2]) x) 1 μ ≤ 2 * eLpNorm (fun x => f x - (μ[f|m1]) x) 1 μ := by
  have hm1 : m1 ≤ m0 := hm12.trans hm2
  have hsm1 : StronglyMeasurable[m1] (μ[f|m1]) := stronglyMeasurable_condExp (f := f) (m := m1)
  have hint1 : Integrable (μ[f|m1]) μ := integrable_condExp (f := f) (m := m1)
  have hm1meas : StronglyMeasurable[m2] (μ[f|m1]) := hsm1.mono hm12
  have hid : μ[μ[f|m1]|m2] = μ[f|m1] :=
    condExp_of_stronglyMeasurable hm2 hm1meas hint1
  have hsub : μ[f - μ[f|m1]|m2] =ᵐ[μ] μ[f|m2] - μ[f|m1] := by
    have h := condExp_sub hf hint1 m2
    rwa [hid] at h
  have hae1 : AEStronglyMeasurable[m0] (μ[f|m1]) μ := (hsm1.mono hm1).aestronglyMeasurable
  have hae2 : AEStronglyMeasurable[m0] (μ[f|m2]) μ :=
    ((stronglyMeasurable_condExp (f := f) (m := m2)).mono hm2).aestronglyMeasurable
  have hgap : eLpNorm (fun x => (μ[f|m2]) x - (μ[f|m1]) x) 1 μ ≤
      eLpNorm (fun x => f x - (μ[f|m1]) x) 1 μ := by
    calc eLpNorm (fun x => (μ[f|m2]) x - (μ[f|m1]) x) 1 μ
        = eLpNorm (μ[f - μ[f|m1]|m2]) 1 μ := (eLpNorm_congr_ae hsub).symm
      _ ≤ eLpNorm (f - μ[f|m1]) 1 μ := eLpNorm_one_condExp_le_eLpNorm _
      _ = eLpNorm (fun x => f x - (μ[f|m1]) x) 1 μ := by rfl
  have htri : eLpNorm (fun x => f x - (μ[f|m2]) x) 1 μ ≤
      eLpNorm (fun x => f x - (μ[f|m1]) x) 1 μ +
        eLpNorm (fun x => (μ[f|m2]) x - (μ[f|m1]) x) 1 μ := by
    have heq : (fun x => f x - (μ[f|m2]) x) =
        (fun x => f x - (μ[f|m1]) x) - (fun x => (μ[f|m2]) x - (μ[f|m1]) x) := by
      funext x; simp only [Pi.sub_apply]; ring
    rw [heq]
    exact eLpNorm_sub_le (hf.aestronglyMeasurable.sub hae1) (hae2.sub hae1) le_rfl
  calc eLpNorm (fun x => f x - (μ[f|m2]) x) 1 μ
      ≤ eLpNorm (fun x => f x - (μ[f|m1]) x) 1 μ +
          eLpNorm (fun x => (μ[f|m2]) x - (μ[f|m1]) x) 1 μ := htri
    _ ≤ eLpNorm (fun x => f x - (μ[f|m1]) x) 1 μ + eLpNorm (fun x => f x - (μ[f|m1]) x) 1 μ := by
        gcongr
    _ = 2 * eLpNorm (fun x => f x - (μ[f|m1]) x) 1 μ := by rw [two_mul]



theorem aux_g9_neumann_response_wrapper_generic_hband_L1
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (R : SubdiffusiveProcess.Lane3.Response (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (Nd : ℕ)
    (hRDint : Integrable (aux_g9_neumann_response_wrapper_generic_RTrue z r hr R M H Nd)
      (chaosSampleLaw M).toMeasure)
    (Cband : ℕ → ℝ)
    (hRDband : ∀ (h : ℕ),
      eLpNorm (fun omega => aux_g9_neumann_response_wrapper_generic_RTrue z r hr R M H Nd omega -
          (((chaosSampleLaw M).toMeasure)[aux_g9_neumann_response_wrapper_generic_RTrue z r hr R M H Nd |
            bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) omega)
        1 (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cband h))
    (Hd : ℕ) :
    eLpNorm (fun y => aux_g9_neumann_response_wrapper_generic_Rf z r hr R M Nd y -
        ((Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M))[aux_g9_neumann_response_wrapper_generic_Rf z r hr R M Nd |
          bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd]) y) 1
      (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M)) ≤
    ENNReal.ofReal (2 * Cband Hd) := by
  set Pm := (chaosSampleLaw M).toMeasure with hPmdef
  set laws := Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M) with hlawsdef
  set RD := aux_g9_neumann_response_wrapper_generic_RTrue z r hr R M H Nd with hRDdef
  set Rf := aux_g9_neumann_response_wrapper_generic_Rf z r hr R M Nd with hRfdef
  have hm1 : bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) Hd ≤
      (MeasurableSpace.pi : MeasurableSpace (BilateralField d)) := by
    refine iSup₂_le fun j _ s hs => ?_
    obtain ⟨t, ht, hst⟩ := hs
    exact hst ▸ measurable_pi_apply j ht
  have hm2Y : bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd ≤
      (MeasurableSpace.pi : MeasurableSpace ((j : ℤ) → aux_lem_local_normalizations_lnorm_regroup_Y d j)) := by
    refine iSup₂_le fun j _ s hs => ?_
    obtain ⟨t, ht, hst⟩ := hs
    exact hst ▸ measurable_pi_apply j ht
  have hm2 : (bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd).comap (aux_lem_local_normalizations_lnorm_regroup (d := d)) ≤
      (MeasurableSpace.pi : MeasurableSpace (BilateralField d)) :=
    le_trans (MeasurableSpace.comap_mono hm2Y)
      (measurable_iff_comap_le.mp (aux_lem_local_normalizations_lnorm_regroup (d := d)).measurable)
  have hm12 : bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) Hd ≤
      (bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd).comap (aux_lem_local_normalizations_lnorm_regroup (d := d)) :=
    aux_lem_local_normalizations_lnorm_regroup_bandSigma_le Hd
  have hcontraction := aux_g9_neumann_response_wrapper_condExp_L1_contraction (Ω := BilateralField d) (μ := Pm)
    (m0 := MeasurableSpace.pi) hm2 hm12 hRDint
  have hbandbound := hRDband Hd
  have hRHS : eLpNorm (fun x => RD x -
      (Pm[RD|bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) Hd]) x) 1 Pm ≤
      ENNReal.ofReal (Cband Hd) := hbandbound
  have hmid : eLpNorm (fun x => RD x -
      (Pm[RD | (bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd).comap
        (aux_lem_local_normalizations_lnorm_regroup (d := d))]) x) 1 Pm ≤
      ENNReal.ofReal (2 * Cband Hd) := by
    refine hcontraction.trans ?_
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
    rw [h2]
    exact mul_le_mul_left' hRHS _
  have hae : Rf ∘ (aux_lem_local_normalizations_lnorm_regroup (d := d)) =ᵐ[Pm] RD := by
    rw [hRfdef, hRDdef, hPmdef]
    exact aux_g9_neumann_response_wrapper_generic_ae_eq z r hr R M H hH Nd
  have hRfmem_comp : Integrable (Rf ∘ (aux_lem_local_normalizations_lnorm_regroup (d := d))) Pm :=
    hRDint.congr hae.symm
  have hmp : MeasurePreserving (aux_lem_local_normalizations_lnorm_regroup (d := d)) Pm laws := by
    rw [hPmdef, hlawsdef]; exact aux_lem_local_normalizations_lnorm_regroup_measurePreserving M
  have hRfmem : MemLp Rf 1 laws := by
    rw [← hmp.map_eq]
    exact (MeasurableEquiv.memLp_map_measure_iff (aux_lem_local_normalizations_lnorm_regroup (d := d))).mpr
      (memLp_one_iff_integrable.mpr hRfmem_comp)
  have htransport : Integrable Rf laws := hRfmem.integrable le_rfl
  have hcep := SubdiffusiveProcess.condExp_comp_measurePreserving hmp
    (bandSigma_le (Y := aux_lem_local_normalizations_lnorm_regroup_Y d) Hd) htransport
  have hcongr1 : Pm[Rf ∘ (aux_lem_local_normalizations_lnorm_regroup (d := d)) |
      (bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd).comap (aux_lem_local_normalizations_lnorm_regroup (d := d))] =ᵐ[Pm]
      Pm[RD | (bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd).comap (aux_lem_local_normalizations_lnorm_regroup (d := d))] :=
    condExp_congr_ae hae
  have hkey : (laws[Rf | bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd]) ∘ (aux_lem_local_normalizations_lnorm_regroup (d := d))
      =ᵐ[Pm] Pm[RD | (bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd).comap (aux_lem_local_normalizations_lnorm_regroup (d := d))] :=
    hcep.symm.trans hcongr1
  have hgoal_ae : (fun omega => Rf (aux_lem_local_normalizations_lnorm_regroup omega) -
      (laws[Rf | bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd]) (aux_lem_local_normalizations_lnorm_regroup omega))
      =ᵐ[Pm] (fun x => RD x -
        (Pm[RD | (bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd).comap (aux_lem_local_normalizations_lnorm_regroup (d := d))]) x) := by
    filter_upwards [hae, hkey] with omega h1 h2
    simp only [Function.comp_apply] at h1 h2
    show Rf (aux_lem_local_normalizations_lnorm_regroup omega) -
      (laws[Rf | bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd]) (aux_lem_local_normalizations_lnorm_regroup omega) = _
    rw [h1, h2]
  have hcompeq : eLpNorm (fun y => Rf y -
      (laws[Rf | bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd]) y) 1 laws =
      eLpNorm (fun omega => Rf (aux_lem_local_normalizations_lnorm_regroup omega) -
        (laws[Rf | bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd]) (aux_lem_local_normalizations_lnorm_regroup omega))
        1 Pm := by
    have hgmeas : AEStronglyMeasurable (fun y => Rf y -
        (laws[Rf | bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) Hd]) y) laws :=
      hRfmem.aestronglyMeasurable.sub
        (stronglyMeasurable_condExp.aestronglyMeasurable.mono (bandSigma_le Hd))
    exact (eLpNorm_comp_measurePreserving hgmeas hmp).symm
  rw [hcompeq, eLpNorm_congr_ae hgoal_ae]
  exact hmid

theorem aux_g9_neumann_response_wrapper_generic_compact_transport
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (R : SubdiffusiveProcess.Lane3.Response (centeredCube z r hr))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]
    (hRDmem : ∀ N, MemLp (aux_g9_neumann_response_wrapper_generic_RTrue z r hr R M H N) p (chaosSampleLaw M).toMeasure)
    (hRfmem : ∀ N, MemLp (aux_g9_neumann_response_wrapper_generic_Rf z r hr R M N) p
      (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M)))
    (hcompact : IsCompact (closure (Set.range (fun N =>
      (hRfmem N).toLp (aux_g9_neumann_response_wrapper_generic_Rf z r hr R M N))))) :
    IsCompact (closure (Set.range (fun N =>
      (hRDmem N).toLp (aux_g9_neumann_response_wrapper_generic_RTrue z r hr R M H N)))) := by
  have hmp := aux_lem_local_normalizations_lnorm_regroup_measurePreserving M
  set pull := Lp.compMeasurePreserving (E := ℝ) (p := p) (aux_lem_local_normalizations_lnorm_regroup (d := d)) hmp
    with pulldef
  have hiso : Isometry pull := Lp.isometry_compMeasurePreserving hmp
  have hrep : (fun N => (hRDmem N).toLp (aux_g9_neumann_response_wrapper_generic_RTrue z r hr R M H N)) =
      pull ∘ (fun N => (hRfmem N).toLp (aux_g9_neumann_response_wrapper_generic_Rf z r hr R M N)) := by
    funext N
    have hae : Filter.EventuallyEq (MeasureTheory.ae (chaosSampleLaw M).toMeasure)
        (aux_g9_neumann_response_wrapper_generic_Rf z r hr R M N ∘ (aux_lem_local_normalizations_lnorm_regroup (d := d)))
        (aux_g9_neumann_response_wrapper_generic_RTrue z r hr R M H N) :=
      aux_g9_neumann_response_wrapper_generic_ae_eq z r hr R M H hH N
    have hstep : pull ((hRfmem N).toLp (aux_g9_neumann_response_wrapper_generic_Rf z r hr R M N)) =
        ((hRfmem N).comp_measurePreserving hmp).toLp
          (aux_g9_neumann_response_wrapper_generic_Rf z r hr R M N ∘ (aux_lem_local_normalizations_lnorm_regroup (d := d))) := by
      rw [pulldef]; exact Lp.toLp_compMeasurePreserving (hRfmem N) hmp
    show _ = pull ((hRfmem N).toLp (aux_g9_neumann_response_wrapper_generic_Rf z r hr R M N))
    rw [hstep]
    apply Lp.ext
    exact ((((hRfmem N).comp_measurePreserving hmp).coeFn_toLp).trans
      (hae.trans (hRDmem N).coeFn_toLp.symm)).symm
  rw [hrep, Set.range_comp pull,
    hiso.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous hiso.continuous]
  exact hcompact.image hiso.continuous

end AuxG9Generic

/-! ## Part 2: the Neumann-specific `Response` wrapper, homogeneity, and the
`rem_bank`/`prop_16.2` moment + band extraction. -/

section AuxG9Neumann

variable {d : ℕ}

/-- `inverseResponse S (expPotentialCoefficient ·) L`, wrapped as a `Lane3.Response`, with
TRIVIAL (constant-in-`s`) mass — the exact mirror of
`aux_lem_local_normalizations_lnaff_response` (`dirichletResponse` swapped for `inverseResponse`,
`dirichletResponse_potential_comparison` swapped for `inverseResponse_potential_comparison`). -/
def g9_neumann_response_wrapper {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (L : S.space →L[ℝ] ℝ) : SubdiffusiveProcess.Lane3.Response Ω where
  eval g := inverseResponse S (expPotentialCoefficient g) L
  mass g _ := inverseResponse S (expPotentialCoefficient g) L
  eval_nonneg g := inverseResponse_nonneg S _ L
  mass_nonneg g _ := inverseResponse_nonneg S _ L
  mass_mono _ _ _ _ _ _ := le_rfl
  mass_univ _ := rfl
  exp_comparison g h := by
    have h2 := (inverseResponse_potential_comparison S L h g).2
    rwa [norm_sub_rev] at h2
  response_perturbation h g _ _ _ := by
    apply aux_lem_prefix_limit_atom_extraction_real_perturb ‖g‖ _ _ (norm_nonneg g)
      (inverseResponse_nonneg S _ L)
    · have hc := (inverseResponse_potential_comparison S L h (h + g)).2
      rwa [show h - (h + g) = -g by abel, norm_neg] at hc
    · have hc := (inverseResponse_potential_comparison S L (h + g) h).2
      rwa [add_sub_cancel_left] at hc
  mass_perturbation h g _ _ _ := by
    have hc := (inverseResponse_potential_comparison S L h (h + g)).2
    rw [show h - (h + g) = -g by abel, norm_neg] at hc
    have hn := inverseResponse_nonneg S (expPotentialCoefficient h) L
    have h1 : 1 ≤ 2 * (1 + ‖g‖ ^ 2 * Real.exp (4 * ‖g‖)) := by
      nlinarith [sq_nonneg ‖g‖, Real.exp_pos (4 * ‖g‖), mul_nonneg (sq_nonneg ‖g‖)
        (Real.exp_pos (4 * ‖g‖)).le]
    calc inverseResponse S (expPotentialCoefficient (h + g)) L
        ≤ Real.exp ‖g‖ * inverseResponse S (expPotentialCoefficient h) L := hc
      _ ≤ 2 * Real.exp ‖g‖ * (1 + ‖g‖ ^ 2 * Real.exp (4 * ‖g‖)) *
            inverseResponse S (expPotentialCoefficient h) L := by
          have hE := Real.exp_pos ‖g‖
          nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hE.le hn)]

theorem aux_g9_neumann_response_wrapper_eval {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (L : S.space →L[ℝ] ℝ) (g : SubdiffusiveProcess.Lane3.Potential Ω) :
    (g9_neumann_response_wrapper S L).eval g = inverseResponse S (expPotentialCoefficient g) L := rfl

/-- Neumann Poincaré on the unit Neumann cube. -/
theorem aux_g9_neumann_response_wrapper_poincare [NeZero d] :
    ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph (centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos),
      ‖(w : SobolevData (centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph
          (centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)) w‖ :=
  (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain _
    (lane2_isOpenBoundedConvexDomain_centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)).2

/-- `affineNeumannLoad` is `ℝ`-linear in the slope. -/
theorem aux_g9_neumann_response_wrapper_affineNeumannLoad_smul {Ω : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (c : ℝ) (p : Fin d → ℝ) :
    affineNeumannLoad (Ω := Ω) (c • p) = c • affineNeumannLoad (Ω := Ω) p := by
  apply ContinuousLinearMap.ext
  intro g
  rw [affineNeumannLoad_apply, ContinuousLinearMap.smul_apply, affineNeumannLoad_apply,
    smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext x; ring

/-- `inverseResponse` is `2`-homogeneous in the load. -/
theorem aux_g9_neumann_response_wrapper_inverseResponse_smul {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (c : ℝ) (L : S.space →L[ℝ] ℝ) :
    inverseResponse S a (c • L) = c ^ 2 * inverseResponse S a L := by
  rw [inverseResponse_eq_load, responseSolution_smul, ContinuousLinearMap.smul_apply,
    map_smul, smul_eq_mul, smul_eq_mul, ← inverseResponse_eq_load]
  ring

/-- `affineInverseNeumannResponse` at slope `c • p` is `c^2` times its value at `p`. -/
theorem aux_g9_neumann_response_wrapper_affineInverseNeumannResponse_smul {Ω : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (hPn : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) (c : ℝ) (p : Fin d → ℝ) :
    affineInverseNeumannResponse hPn a (c • p) = c ^ 2 * affineInverseNeumannResponse hPn a p := by
  unfold affineInverseNeumannResponse
  rw [aux_g9_neumann_response_wrapper_affineNeumannLoad_smul, ContinuousLinearMap.smul_comp, aux_g9_neumann_response_wrapper_inverseResponse_smul]

end AuxG9Neumann




section AuxG9HstepCombinator

/-- Pure real-number algebra: `eps(k) := 3^{-(4a/9 · k + 4)}` (a shift of `4` keeps it `< 1/8` for
EVERY `k ≥ 0`, avoiding any small-`k` case split) makes both `eps^{1/4}` and `eps^{-2}·3^{-ak}`
decay at exactly the SAME rate `a/9`. Isolated as its own top-level lemma (no `set`-chaining) to
avoid a `whnf` heartbeat timeout that the same computation hit when inlined inside a longer
measure-theoretic proof (a chained-`set` elaboration-depth issue, same family as the one recorded
for `g9_dirichlet_response_compact`'s own RECEIPT). -/
theorem aux_g9_neumann_response_wrapper_eps_choice (a : ℝ) (ha0 : 0 < a) (k : ℕ) :
    ∃ eps : ℝ, 0 < eps ∧ eps < 1 / 8 ∧
      eps ^ (1 / 4 : ℝ) = (1 / 3 : ℝ) * (3 : ℝ) ^ (-(a / 9) * (k : ℝ)) ∧
      eps ^ (-2 : ℝ) * (3 : ℝ) ^ (-a * (k : ℝ)) = (6561 : ℝ) * (3 : ℝ) ^ (-(a / 9) * (k : ℝ)) := by
  refine ⟨(3 : ℝ) ^ (-(4 * a / 9 * (k : ℝ) + 4)), Real.rpow_pos_of_pos (by norm_num) _, ?_, ?_, ?_⟩
  · have hexp_le : -(4 * a / 9 * (k : ℝ) + 4) ≤ (-4 : ℝ) := by
      have : 0 ≤ 4 * a / 9 * (k : ℝ) := by positivity
      linarith
    have heps_le : (3 : ℝ) ^ (-(4 * a / 9 * (k : ℝ) + 4)) ≤ (3 : ℝ) ^ (-4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le
    have h81 : (3 : ℝ) ^ (-4 : ℝ) = 1 / 81 := by
      rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num), Real.rpow_natCast]
      norm_num
    rw [h81] at heps_le; linarith
  · rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      show (-(4 * a / 9 * (k : ℝ) + 4)) * (1 / 4 : ℝ) = -1 + -(a / 9) * (k : ℝ) by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    rw [show (-1 : ℝ) = -((1 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num), Real.rpow_natCast]
    norm_num
  · rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      show (-(4 * a / 9 * (k : ℝ) + 4)) * (-2 : ℝ) + -a * (k : ℝ) = 8 + -(a / 9) * (k : ℝ) by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num

theorem aux_g9_neumann_response_wrapper_hstep_combinator {X : Type} [MeasurableSpace X]
    (laws : ℤ → Measure X) [∀ j, IsProbabilityMeasure (laws j)]
    (f : (ℤ → X) → ℝ) (g : ℝ → (ℤ → X) → ℝ) (N : ℕ)
    (hfmeas : AEStronglyMeasurable f (Measure.infinitePi laws))
    (hgmeas : ∀ eps, AEStronglyMeasurable (g eps) (Measure.infinitePi laws))
    (a : ℝ) (ha0 : 0 < a)
    (Cn : ℝ) (hCn : 0 ≤ Cn)
    (hstepg : ∀ (eps : ℝ), 0 < eps → eps < 1 / 8 → ∀ k : ℕ, k ≤ N →
      eLpNorm (fun q : (ℤ → X) × (ℤ → X) =>
          g eps q.1 - g eps (Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ))))) 2
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) ≤
      ENNReal.ofReal (Cn * eps ^ (-2 : ℝ) * (3 : ℝ) ^ (-a * (k : ℝ))))
    (Cerr : ℝ) (hCerr : 0 ≤ Cerr)
    (hsmooth : ∀ (eps : ℝ), 0 < eps → eps < 1 / 8 →
      eLpNorm (fun ω => f ω - g eps ω) 2 (Measure.infinitePi laws) ≤
        ENNReal.ofReal (Cerr * eps ^ (1 / 4 : ℝ))) :
    ∀ k : ℕ, k ≤ N →
      eLpNorm (fun q : (ℤ → X) × (ℤ → X) =>
          f q.1 - f (Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ))))) 1
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) ≤
      ENNReal.ofReal ((2 * Cerr / 3 + 6561 * Cn) * (3 : ℝ) ^ (-(a / 9) * (k : ℝ))) := by
  intro k hk
  obtain ⟨eps, heps_pos, heps_lt, heps14, hepsm2⟩ :=
    aux_g9_neumann_response_wrapper_eps_choice a ha0 k
  set laws2 := (Measure.infinitePi laws).prod (Measure.infinitePi laws) with hlaws2
  haveI hlaws2prob : IsProbabilityMeasure laws2 := by rw [hlaws2]; infer_instance
  clear_value laws2
  set F1 : (ℤ → X) × (ℤ → X) → ℝ := fun q => f q.1 - g eps q.1 with hF1
  set F2 : (ℤ → X) × (ℤ → X) → ℝ := fun q =>
    g eps q.1 - g eps (Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ)))) with hF2
  set F3 : (ℤ → X) × (ℤ → X) → ℝ := fun q =>
    g eps (Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ)))) - f (Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ)))) with hF3
  have hsplit : (fun q : (ℤ → X) × (ℤ → X) =>
      f q.1 - f (Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ))))) = F1 + F2 + F3 := by
    funext q
    simp only [hF1, hF2, hF3, Pi.add_apply]
    ring
  clear_value F1 F2 F3
  have hupdmp : MeasurePreserving (fun q : (ℤ → X) × (ℤ → X) => Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ))))
      laws2 (Measure.infinitePi laws) := by rw [hlaws2]; exact aux_prop_16_update_mp laws (-(k : ℤ))
  have hp12 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hmpfst : MeasurePreserving (Prod.fst : (ℤ → X) × (ℤ → X) → (ℤ → X)) laws2 (Measure.infinitePi laws) := by
    rw [hlaws2]; exact measurePreserving_fst
  have hF1meas : AEStronglyMeasurable F1 laws2 := by
    rw [hF1]; exact (hfmeas.sub (hgmeas eps)).comp_measurePreserving hmpfst
  have hF2meas : AEStronglyMeasurable F2 laws2 := by
    rw [hF2]
    exact ((hgmeas eps).comp_measurePreserving hmpfst).sub
      ((hgmeas eps).comp_measurePreserving hupdmp)
  have hF3meas : AEStronglyMeasurable F3 laws2 := by
    rw [hF3]; exact ((hgmeas eps).sub hfmeas).comp_measurePreserving hupdmp
  have hF1eLp : eLpNorm F1 2 laws2 ≤ ENNReal.ofReal (Cerr * eps ^ (1 / 4 : ℝ)) := by
    rw [hF1]
    exact (eLpNorm_comp_measurePreserving (hfmeas.sub (hgmeas eps)) hmpfst).le.trans
      (hsmooth eps heps_pos heps_lt)
  have hF3eLp : eLpNorm F3 2 laws2 ≤ ENNReal.ofReal (Cerr * eps ^ (1 / 4 : ℝ)) := by
    rw [hF3]
    have hneg : eLpNorm (g eps - f) 2 (Measure.infinitePi laws) =
        eLpNorm (fun ω => f ω - g eps ω) 2 (Measure.infinitePi laws) := by
      rw [show (g eps - f) = -(f - g eps) by funext ω; simp [Pi.sub_apply], eLpNorm_neg]
      rfl
    exact ((eLpNorm_comp_measurePreserving ((hgmeas eps).sub hfmeas) hupdmp).trans hneg).le.trans
      (hsmooth eps heps_pos heps_lt)
  have hF2eLp : eLpNorm F2 2 laws2 ≤ ENNReal.ofReal (Cn * eps ^ (-2 : ℝ) * (3 : ℝ) ^ (-a * (k : ℝ))) := by
    rw [hF2]; exact hstepg eps heps_pos heps_lt k hk
  have htri2 : eLpNorm (F1 + F2 + F3) 2 laws2 ≤
      ENNReal.ofReal (Cerr * eps ^ (1 / 4 : ℝ)) + ENNReal.ofReal (Cn * eps ^ (-2 : ℝ) * (3 : ℝ) ^ (-a * (k : ℝ))) +
        ENNReal.ofReal (Cerr * eps ^ (1 / 4 : ℝ)) :=
    ((eLpNorm_add_le (hF1meas.add hF2meas) hF3meas hp12).trans
      (add_le_add (eLpNorm_add_le hF1meas hF2meas hp12) le_rfl)).trans
      (add_le_add (add_le_add hF1eLp hF2eLp) hF3eLp)
  have hRHS_eq : Cerr * eps ^ (1 / 4 : ℝ) + Cn * eps ^ (-2 : ℝ) * (3 : ℝ) ^ (-a * (k : ℝ)) +
      Cerr * eps ^ (1 / 4 : ℝ) = (2 * Cerr / 3 + 6561 * Cn) * (3 : ℝ) ^ (-(a / 9) * (k : ℝ)) := by
    rw [heps14, show Cn * eps ^ (-2 : ℝ) * (3 : ℝ) ^ (-a * (k : ℝ)) =
      Cn * (eps ^ (-2 : ℝ) * (3 : ℝ) ^ (-a * (k : ℝ))) by ring, hepsm2]
    ring
  have hcombine_eq : ENNReal.ofReal (Cerr * eps ^ (1 / 4 : ℝ)) +
      ENNReal.ofReal (Cn * eps ^ (-2 : ℝ) * (3 : ℝ) ^ (-a * (k : ℝ))) +
      ENNReal.ofReal (Cerr * eps ^ (1 / 4 : ℝ)) =
      ENNReal.ofReal ((2 * Cerr / 3 + 6561 * Cn) * (3 : ℝ) ^ (-(a / 9) * (k : ℝ))) := by
    rw [← ENNReal.ofReal_add (by positivity)
        (by positivity : (0:ℝ) ≤ Cn * eps ^ (-2 : ℝ) * (3 : ℝ) ^ (-a * (k : ℝ))),
      ← ENNReal.ofReal_add (by positivity) (by positivity : (0:ℝ) ≤ Cerr * eps ^ (1 / 4 : ℝ)),
      hRHS_eq]
  have hcombine : eLpNorm (F1 + F2 + F3) 2 laws2 ≤
      ENNReal.ofReal ((2 * Cerr / 3 + 6561 * Cn) * (3 : ℝ) ^ (-(a / 9) * (k : ℝ))) :=
    htri2.trans (le_of_eq hcombine_eq)
  rw [hsplit]
  refine (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (hF1meas.add hF2meas |>.add hF3meas)).trans hcombine

end AuxG9HstepCombinator

end Paper
