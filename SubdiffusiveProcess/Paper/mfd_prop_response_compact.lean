module

public import SubdiffusiveProcess.Paper.prop_response_compact
public import SubdiffusiveProcess.Paper.prop_16
public import SubdiffusiveProcess.Paper.conditional_response_setup
public import SubdiffusiveProcess.Paper.g9_neumann_response_wrapper
public import SubdiffusiveProcess.Section9.ConditionalLpContraction
public import SubdiffusiveProcess.Sobolev.AffineResponseWrap
public import SubdiffusiveProcess.ResponseMoments.ResponseInstances

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper


section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- Transfer a band approximation to the regrouped coordinates at every finite exponent. -/
lemma aux_mfd_prop_response_compact_regroup_band
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (h : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (f : BilateralField d → ℝ)
    (g : ((j : ℤ) → aux_lem_local_normalizations_lnorm_regroup_Y d j) → ℝ)
    (hf : Integrable f (chaosSampleLaw M).toMeasure)
    (hg : MemLp g p (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M)))
    (hae : g ∘ aux_lem_local_normalizations_lnorm_regroup =ᵐ[(chaosSampleLaw M).toMeasure] f)
    {B : ℝ≥0∞}
    (hb : eLpNorm (f - (chaosSampleLaw M).toMeasure[f |
        bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) p
        (chaosSampleLaw M).toMeasure ≤ B) :
    eLpNorm (g - (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M))[g |
        bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) h]) p
        (Measure.infinitePi (aux_lem_local_normalizations_lnorm_regroup_laws M)) ≤ 2 * B := by
  classical
  let Y := aux_lem_local_normalizations_lnorm_regroup_Y d
  let laws := aux_lem_local_normalizations_lnorm_regroup_laws M
  let rho := aux_lem_local_normalizations_lnorm_regroup (d := d)
  let e0 := MeasurableEquiv.piEquivPiSubtypeProd Y (fun j => j ∈ bandSet h)
  have hmp := aux_lem_local_normalizations_lnorm_regroup_measurePreserving M
  have he0 := measurePreserving_infinitePi_split laws (fun j => j ∈ bandSet h)
  let e := rho.trans e0
  have he : MeasurePreserving e (chaosSampleLaw M).toMeasure
      ((Measure.infinitePi fun j : bandSet h => laws j.1).prod
        (Measure.infinitePi fun j : {j : ℤ // j ∉ bandSet h} => laws j.1)) :=
    he0.comp hmp
  have hsigma : (bandSigma Y h).comap rho =
      (inferInstance : MeasurableSpace ((j : bandSet h) → Y j.1)).comap
        (fun x : BilateralField d => (e x).1) := by
    rw [bandSigma_eq_comap, MeasurableSpace.comap_comp]
    rfl
  have hle : bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h ≤
      (inferInstance : MeasurableSpace ((j : bandSet h) → Y j.1)).comap
        (fun x : BilateralField d => (e x).1) := by
    rw [← hsigma]
    exact aux_lem_local_normalizations_lnorm_regroup_bandSigma_le h
  have hbound := SubdiffusiveProcess.Section9.condExp_equiv_fst_error_le_twice e he hle hp hpt hf
  have hce := SubdiffusiveProcess.condExp_comp_measurePreserving hmp (bandSigma_le h)
    (hg.integrable hp)
  have hkey : ((Measure.infinitePi laws)[g | bandSigma Y h]) ∘ rho =ᵐ[(chaosSampleLaw M).toMeasure]
      (chaosSampleLaw M).toMeasure[f | (bandSigma Y h).comap rho] :=
    hce.symm.trans (condExp_congr_ae hae)
  have hgap : (g - (Measure.infinitePi laws)[g | bandSigma Y h]) ∘ rho =ᵐ[(chaosSampleLaw M).toMeasure]
      f - (chaosSampleLaw M).toMeasure[f | (bandSigma Y h).comap rho] := by
    filter_upwards [hae, hkey] with x hx hx'
    exact congrArg₂ (fun a b : ℝ => a - b) hx hx'
  rw [← eLpNorm_comp_measurePreserving
    (hg.aestronglyMeasurable.sub (stronglyMeasurable_condExp.mono (bandSigma_le h)).aestronglyMeasurable)
    hmp, eLpNorm_congr_ae hgap, hsigma]
  exact hbound.trans (mul_le_mul_right hb 2)

/-- Compactness of any of the concrete response objects, with a fixed cutoff offset. -/
lemma aux_mfd_prop_response_compact_response
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (R : Response (centeredCube z r hr))
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (sh : ℕ) (p q : ℝ≥0∞) [hp : Fact (1 ≤ p)] (hpq : p < q) (hqt : q ≠ ∞)
    (a C : ℝ) (ha : 0 < a) (K : ℝ≥0∞) (hK : K ≠ ∞)
    (hm : ∀ N, MemLp (aux_g9_neumann_response_wrapper_generic_RTrue z r hr R M H (N + sh)) q
      (chaosSampleLaw M).toMeasure)
    (hb : ∀ N, eLpNorm (aux_g9_neumann_response_wrapper_generic_RTrue z r hr R M H (N + sh)) q
      (chaosSampleLaw M).toMeasure ≤ K)
    (hband : ∀ h N, h ≤ N → eLpNorm
      (aux_g9_neumann_response_wrapper_generic_RTrue z r hr R M H (N + sh) -
        (chaosSampleLaw M).toMeasure[aux_g9_neumann_response_wrapper_generic_RTrue z r hr R M H (N + sh) |
          bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) p (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (C * M.delta * (3 : ℝ) ^ (-(a * (h : ℝ))))) :
    IsCompact (closure (Set.range (fun N => ((hm N).mono_exponent hpq.le).toLp
      (aux_g9_neumann_response_wrapper_generic_RTrue z r hr R M H (N + sh))))) := by
  classical
  let laws := aux_lem_local_normalizations_lnorm_regroup_laws M
  let rho := aux_lem_local_normalizations_lnorm_regroup (d := d)
  let f := fun N => aux_g9_neumann_response_wrapper_generic_RTrue z r hr R M H (N + sh)
  let g := fun N => aux_g9_neumann_response_wrapper_generic_Rf z r hr R M (N + sh)
  have hmp := aux_lem_local_normalizations_lnorm_regroup_measurePreserving M
  have heq : ∀ N, g N ∘ rho =ᵐ[(chaosSampleLaw M).toMeasure] f N :=
    fun N => aux_g9_neumann_response_wrapper_generic_ae_eq z r hr R M H hH (N + sh)
  have hgm : ∀ N, MemLp (g N) q (Measure.infinitePi laws) := by
    intro N
    rw [← hmp.map_eq]
    exact (MeasurableEquiv.memLp_map_measure_iff rho).mpr ((hm N).ae_eq (heq N).symm)
  have hgb : ∀ N, eLpNorm (g N) q (Measure.infinitePi laws) ≤ K := by
    intro N
    rw [← eLpNorm_comp_measurePreserving (hgm N).aestronglyMeasurable hmp,
      eLpNorm_congr_ae (heq N)]
    exact hb N
  have hband' : ∀ h N, h ≤ N →
      eLpNorm (g N - (Measure.infinitePi laws)[g N |
          bandSigma (aux_lem_local_normalizations_lnorm_regroup_Y d) h]) p
        (Measure.infinitePi laws) ≤
        ENNReal.ofReal ((2 * max C 0) * M.delta * (3 : ℝ) ^ (-(a * (h : ℝ)))) := by
    intro h N hN
    have htrans := aux_mfd_prop_response_compact_regroup_band M h hp.out (ne_top_of_lt hpq)
      (f N) (g N) ((hm N).integrable (hp.out.trans hpq.le))
      ((hgm N).mono_exponent hpq.le) (heq N) (hband h N hN)
    refine htrans.trans ?_
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply ENNReal.ofReal_le_ofReal
    calc
      2 * (C * M.delta * (3 : ℝ) ^ (-(a * (h : ℝ)))) ≤
          2 * (max C 0 * M.delta * (3 : ℝ) ^ (-(a * (h : ℝ)))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left C 0)
            M.shellPrefix.delta_pos.le) (Real.rpow_nonneg (by norm_num) _)) (by norm_num)
      _ = (2 * max C 0) * M.delta * (3 : ℝ) ^ (-(a * (h : ℝ))) := by ring
  have hsplit : ∀ h : ℕ,
      ∃ (X : Type) (_ : MetricSpace X) (_ : SeparableSpace X) (_ : MeasurableSpace X)
        (_ : BorelSpace X) (Q : Opens (SpatialCoordinates d)) (R' : Response Q)
        (V : ((j : bandSet h) → aux_lem_local_normalizations_lnorm_regroup_Y d j.1) → X)
        (psi : X → Potential Q)
        (tail : ℕ → ((j : {j : ℤ // j ∉ bandSet h}) → aux_lem_local_normalizations_lnorm_regroup_Y d j.1) → Potential Q),
        Measurable V ∧ LipschitzWith 1 psi ∧
        (∀ N, h ≤ N → Measurable (fun w : X × ((j : {j : ℤ // j ∉ bandSet h}) →
          aux_lem_local_normalizations_lnorm_regroup_Y d j.1) => R'.eval (psi w.1 + tail N w.2))) ∧
        (∀ N, h ≤ N → ∀ omega, g N omega =
          R'.eval (psi (V (fun j => omega j.1)) + tail N (fun j => omega j.1))) := by
    intro h
    obtain ⟨X, hX, hsX, mX, bX, Q, R', V, psi, tail, hV, hpsi, hmeas, hrepr⟩ :=
      aux_g9_neumann_response_wrapper_generic_hsplit z r hr R M h
    refine ⟨X, hX, hsX, mX, bX, Q, R', V, psi, (fun N => tail (N + sh)), hV, hpsi, ?_, ?_⟩
    · intro N hN
      exact hmeas (N + sh) (hN.trans (Nat.le_add_right N sh))
    · intro N hN omega
      exact hrepr (N + sh) (hN.trans (Nat.le_add_right N sh)) omega
  obtain ⟨hc, -, -, -, -⟩ := prop_response_compact d
    (aux_lem_local_normalizations_lnorm_regroup_Y d) laws Unit Empty
    (fun _ => g) (fun e _ _ => e.elim) p q hpq hqt a M.delta ha M.shellPrefix.delta_pos
    (fun _ => 2 * max C 0) (fun _ => mul_nonneg (by norm_num) (le_max_right C 0))
    (fun _ => K) (fun _ => hK) (fun _ => hgm) (fun _ => hgb)
    (fun _ => hband') (fun _ => hsplit) (fun e => e.elim) (fun e => e.elim) (fun e _ _ => e.elim)
  let pull := Lp.compMeasurePreserving (E := ℝ) (p := p) rho hmp
  have hi : Isometry pull := Lp.isometry_compMeasurePreserving hmp
  have hrepr : (fun N => ((hm N).mono_exponent hpq.le).toLp (f N)) =
      pull ∘ (fun N => ((hgm N).mono_exponent hpq.le).toLp (g N)) := by
    funext N
    rw [Function.comp_apply, Lp.toLp_compMeasurePreserving]
    exact MemLp.toLp_congr ((hm N).mono_exponent hpq.le)
      (((hgm N).mono_exponent hpq.le).comp_measurePreserving hmp)
      (heq N).symm
  rw [hrepr, Set.range_comp pull,
    hi.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous hi.continuous]
  exact (hc ()).image hi.continuous

end
/- Joint extraction is carried out on the countable product of the compact Lp closures. -/
lemma aux_mfd_prop_response_compact_joint
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (I Pol : Type) [Countable I] [Countable Pol]
    (R : I → ℕ → Ω → ℝ) (G : Pol → ℕ → Ω → ℝ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hm : ∀ i N, MemLp (R i N) p μ) (hg : ∀ w N, MemLp (G w N) p μ)
    (hc : ∀ i, IsCompact (closure (Set.range (fun N => (hm i N).toLp (R i N)))))
    (hcg : ∀ w, IsCompact (closure (Set.range (fun N => (hg w N).toLp (G w N))))) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ (Rlim : I → Ω → ℝ) (Glim : Pol → Ω → ℝ),
        (∀ i, MemLp (Rlim i) p μ) ∧ (∀ w, MemLp (Glim w) p μ) ∧
        (∀ i, Tendsto (fun N => eLpNorm (fun om => R i (phi N) om - Rlim i om) p μ)
          atTop (𝓝 0)) ∧
        (∀ w, Tendsto (fun N => eLpNorm (fun om => G w (phi N) om - Glim w om) p μ)
          atTop (𝓝 0)) := by
  classical
  let u : I ⊕ Pol → ℕ → Lp ℝ p μ := fun k =>
    Sum.elim (fun i N => (hm i N).toLp (R i N)) (fun w N => (hg w N).toLp (G w N)) k
  have hcu : ∀ k, IsCompact (closure (Set.range (u k))) := by
    intro k
    cases k with
    | inl i => exact hc i
    | inr w => exact hcg w
  obtain ⟨phi, hphi, hlim⟩ := aux_countable_compact_subseq
    (fun k => closure (Set.range (u k))) hcu u
    (fun k N => subset_closure (Set.mem_range_self N))
  choose x hx using hlim
  refine ⟨phi, hphi, (fun i => x (.inl i)), (fun w => x (.inr w)),
    (fun i => Lp.memLp _), (fun w => Lp.memLp _), ?_, ?_⟩
  · intro i
    exact aux_raw_tendsto_of_lp (fun N => hm i (phi N)) (hx (.inl i))
  · intro w
    exact aux_raw_tendsto_of_lp (fun N => hg w (phi N)) (hx (.inr w))


/-!
Live proposition `mfd:prop-response-compact`, CONCRETE version (no abstract layer spaces, no
`hsplit`, no abstract index types).

* The energies `R_N` are the paper's own: for a member `i` of a countable family, a cube `Q_i = centeredCube (z i) (r i) (hr i)` (any centre/side;
  the determining cubes are a special case), a fixed integer shift `sh i` (`N ↦ N + sh i`) and one of
    kind 0: the Dirichlet energy `Λ_{N,Q}(b)` of a boundary datum `b` (`dirichletResponse`),
    kind 1: the killed quadratic response `⟨f, G_N^Q f⟩` of a source `f` (`inverseResponse` on the killed space),
    kind 2: the inverse affine Neumann energy `Y_N^Q(p) = |Q| p·a_*^{-1}(Q;A_N)p` (`affineInverseNeumannResponse`),
  computed for the actual cutoff coefficient `A_N = cutoffPositiveCoefficient M H ω N` of the model.
* "Satisfying Proposition `mfd:prop-16`" is rendered as its conclusion `eq:mfd-16` (the band approximation
  `‖R_N - E[R_N | B_h]‖_{L^p} ≤ C_i δ 3^{-a h}`, `h ≤ N`, as used by the live proof) — a hypothesis on the family, exactly as in the abstract
  principal `prop_response_compact`; `prop_16` proves it from the growth/moment package.  Together with `sup_N ‖R_N‖_{L^q} ≤ Kb i`, `q > p`.
* Signed forms `⟨f, G_N^Q g⟩ = ¼(R⁺_N - R⁻_N)` with `R^± = ⟨f ± g, G(f ± g)⟩` (polarisation), each of the two responses satisfying the same hypotheses.
* Conclusions: (i) `(R_N)` relatively compact in `L^p(P)` for every member; (ii) the same for every signed form; (iii) ONE extraction `φ`
  works for all members and shifts simultaneously, and every `L^p` subsequential limit is measurable for `σ(γ_{-j} : j ∈ ℤ)` (= the product
  band σ-algebra `⨆_H bandSigma H`).
The proof applies the abstract `prop_response_compact` to the exact total proxy of the concrete response after regrouping the infrared coordinates.
The existing `g9_neumann_response_wrapper` machinery supplies its splitting, measurability and a.e. equality to the true response. The new finite-Lp
conditioning estimate transfers the original band bound to the finer regrouped band with factor two; fixed shifts reindex only the omitted potential.
An isometric pullback transfers compactness to the true response. Polarisation and compactness of a countable product give one joint extraction.
The original bands generate the full layer product sigma field (`iSup_bandFiltration`), so all Lp representatives of the limits are layer-measurable.
-/

theorem mfd_prop_response_compact
    (d : ℕ) (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (_hH : InfraredCharacterization M H)
    (I Pol : Type) [Countable I] [Countable Pol]
    -- the members: cubes, shifts, kinds, data
    (z : I → SpatialCoordinates d) (r : I → ℝ) (hr : ∀ i, 0 < r i) (sh : I → ℕ)
    (hP : ∀ i, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (z i) (r i) (hr i)),
      ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (z i) (r i) (hr i))) u‖)
    (hP0 : ∀ i, ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph (centeredCube (z i) (r i) (hr i)),
      ‖(u : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (centeredCube (z i) (r i) (hr i))) u‖)
    (kind : I → Fin 3)
    (b : ∀ i, weakSobolevGraph (centeredCube (z i) (r i) (hr i)))
    (fL : ∀ i, DomainL2 (centeredCube (z i) (r i) (hr i)))
    (pv : I → Fin d → ℝ)
    -- the signed forms `⟨f, G g⟩`
    (zP : Pol → SpatialCoordinates d) (rP : Pol → ℝ) (hrP : ∀ w, 0 < rP w) (shP : Pol → ℕ)
    (hPP : ∀ w, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (zP w) (rP w) (hrP w)),
      ‖(u : SobolevData (centeredCube (zP w) (rP w) (hrP w))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (zP w) (rP w) (hrP w))) u‖)
    (fP gP : ∀ w, DomainL2 (centeredCube (zP w) (rP w) (hrP w)))
    -- orders and the band-approximation data
    (p q : ℝ≥0∞) [hp : Fact (1 ≤ p)] (hpq : p < q) (hq : q ≠ ∞)
    (a : ℝ) (ha : 0 < a) (Cp : I → ℝ) (Kb : I → ℝ≥0∞) (hKb : ∀ i, Kb i ≠ ∞)
    (CpP : Pol → ℝ) (KbP : Pol → ℝ≥0∞) (hKbP : ∀ w, KbP w ≠ ∞) :
    let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
    let Rsp : I → ℕ → BilateralField d → ℝ := fun i N omega =>
      let ac : PositiveCoefficient (centeredCube (z i) (r i) (hr i)) :=
        cutoffPositiveCoefficient M H omega (N + sh i) (z i) (hr i)
      match (kind i).val with
      | 0 => dirichletResponse (killedResponseSpace (hP i)) ac (b i)
      | 1 => inverseResponse (killedResponseSpace (hP i)) ac
          ((sobolevVolumeLoad (fL i)).comp (killedResponseSpace (hP i)).space.subtypeL)
      | _ => affineInverseNeumannResponse (hP0 i) ac (pv i)
    let Rpm : Pol → Bool → ℕ → BilateralField d → ℝ := fun w s N omega =>
      let ac : PositiveCoefficient (centeredCube (zP w) (rP w) (hrP w)) :=
        cutoffPositiveCoefficient M H omega (N + shP w) (zP w) (hrP w)
      inverseResponse (killedResponseSpace (hPP w)) ac
        ((sobolevVolumeLoad (if s then fP w + gP w else fP w - gP w)).comp
          (killedResponseSpace (hPP w)).space.subtypeL)
    let Gpol : Pol → ℕ → BilateralField d → ℝ := fun w N omega =>
      (1 / 4 : ℝ) * (Rpm w true N omega - Rpm w false N omega)
    -- hypotheses: moments and `eq:mfd-16` for every member and every one of the two responses of a signed form
    (∀ (i : I) (N : ℕ), MemLp (Rsp i N) q P) →
    (∀ (i : I) (N : ℕ), eLpNorm (Rsp i N) q P ≤ Kb i) →
    (∀ (i : I) (h N : ℕ), h ≤ N →
      eLpNorm (fun om => Rsp i N om -
          (P[Rsp i N | bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) om) p P ≤
        ENNReal.ofReal (Cp i * M.delta * (3 : ℝ) ^ (-(a * (h : ℝ))))) →
    (∀ (w : Pol) (s : Bool) (N : ℕ), MemLp (Rpm w s N) q P) →
    (∀ (w : Pol) (s : Bool) (N : ℕ), eLpNorm (Rpm w s N) q P ≤ KbP w) →
    (∀ (w : Pol) (s : Bool) (h N : ℕ), h ≤ N →
      eLpNorm (fun om => Rpm w s N om -
          (P[Rpm w s N | bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) om) p P ≤
        ENNReal.ofReal (CpP w * M.delta * (3 : ℝ) ^ (-(a * (h : ℝ))))) →
    -- (i) relative compactness in `L^p(P)`
    (∀ (i : I) (hmem : ∀ N, MemLp (Rsp i N) p P),
      IsCompact (closure (Set.range (fun N : ℕ => (hmem N).toLp (Rsp i N))))) ∧
    -- (ii) the same for the signed forms
    (∀ (w : Pol) (hmem : ∀ N, MemLp (Gpol w N) p P),
      IsCompact (closure (Set.range (fun N : ℕ => (hmem N).toLp (Gpol w N))))) ∧
    -- (iii) one extraction for all members, shifts and signed forms; every `L^p` limit is layer-measurable
    (∃ (phi : ℕ → ℕ), StrictMono phi ∧
      ∃ (Rlim : I → BilateralField d → ℝ) (Glim : Pol → BilateralField d → ℝ),
        (∀ i, MemLp (Rlim i) p P) ∧ (∀ w, MemLp (Glim w) p P) ∧
        (∀ i, Tendsto (fun N => eLpNorm (fun om => Rsp i (phi N) om - Rlim i om) p P)
          atTop (𝓝 0)) ∧
        (∀ w, Tendsto (fun N => eLpNorm (fun om => Gpol w (phi N) om - Glim w om) p P)
          atTop (𝓝 0)) ∧
        (∀ i, AEStronglyMeasurable[⨆ h : ℕ, bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]
          (Rlim i) P) ∧
        (∀ w, AEStronglyMeasurable[⨆ h : ℕ, bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]
          (Glim w) P)) ∧
    (∀ (i : I) (psi : ℕ → ℕ), StrictMono psi → ∀ f : BilateralField d → ℝ, MemLp f p P →
      Tendsto (fun N => eLpNorm (fun om => Rsp i (psi N) om - f om) p P) atTop (𝓝 0) →
      AEStronglyMeasurable[⨆ h : ℕ, bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h] f P) ∧
    (∀ (w : Pol) (psi : ℕ → ℕ), StrictMono psi → ∀ f : BilateralField d → ℝ, MemLp f p P →
      Tendsto (fun N => eLpNorm (fun om => Gpol w (psi N) om - f om) p P) atTop (𝓝 0) →
      AEStronglyMeasurable[⨆ h : ℕ, bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h] f P) := by
  classical
  intro P Rsp Rpm Gpol hm hb hband hmP hbP hbandP
  let Robj : ∀ i, Response (centeredCube (z i) (r i) (hr i)) := fun i =>
    match (kind i).val with
    | 0 => dirichletResponseData (killedResponseSpace (hP i)) (b i)
    | 1 => inverseResponseData (killedResponseSpace (hP i))
        ((sobolevVolumeLoad (fL i)).comp (killedResponseSpace (hP i)).space.subtypeL)
    | _ => affineInverseNeumannResponseObj (hP0 i) (pv i)
  let RobjP : ∀ w, Bool → Response (centeredCube (zP w) (rP w) (hrP w)) := fun w s =>
    inverseResponseData (killedResponseSpace (hPP w))
      ((sobolevVolumeLoad (if s then fP w + gP w else fP w - gP w)).comp
        (killedResponseSpace (hPP w)).space.subtypeL)
  have hRspEq : ∀ i N, Rsp i N =
      aux_g9_neumann_response_wrapper_generic_RTrue (z i) (r i) (hr i) (Robj i) M H (N + sh i) := by
    intro i N
    funext omega
    dsimp only [Rsp, Robj, aux_g9_neumann_response_wrapper_generic_RTrue]
    split <;> simp only [dirichletResponseData, inverseResponseData,
      affineInverseNeumannResponseObj, _root_.SubdiffusiveProcess.ResponseMoments.Response.ofExpComparison]
    all_goals rw [← aux_lem_local_normalizations_lnorm_proxy_pot_eq_coefficient]
  have hRpmEq : ∀ w s N, Rpm w s N =
      aux_g9_neumann_response_wrapper_generic_RTrue (zP w) (rP w) (hrP w) (RobjP w s) M H (N + shP w) := by
    intro w s N
    funext omega
    dsimp only [Rpm, RobjP, aux_g9_neumann_response_wrapper_generic_RTrue, inverseResponseData]
    rw [← aux_lem_local_normalizations_lnorm_proxy_pot_eq_coefficient]
  have hm2 : ∀ i N, MemLp (Rsp i N) p P := fun i N => (hm i N).mono_exponent hpq.le
  have hmP2 : ∀ w s N, MemLp (Rpm w s N) p P := fun w s N => (hmP w s N).mono_exponent hpq.le
  have hc : ∀ i, IsCompact (closure (Set.range (fun N => (hm2 i N).toLp (Rsp i N)))) := by
    intro i
    have hmi : ∀ N, MemLp (aux_g9_neumann_response_wrapper_generic_RTrue
        (z i) (r i) (hr i) (Robj i) M H (N + sh i)) q P := by
      intro N
      rw [← hRspEq i N]
      exact hm i N
    have hci := aux_mfd_prop_response_compact_response (z i) (r i) (hr i) (Robj i)
      M H _hH (sh i) p q hpq hq a (Cp i) ha (Kb i) (hKb i) hmi
      (by intro N; rw [← hRspEq i N]; exact hb i N)
      (by intro h N hN; rw [← hRspEq i N]; exact hband i h N hN)
    have heq : (fun N => (hm2 i N).toLp (Rsp i N)) =
        (fun N => ((hmi N).mono_exponent hpq.le).toLp
          (aux_g9_neumann_response_wrapper_generic_RTrue (z i) (r i) (hr i) (Robj i) M H (N + sh i))) := by
      funext N
      exact MemLp.toLp_congr _ _ (Eventually.of_forall (congrFun (hRspEq i N)))
    rwa [heq]
  have hcP : ∀ w s, IsCompact (closure (Set.range (fun N => (hmP2 w s N).toLp (Rpm w s N)))) := by
    intro w s
    have hmi : ∀ N, MemLp (aux_g9_neumann_response_wrapper_generic_RTrue
        (zP w) (rP w) (hrP w) (RobjP w s) M H (N + shP w)) q P := by
      intro N
      rw [← hRpmEq w s N]
      exact hmP w s N
    have hci := aux_mfd_prop_response_compact_response (zP w) (rP w) (hrP w) (RobjP w s)
      M H _hH (shP w) p q hpq hq a (CpP w) ha (KbP w) (hKbP w) hmi
      (by intro N; rw [← hRpmEq w s N]; exact hbP w s N)
      (by intro h N hN; rw [← hRpmEq w s N]; exact hbandP w s h N hN)
    have heq : (fun N => (hmP2 w s N).toLp (Rpm w s N)) =
        (fun N => ((hmi N).mono_exponent hpq.le).toLp
          (aux_g9_neumann_response_wrapper_generic_RTrue (zP w) (rP w) (hrP w) (RobjP w s) M H (N + shP w))) := by
      funext N
      exact MemLp.toLp_congr _ _ (Eventually.of_forall (congrFun (hRpmEq w s N)))
    rwa [heq]
  have hmG : ∀ w N, MemLp (Gpol w N) p P := by
    intro w N
    exact ((hmP2 w true N).sub (hmP2 w false N)).const_mul (1 / 4 : ℝ)
  have hcG : ∀ w, IsCompact (closure (Set.range (fun N => (hmG w N).toLp (Gpol w N)))) := by
    intro w
    let F : Lp ℝ p P × Lp ℝ p P → Lp ℝ p P := fun x => (1 / 4 : ℝ) • (x.1 - x.2)
    refine aux_compact_image_pair
      (fun N => (hmP2 w true N).toLp (Rpm w true N))
      (fun N => (hmP2 w false N).toLp (Rpm w false N)) (hcP w true) (hcP w false)
      F (by dsimp only [F]; fun_prop)
      (fun N => (hmG w N).toLp (Gpol w N)) ?_
    intro N
    apply Lp.ext
    filter_upwards [(hmG w N).coeFn_toLp, (hmP2 w true N).coeFn_toLp,
      (hmP2 w false N).coeFn_toLp,
      Lp.coeFn_smul (1 / 4 : ℝ) ((hmP2 w true N).toLp (Rpm w true N) -
        (hmP2 w false N).toLp (Rpm w false N)),
      Lp.coeFn_sub ((hmP2 w true N).toLp (Rpm w true N))
        ((hmP2 w false N).toLp (Rpm w false N))] with om h1 h2 h3 h4 h5
    simp only [F, h1, h4, h5, h2, h3, Gpol, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have hfull : (⨆ h : ℕ, bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h) =
      (inferInstance : MeasurableSpace (BilateralField d)) := iSup_bandFiltration
  refine ⟨(fun i _ => hc i), (fun w _ => hcG w), ?_, ?_, ?_⟩
  · obtain ⟨phi, hphi, Rlim, Glim, hRm, hGm, hRconv, hGconv⟩ :=
      aux_mfd_prop_response_compact_joint P I Pol Rsp Gpol p hm2 hmG hc hcG
    refine ⟨phi, hphi, Rlim, Glim, hRm, hGm, hRconv, hGconv, ?_, ?_⟩
    · intro i
      rw [hfull]
      exact (hRm i).aestronglyMeasurable
    · intro w
      rw [hfull]
      exact (hGm w).aestronglyMeasurable
  · intro i psi hpsi f hf hconv
    rw [hfull]
    exact hf.aestronglyMeasurable
  · intro w psi hpsi f hf hconv
    rw [hfull]
    exact hf.aestronglyMeasurable


end SubdiffusiveProcess.Paper
