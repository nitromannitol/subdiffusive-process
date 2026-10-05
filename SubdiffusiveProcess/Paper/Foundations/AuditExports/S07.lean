module

public import SubdiffusiveProcess.Paper.mfd_lem_15
public import SubdiffusiveProcess.Paper.mfd_prop_16
public import SubdiffusiveProcess.Paper.mfd_thm_fold
public import SubdiffusiveProcess.Paper.inputs_hES_witness
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.Paper

noncomputable section
namespace SubdiffusiveProcess.AuditExports

/-- The actual cube supplies its killed Poincaré inequality. -/
theorem cubeKilledPoincare {d : ℕ} (hd : 0 < d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖ := by
  let : NeZero d := ⟨ne_of_gt hd⟩
  exact (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain _
    (isOpenBoundedConvexDomain_centeredCube z hr)).1

/-- The actual cube supplies its mean-zero Poincaré inequality. -/
theorem cubeMeanZeroPoincare {d : ℕ} (hd : 0 < d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (centeredCube z r hr)) u‖ := by
  let : NeZero d := ⟨ne_of_gt hd⟩
  exact (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain _
    (isOpenBoundedConvexDomain_centeredCube z hr)).2

/-- Poincaré on every odd-grid killed cell, supplied from its literal cube geometry. -/
theorem gridKilledPoincare {d : ℕ} (hd : 0 < d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∀ J (k : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
      ∀ u : killedSobolevGraph (oddGridCell z r hr (triadicHalf J) k),
        ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) k)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (oddGridCell z r hr (triadicHalf J) k)) u‖ := by
  intro J k
  exact cubeKilledPoincare hd _ (div_pos hr (by positivity))

/-- Poincaré on every odd-grid mean-zero cell, supplied from its literal cube geometry. -/
theorem gridMeanZeroPoincare {d : ℕ} (hd : 0 < d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∀ J (k : OddGridIndex d (triadicHalf J)), ∃ K : ℝ≥0,
      ∀ u : meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) k),
        ‖(u : SobolevData (oddGridCell z r hr (triadicHalf J) k)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (oddGridCell z r hr (triadicHalf J) k)) u‖ := by
  intro J k
  exact cubeMeanZeroPoincare hd _ (div_pos hr (by positivity))

/-- Normalize an arbitrary positive scalar before taking the logarithmic potential. -/
def normalizedPotential {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (a : C(closedCube z r hr, ℝ)) (ha : ∀ x, 0 < a x) (a₀ : ℝ) (ha₀ : 0 < a₀) :
    C(closedCube z r hr, ℝ) :=
  ⟨fun x => Real.log (a x / a₀),
    (a.continuous.div_const a₀).log (fun x => ne_of_gt (div_pos (ha x) ha₀))⟩

/-- `mfd:thm-fold` for every continuous positive coefficient and every positive normalizer.
The displayed discounted sums are the two squared errors with their common positive
factor `1 - 3^(-2*s)` canceled, exactly as in the existing folding export. -/
theorem foldingComparison {d : ℕ} (hd : 0 < d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (m : ℕ) (I P : Finset (Fin d))
    (a : C(closedCube z r hr, ℝ)) (ha : ∀ x, 0 < a x)
    (a₀ : ℝ) (ha₀ : 0 < a₀) {s : ℝ} (hs : 0 < s) (hs1 : s < 1 / 2) :
    let g := normalizedPotential z hr a ha a₀ ha₀
    let coeff := expPotentialCoefficient (compactPotentialLp (Ω := centeredCube z r hr)
      (closedCube z r hr) g)
    let folded := expPotentialCoefficient (compactPotentialLp (Ω := centeredCube z r hr)
      (closedCube z r hr) (g.comp (coordinateFoldOnCube z hr I P)))
    (∑' n : ℕ, ((3 : ℝ)^(-(2*s)))^n * triadicDefectSup z hr
      (gridKilledPoincare hd z hr) (gridMeanZeroPoincare hd z hr) folded hd (m+n)) ≤
      (1 + 3*(d : ℝ)/((3 : ℝ)^(1-2*s)-1)) *
        ∑' n : ℕ, ((3 : ℝ)^(-(2*s)))^n * triadicDefectSup z hr
          (gridKilledPoincare hd z hr) (gridMeanZeroPoincare hd z hr) coeff hd (m+n) := by
  exact mfd_thm_fold z hr (gridKilledPoincare hd z hr)
    (gridMeanZeroPoincare hd z hr) hd m I P (normalizedPotential z hr a ha a₀ ha₀) hs hs1

/-- The coefficient in `foldingComparison` is literally `a/a₀` on the open cube. -/
theorem normalizedPotential_coefficient {d : ℕ}
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (a : C(closedCube z r hr, ℝ)) (ha : ∀ x, 0 < a x)
    (a₀ : ℝ) (ha₀ : 0 < a₀) :
    ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∀ hx : x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
        (expPotentialCoefficient (compactPotentialLp (Ω := centeredCube z r hr)
          (closedCube z r hr) (normalizedPotential z hr a ha a₀ ha₀))).val x =
            a ⟨x, hx⟩ / a₀ := by
  filter_upwards [expPotentialCoefficient_coeFn
    (compactPotentialLp (Ω := centeredCube z r hr) (closedCube z r hr)
      (normalizedPotential z hr a ha a₀ ha₀)),
    compactPotentialLp_on_domain (Ω := centeredCube z r hr) (closedCube z r hr)
      (centeredCube_subset_closedCube z hr) (normalizedPotential z hr a ha a₀ ha₀),
    self_mem_ae_restrict (centeredCube z r hr).isOpen.measurableSet] with x he hg hx
  intro hx'
  rw [he, hg hx]
  exact Real.exp_log (div_pos (ha _) ha₀)

/-- `mfd:lem-15` on the actual response carriers, including zero source and constant trace.
The uniform response theorem has no nontriviality or Efron–Stein premise. -/
theorem resamplingEstimate
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (b : weakSobolevGraph (centeredCube z r hr))
    (fL2 : DomainL2 (centeredCube z r hr))
    (t p B : ℝ) (ht_lower : (d : ℝ) - 1 < t) (ht_upper : t < (d : ℝ))
    (hp : 2 ≤ p) (hB : 0 ≤ B) (dirichlet : Bool) :
    let S := killedResponseSpace (cubeKilledPoincare (by omega : 0 < d) z hr)
    let L := (sobolevVolumeLoad fL2).comp S.space.subtypeL
    ∃ C : ℝ, 0 < C ∧
      ∀ (delta : ℝ), 0 < delta → delta ≤ 1 →
        ∀ (Praw : ProbabilityMeasure (_root_.SubdiffusiveProcess.Model.PotentialSample d))
          (_G1 : _root_.SubdiffusiveProcess.Model.ShellLawG1 d Praw)
          (_G2 : _root_.SubdiffusiveProcess.Model.ShellLawG2 d delta Praw),
          let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d,
              C(SpatialCoordinates d, ℝ)) :=
            ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
          let nu := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw Praw).map
            forget
          let P := (commonScaleLaw d nu).toMeasure
          ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
            Measurable H →
            (∀ᵐ omega ∂P,
              Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega))) →
          ∀ (kappa : ℕ → ℝ), (∀ N, 0 < kappa N) →
          ∀ (aN : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr)),
            (∀ N omega,
              (aN N omega).val =ᵐ[volume.restrict
                (centeredCube z r hr : Set (SpatialCoordinates d))]
                (fun x => Real.exp (cutoffPotential H omega N x - Real.log (kappa N)))) →
          let RN : ℕ → BilateralField d → ℝ :=
            fun N omega =>
              if dirichlet then
                dirichletResponse S (aN N omega) b
              else
                inverseResponse S (aN N omega) L
          let gN : ℕ → BilateralField d → HilbertGradient (centeredCube z r hr) :=
            fun N omega =>
              if dirichlet then
                sobolevGradient (dirichletMinimizer S (aN N omega) b).val
              else
                subspaceGradient S.space (responseSolution S (aN N omega) L)
          ∀ (K : ℕ → BilateralField d → ℝ),
            ((∀ N, AEStronglyMeasurable (K N) P) ∧
            (∀ᵐ omega ∂P, ∀ N, 0 ≤ K N omega)) →
            (∀ᵐ omega ∂P, ∀ N, ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
              ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
                localGradientEnergy (aN N omega)
                  (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
                  (gN N omega) ≤ K N omega * rho ^ t) →
            (∀ N,
              MemLp (K N) (ENNReal.ofReal (3 * p)) P ∧
              MemLp (RN N) (ENNReal.ofReal (3 * p)) P ∧
              eLpNorm (K N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B ∧
              eLpNorm (RN N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
            ∀ (N j : ℕ), j ≤ N →
              eLpNorm
                (fun pair : BilateralField d × BilateralField d =>
                  RN N pair.1 -
                    RN N
                      (Function.update pair.1 (-(j : ℤ))
                        (pair.2 (-(j : ℤ)))))
                (ENNReal.ofReal p) (P.prod P) ≤
              ENNReal.ofReal
                (C * delta *
                  (3 : ℝ) ^
                  (-(t * (t - (d : ℝ) + 1) / (t + 1) /
                      8) * (j : ℝ)))
    := by
  intro S L
  obtain ⟨A, hA, hest⟩ := aux_mfd_lem_15_uniform d hd z r hr t p ht_lower hp
  refine ⟨A * B + 1, by positivity, ?_⟩
  intro delta hdelta hdelta1 Praw G1 G2 forget nu P H hH hHconv kappa _ aN haN
    RN gN K hK hgrowth hmom N j hjN
  have h := hest B hB S dirichlet b L delta hdelta hdelta1 Praw G1 G2
    H hH hHconv kappa aN haN K hK.1 hK.2 hgrowth N j hjN
    (hmom N).2.2.1 (hmom N).2.2.2
  exact h.trans (ENNReal.ofReal_le_ofReal (by gcongr; linarith))

/-- The Dirichlet/source clauses of `mfd:prop-16`, with all zero-response cases retained. -/
theorem conditioningEstimate :
  ∀ (d : ℕ) (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (b : weakSobolevGraph (centeredCube z r hr))
    (fL2 : DomainL2 (centeredCube z r hr))
    (t p B : ℝ) (_ht_lower : (d : ℝ) - 1 < t) (_ht_upper : t < (d : ℝ))
    (_hp : 2 ≤ p) (_hB : 0 ≤ B) (dirichlet : Bool),
    let S := killedResponseSpace (cubeKilledPoincare (by omega : 0 < d) z hr)
    let L := (sobolevVolumeLoad fL2).comp S.space.subtypeL
    ∃ C : ℝ, 0 < C ∧
      ∀ (delta : ℝ), 0 < delta → delta ≤ 1 →
        ∀ (Praw : ProbabilityMeasure (_root_.SubdiffusiveProcess.Model.PotentialSample d))
          (_G1 : _root_.SubdiffusiveProcess.Model.ShellLawG1 d Praw)
          (_G2 : _root_.SubdiffusiveProcess.Model.ShellLawG2 d delta Praw),
          let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d,
              C(SpatialCoordinates d, ℝ)) :=
            ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
          let nu := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw Praw).map
            forget
          let P := (commonScaleLaw d nu).toMeasure
          ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
            Measurable H →
            (∀ᵐ omega ∂P,
              Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega))) →
            ∀ (kappa : ℕ → ℝ), (∀ N, 0 < kappa N) →
            ∀ (aN : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr)),
              (∀ N omega,
                (aN N omega).val =ᵐ[volume.restrict
                  (centeredCube z r hr : Set (SpatialCoordinates d))]
                  (fun x => Real.exp (cutoffPotential H omega N x - Real.log (kappa N)))) →
            let RN : ℕ → BilateralField d → ℝ :=
            fun N omega =>
              if dirichlet then
                dirichletResponse S (aN N omega) b
              else
                inverseResponse S (aN N omega) L
          let gN : ℕ → BilateralField d → HilbertGradient (centeredCube z r hr) :=
            fun N omega =>
              if dirichlet then
                sobolevGradient (dirichletMinimizer S (aN N omega) b).val
              else
                subspaceGradient S.space (responseSolution S (aN N omega) L)
          ∀ (K : ℕ → BilateralField d → ℝ),
            ((∀ N, AEStronglyMeasurable (K N) P) ∧
            (∀ᵐ omega ∂P, ∀ N, 0 ≤ K N omega)) →
            (∀ᵐ omega ∂P, ∀ N, ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
              ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
                localGradientEnergy (aN N omega)
                  (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
                  (gN N omega) ≤ K N omega * rho ^ t) →
            (∀ N,
              MemLp (K N) (ENNReal.ofReal (3 * p)) P ∧
              MemLp (RN N) (ENNReal.ofReal (3 * p)) P ∧
              eLpNorm (K N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B ∧
              eLpNorm (RN N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
            (∀ h N : ℕ,
              let sigma_h := bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h
              eLpNorm
                (fun om => RN N om - (P[RN N | sigma_h]) om)
                (ENNReal.ofReal p) P ≤
              ENNReal.ofReal
                (C * delta *
                  (3 : ℝ) ^
                    (-(t * (t - (d : ℝ) + 1) / (t + 1) /
                        8) * (h : ℝ)))) ∧
            (∀ h N : ℕ, N < h →
              let sigma_h := bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h
              eLpNorm
                (fun om => RN N om - (P[RN N | sigma_h]) om)
                (ENNReal.ofReal p) P ≤
              ENNReal.ofReal
                (C * delta * (3 : ℝ) ^ (-(h : ℝ))))
    := by
  intro d hd instM instB z r hr b fL2
    t p B ht_lower ht_upper hp hB dirichlet S L
  have hP := cubeKilledPoincare (by omega : 0 < d) z hr
  obtain ⟨C15, hC15, h15⟩ := resamplingEstimate d hd z r hr b fL2
    t p B ht_lower ht_upper hp hB dirichlet
  obtain ⟨Ctail, hCtail, htail⟩ := aux_prop_16_coarse_tail d z r hr
  obtain ⟨Ccb, hCcb, hcb⟩ := prop_16_coarse_block_dirichlet d hd z r hr hP b fL2 t p B
    ht_lower ht_upper hp hB dirichlet Ctail hCtail
  obtain ⟨ha0, ha1⟩ := SubdiffusiveProcess.Section9LiveRate.influence_exponent_pos_le_one d hd t ht_lower ht_upper
  set a := t * (t - (d : ℝ) + 1) / (t + 1) / 8 with ha_def
  have hr1 : (3 : ℝ) ^ (-a) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h1r : 0 < 1 - (3 : ℝ) ^ (-a) := by linarith
  refine ⟨C15 / (1 - (3 : ℝ) ^ (-a)) + Ccb, by positivity, ?_⟩
  intro delta hdelta hdelta1 Praw G1 G2 forget nu P H hH hHconv kappa hkappa aN haN RN gN
    K hK hgrowth hmom
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ p)
  have hkey : ∀ h N : ℕ,
      eLpNorm (fun om => RN N om -
          (P[RN N | bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) om)
        (ENNReal.ofReal p) P ≤
      (∑ k ∈ Finset.Ioc h N,
          ENNReal.ofReal (C15 * delta * (3 : ℝ) ^ (-a * (k : ℝ)))) +
        ENNReal.ofReal (Ccb * delta * (3 : ℝ) ^ (-(h : ℝ))) := by
    intro h N
    have hRmem : MemLp (RN N) (ENNReal.ofReal (3 * p)) P := (hmom N).2.1
    have hRint : Integrable (RN N) P :=
      hRmem.integrable (by simpa using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ 3 * p))
    have hsplit := aux_prop_16_band_split
      (fun j : ℤ => (scaledLayerLaw d nu j : Measure C(SpatialCoordinates d, ℝ))) h hp1
      ENNReal.ofReal_ne_top hRint
    refine hsplit.trans ?_
    rw [add_comm]
    refine add_le_add ?_ ?_
    · have hdet : ∀ ω₁ ∈ {om : BilateralField d | Tendsto (infraredPartialSum om) atTop (𝓝 (H om))},
          ∀ ω₂ ∈ {om : BilateralField d | Tendsto (infraredPartialSum om) atTop (𝓝 (H om))},
          (∀ j : ℤ, -(N : ℤ) ≤ j → ω₁ j = ω₂ j) → RN N ω₁ = RN N ω₂ := by
        intro ω₁ h1 ω₂ h2 hagree
        have hH12 := aux_prop_16_infrared_eq H ω₁ ω₂ h1 h2 (fun j hj => hagree j (by omega))
        have hcut := aux_prop_16_cutoff_eq H ω₁ ω₂ N hH12 hagree
        have haeq : aN N ω₁ = aN N ω₂ := by
          apply Subtype.ext
          apply Lp.ext
          filter_upwards [haN N ω₁, haN N ω₂] with x hx1 hx2
          rw [hx1, hx2, hcut]
        simp only [RN, haeq]
      exact aux_prop_16_fine_telescope _ hp1 (RN N) hRmem.aestronglyMeasurable _ hHconv h N hdet
        (fun k => ENNReal.ofReal (C15 * delta * (3 : ℝ) ^ (-a * (k : ℝ))))
        (fun k _ hkN => h15 delta hdelta hdelta1 Praw G1 G2 H hH hHconv kappa hkappa aN haN
          K hK hgrowth hmom N k hkN)
    · have hcb' := hcb delta hdelta hdelta1 Praw G1 G2 H hH hHconv kappa hkappa aN haN
        (htail delta hdelta hdelta1 Praw G1 G2 H hH hHconv)
        (fun N => ⟨(hmom N).2.1, (hmom N).2.2.2⟩) h N
      have hTmp := measurePreserving_copy_infinitePi_block
        (fun j : ℤ => (scaledLayerLaw d nu j : Measure C(SpatialCoordinates d, ℝ)))
        {j : ℤ | (h : ℤ) < j}
      have hmeas : AEStronglyMeasurable (fun q : BilateralField d × BilateralField d =>
          RN N q.1 - RN N (fun j => if (h : ℤ) < j then q.2 j else q.1 j)) (P.prod P) :=
        (hRmem.aestronglyMeasurable.comp_measurePreserving measurePreserving_fst).sub
          (hRmem.aestronglyMeasurable.comp_measurePreserving hTmp)
      exact (eLpNorm_le_eLpNorm_of_exponent_le
        (ENNReal.ofReal_le_ofReal (by linarith))).trans hcb'
  refine ⟨fun h N => ?_, fun h N hNh => ?_⟩
  · refine (hkey h N).trans ?_
    have hg := aux_prop_16_geom a ha0 (C15 * delta) (by positivity) h N
    refine (add_le_add hg le_rfl).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h3 : (3 : ℝ) ^ (-(h : ℝ)) ≤ (3 : ℝ) ^ (-a * (h : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have : (0 : ℝ) ≤ h := Nat.cast_nonneg h
      nlinarith
    have h4 : 0 ≤ (3 : ℝ) ^ (-a * (h : ℝ)) := by positivity
    calc C15 * delta * (3 : ℝ) ^ (-a * (h : ℝ)) / (1 - (3 : ℝ) ^ (-a)) +
          Ccb * delta * (3 : ℝ) ^ (-(h : ℝ))
        ≤ C15 * delta * (3 : ℝ) ^ (-a * (h : ℝ)) / (1 - (3 : ℝ) ^ (-a)) +
          Ccb * delta * (3 : ℝ) ^ (-a * (h : ℝ)) := by gcongr
      _ = (C15 / (1 - (3 : ℝ) ^ (-a)) + Ccb) * delta * (3 : ℝ) ^ (-a * (h : ℝ)) := by
          field_simp
  · refine (hkey h N).trans ?_
    rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, zero_add]
    apply ENNReal.ofReal_le_ofReal
    have : 0 ≤ C15 / (1 - (3 : ℝ) ^ (-a)) := by positivity
    have h4 : 0 ≤ delta * (3 : ℝ) ^ (-(h : ℝ)) := by positivity
    nlinarith

end SubdiffusiveProcess.AuditExports
