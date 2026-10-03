module

public import SubdiffusiveProcess.Frozen.Section6.CutoffHolderRegularity


public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.CoarseGrainingVocab.Core
public import SubdiffusiveProcess.CoarseGrainingVocab.Norms
public import SubdiffusiveProcess.Frozen.Section6.Defs.HolderRegularityConclusions

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

attribute [local instance] Classical.propDecidable

namespace SubdiffusiveProcess.Lane4

attribute [local instance] Classical.propDecidable



structure SmallPerturbationInput (d : ℕ) where
  /-- The Meyers constant, which may depend on the exponent but not on the coefficient. -/
  C : ℝ → ℝ
  C_pos : ∀ p, 0 < C p
  /-- The smallness threshold on the logarithmic oscillation of the coefficient. -/
  osc : ℝ → ℝ
  osc_pos : ∀ p, 0 < osc p
  /-- The interior `W^{1,p_1}` estimate with normalized gradient norms, together with the
  membership of the Euclidean gradient length in `L^{p_1}` on the half-size ball. -/
  interior_gradient : ∀ (p1 : ℝ), 2 ≤ p1 → ∀ (x0 : SpatialCoordinates d) (l : ℝ)
      (hl : (0 : ℝ) < 4 * l) (a : PositiveCoefficient (centeredCube x0 (4 * l) hl))
      (a0 : ℝ), 0 < a0 →
      (∀ᵐ y ∂volume.restrict (centeredCube x0 (4 * l) hl : Set (SpatialCoordinates d)),
        |Real.log (a.val y) - Real.log a0| ≤ osc p1) →
      ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
        AEMeasurable F (volume.restrict (centeredCube x0 (4 * l) hl :
            Set (SpatialCoordinates d))) →
        0 ≤ Kf →
        (∀ᵐ y ∂volume.restrict (centeredCube x0 (4 * l) hl : Set (SpatialCoordinates d)),
          |F y| ≤ Kf) →
      ∀ u : weakSobolevGraph (centeredCube x0 (4 * l) hl),
        (∀ φ : killedSobolevGraph (centeredCube x0 (4 * l) hl),
          sobolevCoefficientForm a (u : SobolevData (centeredCube x0 (4 * l) hl))
              (φ : SobolevData (centeredCube x0 (4 * l) hl)) =
            ∫ y in (centeredCube x0 (4 * l) hl : Set (SpatialCoordinates d)),
              F y * (φ : SobolevData (centeredCube x0 (4 * l) hl)).1 y) →
        MemLp (fun y => Real.sqrt (∑ i : Fin d,
              ((sobolevGradient (u : SobolevData (centeredCube x0 (4 * l) hl))) i y) ^ 2))
            (ENNReal.ofReal p1)
            ((volume.restrict (centeredCube x0 (4 * l) hl : Set (SpatialCoordinates d))).restrict
              (Metric.ball x0 l)) ∧
          normalizedGradientLpNorm (ENNReal.ofReal p1) (Metric.ball x0 l)
              (sobolevGradient (u : SobolevData (centeredCube x0 (4 * l) hl))) ≤
            C p1 * normalizedGradientLpNorm 2 (Metric.ball x0 (2 * l))
                (sobolevGradient (u : SobolevData (centeredCube x0 (4 * l) hl))) +
              C p1 * l * a0⁻¹ * Kf
  /-- Morrey's inequality: the `W^{1,p_1}` bound on the ball gives a continuous
  representative that is Hölder there, with the seminorm bounded by
  `CMorrey p1 alpha * l ^ (1 - alpha)` times the volume-normalized gradient norm. -/
  CMorrey : ℝ → ℝ → ℝ
  CMorrey_pos : ∀ p alpha, 0 < CMorrey p alpha
  morrey : ∀ (p1 : ℝ), 2 ≤ p1 → ∀ (alpha : ℝ), 0 < alpha → alpha < 1 - (d : ℝ) / p1 →
      ∀ (x0 : SpatialCoordinates d) (l : ℝ) (hl : (0 : ℝ) < 4 * l)
      (u : weakSobolevGraph (centeredCube x0 (4 * l) hl)),
      MemLp (fun y => Real.sqrt (∑ i : Fin d,
            ((sobolevGradient (u : SobolevData (centeredCube x0 (4 * l) hl))) i y) ^ 2))
          (ENNReal.ofReal p1)
          ((volume.restrict (centeredCube x0 (4 * l) hl : Set (SpatialCoordinates d))).restrict
            (Metric.ball x0 l)) →
      ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
        ((u : SobolevData (centeredCube x0 (4 * l) hl)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[(volume.restrict (centeredCube x0 (4 * l) hl : Set (SpatialCoordinates d))).restrict
              (Metric.ball x0 l)] U ∧
        IsHolderOn alpha (Metric.closedBall x0 l) U ∧
        holderSeminorm alpha (Metric.closedBall x0 l) U ≤
          CMorrey p1 alpha * l ^ (1 - alpha) *
            normalizedGradientLpNorm (ENNReal.ofReal p1) (Metric.ball x0 l)
              (sobolevGradient (u : SobolevData (centeredCube x0 (4 * l) hl)))



structure CampanatoInput (d : ℕ) where
  /-- The Campanato constant may depend on the Hölder exponent. -/
  C : ℝ → ℝ
  C_pos : ∀ alpha, 0 < alpha → alpha < 1 → 0 < C alpha
  /-- Decay `⨍_{B_r(x) ∩ Q}|u - (u)_{B_r(x) ∩ Q}|² ≤ K² r^{2α}` at every centre and every
  radius below the size of the cube gives a continuous representative that is
  genuinely `α`-Hölder on the closed cube, with `C^α` seminorm at most
  `C alpha * K`. The `IsHolderOn` conjunct is substantive because
  `holderSeminorm` alone can have a junk `sSup` value for unbounded quotients. -/
  holder_of_campanato : ∀ (alpha : ℝ), 0 < alpha → alpha < 1 →
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
    ∀ (u : DomainL2 (centeredCube z r hr)) (K : ℝ), 0 ≤ K →
      (∀ x ∈ centeredCube z r hr, ∀ rad : ℝ, 0 < rad → rad ≤ r →
        ∫ y in Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)),
            (u y - setAverage
              (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) u) ^ 2
            ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
          K ^ 2 * rad ^ (2 * alpha) *
            volume.real (Metric.ball x rad ∩
              (centeredCube z r hr : Set (SpatialCoordinates d)))) →
      ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
        ((u : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U) ∧
        IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
        holderSeminorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤ C alpha * K



structure SobolevFoundationalInput (d : ℕ) (hd : 2 ≤ d) where
  C : ℝ
  C_pos : 0 < C
  /-- The Besov embedding constant, depending on the fixed exponent `s ∈ (0, 1/4)` only
  (not on the cube or the datum). -/
  CBesov : ℝ → ℝ
  CBesov_pos : ∀ s, s ∈ Set.Ioo (0 : ℝ) (1 / 4) → 0 < CBesov s
  /-- The Besov seminorm `[v]_{B^{t}_{2,∞}(z + Q_r)}` used by `e.nabla.u.detach`. -/
  besovSeminorm : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
    ℝ → DomainL2 (centeredCube z r hr) → ℝ
  besovSeminorm_nonneg : ∀ z r hr t v, 0 ≤ besovSeminorm z r hr t v
  /-- Actual `L²`-integrability of the root/overlap averages of the affine pullback
  `T x i = z i + r * x i` of `v` to `Homogenization.originCube d 0`, recording that the
  depth terms below are genuine normalized averages rather than free transported data. -/
  positive_integrable : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
    ∀ v : DomainL2 (centeredCube z r hr),
      Homogenization.ExactOverlapIntegrable (Homogenization.originCube d 0)
        (fun x => v (fun i : Fin d => z i + r * x i))
  /-- The Besov seminorm of positive order `t ∈ (0,1)` is the `r^{-t}`-rescaled supremum
  of the native exact overlapping-cube depth terms of the affine pullback. -/
  besovSeminorm_eq : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) (v : DomainL2 (centeredCube z r hr)),
      besovSeminorm z r hr t v =
        r ^ (-t) * (iSup fun j : ℕ =>
          Homogenization.exactOverlapDepthTerm (Homogenization.originCube d 0) t 2
            (fun x => v (fun i : Fin d => z i + r * x i))
            (positive_integrable z r hr v) j).toReal
  /-- For every `H^1` datum and every positive order `t ∈ (0,1)`, the extended depth
  `iSup` of the affine pullback is finite. -/
  besov_finite_H1 : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (t : ℝ)
      (ht : t ∈ Set.Ioo (0 : ℝ) 1) (u : weakSobolevGraph (centeredCube z r hr)),
      (iSup fun j : ℕ =>
        Homogenization.exactOverlapDepthTerm (Homogenization.originCube d 0) t 2
          (fun x => (u : SobolevData (centeredCube z r hr)).1
            (fun i : Fin d => z i + r * x i))
          (positive_integrable z r hr (u : SobolevData (centeredCube z r hr)).1) j) < ⊤
  /-- Every `H^1` datum lies in the genuine (finite) fractional `H^{3/4}` domain. -/
  h1_fractional_finite : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
    ∀ u : weakSobolevGraph (centeredCube z r hr),
      cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
        (fun _ : Fin 1 => (u : SobolevData (centeredCube z r hr)).1) < ⊤
  /-- Used in Lemma `mfd:lem-coercivity` (paper lines 396–401): the embedding
  `B^{1-s}_{2,∞}(Q) ⊂ H^{3/4}(Q)`, strict since `1 - s > 3/4` for `s ∈ (0,1/4)`.  The
  datum is restricted to the genuine finite Besov domain by the extended `iSup` guard,
  and the `L²` factor is the volume-normalized square root term of the cube, matched to
  the normalized convention of `cubeFractionalSqNorm`. -/
  besov_embedding : ∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) (1 / 4) →
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
    ∀ v : DomainL2 (centeredCube z r hr),
      (iSup fun j : ℕ =>
        Homogenization.exactOverlapDepthTerm (Homogenization.originCube d 0) (1 - s) 2
          (fun x => v (fun i : Fin d => z i + r * x i))
          (positive_integrable z r hr v) j) < ⊤ →
      cubeFractionalSqNorm hd z r hr threeQuarterOrder v ≤
        CBesov s * (besovSeminorm z r hr (1 - s) v ^ 2 +
          ‖v‖ ^ 2 / volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))
  /-- Used in Lemma `mfd:lem-load` (paper lines 790-807): a bounded extension operator
  `H^{3/4}(Q) → H^{3/4}(ℝ^d)`.  The datum must genuinely be in `H^{3/4}`: the guard is
  the extended-valued seminorm itself, not its `toReal` shadow, since
  `(⊤ : ℝ≥0∞).toReal = 0`. -/
  extension : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
    ∀ v : DomainL2 (centeredCube z r hr),
      cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => v) < ⊤ →
      ∃ V : SpatialCoordinates d → ℝ,
        ((v : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] V) ∧
        globalFractionalSqNorm (3 / 4) V ≤
          ENNReal.ofReal (C * cubeFractionalSqNorm hd z r hr threeQuarterOrder v)
  /-- Interpolation `‖·‖_{H^{1/2}} ≤ ‖·‖_{L²}^{1/3} ‖·‖_{H^{3/4}}^{2/3}`, with the `L²`
  factor normalized by the cube volume, as the normalized `H^s` convention of
  `cubeFractionalSqNorm` requires. -/
  interpolation : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
    ∀ v : DomainL2 (centeredCube z r hr),
      cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => v) < ⊤ →
      Real.sqrt (cubeFractionalSqNorm hd z r hr ⟨1 / 2, by norm_num, by norm_num⟩ v) ≤
        C * (‖v‖ /
            Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) ^ (1 / 3 : ℝ) *
          Real.sqrt (cubeFractionalSqNorm hd z r hr threeQuarterOrder v) ^ (2 / 3 : ℝ)
  /-- The compact embedding `H^{3/4}(Q) ⊂⊂ L²(Q)`.  The genuine `H^{3/4}` membership of
  every term is required before the uniform real bound, so that a sequence outside
  `H^{3/4}` cannot enter through the `toReal` junk value. -/
  compactEmbedding : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
    ∀ (v : ℕ → DomainL2 (centeredCube z r hr)) (B : ℝ),
      (∀ n, cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => v n) < ⊤) →
      (∀ n, cubeFractionalSqNorm hd z r hr threeQuarterOrder (v n) ≤ B) →
      ∃ (phi : ℕ → ℕ) (w : DomainL2 (centeredCube z r hr)),
        StrictMono phi ∧ Filter.Tendsto (fun n => v (phi n)) Filter.atTop (nhds w)
  /-- The zero-extension bound for `H^{3/4}_0(Q)`: extending a killed variation by zero
  costs only the constant `C`. -/
  zeroExtension : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
    ∀ v : killedSobolevGraph (centeredCube z r hr),
      ∃ V : SpatialCoordinates d → ℝ,
        ((v : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] V ∧
        (∀ x, x ∉ (closedCube z r hr : Set (SpatialCoordinates d)) → V x = 0) ∧
        globalFractionalSqNorm (3 / 4) V ≤
          ENNReal.ofReal (C * cubeFractionalSqNorm hd z r hr threeQuarterOrder
            (v : SobolevData (centeredCube z r hr)).1)
  /-- The trace constant, depending on `beta` only. -/
  CTrace : ℝ → ℝ
  CTrace_pos : ∀ beta, 0 < CTrace beta
  /-- Used in Lemma `mfd:lem-extension` (paper lines 478-485): the source's unit-cube
  trace-extension input.  A boundary datum `G` that is Hölder-`beta` on the frontier of
  the unit cube has an `H^1` cube element `b` realizing it, with a continuous global
  representative `U` that agrees with `b` inside the cube and equals `G` **on the
  frontier**, whose gradient components lie in `H^sigma` with `sigma = (beta - 1/2)/2`,
  and whose gradient energy is bounded by `CTrace beta` times the squared Hölder data.
  The right inverse identifies only the boundary trace: `b` is tied to `U` inside the
  cube and to `G` on the frontier; no condition is imposed on the values of `G` off the
  boundary, and `b.value = G` inside the cube is never demanded.  The paper rescales this
  unit-cube input in its own argument; that scaling is not an input field here. -/
  traceRightInverse : ∀ (beta : ℝ) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1),
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r = 1 →
    ∀ (G : SpatialCoordinates d → ℝ),
      IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
      ∃ b : weakSobolevGraph (centeredCube z r hr),
        ∃ U : SpatialCoordinates d → ℝ,
          Continuous U ∧
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
          (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = G x) ∧
          (∀ i : Fin d,
            cubeFractionalL2Seminorm hd z r hr
              ⟨(beta - 1 / 2) / 2, by
                have h1 := hbeta.1
                have h2 := hbeta.2
                constructor <;> simp only [Set.mem_Ioo] at * <;> linarith⟩
              (fun _ : Fin 1 => ((b : SobolevData (centeredCube z r hr)).2 i)) < ⊤) ∧
          ∑ i : Fin d,
              cubeFractionalSqNorm hd z r hr
                ⟨(beta - 1 / 2) / 2, by
                  have h1 := hbeta.1
                  have h2 := hbeta.2
                  constructor <;> simp only [Set.mem_Ioo] at * <;> linarith⟩
                ((b : SobolevData (centeredCube z r hr)).2 i) ≤
            CTrace beta * (r ^ beta *
              holderSeminorm beta
                (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2




structure PaperSourcedRegularity (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) where
  /-- The stationary cutoff coefficient `a_L` on the cube `y + Q_{3^m}`. -/
  cutoffOn : ∀ (_L : ℕ) (_om : BilateralField d) (y : SpatialCoordinates d) (R : ℝ)
    (hR : 0 < R), PositiveCoefficient (centeredCube y R hR)
  cutoffOn_eq : ∀ (L : ℕ) (om : BilateralField d) (y : SpatialCoordinates d)
      (R : ℝ) (hR : 0 < R),
    ∀ᵐ x ∂volume.restrict (centeredCube y R hR : Set (SpatialCoordinates d)),
      (cutoffOn L om y R hR).val x =
        Real.exp ((∑ j ∈ Finset.range (L + 1), (om (j : ℤ)) x) -
          (L + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
  /-- The random prefix length `𝓛_L(α,m)`. -/
  prefixLen : ℕ → ℝ → ℕ → SpatialCoordinates d → BilateralField d → ℕ
  prefix_measurable : ∀ L alpha m y, Measurable (prefixLen L alpha m y)
  prefix_pos : ∀ L alpha m y om, 0 < prefixLen L alpha m y om
  /-- The original reference average `(b_{L,m})_{y+Q_{3^m}}`. -/
  refAvg : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ
  refAvg_pos : ∀ L m y om, 0 < refAvg L m y om
  refAvg_eq : ∀ (L m : ℕ) (y : SpatialCoordinates d) (om : BilateralField d)
      (hR : 0 < (3 : ℝ) ^ m),
    refAvg L m y om =
      (volume.real (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)))⁻¹ *
        ∫ x in (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)),
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M (min m L) *
            Real.exp ((∑ j ∈ Finset.range (L + 1), (om (j : ℤ)) x) -
              (∑ j ∈ Finset.range (min m L + 1), (om (j : ℤ)) x) -
              ((L : ℝ) - (min m L : ℝ)) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
  C : ℝ
  C_pos : 0 < C
  /-- Dimensional constants may be enlarged to at least `1`; this explicitly covers
  `k = 0` in the tail, where the upstream theorem only states `k > 0`. -/
  C_ge_one : 1 ≤ C
  /-- The constant `C` is a dimension-only enlarged witness of the already-frozen upstream
  export `SubdiffusiveProcess.Frozen.Section6.cutoff_holder_regularity`, whose statement binds `∃C` before
  `∀M`: hence `C` precedes `M` semantically and depends only on the dimension `d`.  The
  enlarging factor `((d : ℝ) + 1)^2` accommodates the equivalent Euclidean and Pi vector
  norm conventions used in this project and upstream, and `max 1 ·` keeps the source's
  freedom to enlarge dimensional constants.  Both source estimates,
  `e.Holder.estimate.boxes.local` and `eq:mfd-6.3`, use this same constant.  This is a
  defining equation of the input's constant, not a proof or a new theorem. -/
  C_eq_dimensional :
    C = ((d : ℝ) + 1) ^ 2 *
      max 1 (Classical.choose (SubdiffusiveProcess.Frozen.Section6.cutoff_holder_regularity d))
  /-- The paper's Hölder range, line 285. -/
  alphaRange : Set ℝ
  alphaRange_eq : alphaRange =
    Set.Icc (1 / 2 : ℝ) (1 - C * M.delta * Real.sqrt |Real.log M.delta|)
  /-- `eq:mfd-L-tail`, uniform in `L`, `m` and the deterministic centre. -/
  tail : ∀ (L : ℕ) (alpha : ℝ), M.delta ≤ C⁻¹ → alpha ∈ alphaRange → ∀ (m : ℕ) (y : SpatialCoordinates d) (k : ℕ),
    (chaosSampleLaw M).toMeasure {om | k < prefixLen L alpha m y om} ≤
      ENNReal.ofReal (C * Real.exp (-((1 - alpha) ^ 2 * (max ((k : ℝ) - C) 0) /
        (C * M.delta ^ 2 * |Real.log M.delta|))))
  /-- `eq:mfd-6.3` / `e.energy.density.estimate`. -/
  energy_density : ∀ (L : ℕ) (om : BilateralField d) (alpha : ℝ), M.delta ≤ C⁻¹ → alpha ∈ alphaRange →
    ∀ (m : ℕ) (y : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m)
      (g : SpatialCoordinates d → Fin d → ℝ)
      (hgrad : HilbertGradient (centeredCube y (3 ^ m) hR)),
      (∀ i : Fin d, ((hgrad i : SpatialCoordinates d → ℝ))
        =ᵐ[volume.restrict (centeredCube y ((3 : ℝ) ^ m) hR :
          Set (SpatialCoordinates d))] fun x => g x i) →
      (∀ i : Fin d, IsHolderOn (1 / 2)
        (closedCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) (fun x => g x i)) →
    ∀ (h u : weakSobolevGraph (centeredCube y ((3 : ℝ) ^ m) hR))
      (gh : SpatialCoordinates d → Fin d → ℝ),
      (∀ i : Fin d,
        (sobolevGradient (h : SobolevData (centeredCube y ((3 : ℝ) ^ m) hR)) i : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))]
            (fun x => gh x i)) →
      (∀ i : Fin d, IsHolderOn (1 / 2)
        (closedCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) (fun x => gh x i)) →
      (∀ φ : killedSobolevGraph (centeredCube y ((3 : ℝ) ^ m) hR),
        sobolevCoefficientForm (cutoffOn L om y (3 ^ m) hR)
            (u : SobolevData _) (φ : SobolevData _) =
          -inner ℝ hgrad
            (subspaceGradient (killedSobolevGraph (centeredCube y (3 ^ m) hR)) φ)) →
      -- `u = h` on `∂(y + 𝕔_m)`: the paper's Dirichlet condition
      ((u : SobolevData (centeredCube y ((3 : ℝ) ^ m) hR)) -
          (h : SobolevData (centeredCube y ((3 : ℝ) ^ m) hR))) ∈
        killedSobolevGraph (centeredCube y ((3 : ℝ) ^ m) hR) →
    ∀ (x : SpatialCoordinates d), x ∈ centeredCube y ((3 : ℝ) ^ m) hR →
    ∀ (n : ℕ), (n : ℤ) ≤ (m : ℤ) - prefixLen L alpha m y om →
      normalizedEnergyNorm (cutoffOn L om y (3 ^ m) hR)
          ((isOpen_ball (x := x) (ε := (3 : ℝ) ^ n / 2)).measurableSet.inter
            (centeredCube y ((3 : ℝ) ^ m) hR).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData _)) ≤
        C * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - n)) *
          (normalizedEnergyNorm (cutoffOn L om y (3 ^ m) hR)
              (centeredCube y ((3 : ℝ) ^ m) hR).isOpen.measurableSet
              (sobolevGradient (u : SobolevData _)) +
            Real.sqrt (refAvg L m y om)⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) *
              halfHolderSeminorm
                (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) g) +
        (if x ∈ (centeredCube y ((3 : ℝ) ^ ((m : ℤ) - 1)) (by positivity) :
            Set (SpatialCoordinates d)) then 0 else
          C * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - n)) * Real.sqrt (refAvg L m y om) *
            halfHolderNorm ((3 : ℝ) ^ m)
              (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))
              gh)

  holder_estimate : ∀ (L : ℕ) (om : BilateralField d) (alpha : ℝ), M.delta ≤ C⁻¹ → alpha ∈ alphaRange →
    ∀ (m : ℕ) (y : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m)
      (g : SpatialCoordinates d → Fin d → ℝ)
      (hgrad : HilbertGradient (centeredCube y (3 ^ m) hR)),
      (∀ i : Fin d, ((hgrad i : SpatialCoordinates d → ℝ))
        =ᵐ[volume.restrict (centeredCube y ((3 : ℝ) ^ m) hR :
          Set (SpatialCoordinates d))] fun x => g x i) →
      (∀ i : Fin d, IsHolderOn (1 / 2)
        (closedCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) (fun x => g x i)) →
    ∀ (h u : weakSobolevGraph (centeredCube y ((3 : ℝ) ^ m) hR))
      (gh : SpatialCoordinates d → Fin d → ℝ),
      (∀ i : Fin d,
        (sobolevGradient (h : SobolevData (centeredCube y ((3 : ℝ) ^ m) hR)) i : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))]
            (fun x => gh x i)) →
      (∀ i : Fin d, IsHolderOn (1 / 2)
        (closedCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) (fun x => gh x i)) →
      (∀ φ : killedSobolevGraph (centeredCube y ((3 : ℝ) ^ m) hR),
        sobolevCoefficientForm (cutoffOn L om y (3 ^ m) hR)
            (u : SobolevData _) (φ : SobolevData _) =
          -inner ℝ hgrad
            (subspaceGradient (killedSobolevGraph (centeredCube y (3 ^ m) hR)) φ)) →
      -- `u = h` on `∂(y + 𝕔_m)`: the paper's Dirichlet condition
      ((u : SobolevData (centeredCube y ((3 : ℝ) ^ m) hR)) -
          (h : SobolevData (centeredCube y ((3 : ℝ) ^ m) hR))) ∈
        killedSobolevGraph (centeredCube y ((3 : ℝ) ^ m) hR) →
    ∀ (x : SpatialCoordinates d), x ∈ centeredCube y ((3 : ℝ) ^ m) hR →
    ∀ (n : ℕ), (n : ℤ) ≤ (m : ℤ) - prefixLen L alpha m y om →
    ∀ (ell : ℕ), ell ≤ n →
    ∀ (z : SpatialCoordinates d),
      (∃ k : Fin d → ℤ, ∀ i, z i = y i + (3 : ℝ) ^ ell * (k i : ℝ)) →
      z ∈ Metric.ball x ((3 : ℝ) ^ n / 2) ∩
        (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) →
      let S : Set (SpatialCoordinates d) := Metric.ball z ((3 : ℝ) ^ ell / 2) ∩
        (centeredCube y ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))
      let rootSet : Set (SpatialCoordinates d) := centeredCube y ((3 : ℝ) ^ m) hR
      let v : SpatialCoordinates d → ℝ :=
        ((u : SobolevData (centeredCube y ((3 : ℝ) ^ m) hR)).1 : SpatialCoordinates d → ℝ)
      let avg : Set (SpatialCoordinates d) → ℝ :=
        fun T => (volume.real T)⁻¹ * ∫ w in T, v w
      let osc : Set (SpatialCoordinates d) → ℝ :=
        fun T => Real.sqrt ((volume.real T)⁻¹ * ∫ w in T, (v w - avg T) ^ 2)
      (3 : ℝ) ^ (alpha * ((n : ℝ) - (ell : ℝ))) * osc S ≤
        C * (3 : ℝ) ^ (-alpha * ((m : ℝ) - (n : ℝ))) *
          (osc rootSet + (refAvg L m y om)⁻¹ * (3 : ℝ) ^ (3 * (m : ℝ) / 2) *
            halfHolderSeminorm rootSet g) +
        (if x ∈ Metric.ball y ((3 : ℝ) ^ ((m : ℤ) - 1) / 2) then 0 else
          C * (3 : ℝ) ^ (-alpha * ((m : ℝ) - (n : ℝ))) *
            (3 : ℝ) ^ (m : ℝ) * halfHolderNorm ((3 : ℝ) ^ m) rootSet gh)

end SubdiffusiveProcess.Lane4
