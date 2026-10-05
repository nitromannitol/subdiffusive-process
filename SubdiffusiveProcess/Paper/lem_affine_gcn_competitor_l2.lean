module

public import SubdiffusiveProcess.Paper.lem_affine_gcn_competitor
public import SubdiffusiveProcess.Paper.inputs_classical_harmonic_lipschitz
public import SubdiffusiveProcess.Analysis.NormalizedMeanMinimizer

@[expose] public section

/-! # Affine trace approximation with an `L²` comparison-scale oscillation

Variant of `SubdiffusiveProcess.Paper.lem_affine_gcn_competitor` whose oscillation premise is the normalized
`L²` distance to a constant on the comparison ball (instead of a pointwise oscillation),
whose harmonic comparison may live on a larger concentric cube, and whose Hölder premise is
the good-cell estimate at the scale of `q` (normalized by the centered `L²` oscillation on the
padded parent `p`).  The gain `(r/R)^α` is derived here from the harmonic comparison and the
classical interior Lipschitz estimate.  It does not claim any pointwise oscillation bound. -/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Shift variant: an `L²` oscillation bound about a constant `c0` transfers to the
comparison function. -/
lemma aux_lem_affine_gcn_competitor_l2_shift
    {d : ℕ} (z : SpatialCoordinates d) (R Os Err c0 : ℝ) (hR : 0 < R)
    (U V : SpatialCoordinates d → ℝ)
    (hU : MemLp U 2 (volume.restrict (Metric.ball z (R / 2))))
    (hV : MemLp V 2 (volume.restrict (Metric.ball z (R / 2))))
    (hosc : normalizedL2On (Metric.ball z (R / 2)) (fun x => U x - c0) ≤ Os)
    (herr : normalizedL2On (Metric.ball z (R / 2)) (fun x => U x - V x) ≤ Err) :
    normalizedL2On (Metric.ball z (R / 2)) (fun x => V x - c0) ≤ Err + Os := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball z (R / 2))) := by
    change IsFiniteMeasure (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d)))
    infer_instance
  have hU0 := hU.sub (memLp_const c0)
  have hsum := Section6Iteration.normalizedL2On_add_le (hV.sub hU) hU0
  have he : (fun x => V x - U x + (U x - c0)) = (fun x => V x - c0) := by funext x; ring
  simp only [Pi.sub_apply] at hsum
  rw [he] at hsum
  change normalizedL2On _ (fun x => V x - c0) ≤
    normalizedL2On _ (fun x => V x - U x) + normalizedL2On _ (fun x => U x - c0) at hsum
  rw [Section6Iteration.normalizedL2On_sub_comm _ V U] at hsum
  exact hsum.trans (add_le_add herr hosc)

lemma aux_lem_affine_gcn_competitor_l2_approximation
    {d : ℕ} [NeZero d] (z : SpatialCoordinates d) (r R Os Err c0 : ℝ)
    (hr : 0 < r) (hR : 0 < R) (h2r : 2 * r ≤ R)
    (U V : SpatialCoordinates d → ℝ)
    (hU : MemLp U 2 (volume.restrict (Metric.ball z (R / 2))))
    (hV : MemLp V 2 (volume.restrict (Metric.ball z (R / 2))))
    (hosc : normalizedL2On (Metric.ball z (R / 2)) (fun x => U x - c0) ≤ Os)
    (herr : normalizedL2On (Metric.ball z (R / 2)) (fun x => U x - V x) ≤ Err)
    (hh : InnerProductSpace.HarmonicOnNhd
      (V ∘ (Section6Schauder.toEuc.symm : EuclideanSpace ℝ (Fin d) → SpatialCoordinates d))
      ((Section6Schauder.toEuc : SpatialCoordinates d → EuclideanSpace ℝ (Fin d)) ''
        Metric.ball z (R / 2))) :
    ∃ (m : Fin d → ℝ) (c : ℝ), normalizedL2On (Metric.ball z (r / 2))
        (fun x => U x - ((∑ i, m i * x i) + c)) ≤
      (R / r) ^ ((d : ℝ) / 2) * Err +
        aux_lem_affine_gcn_competitor_taylorC d * (r / R) ^ 2 * (Err + Os) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball z (R / 2))) := by
    change IsFiniteMeasure (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d)))
    infer_instance
  have hV0 := hV.sub (memLp_const c0)
  obtain ⟨m, c, happ⟩ := aux_lem_affine_gcn_competitor_harmonic_approx z r R hr hR h2r
    (fun x => V x - c0) hV0 (by
      simpa only [Function.comp_def] using Section6Schauder.harmonicOnNhd_sub_const hh c0)
  have hshift := aux_lem_affine_gcn_competitor_l2_shift z R Os Err c0 hR U V hU hV hosc herr
  have hsub : Metric.ball z (r / 2) ⊆ Metric.ball z (R / 2) :=
    Metric.ball_subset_ball (by linarith only [h2r, hr])
  have hsmall := Section6Iteration.normalizedL2On_le_of_subset hsub
    (by rw [aux_lem_affine_gcn_competitor_ball_volume z R hR]; positivity)
    (by rw [aux_lem_affine_gcn_competitor_ball_volume z r hr]; positivity)
    (hU.sub hV).integrable_sq
  rw [aux_lem_affine_gcn_competitor_volume_ratio z r R hr hR] at hsmall
  have hsmall' := hsmall.trans (mul_le_mul_of_nonneg_left herr (by positivity))
  have hm : MemLp (fun x : SpatialCoordinates d => (∑ i, m i * x i) + c) 2
      (volume.restrict (Metric.ball z (r / 2))) := by
    obtain ⟨h, _⟩ := continuousOn_cube_memLp_and_nonzero z r hr
      (fun x => fun _ : Fin 1 => (∑ i, m i * x i) + c)
      (continuousOn_pi' (fun _ => by fun_prop))
    exact h 0
  refine ⟨m, c + c0, ?_⟩
  apply aux_lem_affine_gcn_competitor_normalizedL2_add_bound
    ((hU.sub hV).mono_measure (Measure.restrict_mono hsub le_rfl))
    ((hV0.mono_measure (Measure.restrict_mono hsub le_rfl)).sub hm)
    (fun x => by dsimp; ring) hsmall'
  exact happ.trans (mul_le_mul_of_nonneg_left hshift
    (mul_nonneg (aux_lem_affine_gcn_competitor_taylorC_nonneg d) (sq_nonneg _)))





lemma aux_lem_affine_gcn_competitor_l2_projected_data
    {d : ℕ} [NeZero d] (z : SpatialCoordinates d) (r R N Cin Os Src eps alpha c0 : ℝ)
    (hr : 0 < r) (hR : 0 < R) (h2r : 2 * r ≤ R) (hN : 0 < N) (hCin : 0 ≤ Cin)
    (hOs : 0 ≤ Os) (hSrc : 0 ≤ Src) (ha : 0 < alpha) (ha1 : alpha < 1)
    (U V : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U (closure (Metric.ball z (r / 2))))
    (hUm : MemLp U 2 (volume.restrict (Metric.ball z (R / 2))))
    (hVm : MemLp V 2 (volume.restrict (Metric.ball z (R / 2))))
    (hosc : normalizedL2On (Metric.ball z (R / 2)) (fun x => U x - c0) ≤ Os)
    (herr : normalizedL2On (Metric.ball z (R / 2)) (fun x => U x - V x) ≤ eps * Os + Src)
    (hh : InnerProductSpace.HarmonicOnNhd
      (V ∘ (Section6Schauder.toEuc.symm : EuclideanSpace ℝ (Fin d) → SpatialCoordinates d))
      ((Section6Schauder.toEuc : SpatialCoordinates d → EuclideanSpace ℝ (Fin d)) '' Metric.ball z (R / 2)))
    (hHol : ∀ x ∈ closure (Metric.ball z (r / 2)), ∀ y ∈ closure (Metric.ball z (r / 2)),
      |U x - U y| ≤ Cin * (Os + Src) * (dist x y / R) ^ alpha) :
    ∃ (pc : (Fin d → ℝ) × ℝ) (F : SpatialCoordinates d → ℝ),
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d) F ∧
      (∀ x, U x - ((∑ i, pc.1 i * x i) + pc.2) = N * F (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation 0 z r⁻¹ x)) ∧
      (eLpNorm F 2 (volume.restrict (_root_.SubdiffusiveProcess.Paper.AffineProjection.Q0 d))).toReal ≤
        ((R / r) ^ ((d : ℝ) / 2) * (eps * Os + Src) +
          aux_lem_affine_gcn_competitor_taylorC d * (r / R) ^ 2 * (eps * Os + Src + Os)) / N ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha (_root_.SubdiffusiveProcess.Paper.AffineProjection.S0 d) F ≤
        aux_lem_affine_gcn_competitor_projC d alpha * (Cin * (Os + Src) / N * (r / R) ^ alpha) := by
  let F0 := fun x => (U (_root_.SubdiffusiveProcess.EllipticRegularity.cubeDilation z 0 r x) - U z) / N
  obtain ⟨hFcont, hFhold, hFabs, hFnorm⟩ := aux_lem_affine_gcn_competitor_centered_rescaling
    z r R N Cin Os Src alpha hr hR hN hCin hOs hSrc ha ha1 U hU hHol
  have hK : 0 ≤ Cin * (Os + Src) / N * (r / R) ^ alpha := by positivity
  obtain ⟨hprojHold, hprojNorm⟩ := aux_lem_affine_gcn_competitor_projection_holder
    alpha _ ha ha1 hK F0 hFhold hFabs hFnorm
  obtain ⟨pc, hpc⟩ := aux_lem_affine_gcn_competitor_projection_pullback z r N hr hN U F0 (fun _ => rfl)
  refine ⟨pc, (fun x => F0 x - _root_.SubdiffusiveProcess.Paper.AffineProjection.proj F0 x), hprojHold, hpc, ?_, hprojNorm⟩
  obtain ⟨m, c, happrox⟩ := aux_lem_affine_gcn_competitor_l2_approximation z r R Os (eps * Os + Src) c0
    hr hR h2r U V hUm hVm hosc herr hh
  have hm : MemLp (fun x : SpatialCoordinates d => (∑ i, m i * x i) + c) 2
      (volume.restrict (Metric.ball z (r / 2))) := by
    obtain ⟨h, _⟩ := continuousOn_cube_memLp_and_nonzero z r hr
      (fun x => fun _ : Fin 1 => (∑ i, m i * x i) + c)
      (continuousOn_pi' (fun _ => by fun_prop))
    exact h 0
  have hmem := (hUm.mono_measure (Measure.restrict_mono
    (Metric.ball_subset_ball (by linarith only [h2r, hr])) le_rfl)).sub hm
  exact (aux_lem_affine_gcn_competitor_projection_compare z r N hr hN U F0 hFcont
    (fun _ => rfl) m c hmem).trans (div_le_div_of_nonneg_right happrox hN.le)


lemma aux_lem_affine_gcn_competitor_l2_trace_core
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (alpha beta gamma zeta rho Cin Cinterp Cc L r R N Os Src eps eh s S c0 : ℝ)
    (z : SpatialCoordinates d) (U V : SpatialCoordinates d → ℝ)
    (hb : 0 < beta) (hba : beta < alpha) (ha1 : alpha < 1) (hg : 0 < gamma)
    (hCin : 1 ≤ Cin) (hCc : 1 ≤ Cc) (hCinterp : 0 < Cinterp) (hL : 1 < L)
    (hr : 0 < r) (hR : 0 < R) (h2r : 2 * r ≤ R) (hN : 0 < N) (hs : 0 < s) (hS : 0 < S)
    (hOs : 0 ≤ Os) (hSrc : 0 ≤ Src) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hlo : L ^ gamma * r ≤ R) (hhi : R ≤ Cin * L ^ gamma * r)
    (hON : Os / N ≤ Cin * ((R / r) ^ ((2 - (d : ℝ)) / 2) * L ^ (((d : ℝ) + zeta) / 2)))
    (hSN : Src / N ≤ L ^ (((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2))
    (heSmall : Cin ^ ((d : ℝ) / 2) * Cin * eps ≤ eh / 2)
    (hsrcSmall : (Cin ^ ((d : ℝ) / 2) * L ^ (gamma * (d : ℝ) / 2) +
      aux_lem_affine_gcn_competitor_taylorC d) * (Src / N) ≤ eh / 2 * L ^ (((d : ℝ) + zeta) / 2 + gamma))
    (hHC : 2 * aux_lem_affine_gcn_competitor_taylorC d * Cin ≤ Cc)
    (hPC : aux_lem_affine_gcn_competitor_projC d alpha * Cin * (Cin + 1) ≤ Cc)
    (hcoef : Cin * Cinterp ^ 2 ≤ Cc)
    (hscale : s * r ^ ((d : ℝ) - 2) * N ^ 2 = S)
    (hAffine : aux_lem_affine_gcn_competitor_affineProp d alpha beta gamma zeta rho Cc eh L)
    (hinterp : aux_lem_affine_gcn_competitor_interpProp d alpha beta Cinterp)
    (hU : ContinuousOn U (closure (Metric.ball z (r / 2))))
    (hUm : MemLp U 2 (volume.restrict (Metric.ball z (R / 2))))
    (hVm : MemLp V 2 (volume.restrict (Metric.ball z (R / 2))))
    (hosc : normalizedL2On (Metric.ball z (R / 2)) (fun x => U x - c0) ≤ Os)
    (herr : normalizedL2On (Metric.ball z (R / 2)) (fun x => U x - V x) ≤ eps * Os + Src)
    (hh : InnerProductSpace.HarmonicOnNhd
      (V ∘ (Section6Schauder.toEuc.symm : EuclideanSpace ℝ (Fin d) → SpatialCoordinates d))
      ((Section6Schauder.toEuc : SpatialCoordinates d → EuclideanSpace ℝ (Fin d)) '' Metric.ball z (R / 2)))
    (hHol : ∀ x ∈ closure (Metric.ball z (r / 2)), ∀ y ∈ closure (Metric.ball z (r / 2)),
      |U x - U y| ≤ Cin * (Os + Src) * (dist x y / R) ^ alpha) :
    ∃ pc : (Fin d → ℝ) × ℝ,
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (frontier (Metric.ball z (r / 2)))
        (fun x => U x - ((∑ i, pc.1 i * x i) + pc.2)) ∧
      Cin * s * r ^ ((d : ℝ) - 2) * (r ^ beta * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta
        (frontier (Metric.ball z (r / 2))) (fun x => U x - ((∑ i, pc.1 i * x i) + pc.2))) ^ 2 ≤ rho * S := by
  have ha : 0 < alpha := hb.trans hba
  obtain ⟨pc, F, hF, hrel, hA, hB⟩ := aux_lem_affine_gcn_competitor_l2_projected_data
    z r R N Cin Os Src eps alpha c0 hr hR h2r hN (by linarith only [hCin])
    hOs hSrc ha ha1 U V hU hUm hVm hosc herr hh hHol
  obtain ⟨hA_bound, hB_bound⟩ := aux_lem_affine_gcn_competitor_rescaled_AB hd
    alpha gamma zeta Cin Cc L r R N Os Src eps eh ha hg hCin hCc hL hr hR hN
    hOs hSrc heps heps1 hlo hhi hON hSN heSmall hsrcSmall hHC hPC _ _ hA hB
  obtain ⟨hHolder, htrace⟩ := aux_lem_affine_gcn_competitor_trace_interpolation
    alpha beta Cinterp Cin Cc r s S N z F (fun x => U x - ((∑ i, pc.1 i * x i) + pc.2))
    hb hba hCinterp.le (by linarith only [hCin]) hr hs hS hN hscale hcoef hinterp hF hrel
  refine ⟨pc, hHolder, ?_⟩
  exact hAffine _ _ _ S _ rfl ENNReal.toReal_nonneg
    ((aux_lem_affine_gcn_competitor_holder_nonneg alpha _ F).trans
      (aux_lem_affine_gcn_competitor_holder_le_cAlpha alpha _ F)) hS.le hA_bound hB_bound htrace



/-- The harmonic comparison error transfers from `Vbar` to the harmonic representative when
the comparison cube `R2` contains the ball of radius `R / 2`. -/
lemma aux_lem_affine_gcn_competitor_l2_harmonic_error
    {d : ℕ} (z : SpatialCoordinates d) (R R2 Err : ℝ) (hR2 : 0 < R2) (hRR2 : R ≤ R2)
    (U Vbar vH : SpatialCoordinates d → ℝ)
    (Ubar : weakSobolevGraph (centeredCube z R2 hR2))
    (w : Homogenization.H1Function (centeredCube z R2 hR2 : Set (SpatialCoordinates d)))
    (hUbarV : ((Ubar : SobolevData (centeredCube z R2 hR2)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z R2 hR2 : Set (SpatialCoordinates d))] Vbar)
    (hwval : (w : SpatialCoordinates d → ℝ) = (Ubar : SobolevData (centeredCube z R2 hR2)).1)
    (hvHae : vH =ᵐ[volume] Set.indicator (centeredCube z R2 hR2 : Set (SpatialCoordinates d))
      w.toFun)
    (herr : normalizedL2On (Metric.ball z (R / 2)) (fun x => U x - Vbar x) ≤ Err) :
    normalizedL2On (Metric.ball z (R / 2)) (fun x => U x - vH x) ≤ Err := by
  have hsub : Metric.ball z (R / 2) ⊆ (centeredCube z R2 hR2 : Set (SpatialCoordinates d)) :=
    Metric.ball_subset_ball (by linarith only [hRR2])
  have hvHae' : vH =ᵐ[volume.restrict (Metric.ball z (R / 2))]
      ((Ubar : SobolevData (centeredCube z R2 hR2)).1 : SpatialCoordinates d → ℝ) := by
    have hv := ae_restrict_of_ae (s := Metric.ball z (R / 2)) hvHae
    filter_upwards [hv, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxmem
    rw [hx, Set.indicator_of_mem (hsub hxmem), ← hwval]
  have hUbarV' := ae_restrict_of_ae_restrict_of_subset hsub hUbarV
  have hUVae : (fun x => U x - vH x) =ᵐ[volume.restrict (Metric.ball z (R / 2))]
      (fun x => U x - Vbar x) := by
    filter_upwards [hvHae', hUbarV'] with x hx hy
    rw [hx, hy]
  rw [Section6ExcessDecay.normalizedL2On_congr_ae hUVae]
  exact herr

/-- Harmonic comparison and an interior Lipschitz bound control the centered oscillation on
the padded parent `p = B(z, 3r/2)` of `q` by the comparison-scale quantities. -/
lemma aux_lem_affine_gcn_competitor_l2_holder_gain
    {d : ℕ} [NeZero d] (z : SpatialCoordinates d) (r R Os Err c0 Clip : ℝ)
    (hr : 0 < r) (hR : 0 < R) (h6r : 6 * r ≤ R) (hClip : 0 ≤ Clip)
    (U V : SpatialCoordinates d → ℝ)
    (hU : MemLp U 2 (volume.restrict (Metric.ball z (R / 2))))
    (hV : MemLp V 2 (volume.restrict (Metric.ball z (R / 2))))
    (hosc : normalizedL2On (Metric.ball z (R / 2)) (fun x => U x - c0) ≤ Os)
    (herr : normalizedL2On (Metric.ball z (R / 2)) (fun x => U x - V x) ≤ Err)
    (hLip : ∀ x ∈ Metric.ball z (R / 4), ∀ y ∈ Metric.ball z (R / 4),
      |(V x - c0) - (V y - c0)| ≤
        Clip * (dist x y / R) * normalizedL2On (Metric.ball z (R / 2)) (fun x => V x - c0)) :
    normalizedL2On (Metric.ball z (3 * r / 2))
      (fun x => U x - (volume.real (Metric.ball z (3 * r / 2)))⁻¹ *
        ∫ y in Metric.ball z (3 * r / 2), U y) ≤
      (R / (3 * r)) ^ ((d : ℝ) / 2) * Err + Clip * (3 * r / (2 * R)) * (Err + Os) := by
  have h3r : 0 < 3 * r := by positivity
  have hpsub : Metric.ball z (3 * r / 2) ⊆ Metric.ball z (R / 2) :=
    Metric.ball_subset_ball (by linarith only [h6r, hr])
  have hpR4 : Metric.ball z (3 * r / 2) ⊆ Metric.ball z (R / 4) :=
    Metric.ball_subset_ball (by linarith only [h6r])
  have hptop : volume (Metric.ball z (3 * r / 2)) ≠ ⊤ := by
    change volume (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) ≠ ⊤
    rw [centeredCube_volume]; exact ENNReal.ofReal_ne_top
  let : IsFiniteMeasure (volume.restrict (Metric.ball z (3 * r / 2))) := by
    change IsFiniteMeasure (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    infer_instance
  have hppos : 0 < (volume (Metric.ball z (3 * r / 2))).toReal := by
    rw [aux_lem_affine_gcn_competitor_ball_volume z (3 * r) h3r]; positivity
  have hUp : MemLp U 2 (volume.restrict (Metric.ball z (3 * r / 2))) :=
    hU.mono_measure (Measure.restrict_mono hpsub le_rfl)
  have hVp : MemLp V 2 (volume.restrict (Metric.ball z (3 * r / 2))) :=
    hV.mono_measure (Measure.restrict_mono hpsub le_rfl)
  have h1 := normalizedL2On_sub_average_le_sub_const (Metric.ball z (3 * r / 2)) hptop U hUp (V z)
  have h2 : normalizedL2On (Metric.ball z (3 * r / 2)) (fun x => U x - V z) ≤
      normalizedL2On (Metric.ball z (3 * r / 2)) (fun x => U x - V x) +
      normalizedL2On (Metric.ball z (3 * r / 2)) (fun x => V x - V z) := by
    have hsum := Section6Iteration.normalizedL2On_add_le (hUp.sub hVp)
      (hVp.sub (memLp_const (V z)))
    have he : (fun x => U x - V x + (V x - V z)) = (fun x => U x - V z) := by
      funext x; ring
    simp only [Pi.sub_apply] at hsum
    rw [he] at hsum
    exact hsum
  have h3 : normalizedL2On (Metric.ball z (3 * r / 2)) (fun x => U x - V x) ≤
      (R / (3 * r)) ^ ((d : ℝ) / 2) * Err := by
    have hsmall := Section6Iteration.normalizedL2On_le_of_subset hpsub
      (by rw [aux_lem_affine_gcn_competitor_ball_volume z R hR]; positivity) hppos
      (hU.sub hV).integrable_sq
    rw [aux_lem_affine_gcn_competitor_volume_ratio z (3 * r) R h3r hR] at hsmall
    exact hsmall.trans (mul_le_mul_of_nonneg_left herr (by positivity))
  have hshift := aux_lem_affine_gcn_competitor_l2_shift z R Os Err c0 hR U V hU hV hosc herr
  have hEO : 0 ≤ Err + Os :=
    (Section6Iteration.normalizedL2On_nonneg _ _).trans hshift
  have hM : 0 ≤ Clip * (3 * r / (2 * R)) * (Err + Os) := by positivity
  have h4 : normalizedL2On (Metric.ball z (3 * r / 2)) (fun x => V x - V z) ≤
      Clip * (3 * r / (2 * R)) * (Err + Os) := by
    apply Section6Iteration.normalizedL2On_le_of_abs_le Metric.isOpen_ball.measurableSet
      hppos hptop hM (hVp.sub (memLp_const (V z))).integrable_sq
    intro x hx
    have hz4 : z ∈ Metric.ball z (R / 4) := Metric.mem_ball_self (by linarith only [hR])
    have hL := hLip x (hpR4 hx) z hz4
    have hxz : dist x z < 3 * r / 2 := Metric.mem_ball.mp hx
    have hdist : dist x z / R ≤ 3 * r / (2 * R) := by
      rw [div_le_div_iff₀ hR (by positivity)]
      nlinarith only [hxz, hR, dist_nonneg (x := x) (y := z)]
    have heq : V x - V z = (V x - c0) - (V z - c0) := by ring
    show |V x - V z| ≤ _
    rw [heq]
    calc |(V x - c0) - (V z - c0)|
        ≤ Clip * (dist x z / R) *
            normalizedL2On (Metric.ball z (R / 2)) (fun x => V x - c0) := hL
      _ ≤ Clip * (3 * r / (2 * R)) * (Err + Os) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hdist hClip) hshift
            (Section6Iteration.normalizedL2On_nonneg _ _) (by positivity)
  calc _ ≤ normalizedL2On (Metric.ball z (3 * r / 2)) (fun x => U x - V z) := h1
    _ ≤ _ := h2
    _ ≤ _ := add_le_add h3 h4

/-- Scalar transfer from the `q`-scale Hölder bound to the comparison-scale form. -/
lemma aux_lem_affine_gcn_competitor_l2_holder_scalar
    (Cin Clip T D alpha r R Os Src eps Np t : ℝ)
    (hCin : 0 ≤ Cin) (hClip : 0 ≤ Clip) (hD : 0 ≤ D) (ha : 0 < alpha) (ha1 : alpha < 1)
    (hr : 0 < r) (hrR : r ≤ R) (hRT : R / r ≤ T)
    (hOs : 0 ≤ Os) (hSrc : 0 ≤ Src) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hepsT : eps * T ^ (alpha + D) ≤ 1) (ht : 0 ≤ t)
    (hNp : Np ≤ (R / (3 * r)) ^ D * (eps * Os + Src) +
      Clip * (3 * r / (2 * R)) * (eps * Os + Src + Os)) :
    Cin * (Np + Src) * (t / r) ^ alpha ≤
      Cin * (1 + 3 * Clip) * (Os + (2 * T ^ (alpha + D) + 2 * Clip + 1) * Src) *
        (t / R) ^ alpha := by
  have hR : 0 < R := hr.trans_le hrR
  set ρ : ℝ := R / r with hρ
  have hρ1 : 1 ≤ ρ := by rw [hρ, le_div_iff₀ hr]; linarith only [hrR]
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos hρ1
  have hsplit : (t / r) ^ alpha = ρ ^ alpha * (t / R) ^ alpha := by
    rw [← Real.mul_rpow hρ0.le (div_nonneg ht hR.le)]
    congr 1
    rw [hρ]; field_simp
  set KL : ℝ := T ^ (alpha + D) with hKL
  set B : ℝ := ρ ^ alpha with hB
  set y : ℝ := (R / (3 * r)) ^ D with hy
  set x : ℝ := 3 * r / (2 * R) with hx
  have hB0 : 0 ≤ B := by positivity
  have hy0 : 0 ≤ y := by positivity
  have hx0 : 0 ≤ x := by positivity
  have hyA : y ≤ ρ ^ D := by
    apply Real.rpow_le_rpow (by positivity) _ hD
    rw [hρ]; exact div_le_div_of_nonneg_left hR.le hr (by linarith only [hr])
  have hABle : ρ ^ D * B ≤ KL := by
    rw [hB, ← Real.rpow_add hρ0, add_comm D alpha, hKL]
    exact Real.rpow_le_rpow hρ0.le hRT (by linarith only [ha, hD])
  have hyB : y * B ≤ KL := (mul_le_mul_of_nonneg_right hyA hB0).trans hABle
  have hBle : B ≤ KL := by
    have hBD : B ≤ ρ ^ D * B := le_mul_of_one_le_left hB0 (Real.one_le_rpow hρ1 hD)
    exact hBD.trans hABle
  have hxB : x * B ≤ 3 / 2 := by
    have hBρ : B ≤ ρ := by
      have := Real.rpow_le_rpow_of_exponent_le hρ1 ha1.le
      rwa [Real.rpow_one] at this
    have hxρ : x * ρ = 3 / 2 := by
      rw [hx, hρ]; field_simp
    calc x * B ≤ x * ρ := mul_le_mul_of_nonneg_left hBρ hx0
      _ = 3 / 2 := hxρ
  have hKL0 : 0 ≤ KL := hB0.trans hBle
  have hmain : (Np + Src) * B ≤ (1 + 3 * Clip) * (Os + (2 * KL + 2 * Clip + 1) * Src) := by
    have h1 : (Np + Src) * B ≤ (y * (eps * Os + Src) + Clip * x * (eps * Os + Src + Os) + Src) * B :=
      mul_le_mul_of_nonneg_right (by linarith only [hNp]) hB0
    have e1 : 0 ≤ (KL - y * B) * (eps * Os) := mul_nonneg (by linarith only [hyB]) (by positivity)
    have e2 : 0 ≤ (1 - eps * KL) * Os := mul_nonneg (by linarith only [hepsT]) hOs
    have e3 : 0 ≤ (KL - y * B) * Src := mul_nonneg (by linarith only [hyB]) hSrc
    have e4 : 0 ≤ (3 / 2 - x * B) * (Clip * (eps * Os + Src + Os)) :=
      mul_nonneg (by linarith only [hxB]) (by positivity)
    have e5 : 0 ≤ Clip * ((1 - eps) * Os) := mul_nonneg hClip (mul_nonneg (by linarith only [heps1]) hOs)
    have e6 : 0 ≤ (KL - B) * Src := mul_nonneg (by linarith only [hBle]) hSrc
    have e7 : 0 ≤ Clip * Src * (1 + 6 * KL + 6 * Clip) := by positivity
    have e8 : 0 ≤ KL * Src := mul_nonneg hKL0 hSrc
    nlinarith only [h1, e1, e2, e3, e4, e5, e6, e7, e8, hClip, hSrc, hOs]
  rw [hsplit]
  have hT0 : 0 ≤ (t / R) ^ alpha := by positivity
  calc Cin * (Np + Src) * (B * (t / R) ^ alpha)
      = Cin * ((Np + Src) * B) * (t / R) ^ alpha := by ring
    _ ≤ Cin * ((1 + 3 * Clip) * (Os + (2 * KL + 2 * Clip + 1) * Src)) * (t / R) ^ alpha := by
        gcongr
    _ = _ := by ring


/-- Per-cell core of `lem_affine_gcn_competitor_l2`, for constants already selected. -/
lemma aux_lem_affine_gcn_competitor_l2_instance
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    (alpha beta gamma zeta rho : ℝ)
    (hbeta : 1 / 2 < beta) (hba : beta < alpha) (halpha : alpha < 1) (hgamma0 : 0 < gamma)
    (Cin Clip Cw Cinterp Cc L ehom epshom src0G T K' : ℝ)
    (hCin : 1 ≤ Cin) (hClip0 : 0 ≤ Clip) (hCwdef : Cw = Cin * (1 + 3 * Clip))
    (hLipAll : ∀ (z : SpatialCoordinates d) (R : ℝ) (V : SpatialCoordinates d → ℝ), 0 < R →
        InnerProductSpace.HarmonicOnNhd
          (V ∘ (Section6Schauder.toEuc.symm :
            EuclideanSpace ℝ (Fin d) → SpatialCoordinates d))
          ((Section6Schauder.toEuc : SpatialCoordinates d → EuclideanSpace ℝ (Fin d)) ''
            Metric.ball z (R / 2)) →
        MemLp V 2 (volume.restrict (Metric.ball z (R / 2))) →
        ∀ x ∈ Metric.ball z (R / 4), ∀ y ∈ Metric.ball z (R / 4),
          |V x - V y| ≤ Clip * (dist x y / R) * normalizedL2On (Metric.ball z (R / 2)) V)
    (hCinterp : 0 < Cinterp) (hinterp : aux_lem_affine_gcn_competitor_interpProp d alpha beta Cinterp)
    (hCc : 1 ≤ Cc) (hcoef : Cw * Cinterp ^ 2 ≤ Cc)
    (hHC : 2 * aux_lem_affine_gcn_competitor_taylorC d * Cw ≤ Cc)
    (hPC : aux_lem_affine_gcn_competitor_projC d alpha * Cw * (Cw + 1) ≤ Cc)
    (hAffine : aux_lem_affine_gcn_competitor_affineProp d alpha beta gamma zeta rho Cc ehom L)
    (hLpow6 : 6 ≤ L ^ gamma) (hLcur : 1 < L)
    (hepshom : 0 < epshom) (heps1 : epshom ≤ 1)
    (heSmall : Cw ^ ((d : ℝ) / 2) * Cw * epshom ≤ ehom / 2)
    (hTdef : T = Cin * L ^ gamma) (hepsKL : epshom * T ^ (alpha + (d : ℝ) / 2) ≤ 1)
    (hK'def : K' = 2 * T ^ (alpha + (d : ℝ) / 2) + 2 * Clip + 1)
    (hsrcBound : ∀ y : ℝ, 0 ≤ y → y ≤ src0G →
      y ≤ L ^ (((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2) ∧
      (Cw ^ ((d : ℝ) / 2) * L ^ (gamma * (d : ℝ) / 2) + aux_lem_affine_gcn_competitor_taylorC d) * y ≤
        ehom / 2 * L ^ (((d : ℝ) + zeta) / 2 + gamma)) :
    ∀ (Q : Opens (SpatialCoordinates d))
      (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
      (GammaE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
      (u : DomainL2 Q) (U : SpatialCoordinates d → ℝ)
      (_hUcont : ContinuousOn U (closure (Q : Set (SpatialCoordinates d))))
      (_hUae : ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (Q : Set (SpatialCoordinates d))] U))
      (z : SpatialCoordinates d) (r R : ℝ) (_hr : 0 < r)
      (_hRlo : L ^ gamma * r ≤ R) (_hRhi : R ≤ Cin * L ^ gamma * r)
      (_hQR : Metric.ball z (R / 2) ⊆ (Q : Set (SpatialCoordinates d)))
      (c s : ℝ) (_hc : 0 < c) (_hs : 0 < s)
      (Os Src c0 : ℝ) (_hOs0 : 0 ≤ Os) (_hSrc0 : 0 ≤ Src),
      let q : Set (SpatialCoordinates d) := Metric.ball z (r / 2)
      let p : Set (SpatialCoordinates d) := Metric.ball z (3 * r / 2)
      let S : ℝ := (GammaE.measure u q).toReal + c * (volume q).toReal
      normalizedL2On (Metric.ball z (R / 2)) (fun x => U x - c0) ≤ Os →
      Os ≤ Cin * R ^ ((2 - (d : ℝ)) / 2) * L ^ (((d : ℝ) + zeta) / 2) * Real.sqrt (S / s) →
      (∃ (R2 : ℝ) (hR2 : 0 < R2), R ≤ R2 ∧
        ∃ (Ubar : weakSobolevGraph (centeredCube z R2 hR2))
          (Vbar : SpatialCoordinates d → ℝ),
        ContinuousOn Vbar (closure (centeredCube z R2 hR2 : Set (SpatialCoordinates d))) ∧
        (((Ubar : SobolevData (centeredCube z R2 hR2)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z R2 hR2 : Set (SpatialCoordinates d))] Vbar) ∧
        (∀ psi : killedSobolevGraph (centeredCube z R2 hR2),
          inner ℝ (sobolevGradient (Ubar : SobolevData (centeredCube z R2 hR2)))
            (subspaceGradient (killedSobolevGraph (centeredCube z R2 hR2)) psi) = 0) ∧
        normalizedL2On (Metric.ball z (R / 2)) (fun x => U x - Vbar x) ≤ epshom * Os + Src) →
      (∀ x ∈ closure q, ∀ y ∈ closure q,
        |U x - U y| ≤ Cin * (normalizedL2On p
          (fun x => U x - (volume.real p)⁻¹ * ∫ y in p, U y) + Src) * (dist x y / r) ^ alpha) →
      (∀ g : SpatialCoordinates d → ℝ,
        ContinuousOn g (closure (Q : Set (SpatialCoordinates d))) →
        _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (frontier q) g →
        ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
          v ∈ E.domain ∧
          ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
          ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (Q : Set (SpatialCoordinates d))] V) ∧
          (∀ x ∈ frontier q, V x = g x) ∧
          (GammaE.measure v q).toReal ≤
            Cin * s * r ^ ((d : ℝ) - 2) * (r ^ beta * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier q) g) ^ 2) →
      Src ≤ src0G / K' * r ^ ((2 - (d : ℝ)) / 2) * Real.sqrt (S / s) →
      ∃ pc : (Fin d → ℝ) × ℝ,
        (let ell : SpatialCoordinates d → ℝ := fun x => (∑ i, pc.1 i * x i) + pc.2
         let b : SpatialCoordinates d → ℝ := fun x => U x - ell x
         let eSet : Set ℝ :=
           {e : ℝ | ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
               v ∈ E.domain ∧
               ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
               ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                 (Q : Set (SpatialCoordinates d))] V) ∧
               (∀ x ∈ frontier q, V x = b x) ∧
               e = (GammaE.measure v q).toReal}
         ∃ Lambda : ℝ, IsGLB eSet Lambda ∧ eSet.Nonempty ∧ Lambda ≤ rho * S) := by
  have hCinCw : Cin ≤ Cw := by
    rw [hCwdef]; exact le_mul_of_one_le_right (by linarith only [hCin]) (by linarith only [hClip0])
  have hCw : 1 ≤ Cw := hCin.trans hCinCw
  have hLp : 0 < L := zero_lt_one.trans hLcur
  have hT1 : 1 ≤ T := by
    rw [hTdef]
    have h6 : (1 : ℝ) ≤ L ^ gamma := by linarith only [hLpow6]
    calc (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ Cin * L ^ gamma := mul_le_mul hCin h6 zero_le_one (by linarith only [hCin])
  have halpha0 : 0 < alpha := by linarith only [hbeta, hba]
  have hKL1 : 1 ≤ T ^ (alpha + (d : ℝ) / 2) := Real.one_le_rpow hT1 (by positivity)
  have hK'1 : 1 ≤ K' := by rw [hK'def]; linarith only [hKL1, hClip0]
  intro Q E GammaE u U hUcont hUae z r R hr hRlo hRhi hQR c s hc hs Os Src c0 hOs0 hSrc0
  dsimp only
  intro hoscL2 hOs hharm hHolq hext hSrc
  have hRpos : 0 < R := (mul_pos (Real.rpow_pos_of_pos hLp gamma) hr).trans_le hRlo
  have h6r : 6 * r ≤ R := (mul_le_mul_of_nonneg_right hLpow6 hr.le).trans hRlo
  have h2r : 2 * r ≤ R := by linarith only [h6r, hr]
  have hSpos :
      0 < (GammaE.measure u (Metric.ball z (r / 2))).toReal +
        c * (volume (Metric.ball z (r / 2))).toReal :=
    aux_lem_affine_gcn_competitor_budget_pos d Q E GammaE u z r c hr hc
  rcases hharm with ⟨R2, hR2, hRR2, Ubar, Vbar, hVbarcont, hUbarV, hEq, herr⟩
  obtain ⟨w, hwweak, hwval⟩ :=
    aux_lem_affine_gcn_competitor_weak_harmonic d z R2 hR2 Ubar hEq
  obtain ⟨vH, hvHarm2, hvHMlp, hvHae⟩ :=
    Section6Schauder.exists_harmonicRepresentative_memLp (centeredCube z R2 hR2).isOpen hwweak
  have hballsub : Metric.ball z (R / 2) ⊆
      (centeredCube z R2 hR2 : Set (SpatialCoordinates d)) :=
    Metric.ball_subset_ball (by linarith only [hRR2])
  have hvHarm : InnerProductSpace.HarmonicOnNhd
      (vH ∘ (Section6Schauder.toEuc.symm : EuclideanSpace ℝ (Fin d) → SpatialCoordinates d))
      ((Section6Schauder.toEuc : SpatialCoordinates d → EuclideanSpace ℝ (Fin d)) ''
        Metric.ball z (R / 2)) :=
    fun x hx => hvHarm2 x (Set.image_mono hballsub hx)
  have hErr := aux_lem_affine_gcn_competitor_l2_harmonic_error z R R2 (epshom * Os + Src)
    hR2 hRR2 U Vbar vH Ubar w hUbarV hwval hvHae herr
  have hUcontW := hUcont.mono (closure_mono hQR)
  have hUmem := aux_lem_affine_gcn_competitor_cube_memLp z R hRpos U hUcontW
  have hvHm : MemLp vH 2 (volume.restrict (Metric.ball z (R / 2))) := hvHMlp.restrict _
  let : IsFiniteMeasure (volume.restrict (Metric.ball z (R / 2))) := by
    change IsFiniteMeasure (volume.restrict (centeredCube z R hRpos : Set (SpatialCoordinates d)))
    infer_instance
  have hLip := hLipAll z R (fun x => vH x - c0) hRpos
    (by simpa only [Function.comp_def] using Section6Schauder.harmonicOnNhd_sub_const hvHarm c0)
    (hvHm.sub (memLp_const c0))
  have hGain := aux_lem_affine_gcn_competitor_l2_holder_gain z r R Os (epshom * Os + Src) c0
    Clip hr hRpos h6r hClip0 U vH hUmem hvHm hoscL2 hErr hLip
  let Src' : ℝ := K' * Src
  have hSrc'0 : 0 ≤ Src' := mul_nonneg (by linarith only [hK'1]) hSrc0
  have hSrcle : Src ≤ Src' := le_mul_of_one_le_left hSrc0 hK'1
  have hRT : R / r ≤ T := by
    rw [div_le_iff₀ hr, hTdef]
    linarith only [hRhi]
  have hHol : ∀ x ∈ closure (Metric.ball z (r / 2)), ∀ y ∈ closure (Metric.ball z (r / 2)),
      |U x - U y| ≤ Cw * (Os + Src') * (dist x y / R) ^ alpha := by
    intro x hx y hy
    have hxy := hHolq x hx y hy
    have hsc := aux_lem_affine_gcn_competitor_l2_holder_scalar Cin Clip T ((d : ℝ) / 2) alpha
      r R Os Src epshom _ (dist x y) (by linarith only [hCin]) hClip0 (by positivity)
      (by linarith only [hbeta, hba]) halpha hr (by linarith only [h2r, hr]) hRT hOs0 hSrc0
      hepshom.le heps1 hepsKL dist_nonneg hGain
    refine hxy.trans (hsc.trans (le_of_eq ?_))
    rw [hCwdef, ← hK'def]
  have herr' : normalizedL2On (Metric.ball z (R / 2)) (fun x => U x - vH x) ≤
      epshom * Os + Src' := hErr.trans (by linarith only [hSrcle])
  have hRhi' : R ≤ Cw * L ^ gamma * r := by
    have hLg : 0 ≤ L ^ gamma * r := by positivity
    calc R ≤ Cin * L ^ gamma * r := hRhi
      _ = Cin * (L ^ gamma * r) := by ring
      _ ≤ Cw * (L ^ gamma * r) := mul_le_mul_of_nonneg_right hCinCw hLg
      _ = Cw * L ^ gamma * r := by ring
  have hOs' : Os ≤ Cw * R ^ ((2 - (d : ℝ)) / 2) * L ^ (((d : ℝ) + zeta) / 2) *
      Real.sqrt (((GammaE.measure u (Metric.ball z (r / 2))).toReal +
        c * (volume (Metric.ball z (r / 2))).toReal) / s) := by
    refine hOs.trans ?_
    have hX : 0 ≤ R ^ ((2 - (d : ℝ)) / 2) * L ^ (((d : ℝ) + zeta) / 2) *
        Real.sqrt (((GammaE.measure u (Metric.ball z (r / 2))).toReal +
          c * (volume (Metric.ball z (r / 2))).toReal) / s) := by positivity
    calc Cin * R ^ ((2 - (d : ℝ)) / 2) * L ^ (((d : ℝ) + zeta) / 2) *
          Real.sqrt (((GammaE.measure u (Metric.ball z (r / 2))).toReal +
            c * (volume (Metric.ball z (r / 2))).toReal) / s)
        = Cin * (R ^ ((2 - (d : ℝ)) / 2) * L ^ (((d : ℝ) + zeta) / 2) *
          Real.sqrt (((GammaE.measure u (Metric.ball z (r / 2))).toReal +
            c * (volume (Metric.ball z (r / 2))).toReal) / s)) := by ring
      _ ≤ Cw * (R ^ ((2 - (d : ℝ)) / 2) * L ^ (((d : ℝ) + zeta) / 2) *
          Real.sqrt (((GammaE.measure u (Metric.ball z (r / 2))).toReal +
            c * (volume (Metric.ball z (r / 2))).toReal) / s)) :=
          mul_le_mul_of_nonneg_right hCinCw hX
      _ = _ := by ring
  have hext' : ∀ g : SpatialCoordinates d → ℝ,
      ContinuousOn g (closure (Q : Set (SpatialCoordinates d))) →
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (frontier (Metric.ball z (r / 2))) g →
      ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
        v ∈ E.domain ∧
        ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
        ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (Q : Set (SpatialCoordinates d))] V) ∧
        (∀ x ∈ frontier (Metric.ball z (r / 2)), V x = g x) ∧
        (GammaE.measure v (Metric.ball z (r / 2))).toReal ≤
          Cw * s * r ^ ((d : ℝ) - 2) * (r ^ beta * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta
            (frontier (Metric.ball z (r / 2))) g) ^ 2 := by
    intro g hg hgH
    obtain ⟨v, V, hv, hVc, hvV, hVb, hbound⟩ := hext g hg hgH
    refine ⟨v, V, hv, hVc, hvV, hVb, hbound.trans ?_⟩
    have hX : 0 ≤ s * r ^ ((d : ℝ) - 2) * (r ^ beta * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta
        (frontier (Metric.ball z (r / 2))) g) ^ 2 := by positivity
    calc Cin * s * r ^ ((d : ℝ) - 2) * (r ^ beta * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta
          (frontier (Metric.ball z (r / 2))) g) ^ 2
        = Cin * (s * r ^ ((d : ℝ) - 2) * (r ^ beta * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta
          (frontier (Metric.ball z (r / 2))) g) ^ 2) := by ring
      _ ≤ Cw * (s * r ^ ((d : ℝ) - 2) * (r ^ beta * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta
          (frontier (Metric.ball z (r / 2))) g) ^ 2) := mul_le_mul_of_nonneg_right hCinCw hX
      _ = _ := by ring
  let Sval := (GammaE.measure u (Metric.ball z (r / 2))).toReal +
    c * (volume (Metric.ball z (r / 2))).toReal
  let N := r ^ ((2 - (d : ℝ)) / 2) * Real.sqrt (Sval / s)
  have hNpos : 0 < N := mul_pos (Real.rpow_pos_of_pos hr _) (Real.sqrt_pos.2 (div_pos hSpos hs))
  have hON := aux_lem_affine_gcn_competitor_normalized_Os d Cw R r L zeta Sval s N Os
    hr hRpos hNpos rfl hOs'
  have hK'pos : 0 < K' := by linarith only [hK'1]
  have hSrcN : Src' / N ≤ src0G := by
    apply (div_le_iff₀ hNpos).2
    have h1 : Src' ≤ K' * (src0G / K' * r ^ ((2 - (d : ℝ)) / 2) * Real.sqrt (Sval / s)) :=
      mul_le_mul_of_nonneg_left hSrc hK'pos.le
    have h2 : K' * (src0G / K' * r ^ ((2 - (d : ℝ)) / 2) * Real.sqrt (Sval / s)) = src0G * N := by
      dsimp only [N]
      field_simp
    linarith only [h1, h2]
  obtain ⟨hSN, hsrcSmall⟩ := hsrcBound (Src' / N) (div_nonneg hSrc'0 hNpos.le) hSrcN
  have hUcontq : ContinuousOn U (closure (Metric.ball z (r / 2))) :=
    hUcontW.mono (closure_mono (Metric.ball_subset_ball (by linarith only [h2r, hr])))
  have htrace := aux_lem_affine_gcn_competitor_l2_trace_core hd
    alpha beta gamma zeta rho Cw Cinterp Cc L r R N Os Src' epshom ehom s Sval c0 z U vH
    (by linarith only [hbeta]) hba halpha hgamma0 hCw hCc hCinterp hLcur
    hr hRpos h2r hNpos hs hSpos hOs0 hSrc'0 hepshom.le heps1 hRlo hRhi'
    hON hSN heSmall hsrcSmall hHC hPC hcoef
    (aux_lem_affine_gcn_competitor_normalization d r s Sval hr hs hSpos)
    hAffine hinterp hUcontq hUmem hvHm hoscL2 herr' hvHarm hHol
  obtain ⟨pc, hpcHolder, hpcBudget⟩ := htrace
  let ell : SpatialCoordinates d → ℝ :=
    fun x => (∑ i, pc.1 i * x i) + pc.2
  let b : SpatialCoordinates d → ℝ := fun x => U x - ell x
  have hbHolder : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (frontier (Metric.ball z (r / 2))) b := by
    change _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (frontier (Metric.ball z (r / 2)))
      (fun x => U x - ((∑ i, pc.1 i * x i) + pc.2))
    exact hpcHolder
  have hbcont : ContinuousOn b (closure (Q : Set (SpatialCoordinates d))) := by
    have hell : ContinuousOn ell (closure (Q : Set (SpatialCoordinates d))) := by
      have hlin : Continuous (fun x : SpatialCoordinates d =>
          ∑ i : Fin d, pc.1 i * x i) := by
        exact continuous_finsetSum _ (fun i _ =>
          continuous_const.mul (continuous_apply i))
      exact (hlin.add continuous_const).continuousOn
    exact hUcont.sub hell
  obtain ⟨Lambda, hglb, hne, hLambda⟩ :=
    aux_lem_affine_gcn_competitor_extension_glb d Q E GammaE
      (Metric.ball z (r / 2)) b beta Cw s r
      (rho * ((GammaE.measure u (Metric.ball z (r / 2))).toReal +
        c * (volume (Metric.ball z (r / 2))).toReal))
      hbcont hbHolder hext' hpcBudget
  refine ⟨pc, ?_⟩
  exact ⟨Lambda, hglb, hne, hLambda⟩



/-- Affine trace approximation on a good cell with an `L²` comparison-scale oscillation: the
oscillation premise is the normalized `L²` distance to a constant on the comparison ball, the
harmonic comparison may live on any larger concentric cube, and the Hölder premise is the
good-cell estimate of `q` normalized by the centered oscillation on its padded parent. -/
theorem lem_affine_gcn_competitor_l2
    (d : ℕ) (hd : 2 ≤ d)
    (alpha beta gamma zeta rho : ℝ)
    (hbeta : 1 / 2 < beta) (hba : beta < alpha) (halpha : alpha < 1)
    (hgamma0 : 0 < gamma) (hgamma1 : gamma < 1) (hzeta : 0 < zeta) (hrho : 0 < rho)
    (hneg : affineExponent (d : ℝ) alpha beta gamma zeta < 0)
    (Cin : ℝ) (hCin : 1 ≤ Cin) :
    ∃ L0 : ℝ, 1 < L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ epshom : ℝ, 0 < epshom → epshom ≤ eps0 →
    ∃ src0 : ℝ, 0 < src0 ∧
    ∀ (Q : Opens (SpatialCoordinates d))
      (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
      (GammaE : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
      (u : DomainL2 Q) (U : SpatialCoordinates d → ℝ)
      (_hUcont : ContinuousOn U (closure (Q : Set (SpatialCoordinates d))))
      (_hUae : ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (Q : Set (SpatialCoordinates d))] U))
      (z : SpatialCoordinates d) (r R : ℝ) (_hr : 0 < r)
      (_hRlo : L ^ gamma * r ≤ R) (_hRhi : R ≤ Cin * L ^ gamma * r)
      (_hQR : Metric.ball z (R / 2) ⊆ (Q : Set (SpatialCoordinates d)))
      (c s : ℝ) (_hc : 0 < c) (_hs : 0 < s)
      (Os Src c0 : ℝ) (_hOs0 : 0 ≤ Os) (_hSrc0 : 0 ≤ Src),
      let q : Set (SpatialCoordinates d) := Metric.ball z (r / 2)
      let p : Set (SpatialCoordinates d) := Metric.ball z (3 * r / 2)
      let S : ℝ := (GammaE.measure u q).toReal + c * (volume q).toReal
      normalizedL2On (Metric.ball z (R / 2)) (fun x => U x - c0) ≤ Os →
      Os ≤ Cin * R ^ ((2 - (d : ℝ)) / 2) * L ^ (((d : ℝ) + zeta) / 2) * Real.sqrt (S / s) →
      (∃ (R2 : ℝ) (hR2 : 0 < R2), R ≤ R2 ∧
        ∃ (Ubar : weakSobolevGraph (centeredCube z R2 hR2))
          (Vbar : SpatialCoordinates d → ℝ),
        ContinuousOn Vbar (closure (centeredCube z R2 hR2 : Set (SpatialCoordinates d))) ∧
        (((Ubar : SobolevData (centeredCube z R2 hR2)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z R2 hR2 : Set (SpatialCoordinates d))] Vbar) ∧
        (∀ psi : killedSobolevGraph (centeredCube z R2 hR2),
          inner ℝ (sobolevGradient (Ubar : SobolevData (centeredCube z R2 hR2)))
            (subspaceGradient (killedSobolevGraph (centeredCube z R2 hR2)) psi) = 0) ∧
        normalizedL2On (Metric.ball z (R / 2)) (fun x => U x - Vbar x) ≤ epshom * Os + Src) →
      (∀ x ∈ closure q, ∀ y ∈ closure q,
        |U x - U y| ≤ Cin * (normalizedL2On p
          (fun x => U x - (volume.real p)⁻¹ * ∫ y in p, U y) + Src) * (dist x y / r) ^ alpha) →
      (∀ g : SpatialCoordinates d → ℝ,
        ContinuousOn g (closure (Q : Set (SpatialCoordinates d))) →
        _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta (frontier q) g →
        ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
          v ∈ E.domain ∧
          ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
          ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (Q : Set (SpatialCoordinates d))] V) ∧
          (∀ x ∈ frontier q, V x = g x) ∧
          (GammaE.measure v q).toReal ≤
            Cin * s * r ^ ((d : ℝ) - 2) * (r ^ beta * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta (frontier q) g) ^ 2) →
      Src ≤ src0 * r ^ ((2 - (d : ℝ)) / 2) * Real.sqrt (S / s) →
      ∃ pc : (Fin d → ℝ) × ℝ,
        (let ell : SpatialCoordinates d → ℝ := fun x => (∑ i, pc.1 i * x i) + pc.2
         let b : SpatialCoordinates d → ℝ := fun x => U x - ell x
         let eSet : Set ℝ :=
           {e : ℝ | ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
               v ∈ E.domain ∧
               ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
               ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                 (Q : Set (SpatialCoordinates d))] V) ∧
               (∀ x ∈ frontier q, V x = b x) ∧
               e = (GammaE.measure v q).toReal}
         ∃ Lambda : ℝ, IsGLB eSet Lambda ∧ eSet.Nonempty ∧ Lambda ≤ rho * S) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Clip, hClip0, hLipAll⟩ := inputs_classical_harmonic_lipschitz d
  set Cw : ℝ := Cin * (1 + 3 * Clip) with hCwdef
  have hCinCw : Cin ≤ Cw := le_mul_of_one_le_right (by linarith only [hCin]) (by linarith only [hClip0])
  have hCw : 1 ≤ Cw := hCin.trans hCinCw
  obtain ⟨Cinterp, hCinterp, hinterp⟩ :=
    aux_lem_affine_gcn_competitor_interp d (by omega) alpha beta (by linarith) hba halpha.le
  obtain ⟨Cc, hCc, hcoef, hHC, hPC⟩ :=
    aux_lem_affine_gcn_competitor_constants d alpha Cw Cinterp (by linarith only [hCw])
  obtain ⟨Lbase, hLbase1, hAll⟩ :=
    aux_lem_affine_gcn_competitor_affine_trace_all d hd Cc hCc
      alpha beta gamma zeta hbeta hba halpha hgamma0 hgamma1 hzeta hneg rho hrho
  let L0 : ℝ := max Lbase (6 ^ (1 / gamma))
  have hL01 : 1 < L0 := by
    exact lt_of_lt_of_le hLbase1 (le_max_left _ _)
  refine ⟨L0, hL01, ?_⟩
  intro L hL
  have hLbaseL : Lbase ≤ L := le_trans (le_max_left _ _) hL
  have hLpow6 : 6 ≤ L ^ gamma := by
    have hroot : 6 ^ (1 / gamma) ≤ L :=
      le_trans (le_max_right _ _) hL
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (6 : ℝ) ^ (1 / gamma))
      hroot hgamma0.le
    have hroot_eq : ((6 : ℝ) ^ (1 / gamma)) ^ gamma = 6 := by
      rw [← Real.rpow_mul (by norm_num : 0 ≤ (6 : ℝ))]
      have hγ : (1 / gamma) * gamma = (1 : ℝ) := by
        field_simp
      rw [hγ]
      norm_num
    rw [hroot_eq] at hpow
    exact hpow
  obtain ⟨ehom, hehom, hAffine⟩ := hAll L hLbaseL
  have hLcur : 1 < L := hL01.trans_le hL
  have hLp : 0 < L := zero_lt_one.trans hLcur
  obtain ⟨eps0G, src0G, heps0G, hsrc0G, hepsBound, hsrcBound⟩ :=
    aux_lem_affine_gcn_competitor_thresholds (Cw ^ ((d : ℝ) / 2)) Cw
      (L ^ (gamma * (d : ℝ) / 2)) (aux_lem_affine_gcn_competitor_taylorC d)
      (L ^ (((d : ℝ) + zeta) / 2 - gamma * ((d : ℝ) - 2) / 2))
      (L ^ (((d : ℝ) + zeta) / 2 + gamma)) ehom
      (by positivity) (by linarith only [hCw]) (by positivity)
      (aux_lem_affine_gcn_competitor_taylorC_nonneg d)
      (Real.rpow_pos_of_pos hLp _) (Real.rpow_pos_of_pos hLp _) hehom
  have hT1 : 1 ≤ Cin * L ^ gamma := by
    have h6 : (1 : ℝ) ≤ L ^ gamma := by linarith only [hLpow6]
    calc (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ Cin * L ^ gamma := mul_le_mul hCin h6 zero_le_one (by linarith only [hCin])
  have halpha0 : 0 < alpha := by linarith only [hbeta, hba]
  have hKL1 : 1 ≤ (Cin * L ^ gamma) ^ (alpha + (d : ℝ) / 2) :=
    Real.one_le_rpow hT1 (by positivity)
  set KL : ℝ := (Cin * L ^ gamma) ^ (alpha + (d : ℝ) / 2) with hKLdef
  set K' : ℝ := 2 * KL + 2 * Clip + 1 with hK'def
  have hK'1 : 1 ≤ K' := by linarith only [hKL1, hClip0]
  refine ⟨min eps0G KL⁻¹, lt_min heps0G (inv_pos.mpr (by linarith only [hKL1])), ?_⟩
  intro epshom hepshom hepshom_le
  have hepsG : epshom ≤ eps0G := hepshom_le.trans (min_le_left _ _)
  have hepsKL : epshom * KL ≤ 1 := by
    have h := hepshom_le.trans (min_le_right _ _)
    calc epshom * KL ≤ KL⁻¹ * KL := mul_le_mul_of_nonneg_right h (by linarith only [hKL1])
      _ = 1 := inv_mul_cancel₀ (by linarith only [hKL1])
  obtain ⟨heps1, heSmall⟩ := hepsBound epshom hepshom.le hepsG
  refine ⟨src0G / K', div_pos hsrc0G (by linarith only [hK'1]), ?_⟩
  exact aux_lem_affine_gcn_competitor_l2_instance d hd alpha beta gamma zeta rho hbeta hba halpha
    hgamma0 Cin Clip Cw Cinterp Cc L ehom epshom src0G (Cin * L ^ gamma) K' hCin hClip0 hCwdef
    hLipAll hCinterp hinterp hCc hcoef hHC hPC hAffine hLpow6 hLcur hepshom heps1 heSmall rfl
    hepsKL hK'def hsrcBound

end SubdiffusiveProcess.Paper
