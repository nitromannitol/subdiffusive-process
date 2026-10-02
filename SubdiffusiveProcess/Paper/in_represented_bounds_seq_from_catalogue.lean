import SubdiffusiveProcess.Paper.in_represented_bounds_seq_local_cutoffs
import SubdiffusiveProcess.Paper.in_represented_bounds_seq_collar_uniform
import SubdiffusiveProcess.Paper.in_represented_bounds_seq_collar_product
import SubdiffusiveProcess.Paper.in_represented_bounds_seq_finite_mesh_from_catalogue
import SubdiffusiveProcess.Paper.conv_represented_bounds_env_smooth
import SubdiffusiveProcess.Paper.conv_represented_bounds_env_holder
import SubdiffusiveProcess.Paper.in_represented_bounds_seq

open Set Filter MeasureTheory TopologicalSpace SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped Topology ENNReal NNReal BigOperators ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- The actual represented catalogue and native collar estimates supply the entire bounds bundle. -/
theorem in_represented_bounds_seq_from_catalogue
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Cext beta alpha eta t : ℝ) (orders : Finset ℝ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (rad : J → ℝ)
    (hrad : ∀ j, 0 < rad j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hrad j)))
    (D : ∀ j, Submodule ℚ
      (DomainL2 (centeredCube (z j) (rad j) (hrad j))))
    [hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j →
      Homogenization.H1Function
        (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → Ω →
      Homogenization.H1Function
        (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (E : Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey :
      ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J)
    (gridKey : Grid → Index)
    (hrepresented :
      Paper.conv_represented_estimates d hd M H Ω P cutoff env J j0 z rad hrad
        S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E
        Index resp respLim constants G coercivityKey extensionKey lambdaKey
        sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey
        cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (hext : InfraredCharacterization M H → aux_lem_cutoffs_root_uniform_extrema d M H eta)
    (hseed : ∀ k : ℕ, ∃ b : T j0, (thetaH1 j0 b).toFun =
      bufferedCollarProfile d (z j0) (rad j0) (rad j0 / (10 * (3 : ℝ) ^ k)))
    (Glim : Ω → DomainL2 (centeredCube (z j0) (rad j0) (hrad j0)) →L[ℝ]
      DomainL2 (centeredCube (z j0) (rad j0) (hrad j0)))
    (hconv : ∀ᵐ omega ∂P, ∀ g : DomainL2 (centeredCube (z j0) (rad j0) (hrad j0)),
      Tendsto (fun n => (responseSolution (S j0)
        (Lane4.cutoffPositiveCoefficient M H (env n omega) (cutoff n) (z j0) (hrad j0))
        ((sobolevVolumeLoad g).comp (S j0).space.subtypeL)).val.1) atTop (𝓝 (Glim omega g))) :
    ∀ᵐ omega ∂P, in_represented_bounds_seq d hd (z j0) (rad j0) (hrad j0) (S j0)
      (fun n => Lane4.cutoffPositiveCoefficient M H (env n omega) (cutoff n) (z j0) (hrad j0))
      (Glim omega) := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨Ggood, hGmeas, hGsub, hGnull, hcollar⟩ :=
    in_represented_bounds_seq_collar_uniform d hd M H Cext beta alpha eta t orders Ω P cutoff
      env J j0 z rad hrad S D f T theta thetaH1 usrc srcRep ucell E Index resp respLim constants
      G coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hrepresented hext hseed
  have hgood : ∀ᵐ omega ∂P, omega ∈ Ggood := by
    rw [ae_iff]
    exact hGnull
  filter_upwards [hgood, hconv] with omega homega hlim
  have hmem := hGsub homega
  obtain ⟨KE, hKE, v, hv⟩ := hcollar omega homega
  choose Kchi hKchi hv using hv
  have hrep := hrepresented
  rcases hrep with
    ⟨ht, ha, hb, _, _, _, _, _, _, hseq, _, _, _, _, _, _, hS, hdense, hsource,
      hsdense, htrace, hsourceTrace, _, _, _, _, _, hnonneg, hresponse, _, hcoercive,
      _, _, hsourcebound, _⟩
  have halpha : 0 < alpha := lt_trans (by norm_num) (lt_trans hb.1 hb.2)
  have halphaHalf : 1 / 2 < alpha := hb.1.trans hb.2
  have hbounded := hseq.2.2.2.2
  obtain ⟨KC, hKC⟩ := hbounded (coercivityKey j0) omega hmem
  have hcoercBound : ∀ n, constants (coercivityKey j0) n omega ≤ KC := fun n =>
    (le_abs_self _).trans (hKC n)
  obtain ⟨phi, hphi, hPhi, hsmooth⟩ := conv_represented_bounds_env_smooth
    (z j0) (rad j0) (hrad j0) (D j0) (f j0) (T j0) (theta j0) (thetaH1 j0)
    (hsource j0) (fun b => (htrace j0 b).2) (hsourceTrace j0) (hsdense j0)
  have hHolder : ∀ g : D j0, ∃ Kf : ℝ, 0 ≤ Kf ∧ ∀ n : ℕ,
      ContinuousOn (srcRep j0 g n omega)
        (closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d))) ∧
      Lane4.IsHolderOn alpha
        (closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)))
        (srcRep j0 g n omega) ∧
      Lane4.cAlphaNorm alpha
        (closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)))
        (srcRep j0 g n omega) ≤ Kf ∧
      ∀ x ∈ frontier (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)),
        srcRep j0 g n omega x = 0 := by
    intro g
    let sf := sSup {w : ℝ | ∃ x ∈ closure
      (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)), w = |f j0 g x|}
    have hsf : 0 ≤ sf := Real.sSup_nonneg (by rintro w ⟨x, hx, rfl⟩; exact abs_nonneg _)
    obtain ⟨B, hB⟩ := hbounded (sourceHolderKey j0 g) omega hmem
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
    refine ⟨B * sf, mul_nonneg hB0 hsf, fun n => ?_⟩
    have h := hsourcebound j0 g n omega hmem
    exact ⟨h.2.1, h.2.2.2.1, h.2.2.2.2.trans
      (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hB n)) hsf), h.2.2.1⟩
  obtain ⟨u, uc, hU, hUrep, hUconv, hUholder⟩ := conv_represented_bounds_env_holder
    (z j0) (rad j0) (hrad j0) (S j0) (D j0)
    (fun n => Lane4.cutoffPositiveCoefficient M H (env n omega) (cutoff n) (z j0) (hrad j0))
    alpha (Glim omega) (fun g n => usrc j0 g n omega) (fun g n => srcRep j0 g n omega)
    (fun g n => ((hresponse j0 n omega hmem).1 g).1)
    (fun g n => ((hresponse j0 n omega hmem).1 g).2.1) hHolder hlim
  have hGrowth : ∀ g : D j0, ∃ B : ℝ, 0 ≤ B ∧ ∀ n x,
      x ∈ closure (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)) →
      ∀ rr, 0 < rr → rr ≤ 1 →
      (((volume.restrict (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal
          ((Lane4.cutoffPositiveCoefficient M H (env n omega) (cutoff n) (z j0) (hrad j0)).val y *
            ∑ i : Fin d, ((u g.val n).val.2 i : SpatialCoordinates d → ℝ) y ^ 2)))
        (Metric.ball x rr)) ≤ ENNReal.ofReal (B * rr ^ t) := by
    intro g
    let sf := sSup {w : ℝ | ∃ x ∈ closure
      (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d)), w = |f j0 g x|}
    obtain ⟨B, hB⟩ := hbounded (sourceGrowthKey j0 g) omega hmem
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
    refine ⟨B * sf ^ 2, mul_nonneg hB0 (sq_nonneg sf), fun n x hx rr hrr hrr1 => ?_⟩
    have hueq : u g.val n = usrc j0 g n omega :=
      (hU g.val n).trans (((hresponse j0 n omega hmem).1 g).1.symm)
    rw [hueq]
    exact ((hsourcebound j0 g n omega hmem).1 x hx rr hrr hrr1).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hB n)) (sq_nonneg sf))
        (Real.rpow_nonneg hrr.le t)))
  obtain ⟨w, hW, hError⟩ := in_represented_bounds_seq_collar_product d hd (z j0) (rad j0)
    (hrad j0) (S j0) (hS j0)
    (fun n => Lane4.cutoffPositiveCoefficient M H (env n omega) (cutoff n) (z j0) (hrad j0))
    (D j0) u uc hU hUrep alpha halpha hUholder t eta ht.1 ht.2 halphaHalf ha.1 ha.2.1 ha.2.2
    (fun k => rad j0 / (10 * (3 : ℝ) ^ k)) (fun k => div_pos (hrad j0) (by positivity)) hGrowth v
    (fun k n => (hv k n).2.2.2.1) (fun k n => (hv k n).2.2.2.2.2.1) KE hKE (by
      intro k n
      have heq : energy
          (Lane4.cutoffPositiveCoefficient M H (env n omega) (cutoff n) (z j0) (hrad j0)).val
          (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d))
          (v k n).toH1Function =
          energy (cutoffCoefficient M H (env n omega) (cutoff n))
          (centeredCube (z j0) (rad j0) (hrad j0) : Set (SpatialCoordinates d))
          (v k n).toH1Function := by
        unfold energy
        apply integral_congr_ae
        filter_upwards [aux_lem_cutoffs_positiveCoefficient_ae M H (env n omega)
          (cutoff n) (z j0) (hrad j0)] with x hx
        rw [hx]
      rw [heq]
      exact (hv k n).2.2.2.2.2.2)
  refine ⟨fun n => constants (coercivityKey j0) n omega,
    fun n => hnonneg (coercivityKey j0) omega hmem n, KC, hcoercBound,
    fun v => (hcoercive j0 0 omega hmem v).1,
    fun n v => (hcoercive j0 n omega hmem v).2, hInterp, t, ht.1, ht.2,
    in_represented_bounds_seq_local_cutoffs d hd M H Cext beta alpha eta t orders Ω P cutoff
      env J j0 z rad hrad S D f T theta thetaH1 usrc srcRep ucell E Index resp respLim constants
      G coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hrepresented omega hmem,
    D j0, inferInstance, hdense j0, phi, hPhi, alpha, eta, halphaHalf, ha.1, ha.2.1, ha.2.2,
    u, uc, hU, hUrep, hUconv, hUholder,
    fun k => rad j0 / (10 * (3 : ℝ) ^ k), fun _ => rfl,
    fun k n => (v k n).toH1Function.toFun, ?_, w, hW, hError,
    in_represented_bounds_seq_finite_mesh_from_catalogue hd M H Ω P cutoff env J j0 z rad hrad
      S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim
      constants G coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey
      sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey
      hrepresented omega hmem phi hPhi halpha, hsmooth, trivial⟩
  intro k
  refine ⟨Kchi k, hKchi k, fun n => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, _⟩ := hv k n
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end Paper

