import SubdiffusiveProcess.Paper.lem_as_regularity_actual_dirichlet_trunc
import SubdiffusiveProcess.Paper.lem_as_regularity_dirichlet_coeff
import SubdiffusiveProcess.Paper.lem_as_regularity_dirichlet_exists
import SubdiffusiveProcess.Paper.lem_as_regularity_dirichlet_stability
import SubdiffusiveProcess.Paper.lem_as_regularity_dirichlet_limit
import SubdiffusiveProcess.Analysis.NativeScoreAllowance
import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.Windows

/-! The original native allowance supplies the full Dirichlet oscillation iteration for the physical
coefficient with the genuine infrared field: the estimate for the truncated infrared fields
(`lem_as_regularity_actual_dirichlet_trunc`, uniform in the truncation) passes to the limit along
the `L²` convergence of the Dirichlet solutions. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set Filter SubdiffusiveProcess SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open Homogenization hiding Vec
open Homogenization.Book
open scoped ENNReal BigOperators Topology
noncomputable section
namespace Paper

/-- The reference scalar is continuous in the value of the infrared field at the point. -/
theorem aux_lem_as_regularity_actual_dirichlet_sref_tendsto {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Hk : ℕ → BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N : ℕ) (l : ℤ) (w : SpatialCoordinates d)
    (h : Tendsto (fun k => Hk k omega w) atTop (𝓝 (H omega w))) :
    Tendsto (fun k => aux_in_deterministic_onestep_sref M (Hk k) omega N l w) atTop
      (𝓝 (aux_in_deterministic_onestep_sref M H omega N l w)) := by
  unfold aux_in_deterministic_onestep_sref
  dsimp only
  exact tendsto_const_nhds.mul ((Real.continuous_exp.tendsto _).comp (h.add tendsto_const_nhds))

/-- The Euclidean fractional carrier gives `L²` membership of the datum. -/
theorem aux_lem_as_regularity_actual_dirichlet_memVectorL2 {d : ℕ}
    {Q : Homogenization.TriadicCube d} {s : FractionalOrder} {g : Vec d → Vec d}
    (hg : Ch03.ABK26.MemCubeEuclideanFullWsp Q s FiniteLpExponent.two g) :
    MemVectorL2 (openCubeSet Q) g := by
  have h2 := Ch03.ABK26.MemCubeEuclideanFullWsp.memLpTwo (p := FiniteLpExponent.two)
    (by simp [FiniteLpExponent.two]) hg
  unfold normalizedCubeMeasure at h2
  have hc0 : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 := by
    have := cubeVolume_pos Q
    simpa using this
  have h3 := h2.smul_measure (c := (ENNReal.ofReal ((cubeVolume Q)⁻¹))⁻¹)
    (ENNReal.inv_ne_top.2 hc0)
  rw [smul_smul, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_smul] at h3
  simpa [volumeMeasureOn, cubeMeasure, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    using h3

/-- One original native allowance gives the actual Dirichlet oscillation estimate. -/
theorem lem_as_regularity_actual_dirichlet (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d,ℝ)] [BorelSpace C(SpatialCoordinates d,ℝ)]
    (E : in_J d) (D : lane4_deterministic_good_scale_input d)
    (rho : ℝ) (hrho : 0 < rho) :
    ∃ eps rate delta0 C : ℝ, eps ∈ Ioo (0:ℝ) 1 ∧ 0 < rate ∧ 0 < delta0 ∧ 0 < C ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
      (H : BilateralField d → C(SpatialCoordinates d,ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
    ∀ (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
      (F P R Draw : ℕ → ℕ → Vec d → BilateralField d → ℝ≥0∞)
      (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
      (good : ℕ → ℕ → Vec d → BilateralField d → Prop),
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,∀ N i y,
        eta N omega i y = omega ((i:ℤ)-(N:ℤ)) ((3:ℝ)^(-(N:ℤ)) • y)) →
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,∀ N,
        primitive_scores d M (1/32) eps (eta N omega)
          (fun m y => F N m y omega) (fun m y => P N m y omega)
          (fun m y => R N m y omega) (fun m y => Draw N m y omega)
          (fun m y => Z N m y omega) (fun m y => good N m y omega)) →
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
    ∀ N m n : ℕ,n ≤ m → ∀ w z0 : SpatialCoordinates d,(3:ℝ)^N • (w-z0) ∈ cube d m →
      nativeScoreAllowance (fun j => Z N j ((3:ℝ)^N • w) omega)
        (fun j => Draw N j ((3:ℝ)^N • w) omega) m rate ≤ m-n →
    ∀ data : ScalarTriadicCoeffData (fun y => cutoffCoefficient M H omega N
      ((3:ℝ)^(-(N:ℤ)) • (y+(3:ℝ)^N • (w-z0))+z0)),
    ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
      IsDirichletSolutionOn (fun y => cutoffCoefficient M H omega N ((3:ℝ)^(-(N:ℤ)) • y+z0))
        (originCube d m) u h g →
      (∃ sOrder : FractionalOrder,sOrder.1 = (1/4:ℝ) ∧
        Ch03.ABK26.MemCubeEuclideanFullWsp (originCube d m) sOrder FiniteLpExponent.two g) →
      MemHolder (cube d m) (1/2) g → MemHolder (cube d m) (1/2) h.grad →
      (3:ℝ)^(-((n+2:ℕ):ℤ))*normalizedL2On (truncatedCube d m (n+2:ℕ) ((3:ℝ)^N • (w-z0)))
        (fun x => u.toFun x-averageOn (truncatedCube d m (n+2:ℕ) ((3:ℝ)^N • (w-z0))) u.toFun) ≤
      C*(3:ℝ)^(rho*((m:ℝ)-n))*
        ((3:ℝ)^(-((m-5:ℕ):ℤ))*normalizedL2On (truncatedCube d m (m-5:ℕ) ((3:ℝ)^N • (w-z0)))
          (fun x => u.toFun x-averageOn (truncatedCube d m (m-5:ℕ) ((3:ℝ)^N • (w-z0))) u.toFun) +
          vectorSupNormOn (cube d m) h.grad +
          (aux_in_deterministic_onestep_sref M H omega N ((N:ℤ)-m) w)⁻¹ *
            (3:ℝ)^((m:ℝ)/2)*holderSeminormOn (cube d m) (1/2) g +
          (3:ℝ)^((m:ℝ)/2)*holderSeminormOn (cube d m) (1/2) h.grad) := by
  obtain ⟨eps, rate, C, heps, hrate, hC, hA⟩ :=
    lem_as_regularity_actual_dirichlet_trunc d hd D rho hrho
  refine ⟨eps, rate, eps, C, heps, hrate, heps.1, hC, ?_⟩
  intro M Rm H hIR hδ eta F P R Draw Z good hEta hPS
  filter_upwards [hIR.2, hEta, hPS] with omega hlim hEtaw hPSw
  intro N m n hnm w z0 hw hallow data u h g hsol hg hgh hhh
  obtain ⟨hgap, -, -, -⟩ := nativeScoreAllowance_window
    (fun j => Z N j ((3:ℝ)^N • w) omega) (fun j => Draw N j ((3:ℝ)^N • w) omega) m n rate hnm
    hallow
  obtain ⟨sOrder, hsO, hfw⟩ := hg
  have hgL2 := aux_lem_as_regularity_actual_dirichlet_memVectorL2 hfw
  have hWm : MeasurableSet (openCubeSet (originCube d m)) :=
    (isOpenBoundedConvexDomain_openCubeSet (originCube d m)).isOpen.measurableSet
  -- a compact set carrying the coefficients
  have hKc : IsCompact (Metric.closedBall (cubeCenter (originCube d m))
      (cubeRadius (originCube d m))) := ProperSpace.isCompact_closedBall _ _
  have hWK : openCubeSet (originCube d m) ⊆ Metric.closedBall (cubeCenter (originCube d m))
      (cubeRadius (originCube d m)) :=
    (openCubeSet_subset_cubeSet _).trans (cubeSet_subset_closedBall _)
  have hKne : (Metric.closedBall (cubeCenter (originCube d m))
      (cubeRadius (originCube d m))).Nonempty := (Section6TheoremC.nonempty_openCubeSet (originCube d m)).mono hWK
  have hφ : Continuous (fun y : SpatialCoordinates d => (3:ℝ)^(-(N:ℤ)) • y + z0) := by fun_prop
  have hac : Continuous (fun y : SpatialCoordinates d =>
      cutoffCoefficient M H omega N ((3:ℝ)^(-(N:ℤ)) • y + z0)) :=
    (cutoffCoefficient_continuous M H omega N).comp hφ
  obtain ⟨lam0, Lam0, hlam0, hbd⟩ := aux_lem_as_regularity_dirichlet_coeff_bounds hKc hKne hac
    (fun y => cutoffCoefficient_pos M H omega N _)
  have hU := lem_as_regularity_dirichlet_coeff M H omega N z0 hlim hKc
  obtain ⟨L0, hL0⟩ := eventually_atTop.1 (hU (lam0 / 2) (by positivity))
  let ℓ : ℕ → ℕ := fun k => k + L0 + m
  have hℓ : Tendsto ℓ atTop atTop :=
    tendsto_atTop_mono (fun k => (by show k ≤ k + L0 + m; omega)) tendsto_id
  let bk : ℕ → SpatialCoordinates d → ℝ := fun k y => cutoffCoefficient M
    (fun om => infraredPartialSum om (ℓ k)) omega N ((3:ℝ)^(-(N:ℤ)) • y + z0)
  have hbkc : ∀ k, Continuous (bk k) := fun k =>
    (cutoffCoefficient_continuous M (fun om => infraredPartialSum om (ℓ k)) omega N).comp hφ
  have hbklo : ∀ k, ∀ y ∈ openCubeSet (originCube d m), lam0 / 2 ≤ bk k y := by
    intro k y hy
    have h1 := hL0 (ℓ k) (by show L0 ≤ k + L0 + m; omega) y (hWK hy)
    have h2 := (hbd y (hWK hy)).1
    have h3 := (abs_le.1 h1).2
    show lam0 / 2 ≤ cutoffCoefficient M (fun om => infraredPartialSum om (ℓ k)) omega N _
    linarith
  have hbkhi : ∀ k, ∀ y ∈ openCubeSet (originCube d m), bk k y ≤ Lam0 + lam0 / 2 := by
    intro k y hy
    have h1 := hL0 (ℓ k) (by show L0 ≤ k + L0 + m; omega) y (hWK hy)
    have h2 := (hbd y (hWK hy)).2
    have h3 := (abs_le.1 h1).1
    show cutoffCoefficient M (fun om => infraredPartialSum om (ℓ k)) omega N _ ≤ _
    linarith
  have hElla : IsEllipticFieldOn lam0 Lam0 (openCubeSet (originCube d m))
      (scalarCoeffField (fun y : SpatialCoordinates d =>
        cutoffCoefficient M H omega N ((3:ℝ)^(-(N:ℤ)) • y + z0))) :=
    Section6TheoremC.isEllipticFieldOn_scalarCoeffField_of_bounds hlam0
      (hac.measurable.ite hWm measurable_const) (fun y hy => (hbd y (hWK hy)).1)
      (fun y hy => (hbd y (hWK hy)).2)
  have hEllb : ∀ k, IsEllipticFieldOn (lam0 / 2) (Lam0 + lam0 / 2)
      (openCubeSet (originCube d m)) (scalarCoeffField (bk k)) := fun k =>
    Section6TheoremC.isEllipticFieldOn_scalarCoeffField_of_bounds (by positivity)
      ((hbkc k).measurable.ite hWm measurable_const) (hbklo k) (hbkhi k)
  choose v hv using fun k => lem_as_regularity_dirichlet_exists (hEllb k) h hgL2
  have hdefect : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ openCubeSet (originCube d m),
      |cutoffCoefficient M H omega N ((3:ℝ)^(-(N:ℤ)) • x + z0) - bk k x| ≤ ε := fun ε hε =>
    (hℓ.eventually (hU ε hε)).mono fun k hk x hx => hk x (hWK hx)
  have hconv := lem_as_regularity_dirichlet_stability (by positivity) hElla hEllb
    hbklo hsol hv hdefect
  have hAk : ∀ k, (3:ℝ)^(-((n+2:ℕ):ℤ))*normalizedL2On
        (truncatedCube d m (n+2:ℕ) ((3:ℝ)^N • (w-z0)))
        (fun x => (v k).toFun x-averageOn (truncatedCube d m (n+2:ℕ) ((3:ℝ)^N • (w-z0)))
          (v k).toFun) ≤
      C*(3:ℝ)^(rho*((m:ℝ)-n))*
        ((3:ℝ)^(-((m-5:ℕ):ℤ))*normalizedL2On (truncatedCube d m (m-5:ℕ) ((3:ℝ)^N • (w-z0)))
          (fun x => (v k).toFun x-averageOn (truncatedCube d m (m-5:ℕ) ((3:ℝ)^N • (w-z0)))
            (v k).toFun) +
          vectorSupNormOn (cube d m) h.grad +
          (aux_in_deterministic_onestep_sref M (fun om => infraredPartialSum om (ℓ k)) omega N
            ((N:ℤ)-m) w)⁻¹ *
            (3:ℝ)^((m:ℝ)/2)*holderSeminormOn (cube d m) (1/2) g +
          (3:ℝ)^((m:ℝ)/2)*holderSeminormOn (cube d m) (1/2) h.grad) := fun k =>
    hA M Rm hδ omega N (eta N omega) (fun m y => F N m y omega) (fun m y => P N m y omega)
      (fun m y => R N m y omega) (fun m y => Draw N m y omega) (fun m y => Z N m y omega)
      (fun m y => good N m y omega) (hEtaw N) (hPSw N) (ℓ k) m n hnm (by show m ≤ N + (k + L0 + m); omega)
      w z0 hw hallow (v k) h g (hv k) ⟨sOrder, hsO, hfw⟩ hgh hhh
  -- windows
  have hVQ : truncatedCube d m ((n+2:ℕ):ℤ) ((3:ℝ)^N • (w-z0)) ⊆ openCubeSet (originCube d m) :=
    truncatedCube_subset_cube d m _ _
  have hWQ : truncatedCube d m ((m-5:ℕ):ℤ) ((3:ℝ)^N • (w-z0)) ⊆ openCubeSet (originCube d m) :=
    truncatedCube_subset_cube d m _ _
  have hfinQ : volume (openCubeSet (originCube d m)) ≠ ⊤ :=
    (volume_openCubeSet_lt_top (originCube d m)).ne
  have hsr : Tendsto (fun k => aux_in_deterministic_onestep_sref M
      (fun om => infraredPartialSum om (ℓ k)) omega N ((N:ℤ)-m) w) atTop
      (𝓝 (aux_in_deterministic_onestep_sref M H omega N ((N:ℤ)-m) w)) :=
    aux_lem_as_regularity_actual_dirichlet_sref_tendsto M H
      (fun k om => infraredPartialSum om (ℓ k)) omega N _ w
      (((continuous_eval_const w).tendsto (H omega)).comp (hlim.comp hℓ))
  have hspos := aux_in_deterministic_onestep_sref_pos M H omega N ((N:ℤ)-m) w
  have hr : Tendsto (fun k => vectorSupNormOn (cube d m) h.grad +
      (aux_in_deterministic_onestep_sref M (fun om => infraredPartialSum om (ℓ k)) omega N
        ((N:ℤ)-m) w)⁻¹ * (3:ℝ)^((m:ℝ)/2) * holderSeminormOn (cube d m) (1/2) g +
      (3:ℝ)^((m:ℝ)/2) * holderSeminormOn (cube d m) (1/2) h.grad) atTop
      (𝓝 (vectorSupNormOn (cube d m) h.grad +
      (aux_in_deterministic_onestep_sref M H omega N ((N:ℤ)-m) w)⁻¹ * (3:ℝ)^((m:ℝ)/2) *
        holderSeminormOn (cube d m) (1/2) g +
      (3:ℝ)^((m:ℝ)/2) * holderSeminormOn (cube d m) (1/2) h.grad)) :=
    (tendsto_const_nhds.add (((hsr.inv₀ hspos.ne').mul_const _).mul_const _)).add
      tendsto_const_nhds
  have hlimit := lem_as_regularity_dirichlet_limit (Q := originCube d m)
    (measurableSet_truncatedCube d m _ _)
    (volume_toReal_truncatedCube_pos _ hw (by omega))
    (ne_top_of_le_ne_top hfinQ (measure_mono hVQ)) hVQ
    (measurableSet_truncatedCube d m _ _)
    (volume_toReal_truncatedCube_pos _ hw (by omega))
    (ne_top_of_le_ne_top hfinQ (measure_mono hWQ)) hWQ hconv
    (c1 := (3:ℝ)^(-((n+2:ℕ):ℤ))) (c2 := (3:ℝ)^(-((m-5:ℕ):ℤ)))
    (C := C*(3:ℝ)^(rho*((m:ℝ)-n))) hr (fun k => (hAk k).trans_eq (by ring))
  exact hlimit.trans_eq (by ring)

end Paper
