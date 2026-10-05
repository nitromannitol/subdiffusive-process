module

public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.FiniteStopping.CutoffRestrictions
public import SubdiffusiveProcess.FiniteStopping.QuotientNormBounds
public import SubdiffusiveProcess.FiniteStopping.TraceRescaling
public import SubdiffusiveProcess.Sobolev.NativeBoundaryResponse
public import SubdiffusiveProcess.Sobolev.BoundaryGrowthEnergy

@[expose] public section

/-!
# Absolute trace estimate (`eq:mfd-2`) for the native cell infimum, every radius

The deterministic half `eq:mfd-2` of `SubdiffusiveProcess.Paper.lem_extension` in the form of the represented
catalogue's clause I: for every cube `q = z + r Q_0` (any `r > 0`; the hypothesis `r ≤ 1` of the
installed statement is not used in its proof and is dropped in the re-proof below) and every
continuous `H¹` representative `e` with a boundary datum of the cell class,
`Λ_{N,q}(e) ≤ C_ext · U_N(q) · r^{d-2} · ‖e‖²_{C^β(∂q)/ℝ}` with
`U_N(q) = Λ_{σ/2,2}(q; A_N)` of the *cell-local* cutoff coefficient and `C_ext` uniform.
No stochastic input: the estimate holds for every field value.
-/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The deterministic half `eq:mfd-2` of `lem_extension` for every radius `r > 0` (the proof of the
installed `aux_lem_extension_boundary_half` never uses `r ≤ 1`). -/
theorem aux_model_cube_trace_bound_boundary_half (d : ℕ) (hd : 2 ≤ d) (E : in_J d)
    (X : in_extension d hd E) (S : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd) :
    ∀ (beta : ℝ), beta ∈ Set.Ioo (1 / 2 : ℝ) 1 →
    ∃ C : ℝ, 0 < C ∧
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
          ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
            K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
        (a : PositiveCoefficient (centeredCube z r hr))
        (G : SpatialCoordinates d → ℝ) (b : weakSobolevGraph (centeredCube z r hr)),
        ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
        IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
        ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
        dirichletResponse (killedResponseSpace hP) a b ≤
          C * E.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) *
            (r ^ beta *
              holderSeminorm beta
                (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2 := by
  intro beta hbeta
  have hσ : (beta - 1 / 2) / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hbeta.1, hbeta.2]
  refine ⟨2 * X.C ^ 2 * (((beta - 1 / 2) / 2) ^ (-3 : ℝ) * S.CTrace beta),
    mul_pos (mul_pos two_pos (pow_pos X.C_pos 2))
      (mul_pos (Real.rpow_pos_of_pos hσ.1 _) (S.CTrace_pos beta)), ?_⟩
  intro z r hr hP a G b hGcont hGhol htie
  have h1 : (0 : ℝ) < 1 := one_pos
  have : NeZero d := ⟨by omega⟩
  -- the coefficient on the unit cube, and the dilation invariance of `Λ`
  obtain ⟨ah, hah⟩ := dilation_coefficient_transport d z 0 r hr h1 a
  have hLam : E.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 =
      E.Lam 0 1 h1 ah 0 1 ((beta - 1 / 2) / 2 / 2) 2 := by
    rw [show (beta - 1 / 2) / 4 = (beta - 1 / 2) / 2 / 2 by ring]
    exact E.Lam_dilation z r hr a 0 h1 ah hah _ 2
  -- the boundary datum on the unit cube and its trace extension
  have hGhol1 := aux_lem_extension_isHolderOn_dilation z r hr beta G hGhol
  have hGsemi1 := (aux_lem_extension_holderSeminorm_dilation z r hr beta G).le
  obtain ⟨hh, U, hUc, hhU, hUG, hfin, hsum⟩ :=
    S.traceRightInverse beta hbeta 0 1 h1 rfl _ hGhol1
  -- the harmonic extension of `ĥ` on the unit cube and its energy
  obtain ⟨hP1, -⟩ := exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
    (centeredCube (0 : SpatialCoordinates d) 1 h1)
    (aux_lem_extension_isOpenBoundedConvexDomain_centeredCube 0 h1)
  have hEn := aux_lem_extension_unit_energy hd E X h1 hP1 ah _ hσ hh hfin
  have hker := dirichletMinimizer_mem_affine (killedResponseSpace hP1) ah hh
  -- the trace bound, rescaled
  have hNb : ∑ i : Fin d, cubeFractionalSqNorm hd 0 1 h1 ⟨_, hσ.1, hσ.2⟩
        ((hh : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i) ≤
      S.CTrace beta * (r ^ beta *
        holderSeminorm beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2 := by
    refine hsum.trans ?_
    rw [Real.one_rpow, one_mul]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (aux_lem_extension_holderSeminorm_nonneg _ _ _) hGsemi1 2)
      (S.CTrace_pos beta).le
  -- push-forward of the extension and of the harmonic correction
  obtain ⟨h, hhtie⟩ := aux_lem_extension_weak_pushforward z hr h1 hh
  obtain ⟨k, hktie⟩ := aux_lem_extension_killed_pushforward z hr h1 ⟨_, hker⟩
  have hhb := aux_lem_extension_datum_killed hd z hr h1 G hGcont U hUc hUG hh hhU h b hhtie htie
  have hresp := aux_lem_extension_response_le z hr h1 hP a ah hah b h k hhb hh
    (dirichletMinimizer (killedResponseSpace hP1) ah hh) hhtie hktie
  have hrd : 0 < r ^ ((d : ℝ) - 2) := Real.rpow_pos_of_pos hr _
  have hLpos := E.Lam_pos 0 1 h1 ah 0 1 ((beta - 1 / 2) / 2 / 2) 2
  refine hresp.trans ?_
  rw [hLam]
  calc r ^ ((d : ℝ) - 2) * sobolevCoefficientForm ah _ _
      ≤ r ^ ((d : ℝ) - 2) * (2 * X.C ^ 2 * ((beta - 1 / 2) / 2) ^ (-3 : ℝ) *
          E.Lam 0 1 h1 ah 0 1 ((beta - 1 / 2) / 2 / 2) 2 * (S.CTrace beta * (r ^ beta *
            holderSeminorm beta
              (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (hEn.trans ?_) hrd.le
        exact mul_le_mul_of_nonneg_left hNb
          (mul_nonneg (mul_nonneg (mul_nonneg two_pos.le (pow_pos X.C_pos 2).le)
            (Real.rpow_nonneg hσ.1.le _)) hLpos.le)
    _ = _ := by ring

/-- **Clause I (`eq:mfd-2`) of the represented catalogue**, for every radius and every field
value, with the cell-local pinned constant `U = Λ_{σ/2,2}(cell; cutoffPositiveCoefficient …)`. -/
theorem model_cube_trace_bound
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Xc : in_extension d hd E)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    ∃ Cext : ℝ, 0 < Cext ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (β : BilateralField d) (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (e : Homogenization.H1Function (centeredCube z r hr : Set (SpatialCoordinates d))),
        ContinuousOn e.toFun (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
        IsCellBoundaryClass beta z r e.toFun →
        cellDirichletInfimum (cutoffCoefficient M H β N)
            (centeredCube z r hr : Set (SpatialCoordinates d)) e ≤
          Cext * E.Lam z r hr (cutoffPositiveCoefficient M H β N z hr) z r
              ((beta - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) *
            (cellBoundaryQuotientNorm beta z r e.toFun) ^ 2 := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hExt⟩ := aux_model_cube_trace_bound_boundary_half d hd E Xc Sf beta hbeta
  refine ⟨C, hC, ?_⟩
  intro M H β N z r hr e hcont hcls
  have hP := SubdiffusiveProcess.centeredCube_killedPoincare (d := d) z hr
  set a : PositiveCoefficient (centeredCube z r hr) := cutoffPositiveCoefficient M H β N z hr
    with ha
  have hc := SubdiffusiveProcess.FiniteStopping.cutoffCoefficient_ae M H β N z hr
  rw [SubdiffusiveProcess.cellDirichletInfimum_eq_dirichletResponse hP a
    (cutoffCoefficient M H β N) hc e]
  have hclosure : closure (centeredCube z r hr : Set (SpatialCoordinates d)) =
      closedCube z r hr := by
    change closure (Metric.ball z (r / 2)) = Metric.closedBall z (r / 2)
    exact closure_ball z (ne_of_gt (half_pos hr))
  have hGcont : ContinuousOn e.toFun (closedCube z r hr : Set (SpatialCoordinates d)) := by
    rw [← hclosure]; exact hcont
  -- rescaled datum = pullback along the cube dilation
  have hresc : rescaledDatum z r e.toFun = fun x => e.toFun (cubeDilation z 0 r x) := by
    funext x
    unfold rescaledDatum
    congr 1
    funext i
    simp only [cubeDilation_apply, Pi.zero_apply, sub_zero]
  obtain ⟨hHold1, -⟩ := hcls
  rw [hresc] at hHold1
  have hHold : IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d)))
      e.toFun := by
    unfold IsHolderOn at hHold1 ⊢
    rw [aux_lem_extension_holderRatioSet_dilation z r hr beta e.toFun] at hHold1
    exact (bddAbove_smul_iff_of_pos (Real.rpow_pos_of_pos hr beta)).mp hHold1
  have hbTie : ((⟨sobolevDataOfH1 e, sobolevDataOfH1_mem_weak e⟩ :
        weakSobolevGraph (centeredCube z r hr)) : SobolevData (centeredCube z r hr)).1 =ᵐ[
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] e.toFun :=
    sobolevDataOfH1_fst_coeFn e
  have hbase := hExt z r hr hP a e.toFun ⟨sobolevDataOfH1 e, sobolevDataOfH1_mem_weak e⟩
    hGcont hHold hbTie
  have hKpos : 0 < C * E.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) :=
    mul_pos (mul_pos hC (E.Lam_pos _ _ _ _ _ _ _ _)) (Real.rpow_pos_of_pos hr _)
  have hsemi : ∀ c : ℝ,
      r ^ beta * holderSeminorm beta
          (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) e.toFun ≤
        cAlphaNorm beta (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
          Set (SpatialCoordinates d))) (fun x => rescaledDatum z r e.toFun x - c) := by
    intro c
    have hratio : holderRatioSet beta (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d))) (fun x => rescaledDatum z r e.toFun x - c) =
        holderRatioSet beta (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
          Set (SpatialCoordinates d))) (rescaledDatum z r e.toFun) := by
      ext v
      simp only [holderRatioSet, mem_ofPred_eq, sub_sub_sub_cancel_right]
    have h1 : holderSeminorm beta (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d))) (fun x => rescaledDatum z r e.toFun x - c) =
        r ^ beta * holderSeminorm beta
          (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) e.toFun := by
      unfold holderSeminorm
      rw [hratio, hresc]
      exact congrArg sSup (aux_lem_extension_holderRatioSet_dilation z r hr beta e.toFun) |>.trans
        (by rw [Real.sSup_smul_of_nonneg (Real.rpow_nonneg hr.le _)]; simp only [smul_eq_mul])
    unfold cAlphaNorm
    rw [h1]
    have h0 : 0 ≤ sSup {v : ℝ | ∃ x ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)), v = |rescaledDatum z r e.toFun x - c|} := by
      refine Real.sSup_nonneg ?_
      rintro v ⟨x, -, rfl⟩
      exact abs_nonneg _
    linarith
  have hX : 0 ≤ dirichletResponse (killedResponseSpace hP) a
      ⟨sobolevDataOfH1 e, sobolevDataOfH1_mem_weak e⟩ := dirichletResponse_nonneg _ _ _
  have hfinal := SubdiffusiveProcess.FiniteStopping.forall_c_to_quotient beta
    (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
    (rescaledDatum z r e.toFun) _ _ hX hKpos (fun c => by
      refine hbase.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hKpos.le
      exact pow_le_pow_left₀ (mul_nonneg (Real.rpow_nonneg hr.le _)
        (aux_lem_extension_holderSeminorm_nonneg _ _ _)) (hsemi c) 2)
  unfold cellBoundaryQuotientNorm
  exact hfinal

end SubdiffusiveProcess.Paper
