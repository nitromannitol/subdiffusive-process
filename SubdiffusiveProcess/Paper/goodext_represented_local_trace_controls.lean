import SubdiffusiveProcess.Paper.goodext_represented_controls_with_bank
import SubdiffusiveProcess.Paper.goodext_represented_cell_growth_bank
import SubdiffusiveProcess.Paper.goodext_represented_cell_coefficient_bank
import SubdiffusiveProcess.Sobolev.HarmonicSmoothGrowth

/-! Ambient form controls and every local-cell trace control share one represented
subsequence. The ultraviolet cutoff condition is discharged by a deterministic tail. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace Paper

/-- A single represented subsequence retains ambient controls and smooth-minimizer regularity and upper coefficients on a countable triadic-cell catalogue. -/
theorem goodext_represented_local_trace_controls
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (Interp : CubeFractionalInterpolationInput d hd)
    (t alpha beta : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hb : beta ∈ Ioo (1 / 2 : ℝ) 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (S : ResponseSpace (centeredCube z r hr))
        (hS : S.space = killedSobolevGraph (centeredCube z r hr))
        (k : ℕ) (ι : Type) [Countable ι] (zc : ι → SpatialCoordinates d)
        (N : ℕ → ℕ) (hN : StrictMono N)
        (Omega : Type) [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
        (env : ℕ → Omega → BilateralField d)
        (hEnv : ∀ n, Measurable (env n))
        (hLaw : ∀ n, Measure.map (env n) P = (chaosSampleLaw M).toMeasure),
      ∀ᵐ om ∂P,
      ∃ seq : ℕ → ℕ, StrictMono seq ∧
        Nonempty (aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S
          (fun n => cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n)) z hr)) ∧
        aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr
          (fun n => cutoffCoefficient M H (env (seq n) om) (N (seq n))) t alpha ∧
        ∀ i, ∃ Lam : ℝ, 0 ≤ Lam ∧
          (∀ n, I.Lam (zc i) ((3 : ℝ) ^ (-(k : ℤ))) (by positivity)
            (cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n)) (zc i) (by positivity))
            (zc i) ((3 : ℝ) ^ (-(k : ℤ))) ((beta - 1 / 2) / 4) 2 ≤ Lam) ∧
          ∀ (phi : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ phi →
          ∀ b : weakSobolevGraph (centeredCube (zc i) ((3 : ℝ) ^ (-(k : ℤ))) (by positivity)),
            ((b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (centeredCube (zc i) ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) : Set (SpatialCoordinates d))] phi) →
            ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∃ V : SpatialCoordinates d → ℝ,
              ContinuousOn V (closure (centeredCube (zc i) ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) : Set (SpatialCoordinates d))) ∧
              ((dirichletMinimizer
                (killedResponseSpace (centeredCube_killedPoincare (zc i) (by positivity)))
                (cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n)) (zc i) (by positivity)) b).val.1 :
                  SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                    (centeredCube (zc i) ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) : Set (SpatialCoordinates d))] V ∧
              IsHolderOn alpha (closure
                (centeredCube (zc i) ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) : Set (SpatialCoordinates d))) V ∧
              cAlphaNorm alpha (closure
                (centeredCube (zc i) ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) : Set (SpatialCoordinates d))) V ≤ C := by
  classical
  obtain ⟨da, hda, hA⟩ := goodext_represented_controls_with_bank d hd I Pin X W Cp Sob Interp
    t alpha ht htd ha ha1
  obtain ⟨dg, hdg, hG⟩ := goodext_represented_cell_growth_bank d hd I Pin X W Cp Sob
    t alpha ht htd ha ha1
  obtain ⟨dc, hdc, hC⟩ := goodext_represented_cell_coefficient_bank d hd I X Sob beta 1 hb zero_lt_one
  refine ⟨min da (min dg dc), lt_min hda (lt_min hdg hdc), ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr S hS k ι _ zc N hN Omega _ P _ env hEnv hLaw
  let rc : ℝ := (3 : ℝ) ^ (-(k : ℤ))
  have hrc : 0 < rc := by positivity
  obtain ⟨Bg, Cg, hmg, hng, hGrowth⟩ := hG M Rm Sreg It H hIR
    (hdelta.trans ((min_le_right _ _).trans (min_le_left _ _)))
    ι zc (fun _ => rc) (fun _ => hrc) N Omega P env hEnv hLaw
  obtain ⟨Bc, Cc, hmc, hnc, hCoeff⟩ := hC M Rm H hIR
    (hdelta.trans ((min_le_right _ _).trans (min_le_right _ _)))
    k ι zc N Omega P env hEnv hLaw
  let bank : (ι ⊕ ι) → ℕ → Omega → ℝ := Sum.elim Bg Bc
  let bounds : (ι ⊕ ι) → ℝ≥0 := Sum.elim Cg Cc
  have hm : ∀ j n, MemLp (bank j n) 1 P := by
    intro j n
    cases j with
    | inl i => exact hmg i n
    | inr i => exact hmc i n
  have hn : ∀ j n, eLpNorm (bank j n) 1 P ≤ bounds j := by
    intro j n
    cases j with
    | inl i => exact hng i n
    | inr i => exact hnc i n
  have hControls := hA M Rm Sreg It H hIR (hdelta.trans (min_le_left _ _))
    z r hr S hS N Omega P env hEnv hLaw (ι ⊕ ι) bank bounds hm hn
  filter_upwards [hControls, hGrowth, hCoeff] with om hControls hGrowth hCoeff
  obtain ⟨tau, htau, ⟨A⟩, hcell, hbank⟩ := hControls
  let seq : ℕ → ℕ := fun n => tau (n + k)
  have hseq : StrictMono seq := htau.comp (fun _ _ h => Nat.add_lt_add_right h k)
  have hLevel (n : ℕ) : k ≤ N (seq n) :=
    (Nat.le_add_left k n).trans ((htau.id_le (n + k)).trans (hN.id_le (seq n)))
  have hcell' : aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr
      (fun n => cutoffCoefficient M H (env (seq n) om) (N (seq n))) t alpha := by
    intro J hJ theta htheta thetaH hthetaH i
    obtain ⟨E, Gr, Ho, hE, hGr, hHo, hall⟩ := hcell J hJ theta htheta thetaH hthetaH i
    exact ⟨E, Gr, Ho, hE, hGr, hHo, fun n => hall (n + k)⟩
  refine ⟨seq, hseq, ⟨aux_prop_conc_controlled_forms_controls_reindex A (fun n => n + k)⟩,
    hcell', ?_⟩
  intro i
  obtain ⟨Kg, hKg, hBg⟩ := hbank (Sum.inl i)
  obtain ⟨Kc, hKc, hBc⟩ := hbank (Sum.inr i)
  let Lam : ℝ := Kc * rc ^ (-(1 : ℝ))
  have hLam : 0 ≤ Lam := mul_nonneg hKc (Real.rpow_nonneg hrc.le _)
  refine ⟨Lam, hLam, ?_, ?_⟩
  · intro n
    have hc := hCoeff i (seq n) (hLevel n)
    exact hc.trans (mul_le_mul_of_nonneg_right
      ((le_abs_self _).trans (hBc (n + k))) (Real.rpow_nonneg hrc.le _))
  · apply smooth_minimizer_regularity_of_growth (zc i) rc hrc
      (centeredCube_killedPoincare (zc i) hrc)
      (fun n => cutoffPositiveCoefficient M H (env (seq n) om) (N (seq n)) (zc i) hrc)
      alpha Kg hKg
    intro n phi Cphi hphi hCphi b u hb hu
    obtain ⟨V, hVc, hVae, hVh, hVn⟩ := hGrowth i (seq n) phi Cphi hphi hCphi b u hb hu
    refine ⟨V, hVc, hVae, hVh, hVn.trans ?_⟩
    have hCphi0 : 0 ≤ Cphi := (aux_prop_growth_c2Norm_nonneg _ _).trans hCphi
    exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hBg (n + k))) hCphi0

end Paper
