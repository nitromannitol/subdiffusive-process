import SubdiffusiveProcess.Paper.Support.B7cGluingStatement
import SubdiffusiveProcess.Paper.Support.B7cFiniteCellIdentification
import SubdiffusiveProcess.Paper.limit_form_package_controls




set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace Paper

/-- Complete the actual smooth trace packages in the form norm and uniformly.
All finite trace/mesh estimates are proved separately from the standing catalogue;
this helper has no presumed target limit. -/
theorem aux_mfd_prop_gluing_holder_from_smooth {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (w : ℕ → BilateralField d) (cutoff : ℕ → ℕ)
    (Ein : Paper.in_J d) (alpha : ℝ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (hqQ : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
        ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
            Set (SpatialCoordinates d)) ⊆
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (beta : ℝ) (hbeta0 : 0 ≤ beta)
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (G0 : DomainL2 (centeredCube z (3 * r) h3r) →L[ℝ]
      DomainL2 (centeredCube z (3 * r) h3r))
    (L0 : aux_limit_form_package_limit_side d hd z (3 * r) h3r S G0
      (fun n => Lane4.cutoffPositiveCoefficient M H (w n) (cutoff n) z h3r))
    (C : ℝ) (hC : 0 ≤ C)
    (hUqBdd : BddAbove (Set.range (fun n => Ein.Lam z r hr
      (Lane4.cutoffPositiveCoefficient M H (w n) (cutoff n) z hr)
      z r ((beta - 1 / 2) / 4) 2)))
    (hUq : ∀ n, 0 ≤ ((fun n => Ein.Lam z r hr
      (Lane4.cutoffPositiveCoefficient M H (w n) (cutoff n) z hr)
      z r ((beta - 1 / 2) / 4) 2)) n ∧ ((fun n => Ein.Lam z r hr
      (Lane4.cutoffPositiveCoefficient M H (w n) (cutoff n) z hr)
      z r ((beta - 1 / 2) / 4) 2)) n ≤ sSup (Set.range (fun n => Ein.Lam z r hr
      (Lane4.cutoffPositiveCoefficient M H (w n) (cutoff n) z hr)
      z r ((beta - 1 / 2) / 4) 2)))
    (hBound : ∀ n, ∀ e : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)),
      ContinuousOn e.toFun (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
      IsCellBoundaryClass beta z r e.toFun →
      cellDirichletInfimum (cutoffCoefficient M H (w n) (cutoff n))
        (centeredCube z r hr : Set (SpatialCoordinates d)) e ≤
      C * ((fun n => Ein.Lam z r hr
      (Lane4.cutoffPositiveCoefficient M H (w n) (cutoff n) z hr)
      z r ((beta - 1 / 2) / 4) 2)) n * r ^ ((d : ℝ) - 2) * cellBoundaryQuotientNorm beta z r e.toFun ^ 2)
    (Ugrid : OddGridIndex d (triadicHalf 1) → ℕ → ℝ)
    (UgridStar : OddGridIndex d (triadicHalf 1) → ℝ)
    (hUg : ∀ (k : OddGridIndex d (triadicHalf 1)) (n : ℕ),
      0 ≤ Ugrid k n ∧ Ugrid k n ≤ UgridStar k)
    (hGridBound : ∀ (k : OddGridIndex d (triadicHalf 1)) (n : ℕ),
      ∀ e : H1Function
          ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
            Set (SpatialCoordinates d)),
      ContinuousOn e.toFun
          (closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
              Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))) →
      IsCellBoundaryClass beta (oddGridCenter z (3 * r) (triadicHalf 1) k) r e.toFun →
      cellDirichletInfimum (cutoffCoefficient M H (w n) (cutoff n))
          ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
            Set (SpatialCoordinates d)) e ≤
        C * Ugrid k n * r ^ ((d : ℝ) - 2) *
          cellBoundaryQuotientNorm beta
            (oddGridCenter z (3 * r) (triadicHalf 1) k) r e.toFun ^ 2)
    (Bs : ℕ → SpatialCoordinates d → ℝ) (B : SpatialCoordinates d → ℝ)
    (hBc : Continuous B) (hBsupp : HasCompactSupport B)
    (hBinside : tsupport B ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hBholder : Lane4.IsHolderOn alpha Set.univ B)
    (hBsC : ∀ k, Continuous (Bs k))
    (hBsU : TendstoUniformly Bs B atTop)
    (hBsHol : ∀ k, Lane4.IsHolderOn beta
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
      (fun x => Bs k x - B x))
    (hBsBdd : ∀ k, BddAbove {v : ℝ | ∃ x ∈ closure
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)), v = |Bs k x - B x|})
    (hBsNorm : Tendsto (fun k => Lane4.cAlphaNorm beta
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
        (fun x => Bs k x - B x)) atTop (𝓝 0))
    (b : SpatialCoordinates d → ℝ)
    (hba : beta ≤ alpha)
    (hb : Lane4.IsHolderOn alpha (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) b)
    (hBb : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), B x = b x)
    (PhiH : ℕ → H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hPhiH : ∀ k, (PhiH k).toFun = Bs k)
    (Phiq : ℕ → H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hPhiq : ∀ k, (Phiq k).toFun = Bs k)
    (W : ℕ → ℕ → H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (WS : ℕ → ℕ → S.space)
    (hW : ∀ k n,
      (WS k n : SobolevData (centeredCube z (3 * r) h3r)) = sobolevDataOfH1 (W k n) ∧
      ContinuousOn (W k n).toFun
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      (∀ x ∈ frontier (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        (W k n).toFun x = 0) ∧
      ∀ c : OddGridIndex d (triadicHalf 1),
        IsWeaklyHarmonicOn (cutoffCoefficient M H (w n) (cutoff n))
          ((oddGridCell z (3 * r) h3r (triadicHalf 1) c :
            Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
          ((W k n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) c).isOpen
            (hcellsub c)) ∧
        HasZeroTraceDifferenceOn
          ((oddGridCell z (3 * r) h3r (triadicHalf 1) c :
            Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
          ((W k n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) c).isOpen
            (hcellsub c))
          ((PhiH k).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) c).isOpen
            (hcellsub c)) ∧
        ∀ x ∈ frontier ((oddGridCell z (3 * r) h3r (triadicHalf 1) c :
            Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
          (W k n).toFun x = Bs k x)
    (Uk : ℕ → DomainL2 (centeredCube z (3 * r) h3r)) (Uck : ℕ → SpatialCoordinates d → ℝ)
    (hUk1 : ∀ k, Uk k ∈ L0.form.domain)
    (hUk2 : ∀ k, ContinuousOn (Uck k)
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (hUk3 : ∀ k, (Uk k : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Uck k)
    (hUk4 : ∀ k, TendstoUniformlyOn (fun n => (W k n).toFun) (Uck k) atTop
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (hUk5 : ∀ k, ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      Uck k x = Bs k x)
    (hUk6 : ∀ k, L0.gamma.measure (Uk k)
      (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) = 0)
    (hUk7 : ∀ k, ∀ φ : DomainL2 (centeredCube z (3 * r) h3r), φ ∈ (L0.form.toClosedForm.killedCoreClosure (centeredCube z r hr : Set (SpatialCoordinates d))) → L0.form.form (Uk k) φ = 0)
    (hUk9 : ∀ k, ∀ V : DomainL2 (centeredCube z (3 * r) h3r),
      V ∈ L0.form.domain →
      ∀ Vc : SpatialCoordinates d → ℝ,
      ContinuousOn Vc
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
      (V : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Vc →
      (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), Vc x = Bs k x) →
      (L0.gamma.measure (Uk k) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        (L0.gamma.measure V (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
    (hUk8 : ∀ k, Tendsto (fun n => cellDirichletInfimum
      (cutoffCoefficient M H (w n) (cutoff n))
      (centeredCube z r hr : Set (SpatialCoordinates d)) (Phiq k)) atTop
      (𝓝 ((L0.gamma.measure (Uk k) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal))) :
    ∃ lam : ℝ, ∃ U : DomainL2 (centeredCube z (3 * r) h3r),
      ∃ Uc : SpatialCoordinates d → ℝ,
        aux_mfd_prop_gluing_trace_package d hd M H w cutoff z r hr z (3 * r) h3r
          rfl rfl S G0 L0 Ein C beta alpha b lam U Uc := by
  classical
  let A := fun n => cutoffCoefficient M H (w n) (cutoff n)
  let aC := fun n => Lane4.cutoffPositiveCoefficient M H (w n) (cutoff n) z h3r
  let E := L0.form.toClosedForm
  let Gamma := L0.gamma
  let Dq := E.killedCoreClosure (centeredCube z r hr : Set (SpatialCoordinates d))
  have hDq := DirichletForm.ClosedForm.isKilledDomain_killedCoreClosure E
    (centeredCube z r hr : Set (SpatialCoordinates d))
  have hAcont : ∀ n, ContinuousOn (A n)
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) :=
    fun n => (aux_mfd_prop_boundary_cutoff_continuous M H (w n) (cutoff n)).continuousOn
  have haC : ∀ n, ((aC n).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] A n :=
    fun n => FiniteStopping.cutoffCoefficient_ae M H (w n) (cutoff n) z h3r
  have hell : ∀ n, ∃ lo hi : ℝ, 0 < lo ∧
      ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        lo ≤ A n x ∧ A n x ≤ hi :=
    fun n => aux_mfd_prop_boundary_cutoff_elliptic_closure M H (w n) (cutoff n) _ _ _
  obtain ⟨_, hLower0, _⟩ := aux_limit_form_package_mosco_free d hd z (3 * r) h3r S G0 aC
    L0.response L0.response_eq L0.response_tendsto
  have hLower : ∀ (vN : ℕ → S.space) (v : DomainL2 (centeredCube z (3 * r) h3r)),
      (∀ f : DomainL2 (centeredCube z (3 * r) h3r), Tendsto (fun n => ∫ x, f x * (vN n).val.1 x
        ∂(volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))) atTop
        (𝓝 (∫ x, f x * v x ∂(volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))))) →
      E.energy v ≤ liminf (fun n => (responseForm S (aC n) (vN n) (vN n) : EReal)) atTop := by
    intro vN v hv
    rw [L0.energy_eq]
    apply hLower0 vN v
    intro f
    simpa only [aux_prop_gluing_inner_eq_integral] using hv f
  let Uq := fun n => Ein.Lam z r hr
    (Lane4.cutoffPositiveCoefficient M H (w n) (cutoff n) z hr)
    z r ((beta - 1 / 2) / 4) 2
  let UStar := sSup (Set.range Uq)
  have hcls := aux_prop_gluing_cellBoundaryClass z r hr beta alpha hbeta0 hba b hb
  obtain ⟨UN, UNS, hpatch, hUNcomp⟩ := aux_prop_gluing_holder_patches hd z r hr h3r hcellsub beta
    hbeta0 S A hAcont aC haC hell C hC Ugrid UgridStar hUg hGridBound Bs B hBsU hBsHol
    hBsBdd hBsNorm PhiH hPhiH W WS hW
  have hUNq : ∀ n, ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      (UN n).toFun x = b x := by
    intro n x hx
    let mid : OddGridIndex d (triadicHalf 1) := fun _ => ⟨triadicHalf 1, by omega⟩
    have hxmid : x ∈ frontier (oddGridCell z (3 * r) h3r (triadicHalf 1) mid : Set (SpatialCoordinates d)) := by
      rw [aux_prop_gluing_central_cell z r hr h3r]
      exact hx
    exact (((hpatch n).2.2.2 mid).2 x hxmid).trans (hBb x hx)
  obtain ⟨lam, hlam, hlL⟩ := aux_prop_gluing_response z r hr h3r hqQ beta A hAcont hell
    C UStar hC Uq hUq hBound Bs B hBsC hBsHol hBsBdd hBsNorm Phiq hPhiq
    (fun k => (Gamma.measure (Uk k) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) hUk8 UN (fun n => (hpatch n).2.1)
    (fun n x hx => (hUNq n x hx).trans (hBb x hx).symm)
  have hLb := aux_prop_gluing_bound z r hr h3r hqQ beta A C UStar hC Uq hUq hBound b hcls UN
    (fun n => (hpatch n).2.1) hUNq lam hlam
  obtain ⟨U, Uc, hrest⟩ := aux_prop_gluing_limit_object hd z r hr h3r hqQ hcellsub beta hbeta0 S A
    hAcont aC haC hell E Gamma hLower Dq hDq C hC Ugrid UgridStar hUg hGridBound Bs B hBsU
    hBsHol hBsBdd hBsNorm b hBb PhiH hPhiH W WS hW Uk Uck hUk1 hUk2 hUk3 hUk4 hUk5 hUk6
    hUk7 hUk9 UN hUNcomp lam hlL
  exact ⟨lam, U, Uc, B, UN, UNS, hcls, hBc, hBsupp, hBinside, hBholder, hBb, hpatch,
    hlam, hUqBdd, hLb, hrest⟩

end Paper
